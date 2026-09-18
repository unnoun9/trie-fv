From Trie Require Import abs_aut conc_aut.

(* ################################################################# *)
(** * Example executions of the concrete machine *)

(** These are test cases rather than results. Every one is closed by
    reflexivity, so each really does run the step function, and any of them
    would stop compiling if the machine changed behaviour. Three of them are
    there to pin down behaviour that is easy to get wrong: a query reading a
    stale version, a refresh losing its CAS, and two threads racing at a
    leaf *)

(* ================================================================= *)
(** ** Schedules for a thread running on its own *)

(** A whole update by one thread at an internal node with nobody
    interfering: the invoke, the child step, the four steps of the first
    refresh, then the return.

    Arguments: t the thread, o the operation. Returns the schedule *)

Definition solo (t : tid) (o : op) : list (tid * action) :=
  [ (t, act_invoke o); (t, act_step); (t, act_step);
    (t, act_step); (t, act_step); (t, act_step); (t, act_return) ].

(** An update at a leaf is shorter, since there is no child and no refresh:
    invoke, read, CAS, return *)

Definition solo_leaf (t : tid) (o : op) : list (tid * action) :=
  [ (t, act_invoke o); (t, act_step); (t, act_step); (t, act_return) ].

(** A query is shorter still, one read between the invoke and the return,
    whichever shape of component it runs on *)

Definition solo_query (t : tid) (o : op) : list (tid * action) :=
  [ (t, act_invoke o); (t, act_step); (t, act_return) ].

(* ================================================================= *)
(** ** An internal component over 1..2 on two abstract subcomponents *)

(** Two abstract slots, one per key, both empty, and the component built over
    them. Tags 1 and 2 belong to the slots' versions and 3 to the
    component's, so 4 is the first free tag *)

Definition al : node := node_abs 1 1 empty_abs_set (vleaf 1 1 0).
Definition ar : node := node_abs 2 2 empty_abs_set (vleaf 2 2 0).
Definition c0 : conc_config := conc_init (n_build 1 2 al ar 3) 4.

(** The schedule runs to completion and the trace is the invoke followed by
    the return, with true because the key was absent *)

Example insert_runs :
  conc_legal 1 2 c0 (solo 1 (op_insert 2)) = true
  /\ conc_trace 1 2 c0 (solo 1 (op_insert 2))
     = [ ev_invoke 1 (op_insert 2); ev_return 1 (res_bool true) ].
Proof. split; reflexivity. Qed.

(** and afterwards the component's own published version really does report
    the key, so the refresh did its job and did not merely return *)

Example insert_lands :
  let after := fst (conc_run 1 2 c0 (solo 1 (op_insert 2))) in
  v_sum (n_version after.(root)) = 1
  /\ v_elements (n_version after.(root)) = [2].
Proof. split; reflexivity. Qed.

(** Inserting a key that is already there answers false and changes nothing.
    The answer comes from the subcomponent, not from the refresh, which is
    why it is false even though the refresh still runs *)

Example insert_twice :
  let after := fst (conc_run 1 2 c0 (solo 1 (op_insert 2))) in
  conc_trace 1 2 after (solo 1 (op_insert 2))
  = [ ev_invoke 1 (op_insert 2); ev_return 1 (res_bool false) ].
Proof. reflexivity. Qed.

(** A key outside 1..2 cannot even be invoked here, so the schedule is not
    legal and its trace is empty. This is the guard that keeps a component
    from doing a sibling's work *)

Example out_of_interval :
  conc_legal 1 2 c0 [ (1, act_invoke (op_insert 7)) ] = false
  /\ conc_trace 1 2 c0 [ (1, act_invoke (op_insert 7)) ] = [].
Proof. split; reflexivity. Qed.

(** A query is answered from this component's own published version in a
    single read, never by descending, which is why solo_query has only one
    step in it *)

Example size_after :
  let after := fst (conc_run 1 2 c0 (solo 1 (op_insert 2))) in
  conc_trace 1 2 after (solo_query 2 op_size)
  = [ ev_invoke 2 op_size; ev_return 2 (res_nat 1) ].
Proof. reflexivity. Qed.

(** The abstract child really moved, and both halves of the slot moved
    together: the set it claims to hold says the key is there, and the
    version it publishes lists it. That agreement is exactly wf_slot, and it
    is what lets an abstract child stand in for a concrete one *)

Example child_set_moved :
  let after := fst (conc_run 1 2 c0 (solo 1 (op_insert 2))) in
  match after.(root) with
  | nnode _ _ _ r _ => slot_set r 2 = true
                       /\ v_elements (slot_snapshot r) = [2]
  | nleaf _ _ => False
  end.
Proof. split; reflexivity. Qed.

(** The example that decides where linearization points go.

    Thread 1 takes its child step, so the key genuinely is in the
    subcomponent now, and thread 2 then runs a whole size query before thread
    1 has refreshed. The query reports 0. That is not a bug: thread 1 has not
    returned yet, so an observer is allowed to be told the key is absent, and
    the insert may be linearized after the query. This is why the
    linearization point of an update is its arrival at the root and not its
    write at the leaf *)

Example size_sees_stale :
  conc_trace 1 2 c0
    ([ (1, act_invoke (op_insert 2)); (1, act_step) ]   (* child step done *)
     ++ solo_query 2 op_size
     ++ [ (1, act_step); (1, act_step); (1, act_step);
          (1, act_step); (1, act_return) ])
  = [ ev_invoke 1 (op_insert 2);
      ev_invoke 2 op_size;
      ev_return 2 (res_nat 0);         (* stale, and legitimately so *)
      ev_return 1 (res_bool true) ].
Proof. reflexivity. Qed.

(** A refresh that loses its CAS, which is the case the double refresh
    exists for.

    Thread 1 reads the component's version, then thread 2 runs an entire
    insert and installs a new one. Thread 1's CAS now finds a different tag
    and fails, so it goes round a second time. The final sum is 2, so nothing
    was lost, and both threads answer true *)

Example first_refresh_loses :
  let sched :=
    [ (1, act_invoke (op_insert 1)); (1, act_step);  (* child step *)
      (1, act_step);                                 (* read own version *)
      (2, act_invoke (op_insert 2)); (2, act_step); (2, act_step);
      (2, act_step); (2, act_step); (2, act_step); (2, act_return);
      (1, act_step); (1, act_step);                  (* snapshot both slots *)
      (1, act_step);                                 (* CAS, must fail *)
      (1, act_step); (1, act_step); (1, act_step); (1, act_step);
      (1, act_return) ] in
  conc_legal 1 2 c0 sched = true
  /\ conc_trace 1 2 c0 sched
     = [ ev_invoke 1 (op_insert 1);
         ev_invoke 2 (op_insert 2);
         ev_return 2 (res_bool true);
         ev_return 1 (res_bool true) ]
  /\ v_sum (n_version (fst (conc_run 1 2 c0 sched)).(root)) = 2.
Proof. repeat split; reflexivity. Qed.

(* ================================================================= *)
(** ** The same machine on a leaf component, covering the single key 5 *)

(** One leaf, empty, with tag 0 taken and 1 free *)

Definition lc0 : conc_config := conc_init (nleaf 5 (vleaf 0 5 0)) 1.

(** Two threads race to insert the same key. Both read the same version, so
    both then try to CAS over it, and only the first one wins. The loser
    answers false, which is correct, because by the time it looked again the
    key was already there *)

Example leaf_race :
  let sched := [ (1, act_invoke (op_insert 5)); (2, act_invoke (op_insert 5));
                 (1, act_step); (2, act_step);        (* both read *)
                 (1, act_step); (2, act_step);        (* 1 wins the CAS *)
                 (1, act_return); (2, act_return) ] in
  conc_legal 5 5 lc0 sched = true
  /\ conc_trace 5 5 lc0 sched
     = [ ev_invoke 1 (op_insert 5);
         ev_invoke 2 (op_insert 5);
         ev_return 1 (res_bool true);
         ev_return 2 (res_bool false) ]
  /\ v_sum (n_version (fst (conc_run 5 5 lc0 sched)).(root)) = 1.
Proof. repeat split; reflexivity. Qed.

(** and a query on that same leaf, driven by the very same step function that
    drives queries at an internal node *)

Example leaf_find :
  let after := fst (conc_run 5 5 lc0 (solo_leaf 1 (op_insert 5))) in
  conc_trace 5 5 after (solo_query 2 (op_find 5))
  = [ ev_invoke 2 (op_find 5); ev_return 2 (res_bool true) ].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** A real subcomponent in one slot and an abstract set in the other *)

(** This is the substitution that monotonicity is about: the right slot holds
    a genuine two leaf component over 3..4, the left slot is still an
    abstract set over 1..2, and the parent cannot tell them apart *)

Definition sub : nodetree :=
  nnode 3 4 (node_conc (nleaf 3 (vleaf 11 3 0)))
            (node_conc (nleaf 4 (vleaf 12 4 0)))
            (vnode 10 3 4 0 (vleaf 11 3 0) (vleaf 12 4 0)).

Definition c1 : conc_config :=
  conc_init (n_build 1 4
               (node_abs 1 2 empty_abs_set
                  (vnode 20 1 2 0 (vleaf 21 1 0) (vleaf 22 2 0)))
               (node_conc sub) 30) 31.

(** An insert of 3 goes through the concrete slot, two levels of real
    component, and the parent's published version ends up listing it *)

Example mixed_slots :
  conc_legal 1 4 c1 (solo 1 (op_insert 3)) = true
  /\ conc_trace 1 4 c1 (solo 1 (op_insert 3))
     = [ ev_invoke 1 (op_insert 3); ev_return 1 (res_bool true) ]
  /\ v_elements (n_version (fst (conc_run 1 4 c1 (solo 1 (op_insert 3)))).(root))
     = [3].
Proof. repeat split; reflexivity. Qed.

(** and the same insert through the abstract slot on the other side produces
    the same shape of result, from the same schedule, through the same step
    function. Neither the schedule nor the machine mentions which kind of
    child it is talking to *)

Example mixed_slots_abs :
  conc_trace 1 4 c1 (solo 1 (op_insert 2))
  = [ ev_invoke 1 (op_insert 2); ev_return 1 (res_bool true) ]
  /\ v_elements (n_version (fst (conc_run 1 4 c1 (solo 1 (op_insert 2)))).(root))
     = [2].
Proof. split; reflexivity. Qed.
