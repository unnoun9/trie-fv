From Trie Require Import abs_aut.

(* ################################################################# *)
(** * Example executions of the abstract machine *)

(** These are test cases rather than results. Almost every one is closed by
    reflexivity, so it really does run the definitions, and it would stop
    compiling if a definition changed behaviour. The component is 1..4
    throughout, except where the point is a key outside it *)

(* ================================================================= *)
(** ** Version 1, the option shaped step *)

(** A genuinely interleaved schedule: three threads announce, linearize and
    return in different orders, and the trace comes out with the events in
    the order they actually happened. Thread 3 asks for the size after both
    inserts have linearized but before either has returned, and correctly
    sees 2, since linearization is what the answer depends on and not the
    return *)

Example abs_run_opt_example1 :
  abs_trace_opt 1 4 [ (1, act_invoke (op_insert 3));
                      (2, act_invoke (op_insert 1));
                      (1, act_step);
                      (2, act_step);
                      (3, act_invoke op_size);
                      (2, act_return);
                      (3, act_step);
                      (1, act_return);
                      (3, act_return) ]
  = Some [ ev_invoke 1 (op_insert 3);
           ev_invoke 2 (op_insert 1);
           ev_invoke 3 op_size;
           ev_return 2 (res_bool true);
           ev_return 1 (res_bool true);
           ev_return 3 (res_nat 2) ].
Proof. reflexivity. Qed.

(** and a schedule that is not legal: thread 1 returns before it has invoked
    anything, so version 1 refuses the whole run *)

Example abs_run_opt_example2 :
  abs_trace_opt 1 4 [ (1, act_return) ] = None.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Version 2, the total step *)

(** The same interleaving as the first example, run through the total step
    function. The schedule is legal and the trace agrees, which is
    abs_trace_split made concrete *)

Example abs_run_example1 :
  let sched := [ (1, act_invoke (op_insert 3));
                 (2, act_invoke (op_insert 1));
                 (1, act_step);
                 (2, act_step);
                 (3, act_invoke op_size);
                 (2, act_return);
                 (3, act_step);
                 (1, act_return);
                 (3, act_return) ] in
  abs_legal 1 4 abs_init sched = true
  /\ abs_trace 1 4 sched = [ ev_invoke 1 (op_insert 3);
                             ev_invoke 2 (op_insert 1);
                             ev_invoke 3 op_size;
                             ev_return 2 (res_bool true);
                             ev_return 1 (res_bool true);
                             ev_return 3 (res_nat 2) ].
Proof. split; reflexivity. Qed.

(** The illegal schedule from before. Version 2 does not refuse it, it just
    stutters, so the schedule is reported as not legal and its trace is
    empty *)

Example abs_run_example2 :
  abs_legal 1 4 abs_init [ (1, act_return) ] = false /\
  abs_trace 1 4 [ (1, act_return) ] = [].
Proof. split; reflexivity. Qed.

(** A schedule with one stutter buried in the middle of legal steps. The
    stutter contributes nothing, so the trace is exactly the trace of the
    other three steps, while version 1 refuses the run outright. This is the
    difference between the two versions in one example *)

Example abs_run_example3 :
  let sched := [ (1, act_invoke (op_insert 3));
                 (2, act_return);                (* thread 2 never invoked *)
                 (1, act_step);
                 (1, act_return) ] in
  abs_legal 1 4 abs_init sched = false
  /\ abs_trace 1 4 sched = [ ev_invoke 1 (op_insert 3);
                             ev_return 1 (res_bool true) ]
  /\ abs_trace_opt 1 4 sched = None.
Proof. repeat split; reflexivity. Qed.

(** Pruning that same schedule drops the stutter and nothing else, and what
    is left is legal and has the same trace. This is abs_prune_legal and
    abs_prune_same on a concrete input *)

Example abs_prune_example :
  let sched := [ (1, act_invoke (op_insert 3));
                 (2, act_return);
                 (1, act_step);
                 (1, act_return) ] in
  abs_prune 1 4 abs_init sched = [ (1, act_invoke (op_insert 3));
                                   (1, act_step);
                                   (1, act_return) ]
  /\ abs_legal 1 4 abs_init (abs_prune 1 4 abs_init sched) = true
  /\ abs_trace 1 4 (abs_prune 1 4 abs_init sched) = abs_trace 1 4 sched.
Proof. repeat split; reflexivity. Qed.

(* ================================================================= *)
(** ** Version 3, the relation *)

(** One thread running an insert on its own. The configuration it lands in is
    left as an existential, since the relation does not compute it for us;
    the proof builds the derivation one step at a time, one constructor per
    action. The commented block below is the same proof written with
    automation, kept for comparison *)

Example abs_run_R_example1 : exists c,
  abs_run_R 1 4 abs_init
    [ (1, act_invoke (op_insert 3));
      (1, act_step);
      (1, act_return) ]
    [ ev_invoke 1 (op_insert 3);
      ev_return 1 (res_bool true) ]
    c.
Proof.
  eexists.
  eapply abs_run_R_cons.
  - apply abs_next_R_invoke; reflexivity.
  - eapply abs_run_R_cons.
    + eapply abs_next_R_linearize.
      * reflexivity.
      * reflexivity.
    + eapply abs_run_R_cons.
      * apply abs_next_R_return. reflexivity.
      * apply abs_run_R_nil.
      * reflexivity.
    + reflexivity.
  - reflexivity.

(*
  eexists.
  repeat (eapply abs_run_R_cons; [ econstructor; reflexivity | | ]).
  apply abs_run_R_nil.
  all: reflexivity.
*)
Qed.

(** The relation has no tuple at all for a disallowed step. Where version 2
    stutters and version 1 answers None, version 3 simply cannot be derived,
    and inversion finds the contradiction in the premise that thread 1 is
    already owing an answer *)

Example abs_run_R_example2 : forall (evs : list event) (c' : abs_config),
  ~ abs_next_R 1 4 abs_init 1 act_return evs c'.
Proof. intros evs c' H. inversion H. discriminate. Qed.

(* ================================================================= *)
(** ** The specification itself *)

(** Two of the harder query answers, read straight off abs_apply_op on a set
    holding 1 and 3. Snapshot lists them in order, and the rank of 3 is 2,
    counting both keys that are at most 3 *)

Example snapshot_and_rank_example :
  snd (abs_apply_op 1 4 op_snapshot
         (upd (upd empty_abs_set 1 true) 3 true))
  = res_set [1; 3]
  /\
  snd (abs_apply_op 1 4 (op_rank 3)
         (upd (upd empty_abs_set 1 true) 3 true))
  = res_nat 2.
Proof. split; reflexivity. Qed.

(** A key outside the component's interval cannot even be invoked, so the
    operation never starts and the trace stays empty. This is the guard the
    recursive plan needs, since a component must refuse work that belongs to
    a sibling *)

Example out_of_interval_example :
  abs_trace_opt 1 4 [ (1, act_invoke (op_insert 5)) ] = None
  /\
  abs_legal 1 4 abs_init [ (1, act_invoke (op_insert 5)) ] = false
  /\
  abs_trace 1 4 [ (1, act_invoke (op_insert 5)) ] = [].
Proof. repeat split; reflexivity. Qed.
