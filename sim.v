From Trie Require Import abs_aut conc_aut.

(*  ###############################################################  *)
(*  Refinement, and forward simulation as the way to prove it  *)

(*  ===============================================================  *)
(*  Running an execution in two halves  *)

(*  Replaying e1 followed by e2 is replaying e1, then replaying e2 from where
    that left off, with the two traces stuck together.  *)

Lemma abs_run_app : forall (i j : nat) (e1 e2 : execution) (c : abs_config),
  abs_run i j c (e1 ++ e2)
  = (fst (abs_run i j (fst (abs_run i j c e1)) e2),
     snd (abs_run i j c e1)
     ++ snd (abs_run i j (fst (abs_run i j c e1)) e2)).
Proof.
  intros i j e1.
  induction e1 as [| [t act] rest IH]; intros e2 c; simpl.
  - destruct (abs_run i j c e2). reflexivity.
  - destruct (abs_next i j c t act) as [c1 evs] eqn:E1. simpl.
    rewrite IH. simpl.
    destruct (abs_run i j c1 rest) as [c2 evs'] eqn:E2. simpl.
    destruct (abs_run i j c2 e2) as [c3 evs''] eqn:E3. simpl.
    rewrite app_assoc. reflexivity.
Qed.

(*  and legality behaves the same way; if the first half is something the
    machine could have done, and the second half is something it could have
    done from where the first half ended, then so is the whole  *)

Lemma abs_legal_app : forall (i j : nat) (e1 e2 : execution) (c : abs_config),
  abs_legal i j c e1 = true ->
  abs_legal i j (fst (abs_run i j c e1)) e2 = true ->
  abs_legal i j c (e1 ++ e2) = true.
Proof.
  intros i j e1.
  induction e1 as [| [t act] rest IH]; intros e2 c H1 H2; simpl in *.
  - exact H2.
  - apply Bool.andb_true_iff in H1 as [Hen Hrest].
    rewrite Hen. simpl.
    destruct (abs_next i j c t act) as [c1 evs] eqn:E1. simpl in *.
    apply IH.
    + exact Hrest.
    + destruct (abs_run i j c1 rest). simpl in *. exact H2.
Qed.

(*  ===============================================================  *)
(*  What we have to prove  *)

(*  The concrete component c refines the abstract component a when, whatever
    the threads were told to do and whatever order turns in, the trace that
    comes out is one the abstract component could have produced as well via
    some execution.

    Arguments: i and j the interval both are over, c the concrete starting
    configuration, a the abstract one. Returns a Prop.

    Every execution mentioned here is one a machine could really have performed
    (legal). On the left the execution is generated from a schedule and the
    programs, so it is legal by conc_exec_legal. On the right the legality is
    demanded outright. The schedules are not required to match, and they could
    not be. One operation is three turns in the abstract machine and up to
    eleven in the concrete. So traces, what outsiders observe, are compared.  *)

Definition refines (i j : nat) (c : conc_config) (a : abs_config) : Prop :=
  forall (sigma : sched) (P : progs),
    wf_progs i j P ->
    exists e : execution,
      abs_legal i j a e = true
      /\ conc_trace i j c sigma P = abs_trace_from i j a e.

(*  ===============================================================  *)
(*  Forward simulation  *)

(*  R is a forward simulation when every single concrete step can be answered
    by a stretch of abstract execution that emits the same events and R still
    holds.

    Argument: R a relation between concrete and abstract configurations.
    Returns a Prop.
    
    concrete:   c  ----- one step -------->  c'
                |                            |
                R                            R
                |                            |
    abstract:   a  ----- e (any length) -->  a'

    and both arrows emit the same events

    Note: The abstract answer is a stretch of a (legal) execution rather than
    one action. It has to be, because the two machines run at different speeds.
    Also, this only says R, once it holds, keeps holding, not that it holds to
    begin with. The events must also agree exactly.  *)

Definition forward_simulation (i j : nat) (R : conc_config -> abs_config -> Prop) : Prop :=
  forall (c c' : conc_config) (t : tid) (act : action) (evs : list event)
         (a : abs_config),
    conc_next i j c t act = (c', evs) ->     (*  c steps to c', emitting evs  *)
    R c a ->                                 (*  c and a are related  *)
    exists (e : execution) (a' : abs_config),
      abs_run i j a e = (a', evs)            (*  e takes a to a', emitting evs too  *)
      /\ abs_legal i j a e = true            (*  e is a real abstract run  *)
      /\ R c' a'.                            (*  c' and a' are related again  *)

(*  If R is a forward simulation, and R relates the two starting
    configurations, then the concrete component refines the abstract one.

    The proof walks down the schedule one turn at a time. Each turn is one
    concrete step, forward_simulation hands back a stretch of abstract execution
    for it, which are joined together with abs_run_app and abs_legal_app.

    The induction has three cases, because conc_exec does. A busy thread
    taking its forced action and an idle thread announcing the next
    operation of its program both put one step in front of the rest, and are
    handled together by Hmove. A thread whose program has run out has its
    turn skipped, so nothing happens and there is nothing to answer.

    Nothing in this proof mentions the trie, so it is done once here and used
    for every refinement. *)

Theorem forward_simulation_refines :
  forall (i j : nat) (R : conc_config -> abs_config -> Prop)
         (c : conc_config) (a : abs_config),
  forward_simulation i j R ->
  R c a ->
  refines i j c a.
Proof.
  intros i j R c a Hsim HR sigma P _.
  unfold conc_trace, conc_trace_from, abs_trace_from.
  revert P c a HR.
  induction sigma as [| t rest IH]; intros P c a HR.
  - exists []. split; reflexivity.
  - assert (Hmove : forall (act : action) (Q : progs),
      exists e : execution,
        abs_legal i j a e = true
        /\ snd (conc_run i j c
                  ((t, act) :: conc_exec i j (fst (conc_next i j c t act)) rest Q))
           = snd (abs_run i j a e)).
    { intros act Q.
      destruct (conc_next i j c t act) as [c1 evs] eqn:E1.
      destruct (Hsim c c1 t act evs a E1 HR) as [e1 [a1 [Hrun1 [Hleg1 HR1]]]].
      destruct (IH Q c1 a1 HR1) as [e2 [Hleg2 Hev2]].
      exists (e1 ++ e2). rewrite abs_run_app, Hrun1. simpl. rewrite E1.
      destruct (conc_run i j c1 (conc_exec i j c1 rest Q)) as [c2 evs'] eqn:E2.
      simpl in *. split.
      - apply abs_legal_app. exact Hleg1. rewrite Hrun1. exact Hleg2.
      - rewrite Hev2. reflexivity. }
    simpl. destruct (conc_busy_act (cstate c t)) as [act |] eqn:Eb.
    + apply (Hmove act P).
    + destruct (P t) as [| o os] eqn:EP.
      * apply IH. exact HR.
      * apply (Hmove (act_invoke o) (upd P t os)).
Qed.