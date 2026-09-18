From Trie Require Import abs_aut conc_aut.

(* ################################################################# *)
(** * Refinement, and forward simulation as the way to prove it *)

(* ================================================================= *)
(** ** Running a schedule in two halves *)

(** Running s1 followed by s2 is running s1, then running s2 from where that
    left off, and sticking the two traces together.

    i and j are the interval, s1 and s2 the two halves, a the starting
    configuration. This is needed in soundness proof below *)

Lemma abs_run_app : forall (i j : nat) (s1 s2 : list (tid * action)) (a : abs_config),
  abs_run i j a (s1 ++ s2)
  = (fst (abs_run i j (fst (abs_run i j a s1)) s2),
     snd (abs_run i j a s1)
     ++ snd (abs_run i j (fst (abs_run i j a s1)) s2)).
Proof.
  intros i j s1.
  induction s1 as [| [t act] rest IH]; intros s2 a; simpl.
  - destruct (abs_run i j a s2). reflexivity.
  - destruct (abs_next i j a t act) as [a1 evs] eqn:E1. simpl.
    rewrite IH. simpl.
    destruct (abs_run i j a1 rest) as [a2 evs'] eqn:E2. simpl.
    destruct (abs_run i j a2 s2) as [a3 evs''] eqn:E3. simpl.
    rewrite app_assoc. reflexivity.
Qed.

(* ================================================================= *)
(** ** What we have to prove *)

(** The concrete component c refines the abstract component a when every
    trace c can produce, a can produce too.

    Arguments: i and j the interval both are over, c the concrete starting
    configuration, a the abstract one. Returns a Prop.

    Note that the legality hypothesis is not needed because a step that isn't
    enabled stutters in both machines, and the stutters can be deleted without
    changing the trace. *)

Definition refines (i j : nat) (c : conc_config) (a : abs_config) : Prop :=
  forall csched : list (tid * action),
    exists asched : list (tid * action),
      conc_trace i j c csched = abs_trace_from i j a asched.

(* ================================================================= *)
(** ** Forward simulation *)

(** R is a forward simulation when every single concrete step can be answered
    by some abstract steps that emit the same events, landing back to R.

    Argument: R a relation between concrete and abstract configurations.
    Returns a Prop.

    Note that the abstract side is a whole schedule, not one action. It has
    to be since in many cases one concrete step is answered by mange abstract
    steps (be them be empty or containing a linearization point).

    Also, the events must agree exactly, which is what ties the two machines
    together.

    There is no hypothesis that the concrete step was enabled. It again is
    not needed since a disabled step stutters and emits nothing, so it is
    answered by the empty schedule *)

Definition simulates (i j : nat) (R : conc_config -> abs_config -> Prop) : Prop :=
  forall (c : conc_config) (a : abs_config) (t : tid) (act : action),
    R c a ->
    exists asched : list (tid * action),
      R (fst (conc_next i j c t act)) (fst (abs_run i j a asched))
      /\ snd (conc_next i j c t act) = snd (abs_run i j a asched).

(** and a forward simulation is enough if R relates the two starting
    configurations and R is a simulation, then the concrete component
    refines the abstract one.

    Note that this proof doesn't mention anything about the trie, so it can be used
    in many places. Very useful. *)

Theorem simulation_sound : forall (i j : nat) (R : conc_config -> abs_config -> Prop),
  simulates i j R ->
  forall (c : conc_config) (a : abs_config),
    R c a -> refines i j c a.
Proof.
  intros i j R Hsim c a HR csched. revert c a HR.
  induction csched as [| [t act] rest IH]; intros c a HR.
  - exists []. reflexivity.
  - destruct (Hsim c a t act HR) as [as1 [HR' Hev]].
    destruct (IH (fst (conc_next i j c t act))
                 (fst (abs_run i j a as1)) HR') as [as2 Heq].
    exists (as1 ++ as2).
    unfold conc_trace, abs_trace_from in *.
    rewrite abs_run_app. simpl.
    destruct (conc_next i j c t act) as [c1 evs] eqn:E1. simpl in *.
    destruct (conc_run i j c1 rest) as [c2 evs'] eqn:E2. simpl in *.
    rewrite Hev, Heq. reflexivity.
Qed.
