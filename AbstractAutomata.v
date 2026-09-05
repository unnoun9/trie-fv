From Stdlib Require Export Arith.
From Stdlib Require Export List.
From Stdlib Require Export Lia.
Export ListNotations.

(* ################################################################# *)
(** The Abstract Implementation *)

Definition tid := nat.
Definition key := nat.

(** The operations of the set abstract data type *)

Inductive op : Type :=
  | op_insert (k : key)
  | op_delete (k : key)
  | op_find   (k : key)
  | op_size
  | op_select (r : nat).

(** Operations return different type, hence this type *)

Inductive res : Type :=
  | res_bool (b : bool)
  | res_nat  (n : nat)
  | res_opt  (o : option key).

(** The abstract set itself, represented as a characteristic function *)

Definition aset := key -> bool.

Definition empty_aset : aset :=
  fun _ => false.

Definition aset_update (S : aset) (k : key) (b : bool) : aset :=
  fun x => if x =? k then b else S x.

Section Abstract.

(** Size of the key universe (keys are 1 to N) *)

Variable N : nat.

Definition elems (S : aset) : list key := filter S (seq 1 N).

(** The sequential specification (what each operation does to the set and returns) *)

Definition apply_op (o : op) (S : aset) : aset * res :=
  match o with
  | op_insert k => (aset_update S k true,  res_bool (negb (S k)))
  | op_delete k => (aset_update S k false, res_bool (S k))
  | op_find k   => (S, res_bool (S k))
  | op_size     => (S, res_nat (length (elems S)))
  | op_select r => (S, res_opt (nth_error (elems S) (r - 1)))
  end.

(** Program counter (PC) (or state) of a thread in the Abstract machine *)

Inductive PC : Type :=
  | idle
  | pending   (o : op)
  | returning (v : res).

Record aconfig : Type := AConfig {
  set : aset;
  pc : tid -> PC
}.

Definition pc_update (f : tid -> PC) (t : tid) (p : PC) : tid -> PC :=
  fun (t' : tid) => if t' =? t then p else f t'.

(** Events (part of traces) that an outside observer sees *)

Inductive event : Type :=
  | ev_invoke (t : tid) (o : op)
  | ev_return (t : tid) (v : res).

(** Actions that perform transitions in the machine *)

Inductive action : Type :=
  | act_invoke (o : op)
  | act_linearize
  | act_return.

(** No thread has started and the set is empty *)

Definition a_init : aconfig :=
  AConfig empty_aset (fun _ => idle).

(* ================================================================= *)
(** 1. Step function that is total via usage of options *)

(** One step of the abstract automaton
    None is returned when the requested action is not enabled *)

Definition anext_error (c : aconfig) (t : tid) (a : action)
                       : option (aconfig * list event) :=
  match a, c.(pc) t (* or pc c *) with
  | act_invoke o, idle =>
      Some (AConfig (set c) (pc_update (pc c) t (pending o)), [ev_invoke t o])
  | act_linearize, pending o =>
      let (S', v) := apply_op o (set c) in
      Some (AConfig S' (pc_update (pc c) t (returning v)), [])
  | act_return, returning v =>
      Some (AConfig (set c) (pc_update (pc c) t idle), [ev_return t v])
  | _, _ => None
  end.

(** Running a whole schedule (series of actions taken by threads), giving
    final config and the trace *)

Fixpoint arun_error (c : aconfig) (sched : list (tid * action))
                    : option (aconfig * list event) :=
  match sched with
  | [] => Some (c, [])
  | (t, a) :: rest =>
      match anext_error c t a with
      | None => None
      | Some (c', evs) =>
          match arun_error c' rest with
          | None => None
          | Some (c'', evs') => Some (c'', evs ++ evs')
          end
      end
  end.

Definition atrace_error (sched : list (tid * action)) : option (list event) :=
  match arun_error a_init sched with
  | None => None
  | Some (_, evs) => Some evs
  end.

(* ================================================================= *)
(** 2. A Cleaner step function where enabledness and the step are asked separately *)

Definition enabled (c : aconfig) (t : tid) (a : action) : bool :=
  match a, c.(pc) t with
  | act_invoke _, idle       => true
  | act_linearize, pending _ => true
  | act_return, returning _  => true
  | _, _                     => false
  end.

(** A step that is not enabled does nothing so the function is total without
    options *)

Definition anext (c : aconfig) (t : tid) (a : action)
                 : aconfig * list event :=
  match a, c.(pc) t with
  | act_invoke o, idle =>
      (AConfig c.(set) (pc_update c.(pc) t (pending o)), [ev_invoke t o])
  | act_linearize, pending o =>
      let (S', v) := apply_op o c.(set) in
      (AConfig S' (pc_update c.(pc) t (returning v)), [])
  | act_return, returning v =>
      (AConfig c.(set) (pc_update c.(pc) t idle), [ev_return t v])
  | _, _ => (c, [])
  end.

Fixpoint arun (c : aconfig) (sched : list (tid * action))
              : aconfig * list event :=
  match sched with
  | [] => (c, [])
  | (t, a) :: rest =>
      let (c',  evs)  := anext c t a in
      let (c'', evs') := arun c' rest in
      (c'', evs ++ evs')
  end.

Definition atrace (sched : list (tid * action)) : list event :=
  snd (arun a_init sched).

(** For a schedule to be a legal execution, each step must be enabled given 
    the reached configuration from the steps *)

Fixpoint legal (c : aconfig) (sched : list (tid * action)) : bool :=
  match sched with
  | [] => true
  | (t, a) :: rest => enabled c t a && legal (fst (anext c t a)) rest
  end.

(* ================================================================= *)
(** The two versions (1 and 2) agree *)

(** One step of (1) is one step of (2) with the enabledness *)

Lemma anext_split : forall c t a,
  anext_error c t a = if enabled c t a then Some (anext c t a) else None.
Proof.
  intros c t a. unfold anext_error, anext, enabled.
  destruct a; destruct (pc c t); try reflexivity.
  destruct (apply_op o (set c)). reflexivity.
Qed.

(** Same for a whole schedule *)

Lemma arun_split : forall sched c,
  arun_error c sched = if legal c sched then Some (arun c sched) else None.
Proof.
  induction sched as [| [t a] rest IH]; intros c; simpl.
  - reflexivity.
  - rewrite anext_split.
    destruct (enabled c t a) eqn:E; simpl.
    + destruct (anext c t a) as [c' evs] eqn:E2. simpl.
      rewrite IH. destruct (legal c' rest); simpl.
      * destruct (arun c' rest). reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

(** And at the level of traces as well *)

Lemma atrace_split : forall sched,
  atrace_error sched = if legal a_init sched then Some (atrace sched) else None.
Proof.
  intros sched. unfold atrace_error, atrace.
  rewrite arun_split. destruct (legal a_init sched).
  - destruct (arun a_init sched). reflexivity.
  - reflexivity.
Qed.

(** Legality doesn't have to be a side condition *)

(** A step that was not allowed (a stutter) is a does nothing and emits nothing *)

Lemma anext_disabled : forall c t a,
  enabled c t a = false -> anext c t a = (c, []).
Proof.
  intros c t a H. unfold enabled, anext in *.
  destruct a; destruct (c.(pc) t); simpl in *;
    try reflexivity; try discriminate.
Qed.

Fixpoint prune (c : aconfig) (sched : list (tid * action))
               : list (tid * action) :=
  match sched with
  | [] => []
  | (t, a) :: rest =>
      if enabled c t a then (t, a) :: prune (fst (anext c t a)) rest
      else prune c rest
  end.

(** Removing stutters always leaves a legal execution *)

Lemma prune_legal : forall sched c,
  legal c (prune c sched) = true.
Proof.
  induction sched as [| [t a] rest IH]; intros c; simpl.
  - reflexivity.
  - destruct (enabled c t a) eqn:E.
    + simpl. rewrite E. simpl. apply IH.
    + apply IH.
Qed.

(** Removing stutters gives the same result after a run as without removing,
    meaning no cost of removing (and this further means that every schedule
    runs like some legal schedule and legality need never appear as a hypothesis *)

Lemma prune_same : forall sched c,
  arun c (prune c sched) = arun c sched.
Proof.
  induction sched as [| [t a] rest IH]; intros c; simpl.
  - reflexivity.
  - destruct (enabled c t a) eqn:E.
    + simpl. destruct (anext c t a) as [c' evs] eqn:E2. simpl.
      rewrite IH. reflexivity.
    + rewrite (anext_disabled c t a E). simpl.
      rewrite IH. destruct (arun c rest). reflexivity.
Qed.

(* ================================================================= *)
(** 3. Step as a relation, a set of triples*)

Inductive anext_R : aconfig -> tid -> action -> list event -> aconfig -> Prop :=
  | anext_R_invoke : forall c t o,
      pc c t = idle ->
      anext_R c t (act_invoke o) [ev_invoke t o]
              (AConfig (set c) (pc_update (pc c) t (pending o)))
  | anext_R_linearize : forall c t o S' v,
      pc c t = pending o ->
      apply_op o (set c) = (S', v) ->
      anext_R c t act_linearize []
              (AConfig S' (pc_update (pc c) t (returning v)))
  | anext_R_return : forall c t v,
      pc c t = returning v ->
      anext_R c t act_return [ev_return t v]
              (AConfig (set c) (pc_update (pc c) t idle)).

(** The trace has to be a plain variable in the conclusion, with the
    concatenation as a premise, because [evs ++ evs'] cannot be matched
    against a concrete trace while [evs] is still unknown *)

Inductive arun_R : aconfig -> list (tid * action) -> list event -> aconfig -> Prop :=
  | arun_R_nil : forall c,
      arun_R c [] [] c
  | arun_R_cons : forall c t a evs c' sched evs' c'' full,
      anext_R c t a evs c' ->
      arun_R c' sched evs' c'' ->
      full = evs ++ evs' ->
      arun_R c ((t, a) :: sched) full c''.

(** A triple is in the relation exactly when the step was legal/allowed and the
    function computes it, all three versions describe one machine *)

Lemma anext_R_iff : forall c t a evs c',
  anext_R c t a evs c' <-> enabled c t a = true /\ anext c t a = (c', evs).
Proof.
  intros c t a evs c'. split.
  - intros H. inversion H; subst; unfold enabled, anext.
    + rewrite H0. split; reflexivity.
    + rewrite H0, H1. split; reflexivity.
    + rewrite H0. split; reflexivity.
  - intros [He Hn]. unfold enabled, anext in *.
    destruct a; destruct (pc c t) eqn:E; try discriminate.
    + injection Hn. intros. subst. apply anext_R_invoke. exact E.
    + destruct (apply_op o (set c)) as [S' v] eqn:E2.
      injection Hn. intros. subst.
      apply anext_R_linearize with (o := o). exact E. exact E2.
    + injection Hn. intros. subst. apply anext_R_return. exact E.
Qed.

(** Being enabled is having a state to transition to*)

Lemma enabled_iff_R : forall c t a,
  enabled c t a = true <-> exists evs c', anext_R c t a evs c'.
Proof.
  intros c t a. split.
  - intros H. exists (snd (anext c t a)), (fst (anext c t a)).
    apply anext_R_iff. split.
    + exact H.
    + destruct (anext c t a). reflexivity.
  - intros [evs [c' H]]. apply anext_R_iff in H. destruct H as [H _]. exact H.
Qed.

End Abstract.

(* ################################################################# *)
(** Example executions / test cases *)

(** Here 4 is the N Variable from above and is required as an argument  because
    elem uses it, which is used by apply_op, which by anext, which by arun, and
    thus by atrace *)

(** Step (1) on a genuinely interleaved schedule *)

Example arun_error_example1 :
  atrace_error 4 [ (1, act_invoke (op_insert 3));
                   (2, act_invoke (op_insert 1));
                   (1, act_linearize);
                   (2, act_linearize);
                   (3, act_invoke op_size);
                   (2, act_return);
                   (3, act_linearize);
                   (1, act_return);
                   (3, act_return) ]
  = Some [ ev_invoke 1 (op_insert 3);
           ev_invoke 2 (op_insert 1);
           ev_invoke 3 op_size;
           ev_return 2 (res_bool true);
           ev_return 1 (res_bool true);
           ev_return 3 (res_nat 2) ].
Proof. reflexivity. Qed.

(** thread 1 returns before it has invoked anything, so no run *)

Example arun_error_example2 :
  atrace_error 4 [ (1, act_return) ] = None.
Proof. reflexivity. Qed.

(** With step (2) *)

Example arun_example1 :
  let sched := [ (1, act_invoke (op_insert 3));
                 (2, act_invoke (op_insert 1));
                 (1, act_linearize);
                 (2, act_linearize);
                 (3, act_invoke op_size);
                 (2, act_return);
                 (3, act_linearize);
                 (1, act_return);
                 (3, act_return) ] in
  legal 4 a_init sched = true
  /\ atrace 4 sched = [ ev_invoke 1 (op_insert 3);
                        ev_invoke 2 (op_insert 1);
                        ev_invoke 3 op_size;
                        ev_return 2 (res_bool true);
                        ev_return 1 (res_bool true);
                        ev_return 3 (res_nat 2) ].
Proof. split; reflexivity. Qed.

Example arun_example2 :
  legal 4 a_init [ (1, act_return) ] = false /\ atrace 4 [ (1, act_return) ] = [].
Proof. split; reflexivity. Qed.

Example arun_example3 :
  let sched := [ (1, act_invoke (op_insert 3));
                 (2, act_return);                (* thread 2 never invoked *)
                 (1, act_linearize);
                 (1, act_return) ] in
  legal 4 a_init sched = false
  /\ atrace 4 sched = [ ev_invoke 1 (op_insert 3);
                        ev_return 1 (res_bool true) ]
  /\ atrace_error 4 sched = None.
Proof. repeat split; reflexivity. Qed.

Example prune_example :
  let sched := [ (1, act_invoke (op_insert 3));
                 (2, act_return);
                 (1, act_linearize);
                 (1, act_return) ] in
  prune 4 a_init sched = [ (1, act_invoke (op_insert 3));
                           (1, act_linearize);
                           (1, act_return) ]
  /\ legal 4 a_init (prune 4 a_init sched) = true
  /\ atrace 4 (prune 4 a_init sched) = atrace 4 sched.
Proof. repeat split; reflexivity. Qed.

(** With step (3), the relation *)

Example arun_R_example1 : exists c,
  arun_R 4 a_init
    [ (1, act_invoke (op_insert 3));
      (1, act_linearize);
      (1, act_return) ]
    [ ev_invoke 1 (op_insert 3);
      ev_return 1 (res_bool true) ]
    c.
Proof.
  eexists.
  eapply arun_R_cons.
  - apply anext_R_invoke. reflexivity.
  - eapply arun_R_cons.
    + eapply anext_R_linearize.
      * reflexivity.
      * reflexivity.
    + eapply arun_R_cons.
      * apply anext_R_return. reflexivity.
      * apply arun_R_nil.
      * reflexivity.
    + reflexivity.
  - reflexivity. 

(* 
  eexists.
  repeat (eapply arun_R_cons; [ econstructor; reflexivity | | ]).
  apply arun_R_nil.
  all: reflexivity.
*)
Qed.

(** Invalid schedule example *)

Example arun_R_example2 : forall evs c',
  ~ anext_R 4 a_init 1 act_return evs c'.
Proof. intros evs c' H. inversion H. discriminate. Qed.