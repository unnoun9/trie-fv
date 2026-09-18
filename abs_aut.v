From Stdlib Require Export Arith.
From Stdlib Require Export List.
From Stdlib Require Export Lia.
Export ListNotations.

(* ################################################################# *)
(** * The Abstract Implementation *)

(** Thread identifiers and keys are both just natural numbers. They are given
    names of their own so that a signature says which one it means *)

Definition tid := nat.
Definition key := nat.

(** upd f x a is the function f with its value at the single point x replaced
    by a, and every other point left alone.

    Arguments: f the function being updated, x the point to change, a the new
    value there. Returns the updated function.

    Every mutable map in this project is a function of nat, whether
    it holds a set of keys or the state of each thread, and this one updater
    serves all of them *)

Definition upd {A : Type} (f : nat -> A) (x : nat) (a : A) : nat -> A :=
  fun y => if y =? x then a else f y.

(** The operations of the set abstract data type.

    op_insert k, op_delete k and op_find k carry the key they are about.
    op_select r carries the rank being asked for. op_rank k asks how many
    keys are at most k. op_size and op_snapshot carry nothing, because they
    are about the whole component *)

Inductive op : Type :=
  | op_insert (k : key)
  | op_delete (k : key)
  | op_find   (k : key)
  | op_size
  | op_select (r : nat)
  | op_rank   (k : key)
  | op_snapshot.

(** Results for returning from an opertation.

    res_bool is what insert, delete and find give back, res_nat what size and
    rank give, res_opt what select gives, None when the rank is out of range,
    and res_set what snapshot gives *)

Inductive res : Type :=
  | res_bool (b : bool)
  | res_nat  (n : nat)
  | res_opt  (o : option key)
  | res_set  (l : list key).

(** Events that an outside observer sees. ev_invoke t o records that thread t
    announced operation o, and ev_return t v that thread t handed back the
    value v. A trace is a list of these, and linearizability would be a statement. *)

Inductive event : Type :=
  | ev_invoke (t : tid) (o : op)
  | ev_return (t : tid) (v : res).

(** The alphabet of transitions. act_invoke o announces an operation,
    act_step is the one internal action, and act_return hands the answer
    back.

    Both machines use this same alphabet, so a concrete schedule and an
    abstract schedule have the same type need. In this machine act_step
    is the linearization point; in the concrete machine it is one memory access *)

Inductive action : Type :=
  | act_invoke (o : op)
  | act_step
  | act_return.

(** The abstract set itself, as a characteristic function where `set k` is true
    exactly when k is in the set *)

Definition abs_set := key -> bool.

(** The set holding nothing *)

Definition empty_abs_set : abs_set :=
  fun _ => false.

(** Everything from here on is parametrized by the interval i..j that this
    component covers, so queries such as size, select, rank and snapshot are
    relative to that interval, litting the same machine describe every
    recursive child. *)

(** in_interval i j k says whether the key k is covered by some i and j.

    Arguments: i and j the bounds, k the key. Returns true exactly when
    i <= k <= j *)

Definition in_interval (i j : nat) (k : key) : bool :=
  andb (i <=? k) (k <=? j).

(** Which operations this component will take.

    Arguments: i and j the interval, o the operation. Returns true when the
    component is allowed to run o.

    An operation carrying a key is taken only if the key is one of ours. The
    rest are always taken, because they are about the component as a whole
    and every component can answer them about itself *)

Definition op_ok (i j : nat) (o : op) : bool :=
  match o with
  | op_insert k
  | op_delete k
  | op_find k
  | op_rank k   => in_interval i j k
  | op_size
  | op_select _
  | op_snapshot => true
  end.

(** `abs_elems i j set` is the list of keys of the set that lie in i..j.

    Arguments: i and j the interval, set the characteristic function.
    Returns the list in increasing order, since seq produces the keys in
    order and filter preserves that order.

    Every query answer is some view of this list, which is why it is worth
    naming *)

Definition abs_elems (i j : nat) (set : abs_set) : list key :=
  filter set (seq i (j - i + 1)).

(** abs_rank i j set k counts how many of the component's keys are at most k.

    Arguments: i and j the interval, set the characteristic function, k the
    key being ranked. Returns that count *)

Definition abs_rank (i j : nat) (set : abs_set) (k : key) : nat :=
  length (filter (fun x => x <=? k) (abs_elems i j set)).

(** The sequential specification; what one operation does to the set, and
    what it returns.

    Arguments: i and j the interval, o the operation, set the current
    contents. Returns a pair of the set afterwards and the result.

    This is the entire meaning of the data structure. act_step in the machine
    below is exactly one call to this function, which is what makes that step
    the linearization point *)

Definition abs_apply_op (i j : nat) (o : op) (set : abs_set) : abs_set * res :=
  match o with
  | op_insert k => (upd set k true,  res_bool (negb (set k)))
  | op_delete k => (upd set k false, res_bool (set k))
  | op_find k   => (set, res_bool (set k))
  | op_size     => (set, res_nat (length (abs_elems i j set)))
  | op_select r => (set, res_opt (nth_error (abs_elems i j set) (r - 1)))
  | op_rank k   => (set, res_nat (abs_rank i j set k))
  | op_snapshot => (set, res_set (abs_elems i j set))
  end.

(** Where a thread is in the abstract machine; its program counter together
    with whatever it is carrying there.

    a_idle means it has nothing running. a_pending o means it announced o but
    has not linearized yet. a_returning v means it has linearized and owes
    the answer v *)

Inductive abs_progstate : Type :=
  | a_idle
  | a_pending   (o : op)
  | a_returning (v : res).

(** A configuration of the abstract machine, the whole state at one moment. *)

Record abs_config : Type := AbsConfig {
  set       : abs_set;
  astate : tid -> abs_progstate
}.

(** The starting configuration where the set is empty and no thread has begun *)

Definition abs_init : abs_config :=
  AbsConfig empty_abs_set (fun _ => a_idle).

(* ================================================================= *)
(** ** 1. Step function that is total via usage of options *)

(** Version 1 of the one step of the abstract machine where invalid steps not
    allowed are reported via an option.

    Arguments: i and j the interval, c the configuration, t the thread taking
    the step, a the action it takes. Returns None when a is not allowed from
    c, and otherwise Some of the configuration afterwards paired with the
    events emitted, which is one event for an invoke or a return and none for
    the internal step *)

Definition abs_next_opt (i j : nat) (c : abs_config) (t : tid) (a : action)
                          : option (abs_config * list event) :=
  match a, c.(astate) t with
  | act_invoke o, a_idle =>
      if op_ok i j o
      then Some (AbsConfig c.(set) (upd c.(astate) t (a_pending o)),
                 [ev_invoke t o])
      else None
  | act_step, a_pending o =>
      let (set', v) := abs_apply_op i j o c.(set) in
      Some (AbsConfig set' (upd c.(astate) t (a_returning v)), [])
  | act_return, a_returning v =>
      Some (AbsConfig c.(set) (upd c.(astate) t a_idle), [ev_return t v])
  | _, _ => None
  end.

(** Version 1 run over a whole schedule.

    Arguments: i and j the interval, c the starting configuration, sched a
    list of thread and action pairs in the order they happen. Returns None as
    soon as any step is disallowed, and otherwise Some of the final
    configuration paired with the trace, which is the events of every step
    concatenated in order *)

Fixpoint abs_run_opt (i j : nat) (c : abs_config) (sched : list (tid*action))
                       : option (abs_config * list event) :=
  match sched with
  | [] => Some (c, [])
  | (t, a) :: rest =>
      match abs_next_opt i j c t a with
      | None => None
      | Some (c', evs) =>
          match abs_run_opt i j c' rest with
          | None => None
          | Some (c'', evs') => Some (c'', evs ++ evs')
          end
      end
  end.

(** Version 1 started from abs_init, keeping only the trace.

    Arguments: i and j the interval, sched the schedule. Returns None when
    the schedule is not legal, and otherwise Some of its trace *)

Definition abs_trace_opt (i j : nat) (sched : list (tid*action))
                           : option (list event) :=
  match abs_run_opt i j abs_init sched with
  | None => None
  | Some (_, evs) => Some evs
  end.

(* ================================================================= *)
(** ** 2. A cleaner step function where enabledness and the step are asked separately *)

(** Whether thread t is allowed to take action a from configuration c.

    Arguments: i and j the interval, c the configuration, t the thread, a the
    action. Returns a bool. A thread may invoke only when idle, and only an
    operation this component owns; may step only when it has one pending; and
    may return only when it owes an answer *)

Definition abs_enabled (i j : nat) (c : abs_config) (t : tid) (a : action) : bool :=
  match a, c.(astate) t with
  | act_invoke o, a_idle      => op_ok i j o
  | act_step, a_pending _     => true
  | act_return, a_returning _ => true
  | _, _                      => false
  end.

(** One step of the abstract machine, version 2.

    Same arguments as abs_next_opt, but it returns a pair rather than an
    option. A step that is not allowed is a stutter, leaving the
    configuration alone and emitting nothing. That keeps the function total
    without an option, at the cost of having to ask abs_enabled separately
    whenever legality matters *)

Definition abs_next (i j : nat) (c : abs_config) (t : tid) (a : action)
                    : abs_config * list event :=
  match a, c.(astate) t with
  | act_invoke o, a_idle =>
      if op_ok i j o
      then (AbsConfig c.(set) (upd c.(astate) t (a_pending o)),
            [ev_invoke t o])
      else (c, [])
  | act_step, a_pending o =>
      let (set', v) := abs_apply_op i j o c.(set) in
      (AbsConfig set' (upd c.(astate) t (a_returning v)), [])
  | act_return, a_returning v =>
      (AbsConfig c.(set) (upd c.(astate) t a_idle), [ev_return t v])
  | _, _ => (c, [])
  end.

(** Version 2 run over a whole schedule.

    Arguments: i and j the interval, c the starting configuration, sched the
    schedule. Returns the final configuration paired with the trace. There is
    no failure case, since a disallowed step simply contributes nothing *)

Fixpoint abs_run (i j : nat) (c : abs_config) (sched : list (tid*action))
                 : abs_config * list event :=
  match sched with
  | [] => (c, [])
  | (t, a) :: rest =>
      let (c',  evs)  := abs_next i j c t a in
      let (c'', evs') := abs_run i j c' rest in
      (c'', evs ++ evs')
  end.

(** The trace of a run, throwing the final configuration away.

    Arguments: i and j the interval, c the starting configuration, sched the
    schedule. Returns the list of events. *)

Definition abs_trace_from (i j : nat) (c : abs_config)
                          (sched : list (tid*action)) : list event :=
  snd (abs_run i j c sched).

(** The same starting from abs_init, which is the set of traces the concrete
    machine will have to be shown to stay inside *)

Definition abs_trace (i j : nat) (sched : list (tid*action)) : list event :=
  abs_trace_from i j abs_init sched.

(** Whether a schedule is a legal execution.

    Arguments: i and j the interval, c the starting configuration, sched the
    schedule. Returns true when every step is enabled at the moment it is
    reached. It runs the machine it goes. *)

Fixpoint abs_legal (i j : nat) (c : abs_config) (sched : list (tid*action)) : bool :=
  match sched with
  | [] => true
  | (t, a) :: rest =>
      abs_enabled i j c t a && abs_legal i j (fst (abs_next i j c t a)) rest
  end.

(* ================================================================= *)
(** ** The two versions 1 and 2 agree *)

(** One step of version 1 is one step of version 2 together with the
    enabledness test.

      abs_next_opt c t a = Some (abs_next c t a)   when abs_enabled c t a
      abs_next_opt c t a = None                    otherwise

    so version 1 carries no extra information and only bundles enabledness
    into the return value *)

Lemma abs_next_split : forall (i j : nat) (c : abs_config) (t : tid) (a : action),
  abs_next_opt i j c t a
  = if abs_enabled i j c t a then Some (abs_next i j c t a) else None.
Proof.
  intros i j c t a. unfold abs_next_opt, abs_next, abs_enabled.
  destruct a; destruct (c.(astate) t); try reflexivity.
  - destruct (op_ok i j o); reflexivity.
  - destruct (abs_apply_op i j o c.(set)). reflexivity.
Qed.

(** The same at the level of a whole schedule.*)

Lemma abs_run_split : forall (i j : nat) (sched : list (tid*action)) (c : abs_config),
  abs_run_opt i j c sched
  = if abs_legal i j c sched then Some (abs_run i j c sched) else None.
Proof.
  intros i j sched.
  induction sched as [| [t a] rest IH]; intros c; simpl.
  - reflexivity.
  - rewrite abs_next_split.
    destruct (abs_enabled i j c t a) eqn:E; simpl.
    + destruct (abs_next i j c t a) as [c' evs] eqn:E2. simpl.
      rewrite IH. destruct (abs_legal i j c' rest); simpl.
      * destruct (abs_run i j c' rest). reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

(** And also at the level of traces *)

Lemma abs_trace_split : forall (i j : nat) (sched : list (tid*action)),
  abs_trace_opt i j sched
  = if abs_legal i j abs_init sched then Some (abs_trace i j sched) else None.
Proof.
  intros i j sched. unfold abs_trace_opt, abs_trace, abs_trace_from.
  rewrite abs_run_split. destruct (abs_legal i j abs_init sched).
  - destruct (abs_run i j abs_init sched). reflexivity.
  - reflexivity.
Qed.

(* ================================================================= *)
(** ** Legality does not have to be a side condition *)

(** A step that was not allowed does nothing at all. *)

Lemma abs_next_disabled : forall (i j : nat) (c : abs_config) (t : tid) (a : action),
  abs_enabled i j c t a = false -> abs_next i j c t a = (c, []).
Proof.
  intros i j c t a H. unfold abs_enabled, abs_next in *.
  destruct a; destruct (c.(astate) t); simpl in *;
    try reflexivity; try discriminate.
  destruct (op_ok i j o) eqn:E; simpl in *;
    try discriminate; reflexivity.
Qed.

(** Deleting the stutters from a schedule.

    Arguments: i and j the interval, c the starting configuration, sched the
    schedule. Returns the sublist of sched holding just the steps that were
    enabled at the moment they were reached. *)

Fixpoint abs_prune (i j : nat) (c : abs_config) (sched : list (tid*action))
                   : list (tid*action) :=
  match sched with
  | [] => []
  | (t, a) :: rest =>
      if abs_enabled i j c t a
      then (t, a) :: abs_prune i j (fst (abs_next i j c t a)) rest
      else abs_prune i j c rest
  end.

(** Pruning always produces a legal schedule, with no hypothesis at all on
    the schedule it started from *)

Lemma abs_prune_legal : forall (i j : nat) (sched : list (tid*action)) (c : abs_config),
  abs_legal i j c (abs_prune i j c sched) = true.
Proof.
  intros i j sched.
  induction sched as [| [t a] rest IH]; intros c; simpl.
  - reflexivity.
  - destruct (abs_enabled i j c t a) eqn:E.
    + simpl. rewrite E. simpl. apply IH.
    + apply IH.
Qed.

(** and pruning costs nothing, meaning the pruned schedule lands in the same
    configuration with the same trace as the original.

    Together with abs_prune_legal this says every schedule behaves like some
    legal schedule, which is why legality never has to be carried around as a
    hypothesis *)

Lemma abs_prune_same : forall (i j : nat) (sched : list (tid*action)) (c : abs_config),
  abs_run i j c (abs_prune i j c sched) = abs_run i j c sched.
Proof.
  intros i j sched.
  induction sched as [| [t a] rest IH]; intros c; simpl.
  - reflexivity.
  - destruct (abs_enabled i j c t a) eqn:E.
    + simpl. destruct (abs_next i j c t a) as [c' evs] eqn:E2. simpl.
      rewrite IH. reflexivity.
    + rewrite (abs_next_disabled i j c t a E). simpl.
      rewrite IH. destruct (abs_run i j c rest). reflexivity.
Qed.

(* ================================================================= *)
(** ** 3. Step as a relation *)

(** One step of the abstract machine, version 3, as a relation instead of a
    function. abs_next_R i j c t a evs c' holds when thread t taking action a
    from c is allowed, lands in c', and emits evs.

    There is one constructor per allowed step and no constructor at all for a
    disallowed one, so where the function stutters the relation simply has no
    tuple. That is the difference between the two, and abs_next_R_iff below
    says it is the only one *)

Inductive abs_next_R (i j : nat)
  : abs_config -> tid -> action -> list event -> abs_config -> Prop :=
  | abs_next_R_invoke : forall (c : abs_config) (t : tid) (o : op),
      c.(astate) t = a_idle ->
      op_ok i j o = true ->
      abs_next_R i j c t (act_invoke o) [ev_invoke t o]
        (AbsConfig c.(set) (upd c.(astate) t (a_pending o)))
  | abs_next_R_linearize : forall (c : abs_config) (t : tid) (o : op)
                                  (set' : abs_set) (v : res),
      c.(astate) t = a_pending o ->
      abs_apply_op i j o c.(set) = (set', v) ->
      abs_next_R i j c t act_step []
        (AbsConfig set' (upd c.(astate) t (a_returning v)))
  | abs_next_R_return : forall (c : abs_config) (t : tid) (v : res),
      c.(astate) t = a_returning v ->
      abs_next_R i j c t act_return [ev_return t v]
        (AbsConfig c.(set) (upd c.(astate) t a_idle)).

(** Version 3 over a whole schedule. abs_run_R i j c sched evs c' holds when
    running sched from c is legal throughout, ends in c', and emits evs.

    abs_run_R_cons takes the trace as a plain variable full and states
    full = evs ++ evs' as a premise, rather than writing evs ++ evs' in the
    conclusion. That is needed because evs ++ evs' cannot be matched against
    a written out trace while evs is still unknown *)

Inductive abs_run_R (i j : nat)
  : abs_config -> list (tid*action) -> list event -> abs_config -> Prop :=
  | abs_run_R_nil : forall (c : abs_config),
      abs_run_R i j c [] [] c
  | abs_run_R_cons : forall (c : abs_config) (t : tid) (a : action)
                            (evs : list event) (c' : abs_config)
                            (sched : list (tid*action))
                            (evs' : list event) (c'' : abs_config)
                            (full : list event),
      abs_next_R i j c t a evs c' ->
      abs_run_R i j c' sched evs' c'' ->
      full = evs ++ evs' ->
      abs_run_R i j c ((t, a) :: sched) full c''.

(** Versions 2 and 3 are the same machine as well. A tuple is in the relation
    exactly when the step was enabled and the function computes it. *)

Lemma abs_next_R_iff : forall (i j : nat) (c : abs_config) (t : tid) (a : action)
                              (evs : list event) (c' : abs_config),
  abs_next_R i j c t a evs c'
  <-> abs_enabled i j c t a = true /\ abs_next i j c t a = (c', evs).
Proof.
  intros i j c t a evs c'. split.
  - intros H. inversion H; subst; unfold abs_enabled, abs_next.
    + rewrite H0, H1. split; reflexivity.
    + rewrite H0, H1. split; reflexivity.
    + rewrite H0. split; reflexivity.
  - intros [He Hn]. unfold abs_enabled, abs_next in *.
    destruct a; destruct (c.(astate) t) eqn:E; try discriminate.
    + destruct (op_ok i j o) eqn:Ho; try discriminate.
      injection Hn. intros. subst.
      apply abs_next_R_invoke.
      * exact E.
      * exact Ho.
    + destruct (abs_apply_op i j o c.(set)) as [set' v] eqn:E2.
      injection Hn. intros. subst.
      apply abs_next_R_linearize with (o := o). exact E. exact E2.
    + injection Hn. intros. subst. apply abs_next_R_return. exact E.
Qed.

(** Being enabled is exactly having somewhere to go: abs_enabled answers true
    at c, t, a precisely when the relation has at least one outgoing tuple
    there *)

Lemma abs_enabled_iff_R : forall (i j : nat) (c : abs_config) (t : tid) (a : action),
  abs_enabled i j c t a = true
  <-> exists (evs : list event) (c' : abs_config), abs_next_R i j c t a evs c'.
Proof.
  intros i j c t a. split.
  - intros H. exists (snd (abs_next i j c t a)), (fst (abs_next i j c t a)).
    apply abs_next_R_iff. split.
    + exact H.
    + destruct (abs_next i j c t a). reflexivity.
  - intros [evs [c' H]]. apply abs_next_R_iff in H. destruct H as [H _]. exact H.
Qed.
