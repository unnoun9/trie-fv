From Stdlib Require Export Arith.
From Stdlib Require Export List.
From Stdlib Require Export Lia.
Export ListNotations.

(*  ###############################################################  *)
(*  The Abstract Implementation  *)

(*  Thread identifiers and keys are both just natural numbers.  *)

Definition tid := nat.
Definition key := nat.

(*  upd f x a is the function f with its value at the single point x replaced
    by a, and every other point left alone. The purpose here is to update any
    characteristic function whose keys map a nat to some type.

    Arguments: f the function being updated, x the point to change, a the new
    value there. Returns the updated function.  *)

Definition upd {A : Type} (f : nat -> A) (x : nat) (a : A) : nat -> A :=
  fun y => if y =? x then a else f y.

(*  The operations of the set abstract data type.

    op_insert k, op_delete k and op_find k carry the key they are about.
    op_select r carries the rank being asked for. op_rank k asks how many
    keys are at most k. op_size and op_snapshot carry nothing, because they
    are about the whole component  *)

Inductive op : Type :=
  | op_insert (k : key)
  | op_delete (k : key)
  | op_find   (k : key)
  | op_size
  | op_select (r : nat)
  | op_rank   (k : key)
  | op_snapshot.

(*  Results for returning from an operation.

    res_bool is what insert, delete and find give back, res_nat what size and
    rank give, res_opt what select gives, None when the rank is out of range,
    and res_set what snapshot gives  *)

Inductive res : Type :=
  | res_bool (b : bool)
  | res_nat  (n : nat)
  | res_opt  (o : option key)
  | res_set  (l : list key).

(*  Events that an outside observer sees. ev_invoke t o records that thread t
    announced operation o, and ev_return t v that thread t returned back the
    value v. A trace is a list of these, and linearizability is a statement
    about traces alone  *)

Inductive event : Type :=
  | ev_invoke (t : tid) (o : op)
  | ev_return (t : tid) (v : res).

(*  The alphabet of transitions. act_invoke o announces an operation,
    act_step is the one internal action, and act_return hands the answer
    back.

    Both machines use this same alphabet, so a concrete execution and an
    abstract execution have the same type, which the simulation needs. In
    this machine act_step is the linearization point; in the concrete machine
    it is one memory access  *)

Inductive action : Type :=
  | act_invoke (o : op)
  | act_step
  | act_return.

(*  Three names for the three lists that describe a run of the machine.

    A schedule says only whose turn it is next with no information about
    what a thread will do with its turn.

    A program is the order of operations the thread is to do or invoke
    (like a real program written in a programming language).

    An execution tells what action each thread performed in order, consulted by
    and contructed carefully via schedules and programs. It is the list consumed
    by the step function to give the trace and the final configuration (a run).  *)

(*  The only thing in this development that ever builds an execution is
    abs_exec further down. That is deliberate. An execution written out by
    hand can say things the machine could never do, such as a thread returning 
    back an answer without anyone invoking an operation from it, whereas an
    execution that abs_exec builds is always something the machine really could
    have performed. That is the content of abs_exec_legal, and it is why no result
    below ever has to argue that a disallowed step would have been harmless  *)

Definition sched     := list tid.
Definition progs     := tid -> list op.
Definition execution := list (tid * action).

(*  The abstract set itself, as a characteristic function where `set k` is true
    exactly when k is in the set  *)

Definition abs_set := key -> bool.

(*  The abstract set holding nothing  *)

Definition empty_abs_set : abs_set :=
  fun _ => false.

(*  Below here, everything is parametrized by the interval i..j that this
    component covers, including queries and updates being relative to that
    interval, letting the same machine describe every recursive child.  *)

(*  in_interval i j k says whether the key k is covered by some i and j.

    Arguments: i and j the bounds, k the key. Returns true exactly when
    i <= k <= j  *)

Definition in_interval (i j : nat) (k : key) : bool :=
  andb (i <=? k) (k <=? j).

(*  Tells whether an operation is valid or OK for a given interval.

    Arguments: i and j the interval, o the operation. Returns true when the
    component is allowed to run o.

    A key must lie in the interval. A rank must be at least 1, since ranks
    count from one. The paper's Select(k) asks for the kth smallest key and
    says nothing about k = 0, and on 0 its code walks to the leftmost leaf
    and returns that key whether it is in the set or not.  *)

Definition op_ok (i j : nat) (o : op) : bool :=
  match o with
  | op_insert k
  | op_delete k
  | op_find k
  | op_rank k   => in_interval i j k
  | op_select r => 1 <=? r
  | op_size
  | op_snapshot => true
  end.

(*  `abs_elems i j set` is the list of keys of the set that lie in i..j.

    Arguments: i and j the interval, set the characteristic function.
    Returns the list in increasing order, since seq produces the keys in
    order and filter preserves that order.  *)

Definition abs_elems (i j : nat) (set : abs_set) : list key :=
  filter set (seq i (j - i + 1)).

(*  abs_rank i j set k counts how many of the component's keys are at most k.

    Arguments: i and j the interval, set the characteristic function, k the
    key being ranked. Returns that count  *)

Definition abs_rank (i j : nat) (set : abs_set) (k : key) : nat :=
  length (filter (fun x => x <=? k) (abs_elems i j set)).

(*  The sequential specification; what one operation does to the set, and
    what it returns.

    Arguments: i and j the interval, o the operation, set the current
    contents. Returns a pair of the set afterwards and the result.

    This is the entire meaning of the data structure. act_step in the machine
    below is exactly one call to this function, making that step the linearization
    point  *)

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

(*  Where a thread is in the abstract machine; its program counter together
    with whatever (local variables, and important information) it is carrying there.

    a_idle means it has nothing running. a_pending o means it announced o but
    has not linearized yet. a_returning v means it has linearized and owes
    the answer v  *)

Inductive abs_progstate : Type :=
  | a_idle
  | a_pending   (o : op)
  | a_returning (v : res).

(*  A configuration of the abstract machine, the whole state at one moment.  *)

Record abs_config : Type := AbsConfig {
  set       : abs_set;
  astate : tid -> abs_progstate
}.

(*  The starting configuration where the set is empty and no thread has begun  *)

Definition abs_init : abs_config :=
  {| set := empty_abs_set; astate := fun _ => a_idle |}.

(*  ===============================================================  *)
(*  The step and the run  *)

(*  Whether a step is allowed and what it does are asked separately, by
    abs_enabled and abs_next. This shape was chosen because abs_next is then a
    plain total function. Two other possible shapes are in abs_next_versions.v  *)

(*  Whether thread t is allowed to take action a from configuration c.

    Arguments: i and j the interval, c the configuration, t the thread, a the
    action. Returns a bool. A thread may invoke only when idle with the invoked
    operation being valid; may step only when it has one pending; and
    may return only when it owes an answer  *)

Definition abs_enabled (i j : nat) (c : abs_config) (t : tid) (a : action) : bool :=
  match a, c.(astate) t with
  | act_invoke o, a_idle      => op_ok i j o
  | act_step, a_pending _     => true
  | act_return, a_returning _ => true
  | _, _                      => false
  end.

(*  One step of the abstract machine.

    Arguments: i and j the interval, c the configuration, t the thread taking
    the step, a the action it takes. Returns the configuration afterwards
    paired with the events emitted, which is one event for an invoke or a
    return and none for the internal step. A step that is not allowed is a
    stutter, leaving the configuration alone and emitting nothing  *)

Definition abs_next (i j : nat) (c : abs_config) (t : tid) (a : action)
                    : abs_config * list event :=
  match a, c.(astate) t with
  | act_invoke o, a_idle =>
      if op_ok i j o
      then ({| set    := c.(set);
               astate := upd c.(astate) t (a_pending o) |},
            [ev_invoke t o])
      else (c, [])
  | act_step, a_pending o =>
      let (set', v) := abs_apply_op i j o c.(set) in
      ({| set    := set';
          astate := upd c.(astate) t (a_returning v) |}, [])
  | act_return, a_returning v =>
      ({| set    := c.(set);
          astate := upd c.(astate) t a_idle |}, [ev_return t v])
  | _, _ => (c, [])
  end.

(*  A run over a whole execution.

    Arguments: i and j the interval, c the starting configuration, e the
    execution. Returns the final configuration paired with the trace. There
    is no failure case, since a disallowed step simply contributes nothing  *)

Fixpoint abs_run (i j : nat) (c : abs_config) (e : execution)
                 : abs_config * list event :=
  match e with
  | [] => (c, [])
  | (t, a) :: rest =>
      let (c',  evs)  := abs_next i j c t a in
      let (c'', evs') := abs_run i j c' rest in
      (c'', evs ++ evs')
  end.

(*  The trace of a run, throwing the final configuration away.

    Arguments: i and j the interval, c the starting configuration, e the
    execution. Returns the list of events.  *)

Definition abs_trace_from (i j : nat) (c : abs_config) (e : execution)
                          : list event :=
  snd (abs_run i j c e).

(*  Whether an execution is legal.

    Arguments: i and j the interval, c the starting configuration, e the
    execution. Returns true when every step is enabled at the moment it is
    reached. It runs the machine as it goes.  *)

Fixpoint abs_legal (i j : nat) (c : abs_config) (e : execution) : bool :=
  match e with
  | [] => true
  | (t, a) :: rest =>
      abs_enabled i j c t a && abs_legal i j (fst (abs_next i j c t a)) rest
  end.

(*  A step that was not allowed does nothing at all.  *)

Lemma abs_next_disabled : forall (i j : nat) (c : abs_config) (t : tid) (a : action),
  abs_enabled i j c t a = false -> abs_next i j c t a = (c, []).
Proof.
  intros i j c t a H. unfold abs_enabled, abs_next in *.
  destruct a; destruct (c.(astate) t); simpl in *;
    try reflexivity; try discriminate.
  destruct (op_ok i j o) eqn:E; simpl in *;
    try discriminate; reflexivity.
Qed.

(*  A program may only ask for operations this component owns. The execution
    generation can't guarantee this one thing.

    Arguments: i and j the interval, P the programs. Returns a Prop  *)

Definition wf_progs (i j : nat) (P : progs) : Prop :=
  forall (t : tid) (o : op), In o (P t) -> op_ok i j o = true.

(*  A thread that already has an operation running has no choice about what
    it does next. A thread that owes an answer gives it, and a thread that
    has announced an operation takes its internal step.

    Argument: p the thread's state. Returns that forced action, or None when
    the thread is idle, which means it has nothing running and must start
    something from its program instead  *)

Definition abs_busy_act (p : abs_progstate) : option action :=
  match p with
  | a_idle        => None
  | a_pending _   => Some act_step
  | a_returning _ => Some act_return
  end.

(*  Turning a schedule and the programs into an execution.

    Arguments: i and j the interval, c the configuration it all starts from,
    sigma the schedule, P what each thread still has to do. Returns the
    corresponding execution.

    Look at each thread in the schedule. If the current thread is busy, then
    its forced action is the answer. If the current thread is idle instead,
    then find its next operation from it's program, drop it from the program
    (so cannot be called twice), and that is the invokation of that operation
    is the answer. If the program is empty instead, then that thread's turn is
    ignored abd tge confguration is untouched.  *)

Fixpoint abs_exec (i j : nat) (c : abs_config) (sigma : sched) (P : progs)
                  : execution :=
  match sigma with
  | [] => []
  | t :: rest =>
      match abs_busy_act (c.(astate) t) with
      | Some a =>
          (t, a) :: abs_exec i j (fst (abs_next i j c t a)) rest P
      | None =>
          match P t with
          | []      => abs_exec i j c rest P
          | o :: os =>
              (t, act_invoke o)
              :: abs_exec i j (fst (abs_next i j c t (act_invoke o)))
                   rest (upd P t os)
          end
      end
  end.

(*  Finally, all the corresponding executions from any schedule and wf
    programs are legal.

    There is no hypothesis on sigma whatsoever. An execution that could never
    happen, cannot be written down.  *)

Theorem abs_exec_legal : forall (i j : nat) (c : abs_config)
                                (sigma : sched) (P : progs),
  wf_progs i j P -> abs_legal i j c (abs_exec i j c sigma P) = true.
Proof.
  intros i j c sigma. revert c.
  induction sigma as [| t rest IH]; intros c P HP.
  - simpl. reflexivity.
  - simpl. destruct (abs_busy_act (astate c t)) as [act |] eqn:Eb.
    + simpl.
      assert (Hen : abs_enabled i j c t act = true).
      { unfold abs_busy_act in Eb. unfold abs_enabled.
        destruct (astate c t); inversion Eb; subst; reflexivity. }
      rewrite Hen. simpl. apply IH. exact HP.
    + destruct (P t) as [| o os] eqn:EP.
      * apply IH. exact HP.
      * simpl.
        assert (Hidle : astate c t = a_idle).
        { unfold abs_busy_act in Eb. destruct (astate c t); congruence. }
        assert (Hok : op_ok i j o = true).
        { apply (HP t). rewrite EP. now left. }
        rewrite Hidle, Hok. simpl. apply IH.
        intros t' o' Hin. unfold upd in Hin.
        destruct (t' =? t) eqn:Et.
        -- apply (HP t). rewrite EP. right. easy.
        -- apply (HP t'). exact Hin.
Qed.

(*  The trace of a schedule is the trace of the corresponding execution. This
    is the form every result about the abstract automata is stated in, because
    here built executions are seen rather than written by hand.

    Arguments: i and j the interval, c the starting configuration, sigma the
    schedule, P the programs. Returns the list of events  *)

Definition abs_trace (i j : nat) (c : abs_config) (sigma : sched) (P : progs)
                     : list event :=
  abs_trace_from i j c (abs_exec i j c sigma P).
