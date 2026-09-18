From Trie Require Import abs_aut.

(* ################################################################# *)
(** * The concrete implementation *)

(** mid i j is where the interval i..j splits: the left child takes
    i..mid i j and the right child takes mid i j + 1..j.

    Arguments: i and j the bounds. Returns the floor of their average *)

Definition mid (i j : nat) : nat := (i + j) / 2.

(* ================================================================= *)
(** ** Arithmetic facts about mid *)

(** Division fact the other four rest on. (just the division definition unfolded)

      i + j = 2 * mid i j + (i + j) mod 2   with   (i + j) mod 2 < 2

    Once this is available, lia can finish every inequality below. *)

Lemma mid_div_mod : forall (i j : nat),
  i + j = 2 * mid i j + (i + j) mod 2 /\ (i + j) mod 2 < 2.
Proof.
  intros i j. unfold mid. split.
  - apply Nat.div_mod_eq.
  - apply Nat.mod_upper_bound. lia.
Qed.

(*  if j < i then mid i j < i *)

Lemma mid_gt : forall (i j : nat), j < i -> mid i j < i.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

(** The split point is inside a real interval. *)

Lemma mid_lower : forall (i j : nat), i <= j -> i <= mid i j.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

Lemma mid_upper : forall (i j : nat), i <= j -> mid i j <= j.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

(** When the interval has more than one key the split point is strictly
    below the top. *)

Lemma mid_lt : forall (i j : nat), i < j -> mid i j < j.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

(* ================================================================= *)
(** ** Reading an operation *)

(** is_update o says whether o writes.

    Argument: o the operation. Returns true for insert and delete, false for
    the five queries *)

Definition is_update (o : op) : bool :=
  match o with
  | op_insert _ | op_delete _ => true
  | _                         => false
  end.

(** op_key o is the key an operation is about.

    Argument: o the operation. Returns the key for the four operations that
    carry one, and 0 for the three that do not. Those three never descend, so
    the 0 is a default rather than a case *)

Definition op_key (o : op) : key :=
  match o with
  | op_insert k | op_delete k | op_find k | op_rank k => k
  | _                                                 => 0
  end.

(** target_bit o is the value an update (insert/delete) wants a leaf's bit
    to end up holding.

    Argument: o the operation. Returns 1 for insert and 0 for delete. *)

Definition target_bit (o : op) : nat :=
  match o with
  | op_insert _ => 1
  | _           => 0
  end.

(* ================================================================= *)
(** ** Version object *)

(** vleaf id i s covers the single key i, with s equal to 1 when that key is
    present and 0 when it is not. vnode id i j s l r covers i..j, with s the
    number of keys under it and l and r the snapshots of its two halves.

    The id field is a tag handed out once and never again, so that CAS
    can compare versions. *)

Inductive versiontree : Type :=
  | vleaf (id : nat)                (* tag *)
          (i : nat)                 (* key *)
          (s : nat)                 (* sum *)
  | vnode (id : nat)
          (i j : nat)               (* the interval it covers *)
          (s : nat)                 (* sum *)
          (l r : versiontree).

(** Functions to easily read fields of versions *)

(** id *)

Definition v_id (v : versiontree) : nat :=
  match v with
  | vleaf tag _ _       => tag
  | vnode tag _ _ _ _ _ => tag
  end.

(** sum *)

Definition v_sum (v : versiontree) : nat :=
  match v with
  | vleaf _ _ s       => s
  | vnode _ _ _ s _ _ => s
  end.

(* i and j, the low and high ends of the interval *)

Definition v_lo (v : versiontree) : nat :=
  match v with
  | vleaf _ i _       => i
  | vnode _ i _ _ _ _ => i
  end.

Definition v_hi (v : versiontree) : nat :=
  match v with
  | vleaf _ i _       => i
  | vnode _ _ j _ _ _ => j
  end.

(** v_covers v i j is the proposition that v covers exactly i..j.

    Arguments: v the version tree, i and j the bounds. Returns a Prop, the
    conjunction of v_lo v = i and v_hi v = j *)

Definition v_covers (v : versiontree) (i j : nat) : Prop :=
  v_lo v = i /\ v_hi v = j.

(** Well formedness of a version tree.

    Argument: v the tree. Returns a Prop.

    A leaf is well formed when its sum is 0 or 1. A node is well formed
    when its two children cover the two halves the algorithm splits
    into, its sum really is the sum of theirs, and both children are
    themselves well formed. *)

Fixpoint wf (v : versiontree) : Prop :=
  match v with
  | vleaf _ _ s       => s = 0 \/ s = 1
  | vnode _ i j s l r =>
      v_covers l i (mid i j) /\
      v_covers r (mid i j + 1) j /\
      s = v_sum l + v_sum r /\ wf l /\ wf r
  end.

(* ================================================================= *)
(** ** Operating on a version tree *)

(** The keys a version tree holds as a list in increasing order.

    Argument: v the tree. Returns the list. *)

Fixpoint v_elements (v : versiontree) : list key :=
  match v with
  | vleaf _ k s       => if s =? 1 then [k] else []
  | vnode _ _ _ _ l r => v_elements l ++ v_elements r
  end.

(** The r-th smallest key, counting from one.

    Arguments: r is the rank, v the tree. Returns Some of that key, or
    None when r is out of range. *)

Fixpoint v_select (r : nat) (v : versiontree) : option key :=
  match v with
  | vleaf _ k s        => if s =? 1
                          then (if r =? 1 then Some k else None)
                          else None
  | vnode _ _ _ _ ltree rtree => if r <=? v_sum ltree
                          then v_select r ltree
                          else v_select (r - v_sum ltree) rtree
  end.

(** Whether a key is present.

    Arguments: k the key, v the tree. Returns a bool. *)

Fixpoint v_find (k : key) (v : versiontree) : bool :=
  match v with
  | vleaf _ _ s       => s =? 1
  | vnode _ i j _ l r => if k <=? mid i j then v_find k l else v_find k r
  end.

(** How many of the tree's keys are at most k.

    Arguments: k the key, v the tree. Returns the count. When the walk goes
    right the whole left half is already counted by its sum, so only the
    right half has to be descended *)

Fixpoint v_rank (k : key) (v : versiontree) : nat :=
  match v with
  | vleaf _ p s       => if andb (p <=? k) (s =? 1) then 1 else 0
  | vnode _ i j _ l r => if k <=? mid i j
                         then v_rank k l
                         else v_sum l + v_rank k r
  end.

(** What a query answers once it is holding a snapshot.

    Arguments: o the operation, v the snapshot. Returns the result. This is
    the concrete counterpart of the result half of abs_apply_op. The two
    updates never take this route, so the last line is unreachable junk kept
    to make the function total *)

Definition v_op_result (o : op) (v : versiontree) : res :=
  match o with
  | op_find k   => res_bool (v_find k v)
  | op_size     => res_nat (v_sum v)
  | op_select r => res_opt (v_select r v)
  | op_rank k   => res_nat (v_rank k v)
  | op_snapshot => res_set (v_elements v)
  | _           => res_bool false
  end.

(** Rebuilding a version tree with one key's bit changed.

    Arguments: k the key, b the value to give its bit, tag the next free tag,
    v the tree. Returns the new tree paired with the next free tag after it. *)

Fixpoint v_set_key (k : key) (b : bool) (tag : nat) (v : versiontree)
                   : versiontree * nat :=
  match v with
  | vleaf _ p _       => (vleaf tag p (if b then 1 else 0), S tag)
  | vnode _ i j _ l r =>
      if k <=? mid i j
      then let (l', tag') := v_set_key k b tag l in
           (vnode tag' i j (v_sum l' + v_sum r) l' r, S tag')
      else let (r', tag') := v_set_key k b tag r in
           (vnode tag' i j (v_sum l + v_sum r') l r', S tag')
  end.

(* ================================================================= *)
(** ** Inverted intervals are uninhabited *)

(** No well formed tree has an inverted interval. If wf v holds then
    v_hi v < v_lo v is impossible. *)

Lemma versiontree_empty : forall (v : versiontree),
  wf v -> v_hi v < v_lo v -> False.
Proof.
  intros v.
  induction v as [ tag i s | tag i j s l IHl r IHr ]; intros Hwf Hlt.
  - simpl in *. lia.
  - simpl in *. destruct Hwf as [[Hll Hlh] [_ [_ [Hl _]]]].
    apply (IHl Hl). rewrite Hll, Hlh. apply mid_gt. exact Hlt.
Qed.

(** The same fact in the form it actually gets used. A well formed tree
    always covers a non empty interval, v_lo v <= v_hi v *)

Lemma versiontree_le : forall (v : versiontree), wf v -> v_lo v <= v_hi v.
Proof.
  intros v Hwf.
  destruct (Nat.le_gt_cases (v_lo v) (v_hi v)) as [H | H].
  - exact H.
  - exfalso. apply (versiontree_empty v Hwf). exact H.
Qed.

(* ================================================================= *)
(** ** The elements lie inside the interval *)

(** A well formed tree never lists a key it does not own: if x appears in
    v_elements v then v_lo v <= x <= v_hi v *)

Lemma versiontree_elements_bounded : forall (v : versiontree) (x : key),
  wf v -> In x (v_elements v) -> v_lo v <= x /\ x <= v_hi v.
Proof.
  intros v.
  induction v as [ tag i s | tag i j s l IHl r IHr ]; intros x Hwf Hin; simpl in *.
  - destruct (s =? 1); simpl in Hin.
    + destruct Hin as [Heq | []]. lia.
    + destruct Hin.
  - destruct Hwf as [[Hll Hlh] [[Hrl Hrh] [_ [Hl Hr]]]].
    assert (Hle : i <= j).
    { pose proof (versiontree_le l Hl) as Hl'.
      pose proof (versiontree_le r Hr) as Hr'.
      rewrite Hll, Hlh in Hl'. rewrite Hrl, Hrh in Hr'. lia. }
    rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + destruct (IHl x Hl Hin) as [Hlo Hhi].
      rewrite Hll in Hlo. rewrite Hlh in Hhi.
      pose proof (mid_upper i j Hle). lia.
    + destruct (IHr x Hr Hin) as [Hlo Hhi].
      rewrite Hrl in Hlo. rewrite Hrh in Hhi.
      pose proof (mid_lower i j Hle). lia.
Qed.

(* ================================================================= *)
(** ** The sum field counts the elements *)

(** For a well formed tree,

      v_sum v = length (v_elements v) *)

Theorem versiontree_sum_correct : forall (v : versiontree),
  wf v -> v_sum v = length (v_elements v).
Proof.
  intros v.
  induction v as [ tag i s | tag i j s l IHl r IHr ]; intros Hwf; simpl in *.
  - destruct Hwf as [H | H]; subst; reflexivity.
  - destruct Hwf as [_ [_ [Hs [Hl Hr]]]].
    rewrite length_app.
    rewrite <- IHl by exact Hl.
    rewrite <- IHr by exact Hr.
    exact Hs.
Qed.

(* ================================================================= *)
(** ** Select returns the r-th smallest element *)

(** For a well formed tree and a rank r of at least 1,

      v_select r v = nth_error (v_elements v) (r - 1)

    r - 1 is needed since ranks start at one while list positions start
    at zero. The hypothesis 1 <= r is needed because with r = 0, the subtraction
    would underflow to 0 and the statement would be false *)

Theorem versiontree_select_correct : forall (v : versiontree) (r : nat),
  wf v ->
  1 <= r ->
  v_select r v = nth_error (v_elements v) (r - 1).
Proof.
  intros v.
  induction v as [ tag i s | tag i j s l IHl r IHr ]; intros q Hwf Hq; simpl in *.
  - destruct Hwf as [H | H]; subst; simpl.
    + rewrite nth_error_nil. reflexivity.
    + destruct q as [| q']. lia. simpl.
      rewrite Nat.sub_0_r.
      destruct q' as [| q'']; simpl.
      * reflexivity.
      * rewrite nth_error_nil. reflexivity.
  - destruct Hwf as [_ [_ [Hs [Hl Hr]]]].
    rewrite (versiontree_sum_correct l Hl).
    destruct (Nat.leb_spec q (length (v_elements l))) as [Hcmp | Hcmp].
    + rewrite IHl by assumption.
      rewrite nth_error_app1 by lia.
      reflexivity.
    + rewrite IHr by (solve [ assumption | lia ]).
      rewrite nth_error_app2 by lia.
      f_equal. lia.
Qed.

(* ################################################################# *)
(** * The node tree and its components *)

(** The two types are mutually recursive, because a component's children are
    slots and a slot may hold a component.

    nleaf i version covers the single key i. nnode i j l r version covers
    i..j and has the two child slots l and r. In both, version is the only
    mutable field, the one a CAS writes; everything else is fixed when the
    tree is built.

    A slot is either node_conc n, a real subcomponent, or node_abs i j set v,
    an abstract one covering i..j that holds the set and stores the corresponding
    version v.

    Being able to put either kind into a slot will be needed to make the
    connection of a node with abstract children to a pure abstract set by
    using another connection where a node with concrete children implements
    the node with concrete children. *)

Inductive nodetree : Type :=
  | nleaf (i : nat)                     (* covers the single key i *)
          (version : versiontree)       (* the mutable field *)
  | nnode (i j : nat)                   (* the interval it covers *)
          (l r: node)                   (* the two child slots *)
          (version : versiontree)       (* the mutable field *)

with node : Type :=
  | node_conc (n : nodetree)
  | node_abs  (i j : nat) (set : abs_set) (v : versiontree).

(** The version a component stores.

    Argument: n the component. Returns whatever is in its mutable field, for
    either shape *)

Definition n_version (n : nodetree) : versiontree :=
  match n with
  | nleaf _ v       => v
  | nnode _ _ _ _ v => v
  end.

(** The ends of the interval a component covers.

    Argument: n the component. Returns the low, respectively the high, end.
    For a leaf both are the single key it covers *)

Definition n_lo (n : nodetree) : nat :=
  match n with
  | nleaf i _       => i
  | nnode i _ _ _ _ => i
  end.

Definition n_hi (n : nodetree) : nat :=
  match n with
  | nleaf i _       => i
  | nnode _ j _ _ _ => j
  end.

(** Whether a component is a leaf.

    Argument: n the component. Returns a bool. *)

Definition n_is_leaf (n : nodetree) : bool :=
  match n with
  | nleaf _ _       => true
  | nnode _ _ _ _ _ => false
  end.

(** Writing the mutable field.

    Arguments: n the component, v the new version. Returns n with its version
    replaced and everything else kept. *)

Definition n_put_version (n : nodetree) (v : versiontree) : nodetree :=
  match n with
  | nleaf a _        => nleaf a v
  | nnode a b l r _  => nnode a b l r v
  end.

(** Replacing a child slot.

    Arguments: n the component, x the new slot. Returns n with its left,
    respectively right, slot replaced. A leaf has no children, so on a leaf
    both do nothing *)

Definition n_put_left (n : nodetree) (x : node) : nodetree :=
  match n with
  | nleaf a v        => nleaf a v
  | nnode a b _ r v  => nnode a b x r v
  end.

Definition n_put_right (n : nodetree) (x : node) : nodetree :=
  match n with
  | nleaf a v        => nleaf a v
  | nnode a b l _ v  => nnode a b l x v
  end.

(** Reading a child slot.

    Argument: n the component. Returns its left, respectively right, slot.
    A leaf has no children, so it answers with itself. That is junk, but no
    reachable configuration ever asks for it, by conc_threads_ok_run below. *)

Definition n_left (n : nodetree) : node :=
  match n with
  | nleaf a v       => node_conc (nleaf a v)
  | nnode _ _ l _ _ => l
  end.

Definition n_right (n : nodetree) : node :=
  match n with
  | nleaf a v       => node_conc (nleaf a v)
  | nnode _ _ _ r _ => r
  end.

(* ================================================================= *)
(** ** The interface a child offers its parent *)

(** These are the only things a component ever asks of a child, and each one
    is defined for both kinds of child with the same signature. Swapping an
    abstract child for a concrete one therefore changes nothing in the step
    function below, which is what makes the monotonicity argument possible.

    An abstract child answers with abs_apply_op, the sequential specification
    from the abstract machine *)

(** The ends of the interval a slot covers.

    Argument: x the slot. Returns the low, respectively the high, end, read
    from the component for a concrete slot and from the constructor for an
    abstract one *)

Definition slot_lo (x : node) : nat :=
  match x with
  | node_conc n      => n_lo n
  | node_abs i _ _ _ => i
  end.

Definition slot_hi (x : node) : nat :=
  match x with
  | node_conc n      => n_hi n
  | node_abs _ j _ _ => j
  end.

(** The version a slot stores, which is what a snapshot of it returns.

    Argument: x the slot. Returns corresponding version. The component's
    mutable version field for a concrete slot, and the version carried for
    an abstract one *)

Definition slot_snapshot (x : node) : versiontree :=
  match x with
  | node_conc n      => n_version n
  | node_abs _ _ _ v => v
  end.

(** The set a slot currently holds, as a characteristic function.

    Argument: x the slot. Returns that set. A concrete slot answers by
    looking the key up in its version; an abstract one hands back
    the set it is carrying. *)

Definition slot_set (x : node) : abs_set :=
  match x with
  | node_conc n       => fun k => v_find k (n_version n)
  | node_abs _ _ set _ => set
  end.

(** Building an internal component out of two finished slots.

    Arguments: i and j the interval it covers, l and r the two slots, tag the
    tag for the version it will store. Returns the component, whose version
    is a vnode over the two slots' snapshots with their sums added. *)

Definition n_build (i j : nat) (l r : node) (tag : nat) : nodetree :=
  nnode i j l r
    (vnode tag i j
       (v_sum (slot_snapshot l) + v_sum (slot_snapshot r))
       (slot_snapshot l) (slot_snapshot r)).

(* ================================================================= *)
(** ** Well formedness*)

(** Well formedness of a component.

    Argument: n the component. Returns a Prop.

    A leaf is well formed when its version covers exactly its own key and is
    itself a well formed version tree. A node is well formed when its version
    covers its interval, its two slots cover the right interval and both slots
    are well formed. *)

Fixpoint wf_nodetree (n : nodetree) : Prop :=
  match n with
  | nleaf i v => v_covers v i i /\ wf v
  | nnode a b l r v =>
      v_covers v a b /\ wf v /\
      slot_lo l = a /\ slot_hi l = mid a b /\
      slot_lo r = mid a b + 1 /\ slot_hi r = b /\
      wf_slot l /\ wf_slot r
  end

(** Well formedness of a slot.

    Argument: x the slot. Returns a Prop. A concrete slot is well formed when
    its component is. An abstract slot is well formed when the version it stores
    holds is well-formed, holds the set of keys the abs_set holds, and covers
    the right interval *)

with wf_slot (x : node) : Prop :=
  match x with
  | node_conc n       => wf_nodetree n
  | node_abs a b set v => v_covers v a b /\ wf v /\ v_elements v = abs_elems a b set
  end.

(** A well formed component and its version agree about which
    interval they are talking about.

      n.version.i = n.i    and    n.version.j = n.j *)

Lemma nodetree_version_interval : forall (n : nodetree),
  wf_nodetree n -> v_lo (n_version n) = n_lo n /\ v_hi (n_version n) = n_hi n.
Proof.
  intros n Hwf. destruct n; simpl in *;
    destruct Hwf as [[Hlo Hhi] _]; split; assumption.
Qed.

(* ================================================================= *)
(** ** One whole update on a node component, done in a single step *)

(** Running a real component to completion instantly, as one atomic step.

    Arguments: o the operation, tag the next free tag, x the component.
    Returns a triple of the potentially updated component, the next free
    tag after it, and the answer.

    Every version on the path is rebuilt with a tag of its own, as the
    algorithm would have done. Only the two updates are recursively routed
    to the leaves. Queries just reuse the version functions defined above *)

Fixpoint n_apply (o : op) (tag : nat) (x : nodetree) : nodetree * nat * res :=
  match x with
  | nleaf a v =>
      match o with
      | op_insert _ => if v_sum v =? 1
                       then (nleaf a v, tag, res_bool false)
                       else (nleaf a (vleaf tag a 1), S tag, res_bool true)
      | op_delete _ => if v_sum v =? 0
                       then (nleaf a v, tag, res_bool false)
                       else (nleaf a (vleaf tag a 0), S tag, res_bool true)
      | _           => (nleaf a v, tag, v_op_result o v)
      end
  | nnode a b l r _ =>
      if op_key o <=? mid a b
      then let '(l', tag', ans) := slot_apply o tag l in
           (nnode a b l' r
              (vnode tag' a b
                 (v_sum (slot_snapshot l') + v_sum (slot_snapshot r))
                 (slot_snapshot l') (slot_snapshot r)),
            S tag', ans)
      else let '(r', tag', ans) := slot_apply o tag r in
           (nnode a b l r'
              (vnode tag' a b
                 (v_sum (slot_snapshot l) + v_sum (slot_snapshot r'))
                 (slot_snapshot l) (slot_snapshot r')),
            S tag', ans)
  end

(** The same for a slot, whichever kind it is.

    Arguments: o the operation, tag the next free tag, x the slot. Returns
    the slot afterwards, the next free tag, and the answer.

    A concrete slot just passes the work down. An abstract one answers by
    abs_apply_op and then stores an updated version, so that slot_snapshot still
    agrees with the set it claims to hold, ensuring well-formedness. *)

with slot_apply (o : op) (tag : nat) (x : node) : node * nat * res :=
  match x with
  | node_conc c =>
      let '(c', tag', ans) := n_apply o tag c in
      (node_conc c', tag', ans)
  | node_abs a b set v =>
      let (set', ans) := abs_apply_op a b o set in
      match o with
      | op_insert k => if set k
                       then (node_abs a b set' v, tag, ans)
                       else let (v', tag') := v_set_key k true tag v in
                            (node_abs a b set' v', tag', ans)
      | op_delete k => if set k
                       then let (v', tag') := v_set_key k false tag v in
                            (node_abs a b set' v', tag', ans)
                       else (node_abs a b set' v, tag, ans)
      | _           => (node_abs a b set' v, tag, ans)
      end
  end.

(* ################################################################# *)
(** * The concrete automaton *)

(** Like the abstract machine, everything below takes the interval i..j that
    this component covers as an ordinary argument *)

(** A thread's state is its program counter and local variables alive at
    that moment. Program counters here are for only shared-memory access
    steps. All others (local computations with only local variables,
    mathematical expressions's computations, conditionals, reads of immutable
    memory...) are considered ATOMIC.

    c_idle: nothing running

    c_read o: about to read a leaf's version, for the update o

    c_flip o old: has read old, and is about to CAS a new leaf version

    c_child o: about to hand o down to the correct subcomponent/child

    c_own o ans att: the child is finished and answered ans; about to begin
    refresh attempt att by reading this node's own version

    c_left o ans att old: has read old, and is about to snapshot the left slot

    c_right o ans att old vl: took vl from the left, and is about to snapshot
    the right slot

    c_cas o ans att old vl vr: holds all three, and is about to CAS a new
    version built from vl and vr over old.

    c_query o: about to read this component's own version to answer o (done
    fully atomic after the snapshot)

    c_returning ans: waiting to return ans

    The answer a thread carries is a res, the same type the abstract machine
    carries in a_returning. The attempt count att is 1 or 2, since two
    refresh attempts always suffice *)

Inductive conc_progstate : Type :=
  | c_idle
  | c_read      (o : op)
  | c_flip      (o : op) (old : versiontree)
  | c_child     (o : op)
  | c_own       (o : op) (ans : res) (att : nat)
  | c_left      (o : op) (ans : res) (att : nat) (old : versiontree)
  | c_right     (o : op) (ans : res) (att : nat) (old vl : versiontree)
  | c_cas       (o : op) (ans : res) (att : nat) (old vl vr : versiontree)
  | c_query     (o : op)
  | c_returning (ans : res).

(** A configuration of the concrete machine, the whole state at one moment.

    Fields: root is the shared node-component we are interested in. fresh is
    the next unused tag. cstate says where every thread is with its local
    variables. *)

Record conc_config : Type := ConcConfig {
  root       : nodetree;
  fresh      : nat;
  cstate : tid -> conc_progstate
}.

(** The starting configuration.

    Arguments: tree, the node tree to run on, tag the first unused tag, which
    has to be larger than every tag already inside tree. Returns the
    configuration with no thread started *)

Definition conc_init (tree : nodetree) (tag : nat) : conc_config :=
  ConcConfig tree tag (fun _ => c_idle).

(** Moving one thread and touching nothing else.

    Arguments: c the configuration, t the thread, p its new state. Returns c
    with thread t at p, the component and the tag supply unchanged. Every use
    of it is a step that reads memory or computes, but does not write
    (For readability in conc_next) *)

Definition put_state (c : conc_config) (t : tid) (p : conc_progstate) : conc_config :=
  ConcConfig c.(root) c.(fresh) (upd c.(cstate) t p).

(** Moving one thread and writing shared memory at the same time.

    Arguments: tree the new component, tag the new tag supply, c the
    configuration, t the thread, p its new state. Returns a configuration
    with all three replaced. Every use of it is a real write. *)

Definition put_all (tree : nodetree) (tag : nat) (c : conc_config)
                   (t : tid) (p : conc_progstate) : conc_config :=
  ConcConfig tree tag (upd c.(cstate) t p).

(** Whether thread t is allowed to take action a from configuration c.

    Arguments: i and j the interval, c the configuration, t the thread, a the
    action. Returns a bool.

    The only guard that can really fail is op_ok, which asks whether the node
    we are about to operate on covers the key. A thread in the middle of an
    operation can always take its next step, and which shape of component it
    is running on was settled at the invoke and never changes, so we do not
    need to retest. *)

Definition conc_enabled (i j : nat) (c : conc_config) (t : tid) (a : action) : bool :=
  match a, c.(cstate) t with
  | act_invoke o, c_idle      => op_ok i j o
  | act_return, c_returning _ => true
  | act_step, c_idle          => false
  | act_step, c_returning _   => false
  | act_step, _               => true
  | _, _                      => false
  end.

(** One step of the concrete machine, covering both shapes of component and
    all seven operations.

    Arguments: i and j the interval, c the configuration, t the thread, a the
    action. Returns the configuration afterwards paired with the events
    emitted (for invokes and returns only). A step that is not allowed is
    a stutter, similar to the abstract machine.

    Again, each arm is one atomic memory access. The local tests between accesses
    cost nothing and are folded into the step that reaches them, which is why
    there are fewer program counters than lines of pseudocode *)

Definition conc_next (i j : nat) (c : conc_config) (t : tid) (a : action)
                     : conc_config * list event :=
  match a, c.(cstate) t with

  (* ---- announcing an operation ------------------------------------- *)
  | act_invoke o, c_idle =>
      if op_ok i j o
      then let p := if negb (is_update o) then c_query o
                    else if n_is_leaf c.(root) then c_read o
                    else c_child o in
           (put_state c t p, [ev_invoke t o])
      else (c, [])

  (* ---- a leaf reads its version, then flips the bit if it must ------ *)
  | act_step, c_read o =>
      let old := n_version c.(root) in
      let p := if v_sum old =? target_bit o
               then c_returning (res_bool false)
               else c_flip o old in
      (put_state c t p, [])

  | act_step, c_flip o old =>
      if v_id (n_version c.(root)) =? v_id old
      then (* only an update reaches here, so an insert sets the bit
              and a delete clears it *)
           (put_all (n_put_version c.(root) (vleaf c.(fresh) i (target_bit o)))
                    (S c.(fresh)) c t (c_returning (res_bool true)), [])
      else (put_state c t (c_returning (res_bool false)), [])

  (* ---- an internal node hands the key to a subcomponent ------------- *)
  | act_step, c_child o =>
      (* the whole subcomponent operation is one step, which is what
         makes the subcomponent atomic *)
      if op_key o <=? mid i j
      then let '(l', tag', ans) := slot_apply o c.(fresh) (n_left c.(root)) in
           (put_all (n_put_left c.(root) l') tag' c t
                    (c_own o ans 1), [])
      else let '(r', tag', ans) := slot_apply o c.(fresh) (n_right c.(root)) in
           (put_all (n_put_right c.(root) r') tag' c t
                    (c_own o ans 1), [])

  (* ---- the four steps of a refresh ---------------------------------- *)
  | act_step, c_own o ans att =>
      (put_state c t (c_left o ans att (n_version c.(root))), [])

  | act_step, c_left o ans att old =>
      (put_state c t (c_right o ans att old
                        (slot_snapshot (n_left c.(root)))), [])

  | act_step, c_right o ans att old vl =>
      (put_state c t (c_cas o ans att old vl
                        (slot_snapshot (n_right c.(root)))), [])

  | act_step, c_cas o ans att old vl vr =>
      if v_id (n_version c.(root)) =? v_id old
      then (put_all (n_put_version c.(root)
                       (vnode c.(fresh) i j (v_sum vl + v_sum vr) vl vr))
                    (S c.(fresh)) c t (c_returning ans), [])
      else if att =? 1
      then (* the first attempt lost the race, so refresh once more *)
           (put_state c t (c_own o ans 2), [])
      else (* two attempts are enough, someone else did the work *)
           (put_state c t (c_returning ans), [])

  (* ---- a query is one read of this component's own version ---------- *)
  | act_step, c_query o =>
      (put_state c t (c_returning (v_op_result o (n_version c.(root)))), [])

  (* ---- handing the answer back -------------------------------------- *)
  | act_return, c_returning ans =>
      (put_state c t c_idle, [ev_return t ans])

  | _, _ => (c, [])
  end.

(** The machine run over a whole schedule.

    Arguments: i and j the interval, c the starting configuration, sched a
    list of thread and action pairs in the order they happen. Returns the
    final configuration paired with the trace *)

Fixpoint conc_run (i j : nat) (c : conc_config) (sched : list (tid*action))
                  : conc_config * list event :=
  match sched with
  | [] => (c, [])
  | (t, a) :: rest =>
      let (c',  evs)  := conc_next i j c t a in
      let (c'', evs') := conc_run i j c' rest in
      (c'', evs ++ evs')
  end.

(** The trace of a run, throwing the final configuration away. *)

Definition conc_trace (i j : nat) (c : conc_config) (sched : list (tid*action))
                      : list event :=
  snd (conc_run i j c sched).

(** Whether a schedule is a legal execution.

    Arguments: i and j the interval, c the starting configuration, sched the
    schedule. Returns true when every step is enabled at the moment it is
    reached *)

Fixpoint conc_legal (i j : nat) (c : conc_config) (sched : list (tid*action)) : bool :=
  match sched with
  | [] => true
  | (t, a) :: rest =>
      conc_enabled i j c t a && conc_legal i j (fst (conc_next i j c t a)) rest
  end.

(* ================================================================= *)
(** ** Reasoning about a step *)

(** Tactic for splitting a step into its branches. conc_next is one big match
    with a test or two inside most arms, so every proof about it begins by taking
    those apart. This does that and keeps the equation for each test, so the
    branch a goal came from is still readable afterwards
    
    "Keep splitting the goal on whatever test is blocking it, remembering which
     way each test went, and simplify after each split, until nothing is blocking." *)

Ltac conc_next_cases :=
  repeat (match goal with
          | |- context [ if ?b then _ else _ ] => destruct b eqn:?
          | |- context [ match root ?c with _ => _ end ] =>
              destruct (root c) eqn:?
          | |- context [ match slot_apply ?o ?tag ?x with _ => _ end ] =>
              destruct (slot_apply o tag x) as [[? ?] ?]
          end; simpl).

(** A step that is not enabled does nothing: it leaves the configuration
    untouched and emits no events. *)

Lemma conc_next_disabled : forall (i j : nat) (c : conc_config) (t : tid) (a : action),
  conc_enabled i j c t a = false -> conc_next i j c t a = (c, []).
Proof.
  intros i j c t a H.
  destruct a as [o | |]; destruct (c.(cstate) t) eqn:E;
    simpl in *; rewrite ?E in *;
    simpl in *; try reflexivity; try discriminate;
    repeat (match goal with
            | H : context [ if ?b then _ else _ ] |- _ => destruct b eqn:?
            | |- context [ if ?b then _ else _ ] => destruct b eqn:?
            end; simpl in *);
    try reflexivity; try discriminate; try congruence.
Qed.

(* ================================================================= *)
(** ** Thread states always agree with the shape of the component *)

(** The three writers keep the constructor they were given, so none of them
    turn a leaf into a node or a node into a leaf *)

Lemma leaf_put_version : forall (n : nodetree) (v : versiontree),
  n_is_leaf (n_put_version n v) = n_is_leaf n.
Proof. intros [|] v; reflexivity. Qed.

Lemma leaf_put_left : forall (n : nodetree) (x : node),
  n_is_leaf (n_put_left n x) = n_is_leaf n.
Proof. intros [|] x; reflexivity. Qed.

Lemma leaf_put_right : forall (n : nodetree) (x : node),
  n_is_leaf (n_put_right n x) = n_is_leaf n.
Proof. intros [|] x; reflexivity. Qed.

(** and therefore no step ever changes the shape of the component. Whether
    c.(root) is a leaf is the same before and after any step, so it is
    decided once at conc_init and never changes again *)

Lemma conc_shape_fixed : forall (i j : nat) (c : conc_config) (t : tid) (a : action),
  n_is_leaf (fst (conc_next i j c t a)).(root) = n_is_leaf c.(root).
Proof.
  intros i j c t a.
  destruct a as [o | |]; destruct (c.(cstate) t) eqn:E; simpl; rewrite ?E; simpl;
    conc_next_cases;
    rewrite ?leaf_put_version, ?leaf_put_left, ?leaf_put_right;
    repeat match goal with H : root c = _ |- _ => rewrite H end;
    simpl; congruence.
Qed.

(** A step only moves the thread that takes it and any other thread t' is in the
    same state afterwards as before *)

Lemma conc_state_other : forall (i j : nat) (c : conc_config) (t : tid)
                                (a : action) (t' : tid),
  t' <> t -> (fst (conc_next i j c t a)).(cstate) t' = c.(cstate) t'.
Proof.
  intros i j c t a t' Hne.
  assert (Hb : (t' =? t) = false) by (apply Nat.eqb_neq; exact Hne).
  destruct a as [o | |]; destruct (c.(cstate) t) eqn:E; simpl; rewrite ?E; simpl;
    conc_next_cases; unfold put_state, put_all, upd; simpl;
    rewrite ?Hb; reflexivity.
Qed.

(** What a thread state may hold, given the shape of the component it is
    running on.

    Arguments: leaf, which says whether the component is a leaf, and p the
    thread state. Returns a Prop.

    leaf = false, and both demand that the operation is an update. c_query
    demands a query. c_idle and c_returning demand nothing, since a thread
    that owes an answer no longer cares how it got it *)

Definition conc_progstate_ok (leaf : bool) (p : conc_progstate) : Prop :=
  match p with
  | c_idle            => True
  | c_read o          => leaf = true  /\ is_update o = true
  | c_flip o _        => leaf = true  /\ is_update o = true
  | c_child o         => leaf = false /\ is_update o = true
  | c_own o _ _       => leaf = false /\ is_update o = true
  | c_left o _ _ _    => leaf = false /\ is_update o = true
  | c_right o _ _ _ _ => leaf = false /\ is_update o = true
  | c_cas o _ _ _ _ _ => leaf = false /\ is_update o = true
  | c_query o         => is_update o = false
  | c_returning _     => True
  end.

(** The same condition asked of every thread of a configuration at once.

    Argument: c the configuration. Returns a Prop *)

Definition conc_threads_ok (c : conc_config) : Prop :=
  forall t, conc_progstate_ok (n_is_leaf c.(root)) (c.(cstate) t).

(** It holds when nothing has started, since every thread is idle and c_idle
    demands nothing *)

Lemma conc_threads_ok_init : forall (tree : nodetree) (tag : nat),
  conc_threads_ok (conc_init tree tag).
Proof. intros tree tag t. exact I. Qed.

(** and it survives one step, whichever thread takes it *)

Lemma conc_threads_ok_step : forall (i j : nat) (c : conc_config) (t : tid)
                                    (a : action),
  conc_threads_ok c -> conc_threads_ok (fst (conc_next i j c t a)).
Proof.
  intros i j c t a H t'.
  rewrite (conc_shape_fixed i j c t a).
  destruct (Nat.eq_dec t' t) as [Heq | Hne].
  - subst t'.
    assert (Ht := H t).
    assert (Hb : (t =? t) = true) by (apply Nat.eqb_eq; reflexivity).
    destruct a as [o | |]; destruct (c.(cstate) t) eqn:E;
      simpl; rewrite ?E; simpl;
      conc_next_cases;
      unfold put_state, put_all, upd; simpl; rewrite ?Hb; simpl;
      repeat match goal with Ho : root c = _ |- _ => rewrite Ho in * end;
      simpl in *;
      try apply H;
      try exact I;
      try (destruct o; simpl in *; intuition (try congruence));
      intuition (try congruence).
  - rewrite (conc_state_other i j c t a t' Hne). apply H.
Qed.

(** and therefore it holds everywhere any schedule can reach, starting from
    any configuration that satisfies it, in particular from conc_init.

    This lemma justifies conc_next having no leaf test past the invoke *)

Theorem conc_threads_ok_run : forall (i j : nat) (sched : list (tid*action))
                                     (c : conc_config),
  conc_threads_ok c -> conc_threads_ok (fst (conc_run i j c sched)).
Proof.
  intros i j sched.
  induction sched as [| [t a] rest IH]; intros c H.
  - exact H.
  - simpl. destruct (conc_next i j c t a) as [c' evs] eqn:E.
    destruct (conc_run i j c' rest) as [c'' evs'] eqn:E'. simpl.
    assert (Hc' : conc_threads_ok c').
    { replace c' with (fst (conc_next i j c t a)) by (rewrite E; reflexivity).
      apply conc_threads_ok_step. exact H. }
    specialize (IH c' Hc'). rewrite E' in IH. exact IH.
Qed.
