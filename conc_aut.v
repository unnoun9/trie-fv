From Trie Require Import abs_aut.

(*  ###############################################################  *)
(*  The concrete implementation  *)

(*  mid i j is where the interval i..j splits. The left child takes
    i..mid i j and the right child takes mid i j + 1..j.

    Arguments: i and j the bounds. Returns the floor of their average  *)

Definition mid (i j : nat) : nat := (i + j) / 2.

(*  ===============================================================  *)
(*  Arithmetic facts about mid  *)

(*  The division definition unfolded

      i + j = 2 * mid i j + (i + j) mod 2   with   (i + j) mod 2 < 2

    This is to help lia finish every inequality below.  *)

Lemma mid_div_mod : forall (i j : nat),
  i + j = 2 * mid i j + (i + j) mod 2 /\ (i + j) mod 2 < 2.
Proof.
  intros i j. unfold mid. split.
  - apply Nat.div_mod_eq.
  - apply Nat.mod_upper_bound. lia.
Qed.

(*  if j < i then mid i j < i  *)

Lemma mid_gt : forall (i j : nat), j < i -> mid i j < i.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

(*  The split point is inside a real interval.  *)

Lemma mid_lower : forall (i j : nat), i <= j -> i <= mid i j.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

Lemma mid_upper : forall (i j : nat), i <= j -> mid i j <= j.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

(*  When the interval has more than one key the split point is strictly
    below the top.  *)

Lemma mid_lt : forall (i j : nat), i < j -> mid i j < j.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

(*  ===============================================================  *)
(*  Reading an operation  *)

(*  is_update o says whether o writes.

    Argument: o the operation. Returns true for insert and delete, false for
    the five queries  *)

Definition is_update (o : op) : bool :=
  match o with
  | op_insert _ | op_delete _ => true
  | _                         => false
  end.

(*  op_key o is the key an operation is about.

    Argument: o the operation. Returns the key for the four operations that
    carry one, and 0 for the three that do not. Those three never descend, so
    the 0 is a default rather than a case  *)

Definition op_key (o : op) : key :=
  match o with
  | op_insert k | op_delete k | op_find k | op_rank k => k
  | _                                                 => 0
  end.

(*  target_bit o is the value an update (insert/delete) wants a leaf's bit
    to end up holding.

    Argument: o the operation. Returns 1 for insert and 0 for delete.  *)

Definition target_bit (o : op) : nat :=
  match o with
  | op_insert _ => 1
  | _           => 0
  end.

(*  ===============================================================  *)
(*  Version object  *)

(*  vleaf id i s covers the single key i, with s equal to 1 when that key is
    present and 0 when it is not. vnode id i j s l r covers i..j, with s the
    number of keys under it and l and r the snapshots of its two halves.

    The id field is a tag handed out once and never again, so that CAS
    can compare versions.  *)

Inductive versiontree : Type :=
  | vleaf (id : nat)                (*  tag  *)
          (i : nat)                 (*  key  *)
          (s : nat)                 (*  sum  *)
  | vnode (id : nat)
          (i j : nat)               (*  the interval it covers  *)
          (s : nat)                 (*  sum  *)
          (l r : versiontree).

(*  Functions to easily read fields of versions  *)

(*  id  *)

Definition v_id (v : versiontree) : nat :=
  match v with
  | vleaf tag _ _       => tag
  | vnode tag _ _ _ _ _ => tag
  end.

(*  sum  *)

Definition v_sum (v : versiontree) : nat :=
  match v with
  | vleaf _ _ s       => s
  | vnode _ _ _ s _ _ => s
  end.

(*  i and j, the low and high ends of the interval  *)

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

(*  v_covers v i j is the proposition that v covers exactly i..j.

    Arguments: v the version tree, i and j the bounds. Returns a Prop, the
    conjunction of v_lo v = i and v_hi v = j  *)

Definition v_covers (v : versiontree) (i j : nat) : Prop :=
  v_lo v = i /\ v_hi v = j.

(*  Well formedness of a version tree.

    Argument: v the tree. Returns a Prop.

    A leaf is well formed when its sum is 0 or 1. A node is well formed
    when its two children cover the two halves the algorithm splits
    into, its sum really is the sum of theirs, and both children are
    themselves well formed.  *)

Fixpoint wf (v : versiontree) : Prop :=
  match v with
  | vleaf _ _ s       => s = 0 \/ s = 1
  | vnode _ i j s l r =>
      v_covers l i (mid i j) /\
      v_covers r (mid i j + 1) j /\
      s = v_sum l + v_sum r /\ wf l /\ wf r
  end.

(*  ===============================================================  *)
(*  Operating on a version tree  *)

(*  The keys a version tree holds as a list in increasing order.

    Argument: v the tree. Returns the list.  *)

Fixpoint v_elements (v : versiontree) : list key :=
  match v with
  | vleaf _ k s       => if s =? 1 then [k] else []
  | vnode _ _ _ _ l r => v_elements l ++ v_elements r
  end.

(*  The r-th smallest key, counting from one.

    Arguments: r is the rank, v the tree. Returns Some of that key, or
    None when r is out of range.  *)

Fixpoint v_select (r : nat) (v : versiontree) : option key :=
  match v with
  | vleaf _ k s        => if s =? 1
                          then (if r =? 1 then Some k else None)
                          else None
  | vnode _ _ _ _ ltree rtree => if r <=? v_sum ltree
                          then v_select r ltree
                          else v_select (r - v_sum ltree) rtree
  end.

(*  Whether a key is present.

    Arguments: k the key, v the tree. Returns a bool.  *)

Fixpoint v_find (k : key) (v : versiontree) : bool :=
  match v with
  | vleaf _ _ s       => s =? 1
  | vnode _ i j _ l r => if k <=? mid i j then v_find k l else v_find k r
  end.

(*  How many of the tree's keys are at most k.

    Arguments: k the key, v the tree. Returns the count. When the walk goes
    right the whole left half is already counted by its sum, so only the
    right half has to be descended  *)

Fixpoint v_rank (k : key) (v : versiontree) : nat :=
  match v with
  | vleaf _ p s       => if andb (p <=? k) (s =? 1) then 1 else 0
  | vnode _ i j _ l r => if k <=? mid i j
                         then v_rank k l
                         else v_sum l + v_rank k r
  end.

(*  What a query answers once it is holding a snapshot.

    Arguments: o the operation, v the snapshot. Returns the result. This is
    the concrete counterpart of the result half of abs_apply_op. The two
    updates never take this route, so the last line is unreachable junk kept
    to make the function total  *)

Definition v_op_result (o : op) (v : versiontree) : res :=
  match o with
  | op_find k   => res_bool (v_find k v)
  | op_size     => res_nat (v_sum v)
  | op_select r => res_opt (v_select r v)
  | op_rank k   => res_nat (v_rank k v)
  | op_snapshot => res_set (v_elements v)
  | _           => res_bool false
  end.

(*  Rebuilding a version tree with one key's bit changed.

    Arguments: k the key, b the value to give its bit, tag the next free tag,
    v the tree. Returns the new tree paired with the next free tag after it.  *)

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

(*  ===============================================================  *)
(*  Inverted intervals are uninhabited  *)

(*  No well formed tree has an inverted interval. If wf v holds then
    v_hi v < v_lo v is impossible.  *)

Lemma versiontree_empty : forall (v : versiontree),
  wf v -> v_hi v < v_lo v -> False.
Proof.
  intros v.
  induction v as [ tag i s | tag i j s l IHl r IHr ]; intros Hwf Hlt.
  - simpl in *. lia.
  - simpl in *. destruct Hwf as [[Hll Hlh] [_ [_ [Hl _]]]].
    apply (IHl Hl). rewrite Hll, Hlh. apply mid_gt. exact Hlt.
Qed.

(*  The same fact in the form it actually gets used. A well formed tree
    always covers a non empty interval, v_lo v <= v_hi v  *)

Lemma versiontree_le : forall (v : versiontree), wf v -> v_lo v <= v_hi v.
Proof.
  intros v Hwf.
  destruct (Nat.le_gt_cases (v_lo v) (v_hi v)) as [H | H].
  - exact H.
  - exfalso. apply (versiontree_empty v Hwf). exact H.
Qed.

(*  ===============================================================  *)
(*  The elements lie inside the interval  *)

(*  A well formed tree never lists a key it does not own: if x appears in
    v_elements v then v_lo v <= x <= v_hi v  *)

Lemma versiontree_elements_bounded : forall (v : versiontree) (x : key),
  wf v -> In x (v_elements v) -> v_lo v <= x /\ x <= v_hi v.
Proof.
  intros v x.
  induction v as [ tag i s | tag i j s l IHl r IHr ]; intros Hwf Hin; simpl in *.
  - destruct (s =? 1); simpl in Hin.
    + destruct Hin as [Heq | []]. lia.
    + destruct Hin.
  - destruct Hwf as [[Hll Hlh] [[Hrl Hrh] [_ [Hl Hr]]]].
    assert (Hle : i <= j).
    { pose proof (versiontree_le l Hl) as Hl'.
      pose proof (versiontree_le r Hr) as Hr'.
      rewrite Hll, Hlh in Hl'. rewrite Hrl, Hrh in Hr'. lia. }
    rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + destruct (IHl Hl Hin) as [Hlo Hhi].
      rewrite Hll in Hlo. rewrite Hlh in Hhi.
      pose proof (mid_upper i j Hle). lia.
    + destruct (IHr Hr Hin) as [Hlo Hhi].
      rewrite Hrl in Hlo. rewrite Hrh in Hhi.
      pose proof (mid_lower i j Hle). lia.
Qed.

(*  ===============================================================  *)
(*  The sum field counts the elements  *)

(*  For a well formed tree,

      v_sum v = length (v_elements v)  *)

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

(*  ===============================================================  *)
(*  Select returns the r-th smallest element  *)

(*  For a well formed tree and a rank r of at least 1,

      v_select r v = nth_error (v_elements v) (r - 1)

    r - 1 is needed since ranks start at one while list positions start
    at zero. The hypothesis 1 <= r is needed because with r = 0, the subtraction
    would underflow to 0 and the statement would be false  *)

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

(*  A thread's state inside one node. It include its program counter and
    the local variables alive at that moment. Program counters here are for
    only shared-memory access steps. All others (local computations with only
    local variables, evaluating mathematical expressions, conditionals, reads
    of immutable memory...) are considered ATOMIC.

    c_idle: nothing running

    c_read o: about to read a leaf's version, for the update o

    c_flip o old: has read old, and is about to CAS a new leaf version

    c_call o: about to hand the update o down to the child that owns its
    key

    c_wait o: has handed o down. Every turn the thread gets now goes to the
    child, which works on o with steps of its own, interleaved with everyone
    else's. Once the child has an answer, the next turn collects it, which is
    the child's return

    c_own o ans att: the child answered ans; about to begin refresh attempt
    att by reading this node's own version

    c_left o ans att old: has read old, and is about to snapshot the left child

    c_right o ans att old vl: took vl from the left, and is about to snapshot
    the right child

    c_cas o ans att old vl vr: holds all three, and is about to CAS a new
    version built from vl and vr over old.

    c_query o: about to read this node's own version to answer o (done
    fully atomic after the snapshot)

    c_returning ans: waiting to return ans  *)

Inductive conc_progstate : Type :=

  (*  between operations, no line of code  *)
  | c_idle

  (*  insert or delete, leaf case:
        old <- read x.version
        if old.sum = 1  return false        (insert)
        if old.sum = 0  return false        (delete)  *)
  | c_read      (o : op)

  (*  insert or delete, leaf case:
        return CAS(x.version, old, vleaf(i, 1))   (insert)
        return CAS(x.version, old, vleaf(i, 0))   (delete)  *)
  | c_flip      (o : op) (old : versiontree)

  (*  insert or delete, internal case, the start of the call:
        if k <= (i+j)/2  result <- insert(x.left, i, (i+j)/2, k)
        else             result <- insert(x.right, (i+j)/2 + 1, j, k)
      (delete in place of insert for a delete)  *)
  | c_call      (o : op)

  (*  inside that same call, until it returns into result  *)
  | c_wait      (o : op)

  (*  the first line of refresh(x, i, j), reached from
        if not refresh(x, i, j)             (att = 1)
          refresh(x, i, j)                  (att = 2)
      which is
        old <- read x.version  *)
  | c_own       (o : op) (ans : res) (att : nat)

  (*  refresh:
        vl <- snapshot(x.left)  *)
  | c_left      (o : op) (ans : res) (att : nat) (old : versiontree)

  (*  refresh:
        vr <- snapshot(x.right)  *)
  | c_right     (o : op) (ans : res) (att : nat) (old vl : versiontree)

  (*  refresh, and the test on its answer:
        return CAS(x.version, old, vnode(i, j, vl.sum + vr.sum, vl, vr))
        if not refresh(x, i, j)  refresh(x, i, j)  *)
  | c_cas       (o : op) (ans : res) (att : nat) (old vl vr : versiontree)

  (*  any query, the read inside snapshot(root):
        return read x.version
      as used by
        find_at(snapshot(root), 1, N, k)
        snapshot(root).sum
        v <- snapshot(root)
        rank_at(snapshot(root), 1, N, k)
      the walk over the version read afterwards is plain sequential code  *)
  | c_query     (o : op)

  (*  the final return of any operation:
        return result                       (insert, delete)
        return find_at(...) and the like    (queries)  *)
  | c_returning (ans : res).

(*  ###############################################################  *)
(*  Nodes and their children  *)

(*  The two types are mutually recursive, because a node has two children
    and a child may itself be a node.

    leaf i version covers the single key i. internal i j l r version covers
    i..j and has the two children l and r. In both, version is the only
    mutable field.

    A child is either child_conc n st, a real node n together with where
    every thread is inside it, or child_abs i j set v st, an abstract set
    covering i..j that holds the set, stores the corresponding version v,
    and records where every thread is in its own abstract machine.

    The thread states are what make a child a machine and not just a value.
    A thread hands an update down, the child takes steps of its own on it,
    interleaved with every other thread's steps, and only later hands an
    answer back.

    Being able to make a child either kind will be needed to make the
    connection of a node with abstract children to a pure abstract set by
    using another connection where a node with concrete children implements
    the node with abstract children.  *)

Inductive node : Type :=
  | leaf     (i : nat)                  (*  covers the single key i  *)
             (version : versiontree)    (*  the mutable field  *)
  | internal (i j : nat)                (*  the interval it covers  *)
             (l r : child)              (*  the two children  *)
             (version : versiontree)    (*  the mutable field  *)

with child : Type :=
  | child_conc (n : node)
               (st : tid -> conc_progstate)
  | child_abs  (i j : nat) (set : abs_set) (v : versiontree)
               (st : tid -> abs_progstate).

(*  The version a node stores.

    Argument: n the node. Returns the versiontree in either shape.  *)

Definition n_version (n : node) : versiontree :=
  match n with
  | leaf _ v           => v
  | internal _ _ _ _ v => v
  end.

(*  The ends of the interval a node covers.

    Argument: n the node. Returns the low, respectively the high, end.
    For a leaf both are the single key it covers  *)

Definition n_lo (n : node) : nat :=
  match n with
  | leaf i _           => i
  | internal i _ _ _ _ => i
  end.

Definition n_hi (n : node) : nat :=
  match n with
  | leaf i _           => i
  | internal _ j _ _ _ => j
  end.

(*  Whether a node is a leaf.

    Argument: n the node. Returns a bool.  *)

Definition n_is_leaf (n : node) : bool :=
  match n with
  | leaf _ _           => true
  | internal _ _ _ _ _ => false
  end.

(*  Writing the mutable versiontree field.

    Arguments: n the node, v the new version. Returns n with its version
    replaced and everything else kept.  *)

Definition n_put_version (n : node) (v : versiontree) : node :=
  match n with
  | leaf a _           => leaf a v
  | internal a b l r _ => internal a b l r v
  end.

(*  Replacing a child.

    Arguments: n the node, x the new child. Returns n with its left,
    respectively right, child replaced. A leaf has no children, so on a leaf
    both do nothing  *)

Definition n_put_left (n : node) (x : child) : node :=
  match n with
  | leaf a v           => leaf a v
  | internal a b _ r v => internal a b x r v
  end.

Definition n_put_right (n : node) (x : child) : node :=
  match n with
  | leaf a v           => leaf a v
  | internal a b l _ v => internal a b l x v
  end.

(*  Reading a child.

    Argument: n the node. Returns its left, respectively right, child.
    A leaf has no children, so it answers with itself. That is junk, but no
    reachable configuration ever asks for it, by conc_threads_ok_run below.  *)

Definition n_left (n : node) : child :=
  match n with
  | leaf a v           => child_conc (leaf a v) (fun _ => c_idle)
  | internal _ _ l _ _ => l
  end.

Definition n_right (n : node) : child :=
  match n with
  | leaf a v           => child_conc (leaf a v) (fun _ => c_idle)
  | internal _ _ _ r _ => r
  end.

(*  ===============================================================  *)
(*  The interface a child offers its parent  *)

(*  These are the only things a node ever asks of a child whether concrete or
    abstract. An abstract child answers with abs_apply_op, the sequential
    specification from the abstract machine  *)

(*  The ends of the interval a child covers.

    Argument: x the child. Returns the low, respectively the high, end, read
    from the node for a concrete child and from the constructor for an
    abstract one  *)

Definition child_lo (x : child) : nat :=
  match x with
  | child_conc n _      => n_lo n
  | child_abs i _ _ _ _ => i
  end.

Definition child_hi (x : child) : nat :=
  match x with
  | child_conc n _      => n_hi n
  | child_abs _ j _ _ _ => j
  end.

(*  The version a child stores, which is what a snapshot of it returns.

    Argument: x the child. Returns corresponding version. The node's
    mutable version field for a concrete child, and the version carried for
    an abstract one  *)

Definition child_snapshot (x : child) : versiontree :=
  match x with
  | child_conc n _      => n_version n
  | child_abs _ _ _ v _ => v
  end.

(*  The set a child currently holds, as a characteristic function.

    Argument: x the child. Returns that set. A concrete child answers by
    looking the key up in its version; an abstract one hands back
    the set it is carrying.  *)

Definition child_set (x : child) : abs_set :=
  match x with
  | child_conc n _        => fun k => v_find k (n_version n)
  | child_abs _ _ set _ _ => set
  end.

(*  Building an internal node out of two finished children.

    Arguments: i and j the interval it covers, l and r the two children, tag
    the tag for the version it will store. Returns the node, whose version
    is a vnode over the two children's snapshots with their sums added.  *)

Definition n_build (i j : nat) (l r : child) (tag : nat) : node :=
  internal i j l r
    (vnode tag i j
       (v_sum (child_snapshot l) + v_sum (child_snapshot r))
       (child_snapshot l) (child_snapshot r)).

(*  ===============================================================  *)
(*  Well formedness  *)

(*  Well formedness of a node.

    Argument: n the node. Returns a Prop.

    A leaf is well formed when its version covers exactly its own key and is
    itself a well formed version tree. An internal node is well formed when
    its version covers its interval, its version is well formed, its two children
    cover the right intervals, and both children are well formed.  *)

Fixpoint wf_node (n : node) : Prop :=
  match n with
  | leaf i v           => v_covers v i i /\ wf v
  | internal a b l r v =>
      v_covers v a b /\ wf v /\
      child_lo l = a /\ child_hi l = mid a b /\
      child_lo r = mid a b + 1 /\ child_hi r = b /\
      wf_child l /\ wf_child r
  end

(*  Well formedness of a child.

    Argument: x the child. Returns a Prop. A concrete child is well formed when
    its node is. An abstract child is well formed when the version it
    stores is well formed with the right interval, holds the same keys as the
    abs_set, and covers the right interval  *)

with wf_child (x : child) : Prop :=
  match x with
  | child_conc n _        => wf_node n
  | child_abs a b set v _ => v_covers v a b /\ wf v /\ v_elements v = abs_elems a b set
  end.

(*  A well formed node and its version agree about which
    interval they are talking about.

      n.version.i = n.i    and    n.version.j = n.j  *)

Lemma node_version_interval : forall (n : node), wf_node n
  -> v_lo (n_version n) = n_lo n /\ v_hi (n_version n) = n_hi n.
Proof.
  intros n Hwf. destruct n; simpl in *;
    destruct Hwf as [[Hlo Hhi] _]; split; assumption.
Qed.

(*  ===============================================================  *)
(*  Talking to a child  *)

(*  A thread handing an update down to a child, which is the child's invoke.
    It emits no event, since it happens inside this node.

    Arguments: o the update, t the thread, x the child. Returns the child
    with t's state there set to the start of o (pending for an abstract
    child, and for a real one the first state of an update on that shape of
    node).  *)

Definition child_call (o : op) (t : tid) (x : child) : child :=
  match x with
  | child_conc n st =>
      child_conc n (upd st t (if n_is_leaf n then c_read o else c_call o))
  | child_abs a b set v st => child_abs a b set v (upd st t (a_pending o))
  end.

(*  The answer a child owes thread t, if it has finished t's update.

    Arguments: t the thread, x the child. Returns Some of the answer when t
    is waiting to return inside the child, and None otherwise  *)

Definition child_answer (t : tid) (x : child) : option res :=
  match x with
  | child_conc _ st =>
      match st t with
      | c_returning ans => Some ans
      | _               => None
      end
  | child_abs _ _ _ _ st =>
      match st t with
      | a_returning ans => Some ans
      | _               => None
      end
  end.

(*  Collecting that answer, which is the child's return.

    Arguments: t the thread, x the child. Returns the child with t idle
    inside it again  *)

Definition child_done (t : tid) (x : child) : child :=
  match x with
  | child_conc n st        => child_conc n (upd st t c_idle)
  | child_abs a b set v st => child_abs a b set v (upd st t a_idle)
  end.

(*  One step of an abstract child on behalf of thread t, which is that
    child's linearization point. The update takes effect on the set, and the
    version the child stores is rebuilt to match, so that wf_child keeps
    holding.

    Arguments: t the thread, tag the next free tag, x the child. Returns the
    child afterwards and the next free tag. A thread with nothing pending in
    the child takes no step. A real child is not handled here, since its
    step is a step of the concrete machine itself, which is why conc_step
    below does that case  *)

Definition abs_child_step (t : tid) (tag : nat) (x : child) : child * nat :=
  match x with
  | child_abs a b set v st =>
      match st t with
      | a_pending o =>
          let (set', ans) := abs_apply_op a b o set in
          let (v', tag') :=
            match o with
            | op_insert k => if set k then (v, tag) else v_set_key k true tag v
            | op_delete k => if set k then v_set_key k false tag v else (v, tag)
            | _           => (v, tag)
            end in
          (child_abs a b set' v' (upd st t (a_returning ans)), tag')
      | _ => (x, tag)
      end
  | child_conc _ _ => (x, tag)
  end.

(*  ###############################################################  *)
(*  The concrete automaton  *)

(*  Like the abstract machine, everything below takes the interval i..j that
    this node covers as an ordinary argument.  *)

(*  A configuration of the concrete machine, the whole state at one moment.

    Fields: root is the shared node (the trie) we are interested in. fresh is
    the next unused tag. cstate says where every thread is with its local
    variables.  *)

Record conc_config : Type := ConcConfig {
  root       : node;
  fresh      : nat;
  cstate : tid -> conc_progstate
}.

(*  The starting configuration.

    Arguments: tree, the node tree to run on, tag the first unused tag, which
    has to be larger than every tag already inside tree. Returns the
    configuration with no thread started  *)

Definition conc_init (tree : node) (tag : nat) : conc_config :=
  {| root := tree; fresh := tag; cstate := fun _ => c_idle |}.

(*  Two helper functions for readability in conc_step.
    
    Moving one thread and touching nothing else.

    Arguments: c the configuration, t the thread, p its new state. Returns c
    with thread t at p, the node and the tag supply unchanged. Every use
    of it is a step that reads memory or computes, but does not write.  *)

Definition put_state (c : conc_config) (t : tid) (p : conc_progstate) : conc_config :=
  {| root := c.(root); fresh := c.(fresh); cstate := upd c.(cstate) t p |}.

(*  Moving one thread and writing shared memory at the same time.

    Arguments: tree the new node, tag the new tag supply, c the
    configuration, t the thread, p its new state. Returns a configuration
    with all three replaced. Every use of it is a real write.  *)

Definition put_all (tree : node) (tag : nat) (c : conc_config)
                   (t : tid) (p : conc_progstate) : conc_config :=
  {| root := tree; fresh := tag; cstate := upd c.(cstate) t p |}.

(*  Whether thread t is allowed to take action a from configuration c.

    Arguments: i and j the interval, c the configuration, t the thread, a the
    action. Returns a bool.
    
    The only guard that can really fail is op_ok. A thread in the middle of
    an operation can always take its next step, and which shape of node it is
    running on was decided at the invoke and never changes, so we don't need
    to retest.  *)

Definition conc_enabled (i j : nat) (c : conc_config) (t : tid) (a : action) : bool :=
  match a, c.(cstate) t with
  | act_invoke o, c_idle      => op_ok i j o
  | act_return, c_returning _ => true
  | act_step, c_idle          => false
  | act_step, c_returning _   => false
  | act_step, _               => true
  | _, _                      => false
  end.

(*  One step of one node, covering both shapes of node and all seven
    operations. This is the concrete machine's transition, with the configuration
    passed as its three fields, so that it can call itself on a child.

    Arguments: i and j the interval, n the node, tag the next free tag,
    st where every thread is, t the thread taking the step, a the action it
    takes. Returns the configuration afterwards paired with the events
    emitted. A disallowed step is a stutter, similar to before.

    Again, each transition or arm is one atomic memory access. The local tests
    between accesses cost nothing and are folded into the step that reaches
    them, so there are fewer program counters than lines of pseudocode.

    The one arm that is not a memory access of this node is c_wait where a
    thread waits on a child to do the update and spends its turn inside that
    child. For a real child that is a step of this very function, one level down,
    making it a Fixpoint on n. The events a child emits are dropped, because the
    child's invokes and returns happen inside this node and an outside
    observer cannot see them.  *)

Fixpoint conc_step (i j : nat) (n : node) (tag : nat) (st : tid -> conc_progstate)
                   (t : tid) (a : action) {struct n} : conc_config * list event :=
  let c := {| root := n; fresh := tag; cstate := st |} in
  match a, st t with

  (*  ---- announcing an operation -----------------------------------  *)
  | act_invoke o, c_idle =>
      if op_ok i j o
      then let p := if negb (is_update o) then c_query o
                    else if n_is_leaf c.(root) then c_read o
                    else c_call o in
           (put_state c t p, [ev_invoke t o])
      else (c, [])

  (*  ---- a leaf reads its version, then flips the bit if it must ----  *)
  | act_step, c_read o =>
      let old := n_version c.(root) in
      let p := if v_sum old =? target_bit o
               then c_returning (res_bool false)
               else c_flip o old in
      (put_state c t p, [])

  | act_step, c_flip o old =>
      if v_id (n_version c.(root)) =? v_id old
      then (*  only an update reaches here, so an insert sets the bit
               and a delete clears it  *)
           (put_all (n_put_version c.(root) (vleaf c.(fresh) i (target_bit o)))
                    (S c.(fresh)) c t (c_returning (res_bool true)), [])
      else (put_state c t (c_returning (res_bool false)), [])

  (*  ---- an internal node hands the update to a child, and waits ----  *)
  | act_step, c_call o =>
      if op_key o <=? mid i j
      then (put_all (n_put_left c.(root) (child_call o t (n_left c.(root))))
                    c.(fresh) c t (c_wait o), [])
      else (put_all (n_put_right c.(root) (child_call o t (n_right c.(root))))
                    c.(fresh) c t (c_wait o), [])

  | act_step, c_wait o =>
      match n with
      | leaf _ _ => (c, [])           (*  never reached, by conc_threads_ok  *)
      | internal lo hi l r v =>
          if op_key o <=? mid i j
          then match child_answer t l with
               | Some ans =>          (*  the child's return  *)
                   (put_all (internal lo hi (child_done t l) r v) c.(fresh) c t
                            (c_own o ans 1), [])
               | None =>              (*  one step inside the child  *)
                   let (l', tag') :=
                     match l with
                     | child_conc n' st' =>
                         let (c', _) := conc_step (n_lo n') (n_hi n') n' c.(fresh)
                                                  st' t act_step in
                         (child_conc c'.(root) c'.(cstate), c'.(fresh))
                     | child_abs _ _ _ _ _ => abs_child_step t c.(fresh) l
                     end in
                   (put_all (internal lo hi l' r v) tag' c t (c_wait o), [])
               end
          else match child_answer t r with
               | Some ans =>
                   (put_all (internal lo hi l (child_done t r) v) c.(fresh) c t
                            (c_own o ans 1), [])
               | None =>
                   let (r', tag') :=
                     match r with
                     | child_conc n' st' =>
                         let (c', _) := conc_step (n_lo n') (n_hi n') n' c.(fresh)
                                                  st' t act_step in
                         (child_conc c'.(root) c'.(cstate), c'.(fresh))
                     | child_abs _ _ _ _ _ => abs_child_step t c.(fresh) r
                     end in
                   (put_all (internal lo hi l r' v) tag' c t (c_wait o), [])
               end
      end

  (*  ---- the four steps of a refresh --------------------------------  *)
  | act_step, c_own o ans att =>
      (put_state c t (c_left o ans att (n_version c.(root))), [])

  | act_step, c_left o ans att old =>
      (put_state c t (c_right o ans att old
                        (child_snapshot (n_left c.(root)))), [])

  | act_step, c_right o ans att old vl =>
      (put_state c t (c_cas o ans att old vl
                        (child_snapshot (n_right c.(root)))), [])

  | act_step, c_cas o ans att old vl vr =>
      if v_id (n_version c.(root)) =? v_id old
      then (put_all (n_put_version c.(root)
                       (vnode c.(fresh) i j (v_sum vl + v_sum vr) vl vr))
                    (S c.(fresh)) c t (c_returning ans), [])
      else if att =? 1
      then (*  the first attempt lost the race, so refresh once more  *)
           (put_state c t (c_own o ans 2), [])
      else (*  two attempts are enough, someone else did the work  *)
           (put_state c t (c_returning ans), [])

  (*  ---- a query is one read of this node's own version -------------  *)
  | act_step, c_query o =>
      (put_state c t (c_returning (v_op_result o (n_version c.(root)))), [])

  (*  ---- handing the answer back ------------------------------------  *)
  | act_return, c_returning ans =>
      (put_state c t c_idle, [ev_return t ans])

  | _, _ => (c, [])
  end.

(*  A small wrapper over conc_step, on a whole configuration.

    Arguments: i and j the interval, c the configuration, t the thread, a the
    action. Returns the configuration afterwards paired with the events
    emitted.  *)

Definition conc_next (i j : nat) (c : conc_config) (t : tid) (a : action)
                     : conc_config * list event :=
  conc_step i j c.(root) c.(fresh) c.(cstate) t a.

(*  Replaying a whole execution, one step after another.

    Arguments: i and j the interval, c the starting configuration, e the
    execution. Returns the final configuration paired with the trace  *)

Fixpoint conc_run (i j : nat) (c : conc_config) (e : execution)
                  : conc_config * list event :=
  match e with
  | [] => (c, [])
  | (t, a) :: rest =>
      let (c',  evs)  := conc_next i j c t a in
      let (c'', evs') := conc_run i j c' rest in
      (c'', evs ++ evs')
  end.

(*  The trace of an execution, throwing the final configuration away.  *)

Definition conc_trace_from (i j : nat) (c : conc_config) (e : execution)
                           : list event :=
  snd (conc_run i j c e).

(*  Whether an execution is one the machine could really have performed.

    Arguments: i and j the interval, c the starting configuration, e the
    execution. Returns true when every step was enabled at the moment it was
    reached. The next block builds executions that meet this by construction  *)

Fixpoint conc_legal (i j : nat) (c : conc_config) (e : execution) : bool :=
  match e with
  | [] => true
  | (t, a) :: rest =>
      conc_enabled i j c t a && conc_legal i j (fst (conc_next i j c t a)) rest
  end.

(*  The same generator as in the abstract machine. A schedule says only whose
    turn it is next, each thread has a program of operations to announce, and
    the two together are turned into an execution.

    Nobody writing a schedule has to know that a query here costs one
    internal step, an update at a leaf two, and an update at an internal node
    seven or more, depending on what its children are and on whether its
    first refresh wins. The generator reads that off the thread's own statei.  *)

(*  A thread already running an operation has no choice about its next
    action. At a leaf it is the read or the CAS, at an internal node it is
    handing the key down, a turn spent waiting on the child, or one of the
    four steps of a refresh, and for a thread that owes an answer it is the
    return.

    Argument: p the thread's state. Returns that forced action, or None when
    the thread is idle and has to start something from its program.  *)

Definition conc_busy_act (p : conc_progstate) : option action :=
  match p with
  | c_idle        => None
  | c_returning _ => Some act_return
  | _             => Some act_step
  end.

(*  Turning a schedule and the programs into an execution.

    Arguments: i and j the interval, c the configuration it all starts from,
    sigma the schedule, P what each thread still has to do. Returns the
    execution those turns amount to. See abs_exec for the three cases.  *)

Fixpoint conc_exec (i j : nat) (c : conc_config) (sigma : sched) (P : progs)
                   : execution :=
  match sigma with
  | [] => []
  | t :: rest =>
      match conc_busy_act (c.(cstate) t) with
      | Some a =>
          (t, a) :: conc_exec i j (fst (conc_next i j c t a)) rest P
      | None =>
          match P t with
          | []      => conc_exec i j c rest P
          | o :: os =>
              (t, act_invoke o)
              :: conc_exec i j (fst (conc_next i j c t (act_invoke o)))
                   rest (upd P t os)
          end
      end
  end.

(*  and whatever schedule you hand it, the execution that comes out is one
    the machine really could have performed, provided the programs only ask
    for keys this node owns  *)

Theorem conc_exec_legal : forall (i j : nat) (c : conc_config)
                                 (sigma : sched) (P : progs),
  wf_progs i j P -> conc_legal i j c (conc_exec i j c sigma P) = true.
Proof.
  intros i j c sigma. revert c.
  induction sigma as [| t rest IH]; intros c P HP; simpl.
  - reflexivity.
  - destruct (conc_busy_act (cstate c t)) as [act |] eqn:Eb.
    + simpl.
      assert (Hen : conc_enabled i j c t act = true).
      { unfold conc_busy_act in Eb. unfold conc_enabled.
        destruct (cstate c t); inversion Eb; subst; reflexivity. }
      rewrite Hen. simpl. apply IH. exact HP.
    + destruct (P t) as [| o os] eqn:EP.
      * apply IH. exact HP.
      * simpl.
        assert (Hidle : cstate c t = c_idle).
        { unfold conc_busy_act in Eb. destruct (cstate c t); congruence. }
        assert (Hok : op_ok i j o = true).
        { apply (HP t). rewrite EP. now left. }
        rewrite Hidle, Hok. simpl. apply IH.
        intros t' o' Hin. unfold upd in Hin.
        destruct (t' =? t) eqn:Et.
        -- apply (HP t). rewrite EP. now right.
        -- apply (HP t'). exact Hin.
Qed.

(*  The trace of a schedule is the trace of the execution it generates. This
    is the form every result about the concrete machine is stated in, and it
    is what linearizability will be about.

    Arguments: i and j the interval, c the starting configuration, sigma the
    schedule, P the programs. Returns the list of events  *)

Definition conc_trace (i j : nat) (c : conc_config) (sigma : sched) (P : progs)
                      : list event :=
  conc_trace_from i j c (conc_exec i j c sigma P).

(*  and the configuration a schedule leaves behind, for when what matters is
    where the data structure ended up rather than what it said  *)

Definition conc_after (i j : nat) (c : conc_config) (sigma : sched) (P : progs)
                      : conc_config :=
  fst (conc_run i j c (conc_exec i j c sigma P)).

(*  ===============================================================  *)
(*  Reasoning about a step  *)

(*  Tactic for splitting a step into its branches. conc_next is one big match
    with a test or two inside most arms, so every proof about it begins by taking
    those apart. This does that and keeps the equation for each test, so the
    branch a goal came from is still readable afterwards
    
    "Keep splitting the goal on whatever test is blocking it, remembering which
     way each test went, and simplify after each split, until nothing is blocking."  *)

Ltac conc_next_cases :=
  repeat (match goal with
          | |- context [ match ?x with _ => _ end ] => destruct x eqn:?
          end; simpl).

(*  The catch all branch of conc_next is inert (a step that was not enabled
    leaves the configuration untouched and emits no events). Generated
    executions never reach it, by conc_exec_legal. This is just here to explain
    the branch rather than to carry any weight.  *)

Lemma conc_next_disabled : forall (i j : nat) (c : conc_config) (t : tid) (a : action),
  conc_enabled i j c t a = false -> conc_next i j c t a = (c, []).
Proof.
  intros i j [n tag st] t a H. unfold conc_enabled in H. unfold conc_next.
  simpl in *.
  destruct n; destruct a as [o | |]; simpl;
    destruct (st t) eqn:E; simpl in *; try discriminate; try reflexivity;
    rewrite H; reflexivity.
Qed.

(*  ===============================================================  *)
(*  Thread states always agree with the shape of the node  *)

(*  No step ever changes the shape of the node. Whether c.(root) is a
    leaf is the same before and after any step, so it is decided once at
    conc_init and never moves again  *)

Lemma conc_shape_fixed : forall (i j : nat) (c : conc_config) (t : tid) (a : action),
  n_is_leaf (fst (conc_next i j c t a)).(root) = n_is_leaf c.(root).
Proof.
  intros i j [n tag st] t a. unfold conc_next. simpl.
  destruct n; destruct a as [o | |]; simpl; conc_next_cases; reflexivity.
Qed.

(*  A step only moves the thread that takes it and any other thread t' is in the
    same state afterwards as before  *)

Lemma conc_state_other : forall (i j : nat) (c : conc_config) (t : tid)
                                (a : action) (t' : tid),
  t' <> t -> (fst (conc_next i j c t a)).(cstate) t' = c.(cstate) t'.
Proof.
  intros i j [n tag st] t a t' Hne.
  assert (Hb : (t' =? t) = false) by (apply Nat.eqb_neq; exact Hne).
  unfold conc_next. simpl.
  destruct n; destruct a as [o | |]; simpl; conc_next_cases;
    unfold put_state, put_all, upd; simpl; rewrite ?Hb; reflexivity.
Qed.

(*  What a thread state may hold, given the shape of the node it is
    running on.

    Arguments: at_leaf, which says whether the node is a leaf, and p the
    thread state. Returns a Prop.

    c_read and c_flip demand at_leaf = true, the six states of an internal
    node demand at_leaf = false, and all eight demand that the operation is
    an update. c_query demands a query. c_idle and c_returning demand
    nothing.  *)

Definition conc_progstate_ok (at_leaf : bool) (p : conc_progstate) : Prop :=
  match p with
  | c_idle            => True
  | c_read o          => at_leaf = true  /\ is_update o = true
  | c_flip o _        => at_leaf = true  /\ is_update o = true
  | c_call o          => at_leaf = false /\ is_update o = true
  | c_wait o          => at_leaf = false /\ is_update o = true
  | c_own o _ _       => at_leaf = false /\ is_update o = true
  | c_left o _ _ _    => at_leaf = false /\ is_update o = true
  | c_right o _ _ _ _ => at_leaf = false /\ is_update o = true
  | c_cas o _ _ _ _ _ => at_leaf = false /\ is_update o = true
  | c_query o         => is_update o = false
  | c_returning _     => True
  end.

(*  The same condition asked of every thread of a configuration at once.

    Argument: c the configuration. Returns a Prop.  *)

Definition conc_threads_ok (c : conc_config) : Prop :=
  forall t, conc_progstate_ok (n_is_leaf c.(root)) (c.(cstate) t).

(*  It holds when nothing has started, since every thread is idle and c_idle
    demands nothing  *)

Lemma conc_threads_ok_init : forall (tree : node) (tag : nat),
  conc_threads_ok (conc_init tree tag).
Proof. intros tree tag t. exact I. Qed.

(*  and it survives one step, whichever thread takes it  *)

Lemma conc_threads_ok_step : forall (i j : nat) (c : conc_config) (t : tid)
                                    (a : action),
  conc_threads_ok c -> conc_threads_ok (fst (conc_next i j c t a)).
Proof.
  intros i j [n tag st] t a H t'.
  rewrite (conc_shape_fixed i j {| root := n; fresh := tag; cstate := st |} t a).
  destruct (Nat.eq_dec t' t) as [Heq | Hne].
  - subst t'. assert (Ht := H t). simpl in Ht.
    unfold conc_next. simpl.
    destruct n; destruct a as [o | |]; simpl in *;
      destruct (st t) eqn:E; rewrite ?E in Ht; simpl in *;
      conc_next_cases;
      unfold put_state, put_all, upd; simpl; rewrite ?Nat.eqb_refl, ?E; simpl;
      try exact I; try exact Ht;
      try (destruct o; simpl in *; intuition (try congruence));
      intuition (try congruence).
  - rewrite (conc_state_other i j {| root := n; fresh := tag; cstate := st |}
                              t a t' Hne).
    apply H.
Qed.

(*  and therefore it holds everywhere any execution can reach, starting from
    any configuration that satisfies it, in particular from conc_init.

    This lemma justifies conc_next having no leaf test past the invoke.  *)

Lemma conc_threads_ok_replay : forall (i j : nat) (e : execution) (c : conc_config),
  conc_threads_ok c -> conc_threads_ok (fst (conc_run i j c e)).
Proof.
  intros i j e.
  induction e as [| [t a] rest IH]; intros c H.
  - exact H.
  - simpl. destruct (conc_next i j c t a) as [c' evs] eqn:E.
    destruct (conc_run i j c' rest) as [c'' evs'] eqn:E'. simpl.
    assert (Hc' : conc_threads_ok c').
    { replace c' with (fst (conc_next i j c t a)) by (rewrite E; reflexivity).
      apply conc_threads_ok_step. exact H. }
    specialize (IH c' Hc'). rewrite E' in IH. exact IH.
Qed.

(*  and so it holds after any schedule at all, which is the form it gets
    used in.  *)

Theorem conc_threads_ok_run : forall (i j : nat) (c : conc_config)
                                     (sigma : sched) (P : progs),
  conc_threads_ok c -> conc_threads_ok (conc_after i j c sigma P).
Proof.
  intros i j c sigma P H. unfold conc_after. apply conc_threads_ok_replay. exact H.
Qed.
