From Trie Require Import AbstractAutomata.

(* ################################################################# *)
(** The concrete implementation *)

Definition mid (i j : nat) : nat := (i + j) / 2.

Inductive versiontree : Type :=
  | vleaf (i : nat)                 (* the one key it covers *)
          (s : nat)                 (* sum *)
  | vnode (i j : nat)               (* the interval it covers *)
          (s : nat)                 (* sum *)
          (l r : versiontree).

Inductive nodetree : Type :=
  | nleaf (i : nat)
          (v : versiontree)         (* the mutable version field *)
  | nnode (i j : nat)
          (v : versiontree)         (* the mutable version field *)
          (l r : nodetree).

Definition version_of (n : nodetree) : versiontree :=
  match n with
  | nleaf _ v       => v
  | nnode _ _ v _ _ => v
  end.

Definition sum_of (v : versiontree) : nat :=
  match v with
  | vleaf _ s       => s
  | vnode _ _ s _ _ => s
  end.

Definition v_lo (v : versiontree) : nat :=
  match v with
  | vleaf i _       => i
  | vnode i _ _ _ _ => i
  end.

Definition v_hi (v : versiontree) : nat :=
  match v with
  | vleaf i _       => i
  | vnode _ j _ _ _ => j
  end.

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

Definition v_covers (v : versiontree) (i j : nat) : Prop :=
  v_lo v = i /\ v_hi v = j.

Definition n_covers (n : nodetree) (i j : nat) : Prop :=
  n_lo n = i /\ n_hi n = j.

(** Predicates to ensure fields are correct for node and version tree*)

Fixpoint wf (v : versiontree) : Prop :=
  match v with
  | vleaf _ s       => s = 0 \/ s = 1
  | vnode i j s l r =>
      v_covers l i (mid i j) /\
      v_covers r (mid i j + 1) j /\
      s = sum_of l + sum_of r /\ wf l /\ wf r
  end.

Fixpoint wf_node (n : nodetree) : Prop :=
  match n with
  | nleaf i v       => v_covers v i i /\ wf v
  | nnode i j v l r =>
      v_covers v i j /\ wf v /\
      n_covers l i (mid i j) /\
      n_covers r (mid i j + 1) j /\
      wf_node l /\ wf_node r
  end.

(** Basically the set(v) *)

Fixpoint elements (v : versiontree) : list key :=
  match v with
  | vleaf k s       => if s =? 1 then [k] else []
  | vnode _ _ _ l r => elements l ++ elements r
  end.

Fixpoint select (r : nat) (v : versiontree) : option key :=
  match v with
  | vleaf k s        => if s =? 1
                        then (if r =? 1 then Some k else None)
                        else None
  | vnode _ _ _ ltree rtree => if r <=? sum_of ltree
                        then select r ltree
                        else select (r - sum_of ltree) rtree
  end.

(* ================================================================= *)
(** Arithmetic facts about mid *)

Lemma mid_div_mod : forall i j,
  i + j = 2 * mid i j + (i + j) mod 2 /\ (i + j) mod 2 < 2.
Proof.
  intros i j. unfold mid. split.
  - apply Nat.div_mod_eq.
  - apply Nat.mod_upper_bound. lia.
Qed.

Lemma mid_gt : forall i j, j < i -> mid i j < i.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

Lemma mid_lower : forall i j, i <= j -> i <= mid i j.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

Lemma mid_upper : forall i j, i <= j -> mid i j <= j.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

Lemma mid_lt : forall i j, i < j -> mid i j < j.
Proof.
  intros i j H. destruct (mid_div_mod i j) as [H1 H2]. lia.
Qed.

(* ================================================================= *)
(** Inverted intervals are uninhabited *)

(** With the bounds sitting in fields this is no longer given by the type,
    so it has to be read out of [wf] instead *)

Lemma versiontree_empty : forall v,
  wf v -> v_hi v < v_lo v -> False.
Proof.
  intros v.
  induction v as [ i s | i j s l IHl r IHr ]; intros Hwf Hlt; simpl in *.
  - lia.
  - destruct Hwf as [[Hll Hlh] [_ [_ [Hl _]]]].
    apply (IHl Hl). rewrite Hll, Hlh. apply mid_gt. exact Hlt.
Qed.

Lemma versiontree_le : forall v, wf v -> v_lo v <= v_hi v.
Proof.
  intros v Hwf.
  destruct (Nat.le_gt_cases (v_lo v) (v_hi v)) as [H | H].
  - exact H.
  - exfalso. apply (versiontree_empty v Hwf). exact H.
Qed.

(* ================================================================= *)
(** The elements lie inside the interval *)

Lemma elements_bounded : forall v x,
  wf v -> In x (elements v) -> v_lo v <= x /\ x <= v_hi v.
Proof.
  intros v.
  induction v as [ i s | i j s l IHl r IHr ]; intros x Hwf Hin; simpl in *.
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
(** The sum field counts the elements *)

Theorem sum_correct : forall v,
  wf v -> sum_of v = length (elements v).
Proof.
  intros v.
  induction v as [ i s | i j s l IHl r IHr ]; intros Hwf; simpl in *.
  - destruct Hwf as [H | H]; subst; reflexivity.
  - destruct Hwf as [_ [_ [Hs [Hl Hr]]]].
    rewrite length_app.
    rewrite <- IHl by exact Hl.
    rewrite <- IHr by exact Hr.
    exact Hs.
Qed.

(* ================================================================= *)
(** n.version.i = n.i and n.version.j = v.version.j *)

(** Also no longer given by the type, it is now one of the conditions in
    [wf_node] *)

Lemma node_version_interval : forall n,
  wf_node n -> v_lo (version_of n) = n_lo n /\ v_hi (version_of n) = n_hi n.
Proof.
  intros n Hwf. destruct n; simpl in *;
    destruct Hwf as [[Hlo Hhi] _]; split; assumption.
Qed.

(* ================================================================= *)
(** Select returns the r-th smallest element *)

(** The hypothesis 1 <= r is needed because ranks start at one and with
    r = 0 the subtraction on the right hand side would underflow and
    the statement would be false. *)

Theorem select_correct : forall v r,
  wf v ->
  1 <= r ->
  select r v = nth_error (elements v) (r - 1).
Proof.
  intros v.
  induction v as [ i s | i j s l IHl r IHr ]; intros q Hwf Hq; simpl in *.
  - destruct Hwf as [H | H]; subst; simpl.
    + (* the key is absent, so nothing can be selected *)
      rewrite nth_error_nil. reflexivity.
    + (* the key is present, so only rank one succeeds *)
      destruct q as [| q']. lia. simpl.
      rewrite Nat.sub_0_r.
      destruct q' as [| q'']; simpl.
      * reflexivity.
      * rewrite nth_error_nil. reflexivity.
  - destruct Hwf as [_ [_ [Hs [Hl Hr]]]].
    rewrite (sum_correct l Hl).
    destruct (Nat.leb_spec q (length (elements l))) as [Hcmp | Hcmp].
    + (* the answer is in the left subtree, at the same rank *)
      rewrite IHl by assumption.
      rewrite nth_error_app1 by lia.
      reflexivity.
    + (* the answer is in the right subtree, at a reduced rank *)
      rewrite IHr by (solve [ assumption | lia ]).
      rewrite nth_error_app2 by lia.
      f_equal. lia.
Qed.
