Require Import SegmentTrees.Definitions.

From Coq Require Import Recdef List.
Import ListNotations.
Require Import Lia.

Compute segtree_example_123.

Lemma height_zero_is_empty : forall t, height t = 0 -> t = Empty.
Proof.
  destruct t.
  * simpl. reflexivity.
  * simpl. intros. discriminate.
Qed.

Lemma build_singleton_empty_sides : forall (x lbound rbound : nat),
  build [x] lbound rbound = Node Empty x lbound rbound Empty.
Proof.
  intros.
  simpl. unfold build. simpl.
  reflexivity.
Qed.

Lemma length_one_list_is_singleton : forall (l : list nat), length l = 1 ->
  exists x, l = [x].
Proof.
  intros l Hlen.
  destruct l as [|x l'].
  - simpl in Hlen. lia.
  - destruct l' as [|y l''].
    + exists x. reflexivity.
    + simpl in Hlen. lia.
Qed.

Lemma leaf_means_empty_children : forall l v lb rb r, lb = rb -> Node l v lb rb r = Node Empty v lb rb Empty ->
  amountOfNodes l = 0 /\ amountOfNodes r = 0.
Proof.
  intros l v lb rb r Hbounds Heq.
  inversion Heq. subst.
  split. reflexivity. reflexivity.
Qed.

Lemma height_zero_node_children_empty : forall l v lbound rbound r, height (Node l v lbound rbound r) = 0 ->
  l = Empty /\ r = Empty /\ Node l v lbound rbound r = Empty.
Proof.
  intros l v lbound rbound r H.
  simpl in H.
  inversion H.
Qed.

Lemma height_eq_zero_iff_empty : forall (t : Segtree), height t = 0 -> t = Empty.
Proof.
  intros. destruct t.
  * reflexivity.
  * apply height_zero_node_children_empty in H.
    inversion H.
    inversion H1.
    assumption.
Qed.

Lemma height_eq_0_iff_empty :
  forall t, balanced t -> height t = 0 -> t = Empty.
Proof.
  intros t Hbal Hh.
  destruct t.
  - reflexivity.
  - simpl in Hh. lia.
Qed.

Lemma lbound_eq_rbound_means_leaf : forall l v lbound rbound r, balanced (Node l v lbound rbound r) -> lbound = rbound ->
    l = Empty /\ r = Empty.
Proof.
  intros l v lbound rbound r Hbal Heq.
  inversion Hbal as [| l' r' v' lb rb Hbl Hbr Hdiff]; subst.
  unfold height_diff_ok in Hdiff.
Admitted.

Lemma leaf_has_no_children : forall l v lbound rbound r, balanced (Node l v lbound rbound r) -> lbound = rbound ->
  l = Empty /\ r = Empty.
Proof.
  intros l v lbound rbound r Hbal Heq.
  inversion Hbal as [| l' r' v' lb rb Hbl Hbr Hhd]; subst. unfold height_diff_ok in Hhd. destruct Hhd.
  *
Admitted.

Lemma leaf_node_empty_children_from_build : forall (l : list nat) (lbound rbound : nat), lbound = rbound -> length l = 1 ->
  build l lbound rbound = Node Empty (hd 0 l) lbound rbound Empty.
Proof.
  intros. induction l.
  * simpl. discriminate.
  * simpl. destruct l as [| b l']. 
    - constructor.
    - simpl in H0. lia.
Qed.

Lemma amountOfNodes_leaf : forall (x lbound rbound : nat), lbound = rbound ->
  amountOfNodes (Node Empty x lbound rbound Empty) = 1.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma sublist_nil : forall i j,
  sublist [] i j = [].
Proof.
  intros i j.
  unfold sublist.
  rewrite skipn_nil.
  rewrite firstn_nil.
  reflexivity.
Qed.

Lemma update_pointUpdate_cancel : forall (t : Segtree) (lbound rbound value : nat), lbound <= S(rbound) ->
  update (pointUpdate t (S rbound) value) lbound rbound value = update t lbound (S rbound) value.
Proof.
Admitted.

Lemma update_pointUpdate_cancel2 : forall (t : Segtree) (lbound rbound value : nat), lbound <= S(rbound) ->
  pointUpdate (update t lbound rbound value) rbound value = update t lbound rbound value.
Proof.
Admitted.

Lemma update_pointUpdate_cancel3 : forall (t : Segtree) (lbound rbound value : nat), lbound <= S(rbound) ->
  update t lbound (S rbound) value = update (update t lbound (S rbound) value) lbound rbound value.
Proof.
Admitted.