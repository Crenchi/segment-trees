Require Import SegmentTrees.Lemmas.
Require Import SegmentTrees.Definitions.

Require Import Nat.
Require Import List.
Require Import Bool.
Require Import Datatypes.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Arith.
Require Import Arith Psatz.
From Coq Require Import Recdef List.
Require Import Coq.Arith.Wf_nat.
Import ListNotations.
Require Coq.Program.Wf.
Require Coq.Classes.RelationClasses.
Require Coq.Numbers.Natural.Abstract.NDiv0.

(* BUILD LEMMAS ==============================================================*)

(* A list of length 0 returns an empty segment tree*)
Lemma build_empty_list_empty_tree : forall lbound rbound,
    build [] lbound rbound = Empty.
Proof.
  intros lbound rbound.
  simpl.
  reflexivity.
Qed.

(* A list of length 1 returns a node with empty children *)
Lemma build_leaf_has_empty_children : forall (x : nat) (lbound rbound : nat), lbound = rbound ->
    build [x] lbound rbound = Node Empty x lbound rbound Empty.
Proof.
  intros. constructor.
Qed.

(* A list with a finite list of number in it can turn into a segment tree*)
Lemma build_produces_segment_tree : forall (l : list nat) (lbound rbound : nat),
    exists t, build l lbound rbound = t.
Proof.
  intros l lbound rbound.
  exists (build l lbound rbound).
  reflexivity.
Qed.

(* A segment tree is by definition balanced*)
Lemma build_produces_balanced2 : forall (l : list nat) (lbound rbound : nat),
  balanced (build l lbound rbound).
Proof.
  intros.
  remember (build l lbound rbound) as t eqn:Ht.
  induction t.
  * constructor.
  * intros. apply balancedNode.
    ** apply TODO.
    ** apply TODO.
    ** apply TODO.
Admitted.

(*Fixpoint treeToList (t : Segtree) : list nat :=
  match t with
  | Empty => []
  | Node lTree value lbound rbound rTree =>

Lemma all_segment_trees_are_built_from_list : forall (t leftTree rightTree : Segtree) (value lbound rbound  : nat) (l : list nat) ,
  Node leftTree value lbound rbound rightTree = build l lbound rbound -> length(treeToList leftTree) < length l /\ length (treeToList rightTree) < length l.
Proof.
Admitted.*)



Lemma build_unf l lbound rbound :
  build l lbound rbound =
  match l with
  | [] => Empty
  | [x] => Node Empty x lbound rbound Empty 
  | _ =>
    let mid : nat := Nat.div (length l + 1) 2 in
    let firstHalf := firstn mid l in
    let secondHalf := skipn mid l in
    let leftTree := build firstHalf lbound (mid-1) in
    let rightTree := build secondHalf mid rbound in
    let value :=
      match leftTree, rightTree with
      | Node _ lv _ _ _, Node _ rv _ _ _ => lv + rv
      | Node _ lv _ _ _, Empty => lv
      | Empty, Node _ rv _ _ _ => rv
      | Empty, Empty => 0
      end
    in Node leftTree value lbound rbound rightTree
  end.
Proof. Admitted.

(* A segment tree is by definition balanced*)
Lemma build_produces_balanced : forall (l : list nat) (lbound rbound : nat),
  balanced (build l lbound rbound).
Proof.
  apply (well_founded_induction (well_founded_ltof _ (@length nat)) (fun l => forall lbound rbound, balanced (build l lbound rbound))).
  intros l IH lbound rbound.
  destruct l as [|x xs].
  ** rewrite (build_unf [] _ _); simpl. constructor.
  ** destruct xs as [|x2 xs]; rewrite build_unf.
     +++ admit. 
     +++ set (mid := (length (x :: x2 :: xs) + 1) / 2).
         set (firstHalf := firstn mid (x :: x2 :: xs) ).
         assert (Hlt : ltof (list nat) (length (A:=nat)) firstHalf (x :: x2 :: xs) ).
         { admit. }
         assert (Hleft : balanced (build firstHalf lbound (mid - 1))).
         { apply IH; auto. }
         simpl. apply balancedNode.
         *** apply Hleft.
         *** admit.
         *** 
Admitted.

(* Querying a list from build should return the same answer as a regular list*)
Lemma build_correct : forall l lbound rbound i j, i >= lbound -> j <= rbound ->
    query (build l lbound rbound) i j = if 0 <? length (sublist l i j) then Some (fold_left Nat.add (sublist l i j) 0) else None.
Proof.
  intros l.
  remember (length l) as n eqn:Heqn.
  revert l Heqn.
  induction n using (well_founded_induction lt_wf).
  intros l Heqlen lbound rbound i j Hge Hle.
      destruct l as [| x xs].
      - rewrite sublist_nil. simpl. reflexivity.
      - destruct xs as [| x' xs'].
Admitted.

(* POINT UPDATE LEMMAS ==============================================================*)

(* Updating an empty segment tree returns an empty segment tree*)
Lemma Point_update_empty_tree_returns_empty_tree : forall (index number : nat),
    pointUpdate Empty index number = Empty.
Proof.
  reflexivity. 
Qed.

Lemma Point_update_single_value_returns_the_tree : forall (lbound rbound index value : nat), lbound = rbound ->
  pointUpdate (Node Empty value lbound rbound Empty) index value = Node Empty value lbound rbound Empty.
Proof.
  intros * Hbounds.
  simpl.
  rewrite (proj2 (Nat.eqb_eq _ _) Hbounds).
  destruct ((lbound <=? index) && (index <=? rbound)) eqn:Hinrange; try discriminate.
  destruct (lbound =? rbound) eqn:Hleaf.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma pointUpdate_preserves_height : forall t index value, balanced t ->
  height t = height (pointUpdate t index value).
Proof.
  induction t as [| l IHl v lo hi r IHr]; intros index value Hbal.
  - simpl. reflexivity.
  - simpl.
    remember ((lo <=? index) && (index <=? hi)) as in_range eqn:Heqin_range.
    destruct in_range eqn:Hin.
    + symmetry in Heqin_range. apply andb_true_iff in Heqin_range as [Hlo Hhi].
      apply Nat.leb_le in Hlo. apply Nat.leb_le in Hhi.
      destruct (lo =? hi) eqn:Hleaf.
      * apply Nat.eqb_eq in Hleaf.
        apply leaf_has_no_children in Hbal; [| assumption].
        destruct Hbal as [Hl_empty Hr_empty].
        subst l r. simpl. reflexivity.
      * inversion Hbal as [| ? ? ? ? ? Hbl Hbr Hhd]; subst. cbn [height].
        rewrite <- (IHl index value Hbl).
        rewrite <- (IHr index value Hbr).
        reflexivity.
    + reflexivity.
Qed.

Lemma pointUpdate_preserves_height_diff_ok : forall l r index value, balanced l -> balanced r -> height_diff_ok l r ->
  height_diff_ok (pointUpdate l index value) (pointUpdate r index value).
Proof.
  intros l r index value Hbl Hbr Hdiff.
  assert (Hl : height l = height (pointUpdate l index value)) by (apply pointUpdate_preserves_height; assumption ).
  assert (Hr : height r = height (pointUpdate r index value)) by (apply pointUpdate_preserves_height; assumption ).
  
  unfold height_diff_ok in *.
  rewrite <- Hl, <- Hr.
  assumption.
Qed.

(* Point update on a segment tree does not violate the balanced invariant*)
Lemma Point_update_does_not_violate_balanced : forall (t : Segtree) (index number : nat), balanced t ->
  balanced(pointUpdate t index number).
Proof.
  induction t as [| t1 IHl value lbound rbound t2 IHr]; intros index number Hbal.
  * constructor.
  * simpl. remember ((lbound <=? index) && (index <=? rbound)) as in_range.
  destruct in_range eqn:Hin.
  - symmetry in Heqin_range. apply andb_true_iff in Heqin_range as [Hle Hge].
    apply Nat.leb_le in Hle.
    apply Nat.leb_le in Hge.
    destruct (lbound =? rbound) eqn:Hleaf.
    + constructor. apply balancedEmpty. apply balancedEmpty. unfold height_diff_ok. lia.
    + inversion Hbal as [| ? ? ? ? ? Hbl Hbr Hheight]; subst.
      specialize (pointUpdate_preserves_height t1 index number Hbl) as Hbl'.
      specialize (pointUpdate_preserves_height t2 index number Hbr) as Hbr'.
  
      set (left_tree := pointUpdate t1 index number).
      set (right_tree := pointUpdate t2 index number).
  
      assert (height_diff_ok left_tree right_tree) as Hhd'.
      {
        unfold left_tree, right_tree.
        apply (pointUpdate_preserves_height_diff_ok t1 t2 index number); assumption.
      }
  
      constructor.
      ++ apply IHl. exact Hbl.
      ++ apply IHr. assumption.
      ++ assumption.
  - assumption.
Qed.

(* Point update returns the same size segment tree*)
Lemma Point_update_keeps_same_length_tree : forall (t : Segtree) (index value : nat), balanced t ->
    amountOfNodes t = amountOfNodes (pointUpdate t index value).
Proof.
  intros t.
  induction t as [| l IHl v lbound rbound r IHr]; intros index value Hbal.
  - simpl. reflexivity.
  - simpl in *.
    inversion Hbal as [| l' r' z y x Hbl Hbr Hhd]; subst.
    destruct ((lbound <=? index) && (index <=? rbound)) eqn:Hinrange.
    + apply andb_true_iff in Hinrange as [H1 H2].
      apply Nat.leb_le in H1. apply Nat.leb_le in H2.
      destruct (lbound =? rbound) eqn:Hleaf.
      * simpl. apply leaf_has_no_children in Hbal; [|apply Nat.eqb_eq in Hleaf; assumption].
        destruct Hbal as [Ha Hb]. rewrite Ha, Hb. simpl. reflexivity.
      * simpl.
        specialize (IHl index value Hbl).
        specialize (IHr index value Hbr).
        rewrite IHl. rewrite IHr. reflexivity.
    + simpl. reflexivity.
Qed.

(* Updating a segmentree at an index will then return the updated number from a query*)
Lemma Query_point_update_returns_updated_number_or_none : forall (t : Segtree) (index number : nat),
    query (pointUpdate t index number) index index = Some number \/ query (pointUpdate t index number) index index = None.
Proof.
Admitted.

Lemma pointUpdate_out_of_bounds : forall l r v lo hi index value, index < lo \/ hi < index ->
    pointUpdate (Node l v lo hi r) index value = Node l v lo hi r.
Proof.
  intros l r v lo hi index value Hout.
  unfold pointUpdate.
  assert (Hrange_false : (lo <=? index) && (index <=? hi) = false).
  {
    apply Bool.andb_false_iff.
    destruct Hout as [Hlt | Hgt].
    - left. apply Nat.leb_gt. exact Hlt.
    - right. apply Nat.leb_gt. exact Hgt.
  }
  rewrite Hrange_false.
  reflexivity.
Qed.

(* Updating is idempotent*)
Lemma point_update_idempotent : forall (t : Segtree) (index value : nat),
  pointUpdate t index value = pointUpdate (pointUpdate t index value) index value.
Proof.
  induction t as [| l IHl v lo hi r IHr]; intros index value.
  - simpl. reflexivity.
  - simpl.
    remember ((lo <=? index) && (index <=? hi)) as in_range eqn:Hrange.
    destruct in_range eqn:Hinrange.
    + symmetry in Hrange. apply andb_true_iff in Hrange as [Hlo_le Hhi_le].
      apply Nat.leb_le in Hlo_le.
      apply Nat.leb_le in Hhi_le.
      remember (lo =? hi) as is_leaf eqn:Hleaf.
      destruct is_leaf eqn:Hisleaf.
      * symmetry in Hleaf. apply Nat.eqb_eq in Hleaf. subst.
        now rewrite Point_update_single_value_returns_the_tree.
      * symmetry in Hleaf. apply Nat.eqb_neq in Hleaf.
        destruct (pointUpdate l index value) eqn:Hl';
        destruct (pointUpdate r index value) eqn:Hr'.
        -- simpl. assert (Hrangeb : (lo <=? index) && (index <=? hi) = true). { apply andb_true_iff. split; apply Nat.leb_le; assumption. } rewrite Hrangeb.
           apply Nat.eqb_neq in Hleaf. rewrite Hleaf. reflexivity.
        -- rewrite <- Hl', <- Hr'. simpl.
           assert (Hrangeb : (lo <=? index) && (index <=? hi) = true). { apply andb_true_iff. split; apply Nat.leb_le; assumption. } rewrite Hrangeb.
           apply Nat.eqb_neq in Hleaf. rewrite Hleaf.
           rewrite Hl', Hr'.
           rewrite Point_update_empty_tree_returns_empty_tree.
           rewrite <- Hr'.
           specialize (IHr index value). rewrite <- IHr. rewrite Hr'. reflexivity.
        -- rewrite <- Hl', <- Hr'. simpl.
           assert (Hrangeb : (lo <=? index) && (index <=? hi) = true). { apply andb_true_iff. split; apply Nat.leb_le; assumption. } rewrite Hrangeb.
           apply Nat.eqb_neq in Hleaf. rewrite Hleaf.
           rewrite Hl', Hr'.
           rewrite Point_update_empty_tree_returns_empty_tree.
           rewrite <- Hl'.
           specialize (IHl index value). rewrite <- IHl. rewrite Hl'. reflexivity.
        -- rewrite <- Hl', <- Hr'. simpl.
           assert (Hrangeb : (lo <=? index) && (index <=? hi) = true). { apply andb_true_iff. split; apply Nat.leb_le; assumption. } rewrite Hrangeb.
           apply Nat.eqb_neq in Hleaf. rewrite Hleaf.
           specialize (IHl index value). specialize (IHr index value).
           rewrite <- IHl, <- IHr. rewrite Hl', Hr'. reflexivity.
    + symmetry in Hrange. apply Bool.andb_false_iff in Hrange as [Hlo | Hhi].
      * apply Nat.leb_gt in Hlo. rewrite pointUpdate_out_of_bounds; [reflexivity|lia].
      * apply Nat.leb_gt in Hhi. rewrite pointUpdate_out_of_bounds; [reflexivity|lia].
Qed.

(* RANGE UPDATE LEMMAS ==============================================================*)

Lemma Range_update_empty_tree_returns_empty_tree : forall (lbound rbound number : nat),
  update Empty lbound rbound number = Empty.
Proof.
  intros lbound rbound number.
  induction rbound as [| rbound' IHr].
  - simpl. destruct lbound as [| lbound'].
    + reflexivity.
    + reflexivity.
  - simpl. destruct (lbound <=? S rbound') eqn:Hle.
    + apply IHr.
    + reflexivity.
Qed.

Lemma RangeUpdate_preserves_height : forall lbound rbound value, forall t, balanced t ->
    height t = height (update t lbound rbound value).
Proof.
  intros lbound rbound value.
  induction rbound as [| rbound' IHrbound]; intros t Hbal.
  - destruct lbound.
    + apply pointUpdate_preserves_height. assumption.
    + reflexivity.
  - simpl. remember (lbound <=? S rbound') as boundTrue eqn:HboundTrue.
    destruct boundTrue.
    + symmetry in HboundTrue. apply Nat.leb_le in HboundTrue.
      assert (balanced (pointUpdate t (S rbound') value)) as Hbal'. { apply Point_update_does_not_violate_balanced; assumption. }
      apply IHrbound in Hbal'.
      rewrite pointUpdate_preserves_height with (t := t) (index := S rbound') (value := value) by assumption.
      apply IHrbound.
      apply Point_update_does_not_violate_balanced. assumption.
    + reflexivity.
Qed.

(* Range update on a segment tree does not violate the balanced invariant*)
Lemma Range_update_does_not_violate_balanced : forall (t : Segtree) (lbound rbound number : nat),
    balanced(update t lbound rbound number).
Admitted.

(* Range update returns the same size segment tree*)
Lemma Range_update_keeps_same_length_tree : forall (t : Segtree) (lbound rbound number : nat), balanced t ->
  amountOfNodes t = amountOfNodes (update t lbound rbound number).
Proof.
  intros t lbound rbound number Hbal.
  generalize dependent t.
  induction rbound as [| rbound' IHr]; intros t Hbal.
  - destruct lbound as [| lbound'].
    + apply Point_update_keeps_same_length_tree; assumption.
    + simpl. reflexivity.
  - simpl.
    destruct (lbound <=? S rbound') eqn:Hcmp.
    + apply Nat.leb_le in Hcmp.
      remember (pointUpdate t (S rbound') number) as t'.
      assert (balanced t') as Hbal' by (subst t'; apply Point_update_does_not_violate_balanced; exact Hbal).
      assert (amountOfNodes t = amountOfNodes t') as Heq by (subst t'; apply Point_update_keeps_same_length_tree; exact Hbal).
      specialize (IHr t' Hbal').
      rewrite Heq.
      apply IHr.
    + reflexivity.
Qed.

(* Updating a segmentree in a range will then return the updated number from a query at all index*)
Lemma Query_range_update_returns_updated_number : forall (t : Segtree) (lbound rbound number : nat),
    query (update t lbound rbound number) lbound rbound = Some ((rbound - lbound + 1) * number).
Admitted.

Lemma range_update_idempotent : forall (t : Segtree) (lbound rbound value : nat),
  update t lbound rbound value = update (update t lbound rbound value) lbound rbound value.
Proof.
  intros t lbound rbound value.
  revert t lbound value.
  induction rbound as [| rbound' IH]; intros t lbound value.
  - destruct lbound as [| lbound'].
    + simpl. rewrite <- point_update_idempotent. reflexivity.
    + simpl. reflexivity.
  - simpl. destruct (lbound <=? S rbound') eqn:Hle.
    + apply Nat.leb_le in Hle. rewrite update_pointUpdate_cancel.
      ++ rewrite update_pointUpdate_cancel2.
        +++ apply update_pointUpdate_cancel3.
        ++++ assumption.
        +++ lia.
      ++ lia.
    + reflexivity.
Qed.

(* QUERY LEMMAS ==============================================================*)

Lemma query_entire_range : forall l, l <> [] -> 
  query (build_aux l) 0 (length l - 1) = Some (fold_left Nat.add l 0).
Proof.
  intros l Hne.
  unfold build_aux. destruct l.
  * exfalso. apply Hne. reflexivity.
  * induction l.
    ** simpl. reflexivity.
    **
Admitted.

(* Querying out of bounds will return none *)
Lemma query_malformed_index_none : forall (t : Segtree) (i j : nat), i > j ->
  query t i j = None.
Proof.
  intros t i j H.
  induction t as [| l IHl value lbound rbound r IHr].
  * simpl. reflexivity.
Admitted.

Lemma query_index_out_of_bounds : forall (t : Segtree) (l r : nat),
  r > amountOfNodes t - 1 -> query t l r = None.
Proof.
Admitted.