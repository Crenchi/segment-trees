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
Require Import Coq.Arith.Div2.
Require Import Coq.Arith.Wf_nat.
Import ListNotations.
Require Coq.Program.Wf.
Require Coq.Classes.RelationClasses.
Require Coq.Numbers.Natural.Abstract.NDiv0.

Inductive SegTreeSumOfList : Segtree -> list nat -> Prop :=
  | sumEmpty  : SegTreeSumOfList Empty []
  | sumLeaf : forall value index, SegTreeSumOfList (Node Empty value index index Empty) [value]
  | sumNode : forall ltree rtree llist rlist lbound rbound,
        llist <> [] ->
        rlist <> [] ->
        SegTreeSumOfList ltree llist ->
        SegTreeSumOfList rtree rlist ->
        let value := get_value ltree rtree in
        SegTreeSumOfList (Node ltree value lbound rbound rtree) (llist ++ rlist).


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

Lemma build_height_eq_length : forall xs ys l1 l2 r1 r2,
  length xs = length ys ->
  r1-l1 = r2-l2 ->
  height (build xs l1 r1) = height (build ys l2 r2).
Proof.
Admitted.

Lemma build_height_succ_length : forall xs ys l1 l2 r1 r2,
  length xs = length ys+1 ->
  r1-l1 = r2-l2+1 ->
  height (build xs l1 r1) = height (build ys l2 r2) \/ height (build xs l1 r1) = S(height (build ys l2 r2)).
Proof.
Admitted.

Search Nat.log2.
Lemma height_le_log2_length : forall (xs : list nat) (l r : nat), balanced (build xs l r) ->
  height (build xs l r) <= Nat.log2 (length xs + 1).
Proof.
  intros. induction xs.
  - simpl. reflexivity.
  - simpl. apply TODO.
Admitted.

Lemma balanced_build_height_depends_on_length : forall (xs ys : list nat) (lx rx ly ry : nat),
  length xs = length ys ->
  balanced (build xs lx rx) ->
  balanced (build ys ly ry) ->
  height (build xs lx rx) = height (build ys ly ry).
  Proof.
    induction xs; intros ys lx rx ly ry Hlen Hbx Hby.
    - destruct ys as [| y ys'].
      * reflexivity.
      * simpl in Hlen. lia.
    - induction ys as [| ys' y] eqn:Eys.
      * inversion Hlen.
      *
  Admitted.

Lemma height_diff_when_left_has_one_more :
  forall xs lbound rbound,
    let mid := (length xs + 1) / 2 in
    let firstHalf := firstn mid xs in
    let secondHalf := skipn mid xs in
    let leftTree := build firstHalf lbound (mid - 1) in
    let rightTree := build secondHalf mid rbound in
    length firstHalf = length secondHalf + 1 ->
    balanced leftTree ->
    balanced rightTree ->
    height leftTree = height rightTree \/ height leftTree = S (height rightTree).
Proof.
  induction xs; intros.
  * right. subst firstHalf; subst secondHalf.
Admitted.

Lemma half_round_up_leq_num : forall (n : nat),
  (n+1)/2<=n.
Proof.
  apply TODO.
Qed.

Lemma length_firstn_mid : forall (xs : list nat), let mid := (length xs + 1) / 2 in
  length (firstn mid xs) = mid.
Proof.
  intros. unfold mid.
  apply firstn_length_le. apply half_round_up_leq_num.
Qed.

Lemma nat_div_split_manual : forall n : nat,
  n = n / 2 + (n - n / 2).
Proof.
  intros n.
  remember (n / 2) as a eqn:H1.
  replace n with (a + (n - a)). { simpl. lia. }
  rewrite -> Arith_prebase.le_plus_minus_r_stt. lia. rewrite H1.
  apply Nat.div_le_upper_bound. lia. lia.
Qed.

Lemma mid_split_lengths : forall (xs : list nat),
  let mid := (length xs + 1) / 2 in
  let firstHalf := firstn mid xs in
  let secondHalf := skipn mid xs in
  length firstHalf = length secondHalf \/ length firstHalf = length secondHalf + 1.
Proof.
  intros.
  unfold firstHalf, secondHalf, mid.
  remember (length xs) as n.
  assert (H: n = n / 2 + (n - n / 2)). { apply nat_div_split_manual. }
  remember (n / 2) as a.
  remember (n - a) as b.
  assert (Hcases: b = a \/ b = a + 1).
  {
    rewrite Heqb, Heqa.
    destruct (Nat.even n) eqn:E.
    - apply Nat.even_spec in E. destruct E as [k Hk].
      rewrite Hk. left. 
      rewrite Nat.mul_comm. rewrite Nat.div_mul. lia. lia.
    - assert (odd_n: Nat.odd n = true). { rewrite <- Nat.negb_even. rewrite E. reflexivity. }
      apply Nat.odd_spec in odd_n.
      destruct odd_n as [k Hk].
      rewrite Hk.
      right. remember (2*k+1) as c. subst c. (* just to see the goal simplified. *)
      rewrite Nat.add_comm.
      rewrite <- Nat.mul_comm.
      assert (Hdiv: (1 + 2 * k) / 2 = k).
      {
        rewrite Nat.add_comm. rewrite Nat.mul_comm.
        rewrite Nat.div_add_l. simpl. lia. lia.
      }
      rewrite Nat.mul_comm.
      rewrite Hdiv. lia.
  }
  rewrite Heqb in Hcases.
  rewrite Heqa in Hcases.
  destruct Hcases as [H1|H1].
  * left.
    rewrite firstn_length_le.
    - rewrite skipn_length. rewrite <- Heqn.
      admit. (* H1 implues n is even, and the goal here is true only for even numbers*)
    - rewrite <- Heqn. apply half_round_up_leq_num.
  * right.
    rewrite firstn_length_le. rewrite skipn_length. rewrite <- Heqn.
    admit. (* H1 implies n is odd, which this line holds only for odd numbers *)
    rewrite <- Heqn.
    apply half_round_up_leq_num.
Admitted.

Lemma height_diff_ok_build : forall (xs : list nat) (lbound rbound : nat),
  let mid := (length xs + 1) / 2 in
  let leftTree := build (firstn mid xs) lbound (mid - 1) in
  let rightTree := build (skipn mid xs) mid rbound in
  balanced leftTree ->
  balanced rightTree ->
  height_diff_ok leftTree rightTree.
Proof.
  intros.
  set (firstHalf := firstn mid xs).
  set (secondHalf := skipn mid xs).
  
  assert (Hlen: length firstHalf = mid). 
  { subst firstHalf. unfold mid. rewrite length_firstn_mid. reflexivity. }
  
  assert (Hlen_total: length xs = length firstHalf + length secondHalf). 
  { subst firstHalf secondHalf. rewrite firstn_length, skipn_length. lia. }
  
  assert (Hlen2: length secondHalf = length xs - mid) by lia.
  
  assert (Hdiff: length firstHalf = length secondHalf \/ length firstHalf = length secondHalf + 1) by apply mid_split_lengths.

  unfold height_diff_ok.
  destruct Hdiff as [Heq | Hsucc].
  - left. apply balanced_build_height_depends_on_length; assumption.
  - apply height_diff_when_left_has_one_more; assumption.
Qed.



(*Lemma build_preserves_height_diff : forall l lbound rbound,
  height_diff_ok (build (firstn ((length l + 1) / 2) l) lbound ((length l + 1) / 2 - 1))
                 (build (skipn ((length l + 1) / 2) l) ((length l + 1) / 2) rbound).
Proof.
  induction l as [| x xs IH]; intros.
  - simpl. left. reflexivity.
  - destruct xs as [| y ys].
    + simpl. right. left. simpl. lia.
    + set (mid := (length (x :: y :: ys) + 1) / 2).
      set (leftTree := build (firstn mid (x :: y :: ys)) lbound (mid - 1)).
      set (rightTree := build (skipn mid (x :: y :: ys)) mid rbound).

      (* By IH on smaller lists *)
      assert (Hleft := IH lbound (mid - 1)).
      assert (Hright := IH mid rbound).
Admitted. *)

(* A segment tree is by definition balanced*)
(*Lemma build_produces_balanced2 :
  forall (l : list nat),
    forall lbound rbound : nat,
      balanced (build l lbound rbound).
Proof.
  induction l using rev_ind.
  - simpl. constructor. (* Empty list case *)
  - (* l = l' ++ [x] *)
    intros lbound rbound.
    rewrite build_unf.
    destruct (l ++ [x]) as [|a [|b tl]] eqn:E.
    + simpl. constructor. (* Impossible because l ++ [x] ≠ [] *)
    + simpl. constructor. constructor. constructor. unfold height_diff_ok. left. reflexivity. (* Singleton case *)
    + (* General case *)
      set (mid := (length (l ++ [x]) + 1) / 2).
      set (firstHalf := firstn mid (l ++ [x])).
      set (secondHalf := skipn mid (l ++ [x])).
      specialize (IHl lbound (mid - 1)) as leftTree.
      specialize (IHl mid rbound) as rightTree.

Admitted.*)

Search firstn.
Search skipn.
(* A segment tree is by definition balanced*)
Lemma build_produces_balanced : forall (l : list nat) (lbound rbound : nat),
  balanced (build l lbound rbound).
Proof.
  apply (well_founded_induction (well_founded_ltof _ (@length nat)) (fun l => forall lbound rbound, balanced (build l lbound rbound))).
  intros l IH lbound rbound.
  destruct l as [|x xs].
  * rewrite (build_unf [] _ _); simpl. constructor.
  * destruct xs as [|x2 xs]; rewrite build_unf.
    + constructor.
      - constructor.
      - constructor.
      - unfold height_diff_ok. left. reflexivity.
    + set (mid := (length (x :: x2 :: xs) + 1) / 2).
         set (firstHalf := firstn mid (x :: x2 :: xs) ).
         set (secondHalf := skipn mid (x :: x2 :: xs) ).
         assert (Hlt : ltof (list nat) (length (A:=nat)) firstHalf (x :: x2 :: xs)).
         {
          unfold ltof, firstHalf, mid.
          set (len := length (x :: x2 :: xs)).
          assert (Hlen_gt_1 : len > 1) by (unfold len; simpl; lia).
          assert (Hmid_lt_len : (len + 1) / 2 < len). { apply Nat.div_lt_upper_bound; lia. }
          assert (Hlen_firstn_le_mid : length (firstn ((len + 1) / 2) (x :: x2 :: xs)) <= (len + 1) / 2) by apply firstn_le_length.
          assert (Hlen_firstn_lt_len : length (firstn ((len + 1) / 2) (x :: x2 :: xs)) < len).
          {
            eapply Nat.le_lt_trans.
            - exact Hlen_firstn_le_mid.
            - exact Hmid_lt_len.
          }
          exact Hlen_firstn_lt_len.
         }
        
         assert (Hlr : ltof (list nat) (length (A:=nat)) secondHalf (x :: x2 :: xs)).
         {
          unfold ltof, secondHalf, mid.
          set (len := length (x :: x2 :: xs)).
          assert (Hlen_gt_1 : len > 1) by (unfold len; simpl; lia).
          assert (Hmid_lt_len : (len + 1) / 2 < len) by (apply Nat.div_lt_upper_bound; lia).
          assert (Hlen_skipn_le_mid : length (skipn ((len + 1) / 2) (x :: x2 :: xs)) = len - min ((len + 1) / 2) len).
          {
            rewrite skipn_length.
            assert (Hmin : min ((len + 1) / 2) len = (len + 1) / 2).
            {
              apply Nat.min_l.
              assert (Hmid_le_len : (len + 1) / 2 <= len) by (apply Nat.lt_le_incl; exact Hmid_lt_len).
              assumption.
            }
            rewrite Hmin.
            reflexivity.
          }
          rewrite Min.min_l in Hlen_skipn_le_mid by lia.
          rewrite Hlen_skipn_le_mid.
          assert (H: len - (len + 1) / 2 < len).
          {
            apply Nat.sub_lt.
            - lia.
            - apply Nat.div_str_pos. lia.
          }
          assumption.
         }
         assert (Hleft : balanced (build firstHalf lbound (mid - 1))).
         { apply IH; auto. }
         assert (Hright : balanced (build secondHalf mid rbound)).
         { apply IH; auto. }
         simpl. apply balancedNode.
         *** apply Hleft.
         *** apply Hright.
         *** apply height_diff_ok_build. assumption. assumption.
Qed.

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

Lemma update_out_of_range_noop :  forall (t : Segtree) (lbound rbound value : nat), lbound > rbound ->
  update t lbound rbound value = t.
Admitted.


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
Lemma Range_update_does_not_violate_balanced : forall (t : Segtree) (lbound rbound number : nat), balanced t ->
  balanced (update t lbound rbound number).
Proof.
  intros t lbound rbound number Hbalanced.
  generalize dependent t.
  induction rbound as [| rbound' IHr].
  - intros t Hbalanced.
    simpl.
    destruct lbound.
    + apply Point_update_does_not_violate_balanced. assumption.
    + assumption.
  - intros t Hbalanced. simpl.
    remember (lbound <=? S rbound') as in_range eqn:Hrange.
    destruct in_range.
    -- assert (Hpt := Point_update_does_not_violate_balanced t (S rbound') number Hbalanced).
      apply IHr.
      assumption.
    -- assumption.
Qed.

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
  generalize dependent lbound.
  induction rbound as [| rbound' IHr].
  - intros lbound. simpl. destruct lbound.
    + apply point_update_idempotent.
    + reflexivity.
  - intros lbound. simpl. destruct (Nat.leb lbound (S rbound')) eqn:Heq.
    + apply TODO.
    + reflexivity.
Qed.

Lemma range_update_idempotent2 :
  forall (t : Segtree) (lbound rbound value : nat),
    update t lbound rbound value =
    update (update t lbound rbound value) lbound rbound value.
Proof.
  intros t lbound rbound value.
  remember (update t lbound rbound value) as u eqn:Hu.
  induction rbound as [| rbound' IHr].
  - simpl in Hu. destruct lbound.
  + subst. simpl. apply point_update_idempotent.
    + subst. simpl. reflexivity.

  - simpl in Hu.
    remember (lbound <=? S rbound') as in_range eqn:Heqin_range.
    destruct in_range.
    + subst. rewrite <- update_pointUpdate_cancel. rewrite -> update_pointUpdate_cancel. rewrite -> update_pointUpdate_cancel.
Admitted.

(* QUERY LEMMAS ==============================================================*)


(* Try using the new ind prop for this instead of directly proving it *)
(*Lemma query_entire_range :
  forall l, l <> [] ->
    query (build l 0 (length l - 1)) 0 (length l - 1) = Some (fold_left Nat.add l 0).
Proof.
  induction l as [| a l' IH].
  - intros H. contradiction H. reflexivity.
  - intros _. destruct l' as [| b l''].
    + (* l = [a] *)
      simpl. unfold build_aux, build. simpl.
      (* build [a] 0 0 = Node Empty a 0 0 Empty *)
      (* query (Node ...) 0 0 = Some a *)
      reflexivity.
    + (* l = a :: b :: l'' *)
      remember (length (a :: b :: l'') - 1) as tr eqn:Heqtr.
      remember (build (a :: b :: l'') 0 tr) as t eqn:Heqt.
      destruct t as [| lchild val tl tr' rchild]; try discriminate.
      assert (val = fold_left Nat.add (a :: b :: l'') 0) by admit.
      rewrite H. simpl.
  
Admitted.  *)

Lemma skipn_firstn_split :
  forall (l : list nat) lbound mid,
    lbound <= mid ->
    skipn lbound (firstn mid (firstn mid l ++ skipn mid l)) =
    firstn (mid - lbound) (skipn lbound l).
Proof.
  intros l lbound mid Hle. 
  rewrite skipn_firstn_comm by lia.
  rewrite firstn_skipn. reflexivity.
Qed.

Lemma firstn_skipn_split :
  forall (l : list nat) lbound mid rbound,
    lbound <= mid <= rbound ->
    firstn (rbound - lbound + 1) (skipn lbound l) =
    firstn (mid - lbound) (skipn lbound (firstn mid l)) ++
    firstn (rbound - mid + 1) (skipn mid l).
Proof.
  intros l lbound mid rbound Hle.
  assert (H1: skipn lbound (firstn mid l) = firstn (mid - lbound) (skipn lbound l)).
  {
    rewrite <- firstn_skipn with (n := mid) (l := l) at 1.
    rewrite skipn_firstn_split. reflexivity. lia.
  }
  rewrite H1.
  set (fullRange := rbound - lbound + 1).
  set (firstHalf := mid - lbound).
  set (secondHalf := rbound - mid + 1).
  rewrite firstn_firstn.
  rewrite Nat.min_id.
  Search firstn.
Admitted.

Lemma SegTreeSumOfList_build_aux :
  forall (l : list nat) (lbound rbound : nat),
    lbound <= rbound ->
    rbound < length l ->
    rbound - lbound + 1 = length l ->
    SegTreeSumOfList (build l lbound rbound) l.
Proof.
  intros. functional induction (build l lbound rbound) using build_ind as [| | x lbound rbound l' Hr H9 H2 H3 H4 H5 H6 H7 H8].
  * apply sumEmpty.
  * assert (rbound = 0). { simpl in H0. lia. }
    assert (lbound = 0). { lia. }
    subst. apply sumLeaf.
  * remember ((length l' + 1) / 2) as mid eqn:Heq_mid.
    assert(lbound <= mid <= rbound). { split. lia. subst. admit. }

    remember (firstn mid l') as l1 eqn:Hl1.
    remember (skipn mid l') as l2 eqn:Hl2.

    remember (build l1 lbound (mid - 1)) as left.
    remember (build l2 mid rbound) as right.

    assert (SegTreeSumOfList left l1). { apply H5. subst. lia. admit. admit. }
    assert (SegTreeSumOfList right l2). { apply H7. subst. lia. admit. admit. }

    assert (Hsplit: l' = l1 ++ l2). { subst. rewrite firstn_skipn. reflexivity. }

    rewrite Hsplit.
    apply sumNode.

Admitted.

Fixpoint sum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
  end.

  Lemma sum_app : forall l1 l2 : list nat,
  sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  intros l1 l2.
  induction l1 as [| x xs IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.


Lemma SegTreeSum_correct : forall (t : Segtree) (l : list nat),
  SegTreeSumOfList t l ->
  t <> Empty ->
  l <> [] ->
  get_value_oneTree t = Some (sum l).
Proof.
  intros. induction H.
  - congruence.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - unfold value. unfold get_value_oneTree. unfold get_value.
    destruct ltree eqn:Eltree; destruct rtree eqn:Ertree; simpl get_value.

    + assert (sum llist = 0) by (inversion H3; reflexivity).
      assert (sum rlist = 0) by (inversion H4; reflexivity).
      rewrite sum_app. rewrite H5; rewrite H6. reflexivity.

    + assert (sum llist = 0) by (inversion H3; reflexivity).
      assert (llist = []) by (inversion H3; reflexivity).
      inversion H4; subst.
      * rewrite sum_app. rewrite H5. simpl. rewrite Nat.add_0_r. reflexivity.
      * rewrite sum_app. rewrite sum_app. rewrite H5. simpl.
        assert (Some value2 = get_value_oneTree (Node s1 value2 lbound0 rbound0 s2)). { simpl. reflexivity. } 
        rewrite H6.
        rewrite IHSegTreeSumOfList2. 
        ** rewrite sum_app. reflexivity.
        ** discriminate.
        ** rewrite app_nil_l in H1. assumption.

    + assert (sum rlist = 0). {inversion H4. reflexivity. }
      inversion H4; subst.
      rewrite sum_app. rewrite H5. rewrite Nat.add_0_r. simpl in IHSegTreeSumOfList1.
      apply IHSegTreeSumOfList1.
      * discriminate.
      * assumption.
      
    + simpl in IHSegTreeSumOfList1.
      simpl in IHSegTreeSumOfList2.
      assert (Node s1 value0 lbound0 rbound0 s2 <> Empty). { discriminate. }
      assert (Node s3 value1 lbound1 rbound1 s4 <> Empty). { discriminate. }
      assert (Hv0 : Some value0 = Some (sum llist)) by apply (IHSegTreeSumOfList1 H5 H).
      assert (Hv1 : Some value1 = Some (sum rlist)) by apply (IHSegTreeSumOfList2 H6 H2).
      f_equal. inversion Hv0; inversion Hv1. rewrite sum_app. reflexivity.
Qed.


(* ------------------------------ TODO  use well founded induction*)
Search skipn.
Lemma build_preserves_sum : forall l lbound rbound,
    lbound <= rbound ->
    rbound < length l ->
    SegTreeSumOfList (build l lbound rbound) (firstn (rbound - lbound + 1) (skipn lbound l)).
Proof.
  intros l.
  induction (length l) as [|n IHn]; intros lbound rbound Hle Hlt.
  - lia.
  - remember (rbound - lbound) as d eqn:Hd.
    generalize dependent rbound.
    generalize dependent lbound.
    induction d as [|d' IH]; intros lbound rbound Hle Hlt Hd.
    + assert (lbound = rbound) by lia. subst rbound.
      simpl.
      destruct (skipn lbound l) eqn:Hskip.
      * apply TODO.
      * simpl. apply TODO.
    + assert (lbound < rbound) by lia.
      remember ((lbound + rbound) / 2) as mid eqn:Hmid.
      set (leftTree := build l lbound mid).
      set (rightTree := build l (mid + 1) rbound).
      set (ll := firstn (mid - lbound + 1) (skipn lbound l)).
      set (rl := firstn (rbound - (mid + 1) + 1) (skipn (mid + 1) l)).
      assert (SegTreeSumOfList leftTree ll) as Hleft. { admit. }
      assert (SegTreeSumOfList rightTree rl) as Hright. { admit. }
      replace (firstn (rbound - lbound + 1) (skipn lbound l)) with (ll ++ rl).
      rewrite build_unf.
      * admit.
      * subst ll rl. admit.
Admitted.

Lemma query_entire_returns_root : forall (t lt rt : Segtree) (l : list nat) (lbound rbound v : nat),
  SegTreeSumOfList t l -> t = Node lt v lbound rbound rt ->
  query t lbound rbound = Some v.
Proof.
  intros t lt rt l lbound rbound v Hsum Heq.
  subst.
  simpl.

Admitted.

Lemma segtree_sum_correct : forall t l, SegTreeSumOfList t l ->
  get_value_oneTree t = Some (fold_left Nat.add l 0).
Proof.
Admitted.

(* Querying out of bounds will return none *)
(*Lemma query_malformed_index_none : forall (t : Segtree) (lbound rbound : nat), lbound > rbound ->
  query t lbound rbound = None.
Proof.
  intros t lbound rbound H.
  induction t as [| l IHl value lbound' rbound' r IHr].
  * simpl. reflexivity.
  * simpl. rewrite IHl, IHr. destruct ((rbound' <? lbound) || (rbound <? lbound')) eqn:Hcmp.
    - reflexivity.
    - assert (Hfull_cover_false : (lbound <=? lbound') && (rbound' <=? rbound) = false).
    {
      (* We reason by contradiction: suppose it is true *)
      destruct (lbound <=? lbound') eqn:Hlb;
      destruct (rbound' <=? rbound) eqn:Hrb;
      try (apply Nat.leb_le in Hlb; apply Nat.leb_le in Hrb; lia).
      lia.
      - reflexivity.
    }
      rewrite Hrange_invalid.
      reflexivity.
Qed.*)

Lemma query_index_out_of_bounds : forall (t : Segtree) (l r : nat),
  r > amountOfNodes t - 1 -> query t l r = None.
Proof.
Admitted.