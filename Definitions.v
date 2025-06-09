Require Import Nat.
Require Import List.
Require Import Bool.
Require Import Datatypes.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Require Import Arith Psatz.
From Coq Require Import Recdef List.
Import ListNotations.
Require Coq.Program.Wf.

Lemma TODO : forall {A:Prop}, A.
Admitted.


(* Generic segment tree definition *)
Inductive Segtree : Type :=
    | Empty
    | Node (l : Segtree) (value lbound rbound : nat) (r : Segtree).

(* Core functions for a segment tree *)
(* These functions pertain to summation *)
Fixpoint query (t : Segtree) (tl tr : nat) : option nat :=
    match t with
    | Empty => None
    | Node l value lbound rbound r =>
    (* 3 cases, case 1: no overlap *)
    if (rbound <? tl) || (tr <? lbound) then None
    (* Case 2: full overlap *)
    else if (tl <=? lbound) && (rbound <=? tr) then Some value
    (* Case 3: Partial overlap — combine results *)
    else
      match (query l tl tr, query r tl tr) with
      | (Some v1, Some v2) => Some (v1 + v2)
      | (Some v, None) | (None, Some v) => Some v
      | (None, None) => None
      end
end.


(*
Following two functions define different types of segment tress 
    1. What value is held at a node
    2. How to build a segment tree
This can further be abstracted by defining a merge function, and
have a generic build function that uses that. Same with update. 
*)

Fixpoint pointUpdate (t : Segtree) (index value : nat) : Segtree :=
  match t with
  | Empty => Empty (* [] *)
  | Node l node_value lbound rbound r =>
      if (lbound <=? index) && (index <=? rbound) then
        if (lbound =? rbound) then
          Node Empty value lbound rbound Empty
        else
          let mid := (lbound + rbound) / 2 in
          let left_tree := pointUpdate l index value in
          let right_tree := pointUpdate r index value in
          let new_value :=
            match left_tree, right_tree with
            | Node _ lv _ _ _, Node _ rv _ _ _ => lv + rv
            | Node _ lv _ _ _, Empty => lv
            | Empty, Node _ rv _ _ _ => rv
            | Empty, Empty => 0
            end
          in
          Node left_tree new_value lbound rbound right_tree
      else
        t
  end.

Fixpoint update (t : Segtree) (lbound rbound value : nat) : Segtree :=
  match rbound with
  | 0 =>
      match lbound with
      | 0 => pointUpdate t 0 value
      | _ => t
      end
  | S rbound' =>
      match lbound <=? rbound with
      | true  => let t' := pointUpdate t rbound value in update t' lbound rbound' value
      | false => t
      end
  end.

Program Fixpoint build (l : list nat) (lbound rbound : nat) {measure (length l)} : Segtree :=
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
Next Obligation.
  assert (1 <= 1) as Hle11 by lia.
  pose proof Nat.divmod_spec (length l + 1) 1 0 1 Hle11 as H1.
  simpl in H1.
  destruct (Nat.divmod (length l + 1) 1 0 1) as [n rem] eqn:Hdiv.
  destruct rem as [|[|rem']]; simpl in *.
  - assert (length l = 2 * n) by lia.
    rewrite firstn_length.
    rewrite Nat.min_l.
    + rewrite H2.
      assert (length l >= 2) by (destruct l as [|a [|b tl]]; simpl in *; try contradiction; lia; lia).
      lia.
    + lia.
  - assert (length l = 2 * n - 1) by lia.
    rewrite firstn_length.
    rewrite Nat.min_l.
    + rewrite H2.
      assert (length l >= 2). 
      {
        destruct l as [|a [|b tl]]; simpl in *; try contradiction.
        exfalso.  apply (H a). reflexivity. lia.
      }
      lia.
    + lia.
  - lia.
Qed.
Next Obligation.
assert (1 <= 1) as Hle11 by lia.
  pose proof Nat.divmod_spec (length l + 1) 1 0 1 Hle11 as H1.
  simpl in H1.
  destruct (Nat.divmod (length l + 1) 1 0 1) as [n rem] eqn:Hdiv.
  destruct rem as [|[|rem']]; simpl in *.
  - assert (length l = 2 * n) by lia.
    rewrite skipn_length.
    assert (length l >= 1).  
      {
        destruct l. contradiction H0. reflexivity. simpl. lia.
      }
    assert (n > 0) by (rewrite H2 in *; lia).
    rewrite H2. lia.
  - assert (length l = 2 * n - 1) by lia.
    rewrite skipn_length.
    rewrite H2. lia.
  - lia.
Qed.
Next Obligation.
  split.
  + discriminate.
  + discriminate.
Qed.

  
Lemma div_lt_self : forall n, n >= 2 -> (n + 1) / 2 < n.
Proof.
  intros n H.
  destruct n as [| [| n']].
  * simpl. lia.
  * simpl. lia.
  * inversion H.
    - simpl. lia.
    - rewrite <- H0. rewrite <- H0 in H1. rewrite <- H0 in H. apply Nat.div_lt_upper_bound with (b := 2). lia. lia.
Qed.

Function build2 (l : list nat) (lbound rbound : nat) {measure length l} : Segtree :=
  match l with
  | [] => Empty
  | [x] => Node Empty x lbound rbound Empty 
  | _ =>
    let mid : nat := Nat.div (length l + 1) 2 in
    let firstHalf := firstn mid l in
    let secondHalf := skipn mid l in
    let leftTree := build2 firstHalf lbound (mid-1) in
    let rightTree := build2 secondHalf mid rbound in
    let value :=
      match leftTree, rightTree with
      | Node _ lv _ _ _, Node _ rv _ _ _ => lv + rv
      | Node _ lv _ _ _, Empty => lv
      | Empty, Node _ rv _ _ _ => rv
      | Empty, Empty => 0
      end
    in Node leftTree value lbound rbound rightTree
  end.
Proof.
  * intros. rewrite skipn_length.
    assert (Hlen_pos : length (x :: n :: l1) >= 2). { simpl. lia. }
    replace (length (x :: n :: l1)) with (S (S (length l1))) by reflexivity.
    assert (H : (S (S (length l1)) + 1) / 2 >= 1). {destruct l1. simpl. lia. apply Nat.div_le_lower_bound. auto. simpl. lia. }
    lia.
  * intros. rewrite skipn_length.
    assert (Hlen_pos : length (x :: n :: l1) >= 2). { simpl. lia. }
    replace (length (x :: n :: l1)) with (S (S (length l1))) by reflexivity.
    assert (H : (S (S (length l1)) + 1) / 2 >= 1). {destruct l1. simpl. lia. apply Nat.div_le_lower_bound. auto. simpl. lia. }
    lia.
  * intros. rewrite firstn_length.
    destruct (Nat.min ((length (x :: n :: l1) + 1) / 2) (length (x :: n :: l1))) eqn:Hmin.
    - simpl. lia.
    - assert (Hlen : length (x :: n :: l1) >= 2) by (simpl; lia).
      remember (length (x :: n :: l1)) as n2 eqn:Hlen'.
      assert (Hdiv : (n2 + 1) / 2 < n2).
      {
        destruct n2 as [| [| n']].
          + simpl. discriminate.
          + simpl. discriminate.
          + apply div_lt_self. auto.
      }
      rewrite <- Hmin. lia.
Defined.


Definition build_aux (l : list nat) : Segtree := build l 0 (length l - 1).

Lemma div_upper_bound : forall a b,
  b > 0 -> a / b <= a.
Proof.
  intros. apply Nat.div_le_upper_bound. lia. induction b.
  * lia.
  * lia.
Qed.

(* Example usage: Compute the segment tree for an array *)
Definition segtree_example_12 : Segtree :=
  Node
    (Node Empty 1 0 0 Empty)
    3
    0
    1
    (Node Empty 2 1 1 Empty).

Definition segtree_example_123 : Segtree :=
    Node
      (Node
        (Node Empty 1 0 0 Empty)
        3
        0
        1
        (Node Empty 2 1 1 Empty))
      6
      0
      2
      (Node Empty 3 2 2 Empty).

(* Using Compute to evaluate the segment tree construction *)

(* Supplementary functions to a segment tree *)

Definition emptyTree : Segtree := Empty.

Definition isEmpty (t : Segtree) : bool :=
    match t with
    | Empty => true
    | _     => false
    end
.

Fixpoint height (t : Segtree) : nat :=
    match t with
    | Empty           => 0
    | Node l _ _ _ r  => S (Nat.max (height l) (height r))
    end
.

Fixpoint fastestRoute (t : Segtree) : nat :=
    match t with
    | Empty           => 0
    | Node l _ _ _ r  => 1 + min (fastestRoute l) (fastestRoute r)
    end
.

Fixpoint amountOfNodes (t : Segtree) : nat :=
    match t with
    | Empty           => 0
    | Node l _ _ _ r  => 1 + (amountOfNodes l) + (amountOfNodes r)
    end
.

Definition height_diff_ok l r :=
  height l = height r \/
  height l = S (height r) \/
  height r = S (height l).

Inductive balanced : Segtree -> Prop :=
  | balancedEmpty : balanced Empty
  | balancedNode : forall l r v lbound rbound,
      balanced l ->
      balanced r ->
      height_diff_ok l r ->
      balanced (Node l v lbound rbound r).

Definition balancedFunc (t : Segtree) : Prop := height t - fastestRoute t <= 1.

Definition sublist (l : list nat) (i j : nat) : list nat :=
  firstn (j - i + 1) (skipn i l).

Compute segtree_example_12.
Compute segtree_example_123.
Compute (height segtree_example_123).
Compute (fastestRoute segtree_example_123).
Compute segtree_example_123.
Compute (pointUpdate segtree_example_123 1 4).
Compute segtree_example_123.
Compute (update segtree_example_123 0 1 0).
Compute (balanced segtree_example_123).
Compute query segtree_example_123 1 2.

Compute query (build [1; 2; 3] 0 2) 2 2.
Compute build_aux [1; 2; 3].
Compute segtree_example_123.