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
    | Node (l : Segtree) (value lbound rbound : nat) (r : Segtree)
.

(* Core functions for a segment tree *)
(* These functions pertain to summation *)
Fixpoint query (t : Segtree) (tl tr : nat) : option nat :=
    match t with
    | Empty => None
    | Node l value lbound rbound r =>
    (* 3 cases, case 1: no overlap *)
    if (tl <? lbound) || (rbound <? tr) then None
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

Definition balanced (t : Segtree) : bool := (height t - fastestRoute t) <? 2.

Compute segtree_example_12.
Compute segtree_example_123.
Compute (height segtree_example_123).
Compute (fastestRoute segtree_example_123).
Compute segtree_example_123.
Compute (pointUpdate segtree_example_123 1 4).
Compute segtree_example_123.
Compute (update segtree_example_123 0 1 0).
Compute (balanced segtree_example_123).

Compute (build [1; 2; 3] 0 2).
Compute segtree_example_123.