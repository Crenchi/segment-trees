Require Import Nat.
Require Import List.
Require Import Bool.
Require Import Datatypes.

Import ListNotations.

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
Fixpoint update (t : Segtree) (lbound rbound value : nat) : Segtree.
Admitted.

Fixpoint build (array : list nat) (lbound rbound : nat) : Segtree.
(*
        match lbound =? rbound with
    | true => 
        match nth_error array lbound with
        | Some v => Node Empty v lbound rbound Empty
        | None => Empty
        end
*)
Admitted.

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
    | Empty  => 0
    | Node l _ _ _ r => 1 + max (height l) (height r)
    end
.