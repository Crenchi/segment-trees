Require Import Nat.
Require Import List.
Import ListNotations.

(* Generic segment tree definition *)
Inductive Segtree : Type :=
    | Empty
    | Node (l : Segtree) (value lbound rbound : nat) (r : Segtree)
.

(* Core functions for a segment tree *)
Fixpoint query (t : Segtree) (lbound rbound : nat) : nat.
Admitted.

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
Admitted.