From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Template Require Import Loader All.
Require  Import ssreflect.
(* above two lines can be run in either order *)

Parameter a : nat.
Axiom aa : a = a + a.

Goal a + a + a + a+ a+ a + a = a.
  now rewrite -!aa.
Qed.
