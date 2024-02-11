From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import MetaCoq.Template.Loader.

Axiom a_nat : nat.

MetaCoq Quote Recursively Definition qn := (a_nat + 1).

Polymorphic Axiom poly : forall x : Type, x.

MetaCoq Quote Recursively Definition qpoly := poly.

