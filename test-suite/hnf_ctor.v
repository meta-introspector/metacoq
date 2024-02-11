From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import Coq.Strings.String.
Require Import MetaCoq.Template.Loader.

Inductive U : Type :=
| TT : id U.

MetaCoq Quote Recursively Definition qU := U.
