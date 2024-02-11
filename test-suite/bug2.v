From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import MetaCoq.Template.Loader.

Definition I (t:Type) (x:t) : t := x.
Definition II := I (forall t:Type, t -> t) I.
MetaCoq Quote Recursively Definition qII := II.
