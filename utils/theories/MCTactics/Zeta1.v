From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Ltac zeta1 x :=
  lazymatch x with
  | let a := ?b in ?f => constr:(match b with a => f end)
  end.
