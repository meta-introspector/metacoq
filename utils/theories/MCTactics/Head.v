From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
(** find the head of the given expression *)
Ltac head expr :=
  match expr with
  | ?f _ => head f
  | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.
