From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Export MetaCoq.Utils.MCTactics.UniquePose.

Ltac specialize_all_ways :=
  repeat match goal with
         | [ H : ?A, H' : forall a : ?A, _ |- _ ]
           => unique pose proof (H' H)
         end.
