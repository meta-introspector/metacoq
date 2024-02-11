From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import MetaCoq.Template.Loader.
Local Open Scope string_scope.
MetaCoq Quote Recursively Definition p_NN := nat.