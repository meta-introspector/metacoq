From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import MetaCoq.Template.Loader.
Require Import Streams.

CoFixpoint ones := Cons 1 ones.

MetaCoq Quote Recursively Definition q_ones := ones.

