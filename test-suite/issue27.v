From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import MetaCoq.Template.All.
Require Export List.
Open Scope bs_scope.
MetaCoq Run (tmLemma "test" (@nil nat = @nil nat)).
