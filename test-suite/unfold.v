From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
Import MCMonadNotation.

MetaCoq Test Quote negb.
MetaCoq Run (tmBind (tmEval (unfold (MPfile ["Datatypes"; "Init"; "Coq"], "negb")) negb) tmPrint).
