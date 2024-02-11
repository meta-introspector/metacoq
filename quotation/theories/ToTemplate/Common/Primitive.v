From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Quotation.ToTemplate Require Import Coq.Init.
From MetaCoq.Common Require Import Primitive.

#[export] Instance quote_prim_tag : ground_quotable prim_tag := ltac:(destruct 1; exact _).
