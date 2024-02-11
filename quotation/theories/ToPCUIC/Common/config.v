From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Quotation.ToPCUIC Require Import Coq.Init.
From MetaCoq.Common Require Import config.

#[export] Instance quote_checker_flags : ground_quotable checker_flags := ltac:(destruct 1; exact _).
