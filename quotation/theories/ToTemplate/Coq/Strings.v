From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import Coq.Strings.String Coq.Strings.Ascii.
From MetaCoq.Quotation.ToTemplate Require Import Coq.Init.

#[export] Instance quote_ascii : ground_quotable Ascii.ascii := (ltac:(induction 1; exact _)).
#[export] Instance quote_string : ground_quotable string := (ltac:(induction 1; exact _)).
