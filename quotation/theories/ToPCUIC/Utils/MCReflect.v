From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Quotation.ToPCUIC Require Import Coq.Init.
From MetaCoq.Utils Require Import MCReflect.

#[export] Instance quote_reflectT {A} {qA : quotation_of A} {quoteA : ground_quotable A} {quote_negA : ground_quotable (A -> False)} {b} : ground_quotable (@reflectT A b) := ltac:(destruct 1; exact _).
