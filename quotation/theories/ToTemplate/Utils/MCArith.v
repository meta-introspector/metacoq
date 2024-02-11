From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Quotation.ToTemplate Require Import Coq.Init.
From MetaCoq.Utils Require Import MCArith.

#[export] Instance quote_BoolSpecSet {P Q : Prop} {b} {qP : quotation_of P} {qQ : quotation_of Q} {quoteP : ground_quotable P} {quoteQ : ground_quotable Q} : ground_quotable (BoolSpecSet P Q b) := ltac:(destruct 1; exact _).
