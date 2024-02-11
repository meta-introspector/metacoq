From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Quotation.ToPCUIC Require Import Coq.Init.
From MetaCoq.Utils Require Import ReflectEq.

#[export] Instance quote_reflectProp {A:Prop} {qA : quotation_of A} {quoteA : ground_quotable A} {quote_negA : ground_quotable (~A)} {b} : ground_quotable (@reflectProp A b).
Proof.
  destruct b; adjust_ground_quotable_by_econstructor_inversion ().
Defined.
