From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Coq.MSets Require Import MSetAVL.Sig.

Module qConstraintSet <: MSetAVL.QuotationOfMake UnivConstraint ConstraintSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSet").
End qConstraintSet.
