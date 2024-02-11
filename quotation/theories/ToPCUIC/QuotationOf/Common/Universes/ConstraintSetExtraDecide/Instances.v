From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MCMSets.Sig.

Module qConstraintSetExtraDecide <: MSetAVL.QuotationOfDecide ConstraintSet.E ConstraintSet ConstraintSetExtraDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSetExtraDecide").
End qConstraintSetExtraDecide.
