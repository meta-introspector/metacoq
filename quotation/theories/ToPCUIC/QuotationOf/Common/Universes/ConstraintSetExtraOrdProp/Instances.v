From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MCMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qConstraintSetExtraOrdProp <: QuotationOfExtraOrdProperties ConstraintSet ConstraintSetOrdProp ConstraintSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn ConstraintSet.E ConstraintSet ConstraintSetOrdProp.P ConstraintSetExtraOrdProp.P.
    MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSetExtraOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "ConstraintSetExtraOrdProp").
End qConstraintSetExtraOrdProp.
