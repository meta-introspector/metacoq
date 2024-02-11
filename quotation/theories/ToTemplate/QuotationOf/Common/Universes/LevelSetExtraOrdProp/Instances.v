From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelSetExtraOrdProp <: QuotationOfExtraOrdProperties LevelSet LevelSetOrdProp LevelSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn LevelSet.E LevelSet LevelSetOrdProp.P LevelSetExtraOrdProp.P.
    MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSetExtraOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "LevelSetExtraOrdProp").
End qLevelSetExtraOrdProp.
