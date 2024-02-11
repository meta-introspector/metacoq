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

Module qLevelExprSetExtraOrdProp <: QuotationOfExtraOrdProperties LevelExprSet LevelExprSetOrdProp LevelExprSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn LevelExprSet.E LevelExprSet LevelExprSetOrdProp.P LevelExprSetExtraOrdProp.P.
    MetaCoq Run (tmMakeQuotationOfModule everything None "LevelExprSetExtraOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "LevelExprSetExtraOrdProp").
End qLevelExprSetExtraOrdProp.
