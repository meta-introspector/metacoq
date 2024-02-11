From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.MSets Require Import MSetList.Sig.

Module qLevelExprSet <: MSetList.QuotationOfMakeWithLeibniz LevelExpr LevelExprSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "LevelExprSet").
End qLevelExprSet.
