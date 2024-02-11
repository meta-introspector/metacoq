From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Universes.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.MSets Require Import MSetProperties.Sig MSetDecide.Sig MSetFacts.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qLevelSetOrdProp <: QuotationOfOrdProperties LevelSet LevelSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFacts LevelSet.E LevelSetOrdProp.ME.
    MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWProperties LevelSet LevelSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOn Level LevelSet LevelSetOrdProp.P.Dec.
      MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOn Level LevelSet LevelSetOrdProp.P.FM.
      MetaCoq Run (tmMakeQuotationOfModule everything None "LevelSetOrdProp.P.FM").
    End qFM.
    MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "LevelSetOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "LevelSetOrdProp").
End qLevelSetOrdProp.
