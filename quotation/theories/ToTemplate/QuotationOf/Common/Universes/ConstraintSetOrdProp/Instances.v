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

Module qConstraintSetOrdProp <: QuotationOfOrdProperties ConstraintSet ConstraintSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFacts ConstraintSet.E ConstraintSetOrdProp.ME.
    MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWProperties ConstraintSet ConstraintSetOrdProp.P.
    Module qDec <: QuotationOfWDecideOn UnivConstraint ConstraintSet ConstraintSetOrdProp.P.Dec.
      MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSetOrdProp.P.Dec").
    End qDec.
    Module qFM <: QuotationOfWFactsOn UnivConstraint ConstraintSet ConstraintSetOrdProp.P.FM.
      MetaCoq Run (tmMakeQuotationOfModule everything None "ConstraintSetOrdProp.P.FM").
    End qFM.
    MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["Dec"]; ["FM"]]%bs) None "ConstraintSetOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "ConstraintSetOrdProp").
End qConstraintSetOrdProp.
