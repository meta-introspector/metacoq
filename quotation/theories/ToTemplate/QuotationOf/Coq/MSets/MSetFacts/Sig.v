From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From Coq.MSets Require Import MSetFacts.
From MetaCoq.Utils Require Import MCMSets.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module Export MSets.
  Module Type QuotationOfWFactsOn (E : DecidableType) (M : WSetsOn E) (F : WFactsOnSig E M).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "F").
  End QuotationOfWFactsOn.

  Module Type QuotationOfWFacts (M : WSets) (F : WFactsSig M) := QuotationOfWFactsOn M.E M F.
End MSets.
