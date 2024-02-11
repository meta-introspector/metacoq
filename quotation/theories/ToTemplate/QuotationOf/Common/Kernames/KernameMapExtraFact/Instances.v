From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCFSets.Sig.

Module qKernameMapExtraFact <: QuotationOfWFactsExtra_fun KernameMap.E KernameMap KernameMapFact.F KernameMapExtraFact.
  MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMapExtraFact").
End qKernameMapExtraFact.
