From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Coq.FSets Require Import FMapFacts.Sig.

Module qKernameMapFact.
  Module qF <: QuotationOfWFacts_fun Kername.OT KernameMap KernameMapFact.F.
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMapFact.F").
  End qF.
End qKernameMapFact.
