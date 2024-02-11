From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.MSets Require Import MSetAVL.Sig.

Module qKernameSet <: MSetAVL.QuotationOfMake Kername KernameSet.
  MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSet").
End qKernameSet.
