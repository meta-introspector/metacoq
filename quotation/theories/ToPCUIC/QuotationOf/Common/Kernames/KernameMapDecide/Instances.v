From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Utils Require Import MCFSets.Sig.

Module qKernameMapDecide <: FMapAVL.QuotationOfDecide KernameMap.E KernameMap KernameMapDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "KernameMapDecide").
End qKernameMapDecide.
