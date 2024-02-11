From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.PCUIC Require Import PCUICAst Syntax.PCUICReflect.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig.

Module qPCUICEnvironmentDecide <: QuotationOfEnvironmentDecide PCUICTerm PCUICEnvironment PCUICEnvironmentDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICEnvironmentDecide").
End qPCUICEnvironmentDecide.
