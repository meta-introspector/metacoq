From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICEnvTyping <: QuotationOfEnvTyping PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICEnvTyping").
End qPCUICEnvTyping.
