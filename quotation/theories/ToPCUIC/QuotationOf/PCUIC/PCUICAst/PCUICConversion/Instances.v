From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.PCUIC Require Import PCUICAst.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICConversion <: QuotationOfConversion PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICConversion").
End qPCUICConversion.
