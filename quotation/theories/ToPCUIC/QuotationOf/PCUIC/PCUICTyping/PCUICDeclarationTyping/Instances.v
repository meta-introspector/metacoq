From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICDeclarationTyping <: QuotationOfDeclarationTyping PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICConversionParSpec PCUICTypingDef PCUICLookup PCUICGlobalMaps PCUICDeclarationTyping.
  MetaCoq Run (tmMakeQuotationOfModule everything None "PCUICDeclarationTyping").
End qPCUICDeclarationTyping.
