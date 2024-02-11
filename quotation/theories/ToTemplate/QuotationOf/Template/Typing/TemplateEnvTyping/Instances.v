From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Template Require Import Ast Typing.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateEnvTyping <: QuotationOfEnvTyping TemplateTerm Env TemplateTermUtils TemplateEnvTyping.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateEnvTyping").
End qTemplateEnvTyping.
