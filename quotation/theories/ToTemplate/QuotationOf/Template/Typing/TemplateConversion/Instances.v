From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Template Require Import Ast Typing.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateConversion <: QuotationOfConversion TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateConversion").
End qTemplateConversion.
