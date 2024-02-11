From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Template Require Import Ast ReflectAst.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Import Environment.Sig.

Module qTemplateTermDecide <: QuotationOfTermDecide TemplateTerm TemplateTermDecide.
  MetaCoq Run (tmMakeQuotationOfModule everything None "TemplateTermDecide").
End qTemplateTermDecide.
