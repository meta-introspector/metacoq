From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Template.Ast Require Export
  TemplateTerm.Instances
  EnvHelper.Instances
  Env.Instances
  TemplateTermUtils.Instances
  TemplateLookup.Instances
.

(* TODO: maybe do something about [Include TemplateLookup.] *)
