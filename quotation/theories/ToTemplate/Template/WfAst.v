From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Template Require Import Ast WfAst.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate Require Import (hints) Coq.Init Coq.Lists Coq.Numbers Coq.Floats.
From MetaCoq.Quotation.ToTemplate.Utils Require Import (hints) utils All_Forall MCProd MCOption.
From MetaCoq.Quotation.ToTemplate.Common Require Import (hints) config BasicAst Universes Kernames.
From MetaCoq.Quotation.ToTemplate.Template Require Import (hints) Ast AstUtils Induction UnivSubst.

#[export] Instance quote_wf {Σ t} : ground_quotable (@wf Σ t).
Proof.
  cbv [ground_quotable]; revert t.
  fix quote_wf 2; change (forall t, ground_quotable (@wf Σ t)) in quote_wf.
  intro t; destruct 1; replace_quotation_of_goal ().
Defined.

#[export] Instance quote_wf_Inv {Σ t} : ground_quotable (@wf_Inv Σ t) := ltac:(cbv [wf_Inv]; exact _).
#[export] Instance quote_wf_decl {Σ d} : ground_quotable (@wf_decl Σ d) := ltac:(cbv [wf_decl]; exact _).
#[export] Instance quote_wf_decl_pred {Σ Γ j} : ground_quotable (@wf_decl_pred Σ Γ j) := ltac:(cbv [wf_decl_pred]; exact _).
