From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.PCUIC Require Import PCUICAst PCUICTyping.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC Require Import (hints) Coq.Init Coq.Lists Coq.Numbers Coq.Floats.
From MetaCoq.Quotation.ToPCUIC.Utils Require Import (hints) utils All_Forall (* MCProd*).
From MetaCoq.Quotation.ToPCUIC.Common Require Import (hints) config BasicAst Universes Kernames Environment EnvironmentTyping Primitive Reflect.
From MetaCoq.Quotation.ToPCUIC.Common Require Import (hints) Environment EnvironmentTyping.
From MetaCoq.Quotation.ToPCUIC.PCUIC Require Import (hints) (*PCUICAstUtils
  LiftSubst UnivSubst*) PCUICEquality (*WfAst*) PCUICAst Syntax.PCUICCases utils.PCUICPrimitive PCUICCumulativitySpec.
(*From MetaCoq.Quotation.ToPCUIC.PCUIC Require Import (hints) PCUICAstUtils
  LiftSubst UnivSubst TermEquality WfAst.*)
From MetaCoq.Quotation.ToPCUIC.Common Require Import EnvironmentTyping.
From MetaCoq.Quotation.ToPCUIC.PCUIC Require Import PCUICAst.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.PCUIC Require Import PCUICAst.Instances PCUICTyping.Instances.

#[export] Instance quote_FixCoFix : ground_quotable FixCoFix := ltac:(destruct 1; exact _).

#[export] Instance quote_case_side_conditions {cf wf_local_fun typing Σ Γ ci p ps mdecl idecl indices predctx} {qwf_local_fun : quotation_of wf_local_fun} {qtyping : quotation_of typing} {quote_wf_local_fun : forall Γ, ground_quotable (@wf_local_fun Σ Γ)} {quote_typing : forall i t, ground_quotable (typing Σ Γ i t)} : ground_quotable (@case_side_conditions cf wf_local_fun typing Σ Γ ci p ps mdecl idecl indices predctx) := ltac:(destruct 1; exact _).

#[export] Instance quote_case_branch_typing {cf wf_local_fun typing Σ Γ ci p ps mdecl idecl ptm brs} {qwf_local_fun : quotation_of wf_local_fun} {qtyping : quotation_of typing} {quote_wf_local_fun : forall Γ, ground_quotable (@wf_local_fun Σ Γ)} {quote_typing : forall Γ i t, ground_quotable (typing Σ Γ i t)} : ground_quotable (@case_branch_typing cf wf_local_fun typing Σ Γ ci p ps mdecl idecl ptm brs)
  := ltac:(destruct 1; exact _).

#[export] Instance quote_primitive_typing_hyps {cf typing Σ Γ p} {qtyping : quotation_of typing} {quote_typing : forall x y, ground_quotable (typing Σ Γ x y)} : ground_quotable (@primitive_typing_hyps cf typing Σ Γ p)
  := ltac:(destruct 1; exact _).

(* So long as pcuic does axiomatic guard checking, we can't do better than axiomatizing it here *)
#[export] Instance quote_guard_checking {k Σ Γ t} : ground_quotable (@guard guard_checking k Σ Γ t).
Proof.
  tryif unfold_quotation_of ()
  then fail "It seems that guard_checking is no longer an axiom, please remove the Axiom of this theorem and properly define quotability"
  else idtac.
Abort.
Axiom quote_guard_checking : forall {k Σ Γ t}, ground_quotable (@guard guard_checking k Σ Γ t).
#[export] Existing Instance quote_guard_checking.

#[export] Hint Unfold
  fix_guard
  cofix_guard
  : quotation.
#[export] Typeclasses Transparent
  fix_guard
  cofix_guard
.

Section quote_typing.
  Context {cf : config.checker_flags} {Σ : global_env_ext}.

  (*#[local] Hint Extern 1 => progress cbv zeta : typeclass_instances.*)

  Fixpoint quote_typing' {Γ t T} (pf : @typing cf Σ Γ t T) {struct pf} : quotation_of pf.
  Proof.
    change (forall Γ t T, ground_quotable (@typing cf Σ Γ t T)) in quote_typing'.
    destruct pf.
    all: [ > try replace_quotation_of_goal () .. ].
  Defined.
End quote_typing.
#[export] Instance quote_typing {cf Σ Γ t T} : ground_quotable (@typing cf Σ Γ t T) := quote_typing'.

Definition quote_wf_local {cf : config.checker_flags} {Σ Γ} : ground_quotable (wf_local Σ Γ) := _.

#[export] Instance quote_has_nparams {npars ty} : ground_quotable (@has_nparams npars ty) := ltac:(cbv [has_nparams]; exact _).

Module QuotePCUICTypingDef <: QuoteTyping PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping
                                PCUICConversion PCUICConversionParSpec PCUICTypingDef.
  #[export] Instance quote_typing {cf Σ Γ t T} : ground_quotable (@PCUICTyping.typing cf Σ Γ t T) := quote_typing.
End QuotePCUICTypingDef.
Export (hints) QuotePCUICTypingDef.

Module QuotePCUICDeclarationTyping
  := QuoteDeclarationTyping
       PCUICTerm
       PCUICEnvironment
       PCUICTermUtils
       PCUICEnvTyping
       PCUICConversion
       PCUICConversionParSpec
       PCUICTypingDef
       PCUICLookup
       PCUICGlobalMaps
       PCUICDeclarationTyping
       qPCUICTerm
       qPCUICEnvironment
       qPCUICEnvTyping
       qPCUICConversion
       qPCUICTypingDef
       qPCUICGlobalMaps
       QuotePCUICTerm
       QuotePCUICEnvironment
       QuotePCUICEnvTyping
       QuotePCUICConversion
       QuotePCUICTypingDef
       QuotePCUICLookup
       QuotePCUICGlobalMaps.
Export (hints) QuotePCUICDeclarationTyping.

#[export] Instance quote_wf {cf Σ} : ground_quotable (@wf cf Σ) := ltac:(cbv [wf]; exact _).
#[export] Instance quote_wf_ext {cf Σ} : ground_quotable (@wf_ext cf Σ) := ltac:(cbv [wf_ext]; exact _).
