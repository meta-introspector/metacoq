From Coq Require Import Strings.String.
From Template Require Import
     Ast AstUtils TemplateMonad.Common.

Set Universe Polymorphism.
Set Universe Minimization ToSet.
Set Primitive Projections.
Set Printing Universes.

(** ** The Extractable Template Monad

  A monad for programming with Template Coq structures. Use [Run
  TemplateProgram] on a monad action to produce its side-effects.

 *)


Cumulative Inductive TM@{t u} : Type@{t} -> Type :=
(* Monadic operations *)
| tmReturn {A:Type@{t}}
  : A -> TM A
| tmBind {A B : Type@{t}}
  : TM A -> (A -> TM B) -> TM B

(* General commands *)
| tmPrint : Ast.term -> TM unit
| tmFail : forall {A:Type@{t}}, string -> TM A
| tmEval (red : reductionStrategy) (tm : Ast.term)
  : TM Ast.term

| tmResolve : string -> TM kername

(* Return the defined constant *)
| tmDefinitionRed (nm : ident) (red : option reductionStrategy)
                  (type : option Ast.term) (term : Ast.term)
  : TM kername
| tmAxiomRed (nm : ident) (red : option reductionStrategy)
             (type : Ast.term)
  : TM kername
| tmLemmaRed (nm : ident) (red : option reductionStrategy)
             (type : option Ast.term) (term : Ast.term)
  : TM kername

(* Guaranteed to not cause "... already declared" error *)
| tmFreshName : ident -> TM ident

| tmAbout : ident -> TM (option global_reference)
| tmCurrentModPath : unit -> TM string

(* Quote the body of a definition or inductive. *)
| tmQuoteInductive (nm : kername)
  : TM mutual_inductive_body
| tmQuoteUniverses : TM uGraph.t
| tmQuoteConstant (nm : kername) (bypass_opacity : bool)
  : TM constant_entry

(* unquote before making the definition *)
(* FIXME take an optional universe context as well *)
| tmMkInductive : mutual_inductive_entry -> TM unit

(* Typeclass registration and querying for an instance *)
| tmExistingInstance : ident -> TM unit
| tmInferInstance (red : option reductionStrategy)
                  (type : Ast.term)
  : TM (option Ast.term)
.


Definition TypeInstance@{t u r}: Common.TMInstance@{t u r} :=
  {| Common.TemplateMonad := TM@{t u}
   ; Common.tmReturn:=@tmReturn
   ; Common.tmBind:=@tmBind
   ; Common.tmFail:=@tmFail
   ; Common.tmFreshName:=@tmFreshName
   ; Common.tmAbout:=@tmAbout
   ; Common.tmCurrentModPath:=@tmCurrentModPath
   ; Common.tmQuoteInductive:=@tmQuoteInductive
   ; Common.tmQuoteUniverses:=@tmQuoteUniverses
   ; Common.tmQuoteConstant:=@tmQuoteConstant
   ; Common.tmMkInductive:=@tmMkInductive
   ; Common.tmExistingInstance:=@tmExistingInstance
   |}.
(* Monadic operations *)

Definition print_nf (msg : Ast.term) : TM unit
  := tmBind (tmEval all msg) tmPrint.

(*
Definition fail_nf {A} (msg : string) : TM A
  := tmBind (tmEval all msg) tmFail.
*)

Definition tmMkInductive' (mind : mutual_inductive_body) : TM unit
  := tmMkInductive (mind_body_to_entry mind).

Definition tmLemma (i : ident) := tmLemmaRed i (Some hnf).
Definition tmAxiom (i : ident) := tmAxiomRed i (Some hnf).
Definition tmDefinition (i : ident) :=
  @tmDefinitionRed i (Some hnf).