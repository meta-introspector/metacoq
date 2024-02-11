From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import MetaCoq.Template.All.
Require Export String List.

Import MCMonadNotation.

Existing Class True.
Global Existing Instance I.

MetaCoq Run (tmInferInstance None True >>= tmPrint).
MetaCoq Run (tmInferInstance None False >>= tmPrint).

Section noFixUniverse.
  Set Printing Universes.

  Universes u__opt u1 u2.
  Let set_u__opt :=  (option : Type@{u__opt} -> Type).
  Constraint u__opt < u1.

  Check ( tmInferInstance@{u1 u2}).
End noFixUniverse.
