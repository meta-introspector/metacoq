From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import MetaCoq.Template.Loader.

MetaCoq Quote Recursively Definition aterm := Ast.term.
(*Time MetaCoq Quote Recursively Definition aterm' := aterm.*)
