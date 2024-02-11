From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import List Arith.
Require Import MetaCoq.Template.All.
Import ListNotations MCMonadNotation.


MetaCoq Run (x <- tmFreshName ("x" ++ "y")%bs ;;
             tmDefinition x 0).

Check (eq_refl : xy = 0).


MetaCoq Run (x <- tmFreshName ("x" ++ "y")%bs ;;
             tmDefinition x 1).

Check (eq_refl : xy0 = 1).
