From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
(* Distributed under the terms of the MIT license. *)
Require Import MetaCoq.SafeCheckerPlugin.Loader.

MetaCoq SafeCheck (3 + 9).

Require Import Reals.
MetaCoq SafeCheck Rplus.
