From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import MetaCoq.Template.Loader.
Require Import Uint63.

Definition n : Uint63.int := 42.
Import List.ListNotations.
Definition ns : list Uint63.int := [n]%list.


MetaCoq Quote Recursively Definition q_n := n.
MetaCoq Unquote Definition n' := (snd q_n).

MetaCoq Quote Recursively Definition q_ns := ns.
MetaCoq Unquote Definition ns' := (snd q_ns).

