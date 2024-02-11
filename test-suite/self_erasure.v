From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Erasure Require Import Loader Erasure.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
Set MetaCoq Timing.
MetaCoq Fast Erase @erase_and_print_template_program.
MetaCoq Fast Erase @typecheck_program.
