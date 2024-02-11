From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Template Require Import Extraction.
Require Import Lens MyPlugin.

Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Set Extraction Output Directory "gen-src".

Extraction Library Lens.
Extraction Library MyPlugin.

