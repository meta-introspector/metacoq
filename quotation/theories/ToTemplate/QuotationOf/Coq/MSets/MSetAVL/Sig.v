From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From Coq.Structures Require Import Orders.
From Coq.MSets Require Import MSetAVL.
From MetaCoq.Utils Require Import MCMSets.
From MetaCoq.Quotation.ToTemplate Require Import Init.

Module MSetAVL.
  Module Type QuotationOfMake (T : OrderedType) (M : MSetAVL.MakeSig T).
    MetaCoq Run (tmDeclareQuotationOfModule everything (Some export) "M").
  End QuotationOfMake.
End MSetAVL.
