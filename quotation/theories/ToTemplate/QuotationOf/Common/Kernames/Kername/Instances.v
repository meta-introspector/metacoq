From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.Structures Require Import Orders.Sig OrdersAlt.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKername <: QuotationOfOrderedType Kername.
  Module qOT <: QuotationOfOrderedTypeOrig Kername.OT.
    MetaCoq Run (tmMakeQuotationOfModule everything None "Kername.OT").
  End qOT.
  MetaCoq Run (tmMakeQuotationOfModuleWorkAroundCoqBug17303 (all_submodules_except [["OT"]]%bs) (*None*) "Kername").
End qKername.
