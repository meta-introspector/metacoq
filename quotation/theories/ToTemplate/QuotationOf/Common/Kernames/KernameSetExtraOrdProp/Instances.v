From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate Require Import Init.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Utils Require Import MCMSets.Sig.
Import List.ListNotations.
Local Open Scope list_scope.

Module qKernameSetExtraOrdProp <: QuotationOfExtraOrdProperties KernameSet KernameSetOrdProp KernameSetExtraOrdProp.
  Module qP <: QuotationOfWExtraPropertiesOn KernameSet.E KernameSet KernameSetOrdProp.P KernameSetExtraOrdProp.P.
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetExtraOrdProp.P").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["P"]]%bs) None "KernameSetExtraOrdProp").
End qKernameSetExtraOrdProp.
