From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Quotation.ToPCUIC Require Import Init.
From MetaCoq.Quotation.ToPCUIC.QuotationOf.PCUIC.PCUICAst Require Export
  PCUICTerm.Instances
  PCUICEnvironmentHelper.Instances
  PCUICEnvironment.Instances
  PCUICTermUtils.Instances
  PCUICEnvTyping.Instances
  PCUICConversion.Instances
  PCUICLookup.Instances
  PCUICGlobalMaps.Instances
.

(* TODO: maybe do something about [Include PCUICLookup.] *)
