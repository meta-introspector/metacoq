From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
From MetaCoq.Quotation.ToPCUIC Require Import Coq.Init.
From MetaCoq.Utils Require Import bytestring.

Module String.
  #[export] Instance quote_t : ground_quotable String.t := ltac:(induction 1; exact _).
End String.
#[export] Existing Instance String.quote_t.
Notation quote_bs := String.quote_t.
Notation quote_string := String.quote_t.

#[export] Hint Unfold
  bs
  OT_byte.t
  OT_byte.eq
  OT_byte.lt
  StringOT.t
  StringOT.eq
  StringOT.lt
  : quotation.

Module Tree.
  #[export] Instance quote_t : ground_quotable Tree.t := ltac:(induction 1; exact _).
End Tree.
#[export] Existing Instance Tree.quote_t.
