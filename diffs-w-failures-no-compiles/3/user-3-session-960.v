Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWfrXOb"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 51.
Set Silent.
From Coq Require Import ProofIrrelevance.
From Coq Require Export String.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Print LoadPath.
Set Printing Width 78.
From Coq Require Import FunInd Recdef.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0iIh4K"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqPaL2mC"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
From Classes Require Import EqualDec.
From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import decidable countable.
From stdpp Require gmap.
From stdpp Require Import fin_maps.
Set Implicit Arguments.
Instance eqdecision  `{dec : EqualDec A}: (EqDecision A) := dec.
Definition uint64 := nat.
Definition compare_to x y (c : comparison) :
  {match c with
   | Lt => x < y
   | Gt => y < x
   | Eq => x = y
   end} + {match c with
           | Lt => x >= y
           | Gt => y >= x
           | Eq => x <> y
           end}.
(destruct c).
-
(apply Nat.eq_dec).
-
(destruct (lt_dec x y); auto; right; abstract omega).
-
(destruct (lt_dec y x); auto; right; abstract omega).
Defined.
Record FixedLengthEncoder bytes intTy byteTy (enc : intTy -> list byteTy)
(dec : list byteTy -> option intTy) :={encode_length_ok :
                                        forall x, length (enc x) = bytes;
                                       encode_decode_ok :
                                        forall x, dec (enc x) = Some x}.
Module Ptr.
Inductive ty : Type :=
  | Heap : forall T : Type, _
  | Map : forall V : Type, _
  | Lock : _.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @N.lbase.
Timeout 1 Check @N.lbase.
Timeout 1 Check @N.lbase.
Timeout 1 Check @N.lbase.
Timeout 1 Check @BoolTheory.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @Zmod_le.
Timeout 1 Check @N.mod_lt.
Timeout 1 Check @forallb.
Timeout 1 Check @plus_Snm_nSm.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Theorem mod_S_lt n m : n `mod` S m < S m.
Set Silent.
Proof.
(apply PeanoNat.Nat.mod_upper_bound; auto).
Qed.
Unset Silent.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @N.lbase.
Timeout 1 Check @N.lbase.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @N.lbase.
Set Printing Width 78.
Timeout 1 Check @ex.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @mod_S_lt.
Timeout 1 Check @mod_S_lt.
Timeout 1 Check @mod_S_lt.
Timeout 1 Check @N.div.
Timeout 1 Check @Ascii.N_of_digits.
Timeout 1 Check @N.lbase.
Timeout 1 Check @N.lbase.
Timeout 1 Check @N.lbase.
Function
 nat_to_le base_m2 (x : nat) {wf lt x} : list {x : nat | x < S (S base_m2)}
 :=
   match x with
   | 0 => nil
   | _ =>
       let base := base_m2 in
       let digit := x `mod` S (S base_m2) in
       exist (fun x => x < base) digit _ :: nat_to_le base (x / base)
   end.
