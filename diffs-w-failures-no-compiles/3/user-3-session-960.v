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
Timeout 1 Check @N.lbase.
Timeout 1 Check @FinMapToList.
Timeout 1 Check @applicative_ap.
Timeout 1 Check @applicative_ap.
Timeout 1 Check @N.lbase.
Timeout 1 Check @N.lbase.
Timeout 1 Check @N.lbase.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @mod_S_lt.
Timeout 1 Check @mod_S_lt.
Timeout 1 Check @mod_S_lt.
Check mod_S_lt.
Timeout 1 Check @N.lbase.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @N.lbase.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @FinMapToList.
Timeout 1 Check @applicative_ap.
Timeout 1 Check @applicative_ap.
Timeout 1 Check @apply.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @mod_S_lt.
Timeout 1 Check @mod_S_lt.
Timeout 1 Check @mod_S_lt.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @mod_S_lt.
Timeout 1 Check @mod_S_lt.
Timeout 1 Check @mod_S_lt.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @N.lbase.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @N.lbase.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Function
 nat_to_le base_m2 (x : nat) {wf lt x} : list {x : nat | x < S (S base_m2)}
 :=
   match x with
   | 0 => nil
   | _ =>
       let base := S (S base_m2) in
       let digit := x `mod` base in
       exist (fun x => x < base) digit _ :: nat_to_le base_m2 (x / base)
   end.
Proof.
-
(intros; subst).
Unset Silent.
(apply PeanoNat.Nat.div_lt; auto; try lia).
-
(apply lt_wf).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq1B53nb"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq1F4h2B"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq1tRDll"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @BoolTheory.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le_F.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @Choice.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Fixpoint le_to_nat base (digits : list {x : nat | x < S (S base)}) : nat :=
  match digits with
  | nil => 0
  | digit :: digits' => proj1_sig digit * base + le_to_nat digits'
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq8Bga3l"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqq7lPKp"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Theorem nat_le_inverse base_m2 :
  forall n, le_to_nat (nat_to_le base_m2 n) = n.
Proof.
(intros).
(induction n as [n IHn] using lt_wf_ind).
(destruct n; rewrite nat_to_le_equation; simpl).
-
auto.
-
Unset Silent.
Set Diffs "off".
Timeout 1 Check @last.
Timeout 1 Check @byte.
Timeout 1 Check @sig.
Timeout 1 Check @Tauto.A.
Set Printing Width 78.
Show.
Timeout 1 Check @split.
(assert (base_m2 = S (S base_m2) - 2) by lia).
Unset Silent.
Set Diffs "off".
Timeout 1 Check @pointwise_relation.
Timeout 1 Check @sum.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(generalize dependent S (S base_m2); intros base **; subst).
