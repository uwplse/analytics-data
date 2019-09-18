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
From Coq Require Import Program.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIMcfaF"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqJDHgkK"
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
End Ptr.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Opaque Nat.modulo Nat.div.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
#[program]
Fixpoint nat_to_le base (x : nat) {measure x lt} :
list {x : nat | x < S (S base)} :=
  match x with
  | 0 => nil
  | _ =>
      let digit := x mod S (S base) in
      exist _ digit _ :: nat_to_le base (x / S (S base))
  end.
Next Obligation of nat_to_le_func.
Proof.
(apply PeanoNat.Nat.mod_upper_bound; auto).
Qed.
Next Obligation of nat_to_le_func.
Proof.
subst digit.
(apply PeanoNat.Nat.div_lt; auto; try lia).
Qed.
Next Obligation of nat_to_le_func.
Proof.
lia.
Qed.
Next Obligation of nat_to_le_func.
Proof.
(unfold MR).
(apply (wf_projected lt projT2); auto).
(apply lt_wf).
Unset Silent.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhwf9lL"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqNJr2rI"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Fixpoint le_to_nat base (digits : list {x : nat | x < S (S base)}) : nat :=
  match digits with
  | nil => 0
  | digit :: digits' => proj1_sig digit * base + le_to_nat digits'
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0fxDJv"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqP3FOAC"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Silent.
Set Diffs "off".
Timeout 1 Check @BoolTheory.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_le_pi.
Timeout 1 Check @nat_le_pi.
Timeout 1 Check @nat_le_pi.
Print FixedLengthEncoder.
Timeout 1 Check @PeanoNat.Nat.le_decidable.
Timeout 1 Check @le_to_nat.
Timeout 1 Check @le_to_nat.
Timeout 1 Check @le_to_nat.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @top.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @Z.to_N.
Timeout 1 Check @top.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @nat_to_le.
Timeout 1 Check @N.lbase.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Theorem nat_le_inverse base : forall n, le_to_nat (nat_to_le base n) = n.
Proof.
(intros).
Unset Silent.
(induction n as [n IHn] using lt_wf_ind).
Timeout 1 Check @nat_eq_dec.
(destruct n).
