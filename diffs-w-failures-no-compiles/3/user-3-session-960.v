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
Unset Silent.
Set Diffs "off".
Unset Silent.
Set Diffs "off".
Unset Silent.
Set Diffs "off".
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Fixpoint le_to_nat base_m2 (digits : list {x : nat | x < S (S base_m2)}) :
nat :=
  match digits with
  | nil => 0
  | digit :: digits' => proj1_sig digit + le_to_nat digits' * S (S base_m2)
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqXgKMjI"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqdn91SA"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
(assert (1 < S (S base_m2)) by lia).
(assert (base_m2 = S (S base_m2) - 2) by lia).
(generalize dependent S (S base_m2); intros base **; subst).
(assert (0 < S n) by lia).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @eq_nat_decide.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @map_filter.
Timeout 1 Check @lt_dec.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Set Silent.
(rewrite IHn).
{
(rewrite (PeanoNat.Nat.div_mod n base)  at 3 by lia).
lia.
Unset Silent.
}
(apply Nat.div_lt; lia).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQBdBtX"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqicZbpe"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlBjurg"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Silent.
Set Diffs "off".
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @PeanoNat.Nat.mod_upper_bound.
Timeout 1 Check @Qp_bounded_split.
Timeout 1 Check @Qp_bounded_split.
Timeout 1 Check @Qp_bounded_split.
Timeout 1 Check @Byte.x25.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.ascii.
Set Printing Width 78.
Search -Ascii.ascii.
Timeout 1 Check @last.
Timeout 1 Check @ascii_cmp.
Timeout 1 Check @last.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Timeout 1 Check @Ascii.byte_of_ascii.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.ascii.
Timeout 1 Check @Ascii.ascii.
Timeout 1 Check @Ascii.ascii_dec.
Timeout 1 Check @Ascii.ascii_of_N.
Timeout 1 Check @Ascii.ascii_of_N.
Timeout 1 Check @Ascii.ascii_of_byte.
Timeout 1 Check @Ascii.ascii_of_byte.
Timeout 1 Check @Ascii.ascii_of_byte.
Timeout 1 Check @Ascii.ascii_of_byte.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Print Ascii.ascii_of_byte.
Timeout 1 Check @ByteV2N.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Search -Byte.byte.
Timeout 1 Check @ByteV2N.
Timeout 1 Check @prod_eq_dec.
Timeout 1 Check @proj1.
Timeout 1 Check @proj1_sig.
Timeout 1 Check @pointwise_relation.
Timeout 1 Check @Some.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.ascii.
Timeout 1 Check @Ascii.ascii_dec.
Timeout 1 Check @Ascii.ascii_of_N.
Timeout 1 Check @Ascii.ascii_of_N.
Timeout 1 Check @Ascii.ascii_of_byte.
Timeout 1 Check @Ascii.ascii_of_byte.
Timeout 1 Check @Ascii.ascii_of_byte.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @last.
Timeout 1 Check @ascii_cmp.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.ascii.
Timeout 1 Check @Ascii.ascii.
Timeout 1 Check @Ascii.ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @false.
Set Silent.
Unset Silent.
Timeout 1 Check @false.
Definition ascii0 :=
  Ascii.Ascii false false false false false false false false.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOF8kVi"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqcc1tDj"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @last.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @prod_eq_dec.
Timeout 1 Check @proj1.
Timeout 1 Check @proj1_sig.
Timeout 1 Check @proj1_sig.
Timeout 1 Check @proj1_sig.
Timeout 1 Check @proj1_sig.
Set Printing Width 78.
Timeout 1 Check @Ascii.ascii.
Timeout 1 Check @Ascii.ascii_dec.
Timeout 1 Check @Ascii.ascii_of_N.
Timeout 1 Check @Ascii.ascii_of_nat.
Definition bounded_to_ascii (x : {x | x < 256}) : Ascii.ascii :=
  Ascii.ascii_of_nat (proj1_sig x).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqjMbEGo"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq7rBVPP"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Definition ascii_to_bounded (a : Ascii.ascii) : {x | x < 256}.
refine (exist _ (Ascii.nat_of_ascii a) _).
(apply Ascii.nat_ascii_bounded).
Unset Silent.
Defined.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq90h9tp"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqMBk2vQ"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @Byte.x25.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Unset Silent.
Set Diffs "off".
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Instance aModel : GoModel.
Proof.
Unset Silent.
refine
 {|
 byte := {x | x < 256};
 byte0 := exist _ 0 _;
 uint64_to_string := pretty.pretty_nat;
 ascii_to_byte := ascii_to_bounded;
 byte_to_ascii := bounded_to_ascii;
 uint64_to_le := nat_to_le 254;
 uint64_from_le := fun digits => Some (le_to_nat digits);
 File := Z;
 nilFile := (- 1)%Z;
 Ptr := fun _ => nat;
 nullptr := fun _ => 0 |}.
Set Silent.
(apply Nat.lt_0_succ).
Unset Silent.
Defined.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqfDpN1C"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqx50w41"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Class GoModelWf (model : GoModel) :={uint64_to_string_inj :
                                      forall x y,
                                      uint64_to_string x = uint64_to_string y ->
                                      x = y;
                                     ascii_byte_bijection1 :
                                      forall c,
                                      byte_to_ascii (ascii_to_byte c) = c;
                                     ascii_byte_bijection2 :
                                      forall b,
                                      ascii_to_byte (byte_to_ascii b) = b;
                                     uint64_le_enc :
                                      FixedLengthEncoder 8 uint64_to_le
                                        uint64_from_le;
                                     file_eqdec :> EqualDec File;
                                     file_countable :> Countable File;
                                     sigPtr_eq_dec :> EqualDec (sigT Ptr)}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQqPLC9"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqM2DVBS"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @In.
Timeout 1 Check @Byte.of_nat_via_N.
Timeout 1 Check @aModel.
Timeout 1 Check @aModel.
Timeout 1 Check @aModel.
Timeout 1 Check @GoModel.
Timeout 1 Check @GoModel.
Timeout 1 Check @GoModelWf.
Timeout 1 Check @GoModelWf.
Timeout 1 Check @aModel.
Instance aModel_wf : (GoModelWf aModel).
Proof.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @const.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @aModel.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
econstructor.
-
(simpl).
Timeout 1 Check @prod_eq_dec.
Timeout 1 Check @pretty.pretty.
Timeout 1 Check @pretty.pretty.
Timeout 1 Check @pretty.pretty.
Timeout 1 Check @pretty.pretty.
Timeout 1 Check @pretty.pretty.
Timeout 1 Check @pretty.pretty.
Timeout 1 Check @pretty.pretty_N.
Timeout 1 Check @pretty.pretty_nat.
Timeout 1 Check @pretty.pretty_nat.
Timeout 1 Check @pretty.pretty_nat.
Timeout 1 Check @pretty.pretty_nat_inj.
Timeout 1 Check @pretty.pretty_nat_inj.
Timeout 1 Check @pretty.pretty_nat_inj.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Choice.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(apply pretty.pretty_nat_inj).
-
Timeout 1 Check @sig.
(simpl).
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @ascii_to_bounded.
(unfold bounded_to_ascii, ascii_to_bounded).
Timeout 1 Check @pointwise_relation.
(intros).
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @sig.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(destruct c; simpl).
(rewrite Ascii.ascii_nat_embedding; auto).
-
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @byte.
Timeout 1 Check @byte.
Timeout 1 Check @byte_to_ascii.
Timeout 1 Check @byte_to_ascii.
Timeout 1 Check @byte_to_ascii.
Timeout 1 Check @byte_to_ascii.
Timeout 1 Check @byte_to_ascii.
Timeout 1 Check @byte_to_ascii.
Timeout 1 Check @byte_to_ascii.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @sig.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(simpl).
Timeout 1 Check @sig.
(destruct b; simpl).
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_byte.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @ascii_to_bounded.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @ascii_to_bounded.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @sig.
Set Printing Width 78.
Show.
(unfold ascii_to_bounded, bounded_to_ascii; simpl).
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_of_ascii.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @pointwise_relation.
Check Ascii.nat_ascii_embedding.
Timeout 1 Check @FinMapToList.
Timeout 1 Check @sig.
Timeout 1 Check @sig.
Timeout 1 Check @sig_eta.
Timeout 1 Check @sig_eta.
Timeout 1 Check @sig_eta.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @sig.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @FinMapToList.
Timeout 1 Check @sum.
Timeout 1 Check @subseteq.
Timeout 1 Check @subset_size.
Timeout 1 Check @subset_eq_compat.
Timeout 1 Check @subset_eq_compat.
Timeout 1 Check @subset_eq_compat.
Timeout 1 Check @subset_eq_compat.
Timeout 1 Check @subset_eq_compat.
Timeout 1 Check @subset_eq_compat.
Set Printing Width 78.
Show.
(apply subset_eq_compat).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(rewrite Ascii.nat_ascii_embedding; auto).
Print subset_eq_compat.
-
Set Silent.
admit.
Unset Silent.
-
Unset Silent.
Set Diffs "off".
Timeout 1 Check @sig.
Set Printing Width 78.
Show.
(simpl).
Timeout 1 Check @empty.
Timeout 1 Check @PeanoNat.Nat.mod_small.
typeclasses eauto.
-
Timeout 1 Check @empty.
Timeout 1 Check @PeanoNat.Nat.mod_small.
(simpl).
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @Eq.
Timeout 1 Check @EqualDec.
Timeout 1 Check @EqualDec.eqb_spec.
(unfold EqualDec).
Timeout 1 Check @bounded_to_ascii.
Timeout 1 Check @subset_eq_compat.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @sig.
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
(intros; simpl).
Timeout 1 Check @bounded_to_ascii.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @sig.
Set Printing Width 78.
Show.
(destruct x, y; simpl).
Timeout 1 Check @bounded_to_ascii.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @subset_eq_compat.
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(destruct (nat_eq_dec n n0); subst; auto).
