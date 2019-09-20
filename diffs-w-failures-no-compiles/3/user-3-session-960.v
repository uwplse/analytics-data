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
Unset Silent.
Set Diffs "off".
Timeout 1 Check @empty.
Timeout 1 Check @max_type.
Timeout 1 Check @max_type.
Timeout 1 Check @Eq.
Timeout 1 Check @EqualDec.
Timeout 1 Check @EqualDec.
Timeout 1 Check @EqualDec.
Timeout 1 Check @EqualDec.
Timeout 1 Check @EqualDec.
Timeout 1 Check @Decision.
Timeout 1 Check @DeclConstant.DO.
Timeout 1 Check @In.
Timeout 1 Check @empty.
Set Printing Width 78.
Set Silent.
Module Ptr.
Inductive ty : Type :=
  | Heap : forall T : Type, _
  | Map : forall V : Type, _
  | Lock : _.
Unset Silent.
#[global]Declare Instance type_dec : (EqualDec ty).
End Ptr.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
Class GoModel : Type :={byte : Type;
                        byte0 : byte;
                        uint64_to_string : uint64 -> string;
                        ascii_to_byte : Ascii.ascii -> byte;
                        byte_to_ascii : byte -> Ascii.ascii;
                        uint64_to_le : uint64 -> list byte;
                        uint64_from_le : list byte -> option uint64;
                        File : Type;
                        nilFile : File;
                        Ptr : Ptr.ty -> Type;
                        nullptr : forall ty, Ptr ty}.
Opaque Nat.modulo Nat.div.
#[local]Obligation Tactic := (intros; simpl; subst).
Theorem mod_S_lt n m : n `mod` S m < S m.
Proof.
(apply PeanoNat.Nat.mod_upper_bound; auto).
Qed.
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
(apply PeanoNat.Nat.div_lt; auto; try lia).
-
(apply lt_wf).
Qed.
Unset Silent.
Fixpoint le_to_nat base_m2 (digits : list {x : nat | x < S (S base_m2)}) :
nat :=
  match digits with
  | nil => 0
  | digit :: digits' => proj1_sig digit + le_to_nat digits' * S (S base_m2)
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlpFEfT"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqSBClfV"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
Theorem nat_le_inverse base_m2 :
  forall n, le_to_nat (nat_to_le base_m2 n) = n.
Proof.
(intros).
Unset Silent.
(induction n as [n IHn] using lt_wf_ind).
(destruct n; rewrite nat_to_le_equation; simpl).
-
auto.
-
(assert (1 < S (S base_m2)) by lia).
(assert (base_m2 = S (S base_m2) - 2) by lia).
(generalize dependent S (S base_m2); intros base **; subst).
Set Silent.
(assert (0 < S n) by lia).
(generalize dependent S n; clear n; intros n **).
(rewrite IHn).
{
(rewrite (PeanoNat.Nat.div_mod n base)  at 3 by lia).
lia.
}
(apply Nat.div_lt; lia).
Unset Silent.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqeJSuoV"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqFNw7z8"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Definition bounded_to_ascii (x : {x | x < 256}) : Ascii.ascii :=
  Ascii.ascii_of_nat (proj1_sig x).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtD6WKo"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq4qjpOa"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition ascii_to_bounded (a : Ascii.ascii) : {x | x < 256}.
Set Silent.
Set Silent.
Set Silent.
refine (exist _ (Ascii.nat_of_ascii a) _).
(apply Ascii.nat_ascii_bounded).
Unset Silent.
Defined.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2e8LX6"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqZAxZFb"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Instance aModel : GoModel.
Proof.
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
(apply Nat.lt_0_succ).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqmN14LA"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Defined.
Set Silent.
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
Unset Silent.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqwRsNEY"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqgoHMEH"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Instance aModel_wf : (GoModelWf aModel).
Proof.
Set Silent.
econstructor.
-
(simpl).
(apply pretty.pretty_nat_inj).
-
(simpl).
(unfold bounded_to_ascii, ascii_to_bounded).
(intros).
(destruct c; simpl).
(rewrite Ascii.ascii_nat_embedding; auto).
-
(simpl).
(destruct b; simpl).
(unfold ascii_to_bounded, bounded_to_ascii; simpl).
(apply subset_eq_compat).
(rewrite Ascii.nat_ascii_embedding; auto).
-
admit.
-
(simpl).
typeclasses eauto.
-
(simpl).
(unfold EqualDec).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(intros; simpl).
(decide equality; subst).
(decide equality; subst).
Timeout 1 Check @FinMapToList.
Timeout 1 Check @Acc.
Timeout 1 Check @empty.
Timeout 1 Check @max_type.
Timeout 1 Check @PeanoNat.Nat.mod_small.
typeclasses eauto.
