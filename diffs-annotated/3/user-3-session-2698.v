Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOZTC4R"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import FunInd Recdef.
From Coq Require Import PeanoNat.
From Coq Require Import Arith.
From Coq Require Import ProofIrrelevance.
From stdpp Require Import decidable countable.
From Classes Require Import EqualDec.
Import EqualDecNotation.
From Armada Require Import Goose.Machine.
From Coq Require Import List.
Set Implicit Arguments.
Opaque Nat.modulo Nat.div.
#[local]Obligation Tactic := (intros; simpl; subst).
Theorem mod_S_lt n m : n `mod` S m < S m.
Proof.
(apply Nat.mod_upper_bound; auto).
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
(apply Nat.div_lt; auto; try lia).
-
(apply lt_wf).
Qed.
Fixpoint nat_from_le base_m2 (digits : list {x : nat | x < S (S base_m2)}) :
nat :=
  match digits with
  | nil => 0
  | digit :: digits' => proj1_sig digit + nat_from_le digits' * S (S base_m2)
  end.
Theorem nat_le_inverse base_m2 :
  forall n, nat_from_le (nat_to_le base_m2 n) = n.
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
(generalize dependent S n; clear n; intros n **).
(rewrite IHn).
{
(rewrite (Nat.div_mod n base)  at 3 by lia).
lia.
}
(apply Nat.div_lt; lia).
Qed.
Definition bounded0 : {x | x < 256}.
exists 0.
(apply Nat.lt_0_succ).
Defined.
Definition nat64_from_le (digits : list {x | x < 256}) : nat :=
  nat_from_le digits.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIQarSZ"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqGiBzRk"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition bounded_to_ascii (x : {x | x < 256}) : Ascii.ascii :=
  Ascii.ascii_of_nat (proj1_sig x).
Definition ascii_to_bounded (a : Ascii.ascii) : {x | x < 256}.
refine (exist _ (Ascii.nat_of_ascii a) _).
(apply Ascii.nat_ascii_bounded).
Defined.
Instance aModel : GoModel.
Proof.
refine
 {|
 byte := {x | x < 256};
 byte0 := exist _ 0 _;
 uint64_to_string := pretty.pretty_nat;
 ascii_to_byte := ascii_to_bounded;
 byte_to_ascii := bounded_to_ascii;
 uint64_to_le := nat64_to_le;
 uint64_from_le := nat64_from_le;
 File := Z;
 nilFile := (- 1)%Z;
 Ptr := fun _ => nat;
 nullptr := fun _ => 0 |}.
(apply Nat.lt_0_succ).
Defined.
Instance aModel_wf : (GoModelWf aModel).
Proof.
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
(simpl; constructor).
(match goal with
 | H:context [ nat_le_dec ?n ?m ]
   |- _ => destruct (nat_le_dec n m); try congruence
 end).
(inversion H; subst).
(rewrite app_length).
