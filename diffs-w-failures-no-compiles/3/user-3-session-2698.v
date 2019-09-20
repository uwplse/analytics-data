Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOZTC4R"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
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
Unset Silent.
Set Diffs "off".
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.N_of_digits.
Timeout 1 Check @repeat_length.
Timeout 1 Check @pointwise_relation.
Timeout 1 Check @None.
Timeout 1 Check @DiagNone.
Set Printing Width 78.
Definition nat64_to_le (x : nat) : option (list {x | x < 256}) :=
  let digits := nat_to_le 254 x in
  if nat_le_dec (length digits) 8
  then Some (digits ++ repeat bounded0 (8 - length digits))
  else None.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq3PKT1A"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqmyolBc"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Theorem nat_from_le_zeros base_m2 digits zero_v n :
  proj1_sig zero_v = 0 ->
  @nat_from_le base_m2 (digits ++ repeat zero_v n) =
  @nat_from_le base_m2 digits.
Set Silent.
Proof.
(intros).
(induction digits; simpl; auto).
(induction n; simpl; auto).
lia.
Qed.
Unset Silent.
Definition nat64_from_le (digits : list {x | x < 256}) : 
  option nat :=
  if nat_eq_dec (length digits) 8 then Some (nat_from_le digits) else None.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq2AL3Dg"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWpS2bI"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition bounded_to_ascii (x : {x | x < 256}) : Ascii.ascii :=
  Ascii.ascii_of_nat (proj1_sig x).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqulyt9M"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqt9Zf90"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
