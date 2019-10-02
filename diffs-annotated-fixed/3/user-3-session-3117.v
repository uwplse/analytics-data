Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqkXC7vA"
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
Definition nat64_to_le (x : nat) : option (list {x | x < 256}) :=
  let digits := nat_to_le 254 x in
  if nat_le_dec (length digits) 8
  then Some (digits ++ repeat bounded0 (8 - length digits))
  else None.
Theorem nat_from_le_zeros base_m2 digits zero_v n :
  proj1_sig zero_v = 0 ->
  @nat_from_le base_m2 (digits ++ repeat zero_v n) =
  @nat_from_le base_m2 digits.
Proof.
(intros).
(induction digits; simpl; auto).
(induction n; simpl; auto).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqll1W1i"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqGtM8hg"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
(rewrite H, IHn; simpl; auto).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq4x1vYk"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Definition nat64_from_le (digits : list {x | x < 256}) : nat :=
  nat_from_le digits.
Definition bounded_to_ascii (x : {x | x < 256}) : Ascii.ascii :=
  Ascii.ascii_of_nat (proj1_sig x).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqTZvLgo"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqYMIykl"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Check Ascii.nat_ascii_bounded.
Theorem N_ascii_bounded : forall a, (Ascii.N_of_ascii a < 256)%N.
Proof.
(destruct a as [[| ] [| ] [| ] [| ] [| ] [| ] [| ] [| ]]; vm_compute;
  reflexivity).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqrQYZbi"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
(* Auto-generated comment: Succeeded. *)

