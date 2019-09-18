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
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Set Silent.
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
(rewrite (PeanoNat.Nat.div_mod n base)  at 3 by lia).
lia.
}
(apply Nat.div_lt; lia).
Qed.
Unset Silent.
Timeout 1 Check @pointwise_relation.
Timeout 1 Check @repeat.
Timeout 1 Check @repeat.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @Plength.
Timeout 1 Check @Plength.
Timeout 1 Check @Plength.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @pointwise_relation.
Timeout 1 Check @byte.
Timeout 1 Check @Byte.x25.
Definition bounded0 : {x | x < 256}.
Timeout 1 Check @pointwise_relation.
Timeout 1 Check @eq_existT_curried.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @FinMapToList.
Timeout 1 Check @PeanoNat.Nat.mod_small.
Timeout 1 Check @Nat.lt_0_succ.
Timeout 1 Check @Nat.lt_0_succ.
Timeout 1 Check @Nat.lt_0_succ.
Set Printing Width 78.
Show.
Set Silent.
exists 0.
Unset Silent.
(apply Nat.lt_0_succ).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOGprCQ"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Defined.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqBCZxql"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqpJJRBT"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Definition nat64_to_le (x : nat) : list byte :=
  let digits := nat_to_le 254 x in
  digits ++ repeat (8 - length digits) bounded0.
