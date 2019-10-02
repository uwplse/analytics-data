Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqWfrXOb"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import ProofIrrelevance.
From Coq Require Export String.
From Coq Require Import Program.
Timeout 1 Print LoadPath.
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
Module Ptr.
Inductive ty : Type :=
  | Heap : forall T : Type, _
  | Map : forall V : Type, _
  | Lock : _.
#[global]Declare Instance type_dec : (EqualDec ty).
End Ptr.
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
Fixpoint le_to_nat base_m2 (digits : list {x : nat | x < S (S base_m2)}) :
nat :=
  match digits with
  | nil => 0
  | digit :: digits' => proj1_sig digit + le_to_nat digits' * S (S base_m2)
  end.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlpFEfT"
Print Ltac Signatures.
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
Definition bounded0 : {x | x < 256}.
exists 0.
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
Definition nat64_to_le (x : nat) : list {x | x < 256} :=
  let digits := nat_to_le 254 x in
  digits ++ repeat bounded0 (8 - length digits).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0IJEmx"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQ7ZRNG"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0tOdBI"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqtgpwMU"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition bounded_to_ascii (x : {x | x < 256}) : Ascii.ascii :=
  Ascii.ascii_of_nat (proj1_sig x).
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqN87KBx"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq3cjQfp"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition ascii_to_bounded (a : Ascii.ascii) : {x | x < 256}.
refine (exist _ (Ascii.nat_of_ascii a) _).
(apply Ascii.nat_ascii_bounded).
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqnI3cRx"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
 uint64_to_le := nat_to_le 254;
 uint64_from_le := fun digits => Some (nat_from_le digits);
 File := Z;
 nilFile := (- 1)%Z;
 Ptr := fun _ => nat;
 nullptr := fun _ => 0 |}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqih90a6"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
refine
 {|
 byte := {x | x < 256};
 byte0 := exist _ 0 _;
 uint64_to_string := pretty.pretty_nat;
 ascii_to_byte := ascii_to_bounded;
 byte_to_ascii := bounded_to_ascii;
 uint64_to_le := nat64_from_le;
 uint64_from_le := nat64_from_le;
 File := Z;
 nilFile := (- 1)%Z;
 Ptr := fun _ => nat;
 nullptr := fun _ => 0 |}.
(* Auto-generated comment: Failed. *)

