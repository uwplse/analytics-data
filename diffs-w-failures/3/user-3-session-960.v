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
From Classes Require Import EqualDec.
From RecordUpdate Require Import RecordUpdate.
From stdpp Require Import decidable countable.
From stdpp Require gmap.
From stdpp Require Import fin_maps.
Set Implicit Arguments.
Instance eqdecision  `{dec : EqualDec A}:
 (EqDecision A) := dec.
Definition uint64 := nat.
Definition compare_to x y (c : comparison) :
  {match c with
   | Lt => x < y
   | Gt => y < x
   | Eq => x = y
   end} +
  {match c with
   | Lt => x >= y
   | Gt => y >= x
   | Eq => x <> y
   end}.
(destruct c).
-
(apply Nat.eq_dec).
-
(destruct (lt_dec x y); auto; right;
  abstract omega).
-
(destruct (lt_dec y x); auto; right;
  abstract omega).
Defined.
Record FixedLengthEncoder bytes intTy 
byteTy (enc : intTy -> list byteTy)
(dec : list byteTy -> option intTy) :={
 encode_length_ok :
  forall x, length (enc x) = bytes;
 encode_decode_ok : forall x, dec (enc x) = Some x}.
Module Ptr.
Inductive ty : Type :=
  | Heap : forall T : Type, _
  | Map : forall V : Type, _
  | Lock : _.
End Ptr.
Unset Silent.
Class GoModel : Type :={byte : Type;
                        byte0 : byte;
                        uint64_to_string :
                         uint64 -> string;
                        ascii_to_byte :
                         Ascii.ascii -> byte;
                        byte_to_ascii :
                         byte -> Ascii.ascii;
                        uint64_to_le :
                         uint64 -> list byte;
                        uint64_from_le :
                         list byte ->
                         option uint64;
                        File : Type;
                        nilFile : File;
                        Ptr : Ptr.ty -> Type;
                        nullptr :
                         forall ty, Ptr ty}.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqClEEQ0"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqwoEFA8"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Timeout 1 Check @Insert.
Timeout 1 Check @ex.
Timeout 1 Check @ex.
Timeout 1 Check @GoModel.
Timeout 1 Check @GoModel.
Timeout 1 Check @GoModel.
Timeout 1 Check @GoModel.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.Ascii.
Timeout 1 Check @Ascii.shift.
Timeout 1 Check @Ascii.Space.
Timeout 1 Check @Ascii.shift.
Timeout 1 Check @strings.string_countable.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @FinMapToList.
Timeout 1 Check @strings.string_countable.
Set Printing Width 78.
Unset Silent.
Set Diffs "off".
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Search -"endian".
Timeout 1 Check @Build_Settable.
Timeout 1 Check @uint64.
Timeout 1 Check @uint64.
Timeout 1 Check @uint64.
Timeout 1 Check @uint64_to_le.
Timeout 1 Check @uint64_to_le.
Timeout 1 Check @uint64_to_le.
Timeout 1 Check @uint64_to_le.
Timeout 1 Check @Build_Settable.
Timeout 1 Check @uint64.
Timeout 1 Check @uint64.
Timeout 1 Check @ByteV2N.
Timeout 1 Check @ByteV2N.
Timeout 1 Check @ByteV2N.
Timeout 1 Check @ByteV2N.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteNil.
Timeout 1 Check @ByteVector.ByteVector.
Timeout 1 Check @ByteVector.ByteVector.
Timeout 1 Check @ByteVector.ByteVector.
Timeout 1 Check @ByteVector.ByteVector.
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
Timeout 1 Check @byte.
Timeout 1 Check @byte.
Timeout 1 Check @byte_to_ascii.
Timeout 1 Check @byte_to_ascii.
Timeout 1 Check @Byte.x25.
Set Printing Width 78.
Definition byte_nat := {x : nat | x < 256}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlC6Bto"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqhhWJJV"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Check @byte.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @FinMapToList.
Set Printing Width 78.
Timeout 1 Check @pointwise_relation.
Timeout 1 Check @nil.
Timeout 1 Check @Byte.x25.
Print sigT.
Print sig.
Timeout 1 Check @ex.
Timeout 1 Check @exist.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @nat_eq_dec.
Timeout 1 Check @Byte.x25.
Timeout 1 Check @gen.
#[program]
Fixpoint nat_to_le (x : nat) : list byte_nat :=
  match x with
  | 0 => nil
  | _ => exist _ (x mod 256) _ :: nat_to_le (x / 256)
  end.
