Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqbYKjAs"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 78.
Set Silent.
From Coq Require Import ProofIrrelevance.
From Coq Require Export String.
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
Unset Silent.
Record FixedLengthEncoder bytes intTy byteTy
(enc : intTy -> option (list byteTy)) (dec : list byteTy -> intTy) :={
 encode_length_ok : forall x bs, enc x = Some bs -> length bs = bytes;
 encode_decode_ok : forall x bs, enc x = Some bs -> dec bs = x}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqu7NmrE"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqqwidoe"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
Module Ptr.
Inductive ty : Type :=
  | Heap : forall T : Type, _
  | Map : forall V : Type, _
  | Lock : _.
End Ptr.
Declare Instance type_dec : (EqualDec Ptr.ty).
Unset Silent.
Class GoModel : Type :={byte : Type;
                        byte0 : byte;
                        uint64_to_string : uint64 -> string;
                        ascii_to_byte : Ascii.ascii -> byte;
                        byte_to_ascii : byte -> Ascii.ascii;
                        uint64_to_le : uint64 -> option (list byte);
                        uint64_from_le : list byte -> uint64;
                        File : Type;
                        nilFile : File;
                        Ptr : Ptr.ty -> Type;
                        nullptr : forall ty, Ptr ty}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqKmVi7p"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqND8s9b"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
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
Section DerivedMethods.
Context {model : GoModel} {model_wf : GoModelWf model}.
Fixpoint bytes_to_string (l : list byte) : string :=
  match l with
  | nil => EmptyString
  | b :: bs => String (byte_to_ascii b) (bytes_to_string bs)
  end.
Fixpoint string_to_bytes (s : string) : list byte :=
  match s with
  | EmptyString => nil
  | String c s' => ascii_to_byte c :: string_to_bytes s'
  end.
Theorem bytes_to_string_bijection_1 :
  forall l, string_to_bytes (bytes_to_string l) = l.
Proof.
(induction l; simpl; rewrite ?ascii_byte_bijection1, ?ascii_byte_bijection2;
  congruence).
Qed.
Theorem bytes_to_string_bijection_2 :
  forall s, bytes_to_string (string_to_bytes s) = s.
Proof.
(induction s; simpl; rewrite ?ascii_byte_bijection1, ?ascii_byte_bijection2;
  congruence).
Qed.
End DerivedMethods.
Notation ptr T:= (Ptr (Ptr.Heap T)).
Notation Map V:= (Ptr (Ptr.Map V)).
Notation LockRef := (Ptr Ptr.Lock).
Module slice.
Section Slices.
Context {model : GoModel}.
Variable (A : Type).
Record t := mk {ptr : Ptr (Ptr.Heap A); offset : uint64; length : uint64}.
Instance _eta : (Settable t) := settable! mk < ptr; offset; length >.
Definition nil := {| ptr := nullptr _; offset := 0; length := 0 |}.
Definition skip (n : uint64) (x : t) : t :=
  set length (fun l => l - n) (set offset (fun o => o + n) x).
Definition take (n : uint64) (x : t) : t := set length (fun _ => n) x.
Definition subslice (low high : uint64) (x : t) : t :=
  set length (fun _ => high - low) (set offset (fun o => o + low) x).
Theorem subslice_skip_take low high x :
  subslice low high x = skip low (take high x).
Proof.
(destruct x; unfold subslice, skip; simpl; auto).
Qed.
Theorem subslice_take_skip low high x :
  subslice low high x = take (high - low) (skip low x).
Proof.
(destruct x; unfold subslice, skip; simpl; auto).
Qed.
End Slices.
End slice.
Instance slice_eq_dec  `{GoModelWf}: (EqualDec (sigT slice.t)).
Proof.
(hnf; intros).
(destruct x as [T1 x], y as [T2 y]).
(destruct x, y; simpl).
(destruct (equal (existT _ ptr) (existT _ ptr0)); [  | right ]).
-
(destruct (equal offset offset0), (equal length length0); [ left | right.. ];
  repeat
   match goal with
   | H:existT ?T _ = existT ?T _ |- _ => apply inj_pair2 in H; subst
   | H:existT _ _ = existT _ _ |- _ => inversion H; subst; clear H
   end; eauto; try (inversion 1; congruence)).
-
(inversion 1; subst).
(apply inj_pair2 in H3; subst; congruence).
Unset Silent.
Defined.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqK1j6SC"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqJSOiX8"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
