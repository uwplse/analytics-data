Time From Coq Require Import ProofIrrelevance.
Time From Coq Require Export String.
Time From Classes Require Import EqualDec.
Time From RecordUpdate Require Import RecordUpdate.
Time From stdpp Require Import decidable countable.
Time From stdpp Require gmap.
Time From stdpp Require Import fin_maps.
Time Set Implicit Arguments.
Time Instance eqdecision  `{dec : EqualDec A}: (EqDecision A) := dec.
Time Definition uint64 := nat.
Time
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
Time (destruct c).
Time -
Time (apply Nat.eq_dec).
Time -
Time (destruct (lt_dec x y); auto; right; abstract omega).
Time -
Time (destruct (lt_dec y x); auto; right; abstract omega).
Time Defined.
Time
Record FixedLengthEncoder bytes intTy byteTy
(enc : intTy -> option (list byteTy)) (dec : list byteTy -> intTy) :={
 encode_length_ok : forall x bs, enc x = Some bs -> length bs = bytes;
 encode_decode_ok : forall x bs, enc x = Some bs -> dec bs = x}.
Time Module Ptr.
Time
Inductive ty : Type :=
  | Heap : forall T : Type, _
  | Map : forall V : Type, _
  | Lock : _.
Time End Ptr.
Time Declare Instance type_dec : (EqualDec Ptr.ty).
Time
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
Time
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
Time Section DerivedMethods.
Time Context {model : GoModel} {model_wf : GoModelWf model}.
Time
Fixpoint bytes_to_string (l : list byte) : string :=
  match l with
  | nil => EmptyString
  | b :: bs => String (byte_to_ascii b) (bytes_to_string bs)
  end.
Time
Fixpoint string_to_bytes (s : string) : list byte :=
  match s with
  | EmptyString => nil
  | String c s' => ascii_to_byte c :: string_to_bytes s'
  end.
Time
Theorem bytes_to_string_bijection_1 :
  forall l, string_to_bytes (bytes_to_string l) = l.
Time Proof.
Time
(induction l; simpl; rewrite ?ascii_byte_bijection1, ?ascii_byte_bijection2;
  congruence).
Time Qed.
Time
Theorem bytes_to_string_bijection_2 :
  forall s, bytes_to_string (string_to_bytes s) = s.
Time Proof.
Time
(induction s; simpl; rewrite ?ascii_byte_bijection1, ?ascii_byte_bijection2;
  congruence).
Time Qed.
Time End DerivedMethods.
Time Notation ptr T:= (Ptr (Ptr.Heap T)).
Time Notation Map V:= (Ptr (Ptr.Map V)).
Time Notation LockRef := (Ptr Ptr.Lock).
Time Module slice.
Time Section Slices.
Time Context {model : GoModel}.
Time Variable (A : Type).
Time
Record t := mk {ptr : Ptr (Ptr.Heap A); offset : uint64; length : uint64}.
Time Instance _eta : (Settable t) := settable! mk < ptr; offset; length >.
Time Definition nil := {| ptr := nullptr _; offset := 0; length := 0 |}.
Time
Definition skip (n : uint64) (x : t) : t :=
  set length (fun l => l - n) (set offset (fun o => o + n) x).
Time Definition take (n : uint64) (x : t) : t := set length (fun _ => n) x.
Time
Definition subslice (low high : uint64) (x : t) : t :=
  set length (fun _ => high - low) (set offset (fun o => o + low) x).
Time
Theorem subslice_skip_take low high x :
  subslice low high x = skip low (take high x).
Time Proof.
Time (destruct x; unfold subslice, skip; simpl; auto).
Time Qed.
Time
Theorem subslice_take_skip low high x :
  subslice low high x = take (high - low) (skip low x).
Time Proof.
Time (destruct x; unfold subslice, skip; simpl; auto).
Time Qed.
Time End Slices.
Time End slice.
Time Instance slice_eq_dec  `{GoModelWf}: (EqualDec (sigT slice.t)).
Time Proof.
Time (hnf; intros).
Time (destruct x as [T1 x], y as [T2 y]).
Time (destruct x, y; simpl).
Time (destruct (equal (existT _ ptr) (existT _ ptr0)); [  | right ]).
Time -
Time
(destruct (equal offset offset0), (equal length length0); [ left | right.. ];
  repeat
   match goal with
   | H:existT ?T _ = existT ?T _ |- _ => apply inj_pair2 in H; subst
   | H:existT _ _ = existT _ _ |- _ => inversion H; subst; clear H
   end; eauto; try (inversion 1; congruence)).
Time -
Time (inversion 1; subst).
Time (apply inj_pair2 in H3; subst; congruence).
Time Defined.
