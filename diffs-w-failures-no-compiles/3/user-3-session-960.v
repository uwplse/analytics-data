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
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Ascii.nat_ascii_bounded.
Timeout 1 Check @Byte.x25.
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
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nat64_to_le.
Timeout 1 Check @nat64_to_le.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @split.
Timeout 1 Check @Byte.x25.
Timeout 1 Check @top.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @PeanoNat.Nat.le_decidable.
Timeout 1 Check @PeanoNat.Nat.le_decidable.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @Plength.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nth.
Timeout 1 Check @Some.
Timeout 1 Check @Some.
Timeout 1 Check @Some.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @pointwise_relation.
Set Printing Width 78.
Unset Silent.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @BoolTheory.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.N_of_digits.
Timeout 1 Check @eq_existT_curried.
Timeout 1 Check @Eq_ext.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @nat_to_le_equation.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.N_of_digits.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.N_of_digits.
Timeout 1 Check @pointwise_relation.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Timeout 1 Check @nat_from_le.
Set Printing Width 78.
Timeout 1 Check @N.lbase.
Timeout 1 Check @N.lbase.
Timeout 1 Check @size.
Timeout 1 Check @zerop.
Timeout 1 Check @N.zero_one.
Timeout 1 Check @size.
Timeout 1 Check @prod_eq_dec.
Timeout 1 Check @proj1.
Timeout 1 Check @proj1_sig.
Timeout 1 Check @proj1_sig.
Timeout 1 Check @proj1_sig.
Timeout 1 Check @proj1_sig.
Timeout 1 Check @size.
Timeout 1 Check @zerop.
Timeout 1 Check @N.zero_one.
Theorem nat_from_le_zeros base_m2 digits zero_v n :
  proj1_sig zero_v = 0 ->
  @nat_from_le base_m2 (digits ++ repeat zero_v n) =
  @nat_from_le base_m2 digits.
Proof.
Timeout 1 Check @Ascii.nat_ascii_embedding.
(intros).
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @N.induction.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @sigT_eq_dec.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(induction digits; simpl; auto).
Timeout 1 Check @Ascii.nat_ascii_embedding.
Timeout 1 Check @N.induction.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @sigT_eq_dec.
Set Printing Width 78.
Show.
(induction n; simpl; auto).
Timeout 1 Check @split.
lia.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq9nV4Di"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Qed.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqi0BG8o"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqsIGmtC"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
Set Silent.
Set Silent.
Set Silent.
Definition nat64_from_le (digits : list {x | x < 256}) : 
  option nat :=
  if nat_eq_dec (length digits) 8 then Some (nat_from_le digits) else None.
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
Unset Silent.
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
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqR1BSph"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqMnUoo9"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
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
(apply subset_eq_compat).
(rewrite Ascii.nat_ascii_embedding; auto).
Unset Silent.
-
Timeout 1 Check @subset_eq_compat.
Timeout 1 Check @subset_eq_compat.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
admit.
admit.
