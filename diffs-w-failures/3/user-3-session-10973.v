Time From Coq Require Import FunInd Recdef.
Time From Coq Require Import PeanoNat.
Time From Coq Require Import Arith.
Time From Coq Require Import ProofIrrelevance.
Time From stdpp Require Import decidable countable.
Time From Classes Require Import EqualDec.
Time Import EqualDecNotation.
Time From Perennial Require Import Goose.Machine.
Time From Coq Require Import List.
Time Set Implicit Arguments.
Time Opaque Nat.modulo Nat.div.
Time #[local]Obligation Tactic := (intros; simpl; subst).
Time Theorem mod_S_lt n m : n `mod` S m < S m.
Time Proof.
Time (apply Nat.mod_upper_bound; auto).
Time Qed.
Time
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
Time Proof.
Time -
Time (intros; subst).
Time (apply Nat.div_lt; auto; try lia).
Time -
Time (apply lt_wf).
Time Qed.
Time
Fixpoint nat_from_le base_m2 (digits : list {x : nat | x < S (S base_m2)}) :
nat :=
  match digits with
  | nil => 0
  | digit :: digits' => proj1_sig digit + nat_from_le digits' * S (S base_m2)
  end.
Time
Theorem nat_le_inverse base_m2 :
  forall n, nat_from_le (nat_to_le base_m2 n) = n.
Time Proof.
Time (intros).
Time (induction n as [n IHn] using lt_wf_ind).
Time (destruct n; rewrite nat_to_le_equation; simpl).
Time -
Time auto.
Time -
Time (assert (1 < S (S base_m2)) by lia).
Time (assert (base_m2 = S (S base_m2) - 2) by lia).
Time (generalize dependent S (S base_m2); intros base **; subst).
Time (assert (0 < S n) by lia).
Time (generalize dependent S n; clear n; intros n **).
Time (rewrite IHn).
Time {
Time (rewrite (Nat.div_mod n base)  at 3 by lia).
Time lia.
Time }
Time (apply Nat.div_lt; lia).
Time Qed.
Time Definition bounded0 : {x | x < 256}.
Time exists 0.
Time (apply Nat.lt_0_succ).
Time Defined.
Time
Definition nat64_to_le (x : nat) : option (list {x | x < 256}) :=
  let digits := nat_to_le 254 x in
  if nat_le_dec (length digits) 8
  then Some (digits ++ repeat bounded0 (8 - length digits))
  else None.
Time
Theorem nat_from_le_zeros base_m2 digits zero_v n :
  proj1_sig zero_v = 0 ->
  @nat_from_le base_m2 (digits ++ repeat zero_v n) =
  @nat_from_le base_m2 digits.
Time Proof.
Time (intros).
Time (induction digits; simpl; auto).
Time (induction n; simpl; auto).
Time (rewrite H, IHn; simpl; auto).
Time Qed.
Time
Definition nat64_from_le (digits : list {x | x < 256}) : nat :=
  nat_from_le digits.
Time
Definition bounded_to_ascii (x : {x | x < 256}) : Ascii.ascii :=
  Ascii.ascii_of_nat (proj1_sig x).
Time Theorem N_ascii_bounded : forall a, (Ascii.N_of_ascii a < 256)%N.
Time Proof.
Time
(destruct a as [[| ] [| ] [| ] [| ] [| ] [| ] [| ] [| ]]; vm_compute;
  reflexivity).
Time Qed.
Time Theorem nat_ascii_bounded : forall a, Ascii.nat_of_ascii a < 256.
Time Proof.
Time (intro a; unfold Ascii.nat_of_ascii).
Time (change_no_check 256 with (N.to_nat 256)).
Time (rewrite <- Nat.compare_lt_iff, <- N2Nat.inj_compare, N.compare_lt_iff).
Time (apply N_ascii_bounded).
Time Qed.
Time Definition ascii_to_bounded (a : Ascii.ascii) : {x | x < 256}.
Time refine (exist _ (Ascii.nat_of_ascii a) _).
Time (apply nat_ascii_bounded).
Time Defined.
Time Instance aModel : GoModel.
Time Proof.
Time
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
Time (apply Nat.lt_0_succ).
Time Defined.
Time Instance aModel_wf : (GoModelWf aModel).
Time Proof.
Time econstructor.
Time -
Time (simpl).
Time (apply pretty.pretty_nat_inj).
Time -
Time (simpl).
Time (unfold bounded_to_ascii, ascii_to_bounded).
Time (intros).
Time (destruct c; simpl).
Time (rewrite Ascii.ascii_nat_embedding; auto).
Time -
Time (simpl).
Time (destruct b; simpl).
Time (unfold ascii_to_bounded, bounded_to_ascii; simpl).
Time (apply ProofIrrelevanceTheory.subset_eq_compat).
Time (rewrite Ascii.nat_ascii_embedding; auto).
Time -
Time
(simpl; constructor; unfold nat64_to_le, nat64_from_le; intros;
  match goal with
  | H:context [ nat_le_dec ?n ?m ]
    |- _ => destruct (nat_le_dec n m); try congruence
  end).
Time +
Time (inversion H; subst).
Time (rewrite app_length, repeat_length).
Time lia.
Time +
Time (inversion H; subst).
Time (rewrite nat_from_le_zeros; auto).
Time (rewrite nat_le_inverse; auto).
Time -
Time (simpl).
Time typeclasses eauto.
Time -
Time (simpl).
Time (unfold EqualDec).
Time (intros; simpl).
Time (decide equality; subst).
Time (decide equality; subst).
Time (destruct (x0 == x1); auto).
Time Qed.
