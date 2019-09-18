Time From RecordUpdate Require Import RecordUpdate.
Time From Transitions Require Import Relations.
Time From Coq Require Import FunInd Recdef.
Time From Coq Require Import PeanoNat.
Time From Coq Require Import Arith.
Time From Armada Require Import Spec.Proc.
Time From Armada Require Import Spec.InjectOp.
Time From Armada.Goose Require Import Machine.
Time From Coq Require Import ProofIrrelevance.
Time From stdpp Require Import decidable countable.
Time Set Implicit Arguments.
Time Module Globals.
Time Section GoModel.
Time Context `{model_wf : GoModelWf}.
Time Context {G : Type}.
Time
Inductive Op : Type -> Type :=
  | SetX : forall x : G, Op unit
  | GetX : Op G.
Time Definition State := option G.
Time Definition init : State := None.
Time Import RelationNotations.
Time
Definition step T (op : Op T) : relation State State T :=
  match op in (Op T) return (relation State State T) with
  | SetX x => s <- reads id;
      match s with
      | Some _ => error
      | None => puts (fun _ => Some x)
      end
  | GetX => readSome id
  end.
Time Section OpWrappers.
Time Context {Op'} {i : Injectable Op Op'}.
Time Notation proc := (proc Op').
Time Notation "'Call' op" := (Call (inject op) : proc _) (at level 0).
Time
Notation "'Call!' op" := (Call (op) : proc _) (at level 0, op  at level 200).
Time Definition setX x := Call! SetX x.
Time Definition getX := Call! GetX.
Time End OpWrappers.
Time End GoModel.
Time End Globals.
Time Arguments Globals.Op G : clear implicits.
Time Arguments Globals.State G : clear implicits.
Time From Classes Require Import EqualDec.
Time Import EqualDecNotation.
Time From Armada Require Import Goose.Machine.
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
Definition nat64_to_le (x : nat) : list {x | x < 256} :=
  let digits := nat_to_le 254 x in
  digits ++ repeat bounded0 (8 - length digits).
Time
Theorem nat_from_le_zeros base_m2 digits zero_v n :
  proj1_sig zero_v = 0 ->
  @nat_from_le base_m2 (digits ++ repeat zero_v n) =
  @nat_from_le base_m2 digits.
Time Proof.
Time (intros).
Time (induction digits; simpl; auto).
Time (induction n; simpl; auto).
Time lia.
Time Qed.
Time
Definition nat64_from_le (digits : list {x | x < 256}) : 
  option nat :=
  if nat_eq_dec (length digits) 8 then Some (nat_from_le digits) else None.
Time
Definition bounded_to_ascii (x : {x | x < 256}) : Ascii.ascii :=
  Ascii.ascii_of_nat (proj1_sig x).
Time Definition ascii_to_bounded (a : Ascii.ascii) : {x | x < 256}.
Time refine (exist _ (Ascii.nat_of_ascii a) _).
Time (apply Ascii.nat_ascii_bounded).
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
