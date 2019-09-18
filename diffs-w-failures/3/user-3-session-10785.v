From Coq Require Import ProofIrrelevance.
From Coq Require Import String.
From Coq Require Import NArith.NArith.
From Coq Require Import ZArith.ZArith.
Class EqualDec A :=
    equal : forall x y : A, {x = y} + {x <> y}.
Module EqualDecNotation.
Infix "==" := equal (no associativity, at level 70).
End EqualDecNotation.
Instance unit_equal_dec : (EqualDec unit) :=
 (fun x y => left match x, y with
                  | tt, tt => eq_refl
                  end).
Hint Extern 2 (EqualDec _) => (hnf; repeat decide equality):
  typeclass_instances.
Instance nat_equal_dec : (EqualDec nat) := _.
Instance bool_equal_dec : (EqualDec bool) := _.
Instance positive_equal_dec : (EqualDec positive) := _.
Instance N_equal_dec : (EqualDec N) := _.
Instance Z_equal_dec : (EqualDec Z) := _.
Instance sigT_eq_dec  A (P : A -> Prop) (dec : EqualDec A):
 (EqualDec (sig P)).
Proof.
(hnf; intros).
(destruct x as [x ?], y as [y ?]).
(destruct (equal x y); subst; [ left | right ]).
-
f_equal.
(apply proof_irrelevance).
-
intro.
(inversion H; congruence).
Qed.
Definition ascii_cmp (x y : Ascii.ascii) : bool :=
  match x, y with
  | Ascii.Ascii x0 x1 x2 x3 x4 x5 x6 x7, Ascii.Ascii y0 y1 y2 y3 y4 y5 y6
    y7 =>
      Bool.eqb x0 y0 && Bool.eqb x1 y1 && Bool.eqb x2 y2 && Bool.eqb x3 y3 &&
      Bool.eqb x4 y4 && Bool.eqb x5 y5 && Bool.eqb x6 y6 && 
      Bool.eqb x7 y7
  end.
#[local]
Theorem eqb_spec b1 b2 :
  {Bool.eqb b1 b2 = true /\ b1 = b2} + {Bool.eqb b1 b2 = false /\ b1 <> b2}.
Proof.
(destruct b1, b2; simpl; auto).
(right; intuition idtac; congruence).
Qed.
#[local]
Ltac
 checkeq b1 b2 :=
  let Heqb := fresh "Heqb" in
  let Hb := fresh "Hb" in
  destruct (eqb_spec b1 b2) as [(Heqb, Hb)| (Heqb, Hb)]; rewrite Heqb; simpl;
   clear Heqb; [  | inversion 1; congruence ].
Theorem ascii_cmp_ok : forall x y, if ascii_cmp x y then x = y else x <> y.
Proof.
(destruct x as [x0 x1 x2 x3 x4 x5 x6 x7], y as [y0 y1 y2 y3 y4 y5 y6 y7];
  simpl).
(checkeq x0 y0).
(checkeq x1 y1).
(checkeq x2 y2).
(checkeq x3 y3).
(checkeq x4 y4).
(checkeq x5 y5).
(checkeq x6 y6).
(checkeq x7 y7).
(simpl; f_equal; auto).
Qed.
Instance ascii_eq_dec : (EqualDec Ascii.ascii).
Proof.
(hnf; intros).
(pose proof (ascii_cmp_ok x y)).
(destruct (ascii_cmp x y); auto).
Defined.
Instance string_eq_dec : (EqualDec string).
Proof.
(hnf; decide equality).
(destruct (equal a a0); auto).
Defined.
Definition inj_eq_dec {A} {dec : EqualDec A} {B} (f : B -> A)
  (f_inj : forall x y, f x = f y -> x = y) : EqualDec B.
Proof.
(hnf; intros).
(destruct (equal (f x) (f y)); [ left | right ]).
-
auto.
-
now intros ->.
Defined.
Instance pair_eq_dec  {A} {B} {decA : EqualDec A} 
 {decB : EqualDec B}: (EqualDec (A * B)) := _.
Instance sum_eq_dec  {A} {B} {decA : EqualDec A} {decB : EqualDec B}:
 (EqualDec (A + B)) := _.
Instance option_eq_dec  {A} {dec : EqualDec A}: (EqualDec (option A)) := _.
Instance list_eq_dec  {A} {dec : EqualDec A}: (EqualDec (list A)) := _.
