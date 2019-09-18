Time
Ltac
 safe_intuition_then t :=
  repeat
   match goal with
   | H:_ /\ _ |- _ => destruct H
   | H:?P -> _
     |- _ => lazymatch type of P with
             | Prop => specialize (H _)
             | _ => fail
             end
   | _ => progress t
   end.
Time Tactic Notation "safe_intuition" := (safe_intuition_then ltac:(auto)).
Time Tactic Notation "safe_intuition" tactic(t) := (safe_intuition_then t).
Time From Coq Require Import ProofIrrelevance.
Time Class Default T :=
         default : T.
Time #[local]Ltac mkDefault := unfold Default; constructor; exact default.
Time Hint Extern 1 (Default _) => mkDefault: typeclass_instances.
Time #[local]Notation cache_default := _ (only parsing).
Time Instance unit_def : (Default unit) := cache_default.
Time Instance nat_def : (Default nat) := cache_default.
Time
Ltac
 propositional :=
  repeat
   match goal with
   | |- forall _, _ => intros
   | H:_ /\ _ |- _ => destruct H
   | H:_ <-> _ |- _ => destruct H
   | H:False |- _ => solve [ destruct H ]
   | H:True |- _ => clear H
   | H:?P -> _, H':?P
     |- _ => match type of P with
             | Prop => specialize (H H')
             end
   | H:forall x, x = _ -> _ |- _ => specialize (H _ eq_refl)
   | H:forall x, _ = x -> _ |- _ => specialize (H _ eq_refl)
   | H:exists varname, _
     |- _ => let newvar := fresh varname in
             destruct H as [newvar ?]
   | H:?P |- ?P => exact H
   | _ => progress subst
   end.
Time
Ltac
 prove_hyps H :=
  match type of H with
  | ?P -> ?Q =>
      let HP := fresh in
      assert (HP : P); [  | specialize (H HP); clear HP; prove_hyps H ]
  | _ => idtac
  end.
Time
Ltac destruct_ands := repeat match goal with
                             | H:_ /\ _ |- _ => destruct H
                             end.
Time
Ltac
 deex :=
  match goal with
  | H:exists varname, _
    |- _ =>
        let newvar := fresh varname in
        destruct H as [newvar ?]; destruct_ands; subst
  end.
Time From Coq Require Import String.
Time Instance list_def  A: (Default (list A)) := cache_default.
Time Instance option_def  A: (Default (option A)) := cache_default.
Time
Instance pair_def  A B (defA : Default A) (defB : Default B):
 (Default (A * B)) := cache_default.
Time From Coq Require Import NArith.NArith.
Time From Coq Require Import ZArith.ZArith.
Time Class EqualDec A :=
         equal : forall x y : A, {x = y} + {x <> y}.
Time Module EqualDecNotation.
Time Infix "==" := equal (no associativity, at level 70).
Time End EqualDecNotation.
Time
Instance unit_equal_dec : (EqualDec unit) :=
 (fun x y => left match x, y with
                  | tt, tt => eq_refl
                  end).
Time
Hint Extern 2 (EqualDec _) => (hnf; repeat decide equality):
  typeclass_instances.
Time Instance nat_equal_dec : (EqualDec nat) := _.
Time Instance bool_equal_dec : (EqualDec bool) := _.
Time Instance positive_equal_dec : (EqualDec positive) := _.
Time Instance N_equal_dec : (EqualDec N) := _.
Time Instance Z_equal_dec : (EqualDec Z) := _.
Time
Instance sigT_eq_dec  A (P : A -> Prop) (dec : EqualDec A):
 (EqualDec (sig P)).
Time Proof.
Time (hnf; intros).
Time (destruct x as [x ?], y as [y ?]).
Time (destruct (equal x y); subst; [ left | right ]).
Time -
Time f_equal.
Time (apply proof_irrelevance).
Time -
Time intro.
Time (inversion H; congruence).
Time Qed.
Time
Definition ascii_cmp (x y : Ascii.ascii) : bool :=
  match x, y with
  | Ascii.Ascii x0 x1 x2 x3 x4 x5 x6 x7, Ascii.Ascii y0 y1 y2 y3 y4 y5 y6
    y7 =>
      Bool.eqb x0 y0 && Bool.eqb x1 y1 && Bool.eqb x2 y2 && Bool.eqb x3 y3 &&
      Bool.eqb x4 y4 && Bool.eqb x5 y5 && Bool.eqb x6 y6 && 
      Bool.eqb x7 y7
  end.
Time #[local]
Theorem eqb_spec b1 b2 :
  {Bool.eqb b1 b2 = true /\ b1 = b2} + {Bool.eqb b1 b2 = false /\ b1 <> b2}.
Time Proof.
Time (destruct b1, b2; simpl; auto).
Time (right; intuition idtac; congruence).
Time Qed.
Time #[local]
Ltac
 checkeq b1 b2 :=
  let Heqb := fresh "Heqb" in
  let Hb := fresh "Hb" in
  destruct (eqb_spec b1 b2) as [(Heqb, Hb)| (Heqb, Hb)]; rewrite Heqb; simpl;
   clear Heqb; [  | inversion 1; congruence ].
Time
Theorem ascii_cmp_ok : forall x y, if ascii_cmp x y then x = y else x <> y.
Time Proof.
Time
(destruct x as [x0 x1 x2 x3 x4 x5 x6 x7], y as [y0 y1 y2 y3 y4 y5 y6 y7];
  simpl).
Time (checkeq x0 y0).
Time (checkeq x1 y1).
Time (checkeq x2 y2).
Time (checkeq x3 y3).
Time (checkeq x4 y4).
Time (checkeq x5 y5).
Time (checkeq x6 y6).
Time (checkeq x7 y7).
Time (simpl; f_equal; auto).
Time Qed.
Time Instance ascii_eq_dec : (EqualDec Ascii.ascii).
Time Proof.
Time (hnf; intros).
Time (pose proof (ascii_cmp_ok x y)).
Time (destruct (ascii_cmp x y); auto).
Time Defined.
Time Instance string_eq_dec : (EqualDec string).
Time Proof.
Time (hnf; decide equality).
Time (destruct (equal a a0); auto).
Time Defined.
Time
Definition inj_eq_dec {A} {dec : EqualDec A} {B} (f : B -> A)
  (f_inj : forall x y, f x = f y -> x = y) : EqualDec B.
Time Proof.
Time (hnf; intros).
Time (destruct (equal (f x) (f y)); [ left | right ]).
Time -
Time auto.
Time -
Time now intros ->.
Time Defined.
Time
Instance pair_eq_dec  {A} {B} {decA : EqualDec A} 
 {decB : EqualDec B}: (EqualDec (A * B)) := _.
Time
Instance sum_eq_dec  {A} {B} {decA : EqualDec A} {decB : EqualDec B}:
 (EqualDec (A + B)) := _.
Time
Instance option_eq_dec  {A} {dec : EqualDec A}: (EqualDec (option A)) := _.
Time Instance list_eq_dec  {A} {dec : EqualDec A}: (EqualDec (list A)) := _.
