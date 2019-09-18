Class Default T :=
    default : T.
#[local]Ltac mkDefault := unfold Default; constructor; exact default.
Set Implicit Arguments.
Definition Reader E T := forall e : E, T e.
Arguments Reader : clear implicits.
Definition constructor {E} {T} (x : T) : Reader E (fun _ => T) := fun _ => x.
Hint Extern 1 (Default _) => mkDefault: typeclass_instances.
#[local]Notation cache_default := _ (only parsing).
Instance unit_def : (Default unit) := cache_default.
Instance nat_def : (Default nat) := cache_default.
Instance list_def  A: (Default (list A)) := cache_default.
Instance option_def  A: (Default (option A)) := cache_default.
Instance pair_def  A B (defA : Default A) (defB : Default B):
 (Default (A * B)) := cache_default.
Definition applicative_ap {E} {A : E -> Type} {B : forall e : E, A e -> Type}
  (f : Reader E (fun e => forall a : A e, B e a)) :
  forall x : Reader E A, Reader E (fun e => B e (x e)) :=
  fun x => fun e => f e (x e).
Class Settable T :={mkT : Reader T (fun _ => T);
                    mkT_ok : forall x, mkT x = x}.
Arguments mkT T mk : clear implicits,  rename.
#[local]
Ltac
 solve_mkT_ok :=
  match goal with
  | |- forall x, _ = _ => solve [ destruct x; compute; f_equal ]
  end.
Notation "'settable!' mk < f1 ; .. ; fn >" :=
  (Build_Settable
     (applicative_ap .. (applicative_ap (constructor mk) f1) .. fn) _)
  (at level 0, mk  at level 10, f1, fn  at level 9, only parsing).
#[local]
Ltac
 setter etaT proj :=
  let set :=
   match eval pattern proj in etaT with
   | ?setter ?proj => fun f => setter (fun r => f (proj r))
   end
  in
  let set := eval cbv[constructor applicative_ap] in set in
  exact
  set.
#[local]
Ltac
 get_setter T proj :=
  match mkT T _ with
  | mkT _ ?updateable =>
      let updateable := eval hnf in updateable in
      match updateable with
      | {| mkT := ?mk |} => setter mk proj
      end
  end.
Class Setter {R} {T} (proj : R -> T) :=
    set : (T -> T) -> R -> R.
From Coq Require Import ProofIrrelevance.
From Coq Require Import String.
Arguments set {R} {T} proj {Setter}.
Class SetterWf {R} {T} (proj : R -> T) :={set_wf :> Setter proj;
                                          set_get :
                                           forall v r,
                                           proj (set proj v r) = v (proj r);
                                          set_eq :
                                           forall f r,
                                           f (proj r) = proj r ->
                                           set proj f r = r}.
Arguments set_wf {R} {T} proj {SetterWf}.
#[local]
Ltac
 SetterInstance_t := match goal with
                     | |- @Setter ?T _ ?A => get_setter T A
                     end.
#[local]
Ltac
 SetterWfInstance_t :=
  match goal with
  | |- @SetterWf ?T _ ?A =>
        unshelve notypeclasses refine (Build_SetterWf _ _ _);
         [ get_setter T A
         | let r := fresh in
           intros ? r; destruct r; reflexivity
         | let f := fresh in
           let r := fresh in
           intros f r; destruct r; compute; congruence ]
  end.
Hint Extern 1 (Setter _) => SetterInstance_t: typeclass_instances.
Hint Extern 1 (SetterWf _) => SetterWfInstance_t: typeclass_instances.
Module RecordSetNotations.
Delimit Scope record_set with rs.
Open Scope rs.
Notation "x <| proj  :=  v |>" := (set proj (constructor v) x)
  (at level 12, left associativity) : record_set.
Notation "x <| proj  ::=  f |>" := (set proj f x)
  (at level 12, f  at next level, left associativity) : record_set.
End RecordSetNotations.
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
