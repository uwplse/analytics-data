From Coq Require Import ProofIrrelevance.
Class EqualDec A :=
    equal : forall x y : A, {x = y} + {x <> y}.
Module EqualDecNotation.
Infix "==" := equal (no associativity, at level 70).
End EqualDecNotation.
Instance unit_equal_dec : (EqualDec unit) :=
 (fun x y => left match x, y with
                  | tt, tt => eq_refl
                  end).
Instance nat_equal_dec : (EqualDec nat) := _.
Instance bool_equal_dec : (EqualDec bool) := _.
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
