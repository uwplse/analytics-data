Class EqDec A :=
    equal : forall x y : A, {x = y} + {x <> y}.
Infix "==" := equal (at level 70, no associativity).
Hint Extern 2 (EqDec _) => (hnf; decide equality): typeclass_instances.
Instance unit_eqdec : (EqDec unit) := _.
Instance nat_eqdec : (EqDec nat) := _.
