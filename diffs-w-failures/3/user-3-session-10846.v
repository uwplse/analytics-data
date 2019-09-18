Time From stdpp Require Import tactics.
Time Set Default Proof Using "Type".
Time #[local]Set Universe Polymorphism.
Time Inductive tlist :=
       | tnil : tlist
       | tcons : Type \226\134\146 tlist \226\134\146 tlist.
Time
Inductive hlist : tlist \226\134\146 Type :=
  | hnil : hlist tnil
  | hcons : forall {A} {As}, A \226\134\146 hlist As \226\134\146 hlist (tcons A As).
Time
Fixpoint tapp (As Bs : tlist) : tlist :=
  match As with
  | tnil => Bs
  | tcons A As => tcons A (tapp As Bs)
  end.
Time
Fixpoint happ {As Bs} (xs : hlist As) (ys : hlist Bs) : 
hlist (tapp As Bs) :=
  match xs with
  | hnil => ys
  | hcons x xs => hcons x (happ xs ys)
  end.
Time
Fixpoint hhead {A As} (xs : hlist (tcons A As)) : A :=
  match xs with
  | hnil => ()
  | hcons x _ => x
  end.
Time
Fixpoint htail {A As} (xs : hlist (tcons A As)) : 
hlist As := match xs with
            | hnil => ()
            | hcons _ xs => xs
            end.
Time
Fixpoint hheads {As Bs} : hlist (tapp As Bs) \226\134\146 hlist As :=
  match As with
  | tnil => \206\187 _, hnil
  | tcons A As => \206\187 xs, hcons (hhead xs) (hheads (htail xs))
  end.
Time
Fixpoint htails {As Bs} : hlist (tapp As Bs) \226\134\146 hlist Bs :=
  match As with
  | tnil => id
  | tcons A As => \206\187 xs, htails (htail xs)
  end.
Time
Fixpoint himpl (As : tlist) (B : Type) : Type :=
  match As with
  | tnil => B
  | tcons A As => A \226\134\146 himpl As B
  end.
Time Definition hinit {B} (y : B) : himpl tnil B := y.
Time
Definition hlam {A} {As} {B} (f : A \226\134\146 himpl As B) : himpl (tcons A As) B := f.
Time Arguments hlam _ _ _ _ _ / : assert.
Time
Definition hcurry {As} {B} (f : himpl As B) (xs : hlist As) : B :=
  (fix go {As} xs :=
     match xs in (hlist As) return (himpl As B \226\134\146 B) with
     | hnil => \206\187 f, f
     | hcons x xs => \206\187 f, go xs (f x)
     end) _ xs f.
Time Coercion hcurry : himpl >-> Funclass.
Time
Fixpoint huncurry {As B} : (hlist As \226\134\146 B) \226\134\146 himpl As B :=
  match As with
  | tnil => \206\187 f, f hnil
  | tcons x xs => \206\187 f, hlam (\206\187 x, huncurry (f \226\136\152 hcons x))
  end.
Time
Lemma hcurry_uncurry {As} {B} (f : hlist As \226\134\146 B) xs : huncurry f xs = f xs.
Time Proof.
Time by induction xs as [| A As x xs IH]; simpl; rewrite ?IH.
Time Qed.
Time
Fixpoint hcompose {As B C} (f : B \226\134\146 C) {struct As} : 
himpl As B \226\134\146 himpl As C :=
  match As with
  | tnil => f
  | tcons A As => \206\187 g, hlam (\206\187 x, hcompose f (g x))
  end.
