Time From stdpp Require Export strings.
Time From iris.algebra Require Export base.
Time From Coq Require Export Ascii.
Time Set Default Proof Using "Type".
Time Inductive direction :=
       | Left : _
       | Right : _.
Time #[local]Notation "b1 && b2" := (if b1 then b2 else false) : bool_scope.
Time
Lemma lazy_andb_true (b1 b2 : bool) : b1 && b2 = true \226\134\148 b1 = true \226\136\167 b2 = true.
Time Proof.
Time (destruct b1, b2; intuition congruence).
Time Qed.
Time
Fixpoint Pos_succ (x : positive) : positive :=
  match x with
  | (p~1)%positive => ((Pos_succ p)~0)%positive
  | (p~0)%positive => (p~1)%positive
  | 1%positive => 2%positive
  end.
Time
Definition beq (b1 b2 : bool) : bool :=
  match b1, b2 with
  | false, false | true, true => true
  | _, _ => false
  end.
Time
Definition ascii_beq (x y : ascii) : bool :=
  let
  'Ascii x1 x2 x3 x4 x5 x6 x7 x8 := x in
   let
   'Ascii y1 y2 y3 y4 y5 y6 y7 y8 := y in
    beq x1 y1 && beq x2 y2 && beq x3 y3 && beq x4 y4 && beq x5 y5 &&
    beq x6 y6 && beq x7 y7 && beq x8 y8.
Time
Fixpoint string_beq (s1 s2 : string) : bool :=
  match s1, s2 with
  | "", "" => true
  | String a1 s1, String a2 s2 => ascii_beq a1 a2 && string_beq s1 s2
  | _, _ => false
  end.
Time Lemma beq_true b1 b2 : beq b1 b2 = true \226\134\148 b1 = b2.
Time Proof.
Time (destruct b1, b2; simpl; intuition congruence).
Time Qed.
Time Lemma ascii_beq_true x y : ascii_beq x y = true \226\134\148 x = y.
Time Proof.
Time (destruct x, y; rewrite /= !lazy_andb_true !beq_true).
Time intuition congruence.
Time Qed.
Time Lemma string_beq_true s1 s2 : string_beq s1 s2 = true \226\134\148 s1 = s2.
Time Proof.
Time revert s2.
Time
(<ssreflect_plugin::ssrtclintros@0> induction s1 as [| x s1 IH] =>- 
 [|y s2] //=).
Time rewrite lazy_andb_true ascii_beq_true IH.
Time intuition congruence.
Time Qed.
Time Lemma string_beq_reflect s1 s2 : reflect (s1 = s2) (string_beq s1 s2).
Time Proof.
Time (apply iff_reflect).
Time by rewrite string_beq_true.
Time Qed.
Time Module Export ident.
Time
Inductive ident :=
  | IAnon : positive \226\134\146 ident
  | INamed :> string \226\134\146 ident.
Time End ident.
Time
Instance maybe_IAnon : (Maybe IAnon) :=
 (\206\187 i, match i with
       | IAnon n => Some n
       | _ => None
       end).
Time
Instance maybe_INamed : (Maybe INamed) :=
 (\206\187 i, match i with
       | INamed s => Some s
       | _ => None
       end).
Time Instance beq_eq_dec : (EqDecision ident).
Time Proof.
Time solve_decision.
Time Defined.
Time Definition positive_beq := Eval compute in Pos.eqb.
Time Lemma positive_beq_true x y : positive_beq x y = true \226\134\148 x = y.
Time Proof.
Time (apply Pos.eqb_eq).
Time Qed.
Time
Definition ident_beq (i1 i2 : ident) : bool :=
  match i1, i2 with
  | IAnon n1, IAnon n2 => positive_beq n1 n2
  | INamed s1, INamed s2 => string_beq s1 s2
  | _, _ => false
  end.
Time Lemma ident_beq_true i1 i2 : ident_beq i1 i2 = true \226\134\148 i1 = i2.
Time Proof.
Time
(destruct i1, i2; rewrite /= ?string_beq_true ?positive_beq_true;
  naive_solver).
Time Qed.
Time Lemma ident_beq_reflect i1 i2 : reflect (i1 = i2) (ident_beq i1 i2).
Time Proof.
Time (apply iff_reflect).
Time by rewrite ident_beq_true.
Time Qed.
Time
Definition pm_option_bind {A} {B} (f : A \226\134\146 option B) 
  (mx : option A) : option B :=
  match mx with
  | Some x => f x
  | None => None
  end.
Time Arguments pm_option_bind {_} {_} _ !_ /.
Time
Definition pm_from_option {A} {B} (f : A \226\134\146 B) (y : B) 
  (mx : option A) : B := match mx with
                         | None => y
                         | Some x => f x
                         end.
Time Arguments pm_from_option {_} {_} _ _ !_ /.
Time
Definition pm_option_fun {A} {B} (f : option (A \226\134\146 B)) 
  (x : A) : option B :=
  match f with
  | None => None
  | Some f => Some (f x)
  end.
Time Arguments pm_option_fun {_} {_} !_ _ /.
Time Notation pm_default := (pm_from_option (\206\187 x, x)).
