Time From stdpp Require Export tactics.
Time Set Default Proof Using "Type".
Time
Inductive option_reflect {A} (P : A \226\134\146 Prop) (Q : Prop) : option A \226\134\146 Type :=
  | ReflectSome : forall x, P x \226\134\146 option_reflect P Q (Some x)
  | ReflectNone : Q \226\134\146 option_reflect P Q None.
Time Lemma None_ne_Some {A} (x : A) : None \226\137\160 Some x.
Time Proof.
Time congruence.
Time Qed.
Time Lemma Some_ne_None {A} (x : A) : Some x \226\137\160 None.
Time Proof.
Time congruence.
Time Qed.
Time Lemma eq_None_ne_Some {A} (mx : option A) x : mx = None \226\134\146 mx \226\137\160 Some x.
Time Proof.
Time congruence.
Time Qed.
Time Instance Some_inj  {A}: (Inj (=) (=) (@Some A)).
Time Proof.
Time congruence.
Time Qed.
Time
Definition from_option {A} {B} (f : A \226\134\146 B) (y : B) 
  (mx : option A) : B := match mx with
                         | None => y
                         | Some x => f x
                         end.
Time Instance: (Params (@from_option) 3) := { }.
Time Arguments from_option {_} {_} _ _ !_ / : assert.
Time Notation default := (from_option id).
Time
Lemma option_eq {A} (mx my : option A) :
  mx = my \226\134\148 (\226\136\128 x, mx = Some x \226\134\148 my = Some x).
Time Proof.
Time (split; [ by intros; by subst |  ]).
Time (destruct mx, my; naive_solver).
Time Qed.
Time
Lemma option_eq_1 {A} (mx my : option A) x :
  mx = my \226\134\146 mx = Some x \226\134\146 my = Some x.
Time Proof.
Time congruence.
Time Qed.
Time
Lemma option_eq_1_alt {A} (mx my : option A) x :
  mx = my \226\134\146 my = Some x \226\134\146 mx = Some x.
Time Proof.
Time congruence.
Time Qed.
Time Definition is_Some {A} (mx : option A) := \226\136\131 x, mx = Some x.
Time Instance: (Params (@is_Some) 1) := { }.
Time
Lemma is_Some_alt {A} (mx : option A) :
  is_Some mx \226\134\148 match mx with
               | Some _ => True
               | None => False
               end.
Time Proof.
Time (unfold is_Some).
Time (destruct mx; naive_solver).
Time Qed.
Time Lemma mk_is_Some {A} (mx : option A) x : mx = Some x \226\134\146 is_Some mx.
Time Proof.
Time (intros; red; subst; eauto).
Time Qed.
Time Hint Resolve mk_is_Some: core.
Time Lemma is_Some_None {A} : \194\172 is_Some (@None A).
Time Proof.
Time by destruct 1.
Time Qed.
Time Hint Resolve is_Some_None: core.
Time Lemma eq_None_not_Some {A} (mx : option A) : mx = None \226\134\148 \194\172 is_Some mx.
Time Proof.
Time (rewrite is_Some_alt; destruct mx; naive_solver).
Time Qed.
Time Lemma not_eq_None_Some {A} (mx : option A) : mx \226\137\160 None \226\134\148 is_Some mx.
Time Proof.
Time (rewrite is_Some_alt; destruct mx; naive_solver).
Time Qed.
Time Instance is_Some_pi  {A} (mx : option A): (ProofIrrel (is_Some mx)).
Time Proof.
Time
(set
  (P := fun mx : option A => match mx with
                             | Some _ => True
                             | _ => False
                             end)).
Time
(set
  (f :=
   fun mx =>
   match mx return (P mx \226\134\146 is_Some mx) with
   | Some _ => \206\187 _, ex_intro _ _ eq_refl
   | None => False_rect _
   end)).
Time
(set
  (g :=
   fun mx =>
   fun H : is_Some mx =>
   match H return (P mx) with
   | ex_intro _ _ p => eq_rect _ _ I _ (eq_sym p)
   end)).
Time (assert (f_g : \226\136\128 mx H, f mx (g mx H) = H) by by intros ? [? ?]; subst).
Time (intros p1 p2).
Time (rewrite <- (f_g _ p1), <- (f_g _ p2)).
Time by destruct mx, p1.
Time Qed.
Time
Instance is_Some_dec  {A} (mx : option A): (Decision (is_Some mx)) :=
 match mx with
 | Some x => left (ex_intro _ x eq_refl)
 | None => right is_Some_None
 end.
Time
Definition is_Some_proj {A} {mx : option A} : is_Some mx \226\134\146 A :=
  match mx with
  | Some x => \206\187 _, x
  | None => False_rect _ \226\136\152 is_Some_None
  end.
Time
Definition Some_dec {A} (mx : option A) : {x | mx = Some x} + {mx = None} :=
  match mx return ({x | mx = Some x} + {mx = None}) with
  | Some x => inleft (x \226\134\190 eq_refl _)
  | None => inright eq_refl
  end.
Time
Inductive option_Forall2 {A} {B} (R : A \226\134\146 B \226\134\146 Prop) :
option A \226\134\146 option B \226\134\146 Prop :=
  | Some_Forall2 : forall x y, R x y \226\134\146 option_Forall2 R (Some x) (Some y)
  | None_Forall2 : option_Forall2 R None None.
Time
Definition option_relation {A} {B} (R : A \226\134\146 B \226\134\146 Prop) 
  (P : A \226\134\146 Prop) (Q : B \226\134\146 Prop) (mx : option A) (my : option B) : Prop :=
  match mx, my with
  | Some x, Some y => R x y
  | Some x, None => P x
  | None, Some y => Q y
  | None, None => True
  end.
Time Section Forall2.
Time Context {A} (R : relation A).
Time #[global]
Instance option_Forall2_refl : (Reflexive R \226\134\146 Reflexive (option_Forall2 R)).
Time Proof.
Time (intros ? [?| ]; by constructor).
Time Qed.
Time #[global]
Instance option_Forall2_sym : (Symmetric R \226\134\146 Symmetric (option_Forall2 R)).
Time Proof.
Time (destruct 2; by constructor).
Time Qed.
Time #[global]
Instance option_Forall2_trans :
 (Transitive R \226\134\146 Transitive (option_Forall2 R)).
Time Proof.
Time (destruct 2; inversion_clear 1; constructor; etrans; eauto).
Time Qed.
Time #[global]
Instance option_Forall2_equiv :
 (Equivalence R \226\134\146 Equivalence (option_Forall2 R)).
Time Proof.
Time (destruct 1; split; apply _).
Time Qed.
Time End Forall2.
Time
Instance option_equiv  `{Equiv A}: (Equiv (option A)) := (option_Forall2 (\226\137\161)).
Time Section setoids.
Time Context `{Equiv A}.
Time Implicit Types mx my : option A.
Time Lemma equiv_option_Forall2 mx my : mx \226\137\161 my \226\134\148 option_Forall2 (\226\137\161) mx my.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance option_equivalence :
 (Equivalence (\226\137\161@{A} ) \226\134\146 Equivalence (\226\137\161@{option A} )).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance Some_proper : (Proper ((\226\137\161) ==> (\226\137\161@{option A} )) Some).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance Some_equiv_inj : (Inj (\226\137\161) (\226\137\161@{option A} ) Some).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time #[global]
Instance option_leibniz  `{!LeibnizEquiv A}: (LeibnizEquiv (option A)).
Time Proof.
Time (intros x y; destruct 1; f_equal; by apply leibniz_equiv).
Time Qed.
Time Lemma equiv_None mx : mx \226\137\161 None \226\134\148 mx = None.
Time Proof.
Time (split; [ by inversion_clear 1 | intros ->; constructor ]).
Time Qed.
Time
Lemma equiv_Some_inv_l mx my x :
  mx \226\137\161 my \226\134\146 mx = Some x \226\134\146 \226\136\131 y, my = Some y \226\136\167 x \226\137\161 y.
Time Proof.
Time (destruct 1; naive_solver).
Time Qed.
Time
Lemma equiv_Some_inv_r mx my y :
  mx \226\137\161 my \226\134\146 my = Some y \226\134\146 \226\136\131 x, mx = Some x \226\136\167 x \226\137\161 y.
Time Proof.
Time (destruct 1; naive_solver).
Time Qed.
Time
Lemma equiv_Some_inv_l' my x : Some x \226\137\161 my \226\134\146 \226\136\131 x', Some x' = my \226\136\167 x \226\137\161 x'.
Time Proof.
Time (intros ?%(equiv_Some_inv_l _ _ x); naive_solver).
Time Qed.
Time
Lemma equiv_Some_inv_r' `{!Equivalence (\226\137\161@{A} )} mx 
  y : mx \226\137\161 Some y \226\134\146 \226\136\131 y', mx = Some y' \226\136\167 y \226\137\161 y'.
Time Proof.
Time (intros ?%(equiv_Some_inv_r _ _ y); naive_solver).
Time Qed.
Time #[global]
Instance is_Some_proper : (Proper ((\226\137\161@{option A} ) ==> iff) is_Some).
Time Proof.
Time (inversion_clear 1; split; eauto).
Time Qed.
Time #[global]
Instance from_option_proper  {B} (R : relation B) 
 (f : A \226\134\146 B):
 (Proper ((\226\137\161) ==> R) f \226\134\146 Proper (R ==> (\226\137\161) ==> R) (from_option f)).
Time Proof.
Time (destruct 3; simpl; auto).
Time Qed.
Time End setoids.
Time Typeclasses Opaque option_equiv.
Time
Instance option_eq_None_dec  {A} (mx : option A): 
 (Decision (mx = None)) :=
 match mx with
 | Some _ => right (Some_ne_None _)
 | None => left eq_refl
 end.
Time
Instance option_None_eq_dec  {A} (mx : option A): 
 (Decision (None = mx)) :=
 match mx with
 | Some _ => right (None_ne_Some _)
 | None => left eq_refl
 end.
Time Instance option_eq_dec  `{dec : EqDecision A}: (EqDecision (option A)).
Time Proof.
Time
(refine
  (\206\187 mx my,
     match mx, my with
     | Some x, Some y => cast_if (decide (x = y))
     | None, None => left _
     | _, _ => right _
     end); clear dec; abstract congruence).
Time Defined.
Time Instance option_ret : (MRet option) := @Some.
Time
Instance option_bind : (MBind option) :=
 (\206\187 A B f mx, match mx with
              | Some x => f x
              | None => None
              end).
Time
Instance option_join : (MJoin option) :=
 (\206\187 A mmx, match mmx with
           | Some mx => mx
           | None => None
           end).
Time Instance option_fmap : (FMap option) := @option_map.
Time
Instance option_guard : (MGuard option) :=
 (\206\187 P dec A f, match dec with
               | left H => f H
               | _ => None
               end).
Time
Lemma fmap_is_Some {A} {B} (f : A \226\134\146 B) mx : is_Some (f <$> mx) \226\134\148 is_Some mx.
Time Proof.
Time (unfold is_Some; destruct mx; naive_solver).
Time Qed.
Time
Lemma fmap_Some {A} {B} (f : A \226\134\146 B) mx y :
  f <$> mx = Some y \226\134\148 (\226\136\131 x, mx = Some x \226\136\167 y = f x).
Time Proof.
Time (destruct mx; naive_solver).
Time Qed.
Time
Lemma fmap_Some_1 {A} {B} (f : A \226\134\146 B) mx y :
  f <$> mx = Some y \226\134\146 \226\136\131 x, mx = Some x \226\136\167 y = f x.
Time Proof.
Time (apply fmap_Some).
Time Qed.
Time
Lemma fmap_Some_2 {A} {B} (f : A \226\134\146 B) mx x :
  mx = Some x \226\134\146 f <$> mx = Some (f x).
Time Proof.
Time (intros).
Time (apply fmap_Some; eauto).
Time Qed.
Time
Lemma fmap_Some_equiv {A} {B} `{Equiv B} `{!Equivalence (\226\137\161@{B} )} 
  (f : A \226\134\146 B) mx y : f <$> mx \226\137\161 Some y \226\134\148 (\226\136\131 x, mx = Some x \226\136\167 y \226\137\161 f x).
Time Proof.
Time (destruct mx; simpl; split).
Time -
Time (intros ?%Some_equiv_inj).
Time eauto.
Time -
Time (intros (?, (->%Some_inj, ?))).
Time constructor.
Time done.
Time -
Time (intros ?%equiv_None%symmetry).
Time done.
Time -
Time (intros (?, (?, ?))).
Time done.
Time Qed.
Time
Lemma fmap_Some_equiv_1 {A} {B} `{Equiv B} `{!Equivalence (\226\137\161@{B} )}
  (f : A \226\134\146 B) mx y : f <$> mx \226\137\161 Some y \226\134\146 \226\136\131 x, mx = Some x \226\136\167 y \226\137\161 f x.
Time Proof.
Time by rewrite fmap_Some_equiv.
Time Qed.
Time Lemma fmap_None {A} {B} (f : A \226\134\146 B) mx : f <$> mx = None \226\134\148 mx = None.
Time Proof.
Time by destruct mx.
Time Qed.
Time Lemma option_fmap_id {A} (mx : option A) : id <$> mx = mx.
Time Proof.
Time by destruct mx.
Time Qed.
Time
Lemma option_fmap_compose {A} {B} (f : A \226\134\146 B) {C} 
  (g : B \226\134\146 C) mx : g \226\136\152 f <$> mx = g <$> (f <$> mx).
Time Proof.
Time by destruct mx.
Time Qed.
Time
Lemma option_fmap_ext {A} {B} (f g : A \226\134\146 B) mx :
  (\226\136\128 x, f x = g x) \226\134\146 f <$> mx = g <$> mx.
Time Proof.
Time (intros; destruct mx; f_equal /=; auto).
Time Qed.
Time
Lemma option_fmap_equiv_ext `{Equiv A} `{Equiv B} 
  (f g : A \226\134\146 B) (mx : option A) : (\226\136\128 x, f x \226\137\161 g x) \226\134\146 f <$> mx \226\137\161 g <$> mx.
Time Proof.
Time (destruct mx; constructor; auto).
Time Qed.
Time
Lemma option_fmap_bind {A} {B} {C} (f : A \226\134\146 B) (g : B \226\134\146 option C) 
  mx : (f <$> mx) \226\137\171= g = mx \226\137\171= g \226\136\152 f.
Time Proof.
Time by destruct mx.
Time Qed.
Time
Lemma option_bind_assoc {A} {B} {C} (f : A \226\134\146 option B) 
  (g : B \226\134\146 option C) (mx : option A) : (mx \226\137\171= f) \226\137\171= g = mx \226\137\171= mbind g \226\136\152 f.
Time Proof.
Time by destruct mx; simpl.
Time Qed.
Time
Lemma option_bind_ext {A} {B} (f g : A \226\134\146 option B) 
  mx my : (\226\136\128 x, f x = g x) \226\134\146 mx = my \226\134\146 mx \226\137\171= f = my \226\137\171= g.
Time Proof.
Time (destruct mx, my; naive_solver).
Time Qed.
Time
Lemma option_bind_ext_fun {A} {B} (f g : A \226\134\146 option B) 
  mx : (\226\136\128 x, f x = g x) \226\134\146 mx \226\137\171= f = mx \226\137\171= g.
Time Proof.
Time (intros).
Time by apply option_bind_ext.
Time Qed.
Time
Lemma bind_Some {A} {B} (f : A \226\134\146 option B) (mx : option A) 
  y : mx \226\137\171= f = Some y \226\134\148 (\226\136\131 x, mx = Some x \226\136\167 f x = Some y).
Time Proof.
Time (destruct mx; naive_solver).
Time Qed.
Time
Lemma bind_None {A} {B} (f : A \226\134\146 option B) (mx : option A) :
  mx \226\137\171= f = None \226\134\148 mx = None \226\136\168 (\226\136\131 x, mx = Some x \226\136\167 f x = None).
Time Proof.
Time (destruct mx; naive_solver).
Time Qed.
Time Lemma bind_with_Some {A} (mx : option A) : mx \226\137\171= Some = mx.
Time Proof.
Time by destruct mx.
Time Qed.
Time
Instance option_fmap_proper  `{Equiv A} `{Equiv B}:
 (Proper (((\226\137\161) ==> (\226\137\161)) ==> (\226\137\161@{option A} ) ==> (\226\137\161@{option B} )) fmap).
Time Proof.
Time (destruct 2; constructor; auto).
Time Qed.
Time
Instance option_mbind_proper  `{Equiv A} `{Equiv B}:
 (Proper (((\226\137\161) ==> (\226\137\161)) ==> (\226\137\161@{option A} ) ==> (\226\137\161@{option B} )) mbind).
Time Proof.
Time (destruct 2; simpl; try constructor; auto).
Time Qed.
Time
Instance option_mjoin_proper  `{Equiv A}:
 (Proper ((\226\137\161) ==> (\226\137\161@{option (option A)} )) mjoin).
Time Proof.
Time (destruct 1 as [? ? []| ]; simpl; by constructor).
Time Qed.
Time Class Maybe {A B : Type} (c : A \226\134\146 B) :=
         maybe : B \226\134\146 option A.
Time Arguments maybe {_} {_} _ {_} !_ / : assert.
Time
Class Maybe2 {A1 A2 B : Type} (c : A1 \226\134\146 A2 \226\134\146 B) :=
    maybe2 : B \226\134\146 option (A1 * A2).
Time Arguments maybe2 {_} {_} {_} _ {_} !_ / : assert.
Time
Class Maybe3 {A1 A2 A3 B : Type} (c : A1 \226\134\146 A2 \226\134\146 A3 \226\134\146 B) :=
    maybe3 : B \226\134\146 option (A1 * A2 * A3).
Time Arguments maybe3 {_} {_} {_} {_} _ {_} !_ / : assert.
Time
Class Maybe4 {A1 A2 A3 A4 B : Type} (c : A1 \226\134\146 A2 \226\134\146 A3 \226\134\146 A4 \226\134\146 B) :=
    maybe4 : B \226\134\146 option (A1 * A2 * A3 * A4).
Time Arguments maybe4 {_} {_} {_} {_} {_} _ {_} !_ / : assert.
Time
Instance maybe_comp  `{Maybe B C c1} `{Maybe A B c2}: 
 (Maybe (c1 \226\136\152 c2)) := (\206\187 x, maybe c1 x \226\137\171= maybe c2).
Time Arguments maybe_comp _ _ _ _ _ _ _ !_ / : assert.
Time
Instance maybe_inl  {A} {B}: (Maybe (@inl A B)) :=
 (\206\187 xy, match xy with
        | inl x => Some x
        | _ => None
        end).
Time
Instance maybe_inr  {A} {B}: (Maybe (@inr A B)) :=
 (\206\187 xy, match xy with
        | inr y => Some y
        | _ => None
        end).
Time Instance maybe_Some  {A}: (Maybe (@Some A)) := id.
Time Arguments maybe_Some _ !_ / : assert.
Time
Instance option_union_with  {A}: (UnionWith A (option A)) :=
 (\206\187 f mx my,
    match mx, my with
    | Some x, Some y => f x y
    | Some x, None => Some x
    | None, Some y => Some y
    | None, None => None
    end).
Time
Instance option_intersection_with  {A}: (IntersectionWith A (option A)) :=
 (\206\187 f mx my, match mx, my with
             | Some x, Some y => f x y
             | _, _ => None
             end).
Time
Instance option_difference_with  {A}: (DifferenceWith A (option A)) :=
 (\206\187 f mx my,
    match mx, my with
    | Some x, Some y => f x y
    | Some x, None => Some x
    | None, _ => None
    end).
Time
Instance option_union  {A}: (Union (option A)) :=
 (union_with (\206\187 x _, Some x)).
Time
Lemma option_union_Some {A} (mx my : option A) z :
  mx \226\136\170 my = Some z \226\134\146 mx = Some z \226\136\168 my = Some z.
Time Proof.
Time (destruct mx, my; naive_solver).
Time Qed.
Time
Class DiagNone {A} {B} {C} (f : option A \226\134\146 option B \226\134\146 option C) :=
    diag_none : f None None = None.
Time Section union_intersection_difference.
Time Context {A} (f : A \226\134\146 A \226\134\146 option A).
Time #[global]Instance union_with_diag_none : (DiagNone (union_with f)).
Time Proof.
Time reflexivity.
Time Qed.
Time #[global]
Instance intersection_with_diag_none : (DiagNone (intersection_with f)).
Time Proof.
Time reflexivity.
Time Qed.
Time #[global]
Instance difference_with_diag_none : (DiagNone (difference_with f)).
Time Proof.
Time reflexivity.
Time Qed.
Time #[global]Instance union_with_left_id : (LeftId (=) None (union_with f)).
Time Proof.
Time by intros [?| ].
Time Qed.
Time #[global]
Instance union_with_right_id : (RightId (=) None (union_with f)).
Time Proof.
Time by intros [?| ].
Time Qed.
Time #[global]
Instance union_with_comm : (Comm (=) f \226\134\146 Comm (=@{option A} ) (union_with f)).
Time Proof.
Time by intros ? [?| ] [?| ]; compute; rewrite 1?(comm f).
Time Qed.
Time #[global]
Instance intersection_with_left_ab :
 (LeftAbsorb (=) None (intersection_with f)).
Time Proof.
Time by intros [?| ].
Time Qed.
Time #[global]
Instance intersection_with_right_ab :
 (RightAbsorb (=) None (intersection_with f)).
Time Proof.
Time by intros [?| ].
Time Qed.
Time #[global]
Instance difference_with_comm :
 (Comm (=) f \226\134\146 Comm (=@{option A} ) (intersection_with f)).
Time Proof.
Time by intros ? [?| ] [?| ]; compute; rewrite 1?(comm f).
Time Qed.
Time #[global]
Instance difference_with_right_id : (RightId (=) None (difference_with f)).
Time Proof.
Time by intros [?| ].
Time Qed.
Time End union_intersection_difference.
Time
Tactic Notation "case_option_guard" "as" ident(Hx) :=
 (match goal with
  | H:context C[ @mguard option _ ?P ?dec ]
    |- _ =>
        change_no_check (@mguard option _ P dec) with
         (\206\187 A (f : P \226\134\146 option A),
            match @decide P dec with
            | left H' => f H'
            | _ => None
            end) in *; destruct_decide @decide P dec as Hx
  | |- context C[ @mguard option _ ?P ?dec ] =>
        change_no_check (@mguard option _ P dec) with
         (\206\187 A (f : P \226\134\146 option A),
            match @decide P dec with
            | left H' => f H'
            | _ => None
            end) in *; destruct_decide @decide P dec as Hx
  end).
Time
Tactic Notation "case_option_guard" :=
 (let H := fresh in
  case_option_guard
  as
  H).
Time
Lemma option_guard_True {A} P `{Decision P} (mx : option A) :
  P \226\134\146 guard P; mx = mx.
Time Proof.
Time (intros).
Time by case_option_guard.
Time Qed.
Time
Lemma option_guard_False {A} P `{Decision P} (mx : option A) :
  \194\172 P \226\134\146 guard P; mx = None.
Time Proof.
Time (intros).
Time by case_option_guard.
Time Qed.
Time
Lemma option_guard_iff {A} P Q `{Decision P} `{Decision Q} 
  (mx : option A) : P \226\134\148 Q \226\134\146 guard P; mx = guard Q; mx.
Time Proof.
Time (intros [? ?]).
Time (repeat case_option_guard; intuition).
Time Qed.
Time
Tactic Notation "simpl_option" "by" tactic3(tac) :=
 (let assert_Some_None A mx H := first
  [ let x := fresh in
    evar ( x : A );
     (let x' := eval unfold x in x in
      clear x; assert (H : mx = Some x') by tac)
  | assert (H : mx = None) by tac ]
  in
  repeat
   match goal with
   | H:context [ @mret _ _ ?A ]
     |- _ => change_no_check (@mret _ _ A) with (@Some A) in H
   | |- context [ @mret _ _ ?A ] =>
         change_no_check (@mret _ _ A) with (@Some A)
   | H:context [ mbind (M:=option) (A:=?A) ?f ?mx ]
     |- _ =>
         let Hx := fresh in
         assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
   | H:context [ fmap (M:=option) (A:=?A) ?f ?mx ]
     |- _ =>
         let Hx := fresh in
         assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
   | H:context [ from_option (A:=?A) _ _ ?mx ]
     |- _ =>
         let Hx := fresh in
         assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
   | H:context [ match ?mx with
                 | _ => _
                 end ]
     |- _ =>
         match type of mx with
         | option ?A =>
             let Hx := fresh in
             assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
         end
   | |- context [ mbind (M:=option) (A:=?A) ?f ?mx ] =>
         let Hx := fresh in
         assert_Some_None A mx Hx; rewrite Hx; clear Hx
   | |- context [ fmap (M:=option) (A:=?A) ?f ?mx ] =>
         let Hx := fresh in
         assert_Some_None A mx Hx; rewrite Hx; clear Hx
   | |- context [ from_option (A:=?A) _ _ ?mx ] =>
         let Hx := fresh in
         assert_Some_None A mx Hx; rewrite Hx; clear Hx
   | |- context [ match ?mx with
                  | _ => _
                  end ] =>
         match type of mx with
         | option ?A =>
             let Hx := fresh in
             assert_Some_None A mx Hx; rewrite Hx; clear Hx
         end
   | H:context [ decide _ ] |- _ => rewrite decide_True in H by tac
   | H:context [ decide _ ] |- _ => rewrite decide_False in H by tac
   | H:context [ mguard _ _ ] |- _ => rewrite option_guard_False in H by tac
   | H:context [ mguard _ _ ] |- _ => rewrite option_guard_True in H by tac
   | _ => rewrite decide_True by tac
   | _ => rewrite decide_False by tac
   | _ => rewrite option_guard_True by tac
   | _ =>
       rewrite option_guard_False by tac
   | H:context [ None \226\136\170 _ ] |- _ => rewrite (left_id_L None (\226\136\170)) in H
   | H:context [ _ \226\136\170 None ] |- _ => rewrite (right_id_L None (\226\136\170)) in H
   | |- context [ None \226\136\170 _ ] => rewrite (left_id_L None (\226\136\170))
   | |- context [ _ \226\136\170 None ] => rewrite (right_id_L None (\226\136\170))
   end).
Time
Tactic Notation "simplify_option_eq" "by" tactic3(tac) :=
 (repeat
   match goal with
   | _ => progress simplify_eq /=
   | _ =>
       progress simpl_option by tac
   | _:maybe _ ?x = Some _ |- _ => is_var x; destruct x
   | _:maybe2 _ ?x = Some _ |- _ => is_var x; destruct x
   | _:maybe3 _ ?x = Some _ |- _ => is_var x; destruct x
   | _:maybe4 _ ?x = Some _ |- _ => is_var x; destruct x
   | H:_ \226\136\170 _ = Some _ |- _ => apply option_union_Some in H; destruct H
   | H:mbind (M:=option) ?f ?mx = ?my
     |- _ =>
         match mx with
         | Some _ => fail 1
         | None => fail 1
         | _ => idtac
         end; match my with
              | Some _ => idtac
              | None => idtac
              | _ => fail 1
              end;
          (let x := fresh in
           destruct mx as [x| ] eqn:?;
            [ change_no_check (f x = my) in H
            | change_no_check (None = my) in H ])
   | H:?my = mbind (M:=option) ?f ?mx
     |- _ =>
         match mx with
         | Some _ => fail 1
         | None => fail 1
         | _ => idtac
         end; match my with
              | Some _ => idtac
              | None => idtac
              | _ => fail 1
              end;
          (let x := fresh in
           destruct mx as [x| ] eqn:?;
            [ change_no_check (my = f x) in H
            | change_no_check (my = None) in H ])
   | H:fmap (M:=option) ?f ?mx = ?my
     |- _ =>
         match mx with
         | Some _ => fail 1
         | None => fail 1
         | _ => idtac
         end; match my with
              | Some _ => idtac
              | None => idtac
              | _ => fail 1
              end;
          (let x := fresh in
           destruct mx as [x| ] eqn:?;
            [ change_no_check (Some (f x) = my) in H
            | change_no_check (None = my) in H ])
   | H:?my = fmap (M:=option) ?f ?mx
     |- _ =>
         match mx with
         | Some _ => fail 1
         | None => fail 1
         | _ => idtac
         end; match my with
              | Some _ => idtac
              | None => idtac
              | _ => fail 1
              end;
          (let x := fresh in
           destruct mx as [x| ] eqn:?;
            [ change_no_check (my = Some (f x)) in H
            | change_no_check (my = None) in H ])
   | _ => progress case_decide
   | _ => progress case_option_guard
   end).
Time Tactic Notation "simplify_option_eq" := simplify_option_eq by eauto.
