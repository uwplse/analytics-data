Time From iris.bi Require Export derived_laws_bi.
Time From iris.algebra Require Import monoid.
Time Module bi.
Time Import interface.bi.
Time Import derived_laws_bi.bi.
Time Section sbi_derived.
Time Context {PROP : sbi}.
Time Implicit Type \207\134 : Prop.
Time Implicit Types P Q R : PROP.
Time Implicit Type Ps : list PROP.
Time Implicit Type A : Type.
Time Notation "P \226\138\162 Q" := (P \226\138\162@{ PROP} Q).
Time Notation "P \226\138\163\226\138\162 Q" := (P \226\138\163\226\138\162@{ PROP} Q).
Time
Hint Resolve or_elim or_intro_l' or_intro_r' True_intro False_elim: core.
Time Hint Resolve and_elim_l' and_elim_r' and_intro forall_intro: core.
Time #[global]
Instance internal_eq_proper  (A : ofeT):
 (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\138\163\226\138\162)) (@sbi_internal_eq PROP A)) := 
 (ne_proper_2 _).
Time #[global]
Instance later_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@sbi_later PROP)) :=
 (ne_proper _).
Time Hint Resolve internal_eq_refl: core.
Time Hint Extern 100 (NonExpansive _) => solve_proper: core.
Time Lemma equiv_internal_eq {A : ofeT} P (a b : A) : a \226\137\161 b \226\134\146 P \226\138\162 a \226\137\161 b.
Time Proof.
Time (intros ->).
Time auto.
Time Qed.
Time
Lemma internal_eq_rewrite' {A : ofeT} a b (\206\168 : A \226\134\146 PROP) 
  P {H\206\168 : NonExpansive \206\168} : (P \226\138\162 a \226\137\161 b) \226\134\146 (P \226\138\162 \206\168 a) \226\134\146 P \226\138\162 \206\168 b.
Time Proof.
Time (intros Heq H\206\168a).
Time rewrite -(idemp bi_and P) {+1}Heq H\206\168a.
Time (apply impl_elim_l').
Time by apply internal_eq_rewrite.
Time Qed.
Time Lemma internal_eq_sym {A : ofeT} (a b : A) : a \226\137\161 b \226\138\162 b \226\137\161 a.
Time Proof.
Time (apply (internal_eq_rewrite' a b (\206\187 b, b \226\137\161 a)%I); auto).
Time Qed.
Time Lemma internal_eq_iff P Q : P \226\137\161 Q \226\138\162 P \226\134\148 Q.
Time Proof.
Time (apply (internal_eq_rewrite' P Q (\206\187 Q, P \226\134\148 Q))%I; auto using iff_refl).
Time Qed.
Time
Lemma f_equiv {A B : ofeT} (f : A \226\134\146 B) `{!NonExpansive f} 
  x y : x \226\137\161 y \226\138\162 f x \226\137\161 f y.
Time Proof.
Time (apply (internal_eq_rewrite' x y (\206\187 y, f x \226\137\161 f y)%I); auto).
Time Qed.
Time
Lemma prod_equivI {A B : ofeT} (x y : A * B) : x \226\137\161 y \226\138\163\226\138\162 x.1 \226\137\161 y.1 \226\136\167 x.2 \226\137\161 y.2.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (apply and_intro; apply f_equiv; apply _).
Time -
Time rewrite {+3}(surjective_pairing x) {+3}(surjective_pairing y).
Time
(apply (internal_eq_rewrite' x.1 y.1 (\206\187 a, (x.1, x.2) \226\137\161 (a, y.2))%I); auto).
Time
(apply (internal_eq_rewrite' x.2 y.2 (\206\187 b, (x.1, x.2) \226\137\161 (x.1, b))%I); auto).
Time Qed.
Time
Lemma sum_equivI {A B : ofeT} (x y : A + B) :
  x \226\137\161 y
  \226\138\163\226\138\162 match x, y with
     | inl a, inl a' => a \226\137\161 a'
     | inr b, inr b' => b \226\137\161 b'
     | _, _ => False
     end.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time
(apply
  (internal_eq_rewrite' x y
     (\206\187 y,
        match x, y with
        | inl a, inl a' => a \226\137\161 a'
        | inr b, inr b' => b \226\137\161 b'
        | _, _ => False
        end)%I); auto).
Time (destruct x; auto).
Time -
Time (destruct x as [a| b], y as [a'| b']; auto; apply f_equiv, _).
Time Qed.
Time
Lemma option_equivI {A : ofeT} (x y : option A) :
  x \226\137\161 y
  \226\138\163\226\138\162 match x, y with
     | Some a, Some a' => a \226\137\161 a'
     | None, None => True
     | _, _ => False
     end.
Time Proof.
Time (apply (anti_symm _)).
Time -
Time
(apply
  (internal_eq_rewrite' x y
     (\206\187 y,
        match x, y with
        | Some a, Some a' => a \226\137\161 a'
        | None, None => True
        | _, _ => False
        end)%I); auto).
Time (destruct x; auto).
Time -
Time (destruct x as [a| ], y as [a'| ]; auto).
Time (apply f_equiv, _).
Time Qed.
Time
Lemma sig_equivI {A : ofeT} (P : A \226\134\146 Prop) (x y : sig P) : `x \226\137\161 `y \226\138\163\226\138\162 x \226\137\161 y.
Time Proof.
Time (apply (anti_symm _)).
Time (apply sig_eq).
Time (apply f_equiv, _).
Time Qed.
Time Section sigT_equivI.
Time Import EqNotations.
Time
Lemma sigT_equivI {A : Type} {P : A \226\134\146 ofeT} (x y : sigT P) :
  x \226\137\161 y \226\138\163\226\138\162 (\226\136\131 eq : projT1 x = projT1 y, rew eq in projT2 x \226\137\161 projT2 y).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time
(apply
  (internal_eq_rewrite' x y
     (\206\187 y, \226\136\131 eq : projT1 x = projT1 y, rew eq in projT2 x \226\137\161 projT2 y))%I;
  [  | done | exact : {}(exist_intro' _ _ eq_refl) {} ]).
Time
(move  {}=>n [a pa] [b pb] [/=]; <ssreflect_plugin::ssrtclintros@0> 
  intros -> =>/= Hab).
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_ne =>?).
Time by rewrite Hab.
Time -
Time (apply exist_elim).
Time move : {}x {}y {} =>[a pa] [b pb] /=.
Time (intros ->; simpl).
Time (apply f_equiv, _).
Time Qed.
Time End sigT_equivI.
Time
Lemma discrete_fun_equivI {A} {B : A \226\134\146 ofeT} (f g : discrete_fun B) :
  f \226\137\161 g \226\138\163\226\138\162 (\226\136\128 x, f x \226\137\161 g x).
Time Proof.
Time (apply (anti_symm _); auto using fun_ext).
Time (apply (internal_eq_rewrite' f g (\206\187 g, \226\136\128 x : A, f x \226\137\161 g x)%I); auto).
Time
(intros n h h' Hh; <ssreflect_plugin::ssrtclintros@0> apply forall_ne =>x;
  apply internal_eq_ne; auto).
Time Qed.
Time
Lemma ofe_morO_equivI {A B : ofeT} (f g : A -n> B) :
  f \226\137\161 g \226\138\163\226\138\162 (\226\136\128 x, f x \226\137\161 g x).
Time Proof.
Time (apply (anti_symm _)).
Time -
Time (apply (internal_eq_rewrite' f g (\206\187 g, \226\136\128 x : A, f x \226\137\161 g x)%I); auto).
Time -
Time rewrite -(discrete_fun_equivI (ofe_mor_car _ _ f) (ofe_mor_car _ _ g)).
Time
(set
  (h1 :=
   fun f : A -n> B =>
   exist (\206\187 f : A -d> B, NonExpansive (f : A \226\134\146 B)) f (ofe_mor_ne A B f))).
Time
(set
  (h2 :=
   fun f : sigO (\206\187 f : A -d> B, NonExpansive (f : A \226\134\146 B)) =>
   @OfeMor A B (`f) (proj2_sig f))).
Time (assert (Hh : \226\136\128 f, h2 (h1 f) = f) by by intros []).
Time (assert (NonExpansive h2) by (intros ? ? ? EQ; apply EQ)).
Time by rewrite -{+2}[f]Hh -{+2}[g]Hh -f_equiv -sig_equivI.
Time Qed.
Time Lemma pure_internal_eq {A : ofeT} (x y : A) : \226\140\156x \226\137\161 y\226\140\157 \226\138\162 x \226\137\161 y.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim' =>{+}->).
Time (apply internal_eq_refl).
Time Qed.
Time Lemma discrete_eq {A : ofeT} (a b : A) : Discrete a \226\134\146 a \226\137\161 b \226\138\163\226\138\162 \226\140\156a \226\137\161 b\226\140\157.
Time Proof.
Time (intros).
Time (apply (anti_symm _); auto using discrete_eq_1, pure_internal_eq).
Time Qed.
Time
Lemma absorbingly_internal_eq {A : ofeT} (x y : A) :
  <absorb> (x \226\137\161 y) \226\138\163\226\138\162 x \226\137\161 y.
Time Proof.
Time (apply (anti_symm _), absorbingly_intro).
Time
(apply wand_elim_r', (internal_eq_rewrite' x y (\206\187 y, True -\226\136\151 x \226\137\161 y)%I); auto).
Time (apply wand_intro_l, internal_eq_refl).
Time Qed.
Time
Lemma persistently_internal_eq {A : ofeT} (a b : A) : <pers> (a \226\137\161 b) \226\138\163\226\138\162 a \226\137\161 b.
Time Proof.
Time (apply (anti_symm (\226\138\162))).
Time {
Time by rewrite persistently_into_absorbingly absorbingly_internal_eq.
Time }
Time (apply (internal_eq_rewrite' a b (\206\187 b, <pers> (a \226\137\161 b))%I); auto).
Time rewrite -(internal_eq_refl emp%I a).
Time (apply persistently_emp_intro).
Time Qed.
Time #[global]
Instance internal_eq_absorbing  {A : ofeT} (x y : A):
 (Absorbing (PROP:=PROP) (x \226\137\161 y)).
Time Proof.
Time by rewrite /Absorbing absorbingly_internal_eq.
Time Qed.
Time #[global]
Instance internal_eq_persistent  {A : ofeT} (a b : A):
 (Persistent (PROP:=PROP) (a \226\137\161 b)).
Time Proof.
Time by intros; rewrite /Persistent persistently_internal_eq.
Time Qed.
Time
Lemma internal_eq_rewrite_contractive {A : ofeT} a 
  b (\206\168 : A \226\134\146 PROP) {H\206\168 : Contractive \206\168} : \226\150\183 (a \226\137\161 b) \226\138\162 \206\168 a \226\134\146 \206\168 b.
Time Proof.
Time rewrite later_eq_2.
Time move : {}H\206\168 {} =>/contractive_alt [g [? H\206\168]].
Time rewrite !H\206\168.
Time by apply internal_eq_rewrite.
Time Qed.
Time
Lemma internal_eq_rewrite_contractive' {A : ofeT} 
  a b (\206\168 : A \226\134\146 PROP) P {H\206\168 : Contractive \206\168} :
  (P \226\138\162 \226\150\183 (a \226\137\161 b)) \226\134\146 (P \226\138\162 \206\168 a) \226\134\146 P \226\138\162 \206\168 b.
Time Proof.
Time rewrite later_eq_2.
Time move : {}H\206\168 {} =>/contractive_alt [g [? H\206\168]].
Time rewrite !H\206\168.
Time by apply internal_eq_rewrite'.
Time Qed.
Time Lemma later_equivI {A : ofeT} (x y : A) : Next x \226\137\161 Next y \226\138\163\226\138\162 \226\150\183 (x \226\137\161 y).
Time Proof.
Time (apply (anti_symm _); auto using later_eq_1, later_eq_2).
Time Qed.
Time Hint Resolve later_mono: core.
Time #[global]
Instance later_mono' : (Proper ((\226\138\162) ==> (\226\138\162)) (@sbi_later PROP)).
Time Proof.
Time (intros P Q; apply later_mono).
Time Qed.
Time #[global]
Instance later_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@sbi_later PROP)).
Time Proof.
Time (intros P Q; apply later_mono).
Time Qed.
Time Lemma later_True : \226\150\183 True \226\138\163\226\138\162 True.
Time Proof.
Time (apply (anti_symm (\226\138\162)); auto using later_intro).
Time Qed.
Time Lemma later_emp `{!BiAffine PROP} : \226\150\183 emp \226\138\163\226\138\162 emp.
Time Proof.
Time by rewrite -True_emp later_True.
Time Qed.
Time Lemma later_forall {A} (\206\166 : A \226\134\146 PROP) : \226\150\183 (\226\136\128 a, \206\166 a) \226\138\163\226\138\162 (\226\136\128 a, \226\150\183 \206\166 a).
Time Proof.
Time (apply (anti_symm _); auto using later_forall_2).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time by rewrite (forall_elim x).
Time Qed.
Time Lemma later_exist_2 {A} (\206\166 : A \226\134\146 PROP) : (\226\136\131 a, \226\150\183 \206\166 a) \226\138\162 \226\150\183 (\226\136\131 a, \206\166 a).
Time Proof.
Time (apply exist_elim; eauto using exist_intro).
Time Qed.
Time
Lemma later_exist `{Inhabited A} (\206\166 : A \226\134\146 PROP) :
  \226\150\183 (\226\136\131 a, \206\166 a) \226\138\163\226\138\162 (\226\136\131 a, \226\150\183 \206\166 a).
Time Proof.
Time (apply : {}anti_symm {}; [  | apply later_exist_2 ]).
Time rewrite later_exist_false.
Time (<ssreflect_plugin::ssrtclseq@0> apply or_elim ; last  done).
Time (rewrite -(exist_intro inhabitant); auto).
Time Qed.
Time Lemma later_and P Q : \226\150\183 (P \226\136\167 Q) \226\138\163\226\138\162 \226\150\183 P \226\136\167 \226\150\183 Q.
Time Proof.
Time rewrite !and_alt later_forall.
Time by <ssreflect_plugin::ssrtclintros@0> apply forall_proper =>- [].
Time Qed.
Time Lemma later_or P Q : \226\150\183 (P \226\136\168 Q) \226\138\163\226\138\162 \226\150\183 P \226\136\168 \226\150\183 Q.
Time Proof.
Time rewrite !or_alt later_exist.
Time by <ssreflect_plugin::ssrtclintros@0> apply exist_proper =>- [].
Time Qed.
Time Lemma later_impl P Q : \226\150\183 (P \226\134\146 Q) \226\138\162 \226\150\183 P \226\134\146 \226\150\183 Q.
Time Proof.
Time (apply impl_intro_l).
Time by rewrite -later_and impl_elim_r.
Time Qed.
Time Lemma later_sep P Q : \226\150\183 (P \226\136\151 Q) \226\138\163\226\138\162 \226\150\183 P \226\136\151 \226\150\183 Q.
Time Proof.
Time (apply (anti_symm _); auto using later_sep_1, later_sep_2).
Time Qed.
Time Lemma later_wand P Q : \226\150\183 (P -\226\136\151 Q) \226\138\162 \226\150\183 P -\226\136\151 \226\150\183 Q.
Time Proof.
Time (apply wand_intro_l).
Time by rewrite -later_sep wand_elim_r.
Time Qed.
Time Lemma later_iff P Q : \226\150\183 (P \226\134\148 Q) \226\138\162 \226\150\183 P \226\134\148 \226\150\183 Q.
Time Proof.
Time by rewrite /bi_iff later_and !later_impl.
Time Qed.
Time Lemma later_persistently P : \226\150\183 <pers> P \226\138\163\226\138\162 <pers> \226\150\183 P.
Time Proof.
Time
(apply (anti_symm _); auto using later_persistently_1, later_persistently_2).
Time Qed.
Time Lemma later_affinely_2 P : <affine> \226\150\183 P \226\138\162 \226\150\183 <affine> P.
Time Proof.
Time rewrite /bi_affinely later_and.
Time auto using later_intro.
Time Qed.
Time Lemma later_intuitionistically_2 P : \226\150\161 \226\150\183 P \226\138\162 \226\150\183 \226\150\161 P.
Time Proof.
Time by rewrite /bi_intuitionistically -later_persistently later_affinely_2.
Time Qed.
Time Lemma later_intuitionistically_if_2 p P : \226\150\161?p \226\150\183 P \226\138\162 \226\150\183 \226\150\161?p P.
Time Proof.
Time (destruct p; simpl; auto using later_intuitionistically_2).
Time Qed.
Time Lemma later_absorbingly P : \226\150\183 <absorb> P \226\138\163\226\138\162 <absorb> \226\150\183 P.
Time Proof.
Time by rewrite /bi_absorbingly later_sep later_True.
Time Qed.
Time Lemma later_affinely `{!BiAffine PROP} P : \226\150\183 <affine> P \226\138\163\226\138\162 <affine> \226\150\183 P.
Time Proof.
Time by rewrite !affine_affinely.
Time Qed.
Time Lemma later_intuitionistically `{!BiAffine PROP} P : \226\150\183 \226\150\161 P \226\138\163\226\138\162 \226\150\161 \226\150\183 P.
Time Proof.
Time by rewrite !intuitionistically_into_persistently later_persistently.
Time Qed.
Time
Lemma later_intuitionistically_if `{!BiAffine PROP} p P : \226\150\183 \226\150\161?p P \226\138\163\226\138\162 \226\150\161?p \226\150\183 P.
Time Proof.
Time (destruct p; simpl; auto using later_intuitionistically).
Time Qed.
Time #[global]
Instance later_persistent  P: (Persistent P \226\134\146 Persistent (\226\150\183 P)).
Time Proof.
Time (intros).
Time by rewrite /Persistent -later_persistently {+1}(persistent P).
Time Qed.
Time #[global]Instance later_absorbing  P: (Absorbing P \226\134\146 Absorbing (\226\150\183 P)).
Time Proof.
Time (intros ?).
Time by rewrite /Absorbing -later_absorbingly absorbing.
Time Qed.
Time Section l\195\182b.
Time Lemma weak_l\195\182b P : (\226\150\183 P \226\138\162 P) \226\134\146 True \226\138\162 P.
Time Proof.
Time (pose (fl\195\182b_pre := fun P Q : PROP => (\226\150\183 Q \226\134\146 P)%I)).
Time (assert (\226\136\128 P, Contractive (fl\195\182b_pre P)) by solve_contractive).
Time (set (Q := fixpoint (fl\195\182b_pre P))).
Time (assert (HQ : Q \226\138\163\226\138\162 (\226\150\183 Q \226\134\146 P)) by exact : {}fixpoint_unfold {}).
Time (intros HP).
Time rewrite -HP.
Time (assert (HQP : \226\150\183 Q \226\138\162 P)).
Time {
Time rewrite -HP.
Time rewrite -(idemp (\226\136\167) (\226\150\183 Q))%I {+2}(later_intro (\226\150\183 Q))%I.
Time by rewrite {+1}HQ {+1}later_impl impl_elim_l.
Time }
Time rewrite -HQP HQ -2!later_intro.
Time (apply (entails_impl_True _ P)).
Time done.
Time Qed.
Time Lemma l\195\182b P : (\226\150\183 P \226\134\146 P) \226\138\162 P.
Time Proof.
Time (apply entails_impl_True, weak_l\195\182b).
Time (apply impl_intro_r).
Time rewrite -{+2}(idemp (\226\136\167) (\226\150\183 P \226\134\146 P))%I.
Time rewrite {+2}(later_intro (\226\150\183 P \226\134\146 P))%I.
Time rewrite later_impl.
Time rewrite assoc impl_elim_l.
Time rewrite impl_elim_r.
Time done.
Time Qed.
Time End l\195\182b.
Time #[global]Instance laterN_ne  m: (NonExpansive (@sbi_laterN PROP m)).
Time Proof.
Time (induction m; simpl).
Time by intros ? ? ?.
Time solve_proper.
Time Qed.
Time #[global]
Instance laterN_proper  m: (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@sbi_laterN PROP m)) :=
 (ne_proper _).
Time Lemma laterN_0 P : \226\150\183^0 P \226\138\163\226\138\162 P.
Time Proof.
Time done.
Time Qed.
Time Lemma later_laterN n P : \226\150\183^(S n) P \226\138\163\226\138\162 \226\150\183 \226\150\183^n P.
Time Proof.
Time done.
Time Qed.
Time Lemma laterN_later n P : \226\150\183^(S n) P \226\138\163\226\138\162 \226\150\183^n \226\150\183 P.
Time Proof.
Time (induction n; f_equiv /=; auto).
Time Qed.
Time Lemma laterN_plus n1 n2 P : \226\150\183^(n1 + n2) P \226\138\163\226\138\162 \226\150\183^n1 \226\150\183^n2 P.
Time Proof.
Time (induction n1; f_equiv /=; auto).
Time Qed.
Time Lemma laterN_le n1 n2 P : n1 \226\137\164 n2 \226\134\146 \226\150\183^n1 P \226\138\162 \226\150\183^n2 P.
Time Proof.
Time (induction 1; simpl; by rewrite -?later_intro).
Time Qed.
Time Lemma laterN_iter n P : (\226\150\183^n P)%I = Nat.iter n sbi_later P.
Time Proof.
Time (induction n; f_equal /=; auto).
Time Qed.
Time Lemma laterN_mono n P Q : (P \226\138\162 Q) \226\134\146 \226\150\183^n P \226\138\162 \226\150\183^n Q.
Time Proof.
Time (induction n; simpl; auto).
Time Qed.
Time #[global]
Instance laterN_mono'  n: (Proper ((\226\138\162) ==> (\226\138\162)) (@sbi_laterN PROP n)).
Time Proof.
Time (intros P Q; apply laterN_mono).
Time Qed.
Time #[global]
Instance laterN_flip_mono'  n:
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@sbi_laterN PROP n)).
Time Proof.
Time (intros P Q; apply laterN_mono).
Time Qed.
Time Lemma laterN_intro n P : P \226\138\162 \226\150\183^n P.
Time Proof.
Time (induction n as [| n IH]; simpl; by rewrite -?later_intro).
Time Qed.
Time Lemma laterN_True n : \226\150\183^n True \226\138\163\226\138\162 True.
Time Proof.
Time (apply (anti_symm (\226\138\162)); auto using laterN_intro, True_intro).
Time Qed.
Time Lemma laterN_emp `{!BiAffine PROP} n : \226\150\183^n emp \226\138\163\226\138\162 emp.
Time Proof.
Time by rewrite -True_emp laterN_True.
Time Qed.
Time
Lemma laterN_forall {A} n (\206\166 : A \226\134\146 PROP) : \226\150\183^n (\226\136\128 a, \206\166 a) \226\138\163\226\138\162 (\226\136\128 a, \226\150\183^n \206\166 a).
Time Proof.
Time (induction n as [| n IH]; simpl; rewrite -?later_forall ?IH; auto).
Time Qed.
Time
Lemma laterN_exist_2 {A} n (\206\166 : A \226\134\146 PROP) : (\226\136\131 a, \226\150\183^n \206\166 a) \226\138\162 \226\150\183^n (\226\136\131 a, \206\166 a).
Time Proof.
Time (apply exist_elim; eauto using exist_intro, laterN_mono).
Time Qed.
Time
Lemma laterN_exist `{Inhabited A} n (\206\166 : A \226\134\146 PROP) :
  \226\150\183^n (\226\136\131 a, \206\166 a) \226\138\163\226\138\162 (\226\136\131 a, \226\150\183^n \206\166 a).
Time Proof.
Time (induction n as [| n IH]; simpl; rewrite -?later_exist ?IH; auto).
Time Qed.
Time Lemma laterN_and n P Q : \226\150\183^n (P \226\136\167 Q) \226\138\163\226\138\162 \226\150\183^n P \226\136\167 \226\150\183^n Q.
Time Proof.
Time (induction n as [| n IH]; simpl; rewrite -?later_and ?IH; auto).
Time Qed.
Time Lemma laterN_or n P Q : \226\150\183^n (P \226\136\168 Q) \226\138\163\226\138\162 \226\150\183^n P \226\136\168 \226\150\183^n Q.
Time Proof.
Time (induction n as [| n IH]; simpl; rewrite -?later_or ?IH; auto).
Time Qed.
Time Lemma laterN_impl n P Q : \226\150\183^n (P \226\134\146 Q) \226\138\162 \226\150\183^n P \226\134\146 \226\150\183^n Q.
Time Proof.
Time (apply impl_intro_l).
Time by rewrite -laterN_and impl_elim_r.
Time Qed.
Time Lemma laterN_sep n P Q : \226\150\183^n (P \226\136\151 Q) \226\138\163\226\138\162 \226\150\183^n P \226\136\151 \226\150\183^n Q.
Time Proof.
Time (induction n as [| n IH]; simpl; rewrite -?later_sep ?IH; auto).
Time Qed.
Time Lemma laterN_wand n P Q : \226\150\183^n (P -\226\136\151 Q) \226\138\162 \226\150\183^n P -\226\136\151 \226\150\183^n Q.
Time Proof.
Time (apply wand_intro_l).
Time by rewrite -laterN_sep wand_elim_r.
Time Qed.
Time Lemma laterN_iff n P Q : \226\150\183^n (P \226\134\148 Q) \226\138\162 \226\150\183^n P \226\134\148 \226\150\183^n Q.
Time Proof.
Time by rewrite /bi_iff laterN_and !laterN_impl.
Time Qed.
Time Lemma laterN_persistently n P : \226\150\183^n <pers> P \226\138\163\226\138\162 <pers> \226\150\183^n P.
Time Proof.
Time (induction n as [| n IH]; simpl; auto).
Time by rewrite IH later_persistently.
Time Qed.
Time Lemma laterN_affinely_2 n P : <affine> \226\150\183^n P \226\138\162 \226\150\183^n <affine> P.
Time Proof.
Time rewrite /bi_affinely laterN_and.
Time auto using laterN_intro.
Time Qed.
Time Lemma laterN_intuitionistically_2 n P : \226\150\161 \226\150\183^n P \226\138\162 \226\150\183^n \226\150\161 P.
Time Proof.
Time
by rewrite /bi_intuitionistically -laterN_persistently laterN_affinely_2.
Time Qed.
Time Lemma laterN_intuitionistically_if_2 n p P : \226\150\161?p \226\150\183^n P \226\138\162 \226\150\183^n \226\150\161?p P.
Time Proof.
Time (destruct p; simpl; auto using laterN_intuitionistically_2).
Time Qed.
Time Lemma laterN_absorbingly n P : \226\150\183^n <absorb> P \226\138\163\226\138\162 <absorb> \226\150\183^n P.
Time Proof.
Time by rewrite /bi_absorbingly laterN_sep laterN_True.
Time Qed.
Time #[global]
Instance laterN_persistent  n P: (Persistent P \226\134\146 Persistent (\226\150\183^n P)).
Time Proof.
Time (induction n; apply _).
Time Qed.
Time #[global]
Instance laterN_absorbing  n P: (Absorbing P \226\134\146 Absorbing (\226\150\183^n P)).
Time Proof.
Time (induction n; apply _).
Time Qed.
Time #[global]Instance except_0_ne : (NonExpansive (@sbi_except_0 PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance except_0_proper : (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@sbi_except_0 PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance except_0_mono' : (Proper ((\226\138\162) ==> (\226\138\162)) (@sbi_except_0 PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance except_0_flip_mono' :
 (Proper (flip (\226\138\162) ==> flip (\226\138\162)) (@sbi_except_0 PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time Lemma except_0_intro P : P \226\138\162 \226\151\135 P.
Time Proof.
Time (rewrite /sbi_except_0; auto).
Time Qed.
Time Lemma except_0_mono P Q : (P \226\138\162 Q) \226\134\146 \226\151\135 P \226\138\162 \226\151\135 Q.
Time Proof.
Time by intros ->.
Time Qed.
Time Lemma except_0_idemp P : \226\151\135 \226\151\135 P \226\138\163\226\138\162 \226\151\135 P.
Time Proof.
Time (apply (anti_symm _); rewrite /sbi_except_0; auto).
Time Qed.
Time Lemma except_0_True : \226\151\135 True \226\138\163\226\138\162 True.
Time Proof.
Time rewrite /sbi_except_0.
Time (apply (anti_symm _); auto).
Time Qed.
Time Lemma except_0_emp `{!BiAffine PROP} : \226\151\135 emp \226\138\163\226\138\162 emp.
Time Proof.
Time by rewrite -True_emp except_0_True.
Time Qed.
Time Lemma except_0_or P Q : \226\151\135 (P \226\136\168 Q) \226\138\163\226\138\162 \226\151\135 P \226\136\168 \226\151\135 Q.
Time Proof.
Time rewrite /sbi_except_0.
Time (apply (anti_symm _); auto).
Time Qed.
Time Lemma except_0_and P Q : \226\151\135 (P \226\136\167 Q) \226\138\163\226\138\162 \226\151\135 P \226\136\167 \226\151\135 Q.
Time Proof.
Time by rewrite /sbi_except_0 or_and_l.
Time Qed.
Time Lemma except_0_sep P Q : \226\151\135 (P \226\136\151 Q) \226\138\163\226\138\162 \226\151\135 P \226\136\151 \226\151\135 Q.
Time Proof.
Time rewrite /sbi_except_0.
Time (apply (anti_symm _)).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> apply or_elim ; last  by auto
 using sep_mono).
Time
by rewrite -!or_intro_l -persistently_pure -later_sep -persistently_sep_dup.
Time -
Time rewrite sep_or_r !sep_or_l {+1}(later_intro P) {+1}(later_intro Q).
Time rewrite -!later_sep !left_absorb right_absorb.
Time auto.
Time Qed.
Time Lemma except_0_forall {A} (\206\166 : A \226\134\146 PROP) : \226\151\135 (\226\136\128 a, \206\166 a) \226\138\163\226\138\162 (\226\136\128 a, \226\151\135 \206\166 a).
Time Proof.
Time (apply (anti_symm _)).
Time {
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>a).
Time by rewrite (forall_elim a).
Time }
Time trans (\226\150\183 (\226\136\128 a : A, \206\166 a) \226\136\167 (\226\136\128 a : A, \226\151\135 \206\166 a))%I.
Time {
Time (apply and_intro, reflexivity).
Time rewrite later_forall.
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_mono =>a).
Time (apply or_elim; auto using later_intro).
Time }
Time rewrite later_false_em and_or_r.
Time (apply or_elim).
Time {
Time rewrite and_elim_l.
Time (apply or_intro_l).
Time }
Time
(<ssreflect_plugin::ssrtclintros@0> apply or_intro_r', forall_intro =>a).
Time rewrite !(forall_elim a).
Time by rewrite and_or_l impl_elim_l and_elim_r idemp.
Time Qed.
Time Lemma except_0_exist_2 {A} (\206\166 : A \226\134\146 PROP) : (\226\136\131 a, \226\151\135 \206\166 a) \226\138\162 \226\151\135 (\226\136\131 a, \206\166 a).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>a).
Time by rewrite (exist_intro a).
Time Qed.
Time
Lemma except_0_exist `{Inhabited A} (\206\166 : A \226\134\146 PROP) :
  \226\151\135 (\226\136\131 a, \206\166 a) \226\138\163\226\138\162 (\226\136\131 a, \226\151\135 \206\166 a).
Time Proof.
Time (apply (anti_symm _); [  | by apply except_0_exist_2 ]).
Time (apply or_elim).
Time -
Time rewrite -(exist_intro inhabitant).
Time by apply or_intro_l.
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_mono =>a).
Time (apply except_0_intro).
Time Qed.
Time Lemma except_0_later P : \226\151\135 \226\150\183 P \226\138\162 \226\150\183 P.
Time Proof.
Time by rewrite /sbi_except_0 -later_or False_or.
Time Qed.
Time Lemma except_0_persistently P : \226\151\135 <pers> P \226\138\163\226\138\162 <pers> \226\151\135 P.
Time Proof.
Time
by rewrite /sbi_except_0 persistently_or -later_persistently
 persistently_pure.
Time Qed.
Time Lemma except_0_affinely_2 P : <affine> \226\151\135 P \226\138\162 \226\151\135 <affine> P.
Time Proof.
Time rewrite /bi_affinely except_0_and.
Time auto using except_0_intro.
Time Qed.
Time Lemma except_0_intuitionistically_2 P : \226\150\161 \226\151\135 P \226\138\162 \226\151\135 \226\150\161 P.
Time Proof.
Time
by rewrite /bi_intuitionistically -except_0_persistently except_0_affinely_2.
Time Qed.
Time Lemma except_0_intuitionistically_if_2 p P : \226\150\161?p \226\151\135 P \226\138\162 \226\151\135 \226\150\161?p P.
Time Proof.
Time (destruct p; simpl; auto using except_0_intuitionistically_2).
Time Qed.
Time Lemma except_0_absorbingly P : \226\151\135 <absorb> P \226\138\163\226\138\162 <absorb> \226\151\135 P.
Time Proof.
Time by rewrite /bi_absorbingly except_0_sep except_0_True.
Time Qed.
Time Lemma except_0_frame_l P Q : P \226\136\151 \226\151\135 Q \226\138\162 \226\151\135 (P \226\136\151 Q).
Time Proof.
Time by rewrite {+1}(except_0_intro P) except_0_sep.
Time Qed.
Time Lemma except_0_frame_r P Q : \226\151\135 P \226\136\151 Q \226\138\162 \226\151\135 (P \226\136\151 Q).
Time Proof.
Time by rewrite {+1}(except_0_intro Q) except_0_sep.
Time Qed.
Time
Lemma later_affinely_1 `{!Timeless (PROP:=PROP) emp} 
  P : \226\150\183 <affine> P \226\138\162 \226\151\135 <affine> \226\150\183 P.
Time Proof.
Time rewrite /bi_affinely later_and (timeless emp%I) except_0_and.
Time by apply and_mono, except_0_intro.
Time Qed.
Time #[global]
Instance except_0_persistent  P: (Persistent P \226\134\146 Persistent (\226\151\135 P)).
Time Proof.
Time (rewrite /sbi_except_0; apply _).
Time Qed.
Time #[global]
Instance except_0_absorbing  P: (Absorbing P \226\134\146 Absorbing (\226\151\135 P)).
Time Proof.
Time (rewrite /sbi_except_0; apply _).
Time Qed.
Time #[global]
Instance Timeless_proper : (Proper ((\226\137\161) ==> iff) (@Timeless PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]Instance pure_timeless  \207\134: (Timeless (PROP:=PROP) \226\140\156\207\134\226\140\157).
Time Proof.
Time rewrite /Timeless /sbi_except_0 pure_alt later_exist_false.
Time
(<ssreflect_plugin::ssrtclintros@0> apply or_elim, exist_elim; [ auto |  ]
 =>H\207\134).
Time rewrite -(exist_intro H\207\134).
Time auto.
Time Qed.
Time #[global]
Instance emp_timeless  `{BiAffine PROP}: (Timeless (PROP:=PROP) emp).
Time Proof.
Time rewrite -True_emp.
Time (apply _).
Time Qed.
Time #[global]
Instance and_timeless  P Q: (Timeless P \226\134\146 Timeless Q \226\134\146 Timeless (P \226\136\167 Q)).
Time Proof.
Time (intros; rewrite /Timeless except_0_and later_and; auto).
Time Qed.
Time #[global]
Instance or_timeless  P Q: (Timeless P \226\134\146 Timeless Q \226\134\146 Timeless (P \226\136\168 Q)).
Time Proof.
Time (intros; rewrite /Timeless except_0_or later_or; auto).
Time Qed.
Time #[global]Instance impl_timeless  P Q: (Timeless Q \226\134\146 Timeless (P \226\134\146 Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Timeless =>HQ).
Time rewrite later_false_em.
Time
(<ssreflect_plugin::ssrtclseq@0> apply or_mono, impl_intro_l ; first  done).
Time (rewrite -{+2}(l\195\182b Q); apply impl_intro_l).
Time rewrite HQ /sbi_except_0 !and_or_r.
Time (<ssreflect_plugin::ssrtclseq@0> apply or_elim ; last  auto).
Time by rewrite assoc (comm _ _ P) -assoc !impl_elim_r.
Time Qed.
Time #[global]
Instance sep_timeless  P Q: (Timeless P \226\134\146 Timeless Q \226\134\146 Timeless (P \226\136\151 Q)).
Time Proof.
Time (intros; rewrite /Timeless except_0_sep later_sep; auto using sep_mono).
Time Qed.
Time #[global]Instance wand_timeless  P Q: (Timeless Q \226\134\146 Timeless (P -\226\136\151 Q)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Timeless =>HQ).
Time rewrite later_false_em.
Time
(<ssreflect_plugin::ssrtclseq@0> apply or_mono, wand_intro_l ; first  done).
Time (rewrite -{+2}(l\195\182b Q); apply impl_intro_l).
Time rewrite HQ /sbi_except_0 !and_or_r.
Time (<ssreflect_plugin::ssrtclseq@0> apply or_elim ; last  auto).
Time by rewrite (comm _ P) persistent_and_sep_assoc impl_elim_r wand_elim_l.
Time Qed.
Time #[global]
Instance forall_timeless  {A} (\206\168 : A \226\134\146 PROP):
 ((\226\136\128 x, Timeless (\206\168 x)) \226\134\146 Timeless (\226\136\128 x, \206\168 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Timeless =>HQ).
Time rewrite except_0_forall later_forall.
Time (apply forall_mono; auto).
Time Qed.
Time #[global]
Instance exist_timeless  {A} (\206\168 : A \226\134\146 PROP):
 ((\226\136\128 x, Timeless (\206\168 x)) \226\134\146 Timeless (\226\136\131 x, \206\168 x)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Timeless =>?).
Time rewrite later_exist_false.
Time (apply or_elim).
Time -
Time (rewrite /sbi_except_0; auto).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply exist_elim =>x).
Time (rewrite -(exist_intro x); auto).
Time Qed.
Time #[global]
Instance persistently_timeless  P: (Timeless P \226\134\146 Timeless (<pers> P)).
Time Proof.
Time (intros).
Time rewrite /Timeless /sbi_except_0 later_persistently_1.
Time
by rewrite (timeless P) /sbi_except_0 persistently_or {+1}persistently_elim.
Time Qed.
Time #[global]
Instance affinely_timeless  P:
 (Timeless (PROP:=PROP) emp \226\134\146 Timeless P \226\134\146 Timeless (<affine> P)).
Time Proof.
Time (rewrite /bi_affinely; apply _).
Time Qed.
Time #[global]
Instance absorbingly_timeless  P: (Timeless P \226\134\146 Timeless (<absorb> P)).
Time Proof.
Time (rewrite /bi_absorbingly; apply _).
Time Qed.
Time #[global]
Instance intuitionistically_timeless  P:
 (Timeless (PROP:=PROP) emp \226\134\146 Timeless P \226\134\146 Timeless (\226\150\161 P)).
Time Proof.
Time (rewrite /bi_intuitionistically; apply _).
Time Qed.
Time #[global]
Instance eq_timeless  {A : ofeT} (a b : A):
 (Discrete a \226\134\146 Timeless (PROP:=PROP) (a \226\137\161 b)).
Time Proof.
Time (intros).
Time rewrite /Discrete !discrete_eq.
Time (apply (timeless _)).
Time Qed.
Time #[global]
Instance from_option_timeless  {A} P (\206\168 : A \226\134\146 PROP) 
 (mx : option A):
 ((\226\136\128 x, Timeless (\206\168 x)) \226\134\146 Timeless P \226\134\146 Timeless (from_option \206\168 P mx)).
Time Proof.
Time (destruct mx; apply _).
Time Qed.
Time #[global]
Instance sbi_later_monoid_and_homomorphism :
 (MonoidHomomorphism bi_and bi_and (\226\137\161) (@sbi_later PROP)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (apply later_and).
Time (apply later_True).
Time Qed.
Time #[global]
Instance sbi_laterN_and_homomorphism  n:
 (MonoidHomomorphism bi_and bi_and (\226\137\161) (@sbi_laterN PROP n)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (apply laterN_and).
Time (apply laterN_True).
Time Qed.
Time #[global]
Instance sbi_except_0_and_homomorphism :
 (MonoidHomomorphism bi_and bi_and (\226\137\161) (@sbi_except_0 PROP)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (apply except_0_and).
Time (apply except_0_True).
Time Qed.
Time #[global]
Instance sbi_later_monoid_or_homomorphism :
 (WeakMonoidHomomorphism bi_or bi_or (\226\137\161) (@sbi_later PROP)).
Time Proof.
Time (split; try apply _).
Time (apply later_or).
Time Qed.
Time #[global]
Instance sbi_laterN_or_homomorphism  n:
 (WeakMonoidHomomorphism bi_or bi_or (\226\137\161) (@sbi_laterN PROP n)).
Time Proof.
Time (split; try apply _).
Time (apply laterN_or).
Time Qed.
Time #[global]
Instance sbi_except_0_or_homomorphism :
 (WeakMonoidHomomorphism bi_or bi_or (\226\137\161) (@sbi_except_0 PROP)).
Time Proof.
Time (split; try apply _).
Time (apply except_0_or).
Time Qed.
Time #[global]
Instance sbi_later_monoid_sep_weak_homomorphism :
 (WeakMonoidHomomorphism bi_sep bi_sep (\226\137\161) (@sbi_later PROP)).
Time Proof.
Time (split; try apply _).
Time (apply later_sep).
Time Qed.
Time #[global]
Instance sbi_laterN_sep_weak_homomorphism  n:
 (WeakMonoidHomomorphism bi_sep bi_sep (\226\137\161) (@sbi_laterN PROP n)).
Time Proof.
Time (split; try apply _).
Time (apply laterN_sep).
Time Qed.
Time #[global]
Instance sbi_except_0_sep_weak_homomorphism :
 (WeakMonoidHomomorphism bi_sep bi_sep (\226\137\161) (@sbi_except_0 PROP)).
Time Proof.
Time (split; try apply _).
Time (apply except_0_sep).
Time Qed.
Time #[global]
Instance sbi_later_monoid_sep_homomorphism  `{!BiAffine PROP}:
 (MonoidHomomorphism bi_sep bi_sep (\226\137\161) (@sbi_later PROP)).
Time Proof.
Time (split; try apply _).
Time (apply later_emp).
Time Qed.
Time #[global]
Instance sbi_laterN_sep_homomorphism  `{!BiAffine PROP} 
 n: (MonoidHomomorphism bi_sep bi_sep (\226\137\161) (@sbi_laterN PROP n)).
Time Proof.
Time (split; try apply _).
Time (apply laterN_emp).
Time Qed.
Time #[global]
Instance sbi_except_0_sep_homomorphism  `{!BiAffine PROP}:
 (MonoidHomomorphism bi_sep bi_sep (\226\137\161) (@sbi_except_0 PROP)).
Time Proof.
Time (split; try apply _).
Time (apply except_0_emp).
Time Qed.
Time #[global]
Instance sbi_later_monoid_sep_entails_weak_homomorphism :
 (WeakMonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@sbi_later PROP)).
Time Proof.
Time (split; try apply _).
Time (intros P Q).
Time by rewrite later_sep.
Time Qed.
Time #[global]
Instance sbi_laterN_sep_entails_weak_homomorphism  
 n: (WeakMonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@sbi_laterN PROP n)).
Time Proof.
Time (split; try apply _).
Time (intros P Q).
Time by rewrite laterN_sep.
Time Qed.
Time #[global]
Instance sbi_except_0_sep_entails_weak_homomorphism :
 (WeakMonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@sbi_except_0 PROP)).
Time Proof.
Time (split; try apply _).
Time (intros P Q).
Time by rewrite except_0_sep.
Time Qed.
Time #[global]
Instance sbi_later_monoid_sep_entails_homomorphism :
 (MonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@sbi_later PROP)).
Time Proof.
Time (split; try apply _).
Time (apply later_intro).
Time Qed.
Time #[global]
Instance sbi_laterN_sep_entails_homomorphism  n:
 (MonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@sbi_laterN PROP n)).
Time Proof.
Time (split; try apply _).
Time (apply laterN_intro).
Time Qed.
Time #[global]
Instance sbi_except_0_sep_entails_homomorphism :
 (MonoidHomomorphism bi_sep bi_sep (flip (\226\138\162)) (@sbi_except_0 PROP)).
Time Proof.
Time (split; try apply _).
Time (apply except_0_intro).
Time Qed.
Time End sbi_derived.
Time End bi.
