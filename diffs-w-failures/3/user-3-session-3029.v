Time From iris.algebra Require Export big_op.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type*".
Time #[local]
Existing Instances
 monoid_ne, monoid_assoc, monoid_comm, monoid_left_id, monoid_right_id, monoid_proper, monoid_homomorphism_rel_po, monoid_homomorphism_rel_proper, monoid_homomorphism_op_proper, monoid_homomorphism_ne, weak_monoid_homomorphism_proper.
Time Require Import EqualDec.
Time Require Export SemanticsHelpers.
Time
Definition big_opDM `{Monoid M o} A (Ref Model : A -> Type)
  (f : \226\136\128 {T}, Ref T \226\134\146 Model T \226\134\146 M) (m : DynMap Ref Model) :=
  big_opL o
    (\206\187 _ k,
       match getDyn m (projT2 k) with
       | None => monoid_unit
       | Some v => f (projT2 k) v
       end) (dynMap_dom m).
Time Arguments big_opDM {M} o {_} {A} {Ref} {Model} _ _ : simpl never.
Time Typeclasses Opaque big_opDM.
Time
Notation "'[^' o 'dmap]' k \226\134\166 x \226\136\136 m , P" := (big_opDM o (\206\187 _ k x, P) m)
  (at level 200, o  at level 1, m  at level 10, k, x  at level 1,
   right associativity, format "[^  o  dmap]  k \226\134\166 x  \226\136\136  m ,  P") :
  stdpp_scope.
Time
Notation "'[^' o 'dmap]' x \226\136\136 m , P" := (big_opDM o (\206\187 _ _ x, P) m)
  (at level 200, o  at level 1, m  at level 10, x  at level 1,
   right associativity, format "[^ o  dmap]  x  \226\136\136  m ,  P") : stdpp_scope.
Time
Notation "'[^' o 'dmap]' ( k : 'Ref' a ) \226\134\166 x \226\136\136 m , P" :=
  (big_opDM o (\206\187 a k x, P) m)
  (at level 200, o  at level 1, m  at level 10, k, x  at level 1,
   right associativity, only printing,
   format "[^  o  dmap]  ( k :  Ref  a ) \226\134\166 x  \226\136\136  m ,  P") : stdpp_scope.
Time Section monoid.
Time Context `{Monoid M o}.
Time Infix "`o`" := o (at level 50, left associativity).
Time Context {A : Type} {Ref Model : A \226\134\146 Type}.
Time Context `{dec : EqualDec {x : A & Ref x}}.
Time Implicit Type m : DynMap Ref Model.
Time Implicit Types f g : \226\136\128 {T}, Ref T \226\134\146 Model T \226\134\146 M.
Time
Lemma big_opDM_forall R f g m :
  Reflexive R
  \226\134\146 Proper (R ==> R ==> R) o
    \226\134\146 (\226\136\128 {T} (k : Ref T) x, getDyn m k = Some x \226\134\146 R (f _ k x) (g _ k x))
      \226\134\146 R ([^ o dmap] k\226\134\166x \226\136\136 m, f _ k x) ([^ o dmap] k\226\134\166x \226\136\136 m, g _ k x).
Time Proof.
Time (intros ? ? Hf).
Time (apply (big_opL_forall R); auto).
Time (intros k [i x] (v, Heq)%dynMap_dom_lookup; eauto).
Time (rewrite Heq; eauto).
Time Qed.
Time
Lemma big_opDM_ext f g m :
  (\226\136\128 {T} (k : Ref T) x, getDyn m k = Some x \226\134\146 f _ k x = g _ k x)
  \226\134\146 ([^ o dmap] k\226\134\166x \226\136\136 m, f _ k x) = ([^ o dmap] k\226\134\166x \226\136\136 m, g _ k x).
Time Proof.
Time (apply big_opDM_forall; apply _).
Time Qed.
Time
Lemma big_opDM_proper f g m :
  (\226\136\128 {T} (k : Ref T) x, getDyn m k = Some x \226\134\146 f _ k x \226\137\161 g _ k x)
  \226\134\146 ([^ o dmap] k\226\134\166x \226\136\136 m, f _ k x) \226\137\161 ([^ o dmap] k\226\134\166x \226\136\136 m, g _ k x).
Time Proof.
Time (apply big_opDM_forall; apply _).
Time Qed.
Time
Lemma big_opDM_proper_map f m1 m2 :
  m1 \226\137\161 m2 \226\134\146 ([^ o dmap] k\226\134\166x \226\136\136 m1, f _ k x) \226\137\161 ([^ o dmap] k\226\134\166x \226\136\136 m2, f _ k x).
Time Proof.
Time (intros Hequiv).
Time (unfold big_opDM).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite big_opL_permutation ; last  by
 rewrite Hequiv; reflexivity).
Time (<ssreflect_plugin::ssrtclintros@0> eapply big_opL_proper =>? ? ?).
Time by rewrite Hequiv.
Time Qed.
Time #[global]
Instance big_opDM_ne  n:
 (Proper
    (forall_relation
       (\206\187 T,
          pointwise_relation (Ref T) (pointwise_relation (Model T) (dist n))) ==>
     eq ==> dist n) (big_opDM o (A:=A) (Ref:=Ref) (Model:=Model))).
Time Proof.
Time (intros f g Hf m ? <-).
Time (apply big_opDM_forall; apply _ || intros; apply Hf).
Time Qed.
Time #[global]
Instance big_opDM_proper' :
 (Proper
    (forall_relation
       (\206\187 T, pointwise_relation (Ref T) (pointwise_relation (Model T) (\226\137\161))) ==>
     (\226\137\161) ==> (\226\137\161)) (big_opDM o (A:=A) (Ref:=Ref) (Model:=Model))).
Time Proof.
Time (intros f g Hf m1 m2 Hequiv).
Time rewrite big_opDM_proper_map //.
Time (apply big_opDM_forall; apply _ || intros; apply Hf).
Time Qed.
Time #[global]
Instance big_opDM_proper'' :
 (Proper (eq ==> (\226\137\161) ==> (\226\137\161)) (big_opDM o (A:=A) (Ref:=Ref) (Model:=Model))).
Time Proof.
Time (intros ? ? <- ? ? ?).
Time (eapply big_opDM_proper'; eauto).
Time (intros ? ?).
Time reflexivity.
Time Qed.
Time
Lemma big_opDM_empty f :
  ([^ o dmap] k\226\134\166x \226\136\136 (\226\136\133 : DynMap Ref Model), f _ k x) = monoid_unit.
Time Proof.
Time rewrite /big_opDM //=.
Time Qed.
Time
Lemma big_opDM_updDyn {T} f m (i : Ref T) (x : Model T) :
  getDyn m i = None
  \226\134\146 ([^ o dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x m, f _ k y)
    \226\137\161 f _ i x `o` ([^ o dmap] k\226\134\166y \226\136\136 m, f _ k y).
Time Proof.
Time (intros Hnone).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite /big_opDM //= decide_False //=
 ?getDyn_updDyn //= ; last  first).
Time {
Time (<ssreflect_plugin::ssrtclintros@0> rewrite -dynMap_dom_spec =>Hfalse).
Time by apply Hfalse, getDyn_lookup_none.
Time }
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> apply big_opL_proper =>k y).
Time (intros (v, Heq)%dynMap_dom_lookup).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite getDyn_updDyn_ne1 // =>?; subst).
Time rewrite Hnone // in  {} Heq.
Time Qed.
Time
Lemma big_opDM_delete {T} f m (i : Ref T) x :
  getDyn m i = Some x
  \226\134\146 ([^ o dmap] k\226\134\166y \226\136\136 m, f _ k y)
    \226\137\161 f _ i x `o` ([^ o dmap] k\226\134\166y \226\136\136 deleteDyn (dec:=dec) i m, f _ k y).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite -big_opDM_updDyn
 ?getDyn_deleteDyn // =>Hsome).
Time by rewrite updDyn_deleteDyn updDyn_identity.
Time Qed.
Time
Lemma big_opDM_singleton {T} f (i : Ref T) x :
  ([^ o dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x \226\136\133, f _ k y) \226\137\161 f _ i x.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite big_opDM_updDyn /= ; last  auto
 using lookup_empty).
Time by rewrite big_opDM_empty right_id.
Time Qed.
Time
Lemma big_opDM_unit m : ([^ o dmap] k\226\134\166y \226\136\136 m, monoid_unit) \226\137\161 (monoid_unit : M).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> etransitivity ; last  eapply big_opL_unit).
Time (unfold big_opDM).
Time (eapply big_opL_proper).
Time (intros ? ?; by destruct getDyn).
Time Qed.
Time
Lemma big_opDM_insert_override {T} f m (i : Ref T) 
  x x' :
  getDyn m i = Some x
  \226\134\146 f _ i x \226\137\161 f _ i x'
    \226\134\146 ([^ o dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x' m, f _ k y)
      \226\137\161 ([^ o dmap] k\226\134\166y \226\136\136 m, f _ k y).
Time Proof.
Time (intros ? Hx).
Time rewrite -updDyn_deleteDyn big_opDM_updDyn ?getDyn_deleteDyn //.
Time by rewrite -Hx -big_opDM_delete.
Time Qed.
Time
Lemma big_opDM_opDM f g m :
  ([^ o dmap] k\226\134\166x \226\136\136 m, f _ k x `o` g _ k x)
  \226\137\161 ([^ o dmap] k\226\134\166x \226\136\136 m, f _ k x) `o` ([^ o dmap] k\226\134\166x \226\136\136 m, g _ k x).
Time Proof.
Time rewrite /big_opM -big_opL_op.
Time
(<ssreflect_plugin::ssrtclintros@0> eapply big_opL_proper =>k [? ?] Heq).
Time (<ssreflect_plugin::ssrtclintros@0> destruct (getDyn) =>//=).
Time by rewrite right_id.
Time Qed.
Time End monoid.
Time Section homomorphisms.
Time Context `{Monoid M1 o1} `{Monoid M2 o2}.
Time Context {A : Type} {Ref Model : A \226\134\146 Type}.
Time Context `{dec : EqualDec {x : A & Ref x}}.
Time Infix "`o1`" := o1 (at level 50, left associativity).
Time Infix "`o2`" := o2 (at level 50, left associativity).
Time #[local]Instance: (\226\136\128 {A} (R : relation A), RewriteRelation R) := { }.
Time
Lemma morphism_commute_lookup (h : M1 \226\134\146 M2) `{!MonoidHomomorphism o1 o2 R h}
  (f : \226\136\128 T, Ref T \226\134\146 Model T \226\134\146 M1) (m : DynMap Ref Model) 
  x :
  R
    (h
       match getDyn m (projT2 x) with
       | Some v => f (projT1 x) (projT2 x) v
       | None => monoid_unit
       end)
    match getDyn m (projT2 x) with
    | Some v => h (f (projT1 x) (projT2 x) v)
    | None => monoid_unit
    end.
Time Proof.
Time (destruct getDyn; eauto).
Time -
Time reflexivity.
Time -
Time by rewrite monoid_homomorphism_unit.
Time Qed.
Time
Lemma big_opDM_commute (h : M1 \226\134\146 M2) `{!MonoidHomomorphism o1 o2 R h}
  (f : \226\136\128 T, Ref T \226\134\146 Model T \226\134\146 M1) (m : DynMap Ref Model) :
  R (h ([^ o1 dmap] k\226\134\166x \226\136\136 m, f _ k x)) ([^ o2 dmap] k\226\134\166x \226\136\136 m, h (f _ k x)).
Time Proof.
Time rewrite /big_opDM.
Time rewrite big_opL_commute.
Time (apply big_opL_forall; try apply _).
Time (intros).
Time by rewrite morphism_commute_lookup.
Time Qed.
Time
Lemma big_opDM_commute1 (h : M1 \226\134\146 M2) `{!WeakMonoidHomomorphism o1 o2 R h}
  (f : \226\136\128 T, Ref T \226\134\146 Model T \226\134\146 M1) (m : DynMap Ref Model) :
  m \226\137\162 \226\136\133
  \226\134\146 R (h ([^ o1 dmap] k\226\134\166x \226\136\136 m, f _ k x)) ([^ o2 dmap] k\226\134\166x \226\136\136 m, h (f _ k x)).
Time Proof.
Time (intros).
Time rewrite /big_opDM big_opL_commute1.
Time -
Time (apply big_opL_forall; try apply _).
Time (intros ? ? (v, ->)%dynMap_dom_lookup).
Time reflexivity.
Time -
Time by rewrite -dynMap_dom_empty_iff.
Time Qed.
Time End homomorphisms.
Time From iris.bi Require Import derived_laws_sbi plainly big_op.
Time Import interface.bi derived_laws_bi.bi derived_laws_sbi.bi.
Time
Notation "'[\226\136\151' 'dmap]' k \226\134\166 x \226\136\136 m , P" := (big_opDM bi_sep (\206\187 _ k x, P) m)
  (at level 200, m  at level 10, k, x  at level 1, right associativity,
   format "[\226\136\151  dmap]  k \226\134\166 x  \226\136\136  m ,  P") : bi_scope.
Time
Notation "'[\226\136\151' 'dmap]' ( k : 'Ref' a ) \226\134\166 x \226\136\136 m , P" :=
  (big_opDM bi_sep (\206\187 a k x, P) m)
  (at level 200, m  at level 10, k, x  at level 1, right associativity,
   only printing, format "[\226\136\151  dmap]  ( k :  Ref  a ) \226\134\166 x  \226\136\136  m ,  P") :
  stdpp_scope.
Time Section prop.
Time Context {PROP : bi}.
Time Implicit Types P Q : PROP.
Time Implicit Types Ps Qs : list PROP.
Time Context {A : Type} {Ref Model : A \226\134\146 Type}.
Time Context `{dec : EqualDec {x : A & Ref x}}.
Time Implicit Type m : DynMap Ref Model.
Time Implicit Types \206\166 \206\168 : \226\136\128 {T}, Ref T \226\134\146 Model T \226\134\146 PROP.
Time
Lemma big_sepDM_mono \206\166 \206\168 m :
  (\226\136\128 a k x, getDyn m k = Some x \226\134\146 \206\166 a k x \226\138\162 \206\168 a k x)
  \226\134\146 ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x) \226\138\162 [\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\168 _ k x.
Time Proof.
Time (apply big_opDM_forall; apply _ || auto).
Time Qed.
Time
Lemma big_sepDM_proper \206\166 \206\168 m :
  (\226\136\128 a k x, getDyn m k = Some x \226\134\146 \206\166 a k x \226\138\163\226\138\162 \206\168 a k x)
  \226\134\146 ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x) \226\138\163\226\138\162 ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\168 _ k x).
Time Proof.
Time (apply big_opDM_proper).
Time Qed.
Time #[global]
Instance big_sepDM_mono' :
 (Proper
    (forall_relation
       (\206\187 T, pointwise_relation (Ref T) (pointwise_relation (Model T) (\226\138\162))) ==>
     (\226\137\161) ==> (\226\138\162)) (big_opDM (@bi_sep PROP) (A:=A) (Ref:=Ref) (Model:=Model))).
Time Proof.
Time (intros f g Hf m ? <-).
Time
(<ssreflect_plugin::ssrtclintros@0> apply big_sepDM_mono =>? ? ? ?; apply Hf).
Time Qed.
Time
Lemma big_sepDM_empty \206\166 :
  ([\226\136\151 dmap] k\226\134\166x \226\136\136 (\226\136\133 : DynMap Ref Model), \206\166 _ k x) \226\138\163\226\138\162 emp.
Time Proof.
Time by rewrite big_opDM_empty.
Time Qed.
Time
Lemma big_sepDM_empty' `{BiAffine PROP} P \206\166 :
  P \226\138\162 [\226\136\151 dmap] k\226\134\166x \226\136\136 (\226\136\133 : DynMap Ref Model), \206\166 _ k x.
Time Proof.
Time rewrite big_sepDM_empty.
Time apply : {}affine {}.
Time Qed.
Time
Lemma big_sepDM_updDyn {T} \206\166 m (i : Ref T) x :
  getDyn m i = None
  \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x m, \206\166 _ k y)
    \226\138\163\226\138\162 \206\166 _ i x \226\136\151 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y).
Time Proof.
Time (apply big_opDM_updDyn).
Time Qed.
Time
Lemma big_sepDM_delete {T} \206\166 m (i : Ref T) x :
  getDyn m i = Some x
  \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y)
    \226\138\163\226\138\162 \206\166 _ i x \226\136\151 ([\226\136\151 dmap] k\226\134\166y \226\136\136 deleteDyn (dec:=dec) i m, \206\166 _ k y).
Time Proof.
Time (apply big_opDM_delete).
Time Qed.
Time
Lemma big_sepDM_updDyn_2 {T} \206\166 m (i : Ref T) x :
  TCOr (\226\136\128 x, Affine (\206\166 _ i x)) (Absorbing (\206\166 _ i x))
  \226\134\146 \206\166 _ i x
    -\226\136\151 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y)
       -\226\136\151 [\226\136\151 dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x m, 
       \206\166 _ k y.
Time Proof.
Time (intros Ha).
Time (apply wand_intro_r).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (getDyn m i) as [y| ] eqn:Hi ;
 last  first).
Time {
Time by rewrite -big_sepDM_updDyn.
Time }
Time (assert (TCOr (Affine (\206\166 _ i y)) (Absorbing (\206\166 _ i x)))).
Time {
Time (destruct Ha; try apply _).
Time }
Time rewrite big_sepDM_delete // assoc.
Time rewrite (sep_elim_l (\206\166 _ i x)) -big_sepDM_updDyn ?getDyn_deleteDyn //.
Time by rewrite updDyn_deleteDyn.
Time Qed.
Time
Lemma big_sepDM_lookup_acc {T} \206\166 m (i : Ref T) x :
  getDyn m i = Some x
  \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y)
    \226\138\162 \206\166 _ i x \226\136\151 (\206\166 _ i x -\226\136\151 [\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y).
Time Proof.
Time (intros).
Time rewrite big_sepDM_delete //.
Time by apply sep_mono_r, wand_intro_l.
Time Qed.
Time
Lemma big_sepDM_lookup {T} \206\166 m (i : Ref T) x `{!Absorbing (\206\166 _ i x)} :
  getDyn m i = Some x \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y) \226\138\162 \206\166 _ i x.
Time Proof.
Time (intros).
Time rewrite big_sepDM_lookup_acc //.
Time by rewrite sep_elim_l.
Time Qed.
Time
Lemma big_sepDM_singleton {T} \206\166 (i : Ref T) x :
  ([\226\136\151 dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x \226\136\133, \206\166 _ k y) \226\138\163\226\138\162 \206\166 _ i x.
Time Proof.
Time by rewrite big_opDM_singleton.
Time Qed.
Time
Lemma big_sepDM_insert_override {T} \206\166 m (i : Ref T) 
  x x' :
  getDyn m i = Some x
  \226\134\146 \206\166 _ i x \226\138\163\226\138\162 \206\166 _ i x'
    \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x' m, \206\166 _ k y)
      \226\138\163\226\138\162 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y).
Time Proof.
Time (apply big_opDM_insert_override).
Time Qed.
Time
Lemma big_sepDM_insert_override_1 {T} \206\166 m (i : Ref T) 
  x x' :
  getDyn m i = Some x
  \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x' m, \206\166 _ k y)
    \226\138\162 (\206\166 _ i x' -\226\136\151 \206\166 _ i x) -\226\136\151 [\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y.
Time Proof.
Time (intros ?).
Time (apply wand_intro_l).
Time rewrite -updDyn_deleteDyn big_sepDM_updDyn ?getDyn_deleteDyn //.
Time by rewrite assoc wand_elim_l -big_sepDM_delete.
Time Qed.
Time
Lemma big_sepDM_insert_override_2 {T} \206\166 m (i : Ref T) 
  x x' :
  getDyn m i = Some x
  \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y)
    \226\138\162 (\206\166 _ i x -\226\136\151 \206\166 _ i x')
      -\226\136\151 [\226\136\151 dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x' m, 
      \206\166 _ k y.
Time Proof.
Time (intros ?).
Time (apply wand_intro_l).
Time (rewrite {+1}big_sepDM_delete //; rewrite assoc wand_elim_l).
Time rewrite -updDyn_deleteDyn big_sepDM_updDyn ?getDyn_deleteDyn //.
Time Qed.
Time
Lemma big_sepDM_insert_acc {T} \206\166 m (i : Ref T) x :
  getDyn m i = Some x
  \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y)
    \226\138\162 \206\166 _ i x
      \226\136\151 (\226\136\128 x', \206\166 _ i x' -\226\136\151 [\226\136\151 dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x' m, \206\166 _ k y).
Time Proof.
Time (intros ?).
Time rewrite {+1}big_sepDM_delete //.
Time (apply sep_mono; [ done |  ]).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x').
Time rewrite -updDyn_deleteDyn big_sepDM_updDyn ?getDyn_deleteDyn //.
Time by apply wand_intro_l.
Time Qed.
Time
Lemma big_sepDM_sepDM \206\166 \206\168 m :
  ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x \226\136\151 \206\168 _ k x)
  \226\138\163\226\138\162 ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x) \226\136\151 ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\168 _ k x).
Time Proof.
Time (apply big_opDM_opDM).
Time Qed.
Time
Lemma big_sepDM_and \206\166 \206\168 m :
  ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x \226\136\167 \206\168 _ k x)
  \226\138\162 ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x) \226\136\167 ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\168 _ k x).
Time Proof.
Time auto using and_intro, big_sepDM_mono, and_elim_l, and_elim_r.
Time Qed.
Time
Lemma big_sepDM_persistently `{BiAffine PROP} \206\166 m :
  <pers> ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x) \226\138\163\226\138\162 ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, <pers> \206\166 _ k x).
Time Proof.
Time (apply (big_opDM_commute _)).
Time Qed.
Time
Lemma big_sepDM_forall `{BiAffine PROP} \206\166 m :
  (\226\136\128 a k x, Persistent (\206\166 a k x))
  \226\134\146 ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x) \226\138\163\226\138\162 (\226\136\128 a k x, \226\140\156getDyn m k = Some x\226\140\157 \226\134\146 \206\166 a k x).
Time Proof.
Time (intros).
Time (apply (anti_symm _)).
Time {
Time
(<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>a;
  <ssreflect_plugin::ssrtclintros@0> apply forall_intro =>k;
  <ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply impl_intro_l, pure_elim_l =>?; by
  apply : {}big_sepDM_lookup {}).
Time }
Time rewrite /big_opDM big_sepL_forall.
Time iIntros "H".
Time iIntros ( a (k, x) (v, Heq)%dynMap_dom_lookup ).
Time rewrite Heq.
Time by iApply "H".
Time Qed.
Time
Lemma big_sepDM_impl \206\166 \206\168 m :
  ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x)
  -\226\136\151 \226\150\161 (\226\136\128 a k x, \226\140\156getDyn m k = Some x\226\140\157 \226\134\146 \206\166 a k x -\226\136\151 \206\168 _ k x)
     -\226\136\151 [\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\168 _ k x.
Time Proof.
Time iIntros "H #Himpl".
Time rewrite /big_opDM.
Time iApply (big_sepL_impl with "H").
Time (iAlways; iIntros ( n (a, k) (v, Heq)%dynMap_dom_lookup )).
Time rewrite Heq.
Time iIntros "H".
Time (unshelve by iApply ("Himpl" $! a k v _); eauto).
Time Qed.
Time #[global]
Instance big_sepDM_empty_persistent  \206\166:
 (Persistent ([\226\136\151 dmap] k\226\134\166x \226\136\136 (\226\136\133 : DynMap Ref Model), \206\166 _ k x)).
Time Proof.
Time rewrite /big_opDM.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepDM_persistent  \206\166 m:
 ((\226\136\128 a k x, Persistent (\206\166 a k x)) \226\134\146 Persistent ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x)).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclintros@0> apply big_sepL_persistent =>_ 
  [? ?]; apply _).
Time Qed.
Time #[global]
Instance big_sepDM_empty_affine  \206\166:
 (Affine ([\226\136\151 dmap] k\226\134\166x \226\136\136 (\226\136\133 : DynMap Ref Model), \206\166 _ k x)).
Time Proof.
Time rewrite /big_opDM.
Time (apply _).
Time Qed.
Time #[global]
Instance big_sepDM_affine  \206\166 m:
 ((\226\136\128 a k x, Affine (\206\166 a k x)) \226\134\146 Affine ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x)).
Time Proof.
Time (intros).
Time (<ssreflect_plugin::ssrtclintros@0> apply big_sepL_affine =>_ [? ?]).
Time (destruct getDyn; apply _).
Time Qed.
Time End prop.
Time Section sprop.
Time Context {PROP : sbi}.
Time Implicit Types P Q : PROP.
Time Implicit Types Ps Qs : list PROP.
Time Context {A : Type} {Ref Model : A \226\134\146 Type}.
Time Implicit Type m : DynMap Ref Model.
Time Implicit Types \206\166 \206\168 : \226\136\128 {T}, Ref T \226\134\146 Model T \226\134\146 PROP.
Time #[global]
Instance big_sepDM_timeless  \206\166 m:
 (Timeless (emp : PROP)%I
  \226\134\146 (\226\136\128 a k x, Timeless (\206\166 a k x)) \226\134\146 Timeless ([\226\136\151 dmap] k\226\134\166x \226\136\136 m, \206\166 _ k x)).
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclintros@0> eapply big_sepL_timeless =>_ 
  [? ?]; apply _).
Time Qed.
Time End sprop.
Time Section big_op.
Time Context `{Monoid M o}.
Time Implicit Type xs : list M.
Time Infix "`o`" := o (at level 50, left associativity).
Time Section gset.
Time Context `{Countable A} `{Countable B}.
Time Implicit Type X : gset A.
Time Implicit Type f : A \226\134\146 M.
Time
Lemma set_map_union_singleton (h : A \226\134\146 B) X x :
  set_map h ({[x]} \226\136\170 X) = ({[h x]} \226\136\170 set_map h X : gset B).
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma big_opS_fmap (h : A \226\134\146 B) X (g : B \226\134\146 M) :
  (\226\136\128 x y, h x = h y \226\134\146 x = y)
  \226\134\146 ([^o set] x \226\136\136 set_map h X, g x) \226\137\161 ([^o set] x \226\136\136 X, g (h x)).
Time Proof.
Time (intros Hinj).
Time
(<ssreflect_plugin::ssrtclintros@0>
 induction X as [| x X ? IH] using set_ind_L =>//=).
Time rewrite set_map_union_singleton.
Time rewrite ?big_opS_union.
Time -
Time rewrite ?big_opS_singleton IH //.
Time -
Time set_solver.
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> cut (h x \226\136\137 (set_map h X : gset _)) ; first 
 by set_solver).
Time (intros (x', (Heq, Hin))%elem_of_map).
Time (apply Hinj in Heq).
Time subst.
Time auto.
Time Qed.
Time End gset.
Time End big_op.
Time Section bi_big_op.
Time Context {PROP : bi}.
Time Implicit Types P Q : PROP.
Time Implicit Types Ps Qs : list PROP.
Time Implicit Type A : Type.
Time Section map.
Time Context `{Countable K} {A : Type}.
Time Implicit Type m : gmap K A.
Time Implicit Types \206\166 \206\168 : K \226\134\146 A \226\134\146 PROP.
Time
Lemma big_sepM_mono_with_inv' P \206\166 \206\168 m :
  (\226\136\128 k x, m !! k = Some x \226\134\146 P \226\136\151 \206\166 k x \226\138\162 P \226\136\151 \206\168 k x)
  \226\134\146 P \226\136\151 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) \226\138\162 P \226\136\151 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\168 k x).
Time Proof.
Time (intros Hwand).
Time
(induction m as [| i x m ? IH] using map_ind; auto using big_sepM_empty').
Time rewrite ?big_sepM_insert //.
Time iIntros "(HP&Hi&H)".
Time iDestruct (Hwand with "[$]") as "(?&$)".
Time {
Time by rewrite lookup_insert.
Time }
Time (iApply IH; eauto).
Time {
Time iIntros ( k x' Hlookup ).
Time iApply Hwand.
Time (destruct (decide (i = k))).
Time -
Time subst.
Time congruence.
Time -
Time rewrite lookup_insert_ne //.
Time }
Time iFrame.
Time Qed.
Time
Lemma big_sepM_mono_with_inv P \206\166 \206\168 m :
  (\226\136\128 k x, m !! k = Some x \226\134\146 P \226\136\151 \206\166 k x \226\138\162 P \226\136\151 \206\168 k x)
  \226\134\146 P -\226\136\151 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\166 k x) -\226\136\151 P \226\136\151 ([\226\136\151 map] k\226\134\166x \226\136\136 m, \206\168 k x).
Time Proof.
Time iIntros ( ? ) "HP H".
Time (iApply (big_sepM_mono_with_inv' with "[HP H]"); eauto).
Time iFrame.
Time Qed.
Time End map.
Time End bi_big_op.
