Time From iris.algebra Require Export big_op.
Time From iris.algebra Require Export frac agree local_updates.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type*".
Time #[local]
Existing Instances
 monoid_ne, monoid_assoc, monoid_comm, monoid_left_id, monoid_right_id, monoid_proper, monoid_homomorphism_rel_po, monoid_homomorphism_rel_proper, monoid_homomorphism_op_proper, monoid_homomorphism_ne, weak_monoid_homomorphism_proper.
Time Require Import EqualDec.
Time Require Export SemanticsHelpers.
Time From iris.algebra Require Import proofmode_classes.
Time From iris.base_logic Require Import base_logic.
Time From iris.proofmode Require Import tactics.
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
Time Set Default Proof Using "Type".
Time Qed.
Time
Record auth (A : Type) :=
 Auth {auth_auth_proj : option (frac * agree A); auth_frag_proj : A}.
Time Add Printing Constructor auth.
Time Arguments Auth {_} _ _.
Time Arguments auth_auth_proj {_} _.
Time Arguments auth_frag_proj {_} _.
Time Instance: (Params (@Auth) 1) := { }.
Time Instance: (Params (@auth_auth_proj) 1) := { }.
Time Instance: (Params (@auth_frag_proj) 1) := { }.
Time Definition auth_frag {A : ucmraT} (a : A) : auth A := Auth None a.
Time
Definition auth_auth {A : ucmraT} (q : Qp) (a : A) : 
  auth A := Auth (Some (q, to_agree a)) \206\181.
Time Typeclasses Opaque auth_auth auth_frag.
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
Time Instance: (Params (@auth_frag) 1) := { }.
Time Instance: (Params (@auth_auth) 1) := { }.
Time Notation "\226\151\175 a" := (auth_frag a) (at level 20).
Time
Notation "\226\151\143{ q } a" := (auth_auth q a) (at level 20, format "\226\151\143{ q }  a").
Time Notation "\226\151\143 a" := (auth_auth 1 a) (at level 20).
Time Section ofe.
Time Context {A : ofeT}.
Time Implicit Type a : option (frac * agree A).
Time Implicit Type b : A.
Time Implicit Types x y : auth A.
Time
Instance auth_equiv : (Equiv (auth A)) :=
 (\206\187 x y,
    auth_auth_proj x \226\137\161 auth_auth_proj y \226\136\167 auth_frag_proj x \226\137\161 auth_frag_proj y).
Time
Instance auth_dist : (Dist (auth A)) :=
 (\206\187 n x y,
    auth_auth_proj x \226\137\161{n}\226\137\161 auth_auth_proj y
    \226\136\167 auth_frag_proj x \226\137\161{n}\226\137\161 auth_frag_proj y).
Time #[global]Instance Auth_ne : (NonExpansive2 (@Auth A)).
Time Qed.
Time
Lemma big_opDM_proper_map f m1 m2 :
  m1 \226\137\161 m2 \226\134\146 ([^ o dmap] k\226\134\166x \226\136\136 m1, f _ k x) \226\137\161 ([^ o dmap] k\226\134\166x \226\136\136 m2, f _ k x).
Time Proof.
Time (intros Hequiv).
Time Proof.
Time by split.
Time Qed.
Time #[global]
Instance Auth_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@Auth A)).
Time Proof.
Time by split.
Time Qed.
Time #[global]
Instance auth_auth_proj_ne : (NonExpansive (@auth_auth_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time #[global]
Instance auth_auth_proj_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@auth_auth_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time (unfold big_opDM).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite big_opL_permutation ; last  by
 rewrite Hequiv; reflexivity).
Time #[global]
Instance auth_frag_proj_ne : (NonExpansive (@auth_frag_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time #[global]
Instance auth_frag_proj_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@auth_frag_proj A)).
Time Proof.
Time by destruct 1.
Time Qed.
Time Definition auth_ofe_mixin : OfeMixin (auth A).
Time Proof.
Time by apply (iso_ofe_mixin (\206\187 x, (auth_auth_proj x, auth_frag_proj x))).
Time Qed.
Time Canonical Structure authO := OfeT (auth A) auth_ofe_mixin.
Time #[global]
Instance Auth_discrete  a b: (Discrete a \226\134\146 Discrete b \226\134\146 Discrete (Auth a b)).
Time Proof.
Time by intros ? ? [? ?] [? ?]; split; apply : {}discrete {}.
Time Qed.
Time #[global]
Instance auth_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete authO).
Time Proof.
Time (intros ? [? ?]; apply _).
Time Qed.
Time End ofe.
Time (<ssreflect_plugin::ssrtclintros@0> eapply big_opL_proper =>? ? ?).
Time by rewrite Hequiv.
Time Arguments authO : clear implicits.
Time Section cmra.
Time Context {A : ucmraT}.
Time Implicit Types a b : A.
Time Implicit Types x y : auth A.
Time #[global]Instance auth_frag_ne : (NonExpansive (@auth_frag A)).
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance auth_frag_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@auth_frag A)).
Time Proof.
Time done.
Time Qed.
Time #[global]Instance auth_auth_ne  q: (NonExpansive (@auth_auth A q)).
Time Proof.
Time solve_proper.
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
Time Qed.
Time #[global]
Instance auth_auth_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@auth_auth A)).
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
Time solve_proper.
Time Proof.
Time (intros Hnone).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite /big_opDM //= decide_False //=
 ?getDyn_updDyn //= ; last  first).
Time Qed.
Time #[global]
Instance auth_auth_discrete  q a:
 (Discrete a \226\134\146 Discrete (\206\181 : A) \226\134\146 Discrete (\226\151\143{q} a)).
Time Proof.
Time (intros).
Time (apply Auth_discrete; apply _).
Time Qed.
Time #[global]Instance auth_frag_discrete  a: (Discrete a \226\134\146 Discrete (\226\151\175 a)).
Time Proof.
Time (intros).
Time (apply Auth_discrete; apply _).
Time Qed.
Time
Instance auth_valid : (Valid (auth A)) :=
 (\206\187 x,
    match auth_auth_proj x with
    | Some (q, ag) =>
        \226\156\147 q
        \226\136\167 (\226\136\128 n, \226\136\131 a, ag \226\137\161{n}\226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188{n} a \226\136\167 \226\156\147{n} a)
    | None => \226\156\147 auth_frag_proj x
    end).
Time #[global]Arguments auth_valid !_ /.
Time
Instance auth_validN : (ValidN (auth A)) :=
 (\206\187 n x,
    match auth_auth_proj x with
    | Some (q, ag) =>
        \226\156\147{n} q
        \226\136\167 (\226\136\131 a, ag \226\137\161{n}\226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188{n} a \226\136\167 \226\156\147{n} a)
    | None => \226\156\147{n} auth_frag_proj x
    end).
Time #[global]Arguments auth_validN _ !_ /.
Time
Instance auth_pcore : (PCore (auth A)) :=
 (\206\187 x, Some (Auth (core (auth_auth_proj x)) (core (auth_frag_proj x)))).
Time
Instance auth_op : (Op (auth A)) :=
 (\206\187 x y,
    Auth (auth_auth_proj x \226\139\133 auth_auth_proj y)
      (auth_frag_proj x \226\139\133 auth_frag_proj y)).
Time
Definition auth_valid_eq :
  valid =
  (\206\187 x,
     match auth_auth_proj x with
     | Some (q, ag) =>
         \226\156\147 q
         \226\136\167 (\226\136\128 n, \226\136\131 a, ag \226\137\161{n}\226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188{n} a \226\136\167 \226\156\147{n} a)
     | None => \226\156\147 auth_frag_proj x
     end) := eq_refl _.
Time
Definition auth_validN_eq :
  validN =
  (\206\187 n x,
     match auth_auth_proj x with
     | Some (q, ag) =>
         \226\156\147{n} q
         \226\136\167 (\226\136\131 a, ag \226\137\161{n}\226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188{n} a \226\136\167 \226\156\147{n} a)
     | None => \226\156\147{n} auth_frag_proj x
     end) := eq_refl _.
Time
Lemma auth_included (x y : auth A) :
  x \226\137\188 y
  \226\134\148 auth_auth_proj x \226\137\188 auth_auth_proj y \226\136\167 auth_frag_proj x \226\137\188 auth_frag_proj y.
Time Proof.
Time
(split;
  [ intros [[z1 z2] Hz]; split; [ exists z1 | exists z2 ]; apply Hz |  ]).
Time (intros [[z1 Hz1] [z2 Hz2]]; exists (Auth z1 z2); split; auto).
Time Qed.
Time Lemma auth_auth_proj_validN n x : \226\156\147{n} x \226\134\146 \226\156\147{n} auth_auth_proj x.
Time Proof.
Time (destruct x as [[[]| ]]; [ by intros (?, (?, (->, ?))) | done ]).
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
Time Qed.
Time Lemma auth_frag_proj_validN n x : \226\156\147{n} x \226\134\146 \226\156\147{n} auth_frag_proj x.
Time Proof.
Time rewrite auth_validN_eq.
Time (destruct x as [[[]| ]]; [  | done ]).
Time by rewrite big_opDM_empty right_id.
Time naive_solver eauto using cmra_validN_includedN.
Time Qed.
Time Qed.
Time Lemma auth_auth_proj_valid x : \226\156\147 x \226\134\146 \226\156\147 auth_auth_proj x.
Time
Lemma big_opDM_unit m : ([^ o dmap] k\226\134\166y \226\136\136 m, monoid_unit) \226\137\161 (monoid_unit : M).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> etransitivity ; last  eapply big_opL_unit).
Time (unfold big_opDM).
Time (eapply big_opL_proper).
Time (intros ? ?; by destruct getDyn).
Time Qed.
Time Proof.
Time (destruct x as [[[]| ]]; [ intros [? H] | done ]).
Time (split; [ done |  ]).
Time (intros n).
Time by destruct (H n) as [? [-> [? ?]]].
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
Time Qed.
Time Lemma auth_frag_proj_valid x : \226\156\147 x \226\134\146 \226\156\147 auth_frag_proj x.
Time Proof.
Time (destruct x as [[[]| ]]; [ intros [? H] | done ]).
Time (apply cmra_valid_validN).
Time (intros n).
Time (destruct (H n) as [? [? [? ?]]]).
Time naive_solver eauto using cmra_validN_includedN.
Time by rewrite right_id.
Time Qed.
Time Qed.
Time End monoid.
Time Lemma auth_frag_validN n a : \226\156\147{n} (\226\151\175 a) \226\134\148 \226\156\147{n} a.
Time Proof.
Time done.
Time Qed.
Time Lemma auth_auth_frac_validN n q a : \226\156\147{n} (\226\151\143{q} a) \226\134\148 \226\156\147{n} q \226\136\167 \226\156\147{n} a.
Time Proof.
Time rewrite auth_validN_eq /=.
Time (apply and_iff_compat_l).
Time split.
Time -
Time by intros [? [->%to_agree_injN []]].
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
Time -
Time naive_solver eauto using ucmra_unit_leastN.
Time
(<ssreflect_plugin::ssrtclintros@0> apply big_sepDM_mono =>? ? ? ?; apply Hf).
Time Qed.
Time Lemma auth_auth_validN n a : \226\156\147{n} a \226\134\148 \226\156\147{n} (\226\151\143 a).
Time Proof.
Time rewrite auth_auth_frac_validN -cmra_discrete_valid_iff frac_valid'.
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
Time naive_solver.
Time Qed.
Time
Lemma auth_both_frac_validN n q a b :
  \226\156\147{n} (\226\151\143{q} a \226\139\133 \226\151\175 b) \226\134\148 \226\156\147{n} q \226\136\167 b \226\137\188{n} a \226\136\167 \226\156\147{n} a.
Time Proof.
Time rewrite auth_validN_eq /=.
Time (apply and_iff_compat_l).
Time setoid_rewrite (left_id _ _ b).
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
Time split.
Time -
Time by intros [? [->%to_agree_injN]].
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
Time -
Time naive_solver.
Time Qed.
Time Lemma auth_both_validN n a b : \226\156\147{n} (\226\151\143 a \226\139\133 \226\151\175 b) \226\134\148 b \226\137\188{n} a \226\136\167 \226\156\147{n} a.
Time Proof.
Time rewrite auth_both_frac_validN -cmra_discrete_valid_iff frac_valid'.
Time naive_solver.
Time by apply sep_mono_r, wand_intro_l.
Time Qed.
Time
Lemma big_sepDM_lookup {T} \206\166 m (i : Ref T) x `{!Absorbing (\206\166 _ i x)} :
  getDyn m i = Some x \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y) \226\138\162 \206\166 _ i x.
Time Proof.
Time (intros).
Time rewrite big_sepDM_lookup_acc //.
Time Qed.
Time Lemma auth_frag_valid a : \226\156\147 (\226\151\175 a) \226\134\148 \226\156\147 a.
Time Proof.
Time done.
Time Qed.
Time Lemma auth_auth_frac_valid q a : \226\156\147 (\226\151\143{q} a) \226\134\148 \226\156\147 q \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite auth_valid_eq /=.
Time (apply and_iff_compat_l).
Time split.
Time -
Time (intros H').
Time (apply cmra_valid_validN).
Time (intros n).
Time by destruct (H' n) as [? [->%to_agree_injN [? ?]]].
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
Time -
Time (intros).
Time exists a.
Time (split; [ done |  ]).
Time (split; by [ apply ucmra_unit_leastN | apply cmra_valid_validN ]).
Time Qed.
Time Lemma auth_auth_valid a : \226\156\147 (\226\151\143 a) \226\134\148 \226\156\147 a.
Time Proof.
Time rewrite auth_auth_frac_valid frac_valid'.
Time naive_solver.
Time Qed.
Time Qed.
Time
Lemma big_sepDM_insert_override_2 {T} \206\166 m (i : Ref T) 
  x x' :
  getDyn m i = Some x
  \226\134\146 ([\226\136\151 dmap] k\226\134\166y \226\136\136 m, \206\166 _ k y)
    \226\138\162 (\206\166 _ i x -\226\136\151 \206\166 _ i x')
      -\226\136\151 [\226\136\151 dmap] k\226\134\166y \226\136\136 updDyn (dec:=dec) i x' m, 
      \206\166 _ k y.
Time
Lemma auth_both_frac_valid_2 q a b : \226\156\147 q \226\134\146 \226\156\147 a \226\134\146 b \226\137\188 a \226\134\146 \226\156\147 (\226\151\143{q} a \226\139\133 \226\151\175 b).
Time Proof.
Time (intros Val1 Val2 Incl).
Time rewrite auth_valid_eq /=.
Time (split; [ done |  ]).
Time (intros n).
Time exists a.
Time (split; [ done |  ]).
Time Proof.
Time (intros ?).
Time (apply wand_intro_l).
Time (rewrite {+1}big_sepDM_delete //; rewrite assoc wand_elim_l).
Time rewrite left_id.
Time (split; by [ apply cmra_included_includedN | apply cmra_valid_validN ]).
Time Qed.
Time Lemma auth_both_valid_2 a b : \226\156\147 a \226\134\146 b \226\137\188 a \226\134\146 \226\156\147 (\226\151\143 a \226\139\133 \226\151\175 b).
Time Proof.
Time (intros ? ?).
Time by apply auth_both_frac_valid_2.
Time Qed.
Time
Lemma auth_valid_discrete `{!CmraDiscrete A} x :
  \226\156\147 x
  \226\134\148 match auth_auth_proj x with
    | Some (q, ag) =>
        \226\156\147 q \226\136\167 (\226\136\131 a, ag \226\137\161 to_agree a \226\136\167 auth_frag_proj x \226\137\188 a \226\136\167 \226\156\147 a)
    | None => \226\156\147 auth_frag_proj x
    end.
Time Proof.
Time rewrite auth_valid_eq.
Time (destruct x as [[[? ?]| ] ?]; simpl; [  | done ]).
Time setoid_rewrite  <- cmra_discrete_included_iff.
Time rewrite -updDyn_deleteDyn big_sepDM_updDyn ?getDyn_deleteDyn //.
Time setoid_rewrite  <- (discrete_iff _ a).
Time setoid_rewrite  <- cmra_discrete_valid_iff.
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
Time naive_solver eauto using O.
Time (apply sep_mono; [ done |  ]).
Time (<ssreflect_plugin::ssrtclintros@0> apply forall_intro =>x').
Time rewrite -updDyn_deleteDyn big_sepDM_updDyn ?getDyn_deleteDyn //.
Time Qed.
Time
Lemma auth_both_frac_valid `{!CmraDiscrete A} q a 
  b : \226\156\147 (\226\151\143{q} a \226\139\133 \226\151\175 b) \226\134\148 \226\156\147 q \226\136\167 b \226\137\188 a \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite auth_valid_discrete /=.
Time (apply and_iff_compat_l).
Time setoid_rewrite (left_id _ _ b).
Time split.
Time -
Time by intros [? [->%to_agree_inj]].
Time -
Time naive_solver.
Time Qed.
Time
Lemma auth_both_valid `{!CmraDiscrete A} a b : \226\156\147 (\226\151\143 a \226\139\133 \226\151\175 b) \226\134\148 b \226\137\188 a \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite auth_both_frac_valid frac_valid'.
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
Time naive_solver.
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
Time Qed.
Time Lemma auth_cmra_mixin : CmraMixin (auth A).
Time }
Time rewrite /big_opDM big_sepL_forall.
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time by intros n x y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
Time iIntros "H".
Time iIntros ( a (k, x) (v, Heq)%dynMap_dom_lookup ).
Time rewrite Heq.
Time by iApply "H".
Time Qed.
Time -
Time by intros n y1 y2 [Hy Hy']; split; simpl; rewrite ?Hy ?Hy'.
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
Time -
Time (intros n [x a] [y b] [Hx Ha]; simpl in *).
Time iIntros "H".
Time (unshelve by iApply ("Himpl" $! a k v _); eauto).
Time rewrite !auth_validN_eq.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct Hx as [x y Hx| ] ; first 
  destruct Hx as [? Hx]; [ destruct x, y |  ]; intros VI; ofe_subst; auto).
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
Time -
Time
(intros [[[]| ]]; rewrite /= ?auth_valid_eq ?auth_validN_eq /=
  ?cmra_valid_validN; naive_solver).
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
Time -
Time
(intros n [[[]| ]]; rewrite !auth_validN_eq /=; naive_solver eauto
  using dist_S, cmra_includedN_S, cmra_validN_S).
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
Time by split; simpl; rewrite assoc.
Time -
Time rewrite ?big_opS_singleton IH //.
Time -
Time by split; simpl; rewrite comm.
Time -
Time set_solver.
Time -
Time by split; simpl; rewrite ?cmra_core_l.
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> cut (h x \226\136\137 (set_map h X : gset _)) ; first 
 by set_solver).
Time -
Time by split; simpl; rewrite ?cmra_core_idemp.
Time (intros (x', (Heq, Hin))%elem_of_map).
Time -
Time (intros ? ?; rewrite !auth_included; intros [? ?]).
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
Time by split; simpl; apply : {}cmra_core_mono {}.
Time -
Time (assert (\226\136\128 n (a b1 b2 : A), b1 \226\139\133 b2 \226\137\188{n} a \226\134\146 b1 \226\137\188{n} a)).
Time {
Time (intros n a b1 b2 <-; apply cmra_includedN_l).
Time Proof.
Time (intros Hwand).
Time
(induction m as [| i x m ? IH] using map_ind; auto using big_sepM_empty').
Time }
Time
(intros n [[[q1 a1]| ] b1] [[[q2 a2]| ] b2]; rewrite auth_validN_eq /=;
  try naive_solver eauto using cmra_validN_op_l, cmra_validN_includedN).
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
Time (intros [? [a [Eq [? Valid]]]]).
Time (assert (Eq' : a1 \226\137\161{n}\226\137\161 a2)).
Time {
Time by apply agree_op_invN; rewrite Eq.
Time }
Time (split; [ naive_solver eauto using cmra_validN_op_l |  ]).
Time exists a.
Time rewrite -Eq -Eq' agree_idemp.
Time naive_solver.
Time -
Time (intros n x y1 y2 ? [? ?]; simpl in *).
Time
(destruct
  (cmra_extend n (auth_auth_proj x) (auth_auth_proj y1) (auth_auth_proj y2))
  as (ea1, (ea2, (?, (?, ?)))); auto using auth_auth_proj_validN).
Time
(destruct
  (cmra_extend n (auth_frag_proj x) (auth_frag_proj y1) (auth_frag_proj y2))
  as (b1, (b2, (?, (?, ?)))); auto using auth_frag_proj_validN).
Time by exists (Auth ea1 b1),(Auth ea2 b2).
Time Qed.
Time Canonical Structure authR := CmraT (auth A) auth_cmra_mixin.
Time #[global]
Instance auth_cmra_discrete : (CmraDiscrete A \226\134\146 CmraDiscrete authR).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time (intros [[[]| ] ?]; rewrite auth_valid_eq auth_validN_eq /=; auto).
Time -
Time setoid_rewrite  <- cmra_discrete_included_iff.
Time rewrite -cmra_discrete_valid_iff.
Time setoid_rewrite  <- cmra_discrete_valid_iff.
Time setoid_rewrite  <- (discrete_iff _ a).
Time tauto.
Time -
Time by rewrite -cmra_discrete_valid_iff.
Time Qed.
Time Instance auth_empty : (Unit (auth A)) := (Auth \206\181 \206\181).
Time Lemma auth_ucmra_mixin : UcmraMixin (auth A).
Time Proof.
Time (split; simpl).
Time -
Time rewrite auth_valid_eq /=.
Time (apply ucmra_unit_valid).
Time -
Time by intros x; constructor; rewrite /= left_id.
Time -
Time (do 2 constructor; [ done | apply (core_id_core _) ]).
Time Qed.
Time Canonical Structure authUR := UcmraT (auth A) auth_ucmra_mixin.
Time #[global]Instance auth_frag_core_id  a: (CoreId a \226\134\146 CoreId (\226\151\175 a)).
Time Proof.
Time (do 2 constructor; simpl; auto).
Time by apply core_id_core.
Time Qed.
Time Lemma auth_frag_op a b : \226\151\175 (a \226\139\133 b) = \226\151\175 a \226\139\133 \226\151\175 b.
Time Proof.
Time done.
Time Qed.
Time Lemma auth_frag_mono a b : a \226\137\188 b \226\134\146 \226\151\175 a \226\137\188 \226\151\175 b.
Time Proof.
Time (intros [c ->]).
Time rewrite auth_frag_op.
Time (apply cmra_included_l).
Time Qed.
Time #[global]
Instance auth_frag_sep_homomorphism :
 (MonoidHomomorphism op op (\226\137\161) (@auth_frag A)).
Time Proof.
Time by split; [ split; try apply _ |  ].
Time Qed.
Time
Lemma auth_both_frac_op q a b : Auth (Some (q, to_agree a)) b \226\137\161 \226\151\143{q} a \226\139\133 \226\151\175 b.
Time Proof.
Time by rewrite /op /auth_op /= left_id.
Time Qed.
Time Lemma auth_both_op a b : Auth (Some (1%Qp, to_agree a)) b \226\137\161 \226\151\143 a \226\139\133 \226\151\175 b.
Time Proof.
Time by rewrite auth_both_frac_op.
Time Qed.
Time Lemma auth_auth_frac_op p q a : \226\151\143{p + q} a \226\137\161 \226\151\143{p} a \226\139\133 \226\151\143{q} a.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; split; simpl ; last  by rewrite
 left_id).
Time by rewrite -Some_op -pair_op agree_idemp.
Time Qed.
Time
Lemma auth_auth_frac_op_invN n p a q b : \226\156\147{n} (\226\151\143{p} a \226\139\133 \226\151\143{q} b) \226\134\146 a \226\137\161{n}\226\137\161 b.
Time Proof.
Time rewrite /op /auth_op /= left_id -Some_op -pair_op auth_validN_eq /=.
Time (intros (?, (?, (Eq, (?, ?))))).
Time (apply to_agree_injN, agree_op_invN).
Time by rewrite Eq.
Time Qed.
Time Lemma auth_auth_frac_op_inv p a q b : \226\156\147 (\226\151\143{p} a \226\139\133 \226\151\143{q} b) \226\134\146 a \226\137\161 b.
Time Proof.
Time (intros ?).
Time (apply equiv_dist).
Time (intros n).
Time by eapply auth_auth_frac_op_invN, cmra_valid_validN.
Time Qed.
Time
Lemma auth_auth_frac_op_invL `{!LeibnizEquiv A} q 
  a p b : \226\156\147 (\226\151\143{p} a \226\139\133 \226\151\143{q} b) \226\134\146 a = b.
Time Proof.
Time by intros ?%leibniz_equiv%auth_auth_frac_op_inv.
Time Qed.
Time
Lemma auth_equivI {M} x y :
  x \226\137\161 y
  \226\138\163\226\138\162@{ uPredI M} auth_auth_proj x \226\137\161 auth_auth_proj y
                 \226\136\167 auth_frag_proj x \226\137\161 auth_frag_proj y.
Time Proof.
Time by uPred.unseal.
Time Qed.
Time
Lemma auth_validI {M} x :
  \226\156\147 x
  \226\138\163\226\138\162@{ uPredI M} match auth_auth_proj x with
                 | Some (q, ag) =>
                     \226\156\147 q
                     \226\136\167 (\226\136\131 a,
                          ag \226\137\161 to_agree a
                          \226\136\167 (\226\136\131 b, a \226\137\161 auth_frag_proj x \226\139\133 b) \226\136\167 \226\156\147 a)
                 | None => \226\156\147 auth_frag_proj x
                 end.
Time Proof.
Time uPred.unseal.
Time by destruct x as [[[]| ]].
Time Qed.
Time Lemma auth_frag_validI {M} (a : A) : \226\156\147 (\226\151\175 a) \226\138\163\226\138\162@{ uPredI M} \226\156\147 a.
Time Proof.
Time by rewrite auth_validI.
Time Qed.
Time
Lemma auth_both_validI {M} q (a b : A) :
  \226\156\147 (\226\151\143{q} a \226\139\133 \226\151\175 b) \226\138\163\226\138\162@{ uPredI M} \226\156\147 q \226\136\167 (\226\136\131 c, a \226\137\161 b \226\139\133 c) \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite -auth_both_frac_op auth_validI /=.
Time (apply bi.and_proper; [ done |  ]).
Time setoid_rewrite agree_equivI.
Time iSplit.
Time -
Time iDestruct 1 as ( a' ) "[#Eq [H V]]".
Time iDestruct "H" as ( b' ) "H".
Time iRewrite - "Eq" in "H".
Time iRewrite - "Eq" in "V".
Time auto.
Time -
Time iDestruct 1 as "[H V]".
Time iExists a.
Time auto.
Time Qed.
Time
Lemma auth_auth_validI {M} q (a b : A) : \226\156\147 (\226\151\143{q} a) \226\138\163\226\138\162@{ uPredI M} \226\156\147 q \226\136\167 \226\156\147 a.
Time Proof.
Time rewrite auth_validI /=.
Time (apply bi.and_proper; [ done |  ]).
Time setoid_rewrite agree_equivI.
Time iSplit.
Time -
Time iDestruct 1 as ( a' ) "[Eq [_ V]]".
Time by iRewrite - "Eq" in "V".
Time -
Time iIntros "V".
Time iExists a.
Time (iSplit; [ done |  ]).
Time (iSplit; [  | done ]).
Time iExists a.
Time by rewrite left_id.
Time Qed.
Time
Lemma auth_update a b a' b' :
  (a, b) ~l~> (a', b') \226\134\146 \226\151\143 a \226\139\133 \226\151\175 b ~~> \226\151\143 a' \226\139\133 \226\151\175 b'.
Time Proof.
Time (intros Hup; apply cmra_total_update).
Time
(move  {}=>n [[[? ?]|] bf1] [/= VL [a0 [Eq [[bf2 Ha] VL2]]]]; do 2 red;
  simpl in *).
Time +
Time exfalso.
Time move : {}VL {} =>/frac_valid'.
Time rewrite frac_op'.
Time by apply Qp_not_plus_q_ge_1.
Time +
Time (split; [ done |  ]).
Time (apply to_agree_injN in Eq).
Time
(move : {}Ha {}; <ssreflect_plugin::ssrtclintros@0> rewrite !left_id -assoc
  =>Ha).
Time (destruct (Hup n (Some (bf1 \226\139\133 bf2))); [ by rewrite Eq.. | idtac ]).
Time (simpl in *).
Time exists a'.
Time (split; [ done |  ]).
Time (split; [  | done ]).
Time exists bf2.
Time by rewrite left_id -assoc.
Time Qed.
Time
Lemma auth_update_alloc a a' b' : (a, \206\181) ~l~> (a', b') \226\134\146 \226\151\143 a ~~> \226\151\143 a' \226\139\133 \226\151\175 b'.
Time Proof.
Time (intros).
Time rewrite -(right_id _ _ (\226\151\143 a)).
Time by apply auth_update.
Time Qed.
Time Lemma auth_update_auth a a' b' : (a, \206\181) ~l~> (a', b') \226\134\146 \226\151\143 a ~~> \226\151\143 a'.
Time Proof.
Time (intros).
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; first  exact : {}auth_update_alloc
 {}).
Time exact : {}cmra_update_op_l {}.
Time Qed.
Time Lemma auth_update_core_id a b `{!CoreId b} : b \226\137\188 a \226\134\146 \226\151\143 a ~~> \226\151\143 a \226\139\133 \226\151\175 b.
Time Proof.
Time (intros Hincl).
Time apply : {}auth_update_alloc {}.
Time rewrite -(left_id \206\181 _ b).
Time apply : {}core_id_local_update {}.
Time done.
Time Qed.
Time
Lemma auth_update_dealloc a b a' : (a, b) ~l~> (a', \206\181) \226\134\146 \226\151\143 a \226\139\133 \226\151\175 b ~~> \226\151\143 a'.
Time Proof.
Time (intros).
Time rewrite -(right_id _ _ (\226\151\143 a')).
Time by apply auth_update.
Time Qed.
Time
Lemma auth_local_update (a b0 b1 a' b0' b1' : A) :
  (b0, b1) ~l~> (b0', b1')
  \226\134\146 b0' \226\137\188 a'
    \226\134\146 \226\156\147 a' \226\134\146 (\226\151\143 a \226\139\133 \226\151\175 b0, \226\151\143 a \226\139\133 \226\151\175 b1) ~l~> (\226\151\143 a' \226\139\133 \226\151\175 b0', \226\151\143 a' \226\139\133 \226\151\175 b1').
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !local_update_unital =>Hup ? ? n
 /=).
Time move  {}=>[[[qc ac]|] bc] /auth_both_validN [Le Val] [] /=.
Time -
Time move  {}=>Ha.
Time exfalso.
Time move : {}Ha {}.
Time rewrite right_id -Some_op -pair_op.
Time move  {}=>/Some_dist_inj [/=].
Time (<ssreflect_plugin::ssrtclintros@0> rewrite frac_op' =>Eq _).
Time (apply (Qp_not_plus_q_ge_1 qc)).
Time by rewrite -Eq.
Time -
Time move  {}=>_.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite !left_id =>?).
Time (destruct (Hup n bc) as [Hval' Heq]; eauto using cmra_validN_includedN).
Time rewrite -!auth_both_op auth_validN_eq /=.
Time (split_and !; [ done |  | done ]).
Time exists a'.
Time
(split_and !;
  [ done | by apply cmra_included_includedN | by apply cmra_valid_validN ]).
Time Qed.
Time End cmra.
Time Arguments authR : clear implicits.
Time Arguments authUR : clear implicits.
Time
Instance is_op_auth_frag  {A : ucmraT} (a b1 b2 : A):
 (IsOp a b1 b2 \226\134\146 IsOp' (\226\151\175 a) (\226\151\175 b1) (\226\151\175 b2)).
Time Proof.
Time done.
Time Qed.
Time
Instance is_op_auth_auth_frac  {A : ucmraT} (q q1 q2 : frac) 
 (a : A): (IsOp q q1 q2 \226\134\146 IsOp' (\226\151\143{q} a) (\226\151\143{q1} a) (\226\151\143{q2} a)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp =>{+}->).
Time by rewrite -auth_auth_frac_op.
Time Qed.
Time
Definition auth_map {A} {B} (f : A \226\134\146 B) (x : auth A) : 
  auth B :=
  Auth (prod_map id (agree_map f) <$> auth_auth_proj x)
    (f (auth_frag_proj x)).
Time Lemma auth_map_id {A} (x : auth A) : auth_map id x = x.
Time Proof.
Time (destruct x as [[[]| ]]; by rewrite // /auth_map /= agree_map_id).
Time Qed.
Time
Lemma auth_map_compose {A} {B} {C} (f : A \226\134\146 B) (g : B \226\134\146 C) 
  (x : auth A) : auth_map (g \226\136\152 f) x = auth_map g (auth_map f x).
Time Proof.
Time (destruct x as [[[]| ]]; by rewrite // /auth_map /= agree_map_compose).
Time Qed.
Time
Lemma auth_map_ext {A B : ofeT} (f g : A \226\134\146 B) `{!NonExpansive f} 
  x : (\226\136\128 x, f x \226\137\161 g x) \226\134\146 auth_map f x \226\137\161 auth_map g x.
Time Proof.
Time (constructor; simpl; auto).
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_equiv_ext =>a; by
  rewrite /prod_map /= agree_map_ext).
Time Qed.
Time
Instance auth_map_ne  {A B : ofeT} (f : A -> B) `{Hf : !NonExpansive f}:
 (NonExpansive (auth_map f)).
Time Proof.
Time (intros n [? ?] [? ?] [? ?]; split; simpl in *; [  | by apply Hf ]).
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_ne; [  | done ] =>x y
 ?).
Time (apply prod_map_ne; [ done |  | done ]).
Time by apply agree_map_ne.
Time Qed.
Time
Instance auth_map_cmra_morphism  {A B : ucmraT} (f : A \226\134\146 B):
 (CmraMorphism f \226\134\146 CmraMorphism (auth_map f)).
Time Proof.
Time (split; try apply _).
Time -
Time
(intros n [[[? ?]| ] b]; rewrite !auth_validN_eq;
  [ 
  | naive_solver
  eauto
  using cmra_morphism_monotoneN, cmra_morphism_validN ]).
Time (intros [? [a' [Eq [? ?]]]]).
Time (split; [ done |  ]).
Time exists (f a').
Time rewrite -agree_map_to_agree -Eq.
Time naive_solver eauto using cmra_morphism_monotoneN, cmra_morphism_validN.
Time -
Time (intros [? ?]).
Time (apply Some_proper; rewrite /auth_map /=).
Time by f_equiv; rewrite /= cmra_morphism_core.
Time -
Time
(intros [[[? ?]| ] ?] [[[? ?]| ] ?];
  try <ssreflect_plugin::ssrtclintros@0> apply Auth_proper =>//=; by rewrite
  cmra_morphism_op).
Time Qed.
Time
Definition authO_map {A} {B} (f : A -n> B) : authO A -n> authO B :=
  OfeMor (auth_map f).
Time Lemma authO_map_ne A B : NonExpansive (@authO_map A B).
Time Proof.
Time
(intros n f f' Hf [[[]| ]]; repeat constructor; try naive_solver;
  apply agreeO_map_ne; auto).
Time Qed.
Time #[program]
Definition authRF (F : urFunctor) : rFunctor :=
  {|
  rFunctor_car := fun A _ B _ => authR (urFunctor_car F A B);
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  authO_map (urFunctor_map F fg) |}.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply authO_map_ne, urFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(auth_map_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply (auth_map_ext _ _) =>y;
  apply urFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -auth_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply (auth_map_ext _ _) =>y;
  apply urFunctor_compose).
Time Qed.
Time
Instance authRF_contractive  F:
 (urFunctorContractive F \226\134\146 rFunctorContractive (authRF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply authO_map_ne, urFunctor_contractive.
Time Qed.
Time #[program]
Definition authURF (F : urFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => authUR (urFunctor_car F A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   authO_map (urFunctor_map F fg) |}.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply authO_map_ne, urFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(auth_map_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply (auth_map_ext _ _) =>y;
  apply urFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -auth_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply (auth_map_ext _ _) =>y;
  apply urFunctor_compose).
Time Qed.
Time
Instance authURF_contractive  F:
 (urFunctorContractive F \226\134\146 urFunctorContractive (authURF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply authO_map_ne, urFunctor_contractive.
Time Qed.
