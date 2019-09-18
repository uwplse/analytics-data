Time From iris.algebra Require Export cmra.
Time From stdpp Require Export list gmap.
Time From iris.algebra Require Import updates local_updates.
Time From iris.base_logic Require Import base_logic.
Time From iris.algebra Require Import proofmode_classes.
Time Set Default Proof Using "Type".
Time Section cofe.
Time Context `{Countable K} {A : ofeT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time
Instance gmap_dist : (Dist (gmap K A)) :=
 (\206\187 n m1 m2, \226\136\128 i, m1 !! i \226\137\161{n}\226\137\161 m2 !! i).
Time Definition gmap_ofe_mixin : OfeMixin (gmap K A).
Time Proof.
Time split.
Time -
Time (intros m1 m2; split).
Time +
Time by intros Hm n k; apply equiv_dist.
Time +
Time (intros Hm k; apply equiv_dist; intros n; apply Hm).
Time -
Time (intros n; split).
Time +
Time by intros m k.
Time +
Time by intros m1 m2 ? k.
Time +
Time by intros m1 m2 m3 ? ? k; trans m2 !! k.
Time -
Time by intros n m1 m2 ? k; apply dist_S.
Time Qed.
Time Canonical Structure gmapO : ofeT := OfeT (gmap K A) gmap_ofe_mixin.
Time #[program]
Definition gmap_chain (c : chain gmapO) (k : K) : 
  chain (optionO A) := {| chain_car := fun n => c n !! k |}.
Time Next Obligation.
Time by intros c k n i ?; apply (chain_cauchy c).
Time Qed.
Time
Definition gmap_compl `{Cofe A} : Compl gmapO :=
  \206\187 c, map_imap (\206\187 i _, compl (gmap_chain c i)) (c 0).
Time #[global, program]
Instance gmap_cofe  `{Cofe A}: (Cofe gmapO) := {| compl := gmap_compl |}.
Time Next Obligation.
Time (intros ? n c k).
Time rewrite /compl /gmap_compl map_lookup_imap.
Time
(feed inversion \206\187 H, chain_cauchy c 0 n H k; simplify_option_eq; auto
  with lia).
Time by rewrite conv_compl /=; apply reflexive_eq.
Time Qed.
Time #[global]
Instance gmap_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete gmapO).
Time Proof.
Time (intros ? m m' ? i).
Time by apply (discrete _).
Time Qed.
Time #[global]Instance gmapO_leibniz : (LeibnizEquiv A \226\134\146 LeibnizEquiv gmapO).
Time Proof.
Time (intros; change_no_check (LeibnizEquiv (gmap K A)); apply _).
Time Qed.
Time #[global]
Instance lookup_ne  k: (NonExpansive (lookup k : gmap K A \226\134\146 option A)).
Time Proof.
Time by intros m1 m2.
Time Qed.
Time #[global]
Instance lookup_proper  k:
 (Proper ((\226\137\161) ==> (\226\137\161)) (lookup k : gmap K A \226\134\146 option A)) := _.
Time #[global]
Instance alter_ne  f k n:
 (Proper (dist n ==> dist n) f \226\134\146 Proper (dist n ==> dist n) (alter f k)).
Time Proof.
Time (intros ? m m' Hm k').
Time by destruct (decide (k = k')); simplify_map_eq; rewrite (Hm k').
Time Qed.
Time #[global]
Instance insert_ne  i: (NonExpansive2 (insert (M:=gmap K A) i)).
Time Proof.
Time
(intros n x y ? m m' ? j; destruct (decide (i = j)); simplify_map_eq;
  [ by constructor | by apply lookup_ne ]).
Time Qed.
Time #[global]
Instance singleton_ne  i: (NonExpansive (singletonM i : A \226\134\146 gmap K A)).
Time Proof.
Time by intros ? ? ? ?; apply insert_ne.
Time Qed.
Time #[global]Instance delete_ne  i: (NonExpansive (delete (M:=gmap K A) i)).
Time Proof.
Time
(intros n m m' ? j; destruct (decide (i = j)); simplify_map_eq;
  [ by constructor | by apply lookup_ne ]).
Time Qed.
Time #[global]Instance gmap_empty_discrete : (Discrete (\226\136\133 : gmap K A)).
Time Proof.
Time (intros m Hm i; specialize (Hm i); rewrite lookup_empty in  {} Hm |- *).
Time (inversion_clear Hm; constructor).
Time Qed.
Time #[global]
Instance gmap_lookup_discrete  m i: (Discrete m \226\134\146 Discrete (m !! i)).
Time Proof.
Time (intros ? [x| ] Hx; [  | by symmetry; apply : {}discrete {} ]).
Time
(assert (m \226\137\161{0}\226\137\161 <[i:=x]> m) by by
  symmetry in Hx; inversion Hx; ofe_subst; rewrite insert_id).
Time by rewrite (discrete m (<[i:=x]> m)) // lookup_insert.
Time Qed.
Time #[global]
Instance gmap_insert_discrete  m i x:
 (Discrete x \226\134\146 Discrete m \226\134\146 Discrete (<[i:=x]> m)).
Time Proof.
Time (intros ? ? m' Hm j; destruct (decide (i = j)); simplify_map_eq).
Time {
Time by apply : {}discrete {}; rewrite -Hm lookup_insert.
Time }
Time by apply : {}discrete {}; rewrite -Hm lookup_insert_ne.
Time Qed.
Time #[global]
Instance gmap_singleton_discrete  i x:
 (Discrete x \226\134\146 Discrete ({[i := x]} : gmap K A)) := _.
Time Lemma insert_idN n m i x : m !! i \226\137\161{n}\226\137\161 Some x \226\134\146 <[i:=x]> m \226\137\161{n}\226\137\161 m.
Time Proof.
Time (intros (y', (?, ->))%dist_Some_inv_r').
Time by rewrite insert_id.
Time Qed.
Time End cofe.
Time Arguments gmapO _ {_} {_} _.
Time Section cmra.
Time Context `{Countable K} {A : cmraT}.
Time Implicit Type m : gmap K A.
Time Instance gmap_unit : (Unit (gmap K A)) := (\226\136\133 : gmap K A).
Time Instance gmap_op : (Op (gmap K A)) := (merge op).
Time Instance gmap_pcore : (PCore (gmap K A)) := (\206\187 m, Some (omap pcore m)).
Time Instance gmap_valid : (Valid (gmap K A)) := (\206\187 m, \226\136\128 i, \226\156\147 (m !! i)).
Time
Instance gmap_validN : (ValidN (gmap K A)) := (\206\187 n m, \226\136\128 i, \226\156\147{n} (m !! i)).
Time Lemma lookup_op m1 m2 i : (m1 \226\139\133 m2) !! i = m1 !! i \226\139\133 m2 !! i.
Time Proof.
Time by apply lookup_merge.
Time Qed.
Time Lemma lookup_core m i : core m !! i = core (m !! i).
Time Proof.
Time by apply lookup_omap.
Time Qed.
Time
Lemma lookup_included (m1 m2 : gmap K A) : m1 \226\137\188 m2 \226\134\148 (\226\136\128 i, m1 !! i \226\137\188 m2 !! i).
Time Proof.
Time
(split; [ by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm |  ]).
Time revert m2.
Time
(<ssreflect_plugin::ssrtclintros@0>
 induction m1 as [| i x m Hi IH] using map_ind =>m2 Hm).
Time {
Time exists m2.
Time by rewrite left_id.
Time }
Time (destruct (IH (delete i m2)) as [m2' Hm2']).
Time {
Time (intros j).
Time (move : {}(Hm j) {}; destruct (decide (i = j)) as [->| ]).
Time -
Time (intros _).
Time rewrite Hi.
Time apply : {}ucmra_unit_least {}.
Time -
Time rewrite lookup_insert_ne // lookup_delete_ne //.
Time }
Time (destruct (Hm i) as [my Hi']; simplify_map_eq).
Time
(<ssreflect_plugin::ssrtclintros@0> exists (partial_alter (\206\187 _, my) i m2')
  =>j; destruct (decide (i = j)) as [->| ]).
Time -
Time by rewrite Hi' lookup_op lookup_insert lookup_partial_alter.
Time -
Time move : {}(Hm2' j) {}.
Time
by rewrite !lookup_op lookup_delete_ne // lookup_insert_ne //
 lookup_partial_alter_ne.
Time Qed.
Time Lemma gmap_cmra_mixin : CmraMixin (gmap K A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time (intros n m1 m2 m3 Hm i; by rewrite !lookup_op (Hm i)).
Time -
Time (intros n m1 m2 Hm i; by rewrite !lookup_core (Hm i)).
Time -
Time (intros n m1 m2 Hm ? i; by rewrite -(Hm i)).
Time -
Time (intros m; split).
Time +
Time by intros ? n i; apply cmra_valid_validN.
Time +
Time
(intros Hm i; <ssreflect_plugin::ssrtclintros@0> apply cmra_valid_validN =>n;
  apply Hm).
Time -
Time (intros n m Hm i; apply cmra_validN_S, Hm).
Time -
Time by intros m1 m2 m3 i; rewrite !lookup_op assoc.
Time -
Time by intros m1 m2 i; rewrite !lookup_op comm.
Time -
Time (intros m i).
Time by rewrite lookup_op lookup_core cmra_core_l.
Time -
Time (intros m i).
Time by rewrite !lookup_core cmra_core_idemp.
Time -
Time
(intros m1 m2; <ssreflect_plugin::ssrtclintros@0> rewrite !lookup_included
  =>Hm i).
Time rewrite !lookup_core.
Time by apply cmra_core_mono.
Time -
Time (intros n m1 m2 Hm i; apply cmra_validN_op_l with (m2 !! i)).
Time by rewrite -lookup_op.
Time -
Time (intros n m y1 y2 Hm Heq).
Time
(<ssreflect_plugin::ssrtclseq@0> refine
 ((\206\187 FUN, _) (\206\187 i, cmra_extend n (m !! i) (y1 !! i) (y2 !! i) (Hm i) _)) ;
 last  by rewrite -lookup_op).
Time exists (map_imap (\206\187 i _, projT1 (FUN i)) y1).
Time exists (map_imap (\206\187 i _, proj1_sig (projT2 (FUN i))) y2).
Time
(<ssreflect_plugin::ssrtclintros@0> split; [  | split ] =>i; rewrite
  ?lookup_op !map_lookup_imap; <ssreflect_plugin::ssrtclintros@0>
  destruct (FUN i) as (z1i, (z2i, (Hmi, (Hz1i, Hz2i)))) =>/=).
Time +
Time
(destruct (y1 !! i), (y2 !! i); inversion Hz1i; inversion Hz2i;
  <ssreflect_plugin::ssrtclintros@0> subst =>//).
Time +
Time revert Hz1i.
Time case : {}(y1 !! i) {} =>[?|] //.
Time +
Time revert Hz2i.
Time case : {}(y2 !! i) {} =>[?|] //.
Time Qed.
Time Canonical Structure gmapR := CmraT (gmap K A) gmap_cmra_mixin.
Time #[global]
Instance gmap_cmra_discrete : (CmraDiscrete A \226\134\146 CmraDiscrete gmapR).
Time Proof.
Time (split; [ apply _ |  ]).
Time (intros m ? i).
Time by apply : {}cmra_discrete_valid {}.
Time Qed.
Time Lemma gmap_ucmra_mixin : UcmraMixin (gmap K A).
Time Proof.
Time split.
Time -
Time by intros i; rewrite lookup_empty.
Time -
Time by intros m i; rewrite /= lookup_op lookup_empty (left_id_L None _).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> constructor =>i).
Time by rewrite lookup_omap lookup_empty.
Time Qed.
Time Canonical Structure gmapUR := UcmraT (gmap K A) gmap_ucmra_mixin.
Time
Lemma gmap_equivI {M} m1 m2 : m1 \226\137\161 m2 \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, m1 !! i \226\137\161 m2 !! i).
Time Proof.
Time by uPred.unseal.
Time Qed.
Time Lemma gmap_validI {M} m : \226\156\147 m \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, \226\156\147 (m !! i)).
Time Proof.
Time by uPred.unseal.
Time Qed.
Time End cmra.
Time Arguments gmapR _ {_} {_} _.
Time Arguments gmapUR _ {_} {_} _.
Time Section properties.
Time Context `{Countable K} {A : cmraT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time Implicit Types x y : A.
Time #[global]
Instance lookup_op_homomorphism :
 (MonoidHomomorphism op op (\226\137\161) (lookup i : gmap K A \226\134\146 option A)).
Time Proof.
Time (split; [ split |  ]; try apply _).
Time (intros m1 m2; by rewrite lookup_op).
Time done.
Time Qed.
Time Lemma lookup_opM m1 mm2 i : (m1 \226\139\133? mm2) !! i = m1 !! i \226\139\133 (mm2 \226\137\171= (!!i)).
Time Proof.
Time (destruct mm2; by rewrite /= ?lookup_op ?right_id_L).
Time Qed.
Time
Lemma lookup_validN_Some n m i x : \226\156\147{n} m \226\134\146 m !! i \226\137\161{n}\226\137\161 Some x \226\134\146 \226\156\147{n} x.
Time Proof.
Time by move  {}=>/(_ i) Hm Hi; move : {}Hm {}; rewrite Hi.
Time Qed.
Time Lemma lookup_valid_Some m i x : \226\156\147 m \226\134\146 m !! i \226\137\161 Some x \226\134\146 \226\156\147 x.
Time Proof.
Time move  {}=>Hm Hi.
Time move : {}(Hm i) {}.
Time by rewrite Hi.
Time Qed.
Time Lemma insert_validN n m i x : \226\156\147{n} x \226\134\146 \226\156\147{n} m \226\134\146 \226\156\147{n} <[i:=x]> m.
Time Proof.
Time by intros ? ? j; destruct (decide (i = j)); simplify_map_eq.
Time Qed.
Time Lemma insert_valid m i x : \226\156\147 x \226\134\146 \226\156\147 m \226\134\146 \226\156\147 <[i:=x]> m.
Time Proof.
Time by intros ? ? j; destruct (decide (i = j)); simplify_map_eq.
Time Qed.
Time Lemma singleton_validN n i x : \226\156\147{n} ({[i := x]} : gmap K A) \226\134\148 \226\156\147{n} x.
Time Proof.
Time split.
Time -
Time (move  {}=>/(_ i); by simplify_map_eq).
Time -
Time (intros).
Time (apply insert_validN).
Time done.
Time apply : {}ucmra_unit_validN {}.
Time Qed.
Time Lemma singleton_valid i x : \226\156\147 ({[i := x]} : gmap K A) \226\134\148 \226\156\147 x.
Time Proof.
Time rewrite !cmra_valid_validN.
Time by setoid_rewrite singleton_validN.
Time Qed.
Time Lemma delete_validN n m i : \226\156\147{n} m \226\134\146 \226\156\147{n} delete i m.
Time Proof.
Time (intros Hm j; destruct (decide (i = j)); by simplify_map_eq).
Time Qed.
Time Lemma delete_valid m i : \226\156\147 m \226\134\146 \226\156\147 delete i m.
Time Proof.
Time (intros Hm j; destruct (decide (i = j)); by simplify_map_eq).
Time Qed.
Time
Lemma insert_singleton_op m i x : m !! i = None \226\134\146 <[i:=x]> m = {[i := x]} \226\139\133 m.
Time Proof.
Time
(intros Hi; <ssreflect_plugin::ssrtclintros@0> apply map_eq =>j;
  destruct (decide (i = j)) as [->| ]).
Time -
Time by rewrite lookup_op lookup_insert lookup_singleton Hi right_id_L.
Time -
Time
by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id_L.
Time Qed.
Time
Lemma core_singleton (i : K) (x : A) cx :
  pcore x = Some cx \226\134\146 core ({[i := x]} : gmap K A) = {[i := cx]}.
Time Proof.
Time (apply omap_singleton).
Time Qed.
Time
Lemma core_singleton' (i : K) (x : A) cx :
  pcore x \226\137\161 Some cx \226\134\146 core ({[i := x]} : gmap K A) \226\137\161 {[i := cx]}.
Time Proof.
Time (intros (cx', (?, ->))%equiv_Some_inv_r').
Time by rewrite (core_singleton _ _ cx').
Time Qed.
Time
Lemma op_singleton (i : K) (x y : A) :
  {[i := x]} \226\139\133 {[i := y]} = ({[i := x \226\139\133 y]} : gmap K A).
Time Proof.
Time by apply (merge_singleton _ _ _ x y).
Time Qed.
Time #[global]
Instance is_op_singleton  i a a1 a2:
 (IsOp a a1 a2 \226\134\146 IsOp' ({[i := a]} : gmap K A) {[i := a1]} {[i := a2]}).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /IsOp' /IsOp =>{+}->).
Time by rewrite -op_singleton.
Time Qed.
Time #[global]Instance gmap_core_id  m: ((\226\136\128 x : A, CoreId x) \226\134\146 CoreId m).
Time Proof.
Time (intros; <ssreflect_plugin::ssrtclintros@0> apply core_id_total =>i).
Time rewrite lookup_core.
Time (apply (core_id_core _)).
Time Qed.
Time #[global]
Instance gmap_singleton_core_id  i (x : A): (CoreId x \226\134\146 CoreId {[i := x]}).
Time Proof.
Time (intros).
Time by apply core_id_total, core_singleton'.
Time Qed.
Time
Lemma singleton_includedN n m i x :
  {[i := x]} \226\137\188{n} m \226\134\148 (\226\136\131 y, m !! i \226\137\161{n}\226\137\161 Some y \226\136\167 Some x \226\137\188{n} Some y).
Time Proof.
Time split.
Time -
Time
(move  {}=>[m' /(_ i)]; <ssreflect_plugin::ssrtclintros@0> rewrite lookup_op
  lookup_singleton =>Hi).
Time exists (x \226\139\133? m' !! i).
Time rewrite -Some_op_opM.
Time split.
Time done.
Time (apply cmra_includedN_l).
Time -
Time (intros (y, (Hi, [mz Hy]))).
Time exists (partial_alter (\206\187 _, mz) i m).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time +
Time by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
Time +
Time
by rewrite lookup_op lookup_singleton_ne // lookup_partial_alter_ne //
 left_id.
Time Qed.
Time
Lemma singleton_included m i x :
  {[i := x]} \226\137\188 m \226\134\148 (\226\136\131 y, m !! i \226\137\161 Some y \226\136\167 Some x \226\137\188 Some y).
Time Proof.
Time split.
Time -
Time (move  {}=>[m' /(_ i)]; rewrite lookup_op lookup_singleton).
Time exists (x \226\139\133? m' !! i).
Time rewrite -Some_op_opM.
Time split.
Time done.
Time (apply cmra_included_l).
Time -
Time (intros (y, (Hi, [mz Hy]))).
Time exists (partial_alter (\206\187 _, mz) i m).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time +
Time by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
Time +
Time
by rewrite lookup_op lookup_singleton_ne // lookup_partial_alter_ne //
 left_id.
Time Qed.
Time
Lemma singleton_included_exclusive m i x :
  Exclusive x \226\134\146 \226\156\147 m \226\134\146 {[i := x]} \226\137\188 m \226\134\148 m !! i \226\137\161 Some x.
Time Proof.
Time (intros ? Hm).
Time rewrite singleton_included.
Time (<ssreflect_plugin::ssrtclseq@0> split ; last  by eauto).
Time
(intros (y, (?, ->%(Some_included_exclusive _))); eauto
  using lookup_valid_Some).
Time Qed.
Time #[global]
Instance singleton_cancelable  i x:
 (Cancelable (Some x) \226\134\146 Cancelable {[i := x]}).
Time Proof.
Time (intros ? n m1 m2 Hv EQ j).
Time move : {}(Hv j) {}(EQ j) {}.
Time rewrite !lookup_op.
Time (destruct (decide (i = j)) as [->| ]).
Time -
Time rewrite lookup_singleton.
Time by apply cancelableN.
Time -
Time by rewrite lookup_singleton_ne // !(left_id None _).
Time Qed.
Time #[global]
Instance gmap_cancelable  (m : gmap K A):
 ((\226\136\128 x : A, IdFree x) \226\134\146 (\226\136\128 x : A, Cancelable x) \226\134\146 Cancelable m).
Time Proof.
Time (intros ? ? n m1 m2 ? ? i).
Time (apply (cancelableN (m !! i)); by rewrite -!lookup_op).
Time Qed.
Time
Lemma insert_op m1 m2 i x y :
  <[i:=x \226\139\133 y]> (m1 \226\139\133 m2) = <[i:=x]> m1 \226\139\133 <[i:=y]> m2.
Time Proof.
Time by rewrite (insert_merge (\226\139\133) m1 m2 i (x \226\139\133 y) x y).
Time Qed.
Time
Lemma insert_updateP (P : A \226\134\146 Prop) (Q : gmap K A \226\134\146 Prop) 
  m i x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q (<[i:=y]> m)) \226\134\146 <[i:=x]> m ~~>: Q.
Time Proof.
Time
(intros Hx%option_updateP' HP; <ssreflect_plugin::ssrtclintros@0>
  apply cmra_total_updateP =>n mf Hm).
Time (destruct (Hx n (Some (mf !! i))) as ([y| ], (?, ?)); try done).
Time {
Time by generalize (Hm i); rewrite lookup_op; simplify_map_eq.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists (<[i:=y]> m); split ; first  by auto).
Time
(intros j; move : {}(Hm j) {} =>{Hm}; <ssreflect_plugin::ssrtclintros@0>
  rewrite !lookup_op =>Hm).
Time (destruct (decide (i = j)); simplify_map_eq /=; auto).
Time Qed.
Time
Lemma insert_updateP' (P : A \226\134\146 Prop) m i x :
  x ~~>: P \226\134\146 <[i:=x]> m ~~>: (\206\187 m', \226\136\131 y, m' = <[i:=y]> m \226\136\167 P y).
Time Proof.
Time eauto using insert_updateP.
Time Qed.
Time Lemma insert_update m i x y : x ~~> y \226\134\146 <[i:=x]> m ~~> <[i:=y]> m.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using insert_updateP with subst).
Time Qed.
Time
Lemma singleton_updateP (P : A \226\134\146 Prop) (Q : gmap K A \226\134\146 Prop) 
  i x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q {[i := y]}) \226\134\146 {[i := x]} ~~>: Q.
Time Proof.
Time (apply insert_updateP).
Time Qed.
Time
Lemma singleton_updateP' (P : A \226\134\146 Prop) i x :
  x ~~>: P \226\134\146 {[i := x]} ~~>: (\206\187 m, \226\136\131 y, m = {[i := y]} \226\136\167 P y).
Time Proof.
Time (apply insert_updateP').
Time Qed.
Time
Lemma singleton_update i (x y : A) : x ~~> y \226\134\146 {[i := x]} ~~> {[i := y]}.
Time Proof.
Time (apply insert_update).
Time Qed.
Time Lemma delete_update m i : m ~~> delete i m.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply cmra_total_update =>n mf Hm j;
  destruct (decide (i = j)); subst).
Time -
Time move : {}(Hm j) {}.
Time rewrite !lookup_op lookup_delete left_id.
Time (apply cmra_validN_op_r).
Time -
Time move : {}(Hm j) {}.
Time by rewrite !lookup_op lookup_delete_ne.
Time Qed.
Time Lemma dom_op m1 m2 : dom (gset K) (m1 \226\139\133 m2) = dom _ m1 \226\136\170 dom _ m2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply elem_of_equiv_L =>i; rewrite
  elem_of_union !elem_of_dom).
Time (unfold is_Some; setoid_rewrite lookup_op).
Time (destruct (m1 !! i), (m2 !! i); naive_solver).
Time Qed.
Time Lemma dom_included m1 m2 : m1 \226\137\188 m2 \226\134\146 dom (gset K) m1 \226\138\134 dom _ m2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite lookup_included =>? i; rewrite
  !elem_of_dom).
Time by apply is_Some_included.
Time Qed.
Time Section freshness.
Time #[local]Set Default Proof Using "Type*".
Time Context `{!Infinite K}.
Time
Lemma alloc_updateP_strong (Q : gmap K A \226\134\146 Prop) (I : K \226\134\146 Prop) 
  m x :
  pred_infinite I
  \226\134\146 \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 I i \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time Proof.
Time move  {}=>/(pred_infinite_set I (C:=gset K)) HP ? HQ.
Time (apply cmra_total_updateP).
Time (intros n mf Hm).
Time (destruct (HP (dom (gset K) (m \226\139\133 mf))) as [i [Hi1 Hi2]]).
Time (assert (m !! i = None)).
Time {
Time (eapply (not_elem_of_dom (D:=gset K))).
Time revert Hi2.
Time rewrite dom_op not_elem_of_union.
Time naive_solver.
Time }
Time (exists (<[i:=x]> m); split).
Time -
Time by apply HQ.
Time -
Time rewrite insert_singleton_op //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -assoc -insert_singleton_op ; last 
 by eapply (not_elem_of_dom (D:=gset K))).
Time by apply insert_validN; [ apply cmra_valid_validN |  ].
Time Qed.
Time
Lemma alloc_updateP (Q : gmap K A \226\134\146 Prop) m x :
  \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time Proof.
Time move  {}=>? ?.
Time
(eapply alloc_updateP_strong with (I := \206\187 _, True); eauto
  using pred_infinite_True).
Time Qed.
Time
Lemma alloc_updateP_strong' m x (I : K \226\134\146 Prop) :
  pred_infinite I
  \226\134\146 \226\156\147 x \226\134\146 m ~~>: (\206\187 m', \226\136\131 i, I i \226\136\167 m' = <[i:=x]> m \226\136\167 m !! i = None).
Time Proof.
Time eauto using alloc_updateP_strong.
Time Qed.
Time
Lemma alloc_updateP' m x :
  \226\156\147 x \226\134\146 m ~~>: (\206\187 m', \226\136\131 i, m' = <[i:=x]> m \226\136\167 m !! i = None).
Time Proof.
Time eauto using alloc_updateP.
Time Qed.
Time
Lemma alloc_updateP_cofinite (Q : gmap K A \226\134\146 Prop) 
  (J : gset K) m x :
  \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 i \226\136\137 J \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time Proof.
Time (eapply alloc_updateP_strong).
Time (apply (pred_infinite_set (C:=gset K))).
Time (intros E).
Time exists (fresh (J \226\136\170 E)).
Time (apply not_elem_of_union, is_fresh).
Time Qed.
Time
Lemma alloc_updateP_cofinite' m x (J : gset K) :
  \226\156\147 x \226\134\146 m ~~>: (\206\187 m', \226\136\131 i, (i \226\136\137 J) \226\136\167 m' = <[i:=x]> m \226\136\167 m !! i = None).
Time Proof.
Time eauto using alloc_updateP_cofinite.
Time Qed.
Time End freshness.
Time
Lemma alloc_unit_singleton_updateP (P : A \226\134\146 Prop) 
  (Q : gmap K A \226\134\146 Prop) u i :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q {[i := y]}) \226\134\146 \226\136\133 ~~>: Q.
Time Proof.
Time (intros ? ? Hx HQ).
Time (<ssreflect_plugin::ssrtclintros@0> apply cmra_total_updateP =>n gf Hg).
Time (destruct (Hx n (gf !! i)) as (y, (?, Hy))).
Time {
Time move : {}(Hg i) {}.
Time rewrite !left_id.
Time (case : {}(gf !! i) {} =>[x|]; rewrite /= ?left_id //).
Time (intros; by apply cmra_valid_validN).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists {[i := y]}; split ; first  by auto).
Time (intros i'; destruct (decide (i' = i)) as [->| ]).
Time -
Time rewrite lookup_op lookup_singleton.
Time (move : {}Hy {}; case : {}(gf !! i) {} =>[x|]; rewrite /= ?right_id //).
Time -
Time move : {}(Hg i') {}.
Time by rewrite !lookup_op lookup_singleton_ne // !left_id.
Time Qed.
Time
Lemma alloc_unit_singleton_updateP' (P : A \226\134\146 Prop) 
  u i :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~>: P \226\134\146 \226\136\133 ~~>: (\206\187 m, \226\136\131 y, m = {[i := y]} \226\136\167 P y).
Time Proof.
Time eauto using alloc_unit_singleton_updateP.
Time Qed.
Time
Lemma alloc_unit_singleton_update (u : A) i (y : A) :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~> y \226\134\146 (\226\136\133 : gmap K A) ~~> {[i := y]}.
Time Proof.
Time
(rewrite !cmra_update_updateP; eauto using alloc_unit_singleton_updateP
  with subst).
Time Qed.
Time
Lemma alloc_local_update m1 m2 i x :
  m1 !! i = None \226\134\146 \226\156\147 x \226\134\146 (m1, m2) ~l~> (<[i:=x]> m1, <[i:=x]> m2).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite cmra_valid_validN =>Hi ?).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time (split; auto using insert_validN).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time -
Time
(move : {}(Hm j) {}; <ssreflect_plugin::ssrtclintros@0> rewrite Hi
  symmetry_iff dist_None lookup_op op_None =>- [_ Hj]).
Time by rewrite lookup_op !lookup_insert Hj.
Time -
Time rewrite Hm lookup_insert_ne // !lookup_op lookup_insert_ne //.
Time Qed.
Time
Lemma alloc_singleton_local_update m i x :
  m !! i = None \226\134\146 \226\156\147 x \226\134\146 (m, \226\136\133) ~l~> (<[i:=x]> m, {[i := x]}).
Time Proof.
Time (apply alloc_local_update).
Time Qed.
Time
Lemma insert_local_update m1 m2 i x y x' y' :
  m1 !! i = Some x
  \226\134\146 m2 !! i = Some y
    \226\134\146 (x, y) ~l~> (x', y') \226\134\146 (m1, m2) ~l~> (<[i:=x']> m1, <[i:=y']> m2).
Time Proof.
Time
(intros Hi1 Hi2 Hup; <ssreflect_plugin::ssrtclintros@0>
  apply local_update_unital =>n mf Hmv Hm; simpl in *).
Time (destruct (Hup n (mf !! i)) as [? Hx']; simpl in *).
Time {
Time move : {}(Hmv i) {}.
Time by rewrite Hi1.
Time }
Time {
Time move : {}(Hm i) {}.
Time by rewrite lookup_op Hi1 Hi2 Some_op_opM (inj_iff Some).
Time }
Time (split; auto using insert_validN).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite Hm Hx' =>j;
  destruct (decide (i = j)) as [->| ]).
Time -
Time by rewrite lookup_insert lookup_op lookup_insert Some_op_opM.
Time -
Time by rewrite lookup_insert_ne // !lookup_op lookup_insert_ne.
Time Qed.
Time
Lemma singleton_local_update m i x y x' y' :
  m !! i = Some x
  \226\134\146 (x, y) ~l~> (x', y') \226\134\146 (m, {[i := y]}) ~l~> (<[i:=x']> m, {[i := y']}).
Time Proof.
Time (intros).
Time rewrite /singletonM /map_singleton -(insert_insert \226\136\133 i y' y).
Time by eapply insert_local_update; [  | eapply lookup_insert |  ].
Time Qed.
Time
Lemma delete_local_update m1 m2 i x `{!Exclusive x} :
  m2 !! i = Some x \226\134\146 (m1, m2) ~l~> (delete i m1, delete i m2).
Time Proof.
Time (intros Hi).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time (split; auto using delete_validN).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite Hm =>j;
  destruct (decide (i = j)) as [<-| ]).
Time -
Time rewrite lookup_op !lookup_delete left_id symmetry_iff dist_None.
Time (<ssreflect_plugin::ssrtclintros@0> apply eq_None_not_Some =>- [y Hi']).
Time move : {}(Hmv i) {}.
Time rewrite Hm lookup_op Hi Hi' -Some_op.
Time by apply exclusiveN_l.
Time -
Time by rewrite lookup_op !lookup_delete_ne // lookup_op.
Time Qed.
Time
Lemma delete_singleton_local_update m i x `{!Exclusive x} :
  (m, {[i := x]}) ~l~> (delete i m, \226\136\133).
Time Proof.
Time rewrite -(delete_singleton i x).
Time by eapply delete_local_update, lookup_singleton.
Time Qed.
Time
Lemma delete_local_update_cancelable m1 m2 i mx `{!Cancelable mx} :
  m1 !! i \226\137\161 mx \226\134\146 m2 !! i \226\137\161 mx \226\134\146 (m1, m2) ~l~> (delete i m1, delete i m2).
Time Proof.
Time (intros Hm1i Hm2i).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time (split; [ eauto using delete_validN |  ]).
Time (intros j).
Time (destruct (decide (i = j)) as [->| ]).
Time -
Time move : {}(Hm j) {}.
Time rewrite !lookup_op Hm1i Hm2i !lookup_delete.
Time (intros Hmx).
Time rewrite (cancelableN mx n (mf !! j) None) ?right_id // -Hmx -Hm1i.
Time (apply Hmv).
Time -
Time by rewrite lookup_op !lookup_delete_ne // Hm lookup_op.
Time Qed.
Time
Lemma delete_singleton_local_update_cancelable m i 
  x `{!Cancelable (Some x)} :
  m !! i \226\137\161 Some x \226\134\146 (m, {[i := x]}) ~l~> (delete i m, \226\136\133).
Time Proof.
Time (intros).
Time rewrite -(delete_singleton i x).
Time
(apply (delete_local_update_cancelable m _ i (Some x));
  [ done | by rewrite lookup_singleton ]).
Time Qed.
Time
Lemma gmap_fmap_mono {B : cmraT} (f : A \226\134\146 B) m1 m2 :
  Proper ((\226\137\161) ==> (\226\137\161)) f
  \226\134\146 (\226\136\128 x y, x \226\137\188 y \226\134\146 f x \226\137\188 f y) \226\134\146 m1 \226\137\188 m2 \226\134\146 fmap f m1 \226\137\188 fmap f m2.
Time Proof.
Time (intros ? ?).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite !lookup_included =>Hm i).
Time rewrite !lookup_fmap.
Time by apply option_fmap_mono.
Time Qed.
Time End properties.
Time Section unital_properties.
Time Context `{Countable K} {A : ucmraT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time Implicit Types x y : A.
Time
Lemma insert_alloc_local_update m1 m2 i x x' y' :
  m1 !! i = Some x
  \226\134\146 m2 !! i = None
    \226\134\146 (x, \206\181) ~l~> (x', y') \226\134\146 (m1, m2) ~l~> (<[i:=x']> m1, <[i:=y']> m2).
Time Proof.
Time (intros Hi1 Hi2 Hup).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hm1v Hm).
Time (assert (Hif : mf !! i \226\137\161{n}\226\137\161 Some x)).
Time {
Time move : {}(Hm i) {}.
Time by rewrite lookup_op Hi1 Hi2 left_id.
Time }
Time (destruct (Hup n (mf !! i)) as [Hx'v Hx'eq]).
Time {
Time move : {}(Hm1v i) {}.
Time by rewrite Hi1.
Time }
Time {
Time by rewrite Hif -(inj_iff Some) -Some_op_opM -Some_op left_id.
Time }
Time split.
Time -
Time by apply insert_validN.
Time -
Time (simpl in Hx'eq).
Time by rewrite -(insert_idN n mf i x) // -insert_op -Hm Hx'eq Hif.
Time Qed.
Time End unital_properties.
Time
Instance gmap_fmap_ne  `{Countable K} {A B : ofeT} 
 (f : A \226\134\146 B) n:
 (Proper (dist n ==> dist n) f
  \226\134\146 Proper (dist n ==> dist n) (fmap (M:=gmap K) f)).
Time Proof.
Time by intros ? m m' Hm k; rewrite !lookup_fmap; apply option_fmap_ne.
Time Qed.
Time
Instance gmap_fmap_cmra_morphism  `{Countable K} {A B : cmraT} 
 (f : A \226\134\146 B) `{!CmraMorphism f}:
 (CmraMorphism (fmap f : gmap K A \226\134\146 gmap K B)).
Time Proof.
Time (split; try apply _).
Time -
Time by intros n m ? i; rewrite lookup_fmap; apply (cmra_morphism_validN _).
Time -
Time (intros m).
Time (<ssreflect_plugin::ssrtclintros@0> apply Some_proper =>i).
Time rewrite lookup_fmap !lookup_omap lookup_fmap.
Time case : {}(m !! i) {} =>//= ?.
Time (apply cmra_morphism_pcore, _).
Time -
Time (intros m1 m2 i).
Time by rewrite lookup_op !lookup_fmap lookup_op cmra_morphism_op.
Time Qed.
Time
Definition gmapO_map `{Countable K} {A} {B} (f : A -n> B) :
  gmapO K A -n> gmapO K B := OfeMor (fmap f : gmapO K A \226\134\146 gmapO K B).
Time
Instance gmapO_map_ne  `{Countable K} {A} {B}:
 (NonExpansive (@gmapO_map K _ _ A B)).
Time Proof.
Time (intros n f g Hf m k; rewrite /= !lookup_fmap).
Time (destruct (_ !! k) eqn:?; simpl; constructor; apply Hf).
Time Qed.
Time #[program]
Definition gmapOF K `{Countable K} (F : oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ => gmapO K (oFunctor_car F A B);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg => gmapO_map (oFunctor_map F fg) |}.
Time Next Obligation.
Time
by
 intros K ? ? F A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapO_map_ne, oFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A ? B ? x).
Time rewrite /= -{+2}(map_fmap_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply oFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -map_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply oFunctor_compose).
Time Qed.
Time
Instance gmapOF_contractive  K `{Countable K} F:
 (oFunctorContractive F \226\134\146 oFunctorContractive (gmapOF K F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapO_map_ne, oFunctor_contractive.
Time Qed.
Time #[program]
Definition gmapURF K `{Countable K} (F : rFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => gmapUR K (rFunctor_car F A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   gmapO_map (rFunctor_map F fg) |}.
Time Next Obligation.
Time
by
 intros K ? ? F A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapO_map_ne, rFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A ? B ? x).
Time rewrite /= -{+2}(map_fmap_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply rFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros K ? ? F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -map_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply map_fmap_equiv_ext =>y ? ?;
  apply rFunctor_compose).
Time Qed.
Time
Instance gmapRF_contractive  K `{Countable K} F:
 (rFunctorContractive F \226\134\146 urFunctorContractive (gmapURF K F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply gmapO_map_ne, rFunctor_contractive.
Time Qed.
