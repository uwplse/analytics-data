Time From iris.algebra Require Export cmra.
Time From iris.algebra Require Export cmra.
Time From stdpp Require Export list.
Time From stdpp Require Export list gmap.
Time From iris.base_logic Require Import base_logic.
Time From iris.algebra Require Import updates local_updates.
Time From iris.base_logic Require Import base_logic.
Time From iris.algebra Require Import updates local_updates.
Time From iris.algebra Require Import proofmode_classes.
Time Set Default Proof Using "Type".
Time Section cofe.
Time Context `{Countable K} {A : ofeT}.
Time Implicit Type m : gmap K A.
Time Implicit Type i : K.
Time Set Default Proof Using "Type".
Time Section cofe.
Time Context {A : ofeT}.
Time Implicit Type l : list A.
Time Instance list_dist : (Dist (list A)) := (\206\187 n, Forall2 (dist n)).
Time
Lemma list_dist_lookup n l1 l2 : l1 \226\137\161{n}\226\137\161 l2 \226\134\148 (\226\136\128 i, l1 !! i \226\137\161{n}\226\137\161 l2 !! i).
Time Proof.
Time
Instance gmap_dist : (Dist (gmap K A)) :=
 (\206\187 n m1 m2, \226\136\128 i, m1 !! i \226\137\161{n}\226\137\161 m2 !! i).
Time Definition gmap_ofe_mixin : OfeMixin (gmap K A).
Time Proof.
Time split.
Time -
Time (intros m1 m2; split).
Time setoid_rewrite dist_option_Forall2.
Time +
Time by intros Hm n k; apply equiv_dist.
Time (apply Forall2_lookup).
Time Qed.
Time +
Time (intros Hm k; apply equiv_dist; intros n; apply Hm).
Time -
Time (intros n; split).
Time #[global]Instance cons_ne : (NonExpansive2 (@cons A)) := _.
Time +
Time by intros m k.
Time +
Time by intros m1 m2 ? k.
Time #[global]Instance app_ne : (NonExpansive2 (@app A)) := _.
Time +
Time by intros m1 m2 m3 ? ? k; trans m2 !! k.
Time -
Time #[global]
Instance length_ne  n: (Proper (dist n ==> (=)) (@length A)) := _.
Time by intros n m1 m2 ? k; apply dist_S.
Time Qed.
Time #[global]Instance tail_ne : (NonExpansive (@tail A)) := _.
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
Time #[global]Instance take_ne : (NonExpansive (@take A n)) := _.
Time #[global]Instance drop_ne : (NonExpansive (@drop A n)) := _.
Time #[global]Instance head_ne : (NonExpansive (head (A:=A))).
Time Proof.
Time (destruct 1; by constructor).
Time Qed.
Time #[global]
Instance list_lookup_ne  i: (NonExpansive (lookup (M:=list A) i)).
Time Proof.
Time (intros ? ? ? ?).
Time by apply dist_option_Forall2, Forall2_lookup.
Time Qed.
Time #[global]
Instance list_alter_ne  n f i:
 (Proper (dist n ==> dist n) f
  \226\134\146 Proper (dist n ==> dist n) (alter (M:=list A) f i)) := _.
Time by rewrite conv_compl /=; apply reflexive_eq.
Time #[global]
Instance list_insert_ne  i: (NonExpansive2 (insert (M:=list A) i)) := _.
Time Qed.
Time #[global]
Instance list_inserts_ne  i: (NonExpansive2 (@list_inserts A i)) := _.
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
Time #[global]
Instance list_delete_ne  i: (NonExpansive (delete (M:=list A) i)) := _.
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
Time #[global]Instance option_list_ne : (NonExpansive (@option_list A)).
Time Proof.
Time (intros ? ? ? ?; by apply Forall2_option_list, dist_option_Forall2).
Time Qed.
Time #[global]
Instance list_filter_ne  n P `{\226\136\128 x, Decision (P x)}:
 (Proper (dist n ==> iff) P
  \226\134\146 Proper (dist n ==> dist n) (filter (B:=list A) P)) := _.
Time #[global]Instance replicate_ne : (NonExpansive (@replicate A n)) := _.
Time #[global]Instance reverse_ne : (NonExpansive (@reverse A)) := _.
Time #[global]Instance last_ne : (NonExpansive (@last A)).
Time Qed.
Time Proof.
Time (intros ? ? ? ?; by apply dist_option_Forall2, Forall2_last).
Time Qed.
Time #[global]Instance resize_ne  n: (NonExpansive2 (@resize A n)) := _.
Time
Lemma list_dist_cons_inv_l n x l k :
  x :: l \226\137\161{n}\226\137\161 k \226\134\146 \226\136\131 y k', x \226\137\161{n}\226\137\161 y \226\136\167 l \226\137\161{n}\226\137\161 k' \226\136\167 k = y :: k'.
Time Proof.
Time (apply Forall2_cons_inv_l).
Time Qed.
Time
Lemma list_dist_cons_inv_r n l k y :
  l \226\137\161{n}\226\137\161 y :: k \226\134\146 \226\136\131 x l', x \226\137\161{n}\226\137\161 y \226\136\167 l' \226\137\161{n}\226\137\161 k \226\136\167 l = x :: l'.
Time Proof.
Time (apply Forall2_cons_inv_r).
Time Qed.
Time Definition list_ofe_mixin : OfeMixin (list A).
Time Proof.
Time split.
Time -
Time (intros l k).
Time rewrite equiv_Forall2 -Forall2_forall.
Time (split; induction 1; constructor; intros; try apply equiv_dist; auto).
Time -
Time (apply _).
Time -
Time rewrite /dist /list_dist.
Time eauto using Forall2_impl, dist_S.
Time Qed.
Time Canonical Structure listO := OfeT (list A) list_ofe_mixin.
Time
Fixpoint list_compl_go `{!Cofe A} (c0 : list A) (c : chain listO) : listO :=
  match c0 with
  | [] => []
  | x :: c0 =>
      compl (chain_map (default x \226\136\152 head) c)
      :: list_compl_go c0 (chain_map tail c)
  end.
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
Time #[global, program]
Instance list_cofe  `{!Cofe A}: (Cofe listO) :=
 {| compl := fun c => list_compl_go (c 0) c |}.
Time End cofe.
Time Next Obligation.
Time (intros ? n c; rewrite /compl).
Time (assert (Hc0 : c 0 \226\137\161{0}\226\137\161 c n) by (symmetry; apply chain_cauchy; lia)).
Time revert Hc0.
Time (<ssreflect_plugin::ssrtclintros@0> generalize (c 0) =>c0).
Time revert c.
Time
(<ssreflect_plugin::ssrtclintros@0> induction c0 as [| x c0 IH] =>c Hc0 /=).
Time {
Time by inversion Hc0.
Time Arguments gmapO _ {_} {_} _.
Time Section cmra.
Time Context `{Countable K} {A : cmraT}.
Time Implicit Type m : gmap K A.
Time Instance gmap_unit : (Unit (gmap K A)) := (\226\136\133 : gmap K A).
Time }
Time (apply list_dist_cons_inv_l in Hc0 as (x', (xs', (Hx, (Hc0, Hcn))))).
Time Instance gmap_op : (Op (gmap K A)) := (merge op).
Time Instance gmap_pcore : (PCore (gmap K A)) := (\206\187 m, Some (omap pcore m)).
Time Instance gmap_valid : (Valid (gmap K A)) := (\206\187 m, \226\136\128 i, \226\156\147 (m !! i)).
Time
Instance gmap_validN : (ValidN (gmap K A)) := (\206\187 n m, \226\136\128 i, \226\156\147{n} (m !! i)).
Time rewrite Hcn.
Time f_equiv.
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
Time -
Time by rewrite conv_compl /= Hcn /=.
Time Proof.
Time
(split; [ by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm |  ]).
Time -
Time rewrite IH /= ?Hcn //.
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
Time Qed.
Time (intros j).
Time (move : {}(Hm j) {}; destruct (decide (i = j)) as [->| ]).
Time -
Time (intros _).
Time rewrite Hi.
Time #[global]
Instance list_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete listO).
Time Proof.
Time (induction 2; constructor; try apply (discrete _); auto).
Time apply : {}ucmra_unit_least {}.
Time Qed.
Time -
Time rewrite lookup_insert_ne // lookup_delete_ne //.
Time #[global]Instance nil_discrete : (Discrete (@nil A)).
Time Proof.
Time (inversion_clear 1; constructor).
Time Qed.
Time #[global]
Instance cons_discrete  x l: (Discrete x \226\134\146 Discrete l \226\134\146 Discrete (x :: l)).
Time Proof.
Time (intros ? ?; inversion_clear 1; constructor; by apply discrete).
Time Qed.
Time End cofe.
Time Arguments listO : clear implicits.
Time
Lemma list_fmap_ext_ne {A} {B : ofeT} (f g : A \226\134\146 B) 
  (l : list A) n : (\226\136\128 x, f x \226\137\161{n}\226\137\161 g x) \226\134\146 f <$> l \226\137\161{n}\226\137\161 g <$> l.
Time }
Time (destruct (Hm i) as [my Hi']; simplify_map_eq).
Time Proof.
Time (intros Hf).
Time by apply Forall2_fmap, Forall_Forall2, Forall_true.
Time Qed.
Time
Instance list_fmap_ne  {A B : ofeT} (f : A \226\134\146 B) n:
 (Proper (dist n ==> dist n) f
  \226\134\146 Proper (dist n ==> dist n) (fmap (M:=list) f)).
Time Proof.
Time (intros Hf l k ?; by eapply Forall2_fmap, Forall2_impl; eauto).
Time Qed.
Time
Definition listO_map {A} {B} (f : A -n> B) : listO A -n> listO B :=
  OfeMor (fmap f : listO A \226\134\146 listO B).
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
Time Instance listO_map_ne  A B: (NonExpansive (@listO_map A B)).
Time Proof.
Time (intros n f g ? l).
Time by apply list_fmap_ext_ne.
Time Qed.
Time #[program]
Definition listOF (F : oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ => listO (oFunctor_car F A B);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg => listO_map (oFunctor_map F fg) |}.
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
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, oFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(list_fmap_id x).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y).
Time (apply oFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -list_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y;
  apply oFunctor_compose).
Time Qed.
Time -
Time by intros m1 m2 i; rewrite !lookup_op comm.
Time
Instance listOF_contractive  F:
 (oFunctorContractive F \226\134\146 oFunctorContractive (listOF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply listO_map_ne, oFunctor_contractive.
Time Qed.
Time Section cmra.
Time Context {A : ucmraT}.
Time Implicit Type l : list A.
Time #[local]Arguments op _ _ !_ !_ / : simpl nomatch.
Time
Instance list_op : (Op (list A)) :=
 (fix go l1 l2 :=
    let _ : Op _ := @go in
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x :: l1, y :: l2 => x \226\139\133 y :: l1 \226\139\133 l2
    end).
Time Instance list_pcore : (PCore (list A)) := (\206\187 l, Some (core <$> l)).
Time Instance list_valid : (Valid (list A)) := (Forall (\206\187 x, \226\156\147 x)).
Time Instance list_validN : (ValidN (list A)) := (\206\187 n, Forall (\206\187 x, \226\156\147{n} x)).
Time Lemma cons_valid l x : \226\156\147 (x :: l) \226\134\148 \226\156\147 x \226\136\167 \226\156\147 l.
Time Proof.
Time (apply Forall_cons).
Time Qed.
Time Lemma cons_validN n l x : \226\156\147{n} (x :: l) \226\134\148 \226\156\147{n} x \226\136\167 \226\156\147{n} l.
Time Proof.
Time (apply Forall_cons).
Time Qed.
Time Lemma app_valid l1 l2 : \226\156\147 (l1 ++ l2) \226\134\148 \226\156\147 l1 \226\136\167 \226\156\147 l2.
Time Proof.
Time (apply Forall_app).
Time Qed.
Time Lemma app_validN n l1 l2 : \226\156\147{n} (l1 ++ l2) \226\134\148 \226\156\147{n} l1 \226\136\167 \226\156\147{n} l2.
Time Proof.
Time (apply Forall_app).
Time -
Time (intros m i).
Time by rewrite lookup_op lookup_core cmra_core_l.
Time Qed.
Time Lemma list_lookup_valid l : \226\156\147 l \226\134\148 (\226\136\128 i, \226\156\147 (l !! i)).
Time Proof.
Time (rewrite {+1}/valid /list_valid Forall_lookup; split).
Time -
Time (intros Hl i).
Time by destruct (l !! i) as [x| ] eqn:?; [ apply (Hl i) |  ].
Time -
Time (intros Hl i x Hi).
Time (move : {}(Hl i) {}; by rewrite Hi).
Time Qed.
Time Lemma list_lookup_validN n l : \226\156\147{n} l \226\134\148 (\226\136\128 i, \226\156\147{n} (l !! i)).
Time Proof.
Time (rewrite {+1}/validN /list_validN Forall_lookup; split).
Time -
Time (intros m i).
Time by rewrite !lookup_core cmra_core_idemp.
Time -
Time (intros Hl i).
Time by destruct (l !! i) as [x| ] eqn:?; [ apply (Hl i) |  ].
Time -
Time (intros Hl i x Hi).
Time (move : {}(Hl i) {}; by rewrite Hi).
Time Qed.
Time Lemma list_lookup_op l1 l2 i : (l1 \226\139\133 l2) !! i = l1 !! i \226\139\133 l2 !! i.
Time Proof.
Time revert i l2.
Time
(induction l1 as [| x l1]; intros [| i] [| y l2]; by rewrite /= ?left_id_L
  ?right_id_L).
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
Time Qed.
Time Lemma list_lookup_core l i : core l !! i = core (l !! i).
Time Proof.
Time rewrite /core /= list_lookup_fmap.
Time (destruct (l !! i); by rewrite /= ?Some_core).
Time Qed.
Time Lemma list_lookup_included l1 l2 : l1 \226\137\188 l2 \226\134\148 (\226\136\128 i, l1 !! i \226\137\188 l2 !! i).
Time Proof.
Time split.
Time {
Time (intros [l Hl] i).
Time exists (l !! i).
Time by rewrite Hl list_lookup_op.
Time +
Time
(destruct (y1 !! i), (y2 !! i); inversion Hz1i; inversion Hz2i;
  <ssreflect_plugin::ssrtclintros@0> subst =>//).
Time }
Time revert l1.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l2 as [| y l2 IH] =>- 
 [|x l1] Hl).
Time -
Time by exists [].
Time -
Time (destruct (Hl 0) as [[z| ] Hz]; inversion Hz).
Time -
Time by exists (y :: l2).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (IH l1) as [l3 ?] ; first 
 intros i; apply (Hl (S i))).
Time (destruct (Hl 0) as [[z| ] Hz]; inversion_clear Hz; simplify_eq /=).
Time +
Time (exists (z :: l3); by constructor).
Time +
Time (exists (core x :: l3); constructor; by rewrite ?cmra_core_r).
Time Qed.
Time +
Time revert Hz1i.
Time case : {}(y1 !! i) {} =>[?|] //.
Time +
Time revert Hz2i.
Time case : {}(y2 !! i) {} =>[?|] //.
Time Definition list_cmra_mixin : CmraMixin (list A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time Qed.
Time -
Time
(intros n l l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite
  !list_dist_lookup =>Hl i).
Time by rewrite !list_lookup_op Hl.
Time -
Time (intros n l1 l2 Hl; by rewrite /core /= Hl).
Time Canonical Structure gmapR := CmraT (gmap K A) gmap_cmra_mixin.
Time #[global]
Instance gmap_cmra_discrete : (CmraDiscrete A \226\134\146 CmraDiscrete gmapR).
Time Proof.
Time (split; [ apply _ |  ]).
Time (intros m ? i).
Time by apply : {}cmra_discrete_valid {}.
Time -
Time
(intros n l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite !list_dist_lookup
  !list_lookup_validN =>Hl ? i).
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
Time by rewrite -Hl.
Time Qed.
Time Lemma gmap_validI {M} m : \226\156\147 m \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, \226\156\147 (m !! i)).
Time Proof.
Time by uPred.unseal.
Time -
Time (intros l).
Time rewrite list_lookup_valid.
Time setoid_rewrite list_lookup_validN.
Time Qed.
Time End cmra.
Time setoid_rewrite cmra_valid_validN.
Time naive_solver.
Time -
Time (intros n x).
Time rewrite !list_lookup_validN.
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
Time auto using cmra_validN_S.
Time -
Time
(intros l1 l2 l3; <ssreflect_plugin::ssrtclintros@0> rewrite
  list_equiv_lookup =>i).
Time by rewrite !list_lookup_op assoc.
Time (intros m1 m2; by rewrite lookup_op).
Time done.
Time Qed.
Time -
Time
(intros l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite list_equiv_lookup
  =>i).
Time Lemma lookup_opM m1 mm2 i : (m1 \226\139\133? mm2) !! i = m1 !! i \226\139\133 (mm2 \226\137\171= (!!i)).
Time Proof.
Time (destruct mm2; by rewrite /= ?lookup_op ?right_id_L).
Time by rewrite !list_lookup_op comm.
Time -
Time
(intros l; <ssreflect_plugin::ssrtclintros@0> rewrite list_equiv_lookup =>i).
Time by rewrite list_lookup_op list_lookup_core cmra_core_l.
Time -
Time
(intros l; <ssreflect_plugin::ssrtclintros@0> rewrite list_equiv_lookup =>i).
Time by rewrite !list_lookup_core cmra_core_idemp.
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
Time -
Time
(intros l1 l2; <ssreflect_plugin::ssrtclintros@0> rewrite
  !list_lookup_included =>Hl i).
Time Qed.
Time Lemma insert_validN n m i x : \226\156\147{n} x \226\134\146 \226\156\147{n} m \226\134\146 \226\156\147{n} <[i:=x]> m.
Time Proof.
Time by intros ? ? j; destruct (decide (i = j)); simplify_map_eq.
Time rewrite !list_lookup_core.
Time by apply cmra_core_mono.
Time -
Time (intros n l1 l2).
Time rewrite !list_lookup_validN.
Time Qed.
Time Lemma insert_valid m i x : \226\156\147 x \226\134\146 \226\156\147 m \226\134\146 \226\156\147 <[i:=x]> m.
Time Proof.
Time by intros ? ? j; destruct (decide (i = j)); simplify_map_eq.
Time setoid_rewrite list_lookup_op.
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
Time eauto using cmra_validN_op_l.
Time -
Time (intros n l).
Time
(<ssreflect_plugin::ssrtclintros@0> induction l as [| x l IH] =>- 
  [|y1 l1] [|y2 l2] Hl Heq; try by exfalso; inversion Heq).
Time Qed.
Time Lemma delete_valid m i : \226\156\147 m \226\134\146 \226\156\147 delete i m.
Time Proof.
Time (intros Hm j; destruct (decide (i = j)); by simplify_map_eq).
Time +
Time by exists [],[].
Time +
Time (exists [],(x :: l); inversion Heq; by repeat constructor).
Time Qed.
Time
Lemma insert_singleton_op m i x : m !! i = None \226\134\146 <[i:=x]> m = {[i := x]} \226\139\133 m.
Time Proof.
Time
(intros Hi; <ssreflect_plugin::ssrtclintros@0> apply map_eq =>j;
  destruct (decide (i = j)) as [->| ]).
Time -
Time by rewrite lookup_op lookup_insert lookup_singleton Hi right_id_L.
Time +
Time (exists (x :: l),[]; inversion Heq; by repeat constructor).
Time -
Time
by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id_L.
Time +
Time
(destruct (IH l1 l2) as (l1', (l2', (?, (?, ?)))), 
  (cmra_extend n x y1 y2) as (y1', (y2', (?, (?, ?))));
  [ by inversion_clear Heq; inversion_clear Hl.. | idtac ]).
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
Time (exists (y1' :: l1'),(y2' :: l2'); repeat constructor; auto).
Time Qed.
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
Time Canonical Structure listR := CmraT (list A) list_cmra_mixin.
Time #[global]Instance list_unit : (Unit (list A)) := [].
Time Definition list_ucmra_mixin : UcmraMixin (list A).
Time Proof.
Time split.
Time -
Time constructor.
Time -
Time by intros l.
Time -
Time by constructor.
Time Qed.
Time Canonical Structure listUR := UcmraT (list A) list_ucmra_mixin.
Time #[global]
Instance list_cmra_discrete : (CmraDiscrete A \226\134\146 CmraDiscrete listR).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> split; [ apply _ |  ] =>l;
  <ssreflect_plugin::ssrtclintros@0> rewrite list_lookup_valid
  list_lookup_validN =>Hl i).
Time by apply cmra_discrete_valid.
Time Qed.
Time #[global]Instance list_core_id  l: ((\226\136\128 x : A, CoreId x) \226\134\146 CoreId l).
Time Proof.
Time
(intros ?; constructor; <ssreflect_plugin::ssrtclintros@0>
  apply list_equiv_lookup =>i).
Time by rewrite list_lookup_core (core_id_core (l !! i)).
Time Qed.
Time
Lemma list_equivI {M} l1 l2 : l1 \226\137\161 l2 \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, l1 !! i \226\137\161 l2 !! i).
Time Proof.
Time (uPred.unseal; <ssreflect_plugin::ssrtclintros@0> constructor =>n x ?).
Time (apply list_dist_lookup).
Time Qed.
Time Lemma list_validI {M} l : \226\156\147 l \226\138\163\226\138\162@{ uPredI M} (\226\136\128 i, \226\156\147 (l !! i)).
Time Proof.
Time (uPred.unseal; <ssreflect_plugin::ssrtclintros@0> constructor =>n x ?).
Time (apply list_lookup_validN).
Time Qed.
Time End cmra.
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
Time Arguments listR : clear implicits.
Time Arguments listUR : clear implicits.
Time
Instance list_singletonM  {A : ucmraT}: (SingletonM nat A (list A)) :=
 (\206\187 n x, replicate n \206\181 ++ [x]).
Time split.
Time done.
Time (apply cmra_includedN_l).
Time -
Time (intros (y, (Hi, [mz Hy]))).
Time exists (partial_alter (\206\187 _, mz) i m).
Time Section properties.
Time Context {A : ucmraT}.
Time Implicit Type l : list A.
Time Implicit Types x y z : A.
Time #[local]Arguments op _ _ !_ !_ / : simpl nomatch.
Time #[local]Arguments cmra_op _ !_ !_ / : simpl nomatch.
Time #[local]Arguments ucmra_op _ !_ !_ / : simpl nomatch.
Time Lemma list_lookup_opM l mk i : (l \226\139\133? mk) !! i = l !! i \226\139\133 (mk \226\137\171= (!!i)).
Time Proof.
Time (destruct mk; by rewrite /= ?list_lookup_op ?right_id_L).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time +
Time by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
Time +
Time
by rewrite lookup_op lookup_singleton_ne // lookup_partial_alter_ne //
 left_id.
Time Qed.
Time #[global]Instance list_op_nil_l : (LeftId (=) (@nil A) op).
Time Proof.
Time done.
Time Qed.
Time #[global]Instance list_op_nil_r : (RightId (=) (@nil A) op).
Time Proof.
Time by intros [].
Time Qed.
Time
Lemma list_op_app l1 l2 l3 :
  (l1 ++ l3) \226\139\133 l2 = l1 \226\139\133 take (length l1) l2 ++ l3 \226\139\133 drop (length l1) l2.
Time Proof.
Time revert l2 l3.
Time
(<ssreflect_plugin::ssrtclintros@0> induction l1 as [| x1 l1] =>- 
  [|x2 l2] [|x3 l3]; f_equal /=; auto).
Time Qed.
Time
Lemma list_op_app_le l1 l2 l3 :
  length l2 \226\137\164 length l1 \226\134\146 (l1 ++ l3) \226\139\133 l2 = l1 \226\139\133 l2 ++ l3.
Time Proof.
Time (intros ?).
Time by rewrite list_op_app take_ge // drop_ge // right_id_L.
Time Qed.
Time Qed.
Time
Lemma list_lookup_validN_Some n l i x : \226\156\147{n} l \226\134\146 l !! i \226\137\161{n}\226\137\161 Some x \226\134\146 \226\156\147{n} x.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> move  {}=>/list_lookup_validN/
  (_ i) =>Hl Hi; move : {}Hl {}).
Time by rewrite Hi.
Time
Lemma singleton_included m i x :
  {[i := x]} \226\137\188 m \226\134\148 (\226\136\131 y, m !! i \226\137\161 Some y \226\136\167 Some x \226\137\188 Some y).
Time Qed.
Time Proof.
Time split.
Time -
Time (move  {}=>[m' /(_ i)]; rewrite lookup_op lookup_singleton).
Time exists (x \226\139\133? m' !! i).
Time Lemma list_lookup_valid_Some l i x : \226\156\147 l \226\134\146 l !! i \226\137\161 Some x \226\134\146 \226\156\147 x.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> move  {}=>/list_lookup_valid/
  (_ i) =>Hl Hi; move : {}Hl {}).
Time by rewrite Hi.
Time Qed.
Time
Lemma list_op_length l1 l2 : length (l1 \226\139\133 l2) = max (length l1) (length l2).
Time Proof.
Time revert l2.
Time (induction l1; intros [| ? ?]; f_equal /=; auto).
Time rewrite -Some_op_opM.
Time split.
Time done.
Time (apply cmra_included_l).
Time -
Time (intros (y, (Hi, [mz Hy]))).
Time exists (partial_alter (\206\187 _, mz) i m).
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time Qed.
Time Lemma replicate_valid n (x : A) : \226\156\147 x \226\134\146 \226\156\147 replicate n x.
Time Proof.
Time (apply Forall_replicate).
Time Qed.
Time #[global]
Instance list_singletonM_ne  i: (NonExpansive (@list_singletonM A i)).
Time Proof.
Time (intros n l1 l2 ?).
Time (apply Forall2_app; by repeat constructor).
Time Qed.
Time +
Time by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
Time #[global]
Instance list_singletonM_proper  i:
 (Proper ((\226\137\161) ==> (\226\137\161)) (list_singletonM i)) := (ne_proper _).
Time
Lemma elem_of_list_singletonM i z x :
  z \226\136\136 ({[i := x]} : list A) \226\134\146 z = \206\181 \226\136\168 z = x.
Time Proof.
Time rewrite elem_of_app elem_of_list_singleton elem_of_replicate.
Time +
Time
by rewrite lookup_op lookup_singleton_ne // lookup_partial_alter_ne //
 left_id.
Time naive_solver.
Time Qed.
Time Lemma list_lookup_singletonM i x : ({[i := x]} : list A) !! i = Some x.
Time Proof.
Time (induction i; by f_equal /=).
Time Qed.
Time
Lemma list_lookup_singletonM_ne i j x :
  i \226\137\160 j
  \226\134\146 ({[i := x]} : list A) !! j = None \226\136\168 ({[i := x]} : list A) !! j = Some \206\181.
Time Proof.
Time (revert j; induction i; intros [| j]; naive_solver auto with lia).
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
Time Qed.
Time
Lemma list_singletonM_validN n i x : \226\156\147{n} ({[i := x]} : list A) \226\134\148 \226\156\147{n} x.
Time Proof.
Time rewrite list_lookup_validN.
Time -
Time rewrite lookup_singleton.
Time by apply cancelableN.
Time split.
Time {
Time move  {}=>/(_ i).
Time -
Time by rewrite lookup_singleton_ne // !(left_id None _).
Time by rewrite list_lookup_singletonM.
Time }
Time (intros Hx j; destruct (decide (i = j)); subst).
Time -
Time by rewrite list_lookup_singletonM.
Time -
Time
(<ssreflect_plugin::ssrtclseq@0>
  destruct (list_lookup_singletonM_ne i j x) as [Hi| Hi] ; first  done;
  rewrite Hi; by try apply (ucmra_unit_validN (A:=A))).
Time Qed.
Time Lemma list_singleton_valid i x : \226\156\147 ({[i := x]} : list A) \226\134\148 \226\156\147 x.
Time Proof.
Time rewrite !cmra_valid_validN.
Time by setoid_rewrite list_singletonM_validN.
Time Qed.
Time Lemma list_singletonM_length i x : length {[i := x]} = S i.
Time Proof.
Time
(rewrite /singletonM /list_singletonM app_length replicate_length /=; lia).
Time Qed.
Time
Lemma list_core_singletonM i (x : A) : core {[i := x]} \226\137\161 {[i := core x]}.
Time Proof.
Time rewrite /singletonM /list_singletonM.
Time by rewrite {+1}/core /= fmap_app fmap_replicate (core_id_core \226\136\133).
Time Qed.
Time Qed.
Time
Lemma list_op_singletonM i (x y : A) :
  {[i := x]} \226\139\133 {[i := y]} \226\137\161 {[i := x \226\139\133 y]}.
Time Proof.
Time rewrite /singletonM /list_singletonM /=.
Time (induction i; constructor; rewrite ?left_id; auto).
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
Time Qed.
Time
Lemma list_alter_singletonM f i x :
  alter f i ({[i := x]} : list A) = {[i := f x]}.
Time Proof.
Time rewrite /singletonM /list_singletonM /=.
Time (induction i; f_equal /=; auto).
Time Qed.
Time #[global]
Instance list_singleton_core_id  i (x : A): (CoreId x \226\134\146 CoreId {[i := x]}).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists (<[i:=y]> m); split ; first  by auto).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite !core_id_total
 list_core_singletonM =>{+}->.
Time
(intros j; move : {}(Hm j) {} =>{Hm}; <ssreflect_plugin::ssrtclintros@0>
  rewrite !lookup_op =>Hm).
Time (destruct (decide (i = j)); simplify_map_eq /=; auto).
Time Qed.
Time Lemma list_singleton_snoc l x : {[length l := x]} \226\139\133 l \226\137\161 l ++ [x].
Time Proof.
Time elim : {}l {} =>//= ? ? {+}<-.
Time by rewrite left_id.
Time Qed.
Time
Lemma insert_updateP' (P : A \226\134\146 Prop) m i x :
  x ~~>: P \226\134\146 <[i:=x]> m ~~>: (\206\187 m', \226\136\131 y, m' = <[i:=y]> m \226\136\167 P y).
Time Proof.
Time eauto using insert_updateP.
Time Qed.
Time Qed.
Time Lemma insert_update m i x y : x ~~> y \226\134\146 <[i:=x]> m ~~> <[i:=y]> m.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using insert_updateP with subst).
Time
Lemma list_singleton_updateP (P : A \226\134\146 Prop) (Q : list A \226\134\146 Prop) 
  x : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q [y]) \226\134\146 [x] ~~>: Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !cmra_total_updateP =>Hup HQ n lf
 /list_lookup_validN Hv).
Time Qed.
Time (destruct (Hup n (default \206\181 (lf !! 0))) as (y, (?, Hv'))).
Time {
Time move : {}(Hv 0) {}.
Time by destruct lf; rewrite /= ?right_id.
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
Time }
Time (<ssreflect_plugin::ssrtclseq@0> exists [y]; split ; first  by auto).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_lookup_validN =>i).
Time move : {}(Hv i) {}Hv' {}.
Time by destruct i, lf; rewrite /= ?right_id.
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
Time Qed.
Time
Lemma list_singleton_updateP' (P : A \226\134\146 Prop) x :
  x ~~>: P \226\134\146 [x] ~~>: (\206\187 k, \226\136\131 y, k = [y] \226\136\167 P y).
Time Proof.
Time eauto using list_singleton_updateP.
Time Qed.
Time Lemma list_singleton_update x y : x ~~> y \226\134\146 [x] ~~> [y].
Time Proof.
Time
(rewrite !cmra_update_updateP; eauto using list_singleton_updateP with subst).
Time Qed.
Time
Lemma app_updateP (P1 P2 Q : list A \226\134\146 Prop) l1 l2 :
  l1 ~~>: P1
  \226\134\146 l2 ~~>: P2
    \226\134\146 (\226\136\128 k1 k2, P1 k1 \226\134\146 P2 k2 \226\134\146 length l1 = length k1 \226\136\167 Q (k1 ++ k2))
      \226\134\146 l1 ++ l2 ~~>: Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !cmra_total_updateP =>Hup1 Hup2
 HQ n lf).
Time (destruct (m1 !! i), (m2 !! i); naive_solver).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite list_op_app app_validN =>- [? ?]).
Time (destruct (Hup1 n (take (length l1) lf)) as (k1, (?, ?)); auto).
Time (destruct (Hup2 n (drop (length l1) lf)) as (k2, (?, ?)); auto).
Time exists (k1 ++ k2).
Time rewrite list_op_app app_validN.
Time Qed.
Time by destruct (HQ k1 k2) as [<- ?].
Time Qed.
Time Lemma dom_included m1 m2 : m1 \226\137\188 m2 \226\134\146 dom (gset K) m1 \226\138\134 dom _ m2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite lookup_included =>? i; rewrite
  !elem_of_dom).
Time
Lemma app_update l1 l2 k1 k2 :
  length l1 = length k1 \226\134\146 l1 ~~> k1 \226\134\146 l2 ~~> k2 \226\134\146 l1 ++ l2 ~~> k1 ++ k2.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using app_updateP with subst).
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
Time Qed.
Time revert Hi2.
Time rewrite dom_op not_elem_of_union.
Time
Lemma cons_updateP (P1 : A \226\134\146 Prop) (P2 Q : list A \226\134\146 Prop) 
  x l :
  x ~~>: P1 \226\134\146 l ~~>: P2 \226\134\146 (\226\136\128 y k, P1 y \226\134\146 P2 k \226\134\146 Q (y :: k)) \226\134\146 x :: l ~~>: Q.
Time Proof.
Time (intros).
Time
(eapply (app_updateP _ _ _ [x]); naive_solver eauto
  using list_singleton_updateP').
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
Time Qed.
Time
Lemma cons_updateP' (P1 : A \226\134\146 Prop) (P2 : list A \226\134\146 Prop) 
  x l :
  x ~~>: P1
  \226\134\146 l ~~>: P2 \226\134\146 x :: l ~~>: (\206\187 k, \226\136\131 y k', k = y :: k' \226\136\167 P1 y \226\136\167 P2 k').
Time Proof.
Time eauto  10 using cons_updateP.
Time Qed.
Time Lemma cons_update x y l k : x ~~> y \226\134\146 l ~~> k \226\134\146 x :: l ~~> y :: k.
Time Proof.
Time (rewrite !cmra_update_updateP; eauto using cons_updateP with subst).
Time by apply insert_validN; [ apply cmra_valid_validN |  ].
Time Qed.
Time Qed.
Time
Lemma list_middle_updateP (P : A \226\134\146 Prop) (Q : list A \226\134\146 Prop) 
  l1 x l2 : x ~~>: P \226\134\146 (\226\136\128 y, P y \226\134\146 Q (l1 ++ y :: l2)) \226\134\146 l1 ++ x :: l2 ~~>: Q.
Time Proof.
Time (intros).
Time (eapply app_updateP).
Time -
Time by apply cmra_update_updateP.
Time
Lemma alloc_updateP (Q : gmap K A \226\134\146 Prop) m x :
  \226\156\147 x \226\134\146 (\226\136\128 i, m !! i = None \226\134\146 Q (<[i:=x]> m)) \226\134\146 m ~~>: Q.
Time -
Time by eapply cons_updateP', cmra_update_updateP.
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
Time -
Time naive_solver.
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
Time Qed.
Time
Lemma list_middle_update l1 l2 x y :
  x ~~> y \226\134\146 l1 ++ x :: l2 ~~> l1 ++ y :: l2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !cmra_update_updateP =>?; eauto
  using list_middle_updateP with subst).
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
Time Qed.
Time rewrite !left_id.
Time
Lemma list_alloc_singleton_local_update x l :
  \226\156\147 x \226\134\146 (l, \206\181) ~l~> (l ++ [x], {[length l := x]}).
Time Proof.
Time move  {}=>?.
Time
have {+}->: {[length l := x]} \226\137\161 {[length l := x]} \226\139\133 \206\181by rewrite right_id.
Time (case : {}(gf !! i) {} =>[x|]; rewrite /= ?left_id //).
Time rewrite -list_singleton_snoc.
Time (intros; by apply cmra_valid_validN).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> exists {[i := y]}; split ; first  by auto).
Time (intros i'; destruct (decide (i' = i)) as [->| ]).
Time -
Time rewrite lookup_op lookup_singleton.
Time (move : {}Hy {}; case : {}(gf !! i) {} =>[x|]; rewrite /= ?right_id //).
Time (<ssreflect_plugin::ssrtclintros@0> apply op_local_update =>? ?).
Time rewrite list_singleton_snoc app_validN cons_validN.
Time -
Time move : {}(Hg i') {}.
Time by rewrite !lookup_op lookup_singleton_ne // !left_id.
Time
(<ssreflect_plugin::ssrtclintros@0> split_and ? =>//; [  | constructor ]).
Time Qed.
Time by apply cmra_valid_validN.
Time Qed.
Time
Lemma alloc_unit_singleton_updateP' (P : A \226\134\146 Prop) 
  u i :
  \226\156\147 u \226\134\146 LeftId (\226\137\161) u (\226\139\133) \226\134\146 u ~~>: P \226\134\146 \226\136\133 ~~>: (\206\187 m, \226\136\131 y, m = {[i := y]} \226\136\167 P y).
Time End properties.
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
Time
Instance list_fmap_cmra_morphism  {A B : ucmraT} (f : A \226\134\146 B)
 `{!CmraMorphism f}: (CmraMorphism (fmap f : list A \226\134\146 list B)).
Time Proof.
Time (split; try apply _).
Time Qed.
Time
Lemma alloc_local_update m1 m2 i x :
  m1 !! i = None \226\134\146 \226\156\147 x \226\134\146 (m1, m2) ~l~> (<[i:=x]> m1, <[i:=x]> m2).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite cmra_valid_validN =>Hi ?).
Time -
Time (intros n l).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite !list_lookup_validN =>Hl i).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time rewrite list_lookup_fmap.
Time by apply (cmra_morphism_validN (fmap f : option A \226\134\146 option B)).
Time -
Time (intros l).
Time (apply Some_proper).
Time rewrite -!list_fmap_compose.
Time (apply list_fmap_equiv_ext, cmra_morphism_core, _).
Time -
Time (intros l1 l2).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_equiv_lookup =>i).
Time
by rewrite list_lookup_op !list_lookup_fmap list_lookup_op cmra_morphism_op.
Time (split; auto using insert_validN).
Time Qed.
Time (intros j; destruct (decide (i = j)) as [->| ]).
Time -
Time
(move : {}(Hm j) {}; <ssreflect_plugin::ssrtclintros@0> rewrite Hi
  symmetry_iff dist_None lookup_op op_None =>- [_ Hj]).
Time #[program]
Definition listURF (F : urFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => listUR (urFunctor_car F A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   listO_map (urFunctor_map F fg) |}.
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
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply listO_map_ne, urFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(list_fmap_id x).
Time (<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y).
Time (apply urFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -list_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply list_fmap_equiv_ext =>y;
  apply urFunctor_compose).
Time Qed.
Time
Instance listURF_contractive  F:
 (urFunctorContractive F \226\134\146 urFunctorContractive (listURF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply listO_map_ne, urFunctor_contractive.
Time Qed.
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
