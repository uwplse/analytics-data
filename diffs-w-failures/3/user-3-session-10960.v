Time From iris.base_logic.lib Require Export own.
Time From stdpp Require Export coPset.
Time From iris.algebra Require Import gmap auth agree gset coPset.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Module invG.
Time
Class invG (\206\163 : gFunctors) : Set :=
 WsatG {inv_inG :>
         inG \206\163 (authR (gmapUR positive (agreeR (laterO (iPreProp \206\163)))));
        enabled_inG :> inG \206\163 coPset_disjR;
        disabled_inG :> inG \206\163 (gset_disjR positive);
        invariant_name : gname;
        enabled_name : gname;
        disabled_name : gname}.
Time
Definition inv\206\163 : gFunctors :=
  #[ GFunctor (authRF (gmapURF positive (agreeRF (laterOF idOF))));
  GFunctor coPset_disjUR; GFunctor (gset_disjUR positive)].
Time
Class invPreG (\206\163 : gFunctors) : Set :=
 WsatPreG {inv_inPreG :>
            inG \206\163 (authR (gmapUR positive (agreeR (laterO (iPreProp \206\163)))));
           enabled_inPreG :> inG \206\163 coPset_disjR;
           disabled_inPreG :> inG \206\163 (gset_disjR positive)}.
Time Instance subG_inv\206\163  {\206\163}: (subG inv\206\163 \206\163 \226\134\146 invPreG \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time End invG.
Time Import invG.
Time
Definition invariant_unfold {\206\163} (P : iProp \206\163) : agree (later (iPreProp \206\163)) :=
  to_agree (Next (iProp_unfold P)).
Time
Definition ownI `{!invG \206\163} (i : positive) (P : iProp \206\163) : 
  iProp \206\163 := own invariant_name (\226\151\175 {[i := invariant_unfold P]}).
Time Arguments ownI {_} {_} _ _%I.
Time Typeclasses Opaque ownI.
Time Instance: (Params (@invariant_unfold) 1) := { }.
Time Instance: (Params (@ownI) 3) := { }.
Time
Definition ownE `{!invG \206\163} (E : coPset) : iProp \206\163 :=
  own enabled_name (CoPset E).
Time Typeclasses Opaque ownE.
Time Instance: (Params (@ownE) 3) := { }.
Time
Definition ownD `{!invG \206\163} (E : gset positive) : iProp \206\163 :=
  own disabled_name (GSet E).
Time Typeclasses Opaque ownD.
Time Instance: (Params (@ownD) 3) := { }.
Time
Definition wsat `{!invG \206\163} : iProp \206\163 :=
  locked
    (\226\136\131 I : gmap positive (iProp \206\163),
       own invariant_name (\226\151\143 (invariant_unfold <$> I : gmap _ _))
       \226\136\151 ([\226\136\151 map] i\226\134\166Q \226\136\136 I, \226\150\183 Q \226\136\151 ownD {[i]} \226\136\168 ownE {[i]}))%I.
Time Section wsat.
Time Context `{!invG \206\163}.
Time Implicit Type P : iProp \206\163.
Time
Instance invariant_unfold_contractive : (Contractive (@invariant_unfold \206\163)).
Time Proof.
Time solve_contractive.
Time Qed.
Time #[global]Instance ownI_contractive  i: (Contractive (@ownI \206\163 _ i)).
Time Proof.
Time solve_contractive.
Time Qed.
Time #[global]Instance ownI_persistent  i P: (Persistent (ownI i P)).
Time Proof.
Time rewrite /ownI.
Time (apply _).
Time Qed.
Time Lemma ownE_empty : (|==> ownE \226\136\133)%I.
Time Proof.
Time rewrite /uPred_valid /bi_emp_valid.
Time by rewrite (own_unit coPset_disjUR enabled_name).
Time Qed.
Time Lemma ownE_op E1 E2 : E1 ## E2 \226\134\146 ownE (E1 \226\136\170 E2) \226\138\163\226\138\162 ownE E1 \226\136\151 ownE E2.
Time Proof.
Time (intros).
Time by rewrite /ownE -own_op coPset_disj_union.
Time Qed.
Time Lemma ownE_disjoint E1 E2 : ownE E1 \226\136\151 ownE E2 \226\138\162 \226\140\156E1 ## E2\226\140\157.
Time Proof.
Time rewrite /ownE -own_op own_valid.
Time by iIntros ( ?%coPset_disj_valid_op ).
Time Qed.
Time Lemma ownE_op' E1 E2 : \226\140\156E1 ## E2\226\140\157 \226\136\167 ownE (E1 \226\136\170 E2) \226\138\163\226\138\162 ownE E1 \226\136\151 ownE E2.
Time Proof.
Time (iSplit; [ iIntros "[% ?]"; by iApply ownE_op |  ]).
Time iIntros "HE".
Time iDestruct (ownE_disjoint with "HE") as % ?.
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; first  done).
Time (iApply ownE_op; by try iFrame).
Time Qed.
Time Lemma ownE_singleton_twice i : ownE {[i]} \226\136\151 ownE {[i]} \226\138\162 False.
Time Proof.
Time rewrite ownE_disjoint.
Time (iIntros ( ? ); set_solver).
Time Qed.
Time Lemma ownD_empty : (|==> ownD \226\136\133)%I.
Time Proof.
Time rewrite /uPred_valid /bi_emp_valid.
Time by rewrite (own_unit (gset_disjUR positive) disabled_name).
Time Qed.
Time Lemma ownD_op E1 E2 : E1 ## E2 \226\134\146 ownD (E1 \226\136\170 E2) \226\138\163\226\138\162 ownD E1 \226\136\151 ownD E2.
Time Proof.
Time (intros).
Time by rewrite /ownD -own_op gset_disj_union.
Time Qed.
Time Lemma ownD_disjoint E1 E2 : ownD E1 \226\136\151 ownD E2 \226\138\162 \226\140\156E1 ## E2\226\140\157.
Time Proof.
Time rewrite /ownD -own_op own_valid.
Time by iIntros ( ?%gset_disj_valid_op ).
Time Qed.
Time Lemma ownD_op' E1 E2 : \226\140\156E1 ## E2\226\140\157 \226\136\167 ownD (E1 \226\136\170 E2) \226\138\163\226\138\162 ownD E1 \226\136\151 ownD E2.
Time Proof.
Time (iSplit; [ iIntros "[% ?]"; by iApply ownD_op |  ]).
Time iIntros "HE".
Time iDestruct (ownD_disjoint with "HE") as % ?.
Time (<ssreflect_plugin::ssrtclseq@0> iSplit ; first  done).
Time (iApply ownD_op; by try iFrame).
Time Qed.
Time Lemma ownD_singleton_twice i : ownD {[i]} \226\136\151 ownD {[i]} \226\138\162 False.
Time Proof.
Time rewrite ownD_disjoint.
Time (iIntros ( ? ); set_solver).
Time Qed.
Time
Lemma invariant_lookup (I : gmap positive (iProp \206\163)) 
  i P :
  own invariant_name (\226\151\143 (invariant_unfold <$> I : gmap _ _))
  \226\136\151 own invariant_name (\226\151\175 {[i := invariant_unfold P]})
  \226\138\162 \226\136\131 Q, \226\140\156I !! i = Some Q\226\140\157 \226\136\151 \226\150\183 (Q \226\137\161 P).
Time Proof.
Time rewrite -own_op own_valid auth_both_validI /=.
Time iIntros "[_ [#HI #HvI]]".
Time iDestruct "HI" as ( I' ) "HI".
Time rewrite gmap_equivI gmap_validI.
Time iSpecialize ("HI" $! i).
Time iSpecialize ("HvI" $! i).
Time rewrite lookup_fmap lookup_op lookup_singleton bi.option_equivI.
Time
(case : {}(I !! i) {} =>[Q|] /=;
  [  | case : {}(I' !! i) {} =>[Q'|] /=; by iExFalso ]).
Time (<ssreflect_plugin::ssrtclseq@0> iExists Q; iSplit ; first  done).
Time iAssert (invariant_unfold Q \226\137\161 invariant_unfold P)%I as "?".
Time {
Time case : {}(I' !! i) {} =>[Q'|] //=.
Time iRewrite "HI" in "HvI".
Time rewrite uPred.option_validI agree_validI.
Time iRewrite - "HvI" in "HI".
Time by rewrite agree_idemp.
Time }
Time rewrite /invariant_unfold.
Time by rewrite agree_equivI bi.later_equivI iProp_unfold_equivI.
Time Qed.
Time
Lemma ownI_open i P : wsat \226\136\151 ownI i P \226\136\151 ownE {[i]} \226\138\162 wsat \226\136\151 \226\150\183 P \226\136\151 ownD {[i]}.
Time Proof.
Time rewrite /ownI /wsat -!lock.
Time iIntros "(Hw & Hi & HiE)".
Time iDestruct "Hw" as ( I ) "[Hw HI]".
Time iDestruct (invariant_lookup I i P with "[$]") as ( Q ? ) "#HPQ".
Time
(iDestruct (big_opM_delete _ _ i with "HI") as "[[[HQ $]|HiE'] HI]"; eauto).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitR "HQ" ; last  by
 iNext; iRewrite - "HPQ").
Time iExists I.
Time iFrame "Hw".
Time (iApply (big_opM_delete _ _ i); eauto).
Time (iFrame "HI"; eauto).
Time -
Time iDestruct (ownE_singleton_twice with "[$HiE $HiE']") as % [].
Time Qed.
Time
Lemma ownI_close i P : wsat \226\136\151 ownI i P \226\136\151 \226\150\183 P \226\136\151 ownD {[i]} \226\138\162 wsat \226\136\151 ownE {[i]}.
Time Proof.
Time rewrite /ownI /wsat -!lock.
Time iIntros "(Hw & Hi & HP & HiD)".
Time iDestruct "Hw" as ( I ) "[Hw HI]".
Time iDestruct (invariant_lookup with "[$]") as ( Q ? ) "#HPQ".
Time
(iDestruct (big_opM_delete _ _ i with "HI") as "[[[HQ ?]|$] HI]"; eauto).
Time -
Time iDestruct (ownD_singleton_twice with "[$]") as % [].
Time -
Time iExists I.
Time iFrame "Hw".
Time (iApply (big_opM_delete _ _ i); eauto).
Time iFrame "HI".
Time iLeft.
Time iFrame "HiD".
Time by iNext; iRewrite "HPQ".
Time Qed.
Time
Lemma ownI_alloc \207\134 P :
  (\226\136\128 E : gset positive, \226\136\131 i, (i \226\136\137 E) \226\136\167 \207\134 i)
  \226\134\146 wsat \226\136\151 \226\150\183 P ==\226\136\151 \226\136\131 i, \226\140\156\207\134 i\226\140\157 \226\136\151 wsat \226\136\151 ownI i P.
Time Proof.
Time iIntros ( Hfresh ) "[Hw HP]".
Time rewrite /wsat -!lock.
Time iDestruct "Hw" as ( I ) "[Hw HI]".
Time iMod (own_unit (gset_disjUR positive) disabled_name) as "HE".
Time iMod (own_updateP with "[$]") as "HE".
Time {
Time
(apply (gset_disj_alloc_empty_updateP_strong' (\206\187 i, I !! i = None \226\136\167 \207\134 i))).
Time (intros E).
Time
(destruct (Hfresh (E \226\136\170 dom _ I))
  as (i, ([? HIi%not_elem_of_dom]%not_elem_of_union, ?)); eauto).
Time }
Time
(iDestruct "HE" as ( X ) "[Hi HE]"; iDestruct "Hi" as % (i, (->, (HIi, ?)))).
Time iMod (own_update with "Hw") as "[Hw HiP]".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0>
 eapply auth_update_alloc,
  (alloc_singleton_local_update _ i (invariant_unfold P)) ; last  done).
Time by rewrite /= lookup_fmap HIi.
Time }
Time (iModIntro; iExists i; iSplit; [ done |  ]).
Time (rewrite /ownI; iFrame "HiP").
Time (iExists (<[i:=P]> I); iSplitL "Hw").
Time {
Time by rewrite fmap_insert insert_singleton_op ?lookup_fmap ?HIi.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (big_opM_insert _ I) ; first  done).
Time iFrame "HI".
Time iLeft.
Time by rewrite /ownD; iFrame.
Time Qed.
Time
Lemma ownI_alloc_open \207\134 P :
  (\226\136\128 E : gset positive, \226\136\131 i, (i \226\136\137 E) \226\136\167 \207\134 i)
  \226\134\146 wsat ==\226\136\151 \226\136\131 i, \226\140\156\207\134 i\226\140\157 \226\136\151 (ownE {[i]} -\226\136\151 wsat) \226\136\151 ownI i P \226\136\151 ownD {[i]}.
Time Proof.
Time iIntros ( Hfresh ) "Hw".
Time rewrite /wsat -!lock.
Time iDestruct "Hw" as ( I ) "[Hw HI]".
Time iMod (own_unit (gset_disjUR positive) disabled_name) as "HD".
Time iMod (own_updateP with "[$]") as "HD".
Time {
Time
(apply (gset_disj_alloc_empty_updateP_strong' (\206\187 i, I !! i = None \226\136\167 \207\134 i))).
Time (intros E).
Time
(destruct (Hfresh (E \226\136\170 dom _ I))
  as (i, ([? HIi%not_elem_of_dom]%not_elem_of_union, ?)); eauto).
Time }
Time
(iDestruct "HD" as ( X ) "[Hi HD]"; iDestruct "Hi" as % (i, (->, (HIi, ?)))).
Time iMod (own_update with "Hw") as "[Hw HiP]".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0>
 eapply auth_update_alloc,
  (alloc_singleton_local_update _ i (invariant_unfold P)) ; last  done).
Time by rewrite /= lookup_fmap HIi.
Time }
Time (iModIntro; iExists i; iSplit; [ done |  ]).
Time (rewrite /ownI; iFrame "HiP").
Time rewrite -/(ownD _).
Time iFrame "HD".
Time iIntros "HE".
Time (iExists (<[i:=P]> I); iSplitL "Hw").
Time {
Time by rewrite fmap_insert insert_singleton_op ?lookup_fmap ?HIi.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iApply (big_opM_insert _ I) ; first  done).
Time iFrame "HI".
Time by iRight.
Time Qed.
Time End wsat.
Time Lemma wsat_alloc `{!invPreG \206\163} : (|==> \226\136\131 _ : invG \206\163, wsat \226\136\151 ownE \226\138\164)%I.
Time Proof.
Time iIntros.
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (own_alloc (\226\151\143 (\226\136\133 : gmap positive _)))
 as ( \206\179I ) "HI" ; first  by rewrite auth_auth_valid).
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (own_alloc (CoPset \226\138\164)) as ( \206\179E ) "HE" ;
 first  done).
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (own_alloc (GSet \226\136\133)) as ( \206\179D ) "HD" ;
 first  done).
Time (iModIntro; iExists (WsatG _ _ _ _ \206\179I \206\179E \206\179D)).
Time (rewrite /wsat /ownE -lock; iFrame).
Time iExists \226\136\133.
Time rewrite fmap_empty big_opM_empty.
Time by iFrame.
Time Qed.
