Time From iris.base_logic.lib Require Export fancy_updates.
Time From iris.base_logic.lib Require Export fancy_updates.
Time From iris.program_logic Require Export language.
Time From stdpp Require Export namespaces.
Time From iris.base_logic.lib Require Import wsat.
Time From iris.algebra Require Import gmap.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Definition inv_def `{!invG \206\163} (N : namespace) (P : iProp \206\163) : 
  iProp \206\163 := (\226\136\131 i P', \226\140\156i \226\136\136 (\226\134\145N : coPset)\226\140\157 \226\136\167 \226\150\183 \226\150\161 (P' \226\134\148 P) \226\136\167 ownI i P')%I.
Time Definition inv_aux : seal (@inv_def).
Time by eexists.
Time Qed.
Time Definition inv {\206\163} {i} := inv_aux.(unseal) \206\163 i.
Time Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq).
Time Instance: (Params (@inv) 3) := { }.
Time Typeclasses Opaque inv.
Time Section inv.
Time Context `{!invG \206\163}.
Time Implicit Type i : positive.
Time Implicit Type N : namespace.
Time Implicit Types P Q R : iProp \206\163.
Time #[global]Instance inv_contractive  N: (Contractive (inv N)).
Time Proof.
Time rewrite inv_eq.
Time solve_contractive.
Time From iris.bi Require Export weakestpre.
Time From iris.proofmode Require Import base tactics classes.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Class irisG (\206\155 : language) (\206\163 : gFunctors) :=
 IrisG {iris_invG :> invG \206\163;
        state_interp : state \206\155 \226\134\146 list (observation \206\155) \226\134\146 nat \226\134\146 iProp \206\163;
        fork_post : val \206\155 \226\134\146 iProp \206\163}.
Time #[global]Opaque iris_invG.
Time
Definition wp_pre `{!irisG \206\155 \206\163} (s : stuckness)
  (wp : coPset -d> expr \206\155 -d> (val \206\155 -d> iProp \206\163) -d> iProp \206\163) :
  coPset -d> expr \206\155 -d> (val \206\155 -d> iProp \206\163) -d> iProp \206\163 :=
  \206\187 E e1 \206\166,
    match to_val e1 with
    | Some v => |={E}=> \206\166 v
    | None =>
        \226\136\128 \207\1311 \206\186 \206\186s n,
          state_interp \207\1311 (\206\186 ++ \206\186s) n
          ={E,\226\136\133}=\226\136\151 \226\140\156match s with
                    | NotStuck => reducible e1 \207\1311
                    | _ => True
                    end\226\140\157
                   \226\136\151 (\226\136\128 e2 \207\1312 efs,
                        \226\140\156prim_step e1 \207\1311 \206\186 e2 \207\1312 efs\226\140\157
                        ={\226\136\133,\226\136\133,E}\226\150\183=\226\136\151 state_interp \207\1312 \206\186s (length efs + n)
                                    \226\136\151 wp E e2 \206\166
                                      \226\136\151 ([\226\136\151 list] i\226\134\166ef \226\136\136 efs, 
                                         wp \226\138\164 ef fork_post))
    end%I.
Time #[local]
Instance wp_pre_contractive  `{!irisG \206\155 \206\163} s: (Contractive (wp_pre s)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /wp_pre =>n wp wp' Hwp E e1 \206\166).
Time (repeat f_contractive || f_equiv; apply Hwp).
Time Qed.
Time #[global]Instance inv_ne  N: (NonExpansive (inv N)).
Time Proof.
Time (apply contractive_ne, _).
Time Qed.
Time #[global]Instance inv_proper  N: (Proper ((\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (inv N)).
Time Proof.
Time (apply ne_proper, _).
Time Qed.
Time #[global]Instance inv_persistent  N P: (Persistent (inv N P)).
Time Proof.
Time (rewrite inv_eq /inv; apply _).
Time Qed.
Time Lemma inv_iff N P Q : \226\150\183 \226\150\161 (P \226\134\148 Q) -\226\136\151 inv N P -\226\136\151 inv N Q.
Time Proof.
Time iIntros "#HPQ".
Time rewrite inv_eq.
Time iDestruct 1 as ( i P' ) "(?&#HP&?)".
Time iExists i , P'.
Time iFrame.
Time (iNext; iAlways; iSplit).
Time -
Time iIntros "HP'".
Time iApply "HPQ".
Time by iApply "HP".
Time -
Time iIntros "HQ".
Time iApply "HP".
Time by iApply "HPQ".
Time Qed.
Time
Lemma fresh_inv_name (E : gset positive) N : \226\136\131 i, (i \226\136\137 E) \226\136\167 i \226\136\136 (\226\134\145N : coPset).
Time Proof.
Time exists (coPpick (\226\134\145N \226\136\150 gset_to_coPset E)).
Time rewrite -elem_of_gset_to_coPset (comm and) -elem_of_difference.
Time (<ssreflect_plugin::ssrtclintros@0> apply coPpick_elem_of =>Hfin).
Time (eapply nclose_infinite, (difference_finite_inv _ _), Hfin).
Time (apply gset_to_coPset_finite).
Time Qed.
Time Lemma inv_alloc N E P : \226\150\183 P ={E}=\226\136\151 inv N P.
Time Proof.
Time rewrite inv_eq /inv_def uPred_fupd_eq.
Time iIntros "HP [Hw $]".
Time
(iMod (ownI_alloc (\226\136\136\226\134\145N : coPset) P with "[$HP $Hw]") as ( i ? ) "[$ ?]"; auto
  using fresh_inv_name).
Time (do 2 iModIntro).
Time iExists i , P.
Time rewrite -(iff_refl True%I).
Time auto.
Time Qed.
Time Qed.
Time
Lemma inv_alloc_open N E P :
  \226\134\145N \226\138\134 E \226\134\146 (|={E,E \226\136\150 \226\134\145N}=> inv N P \226\136\151 (\226\150\183 P ={E \226\136\150 \226\134\145N,E}=\226\136\151 True))%I.
Time Proof.
Time rewrite inv_eq /inv_def uPred_fupd_eq.
Time iIntros ( Sub ) "[Hw HE]".
Time
(iMod (ownI_alloc_open (\226\136\136\226\134\145N : coPset) P with "Hw") as ( i ? )
  "(Hw & #Hi & HD)"; auto using fresh_inv_name).
Time
Definition wp_def `{!irisG \206\155 \206\163} (s : stuckness) :
  coPset \226\134\146 expr \206\155 \226\134\146 (val \206\155 \226\134\146 iProp \206\163) \226\134\146 iProp \206\163 := 
  fixpoint (wp_pre s).
Time Definition wp_aux `{!irisG \206\155 \206\163} : seal (@wp_def \206\155 \206\163 _).
Time by eexists.
Time Qed.
Time
Instance wp'  `{!irisG \206\155 \206\163}: (Wp \206\155 (iProp \206\163) stuckness) := wp_aux.(unseal).
Time Definition wp_eq `{!irisG \206\155 \206\163} : wp = @wp_def \206\155 \206\163 _ := wp_aux.(seal_eq).
Time Section wp.
Time Context `{!irisG \206\155 \206\163}.
Time Implicit Type s : stuckness.
Time Implicit Type P : iProp \206\163.
Time Implicit Type \206\166 : val \206\155 \226\134\146 iProp \206\163.
Time Implicit Type v : val \206\155.
Time Implicit Type e : expr \206\155.
Time
Lemma wp_unfold s E e \206\166 :
  WP e @ s; E {{\206\166} } \226\138\163\226\138\162 wp_pre s (wp (PROP:=iProp \206\163) s) E e \206\166.
Time Proof.
Time rewrite wp_eq.
Time (apply (fixpoint_unfold (wp_pre s))).
Time
iAssert (ownE {[i]} \226\136\151 ownE (\226\134\145N \226\136\150 {[i]}) \226\136\151 ownE (E \226\136\150 \226\134\145N))%I with "[HE]" as
 "(HEi & HEN\i & HE\N)".
Time Qed.
Time #[global]
Instance wp_ne  s E e n:
 (Proper (pointwise_relation _ (dist n) ==> dist n)
    (wp (PROP:=iProp \206\163) s E e)).
Time Proof.
Time revert e.
Time
(<ssreflect_plugin::ssrtclintros@0> induction (lt_wf n) as [n _ IH] =>e \206\166 \206\168
 H\206\166).
Time rewrite !wp_unfold /wp_pre.
Time {
Time (rewrite -?ownE_op; [ idtac | set_solver.. ]).
Time (do 24 f_contractive || f_equiv).
Time rewrite assoc_L -!union_difference_L //.
Time set_solver.
Time }
Time (do 2 iModIntro).
Time iFrame "HE\N".
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitL "Hw HEi" ; first  by iApply "Hw").
Time iSplitL "Hi".
Time {
Time iExists i , P.
Time rewrite -(iff_refl True%I).
Time auto.
Time }
Time iIntros "HP [Hw HE\N]".
Time iDestruct (ownI_close with "[$Hw $Hi $HP $HD]") as "[$ HEi]".
Time (do 2 iModIntro).
Time (iSplitL; [  | done ]).
Time iCombine "HEi HEN\i HE\N" as "HEN".
Time (rewrite -?ownE_op; [ idtac | set_solver.. ]).
Time (rewrite assoc_L -!union_difference_L //; set_solver).
Time Qed.
Time
Lemma inv_open E N P :
  \226\134\145N \226\138\134 E \226\134\146 inv N P ={E,E \226\136\150 \226\134\145N}=\226\136\151 \226\150\183 P \226\136\151 (\226\150\183 P ={E \226\136\150 \226\134\145N,E}=\226\136\151 True).
Time Proof.
Time rewrite inv_eq /inv_def uPred_fupd_eq /uPred_fupd_def.
Time iDestruct 1 as ( i P' ) "(Hi & #HP' & #HiP)".
Time iDestruct "Hi" as % ?%elem_of_subseteq_singleton.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite {+1 4}(union_difference_L (\226\134\145N) E) //
 ownE_op ; last  set_solver).
Time (<ssreflect_plugin::ssrtclseq@0> apply IH ; first  lia).
Time (intros v).
Time (eapply dist_le; eauto with lia).
Time Qed.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 {+1 5}(union_difference_L {[i]} (\226\134\145N)) // ownE_op ; last  set_solver).
Time #[global]
Instance wp_proper  s E e:
 (Proper (pointwise_relation _ (\226\137\161) ==> (\226\137\161)) (wp (PROP:=iProp \206\163) s E e)).
Time Proof.
Time
by
 intros \206\166 \206\166' ?; <ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n;
  <ssreflect_plugin::ssrtclintros@0> apply wp_ne =>v; 
  apply equiv_dist.
Time Qed.
Time Lemma wp_value' s E \206\166 v : \206\166 v \226\138\162 WP of_val v @ s; E {{\206\166} }.
Time Proof.
Time iIntros "H\206\166".
Time rewrite wp_unfold /wp_pre to_of_val.
Time auto.
Time Qed.
Time Lemma wp_value_inv' s E \206\166 v : WP of_val v @ s; E {{\206\166} } ={E}=\226\136\151 \206\166 v.
Time Proof.
Time by rewrite wp_unfold /wp_pre to_of_val.
Time Qed.
Time
Lemma wp_strong_mono s1 s2 E1 E2 e \206\166 \206\168 :
  s1 \226\138\145 s2
  \226\134\146 E1 \226\138\134 E2
    \226\134\146 WP e @ s1; E1 {{\206\166} } -\226\136\151 (\226\136\128 v, \206\166 v ={E2}=\226\136\151 \206\168 v) -\226\136\151 WP e @ s2; E2 {{\206\168} }.
Time Proof.
Time iIntros ( ? HE ) "H H\206\166".
Time iL\195\182b as "IH" forall ( e E1 E2 HE \206\166 \206\168 ).
Time rewrite !wp_unfold /wp_pre.
Time (destruct (to_val e) as [v| ] eqn:?).
Time {
Time iApply ("H\206\166" with "[> -]").
Time by iApply (fupd_mask_mono E1 _).
Time }
Time iIntros ( \207\1311 \206\186 \206\186s n ) "H\207\131".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (fupd_intro_mask' E2 E1) as "Hclose" ;
 first  done).
Time iMod ("H" with "[$]") as "[% H]".
Time iModIntro.
Time (iSplit; [ by destruct s1, s2 |  ]).
Time iIntros "(Hw & [HE $] & $) !> !>".
Time iIntros ( e2 \207\1312 efs Hstep ).
Time iMod ("H" with "[//]") as "H".
Time iDestruct (ownI_open i with "[$Hw $HE $HiP]") as "($ & HP & HD)".
Time iIntros "!> !>".
Time iMod "H" as "(H\207\131 & H & Hefs)".
Time iDestruct ("HP'" with "HP") as "$".
Time iMod "Hclose" as "_".
Time iIntros "HP [Hw $] !> !>".
Time iModIntro.
Time iFrame "H\207\131".
Time iSplitR "Hefs".
Time -
Time iApply ("IH" with "[//] H H\206\166").
Time iApply (ownI_close _ P').
Time iFrame "HD Hw HiP".
Time -
Time (iApply (big_sepL_impl with "Hefs"); iIntros "!#" ( k ef _ )).
Time iApply "HP'".
Time iFrame.
Time Qed.
Time iIntros "H".
Time (iApply ("IH" with "[] H"); auto).
Time
Lemma inv_open_strong E N P :
  \226\134\145N \226\138\134 E \226\134\146 inv N P ={E,E \226\136\150 \226\134\145N}=\226\136\151 \226\150\183 P \226\136\151 (\226\136\128 E', \226\150\183 P ={E',\226\134\145N \226\136\170 E'}=\226\136\151 True).
Time Proof.
Time iIntros ( ? ) "Hinv".
Time
(<ssreflect_plugin::ssrtclseq@0> iPoseProof (inv_open (\226\134\145N) N P with "Hinv")
 as "H" ; first  done).
Time rewrite difference_diag_L.
Time
(<ssreflect_plugin::ssrtclseq@0> iPoseProof
 (fupd_mask_frame_r _ _ (E \226\136\150 \226\134\145N) with "H") as "H" ; first  set_solver).
Time rewrite left_id_L -union_difference_L //.
Time (iMod "H" as "[$ H]"; iModIntro).
Time iIntros ( E' ) "HP".
Time Qed.
Time
(<ssreflect_plugin::ssrtclseq@0> iPoseProof
 (fupd_mask_frame_r _ _ E' with "(H HP)") as "H" ; first  set_solver).
Time by rewrite left_id_L.
Time Qed.
Time #[global]Instance into_inv_inv  N P: (IntoInv (inv N P) N) := { }.
Time #[global]
Instance into_acc_inv  E N P:
 (IntoAcc (X:=unit) (inv N P) (\226\134\145N \226\138\134 E) True (fupd E (E \226\136\150 \226\134\145N))
    (fupd (E \226\136\150 \226\134\145N) E) (\206\187 _, \226\150\183 P)%I (\206\187 _, \226\150\183 P)%I (\206\187 _, None)%I).
Time Proof.
Time rewrite /IntoAcc /accessor exist_unit.
Time iIntros ( ? ) "#Hinv _".
Time (iApply inv_open; done).
Time Qed.
Time
Lemma inv_open_timeless E N P `{!Timeless P} :
  \226\134\145N \226\138\134 E \226\134\146 inv N P ={E,E \226\136\150 \226\134\145N}=\226\136\151 P \226\136\151 (P ={E \226\136\150 \226\134\145N,E}=\226\136\151 True).
Time Proof.
Time iIntros ( ? ) "Hinv".
Time (iMod (inv_open with "Hinv") as "[>HP Hclose]"; auto).
Time
Lemma fupd_wp s E e \206\166 : (|={E}=> WP e @ s; E {{\206\166} }) \226\138\162 WP e @ s; E {{\206\166} }.
Time Proof.
Time rewrite wp_unfold /wp_pre.
Time iIntros "H".
Time (destruct (to_val e) as [v| ] eqn:?).
Time {
Time by iMod "H".
Time }
Time iIntros ( \207\1311 \206\186 \206\186s n ) "H\207\1311".
Time iIntros "!> {$HP} HP".
Time iMod "H".
Time (iApply "Hclose"; auto).
Time by iApply "H".
Time Qed.
Time End inv.
Time Qed.
Time
Lemma wp_fupd s E e \206\166 : WP e @ s; E {{ v, |={E}=> \206\166 v }} \226\138\162 WP e @ s; E {{\206\166} }.
Time Proof.
Time iIntros "H".
Time (iApply (wp_strong_mono s s E with "H"); auto).
Time Qed.
Time
Lemma wp_atomic s E1 E2 e \206\166 `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> \206\166 v }}) \226\138\162 WP e @ s; E1 {{\206\166} }.
Time Proof.
Time iIntros "H".
Time rewrite !wp_unfold /wp_pre.
Time (destruct (to_val e) as [v| ] eqn:He).
Time {
Time by iDestruct "H" as ">>> $".
Time }
Time iIntros ( \207\1311 \206\186 \206\186s n ) "H\207\131".
Time iMod "H".
Time iMod ("H" $! \207\1311 with "H\207\131") as "[$ H]".
Time iModIntro.
Time iIntros ( e2 \207\1312 efs Hstep ).
Time iMod ("H" with "[//]") as "H".
Time iIntros "!>!>".
Time iMod "H" as "(H\207\131 & H & Hefs)".
Time (destruct s).
Time -
Time rewrite !wp_unfold /wp_pre.
Time (destruct (to_val e2) as [v2| ] eqn:He2).
Time +
Time iDestruct "H" as ">> $".
Time by iFrame.
Time +
Time iMod ("H" $! _ [] with "[$]") as "[H _]".
Time iDestruct "H" as % (?, (?, (?, (?, ?)))).
Time by edestruct (atomic _ _ _ _ _ Hstep).
Time -
Time (destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val]).
Time iMod (wp_value_inv' with "H") as ">H".
Time iModIntro.
Time iFrame "H\207\131 Hefs".
Time by iApply wp_value'.
Time Qed.
Time
Lemma wp_step_fupd s E1 E2 e P \206\166 :
  to_val e = None
  \226\134\146 E2 \226\138\134 E1
    \226\134\146 (|={E1,E2}\226\150\183=> P)
      -\226\136\151 WP e @ s; E2 {{ v, P ={E1}=\226\136\151 \206\166 v }} -\226\136\151 WP e @ s; E1 {{\206\166} }.
Time Proof.
Time rewrite !wp_unfold /wp_pre.
Time iIntros ( -> ? ) "HR H".
Time iIntros ( \207\1311 \206\186 \206\186s n ) "H\207\131".
Time iMod "HR".
Time iMod ("H" with "[$]") as "[$ H]".
Time iIntros "!>" ( e2 \207\1312 efs Hstep ).
Time iMod ("H" $! e2 \207\1312 efs with "[% //]") as "H".
Time iIntros "!>!>".
Time iMod "H" as "(H\207\131 & H & Hefs)".
Time iMod "HR".
Time iModIntro.
Time iFrame "H\207\131 Hefs".
Time (iApply (wp_strong_mono s s E2 with "H"); [ done.. | idtac ]).
Time iIntros ( v ) "H".
Time by iApply "H".
Time Qed.
Time
Lemma wp_bind K `{!LanguageCtx K} s E e \206\166 :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{\206\166} } }} \226\138\162 WP K e @ s; E {{\206\166} }.
Time Proof.
Time iIntros "H".
Time iL\195\182b as "IH" forall ( E e \206\166 ).
Time rewrite wp_unfold /wp_pre.
Time (destruct (to_val e) as [v| ] eqn:He).
Time {
Time (apply of_to_val in He as <-).
Time by iApply fupd_wp.
Time }
Time rewrite wp_unfold /wp_pre fill_not_val //.
Time iIntros ( \207\1311 \206\186 \206\186s n ) "H\207\131".
Time iMod ("H" with "[$]") as "[% H]".
Time (iModIntro; iSplit).
Time {
Time iPureIntro.
Time (<ssreflect_plugin::ssrtclseq@0> destruct s ; last  done).
Time (unfold reducible in *).
Time naive_solver eauto using fill_step.
Time }
Time iIntros ( e2 \207\1312 efs Hstep ).
Time (destruct (fill_step_inv e \207\1311 \206\186 e2 \207\1312 efs) as (e2', (->, ?)); auto).
Time iMod ("H" $! e2' \207\1312 efs with "[//]") as "H".
Time iIntros "!>!>".
Time iMod "H" as "(H\207\131 & H & Hefs)".
Time iModIntro.
Time iFrame "H\207\131 Hefs".
Time by iApply "IH".
Time Qed.
Time
Lemma wp_bind_inv K `{!LanguageCtx K} s E e \206\166 :
  WP K e @ s; E {{\206\166} } \226\138\162 WP e @ s; E {{ v, WP K (of_val v) @ s; E {{\206\166} } }}.
Time Proof.
Time iIntros "H".
Time iL\195\182b as "IH" forall ( E e \206\166 ).
Time rewrite !wp_unfold /wp_pre.
Time (destruct (to_val e) as [v| ] eqn:He).
Time {
Time (apply of_to_val in He as <-).
Time by rewrite !wp_unfold /wp_pre.
Time }
Time rewrite fill_not_val //.
Time iIntros ( \207\1311 \206\186 \206\186s n ) "H\207\131".
Time iMod ("H" with "[$]") as "[% H]".
Time (iModIntro; iSplit).
Time {
Time (destruct s; eauto using reducible_fill).
Time }
Time iIntros ( e2 \207\1312 efs Hstep ).
Time
(iMod ("H" $! (K e2) \207\1312 efs with "[]") as "H";
  [ by eauto using fill_step |  ]).
Time iIntros "!>!>".
Time iMod "H" as "(H\207\131 & H & Hefs)".
Time iModIntro.
Time iFrame "H\207\131 Hefs".
Time by iApply "IH".
Time Qed.
Time
Lemma wp_mono s E e \206\166 \206\168 :
  (\226\136\128 v, \206\166 v \226\138\162 \206\168 v) \226\134\146 WP e @ s; E {{\206\166} } \226\138\162 WP e @ s; E {{\206\168} }.
Time Proof.
Time (iIntros ( H\206\166 ) "H"; iApply (wp_strong_mono with "H"); auto).
Time iIntros ( v ) "?".
Time by iApply H\206\166.
Time Qed.
Time
Lemma wp_stuck_mono s1 s2 E e \206\166 :
  s1 \226\138\145 s2 \226\134\146 WP e @ s1; E {{\206\166} } \226\138\162 WP e @ s2; E {{\206\166} }.
Time Proof.
Time iIntros ( ? ) "H".
Time (iApply (wp_strong_mono with "H"); auto).
Time Qed.
Time Lemma wp_stuck_weaken s E e \206\166 : WP e @ s; E {{\206\166} } \226\138\162 WP e @ E ? {{\206\166} }.
Time Proof.
Time (apply wp_stuck_mono).
Time by destruct s.
Time Qed.
Time
Lemma wp_mask_mono s E1 E2 e \206\166 :
  E1 \226\138\134 E2 \226\134\146 WP e @ s; E1 {{\206\166} } \226\138\162 WP e @ s; E2 {{\206\166} }.
Time Proof.
Time (iIntros ( ? ) "H"; iApply (wp_strong_mono with "H"); auto).
Time Qed.
Time #[global]
Instance wp_mono'  s E e:
 (Proper (pointwise_relation _ (\226\138\162) ==> (\226\138\162)) (wp (PROP:=iProp \206\163) s E e)).
Time Proof.
Time by intros \206\166 \206\166' ?; apply wp_mono.
Time Qed.
Time Lemma wp_value s E \206\166 e v : IntoVal e v \226\134\146 \206\166 v \226\138\162 WP e @ s; E {{\206\166} }.
Time Proof.
Time (intros <-).
Time by apply wp_value'.
Time Qed.
Time
Lemma wp_value_fupd' s E \206\166 v : (|={E}=> \206\166 v) \226\138\162 WP of_val v @ s; E {{\206\166} }.
Time Proof.
Time (intros).
Time by rewrite -wp_fupd -wp_value'.
Time Qed.
Time
Lemma wp_value_fupd s E \206\166 e v `{!IntoVal e v} :
  (|={E}=> \206\166 v) \226\138\162 WP e @ s; E {{\206\166} }.
Time Proof.
Time (intros).
Time rewrite -wp_fupd -wp_value //.
Time Qed.
Time
Lemma wp_value_inv s E \206\166 e v : IntoVal e v \226\134\146 WP e @ s; E {{\206\166} } ={E}=\226\136\151 \206\166 v.
Time Proof.
Time (intros <-).
Time by apply wp_value_inv'.
Time Qed.
Time
Lemma wp_frame_l s E e \206\166 R :
  R \226\136\151 WP e @ s; E {{\206\166} } \226\138\162 WP e @ s; E {{ v, R \226\136\151 \206\166 v }}.
Time Proof.
Time iIntros "[? H]".
Time (iApply (wp_strong_mono with "H"); auto with iFrame).
Time Qed.
Time
Lemma wp_frame_r s E e \206\166 R :
  WP e @ s; E {{\206\166} } \226\136\151 R \226\138\162 WP e @ s; E {{ v, \206\166 v \226\136\151 R }}.
Time Proof.
Time iIntros "[H ?]".
Time (iApply (wp_strong_mono with "H"); auto with iFrame).
Time Qed.
Time
Lemma wp_frame_step_l s E1 E2 e \206\166 R :
  to_val e = None
  \226\134\146 E2 \226\138\134 E1
    \226\134\146 (|={E1,E2}\226\150\183=> R) \226\136\151 WP e @ s; E2 {{\206\166} } \226\138\162 WP e @ s; E1 {{ v, R \226\136\151 \206\166 v }}.
Time Proof.
Time iIntros ( ? ? ) "[Hu Hwp]".
Time (iApply (wp_step_fupd with "Hu"); try done).
Time iApply (wp_mono with "Hwp").
Time by iIntros ( ? ) "$$".
Time Qed.
Time
Lemma wp_frame_step_r s E1 E2 e \206\166 R :
  to_val e = None
  \226\134\146 E2 \226\138\134 E1
    \226\134\146 WP e @ s; E2 {{\206\166} } \226\136\151 (|={E1,E2}\226\150\183=> R) \226\138\162 WP e @ s; E1 {{ v, \206\166 v \226\136\151 R }}.
Time Proof.
Time (rewrite [(WP _ @ _; _ {{_} } \226\136\151 _)%I]comm; setoid_rewrite (comm _ _ R)).
Time (apply wp_frame_step_l).
Time Qed.
Time
Lemma wp_frame_step_l' s E e \206\166 R :
  to_val e = None \226\134\146 \226\150\183 R \226\136\151 WP e @ s; E {{\206\166} } \226\138\162 WP e @ s; E {{ v, R \226\136\151 \206\166 v }}.
Time Proof.
Time iIntros ( ? ) "[??]".
Time (iApply (wp_frame_step_l s E E); try iFrame; eauto).
Time Qed.
Time
Lemma wp_frame_step_r' s E e \206\166 R :
  to_val e = None \226\134\146 WP e @ s; E {{\206\166} } \226\136\151 \226\150\183 R \226\138\162 WP e @ s; E {{ v, \206\166 v \226\136\151 R }}.
Time Proof.
Time iIntros ( ? ) "[??]".
Time (iApply (wp_frame_step_r s E E); try iFrame; eauto).
Time Qed.
Time
Lemma wp_wand s E e \206\166 \206\168 :
  WP e @ s; E {{\206\166} } -\226\136\151 (\226\136\128 v, \206\166 v -\226\136\151 \206\168 v) -\226\136\151 WP e @ s; E {{\206\168} }.
Time Proof.
Time iIntros "Hwp H".
Time (iApply (wp_strong_mono with "Hwp"); auto).
Time iIntros ( ? ) "?".
Time by iApply "H".
Time Qed.
Time
Lemma wp_wand_l s E e \206\166 \206\168 :
  (\226\136\128 v, \206\166 v -\226\136\151 \206\168 v) \226\136\151 WP e @ s; E {{\206\166} } \226\138\162 WP e @ s; E {{\206\168} }.
Time Proof.
Time iIntros "[H Hwp]".
Time iApply (wp_wand with "Hwp H").
Time Qed.
Time
Lemma wp_wand_r s E e \206\166 \206\168 :
  WP e @ s; E {{\206\166} } \226\136\151 (\226\136\128 v, \206\166 v -\226\136\151 \206\168 v) \226\138\162 WP e @ s; E {{\206\168} }.
Time Proof.
Time iIntros "[Hwp H]".
Time iApply (wp_wand with "Hwp H").
Time Qed.
Time
Lemma wp_frame_wand_l s E e Q \206\166 :
  Q \226\136\151 WP e @ s; E {{ v, Q -\226\136\151 \206\166 v }} -\226\136\151 WP e @ s; E {{\206\166} }.
Time Proof.
Time iIntros "[HQ HWP]".
Time iApply (wp_wand with "HWP").
Time iIntros ( v ) "H\206\166".
Time by iApply "H\206\166".
Time Qed.
Time End wp.
Time Section proofmode_classes.
Time Context `{!irisG \206\155 \206\163}.
Time Implicit Types P Q : iProp \206\163.
Time Implicit Type \206\166 : val \206\155 \226\134\146 iProp \206\163.
Time #[global]
Instance frame_wp  p s E e R \206\166 \206\168:
 ((\226\136\128 v, Frame p R (\206\166 v) (\206\168 v))
  \226\134\146 Frame p R (WP e @ s; E {{\206\166} }) (WP e @ s; E {{\206\168} })).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /Frame =>HR).
Time rewrite wp_frame_l.
Time (apply wp_mono, HR).
Time Qed.
Time #[global]
Instance is_except_0_wp  s E e \206\166: (IsExcept0 (WP e @ s; E {{\206\166} })).
Time Proof.
Time by rewrite /IsExcept0 -{+2}fupd_wp -except_0_fupd -fupd_intro.
Time Qed.
Time #[global]
Instance elim_modal_bupd_wp  p s E e P \206\166:
 (ElimModal True p false (|==> P) P (WP e @ s; E {{\206\166} }) (WP e @ s; E {{\206\166} })).
Time Proof.
Time
by rewrite /ElimModal intuitionistically_if_elim (bupd_fupd E) fupd_frame_r
 wand_elim_r fupd_wp.
Time Qed.
Time #[global]
Instance elim_modal_fupd_wp  p s E e P \206\166:
 (ElimModal True p false (|={E}=> P) P (WP e @ s; E {{\206\166} })
    (WP e @ s; E {{\206\166} })).
Time Proof.
Time
by rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r
 fupd_wp.
Time Qed.
Time #[global]
Instance elim_modal_fupd_wp_atomic  p s E1 E2 e P 
 \206\166:
 (Atomic (stuckness_to_atomicity s) e
  \226\134\146 ElimModal True p false (|={E1,E2}=> P) P (WP e @ s; E1 {{\206\166} })
      (WP e @ s; E2 {{ v, |={E2,E1}=> \206\166 v }})%I).
Time Proof.
Time (intros).
Time
by rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r
 wp_atomic.
Time Qed.
Time #[global]
Instance add_modal_fupd_wp  s E e P \206\166:
 (AddModal (|={E}=> P) P (WP e @ s; E {{\206\166} })).
Time Proof.
Time by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp.
Time Qed.
Time #[global]
Instance elim_acc_wp  {X} E1 E2 \206\177 \206\178 \206\179 e s \206\166:
 (Atomic (stuckness_to_atomicity s) e
  \226\134\146 ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1) \206\177 \206\178 \206\179 
      (WP e @ s; E1 {{\206\166} })
      (\206\187 x, WP e @ s; E2 {{ v, |={E2}=> \206\178 x \226\136\151 (\206\179 x -\226\136\151? \206\166 v) }})%I).
Time Proof.
Time (intros ?).
Time rewrite /ElimAcc.
Time iIntros "Hinner >Hacc".
Time iDestruct "Hacc" as ( x ) "[H\206\177 Hclose]".
Time iApply (wp_wand with "(Hinner H\206\177)").
Time iIntros ( v ) ">[H\206\178 H\206\166]".
Time iApply "H\206\166".
Time by iApply "Hclose".
Time Qed.
Time #[global]
Instance elim_acc_wp_nonatomic  {X} E \206\177 \206\178 \206\179 e s \206\166:
 (ElimAcc (X:=X) (fupd E E) (fupd E E) \206\177 \206\178 \206\179 (WP e @ s; E {{\206\166} })
    (\206\187 x, WP e @ s; E {{ v, |={E}=> \206\178 x \226\136\151 (\206\179 x -\226\136\151? \206\166 v) }})%I).
Time Proof.
Time rewrite /ElimAcc.
Time iIntros "Hinner >Hacc".
Time iDestruct "Hacc" as ( x ) "[H\206\177 Hclose]".
Time iApply wp_fupd.
Time iApply (wp_wand with "(Hinner H\206\177)").
Time iIntros ( v ) ">[H\206\178 H\206\166]".
Time iApply "H\206\166".
Time by iApply "Hclose".
Time Qed.
Time End proofmode_classes.
