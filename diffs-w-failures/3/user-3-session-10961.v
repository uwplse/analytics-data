Time From iris.base_logic.lib Require Export own.
Time From stdpp Require Export coPset.
Time From iris.base_logic.lib Require Import wsat.
Time From iris.algebra Require Import gmap auth agree gset coPset.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Export invG.
Time Import uPred.
Time
Definition uPred_fupd_def `{!invG \206\163} (E1 E2 : coPset) 
  (P : iProp \206\163) : iProp \206\163 := (wsat \226\136\151 ownE E1 ==\226\136\151 \226\151\135 (wsat \226\136\151 ownE E2 \226\136\151 P))%I.
Time Definition uPred_fupd_aux `{!invG \206\163} : seal uPred_fupd_def.
Time by eexists.
Time Qed.
Time
Definition uPred_fupd `{!invG \206\163} : FUpd (iProp \206\163) := uPred_fupd_aux.(unseal).
Time
Definition uPred_fupd_eq `{!invG \206\163} : @fupd _ uPred_fupd = uPred_fupd_def :=
  uPred_fupd_aux.(seal_eq).
Time
Lemma uPred_fupd_mixin `{!invG \206\163} :
  BiFUpdMixin (uPredSI (iResUR \206\163)) uPred_fupd.
Time Proof.
Time split.
Time -
Time rewrite uPred_fupd_eq.
Time solve_proper.
Time -
Time (intros E1 E2 P (E1'', (->, ?))%subseteq_disjoint_union_L).
Time rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //.
Time by iIntros "$ ($ & $ & HE) !> !> [$ $] !> !>".
Time -
Time rewrite uPred_fupd_eq.
Time iIntros ( E1 E2 P ) ">H [Hw HE]".
Time (iApply "H"; by iFrame).
Time -
Time rewrite uPred_fupd_eq.
Time iIntros ( E1 E2 P Q HPQ ) "HP HwE".
Time rewrite -HPQ.
Time by iApply "HP".
Time -
Time rewrite uPred_fupd_eq.
Time iIntros ( E1 E2 E3 P ) "HP HwE".
Time iMod ("HP" with "HwE") as ">(Hw & HE & HP)".
Time (iApply "HP"; by iFrame).
Time -
Time (intros E1 E2 Ef P HE1Ef).
Time rewrite uPred_fupd_eq /uPred_fupd_def ownE_op //.
Time iIntros "Hvs (Hw & HE1 &HEf)".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod ("Hvs" with "[Hw HE1]") as
 ">($ & HE2 & HP)" ; first  by iFrame).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (ownE_op' with "[HE2 HEf]") as
 "[? $]" ; first  by iFrame).
Time iIntros "!> !>".
Time by iApply "HP".
Time -
Time rewrite uPred_fupd_eq /uPred_fupd_def.
Time by iIntros ( ? ? ? ? ) "[HwP $]".
Time Qed.
Time
Instance uPred_bi_fupd  `{!invG \206\163}: (BiFUpd (uPredSI (iResUR \206\163))) :=
 {| bi_fupd_mixin := uPred_fupd_mixin |}.
Time
Instance uPred_bi_bupd_fupd  `{!invG \206\163}: (BiBUpdFUpd (uPredSI (iResUR \206\163))).
Time Proof.
Time rewrite /BiBUpdFUpd uPred_fupd_eq.
Time by iIntros ( E P ) ">? [$ $] !> !>".
Time Qed.
Time
Instance uPred_bi_fupd_plainly  `{!invG \206\163}:
 (BiFUpdPlainly (uPredSI (iResUR \206\163))).
Time Proof.
Time split.
Time -
Time rewrite uPred_fupd_eq /uPred_fupd_def.
Time iIntros ( E P ) "H [Hw HE]".
Time iAssert (\226\151\135 \226\150\160 P)%I as "#>HP".
Time {
Time by iMod ("H" with "[$]") as "(_ & _ & HP)".
Time }
Time by iFrame.
Time -
Time rewrite uPred_fupd_eq /uPred_fupd_def.
Time iIntros ( E P Q ) "[H HQ] [Hw HE]".
Time iAssert (\226\151\135 \226\150\160 P)%I as "#>HP".
Time {
Time by iMod ("H" with "HQ [$]") as "(_ & _ & HP)".
Time }
Time by iFrame.
Time -
Time rewrite uPred_fupd_eq /uPred_fupd_def.
Time iIntros ( E P ) "H [Hw HE]".
Time iAssert (\226\150\183 \226\151\135 \226\150\160 P)%I as "#HP".
Time {
Time iNext.
Time by iMod ("H" with "[$]") as "(_ & _ & HP)".
Time }
Time iFrame.
Time iIntros "!> !> !>".
Time by iMod "HP".
Time -
Time rewrite uPred_fupd_eq /uPred_fupd_def.
Time iIntros ( E A \206\166 ) "H\206\166 [Hw HE]".
Time iAssert (\226\151\135 \226\150\160 (\226\136\128 x : A, \206\166 x))%I as "#>HP".
Time {
Time iIntros ( x ).
Time by iMod ("H\206\166" with "[$Hw $HE]") as "(_&_&?)".
Time }
Time by iFrame.
Time Qed.
Time
Lemma fupd_plain_soundness `{!invPreG \206\163} E1 E2 (P : iProp \206\163) 
  `{!Plain P} :
  (\226\136\128 `{Hinv : !invG \206\163}, bi_emp_valid (|={E1,E2}=> P)) \226\134\146 bi_emp_valid P.
Time Proof.
Time iIntros ( Hfupd ).
Time (apply later_soundness).
Time iMod wsat_alloc as ( Hinv ) "[Hw HE]".
Time iAssert (|={\226\138\164,E2}=> P)%I as "H".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> iMod fupd_intro_mask' ; last  iApply Hfupd).
Time done.
Time }
Time rewrite uPred_fupd_eq /uPred_fupd_def.
Time (iMod ("H" with "[$]") as "[Hw [HE >H']]"; iFrame).
Time Qed.
Time
Lemma step_fupdN_soundness `{!invPreG \206\163} \207\134 n :
  (\226\136\128 `{Hinv : !invG \206\163}, (|={\226\138\164,\226\136\133}\226\150\183=>^n |={\226\138\164,\226\136\133}=> \226\140\156\207\134\226\140\157 : iProp \206\163)%I) \226\134\146 \207\134.
Time Proof.
Time (intros Hiter).
Time (apply (soundness (M:=iResUR \206\163) _ (S n)); simpl).
Time
(<ssreflect_plugin::ssrtclintros@0> apply (fupd_plain_soundness \226\138\164 \226\138\164 _)
 =>Hinv).
Time iPoseProof (Hiter Hinv) as "H".
Time clear Hiter.
Time (destruct n as [| n]).
Time -
Time iApply fupd_plainly_mask_empty.
Time (iMod "H" as % ?; auto).
Time -
Time iDestruct (step_fupdN_wand _ _ _ _ (|={\226\138\164}=> \226\140\156\207\134\226\140\157)%I with "H []") as "H'".
Time {
Time by iApply fupd_plain_mask_empty.
Time }
Time rewrite -step_fupdN_S_fupd.
Time iMod (step_fupdN_plain with "H'") as "H\207\134".
Time iModIntro.
Time iNext.
Time rewrite -later_laterN laterN_later.
Time iNext.
Time by iMod "H\207\134".
Time Qed.
Time
Lemma step_fupdN_soundness' `{!invPreG \206\163} \207\134 n :
  (\226\136\128 `{Hinv : !invG \206\163}, (|={\226\138\164,\226\136\133}\226\150\183=>^n \226\140\156\207\134\226\140\157 : iProp \206\163)%I) \226\134\146 \207\134.
Time Proof.
Time iIntros ( Hiter ).
Time (eapply (step_fupdN_soundness _ n)).
Time iIntros ( Hinv ).
Time iPoseProof (Hiter Hinv) as "Hiter".
Time iApply (step_fupdN_wand with "Hiter").
Time by iApply (fupd_mask_weaken _ _ _).
Time Qed.
