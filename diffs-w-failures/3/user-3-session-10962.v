Time From iris.base_logic.lib Require Export fancy_updates.
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
iAssert (ownE {[i]} \226\136\151 ownE (\226\134\145N \226\136\150 {[i]}) \226\136\151 ownE (E \226\136\150 \226\134\145N))%I with "[HE]" as
 "(HEi & HEN\i & HE\N)".
Time {
Time (rewrite -?ownE_op; [ idtac | set_solver.. ]).
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
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 {+1 5}(union_difference_L {[i]} (\226\134\145N)) // ownE_op ; last  set_solver).
Time iIntros "(Hw & [HE $] & $) !> !>".
Time iDestruct (ownI_open i with "[$Hw $HE $HiP]") as "($ & HP & HD)".
Time iDestruct ("HP'" with "HP") as "$".
Time iIntros "HP [Hw $] !> !>".
Time iApply (ownI_close _ P').
Time iFrame "HD Hw HiP".
Time iApply "HP'".
Time iFrame.
Time Qed.
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
Time iIntros "!> {$HP} HP".
Time (iApply "Hclose"; auto).
Time Qed.
Time End inv.
