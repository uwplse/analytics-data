Time From iris.algebra Require Import auth gmap frac agree csum excl.
Time From iris.algebra Require Import auth agree functions csum cmra.
Time
Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.ThreadReg
  CSL.Leased_Heap.
Time From Armada.CSL Require Import Counting.
Time From iris.base_logic.lib Require Export own.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Require Export CSL.Refinement CSL.NamedDestruct CSL.ProofModeClasses.
Time From iris.algebra Require Export functions csum.
Time From iris.base_logic.lib Require Export invariants gen_heap.
Time From iris.proofmode Require Export tactics.
Time Require Export TwoDiskAPI.
Time Set Default Proof Using "Type".
Time Import TwoDisk.
Time Canonical Structure diskIdC := leibnizO diskId.
Time
Class disk_statusG (\206\163 : gFunctors) : Set :=
 Disk_statusG {disk_status_inG :>
                inG \206\163 (csumR (exclR unitO) (agreeR diskIdC));
               disk_status_name : gname}.
Time Arguments disk_status_name {_}.
Time Section disk_status.
Time Context `{tr : disk_statusG \206\163}.
Time
Definition is_OnlyDisk (id : diskId) :=
  own (disk_status_name tr) (Cinr (to_agree id)).
Time
Definition to_status (ds : DisksState) :=
  match ds with
  | OnlyDisk id _ => Cinr (to_agree id)
  | BothDisks _ _ => Cinl (Excl tt)
  end.
Time
Definition disk_status_ctx ds := own (disk_status_name tr) (to_status ds).
Time
Lemma disk_status_agree id ds :
  disk_status_ctx ds -\226\136\151 is_OnlyDisk id -\226\136\151 \226\136\131 d, \226\140\156ds = OnlyDisk id d\226\140\157.
Time Proof.
Time iIntros "H1 H2".
Time iDestruct (own_valid_2 with "H1 H2") as % H.
Time (destruct ds; eauto).
Time Require Eqdep.
Time Import uPred.
Time
Class ghost_mapG (A : ofeT) \206\163 `{@LeibnizEquiv _ A.(ofe_equiv)}
`{OfeDiscrete A} :={ghost_map_inG :>
                     inG \206\163 (authR (optionUR (prodR countingR (agreeR A))))}.
Time
Definition ghost_map\206\163 (A : ofeT) `{@LeibnizEquiv _ A.(ofe_equiv)}
  `{OfeDiscrete A} : gFunctors :=
  #[ GFunctor (authR (optionUR (prodR countingR (agreeR A))))].
Time
Instance subG_ghost_mapG  (A : ofeT) \206\163 `{@LeibnizEquiv _ A.(ofe_equiv)}
 `{OfeDiscrete A}: (subG (ghost_map\206\163 A) \206\163 \226\134\146 ghost_mapG A \206\163).
Time rewrite Cinr_op in  {} H.
Time Proof.
Time solve_inG.
Time Qed.
Time Section ghost_var_helpers.
Time Context {A : ofeT} `{hGMG : @ghost_mapG A \206\163 H1 H2}.
Time
Definition ghost_mapsto (\206\179 : gname) (n : Z) (v : A) : 
  iProp \206\163 := (own \206\179 (\226\151\175 Some (Count n, to_agree v)))%I.
Time
Definition ghost_mapsto_auth (\206\179 : gname) (v : A) : 
  iProp \206\163 := own \206\179 (\226\151\143 Some (Count 0, to_agree v)).
Time End ghost_var_helpers.
Time #[local]
Notation "l \226\151\143\226\134\166 v" := (ghost_mapsto_auth l v)
  (at level 20, format "l  \226\151\143\226\134\166  v") : bi_scope.
Time #[local]
Notation "l \226\134\166{ q } v" := (ghost_mapsto l q v)
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  v") : bi_scope.
Time #[local]
Notation "l \226\134\166 v" := (ghost_mapsto l 0 v) (at level 20) : bi_scope.
Time #[local]
Notation "l \226\134\166{ q } -" := (\226\136\131 v, l \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  -") : bi_scope.
Time #[local]Notation "l \226\134\166 -" := (l \226\134\166{0} -)%I (at level 20) : bi_scope.
Time Section ghost_var_helpers.
Time Context {A} {\206\163} `{ghost_mapG A \206\163}.
Time Lemma ghost_var_alloc (a : A) : (|==> \226\136\131 \206\179, \206\179 \226\151\143\226\134\166 a \226\136\151 \206\179 \226\134\166 a)%I.
Time Proof.
Time
iMod
 (own_alloc (\226\151\143 Some (Count 0, to_agree a) \226\139\133 \226\151\175 Some (Count 0, to_agree a))) as
 ( \206\179 ) "[H1 H2]".
Time {
Time (apply auth_both_valid; split; eauto).
Time (split; econstructor).
Time }
Time iModIntro.
Time iExists \206\179.
Time iFrame.
Time Qed.
Time
Lemma ghost_var_bulk_alloc {L} {V} `{Countable L} 
  (m : gmap L V) (f : L \226\134\146 V \226\134\146 A) :
  (|==> \226\136\131 \206\147 : gmap L gname,
          \226\140\156dom (gset L) \206\147 = dom (gset L) m\226\140\157
          \226\136\151 ([\226\136\151 map] k\226\134\166v \226\136\136 m, \226\136\131 \206\179, \226\140\156\206\147 !! k = Some \206\179\226\140\157 \226\136\151 \206\179 \226\151\143\226\134\166 f k v \226\136\151 \206\179 \226\134\166 f k v))%I.
Time Proof.
Time iInduction m as [| k v] "IH" using map_ind.
Time -
Time iExists \226\136\133.
Time iSplitL "".
Time {
Time by rewrite ?dom_empty_L.
Time }
Time {
Time by iApply big_sepM_empty.
Time }
Time -
Time iMod "IH" as ( \206\147 Hdom ) "Hmap".
Time iMod (ghost_var_alloc (f k v)) as ( \206\179 ) "H".
Time iModIntro.
Time iExists (<[k:=\206\179]> \206\147).
Time iSplitL "".
Time {
Time iPureIntro.
Time rewrite ?dom_insert_L Hdom //.
Time }
Time {
Time (iApply big_sepM_insert; auto).
Time iSplitL "H".
Time {
Time iExists \206\179.
Time rewrite lookup_insert.
Time by iFrame.
Time }
Time {
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
Time iIntros ( k' x' Hin ) "H".
Time (rewrite lookup_insert_ne; auto).
Time (intros ->).
Time congruence.
Time }
Time }
Time Qed.
Time
Lemma ghost_var_agree \206\179 (a1 a2 : A) q : \206\179 \226\151\143\226\134\166 a1 -\226\136\151 \206\179 \226\134\166{q} a2 -\226\136\151 \226\140\156a1 = a2\226\140\157.
Time Proof.
Time iIntros "H\206\1791 H\206\1792".
Time iDestruct (own_valid_2 with "H\206\1791 H\206\1792") as % Hval.
Time (apply auth_both_valid in Hval as (Hincl, ?)).
Time
(<ssreflect_plugin::ssrtclseq@0>
 apply option_included in Hincl as [| (p1, (p2, (Heq1, (Heq2, Hcase))))] ;
 first  by congruence).
Time (inversion Heq1; subst).
Time (inversion Heq2; subst).
Time (destruct Hcase as [(Heq1', Heq2')| Hincl]).
Time -
Time (apply to_agree_inj in Heq2').
Time eauto.
Time -
Time (apply prod_included in Hincl as (?, Heq2'%to_agree_included); eauto).
Time Qed.
Time Lemma ghost_var_auth_valid \206\179 (a1 a2 : A) : \206\179 \226\151\143\226\134\166 a1 -\226\136\151 \206\179 \226\151\143\226\134\166 a2 -\226\136\151 False.
Time Proof.
Time (apply wand_intro_r).
Time rewrite -own_op //=.
Time rewrite /op /cmra_op //= /auth_op //=.
Time rewrite -Some_op /op /cmra_op //= /excl_op /prod_op //= frac_op'.
Time rewrite own_valid discrete_valid.
Time (iIntros ( [] ); exfalso; eauto).
Time Qed.
Time
Lemma ghost_valid \206\179 (q1 q2 : Z) (v1 v2 : A) :
  (q1 >= 0)%Z \226\134\146 (q2 >= 0)%Z \226\134\146 \206\179 \226\134\166{q1} v1 -\226\136\151 \206\179 \226\134\166{q2} v2 -\226\136\151 False.
Time Proof.
Time (intros).
Time (apply wand_intro_r).
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite -Some_op -pair_op.
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time lia.
Time Qed.
Time
Lemma ghost_valid' \206\179 (q1 q2 : nat) (v1 v2 : A) :
  \206\179 \226\134\166{q1} v1 -\226\136\151 \206\179 \226\134\166{q2} v2 -\226\136\151 False.
Time Proof.
Time (intros).
Time (eapply ghost_valid; lia).
Time Qed.
Time
Lemma ghost_var_agree2 \206\179 (a1 a2 : A) q1 q2 :
  \206\179 \226\134\166{q1} a1 -\226\136\151 \206\179 \226\134\166{q2} a2 -\226\136\151 \226\140\156a1 = a2\226\140\157.
Time Proof.
Time (apply wand_intro_r).
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite -Some_op -pair_op.
Time (intros [_ Heq%agree_op_invL']).
Time eauto.
Time Qed.
Time
Lemma read_split_join \206\179 (n : nat) (v : A) :
  \206\179 \226\134\166{n} v \226\138\163\226\138\162 \206\179 \226\134\166{S n} v \226\136\151 \206\179 \226\134\166{- 1} v.
Time Proof.
Time rewrite -own_op -auth_frag_op /ghost_mapsto.
Time f_equiv.
