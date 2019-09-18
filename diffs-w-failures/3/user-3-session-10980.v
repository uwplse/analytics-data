Time From iris.algebra Require Import auth gmap agree.
Time From Perennial.CSL Require Import Counting Count_GHeap.
Time From iris.base_logic.lib Require Export own.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Definition gen_dirUR (L1 L2 V : Type) `{Countable L1} 
  `{Countable L2} : ucmraT :=
  gmapUR L1 (gmapUR L2 (prodR countingR (agreeR (leibnizO V)))).
Time
Definition to_gen_dir {L1} {L2} {V} `{Countable L1} 
  `{Countable L2} : gmap L1 (gmap L2 V) \226\134\146 gen_dirUR L1 L2 V :=
  fmap (\206\187 m, to_gen_heap m).
Time
Class gen_dirG (L1 L2 V : Type) (\206\163 : gFunctors) `{Countable L1}
`{Countable L2} :=
 GenDirG {gen_dir_inG :> inG \206\163 (authR (gen_dirUR L1 L2 V));
          gen_dir_name : gname}.
Time Arguments gen_dir_name {_} {_} {_} {_} {_} {_} {_} {_} _ : assert.
Time
Class gen_dirPreG (L1 L2 V : Type) (\206\163 : gFunctors) 
`{Countable L1} `{Countable L2} :={gen_dir_preG_inG :>
                                    inG \206\163 (authR (gen_dirUR L1 L2 V))}.
Time
Definition gen_dir\206\163 (L1 L2 V : Type) `{Countable L1} 
  `{Countable L2} : gFunctors := #[ GFunctor (authR (gen_dirUR L1 L2 V))].
Time
Instance subG_gen_dirPreG  {\206\163} {L1} {L2} {V} `{Countable L1} 
 `{Countable L2}: (subG (gen_dir\206\163 L1 L2 V) \206\163 \226\134\146 gen_dirPreG L1 L2 V \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Section definitions.
Time Context `{hG : gen_dirG L1 L2 V \206\163}.
Time
Definition gen_dir_ctx (\207\131 : gmap L1 (gmap L2 V)) : 
  iProp \206\163 := own (gen_dir_name hG) (\226\151\143 to_gen_dir \207\131).
Time
Definition mapsto_def (l1 : L1) (l2 : L2) (n : Z) 
  (v : V) : iProp \206\163 :=
  own (gen_dir_name hG)
    (\226\151\175 {[l1 := {[l2 := (Count n, to_agree (v : leibnizO V))]}]}).
Time Definition mapsto_aux : seal (@mapsto_def).
Time by eexists.
Time Qed.
Time Definition mapsto := mapsto_aux.(unseal).
Time Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
Time Definition read_mapsto l1 l2 v : iProp \206\163 := mapsto l1 l2 (- 1) v.
Time End definitions.
Time #[local]
Notation "l1 / l2 \226\134\166{ q } v" := (mapsto l1 l2 q v)
  (at level 20, q  at level 50, format "l1 / l2  \226\134\166{ q }  v") : bi_scope.
Time #[local]
Notation "l1 / l2 \226\134\166 v" := (mapsto l1 l2 0 v) (at level 20) : bi_scope.
Time #[local]
Notation "l1 / l2 \226\134\166{ q } -" := (\226\136\131 v, l1/l2 \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l1 / l2  \226\134\166{ q }  -") : bi_scope.
Time #[local]
Notation "l1 / l2 \226\134\166 -" := (l1/l2 \226\134\166{0} -)%I (at level 20) : bi_scope.
Time #[local]
Notation "l1 / l2 r\226\134\166 v" := (read_mapsto l1 l2 v)
  (at level 20, format "l1 / l2  r\226\134\166  v") : bi_scope.
Time #[local]
Notation "l1 / l2 r\226\134\166 -" := (\226\136\131 v, l1/l2 r\226\134\166 v)%I
  (at level 20, format "l1 / l2  r\226\134\166 -") : bi_scope.
Time Section to_gen_dir.
Time Context (L1 L2 V : Type) `{Countable L1} `{Countable L2}.
Time Implicit Type \207\131 : gmap L1 (gmap L2 V).
Time Lemma to_gen_dir_valid \207\131 : \226\156\147 to_gen_dir \207\131.
Time Proof.
Time (intros l1).
Time rewrite lookup_fmap.
Time (<ssreflect_plugin::ssrtclseq@0> case (\207\131 !! l1) ; last  done).
Time (intros m l2).
Time rewrite lookup_fmap.
Time (case (m !! l2); done).
Time Qed.
Time
Lemma lookup_to_gen_dir_None \207\131 l : \207\131 !! l = None \226\134\146 to_gen_dir \207\131 !! l = None.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_dir lookup_fmap =>{+}->.
Time Qed.
Time
Lemma lookup_to_gen_dir_Some \207\131 \207\131d l :
  \207\131 !! l = Some \207\131d \226\134\146 to_gen_dir \207\131 !! l = Some (to_gen_heap \207\131d).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_dir lookup_fmap =>{+}->.
Time Qed.
Time
Lemma lookup_to_gen_dir_None2 \207\131 \207\131d l1 l2 :
  \207\131 !! l1 = Some \207\131d
  \226\134\146 \207\131d !! l2 = None
    \226\134\146 to_gen_dir \207\131 !! l1 = Some (to_gen_heap \207\131d) /\
      to_gen_heap \207\131d !! l2 = None.
Time Proof.
Time by intros ?%lookup_to_gen_dir_Some ?%lookup_to_gen_heap_None.
Time Qed.
Time
Lemma gen_dir_singleton_included \207\131 l1 l2 q v :
  {[l1 := {[l2 := (q, to_agree v)]}]} \226\137\188 to_gen_dir \207\131
  \226\134\146 \226\136\131 \207\131d, \207\131 !! l1 = Some \207\131d \226\136\167 \207\131d !! l2 = Some v.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite singleton_included =>-
 [[q' av] []]).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_dir lookup_fmap
 fmap_Some_equiv =>- [\207\131d [Hl {+}->]]).
Time move  {}=>/Some_included_total.
Time eauto using gen_heap_singleton_included.
Time Qed.
Time
Lemma to_gen_dir_insert1 l1 m \207\131 :
  to_gen_dir (<[l1:=m]> \207\131) = <[l1:=to_gen_heap m]> (to_gen_dir \207\131).
Time Proof.
Time by rewrite /to_gen_dir fmap_insert.
Time Qed.
Time
Lemma to_gen_dir_insert2 l1 l2 v (m : gmap L2 V) \207\131 :
  to_gen_dir (<[l1:=<[l2:=v]> m]> \207\131) =
  <[l1:=<[l2:=(Count 0, to_agree (v : leibnizO V))]> (to_gen_heap m)]>
    (to_gen_dir \207\131).
Time Proof.
Time by rewrite to_gen_dir_insert1 to_gen_heap_insert.
Time Qed.
Time
Lemma to_gen_dir_delete1 l \207\131 :
  to_gen_dir (delete l \207\131) = delete l (to_gen_dir \207\131).
Time Proof.
Time by rewrite /to_gen_dir fmap_delete.
Time Qed.
Time
Lemma to_gen_dir_delete2 (l1 : L1) (l2 : L2) (m : gmap L2 V) 
  \207\131 :
  to_gen_dir (<[l1:=delete l2 m]> \207\131) =
  <[l1:=delete l2 (to_gen_heap m)]> (to_gen_dir \207\131).
Time Proof.
Time by rewrite to_gen_dir_insert1 to_gen_heap_delete.
Time Qed.
Time End to_gen_dir.
Time
Lemma gen_dir_init `{gen_dirPreG L1 L2 V \206\163} \207\131 :
  (|==> \226\136\131 _ : gen_dirG L1 L2 V \206\163, gen_dir_ctx \207\131)%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_dir \207\131)) as ( \206\179 ) "Hh".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_dir_valid {}.
Time }
Time iModIntro.
Time by iExists (GenDirG L1 L2 V \206\163 _ _ _ _ _ \206\179).
Time Qed.
Time
Lemma gen_dir_strong_init `{gen_dirPreG L1 L2 V \206\163} 
  \207\131 :
  (|==> \226\136\131 (H0 : gen_dirG L1 L2 V \206\163) (Hpf : @gen_dir_inG _ _ _ _ _ _ _ _ H0 =
                                           gen_dir_preG_inG),
          gen_dir_ctx \207\131 \226\136\151 own (gen_dir_name H0) (\226\151\175 to_gen_dir \207\131))%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_dir \207\131 \226\139\133 \226\151\175 to_gen_dir \207\131)) as ( \206\179 ) "(?&?)".
Time {
Time (apply auth_both_valid; split; auto).
Time exact : {}to_gen_dir_valid {}.
Time }
Time iModIntro.
Time (unshelve iExists (GenDirG L1 L2 V \206\163 _ _ _ _ _ \206\179) , _; auto).
Time iFrame.
Time Qed.
Time Section gen_dir.
Time Context `{gen_dirG L1 L2 V \206\163}.
Time Implicit Types P Q : iProp \206\163.
Time Implicit Type \206\166 : V \226\134\146 iProp \206\163.
Time Implicit Type \207\131 : gmap L1 (gmap L2 V).
Time Implicit Types h g : gen_dirUR L1 L2 V.
Time Implicit Type v : V.
Time Implicit Type d : L1.
Time Implicit Type f : L2.
Time #[global]
Instance mapsto_timeless  (l1 : L1) (l2 : L2) q v: (Timeless (l1/l2 \226\134\166{q} v)).
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time (apply _).
Time Qed.
Time #[global]
Instance read_mapsto_timeless  (l1 : L1) (l2 : L2) v: (Timeless (l1/l2 r\226\134\166 v)).
Time Proof.
Time (apply _).
Time Qed.
Time
Lemma mapsto_agree d f q1 v1 v2 : d/f \226\134\166{q1} v1 -\226\136\151 d/f r\226\134\166 v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time (apply wand_intro_r).
Time rewrite /read_mapsto mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite ?op_singleton ?singleton_valid -pair_op.
Time by intros [_ ?%agree_op_invL'].
Time Qed.
Time
Lemma mapsto_valid d f q1 q2 v1 v2 :
  q1 >= 0 \226\134\146 q2 >= 0 \226\134\146 d/f \226\134\166{q1} v1 -\226\136\151 d/f \226\134\166{q2} v2 -\226\136\151 False.
Time Proof.
Time (intros).
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite ?op_singleton ?singleton_valid -pair_op.
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time lia.
Time Qed.
Time
Lemma read_split_join d f (q : nat) v : d/f \226\134\166{q} v \226\138\163\226\138\162 d/f \226\134\166{S q} v \226\136\151 d/f r\226\134\166 v.
Time Proof.
Time rewrite /read_mapsto mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
Time rewrite ?op_singleton -pair_op.
Time rewrite counting_op' //=.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time lia.
Time replace (S q + - 1)%Z with q : Z by lia.
Time by rewrite agree_idemp.
Time Qed.
Time
Lemma gen_dir_alloc1 \207\131 d f v :
  \207\131 !! d = None
  \226\134\146 gen_dir_ctx \207\131 ==\226\136\151 gen_dir_ctx (<[d:={[f := v]}]> \207\131) \226\136\151 d / f \226\134\166 v.
Time Proof.
Time iIntros ( ? ) "H\207\131".
Time rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
Time iMod (own_update with "H\207\131") as "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update_alloc,
  (alloc_singleton_local_update _ _
     {[f := (Count 0, to_agree (v : leibnizO _))]}) =>//).
Time -
Time by apply lookup_to_gen_dir_None.
Time -
Time by apply singleton_valid.
Time }
Time iModIntro.
Time rewrite to_gen_dir_insert1 /to_gen_heap map_fmap_singleton.
Time iFrame.
Time Qed.
Time
Lemma gen_dir_alloc2 \207\131 \207\131d d f v :
  \207\131 !! d = Some \207\131d
  \226\134\146 \207\131d !! f = None
    \226\134\146 gen_dir_ctx \207\131 ==\226\136\151 gen_dir_ctx (<[d:=<[f:=v]> \207\131d]> \207\131) \226\136\151 d / f \226\134\166 v.
Time Proof.
Time iIntros ( ? ? ) "H\207\131".
Time rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
Time iMod (own_update with "H\207\131") as "[H\207\131 Hl]".
Time {
Time (eapply auth_update_alloc).
Time (eapply insert_alloc_local_update).
Time -
Time by apply lookup_to_gen_dir_Some.
Time -
Time rewrite //=.
Time -
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply
  (alloc_singleton_local_update _ _ (Count 0, to_agree (v : leibnizO _)))
 =>//=).
Time by apply lookup_to_gen_heap_None.
Time }
Time iModIntro.
Time rewrite to_gen_dir_insert1 to_gen_heap_insert.
Time iFrame.
Time Qed.
Time
Lemma gen_dir_dealloc \207\131 \207\131d d f v :
  \207\131 !! d = Some \207\131d
  \226\134\146 gen_dir_ctx \207\131 -\226\136\151 d / f \226\134\166 v ==\226\136\151 gen_dir_ctx (<[d:=delete f \207\131d]> \207\131).
Time Proof.
Time iIntros ( ? ) "H\207\131 Hl".
Time rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
Time rewrite to_gen_dir_delete2.
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (own_update_2 with "H\207\131 Hl") as "[$ Hl]"
 ; last  by auto).
Time (eapply auth_update, singleton_local_update).
Time {
Time by eapply lookup_to_gen_dir_Some.
Time }
Time (eapply (delete_singleton_local_update _ _ _)).
Time Qed.
Time
Lemma gen_dir_valid \207\131 d f q v :
  gen_dir_ctx \207\131 -\226\136\151 d/f \226\134\166{q} v -\226\136\151 \226\140\156\226\136\131 \207\131d, \207\131 !! d = Some \207\131d \226\136\167 \207\131d !! f = Some v\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
Time
(iDestruct (own_valid_2 with "H\207\131 Hl") as %
  [Hl%gen_dir_singleton_included _]%auth_both_valid; auto).
Time Qed.
Time
Lemma gen_dir_valid_2 \207\131 d f v :
  gen_dir_ctx \207\131 -\226\136\151 d/f r\226\134\166 v -\226\136\151 \226\140\156\226\136\131 \207\131d, \207\131 !! d = Some \207\131d \226\136\167 \207\131d !! f = Some v\226\140\157.
Time Proof.
Time (apply gen_dir_valid).
Time Qed.
Time
Lemma gen_dir_update \207\131 \207\131d d f v1 v2 :
  \207\131 !! d = Some \207\131d
  \226\134\146 gen_dir_ctx \207\131
    -\226\136\151 d / f \226\134\166 v1 ==\226\136\151 gen_dir_ctx (<[d:=<[f:=v2]> \207\131d]> \207\131) \226\136\151 d / f \226\134\166 v2.
Time Proof.
Time iIntros ( ? ) "H\207\131 Hl".
Time rewrite /gen_dir_ctx mapsto_eq /mapsto_def.
Time
iDestruct (own_valid_2 with "H\207\131 Hl") as %
 [Hl%gen_dir_singleton_included _]%auth_both_valid.
Time (destruct Hl as (\207\131d', (Hlookup, Hdf))).
Time (assert (\207\131d = \207\131d') as <- by congruence).
Time iMod (own_update_2 with "H\207\131 Hl") as "[H\207\131 Hl]".
Time {
Time (eapply auth_update, singleton_local_update).
Time {
Time by eapply lookup_to_gen_dir_Some.
Time }
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply singleton_local_update,
  (exclusive_local_update _ (Count 0, to_agree (v2 : leibnizO _))) =>//).
Time by rewrite /to_gen_dir lookup_fmap Hdf.
Time }
Time iModIntro.
Time rewrite to_gen_dir_insert2.
Time iFrame.
Time Qed.
Time End gen_dir.
