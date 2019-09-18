Time From iris.algebra Require Import auth gmap agree.
Time From Perennial.CSL Require Import Counting.
Time From iris.base_logic.lib Require Export own.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Definition gen_heapUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (prodR countingR (agreeR (leibnizO V))).
Time
Definition to_gen_heap {L} {V} `{Countable L} : gmap L V \226\134\146 gen_heapUR L V :=
  fmap (\206\187 v, (Count 0, to_agree (v : leibnizO V))).
Time
Class gen_heapG (L V : Type) (\206\163 : gFunctors) `{Countable L} :=
 GenHeapG {gen_heap_inG :> inG \206\163 (authR (gen_heapUR L V));
           gen_heap_name : gname}.
Time Arguments gen_heap_name {_} {_} {_} {_} {_} _ : assert.
Time
Class gen_heapPreG (L V : Type) (\206\163 : gFunctors) `{Countable L} :={
 gen_heap_preG_inG :> inG \206\163 (authR (gen_heapUR L V))}.
Time
Definition gen_heap\206\163 (L V : Type) `{Countable L} : gFunctors :=
  #[ GFunctor (authR (gen_heapUR L V))].
Time
Instance subG_gen_heapPreG  {\206\163} {L} {V} `{Countable L}:
 (subG (gen_heap\206\163 L V) \206\163 \226\134\146 gen_heapPreG L V \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Section definitions.
Time Context `{hG : gen_heapG L V \206\163}.
Time
Definition gen_heap_ctx (\207\131 : gmap L V) : iProp \206\163 :=
  own (gen_heap_name hG) (\226\151\143 to_gen_heap \207\131).
Time
Definition mapsto_def (l : L) (n : Z) (v : V) : iProp \206\163 :=
  own (gen_heap_name hG) (\226\151\175 {[l := (Count n, to_agree (v : leibnizO V))]}).
Time Definition mapsto_aux : seal (@mapsto_def).
Time by eexists.
Time Qed.
Time Definition mapsto := mapsto_aux.(unseal).
Time Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
Time
Definition read_mapsto_def (l : L) (v : V) : iProp \206\163 :=
  own (gen_heap_name hG)
    (\226\151\175 {[l := (Count (- 1), to_agree (v : leibnizO V))]}).
Time Definition read_mapsto_aux : seal (@read_mapsto_def).
Time by eexists.
Time Qed.
Time Definition read_mapsto := read_mapsto_aux.(unseal).
Time
Definition read_mapsto_eq : @read_mapsto = @read_mapsto_def :=
  read_mapsto_aux.(seal_eq).
Time End definitions.
Time #[local]
Notation "l \226\134\166{ q } v" := (mapsto l q v)
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  v") : bi_scope.
Time #[local]Notation "l \226\134\166 v" := (mapsto l 0 v) (at level 20) : bi_scope.
Time #[local]
Notation "l \226\134\166{ q } -" := (\226\136\131 v, l \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  -") : bi_scope.
Time #[local]Notation "l \226\134\166 -" := (l \226\134\166{0} -)%I (at level 20) : bi_scope.
Time #[local]
Notation "l r\226\134\166 v" := (read_mapsto l v) (at level 20, format "l  r\226\134\166  v") :
  bi_scope.
Time #[local]
Notation "l r\226\134\166 -" := (\226\136\131 v, l r\226\134\166 v)%I (at level 20, format "l  r\226\134\166 -") :
  bi_scope.
Time Section to_gen_heap.
Time Context (L V : Type) `{Countable L}.
Time Implicit Type \207\131 : gmap L V.
Time Lemma to_gen_heap_valid \207\131 : \226\156\147 to_gen_heap \207\131.
Time Proof.
Time (intros l).
Time rewrite lookup_fmap.
Time by case (\207\131 !! l).
Time Qed.
Time
Lemma lookup_to_gen_heap_None \207\131 l : \207\131 !! l = None \226\134\146 to_gen_heap \207\131 !! l = None.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap lookup_fmap
 =>{+}->.
Time Qed.
Time
Lemma gen_heap_singleton_included \207\131 l q v :
  {[l := (q, to_agree v)]} \226\137\188 to_gen_heap \207\131 \226\134\146 \207\131 !! l = Some v.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite singleton_included =>-
 [[q' av] []]).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap lookup_fmap
 fmap_Some_equiv =>- [v' [Hl [/= {+}-> {+}->]]]).
Time
move  {}=>/Some_pair_included_total_2 [_]
 /to_agree_included/leibniz_equiv_iff {+}-> //.
Time Qed.
Time
Lemma to_gen_heap_insert l v \207\131 :
  to_gen_heap (<[l:=v]> \207\131) =
  <[l:=(Count 0, to_agree (v : leibnizO V))]> (to_gen_heap \207\131).
Time Proof.
Time by rewrite /to_gen_heap fmap_insert.
Time Qed.
Time
Lemma to_gen_heap_delete l \207\131 :
  to_gen_heap (delete l \207\131) = delete l (to_gen_heap \207\131).
Time Proof.
Time by rewrite /to_gen_heap fmap_delete.
Time Qed.
Time End to_gen_heap.
Time
Lemma gen_heap_init `{gen_heapPreG L V \206\163} \207\131 :
  (|==> \226\136\131 _ : gen_heapG L V \206\163, gen_heap_ctx \207\131)%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131)) as ( \206\179 ) "Hh".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_heap_valid {}.
Time }
Time iModIntro.
Time by iExists (GenHeapG L V \206\163 _ _ _ \206\179).
Time Qed.
Time
Lemma gen_heap_strong_init `{H : gen_heapPreG L V \206\163} 
  \207\131s :
  (|==> \226\136\131 (H0 : gen_heapG L V \206\163) (Hpf : @gen_heap_inG _ _ _ _ _ H0 =
                                        gen_heap_preG_inG),
          gen_heap_ctx \207\131s \226\136\151 own (gen_heap_name H0) (\226\151\175 to_gen_heap \207\131s))%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131s \226\139\133 \226\151\175 to_gen_heap \207\131s)) as ( \206\179 ) "(?&?)".
Time {
Time (apply auth_both_valid; split; auto).
Time exact : {}to_gen_heap_valid {}.
Time }
Time iModIntro.
Time (unshelve iExists (GenHeapG L V \206\163 _ _ _ \206\179) , _; auto).
Time iFrame.
Time Qed.
Time Section gen_heap.
Time Context `{hG : gen_heapG L V \206\163}.
Time Implicit Types P Q : iProp \206\163.
Time Implicit Type \206\166 : V \226\134\146 iProp \206\163.
Time Implicit Type \207\131 : gmap L V.
Time Implicit Types h g : gen_heapUR L V.
Time Implicit Type l : L.
Time Implicit Type v : V.
Time #[global]Instance mapsto_timeless  l q v: (Timeless (l \226\134\166{q} v)).
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time (apply _).
Time Qed.
Time #[global]Instance read_mapsto_timeless  l v: (Timeless (l r\226\134\166 v)).
Time Proof.
Time rewrite read_mapsto_eq /read_mapsto_def.
Time (apply _).
Time Qed.
Time
Lemma gen_heap_init_to_bigOp \207\131 :
  own (gen_heap_name hG) (\226\151\175 to_gen_heap \207\131) -\226\136\151 [\226\136\151 map] i\226\134\166v \226\136\136 \207\131, i \226\134\166 v.
Time Proof.
Time (induction \207\131 using map_ind).
Time -
Time iIntros.
Time rewrite //=.
Time -
Time iIntros "Hown".
Time rewrite big_opM_insert //.
Time
iAssert (own (gen_heap_name hG) (\226\151\175 to_gen_heap m) \226\136\151 i \226\134\166 x)%I with "[Hown]" as
 "[Hrest $]".
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite to_gen_heap_insert
 insert_singleton_op ; last  by apply lookup_to_gen_heap_None).
Time rewrite auth_frag_op.
Time iDestruct "Hown" as "(?&?)".
Time iFrame.
Time }
Time by iApply IH\207\131.
Time Qed.
Time
Lemma mapsto_agree l q1 q2 v1 v2 : l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite op_singleton singleton_valid -pair_op.
Time by intros [_ ?%agree_op_invL'].
Time Qed.
Time
Lemma mapsto_valid l q1 q2 v1 v2 :
  q1 >= 0 \226\134\146 q2 >= 0 \226\134\146 l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 False.
Time Proof.
Time (intros).
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite op_singleton singleton_valid -pair_op.
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time lia.
Time Qed.
Time
Lemma read_split_join l (q : nat) v : l \226\134\166{q} v \226\138\163\226\138\162 l \226\134\166{S q} v \226\136\151 l \226\134\166{- 1} v.
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
Time rewrite op_singleton -pair_op.
Time rewrite counting_op' //=.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time lia.
Time replace (S q + - 1)%Z with q : Z by lia.
Time by rewrite agree_idemp.
Time Qed.
Time
Lemma gen_heap_alloc \207\131 l v :
  \207\131 !! l = None \226\134\146 gen_heap_ctx \207\131 ==\226\136\151 gen_heap_ctx (<[l:=v]> \207\131) \226\136\151 l \226\134\166 v.
Time Proof.
Time iIntros ( ? ) "H\207\131".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time iMod (own_update with "H\207\131") as "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update_alloc,
  (alloc_singleton_local_update _ _ (Count 0, to_agree (v : leibnizO _)))
 =>//).
Time by apply lookup_to_gen_heap_None.
Time }
Time iModIntro.
Time rewrite to_gen_heap_insert.
Time iFrame.
Time Qed.
Time
Lemma gen_heap_dealloc \207\131 l v :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166 v ==\226\136\151 gen_heap_ctx (delete l \207\131).
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time rewrite to_gen_heap_delete.
Time iApply (own_update_2 with "H\207\131 Hl").
Time (eapply auth_update_dealloc, (delete_singleton_local_update _ _ _)).
Time Qed.
Time
Lemma gen_heap_valid \207\131 l q v :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166{q} v -\226\136\151 \226\140\156\207\131 !! l = Some v\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
(iDestruct (own_valid_2 with "H\207\131 Hl") as %
  [Hl%gen_heap_singleton_included _]%auth_both_valid; auto).
Time Qed.
Time
Lemma gen_heap_valid_2 \207\131 l v : gen_heap_ctx \207\131 -\226\136\151 l r\226\134\166 v -\226\136\151 \226\140\156\207\131 !! l = Some v\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx read_mapsto_eq /read_mapsto_def.
Time
(iDestruct (own_valid_2 with "H\207\131 Hl") as %
  [Hl%gen_heap_singleton_included _]%auth_both_valid; auto).
Time Qed.
Time
Lemma gen_heap_update \207\131 l v1 v2 :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166 v1 ==\226\136\151 gen_heap_ctx (<[l:=v2]> \207\131) \226\136\151 l \226\134\166 v2.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
iDestruct (own_valid_2 with "H\207\131 Hl") as %
 [Hl%gen_heap_singleton_included _]%auth_both_valid.
Time iMod (own_update_2 with "H\207\131 Hl") as "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update, singleton_local_update,
  (exclusive_local_update _ (Count 0, to_agree (v2 : leibnizO _))) =>//).
Time by rewrite /to_gen_heap lookup_fmap Hl.
Time }
Time iModIntro.
Time rewrite to_gen_heap_insert.
Time iFrame.
Time Qed.
Time End gen_heap.
