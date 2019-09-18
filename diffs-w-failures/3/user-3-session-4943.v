Time
From iris.algebra Require Import auth gmap frac agree namespace_map excl.
Time From stdpp Require Export namespaces.
Time From iris.base_logic.lib Require Export own.
Time From iris.base_logic.lib Require Import gen_heap.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Class leased_heapG (L V : Type) (\206\163 : gFunctors) `{Countable L} :=
 LeasedHeapG {leased_heap_heapG :> gen_heapG L V \206\163;
              leased_heap_exclG :>
               inG \206\163 (authR (optionUR (exclR (leibnizO V))));
              leased_heap_gen : namespace}.
Time Arguments leased_heap_heapG {_} {_} {_} {_} {_} _ : assert.
Time Arguments leased_heap_exclG {_} {_} {_} {_} {_} _ : assert.
Time Arguments leased_heap_gen {_} {_} {_} {_} {_} _ : assert.
Time
Class leased_heapPreG (L V : Type) (\206\163 : gFunctors) `{Countable L} :={
 leased_heap_heapPreG :> gen_heapPreG L V \206\163;
 leased_heap_exclPreG :> inG \206\163 (authR (optionUR (exclR (leibnizO V))))}.
Time
Definition leased_heap\206\163 (L V : Type) `{Countable L} : gFunctors :=
  #[ gen_heap\206\163 L V; GFunctor (authR (optionUR (exclR (leibnizO V))))].
Time
Instance subG_leased_heapPreG  {\206\163} {L} {V} `{Countable L}:
 (subG (leased_heap\206\163 L V) \206\163 \226\134\146 leased_heapPreG L V \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Definition current_gen (N : namespace) := ndot N 0.
Time Definition next_gen (N : namespace) := ndot N 1.
Time Lemma split_gen_disj N : current_gen N ## next_gen N.
Time Proof.
Time solve_ndisj.
Time Qed.
Time
Definition next_leased_heapG `{hG : leased_heapG L V \206\163} :=
  LeasedHeapG _ _ _ _ _ (@leased_heap_heapG _ _ _ _ _ hG)
    (@leased_heap_exclG _ _ _ _ _ hG) (next_gen (leased_heap_gen hG)).
Time Section definitions.
Time Context {L} {V} `{Countable L} `{hG : !leased_heapG L V \206\163}.
Time
Definition lease (l : L) (v : V) :=
  (\226\136\131 \206\179 : gname,
     meta l (current_gen (leased_heap_gen hG)) \206\179
     \226\136\151 own \206\179 (\226\151\175 Excl' (v : leibnizO V)))%I.
Time
Definition master (l : L) (v : V) :=
  (\226\136\131 \206\179 : gname,
     meta l (current_gen (leased_heap_gen hG)) \206\179
     \226\136\151 meta_token l (\226\134\145next_gen (leased_heap_gen hG))
       \226\136\151 own \206\179 (\226\151\143 Excl' (v : leibnizO V)))%I.
Time End definitions.
Time #[local]
Notation "l \226\134\166{ q } v" := (mapsto l q v)
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  v") : bi_scope.
Time #[local]Notation "l \226\134\166 v" := (mapsto l 1 v) (at level 20) : bi_scope.
Time #[local]
Notation "l \226\134\166{ q } -" := (\226\136\131 v, l \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  -") : bi_scope.
Time #[local]Notation "l \226\134\166 -" := (l \226\134\166{1} -)%I (at level 20) : bi_scope.
Time
Definition next_lease `{hG : leased_heapG L V \206\163} (l : L) 
  (v : V) := lease (hG:=next_leased_heapG) l v.
Time
Definition next_master `{hG : leased_heapG L V \206\163} 
  (l : L) (v : V) := master (hG:=next_leased_heapG) l v.
Time Section lease_heap.
Time Context {L} {V} `{Countable L} `{hG : !leased_heapG L V \206\163}.
Time Implicit Types P Q : iProp \206\163.
Time Implicit Type \206\166 : V \226\134\146 iProp \206\163.
Time Implicit Type \207\131 : gmap L V.
Time Implicit Type m : gmap L gname.
Time Implicit Types h g : gen_heapUR L V.
Time Implicit Type l : L.
Time Implicit Type v : V.
Time #[global]Instance lease_timeless  l v: (Timeless (lease l v)).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance master_timeless  l v: (Timeless (master l v)).
Time Proof.
Time (apply _).
Time Qed.
Time
Lemma master_lease_agree l (v1 v2 : V) :
  master l v1 -\226\136\151 lease l v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time
(iDestruct 1 as ( \206\179m1 ) "(H\206\1791&_&Hown1)"; iDestruct 1 as ( \206\179m2 ) "(H\206\1792&Hown2)").
Time iDestruct (meta_agree with "H\206\1791 H\206\1792") as % ->.
Time iDestruct (own_valid_2 with "Hown1 Hown2") as "H".
Time iDestruct "H" as % [<-%leibniz_equiv%Excl_included _]%auth_both_valid.
Time done.
Time Qed.
Time
Lemma meta_lease_init N l (\206\179 : gname) :
  meta_token l (\226\134\145N) ==\226\136\151 meta l (current_gen N) \206\179 \226\136\151 meta_token l (\226\134\145next_gen N).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 (union_difference_L (\226\134\145next_gen N) (\226\134\145N)) ; last  by solve_ndisj).
Time iIntros "H".
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (meta_token_union with "H") as
 "($&?)" ; first  set_solver).
Time
by <ssreflect_plugin::ssrtclseq@0> iMod
 (meta_set _ _ \206\179 (current_gen N) with "[$]") as "$" ; first  solve_ndisj.
Time Qed.
Time Lemma master_next l v : master l v ==\226\136\151 next_master l v \226\136\151 next_lease l v.
Time Proof.
Time iDestruct 1 as ( \206\179 ) "(H\206\179&Hrest&Hown)".
Time
iMod (own_alloc (\226\151\143 Excl' (v : leibnizO V) \226\139\133 \226\151\175 Excl' (v : leibnizO V))) as (
 \206\179' ) "[H1 H2]".
Time {
Time (apply auth_both_valid; split; eauto).
Time econstructor.
Time }
Time iMod (meta_lease_init _ _ \206\179' with "Hrest") as "(#Hset&Hrest)".
Time iModIntro.
Time (iSplitL "Hrest H1"; by iExists _; iFrame).
Time Qed.
Time
Lemma master_lease_alloc l v : meta_token l \226\138\164 ==\226\136\151 master l v \226\136\151 lease l v.
Time Proof.
Time iIntros "H".
Time
iMod (own_alloc (\226\151\143 Excl' (v : leibnizO V) \226\139\133 \226\151\175 Excl' (v : leibnizO V))) as ( \206\179
 ) "[H1 H2]".
Time {
Time (apply auth_both_valid; split; eauto).
Time econstructor.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 (union_difference_L (\226\134\145leased_heap_gen hG) \226\138\164) ; last  by solve_ndisj).
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct (meta_token_union with "H") as
 "(H&_)" ; first  set_solver).
Time iMod (meta_lease_init _ _ \206\179 with "H") as "(#Hset&Hrest)".
Time iModIntro.
Time (iSplitL "Hrest H1"; by iExists _; iFrame).
Time Qed.
Time
Lemma big_sepM_master_lease_alloc \207\131 :
  ([\226\136\151 map] l\226\134\166v \226\136\136 \207\131, meta_token l \226\138\164)
  ==\226\136\151 [\226\136\151 map] l\226\134\166v \226\136\136 \207\131, master l v \226\136\151 lease l v.
Time Proof.
Time iIntros "H".
Time (iApply (big_opM_forall (\206\187 P Q, P ==\226\136\151 Q)); auto using bupd_intro).
Time {
Time (intros P1 P2 HP Q1 Q2 HQ).
Time by rewrite HP HQ -bupd_sep.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  by eauto).
Time (intros; by iApply master_lease_alloc).
Time Qed.
Time
Lemma master_lease_update l v v0 v' :
  master l v -\226\136\151 lease l v0 ==\226\136\151 master l v' \226\136\151 lease l v'.
Time Proof.
Time
(iDestruct 1 as ( \206\179m1 ) "(H\206\1791&Hrest&Hown1)"; iDestruct 1 as ( \206\179m2 )
  "(H\206\1792&Hown2)").
Time iDestruct (meta_agree with "H\206\1791 H\206\1792") as % ->.
Time
iMod
 (own_update_2 _ _ _ (\226\151\143 Excl' (v' : leibnizO V) \226\139\133 \226\151\175 Excl' (v' : leibnizO V))
 with "Hown1 Hown2") as "[Hown1 Hown2]".
Time {
Time by apply auth_update, option_local_update, exclusive_local_update.
Time }
Time iModIntro.
Time (iSplitL "H\206\1791 Hrest Hown1"; iExists _; iFrame).
Time Qed.
Time
Lemma leased_heap_alloc \207\131 l v :
  \207\131 !! l = None
  \226\134\146 gen_heap_ctx \207\131
    ==\226\136\151 gen_heap_ctx (<[l:=v]> \207\131) \226\136\151 l \226\134\166 v \226\136\151 master l v \226\136\151 lease l v.
Time Proof.
Time iIntros ( H\207\131l ) "H".
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (gen_heap_alloc \207\131 l v with "H") as
 "($&$&H)" ; first  done).
Time by iApply master_lease_alloc.
Time Qed.
Time End lease_heap.
Time
Lemma heap_init_to_bigOp `{hG : leased_heapG L V \206\163} 
  (\207\131 : gmap L V) :
  own (i:=@gen_heap_inG _ _ _ _ _ (leased_heap_heapG hG))
    (gen_heap_name (leased_heap_heapG hG)) (\226\151\175 to_gen_heap \207\131)
  -\226\136\151 [\226\136\151 map] i\226\134\166v \226\136\136 \207\131, i \226\134\166 v.
Time Proof.
Time (induction \207\131 as [| ? ? ? ? IH] using map_ind).
Time -
Time iIntros.
Time rewrite //=.
Time -
Time iIntros "Hown".
Time rewrite big_opM_insert //.
Time
iAssert
 (own (i:=@gen_heap_inG _ _ _ _ _ (leased_heap_heapG hG))
    (gen_heap_name (leased_heap_heapG hG)) (\226\151\175 to_gen_heap m) \226\136\151 
  i \226\134\166 x)%I with "[Hown]" as "[Hrest $]".
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite to_gen_heap_insert
 insert_singleton_op ; last  by apply lookup_to_gen_heap_None).
Time rewrite auth_frag_op.
Time iDestruct "Hown" as "(?&?)".
Time iFrame.
Time }
Time by iApply IH.
Time Qed.
Time
Lemma leased_heap_strong_init `{H : leased_heapPreG L V \206\163} 
  \207\131 :
  (|==> \226\136\131 (H0 : leased_heapG L V \206\163) (Hpf : @gen_heap_inG _ _ _ _ _
                                             (leased_heap_heapG H0) =
                                           gen_heap_preG_inG),
          gen_heap_ctx \207\131 \226\136\151 ([\226\136\151 map] i\226\134\166v \226\136\136 \207\131, i \226\134\166 v \226\136\151 master i v \226\136\151 lease i v))%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \226\136\133)) as ( \206\179 ) "Hg".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_heap_valid {}.
Time }
Time iMod (own_alloc (\226\151\143 to_gen_meta \226\136\133)) as ( \206\179m ) "Hm".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_meta_valid {}.
Time }
Time (set (hG := GenHeapG L V \206\163 _ _ _ _ _ \206\179 \206\179m)).
Time (set (hL := LeasedHeapG L V \206\163 _ _ hG _ (1%positive :: nil))).
Time iAssert (gen_heap_ctx (hG:=hG) \226\136\133) with "[-]" as "H".
Time {
Time iExists \226\136\133.
Time iFrame.
Time eauto.
Time }
Time iMod (gen_heap_alloc_gen \226\136\133 \207\131 with "H") as "(Hctx&Hheap&Hmeta)".
Time {
Time (apply map_disjoint_empty_r).
Time }
Time rewrite right_id_L.
Time iMod (big_sepM_master_lease_alloc \207\131 with "Hmeta").
Time iModIntro.
Time iExists hL , eq_refl.
Time iFrame.
Time iApply big_sepM_sep.
Time iFrame.
Time Qed.
