Time From iris.algebra Require Import auth agree functions csum.
Time From Perennial.CSL Require Import Counting.
Time From iris.base_logic.lib Require Export own.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time From Perennial Require Export Spec.LockDefs.
Time Set Default Proof Using "Type".
Time Import uPred.
Time From Classes Require Import EqualDec.
Time Import EqualDecNotation.
Time #[global]
Instance partial_fn_insert  (A T : Type) `{EqualDec A}:
 (Insert A T (A \226\134\146 option T)) :=
 (\206\187 (a : A) (t : T) (f : A \226\134\146 option T) (b : A),
    if b == a then Some t else f b).
Time #[global]
Instance partial_fn_delete  (A T : Type) `{EqualDec A}:
 (Delete A (A \226\134\146 option T)) :=
 (\206\187 (a : A) (f : A \226\134\146 option T) (b : A), if b == a then None else f b).
Time Definition lockR := csumR natR (agreeR unitO).
Time
Definition to_lock (s : LockStatus) : lockR :=
  match s with
  | Locked => Cinr (to_agree tt)
  | ReadLocked n => Cinl (S n)
  | Unlocked => Cinl O
  end.
Time
Definition gen_heapUR (L V : Type) `{EqualDec L} : ucmraT :=
  discrete_funUR
    (fun a : L =>
     optionUR (prodR countingR (prodR lockR (agreeR (leibnizO V))))).
Time
Definition to_gen_heap {L} {V} `{EqualDec L}
  (f : L \226\134\146 option (LockStatus * V)) : gen_heapUR L V :=
  \206\187 k,
    match f k with
    | None => None
    | Some (s, v) => Some (Count 0, (to_lock s, to_agree (v : leibnizO V)))
    end.
Time
Class gen_heapG (L V : Type) (\206\163 : gFunctors) `{EqualDec L} :=
 GenHeapG {gen_heap_inG :> inG \206\163 (authR (@gen_heapUR L V _));
           gen_heap_name : gname}.
Time Arguments gen_heap_name {_} {_} {_} {_} _ : assert.
Time
Class gen_heapPreG (L V : Type) (\206\163 : gFunctors) `{EqualDec L} :={
 gen_heap_preG_inG :> inG \206\163 (authR (gen_heapUR L V))}.
Time
Definition gen_heap\206\163 (L V : Type) `{EqualDec L} : gFunctors :=
  #[ GFunctor (authR (gen_heapUR L V))].
Time
Instance subG_gen_heapPreG  {\206\163} {L} {V} `{EqualDec L}:
 (subG (gen_heap\206\163 L V) \206\163 \226\134\146 gen_heapPreG L V \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Section definitions.
Time Context `{hG : gen_heapG L V \206\163}.
Time
Definition gen_heap_ctx (\207\131 : L \226\134\146 option (LockStatus * V)) : 
  iProp \206\163 := own (gen_heap_name hG) (\226\151\143 to_gen_heap \207\131).
Time
Definition mapsto_def (l : L) (n : Z) (s : LockStatus) 
  (v : V) : iProp \206\163 :=
  own (gen_heap_name hG)
    (\226\151\175 ((fun l' =>
         if l' == l
         then Some (Count (n : Z), (to_lock s, to_agree (v : leibnizO V)))
         else \206\181)
          : gen_heapUR L V)).
Time Definition mapsto_aux : seal (@mapsto_def).
Time by eexists.
Time Qed.
Time Definition mapsto := mapsto_aux.(unseal).
Time Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
Time Definition read_mapsto l s v := mapsto l (- 1) s v.
Time End definitions.
Time #[local]
Notation "l \226\134\166{ q } v" := (mapsto l q Unlocked v)
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  v") : bi_scope.
Time #[local]
Notation "l \226\134\166 v" := (mapsto l 0 Unlocked v) (at level 20) : bi_scope.
Time #[local]
Notation "l \226\134\166{ q } -" := (\226\136\131 v, l \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  -") : bi_scope.
Time #[local]Notation "l \226\134\166 -" := (l \226\134\166{0} -)%I (at level 20) : bi_scope.
Time #[local]
Notation "l r\226\134\166 v" := (read_mapsto l Unlocked v)
  (at level 20, format "l  r\226\134\166  v") : bi_scope.
Time #[local]
Notation "l r\226\134\166 -" := (\226\136\131 v, l r\226\134\166 v)%I (at level 20, format "l  r\226\134\166 -") :
  bi_scope.
Time Section to_gen_heap.
Time Context (L V : Type) `{EqualDec L}.
Time Implicit Type \207\131 : L \226\134\146 option (LockStatus * V).
Time Lemma to_gen_heap_valid \207\131 : \226\156\147 to_gen_heap \207\131.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>l).
Time (destruct (\207\131 l) as [([], ?)| ]; by econstructor; simpl; eauto).
Time Qed.
Time Lemma lookup_to_gen_heap_None \207\131 l : \207\131 l = None \226\134\146 to_gen_heap \207\131 l = None.
Time Proof.
Time rewrite /to_gen_heap.
Time by case (\207\131 l).
Time Qed.
Time
Lemma gen_heap_singleton_included \207\131 l q s v :
  ((fun l' =>
    if l' == l then Some (Count q, (to_lock s, to_agree (v : leibnizO V)))
    else \206\181)
     : gen_heapUR L V) \226\137\188 to_gen_heap \207\131
  \226\134\146 \226\136\131 s', \207\131 l = Some (s', v) \226\136\167 to_lock s \226\137\188 to_lock s'.
Time Proof.
Time (intros Hincl).
Time (apply (discrete_fun_included_spec_1 _ _ l) in Hincl).
Time move : {}Hincl {}.
Time rewrite /to_gen_heap.
Time (<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  congruence).
Time (destruct (\207\131 l) as [(s', v')| ]).
Time -
Time move /Some_pair_included {}=>[_ Hincl].
Time (apply Some_pair_included in Hincl as [Hincl1 Hincl2]).
Time
(move /Some_included_total/to_agree_included/leibniz_equiv_iff {} in 
  {} Hincl2; subst).
Time (exists s'; split; auto).
Time (apply Some_included in Hincl1 as [->| ?]; auto).
Time
(<ssreflect_plugin::ssrtclintros@0> destruct s' =>//=; apply csum_included;
  intuition eauto).
Time -
Time rewrite option_included.
Time (intros [?| Hcase]).
Time *
Time congruence.
Time *
Time (repeat destruct Hcase as [? Hcase]).
Time congruence.
Time Qed.
Time Lemma to_lock_inj s s' : to_lock s \226\137\161 to_lock s' \226\134\146 s = s'.
Time (destruct s, s'; inversion 1; auto; congruence).
Time Qed.
Time
Lemma gen_heap_singleton_full_included \207\131 l s v :
  ((fun l' =>
    if l' == l then Some (Count 0, (to_lock s, to_agree (v : leibnizO V)))
    else \206\181)
     : gen_heapUR L V) \226\137\188 to_gen_heap \207\131 \226\134\146 \207\131 l = Some (s, v).
Time Proof.
Time (intros Hincl).
Time (apply (discrete_fun_included_spec_1 _ _ l) in Hincl).
Time move : {}Hincl {}.
Time rewrite /to_gen_heap.
Time (<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  congruence).
Time (destruct (\207\131 l) as [(s', v')| ]).
Time -
Time move /Some_included_exclusive {}=>Hequiv.
Time (feed pose proof Hequiv as Hequiv'; clear Hequiv).
Time {
Time (repeat <ssreflect_plugin::ssrtclintros@0> econstructor =>//=).
Time (destruct s'; econstructor).
Time }
Time (destruct Hequiv' as [? [Heq1 Heq2]]).
Time
(move /to_lock_inj {} in  {} Heq1; move /to_agree_inj/leibniz_equiv_iff {}
  in  {} Heq2; subst; auto).
Time -
Time rewrite option_included.
Time (intros [?| Hcase]).
Time *
Time congruence.
Time *
Time (repeat destruct Hcase as [? Hcase]).
Time congruence.
Time Qed.
Time
Lemma to_gen_heap_insert l s v \207\131 :
  to_gen_heap (<[l:=(s, v)]> \207\131)
  \226\137\161 <[l:=(Count 0, (to_lock s, to_agree (v : leibnizO V)))]> (to_gen_heap \207\131).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>k //=).
Time rewrite /insert /partial_fn_insert.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (k == l) =>//=).
Time Qed.
Time
Lemma to_gen_heap_delete l \207\131 :
  to_gen_heap (delete l \207\131) \226\137\161 delete l (to_gen_heap \207\131).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>k //=).
Time rewrite /delete /partial_fn_delete.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (k == l) =>//=).
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
Time by iExists (GenHeapG L V \206\163 _ _ \206\179).
Time Qed.
Time
Lemma gen_heap_strong_init `{H : gen_heapPreG L V \206\163} 
  \207\131s :
  (|==> \226\136\131 (H0 : gen_heapG L V \206\163) (Hpf : gen_heap_inG = gen_heap_preG_inG),
          gen_heap_ctx \207\131s \226\136\151 own (gen_heap_name _) (\226\151\175 to_gen_heap \207\131s))%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131s \226\139\133 \226\151\175 to_gen_heap \207\131s)) as ( \206\179 ) "(?&?)".
Time {
Time (apply auth_both_valid; split; auto).
Time exact : {}to_gen_heap_valid {}.
Time }
Time iModIntro.
Time (unshelve iExists (GenHeapG L V \206\163 _ _ \206\179) , _; auto).
Time iFrame.
Time Qed.
Time Section gen_heap.
Time Context `{hG : gen_heapG L V \206\163}.
Time Implicit Types P Q : iProp \206\163.
Time Implicit Type \206\166 : V \226\134\146 iProp \206\163.
Time Implicit Type \207\131 : L \226\134\146 option (LockStatus * V).
Time Implicit Types h g : gen_heapUR L V.
Time Implicit Type l : L.
Time Implicit Type v : V.
Time #[global]Instance mapsto_timeless  l q m v: (Timeless (mapsto l q m v)).
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time (apply _).
Time Qed.
Time #[global]Instance read_mapsto_timeless  l v: (Timeless (l r\226\134\166 v)).
Time Proof.
Time (apply _).
Time Qed.
Time
Lemma gen_heap_init_to_bigOp `{Countable L} (\207\131 : gmap L (LockStatus * V)) :
  (\226\136\128 s x, \207\131 !! s = Some x \226\134\146 fst x = Unlocked)
  \226\134\146 own (gen_heap_name hG) (\226\151\175 to_gen_heap (\206\187 s, \207\131 !! s))
    -\226\136\151 [\226\136\151 map] i\226\134\166x \226\136\136 \207\131, i \226\134\166 snd x.
Time Proof.
Time (induction \207\131 using map_ind).
Time -
Time iIntros.
Time rewrite //=.
Time -
Time iIntros ( Hunlocked ) "Hown".
Time rewrite big_opM_insert //.
Time
iAssert (own (gen_heap_name hG) (\226\151\175 to_gen_heap (\206\187 s, m !! s)) \226\136\151 i \226\134\166 snd x)%I
 with "[Hown]" as "[Hrest $]".
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time
iAssert (own (gen_heap_name hG) (\226\151\175 to_gen_heap (<[i:=x]> (\206\187 s : L, m !! s))))
 with "[Hown]" as "Hown'".
Time {
Time iApply (own_proper with "Hown").
Time f_equiv.
Time (intros k).
Time rewrite /to_gen_heap /insert /partial_fn_insert //=.
Time (destruct (equal)).
Time *
Time subst.
Time rewrite lookup_insert //=.
Time *
Time rewrite lookup_insert_ne //=.
Time }
Time (assert (Heq_unlocked : fst x = Unlocked)).
Time {
Time (eapply (Hunlocked i)).
Time by rewrite lookup_insert.
Time }
Time (destruct x as (l, v)).
Time rewrite to_gen_heap_insert.
Time rewrite -own_op.
Time iApply (own_proper with "Hown'").
Time rewrite -auth_frag_op.
Time f_equiv.
Time (intros k).
Time rewrite discrete_fun_lookup_op.
Time rewrite /insert /partial_fn_insert //=.
Time (destruct (k == i)).
Time -
Time subst.
Time rewrite lookup_to_gen_heap_None //.
Time rewrite left_id.
Time (simpl in Heq_unlocked).
Time by rewrite Heq_unlocked.
Time -
Time by rewrite right_id.
Time }
Time iApply IH\207\131.
Time *
Time (intros).
Time (eapply (Hunlocked s)).
Time (rewrite lookup_insert_ne; eauto).
Time (intros Heq).
Time congruence.
Time *
Time eauto.
Time Qed.
Time
Lemma mapsto_agree_generic l (q1 q2 : Z) ls1 ls2 v1 
  v2 : mapsto l q1 ls1 v1 -\226\136\151 mapsto l q2 ls2 v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time (intros Hval).
Time move : {}(Hval l) {}.
Time rewrite discrete_fun_lookup_op.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time rewrite -Some_op -pair_op.
Time by intros [_ [_ ?%agree_op_invL']].
Time Qed.
Time
Lemma mapsto_agree l q1 q2 v1 v2 : l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time (apply mapsto_agree_generic).
Time Qed.
Time
Lemma mapsto_valid_generic l (q1 q2 : Z) ls1 ls2 v1 
  v2 :
  (q1 >= 0 \226\134\146 q2 >= 0 \226\134\146 mapsto l q1 ls1 v1 -\226\136\151 mapsto l q2 ls2 v2 -\226\136\151 False)%Z.
Time Proof.
Time (intros ? ?).
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time (intros Hval).
Time move : {}(Hval l) {}.
Time rewrite discrete_fun_lookup_op.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time rewrite -Some_op -pair_op.
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time lia.
Time Qed.
Time
Lemma mapsto_valid l q1 q2 v1 v2 :
  (q1 >= 0 \226\134\146 q2 >= 0 \226\134\146 l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 False)%Z.
Time Proof.
Time (intros).
Time (apply mapsto_valid_generic; eauto).
Time Qed.
Time Lemma mapsto_valid' l v1 v2 : l \226\134\166{0} v1 -\226\136\151 l \226\134\166{- 1} v2 -\226\136\151 False.
Time Proof.
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time (intros Hval).
Time move : {}(Hval l) {}.
Time rewrite discrete_fun_lookup_op.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time rewrite -Some_op -pair_op.
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time Qed.
Time
Lemma read_split_join1 l (q : nat) n v :
  mapsto l q (ReadLocked n) v
  \226\138\163\226\138\162 mapsto l (S q) Unlocked v \226\136\151 mapsto l (- 1) (ReadLocked n) v.
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> split =>//= l').
Time rewrite discrete_fun_lookup_op.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
Time rewrite -Some_op -?pair_op.
Time rewrite counting_op' //= -Cinl_op.
Time replace (S q + - 1)%Z with q : Z by lia.
Time (assert (Hop : 0 \226\139\133 S n = S n) by auto).
Time replace (S q + - 1)%Z with q : Z by lia.
Time (repeat destruct (decide); try lia).
Time rewrite Hop.
Time rewrite agree_idemp //=.
Time Qed.
Time
Lemma read_split_join2 l (q : nat) n v :
  mapsto l q (ReadLocked n) v
  \226\138\163\226\138\162 mapsto l (S q) (ReadLocked n) v \226\136\151 mapsto l (- 1) Unlocked v.
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> split =>//= l').
Time rewrite discrete_fun_lookup_op.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
Time rewrite -Some_op -?pair_op.
Time rewrite counting_op' //= -Cinl_op.
Time replace (S q + - 1)%Z with q : Z by lia.
Time (assert (Hop : S n \226\139\133 0 = S n) by auto).
Time replace (S q + - 1)%Z with q : Z by lia.
Time (repeat destruct (decide); try lia).
Time rewrite Hop.
Time rewrite agree_idemp //=.
Time Qed.
Time
Lemma read_split_join3 l (q : nat) v :
  mapsto l q Locked v \226\138\163\226\138\162 mapsto l (S q) Locked v \226\136\151 mapsto l (- 1) Locked v.
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> split =>//= l').
Time rewrite discrete_fun_lookup_op.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
Time rewrite -Some_op -?pair_op.
Time rewrite counting_op' //= -Cinr_op.
Time replace (S q + - 1)%Z with q : Z by lia.
Time (repeat destruct (decide); try lia).
Time rewrite ?agree_idemp //=.
Time Qed.
Time Lemma read_split_join l (q : nat) v : l \226\134\166{q} v \226\138\163\226\138\162 l \226\134\166{S q} v \226\136\151 l r\226\134\166 v.
Time Proof.
Time rewrite /read_mapsto mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> split =>//= l').
Time rewrite discrete_fun_lookup_op.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
Time rewrite -Some_op -?pair_op.
Time rewrite counting_op' //= -Cinl_op.
Time replace (S q + - 1)%Z with q : Z by lia.
Time (repeat destruct (decide); try lia).
Time rewrite agree_idemp //=.
Time Qed.
Time
Lemma discrete_fun_local_update `{EqualDec A} {B : A \226\134\146 ucmraT} 
  f1 f2 f1' f2' :
  (\226\136\128 x, (f1 x, f2 x) ~l~> (f1' x, f2' x))
  \226\134\146 (f1 : discrete_fun B, f2) ~l~> (f1', f2').
Time Proof.
Time (intros Hupd).
Time
(<ssreflect_plugin::ssrtclintros@0> apply local_update_unital =>n mf Hmv Hm;
  simpl in *).
Time split.
Time -
Time (intros k).
Time specialize (Hupd k).
Time specialize (Hm k).
Time rewrite discrete_fun_lookup_op in  {} Hm.
Time (edestruct (Hupd n (Some (mf k))); eauto).
Time -
Time (intros k).
Time specialize (Hupd k).
Time specialize (Hm k).
Time rewrite discrete_fun_lookup_op in  {} Hm.
Time (edestruct (Hupd n (Some (mf k))); eauto).
Time Qed.
Time
Lemma gen_heap_ctx_proper \207\131 \207\131' :
  (\226\136\128 k, \207\131 k = \207\131' k) \226\134\146 gen_heap_ctx \207\131 -\226\136\151 gen_heap_ctx \207\131'.
Time Proof.
Time (intros Hequiv).
Time rewrite /gen_heap_ctx.
Time iApply own_mono.
Time rewrite /to_gen_heap.
Time
(apply auth_included; split; <ssreflect_plugin::ssrtclintros@0> auto =>//=).
Time exists \206\181.
Time rewrite right_id.
Time (do 2 f_equiv).
Time (intros k).
Time (apply to_agree_ne).
Time (intros l).
Time (rewrite Hequiv; eauto).
Time Qed.
Time
Lemma gen_heap_alloc \207\131 l v :
  \207\131 l = None
  \226\134\146 gen_heap_ctx \207\131 ==\226\136\151 gen_heap_ctx (<[l:=(Unlocked, v)]> \207\131) \226\136\151 l \226\134\166 v.
Time Proof.
Time iIntros ( Hnone ) "H\207\131".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
iMod
 (own_update _ _
    (\226\151\143 to_gen_heap (<[l:=(Unlocked, v)]> \207\131)
     \226\139\133 \226\151\175 <[l:=(Count 0, (Cinl 0, to_agree v))]> \206\181) with "H\207\131") as "[H\207\131 Hl]".
Time {
Time (eapply auth_update_alloc).
Time
(<ssreflect_plugin::ssrtclintros@0> apply discrete_fun_local_update =>k).
Time rewrite /to_gen_heap.
Time rewrite /insert /partial_fn_insert.
Time (destruct (k == l)).
Time *
Time subst.
Time rewrite /insert /partial_fn_insert.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time rewrite Hnone.
Time rewrite discrete_fun_lookup_empty.
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply
  (alloc_option_local_update
     (Count 0, (to_lock Unlocked, to_agree (v : leibnizO _)))) =>//).
Time *
Time reflexivity.
Time }
Time by iFrame.
Time Qed.
Time
Lemma gen_heap_dealloc \207\131 l v :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166 v ==\226\136\151 gen_heap_ctx (delete l \207\131).
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time rewrite to_gen_heap_delete.
Time iApply (own_update_2 with "H\207\131 Hl").
Time (eapply auth_update_dealloc).
Time
(<ssreflect_plugin::ssrtclintros@0> apply discrete_fun_local_update =>k).
Time rewrite /delete /partial_fn_delete.
Time (destruct (k == l)).
Time *
Time (apply delete_option_local_update; apply _).
Time *
Time reflexivity.
Time Qed.
Time
Lemma gen_heap_valid1 \207\131 l s v :
  gen_heap_ctx \207\131 -\226\136\151 mapsto l 0 s v -\226\136\151 \226\140\156\207\131 l = Some (s, v)\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
(iDestruct (own_valid_2 with "H\207\131 Hl") as % [Hl _]%auth_both_valid; auto).
Time (apply gen_heap_singleton_full_included in Hl; eauto).
Time Qed.
Time
Lemma gen_heap_valid2 \207\131 l z s v :
  gen_heap_ctx \207\131
  -\226\136\151 mapsto l z s v
     -\226\136\151 \226\140\156\226\136\131 s' : LockStatus, \207\131 l = Some (s', v) \226\136\167 to_lock s \226\137\188 to_lock s'\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
(iDestruct (own_valid_2 with "H\207\131 Hl") as % [Hl _]%auth_both_valid; auto).
Time (apply gen_heap_singleton_included in Hl; eauto).
Time Qed.
Time
Lemma gen_heap_valid \207\131 l q v :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166{q} v -\226\136\151 \226\140\156\226\136\131 s, \207\131 l = Some (s, v) \226\136\167 s \226\137\160 Locked\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
(iDestruct (own_valid_2 with "H\207\131 Hl") as %
  [(s', (Hl, Hincl))%gen_heap_singleton_included _]%auth_both_valid; auto).
Time (iExists s'; iPureIntro; split; auto).
Time (destruct s'; auto).
Time rewrite //= in  {} Hincl.
Time (apply csum_included in Hincl).
Time
(destruct Hincl as [| [(?, (?, ?))| (?, (?, ?))]]; intuition; try congruence).
Time Qed.
Time
Lemma gen_heap_update \207\131 l s1 s2 v1 v2 :
  gen_heap_ctx \207\131
  -\226\136\151 mapsto l 0 s1 v1 ==\226\136\151 gen_heap_ctx (<[l:=(s2, v2)]> \207\131) \226\136\151 mapsto l 0 s2 v2.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
iDestruct (own_valid_2 with "H\207\131 Hl") as %
 [Hl%gen_heap_singleton_included _]%auth_both_valid.
Time
iMod
 (own_update_2 _ _ _
    (\226\151\143 to_gen_heap (<[l:=(s2, v2)]> \207\131)
     \226\139\133 \226\151\175 <[l:=(Count 0, (to_lock s2, to_agree v2))]> \206\181) with "H\207\131 Hl") as
 "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update, discrete_fun_local_update =>k).
Time rewrite /to_gen_heap /insert /partial_fn_insert //=.
Time (destruct (k == l)).
Time *
Time subst.
Time (destruct Hl as (s', (Hl, ?))).
Time rewrite Hl.
Time unshelve apply : {}option_local_update {}.
Time (<ssreflect_plugin::ssrtclintros@0> apply exclusive_local_update =>//=).
Time (repeat <ssreflect_plugin::ssrtclintros@0> econstructor =>//=).
Time (destruct s2; econstructor).
Time *
Time reflexivity.
Time }
Time by iFrame.
Time Qed.
Time
Lemma Cinl_included_nat (n m : nat) : (Cinl n : lockR) \226\137\188 Cinl m \226\134\146 n <= m.
Time Proof.
Time rewrite csum_included.
Time
(intros [| [(n', (m', (Heqn, (Heqm, Hincl))))| (?, (?, ?))]]; intuition;
  try congruence).
Time (inversion Heqn).
Time (inversion Heqm).
Time subst.
Time by apply nat_included in Hincl.
Time Qed.
Time
Lemma Cinl_included_nat' (n : nat) s :
  (Cinl n : lockR) \226\137\188 to_lock s \226\134\146 \226\136\131 m, n <= m \226\136\167 to_lock s = Cinl m.
Time Proof.
Time rewrite csum_included.
Time
(intros [| [(n', (m', (Heqn, (Heqm, Hincl))))| (?, (?, ?))]]; intuition;
  try congruence).
Time {
Time (destruct s; simpl in *; congruence).
Time }
Time (inversion Heqn).
Time (inversion Heqm).
Time subst.
Time (apply nat_included in Hincl).
Time (eexists; split; eauto).
Time Qed.
Time
Lemma Cinr_included_excl' s :
  (Cinr (to_agree tt) : lockR) \226\137\188 to_lock s \226\134\146 s = Locked.
Time Proof.
Time rewrite csum_included.
Time
(intros [| [(n', (m', (Heqn, (Heqm, Hincl))))| (?, (?, ?))]]; intuition;
  destruct s; simpl in *; congruence).
Time Qed.
Time
Lemma gen_heap_readlock \207\131 l q v :
  gen_heap_ctx \207\131
  -\226\136\151 mapsto l q Unlocked v
     ==\226\136\151 \226\136\131 s,
           \226\140\156\207\131 l = Some (s, v)\226\140\157
           \226\136\151 gen_heap_ctx (<[l:=(force_read_lock s, v)]> \207\131)
             \226\136\151 mapsto l q (ReadLocked 0) v.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
iDestruct (own_valid_2 with "H\207\131 Hl") as %
 [Hl%gen_heap_singleton_included _]%auth_both_valid.
Time (destruct Hl as (s, (Hl, Hincl))).
Time
iMod
 (own_update_2 _ _ _
    (\226\151\143 to_gen_heap (<[l:=(force_read_lock s, v)]> \207\131)
     \226\139\133 \226\151\175 <[l:=(Count q, (to_lock (ReadLocked 0), to_agree v))]> \206\181)
 with "H\207\131 Hl") as "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update, discrete_fun_local_update =>k).
Time rewrite /to_gen_heap /insert /partial_fn_insert //=.
Time (destruct (k == l)).
Time *
Time subst.
Time rewrite Hl.
Time unshelve apply : {}option_local_update {}.
Time unshelve apply : {}prod_local_update_2 {}.
Time (destruct s).
Time **
Time (simpl in Hincl).
Time (apply csum_included in Hincl).
Time
(destruct Hincl as [| [(?, (?, ?))| (?, (?, ?))]]; intuition; try congruence).
Time **
Time (simpl).
Time unshelve apply : {}prod_local_update_1 {}.
Time (apply csum_local_update_l).
Time (apply nat_local_update; lia).
Time **
Time (simpl).
Time unshelve apply : {}prod_local_update_1 {}.
Time (apply csum_local_update_l).
Time (apply nat_local_update; lia).
Time *
Time reflexivity.
Time }
Time iExists s.
Time by iFrame.
Time Qed.
Time
Lemma gen_heap_readlock' \207\131 l q v n :
  gen_heap_ctx \207\131
  -\226\136\151 mapsto l q (ReadLocked n) v
     ==\226\136\151 \226\136\131 s,
           \226\140\156\207\131 l = Some (s, v)\226\140\157
           \226\136\151 gen_heap_ctx (<[l:=(force_read_lock s, v)]> \207\131)
             \226\136\151 mapsto l q (ReadLocked (S n)) v.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
iDestruct (own_valid_2 with "H\207\131 Hl") as %
 [Hl%gen_heap_singleton_included _]%auth_both_valid.
Time (destruct Hl as (s, (Hl, Hincl))).
Time
iMod
 (own_update_2 _ _ _
    (\226\151\143 to_gen_heap (<[l:=(force_read_lock s, v)]> \207\131)
     \226\139\133 \226\151\175 <[l:=(Count q, (to_lock (ReadLocked (S n)), to_agree v))]> \206\181)
 with "H\207\131 Hl") as "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update, discrete_fun_local_update =>k).
Time rewrite /to_gen_heap /insert /partial_fn_insert //=.
Time (destruct (k == l)).
Time *
Time subst.
Time rewrite Hl.
Time unshelve apply : {}option_local_update {}.
Time unshelve apply : {}prod_local_update_2 {}.
Time (destruct s).
Time **
Time (simpl in Hincl).
Time (apply csum_included in Hincl).
Time
(destruct Hincl as [| [(?, (?, ?))| (?, (?, ?))]]; intuition; try congruence).
Time **
Time (simpl).
Time unshelve apply : {}prod_local_update_1 {}.
Time (apply csum_local_update_l).
Time (apply nat_local_update; lia).
Time **
Time (simpl).
Time unshelve apply : {}prod_local_update_1 {}.
Time (apply csum_local_update_l).
Time (apply nat_local_update; lia).
Time *
Time reflexivity.
Time }
Time iExists s.
Time by iFrame.
Time Qed.
Time
Lemma gen_heap_readunlock \207\131 l q n v :
  gen_heap_ctx \207\131
  -\226\136\151 mapsto l q (ReadLocked n) v
     ==\226\136\151 \226\136\131 n',
           \226\140\156\207\131 l = Some (ReadLocked n', v)\226\140\157
           \226\136\151 gen_heap_ctx (<[l:=(force_read_unlock (ReadLocked n'), v)]> \207\131)
             \226\136\151 mapsto l q (force_read_unlock (ReadLocked n)) v.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
iDestruct (own_valid_2 with "H\207\131 Hl") as %
 [Hl%gen_heap_singleton_included _]%auth_both_valid.
Time (destruct Hl as (s, (Hl, Hincl))).
Time
iMod
 (own_update_2 _ _ _
    (\226\151\143 to_gen_heap (<[l:=(force_read_unlock s, v)]> \207\131)
     \226\139\133 \226\151\175 <[l:=(Count q,
              (to_lock (force_read_unlock (ReadLocked n)), to_agree v))]> \206\181)
 with "H\207\131 Hl") as "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update, discrete_fun_local_update =>k).
Time rewrite /to_gen_heap /insert /partial_fn_insert //=.
Time (destruct (k == l)).
Time *
Time subst.
Time rewrite Hl.
Time unshelve apply : {}option_local_update {}.
Time unshelve apply : {}prod_local_update_2 {}.
Time (destruct s).
Time **
Time (simpl in Hincl).
Time (apply csum_included in Hincl).
Time
(destruct Hincl as [| [(?, (?, ?))| (?, (?, ?))]]; intuition; try congruence).
Time **
Time (simpl).
Time unshelve apply : {}prod_local_update_1 {}.
Time
(<ssreflect_plugin::ssrtclintros@0> destruct num, n =>//=;
  apply csum_local_update_l; apply nat_local_update; lia).
Time **
Time (simpl).
Time unshelve apply : {}prod_local_update_1 {}.
Time (simpl in Hincl).
Time (apply Cinl_included_nat in Hincl).
Time lia.
Time *
Time reflexivity.
Time }
Time (apply Cinl_included_nat' in Hincl as (m, (?, Heq))).
Time (destruct s; simpl in *; inversion Heq; subst; try lia).
Time (iExists num; by iFrame).
Time Qed.
Time End gen_heap.
