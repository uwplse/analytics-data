Time From iris.algebra Require Import auth agree functions csum.
Time From Armada.CSL Require Import Counting.
Time From iris.base_logic.lib Require Export own.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Require Export Armada.Spec.LockDefs.
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
Time rewrite -Some_op pair_op.
