Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqRxvqnx"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqIk7JQU"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqfZFNgs"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From iris.algebra Require Import auth agree functions csum.
From Armada.CSL Require Import Counting.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Require Export Armada.Spec.LockDefs.
Set Default Proof Using "Type".
Import uPred.
From Classes Require Import EqualDec.
Import EqualDecNotation.
#[global]
Instance partial_fn_insert  (A T : Type) `{EqualDec A}:
 (Insert A T (A \226\134\146 option T)) :=
 (\206\187 (a : A) (t : T) (f : A \226\134\146 option T) (b : A),
    if b == a then Some t else f b).
#[global]
Instance partial_fn_delete  (A T : Type) `{EqualDec A}:
 (Delete A (A \226\134\146 option T)) :=
 (\206\187 (a : A) (f : A \226\134\146 option T) (b : A), if b == a then None else f b).
Definition lockR := csumR natR (agreeR unitO).
Definition to_lock (s : LockStatus) : lockR :=
  match s with
  | Locked => Cinr (to_agree tt)
  | ReadLocked n => Cinl (S n)
  | Unlocked => Cinl O
  end.
Definition gen_heapUR (L V : Type) `{EqualDec L} : ucmraT :=
  discrete_funUR
    (fun a : L =>
     optionUR (prodR countingR (prodR lockR (agreeR (leibnizO V))))).
Definition to_gen_heap {L} {V} `{EqualDec L}
  (f : L \226\134\146 option (LockStatus * V)) : gen_heapUR L V :=
  \206\187 k,
    match f k with
    | None => None
    | Some (s, v) =>
        Some (Count 0, (to_lock s, to_agree (v : leibnizO V)))
    end.
Class gen_heapG (L V : Type) (\206\163 : gFunctors) `{EqualDec L} :=
 GenHeapG {gen_heap_inG :> inG \206\163 (authR (@gen_heapUR L V _));
           gen_heap_name : gname}.
Arguments gen_heap_name {_} {_} {_} {_} _ : assert.
Class gen_heapPreG (L V : Type) (\206\163 : gFunctors) `{EqualDec L} :={
 gen_heap_preG_inG :> inG \206\163 (authR (gen_heapUR L V))}.
Definition gen_heap\206\163 (L V : Type) `{EqualDec L} : gFunctors :=
  #[ GFunctor (authR (gen_heapUR L V))].
Instance subG_gen_heapPreG  {\206\163} {L} {V} `{EqualDec L}:
 (subG (gen_heap\206\163 L V) \206\163 \226\134\146 gen_heapPreG L V \206\163).
Proof.
solve_inG.
Qed.
Section definitions.
Context `{hG : gen_heapG L V \206\163}.
Definition gen_heap_ctx (\207\131 : L \226\134\146 option (LockStatus * V)) :
  iProp \206\163 := own (gen_heap_name hG) (\226\151\143 to_gen_heap \207\131).
Definition mapsto_def (l : L) (n : Z) (s : LockStatus) 
  (v : V) : iProp \206\163 :=
  own (gen_heap_name hG)
    (\226\151\175 ((fun l' =>
         if l' == l
         then Some
                (Count (n : Z),
                (to_lock s, to_agree (v : leibnizO V))) else \206\181)
          : gen_heapUR L V)).
Definition mapsto_aux : seal (@mapsto_def).
by eexists.
Qed.
Definition mapsto := mapsto_aux.(unseal).
Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
Definition read_mapsto l s v := mapsto l (- 1) s v.
End definitions.
#[local]
Notation "l \226\134\166{ q } v" := (mapsto l q Unlocked v)
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  v") : bi_scope.
#[local]
Notation "l \226\134\166 v" := (mapsto l 0 Unlocked v) (at level 20) : bi_scope.
#[local]
Notation "l \226\134\166{ q } -" := (\226\136\131 v, l \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  -") : bi_scope.
#[local]Notation "l \226\134\166 -" := (l \226\134\166{0} -)%I (at level 20) : bi_scope.
#[local]
Notation "l r\226\134\166 v" := (read_mapsto l Unlocked v)
  (at level 20, format "l  r\226\134\166  v") : bi_scope.
#[local]
Notation "l r\226\134\166 -" := (\226\136\131 v, l r\226\134\166 v)%I
  (at level 20, format "l  r\226\134\166 -") : bi_scope.
Section to_gen_heap.
Context (L V : Type) `{EqualDec L}.
Implicit Type \207\131 : L \226\134\146 option (LockStatus * V).
Lemma to_gen_heap_valid \207\131 : \226\156\147 to_gen_heap \207\131.
Proof.
(<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>l).
(destruct (\207\131 l) as [([], ?)| ]; by econstructor; simpl; eauto).
Qed.
Lemma lookup_to_gen_heap_None \207\131 l :
  \207\131 l = None \226\134\146 to_gen_heap \207\131 l = None.
Proof.
rewrite /to_gen_heap.
by case (\207\131 l).
Qed.
Lemma gen_heap_singleton_included \207\131 l q s v :
  ((fun l' =>
    if l' == l
    then Some (Count q, (to_lock s, to_agree (v : leibnizO V)))
    else \206\181)
     : gen_heapUR L V) \226\137\188 to_gen_heap \207\131
  \226\134\146 \226\136\131 s', \207\131 l = Some (s', v) \226\136\167 to_lock s \226\137\188 to_lock s'.
Proof.
(intros Hincl).
(apply (discrete_fun_included_spec_1 _ _ l) in Hincl).
move : {}Hincl {}.
rewrite /to_gen_heap.
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last 
 congruence).
(destruct (\207\131 l) as [(s', v')| ]).
-
move /Some_pair_included {}=>[_ Hincl].
(apply Some_pair_included in Hincl as [Hincl1 Hincl2]).
(move /Some_included_total/to_agree_included/leibniz_equiv_iff {}
  in  {} Hincl2; subst).
(exists s'; split; auto).
(apply Some_included in Hincl1 as [->| ?]; auto).
(<ssreflect_plugin::ssrtclintros@0> destruct s' =>//=;
  apply csum_included; intuition eauto).
-
rewrite option_included.
(intros [?| Hcase]).
*
congruence.
*
(repeat destruct Hcase as [? Hcase]).
congruence.
Qed.
Lemma to_lock_inj s s' : to_lock s \226\137\161 to_lock s' \226\134\146 s = s'.
(destruct s, s'; inversion 1; auto; congruence).
Qed.
Lemma gen_heap_singleton_full_included \207\131 l s 
  v :
  ((fun l' =>
    if l' == l
    then Some (Count 0, (to_lock s, to_agree (v : leibnizO V)))
    else \206\181)
     : gen_heapUR L V) \226\137\188 to_gen_heap \207\131 \226\134\146 \207\131 l = Some (s, v).
Proof.
(intros Hincl).
(apply (discrete_fun_included_spec_1 _ _ l) in Hincl).
move : {}Hincl {}.
rewrite /to_gen_heap.
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last 
 congruence).
(destruct (\207\131 l) as [(s', v')| ]).
-
move /Some_included_exclusive {}=>Hequiv.
(feed pose proof Hequiv as Hequiv'; clear Hequiv).
{
(repeat <ssreflect_plugin::ssrtclintros@0> econstructor =>//=).
(destruct s'; econstructor).
}
(destruct Hequiv' as [? [Heq1 Heq2]]).
(move /to_lock_inj {} in  {} Heq1; move
  /to_agree_inj/leibniz_equiv_iff {} in  {} Heq2; subst; auto).
-
rewrite option_included.
(intros [?| Hcase]).
*
congruence.
*
(repeat destruct Hcase as [? Hcase]).
congruence.
Qed.
Lemma to_gen_heap_insert l s v \207\131 :
  to_gen_heap (<[l:=(s, v)]> \207\131)
  \226\137\161 <[l:=(Count 0, (to_lock s, to_agree (v : leibnizO V)))]>
      (to_gen_heap \207\131).
Proof.
(<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>k //=).
rewrite /insert /partial_fn_insert.
(<ssreflect_plugin::ssrtclintros@0> destruct (k == l) =>//=).
Qed.
Lemma to_gen_heap_delete l \207\131 :
  to_gen_heap (delete l \207\131) \226\137\161 delete l (to_gen_heap \207\131).
Proof.
(<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>k //=).
rewrite /delete /partial_fn_delete.
(<ssreflect_plugin::ssrtclintros@0> destruct (k == l) =>//=).
Qed.
End to_gen_heap.
Lemma gen_heap_init `{gen_heapPreG L V \206\163} \207\131 :
  (|==> \226\136\131 _ : gen_heapG L V \206\163, gen_heap_ctx \207\131)%I.
Proof.
iMod (own_alloc (\226\151\143 to_gen_heap \207\131)) as ( \206\179 ) "Hh".
{
rewrite auth_auth_valid.
exact : {}to_gen_heap_valid {}.
}
iModIntro.
by iExists (GenHeapG L V \206\163 _ _ \206\179).
Qed.
Lemma gen_heap_strong_init `{H : gen_heapPreG L V \206\163} 
  \207\131s :
  (|==> \226\136\131 (H0 : gen_heapG L V \206\163) (Hpf : gen_heap_inG =
                                        gen_heap_preG_inG),
          gen_heap_ctx \207\131s \226\136\151 own (gen_heap_name _) (\226\151\175 to_gen_heap \207\131s))%I.
Proof.
iMod (own_alloc (\226\151\143 to_gen_heap \207\131s \226\139\133 \226\151\175 to_gen_heap \207\131s)) as ( \206\179 )
 "(?&?)".
{
(apply auth_both_valid; split; auto).
exact : {}to_gen_heap_valid {}.
}
iModIntro.
(unshelve iExists (GenHeapG L V \206\163 _ _ \206\179) , _; auto).
iFrame.
Qed.
Section gen_heap.
Context `{hG : gen_heapG L V \206\163}.
Implicit Types P Q : iProp \206\163.
Implicit Type \206\166 : V \226\134\146 iProp \206\163.
Implicit Type \207\131 : L \226\134\146 option (LockStatus * V).
Implicit Types h g : gen_heapUR L V.
Implicit Type l : L.
Implicit Type v : V.
#[global]
Instance mapsto_timeless  l q m v: (Timeless (mapsto l q m v)).
Proof.
rewrite mapsto_eq /mapsto_def.
(apply _).
Qed.
#[global]Instance read_mapsto_timeless  l v: (Timeless (l r\226\134\166 v)).
Proof.
(apply _).
Qed.
Lemma gen_heap_init_to_bigOp `{Countable L}
  (\207\131 : gmap L (LockStatus * V)) :
  (\226\136\128 s x, \207\131 !! s = Some x \226\134\146 fst x = Unlocked)
  \226\134\146 own (gen_heap_name hG) (\226\151\175 to_gen_heap (\206\187 s, \207\131 !! s))
    -\226\136\151 [\226\136\151 map] i\226\134\166x \226\136\136 \207\131, i \226\134\166 snd x.
Proof.
(induction \207\131 using map_ind).
-
iIntros.
rewrite //=.
-
iIntros ( Hunlocked ) "Hown".
rewrite big_opM_insert //.
iAssert
 (own (gen_heap_name hG) (\226\151\175 to_gen_heap (\206\187 s, m !! s)) \226\136\151 i \226\134\166 snd x)%I
 with "[Hown]" as "[Hrest $]".
{
rewrite mapsto_eq /mapsto_def //.
iAssert
 (own (gen_heap_name hG)
    (\226\151\175 to_gen_heap (<[i:=x]> (\206\187 s : L, m !! s)))) with "[Hown]" as
 "Hown'".
{
iApply (own_proper with "Hown").
f_equiv.
(intros k).
rewrite /to_gen_heap /insert /partial_fn_insert //=.
(destruct (equal)).
*
subst.
rewrite lookup_insert //=.
*
rewrite lookup_insert_ne //=.
}
(assert (Heq_unlocked : fst x = Unlocked)).
{
(eapply (Hunlocked i)).
by rewrite lookup_insert.
}
(destruct x as (l, v)).
rewrite to_gen_heap_insert.
rewrite -own_op.
iApply (own_proper with "Hown'").
rewrite -auth_frag_op.
f_equiv.
(intros k).
rewrite discrete_fun_lookup_op.
rewrite /insert /partial_fn_insert //=.
(destruct (k == i)).
-
subst.
rewrite lookup_to_gen_heap_None //.
rewrite left_id.
(simpl in Heq_unlocked).
by rewrite Heq_unlocked.
-
by rewrite right_id.
}
iApply IH\207\131.
*
(intros).
(eapply (Hunlocked s)).
(rewrite lookup_insert_ne; eauto).
(intros Heq).
congruence.
*
eauto.
Qed.
Lemma mapsto_agree_generic l (q1 q2 : Z) ls1 
  ls2 v1 v2 : mapsto l q1 ls1 v1 -\226\136\151 mapsto l q2 ls2 v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Proof.
(apply wand_intro_r).
rewrite mapsto_eq /mapsto_def.
rewrite -own_op -auth_frag_op own_valid discrete_valid.
(<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid
 /=).
(intros Hval).
move : {}(Hval l) {}.
rewrite discrete_fun_lookup_op.
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by
 congruence).
rewrite -Some_op -pair_op.
by intros [_ [_ ?%agree_op_invL']].
Qed.
Lemma mapsto_agree l q1 q2 v1 v2 :
  l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Proof.
(apply mapsto_agree_generic).
Qed.
Lemma mapsto_valid_generic l (q1 q2 : Z) ls1 
  ls2 v1 v2 :
  (q1 >= 0
   \226\134\146 q2 >= 0 \226\134\146 mapsto l q1 ls1 v1 -\226\136\151 mapsto l q2 ls2 v2 -\226\136\151 False)%Z.
Proof.
(intros ? ?).
(apply wand_intro_r).
rewrite mapsto_eq /mapsto_def.
rewrite -own_op -auth_frag_op own_valid discrete_valid.
(<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid
 /=).
(intros Hval).
move : {}(Hval l) {}.
rewrite discrete_fun_lookup_op.
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by
 congruence).
rewrite -Some_op -pair_op.
(intros [Hcount ?]).
rewrite counting_op' //= in  {} Hcount.
(repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
lia.
Qed.
Lemma mapsto_valid l q1 q2 v1 v2 :
  (q1 >= 0 \226\134\146 q2 >= 0 \226\134\146 l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 False)%Z.
Proof.
(intros).
(apply mapsto_valid_generic; eauto).
Qed.
Lemma mapsto_valid' l v1 v2 : l \226\134\166{0} v1 -\226\136\151 l \226\134\166{- 1} v2 -\226\136\151 False.
Proof.
(apply wand_intro_r).
rewrite mapsto_eq /mapsto_def.
rewrite -own_op -auth_frag_op own_valid discrete_valid.
(<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid
 /=).
(intros Hval).
move : {}(Hval l) {}.
rewrite discrete_fun_lookup_op.
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by
 congruence).
rewrite -Some_op -pair_op.
(intros [Hcount ?]).
rewrite counting_op' //= in  {} Hcount.
Qed.
Lemma read_split_join1 l (q : nat) n v :
  mapsto l q (ReadLocked n) v
  \226\138\163\226\138\162 mapsto l (S q) Unlocked v \226\136\151 mapsto l (- 1) (ReadLocked n) v.
Proof.
rewrite mapsto_eq /mapsto_def.
rewrite -own_op -auth_frag_op.
f_equiv.
(<ssreflect_plugin::ssrtclintros@0> split =>//= l').
rewrite discrete_fun_lookup_op.
(<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
rewrite -Some_op -?pair_op.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqxBL7Jr"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqBQnzZu"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
rewrite counting_op' //= Cinl_op.
(* Auto-generated comment: Failed. *)

