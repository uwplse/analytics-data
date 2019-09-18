Time From iris.algebra Require Import auth gmap frac agree namespace_map.
Time From stdpp Require Export namespaces.
Time From iris.base_logic.lib Require Export own.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Definition gen_heapUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (prodR fracR (agreeR (leibnizO V))).
Time
Definition gen_metaUR (L : Type) `{Countable L} : ucmraT :=
  gmapUR L (agreeR gnameO).
Time
Definition to_gen_heap {L} {V} `{Countable L} : gmap L V \226\134\146 gen_heapUR L V :=
  fmap (\206\187 v, (1%Qp, to_agree (v : leibnizO V))).
Time
Definition to_gen_meta `{Countable L} : gmap L gname \226\134\146 gen_metaUR L :=
  fmap to_agree.
Time
Class gen_heapG (L V : Type) (\206\163 : gFunctors) `{Countable L} :=
 GenHeapG {gen_heap_inG :> inG \206\163 (authR (gen_heapUR L V));
           gen_meta_inG :> inG \206\163 (authR (gen_metaUR L));
           gen_meta_data_inG :> inG \206\163 (namespace_mapR (agreeR positiveO));
           gen_heap_name : gname;
           gen_meta_name : gname}.
Time Arguments gen_heap_name {_} {_} {_} {_} {_} _ : assert.
Time Arguments gen_meta_name {_} {_} {_} {_} {_} _ : assert.
Time
Class gen_heapPreG (L V : Type) (\206\163 : gFunctors) `{Countable L} :={
 gen_heap_preG_inG :> inG \206\163 (authR (gen_heapUR L V));
 gen_meta_preG_inG :> inG \206\163 (authR (gen_metaUR L));
 gen_meta_data_preG_inG :> inG \206\163 (namespace_mapR (agreeR positiveO))}.
Time
Definition gen_heap\206\163 (L V : Type) `{Countable L} : gFunctors :=
  #[ GFunctor (authR (gen_heapUR L V)); GFunctor (authR (gen_metaUR L));
  GFunctor (namespace_mapR (agreeR positiveO))].
Time
Instance subG_gen_heapPreG  {\206\163} {L} {V} `{Countable L}:
 (subG (gen_heap\206\163 L V) \206\163 \226\134\146 gen_heapPreG L V \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Section definitions.
Time Context `{Countable L} `{hG : !gen_heapG L V \206\163}.
Time
Definition gen_heap_ctx (\207\131 : gmap L V) : iProp \206\163 :=
  (\226\136\131 m,
     \226\140\156dom _ m \226\138\134 dom (gset L) \207\131\226\140\157
     \226\136\167 own (gen_heap_name hG) (\226\151\143 to_gen_heap \207\131)
       \226\136\151 own (gen_meta_name hG) (\226\151\143 to_gen_meta m))%I.
Time
Definition mapsto_def (l : L) (q : Qp) (v : V) : iProp \206\163 :=
  own (gen_heap_name hG) (\226\151\175 {[l := (q, to_agree (v : leibnizO V))]}).
Time Definition mapsto_aux : seal (@mapsto_def).
Time by eexists.
Time Qed.
Time Definition mapsto := mapsto_aux.(unseal).
Time Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
Time
Definition meta_token_def (l : L) (E : coPset) : iProp \206\163 :=
  (\226\136\131 \206\179m,
     own (gen_meta_name hG) (\226\151\175 {[l := to_agree \206\179m]})
     \226\136\151 own \206\179m (namespace_map_token E))%I.
Time Definition meta_token_aux : seal (@meta_token_def).
Time by eexists.
Time Qed.
Time Definition meta_token := meta_token_aux.(unseal).
Time
Definition meta_token_eq : @meta_token = @meta_token_def :=
  meta_token_aux.(seal_eq).
Time
Definition meta_def `{Countable A} (l : L) (N : namespace) 
  (x : A) : iProp \206\163 :=
  (\226\136\131 \206\179m,
     own (gen_meta_name hG) (\226\151\175 {[l := to_agree \206\179m]})
     \226\136\151 own \206\179m (namespace_map_data N (to_agree (encode x))))%I.
Time Definition meta_aux : seal (@meta_def).
Time by eexists.
Time Qed.
Time Definition meta {A} {dA} {cA} := meta_aux.(unseal) A dA cA.
Time Definition meta_eq : @meta = @meta_def := meta_aux.(seal_eq).
Time End definitions.
Time #[local]
Notation "l \226\134\166{ q } v" := (mapsto l q v)
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  v") : bi_scope.
Time #[local]Notation "l \226\134\166 v" := (mapsto l 1 v) (at level 20) : bi_scope.
Time #[local]
Notation "l \226\134\166{ q } -" := (\226\136\131 v, l \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  -") : bi_scope.
Time #[local]Notation "l \226\134\166 -" := (l \226\134\166{1} -)%I (at level 20) : bi_scope.
Time Section to_gen_heap.
Time Context (L V : Type) `{Countable L}.
Time Implicit Type \207\131 : gmap L V.
Time Implicit Type m : gmap L gname.
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
  <[l:=(1%Qp, to_agree (v : leibnizO V))]> (to_gen_heap \207\131).
Time Proof.
Time by rewrite /to_gen_heap fmap_insert.
Time Qed.
Time Lemma to_gen_meta_valid m : \226\156\147 to_gen_meta m.
Time Proof.
Time (intros l).
Time rewrite lookup_fmap.
Time by case (m !! l).
Time Qed.
Time
Lemma lookup_to_gen_meta_None m l : m !! l = None \226\134\146 to_gen_meta m !! l = None.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_meta lookup_fmap
 =>{+}->.
Time Qed.
Time
Lemma to_gen_meta_insert l m \206\179m :
  to_gen_meta (<[l:=\206\179m]> m) = <[l:=to_agree \206\179m]> (to_gen_meta m).
Time Proof.
Time by rewrite /to_gen_meta fmap_insert.
Time Qed.
Time End to_gen_heap.
Time
Lemma gen_heap_init `{Countable L} `{!gen_heapPreG L V \206\163} 
  \207\131 : (|==> \226\136\131 _ : gen_heapG L V \206\163, gen_heap_ctx \207\131)%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131)) as ( \206\179h ) "Hh".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_heap_valid {}.
Time }
Time iMod (own_alloc (\226\151\143 to_gen_meta \226\136\133)) as ( \206\179m ) "Hm".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_meta_valid {}.
Time }
Time iModIntro.
Time iExists (GenHeapG L V \206\163 _ _ _ _ _ \206\179h \206\179m).
Time (iExists \226\136\133; simpl).
Time iFrame "Hh Hm".
Time by rewrite dom_empty_L.
Time Qed.
Time Section gen_heap.
Time Context {L} {V} `{Countable L} `{!gen_heapG L V \206\163}.
Time Implicit Types P Q : iProp \206\163.
Time Implicit Type \206\166 : V \226\134\146 iProp \206\163.
Time Implicit Type \207\131 : gmap L V.
Time Implicit Type m : gmap L gname.
Time Implicit Types h g : gen_heapUR L V.
Time Implicit Type l : L.
Time Implicit Type v : V.
Time #[global]Instance mapsto_timeless  l q v: (Timeless (l \226\134\166{q} v)).
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time (apply _).
Time Qed.
Time #[global]
Instance mapsto_fractional  l v: (Fractional (\206\187 q, l \226\134\166{q} v)%I).
Time Proof.
Time (intros p q).
Time
by rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op op_singleton -pair_op
 agree_idemp.
Time Qed.
Time #[global]
Instance mapsto_as_fractional  l q v:
 (AsFractional (l \226\134\166{q} v) (\206\187 q, l \226\134\166{q} v)%I q).
Time Proof.
Time split.
Time done.
Time (apply _).
Time Qed.
Time
Lemma mapsto_agree l q1 q2 v1 v2 : l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time (apply wand_intro_r).
Time
rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op own_valid discrete_valid.
Time f_equiv.
Time rewrite auth_frag_valid op_singleton singleton_valid -pair_op.
Time by intros [_ ?%agree_op_invL'].
Time Qed.
Time
Lemma mapsto_combine l q1 q2 v1 v2 :
  l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 l \226\134\166{q1 + q2} v1 \226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time iIntros "Hl1 Hl2".
Time iDestruct (mapsto_agree with "Hl1 Hl2") as % ->.
Time iCombine "Hl1 Hl2" as "Hl".
Time eauto with iFrame.
Time Qed.
Time #[global]
Instance ex_mapsto_fractional  l: (Fractional (\206\187 q, l \226\134\166{q} -)%I).
Time Proof.
Time (intros p q).
Time iSplit.
Time -
Time iDestruct 1 as ( v ) "[H1 H2]".
Time (iSplitL "H1"; eauto).
Time -
Time iIntros "[H1 H2]".
Time iDestruct "H1" as ( v1 ) "H1".
Time iDestruct "H2" as ( v2 ) "H2".
Time iDestruct (mapsto_agree with "H1 H2") as % ->.
Time iExists v2.
Time by iFrame.
Time Qed.
Time #[global]
Instance ex_mapsto_as_fractional  l q:
 (AsFractional (l \226\134\166{q} -) (\206\187 q, l \226\134\166{q} -)%I q).
Time Proof.
Time split.
Time done.
Time (apply _).
Time Qed.
Time Lemma mapsto_valid l q v : l \226\134\166{q} v -\226\136\151 \226\156\147 q.
Time Proof.
Time
rewrite mapsto_eq /mapsto_def own_valid !discrete_valid -auth_frag_valid.
Time
by <ssreflect_plugin::ssrtclintros@0> apply pure_mono =>/singleton_valid
 [? ?].
Time Qed.
Time
Lemma mapsto_valid_2 l q1 q2 v1 v2 :
  l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 \226\156\147 (q1 + q2)%Qp.
Time Proof.
Time iIntros "H1 H2".
Time iDestruct (mapsto_agree with "H1 H2") as % ->.
Time iApply (mapsto_valid l _ v2).
Time by iFrame.
Time Qed.
Time #[global]Instance meta_token_timeless  l N: (Timeless (meta_token l N)).
Time Proof.
Time rewrite meta_token_eq /meta_token_def.
Time (apply _).
Time Qed.
Time #[global]
Instance meta_timeless  `{Countable A} l N (x : A): (Timeless (meta l N x)).
Time Proof.
Time rewrite meta_eq /meta_def.
Time (apply _).
Time Qed.
Time #[global]
Instance meta_persistent  `{Countable A} l N (x : A):
 (Persistent (meta l N x)).
Time Proof.
Time rewrite meta_eq /meta_def.
Time (apply _).
Time Qed.
Time
Lemma meta_token_union_1 l E1 E2 :
  E1 ## E2 \226\134\146 meta_token l (E1 \226\136\170 E2) -\226\136\151 meta_token l E1 \226\136\151 meta_token l E2.
Time Proof.
Time rewrite meta_token_eq /meta_token_def.
Time (intros ?).
Time iDestruct 1 as ( \206\179m1 ) "[#H\206\179m Hm]".
Time rewrite namespace_map_token_union //.
Time iDestruct "Hm" as "[Hm1 Hm2]".
Time (iSplitL "Hm1"; eauto).
Time Qed.
Time
Lemma meta_token_union_2 l E1 E2 :
  meta_token l E1 -\226\136\151 meta_token l E2 -\226\136\151 meta_token l (E1 \226\136\170 E2).
Time Proof.
Time rewrite meta_token_eq /meta_token_def.
Time iDestruct 1 as ( \206\179m1 ) "[#H\206\179m1 Hm1]".
Time iDestruct 1 as ( \206\179m2 ) "[#H\206\179m2 Hm2]".
Time iAssert \226\140\156\206\179m1 = \206\179m2\226\140\157%I as % ->.
Time {
Time (iDestruct (own_valid_2 with "H\206\179m1 H\206\179m2") as % H\206\179; iPureIntro).
Time move : {}H\206\179 {}.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite -auth_frag_op op_singleton
 =>/auth_frag_valid /=).
Time rewrite singleton_valid.
Time apply : {}agree_op_invL' {}.
Time }
Time
iDestruct (own_valid_2 with "Hm1 Hm2") as % ?%namespace_map_token_valid_op.
Time iExists \206\179m2.
Time iFrame "H\206\179m2".
Time rewrite namespace_map_token_union //.
Time by iSplitL "Hm1".
Time Qed.
Time
Lemma meta_token_union l E1 E2 :
  E1 ## E2 \226\134\146 meta_token l (E1 \226\136\170 E2) \226\138\163\226\138\162 meta_token l E1 \226\136\151 meta_token l E2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; iSplit ; first  by iApply
 meta_token_union_1).
Time iIntros "[Hm1 Hm2]".
Time by iApply (meta_token_union_2 with "Hm1 Hm2").
Time Qed.
Time
Lemma meta_token_difference l E1 E2 :
  E1 \226\138\134 E2 \226\134\146 meta_token l E2 \226\138\163\226\138\162 meta_token l E1 \226\136\151 meta_token l (E2 \226\136\150 E1).
Time Proof.
Time (intros).
Time rewrite {+1}(union_difference_L E1 E2) //.
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite meta_token_union ; last 
 set_solver.
Time Qed.
Time
Lemma meta_agree `{Countable A} l i (x1 x2 : A) :
  meta l i x1 -\226\136\151 meta l i x2 -\226\136\151 \226\140\156x1 = x2\226\140\157.
Time Proof.
Time rewrite meta_eq /meta_def.
Time
(iDestruct 1 as ( \206\179m1 ) "[H\206\179m1 Hm1]"; iDestruct 1 as ( \206\179m2 ) "[H\206\179m2 Hm2]").
Time iAssert \226\140\156\206\179m1 = \206\179m2\226\140\157%I as % ->.
Time {
Time (iDestruct (own_valid_2 with "H\206\179m1 H\206\179m2") as % H\206\179; iPureIntro).
Time move : {}H\206\179 {}.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite -auth_frag_op op_singleton
 =>/auth_frag_valid /=).
Time rewrite singleton_valid.
Time apply : {}agree_op_invL' {}.
Time }
Time (iDestruct (own_valid_2 with "Hm1 Hm2") as % H\206\179; iPureIntro).
Time move : {}H\206\179 {}.
Time rewrite -namespace_map_data_op namespace_map_data_valid.
Time move  {}=>/agree_op_invL'.
Time naive_solver.
Time Qed.
Time
Lemma meta_set `{Countable A} E l (x : A) N :
  \226\134\145N \226\138\134 E \226\134\146 meta_token l E ==\226\136\151 meta l N x.
Time Proof.
Time rewrite meta_token_eq meta_eq /meta_token_def /meta_def.
Time iDestruct 1 as ( \206\179m ) "[H\206\179m Hm]".
Time iExists \206\179m.
Time iFrame "H\206\179m".
Time iApply (own_update with "Hm").
Time by apply namespace_map_alloc_update.
Time Qed.
Time
Lemma gen_heap_alloc \207\131 l v :
  \207\131 !! l = None
  \226\134\146 gen_heap_ctx \207\131 ==\226\136\151 gen_heap_ctx (<[l:=v]> \207\131) \226\136\151 l \226\134\166 v \226\136\151 meta_token l \226\138\164.
Time Proof.
Time iIntros ( H\207\131l ).
Time
rewrite /gen_heap_ctx mapsto_eq /mapsto_def meta_token_eq /meta_token_def /=.
Time iDestruct 1 as ( m H\207\131m ) "[H\207\131 Hm]".
Time iMod (own_update with "H\207\131") as "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update_alloc,
  (alloc_singleton_local_update _ _ (1%Qp, to_agree (v : leibnizO _))) =>//).
Time by apply lookup_to_gen_heap_None.
Time }
Time iMod (own_alloc (namespace_map_token \226\138\164)) as ( \206\179m ) "H\206\179m".
Time {
Time (apply namespace_map_token_valid).
Time }
Time iMod (own_update with "Hm") as "[Hm Hlm]".
Time {
Time (eapply auth_update_alloc).
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply (alloc_singleton_local_update _ l (to_agree \206\179m)) =>//).
Time (apply lookup_to_gen_meta_None).
Time move : {}H\207\131l {}.
Time rewrite -!(not_elem_of_dom (D:=gset L)).
Time set_solver.
Time }
Time iModIntro.
Time iFrame "Hl".
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitL "H\207\131 Hm" ; last  by eauto
 with iFrame).
Time iExists (<[l:=\206\179m]> m).
Time rewrite to_gen_heap_insert to_gen_meta_insert !dom_insert_L.
Time iFrame.
Time iPureIntro.
Time set_solver.
Time Qed.
Time
Lemma gen_heap_alloc_gen \207\131 \207\131' :
  \207\131' ##\226\130\152 \207\131
  \226\134\146 gen_heap_ctx \207\131
    ==\226\136\151 gen_heap_ctx (\207\131' \226\136\170 \207\131)
        \226\136\151 ([\226\136\151 map] l\226\134\166v \226\136\136 \207\131', l \226\134\166 v) \226\136\151 ([\226\136\151 map] l\226\134\166_ \226\136\136 \207\131', meta_token l \226\138\164).
Time Proof.
Time
(revert \207\131; induction \207\131' as [| l v \207\131' Hl IH] using map_ind; iIntros ( \207\131 Hdisj
  ) "H\207\131").
Time {
Time rewrite left_id_L.
Time auto.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (IH with "H\207\131") as "[H\207\131'\207\131 H\207\131']" ; first 
 by eapply map_disjoint_insert_l).
Time decompose_map_disjoint.
Time rewrite !big_opM_insert // -insert_union_l //.
Time
by <ssreflect_plugin::ssrtclseq@0> iMod (gen_heap_alloc with "H\207\131'\207\131") as
 "($ & $ & $)" ; first  by apply lookup_union_None.
Time Qed.
Time
Lemma gen_heap_valid \207\131 l q v :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166{q} v -\226\136\151 \226\140\156\207\131 !! l = Some v\226\140\157.
Time Proof.
Time iDestruct 1 as ( m H\207\131m ) "[H\207\131 _]".
Time iIntros "Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
(iDestruct (own_valid_2 with "H\207\131 Hl") as %
  [Hl%gen_heap_singleton_included _]%auth_both_valid; auto).
Time Qed.
Time
Lemma gen_heap_update \207\131 l v1 v2 :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166 v1 ==\226\136\151 gen_heap_ctx (<[l:=v2]> \207\131) \226\136\151 l \226\134\166 v2.
Time Proof.
Time iDestruct 1 as ( m H\207\131m ) "[H\207\131 Hm]".
Time iIntros "Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
iDestruct (own_valid_2 with "H\207\131 Hl") as %
 [Hl%gen_heap_singleton_included _]%auth_both_valid.
Time iMod (own_update_2 with "H\207\131 Hl") as "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update, singleton_local_update,
  (exclusive_local_update _ (1%Qp, to_agree (v2 : leibnizO _))) =>//).
Time by rewrite /to_gen_heap lookup_fmap Hl.
Time }
Time iModIntro.
Time iFrame "Hl".
Time iExists m.
Time rewrite to_gen_heap_insert.
Time iFrame.
Time iPureIntro.
Time (apply (elem_of_dom_2 (D:=gset L)) in Hl).
Time rewrite dom_insert_L.
Time set_solver.
Time Qed.
Time End gen_heap.
