Time From iris.algebra Require Import auth gmap frac agree namespace_map.
Time From iris.algebra Require Import auth agree functions csum.
Time From iris.algebra Require Import auth gmap agree.
Time From Armada.CSL Require Import Counting.
Time From Armada.CSL Require Import Counting.
Time From iris.base_logic.lib Require Export own.
Time From iris.base_logic.lib Require Export own.
Time From stdpp Require Export namespaces.
Time From iris.base_logic.lib Require Export own.
Time From iris.bi.lib Require Import fractional.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Definition gen_heapUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (prodR countingR (agreeR (leibnizC V))).
Time
Definition to_gen_heap {L} {V} `{Countable L} : gmap L V \226\134\146 gen_heapUR L V :=
  fmap (\206\187 v, (Count 0, to_agree (v : leibnizC V))).
Time Require Export Armada.Spec.LockDefs.
Time Set Default Proof Using "Type".
Time Import uPred.
Time From Classes Require Import EqualDec.
Time
Class gen_heapG (L V : Type) (\206\163 : gFunctors) `{Countable L} :=
 GenHeapG {gen_heap_inG :> inG \206\163 (authR (gen_heapUR L V));
           gen_heap_name : gname}.
Time Arguments gen_heap_name {_} {_} {_} {_} {_} _ : assert.
Time
Class gen_heapPreG (L V : Type) (\206\163 : gFunctors) `{Countable L} :={
 gen_heap_preG_inG :> inG \206\163 (authR (gen_heapUR L V))}.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time
Definition gen_heapUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (prodR fracR (agreeR (leibnizC V))).
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
Time
Definition gen_heap\206\163 (L V : Type) `{Countable L} : gFunctors :=
  #[ GFunctor (authR (gen_heapUR L V))].
Time
Instance subG_gen_heapPreG  {\206\163} {L} {V} `{Countable L}:
 (subG (gen_heap\206\163 L V) \206\163 \226\134\146 gen_heapPreG L V \206\163).
Time Proof.
Time solve_inG.
Time
Definition gen_metaUR (L : Type) `{Countable L} : ucmraT :=
  gmapUR L (agreeR gnameC).
Time
Definition to_gen_heap {L} {V} `{Countable L} : gmap L V \226\134\146 gen_heapUR L V :=
  fmap (\206\187 v, (1%Qp, to_agree (v : leibnizC V))).
Time Definition lockR := csumR natR (agreeR unitC).
Time
Definition to_lock (s : LockStatus) : lockR :=
  match s with
  | Locked => Cinr (to_agree tt)
  | ReadLocked n => Cinl (S n)
  | Unlocked => Cinl O
  end.
Time
Definition to_gen_meta `{Countable L} : gmap L gname \226\134\146 gen_metaUR L :=
  fmap to_agree.
Time
Class gen_heapG (L V : Type) (\206\163 : gFunctors) `{Countable L} :=
 GenHeapG {gen_heap_inG :> inG \206\163 (authR (gen_heapUR L V));
           gen_meta_inG :> inG \206\163 (authR (gen_metaUR L));
           gen_meta_data_inG :> inG \206\163 (namespace_mapR (agreeR positiveC));
           gen_heap_name : gname;
           gen_meta_name : gname}.
Time
Definition gen_heapUR (L V : Type) `{EqualDec L} : ucmraT :=
  ofe_funUR
    (fun a : L =>
     optionUR (prodR countingR (prodR lockR (agreeR (leibnizC V))))).
Time
Definition to_gen_heap {L} {V} `{EqualDec L}
  (f : L \226\134\146 option (LockStatus * V)) : gen_heapUR L V :=
  \206\187 k,
    match f k with
    | None => None
    | Some (s, v) => Some (Count 0, (to_lock s, to_agree (v : leibnizC V)))
    end.
Time Qed.
Time Section definitions.
Time Context `{hG : gen_heapG L V \206\163}.
Time
Definition gen_heap_ctx (\207\131 : gmap L V) : iProp \206\163 :=
  own (gen_heap_name hG) (\226\151\143 to_gen_heap \207\131).
Time
Definition mapsto_def (l : L) (n : Z) (v : V) : iProp \206\163 :=
  own (gen_heap_name hG) (\226\151\175 {[l := (Count n, to_agree (v : leibnizC V))]}).
Time Arguments gen_heap_name {_} {_} {_} {_} {_} _ : assert.
Time Arguments gen_meta_name {_} {_} {_} {_} {_} _ : assert.
Time
Class gen_heapPreG (L V : Type) (\206\163 : gFunctors) `{Countable L} :={
 gen_heap_preG_inG :> inG \206\163 (authR (gen_heapUR L V));
 gen_meta_preG_inG :> inG \206\163 (authR (gen_metaUR L));
 gen_meta_data_preG_inG :> inG \206\163 (namespace_mapR (agreeR positiveC))}.
Time Definition mapsto_aux : seal (@mapsto_def).
Time by eexists.
Time Qed.
Time Definition mapsto := mapsto_aux.(unseal).
Time Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
Time
Definition read_mapsto_def (l : L) (v : V) : iProp \206\163 :=
  own (gen_heap_name hG)
    (\226\151\175 {[l := (Count (- 1), to_agree (v : leibnizC V))]}).
Time Definition read_mapsto_aux : seal (@read_mapsto_def).
Time by eexists.
Time Qed.
Time Definition read_mapsto := read_mapsto_aux.(unseal).
Time
Definition read_mapsto_eq : @read_mapsto = @read_mapsto_def :=
  read_mapsto_aux.(seal_eq).
Time
Definition gen_heap\206\163 (L V : Type) `{Countable L} : gFunctors :=
  #[ GFunctor (authR (gen_heapUR L V)); GFunctor (authR (gen_metaUR L));
  GFunctor (namespace_mapR (agreeR positiveC))].
Time
Instance subG_gen_heapPreG  {\206\163} {L} {V} `{Countable L}:
 (subG (gen_heap\206\163 L V) \206\163 \226\134\146 gen_heapPreG L V \206\163).
Time Proof.
Time solve_inG.
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
Class gen_heapG (L V : Type) (\206\163 : gFunctors) `{EqualDec L} :=
 GenHeapG {gen_heap_inG :> inG \206\163 (authR (@gen_heapUR L V _));
           gen_heap_name : gname}.
Time by case (\207\131 !! l).
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
Time Qed.
Time
Definition mapsto_def (l : L) (q : Qp) (v : V) : iProp \206\163 :=
  own (gen_heap_name hG) (\226\151\175 {[l := (q, to_agree (v : leibnizC V))]}).
Time Definition mapsto_aux : seal (@mapsto_def).
Time by eexists.
Time solve_inG.
Time Qed.
Time Section definitions.
Time Context `{hG : gen_heapG L V \206\163}.
Time Qed.
Time Definition mapsto := mapsto_aux.(unseal).
Time
Definition gen_heap_ctx (\207\131 : L \226\134\146 option (LockStatus * V)) : 
  iProp \206\163 := own (gen_heap_name hG) (\226\151\143 to_gen_heap \207\131).
Time
Lemma lookup_to_gen_heap_None \207\131 l : \207\131 !! l = None \226\134\146 to_gen_heap \207\131 !! l = None.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap lookup_fmap
 =>{+}->.
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
Definition mapsto_def (l : L) (n : Z) (s : LockStatus) 
  (v : V) : iProp \206\163 :=
  own (gen_heap_name hG)
    (\226\151\175 ((fun l' =>
         if l' == l
         then Some (Count (n : Z), (to_lock s, to_agree (v : leibnizC V)))
         else \206\181)
          : gen_heapUR L V)).
Time Qed.
Time
Lemma gen_heap_singleton_included \207\131 l q v :
  {[l := (q, to_agree v)]} \226\137\188 to_gen_heap \207\131 \226\134\146 \207\131 !! l = Some v.
Time
Definition meta_def `{Countable A} (l : L) (N : namespace) 
  (x : A) : iProp \206\163 :=
  (\226\136\131 \206\179m,
     own (gen_meta_name hG) (\226\151\175 {[l := to_agree \206\179m]})
     \226\136\151 own \206\179m (namespace_map_data N (to_agree (encode x))))%I.
Time Definition meta_aux : seal (@meta_def).
Time by eexists.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite singleton_included =>-
 [[q' av] []]).
Time Qed.
Time Definition meta {A} {dA} {cA} := meta_aux.(unseal) A dA cA.
Time Definition meta_eq : @meta = @meta_def := meta_aux.(seal_eq).
Time End definitions.
Time #[local]
Notation "l \226\134\166{ q } v" := (mapsto l q v)
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  v") : bi_scope.
Time Definition mapsto_aux : seal (@mapsto_def).
Time by eexists.
Time #[local]Notation "l \226\134\166 v" := (mapsto l 1 v) (at level 20) : bi_scope.
Time #[local]
Notation "l \226\134\166{ q } -" := (\226\136\131 v, l \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  -") : bi_scope.
Time #[local]Notation "l \226\134\166 -" := (l \226\134\166{1} -)%I (at level 20) : bi_scope.
Time Section to_gen_heap.
Time Context (L V : Type) `{Countable L}.
Time Implicit Type \207\131 : gmap L V.
Time Implicit Type m : gmap L gname.
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
Time Lemma to_gen_heap_valid \207\131 : \226\156\147 to_gen_heap \207\131.
Time Proof.
Time (intros l).
Time rewrite lookup_fmap.
Time by case (\207\131 !! l).
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
Time
Lemma lookup_to_gen_heap_None \207\131 l : \207\131 !! l = None \226\134\146 to_gen_heap \207\131 !! l = None.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap lookup_fmap
 =>{+}->.
Time Qed.
Time Qed.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap lookup_fmap
 fmap_Some_equiv =>- [v' [Hl [/= {+}-> {+}->]]]).
Time
Lemma gen_heap_singleton_included \207\131 l q v :
  {[l := (q, to_agree v)]} \226\137\188 to_gen_heap \207\131 \226\134\146 \207\131 !! l = Some v.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite singleton_included =>-
 [[q' av] []]).
Time Lemma lookup_to_gen_heap_None \207\131 l : \207\131 l = None \226\134\146 to_gen_heap \207\131 l = None.
Time Proof.
Time rewrite /to_gen_heap.
Time by case (\207\131 l).
Time Qed.
Time
Lemma gen_heap_singleton_included \207\131 l q s v :
  ((fun l' =>
    if l' == l then Some (Count q, (to_lock s, to_agree (v : leibnizC V)))
    else \206\181)
     : gen_heapUR L V) \226\137\188 to_gen_heap \207\131
  \226\134\146 \226\136\131 s', \207\131 l = Some (s', v) \226\136\167 to_lock s \226\137\188 to_lock s'.
Time Proof.
Time (intros Hincl).
Time (apply (ofe_fun_included_spec_1 _ _ l) in Hincl).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap lookup_fmap
 fmap_Some_equiv =>- [v' [Hl [/= {+}-> {+}->]]]).
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
Time
move  {}=>/Some_pair_included_total_2 [_]
 /to_agree_included/leibniz_equiv_iff {+}-> //.
Time Qed.
Time
Lemma to_gen_heap_insert l v \207\131 :
  to_gen_heap (<[l:=v]> \207\131) =
  <[l:=(Count 0, to_agree (v : leibnizC V))]> (to_gen_heap \207\131).
Time
move  {}=>/Some_pair_included_total_2 [_]
 /to_agree_included/leibniz_equiv_iff {+}-> //.
Time Proof.
Time by rewrite /to_gen_heap fmap_insert.
Time Qed.
Time
Lemma to_gen_heap_delete l \207\131 :
  to_gen_heap (delete l \207\131) = delete l (to_gen_heap \207\131).
Time Qed.
Time Proof.
Time by rewrite /to_gen_heap fmap_delete.
Time Qed.
Time End to_gen_heap.
Time
Lemma gen_heap_init `{gen_heapPreG L V \206\163} \207\131 :
  (|==> \226\136\131 _ : gen_heapG L V \206\163, gen_heap_ctx \207\131)%I.
Time
Lemma to_gen_heap_insert l v \207\131 :
  to_gen_heap (<[l:=v]> \207\131) =
  <[l:=(1%Qp, to_agree (v : leibnizC V))]> (to_gen_heap \207\131).
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131)) as ( \206\179 ) "Hh".
Time Proof.
Time by rewrite /to_gen_heap fmap_insert.
Time {
Time rewrite auth_auth_valid.
Time Qed.
Time Lemma to_gen_meta_valid m : \226\156\147 to_gen_meta m.
Time Proof.
Time (intros l).
Time rewrite lookup_fmap.
Time exact : {}to_gen_heap_valid {}.
Time }
Time iModIntro.
Time by iExists (GenHeapG L V \206\163 _ _ _ \206\179).
Time by case (m !! l).
Time Qed.
Time
Lemma lookup_to_gen_meta_None m l : m !! l = None \226\134\146 to_gen_meta m !! l = None.
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_meta lookup_fmap
 =>{+}->.
Time Qed.
Time Qed.
Time
Lemma to_gen_meta_insert l m \206\179m :
  to_gen_meta (<[l:=\206\179m]> m) = <[l:=to_agree \206\179m]> (to_gen_meta m).
Time Proof.
Time by rewrite /to_gen_meta fmap_insert.
Time
Lemma gen_heap_strong_init `{H : gen_heapPreG L V \206\163} 
  \207\131s :
  (|==> \226\136\131 (H0 : gen_heapG L V \206\163) (Hpf : @gen_heap_inG _ _ _ _ _ H0 =
                                        gen_heap_preG_inG),
          gen_heap_ctx \207\131s \226\136\151 own (gen_heap_name H0) (\226\151\175 to_gen_heap \207\131s))%I.
Time -
Time rewrite option_included.
Time Qed.
Time End to_gen_heap.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131s \226\139\133 \226\151\175 to_gen_heap \207\131s)) as ( \206\179 ) "(?&?)".
Time
Lemma gen_heap_init `{Countable L} `{!gen_heapPreG L V \206\163} 
  \207\131 : (|==> \226\136\131 _ : gen_heapG L V \206\163, gen_heap_ctx \207\131)%I.
Time {
Time (apply auth_both_valid; split; auto).
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131)) as ( \206\179h ) "Hh".
Time (intros [?| Hcase]).
Time *
Time congruence.
Time *
Time (repeat destruct Hcase as [? Hcase]).
Time congruence.
Time exact : {}to_gen_heap_valid {}.
Time }
Time iModIntro.
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_heap_valid {}.
Time }
Time iMod (own_alloc (\226\151\143 to_gen_meta \226\136\133)) as ( \206\179m ) "Hm".
Time Qed.
Time (unshelve iExists (GenHeapG L V \206\163 _ _ _ \206\179) , _; auto).
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_meta_valid {}.
Time }
Time iModIntro.
Time iExists (GenHeapG L V \206\163 _ _ _ _ _ \206\179h \206\179m).
Time (iExists \226\136\133; simpl).
Time iFrame "Hh Hm".
Time iFrame.
Time Lemma to_lock_inj s s' : to_lock s \226\137\161 to_lock s' \226\134\146 s = s'.
Time (destruct s, s'; inversion 1; auto; congruence).
Time Qed.
Time by rewrite dom_empty_L.
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
Time Qed.
Time Qed.
Time (apply _).
Time
Lemma gen_heap_singleton_full_included \207\131 l s v :
  ((fun l' =>
    if l' == l then Some (Count 0, (to_lock s, to_agree (v : leibnizC V)))
    else \206\181)
     : gen_heapUR L V) \226\137\188 to_gen_heap \207\131 \226\134\146 \207\131 l = Some (s, v).
Time Qed.
Time #[global]Instance read_mapsto_timeless  l v: (Timeless (l r\226\134\166 v)).
Time Proof.
Time rewrite read_mapsto_eq /read_mapsto_def.
Time (apply _).
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
Time Proof.
Time (intros Hincl).
Time (apply (ofe_fun_included_spec_1 _ _ l) in Hincl).
Time Qed.
Time
Lemma gen_heap_init_to_bigOp \207\131 :
  own (gen_heap_name hG) (\226\151\175 to_gen_heap \207\131) -\226\136\151 [\226\136\151 map] i\226\134\166v \226\136\136 \207\131, i \226\134\166 v.
Time move : {}Hincl {}.
Time Proof.
Time (induction \207\131 using map_ind).
Time -
Time iIntros.
Time rewrite /to_gen_heap.
Time (<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  congruence).
Time Qed.
Time #[global]
Instance mapsto_fractional  l v: (Fractional (\206\187 q, l \226\134\166{q} v)%I).
Time Proof.
Time (intros p q).
Time
by rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op op_singleton pair_op
 agree_idemp.
Time (destruct (\207\131 l) as [(s', v')| ]).
Time -
Time move /Some_included_exclusive {}=>Hequiv.
Time (feed pose proof Hequiv as Hequiv'; clear Hequiv).
Time {
Time (repeat <ssreflect_plugin::ssrtclintros@0> econstructor =>//=).
Time rewrite //=.
Time -
Time iIntros "Hown".
Time rewrite big_opM_insert //.
Time (destruct s'; econstructor).
Time }
Time (destruct Hequiv' as [? [Heq1 Heq2]]).
Time
(move /to_lock_inj {} in  {} Heq1; move /to_agree_inj/leibniz_equiv_iff {}
  in  {} Heq2; subst; auto).
Time -
Time rewrite option_included.
Time
iAssert (own (gen_heap_name hG) (\226\151\175 to_gen_heap m) \226\136\151 i \226\134\166 x)%I with "[Hown]" as
 "[Hrest $]".
Time (intros [?| Hcase]).
Time *
Time congruence.
Time *
Time (repeat destruct Hcase as [? Hcase]).
Time congruence.
Time Qed.
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite to_gen_heap_insert
 insert_singleton_op ; last  by apply lookup_to_gen_heap_None).
Time rewrite auth_frag_op.
Time
Lemma to_gen_heap_insert l s v \207\131 :
  to_gen_heap (<[l:=(s, v)]> \207\131)
  \226\137\161 <[l:=(Count 0, (to_lock s, to_agree (v : leibnizC V)))]> (to_gen_heap \207\131).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>k //=).
Time iDestruct "Hown" as "(?&?)".
Time iFrame.
Time }
Time by iApply IH\207\131.
Time rewrite /insert /partial_fn_insert.
Time Qed.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (k == l) =>//=).
Time
Lemma mapsto_agree l q1 q2 v1 v2 : l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time Qed.
Time
Lemma to_gen_heap_delete l \207\131 :
  to_gen_heap (delete l \207\131) \226\137\161 delete l (to_gen_heap \207\131).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>k //=).
Time rewrite /delete /partial_fn_delete.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (k == l) =>//=).
Time Qed.
Time Qed.
Time End to_gen_heap.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite op_singleton singleton_valid pair_op.
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
Time
Lemma gen_heap_init `{gen_heapPreG L V \206\163} \207\131 :
  (|==> \226\136\131 _ : gen_heapG L V \206\163, gen_heap_ctx \207\131)%I.
Time (apply wand_intro_r).
Time
rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op own_valid discrete_valid.
Time by intros [_ ?%agree_op_invL'].
Time Qed.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_heap \207\131)) as ( \206\179 ) "Hh".
Time {
Time rewrite auth_auth_valid.
Time exact : {}to_gen_heap_valid {}.
Time }
Time iModIntro.
Time
Lemma mapsto_valid l q1 q2 v1 v2 :
  q1 >= 0 \226\134\146 q2 >= 0 \226\134\146 l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 False.
Time Proof.
Time (intros).
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
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
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite auth_frag_valid op_singleton singleton_valid pair_op.
Time }
Time iModIntro.
Time (unshelve iExists (GenHeapG L V \206\163 _ _ \206\179) , _; auto).
Time rewrite op_singleton singleton_valid pair_op.
Time by intros [_ ?%agree_op_invL'].
Time Qed.
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time iFrame.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time lia.
Time Qed.
Time
Lemma mapsto_combine l q1 q2 v1 v2 :
  l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 l \226\134\166{q1 + q2} v1 \226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time iIntros "Hl1 Hl2".
Time iDestruct (mapsto_agree with "Hl1 Hl2") as % ->.
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
Time Qed.
Time (apply _).
Time iCombine "Hl1 Hl2" as "Hl".
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
Time eauto with iFrame.
Time
Lemma read_split_join l (q : nat) v : l \226\134\166{q} v \226\138\163\226\138\162 l \226\134\166{S q} v \226\136\151 l \226\134\166{- 1} v.
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
Time Proof.
Time (induction \207\131 using map_ind).
Time -
Time iIntros.
Time Qed.
Time rewrite //=.
Time -
Time iIntros ( Hunlocked ) "Hown".
Time #[global]
Instance ex_mapsto_fractional  l: (Fractional (\206\187 q, l \226\134\166{q} -)%I).
Time rewrite big_opM_insert //.
Time Proof.
Time (intros p q).
Time iSplit.
Time -
Time iDestruct 1 as ( v ) "[H1 H2]".
Time rewrite op_singleton pair_op.
Time (iSplitL "H1"; eauto).
Time rewrite counting_op' //=.
Time
iAssert (own (gen_heap_name hG) (\226\151\175 to_gen_heap (\206\187 s, m !! s)) \226\136\151 i \226\134\166 snd x)%I
 with "[Hown]" as "[Hrest $]".
Time -
Time iIntros "[H1 H2]".
Time iDestruct "H1" as ( v1 ) "H1".
Time iDestruct "H2" as ( v2 ) "H2".
Time iDestruct (mapsto_agree with "H1 H2") as % ->.
Time {
Time rewrite mapsto_eq /mapsto_def //.
Time
iAssert (own (gen_heap_name hG) (\226\151\175 to_gen_heap (<[i:=x]> (\206\187 s : L, m !! s))))
 with "[Hown]" as "Hown'".
Time iExists v2.
Time by iFrame.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time Qed.
Time {
Time iApply (own_proper with "Hown").
Time f_equiv.
Time (intros k).
Time rewrite /to_gen_heap /insert /partial_fn_insert //=.
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
Time (destruct (equal)).
Time *
Time subst.
Time rewrite lookup_insert //=.
Time *
Time rewrite lookup_insert_ne //=.
Time lia.
Time }
Time (assert (Heq_unlocked : fst x = Unlocked)).
Time {
Time (eapply (Hunlocked i)).
Time by rewrite lookup_insert.
Time }
Time (destruct x as (l, v)).
Time rewrite to_gen_heap_insert.
Time replace (S q + - 1)%Z with q : Z by lia.
Time
by <ssreflect_plugin::ssrtclintros@0> apply pure_mono =>/singleton_valid
 [? ?].
Time Qed.
Time by rewrite agree_idemp.
Time rewrite -own_op.
Time
Lemma mapsto_valid_2 l q1 q2 v1 v2 :
  l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 \226\156\147 (q1 + q2)%Qp.
Time Proof.
Time iIntros "H1 H2".
Time iDestruct (mapsto_agree with "H1 H2") as % ->.
Time iApply (mapsto_valid l _ v2).
Time by iFrame.
Time iApply (own_proper with "Hown'").
Time Qed.
Time #[global]Instance meta_token_timeless  l N: (Timeless (meta_token l N)).
Time Proof.
Time rewrite meta_token_eq /meta_token_def.
Time (apply _).
Time rewrite -auth_frag_op.
Time f_equiv.
Time (intros k).
Time rewrite ofe_fun_lookup_op.
Time Qed.
Time rewrite /insert /partial_fn_insert //=.
Time #[global]
Instance meta_timeless  `{Countable A} l N (x : A): (Timeless (meta l N x)).
Time Proof.
Time rewrite meta_eq /meta_def.
Time (apply _).
Time Qed.
Time (destruct (k == i)).
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
Time -
Time subst.
Time rewrite lookup_to_gen_heap_None //.
Time rewrite namespace_map_token_union //.
Time rewrite left_id.
Time iDestruct "Hm" as "[Hm1 Hm2]".
Time (iSplitL "Hm1"; eauto).
Time (simpl in Heq_unlocked).
Time by rewrite Heq_unlocked.
Time -
Time by rewrite right_id.
Time Qed.
Time
Lemma gen_heap_alloc \207\131 l v :
  \207\131 !! l = None \226\134\146 gen_heap_ctx \207\131 ==\226\136\151 gen_heap_ctx (<[l:=v]> \207\131) \226\136\151 l \226\134\166 v.
Time Proof.
Time iIntros ( ? ) "H\207\131".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time }
Time iApply IH\207\131.
Time Qed.
Time iMod (own_update with "H\207\131") as "[H\207\131 Hl]".
Time *
Time (intros).
Time (eapply (Hunlocked s)).
Time (rewrite lookup_insert_ne; eauto).
Time (intros Heq).
Time congruence.
Time *
Time eauto.
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update_alloc,
  (alloc_singleton_local_update _ _ (Count 0, to_agree (v : leibnizC _)))
 =>//).
Time Qed.
Time
Lemma meta_token_union_2 l E1 E2 :
  meta_token l E1 -\226\136\151 meta_token l E2 -\226\136\151 meta_token l (E1 \226\136\170 E2).
Time Proof.
Time rewrite meta_token_eq /meta_token_def.
Time iDestruct 1 as ( \206\179m1 ) "[#H\206\179m1 Hm1]".
Time by apply lookup_to_gen_heap_None.
Time }
Time iModIntro.
Time rewrite to_gen_heap_insert.
Time iFrame.
Time iDestruct 1 as ( \206\179m2 ) "[#H\206\179m2 Hm2]".
Time Qed.
Time iAssert \226\140\156\206\179m1 = \206\179m2\226\140\157%I as % ->.
Time {
Time (iDestruct (own_valid_2 with "H\206\179m1 H\206\179m2") as % H\206\179; iPureIntro).
Time move : {}H\206\179 {}.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite -auth_frag_op op_singleton
 =>/auth_frag_valid /=).
Time
Lemma gen_heap_dealloc \207\131 l v :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166 v ==\226\136\151 gen_heap_ctx (delete l \207\131).
Time rewrite singleton_valid.
Time Proof.
Time iIntros "H\207\131 Hl".
Time
Lemma mapsto_agree_generic l (q1 q2 : Z) ls1 ls2 v1 
  v2 : mapsto l q1 ls1 v1 -\226\136\151 mapsto l q2 ls2 v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time apply : {}agree_op_invL' {}.
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time rewrite to_gen_heap_delete.
Time iApply (own_update_2 with "H\207\131 Hl").
Time }
Time
iDestruct (own_valid_2 with "Hm1 Hm2") as % ?%namespace_map_token_valid_op.
Time (eapply auth_update_dealloc, (delete_singleton_local_update _ _ _)).
Time Qed.
Time iExists \206\179m2.
Time iFrame "H\206\179m2".
Time rewrite namespace_map_token_union //.
Time by iSplitL "Hm1".
Time
Lemma gen_heap_valid \207\131 l q v :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166{q} v -\226\136\151 \226\140\156\207\131 !! l = Some v\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time Qed.
Time
(iDestruct (own_valid_2 with "H\207\131 Hl") as %
  [Hl%gen_heap_singleton_included _]%auth_both_valid; auto).
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time (intros Hval).
Time move : {}(Hval l) {}.
Time rewrite ofe_fun_lookup_op.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time Qed.
Time rewrite -Some_op pair_op.
Time
Lemma meta_token_union l E1 E2 :
  E1 ## E2 \226\134\146 meta_token l (E1 \226\136\170 E2) \226\138\163\226\138\162 meta_token l E1 \226\136\151 meta_token l E2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros; iSplit ; first  by iApply
 meta_token_union_1).
Time by intros [_ [_ ?%agree_op_invL']].
Time iIntros "[Hm1 Hm2]".
Time Qed.
Time by iApply (meta_token_union_2 with "Hm1 Hm2").
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
Lemma mapsto_agree l q1 q2 v1 v2 : l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time
Lemma meta_token_difference l E1 E2 :
  E1 \226\138\134 E2 \226\134\146 meta_token l E2 \226\138\163\226\138\162 meta_token l E1 \226\136\151 meta_token l (E2 \226\136\150 E1).
Time Proof.
Time (intros).
Time rewrite {+1}(union_difference_L E1 E2) //.
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
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite meta_token_union ; last 
 set_solver.
Time Qed.
Time Qed.
Time
Lemma meta_agree `{Countable A} l i (x1 x2 : A) :
  meta l i x1 -\226\136\151 meta l i x2 -\226\136\151 \226\140\156x1 = x2\226\140\157.
Time Proof.
Time rewrite meta_eq /meta_def.
Time
(iDestruct 1 as ( \206\179m1 ) "[H\206\179m1 Hm1]"; iDestruct 1 as ( \206\179m2 ) "[H\206\179m2 Hm2]").
Time iAssert \226\140\156\206\179m1 = \206\179m2\226\140\157%I as % ->.
Time
Lemma gen_heap_update \207\131 l v1 v2 :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166 v1 ==\226\136\151 gen_heap_ctx (<[l:=v2]> \207\131) \226\136\151 l \226\134\166 v2.
Time Proof.
Time iIntros "H\207\131 Hl".
Time {
Time (iDestruct (own_valid_2 with "H\206\179m1 H\206\179m2") as % H\206\179; iPureIntro).
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time
iDestruct (own_valid_2 with "H\207\131 Hl") as %
 [Hl%gen_heap_singleton_included _]%auth_both_valid.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time (intros Hval).
Time move : {}(Hval l) {}.
Time rewrite ofe_fun_lookup_op.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time move : {}H\206\179 {}.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite -auth_frag_op op_singleton
 =>/auth_frag_valid /=).
Time rewrite singleton_valid.
Time apply : {}agree_op_invL' {}.
Time }
Time (iDestruct (own_valid_2 with "Hm1 Hm2") as % H\206\179; iPureIntro).
Time iMod (own_update_2 with "H\207\131 Hl") as "[H\207\131 Hl]".
Time rewrite -Some_op pair_op.
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time move : {}H\206\179 {}.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time rewrite -namespace_map_data_op namespace_map_data_valid.
Time move  {}=>/agree_op_invL'.
Time naive_solver.
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update, singleton_local_update,
  (exclusive_local_update _ (Count 0, to_agree (v2 : leibnizC _))) =>//).
Time Qed.
Time lia.
Time by rewrite /to_gen_heap lookup_fmap Hl.
Time Qed.
Time }
Time iModIntro.
Time rewrite to_gen_heap_insert.
Time iFrame.
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
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time End gen_heap.
Time (intros Hval).
Time move : {}(Hval l) {}.
Time rewrite ofe_fun_lookup_op.
Time iMod (own_update with "H\207\131") as "[H\207\131 Hl]".
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update_alloc,
  (alloc_singleton_local_update _ _ (1%Qp, to_agree (v : leibnizC _))) =>//).
Time by apply lookup_to_gen_heap_None.
Time }
Time iMod (own_alloc (namespace_map_token \226\138\164)) as ( \206\179m ) "H\206\179m".
Time rewrite -Some_op pair_op.
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time Qed.
Time {
Time (apply namespace_map_token_valid).
Time }
Time iMod (own_update with "Hm") as "[Hm Hlm]".
Time
Lemma read_split_join1 l (q : nat) n v :
  mapsto l q (ReadLocked n) v
  \226\138\163\226\138\162 mapsto l (S q) Unlocked v \226\136\151 mapsto l (- 1) (ReadLocked n) v.
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time {
Time (eapply auth_update_alloc).
Time rewrite -own_op -auth_frag_op.
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply (alloc_singleton_local_update _ l (to_agree \206\179m)) =>//).
Time (apply lookup_to_gen_meta_None).
Time move : {}H\207\131l {}.
Time rewrite -!(not_elem_of_dom (D:=gset L)).
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> split =>//= l').
Time set_solver.
Time rewrite ofe_fun_lookup_op.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
Time }
Time iModIntro.
Time iFrame "Hl".
Time
(<ssreflect_plugin::ssrtclseq@0> iSplitL "H\207\131 Hm" ; last  by eauto
 with iFrame).
Time rewrite -Some_op ?pair_op.
Time rewrite counting_op' //= Cinl_op.
Time iExists (<[l:=\206\179m]> m).
Time rewrite to_gen_heap_insert to_gen_meta_insert !dom_insert_L.
Time replace (S q + - 1)%Z with q : Z by lia.
Time iFrame.
Time (assert (Hop : 0 \226\139\133 S n = S n) by auto).
Time replace (S q + - 1)%Z with q : Z by lia.
Time (repeat destruct (decide); try lia).
Time iPureIntro.
Time set_solver.
Time rewrite Hop.
Time Qed.
Time rewrite agree_idemp //=.
Time Qed.
Time
Lemma read_split_join2 l (q : nat) n v :
  mapsto l q (ReadLocked n) v
  \226\138\163\226\138\162 mapsto l (S q) (ReadLocked n) v \226\136\151 mapsto l (- 1) Unlocked v.
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
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
Time f_equiv.
Time auto.
Time (<ssreflect_plugin::ssrtclintros@0> split =>//= l').
Time rewrite ofe_fun_lookup_op.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iMod (IH with "H\207\131") as "[H\207\131'\207\131 H\207\131']" ; first 
 by eapply map_disjoint_insert_l).
Time rewrite -Some_op ?pair_op.
Time rewrite counting_op' //= Cinl_op.
Time decompose_map_disjoint.
Time rewrite !big_opM_insert // -insert_union_l //.
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
Time
by <ssreflect_plugin::ssrtclseq@0> iMod (gen_heap_alloc with "H\207\131'\207\131") as
 "($ & $ & $)" ; first  by apply lookup_union_None.
Time rewrite ofe_fun_lookup_op.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
Time Qed.
Time rewrite -Some_op ?pair_op.
Time rewrite counting_op' //= Cinr_op.
Time
Lemma gen_heap_valid \207\131 l q v :
  gen_heap_ctx \207\131 -\226\136\151 l \226\134\166{q} v -\226\136\151 \226\140\156\207\131 !! l = Some v\226\140\157.
Time Proof.
Time iDestruct 1 as ( m H\207\131m ) "[H\207\131 _]".
Time iIntros "Hl".
Time rewrite /gen_heap_ctx mapsto_eq /mapsto_def.
Time replace (S q + - 1)%Z with q : Z by lia.
Time
(iDestruct (own_valid_2 with "H\207\131 Hl") as %
  [Hl%gen_heap_singleton_included _]%auth_both_valid; auto).
Time (repeat destruct (decide); try lia).
Time rewrite ?agree_idemp //=.
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
Time Qed.
Time iMod (own_update_2 with "H\207\131 Hl") as "[H\207\131 Hl]".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 eapply auth_update, singleton_local_update,
  (exclusive_local_update _ (1%Qp, to_agree (v2 : leibnizC _))) =>//).
Time Lemma read_split_join l (q : nat) v : l \226\134\166{q} v \226\138\163\226\138\162 l \226\134\166{S q} v \226\136\151 l r\226\134\166 v.
Time Proof.
Time rewrite /read_mapsto mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
Time by rewrite /to_gen_heap lookup_fmap Hl.
Time }
Time iModIntro.
Time iFrame "Hl".
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> split =>//= l').
Time iExists m.
Time rewrite to_gen_heap_insert.
Time iFrame.
Time rewrite ofe_fun_lookup_op.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
Time iPureIntro.
Time (apply (elem_of_dom_2 (D:=gset L)) in Hl).
Time rewrite dom_insert_L.
Time set_solver.
Time rewrite -Some_op ?pair_op.
Time rewrite counting_op' //= Cinl_op.
Time Qed.
Time replace (S q + - 1)%Z with q : Z by lia.
Time (repeat destruct (decide); try lia).
Time rewrite agree_idemp //=.
Time End gen_heap.
Time Qed.
Time
Lemma ofe_fun_local_update `{EqualDec A} {B : A \226\134\146 ucmraT} 
  f1 f2 f1' f2' :
  (\226\136\128 x, (f1 x, f2 x) ~l~> (f1' x, f2' x))
  \226\134\146 (f1 : ofe_fun B, f2) ~l~> (f1', f2').
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
Time rewrite ofe_fun_lookup_op in  {} Hm.
Time (edestruct (Hupd n (Some (mf k))); eauto).
Time -
Time (intros k).
Time specialize (Hupd k).
Time specialize (Hm k).
Time rewrite ofe_fun_lookup_op in  {} Hm.
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
Time (<ssreflect_plugin::ssrtclintros@0> apply ofe_fun_local_update =>k).
Time rewrite /to_gen_heap.
Time rewrite /insert /partial_fn_insert.
Time (destruct (k == l)).
Time *
Time subst.
Time rewrite /insert /partial_fn_insert.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time rewrite Hnone.
Time rewrite ofe_fun_lookup_empty.
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply
  (alloc_option_local_update
     (Count 0, (to_lock Unlocked, to_agree (v : leibnizC _)))) =>//).
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
Time (<ssreflect_plugin::ssrtclintros@0> apply ofe_fun_local_update =>k).
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
(<ssreflect_plugin::ssrtclintros@0> eapply auth_update, ofe_fun_local_update
 =>k).
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
(<ssreflect_plugin::ssrtclintros@0> eapply auth_update, ofe_fun_local_update
 =>k).
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
(<ssreflect_plugin::ssrtclintros@0> eapply auth_update, ofe_fun_local_update
 =>k).
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
(<ssreflect_plugin::ssrtclintros@0> eapply auth_update, ofe_fun_local_update
 =>k).
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
