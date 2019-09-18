Time From iris.algebra Require Import auth gmap agree.
Time From Transitions Require Import Relations.
Time From iris.algebra Require Import auth agree functions csum.
Time From iris.algebra Require Export auth functions csum excl.
Time From Armada.CSL Require Import Counting Count_GHeap.
Time From Armada.CSL Require Import Counting.
Time From iris.base_logic.lib Require Export own.
Time Require Export CSL.WeakestPre CSL.Lifting CSL.Counting.
Time From iris.base_logic.lib Require Export own.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Set Default Proof Using "Type".
Time Import uPred.
Time From iris.bi.lib Require Import fractional.
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
Time From iris.proofmode Require Import tactics.
Time Arguments gen_dir_name {_} {_} {_} {_} {_} {_} {_} {_} _ : assert.
Time
Class gen_dirPreG (L1 L2 V : Type) (\206\163 : gFunctors) 
`{Countable L1} `{Countable L2} :={gen_dir_preG_inG :>
                                    inG \206\163 (authR (gen_dirUR L1 L2 V))}.
Time
Definition gen_dir\206\163 (L1 L2 V : Type) `{Countable L1} 
  `{Countable L2} : gFunctors := #[ GFunctor (authR (gen_dirUR L1 L2 V))].
Time Require Export Armada.Spec.LockDefs.
Time Set Default Proof Using "Type".
Time Import uPred.
Time From Classes Require Import EqualDec.
Time
Instance subG_gen_dirPreG  {\206\163} {L1} {L2} {V} `{Countable L1} 
 `{Countable L2}: (subG (gen_dir\206\163 L1 L2 V) \206\163 \226\134\146 gen_dirPreG L1 L2 V \206\163).
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
Time
Class gen_heapG (L V : Type) (\206\163 : gFunctors) `{EqualDec L} :=
 GenHeapG {gen_heap_inG :> inG \206\163 (authR (@gen_heapUR L V _));
           gen_heap_name : gname}.
Time Arguments gen_heap_name {_} {_} {_} {_} _ : assert.
Time
Class gen_heapPreG (L V : Type) (\206\163 : gFunctors) `{EqualDec L} :={
 gen_heap_preG_inG :> inG \206\163 (authR (gen_heapUR L V))}.
Time (case (m !! l2); done).
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
Time Qed.
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
Time Definition mapsto_aux : seal (@mapsto_def).
Time by eexists.
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_dir lookup_fmap =>{+}->.
Time Qed.
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
Time
Lemma lookup_to_gen_dir_None2 \207\131 \207\131d l1 l2 :
  \207\131 !! l1 = Some \207\131d
  \226\134\146 \207\131d !! l2 = None
    \226\134\146 to_gen_dir \207\131 !! l1 = Some (to_gen_heap \207\131d) /\
      to_gen_heap \207\131d !! l2 = None.
Time From iris.proofmode Require Export tactics.
Time From Armada Require Export Lib.
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
Time
Class tregG \206\163 :=
 TRegG {treg_counter_inG :>
         inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))));
        treg_name : gname}.
Time Arguments treg_name {_}.
Time Section thread_reg.
Time Context `{tr : tregG \206\163}.
Time Definition Registered := own (treg_name tr) (Cinl (Count (- 1)%Z)).
Time Definition AllDone := own (treg_name tr) (Cinr (\226\151\175 Excl' tt)).
Time Lemma AllDone_Register_excl : AllDone -\226\136\151 Registered -\226\136\151 False.
Time Proof.
Time iIntros "Had Hreg".
Time move : {}Hincl {}.
Time rewrite /to_gen_heap.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_dir lookup_fmap
 fmap_Some_equiv =>- [\207\131d [Hl {+}->]]).
Time iDestruct (own_valid_2 with "Had Hreg") as % [].
Time (<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  congruence).
Time Qed.
Time (destruct (\207\131 l) as [(s', v')| ]).
Time -
Time move /Some_pair_included {}=>[_ Hincl].
Time End thread_reg.
Time (apply Some_pair_included in Hincl as [Hincl1 Hincl2]).
Time
(move /Some_included_total/to_agree_included/leibniz_equiv_iff {} in 
  {} Hincl2; subst).
Time
Definition thread_count_interp {\206\163} {tr : tregG \206\163} :=
  \206\187 n,
    match n with
    | 1 =>
        own (treg_name tr) (Cinl (Count 1))
        \226\136\168 own (treg_name tr) (Cinr (\226\151\143 Excl' tt))
    | _ => own (treg_name tr) (Cinl (Count n))
    end%I.
Time (exists s'; split; auto).
Time Module Reg_wp.
Time Section Reg_wp.
Time Context {OpT} {\206\155 : Layer OpT} `{IRIS : irisG OpT \206\155 \206\163}.
Time Context `{!tregG \206\163}.
Time
Lemma fst_lift_puts_inv {A} {B} f (n1 : A) (\207\1311 : B) 
  n2 \207\1312 t :
  fst_lift (puts f) (n1, \207\1311) (Val (n2, \207\1312) t) \226\134\146 n2 = f n1 \226\136\167 \207\1312 = \207\1311 \226\136\167 t = tt.
Time Proof.
Time (intros [Hput ?]).
Time (inversion Hput; subst; auto).
Time (apply Some_included in Hincl1 as [->| ?]; auto).
Time Qed.
Time Context (Interp : OpState \206\155 \226\134\146 iProp \206\163).
Time
Context
 (Hinterp1 : \226\136\128 n \207\131, state_interp (n, \207\131) -\226\136\151 thread_count_interp n \226\136\151 Interp \207\131).
Time
Context
 (Hinterp2 : \226\136\128 n \207\131, thread_count_interp n \226\136\151 Interp \207\131 -\226\136\151 state_interp (n, \207\131)).
Time
Lemma wp_spawn {T} s E (e : proc _ T) \206\166 :
  \226\150\183 Registered
  -\226\136\151 \226\150\183 (Registered -\226\136\151 WP (let! _ <- e; Unregister)%proc @ s; \226\138\164 {{ _, True }})
     -\226\136\151 \226\150\183 (Registered -\226\136\151 \206\166 tt) -\226\136\151 WP Spawn e @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "Hreg He H\206\166".
Time iApply wp_lift_atomic_step.
Time move  {}=>/Some_included_total.
Time eauto using gen_heap_singleton_included.
Time {
Time auto.
Time }
Time iIntros ( (n, \207\131) ) "Hown".
Time
(<ssreflect_plugin::ssrtclintros@0> destruct s' =>//=; apply csum_included;
  intuition eauto).
Time iModIntro.
Time iSplit.
Time Qed.
Time {
Time (destruct s; intuition).
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
Time iPureIntro.
Time (eapply spawn_non_errorable).
Time }
Time iIntros ( e2 (n', \207\1312) ? Hstep ) "!>".
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
Time (destruct Hstep as ([], ((?, ?), (Hput, Hpure)))).
Time Qed.
Time End to_gen_dir.
Time (inversion Hpure).
Time subst.
Time
Lemma gen_dir_init `{gen_dirPreG L1 L2 V \206\163} \207\131 :
  (|==> \226\136\131 _ : gen_dirG L1 L2 V \206\163, gen_dir_ctx \207\131)%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_dir \207\131)) as ( \206\179 ) "Hh".
Time -
Time rewrite option_included.
Time {
Time rewrite auth_auth_valid.
Time (apply fst_lift_puts_inv in Hput as (?, (?, ?)); subst).
Time exact : {}to_gen_dir_valid {}.
Time }
Time iModIntro.
Time by iExists (GenDirG L1 L2 V \206\163 _ _ _ _ _ \206\179).
Time iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".
Time (intros [?| Hcase]).
Time *
Time congruence.
Time Qed.
Time *
Time (repeat destruct Hcase as [? Hcase]).
Time congruence.
Time
Lemma gen_dir_strong_init `{gen_dirPreG L1 L2 V \206\163} 
  \207\131 :
  (|==> \226\136\131 (H0 : gen_dirG L1 L2 V \206\163) (Hpf : @gen_dir_inG _ _ _ _ _ _ _ _ H0 =
                                           gen_dir_preG_inG),
          gen_dir_ctx \207\131 \226\136\151 own (gen_dir_name H0) (\226\151\175 to_gen_dir \207\131))%I.
Time
iAssert (own (treg_name _) (Cinl (Count n)) \226\136\151 Registered)%I with
 "[Hown Hreg]" as "(Hown&Hreg)".
Time Qed.
Time Proof.
Time iMod (own_alloc (\226\151\143 to_gen_dir \207\131 \226\139\133 \226\151\175 to_gen_dir \207\131)) as ( \206\179 ) "(?&?)".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide (n = 1)) as [->| ] ; last 
 first).
Time {
Time (apply auth_both_valid; split; auto).
Time {
Time (destruct n as [| [| n]]; try lia; iFrame).
Time exact : {}to_gen_dir_valid {}.
Time }
Time iModIntro.
Time Lemma to_lock_inj s s' : to_lock s \226\137\161 to_lock s' \226\134\146 s = s'.
Time (destruct s, s'; inversion 1; auto; congruence).
Time (unshelve iExists (GenDirG L1 L2 V \206\163 _ _ _ _ _ \206\179) , _; auto).
Time Qed.
Time iFrame.
Time
Lemma gen_heap_singleton_full_included \207\131 l s v :
  ((fun l' =>
    if l' == l then Some (Count 0, (to_lock s, to_agree (v : leibnizO V)))
    else \206\181)
     : gen_heapUR L V) \226\137\188 to_gen_heap \207\131 \226\134\146 \207\131 l = Some (s, v).
Time Qed.
Time Proof.
Time (intros Hincl).
Time (apply (discrete_fun_included_spec_1 _ _ l) in Hincl).
Time Section gen_dir.
Time Context `{gen_dirG L1 L2 V \206\163}.
Time move : {}Hincl {}.
Time rewrite /to_gen_heap.
Time (<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  congruence).
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
Time (destruct (\207\131 l) as [(s', v')| ]).
Time Qed.
Time #[global]
Instance read_mapsto_timeless  (l1 : L1) (l2 : L2) v: (Timeless (l1/l2 r\226\134\166 v)).
Time Proof.
Time (apply _).
Time Qed.
Time -
Time move /Some_included_exclusive {}=>Hequiv.
Time
Lemma mapsto_agree d f q1 v1 v2 : d/f \226\134\166{q1} v1 -\226\136\151 d/f r\226\134\166 v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time (apply wand_intro_r).
Time rewrite /read_mapsto mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
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
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hown" as "[Hown|Hown]" ; first 
 by iFrame).
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time (intros [?| Hcase]).
Time *
Time congruence.
Time *
Time (repeat destruct Hcase as [? Hcase]).
Time congruence.
Time Qed.
Time }
Time
iAssert (own (treg_name _) (Cinl (Count (S n))) \226\136\151 Registered)%I with "[Hown]"
 as "(Hown&Hreg')".
Time
Lemma to_gen_heap_insert l s v \207\131 :
  to_gen_heap (<[l:=(s, v)]> \207\131)
  \226\137\161 <[l:=(Count 0, (to_lock s, to_agree (v : leibnizO V)))]> (to_gen_heap \207\131).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>k //=).
Time {
Time rewrite -own_op -Cinl_op counting_op' //=.
Time rewrite /insert /partial_fn_insert.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (k == l) =>//=).
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite ?op_singleton ?singleton_valid pair_op.
Time (repeat destruct decide; try lia).
Time Qed.
Time
Lemma to_gen_heap_delete l \207\131 :
  to_gen_heap (delete l \207\131) \226\137\161 delete l (to_gen_heap \207\131).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_heap =>k //=).
Time replace (S n + - 1)%Z with n : Z by lia.
Time rewrite /delete /partial_fn_delete.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (k == l) =>//=).
Time done.
Time }
Time iModIntro.
Time (simpl).
Time iFrame.
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
Time iSplitL "Hown Hrest".
Time {
Time iApply Hinterp2.
Time exact : {}to_gen_heap_valid {}.
Time }
Time iModIntro.
Time (unshelve iExists (GenHeapG L V \206\163 _ _ \206\179) , _; auto).
Time (destruct n; iFrame).
Time iFrame.
Time }
Time iSplitL "Hreg H\206\166".
Time {
Time by iApply "H\206\166".
Time Qed.
Time }
Time rewrite right_id.
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
Time by iApply "He".
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
Time Qed.
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
Time
Lemma wp_unregister s E :
  {{{ \226\150\183 Registered }}} Unregister @ s; E {{{ RET tt; True}}}.
Time (destruct (equal)).
Time Proof.
Time iIntros ( \206\166 ) ">Hreg H\206\166".
Time iApply wp_lift_atomic_step.
Time *
Time subst.
Time rewrite lookup_insert //=.
Time *
Time rewrite lookup_insert_ne //=.
Time {
Time auto.
Time }
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time }
Time (assert (Heq_unlocked : fst x = Unlocked)).
Time {
Time (eapply (Hunlocked i)).
Time by rewrite lookup_insert.
Time {
Time (destruct s; intuition).
Time }
Time (destruct x as (l, v)).
Time rewrite to_gen_heap_insert.
Time iPureIntro.
Time (eapply unregister_non_errorable).
Time }
Time iIntros ( e2 (n', \207\1312) ? Hstep ) "!>".
Time rewrite -own_op.
Time (destruct Hstep as ([], ((?, ?), (Hput, Hpure)))).
Time (inversion Hpure).
Time iApply (own_proper with "Hown'").
Time subst.
Time (apply fst_lift_puts_inv in Hput as (?, (?, ?)); subst).
Time iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".
Time rewrite -auth_frag_op.
Time f_equiv.
Time (intros k).
Time rewrite discrete_fun_lookup_op.
Time
iAssert
 (\226\136\131 n', \226\140\156n = S n'\226\140\157 \226\136\151 own (treg_name _) (Cinl (Count n)) \226\136\151 Registered)%I with
 "[Hown Hreg]" as ( n' Heq ) "(Hown&Hreg)".
Time rewrite /insert /partial_fn_insert //=.
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide (n = 1)) as [->| ] ; last 
 first).
Time {
Time (destruct n as [| [| n]]; try lia).
Time (destruct (k == i)).
Time -
Time subst.
Time rewrite lookup_to_gen_heap_None //.
Time -
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time rewrite left_id.
Time -
Time iExists (S n).
Time (iFrame; eauto).
Time (simpl in Heq_unlocked).
Time by rewrite Heq_unlocked.
Time }
Time iExists O.
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hown" as "[Hown|Hown]" ; first 
 by iFrame).
Time -
Time by rewrite right_id.
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time }
Time iApply IH\207\131.
Time }
Time subst.
Time *
Time (intros).
Time (eapply (Hunlocked s)).
Time (rewrite lookup_insert_ne; eauto).
Time
iAssert (own (treg_name _) (Cinl (Count n')))%I with "[Hown Hreg]" as "Hown".
Time (intros Heq).
Time congruence.
Time {
Time iCombine "Hown Hreg" as "Hown".
Time *
Time eauto.
Time Qed.
Time rewrite -Cinl_op counting_op' //=.
Time (repeat destruct decide; try lia).
Time replace (S n' + - 1)%Z with n' : Z by lia.
Time done.
Time }
Time iModIntro.
Time (simpl).
Time iFrame.
Time
Lemma mapsto_agree_generic l (q1 q2 : Z) ls1 ls2 v1 
  v2 : mapsto l q1 ls1 v1 -\226\136\151 mapsto l q2 ls2 v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time (apply wand_intro_r).
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op own_valid discrete_valid.
Time iSplitL "Hown Hrest".
Time {
Time iApply Hinterp2.
Time (destruct n' as [| [| n']]; iFrame).
Time }
Time rewrite right_id.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time (intros Hval).
Time move : {}(Hval l) {}.
Time rewrite discrete_fun_lookup_op.
Time by iApply "H\206\166".
Time Qed.
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
Time
Lemma wp_wait s E : {{{ \226\150\183 Registered }}} Wait @ s; E {{{ RET tt; AllDone}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hreg H\206\166".
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time iApply wp_lift_atomic_step.
Time (intros Hval).
Time move : {}(Hval l) {}.
Time rewrite discrete_fun_lookup_op.
Time {
Time auto.
Time }
Time iIntros ( (n, \207\131) ) "Hown".
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; intuition).
Time rewrite -Some_op -pair_op.
Time iPureIntro.
Time (eapply wait_non_errorable).
Time }
Time iIntros ( e2 (n', \207\1312) ? Hstep ) "!>".
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time (repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
Time (destruct Hstep as ([], ((?, ?), (Hput, Hpure)))).
Time lia.
Time (inversion Hpure).
Time Qed.
Time subst.
Time (inversion Hput as [Hsuch Heq]).
Time subst.
Time (inversion Hsuch; subst).
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
Time iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".
Time
iAssert (own (treg_name _) (Cinl (Count 1)) \226\136\151 Registered)%I with
 "[Hown Hreg]" as "(Hown&Hreg)".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hown" as "[Hown|Hown]" ; first 
 by iFrame).
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time }
Time subst.
Time
iAssert (own (treg_name _) (Cinl (Count O)))%I with "[Hown Hreg]" as "Hown".
Time {
Time iCombine "Hown Hreg" as "Hown".
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid /=).
Time rewrite -Cinl_op counting_op' //=.
Time (intros Hval).
Time move : {}(Hval l) {}.
Time rewrite discrete_fun_lookup_op.
Time }
Time iMod (own_update with "Hown") as "(Hdone&Hown)".
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (l == l) ; last  by congruence).
Time {
Time rewrite -Some_op -pair_op.
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply cmra_update_exclusive with
   (y := Cinr (\226\151\175 Excl' tt) \226\139\133 Cinr (\226\151\143 Excl' tt)) =>//=).
Time (intros [Hcount ?]).
Time rewrite counting_op' //= in  {} Hcount.
Time Qed.
Time rewrite -Cinr_op comm.
Time
Lemma read_split_join1 l (q : nat) n v :
  mapsto l q (ReadLocked n) v
  \226\138\163\226\138\162 mapsto l (S q) Unlocked v \226\136\151 mapsto l (- 1) (ReadLocked n) v.
Time Proof.
Time rewrite mapsto_eq /mapsto_def.
Time rewrite -own_op -auth_frag_op.
Time (apply auth_both_valid; split; done).
Time }
Time iModIntro.
Time iSplitL "Hown Hrest".
Time f_equiv.
Time (<ssreflect_plugin::ssrtclintros@0> split =>//= l').
Time {
Time (iApply Hinterp2; iFrame).
Time }
Time (simpl).
Time rewrite right_id.
Time rewrite discrete_fun_lookup_op.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (l' == l) =>//=).
Time by iApply "H\206\166".
Time Qed.
Time End Reg_wp.
Time End Reg_wp.
