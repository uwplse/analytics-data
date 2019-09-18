Time From iris.algebra Require Import auth agree functions csum.
Time From Perennial.CSL Require Import Counting.
Time From iris.base_logic.lib Require Export own.
Time From iris.bi.lib Require Import fractional.
Time From iris.proofmode Require Import tactics.
Time Require Import SemanticsHelpers.
Time From Perennial Require Export Spec.LockDefs.
Time Require Import Count_Heap.
Time Unset Implicit Arguments.
Time Set Default Proof Using "Type".
Time Import uPred.
Time From Classes Require Import EqualDec.
Time Import EqualDecNotation.
Time
Ltac
 inj_pair2 :=
  repeat
   match goal with
   | H:existT ?x ?o1 = existT ?x ?o2
     |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H; subst
   | H:existT ?x _ = existT ?y _ |- _ => inversion H; subst
   end.
Time
Definition gen_typed_heapUR A (L : A \226\134\146 Type) (V : A \226\134\146 Type)
  {Heq : EqualDec (sigT L)} : ucmraT := gen_heapUR (sigT L) (sigT V).
Time
Definition pull_lock {A} {V : A \226\134\146 Type}
  (v : option (sigT (\206\187 A, LockStatus * V A))%type) :=
  match v with
  | Some (existT T (s, x)) => Some (s, existT T x)
  | None => None
  end.
Time
Definition to_gen_typed_heap {A} {L V : A \226\134\146 Type} 
  {Heq : EqualDec (sigT L)} (f : DynMap L (\206\187 T, (LockStatus * V T)%type)) :
  @gen_typed_heapUR A L V _ := to_gen_heap (\206\187 k, pull_lock (dynMap f k)).
Time
Class gen_typed_heapG {A} (L V : A \226\134\146 Type) (\206\163 : gFunctors)
`{Heq : EqualDec (sigT L)} :={gt_inG :> gen_heapG (sigT L) (sigT V) \206\163}.
Time
Definition gen_typed_heap\206\163 {A} (L V : A \226\134\146 Type) `{Heq : EqualDec (sigT L)} :
  gFunctors := gen_heap\206\163 (sigT L) (sigT V).
Time
Instance subG_gen_heapPreG  {\206\163} {A} {L V : A \226\134\146 Type}
 `{Heq : EqualDec (sigT L)}:
 (subG (gen_typed_heap\206\163 L V) \206\163 \226\134\146 gen_heapPreG (sigT L) (sigT V) \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time Section definitions.
Time Context `{hG : gen_typed_heapG A L V \206\163}.
Time
Definition gen_typed_heap_ctx \207\131 : iProp \206\163 :=
  own (gen_heap_name gt_inG) (\226\151\143 to_gen_typed_heap \207\131).
Time
Definition mapsto {T} (l : L T) (n : Z) (s : LockStatus) 
  (v : V T) := mapsto (existT _ l) n s (existT _ v).
Time
Definition read_mapsto {T} (l : L T) (s : LockStatus) 
  (v : V T) : iProp \206\163 := read_mapsto (existT _ l) s (existT _ v).
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
Time Section to_gen_typed_heap.
Time Context {A} (L V : A \226\134\146 Type) `{EqualDec (sigT L)}.
Time Implicit Type \207\131 : DynMap L (\206\187 T, (LockStatus * V T)%type).
Time Lemma to_gen_typed_heap_valid \207\131 : \226\156\147 to_gen_typed_heap \207\131.
Time Proof.
Time (apply to_gen_heap_valid).
Time Qed.
Time
Lemma getDyn_to_gen_typed_heap_None {T} \207\131 (l : L T) :
  getDyn \207\131 l = None \226\134\146 to_gen_typed_heap \207\131 (existT _ l) = None.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /to_gen_typed_heap =>Hget).
Time (apply lookup_to_gen_heap_None).
Time rewrite /pull_lock getDyn_lookup_none2 //=.
Time Qed.
Time
Lemma to_gen_typed_heap_insert {T} (l : L T) s v \207\131 :
  to_gen_typed_heap (updDyn l (s, v) \207\131)
  \226\137\161 <[existT _ l:=(Count 0, (to_lock s, to_agree (existT _ v)))]>
      (to_gen_typed_heap \207\131).
Time Proof.
Time rewrite -to_gen_heap_insert /to_gen_typed_heap /to_gen_heap.
Time (intros k).
Time rewrite /updDyn //=.
Time rewrite /insert /partial_fn_insert.
Time
(destruct (k == existT T l); <ssreflect_plugin::ssrtclintros@0> subst =>//=).
Time Qed.
Time
Lemma to_gen_typed_heap_delete {T} l \207\131 :
  to_gen_typed_heap (deleteDyn l \207\131)
  \226\137\161 delete (existT T l) (to_gen_typed_heap \207\131).
Time Proof.
Time rewrite -to_gen_heap_delete /to_gen_typed_heap /to_gen_heap.
Time (intros k).
Time rewrite /deleteDyn //=.
Time rewrite /delete /partial_fn_delete.
Time (<ssreflect_plugin::ssrtclintros@0> destruct (k == existT T l) =>//=).
Time Qed.
Time End to_gen_typed_heap.
Time
Lemma gen_typed_heap_init {A} {L V : A \226\134\146 Type}
  `{gen_heapPreG (sigT L) (sigT V) \206\163} \207\131 :
  (|==> \226\136\131 _ : gen_typed_heapG L V \206\163, gen_typed_heap_ctx \207\131)%I.
Time Proof.
Time iMod (gen_heap_init (\206\187 k, pull_lock (dynMap \207\131 k))) as ( Hgen ) "?".
Time iModIntro.
Time by iExists {| gt_inG := Hgen |}.
Time Qed.
Time
Lemma gen_typed_heap_strong_init {A} {L V : A \226\134\146 Type}
  `{H : gen_heapPreG (sigT L) (sigT V) \206\163} \207\131 :
  (|==> \226\136\131 (H0 : gen_typed_heapG L V \206\163) (Hpf : @gen_heap_inG _ _ _ _ gt_inG =
                                              gen_heap_preG_inG),
          gen_typed_heap_ctx \207\131
          \226\136\151 own (gen_heap_name gt_inG) (\226\151\175 to_gen_typed_heap \207\131))%I.
Time Proof.
Time
iMod (gen_heap_strong_init (\206\187 k, pull_lock (dynMap \207\131 k))) as ( Hgen ? )
 "(?&?)".
Time iModIntro.
Time (unshelve iExists {| gt_inG := Hgen |} , _; eauto).
Time iFrame.
Time Qed.
Time Section gen_heap.
Time Context `{gen_typed_heapG A L V \206\163}.
Time Implicit Types P Q : iProp \206\163.
Time Implicit Type \207\131 : DynMap L (\206\187 T, (LockStatus * V T)%type).
Time Implicit Types h g : gen_typed_heapUR A L V.
Time #[global]
Instance mapsto_timeless  {T} (l : L T) q m v: (Timeless (mapsto l q m v)).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]
Instance read_mapsto_timeless  {T} (l : L T) v: (Timeless (l r\226\134\166 v)).
Time Proof.
Time (apply _).
Time Qed.
Time
Lemma mapsto_agree_generic {T} (l : L T) (q1 q2 : Z) 
  ls1 ls2 v1 v2 : mapsto l q1 ls1 v1 -\226\136\151 mapsto l q2 ls2 v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time iIntros "H1 H2".
Time iDestruct (@mapsto_agree_generic with "H1 H2") as % Heq'.
Time by inj_pair2.
Time Qed.
Time
Lemma mapsto_agree {T} (l : L T) q1 q2 v1 v2 :
  l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Time Proof.
Time iIntros "H1 H2".
Time iDestruct (@mapsto_agree with "H1 H2") as % Heq'.
Time by inj_pair2.
Time Qed.
Time
Lemma mapsto_valid {T} (l : L T) q1 q2 v1 v2 :
  (q1 >= 0 \226\134\146 q2 >= 0 \226\134\146 l \226\134\166{q1} v1 -\226\136\151 l \226\134\166{q2} v2 -\226\136\151 False)%Z.
Time Proof.
Time iIntros ( ? ? ) "H1 H2".
Time by iApply (@mapsto_valid with "H1 H2").
Time Qed.
Time
Lemma mapsto_valid' {T} (l : L T) v1 v2 : l \226\134\166{0} v1 -\226\136\151 l \226\134\166{- 1} v2 -\226\136\151 False.
Time Proof.
Time iIntros "H1 H2".
Time by iApply (@mapsto_valid' with "H1 H2").
Time Qed.
Time
Lemma mapsto_valid_generic {T} (l : L T) (q1 q2 : Z) 
  ls1 ls2 v1 v2 :
  (q1 >= 0 \226\134\146 q2 >= 0 \226\134\146 mapsto l q1 ls1 v1 -\226\136\151 mapsto l q2 ls2 v2 -\226\136\151 False)%Z.
Time Proof.
Time iIntros ( ? ? ) "H1 H2".
Time by iApply (@mapsto_valid_generic with "H1 H2").
Time Qed.
Time
Lemma read_split_join1 {T} (l : L T) (q : nat) n v :
  mapsto l q (ReadLocked n) v
  \226\138\163\226\138\162 mapsto l (S q) Unlocked v \226\136\151 mapsto l (- 1) (ReadLocked n) v.
Time Proof.
Time rewrite /mapsto /read_mapsto.
Time (apply @read_split_join1).
Time Qed.
Time
Lemma read_split_join2 {T} (l : L T) (q : nat) n v :
  mapsto l q (ReadLocked n) v
  \226\138\163\226\138\162 mapsto l (S q) (ReadLocked n) v \226\136\151 mapsto l (- 1) Unlocked v.
Time Proof.
Time rewrite /mapsto /read_mapsto.
Time (apply @read_split_join2).
Time Qed.
Time
Lemma read_split_join3 {T} (l : L T) (q : nat) v :
  mapsto l q Locked v \226\138\163\226\138\162 mapsto l (S q) Locked v \226\136\151 mapsto l (- 1) Locked v.
Time Proof.
Time rewrite /mapsto /read_mapsto.
Time (apply @read_split_join3).
Time Qed.
Time
Lemma read_split_join {T} (l : L T) (q : nat) v :
  l \226\134\166{q} v \226\138\163\226\138\162 l \226\134\166{S q} v \226\136\151 l r\226\134\166 v.
Time Proof.
Time rewrite /mapsto /read_mapsto.
Time (apply @read_split_join).
Time Qed.
Time
Lemma pull_lock_getDyn {T} \207\131 l (s : LockStatus) v :
  pull_lock (\207\131.(dynMap) (existT T l)) = Some (s, existT T v)
  \226\134\146 getDyn \207\131 l = Some (s, v).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /pull_lock =>Heq').
Time (eapply (getDyn_lookup1 \207\131)).
Time
(<ssreflect_plugin::ssrtclintros@0> destruct (dynMap) as [(?, (?, ?))| ]
 =>//=).
Time (inversion Heq').
Time subst.
Time by inj_pair2.
Time Qed.
Time
Lemma gen_typed_heap_alloc T \207\131 (l : L T) v :
  getDyn \207\131 l = None
  \226\134\146 gen_typed_heap_ctx \207\131
    ==\226\136\151 gen_typed_heap_ctx (updDyn l (Unlocked, v) \207\131) \226\136\151 l \226\134\166 v.
Time Proof.
Time iIntros ( Hnone ) "H\207\131".
Time
iMod (@gen_heap_alloc _ _ _ _ _ _ (existT _ l) (existT _ v) with "H\207\131") as
 "(H&$)".
Time {
Time rewrite /= getDyn_lookup_none2 //=.
Time }
Time iModIntro.
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (@gen_heap_ctx_proper with "H")
 =>k).
Time rewrite /insert /partial_fn_insert /updDyn //=.
Time (<ssreflect_plugin::ssrtclintros@0> destruct equal =>//=).
Time Qed.
Time
Lemma gen_typed_heap_dealloc T \207\131 (l : L T) v :
  gen_typed_heap_ctx \207\131 -\226\136\151 l \226\134\166 v ==\226\136\151 gen_typed_heap_ctx (deleteDyn l \207\131).
Time Proof.
Time iIntros "H\207\131 Hl".
Time iMod (@gen_heap_dealloc _ _ _ _ _ _ (existT _ l) with "H\207\131 Hl") as "H".
Time iModIntro.
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (@gen_heap_ctx_proper with "H")
 =>k).
Time rewrite /delete /partial_fn_delete /deleteDyn //=.
Time (<ssreflect_plugin::ssrtclintros@0> destruct equal =>//=).
Time Qed.
Time
Lemma gen_typed_heap_valid1 T \207\131 (l : L T) s v :
  gen_typed_heap_ctx \207\131 -\226\136\151 mapsto l 0 s v -\226\136\151 \226\140\156getDyn \207\131 l = Some (s, v)\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time iDestruct (@gen_heap_valid1 with "H\207\131 Hl") as % Heq'.
Time eauto using pull_lock_getDyn.
Time Qed.
Time
Lemma gen_typed_heap_valid2 T \207\131 (l : L T) z s v :
  gen_typed_heap_ctx \207\131
  -\226\136\151 mapsto l z s v
     -\226\136\151 \226\140\156\226\136\131 s' : LockStatus,
           getDyn \207\131 l = Some (s', v) \226\136\167 to_lock s \226\137\188 to_lock s'\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time iDestruct (@gen_heap_valid2 with "H\207\131 Hl") as % [s' [Heq' ?]].
Time iPureIntro.
Time (exists s'; split; auto).
Time eauto using pull_lock_getDyn.
Time Qed.
Time
Lemma gen_typed_heap_valid T \207\131 (l : L T) q v :
  gen_typed_heap_ctx \207\131
  -\226\136\151 l \226\134\166{q} v -\226\136\151 \226\140\156\226\136\131 s, getDyn \207\131 l = Some (s, v) \226\136\167 s \226\137\160 Locked\226\140\157.
Time Proof.
Time iIntros "H\207\131 Hl".
Time iDestruct (@gen_heap_valid with "H\207\131 Hl") as % [s' [Heq' ?]].
Time iPureIntro.
Time (exists s'; split; auto).
Time eauto using pull_lock_getDyn.
Time Qed.
Time
Lemma gen_typed_heap_update T \207\131 (l : L T) s1 s2 (v1 v2 : V T) :
  gen_typed_heap_ctx \207\131
  -\226\136\151 mapsto l 0 s1 v1
     ==\226\136\151 gen_typed_heap_ctx (updDyn l (s2, v2) \207\131) \226\136\151 mapsto l 0 s2 v2.
Time Proof.
Time iIntros "H\207\131 Hl".
Time iMod (@gen_heap_update with "H\207\131 Hl") as "(H\207\131&$)".
Time iModIntro.
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (@gen_heap_ctx_proper with "H\207\131")
 =>k).
Time rewrite /insert /partial_fn_insert /updDyn //=.
Time (<ssreflect_plugin::ssrtclintros@0> destruct equal =>//=).
Time Qed.
Time
Lemma gen_typed_heap_readlock T \207\131 (l : L T) q v :
  gen_typed_heap_ctx \207\131
  -\226\136\151 mapsto l q Unlocked v
     ==\226\136\151 \226\136\131 s,
           \226\140\156getDyn \207\131 l = Some (s, v)\226\140\157
           \226\136\151 gen_typed_heap_ctx (updDyn l (force_read_lock s, v) \207\131)
             \226\136\151 mapsto l q (ReadLocked 0) v.
Time Proof.
Time iIntros "H\207\131 Hl".
Time iMod (@gen_heap_readlock with "H\207\131 Hl") as ( s Heq' ) "(H\207\131&$)".
Time iModIntro.
Time iExists s.
Time iSplitL "".
Time {
Time eauto using pull_lock_getDyn.
Time }
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (@gen_heap_ctx_proper with "H\207\131")
 =>k).
Time rewrite /insert /partial_fn_insert /updDyn //=.
Time (<ssreflect_plugin::ssrtclintros@0> destruct equal =>//=).
Time Qed.
Time
Lemma gen_typed_heap_readlock' T \207\131 (l : L T) q v n :
  gen_typed_heap_ctx \207\131
  -\226\136\151 mapsto l q (ReadLocked n) v
     ==\226\136\151 \226\136\131 s,
           \226\140\156getDyn \207\131 l = Some (s, v)\226\140\157
           \226\136\151 gen_typed_heap_ctx (updDyn l (force_read_lock s, v) \207\131)
             \226\136\151 mapsto l q (ReadLocked (S n)) v.
Time Proof.
Time iIntros "H\207\131 Hl".
Time iMod (@gen_heap_readlock' with "H\207\131 Hl") as ( s Heq' ) "(H\207\131&$)".
Time iModIntro.
Time iExists s.
Time iSplitL "".
Time {
Time eauto using pull_lock_getDyn.
Time }
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (@gen_heap_ctx_proper with "H\207\131")
 =>k).
Time rewrite /insert /partial_fn_insert /updDyn //=.
Time (<ssreflect_plugin::ssrtclintros@0> destruct equal =>//=).
Time Qed.
Time
Lemma gen_typed_heap_readunlock T \207\131 (l : L T) q n1 
  v :
  gen_typed_heap_ctx \207\131
  -\226\136\151 mapsto l q (ReadLocked n1) v
     ==\226\136\151 \226\136\131 n,
           \226\140\156getDyn \207\131 l = Some (ReadLocked n, v)\226\140\157
           \226\136\151 gen_typed_heap_ctx
               (updDyn l (force_read_unlock (ReadLocked n), v) \207\131)
             \226\136\151 mapsto l q (force_read_unlock (ReadLocked n1)) v.
Time Proof.
Time iIntros "H\207\131 Hl".
Time iMod (@gen_heap_readunlock with "H\207\131 Hl") as ( s Heq' ) "(H\207\131&$)".
Time iModIntro.
Time iExists s.
Time iSplitL "".
Time {
Time eauto using pull_lock_getDyn.
Time }
Time
(<ssreflect_plugin::ssrtclintros@0> iApply (@gen_heap_ctx_proper with "H\207\131")
 =>k).
Time rewrite /insert /partial_fn_insert /updDyn //=.
Time (<ssreflect_plugin::ssrtclintros@0> destruct equal =>//=).
Time Qed.
Time End gen_heap.
