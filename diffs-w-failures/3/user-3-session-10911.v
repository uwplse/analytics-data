Time From Coq Require Import PArith.
Time From stdpp Require Import mapset countable.
Time From stdpp Require Export fin_maps.
Time Set Default Proof Using "Type".
Time #[local]Open Scope positive_scope.
Time #[local]Hint Extern 0 (_ =@{ positive} _) => congruence: core.
Time #[local]Hint Extern 0 (_ \226\137\160@{ positive} _) => congruence: core.
Time
Inductive Pmap_raw (A : Type) : Type :=
  | PLeaf : Pmap_raw A
  | PNode : option A \226\134\146 Pmap_raw A \226\134\146 Pmap_raw A \226\134\146 Pmap_raw A.
Time Arguments PLeaf {_} : assert.
Time Arguments PNode {_} _ _ _ : assert.
Time Instance Pmap_raw_eq_dec  `{EqDecision A}: (EqDecision (Pmap_raw A)).
Time Proof.
Time solve_decision.
Time Defined.
Time
Fixpoint Pmap_wf {A} (t : Pmap_raw A) : bool :=
  match t with
  | PLeaf => true
  | PNode None PLeaf PLeaf => false
  | PNode _ l r => Pmap_wf l && Pmap_wf r
  end.
Time Arguments Pmap_wf _ !_ / : simpl nomatch,  assert.
Time
Lemma Pmap_wf_l {A} o (l r : Pmap_raw A) : Pmap_wf (PNode o l r) \226\134\146 Pmap_wf l.
Time Proof.
Time (destruct o, l, r; simpl; rewrite ?andb_True; tauto).
Time Qed.
Time
Lemma Pmap_wf_r {A} o (l r : Pmap_raw A) : Pmap_wf (PNode o l r) \226\134\146 Pmap_wf r.
Time Proof.
Time (destruct o, l, r; simpl; rewrite ?andb_True; tauto).
Time Qed.
Time #[local]Hint Immediate Pmap_wf_l Pmap_wf_r: core.
Time
Definition PNode' {A} (o : option A) (l r : Pmap_raw A) :=
  match l, o, r with
  | PLeaf, None, PLeaf => PLeaf
  | _, _, _ => PNode o l r
  end.
Time Arguments PNode' : simpl never.
Time
Lemma PNode_wf {A} o (l r : Pmap_raw A) :
  Pmap_wf l \226\134\146 Pmap_wf r \226\134\146 Pmap_wf (PNode' o l r).
Time Proof.
Time (destruct o, l, r; simpl; auto).
Time Qed.
Time #[local]Hint Resolve PNode_wf: core.
Time Instance Pempty_raw  {A}: (Empty (Pmap_raw A)) := PLeaf.
Time
Instance Plookup_raw  {A}: (Lookup positive A (Pmap_raw A)) :=
 (fix go (i : positive) (t : Pmap_raw A) {struct t} : 
  option A :=
    let _ : Lookup _ _ _ := @go in
    match t with
    | PLeaf => None
    | PNode o l r =>
        match i with
        | 1 => o
        | i~0 => l !! i
        | i~1 => r !! i
        end
    end).
Time #[local]Arguments lookup _ _ _ _ _ !_ / : simpl nomatch,  assert.
Time
Fixpoint Psingleton_raw {A} (i : positive) (x : A) : 
Pmap_raw A :=
  match i with
  | 1 => PNode (Some x) PLeaf PLeaf
  | i~0 => PNode None (Psingleton_raw i x) PLeaf
  | i~1 => PNode None PLeaf (Psingleton_raw i x)
  end.
Time
Fixpoint Ppartial_alter_raw {A} (f : option A \226\134\146 option A) 
(i : positive) (t : Pmap_raw A) {struct t} : Pmap_raw A :=
  match t with
  | PLeaf =>
      match f None with
      | None => PLeaf
      | Some x => Psingleton_raw i x
      end
  | PNode o l r =>
      match i with
      | 1 => PNode' (f o) l r
      | i~0 => PNode' o (Ppartial_alter_raw f i l) r
      | i~1 => PNode' o l (Ppartial_alter_raw f i r)
      end
  end.
Time
Fixpoint Pfmap_raw {A B} (f : A \226\134\146 B) (t : Pmap_raw A) : 
Pmap_raw B :=
  match t with
  | PLeaf => PLeaf
  | PNode o l r => PNode (f <$> o) (Pfmap_raw f l) (Pfmap_raw f r)
  end.
Time
Fixpoint Pto_list_raw {A} (j : positive) (t : Pmap_raw A)
(acc : list (positive * A)) : list (positive * A) :=
  match t with
  | PLeaf => acc
  | PNode o l r =>
      from_option (\206\187 x, [(Preverse j, x)]) [] o ++
      Pto_list_raw j~0 l (Pto_list_raw j~1 r acc)
  end%list.
Time
Fixpoint Pomap_raw {A B} (f : A \226\134\146 option B) (t : Pmap_raw A) : 
Pmap_raw B :=
  match t with
  | PLeaf => PLeaf
  | PNode o l r => PNode' (o \226\137\171= f) (Pomap_raw f l) (Pomap_raw f r)
  end.
Time
Fixpoint Pmerge_raw {A B C} (f : option A \226\134\146 option B \226\134\146 option C)
(t1 : Pmap_raw A) (t2 : Pmap_raw B) : Pmap_raw C :=
  match t1, t2 with
  | PLeaf, t2 => Pomap_raw (f None \226\136\152 Some) t2
  | t1, PLeaf => Pomap_raw (flip f None \226\136\152 Some) t1
  | PNode o1 l1 r1, PNode o2 l2 r2 =>
      PNode' (f o1 o2) (Pmerge_raw f l1 l2) (Pmerge_raw f r1 r2)
  end.
Time
Lemma Pmap_wf_canon {A} (t : Pmap_raw A) :
  (\226\136\128 i, t !! i = None) \226\134\146 Pmap_wf t \226\134\146 t = PLeaf.
Time Proof.
Time (induction t as [| o l IHl r IHr]; intros Ht ?; auto).
Time (assert (o = None) as -> by apply (Ht 1)).
Time
(assert (l = PLeaf) as -> by (apply IHl; try apply (\206\187 i, Ht i~0); eauto)).
Time
by assert (r = PLeaf) as -> by (apply IHr; try apply (\206\187 i, Ht i~1); eauto).
Time Qed.
Time
Lemma Pmap_wf_eq {A} (t1 t2 : Pmap_raw A) :
  (\226\136\128 i, t1 !! i = t2 !! i) \226\134\146 Pmap_wf t1 \226\134\146 Pmap_wf t2 \226\134\146 t1 = t2.
Time Proof.
Time revert t2.
Time
(induction t1 as [| o1 l1 IHl r1 IHr]; intros [| o2 l2 r2] Ht ? ?; simpl;
  auto).
Time -
Time (discriminate (Pmap_wf_canon (PNode o2 l2 r2)); eauto).
Time -
Time (discriminate (Pmap_wf_canon (PNode o1 l1 r1)); eauto).
Time -
Time (f_equal; [ apply (Ht 1) |  |  ]).
Time +
Time (apply IHl; try apply (\206\187 x, Ht x~0); eauto).
Time +
Time (apply IHr; try apply (\206\187 x, Ht x~1); eauto).
Time Qed.
Time
Lemma PNode_lookup {A} o (l r : Pmap_raw A) i :
  PNode' o l r !! i = PNode o l r !! i.
Time Proof.
Time by destruct i, o, l, r.
Time Qed.
Time Lemma Psingleton_wf {A} i (x : A) : Pmap_wf (Psingleton_raw i x).
Time Proof.
Time (induction i as [[]| []| ]; simpl; rewrite ?andb_true_r; auto).
Time Qed.
Time
Lemma Ppartial_alter_wf {A} f i (t : Pmap_raw A) :
  Pmap_wf t \226\134\146 Pmap_wf (Ppartial_alter_raw f i t).
Time Proof.
Time (revert i; induction t as [| o l IHl r IHr]; intros i ?; simpl).
Time -
Time (destruct (f None); auto using Psingleton_wf).
Time -
Time (destruct i; simpl; eauto).
Time Qed.
Time
Lemma Pfmap_wf {A} {B} (f : A \226\134\146 B) t : Pmap_wf t \226\134\146 Pmap_wf (Pfmap_raw f t).
Time Proof.
Time
(induction t as [| [x| ] [] ? [] ?]; simpl in *; rewrite ?andb_True;
  intuition).
Time Qed.
Time
Lemma Pomap_wf {A} {B} (f : A \226\134\146 option B) t :
  Pmap_wf t \226\134\146 Pmap_wf (Pomap_raw f t).
Time Proof.
Time (induction t; simpl; eauto).
Time Qed.
Time
Lemma Pmerge_wf {A} {B} {C} (f : option A \226\134\146 option B \226\134\146 option C) 
  t1 t2 : Pmap_wf t1 \226\134\146 Pmap_wf t2 \226\134\146 Pmap_wf (Pmerge_raw f t1 t2).
Time Proof.
Time revert t2.
Time (induction t1; intros []; simpl; eauto using Pomap_wf).
Time Qed.
Time Lemma Plookup_empty {A} i : (\226\136\133 : Pmap_raw A) !! i = None.
Time Proof.
Time by destruct i.
Time Qed.
Time
Lemma Plookup_singleton {A} i (x : A) : Psingleton_raw i x !! i = Some x.
Time Proof.
Time by induction i.
Time Qed.
Time
Lemma Plookup_singleton_ne {A} i j (x : A) :
  i \226\137\160 j \226\134\146 Psingleton_raw i x !! j = None.
Time Proof.
Time revert j.
Time (induction i; intros [?| ?| ]; simpl; auto with congruence).
Time Qed.
Time
Lemma Plookup_alter {A} f i (t : Pmap_raw A) :
  Ppartial_alter_raw f i t !! i = f (t !! i).
Time Proof.
Time (revert i; induction t as [| o l IHl r IHr]; intros i; simpl).
Time -
Time by destruct (f None); rewrite ?Plookup_singleton.
Time -
Time (destruct i; simpl; rewrite PNode_lookup; simpl; auto).
Time Qed.
Time
Lemma Plookup_alter_ne {A} f i j (t : Pmap_raw A) :
  i \226\137\160 j \226\134\146 Ppartial_alter_raw f i t !! j = t !! j.
Time Proof.
Time (revert i j; induction t as [| o l IHl r IHr]; simpl).
Time -
Time by intros; destruct (f None); rewrite ?Plookup_singleton_ne.
Time -
Time
by intros [?| ?| ] [?| ?| ] ?; simpl; rewrite ?PNode_lookup; simpl; auto.
Time Qed.
Time
Lemma Plookup_fmap {A} {B} (f : A \226\134\146 B) t i :
  Pfmap_raw f t !! i = f <$> t !! i.
Time Proof.
Time revert i.
Time by induction t; intros [?| ?| ]; simpl.
Time Qed.
Time
Lemma Pelem_of_to_list {A} (t : Pmap_raw A) j i acc 
  x :
  (i, x) \226\136\136 Pto_list_raw j t acc
  \226\134\148 (\226\136\131 i', i = i' ++ Preverse j \226\136\167 t !! i' = Some x) \226\136\168 (i, x) \226\136\136 acc.
Time Proof.
Time split.
Time {
Time revert j acc.
Time (induction t as [| [y| ] l IHl r IHr]; intros j acc; simpl).
Time -
Time by right.
Time -
Time (rewrite elem_of_cons).
Time (intros [?| ?]; simplify_eq).
Time {
Time (left; exists 1).
Time by rewrite (left_id_L 1 (++))%positive.
Time }
Time
(destruct (IHl j~0 (Pto_list_raw j~1 r acc)) as [(i', (->, ?))| ?]; auto).
Time {
Time (left; exists i'~0).
Time by rewrite Preverse_xO, (assoc_L _).
Time }
Time (destruct (IHr j~1 acc) as [(i', (->, ?))| ?]; auto).
Time (left; exists i'~1).
Time by rewrite Preverse_xI, (assoc_L _).
Time -
Time (intros).
Time
(destruct (IHl j~0 (Pto_list_raw j~1 r acc)) as [(i', (->, ?))| ?]; auto).
Time {
Time (left; exists i'~0).
Time by rewrite Preverse_xO, (assoc_L _).
Time }
Time (destruct (IHr j~1 acc) as [(i', (->, ?))| ?]; auto).
Time (left; exists i'~1).
Time by rewrite Preverse_xI, (assoc_L _).
Time }
Time revert t j i acc.
Time
(assert (help : \226\136\128 t j i acc, (i, x) \226\136\136 acc \226\134\146 (i, x) \226\136\136 Pto_list_raw j t acc)).
Time {
Time
(intros t; induction t as [| [y| ] l IHl r IHr]; intros j i acc; simpl;
  rewrite ?elem_of_cons; auto).
Time }
Time (intros t j ? acc [(i, (->, Hi))| ?]; [  | by auto ]).
Time revert j i acc Hi.
Time (induction t as [| [y| ] l IHl r IHr]; intros j i acc ?; simpl).
Time -
Time done.
Time -
Time (rewrite elem_of_cons).
Time (destruct i as [i| i| ]; simplify_eq /=).
Time +
Time right.
Time (apply help).
Time specialize (IHr j~1 i).
Time (rewrite Preverse_xI, (assoc_L _) in IHr).
Time by apply IHr.
Time +
Time right.
Time specialize (IHl j~0 i).
Time (rewrite Preverse_xO, (assoc_L _) in IHl).
Time by apply IHl.
Time +
Time left.
Time by rewrite (left_id_L 1 (++))%positive.
Time -
Time (destruct i as [i| i| ]; simplify_eq /=).
Time +
Time (apply help).
Time specialize (IHr j~1 i).
Time (rewrite Preverse_xI, (assoc_L _) in IHr).
Time by apply IHr.
Time +
Time specialize (IHl j~0 i).
Time (rewrite Preverse_xO, (assoc_L _) in IHl).
Time by apply IHl.
Time Qed.
Time
Lemma Pto_list_nodup {A} j (t : Pmap_raw A) acc :
  (\226\136\128 i x, (i ++ Preverse j, x) \226\136\136 acc \226\134\146 t !! i = None)
  \226\134\146 NoDup acc \226\134\146 NoDup (Pto_list_raw j t acc).
Time Proof.
Time revert j acc.
Time (induction t as [| [y| ] l IHl r IHr]; simpl; intros j acc Hin ?).
Time -
Time done.
Time -
Time (repeat constructor).
Time {
Time (rewrite Pelem_of_to_list).
Time (intros [(i, (Hi, ?))| Hj]).
Time {
Time (apply (f_equal Plength) in Hi).
Time (rewrite Preverse_xO, !Papp_length in Hi; simpl in *; lia).
Time }
Time (rewrite Pelem_of_to_list in Hj).
Time (destruct Hj as [(i, (Hi, ?))| Hj]).
Time {
Time (apply (f_equal Plength) in Hi).
Time (rewrite Preverse_xI, !Papp_length in Hi; simpl in *; lia).
Time }
Time specialize (Hin 1 y).
Time (rewrite (left_id_L 1 (++))%positive in Hin).
Time discriminate (Hin Hj).
Time }
Time (apply IHl).
Time {
Time (intros i x).
Time (rewrite Pelem_of_to_list).
Time (intros [(?, (Hi, ?))| Hi]).
Time +
Time (rewrite Preverse_xO, Preverse_xI, !(assoc_L _) in Hi).
Time by apply (inj (++_)) in Hi.
Time +
Time (apply (Hin i~0 x)).
Time by rewrite Preverse_xO, (assoc_L _) in Hi.
Time }
Time (apply IHr; auto).
Time (intros i x Hi).
Time (apply (Hin i~1 x)).
Time by rewrite Preverse_xI, (assoc_L _) in Hi.
Time -
Time (apply IHl).
Time {
Time (intros i x).
Time (rewrite Pelem_of_to_list).
Time (intros [(?, (Hi, ?))| Hi]).
Time +
Time (rewrite Preverse_xO, Preverse_xI, !(assoc_L _) in Hi).
Time by apply (inj (++_)) in Hi.
Time +
Time (apply (Hin i~0 x)).
Time by rewrite Preverse_xO, (assoc_L _) in Hi.
Time }
Time (apply IHr; auto).
Time (intros i x Hi).
Time (apply (Hin i~1 x)).
Time by rewrite Preverse_xI, (assoc_L _) in Hi.
Time Qed.
Time
Lemma Pomap_lookup {A} {B} (f : A \226\134\146 option B) t i :
  Pomap_raw f t !! i = t !! i \226\137\171= f.
Time Proof.
Time revert i.
Time
(induction t as [| o l IHl r IHr]; intros [i| i| ]; simpl;
  rewrite ?PNode_lookup; simpl; auto).
Time Qed.
Time
Lemma Pmerge_lookup {A} {B} {C} (f : option A \226\134\146 option B \226\134\146 option C)
  (Hf : f None None = None) t1 t2 i :
  Pmerge_raw f t1 t2 !! i = f (t1 !! i) (t2 !! i).
Time Proof.
Time
(revert t2 i; induction t1 as [| o1 l1 IHl1 r1 IHr1]; intros t2 i; simpl).
Time {
Time (rewrite Pomap_lookup).
Time by destruct (t2 !! i).
Time }
Time (unfold compose, flip).
Time (destruct t2 as [| l2 o2 r2]; rewrite PNode_lookup).
Time -
Time
by
 destruct i; rewrite ?Pomap_lookup; simpl; rewrite ?Pomap_lookup;
  match goal with
  | |- ?o \226\137\171= _ = _ => destruct o
  end.
Time -
Time (destruct i; rewrite ?Pomap_lookup; simpl; auto).
Time Qed.
Time
Inductive Pmap (A : Type) : Type :=
 PMap {pmap_car : Pmap_raw A; pmap_prf : Pmap_wf pmap_car}.
Time Arguments PMap {_} _ _ : assert.
Time Arguments pmap_car {_} _ : assert.
Time Arguments pmap_prf {_} _ : assert.
Time
Lemma Pmap_eq {A} (m1 m2 : Pmap A) : m1 = m2 \226\134\148 pmap_car m1 = pmap_car m2.
Time Proof.
Time (split; [ by intros -> | intros ]; destruct m1 as [t1 ?], m2 as [t2 ?]).
Time (simplify_eq /=; f_equal; apply proof_irrel).
Time Qed.
Time
Instance Pmap_eq_dec  `{EqDecision A}: (EqDecision (Pmap A)) :=
 (\206\187 m1 m2,
    match Pmap_raw_eq_dec (pmap_car m1) (pmap_car m2) with
    | left H => left (proj2 (Pmap_eq m1 m2) H)
    | right H => right (H \226\136\152 proj1 (Pmap_eq m1 m2))
    end).
Time Instance Pempty  {A}: (Empty (Pmap A)) := (PMap \226\136\133 I).
Time
Instance Plookup  {A}: (Lookup positive A (Pmap A)) :=
 (\206\187 i m, pmap_car m !! i).
Time
Instance Ppartial_alter  {A}: (PartialAlter positive A (Pmap A)) :=
 (\206\187 f i m,
    let (t, Ht) := m in
    PMap (partial_alter f i t) (Ppartial_alter_wf f i _ Ht)).
Time
Instance Pfmap : (FMap Pmap) :=
 (\206\187 A B f m, let (t, Ht) := m in PMap (f <$> t) (Pfmap_wf f _ Ht)).
Time
Instance Pto_list  {A}: (FinMapToList positive A (Pmap A)) :=
 (\206\187 m, let (t, Ht) := m in Pto_list_raw 1 t []).
Time
Instance Pomap : (OMap Pmap) :=
 (\206\187 A B f m, let (t, Ht) := m in PMap (omap f t) (Pomap_wf f _ Ht)).
Time
Instance Pmerge : (Merge Pmap) :=
 (\206\187 A B C f m1 m2,
    let (t1, Ht1) := m1 in
    let (t2, Ht2) := m2 in PMap _ (Pmerge_wf f _ _ Ht1 Ht2)).
Time Instance Pmap_finmap : (FinMap positive Pmap).
Time Proof.
Time split.
Time -
Time by intros ? [t1 ?] [t2 ?] ?; apply Pmap_eq, Pmap_wf_eq.
Time -
Time by intros ? [].
Time -
Time (intros ? ? [? ?] ?).
Time by apply Plookup_alter.
Time -
Time (intros ? ? [? ?] ? ?).
Time by apply Plookup_alter_ne.
Time -
Time (intros ? ? ? [? ?]).
Time by apply Plookup_fmap.
Time -
Time (intros ? [? ?]).
Time (apply Pto_list_nodup; [  | constructor ]).
Time (intros ? ?).
Time by rewrite elem_of_nil.
Time -
Time (intros ? [? ?] i x; unfold map_to_list, Pto_list).
Time (rewrite Pelem_of_to_list, elem_of_nil).
Time split.
Time by intros [(?, (->, ?))| ].
Time by left; exists i.
Time -
Time (intros ? ? ? [? ?] ?).
Time by apply Pomap_lookup.
Time -
Time (intros ? ? ? ? ? [? ?] [? ?] ?).
Time by apply Pmerge_lookup.
Time Qed.
Time #[program]
Instance Pmap_countable  `{Countable A}: (Countable (Pmap A)) := {
 encode :=fun m => encode (map_to_list m : list (positive * A));
 decode :=fun p => list_to_map <$> decode p}.
Time Next Obligation.
Time (intros A ? ? m; simpl).
Time (rewrite decode_encode; simpl).
Time by rewrite list_to_map_to_list.
Time Qed.
Time Notation Pset := (mapset Pmap).
Time Instance Pmap_dom  {A}: (Dom (Pmap A) Pset) := mapset_dom.
Time
Instance Pmap_dom_spec : (FinMapDom positive Pmap Pset) := mapset_dom_spec.
