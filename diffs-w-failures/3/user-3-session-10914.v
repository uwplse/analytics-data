Time From stdpp Require Export sets.
Time From stdpp Require Import pmap gmap mapset.
Time Set Default Proof Using "Type".
Time #[local]Open Scope positive_scope.
Time
Inductive coPset_raw :=
  | coPLeaf : bool \226\134\146 coPset_raw
  | coPNode : bool \226\134\146 coPset_raw \226\134\146 coPset_raw \226\134\146 coPset_raw.
Time Instance coPset_raw_eq_dec : (EqDecision coPset_raw).
Time Proof.
Time solve_decision.
Time Defined.
Time
Fixpoint coPset_wf (t : coPset_raw) : bool :=
  match t with
  | coPLeaf _ => true
  | coPNode true (coPLeaf true) (coPLeaf true) => false
  | coPNode false (coPLeaf false) (coPLeaf false) => false
  | coPNode b l r => coPset_wf l && coPset_wf r
  end.
Time Arguments coPset_wf !_ / : simpl nomatch,  assert.
Time Lemma coPNode_wf_l b l r : coPset_wf (coPNode b l r) \226\134\146 coPset_wf l.
Time Proof.
Time
(destruct b, l as [[]| ], r as [[]| ]; simpl; rewrite ?andb_True; tauto).
Time Qed.
Time Lemma coPNode_wf_r b l r : coPset_wf (coPNode b l r) \226\134\146 coPset_wf r.
Time Proof.
Time
(destruct b, l as [[]| ], r as [[]| ]; simpl; rewrite ?andb_True; tauto).
Time Qed.
Time #[local]Hint Immediate coPNode_wf_l coPNode_wf_r: core.
Time
Definition coPNode' (b : bool) (l r : coPset_raw) : coPset_raw :=
  match b, l, r with
  | true, coPLeaf true, coPLeaf true => coPLeaf true
  | false, coPLeaf false, coPLeaf false => coPLeaf false
  | _, _, _ => coPNode b l r
  end.
Time Arguments coPNode' : simpl never.
Time
Lemma coPNode_wf b l r :
  coPset_wf l \226\134\146 coPset_wf r \226\134\146 coPset_wf (coPNode' b l r).
Time Proof.
Time (destruct b, l as [[]| ], r as [[]| ]; simpl; auto).
Time Qed.
Time Hint Resolve coPNode_wf: core.
Time
Fixpoint coPset_elem_of_raw (p : positive) (t : coPset_raw) {struct t} : bool
:=
  match t, p with
  | coPLeaf b, _ => b
  | coPNode b l r, 1 => b
  | coPNode _ l _, p~0 => coPset_elem_of_raw p l
  | coPNode _ _ r, p~1 => coPset_elem_of_raw p r
  end.
Time #[local]Notation e_of := coPset_elem_of_raw.
Time Arguments coPset_elem_of_raw _ !_ / : simpl nomatch,  assert.
Time
Lemma coPset_elem_of_node b l r p :
  e_of p (coPNode' b l r) = e_of p (coPNode b l r).
Time Proof.
Time by destruct p, b, l as [[]| ], r as [[]| ].
Time Qed.
Time
Lemma coPLeaf_wf t b : (\226\136\128 p, e_of p t = b) \226\134\146 coPset_wf t \226\134\146 t = coPLeaf b.
Time Proof.
Time
(induction t as [b'| b' l IHl r IHr]; intros Ht ?;
  [ f_equal; apply (Ht 1) |  ]).
Time (assert (b' = b) by apply (Ht 1); subst).
Time
(assert (l = coPLeaf b) as -> by (apply IHl; try apply (\206\187 p, Ht p~0); eauto)).
Time
(assert (r = coPLeaf b) as -> by (apply IHr; try apply (\206\187 p, Ht p~1); eauto)).
Time by destruct b.
Time Qed.
Time
Lemma coPset_eq t1 t2 :
  (\226\136\128 p, e_of p t1 = e_of p t2) \226\134\146 coPset_wf t1 \226\134\146 coPset_wf t2 \226\134\146 t1 = t2.
Time Proof.
Time revert t2.
Time
(induction t1 as [b1| b1 l1 IHl r1 IHr]; intros [b2| b2 l2 r2] Ht ? ?;
  simpl in *).
Time -
Time (f_equal; apply (Ht 1)).
Time -
Time by discriminate (coPLeaf_wf (coPNode b2 l2 r2) b1).
Time -
Time by discriminate (coPLeaf_wf (coPNode b1 l1 r1) b2).
Time -
Time (f_equal; [ apply (Ht 1) |  |  ]).
Time +
Time (apply IHl; try apply (\206\187 x, Ht x~0); eauto).
Time +
Time (apply IHr; try apply (\206\187 x, Ht x~1); eauto).
Time Qed.
Time
Fixpoint coPset_singleton_raw (p : positive) : coPset_raw :=
  match p with
  | 1 => coPNode true (coPLeaf false) (coPLeaf false)
  | p~0 => coPNode' false (coPset_singleton_raw p) (coPLeaf false)
  | p~1 => coPNode' false (coPLeaf false) (coPset_singleton_raw p)
  end.
Time
Instance coPset_union_raw : (Union coPset_raw) :=
 (fix go t1 t2 :=
    let _ : Union _ := @go in
    match t1, t2 with
    | coPLeaf false, coPLeaf false => coPLeaf false
    | _, coPLeaf true => coPLeaf true
    | coPLeaf true, _ => coPLeaf true
    | coPNode b l r, coPLeaf false => coPNode b l r
    | coPLeaf false, coPNode b l r => coPNode b l r
    | coPNode b1 l1 r1, coPNode b2 l2 r2 =>
        coPNode' (b1 || b2) (l1 \226\136\170 l2) (r1 \226\136\170 r2)
    end).
Time #[local]Arguments union _ _ !_ !_ / : assert.
Time
Instance coPset_intersection_raw : (Intersection coPset_raw) :=
 (fix go t1 t2 :=
    let _ : Intersection _ := @go in
    match t1, t2 with
    | coPLeaf true, coPLeaf true => coPLeaf true
    | _, coPLeaf false => coPLeaf false
    | coPLeaf false, _ => coPLeaf false
    | coPNode b l r, coPLeaf true => coPNode b l r
    | coPLeaf true, coPNode b l r => coPNode b l r
    | coPNode b1 l1 r1, coPNode b2 l2 r2 =>
        coPNode' (b1 && b2) (l1 \226\136\169 l2) (r1 \226\136\169 r2)
    end).
Time #[local]Arguments intersection _ _ !_ !_ / : assert.
Time
Fixpoint coPset_opp_raw (t : coPset_raw) : coPset_raw :=
  match t with
  | coPLeaf b => coPLeaf (negb b)
  | coPNode b l r => coPNode' (negb b) (coPset_opp_raw l) (coPset_opp_raw r)
  end.
Time Lemma coPset_singleton_wf p : coPset_wf (coPset_singleton_raw p).
Time Proof.
Time (induction p; simpl; eauto).
Time Qed.
Time
Lemma coPset_union_wf t1 t2 :
  coPset_wf t1 \226\134\146 coPset_wf t2 \226\134\146 coPset_wf (t1 \226\136\170 t2).
Time Proof.
Time
(revert t2; induction t1 as [[]| []]; intros [[]| [] ? ?]; simpl; eauto).
Time Qed.
Time
Lemma coPset_intersection_wf t1 t2 :
  coPset_wf t1 \226\134\146 coPset_wf t2 \226\134\146 coPset_wf (t1 \226\136\169 t2).
Time Proof.
Time
(revert t2; induction t1 as [[]| []]; intros [[]| [] ? ?]; simpl; eauto).
Time Qed.
Time Lemma coPset_opp_wf t : coPset_wf (coPset_opp_raw t).
Time Proof.
Time (induction t as [[]| []]; simpl; eauto).
Time Qed.
Time
Lemma coPset_elem_of_singleton p q : e_of p (coPset_singleton_raw q) \226\134\148 p = q.
Time Proof.
Time
(split; [  | by intros <-; induction p; simpl; rewrite ?coPset_elem_of_node ]).
Time
by
 revert q; induction p; intros [?| ?| ]; simpl; rewrite ?coPset_elem_of_node;
  intros; f_equal /=; auto.
Time Qed.
Time
Lemma coPset_elem_of_union t1 t2 p :
  e_of p (t1 \226\136\170 t2) = e_of p t1 || e_of p t2.
Time Proof.
Time
by
 revert t2 p; induction t1 as [[]| []]; intros [[]| [] ? ?] [?| ?| ]; simpl;
  rewrite ?coPset_elem_of_node; simpl;
  rewrite ?orb_true_l, ?orb_false_l, ?orb_true_r, ?orb_false_r.
Time Qed.
Time
Lemma coPset_elem_of_intersection t1 t2 p :
  e_of p (t1 \226\136\169 t2) = e_of p t1 && e_of p t2.
Time Proof.
Time
by
 revert t2 p; induction t1 as [[]| []]; intros [[]| [] ? ?] [?| ?| ]; simpl;
  rewrite ?coPset_elem_of_node; simpl;
  rewrite ?andb_true_l, ?andb_false_l, ?andb_true_r, ?andb_false_r.
Time Qed.
Time
Lemma coPset_elem_of_opp t p : e_of p (coPset_opp_raw t) = negb (e_of p t).
Time Proof.
Time
by
 revert p; induction t as [[]| []]; intros [?| ?| ]; simpl;
  rewrite ?coPset_elem_of_node; simpl.
Time Qed.
Time Definition coPset := {t | coPset_wf t}.
Time
Instance coPset_singleton : (Singleton positive coPset) :=
 (\206\187 p, coPset_singleton_raw p \226\134\190 coPset_singleton_wf _).
Time
Instance coPset_elem_of : (ElemOf positive coPset) := (\206\187 p X, e_of p (`X)).
Time Instance coPset_empty : (Empty coPset) := (coPLeaf false \226\134\190 I).
Time Instance coPset_top : (Top coPset) := (coPLeaf true \226\134\190 I).
Time
Instance coPset_union : (Union coPset) :=
 (\206\187 X Y,
    let (t1, Ht1) := X in
    let (t2, Ht2) := Y in (t1 \226\136\170 t2) \226\134\190 coPset_union_wf _ _ Ht1 Ht2).
Time
Instance coPset_intersection : (Intersection coPset) :=
 (\206\187 X Y,
    let (t1, Ht1) := X in
    let (t2, Ht2) := Y in (t1 \226\136\169 t2) \226\134\190 coPset_intersection_wf _ _ Ht1 Ht2).
Time
Instance coPset_difference : (Difference coPset) :=
 (\206\187 X Y,
    let (t1, Ht1) := X in
    let (t2, Ht2) := Y in
    (t1 \226\136\169 coPset_opp_raw t2)
    \226\134\190 coPset_intersection_wf _ _ Ht1 (coPset_opp_wf _)).
Time Instance coPset_set : (Set_ positive coPset).
Time Proof.
Time (split; [ split |  |  ]).
Time -
Time by intros ? ?.
Time -
Time (intros p q).
Time (apply coPset_elem_of_singleton).
Time -
Time
(intros [t] [t'] p; unfold elem_of, coPset_elem_of, coPset_union; simpl).
Time by rewrite coPset_elem_of_union, orb_True.
Time -
Time
(intros [t] [t'] p; unfold elem_of, coPset_elem_of, coPset_intersection;
  simpl).
Time by rewrite coPset_elem_of_intersection, andb_True.
Time -
Time
(intros [t] [t'] p; unfold elem_of, coPset_elem_of, coPset_difference; simpl).
Time
by
 rewrite coPset_elem_of_intersection, coPset_elem_of_opp, andb_True,
  negb_True.
Time Qed.
Time Instance coPset_leibniz : (LeibnizEquiv coPset).
Time Proof.
Time (intros X Y; rewrite elem_of_equiv; intros HXY).
Time (apply (sig_eq_pi _), coPset_eq; try apply @proj2_sig).
Time (intros p; apply eq_bool_prop_intro, (HXY p)).
Time Qed.
Time Instance coPset_elem_of_dec : (RelDecision (\226\136\136@{coPset} )).
Time Proof.
Time solve_decision.
Time Defined.
Time Instance coPset_equiv_dec : (RelDecision (\226\137\161@{coPset} )).
Time Proof.
Time (refine (\206\187 X Y, cast_if (decide (X = Y))); abstract by fold_leibniz).
Time Defined.
Time Instance mapset_disjoint_dec : (RelDecision (##@{coPset} )).
Time Proof.
Time
(refine (\206\187 X Y, cast_if (decide (X \226\136\169 Y = \226\136\133))); abstract by
  rewrite disjoint_intersection_L).
Time Defined.
Time Instance mapset_subseteq_dec : (RelDecision (\226\138\134@{coPset} )).
Time Proof.
Time
(refine (\206\187 X Y, cast_if (decide (X \226\136\170 Y = Y))); abstract by
  rewrite subseteq_union_L).
Time Defined.
Time Lemma coPset_top_subseteq (X : coPset) : X \226\138\134 \226\138\164.
Time Proof.
Time done.
Time Qed.
Time Hint Resolve coPset_top_subseteq: core.
Time
Fixpoint coPset_finite (t : coPset_raw) : bool :=
  match t with
  | coPLeaf b => negb b
  | coPNode b l r => coPset_finite l && coPset_finite r
  end.
Time
Lemma coPset_finite_node b l r :
  coPset_finite (coPNode' b l r) = coPset_finite l && coPset_finite r.
Time Proof.
Time by destruct b, l as [[]| ], r as [[]| ].
Time Qed.
Time Lemma coPset_finite_spec X : set_finite X \226\134\148 coPset_finite (`X).
Time Proof.
Time (destruct X as [t Ht]).
Time
(unfold set_finite, elem_of at 1, coPset_elem_of; simpl; clear Ht; split).
Time -
Time (induction t as [b| b l IHl r IHr]; simpl).
Time {
Time (destruct b; simpl; [ intros [l Hl] | done ]).
Time by apply (is_fresh (list_to_set l : Pset)), elem_of_list_to_set, Hl.
Time }
Time (intros [ll Hll]; rewrite andb_True; split).
Time +
Time (apply IHl; exists (omap (maybe (~0)) ll); intros i).
Time (rewrite elem_of_list_omap; intros; exists i~0; auto).
Time +
Time (apply IHr; exists (omap (maybe (~1)) ll); intros i).
Time (rewrite elem_of_list_omap; intros; exists i~1; auto).
Time -
Time
(induction t as [b| b l IHl r IHr]; simpl; [ by exists []; destruct b |  ]).
Time
(rewrite andb_True; intros [? ?]; destruct IHl as [ll ?], IHr as [rl ?]; auto).
Time
(exists ([1] ++ ((~0) <$> ll) ++ ((~1) <$> rl))%list; intros [i| i| ]; simpl;
  rewrite elem_of_cons, elem_of_app, !elem_of_list_fmap; naive_solver).
Time Qed.
Time Instance coPset_finite_dec  (X : coPset): (Decision (set_finite X)).
Time Proof.
Time
(refine (cast_if (decide (coPset_finite (`X)))); by
  rewrite coPset_finite_spec).
Time Defined.
Time
Fixpoint coPpick_raw (t : coPset_raw) : option positive :=
  match t with
  | coPLeaf true | coPNode true _ _ => Some 1
  | coPLeaf false => None
  | coPNode false l r =>
      match coPpick_raw l with
      | Some i => Some i~0
      | None => (~1) <$> coPpick_raw r
      end
  end.
Time
Definition coPpick (X : coPset) : positive := default 1 (coPpick_raw (`X)).
Time Lemma coPpick_raw_elem_of t i : coPpick_raw t = Some i \226\134\146 e_of i t.
Time Proof.
Time
(revert i; induction t as [[]| [] l ? r]; intros i ?; simplify_eq /=; auto).
Time (destruct (coPpick_raw l); simplify_option_eq; auto).
Time Qed.
Time Lemma coPpick_raw_None t : coPpick_raw t = None \226\134\146 coPset_finite t.
Time Proof.
Time (induction t as [[]| [] l ? r]; intros i; simplify_eq /=; auto).
Time (destruct (coPpick_raw l); simplify_option_eq; auto).
Time Qed.
Time Lemma coPpick_elem_of X : \194\172 set_finite X \226\134\146 coPpick X \226\136\136 X.
Time Proof.
Time
(destruct X as [t ?]; unfold coPpick; destruct (coPpick_raw _) as [j| ] eqn:?).
Time -
Time by intros; apply coPpick_raw_elem_of.
Time -
Time by intros []; apply coPset_finite_spec, coPpick_raw_None.
Time Qed.
Time
Fixpoint coPset_to_Pset_raw (t : coPset_raw) : Pmap_raw () :=
  match t with
  | coPLeaf _ => PLeaf
  | coPNode false l r =>
      PNode' None (coPset_to_Pset_raw l) (coPset_to_Pset_raw r)
  | coPNode true l r =>
      PNode (Some ()) (coPset_to_Pset_raw l) (coPset_to_Pset_raw r)
  end.
Time
Lemma coPset_to_Pset_wf t : coPset_wf t \226\134\146 Pmap_wf (coPset_to_Pset_raw t).
Time Proof.
Time (induction t as [| []]; simpl; eauto using PNode_wf).
Time Qed.
Time
Definition coPset_to_Pset (X : coPset) : Pset :=
  let (t, Ht) := X in
  Mapset (PMap (coPset_to_Pset_raw t) (coPset_to_Pset_wf _ Ht)).
Time
Lemma elem_of_coPset_to_Pset X i :
  set_finite X \226\134\146 i \226\136\136 coPset_to_Pset X \226\134\148 i \226\136\136 X.
Time Proof.
Time (rewrite coPset_finite_spec; destruct X as [t Ht]).
Time
(change_no_check
   (coPset_finite t \226\134\146 coPset_to_Pset_raw t !! i = Some () \226\134\148 e_of i t)).
Time
(clear Ht; revert i; induction t as [[]| [] l IHl r IHr]; intros [i| i| ];
  simpl; rewrite ?andb_True, ?PNode_lookup; naive_solver).
Time Qed.
Time
Fixpoint Pset_to_coPset_raw (t : Pmap_raw ()) : coPset_raw :=
  match t with
  | PLeaf => coPLeaf false
  | PNode None l r =>
      coPNode false (Pset_to_coPset_raw l) (Pset_to_coPset_raw r)
  | PNode (Some _) l r =>
      coPNode true (Pset_to_coPset_raw l) (Pset_to_coPset_raw r)
  end.
Time
Lemma Pset_to_coPset_wf t : Pmap_wf t \226\134\146 coPset_wf (Pset_to_coPset_raw t).
Time Proof.
Time (induction t as [| [] l IHl r IHr]; simpl; rewrite ?andb_True; auto).
Time -
Time (intros [? ?]; destruct l as [| []], r as [| []]; simpl in *; auto).
Time -
Time
(destruct l as [| []], r as [| []]; simpl in *; rewrite ?andb_true_r;
  rewrite ?andb_True; rewrite ?andb_True in IHl, IHr; intuition).
Time Qed.
Time
Lemma elem_of_Pset_to_coPset_raw i t :
  e_of i (Pset_to_coPset_raw t) \226\134\148 t !! i = Some ().
Time Proof.
Time by revert i; induction t as [| [[]| ]]; intros []; simpl; auto; split.
Time Qed.
Time
Lemma Pset_to_coPset_raw_finite t : coPset_finite (Pset_to_coPset_raw t).
Time Proof.
Time (induction t as [| [[]| ]]; simpl; rewrite ?andb_True; auto).
Time Qed.
Time
Definition Pset_to_coPset (X : Pset) : coPset :=
  let
  'Mapset (PMap t Ht) := X in Pset_to_coPset_raw t \226\134\190 Pset_to_coPset_wf _ Ht.
Time Lemma elem_of_Pset_to_coPset X i : i \226\136\136 Pset_to_coPset X \226\134\148 i \226\136\136 X.
Time Proof.
Time (destruct X as [[t ?]]; apply elem_of_Pset_to_coPset_raw).
Time Qed.
Time Lemma Pset_to_coPset_finite X : set_finite (Pset_to_coPset X).
Time Proof.
Time
(apply coPset_finite_spec; destruct X as [[t ?]];
  apply Pset_to_coPset_raw_finite).
Time Qed.
Time Lemma coPset_to_gset_wf (m : Pmap ()) : gmap_wf positive m.
Time Proof.
Time done.
Time Qed.
Time
Definition coPset_to_gset (X : coPset) : gset positive :=
  let
  'Mapset m := coPset_to_Pset X in
   Mapset (GMap m (bool_decide_pack _ (coPset_to_gset_wf m))).
Time
Definition gset_to_coPset (X : gset positive) : coPset :=
  let
  'Mapset (GMap (PMap t Ht) _) := X in
   Pset_to_coPset_raw t \226\134\190 Pset_to_coPset_wf _ Ht.
Time
Lemma elem_of_coPset_to_gset X i :
  set_finite X \226\134\146 i \226\136\136 coPset_to_gset X \226\134\148 i \226\136\136 X.
Time Proof.
Time (intros ?).
Time (rewrite <- elem_of_coPset_to_Pset by done).
Time (unfold coPset_to_gset).
Time by destruct (coPset_to_Pset X).
Time Qed.
Time Lemma elem_of_gset_to_coPset X i : i \226\136\136 gset_to_coPset X \226\134\148 i \226\136\136 X.
Time Proof.
Time (destruct X as [[[t ?]]]; apply elem_of_Pset_to_coPset_raw).
Time Qed.
Time Lemma gset_to_coPset_finite X : set_finite (gset_to_coPset X).
Time Proof.
Time
(apply coPset_finite_spec; destruct X as [[[t ?]]];
  apply Pset_to_coPset_raw_finite).
Time Qed.
Time
Instance Pmap_dom_coPset  {A}: (Dom (Pmap A) coPset) :=
 (\206\187 m, Pset_to_coPset (dom _ m)).
Time Instance Pmap_dom_coPset_spec : (FinMapDom positive Pmap coPset).
Time Proof.
Time (split; try apply _; intros A m i; unfold dom, Pmap_dom_coPset).
Time by rewrite elem_of_Pset_to_coPset, elem_of_dom.
Time Qed.
Time
Instance gmap_dom_coPset  {A}: (Dom (gmap positive A) coPset) :=
 (\206\187 m, gset_to_coPset (dom _ m)).
Time
Instance gmap_dom_coPset_spec : (FinMapDom positive (gmap positive) coPset).
Time Proof.
Time (split; try apply _; intros A m i; unfold dom, gmap_dom_coPset).
Time by rewrite elem_of_gset_to_coPset, elem_of_dom.
Time Qed.
Time
Fixpoint coPset_suffixes_raw (p : positive) : coPset_raw :=
  match p with
  | 1 => coPLeaf true
  | p~0 => coPNode' false (coPset_suffixes_raw p) (coPLeaf false)
  | p~1 => coPNode' false (coPLeaf false) (coPset_suffixes_raw p)
  end.
Time Lemma coPset_suffixes_wf p : coPset_wf (coPset_suffixes_raw p).
Time Proof.
Time (induction p; simpl; eauto).
Time Qed.
Time
Definition coPset_suffixes (p : positive) : coPset :=
  coPset_suffixes_raw p \226\134\190 coPset_suffixes_wf _.
Time
Lemma elem_coPset_suffixes p q : p \226\136\136 coPset_suffixes q \226\134\148 (\226\136\131 q', p = q' ++ q).
Time Proof.
Time (unfold elem_of, coPset_elem_of; simpl; split).
Time -
Time
(revert p; induction q; intros [?| ?| ]; simpl; rewrite ?coPset_elem_of_node;
  naive_solver).
Time -
Time by intros [q' ->]; induction q; simpl; rewrite ?coPset_elem_of_node.
Time Qed.
Time Lemma coPset_suffixes_infinite p : \194\172 set_finite (coPset_suffixes p).
Time Proof.
Time (rewrite coPset_finite_spec; simpl).
Time
(induction p; simpl; rewrite ?coPset_finite_node, ?andb_True; naive_solver).
Time Qed.
Time
Fixpoint coPset_l_raw (t : coPset_raw) : coPset_raw :=
  match t with
  | coPLeaf false => coPLeaf false
  | coPLeaf true => coPNode true (coPLeaf true) (coPLeaf false)
  | coPNode b l r => coPNode' b (coPset_l_raw l) (coPset_l_raw r)
  end.
Time
Fixpoint coPset_r_raw (t : coPset_raw) : coPset_raw :=
  match t with
  | coPLeaf false => coPLeaf false
  | coPLeaf true => coPNode false (coPLeaf false) (coPLeaf true)
  | coPNode b l r => coPNode' false (coPset_r_raw l) (coPset_r_raw r)
  end.
Time Lemma coPset_l_wf t : coPset_wf (coPset_l_raw t).
Time Proof.
Time (induction t as [[]| ]; simpl; auto).
Time Qed.
Time Lemma coPset_r_wf t : coPset_wf (coPset_r_raw t).
Time Proof.
Time (induction t as [[]| ]; simpl; auto).
Time Qed.
Time
Definition coPset_l (X : coPset) : coPset :=
  let (t, Ht) := X in coPset_l_raw t \226\134\190 coPset_l_wf _.
Time
Definition coPset_r (X : coPset) : coPset :=
  let (t, Ht) := X in coPset_r_raw t \226\134\190 coPset_r_wf _.
Time Lemma coPset_lr_disjoint X : coPset_l X \226\136\169 coPset_r X = \226\136\133.
Time Proof.
Time (apply elem_of_equiv_empty_L; intros p; apply Is_true_false).
Time
(destruct X as [t Ht]; simpl; clear Ht; rewrite coPset_elem_of_intersection).
Time
(revert p; induction t as [[]| []]; intros [?| ?| ]; simpl;
  rewrite ?coPset_elem_of_node; simpl;
  rewrite ?orb_true_l, ?orb_false_l, ?orb_true_r, ?orb_false_r; auto).
Time Qed.
Time Lemma coPset_lr_union X : coPset_l X \226\136\170 coPset_r X = X.
Time Proof.
Time (apply elem_of_equiv_L; intros p; apply eq_bool_prop_elim).
Time (destruct X as [t Ht]; simpl; clear Ht; rewrite coPset_elem_of_union).
Time
(revert p; induction t as [[]| []]; intros [?| ?| ]; simpl;
  rewrite ?coPset_elem_of_node; simpl;
  rewrite ?orb_true_l, ?orb_false_l, ?orb_true_r, ?orb_false_r; auto).
Time Qed.
Time Lemma coPset_l_finite X : set_finite (coPset_l X) \226\134\146 set_finite X.
Time Proof.
Time (rewrite !coPset_finite_spec; destruct X as [t Ht]; simpl; clear Ht).
Time
(induction t as [[]| ]; simpl; rewrite ?coPset_finite_node, ?andb_True; tauto).
Time Qed.
Time Lemma coPset_r_finite X : set_finite (coPset_r X) \226\134\146 set_finite X.
Time Proof.
Time (rewrite !coPset_finite_spec; destruct X as [t Ht]; simpl; clear Ht).
Time
(induction t as [[]| ]; simpl; rewrite ?coPset_finite_node, ?andb_True; tauto).
Time Qed.
Time
Lemma coPset_split (X : coPset) :
  \194\172 set_finite X
  \226\134\146 \226\136\131 X1 X2, X = X1 \226\136\170 X2 \226\136\167 X1 \226\136\169 X2 = \226\136\133 \226\136\167 \194\172 set_finite X1 \226\136\167 \194\172 set_finite X2.
Time Proof.
Time
(exists (coPset_l X),(coPset_r X); eauto  10
  using coPset_lr_union, coPset_lr_disjoint, coPset_l_finite, coPset_r_finite).
Time Qed.
