Time From stdpp Require Export sets.
Time From stdpp Require Export sets list.
Time From stdpp Require Import relations.
Time From stdpp Require Export numbers sets.
Time Set Default Proof Using "Type".
Time Record listset A := Listset {listset_car : list A}.
Time Arguments listset_car {_} _ : assert.
Time Arguments Listset {_} _ : assert.
Time Section listset.
Time Context {A : Type}.
Time #[global]
Instance listset_elem_of : (ElemOf A (listset A)) :=
 (\206\187 x l, x \226\136\136 listset_car l).
Time #[global]Instance listset_empty : (Empty (listset A)) := (Listset []).
Time #[global]
Instance listset_singleton : (Singleton A (listset A)) := (\206\187 x, Listset [x]).
Time #[global]
Instance listset_union : (Union (listset A)) :=
 (\206\187 l k, let (l') := l in let (k') := k in Listset (l' ++ k')).
Time #[global]Opaque listset_singleton listset_empty.
Time #[global]Instance listset_simple_set : (SemiSet A (listset A)).
Time Proof.
Time split.
Time -
Time by apply not_elem_of_nil.
Time -
Time by apply elem_of_list_singleton.
Time -
Time (intros [?] [?]).
Time (apply elem_of_app).
Time Set Default Proof Using "Type".
Time Record propset (A : Type) : Type := PropSet {propset_car : A \226\134\146 Prop}.
Time Qed.
Time Lemma listset_empty_alt X : X \226\137\161 \226\136\133 \226\134\148 listset_car X = [].
Time Proof.
Time (destruct X as [l]; split; [  | by intros; simplify_eq /= ]).
Time Add Printing Constructor propset.
Time Arguments PropSet {_} _ : assert.
Time Arguments propset_car {_} _ _ : assert.
Time
Notation "{[ x | P ]}" := (PropSet (\206\187 x, P))
  (at level 1, format "{[  x  |  P  ]}") : stdpp_scope.
Time
Instance propset_elem_of  {A}: (ElemOf A (propset A)) :=
 (\206\187 x X, propset_car X x).
Time Instance propset_top  {A}: (Top (propset A)) := {[ _ | True ]}.
Time Instance propset_empty  {A}: (Empty (propset A)) := {[ _ | False ]}.
Time
Instance propset_singleton  {A}: (Singleton A (propset A)) :=
 (\206\187 y, {[ x | y = x ]}).
Time
Instance propset_union  {A}: (Union (propset A)) :=
 (\206\187 X1 X2, {[ x | x \226\136\136 X1 \226\136\168 x \226\136\136 X2 ]}).
Time (rewrite elem_of_equiv_empty; intros Hl).
Time Set Default Proof Using "Type*".
Time Instance set_size  `{Elements A C}: (Size C) := (length \226\136\152 elements).
Time
Definition set_fold `{Elements A C} {B} (f : A \226\134\146 B \226\134\146 B) 
  (b : B) : C \226\134\146 B := foldr f b \226\136\152 elements.
Time
Instance propset_intersection  {A}: (Intersection (propset A)) :=
 (\206\187 X1 X2, {[ x | x \226\136\136 X1 \226\136\167 x \226\136\136 X2 ]}).
Time
Instance propset_difference  {A}: (Difference (propset A)) :=
 (\206\187 X1 X2, {[ x | x \226\136\136 X1 \226\136\167 x \226\136\137 X2 ]}).
Time Instance propset_set : (Set_ A (propset A)).
Time Proof.
Time (split; [ split |  |  ]; by repeat intro).
Time (destruct l as [| x l]; [ done |  ]).
Time feed inversion Hl x.
Time left.
Time Qed.
Time
Instance set_filter  `{Elements A C} `{Empty C} `{Singleton A C} 
 `{Union C}: (Filter A C) := (\206\187 P _ X, list_to_set (filter P (elements X))).
Time Typeclasses Opaque set_filter.
Time Qed.
Time #[global]
Instance listset_empty_dec  (X : listset A): (Decision (X \226\137\161 \226\136\133)).
Time Proof.
Time
(refine (cast_if (decide (listset_car X = []))); abstract by
  rewrite listset_empty_alt).
Time
Definition set_map `{Elements A C} `{Singleton B D} 
  `{Empty D} `{Union D} (f : A \226\134\146 B) (X : C) : D :=
  list_to_set (f <$> elements X).
Time Typeclasses Opaque set_map.
Time Lemma elem_of_top {A} (x : A) : x \226\136\136 (\226\138\164 : propset A) \226\134\148 True.
Time Proof.
Time done.
Time Qed.
Time Lemma elem_of_PropSet {A} (P : A \226\134\146 Prop) x : x \226\136\136 {[ x | P x ]} \226\134\148 P x.
Time Proof.
Time done.
Time Qed.
Time Defined.
Time Context `{Aeq : !EqDecision A}.
Time #[global]Instance listset_elem_of_dec : (RelDecision (\226\136\136@{listset A} )).
Time Proof  using (Aeq).
Time (refine (\206\187 x X, cast_if (decide (x \226\136\136 listset_car X))); done).
Time
Instance set_fresh  `{Elements A C} `{Fresh A (list A)}: 
 (Fresh A C) := (fresh \226\136\152 elements).
Time Typeclasses Opaque set_filter.
Time
Lemma not_elem_of_PropSet {A} (P : A \226\134\146 Prop) x : x \226\136\137 {[ x | P x ]} \226\134\148 \194\172 P x.
Time Proof.
Time done.
Time Qed.
Time Lemma top_subseteq {A} (X : propset A) : X \226\138\134 \226\138\164.
Time Proof.
Time done.
Time Defined.
Time #[global]
Instance listset_intersection : (Intersection (listset A)) :=
 (\206\187 l k, let (l') := l in let (k') := k in Listset (list_intersection l' k')).
Time #[global]
Instance listset_difference : (Difference (listset A)) :=
 (\206\187 l k, let (l') := l in let (k') := k in Listset (list_difference l' k')).
Time Instance listset_set : (Set_ A (listset A)).
Time Proof.
Time split.
Time -
Time (apply _).
Time -
Time
Fixpoint fresh_list `{Fresh A C} `{Union C} `{Singleton A C} 
(n : nat) (X : C) : list A :=
  match n with
  | 0 => []
  | S n => let x := fresh X in x :: fresh_list n ({[x]} \226\136\170 X)
  end.
Time Instance: (Params (@fresh_list) 6) := { }.
Time
Inductive Forall_fresh `{ElemOf A C} (X : C) : list A \226\134\146 Prop :=
  | Forall_fresh_nil : Forall_fresh X []
  | Forall_fresh_cons :
      forall x xs,
      x \226\136\137 xs \226\134\146 x \226\136\137 X \226\134\146 Forall_fresh X xs \226\134\146 Forall_fresh X (x :: xs).
Time (intros [?] [?]).
Time (apply elem_of_list_intersection).
Time -
Time (intros [?] [?]).
Time (apply elem_of_list_difference).
Time Qed.
Time #[global]
Instance listset_elements : (Elements A (listset A)) :=
 (remove_dups \226\136\152 listset_car).
Time Section fin_set.
Time Context `{FinSet A C}.
Time Implicit Types X Y : C.
Time Lemma fin_set_finite X : set_finite X.
Time Proof.
Time by exists (elements X); intros; rewrite elem_of_elements.
Time Qed.
Time Hint Resolve top_subseteq: core.
Time
Definition set_to_propset `{ElemOf A C} (X : C) : 
  propset A := {[ x | x \226\136\136 X ]}.
Time
Lemma elem_of_set_to_propset `{SemiSet A C} x (X : C) :
  x \226\136\136 set_to_propset X \226\134\148 x \226\136\136 X.
Time #[global]Instance listset_fin_set : (FinSet A (listset A)).
Time Proof.
Time split.
Time -
Time (apply _).
Time -
Time (intros).
Time (apply elem_of_remove_dups).
Time -
Time (intros).
Time (apply NoDup_remove_dups).
Time Qed.
Time Qed.
Time Instance elem_of_dec_slow : (RelDecision (\226\136\136@{C} )) |100.
Time Proof.
Time
(refine (\206\187 x X, cast_if (decide_rel (\226\136\136) x (elements X))); by
  rewrite <- (elem_of_elements _)).
Time Proof.
Time done.
Time Qed.
Time Instance propset_ret : (MRet propset) := (\206\187 A (x : A), {[x]}).
Time
Instance propset_bind : (MBind propset) :=
 (\206\187 A B (f : A \226\134\146 propset B) (X : propset A),
    PropSet (\206\187 b, \226\136\131 a, b \226\136\136 f a \226\136\167 a \226\136\136 X)).
Time End listset.
Time Instance listset_ret : (MRet listset) := (\206\187 A x, {[x]}).
Time
Instance propset_fmap : (FMap propset) :=
 (\206\187 A B (f : A \226\134\146 B) (X : propset A), {[ b | \226\136\131 a, b = f a \226\136\167 a \226\136\136 X ]}).
Time
Instance propset_join : (MJoin propset) :=
 (\206\187 A (XX : propset (propset A)), {[ a | \226\136\131 X : propset A, a \226\136\136 X \226\136\167 X \226\136\136 XX ]}).
Time Instance propset_monad_set : (MonadSet propset).
Time Proof.
Time by split; try apply _.
Time
Instance listset_fmap : (FMap listset) :=
 (\206\187 A B f l, let (l') := l in Listset (f <$> l')).
Time
Instance listset_bind : (MBind listset) :=
 (\206\187 A B f l, let (l') := l in Listset (mbind (listset_car \226\136\152 f) l')).
Time Defined.
Time #[global]
Instance set_unfold_elements  X x P:
 (SetUnfoldElemOf x X P \226\134\146 SetUnfoldElemOf x (elements X) P).
Time Proof.
Time constructor.
Time by rewrite elem_of_elements, (set_unfold_elem_of x X P).
Time Instance listset_join : (MJoin listset) := (\206\187 A, mbind id).
Time Instance listset_set_monad : (MonadSet listset).
Time Proof.
Time split.
Time -
Time (intros).
Time (apply _).
Time -
Time (intros ? ? ? [?] ?).
Time (apply elem_of_list_bind).
Time Qed.
Time #[global]
Instance elements_proper : (Proper ((\226\137\161) ==> (\226\137\161\226\130\154)) (elements (C:=C))).
Time Qed.
Time
Instance set_unfold_propset_top  {A} (x : A):
 (SetUnfoldElemOf x (\226\138\164 : propset A) True).
Time Proof.
Time by constructor.
Time Qed.
Time -
Time (intros).
Time (apply elem_of_list_ret).
Time -
Time (intros ? ? ? [?]).
Time (apply elem_of_list_fmap).
Time -
Time (intros ? [?] ?).
Time (unfold mjoin, listset_join, elem_of, listset_elem_of).
Time (simpl).
Time by rewrite elem_of_list_bind.
Time Proof.
Time (intros ? ? E).
Time (apply NoDup_Permutation).
Time -
Time (apply NoDup_elements).
Time -
Time (apply NoDup_elements).
Time -
Time (intros).
Time by rewrite !elem_of_elements, E.
Time
Instance set_unfold_PropSet  {A} (P : A \226\134\146 Prop) x 
 Q: (SetUnfoldSimpl (P x) Q \226\134\146 SetUnfoldElemOf x (PropSet P) Q).
Time Proof.
Time (intros HPQ).
Time constructor.
Time (apply HPQ).
Time Qed.
Time #[global]
Opaque propset_elem_of propset_top propset_empty propset_singleton.
Time #[global]Opaque propset_union propset_intersection propset_difference.
Time #[global]Opaque propset_ret propset_bind propset_fmap propset_join.
Time Qed.
Time Qed.
Time Lemma elements_empty : elements (\226\136\133 : C) = [].
Time Proof.
Time (apply elem_of_nil_inv; intros x).
Time (rewrite elem_of_elements, elem_of_empty; tauto).
Time Qed.
Time Lemma elements_empty_inv X : elements X = [] \226\134\146 X \226\137\161 \226\136\133.
Time Proof.
Time (intros HX; apply elem_of_equiv_empty; intros x).
Time (rewrite <- elem_of_elements, HX, elem_of_nil).
Time tauto.
Time Qed.
Time Lemma elements_empty' X : elements X = [] \226\134\148 X \226\137\161 \226\136\133.
Time Proof.
Time (split; intros HX; [ by apply elements_empty_inv |  ]).
Time by rewrite <- Permutation_nil, HX, elements_empty.
Time Qed.
Time
Lemma elements_union_singleton (X : C) x :
  x \226\136\137 X \226\134\146 elements ({[x]} \226\136\170 X) \226\137\161\226\130\154 x :: elements X.
Time Proof.
Time (intros ?; apply NoDup_Permutation).
Time {
Time (apply NoDup_elements).
Time }
Time {
Time by constructor; rewrite ?elem_of_elements; try apply NoDup_elements.
Time }
Time (intros y; rewrite elem_of_elements, elem_of_union, elem_of_singleton).
Time by rewrite elem_of_cons, elem_of_elements.
Time Qed.
Time Lemma elements_singleton x : elements ({[x]} : C) = [x].
Time Proof.
Time (apply Permutation_singleton).
Time
by
 rewrite <- (right_id \226\136\133 (\226\136\170) {[x]}), elements_union_singleton, elements_empty
  by set_solver.
Time Qed.
Time
Lemma elements_disj_union (X Y : C) :
  X ## Y \226\134\146 elements (X \226\136\170 Y) \226\137\161\226\130\154 elements X ++ elements Y.
Time Proof.
Time (intros HXY).
Time (apply NoDup_Permutation).
Time -
Time (apply NoDup_elements).
Time -
Time (apply NoDup_app).
Time set_solver by eauto using NoDup_elements.
Time -
Time set_solver.
Time Qed.
Time Lemma elements_submseteq X Y : X \226\138\134 Y \226\134\146 elements X \226\138\134+ elements Y.
Time Proof.
Time (intros; apply NoDup_submseteq; eauto using NoDup_elements).
Time (intros x).
Time (rewrite !elem_of_elements; auto).
Time Qed.
Time #[global]Instance set_size_proper : (Proper ((\226\137\161) ==> (=)) (@size C _)).
Time Proof.
Time (intros ? ? E).
Time (apply Permutation_length).
Time by rewrite E.
Time Qed.
Time Lemma size_empty : size (\226\136\133 : C) = 0.
Time Proof.
Time (unfold size, set_size).
Time (simpl).
Time by rewrite elements_empty.
Time Qed.
Time Lemma size_empty_inv (X : C) : size X = 0 \226\134\146 X \226\137\161 \226\136\133.
Time Proof.
Time (intros; apply equiv_empty; intros x; rewrite <- elem_of_elements).
Time by rewrite (nil_length_inv (elements X)), ?elem_of_nil.
Time Qed.
Time Lemma size_empty_iff (X : C) : size X = 0 \226\134\148 X \226\137\161 \226\136\133.
Time Proof.
Time split.
Time (apply size_empty_inv).
Time by intros ->; rewrite size_empty.
Time Qed.
Time Lemma size_non_empty_iff (X : C) : size X \226\137\160 0 \226\134\148 X \226\137\162 \226\136\133.
Time Proof.
Time by rewrite size_empty_iff.
Time Qed.
Time Lemma set_choose_or_empty X : (\226\136\131 x, x \226\136\136 X) \226\136\168 X \226\137\161 \226\136\133.
Time Proof.
Time (destruct (elements X) as [| x l] eqn:HX; [ right | left ]).
Time -
Time (apply equiv_empty; intros x).
Time by rewrite <- elem_of_elements, HX, elem_of_nil.
Time -
Time exists x.
Time (rewrite <- elem_of_elements, HX).
Time by left.
Time Qed.
Time Lemma set_choose X : X \226\137\162 \226\136\133 \226\134\146 \226\136\131 x, x \226\136\136 X.
Time Proof.
Time (intros).
Time by destruct (set_choose_or_empty X).
Time Qed.
Time Lemma set_choose_L `{!LeibnizEquiv C} X : X \226\137\160 \226\136\133 \226\134\146 \226\136\131 x, x \226\136\136 X.
Time Proof.
Time unfold_leibniz.
Time (apply set_choose).
Time Qed.
Time Lemma size_pos_elem_of X : 0 < size X \226\134\146 \226\136\131 x, x \226\136\136 X.
Time Proof.
Time (intros Hsz).
Time (destruct (set_choose_or_empty X) as [| HX]; [ done |  ]).
Time (contradict Hsz).
Time (rewrite HX, size_empty; lia).
Time Qed.
Time Lemma size_singleton (x : A) : size ({[x]} : C) = 1.
Time Proof.
Time (unfold size, set_size).
Time (simpl).
Time by rewrite elements_singleton.
Time Qed.
Time Lemma size_singleton_inv X x y : size X = 1 \226\134\146 x \226\136\136 X \226\134\146 y \226\136\136 X \226\134\146 x = y.
Time Proof.
Time (unfold size, set_size).
Time (simpl).
Time (rewrite <- !elem_of_elements).
Time (generalize (elements X)).
Time (intros [| ? l]; intro; simplify_eq /=).
Time
(rewrite (nil_length_inv l), !elem_of_list_singleton by done; congruence).
Time Qed.
Time Lemma size_1_elem_of X : size X = 1 \226\134\146 \226\136\131 x, X \226\137\161 {[x]}.
Time Proof.
Time (intros E).
Time (destruct (size_pos_elem_of X); auto with lia).
Time exists x.
Time (apply elem_of_equiv).
Time split.
Time -
Time (rewrite elem_of_singleton).
Time eauto using size_singleton_inv.
Time -
Time set_solver.
Time Qed.
Time Lemma size_union X Y : X ## Y \226\134\146 size (X \226\136\170 Y) = size X + size Y.
Time Proof.
Time (intros).
Time (unfold size, set_size).
Time (simpl).
Time (rewrite <- app_length).
Time (apply Permutation_length, NoDup_Permutation).
Time -
Time (apply NoDup_elements).
Time -
Time (apply NoDup_app; repeat split; try apply NoDup_elements).
Time (intros x; rewrite !elem_of_elements; set_solver).
Time -
Time (intros).
Time by rewrite elem_of_app, !elem_of_elements, elem_of_union.
Time Qed.
Time Lemma size_union_alt X Y : size (X \226\136\170 Y) = size X + size (Y \226\136\150 X).
Time Proof.
Time (rewrite <- size_union by set_solver).
Time setoid_replace Y \226\136\150 X with (Y \226\136\170 X) \226\136\150 X by set_solver.
Time (rewrite <- union_difference, (comm (\226\136\170)); set_solver).
Time Qed.
Time Lemma subseteq_size X Y : X \226\138\134 Y \226\134\146 size X \226\137\164 size Y.
Time Proof.
Time (intros).
Time (rewrite (union_difference X Y), size_union_alt by done).
Time lia.
Time Qed.
Time Lemma subset_size X Y : X \226\138\130 Y \226\134\146 size X < size Y.
Time Proof.
Time (intros).
Time (rewrite (union_difference X Y) by set_solver).
Time (rewrite size_union_alt, difference_twice).
Time (cut (size (Y \226\136\150 X) \226\137\160 0); [ lia |  ]).
Time by apply size_non_empty_iff, non_empty_difference.
Time Qed.
Time Lemma set_wf : wf (\226\138\130@{C} ).
Time Proof.
Time (apply (wf_projected (<) size); auto using subset_size, lt_wf).
Time Qed.
Time
Lemma set_ind (P : C \226\134\146 Prop) :
  Proper ((\226\137\161) ==> iff) P
  \226\134\146 P \226\136\133 \226\134\146 (\226\136\128 x X, x \226\136\137 X \226\134\146 P X \226\134\146 P ({[x]} \226\136\170 X)) \226\134\146 \226\136\128 X, P X.
Time Proof.
Time (intros ? Hemp Hadd).
Time (apply well_founded_induction with (\226\138\130)).
Time {
Time (apply set_wf).
Time }
Time (intros X IH).
Time (destruct (set_choose_or_empty X) as [[x ?]| HX]).
Time -
Time (rewrite (union_difference {[x]} X) by set_solver).
Time (apply Hadd).
Time set_solver.
Time (apply IH; set_solver).
Time -
Time by rewrite HX.
Time Qed.
Time
Lemma set_ind_L `{!LeibnizEquiv C} (P : C \226\134\146 Prop) :
  P \226\136\133 \226\134\146 (\226\136\128 x X, x \226\136\137 X \226\134\146 P X \226\134\146 P ({[x]} \226\136\170 X)) \226\134\146 \226\136\128 X, P X.
Time Proof.
Time (apply set_ind).
Time by intros ? ? ->%leibniz_equiv_iff.
Time Qed.
Time
Lemma set_fold_ind {B} (P : B \226\134\146 C \226\134\146 Prop) (f : A \226\134\146 B \226\134\146 B) 
  (b : B) :
  Proper ((=) ==> (\226\137\161) ==> iff) P
  \226\134\146 P b \226\136\133
    \226\134\146 (\226\136\128 x X r, x \226\136\137 X \226\134\146 P r X \226\134\146 P (f x r) ({[x]} \226\136\170 X))
      \226\134\146 \226\136\128 X, P (set_fold f b X) X.
Time Proof.
Time (intros ? Hemp Hadd).
Time (cut (\226\136\128 l, NoDup l \226\134\146 \226\136\128 X, (\226\136\128 x, x \226\136\136 X \226\134\148 x \226\136\136 l) \226\134\146 P (foldr f b l) X)).
Time {
Time (intros help ?).
Time (apply help; [ apply NoDup_elements |  ]).
Time symmetry.
Time (apply elem_of_elements).
Time }
Time (induction 1 as [| x l ? ? IH]; simpl).
Time -
Time (intros X HX).
Time setoid_rewrite elem_of_nil in HX.
Time (rewrite equiv_empty).
Time done.
Time set_solver.
Time -
Time (intros X HX).
Time setoid_rewrite elem_of_cons in HX.
Time (rewrite (union_difference {[x]} X) by set_solver).
Time (apply Hadd).
Time set_solver.
Time (apply IH).
Time set_solver.
Time Qed.
Time
Lemma set_fold_ind_L `{!LeibnizEquiv C} {B} (P : B \226\134\146 C \226\134\146 Prop)
  (f : A \226\134\146 B \226\134\146 B) (b : B) :
  P b \226\136\133
  \226\134\146 (\226\136\128 x X r, x \226\136\137 X \226\134\146 P r X \226\134\146 P (f x r) ({[x]} \226\136\170 X))
    \226\134\146 \226\136\128 X, P (set_fold f b X) X.
Time Proof.
Time (apply set_fold_ind).
Time by intros ? ? -> ? ? ->%leibniz_equiv.
Time Qed.
Time
Lemma set_fold_proper {B} (R : relation B) `{!Equivalence R} 
  (f : A \226\134\146 B \226\134\146 B) (b : B) `{!Proper ((=) ==> R ==> R) f}
  (Hf : \226\136\128 a1 a2 b, R (f a1 (f a2 b)) (f a2 (f a1 b))) :
  Proper ((\226\137\161) ==> R) (set_fold f b : C \226\134\146 B).
Time Proof.
Time (intros ? ? E).
Time (apply (foldr_permutation R f b); auto).
Time by rewrite E.
Time Qed.
Time
Lemma set_fold_empty {B} (f : A \226\134\146 B \226\134\146 B) (b : B) : set_fold f b (\226\136\133 : C) = b.
Time Proof.
Time by unfold set_fold; simpl; rewrite elements_empty.
Time Qed.
Time
Lemma set_fold_singleton {B} (f : A \226\134\146 B \226\134\146 B) (b : B) 
  (a : A) : set_fold f b ({[a]} : C) = f a b.
Time Proof.
Time by unfold set_fold; simpl; rewrite elements_singleton.
Time Qed.
Time
Lemma set_fold_disj_union (f : A \226\134\146 A \226\134\146 A) (b : A) 
  X Y :
  Comm (=) f
  \226\134\146 Assoc (=) f
    \226\134\146 X ## Y \226\134\146 set_fold f b (X \226\136\170 Y) = set_fold f (set_fold f b X) Y.
Time Proof.
Time (intros Hcomm Hassoc Hdisj).
Time (unfold set_fold; simpl).
Time by rewrite elements_disj_union, <- foldr_app, (comm (++)).
Time Qed.
Time
Lemma minimal_exists R `{!Transitive R} `{\226\136\128 x y, Decision (R x y)} 
  (X : C) : X \226\137\162 \226\136\133 \226\134\146 \226\136\131 x, x \226\136\136 X \226\136\167 minimal R x X.
Time Proof.
Time (pattern X; apply set_ind; clear X).
Time {
Time by intros X X' HX; setoid_rewrite HX.
Time }
Time {
Time done.
Time }
Time (intros x X ? IH Hemp).
Time (destruct (set_choose_or_empty X) as [[z ?]| HX]).
Time {
Time (destruct IH as (x', (Hx', Hmin)); [ set_solver |  ]).
Time (destruct (decide (R x x'))).
Time -
Time (exists x; split; [ set_solver |  ]).
Time
eauto
 using (union_minimal (C:=C)), (singleton_minimal (C:=C)), minimal_weaken.
Time -
Time (exists x'; split; [ set_solver |  ]).
Time
eauto using (union_minimal (C:=C)), (singleton_minimal_not_above (C:=C)).
Time }
Time (exists x; split; [ set_solver |  ]).
Time (rewrite HX, (right_id _ (\226\136\170))).
Time (apply singleton_minimal).
Time Qed.
Time
Lemma minimal_exists_L R `{!LeibnizEquiv C} `{!Transitive R}
  `{\226\136\128 x y, Decision (R x y)} (X : C) : X \226\137\160 \226\136\133 \226\134\146 \226\136\131 x, x \226\136\136 X \226\136\167 minimal R x X.
Time Proof.
Time unfold_leibniz.
Time (apply (minimal_exists R)).
Time Qed.
Time Section filter.
Time Context (P : A \226\134\146 Prop) `{!\226\136\128 x, Decision (P x)}.
Time Lemma elem_of_filter X x : x \226\136\136 filter P X \226\134\148 P x \226\136\167 x \226\136\136 X.
Time Proof.
Time (unfold filter, set_filter).
Time by rewrite elem_of_list_to_set, elem_of_list_filter, elem_of_elements.
Time Qed.
Time #[global]
Instance set_unfold_filter  X Q:
 (SetUnfoldElemOf x X Q \226\134\146 SetUnfoldElemOf x (filter P X) (P x \226\136\167 Q)).
Time Proof.
Time (intros ? ?; constructor).
Time by rewrite elem_of_filter, (set_unfold_elem_of x X Q).
Time Qed.
Time Lemma filter_empty : filter P (\226\136\133 : C) \226\137\161 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma filter_union X Y : filter P (X \226\136\170 Y) \226\137\161 filter P X \226\136\170 filter P Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma filter_singleton x : P x \226\134\146 filter P ({[x]} : C) \226\137\161 {[x]}.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma filter_singleton_not x : \194\172 P x \226\134\146 filter P ({[x]} : C) \226\137\161 \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Section leibniz_equiv.
Time Context `{!LeibnizEquiv C}.
Time Lemma filter_empty_L : filter P (\226\136\133 : C) = \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma filter_union_L X Y : filter P (X \226\136\170 Y) = filter P X \226\136\170 filter P Y.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma filter_singleton_L x : P x \226\134\146 filter P ({[x]} : C) = {[x]}.
Time Proof.
Time set_solver.
Time Qed.
Time Lemma filter_singleton_not_L x : \194\172 P x \226\134\146 filter P ({[x]} : C) = \226\136\133.
Time Proof.
Time set_solver.
Time Qed.
Time End leibniz_equiv.
Time End filter.
Time Section map.
Time Context `{Set_ B D}.
Time
Lemma elem_of_map (f : A \226\134\146 B) (X : C) y :
  y \226\136\136 set_map (D:=D) f X \226\134\148 (\226\136\131 x, y = f x \226\136\167 x \226\136\136 X).
Time Proof.
Time (unfold set_map).
Time (rewrite elem_of_list_to_set, elem_of_list_fmap).
Time by setoid_rewrite elem_of_elements.
Time Qed.
Time #[global]
Instance set_unfold_map  (f : A \226\134\146 B) (X : C) (P : A \226\134\146 Prop):
 ((\226\136\128 y, SetUnfoldElemOf y X (P y))
  \226\134\146 SetUnfoldElemOf x (set_map (D:=D) f X) (\226\136\131 y, x = f y \226\136\167 P y)).
Time Proof.
Time constructor.
Time (rewrite elem_of_map; naive_solver).
Time Qed.
Time #[global]
Instance set_map_proper :
 (Proper (pointwise_relation _ (=) ==> (\226\137\161) ==> (\226\137\161)) (set_map (C:=C) (D:=D))).
Time Proof.
Time (intros f g ? X Y).
Time (set_unfold; naive_solver).
Time Qed.
Time #[global]
Instance set_map_mono :
 (Proper (pointwise_relation _ (=) ==> (\226\138\134) ==> (\226\138\134)) (set_map (C:=C) (D:=D))).
Time Proof.
Time (intros f g ? X Y).
Time (set_unfold; naive_solver).
Time Qed.
Time
Lemma elem_of_map_1 (f : A \226\134\146 B) (X : C) (y : B) :
  y \226\136\136 set_map (D:=D) f X \226\134\146 \226\136\131 x, y = f x \226\136\167 x \226\136\136 X.
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma elem_of_map_2 (f : A \226\134\146 B) (X : C) (x : A) :
  x \226\136\136 X \226\134\146 f x \226\136\136 set_map (D:=D) f X.
Time Proof.
Time set_solver.
Time Qed.
Time
Lemma elem_of_map_2_alt (f : A \226\134\146 B) (X : C) (x : A) 
  (y : B) : x \226\136\136 X \226\134\146 y = f x \226\134\146 y \226\136\136 set_map (D:=D) f X.
Time Proof.
Time set_solver.
Time Qed.
Time End map.
Time Lemma set_Forall_elements P X : set_Forall P X \226\134\148 Forall P (elements X).
Time Proof.
Time (rewrite Forall_forall).
Time by setoid_rewrite elem_of_elements.
Time Qed.
Time Lemma set_Exists_elements P X : set_Exists P X \226\134\148 Exists P (elements X).
Time Proof.
Time (rewrite Exists_exists).
Time by setoid_rewrite elem_of_elements.
Time Qed.
Time
Lemma set_Forall_Exists_dec (P Q : A \226\134\146 Prop) (dec : \226\136\128 x, {P x} + {Q x}) 
  X : {set_Forall P X} + {set_Exists Q X}.
Time Proof.
Time
(refine (cast_if (Forall_Exists_dec P Q dec (elements X)));
  [ by apply set_Forall_elements | by apply set_Exists_elements ]).
Time Defined.
Time
Lemma not_set_Forall_Exists P `{dec : \226\136\128 x, Decision (P x)} 
  X : \194\172 set_Forall P X \226\134\146 set_Exists (not \226\136\152 P) X.
Time Proof.
Time intro.
Time by destruct (set_Forall_Exists_dec P (not \226\136\152 P) dec X).
Time Qed.
Time
Lemma not_set_Exists_Forall P `{dec : \226\136\128 x, Decision (P x)} 
  X : \194\172 set_Exists P X \226\134\146 set_Forall (not \226\136\152 P) X.
Time Proof.
Time
by
 destruct (set_Forall_Exists_dec (not \226\136\152 P) P (\206\187 x, swap_if (decide (P x))) X).
Time Qed.
Time #[global]
Instance set_Forall_dec  (P : A \226\134\146 Prop) `{\226\136\128 x, Decision (P x)} 
 X: (Decision (set_Forall P X)) |100.
Time Proof.
Time
(refine (cast_if (decide (Forall P (elements X)))); by
  rewrite set_Forall_elements).
Time Defined.
Time #[global]
Instance set_Exists_dec  `(P : A \226\134\146 Prop) `{\226\136\128 x, Decision (P x)} 
 X: (Decision (set_Exists P X)) |100.
Time Proof.
Time
(refine (cast_if (decide (Exists P (elements X)))); by
  rewrite set_Exists_elements).
Time Defined.
Time
Lemma pred_finite_set (P : A \226\134\146 Prop) :
  pred_finite P \226\134\148 (\226\136\131 X : C, \226\136\128 x, P x \226\134\146 x \226\136\136 X).
Time Proof.
Time split.
Time -
Time (intros [xs Hfin]).
Time exists (list_to_set xs).
Time set_solver.
Time -
Time (intros [X Hfin]).
Time exists (elements X).
Time set_solver.
Time Qed.
Time
Lemma pred_infinite_set (P : A \226\134\146 Prop) :
  pred_infinite P \226\134\148 (\226\136\128 X : C, \226\136\131 x, P x \226\136\167 x \226\136\137 X).
Time Proof.
Time split.
Time -
Time (intros Hinf X).
Time (destruct (Hinf (elements X))).
Time set_solver.
Time -
Time (intros Hinf xs).
Time (destruct (Hinf (list_to_set xs))).
Time set_solver.
Time Qed.
Time Section infinite.
Time Context `{Infinite A}.
Time #[global]Instance fresh_proper : (Proper ((\226\137\161@{C} ) ==> (=)) fresh).
Time Proof.
Time (unfold fresh, set_fresh).
Time solve_proper.
Time Qed.
Time Lemma is_fresh X : fresh X \226\136\137 X.
Time Proof.
Time (unfold fresh, set_fresh).
Time (rewrite <- elem_of_elements).
Time (apply infinite_is_fresh).
Time Qed.
Time Lemma exist_fresh X : \226\136\131 x, x \226\136\137 X.
Time Proof.
Time exists (fresh X).
Time (apply is_fresh).
Time Qed.
Time #[global]
Instance fresh_list_proper  n: (Proper ((\226\137\161@{C} ) ==> (=)) (fresh_list n)).
Time Proof.
Time (induction n as [| n IH]; intros ? ? E; by setoid_subst).
Time Qed.
Time Lemma Forall_fresh_NoDup X xs : Forall_fresh X xs \226\134\146 NoDup xs.
Time Proof.
Time (induction 1; by constructor).
Time Qed.
Time Lemma Forall_fresh_elem_of X xs x : Forall_fresh X xs \226\134\146 x \226\136\136 xs \226\134\146 x \226\136\137 X.
Time Proof.
Time (intros HX; revert x; rewrite <- Forall_forall).
Time by induction HX; constructor.
Time Qed.
Time
Lemma Forall_fresh_alt X xs :
  Forall_fresh X xs \226\134\148 NoDup xs \226\136\167 (\226\136\128 x, x \226\136\136 xs \226\134\146 x \226\136\137 X).
Time Proof.
Time (split; eauto using Forall_fresh_NoDup, Forall_fresh_elem_of).
Time (rewrite <- Forall_forall).
Time (intros [Hxs Hxs']).
Time (induction Hxs; decompose_Forall_hyps; constructor; auto).
Time Qed.
Time
Lemma Forall_fresh_subseteq X Y xs :
  Forall_fresh X xs \226\134\146 Y \226\138\134 X \226\134\146 Forall_fresh Y xs.
Time Proof.
Time (rewrite !Forall_fresh_alt; set_solver).
Time Qed.
Time Lemma fresh_list_length n X : length (fresh_list n X) = n.
Time Proof.
Time revert X.
Time (induction n; simpl; auto).
Time Qed.
Time Lemma fresh_list_is_fresh n X x : x \226\136\136 fresh_list n X \226\134\146 x \226\136\137 X.
Time Proof.
Time revert X.
Time
(induction n as [| n IH]; intros X; simpl; [ by rewrite elem_of_nil |  ]).
Time (rewrite elem_of_cons; intros [->| Hin]; [ apply is_fresh |  ]).
Time (apply IH in Hin; set_solver).
Time Qed.
Time Lemma NoDup_fresh_list n X : NoDup (fresh_list n X).
Time Proof.
Time revert X.
Time (induction n; simpl; constructor; auto).
Time (intros Hin; apply fresh_list_is_fresh in Hin; set_solver).
Time Qed.
Time Lemma Forall_fresh_list X n : Forall_fresh X (fresh_list n X).
Time Proof.
Time
(rewrite Forall_fresh_alt; eauto using NoDup_fresh_list, fresh_list_is_fresh).
Time Qed.
Time End infinite.
Time End fin_set.
