Time From stdpp Require Import gmap.
Time Set Default Proof Using "Type".
Time
Record gmultiset A `{Countable A} := GMultiSet {gmultiset_car : gmap A nat}.
Time Arguments GMultiSet {_} {_} {_} _ : assert.
Time Arguments gmultiset_car {_} {_} {_} _ : assert.
Time Instance gmultiset_eq_dec  `{Countable A}: (EqDecision (gmultiset A)).
Time Proof.
Time solve_decision.
Time Defined.
Time #[program]
Instance gmultiset_countable  `{Countable A}: (Countable (gmultiset A)) :=
 {|
 encode := fun X => encode (gmultiset_car X);
 decode := fun p => GMultiSet <$> decode p |}.
Time Next Obligation.
Time (intros A ? ? [X]; simpl).
Time by rewrite decode_encode.
Time Qed.
Time Section definitions.
Time Context `{Countable A}.
Time
Definition multiplicity (x : A) (X : gmultiset A) : nat :=
  match gmultiset_car X !! x with
  | Some n => S n
  | None => 0
  end.
Time #[global]
Instance gmultiset_elem_of : (ElemOf A (gmultiset A)) :=
 (\206\187 x X, 0 < multiplicity x X).
Time #[global]
Instance gmultiset_subseteq : (SubsetEq (gmultiset A)) :=
 (\206\187 X Y, \226\136\128 x, multiplicity x X \226\137\164 multiplicity x Y).
Time #[global]
Instance gmultiset_equiv : (Equiv (gmultiset A)) :=
 (\206\187 X Y, \226\136\128 x, multiplicity x X = multiplicity x Y).
Time #[global]
Instance gmultiset_elements : (Elements A (gmultiset A)) :=
 (\206\187 X, let (X) := X in ' '(x, n) \226\134\144 map_to_list X; replicate (S n) x).
Time #[global]
Instance gmultiset_size : (Size (gmultiset A)) := (length \226\136\152 elements).
Time #[global]
Instance gmultiset_empty : (Empty (gmultiset A)) := (GMultiSet \226\136\133).
Time #[global]
Instance gmultiset_singleton : (Singleton A (gmultiset A)) :=
 (\206\187 x, GMultiSet {[x := 0]}).
Time #[global]
Instance gmultiset_union : (Union (gmultiset A)) :=
 (\206\187 X Y,
    let (X) := X in
    let (Y) := Y in GMultiSet $ union_with (\206\187 x y, Some (x `max` y)) X Y).
Time #[global]
Instance gmultiset_intersection : (Intersection (gmultiset A)) :=
 (\206\187 X Y,
    let (X) := X in
    let (Y) := Y in
    GMultiSet $ intersection_with (\206\187 x y, Some (x `min` y)) X Y).
Time #[global]
Instance gmultiset_disj_union : (DisjUnion (gmultiset A)) :=
 (\206\187 X Y,
    let (X) := X in
    let (Y) := Y in GMultiSet $ union_with (\206\187 x y, Some (S (x + y))) X Y).
Time #[global]
Instance gmultiset_difference : (Difference (gmultiset A)) :=
 (\206\187 X Y,
    let (X) := X in
    let (Y) := Y in
    GMultiSet $
    difference_with (\206\187 x y, let z := x - y in guard 0 < z; Some (pred z)) X Y).
Time #[global]
Instance gmultiset_dom : (Dom (gmultiset A) (gset A)) :=
 (\206\187 X, let (X) := X in dom _ X).
Time End definitions.
Time Typeclasses Opaque gmultiset_elem_of gmultiset_subseteq.
Time Typeclasses Opaque gmultiset_elements gmultiset_size gmultiset_empty.
Time
Typeclasses Opaque gmultiset_singleton gmultiset_union gmultiset_difference.
Time Typeclasses Opaque gmultiset_dom.
Time Section lemmas.
Time Context `{Countable A}.
Time Implicit Types x y : A.
Time Implicit Types X Y : gmultiset A.
Time
Lemma gmultiset_eq X Y : X = Y \226\134\148 (\226\136\128 x, multiplicity x X = multiplicity x Y).
Time Proof.
Time (split; [ by intros -> | intros HXY ]).
Time (destruct X as [X], Y as [Y]; f_equal; apply map_eq; intros x).
Time (specialize (HXY x); unfold multiplicity in *; simpl in *).
Time (repeat case_match; naive_solver).
Time Qed.
Time #[global]Instance gmultiset_leibniz : (LeibnizEquiv (gmultiset A)).
Time Proof.
Time (intros X Y).
Time by rewrite gmultiset_eq.
Time Qed.
Time #[global]
Instance gmultiset_equiv_equivalence : (Equivalence (\226\137\161@{gmultiset A} )).
Time Proof.
Time (constructor; repeat intro; naive_solver).
Time Qed.
Time Lemma multiplicity_empty x : multiplicity x \226\136\133 = 0.
Time Proof.
Time done.
Time Qed.
Time Lemma multiplicity_singleton x : multiplicity x {[x]} = 1.
Time Proof.
Time (unfold multiplicity; simpl).
Time by rewrite lookup_singleton.
Time Qed.
Time Lemma multiplicity_singleton_ne x y : x \226\137\160 y \226\134\146 multiplicity x {[y]} = 0.
Time Proof.
Time (intros).
Time (unfold multiplicity; simpl).
Time by rewrite lookup_singleton_ne.
Time Qed.
Time
Lemma multiplicity_singleton' x y :
  multiplicity x {[y]} = (if decide (x = y) then 1 else 0).
Time Proof.
Time (destruct (decide _) as [->| ]).
Time -
Time by rewrite multiplicity_singleton.
Time -
Time by rewrite multiplicity_singleton_ne.
Time Qed.
Time
Lemma multiplicity_union X Y x :
  multiplicity x (X \226\136\170 Y) = multiplicity x X `max` multiplicity x Y.
Time Proof.
Time (destruct X as [X], Y as [Y]; unfold multiplicity; simpl).
Time (rewrite lookup_union_with).
Time (destruct (X !! _), (Y !! _); simpl; lia).
Time Qed.
Time
Lemma multiplicity_intersection X Y x :
  multiplicity x (X \226\136\169 Y) = multiplicity x X `min` multiplicity x Y.
Time Proof.
Time (destruct X as [X], Y as [Y]; unfold multiplicity; simpl).
Time (rewrite lookup_intersection_with).
Time (destruct (X !! _), (Y !! _); simpl; lia).
Time Qed.
Time
Lemma multiplicity_disj_union X Y x :
  multiplicity x (X \226\138\142 Y) = multiplicity x X + multiplicity x Y.
Time Proof.
Time (destruct X as [X], Y as [Y]; unfold multiplicity; simpl).
Time (rewrite lookup_union_with).
Time (destruct (X !! _), (Y !! _); simpl; lia).
Time Qed.
Time
Lemma multiplicity_difference X Y x :
  multiplicity x (X \226\136\150 Y) = multiplicity x X - multiplicity x Y.
Time Proof.
Time (destruct X as [X], Y as [Y]; unfold multiplicity; simpl).
Time (rewrite lookup_difference_with).
Time (destruct (X !! _), (Y !! _); simplify_option_eq; lia).
Time Qed.
Time Lemma elem_of_multiplicity x X : x \226\136\136 X \226\134\148 0 < multiplicity x X.
Time Proof.
Time done.
Time Qed.
Time #[global]Instance gmultiset_simple_set : (SemiSet A (gmultiset A)).
Time Proof.
Time split.
Time -
Time (intros x).
Time (rewrite elem_of_multiplicity, multiplicity_empty).
Time lia.
Time -
Time (intros x y).
Time (rewrite elem_of_multiplicity, multiplicity_singleton').
Time (destruct (decide (x = y)); intuition lia).
Time -
Time (intros X Y x).
Time (rewrite !elem_of_multiplicity, multiplicity_union).
Time lia.
Time Qed.
Time #[global]
Instance gmultiset_elem_of_dec : (RelDecision (\226\136\136@{gmultiset A} )).
Time Proof.
Time (refine (\206\187 x X, cast_if (decide (0 < multiplicity x X))); done).
Time Defined.
Time Lemma gmultiset_elem_of_disj_union X Y x : x \226\136\136 X \226\138\142 Y \226\134\148 x \226\136\136 X \226\136\168 x \226\136\136 Y.
Time Proof.
Time (rewrite !elem_of_multiplicity, multiplicity_disj_union).
Time lia.
Time Qed.
Time #[global]
Instance set_unfold_gmultiset_disj_union  x X Y P 
 Q:
 (SetUnfoldElemOf x X P
  \226\134\146 SetUnfoldElemOf x Y Q \226\134\146 SetUnfoldElemOf x (X \226\138\142 Y) (P \226\136\168 Q)).
Time Proof.
Time (intros ? ?; constructor).
Time (rewrite gmultiset_elem_of_disj_union).
Time by rewrite <- (set_unfold_elem_of x X P), <- (set_unfold_elem_of x Y Q).
Time Qed.
Time #[global]Instance gmultiset_union_comm : (Comm (=@{gmultiset A} ) (\226\136\170)).
Time Proof.
Time (intros X Y).
Time (apply gmultiset_eq; intros x).
Time (rewrite !multiplicity_union; lia).
Time Qed.
Time #[global]
Instance gmultiset_union_assoc : (Assoc (=@{gmultiset A} ) (\226\136\170)).
Time Proof.
Time (intros X Y Z).
Time (apply gmultiset_eq; intros x).
Time (rewrite !multiplicity_union; lia).
Time Qed.
Time #[global]
Instance gmultiset_union_left_id : (LeftId (=@{gmultiset A} ) \226\136\133 (\226\136\170)).
Time Proof.
Time (intros X).
Time (apply gmultiset_eq; intros x).
Time by rewrite multiplicity_union, multiplicity_empty.
Time Qed.
Time #[global]
Instance gmultiset_union_right_id : (RightId (=@{gmultiset A} ) \226\136\133 (\226\136\170)).
Time Proof.
Time (intros X).
Time by rewrite (comm_L (\226\136\170)), (left_id_L _ _).
Time Qed.
Time #[global]
Instance gmultiset_union_idemp : (IdemP (=@{gmultiset A} ) (\226\136\170)).
Time Proof.
Time (intros X).
Time (apply gmultiset_eq; intros x).
Time (rewrite !multiplicity_union; lia).
Time Qed.
Time #[global]
Instance gmultiset_intersection_comm : (Comm (=@{gmultiset A} ) (\226\136\169)).
Time Proof.
Time (intros X Y).
Time (apply gmultiset_eq; intros x).
Time (rewrite !multiplicity_intersection; lia).
Time Qed.
Time #[global]
Instance gmultiset_intersection_assoc : (Assoc (=@{gmultiset A} ) (\226\136\169)).
Time Proof.
Time (intros X Y Z).
Time (apply gmultiset_eq; intros x).
Time (rewrite !multiplicity_intersection; lia).
Time Qed.
Time #[global]
Instance gmultiset_intersection_left_absorb :
 (LeftAbsorb (=@{gmultiset A} ) \226\136\133 (\226\136\169)).
Time Proof.
Time (intros X).
Time (apply gmultiset_eq; intros x).
Time by rewrite multiplicity_intersection, multiplicity_empty.
Time Qed.
Time #[global]
Instance gmultiset_intersection_right_absorb :
 (RightAbsorb (=@{gmultiset A} ) \226\136\133 (\226\136\169)).
Time Proof.
Time (intros X).
Time by rewrite (comm_L (\226\136\169)), (left_absorb_L _ _).
Time Qed.
Time #[global]
Instance gmultiset_intersection_idemp : (IdemP (=@{gmultiset A} ) (\226\136\169)).
Time Proof.
Time (intros X).
Time (apply gmultiset_eq; intros x).
Time (rewrite !multiplicity_intersection; lia).
Time Qed.
Time
Lemma gmultiset_union_intersection_l X Y Z : X \226\136\170 Y \226\136\169 Z = (X \226\136\170 Y) \226\136\169 (X \226\136\170 Z).
Time Proof.
Time (apply gmultiset_eq; intros y).
Time
(rewrite multiplicity_union, !multiplicity_intersection, !multiplicity_union).
Time lia.
Time Qed.
Time
Lemma gmultiset_union_intersection_r X Y Z : X \226\136\169 Y \226\136\170 Z = (X \226\136\170 Z) \226\136\169 (Y \226\136\170 Z).
Time Proof.
Time by rewrite <- !(comm_L _ Z), gmultiset_union_intersection_l.
Time Qed.
Time
Lemma gmultiset_intersection_union_l X Y Z : X \226\136\169 (Y \226\136\170 Z) = X \226\136\169 Y \226\136\170 X \226\136\169 Z.
Time Proof.
Time (apply gmultiset_eq; intros y).
Time
(rewrite multiplicity_union, !multiplicity_intersection, !multiplicity_union).
Time lia.
Time Qed.
Time
Lemma gmultiset_intersection_union_r X Y Z : (X \226\136\170 Y) \226\136\169 Z = X \226\136\169 Z \226\136\170 Y \226\136\169 Z.
Time Proof.
Time by rewrite <- !(comm_L _ Z), gmultiset_intersection_union_l.
Time Qed.
Time #[global]
Instance gmultiset_disj_union_comm : (Comm (=@{gmultiset A} ) (\226\138\142)).
Time Proof.
Time (intros X Y).
Time (apply gmultiset_eq; intros x).
Time (rewrite !multiplicity_disj_union; lia).
Time Qed.
Time #[global]
Instance gmultiset_disj_union_assoc : (Assoc (=@{gmultiset A} ) (\226\138\142)).
Time Proof.
Time (intros X Y Z).
Time (apply gmultiset_eq; intros x).
Time (rewrite !multiplicity_disj_union; lia).
Time Qed.
Time #[global]
Instance gmultiset_disj_union_left_id : (LeftId (=@{gmultiset A} ) \226\136\133 (\226\138\142)).
Time Proof.
Time (intros X).
Time (apply gmultiset_eq; intros x).
Time by rewrite multiplicity_disj_union, multiplicity_empty.
Time Qed.
Time #[global]
Instance gmultiset_disj_union_right_id : (RightId (=@{gmultiset A} ) \226\136\133 (\226\138\142)).
Time Proof.
Time (intros X).
Time by rewrite (comm_L (\226\138\142)), (left_id_L _ _).
Time Qed.
Time #[global]Instance gmultiset_disj_union_inj_1  X: (Inj (=) (=) (X\226\138\142)).
Time Proof.
Time (intros Y1 Y2).
Time (rewrite !gmultiset_eq).
Time (intros HX x; generalize (HX x)).
Time (rewrite !multiplicity_disj_union).
Time lia.
Time Qed.
Time #[global]Instance gmultiset_disj_union_inj_2  X: (Inj (=) (=) (\226\138\142X)).
Time Proof.
Time (intros Y1 Y2).
Time (rewrite <- !(comm_L _ X)).
Time (apply (inj _)).
Time Qed.
Time
Lemma gmultiset_disj_union_intersection_l X Y Z :
  X \226\138\142 Y \226\136\169 Z = (X \226\138\142 Y) \226\136\169 (X \226\138\142 Z).
Time Proof.
Time (apply gmultiset_eq; intros y).
Time
(rewrite multiplicity_disj_union, !multiplicity_intersection,
  !multiplicity_disj_union).
Time lia.
Time Qed.
Time
Lemma gmultiset_disj_union_intersection_r X Y Z :
  X \226\136\169 Y \226\138\142 Z = (X \226\138\142 Z) \226\136\169 (Y \226\138\142 Z).
Time Proof.
Time by rewrite <- !(comm_L _ Z), gmultiset_disj_union_intersection_l.
Time Qed.
Time
Lemma gmultiset_disj_union_union_l X Y Z : X \226\138\142 (Y \226\136\170 Z) = X \226\138\142 Y \226\136\170 (X \226\138\142 Z).
Time Proof.
Time (apply gmultiset_eq; intros y).
Time
(rewrite multiplicity_disj_union, !multiplicity_union,
  !multiplicity_disj_union).
Time lia.
Time Qed.
Time Lemma gmultiset_disj_union_union_r X Y Z : X \226\136\170 Y \226\138\142 Z = X \226\138\142 Z \226\136\170 (Y \226\138\142 Z).
Time Proof.
Time by rewrite <- !(comm_L _ Z), gmultiset_disj_union_union_l.
Time Qed.
Time Lemma gmultiset_non_empty_singleton x : {[x]} \226\137\160@{ gmultiset A} \226\136\133.
Time Proof.
Time (rewrite gmultiset_eq).
Time (intros Hx; generalize (Hx x)).
Time by rewrite multiplicity_singleton, multiplicity_empty.
Time Qed.
Time Lemma list_to_set_disj_nil : list_to_set_disj [] =@{ gmultiset A} \226\136\133.
Time Proof.
Time done.
Time Qed.
Time
Lemma list_to_set_disj_cons x l :
  list_to_set_disj (x :: l) =@{ gmultiset A} {[x]} \226\138\142 list_to_set_disj l.
Time Proof.
Time done.
Time Qed.
Time
Lemma list_to_set_disj_app l1 l2 :
  list_to_set_disj (l1 ++ l2) =@{
  gmultiset A} list_to_set_disj l1 \226\138\142 list_to_set_disj l2.
Time Proof.
Time (induction l1 as [| x l1 IH]; simpl).
Time -
Time by rewrite (left_id_L _ _).
Time -
Time by rewrite IH, (assoc_L _).
Time Qed.
Time #[global]
Instance list_to_set_disj_perm :
 (Proper ((\226\137\161\226\130\154) ==> (=)) (list_to_set_disj (C:=gmultiset A))).
Time Proof.
Time
(induction 1 as [| x l l' _ IH| x y l| l l' l'' _ IH1 _ IH2]; simpl; auto).
Time -
Time by rewrite IH.
Time -
Time by rewrite !(assoc_L _), (comm_L _ {[x]}).
Time -
Time by rewrite IH1.
Time Qed.
Time Lemma gmultiset_elements_empty : elements (\226\136\133 : gmultiset A) = [].
Time Proof.
Time (unfold elements, gmultiset_elements; simpl).
Time by rewrite map_to_list_empty.
Time Qed.
Time Lemma gmultiset_elements_empty_inv X : elements X = [] \226\134\146 X = \226\136\133.
Time Proof.
Time (destruct X as [X]; unfold elements, gmultiset_elements; simpl).
Time (intros; apply (f_equal GMultiSet)).
Time (destruct (map_to_list X) as [| []] eqn:?).
Time -
Time by apply map_to_list_empty_inv.
Time -
Time naive_solver.
Time Qed.
Time Lemma gmultiset_elements_empty' X : elements X = [] \226\134\148 X = \226\136\133.
Time Proof.
Time (split; intros HX; [ by apply gmultiset_elements_empty_inv |  ]).
Time by rewrite HX, gmultiset_elements_empty.
Time Qed.
Time
Lemma gmultiset_elements_singleton x : elements ({[x]} : gmultiset A) = [x].
Time Proof.
Time (unfold elements, gmultiset_elements; simpl).
Time by rewrite map_to_list_singleton.
Time Qed.
Time
Lemma gmultiset_elements_disj_union X Y :
  elements (X \226\138\142 Y) \226\137\161\226\130\154 elements X ++ elements Y.
Time Proof.
Time (destruct X as [X], Y as [Y]; unfold elements, gmultiset_elements).
Time (set (f := fun xn => let '(x, n) := xn in replicate (S n) x); simpl).
Time (revert Y; induction X as [| x n X HX IH] using map_ind; intros Y).
Time {
Time by rewrite (left_id_L _ _ Y), map_to_list_empty.
Time }
Time (destruct (Y !! x) as [n'| ] eqn:HY).
Time -
Time (rewrite <- (insert_id Y x n'), <- (insert_delete Y) by done).
Time (erewrite <- insert_union_with by done).
Time
(rewrite !map_to_list_insert, !bind_cons by by
  rewrite ?lookup_union_with, ?lookup_delete, ?HX).
Time
(rewrite (assoc_L _), <- (comm (++) (f (_, n'))), <- !(assoc_L _), <- IH).
Time (rewrite (assoc_L _)).
Time f_equiv.
Time (rewrite (comm _); simpl).
Time by rewrite replicate_plus, Permutation_middle.
Time -
Time
(rewrite <- insert_union_with_l, !map_to_list_insert, !bind_cons by by
  rewrite ?lookup_union_with, ?HX, ?HY).
Time by rewrite <- (assoc_L (++)), <- IH.
Time Qed.
Time Lemma gmultiset_elem_of_elements x X : x \226\136\136 elements X \226\134\148 x \226\136\136 X.
Time Proof.
Time (destruct X as [X]).
Time (unfold elements, gmultiset_elements).
Time (set (f := fun xn => let '(x, n) := xn in replicate (S n) x); simpl).
Time (unfold elem_of at 2, gmultiset_elem_of, multiplicity; simpl).
Time (rewrite elem_of_list_bind).
Time split.
Time -
Time (intros [[? ?] [[<- ?]%elem_of_replicate ->%elem_of_map_to_list]]; lia).
Time -
Time (intros).
Time (destruct (X !! x) as [n| ] eqn:Hx; [  | lia ]).
Time (exists (x, n); split; [  | by apply elem_of_map_to_list ]).
Time (apply elem_of_replicate; auto with lia).
Time Qed.
Time Lemma gmultiset_elem_of_dom x X : x \226\136\136 dom (gset A) X \226\134\148 x \226\136\136 X.
Time Proof.
Time
(unfold dom, gmultiset_dom, elem_of at 2, gmultiset_elem_of, multiplicity).
Time (destruct X as [X]; simpl; rewrite elem_of_dom, <- not_eq_None_Some).
Time (destruct (X !! x); naive_solver lia).
Time Qed.
Time
Lemma gmultiset_set_fold_empty {B} (f : A \226\134\146 B \226\134\146 B) 
  (b : B) : set_fold f b (\226\136\133 : gmultiset A) = b.
Time Proof.
Time by unfold set_fold; simpl; rewrite gmultiset_elements_empty.
Time Qed.
Time
Lemma gmultiset_set_fold_singleton {B} (f : A \226\134\146 B \226\134\146 B) 
  (b : B) (a : A) : set_fold f b ({[a]} : gmultiset A) = f a b.
Time Proof.
Time by unfold set_fold; simpl; rewrite gmultiset_elements_singleton.
Time Qed.
Time
Lemma gmultiset_set_fold_disj_union (f : A \226\134\146 A \226\134\146 A) 
  (b : A) X Y :
  Comm (=) f
  \226\134\146 Assoc (=) f \226\134\146 set_fold f b (X \226\138\142 Y) = set_fold f (set_fold f b X) Y.
Time Proof.
Time (intros Hcomm Hassoc).
Time (unfold set_fold; simpl).
Time by rewrite gmultiset_elements_disj_union, <- foldr_app, (comm (++)).
Time Qed.
Time Lemma gmultiset_size_empty : size (\226\136\133 : gmultiset A) = 0.
Time Proof.
Time done.
Time Qed.
Time Lemma gmultiset_size_empty_inv X : size X = 0 \226\134\146 X = \226\136\133.
Time Proof.
Time (unfold size, gmultiset_size; simpl).
Time (rewrite length_zero_iff_nil).
Time (apply gmultiset_elements_empty_inv).
Time Qed.
Time Lemma gmultiset_size_empty_iff X : size X = 0 \226\134\148 X = \226\136\133.
Time Proof.
Time (split; [ apply gmultiset_size_empty_inv |  ]).
Time by intros ->; rewrite gmultiset_size_empty.
Time Qed.
Time Lemma gmultiset_size_non_empty_iff X : size X \226\137\160 0 \226\134\148 X \226\137\160 \226\136\133.
Time Proof.
Time by rewrite gmultiset_size_empty_iff.
Time Qed.
Time Lemma gmultiset_choose_or_empty X : (\226\136\131 x, x \226\136\136 X) \226\136\168 X = \226\136\133.
Time Proof.
Time (destruct (elements X) as [| x l] eqn:HX; [ right | left ]).
Time -
Time by apply gmultiset_elements_empty_inv.
Time -
Time exists x.
Time (rewrite <- gmultiset_elem_of_elements, HX).
Time by left.
Time Qed.
Time Lemma gmultiset_choose X : X \226\137\160 \226\136\133 \226\134\146 \226\136\131 x, x \226\136\136 X.
Time Proof.
Time (intros).
Time by destruct (gmultiset_choose_or_empty X).
Time Qed.
Time Lemma gmultiset_size_pos_elem_of X : 0 < size X \226\134\146 \226\136\131 x, x \226\136\136 X.
Time Proof.
Time (intros Hsz).
Time (destruct (gmultiset_choose_or_empty X) as [| HX]; [ done |  ]).
Time (contradict Hsz).
Time (rewrite HX, gmultiset_size_empty; lia).
Time Qed.
Time Lemma gmultiset_size_singleton x : size ({[x]} : gmultiset A) = 1.
Time Proof.
Time (unfold size, gmultiset_size; simpl).
Time by rewrite gmultiset_elements_singleton.
Time Qed.
Time Lemma gmultiset_size_disj_union X Y : size (X \226\138\142 Y) = size X + size Y.
Time Proof.
Time (unfold size, gmultiset_size; simpl).
Time by rewrite gmultiset_elements_disj_union, app_length.
Time Qed.
Time #[global]Instance gmultiset_po : (PartialOrder (\226\138\134@{gmultiset A} )).
Time Proof.
Time (split; [ split |  ]).
Time -
Time by intros X x.
Time -
Time (intros X Y Z HXY HYZ x).
Time by trans multiplicity x Y.
Time -
Time (intros X Y HXY HYX; apply gmultiset_eq; intros x).
Time by apply (anti_symm (\226\137\164)).
Time Qed.
Time
Lemma gmultiset_subseteq_alt X Y :
  X \226\138\134 Y
  \226\134\148 map_relation (\226\137\164) (\206\187 _, False) (\206\187 _, True) (gmultiset_car X)
      (gmultiset_car Y).
Time Proof.
Time (apply forall_proper; intros x).
Time (unfold multiplicity).
Time
(destruct (gmultiset_car X !! x), (gmultiset_car Y !! x); naive_solver lia).
Time Qed.
Time #[global]
Instance gmultiset_subseteq_dec : (RelDecision (\226\138\134@{gmultiset A} )).
Time Proof.
Time
(refine
  (\206\187 X Y,
     cast_if
       (decide
          (map_relation (\226\137\164) (\206\187 _, False) (\206\187 _, True) 
             (gmultiset_car X) (gmultiset_car Y)))); by
  rewrite gmultiset_subseteq_alt).
Time Defined.
Time Lemma gmultiset_subset_subseteq X Y : X \226\138\130 Y \226\134\146 X \226\138\134 Y.
Time Proof.
Time (apply strict_include).
Time Qed.
Time Hint Resolve gmultiset_subset_subseteq: core.
Time Lemma gmultiset_empty_subseteq X : \226\136\133 \226\138\134 X.
Time Proof.
Time (intros x).
Time (rewrite multiplicity_empty).
Time lia.
Time Qed.
Time Lemma gmultiset_union_subseteq_l X Y : X \226\138\134 X \226\136\170 Y.
Time Proof.
Time (intros x).
Time (rewrite multiplicity_union).
Time lia.
Time Qed.
Time Lemma gmultiset_union_subseteq_r X Y : Y \226\138\134 X \226\136\170 Y.
Time Proof.
Time (intros x).
Time (rewrite multiplicity_union).
Time lia.
Time Qed.
Time
Lemma gmultiset_union_mono X1 X2 Y1 Y2 :
  X1 \226\138\134 X2 \226\134\146 Y1 \226\138\134 Y2 \226\134\146 X1 \226\136\170 Y1 \226\138\134 X2 \226\136\170 Y2.
Time Proof.
Time (intros HX HY x).
Time (rewrite !multiplicity_union).
Time (specialize (HX x); specialize (HY x); lia).
Time Qed.
Time Lemma gmultiset_union_mono_l X Y1 Y2 : Y1 \226\138\134 Y2 \226\134\146 X \226\136\170 Y1 \226\138\134 X \226\136\170 Y2.
Time Proof.
Time (intros).
Time by apply gmultiset_union_mono.
Time Qed.
Time Lemma gmultiset_union_mono_r X1 X2 Y : X1 \226\138\134 X2 \226\134\146 X1 \226\136\170 Y \226\138\134 X2 \226\136\170 Y.
Time Proof.
Time (intros).
Time by apply gmultiset_union_mono.
Time Qed.
Time Lemma gmultiset_disj_union_subseteq_l X Y : X \226\138\134 X \226\138\142 Y.
Time Proof.
Time (intros x).
Time (rewrite multiplicity_disj_union).
Time lia.
Time Qed.
Time Lemma gmultiset_disj_union_subseteq_r X Y : Y \226\138\134 X \226\138\142 Y.
Time Proof.
Time (intros x).
Time (rewrite multiplicity_disj_union).
Time lia.
Time Qed.
Time
Lemma gmultiset_disj_union_mono X1 X2 Y1 Y2 :
  X1 \226\138\134 X2 \226\134\146 Y1 \226\138\134 Y2 \226\134\146 X1 \226\138\142 Y1 \226\138\134 X2 \226\138\142 Y2.
Time Proof.
Time (intros ? ? x).
Time (rewrite !multiplicity_disj_union).
Time by apply Nat.add_le_mono.
Time Qed.
Time Lemma gmultiset_disj_union_mono_l X Y1 Y2 : Y1 \226\138\134 Y2 \226\134\146 X \226\138\142 Y1 \226\138\134 X \226\138\142 Y2.
Time Proof.
Time (intros).
Time by apply gmultiset_disj_union_mono.
Time Qed.
Time Lemma gmultiset_disj_union_mono_r X1 X2 Y : X1 \226\138\134 X2 \226\134\146 X1 \226\138\142 Y \226\138\134 X2 \226\138\142 Y.
Time Proof.
Time (intros).
Time by apply gmultiset_disj_union_mono.
Time Qed.
Time Lemma gmultiset_subset X Y : X \226\138\134 Y \226\134\146 size X < size Y \226\134\146 X \226\138\130 Y.
Time Proof.
Time (intros).
Time (apply strict_spec_alt; split; naive_solver auto with lia).
Time Qed.
Time Lemma gmultiset_disj_union_subset_l X Y : Y \226\137\160 \226\136\133 \226\134\146 X \226\138\130 X \226\138\142 Y.
Time Proof.
Time (intros HY%gmultiset_size_non_empty_iff).
Time (apply gmultiset_subset; auto using gmultiset_disj_union_subseteq_l).
Time (rewrite gmultiset_size_disj_union; lia).
Time Qed.
Time Lemma gmultiset_union_subset_r X Y : X \226\137\160 \226\136\133 \226\134\146 Y \226\138\130 X \226\138\142 Y.
Time Proof.
Time (rewrite (comm_L (\226\138\142))).
Time (apply gmultiset_disj_union_subset_l).
Time Qed.
Time Lemma gmultiset_elem_of_singleton_subseteq x X : x \226\136\136 X \226\134\148 {[x]} \226\138\134 X.
Time Proof.
Time (rewrite elem_of_multiplicity).
Time split.
Time -
Time (intros Hx y).
Time (rewrite multiplicity_singleton').
Time (destruct (decide (y = x)); naive_solver lia).
Time -
Time (intros Hx).
Time (generalize (Hx x)).
Time (rewrite multiplicity_singleton).
Time lia.
Time Qed.
Time Lemma gmultiset_elem_of_subseteq X1 X2 x : x \226\136\136 X1 \226\134\146 X1 \226\138\134 X2 \226\134\146 x \226\136\136 X2.
Time Proof.
Time (rewrite !gmultiset_elem_of_singleton_subseteq).
Time by intros ->.
Time Qed.
Time Lemma gmultiset_disj_union_difference X Y : X \226\138\134 Y \226\134\146 Y = X \226\138\142 Y \226\136\150 X.
Time Proof.
Time (intros HXY).
Time (apply gmultiset_eq; intros x; specialize (HXY x)).
Time (rewrite multiplicity_disj_union, multiplicity_difference; lia).
Time Qed.
Time
Lemma gmultiset_disj_union_difference' x Y : x \226\136\136 Y \226\134\146 Y = {[x]} \226\138\142 Y \226\136\150 {[x]}.
Time Proof.
Time (intros).
Time
by
 apply gmultiset_disj_union_difference, gmultiset_elem_of_singleton_subseteq.
Time Qed.
Time
Lemma gmultiset_size_difference X Y : Y \226\138\134 X \226\134\146 size (X \226\136\150 Y) = size X - size Y.
Time Proof.
Time (intros HX%gmultiset_disj_union_difference).
Time (rewrite HX  at 2; rewrite gmultiset_size_disj_union).
Time lia.
Time Qed.
Time Lemma gmultiset_empty_difference X Y : Y \226\138\134 X \226\134\146 Y \226\136\150 X = \226\136\133.
Time Proof.
Time (intros HYX).
Time unfold_leibniz.
Time (intros x).
Time (rewrite multiplicity_difference, multiplicity_empty).
Time specialize (HYX x).
Time lia.
Time Qed.
Time Lemma gmultiset_non_empty_difference X Y : X \226\138\130 Y \226\134\146 Y \226\136\150 X \226\137\160 \226\136\133.
Time Proof.
Time (intros [_ HXY2] Hdiff; destruct HXY2; intros x).
Time (generalize (f_equal (multiplicity x) Hdiff)).
Time (rewrite multiplicity_difference, multiplicity_empty; lia).
Time Qed.
Time Lemma gmultiset_difference_diag X : X \226\136\150 X = \226\136\133.
Time Proof.
Time by apply gmultiset_empty_difference.
Time Qed.
Time Lemma gmultiset_difference_subset X Y : X \226\137\160 \226\136\133 \226\134\146 X \226\138\134 Y \226\134\146 Y \226\136\150 X \226\138\130 Y.
Time Proof.
Time (intros).
Time (eapply strict_transitive_l; [ by apply gmultiset_union_subset_r |  ]).
Time by rewrite <- (gmultiset_disj_union_difference X Y).
Time Qed.
Time
Lemma gmultiset_elements_submseteq X Y : X \226\138\134 Y \226\134\146 elements X \226\138\134+ elements Y.
Time Proof.
Time (intros ->%gmultiset_disj_union_difference).
Time (rewrite gmultiset_elements_disj_union).
Time by apply submseteq_inserts_r.
Time Qed.
Time Lemma gmultiset_subseteq_size X Y : X \226\138\134 Y \226\134\146 size X \226\137\164 size Y.
Time Proof.
Time (intros).
Time by apply submseteq_length, gmultiset_elements_submseteq.
Time Qed.
Time Lemma gmultiset_subset_size X Y : X \226\138\130 Y \226\134\146 size X < size Y.
Time Proof.
Time (intros HXY).
Time (assert (size (Y \226\136\150 X) \226\137\160 0)).
Time {
Time by apply gmultiset_size_non_empty_iff, gmultiset_non_empty_difference.
Time }
Time
(rewrite (gmultiset_disj_union_difference X Y), gmultiset_size_disj_union by
  auto).
Time lia.
Time Qed.
Time Lemma gmultiset_wf : wf (\226\138\130@{gmultiset A} ).
Time Proof.
Time
(apply (wf_projected (<) size); auto using gmultiset_subset_size, lt_wf).
Time Qed.
Time
Lemma gmultiset_ind (P : gmultiset A \226\134\146 Prop) :
  P \226\136\133 \226\134\146 (\226\136\128 x X, P X \226\134\146 P ({[x]} \226\138\142 X)) \226\134\146 \226\136\128 X, P X.
Time Proof.
Time (intros Hemp Hinsert X).
Time (induction (gmultiset_wf X) as [X _ IH]).
Time (destruct (gmultiset_choose_or_empty X) as [[x Hx]| ->]; auto).
Time (rewrite (gmultiset_disj_union_difference' x X) by done).
Time
(apply Hinsert, IH, gmultiset_difference_subset,
  gmultiset_elem_of_singleton_subseteq; auto
  using gmultiset_non_empty_singleton).
Time Qed.
Time End lemmas.
