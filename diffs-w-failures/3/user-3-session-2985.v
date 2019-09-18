Time From Coq Require Import PArith.
Time From iris.algebra Require Export ofe monoid.
Time From iris.algebra Require Export ofe.
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
Time From stdpp Require Import finite.
Time Set Default Proof Using "Type".
Time
Record solution (F : cFunctor) :=
 Solution {solution_car :> ofeT;
           solution_cofe : Cofe solution_car;
           solution_unfold : solution_car -n> F solution_car _;
           solution_fold : F solution_car _ -n> solution_car;
           solution_fold_unfold :
            forall X, solution_fold (solution_unfold X) \226\137\161 X;
           solution_unfold_fold :
            forall X, solution_unfold (solution_fold X) \226\137\161 X}.
Time Qed.
Time Lemma Psingleton_wf {A} i (x : A) : Pmap_wf (Psingleton_raw i x).
Time Proof.
Time (induction i as [[]| []| ]; simpl; rewrite ?andb_true_r; auto).
Time Set Default Proof Using "Type".
Time Class PCore (A : Type) :=
         pcore : A \226\134\146 option A.
Time Hint Mode PCore !: typeclass_instances.
Time Arguments solution_unfold {_} _.
Time Arguments solution_fold {_} _.
Time Existing Instance solution_cofe.
Time Module solver.
Time Section solver.
Time Context (F : cFunctor) `{Fcontr : cFunctorContractive F}.
Time Context `{Fcofe : \226\136\128 (T : ofeT) `{!Cofe T}, Cofe (F T _)}.
Time Context `{Finh : Inhabited (F unitC _)}.
Time Notation map := (cFunctor_map F).
Time
Fixpoint A' (k : nat) : {C : ofeT & Cofe C} :=
  match k with
  | 0 => existT (P:=Cofe) unitC _
  | S k => existT (P:=Cofe) (F (projT1 (A' k)) (projT2 (A' k))) _
  end.
Time Instance: (Params (@pcore) 2) := { }.
Time Class Op (A : Type) :=
         op : A \226\134\146 A \226\134\146 A.
Time Hint Mode Op !: typeclass_instances.
Time Instance: (Params (@op) 2) := { }.
Time Infix "\226\139\133" := op (at level 50, left associativity) : stdpp_scope.
Time Notation "(\226\139\133)" := op (only parsing) : stdpp_scope.
Time Definition included `{Equiv A} `{Op A} (x y : A) := \226\136\131 z, y \226\137\161 x \226\139\133 z.
Time Infix "\226\137\188" := included (at level 70) : stdpp_scope.
Time Notation "(\226\137\188)" := included (only parsing) : stdpp_scope.
Time Hint Extern 0 (_ \226\137\188 _) => reflexivity: core.
Time Instance: (Params (@included) 3) := { }.
Time Class ValidN (A : Type) :=
         validN : nat \226\134\146 A \226\134\146 Prop.
Time Notation A k:= (projT1 (A' k)).
Time #[local]Instance A_cofe  k: (Cofe (A k)) := (projT2 (A' k)).
Time
Fixpoint f (k : nat) : A k -n> A (S k) :=
  match k with
  | 0 => CofeMor (\206\187 _, inhabitant)
  | S k => map (g k, f k)
  end
with g (k : nat) : A (S k) -n> A k :=
  match k with
  | 0 => CofeMor (\206\187 _, ())
  | S k => map (f k, g k)
  end.
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
Time Hint Mode ValidN !: typeclass_instances.
Time Instance: (Params (@validN) 3) := { }.
Time
Notation "\226\156\147{ n } x" := (validN n x)
  (at level 20, n  at next level, format "\226\156\147{ n }  x").
Time Class Valid (A : Type) :=
         valid : A \226\134\146 Prop.
Time Hint Mode Valid !: typeclass_instances.
Time Instance: (Params (@valid) 2) := { }.
Time Notation "\226\156\147 x" := (valid x) (at level 20) : stdpp_scope.
Time
Definition includedN `{Dist A} `{Op A} (n : nat) (x y : A) :=
  \226\136\131 z, y \226\137\161{n}\226\137\161 x \226\139\133 z.
Time
Notation "x \226\137\188{ n } y" := (includedN n x y)
  (at level 70, n  at next level, format "x  \226\137\188{ n }  y") : stdpp_scope.
Time Instance: (Params (@includedN) 4) := { }.
Time Hint Extern 0 (_ \226\137\188{_} _) => reflexivity: core.
Time Section mixin.
Time #[local]Set Primitive Projections.
Time
Record CmraMixin A `{Dist A} `{Equiv A} `{PCore A} 
`{Op A} `{Valid A} `{ValidN A} :={mixin_cmra_op_ne :
                                   forall x : A, NonExpansive (op x);
                                  mixin_cmra_pcore_ne :
                                   forall n (x y : A) cx,
                                   x \226\137\161{n}\226\137\161 y
                                   \226\134\146 pcore x = Some cx
                                     \226\134\146 \226\136\131 cy, pcore y = Some cy \226\136\167 cx \226\137\161{n}\226\137\161 cy;
                                  mixin_cmra_validN_ne :
                                   forall n,
                                   Proper (dist n ==> impl) (validN n);
                                  mixin_cmra_valid_validN :
                                   forall x : A, \226\156\147 x \226\134\148 (\226\136\128 n, \226\156\147{n} x);
                                  mixin_cmra_validN_S :
                                   forall n (x : A), \226\156\147{S n} x \226\134\146 \226\156\147{n} x;
                                  mixin_cmra_assoc : Assoc (\226\137\161@{A} ) (\226\139\133);
                                  mixin_cmra_comm : Comm (\226\137\161@{A} ) (\226\139\133);
                                  mixin_cmra_pcore_l :
                                   forall (x : A) cx,
                                   pcore x = Some cx \226\134\146 cx \226\139\133 x \226\137\161 x;
                                  mixin_cmra_pcore_idemp :
                                   forall (x : A) cx,
                                   pcore x = Some cx \226\134\146 pcore cx \226\137\161 Some cx;
                                  mixin_cmra_pcore_mono :
                                   forall (x y : A) cx,
                                   x \226\137\188 y
                                   \226\134\146 pcore x = Some cx
                                     \226\134\146 \226\136\131 cy, pcore y = Some cy \226\136\167 cx \226\137\188 cy;
                                  mixin_cmra_validN_op_l :
                                   forall n (x y : A), \226\156\147{n} (x \226\139\133 y) \226\134\146 \226\156\147{n} x;
                                  mixin_cmra_extend :
                                   forall n (x y1 y2 : A),
                                   \226\156\147{n} x
                                   \226\134\146 x \226\137\161{n}\226\137\161 y1 \226\139\133 y2
                                     \226\134\146 {z1 : A &
                                       {z2 |
                                       x \226\137\161 z1 \226\139\133 z2
                                       \226\136\167 z1 \226\137\161{n}\226\137\161 y1 \226\136\167 z2 \226\137\161{n}\226\137\161 y2}}}.
Time
Definition f_S k (x : A (S k)) : f (S k) x = map (g k, f k) x := eq_refl.
Time Qed.
Time
Lemma Pfmap_wf {A} {B} (f : A \226\134\146 B) t : Pmap_wf t \226\134\146 Pmap_wf (Pfmap_raw f t).
Time Proof.
Time
(induction t as [| [x| ] [] ? [] ?]; simpl in *; rewrite ?andb_True;
  intuition).
Time
Definition g_S k (x : A (S (S k))) : g (S k) x = map (f k, g k) x := eq_refl.
Time End mixin.
Time
Structure cmraT :=
 CmraT' {cmra_car :> Type;
         cmra_equiv : Equiv cmra_car;
         cmra_dist : Dist cmra_car;
         cmra_pcore : PCore cmra_car;
         cmra_op : Op cmra_car;
         cmra_valid : Valid cmra_car;
         cmra_validN : ValidN cmra_car;
         cmra_ofe_mixin : OfeMixin cmra_car;
         cmra_mixin : CmraMixin cmra_car;
         _ : Type}.
Time Arguments CmraT' _ {_} {_} {_} {_} {_} {_} _ _ _.
Time
Notation CmraT A m:= (CmraT' A (ofe_mixin_of A%type) m A) (only parsing).
Time Arguments cmra_car : simpl never.
Time Arguments cmra_equiv : simpl never.
Time Arguments cmra_dist : simpl never.
Time Arguments cmra_pcore : simpl never.
Time Arguments cmra_op : simpl never.
Time Arguments cmra_valid : simpl never.
Time Arguments cmra_validN : simpl never.
Time Arguments cmra_ofe_mixin : simpl never.
Time Arguments cmra_mixin : simpl never.
Time Add Printing Constructor cmraT.
Time
Hint Extern 0 (PCore _) => (eapply (@cmra_pcore _)): typeclass_instances.
Time Hint Extern 0 (Op _) => (eapply (@cmra_op _)): typeclass_instances.
Time
Hint Extern 0 (Valid _) => (eapply (@cmra_valid _)): typeclass_instances.
Time
Hint Extern 0 (ValidN _) => (eapply (@cmra_validN _)): typeclass_instances.
Time Coercion cmra_ofeC (A : cmraT) : ofeT := OfeT A (cmra_ofe_mixin A).
Time Canonical Structure cmra_ofeC.
Time
Definition cmra_mixin_of' A {Ac : cmraT} (f : Ac \226\134\146 A) : 
  CmraMixin Ac := cmra_mixin Ac.
Time Notation cmra_mixin_of A:= _ (only parsing).
Time Section cmra_mixin.
Time Context {A : cmraT}.
Time Implicit Types x y : A.
Time #[global]Instance cmra_op_ne  (x : A): (NonExpansive (op x)).
Time Proof.
Time (apply (mixin_cmra_op_ne _ (cmra_mixin A))).
Time Qed.
Time
Lemma cmra_pcore_ne n x y cx :
  x \226\137\161{n}\226\137\161 y \226\134\146 pcore x = Some cx \226\134\146 \226\136\131 cy, pcore y = Some cy \226\136\167 cx \226\137\161{n}\226\137\161 cy.
Time Arguments f : simpl never.
Time Arguments g : simpl never.
Time Lemma gf {k} (x : A k) : g k (f k x) \226\137\161 x.
Time Proof  using (Fcontr).
Time (induction k as [| k IH]; simpl in *; [ by destruct x |  ]).
Time rewrite -cFunctor_compose -{+2}[x]cFunctor_id.
Time Proof.
Time (apply (mixin_cmra_pcore_ne _ (cmra_mixin A))).
Time Qed.
Time #[global]
Instance cmra_validN_ne  n: (Proper (dist n ==> impl) (@validN A _ n)).
Time Proof.
Time (apply (mixin_cmra_validN_ne _ (cmra_mixin A))).
Time Qed.
Time Lemma cmra_valid_validN x : \226\156\147 x \226\134\148 (\226\136\128 n, \226\156\147{n} x).
Time Proof.
Time (apply (mixin_cmra_valid_validN _ (cmra_mixin A))).
Time Qed.
Time Lemma cmra_validN_S n x : \226\156\147{S n} x \226\134\146 \226\156\147{n} x.
Time Proof.
Time (apply (mixin_cmra_validN_S _ (cmra_mixin A))).
Time Qed.
Time #[global]Instance cmra_assoc : (Assoc (\226\137\161) (@op A _)).
Time Proof.
Time (apply (mixin_cmra_assoc _ (cmra_mixin A))).
Time Qed.
Time #[global]Instance cmra_comm : (Comm (\226\137\161) (@op A _)).
Time Proof.
Time (apply (mixin_cmra_comm _ (cmra_mixin A))).
Time Qed.
Time Lemma cmra_pcore_l x cx : pcore x = Some cx \226\134\146 cx \226\139\133 x \226\137\161 x.
Time Proof.
Time (apply (mixin_cmra_pcore_l _ (cmra_mixin A))).
Time Qed.
Time Lemma cmra_pcore_idemp x cx : pcore x = Some cx \226\134\146 pcore cx \226\137\161 Some cx.
Time Proof.
Time (apply (mixin_cmra_pcore_idemp _ (cmra_mixin A))).
Time Qed.
Time
Lemma cmra_pcore_mono x y cx :
  x \226\137\188 y \226\134\146 pcore x = Some cx \226\134\146 \226\136\131 cy, pcore y = Some cy \226\136\167 cx \226\137\188 cy.
Time Proof.
Time (apply (mixin_cmra_pcore_mono _ (cmra_mixin A))).
Time Qed.
Time Lemma cmra_validN_op_l n x y : \226\156\147{n} (x \226\139\133 y) \226\134\146 \226\156\147{n} x.
Time Proof.
Time (apply (mixin_cmra_validN_op_l _ (cmra_mixin A))).
Time Qed.
Time
Lemma cmra_extend n x y1 y2 :
  \226\156\147{n} x
  \226\134\146 x \226\137\161{n}\226\137\161 y1 \226\139\133 y2
    \226\134\146 {z1 : A & {z2 | x \226\137\161 z1 \226\139\133 z2 \226\136\167 z1 \226\137\161{n}\226\137\161 y1 \226\136\167 z2 \226\137\161{n}\226\137\161 y2}}.
Time Proof.
Time (apply (mixin_cmra_extend _ (cmra_mixin A))).
Time Qed.
Time End cmra_mixin.
Time
Definition opM {A : cmraT} (x : A) (my : option A) :=
  match my with
  | Some y => x \226\139\133 y
  | None => x
  end.
Time Infix "\226\139\133?" := opM (at level 50, left associativity) : stdpp_scope.
Time Class CoreId {A : cmraT} (x : A) :=
         core_id : pcore x \226\137\161 Some x.
Time Arguments core_id {_} _ {_}.
Time Hint Mode CoreId + !: typeclass_instances.
Time Instance: (Params (@CoreId) 1) := { }.
Time
Class Exclusive {A : cmraT} (x : A) :=
    exclusive0_l : forall y, \226\156\147{0} (x \226\139\133 y) \226\134\146 False.
Time Arguments exclusive0_l {_} _ {_} _ _.
Time Hint Mode Exclusive + !: typeclass_instances.
Time Instance: (Params (@Exclusive) 1) := { }.
Time
Class Cancelable {A : cmraT} (x : A) :=
    cancelableN : forall n y z, \226\156\147{n} (x \226\139\133 y) \226\134\146 x \226\139\133 y \226\137\161{n}\226\137\161 x \226\139\133 z \226\134\146 y \226\137\161{n}\226\137\161 z.
Time Qed.
Time Arguments cancelableN {_} _ {_} _ _ _ _.
Time Hint Mode Cancelable + !: typeclass_instances.
Time Instance: (Params (@Cancelable) 1) := { }.
Time
Class IdFree {A : cmraT} (x : A) :=
    id_free0_r : forall y, \226\156\147{0} x \226\134\146 x \226\139\133 y \226\137\161{0}\226\137\161 x \226\134\146 False.
Time
Lemma Pomap_wf {A} {B} (f : A \226\134\146 option B) t :
  Pmap_wf t \226\134\146 Pmap_wf (Pomap_raw f t).
Time Proof.
Time (induction t; simpl; eauto).
Time Arguments id_free0_r {_} _ {_} _ _.
Time Hint Mode IdFree + !: typeclass_instances.
Time Instance: (Params (@IdFree) 1) := { }.
Time
Class CmraTotal (A : cmraT) :=
    cmra_total : forall x : A, is_Some (pcore x).
Time Qed.
Time
Lemma Pmerge_wf {A} {B} {C} (f : option A \226\134\146 option B \226\134\146 option C) 
  t1 t2 : Pmap_wf t1 \226\134\146 Pmap_wf t2 \226\134\146 Pmap_wf (Pmerge_raw f t1 t2).
Time Hint Mode CmraTotal !: typeclass_instances.
Time Class Core (A : Type) :=
         core : A \226\134\146 A.
Time Hint Mode Core !: typeclass_instances.
Time Instance: (Params (@core) 2) := { }.
Time Instance core'  `{PCore A}: (Core A) := (\206\187 x, default x (pcore x)).
Time Arguments core' _ _ _ /.
Time Class Unit (A : Type) :=
         \206\181 : A.
Time Proof.
Time revert t2.
Time (induction t1; intros []; simpl; eauto using Pomap_wf).
Time Arguments \206\181 {_} {_}.
Time
Record UcmraMixin A `{Dist A} `{Equiv A} `{PCore A} 
`{Op A} `{Valid A} `{Unit A} :={mixin_ucmra_unit_valid : \226\156\147 (\206\181 : A);
                                mixin_ucmra_unit_left_id : LeftId (\226\137\161) \206\181 (\226\139\133);
                                mixin_ucmra_pcore_unit : pcore \206\181 \226\137\161 Some \206\181}.
Time
Structure ucmraT :=
 UcmraT' {ucmra_car :> Type;
          ucmra_equiv : Equiv ucmra_car;
          ucmra_dist : Dist ucmra_car;
          ucmra_pcore : PCore ucmra_car;
          ucmra_op : Op ucmra_car;
          ucmra_valid : Valid ucmra_car;
          ucmra_validN : ValidN ucmra_car;
          ucmra_unit : Unit ucmra_car;
          ucmra_ofe_mixin : OfeMixin ucmra_car;
          ucmra_cmra_mixin : CmraMixin ucmra_car;
          ucmra_mixin : UcmraMixin ucmra_car;
          _ : Type}.
Time Arguments UcmraT' _ {_} {_} {_} {_} {_} {_} {_} _ _ _ _.
Time
Notation UcmraT A m:=
  (UcmraT' A (ofe_mixin_of A%type) (cmra_mixin_of A%type) m A) 
  (only parsing).
Time Arguments ucmra_car : simpl never.
Time Arguments ucmra_equiv : simpl never.
Time Arguments ucmra_dist : simpl never.
Time Arguments ucmra_pcore : simpl never.
Time Arguments ucmra_op : simpl never.
Time Arguments ucmra_valid : simpl never.
Time Arguments ucmra_validN : simpl never.
Time Arguments ucmra_ofe_mixin : simpl never.
Time Arguments ucmra_cmra_mixin : simpl never.
Time Arguments ucmra_mixin : simpl never.
Time Add Printing Constructor ucmraT.
Time Hint Extern 0 (Unit _) => (eapply (@ucmra_unit _)): typeclass_instances.
Time Coercion ucmra_ofeC (A : ucmraT) : ofeT := OfeT A (ucmra_ofe_mixin A).
Time Canonical Structure ucmra_ofeC.
Time
Coercion ucmra_cmraR (A : ucmraT) : cmraT :=
  CmraT' A (ucmra_ofe_mixin A) (ucmra_cmra_mixin A) A.
Time Canonical Structure ucmra_cmraR.
Time Section ucmra_mixin.
Time Context {A : ucmraT}.
Time Implicit Types x y : A.
Time Lemma ucmra_unit_valid : \226\156\147 (\206\181 : A).
Time Proof.
Time (apply (mixin_ucmra_unit_valid _ (ucmra_mixin A))).
Time Qed.
Time #[global]Instance ucmra_unit_left_id : (LeftId (\226\137\161) \206\181 (@op A _)).
Time Proof.
Time (apply (mixin_ucmra_unit_left_id _ (ucmra_mixin A))).
Time Qed.
Time Lemma ucmra_pcore_unit : pcore (\206\181 : A) \226\137\161 Some \206\181.
Time Proof.
Time (apply (mixin_ucmra_pcore_unit _ (ucmra_mixin A))).
Time Qed.
Time End ucmra_mixin.
Time
Class CmraDiscrete (A : cmraT) :={cmra_discrete_ofe_discrete :> OfeDiscrete A;
                                  cmra_discrete_valid :
                                   forall x : A, \226\156\147{0} x \226\134\146 \226\156\147 x}.
Time Hint Mode CmraDiscrete !: typeclass_instances.
Time
Class CmraMorphism {A B : cmraT} (f : A \226\134\146 B) :={cmra_morphism_ne :>
                                                 NonExpansive f;
                                                cmra_morphism_validN :
                                                 forall n x,
                                                 \226\156\147{n} x \226\134\146 \226\156\147{n} f x;
                                                cmra_morphism_pcore :
                                                 forall x,
                                                 pcore (f x) \226\137\161 f <$> pcore x;
                                                cmra_morphism_op :
                                                 forall x y,
                                                 f x \226\139\133 f y \226\137\161 f (x \226\139\133 y)}.
Time Arguments cmra_morphism_validN {_} {_} _ {_} _ _ _.
Time Arguments cmra_morphism_pcore {_} {_} _ {_} _.
Time Arguments cmra_morphism_op {_} {_} _ {_} _ _.
Time Section cmra.
Time Context {A : cmraT}.
Time Implicit Types x y z : A.
Time Implicit Types xs ys zs : list A.
Time #[global]Instance cmra_pcore_ne' : (NonExpansive (@pcore A _)).
Time Qed.
Time Lemma Plookup_empty {A} i : (\226\136\133 : Pmap_raw A) !! i = None.
Time Proof.
Time by destruct i.
Time Qed.
Time
Lemma Plookup_singleton {A} i (x : A) : Psingleton_raw i x !! i = Some x.
Time Proof.
Time (intros n x y Hxy).
Time (destruct (pcore x) as [cx| ] eqn:?).
Time {
Time (destruct (cmra_pcore_ne n x y cx) as (cy, (->, ->)); auto).
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
Time }
Time (destruct (pcore y) as [cy| ] eqn:?; auto).
Time -
Time by intros; destruct (f None); rewrite ?Plookup_singleton_ne.
Time -
Time
by intros [?| ?| ] [?| ?| ] ?; simpl; rewrite ?PNode_lookup; simpl; auto.
Time
(destruct (cmra_pcore_ne n y x cy) as (cx, (?, ->)); simplify_eq /=; auto).
Time Qed.
Time
Lemma cmra_pcore_proper x y cx :
  x \226\137\161 y \226\134\146 pcore x = Some cx \226\134\146 \226\136\131 cy, pcore y = Some cy \226\136\167 cx \226\137\161 cy.
Time Proof.
Time (intros).
Time (destruct (cmra_pcore_ne 0 x y cx) as (cy, (?, ?)); auto).
Time
(exists cy; split;
  [ done | <ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n ]).
Time Qed.
Time (destruct (cmra_pcore_ne n x y cx) as (cy', (?, ?)); naive_solver).
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
Time Qed.
Time #[global]
Instance cmra_pcore_proper' : (Proper ((\226\137\161) ==> (\226\137\161)) (@pcore A _)).
Time Proof.
Time (apply (ne_proper _)).
Time Qed.
Time #[global]Instance cmra_op_ne' : (NonExpansive2 (@op A _)).
Time Proof.
Time (intros n x1 x2 Hx y1 y2 Hy).
Time by rewrite Hy (comm _ x1) Hx (comm _ y2).
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
Time Qed.
Time #[global]
Instance cmra_op_proper' : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@op A _)).
Time Proof.
Time (apply (ne_proper_2 _)).
Time Qed.
Time }
Time (destruct (IHr j~1 acc) as [(i', (->, ?))| ?]; auto).
Time #[global]
Instance cmra_validN_ne' : (Proper (dist n ==> iff) (@validN A _ n)) |1.
Time Proof.
Time by split; apply cmra_validN_ne.
Time Qed.
Time #[global]
Instance cmra_validN_proper : (Proper ((\226\137\161) ==> iff) (@validN A _ n)) |1.
Time Proof.
Time by intros n x1 x2 Hx; apply cmra_validN_ne', equiv_dist.
Time Qed.
Time #[global]
Instance cmra_valid_proper : (Proper ((\226\137\161) ==> iff) (@valid A _)).
Time (left; exists i'~1).
Time by rewrite Preverse_xI, (assoc_L _).
Time Proof.
Time (intros x y Hxy; rewrite !cmra_valid_validN).
Time
by
 <ssreflect_plugin::ssrtclintros@0> split =>? n;
  [ rewrite -Hxy | rewrite Hxy ].
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
Time Qed.
Time revert j i acc Hi.
Time (induction t as [| [y| ] l IHl r IHr]; intros j i acc ?; simpl).
Time -
Time done.
Time -
Time (rewrite elem_of_cons).
Time (destruct i as [i| i| ]; simplify_eq /=).
Time #[global]
Instance cmra_includedN_ne  n:
 (Proper (dist n ==> dist n ==> iff) (@includedN A _ _ n)) |1.
Time Proof.
Time (intros x x' Hx y y' Hy).
Time by split; intros [z ?]; exists z; [ rewrite -Hx -Hy | rewrite Hx Hy ].
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
Time Qed.
Time #[global]
Instance cmra_includedN_proper  n:
 (Proper ((\226\137\161) ==> (\226\137\161) ==> iff) (@includedN A _ _ n)) |1.
Time Proof.
Time
(intros x x' Hx y y' Hy; revert Hx Hy; <ssreflect_plugin::ssrtclintros@0>
  rewrite !equiv_dist =>Hx Hy).
Time (apply help).
Time specialize (IHr j~1 i).
Time (rewrite Preverse_xI, (assoc_L _) in IHr).
Time by apply IHr.
Time +
Time specialize (IHl j~0 i).
Time (rewrite Preverse_xO, (assoc_L _) in IHl).
Time by apply IHl.
Time Qed.
Time by rewrite (Hx n) (Hy n).
Time Qed.
Time #[global]
Instance cmra_included_proper :
 (Proper ((\226\137\161) ==> (\226\137\161) ==> iff) (@included A _ _)) |1.
Time Proof.
Time (intros x x' Hx y y' Hy).
Time
Lemma Pto_list_nodup {A} j (t : Pmap_raw A) acc :
  (\226\136\128 i x, (i ++ Preverse j, x) \226\136\136 acc \226\134\146 t !! i = None)
  \226\134\146 NoDup acc \226\134\146 NoDup (Pto_list_raw j t acc).
Time Proof.
Time revert j acc.
Time (induction t as [| [y| ] l IHl r IHr]; simpl; intros j acc Hin ?).
Time by split; intros [z ?]; exists z; [ rewrite -Hx -Hy | rewrite Hx Hy ].
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
Time Qed.
Time #[global]Instance cmra_opM_ne : (NonExpansive2 (@opM A)).
Time Proof.
Time (destruct 2; by ofe_subst).
Time }
Time (rewrite Pelem_of_to_list in Hj).
Time (destruct Hj as [(i, (Hi, ?))| Hj]).
Time {
Time (apply (f_equal Plength) in Hi).
Time (rewrite Preverse_xI, !Papp_length in Hi; simpl in *; lia).
Time Qed.
Time #[global]
Instance cmra_opM_proper : (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@opM A)).
Time Proof.
Time (destruct 2; by setoid_subst).
Time }
Time specialize (Hin 1 y).
Time (rewrite (left_id_L 1 (++))%positive in Hin).
Time discriminate (Hin Hj).
Time }
Time (apply IHl).
Time {
Time (intros i x).
Time (rewrite Pelem_of_to_list).
Time by apply (contractive_proper map).
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
Time #[global]Instance CoreId_proper : (Proper ((\226\137\161) ==> iff) (@CoreId A)).
Time Proof.
Time solve_proper.
Time Qed.
Time Qed.
Time #[global]
Instance Exclusive_proper : (Proper ((\226\137\161) ==> iff) (@Exclusive A)).
Time Proof.
Time (intros x y Hxy).
Time rewrite /Exclusive.
Time by setoid_rewrite Hxy.
Time
Lemma Pomap_lookup {A} {B} (f : A \226\134\146 option B) t i :
  Pomap_raw f t !! i = t !! i \226\137\171= f.
Time Proof.
Time revert i.
Time
(induction t as [| o l IHl r IHr]; intros [i| i| ]; simpl;
  rewrite ?PNode_lookup; simpl; auto).
Time Qed.
Time #[global]
Instance Cancelable_proper : (Proper ((\226\137\161) ==> iff) (@Cancelable A)).
Time Proof.
Time (intros x y Hxy).
Time rewrite /Cancelable.
Time by setoid_rewrite Hxy.
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
Time Qed.
Time #[global]Instance IdFree_proper : (Proper ((\226\137\161) ==> iff) (@IdFree A)).
Time Proof.
Time (intros x y Hxy).
Time rewrite /IdFree.
Time by setoid_rewrite Hxy.
Time Qed.
Time -
Time (destruct i; rewrite ?Pomap_lookup; simpl; auto).
Time Qed.
Time Lemma cmra_op_opM_assoc x y mz : x \226\139\133 y \226\139\133? mz \226\137\161 x \226\139\133 (y \226\139\133? mz).
Time Proof.
Time (destruct mz; by rewrite /= -?assoc).
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
Time Lemma cmra_validN_le n n' x : \226\156\147{n} x \226\134\146 n' \226\137\164 n \226\134\146 \226\156\147{n'} x.
Time Proof.
Time (induction 2; eauto using cmra_validN_S).
Time Qed.
Time Lemma cmra_valid_op_l x y : \226\156\147 (x \226\139\133 y) \226\134\146 \226\156\147 x.
Time Proof.
Time (rewrite !cmra_valid_validN; eauto using cmra_validN_op_l).
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
Time Qed.
Time Lemma cmra_validN_op_r n x y : \226\156\147{n} (x \226\139\133 y) \226\134\146 \226\156\147{n} y.
Time Proof.
Time (rewrite (comm _ x); apply cmra_validN_op_l).
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
Time Qed.
Time Lemma cmra_valid_op_r x y : \226\156\147 (x \226\139\133 y) \226\134\146 \226\156\147 y.
Time Proof.
Time (rewrite !cmra_valid_validN; eauto using cmra_validN_op_r).
Time -
Time (intros ? [? ?] i x; unfold map_to_list, Pto_list).
Time (rewrite Pelem_of_to_list, elem_of_nil).
Time Qed.
Time Lemma cmra_pcore_l' x cx : pcore x \226\137\161 Some cx \226\134\146 cx \226\139\133 x \226\137\161 x.
Time Proof.
Time (intros (cx', (?, ->))%equiv_Some_inv_r').
Time split.
Time by intros [(?, (->, ?))| ].
Time by left; exists i.
Time -
Time (intros ? ? ? [? ?] ?).
Time by apply Pomap_lookup.
Time by apply cmra_pcore_l.
Time Qed.
Time Lemma cmra_pcore_r x cx : pcore x = Some cx \226\134\146 x \226\139\133 cx \226\137\161 x.
Time -
Time (intros ? ? ? ? ? [? ?] [? ?] ?).
Time by apply Pmerge_lookup.
Time Qed.
Time Proof.
Time (intros).
Time rewrite comm.
Time by apply cmra_pcore_l.
Time Qed.
Time #[program]
Instance Pmap_countable  `{Countable A}: (Countable (Pmap A)) := {
 encode :=fun m => encode (map_to_list m : list (positive * A));
 decode :=fun p => list_to_map <$> decode p}.
Time Lemma cmra_pcore_r' x cx : pcore x \226\137\161 Some cx \226\134\146 x \226\139\133 cx \226\137\161 x.
Time Proof.
Time (intros (cx', (?, ->))%equiv_Some_inv_r').
Time Next Obligation.
Time (intros A ? ? m; simpl).
Time (rewrite decode_encode; simpl).
Time by rewrite list_to_map_to_list.
Time Qed.
Time Notation Pset := (mapset Pmap).
Time Instance Pmap_dom  {A}: (Dom (Pmap A) Pset) := mapset_dom.
Time
Instance Pmap_dom_spec : (FinMapDom positive Pmap Pset) := mapset_dom_spec.
Time by apply cmra_pcore_r.
Time Qed.
Time Lemma cmra_pcore_idemp' x cx : pcore x \226\137\161 Some cx \226\134\146 pcore cx \226\137\161 Some cx.
Time Proof.
Time (intros (cx', (?, ->))%equiv_Some_inv_r').
Time eauto using cmra_pcore_idemp.
Time Qed.
Time Lemma cmra_pcore_dup x cx : pcore x = Some cx \226\134\146 cx \226\137\161 cx \226\139\133 cx.
Time Proof.
Time (intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp).
Time Qed.
Time Lemma cmra_pcore_dup' x cx : pcore x \226\137\161 Some cx \226\134\146 cx \226\137\161 cx \226\139\133 cx.
Time Proof.
Time (intros; symmetry; eauto using cmra_pcore_r', cmra_pcore_idemp').
Time Lemma fg {k} (x : A (S (S k))) : f (S k) (g (S k) x) \226\137\161{k}\226\137\161 x.
Time Qed.
Time Lemma cmra_pcore_validN n x cx : \226\156\147{n} x \226\134\146 pcore x = Some cx \226\134\146 \226\156\147{n} cx.
Time Proof.
Time (intros Hvx Hx%cmra_pcore_l).
Time (move : {}Hvx {}; rewrite -Hx).
Time Proof  using (Fcontr).
Time (induction k as [| k IH]; simpl).
Time -
Time rewrite f_S g_S -{+2}[x]cFunctor_id -cFunctor_compose.
Time (apply cmra_validN_op_l).
Time Qed.
Time Lemma cmra_pcore_valid x cx : \226\156\147 x \226\134\146 pcore x = Some cx \226\134\146 \226\156\147 cx.
Time Proof.
Time (intros Hv Hx%cmra_pcore_l).
Time (move : {}Hv {}; rewrite -Hx).
Time (apply cmra_valid_op_l).
Time Qed.
Time Lemma core_id_dup x `{!CoreId x} : x \226\137\161 x \226\139\133 x.
Time Proof.
Time by apply cmra_pcore_dup' with x.
Time Qed.
Time Lemma exclusiveN_l n x `{!Exclusive x} y : \226\156\147{n} (x \226\139\133 y) \226\134\146 False.
Time Proof.
Time (intros).
Time (eapply (exclusive0_l x y), cmra_validN_le; eauto with lia).
Time Qed.
Time Lemma exclusiveN_r n x `{!Exclusive x} y : \226\156\147{n} (y \226\139\133 x) \226\134\146 False.
Time Proof.
Time rewrite comm.
Time by apply exclusiveN_l.
Time Qed.
Time Lemma exclusive_l x `{!Exclusive x} y : \226\156\147 (x \226\139\133 y) \226\134\146 False.
Time Proof.
Time by move /cmra_valid_validN/(_ 0)/exclusive0_l {}.
Time Qed.
Time Lemma exclusive_r x `{!Exclusive x} y : \226\156\147 (y \226\139\133 x) \226\134\146 False.
Time Proof.
Time rewrite comm.
Time by apply exclusive_l.
Time Qed.
Time
Lemma exclusiveN_opM n x `{!Exclusive x} my : \226\156\147{n} (x \226\139\133? my) \226\134\146 my = None.
Time Proof.
Time (destruct my as [y| ]).
Time move  {}=>/(exclusiveN_l _ x) [].
Time done.
Time Qed.
Time
Lemma exclusive_includedN n x `{!Exclusive x} y : x \226\137\188{n} y \226\134\146 \226\156\147{n} y \226\134\146 False.
Time Proof.
Time (intros [? ->]).
Time by apply exclusiveN_l.
Time Qed.
Time Lemma exclusive_included x `{!Exclusive x} y : x \226\137\188 y \226\134\146 \226\156\147 y \226\134\146 False.
Time Proof.
Time (intros [? ->]).
Time by apply exclusive_l.
Time Qed.
Time Lemma cmra_included_includedN n x y : x \226\137\188 y \226\134\146 x \226\137\188{n} y.
Time Proof.
Time (intros [z ->]).
Time by exists z.
Time Qed.
Time #[global]
Instance cmra_includedN_trans  n: (Transitive (@includedN A _ _ n)).
Time Proof.
Time (intros x y z [z1 Hy] [z2 Hz]; exists (z1 \226\139\133 z2)).
Time by rewrite assoc -Hy -Hz.
Time Qed.
Time #[global]Instance cmra_included_trans : (Transitive (@included A _ _)).
Time Proof.
Time (intros x y z [z1 Hy] [z2 Hz]; exists (z1 \226\139\133 z2)).
Time by rewrite assoc -Hy -Hz.
Time Qed.
Time Lemma cmra_valid_included x y : \226\156\147 y \226\134\146 x \226\137\188 y \226\134\146 \226\156\147 x.
Time Proof.
Time (intros Hyv [z ?]; setoid_subst; eauto using cmra_valid_op_l).
Time Qed.
Time Lemma cmra_validN_includedN n x y : \226\156\147{n} y \226\134\146 x \226\137\188{n} y \226\134\146 \226\156\147{n} x.
Time Proof.
Time (intros Hyv [z ?]; ofe_subst y; eauto using cmra_validN_op_l).
Time Qed.
Time Lemma cmra_validN_included n x y : \226\156\147{n} y \226\134\146 x \226\137\188 y \226\134\146 \226\156\147{n} x.
Time Proof.
Time (intros Hyv [z ?]; setoid_subst; eauto using cmra_validN_op_l).
Time Qed.
Time Lemma cmra_includedN_S n x y : x \226\137\188{S n} y \226\134\146 x \226\137\188{n} y.
Time Proof.
Time by intros [z Hz]; exists z; apply dist_S.
Time Qed.
Time Lemma cmra_includedN_le n n' x y : x \226\137\188{n} y \226\134\146 n' \226\137\164 n \226\134\146 x \226\137\188{n'} y.
Time Proof.
Time (induction 2; auto using cmra_includedN_S).
Time Qed.
Time Lemma cmra_includedN_l n x y : x \226\137\188{n} x \226\139\133 y.
Time Proof.
Time by exists y.
Time Qed.
Time Lemma cmra_included_l x y : x \226\137\188 x \226\139\133 y.
Time Proof.
Time by exists y.
Time (apply (contractive_0 map)).
Time Qed.
Time Lemma cmra_includedN_r n x y : y \226\137\188{n} x \226\139\133 y.
Time Proof.
Time (rewrite (comm op); apply cmra_includedN_l).
Time -
Time rewrite f_S g_S -{+2}[x]cFunctor_id -cFunctor_compose.
Time Qed.
Time Lemma cmra_included_r x y : y \226\137\188 x \226\139\133 y.
Time Proof.
Time (rewrite (comm op); apply cmra_included_l).
Time Qed.
Time
Lemma cmra_pcore_mono' x y cx :
  x \226\137\188 y \226\134\146 pcore x \226\137\161 Some cx \226\134\146 \226\136\131 cy, pcore y = Some cy \226\136\167 cx \226\137\188 cy.
Time Proof.
Time (intros ? (cx', (?, Hcx))%equiv_Some_inv_r').
Time (destruct (cmra_pcore_mono x y cx') as (cy, (->, ?)); auto).
Time (exists cy; by rewrite Hcx).
Time Qed.
Time
Lemma cmra_pcore_monoN' n x y cx :
  x \226\137\188{n} y \226\134\146 pcore x \226\137\161{n}\226\137\161 Some cx \226\134\146 \226\136\131 cy, pcore y = Some cy \226\136\167 cx \226\137\188{n} cy.
Time Proof.
Time (intros [z Hy] (cx', (?, Hcx))%dist_Some_inv_r').
Time
(destruct (cmra_pcore_mono x (x \226\139\133 z) cx') as (cy, (Hxy, ?)); auto
  using cmra_included_l).
Time (assert (pcore y \226\137\161{n}\226\137\161 Some cy) as (cy', (?, Hcy'))%dist_Some_inv_r').
Time {
Time by rewrite Hy Hxy.
Time }
Time (<ssreflect_plugin::ssrtclseq@0> exists cy'; split ; first  done).
Time (rewrite Hcx -Hcy'; auto using cmra_included_includedN).
Time Qed.
Time Lemma cmra_included_pcore x cx : pcore x = Some cx \226\134\146 cx \226\137\188 x.
Time Proof.
Time exists x.
Time by rewrite cmra_pcore_l.
Time Qed.
Time Lemma cmra_monoN_l n x y z : x \226\137\188{n} y \226\134\146 z \226\139\133 x \226\137\188{n} z \226\139\133 y.
Time Proof.
Time by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op).
Time Qed.
Time Lemma cmra_mono_l x y z : x \226\137\188 y \226\134\146 z \226\139\133 x \226\137\188 z \226\139\133 y.
Time Proof.
Time by intros [z1 Hz1]; exists z1; rewrite Hz1 (assoc op).
Time Qed.
Time Lemma cmra_monoN_r n x y z : x \226\137\188{n} y \226\134\146 x \226\139\133 z \226\137\188{n} y \226\139\133 z.
Time Proof.
Time by intros; rewrite -!(comm _ z); apply cmra_monoN_l.
Time Qed.
Time Lemma cmra_mono_r x y z : x \226\137\188 y \226\134\146 x \226\139\133 z \226\137\188 y \226\139\133 z.
Time Proof.
Time by intros; rewrite -!(comm _ z); apply cmra_mono_l.
Time Qed.
Time
Lemma cmra_monoN n x1 x2 y1 y2 :
  x1 \226\137\188{n} y1 \226\134\146 x2 \226\137\188{n} y2 \226\134\146 x1 \226\139\133 x2 \226\137\188{n} y1 \226\139\133 y2.
Time Proof.
Time (intros; etrans; eauto using cmra_monoN_l, cmra_monoN_r).
Time Qed.
Time Lemma cmra_mono x1 x2 y1 y2 : x1 \226\137\188 y1 \226\134\146 x2 \226\137\188 y2 \226\134\146 x1 \226\139\133 x2 \226\137\188 y1 \226\139\133 y2.
Time Proof.
Time (intros; etrans; eauto using cmra_mono_l, cmra_mono_r).
Time Qed.
Time #[global]
Instance cmra_monoN'  n:
 (Proper (includedN n ==> includedN n ==> includedN n) (@op A _)).
Time Proof.
Time (intros x1 x2 Hx y1 y2 Hy).
Time by apply cmra_monoN.
Time Qed.
Time #[global]
Instance cmra_mono' : (Proper (included ==> included ==> included) (@op A _)).
Time Proof.
Time (intros x1 x2 Hx y1 y2 Hy).
Time by apply cmra_mono.
Time Qed.
Time
Lemma cmra_included_dist_l n x1 x2 x1' :
  x1 \226\137\188 x2 \226\134\146 x1' \226\137\161{n}\226\137\161 x1 \226\134\146 \226\136\131 x2', x1' \226\137\188 x2' \226\136\167 x2' \226\137\161{n}\226\137\161 x2.
Time Proof.
Time
(intros [z Hx2] Hx1; exists (x1' \226\139\133 z); split; auto using cmra_included_l).
Time by rewrite Hx1 Hx2.
Time Qed.
Time Section total_core.
Time #[local]Set Default Proof Using "Type*".
Time Context `{CmraTotal A}.
Time Lemma cmra_core_l x : core x \226\139\133 x \226\137\161 x.
Time Proof.
Time (destruct (cmra_total x) as [cx Hcx]).
Time by rewrite /core /= Hcx cmra_pcore_l.
Time Qed.
Time Lemma cmra_core_idemp x : core (core x) \226\137\161 core x.
Time Proof.
Time (destruct (cmra_total x) as [cx Hcx]).
Time by rewrite /core /= Hcx cmra_pcore_idemp.
Time Qed.
Time Lemma cmra_core_mono x y : x \226\137\188 y \226\134\146 core x \226\137\188 core y.
Time Proof.
Time (intros; destruct (cmra_total x) as [cx Hcx]).
Time (destruct (cmra_pcore_mono x y cx) as (cy, (Hcy, ?)); auto).
Time by rewrite /core /= Hcx Hcy.
Time Qed.
Time #[global]Instance cmra_core_ne : (NonExpansive (@core A _)).
Time Proof.
Time (intros n x y Hxy).
Time (destruct (cmra_total x) as [cx Hcx]).
Time by rewrite /core /= -Hxy Hcx.
Time Qed.
Time #[global]Instance cmra_core_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (@core A _)).
Time Proof.
Time (apply (ne_proper _)).
Time Qed.
Time Lemma cmra_core_r x : x \226\139\133 core x \226\137\161 x.
Time Proof.
Time by rewrite (comm _ x) cmra_core_l.
Time Qed.
Time Lemma cmra_core_dup x : core x \226\137\161 core x \226\139\133 core x.
Time Proof.
Time by rewrite -{+3}(cmra_core_idemp x) cmra_core_r.
Time Qed.
Time Lemma cmra_core_validN n x : \226\156\147{n} x \226\134\146 \226\156\147{n} core x.
Time Proof.
Time (rewrite -{+1}(cmra_core_l x); apply cmra_validN_op_l).
Time Qed.
Time Lemma cmra_core_valid x : \226\156\147 x \226\134\146 \226\156\147 core x.
Time Proof.
Time (rewrite -{+1}(cmra_core_l x); apply cmra_valid_op_l).
Time Qed.
Time Lemma core_id_total x : CoreId x \226\134\148 core x \226\137\161 x.
Time Proof.
Time (split; [ intros; by rewrite /core /= (core_id x) |  ]).
Time rewrite /CoreId /core /=.
Time (destruct (cmra_total x) as [? ->]).
Time by constructor.
Time Qed.
Time Lemma core_id_core x `{!CoreId x} : core x \226\137\161 x.
Time Proof.
Time by apply core_id_total.
Time Qed.
Time #[global]Instance cmra_core_core_id  x: (CoreId (core x)).
Time Proof.
Time (destruct (cmra_total x) as [cx Hcx]).
Time rewrite /CoreId /core /= Hcx /=.
Time eauto using cmra_pcore_idemp.
Time Qed.
Time Lemma cmra_included_core x : core x \226\137\188 x.
Time Proof.
Time by exists x; rewrite cmra_core_l.
Time Qed.
Time #[global]
Instance cmra_includedN_preorder  n: (PreOrder (@includedN A _ _ n)).
Time Proof.
Time (split; [  | apply _ ]).
Time by intros x; exists (core x); rewrite cmra_core_r.
Time Qed.
Time #[global]Instance cmra_included_preorder : (PreOrder (@included A _ _)).
Time Proof.
Time (split; [  | apply _ ]).
Time by intros x; exists (core x); rewrite cmra_core_r.
Time Qed.
Time Lemma cmra_core_monoN n x y : x \226\137\188{n} y \226\134\146 core x \226\137\188{n} core y.
Time Proof.
Time (intros [z ->]).
Time (apply cmra_included_includedN, cmra_core_mono, cmra_included_l).
Time Qed.
Time End total_core.
Time
Lemma cmra_discrete_included_l x y : Discrete x \226\134\146 \226\156\147{0} y \226\134\146 x \226\137\188{0} y \226\134\146 x \226\137\188 y.
Time Proof.
Time (intros ? ? [x' ?]).
Time
(destruct (cmra_extend 0 y x x') as (z, (z', (Hy, (Hz, Hz')))); auto;
  simpl in *).
Time by exists z'; rewrite Hy (discrete x z).
Time Qed.
Time Lemma cmra_discrete_included_r x y : Discrete y \226\134\146 x \226\137\188{0} y \226\134\146 x \226\137\188 y.
Time Proof.
Time (intros ? [x' ?]).
Time exists x'.
Time by apply (discrete y).
Time Qed.
Time
Lemma cmra_op_discrete x1 x2 :
  \226\156\147 (x1 \226\139\133 x2) \226\134\146 Discrete x1 \226\134\146 Discrete x2 \226\134\146 Discrete (x1 \226\139\133 x2).
Time Proof.
Time (intros ? ? ? z Hz).
Time
(destruct (cmra_extend 0 z x1 x2) as (y1, (y2, (Hz', (?, ?)))); auto;
  simpl in *).
Time {
Time rewrite -?Hz.
Time by apply cmra_valid_validN.
Time }
Time by rewrite Hz' (discrete x1 y1) // (discrete x2 y2).
Time Qed.
Time Lemma cmra_discrete_valid_iff `{CmraDiscrete A} n x : \226\156\147 x \226\134\148 \226\156\147{n} x.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> split ; first  by rewrite cmra_valid_validN).
Time eauto using cmra_discrete_valid, cmra_validN_le with lia.
Time Qed.
Time Lemma cmra_discrete_valid_iff_0 `{CmraDiscrete A} n x : \226\156\147{0} x \226\134\148 \226\156\147{n} x.
Time Proof.
Time by rewrite -!cmra_discrete_valid_iff.
Time Qed.
Time
Lemma cmra_discrete_included_iff `{OfeDiscrete A} n x y : x \226\137\188 y \226\134\148 x \226\137\188{n} y.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> split ; first  by
 apply cmra_included_includedN).
Time (intros [z ->%(discrete_iff _ _)]; eauto using cmra_included_l).
Time Qed.
Time
Lemma cmra_discrete_included_iff_0 `{OfeDiscrete A} 
  n x y : x \226\137\188{0} y \226\134\148 x \226\137\188{n} y.
Time Proof.
Time by rewrite -!cmra_discrete_included_iff.
Time Qed.
Time #[global]
Instance cancelable_proper : (Proper (equiv ==> iff) (@Cancelable A)).
Time Proof.
Time (unfold Cancelable).
Time (intros x x' EQ).
Time by setoid_rewrite EQ.
Time Qed.
Time
Lemma cancelable x `{!Cancelable x} y z : \226\156\147 (x \226\139\133 y) \226\134\146 x \226\139\133 y \226\137\161 x \226\139\133 z \226\134\146 y \226\137\161 z.
Time Proof.
Time rewrite !equiv_dist cmra_valid_validN.
Time (intros).
Time by apply (cancelableN x).
Time Qed.
Time
Lemma discrete_cancelable x `{CmraDiscrete A} :
  (\226\136\128 y z, \226\156\147 (x \226\139\133 y) \226\134\146 x \226\139\133 y \226\137\161 x \226\139\133 z \226\134\146 y \226\137\161 z) \226\134\146 Cancelable x.
Time Proof.
Time (intros ? ? ? ?).
Time rewrite -!discrete_iff -cmra_discrete_valid_iff.
Time auto.
Time Qed.
Time #[global]
Instance cancelable_op  x y:
 (Cancelable x \226\134\146 Cancelable y \226\134\146 Cancelable (x \226\139\133 y)).
Time Proof.
Time (intros ? ? n z z' ? ?).
Time (apply (cancelableN y), (cancelableN x)).
Time -
Time (eapply cmra_validN_op_r).
Time by rewrite assoc.
Time -
Time by rewrite assoc.
Time -
Time by rewrite !assoc.
Time Qed.
Time #[global]
Instance exclusive_cancelable  (x : A): (Exclusive x \226\134\146 Cancelable x).
Time Proof.
Time (intros ? n z z' []%(exclusiveN_l _ x)).
Time Qed.
Time #[global]Instance id_free_ne  n: (Proper (dist n ==> iff) (@IdFree A)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros x x' EQ%(dist_le _ 0) ; last  lia).
Time rewrite /IdFree.
Time
(<ssreflect_plugin::ssrtclintros@0> split =>y ?; rewrite -EQ || rewrite EQ;
  eauto).
Time Qed.
Time #[global]Instance id_free_proper : (Proper (equiv ==> iff) (@IdFree A)).
Time Proof.
Time
by <ssreflect_plugin::ssrtclintros@0> move  {}=>P Q /equiv_dist/(_ 0) =>{+}->.
Time Qed.
Time
Lemma id_freeN_r n n' x `{!IdFree x} y : \226\156\147{n} x \226\134\146 x \226\139\133 y \226\137\161{n'}\226\137\161 x \226\134\146 False.
Time Proof.
Time eauto using cmra_validN_le, dist_le with lia.
Time Qed.
Time
Lemma id_freeN_l n n' x `{!IdFree x} y : \226\156\147{n} x \226\134\146 y \226\139\133 x \226\137\161{n'}\226\137\161 x \226\134\146 False.
Time Proof.
Time rewrite comm.
Time eauto using id_freeN_r.
Time Qed.
Time Lemma id_free_r x `{!IdFree x} y : \226\156\147 x \226\134\146 x \226\139\133 y \226\137\161 x \226\134\146 False.
Time Proof.
Time move  {}=>/cmra_valid_validN ? /equiv_dist.
Time eauto.
Time Qed.
Time Lemma id_free_l x `{!IdFree x} y : \226\156\147 x \226\134\146 y \226\139\133 x \226\137\161 x \226\134\146 False.
Time Proof.
Time rewrite comm.
Time eauto using id_free_r.
Time Qed.
Time
Lemma discrete_id_free x `{CmraDiscrete A} :
  (\226\136\128 y, \226\156\147 x \226\134\146 x \226\139\133 y \226\137\161 x \226\134\146 False) \226\134\146 IdFree x.
Time Proof.
Time (intros Hx y ? ?).
Time (apply (Hx y), (discrete _); eauto using cmra_discrete_valid).
Time Qed.
Time #[global]
Instance id_free_op_r  x y: (IdFree y \226\134\146 Cancelable x \226\134\146 IdFree (x \226\139\133 y)).
Time Proof.
Time (intros ? ? z ? Hid%symmetry).
Time revert Hid.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite -assoc =>/(cancelableN x) ?).
Time
(eapply (id_free0_r _); [ by eapply cmra_validN_op_r | symmetry; eauto ]).
Time Qed.
Time #[global]
Instance id_free_op_l  x y: (IdFree x \226\134\146 Cancelable y \226\134\146 IdFree (x \226\139\133 y)).
Time Proof.
Time (intros).
Time rewrite comm.
Time (apply _).
Time Qed.
Time #[global]Instance exclusive_id_free  x: (Exclusive x \226\134\146 IdFree x).
Time Proof.
Time (intros ? z ? Hid).
Time (apply (exclusiveN_l 0 x z)).
Time by rewrite Hid.
Time Qed.
Time End cmra.
Time Section ucmra.
Time Context {A : ucmraT}.
Time Implicit Types x y z : A.
Time Lemma ucmra_unit_validN n : \226\156\147{n} (\206\181 : A).
Time Proof.
Time (apply cmra_valid_validN, ucmra_unit_valid).
Time Qed.
Time Lemma ucmra_unit_leastN n x : \206\181 \226\137\188{n} x.
Time Proof.
Time by exists x; rewrite left_id.
Time Qed.
Time Lemma ucmra_unit_least x : \206\181 \226\137\188 x.
Time Proof.
Time by exists x; rewrite left_id.
Time Qed.
Time #[global]Instance ucmra_unit_right_id : (RightId (\226\137\161) \206\181 (@op A _)).
Time Proof.
Time by intros x; rewrite (comm op) left_id.
Time Qed.
Time #[global]Instance ucmra_unit_core_id : (CoreId (\206\181 : A)).
Time Proof.
Time (apply ucmra_pcore_unit).
Time Qed.
Time #[global]Instance cmra_unit_cmra_total : (CmraTotal A).
Time Proof.
Time (intros x).
Time
(destruct (cmra_pcore_mono' \206\181 x \206\181) as (cx, (->, ?)); eauto
  using ucmra_unit_least, (core_id (\206\181 : A))).
Time Qed.
Time #[global]Instance empty_cancelable : (Cancelable (\206\181 : A)).
Time Proof.
Time (intros ? ? ?).
Time by rewrite !left_id.
Time Qed.
Time #[global]
Instance cmra_monoid : (Monoid (@op A _)) := {| monoid_unit := \206\181 |}.
Time End ucmra.
Time Hint Immediate cmra_unit_cmra_total: core.
Time Section cmra_leibniz.
Time #[local]Set Default Proof Using "Type*".
Time Context {A : cmraT} `{!LeibnizEquiv A}.
Time Implicit Types x y : A.
Time #[global]Instance cmra_assoc_L : (Assoc (=) (@op A _)).
Time Proof.
Time (intros x y z).
Time unfold_leibniz.
Time by rewrite assoc.
Time Qed.
Time #[global]Instance cmra_comm_L : (Comm (=) (@op A _)).
Time Proof.
Time (intros x y).
Time unfold_leibniz.
Time by rewrite comm.
Time Qed.
Time Lemma cmra_pcore_l_L x cx : pcore x = Some cx \226\134\146 cx \226\139\133 x = x.
Time Proof.
Time unfold_leibniz.
Time (apply cmra_pcore_l').
Time Qed.
Time Lemma cmra_pcore_idemp_L x cx : pcore x = Some cx \226\134\146 pcore cx = Some cx.
Time Proof.
Time unfold_leibniz.
Time (apply cmra_pcore_idemp').
Time Qed.
Time Lemma cmra_op_opM_assoc_L x y mz : x \226\139\133 y \226\139\133? mz = x \226\139\133 (y \226\139\133? mz).
Time Proof.
Time unfold_leibniz.
Time (apply cmra_op_opM_assoc).
Time Qed.
Time Lemma cmra_pcore_r_L x cx : pcore x = Some cx \226\134\146 x \226\139\133 cx = x.
Time Proof.
Time unfold_leibniz.
Time (apply cmra_pcore_r').
Time Qed.
Time Lemma cmra_pcore_dup_L x cx : pcore x = Some cx \226\134\146 cx = cx \226\139\133 cx.
Time Proof.
Time unfold_leibniz.
Time (apply cmra_pcore_dup').
Time Qed.
Time Lemma core_id_dup_L x `{!CoreId x} : x = x \226\139\133 x.
Time Proof.
Time unfold_leibniz.
Time by apply core_id_dup.
Time Qed.
Time Section total_core.
Time Context `{CmraTotal A}.
Time Lemma cmra_core_r_L x : x \226\139\133 core x = x.
Time Proof.
Time unfold_leibniz.
Time (apply cmra_core_r).
Time Qed.
Time Lemma cmra_core_l_L x : core x \226\139\133 x = x.
Time Proof.
Time unfold_leibniz.
Time (apply cmra_core_l).
Time Qed.
Time Lemma cmra_core_idemp_L x : core (core x) = core x.
Time Proof.
Time unfold_leibniz.
Time (apply cmra_core_idemp).
Time Qed.
Time Lemma cmra_core_dup_L x : core x = core x \226\139\133 core x.
Time Proof.
Time unfold_leibniz.
Time (apply cmra_core_dup).
Time Qed.
Time Lemma core_id_total_L x : CoreId x \226\134\148 core x = x.
Time Proof.
Time unfold_leibniz.
Time (apply core_id_total).
Time Qed.
Time Lemma core_id_core_L x `{!CoreId x} : core x = x.
Time Proof.
Time by apply core_id_total_L.
Time Qed.
Time End total_core.
Time End cmra_leibniz.
Time Section ucmra_leibniz.
Time #[local]Set Default Proof Using "Type*".
Time Context {A : ucmraT} `{!LeibnizEquiv A}.
Time Implicit Types x y z : A.
Time #[global]Instance ucmra_unit_left_id_L : (LeftId (=) \206\181 (@op A _)).
Time Proof.
Time (intros x).
Time unfold_leibniz.
Time by rewrite left_id.
Time Qed.
Time #[global]Instance ucmra_unit_right_id_L : (RightId (=) \206\181 (@op A _)).
Time Proof.
Time (intros x).
Time unfold_leibniz.
Time by rewrite right_id.
Time Qed.
Time End ucmra_leibniz.
Time Section cmra_total.
Time
Context A `{Dist A} `{Equiv A} `{PCore A} `{Op A} `{Valid A} `{ValidN A}.
Time Context (total : \226\136\128 x : A, is_Some (pcore x)).
Time Context (op_ne : \226\136\128 x : A, NonExpansive (op x)).
Time Context (core_ne : NonExpansive (@core A _)).
Time Context (validN_ne : \226\136\128 n, Proper (dist n ==> impl) (@validN A _ n)).
Time Context (valid_validN : \226\136\128 x : A, \226\156\147 x \226\134\148 (\226\136\128 n, \226\156\147{n} x)).
Time Context (validN_S : \226\136\128 n (x : A), \226\156\147{S n} x \226\134\146 \226\156\147{n} x).
Time Context (op_assoc : Assoc (\226\137\161) (@op A _)).
Time Context (op_comm : Comm (\226\137\161) (@op A _)).
Time Context (core_l : \226\136\128 x : A, core x \226\139\133 x \226\137\161 x).
Time Context (core_idemp : \226\136\128 x : A, core (core x) \226\137\161 core x).
Time Context (core_mono : \226\136\128 x y : A, x \226\137\188 y \226\134\146 core x \226\137\188 core y).
Time Context (validN_op_l : \226\136\128 n (x y : A), \226\156\147{n} (x \226\139\133 y) \226\134\146 \226\156\147{n} x).
Time
Context
 (extend : \226\136\128 n (x y1 y2 : A),
             \226\156\147{n} x
             \226\134\146 x \226\137\161{n}\226\137\161 y1 \226\139\133 y2
               \226\134\146 {z1 : A & {z2 | x \226\137\161 z1 \226\139\133 z2 \226\136\167 z1 \226\137\161{n}\226\137\161 y1 \226\136\167 z2 \226\137\161{n}\226\137\161 y2}}).
Time Lemma cmra_total_mixin : CmraMixin A.
Time Proof  using ((Type))*.
Time (split; auto).
Time -
Time (intros n x y ? Hcx%core_ne Hx; move : {}Hcx {}).
Time rewrite /core /= Hx /=.
Time (<ssreflect_plugin::ssrtclintros@0> case (total y) =>[cy {+}->]; eauto).
Time -
Time (intros x cx Hcx).
Time move : {}(core_l x) {}.
Time by rewrite /core /= Hcx.
Time -
Time (intros x cx Hcx).
Time move : {}(core_idemp x) {}.
Time rewrite /core /= Hcx /=.
Time
(<ssreflect_plugin::ssrtclintros@0> case (total cx) =>
  [ccx {+}->]; by constructor).
Time -
Time (intros x y cx Hxy%core_mono Hx).
Time move : {}Hxy {}.
Time rewrite /core /= Hx /=.
Time (<ssreflect_plugin::ssrtclintros@0> case (total y) =>[cy {+}->]; eauto).
Time Qed.
Time End cmra_total.
Time Instance cmra_morphism_id  {A : cmraT}: (CmraMorphism (@id A)).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> split =>//=).
Time (apply _).
Time (intros).
Time by rewrite option_fmap_id.
Time Qed.
Time
Instance cmra_morphism_proper  {A B : cmraT} (f : A \226\134\146 B) 
 `{!CmraMorphism f}: (Proper ((\226\137\161) ==> (\226\137\161)) f) := (ne_proper _).
Time
Instance cmra_morphism_compose  {A B C : cmraT} (f : A \226\134\146 B) 
 (g : B \226\134\146 C): (CmraMorphism f \226\134\146 CmraMorphism g \226\134\146 CmraMorphism (g \226\136\152 f)).
Time Proof.
Time split.
Time -
Time (apply _).
Time -
Time move  {}=>n x Hx /=.
Time by apply cmra_morphism_validN, cmra_morphism_validN.
Time -
Time move  {}=>x /=.
Time by rewrite 2!cmra_morphism_pcore option_fmap_compose.
Time -
Time move  {}=>x y /=.
Time by rewrite !cmra_morphism_op.
Time Qed.
Time Section cmra_morphism.
Time #[local]Set Default Proof Using "Type*".
Time Context {A B : cmraT} (f : A \226\134\146 B) `{!CmraMorphism f}.
Time Lemma cmra_morphism_core x : core (f x) \226\137\161 f (core x).
Time Proof.
Time (unfold core, core').
Time rewrite cmra_morphism_pcore.
Time by destruct (pcore x).
Time Qed.
Time Lemma cmra_morphism_monotone x y : x \226\137\188 y \226\134\146 f x \226\137\188 f y.
Time Proof.
Time (intros [z ->]).
Time exists (f z).
Time by rewrite cmra_morphism_op.
Time Qed.
Time Lemma cmra_morphism_monotoneN n x y : x \226\137\188{n} y \226\134\146 f x \226\137\188{n} f y.
Time Proof.
Time (intros [z ->]).
Time exists (f z).
Time by rewrite cmra_morphism_op.
Time Qed.
Time Lemma cmra_monotone_valid x : \226\156\147 x \226\134\146 \226\156\147 f x.
Time Proof.
Time (rewrite !cmra_valid_validN; eauto using cmra_morphism_validN).
Time Qed.
Time End cmra_morphism.
Time
Record rFunctor :=
 RFunctor {rFunctor_car : \226\136\128 A `{!Cofe A} B `{!Cofe B}, cmraT;
           rFunctor_map :
            forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} `{!Cofe B2},
            (A2 -n> A1) * (B1 -n> B2)
            \226\134\146 rFunctor_car A1 B1 -n> rFunctor_car A2 B2;
           rFunctor_ne :
            forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} `{!Cofe B2},
            NonExpansive (@rFunctor_map A1 _ A2 _ B1 _ B2 _);
           rFunctor_id :
            forall `{!Cofe A} `{!Cofe B} (x : rFunctor_car A B),
            rFunctor_map (cid, cid) x \226\137\161 x;
           rFunctor_compose :
            forall `{!Cofe A1} `{!Cofe A2} `{!Cofe A3} 
              `{!Cofe B1} `{!Cofe B2} `{!Cofe B3} 
              (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2)
              (g' : B2 -n> B3) x,
            rFunctor_map (f \226\151\142 g, g' \226\151\142 f') x
            \226\137\161 rFunctor_map (g, g') (rFunctor_map (f, f') x);
           rFunctor_mor :
            forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} 
              `{!Cofe B2} (fg : (A2 -n> A1) * (B1 -n> B2)),
            CmraMorphism (rFunctor_map fg)}.
Time Existing Instances rFunctor_ne, rFunctor_mor.
Time Instance: (Params (@rFunctor_map) 9) := { }.
Time Delimit Scope rFunctor_scope with RF.
Time Bind Scope rFunctor_scope with rFunctor.
Time
Class rFunctorContractive (F : rFunctor) :=
    rFunctor_contractive :>
      forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} `{!Cofe B2},
      Contractive (@rFunctor_map F A1 _ A2 _ B1 _ B2 _).
Time
Definition rFunctor_diag (F : rFunctor) (A : ofeT) 
  `{!Cofe A} : cmraT := rFunctor_car F A A.
Time Coercion rFunctor_diag : rFunctor >-> Funclass.
Time #[program]
Definition constRF (B : cmraT) : rFunctor :=
  {|
  rFunctor_car := fun A1 _ A2 _ => B;
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ f => cid |}.
Time Solve Obligations with done.
Time Coercion constRF : cmraT >-> rFunctor.
Time Instance constRF_contractive  B: (rFunctorContractive (constRF B)).
Time Proof.
Time (rewrite /rFunctorContractive; apply _).
Time Qed.
Time
Record urFunctor :=
 URFunctor {urFunctor_car : \226\136\128 A `{!Cofe A} B `{!Cofe B}, ucmraT;
            urFunctor_map :
             forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} `{!Cofe B2},
             (A2 -n> A1) * (B1 -n> B2)
             \226\134\146 urFunctor_car A1 B1 -n> urFunctor_car A2 B2;
            urFunctor_ne :
             forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} `{!Cofe B2},
             NonExpansive (@urFunctor_map A1 _ A2 _ B1 _ B2 _);
            urFunctor_id :
             forall `{!Cofe A} `{!Cofe B} (x : urFunctor_car A B),
             urFunctor_map (cid, cid) x \226\137\161 x;
            urFunctor_compose :
             forall `{!Cofe A1} `{!Cofe A2} `{!Cofe A3} 
               `{!Cofe B1} `{!Cofe B2} `{!Cofe B3} 
               (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2)
               (g' : B2 -n> B3) x,
             urFunctor_map (f \226\151\142 g, g' \226\151\142 f') x
             \226\137\161 urFunctor_map (g, g') (urFunctor_map (f, f') x);
            urFunctor_mor :
             forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} 
               `{!Cofe B2} (fg : (A2 -n> A1) * (B1 -n> B2)),
             CmraMorphism (urFunctor_map fg)}.
Time Existing Instances urFunctor_ne, urFunctor_mor.
Time Instance: (Params (@urFunctor_map) 9) := { }.
Time Delimit Scope urFunctor_scope with URF.
Time Bind Scope urFunctor_scope with urFunctor.
Time
Class urFunctorContractive (F : urFunctor) :=
    urFunctor_contractive :>
      forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} `{!Cofe B2},
      Contractive (@urFunctor_map F A1 _ A2 _ B1 _ B2 _).
Time
Definition urFunctor_diag (F : urFunctor) (A : ofeT) 
  `{!Cofe A} : ucmraT := urFunctor_car F A A.
Time Coercion urFunctor_diag : urFunctor >-> Funclass.
Time #[program]
Definition constURF (B : ucmraT) : urFunctor :=
  {|
  urFunctor_car := fun A1 _ A2 _ => B;
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ f => cid |}.
Time Solve Obligations with done.
Time Coercion constURF : ucmraT >-> urFunctor.
Time Instance constURF_contractive  B: (urFunctorContractive (constURF B)).
Time Proof.
Time (rewrite /urFunctorContractive; apply _).
Time Qed.
Time
Definition cmra_transport {A B : cmraT} (H : A = B) 
  (x : A) : B := eq_rect A id x _ H.
Time Section cmra_transport.
Time Context {A B : cmraT} (H : A = B).
Time Notation T := (cmra_transport H).
Time #[global]Instance cmra_transport_ne : (NonExpansive T).
Time Proof.
Time by intros ? ? ?; destruct H.
Time Qed.
Time #[global]Instance cmra_transport_proper : (Proper ((\226\137\161) ==> (\226\137\161)) T).
Time Proof.
Time by intros ? ? ?; destruct H.
Time Qed.
Time Lemma cmra_transport_op x y : T (x \226\139\133 y) = T x \226\139\133 T y.
Time Proof.
Time by destruct H.
Time Qed.
Time Lemma cmra_transport_core x : T (core x) = core (T x).
Time Proof.
Time by destruct H.
Time Qed.
Time Lemma cmra_transport_validN n x : \226\156\147{n} T x \226\134\148 \226\156\147{n} x.
Time Proof.
Time by destruct H.
Time Qed.
Time Lemma cmra_transport_valid x : \226\156\147 T x \226\134\148 \226\156\147 x.
Time Proof.
Time by destruct H.
Time Qed.
Time #[global]
Instance cmra_transport_discrete  x: (Discrete x \226\134\146 Discrete (T x)).
Time Proof.
Time by destruct H.
Time Qed.
Time #[global]Instance cmra_transport_core_id  x: (CoreId x \226\134\146 CoreId (T x)).
Time Proof.
Time by destruct H.
Time Qed.
Time End cmra_transport.
Time
Record RAMixin A `{Equiv A} `{PCore A} `{Op A} `{Valid A} :={
 ra_op_proper : forall x : A, Proper ((\226\137\161) ==> (\226\137\161)) (op x);
 ra_core_proper :
  forall (x y : A) cx,
  x \226\137\161 y \226\134\146 pcore x = Some cx \226\134\146 \226\136\131 cy, pcore y = Some cy \226\136\167 cx \226\137\161 cy;
 ra_validN_proper : Proper ((\226\137\161@{A} ) ==> impl) valid;
 ra_assoc : Assoc (\226\137\161@{A} ) (\226\139\133);
 ra_comm : Comm (\226\137\161@{A} ) (\226\139\133);
 ra_pcore_l : forall (x : A) cx, pcore x = Some cx \226\134\146 cx \226\139\133 x \226\137\161 x;
 ra_pcore_idemp : forall (x : A) cx, pcore x = Some cx \226\134\146 pcore cx \226\137\161 Some cx;
 ra_pcore_mono :
  forall (x y : A) cx,
  x \226\137\188 y \226\134\146 pcore x = Some cx \226\134\146 \226\136\131 cy, pcore y = Some cy \226\136\167 cx \226\137\188 cy;
 ra_valid_op_l : forall x y : A, \226\156\147 (x \226\139\133 y) \226\134\146 \226\156\147 x}.
Time Section discrete.
Time #[local]Set Default Proof Using "Type*".
Time
Context `{Equiv A} `{PCore A} `{Op A} `{Valid A} (Heq : @Equivalence A (\226\137\161)).
Time Context (ra_mix : RAMixin A).
Time Existing Instance discrete_dist.
Time Instance discrete_validN : (ValidN A) := (\206\187 n x, \226\156\147 x).
Time Definition discrete_cmra_mixin : CmraMixin A.
Time Proof.
Time (destruct ra_mix; split; try done).
Time -
Time (<ssreflect_plugin::ssrtclseq@0> intros x; split ; first  done).
Time by move  {}=>/(_ 0).
Time -
Time (intros n x y1 y2 ? ?; by exists y1,y2).
Time Qed.
Time
Instance discrete_cmra_discrete :
 (CmraDiscrete (CmraT' A (discrete_ofe_mixin Heq) discrete_cmra_mixin A)).
Time Proof.
Time split.
Time (apply _).
Time done.
Time Qed.
Time End discrete.
Time
Notation discreteR A ra_mix:=
  (CmraT A (discrete_cmra_mixin (discrete_ofe_equivalence_of A%type) ra_mix))
  (only parsing).
Time Section ra_total.
Time #[local]Set Default Proof Using "Type*".
Time Context A `{Equiv A} `{PCore A} `{Op A} `{Valid A}.
Time Context (total : \226\136\128 x : A, is_Some (pcore x)).
Time Context (op_proper : \226\136\128 x : A, Proper ((\226\137\161) ==> (\226\137\161)) (op x)).
Time Context (core_proper : Proper ((\226\137\161) ==> (\226\137\161)) (@core A _)).
Time Context (valid_proper : Proper ((\226\137\161) ==> impl) (@valid A _)).
Time Context (op_assoc : Assoc (\226\137\161) (@op A _)).
Time Context (op_comm : Comm (\226\137\161) (@op A _)).
Time Context (core_l : \226\136\128 x : A, core x \226\139\133 x \226\137\161 x).
Time Context (core_idemp : \226\136\128 x : A, core (core x) \226\137\161 core x).
Time Context (core_mono : \226\136\128 x y : A, x \226\137\188 y \226\134\146 core x \226\137\188 core y).
Time Context (valid_op_l : \226\136\128 x y : A, \226\156\147 (x \226\139\133 y) \226\134\146 \226\156\147 x).
Time Lemma ra_total_mixin : RAMixin A.
Time Proof.
Time (split; auto).
Time -
Time (intros x y ? Hcx%core_proper Hx; move : {}Hcx {}).
Time rewrite /core /= Hx /=.
Time (<ssreflect_plugin::ssrtclintros@0> case (total y) =>[cy {+}->]; eauto).
Time -
Time (intros x cx Hcx).
Time move : {}(core_l x) {}.
Time by rewrite /core /= Hcx.
Time -
Time (intros x cx Hcx).
Time move : {}(core_idemp x) {}.
Time rewrite /core /= Hcx /=.
Time
(<ssreflect_plugin::ssrtclintros@0> case (total cx) =>
  [ccx {+}->]; by constructor).
Time -
Time (intros x y cx Hxy%core_mono Hx).
Time move : {}Hxy {}.
Time rewrite /core /= Hx /=.
Time (<ssreflect_plugin::ssrtclintros@0> case (total y) =>[cy {+}->]; eauto).
Time Qed.
Time End ra_total.
Time Section unit.
Time Instance unit_valid : (Valid ()) := (\206\187 x, True).
Time Instance unit_validN : (ValidN ()) := (\206\187 n x, True).
Time Instance unit_pcore : (PCore ()) := (\206\187 x, Some x).
Time Instance unit_op : (Op ()) := (\206\187 x y, ()).
Time Lemma unit_cmra_mixin : CmraMixin ().
Time Proof.
Time (apply discrete_cmra_mixin, ra_total_mixin; by eauto).
Time Qed.
Time Canonical Structure unitR : cmraT := CmraT unit unit_cmra_mixin.
Time Instance unit_unit : (Unit ()) := ().
Time Lemma unit_ucmra_mixin : UcmraMixin ().
Time Proof.
Time done.
Time Qed.
Time Canonical Structure unitUR : ucmraT := UcmraT unit unit_ucmra_mixin.
Time #[global]Instance unit_cmra_discrete : (CmraDiscrete unitR).
Time Proof.
Time done.
Time Qed.
Time #[global]Instance unit_core_id  (x : ()): (CoreId x).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance unit_cancelable  (x : ()): (Cancelable x).
Time Proof.
Time by constructor.
Time Qed.
Time End unit.
Time Section nat.
Time Instance nat_valid : (Valid nat) := (\206\187 x, True).
Time Instance nat_validN : (ValidN nat) := (\206\187 n x, True).
Time Instance nat_pcore : (PCore nat) := (\206\187 x, Some 0).
Time Instance nat_op : (Op nat) := plus.
Time Definition nat_op_plus x y : x \226\139\133 y = x + y := eq_refl.
Time Lemma nat_included (x y : nat) : x \226\137\188 y \226\134\148 x \226\137\164 y.
Time Proof.
Time by rewrite nat_le_sum.
Time Qed.
Time Lemma nat_ra_mixin : RAMixin nat.
Time Proof.
Time (apply ra_total_mixin; try by eauto).
Time -
Time solve_proper.
Time -
Time (intros x y z).
Time (apply Nat.add_assoc).
Time -
Time (intros x y).
Time (apply Nat.add_comm).
Time -
Time by exists 0.
Time Qed.
Time Canonical Structure natR : cmraT := discreteR nat nat_ra_mixin.
Time #[global]Instance nat_cmra_discrete : (CmraDiscrete natR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Instance nat_unit : (Unit nat) := 0.
Time Lemma nat_ucmra_mixin : UcmraMixin nat.
Time Proof.
Time (split; apply _ || done).
Time Qed.
Time Canonical Structure natUR : ucmraT := UcmraT nat nat_ucmra_mixin.
Time #[global]Instance nat_cancelable  (x : nat): (Cancelable x).
Time Proof.
Time by intros ? ? ? ? ?%Nat.add_cancel_l.
Time Qed.
Time End nat.
Time Definition mnat := nat.
Time Section mnat.
Time Instance mnat_unit : (Unit mnat) := 0.
Time Instance mnat_valid : (Valid mnat) := (\206\187 x, True).
Time Instance mnat_validN : (ValidN mnat) := (\206\187 n x, True).
Time Instance mnat_pcore : (PCore mnat) := Some.
Time Instance mnat_op : (Op mnat) := Nat.max.
Time Definition mnat_op_max x y : x \226\139\133 y = x `max` y := eq_refl.
Time Lemma mnat_included (x y : mnat) : x \226\137\188 y \226\134\148 x \226\137\164 y.
Time Proof.
Time split.
Time -
Time (intros [z ->]; unfold op, mnat_op; lia).
Time -
Time exists y.
Time by symmetry; apply Nat.max_r.
Time Qed.
Time Lemma mnat_ra_mixin : RAMixin mnat.
Time Proof.
Time (apply ra_total_mixin; try by eauto).
Time -
Time solve_proper.
Time -
Time solve_proper.
Time -
Time (intros x y z).
Time (apply Nat.max_assoc).
Time -
Time (intros x y).
Time (apply Nat.max_comm).
Time -
Time (intros x).
Time (apply Max.max_idempotent).
Time Qed.
Time Canonical Structure mnatR : cmraT := discreteR mnat mnat_ra_mixin.
Time #[global]Instance mnat_cmra_discrete : (CmraDiscrete mnatR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time Lemma mnat_ucmra_mixin : UcmraMixin mnat.
Time Proof.
Time (split; apply _ || done).
Time Qed.
Time Canonical Structure mnatUR : ucmraT := UcmraT mnat mnat_ucmra_mixin.
Time #[global]Instance mnat_core_id  (x : mnat): (CoreId x).
Time Proof.
Time by constructor.
Time Qed.
Time End mnat.
Time Section positive.
Time Instance pos_valid : (Valid positive) := (\206\187 x, True).
Time Instance pos_validN : (ValidN positive) := (\206\187 n x, True).
Time Instance pos_pcore : (PCore positive) := (\206\187 x, None).
Time Instance pos_op : (Op positive) := Pos.add.
Time Definition pos_op_plus x y : x \226\139\133 y = (x + y)%positive := eq_refl.
Time Lemma pos_included (x y : positive) : x \226\137\188 y \226\134\148 (x < y)%positive.
Time Proof.
Time by rewrite Plt_sum.
Time Qed.
Time Lemma pos_ra_mixin : RAMixin positive.
Time Proof.
Time (split; try by eauto).
Time -
Time by intros ? ? ? ->.
Time -
Time (intros ? ? ?).
Time (apply Pos.add_assoc).
Time -
Time (intros ? ?).
Time (apply Pos.add_comm).
Time Qed.
Time
Canonical Structure positiveR : cmraT := discreteR positive pos_ra_mixin.
Time #[global]Instance pos_cmra_discrete : (CmraDiscrete positiveR).
Time Proof.
Time (apply discrete_cmra_discrete).
Time Qed.
Time #[global]Instance pos_cancelable  (x : positive): (Cancelable x).
Time Proof.
Time (intros n y z ? ?).
Time by eapply Pos.add_reg_l, leibniz_equiv.
Time Qed.
Time #[global]Instance pos_id_free  (x : positive): (IdFree x).
Time Proof.
Time (intros y ? ?).
Time (apply (Pos.add_no_neutral x y)).
Time rewrite Pos.add_comm.
Time by apply leibniz_equiv.
Time Qed.
Time End positive.
Time Section prod.
Time Context {A B : cmraT}.
Time #[local]Arguments pcore _ _ !_ /.
Time #[local]Arguments cmra_pcore _ !_ /.
Time Instance prod_op : (Op (A * B)) := (\206\187 x y, (x.1 \226\139\133 y.1, x.2 \226\139\133 y.2)).
Time
Instance prod_pcore : (PCore (A * B)) :=
 (\206\187 x, c1 \226\134\144 pcore x.1; c2 \226\134\144 pcore x.2; Some (c1, c2)).
Time Arguments prod_pcore !_ /.
Time Instance prod_valid : (Valid (A * B)) := (\206\187 x, \226\156\147 x.1 \226\136\167 \226\156\147 x.2).
Time Instance prod_validN : (ValidN (A * B)) := (\206\187 n x, \226\156\147{n} x.1 \226\136\167 \226\156\147{n} x.2).
Time
Lemma prod_pcore_Some (x cx : A * B) :
  pcore x = Some cx \226\134\148 pcore x.1 = Some cx.1 \226\136\167 pcore x.2 = Some cx.2.
Time Proof.
Time (destruct x, cx; by intuition simplify_option_eq).
Time by apply (contractive_S map).
Time Qed.
Time
Lemma prod_pcore_Some' (x cx : A * B) :
  pcore x \226\137\161 Some cx \226\134\148 pcore x.1 \226\137\161 Some cx.1 \226\136\167 pcore x.2 \226\137\161 Some cx.2.
Time Proof.
Time
(split;
  [ by intros (cx', ([-> ->]%prod_pcore_Some, ->))%equiv_Some_inv_r' |  ]).
Time rewrite {+3}/pcore /prod_pcore.
Time (intros [Hx1 Hx2]; inversion_clear Hx1; simpl; inversion_clear Hx2).
Time by constructor.
Time Qed.
Time Lemma prod_included (x y : A * B) : x \226\137\188 y \226\134\148 x.1 \226\137\188 y.1 \226\136\167 x.2 \226\137\188 y.2.
Time Proof.
Time
(split; [ intros [z Hz]; split; [ exists z.1 | exists z.2 ]; apply Hz |  ]).
Time (intros [[z1 Hz1] [z2 Hz2]]; exists (z1, z2); split; auto).
Time Qed.
Time
Lemma prod_includedN (x y : A * B) n : x \226\137\188{n} y \226\134\148 x.1 \226\137\188{n} y.1 \226\136\167 x.2 \226\137\188{n} y.2.
Time Proof.
Time
(split; [ intros [z Hz]; split; [ exists z.1 | exists z.2 ]; apply Hz |  ]).
Time (intros [[z1 Hz1] [z2 Hz2]]; exists (z1, z2); split; auto).
Time Qed.
Time Definition prod_cmra_mixin : CmraMixin (A * B).
Time Proof.
Time (split; try apply _).
Time -
Time by intros n x y1 y2 [Hy1 Hy2]; split; rewrite /= ?Hy1 ?Hy2.
Time Qed.
Time -
Time
(intros n x y cx; <ssreflect_plugin::ssrtclintros@0> setoid_rewrite
  prod_pcore_Some =>- [? ?] [? ?]).
Time (destruct (cmra_pcore_ne n x.1 y.1 cx.1) as (z1, (->, ?)); auto).
Time (destruct (cmra_pcore_ne n x.2 y.2 cx.2) as (z2, (->, ?)); auto).
Time (exists (z1, z2); repeat constructor; auto).
Time -
Time by intros n y1 y2 [Hy1 Hy2] [? ?]; split; rewrite /= -?Hy1 -?Hy2.
Time -
Time (intros x; split).
Time +
Time (intros [? ?] n; split; by apply cmra_valid_validN).
Time +
Time
(intros Hxy; split; <ssreflect_plugin::ssrtclintros@0>
  apply cmra_valid_validN =>n; apply Hxy).
Time -
Time by intros n x [? ?]; split; apply cmra_validN_S.
Time -
Time by split; rewrite /= assoc.
Time -
Time by split; rewrite /= comm.
Time -
Time
(intros x y [? ?]%prod_pcore_Some; constructor; simpl; eauto
  using cmra_pcore_l).
Time -
Time (intros x y; rewrite prod_pcore_Some prod_pcore_Some').
Time naive_solver eauto using cmra_pcore_idemp.
Time -
Time
(intros x y cx; <ssreflect_plugin::ssrtclintros@0> rewrite prod_included
  prod_pcore_Some =>- [? ?] [? ?]).
Time (destruct (cmra_pcore_mono x.1 y.1 cx.1) as (z1, (?, ?)); auto).
Time (destruct (cmra_pcore_mono x.2 y.2 cx.2) as (z2, (?, ?)); auto).
Time exists (z1, z2).
Time by rewrite prod_included prod_pcore_Some.
Time -
Time (intros n x y [? ?]; split; simpl in *; eauto using cmra_validN_op_l).
Time -
Time (intros n x y1 y2 [? ?] [? ?]; simpl in *).
Time
(destruct (cmra_extend n x.1 y1.1 y2.1) as (z11, (z12, (?, (?, ?)))); auto).
Time
(destruct (cmra_extend n x.2 y1.2 y2.2) as (z21, (z22, (?, (?, ?)))); auto).
Time by exists (z11, z21),(z12, z22).
Time Qed.
Time Canonical Structure prodR := CmraT (prod A B) prod_cmra_mixin.
Time
Lemma pair_op (a a' : A) (b b' : B) : (a, b) \226\139\133 (a', b') = (a \226\139\133 a', b \226\139\133 b').
Time Proof.
Time done.
Time Qed.
Time Lemma pair_valid (a : A) (b : B) : \226\156\147 (a, b) \226\134\148 \226\156\147 a \226\136\167 \226\156\147 b.
Time Proof.
Time done.
Time Qed.
Time #[global]
Instance prod_cmra_total : (CmraTotal A \226\134\146 CmraTotal B \226\134\146 CmraTotal prodR).
Time Proof.
Time (intros H1 H2 [a b]).
Time (destruct (H1 a) as [ca ?], (H2 b) as [cb ?]).
Time (exists (ca, cb); by simplify_option_eq).
Time Qed.
Time #[global]
Instance prod_cmra_discrete :
 (CmraDiscrete A \226\134\146 CmraDiscrete B \226\134\146 CmraDiscrete prodR).
Time Proof.
Time split.
Time (apply _).
Time by intros ? []; split; apply cmra_discrete_valid.
Time Qed.
Time #[global]
Instance pair_core_id  x y: (CoreId x \226\134\146 CoreId y \226\134\146 CoreId (x, y)).
Time Proof.
Time by rewrite /CoreId prod_pcore_Some'.
Time Qed.
Time #[global]
Instance pair_exclusive_l  x y: (Exclusive x \226\134\146 Exclusive (x, y)).
Time Proof.
Time by intros ? [] [?%exclusive0_l].
Time Qed.
Time #[global]
Instance pair_exclusive_r  x y: (Exclusive y \226\134\146 Exclusive (x, y)).
Time Proof.
Time by intros ? [] [? ?%exclusive0_l].
Time Qed.
Time #[global]
Instance pair_cancelable  x y:
 (Cancelable x \226\134\146 Cancelable y \226\134\146 Cancelable (x, y)).
Time Proof.
Time (intros ? ? ? [] [] [] []).
Time (constructor; simpl in *; by eapply cancelableN).
Time Qed.
Time #[global]Instance pair_id_free_l  x y: (IdFree x \226\134\146 IdFree (x, y)).
Time Proof.
Time move  {}=>? [? ?] [? _] [/= ? _].
Time eauto.
Time Qed.
Time #[global]Instance pair_id_free_r  x y: (IdFree y \226\134\146 IdFree (x, y)).
Time Proof.
Time move  {}=>? [? ?] [_ ?] [_ /= ?].
Time eauto.
Time Qed.
Time End prod.
Time Arguments prodR : clear implicits.
Time Section prod_unit.
Time Context {A B : ucmraT}.
Time Instance prod_unit  `{Unit A} `{Unit B}: (Unit (A * B)) := (\206\181, \206\181).
Time Lemma prod_ucmra_mixin : UcmraMixin (A * B).
Time Proof.
Time split.
Time -
Time (split; apply ucmra_unit_valid).
Time -
Time by split; rewrite /= left_id.
Time -
Time (rewrite prod_pcore_Some'; split; apply (core_id _)).
Time Qed.
Time Canonical Structure prodUR := UcmraT (prod A B) prod_ucmra_mixin.
Time Lemma pair_split (x : A) (y : B) : (x, y) \226\137\161 (x, \206\181) \226\139\133 (\206\181, y).
Time Proof.
Time by rewrite pair_op left_id right_id.
Time Qed.
Time
Lemma pair_split_L `{!LeibnizEquiv A} `{!LeibnizEquiv B} 
  (x : A) (y : B) : (x, y) = (x, \206\181) \226\139\133 (\206\181, y).
Time Proof.
Time unfold_leibniz.
Time (apply pair_split).
Time Qed.
Time End prod_unit.
Time Arguments prodUR : clear implicits.
Time
Instance prod_map_cmra_morphism  {A A' B B' : cmraT} 
 (f : A \226\134\146 A') (g : B \226\134\146 B'):
 (CmraMorphism f \226\134\146 CmraMorphism g \226\134\146 CmraMorphism (prod_map f g)).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time -
Time by intros n x [? ?]; split; simpl; apply cmra_morphism_validN.
Time -
Time (intros x).
Time etrans.
Time (apply (reflexivity (mbind _ _))).
Time
(<ssreflect_plugin::ssrtclseq@0> etrans ; last 
 apply (reflexivity (_ <$> mbind _ _))).
Time (simpl).
Time (pose proof (cmra_morphism_pcore f x.1) as Hf).
Time
(destruct (pcore (f x.1)), (pcore x.1); <ssreflect_plugin::ssrtclintros@0>
  inversion_clear Hf =>//=).
Time (pose proof (cmra_morphism_pcore g x.2) as Hg).
Time
(destruct (pcore (g x.2)), (pcore x.2); <ssreflect_plugin::ssrtclintros@0>
  inversion_clear Hg =>//=).
Time by setoid_subst.
Time -
Time (intros).
Time by rewrite /prod_map /= -!cmra_morphism_op.
Time Qed.
Time #[program]
Definition prodRF (F1 F2 : rFunctor) : rFunctor :=
  {|
  rFunctor_car := fun A _ B _ =>
                  prodR (rFunctor_car F1 A B) (rFunctor_car F2 A B);
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  prodC_map (rFunctor_map F1 fg) (rFunctor_map F2 fg) |}.
Time Next Obligation.
Time
Record tower :={tower_car :> forall k, A k;
                g_tower : forall k, g k (tower_car (S k)) \226\137\161 tower_car k}.
Time Instance tower_equiv : (Equiv tower) := (\206\187 X Y, \226\136\128 k, X k \226\137\161 Y k).
Time Instance tower_dist : (Dist tower) := (\206\187 n X Y, \226\136\128 k, X k \226\137\161{n}\226\137\161 Y k).
Time Definition tower_ofe_mixin : OfeMixin tower.
Time Proof.
Time split.
Time -
Time (intros X Y; split; [ by intros HXY n k; apply equiv_dist |  ]).
Time (intros HXY k; apply equiv_dist; intros n; apply HXY).
Time -
Time (intros k; split).
Time +
Time by intros X n.
Time +
Time by intros X Y ? n.
Time +
Time by intros X Y Z ? ? n; trans Y n.
Time -
Time (intros k X Y HXY n; apply dist_S).
Time by rewrite -(g_tower X) (HXY (S n)) g_tower.
Time Qed.
Time Definition T : ofeT := OfeT tower tower_ofe_mixin.
Time #[program]
Definition tower_chain (c : chain T) (k : nat) : chain (A k) :=
  {| chain_car := fun i => c i k |}.
Time Next Obligation.
Time (intros c k n i ?; apply (chain_cauchy c n); lia).
Time Qed.
Time #[program]
Definition tower_compl : Compl T :=
  \206\187 c, {| tower_car := fun n => compl (tower_chain c n) |}.
Time Next Obligation.
Time (intros c k; <ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time
by rewrite (conv_compl n (tower_chain c k))
 (conv_compl n (tower_chain c (S k))) /= (g_tower (c _) k).
Time Qed.
Time #[global, program]
Instance tower_cofe : (Cofe T) := { compl :=tower_compl}.
Time Next Obligation.
Time (intros n c k; rewrite /= (conv_compl n (tower_chain c k))).
Time (apply (chain_cauchy c); lia).
Time (intros F1 F2 A1 ? A2 ? B1 ? B2 ? n ? ? ?).
Time by apply prodC_map_ne; apply rFunctor_ne.
Time Qed.
Time Qed.
Time Next Obligation.
Time by intros F1 F2 A ? B ? [? ?]; rewrite /= !rFunctor_id.
Time
Fixpoint ff {k} (i : nat) : A k -n> A (i + k) :=
  match i with
  | 0 => cid
  | S i => f (i + k) \226\151\142 ff i
  end.
Time
Fixpoint gg {k} (i : nat) : A (i + k) -n> A k :=
  match i with
  | 0 => cid
  | S i => gg i \226\151\142 g (i + k)
  end.
Time Lemma ggff {k} {i} (x : A k) : gg i (ff i x) \226\137\161 x.
Time Proof  using (Fcontr).
Time
(induction i as [| i IH]; simpl; [ done | by rewrite (gf (ff i x)) IH ]).
Time Qed.
Time Next Obligation.
Time (intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [? ?]; simpl).
Time by rewrite !rFunctor_compose.
Time Qed.
Time Lemma f_tower k (X : tower) : f (S k) (X (S k)) \226\137\161{k}\226\137\161 X (S (S k)).
Time Proof  using (Fcontr).
Time (intros).
Time by rewrite -(fg (X (S (S k)))) -(g_tower X).
Time Qed.
Time Notation "F1 * F2" := (prodRF F1%RF F2%RF) : rFunctor_scope.
Time
Instance prodRF_contractive  F1 F2:
 (rFunctorContractive F1
  \226\134\146 rFunctorContractive F2 \226\134\146 rFunctorContractive (prodRF F1 F2)).
Time Proof.
Time
(intros ? ? A1 ? A2 ? B1 ? B2 ? n ? ? ?; by
  apply prodC_map_ne; apply rFunctor_contractive).
Time Qed.
Time Qed.
Time Lemma ff_tower k i (X : tower) : ff i (X (S k)) \226\137\161{k}\226\137\161 X (i + S k).
Time Proof  using (Fcontr).
Time (intros; induction i as [| i IH]; simpl; [ done |  ]).
Time #[program]
Definition prodURF (F1 F2 : urFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ =>
                   prodUR (urFunctor_car F1 A B) (urFunctor_car F2 A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   prodC_map (urFunctor_map F1 fg) (urFunctor_map F2 fg) |}.
Time
by <ssreflect_plugin::ssrtclseq@0> rewrite IH Nat.add_succ_r
 (dist_le _ _ _ _ (f_tower _ X)) ; last  lia.
Time Qed.
Time Lemma gg_tower k i (X : tower) : gg i (X (i + k)) \226\137\161 X k.
Time Proof.
Time by induction i as [| i IH]; simpl; [ done | rewrite g_tower IH ].
Time Qed.
Time Instance tower_car_ne  k: (NonExpansive (\206\187 X, tower_car X k)).
Time Proof.
Time by intros X Y HX.
Time Qed.
Time
Definition project (k : nat) : T -n> A k := CofeMor (\206\187 X : T, tower_car X k).
Time
Definition coerce {i} {j} (H : i = j) : A i -n> A j :=
  eq_rect _ (\206\187 i', A i -n> A i') cid _ H.
Time Lemma coerce_id {i} (H : i = i) (x : A i) : coerce H x = x.
Time Proof.
Time (unfold coerce).
Time by rewrite (proof_irrel H (eq_refl i)).
Time Qed.
Time
Lemma coerce_proper {i} {j} (x y : A i) (H1 H2 : i = j) :
  x = y \226\134\146 coerce H1 x = coerce H2 y.
Time Proof.
Time by destruct H1; rewrite !coerce_id.
Time Qed.
Time
Lemma g_coerce {k} {j} (H : S k = S j) (x : A (S k)) :
  g j (coerce H x) = coerce (Nat.succ_inj _ _ H) (g k x).
Time Proof.
Time by assert (k = j) by lia; subst; rewrite !coerce_id.
Time Qed.
Time
Lemma coerce_f {k} {j} (H : S k = S j) (x : A k) :
  coerce H (f k x) = f j (coerce (Nat.succ_inj _ _ H) x).
Time Proof.
Time by assert (k = j) by lia; subst; rewrite !coerce_id.
Time Qed.
Time
Lemma gg_gg {k} {i} {i1} {i2} {j} :
  \226\136\128 (H1 : k = i + j) (H2 : k = i2 + (i1 + j)) (x : A k),
    gg i (coerce H1 x) = gg i1 (gg i2 (coerce H2 x)).
Time Proof.
Time (intros ? -> x).
Time (assert (i = i2 + i1) as -> by lia).
Time revert j x H1.
Time
(induction i2 as [| i2 IH]; intros j X H1; simplify_eq /=;
  [ by rewrite coerce_id | by rewrite g_coerce IH ]).
Time Qed.
Time Next Obligation.
Time (intros F1 F2 A1 ? A2 ? B1 ? B2 ? n ? ? ?).
Time by apply prodC_map_ne; apply urFunctor_ne.
Time Qed.
Time Next Obligation.
Time by intros F1 F2 A ? B ? [? ?]; rewrite /= !urFunctor_id.
Time
Lemma ff_ff {k} {i} {i1} {i2} {j} :
  \226\136\128 (H1 : i + k = j) (H2 : i1 + (i2 + k) = j) (x : A k),
    coerce H1 (ff i x) = coerce H2 (ff i1 (ff i2 x)).
Time Proof.
Time (intros ? <- x).
Time (assert (i = i1 + i2) as -> by lia).
Time Qed.
Time Next Obligation.
Time (intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [? ?]; simpl).
Time
(induction i1 as [| i1 IH]; simplify_eq /=;
  [ by rewrite coerce_id | by rewrite coerce_f IH ]).
Time by rewrite !urFunctor_compose.
Time Qed.
Time
Definition embed_coerce {k} (i : nat) : A k -n> A i :=
  match le_lt_dec i k with
  | left H => gg (k - i) \226\151\142 coerce (eq_sym (Nat.sub_add _ _ H))
  | right H => coerce (Nat.sub_add k i (Nat.lt_le_incl _ _ H)) \226\151\142 ff (i - k)
  end.
Time
Lemma g_embed_coerce {k} {i} (x : A k) :
  g i (embed_coerce (S i) x) \226\137\161 embed_coerce i x.
Time Proof  using (Fcontr).
Time
(unfold embed_coerce; destruct (le_lt_dec (S i) k), (le_lt_dec i k); simpl).
Time Qed.
Time -
Time (symmetry; by erewrite (@gg_gg _ _ 1 (k - S i)); simpl).
Time -
Time (exfalso; lia).
Time Notation "F1 * F2" := (prodURF F1%URF F2%URF) : urFunctor_scope.
Time
Instance prodURF_contractive  F1 F2:
 (urFunctorContractive F1
  \226\134\146 urFunctorContractive F2 \226\134\146 urFunctorContractive (prodURF F1 F2)).
Time Proof.
Time
(intros ? ? A1 ? A2 ? B1 ? B2 ? n ? ? ?; by
  apply prodC_map_ne; apply urFunctor_contractive).
Time -
Time (assert (i = k) by lia; subst).
Time Qed.
Time rewrite (ff_ff _ (eq_refl (1 + (0 + k)))) /= gf.
Time Section option.
Time Context {A : cmraT}.
Time Implicit Types a b : A.
Time Implicit Types ma mb : option A.
Time #[local]Arguments core _ _ !_ /.
Time #[local]Arguments pcore _ _ !_ /.
Time
Instance option_valid : (Valid (option A)) :=
 (\206\187 ma, match ma with
        | Some a => \226\156\147 a
        | None => True
        end).
Time
Instance option_validN : (ValidN (option A)) :=
 (\206\187 n ma, match ma with
          | Some a => \226\156\147{n} a
          | None => True
          end).
Time
Instance option_pcore : (PCore (option A)) := (\206\187 ma, Some (ma \226\137\171= pcore)).
Time Arguments option_pcore !_ /.
Time
Instance option_op : (Op (option A)) := (union_with (\206\187 a b, Some (a \226\139\133 b))).
Time Definition Some_valid a : \226\156\147 Some a \226\134\148 \226\156\147 a := reflexivity _.
Time Definition Some_validN a n : \226\156\147{n} Some a \226\134\148 \226\156\147{n} a := reflexivity _.
Time by rewrite (gg_gg _ (eq_refl (0 + (0 + k)))).
Time Definition Some_op a b : Some (a \226\139\133 b) = Some a \226\139\133 Some b := eq_refl.
Time Lemma Some_core `{CmraTotal A} a : Some (core a) = core (Some a).
Time Proof.
Time rewrite /core /=.
Time by destruct (cmra_total a) as [? ->].
Time -
Time (assert (H : 1 + (i - k + k) = S i) by lia).
Time Qed.
Time Lemma Some_op_opM a ma : Some a \226\139\133 ma = Some (a \226\139\133? ma).
Time Proof.
Time by destruct ma.
Time Qed.
Time
Lemma option_included ma mb :
  ma \226\137\188 mb \226\134\148 ma = None \226\136\168 (\226\136\131 a b, ma = Some a \226\136\167 mb = Some b \226\136\167 (a \226\137\161 b \226\136\168 a \226\137\188 b)).
Time Proof.
Time split.
Time -
Time (intros [mc Hmc]).
Time (destruct ma as [a| ]; [ right | by left ]).
Time
(destruct mb as [b| ]; [ exists a,b | destruct mc; inversion_clear Hmc ]).
Time rewrite (ff_ff _ H) /= -{+2}(gf (ff (i - k) x)) g_coerce.
Time
(destruct mc as [c| ]; inversion_clear Hmc; split_and ?; auto; setoid_subst;
  eauto using cmra_included_l).
Time by erewrite coerce_proper by done.
Time Qed.
Time #[program]
Definition embed (k : nat) (x : A k) : T :=
  {| tower_car := fun n => embed_coerce n x |}.
Time Next Obligation.
Time (intros k x i).
Time (apply g_embed_coerce).
Time Qed.
Time Instance: (Params (@embed) 1) := { }.
Time Instance embed_ne  k: (NonExpansive (embed k)).
Time Proof.
Time by intros n x y Hxy i; rewrite /= Hxy.
Time -
Time (intros [->| (a, (b, (->, (->, [Hc| [c Hc]]))))]).
Time +
Time exists mb.
Time by destruct mb.
Time Qed.
Time Definition embed' (k : nat) : A k -n> T := CofeMor (embed k).
Time Lemma embed_f k (x : A k) : embed (S k) (f k x) \226\137\161 embed k x.
Time +
Time (exists None; by constructor).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite equiv_dist =>n i; rewrite /embed
  /= /embed_coerce).
Time (destruct (le_lt_dec i (S k)), (le_lt_dec i k); simpl).
Time +
Time (exists (Some c); by constructor).
Time Qed.
Time -
Time
Lemma option_includedN n ma mb :
  ma \226\137\188{n} mb
  \226\134\148 ma = None \226\136\168 (\226\136\131 x y, ma = Some x \226\136\167 mb = Some y \226\136\167 (x \226\137\161{n}\226\137\161 y \226\136\168 x \226\137\188{n} y)).
Time Proof.
Time split.
Time (assert (H : S k = S (k - i) + (0 + i)) by lia; rewrite (gg_gg _ H) /=).
Time -
Time (intros [mc Hmc]).
Time (destruct ma as [a| ]; [ right | by left ]).
Time
(destruct mb as [b| ]; [ exists a,b | destruct mc; inversion_clear Hmc ]).
Time
(destruct mc as [c| ]; inversion_clear Hmc; split_and ?; auto; ofe_subst;
  eauto using cmra_includedN_l).
Time by erewrite g_coerce, gf, coerce_proper by done.
Time -
Time (assert (H : S k = 0 + (0 + i)) by lia).
Time (rewrite (gg_gg _ H); simplify_eq /=).
Time -
Time (intros [->| (a, (y, (->, (->, [Hc| [c Hc]]))))]).
Time +
Time exists mb.
Time by destruct mb.
Time +
Time (exists None; by constructor).
Time +
Time (exists (Some c); by constructor).
Time Qed.
Time Lemma option_cmra_mixin : CmraMixin (option A).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time by intros [a| ] n; destruct 1; constructor; ofe_subst.
Time by rewrite (ff_ff _ (eq_refl (1 + (0 + k)))).
Time -
Time (exfalso; lia).
Time -
Time (assert (H : i - S k + (1 + k) = i) by lia; rewrite (ff_ff _ H) /=).
Time -
Time (destruct 1; by ofe_subst).
Time by erewrite coerce_proper by done.
Time Qed.
Time -
Time by destruct 1; rewrite /validN /option_validN //=; ofe_subst.
Time -
Time (intros [a| ]; [ apply cmra_valid_validN | done ]).
Time -
Time
(intros n [a| ]; unfold validN, option_validN; eauto using cmra_validN_S).
Time -
Time (intros [a| ] [b| ] [c| ]; constructor; rewrite ?assoc; auto).
Time Lemma embed_tower k (X : T) : embed (S k) (X (S k)) \226\137\161{k}\226\137\161 X.
Time Proof.
Time (intros i; rewrite /= /embed_coerce).
Time (destruct (le_lt_dec i (S k)) as [H| H]; simpl).
Time -
Time rewrite -(gg_tower i (S k - i) X).
Time (apply (_ : Proper (_ ==> _) (gg _)); by destruct (eq_sym _)).
Time -
Time (intros [a| ] [b| ]; constructor; rewrite 1?comm; auto).
Time -
Time rewrite (ff_tower k (i - S k) X).
Time -
Time (intros [a| ]; simpl; auto).
Time by destruct (Nat.sub_add _ _ _).
Time Qed.
Time
(destruct (pcore a) as [ca| ] eqn:?; constructor; eauto using cmra_pcore_l).
Time #[program]
Definition unfold_chain (X : T) : chain (F T _) :=
  {| chain_car := fun n => map (project n, embed' n) (X (S n)) |}.
Time Next Obligation.
Time (intros X n i Hi).
Time
(assert (\226\136\131 k, i = k + n) as [k ?] by (exists (i - n); lia); subst; clear Hi).
Time -
Time (intros [a| ]; simpl; auto).
Time
(destruct (pcore a) as [ca| ] eqn:?; simpl; eauto using cmra_pcore_idemp).
Time
(<ssreflect_plugin::ssrtclseq@0> induction k as [| k IH]; simpl ; first 
 done).
Time -
Time (intros ma mb; setoid_rewrite option_included).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite -IH
 -(dist_le _ _ _ _ (f_tower (k + n) _)) ; last  lia).
Time (intros [->| (a, (b, (->, (->, [?| ?]))))]; simpl; eauto).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; eauto).
Time (destruct (cmra_pcore_proper a b ca) as (?, (?, ?)); eauto  10).
Time +
Time (destruct (pcore a) as [ca| ] eqn:?; eauto).
Time (destruct (cmra_pcore_mono a b ca) as (?, (?, ?)); eauto  10).
Time -
Time
(intros n [a| ] [b| ]; rewrite /validN /option_validN /=; eauto
  using cmra_validN_op_l).
Time -
Time (intros n ma mb1 mb2).
Time
(destruct ma as [a| ], mb1 as [b1| ], mb2 as [b2| ]; intros Hx Hx';
  try by exfalso; inversion Hx'; try apply (inj Some) in Hx').
Time +
Time (destruct (cmra_extend n a b1 b2) as (c1, (c2, (?, (?, ?)))); auto).
Time by exists (Some c1),(Some c2); repeat constructor.
Time +
Time by exists (Some a),None; repeat constructor.
Time +
Time by exists None,(Some a); repeat constructor.
Time +
Time (exists None,None; repeat constructor).
Time Qed.
Time rewrite f_S -cFunctor_compose.
Time Canonical Structure optionR := CmraT (option A) option_cmra_mixin.
Time #[global]
Instance option_cmra_discrete : (CmraDiscrete A \226\134\146 CmraDiscrete optionR).
Time Proof.
Time (split; [ apply _ |  ]).
Time by intros [a| ]; [ apply (cmra_discrete_valid a) |  ].
Time Qed.
Time Instance option_unit : (Unit (option A)) := None.
Time Lemma option_ucmra_mixin : UcmraMixin optionR.
Time Proof.
Time split.
Time done.
Time by intros [].
Time done.
Time Qed.
Time Canonical Structure optionUR := UcmraT (option A) option_ucmra_mixin.
Time Lemma op_None ma mb : ma \226\139\133 mb = None \226\134\148 ma = None \226\136\167 mb = None.
Time Proof.
Time (destruct ma, mb; naive_solver).
Time Qed.
Time Lemma op_is_Some ma mb : is_Some (ma \226\139\133 mb) \226\134\148 is_Some ma \226\136\168 is_Some mb.
Time Proof.
Time rewrite -!not_eq_None_Some op_None.
Time (destruct ma, mb; naive_solver).
Time
by
 apply (contractive_ne map); <ssreflect_plugin::ssrtclintros@0> split =>Y /=;
  rewrite ?g_tower ?embed_f.
Time Qed.
Time Lemma cmra_opM_opM_assoc a mb mc : a \226\139\133? mb \226\139\133? mc \226\137\161 a \226\139\133? (mb \226\139\133 mc).
Time Proof.
Time (destruct mb, mc; by rewrite /= -?assoc).
Time Qed.
Time
Lemma cmra_opM_opM_assoc_L `{!LeibnizEquiv A} a mb 
  mc : a \226\139\133? mb \226\139\133? mc = a \226\139\133? (mb \226\139\133 mc).
Time Proof.
Time unfold_leibniz.
Time (apply cmra_opM_opM_assoc).
Time Qed.
Time Lemma cmra_opM_opM_swap a mb mc : a \226\139\133? mb \226\139\133? mc \226\137\161 a \226\139\133? mc \226\139\133? mb.
Time Qed.
Time Proof.
Time by rewrite !cmra_opM_opM_assoc (comm _ mb).
Time Qed.
Time
Lemma cmra_opM_opM_swap_L `{!LeibnizEquiv A} a mb 
  mc : a \226\139\133? mb \226\139\133? mc = a \226\139\133? mc \226\139\133? mb.
Time Proof.
Time by rewrite !cmra_opM_opM_assoc_L (comm_L _ mb).
Time Qed.
Time #[global]Instance Some_core_id  a: (CoreId a \226\134\146 CoreId (Some a)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance option_core_id  ma: ((\226\136\128 x : A, CoreId x) \226\134\146 CoreId ma).
Time Proof.
Time (intros).
Time (destruct ma; apply _).
Time Qed.
Time
Lemma exclusiveN_Some_l n a `{!Exclusive a} mb :
  \226\156\147{n} (Some a \226\139\133 mb) \226\134\146 mb = None.
Time Proof.
Time (destruct mb).
Time move  {}=>/(exclusiveN_l _ a) [].
Time done.
Time Qed.
Time
Lemma exclusiveN_Some_r n a `{!Exclusive a} mb :
  \226\156\147{n} (mb \226\139\133 Some a) \226\134\146 mb = None.
Time Proof.
Time rewrite comm.
Time by apply exclusiveN_Some_l.
Time Qed.
Time
Lemma exclusive_Some_l a `{!Exclusive a} mb : \226\156\147 (Some a \226\139\133 mb) \226\134\146 mb = None.
Time Proof.
Time (destruct mb).
Time move  {}=>/(exclusive_l a) [].
Time done.
Time Qed.
Time
Lemma exclusive_Some_r a `{!Exclusive a} mb : \226\156\147 (mb \226\139\133 Some a) \226\134\146 mb = None.
Time Proof.
Time rewrite comm.
Time by apply exclusive_Some_l.
Time Qed.
Time Lemma Some_includedN n a b : Some a \226\137\188{n} Some b \226\134\148 a \226\137\161{n}\226\137\161 b \226\136\168 a \226\137\188{n} b.
Time Proof.
Time (rewrite option_includedN; naive_solver).
Time Definition unfold (X : T) : F T _ := compl (unfold_chain X).
Time Instance unfold_ne : (NonExpansive unfold).
Time Proof.
Time (intros n X Y HXY).
Time
by rewrite /unfold (conv_compl n (unfold_chain X))
 (conv_compl n (unfold_chain Y)) /= (HXY (S n)).
Time Qed.
Time #[program]
Definition fold (X : F T _) : T :=
  {| tower_car := fun n => g n (map (embed' n, project n) X) |}.
Time Qed.
Time Next Obligation.
Time (intros X k).
Time (apply (_ : Proper ((\226\137\161) ==> (\226\137\161)) (g k))).
Time Lemma Some_included a b : Some a \226\137\188 Some b \226\134\148 a \226\137\161 b \226\136\168 a \226\137\188 b.
Time Proof.
Time (rewrite option_included; naive_solver).
Time rewrite g_S -cFunctor_compose.
Time Qed.
Time Lemma Some_included_2 a b : a \226\137\188 b \226\134\146 Some a \226\137\188 Some b.
Time Proof.
Time (rewrite Some_included; eauto).
Time Qed.
Time
Lemma Some_includedN_total `{CmraTotal A} n a b :
  Some a \226\137\188{n} Some b \226\134\148 a \226\137\188{n} b.
Time Proof.
Time rewrite Some_includedN.
Time split.
Time by intros [->| ?].
Time
(apply (contractive_proper map); <ssreflect_plugin::ssrtclintros@0> split =>Y;
  [ apply embed_f | apply g_tower ]).
Time eauto.
Time Qed.
Time Lemma Some_included_total `{CmraTotal A} a b : Some a \226\137\188 Some b \226\134\148 a \226\137\188 b.
Time Proof.
Time rewrite Some_included.
Time split.
Time by intros [->| ?].
Time Qed.
Time eauto.
Time Instance fold_ne : (NonExpansive fold).
Time Proof.
Time by intros n X Y HXY k; rewrite /fold /= HXY.
Time Qed.
Time Theorem result : solution F.
Time Proof  using ((Type))*.
Time (apply (Solution F T _ (CofeMor unfold) (CofeMor fold))).
Time -
Time move  {}=>X /=.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite equiv_dist =>n k; rewrite /unfold
  /fold /=).
Time (rewrite -g_tower -(gg_tower _ n); apply (_ : Proper (_ ==> _) (g _))).
Time Qed.
Time
Lemma Some_includedN_exclusive n a `{!Exclusive a} 
  b : Some a \226\137\188{n} Some b \226\134\146 \226\156\147{n} b \226\134\146 a \226\137\161{n}\226\137\161 b.
Time Proof.
Time (move  {}=>/Some_includedN [//|/exclusive_includedN]; tauto).
Time Qed.
Time
Lemma Some_included_exclusive a `{!Exclusive a} b :
  Some a \226\137\188 Some b \226\134\146 \226\156\147 b \226\134\146 a \226\137\161 b.
Time Proof.
Time (move  {}=>/Some_included [//|/exclusive_included]; tauto).
Time Qed.
Time Lemma is_Some_includedN n ma mb : ma \226\137\188{n} mb \226\134\146 is_Some ma \226\134\146 is_Some mb.
Time Proof.
Time rewrite -!not_eq_None_Some option_includedN.
Time naive_solver.
Time trans map (ff n, gg n) (X (S (n + k))).
Time Qed.
Time {
Time rewrite /unfold (conv_compl n (unfold_chain X)).
Time Lemma is_Some_included ma mb : ma \226\137\188 mb \226\134\146 is_Some ma \226\134\146 is_Some mb.
Time Proof.
Time rewrite -!not_eq_None_Some option_included.
Time naive_solver.
Time Qed.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 -(chain_cauchy (unfold_chain X) n (S (n + k))) /= ; last  lia).
Time #[global]
Instance cancelable_Some  a: (IdFree a \226\134\146 Cancelable a \226\134\146 Cancelable (Some a)).
Time Proof.
Time (intros Hirr ? ? [b| ] [c| ] ? EQ; inversion_clear EQ).
Time -
Time constructor.
Time by apply (cancelableN a).
Time -
Time (destruct (Hirr b); [  | eauto using dist_le with lia ]).
Time
by <ssreflect_plugin::ssrtclseq@0>
 eapply (cmra_validN_op_l 0 a b), (cmra_validN_le n) ; last  lia.
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 -(dist_le _ _ _ _ (f_tower (n + k) _)) ; last  lia).
Time -
Time (destruct (Hirr c); [  | symmetry; eauto using dist_le with lia ]).
Time
by <ssreflect_plugin::ssrtclseq@0> eapply (cmra_validN_le n) ; last  lia.
Time -
Time done.
Time Qed.
Time #[global]
Instance option_cancelable  (ma : option A):
 ((\226\136\128 a : A, IdFree a) \226\134\146 (\226\136\128 a : A, Cancelable a) \226\134\146 Cancelable ma).
Time Proof.
Time (destruct ma; apply _).
Time Qed.
Time End option.
Time
(rewrite f_S -!cFunctor_compose; apply (contractive_ne map);
  <ssreflect_plugin::ssrtclintros@0> split =>Y).
Time Arguments optionR : clear implicits.
Time Arguments optionUR : clear implicits.
Time Section option_prod.
Time Context {A B : cmraT}.
Time Implicit Type a : A.
Time Implicit Type b : B.
Time
Lemma Some_pair_includedN n a1 a2 b1 b2 :
  Some (a1, b1) \226\137\188{n} Some (a2, b2)
  \226\134\146 Some a1 \226\137\188{n} Some a2 \226\136\167 Some b1 \226\137\188{n} Some b2.
Time Proof.
Time rewrite !Some_includedN.
Time (intros [[? ?]| [? ?]%prod_includedN]; eauto).
Time Qed.
Time
Lemma Some_pair_includedN_total_1 `{CmraTotal A} n 
  a1 a2 b1 b2 :
  Some (a1, b1) \226\137\188{n} Some (a2, b2) \226\134\146 a1 \226\137\188{n} a2 \226\136\167 Some b1 \226\137\188{n} Some b2.
Time Proof.
Time (intros ?%Some_pair_includedN).
Time by rewrite -(Some_includedN_total _ a1).
Time Qed.
Time
Lemma Some_pair_includedN_total_2 `{CmraTotal B} n 
  a1 a2 b1 b2 :
  Some (a1, b1) \226\137\188{n} Some (a2, b2) \226\134\146 Some a1 \226\137\188{n} Some a2 \226\136\167 b1 \226\137\188{n} b2.
Time Proof.
Time (intros ?%Some_pair_includedN).
Time by rewrite -(Some_includedN_total _ b1).
Time Qed.
Time
Lemma Some_pair_included a1 a2 b1 b2 :
  Some (a1, b1) \226\137\188 Some (a2, b2) \226\134\146 Some a1 \226\137\188 Some a2 \226\136\167 Some b1 \226\137\188 Some b2.
Time Proof.
Time rewrite !Some_included.
Time (intros [[? ?]| [? ?]%prod_included]; eauto).
Time Qed.
Time
Lemma Some_pair_included_total_1 `{CmraTotal A} a1 
  a2 b1 b2 : Some (a1, b1) \226\137\188 Some (a2, b2) \226\134\146 a1 \226\137\188 a2 \226\136\167 Some b1 \226\137\188 Some b2.
Time Proof.
Time (intros ?%Some_pair_included).
Time by rewrite -(Some_included_total a1).
Time Qed.
Time
Lemma Some_pair_included_total_2 `{CmraTotal B} a1 
  a2 b1 b2 : Some (a1, b1) \226\137\188 Some (a2, b2) \226\134\146 Some a1 \226\137\188 Some a2 \226\136\167 b1 \226\137\188 b2.
Time Proof.
Time (intros ?%Some_pair_included).
Time by rewrite -(Some_included_total b1).
Time Qed.
Time End option_prod.
Time
Lemma option_fmap_mono {A B : cmraT} (f : A \226\134\146 B) ma 
  mb :
  Proper ((\226\137\161) ==> (\226\137\161)) f
  \226\134\146 (\226\136\128 a b, a \226\137\188 b \226\134\146 f a \226\137\188 f b) \226\134\146 ma \226\137\188 mb \226\134\146 f <$> ma \226\137\188 f <$> mb.
Time Proof.
Time (intros ? ?).
Time
(rewrite !option_included; intros [->| (a, (b, (->, (->, ?))))]; naive_solver).
Time +
Time rewrite /embed' /= /embed_coerce.
Time (destruct (le_lt_dec _ _); simpl; [ exfalso; lia |  ]).
Time by rewrite (ff_ff _ (eq_refl (S n + (0 + k)))) /= gf.
Time +
Time rewrite /embed' /= /embed_coerce.
Time (destruct (le_lt_dec _ _); simpl; [  | exfalso; lia ]).
Time by rewrite (gg_gg _ (eq_refl (0 + (S n + k)))) /= gf.
Time }
Time
(assert
  (map_ff_gg :
   \226\136\128 i k (x : A (S i + k)) (H : S i + k = i + S k),
     map (ff i, gg i) x \226\137\161 gg i (coerce H x))).
Time {
Time (intros i; induction i as [| i IH]; intros k' x H; simpl).
Time {
Time by rewrite coerce_id cFunctor_id.
Time }
Time (rewrite cFunctor_compose g_coerce; apply IH).
Time Qed.
Time
Instance option_fmap_cmra_morphism  {A B : cmraT} 
 (f : A \226\134\146 B) `{!CmraMorphism f}:
 (CmraMorphism (fmap f : option A \226\134\146 option B)).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time }
Time (assert (H : S n + k = n + S k) by lia).
Time -
Time (intros n [a| ] ?; rewrite /cmra_validN //=).
Time by apply (cmra_morphism_validN f).
Time -
Time move  {}=>[a|] //.
Time by apply Some_proper, cmra_morphism_pcore.
Time -
Time move  {}=>[a|] [b|] //=.
Time rewrite (map_ff_gg _ _ _ H).
Time by rewrite -(cmra_morphism_op f).
Time Qed.
Time #[program]
Definition optionRF (F : rFunctor) : rFunctor :=
  {|
  rFunctor_car := fun A _ B _ => optionR (rFunctor_car F A B);
  rFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  optionC_map (rFunctor_map F fg) |}.
Time (apply (_ : Proper (_ ==> _) (gg _)); by destruct H).
Time -
Time
(intros X; <ssreflect_plugin::ssrtclintros@0> rewrite equiv_dist =>n /=).
Time rewrite /unfold /= (conv_compl' n (unfold_chain (fold X))) /=.
Time rewrite g_S -!cFunctor_compose -{+2}[X]cFunctor_id.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply optionC_map_ne, rFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(option_fmap_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_equiv_ext =>y;
  apply rFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -option_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_equiv_ext =>y;
  apply rFunctor_compose).
Time Qed.
Time
Instance optionRF_contractive  F:
 (rFunctorContractive F \226\134\146 rFunctorContractive (optionRF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply optionC_map_ne, rFunctor_contractive.
Time Qed.
Time #[program]
Definition optionURF (F : rFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => optionUR (rFunctor_car F A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   optionC_map (rFunctor_map F fg) |}.
Time
(apply (contractive_ne map); <ssreflect_plugin::ssrtclintros@0> split =>Y /=).
Time +
Time rewrite f_tower.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply optionC_map_ne, rFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(option_fmap_id x).
Time (apply dist_S).
Time by rewrite embed_tower.
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_equiv_ext =>y;
  apply rFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -option_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_equiv_ext =>y;
  apply rFunctor_compose).
Time Qed.
Time +
Time (etrans; [ apply embed_ne, equiv_dist, g_tower | apply embed_tower ]).
Time
Instance optionURF_contractive  F:
 (rFunctorContractive F \226\134\146 urFunctorContractive (optionURF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply optionC_map_ne, rFunctor_contractive.
Time Qed.
Time Qed.
Time Section ofe_fun_cmra.
Time Context `{B : A \226\134\146 ucmraT}.
Time Implicit Types f g : ofe_fun B.
Time Instance ofe_fun_op : (Op (ofe_fun B)) := (\206\187 f g x, f x \226\139\133 g x).
Time
Instance ofe_fun_pcore : (PCore (ofe_fun B)) := (\206\187 f, Some (\206\187 x, core (f x))).
Time Instance ofe_fun_valid : (Valid (ofe_fun B)) := (\206\187 f, \226\136\128 x, \226\156\147 f x).
Time
Instance ofe_fun_validN : (ValidN (ofe_fun B)) := (\206\187 n f, \226\136\128 x, \226\156\147{n} f x).
Time Definition ofe_fun_lookup_op f g x : (f \226\139\133 g) x = f x \226\139\133 g x := eq_refl.
Time Definition ofe_fun_lookup_core f x : (core f) x = core (f x) := eq_refl.
Time Lemma ofe_fun_included_spec_1 (f g : ofe_fun B) x : f \226\137\188 g \226\134\146 f x \226\137\188 g x.
Time Proof.
Time by intros [h Hh]; exists (h x); rewrite /op /ofe_fun_op (Hh x).
Time Qed.
Time
Lemma ofe_fun_included_spec `{Hfin : Finite A} (f g : ofe_fun B) :
  f \226\137\188 g \226\134\148 (\226\136\128 x, f x \226\137\188 g x).
Time Proof.
Time (split; [ by intros; apply ofe_fun_included_spec_1 |  ]).
Time (intros [h ?]%finite_choice; by exists h).
Time Qed.
Time Lemma ofe_fun_cmra_mixin : CmraMixin (ofe_fun B).
Time Proof.
Time (apply cmra_total_mixin).
Time -
Time eauto.
Time -
Time by intros n f1 f2 f3 Hf x; rewrite ofe_fun_lookup_op (Hf x).
Time -
Time by intros n f1 f2 Hf x; rewrite ofe_fun_lookup_core (Hf x).
Time -
Time by intros n f1 f2 Hf ? x; rewrite -(Hf x).
Time -
Time (intros g; split).
Time +
Time (intros Hg n i; apply cmra_valid_validN, Hg).
Time +
Time
(intros Hg i; <ssreflect_plugin::ssrtclintros@0> apply cmra_valid_validN =>n;
  apply Hg).
Time -
Time (intros n f Hf x; apply cmra_validN_S, Hf).
Time -
Time by intros f1 f2 f3 x; rewrite ofe_fun_lookup_op assoc.
Time -
Time by intros f1 f2 x; rewrite ofe_fun_lookup_op comm.
Time -
Time
by intros f x; rewrite ofe_fun_lookup_op ofe_fun_lookup_core cmra_core_l.
Time -
Time by intros f x; rewrite ofe_fun_lookup_core cmra_core_idemp.
Time -
Time (intros f1 f2 Hf12).
Time (<ssreflect_plugin::ssrtclintros@0> exists (core f2) =>x).
Time rewrite ofe_fun_lookup_op.
Time
(apply (ofe_fun_included_spec_1 _ _ x), (cmra_core_mono (f1 x)) in Hf12).
Time rewrite !ofe_fun_lookup_core.
Time (destruct Hf12 as [? ->]).
Time rewrite assoc -cmra_core_dup //.
Time -
Time (intros n f1 f2 Hf x; apply cmra_validN_op_l with (f2 x), Hf).
Time -
Time (intros n f f1 f2 Hf Hf12).
Time
(pose proof (\206\187 x, cmra_extend n (f x) (f1 x) (f2 x) (Hf x) (Hf12 x)) as FUN).
Time exists (\206\187 x, projT1 (FUN x)),(\206\187 x, proj1_sig (projT2 (FUN x))).
Time
(<ssreflect_plugin::ssrtclintros@0> split; [  | split ] =>x;
  [ rewrite ofe_fun_lookup_op |  |  ]; by
  destruct (FUN x) as (?, (?, (?, (?, ?))))).
Time Qed.
Time End solver.
Time Canonical Structure ofe_funR := CmraT (ofe_fun B) ofe_fun_cmra_mixin.
Time Instance ofe_fun_unit : (Unit (ofe_fun B)) := (\206\187 x, \206\181).
Time Definition ofe_fun_lookup_empty x : \206\181 x = \206\181 := eq_refl.
Time Lemma ofe_fun_ucmra_mixin : UcmraMixin (ofe_fun B).
Time Proof.
Time split.
Time -
Time (intros x; apply ucmra_unit_valid).
Time -
Time by intros f x; rewrite ofe_fun_lookup_op left_id.
Time -
Time (<ssreflect_plugin::ssrtclintros@0> constructor =>x).
Time (apply core_id_core, _).
Time Qed.
Time Canonical Structure ofe_funUR := UcmraT (ofe_fun B) ofe_fun_ucmra_mixin.
Time #[global]
Instance ofe_fun_unit_discrete :
 ((\226\136\128 i, Discrete (\206\181 : B i)) \226\134\146 Discrete (\206\181 : ofe_fun B)).
Time Proof.
Time (intros ? f Hf x).
Time by apply : {}discrete {}.
Time Qed.
Time End ofe_fun_cmra.
Time Arguments ofe_funR {_} _.
Time Arguments ofe_funUR {_} _.
Time
Instance ofe_fun_map_cmra_morphism  {A} {B1 B2 : A \226\134\146 ucmraT}
 (f : \226\136\128 x, B1 x \226\134\146 B2 x):
 ((\226\136\128 x, CmraMorphism (f x)) \226\134\146 CmraMorphism (ofe_fun_map f)).
Time Proof.
Time (<ssreflect_plugin::ssrtclseq@0> split ; first  apply _).
Time -
Time
(intros n g Hg x; rewrite /ofe_fun_map;
  apply (cmra_morphism_validN (f _)), Hg).
Time -
Time (intros).
Time (<ssreflect_plugin::ssrtclintros@0> apply Some_proper =>i).
Time (apply (cmra_morphism_core (f i))).
Time -
Time (intros g1 g2 i).
Time by rewrite /ofe_fun_map ofe_fun_lookup_op cmra_morphism_op.
Time Qed.
Time #[program]
Definition ofe_funURF {C} (F : C \226\134\146 urFunctor) : urFunctor :=
  {|
  urFunctor_car := fun A _ B _ => ofe_funUR (\206\187 c, urFunctor_car (F c) A B);
  urFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                   ofe_funC_map (\206\187 c, urFunctor_map (F c) fg) |}.
Time End solver.
Time Next Obligation.
Time (intros C F A1 ? A2 ? B1 ? B2 ? n ? ? g).
Time
by
 <ssreflect_plugin::ssrtclintros@0> apply ofe_funC_map_ne =>?;
  apply urFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros C F A ? B ? g; simpl).
Time rewrite -{+2}(ofe_fun_map_id g).
Time
(<ssreflect_plugin::ssrtclintros@0> apply ofe_fun_map_ext =>y;
  apply urFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros C F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f1 f2 f1' f2' g).
Time rewrite /= -ofe_fun_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply ofe_fun_map_ext =>y;
  apply urFunctor_compose).
Time Qed.
Time
Instance ofe_funURF_contractive  {C} (F : C \226\134\146 urFunctor):
 ((\226\136\128 c, urFunctorContractive (F c)) \226\134\146 urFunctorContractive (ofe_funURF F)).
Time Proof.
Time (intros ? A1 ? A2 ? B1 ? B2 ? n ? ? g).
Time
by
 <ssreflect_plugin::ssrtclintros@0> apply ofe_funC_map_ne =>c;
  apply urFunctor_contractive.
Time Qed.
