Time From Classes Require Import EqualDec.
Time From Coq.QArith Require Import QArith_base Qcanon.
Time From stdpp Require Import base.
Time From stdpp Require Export list numbers.
Time From Transitions Require Import Relations.
Time From Armada Require Import Spec.Proc.
Time Set Implicit Arguments.
Time Arguments existT {A} {P} _ _.
Time Import EqNotations.
Time Import RelationNotations.
Time
Inductive NonAtomicArgs T :=
  | FinishArgs : forall args : T, _
  | Begin : _.
Time Arguments Begin {T}.
Time
Definition retT T (args : NonAtomicArgs T) T' : Type :=
  if args then T' else unit.
Time
Definition nonAtomicOp {Op} {ArgT} {T}
  (op : forall args : NonAtomicArgs ArgT, Op (retT args T)) :
  ArgT -> proc Op T :=
  fun args => Bind (Call (op Begin)) (fun _ => Call (op (FinishArgs args))).
Time
Inductive NonAtomicState Obj\206\163 : Type :=
  | Clean : forall s : Obj\206\163, _
  | Dirty : forall s : Obj\206\163, _.
Time
Definition readClean {State} Obj\206\163 (s : NonAtomicState Obj\206\163) :
  relation State State Obj\206\163 :=
  match s with
  | Clean s => pure s
  | Dirty _ => error
  end.
Time
Definition readDirty {State} Obj\206\163 (s : NonAtomicState Obj\206\163) :
  relation State State Obj\206\163 :=
  match s with
  | Clean _ => error
  | Dirty s => pure s
  end.
Time
Definition nonAtomicStep {ArgT} (args : NonAtomicArgs ArgT) 
  {T} {Obj\206\163} (obj_s : NonAtomicState Obj\206\163) {State}
  (mkDirty : Obj\206\163 -> relation State State unit)
  (opStep : Obj\206\163 -> ArgT -> relation State State T) :
  relation State State (retT args T) :=
  match args with
  | Begin => s <- readClean obj_s; mkDirty s
  | FinishArgs x => s <- readDirty obj_s; opStep s x
  end.
Time
Record DynMap A (Ref : A -> Type) (Model : A -> Type) :={
 dynMap : sigT Ref -> option (sigT Model);
 dynMap_wf :
  forall T v,
  match dynMap (existT T v) with
  | Some (existT T' _) => T' = T
  | None => True
  end;
 dynMap_dom : list (sigT Ref);
 dynMap_dom_spec : forall x, dynMap x <> None <-> x \226\136\136 dynMap_dom;
 dynMap_dom_nodup : NoDup dynMap_dom}.
Time Module OptionNotations.
Time Delimit Scope option_monad with opt.
Time
Notation "'Some!' x <- a ; f" := match a with
                                 | Some x => f
                                 | _ => None
                                 end
  (right associativity, at level 70, x pattern) : option_monad.
Time
Notation "'left!' H <- a ; f" :=
  match a with
  | left H => f
  | right _ => None
  end (right associativity, at level 60, f  at level 200) : option_monad.
Time Notation "'ret!' a" := (Some a) (at level 60) : option_monad.
Time End OptionNotations.
Time Import EqualDecNotation.
Time Import OptionNotations.
Time #[local]Open Scope option_monad.
Time
Definition getDyn A (Ref Model : A -> Type) (m : DynMap Ref Model) 
  a (r : Ref a) : option (Model a).
Time Proof.
Time (pose proof (m.(dynMap_wf) _ r)).
Time (destruct (m.(dynMap) (existT a r)); [ apply Some | exact None ]).
Time (destruct s).
Time exact (rew H in m0).
Time Defined.
Time Require Import Program.
Time
Lemma getDyn_lookup1 A (Ref Model : A -> Type) (m : DynMap Ref Model) 
  a (r : Ref a) (v : Model a) :
  m.(dynMap) (existT _ r) = Some (existT _ v) \226\134\146 getDyn m a r = Some v.
Time Proof.
Time (unfold getDyn).
Time (destruct m as [map wf]).
Time (simpl).
Time (generalize (wf a r)).
Time (generalize (map (existT a r))).
Time (intros ret Heq).
Time clear.
Time (destruct ret as [(?, ?)| ]; inversion 1).
Time subst.
Time (apply Eqdep.EqdepTheory.inj_pair2 in H2; subst; auto).
Time Qed.
Time
Lemma getDyn_lookup2 A (Ref Model : A -> Type) (m : DynMap Ref Model) 
  a (r : Ref a) (v : Model a) :
  getDyn m a r = Some v \226\134\146 m.(dynMap) (existT _ r) = Some (existT _ v).
Time Proof.
Time (unfold getDyn).
Time (destruct m as [map wf]).
Time (simpl).
Time (generalize (wf a r)).
Time (generalize (map (existT a r))).
Time (intros ret Heq).
Time clear.
Time (destruct ret as [(?, ?)| ]; inversion 1).
Time subst.
Time (unfold eq_rect).
Time auto.
Time Qed.
Time
Lemma getDyn_lookup_none A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) a (r : Ref a) :
  getDyn m a r = None <-> m.(dynMap) (existT _ r) = None.
Time Proof.
Time (unfold getDyn).
Time (destruct m as [map wf]).
Time (simpl).
Time (generalize (wf a r)).
Time (generalize (map (existT a r))).
Time (intros ret Heq).
Time clear.
Time (destruct ret as [(?, ?)| ]; [  | intuition ]).
Time (split; inversion 1).
Time Qed.
Time
Lemma getDyn_lookup_none1 A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) a (r : Ref a) :
  m.(dynMap) (existT _ r) = None -> getDyn m a r = None.
Time Proof.
Time (edestruct getDyn_lookup_none; eauto).
Time Qed.
Time
Lemma getDyn_lookup_none2 A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) a (r : Ref a) :
  getDyn m a r = None -> m.(dynMap) (existT _ r) = None.
Time Proof.
Time (edestruct getDyn_lookup_none; eauto).
Time Qed.
Time Arguments getDyn {A} {Ref} {Model} m {a} r.
Time From stdpp Require Import list.
Time Set Default Proof Using "Type".
Time #[local]Open Scope positive.
Time
Class Countable A `{EqDecision A} :={encode : A \226\134\146 positive;
                                     decode : positive \226\134\146 option A;
                                     decode_encode :
                                      forall x, decode (encode x) = Some x}.
Time Hint Mode Countable ! -: typeclass_instances.
Time Arguments encode : simpl never.
Time Arguments decode : simpl never.
Time
Definition encode_nat `{Countable A} (x : A) : nat :=
  pred (Pos.to_nat (encode x)).
Time
Definition decode_nat `{Countable A} (i : nat) : option A :=
  decode (Pos.of_nat (S i)).
Time Instance encode_inj  `{Countable A}: (Inj (=) (=) (encode (A:=A))).
Time Proof.
Time (intros x y Hxy; apply (inj Some)).
Time by rewrite <- (decode_encode x), Hxy, decode_encode.
Time Qed.
Time
Instance encode_nat_inj  `{Countable A}: (Inj (=) (=) (encode_nat (A:=A))).
Time Proof.
Time (unfold encode_nat; intros x y Hxy; apply (inj encode); lia).
Time Qed.
Time
Lemma decode_encode_nat `{Countable A} (x : A) :
  decode_nat (encode_nat x) = Some x.
Time Proof.
Time (pose proof (Pos2Nat.is_pos (encode x))).
Time (unfold decode_nat, encode_nat).
Time (rewrite Nat.succ_pred by lia).
Time by rewrite Pos2Nat.id, decode_encode.
Time Qed.
Time Section choice.
Time Context `{Countable A} (P : A \226\134\146 Prop).
Time
Inductive choose_step : relation positive :=
  | choose_step_None :
      forall {p}, decode (A:=A) p = None \226\134\146 choose_step (Pos.succ p) p
  | choose_step_Some :
      forall {p} {x : A},
      decode p = Some x \226\134\146 \194\172 P x \226\134\146 choose_step (Pos.succ p) p.
Time Lemma choose_step_acc : (\226\136\131 x, P x) \226\134\146 Acc choose_step 1%positive.
Time Proof.
Time (intros [x Hx]).
Time (cut (\226\136\128 i p, i \226\137\164 encode x \226\134\146 1 + encode x = p + i \226\134\146 Acc choose_step p)).
Time {
Time (intros help).
Time by apply (help (encode x)).
Time }
Time (induction i as [| i IH] using Pos.peano_ind; intros p ? ?).
Time {
Time constructor.
Time (intros j).
Time (assert (p = encode x) by lia; subst).
Time
(inversion 1 as [? Hd| ? ? Hd]; subst; rewrite decode_encode in Hd;
  congruence).
Time }
Time constructor.
Time (intros j).
Time (inversion 1 as [? Hd| ? y Hd]; subst; auto with lia).
Time
Instance In_dec  {T} {dec : EqualDec T} (a : T) (l : list T):
 (Decision (a \226\136\136 l)).
Time Proof.
Time (assert (EqDecision T)).
Time {
Time (unfold EqDecision, EqualDec, Decision in *; eauto).
Time }
Time (apply _).
Time Qed.
Time
Definition updDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)} 
  a (v : Ref a) (x : Model a) (m : DynMap Ref Model) : 
  DynMap Ref Model.
Time Proof.
Time
refine
 {|
 dynMap := fun r => if r == existT a v then ret! existT a x else m.(dynMap) r;
 dynMap_dom := if decide (existT a v \226\136\136 m.(dynMap_dom))
               then m.(dynMap_dom)
               else existT a v :: m.(dynMap_dom) |}.
Time {
Time (intros).
Time (destruct (existT _ v0 == existT _ v)).
Time -
Time (inversion e; auto).
Time -
Time (apply (m.(dynMap_wf) _ v0)).
Time }
Time {
Time (intros (a', v')).
Time (destruct (existT _ _ == existT _ v)).
Time Qed.
Time Context `{\226\136\128 x, Decision (P x)}.
Time -
Time
(abstract (split; auto; intros _; inversion e; subst;
            apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto;
            case (decide); eauto; intros; by left)).
Time
Fixpoint choose_go {i} (acc : Acc choose_step i) : A :=
  match Some_dec (decode i) with
  | inleft (x \226\134\190 Hx) =>
      match decide (P x) with
      | left _ => x
      | right H => choose_go (Acc_inv acc (choose_step_Some Hx H))
      end
  | inright H => choose_go (Acc_inv acc (choose_step_None H))
  end.
Time
Fixpoint choose_go_correct {i} (acc : Acc choose_step i) : P (choose_go acc).
Time Proof.
Time (destruct acc; simpl).
Time (repeat case_match; auto).
Time Qed.
Time
Fixpoint choose_go_pi {i} (acc1 acc2 : Acc choose_step i) :
choose_go acc1 = choose_go acc2.
Time Proof.
Time (destruct acc1, acc2; simpl; repeat case_match; auto).
Time -
Time
(abstract (rewrite dynMap_dom_spec; split; case (decide); auto; intros ?;
            [ by
            right
            | rewrite elem_of_cons; intros [| ]; eauto; congruence ])).
Time Qed.
Time Definition choose (H : \226\136\131 x, P x) : A := choose_go (choose_step_acc H).
Time
Definition choose_correct (H : \226\136\131 x, P x) : P (choose H) :=
  choose_go_correct _.
Time
Definition choose_pi (H1 H2 : \226\136\131 x, P x) : choose H1 = choose H2 :=
  choose_go_pi _ _.
Time Definition choice (HA : \226\136\131 x, P x) : {x | P x} := _ \226\134\190 choose_correct HA.
Time End choice.
Time
Lemma surj_cancel `{Countable A} `{EqDecision B} (f : A \226\134\146 B) 
  `{!Surj (=) f} : {g : B \226\134\146 A & Cancel (=) f g}.
Time Proof.
Time exists (\206\187 y, choose (\206\187 x, f x = y) (surj f y)).
Time (intros y).
Time }
Time {
Time (case (decide)).
Time by rewrite (choose_correct (\206\187 x, f x = y) (surj f y)).
Time Qed.
Time Section inj_countable.
Time Context `{Countable A} `{EqDecision B}.
Time Context (f : B \226\134\146 A) (g : A \226\134\146 option B) (fg : \226\136\128 x, g (f x) = Some x).
Time #[program]
Instance inj_countable : (Countable B) :=
 {| encode := fun y => encode (f y); decode := fun p => x \226\134\144 decode p; g x |}.
Time Next Obligation.
Time (intros y; simpl; rewrite decode_encode; eauto).
Time -
Time (intros; apply dynMap_dom_nodup).
Time -
Time (intros Hnotin).
Time (econstructor; [  | apply dynMap_dom_nodup ]; auto).
Time }
Time Defined.
Time Qed.
Time End inj_countable.
Time Section inj_countable'.
Time Context `{Countable A} `{EqDecision B}.
Time Context (f : B \226\134\146 A) (g : A \226\134\146 B) (fg : \226\136\128 x, g (f x) = x).
Time #[program]
Instance inj_countable' : (Countable B) := (inj_countable f (Some \226\136\152 g) _).
Time Next Obligation.
Time (intros x).
Time by f_equal /=.
Time
Lemma remove_elem_of {A : Type} dec (l : list A) (x : A) :
  ~ x \226\136\136 remove dec x l.
Time Qed.
Time End inj_countable'.
Time #[program]
Instance Empty_set_countable : (Countable Empty_set) :=
 {| encode := fun u => 1; decode := fun p => None |}.
Time Next Obligation.
Time by intros [].
Time Qed.
Time #[program]
Instance unit_countable : (Countable unit) :=
 {| encode := fun u => 1; decode := fun p => Some () |}.
Time Next Obligation.
Time by intros [].
Time Qed.
Time Proof.
Time (induction l; eauto; simpl; eauto).
Time *
Time (inversion 1).
Time *
Time (destruct dec; subst; eauto).
Time #[program]
Instance bool_countable : (Countable bool) :=
 {|
 encode := fun b => if b then 1 else 2;
 decode := fun p =>
           Some match p return bool with
                | 1 => true
                | _ => false
                end |}.
Time Next Obligation.
Time by intros [].
Time Qed.
Time #[program]
Instance option_countable  `{Countable A}: (Countable (option A)) :=
 {|
 encode := fun o =>
           match o with
           | None => 1
           | Some x => Pos.succ (encode x)
           end;
 decode := fun p =>
           if decide (p = 1) then Some None else Some <$> decode (Pos.pred p) |}.
Time Next Obligation.
Time (intros ? ? ? [x| ]; simpl; repeat case_decide; auto with lia).
Time (rewrite elem_of_cons; intuition).
Time Qed.
Time
Lemma remove_elem_of_ne {A : Type} dec (l : list A) 
  (x y : A) : ~ y = x -> y \226\136\136 remove dec x l <-> y \226\136\136 l.
Time Proof.
Time (induction l; eauto).
Time (intros Hneq).
Time (simpl).
Time (destruct dec; subst; rewrite ?elem_of_cons).
Time by rewrite Pos.pred_succ, decode_encode.
Time Qed.
Time #[program]
Instance sum_countable  `{Countable A} `{Countable B}:
 (Countable (A + B)%type) :=
 {|
 encode := fun xy =>
           match xy with
           | inl x => (encode x)~0
           | inr y => (encode y)~1
           end;
 decode := fun p =>
           match p with
           | 1 => None
           | p~0 => inl <$> decode p
           | p~1 => inr <$> decode p
           end |}.
Time *
Time (rewrite IHl; intuition).
Time Next Obligation.
Time by intros ? ? ? ? ? ? [x| y]; simpl; rewrite decode_encode.
Time Qed.
Time
Fixpoint prod_encode_fst (p : positive) : positive :=
  match p with
  | 1 => 1
  | p~0 => (prod_encode_fst p)~0~0
  | p~1 => (prod_encode_fst p)~0~1
  end.
Time *
Time (rewrite ?IHl; eauto).
Time
Fixpoint prod_encode_snd (p : positive) : positive :=
  match p with
  | 1 => 1~0
  | p~0 => (prod_encode_snd p)~0~0
  | p~1 => (prod_encode_snd p)~1~0
  end.
Time
Fixpoint prod_encode (p q : positive) : positive :=
  match p, q with
  | 1, 1 => 1~1
  | p~0, 1 => (prod_encode_fst p)~1~0
  | p~1, 1 => (prod_encode_fst p)~1~1
  | 1, q~0 => (prod_encode_snd q)~0~1
  | 1, q~1 => (prod_encode_snd q)~1~1
  | p~0, q~0 => (prod_encode p q)~0~0
  | p~0, q~1 => (prod_encode p q)~1~0
  | p~1, q~0 => (prod_encode p q)~0~1
  | p~1, q~1 => (prod_encode p q)~1~1
  end.
Time
Fixpoint prod_decode_fst (p : positive) : option positive :=
  match p with
  | p~0~0 => (~0) <$> prod_decode_fst p
  | p~0~1 => Some match prod_decode_fst p with
                  | Some q => q~1
                  | _ => 1
                  end
  | p~1~0 => (~0) <$> prod_decode_fst p
  | p~1~1 => Some match prod_decode_fst p with
                  | Some q => q~1
                  | _ => 1
                  end
  | 1~0 => None
  | 1~1 => Some 1
  | 1 => Some 1
  end.
Time Qed.
Time
Lemma remove_In_ne {A : Type} dec (l : list A) (x y : A) :
  ~ x = y -> In y (remove dec x l) <-> In y l.
Time
Fixpoint prod_decode_snd (p : positive) : option positive :=
  match p with
  | p~0~0 => (~0) <$> prod_decode_snd p
  | p~0~1 => (~0) <$> prod_decode_snd p
  | p~1~0 => Some match prod_decode_snd p with
                  | Some q => q~1
                  | _ => 1
                  end
  | p~1~1 => Some match prod_decode_snd p with
                  | Some q => q~1
                  | _ => 1
                  end
  | 1~0 => Some 1
  | 1~1 => Some 1
  | 1 => None
  end.
Time
Lemma prod_decode_encode_fst p q : prod_decode_fst (prod_encode p q) = Some p.
Time Proof.
Time (assert (\226\136\128 p, prod_decode_fst (prod_encode_fst p) = Some p)).
Time {
Time (intros p').
Time by induction p'; simplify_option_eq.
Time Proof.
Time (induction l; eauto).
Time (intros Hneq).
Time (simpl).
Time (destruct dec; subst).
Time *
Time (rewrite IHl; intuition).
Time *
Time (simpl).
Time (rewrite IHl; eauto).
Time Qed.
Time
Lemma remove_NoDup {A : Type} dec (l : list A) (x : A) :
  NoDup l \226\134\146 NoDup (remove dec x l).
Time Proof.
Time (induction 1; simpl).
Time econstructor.
Time (destruct dec; subst; eauto).
Time }
Time (assert (\226\136\128 p, prod_decode_fst (prod_encode_snd p) = None)).
Time {
Time (intros p').
Time by induction p'; simplify_option_eq.
Time (econstructor; eauto).
Time (rewrite elem_of_list_In, remove_In_ne; eauto).
Time by rewrite <- elem_of_list_In.
Time Qed.
Time
Definition deleteDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)} 
  a (v : Ref a) (m : DynMap Ref Model) : DynMap Ref Model.
Time Proof.
Time
refine
 {|
 dynMap := fun r => if r == existT a v then None else m.(dynMap) r;
 dynMap_dom := remove dec (existT a v) m.(dynMap_dom) |}.
Time (intros).
Time (destruct (existT _ v0 == existT _ v)).
Time -
Time auto.
Time -
Time (apply (m.(dynMap_wf) _ v0)).
Time -
Time {
Time (intros (a', v')).
Time }
Time revert q.
Time by induction p; intros [?| ?| ]; simplify_option_eq.
Time (destruct (existT _ _ == existT _ v)).
Time -
Time (split; auto; intros Hin).
Time *
Time by eauto.
Time *
Time (inversion e).
Time subst.
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst; auto).
Time (exfalso; eapply remove_elem_of; eauto).
Time -
Time (rewrite dynMap_dom_spec).
Time (rewrite remove_elem_of_ne; auto).
Time }
Time -
Time (apply remove_NoDup, dynMap_dom_nodup).
Time Defined.
Time Arguments updDyn {A} {Ref} {Model} {dec} {a} v x m.
Time Arguments deleteDyn {A} {Ref} {Model} {dec} {a} v m.
Time Instance empty_dynmap  A Ref Model: (Empty (@DynMap A Ref Model)).
Time refine {| dynMap := fun _ => None; dynMap_dom := nil |}.
Time -
Time (intros; auto).
Time -
Time (abstract (intros; split; try inversion 1; congruence)).
Time -
Time econstructor.
Time Defined.
Time #[global]
Instance DynMap_equiv  A (Ref Model : A \226\134\146 Type): (Equiv (DynMap Ref Model))
 := (\206\187 m m', \226\136\128 a (r : Ref a), getDyn m r = getDyn m' r).
Time #[global]
Instance getDyn_Proper  A (Ref Model : A \226\134\146 Type):
 (Proper (equiv ==> forall_relation (\206\187 a : A, pointwise_relation (Ref a) eq))
    (@getDyn A Ref Model)).
Time Proof.
Time (intros m1 m2 Hequiv).
Time eauto.
Time Qed.
Time #[global]
Instance DynMap_equivalence  A (Ref Model : A \226\134\146 Type):
 (Equivalence (@equiv (DynMap Ref Model) (@DynMap_equiv _ Ref Model))).
Time Proof.
Time split.
Time -
Time (intros m a r; eauto).
Time -
Time (intros m1 m2 a r; eauto).
Time -
Time (intros m1 m2 m3 ? ? a r).
Time (etransitivity; eauto).
Time Qed.
Time
Lemma getDyn_deleteDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)}
  (m : DynMap Ref Model) a (r : Ref a) : getDyn (deleteDyn r m) r = None.
Time Proof.
Time (intros).
Time (unfold getDyn, deleteDyn).
Time (destruct m as [map wf]).
Time Qed.
Time
Lemma prod_decode_encode_snd p q : prod_decode_snd (prod_encode p q) = Some q.
Time Proof.
Time (assert (\226\136\128 p, prod_decode_snd (prod_encode_snd p) = Some p)).
Time {
Time (intros p').
Time by induction p'; simplify_option_eq.
Time (simpl).
Time (destruct (equal); [  | congruence ]; eauto).
Time Qed.
Time }
Time (assert (\226\136\128 p, prod_decode_snd (prod_encode_fst p) = None)).
Time {
Time (intros p').
Time by induction p'; simplify_option_eq.
Time
Lemma getDyn_deleteDyn_ne1 A (Ref Model : A -> Type)
  {dec : EqualDec (sigT Ref)} (m : DynMap Ref Model) 
  a (r1 : Ref a) (r2 : sigT Ref) :
  ~ existT _ r1 = r2 ->
  getDyn (deleteDyn r1 m) (projT2 r2) = getDyn m (projT2 r2).
Time Proof.
Time (unfold getDyn, deleteDyn; simpl).
Time (destruct equal; [  | by congruence ]).
Time (intros).
Time exfalso.
Time (destruct r2).
Time (simpl in *).
Time (inversion e; subst).
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time intuition.
Time }
Time revert q.
Time by induction p; intros [?| ?| ]; simplify_option_eq.
Time Qed.
Time
Lemma getDyn_deleteDyn_ne2 A (Ref Model : A -> Type)
  {dec : EqualDec (sigT Ref)} (m : DynMap Ref Model) 
  a (r1 r2 : Ref a) : ~ r1 = r2 -> getDyn (deleteDyn r1 m) r2 = getDyn m r2.
Time Proof.
Time replace r2 with projT2 (existT _ r2) by auto.
Time (intros).
Time (apply (getDyn_deleteDyn_ne1 _ (r2:=existT a r2))).
Time (intros Heq).
Time (apply Eqdep.EqdepTheory.inj_pair2 in Heq; subst).
Time intuition.
Time Qed.
Time
Lemma updDyn_deleteDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)}
  (m : DynMap Ref Model) a (r : Ref a) x :
  updDyn r x (deleteDyn r m) \226\137\161 updDyn r x m.
Time Proof.
Time (intros a' r').
Time (unfold getDyn, updDyn, deleteDyn; simpl).
Time (destruct (equal); eauto).
Time Qed.
Time #[program]
Instance prod_countable  `{Countable A} `{Countable B}:
 (Countable (A * B)%type) :=
 {|
 encode := fun xy => prod_encode (encode xy.1) (encode xy.2);
 decode := fun p =>
           x \226\134\144 prod_decode_fst p \226\137\171= decode;
           y \226\134\144 prod_decode_snd p \226\137\171= decode; Some (x, y) |}.
Time Next Obligation.
Time (intros ? ? ? ? ? ? [x y]; simpl).
Time (rewrite prod_decode_encode_fst, prod_decode_encode_snd; simpl).
Time by rewrite !decode_encode.
Time Qed.
Time Qed.
Time #[global, program]
Instance list_countable  `{Countable A}: (Countable (list A)) :=
 {|
 encode := fun xs => positives_flatten (encode <$> xs);
 decode := fun p => positives \226\134\144 positives_unflatten p; mapM decode positives |}.
Time Next Obligation.
Time (intros A EqA CA xs).
Time (simpl).
Time (rewrite positives_unflatten_flatten).
Time (simpl).
Time (apply (mapM_fmap_Some _ _ _ decode_encode)).
Time Qed.
Time
Instance pos_countable : (Countable positive) :=
 {| encode := id; decode := Some; decode_encode := fun x => eq_refl |}.
Time #[program]
Instance N_countable : (Countable N) :=
 {|
 encode := fun x => match x with
                    | N0 => 1
                    | Npos p => Pos.succ p
                    end;
 decode := fun p =>
           if decide (p = 1) then Some 0%N else Some (Npos (Pos.pred p)) |}.
Time Next Obligation.
Time (intros [| p]; simpl; [ done |  ]).
Time by rewrite decide_False, Pos.pred_succ by by destruct p.
Time Qed.
Time #[program]
Instance Z_countable : (Countable Z) :=
 {|
 encode := fun x =>
           match x with
           | Z0 => 1
           | Zpos p => p~0
           | Zneg p => p~1
           end;
 decode := fun p =>
           Some match p with
                | 1 => Z0
                | p~0 => Zpos p
                | p~1 => Zneg p
                end |}.
Time Next Obligation.
Time by intros [| p| p].
Time Qed.
Time #[program]
Instance nat_countable : (Countable nat) :=
 {|
 encode := fun x => encode (N.of_nat x);
 decode := fun p => N.to_nat <$> decode p |}.
Time Next Obligation.
Time by intros x; lazy beta; rewrite decode_encode; csimpl; rewrite Nat2N.id.
Time Qed.
Time #[global, program]
Instance Qc_countable : (Countable Qc) :=
 (inj_countable (\206\187 p : Qc, let 'Qcmake (x # y) _ := p in (x, y))
    (\206\187 q : Z * positive, let '(x, y) := q in Some (Q2Qc (x # y))) _).
Time Next Obligation.
Time (intros [[x y] Hcan]).
Time f_equal.
Time (apply Qc_is_canon).
Time (simpl).
Time by rewrite Hcan.
Time Qed.
Time #[global, program]
Instance Qp_countable : (Countable Qp) :=
 (inj_countable Qp_car (\206\187 p : Qc, guard (0 < p)%Qc as Hp; Some (mk_Qp p Hp))
    _).
Time Next Obligation.
Time (intros [p Hp]).
Time (unfold mguard, option_guard; simpl).
Time (case_match; [  | done ]).
Time f_equal.
Time by apply Qp_eq.
Time Qed.
Time Close Scope positive.
Time
Inductive gen_tree (T : Type) : Type :=
  | GenLeaf : T \226\134\146 gen_tree T
  | GenNode : nat \226\134\146 list (gen_tree T) \226\134\146 gen_tree T.
Time Arguments GenLeaf {_} _ : assert.
Time Arguments GenNode {_} _ _ : assert.
Time Instance gen_tree_dec  `{EqDecision T}: (EqDecision (gen_tree T)).
Time Proof.
Time
(refine
  (fix go t1 t2 :=
     let _ : EqDecision _ := @go in
     match t1, t2 with
     | GenLeaf x1, GenLeaf x2 => cast_if (decide (x1 = x2))
     | GenNode n1 ts1, GenNode n2 ts2 =>
         cast_if_and (decide (n1 = n2)) (decide (ts1 = ts2))
     | _, _ => right _
     end); abstract congruence).
Time Defined.
Time
Fixpoint gen_tree_to_list {T} (t : gen_tree T) : list (nat * nat + T) :=
  match t with
  | GenLeaf x => [inr x]
  | GenNode n ts => (ts \226\137\171= gen_tree_to_list) ++ [inl (length ts, n)]
  end.
Time
Fixpoint gen_tree_of_list {T} (k : list (gen_tree T))
(l : list (nat * nat + T)) : option (gen_tree T) :=
  match l with
  | [] => head k
  | inr x :: l => gen_tree_of_list (GenLeaf x :: k) l
  | inl (len, n) :: l =>
      gen_tree_of_list (GenNode n (reverse (take len k)) :: drop len k) l
  end.
Time
Lemma gen_tree_of_to_list {T} k l (t : gen_tree T) :
  gen_tree_of_list k (gen_tree_to_list t ++ l) = gen_tree_of_list (t :: k) l.
Time Proof.
Time (revert t k l; fix FIX 1; intros [| n ts] k l; simpl; auto).
Time trans gen_tree_of_list (reverse ts ++ k) ([inl (length ts, n)] ++ l).
Time -
Time (rewrite <- (assoc_L _)).
Time revert k.
Time (generalize ([inl (length ts, n)] ++ l)).
Time (induction ts as [| t ts'' IH]; intros k ts'''; csimpl; auto).
Time (rewrite reverse_cons, <- !(assoc_L _), FIX; simpl; auto).
Time -
Time (simpl).
Time
by
 rewrite take_app_alt, drop_app_alt, reverse_involutive by by
  rewrite reverse_length.
Time Qed.
Time #[program]
Instance gen_tree_countable  `{Countable T}: (Countable (gen_tree T)) :=
 (inj_countable gen_tree_to_list (gen_tree_of_list []) _).
Time Next Obligation.
Time (intros T ? ? t).
Time
by rewrite <- (right_id_L [] _ (gen_tree_to_list _)), gen_tree_of_to_list.
Time Qed.
Time
Lemma getDyn_updDyn A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)}
  (m : DynMap Ref Model) a x (r : Ref a) : getDyn (updDyn r x m) r = Some x.
Time Proof.
Time (unfold getDyn, updDyn; simpl).
Time (destruct equal; [  | by congruence ]).
Time f_equal.
Time (rewrite <- Eqdep.Eq_rect_eq.eq_rect_eq; auto).
Time Qed.
Time
Lemma getDyn_updDyn_ne1 A (Ref Model : A -> Type) 
  {dec : EqualDec (sigT Ref)} (m : DynMap Ref Model) 
  a x (r1 : Ref a) (r2 : sigT Ref) :
  ~ existT _ r1 = r2 ->
  getDyn (updDyn r1 x m) (projT2 r2) = getDyn m (projT2 r2).
Time Proof.
Time (unfold getDyn, updDyn; simpl).
Time (destruct equal; [  | by congruence ]).
Time (intros).
Time exfalso.
Time (destruct r2).
Time (simpl in *).
Time (inversion e; subst).
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time intuition.
Time Qed.
Time
Lemma getDyn_updDyn_ne2 A (Ref Model : A -> Type) 
  {dec : EqualDec (sigT Ref)} (m : DynMap Ref Model) 
  a x (r1 r2 : Ref a) : ~ r1 = r2 -> getDyn (updDyn r1 x m) r2 = getDyn m r2.
Time Proof.
Time replace r2 with projT2 (existT _ r2) by auto.
Time (intros).
Time (apply (getDyn_updDyn_ne1 _ _ (r2:=existT a r2))).
Time (intros Heq).
Time (apply Eqdep.EqdepTheory.inj_pair2 in Heq; subst).
Time intuition.
Time Qed.
Time #[global]
Instance updDyn_Proper  A (Ref Model : A \226\134\146 Type) {dec : EqualDec (sigT Ref)}
 a (r : Ref a) (x : Model a): (Proper (equiv ==> equiv) (updDyn r x)).
Time Proof.
Time (intros m1 m2 Hequiv a' r').
Time (destruct (dec (existT _ r) (existT _ r'))).
Time -
Time (inversion e).
Time subst.
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time by rewrite ?getDyn_updDyn.
Time -
Time (rewrite ?(getDyn_updDyn_ne1 _ _ (r2:=existT a' r')); eauto).
Time Qed.
Time #[global]
Instance deleteDyn_Proper  A (Ref Model : A \226\134\146 Type)
 {dec : EqualDec (sigT Ref)} a (r : Ref a):
 (Proper (equiv ==> equiv) (deleteDyn (Model:=Model) r)).
Time Proof.
Time (intros m1 m2 Hequiv a' r').
Time (destruct (dec (existT _ r) (existT _ r'))).
Time -
Time (inversion e).
Time subst.
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time by rewrite ?getDyn_deleteDyn.
Time -
Time (rewrite ?(getDyn_deleteDyn_ne1 _ (r2:=existT a' r')); eauto).
Time Qed.
Time
Lemma updDyn_identity A (Ref Model : A -> Type) {dec : EqualDec (sigT Ref)}
  (m : DynMap Ref Model) a (r : Ref a) x :
  getDyn m r = Some x \226\134\146 updDyn r x m \226\137\161 m.
Time Proof.
Time (intros Hlookup a' r').
Time (destruct (dec (existT _ r) (existT _ r'))).
Time *
Time (inversion e; subst).
Time (apply Eqdep.EqdepTheory.inj_pair2 in e; subst).
Time by rewrite getDyn_updDyn.
Time *
Time replace r' with projT2 (existT _ r') by auto.
Time (rewrite (getDyn_updDyn_ne1 _ _ (r2:=existT a' r')); eauto).
Time Qed.
Time
Lemma dynMap_dom_spec' A (Ref Model : A -> Type) (m : DynMap Ref Model) 
  a (x : Ref a) : getDyn m x <> None <-> existT _ x \226\136\136 dynMap_dom m.
Time Proof.
Time by rewrite <- dynMap_dom_spec, getDyn_lookup_none.
Time Qed.
Time
Lemma dynMap_dom_non_spec A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) a (x : Ref a) :
  getDyn m x = None <-> \194\172 existT _ x \226\136\136 dynMap_dom m.
Time Proof.
Time (rewrite <- dynMap_dom_spec').
Time (destruct getDyn; auto; split; firstorder).
Time Qed.
Time
Lemma dynMap_equiv_perm_dom A (Ref Model : A -> Type)
  (m1 m2 : DynMap Ref Model) : m1 \226\137\161 m2 \226\134\146 dynMap_dom m1 \226\137\161\226\130\154 dynMap_dom m2.
Time Proof.
Time (intros Hequiv).
Time (apply NoDup_Permutation; eauto using dynMap_dom_nodup).
Time (intros (a, x)).
Time by rewrite <- ?dynMap_dom_spec', Hequiv.
Time Qed.
Time #[global]
Instance dynMap_dom_Proper  A (Ref Model : A \226\134\146 Type):
 (Proper (equiv ==> (\226\137\161\226\130\154)) (@dynMap_dom A Ref Model)).
Time Proof.
Time (intros m1 m2 Hequiv).
Time (eapply dynMap_equiv_perm_dom; eauto).
Time Qed.
Time
Lemma dynMap_dom_empty_iff A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) : m \226\137\161 \226\136\133 <-> dynMap_dom m = [].
Time Proof.
Time split.
Time -
Time (intros Hequiv).
Time (apply Permutation_nil).
Time (rewrite Hequiv; eauto).
Time -
Time (intros Hdom a k).
Time (unfold getDyn at 2; simpl).
Time (rewrite dynMap_dom_non_spec, Hdom).
Time (inversion 1).
Time Qed.
Time
Lemma dynMap_dom_lookup A (Ref Model : A -> Type) 
  (m : DynMap Ref Model) (k : nat) (y : {a : A & Ref a}) :
  m.(dynMap_dom) !! k = Some y -> exists v, getDyn m (projT2 y) = Some v.
Time Proof.
Time (intros Hin%elem_of_list_lookup_2).
Time replace y with existT _ (projT2 y) in Hin by (destruct y; eauto).
Time (rewrite <- dynMap_dom_spec' in Hin).
Time (destruct getDyn as [?| ] eqn:Heq; eauto; congruence).
Time Qed.
