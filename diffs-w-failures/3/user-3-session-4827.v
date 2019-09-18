Time From stdpp Require Export strings.
Time From iris.algebra Require Export base.
Time From iris.algebra Require Export base.
Time Set Default Proof Using "Type".
Time Set Primitive Projections.
Time Class Dist A :=
         dist : nat \226\134\146 relation A.
Time Instance: (Params (@dist) 3) := { }.
Time
Notation "x \226\137\161{ n }\226\137\161 y" := (dist n x y)
  (at level 70, n  at next level, format "x  \226\137\161{ n }\226\137\161  y").
Time
Notation "x \226\137\161{ n }@{ A }\226\137\161 y" := (dist (A:=A) n x y)
  (at level 70, n  at next level, only parsing).
Time Hint Extern 0 (_ \226\137\161{_}\226\137\161 _) => reflexivity: core.
Time Hint Extern 0 (_ \226\137\161{_}\226\137\161 _) => (symmetry; assumption): core.
Time Notation NonExpansive f:= (\226\136\128 n, Proper (dist n ==> dist n) f).
Time
Notation NonExpansive2 f:= (\226\136\128 n, Proper (dist n ==> dist n ==> dist n) f).
Time
Tactic Notation "ofe_subst" ident(x) :=
 (repeat
   match goal with
   | _ =>
       progress simplify_eq /=
   | H:@dist ?A ?d ?n x _ |- _ => setoid_subst_aux (@dist A d n) x
   | H:@dist ?A ?d ?n _ x
     |- _ => symmetry in H; setoid_subst_aux (@dist A d n) x
   end).
Time
Tactic Notation "ofe_subst" :=
 (repeat
   match goal with
   | _ =>
       progress simplify_eq /=
   | H:@dist ?A ?d ?n ?x _ |- _ => setoid_subst_aux (@dist A d n) x
   | H:@dist ?A ?d ?n _ ?x
     |- _ => symmetry in H; setoid_subst_aux (@dist A d n) x
   end).
Time
Record OfeMixin A `{Equiv A} `{Dist A} :={mixin_equiv_dist :
                                           forall x y,
                                           x \226\137\161 y \226\134\148 (\226\136\128 n, x \226\137\161{n}\226\137\161 y);
                                          mixin_dist_equivalence :
                                           forall n, Equivalence (dist n);
                                          mixin_dist_S :
                                           forall n x y,
                                           x \226\137\161{S n}\226\137\161 y \226\134\146 x \226\137\161{n}\226\137\161 y}.
Time
Structure ofeT :=
 OfeT {ofe_car :> Type;
       ofe_equiv : Equiv ofe_car;
       ofe_dist : Dist ofe_car;
       ofe_mixin : OfeMixin ofe_car}.
Time Arguments OfeT _ {_} {_} _.
Time Add Printing Constructor ofeT.
Time Hint Extern 0 (Equiv _) => (eapply (@ofe_equiv _)): typeclass_instances.
Time Hint Extern 0 (Dist _) => (eapply (@ofe_dist _)): typeclass_instances.
Time Arguments ofe_car : simpl never.
Time Arguments ofe_equiv : simpl never.
Time Arguments ofe_dist : simpl never.
Time Arguments ofe_mixin : simpl never.
Time
Definition ofe_mixin_of' A {Ac : ofeT} (f : Ac \226\134\146 A) : 
  OfeMixin Ac := ofe_mixin Ac.
Time Notation ofe_mixin_of A:= _ (only parsing).
Time Section ofe_mixin.
Time Context {A : ofeT}.
Time Implicit Types x y : A.
Time Lemma equiv_dist x y : x \226\137\161 y \226\134\148 (\226\136\128 n, x \226\137\161{n}\226\137\161 y).
Time Proof.
Time (apply (mixin_equiv_dist _ (ofe_mixin A))).
Time Qed.
Time #[global]Instance dist_equivalence  n: (Equivalence (@dist A _ n)).
Time Proof.
Time (apply (mixin_dist_equivalence _ (ofe_mixin A))).
Time Qed.
Time Lemma dist_S n x y : x \226\137\161{S n}\226\137\161 y \226\134\146 x \226\137\161{n}\226\137\161 y.
Time Proof.
Time (apply (mixin_dist_S _ (ofe_mixin A))).
Time Qed.
Time End ofe_mixin.
Time Hint Extern 1 (_ \226\137\161{_}\226\137\161 _) => (apply equiv_dist; assumption): core.
Time
Class Discrete {A : ofeT} (x : A) :=
    discrete : forall y, x \226\137\161{0}\226\137\161 y \226\134\146 x \226\137\161 y.
Time Arguments discrete {_} _ {_} _ _.
Time Hint Mode Discrete + !: typeclass_instances.
Time Instance: (Params (@Discrete) 1) := { }.
Time
Class OfeDiscrete (A : ofeT) :=
    ofe_discrete_discrete :> forall x : A, Discrete x.
Time From Coq Require Export Ascii.
Time Set Default Proof Using "Type".
Time Inductive direction :=
       | Left : _
       | Right : _.
Time #[local]Notation "b1 && b2" := (if b1 then b2 else false) : bool_scope.
Time
Record chain (A : ofeT) :={chain_car :> nat \226\134\146 A;
                           chain_cauchy :
                            forall n i, n \226\137\164 i \226\134\146 chain_car i \226\137\161{n}\226\137\161 chain_car n}.
Time Arguments chain_car {_} _ _.
Time Arguments chain_cauchy {_} _ _ _ _.
Time #[program]
Definition chain_map {A B : ofeT} (f : A \226\134\146 B) `{!NonExpansive f}
  (c : chain A) : chain B := {| chain_car := fun n => f (c n) |}.
Time Next Obligation.
Time by intros A B f Hf c n i ?; apply Hf, chain_cauchy.
Time Qed.
Time Notation Compl A:= (chain A%type \226\134\146 A).
Time
Class Cofe (A : ofeT) :={compl : Compl A;
                         conv_compl : forall n c, compl c \226\137\161{n}\226\137\161 c n}.
Time Arguments compl : simpl never.
Time Hint Mode Cofe !: typeclass_instances.
Time
Lemma compl_chain_map `{Cofe A} `{Cofe B} (f : A \226\134\146 B) 
  c `(NonExpansive f) : compl (chain_map f c) \226\137\161 f (compl c).
Time
Lemma lazy_andb_true (b1 b2 : bool) : b1 && b2 = true \226\134\148 b1 = true \226\136\167 b2 = true.
Time Proof.
Time (destruct b1, b2; intuition congruence).
Time Qed.
Time
Fixpoint Pos_succ (x : positive) : positive :=
  match x with
  | (p~1)%positive => ((Pos_succ p)~0)%positive
  | (p~0)%positive => (p~1)%positive
  | 1%positive => 2%positive
  end.
Time
Definition beq (b1 b2 : bool) : bool :=
  match b1, b2 with
  | false, false | true, true => true
  | _, _ => false
  end.
Time
Definition ascii_beq (x y : ascii) : bool :=
  let
  'Ascii x1 x2 x3 x4 x5 x6 x7 x8 := x in
   let
   'Ascii y1 y2 y3 y4 y5 y6 y7 y8 := y in
    beq x1 y1 && beq x2 y2 && beq x3 y3 && beq x4 y4 && beq x5 y5 &&
    beq x6 y6 && beq x7 y7 && beq x8 y8.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time by rewrite !conv_compl.
Time
Fixpoint string_beq (s1 s2 : string) : bool :=
  match s1, s2 with
  | "", "" => true
  | String a1 s1, String a2 s2 => ascii_beq a1 a2 && string_beq s1 s2
  | _, _ => false
  end.
Time Lemma beq_true b1 b2 : beq b1 b2 = true \226\134\148 b1 = b2.
Time Proof.
Time (destruct b1, b2; simpl; intuition congruence).
Time Qed.
Time Lemma ascii_beq_true x y : ascii_beq x y = true \226\134\148 x = y.
Time Proof.
Time (destruct x, y; rewrite /= !lazy_andb_true !beq_true).
Time Qed.
Time #[program]
Definition chain_const {A : ofeT} (a : A) : chain A :=
  {| chain_car := fun n => a |}.
Time Next Obligation.
Time by intros A a n i _.
Time Qed.
Time
Lemma compl_chain_const {A : ofeT} `{!Cofe A} (a : A) :
  compl (chain_const a) \226\137\161 a.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time by rewrite conv_compl.
Time Qed.
Time Section ofe.
Time Context {A : ofeT}.
Time Implicit Types x y : A.
Time #[global]Instance ofe_equivalence : (Equivalence ((\226\137\161) : relation A)).
Time Proof.
Time split.
Time -
Time by intros x; rewrite equiv_dist.
Time -
Time by intros x y; rewrite !equiv_dist.
Time -
Time by intros x y z; rewrite !equiv_dist; intros; trans y.
Time Qed.
Time #[global]
Instance dist_ne  n: (Proper (dist n ==> dist n ==> iff) (@dist A _ n)).
Time Proof.
Time (intros x1 x2 ? y1 y2 ?; split; intros).
Time -
Time by trans x1; [  | trans y1 ].
Time -
Time by trans x2; [  | trans y2 ].
Time Qed.
Time #[global]
Instance dist_proper  n: (Proper ((\226\137\161) ==> (\226\137\161) ==> iff) (@dist A _ n)).
Time Proof.
Time
by move  {}=>x1 x2 /equiv_dist Hx y1 y2 /equiv_dist Hy; rewrite (Hx n) (Hy n).
Time Qed.
Time #[global]Instance dist_proper_2  n x: (Proper ((\226\137\161) ==> iff) (dist n x)).
Time Proof.
Time by apply dist_proper.
Time Qed.
Time #[global]
Instance Discrete_proper : (Proper ((\226\137\161) ==> iff) (@Discrete A)).
Time Proof.
Time (intros x y Hxy).
Time rewrite /Discrete.
Time by setoid_rewrite Hxy.
Time Qed.
Time Lemma dist_le n n' x y : x \226\137\161{n}\226\137\161 y \226\134\146 n' \226\137\164 n \226\134\146 x \226\137\161{n'}\226\137\161 y.
Time Proof.
Time (induction 2; eauto using dist_S).
Time Qed.
Time Lemma dist_le' n n' x y : n' \226\137\164 n \226\134\146 x \226\137\161{n}\226\137\161 y \226\134\146 x \226\137\161{n'}\226\137\161 y.
Time Proof.
Time (intros; eauto using dist_le).
Time intuition congruence.
Time Qed.
Time
Instance ne_proper  {B : ofeT} (f : A \226\134\146 B) `{!NonExpansive f}:
 (Proper ((\226\137\161) ==> (\226\137\161)) f) |100.
Time Proof.
Time by intros x1 x2; rewrite !equiv_dist; intros Hx n; rewrite (Hx n).
Time Qed.
Time
Instance ne_proper_2  {B C : ofeT} (f : A \226\134\146 B \226\134\146 C) 
 `{!NonExpansive2 f}: (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) f) |100.
Time Proof.
Time (unfold Proper, respectful; setoid_rewrite equiv_dist).
Time by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
Time Qed.
Time Lemma conv_compl' `{Cofe A} n (c : chain A) : compl c \226\137\161{n}\226\137\161 c (S n).
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> transitivity (c n) ; first  by
 apply conv_compl).
Time symmetry.
Time (apply chain_cauchy).
Time lia.
Time Qed.
Time Lemma discrete_iff n (x : A) `{!Discrete x} y : x \226\137\161 y \226\134\148 x \226\137\161{n}\226\137\161 y.
Time Proof.
Time (split; intros; auto).
Time Qed.
Time (apply (discrete _), dist_le with n; auto with lia).
Time Qed.
Time Lemma discrete_iff_0 n (x : A) `{!Discrete x} y : x \226\137\161{0}\226\137\161 y \226\134\148 x \226\137\161{n}\226\137\161 y.
Time Proof.
Time by rewrite -!discrete_iff.
Time Lemma string_beq_true s1 s2 : string_beq s1 s2 = true \226\134\148 s1 = s2.
Time Proof.
Time revert s2.
Time
(<ssreflect_plugin::ssrtclintros@0> induction s1 as [| x s1 IH] =>- 
 [|y s2] //=).
Time Qed.
Time End ofe.
Time
Definition dist_later `{Dist A} (n : nat) (x y : A) : Prop :=
  match n with
  | 0 => True
  | S n => x \226\137\161{n}\226\137\161 y
  end.
Time Arguments dist_later _ _ !_ _ _ /.
Time #[global]
Instance dist_later_equivalence  (A : ofeT) n:
 (Equivalence (@dist_later A _ n)).
Time Proof.
Time (destruct n as [| n]).
Time by split.
Time (apply dist_equivalence).
Time Qed.
Time rewrite lazy_andb_true ascii_beq_true IH.
Time
Lemma dist_dist_later {A : ofeT} n (x y : A) : dist n x y \226\134\146 dist_later n x y.
Time Proof.
Time (intros Heq).
Time (<ssreflect_plugin::ssrtclseq@0> destruct n ; first  done).
Time exact : {}dist_S {}.
Time Qed.
Time
Lemma dist_later_dist {A : ofeT} n (x y : A) :
  dist_later (S n) x y \226\134\146 dist n x y.
Time intuition congruence.
Time Qed.
Time Lemma string_beq_reflect s1 s2 : reflect (s1 = s2) (string_beq s1 s2).
Time Proof.
Time (apply iff_reflect).
Time by rewrite string_beq_true.
Time Proof.
Time done.
Time Qed.
Time
Lemma ne_dist_later {A B : ofeT} (f : A \226\134\146 B) :
  NonExpansive f \226\134\146 \226\136\128 n, Proper (dist_later n ==> dist_later n) f.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> intros Hf [| n] ; last  exact : {}Hf {}).
Time (hnf).
Time by intros.
Time Qed.
Time Notation Contractive f:= (\226\136\128 n, Proper (dist_later n ==> dist n) f).
Time
Instance const_contractive  {A B : ofeT} (x : A):
 (Contractive (@const A B x)).
Time Proof.
Time by intros n y1 y2.
Time Qed.
Time Module Export ident.
Time
Inductive ident :=
  | IAnon : positive \226\134\146 ident
  | INamed :> string \226\134\146 ident.
Time End ident.
Time
Instance maybe_IAnon : (Maybe IAnon) :=
 (\206\187 i, match i with
       | IAnon n => Some n
       | _ => None
       end).
Time
Instance maybe_INamed : (Maybe INamed) :=
 (\206\187 i, match i with
       | INamed s => Some s
       | _ => None
       end).
Time Instance beq_eq_dec : (EqDecision ident).
Time Proof.
Time solve_decision.
Time Qed.
Time Section contractive.
Time #[local]Set Default Proof Using "Type*".
Time Context {A B : ofeT} (f : A \226\134\146 B) `{!Contractive f}.
Time Implicit Types x y : A.
Time Lemma contractive_0 x y : f x \226\137\161{0}\226\137\161 f y.
Time Proof.
Time by apply (_ : Contractive f).
Time Qed.
Time Lemma contractive_S n x y : x \226\137\161{n}\226\137\161 y \226\134\146 f x \226\137\161{S n}\226\137\161 f y.
Time Proof.
Time (intros).
Time by apply (_ : Contractive f).
Time Qed.
Time Defined.
Time Definition positive_beq := Eval compute in Pos.eqb.
Time Lemma positive_beq_true x y : positive_beq x y = true \226\134\148 x = y.
Time Proof.
Time (apply Pos.eqb_eq).
Time Qed.
Time
Definition ident_beq (i1 i2 : ident) : bool :=
  match i1, i2 with
  | IAnon n1, IAnon n2 => positive_beq n1 n2
  | INamed s1, INamed s2 => string_beq s1 s2
  | _, _ => false
  end.
Time Lemma ident_beq_true i1 i2 : ident_beq i1 i2 = true \226\134\148 i1 = i2.
Time Proof.
Time
(destruct i1, i2; rewrite /= ?string_beq_true ?positive_beq_true;
  naive_solver).
Time #[global]Instance contractive_ne : (NonExpansive f) |100.
Time Proof.
Time by intros n x y ?; apply dist_S, contractive_S.
Time Qed.
Time #[global]Instance contractive_proper : (Proper ((\226\137\161) ==> (\226\137\161)) f) |100.
Time Proof.
Time (apply (ne_proper _)).
Time Qed.
Time End contractive.
Time
Ltac
 f_contractive :=
  match goal with
  | |- ?f _ \226\137\161{_}\226\137\161 ?f _ => simple apply (_ : Proper (dist_later _ ==> _) f)
  | |- ?f _ _ \226\137\161{_}\226\137\161 ?f _ _ =>
        simple apply (_ : Proper (dist_later _ ==> _ ==> _) f)
  | |- ?f _ _ \226\137\161{_}\226\137\161 ?f _ _ =>
        simple apply (_ : Proper (_ ==> dist_later _ ==> _) f)
  end;
   try
    match goal with
    | |- @dist_later ?A _ ?n ?x ?y =>
          destruct n as [| n];
           [ exact I | change_no_check (@dist A _ n x y) ]
    end; try simple apply reflexivity.
Time
Ltac
 solve_contractive :=
  solve_proper_core ltac:(fun _ => first [ f_contractive | f_equiv ]).
Time
Class LimitPreserving `{!Cofe A} (P : A \226\134\146 Prop) : Prop :=
    limit_preserving : forall c : chain A, (\226\136\128 n, P (c n)) \226\134\146 P (compl c).
Time Hint Mode LimitPreserving + + !: typeclass_instances.
Time Section limit_preserving.
Time Context `{Cofe A}.
Time
Lemma limit_preserving_ext (P Q : A \226\134\146 Prop) :
  (\226\136\128 x, P x \226\134\148 Q x) \226\134\146 LimitPreserving P \226\134\146 LimitPreserving Q.
Time Proof.
Time (intros HP Hlimit c ?).
Time (<ssreflect_plugin::ssrtclintros@0> apply HP, Hlimit =>n; by apply HP).
Time Qed.
Time #[global]
Instance limit_preserving_const  (P : Prop): (LimitPreserving (\206\187 _ : A, P)).
Time Proof.
Time (intros c HP).
Time (apply (HP 0)).
Time Qed.
Time
Lemma limit_preserving_discrete (P : A \226\134\146 Prop) :
  Proper (dist 0 ==> impl) P \226\134\146 LimitPreserving P.
Time Proof.
Time (intros PH c Hc).
Time by rewrite (conv_compl 0).
Time Qed.
Time Lemma ident_beq_reflect i1 i2 : reflect (i1 = i2) (ident_beq i1 i2).
Time Proof.
Time (apply iff_reflect).
Time by rewrite ident_beq_true.
Time Qed.
Time
Definition pm_option_bind {A} {B} (f : A \226\134\146 option B) 
  (mx : option A) : option B :=
  match mx with
  | Some x => f x
  | None => None
  end.
Time Arguments pm_option_bind {_} {_} _ !_ /.
Time
Definition pm_from_option {A} {B} (f : A \226\134\146 B) (y : B) 
  (mx : option A) : B := match mx with
                         | None => y
                         | Some x => f x
                         end.
Time Arguments pm_from_option {_} {_} _ _ !_ /.
Time
Definition pm_option_fun {A} {B} (f : option (A \226\134\146 B)) 
  (x : A) : option B :=
  match f with
  | None => None
  | Some f => Some (f x)
  end.
Time Qed.
Time
Lemma limit_preserving_and (P1 P2 : A \226\134\146 Prop) :
  LimitPreserving P1
  \226\134\146 LimitPreserving P2 \226\134\146 LimitPreserving (\206\187 x, P1 x \226\136\167 P2 x).
Time Proof.
Time (intros Hlim1 Hlim2 c Hc).
Time split.
Time (apply Hlim1, Hc).
Time (apply Hlim2, Hc).
Time Qed.
Time
Lemma limit_preserving_impl (P1 P2 : A \226\134\146 Prop) :
  Proper (dist 0 ==> impl) P1
  \226\134\146 LimitPreserving P2 \226\134\146 LimitPreserving (\206\187 x, P1 x \226\134\146 P2 x).
Time Proof.
Time (intros Hlim1 Hlim2 c Hc HP1).
Time (<ssreflect_plugin::ssrtclintros@0> apply Hlim2 =>n; apply Hc).
Time (eapply Hlim1, HP1).
Time (<ssreflect_plugin::ssrtclseq@0> apply dist_le with n ; last  lia).
Time Arguments pm_option_fun {_} {_} !_ _ /.
Time Notation pm_default := (pm_from_option (\206\187 x, x)).
Time (apply (conv_compl n)).
Time Qed.
Time
Lemma limit_preserving_forall {B} (P : B \226\134\146 A \226\134\146 Prop) :
  (\226\136\128 y, LimitPreserving (P y)) \226\134\146 LimitPreserving (\206\187 x, \226\136\128 y, P y x).
Time Proof.
Time (intros Hlim c Hc y).
Time by apply Hlim.
Time Qed.
Time End limit_preserving.
Time #[program]
Definition fixpoint_chain {A : ofeT} `{Inhabited A} 
  (f : A \226\134\146 A) `{!Contractive f} : chain A :=
  {| chain_car := fun i => Nat.iter (S i) f inhabitant |}.
Time Next Obligation.
Time (intros A ? f ? n).
Time
(<ssreflect_plugin::ssrtclintros@0> induction n as [| n IH] =>- 
  [|i] //= ?; try lia).
Time -
Time (apply (contractive_0 f)).
Time -
Time (apply (contractive_S f), IH; auto with lia).
Time Qed.
Time #[program]
Definition fixpoint_def `{Cofe A} `{Inhabited A} (f : A \226\134\146 A)
  `{!Contractive f} : A := compl (fixpoint_chain f).
Time Definition fixpoint_aux : seal (@fixpoint_def).
Time by eexists.
Time Qed.
Time
Definition fixpoint {A} {AC} {AiH} f {Hf} :=
  fixpoint_aux.(unseal) A AC AiH f Hf.
Time
Definition fixpoint_eq : @fixpoint = @fixpoint_def := fixpoint_aux.(seal_eq).
Time Section fixpoint.
Time Context `{Cofe A} `{Inhabited A} (f : A \226\134\146 A) `{!Contractive f}.
Time Lemma fixpoint_unfold : fixpoint f \226\137\161 f (fixpoint f).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time rewrite fixpoint_eq /fixpoint_def (conv_compl n (fixpoint_chain f)) //.
Time
(induction n as [| n IH]; simpl; eauto using contractive_0, contractive_S).
Time Qed.
Time Lemma fixpoint_unique (x : A) : x \226\137\161 f x \226\134\146 x \226\137\161 fixpoint f.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite !equiv_dist =>Hx n).
Time (induction n as [| n IH]; simpl in *).
Time -
Time (rewrite Hx fixpoint_unfold; eauto using contractive_0).
Time -
Time rewrite Hx fixpoint_unfold.
Time (apply (contractive_S _), IH).
Time Qed.
Time
Lemma fixpoint_ne (g : A \226\134\146 A) `{!Contractive g} n :
  (\226\136\128 z, f z \226\137\161{n}\226\137\161 g z) \226\134\146 fixpoint f \226\137\161{n}\226\137\161 fixpoint g.
Time Proof.
Time (intros Hfg).
Time
rewrite fixpoint_eq /fixpoint_def (conv_compl n (fixpoint_chain f))
 (conv_compl n (fixpoint_chain g)) /=.
Time (induction n as [| n IH]; simpl in *; [ by rewrite !Hfg |  ]).
Time (rewrite Hfg; apply contractive_S, IH; auto using dist_S).
Time Qed.
Time
Lemma fixpoint_proper (g : A \226\134\146 A) `{!Contractive g} :
  (\226\136\128 x, f x \226\137\161 g x) \226\134\146 fixpoint f \226\137\161 fixpoint g.
Time Proof.
Time (setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_ne).
Time Qed.
Time
Lemma fixpoint_ind (P : A \226\134\146 Prop) :
  Proper ((\226\137\161) ==> impl) P
  \226\134\146 (\226\136\131 x, P x) \226\134\146 (\226\136\128 x, P x \226\134\146 P (f x)) \226\134\146 LimitPreserving P \226\134\146 P (fixpoint f).
Time Proof.
Time (intros ? [x Hx] Hincr Hlim).
Time (set (chcar := fun i => Nat.iter (S i) f x)).
Time (assert (Hcauch : \226\136\128 n i : nat, n \226\137\164 i \226\134\146 chcar i \226\137\161{n}\226\137\161 chcar n)).
Time {
Time (intros n).
Time rewrite /chcar.
Time
(<ssreflect_plugin::ssrtclintros@0> induction n as [| n IH] =>- 
  [|i] //=; eauto using contractive_0, contractive_S 
  with lia).
Time }
Time (set (fp2 := compl {| chain_cauchy := Hcauch |})).
Time (assert (f fp2 \226\137\161 fp2)).
Time {
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time rewrite /fp2 (conv_compl n) /= /chcar.
Time
(induction n as [| n IH]; simpl; eauto using contractive_0, contractive_S).
Time }
Time rewrite -(fixpoint_unique fp2) //.
Time (<ssreflect_plugin::ssrtclintros@0> apply Hlim =>n /=).
Time by apply Nat_iter_ind.
Time Qed.
Time End fixpoint.
Time
Definition fixpointK `{Cofe A} `{Inhabited A} k (f : A \226\134\146 A)
  `{!Contractive (Nat.iter k f)} := fixpoint (Nat.iter k f).
Time Section fixpointK.
Time #[local]Set Default Proof Using "Type*".
Time Context `{Cofe A} `{Inhabited A} (f : A \226\134\146 A) (k : nat).
Time
Context {f_contractive : Contractive (Nat.iter k f)} {f_ne : NonExpansive f}.
Time Let f_proper : Proper ((\226\137\161) ==> (\226\137\161)) f := ne_proper f.
Time #[local]Existing Instance f_proper.
Time Lemma fixpointK_unfold : fixpointK k f \226\137\161 f (fixpointK k f).
Time Proof.
Time symmetry.
Time rewrite /fixpointK.
Time (apply fixpoint_unique).
Time by rewrite -Nat_iter_S_r Nat_iter_S -fixpoint_unfold.
Time Qed.
Time Lemma fixpointK_unique (x : A) : x \226\137\161 f x \226\134\146 x \226\137\161 fixpointK k f.
Time Proof.
Time (intros Hf).
Time (apply fixpoint_unique).
Time clear f_contractive.
Time (<ssreflect_plugin::ssrtclintros@0> induction k as [| k' IH] =>//=).
Time by rewrite -IH.
Time Qed.
Time Section fixpointK_ne.
Time Context (g : A \226\134\146 A) `{g_contractive : !Contractive (Nat.iter k g)}.
Time Context {g_ne : NonExpansive g}.
Time
Lemma fixpointK_ne n :
  (\226\136\128 z, f z \226\137\161{n}\226\137\161 g z) \226\134\146 fixpointK k f \226\137\161{n}\226\137\161 fixpointK k g.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /fixpointK =>Hfg /=).
Time (<ssreflect_plugin::ssrtclintros@0> apply fixpoint_ne =>z).
Time clear f_contractive g_contractive.
Time (<ssreflect_plugin::ssrtclintros@0> induction k as [| k' IH] =>//=).
Time by rewrite IH Hfg.
Time Qed.
Time
Lemma fixpointK_proper : (\226\136\128 z, f z \226\137\161 g z) \226\134\146 fixpointK k f \226\137\161 fixpointK k g.
Time Proof.
Time (setoid_rewrite equiv_dist; naive_solver eauto using fixpointK_ne).
Time Qed.
Time End fixpointK_ne.
Time
Lemma fixpointK_ind (P : A \226\134\146 Prop) :
  Proper ((\226\137\161) ==> impl) P
  \226\134\146 (\226\136\131 x, P x) \226\134\146 (\226\136\128 x, P x \226\134\146 P (f x)) \226\134\146 LimitPreserving P \226\134\146 P (fixpointK k f).
Time Proof.
Time (intros).
Time rewrite /fixpointK.
Time (apply fixpoint_ind; eauto).
Time (intros; apply Nat_iter_ind; auto).
Time Qed.
Time End fixpointK.
Time Section fixpointAB.
Time #[local]Unset Default Proof Using.
Time Context `{Cofe A} `{Cofe B} `{!Inhabited A} `{!Inhabited B}.
Time Context (fA : A \226\134\146 B \226\134\146 A).
Time Context (fB : A \226\134\146 B \226\134\146 B).
Time Context `{\226\136\128 n, Proper (dist_later n ==> dist n ==> dist n) fA}.
Time Context `{\226\136\128 n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.
Time #[local]Definition fixpoint_AB (x : A) : B := fixpoint (fB x).
Time #[local]Instance fixpoint_AB_contractive : (Contractive fixpoint_AB).
Time Proof.
Time (intros n x x' Hx; rewrite /fixpoint_AB).
Time (<ssreflect_plugin::ssrtclintros@0> apply fixpoint_ne =>y).
Time by f_contractive.
Time Qed.
Time #[local]Definition fixpoint_AA (x : A) : A := fA x (fixpoint_AB x).
Time #[local]Instance fixpoint_AA_contractive : (Contractive fixpoint_AA).
Time Proof.
Time solve_contractive.
Time Qed.
Time Definition fixpoint_A : A := fixpoint fixpoint_AA.
Time Definition fixpoint_B : B := fixpoint_AB fixpoint_A.
Time Lemma fixpoint_A_unfold : fA fixpoint_A fixpoint_B \226\137\161 fixpoint_A.
Time Proof.
Time by rewrite {+2}/fixpoint_A (fixpoint_unfold _).
Time Qed.
Time Lemma fixpoint_B_unfold : fB fixpoint_A fixpoint_B \226\137\161 fixpoint_B.
Time Proof.
Time by rewrite {+2}/fixpoint_B /fixpoint_AB (fixpoint_unfold _).
Time Qed.
Time Instance: (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) fA).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply ne_proper_2 =>n x x' ? y y' ?).
Time (f_contractive; auto using dist_S).
Time Qed.
Time Instance: (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) fB).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> apply ne_proper_2 =>n x x' ? y y' ?).
Time (f_contractive; auto using dist_S).
Time Qed.
Time Lemma fixpoint_A_unique p q : fA p q \226\137\161 p \226\134\146 fB p q \226\137\161 q \226\134\146 p \226\137\161 fixpoint_A.
Time Proof.
Time (intros HfA HfB).
Time rewrite -HfA.
Time (apply fixpoint_unique).
Time rewrite /fixpoint_AA.
Time (<ssreflect_plugin::ssrtclintros@0> f_equiv =>//).
Time (apply fixpoint_unique).
Time by rewrite HfA HfB.
Time Qed.
Time Lemma fixpoint_B_unique p q : fA p q \226\137\161 p \226\134\146 fB p q \226\137\161 q \226\134\146 q \226\137\161 fixpoint_B.
Time Proof.
Time (intros).
Time (apply fixpoint_unique).
Time by rewrite -fixpoint_A_unique.
Time Qed.
Time End fixpointAB.
Time Section fixpointAB_ne.
Time Context `{Cofe A} `{Cofe B} `{!Inhabited A} `{!Inhabited B}.
Time Context (fA fA' : A \226\134\146 B \226\134\146 A).
Time Context (fB fB' : A \226\134\146 B \226\134\146 B).
Time Context `{\226\136\128 n, Proper (dist_later n ==> dist n ==> dist n) fA}.
Time Context `{\226\136\128 n, Proper (dist_later n ==> dist n ==> dist n) fA'}.
Time Context `{\226\136\128 n, Proper (dist_later n ==> dist_later n ==> dist n) fB}.
Time Context `{\226\136\128 n, Proper (dist_later n ==> dist_later n ==> dist n) fB'}.
Time
Lemma fixpoint_A_ne n :
  (\226\136\128 x y, fA x y \226\137\161{n}\226\137\161 fA' x y)
  \226\134\146 (\226\136\128 x y, fB x y \226\137\161{n}\226\137\161 fB' x y) \226\134\146 fixpoint_A fA fB \226\137\161{n}\226\137\161 fixpoint_A fA' fB'.
Time Proof.
Time (intros HfA HfB).
Time (<ssreflect_plugin::ssrtclintros@0> apply fixpoint_ne =>z).
Time rewrite /fixpoint_AA /fixpoint_AB HfA.
Time f_equiv.
Time by apply fixpoint_ne.
Time Qed.
Time
Lemma fixpoint_B_ne n :
  (\226\136\128 x y, fA x y \226\137\161{n}\226\137\161 fA' x y)
  \226\134\146 (\226\136\128 x y, fB x y \226\137\161{n}\226\137\161 fB' x y) \226\134\146 fixpoint_B fA fB \226\137\161{n}\226\137\161 fixpoint_B fA' fB'.
Time Proof.
Time (intros HfA HfB).
Time (<ssreflect_plugin::ssrtclintros@0> apply fixpoint_ne =>z).
Time rewrite HfB.
Time f_contractive.
Time (apply fixpoint_A_ne; auto using dist_S).
Time Qed.
Time
Lemma fixpoint_A_proper :
  (\226\136\128 x y, fA x y \226\137\161 fA' x y)
  \226\134\146 (\226\136\128 x y, fB x y \226\137\161 fB' x y) \226\134\146 fixpoint_A fA fB \226\137\161 fixpoint_A fA' fB'.
Time Proof.
Time (setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_A_ne).
Time Qed.
Time
Lemma fixpoint_B_proper :
  (\226\136\128 x y, fA x y \226\137\161 fA' x y)
  \226\134\146 (\226\136\128 x y, fB x y \226\137\161 fB' x y) \226\134\146 fixpoint_B fA fB \226\137\161 fixpoint_B fA' fB'.
Time Proof.
Time (setoid_rewrite equiv_dist; naive_solver eauto using fixpoint_B_ne).
Time Qed.
Time End fixpointAB_ne.
Time
Record ofe_mor (A B : ofeT) : Type :=
 OfeMor {ofe_mor_car :> A \226\134\146 B; ofe_mor_ne : NonExpansive ofe_mor_car}.
Time Arguments OfeMor {_} {_} _ {_}.
Time Add Printing Constructor ofe_mor.
Time Existing Instance ofe_mor_ne.
Time
Notation "'\206\187ne' x .. y , t" :=
  (@OfeMor _ _ (\206\187 x, .. (@OfeMor _ _ (\206\187 y, t) _) ..) _)
  (at level 200, x binder, y binder, right associativity).
Time Section ofe_mor.
Time Context {A B : ofeT}.
Time #[global]
Instance ofe_mor_proper  (f : ofe_mor A B): (Proper ((\226\137\161) ==> (\226\137\161)) f).
Time Proof.
Time (apply ne_proper, ofe_mor_ne).
Time Qed.
Time
Instance ofe_mor_equiv : (Equiv (ofe_mor A B)) := (\206\187 f g, \226\136\128 x, f x \226\137\161 g x).
Time
Instance ofe_mor_dist : (Dist (ofe_mor A B)) := (\206\187 n f g, \226\136\128 x, f x \226\137\161{n}\226\137\161 g x).
Time Definition ofe_mor_ofe_mixin : OfeMixin (ofe_mor A B).
Time Proof.
Time split.
Time -
Time (intros f g; split; [ intros Hfg n k; apply equiv_dist, Hfg |  ]).
Time
(intros Hfg k; <ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n;
  apply Hfg).
Time -
Time (intros n; split).
Time +
Time by intros f x.
Time +
Time by intros f g ? x.
Time +
Time by intros f g h ? ? x; trans g x.
Time -
Time by intros n f g ? x; apply dist_S.
Time Qed.
Time Canonical Structure ofe_morO := OfeT (ofe_mor A B) ofe_mor_ofe_mixin.
Time #[program]
Definition ofe_mor_chain (c : chain ofe_morO) (x : A) : 
  chain B := {| chain_car := fun n => c n x |}.
Time Next Obligation.
Time (intros c x n i ?).
Time by apply (chain_cauchy c).
Time Qed.
Time #[program]
Definition ofe_mor_compl `{Cofe B} : Compl ofe_morO :=
  \206\187 c, {| ofe_mor_car := fun x => compl (ofe_mor_chain c x) |}.
Time Next Obligation.
Time (intros ? c n x y Hx).
Time
by rewrite (conv_compl n (ofe_mor_chain c x))
 (conv_compl n (ofe_mor_chain c y)) /= Hx.
Time Qed.
Time #[global, program]
Instance ofe_mor_cofe  `{Cofe B}: (Cofe ofe_morO) :=
 {| compl := ofe_mor_compl |}.
Time Next Obligation.
Time (intros ? n c x; simpl).
Time by rewrite (conv_compl n (ofe_mor_chain c x)) /=.
Time Qed.
Time #[global]Instance ofe_mor_car_ne : (NonExpansive2 (@ofe_mor_car A B)).
Time Proof.
Time (intros n f g Hfg x y Hx; rewrite Hx; apply Hfg).
Time Qed.
Time #[global]
Instance ofe_mor_car_proper :
 (Proper ((\226\137\161) ==> (\226\137\161) ==> (\226\137\161)) (@ofe_mor_car A B)) := 
 (ne_proper_2 _).
Time Lemma ofe_mor_ext (f g : ofe_mor A B) : f \226\137\161 g \226\134\148 (\226\136\128 x, f x \226\137\161 g x).
Time Proof.
Time done.
Time Qed.
Time End ofe_mor.
Time Arguments ofe_morO : clear implicits.
Time
Notation "A -n> B" := (ofe_morO A B)
  (at level 99, B  at level 200, right associativity).
Time
Instance ofe_mor_inhabited  {A B : ofeT} `{Inhabited B}:
 (Inhabited (A -n> B)) := (populate (\206\187ne _, inhabitant)).
Time Definition cid {A} : A -n> A := OfeMor id.
Time Instance: (Params (@cid) 1) := { }.
Time Definition cconst {A B : ofeT} (x : B) : A -n> B := OfeMor (const x).
Time Instance: (Params (@cconst) 2) := { }.
Time
Definition ccompose {A} {B} {C} (f : B -n> C) (g : A -n> B) : 
  A -n> C := OfeMor (f \226\136\152 g).
Time Instance: (Params (@ccompose) 3) := { }.
Time Infix "\226\151\142" := ccompose (at level 40, left associativity).
Time #[global]
Instance ccompose_ne  {A} {B} {C}: (NonExpansive2 (@ccompose A B C)).
Time Proof.
Time (intros n ? ? Hf g1 g2 Hg x).
Time rewrite /= (Hg x) (Hf (g2 x)) //.
Time Qed.
Time
Definition ofe_mor_map {A} {A'} {B} {B'} (f : A' -n> A) 
  (g : B -n> B') (h : A -n> B) : A' -n> B' := g \226\151\142 h \226\151\142 f.
Time
Instance ofe_mor_map_ne  {A} {A'} {B} {B'} n:
 (Proper (dist n ==> dist n ==> dist n ==> dist n) (@ofe_mor_map A A' B B')).
Time Proof.
Time (intros ? ? ? ? ? ? ? ? ?).
Time by repeat apply ccompose_ne.
Time Qed.
Time
Definition ofe_morO_map {A} {A'} {B} {B'} (f : A' -n> A) 
  (g : B -n> B') : (A -n> B) -n> A' -n> B' := OfeMor (ofe_mor_map f g).
Time
Instance ofe_morO_map_ne  {A} {A'} {B} {B'}:
 (NonExpansive2 (@ofe_morO_map A A' B B')).
Time Proof.
Time (intros n f f' Hf g g' Hg ?).
Time rewrite /= /ofe_mor_map.
Time by repeat apply ccompose_ne.
Time Qed.
Time Section unit.
Time Instance unit_dist : (Dist unit) := (\206\187 _ _ _, True).
Time Definition unit_ofe_mixin : OfeMixin unit.
Time Proof.
Time by repeat split; try exists 0.
Time Qed.
Time Canonical Structure unitO : ofeT := OfeT unit unit_ofe_mixin.
Time #[global, program]
Instance unit_cofe : (Cofe unitO) := { compl :=fun x => ()}.
Time Next Obligation.
Time by repeat split; try exists 0.
Time Qed.
Time #[global]Instance unit_ofe_discrete : (OfeDiscrete unitO).
Time Proof.
Time done.
Time Qed.
Time End unit.
Time Section empty.
Time Instance Empty_set_dist : (Dist Empty_set) := (\206\187 _ _ _, True).
Time Definition Empty_set_ofe_mixin : OfeMixin Empty_set.
Time Proof.
Time by repeat split; try exists 0.
Time Qed.
Time
Canonical Structure Empty_setO : ofeT := OfeT Empty_set Empty_set_ofe_mixin.
Time #[global, program]
Instance Empty_set_cofe : (Cofe Empty_setO) := { compl :=fun x => x 0}.
Time Next Obligation.
Time by repeat split; try exists 0.
Time Qed.
Time #[global]Instance Empty_set_ofe_discrete : (OfeDiscrete Empty_setO).
Time Proof.
Time done.
Time Qed.
Time End empty.
Time Section product.
Time Context {A B : ofeT}.
Time
Instance prod_dist : (Dist (A * B)) := (\206\187 n, prod_relation (dist n) (dist n)).
Time #[global]Instance pair_ne : (NonExpansive2 (@pair A B)) := _.
Time #[global]Instance fst_ne : (NonExpansive (@fst A B)) := _.
Time #[global]Instance snd_ne : (NonExpansive (@snd A B)) := _.
Time Definition prod_ofe_mixin : OfeMixin (A * B).
Time Proof.
Time split.
Time -
Time (intros x y; unfold dist, prod_dist, equiv, prod_equiv, prod_relation).
Time (rewrite !equiv_dist; naive_solver).
Time -
Time (apply _).
Time -
Time by intros n [x1 y1] [x2 y2] [? ?]; split; apply dist_S.
Time Qed.
Time Canonical Structure prodO : ofeT := OfeT (A * B) prod_ofe_mixin.
Time #[global, program]
Instance prod_cofe  `{Cofe A} `{Cofe B}: (Cofe prodO) := {
 compl :=fun c => (compl (chain_map fst c), compl (chain_map snd c))}.
Time Next Obligation.
Time (intros ? ? n c; split).
Time (apply (conv_compl n (chain_map fst c))).
Time (apply (conv_compl n (chain_map snd c))).
Time Qed.
Time #[global]
Instance prod_discrete  (x : A * B):
 (Discrete x.1 \226\134\146 Discrete x.2 \226\134\146 Discrete x).
Time Proof.
Time by intros ? ? ? [? ?]; split; apply (discrete _).
Time Qed.
Time #[global]
Instance prod_ofe_discrete :
 (OfeDiscrete A \226\134\146 OfeDiscrete B \226\134\146 OfeDiscrete prodO).
Time Proof.
Time (intros ? ? [? ?]; apply _).
Time Qed.
Time End product.
Time Arguments prodO : clear implicits.
Time Typeclasses Opaque prod_dist.
Time
Instance prod_map_ne  {A A' B B' : ofeT} n:
 (Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==> dist n ==> dist n)
    (@prod_map A A' B B')).
Time Proof.
Time by intros f f' Hf g g' Hg ? ? [? ?]; split; [ apply Hf | apply Hg ].
Time Qed.
Time
Definition prodO_map {A} {A'} {B} {B'} (f : A -n> A') 
  (g : B -n> B') : prodO A B -n> prodO A' B' := OfeMor (prod_map f g).
Time
Instance prodO_map_ne  {A} {A'} {B} {B'}:
 (NonExpansive2 (@prodO_map A A' B B')).
Time Proof.
Time (intros n f f' Hf g g' Hg [? ?]; split; [ apply Hf | apply Hg ]).
Time Qed.
Time
Record oFunctor :=
 OFunctor {oFunctor_car : \226\136\128 A `{!Cofe A} B `{!Cofe B}, ofeT;
           oFunctor_map :
            forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} `{!Cofe B2},
            (A2 -n> A1) * (B1 -n> B2)
            \226\134\146 oFunctor_car A1 B1 -n> oFunctor_car A2 B2;
           oFunctor_ne :
            forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} `{!Cofe B2},
            NonExpansive (@oFunctor_map A1 _ A2 _ B1 _ B2 _);
           oFunctor_id :
            forall `{!Cofe A} `{!Cofe B} (x : oFunctor_car A B),
            oFunctor_map (cid, cid) x \226\137\161 x;
           oFunctor_compose :
            forall `{!Cofe A1} `{!Cofe A2} `{!Cofe A3} 
              `{!Cofe B1} `{!Cofe B2} `{!Cofe B3} 
              (f : A2 -n> A1) (g : A3 -n> A2) (f' : B1 -n> B2)
              (g' : B2 -n> B3) x,
            oFunctor_map (f \226\151\142 g, g' \226\151\142 f') x
            \226\137\161 oFunctor_map (g, g') (oFunctor_map (f, f') x)}.
Time Existing Instance oFunctor_ne.
Time Instance: (Params (@oFunctor_map) 9) := { }.
Time Delimit Scope oFunctor_scope with OF.
Time Bind Scope oFunctor_scope with oFunctor.
Time
Class oFunctorContractive (F : oFunctor) :=
    oFunctor_contractive :>
      forall `{!Cofe A1} `{!Cofe A2} `{!Cofe B1} `{!Cofe B2},
      Contractive (@oFunctor_map F A1 _ A2 _ B1 _ B2 _).
Time Hint Mode oFunctorContractive !: typeclass_instances.
Time
Definition oFunctor_diag (F : oFunctor) (A : ofeT) 
  `{!Cofe A} : ofeT := oFunctor_car F A A.
Time Coercion oFunctor_diag : oFunctor >-> Funclass.
Time #[program]
Definition constOF (B : ofeT) : oFunctor :=
  {|
  oFunctor_car := fun A1 A2 _ _ => B;
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ f => cid |}.
Time Solve Obligations with done.
Time Coercion constOF : ofeT >-> oFunctor.
Time Instance constOF_contractive  B: (oFunctorContractive (constOF B)).
Time Proof.
Time (rewrite /oFunctorContractive; apply _).
Time Qed.
Time #[program]
Definition idOF : oFunctor :=
  {|
  oFunctor_car := fun A1 _ A2 _ => A2;
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ f => f.2 |}.
Time Solve Obligations with done.
Time Notation "\226\136\153" := idOF : oFunctor_scope.
Time #[program]
Definition prodOF (F1 F2 : oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ =>
                  prodO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  prodO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg) |}.
Time Next Obligation.
Time
(intros ? ? A1 ? A2 ? B1 ? B2 ? n ? ? ?; by
  apply prodO_map_ne; apply oFunctor_ne).
Time Qed.
Time Next Obligation.
Time by intros F1 F2 A ? B ? [? ?]; rewrite /= !oFunctor_id.
Time Qed.
Time Next Obligation.
Time (intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [? ?]; simpl).
Time by rewrite !oFunctor_compose.
Time Qed.
Time Notation "F1 * F2" := (prodOF F1%OF F2%OF) : oFunctor_scope.
Time
Instance prodOF_contractive  F1 F2:
 (oFunctorContractive F1
  \226\134\146 oFunctorContractive F2 \226\134\146 oFunctorContractive (prodOF F1 F2)).
Time Proof.
Time
(intros ? ? A1 ? A2 ? B1 ? B2 ? n ? ? ?; by
  apply prodO_map_ne; apply oFunctor_contractive).
Time Qed.
Time #[program]
Definition ofe_morOF (F1 F2 : oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ => oFunctor_car F1 B A -n> oFunctor_car F2 A B;
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  ofe_morO_map (oFunctor_map F1 (fg.2, fg.1))
                    (oFunctor_map F2 fg) |}.
Time Next Obligation.
Time (intros F1 F2 A1 ? A2 ? B1 ? B2 ? n [f g] [f' g'] Hfg; simpl in *).
Time (apply ofe_morO_map_ne; apply oFunctor_ne; split; by apply Hfg).
Time Qed.
Time Next Obligation.
Time (intros F1 F2 A ? B ? [f ?] ?; simpl).
Time rewrite /= !oFunctor_id.
Time (apply (ne_proper f)).
