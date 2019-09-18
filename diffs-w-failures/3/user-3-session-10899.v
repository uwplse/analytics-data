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
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> apply equiv_dist =>n).
Time by rewrite !conv_compl.
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
Time (apply (discrete _), dist_le with n; auto with lia).
Time Qed.
Time Lemma discrete_iff_0 n (x : A) `{!Discrete x} y : x \226\137\161{0}\226\137\161 y \226\134\148 x \226\137\161{n}\226\137\161 y.
Time Proof.
Time by rewrite -!discrete_iff.
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
Time (apply oFunctor_id).
Time Qed.
Time Next Obligation.
Time
(intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [h ?] ?; simpl in *).
Time rewrite -!oFunctor_compose.
Time (do 2 apply (ne_proper _)).
Time (apply oFunctor_compose).
Time Qed.
Time Notation "F1 -n> F2" := (ofe_morOF F1%OF F2%OF) : oFunctor_scope.
Time
Instance ofe_morOF_contractive  F1 F2:
 (oFunctorContractive F1
  \226\134\146 oFunctorContractive F2 \226\134\146 oFunctorContractive (ofe_morOF F1 F2)).
Time Proof.
Time (intros ? ? A1 ? A2 ? B1 ? B2 ? n [f g] [f' g'] Hfg; simpl in *).
Time
(apply ofe_morO_map_ne; apply oFunctor_contractive; destruct n, Hfg; by split).
Time Qed.
Time Section sum.
Time Context {A B : ofeT}.
Time
Instance sum_dist : (Dist (A + B)) := (\206\187 n, sum_relation (dist n) (dist n)).
Time #[global]Instance inl_ne : (NonExpansive (@inl A B)) := _.
Time #[global]Instance inr_ne : (NonExpansive (@inr A B)) := _.
Time #[global]Instance inl_ne_inj : (Inj (dist n) (dist n) (@inl A B)) := _.
Time #[global]Instance inr_ne_inj : (Inj (dist n) (dist n) (@inr A B)) := _.
Time Definition sum_ofe_mixin : OfeMixin (A + B).
Time Proof.
Time split.
Time -
Time (intros x y; <ssreflect_plugin::ssrtclintros@0> split =>Hx).
Time +
Time
(<ssreflect_plugin::ssrtclintros@0> destruct Hx =>n; constructor; by
  apply equiv_dist).
Time +
Time
(destruct (Hx 0); constructor; <ssreflect_plugin::ssrtclintros@0>
  apply equiv_dist =>n; by apply (inj _)).
Time -
Time (apply _).
Time -
Time (destruct 1; constructor; by apply dist_S).
Time Qed.
Time Canonical Structure sumO : ofeT := OfeT (A + B) sum_ofe_mixin.
Time #[program]
Definition inl_chain (c : chain sumO) (a : A) : chain A :=
  {| chain_car := fun n => match c n with
                           | inl a' => a'
                           | _ => a
                           end |}.
Time Next Obligation.
Time (intros c a n i ?; simpl).
Time by destruct (chain_cauchy c n i).
Time Qed.
Time #[program]
Definition inr_chain (c : chain sumO) (b : B) : chain B :=
  {| chain_car := fun n => match c n with
                           | inr b' => b'
                           | _ => b
                           end |}.
Time Next Obligation.
Time (intros c b n i ?; simpl).
Time by destruct (chain_cauchy c n i).
Time Qed.
Time
Definition sum_compl `{Cofe A} `{Cofe B} : Compl sumO :=
  \206\187 c,
    match c 0 with
    | inl a => inl (compl (inl_chain c a))
    | inr b => inr (compl (inr_chain c b))
    end.
Time #[global, program]
Instance sum_cofe  `{Cofe A} `{Cofe B}: (Cofe sumO) := { compl :=sum_compl}.
Time Next Obligation.
Time (intros ? ? n c; rewrite /compl /sum_compl).
Time
(<ssreflect_plugin::ssrtclseq@0> feed inversion chain_cauchy c 0 n ; first 
 by auto with lia; constructor).
Time -
Time rewrite (conv_compl n (inl_chain c _)) /=.
Time (destruct (c n); naive_solver).
Time -
Time rewrite (conv_compl n (inr_chain c _)) /=.
Time (destruct (c n); naive_solver).
Time Qed.
Time #[global]
Instance inl_discrete  (x : A): (Discrete x \226\134\146 Discrete (inl x)).
Time Proof.
Time (inversion_clear 2; constructor; by apply (discrete _)).
Time Qed.
Time #[global]
Instance inr_discrete  (y : B): (Discrete y \226\134\146 Discrete (inr y)).
Time Proof.
Time (inversion_clear 2; constructor; by apply (discrete _)).
Time Qed.
Time #[global]
Instance sum_ofe_discrete :
 (OfeDiscrete A \226\134\146 OfeDiscrete B \226\134\146 OfeDiscrete sumO).
Time Proof.
Time (intros ? ? [?| ?]; apply _).
Time Qed.
Time End sum.
Time Arguments sumO : clear implicits.
Time Typeclasses Opaque sum_dist.
Time
Instance sum_map_ne  {A A' B B' : ofeT} n:
 (Proper ((dist n ==> dist n) ==> (dist n ==> dist n) ==> dist n ==> dist n)
    (@sum_map A A' B B')).
Time Proof.
Time
(intros f f' Hf g g' Hg ? ?; destruct 1; constructor;
  [ by apply Hf | by apply Hg ]).
Time Qed.
Time
Definition sumO_map {A} {A'} {B} {B'} (f : A -n> A') 
  (g : B -n> B') : sumO A B -n> sumO A' B' := OfeMor (sum_map f g).
Time
Instance sumO_map_ne  {A} {A'} {B} {B'}:
 (NonExpansive2 (@sumO_map A A' B B')).
Time Proof.
Time (intros n f f' Hf g g' Hg [?| ?]; constructor; [ apply Hf | apply Hg ]).
Time Qed.
Time #[program]
Definition sumOF (F1 F2 : oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ =>
                  sumO (oFunctor_car F1 A B) (oFunctor_car F2 A B);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  sumO_map (oFunctor_map F1 fg) (oFunctor_map F2 fg) |}.
Time Next Obligation.
Time
(intros ? ? A1 ? A2 ? B1 ? B2 ? n ? ? ?; by
  apply sumO_map_ne; apply oFunctor_ne).
Time Qed.
Time Next Obligation.
Time by intros F1 F2 A ? B ? [?| ?]; rewrite /= !oFunctor_id.
Time Qed.
Time Next Obligation.
Time
(intros F1 F2 A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' [?| ?]; simpl; by
  rewrite !oFunctor_compose).
Time Qed.
Time Notation "F1 + F2" := (sumOF F1%OF F2%OF) : oFunctor_scope.
Time
Instance sumOF_contractive  F1 F2:
 (oFunctorContractive F1
  \226\134\146 oFunctorContractive F2 \226\134\146 oFunctorContractive (sumOF F1 F2)).
Time Proof.
Time
(intros ? ? A1 ? A2 ? B1 ? B2 ? n ? ? ?; by
  apply sumO_map_ne; apply oFunctor_contractive).
Time Qed.
Time Section discrete_ofe.
Time Context `{Equiv A} (Heq : @Equivalence A (\226\137\161)).
Time Instance discrete_dist : (Dist A) := (\206\187 n x y, x \226\137\161 y).
Time Definition discrete_ofe_mixin : OfeMixin A.
Time Proof  using ((Type))*.
Time split.
Time -
Time (intros x y; split; [ done | intros Hn; apply (Hn 0) ]).
Time -
Time done.
Time -
Time done.
Time Qed.
Time #[global]
Instance discrete_ofe_discrete : (OfeDiscrete (OfeT A discrete_ofe_mixin)).
Time Proof.
Time by intros x y.
Time Qed.
Time #[global, program]
Instance discrete_cofe : (Cofe (OfeT A discrete_ofe_mixin)) := {
 compl :=fun c => c 0}.
Time Next Obligation.
Time (intros n c).
Time (rewrite /compl /=; symmetry; apply (chain_cauchy c 0 n)).
Time lia.
Time Qed.
Time End discrete_ofe.
Time Notation discreteO A:= (OfeT A (discrete_ofe_mixin _)).
Time Notation leibnizO A:= (OfeT A (@discrete_ofe_mixin _ equivL _)).
Time Notation discrete_ofe_equivalence_of A:= _ (only parsing).
Time Instance leibnizO_leibniz  A: (LeibnizEquiv (leibnizO A)).
Time Proof.
Time by intros x y.
Time Qed.
Time Canonical Structure boolO := leibnizO bool.
Time Canonical Structure natO := leibnizO nat.
Time Canonical Structure positiveO := leibnizO positive.
Time Canonical Structure NO := leibnizO N.
Time Canonical Structure ZO := leibnizO Z.
Time Section option.
Time Context {A : ofeT}.
Time
Instance option_dist : (Dist (option A)) := (\206\187 n, option_Forall2 (dist n)).
Time
Lemma dist_option_Forall2 n mx my :
  mx \226\137\161{n}\226\137\161 my \226\134\148 option_Forall2 (dist n) mx my.
Time Proof.
Time done.
Time Qed.
Time Definition option_ofe_mixin : OfeMixin (option A).
Time Proof.
Time split.
Time -
Time
(intros mx my; split; [ by destruct 1; constructor; apply equiv_dist |  ]).
Time (intros Hxy; destruct (Hxy 0); constructor; apply equiv_dist).
Time by intros n; feed inversion Hxy n.
Time -
Time (apply _).
Time -
Time (destruct 1; constructor; by apply dist_S).
Time Qed.
Time Canonical Structure optionO := OfeT (option A) option_ofe_mixin.
Time #[program]
Definition option_chain (c : chain optionO) (x : A) : 
  chain A := {| chain_car := fun n => default x (c n) |}.
Time Next Obligation.
Time (intros c x n i ?; simpl).
Time by destruct (chain_cauchy c n i).
Time Qed.
Time
Definition option_compl `{Cofe A} : Compl optionO :=
  \206\187 c,
    match c 0 with
    | Some x => Some (compl (option_chain c x))
    | None => None
    end.
Time #[global, program]
Instance option_cofe  `{Cofe A}: (Cofe optionO) := { compl :=option_compl}.
Time Next Obligation.
Time (intros ? n c; rewrite /compl /option_compl).
Time (feed inversion chain_cauchy c 0 n; auto with lia; [  ]).
Time constructor.
Time rewrite (conv_compl n (option_chain c _)) /=.
Time (destruct (c n); naive_solver).
Time Qed.
Time #[global]
Instance option_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete optionO).
Time Proof.
Time (destruct 2; constructor; by apply (discrete _)).
Time Qed.
Time #[global]Instance Some_ne : (NonExpansive (@Some A)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]Instance is_Some_ne  n: (Proper (dist n ==> iff) (@is_Some A)).
Time Proof.
Time (destruct 1; split; eauto).
Time Qed.
Time #[global]Instance Some_dist_inj : (Inj (dist n) (dist n) (@Some A)).
Time Proof.
Time by inversion_clear 1.
Time Qed.
Time #[global]
Instance from_option_ne  {B} (R : relation B) (f : A \226\134\146 B) 
 n: (Proper (dist n ==> R) f \226\134\146 Proper (R ==> dist n ==> R) (from_option f)).
Time Proof.
Time (destruct 3; simpl; auto).
Time Qed.
Time #[global]Instance None_discrete : (Discrete (@None A)).
Time Proof.
Time (inversion_clear 1; constructor).
Time Qed.
Time #[global]Instance Some_discrete  x: (Discrete x \226\134\146 Discrete (Some x)).
Time Proof.
Time by intros ?; inversion_clear 1; constructor; apply discrete.
Time Qed.
Time Lemma dist_None n mx : mx \226\137\161{n}\226\137\161 None \226\134\148 mx = None.
Time Proof.
Time (split; [ by inversion_clear 1 | by intros -> ]).
Time Qed.
Time
Lemma dist_Some_inv_l n mx my x :
  mx \226\137\161{n}\226\137\161 my \226\134\146 mx = Some x \226\134\146 \226\136\131 y, my = Some y \226\136\167 x \226\137\161{n}\226\137\161 y.
Time Proof.
Time (destruct 1; naive_solver).
Time Qed.
Time
Lemma dist_Some_inv_r n mx my y :
  mx \226\137\161{n}\226\137\161 my \226\134\146 my = Some y \226\134\146 \226\136\131 x, mx = Some x \226\136\167 x \226\137\161{n}\226\137\161 y.
Time Proof.
Time (destruct 1; naive_solver).
Time Qed.
Time
Lemma dist_Some_inv_l' n my x :
  Some x \226\137\161{n}\226\137\161 my \226\134\146 \226\136\131 x', Some x' = my \226\136\167 x \226\137\161{n}\226\137\161 x'.
Time Proof.
Time (intros ?%(dist_Some_inv_l _ _ _ x); naive_solver).
Time Qed.
Time
Lemma dist_Some_inv_r' n mx y :
  mx \226\137\161{n}\226\137\161 Some y \226\134\146 \226\136\131 y', mx = Some y' \226\136\167 y \226\137\161{n}\226\137\161 y'.
Time Proof.
Time (intros ?%(dist_Some_inv_r _ _ _ y); naive_solver).
Time Qed.
Time End option.
Time Typeclasses Opaque option_dist.
Time Arguments optionO : clear implicits.
Time
Instance option_fmap_ne  {A B : ofeT} n:
 (Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@fmap option _ A B)).
Time Proof.
Time (intros f f' Hf ? ? []; constructor; auto).
Time Qed.
Time
Instance option_mbind_ne  {A B : ofeT} n:
 (Proper ((dist n ==> dist n) ==> dist n ==> dist n) (@mbind option _ A B)).
Time Proof.
Time (destruct 2; simpl; auto).
Time Qed.
Time
Instance option_mjoin_ne  {A : ofeT} n:
 (Proper (dist n ==> dist n) (@mjoin option _ A)).
Time Proof.
Time (destruct 1 as [? ? []| ]; simpl; by constructor).
Time Qed.
Time
Definition optionO_map {A} {B} (f : A -n> B) : optionO A -n> optionO B :=
  OfeMor (fmap f : optionO A \226\134\146 optionO B).
Time Instance optionO_map_ne  A B: (NonExpansive (@optionO_map A B)).
Time Proof.
Time by intros n f f' Hf []; constructor; apply Hf.
Time Qed.
Time #[program]
Definition optionOF (F : oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ => optionO (oFunctor_car F A B);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  optionO_map (oFunctor_map F fg) |}.
Time Next Obligation.
Time
by intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg; apply optionO_map_ne, oFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x).
Time rewrite /= -{+2}(option_fmap_id x).
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_equiv_ext =>y;
  apply oFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x).
Time rewrite /= -option_fmap_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply option_fmap_equiv_ext =>y;
  apply oFunctor_compose).
Time Qed.
Time
Instance optionOF_contractive  F:
 (oFunctorContractive F \226\134\146 oFunctorContractive (optionOF F)).
Time Proof.
Time
by
 intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply optionO_map_ne, oFunctor_contractive.
Time Qed.
Time Record later (A : Type) : Type := Next {later_car : A}.
Time Add Printing Constructor later.
Time Arguments Next {_} _.
Time Arguments later_car {_} _.
Time Instance: (Params (@Next) 1) := { }.
Time Section later.
Time Context {A : ofeT}.
Time
Instance later_equiv : (Equiv (later A)) :=
 (\206\187 x y, later_car x \226\137\161 later_car y).
Time
Instance later_dist : (Dist (later A)) :=
 (\206\187 n x y, dist_later n (later_car x) (later_car y)).
Time Definition later_ofe_mixin : OfeMixin (later A).
Time Proof.
Time split.
Time -
Time (intros x y; unfold equiv, later_equiv; rewrite !equiv_dist).
Time split.
Time (intros Hxy [| n]; [ done | apply Hxy ]).
Time (intros Hxy n; apply (Hxy (S n))).
Time -
Time (split; rewrite /dist /later_dist).
Time +
Time by intros [x].
Time +
Time by intros [x] [y].
Time +
Time by intros [x] [y] [z] ? ?; trans y.
Time -
Time
(intros [| n] [x] [y] ?; [ done |  ]; rewrite /dist /later_dist; by
  apply dist_S).
Time Qed.
Time Canonical Structure laterO : ofeT := OfeT (later A) later_ofe_mixin.
Time #[program]
Definition later_chain (c : chain laterO) : chain A :=
  {| chain_car := fun n => later_car (c (S n)) |}.
Time Next Obligation.
Time (intros c n i ?; apply (chain_cauchy c (S n)); lia).
Time Qed.
Time #[global, program]
Instance later_cofe  `{Cofe A}: (Cofe laterO) := {
 compl :=fun c => Next (compl (later_chain c))}.
Time Next Obligation.
Time (intros ? [| n] c; [ done | by apply (conv_compl n (later_chain c)) ]).
Time Qed.
Time #[global]Instance Next_contractive : (Contractive (@Next A)).
Time Proof.
Time by intros [| n] x y.
Time Qed.
Time #[global]Instance Later_inj  n: (Inj (dist n) (dist (S n)) (@Next A)).
Time Proof.
Time by intros x y.
Time Qed.
Time Lemma Next_uninj x : \226\136\131 a, x \226\137\161 Next a.
Time Proof.
Time by exists (later_car x).
Time Qed.
Time
Instance later_car_anti_contractive  n:
 (Proper (dist n ==> dist_later n) later_car).
Time Proof.
Time move  {}=>[x] [y] /= Hxy.
Time done.
Time Qed.
Time
Lemma contractive_alt {B : ofeT} (f : A \226\134\146 B) :
  Contractive f
  \226\134\148 (\226\136\131 g : later A \226\134\146 B, NonExpansive g \226\136\167 (\226\136\128 x, f x \226\137\161 g (Next x))).
Time Proof.
Time split.
Time -
Time (intros Hf).
Time
(exists (f \226\136\152 later_car); <ssreflect_plugin::ssrtclintros@0> split =>// n x y
  ?).
Time by f_equiv.
Time -
Time (intros (g, (Hg, Hf)) n x y Hxy).
Time rewrite !Hf.
Time by apply Hg.
Time Qed.
Time End later.
Time Arguments laterO : clear implicits.
Time
Definition later_map {A} {B} (f : A \226\134\146 B) (x : later A) : 
  later B := Next (f (later_car x)).
Time
Instance later_map_ne  {A B : ofeT} (f : A \226\134\146 B) n:
 (Proper (dist (pred n) ==> dist (pred n)) f
  \226\134\146 Proper (dist n ==> dist n) (later_map f)) |0.
Time Proof.
Time (destruct n as [| n]; intros Hf [x] [y] ?; do 2 red; simpl; auto).
Time Qed.
Time Lemma later_map_id {A} (x : later A) : later_map id x = x.
Time Proof.
Time by destruct x.
Time Qed.
Time
Lemma later_map_compose {A} {B} {C} (f : A \226\134\146 B) (g : B \226\134\146 C) 
  (x : later A) : later_map (g \226\136\152 f) x = later_map g (later_map f x).
Time Proof.
Time by destruct x.
Time Qed.
Time
Lemma later_map_ext {A B : ofeT} (f g : A \226\134\146 B) x :
  (\226\136\128 x, f x \226\137\161 g x) \226\134\146 later_map f x \226\137\161 later_map g x.
Time Proof.
Time (destruct x; intros Hf; apply Hf).
Time Qed.
Time
Definition laterO_map {A} {B} (f : A -n> B) : laterO A -n> laterO B :=
  OfeMor (later_map f).
Time
Instance laterO_map_contractive  (A B : ofeT):
 (Contractive (@laterO_map A B)).
Time Proof.
Time (intros [| n] f g Hf n'; [ done |  ]; apply Hf; lia).
Time Qed.
Time #[program]
Definition laterOF (F : oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ => laterO (oFunctor_car F A B);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  laterO_map (oFunctor_map F fg) |}.
Time Next Obligation.
Time (intros F A1 ? A2 ? B1 ? B2 ? n fg fg' ?).
Time by apply (contractive_ne laterO_map), oFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros F A ? B ? x; simpl).
Time rewrite -{+2}(later_map_id x).
Time (<ssreflect_plugin::ssrtclintros@0> apply later_map_ext =>y).
Time by rewrite oFunctor_id.
Time Qed.
Time Next Obligation.
Time (intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl).
Time rewrite -later_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply later_map_ext =>y;
  apply oFunctor_compose).
Time Qed.
Time
Notation "\226\150\182 F" := (laterOF F%OF) (at level 20, right associativity) :
  oFunctor_scope.
Time Instance laterOF_contractive  F: (oFunctorContractive (laterOF F)).
Time Proof.
Time (intros A1 ? A2 ? B1 ? B2 ? n fg fg' Hfg).
Time (apply laterO_map_contractive).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct n as [| n]; simpl in * ; first 
 done).
Time (apply oFunctor_ne, Hfg).
Time Qed.
Time Definition discrete_fun {A} (B : A \226\134\146 ofeT) := \226\136\128 x : A, B x.
Time Section discrete_fun.
Time Context {A : Type} {B : A \226\134\146 ofeT}.
Time Implicit Types f g : discrete_fun B.
Time
Instance discrete_fun_equiv : (Equiv (discrete_fun B)) :=
 (\206\187 f g, \226\136\128 x, f x \226\137\161 g x).
Time
Instance discrete_fun_dist : (Dist (discrete_fun B)) :=
 (\206\187 n f g, \226\136\128 x, f x \226\137\161{n}\226\137\161 g x).
Time Definition discrete_fun_ofe_mixin : OfeMixin (discrete_fun B).
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
Time
Canonical Structure discrete_funO :=
  OfeT (discrete_fun B) discrete_fun_ofe_mixin.
Time #[program]
Definition discrete_fun_chain `(c : chain discrete_funO) 
  (x : A) : chain (B x) := {| chain_car := fun n => c n x |}.
Time Next Obligation.
Time (intros c x n i ?).
Time by apply (chain_cauchy c).
Time Qed.
Time #[global, program]
Instance discrete_fun_cofe  `{\226\136\128 x, Cofe (B x)}: (Cofe discrete_funO) := {
 compl :=fun c x => compl (discrete_fun_chain c x)}.
Time Next Obligation.
Time (intros ? n c x).
Time (apply (conv_compl n (discrete_fun_chain c x))).
Time Qed.
Time #[global]
Instance discrete_fun_inhabited  `{\226\136\128 x, Inhabited (B x)}:
 (Inhabited discrete_funO) := (populate (\206\187 _, inhabitant)).
Time #[global]
Instance discrete_fun_lookup_discrete  `{EqDecision A} 
 f x: (Discrete f \226\134\146 Discrete (f x)).
Time Proof.
Time (intros Hf y ?).
Time
(set
  (g :=
   fun x' =>
   match decide (x = x') with
   | left H => eq_rect _ B y _ H
   | _ => f x'
   end)).
Time trans g x.
Time {
Time (<ssreflect_plugin::ssrtclintros@0> apply Hf =>x').
Time (unfold g).
Time by destruct (decide _) as [[]| ].
Time }
Time (unfold g).
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide _) as [Hx| ] ; last  done).
Time by rewrite (proof_irrel Hx eq_refl).
Time Qed.
Time End discrete_fun.
Time Arguments discrete_funO {_} _.
Time
Notation "A -d> B" := (@discrete_funO A (\206\187 _, B))
  (at level 99, B  at level 200, right associativity).
Time
Definition discrete_fun_map {A} {B1 B2 : A \226\134\146 ofeT} 
  (f : \226\136\128 x, B1 x \226\134\146 B2 x) (g : discrete_fun B1) : discrete_fun B2 :=
  \206\187 x, f _ (g x).
Time
Lemma discrete_fun_map_ext {A} {B1 B2 : A \226\134\146 ofeT} 
  (f1 f2 : \226\136\128 x, B1 x \226\134\146 B2 x) (g : discrete_fun B1) :
  (\226\136\128 x, f1 x (g x) \226\137\161 f2 x (g x))
  \226\134\146 discrete_fun_map f1 g \226\137\161 discrete_fun_map f2 g.
Time Proof.
Time done.
Time Qed.
Time
Lemma discrete_fun_map_id {A} {B : A \226\134\146 ofeT} (g : discrete_fun B) :
  discrete_fun_map (\206\187 _, id) g = g.
Time Proof.
Time done.
Time Qed.
Time
Lemma discrete_fun_map_compose {A} {B1 B2 B3 : A \226\134\146 ofeT}
  (f1 : \226\136\128 x, B1 x \226\134\146 B2 x) (f2 : \226\136\128 x, B2 x \226\134\146 B3 x) 
  (g : discrete_fun B1) :
  discrete_fun_map (\206\187 x, f2 x \226\136\152 f1 x) g =
  discrete_fun_map f2 (discrete_fun_map f1 g).
Time Proof.
Time done.
Time Qed.
Time
Instance discrete_fun_map_ne  {A} {B1 B2 : A \226\134\146 ofeT} 
 (f : \226\136\128 x, B1 x \226\134\146 B2 x) n:
 ((\226\136\128 x, Proper (dist n ==> dist n) (f x))
  \226\134\146 Proper (dist n ==> dist n) (discrete_fun_map f)).
Time Proof.
Time by intros ? y1 y2 Hy x; rewrite /discrete_fun_map (Hy x).
Time Qed.
Time
Definition discrete_funO_map {A} {B1 B2 : A \226\134\146 ofeT}
  (f : discrete_fun (\206\187 x, B1 x -n> B2 x)) :
  discrete_funO B1 -n> discrete_funO B2 := OfeMor (discrete_fun_map f).
Time
Instance discrete_funO_map_ne  {A} {B1 B2 : A \226\134\146 ofeT}:
 (NonExpansive (@discrete_funO_map A B1 B2)).
Time Proof.
Time (intros n f1 f2 Hf g x; apply Hf).
Time Qed.
Time #[program]
Definition discrete_funOF {C} (F : C \226\134\146 oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A _ B _ => discrete_funO (\206\187 c, oFunctor_car (F c) A B);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  discrete_funO_map (\206\187 c, oFunctor_map (F c) fg) |}.
Time Next Obligation.
Time (intros C F A1 ? A2 ? B1 ? B2 ? n ? ? g).
Time
by
 <ssreflect_plugin::ssrtclintros@0> apply discrete_funO_map_ne =>?;
  apply oFunctor_ne.
Time Qed.
Time Next Obligation.
Time (intros C F A ? B ? g; simpl).
Time rewrite -{+2}(discrete_fun_map_id g).
Time
(<ssreflect_plugin::ssrtclintros@0> apply discrete_fun_map_ext =>y;
  apply oFunctor_id).
Time Qed.
Time Next Obligation.
Time (intros C F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f1 f2 f1' f2' g).
Time rewrite /= -discrete_fun_map_compose.
Time
(<ssreflect_plugin::ssrtclintros@0> apply discrete_fun_map_ext =>y;
  apply oFunctor_compose).
Time Qed.
Time
Notation "T -d> F" := (@discrete_funOF T%type (\206\187 _, F%OF)) : oFunctor_scope.
Time
Instance discrete_funOF_contractive  {C} (F : C \226\134\146 oFunctor):
 ((\226\136\128 c, oFunctorContractive (F c)) \226\134\146 oFunctorContractive (discrete_funOF F)).
Time Proof.
Time (intros ? A1 ? A2 ? B1 ? B2 ? n ? ? g).
Time
by
 <ssreflect_plugin::ssrtclintros@0> apply discrete_funO_map_ne =>c;
  apply oFunctor_contractive.
Time Qed.
Time
Lemma iso_ofe_mixin {A : ofeT} `{Equiv B} `{Dist B} 
  (g : B \226\134\146 A) (g_equiv : \226\136\128 y1 y2, y1 \226\137\161 y2 \226\134\148 g y1 \226\137\161 g y2)
  (g_dist : \226\136\128 n y1 y2, y1 \226\137\161{n}\226\137\161 y2 \226\134\148 g y1 \226\137\161{n}\226\137\161 g y2) : 
  OfeMixin B.
Time Proof.
Time split.
Time -
Time (intros y1 y2).
Time rewrite g_equiv.
Time setoid_rewrite g_dist.
Time (apply equiv_dist).
Time -
Time split.
Time +
Time (intros y).
Time by apply g_dist.
Time +
Time (intros y1 y2).
Time by rewrite !g_dist.
Time +
Time (intros y1 y2 y3).
Time rewrite !g_dist.
Time (intros ? ?; etrans; eauto).
Time -
Time (intros n y1 y2).
Time rewrite !g_dist.
Time (apply dist_S).
Time Qed.
Time Section iso_cofe_subtype.
Time
Context {A B : ofeT} `{Cofe A} (P : A \226\134\146 Prop) (f : \226\136\128 x, P x \226\134\146 B) (g : B \226\134\146 A).
Time Context (g_dist : \226\136\128 n y1 y2, y1 \226\137\161{n}\226\137\161 y2 \226\134\148 g y1 \226\137\161{n}\226\137\161 g y2).
Time Let Hgne : NonExpansive g.
Time Proof.
Time (intros n y1 y2).
Time (apply g_dist).
Time Qed.
Time Existing Instance Hgne.
Time Context (gf : \226\136\128 x Hx, g (f x Hx) \226\137\161 x).
Time Context (Hlimit : \226\136\128 c : chain B, P (compl (chain_map g c))).
Time #[program]
Definition iso_cofe_subtype : Cofe B :=
  {| compl := fun c => f (compl (chain_map g c)) _ |}.
Time Next Obligation.
Time (apply Hlimit).
Time Qed.
Time Next Obligation.
Time (intros n c; simpl).
Time (apply g_dist).
Time by rewrite gf conv_compl.
Time Qed.
Time End iso_cofe_subtype.
Time
Lemma iso_cofe_subtype' {A B : ofeT} `{Cofe A} (P : A \226\134\146 Prop)
  (f : \226\136\128 x, P x \226\134\146 B) (g : B \226\134\146 A) (Pg : \226\136\128 y, P (g y))
  (g_dist : \226\136\128 n y1 y2, y1 \226\137\161{n}\226\137\161 y2 \226\134\148 g y1 \226\137\161{n}\226\137\161 g y2)
  (gf : \226\136\128 x Hx, g (f x Hx) \226\137\161 x) (Hlimit : LimitPreserving P) : 
  Cofe B.
Time Proof.
Time apply : {}(iso_cofe_subtype P f g) {} =>// c.
Time (<ssreflect_plugin::ssrtclintros@0> apply Hlimit =>?; apply Pg).
Time Qed.
Time
Definition iso_cofe {A B : ofeT} `{Cofe A} (f : A \226\134\146 B) 
  (g : B \226\134\146 A) (g_dist : \226\136\128 n y1 y2, y1 \226\137\161{n}\226\137\161 y2 \226\134\148 g y1 \226\137\161{n}\226\137\161 g y2)
  (gf : \226\136\128 x, g (f x) \226\137\161 x) : Cofe B.
Time Proof.
Time by apply (iso_cofe_subtype (\206\187 _, True) (\206\187 x _, f x) g).
Time Qed.
Time Section sigma.
Time Context {A : ofeT} {P : A \226\134\146 Prop}.
Time Implicit Type x : sig P.
Time Instance sig_equiv : (Equiv (sig P)) := (\206\187 x1 x2, `x1 \226\137\161 `x2).
Time Instance sig_dist : (Dist (sig P)) := (\206\187 n x1 x2, `x1 \226\137\161{n}\226\137\161 `x2).
Time Definition sig_equiv_alt x y : x \226\137\161 y \226\134\148 `x \226\137\161 `y := reflexivity _.
Time
Definition sig_dist_alt n x y : x \226\137\161{n}\226\137\161 y \226\134\148 `x \226\137\161{n}\226\137\161 `y := reflexivity _.
Time
Lemma exist_ne n a1 a2 (H1 : P a1) (H2 : P a2) :
  a1 \226\137\161{n}\226\137\161 a2 \226\134\146 a1 \226\134\190 H1 \226\137\161{n}\226\137\161 a2 \226\134\190 H2.
Time Proof.
Time done.
Time Qed.
Time #[global]Instance proj1_sig_ne : (NonExpansive (@proj1_sig _ P)).
Time Proof.
Time by intros n [a Ha] [b Hb] ?.
Time Qed.
Time Definition sig_ofe_mixin : OfeMixin (sig P).
Time Proof.
Time by apply (iso_ofe_mixin proj1_sig).
Time Qed.
Time Canonical Structure sigO : ofeT := OfeT (sig P) sig_ofe_mixin.
Time #[global]
Instance sig_cofe  `{Cofe A} `{!LimitPreserving P}: (Cofe sigO).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply (iso_cofe_subtype' P (exist P) proj1_sig) =>//).
Time by intros [].
Time Qed.
Time #[global]
Instance sig_discrete  (x : sig P): (Discrete (`x) \226\134\146 Discrete x).
Time Proof.
Time (intros ? y).
Time rewrite sig_dist_alt sig_equiv_alt.
Time (apply (discrete _)).
Time Qed.
Time #[global]Instance sig_ofe_discrete : (OfeDiscrete A \226\134\146 OfeDiscrete sigO).
Time Proof.
Time (intros ? ?).
Time (apply _).
Time Qed.
Time End sigma.
Time Arguments sigO {_} _.
Time Section sigT.
Time Import EqNotations.
Time Context {A : Type} {P : A \226\134\146 ofeT}.
Time Implicit Type x : sigT P.
Time
Instance sigT_dist : (Dist (sigT P)) :=
 (\206\187 n x1 x2,
    \226\136\131 Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 \226\137\161{n}\226\137\161 projT2 x2).
Time Instance sigT_equiv : (Equiv (sigT P)) := (\206\187 x1 x2, \226\136\128 n, x1 \226\137\161{n}\226\137\161 x2).
Time
Definition sigT_equiv_eq x1 x2 : x1 \226\137\161 x2 \226\134\148 (\226\136\128 n, x1 \226\137\161{n}\226\137\161 x2) :=
  reflexivity _.
Time
Definition sigT_dist_eq x1 x2 n :
  x1 \226\137\161{n}\226\137\161 x2
  \226\134\148 (\226\136\131 Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 \226\137\161{n}\226\137\161 projT2 x2) :=
  reflexivity _.
Time
Definition sigT_dist_proj1 n {x} {y} : x \226\137\161{n}\226\137\161 y \226\134\146 projT1 x = projT1 y :=
  proj1_ex.
Time
Definition sigT_equiv_proj1 {x} {y} : x \226\137\161 y \226\134\146 projT1 x = projT1 y :=
  \206\187 H, proj1_ex (H 0).
Time Definition sigT_ofe_mixin : OfeMixin (sigT P).
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> split =>// n).
Time -
Time (split; hnf; setoid_rewrite sigT_dist_eq).
Time +
Time (intros).
Time by exists eq_refl.
Time +
Time move  {}=>[xa x] [ya y] /=.
Time (destruct 1 as [-> Heq]).
Time by exists eq_refl.
Time +
Time move  {}=>[xa x] [ya y] [za z] /=.
Time (destruct 1 as [-> Heq1]).
Time (destruct 1 as [-> Heq2]).
Time (<ssreflect_plugin::ssrtclintros@0> exists eq_refl =>/=).
Time by trans y.
Time -
Time setoid_rewrite sigT_dist_eq.
Time move  {}=>[xa x] [ya y] /=.
Time (destruct 1 as [-> Heq]).
Time exists eq_refl.
Time exact : {}dist_S {}.
Time Qed.
Time Canonical Structure sigTO : ofeT := OfeT (sigT P) sigT_ofe_mixin.
Time
Lemma sigT_equiv_eq_alt `{!\226\136\128 a b : A, ProofIrrel (a = b)} 
  x1 x2 :
  x1 \226\137\161 x2 \226\134\148 (\226\136\131 Heq : projT1 x1 = projT1 x2, rew Heq in projT2 x1 \226\137\161 projT2 x2).
Time Proof.
Time
(setoid_rewrite equiv_dist; setoid_rewrite sigT_dist_eq;
  <ssreflect_plugin::ssrtclintros@0> split =>Heq).
Time -
Time move : {}(Heq 0) {} =>[H0eq1 _].
Time (<ssreflect_plugin::ssrtclintros@0> exists H0eq1 =>n).
Time move : {}(Heq n) {} =>[] Hneq1.
Time by rewrite (proof_irrel H0eq1 Hneq1).
Time -
Time move : {}Heq {} =>[Heq1 Heqn2] n.
Time by exists Heq1.
Time Qed.
Time #[global]
Instance projT1_ne : (NonExpansive (projT1 : sigTO \226\134\146 leibnizO A)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance projT1_proper : (Proper ((\226\137\161) ==> (\226\137\161)) (projT1 : sigTO \226\134\146 leibnizO A)).
Time Proof.
Time (apply ne_proper, projT1_ne).
Time Qed.
Time
Lemma projT2_ne n (x1 x2 : sigTO) (Heq : x1 \226\137\161{n}\226\137\161 x2) :
  rew sigT_dist_proj1 n Heq in projT2 x1 \226\137\161{n}\226\137\161 projT2 x2.
Time Proof.
Time by destruct Heq.
Time Qed.
Time
Lemma projT2_proper `{!\226\136\128 a b : A, ProofIrrel (a = b)} 
  (x1 x2 : sigTO) (Heqs : x1 \226\137\161 x2) :
  rew sigT_equiv_proj1 Heqs in projT2 x1 \226\137\161 projT2 x2.
Time Proof.
Time move : {}x1 {}x2 {}Heqs {} =>[a1 x1] [a2 x2] Heqs.
Time case : {}(proj1 (sigT_equiv_eq_alt _ _) Heqs) {} =>/=.
Time (intros ->).
Time rewrite (proof_irrel (sigT_equiv_proj1 Heqs) eq_refl) /=.
Time done.
Time Qed.
Time
Lemma existT_ne n {i1} {i2} {v1 : P i1} {v2 : P i2} :
  \226\136\128 Heq : i1 = i2,
    rew f_equal P Heq in v1 \226\137\161{n}\226\137\161 v2 \226\134\146 existT i1 v1 \226\137\161{n}\226\137\161 existT i2 v2.
Time Proof.
Time (intros ->; simpl).
Time (<ssreflect_plugin::ssrtclintros@0> exists eq_refl =>/=).
Time done.
Time Qed.
Time
Lemma existT_proper {i1} {i2} {v1 : P i1} {v2 : P i2} :
  \226\136\128 Heq : i1 = i2, rew f_equal P Heq in v1 \226\137\161 v2 \226\134\146 existT i1 v1 \226\137\161 existT i2 v2.
Time Proof.
Time (intros Heq Heqv n).
Time (apply (existT_ne n Heq), equiv_dist, Heqv).
Time Qed.
Time #[global]Instance existT_ne_2  a: (NonExpansive (@existT A P a)).
Time Proof.
Time move  {}=>? ? ? Heq.
Time (apply (existT_ne _ eq_refl Heq)).
Time Qed.
Time #[global]
Instance existT_proper_2  a: (Proper ((\226\137\161) ==> (\226\137\161)) (@existT A P a)).
Time Proof.
Time (apply ne_proper, _).
Time Qed.
Time Implicit Type c : chain sigTO.
Time #[global]Instance sigT_discrete  x: (Discrete (projT2 x) \226\134\146 Discrete x).
Time Proof.
Time
(move : {}x {} =>[xa x] ? [ya y] [] /=; <ssreflect_plugin::ssrtclintros@0>
  intros -> =>/= Hxy n).
Time (<ssreflect_plugin::ssrtclintros@0> exists eq_refl =>/=).
Time (apply equiv_dist, (discrete _), Hxy).
Time Qed.
Time #[global]
Instance sigT_ofe_discrete : ((\226\136\128 a, OfeDiscrete (P a)) \226\134\146 OfeDiscrete sigTO).
Time Proof.
Time (intros ? ?).
Time (apply _).
Time Qed.
Time Lemma sigT_chain_const_proj1 c n : projT1 (c n) = projT1 (c 0).
Time Proof.
Time refine (sigT_dist_proj1 _ (chain_cauchy c 0 n _)).
Time lia.
Time Qed.
Time Section cofe.
Time Context `{!\226\136\128 a b : A, ProofIrrel (a = b)} `{!\226\136\128 a, Cofe (P a)}.
Time #[program]
Definition chain_map_snd c : chain (P (projT1 (c 0))) :=
  {| chain_car := fun n => rew sigT_chain_const_proj1 c n in projT2 (c n) |}.
Time Next Obligation.
Time move  {}=>c n i Hle /=.
Time case : {}(chain_cauchy c n i Hle) {} =>[Heqin Hgoal] /=.
Time
move : {}(sigT_chain_const_proj1 c i) {}(sigT_chain_const_proj1 c n) {}
 =>Heqi0 Heqn0.
Time (destruct Heqn0).
Time by rewrite /= (proof_irrel Heqi0 Heqin).
Time Qed.
Time
Definition sigT_compl : Compl sigTO :=
  \206\187 c, existT (projT1 (chain_car c 0)) (compl (chain_map_snd c)).
Time #[global, program]
Instance sigT_cofe : (Cofe sigTO) := { compl :=sigT_compl}.
Time Next Obligation.
Time (intros n c).
Time rewrite /sigT_compl sigT_dist_eq /=.
Time exists (symmetry (sigT_chain_const_proj1 c n)).
Time (pose proof (conv_compl n (chain_map_snd c)) as Hgoal).
Time move : {}(compl (chain_map_snd c)) {}Hgoal {} =>pc0 /=.
Time (destruct (sigT_chain_const_proj1 c n); simpl).
Time done.
Time Qed.
Time End cofe.
Time End sigT.
Time Arguments sigTO {_} _.
Time Section sigTOF.
Time Context {A : Type}.
Time #[program]
Definition sigT_map {P1 P2 : A \226\134\146 ofeT} :
  discrete_funO (\206\187 a, P1 a -n> P2 a) -n> sigTO P1 -n> sigTO P2 :=
  \206\187ne f xpx, existT _ (f _ (projT2 xpx)).
Time Next Obligation.
Time move  {}=>? ? f n [x px] [y py] [/= Heq].
Time (destruct Heq; simpl).
Time (<ssreflect_plugin::ssrtclintros@0> exists eq_refl =>/=).
Time by f_equiv.
Time Qed.
Time Next Obligation.
Time move  {}=>? ? n f g Heq [x px] /=.
Time (<ssreflect_plugin::ssrtclintros@0> exists eq_refl =>/=).
Time (apply Heq).
Time Qed.
Time #[program]
Definition sigTOF (F : A \226\134\146 oFunctor) : oFunctor :=
  {|
  oFunctor_car := fun A CA B CB => sigTO (\206\187 a, oFunctor_car (F a) A _ B CB);
  oFunctor_map := fun A1 _ A2 _ B1 _ B2 _ fg =>
                  sigT_map (\206\187 a, oFunctor_map (F a) fg) |}.
Time Next Obligation.
Time (repeat intro).
Time (<ssreflect_plugin::ssrtclintros@0> exists eq_refl =>/=).
Time solve_proper.
Time Qed.
Time Next Obligation.
Time (simpl; intros).
Time (apply (existT_proper eq_refl), oFunctor_id).
Time Qed.
Time Next Obligation.
Time (simpl; intros).
Time (apply (existT_proper eq_refl), oFunctor_compose).
Time Qed.
Time #[global]
Instance sigTOF_contractive  {F}:
 ((\226\136\128 a, oFunctorContractive (F a)) \226\134\146 oFunctorContractive (sigTOF F)).
Time Proof.
Time (repeat intro).
Time (<ssreflect_plugin::ssrtclintros@0> apply sigT_map =>a).
Time exact : {}oFunctor_contractive {}.
Time Qed.
Time End sigTOF.
Time Arguments sigTOF {_} _%OF.
