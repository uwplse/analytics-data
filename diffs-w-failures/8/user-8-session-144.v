Require Import Monad.
Require Import PermutSetoid.
Require Import Sorting.Permutation.
Require Import Sorting.PermutEq.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Notation "\226\138\165" := zero : monoid_scope.
Notation "\226\138\164" := one : monoid_scope.
Notation "a \226\136\152 b" := (m a b) (left associativity, at level 40) : monoid_scope.
Open Scope monoid_scope.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Hint Resolve M_unit M_assoc M_comm M_absorb.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Notation "\226\159\168 b \226\159\169" := (translate b) : monoid_scope.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Instance PPCM_to_PCM  A `{PPCM A}: (PCM (option A)) := { 
 one :=Some one'; zero :=None; m :=fun a b => do x \226\134\144 a; do y \226\134\144 b; m' x y}.
Instance PPCM_to_PCM_Laws  A `{PPCM_Laws A}: (PCM_Laws (option A)).
Proof.
split.
-
(destruct a; simpl; auto).
(apply PMonoid_unit).
-
(destruct a as [a| ], b as [b| ], c as [c| ]; simpl; auto).
*
(apply PMonoid_assoc).
*
(destruct (m' a b); auto).
-
(destruct a as [a| ], b as [b| ]; simpl; auto).
(apply PMonoid_comm).
-
(destruct a; simpl; auto).
Qed.
Require Import List.
Require Import Multiset.
Require Import Arith.
Section CMonoid.
Variable (A : Type).
Variable (PCM_A : `{PCM A}).
Variable (PCM_Laws_A : `{PCM_Laws A}).
Lemma M_unit_l : forall a, \226\138\164 \226\136\152 a = a.
Proof.
(intros).
(rewrite M_comm).
auto.
Defined.
Hint Resolve M_unit_l.
Lemma M_comm_assoc : forall a b c, a \226\136\152 b \226\136\152 c = b \226\136\152 a \226\136\152 c.
Proof.
(intros).
(rewrite (M_comm a b)).
reflexivity.
Defined.
Lemma M_comm_assoc_r : forall a b c, a \226\136\152 (b \226\136\152 c) = b \226\136\152 (a \226\136\152 c).
Proof.
(intros).
(rewrite M_assoc).
(rewrite (M_comm a b)).
(rewrite <- M_assoc).
reflexivity.
Defined.
Lemma M_absorb_l : forall a, \226\138\165 \226\136\152 a = \226\138\165.
Proof.
(intros).
(rewrite M_comm).
auto.
Defined.
Hint Resolve M_absorb_l.
Open Scope list_scope.
Global Instance TranslateA : (Translate A A) := { translate :=fun x => x}.
Definition translate_option {X} `{Translate X A} (x : option X) : A :=
  match x with
  | Some x' => \226\159\168 x' \226\159\169
  | None => \226\138\165
  end.
Global
Instance Translate_option  (X : Type) `{Translate X A}:
 (Translate (option X) A) := { translate :=translate_option}.
Lemma translate_Some :
  forall {X} `{Translate X A} (x : A), \226\159\168 Some x \226\159\169 = \226\159\168 x \226\159\169.
Proof.
auto.
Defined.
Fixpoint translate_list {X} `{Translate X A} (ls : list X) : A :=
  match ls with
  | nil => \226\138\164
  | b :: ls' => \226\159\168 b \226\159\169 \226\136\152 translate_list ls'
  end.
Global
Instance Translate_list  (X : Type) `{Translate X A}: 
 (Translate (list X) A) := { translate :=translate_list}.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Fixpoint translate_M_exp (e : M_exp) : A :=
  match e with
  | M_zero => \226\138\165
  | M_one => \226\138\164
  | M_var a => a
  | M_m e1 e2 => translate_M_exp e1 \226\136\152 translate_M_exp e2
  end.
Global
Instance Translate_M_exp : (Translate M_exp A) := {
 translate :=translate_M_exp}.
Fixpoint flatten (e : M_exp) : option (list A) :=
  match e with
  | M_zero => None
  | M_one => Some nil
  | M_var a => Some (a :: nil)
  | M_m e1 e2 =>
      do ls1 \226\134\144 flatten e1; do ls2 \226\134\144 flatten e2; return_ (ls1 ++ ls2)
  end.
Lemma flatten_correct' :
  forall ls1 ls2 : list A, \226\159\168 ls1 \226\159\169 \226\136\152 \226\159\168 ls2 \226\159\169 = \226\159\168 ls1 ++ ls2 \226\159\169.
Proof.
(induction ls1; intros; auto).
(simpl).
(rewrite <- M_assoc).
(unfold translate_list in *; simpl in *).
(rewrite IHls1).
reflexivity.
Defined.
Lemma option_list_correct :
  forall o1 o2 : option (list A),
  \226\159\168 o1 \226\159\169 \226\136\152 \226\159\168 o2 \226\159\169 = \226\159\168 do ls1 \226\134\144 o1; do ls2 \226\134\144 o2; return_ (ls1 ++ ls2) \226\159\169.
Proof.
(destruct o1; destruct o2; simpl; auto).
(apply flatten_correct').
Defined.
Lemma flatten_correct : forall e, \226\159\168 e \226\159\169 = \226\159\168 flatten e \226\159\169.
Proof.
(intros).
(unfold translate; simpl).
(induction e; simpl; try rewrite M_unit; auto).
(rewrite IHe1, IHe2).
(apply option_list_correct).
Defined.
Fixpoint index (xs : list A) (i : nat) : A :=
  match xs, i with
  | nil, _ => \226\138\165
  | x :: _, 0 => x
  | _ :: xs, S x => index xs x
  end.
Fixpoint index_wrt (values : list A) (indices : list nat) : 
list A :=
  match indices with
  | nil => nil
  | i :: indices' => index values i :: index_wrt values indices'
  end.
Instance Translate_nat_list : (Translate (list A * list nat) A) := {
 translate :=fun x =>
             match x with
             | (values, idx) => \226\159\168 index_wrt values idx \226\159\169
             end}.
Fixpoint nats_lt n : list nat :=
  match n with
  | O => nil
  | S n' => O :: fmap S (nats_lt n')
  end.
Lemma index_wrt_cons :
  forall idx a values,
  index_wrt (a :: values) (fmap S idx) = index_wrt values idx.
Proof.
(induction idx as [| n]; intros a values; simpl; auto).
(rewrite IHidx; auto).
Defined.
Lemma index_wrt_default :
  forall ls : list A, index_wrt ls (nats_lt (length ls)) = ls.
Proof.
(induction ls; simpl; auto).
(rewrite index_wrt_cons).
(rewrite IHls).
reflexivity.
Defined.
Lemma split_list :
  forall values ls1 ls2,
  \226\159\168 index_wrt values (ls1 ++ ls2) \226\159\169 =
  \226\159\168 index_wrt values ls1 \226\159\169 \226\136\152 \226\159\168 index_wrt values ls2 \226\159\169.
Proof.
(induction ls1; simpl; intros; auto).
(simpl in *).
(rewrite IHls1).
auto.
Qed.
Search -(?a = ?b -> ?c = ?d -> ?f ?a ?c = ?f ?b ?d).
Lemma in_index :
  forall i a values, \226\159\168 index values i \226\159\169 = a -> a = \226\138\165 \/ In a values.
Proof.
(induction i; destruct values; intros; auto).
-
(simpl in H).
right.
left.
auto.
-
(simpl in H).
(destruct (IHi _ _ H); auto).
right.
right.
auto.
Defined.
Lemma in_index_wrt :
  forall a idx values, In a (index_wrt values idx) -> a = \226\138\165 \/ In a values.
Proof.
(induction idx as [| i]; intros values pf_in; simpl in *).
-
contradiction.
-
(destruct pf_in as [pf_in| pf_in]).
*
(apply (in_index i); auto).
*
(apply IHidx; auto).
Defined.
Lemma interp_permutation :
  forall (values : list A) (idx1 idx2 : list nat),
  Permutation idx1 idx2 ->
  \226\159\168 index_wrt values idx1 \226\159\169 = \226\159\168 index_wrt values idx2 \226\159\169.
Proof.
(intros values idx1 idx2 pf).
(induction pf; simpl in *; auto).
-
(rewrite IHpf; auto).
-
(rewrite M_comm_assoc_r).
reflexivity.
-
(rewrite IHpf1, IHpf2).
reflexivity.
Defined.
Lemma permutation_reflection :
  forall ls1 ls2,
  @permutation nat _ PeanoNat.Nat.eq_dec ls1 ls2 -> Permutation ls1 ls2.
Proof.
(intros).
(apply (permutation_Permutation PeanoNat.Nat.eq_dec); auto).
Defined.
Notation contents := (list_contents eq Nat.eq_dec).
Lemma meq_multiplicity :
  forall ls1 ls2 : list nat,
  (forall x,
   In x ls1 \/ In x ls2 ->
   multiplicity (contents ls1) x = multiplicity (contents ls2) x) ->
  meq (contents ls1) (contents ls2).
Proof.
(intros ls1 ls2 H x).
(destruct (in_dec Nat.eq_dec x ls1); [ apply H; auto |  ]).
(destruct (in_dec Nat.eq_dec x ls2); [ apply H; auto |  ]).
(repeat rewrite multiplicity_In_O; auto).
Defined.
Fixpoint find_duplicate (ls : list nat) : option nat :=
  match ls with
  | nil => None
  | n :: ls' =>
      if in_dec Nat.eq_dec n ls' then Some n else find_duplicate ls'
  end.
Lemma interp_0 : forall ls : list A, In \226\138\165 ls -> \226\159\168 ls \226\159\169 = \226\138\165.
Proof.
(induction ls; intros pf_in; simpl in *).
-
contradiction.
-
(destruct pf_in as [eq| pf_in]).
*
(rewrite eq).
auto.
*
(rewrite IHls; auto).
Defined.
End CMonoid.
Arguments index_wrt {A} {PCM_A}.
Arguments interp_permutation {A} {PCM_A} {PCM_Laws_A}.
Ltac print_goal := match goal with
                   | |- ?G => idtac G
                   end.
Ltac type_of_goal := match goal with
                     | |- ?a = _ => type of a
                     end.
Ltac
 has_evars term :=
  match term with
  | ?L = ?R => has_evar L; has_evar R
  | ?L = ?R => has_evars L
  | ?L = ?R => has_evars R
  | ?\206\1471 \226\136\152 ?\206\1472 => has_evar \206\1471; has_evar \206\1472
  | ?\206\1471 \226\136\152 ?\206\1472 => has_evars \206\1471
  | ?\206\1471 \226\136\152 ?\206\1472 => has_evars \206\1472
  end.
Ltac
 simpl_arg e :=
  let e' := fresh "e" in
  set (e' := e); simpl in e'; unfold e'; clear e'.
Ltac
 destruct_finite_In :=
  repeat
   match goal with
   | H:In _ _ \/ In _ _ |- _ => destruct H
   | H:In _ nil |- _ => apply (False_rect _ H)
   | H:In ?a (_ :: _) |- _ => destruct H; try (subst; reflexivity)
   end.
Ltac
 append ls1 ls2 :=
  match ls1 with
  | ?x :: ?l => let l' := append l ls2 in
                x :: l'
  | nil => ls2
  end.
Ltac
 lookup x xs :=
  match xs with
  | x :: _ => O
  | ?y :: ?xs' => let n := lookup x xs' in
                  S n
  end.
Ltac
 difference ls1 ls2 :=
  match ls1 with
  | nil => ls1
  | ?x :: ?ls1' => let i := lookup x ls2 in
                   difference ls1' ls2
  | ?x :: ?ls1' => let l := difference ls1' ls2 in
                   x :: l
  end.
Ltac
 find_duplicate ls :=
  match ls with
  | ?n :: ?ls' => let z := lookup n ls' in
                  n
  | _ :: ?ls' => find_duplicate ls'
  end.
Ltac
 repos_evar :=
  repeat
   match goal with
   | |- ?G => has_evars G; fail 1
   | |- ?a = ?b => has_evar b; symmetry
   | |- context [ ?a \226\136\152 ?b ] => has_evar a; rewrite (M_comm a b)
   end;
   repeat
    match goal with
    | |- ?a \226\136\152 (?b \226\136\152 ?c) = _ => rewrite (M_assoc a b c)
    end.
Ltac
 simpl_args :=
  match goal with
  | |- \226\159\168 ?e1 \226\159\169 \226\136\152 ?ev = \226\159\168 ?e2 \226\159\169 => simpl_arg e1; simpl_arg e2
  | |- \226\159\168 ?e1 \226\159\169 = \226\159\168 ?e2 \226\159\169 => simpl_arg e1; simpl_arg e2
  end.
Ltac
 reify A a :=
  match a with
  | \226\138\165 => @M_zero A
  | \226\138\164 => @M_one A
  | ?a1 \226\136\152 ?a2 =>
      let e1 := reify A a1 in
      let e2 := reify A a2 in
      @M_m A e1 e2
  | _ => @M_var A a
  end.
Ltac
 prep_reification :=
  let A := type_of_goal in
  match goal with
  | |- ?a1 \226\136\152 ?ev = ?a2 =>
        is_evar ev;
         (let e1 := reify A a1 in
          let e2 := reify A a2 in
          change ((\226\159\168 e1 \226\159\169 : A) \226\136\152 ev = (\226\159\168 e2 \226\159\169 : A));
           repeat rewrite flatten_correct; auto; simpl_args)
  | |- ?a1 = ?a2 =>
        let e1 := reify A a1 in
        let e2 := reify A a2 in
        change ((\226\159\168 e1 \226\159\169 : A) = (\226\159\168 e2 \226\159\169 : A)); repeat rewrite flatten_correct;
         auto; simpl_args
  end.
Ltac
 reify_wrt values ls :=
  match ls with
  | nil => @nil nat
  | ?a :: ?ls' =>
      let i := lookup a values in
      let idx := reify_wrt values ls' in
      i :: idx
  | _ :: ?ls' => reify_wrt values ls'
  end.
Ltac
 split_reify_wrt values1 values2 ls :=
  let idx1 := reify_wrt values1 ls in
  let idx2 := reify_wrt values2 ls in
  (idx1, idx2).
Ltac
 solve_permutation :=
  apply interp_permutation; apply permutation_reflection;
   apply meq_multiplicity; intros; destruct_finite_In; 
   fail.
Ltac
 strip_Some :=
  let A := type_of_goal in
  repeat
   match goal with
   | |- context [ \226\159\168 Some ?a \226\159\169 ] => replace \226\159\168 Some a \226\159\169 with \226\159\168 a \226\159\169 : A by auto
   end.
Ltac knot_reification tac := strip_Some; tac; solve_permutation.
Ltac
 reification_wrt :=
  let A := type_of_goal in
  match goal with
  | |- ?a = ?a => reflexivity
  | |- \226\159\168 ?ls1 \226\159\169 = \226\159\168 ?ls2 \226\159\169 =>
        let src := append ls1 ls2 in
        let idx1 := reify_wrt src ls1 in
        let idx2 := reify_wrt src ls2 in
        let ls1' := constr:(index_wrt src idx1) in
        let ls2' := constr:(index_wrt src idx2) in
        change ((\226\159\168 ls1' \226\159\169 : A) = (\226\159\168 ls2' \226\159\169 : A))
  | |- \226\159\168 ?ls1 \226\159\169 \226\136\152 ?ev = \226\159\168 ?ls2 \226\159\169 =>
        let src := append ls1 ls2 in
        let ls2_1 := difference ls2 ls1 in
        let idx1 := reify_wrt src ls1 in
        let idx2_1 := reify_wrt src ls2_1 in
        let idx2' := constr:(index_wrt src (idx1 ++ idx2_1)) in
        replace \226\159\168 ls2 \226\159\169 with \226\159\168 idx2' \226\159\169 : A
         by (simpl_args; strip_Some; reification_wrt; solve_permutation);
         repeat rewrite split_list;
         try (apply f_equal2; [  | simpl; reflexivity ]); auto
  end.
Ltac
 monoid :=
  try reflexivity; repos_evar; prep_reification; strip_Some; reification_wrt;
   solve_permutation.
Section Examples.
Variable (A : Type).
Variable (PCM_A : `{PCM A}).
Variable (PCM_A_Laws : `{PCM_Laws A}).
Example PCM_comm' : forall a b : A, a \226\136\152 b = b \226\136\152 a.
Proof.
(intros).
monoid.
Defined.
Example PCM_unit' : forall a, \226\138\164 \226\136\152 a = a.
Proof.
(intros).
monoid.
Defined.
Example PCM_absorb' : forall a, \226\138\165 \226\136\152 a = \226\138\165.
Proof.
(intros).
monoid.
Defined.
Example PCM_aba : forall a b, a \226\136\152 b \226\136\152 a = a \226\136\152 a \226\136\152 b.
Proof.
(intros).
monoid.
Qed.
Example PCM_abc : forall a b c, a \226\136\152 b \226\136\152 c = c \226\136\152 a \226\136\152 \226\138\164 \226\136\152 b.
Proof.
(intros).
monoid.
Defined.
Example PCM_evar : forall a b c, exists d, a \226\136\152 b \226\136\152 c = c \226\136\152 d \226\136\152 a \226\136\152 \226\138\164.
Proof.
(intros).
eexists.
monoid.
Qed.
Example PCM_evar2 :
  forall a b c d e, exists x, a \226\136\152 x \226\136\152 c = b \226\136\152 c \226\136\152 d \226\136\152 \226\138\164 \226\136\152 e \226\136\152 a.
Proof.
(intros).
eexists.
monoid.
Qed.
Example PCM_evar3 : forall x y, exists w, x \226\136\152 y = w.
Proof.
(intros).
eexists.
monoid.
Qed.
End Examples.
