Time From iris.proofmode Require Import base.
Time From iris.algebra Require Export base.
Time From iris.bi Require Export bi.
Time From iris.bi Require Import tactics.
Time Set Default Proof Using "Type".
Time Import bi.
Time
Inductive env (A : Type) : Type :=
  | Enil : env A
  | Esnoc : env A \226\134\146 ident \226\134\146 A \226\134\146 env A.
Time Arguments Enil {_}.
Time Arguments Esnoc {_} _ _ _.
Time Instance: (Params (@Enil) 1) := { }.
Time Instance: (Params (@Esnoc) 1) := { }.
Time
Fixpoint env_lookup {A} (i : ident) (\206\147 : env A) : 
option A :=
  match \206\147 with
  | Enil => None
  | Esnoc \206\147 j x => if ident_beq i j then Some x else env_lookup i \206\147
  end.
Time Module env_notations.
Time Notation "y \226\137\171= f" := (pm_option_bind f y).
Time Notation "x \226\134\144 y ; z" := (y \226\137\171= (\206\187 x, z)).
Time Notation "' x1 .. xn \226\134\144 y ; z" := (y \226\137\171= (\206\187 x1, .. (\206\187 xn, z) ..)).
Time Notation "\206\147 !! j" := (env_lookup j \206\147).
Time Notation "b1 && b2" := (if b1 then b2 else false) : bool_scope.
Time End env_notations.
Time Import env_notations.
Time
Inductive env_wf {A} : env A \226\134\146 Prop :=
  | Enil_wf : env_wf Enil
  | Esnoc_wf : forall \206\147 i x, \206\147 !! i = None \226\134\146 env_wf \206\147 \226\134\146 env_wf (Esnoc \206\147 i x).
Time
Fixpoint env_to_list {A} (E : env A) : list A :=
  match E with
  | Enil => []
  | Esnoc \206\147 _ x => x :: env_to_list \206\147
  end.
Time Coercion env_to_list : env >-> list.
Time Instance: (Params (@env_to_list) 1) := { }.
Time
Fixpoint env_dom {A} (\206\147 : env A) : list ident :=
  match \206\147 with
  | Enil => []
  | Esnoc \206\147 i _ => i :: env_dom \206\147
  end.
Time
Fixpoint env_app {A} (\206\147app : env A) (\206\147 : env A) : 
option (env A) :=
  match \206\147app with
  | Enil => Some \206\147
  | Esnoc \206\147app i x =>
      \206\147' \226\134\144 env_app \206\147app \206\147;
      match \206\147' !! i with
      | None => Some (Esnoc \206\147' i x)
      | Some _ => None
      end
  end.
Time
Fixpoint env_replace {A} (i : ident) (\206\147i : env A) 
(\206\147 : env A) : option (env A) :=
  match \206\147 with
  | Enil => None
  | Esnoc \206\147 j x =>
      if ident_beq i j then env_app \206\147i \206\147
      else match \206\147i !! j with
           | None => \206\147' \226\134\144 env_replace i \206\147i \206\147; Some (Esnoc \206\147' j x)
           | Some _ => None
           end
  end.
Time
Fixpoint env_delete {A} (i : ident) (\206\147 : env A) : 
env A :=
  match \206\147 with
  | Enil => Enil
  | Esnoc \206\147 j x => if ident_beq i j then \206\147 else Esnoc (env_delete i \206\147) j x
  end.
Time
Fixpoint env_lookup_delete {A} (i : ident) (\206\147 : env A) : 
option (A * env A) :=
  match \206\147 with
  | Enil => None
  | Esnoc \206\147 j x =>
      if ident_beq i j then Some (x, \206\147)
      else ' '(y, \206\147') \226\134\144 env_lookup_delete i \206\147; Some (y, Esnoc \206\147' j x)
  end.
Time
Inductive env_Forall2 {A} {B} (P : A \226\134\146 B \226\134\146 Prop) : env A \226\134\146 env B \226\134\146 Prop :=
  | env_Forall2_nil : env_Forall2 P Enil Enil
  | env_Forall2_snoc :
      forall \206\1471 \206\1472 i x y,
      env_Forall2 P \206\1471 \206\1472
      \226\134\146 P x y \226\134\146 env_Forall2 P (Esnoc \206\1471 i x) (Esnoc \206\1472 i y).
Time
Inductive env_subenv {A} : relation (env A) :=
  | env_subenv_nil : env_subenv Enil Enil
  | env_subenv_snoc :
      forall \206\1471 \206\1472 i x,
      env_subenv \206\1471 \206\1472 \226\134\146 env_subenv (Esnoc \206\1471 i x) (Esnoc \206\1472 i x)
  | env_subenv_skip :
      forall \206\1471 \206\1472 i y, env_subenv \206\1471 \206\1472 \226\134\146 env_subenv \206\1471 (Esnoc \206\1472 i y).
Time Section env.
Time Context {A : Type}.
Time Implicit Type \206\147 : env A.
Time Implicit Type i : ident.
Time Implicit Type x : A.
Time Hint Resolve Esnoc_wf Enil_wf: core.
Time
Ltac
 simplify :=
  repeat
   match goal with
   | _ =>
       progress simplify_eq /=
   | H:context [ ident_beq ?s1 ?s2 ]
     |- _ => destruct (ident_beq_reflect s1 s2)
   | |- context [ ident_beq ?s1 ?s2 ] => destruct (ident_beq_reflect s1 s2)
   | H:context [ pm_option_bind _ ?x ] |- _ => destruct x eqn:?
   | |- context [ pm_option_bind _ ?x ] => destruct x eqn:?
   | _ => case_match
   end.
Time
Lemma env_lookup_perm \206\147 i x : \206\147 !! i = Some x \226\134\146 \206\147 \226\137\161\226\130\154 x :: env_delete i \206\147.
Time Proof.
Time
(induction \206\147; intros; simplify; rewrite 1?Permutation_swap; f_equiv; eauto).
Time Qed.
Time Lemma env_lookup_snoc \206\147 i P : env_lookup i (Esnoc \206\147 i P) = Some P.
Time Proof.
Time (induction \206\147; simplify; auto).
Time Qed.
Time
Lemma env_lookup_snoc_ne \206\147 i j P :
  i \226\137\160 j \226\134\146 env_lookup i (Esnoc \206\147 j P) = env_lookup i \206\147.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> induction \206\147 =>?; simplify; auto).
Time Qed.
Time
Lemma env_app_perm \206\147 \206\147app \206\147' :
  env_app \206\147app \206\147 = Some \206\147' \226\134\146 env_to_list \206\147' \226\137\161\226\130\154 \206\147app ++ \206\147.
Time Proof.
Time (revert \206\147'; induction \206\147app; intros; simplify; f_equal; auto).
Time Qed.
Time
Lemma env_app_fresh \206\147 \206\147app \206\147' i :
  env_app \206\147app \206\147 = Some \206\147'
  \226\134\146 \206\147app !! i = None \226\134\146 \206\147 !! i = None \226\134\146 \206\147' !! i = None.
Time Proof.
Time revert \206\147'.
Time (induction \206\147app; intros; simplify; eauto).
Time Qed.
Time
Lemma env_app_fresh_1 \206\147 \206\147app \206\147' i x :
  env_app \206\147app \206\147 = Some \206\147' \226\134\146 \206\147' !! i = None \226\134\146 \206\147 !! i = None.
Time Proof.
Time revert \206\147'.
Time (induction \206\147app; intros; simplify; eauto).
Time Qed.
Time
Lemma env_app_disjoint \206\147 \206\147app \206\147' i :
  env_app \206\147app \206\147 = Some \206\147' \226\134\146 \206\147app !! i = None \226\136\168 \206\147 !! i = None.
Time Proof.
Time revert \206\147'.
Time
(induction \206\147app; intros; simplify; naive_solver eauto using env_app_fresh_1).
Time Qed.
Time
Lemma env_app_wf \206\147 \206\147app \206\147' : env_app \206\147app \206\147 = Some \206\147' \226\134\146 env_wf \206\147 \226\134\146 env_wf \206\147'.
Time Proof.
Time revert \206\147'.
Time (induction \206\147app; intros; simplify; eauto).
Time Qed.
Time
Lemma env_replace_fresh \206\147 \206\147j \206\147' i j :
  env_replace j \206\147j \206\147 = Some \206\147'
  \226\134\146 \206\147j !! i = None \226\134\146 env_delete j \206\147 !! i = None \226\134\146 \206\147' !! i = None.
Time Proof.
Time revert \206\147'.
Time (induction \206\147; intros; simplify; eauto using env_app_fresh).
Time Qed.
Time
Lemma env_replace_wf \206\147 \206\147i \206\147' i :
  env_replace i \206\147i \206\147 = Some \206\147' \226\134\146 env_wf (env_delete i \206\147) \226\134\146 env_wf \206\147'.
Time Proof.
Time revert \206\147'.
Time
(induction \206\147; intros ? ?; simplify; [  | inversion_clear 1 ]; eauto
  using env_app_wf, env_replace_fresh).
Time Qed.
Time
Lemma env_replace_lookup \206\147 \206\147i \206\147' i :
  env_replace i \206\147i \206\147 = Some \206\147' \226\134\146 is_Some (\206\147 !! i).
Time Proof.
Time revert \206\147'.
Time (induction \206\147; intros; simplify; eauto).
Time Qed.
Time
Lemma env_replace_perm \206\147 \206\147i \206\147' i :
  env_replace i \206\147i \206\147 = Some \206\147' \226\134\146 \206\147' \226\137\161\226\130\154 \206\147i ++ env_delete i \206\147.
Time Proof.
Time revert \206\147'.
Time
(<ssreflect_plugin::ssrtclintros@0> induction \206\147 as [| \206\147 IH j y] =>\206\147' ?;
  simplify; auto using env_app_perm).
Time rewrite -Permutation_middle -IH //.
Time Qed.
Time
Lemma env_lookup_delete_correct \206\147 i :
  env_lookup_delete i \206\147 = x \226\134\144 \206\147 !! i; Some (x, env_delete i \206\147).
Time Proof.
Time (induction \206\147; intros; simplify; eauto).
Time Qed.
Time
Lemma env_lookup_delete_Some \206\147 \206\147' i x :
  env_lookup_delete i \206\147 = Some (x, \206\147')
  \226\134\148 \206\147 !! i = Some x \226\136\167 \206\147' = env_delete i \206\147.
Time Proof.
Time (rewrite env_lookup_delete_correct; simplify; naive_solver).
Time Qed.
Time Lemma env_lookup_env_delete \206\147 j : env_wf \206\147 \226\134\146 env_delete j \206\147 !! j = None.
Time Proof.
Time (induction 1; intros; simplify; eauto).
Time Qed.
Time
Lemma env_lookup_env_delete_ne \206\147 i j : i \226\137\160 j \226\134\146 env_delete j \206\147 !! i = \206\147 !! i.
Time Proof.
Time (induction \206\147; intros; simplify; eauto).
Time Qed.
Time
Lemma env_delete_fresh \206\147 i j : \206\147 !! i = None \226\134\146 env_delete j \206\147 !! i = None.
Time Proof.
Time (induction \206\147; intros; simplify; eauto).
Time Qed.
Time Lemma env_delete_wf \206\147 j : env_wf \206\147 \226\134\146 env_wf (env_delete j \206\147).
Time Proof.
Time (induction 1; simplify; eauto using env_delete_fresh).
Time Qed.
Time #[global]
Instance env_Forall2_refl  (P : relation A):
 (Reflexive P \226\134\146 Reflexive (env_Forall2 P)).
Time Proof.
Time (intros ? \206\147).
Time (induction \206\147; constructor; auto).
Time Qed.
Time #[global]
Instance env_Forall2_sym  (P : relation A):
 (Symmetric P \226\134\146 Symmetric (env_Forall2 P)).
Time Proof.
Time (induction 2; constructor; auto).
Time Qed.
Time #[global]
Instance env_Forall2_trans  (P : relation A):
 (Transitive P \226\134\146 Transitive (env_Forall2 P)).
Time Proof.
Time (intros ? \206\1471 \206\1472 \206\1473 H\206\147; revert \206\1473).
Time (induction H\206\147; inversion_clear 1; constructor; eauto).
Time Qed.
Time #[global]
Instance env_Forall2_antisymm  (P Q : relation A):
 (AntiSymm P Q \226\134\146 AntiSymm (env_Forall2 P) (env_Forall2 Q)).
Time Proof.
Time (induction 2; inversion_clear 1; constructor; auto).
Time Qed.
Time
Lemma env_Forall2_impl {B} (P Q : A \226\134\146 B \226\134\146 Prop) \206\147 
  \206\163 : env_Forall2 P \206\147 \206\163 \226\134\146 (\226\136\128 x y, P x y \226\134\146 Q x y) \226\134\146 env_Forall2 Q \206\147 \206\163.
Time Proof.
Time (induction 1; constructor; eauto).
Time Qed.
Time #[global]
Instance Esnoc_proper  (P : relation A):
 (Proper (env_Forall2 P ==> (=) ==> P ==> env_Forall2 P) Esnoc).
Time Proof.
Time (intros \206\1471 \206\1472 H\206\147 i ? <-; by constructor).
Time Qed.
Time #[global]
Instance env_to_list_proper  (P : relation A):
 (Proper (env_Forall2 P ==> Forall2 P) env_to_list).
Time Proof.
Time (induction 1; constructor; auto).
Time Qed.
Time
Lemma env_Forall2_fresh {B} (P : A \226\134\146 B \226\134\146 Prop) \206\147 \206\163 
  i : env_Forall2 P \206\147 \206\163 \226\134\146 \206\147 !! i = None \226\134\146 \206\163 !! i = None.
Time Proof.
Time by induction 1; simplify.
Time Qed.
Time
Lemma env_Forall2_wf {B} (P : A \226\134\146 B \226\134\146 Prop) \206\147 \206\163 :
  env_Forall2 P \206\147 \206\163 \226\134\146 env_wf \206\147 \226\134\146 env_wf \206\163.
Time Proof.
Time (induction 1; inversion_clear 1; eauto using env_Forall2_fresh).
Time Qed.
Time
Lemma env_subenv_fresh \206\147 \206\163 i : env_subenv \206\147 \206\163 \226\134\146 \206\163 !! i = None \226\134\146 \206\147 !! i = None.
Time Proof.
Time by induction 1; simplify.
Time Qed.
Time Lemma env_subenv_wf \206\147 \206\163 : env_subenv \206\147 \206\163 \226\134\146 env_wf \206\163 \226\134\146 env_wf \206\147.
Time Proof.
Time (induction 1; inversion_clear 1; eauto using env_subenv_fresh).
Time Qed.
Time #[global]
Instance env_to_list_subenv_proper :
 (Proper (env_subenv ==> sublist) (@env_to_list A)).
Time Proof.
Time (induction 1; simpl; constructor; auto).
Time Qed.
Time End env.
Time
Record envs (PROP : bi) :=
 Envs {env_intuitionistic : env PROP;
       env_spatial : env PROP;
       env_counter : positive}.
Time Add Printing Constructor envs.
Time Arguments Envs {_} _ _ _.
Time Arguments env_intuitionistic {_} _.
Time Arguments env_spatial {_} _.
Time Arguments env_counter {_} _.
Time
Record envs_wf' {PROP : bi} (\206\147p \206\147s : env PROP) :={
 env_intuitionistic_valid : env_wf \206\147p;
 env_spatial_valid : env_wf \206\147s;
 envs_disjoint : forall i, \206\147p !! i = None \226\136\168 \206\147s !! i = None}.
Time
Definition envs_wf {PROP : bi} (\206\148 : envs PROP) :=
  envs_wf' (env_intuitionistic \206\148) (env_spatial \206\148).
Time
Definition of_envs' {PROP : bi} (\206\147p \206\147s : env PROP) : PROP :=
  (\226\140\156envs_wf' \206\147p \206\147s\226\140\157 \226\136\167 \226\150\161 [\226\136\167] \206\147p \226\136\151 [\226\136\151] \206\147s)%I.
Time Instance: (Params (@of_envs') 1) := { }.
Time
Definition of_envs {PROP : bi} (\206\148 : envs PROP) : PROP :=
  of_envs' (env_intuitionistic \206\148) (env_spatial \206\148).
Time Instance: (Params (@of_envs) 1) := { }.
Time Arguments of_envs : simpl never.
Time
Definition envs_entails_aux :
  seal (\206\187 {PROP : bi} (\206\147p \206\147s : env PROP) (Q : PROP), of_envs' \206\147p \206\147s \226\138\162 Q).
Time Proof.
Time by eexists.
Time Qed.
Time
Definition envs_entails {PROP : bi} (\206\148 : envs PROP) 
  (Q : PROP) : Prop :=
  envs_entails_aux.(unseal) PROP (env_intuitionistic \206\148) (env_spatial \206\148) Q.
Time
Definition envs_entails_eq :
  @envs_entails = (\206\187 {PROP} (\206\148 : envs PROP) Q, of_envs \206\148 \226\138\162 Q).
Time Proof.
Time by rewrite /envs_entails envs_entails_aux.(seal_eq).
Time Qed.
Time Arguments envs_entails {PROP} \206\148 Q%I : rename.
Time Instance: (Params (@envs_entails) 1) := { }.
Time
Record envs_Forall2 {PROP : bi} (R : relation PROP) (\206\1481 \206\1482 : envs PROP) :={
 env_intuitionistic_Forall2 :
  env_Forall2 R (env_intuitionistic \206\1481) (env_intuitionistic \206\1482);
 env_spatial_Forall2 : env_Forall2 R (env_spatial \206\1481) (env_spatial \206\1482)}.
Time
Definition envs_dom {PROP} (\206\148 : envs PROP) : list ident :=
  env_dom (env_intuitionistic \206\148) ++ env_dom (env_spatial \206\148).
Time
Definition envs_lookup {PROP} (i : ident) (\206\148 : envs PROP) :
  option (bool * PROP) :=
  let (\206\147p, \206\147s, n) := \206\148 in
  match env_lookup i \206\147p with
  | Some P => Some (true, P)
  | None => P \226\134\144 env_lookup i \206\147s; Some (false, P)
  end.
Time
Definition envs_delete {PROP} (remove_intuitionistic : bool) 
  (i : ident) (p : bool) (\206\148 : envs PROP) : envs PROP :=
  let (\206\147p, \206\147s, n) := \206\148 in
  match p with
  | true => Envs (if remove_intuitionistic then env_delete i \206\147p else \206\147p) \206\147s n
  | false => Envs \206\147p (env_delete i \206\147s) n
  end.
Time
Definition envs_lookup_delete {PROP} (remove_intuitionistic : bool)
  (i : ident) (\206\148 : envs PROP) : option (bool * PROP * envs PROP) :=
  let (\206\147p, \206\147s, n) := \206\148 in
  match env_lookup_delete i \206\147p with
  | Some (P, \206\147p') =>
      Some (true, P, Envs (if remove_intuitionistic then \206\147p' else \206\147p) \206\147s n)
  | None =>
      ' '(P, \206\147s') \226\134\144 env_lookup_delete i \206\147s; Some (false, P, Envs \206\147p \206\147s' n)
  end.
Time
Fixpoint envs_lookup_delete_list {PROP} (remove_intuitionistic : bool)
(js : list ident) (\206\148 : envs PROP) : option (bool * list PROP * envs PROP) :=
  match js with
  | [] => Some (true, [], \206\148)
  | j :: js =>
      ' '(p, P, \206\148') \226\134\144 envs_lookup_delete remove_intuitionistic j \206\148;
      ' '(q, Ps, \206\148'') \226\134\144 envs_lookup_delete_list remove_intuitionistic js \206\148';
      Some ((p : bool) && q, P :: Ps, \206\148'')
  end.
Time
Definition envs_snoc {PROP} (\206\148 : envs PROP) (p : bool) 
  (j : ident) (P : PROP) : envs PROP :=
  let (\206\147p, \206\147s, n) := \206\148 in
  if p then Envs (Esnoc \206\147p j P) \206\147s n else Envs \206\147p (Esnoc \206\147s j P) n.
Time
Definition envs_app {PROP : bi} (p : bool) (\206\147 : env PROP) 
  (\206\148 : envs PROP) : option (envs PROP) :=
  let (\206\147p, \206\147s, n) := \206\148 in
  match p with
  | true => _ \226\134\144 env_app \206\147 \206\147s; \206\147p' \226\134\144 env_app \206\147 \206\147p; Some (Envs \206\147p' \206\147s n)
  | false => _ \226\134\144 env_app \206\147 \206\147p; \206\147s' \226\134\144 env_app \206\147 \206\147s; Some (Envs \206\147p \206\147s' n)
  end.
Time
Definition envs_simple_replace {PROP : bi} (i : ident) 
  (p : bool) (\206\147 : env PROP) (\206\148 : envs PROP) : option (envs PROP) :=
  let (\206\147p, \206\147s, n) := \206\148 in
  match p with
  | true => _ \226\134\144 env_app \206\147 \206\147s; \206\147p' \226\134\144 env_replace i \206\147 \206\147p; Some (Envs \206\147p' \206\147s n)
  | false => _ \226\134\144 env_app \206\147 \206\147p; \206\147s' \226\134\144 env_replace i \206\147 \206\147s; Some (Envs \206\147p \206\147s' n)
  end.
Time
Definition envs_replace {PROP : bi} (i : ident) (p q : bool) 
  (\206\147 : env PROP) (\206\148 : envs PROP) : option (envs PROP) :=
  if beq p q then envs_simple_replace i p \206\147 \206\148
  else envs_app q \206\147 (envs_delete true i p \206\148).
Time
Definition env_spatial_is_nil {PROP} (\206\148 : envs PROP) : bool :=
  match env_spatial \206\148 with
  | Enil => true
  | _ => false
  end.
Time
Definition envs_clear_spatial {PROP} (\206\148 : envs PROP) : 
  envs PROP := Envs (env_intuitionistic \206\148) Enil (env_counter \206\148).
Time
Definition envs_clear_intuitionistic {PROP} (\206\148 : envs PROP) : 
  envs PROP := Envs Enil (env_spatial \206\148) (env_counter \206\148).
Time
Definition envs_incr_counter {PROP} (\206\148 : envs PROP) : 
  envs PROP :=
  Envs (env_intuitionistic \206\148) (env_spatial \206\148) (Pos_succ (env_counter \206\148)).
Time
Fixpoint envs_split_go {PROP} (js : list ident) (\206\1481 \206\1482 : envs PROP) :
option (envs PROP * envs PROP) :=
  match js with
  | [] => Some (\206\1481, \206\1482)
  | j :: js =>
      ' '(p, P, \206\1481') \226\134\144 envs_lookup_delete true j \206\1481;
      if p : bool then envs_split_go js \206\1481 \206\1482
      else envs_split_go js \206\1481' (envs_snoc \206\1482 false j P)
  end.
Time
Definition envs_split {PROP} (d : direction) (js : list ident)
  (\206\148 : envs PROP) : option (envs PROP * envs PROP) :=
  ' '(\206\1481, \206\1482) \226\134\144 envs_split_go js \206\148 (envs_clear_spatial \206\148);
  match d with
  | Right => Some (\206\1481, \206\1482)
  | _ => Some (\206\1482, \206\1481)
  end.
Time
Definition env_to_prop {PROP : bi} (\206\147 : env PROP) : PROP :=
  let
    fix aux \206\147 acc :=
      match \206\147 with
      | Enil => acc
      | Esnoc \206\147 _ P => aux \206\147 (P \226\136\151 acc)%I
      end in
  match \206\147 with
  | Enil => emp%I
  | Esnoc \206\147 _ P => aux \206\147 P
  end.
Time Section envs.
Time Context {PROP : bi}.
Time Implicit Types \206\147 \206\147p \206\147s : env PROP.
Time Implicit Type \206\148 : envs PROP.
Time Implicit Types P Q : PROP.
Time
Lemma of_envs_eq \206\148 :
  of_envs \206\148 =
  (\226\140\156envs_wf \206\148\226\140\157 \226\136\167 \226\150\161 [\226\136\167] env_intuitionistic \206\148 \226\136\151 [\226\136\151] env_spatial \206\148)%I.
Time Proof.
Time done.
Time Qed.
Time
Lemma of_envs_eq' \206\148 :
  of_envs \206\148 \226\138\163\226\138\162 (\226\140\156envs_wf \206\148\226\140\157 \226\136\167 \226\150\161 [\226\136\167] env_intuitionistic \206\148) \226\136\151 [\226\136\151] env_spatial \206\148.
Time Proof.
Time rewrite of_envs_eq persistent_and_sep_assoc //.
Time Qed.
Time #[global]
Instance envs_Forall2_refl  (R : relation PROP):
 (Reflexive R \226\134\146 Reflexive (envs_Forall2 R)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]
Instance envs_Forall2_sym  (R : relation PROP):
 (Symmetric R \226\134\146 Symmetric (envs_Forall2 R)).
Time Proof.
Time (intros ? ? ? [? ?]; by constructor).
Time Qed.
Time #[global]
Instance envs_Forall2_trans  (R : relation PROP):
 (Transitive R \226\134\146 Transitive (envs_Forall2 R)).
Time Proof.
Time (intros ? ? ? [? ?] [? ?] [? ?]; constructor; etrans; eauto).
Time Qed.
Time #[global]
Instance envs_Forall2_antisymm  (R R' : relation PROP):
 (AntiSymm R R' \226\134\146 AntiSymm (envs_Forall2 R) (envs_Forall2 R')).
Time Proof.
Time (intros ? ? ? [? ?] [? ?]; constructor; by eapply (anti_symm _)).
Time Qed.
Time
Lemma envs_Forall2_impl (R R' : relation PROP) \206\1481 
  \206\1482 : envs_Forall2 R \206\1481 \206\1482 \226\134\146 (\226\136\128 P Q, R P Q \226\134\146 R' P Q) \226\134\146 envs_Forall2 R' \206\1481 \206\1482.
Time Proof.
Time (intros [? ?] ?; constructor; eauto using env_Forall2_impl).
Time Qed.
Time #[global]
Instance env_intuitionistic_mono :
 (Proper (envs_Forall2 (\226\138\162) ==> env_Forall2 (\226\138\162)) (@env_intuitionistic PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance env_intuitionistic_flip_mono :
 (Proper (flip (envs_Forall2 (\226\138\162)) ==> flip (env_Forall2 (\226\138\162)))
    (@env_intuitionistic PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance env_intuitionistic_proper :
 (Proper (envs_Forall2 (\226\138\163\226\138\162) ==> env_Forall2 (\226\138\163\226\138\162)) (@env_intuitionistic PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance env_spatial_mono :
 (Proper (envs_Forall2 (\226\138\162) ==> env_Forall2 (\226\138\162)) (@env_spatial PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance env_spatial_flip_mono :
 (Proper (flip (envs_Forall2 (\226\138\162)) ==> flip (env_Forall2 (\226\138\162)))
    (@env_spatial PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance env_spatial_proper :
 (Proper (envs_Forall2 (\226\138\163\226\138\162) ==> env_Forall2 (\226\138\163\226\138\162)) (@env_spatial PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance of_envs_mono' :
 (Proper (env_Forall2 (\226\138\162) ==> env_Forall2 (\226\138\162) ==> (\226\138\162)) (@of_envs' PROP)).
Time Proof.
Time (intros \206\147p1 \206\147p2 Hp \206\147s1 \206\147s2 Hs; apply and_mono; simpl in *).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_mono =>- [? ? ?]).
Time
(constructor; naive_solver eauto using env_Forall2_wf, env_Forall2_fresh).
Time -
Time by repeat f_equiv.
Time Qed.
Time #[global]
Instance of_envs_proper' :
 (Proper (env_Forall2 (\226\138\163\226\138\162) ==> env_Forall2 (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@of_envs' PROP)).
Time Proof.
Time
(intros \206\147p1 \206\147p2 Hp \206\147s1 \206\147s2 Hs; apply (anti_symm (\226\138\162)); apply of_envs_mono';
  eapply (env_Forall2_impl (\226\138\163\226\138\162)); by eauto using equiv_entails).
Time Qed.
Time #[global]
Instance of_envs_mono : (Proper (envs_Forall2 (\226\138\162) ==> (\226\138\162)) (@of_envs PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance of_envs_proper :
 (Proper (envs_Forall2 (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162)) (@of_envs PROP)).
Time Proof.
Time solve_proper.
Time Qed.
Time #[global]
Instance Envs_proper  (R : relation PROP):
 (Proper (env_Forall2 R ==> env_Forall2 R ==> eq ==> envs_Forall2 R)
    (@Envs PROP)).
Time Proof.
Time by constructor.
Time Qed.
Time #[global]
Instance envs_entails_proper :
 (Proper (envs_Forall2 (\226\138\163\226\138\162) ==> (\226\138\163\226\138\162) ==> iff) (@envs_entails PROP)).
Time Proof.
Time rewrite envs_entails_eq.
Time solve_proper.
Time Qed.
Time #[global]
Instance envs_entails_mono :
 (Proper (flip (envs_Forall2 (\226\138\162)) ==> (\226\138\162) ==> impl) (@envs_entails PROP)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>\206\1481 \206\1482 ? P1 P2
 {+}<- {+}<-).
Time by f_equiv.
Time Qed.
Time #[global]
Instance envs_entails_flip_mono :
 (Proper (envs_Forall2 (\226\138\162) ==> flip (\226\138\162) ==> flip impl) (@envs_entails PROP)).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>\206\1481 \206\1482 ? P1 P2
 {+}<- {+}<-).
Time by f_equiv.
Time Qed.
Time Lemma envs_delete_intuitionistic \206\148 i : envs_delete false i true \206\148 = \206\148.
Time Proof.
Time by destruct \206\148.
Time Qed.
Time
Lemma envs_delete_spatial \206\148 i :
  envs_delete false i false \206\148 = envs_delete true i false \206\148.
Time Proof.
Time by destruct \206\148.
Time Qed.
Time
Lemma envs_lookup_delete_Some \206\148 \206\148' rp i p P :
  envs_lookup_delete rp i \206\148 = Some (p, P, \206\148')
  \226\134\148 envs_lookup i \206\148 = Some (p, P) \226\136\167 \206\148' = envs_delete rp i p \206\148.
Time Proof.
Time rewrite /envs_lookup /envs_delete /envs_lookup_delete.
Time (destruct \206\148 as [\206\147p \206\147s]; rewrite /= !env_lookup_delete_correct).
Time (destruct (\206\147p !! i), (\206\147s !! i); naive_solver).
Time Qed.
Time
Lemma envs_lookup_sound' \206\148 rp i p P :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p P \226\136\151 of_envs (envs_delete rp i p \206\148).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /envs_lookup /envs_delete
 !of_envs_eq =>?).
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>Hwf).
Time (destruct \206\148 as [\206\147p \206\147s], (\206\147p !! i) eqn:?; simplify_eq /=).
Time -
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite pure_True ?left_id ; last 
 destruct Hwf, rp; constructor; naive_solver eauto
  using env_delete_wf, env_delete_fresh).
Time (destruct rp).
Time +
Time rewrite (env_lookup_perm \206\147p) //= intuitionistically_and.
Time by rewrite and_sep_intuitionistically -assoc.
Time +
Time rewrite {+1}intuitionistically_sep_dup {+1}(env_lookup_perm \206\147p) //=.
Time by rewrite intuitionistically_and and_elim_l -assoc.
Time -
Time (destruct (\206\147s !! i) eqn:?; simplify_eq /=).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite pure_True ?left_id ; last 
 destruct Hwf; constructor; naive_solver eauto
  using env_delete_wf, env_delete_fresh).
Time rewrite (env_lookup_perm \206\147s) //=.
Time by rewrite !assoc -(comm _ P).
Time Qed.
Time
Lemma envs_lookup_sound \206\148 i p P :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p P \226\136\151 of_envs (envs_delete true i p \206\148).
Time Proof.
Time (apply envs_lookup_sound').
Time Qed.
Time
Lemma envs_lookup_intuitionistic_sound \206\148 i P :
  envs_lookup i \206\148 = Some (true, P) \226\134\146 of_envs \206\148 \226\138\162 \226\150\161 P \226\136\151 of_envs \206\148.
Time Proof.
Time (intros ?%(envs_lookup_sound' _ false)).
Time by destruct \206\148.
Time Qed.
Time
Lemma envs_lookup_sound_2 \206\148 i p P :
  envs_wf \206\148
  \226\134\146 envs_lookup i \206\148 = Some (p, P)
    \226\134\146 \226\150\161?p P \226\136\151 of_envs (envs_delete true i p \206\148) \226\138\162 of_envs \206\148.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /envs_lookup !of_envs_eq =>Hwf ?).
Time rewrite [\226\140\156envs_wf \206\148\226\140\157%I]pure_True // left_id.
Time (destruct \206\148 as [\206\147p \206\147s], (\206\147p !! i) eqn:?; simplify_eq /=).
Time -
Time
rewrite (env_lookup_perm \206\147p) //= intuitionistically_and
 and_sep_intuitionistically and_elim_r.
Time cancel [\226\150\161 P]%I.
Time solve_sep_entails.
Time -
Time (destruct (\206\147s !! i) eqn:?; simplify_eq /=).
Time rewrite (env_lookup_perm \206\147s) //= and_elim_r.
Time cancel [P].
Time solve_sep_entails.
Time Qed.
Time
Lemma envs_lookup_split \206\148 i p P :
  envs_lookup i \206\148 = Some (p, P) \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p P \226\136\151 (\226\150\161?p P -\226\136\151 of_envs \206\148).
Time Proof.
Time (intros).
Time (apply pure_elim with (envs_wf \206\148)).
Time {
Time rewrite of_envs_eq.
Time (apply and_elim_l).
Time }
Time (intros).
Time rewrite {+1}envs_lookup_sound //.
Time (apply sep_mono_r).
Time (apply wand_intro_l, envs_lookup_sound_2; done).
Time Qed.
Time
Lemma envs_lookup_delete_sound \206\148 \206\148' rp i p P :
  envs_lookup_delete rp i \206\148 = Some (p, P, \206\148')
  \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p P \226\136\151 of_envs \206\148'.
Time Proof.
Time (intros [? ->]%envs_lookup_delete_Some).
Time by apply envs_lookup_sound'.
Time Qed.
Time
Lemma envs_lookup_delete_list_sound \206\148 \206\148' rp js p Ps :
  envs_lookup_delete_list rp js \206\148 = Some (p, Ps, \206\148')
  \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p [\226\136\151] Ps \226\136\151 of_envs \206\148'.
Time Proof.
Time revert \206\148 \206\148' p Ps.
Time
(<ssreflect_plugin::ssrtclintros@0> induction js as [| j js IH] =>\206\148 \206\148'' p Ps
  ?; simplify_eq /=).
Time {
Time by rewrite intuitionistically_emp left_id.
Time }
Time
(destruct (envs_lookup_delete rp j \206\148) as [[[q1 P] \206\148']| ] eqn:Hj; simplify_eq
  /=).
Time (apply envs_lookup_delete_Some in Hj as [Hj ->]).
Time
(destruct (envs_lookup_delete_list _ js _) as [[[q2 Ps'] ?]| ] eqn:?;
  simplify_eq /=).
Time rewrite -intuitionistically_if_sep_2 -assoc.
Time (rewrite envs_lookup_sound' //; rewrite IH //).
Time
(repeat <ssreflect_plugin::ssrtclintros@0> apply sep_mono =>//;
  apply intuitionistically_if_flag_mono; by destruct q1).
Time Qed.
Time
Lemma envs_lookup_delete_list_cons \206\148 \206\148' \206\148'' rp j js 
  p1 p2 P Ps :
  envs_lookup_delete rp j \206\148 = Some (p1, P, \206\148')
  \226\134\146 envs_lookup_delete_list rp js \206\148' = Some (p2, Ps, \206\148'')
    \226\134\146 envs_lookup_delete_list rp (j :: js) \206\148 = Some (p1 && p2, P :: Ps, \206\148'').
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite //= =>{+}-> //= {+}-> //=).
Time Qed.
Time
Lemma envs_lookup_delete_list_nil \206\148 rp :
  envs_lookup_delete_list rp [] \206\148 = Some (true, [], \206\148).
Time Proof.
Time done.
Time Qed.
Time
Lemma envs_lookup_snoc \206\148 i p P :
  envs_lookup i \206\148 = None \226\134\146 envs_lookup i (envs_snoc \206\148 p i P) = Some (p, P).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /envs_lookup /envs_snoc =>?).
Time
(destruct \206\148 as [\206\147p \206\147s], p, (\206\147p !! i); simplify_eq; by rewrite env_lookup_snoc).
Time Qed.
Time
Lemma envs_lookup_snoc_ne \206\148 i j p P :
  i \226\137\160 j \226\134\146 envs_lookup i (envs_snoc \206\148 p j P) = envs_lookup i \206\148.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /envs_lookup /envs_snoc =>?).
Time (destruct \206\148 as [\206\147p \206\147s], p; simplify_eq; by rewrite env_lookup_snoc_ne).
Time Qed.
Time
Lemma envs_snoc_sound \206\148 p i P :
  envs_lookup i \206\148 = None \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p P -\226\136\151 of_envs (envs_snoc \206\148 p i P).
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /envs_lookup /envs_snoc
  !of_envs_eq =>?; <ssreflect_plugin::ssrtclintros@0> 
  apply pure_elim_l =>Hwf).
Time
(destruct \206\148 as [\206\147p \206\147s], (\206\147p !! i) eqn:?, (\206\147s !! i) eqn:?; simplify_eq /=).
Time (apply wand_intro_l; destruct p; simpl).
Time -
Time (apply and_intro; [ apply pure_intro |  ]).
Time +
Time (destruct Hwf; constructor; simpl; eauto using Esnoc_wf).
Time (intros j; destruct (ident_beq_reflect j i); naive_solver).
Time +
Time by rewrite intuitionistically_and and_sep_intuitionistically assoc.
Time -
Time (apply and_intro; [ apply pure_intro |  ]).
Time +
Time (destruct Hwf; constructor; simpl; eauto using Esnoc_wf).
Time (intros j; destruct (ident_beq_reflect j i); naive_solver).
Time +
Time solve_sep_entails.
Time Qed.
Time
Lemma envs_app_sound \206\148 \206\148' p \206\147 :
  envs_app p \206\147 \206\148 = Some \206\148'
  \226\134\146 of_envs \206\148 \226\138\162 (if p then \226\150\161 [\226\136\167] \206\147 else [\226\136\151] \206\147) -\226\136\151 of_envs \206\148'.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite !of_envs_eq /envs_app =>?;
  <ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>Hwf).
Time (destruct \206\148 as [\206\147p \206\147s], p; simplify_eq /=).
Time -
Time
(destruct (env_app \206\147 \206\147s) eqn:Happ, (env_app \206\147 \206\147p) as [\206\147p'| ] eqn:?;
  simplify_eq /=).
Time (apply wand_intro_l, and_intro; [ apply pure_intro |  ]).
Time +
Time (destruct Hwf; constructor; simpl; eauto using env_app_wf).
Time (intros j).
Time (apply (env_app_disjoint _ _ _ j) in Happ).
Time naive_solver eauto using env_app_fresh.
Time +
Time rewrite (env_app_perm _ _ \206\147p') //.
Time rewrite big_opL_app intuitionistically_and and_sep_intuitionistically.
Time solve_sep_entails.
Time -
Time
(destruct (env_app \206\147 \206\147p) eqn:Happ, (env_app \206\147 \206\147s) as [\206\147s'| ] eqn:?;
  simplify_eq /=).
Time (apply wand_intro_l, and_intro; [ apply pure_intro |  ]).
Time +
Time (destruct Hwf; constructor; simpl; eauto using env_app_wf).
Time (intros j).
Time (apply (env_app_disjoint _ _ _ j) in Happ).
Time naive_solver eauto using env_app_fresh.
Time +
Time rewrite (env_app_perm _ _ \206\147s') // big_opL_app.
Time solve_sep_entails.
Time Qed.
Time
Lemma envs_app_singleton_sound \206\148 \206\148' p j Q :
  envs_app p (Esnoc Enil j Q) \206\148 = Some \206\148' \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p Q -\226\136\151 of_envs \206\148'.
Time Proof.
Time move  {}=>/envs_app_sound.
Time (destruct p; by rewrite /= right_id).
Time Qed.
Time
Lemma envs_simple_replace_sound' \206\148 \206\148' i p \206\147 :
  envs_simple_replace i p \206\147 \206\148 = Some \206\148'
  \226\134\146 of_envs (envs_delete true i p \206\148)
    \226\138\162 (if p then \226\150\161 [\226\136\167] \206\147 else [\226\136\151] \206\147) -\226\136\151 of_envs \206\148'.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /envs_simple_replace /envs_delete
 !of_envs_eq =>?).
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>Hwf).
Time (destruct \206\148 as [\206\147p \206\147s], p; simplify_eq /=).
Time -
Time
(destruct (env_app \206\147 \206\147s) eqn:Happ, (env_replace i \206\147 \206\147p) as [\206\147p'| ] eqn:?;
  simplify_eq /=).
Time (apply wand_intro_l, and_intro; [ apply pure_intro |  ]).
Time +
Time (destruct Hwf; constructor; simpl; eauto using env_replace_wf).
Time (intros j).
Time (apply (env_app_disjoint _ _ _ j) in Happ).
Time
(destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh).
Time +
Time rewrite (env_replace_perm _ _ \206\147p') //.
Time rewrite big_opL_app intuitionistically_and and_sep_intuitionistically.
Time solve_sep_entails.
Time -
Time
(destruct (env_app \206\147 \206\147p) eqn:Happ, (env_replace i \206\147 \206\147s) as [\206\147s'| ] eqn:?;
  simplify_eq /=).
Time (apply wand_intro_l, and_intro; [ apply pure_intro |  ]).
Time +
Time (destruct Hwf; constructor; simpl; eauto using env_replace_wf).
Time (intros j).
Time (apply (env_app_disjoint _ _ _ j) in Happ).
Time
(destruct (decide (i = j)); try naive_solver eauto using env_replace_fresh).
Time +
Time rewrite (env_replace_perm _ _ \206\147s') // big_opL_app.
Time solve_sep_entails.
Time Qed.
Time
Lemma envs_simple_replace_singleton_sound' \206\148 \206\148' i 
  p j Q :
  envs_simple_replace i p (Esnoc Enil j Q) \206\148 = Some \206\148'
  \226\134\146 of_envs (envs_delete true i p \206\148) \226\138\162 \226\150\161?p Q -\226\136\151 of_envs \206\148'.
Time Proof.
Time move  {}=>/envs_simple_replace_sound'.
Time (destruct p; by rewrite /= right_id).
Time Qed.
Time
Lemma envs_simple_replace_sound \206\148 \206\148' i p P \206\147 :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 envs_simple_replace i p \206\147 \206\148 = Some \206\148'
    \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p P \226\136\151 ((if p then \226\150\161 [\226\136\167] \206\147 else [\226\136\151] \206\147) -\226\136\151 of_envs \206\148').
Time Proof.
Time (intros).
Time by rewrite envs_lookup_sound // envs_simple_replace_sound' //.
Time Qed.
Time
Lemma envs_simple_replace_maybe_sound \206\148 \206\148' i p P \206\147 :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 envs_simple_replace i p \206\147 \206\148 = Some \206\148'
    \226\134\146 of_envs \206\148
      \226\138\162 \226\150\161?p P
        \226\136\151 ((if p then \226\150\161 [\226\136\167] \206\147 else [\226\136\151] \206\147) -\226\136\151 of_envs \206\148')
          \226\136\167 (\226\150\161?p P -\226\136\151 of_envs \206\148).
Time Proof.
Time (intros).
Time (apply pure_elim with (envs_wf \206\148)).
Time {
Time rewrite of_envs_eq.
Time (apply and_elim_l).
Time }
Time (intros).
Time rewrite {+1}envs_lookup_sound //.
Time (apply sep_mono_r, and_intro).
Time -
Time rewrite envs_simple_replace_sound' //.
Time -
Time (apply wand_intro_l, envs_lookup_sound_2; done).
Time Qed.
Time
Lemma envs_simple_replace_singleton_sound \206\148 \206\148' i p 
  P j Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 envs_simple_replace i p (Esnoc Enil j Q) \206\148 = Some \206\148'
    \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p P \226\136\151 (\226\150\161?p Q -\226\136\151 of_envs \206\148').
Time Proof.
Time (intros).
Time by rewrite envs_lookup_sound // envs_simple_replace_singleton_sound' //.
Time Qed.
Time
Lemma envs_replace_sound' \206\148 \206\148' i p q \206\147 :
  envs_replace i p q \206\147 \206\148 = Some \206\148'
  \226\134\146 of_envs (envs_delete true i p \206\148)
    \226\138\162 (if q then \226\150\161 [\226\136\167] \206\147 else [\226\136\151] \206\147) -\226\136\151 of_envs \206\148'.
Time Proof.
Time (rewrite /envs_replace; destruct (beq _ _) eqn:Hpq).
Time -
Time (apply eqb_prop in Hpq as ->).
Time (apply envs_simple_replace_sound').
Time -
Time (apply envs_app_sound).
Time Qed.
Time
Lemma envs_replace_singleton_sound' \206\148 \206\148' i p q j Q :
  envs_replace i p q (Esnoc Enil j Q) \206\148 = Some \206\148'
  \226\134\146 of_envs (envs_delete true i p \206\148) \226\138\162 \226\150\161?q Q -\226\136\151 of_envs \206\148'.
Time Proof.
Time move  {}=>/envs_replace_sound'.
Time (destruct q; by rewrite /= ?right_id).
Time Qed.
Time
Lemma envs_replace_sound \206\148 \206\148' i p q P \206\147 :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 envs_replace i p q \206\147 \206\148 = Some \206\148'
    \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p P \226\136\151 ((if q then \226\150\161 [\226\136\167] \206\147 else [\226\136\151] \206\147) -\226\136\151 of_envs \206\148').
Time Proof.
Time (intros).
Time by rewrite envs_lookup_sound // envs_replace_sound' //.
Time Qed.
Time
Lemma envs_replace_singleton_sound \206\148 \206\148' i p q P j 
  Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 envs_replace i p q (Esnoc Enil j Q) \206\148 = Some \206\148'
    \226\134\146 of_envs \206\148 \226\138\162 \226\150\161?p P \226\136\151 (\226\150\161?q Q -\226\136\151 of_envs \206\148').
Time Proof.
Time (intros).
Time by rewrite envs_lookup_sound // envs_replace_singleton_sound' //.
Time Qed.
Time
Lemma envs_lookup_envs_clear_spatial \206\148 j :
  envs_lookup j (envs_clear_spatial \206\148) =
  ' '(p, P) \226\134\144 envs_lookup j \206\148; if p : bool then Some (p, P) else None.
Time Proof.
Time rewrite /envs_lookup /envs_clear_spatial.
Time
(destruct \206\148 as [\206\147p \206\147s]; simpl; destruct (\206\147p !! j) eqn:?; simplify_eq /=; auto).
Time by destruct (\206\147s !! j).
Time Qed.
Time
Lemma envs_clear_spatial_sound \206\148 :
  of_envs \206\148 \226\138\162 of_envs (envs_clear_spatial \206\148) \226\136\151 [\226\136\151] env_spatial \206\148.
Time Proof.
Time rewrite !of_envs_eq /envs_clear_spatial /=.
Time (<ssreflect_plugin::ssrtclintros@0> apply pure_elim_l =>Hwf).
Time rewrite right_id -persistent_and_sep_assoc.
Time (apply and_intro; [  | done ]).
Time (apply pure_intro).
Time (destruct Hwf; constructor; simpl; auto using Enil_wf).
Time Qed.
Time
Lemma env_spatial_is_nil_intuitionistically \206\148 :
  env_spatial_is_nil \206\148 = true \226\134\146 of_envs \206\148 \226\138\162 \226\150\161 of_envs \206\148.
Time Proof.
Time (intros).
Time (rewrite !of_envs_eq; destruct \206\148 as [? []]; simplify_eq /=).
Time
rewrite !right_id /bi_intuitionistically {+1}affinely_and_r persistently_and.
Time
by rewrite persistently_affinely_elim persistently_idemp persistently_pure.
Time Qed.
Time
Lemma envs_lookup_envs_delete \206\148 i p P :
  envs_wf \206\148
  \226\134\146 envs_lookup i \206\148 = Some (p, P)
    \226\134\146 envs_lookup i (envs_delete true i p \206\148) = None.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /envs_lookup /envs_delete =>-
 [? ? Hdisj] Hlookup).
Time (destruct \206\148 as [\206\147p \206\147s], p; simplify_eq /=).
Time -
Time rewrite env_lookup_env_delete //.
Time revert Hlookup.
Time (destruct (Hdisj i) as [->| ->]; [  | done ]).
Time by destruct (\206\147s !! _).
Time -
Time rewrite env_lookup_env_delete //.
Time by destruct (\206\147p !! _).
Time Qed.
Time
Lemma envs_lookup_envs_delete_ne \206\148 rp i j p :
  i \226\137\160 j \226\134\146 envs_lookup i (envs_delete rp j p \206\148) = envs_lookup i \206\148.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /envs_lookup /envs_delete =>?).
Time (destruct \206\148 as [\206\147p \206\147s], p; simplify_eq /=).
Time -
Time (<ssreflect_plugin::ssrtclintros@0> destruct rp =>//).
Time by rewrite env_lookup_env_delete_ne.
Time -
Time
(destruct (\206\147p !! i); simplify_eq /=; by rewrite ?env_lookup_env_delete_ne).
Time Qed.
Time
Lemma envs_incr_counter_equiv \206\148 : envs_Forall2 (\226\138\163\226\138\162) \206\148 (envs_incr_counter \206\148).
Time Proof.
Time done.
Time Qed.
Time
Lemma envs_incr_counter_sound \206\148 : of_envs (envs_incr_counter \206\148) \226\138\163\226\138\162 of_envs \206\148.
Time Proof.
Time by f_equiv.
Time Qed.
Time
Lemma envs_split_go_sound js \206\1481 \206\1482 \206\1481' \206\1482' :
  (\226\136\128 j P, envs_lookup j \206\1481 = Some (false, P) \226\134\146 envs_lookup j \206\1482 = None)
  \226\134\146 envs_split_go js \206\1481 \206\1482 = Some (\206\1481', \206\1482')
    \226\134\146 of_envs \206\1481 \226\136\151 of_envs \206\1482 \226\138\162 of_envs \206\1481' \226\136\151 of_envs \206\1482'.
Time Proof.
Time revert \206\1481 \206\1482.
Time
(<ssreflect_plugin::ssrtclintros@0> induction js as [| j js IH] =>\206\1481 \206\1482
  Hlookup H\206\148; simplify_eq /=; [ done |  ]).
Time
(<ssreflect_plugin::ssrtclintros@0> apply pure_elim with (envs_wf \206\1481)
 =>[|Hwf]).
Time {
Time by rewrite !of_envs_eq !and_elim_l sep_elim_l.
Time }
Time
(destruct (envs_lookup_delete _ j \206\1481) as [[[[] P] \206\1481'']| ] eqn:Hdel;
  simplify_eq /=; auto).
Time (apply envs_lookup_delete_Some in Hdel as [? ?]; subst).
Time (rewrite envs_lookup_sound //; rewrite /= (comm _ P) -assoc).
Time (<ssreflect_plugin::ssrtclseq@0> rewrite -(IH _ _ _ H\206\148) ; last  first).
Time {
Time (intros j' P'; destruct (decide (j = j')) as [->| ]).
Time -
Time by rewrite (envs_lookup_envs_delete _ _ _ P).
Time -
Time rewrite envs_lookup_envs_delete_ne // envs_lookup_snoc_ne //.
Time eauto.
Time }
Time (rewrite (envs_snoc_sound \206\1482 false j P) /= ?wand_elim_r; eauto).
Time Qed.
Time
Lemma envs_split_sound \206\148 d js \206\1481 \206\1482 :
  envs_split d js \206\148 = Some (\206\1481, \206\1482) \226\134\146 of_envs \206\148 \226\138\162 of_envs \206\1481 \226\136\151 of_envs \206\1482.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /envs_split =>?).
Time rewrite -(idemp bi_and (of_envs \206\148)).
Time rewrite {+2}envs_clear_spatial_sound.
Time
rewrite (env_spatial_is_nil_intuitionistically (envs_clear_spatial _)) //.
Time rewrite -persistently_and_intuitionistically_sep_l.
Time
rewrite (and_elim_l (<pers> _)%I) persistently_and_intuitionistically_sep_r
 intuitionistically_elim.
Time (destruct (envs_split_go _ _) as [[\206\1481' \206\1482']| ] eqn:H\206\148; [  | done ]).
Time
(<ssreflect_plugin::ssrtclseq@0> apply envs_split_go_sound in H\206\148 as -> ;
 last  first).
Time {
Time (intros j P).
Time
by <ssreflect_plugin::ssrtclintros@0> rewrite envs_lookup_envs_clear_spatial
 =>{+}->.
Time }
Time (destruct d; simplify_eq /=; solve_sep_entails).
Time Qed.
Time Lemma env_to_prop_sound \206\147 : env_to_prop \206\147 \226\138\163\226\138\162 [\226\136\151] \206\147.
Time Proof.
Time
(<ssreflect_plugin::ssrtclseq@0> destruct \206\147 as [| \206\147 ? P]; simpl ; first 
 done).
Time revert P.
Time
(<ssreflect_plugin::ssrtclintros@0> induction \206\147 as [| \206\147 IH ? Q] =>P; simpl).
Time -
Time by rewrite right_id.
Time -
Time rewrite /= IH (comm _ Q _) assoc.
Time done.
Time Qed.
Time End envs.
