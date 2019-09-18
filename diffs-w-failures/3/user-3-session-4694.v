Time From iris.bi Require Export bi.
Time From iris.bi Require Import tactics.
Time
From iris.proofmode Require Export base environments classes
  modality_instances.
Time Import bi.
Time Import env_notations.
Time From iris.proofmode Require Import coq_tactics reduction.
Time
From iris.proofmode Require Import base intro_patterns spec_patterns
  sel_patterns.
Time From iris.bi Require Export bi telescopes.
Time From stdpp Require Import namespaces.
Time From iris.proofmode Require Export classes notation tactics.
Time From stdpp Require Import hlist pretty.
Time Require Import CSL.ProofModeClasses.
Time Set Default Proof Using "Type".
Time Export ident.
Time Definition named_def {PROP : bi} (i : ident) (H : PROP) : PROP := H.
Time Definition named_aux {PROP : bi} : seal (@named_def PROP).
Time by eexists.
Time Qed.
Time Definition named {PROP : bi} := (@named_aux PROP).(unseal).
Time
Definition named_eq {PROP : bi} : @named PROP = @named_def PROP :=
  (@named_aux PROP).(seal_eq).
Time #[global]
Instance named_persistent  {PROP : bi} i (P : PROP):
 (Persistent P \226\134\146 Persistent (named i P)).
Time Proof.
Time rewrite named_eq /named_def //=.
Time Qed.
Time #[global]
Instance named_affine  {PROP : sbi} i (P : PROP):
 (Affine P \226\134\146 Affine (named i P)).
Time Proof.
Time rewrite named_eq /named_def //=.
Time Qed.
Time #[global]
Instance named_timeless  {PROP : sbi} i (P : PROP):
 (Timeless P \226\134\146 Timeless (named i P)).
Time Proof.
Time rewrite named_eq /named_def //=.
Time Qed.
Time #[global]
Instance named_absorbing  {PROP : bi} i (P : PROP):
 (Absorbing P \226\134\146 Absorbing (named i P)).
Time Proof.
Time rewrite named_eq /named_def //=.
Time Qed.
Time #[global]
Instance named_frame_here :
 (\226\136\128 (PROP : bi) i (p : bool) (R : PROP), Frame p (named i R) R emp) |100.
Time Proof.
Time (intros ? ? ?).
Time rewrite named_eq /named_def //= //=.
Time (apply _).
Time Qed.
Time
Fixpoint env_bundle_names {PROP : bi} (\206\147 : env PROP) : 
env PROP :=
  match \206\147 with
  | Enil => Enil
  | Esnoc \206\147 j x => Esnoc (env_bundle_names \206\147) j (named j x)
  end.
Time
Definition envs_bundle_names {PROP : bi} (\206\148 : envs PROP) : 
  envs PROP := let (\206\147p, \206\147s, n) := \206\148 in Envs \206\147p (env_bundle_names \206\147s) n.
Time
Lemma envs_bundle_names_sound {PROP : bi} (\206\148 : envs PROP) :
  envs_bundle_names \206\148 = \206\148.
Time Proof.
Time (destruct \206\148 as (\206\147p, \206\147s, p)).
Time rewrite /envs_bundle_names.
Time f_equal.
Time (induction \206\147s; rewrite //= named_eq /named_def IH\206\147s //=).
Time Qed.
Time
Lemma tac_bundle_names {PROP : bi} (\206\148 : envs PROP) 
  Q : envs_entails (envs_bundle_names \206\148) Q \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time by rewrite envs_entails_eq envs_bundle_names_sound.
Time Qed.
Time
Ltac
 bundle_names :=
  eapply tac_bundle_names;
   match goal with
   | |- ?u =>
         let v := eval cbv[envs_bundle_names env_bundle_names] in u in
         change_no_check v
   end.
Time
Ltac
 unbundle_names :=
  rewrite ?named_eq;
   match goal with
   | |- ?u => let v := eval cbv[named_def] in u in
              change_no_check v
   end.
Time
Ltac
 iAssignNames :=
  repeat
   match goal with
   | |- context [ environments.Esnoc _ (IAnon ?x) (named ?i _) ] => iRename
     IAnon x into i
   end; unbundle_names.
Time Tactic Notation "iNamedAux" tactic1(tac) := (bundle_names; tac).
Time Tactic Notation "iNamed" tactic1(tac) := (iNamedAux tac; iAssignNames).
Time
Ltac
 iDestructRep H :=
  let H1 := iFresh in
  let H2 := iFresh in
  let pat := constr:(IList [cons (IIdent H1) (cons (IIdent H2) nil)]) in
  iDestruct H as pat; try iDestructRep H1; try iDestructRep H2;
   try iDestruct H1 as "%"; try iDestruct H2 as "%".
Time
Ltac
 iDestructExRep H :=
  try
   (let H1 := iFresh in
    let H2 := iFresh in
    let pat := constr:(IList [cons (IIdent H1) (cons (IIdent H2) nil)]) in
    first
    [ (iDestruct H as ( ? ) H; iDestructExRep H) || iDestruct H as pat;
       iDestructExRep H1; iDestructExRep H2; try iDestruct H1 as "%";
       try iDestruct H2 as "%" ]).
Time
Ltac
 iDestructRepR H :=
  let H2 := iFresh in
  let pat := constr:(IList [cons IFresh (cons (IIdent H2) nil)]) in
  iDestruct H as pat; try iDestructRepR H2.
Time
Ltac
 iDestructIntro :=
  let H := iFresh in
  iIntros H; iDestructExRep H; iAssignNames.
Time Inductive LTag : Set :=
       | LNamed : string \226\134\146 LTag
       | LAnon : LTag.
Time Coercion LNamed : string >-> LTag.
Time Definition tagged_prop (PROP : bi) := (LTag * PROP)%type.
Time
Definition tagged_to_prop {PROP} (tP : tagged_prop PROP) : PROP :=
  match tP with
  | (LNamed s, P) => named s P
  | (LAnon, P) => P
  end.
Time Definition prop_list (PROP : bi) := list (tagged_prop PROP).
Time
Definition pl2p {PROP : bi} (Ps : prop_list PROP) : 
  list PROP := map tagged_to_prop Ps.
Time Definition pl2pp {PROP : bi} (Ps : prop_list PROP) := ([\226\136\151] pl2p Ps)%I.
Time
Class IntoSepEnv {PROP : bi} (P : PROP) (Ps : prop_list PROP) :=
    into_sep_env : P \226\138\162 [\226\136\151] pl2p Ps.
Time Arguments IntoSepEnv {_} _%I _%I : simpl never.
Time Arguments into_sep_env {_} _%I _%I {_}.
Time Hint Mode IntoSepEnv + ! -: typeclass_instances.
Time
Class IntoAndEnv {PROP : bi} (p : bool) (P : PROP) (Ps : prop_list PROP) :=
    into_and_env : \226\150\161?p P \226\138\162 \226\150\161?p [\226\136\167] pl2p Ps.
Time Arguments IntoAndEnv {_} _ _%I _%I : simpl never.
Time Arguments into_and_env {_} _ _%I _%I {_}.
Time Hint Mode IntoAndEnv + + ! -: typeclass_instances.
Time
Class FrameSepEnv {PROP : bi} (\206\148 \206\148' : envs PROP) (P Q : PROP) :=
    frame_env : \226\136\131 R, (of_envs \206\148 \226\138\162 R \226\136\151 of_envs \206\148') \226\136\167 (R -\226\136\151 Q -\226\136\151 P).
Time Arguments FrameSepEnv {_} _%I _%I _%I _%I.
Time Arguments frame_env {_} _%I _%I _%I _%I {_}.
Time Hint Mode FrameSepEnv + + - + -: typeclass_instances.
Time
Definition envs_set_counter {PROP} (\206\148 : envs PROP) 
  (p : positive) : envs PROP := Envs (env_intuitionistic \206\148) (env_spatial \206\148) p.
Time
Lemma envs_set_counter_equiv {PROP} (\206\148 : envs PROP) 
  p : envs_Forall2 (\226\138\163\226\138\162) \206\148 (envs_set_counter \206\148 p).
Time Proof.
Time done.
Time Qed.
Time
Lemma envs_set_counter_sound {PROP} (\206\148 : envs PROP) 
  p : of_envs (envs_set_counter \206\148 p) \226\138\163\226\138\162 of_envs \206\148.
Time Proof.
Time by f_equiv.
Time Qed.
Time Section list_destruct.
Time Context {PROP : bi}.
Time
Fixpoint pl_env_expand (p : positive) (Ps : prop_list PROP) 
(\206\147 : env PROP) : positive * env PROP :=
  match Ps with
  | nil => (p, \206\147)
  | (LAnon, P) :: Ps' => pl_env_expand (Pos_succ p) Ps' (Esnoc \206\147 (IAnon p) P)
  | (LNamed s, P) :: Ps' => pl_env_expand p Ps' (Esnoc \206\147 s P)
  end.
Time #[global]
Instance env_into_sep_env  (Ps : prop_list PROP):
 (IntoSepEnv ([\226\136\151] pl2p Ps) Ps).
Time Proof.
Time rewrite /IntoSepEnv.
Time trivial.
Time Qed.
Time #[global]
Instance positive_into_and_sep :
 (BiPositive PROP
  \226\134\146 \226\136\128 (P : PROP) (Ps : prop_list PROP),
      IntoSepEnv P Ps \226\134\146 IntoAndEnv true P Ps).
Time Proof.
Time (intros HPOS P Ps).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /IntoSepEnv /IntoAndEnv =>{+}->).
Time (simpl).
Time (<ssreflect_plugin::ssrtclintros@0> induction Ps =>//=; auto).
Time rewrite intuitionistically_sep intuitionistically_and.
Time iIntros "(?&?)".
Time iFrame.
Time by iApply IHPs.
Time Qed.
Time #[global]
Instance sep_into_sep_single_named  (i : string) (P : PROP):
 (IntoSepEnv (named i P) [(LNamed i, P)]).
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iFrame.
Time eauto.
Time Qed.
Time #[global]
Instance sep_into_sep_cons  (i : string) (P Q : PROP) 
 Ps: (IntoSepEnv Q Ps \226\134\146 IntoSepEnv (named i P \226\136\151 Q) ((LNamed i, P) :: Ps)).
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iIntros ( H1 ) "(?&?)".
Time iFrame.
Time by iApply H1.
Time Qed.
Time #[global]
Instance sep_into_sep_single_anon  (P : PROP): (IntoSepEnv P [(LAnon, P)])
 |100.
Time Proof.
Time rewrite /IntoSepEnv //=.
Time iFrame.
Time eauto.
Time Qed.
Time Implicit Types P Q R : PROP.
Time #[global]
Instance frame_env_here_absorbing  \206\148 \206\148' i (R : PROP):
 (Absorbing R
  \226\134\146 envs_lookup_delete false i \206\148 = Some (false, R, \206\148')
    \226\134\146 FrameSepEnv \206\148 \206\148' (named i R) True) |0.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FrameSepEnv =>? Hsound).
Time (exists R; split).
Time *
Time (rewrite envs_lookup_delete_sound //=; simpl; auto).
Time *
Time iIntros "??".
Time rewrite named_eq.
Time iFrame.
Time Qed.
Time #[global]
Instance frame_env_here  \206\148 \206\148' i (R : PROP):
 (envs_lookup_delete false i \206\148 = Some (false, R, \206\148')
  \226\134\146 FrameSepEnv \206\148 \206\148' (named i R) emp) |1.
Time Proof.
Time (<ssreflect_plugin::ssrtclintros@0> rewrite /FrameSepEnv =>Hsound).
Time (exists R; split).
Time *
Time (rewrite envs_lookup_delete_sound //=; simpl; auto).
Time *
Time iIntros "??".
Time rewrite named_eq.
Time iFrame.
Time Qed.
Time #[global]
Instance frame_env_sep  \206\148 \206\148' \206\148'' P1 P2 Q1 Q2:
 (FrameSepEnv \206\148 \206\148' P1 Q1
  \226\134\146 FrameSepEnv \206\148' \206\148'' P2 Q2 \226\134\146 FrameSepEnv \206\148 \206\148'' (P1 \226\136\151 P2) (Q1 \226\136\151 Q2)).
Time Proof.
Time rewrite /FrameSepEnv.
Time (intros (R1, (HR1, HR1'))).
Time (intros (R2, (HR2, HR2'))).
Time exists (R1 \226\136\151 R2)%I.
Time split.
Time -
Time rewrite HR1 HR2.
Time by rewrite assoc.
Time -
Time rewrite HR1' HR2'.
Time iIntros "(Hw1&Hw2) (H1&H2)".
Time iSplitL "Hw1 H1".
Time *
Time by iApply "Hw1".
Time *
Time by iApply "Hw2".
Time Qed.
Time #[global]Instance frame_env_sep_miss  \206\148 P: (FrameSepEnv \206\148 \206\148 P P) |100.
Time Proof.
Time rewrite /FrameSepEnv.
Time exists emp%I.
Time (split; eauto).
Time Qed.
Time
Lemma tac_frame_env \206\148 \206\148' P Q :
  FrameSepEnv \206\148 \206\148' P Q \226\134\146 envs_entails \206\148' Q \226\134\146 envs_entails \206\148 P.
Time Proof.
Time rewrite /FrameSepEnv.
Time (intros (R, (HR, HR'))).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq HR HR' =>{+}->).
Time (apply wand_elim_l).
Time Qed.
Time
Lemma tac_sep_list_destruct \206\148 \206\148' i p \206\147 bump (P : PROP) 
  (Ps : prop_list PROP) Q :
  envs_lookup i \206\148 = Some (p, P)
  \226\134\146 (if p then IntoAndEnv true P Ps else IntoSepEnv P Ps)
    \226\134\146 pl_env_expand (env_counter \206\148) Ps Enil = (bump, \206\147)
      \226\134\146 envs_simple_replace i p \206\147 \206\148 = Some \206\148'
        \226\134\146 envs_entails (envs_set_counter \206\148' bump) Q \226\134\146 envs_entails \206\148 Q.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_entails_eq =>Hlookup Hsep
 Hexpand Hrepl Himpl).
Time rewrite envs_simple_replace_sound //=.
Time
(assert
  (Hrec1 :
   \226\136\128 p (\206\147 : env PROP),
     ([\226\136\151] \206\147 -\226\136\151 [\226\136\151] pl2p Ps -\226\136\151 [\226\136\151] snd (pl_env_expand p Ps \206\147))%I)).
Time {
Time clear.
Time (<ssreflect_plugin::ssrtclintros@0> induction Ps =>//= p \206\147).
Time *
Time (iIntros "H"; eauto).
Time *
Time iIntros "H1 (a&H2)".
Time (destruct a as ([], ?); simpl; iApply (IHPs with "[a H1] H2"); iFrame).
Time }
Time
(assert
  (Hrec2 :
   \226\136\128 p (\206\147 : env PROP),
     (\226\150\161 [\226\136\167] \206\147 -\226\136\151 \226\150\161 [\226\136\167] pl2p Ps -\226\136\151 \226\150\161 [\226\136\167] snd (pl_env_expand p Ps \206\147))%I)).
Time {
Time clear.
Time (<ssreflect_plugin::ssrtclintros@0> induction Ps =>//= p \206\147).
Time *
Time (iIntros "H"; eauto).
Time *
Time iIntros "#H1 #(a&H2)".
Time
(destruct a as ([], ?); simpl; iApply (IHPs with "[a H1] H2"); iFrame; simpl;
  iApply intuitionistically_and; iSplit; simpl; iFrame "#").
Time }
Time specialize (Hrec1 (env_counter \206\148) Enil).
Time rewrite Hexpand in  {} Hrec1.
Time specialize (Hrec2 (env_counter \206\148) Enil).
Time rewrite Hexpand in  {} Hrec2.
Time (destruct p).
Time -
Time rewrite (into_and_env true P).
Time (simpl).
Time iIntros "(Hps&Hwand)".
Time iPoseProof (Hrec2 with "[ ] [$]") as "HPs'".
Time (simpl; iAlways; trivial).
Time (simpl).
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_set_counter_sound in 
 {} Himpl * =>{+}->).
Time by iApply "Hwand".
Time -
Time rewrite (into_sep_env P).
Time (simpl).
Time iIntros "(Hps&Hwand)".
Time iPoseProof (Hrec1 with "[$] [$]") as "HPs'".
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite envs_set_counter_sound in 
 {} Himpl * =>{+}->).
Time by iApply "Hwand".
Time Qed.
Time End list_destruct.
Time
Ltac
 set_counter_reduce :=
  match goal with
  | |- ?u => let v := eval cbv[envs_set_counter] in u in
             change_no_check v
  end.
Time
Ltac
 iLDestructEx H :=
  match goal with
  | |- context [ environments.Esnoc _ (INamed H) (bi_exist (fun x => _))%I ]
    => iDestruct H as ( x ) H
  | |- context [ environments.Esnoc _ H (bi_exist (fun x => _))%I ] =>
        iDestruct H as ( x ) H
  end.
Time
Ltac
 iLDestructCore H :=
  eapply (tac_sep_list_destruct _ _ H);
   [ pm_reflexivity ||
       (let H := pretty_ident H in
        fail "iLDestruct:" H "not found")
   | apply _
   | pm_reflexivity || fail "iLDestruct: some name not fresh"
   | pm_reflexivity || fail "iLDestruct: some name not fresh"
   | set_counter_reduce; pm_reduce ].
Time
Ltac
 iLDestruct H := repeat try iLDestructEx H; iLDestructCore H; iDestructPure.
Time Ltac iLIntro := let H := iFresh in
                     iIntros H; iLDestruct H.
Time
Ltac
 iLIntroP :=
  let H := iFresh in
  let pat := constr:(IAlwaysElim (IIdent H)) in
  iIntros H; iLDestruct H.
Time Section test.
Time Context {PROP : bi}.
Time Context {Hpos : BiPositive PROP}.
Time Context {P P' : nat \226\134\146 PROP}.
Time Context (HPP' : \226\136\128 n, P n \226\138\162 P' n).
Time Definition test_list := pl2p [(LNamed "Hfoo", P O); (LAnon, P' O)].
Time
Fixpoint bigterm_list (P : nat \226\134\146 PROP) s n :=
  match n with
  | O => []
  | S n' => (LNamed s, P (S n')) :: bigterm_list P (String "a" s) n'
  end.
Time Lemma Hex_destruct : (\226\136\131 foo : nat, named "bar" True) \226\138\162 True : PROP.
Time Proof.
Time iIntros "H".
Time (iLDestruct "H").
Time auto.
Time Qed.
Time
Lemma Hpers_ldestruct :
  (\226\136\131 foo : nat, named "bar" (\226\150\161 emp) \226\136\151 named "foo" (\226\150\161 emp)%I) \226\138\162 True : PROP.
Time Proof  using (Hpos).
Time iIntros "#H".
Time (iLDestruct "H").
Time auto.
Time Qed.
Time
Lemma Hpers_intro_ldestruct :
  (\226\136\131 foo : nat, named "bar" (\226\150\161 emp) \226\136\151 named "foo" (\226\150\161 emp)%I) \226\138\162 True : PROP.
Time Proof  using (Hpos).
Time iLIntroP.
Time auto.
Time Qed.
Time
Lemma HPP_destruct_named :
  True \226\136\151 [\226\136\151] test_list \226\136\151 True \226\138\162 P O -\226\136\151 P O -\226\136\151 P O -\226\136\151 P O -\226\136\151 [\226\136\151] test_list.
Time Proof.
Time iIntros "(?&H0&H1)".
Time (iLDestruct "H0").
Time Abort.
Time
Lemma HPP_intro_named :
  [\226\136\151] test_list \226\138\162 P O -\226\136\151 P O -\226\136\151 P O -\226\136\151 P O -\226\136\151 [\226\136\151] test_list.
Time Proof.
Time iLIntro.
Time Abort.
Time Lemma Hbig : [\226\136\151] pl2p (bigterm_list P "a" 20) \226\138\162 True.
Time Proof.
Time iLIntro.
Time auto.
Time Qed.
Time
Lemma test_pure Q :
  named "HQ" Q \226\136\151 named "?" \226\140\156(2 + 2 = 4)%nat\226\140\157 \226\136\151 named "HQ2" Q \226\138\162 True : PROP.
Time Proof.
Time iLIntro.
Time auto.
Time Qed.
Time
Lemma Hbig_combined :
  [\226\136\151] pl2p (bigterm_list P "a" 20)
  -\226\136\151 [\226\136\151] pl2p (bigterm_list P "b" 20) -\226\136\151 True.
Time Proof.
Time iLIntro.
Time iLIntro.
Time auto.
Time Qed.
Time
Hint Extern 10 (envs_lookup_delete _ _ _ = Some _) => (
  compute; reflexivity): typeclass_instances.
Time End test.
Time
Hint Extern 10 (envs_lookup_delete _ _ _ = Some _) => (
  compute; reflexivity): typeclass_instances.
