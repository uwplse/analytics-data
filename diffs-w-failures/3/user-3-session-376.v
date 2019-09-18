Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqdHPDy2"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 51.
Set Silent.
Require Import Examples.StatDb.Impl.
From Transitions Require Import NonError.
Require Import Spec.Hoare.
Require Import Spec.HoareTactics.
Require Import Spec.AbstractionSpec.
Definition absr :
  relation DB.l.(State) Var.l.(State) unit :=
  fun l res =>
  match res with
  | Val s _ =>
      fst s = fold_right plus 0 l /\
      snd s = length l
  | Err _ _ => False
  end.
Instance absr_non_error : (NonError absr).
Proof.
(compute; auto).
Unset Silent.
Qed.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqoSwlKa"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqrDQQ6t"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Definition init_hspec :
  Specification InitStatus unit Var.State :=
  fun state =>
  {|
  pre := state = (0, 0);
  post := fun state' _ => state' = (0, 0);
  alternate := fun state' (_ : unit) => True |}.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqwoR5dh"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqzgYFfi"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Definition add_hspec n :
  Specification unit unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' (_ : unit) =>
          fst state' = n + fst state /\
          snd state' = S (snd state);
  alternate := fun state' (_ : unit) =>
               state' = (0, 0) |}.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqUi2uZT"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqZ8NfnH"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Printing Width 78.
Definition add_rspec n : Specification unit unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' (_ : unit) =>
          fst state' = n + fst state /\ snd state' = S (snd state);
  alternate := fun state' (_ : unit) => state' = (0, 0) |}.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqjagLzL"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqQWJ5NZ"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Set Silent.
Definition avg_hspec : Specification nat unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v => state = state' /\ v = fst state / snd state';
  alternate := fun state' v => state' = (0, 0) |}.
Definition avg_rspec : Specification nat unit Var.State :=
  fun state =>
  {|
  pre := True;
  post := fun state' v => state = state' /\ v = fst state / snd state';
  alternate := fun state' v => state' = (0, 0) |}.
Definition recover_spec : Specification unit unit Var.State :=
  fun state =>
  {|
  pre := state = (0, 0);
  post := fun state' (_ : unit) => state' = (0, 0);
  alternate := fun state' (_ : unit) => state' = (0, 0) |}.
Lemma read_op_ok :
  forall i,
  proc_hspec Var.dynamics (read i) (op_spec Var.dynamics (Var.Read i)).
Proof.
(intros).
(eapply op_spec_sound).
typeclasses eauto.
typeclasses eauto.
Qed.
Lemma write_op_ok :
  forall i v,
  proc_hspec Var.dynamics (write i v) (op_spec Var.dynamics (Var.Write i v)).
Proof.
(intros).
(eapply op_spec_sound).
typeclasses eauto.
typeclasses eauto.
Qed.
Hint Resolve read_op_ok write_op_ok: core.
Ltac
 simplify :=
  repeat
   match goal with
   | |- forall _, _ => intros
   | _ => deex
   | _ => destruct_tuple
   | _ =>
       destruct_tuple
   | H:reads _ _ _ _ |- _ => unfold reads in H
   | H:puts _ _ _ _ |- _ => unfold puts in H
   | u:unit |- _ => destruct u
   | |- _ /\ _ => split; [ solve [ auto ] |  ]
   | |- _ /\ _ => split; [  | solve [ auto ] ]
   | _ => progress simpl in *
   | _ => progress safe_intuition
   | _ => progress subst
   | _ => progress autorewrite with array in *
   end.
Ltac step := unshelve step_proc; simplify; finish.
Lemma recover_cok : proc_hspec Var.dynamics impl.(recover) recover_spec.
Proof.
(simpl).
(eapply ret_hspec).
-
typeclasses eauto.
-
firstorder.
(inversion H0; subst).
(simpl; auto).
Qed.
Lemma recover_idempotent : idempotent (fun t : unit => recover_spec).
Proof.
(unfold idempotent; intuition; exists tt; simpl in *).
(unfold puts in *; firstorder; congruence).
Qed.
Hint Resolve recover_cok recover_idempotent: core.
Lemma recover_rok :
  proc_rspec Var.dynamics impl.(recover) impl.(recover) recover_spec.
Proof.
(eapply proc_hspec_to_rspec; eauto).
(intros []; eauto).
Qed.
Lemma init_cok : proc_hspec Var.dynamics impl.(init) init_hspec.
Proof.
(eapply ret_hspec).
-
typeclasses eauto.
-
firstorder.
Qed.
Lemma util_and3 (P Q R : Prop) : P -> Q -> R -> P /\ Q /\ R.
Proof.
firstorder.
Qed.
Ltac
 extract_pre H :=
  let P := type of H in
  match eval hnf in P with
  | True => clear H
  | ?v = _ => is_var v; hnf in H; subst
  | ?v = _ /\ _ =>
      is_var v; hnf in H;
       (let Heq := fresh "Heq" in
        destruct H as (Heq, H); subst)
  | _ => idtac
  end.
Lemma crash_step_simp s s' r :
  Var.dynamics.(crash_step) s (Val s' r) -> s' = (0, 0).
Proof.
(compute; inversion 1; auto).
Qed.
Lemma op_step_crash T (op : Var.Op T) u s' r :
  (op_spec Var.dynamics op u).(alternate) s' r -> s' = (0, 0).
Proof.
(intros).
(hnf in H; propositional).
(destruct H0; propositional; eauto using crash_step_simp).
Qed.
Ltac
 extract_crash H :=
  lazymatch type of H with
  | Var.dynamics.(crash_step) _ _ _ =>
      apply crash_step_simp in H; subst
  | (op_spec Var.dynamics _ _).(alternate) _ _ =>
      apply op_step_crash in H; subst
  | _ => idtac
  end.
Ltac
 extract_post :=
  lazymatch goal with
  | |- pre _ => simpl
  | |- alternate _ _ _ => simpl
  | |- post _ _ _ => simpl
  | _ => idtac
  end.
Ltac
 step_bind :=
  eapply proc_hspec_rx; [ solve [ eauto ] | cbn[pre post alternate].. ];
   (let H := fresh "Hpre" in
    intros * H; extract_pre H); apply util_and3; swap 1 2;
   [ intros
   | extract_post
   | let H := fresh "Hcrash" in
     intros * H; extract_crash H; extract_post ].
Ltac
 step_ret :=
  apply ret_hspec; cbn[pre post alternate];
   (let H := fresh "Hpre" in
    intros * H; extract_pre H); apply conj;
   [ extract_post
   | let H := fresh "Hcrash" in
     intros * H; extract_crash H; extract_post ].
Ltac
 newstep :=
  monad_simpl;
   lazymatch goal with
   | |- proc_hspec _ (compile_op _ _) _ => simpl
   | |- proc_hspec _ (Ret _) _ => step_ret
   | |- proc_hspec _ (Bind _ _) _ => step_bind
   end.
Lemma add_cok n :
  proc_hspec Var.dynamics (impl.(compile_op) (DB.Add n)) (add_hspec n).
Proof.
(repeat newstep; auto).
(destruct state0; simpl; auto).
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
Unset Silent.
Set Diffs "off".
Set Printing Width 78.
Show.
(destruct state0; simpl; auto).
Timeout 1 Check @sig.
Unset Silent.
Set Diffs "off".
Timeout 1 Check @denesting.
Timeout 1 Check @step.
Timeout 1 Check @crash_step_refinement.
Timeout 1 Check @crash_step_refinement.
Set Printing Width 78.
Show.
step_ret.
