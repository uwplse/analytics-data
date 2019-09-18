From RecoveryRefinement Require Import Lib.
Require Import Spec.HoareTactics.
Require Import Examples.Logging.Impl.
Require Import Examples.Logging.LogLayout.
Require Import Examples.Logging.LogicalLog.
#[local]Notation proc_rspec := (Hoare.proc_rspec D.ODLayer.(sem)).
#[local]Arguments Hoare.proc_rspec {Op} {State} sem {T} {R}.
Definition logical_abstraction (d : D.State) ps ls :=
  PhyDecode d ps /\ LogDecode ps ls /\ ls.(ls_committed) = false.
#[local]Hint Resolve recovery_ok: core.
#[local]Hint Resolve log_apply_spec_idempotent_notxn': core.
#[local]Hint Resolve log_apply_spec_idempotent': core.
Definition general_rspec ls0 T (p_hspec : Specification T unit D.State) :=
  proc_hspec_to_rspec (sem:=D.ODLayer.(sem)) (p_hspec:=p_hspec)
    (rec_hspec:=fun
                  a : Recghost
                        (fun ls =>
                         if ls.(ls_committed)
                         then
                          massign ls.(ls_log) ls.(ls_disk) =
                          massign ls0.(ls_log) ls0.(ls_disk)
                         else
                          ls.(ls_disk) = ls0.(ls_disk) \/
                          ls.(ls_disk) = massign ls0.(ls_log) ls0.(ls_disk))
                =>
                let
                'recghost ps ls _ := a in
                 log_apply_spec ps ls ls.(ls_disk) ls.(ls_committed)).
Definition mk_rspec ls0 T (p_hspec : Specification T unit D.State) :=
  proc_hspec_to_rspec (sem:=D.ODLayer.(sem)) (p_hspec:=p_hspec)
    (rec_hspec:=fun a : Recghost (fun ls => ls.(ls_disk) = ls0.(ls_disk)) =>
                let
                'recghost ps ls _ := a in
                 log_apply_spec ps ls ls.(ls_disk) false).
#[local]Hint Resolve log_read_ok: core.
Theorem log_read_rec_ok ps ls a :
  proc_rspec (log_read a) recovery
    (fun state =>
     {|
     pre := logical_abstraction state ps ls;
     post := fun state' r => state' = state /\ index ls.(ls_disk) a ?|= eq r;
     alternate := fun state' r =>
                  exists ps',
                    logical_abstraction state' ps'
                      {|
                      ls_committed := false;
                      ls_log := nil;
                      ls_disk := ls.(ls_disk) |} |}).
Proof.
(eapply mk_rspec; eauto; simpl in *; propositional;
  repeat match goal with
         | x:Recghost _ |- _ => destruct x
         end; eauto).
-
(eexists (recghost _ _ _); simpl; intuition eauto).
-
(simpl in H0; propositional).
(unfold logical_abstraction).
(descend; intuition eauto).
(rewrite <- pf).
eassumption.
Grab Existential Variables.
(simpl; auto).
Qed.
#[local]Hint Resolve log_write_ok: core.
Theorem log_write_rec_ok ps ls a v :
  proc_rspec (log_write a v) recovery
    (fun state =>
     {|
     pre := logical_abstraction state ps ls;
     post := fun state' r =>
             exists ps',
               match r with
               | TxnD.WriteOK =>
                   logical_abstraction state' ps'
                     {|
                     ls_committed := false;
                     ls_log := ls.(ls_log) ++ (a, v) :: nil;
                     ls_disk := ls.(ls_disk) |}
               | TxnD.WriteErr =>
                   logical_abstraction state' ps'
                     {|
                     ls_committed := false;
                     ls_log := ls.(ls_log);
                     ls_disk := ls.(ls_disk) |}
               end;
     alternate := fun state' r =>
                  exists ps',
                    logical_abstraction state' ps'
                      {|
                      ls_committed := false;
                      ls_log := nil;
                      ls_disk := ls.(ls_disk) |} |}).
Proof.
(eapply mk_rspec; eauto; simpl in *; propositional;
  repeat match goal with
         | x:Recghost _ |- _ => destruct x
         end; eauto).
-
(unfold logical_abstraction in *; intuition eauto).
(destruct v0; propositional; descend; intuition eauto).
(destruct ls; simpl in *; congruence).
-
(inv_clear H1).
(eexists (recghost _ _ _); simpl; intuition eauto).
-
(simpl in H0; propositional).
(unfold logical_abstraction).
(descend; intuition eauto).
(rewrite <- pf; eassumption).
Grab Existential Variables.
(simpl; auto).
Qed.
#[local]Hint Resolve log_commit_ok: core.
Theorem log_commit_rec_ok ps ls :
  proc_rspec commit recovery
    (fun state =>
     {|
     pre := logical_abstraction state ps ls;
     post := fun state' r =>
             exists ps',
               logical_abstraction state' ps'
                 {|
                 ls_committed := false;
                 ls_log := nil;
                 ls_disk := massign ls.(ls_log) ls.(ls_disk) |};
     alternate := fun state' r =>
                  exists ps',
                    logical_abstraction state' ps'
                      {|
                      ls_committed := false;
                      ls_log := nil;
                      ls_disk := ls.(ls_disk) |} \/
                    logical_abstraction state' ps'
                      {|
                      ls_committed := false;
                      ls_log := nil;
                      ls_disk := massign ls.(ls_log) ls.(ls_disk) |} |}).
Proof.
(eapply general_rspec; eauto; simpl; propositional).
-
(destruct a; eauto).
-
(unfold logical_abstraction in *; intuition eauto).
propositional.
(descend; intuition eauto).
(destruct ls'; simpl in *; congruence).
-
(split_cases;
  lazymatch goal with
  | H:PhyDecode state' ?ps, H':LogDecode ?ps ?ls
    |- _ => unshelve eexists (recghost ps ls _); simpl; eauto
  end).
-
(destruct a; simpl in *; propositional).
exists ps'.
(destruct_with_eqn ls0.(ls_committed); unfold logical_abstraction in *; simpl;
  propositional).
+
(right; split_cases; finish).
+
split_cases.
(left; split_cases; finish).
(right; split_cases; finish).
Qed.
#[local]Hint Resolve log_size_ok: core.
Theorem log_size_rec_ok ps ls :
  proc_rspec log_size recovery
    (fun state =>
     {|
     pre := logical_abstraction state ps ls;
     post := fun state' r => r = length ls.(ls_disk) /\ state' = state;
     alternate := fun state' r =>
                  exists ps',
                    logical_abstraction state' ps'
                      {|
                      ls_committed := false;
                      ls_log := nil;
                      ls_disk := ls.(ls_disk) |} |}).
Proof.
(eapply mk_rspec; eauto; simpl in *; propositional;
  repeat match goal with
         | x:Recghost _ |- _ => destruct x
         end; eauto).
-
(eexists (recghost _ _ _); simpl; intuition eauto).
-
(simpl in H0; propositional).
(unfold logical_abstraction).
(descend; intuition eauto).
(rewrite <- pf; eassumption).
Grab Existential Variables.
(simpl; auto).
Qed.
#[local]Hint Resolve recovery_ok: core.
Theorem recovery_rec_ok ps ls :
  proc_rspec recovery recovery
    (fun state =>
     {|
     pre := logical_abstraction state ps ls;
     post := fun state' _ =>
             exists ps,
               logical_abstraction state' ps
                 {|
                 ls_committed := false;
                 ls_log := nil;
                 ls_disk := ls.(ls_disk) |};
     alternate := fun state' _ =>
                  exists ps,
                    logical_abstraction state' ps
                      {|
                      ls_committed := false;
                      ls_log := nil;
                      ls_disk := ls.(ls_disk) |} |}).
Proof.
(eapply mk_rspec; simpl; intros;
  repeat match goal with
         | x:Recghost _ |- _ => destruct x
         end).
-
(eapply (recovery_ok ps ls false)).
-
(unfold logical_abstraction in *; simplify; intuition eauto).
-
eauto.
-
(simpl; unfold logical_abstraction in *; simplify; intuition eauto).
-
(simpl in *; propositional).
(lazymatch goal with
 | H:PhyDecode state' ?ps, H':LogDecode ?ps ?ls
   |- _ => unshelve eexists (recghost ps ls _); simpl; eauto
 end).
-
(unfold logical_abstraction; simpl in *; propositional).
(exists ps'; intuition eauto).
congruence.
Qed.
Definition abstraction (txnd : TxnD.State) (d : D.State) 
  (u : unit) : Prop :=
  exists ps ls,
    logical_abstraction d ps ls /\
    txnd = (ls.(ls_disk), massign ls.(ls_log) ls.(ls_disk)).
Notation proc_refines p spec:=
  (forall txnd, proc_rspec p recovery (refine_spec abstraction spec txnd))
  (only parsing).
Ltac
 rspec_impl :=
  eapply proc_rspec_impl; [ unfold spec_impl | solve [ eauto ] ]; simpl;
   propositional.
#[local]Hint Resolve log_read_rec_ok: core.
Ltac
 destruct_txnd :=
  let t H :=
   let d_old := fresh "d_old" in
   let d := fresh "d" in
   destruct H as [d_old d]
  in
  repeat
   match goal with
   | H:TxnD.State |- _ => t H
   | H:TxnD.l.(State) |- _ => t H
   end.
Theorem log_read_abs_ok a :
  proc_refines (log_read a)
    (fun '(d_old, d) =>
     {|
     pre := True;
     post := fun '(d_old', d') r =>
             d_old' = d_old /\ d' = d /\ index d_old a ?|= eq r;
     alternate := fun '(d_old', d') _ => d_old' = d_old /\ d' = d_old |}).
Proof.
(unfold refine_spec, abstraction; intros; destruct_txnd; intros).
(spec_intros; simpl in *; simplify).
(rspec_impl; intuition eauto; simplify).
-
(eexists (_, _); intuition eauto).
-
(eexists (_, _); intuition eauto).
Qed.
#[local]Hint Resolve log_write_rec_ok: core.
Theorem log_write_abs_ok a v :
  proc_refines (log_write a v)
    (fun '(d_old, d) =>
     {|
     pre := True;
     post := fun '(d_old', d') r =>
             d_old' = d_old /\
             match r with
             | TxnD.WriteOK => d' = assign d a v
             | TxnD.WriteErr => d' = d
             end;
     alternate := fun '(d_old', d') _ => d_old' = d_old /\ d' = d_old |}).
Proof.
(unfold refine_spec, abstraction; intros; destruct_txnd; intros).
(spec_intros; simpl in *; simplify).
(rspec_impl; intuition eauto; simplify).
(destruct v0).
-
(eexists (_, _); intuition eauto; simpl).
array.
-
(eexists (_, _); intuition eauto; simpl).
-
(eexists (_, _); intuition eauto; simpl).
Qed.
#[local]Hint Resolve log_size_rec_ok: core.
Theorem log_size_abs_ok :
  proc_refines log_size
    (fun '(d_old, d) =>
     {|
     pre := True;
     post := fun '(d_old', d') r => d_old' = d_old /\ d' = d /\ r = length d;
     alternate := fun '(d_old', d') _ => d_old' = d_old /\ d' = d_old |}).
Proof.
(unfold refine_spec, abstraction; intros; destruct_txnd; intros).
(spec_intros; simpl in *; simplify).
(rspec_impl; intuition eauto; simplify).
-
(eexists (_, _); intuition eauto).
array.
-
(eexists (_, _); intuition eauto).
Qed.
#[local]Hint Resolve log_commit_rec_ok: core.
Theorem log_commit_abs_ok :
  proc_refines commit
    (fun '(d_old, d) =>
     {|
     pre := True;
     post := fun '(d_old', d') r => r = tt /\ d_old' = d /\ d' = d;
     alternate := fun '(d_old', d') _ =>
                  d_old' = d_old /\ d' = d_old \/ d_old' = d /\ d' = d |}).
Proof.
(unfold refine_spec, abstraction; intros; destruct_txnd; intros).
(spec_intros; simpl in *; simplify).
(rspec_impl; intuition eauto; simplify; split_cases).
-
(eexists (_, _); intuition eauto).
-
(eexists (_, _); intuition eauto).
-
(eexists (_, _); intuition eauto).
Qed.
#[local]Hint Resolve recovery_rec_ok: core.
Theorem recovery_abs_ok :
  proc_refines recovery
    (fun '(d_old, d) =>
     {|
     pre := True;
     post := fun '(d_old', d') r => r = tt /\ d_old' = d_old /\ d' = d_old;
     alternate := fun '(d_old', d') _ => d_old' = d_old /\ d' = d_old |}).
Proof.
(unfold refine_spec, abstraction; intros; destruct_txnd; intros).
(spec_intros; simpl in *; simplify).
(rspec_impl; intuition eauto; simplify).
-
(eexists (_, _); intuition eauto).
-
(eexists (_, _); intuition eauto).
Qed.
Module LoggingRefinement.
Definition Impl : LayerImpl D.Op TxnD.Op :=
  {|
  compile_op := fun (T : Type) (op : TxnD.Op T) =>
                match op with
                | TxnD.op_read a => log_read a
                | TxnD.op_write a b => log_write a b
                | TxnD.op_commit => commit
                | TxnD.op_size => log_size
                end;
  init := log_init;
  Layer.recover := recovery |}.
Lemma l_compile_refines :
  compile_op_refines_step D.ODLayer TxnD.l Impl abstraction.
Proof.
(unfold compile_op_refines_step; intros).
(destruct op; cbn[Impl compile_op recover]).
-
(eapply proc_rspec_crash_refines_op; intros; eauto using log_commit_abs_ok;
  destruct_txnd; simpl in *; simplify; finish).
constructor.
(split_cases; eauto).
right.
(exists (d0, d0),tt; simpl).
eauto using TxnD.op_step.
-
(eapply proc_rspec_crash_refines_op; intros; eauto using log_read_abs_ok;
  destruct_txnd; simpl in *; simplify; finish).
constructor.
(destruct_with_eqn index d_old0 a; simpl in *; eauto).
-
(eapply proc_rspec_crash_refines_op; intros; eauto using log_write_abs_ok;
  destruct_txnd; simpl in *; simplify; finish).
(destruct v; subst; constructor; auto).
-
(eapply proc_rspec_crash_refines_op; intros; eauto using log_size_abs_ok;
  destruct_txnd; simpl in *; simplify; finish).
constructor.
Qed.
Lemma l_recovery_refines_crash :
  recovery_refines_crash_step D.ODLayer TxnD.l Impl abstraction.
Proof.
(unfold recovery_refines_crash_step).
(eapply proc_rspec_recovery_refines_crash_step).
-
(intros; eapply recovery_abs_ok).
-
(intros; destruct_txnd; simpl in *).
(inv_clear H0; intuition eauto; simpl; eauto).
-
(intros; destruct_txnd; simpl in *).
(inv_clear H0).
(split_cases; destruct_txnd; propositional).
(eexists (_, _); simpl; eauto).
Qed.
Import RelationNotations.
Lemma l_init_ok :
  _ <- test D.ODLayer.(initP); exec D.ODLayer Impl.(init)
  --->
   (_ <- any (T:=unit);
    _ <- test TxnD.l.(initP); _ <- abstraction; pure Initialized) +
   (_ <- any (T:=unit); pure InitFailed).
Proof.
(eapply proc_hspec_init_ok; unfold abstraction).
+
(eapply log_init_ok).
+
simplify.
+
simplify.
(eexists (ls.(ls_disk), ls.(ls_disk)); simpl; intuition eauto).
(unfold logical_abstraction; descend; intuition eauto).
f_equal.
(rewrite H2; simpl; auto).
Qed.
Lemma rf : LayerRefinement D.ODLayer TxnD.l.
Proof.
unshelve econstructor.
-
exact Impl.
-
exact abstraction.
-
exact l_compile_refines.
-
exact l_recovery_refines_crash.
-
exact l_init_ok.
Defined.
End LoggingRefinement.
