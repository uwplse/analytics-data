Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqkzZ4S1"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Relations.Relation_Operators.
Require Import RelationClasses.
Require Import Helpers.Helpers.
Require Import Proc.
Ltac inv_exec' H := inversion H; subst; clear H; repeat sigT_eq.
Theorem exec_ret :
  forall T (v : T) w r,
  exec (Ret v) w r ->
  match r with
  | Finished v' w' => v = v' /\ w = w'
  | Crashed w' => w = w'
  end.
Proof.
(intros).
(inv_exec' H; intuition).
(inv_exec' H4; intuition).
Qed.
Ltac
 inv_ret :=
  match goal with
  | H:exec (Ret _) _ _ |- _ => apply exec_ret in H; safe_intuition; subst
  end.
Ltac
 inv_exec :=
  match goal with
  | _ =>
      inv_ret
  | H:exec (Bind _ _) _ _ |- _ => inv_exec' H; repeat inv_ret
  | H:exec _ _ _ |- _ => inv_exec' H; repeat inv_ret
  end.
Ltac
 inv_rexec :=
  match goal with
  | H:rexec (Ret _) _ _ _ |- _ => inv_exec' H
  | H:rexec _ _ _ _ |- _ => inv_exec' H
  end.
#[local]Hint Constructors exec: core.
Definition exec_equiv T (p : proc T) p' :=
  forall w r, exec p w r <-> exec p' w r.
Instance exec_equiv_equiv  T: (Equivalence (exec_equiv (T:=T))).
Proof.
(constructor; hnf; unfold exec_equiv; intros;
  repeat
   match goal with
   | H:forall (w : world) (r : Result T), _, w:world, r:Result T
     |- _ => specialize (H w r)
   end; intuition eauto).
Qed.
Theorem monad_left_id :
  forall T T' (p : T' -> proc T) v, exec_equiv (Bind (Ret v) p) (p v).
Proof.
(unfold exec_equiv; split; intros).
-
(inv_exec; eauto).
(inv_exec; eauto).
-
(eapply ExecBindFinished; eauto).
Qed.
Theorem monad_assoc :
  forall `(p1 : proc T) `(p2 : T -> proc T') `(p3 : T' -> proc T''),
  exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun v => Bind (p2 v) p3)).
Proof.
(unfold exec_equiv; split; intros).
-
(destruct r; repeat (inv_exec; eauto)).
-
(destruct r; repeat (inv_exec; eauto)).
Qed.
#[local]Hint Constructors rexec: core.
Theorem rexec_equiv :
  forall T (p p' : proc T) `(rec : proc R) w r,
  exec_equiv p p' -> rexec p' rec w r -> rexec p rec w r.
Proof.
(intros).
inv_rexec.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqaWuQ9J"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqlkiVkL"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
-
(apply H in H1; eauto).
-
(apply H in H1; eauto).
Qed.
Theorem rexec_finish_any_rec :
  forall `(p : proc T) `(rec : proc R) `(rec' : proc R') w v w',
  rexec p rec w (RFinished v w') -> rexec p rec' w (RFinished v w').
Proof.
(intros).
(inversion H; subst; eauto).
Qed.
#[local]Hint Constructors exec_recover: core.
Arguments clos_refl_trans_1n {A} R _ _.
Theorem exec_recover_bind_inv :
  forall `(p : proc R) `(p' : R -> proc R') w rv' w'',
  exec_recover (Bind p p') w rv' w'' ->
  exists rv1 w1,
    exec_recover p w rv1 w1 /\
    (exists rv2 w2,
       clos_refl_trans_1n
         (fun '(rv, w) '(rv', w') => rexec (p' rv) p w (Recovered rv' w'))
         (rv1, w1) (rv2, w2) /\ exec (p' rv2) w2 (Finished rv' w'')).
Proof.
(induction 1).
-
(inv_exec; eauto  10 using rt1n_refl).
-
(repeat deex).
(inv_exec; eauto  10).
+
(descend; intuition eauto).
(descend; intuition eauto).
(eapply rt1n_trans; eauto).
(simpl; eauto).
+
(inv_exec; eauto  10).
(descend; intuition eauto).
(descend; intuition eauto).
(eapply rt1n_trans; eauto).
(simpl; eauto).
Qed.
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-09-03 10:56:05.830000.*)

