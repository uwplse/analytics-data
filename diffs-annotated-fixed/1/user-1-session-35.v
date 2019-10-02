Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Export Arith.
Require Export Lia.
Require Export Program.Tactics.
Require Export Coq.Arith.Wf_nat.
Create HintDb math discriminated.
Hint Resolve le_lt_n_Sm: math.
Hint Extern 100  => lia: math.
Hint Extern 100  => congruence: math.
Tactic Notation "dependent" "strong" "induction" constr(e) "generalizing" constr(l) :=
 (let v := fresh "v" in
  let Heq := fresh "Heqv" in
  remember e as v eqn:Heq ; generalize Heq; clear Heq; generalize l; clear l; induction v using lt_wf_ind; intros l;
   (let Heq' := fresh "Heqn" in
    intros Heq'; subst;
     (let l' := fresh "v" in
      let H' := fresh "H" in
      match goal with
      | H:forall m, @?A m -> forall l, m = @?B l -> @?C l
        |- _ =>
            let H0 := fresh "IH" in
            assert (H0 : forall l, A (B l) -> C l); [ intros l' H'; apply (H _ H'); reflexivity | clear H; cbn beta in H0 ]
      end))).
Tactic Notation "dependent" "strong" "induction" constr(e) "generalizing" constr(l) constr(l0) :=
 (let v := fresh "v" in
  let Heq := fresh "Heqv" in
  remember e as v eqn:Heq ; generalize Heq; clear Heq; generalize l, l0; clear l l0; induction v using lt_wf_ind; intros l l0;
   (let Heq' := fresh "Heqn" in
    intros Heq'; subst;
     (let l' := fresh "v" in
      let l0' := fresh "v" in
      let H' := fresh "H" in
      match goal with
      | H:forall m, @?A m -> forall l l0, m = @?B l l0 -> @?C l l0
        |- _ =>
            let H0 := fresh "IH" in
            assert (H0 : forall l l0, A (B l l0) -> C l l0); [ intros l' l0' H'; apply (H _ H'); reflexivity | clear H; cbn beta in H0 ]
      end))).
Tactic Notation "dependent" "strong" "induction" constr(e) "generalizing" constr(l) constr(l0) constr(l1) :=
 (let v := fresh "v" in
  let Heq := fresh "Heqv" in
  remember e as v eqn:Heq ; generalize Heq; clear Heq; generalize l, l0, l1; clear l l0 l1; induction v using lt_wf_ind; intros l l0 l1;
   (let Heq' := fresh "Heqn" in
    intros Heq'; subst;
     (let l' := fresh "v" in
      let l0' := fresh "v" in
      let l1' := fresh "v" in
      let H' := fresh "H" in
      match goal with
      | H:forall m, @?A m -> forall l l0 l1, m = @?B l l0 l1 -> @?C l l0 l1
        |- _ =>
            let H0 := fresh "IH" in
            assert (H0 : forall l l0 l1, A (B l l0 l1) -> C l l0 l1);
             [ intros l' l0' l1' H'; apply (H _ H'); reflexivity | clear H; cbn beta in H0 ]
      end))).
Ltac destruct_pairs := repeat (try match goal with
                                   | H:(_ && _)%bool = true |- _ => apply andb_prop in H
                                   end; Tactics.destruct_pairs).
(* Auto-generated comment: Succeeded. *)

