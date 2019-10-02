Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq1RGWLI"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Prelim.
Require Import Monad.
Require Import HOASCircuits.
Require Import HOASExamples.
Require Import Denotation.
Require Import Composition.
Require Import DBCircuits.
Require Import TypeChecking.
Require Import Symmetric.
Require Import SemanticLib.
Require Import List.
Set Bullet Behavior Strict Subproofs.
Global Unset Asymmetric Patterns.
Require Import Omega.
Delimit Scope bexp_scope with bx.
Open Scope bexp_scope.
Open Scope circ_scope.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Reserved Notation "\226\140\136 b | f \226\140\137" (at level 0).
Fixpoint interpret_bexp (b : bexp) (f : Var -> bool) : bool :=
  match b with
  | b_t => true
  | b_f => false
  | b_var v => f v
  | b_not b => \194\172 \226\140\136 b | f \226\140\137
  | b_and b1 b2 => \226\140\136 b1 | f \226\140\137 && \226\140\136 b2 | f \226\140\137
  | b_xor b1 b2 => \226\140\136 b1 | f \226\140\137 \226\138\149 \226\140\136 b2 | f \226\140\137
  end
where "\226\140\136 b | f \226\140\137" := (interpret_bexp b f).
Reserved Notation "\206\1471 \226\136\170 \206\1472" (at level 30).
Fixpoint classical_merge (\206\1471 \206\1472 : Ctx) :=
  match \206\1471, \206\1472 with
  | [], _ => \206\1472
  | _, [] => \206\1471
  | None :: \206\1471', o :: \206\1472' => o :: \206\1471' \226\136\170 \206\1472'
  | Some w :: \206\1471', _ :: \206\1472' => Some w :: \206\1471' \226\136\170 \206\1472'
  end
where "\206\1471 \226\136\170 \206\1472" := (classical_merge \206\1471 \206\1472).
Fixpoint get_context (b : bexp) : Ctx :=
  match b with
  | b_t => []
  | b_f => []
  | b_var v => singleton v Qubit
  | b_not b => get_context b
  | b_and b1 b2 => get_context b1 \226\136\170 get_context b2
  | b_xor b1 b2 => get_context b1 \226\136\170 get_context b2
  end.
Reserved Notation "\206\1471 \226\138\130 \206\1472" (at level 70).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Lemma classical_merge_nil_l : forall \206\147, [] \226\136\170 \206\147 = \206\147.
Proof.
(destruct \206\147; trivial).
Qed.
Lemma classical_merge_nil_r : forall \206\147, \206\147 \226\136\170 [] = \206\147.
Proof.
(destruct \206\147; trivial).
(simpl).
(destruct o; easy).
Qed.
Lemma subset_classical_merge : forall \206\147 \206\1471 \206\1472, \206\1471 \226\136\170 \206\1472 \226\138\130 \206\147 -> (\206\1471 \226\138\130 \206\147) * (\206\1472 \226\138\130 \206\147).
Proof.
(induction \206\147).
-
(intros \206\1471 \206\1472 H).
(destruct \206\1471, \206\1472).
(split; constructor).
(inversion H).
(destruct o; inversion H).
(destruct o; inversion H).
-
(intros).
(destruct \206\1471, \206\1472).
(split; constructor).
(simpl in H).
(split; [ constructor | easy ]).
(split; [ rewrite classical_merge_nil_r in H; easy | constructor ]).
(destruct a).
(destruct (IH\206\147 \206\1471 \206\1472); auto).
(simpl in H).
(destruct o).
(inversion H; subst).
easy.
(inversion H; subst).
easy.
(split; apply sub_some; easy).
(destruct o, o0; inversion H; subst).
specialize (IH\206\147 _ _ H2) as [S1 S2].
(split; apply sub_none; easy).
Qed.
Fixpoint position_of (v : Var) (\206\147 : Ctx) : nat :=
  match v with
  | 0 => 0
  | S v' =>
      match \206\147 with
      | [] => 0
      | None :: \206\147' => position_of v' \206\147'
      | Some w :: \206\147' => S (position_of v' \206\147')
      end
  end.
Lemma position_of_lt :
  forall v \206\147 W, nth v \206\147 None = Some W -> (position_of v \206\147 < \226\159\166 \206\147 \226\159\167)%nat.
Proof.
(intros v \206\147).
revert v.
(induction \206\147).
-
(simpl).
(destruct v; easy).
-
(intros).
(destruct v).
+
(simpl in H).
subst.
(simpl).
omega.
+
(simpl in *).
specialize (IH\206\147 _ _ H).
(destruct a).
omega.
easy.
Qed.
Lemma singleton_nth_classical :
  forall \206\147 v, singleton v Qubit \226\138\130 \206\147 -> exists W, nth v \206\147 None = Some W.
Proof.
(induction \206\147; intros).
(destruct v; inversion H).
(simpl in *).
(destruct v).
(inversion H).
eauto.
(simpl in *).
(apply IH\206\147).
(inversion H; subst; easy).
Qed.
Fixpoint get_wire {W m} (n : nat) (ps : Pat (m \226\168\130 W)) (default : Pat W) : Pat W.
(destruct m as [| m']).
+
exact default.
+
(simpl in ps).
dependent destruction ps.
(destruct n as [| n']).
-
exact ps1.
-
exact (get_wire W m' n' ps2 default).
Defined.
Lemma get_wire_WT :
  forall \206\147 m n default (p : Pat (m \226\168\130 Qubit)),
  (n < m)%nat ->
  \206\147 \226\138\162 p :Pat ->
  {\206\1471 : OCtx & {\206\1472 : OCtx & \206\147 \226\169\181 \206\1471 \226\136\153 \206\1472 & \206\1471 \226\138\162 get_wire n p default :Pat}}.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq4Orkzk"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Proof.
(intros \206\147 m).
generalize dependent \206\147.
(induction m).
(intros; omega).
(intros \206\147 n default p H H0).
dependent destruction p.
dependent destruction H0.
(destruct n).
-
(simpl).
(unfold solution_left).
(unfold eq_rect_r).
(simpl).
exists \206\1471,\206\1472.
(constructor; trivial).
assumption.
-
(edestruct (IHm \206\1472 n default) as [\206\1471' T]).
omega.
(apply H0_0).
(destruct T as [\206\1472' T]).
(simpl in t).
(simpl).
(unfold solution_left).
(unfold eq_rect_r).
(simpl).
exists \206\1471',(\206\1471 \226\139\147 \206\1472').
2: (apply t).
type_check.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq0vG5Ty"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Fixpoint replace_wire {W m} (p : Pat W) (n : nat) (ps : Pat (m \226\168\130 W)) : Pat (m \226\168\130 W).
(destruct m as [| m']).
+
exact ps.
+
dependent destruction ps.
(destruct n as [| n']).
-
exact (pair p ps2).
-
exact (pair ps1 (replace_wire W m' p n' ps2)).
Defined.
Fixpoint default_wire (W : WType) : Pat W :=
  match W with
  | One => unit
  | Qubit => qubit 0%nat
  | Bit => bit 0%nat
  | Tensor W1 W2 => pair (default_wire W1) (default_wire W2)
  end.
Fixpoint unzip_wires {W m} (n : nat) (ps : Pat (m \226\168\130 W)) :
Pat (n \226\168\130 W) * Pat W * Pat ((m - n - 1) \226\168\130 W).
(destruct m as [| m']).
-
exact (default_wire _, default_wire _, default_wire _)%core.
-
dependent destruction ps.
(destruct n as [| n']).
+
(simpl).
(rewrite Nat.sub_0_r).
exact (unit, ps1, ps2)%core.
+
(simpl).
(apply unzip_wires with (n := n') in ps2).
(destruct ps2 as [[ps1' p] ps2']).
exact (pair ps1 ps1', p, ps2')%core.
Defined.
Fixpoint zip_wires {W m1 m2} (ps1 : Pat (m1 \226\168\130 W)) (p : Pat W) 
(ps2 : Pat (m2 \226\168\130 W)) : Pat ((m1 + m2 + 1) \226\168\130 W).
(destruct m1).
-
(simpl).
(rewrite Nat.add_1_r).
(apply (pair p ps2)).
-
(simpl).
dependent destruction ps1.
specialize (zip_wires _ _ _ ps1_2 p ps2).
exact (pair ps1_1 zip_wires).
Defined.
Notation "'Square_Box' W" := (Box W W) (at level 100).
Fixpoint share_to (n k : nat) : Square_Box n \226\168\130 Qubit \226\138\151 Qubit :=
  match n with
  | 0 => id_circ
  | S n' =>
      match k with
      | 0 =>
          box_ qqst
          \226\135\146 (let_ ( (q, qs), t)\226\134\144 output qqst;
             let_ (q, t)\226\134\144 CNOT $ (q, t); ((q, qs), t))
      | S k' =>
          box_ qqst
          \226\135\146 (let_ ( (q, qs), t)\226\134\144 output qqst;
             let_ (qs, t)\226\134\144 share_to n' k' $ (qs, t); ((q, qs), t))
      end
  end.
Lemma share_to_WT : forall n k, Typed_Box (share_to n k).
Proof.
(induction n; type_check).
(destruct k; type_check).
(apply IHn; type_check).
Qed.
Fixpoint share_to' (n k : nat) : Square_Box S n \226\168\130 Qubit :=
  match n with
  | 0 => id_circ
  | S n' =>
      match k with
      | 0 =>
          box_ qqst
          \226\135\146 (let_ (t, (q, qs))\226\134\144 qqst; let_ (q, t)\226\134\144 CNOT $ (q, t); (t, (q, qs)))
      | S k' =>
          box_ qqst
          \226\135\146 (let_ (t, (q, qs))\226\134\144 qqst;
             let_ (t, qs)\226\134\144 share_to' n' k' $ (t, qs); (t, (q, qs)))
      end
  end.
Lemma share_to_WT' : forall n k, Typed_Box (share_to' n k).
Proof.
(induction n; type_check).
(destruct k; type_check).
(apply IHn; type_check).
Qed.
Lemma size_repeat_ctx : forall n W, size_ctx (repeat (Some W) n) = n.
Proof.
(induction n; trivial).
(intros; simpl).
(rewrite IHn).
reflexivity.
Qed.
Lemma ctx_dom_repeat : forall n, ctx_dom (repeat (Some Qubit) n) = seq 0 n.
Proof.
(induction n; trivial).
(simpl).
(rewrite IHn).
(rewrite seq_shift).
reflexivity.
Qed.
Fixpoint pat_max {W} (p : Pat W) : nat :=
  match p with
  | () => 0
  | qubit v => v
  | bit v => v
  | pair p1 p2 => Nat.max (pat_max p1) (pat_max p2)
  end.
Lemma maps_to_repeat : forall v n W, v < n -> maps_to v (repeat (Some W) n) = Some v.
Proof.
(induction v; intros n W L; auto).
-
(destruct n; try omega).
easy.
-
(destruct n; try omega).
(simpl).
(rewrite IHv by omega).
easy.
Qed.
Lemma subst_pat_\207\131_n :
  forall W W' n (p : Pat W),
  (pat_max p < n)%nat -> subst_pat (repeat (Some W') n) p = p.
Proof.
(intros).
gen W'.
(induction p; intros W').
-
(simpl; reflexivity).
-
(simpl in *).
(unfold subst_var).
(rewrite maps_to_repeat; easy).
-
(simpl in *).
(unfold subst_var).
(rewrite maps_to_repeat; easy).
-
(simpl in *).
(apply Nat.max_lub_lt_iff in H as [L1 L2]).
(rewrite IHp1, IHp2; easy).
Qed.
Lemma pat_max_fresh :
  forall m n,
  (pat_max (add_fresh_pat (n \226\168\130 Qubit) (repeat (Some Qubit) m)) < S (m + n))%nat.
Proof.
(intros).
generalize dependent m.
(induction n).
-
(intros; simpl; omega).
-
(intros).
(simpl).
(unfold add_fresh_pat; simpl).
(rewrite add_fresh_split; simpl).
(apply Nat.max_lub_lt).
(rewrite repeat_length).
omega.
(rewrite (repeat_combine (option WType) m 1%nat)).
specialize (IHn (m + 1)).
omega.
Qed.
Open Scope matrix_scope.
Lemma singleton_repeat :
  forall n W, singleton n W = repeat None n ++ repeat (Some W) 1%nat.
Proof.
(induction n; intros W; trivial).
(simpl).
(rewrite IHn).
reflexivity.
Qed.
Lemma ctx_dom_none_repeat :
  forall m n, ctx_dom (repeat None m ++ repeat (Some Qubit) n) = seq m n.
Proof.
(induction m; intros n).
-
(simpl).
(apply ctx_dom_repeat).
-
(simpl).
(rewrite IHm).
(apply fmap_S_seq).
Qed.
Lemma size_repeat_none : forall n : nat, size_ctx (repeat None n) = 0%nat.
Proof.
(induction n; trivial).
Qed.
Lemma types_pat_fresh_ntensor :
  forall (\206\147 : Ctx) (n : nat),
  n <> 0%nat ->
  Valid (repeat None (length \206\147) ++ repeat (Some Qubit) n)
  \226\138\162 add_fresh_pat (n \226\168\130 Qubit)%qc \206\147 :Pat.
Proof.
(intros \206\147 n nz).
revert \206\147.
(induction n; intros \206\147).
-
(simpl).
contradiction.
-
(destruct n).
+
(simpl).
clear.
econstructor.
4: type_check.
3: type_check.
validate.
(rewrite merge_nil_r).
reflexivity.
(simpl_rewrite' (singleton_repeat (length \206\147))).
(apply singleton_singleton).
+
(remember (S n) as n').
(simpl).
(unfold add_fresh_pat; simpl).
(rewrite add_fresh_split; simpl).
econstructor.
validate.
2: (constructor; apply singleton_singleton).
2: (apply IHn; omega).
(rewrite singleton_repeat).
(rewrite app_length).
(simpl).
(rewrite <- repeat_combine).
(rewrite <- app_assoc).
(erewrite merge_offset).
reflexivity.
unlock_merge.
reflexivity.
Qed.
Fixpoint qubit_at (v : Var) (\206\147 : Ctx) :=
  match \206\147 with
  | [] => false
  | W :: \206\147' =>
      match v with
      | 0 => match W with
             | Some Qubit => true
             | _ => false
             end
      | S v' => qubit_at v' \206\147'
      end
  end.
Lemma qubit_at_reflect :
  forall v \206\147, qubit_at v \206\147 = true <-> nth v \206\147 None = Some Qubit.
Proof.
(induction v).
-
(intros).
(simpl).
(destruct \206\147).
easy.
(destruct o).
(destruct w; easy).
easy.
-
(intros).
(simpl).
(destruct \206\147).
easy.
(simpl).
(apply IHv).
Qed.
Open Scope circ_scope.
Fixpoint compile (b : bexp) (\206\147 : Ctx) : Square_Box S (\226\159\166 \206\147 \226\159\167) \226\168\130 Qubit :=
  match b with
  | b_t => TRUE \226\136\165 id_circ
  | b_f => FALSE \226\136\165 id_circ
  | b_var v => CNOT_at (1 + \226\159\166 \206\147 \226\159\167) (1 + position_of v \206\147) 0
  | b_not b =>
      init_at true (1 + \226\159\166 \206\147 \226\159\167) 1;;
      id_circ \226\136\165 compile b \206\147;;
      CNOT_at (2 + \226\159\166 \206\147 \226\159\167) 1 0;; id_circ \226\136\165 compile b \206\147;; assert_at true (1 + \226\159\166 \206\147 \226\159\167) 1
  | b_and b1 b2 =>
      init_at false (1 + \226\159\166 \206\147 \226\159\167) 1;;
      id_circ \226\136\165 compile b1 \206\147;;
      init_at false (2 + \226\159\166 \206\147 \226\159\167) 2;;
      id_circ \226\136\165 id_circ \226\136\165 compile b2 \206\147;;
      Toffoli_at (3 + \226\159\166 \206\147 \226\159\167) 1 2 0;;
      id_circ \226\136\165 id_circ \226\136\165 compile b2 \206\147;;
      assert_at false (2 + \226\159\166 \206\147 \226\159\167) 2;;
      id_circ \226\136\165 compile b1 \206\147;; assert_at false (1 + \226\159\166 \206\147 \226\159\167) 1
  | b_xor b1 b2 =>
      init_at false (1 + \226\159\166 \206\147 \226\159\167) 1;;
      id_circ \226\136\165 compile b1 \206\147;;
      CNOT_at (2 + \226\159\166 \206\147 \226\159\167) 1 0;;
      id_circ \226\136\165 compile b1 \206\147;;
      id_circ \226\136\165 compile b2 \206\147;;
      CNOT_at (2 + \226\159\166 \206\147 \226\159\167) 1 0;;
      id_circ \226\136\165 compile b2 \206\147;; assert_at false (1 + \226\159\166 \206\147 \226\159\167) 1
  end.
Lemma ntensor_fold : forall n W, W \226\138\151 n \226\168\130 W = S n \226\168\130 W.
Proof.
reflexivity.
Qed.
Ltac
 compile_typing lem :=
  repeat
   match goal with
   | _ => apply inSeq_WT
   | _ => apply inPar_WT
   | _ => apply id_circ_WT
   | _ =>
       apply boxed_gate_WT
   | |- Typed_Box (CNOT_at ?n ?x ?y) => specialize (CNOT_at_WT n x y); simpl; easy
   | |- Typed_Box (Toffoli_at ?n ?x ?y ?z) =>
         specialize (Toffoli_at_WT n x y z); simpl; easy
   | _ => apply share_to_WT'
   | _ => apply TRUE_WT
   | _ => apply FALSE_WT
   | _ => apply strip_one_l_in_WT
   | _ => apply strip_one_l_out_WT
   | _ => apply strip_one_r_in_WT
   | _ => apply strip_one_r_out_WT
   | H:forall \206\147 : Ctx, Typed_Box _ |- _ => apply H
   | _ => apply lem
   end.
Lemma compile_WT : forall (b : bexp) (\206\147 : Ctx), Typed_Box (compile b \206\147).
Proof.
(induction b; intros; simpl; compile_typing True).
Qed.
Hint Resolve compile_WT: typed_db.
Open Scope matrix_scope.
Fixpoint ctx_to_mat_list (\206\147 : Ctx) (f : Var -> bool) {struct \206\147} : 
list (Matrix 2 2) :=
  match \206\147 with
  | [] => []
  | None :: \206\147' => ctx_to_mat_list \206\147' (fun v => f (S v))
  | Some W :: \206\147' => bool_to_matrix (f O) :: ctx_to_mat_list \206\147' (fun v => f (S v))
  end.
Definition ctx_to_matrix (\206\147 : Ctx) (f : Var -> bool) : Square (2 ^ \226\159\166 \206\147 \226\159\167) :=
  big_kron (ctx_to_mat_list \206\147 f).
Lemma ctx_to_mat_list_length : forall \206\147 f, length (ctx_to_mat_list \206\147 f) = \226\159\166 \206\147 \226\159\167.
Proof.
(induction \206\147; intros f; trivial).
(simpl).
(destruct a; simpl; rewrite IH\206\147; easy).
Qed.
Lemma WF_ctx_to_matrix : forall \206\147 f, WF_Matrix (ctx_to_matrix \206\147 f).
Proof.
(induction \206\147; intros f).
-
auto with wf_db.
