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
Lemma pure_bool_to_matrix : forall b, Pure_State (bool_to_matrix b).
Proof.
(destruct b).
(apply pure1).
(apply pure0).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqNvpYR6"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma pure_big_kron :
  forall (n : nat) (l : list (Square n)) (A : Square n),
  (forall i : nat, Pure_State (nth i l A)) -> Pure_State (\226\168\130 l).
Proof.
(induction l; intros A H).
-
(simpl).
(apply pure_id1).
-
(simpl).
(apply pure_state_kron).
(apply (H 0)).
(apply (IHl A)).
(intros i).
(apply (H (S i))).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqtrOAAW"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma mixed_big_kron :
  forall (n : nat) (l : list (Square n)) (A : Square n),
  (forall i : nat, Mixed_State (nth i l A)) -> Mixed_State (\226\168\130 l).
Proof.
(induction l; intros A H).
-
(simpl).
constructor.
(apply pure_id1).
-
(simpl).
(apply mixed_state_kron).
(apply (H 0)).
(eapply IHl).
(intros i).
(apply (H (S i))).
Qed.
Definition mat_equiv' := @mat_equiv.
Definition mat_equiv_shadow : @mat_equiv = mat_equiv' := eq_refl.
Ltac
 show_dimensions :=
  try rewrite mat_equiv_shadow in *; try rewrite kron_shadow in *;
   try rewrite Mmult_shadow in *.
Ltac
 hide_dimensions :=
  try rewrite <- mat_equiv_shadow in *; try rewrite <- kron_shadow in *;
   try rewrite <- Mmult_shadow in *.
Lemma kron_1_l_inv : forall {m} {n} (A : Matrix m n), A == I 1 \226\138\151 A.
Proof.
(intros).
specialize (kron_1_l A) as G.
show_dimensions.
(rewrite 2!Nat.mul_1_l in *).
symmetry.
(apply G).
Qed.
Lemma kron_1_r_inv : forall {m} {n} (A : Matrix m n), A == A \226\138\151 I 1.
Proof.
(intros).
specialize (kron_1_r A) as G.
show_dimensions.
(rewrite 2!Nat.mul_1_r in *).
symmetry.
(apply G).
Qed.
Goal _ forall m n (A B : Matrix m n), A == B -> I 1 \226\138\151 A \226\138\151 I 1 == I 1 \226\138\151 B \226\138\151 I 1.
Proof.
(intros).
(rewrite kron_1_l).
(rewrite kron_1_l).
restore_dims.
(rewrite (kron_1_r A)).
(rewrite (kron_1_r B)).
restore_dims.
(apply H).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqIzkxlr"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma morphism_test :
  forall {m} {n} (A : Matrix m n),
  Morphisms.Proper (Morphisms.respectful mat_equiv (flip impl)) (mat_equiv A).
Proof.
(intros).
(unfold Morphisms.Proper).
(unfold Morphisms.respectful).
(unfold flip).
(unfold impl).
(intros).
(rewrite H0).
(rewrite H).
reflexivity.
Qed.
Lemma big_kron_append :
  forall m n (l1 l2 : list (Matrix m n)),
  m <> 0 -> n <> 0 -> \226\168\130 (l1 ++ l2) == (\226\168\130 l1) \226\138\151 (\226\168\130 l2).
Proof.
(induction l1).
-
(intros).
(simpl).
(rewrite <- kron_1_l_inv).
reflexivity.
-
(intros).
(simpl).
(erewrite IHl1; auto).
restore_dims try rewrite app_length; try rewrite Nat.pow_add_r; lia.
(rewrite kron_assoc'; try apply Nat.pow_nonzero; try lia).
reflexivity.
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqwTWq3g"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma pure_ctx_to_matrix : forall \206\147 f, Pure_State (ctx_to_matrix \206\147 f).
Proof.
(intros).
(unfold ctx_to_matrix).
specialize (pure_big_kron 2) as PBK.
(rewrite <- (ctx_to_mat_list_length \206\147 f)).
(eapply PBK).
clear.
revert f.
(induction \206\147).
(intros f [| i]).
(simpl).
(apply pure0).
(simpl).
(apply pure0).
(destruct i, a; simpl; [ apply pure_bool_to_matrix |  |  |  ]; apply IH\206\147).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqFWeai8"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma is_valid_singleton_merge :
  forall W (\206\147 : Ctx) n, (length \206\147 <= n)%nat -> is_valid (\206\147 \226\139\147 singleton n W).
Proof.
(induction \206\147; intros).
-
unlock_merge.
(simpl).
(apply valid_valid).
-
(destruct n).
(simpl in H; omega).
unlock_merge.
(simpl).
(simpl in H).
(destruct IH\206\147 with (n := n)).
omega.
(rewrite H0).
(destruct a; simpl; apply valid_valid).
Qed.
Lemma size_ctx_app :
  forall \206\1471 \206\1472 : Ctx, size_ctx (\206\1471 ++ \206\1472) = (size_ctx \206\1471 + size_ctx \206\1472)%nat.
Proof.
(induction \206\1471; trivial).
(intros).
(simpl).
(rewrite IH\206\1471).
(destruct a; reflexivity).
Qed.
Lemma singleton_length : forall n W, length (singleton n W) = (n + 1)%nat.
Proof.
(induction n; trivial).
(intros W).
(simpl).
(rewrite IHn).
reflexivity.
Qed.
Ltac
 dim_solve :=
  unify_pows_two; simpl; try rewrite size_ntensor; simpl; try rewrite Nat.mul_1_r;
   omega.
Ltac
 unify_dim_solve :=
  match goal with
  | |- @kron ?m ?n ?o ?p ?A ?B = @kron ?m' ?n' ?o' ?p' ?A' ?B' =>
        replace A with A' by unify_dim_solve; replace B with B' by unify_dim_solve;
         replace m with m' by dim_solve; replace n with n' 
         by dim_solve; replace o with o' by dim_solve; replace p with p'
         by dim_solve; reflexivity
  | |- _ = _ => reflexivity
  end.
Ltac
 show_static :=
  repeat
   match goal with
   | |- Static_Box ?c => constructor; intros
   | |- Static_Circuit ?c => constructor; intros
   end.
Ltac
 show_pure :=
  repeat
   match goal with
   | |- Pure_State (\226\168\130 ctx_to_mat_list ?\206\147 ?f) => replace 
     (\226\168\130 ctx_to_mat_list \206\147 f) with ctx_to_matrix \206\147 f by easy
   | |- @Pure_State ?W (ctx_to_matrix ?\206\147 ?f) =>
         let H := fresh "H" in
         specialize (pure_ctx_to_matrix \206\147 f) as H;
          match type of H with
          | @Pure_State ?W' (ctx_to_matrix ?\206\147 ?f) =>
              replace W with W' by dim_solve; apply H
          end; clear H
   | |- @Pure_State ?W (@kron ?a ?b ?c ?d ?A ?B) =>
         let H := fresh "H" in
         specialize (pure_state_kron a c A B) as H;
          match type of H
          with
          | ?H1 -> ?H2 -> @Pure_State ?W' (@kron ?a' ?b' ?c' ?d' ?A ?B) =>
              replace W with W' by dim_solve; replace a with a' by dim_solve;
               replace b with b' by dim_solve; replace c with c' 
               by dim_solve; replace d with d' by dim_solve; 
               apply H
          end; clear H
   | _ => apply pure_bool_to_matrix
   | _ => apply pure0
   | _ => apply pure1
   | _ => apply pure_id1
   end.
Ltac
 show_mixed :=
  repeat
   match goal with
   | |- @Mixed_State ?W (@denote_box true ?W1 ?W2 ?c ?\207\129) =>
         let H := fresh "H" in
         let S := fresh "S" in
         let T := fresh "T" in
         specialize (@denote_static_box_correct W1 W2 c) as H;
          unfold WF_Superoperator in H; assert (S : Static_Box c) by show_static;
          assert (T : Typed_Box c) by (compile_typing compile_WT; type_check);
          specialize (H S T \207\129); simpl in H;
          match type of H with
          | _ -> @Mixed_State ?W' (denote_box true ?c' ?\207\129') =>
              replace \207\129 with \207\129' by easy; replace W with W' by dim_solve; try apply H
          end; clear H S T
   end; try (solve [ apply Pure_S; show_pure ]).
Hint Extern 2 (Mixed_State _) => show_mixed: wf_db.
Ltac
 rewrite_inPar :=
  match goal with
  | |-
    context [ (@denote_box true ?W ?W' (@inPar ?W1 ?W1' ?W2 ?W2' ?f ?g))
                (@kron ?m ?n ?o ?p ?\207\1291 ?\207\1292) ] =>
        let IP := fresh "IP" in
        specialize (inPar_correct W1 W1' W2 W2' f g true \207\1291 \207\1292) as IP; simpl in IP;
         try rewrite ctx_to_mat_list_length in *; try rewrite size_ntensor in IP;
         try rewrite Nat.mul_1_r in IP; try fold NTensor in *; 
         simpl in *; rewrite IP; clear IP
  end; try (solve [ type_check ]); eauto with wf_db.
Ltac
 rewrite_inPar' :=
  fold NTensor; simpl in *;
   match goal with
   | |-
     context [ (@denote_box true ?W ?W' (@inPar ?W1 ?W1' ?W2 ?W2' ?f ?g))
                 (@kron ?m ?n ?o ?p ?\207\1291 ?\207\1292) ] =>
         let IP := fresh "IP" in
         specialize (inPar_correct W1 W1' W2 W2' f g \207\1291 \207\1292) as IP; simpl in *;
          match goal with
          | H:?A ->
              ?B ->
              ?C ->
              ?D ->
              (@denote_box true ?W ?W' (@inPar ?W1 ?W1' ?W2 ?W2' ?f ?g))
                (@kron ?m' ?n' ?o' ?p' ?\207\1291 ?\207\1292) = ?RHS
            |- _ =>
                replace m with m'; try dim_solve; replace n with n'; try dim_solve;
                 replace o with o'; try dim_solve; replace p with p'; 
                 try dim_solve; try rewrite H
          end; clear IP
   end; try (solve [ type_check ]); eauto with wf_db.
Ltac
 listify_kron :=
  unfold ctx_to_matrix;
   repeat
    match goal with
    | |- context [ @kron ?a ?b ?c ?d ?A (\226\168\130 ?li) ] => replace
      (@kron a b c d A (\226\168\130 li)) with \226\168\130 (A :: li)
      by
        (simpl; Msimpl; rewrite ctx_to_mat_list_length;
          try rewrite size_ntensor, Nat.mul_1_r; easy)
    end.
Lemma ctx_lookup_exists :
  forall v \206\147 f,
  get_context (b_var v) \226\138\130 \206\147 ->
  ctx_to_mat_list \206\147 f !! position_of v \206\147 = Some (bool_to_matrix (f v)).
Proof.
(induction v; intros \206\147 f H).
-
(destruct \206\147).
(inversion H).
(destruct o).
(simpl).
reflexivity.
(inversion H).
-
(destruct \206\147).
(simpl).
(inversion H).
(simpl).
(destruct o).
(simpl).
(apply IHv).
(simpl in H).
(inversion H).
subst.
(simpl).
easy.
(apply IHv).
(simpl in H).
(inversion H).
subst.
(simpl).
easy.
Qed.
Fact CNOT_at_spec :
  forall (b1 b2 : bool) (n x y : nat) (li : list (Matrix 2 2)),
  x < n ->
  y < n ->
  x <> y ->
  nth_error li x = Some (bool_to_matrix b1) ->
  nth_error li y = Some (bool_to_matrix b2) ->
  (\226\159\166 CNOT_at n x y \226\159\167) (\226\168\130 li) = \226\168\130 update_at li y (bool_to_matrix (b1 \226\138\149 b2)).
Admitted.
Fact Toffoli_at_spec :
  forall (b1 b2 b3 : bool) (n x y z : nat) (li : list (Matrix 2 2)),
  x < n ->
  y < n ->
  z < n ->
  x <> y ->
  x <> z ->
  y <> z ->
  nth_error li x = Some (bool_to_matrix b1) ->
  nth_error li y = Some (bool_to_matrix b2) ->
  nth_error li z = Some (bool_to_matrix b3) ->
  (\226\159\166 Toffoli_at n x y z \226\159\167) (\226\168\130 li) =
  \226\168\130 update_at li z (bool_to_matrix ((b1 && b2) \226\138\149 b3)).
Admitted.
Ltac
 rewrite_inPar'' :=
  match goal with
  | |-
    context [ (@denote_box true ?W ?W' (@inPar ?W1 ?W1' ?W2 ?W2' ?f ?g))
                (@kron ?m ?n ?o ?p ?\207\1291 ?\207\1292) ] =>
        let IP := fresh "IP" in
        specialize (inPar_correct W1 W1' W2 W2' f g true \207\1291 \207\1292) as IP;
         rewrite size_ntensor in *; simpl in *; try rewrite Nat.mul_1_r in *;
         rewrite IP; clear IP
  end; try (solve [ type_check ]).
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqYGfOYF"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma init_at_spec :
  forall (b : bool) (n i : nat) (l1 l2 : list (Square 2)) (A B : Square 2),
  length l1 = i ->
  length l2 = n - i ->
  (forall j, Mixed_State (nth j l1 A)) ->
  (forall j, Mixed_State (nth j l2 B)) ->
  i < S n ->
  (\226\159\166 init_at b n i \226\159\167) (\226\168\130 (l1 ++ l2)) == \226\168\130 (l1 ++ [bool_to_matrix b] ++ l2).
Proof.
(intros b n i).
gen n.
(induction i).
-
(intros n l1 l2 A B L1 L2 M1 M2 Lt).
(destruct l1; inversion L1).
(simpl in *).
clear L1 M1 Lt.
(rewrite strip_one_l_in_eq).
(rewrite Nat.sub_0_r in L2).
(rewrite L2 in *).
restore_dims
 simpl; try rewrite size_ntensor; try rewrite L2; simpl; unify_pows_two; lia.
(erewrite denote_box_compat).
2: {
restore_dims
 simpl; try rewrite size_ntensor; try rewrite L2; simpl; unify_pows_two; lia.
(rewrite (kron_1_l_inv (\226\168\130 l2))).
reflexivity.
}
(rewrite L2).
rewrite_inPar''.
restore_dims
 simpl; try rewrite size_ntensor; try rewrite L2; simpl; unify_pows_two; lia.
(rewrite id_circ_spec).
(rewrite init_spec).
restore_dims
 simpl; try rewrite size_ntensor; try rewrite L2; simpl; unify_pows_two; lia.
reflexivity.
-
(intros n l1 l2 A B L1 L2 M1 M2 Lt).
(destruct n; [ omega |  ]).
(destruct l1; inversion L1).
(simpl).
(rewrite H0).
restore_dims
 simpl; try rewrite size_ntensor; try rewrite app_length; simpl; unify_pows_two;
  lia.
replace (length (l1 ++ l2)) with n by (rewrite app_length; lia).
rewrite_inPar''.
(rewrite id_circ_spec).
restore_dims
 simpl; try rewrite size_ntensor; try rewrite app_length; simpl; unify_pows_two;
  lia.
(simpl).
specialize (IHi n l1 l2 A B).
show_dimensions.
(repeat rewrite app_length in *).
(simpl in *).
replace (length l1 + S (length l2)) with S n in * by lia.
(simpl in *).
(rewrite size_ntensor).
(simpl).
(rewrite Nat.mul_1_r).
(rewrite IHi; trivial; try lia).
(* Auto-generated comment: Succeeded. *)

(* Auto-generated comment: At 2019-08-14 18:13:03.430000.*)

