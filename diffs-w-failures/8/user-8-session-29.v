Require Import Datatypes.
Require Export TypeChecking.
Import ListNotations.
Open Scope list_scope.
Open Scope circ_scope.
Definition boxed_gate {W1} {W2} (g : Gate W1 W2) : 
  Box W1 W2 := box_ p \226\135\146 (gate_ p2 \226\134\144 g @ p; output p2).
Lemma boxed_gate_WT {W1} {W2} (g : Gate W1 W2) : Typed_Box (boxed_gate g).
Proof.
type_check.
Qed.
Coercion boxed_gate : Gate >-> Box.
Lemma types_circuit_valid :
  forall w (c : Circuit w) \206\147, \206\147 \226\138\162 c :Circ -> is_valid \206\147.
Proof.
(intros w c \206\147 pf_c).
(induction pf_c).
-
subst.
(eapply pat_ctx_valid; eauto).
-
(destruct pf1).
subst.
auto.
-
(destruct pf).
subst.
auto.
Qed.
Definition apply_box {w1} {w2} (b : Box w1 w2) (c : Circuit w1) :
  Circuit w2 := let_ x \226\134\144 c; unbox b x.
Notation "b $ c" := (apply_box b c) (right associativity, at level 12) :
  circ_scope.
Coercion output : Pat >-> Circuit.
Lemma apply_box_WT :
  forall w1 w2 (b : Box w1 w2) (c : Circuit w1) \206\147,
  Typed_Box b -> \206\147 \226\138\162 c :Circ -> \206\147 \226\138\162 apply_box b c :Circ.
Proof.
(intros w1 w2 b c \206\147 pf_b pf_c).
(type_check; [  | solve_merge; eapply types_circuit_valid; eauto ]).
(apply unbox_typing; auto).
type_check.
Qed.
Fixpoint lift_circ {W W' : WType} (c0 : Circuit W)
(c : interpret W -> Circuit W') {struct W} : Circuit W'.
(induction W).
+
exact (compose (meas $ c0) (fun p => lift p c)).
+
exact (compose c0 (fun p => lift p c)).
+
exact (compose c0 (fun _ => c tt)).
+
(simpl in c).
(pose (c' := curry c)).
exact
 (compose c0
    (fun p =>
     letpair p1 p2 p
       (lift_circ W1 W' p1 (fun x1 => lift_circ W2 W' p2 (c' x1))))).
Defined.
Program
Definition lift_wire {W W' : WType} (c0 : Circuit W) 
  (c : bool -> Circuit W') : Circuit W' :=
  match W with
  | Bit => compose c0 (fun p => lift p c)
  | Qubit => compose (meas $ c0) (fun p => lift p c)
  | One => c true
  | Tensor W1 W2 => c true
  end.
Notation "'lift_' x \226\134\144 c0 ; c" := (lift_wire c0 (fun x => c))
  (at level 14, right associativity) : circ_scope.
Notation "'lift_' ( x , y ) \226\134\144 c0 ; c" :=
  (compose c0
     (fun p =>
      letpair p1 p2 p (lift_wire p1 (fun x => lift_wire p2 (fun y => c)))))
  (at level 14, right associativity) : circ_scope.
Definition id_circ {W} : Box W W := box_ p \226\135\146 output p.
Lemma id_circ_WT : forall W, Typed_Box (@id_circ W).
Proof.
type_check.
Qed.
Definition SWAP : Box (Qubit \226\138\151 Qubit) (Qubit \226\138\151 Qubit) :=
  box_ (p1, p2)\226\135\146 (p2, p1).
Lemma WT_SWAP : Typed_Box SWAP.
Proof.
type_check.
Qed.
Definition SWAP_GEN {W1} {W2} : Box (W1 \226\138\151 W2) (W2 \226\138\151 W1) :=
  box_ (p1, p2)\226\135\146 (p2, p1).
Lemma WT_SWAP_GEN : forall W1 W2, Typed_Box (@SWAP_GEN W1 W2).
Proof.
type_check.
Qed.
Definition new (b : bool) : Box One Bit := if b then new1 else new0.
Lemma new_WT : forall b, Typed_Box (new b).
Proof.
(destruct b; type_check).
Defined.
Definition init (b : bool) : Box One Qubit := if b then init1 else init0.
Lemma init_WT : forall b, Typed_Box (init b).
Proof.
(destruct b; type_check).
Defined.
Definition assert (b : bool) : Box Qubit One :=
  if b then assert1 else assert0.
Lemma assert_WT : forall b, Typed_Box (assert b).
Proof.
type_check.
Qed.
Definition inSeq {w1} {w2} {w3} (c1 : Box w1 w2) (c2 : Box w2 w3) :
  Box w1 w3 := box_ p1 \226\135\146 (let_ p2 \226\134\144 unbox c1 p1; unbox c2 p2).
Lemma inSeq_WT :
  forall W1 W2 W3 (c1 : Box W1 W2) (c2 : Box W2 W3),
  Typed_Box c1 -> Typed_Box c2 -> Typed_Box (inSeq c1 c2).
Proof.
type_check.
Qed.
Definition inPar {w1} {w2} {w1'} {w2'} (c1 : Box w1 w2) 
  (c2 : Box w1' w2') : Box (w1 \226\138\151 w1') (w2 \226\138\151 w2') :=
  box_ p12
  \226\135\146 (let_ (p1, p2)\226\134\144 output p12;
     let_ p1' \226\134\144 unbox c1 p1; let_ p2' \226\134\144 unbox c2 p2; (p1', p2')).
Lemma inPar_WT :
  forall W1 W1' W2 W2' (c1 : Box W1 W2) (c2 : Box W1' W2'),
  Typed_Box c1 -> Typed_Box c2 -> Typed_Box (inPar c1 c2).
Proof.
type_check.
Qed.
Fixpoint units (n : nat) : Pat (n \226\168\130 One) :=
  match n with
  | O => unit
  | S n' => pair unit (units n')
  end.
Lemma types_units : forall n, Types_Pat \226\136\133 (units n).
Proof.
(induction n; type_check).
Qed.
Fixpoint initMany (b : bool) (n : nat) : Box One (n \226\168\130 Qubit) :=
  match n with
  | 0 => id_circ
  | S n' =>
      box_ () \226\135\146 (let_ q \226\134\144 unbox (init b) ();
                 let_ qs \226\134\144 unbox (initMany b n') (); (q, qs))
  end.
Lemma initMany_WT : forall b n, Typed_Box (initMany b n).
Proof.
(induction n; type_check).
Qed.
Fixpoint inSeqMany (n : nat) {W} (c : Box W W) : Box W W :=
  match n with
  | 0 => id_circ
  | S n' => inSeq c (inSeqMany n' c)
  end.
Lemma inSeqMany_WT :
  forall n W (c : Box W W), Typed_Box c -> Typed_Box (inSeqMany n c).
Proof.
(intros).
(induction n as [| n']; type_check).
Qed.
Fixpoint inParMany (n : nat) {W W'} (c : Box W W') : 
Box (n \226\168\130 W) (n \226\168\130 W') :=
  match n with
  | 0 => id_circ
  | S n' => inPar c (inParMany n' c)
  end.
Lemma inParMany_WT :
  forall n W W' (c : Box W W'), Typed_Box c -> Typed_Box (inParMany n c).
Proof.
(intros).
(induction n as [| n']; type_check).
Qed.
Notation "b1 \226\136\165 b2" := (inPar b1 b2) (at level 51, right associativity) :
  circ_scope.
Notation "b' \194\183 b" := (inSeq b b') (at level 60, right associativity) :
  circ_scope.
Notation "c1 ;; c2" := (inSeq c1 c2) (at level 60, right associativity) :
  circ_scope.
Notation "(())" := (units _) (at level 0) : circ_scope.
Notation "g # n" := (inParMany n g) (at level 11) : circ_scope.
Hint Resolve types_units id_circ_WT boxed_gate_WT init_WT inSeq_WT inPar_WT
  initMany_WT inSeqMany_WT inParMany_WT: typed_db.
Definition CL_AND : Box (Qubit \226\138\151 Qubit) Qubit :=
  box_ ab
  \226\135\146 (let_ (a, b)\226\134\144 output ab;
     let_ z \226\134\144 init0 $ ();
     let_ (a, (b, z))\226\134\144 CCNOT $ (a, (b, z));
     let_ a \226\134\144 meas $ a;
     let_ b \226\134\144 meas $ b; let_ () \226\134\144 discard $ a; let_ () \226\134\144 discard $ b; z).
Lemma CL_AND_WT : Typed_Box CL_AND.
Proof.
type_check.
Qed.
Definition CL_XOR : Box (Qubit \226\138\151 Qubit) Qubit :=
  box_ (a, b)
  \226\135\146 (let_ (a, b)\226\134\144 CNOT $ (a, b); let_ a \226\134\144 meas $ a; let_ () \226\134\144 discard $ a; b).
Lemma CL_XOR_WT : Typed_Box CL_XOR.
Proof.
type_check.
Qed.
Definition CL_OR : Box (Qubit \226\138\151 Qubit) Qubit :=
  box_ (a, b)
  \226\135\146 (let_ a' \226\134\144 _X $ a; let_ b' \226\134\144 _X $ b; let_ z \226\134\144 CL_AND $ (a', b'); _X $ z).
Lemma CL_OR_WT : Typed_Box CL_OR.
Proof.
type_check.
Qed.
Definition TRUE : Box Qubit Qubit := _X.
Lemma TRUE_WT : Typed_Box TRUE.
Proof.
type_check.
Qed.
Definition FALSE : Box Qubit Qubit := id_circ.
Lemma FALSE_WT : Typed_Box FALSE.
Proof.
type_check.
Qed.
Definition NOT : Box (Qubit \226\138\151 Qubit) (Qubit \226\138\151 Qubit) :=
  box_ (x, z)
  \226\135\146 (let_ x \226\134\144 _X $ x; let_ (x, z)\226\134\144 CNOT $ (x, z); let_ x \226\134\144 _X $ x; (x, z)).
Lemma NOT_WT : Typed_Box NOT.
Proof.
type_check.
Qed.
Definition AND : Box (Qubit \226\138\151 Qubit \226\138\151 Qubit) (Qubit \226\138\151 Qubit \226\138\151 Qubit) :=
  box_ xyz
  \226\135\146 (let_ (x, y, z)\226\134\144 output xyz;
     let_ (x, (y, z))\226\134\144 CCNOT $ (x, (y, z)); (x, y, z)).
Lemma AND_WT : Typed_Box AND.
Proof.
type_check.
Qed.
Definition XOR : Box (Qubit \226\138\151 Qubit \226\138\151 Qubit) (Qubit \226\138\151 Qubit \226\138\151 Qubit) :=
  box_ xyz
  \226\135\146 (let_ (x, y, z)\226\134\144 output xyz;
     let_ (x, z)\226\134\144 CNOT $ (x, z); let_ (y, z)\226\134\144 CNOT $ (y, z); (x, y, z)).
Lemma XOR_WT : Typed_Box XOR.
Proof.
type_check.
Qed.
