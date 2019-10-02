Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqgmJjIR"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqo9sLpI"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Require Import Program.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coq701yPz"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Import Arith.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqHx786X"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Import Omega.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqSSx1yH"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Import Monad.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqoq3PJ3"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Export Contexts.
Require Export HOASCircuits.
Require Export HOASLib.
Require Export DBCircuits.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqZL5ChX"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Require Export Quantum.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqPmkW1h"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqToWrV3"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
(simpl; Msimpl).
(dependent destruction u; simpl; Msimpl; reflexivity).
Timeout 1 About restore_dims.
Timeout 1 About trans.
Timeout 1 About ctrls_to_list.
(simpl_rewrite @denote_unitary_transpose).
Lemma apply_unitary_unitary :
  forall W n (u : Unitary W) l, length l = \226\159\166 W \226\159\167 -> (forall x, In x l -> x < n)%nat -> WF_Unitary (apply_unitary n u l).
Proof.
(intros W n u l L LT).
(destruct W; try (solve [ inversion u ])).
-
(simpl).
(destruct l; try (solve [ inversion L ])).
(simpl).
specialize (LT n0 (or_introl eq_refl)).
replace (2 ^ n)%nat with (2 ^ n0 * 2 * 2 ^ (n - n0 - 1))%nat by unify_pows_two.
(repeat apply kron_unitary; try apply id_unitary; try apply unitary_gate_unitary).
specialize (unitary_gate_unitary u) as UU.
(apply UU).
-
(dependent destruction u; apply denote_ctrls_unitary; auto).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqgGwNLM" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Lemma apply_U_correct :
  forall W n (U : Unitary W) l, length l = \226\159\166 W \226\159\167 -> (forall x, In x l -> x < n)%nat -> WF_Superoperator (apply_U n U l).
Proof.
(intros).
(apply super_unitary_correct; trivial).
(apply apply_unitary_unitary; easy).
Qed.
Redirect "/var/folders/m1/0k3qczq13cg04mhs4ww613ww0000gn/T/coqmi6AHM" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Definition apply_new0 {n} : Superoperator (2 ^ n) (2 ^ (n + 1)) := super (I (2 ^ n) \226\138\151 \226\136\1630\226\159\169).
Definition apply_new1 {n} : Superoperator (2 ^ n) (2 ^ (n + 1)) := super (I (2 ^ n) \226\138\151 \226\136\1631\226\159\169).
Definition apply_discard {n} (k : nat) : Superoperator (2 ^ n) (2 ^ (n - 1)) :=
  Splus (super (I (2 ^ k) \226\138\151 \226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - k - 1)))) (super (I (2 ^ k) \226\138\151 \226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - k - 1)))).
Definition apply_assert0 {n} (k : nat) : Superoperator (2 ^ n) (2 ^ (n - 1)) := super (I (2 ^ k) \226\138\151 \226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - k - 1))).
Definition apply_assert1 {n} (k : nat) : Superoperator (2 ^ n) (2 ^ (n - 1)) := super (I (2 ^ k) \226\138\151 \226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - k - 1))).
Definition apply_meas {n} (k : nat) : Superoperator (2 ^ n) (2 ^ n) :=
  Splus (super (I (2 ^ k) \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - k - 1)))) (super (I (2 ^ k) \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - k - 1)))).
Definition apply_measQ {n} (k : nat) : Superoperator (2 ^ n) (2 ^ n) :=
  Splus (super (I (2 ^ k) \226\138\151 \226\136\1630\226\159\169\226\159\1680\226\136\163 \226\138\151 I (2 ^ (n - k - 1)))) (super (I (2 ^ k) \226\138\151 \226\136\1631\226\159\169\226\159\1681\226\136\163 \226\138\151 I (2 ^ (n - k - 1)))).
Definition apply_gate {n} {w1} {w2} (safe : bool) (g : Gate w1 w2) (l : list nat) :
  Superoperator (2 ^ n) (2 ^ (n + \226\159\166 w2 \226\159\167 - \226\159\166 w1 \226\159\167)) :=
  match g with
  | U u => apply_U n u l
  | BNOT => apply_U n _X l
  | init0 | new0 => apply_new0
  | init1 | new1 => apply_new1
  | meas => apply_meas (hd O l)
  | measQ => apply_meas (hd O l)
  | discard => apply_discard (hd O l)
  | assert0 => (if safe then apply_discard else apply_assert0) (hd O l)
  | assert1 => (if safe then apply_discard else apply_assert1) (hd O l)
  end.
Definition operator_sum {m} {n} (l : list (Matrix m n)) : Superoperator n m := fold_left Splus (map (fun A => super A) l) SZero.
Definition outer_sum {m} {n} (l : list (Matrix m n)) := fold_left Mplus (map (fun A => (A) \226\128\160 \195\151 A) l) Zero.
Axiom
  (operator_sum_decomposition : forall {m} {n} (l : list (Matrix m n)), outer_sum l = I n <-> WF_Superoperator (operator_sum l)).
Lemma discard_superoperator :
  forall (n i j : nat) (\207\129 : Square (2 ^ n)),
  (i * j * 2 = 2 ^ n)%nat ->
  Mixed_State \207\129 -> Mixed_State (I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\136\1630\226\159\169 \226\138\151 I j) .+ I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j \195\151 \207\129 \195\151 (I i \226\138\151 \226\136\1631\226\159\169 \226\138\151 I j)).
Proof.
(intros n i j \207\129 E M).
(destruct (operator_sum_decomposition [I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j; I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j]) as [WFS _]).
(assert (OS : outer_sum [I i \226\138\151 \226\159\1680\226\136\163 \226\138\151 I j; I i \226\138\151 \226\159\1681\226\136\163 \226\138\151 I j] = I (i * 2 * j))).
idtac.
(unfold outer_sum).
(simpl).
Msimpl.
(rewrite Mplus_0_l).
