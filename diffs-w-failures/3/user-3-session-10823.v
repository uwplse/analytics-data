Time From stdpp Require Export base.
Time Set Default Proof Using "Type".
Time
Hint Extern 200 (ProofIrrel _) => (progress lazy beta): typeclass_instances.
Time Instance True_pi : (ProofIrrel True).
Time Proof.
Time (intros [] []; reflexivity).
Time Qed.
Time Instance False_pi : (ProofIrrel False).
Time Proof.
Time (intros []).
Time Qed.
Time
Instance and_pi  (A B : Prop):
 (ProofIrrel A \226\134\146 ProofIrrel B \226\134\146 ProofIrrel (A \226\136\167 B)).
Time Proof.
Time (intros ? ? [? ?] [? ?]).
Time (f_equal; trivial).
Time Qed.
Time
Instance prod_pi  (A B : Type):
 (ProofIrrel A \226\134\146 ProofIrrel B \226\134\146 ProofIrrel (A * B)).
Time Proof.
Time (intros ? ? [? ?] [? ?]).
Time (f_equal; trivial).
Time Qed.
Time
Instance eq_pi  {A} (x : A) `{\226\136\128 z, Decision (x = z)} 
 (y : A): (ProofIrrel (x = y)).
Time Proof.
Time
(set
  (f :=
   fun z =>
   fun H : x = z =>
   match decide (x = z) return (x = z) with
   | left H => H
   | right H' => False_rect _ (H' H)
   end)).
Time
(assert
  (help : \226\136\128 z (H : x = z), eq_trans (eq_sym (f x (eq_refl x))) (f z H) = H)).
Time {
Time (intros ? []).
Time (destruct (f x eq_refl); tauto).
Time }
Time (intros p q).
Time (rewrite <- (help _ p), <- (help _ q)).
Time (unfold f at 2 4).
Time (destruct (decide _)).
Time reflexivity.
Time (exfalso; tauto).
Time Qed.
Time Instance Is_true_pi  (b : bool): (ProofIrrel (Is_true b)).
Time Proof.
Time (destruct b; simpl; apply _).
Time Qed.
Time
Lemma sig_eq_pi `(P : A \226\134\146 Prop) `{\226\136\128 x, ProofIrrel (P x)} 
  (x y : sig P) : x = y \226\134\148 `x = `y.
Time Proof.
Time (split; [ intros <-; reflexivity |  ]).
Time (destruct x as [x Hx], y as [y Hy]; simpl; intros; subst).
Time f_equal.
Time (apply proof_irrel).
Time Qed.
Time
Lemma exists_proj1_pi `(P : A \226\134\146 Prop) `{\226\136\128 x, ProofIrrel (P x)} 
  (x : sig P) p : `x \226\134\190 p = x.
Time Proof.
Time (apply (sig_eq_pi _); reflexivity).
Time Qed.
