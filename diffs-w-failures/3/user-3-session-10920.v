Time From stdpp Require Export countable coPset.
Time Set Default Proof Using "Type".
Time Definition namespace := list positive.
Time Instance namespace_eq_dec : (EqDecision namespace) := _.
Time Instance namespace_countable : (Countable namespace) := _.
Time Typeclasses Opaque namespace.
Time Definition nroot : namespace := nil.
Time
Definition ndot_def `{Countable A} (N : namespace) 
  (x : A) : namespace := encode x :: N.
Time Definition ndot_aux : seal (@ndot_def).
Time by eexists.
Time Qed.
Time
Definition ndot {A} {A_dec} {A_count} := unseal ndot_aux A A_dec A_count.
Time Definition ndot_eq : @ndot = @ndot_def := seal_eq ndot_aux.
Time
Definition nclose_def (N : namespace) : coPset :=
  coPset_suffixes (positives_flatten N).
Time Definition nclose_aux : seal (@nclose_def).
Time by eexists.
Time Qed.
Time Instance nclose : (UpClose namespace coPset) := (unseal nclose_aux).
Time Definition nclose_eq : @nclose = @nclose_def := seal_eq nclose_aux.
Time
Notation "N .@ x" := (ndot N x)
  (at level 19, left associativity, format "N .@ x") : stdpp_scope.
Time Notation "(.@)" := ndot (only parsing) : stdpp_scope.
Time
Instance ndisjoint : (Disjoint namespace) :=
 (\206\187 N1 N2, nclose N1 ## nclose N2).
Time Section namespace.
Time Context `{Countable A}.
Time Implicit Types x y : A.
Time Implicit Type N : namespace.
Time Implicit Type E : coPset.
Time #[global]Instance ndot_inj : (Inj2 (=) (=) (=) (@ndot A _ _)).
Time Proof.
Time (intros N1 x1 N2 x2; rewrite !ndot_eq; naive_solver).
Time Qed.
Time Lemma nclose_nroot : \226\134\145nroot = (\226\138\164 : coPset).
Time Proof.
Time (rewrite nclose_eq).
Time by apply (sig_eq_pi _).
Time Qed.
Time Lemma nclose_subseteq N x : \226\134\145N.@x \226\138\134 (\226\134\145N : coPset).
Time Proof.
Time (intros p).
Time (unfold up_close).
Time (rewrite !nclose_eq, !ndot_eq).
Time (unfold nclose_def, ndot_def; rewrite !elem_coPset_suffixes).
Time (intros [q ->]).
Time (destruct (positives_flatten_suffix N (ndot_def N x)) as [q' ?]).
Time {
Time by exists [encode x].
Time }
Time by exists (q ++ q')%positive; rewrite <- (assoc_L _); f_equal.
Time Qed.
Time Lemma nclose_subseteq' E N x : \226\134\145N \226\138\134 E \226\134\146 \226\134\145N.@x \226\138\134 E.
Time Proof.
Time (intros).
Time (etrans; eauto using nclose_subseteq).
Time Qed.
Time Lemma nclose_infinite N : \194\172 set_finite (\226\134\145N : coPset).
Time Proof.
Time (rewrite nclose_eq).
Time (apply coPset_suffixes_infinite).
Time Qed.
Time Lemma ndot_ne_disjoint N x y : x \226\137\160 y \226\134\146 N.@x ## N.@y.
Time Proof.
Time (intros Hxy a).
Time (unfold up_close).
Time (rewrite !nclose_eq, !ndot_eq).
Time (unfold nclose_def, ndot_def; rewrite !elem_coPset_suffixes).
Time (intros [qx ->] [qy Hqy]).
Time revert Hqy.
Time by intros [=?%encode_inj]%positives_flatten_suffix_eq.
Time Qed.
Time Lemma ndot_preserve_disjoint_l N E x : \226\134\145N ## E \226\134\146 \226\134\145N.@x ## E.
Time Proof.
Time (intros).
Time (pose proof (nclose_subseteq N x)).
Time set_solver.
Time Qed.
Time Lemma ndot_preserve_disjoint_r N E x : E ## \226\134\145N \226\134\146 E ## \226\134\145N.@x.
Time Proof.
Time (intros).
Time by apply symmetry, ndot_preserve_disjoint_l.
Time Qed.
Time End namespace.
Time Create HintDb ndisj.
Time Hint Resolve (subseteq_difference_r (A:=positive) (C:=coPset)): ndisj.
Time Hint Resolve (empty_subseteq (A:=positive) (C:=coPset)): ndisj.
Time Hint Resolve (union_least (A:=positive) (C:=coPset)): ndisj.
Time
Hint Resolve (subseteq_difference_l (A:=positive) (C:=coPset)) |100: ndisj.
Time Hint Resolve nclose_subseteq' |100: ndisj.
Time Hint Extern 0 (_ ## _) => (apply ndot_ne_disjoint; congruence): ndisj.
Time
Hint Resolve (disjoint_difference_l1 (A:=positive) (C:=coPset)) |50: ndisj.
Time
Hint Resolve (disjoint_difference_l2 (A:=positive) (C:=coPset)) |100: ndisj.
Time
Hint Resolve ndot_preserve_disjoint_l |100 ndot_preserve_disjoint_r |100:
  ndisj.
Time
Ltac
 solve_ndisj :=
  repeat
   match goal with
   | H:_ \226\136\170 _ \226\138\134 _ |- _ => apply union_subseteq in H as [? ?]
   end; (solve [ eauto  12 with ndisj ]).
Time Hint Extern 1000  => solve_ndisj: solve_ndisj.
