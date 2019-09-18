Require Import List.
Require Import Definitions.Zip.
Require Import Proofs.Tactics.
Require Import Impl.Zip.
Lemma zip_fst : forall A B la lb lz, @Zip A B la lb lz -> map fst lz = la.
Proof.
(induction la; intros; inv H).
-
reflexivity.
-
(erewrite <- IHla; eauto).
reflexivity.
Qed.
Lemma zip_snd : forall A B lb la lz, @Zip A B la lb lz -> map snd lz = lb.
Proof.
(induction lb; intros; inv H).
-
reflexivity.
-
(erewrite <- IHlb; eauto).
reflexivity.
Qed.
Lemma zip_map : forall A B (l : list (A * B)), Zip (map fst l) (map snd l) l.
Proof.
(induction l).
-
constructor.
-
(destruct a).
constructor.
assumption.
Qed.
Lemma zip_some :
  forall {A} {B} la lb lab, @zip A B la lb = Some lab -> @Zip A B la lb lab.
Proof.
(induction la; intros; simpl in *; repeat (break_match; try discriminate);
  inj; subst; constructor; auto).
Qed.
Lemma zip_none :
  forall {A} {B} la lb lab, @zip A B la lb = None -> ~ @Zip A B la lb lab.
Proof.
(induction la; intros; simpl in *; repeat (break_match; try discriminate);
  intuition; inversion_then eauto).
Qed.
Lemma zip_dec :
  forall {A} {B} la lb,
  {lab | @Zip A B la lb lab} + {(forall lab, ~ @Zip A B la lb lab)}.
Proof.
(intros).
(destruct (zip la lb) eqn:Z).
-
left.
(solve [ eauto using zip_some ]).
-
right.
(solve [ eauto using zip_none ]).
Qed.
