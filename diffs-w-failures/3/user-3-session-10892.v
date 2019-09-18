Time From stdpp Require Export list.
Time From stdpp Require Import relations pretty.
Time #[program]
Definition inj_infinite `{Infinite A} {B} (f : A \226\134\146 B) 
  (g : B \226\134\146 option A) (Hgf : \226\136\128 x, g (f x) = Some x) : 
  Infinite B := {| infinite_fresh := f \226\136\152 fresh \226\136\152 omap g |}.
Time Next Obligation.
Time (intros A ? B f g Hfg xs Hxs; simpl in *).
Time (apply (infinite_is_fresh (omap g xs)), elem_of_list_omap; eauto).
Time Qed.
Time Next Obligation.
Time solve_proper.
Time Qed.
Time Section search_infinite.
Time Context {B} (f : nat \226\134\146 B) `{!Inj (=) (=) f} `{!EqDecision B}.
Time Let R (xs : list B) (n1 n2 : nat) := n2 < n1 \226\136\167 f (n1 - 1) \226\136\136 xs.
Time Lemma search_infinite_step xs n : f n \226\136\136 xs \226\134\146 R xs (1 + n) n.
Time Proof.
Time (split; [ lia |  ]).
Time (replace (1 + n - 1) with n by lia; eauto).
Time Qed.
Time Lemma search_infinite_R_wf xs : wf (R xs).
Time Proof.
Time revert xs.
Time
(assert
  (help : \226\136\128 xs n n', Acc (R (filter (\226\137\160f n') xs)) n \226\134\146 n' < n \226\134\146 Acc (R xs) n)).
Time {
Time (induction 1 as [n _ IH]).
Time (constructor; intros n2 [? ?]).
Time (apply IH; [  | lia ]).
Time (split; [ done |  ]).
Time (apply elem_of_list_filter; naive_solver lia).
Time }
Time (intros xs).
Time (induction (well_founded_ltof _ length xs) as [xs _ IH]).
Time (intros n1; constructor; intros n2 [Hn Hs]).
Time (apply help with (n2 - 1); [  | lia ]).
Time (apply IH).
Time (eapply filter_length_lt; eauto).
Time Qed.
Time
Definition search_infinite_go (xs : list B) (n : nat)
  (go : \226\136\128 n', R xs n' n \226\134\146 B) : B :=
  let x := f n in
  match decide (x \226\136\136 xs) with
  | left Hx => go (S n) (search_infinite_step xs n Hx)
  | right _ => x
  end.
Time #[program]
Definition search_infinite : Infinite B :=
  {|
  infinite_fresh := fun xs =>
                    Fix_F _ (search_infinite_go xs)
                      (wf_guard 32 (search_infinite_R_wf xs) 0) |}.
Time Next Obligation.
Time (intros xs).
Time (unfold fresh).
Time (generalize 0, (wf_guard 32 (search_infinite_R_wf xs) 0)).
Time revert xs.
Time
(fix FIX 3; intros xs n [?]; simpl; unfold search_infinite_go at 1; simpl).
Time (destruct (decide _); auto).
Time Qed.
Time Next Obligation.
Time (intros xs1 xs2 Hxs).
Time (unfold fresh).
Time (generalize (wf_guard 32 (search_infinite_R_wf xs1) 0)).
Time (generalize (wf_guard 32 (search_infinite_R_wf xs2) 0)).
Time (generalize 0).
Time fix FIX 2.
Time (intros n [acc1] [acc2]; simpl; unfold search_infinite_go).
Time
(destruct (decide (_ \226\136\136 xs1)) as [H1| H1], (decide (_ \226\136\136 xs2)) as [H2| H2];
  auto).
Time -
Time (destruct H2).
Time by rewrite <- Hxs.
Time -
Time (destruct H1).
Time by rewrite Hxs.
Time Qed.
Time End search_infinite.
Time Section max_infinite.
Time Context {A} (f : A \226\134\146 A \226\134\146 A) (a : A) (lt : relation A).
Time Context (HR : \226\136\128 x, \194\172 lt x x).
Time Context (HR1 : \226\136\128 x y, lt x (f x y)).
Time Context (HR2 : \226\136\128 x x' y, lt x x' \226\134\146 lt x (f y x')).
Time Context (Hf : \226\136\128 x x' y, f x (f x' y) = f x' (f x y)).
Time #[program]
Definition max_infinite : Infinite A := {| infinite_fresh := foldr f a |}.
Time Next Obligation.
Time (cut (\226\136\128 xs x, x \226\136\136 xs \226\134\146 lt x (foldr f a xs))).
Time {
Time (intros help xs []%HR%help).
Time }
Time (induction 1; simpl; auto).
Time Qed.
Time Next Obligation.
Time by apply (foldr_permutation_proper _ _ _).
Time Qed.
Time End max_infinite.
Time #[program]
Instance nat_infinite : (Infinite nat) :=
 (max_infinite (Nat.max \226\136\152 S) 0 (<) _ _ _ _).
Time Solve Obligations with (intros; simpl; lia).
Time #[program]
Instance N_infinite : (Infinite N) :=
 (max_infinite (N.max \226\136\152 N.succ) 0%N N.lt _ _ _ _).
Time Solve Obligations with (intros; simpl; lia).
Time #[program]
Instance positive_infinite : (Infinite positive) :=
 (max_infinite (Pos.max \226\136\152 Pos.succ) 1%positive Pos.lt _ _ _ _).
Time Solve Obligations with (intros; simpl; lia).
Time #[program]
Instance Z_infinite : (Infinite Z) :=
 (max_infinite (Z.max \226\136\152 Z.succ) 0%Z Z.lt _ _ _ _).
Time Solve Obligations with (intros; simpl; lia).
Time
Instance option_infinite  `{Infinite A}: (Infinite (option A)) :=
 (inj_infinite Some id (\206\187 _, eq_refl)).
Time
Instance sum_infinite_l  `{Infinite A} {B}: (Infinite (A + B)) :=
 (inj_infinite inl (maybe inl) (\206\187 _, eq_refl)).
Time
Instance sum_infinite_r  {A} `{Infinite B}: (Infinite (A + B)) :=
 (inj_infinite inr (maybe inr) (\206\187 _, eq_refl)).
Time
Instance prod_infinite_l  `{Infinite A} `{Inhabited B}: 
 (Infinite (A * B)) :=
 (inj_infinite (,inhabitant) (Some \226\136\152 fst) (\206\187 _, eq_refl)).
Time
Instance prod_infinite_r  `{Inhabited A} `{Infinite B}: 
 (Infinite (A * B)) :=
 (inj_infinite (inhabitant,) (Some \226\136\152 snd) (\206\187 _, eq_refl)).
Time #[program]
Instance list_infinite  `{Inhabited A}: (Infinite (list A)) :=
 {|
 infinite_fresh := fun xxs => replicate (fresh (length <$> xxs)) inhabitant |}.
Time Next Obligation.
Time (intros A ? xs ?).
Time (destruct (infinite_is_fresh (length <$> xs))).
Time (apply elem_of_list_fmap).
Time (eexists; split; [  | done ]).
Time (unfold fresh).
Time by rewrite replicate_length.
Time Qed.
Time Next Obligation.
Time (unfold fresh).
Time by intros A ? xs1 xs2 ->.
Time Qed.
Time #[program]
Instance string_infinite : (Infinite string) := (search_infinite pretty).
