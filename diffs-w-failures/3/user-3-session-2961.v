Time From stdpp Require Export strings.
Time From stdpp Require Import relations numbers.
Time From Coq Require Import Ascii.
Time Set Default Proof Using "Type".
Time Class Pretty A :=
         pretty : A \226\134\146 string.
Time
Definition pretty_N_char (x : N) : ascii :=
  match x with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | _ => "9"
  end%char%N.
Time
Fixpoint pretty_N_go_help (x : N) (acc : Acc (<)%N x) 
(s : string) : string :=
  match decide (0 < x)%N with
  | left H =>
      pretty_N_go_help (x `div` 10)%N (Acc_inv acc (N.div_lt x 10 H eq_refl))
        (String (pretty_N_char (x `mod` 10)) s)
  | right _ => s
  end.
Time
Definition pretty_N_go (x : N) : string \226\134\146 string :=
  pretty_N_go_help x (wf_guard 32 N.lt_wf_0 x).
Time Lemma pretty_N_go_0 s : pretty_N_go 0 s = s.
Time Proof.
Time done.
Time Qed.
Time
Lemma pretty_N_go_help_irrel x acc1 acc2 s :
  pretty_N_go_help x acc1 s = pretty_N_go_help x acc2 s.
Time Proof.
Time (revert x acc1 acc2 s; fix FIX 2; intros x [acc1] [acc2] s; simpl).
Time (destruct (decide (0 < x)%N); auto).
Time Qed.
Time
Lemma pretty_N_go_step x s :
  (0 < x)%N
  \226\134\146 pretty_N_go x s =
    pretty_N_go (x `div` 10) (String (pretty_N_char (x `mod` 10)) s).
Time Proof.
Time (unfold pretty_N_go; intros; destruct (wf_guard 32 N.lt_wf_0 x)).
Time (destruct wf_guard).
Time (unfold pretty_N_go_help at 1; fold pretty_N_go_help).
Time by destruct (decide (0 < x)%N); auto using pretty_N_go_help_irrel.
Time Qed.
Time Instance pretty_N : (Pretty N) := (\206\187 x, pretty_N_go x ""%string).
Time Lemma pretty_N_unfold x : pretty x = pretty_N_go x "".
Time Proof.
Time done.
Time Qed.
Time Instance pretty_N_inj : (Inj (=@{N} ) (=) pretty).
Time Proof.
Time
(assert
  (\226\136\128 x y, x < 10 \226\134\146 y < 10 \226\134\146 pretty_N_char x = pretty_N_char y \226\134\146 x = y)%N).
Time {
Time (compute; intros).
Time by repeat discriminate || case_match.
Time }
Time
(cut
  (\226\136\128 x y s s',
     pretty_N_go x s = pretty_N_go y s'
     \226\134\146 String.length s = String.length s' \226\134\146 x = y \226\136\167 s = s')).
Time {
Time (intros help x y Hp).
Time (eapply (help x y "" ""); [ by rewrite <- !pretty_N_unfold | done ]).
Time }
Time
(assert (help : \226\136\128 x s, \194\172 String.length (pretty_N_go x s) < String.length s)).
Time {
Time setoid_rewrite  <- Nat.le_ngt.
Time (intros x; induction (N.lt_wf_0 x) as [x _ IH]; intros s).
Time
(assert (x = 0 \226\136\168 0 < x)%N as [->| ?] by lia; [ by rewrite pretty_N_go_0 |  ]).
Time (rewrite pretty_N_go_step by done).
Time (etrans; [  | by eapply IH, N.div_lt ]; simpl; lia).
Time }
Time (intros x; induction (N.lt_wf_0 x) as [x _ IH]; intros y s s').
Time
(assert ((x = 0 \226\136\168 0 < x) \226\136\167 (y = 0 \226\136\168 0 < y))%N as [[->| ?] [->| ?]] by lia;
  rewrite ?pretty_N_go_0, ?pretty_N_go_step, ?(pretty_N_go_step y) by done).
Time {
Time done.
Time }
Time {
Time (intros -> Hlen; edestruct help; rewrite Hlen; simpl; lia).
Time }
Time {
Time (intros <- Hlen; edestruct help; rewrite <- Hlen; simpl; lia).
Time }
Time
(intros Hs Hlen; apply IH in Hs; destruct Hs; simplify_eq /=; split_and ?;
  auto using N.div_lt_upper_bound with lia).
Time (rewrite (N.div_mod x 10), (N.div_mod y 10) by done).
Time auto using N.mod_lt with f_equal.
Time Qed.
Time
Instance pretty_Z : (Pretty Z) :=
 (\206\187 x,
    match x with
    | Z0 => ""
    | Zpos x => pretty (Npos x)
    | Zneg x => "-" +:+ pretty (Npos x)
    end%string).
Time Instance pretty_nat : (Pretty nat) := (\206\187 x, pretty (N.of_nat x)).
Time Instance pretty_nat_inj : (Inj (=@{nat} ) (=) pretty).
Time Proof.
Time (apply _).
Time Qed.
