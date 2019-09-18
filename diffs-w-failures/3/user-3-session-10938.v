Time From stdpp Require Import gmap.
Time From iris.bi Require Export bi.
Time Set Default Proof Using "Type".
Time Import bi.
Time Module bi_reflection.
Time Section bi_reflection.
Time Context {PROP : bi}.
Time
Inductive expr :=
  | EEmp : expr
  | EVar : nat \226\134\146 expr
  | ESep : expr \226\134\146 expr \226\134\146 expr.
Time
Fixpoint eval (\206\163 : list PROP) (e : expr) : PROP :=
  match e with
  | EEmp => emp
  | EVar n => default emp (\206\163 !! n)
  | ESep e1 e2 => eval \206\163 e1 \226\136\151 eval \206\163 e2
  end%I.
Time
Fixpoint flatten (e : expr) : list nat :=
  match e with
  | EEmp => []
  | EVar n => [n]
  | ESep e1 e2 => flatten e1 ++ flatten e2
  end.
Time Notation eval_list \206\163 l:= ([\226\136\151 list] n \226\136\136 l, default emp (\206\163 !! n))%I.
Time Lemma eval_flatten \206\163 e : eval \206\163 e \226\138\163\226\138\162 eval_list \206\163 (flatten e).
Time Proof.
Time
(induction e as [| | e1 IH1 e2 IH2]; rewrite /= ?right_id ?big_opL_app ?IH1
  ?IH2 //).
Time Qed.
Time
Lemma flatten_entails `{BiAffine PROP} \206\163 e1 e2 :
  flatten e2 \226\138\134+ flatten e1 \226\134\146 eval \206\163 e1 \226\138\162 eval \206\163 e2.
Time Proof.
Time (intros).
Time rewrite !eval_flatten.
Time by apply big_sepL_submseteq.
Time Qed.
Time
Lemma flatten_equiv \206\163 e1 e2 :
  flatten e2 \226\137\161\226\130\154 flatten e1 \226\134\146 eval \206\163 e1 \226\138\163\226\138\162 eval \206\163 e2.
Time Proof.
Time (intros He).
Time by rewrite !eval_flatten He.
Time Qed.
Time
Fixpoint prune (e : expr) : expr :=
  match e with
  | EEmp => EEmp
  | EVar n => EVar n
  | ESep e1 e2 =>
      match prune e1, prune e2 with
      | EEmp, e2' => e2'
      | e1', EEmp => e1'
      | e1', e2' => ESep e1' e2'
      end
  end.
Time Lemma flatten_prune e : flatten (prune e) = flatten e.
Time Proof.
Time (induction e as [| | e1 IH1 e2 IH2]; simplify_eq /=; auto).
Time rewrite -IH1 -IH2.
Time by repeat case_match; rewrite ?right_id_L.
Time Qed.
Time Lemma prune_correct \206\163 e : eval \206\163 (prune e) \226\138\163\226\138\162 eval \206\163 e.
Time Proof.
Time by rewrite !eval_flatten flatten_prune.
Time Qed.
Time
Fixpoint cancel_go (n : nat) (e : expr) : option expr :=
  match e with
  | EEmp => None
  | EVar n' => if decide (n = n') then Some EEmp else None
  | ESep e1 e2 =>
      match cancel_go n e1 with
      | Some e1' => Some (ESep e1' e2)
      | None => ESep e1 <$> cancel_go n e2
      end
  end.
Time
Definition cancel (ns : list nat) (e : expr) : option expr :=
  prune <$> fold_right (mbind \226\136\152 cancel_go) (Some e) ns.
Time
Lemma flatten_cancel_go e e' n :
  cancel_go n e = Some e' \226\134\146 flatten e \226\137\161\226\130\154 n :: flatten e'.
Time Proof.
Time
(revert e'; induction e as [| | e1 IH1 e2 IH2]; intros;
  repeat simplify_option_eq || case_match; auto).
Time -
Time by rewrite IH1 //.
Time -
Time by rewrite IH2 // Permutation_middle.
Time Qed.
Time
Lemma flatten_cancel e e' ns :
  cancel ns e = Some e' \226\134\146 flatten e \226\137\161\226\130\154 ns ++ flatten e'.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite /cancel fmap_Some =>-
  [{e'} e' [He {+}->]]; rewrite flatten_prune).
Time
(revert e' He; <ssreflect_plugin::ssrtclintros@0> 
  induction ns as [| n ns IH] =>e' He; simplify_option_eq; auto).
Time (rewrite Permutation_middle -flatten_cancel_go //; eauto).
Time Qed.
Time
Lemma cancel_entails \206\163 e1 e2 e1' e2' ns :
  cancel ns e1 = Some e1'
  \226\134\146 cancel ns e2 = Some e2'
    \226\134\146 (eval \206\163 e1' \226\138\162 eval \206\163 e2') \226\134\146 eval \206\163 e1 \226\138\162 eval \206\163 e2.
Time Proof.
Time (intros ? ?).
Time rewrite !eval_flatten.
Time
(rewrite (flatten_cancel e1 e1' ns) // (flatten_cancel e2 e2' ns) //; csimpl).
Time rewrite !big_opL_app.
Time (apply sep_mono_r).
Time Qed.
Time
Fixpoint to_expr (l : list nat) : expr :=
  match l with
  | [] => EEmp
  | [n] => EVar n
  | n :: l => ESep (EVar n) (to_expr l)
  end.
Time Arguments to_expr !_ / : simpl nomatch.
Time Lemma eval_to_expr \206\163 l : eval \206\163 (to_expr l) \226\138\163\226\138\162 eval_list \206\163 l.
Time Proof.
Time (induction l as [| n1 [| n2 l] IH]; csimpl; rewrite ?right_id //).
Time by rewrite IH.
Time Qed.
Time
Lemma split_l \206\163 e ns e' :
  cancel ns e = Some e' \226\134\146 eval \206\163 e \226\138\163\226\138\162 eval \206\163 (to_expr ns) \226\136\151 eval \206\163 e'.
Time Proof.
Time (intros He%flatten_cancel).
Time by rewrite eval_flatten He big_opL_app eval_to_expr eval_flatten.
Time Qed.
Time
Lemma split_r \206\163 e ns e' :
  cancel ns e = Some e' \226\134\146 eval \206\163 e \226\138\163\226\138\162 eval \206\163 e' \226\136\151 eval \206\163 (to_expr ns).
Time Proof.
Time (intros).
Time rewrite /= comm.
Time by apply split_l.
Time Qed.
Time Class Quote (\206\1631 \206\1632 : list PROP) (P : PROP) (e : expr) :={}.
Time #[global]Instance quote_True  \206\163: (Quote \206\163 \206\163 emp%I EEmp) := { }.
Time #[global]
Instance quote_var  \206\1631 \206\1632 P i:
 (rlist.QuoteLookup \206\1631 \206\1632 P i \226\134\146 Quote \206\1631 \206\1632 P (EVar i)) |1000 := { }.
Time #[global]
Instance quote_sep  \206\1631 \206\1632 \206\1633 P1 P2 e1 e2:
 (Quote \206\1631 \206\1632 P1 e1
  \226\134\146 Quote \206\1632 \206\1633 P2 e2 \226\134\146 Quote \206\1631 \206\1633 (P1 \226\136\151 P2)%I (ESep e1 e2)) := { }.
Time Class QuoteArgs (\206\163 : list PROP) (Ps : list PROP) (ns : list nat) :={}.
Time #[global]Instance quote_args_nil  \206\163: (QuoteArgs \206\163 nil nil) := { }.
Time #[global]
Instance quote_args_cons  \206\163 Ps P ns n:
 (rlist.QuoteLookup \206\163 \206\163 P n
  \226\134\146 QuoteArgs \206\163 Ps ns \226\134\146 QuoteArgs \206\163 (P :: Ps) (n :: ns)) := { }.
Time End bi_reflection.
Time
Ltac
 quote :=
  match goal with
  | |- ?P1 \226\138\162 ?P2 =>
        lazymatch type of (_ : Quote [] _ P1 _) with
        | Quote _ ?\206\1632 _ ?e1 =>
            lazymatch type of (_ : Quote \206\1632 _ P2 _) with
            | Quote _ ?\206\1633 _ ?e2 =>
                change_no_check (eval \206\1633 e1 \226\138\162 eval \206\1633 e2)
            end
        end
  end.
Time
Ltac
 quote_l :=
  match goal with
  | |- ?P1 \226\138\162 ?P2 =>
        lazymatch type of (_ : Quote [] _ P1 _) with
        | Quote _ ?\206\1632 _ ?e1 => change_no_check (eval \206\1632 e1 \226\138\162 P2)
        end
  end.
Time End bi_reflection.
Time
Tactic Notation "solve_sep_entails" :=
 (bi_reflection.quote; (first
   [ apply bi_reflection.flatten_entails
   | apply equiv_entails, bi_reflection.flatten_equiv ]);
   apply (bool_decide_unpack _); vm_compute; exact Logic.I).
Time
Tactic Notation "solve_sep_equiv" :=
 (bi_reflection.quote; apply bi_reflection.flatten_equiv;
   apply (bool_decide_unpack _); vm_compute; exact Logic.I).
Time
Ltac
 close_uPreds Ps tac :=
  let PROP := match goal with
              | |- @bi_entails ?PROP _ _ => PROP
              end in
  let rec go Ps Qs :=
   lazymatch Ps with
   | [] =>
       let Qs' := eval cbv[reverse rev_append] in (reverse Qs) in
       tac Qs'
   | ?P :: ?Ps => find_pat P ltac:(fun Q => go Ps (Q :: Qs))
   end
  in
  try match Ps with
      | [] => unify Ps @nil PROP
      end; go Ps (@nil PROP).
Time
Tactic Notation "cancel" constr(Ps) :=
 (bi_reflection.quote;
   (let \206\163 := match goal with
             | |- bi_reflection.eval ?\206\163 _ \226\138\162 _ => \206\163
             end in
    let ns' :=
     lazymatch type of (_ : bi_reflection.QuoteArgs \206\163 Ps _)
     with
     | bi_reflection.QuoteArgs _ _ ?ns' => ns'
     end
    in
    eapply bi_reflection.cancel_entails with (ns := ns');
     [ compute; reflexivity | compute; reflexivity | simpl ])).
Time
Tactic Notation "ecancel" open_constr(Ps) :=
 (close_uPreds Ps ltac:(fun Qs => cancel Qs)).
Time
Tactic Notation "to_front" open_constr(Ps) :=
 (close_uPreds Ps
   ltac:(fun Ps =>
           bi_reflection.quote_l;
            (let \206\163 := match goal with
                      | |- bi_reflection.eval ?\206\163 _ \226\138\162 _ => \206\163
                      end
             in
             let ns' :=
              lazymatch type of (_ : bi_reflection.QuoteArgs \206\163 Ps _)
              with
              | bi_reflection.QuoteArgs _ _ ?ns' => ns'
              end
             in
             <ssreflect_plugin::ssrtclseq@0> eapply entails_equiv_l ; first 
              apply bi_reflection.split_l with (ns := ns'); compute;
               reflexivity; simpl))).
Time
Tactic Notation "to_back" open_constr(Ps) :=
 (close_uPreds Ps
   ltac:(fun Ps =>
           bi_reflection.quote_l;
            (let \206\163 := match goal with
                      | |- bi_reflection.eval ?\206\163 _ \226\138\162 _ => \206\163
                      end
             in
             let ns' :=
              lazymatch type of (_ : bi_reflection.QuoteArgs \206\163 Ps _)
              with
              | bi_reflection.QuoteArgs _ _ ?ns' => ns'
              end
             in
             <ssreflect_plugin::ssrtclseq@0> eapply entails_equiv_l ; first 
              apply bi_reflection.split_r with (ns := ns'); compute;
               reflexivity; simpl))).
Time
Tactic Notation "sep_split" "right:" open_constr(Ps) :=
 (to_back Ps; apply sep_mono).
Time
Tactic Notation "sep_split" "left:" open_constr(Ps) :=
 (to_front Ps; apply sep_mono).
