Time From iris.algebra Require Import auth.
Time
Require Export CSL.Refinement CSL.NamedDestruct ExMach.WeakestPre
  CSL.ProofModeClasses.
Time Unset Implicit Arguments.
Time Section ghost_var_helpers.
Time Context {A : ofeT} `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A}.
Time Context {\206\163} {Hin : inG \206\163 (authR (optionUR (exclR A)))}.
Time
Lemma ghost_var_alloc (a : A) :
  (|==> \226\136\131 \206\179, own \206\179 (\226\151\143 Excl' a) \226\136\151 own \206\179 (\226\151\175 Excl' a))%I.
Time Proof.
Time iMod (own_alloc (\226\151\143 Excl' a \226\139\133 \226\151\175 Excl' a)) as ( \206\179 ) "[H1 H2]".
Time {
Time (apply auth_both_valid; split; eauto).
Time econstructor.
Time }
Time iModIntro.
Time iExists \206\179.
Time iFrame.
Time Qed.
Time
Lemma ghost_var_agree \206\179 (a1 a2 : A) :
  own \206\179 (\226\151\143 Excl' a1) -\226\136\151 own \206\179 (\226\151\175 Excl' a2) -\226\136\151 \226\140\156a1 = a2\226\140\157.
Time Proof.
Time iIntros "H\206\1791 H\206\1792".
Time iDestruct (own_valid_2 with "H\206\1791 H\206\1792") as "H".
Time iDestruct "H" as % [<-%leibniz_equiv%Excl_included _]%auth_both_valid.
Time done.
Time Qed.
Time
Lemma ghost_var_update \206\179 (a1' a1 a2 : A) :
  own \206\179 (\226\151\143 Excl' a1)
  -\226\136\151 own \206\179 (\226\151\175 Excl' a2) ==\226\136\151 own \206\179 (\226\151\143 Excl' a1') \226\136\151 own \206\179 (\226\151\175 Excl' a1').
Time Proof.
Time iIntros "H\206\179\226\151\143 H\206\179\226\151\175".
Time
iMod (own_update_2 _ _ _ (\226\151\143 Excl' a1' \226\139\133 \226\151\175 Excl' a1') with "H\206\179\226\151\143 H\206\179\226\151\175") as
 "[$$]".
Time {
Time by apply auth_update, option_local_update, exclusive_local_update.
Time }
Time done.
Time Qed.
Time
Lemma named_ghost_var_update \206\179 (a1' a1 a2 : A) i1 
  i2 :
  named i1 (own \206\179 (\226\151\143 Excl' a1))
  -\226\136\151 named i2 (own \206\179 (\226\151\175 Excl' a2))
     ==\226\136\151 named i1 (own \206\179 (\226\151\143 Excl' a1')) \226\136\151 named i2 (own \206\179 (\226\151\175 Excl' a1')).
Time Proof.
Time (unbundle_names; apply ghost_var_update).
Time Qed.
Time End ghost_var_helpers.
Time
Instance from_exist_left_sep  {\206\163} {A} (\206\166 : A \226\134\146 iProp \206\163) 
 Q: (FromExist ((\226\136\131 a, \206\166 a) \226\136\151 Q) (\206\187 a, \206\166 a \226\136\151 Q)%I).
Time Proof.
Time rewrite /FromExist.
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&$)".
Time (iExists _; eauto).
Time Qed.
Time
Instance from_exist_left_sep_later  {\206\163} {A} (\206\166 : A \226\134\146 iProp \206\163) 
 Q: (FromExist (\226\150\183 (\226\136\131 a, \206\166 a) \226\136\151 Q) (\206\187 a, \226\150\183 \206\166 a \226\136\151 Q)%I).
Time Proof.
Time rewrite /FromExist.
Time iIntros "H".
Time iDestruct "H" as ( ? ) "(?&$)".
Time (iExists _; eauto).
Time Qed.
Time
From iris.proofmode Require Import coq_tactics intro_patterns spec_patterns.
Time From iris.proofmode Require Import tactics.
Time From stdpp Require Import hlist pretty.
Time
Ltac
 unify_ghost :=
  match goal with
  | |-
    context [ environments.Esnoc _ (INamed ?auth_name) (own ?y (\226\151\143 Excl' ?x)) ]
    =>
        match goal with
        | |- context [ own y (\226\151\175 Excl' x) ] => fail 1
        | |-
          context [ environments.Esnoc _ (INamed ?frag_name)
                      (own y (\226\151\175 Excl' ?z)) ] =>
              let pat :=
               constr:([SIdent (INamed auth_name) nil;
                       SIdent (INamed frag_name) nil])
              in
              iDestruct (ghost_var_agree with pat) as % Hp;
               inversion_clear Hp; subst; [  ]
        end
  end.
