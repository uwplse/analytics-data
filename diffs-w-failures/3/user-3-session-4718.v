Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqDi4DIO"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Diffs "off".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Printing Width 69.
Set Silent.
From iris.algebra Require Import auth agree functions csum cmra.
From Armada.CSL Require Import Counting.
From iris.base_logic.lib Require Export own.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
Require Export CSL.Refinement CSL.NamedDestruct CSL.ProofModeClasses.
Require Eqdep.
Import uPred.
Class ghost_mapG (A : ofeT) \206\163 `{@LeibnizEquiv _ A.(ofe_equiv)}
`{OfeDiscrete A} :={ghost_map_inG :>
                     inG \206\163
                       (authR
                          (optionUR (prodR countingR (agreeR A))))}.
Definition ghost_map\206\163 (A : ofeT) `{@LeibnizEquiv _ A.(ofe_equiv)}
  `{OfeDiscrete A} : gFunctors :=
  #[ GFunctor (authR (optionUR (prodR countingR (agreeR A))))].
Instance subG_ghost_mapG  (A : ofeT) \206\163
 `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A}:
 (subG (ghost_map\206\163 A) \206\163 \226\134\146 ghost_mapG A \206\163).
Proof.
solve_inG.
Qed.
Section ghost_var_helpers.
Context {A : ofeT} `{hGMG : @ghost_mapG A \206\163 H1 H2}.
Definition ghost_mapsto (\206\179 : gname) (n : Z) (v : A) : 
  iProp \206\163 := (own \206\179 (\226\151\175 Some (Count n, to_agree v)))%I.
Definition ghost_mapsto_auth (\206\179 : gname) (v : A) : 
  iProp \206\163 := own \206\179 (\226\151\143 Some (Count 0, to_agree v)).
End ghost_var_helpers.
#[local]
Notation "l \226\151\143\226\134\166 v" := (ghost_mapsto_auth l v)
  (at level 20, format "l  \226\151\143\226\134\166  v") : bi_scope.
#[local]
Notation "l \226\134\166{ q } v" := (ghost_mapsto l q v)
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  v") : bi_scope.
#[local]
Notation "l \226\134\166 v" := (ghost_mapsto l 0 v) (at level 20) : bi_scope.
#[local]
Notation "l \226\134\166{ q } -" := (\226\136\131 v, l \226\134\166{q} v)%I
  (at level 20, q  at level 50, format "l  \226\134\166{ q }  -") : bi_scope.
#[local]Notation "l \226\134\166 -" := (l \226\134\166{0} -)%I (at level 20) : bi_scope.
Section ghost_var_helpers.
Context {A} {\206\163} `{ghost_mapG A \206\163}.
Lemma ghost_var_alloc (a : A) : (|==> \226\136\131 \206\179, \206\179 \226\151\143\226\134\166 a \226\136\151 \206\179 \226\134\166 a)%I.
Proof.
iMod
 (own_alloc
    (\226\151\143 Some (Count 0, to_agree a) \226\139\133 \226\151\175 Some (Count 0, to_agree a)))
 as ( \206\179 ) "[H1 H2]".
{
(apply auth_both_valid; split; eauto).
(split; econstructor).
}
iModIntro.
iExists \206\179.
iFrame.
Qed.
Lemma ghost_var_bulk_alloc {L} {V} `{Countable L} 
  (m : gmap L V) (f : L \226\134\146 V \226\134\146 A) :
  (|==> \226\136\131 \206\147 : gmap L gname,
          \226\140\156dom (gset L) \206\147 = dom (gset L) m\226\140\157
          \226\136\151 ([\226\136\151 map] k\226\134\166v \226\136\136 m, \226\136\131 \206\179,
                                \226\140\156\206\147 !! k = Some \206\179\226\140\157
                                \226\136\151 \206\179 \226\151\143\226\134\166 f k v \226\136\151 \206\179 \226\134\166 f k v))%I.
Proof.
iInduction m as [| k v] "IH" using map_ind.
-
iExists \226\136\133.
iSplitL "".
{
by rewrite ?dom_empty_L.
}
{
by iApply big_sepM_empty.
}
-
iMod "IH" as ( \206\147 Hdom ) "Hmap".
iMod (ghost_var_alloc (f k v)) as ( \206\179 ) "H".
iModIntro.
iExists (<[k:=\206\179]> \206\147).
iSplitL "".
{
iPureIntro.
rewrite ?dom_insert_L Hdom //.
}
{
(iApply big_sepM_insert; auto).
iSplitL "H".
{
iExists \206\179.
rewrite lookup_insert.
by iFrame.
}
{
(<ssreflect_plugin::ssrtclseq@0> iApply big_sepM_mono ; last  eauto).
iIntros ( k' x' Hin ) "H".
(rewrite lookup_insert_ne; auto).
(intros ->).
congruence.
}
}
Qed.
Lemma ghost_var_agree \206\179 (a1 a2 : A) q :
  \206\179 \226\151\143\226\134\166 a1 -\226\136\151 \206\179 \226\134\166{q} a2 -\226\136\151 \226\140\156a1 = a2\226\140\157.
Proof.
iIntros "H\206\1791 H\206\1792".
iDestruct (own_valid_2 with "H\206\1791 H\206\1792") as % Hval.
(apply auth_both_valid in Hval as (Hincl, ?)).
(<ssreflect_plugin::ssrtclseq@0>
 apply option_included in Hincl
  as [| (p1, (p2, (Heq1, (Heq2, Hcase))))] ; first  by congruence).
(inversion Heq1; subst).
(inversion Heq2; subst).
(destruct Hcase as [(Heq1', Heq2')| Hincl]).
-
(apply to_agree_inj in Heq2').
eauto.
-
(apply prod_included in Hincl as (?, Heq2'%to_agree_included); eauto).
Qed.
Lemma ghost_var_auth_valid \206\179 (a1 a2 : A) :
  \206\179 \226\151\143\226\134\166 a1 -\226\136\151 \206\179 \226\151\143\226\134\166 a2 -\226\136\151 False.
Proof.
(apply wand_intro_r).
rewrite -own_op //=.
rewrite /op /cmra_op //= /auth_op //=.
rewrite -Some_op /op /cmra_op //= /excl_op /prod_op //= frac_op'.
rewrite own_valid discrete_valid.
(iIntros ( [] ); exfalso; eauto).
Qed.
Lemma ghost_valid \206\179 (q1 q2 : Z) (v1 v2 : A) :
  (q1 >= 0)%Z \226\134\146 (q2 >= 0)%Z \226\134\146 \206\179 \226\134\166{q1} v1 -\226\136\151 \206\179 \226\134\166{q2} v2 -\226\136\151 False.
Proof.
(intros).
(apply wand_intro_r).
rewrite -own_op -auth_frag_op own_valid discrete_valid.
(<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid
 /=).
rewrite -Some_op -pair_op.
(intros [Hcount ?]).
rewrite counting_op' //= in  {} Hcount.
(repeat <ssreflect_plugin::ssrtclintros@0> destruct decide =>//=).
lia.
Qed.
Lemma ghost_valid' \206\179 (q1 q2 : nat) (v1 v2 : A) :
  \206\179 \226\134\166{q1} v1 -\226\136\151 \206\179 \226\134\166{q2} v2 -\226\136\151 False.
Proof.
(intros).
(eapply ghost_valid; lia).
Qed.
Lemma ghost_var_agree2 \206\179 (a1 a2 : A) q1 q2 :
  \206\179 \226\134\166{q1} a1 -\226\136\151 \206\179 \226\134\166{q2} a2 -\226\136\151 \226\140\156a1 = a2\226\140\157.
Proof.
(apply wand_intro_r).
rewrite -own_op -auth_frag_op own_valid discrete_valid.
(<ssreflect_plugin::ssrtclintros@0> f_equiv =>/auth_frag_proj_valid
 /=).
rewrite -Some_op -pair_op.
(intros [_ Heq%agree_op_invL']).
eauto.
Qed.
Lemma read_split_join \206\179 (n : nat) (v : A) :
  \206\179 \226\134\166{n} v \226\138\163\226\138\162 \206\179 \226\134\166{S n} v \226\136\151 \206\179 \226\134\166{- 1} v.
Proof.
rewrite -own_op -auth_frag_op /ghost_mapsto.
f_equiv.
Unset Silent.
rewrite -Some_op -?pair_op.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqCsK9ud"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqAapfwb"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
Set Silent.
rewrite counting_op' //=.
replace (S n + - 1)%Z with n : Z by lia.
(assert (Hop : 0 \226\139\133 S n = S n) by auto).
replace (S n + - 1)%Z with n : Z by lia.
(repeat destruct (decide); try lia).
rewrite agree_idemp //=.
Qed.
Lemma read_split \206\179 (n : nat) (v : A) :
  \206\179 \226\134\166{n} v \226\138\162 \206\179 \226\134\166{S n} v \226\136\151 \206\179 \226\134\166{- 1} v.
Proof.
by rewrite read_split_join.
Qed.
Lemma read_join \206\179 (n : nat) (v : A) :
  \206\179 \226\134\166{S n} v \226\136\151 \206\179 \226\134\166{- 1} v \226\138\162 \206\179 \226\134\166{n} v.
Proof.
by rewrite -read_split_join.
Qed.
Lemma ghost_var_update \206\179 (a1' a1 a2 : A) :
  \206\179 \226\151\143\226\134\166 a1 -\226\136\151 \206\179 \226\134\166 a2 ==\226\136\151 \206\179 \226\151\143\226\134\166 a1' \226\136\151 \206\179 \226\134\166 a1'.
Proof.
iIntros "H\206\179\226\151\143 H\206\179\226\151\175".
iMod
 (own_update_2 _ _ _
    (\226\151\143 Some (Count 0, to_agree a1') \226\139\133 \226\151\175 Some (Count 0, to_agree a1'))
 with "H\206\179\226\151\143 H\206\179\226\151\175") as "[$$]".
{
by apply auth_update, option_local_update, exclusive_local_update.
}
done.
Qed.
Lemma named_ghost_var_update \206\179 (a1' a1 a2 : A) 
  i1 i2 :
  named i1 (\206\179 \226\151\143\226\134\166 a1)
  -\226\136\151 named i2 (\206\179 \226\134\166 a2) ==\226\136\151 named i1 (\206\179 \226\151\143\226\134\166 a1') \226\136\151 named i2 (\206\179 \226\134\166 a1').
Proof.
(unbundle_names; apply ghost_var_update).
Qed.
End ghost_var_helpers.
From iris.proofmode Require Import coq_tactics intro_patterns
  spec_patterns.
From iris.proofmode Require Import tactics.
From stdpp Require Import hlist pretty.
Ltac
 unify_ghost :=
  match goal with
  | |- context [ environments.Esnoc _ ?auth_name (?y \226\151\143\226\134\166 ?x) ] =>
        match goal with
        | |- context [ ghost_mapsto y _ x ] => fail 1
        | |-
          context [ environments.Esnoc _ ?frag_name (y \226\134\166{?q} ?z) ]
          =>
              let pat :=
               constr:([SIdent auth_name nil; SIdent frag_name nil])
              in
              iDestruct (ghost_var_agree with pat) as % Hp;
               inversion_clear Hp; subst; [  ]
        end
  end.
Module test.
Section test.
Context {\206\163} `{ghost_mapG A \206\163}.
Lemma test \206\179 q (v1 v2 : A) : \206\179 \226\151\143\226\134\166 v1 -\226\136\151 \206\179 \226\134\166{q} v2 -\226\136\151 \226\140\156v1 = v2\226\140\157.
Proof.
iIntros "H1 H2".
by unify_ghost.
Qed.
End test.
Unset Silent.
End test.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqnxMs7k"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect
"/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqOUbuBh"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Timeout 1 Print LoadPath.
