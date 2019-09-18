Time From Transitions Require Import Relations.
Time From iris.algebra Require Export auth functions csum excl.
Time Require Export CSL.WeakestPre CSL.Lifting CSL.Counting.
Time From iris.proofmode Require Export tactics.
Time From Perennial Require Export Lib.
Time
Class tregG \206\163 :=
 TRegG {treg_counter_inG :>
         inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))));
        treg_name : gname}.
Time Arguments treg_name {_}.
Time Section thread_reg.
Time Context `{tr : tregG \206\163}.
Time Definition Registered := own (treg_name tr) (Cinl (Count (- 1)%Z)).
Time Definition AllDone := own (treg_name tr) (Cinr (\226\151\175 Excl' tt)).
Time Lemma AllDone_Register_excl : AllDone -\226\136\151 Registered -\226\136\151 False.
Time Proof.
Time iIntros "Had Hreg".
Time iDestruct (own_valid_2 with "Had Hreg") as % [].
Time Qed.
Time End thread_reg.
Time
Definition thread_count_interp {\206\163} {tr : tregG \206\163} :=
  \206\187 n,
    match n with
    | 1 =>
        own (treg_name tr) (Cinl (Count 1))
        \226\136\168 own (treg_name tr) (Cinr (\226\151\143 Excl' tt))
    | _ => own (treg_name tr) (Cinl (Count n))
    end%I.
Time Module Reg_wp.
Time Section Reg_wp.
Time Context {OpT} {\206\155 : Layer OpT} `{IRIS : irisG OpT \206\155 \206\163}.
Time Context `{!tregG \206\163}.
Time
Lemma fst_lift_puts_inv {A} {B} f (n1 : A) (\207\1311 : B) 
  n2 \207\1312 t :
  fst_lift (puts f) (n1, \207\1311) (Val (n2, \207\1312) t) \226\134\146 n2 = f n1 \226\136\167 \207\1312 = \207\1311 \226\136\167 t = tt.
Time Proof.
Time (intros [Hput ?]).
Time (inversion Hput; subst; auto).
Time Qed.
Time Context (Interp : OpState \206\155 \226\134\146 iProp \206\163).
Time
Context
 (Hinterp1 : \226\136\128 n \207\131, state_interp (n, \207\131) -\226\136\151 thread_count_interp n \226\136\151 Interp \207\131).
Time
Context
 (Hinterp2 : \226\136\128 n \207\131, thread_count_interp n \226\136\151 Interp \207\131 -\226\136\151 state_interp (n, \207\131)).
Time
Lemma wp_spawn {T} s E (e : proc _ T) \206\166 :
  \226\150\183 Registered
  -\226\136\151 \226\150\183 (Registered -\226\136\151 WP (let! _ <- e; Unregister)%proc @ s; \226\138\164 {{ _, True }})
     -\226\136\151 \226\150\183 (Registered -\226\136\151 \206\166 tt) -\226\136\151 WP Spawn e @ s; E {{ \206\166 }}.
Time Proof.
Time iIntros "Hreg He H\206\166".
Time iApply wp_lift_atomic_step.
Time {
Time auto.
Time }
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; intuition).
Time iPureIntro.
Time (eapply spawn_non_errorable).
Time }
Time iIntros ( e2 (n', \207\1312) ? Hstep ) "!>".
Time (destruct Hstep as ([], ((?, ?), (Hput, Hpure)))).
Time (inversion Hpure).
Time subst.
Time (apply fst_lift_puts_inv in Hput as (?, (?, ?)); subst).
Time iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".
Time
iAssert (own (treg_name _) (Cinl (Count n)) \226\136\151 Registered)%I with
 "[Hown Hreg]" as "(Hown&Hreg)".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide (n = 1)) as [->| ] ; last 
 first).
Time {
Time (destruct n as [| [| n]]; try lia; iFrame).
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hown" as "[Hown|Hown]" ; first 
 by iFrame).
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time }
Time
iAssert (own (treg_name _) (Cinl (Count (S n))) \226\136\151 Registered)%I with "[Hown]"
 as "(Hown&Hreg')".
Time {
Time rewrite -own_op -Cinl_op counting_op' //=.
Time (repeat destruct decide; try lia).
Time replace (S n + - 1)%Z with n : Z by lia.
Time done.
Time }
Time iModIntro.
Time (simpl).
Time iFrame.
Time iSplitL "Hown Hrest".
Time {
Time iApply Hinterp2.
Time (destruct n; iFrame).
Time }
Time iSplitL "Hreg H\206\166".
Time {
Time by iApply "H\206\166".
Time }
Time rewrite right_id.
Time by iApply "He".
Time Qed.
Time
Lemma wp_unregister s E :
  {{{ \226\150\183 Registered }}} Unregister @ s; E {{{ RET tt; True}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hreg H\206\166".
Time iApply wp_lift_atomic_step.
Time {
Time auto.
Time }
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; intuition).
Time iPureIntro.
Time (eapply unregister_non_errorable).
Time }
Time iIntros ( e2 (n', \207\1312) ? Hstep ) "!>".
Time (destruct Hstep as ([], ((?, ?), (Hput, Hpure)))).
Time (inversion Hpure).
Time subst.
Time (apply fst_lift_puts_inv in Hput as (?, (?, ?)); subst).
Time iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".
Time
iAssert
 (\226\136\131 n', \226\140\156n = S n'\226\140\157 \226\136\151 own (treg_name _) (Cinl (Count n)) \226\136\151 Registered)%I with
 "[Hown Hreg]" as ( n' Heq ) "(Hown&Hreg)".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide (n = 1)) as [->| ] ; last 
 first).
Time {
Time (destruct n as [| [| n]]; try lia).
Time -
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time -
Time iExists (S n).
Time (iFrame; eauto).
Time }
Time iExists O.
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hown" as "[Hown|Hown]" ; first 
 by iFrame).
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time }
Time subst.
Time
iAssert (own (treg_name _) (Cinl (Count n')))%I with "[Hown Hreg]" as "Hown".
Time {
Time iCombine "Hown Hreg" as "Hown".
Time rewrite -Cinl_op counting_op' //=.
Time (repeat destruct decide; try lia).
Time replace (S n' + - 1)%Z with n' : Z by lia.
Time done.
Time }
Time iModIntro.
Time (simpl).
Time iFrame.
Time iSplitL "Hown Hrest".
Time {
Time iApply Hinterp2.
Time (destruct n' as [| [| n']]; iFrame).
Time }
Time rewrite right_id.
Time by iApply "H\206\166".
Time Qed.
Time
Lemma wp_wait s E : {{{ \226\150\183 Registered }}} Wait @ s; E {{{ RET tt; AllDone}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hreg H\206\166".
Time iApply wp_lift_atomic_step.
Time {
Time auto.
Time }
Time iIntros ( (n, \207\131) ) "Hown".
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; intuition).
Time iPureIntro.
Time (eapply wait_non_errorable).
Time }
Time iIntros ( e2 (n', \207\1312) ? Hstep ) "!>".
Time (destruct Hstep as ([], ((?, ?), (Hput, Hpure)))).
Time (inversion Hpure).
Time subst.
Time (inversion Hput as [Hsuch Heq]).
Time subst.
Time (inversion Hsuch; subst).
Time iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".
Time
iAssert (own (treg_name _) (Cinl (Count 1)) \226\136\151 Registered)%I with
 "[Hown Hreg]" as "(Hown&Hreg)".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hown" as "[Hown|Hown]" ; first 
 by iFrame).
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time }
Time subst.
Time
iAssert (own (treg_name _) (Cinl (Count O)))%I with "[Hown Hreg]" as "Hown".
Time {
Time iCombine "Hown Hreg" as "Hown".
Time rewrite -Cinl_op counting_op' //=.
Time }
Time iMod (own_update with "Hown") as "(Hdone&Hown)".
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply cmra_update_exclusive with
   (y := Cinr (\226\151\175 Excl' tt) \226\139\133 Cinr (\226\151\143 Excl' tt)) =>//=).
Time rewrite -Cinr_op comm.
Time (apply auth_both_valid; split; done).
Time }
Time iModIntro.
Time iSplitL "Hown Hrest".
Time {
Time (iApply Hinterp2; iFrame).
Time }
Time (simpl).
Time rewrite right_id.
Time by iApply "H\206\166".
Time Qed.
Time End Reg_wp.
Time End Reg_wp.
