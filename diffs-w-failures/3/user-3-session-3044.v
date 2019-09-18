Time From Transitions Require Import Relations.
Time Require Import Spec.Proc.
Time From iris.algebra Require Export auth functions csum excl.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time From Transitions Require Import Relations.
Time Require Import CSL.WeakestPre CSL.Lifting.
Time Require Export CSL.WeakestPre CSL.Lifting CSL.Counting.
Time From iris.algebra Require Import auth frac agree gmap list excl.
Time From iris.base_logic.lib Require Import invariants.
Time From iris.proofmode Require Import tactics.
Time From iris.proofmode Require Export tactics.
Time #[global]Unset Implicit Arguments.
Time Set Nested Proofs Allowed.
Time Definition procT {OpT} := {T : Type & proc OpT T}.
Time Canonical Structure procTC OpT := leibnizC (@procT OpT).
Time Canonical Structure StateC OpT (\206\155 : Layer OpT) := leibnizC (OpState \206\155).
Time Section ghost.
Time Context {OpT : Type \226\134\146 Type}.
Time Context {\206\155 : Layer OpT}.
Time Definition tpoolUR := gmapUR nat (exclR (procTC OpT)).
Time Definition stateUR := optionUR (exclR (StateC _ \206\155)).
Time From Armada Require Export Lib.
Time Definition cfgUR := prodUR tpoolUR stateUR.
Time Class cfgPreG (\206\163 : gFunctors) :={cfg_preG_inG :> inG \206\163 (authR cfgUR)}.
Time Class cfgG \206\163 :={cfg_inG :> inG \206\163 (authR cfgUR); cfg_name : gname}.
Time Definition cfg\206\163 : gFunctors := #[ GFunctor (authR cfgUR)].
Time Instance subG_cfgPreG  {\206\163}: (subG cfg\206\163 \206\163 \226\134\146 cfgPreG \206\163).
Time Proof.
Time solve_inG.
Time Qed.
Time
Fixpoint tpool_to_map_aux (tp : thread_pool OpT) (id : nat) :
gmap nat (@procT OpT) :=
  match tp with
  | [] => \226\136\133
  | e :: tp' => <[id:=e]> (tpool_to_map_aux tp' (S id))
  end.
Time Definition tpool_to_map tp := tpool_to_map_aux tp O.
Time Definition tpool_to_res tp := Excl <$> tpool_to_map tp : tpoolUR.
Time Definition sourceN := nroot.@"source".
Time Section ghost_spec.
Time Context `{cfgG \206\163} `{invG \206\163}.
Time
Definition tpool_mapsto {T} (j : nat) (e : proc OpT T) : 
  iProp \206\163 := own cfg_name (\226\151\175 ({[j := Excl (existT _ e : procTC OpT)]}, \206\181)).
Time
Definition source_cfg (\207\129 : thread_pool OpT * State \206\155) : 
  iProp \206\163 :=
  own cfg_name (\226\151\175 (tpool_to_res (fst \207\129), Some (Excl (snd (snd \207\129))))).
Time
Definition source_state (\207\131 : OpState \206\155) : iProp \206\163 :=
  own cfg_name (\226\151\175 (\226\136\133 : tpoolUR, Some (Excl \207\131))).
Time
Definition source_pool_map (tp : gmap nat {T : Type & proc OpT T}) :
  iProp \206\163 :=
  own cfg_name (\226\151\175 (Excl <$> tp : gmap nat (exclR (procTC OpT)), \206\181)).
Time
Definition source_inv (tp : thread_pool OpT) (\207\131 : OpState \206\155) : 
  iProp \206\163 :=
  (\226\136\131 tp' n \207\131',
     own cfg_name (\226\151\143 (tpool_to_res tp', Some (Excl \207\131')))
     \226\136\151 \226\140\156bind_star (exec_pool \206\155.(sem)) tp (1, \207\131) (Val (n, \207\131') tp')
        \226\136\167 \194\172 bind_star (exec_pool \206\155.(sem)) tp (1, \207\131) Err\226\140\157)%I.
Time
Definition source_ctx' \207\129 : iProp \206\163 :=
  inv sourceN (source_inv (fst \207\129) (snd \207\129)).
Time Definition source_ctx : iProp \206\163 := (\226\136\131 \207\129, source_ctx' \207\129)%I.
Time #[global]
Instance tpool_mapsto_timeless  {T} j (e : proc OpT T):
 (Timeless (tpool_mapsto j e)).
Time Proof.
Time (apply _).
Time
Class tregG \206\163 :=
 TRegG {treg_counter_inG :>
         inG \206\163 (csumR countingR (authR (optionUR (exclR unitC))));
        treg_name : gname}.
Time Qed.
Time #[global]Instance source_state_timeless  \207\131: (Timeless (source_state \207\131)).
Time Proof.
Time (apply _).
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
Time #[global]
Instance source_ctx'_persistent  \207\129: (Persistent (source_ctx' \207\129)).
Time Proof.
Time (apply _).
Time Qed.
Time #[global]Instance source_ctx_persistent : (Persistent source_ctx).
Time Proof.
Time (apply _).
Time Qed.
Time End ghost_spec.
Time Notation "j \226\164\135 e" := (tpool_mapsto j e) (at level 20) : bi_scope.
Time Section ghost_step.
Time Context `{invG \206\163}.
Time
Lemma tpool_to_map_lookup_aux tp id j e :
  tpool_to_map_aux tp id !! (id + j) = Some e \226\134\148 tp !! j = Some e.
Time Proof.
Time
(revert id j; <ssreflect_plugin::ssrtclintros@0> induction tp =>id j //=).
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
Time (destruct j).
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
Time *
Time rewrite //= Nat.add_0_r lookup_insert //=.
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
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite //= lookup_insert_ne //= ; last  by
 lia).
Time Proof.
Time iIntros "Hreg He H\206\166".
Time iApply wp_lift_atomic_step.
Time {
Time auto.
Time }
Time iIntros ( (n, \207\131) ) "Hown".
Time (replace (id + S j) with S id + j by lia; eauto).
Time iModIntro.
Time iSplit.
Time {
Time (destruct s; intuition).
Time Qed.
Time
Lemma tpool_to_map_lookup_aux_none tp id j :
  tpool_to_map_aux tp id !! (id + j) = None \226\134\148 tp !! j = None.
Time Proof.
Time
(revert id j; <ssreflect_plugin::ssrtclintros@0> induction tp =>id j //=).
Time (destruct j).
Time iPureIntro.
Time (eapply spawn_non_errorable).
Time }
Time iIntros ( e2 (n', \207\1312) ? Hstep ) "!>".
Time *
Time rewrite //= Nat.add_0_r lookup_insert //=.
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite //= lookup_insert_ne //= ; last  by
 lia).
Time (destruct Hstep as ([], ((?, ?), (Hput, Hpure)))).
Time (inversion Hpure).
Time (replace (id + S j) with S id + j by lia; eauto).
Time subst.
Time Qed.
Time (apply fst_lift_puts_inv in Hput as (?, (?, ?)); subst).
Time
Lemma tpool_to_map_lookup tp j e :
  tpool_to_map tp !! j = Some e \226\134\148 tp !! j = Some e.
Time Proof.
Time rewrite /tpool_to_map.
Time
(<ssreflect_plugin::ssrtclintros@0> pose (tpool_to_map_lookup_aux tp 0 j e)
 =>//=).
Time Qed.
Time iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".
Time
Lemma tpool_to_map_lookup_none tp j :
  tpool_to_map tp !! j = None \226\134\148 tp !! j = None.
Time Proof.
Time rewrite /tpool_to_map.
Time
(<ssreflect_plugin::ssrtclintros@0>
 pose (tpool_to_map_lookup_aux_none tp 0 j) =>//=).
Time Qed.
Time
Lemma tpool_to_res_lookup tp j e :
  tpool_to_res tp !! j = Some (Excl e) \226\134\148 tp !! j = Some e.
Time Proof.
Time rewrite /tpool_to_res lookup_fmap.
Time
(<ssreflect_plugin::ssrtclintros@0> generalize (tpool_to_map_lookup tp j e)
 =>Hconv).
Time split.
Time -
Time
(destruct (tpool_to_map tp !! j); inversion 1; subst; eapply Hconv; eauto).
Time
iAssert (own (treg_name _) (Cinl (Count n)) \226\136\151 Registered)%I with
 "[Hown Hreg]" as "(Hown&Hreg)".
Time -
Time (intros).
Time (rewrite (proj2 Hconv); eauto).
Time Qed.
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> destruct (decide (n = 1)) as [->| ] ; last 
 first).
Time {
Time (destruct n as [| [| n]]; try lia; iFrame).
Time
Lemma tpool_to_res_lookup_none tp j :
  tpool_to_res tp !! j = None \226\134\148 tp !! j = None.
Time Proof.
Time rewrite /tpool_to_res lookup_fmap.
Time
(<ssreflect_plugin::ssrtclintros@0>
 generalize (tpool_to_map_lookup_none tp j) =>Hconv).
Time split.
Time -
Time
(destruct (tpool_to_map tp !! j); inversion 1; subst; eapply Hconv; eauto).
Time -
Time (intros).
Time (rewrite (proj2 Hconv); eauto).
Time Qed.
Time
Lemma tpool_to_res_lookup_excl tp j x :
  tpool_to_res tp !! j = Some x \226\134\146 \226\136\131 e, x = Excl e.
Time Proof.
Time rewrite /tpool_to_res /tpool_to_map.
Time (generalize 0).
Time (<ssreflect_plugin::ssrtclintros@0> induction tp =>n //=).
Time (destruct (decide (j = n)); subst).
Time *
Time rewrite lookup_fmap //= lookup_insert.
Time (inversion 1; setoid_subst; by eexists).
Time *
Time (rewrite lookup_fmap //= lookup_insert_ne //= -lookup_fmap; eauto).
Time Qed.
Time
Lemma tpool_to_res_insert_update tp j e :
  j < length tp
  \226\134\146 tpool_to_res (<[j:=e]> tp) = <[j:=Excl e]> (tpool_to_res tp).
Time Proof.
Time (intros Hlt).
Time (apply : {}map_eq {}; intros i).
Time (destruct (decide (i = j)); subst).
Time -
Time rewrite lookup_insert tpool_to_res_lookup list_lookup_insert //=.
Time -
Time rewrite lookup_insert_ne //=.
Time }
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hown" as "[Hown|Hown]" ; first 
 by iFrame).
Time (destruct (decide (i < length tp)) as [Hl| Hnl]).
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> efeed pose proof 
 lookup_lt_is_Some_2 tp as His ; first  eassumption).
Time (destruct His as (e', His)).
Time rewrite (proj2 (tpool_to_res_lookup tp i e')) //=.
Time (apply tpool_to_res_lookup).
Time rewrite list_lookup_insert_ne //=.
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> efeed pose proof 
 lookup_ge_None_2 tp i as Hnone ; first  lia).
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time rewrite (proj2 (tpool_to_res_lookup_none tp i)) //=.
Time }
Time
iAssert (own (treg_name _) (Cinl (Count (S n))) \226\136\151 Registered)%I with "[Hown]"
 as "(Hown&Hreg')".
Time (apply tpool_to_res_lookup_none).
Time rewrite list_lookup_insert_ne //=.
Time Qed.
Time {
Time rewrite -own_op Cinl_op counting_op' //=.
Time
Lemma tpool_to_res_insert_snoc tp e :
  tpool_to_res (tp ++ [e]) = <[length tp:=Excl e]> (tpool_to_res tp).
Time Proof.
Time (apply : {}map_eq {}; intros i).
Time (destruct (decide (i = length tp)); subst).
Time -
Time rewrite lookup_insert tpool_to_res_lookup.
Time rewrite lookup_app_r //= Nat.sub_diag //=.
Time -
Time rewrite lookup_insert_ne //=.
Time (destruct (decide (i < length tp)) as [Hl| Hnl]).
Time (repeat destruct decide; try lia).
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> efeed pose proof 
 lookup_lt_is_Some_2 tp as His ; first  eassumption).
Time (destruct His as (e', His)).
Time rewrite (proj2 (tpool_to_res_lookup tp i e')) //=.
Time (apply tpool_to_res_lookup).
Time rewrite lookup_app_l //=.
Time *
Time
(<ssreflect_plugin::ssrtclseq@0> efeed pose proof 
 lookup_ge_None_2 tp i as Hnone ; first  lia).
Time rewrite (proj2 (tpool_to_res_lookup_none tp i)) //=.
Time (apply tpool_to_res_lookup_none).
Time (rewrite lookup_ge_None_2 //= app_length //=; lia).
Time replace (S n + - 1)%Z with n : Z by lia.
Time done.
Time }
Time iModIntro.
Time (simpl).
Time iFrame.
Time Qed.
Time
Lemma tpool_to_res_length tp j e :
  tpool_to_res tp !! j = Some e \226\134\146 j < length tp.
Time Proof.
Time (intros Hlookup).
Time (destruct (decide (j < length tp)) as [Hl| Hnl]; auto).
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite
 (proj2 (tpool_to_res_lookup_none tp j)) in  {} Hlookup ; first  by
 congruence).
Time (apply lookup_ge_None_2; lia).
Time Qed.
Time
Lemma tpool_singleton_included1 tp j e :
  {[j := Excl e]} \226\137\188 tpool_to_res tp \226\134\146 tpool_to_res tp !! j = Some (Excl e).
Time Proof.
Time (intros (x, (Hlookup, Hexcl))%singleton_included).
Time
(destruct (tpool_to_res_lookup_excl tp j x) as (e', Heq); setoid_subst; eauto).
Time (apply Excl_included in Hexcl; setoid_subst; auto).
Time Qed.
Time
Lemma tpool_singleton_included2 tp j e :
  {[j := Excl e]} \226\137\188 tpool_to_res tp \226\134\146 tp !! j = Some e.
Time Proof.
Time (intros Hlookup%tpool_singleton_included1).
Time (apply tpool_to_res_lookup; rewrite Hlookup; eauto).
Time Qed.
Time
Lemma tpool_map_included1 tp1 tp2 :
  Excl <$> tp1 \226\137\188 tpool_to_res tp2
  \226\134\146 \226\136\128 j e, tp1 !! j = Some e \226\134\146 tp2 !! j = Some e.
Time iSplitL "Hown Hrest".
Time {
Time iApply Hinterp2.
Time Proof.
Time
(<ssreflect_plugin::ssrtclintros@0> rewrite lookup_included =>Hincl j e Hin).
Time (destruct n; iFrame).
Time specialize (Hincl j).
Time (apply tpool_to_res_lookup).
Time rewrite (lookup_fmap _ tp1 j) Hin //= in  {} Hincl.
Time
(destruct (tpool_to_res tp2 !! j) as [x| ] eqn:Heq; rewrite Heq in  {} Hincl).
Time {
Time
(destruct (tpool_to_res_lookup_excl tp2 j x) as (e', Heq'); setoid_subst;
  eauto).
Time (apply Excl_included in Hincl; setoid_subst; eauto).
Time }
Time iSplitL "Hreg H\206\166".
Time }
Time
(apply option_included in Hincl as [Hfalse| (?, (?, (?, (?, ?))))];
  congruence).
Time {
Time by iApply "H\206\166".
Time }
Time rewrite right_id.
Time Qed.
Time
Lemma tpool_to_res_lookup_case tp j :
  tpool_to_res tp !! j = None \226\136\168 (\226\136\131 e, tpool_to_res tp !! j = Excl' e).
Time Proof.
Time rewrite /tpool_to_res.
Time
(destruct (tpool_to_map tp !! j) as [p| ] eqn:Heq; rewrite lookup_fmap Heq
  //=).
Time by iApply "He".
Time *
Time by right; exists p.
Time *
Time by left.
Time Qed.
Time Qed.
Time
Lemma source_cfg_init `{cfgPreG \206\163} tp (\207\131 : OpState \206\155) :
  \194\172 bind_star (exec_pool \206\155.(sem)) tp (1, \207\131) Err
  \226\134\146 (|={\226\138\164}=> \226\136\131 _ : cfgG \206\163,
               source_ctx' (tp, \207\131)
               \226\136\151 source_pool_map (tpool_to_map tp) \226\136\151 source_state \207\131)%I.
Time Proof.
Time (intros Hno_err).
Time
iMod
 (own_alloc
    (\226\151\143 (tpool_to_res tp, Some (Excl \207\131)) \226\139\133 \226\151\175 (tpool_to_res tp, Some (Excl \207\131))))
 as ( \206\179 ) "(Hauth&Hfrag)".
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> apply @auth_both_valid ; first  by apply _).
Time (split; [  | split ]).
Time {
Time reflexivity.
Time }
Time -
Time rewrite //=.
Time (intros i).
Time (destruct (tpool_to_res_lookup_case tp i) as [Heq_none| (e, Heq_some)]).
Time *
Time (rewrite Heq_none; econstructor).
Time *
Time (rewrite Heq_some; econstructor).
Time -
Time rewrite //=.
Time }
Time (set (IN := {| cfg_name := \206\179 |})).
Time iExists IN.
Time iMod (inv_alloc sourceN \226\138\164 (source_inv tp \207\131) with "[Hauth]").
Time {
Time rewrite /source_inv.
Time iNext.
Time iExists tp , 1 , \207\131.
Time iFrame "Hauth".
Time (iPureIntro; split; eauto).
Time econstructor.
Time }
Time iModIntro.
Time iFrame.
Time rewrite pair_split.
Time
Lemma wp_unregister s E :
  {{{ \226\150\183 Registered }}} Unregister @ s; E {{{ RET tt; True}}}.
Time Proof.
Time iIntros ( \206\166 ) ">Hreg H\206\166".
Time iDestruct "Hfrag" as "($&$)".
Time iApply wp_lift_atomic_step.
Time Qed.
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
Time Context `{cfgG \206\163}.
Time Context `{Inhabited \206\155.(OpState)}.
Time
Lemma source_thread_update {T} {T'} (e' : proc OpT T') 
  tp j (e : proc OpT T) \207\131 :
  j \226\164\135 e
  -\226\136\151 own cfg_name (\226\151\143 (tpool_to_res tp, Excl' \207\131))
     ==\226\136\151 j \226\164\135 e'
         \226\136\151 own cfg_name (\226\151\143 (tpool_to_res (<[j:=existT _ e']> tp), Excl' \207\131)).
Time Proof.
Time iIntros "Hj Hauth".
Time (destruct Hstep as ([], ((?, ?), (Hput, Hpure)))).
Time iDestruct (own_valid_2 with "Hauth Hj") as % Hval_pool.
Time (inversion Hpure).
Time subst.
Time
(apply auth_both_valid in Hval_pool as ((Hpool, _)%prod_included, Hval')).
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
Time (apply tpool_singleton_included1 in Hpool).
Time iMod (own_update_2 with "Hauth Hj") as "[Hauth Hj]".
Time {
Time (eapply auth_update, prod_local_update_1).
Time
(eapply singleton_local_update,
  (exclusive_local_update _ (Excl (existT _ e' : procTC OpT))); eauto).
Time {
Time econstructor.
Time }
Time }
Time iFrame.
Time -
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time
(<ssreflect_plugin::ssrtclseq@0> rewrite tpool_to_res_insert_update // ;
 last  first).
Time {
Time (eapply tpool_to_res_length; eauto).
Time }
Time Qed.
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
Time rewrite Cinl_op counting_op' //=.
Time (repeat destruct decide; try lia).
Time
Lemma source_threads_fork (efs : thread_pool OpT) 
  tp \207\131 :
  own cfg_name (\226\151\143 (tpool_to_res tp, Excl' \207\131))
  ==\226\136\151 ([\226\136\151 list] ef \226\136\136 efs, \226\136\131 j', j' \226\164\135 `(projT2 ef))
      \226\136\151 own cfg_name (\226\151\143 (tpool_to_res (tp ++ efs), Excl' \207\131)).
Time Proof.
Time iInduction efs as [| ef efs] "IH" forall ( tp ).
Time replace (S n' + - 1)%Z with n' : Z by lia.
Time -
Time (rewrite /= app_nil_r /=; auto).
Time done.
Time }
Time iModIntro.
Time (simpl).
Time iFrame.
Time -
Time iIntros "Hown".
Time iSplitL "Hown Hrest".
Time iMod (own_update with "Hown") as "[Hown Hj']".
Time {
Time iApply Hinterp2.
Time (destruct n' as [| [| n']]; iFrame).
Time (eapply auth_update_alloc, prod_local_update_1).
Time (eapply (alloc_local_update (tpool_to_res tp) _ (length tp) (Excl ef))).
Time {
Time (apply tpool_to_res_lookup_none, lookup_ge_None_2).
Time reflexivity.
Time }
Time {
Time econstructor.
Time }
Time iEval rewrite insert_empty in "Hj'".
Time rewrite //= -assoc.
Time }
Time rewrite right_id.
Time by iApply "H\206\166".
Time Qed.
Time iSplitL "Hj'".
Time {
Time (iExists (length tp); destruct ef; iModIntro; eauto).
Time }
Time replace (ef :: efs) with [ef] ++ efs by auto.
Time rewrite assoc.
Time iApply "IH".
Time (rewrite tpool_to_res_insert_snoc; eauto).
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
Time
Lemma source_state_update \207\131' tp \207\1311 \207\1312 :
  source_state \207\1311
  -\226\136\151 own cfg_name (\226\151\143 (tpool_to_res tp, Excl' \207\1312))
     ==\226\136\151 source_state \207\131' \226\136\151 own cfg_name (\226\151\143 (tpool_to_res tp, Excl' \207\131')).
Time (inversion Hput as [Hsuch Heq]).
Time subst.
Time Proof.
Time iIntros "Hstate Hauth".
Time (inversion Hsuch; subst).
Time iDestruct (own_valid_2 with "Hauth Hstate") as % Hval_state.
Time iDestruct (Hinterp1 with "Hown") as "(Hown&Hrest)".
Time
iAssert (own (treg_name _) (Cinl (Count 1)) \226\136\151 Registered)%I with
 "[Hown Hreg]" as "(Hown&Hreg)".
Time
(apply auth_both_valid in Hval_state as ((_, Hstate)%prod_included, Hval')).
Time {
Time
(<ssreflect_plugin::ssrtclseq@0> iDestruct "Hown" as "[Hown|Hown]" ; first 
 by iFrame).
Time iDestruct (own_valid_2 with "Hown Hreg") as % [].
Time (apply Excl_included in Hstate; setoid_subst).
Time }
Time subst.
Time
iAssert (own (treg_name _) (Cinl (Count O)))%I with "[Hown Hreg]" as "Hown".
Time iMod (own_update_2 with "Hauth Hstate") as "[Hauth Hstate]".
Time {
Time iCombine "Hown Hreg" as "Hown".
Time rewrite Cinl_op counting_op' //=.
Time }
Time iMod (own_update with "Hown") as "(Hdone&Hown)".
Time {
Time (eapply auth_update, prod_local_update_2).
Time
(apply option_local_update, (exclusive_local_update _ (Excl \207\131'));
  econstructor).
Time }
Time by iFrame.
Time Qed.
Time {
Time
(<ssreflect_plugin::ssrtclintros@0>
 apply cmra_update_exclusive with
   (y := Cinr (\226\151\175 Excl' tt) \226\139\133 Cinr (\226\151\143 Excl' tt)) =>//=).
Time rewrite Cinr_op comm.
Time (apply auth_both_valid; split; done).
Time }
Time iModIntro.
Time iSplitL "Hown Hrest".
Time {
Time (iApply Hinterp2; iFrame).
Time }
Time (simpl).
Time rewrite right_id.
Time
Lemma source_thread_reconcile {T} tp j e x :
  j \226\164\135 e
  -\226\136\151 own cfg_name (\226\151\143 (tpool_to_res tp, x)) -\226\136\151 \226\140\156tp !! j = Some (existT T e)\226\140\157.
Time Proof.
Time iIntros "Hj Hauth".
Time iDestruct (own_valid_2 with "Hauth Hj") as % Hval_pool.
Time by iApply "H\206\166".
Time
(apply auth_both_valid in Hval_pool as ((Hpool, _)%prod_included, Hval')).
Time Qed.
Time (apply tpool_singleton_included1, tpool_to_res_lookup in Hpool; eauto).
Time Qed.
Time
Lemma source_pool_map_reconcile tp1 tp2 x :
  source_pool_map tp1
  -\226\136\151 own cfg_name (\226\151\143 (tpool_to_res tp2, x))
     -\226\136\151 \226\140\156\226\136\128 i e, tp1 !! i = Some e \226\134\146 tp2 !! i = Some e\226\140\157.
Time Proof.
Time iIntros "Hj Hauth".
Time iDestruct (own_valid_2 with "Hauth Hj") as % Hval_pool.
Time End Reg_wp.
Time
(apply auth_both_valid in Hval_pool as ((Hpool, _)%prod_included, Hval')).
Time iPureIntro.
Time (eapply tpool_map_included1; eauto).
Time Qed.
Time
Lemma source_state_reconcile \207\131 \207\131' x :
  source_state \207\131 -\226\136\151 own cfg_name (\226\151\143 (x, Excl' \207\131')) -\226\136\151 \226\140\156\207\131 = \207\131'\226\140\157.
Time Proof.
Time iIntros "Hstate Hauth".
Time iDestruct (own_valid_2 with "Hauth Hstate") as % Hval_state.
Time (apply auth_both_valid in Hval_state as ((_, Hstate)%prod_included, _)).
Time (apply Excl_included in Hstate; setoid_subst; auto).
Time End Reg_wp.
Time Qed.
Time
Lemma ghost_step_lifting' {T1} {T2} E \207\129 j K `{LanguageCtx OpT T1 T2 \206\155 K}
  (e1 : proc OpT T1) \207\1311 \207\1312 e2 efs :
  (\226\136\128 n, \226\136\131 n', exec_step \206\155.(sem) e1 (n, \207\1311) (Val (n', \207\1312) (e2, efs)))
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 source_ctx' \207\129 \226\136\151 j \226\164\135 K e1 \226\136\151 source_state \207\1311
      ={E}=\226\136\151 j \226\164\135 K e2
             \226\136\151 source_state \207\1312 \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, \226\136\131 j', j' \226\164\135 projT2 ef).
Time Proof.
Time iIntros ( Hstep ? ) "(#Hctx&Hj&Hstate)".
Time rewrite /source_ctx /source_inv.
Time iInv "Hctx" as ( tp' n' \207\131' ) ">[Hauth %]" "Hclose".
Time iDestruct (source_thread_reconcile with "Hj Hauth") as % Heq_thread.
Time iDestruct (source_state_reconcile with "Hstate Hauth") as % Heq_state.
Time setoid_subst.
Time iMod (source_thread_update (K e2) with "Hj Hauth") as "[Hj Hauth]".
Time iMod (source_threads_fork efs with "Hauth") as "[Hj' Hauth]".
Time iMod (source_state_update \207\1312 with "Hstate Hauth") as "[Hstate Hauth]".
Time (destruct (Hstep n') as (n'', ?)).
Time iMod ("Hclose" with "[Hauth]").
Time {
Time iNext.
Time iExists (<[j:=existT T2 (K e2)]> tp' ++ efs) , n'' , \207\1312.
Time iFrame.
Time intuition.
Time (iPureIntro; split; auto).
Time (apply bind_star_expand_r_valid).
Time right.
Time (exists tp',(n', \207\131'); split; auto).
Time (apply exec_pool_equiv_alt_val).
Time econstructor.
Time {
Time (symmetry; eapply take_drop_middle; eauto).
Time }
Time {
Time reflexivity.
Time }
Time {
Time f_equal.
Time (rewrite app_comm_cons assoc; f_equal).
Time (erewrite <- take_drop_middle  at 1; f_equal).
Time {
Time (apply take_insert; reflexivity).
Time }
Time {
Time f_equal.
Time (apply drop_insert; lia).
Time }
Time rewrite list_lookup_insert //=.
Time (apply lookup_lt_is_Some_1; eauto).
Time }
Time (eapply fill_step_valid; eauto).
Time }
Time (iModIntro; iFrame).
Time Qed.
Time
Lemma ghost_step_lifting {T1} {T2} E j K `{LanguageCtx OpT T1 T2 \206\155 K}
  (e1 : proc OpT T1) \207\1311 \207\1312 e2 efs :
  (\226\136\128 n, \226\136\131 n', exec_step \206\155.(sem) e1 (n, \207\1311) (Val (n', \207\1312) (e2, efs)))
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 j \226\164\135 K e1
      -\226\136\151 source_ctx
         -\226\136\151 source_state \207\1311
            ={E}=\226\136\151 j \226\164\135 K e2
                   \226\136\151 source_state \207\1312
                     \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, \226\136\131 j', j' \226\164\135 projT2 ef).
Time Proof.
Time iIntros ( ? ? ) "Hj Hsrc ?".
Time iDestruct "Hsrc" as ( ? ) "Hsrc".
Time (iApply ghost_step_lifting'; eauto).
Time iFrame.
Time Qed.
Time
Lemma ghost_step_call {T1} {T2} E j K `{LanguageCtx OpT T1 T2 \206\155 K} 
  r \207\1312 (op : OpT T1) \207\1311 :
  (\226\136\128 n, exec_step \206\155.(sem) (Call op) (n, \207\1311) (Val (n, \207\1312) (Ret r, [])))
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 j \226\164\135 K (Call op)
      -\226\136\151 source_ctx
         -\226\136\151 source_state \207\1311
            ={E}=\226\136\151 j \226\164\135 K (Ret r)
                   \226\136\151 source_state \207\1312
                     \226\136\151 ([\226\136\151 list] ef \226\136\136 [], \226\136\131 j', j' \226\164\135 projT2 ef).
Time Proof.
Time iIntros ( ? ? ) "Hj Hsrc ?".
Time (iApply (ghost_step_lifting with "Hj Hsrc"); eauto; iFrame).
Time Qed.
Time
Lemma ghost_step_err {T1} {T2} E j K `{LanguageCtx OpT T1 T2 \206\155 K}
  (op : OpT T1) \207\131 :
  (\226\136\128 n, exec_step \206\155.(sem) (Call op) (n, \207\131) Err)
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 j \226\164\135 K (Call op) -\226\136\151 source_ctx -\226\136\151 source_state \207\131 ={E}=\226\136\151 False.
Time Proof.
Time iIntros ( ? ? ) "Hj Hctx Hstate".
Time rewrite /source_ctx /source_inv.
Time iDestruct "Hctx" as ( \207\129 ) "#Hctx".
Time iInv "Hctx" as ( tp' n' \207\131' ) ">[Hauth Hpure]" "Hclose".
Time iDestruct "Hpure" as % (Hstep, Hnoerr).
Time iDestruct (source_thread_reconcile with "Hj Hauth") as % Heq_thread.
Time iDestruct (source_state_reconcile with "Hstate Hauth") as % Heq_state.
Time subst.
Time exfalso.
Time (eapply Hnoerr).
Time (apply bind_star_expand_r_err).
Time right.
Time right.
Time (exists tp',(n', \207\131'); split; auto).
Time (apply exec_pool_equiv_alt_err).
Time (eapply step_atomic_error).
Time {
Time (symmetry; eapply take_drop_middle; eauto).
Time }
Time {
Time reflexivity.
Time }
Time {
Time (eapply fill_step_err; eauto).
Time }
Time Qed.
Time
Lemma ghost_step_lifting_puredet {T1} {T2} E j K `{LanguageCtx OpT T1 T2 \206\155 K}
  (e1 : proc OpT T1) e2 efs :
  (\226\136\128 n \207\1311, \226\136\131 n', exec_step \206\155.(sem) e1 (n, \207\1311) (Val (n', \207\1311) (e2, efs)))
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 source_ctx \226\136\151 j \226\164\135 K e1
      ={E}=\226\136\151 j \226\164\135 K e2 \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, \226\136\131 j', j' \226\164\135 projT2 ef).
Time Proof.
Time iIntros ( Hstep ? ) "(#Hctx&Hj)".
Time iDestruct "Hctx" as ( ? ) "Hctx".
Time rewrite /source_ctx /source_inv.
Time iInv "Hctx" as ( tp' n' \207\131' ) ">[Hauth %]" "Hclose".
Time iDestruct (source_thread_reconcile with "Hj Hauth") as % Heq_thread.
Time setoid_subst.
Time iMod (source_thread_update (K e2) with "Hj Hauth") as "[Hj Hauth]".
Time iMod (source_threads_fork efs with "Hauth") as "[Hj' Hauth]".
Time (destruct (Hstep n' \207\131') as (n'', ?)).
Time iMod ("Hclose" with "[Hauth]").
Time {
Time iNext.
Time iExists (<[j:=existT T2 (K e2)]> tp' ++ efs) , _ , _.
Time iFrame.
Time intuition.
Time (iPureIntro; split; auto).
Time (apply bind_star_expand_r_valid).
Time right.
Time (exists tp',(n', \207\131'); split; auto).
Time (apply exec_pool_equiv_alt_val).
Time econstructor.
Time {
Time (symmetry; eapply take_drop_middle; eauto).
Time }
Time {
Time reflexivity.
Time }
Time {
Time f_equal.
Time (rewrite app_comm_cons assoc; f_equal).
Time (erewrite <- take_drop_middle  at 1; f_equal).
Time {
Time (apply take_insert; reflexivity).
Time }
Time {
Time f_equal.
Time (apply drop_insert; lia).
Time }
Time rewrite list_lookup_insert //=.
Time (apply lookup_lt_is_Some_1; eauto).
Time }
Time (eapply fill_step_valid; eauto).
Time }
Time (iModIntro; iFrame).
Time Qed.
Time
Lemma ghost_step_lifting_bind' {T1} {T2} E j (K : T1 \226\134\146 proc OpT T2)
  (e1 : proc OpT T1) \207\1311 \207\1312 e2 efs :
  (\226\136\128 n, \226\136\131 n', exec_step \206\155.(sem) e1 (n, \207\1311) (Val (n', \207\1312) (e2, efs)))
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 source_ctx \226\136\151 j \226\164\135 Bind e1 K \226\136\151 source_state \207\1311
      ={E}=\226\136\151 j \226\164\135 Bind e2 K
             \226\136\151 source_state \207\1312 \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, \226\136\131 j', j' \226\164\135 projT2 ef).
Time Proof.
Time (intros).
Time iIntros "(Hsrc&Hj&?)".
Time iDestruct "Hsrc" as ( \207\129 ) "Hsrc".
Time
(iApply (ghost_step_lifting' E \207\129 j (fun x => Bind x K) with "[$]"); eauto).
Time Qed.
Time
Lemma ghost_step_lifting_bind {T1} {T2} E j (K : T1 \226\134\146 proc OpT T2)
  (e1 : proc OpT T1) \207\1311 \207\1312 e2 efs :
  (\226\136\128 n, \226\136\131 n', exec_step \206\155.(sem) e1 (n, \207\1311) (Val (n', \207\1312) (e2, efs)))
  \226\134\146 nclose sourceN \226\138\134 E
    \226\134\146 j \226\164\135 Bind e1 K
      -\226\136\151 source_ctx
         -\226\136\151 source_state \207\1311
            ={E}=\226\136\151 j \226\164\135 Bind e2 K
                   \226\136\151 source_state \207\1312
                     \226\136\151 ([\226\136\151 list] ef \226\136\136 efs, \226\136\131 j', j' \226\164\135 projT2 ef).
Time Proof.
Time iIntros.
Time (iApply ghost_step_lifting_bind'; eauto).
Time iFrame.
Time iAssumption.
Time Qed.
Time
Lemma ghost_step_bind_ret {T1} {T2} {T3} E j K' `{LanguageCtx OpT T2 T3 \206\155 K'}
  (K : T1 \226\134\146 proc OpT T2) v :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K' (Bind (Ret v) K) -\226\136\151 source_ctx ={E}=\226\136\151 j \226\164\135 K' (K v).
Time Proof.
Time iIntros ( ? ) "Hj Hctx".
Time (iMod (ghost_step_lifting_puredet with "[Hj Hctx]") as "($&?)"; eauto).
Time {
Time (intros).
Time eexists.
Time econstructor.
Time }
Time Qed.
Time
Lemma ghost_step_loop {T1} {T2} {T3} E j K `{LanguageCtx OpT T2 T3 \206\155 K}
  (body : T1 \226\134\146 proc OpT (LoopOutcome T1 T2)) v :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Loop body v) -\226\136\151 source_ctx ={E}=\226\136\151 j \226\164\135 K (loop1 body v).
Time Proof.
Time iIntros ( ? ) "Hj Hctx".
Time (iMod (ghost_step_lifting_puredet with "[Hj Hctx]") as "($&?)"; eauto).
Time {
Time (intros).
Time eexists.
Time econstructor.
Time }
Time Qed.
Time
Lemma ghost_step_spawn {T} {T'} E j K `{LanguageCtx OpT unit T \206\155 K}
  (e : proc OpT T') :
  nclose sourceN \226\138\134 E
  \226\134\146 j \226\164\135 K (Spawn e)
    -\226\136\151 source_ctx
       ={E}=\226\136\151 j \226\164\135 K (Ret tt) \226\136\151 (\226\136\131 j', j' \226\164\135 Bind e (\206\187 _, Unregister)).
Time Proof.
Time iIntros ( ? ) "Hj Hctx".
Time (iMod (ghost_step_lifting_puredet with "[Hj Hctx]") as "($&H)"; eauto).
Time {
Time (intros).
Time exists (S n).
Time econstructor.
Time (exists (S n, \207\1311); split; econstructor; eauto).
Time (econstructor; eauto).
Time }
Time iModIntro.
Time iDestruct "H" as "($&_)".
Time Qed.
Time End ghost_step.
Time End ghost.
Time Notation "j \226\164\135 e" := (tpool_mapsto j e) (at level 20) : bi_scope.
