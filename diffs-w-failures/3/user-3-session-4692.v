Time Require Export CSL.Refinement CSL.WeakestPre.
Time From Transitions Require Import Relations Rewriting.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time
Require Export CSL.WeakestPre CSL.Refinement CSL.Adequacy
  CSL.RefinementAdequacy CSL.ThreadReg.
Time From iris.algebra Require Import auth gmap frac agree.
Time Require Export CSL.WeakestPre CSL.Lifting CSL.Counting CSL.ThreadReg.
Time From iris.algebra Require Export functions csum.
Time From iris.base_logic.lib Require Export invariants gen_heap.
Time From iris.algebra Require Import auth frac agree gmap list.
Time From iris.base_logic.lib Require Import invariants.
Time From iris.proofmode Require Import tactics.
Time Unset Implicit Arguments.
Time Import RelationNotations.
Time From Transitions Require Import Relations.
Time Module Type refinement_type.
Time Context (OpC OpT : Type \226\134\146 Type).
Time Context (\206\155c : Layer OpC) (\206\155a : Layer OpT).
Time Context (impl : LayerImplRel OpC OpT).
Time Context (\206\163 : gFunctors).
Time From iris.proofmode Require Export tactics.
Time #[global]
Instance from_exist_left_sep  {\206\163} {A} (\206\166 : A \226\134\146 iProp \206\163) 
 Q: (FromExist (\226\150\183 (\226\136\131 a, \206\166 a) \226\136\151 Q) (\206\187 a, \226\150\183 \206\166 a \226\136\151 Q)%I).
Time Proof.
Time rewrite /FromExist.
Time iIntros "H".
Time Context (exmachG : gFunctors \226\134\146 Type).
Time Existing Class exmachG.
Time iDestruct "H" as ( ? ) "(?&$)".
Time Notation compile_rel_base := (compile_rel_base impl).
Time Notation compile_rel_proc_seq := (compile_rel_proc_seq impl).
Time Notation compile_rel := (compile_rel impl).
Time Notation recover := (recover_rel impl).
Time Notation compile_proc_seq := (compile_proc_seq impl).
Time Context `{CFG : cfgPreG OpT \206\155a \206\163}.
Time Context `{INV : Adequacy.invPreG \206\163}.
Time
Context `{REG : inG \206\163 (csumR countingR (authR (optionUR (exclR unitO))))}.
Time Context {Hinstance : \226\136\128 \206\163, exmachG \206\163 \226\134\146 irisG OpC \206\155c \206\163}.
Time Context {Hinstance_reg : \226\136\128 \206\163, exmachG \206\163 \226\134\146 tregG \206\163}.
Time
Context (crash_inner : forall {_ : @cfgG OpT \206\155a \206\163} {_ : exmachG \206\163}, iProp \206\163).
Time
Context (exec_inner : forall {_ : @cfgG OpT \206\155a \206\163} {_ : exmachG \206\163}, iProp \206\163).
Time
Context (crash_param : forall (_ : @cfgG OpT \206\155a \206\163) (_ : exmachG \206\163), Type).
Time
Context
 (crash_inv : forall {H1 : @cfgG OpT \206\155a \206\163} {H2 : exmachG \206\163},
              @crash_param _ H2 \226\134\146 iProp \206\163).
Time
Context
 (crash_starter : forall {H1 : @cfgG OpT \206\155a \206\163} {H2 : exmachG \206\163},
                  @crash_param _ H2 \226\134\146 iProp \206\163).
Time
Context (exec_inv : forall {_ : @cfgG OpT \206\155a \206\163} {_ : exmachG \206\163}, iProp \206\163).
Time Context (E : coPset).
Time Context (recv : proc OpC unit).
Time Context (set_inv_reg : exmachG \206\163 \226\134\146 invG \206\163 \226\134\146 tregG \206\163 \226\134\146 exmachG \206\163).
Time Context (init_absr : \206\155a.(OpState) \226\134\146 \206\155c.(OpState) \226\134\146 Prop).
Time End refinement_type.
Time Module refinement_definitions (RT: refinement_type).
Time Import RT.
Time Existing Instances Hinstance, Hinstance_reg.
Time
Definition set_reg (Hex : exmachG \206\163) (tR : tregG \206\163) := set_inv_reg Hex _ tR.
Time
Definition set_inv (Hex : exmachG \206\163) (Hinv : invG \206\163) :=
  set_inv_reg Hex Hinv _.
Time
Definition post_crash {Hex : exmachG \206\163} (P : \226\136\128 {_ : exmachG \206\163}, iProp \206\163) :
  iProp \206\163 :=
  (\226\136\128 Hreg' n \207\131,
     state_interp (n, \207\131) \226\136\151 @thread_count_interp _ Hreg' 1
     ={E}=\226\136\151 \226\136\128 \207\131' (Hcrash : \206\155c.(crash_step) \207\131 (Val \207\131' tt)),
              \226\136\131 Hex', let _ := set_reg Hex' Hreg' in state_interp (1, \207\131') \226\136\151 P)%I.
Time (iExists _; eauto).
Time
Definition post_finish {Hex : exmachG \206\163} (P : \226\136\128 {_ : exmachG \206\163}, iProp \206\163) :
  iProp \206\163 :=
  (\226\136\128 n \207\131 \207\131' (Hcrash : \206\155c.(finish_step) \207\131 (Val \207\131' tt)) Hinv' Hreg',
     state_interp (n, \207\131) \226\136\151 @thread_count_interp _ Hreg' 1
     ==\226\136\151 \226\136\131 Hex',
           let _ := set_inv_reg Hex' Hinv' Hreg' in state_interp (1, \207\131') \226\136\151 P)%I.
Time Qed.
Time
Definition post_recv {Hex : exmachG \206\163} (P : \226\136\128 {_ : exmachG \206\163}, iProp \206\163) :
  iProp \206\163 :=
  (\226\136\128 n \207\131 Hinv' Hreg',
     state_interp (n, \207\131) \226\136\151 @thread_count_interp _ Hreg' 1
     ==\226\136\151 \226\136\131 Hex',
           let _ := set_inv_reg Hex' Hinv' Hreg' in state_interp (1, \207\131) \226\136\151 P)%I.
Time
Definition recv_triple_type :=
  \226\136\128 H1 H2 param,
    @crash_inv H1 H2 param \226\136\151 Registered \226\136\151 @crash_starter H1 H2 param
    \226\138\162 WP recv
      @ NotStuck; \226\138\164 {{ v, |={\226\138\164,E}=> \226\136\131 \207\1312a \207\1312a',
                                      source_state \207\1312a
                                      \226\136\151 \226\140\156\206\155a.(crash_step) \207\1312a (Val \207\1312a' tt)\226\140\157
                                        \226\136\151 (\226\136\128 `{Hcfg' : cfgG OpT \206\155a \206\163},
                                             post_recv
                                               (\206\187 H,
                                                 source_ctx
                                                 \226\136\151 
                                                 source_state \207\1312a'
                                                 ==\226\136\151 |={\226\138\164}=> 
                                                 exec_inner Hcfg' H)) }}.
Time
Ltac
 iCancelPureRec P :=
  match P with
  | \226\140\156?P'\226\140\157%I =>
      let H := iFresh in
      iAssert \226\140\156P'\226\140\157%I as H; [ iPureIntro | iFrame H ]
  | (?P1 \226\136\151 ?P2)%I => first [ iCancelPureRec P1 | iCancelPureRec P2 ]
  end.
Time
Ltac
 iCancelPure :=
  match goal with
  | |- environments.envs_entails _ ?P => iCancelPureRec P
  end.
Time
Ltac
 iDestructPure :=
  repeat
   match goal with
   | |- context [ environments.Esnoc _ ?H \226\140\156_\226\140\157%I ] => iDestruct H as "%"
   end.
Time Section test.
Time Context {PROP : bi}.
Time Context {Hpos : BiPositive PROP}.
Time Context {Haffine : BiAffine PROP}.
Time Lemma cancel_pure1 (P : PROP) : P \226\138\162 \226\140\156(2 + 2 = 4)%nat\226\140\157 \226\136\151 P.
Time Proof.
Time iIntros "HP".
Time
Definition init_exec_inner_type :=
  \226\136\128 \207\1311a \207\1311c,
    init_absr \207\1311a \207\1311c
    \226\134\146 (\226\136\128 `{Hinv : invG \206\163} Hreg `{Hcfg : cfgG OpT \206\155a \206\163},
         |={\226\138\164}=> \226\136\131 Hex' : exmachG \206\163,
                   source_ctx
                   \226\136\151 source_state \207\1311a \226\136\151 @thread_count_interp _ Hreg 1
                   ={\226\138\164}=\226\136\151 let _ := set_inv_reg Hex' Hinv Hreg in
                          exec_inner Hcfg _ \226\136\151 state_interp (1, \207\1311c))%I.
Time (<ssreflect_plugin::ssrtclseq@0> iCancelPure ; first  by lia).
Time
Definition exec_inv_preserve_crash_type :=
  \226\136\128 `(Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    exec_inv Hcfg Hex ={\226\138\164,E}=\226\136\151 post_crash (\206\187 H, |==> crash_inner Hcfg H).
Time
Definition crash_inv_preserve_crash_type :=
  \226\136\128 `(Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163) param,
    crash_inv Hcfg Hex param
    ={\226\138\164,E}=\226\136\151 post_crash (\206\187 H, |==> crash_inner Hcfg H).
Time
Definition state_interp_no_inv_type :=
  \226\136\128 `(Hex : exmachG \206\163) Hinv \207\131,
    state_interp \207\131 -\226\136\151 let _ := set_inv Hex Hinv in state_interp \207\131.
Time
Definition crash_inner_inv_type :=
  \226\136\128 `(Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    (\226\136\131 Hinv, crash_inner Hcfg (set_inv Hex Hinv)) \226\136\151 source_ctx
    ={\226\138\164}=\226\136\151 \226\136\131 param, crash_inv Hcfg Hex param \226\136\151 crash_starter Hcfg Hex param.
Time
Definition exec_inner_inv_type :=
  \226\136\128 (Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    (\226\136\131 Hinv, exec_inner Hcfg (set_inv Hex Hinv)) \226\136\151 source_ctx
    ={\226\138\164}=\226\136\151 exec_inv Hcfg Hex.
Time
Definition exec_inv_preserve_finish_type :=
  \226\136\128 `(Hex : exmachG \206\163) `(Hcfg : cfgG OpT \206\155a \206\163),
    AllDone
    -\226\136\151 exec_inv Hcfg Hex
       ={\226\138\164,E}=\226\136\151 \226\136\131 \207\1312a \207\1312a' : \206\155a.(OpState),
                  source_state \207\1312a
                  \226\136\151 \226\140\156\206\155a.(finish_step) \207\1312a (Val \207\1312a' tt)\226\140\157
                    \226\136\151 (\226\136\128 `{Hcfg' : cfgG OpT \206\155a \206\163},
                         post_finish
                           (\206\187 H,
                              source_ctx \226\136\151 source_state \207\1312a'
                              ==\226\136\151 |={\226\138\164}=> exec_inner Hcfg' H)).
Time
Definition refinement_base_triples_type :=
  forall H1 H2 T1 T2 j K `{LanguageCtx OpT T1 T2 \206\155a K} (p : proc OpT T1) p',
  compile_rel_base p p'
  \226\134\146 j \226\164\135 K p \226\136\151 Registered \226\136\151 @exec_inv H1 H2
    \226\138\162 WP p' {{ v, j \226\164\135 K (Ret v) \226\136\151 Registered }}.
Time End refinement_definitions.
Time Module Type refinement_obligations (RT: refinement_type).
Time auto.
Time Qed.
Time Import RT.
Time Module RD:=  refinement_definitions RT.
Time Lemma cancel_pure2 (P : PROP) : P \226\138\162 P \226\136\151 \226\140\156(2 + 2 = 4)%nat\226\140\157.
Time Proof.
Time iIntros "HP".
Time (<ssreflect_plugin::ssrtclseq@0> iCancelPure ; first  by lia).
Time auto.
Time Qed.
Time Import RD.
Time
Context
 (einv_persist : forall {H1 : @cfgG OpT \206\155a \206\163} {H2},
                 Persistent (exec_inv H1 H2)).
Time
Context
 (cinv_persist : forall {H1 : @cfgG OpT \206\155a \206\163} {H2} {P : crash_param _ _},
                 Persistent (crash_inv H1 H2 P)).
Time Context (nameIncl : nclose sourceN \226\138\134 E).
Time Context (recsingle : recover = rec_singleton recv).
Time
Context (exec_inv_source_ctx : \226\136\128 {H1} {H2}, exec_inv H1 H2 \226\138\162 source_ctx).
Time
Context
 (set_inv_reg_spec0 : \226\136\128 Hex,
                        set_inv_reg Hex
                          (Hinstance \206\163 Hex).(@iris_invG OpC (State \206\155c) \206\163)
                          (Hinstance_reg \206\163 Hex) = Hex).
Time
Context
 (set_inv_reg_spec1 : \226\136\128 Hex Hinv Hreg,
                        @iris_invG _ _ _
                          (Hinstance _ (set_inv_reg Hex Hinv Hreg)) = Hinv).
Time
Context
 (set_inv_reg_spec2 : \226\136\128 Hex Hinv Hreg,
                        Hinstance_reg _ (set_inv_reg Hex Hinv Hreg) = Hreg).
Time
Context
 (set_inv_reg_spec3 : \226\136\128 Hex Hinv Hinv' Hreg Hreg',
                        set_inv_reg (set_inv_reg Hex Hinv' Hreg') Hinv Hreg =
                        set_inv_reg Hex Hinv Hreg).
Time
Context
 (register_spec : \226\136\128 {H : exmachG \206\163},
                    \226\136\131 Interp : OpState \206\155c \226\134\146 iProp \206\163,
                      (\226\136\128 n \207\131,
                         @state_interp _ _ _ (Hinstance _ H) (n, \207\131)
                         -\226\136\151 thread_count_interp n \226\136\151 Interp \207\131)
                      \226\136\167 (\226\136\128 n \207\131,
                           thread_count_interp n \226\136\151 Interp \207\131
                           -\226\136\151 state_interp (n, \207\131))).
Time Lemma cancel_pure3 (P : PROP) : P \226\138\162 \226\140\1565 = 5\226\140\157%nat \226\136\151 \226\140\156(2 + 2 = 4)%nat\226\140\157.
Time Proof.
Time iIntros "HP".
Time (<ssreflect_plugin::ssrtclseq@0> iCancelPure ; first  by lia).
Time Context (refinement_base_triples : refinement_base_triples_type).
Time Context (state_interp_no_inv : state_interp_no_inv_type).
Time Context (recv_triple : recv_triple_type).
Time Context (init_exec_inner : init_exec_inner_type).
Time Context (exec_inv_preserve_crash : exec_inv_preserve_crash_type).
Time Context (crash_inv_preserve_crash : crash_inv_preserve_crash_type).
Time Context (exec_inner_inv : exec_inner_inv_type).
Time Context (crash_inner_inv : crash_inner_inv_type).
Time Context (exec_inv_preserve_finish : exec_inv_preserve_finish_type).
Time End refinement_obligations.
Time Module refinement (RT: refinement_type) (RO: refinement_obligations RT).
Time Import RT RO.
Time Existing Instances Hinstance, Hinstance_reg, einv_persist, cinv_persist.
Time Import Reg_wp.
Time
Lemma wp_spawn {H : exmachG \206\163} {T} s E (e : proc _ T) 
  \206\166 :
  \226\150\183 Registered
  -\226\136\151 \226\150\183 (Registered -\226\136\151 WP (let! _ <- e; Unregister)%proc @ s; \226\138\164 {{ _, True }})
     -\226\136\151 \226\150\183 (Registered -\226\136\151 \206\166 tt) -\226\136\151 WP Spawn e @ s; E {{ \206\166 }}.
Time auto.
Time Qed.
Time Lemma destruct_pure1 (P : PROP) n : P \226\136\151 \226\140\156n > 100\226\140\157 \226\138\162 P \226\136\151 \226\140\156n > 99\226\140\157.
Time Proof.
Time iIntros "(?&?)".
Time Proof.
Time (intros).
Time (edestruct (register_spec) as (?, (?, ?))).
Time iDestructPure.
Time (eapply wp_spawn; eauto).
Time Qed.
Time
Lemma wp_unregister {H : exmachG \206\163} s E :
  {{{ \226\150\183 Registered }}} Unregister @ s; E {{{ RET tt; True}}}.
Time (<ssreflect_plugin::ssrtclseq@0> iCancelPure ; first  lia).
Time Proof.
Time (intros).
Time (edestruct (register_spec) as (?, (?, ?))).
Time (eapply wp_unregister; eauto).
Time Qed.
Time
Lemma wp_wait {H : exmachG \206\163} s E :
  {{{ \226\150\183 Registered }}} Wait @ s; E {{{ RET tt; AllDone}}}.
Time Proof.
Time (intros).
Time (edestruct (register_spec) as (?, (?, ?))).
Time (eapply wp_wait; eauto).
Time Qed.
Time
Lemma refinement_triples :
  forall {H1} {H2} {T1} {T2} j K `{LanguageCtx OpT T1 T2 \206\155a K}
    (e : proc OpT T1) e',
  wf_client e
  \226\134\146 compile_rel e e'
    \226\134\146 j \226\164\135 K e \226\136\151 Registered \226\136\151 @exec_inv H1 H2
      \226\138\162 WP e' {{ v, j \226\164\135 K (Ret v) \226\136\151 Registered }}.
Time Proof.
Time (intros ? ? ? ? j K Hctx e e' Hwf Hcompile).
Time iIntros "(Hj&Hreg&#Hinv)".
Time auto.
Time Qed.
Time iAssert \226\140\156\226\136\131 ea : State \206\155a, True\226\140\157%I as % [? _].
Time End test.
Time {
Time iDestruct (exec_inv_source_ctx with "Hinv") as ( (?, ?) ) "#Hctx".
Time eauto.
Time }
Time (assert (Inhabited (State \206\155a))).
Time {
Time eexists.
Time eauto.
Time }
Time (assert (Inhabited \206\155a.(OpState))).
Time {
Time eexists.
Time (destruct x; eauto).
Time }
Time rename T2 into T2'.
Time iInduction Hcompile as [] "IH" forall ( T2' j K Hctx Hwf ).
Time -
Time (iApply refinement_base_triples; eauto).
Time by iFrame.
Time -
Time wp_ret.
Time iFrame.
Time -
Time wp_bind.
Time iApply wp_wand_l.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; last  first).
Time *
Time
unshelve
 (iApply ("IH1" $! _ j (fun x => K (Bind x p1')) with "[] [] [Hj]");
   try iFrame).
Time {
Time iPureIntro.
Time (apply comp_ctx; auto).
Time (apply _).
Time }
Time {
Time (inversion Hwf; eauto).
Time }
Time *
Time iIntros ( ? ) "(Hj&Hreg)".
Time iDestruct (exec_inv_source_ctx with "Hinv") as "#Hctx".
Time iMod (ghost_step_bind_ret with "Hj []") as "Hj".
Time {
Time set_solver +.
Time }
Time {
Time eauto.
Time }
Time (iApply ("IH" with "[] [] Hj Hreg"); auto).
Time {
Time iPureIntro.
Time (eapply Hwf).
Time }
Time -
Time iL\195\182b as "IHloop" forall ( init Hwf ).
Time iDestruct (exec_inv_source_ctx with "Hinv") as "#Hctx".
Time iMod (ghost_step_loop with "Hj []") as "Hj".
Time {
Time set_solver +.
Time }
Time {
Time eauto.
Time }
Time wp_loop.
Time iApply wp_wand_l.
Time (<ssreflect_plugin::ssrtclseq@0> iSplitL "" ; last  first).
Time *
Time rewrite /loop1.
Time (simpl).
Time
unshelve iApply
 ("IH" $! _ _ _
 (fun x =>
  K
    (Bind x
       (fun out =>
        match out with
        | ContinueOutcome x => Loop b x
        | DoneWithOutcome r => Ret r
        end))) with "[] [] Hj Hreg")%proc.
Time {
Time iPureIntro.
Time (apply comp_ctx; auto).
Time (apply _).
Time }
Time {
Time (simpl in Hwf).
Time eauto.
Time }
Time *
Time iIntros ( out ) "(Hj&Hreg)".
Time (destruct out).
Time **
Time iNext.
Time iMod (ghost_step_bind_ret with "Hj []") as "Hj".
Time {
Time set_solver +.
Time }
Time {
Time eauto.
Time }
Time iApply ("IHloop" with "[] Hj Hreg").
Time {
Time eauto.
Time }
Time **
Time iNext.
Time iMod (ghost_step_bind_ret with "Hj []") as "Hj".
Time {
Time set_solver +.
Time }
Time {
Time eauto.
Time }
Time wp_ret.
Time iFrame.
Time -
Time (inversion Hwf).
Time -
Time (inversion Hwf).
Time -
Time iDestruct (exec_inv_source_ctx with "Hinv") as "#Hctx".
Time iMod (ghost_step_spawn with "Hj []") as "(Hj&Hj')".
Time {
Time set_solver +.
Time }
Time {
Time eauto.
Time }
Time iDestruct "Hj'" as ( j' ) "Hj'".
Time iApply (wp_spawn with "Hreg [Hj'] [Hj]").
Time {
Time iNext.
Time iIntros "Hreg'".
Time {
Time wp_bind.
Time iApply (wp_wand with "[Hj' Hreg'] []").
Time {
Time
unshelve iApply
 ("IH" $! _ _ (fun x => Bind x (fun _ => Unregister)) with "[] [] Hj' Hreg'").
Time {
Time iPureIntro.
Time (apply _).
Time }
Time {
Time eauto.
Time }
Time }
Time {
Time iIntros ( ? ) "(?&?)".
Time iApply (wp_unregister with "[$]").
Time iIntros "!> ?".
Time eauto.
Time }
Time }
Time }
Time iIntros "!> ?".
Time iFrame.
Time Qed.
Time Existing Instances INV, CFG, REG.
Time Transparent WeakestPre.iris_invG.
Time
Lemma iris_invG_proj T H Hinv :
  @iris_invG _ T _ (IrisG OpC _ \206\163 Hinv H) = Hinv.
Time Proof.
Time auto.
Time Qed.
Time Opaque WeakestPre.iris_invG.
Time
Lemma Hinstance_eta Hex Hinv Hreg :
  Hinstance \206\163 (set_inv_reg Hex Hinv Hreg) =
  IrisG OpC _ \206\163 Hinv
    (@state_interp _ _ _ (Hinstance \206\163 (set_inv_reg Hex Hinv Hreg))).
Time Proof.
Time specialize (set_inv_reg_spec1 Hex Hinv Hreg).
Time (<ssreflect_plugin::ssrtclintros@0> destruct Hinstance =>//=).
Time (<ssreflect_plugin::ssrtclintros@0> rewrite iris_invG_proj =>{+}-> //).
Time Qed.
Time
Lemma Hinstance_eta2 Hex Hinv Hreg :
  IrisG OpC _ \206\163 Hinv
    (@state_interp _ _ _ (Hinstance \206\163 (set_inv_reg Hex Hinv Hreg))) =
  Hinstance \206\163
    (set_inv_reg (set_inv_reg Hex Hinv Hreg) Hinv
       (Hinstance_reg \206\163 (set_inv_reg Hex Hinv Hreg))).
Time Proof.
Time by rewrite -Hinstance_eta set_inv_reg_spec2 set_inv_reg_spec3.
Time Qed.
Time
Lemma crash_refinement_seq {T} \207\1311c \207\1311a (es : proc_seq OpT T) 
  es' :
  init_absr \207\1311a \207\1311c
  \226\134\146 wf_client_seq es
    \226\134\146 compile_rel_proc_seq es es'
      \226\134\146 \194\172 proc_exec_seq \206\155a es (rec_singleton (Ret ())) (1, \207\1311a) Err
        \226\134\146 \226\136\128 \207\1312c res,
            proc_exec_seq \206\155c es' (rec_singleton recv) (1, \207\1311c) (Val \207\1312c res)
            \226\134\146 \226\136\131 \207\1312a,
                proc_exec_seq \206\155a es (rec_singleton (Ret tt)) 
                  (1, \207\1311a) (Val \207\1312a res).
Time Proof.
Time (intros Hinit Hwf_seq Hcompile Hno_err \207\1312c0 ?).
Time
unshelve
 (eapply wp_proc_seq_refinement_adequacy with (\206\155c := \206\155c)
   (\207\134 := fun va vc _ _ => \226\140\156va = vc\226\140\157%I) (E := E); eauto).
Time clear Hno_err.
Time
iAssert
 (\226\136\128 invG H1 \207\129,
    |={\226\138\164}=> \226\136\131 Hex Hreg (HEQ : Hreg.(@treg_counter_inG \206\163) = REG),
              source_ctx' (\207\129, \207\1311a)
              -\226\136\151 source_state \207\1311a
                 ={\226\138\164}=\226\136\151 let _ := set_inv_reg Hex invG Hreg in
                        state_interp (1, \207\1311c)
                        \226\136\151 own (treg_name Hreg) (Cinl (Count (- 1)))
                          \226\136\151 exec_inner H1 (set_inv_reg Hex invG Hreg))%I as
 "Hpre".
Time {
Time iIntros ( ? ? ? ).
Time iMod (own_alloc (Cinl (Count 0))) as ( tR ) "Ht".
Time {
Time constructor.
Time }
Time (set (Hreg' := {| treg_name := tR; treg_counter_inG := _ |})).
Time
iAssert (own tR (Cinl (Count 1)) \226\136\151 own tR (Cinl (Count (- 1))))%I with "[Ht]"
 as "(Ht&Hreg)".
Time {
Time rewrite /Registered -own_op Cinl_op counting_op' //=.
