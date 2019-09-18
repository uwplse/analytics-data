Time From Transitions Require Import Relations Rewriting.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Spec.Layer.
Time
Require Export CSL.WeakestPre CSL.Refinement CSL.Adequacy
  CSL.RefinementAdequacy CSL.ThreadReg.
Time Require CSL.RefinementIdempotenceModule.
Time From iris.algebra Require Import auth frac agree gmap list.
Time From iris.base_logic.lib Require Import invariants.
Time From iris.proofmode Require Import tactics.
Time Unset Implicit Arguments.
Time Import RelationNotations.
Time From Transitions Require Import Relations.
Time Module Type refinement_type.
Time Context (OpC OpT : Type \226\134\146 Type).
Time Context (\206\155c : Layer OpC) (\206\155a : Layer OpT).
Time Context (impl : LayerImpl OpC OpT).
Time Context (\206\163 : gFunctors).
Time Context (exmachG : gFunctors \226\134\146 Type).
Time Existing Class exmachG.
Time Notation compile_op := (compile_op impl).
Time Notation compile_rec := (compile_rec impl).
Time Notation compile_seq := (compile_seq impl).
Time Notation compile := (compile impl).
Time Notation recover := (recover impl).
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
Time
Definition post_finish {Hex : exmachG \206\163} (P : \226\136\128 {_ : exmachG \206\163}, iProp \206\163) :
  iProp \206\163 :=
  (\226\136\128 n \207\131 \207\131' (Hcrash : \206\155c.(finish_step) \207\131 (Val \207\131' tt)) Hinv' Hreg',
     state_interp (n, \207\131) \226\136\151 @thread_count_interp _ Hreg' 1
     ==\226\136\151 \226\136\131 Hex',
           let _ := set_inv_reg Hex' Hinv' Hreg' in state_interp (1, \207\131') \226\136\151 P)%I.
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
Definition init_exec_inner_type :=
  \226\136\128 \207\1311a \207\1311c,
    init_absr \207\1311a \207\1311c
    \226\134\146 (\226\136\128 `{Hinv : invG \206\163} Hreg `{Hcfg : cfgG OpT \206\155a \206\163},
         |={\226\138\164}=> \226\136\131 Hex' : exmachG \206\163,
                   source_ctx
                   \226\136\151 source_state \207\1311a \226\136\151 @thread_count_interp _ Hreg 1
                   ={\226\138\164}=\226\136\151 let _ := set_inv_reg Hex' Hinv Hreg in
                          exec_inner Hcfg _ \226\136\151 state_interp (1, \207\1311c))%I.
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
Time End refinement_definitions.
Time Module Type refinement_obligations (RT: refinement_type).
Time Import RT.
Time Module RD:=  refinement_definitions RT.
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
Time
Context
 (refinement_op_triples : forall {H1} {H2} {T1} {T2} 
                            j K `{LanguageCtx OpT T1 T2 \206\155a K} 
                            (op : OpT T1),
                          j \226\164\135 K (Call op) \226\136\151 Registered \226\136\151 @exec_inv H1 H2
                          \226\138\162 WP compile (Call op)
                            {{ v, j \226\164\135 K (Ret v) \226\136\151 Registered }}).
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
Time Module RT'<: RefinementIdempotenceModule.refinement_type.
Time Definition OpC := OpC.
Time Definition \206\155c := \206\155c.
Time Definition OpT := OpT.
Time Definition \206\155a := \206\155a.
Time Definition impl := LayerImpl_to_LayerImplRel impl.
Time Definition exmachG := exmachG.
Time Definition \206\163 := \206\163.
Time Definition CFG := CFG.
Time Definition INV := INV.
Time Definition REG := REG.
Time Definition Hinstance := Hinstance.
Time Definition Hinstance_reg := Hinstance_reg.
Time Definition set_inv_reg := set_inv_reg.
Time Definition crash_inner := crash_inner.
Time Definition exec_inner := exec_inner.
Time Definition crash_inv := crash_inv.
Time Definition crash_param := crash_param.
Time Definition crash_starter := crash_starter.
Time Definition exec_inv := exec_inv.
Time Definition E := E.
Time Definition recv := recv.
Time Definition init_absr := init_absr.
Time End RT'.
Time Module RD:=  RefinementIdempotenceModule.refinement_definitions RT'.
Time Module RO'<: RefinementIdempotenceModule.refinement_obligations RT'.
Time Module RD:=  RD.
Time Definition nameIncl := RO.nameIncl.
Time Definition einv_persist := RO.einv_persist.
Time Definition cinv_persist := RO.cinv_persist.
Time Existing Instances einv_persist, cinv_persist.
Time Definition recsingle := RO.recsingle.
Time Definition refinement_op_triples := RO.refinement_op_triples.
Time Definition exec_inv_source_ctx := RO.exec_inv_source_ctx.
Time Definition set_inv_reg_spec0 := RO.set_inv_reg_spec0.
Time Definition set_inv_reg_spec1 := RO.set_inv_reg_spec1.
Time Definition set_inv_reg_spec2 := RO.set_inv_reg_spec2.
Time Definition set_inv_reg_spec3 := RO.set_inv_reg_spec3.
Time Definition register_spec := RO.register_spec.
Time Definition recv_triple := RO.recv_triple.
Time Definition init_exec_inner := RO.init_exec_inner.
Time Definition exec_inv_preserve_crash := RO.exec_inv_preserve_crash.
Time Definition crash_inv_preserve_crash := RO.crash_inv_preserve_crash.
Time Definition state_interp_no_inv := RO.state_interp_no_inv.
Time Definition crash_inner_inv := RO.crash_inner_inv.
Time Definition exec_inner_inv := RO.exec_inner_inv.
Time Definition exec_inv_preserve_finish := RO.exec_inv_preserve_finish.
Time Lemma refinement_base_triples : RD.refinement_base_triples_type.
Time (intros ? ? ? ? j K ? p p' (op, (Heq1, Heq2))).
Time subst.
Time iApply refinement_op_triples.
Time Qed.
Time End RO'.
Time Module R:=  RefinementIdempotenceModule.refinement RT' RO'.
Time
Lemma crash_refinement_seq {T} \207\1311c \207\1311a (es : proc_seq OpT T) :
  init_absr \207\1311a \207\1311c
  \226\134\146 wf_client_seq es
    \226\134\146 \194\172 proc_exec_seq \206\155a es (rec_singleton (Ret ())) (1, \207\1311a) Err
      \226\134\146 \226\136\128 \207\1312c res,
          proc_exec_seq \206\155c (compile_proc_seq es) (rec_singleton recv)
            (1, \207\1311c) (Val \207\1312c res)
          \226\134\146 \226\136\131 \207\1312a,
              proc_exec_seq \206\155a es (rec_singleton (Ret tt)) 
                (1, \207\1311a) (Val \207\1312a res).
Time Proof.
Time (intros).
Time (eapply R.crash_refinement_seq; eauto).
Time clear.
Time (induction es; econstructor; eauto).
Time clear.
Time econstructor.
Time (induction p; eauto; try (repeat econstructor; done)).
Time *
Time (eapply cr_bind; eauto).
Time *
Time (eapply cr_loop; eauto).
Time *
Time (eapply cr_spawn; eauto).
Time Qed.
Time End refinement.
