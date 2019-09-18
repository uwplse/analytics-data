Time Require FunctionalExtensionality.
Time From Transitions Require Import Relations Rewriting.
Time Require Import Spec.Proc.
Time Require Import Spec.ProcTheorems.
Time Require Import Tactical.ProofAutomation.
Time Import RelationNotations.
Time
Record Layer Op :={OpState : Type;
                   sem : Dynamics Op OpState;
                   trace_proj : OpState -> list Event;
                   crash_preserves_trace :
                    forall s1 s2,
                    sem.(crash_step) s1 (Val s2 tt) ->
                    trace_proj s1 = trace_proj s2;
                   crash_total :
                    forall s1, exists s2, sem.(crash_step) s1 (Val s2 tt);
                   finish_total :
                    forall s1, exists s2, sem.(finish_step) s1 (Val s2 tt);
                   crash_non_err :
                    forall s1 ret, sem.(crash_step) s1 ret -> ret <> Err;
                   finish_non_err :
                    forall s1 ret, sem.(finish_step) s1 ret -> ret <> Err;
                   initP : OpState -> Prop}.
Time Definition State `(L : Layer Op) := @Proc.State L.(OpState).
Time Coercion sem : Layer >-> Dynamics.
Time
Record LayerImpl C_Op Op :={compile_op : forall `(op : Op T), proc C_Op T;
                            recover : rec_seq C_Op}.
Time
Fixpoint compile Op C_Op `(impl : LayerImpl C_Op Op) 
T (p : proc Op T) : proc C_Op T :=
  match p with
  | Call op => impl.(compile_op) op
  | Ret v => Ret v
  | Bind p p' => Bind (impl.(compile) p) (fun v => impl.(compile) (p' v))
  | Loop b init => Loop (fun mt => impl.(compile) (b mt)) init
  | Unregister => Unregister
  | Wait => Wait
  | Spawn p => Spawn (impl.(compile) p)
  end.
Time Import ProcNotations.
Time
Definition compile_whole Op C_Op `(impl : LayerImpl C_Op Op) 
  T (p : proc Op T) : proc C_Op T :=
  Bind (compile impl p) (fun v => _ <- Wait; Ret v)%proc.
Time
Fixpoint map_proc_seq {T Op C_Op} (f : forall T, proc Op T -> proc C_Op T)
(es : proc_seq Op T) :=
  match es with
  | Proc_Seq_Nil v => Proc_Seq_Nil v : proc_seq C_Op T
  | @Proc_Seq_Bind _ _ T0 e es' =>
      Proc_Seq_Bind (f _ (e : proc Op T0)) (fun x => map_proc_seq f (es' x))
  end.
Time
Fixpoint compile_seq Op C_Op `(impl : LayerImpl C_Op Op) 
(ps : rec_seq Op) : rec_seq C_Op :=
  match ps with
  | Seq_Nil => Seq_Nil
  | Seq_Cons p ps' =>
      Seq_Cons (compile_whole impl p) (impl.(compile_seq) ps')
  end.
Time
Definition compile_proc_seq {T} Op C_Op `(impl : LayerImpl C_Op Op)
  (ps : proc_seq Op T) := map_proc_seq (compile_whole impl) ps.
Time
Definition compile_rec Op C_Op `(impl : LayerImpl C_Op Op) 
  (rec : rec_seq Op) : rec_seq C_Op :=
  rec_seq_append impl.(recover) (compile_seq impl rec).
Time
Record LayerImplRel C_Op Op :={compile_rel_base :
                                forall {T}, proc Op T -> proc C_Op T -> Prop;
                               recover_rel : rec_seq C_Op}.
Time
Inductive compile_rel Op C_Op `(impl : LayerImplRel C_Op Op) :
forall T, proc Op T -> proc C_Op T -> Prop :=
  | cr_base :
      forall {T} (p1 : proc Op T) p2,
      impl.(compile_rel_base) p1 p2 -> compile_rel impl p1 p2
  | cr_ret : forall {T} (v : T), compile_rel impl (Ret v) (Ret v)
  | cr_bind :
      forall {T1} {T2} (p1 : proc Op T1) (p1' : forall T1, proc Op T2) p2 p2',
      compile_rel impl p1 p2 ->
      (forall x, compile_rel impl (p1' x) (p2' x)) ->
      compile_rel impl (Bind p1 p1') (Bind p2 p2')
  | cr_loop :
      forall {T} {R} (b : T -> proc Op (LoopOutcome T R)) b' init,
      (forall mt, compile_rel impl (b mt) (b' mt)) ->
      compile_rel impl (Loop b init) (Loop b' init)
  | cr_unregister : compile_rel impl Unregister Unregister
  | cr_wait : compile_rel impl Wait Wait
  | cr_spawn :
      forall {T} (p : proc Op T) p',
      compile_rel impl p p' -> compile_rel impl (Spawn p) (Spawn p').
Time
Inductive compile_rel_whole Op C_Op `(impl : LayerImplRel C_Op Op) 
T : proc Op T -> proc C_Op T -> Prop :=
    cr_whole :
      forall p p',
      compile_rel impl p p' ->
      compile_rel_whole impl p (Bind p' (fun v => _ <- Wait; Ret v))%proc.
Time
Inductive compile_rel_proc_seq {T} {Op} {C_Op} `(impl : LayerImplRel C_Op Op)
: proc_seq Op T -> proc_seq C_Op T -> Prop :=
  | cr_seq_nil :
      forall v : T,
      compile_rel_proc_seq impl (Proc_Seq_Nil v) (Proc_Seq_Nil v)
  | cr_seq_cons :
      forall {T'} (p : proc Op T') p' f f',
      compile_rel_whole impl p p' ->
      (forall x, compile_rel_proc_seq impl (f x) (f' x)) ->
      compile_rel_proc_seq impl (Proc_Seq_Bind p f) (Proc_Seq_Bind p' f').
Time
Definition LayerImpl_to_LayerImplRel {C_Op} {Op} (impl : LayerImpl C_Op Op) :
  LayerImplRel C_Op Op :=
  {|
  compile_rel_base := fun {T} =>
                      fun p p' =>
                      exists op : Op T,
                        p = Call op /\ p' = compile impl (Call op);
  recover_rel := recover impl |}.
