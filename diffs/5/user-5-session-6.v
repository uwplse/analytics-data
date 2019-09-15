Require Import List.
Require Import String.
Import ListNotations.
Require Import String.
Open Scope string_scope.
Require Import Relations.
Require Import Definitions.Zip.
Require Import Impl.Ids.
Require Import Impl.Programs.
Require Import Impl.EvaluationState.
Inductive Lookup : Environment -> Id -> Value -> Prop :=
  | LookupHere : forall id val rest, Lookup (cons (id, val) rest) id val
  | LookupElsewhere :
      forall ida vala idb valb rest,
      ida <> idb ->
      Lookup rest idb valb -> Lookup (cons (ida, vala) rest) idb valb.
Open Scope string_scope.
Require Import List.
Section exp_semantics.
Inductive ExpCtx : (Exp -> Exp) -> Prop :=
  | ExpCtx_top : ExpCtx (fun e => e)
  | ExpCtx_binleft :
      forall e2 ctx, ExpCtx ctx -> ExpCtx (fun e1 => EPlus (ctx e1) e2)
  | ExpCtx_binright :
      forall v1 ctx,
      ExpCtx ctx -> ExpCtx (fun e2 => EPlus (ELit v1) (ctx e2))
  | ExpCtx_call :
      forall f lctx, ExpCtxSeq lctx -> ExpCtx (fun e => ECall f (lctx e))
with ExpCtxSeq : (Exp -> list Exp) -> Prop :=
  | ExpCtxSeq_head :
      forall ctx rest, ExpCtx ctx -> ExpCtxSeq (fun e => ctx e :: rest)
  | ExpCtxSeq_tail :
      forall v lctx, ExpCtxSeq lctx -> ExpCtxSeq (fun e => ELit v :: lctx e).
Import ListNotations.
Require Import Impl.Ids.
Require Import Impl.Programs.
Require Import Impl.EvaluationState.
Definition makeInitialState (p : Prog) : State :=
  MakeState (MakeStmState (SReturn (ECall "main" [])) [] []) [] p.
Inductive InterpResult (T : Set) : Set :=
  | Return : T -> InterpResult T
  | Error : string -> InterpResult T.
Arguments Return [T] _.
Arguments Error [T] _.
Variable (env : Environment).
Inductive ExpReduce : Exp -> Exp -> Prop :=
  | VarReduce :
      forall var val, Lookup env var val -> ExpReduce (EVar var) (ELit val)
  | PlusReduce :
      forall v1 v2,
      ExpReduce (EPlus (ELit (VInt32 v1)) (ELit (VInt32 v2)))
        (ELit (VInt32 (v1 + v2))).
End exp_semantics.
Notation "x <- A ; B" :=
  match A with
  | Return x => B
  | Error str => Error str
  end (at level 100, right associativity).
Fixpoint lookup (env : Environment) (id : Id) : InterpResult Value :=
  match env with
  | [] => Error ("no variable " ++ id ++ " in scope")
  | (x, y) :: rest => if id_eq_dec x id then Return y else lookup rest id
  end.
Definition reduceExp (env : Environment) (e : Exp) :
  InterpResult (option Exp) :=
  match e with
  | EVar var => val <- lookup env var; Return (Some (ELit val))
  | EPlus (ELit (VInt32 a)) (ELit (VInt32 b)) =>
      Return (Some (ELit (VInt32 (a + b))))
  | _ => Return None
  end.
Section stm_semantics.
Inductive StmExpCtx : (Exp -> Stm) -> Prop :=
  | StmExpCtx_SSeq :
      forall S s, StmExpCtx S -> StmExpCtx (fun e => SSeq (S e) s)
  | StmExpCtx_SExp : StmExpCtx (fun e => SExp e)
  | StmExpCtx_SAssign : forall lval, StmExpCtx (fun e => SAssign lval e)
  | StmExpCtx_SIf : forall x y, StmExpCtx (fun e => SIf e x y)
  | StmExpCtx_SReturn : StmExpCtx (fun e => SReturn e).
Inductive StmReduce : Stm -> Stm -> Prop :=
  | StmReduce_seq : forall s, StmReduce (SSeq SNoOp s) s
  | StmReduce_ret :
      forall v s, StmReduce (SSeq (SReturn (ELit v)) s) (SReturn (ELit v))
  | StmReduce_exp : forall v, StmReduce (SExp (ELit v)) SNoOp
  | StmReduce_if1 : forall x y, StmReduce (SIf (ELit (VBool true)) x y) x
  | StmReduce_if2 : forall x y, StmReduce (SIf (ELit (VBool false)) x y) y
  | StmReduce_while :
      forall e body,
      StmReduce (SWhile e body) (SIf e (SSeq body (SWhile e body)) SNoOp).
Inductive StmStep : StmState -> StmState -> Prop :=
  | StmStep_exp :
      forall sctx ectx e e' envs globals,
      StmExpCtx sctx ->
      ExpCtx ectx ->
      ExpReduce (List.concat (envs ++ [globals])) e e' ->
      StmStep (MakeStmState (sctx (ectx e)) envs globals)
        (MakeStmState (sctx (ectx e')) envs globals)
  | StmStep_seq1 :
      forall s s' s2 env env' g g',
      StmStep (MakeStmState s env g) (MakeStmState s' env' g') ->
      StmStep (MakeStmState (SSeq s s2) env g)
        (MakeStmState (SSeq s' s2) env' g')
  | StmStep_reduce :
      forall s s' env g,
      StmReduce s s' ->
      StmStep (MakeStmState s env g) (MakeStmState s' env g).
End stm_semantics.
Fixpoint findExpContext (e : Exp) : option (Exp * (Exp -> Exp)) :=
  match e with
  | EVar _ => Some (e, fun e => e)
  | EPlus x y =>
      match findExpContext x with
      | Some (e, ctx) => Some (e, fun e' => EPlus (ctx e') y)
      | None =>
          match findExpContext y with
          | Some (e, ctx) => Some (e, fun e' => EPlus x (ctx e'))
          | None => Some (e, fun e => e)
          end
      end
  | ECall f es =>
      match
        (fix findContextInList (es : list Exp) :
           option (Exp * (Exp -> list Exp)) :=
           match es with
           | [] => None
           | e :: rest =>
               match findExpContext e with
               | Some (e', ectx) => Some (e', fun x => ectx x :: rest)
               | None =>
                   match findContextInList rest with
                   | Some (e', ectx) => Some (e', fun x => e :: ectx x)
                   | None => None
                   end
               end
           end) es
      with
      | Some (e, ctx) => Some (e, fun e' => ECall f (ctx e'))
      | None => Some (e, fun e => e)
      end
  | _ => None
  end.
Inductive AllValues : list Exp -> list Value -> Prop :=
  | AllNil : AllValues [] []
  | AllCons :
      forall v le lv, AllValues le lv -> AllValues (ELit v :: le) (v :: lv).
Definition isFunctionNamed (name : Id) (decl : Decl) : Prop :=
  match decl with
  | DFun f _ _ _ => name = f
  | _ => False
  end.
Inductive LookupFunction : Prog -> Id -> list Id -> Stm -> Prop :=
  | LookupFunctionHere :
      forall f args argtypes argspec retty body rest,
      Zip args argtypes argspec ->
      LookupFunction (DFun f argspec retty body :: rest) f args body
  | LookupFunctionElsewhere :
      forall decl prog f args body,
      ~ isFunctionNamed f decl ->
      LookupFunction prog f args body ->
      LookupFunction (decl :: prog) f args body.
Fixpoint findContextInList (es : list Exp) : option (Exp * (Exp -> list Exp))
:=
  match es with
  | [] => None
  | e :: rest =>
      match findExpContext e with
      | Some (e', ectx) => Some (e', fun x => ectx x :: rest)
      | None =>
          match findContextInList rest with
          | Some (e', ectx) => Some (e', fun x => e :: ectx x)
          | None => None
          end
      end
  end.
Inductive Step : State -> State -> Prop :=
  | Step_stm :
      forall s s' ks prog,
      StmStep s s' -> Step (MakeState s ks prog) (MakeState s' ks prog)
  | Step_call :
      forall f args argv ectx sctx argspec body envs env ks globals prog,
      AllValues args argv ->
      LookupFunction prog f argspec body ->
      Zip argspec argv env ->
      ExpCtx ectx ->
      StmExpCtx sctx ->
      Step
        (MakeState (MakeStmState (sctx (ectx (ECall f args))) envs globals)
           ks prog)
        (MakeState (MakeStmState body [env] globals)
           ((fun res => (sctx (ectx (ELit res)), envs)) :: ks) prog)
  | Step_return :
      forall v k krest envs globals prog,
      Step
        (MakeState (MakeStmState (SReturn (ELit v)) envs globals)
           (k :: krest) prog)
        (MakeState (MakeStmState (fst (k v)) (snd (k v)) globals) krest prog).
Fixpoint findExpToEvaluate (s : Stm) : option (Exp * (Exp -> Stm)) :=
  match s with
  | SSeq a b =>
      match findExpToEvaluate a with
      | Some (e, ctx) => Some (e, fun e' => SSeq (ctx e') b)
      | None => None
      end
  | SExp e => Some (e, fun e' => SExp e')
  | SAssign lval e => Some (e, fun e' => SAssign lval e')
  | SIf cond a b => Some (cond, fun cond' => SIf cond' a b)
  | SReturn e => Some (e, fun e' => SReturn e')
  | _ => None
  end.
Definition reduceStm (s : Stm) : option Stm :=
  match s with
  | SSeq SNoOp s' => Some s'
  | SSeq (SReturn (ELit _) as R) _ => Some R
  | SExp (ELit _) => Some SNoOp
  | SIf (ELit (VBool true)) s' _ => Some s'
  | SIf (ELit (VBool false)) _ s' => Some s'
  | SWhile e body => Some (SIf e (SSeq body s) SNoOp)
  | _ => None
  end.
Definition stepExpInStm (s : Stm) (envs : list Environment)
  (globals : GlobalState) : InterpResult (option StmState) :=
  match findExpToEvaluate s with
  | Some (e, sctx) =>
      match findExpContext e with
      | Some (e, ectx) =>
          res <- reduceExp (List.concat (envs ++ [globals])) e;
          match res with
          | Some e' =>
              Return (Some (MakeStmState (sctx (ectx e')) envs globals))
          | None => Return None
          end
      | _ => Return None
      end
  | _ => Return None
  end.
Inductive Initial : Prog -> State -> Prop :=
    IsInitial :
      forall code,
      Initial code
        (MakeState (MakeStmState (SReturn (ECall "main" [])) [] []) [] code).
Inductive Done : State -> Prop :=
    ReturnWithNoContinuationIsDone :
      forall value scopes globals p,
      Done (MakeState (MakeStmState (SReturn value) scopes globals) [] p).
Definition Trace : State -> State -> Prop := clos_refl_trans _ Step.
Definition reduceStmOrStepExp (s : Stm) (envs : list Environment)
  (globals : GlobalState) : InterpResult (option StmState) :=
  match reduceStm s with
  | Some s' => Return (Some (MakeStmState s' envs globals))
  | None => stepExpInStm s envs globals
  end.
Fixpoint stepStm' (s : Stm) (envs : list Environment) 
(globals : GlobalState) : option StmState :=
  match reduceStm s with
  | Some s' => Some (MakeStmState s' envs globals)
  | None =>
      match s with
      | SSeq s1 s2 =>
          match stepStm' s1 envs globals with
          | Some (MakeStmState s1' envs' globals') =>
              Some (MakeStmState (SSeq s1' s2) envs' globals')
          | None => None
          end
      | _ => None
      end
  end.
Definition stepStm (st : StmState) : InterpResult (option StmState) :=
  let (s, envs, globals) := st in
  expStep <- stepExpInStm s envs globals;
  match expStep with
  | Some s' => Return (Some s')
  | None => Return (stepStm' s envs globals)
  end.
Fixpoint values (es : list Exp) : option (list Value) :=
  match es with
  | [] => Some []
  | ELit v :: rest =>
      match values rest with
      | Some rest' => Some (v :: rest')
      | None => None
      end
  | _ => None
  end.
Fixpoint findFunc (f : Id) (p : Prog) : option (list Id * Stm) :=
  match p with
  | [] => None
  | DGlobal _ _ :: rest => findFunc f rest
  | DFun name args retTy body :: rest =>
      if id_eq_dec name f then Some (map fst args, body) else findFunc f rest
  end.
Fixpoint zip {A B} (x : list A) (y : list B) : option (list (A * B)) :=
  match x, y with
  | [], [] => Some []
  | xx :: xs, yy :: ys =>
      match zip xs ys with
      | Some l => Some ((xx, yy) :: l)
      | None => None
      end
  | _, _ => None
  end.
Definition callStep (st : State) : InterpResult State :=
  let (ss, ks, prog) := st in
  let (s, envs, globals) := ss in
  match findExpToEvaluate s with
  | Some (e, sctx) =>
      match findExpContext e with
      | Some (e, ectx) =>
          match e with
          | ECall f vals =>
              match findFunc f prog with
              | Some (argnames, body) =>
                  match values vals with
                  | Some argv =>
                      match zip argnames argv with
                      | Some env =>
                          Return
                            (MakeState (MakeStmState body [env] globals)
                               ((fun res => (sctx (ectx (ELit res)), envs))
                                :: ks) prog)
                      | None => Error "incorrect number of args"
                      end
                  | None => Error "arguments are not all values"
                  end
              | None => Error ("no function " ++ f)
              end
          | _ => Error "expression to reduce is not a call"
          end
      | _ => Error "expression is not reducible"
      end
  | _ => Error "statement is not reducible"
  end.
Definition returnValue (s : Stm) : option Value :=
  match s with
  | SReturn (ELit v) => Some v
  | _ => None
  end.
Definition step (st : State) : InterpResult (option State) :=
  let (ss, ks, prog) := st in
  maybe_ss' <- stepStm ss;
  match maybe_ss' with
  | Some ss' => Return (Some (MakeState ss' ks prog))
  | None =>
      let (s, envs, globals) := ss in
      match returnValue s with
      | Some val =>
          match ks with
          | k :: rest =>
              let (s', envs') := k val in
              Return
                (Some (MakeState (MakeStmState s' envs' globals) rest prog))
          | [] => Return None
          end
      | _ => st' <- callStep st; Return (Some st')
      end
  end.
