Require Import List.
Require Import Impl.Programs.
Require Import Impl.Typecheck.
Require Import Definitions.Zip.
Inductive ValueWt : Value -> Ty -> Prop :=
  | VBool_wt : forall b, ValueWt (VBool b) TBool
  | VInt_wt : forall i, ValueWt (VInt32 i) TInt32
  | VStr_wt : forall s, ValueWt (VStr s) TString.
Inductive LookupVarType : list (Id * Ty) -> Id -> Ty -> Prop :=
  | LookupVarTypeHere :
      forall id t rest, LookupVarType (cons (id, t) rest) id t
  | LookupVarTypeElsewhere :
      forall ida ta idb tb rest,
      ida <> idb ->
      LookupVarType rest idb tb -> LookupVarType (cons (ida, ta) rest) idb tb.
Inductive LookupFunctionType :
list (Id * list Ty * Ty) -> Id -> list Ty -> Ty -> Prop :=
  | LookupFunctionTypeHere :
      forall id argTypes retType rest,
      LookupFunctionType (cons (id, argTypes, retType) rest) id argTypes
        retType
  | LookupFunctionTypeElsewhere :
      forall ida argTypesA retTypeA idb argTypesB retTypeB rest,
      ida <> idb ->
      LookupFunctionType rest idb argTypesB retTypeB ->
      LookupFunctionType (cons (ida, argTypesA, retTypeA) rest) idb argTypesB
        retTypeB.
Inductive ExpWt : TypeEnvironment -> Exp -> Ty -> Prop :=
  | EVar_wt :
      forall env id t, LookupVarType (vars env) id t -> ExpWt env (EVar id) t
  | ELit_wt : forall env val t, ValueWt val t -> ExpWt env (ELit val) t
  | EPlus_wt :
      forall env e1 e2,
      ExpWt env e1 TInt32 ->
      ExpWt env e2 TInt32 -> ExpWt env (EPlus e1 e2) TInt32
  | ECall_wt :
      forall env f args argTypes argsZipped retType,
      LookupFunctionType (functions env) f argTypes retType ->
      Zip args argTypes argsZipped ->
      (forall a t, In (a, t) argsZipped -> ExpWt env a t) ->
      ExpWt env (ECall f args) retType.
Inductive IsLVal : Exp -> Prop :=
    EVar_lval : forall id, IsLVal (EVar id).
Inductive StmWt : TypeEnvironment -> Stm -> Ty -> Prop :=
  | SNoOp_wt : forall env t, StmWt env SNoOp t
  | SSeq_wt :
      forall env t s1 s2,
      StmWt env s1 t -> StmWt env s2 t -> StmWt env (SSeq s1 s2) t
  | SExp_wt : forall env t tRet e, ExpWt env e t -> StmWt env (SExp e) tRet
  | SAssign_wt :
      forall env t tRet l r,
      IsLVal l ->
      ExpWt env l t -> ExpWt env r t -> StmWt env (SAssign l r) tRet
  | SDecl_wt : forall env id t tRet, StmWt env (SDecl id t) tRet
  | SIf_wt :
      forall env cond s1 s2 tRet,
      ExpWt env cond TBool ->
      StmWt env s1 tRet ->
      StmWt env s2 tRet -> StmWt env (SIf cond s1 s2) tRet
  | SWhile_wt :
      forall env cond body tRet,
      ExpWt env cond TBool ->
      StmWt env body tRet -> StmWt env (SWhile cond body) tRet
  | SReturn_wt : forall env e t, ExpWt env e t -> StmWt env (SReturn e) t.
Inductive AllPathsReturn : Stm -> Prop :=
  | SReturn_returns : forall e, AllPathsReturn (SReturn e)
  | SSeq_returns_l :
      forall s1 s2, AllPathsReturn s1 -> AllPathsReturn (SSeq s1 s2)
  | SSeq_returns_r :
      forall s1 s2, AllPathsReturn s2 -> AllPathsReturn (SSeq s1 s2)
  | SIf_returns :
      forall cond s1 s2,
      AllPathsReturn s1 ->
      AllPathsReturn s2 -> AllPathsReturn (SIf cond s1 s2).
Inductive DeclWt : TypeEnvironment -> Decl -> Prop :=
  | DGlobal_wt : forall env id t, DeclWt env (DGlobal id t)
  | DFun_wt :
      forall env f args ret body,
      StmWt (addVars args env) body ret ->
      AllPathsReturn body -> DeclWt env (DFun f args ret body).
Definition ProgWt (p : Prog) : Prop :=
  forall decl, In decl p -> DeclWt (makeEnv p) decl.
