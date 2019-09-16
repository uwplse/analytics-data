Require Import Impl.Ids.
Require Import List.
Import ListNotations.
Require Import String.
Require Import Impl.Programs.
Definition Environment := list (Id * Value).
Definition GlobalState := Environment.
Record StmState : Set :=
 MakeStmState {ss_stm : Stm;
               ss_envs : list Environment;
               ss_globals : GlobalState}.
Definition Continuation := Value -> Stm * list Environment.
Record State : Set :=
 MakeState {evaluating : StmState;
            call_stack : list Continuation;
            code : Prog}.
Open Scope string_scope.
Require Import Impl.Programs.
Definition typesEq (t1 t2 : Ty) : bool :=
  match t1, t2 with
  | TBool, TBool => true
  | TInt32, TInt32 => true
  | TString, TString => true
  | _, _ => false
  end.
Record TypeEnvironment : Set :=
 MakeTypeEnvironment {vars : list (Id * Ty);
                      functions : list (Id * list Ty * Ty)}.
Definition addVars (vars : list (Id * Ty)) (env : TypeEnvironment) :
  TypeEnvironment :=
  let (oldVars, oldFuncs) := env in
  MakeTypeEnvironment (vars ++ oldVars) oldFuncs.
Definition addDecl (d : Decl) (env : TypeEnvironment) : TypeEnvironment :=
  match d with
  | DGlobal id t => addVars [(id, t)] env
  | DFun f args ret body =>
      let (oldVars, oldFuncs) := env in
      MakeTypeEnvironment oldVars ((f, map snd args, ret) :: oldFuncs)
  end.
Fixpoint makeEnv (p : Prog) : TypeEnvironment :=
  match p with
  | [] => MakeTypeEnvironment [] []
  | d :: rest => addDecl d (makeEnv rest)
  end.
Definition typeOfValue (v : Value) : Ty :=
  match v with
  | VInt32 _ => TInt32
  | VBool _ => TBool
  | VStr _ => TString
  end.
Inductive TcRes (T : Set) : Set :=
  | Ok : T -> TcRes T
  | Errors : list string -> TcRes T.
Arguments Ok [_] _.
Arguments Errors [_] _.
Definition combine {T U : Set} (merge : T -> T -> TcRes U) 
  (x y : TcRes T) :=
  match x, y with
  | Ok x', Ok y' => merge x' y'
  | Errors es1, Errors es2 => Errors (es1 ++ es2)
  | Errors errs, _ => Errors errs
  | _, Errors errs => Errors errs
  end.
Fixpoint lookupVarType (v : Id) (vars : list (Id * Ty)) : 
option Ty :=
  match vars with
  | [] => None
  | (vv, t) :: rest =>
      if id_eq_dec v vv then Some t else lookupVarType v rest
  end.
Fixpoint lookupFuncType (f : Id) (funcs : list (Id * list Ty * Ty)) :
option (list Ty * Ty) :=
  match funcs with
  | [] => None
  | (ff, args, ret) :: rest =>
      if id_eq_dec f ff then Some (args, ret) else lookupFuncType f rest
  end.
Fixpoint typeOfExpr (env : TypeEnvironment) (e : Exp) : 
TcRes Ty :=
  match e with
  | ELit val => Ok (typeOfValue val)
  | EVar v =>
      match lookupVarType v (vars env) with
      | Some t => Ok t
      | None => Errors ["no var " ++ v]
      end
  | ECall f args =>
      match lookupFuncType f (functions env) with
      | Some (argtypes, rettype) =>
          (fix checkArg args argtypes :=
             match args, argtypes with
             | nil, nil => Ok rettype
             | arg :: restargs, argtype :: resttypes =>
                 combine
                   (fun tt res =>
                    if typesEq tt argtype
                    then Ok res
                    else Errors ["incorrect type for argument"])
                   (typeOfExpr env arg) (checkArg restargs resttypes)
             | nil, _ => Errors ["missing arguments in call to " ++ f]
             | _, nil => Errors ["extra arguments in call to " ++ f]
             end) args argtypes
      | None => Errors ["no function " ++ f]
      end
  | EPlus e1 e2 =>
      combine
        (fun t1 t2 =>
         match t1, t2 with
         | TInt32, TInt32 => Ok TInt32
         | _, _ => Errors ["cannot add types"]
         end) (typeOfExpr env e1) (typeOfExpr env e2)
  end.
Fixpoint isLVal (e : Exp) : bool :=
  match e with
  | EVar _ => true
  | _ => false
  end.
Definition combinel {T : Set} := combine (fun x y : T => Ok x).
Definition addError {T : Set} (err : string) (x : TcRes T) : 
  TcRes T :=
  match x with
  | Ok _ => Errors [err]
  | Errors es => Errors (es ++ [err])
  end.
Definition require {T : Set} (cond : bool) (err : string) 
  (x : TcRes T) : TcRes T := if cond then x else addError err x.
Fixpoint stmWellTyped (env : TypeEnvironment) (ret : Ty) 
(s : Stm) : TcRes unit :=
  match s with
  | SNoOp => Ok tt
  | SSeq s1 s2 =>
      combinel (stmWellTyped env ret s1) (stmWellTyped env ret s2)
  | SExp e =>
      match typeOfExpr env e with
      | Ok _ => Ok tt
      | Errors es => Errors es
      end
  | SAssign l r =>
      combine
        (fun lt rt =>
         require (isLVal l) "assignment to non-lvalue"
           (require (typesEq lt rt) "assignment to incompatible type" (Ok tt)))
        (typeOfExpr env l) (typeOfExpr env r)
  | SDecl _ _ => Ok tt
  | SIf e s1 s2 =>
      match typeOfExpr env e with
      | Ok TBool =>
          combinel (stmWellTyped env ret s1) (stmWellTyped env ret s2)
      | Ok _ => Errors ["branch on non-boolean"]
      | Errors errs => Errors errs
      end
  | SWhile e body =>
      match typeOfExpr env e with
      | Ok TBool => stmWellTyped env ret body
      | Ok _ => Errors ["branch on non-boolean"]
      | Errors errs => Errors errs
      end
  | SReturn e =>
      match typeOfExpr env e with
      | Ok t => require (typesEq ret t) "incorrect return type" (Ok tt)
      | Errors errs => Errors errs
      end
  end.
Fixpoint allPathsReturn (s : Stm) : bool :=
  match s with
  | SReturn _ => true
  | SSeq s1 s2 => allPathsReturn s1 || allPathsReturn s2
  | SIf _ s1 s2 => allPathsReturn s1 && allPathsReturn s2
  | _ => false
  end.
Definition declWt (env : TypeEnvironment) (d : Decl) : 
  TcRes unit :=
  match d with
  | DGlobal _ _ => Ok tt
  | DFun f args ret body =>
      match stmWellTyped (addVars args env) ret body with
      | Errors _ as E => E
      | Ok _ =>
          if allPathsReturn body
          then Ok tt
          else Errors ["not all paths return"]
      end
  end.
Fixpoint typecheckProgram_helper (env : TypeEnvironment) 
(p : Prog) : TcRes unit :=
  match p with
  | [] => Ok tt
  | decl :: rest =>
      combinel (declWt env decl) (typecheckProgram_helper env rest)
  end.
Definition typecheckProgram (p : Prog) : TcRes unit :=
  typecheckProgram_helper (makeEnv p) p.
