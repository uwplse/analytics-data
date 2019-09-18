Require Import String.
Require Export Impl.Ids.
Inductive Ty : Set :=
  | TBool : _
  | TInt32 : _
  | TString : _.
Inductive Value :=
  | VInt32 : nat -> Value
  | VBool : bool -> Value
  | VStr : string -> Value.
Inductive Exp : Set :=
  | EVar : Id -> Exp
  | ELit : Value -> Exp
  | EPlus : Exp -> Exp -> Exp
  | ECall : Id -> list Exp -> Exp.
Inductive Stm : Set :=
  | SNoOp : _
  | SSeq : Stm -> Stm -> Stm
  | SExp : Exp -> Stm
  | SAssign : Exp -> Exp -> Stm
  | SDecl : Id -> Ty -> Stm
  | SIf : Exp -> Stm -> Stm -> Stm
  | SWhile : Exp -> Stm -> Stm
  | SReturn : Exp -> Stm.
Inductive Decl : Set :=
  | DGlobal : Id -> Ty -> Decl
  | DFun : Id -> list (Id * Ty) -> Ty -> Stm -> Decl.
Definition Prog := list Decl.
