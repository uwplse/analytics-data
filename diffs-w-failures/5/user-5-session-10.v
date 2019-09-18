Require Import Impl.Programs.
Require Import Impl.Typecheck.
Require Import Impl.Interpreter.
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellNatNum.
Require Import ExtrHaskellString.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellZNum.
Extraction Language Haskell.
Extraction "hs/VerifiedCore.hs"
 Id Ty Value Exp Stm Decl Prog typecheckProgram makeInitialState step.
