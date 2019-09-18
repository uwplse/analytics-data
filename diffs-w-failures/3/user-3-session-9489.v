Cd "runtime/extract/".
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Extraction Language Haskell.
Require Import Lab1.StatDbCli.
Extract Inlined Constant PeanoNat.Nat.div => 
 "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Separate Extraction cli.
Recursive Extraction Library Helpers.
Cd "../../".
