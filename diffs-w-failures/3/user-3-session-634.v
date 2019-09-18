Require Extraction.
From Classes Require Import Classes.
From Array Require Export Array.
Set Implicit Arguments.
Axiom (bytes : nat -> Type).
Axiom (bytes_dec : forall n, EqualDec (bytes n)).
Existing Instance bytes_dec.
Axiom (bytes0 : forall n, bytes n).
Extraction Language Haskell.
Extract Constant bytes =>  "Data.ByteString.ByteString".
Extract Constant bytes_dec =>  "(\n b1 b2 -> b1 Prelude.== b2)".
Extract Constant bytes0 => 
 "(\n -> Data.ByteString.replicate (Prelude.fromIntegral n) 0)".
Definition blockbytes := 1024.
Definition block := bytes blockbytes.
Definition block0 : block := bytes0 _.
Instance bytes_default  n: (Default (bytes n)) := (bytes0 n).
Instance block_default : (Default block) := _.
Opaque blockbytes.
Definition disk := list block.
Definition addr := nat.
