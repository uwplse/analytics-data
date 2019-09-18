Time Cd "replicated-disk/extract/".
Time From Coq Require Extraction.
Time Require Import ExtrHaskellNatInteger.
Time Require Import ExtrHaskellBasic.
Time From Armada Require Import Examples.ReplicatedDisk.ReplicatedDiskImpl.
Time Extraction Language Haskell.
Time Extract Constant Impl.LogHdr_fmt =>  "logHdrFmt".
