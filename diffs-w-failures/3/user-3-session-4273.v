Time From Coq.ssr Require Export ssreflect.
Time From stdpp Require Export prelude.
Time Set Default Proof Using "Type".
Time #[global]Open Scope general_if_scope.
Time #[global]Set SsrOldRewriteGoalsOrder.
Time Ltac done := stdpp.tactics.done.
