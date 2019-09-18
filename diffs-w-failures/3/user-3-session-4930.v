Time From iris.proofmode Require Import coq_tactics environments.
Time From stdpp Require Export strings.
Time Set Default Proof Using "Type".
Time Delimit Scope proof_scope with env.
Time Arguments Envs _ _%proof_scope _%proof_scope _.
Time Arguments Enil {_}.
Time Arguments Esnoc {_} _%proof_scope _%string _%I.
Time Notation "" := Enil (only printing) : proof_scope.
Time
Notation "\206\147 H : P" := (Esnoc \206\147 (INamed H) P%I)
  (at level 1, P  at level 200, left associativity,
   format "\206\147 H  :  '[' P ']' '//'", only printing) : proof_scope.
Time
Notation "\206\147 '_' : P" := (Esnoc \206\147 (IAnon _) P%I)
  (at level 1, P  at level 200, left associativity,
   format "\206\147 '_'  :  '[' P ']' '//'", only printing) : proof_scope.
Time
Notation
  "\206\147 '--------------------------------------' \226\150\161 \206\148 '--------------------------------------' \226\136\151 Q" :=
  (envs_entails (Envs \206\147 \206\148 _) Q%I)
  (at level 1, Q  at level 200, left associativity,
   format "\206\147 '--------------------------------------' \226\150\161 '//' \206\148 '--------------------------------------' \226\136\151 '//' Q '//'",
   only printing) : stdpp_scope.
Time
Notation "\206\148 '--------------------------------------' \226\136\151 Q" :=
  (envs_entails (Envs Enil \206\148 _) Q%I)
  (at level 1, Q  at level 200, left associativity,
   format "\206\148 '--------------------------------------' \226\136\151 '//' Q '//'",
   only printing) : stdpp_scope.
Time
Notation "\206\147 '--------------------------------------' \226\150\161 Q" :=
  (envs_entails (Envs \206\147 Enil _) Q%I)
  (at level 1, Q  at level 200, left associativity,
   format "\206\147 '--------------------------------------' \226\150\161 '//' Q '//'",
   only printing) : stdpp_scope.
Time
Notation "'--------------------------------------' \226\136\151 Q" :=
  (envs_entails (Envs Enil Enil _) Q%I)
  (at level 1, Q  at level 200,
   format "'--------------------------------------' \226\136\151 '//' Q '//'",
   only printing) : stdpp_scope.
