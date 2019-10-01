Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqVOSw5L"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Inductive Marker : String.string -> Type :=
    mark : forall s, Marker s.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coqExPtxA"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Raw" "Proofs".
Set Search Output Name Only.
Redirect "/var/folders/5x/1mdbpbjd7012l971fq0zkj2w0000gn/T/coq0PM91J"
SearchPattern _.
Remove Search Blacklist "Raw" "Proofs".
Unset Search Output Name Only.
Theorem proc_spec_rx :
  forall `(spec : Specification A T R State) `(p : proc T) 
    `(rec : proc R) `(rx : T -> proc T')
    `(spec' : Specification A' T' R State) `(abs : Abstraction State),
  proc_spec spec p rec abs ->
  (forall a' state,
   pre (spec' a' state) ->
   exists a,
     pre (spec a state) /\
     (forall r state',
      recovered (spec a state) r state' ->
      Marker "recovered condition" -> recovered (spec' a' state) r state') /\
     (forall r,
      Marker "post condition" ->
      proc_spec
        (fun (_ : unit) state' =>
         {|
         pre := post (spec a state) r state';
         post := fun r state'' => post (spec' a' state) r state'';
         recovered := fun r state'' => recovered (spec' a' state) r state'' |})
        (rx r) rec abs)) -> proc_spec spec' (Bind p rx) rec abs.
