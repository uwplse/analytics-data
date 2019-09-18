Time From stdpp Require Export strings.
Time From iris.proofmode Require Import base tokens.
Time Set Default Proof Using "Type".
Time
Inductive goal_kind :=
  | GSpatial : _
  | GModal : _
  | GIntuitionistic : _.
Time
Record spec_goal :=
 SpecGoal {spec_goal_kind : goal_kind;
           spec_goal_negate : bool;
           spec_goal_frame : list ident;
           spec_goal_hyps : list ident;
           spec_goal_done : bool}.
Time
Inductive spec_pat :=
  | SForall : spec_pat
  | SIdent : ident \226\134\146 list spec_pat \226\134\146 spec_pat
  | SPureGoal : forall perform_done : bool, spec_pat
  | SGoal : spec_goal \226\134\146 spec_pat
  | SAutoFrame : goal_kind \226\134\146 spec_pat.
Time
Definition goal_kind_modal (k : goal_kind) : bool :=
  match k with
  | GModal => true
  | _ => false
  end.
Time
Definition spec_pat_modal (p : spec_pat) : bool :=
  match p with
  | SGoal g => goal_kind_modal (spec_goal_kind g)
  | SAutoFrame k => goal_kind_modal k
  | _ => false
  end.
Time Module spec_pat.
Time
Inductive stack_item :=
  | StPat : spec_pat \226\134\146 stack_item
  | StIdent : string \226\134\146 stack_item.
Time Notation stack := (list stack_item).
Time
Fixpoint close (k : stack) (ps : list spec_pat) : 
option (list spec_pat) :=
  match k with
  | [] => Some ps
  | StPat p :: k => close k (p :: ps)
  | StIdent _ :: _ => None
  end.
Time
Fixpoint close_ident (k : stack) (ps : list spec_pat) : 
option stack :=
  match k with
  | [] => None
  | StPat p :: k => close_ident k (p :: ps)
  | StIdent s :: k => Some (StPat (SIdent s ps) :: k)
  end.
Time
Fixpoint parse_go (ts : list token) (k : stack) : 
option (list spec_pat) :=
  match ts with
  | [] => close k []
  | TParenL :: TName s :: ts => parse_go ts (StIdent s :: k)
  | TParenR :: ts => k \226\134\144 close_ident k []; parse_go ts k
  | TName s :: ts => parse_go ts (StPat (SIdent s []) :: k)
  | TBracketL :: TAlways :: TFrame :: TBracketR :: ts =>
      parse_go ts (StPat (SAutoFrame GIntuitionistic) :: k)
  | TBracketL :: TFrame :: TBracketR :: ts =>
      parse_go ts (StPat (SAutoFrame GSpatial) :: k)
  | TBracketL :: TModal :: TFrame :: TBracketR :: ts =>
      parse_go ts (StPat (SAutoFrame GModal) :: k)
  | TBracketL :: TPure :: TBracketR :: ts =>
      parse_go ts (StPat (SPureGoal false) :: k)
  | TBracketL :: TPure :: TDone :: TBracketR :: ts =>
      parse_go ts (StPat (SPureGoal true) :: k)
  | TBracketL :: TAlways :: ts => parse_goal ts GIntuitionistic false [] [] k
  | TBracketL :: TModal :: ts => parse_goal ts GModal false [] [] k
  | TBracketL :: ts => parse_goal ts GSpatial false [] [] k
  | TForall :: ts => parse_go ts (StPat SForall :: k)
  | _ => None
  end
with parse_goal (ts : list token) (ki : goal_kind) 
(neg : bool) (frame hyps : list ident) (k : stack) : 
option (list spec_pat) :=
  match ts with
  | TMinus :: ts =>
      guard \194\172 neg \226\136\167 frame = [] \226\136\167 hyps = [];
      parse_goal ts ki true frame hyps k
  | TName s :: ts => parse_goal ts ki neg frame (INamed s :: hyps) k
  | TFrame :: TName s :: ts =>
      parse_goal ts ki neg (INamed s :: frame) hyps k
  | TDone :: TBracketR :: ts =>
      parse_go ts
        (StPat (SGoal (SpecGoal ki neg (reverse frame) (reverse hyps) true))
         :: k)
  | TBracketR :: ts =>
      parse_go ts
        (StPat (SGoal (SpecGoal ki neg (reverse frame) (reverse hyps) false))
         :: k)
  | _ => None
  end.
Time
Definition parse (s : string) : option (list spec_pat) :=
  parse_go (tokenize s) [].
Time
Ltac
 parse s :=
  lazymatch type of s with
  | list spec_pat => s
  | spec_pat => [s]
  | string =>
      lazymatch eval vm_compute in (parse s) with
      | Some ?pats => pats
      | _ => fail "spec_pat.parse: cannot parse" s
      end
  | ident => [SIdent s []]
  | ?X => fail "spec_pat.parse:" s "has unexpected type" X
  end.
Time End spec_pat.
