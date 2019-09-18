Time From stdpp Require Export strings.
Time From iris.proofmode Require Import base tokens sel_patterns.
Time Set Default Proof Using "Type".
Time
Inductive intro_pat :=
  | IIdent : ident \226\134\146 intro_pat
  | IFresh : intro_pat
  | IDrop : intro_pat
  | IFrame : intro_pat
  | IList : list (list intro_pat) \226\134\146 intro_pat
  | IPureElim : intro_pat
  | IAlwaysElim : intro_pat \226\134\146 intro_pat
  | IModalElim : intro_pat \226\134\146 intro_pat
  | IRewrite : direction \226\134\146 intro_pat
  | IPureIntro : intro_pat
  | IAlwaysIntro : intro_pat
  | IModalIntro : intro_pat
  | ISimpl : intro_pat
  | IDone : intro_pat
  | IForall : intro_pat
  | IAll : intro_pat
  | IClear : sel_pat \226\134\146 intro_pat
  | IClearFrame : sel_pat \226\134\146 intro_pat.
Time Module intro_pat.
Time
Inductive stack_item :=
  | StPat : intro_pat \226\134\146 stack_item
  | StList : stack_item
  | StConjList : stack_item
  | StBar : stack_item
  | StAmp : stack_item
  | StAlwaysElim : stack_item
  | StModalElim : stack_item.
Time Notation stack := (list stack_item).
Time
Fixpoint close_list (k : stack) (ps : list intro_pat)
(pss : list (list intro_pat)) : option stack :=
  match k with
  | StList :: k => Some (StPat (IList (ps :: pss)) :: k)
  | StPat pat :: k => close_list k (pat :: ps) pss
  | StAlwaysElim :: k =>
      ' '(p, ps) \226\134\144 maybe2 (::) ps; close_list k (IAlwaysElim p :: ps) pss
  | StModalElim :: k =>
      ' '(p, ps) \226\134\144 maybe2 (::) ps; close_list k (IModalElim p :: ps) pss
  | StBar :: k => close_list k [] (ps :: pss)
  | _ => None
  end.
Time
Fixpoint big_conj (ps : list intro_pat) : intro_pat :=
  match ps with
  | [] => IList [[]]
  | [p] => IList [[p]]
  | [p1; p2] => IList [[p1; p2]]
  | p :: ps => IList [[p; big_conj ps]]
  end.
Time
Fixpoint close_conj_list (k : stack) (cur : option intro_pat)
(ps : list intro_pat) : option stack :=
  match k with
  | StConjList :: k =>
      ps
      \226\134\144 match cur with
        | None => guard ps = []; Some []
        | Some p => Some (p :: ps)
        end; Some (StPat (big_conj ps) :: k)
  | StPat pat :: k => guard cur = None; close_conj_list k (Some pat) ps
  | StAlwaysElim :: k => p \226\134\144 cur; close_conj_list k (Some (IAlwaysElim p)) ps
  | StModalElim :: k => p \226\134\144 cur; close_conj_list k (Some (IModalElim p)) ps
  | StAmp :: k => p \226\134\144 cur; close_conj_list k None (p :: ps)
  | _ => None
  end.
Time
Fixpoint parse_go (ts : list token) (k : stack) : 
option stack :=
  match ts with
  | [] => Some k
  | TName "_" :: ts => parse_go ts (StPat IDrop :: k)
  | TName s :: ts => parse_go ts (StPat (IIdent s) :: k)
  | TAnon :: ts => parse_go ts (StPat IFresh :: k)
  | TFrame :: ts => parse_go ts (StPat IFrame :: k)
  | TBracketL :: ts => parse_go ts (StList :: k)
  | TBar :: ts => parse_go ts (StBar :: k)
  | TBracketR :: ts => close_list k [] [] \226\137\171= parse_go ts
  | TParenL :: ts => parse_go ts (StConjList :: k)
  | TAmp :: ts => parse_go ts (StAmp :: k)
  | TParenR :: ts => close_conj_list k None [] \226\137\171= parse_go ts
  | TPure :: ts => parse_go ts (StPat IPureElim :: k)
  | TAlways :: ts => parse_go ts (StAlwaysElim :: k)
  | TModal :: ts => parse_go ts (StModalElim :: k)
  | TArrow d :: ts => parse_go ts (StPat (IRewrite d) :: k)
  | TPureIntro :: ts => parse_go ts (StPat IPureIntro :: k)
  | TAlwaysIntro :: ts => parse_go ts (StPat IAlwaysIntro :: k)
  | TModalIntro :: ts => parse_go ts (StPat IModalIntro :: k)
  | TSimpl :: ts => parse_go ts (StPat ISimpl :: k)
  | TDone :: ts => parse_go ts (StPat IDone :: k)
  | TAll :: ts => parse_go ts (StPat IAll :: k)
  | TForall :: ts => parse_go ts (StPat IForall :: k)
  | TBraceL :: ts => parse_clear ts k
  | _ => None
  end
with parse_clear (ts : list token) (k : stack) : option stack :=
  match ts with
  | TFrame :: TName s :: ts =>
      parse_clear ts (StPat (IClearFrame (SelIdent s)) :: k)
  | TFrame :: TPure :: ts =>
      parse_clear ts (StPat (IClearFrame SelPure) :: k)
  | TFrame :: TAlways :: ts =>
      parse_clear ts (StPat (IClearFrame SelIntuitionistic) :: k)
  | TFrame :: TSep :: ts =>
      parse_clear ts (StPat (IClearFrame SelSpatial) :: k)
  | TName s :: ts => parse_clear ts (StPat (IClear (SelIdent s)) :: k)
  | TPure :: ts => parse_clear ts (StPat (IClear SelPure) :: k)
  | TAlways :: ts => parse_clear ts (StPat (IClear SelIntuitionistic) :: k)
  | TSep :: ts => parse_clear ts (StPat (IClear SelSpatial) :: k)
  | TBraceR :: ts => parse_go ts k
  | _ => None
  end.
Time
Fixpoint close (k : stack) (ps : list intro_pat) : 
option (list intro_pat) :=
  match k with
  | [] => Some ps
  | StPat pat :: k => close k (pat :: ps)
  | StAlwaysElim :: k =>
      ' '(p, ps) \226\134\144 maybe2 (::) ps; close k (IAlwaysElim p :: ps)
  | StModalElim :: k =>
      ' '(p, ps) \226\134\144 maybe2 (::) ps; close k (IModalElim p :: ps)
  | _ => None
  end.
Time
Definition parse (s : string) : option (list intro_pat) :=
  k \226\134\144 parse_go (tokenize s) []; close k [].
Time
Ltac
 parse s :=
  lazymatch type of s with
  | list intro_pat => s
  | intro_pat => [s]
  | list string =>
      lazymatch eval vm_compute in (mjoin <$> mapM parse s) with
      | Some ?pats => pats
      | _ => fail "intro_pat.parse: cannot parse" s
      end
  | string =>
      lazymatch eval vm_compute in (parse s) with
      | Some ?pats => pats
      | _ => fail "intro_pat.parse: cannot parse" s
      end
  | ident => [IIdent s]
  | ?X => fail "intro_pat.parse:" s "has unexpected type" X
  end.
Time
Ltac
 parse_one s :=
  lazymatch type of s with
  | intro_pat => s
  | string =>
      lazymatch eval vm_compute in (parse s) with
      | Some [?pat] => pat
      | _ => fail "intro_pat.parse_one: cannot parse" s
      end
  | ?X => fail "intro_pat.parse_one:" s "has unexpected type" X
  end.
Time End intro_pat.
Time
Fixpoint intro_pat_intuitionistic (p : intro_pat) :=
  match p with
  | IPureElim => true
  | IAlwaysElim _ => true
  | IList pps => forallb (forallb intro_pat_intuitionistic) pps
  | ISimpl => true
  | IClear _ => true
  | IClearFrame _ => true
  | _ => false
  end.
Time
Ltac
 intro_pat_intuitionistic p :=
  lazymatch type of p with
  | intro_pat => eval compute in (intro_pat_intuitionistic p)
  | list intro_pat =>
      eval compute in (forallb intro_pat_intuitionistic p)
  | string =>
      let pat := intro_pat.parse p in
      eval compute in (forallb intro_pat_intuitionistic pat)
  | ident => false
  | bool => p
  | ?X => fail "intro_pat_intuitionistic:" p "has unexpected type" X
  end.
