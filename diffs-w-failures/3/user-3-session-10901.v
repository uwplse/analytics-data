Time From stdpp Require Export strings.
Time From iris.proofmode Require Import base tokens.
Time Set Default Proof Using "Type".
Time
Inductive sel_pat :=
  | SelPure : _
  | SelIntuitionistic : _
  | SelSpatial : _
  | SelIdent : ident \226\134\146 sel_pat.
Time
Fixpoint sel_pat_pure (ps : list sel_pat) : bool :=
  match ps with
  | [] => false
  | SelPure :: ps => true
  | _ :: ps => sel_pat_pure ps
  end.
Time Module sel_pat.
Time
Fixpoint parse_go (ts : list token) (k : list sel_pat) :
option (list sel_pat) :=
  match ts with
  | [] => Some (reverse k)
  | TName s :: ts => parse_go ts (SelIdent s :: k)
  | TPure :: ts => parse_go ts (SelPure :: k)
  | TAlways :: ts => parse_go ts (SelIntuitionistic :: k)
  | TSep :: ts => parse_go ts (SelSpatial :: k)
  | _ => None
  end.
Time
Definition parse (s : string) : option (list sel_pat) :=
  parse_go (tokenize s) [].
Time
Ltac
 parse s :=
  lazymatch type of s with
  | sel_pat => [s]
  | list sel_pat => s
  | ident => [SelIdent s]
  | list ident => eval vm_compute in (SelIdent <$> s)
  | list string => eval vm_compute in (SelIdent \226\136\152 INamed <$> s)
  | string =>
      lazymatch eval vm_compute in (parse s) with
      | Some ?pats => pats
      | _ => fail "invalid sel_pat" s
      end
  end.
Time End sel_pat.
