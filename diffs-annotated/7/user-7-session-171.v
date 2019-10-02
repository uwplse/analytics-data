Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
#[program]
Fixpoint subst (x : id) (s t : ty) {measure size t :=
  match t with
  | TCName _ => t
  | TPair t1 t2 => TPair (subst x s t1) (subst x s t2)
  | TUnion t1 t2 => TUnion ([x := s] t1) ([x := s] t2)
  | TExist y t' =>
      if IdSet.mem y (FV s)
      then let z := gen_fresh (IdSet.union (FV s) (FV t')) in let tz := [y @ z] t' in TExist z (if beq_id x z then tz else [x := s] tz)
      else TExist y (if beq_id x y then t' else [x := s] t')
  | TVar y => if beq_id x y then s else t
  | TEV y => t
  end
where "'[' x ':=' s ']' t" := (subst x s t) : btjt_scope.
(* Failed. *)
