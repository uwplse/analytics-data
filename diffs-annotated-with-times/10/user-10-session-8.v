Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqAHa5FS"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import Basics ExtrOcamlIntConv List NArith String.
From ExtLib Require Import Applicative Functor Monad StateMonad.
From ITree Require Import Exception ITree Nondeterminism.
From SimpleIO Require Import IO_Random SimpleIO.
From QuickChick Require Import Decidability Show.
From DeepWeb Require Import Exp.
Import ApplicativeNotation FunctorNotation ListNotations MonadNotation SumNotations.
Open Scope N_scope.
Open Scope monad_scope.
Open Scope program_scope.
Open Scope sum_scope.
Definition secret_key := N.
Definition public_key := N.
Definition shared_key := N.
Definition base := 5.
Definition prime := 23.
Definition derive_public (k : secret_key) : public_key := base ^ k mod prime.
Definition calculate_shared (s : secret_key) (p : public_key) : shared_key := p ^ s mod prime.
Definition cipher_text := prod shared_key.
Definition cipher {plain_text} : shared_key -> plain_text -> cipher_text plain_text := pair.
Definition decipher {plain_text} (s : shared_key) (c : cipher_text plain_text) : option plain_text :=
  let (k, t) := c in if s =? k then Some t else None.
Definition random := N.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Arguments kvs_data : clear implicits.
Instance eqKvs_data  (x y : kvs_data id): (Dec (x = y)).
Proof.
dec_eq.
Defined.
Instance showData : (Show (kvs_data id)) :=
 {|
 show := fun d =>
         match d with
         | Kvs_GET k => "GET " ++ show k
         | Kvs_PUT k v => "PUT " ++ show k ++ " " ++ show v
         | Kvs_CAS k x v => "CAS " ++ show k ++ " " ++ show x ++ " " ++ show v
         | Kvs_OK v => "OK  " ++ show (v : N)
         | Kvs_NoContent => "204"
         | Kvs_BadRequest => "400"
         | Kvs_PreconditionFailed => "412"
         end |}.
Instance showDataX : (Show (kvs_data exp)) :=
 {|
 show := fun d =>
         match d with
         | Kvs_GET k => "GET " ++ show k
         | Kvs_PUT k v => "PUT " ++ show k ++ " " ++ show v
         | Kvs_CAS k x v => "CAS " ++ show k ++ " " ++ show x ++ " " ++ show v
         | Kvs_OK v => "OK  " ++ show v
         | Kvs_NoContent => "204"
         | Kvs_BadRequest => "400"
         | Kvs_PreconditionFailed => "412"
         end |}.
Definition kvs_get {V} (k : N) : list (N * V) -> option V := fmap snd \226\136\152 find (N.eqb k \226\136\152 fst).
Definition kvs_put {K} {V} : K -> V -> list (K * V) -> list (K * V) := compose cons \226\136\152 pair.
Module App.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Arguments appE : clear implicits.
Instance showAppE  {T}: (Show (appE id T)) :=
 {|
 show := fun ae =>
         match ae with
         | App_Recv => "Application Receive"
         | App_Send msg => "Application Send \226\159\185 " ++ show msg
         end |}.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition smE := appE exp +' evalE.
Definition kvs_state exp_ := list (N * exp_ N).
Definition kvs : itree smE void :=
  rec
    (fun st : kvs_state exp =>
     req <- trigger App_Recv;;
     match req with
     | Kvs_GET k =>
         match kvs_get k st with
         | Some v => embed App_Send (Kvs_OK v);; call st
         | None => v <- trigger Eval_Var;; embed App_Send (Kvs_OK v);; call (kvs_put k v st)
         end
     | Kvs_PUT k v => embed App_Send Kvs_NoContent;; call (kvs_put k (exp_int v) st)
     | Kvs_CAS k x v' =>
         match kvs_get k st with
         | Some v =>
             b <- trigger (Eval_Decide (exp_eq x v));;
             (if b : bool
              then embed App_Send Kvs_NoContent;; call (kvs_put k (exp_int v') st)
              else embed App_Send Kvs_PreconditionFailed;; call st)
         | None =>
             v <- trigger Eval_Var;;
             b <- trigger (Eval_Decide (exp_eq x v));;
             (if b : bool
              then embed App_Send Kvs_NoContent;; call (kvs_put k (exp_int v') st)
              else embed App_Send Kvs_PreconditionFailed;; call (kvs_put k v st))
         end
     | _ => embed App_Send Kvs_BadRequest;; call st
     end) [].
Definition unwrap_data (rx : kvs_data exp) : kvs_data id :=
  match rx with
  | Kvs_GET k => Kvs_GET k
  | Kvs_PUT k v => Kvs_PUT k v
  | Kvs_CAS k x v => Kvs_CAS k x v
  | Kvs_OK vx => Kvs_OK (unwrap vx)
  | Kvs_NoContent => Kvs_NoContent
  | Kvs_BadRequest => Kvs_BadRequest
  | Kvs_PreconditionFailed => Kvs_PreconditionFailed
  end.
Definition wrap_data (r : kvs_data id) : kvs_data exp :=
  match r with
  | Kvs_GET k => Kvs_GET k
  | Kvs_PUT k v => Kvs_PUT k v
  | Kvs_CAS k x v => Kvs_CAS k x v
  | Kvs_OK v => Kvs_OK (exp_int v)
  | Kvs_NoContent => Kvs_NoContent
  | Kvs_BadRequest => Kvs_BadRequest
  | Kvs_PreconditionFailed => Kvs_PreconditionFailed
  end.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition embed_exp {T} {E} `{appE id -< E} (ex : appE exp T) : itree E T :=
  match ex in (appE _ T) return (itree E T) with
  | App_Recv => trigger App_Recv
  | App_Send rx => trigger (App_Send (unwrap_data rx))
  end.
Variant err :=
  | Err_Decide : forall bx : exp bool, _
  | Err_Guard : forall (rx : kvs_data exp) (r : kvs_data id), _
  | Err_Mismatch : forall {X} {Y} (e0 : appE id X) (te : appE id Y), _
  | Err_Unify : forall (bx : exp bool) (b : bool), _.
Instance showErr : (Show err) :=
 {|
 show := fun e =>
         match e with
         | Err_Decide bx => "Cannot decide: " ++ show bx
         | Err_Guard rx r => "Guard error: " ++ show rx ++ " <> " ++ show r
         | Err_Mismatch e0 te => "Events mismatch: " ++ show e0 ++ " <> " ++ show te
         | Err_Unify bx b => "Cannot unify: " ++ show bx ++ " <> " ++ show b
         end |}.
Definition nmi_of_smi {T} (m : itree smE T) : itree (appE id +' exceptE err +' randomE) T :=
  interp
    (fun T e =>
     match e with
     | (ae|) => embed_exp ae
     | (|ee) =>
         match ee in (evalE T) return (_ T) with
         | Eval_Var => n <- trigger (||Random_Value);; ret (exp_int n)
         | Eval_Decide bx => match unwrap' bx with
                             | Some b => ret b
                             | None => ret false
                             end
         end
     end) m.
(* Auto-generated comment: Succeeded. *)

