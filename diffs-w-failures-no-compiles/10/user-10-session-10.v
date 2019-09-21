Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqNaqxeg"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
Set Silent.
From Coq Require Import Basics ExtrOcamlIntConv List NArith String.
From ExtLib Require Import Applicative Functor Monad StateMonad.
From ITree Require Import Exception ITree Nondeterminism.
From SimpleIO Require Import IO_Random SimpleIO.
From QuickChick Require Import Decidability Show.
From DeepWeb Require Import Exp.
Import ApplicativeNotation FunctorNotation ListNotations MonadNotation
SumNotations.
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
Definition calculate_shared (s : secret_key) (p : public_key) : shared_key :=
  p ^ s mod prime.
Definition cipher_text := prod shared_key.
Definition cipher {plain_text} :
  shared_key -> plain_text -> cipher_text plain_text := pair.
Definition decipher {plain_text} (s : shared_key)
  (c : cipher_text plain_text) : option plain_text :=
  let (k, t) := c in if s =? k then Some t else None.
Definition random := N.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
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
         | Kvs_CAS k x v =>
             "CAS " ++ show k ++ " " ++ show x ++ " " ++ show v
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
         | Kvs_CAS k x v =>
             "CAS " ++ show k ++ " " ++ show x ++ " " ++ show v
         | Kvs_OK v => "OK  " ++ show v
         | Kvs_NoContent => "204"
         | Kvs_BadRequest => "400"
         | Kvs_PreconditionFailed => "412"
         end |}.
Definition kvs_get {V} (k : N) : list (N * V) -> option V :=
  fmap snd \226\136\152 find (N.eqb k \226\136\152 fst).
Definition kvs_put {K} {V} : K -> V -> list (K * V) -> list (K * V) :=
  compose cons \226\136\152 pair.
Module App.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Arguments appE : clear implicits.
Instance showAppE  {T}: (Show (appE id T)) :=
 {|
 show := fun ae =>
         match ae with
         | App_Recv => "Application Receive"
         | App_Send msg => "Application Send \226\159\185 " ++ show msg
         end |}.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
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
         | None =>
             v <- trigger Eval_Var;;
             embed App_Send (Kvs_OK v);; call (kvs_put k v st)
         end
     | Kvs_PUT k v =>
         embed App_Send Kvs_NoContent;; call (kvs_put k (exp_int v) st)
     | Kvs_CAS k x v' =>
         match kvs_get k st with
         | Some v =>
             b <- trigger (Eval_Decide (exp_eq x v));;
             (if b : bool
              then
               embed App_Send Kvs_NoContent;;
               call (kvs_put k (exp_int v') st)
              else embed App_Send Kvs_PreconditionFailed;; call st)
         | None =>
             v <- trigger Eval_Var;;
             b <- trigger (Eval_Decide (exp_eq x v));;
             (if b : bool
              then
               embed App_Send Kvs_NoContent;;
               call (kvs_put k (exp_int v') st)
              else
               embed App_Send Kvs_PreconditionFailed;; call (kvs_put k v st))
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
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition embed_exp {T} {E} `{appE id -< E} (ex : appE exp T) : 
  itree E T :=
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
         | Err_Mismatch e0 te =>
             "Events mismatch: " ++ show e0 ++ " <> " ++ show te
         | Err_Unify bx b => "Cannot unify: " ++ show bx ++ " <> " ++ show b
         end |}.
Unset Silent.
Definition nmi_of_smi {T} (m : itree smE T) :
  itree (appE id +' exceptE err +' randomE) T :=
  interp
    (fun T e =>
     match e return (_ (appE id +' exceptE err +' randomE) T) with
     | (ae|) => embed_exp ae
     | (|ee) =>
         match ee in (evalE T) return (_ T) with
         | Eval_Var => n <- trigger Random_Value;; ret (exp_int n)
         | Eval_Decide bx =>
             match unwrap' bx with
             | Some b => ret b
             | None => throw (Err_Decide bx)
             end
         end
     end) m.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqLMjfun"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Silent.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition unifier_of_smi :
  itree smE void -> itree (appE id +' unifyE +' randomE) unit :=
  rec-fix unifier_of_smi_rec m
  := match (m : itree smE void).(observe) with
     | RetF vd => match vd in void with
                  end
     | TauF m' => unifier_of_smi_rec m'
     | VisF (sae|) k =>
         match sae in (appE _ Y) return ((Y -> _) -> _) with
         | App_Recv =>
             fun k =>
             r <- trigger Random_Request;;
             embed App_Send r;; unifier_of_smi_rec (k r)
         | App_Send rx =>
             fun k =>
             r <- embed App_Recv;;
             trigger (Unify_Guard rx r);; unifier_of_smi_rec (k tt)
         end k
     | VisF (|ee) k =>
         match ee in (evalE Y) return ((Y -> _) -> _) with
         | Eval_Var => bind (trigger Unify_New) \226\136\152 compose unifier_of_smi_rec
         | Eval_Decide bx =>
             bind (embed Unify_Decide bx) \226\136\152 compose unifier_of_smi_rec
         end k
     end.
Notation taE := (appE id +' exceptE err +' nondetE +' randomE).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Definition liftState {s a : Type} {m : Type -> Type} 
  `{Functor m} : m a -> stateT s m a :=
  @mkStateT s m a \226\136\152 flip compose (flip pair) \226\136\152 flip fmap.
Definition tester_of_unifier (u : itree (appE id +' unifyE +' randomE) unit)
  : stateT state (itree taE) unit :=
  interp
    (fun X e =>
     match e with
     | (|(ue|)) => handle_unifier ue
     | (e|) | (||e) => @liftState state X (itree taE) _ (trigger e)
     end) u.
End App.
Module Network.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Instance showPlainMessage : (Show plain_message) :=
 {|
 show := fun pm =>
         match pm with
         | PlainMessage_Hello messageRandom messagePublic =>
             "Hello! random: " ++
             show messageRandom ++ ", public key: " ++ show messagePublic
         | PlainMessage_Finished verifyData =>
             "Finished! verify data: " ++ show verifyData
         | PlainMessage_AppData kvsData =>
             "Application Data! " ++ show kvsData
         | PlainMessage_BadRequest => "Bad Request!"
         end |}.
Inductive message :=
  | Message_Plain : forall plainMessage : plain_message, _
  | Message_Cipher : forall cipherMessage : cipher_text plain_message, _.
Derive Show for message.
Instance eqMessage  (x y : message): (Dec (x = y)).
Proof.
dec_eq.
Defined.
Definition Message_Finished (k : shared_key) (verifyData : N) : message :=
  Message_Cipher (cipher k (PlainMessage_Finished verifyData)).
Definition Message_Hello (messageRandom : random)
  (messagePublic : public_key) : message :=
  Message_Plain (PlainMessage_Hello messageRandom messagePublic).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Import App.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Derive Show for error.
Notation hsE := (networkE +' exceptE error +' hsgenE).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"."
Please report at http://coq.inria.fr/bugs/.
Unset Silent.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqiFtR30"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Printing Width 114.
Unset Silent.
Set Printing Width 114.
Unset Silent.
Set Printing Width 114.
Definition network_of_app {nE} `{networkE -< nE} `{exceptE error -< nE} {E} `{E -< nE} 
  (k : shared_key) T (e : (appE id +' E) T) : itree nE T :=
  match e with
  | (ae|) =>
      match ae with
      | App_Recv =>
          msg <- trigger Network_Recv;;
          match msg with
          | Message_Plain _ => throw Error_UnexpectedMessage
          | Message_Cipher msg =>
              match decipher k msg with
              | Some msg =>
                  match msg with
                  | PlainMessage_AppData data => ret data
                  | _ => throw Error_UnexpectedMessage
                  end
              | None => throw Error_UnexpectedMessage
              end
          end
      | App_Send data => embed Network_Send (Message_Cipher (cipher k (PlainMessage_AppData data)))
      end
  | (|e) => trigger e
  end.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqNOYexa" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Set Silent.
Notation sE := (networkE +' exceptE error +' hsgenE +' randomE).
Notation tE := (nondetE +' sE).
CoFixpoint match_event {X} (e0 : networkE X) (x0 : X) (t : itree tE unit) : itree tE unit :=
  match t.(observe) with
  | RetF r => Ret r
  | TauF t => Tau (match_event e0 x0 t)
  | VisF e k =>
      match e with
      | (|(ne|)) =>
          match e0 in (networkE X), ne in (networkE Y) return ((Y -> _) -> X -> _) with
          | Network_Recv, Network_Recv => id
          | Network_Send m1, Network_Send m2 =>
              if m1 = m2 ? then id else fun _ _ => throw Error_UnexpectedMessage
          | _, _ => fun _ _ => throw Error_UnexpectedBehavior
          end k x0
      | (e|) | (||e|) | (|||e|) | (||||e) => vis e (match_event e0 x0 \226\136\152 k)
      end
  end.
Definition match_event_list {X} : networkE X -> X -> list (itree tE unit) -> list (itree tE unit) :=
  compose pfmap \226\136\152 match_event.
Unset Silent.
Check nmi_of_smi.
Check nmi_of_smi.
Check network_of_app.
Print sE.
Check interp.
Print interp.
Check interp.
Print interp.
Definition server : itree sE void :=
  sk <- translate subevent serverHandshake;; interp (network_of_app sk) (nmi_of_smi kvs).
