Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqDQo6Ez"
Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqm16FTG"
Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import Basics ExtrOcamlIntConv List NArith String.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqRp5hKL" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Print Analytics.
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
Definition nmi_of_smi {T} (m : itree smE T) : itree (appE id) T :=
  interp
    (fun T e =>
     match e with
     | (ae|) => embed_exp ae
     | (|ee) =>
         match ee in (evalE T) return (_ T) with
         | Eval_Var => ret (exp_int 0)
         | Eval_Decide bx => match unwrap' bx with
                             | Some b => ret b
                             | None => ret false
                             end
         end
     end) m.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition unifier_of_smi : itree smE void -> itree (appE id +' unifyE +' randomE) unit :=
  rec-fix unifier_of_smi_rec m
  := match (m : itree smE void).(observe) with
     | RetF vd => match vd in void with
                  end
     | TauF m' => unifier_of_smi_rec m'
     | VisF (sae|) k =>
         match sae in (appE _ Y) return ((Y -> _) -> _) with
         | App_Recv => fun k => r <- trigger Random_Request;; embed App_Send r;; unifier_of_smi_rec (k r)
         | App_Send rx => fun k => r <- embed App_Recv;; trigger (Unify_Guard rx r);; unifier_of_smi_rec (k tt)
         end k
     | VisF (|ee) k =>
         match ee in (evalE Y) return ((Y -> _) -> _) with
         | Eval_Var => bind (trigger Unify_New) \226\136\152 compose unifier_of_smi_rec
         | Eval_Decide bx => bind (embed Unify_Decide bx) \226\136\152 compose unifier_of_smi_rec
         end k
     end.
Notation taE := (appE id +' exceptE err +' nondetE +' randomE).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition liftState {s a : Type} {m : Type -> Type} `{Functor m} : m a -> stateT s m a :=
  @mkStateT s m a \226\136\152 flip compose (flip pair) \226\136\152 flip fmap.
Definition tester_of_unifier (u : itree (appE id +' unifyE +' randomE) unit) : stateT state (itree taE) unit :=
  interp
    (fun X e =>
     match e with
     | (|(ue|)) => handle_unifier ue
     | (e|) | (||e) => @liftState state X (itree taE) _ (trigger e)
     end) u.
CoFixpoint match_event {X} (e0 : appE id X) (x0 : X) (t : itree taE unit) : itree taE unit :=
  match t.(observe) with
  | RetF r => Ret r
  | TauF t => Tau (match_event e0 x0 t)
  | VisF e k =>
      match e with
      | (te|) =>
          match e0 in (appE _ X), te in (appE _ Y) return ((Y -> _) -> X -> _) with
          | App_Recv, App_Recv => id
          | App_Send m1, App_Send m2 => if m1 = m2 ? then id else fun _ _ => throw (Err_Mismatch e0 te)
          | _, _ => fun _ _ => throw (Err_Mismatch e0 te)
          end k x0
      | (|(e|)) | (||e|) | (|||e) => vis e (match_event e0 x0 \226\136\152 k)
      end
  end.
Definition match_event_list {X} (e0 : appE id X) (x : X) : list (itree taE unit) -> list (itree taE unit) :=
  map (match_event e0 x).
End App.
Module Network.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Instance showPlainMessage : (Show plain_message) :=
 {|
 show := fun pm =>
         match pm with
         | PlainMessage_Hello messageRandom messagePublic =>
             "Hello! random: " ++ show messageRandom ++ ", public key: " ++ show messagePublic
         | PlainMessage_Finished verifyData => "Finished! verify data: " ++ show verifyData
         | PlainMessage_AppData kvsData => "Application Data! " ++ show kvsData
         | PlainMessage_BadRequest => "Bad Request!"
         end |}.
Inductive message :=
  | Message_Plain : forall plainMessage : plain_message, _
  | Message_Cipher : forall cipherMessage : cipher_text plain_message, _.
Derive Show for message.
Definition Message_Finished (k : shared_key) (verifyData : N) : message :=
  Message_Cipher (cipher k (PlainMessage_Finished verifyData)).
Definition Message_Hello (messageRandom : random) (messagePublic : public_key) : message :=
  Message_Plain (PlainMessage_Hello messageRandom messagePublic).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Import App.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Derive Show for error.
Notation hsE := (networkE +' exceptE error +' hsgenE).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition network_of_app {nE} `{networkE -< nE} `{exceptE error -< nE} (k : shared_key) 
  T (ae : appE id T) : itree nE T :=
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
  end.
Notation sE := (networkE +' exceptE error +' hsgenE +' randomE).
Notation tE := (nondetE +' sE).
Definition server : itree sE void :=
  sk <- translate subevent serverHandshake;; interp (network_of_app sk) (nmi_of_smi kvs).
Definition map_exceptE {e1} {e2} (f : e1 -> e2) : exceptE e1 ~> exceptE e2 :=
  fun _ e => match e with
             | Throw e => Throw (f e)
             end.
Definition network_of_app_ta sk : taE ~> itree tE :=
  fun _ tae =>
  match tae with
  | (ae|) => network_of_app sk _ ae
  | (|(e|)) => trigger (map_exceptE Error_App _ e)
  | (||tae) => trigger tae
  end.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition showSE (se : sigT (fun X => sE X * X)%type) : string :=
  match se with
  | existT _ _ er =>
      let (e, r) := er in
      match e with
      | (ne|) =>
          match ne in (networkE X) return (X -> _) with
          | Network_Recv => fun m => "Network     Recv to   server: " ++ show m
          | Network_Send m => fun _ => "Network     Send from server: " ++ show m
          end r
      | (|(Throw _|)) => "This message should never be printed."
      | (||hge|) =>
          match hge in (hsgenE X) return (X -> _) with
          | HsGen_Key => fun k => "Handshake   Generate Key    : " ++ show k
          | HsGen_Random => fun r => "Handshake   Generate Random : " ++ show r
          end r
      | (|||re) =>
          match re in (randomE X) return (X -> _) with
          | Random_Value => fun n => "Server      Generate Value  : " ++ show n
          | Random_Requst => fun r => "Tester      Generate Request: " ++ show r
          end r
      end
  end.
Definition showTE (te : sigT (fun X => tE X * X)%type) : string :=
  match te with
  | existT _ _ er =>
      let (e, r) := er in
      match e with
      | (ne|) =>
          match ne in (nondetE X) return (X -> _) with
          | Or => fun b => "Flip coin and get           : " ++ show b
          end r
      | (|se) => showSE (existT _ _ (se, r))
      end
  end.
Instance showEvent : (Show event) :=
 {|
 show := fun e =>
         match e with
         | Event_Tester te => showTE te
         | Event_Server se => showSE se
         | Event_Retry e => "Retry upon exception        : " ++ show e
         end |}.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Notation zE := (exceptE error +' traceE +' hsgenE +' randomE +' nondetE).
CoFixpoint zip' (others : list (itree tE unit)) (client : itree tE unit) (server : itree sE void) : 
itree zE unit :=
  let retry : forall e : error, itree zE unit :=
    fun e : error =>
    match others with
    | [] => throw e
    | some :: others' => embed Trace (Event_Retry e);; Tau (zip' others' some server)
    end in
  match client.(observe) with
  | RetF tt => Ret tt
  | TauF c' => Tau (zip' others c' server)
  | VisF te tk =>
      match te with
      | (ne|) =>
          match ne in (nondetE Y) return ((Y -> _) -> _) with
          | Or =>
              fun tk =>
              b <- trigger Or;;
              embed Trace (Event_Tester (existT _ _ ((Or|), b)));;
              Tau (zip' (tk (negb b) :: others) (tk b) server)
          end tk
      | (|(te|)) =>
          match server.(observe) with
          | RetF vd => match vd in void with
                       end
          | TauF s' => Tau (zip' others client s')
          | VisF se sk =>
              match se with
              | (se|) =>
                  match se in (networkE Z) return ((Z -> _) -> _) with
                  | Network_Recv =>
                      fun sk =>
                      match te in (networkE Y) return ((Y -> _) -> _) with
                      | Network_Recv => fun _ => retry Error_UnexpectedBehavior
                      | Network_Send msg =>
                          fun tk =>
                          embed Trace (Event_Server (existT _ _ ((Network_Recv|), msg)));;
                          Tau (zip' others (tk tt) (sk msg))
                      end tk
                  | Network_Send msg =>
                      fun sk =>
                      match te in (networkE Y) return ((Y -> _) -> _) with
                      | Network_Recv =>
                          fun tk =>
                          embed Trace (Event_Server (existT _ _ ((Network_Send msg|), tt)));;
                          Tau (zip' others (tk msg) (sk tt))
                      | Network_Send _ => fun _ => retry Error_UnexpectedBehavior
                      end tk
                  end sk
              | (|(ee|)) => retry Error_UnexpectedBehavior
              | (||hge|) =>
                  match hge in (hsgenE Y) return ((Y -> _) -> _) with
                  | HsGen_Key =>
                      fun sk =>
                      k <- trigger HsGen_Key;;
                      embed Trace (Event_Server (existT _ _ ((||HsGen_Key|), k)));;
                      Tau (zip' others client (sk k))
                  | HsGen_Random =>
                      fun sk =>
                      r <- trigger HsGen_Random;;
                      embed Trace (Event_Server (existT _ _ ((||HsGen_Random|), r)));;
                      Tau (zip' others client (sk r))
                  end sk
              | (|||re) =>
                  match re in (randomE Y) return ((Y -> _) -> _) with
                  | Random_Value =>
                      fun sk =>
                      n <- trigger Random_Value;;
                      embed Trace (Event_Server (existT _ _ ((|||Random_Value), n)));;
                      Tau (zip' others client (sk n))
                  | Random_Request =>
                      fun sk =>
                      r <- trigger Random_Request;;
                      embed Trace (Event_Server (existT _ _ ((|||Random_Request), r)));;
                      Tau (zip' others client (sk r))
                  end sk
              end
          end
      | (||Throw e|) => retry e
      | (|||hge|) =>
          match hge in (hsgenE Y) return ((Y -> _) -> _) with
          | HsGen_Key =>
              fun tk =>
              k <- trigger HsGen_Key;;
              embed Trace (Event_Tester (existT _ _ ((|||HsGen_Key|), k)));; Tau (zip' others (tk k) server)
          | HsGen_Random =>
              fun tk =>
              r <- trigger HsGen_Random;;
              embed Trace (Event_Tester (existT _ _ ((|||HsGen_Random|), r)));; Tau (zip' others (tk r) server)
          end tk
      | (||||re) =>
          match re in (randomE Y) return ((Y -> _) -> _) with
          | Random_Value =>
              fun tk =>
              n <- trigger Random_Value;;
              embed Trace (Event_Tester (existT _ _ ((||||Random_Value), n)));; Tau (zip' others (tk n) server)
          | Random_Request =>
              fun tk =>
              r <- trigger Random_Request;;
              embed Trace (Event_Tester (existT _ _ ((||||Random_Request), r)));; Tau (zip' others (tk r) server)
          end tk
      end
  end.
Definition _zip (_ : unit) : itree tE unit -> itree sE void -> itree zE unit := zip' [].
Notation zip := (_zip tt).
End Network.
Module Test.
Import App Network.
Definition random_N : N -> IO N := fmap n_of_int \226\136\152 ORandom.int \226\136\152 int_of_n.
Definition random_kvs_data : IO (kvs_data id) :=
  n <- random_N 3;;
  match n with
  | 0 => Kvs_GET <$> random_N 10
  | 1 => (Kvs_PUT <$> random_N 10) <*> random_N 10
  | _ => ((Kvs_CAS <$> random_N 10) <*> random_N 10) <*> random_N 10
  end.
Fixpoint exec_test' (fuel : nat) (m : itree zE unit) : IO bool :=
  match fuel with
  | O => ret true
  | S fuel =>
      match m.(observe) with
      | RetF tt => ret true
      | TauF m' => exec_test' fuel m'
      | VisF ze k =>
          match ze with
          | (Throw e|) => prerr_endline (show e);; ret false
          | (|(te|)) =>
              match te in (traceE Y) return ((Y -> _) -> _) with
              | Trace e => fun k => prerr_endline (show e);; exec_test' fuel (k tt)
              end k
          | (||ge) =>
              sk <- random_N 5;;
              n <- random_N 10;;
              r <- random_kvs_data;;
              b <- ORandom.bool tt;;
              exec_test' fuel
                match ge with
                | (hge|) =>
                    match hge in (hsgenE Y) return ((Y -> _) -> _) with
                    | HsGen_Key => fun k => k sk
                    | HsGen_Random => fun k => k n
                    end k
                | (|(re|)) =>
                    match re in (randomE Y) return ((Y -> _) -> _) with
                    | Random_Value => fun k => k n
                    | Random_Request => fun k => k r
                    end k
                | (||ne) => match ne in (nondetE Y) return ((Y -> _) -> _) with
                            | Or => fun k => k b
                            end k
                end
          end
      end
  end.
Definition exec_test : itree zE unit -> IO bool := exec_test' 5000.
Definition test_crypto : itree zE unit := zip tester server.
End Test.
Redirect "/var/folders/lm/cpf87_lx21n9bgnl4kr72rjm0000gn/T/coqwPV8is" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
(* Auto-generated comment: Succeeded. *)

