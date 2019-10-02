Redirect "/tmp/coq16819l_l" Test Search Output Name Only.
Timeout 1 Print Grammar tactic.
Add Search Blacklist "Private_" "_subproof".
Set Printing Depth 50.
Remove Search Blacklist "Private_" "_subproof".
Add Search Blacklist "Private_" "_subproof".
From Coq Require Import ExtrOcamlIntConv.
From ExtLib Require Import Applicative StateMonad Monad.
From ITree Require Import Exception Nondeterminism ITree.
From SimpleIO Require Import IO_Random SimpleIO.
From DeepWeb Require Import CryptoLib KvsLib.
Redirect "/tmp/coq16819_Ty" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819xdB" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819-nH" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819LyN" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Redirect "/tmp/coq16819Y8T" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
Import ApplicativeNotation FunctorNotation ListNotations MonadNotation SumNotations.
Open Scope sum_scope.
Open Scope monad_scope.
Module App.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Arguments serverAppE : clear implicits.
Definition smE := serverAppE exp +' evalE.
Definition kvs_state exp_ := list (N * exp_ N).
Definition kvs : itree smE void :=
  rec
    (fun st : kvs_state exp =>
     req <- trigger ServerApp_Recv;;
     match req with
     | Kvs_GET k =>
         match kvs_get k st with
         | Some v => embed ServerApp_Send (Kvs_OK v);; call st
         | None => v <- trigger (@ServerApp_Fresh exp);; embed ServerApp_Send (Kvs_OK v);; call (kvs_put k v st)
         end
     | Kvs_PUT k v => embed ServerApp_Send Kvs_NoContent;; call (kvs_put k (exp_int v) st)
     | Kvs_CAS k x v' =>
         match kvs_get k st with
         | Some v =>
             b <- trigger (Eval (exp_eq x v));;
             (if b : bool
              then embed ServerApp_Send Kvs_NoContent;; call (kvs_put k (exp_int v') st)
              else embed ServerApp_Send Kvs_PreconditionFailed;; call st)
         | None =>
             v <- trigger (@ServerApp_Fresh exp);;
             b <- trigger (Eval (exp_eq x v));;
             (if b : bool
              then embed ServerApp_Send Kvs_NoContent;; call (kvs_put k (exp_int v') st)
              else embed ServerApp_Send Kvs_PreconditionFailed;; call (kvs_put k v st))
         end
     | _ => embed ServerApp_Send Kvs_BadRequest;; call st
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
Definition embed_exp {T} {E} `{serverAppE id -< E} (ex : serverAppE exp T) : itree E T :=
  match ex in (serverAppE _ T) return (itree E T) with
  | ServerApp_Recv => trigger ServerApp_Recv
  | ServerApp_Send rx => trigger (ServerApp_Send (unwrap_data rx))
  | ServerApp_Fresh => i <- trigger ServerApp_Fresh;; Ret (exp_int (i : id N))
  end.
Definition nmi_of_smi {T} (m : itree smE T) : itree (serverAppE id) T :=
  interp
    (fun T e =>
     match e with
     | (se|) => embed_exp se
     | (|ee) => match ee in (evalE T) return (_ T) with
                | Eval bx => ret (unwrap bx)
                end
     end) m.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Instance showTesterAppE  {X}: (Show (testerAppE X)) :=
 {| show := fun e => match e with
                     | TesterApp_Recv => "recv"
                     | TesterApp_Send => "send"
                     end |}.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition unifier_of_smi : itree smE void -> itree (testerAppE +' unifyE) unit :=
  rec-fix unifier_of_smi_rec m
  := match (m : itree smE void).(observe) with
     | RetF vd => match vd in void with
                  end
     | TauF m' => unifier_of_smi_rec m'
     | VisF (sae|) k =>
         match sae in (serverAppE _ Y) return ((Y -> _) -> _) with
         | ServerApp_Recv => bind (embed TesterApp_Send) \226\136\152 compose unifier_of_smi_rec
         | ServerApp_Send rx =>
             fun k => r <- embed TesterApp_Recv;; trigger (Unify_Guard rx r);; unifier_of_smi_rec (k tt)
         | ServerApp_Fresh => bind (trigger Unify_New) \226\136\152 compose unifier_of_smi_rec
         end k
     | VisF (|ee) k =>
         match ee in (evalE Y) return ((Y -> _) -> _) with
         | Eval bx => bind (embed Unify_Decide bx) \226\136\152 compose unifier_of_smi_rec
         end k
     end.
Variant err :=
  | Err_Guard : forall (rx : kvs_data exp) (r : kvs_data id), _
  | Err_Decide : forall (bx : exp bool) (b : bool), _
  | Err_Mismatch : forall {X} {Y} (e0 : testerAppE X) (te : testerAppE Y), _.
Instance showErr : (Show err) :=
 {|
 show := fun e =>
         match e with
         | Err_Guard rx r => "Guard error: " ++ show rx ++ " <> " ++ show r
         | Err_Decide bx b => "Decide error: " ++ show bx ++ " <> " ++ show b
         | Err_Mismatch e0 te => "Events mismatch: " ++ show e0 ++ " <> " ++ show te
         end |}.
Notation taE := (exceptE err +' nondetE +' testerAppE).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition liftState {s a : Type} {m : Type -> Type} `{Functor m} : m a -> stateT s m a :=
  @mkStateT s m a \226\136\152 flip compose (flip pair) \226\136\152 flip fmap.
Definition tester_of_unifier (u : itree (testerAppE +' unifyE) unit) : stateT state (itree taE) unit :=
  interp
    (fun X e =>
     match e with
     | (te|) => @liftState state X (itree taE) _ (trigger (te|))
     | (|ue) => handle_unifier ue
     end) u.
CoFixpoint match_event {X} (e0 : testerAppE X) (x0 : X) (t : itree taE unit) : itree taE unit :=
  match t.(observe) with
  | RetF r => Ret r
  | TauF t => Tau (match_event e0 x0 t)
  | VisF e k =>
      match e with
      | (||te) =>
          match e0 in (testerAppE X), te in (testerAppE Y) return ((Y -> _) -> X -> _) with
          | TesterApp_Recv, TesterApp_Recv | TesterApp_Send, TesterApp_Send => id
          | _, _ => fun _ _ => throw (Err_Mismatch e0 te)
          end k x0
      | (e|) | (|(e|)) => vis e (match_event e0 x0 \226\136\152 k)
      end
  end.
Definition match_event_list {X} (e0 : testerAppE X) (x : X) : list (itree taE unit) -> list (itree taE unit) :=
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
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Import App.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Derive Show for error.
Notation hsE := (exceptE error +' hsgenE +' networkE).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
CoFixpoint network_server {T} (m : itree (serverAppE id) T) (sk : shared_key) : itree (appgenE +' networkE) T :=
  match m.(observe) with
  | RetF r => Ret r
  | TauF m => Tau (network_server m sk)
  | VisF e k =>
      match e in (serverAppE _ Y) return ((Y -> _) -> _) with
      | ServerApp_Recv =>
          fun k =>
          r <-
          loop
            (fun _ =>
             reqCipher <- trigger Network_Recv;;
             match reqCipher with
             | Message_Cipher reqCipher =>
                 match decipher sk reqCipher with
                 | Some (PlainMessage_AppData reqKvs) => ret (inr reqKvs)
                 | Some _ =>
                     embed Network_Send (Message_Cipher (cipher sk PlainMessage_BadRequest));; ret (inl tt)
                 | None => ret (inl tt)
                 end
             | Message_Plain _ =>
                 embed Network_Send (Message_Cipher (cipher sk PlainMessage_BadRequest));; ret (inl tt)
             end) tt;; Tau (network_server (k r) sk)
      | ServerApp_Send r =>
          fun k =>
          embed Network_Send (Message_Cipher (cipher sk (PlainMessage_AppData r)));;
          Tau (network_server (k tt) sk)
      | ServerApp_Fresh => fun k => n <- trigger AppGen_N;; Tau (network_server (k (n : N)) sk)
      end k
  end.
CoFixpoint network_tester {T} (m : itree taE T) (sk : shared_key) :
itree (exceptE error +' nondetE +' appgenE +' networkE) T :=
  match m.(observe) with
  | RetF r => Ret r
  | TauF m => Tau (network_tester m sk)
  | VisF e k =>
      match e with
      | (Throw e|) => throw (Error_App e)
      | (|(ne|)) =>
          match ne in (nondetE Y) return ((Y -> _) -> _) with
          | Or => fun k => b <- trigger Or;; Tau (network_tester (k b) sk)
          end k
      | (||te) =>
          match te in (testerAppE Y) return ((Y -> _) -> _) with
          | TesterApp_Recv =>
              fun k =>
              r <-
              loop
                (fun _ =>
                 reqCipher <- trigger Network_Recv;;
                 match reqCipher with
                 | Message_Cipher reqCipher =>
                     match decipher sk reqCipher with
                     | Some (PlainMessage_AppData reqKvs) => ret (inr reqKvs)
                     | Some _ =>
                         embed Network_Send (Message_Cipher (cipher sk PlainMessage_BadRequest));; ret (inl tt)
                     | None => ret (inl tt)
                     end
                 | Message_Plain _ =>
                     embed Network_Send (Message_Cipher (cipher sk PlainMessage_BadRequest));; ret (inl tt)
                 end) tt;; Tau (network_tester (k r) sk)
          | TesterApp_Send =>
              fun k =>
              r <- trigger AppGen_Request;;
              embed Network_Send (Message_Cipher (cipher sk (PlainMessage_AppData r)));;
              Tau (network_tester (k r) sk)
          end k
      end
  end.
Notation sE := (exceptE error +' hsgenE +' appgenE +' networkE).
Notation tE := (nondetE +' sE).
Definition server : itree sE void :=
  sk <- translate subevent serverHandshake;; translate subevent (network_server (nmi_of_smi kvs) sk).
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Anomaly ""Assert_failure printing/ppconstr.ml:399:14"." Please report at http://coq.inria.fr/bugs/.
Definition showSE (se : sigT (fun X => sE X * X)%type) : string :=
  match se with
  | existT _ _ er =>
      let (e, r) := er in
      match e with
      | (Throw _|) => "This message should never be printed."
      | (|(hge|)) =>
          match hge in (hsgenE X) return (X -> _) with
          | HsGen_Key => fun k => "Handshake   Generate Key    : " ++ show k
          | HsGen_Random => fun r => "Handshake   Generate Random : " ++ show r
          end r
      | (||age|) =>
          match age in (appgenE X) return (X -> _) with
          | AppGen_N => fun n => "Application Generate Value  : " ++ show n
          | AppGen_Requst => fun r => "Application Generate Request: " ++ show r
          end r
      | (|||ne) =>
          match ne in (networkE X) return (X -> _) with
          | Network_Recv => fun m => "Network     Recv to   server: " ++ show m
          | Network_Send m => fun _ => "Network     Send from server: " ++ show m
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
Notation zE := (exceptE error +' traceE +' hsgenE +' appgenE +' nondetE).
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
      | (|(Throw e|)) => retry e
      | (||hge|) =>
          match hge in (hsgenE Y) return ((Y -> _) -> _) with
          | HsGen_Key =>
              fun tk =>
              k <- trigger HsGen_Key;;
              embed Trace (Event_Tester (existT _ _ ((||HsGen_Key|), k)));; Tau (zip' others (tk k) server)
          | HsGen_Random =>
              fun tk =>
              r <- trigger HsGen_Random;;
              embed Trace (Event_Tester (existT _ _ ((||HsGen_Random|), r)));; Tau (zip' others (tk r) server)
          end tk
      | (|||age|) =>
          match age in (appgenE Y) return ((Y -> _) -> _) with
          | AppGen_N =>
              fun tk =>
              n <- trigger AppGen_N;;
              embed Trace (Event_Tester (existT _ _ ((|||AppGen_N|), n)));; Tau (zip' others (tk n) server)
          | AppGen_Request =>
              fun tk =>
              r <- trigger AppGen_Request;;
              embed Trace (Event_Tester (existT _ _ ((|||AppGen_Request|), r)));; Tau (zip' others (tk r) server)
          end tk
      | (||||te) =>
          match server.(observe) with
          | RetF vd => match vd in void with
                       end
          | TauF s' => Tau (zip' others client s')
          | VisF se sk =>
              match se with
              | (ee|) => retry Error_UnexpectedBehavior
              | (|(hge|)) =>
                  match hge in (hsgenE Y) return ((Y -> _) -> _) with
                  | HsGen_Key =>
                      fun sk =>
                      k <- trigger HsGen_Key;;
                      embed Trace (Event_Server (existT _ _ ((|(HsGen_Key|)), k)));;
                      Tau (zip' others client (sk k))
                  | HsGen_Random =>
                      fun sk =>
                      r <- trigger HsGen_Random;;
                      embed Trace (Event_Server (existT _ _ ((|(HsGen_Random|)), r)));;
                      Tau (zip' others client (sk r))
                  end sk
              | (||age|) =>
                  match age in (appgenE Y) return ((Y -> _) -> _) with
                  | AppGen_N =>
                      fun sk =>
                      n <- trigger AppGen_N;;
                      embed Trace (Event_Server (existT _ _ ((||AppGen_N|), n)));; Tau (zip' others client (sk n))
                  | AppGen_Request =>
                      fun sk =>
                      r <- trigger AppGen_Request;;
                      embed Trace (Event_Server (existT _ _ ((||AppGen_Request|), r)));;
                      Tau (zip' others client (sk r))
                  end sk
              | (|||se) =>
                  match se in (networkE Z) return ((Z -> _) -> _) with
                  | Network_Recv =>
                      fun sk =>
                      match te in (networkE Y) return ((Y -> _) -> _) with
                      | Network_Recv => fun _ => retry Error_UnexpectedBehavior
                      | Network_Send msg =>
                          fun tk =>
                          embed Trace (Event_Server (existT _ _ ((|||Network_Recv), msg)));;
                          Tau (zip' others (tk tt) (sk msg))
                      end tk
                  | Network_Send msg =>
                      fun sk =>
                      match te in (networkE Y) return ((Y -> _) -> _) with
                      | Network_Recv =>
                          fun tk =>
                          embed Trace (Event_Server (existT _ _ ((|||Network_Send msg), tt)));;
                          Tau (zip' others (tk msg) (sk tt))
                      | Network_Send _ => fun _ => retry Error_UnexpectedBehavior
                      end tk
                  end sk
              end
          end
      end
  end.
Definition _zip (_ : unit) : itree tE unit -> itree sE void -> itree zE unit := zip' [].
Notation zip := (_zip tt).
End Network.
Module Test.
Import Network.
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
                | (|(age|)) =>
                    match age in (appgenE Y) return ((Y -> _) -> _) with
                    | AppGen_N => fun k => k n
                    | AppGen_Request => fun k => k r
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
Redirect "/tmp/coq16819yQg" Print Ltac Signatures.
Timeout 1 Print Grammar tactic.
Timeout 1 Print LoadPath.
