(* This file has been generated by extraction
   of bootstrap/Monad.v. It shouldn't be
   modified directly. To regenerate it run
   coqtop -batch -impredicative-set -l
   bootstrap/Monad.v in Coq's source
   directory. *)

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module IOBase = 
 struct 
  type 'a coq_T = unit -> 'a
  
  type 'a coq_Ref = 'a Pervasives.ref
  
  (** val ret : 'a1 -> 'a1 coq_T **)
  
  let ret = fun a -> (); fun () -> a
  
  (** val bind :
      'a1 coq_T -> ('a1 -> 'a2 coq_T) -> 'a2
      coq_T **)
  
  let bind = fun a k -> (); fun () -> k (a ()) ()
  
  (** val ignore :
      'a1 coq_T -> unit coq_T **)
  
  let ignore = fun a -> (); fun () -> ignore (a ())
  
  (** val seq :
      unit coq_T -> 'a1 coq_T -> 'a1 coq_T **)
  
  let seq = fun a k -> (); fun () -> a (); k ()
  
  (** val ref : 'a1 -> 'a1 coq_Ref coq_T **)
  
  let ref = fun a -> (); fun () -> Pervasives.ref a
  
  (** val set :
      'a1 coq_Ref -> 'a1 -> unit coq_T **)
  
  let set = fun r a -> (); fun () -> Pervasives.(:=) r a
  
  (** val get : 'a1 coq_Ref -> 'a1 coq_T **)
  
  let get = fun r -> (); fun () -> Pervasives.(!) r
  
  (** val raise : exn -> 'a1 coq_T **)
  
  let raise = fun e -> (); fun () -> raise (Proof_errors.Exception e)
  
  (** val catch :
      'a1 coq_T -> (exn -> 'a1 coq_T) -> 'a1
      coq_T **)
  
  let catch = fun s h -> (); fun () -> try s () with Proof_errors.Exception e -> h e ()
  
  (** val read_line : string coq_T **)
  
  let read_line = fun () -> try Pervasives.read_line () with e -> raise e ()
  
  (** val print_char : char -> unit coq_T **)
  
  let print_char = fun c -> (); fun () -> print_char c
  
  (** val print :
      Pp.std_ppcmds -> unit coq_T **)
  
  let print = fun s -> (); fun () -> try Pp.pp s; Pp.pp_flush () with e -> raise e ()
  
  (** val timeout :
      int -> 'a1 coq_T -> 'a1 coq_T **)
  
  let timeout = fun n t -> (); fun () ->
    let timeout_handler _ = Pervasives.raise (Proof_errors.Exception Proof_errors.Timeout) in
    let psh = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
    Pervasives.ignore (Unix.alarm n);
    let restore_timeout () =
      Pervasives.ignore (Unix.alarm 0);
      Sys.set_signal Sys.sigalrm psh
    in
    try
      let res = t () in
      restore_timeout ();
      res
    with
    | e -> restore_timeout (); Pervasives.raise e
 
 end

type proofview = { initial : (Term.constr*Term.types)
                             list;
                   solution : Evd.evar_map;
                   comb : Goal.goal list }

type logicalState = proofview

type logicalMessageType = bool

type logicalEnvironment = Environ.env

module NonLogical = 
 struct 
  type 'a t = 'a IOBase.coq_T
  
  type 'a ref = 'a IOBase.coq_Ref
  
  (** val ret : 'a1 -> 'a1 t **)
  
  let ret x =
    IOBase.ret x
  
  (** val bind :
      'a1 t -> ('a1 -> 'a2 t) -> 'a2 t **)
  
  let bind x k =
    IOBase.bind x k
  
  (** val ignore : 'a1 t -> unit t **)
  
  let ignore x =
    IOBase.ignore x
  
  (** val seq : unit t -> 'a1 t -> 'a1 t **)
  
  let seq x k =
    IOBase.seq x k
  
  (** val new_ref : 'a1 -> 'a1 ref t **)
  
  let new_ref x =
    IOBase.ref x
  
  (** val set : 'a1 ref -> 'a1 -> unit t **)
  
  let set r x =
    IOBase.set r x
  
  (** val get : 'a1 ref -> 'a1 t **)
  
  let get r =
    IOBase.get r
  
  (** val raise : exn -> 'a1 t **)
  
  let raise e =
    IOBase.raise e
  
  (** val catch :
      'a1 t -> (exn -> 'a1 t) -> 'a1 t **)
  
  let catch s h =
    IOBase.catch s h
  
  (** val timeout : int -> 'a1 t -> 'a1 t **)
  
  let timeout n x =
    IOBase.timeout n x
  
  (** val read_line : string t **)
  
  let read_line =
    IOBase.read_line
  
  (** val print_char : char -> unit t **)
  
  let print_char c =
    IOBase.print_char c
  
  (** val print : Pp.std_ppcmds -> unit t **)
  
  let print s =
    IOBase.print s
  
  (** val run : 'a1 t -> 'a1 **)
  
  let run = fun x -> try x () with Proof_errors.Exception e -> Pervasives.raise e
 end

module Logical = 
 struct 
  type 'a t =
    __ -> ('a -> proofview -> Environ.env ->
    __ -> ((__*bool) -> (exn -> __
    IOBase.coq_T) -> __ IOBase.coq_T) -> (exn
    -> __ IOBase.coq_T) -> __ IOBase.coq_T)
    -> proofview -> Environ.env -> __ ->
    ((__*bool) -> (exn -> __ IOBase.coq_T) ->
    __ IOBase.coq_T) -> (exn -> __
    IOBase.coq_T) -> __ IOBase.coq_T
  
  (** val ret :
      'a1 -> __ -> ('a1 -> proofview ->
      Environ.env -> __ -> (('a2*bool) ->
      (exn -> __ IOBase.coq_T) -> __
      IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> 'a3
      IOBase.coq_T) -> 'a3 IOBase.coq_T) ->
      (exn -> 'a3 IOBase.coq_T) -> 'a3
      IOBase.coq_T **)
  
  let ret x =
    (); (fun _ k s -> Obj.magic k x s)
  
  (** val bind :
      'a1 t -> ('a1 -> 'a2 t) -> __ -> ('a2
      -> proofview -> Environ.env -> __ ->
      (('a3*bool) -> (exn -> __ IOBase.coq_T)
      -> __ IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a3*bool) -> (exn -> 'a4
      IOBase.coq_T) -> 'a4 IOBase.coq_T) ->
      (exn -> 'a4 IOBase.coq_T) -> 'a4
      IOBase.coq_T **)
  
  let bind x k =
    (); (fun _ k0 s ->
      Obj.magic x __ (fun a s' ->
        Obj.magic k a __ k0 s') s)
  
  (** val ignore :
      'a1 t -> __ -> (unit -> proofview ->
      Environ.env -> __ -> (('a2*bool) ->
      (exn -> __ IOBase.coq_T) -> __
      IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> 'a3
      IOBase.coq_T) -> 'a3 IOBase.coq_T) ->
      (exn -> 'a3 IOBase.coq_T) -> 'a3
      IOBase.coq_T **)
  
  let ignore x =
    (); (fun _ k s ->
      Obj.magic x __ (fun x1 s' -> k () s') s)
  
  (** val seq :
      unit t -> 'a1 t -> __ -> ('a1 ->
      proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> __ IOBase.coq_T)
      -> __ IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> 'a3
      IOBase.coq_T) -> 'a3 IOBase.coq_T) ->
      (exn -> 'a3 IOBase.coq_T) -> 'a3
      IOBase.coq_T **)
  
  let seq x k =
    (); (fun _ k0 s ->
      Obj.magic x __ (fun x1 s' ->
        Obj.magic k __ k0 s') s)
  
  (** val set :
      logicalState -> __ -> (unit ->
      proofview -> Environ.env -> __ ->
      (('a1*bool) -> (exn -> __ IOBase.coq_T)
      -> __ IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a1*bool) -> (exn -> 'a2
      IOBase.coq_T) -> 'a2 IOBase.coq_T) ->
      (exn -> 'a2 IOBase.coq_T) -> 'a2
      IOBase.coq_T **)
  
  let set s =
    (); (fun _ k x -> Obj.magic k () s)
  
  (** val get :
      __ -> (logicalState -> proofview ->
      Environ.env -> __ -> (('a1*bool) ->
      (exn -> __ IOBase.coq_T) -> __
      IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a1*bool) -> (exn -> 'a2
      IOBase.coq_T) -> 'a2 IOBase.coq_T) ->
      (exn -> 'a2 IOBase.coq_T) -> 'a2
      IOBase.coq_T **)
  
  let get r k s =
    Obj.magic k s s
  
  (** val put :
      logicalMessageType -> __ -> (unit ->
      proofview -> Environ.env -> __ ->
      (('a1*bool) -> (exn -> __ IOBase.coq_T)
      -> __ IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a1*bool) -> (exn -> 'a2
      IOBase.coq_T) -> 'a2 IOBase.coq_T) ->
      (exn -> 'a2 IOBase.coq_T) -> 'a2
      IOBase.coq_T **)
  
  let put m =
    (); (fun _ k s e _ sk fk ->
      Obj.magic k () s e __ (fun a fk0 ->
        let y,c' = a in
        sk (y,(if m then c' else false)) fk0)
        fk)
  
  (** val current :
      __ -> (logicalEnvironment -> proofview
      -> Environ.env -> __ -> (('a1*bool) ->
      (exn -> __ IOBase.coq_T) -> __
      IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a1*bool) -> (exn -> 'a2
      IOBase.coq_T) -> 'a2 IOBase.coq_T) ->
      (exn -> 'a2 IOBase.coq_T) -> 'a2
      IOBase.coq_T **)
  
  let current r k s e r0 sk fk =
    Obj.magic k e s e __ (fun a fk0 ->
      let y,c' = a in sk (y,c') fk0) fk
  
  (** val zero :
      exn -> __ -> ('a1 -> proofview ->
      Environ.env -> __ -> (('a2*bool) ->
      (exn -> __ IOBase.coq_T) -> __
      IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> 'a3
      IOBase.coq_T) -> 'a3 IOBase.coq_T) ->
      (exn -> 'a3 IOBase.coq_T) -> 'a3
      IOBase.coq_T **)
  
  let zero e =
    (); (fun _ k s e0 _ sk fk -> fk e)
  
  (** val plus :
      'a1 t -> (exn -> 'a1 t) -> __ -> ('a1
      -> proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> __ IOBase.coq_T)
      -> __ IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> 'a3
      IOBase.coq_T) -> 'a3 IOBase.coq_T) ->
      (exn -> 'a3 IOBase.coq_T) -> 'a3
      IOBase.coq_T **)
  
  let plus x y =
    (); (fun _ k s env _ sk fk ->
      Obj.magic x __ k s env __ sk (fun e ->
        Obj.magic y e __ k s env __ sk fk))
  
  (** val split :
      'a1 t -> __ -> (('a1*(exn -> 'a1 t),
      exn) Util.union -> proofview ->
      Environ.env -> __ -> (('a2*bool) ->
      (exn -> __ IOBase.coq_T) -> __
      IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> 'a3
      IOBase.coq_T) -> 'a3 IOBase.coq_T) ->
      (exn -> 'a3 IOBase.coq_T) -> 'a3
      IOBase.coq_T **)
  
  let split x =
    (); (fun _ k s e _ sk fk ->
      IOBase.bind
        (Obj.magic x __
          (fun a s' e0 _ sk0 fk0 ->
          sk0 ((a,s'),true) fk0) s e __
          (fun a fk0 ->
          IOBase.ret (Util.Inl
            (a,(fun e0 _ sk0 fk1 ->
            IOBase.bind (fk0 e0) (fun x0 ->
              match x0 with
              | Util.Inl p ->
                let a0,x1 = p in
                sk0 a0 (fun e1 ->
                  x1 e1 __ sk0 fk1)
              | Util.Inr e1 -> fk1 e1)))))
          (fun e0 ->
          IOBase.ret (Util.Inr e0)))
        (fun x0 ->
        match x0 with
        | Util.Inl p ->
          let p0,y = p in
          let p1,m' = p0 in
          let a',s' = p1 in
          Obj.magic k (Util.Inl
            (a',(fun exc _ k0 s0 e0 _ sk0 fk0 ->
            y exc __ (fun a fk1 ->
              let x1,c = a in
              let a0,s'0 = x1 in
              k0 a0 s'0 e0 __ (fun a1 fk2 ->
                let y0,c' = a1 in
                sk0
                  (y0,(if c
                       then c'
                       else false)) fk2) fk1)
              fk0))) s' e __ (fun a fk0 ->
            let y0,c' = a in
            sk
              (y0,(if m' then c' else false))
              fk0) fk
        | Util.Inr exc ->
          Obj.magic k (Util.Inr exc) s e __
            (fun a fk0 ->
            let y,c' = a in sk (y,c') fk0) fk))
  
  (** val lift :
      'a1 NonLogical.t -> __ -> ('a1 ->
      proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> __ IOBase.coq_T)
      -> __ IOBase.coq_T) -> (exn -> __
      IOBase.coq_T) -> __ IOBase.coq_T) ->
      proofview -> Environ.env -> __ ->
      (('a2*bool) -> (exn -> 'a3
      IOBase.coq_T) -> 'a3 IOBase.coq_T) ->
      (exn -> 'a3 IOBase.coq_T) -> 'a3
      IOBase.coq_T **)
  
  let lift x =
    (); (fun _ k s e _ sk fk ->
      IOBase.bind x (fun x0 ->
        Obj.magic k x0 s e __ (fun a fk0 ->
          let y,c' = a in sk (y,c') fk0) fk))
  
  (** val run :
      'a1 t -> logicalEnvironment ->
      logicalState ->
      (('a1*logicalState)*logicalMessageType)
      NonLogical.t **)
  
  let run x e s =
    Obj.magic x __ (fun a s' e0 _ sk fk ->
      sk ((a,s'),true) fk) s e __
      (fun a x0 -> IOBase.ret a) (fun e0 ->
      IOBase.raise
        ((fun e -> Proof_errors.TacticFailure e)
          e0))
 end

