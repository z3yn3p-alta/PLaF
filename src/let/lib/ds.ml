(* This file defines expressed values and environments *)

(* expressed values and environments are defined mutually recursively *)

type 'a tree = Empty | Node of 'a * 'a tree * 'a tree

type exp_val =
  | NumVal of int
  | BoolVal of bool
  | PairVal of exp_val * exp_val
  | TupleVal of exp_val list
  | TreeVal of exp_val tree
  | RecordVal of ( string * exp_val) list
  | Proj of string
  | ProcVal of string*exp_val*env
and
  env =
  | EmptyEnv
  | ExtendEnv of string*exp_val*env


(*
type expr =
  | Var of string
  | Int of int
  | Add of expr * expr
  | Mul of expr * expr
  | Div of expr * expr
  | Sub of expr * expr
  | Let of string * expr * expr
  | IsZero of expr
  | ITE of expr * expr * expr
  | EmptyTree of expr option
  | Node of expr * expr * expr
  | CaseT of expr * expr * string * string * string * expr
  | IsEmpty of expr
  | Record of (string * (bool * expr)) list
  | Proj of expr * string
*)
(* Environment Abstracted Result *)

type 'a result = Ok of 'a | Error of string

type 'a ea_result = env -> 'a result
  
let return : 'a -> 'a ea_result =
  fun v ->
  fun _env ->
  Ok v

let error : string -> 'a ea_result = fun s ->
  fun _env -> 
  Error s

let (>>=) : 'a ea_result -> ('a -> 'b ea_result) -> 'b ea_result = fun c f ->
  fun env ->
  match c env with
  | Error err -> Error err
  | Ok v -> f v env

let (>>+) : env ea_result -> 'a ea_result -> 'a ea_result =
  fun c d ->
  fun env ->
  match c env with
  | Error err -> Error err
  | Ok newenv -> d newenv

let run : 'a ea_result -> 'a result =
  fun c ->
  c EmptyEnv

let lookup : env ea_result = fun env ->
  Ok env

let rec sequence : 'a ea_result list -> 'a list ea_result =
  fun l ->
  match l with
  | [] -> return []
  | h::t ->
    h >>= fun ev ->
    sequence t >>= fun evs ->
    return (ev::evs)
    

(* Operations on environments *)

let empty_env : unit -> env ea_result = fun () ->
  return EmptyEnv

let extend_env : string -> exp_val -> env ea_result = fun id v env ->
  Ok (ExtendEnv(id,v,env))

let rec extend_env_list_helper =
  fun ids evs en ->
  match ids,evs with
  | [],[] -> en
  | id::idt,ev::evt ->
    ExtendEnv(id,ev,extend_env_list_helper idt evt en)
  | _,_ -> failwith
             "extend_env_list_helper: ids and evs have different sizes"
  
let extend_env_list =
  fun ids evs ->
  fun en ->
  Ok (extend_env_list_helper ids evs en)
    
let rec apply_env : string -> exp_val ea_result = fun id env ->
  match env with
  | EmptyEnv -> Error (id^" not found!")
  | ExtendEnv(v,ev,tail) ->
    if id=v
    then Ok ev
    else apply_env id tail



(* operations on expressed values *)

let int_of_numVal : exp_val -> int ea_result =  function
  |  NumVal n -> return n
  | _ -> error "Expected a number!"

let bool_of_boolVal : exp_val -> bool ea_result =  function
  |  BoolVal b -> return b
  | _ -> error "Expected a boolean!"

let list_of_tupleVal : exp_val -> (exp_val list)  ea_result =  function
  |  TupleVal l -> return l
  | _ -> error "Expected a tuple!"
           
let pair_of_pairVal : exp_val -> (exp_val*exp_val) ea_result =  function
  |  PairVal(ev1,ev2) -> return (ev1,ev2)
  | _ -> error "Expected a pair!"
        
let clos_of_procVal : exp_val -> (string*exp_val*env) ea_result =
    fun ev -> 
    match ev with
    | ProcVal(id,body,en) -> return (id,body,en)
    | _ -> error "Expected a closure!"

let rec string_of_expval = function
  | NumVal n -> "NumVal " ^ string_of_int n
  | BoolVal b -> "BoolVal " ^ string_of_bool b
  | PairVal (ev1,ev2) -> "PairVal("^string_of_expval ev1
                         ^","^ string_of_expval ev2^")"
  | TupleVal evs -> "TupleVal("^String.concat "," (List.map string_of_expval evs)^")"
  | TreeVal t -> (
    let rec string_of_treeVal = function
      | Node (v, left, right) ->
        "Node(" ^ string_of_expval v ^ ", " ^ string_of_treeVal left ^ ", " ^ string_of_treeVal right ^ ")"
      | Empty -> "Empty"
    in 
    string_of_treeVal t
  )
  | ProcVal (id,body,env) -> "ProcVal ("^ id ^","^string_of_expval
  body^","^ string_of_env' []
                env^")"
and
  string_of_env' ac = function
  | EmptyEnv ->  "["^String.concat ",\n" ac^"]"
  | ExtendEnv(id,v,env) -> string_of_env' ((id^":="^string_of_expval v)::ac) env

let string_of_env : string ea_result =
  fun env ->
  match env with
  | EmptyEnv -> Ok ">>Environment:\nEmpty"
  | _ -> Ok (">>Environment:\n"^ string_of_env' [] env)

