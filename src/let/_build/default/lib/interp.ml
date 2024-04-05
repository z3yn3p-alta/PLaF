(* Isabella Ganguzza and Zeynep Alta
   I pledge my honor that I have abided by the Stevens Honor System.*)

   open Parser_plaf.Ast
   open Parser_plaf.Parser
   open Ds
   
   (* 
   type expr =
     | Var of string
     | Int of int
     | Sub of expr * expr
     | Let of string * expr * expr
     | IsZero of expr
     | ITE of expr * expr * expr
     | EmptyTree
     | Node of expr * expr * expr
     | IsEmpty of expr
     | CaseT of expr * expr * string * string * string * expr
     | Record of ( string *( bool * expr )) list
     | Proj of expr * string
     | Record of ( string *( bool * expr )) list
     | Proj of expr * string
     *)
   (*
     <Expression> ::= emptytree()
     <Expression> ::= node(<Expression>, <Expression>, <Expression>)
     <Expression> ::= empty?(<Expression>)
     <Expression> ::= caseT <Expression> of { emptytree() -> <Expression> , node(<Id>,<Id>,<Id>) -> <Expression> }
     *)
   
   (** [eval_expr e] evaluates expression [e] *)
   let rec eval_expr : expr -> exp_val ea_result =
     fun e ->
     match e with
     | Int(n) ->
       return (NumVal n)
     | Var(id) ->
       apply_env id
     | Add(e1,e2) ->
       eval_expr e1 >>=
       int_of_numVal >>= fun n1 ->
       eval_expr e2 >>=
       int_of_numVal >>= fun n2 ->
       return (NumVal (n1+n2))
     | Sub(e1,e2) ->
       eval_expr e1 >>=
       int_of_numVal >>= fun n1 ->
       eval_expr e2 >>=
       int_of_numVal >>= fun n2 ->
       return (NumVal (n1-n2))
     | Mul(e1,e2) ->
       eval_expr e1 >>=
       int_of_numVal >>= fun n1 ->
       eval_expr e2 >>=
       int_of_numVal >>= fun n2 ->
       return (NumVal (n1*n2))
     | Div(e1,e2) ->
       eval_expr e1 >>=
       int_of_numVal >>= fun n1 ->
       eval_expr e2 >>=
       int_of_numVal >>= fun n2 ->
       if n2==0
       then error "Division by zero"
       else return (NumVal (n1/n2))
     | Let(id,def,body) ->
       eval_expr def >>= 
       extend_env id >>+
       eval_expr body 
     | ITE(e1,e2,e3) ->
       eval_expr e1 >>=
       bool_of_boolVal >>= fun b ->
       if b 
       then eval_expr e2
       else eval_expr e3
     | IsZero(e) ->
       eval_expr e >>=
       int_of_numVal >>= fun n ->
       return (BoolVal (n = 0))
     | Pair(e1,e2) ->
       eval_expr e1 >>= fun ev1 ->
       eval_expr e2 >>= fun ev2 ->
       return (PairVal(ev1,ev2))
     | Fst(e) ->
       eval_expr e >>=
       pair_of_pairVal >>= fun (l,_) ->
       return l
     | Snd(e) ->
       eval_expr e >>=
       pair_of_pairVal >>= fun (_,r) ->
       return r
     | Debug(_e) ->
       string_of_env >>= fun str ->
       print_endline str; 
       error "Debug called"
   
   (* BELLA'S PART *)
     | EmptyTree (_t)->
       return (TreeVal Empty)
   
     | Node (e1, e2, e3) ->
       (* Evaluates e1, e2, e3, >>= is bind operator for ea_result, takes the result of eval_expr e1 and passes it to the function 
       provided on its right side (v1, v2, v3) *)
       eval_expr e1 >>= fun v1 ->
       eval_expr e2 >>= fun v2 ->
       eval_expr e3 >>= fun v3 ->
       (match v2, v3 with
       | TreeVal t2, TreeVal t3 ->
         return (TreeVal (Node (v1, t2, t3)))
       | _ -> error "The second or third argument is not a tree")
       (*e1 evaluates to a number (NumVal n), e2 evaluates to a tree (TreeVal t1), e3 evaluates to a tree (TreeVal t2). If pattern matches, 
       there are valid arguments to create a node in a binary tree. Return a tree value constructed using Node with the number n as the data 
       value and t1 & t2 as left & right subtrees*)
   
   
     (*e represents binary tree*) 
     
   
     | IsEmpty (e) ->
       eval_expr e >>= 
       tree_of_treeVal >>= fun ev ->
       return (BoolVal(ev = Empty))
       
     (*e1 is expression to be evaluated, e2 is expression to evaluate in the case of an empty tree, and e3 is expression to evaluate in the case of 
     a non-empty tree. id1, id2, and id3 are identifiers used to match fields of node in the case of a non-empty tree*)
     
   
     | CaseT (e1, e2, id1, id2, id3, e3) ->
         eval_expr e1 >>= tree_of_treeVal >>= fun f -> 
         (match f with
         (* If e1 is a TreeVal containing an empty tree, evaluate e2*)
         | Empty -> eval_expr e2 
         | (Node (v, left, right)) ->
           (*Extends the environment id1 with value v*)
           extend_env id1 v >>+
           extend_env id2 (TreeVal left) >>+
           extend_env id3 (TreeVal right) >>+
           eval_expr e3
         | _ -> error "e1 does not evaluate to binary tree.")
           (*Extends the environment id2 with value TreeVal left. Since left represents a subtree, wrap it with TreeVal to ensure it's 
           recognized as a tree value in the environment. Same for id3*)
       
   (* ZEY'S PART *)
     (* {fname1=e1; ...; fnamen=en} creates a record with n fields. 
        Field i is assigned the expressed value resulting from 
        evaluating expression ei. Reports an error if there are
        duplicate fields.
        *)
       
     | Record(fs) -> 
       let rec eval_record_fields fields acc =
         (match fields with
         | [] -> return (List.rev acc)
         | (id, (false, expr)) :: rest ->
             if List.exists (fun (id', _) -> id' = id) acc then
               error "Record: duplicate field"
             else
               eval_expr expr >>= fun value ->
               eval_record_fields rest ((id, value) :: acc))
       in
       eval_record_fields fs [] >>= fun evaluated_fields ->
       return (RecordVal evaluated_fields)
   
     (* e.id projects field id from the record resulting from evaluating e. 
        Reports an error if e does not evaluate to a record or does not 
        have a field named id.
        *)
     | Proj (e , id ) -> 
       eval_expr e >>= function
       | RecordVal fields ->
           (try
             let value = List.assoc id fields in
             return value
           with Not_found -> error "Proj: field does not exist")
       | _ -> error "Expected a record"
     | _ -> error "Not valid input."
   and
     eval_exprs : expr list -> ( exp_val list ) ea_result =
     fun es ->
     match es with
     | [] -> return []
     | h :: t -> eval_expr h >>= fun i ->
       eval_exprs t >>= fun l ->
       return (i :: l)
   
   (** [eval_prog e] evaluates program [e] *)
   let eval_prog (AProg(_,e)) =
     eval_expr e
   
   
   (** [interp s] parses [s] and then evaluates it *)
   let interp (e:string) : exp_val result =
     let c = e |> parse |> eval_prog
     in run c
     
   
   