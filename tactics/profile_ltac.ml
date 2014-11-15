open Pp
open Printer
open Util


let is_profiling = ref false
let set_profiling b = is_profiling := b


let new_call = ref false
let entered_call() = new_call := true
let is_new_call() = let b = !new_call in new_call := false; b


type entry = {mutable total : float; mutable local : float; mutable ncalls : int; mutable max_total : float}
let empty_entry() = {total = 0.; local = 0.; ncalls = 0; max_total = 0.}
let add_entry e {total; local; ncalls; max_total} =
  e.total <- e.total +. total;
  e.local <- e.local +. local;
  e.ncalls <- e.ncalls + ncalls;
  e.max_total <- max e.max_total max_total

type treenode = {entry : entry; children : (string, treenode) Hashtbl.t}
let stack = ref [{entry=empty_entry(); children=Hashtbl.create 20}]

let on_stack = Hashtbl.create 5

let get_node c table = 
  try Hashtbl.find table c
  with Not_found -> 
    let new_node = {entry=empty_entry(); children=Hashtbl.create 5} in
    Hashtbl.add table c new_node;
    new_node

let time() = 
  let times = Unix.times() in
  times.Unix.tms_utime +. times.Unix.tms_stime

let enter_tactic c =
  let parent = List.hd !stack in
  let node = get_node c parent.children in
  stack := node :: !stack;
  Hashtbl.add on_stack c (); 
  time()

let exit_tactic start_time c =
  let node :: stack' = !stack in
  let parent = List.hd stack' in
  stack := stack';
  Hashtbl.remove on_stack c;
  let diff = time() -. start_time in
  parent.entry.local <- parent.entry.local -. diff;
  add_entry node.entry {total = diff; local = diff; ncalls = 1; max_total = diff}

let try_finalize f finally =
  let res = try f() with exn -> finally(); raise exn in
  finally();
  res

let string_of_call ck =
  let s =
  string_of_ppcmds
    (match ck with
       | Proof_type.LtacNotationCall s -> str s
       | Proof_type.LtacNameCall cst -> Pptactic.pr_ltac_constant cst
       | Proof_type.LtacVarCall (id,t) -> Nameops.pr_id id
       | Proof_type.LtacAtomCall (te,otac) ->
	 (Pptactic.pr_glob_tactic (Global.env())
	    (Tacexpr.TacAtom (dummy_loc,te)))
       | Proof_type.LtacConstrInterp (c,(vars,unboundvars)) -> 
	 pr_glob_constr_env (Global.env()) c
    ) in
  for i = 0 to String.length s - 1 do if s.[i] = '\n' then s.[i] <- ' ' done;
  s

(*
let rec add_entry e1 e2 =
  e1.total <- e1.total +. e2.total;
  e1.local <- e1.local +. e2.local;
  Hashtbl.iter 
    (fun c e -> add_entry (get_node c e1.children) e) 
	e2.children
  *)

let format_sec x = (Printf.sprintf "%.3fs" x)
let format_ratio x = (Printf.sprintf "%.1f%%" (100. *. x))
let padl n s = ws (max 0 (n - utf8_length s)) ++ str s
let padr n s = str s ++ ws (max 0 (n - utf8_length s))
let padr_with c n s = 
  let ulength = utf8_length s in
  let length = String.length s in
  str (String.sub s 0 (min length (n + length - ulength))) ++ str(String.make (max 0 (n - ulength)) c)  

let rec list_iter_is_last f = function
  | []      -> ()
  | [x]     -> f true x
  | x :: xs -> f false x; list_iter_is_last f xs

(*
let rec do n f = if n <= 0 then () else f(); do (n-1) f

let repeat_str n s =
  let length_s = String.length s in
  let length_res = n * length_s in
  let res = String.create length_res in
  let pos = ref 0 in
    do n (fun()-> 
      String.blit s 0 res !pos length_s;
      pos := !pos + length_s
    );
    res
*)
let header() = 
  msgnl(str" tactic                                    self  total   calls       max");
  msgnl(str"────────────────────────────────────────┴──────┴──────┴───────┴─────────┘")

let rec print_node all_total indent first_level is_last (s,n) =
  let e = n.entry in
  msgnl(
    h 0(
      padr_with '-' 40 (indent ^ (if first_level then "" else if is_last then "└─" else "├─") ^ s^" ")
      ++padl 7 (format_ratio (e.local /. all_total))
      ++padl 7 (format_ratio (e.total /. all_total))
      ++padl 8 (string_of_int e.ncalls)
      ++padl 10 (format_sec(e.max_total))
    )
  );
  print_table all_total (indent^if first_level then "" else if is_last then "  " else "│ ") false n.children

and print_table all_total indent first_level table =
  (*let table' = Hashtbl.create (2*Hashtbl.length table) in
  Hashtbl.iter 
    (fun s e -> add_entry (get_node (string_of_call c) table') e)
    table;*)
  let ls = Hashtbl.fold 
      (fun s n l -> if n.entry.total /. all_total < 0.02 then l else (s, n) :: l) 
      table [] in
  let ls = List.sort (fun (_, n1) (_, n2) -> compare n2.entry.total n1.entry.total) ls in
    list_iter_is_last (print_node all_total indent first_level) ls

let print_results() =
  let tree = (List.hd !stack).children in
  let all_total = -. (List.hd !stack).entry.local in
  let global = Hashtbl.create 20 in
  let rec cumulate table =
    Hashtbl.iter 
      (fun s node ->
	let node' = get_node s global in
	add_entry node'.entry node.entry;
	cumulate node.children
      )
      table
  in
  cumulate tree;
  header();
  print_table all_total "" true global;
  msgnl(str"");
  header();
  print_table all_total "" true tree

let do_profile s call_trace f =
  if !is_profiling && is_new_call() then
    match call_trace with
      | (_, _, c) :: _ ->
	let s = string_of_call c in
	if 
	  Hashtbl.mem on_stack s
	then
	  f()
	else
	  let start_time = enter_tactic s in
	  try_finalize f (fun()->
	    exit_tactic start_time s
	  )
	  
      | [] -> f()
  else f()

let reset_profile() = stack := [{entry=empty_entry(); children=Hashtbl.create 20}]
