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
let add_entry e add_total {total; local; ncalls; max_total} =
  if add_total then e.total <- e.total +. total;
  e.local <- e.local +. local;
  e.ncalls <- e.ncalls + ncalls;
  if add_total then e.max_total <- max e.max_total max_total				       

type treenode = {entry : entry; children : (string, treenode) Hashtbl.t}
let stack = ref [{entry=empty_entry(); children=Hashtbl.create 20}]

let on_stack = Hashtbl.create 5

let get_node c table = 
  try Hashtbl.find table c
  with Not_found ->
    let new_node = {entry=empty_entry(); children=Hashtbl.create 5} in
    Hashtbl.add table c new_node;
    new_node

let rec add_node node node' =
  add_entry node.entry true node'.entry;
  Hashtbl.iter
    (fun s node' -> add_node (get_node s node.children) node')
    node'.children

let time() = 
  let times = Unix.times() in
  times.Unix.tms_utime +. times.Unix.tms_stime

let try_finalize f (finally : unit -> unit) =
  let res = try f() with exn -> finally(); raise exn in
  finally();
  res

let exit_tactic start_time c add_total =
  let node :: stack' = !stack in
  let parent = List.hd stack' in
  stack := stack';
  if add_total then Hashtbl.remove on_stack c;
  let diff = time() -. start_time in
  parent.entry.local <- parent.entry.local -. diff;
  add_entry node.entry add_total {total = diff; local = diff; ncalls = 1; max_total = diff}

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
  let s = try String.sub s 0 (Util.string_index_from s 0 "(*") with Not_found -> s in
  Util.strip s
	    
let do_profile s call_trace f =
  if !is_profiling && is_new_call() then
    match call_trace with
      | (_, _, c) :: _ ->
	let s = string_of_call c in
	let parent = List.hd !stack in
	let node, add_total = try Hashtbl.find on_stack s, false
			      with Not_found -> 
				   let node = get_node s parent.children in
				   Hashtbl.add on_stack s node;
				   node, true
	in
	if not add_total && node = List.hd !stack then f() else (
	  stack := node :: !stack;
	  let start_time = time() in
	  try_finalize f (fun()->
			  exit_tactic start_time s add_total
			 )
	)
      | [] -> f()
  else f()

let format_sec x = (Printf.sprintf "%.3fs" x)
let format_ratio x = (Printf.sprintf "%.1f%%" (100. *. x))
let padl n s = ws (max 0 (n - utf8_length s)) ++ str s
let padr n s = str s ++ ws (max 0 (n - utf8_length s))
let padr_with c n s = 
  let ulength = utf8_length s in
  let length = String.length s in
  str (utf8_sub s 0 n) ++ str(String.make (max 0 (n - ulength)) c)  

let rec list_iter_is_last f = function
  | []      -> ()
  | [x]     -> f true x
  | x :: xs -> f false x; list_iter_is_last f xs

let header() = 
  msgnl(str" tactic                                    self  total   calls       max");
  msgnl(str"────────────────────────────────────────┴──────┴──────┴───────┴─────────┘")

let rec print_node all_total indent prefix (s,n) =
  let e = n.entry in
  msgnl(
    h 0(
      padr_with '-' 40 (prefix ^ s ^ " ")
      ++padl 7 (format_ratio (e.local /. all_total))
      ++padl 7 (format_ratio (e.total /. all_total))
      ++padl 8 (string_of_int e.ncalls)
      ++padl 10 (format_sec(e.max_total))
    )
    );
  print_table all_total indent false n.children

and print_table all_total indent first_level table =
  let ls = Hashtbl.fold 
	     (fun s n l -> if n.entry.total /. all_total < 0.02 then l else (s, n) :: l) 
      table [] in
  match ls with
  | [(s,n)]  when (not first_level) ->    
     print_node all_total indent (indent^"└") (s,n)
  | _ ->
     let ls = List.sort (fun (_, n1) (_, n2) -> compare n2.entry.total n1.entry.total) ls in
     list_iter_is_last
       (fun is_last ->
	print_node
	  all_total
	  (indent^if first_level then "" else if is_last then "  " else " │")
	  (indent^if first_level then "─" else if is_last then " └─" else " ├─")
       )
       ls

let print_results() =
  let tree = (List.hd !stack).children in
  let all_total = -. (List.hd !stack).entry.local in
  let global = Hashtbl.create 20 in
  let rec cumulate table =
    Hashtbl.iter 
      (fun s node ->
	let node' = get_node s global in
	add_entry node'.entry true node.entry;
	cumulate node.children
      )
      table
  in
  cumulate tree;
  msgnl(str"");
  msgnl(h 0(
      str"total time: "++padl 11 (format_sec(all_total))
    )
       );
  msgnl(str"");
  header();
  print_table all_total "" true global;
  msgnl(str"");
  header();
  print_table all_total "" true tree

let print_results_tactic tactic =
  let tree = (List.hd !stack).children in
  let table_tactic = Hashtbl.create 20 in
  let rec cumulate table =
    Hashtbl.iter
      (fun s node ->
       if String.sub (s^".") 0 (min (1+String.length s) (String.length tactic)) = tactic
       then add_node (get_node s table_tactic) node
       else cumulate node.children
      )
      table
  in
  cumulate tree;
  let all_total = -. (List.hd !stack).entry.local in
  let tactic_total =
    Hashtbl.fold
      (fun _ node all_total -> node.entry.total +. all_total)
      table_tactic 0. in
  msgnl(str"");
   msgnl(h 0(
      str"total time:           "++padl 11 (format_sec(all_total))
    )
	);
   msgnl(h 0(
      str"time spent in tactic: "++padl 11 (format_sec(tactic_total))
    )
       );
  msgnl(str"");
  header();
  print_table tactic_total "" true table_tactic
	      
let reset_profile() = stack := [{entry=empty_entry(); children=Hashtbl.create 20}]
