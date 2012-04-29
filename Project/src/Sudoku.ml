open Glpk

let ($) tab (i,j,k) = 
  assert (i<9 && i>=0 && j<9 && j>=0 &&  k<9 && k>=0 && Array.length tab = 729);
  tab.(i*9+j+9*9*k)

let set tab i j k value = 
  assert (i<9 && i>=0 && j<9 && j>=0 &&  k<9 && k>=0 && Array.length tab = 729);
  tab.(i*9+j+9*9*k)<-value

let print_sudoku s = 
  for k=0 to 8 do
    for j = 0 to 8 do
      for i = 0 to 8 do
	if (s$(i,j,k)<>0.0&&s$(i,j,k)<>1.0) then print_string "lol"
	else print_float (s$(i,j,k));
	print_string " ";
      done;
      print_newline();
    done;
    for i=0 to 8 do
      print_string "---";
    done;
    print_newline();
  done;
  print_newline()


let line_constr i k =
  assert (i<9 && i>=0 && k<9 && k>=0);
  Array.init 729 (fun x -> if ((x mod 81) mod 9  = i && x/81 = k) then 1.0 else 0.0)

let column_constr j k = 
  assert (j<9 && j>=0 && k<9 && k>=0);
  Array.init 729 (fun x -> if ((x mod 81)/9  = j && x/81 = k) then 1.0 else 0.0)

let square_constr n k = 
  assert (n<9 && n>=0 && k<9 && k>=0);
  Array.init 729 (fun x -> if (((x mod 9)/3 = n/3) && (((x mod 81)/9)/3 = n mod 3) && x/81 = k) then 1.0 else 0.0)

let case_constr i j = 
  assert (i<9 && i>=0 && j<9 && j>=0);
  Array.init 729 (fun x -> if ((x mod 81)/9 = j && x mod 9 = i) then 1.0 else 0.0)

let read_sudoku filename = 
  let in_chan = open_in filename 
  and y = Array.make 729 0. in
    for j=0 to 8 do
      for i=0 to 8 do
	Scanf.fscanf in_chan "%c " (fun c -> let k = int_of_char c in if k <> 42 then set y i j (k-49) 1.)
      done;
    done;
    y

let unique_number_case s i j = 
  let k = ref (-1) 
  and c = ref 0 in
    for k' = 0 to 8 do
      if s$(i,j,k')=1. 
      then (k := k';incr c)
    done;
(*    assert (!k>=0 && !k<9 && !c=1);*)
    assert (!k<9 && !c<=1);
    (!k+1)

let write_sudoku out_chan s = 
  for j=0 to 8 do
    for i=0 to 8 do
      let k = (unique_number_case s i j) in
	if (k = 0) then Printf.fprintf out_chan "* " 
	else Printf.fprintf out_chan "%i " k;
    done;
    Printf.fprintf out_chan "\n";
  done

let constr = 
  Array.init (4*81) (fun x -> match x/81 with 
		       |0 -> line_constr ((x mod 81)/9) (x mod 9)
		       |1 -> column_constr ((x mod 81)/9) (x mod 9)
		       |2 -> square_constr ((x mod 81)/9) (x mod 9)
		       |3 -> case_constr ((x mod 81)/9) (x mod 9)
		    )

let new_constr k = 
  assert(k<729);
  Array.init 729 (fun i -> if (i=k) then 1.0 else 0.0)

let add_row matrix new_row = 
  let n = Array.length matrix
  and p = Array.length matrix.(0) in 
  let new_matrix = Array.make_matrix (n+1) p 0.0 in
    for i=0 to (n-1) do
      for j=0 to (p-1) do
	new_matrix.(i).(j) <- matrix.(i).(j);
      done;
    done;
    for j=0 to (p-1) do
      new_matrix.(n).(j) <- new_row.(j);
    done;
    new_matrix


let make_2EZ_sudoku_pb filename = 
  let bbounds = Array.make (4*81) (1.,1.)
  and xbounds = Array.make 729 (0.,1.) 
  and y = read_sudoku filename in
  let slp = make_problem Maximize y constr bbounds xbounds in
    set_class slp Mixed_integer_prog;
    for i=0 to 728 do set_col_kind slp i Integer_var done;
    scale_problem slp;
    use_presolver slp true;
    slp

let init_sudoku filename = 
  let bbounds = Array.make (4*81) (1.,1.)
  and xbounds = Array.make 729 (0.,1.) 
  and y = read_sudoku filename in
  let slp = make_problem Maximize y constr bbounds xbounds in
    set_message_level slp 1;
    use_presolver slp true;
    slp

let solved prim = 
  let n=Array.length prim and b=ref true and i = ref 0 in
    while (!b && !i<n) do
      if (prim.(!i)<>0.0 && prim.(!i)<>1.0) 
      then b:=false;
      incr i
    done;
    !b

exception Solution of (float array)

let rec solve_sudoku_pb slp matrix =
  print_string "Nombre de lignes : ";
  print_int ((get_num_rows slp)-324);
  print_newline();
  simplex slp;
  let prim = get_col_primals slp in
    write_sudoku stdout prim;    
    print_sudoku prim;
    print_newline();
    if (solved prim) 
    then raise (Solution prim)
    else
      begin 
	let pprim = Array.mapi (fun i -> fun x -> (abs_float(x -. 0.5),i)) prim in
	  Array.sort (fun (a,b) (c,d) -> if a=c then 0 else if a<c then 1 else -1) pprim;
	  let nmatrix=add_row matrix (Array.make 729 0.0) and n = Array.length matrix in
	    add_rows slp 1;
	    for i=0 to (Array.length pprim-1) do
	      if ((fst pprim.(i)) <> 0.5)
	      then
		begin
		  (*print_string "On teste ";
		    print_int (snd pprim.(i));
		    print_newline();*)
		let k = snd pprim.(i) in
		  nmatrix.(n).(k)<-1.0;
		  load_matrix slp nmatrix;
		  set_row_bounds slp n Fixed_var 1.0 1.0;
		  begin
		    try
		      simplex slp;
		      if (get_obj_val slp <30.) then raise No_primal_feasible_solution;
(*		      print_float (get_obj_val slp);
		      print_newline();*)
		    with 
			No_primal_feasible_solution -> print_string "1 foire \n";set_row_bounds slp n Fixed_var 0.0 0.0; solve_sudoku_pb slp nmatrix
		  end;
		  set_row_bounds slp n Fixed_var 0.0 0.0;
		  begin
		    try
		      simplex slp;
		      if (get_obj_val slp <30.) then raise No_primal_feasible_solution;
(*		      print_float (get_obj_val slp);
		      print_newline();*)
		    with 
			No_primal_feasible_solution -> print_string "0 foire \n";set_row_bounds slp n Fixed_var 1.0 1.0; solve_sudoku_pb slp nmatrix
		  end;
		  nmatrix.(n).(k) <- 0.0
		end
	    done;
	    nmatrix.(n).(snd pprim.(0))<-1.0;
	    load_matrix slp nmatrix;
	    set_row_bounds slp n Fixed_var 1.0 1.0;
	    solve_sudoku_pb slp nmatrix
      end
	

(*let () =
  let slp = make_2EZ_sudoku_pb "test.su" and s = "lol" in
    add_rows slp 1;
    load_matrix slp (add_row constr (new_constr 0));
    set_row_bounds slp (4*81) Fixed_var 1.0 1.0;
    simplex slp;
    branch_and_bound slp;
    let prim = get_col_primals slp in
      print_sudoku prim;
      write_sudoku stdout prim
*)

let () =
  let slp = init_sudoku "test.su" in
    try
      solve_sudoku_pb slp constr
    with
	Solution(prim) ->
	  print_sudoku prim;
	  write_sudoku stdout prim
