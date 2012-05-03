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
  and y = Array.make 729 0. 
  and g = ref 0. in
    for j=0 to 8 do
      for i=0 to 8 do
	Scanf.fscanf in_chan "%c " (fun c -> let k = int_of_char c in if k <> 42 then (set y i j (k-49) 1.;g:= !g +. 1.))
      done;
    done;
    (y,!g)

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
  and (y,_) = read_sudoku filename in
  let slp = make_problem Maximize y constr bbounds xbounds in
    set_class slp Mixed_integer_prog;
    for i=0 to 728 do set_col_kind slp i Integer_var done;
    scale_problem slp;
    use_presolver slp true;
    slp

let init_sudoku filename = 
  let bbounds = Array.make (4*81) (1.,1.)
  and xbounds = Array.make 729 (0.,1.) 
  and (y,g) = read_sudoku filename in
  let slp = make_problem Maximize y constr bbounds xbounds in
    set_message_level slp 1;
    use_presolver slp true;
    print_float g;
    print_newline();
    (slp,g)

let solved prim = 
  let n=Array.length prim and b=ref true and i = ref 0 in
    while (!b && !i<n) do
      if (prim.(!i)<>0.0 && prim.(!i)<>1.0) 
      then b:=false;
      incr i
    done;
    !b

exception Solution of (float array)
exception MauvaisChoix

let iii = ref 0

let rec solve_sudoku_pb slp g matrix =
  print_string "Nombre de lignes : ";
  print_int ((get_num_rows slp)-324);
  print_newline();
  begin
    try
      simplex slp;  
    with
      |No_primal_feasible_solution -> print_string "akward MauvaisChoix";raise MauvaisChoix
  end;
  if (get_obj_val slp <> g)
  then (print_float (get_obj_val slp);print_string " humhum\n";raise MauvaisChoix);
  let prim = get_col_primals slp in
  print_float (get_obj_val slp);
  print_newline();
  write_sudoku stdout prim;    
  (*print_sudoku prim;*)
  print_newline();
    if (solved prim) 
    then raise (Solution prim)
    else
      begin 
	let pprim = Array.mapi (fun i -> fun x -> (abs_float(x -. 0.5),(prim.(i),i))) prim in
	  Array.sort (fun (a,b) (c,d) -> if a=c then 0 else if a<c then 1 else -1) pprim;
	  let nmatrix=add_row matrix (Array.make 729 0.0) and n = Array.length matrix in
	    add_rows slp 1;
	    for i=0 to (Array.length pprim-1) do
	      if (fst (snd (pprim.(i))) <> 0. && fst (snd (pprim.(i))) <> 1.)
	      then
		begin
		  (*print_string "On teste ";
		    print_int (snd (snd pprim.(i)));
		    print_newline();*)
		let k = snd (snd pprim.(i)) in
		  nmatrix.(n).(k)<-1.0;
		  load_matrix slp nmatrix;
		  set_row_bounds slp n Fixed_var 1.0 1.0;
		  begin
		    try
		      simplex slp;
		      if (get_obj_val slp -. g < 0.) then raise No_primal_feasible_solution;
		     (* print_float (get_obj_val slp);
		      print_newline();*)
		    with 
			No_primal_feasible_solution -> print_string "1 foire \n";set_row_bounds slp n Fixed_var 0.0 0.0; solve_sudoku_pb slp g nmatrix
		  end;
		  set_row_bounds slp n Fixed_var 0.0 0.0;
		  begin
		    try
		      simplex slp;
		      if (get_obj_val slp -. g < 0.) then raise No_primal_feasible_solution;
		      (*print_float (get_obj_val slp);
		      print_newline();*)
		    with 
			No_primal_feasible_solution -> print_string "0 foire \n";set_row_bounds slp n Fixed_var 1.0 1.0; solve_sudoku_pb slp g nmatrix
		  end;

		  nmatrix.(n).(k) <- 0.0
		end
	    done;
	    print_string "lol personne ne foire \n";
	    print_int (snd (snd pprim.(Array.length pprim-1)));
	    print_newline();
	    print_float (fst (snd pprim.(Array.length pprim-1)));
	    print_newline();
	    incr iii;
	    let iiii = !iii 
	    and newmatrix = Array.map (fun x -> Array.copy x) (Array.copy nmatrix) 
	    and newpprim = Array.copy pprim in  
	    try 
	      write_cplex slp ("prevention007-"^(string_of_int iiii));
	      nmatrix.(n).(snd (snd pprim.(Array.length pprim-1)))<-1.0;
	      load_matrix slp nmatrix;
	      set_row_bounds slp n Fixed_var 1.0 1.0;
	      write_cplex slp ("uberprevention007-"^(string_of_int iiii));
	      solve_sudoku_pb slp g nmatrix
	    with 
	      | MauvaisChoix -> 	      
		print_string "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<ùmŝoghf\n";
		newmatrix.(n).(snd (snd newpprim.(Array.length newpprim-1)))<-1.0;
		let newslp = read_cplex ("prevention007-"^(string_of_int iiii)) in
		set_message_level newslp 1;
		use_presolver newslp true;
		load_matrix newslp newmatrix;
		set_row_bounds newslp n Fixed_var 0.0 0.0;
		write_cplex newslp ("uberlastprevention007-"^(string_of_int iiii));
		solve_sudoku_pb newslp g newmatrix
      end
	

exception Solcomb

let read_sudoku_comb filename = 
  let in_chan = open_in filename 
  and y = Array.make 81 0 in
    for i=0 to 8 do
      for j=0 to 8 do
	Scanf.fscanf in_chan "%c " (fun c -> let k = int_of_char c in if k <> 42 then y.(j+9*i)<-(k-48))
      done;
    done;
    y

let write_sudoku_comb out_chan s = 
  for i=0 to 8 do
    for j=0 to 8 do
      Printf.fprintf out_chan "%i " s.(j+9*i);
    done;
    Printf.fprintf out_chan "\n";
  done


let case_vide s = 
  let i = ref 0 and found = ref false in
    while (not(!found) && !i<81) do
      if (s.(!i) = 0)
      then found := true
      else incr i
    done;
    if (!found) 
    then !i
    else raise Solcomb

let test_num s n i =
  let found = ref true in
    for j = 0 to 80 do
      if (((j mod 9) = (n mod 9)) || (j/9 = n/9) || ((j/27 = n/27) && ((j mod 9)/3 = (n mod 9)/3)))
      then (found := (s.(j) <> i) && !found)
    done;
    !found

let possible_num s n = 
  let l = ref [] in
    for i=1 to 9 do
      if test_num s n i 
      then l := i::!l
    done;
    !l    

let rec sud_comb s = 
  let n = case_vide s in
  let l = possible_num s n in
    teste n s l 
and teste n s l = match l with
  | [] -> s.(n)<-0;
  |x::m -> s.(n)<-x; sud_comb s; teste n s m



let () =
  let slp = make_2EZ_sudoku_pb "test.su" in
    simplex slp;
    branch_and_bound slp;
    let prim = get_col_primals slp in
      write_sudoku stdout prim;
      print_newline()



let () =
  let (slp,g) = init_sudoku "test.su" in
    try
      solve_sudoku_pb slp g constr
    with
	Solution(prim) ->
	  write_sudoku stdout prim;
	  print_newline()

let () = 
  let y = read_sudoku_comb "test.su" in
  try
    sud_comb y
  with
      Solcomb -> write_sudoku_comb stdout y
