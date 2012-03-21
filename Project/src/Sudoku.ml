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
	print_float (s$(i,j,k));
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
    assert (!k>=0 && !k<9 && !c=1);
    (!k+1)

let write_sudoku out_chan s = 
  for j=0 to 8 do
    for i=0 to 8 do
      Printf.fprintf out_chan "%i " (unique_number_case s i j)
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


let make_sudoku_pb filename = 
  let bbounds = Array.make (4*81) (1.,1.)
  and xbounds = Array.make 729 (0.,1.) 
  and y = read_sudoku filename in
  let slp = make_problem Maximize y constr bbounds xbounds in
    set_class slp Mixed_integer_prog;
    for i=0 to 728 do set_col_kind slp i Integer_var done;
    scale_problem slp;
    use_presolver slp true;
    slp

let () =
  let slp = make_sudoku_pb "test.su" in
    simplex slp;
    branch_and_bound slp;
    let prim = get_col_primals slp in
      print_sudoku prim;
      write_sudoku stdout prim
