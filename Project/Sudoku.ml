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
      print_string "--";
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


let () = 
  print_sudoku (square_constr 4 8)


let make_ukp z c b =
  let n = Array.length z in
  let bbounds = Array.make 1 (0., b) in
  let xbounds = Array.make n (0., infinity) in
  let constrs = Array.init 1 (fun _ -> Array.init n (fun j -> c.(j))) in
  let lp = make_problem Maximize z constrs bbounds xbounds in
    set_class lp Mixed_integer_prog;
    Array.iteri (fun i _ -> set_col_kind lp i Integer_var) c;
    scale_problem lp;
    use_presolver lp true;
    lp

let () =
  let lp = make_ukp [|3.; 5.; 7.|] [|12.; 3.; 9.|] 100. in
    simplex lp;
    branch_and_bound lp;
    let prim = get_col_primals lp in
      Printf.printf "Z: %g    x0: %g    x1: %g    x2: %g\n%!" (get_obj_val lp) prim.(0) prim.(1) prim.(2)
