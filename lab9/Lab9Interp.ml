let rec i2n i =
  match i with
  | 0 -> O
  | _ -> S (i2n (i - 1))

let rec n2i n =
  match n with
  | O -> 0
  | S n' -> n2i n' + 1

let interp c =
  let rec interp' (c : 'a cmd) : 'a =
    match c with
    | Return v -> v
    | Bind (c1, c2) -> interp' (c2 (interp' c1))
    | Input -> Obj.magic (i2n (read_int ()))
    | Output v -> Obj.magic (print_int (n2i v); print_newline ())
    | Loop (i, b) ->
      begin match Obj.magic (interp' (Obj.magic (b i))) with
      | Done r -> r
      | Again r -> interp' (Loop (r, b))
      end
    | Fail -> failwith "Fail"

  in interp' c
