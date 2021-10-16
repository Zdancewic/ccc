

(* This isn't very efficient *)
let string_sep_of_list (p : 'a -> string) (sep : string) (l : 'a list) =
  let rec loop l acc = 
    begin match l with
    | [] -> acc
    | x::[] -> acc ^ (p x)
    | x::tl -> loop tl (acc ^ (p x) ^ sep)
    end
  in
  loop l ""
