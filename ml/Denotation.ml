;; open STLC
;; open CCC


module Denote (C : CCC) = struct

  let rec denote_typ (t:typ) : C.obj =
    begin match t with
    | Base n -> C.b n
    | Zero   -> C.z ()  (* Thunked? *)
    | Plus(t, u) -> C.sum (denote_typ t) (denote_typ u)
    | One -> C.u
    | Prod(t, u) -> C.prod (denote_typ t) (denote_typ u)
    | Arr(t, u) -> C.exp (denote_typ t) (denote_typ u)
    end


end  
