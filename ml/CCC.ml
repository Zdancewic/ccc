module type CCC = sig

  (*
  (* These are mostly "phantom types" that don't really have much impact *)
  type base
  type one
  type ('a, 'b) prod
  type zero
  type ('a, 'b) sum
  type ('a, 'b) exp
   *)

  (* A category consists of a collection of objects and a collection of hom sets *)
  type obj
  type hom

  (* There is a notion of equality of morphisms *)
  val eq2 : hom -> hom -> bool

  (* every object has an identity morphsym *)
  val id : obj -> hom

  (* There is a way of composing morphisms *)
  val (>>>) : hom -> hom -> hom

  
  (* We have various ways of "naming" objects in the category *)
  (* [b] is some unspecified collection of "atomic" base objects *)
  val b : int -> obj

  (* These provide ways of constructing objects in the category *)
  val u : obj
  val z : obj
  val prod : obj -> obj -> obj
  val sum  : obj -> obj -> obj
  val exp  : obj -> obj -> obj

  val zero : obj -> hom

  val inl  : obj -> obj -> hom
  val inr  : obj -> obj -> hom
  val case : hom -> hom -> hom

  val unit : obj -> hom

  val fst  : obj -> obj -> hom
  val snd  : obj -> obj -> hom
  val pair : hom -> hom -> hom

  val curry : hom -> hom
  val apply : obj -> obj -> hom

  (* For debugging *)  
  val string_of_obj : obj -> string
  val string_of_hom : hom -> (string * string) list

end

module OCaml : CCC =

  struct
    type obj = unit
    type hom =
      | Fun : ('a -> 'b) -> hom

    let b x = ()
    let u = ()
    let z = ()
    let prod x y = ()
    let sum x y = ()
    let exp x y = ()

    type ('a,'b) sum =
      | Inl of 'a
      | Inr of 'b

    type void = | 
    
    let eq2 f g = false
    let id x = Fun (fun a -> a)

    let (>>>) (Fun f) (Fun g) = Fun (fun x -> g (Obj.magic (f x)))
    
    let zero _ = Fun (fun (z:void) -> begin match z with | _ -> . end)

    let inl _ _  = Fun (fun x -> Inl x)
    let inr _ _ = Fun (fun y -> Inr y)
    let case (Fun f) (Fun g) = Fun (fun a -> begin match a with | Inl x -> f x | Inr y -> (Obj.magic g y) end)

    let unit _ = Fun (fun _ -> ())

    let fst _ _ = Fun fst
    let snd _ _ = Fun snd
    let pair (Fun f) (Fun g) = Fun (fun c -> (f c, (Obj.magic g c)))

    let curry (Fun f) = Fun (fun x y -> (Obj.magic f (x, y)))
    let apply _ _ = Fun (fun (f, x) -> f x)

    let string_of_obj _ = "<obj>"
    let string_of_hom _ = [("in", "out")]
  end
