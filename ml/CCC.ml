module type CCC = sig

  (* These are mostly "phantom types" that don't really have much impact *)
  type base
  type one
  type ('a, 'b) prod
  type zero
  type ('a, 'b) sum
  type ('a, 'b) exp

  (* A category consists of a collection of objects and a collection of hom sets *)
  type 'a obj
  type ('a, 'b) hom

  (* There is a notion of equality of morphisms *)
  val eq2 : ('a obj, 'b obj) hom -> ('a obj, 'b obj) hom -> bool

  (* every object has an identity morphsym *)
  val id : 'a obj -> ('a obj, 'a obj) hom

  (* There is a way of composing morphisms *)
  val (>>>) : ('a obj, 'b obj) hom -> ('b obj, 'c obj) hom -> ('a obj, 'c obj) hom

  
  (* We have various ways of "naming" objects in the category *)
  (* [b] is some unspecified collection of "atomic" base objects *)
  val b : int -> base obj

  (* These provide ways of constructing objects in the category *)
  val u : one obj
  val z : unit -> zero obj
  val prod : 'a obj -> 'b obj -> ('a, 'b) prod obj
  val sum  : 'a obj -> 'b obj -> ('a, 'b) sum obj
  val exp  : 'a obj -> 'b obj -> ('a, 'b) exp obj

  val zero : (zero obj, 'a obj) hom

  val inl  : 'a obj -> ('a obj, ('a obj, 'b obj) sum obj) hom
  val inr  : 'b obj -> ('b obj, ('a obj, 'b obj) sum obj) hom
  val case : ('a obj, 'c obj) hom -> ('b obj, 'c obj) hom -> (('a obj, 'b obj) sum obj, 'c obj) hom

  val unit : 'a obj -> ('a obj, one obj) hom

  val fst  : 'a obj -> 'b obj -> (('a obj, 'b obj) prod obj, 'a obj) hom
  val snd  : 'a obj -> 'b obj -> (('a obj, 'b obj) prod obj, 'b obj) hom
  val pair : ('c obj, 'a obj) hom -> ('c obj, 'b obj) hom -> ('c obj, ('a obj, 'b obj) prod obj) hom

  val curry : (('a obj, 'b obj) prod obj, 'c obj) hom -> ('a obj, ('b obj, 'c obj) exp obj) hom
  val apply : 'a obj -> 'b obj -> ((('a obj, 'b obj) exp obj, 'a obj) prod obj, 'b obj) hom

  (* For debugging *)  
  val string_of_obj : 'a obj -> string
  val string_of_hom : ('a, 'b) hom -> (string * string) list

end

module OCaml : CCC =

  struct

    type base = int
    type one = unit
    type ('a, 'b) prod = 'a * 'b
    type zero = | 
    type ('a, 'b) sum =
      | Inl of 'a
      | Inr of 'b
    type ('a, 'b) exp = 'a -> 'b

    type 'a obj = 'a
    type ('a, 'b) hom = 'a -> 'b

    let b x = x
    let u = ()
    let z () = failwith "no zero obj"
    let prod x y = (x,y)
    let sum x y = Inl x
    let exp x y = fun _ -> y
    
    let eq2 f g = false
    let id x = fun a -> a

    let (>>>) f g = fun x -> g (f x)
    
    let zero = fun z -> begin match z with | _ -> failwith "ZERO" end

    let inl _  = fun x -> Inl x
    let inr _ = fun y -> Inr y
    let case f g = fun a -> begin match a with | Inl x -> f x | Inr y -> g y end

    let unit _ = fun _ -> ()

    let fst _ _ (x, y) = x
    let snd _ _ (x, y) = y
    let pair f g = fun c -> (f c, g c)

    let curry f = fun x y -> f (x, y)
    let apply _ _ (f, x) = f x

    let string_of_obj _ = "<obj>"
    let string_of_hom _ = [("in", "ou")]
  end
