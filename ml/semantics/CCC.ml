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
  val one : obj
  val zero : obj
  val prod : obj -> obj -> obj
  val sum  : obj -> obj -> obj
  val exp  : obj -> obj -> obj

  (* abort A : 0 ==> A *)
  val abort : obj -> hom

  (* inl A B : A ==> A + B *)
  val inl  : obj -> obj -> hom

  (* inr A B : B ==> A + B *)
  val inr  : obj -> obj -> hom

  (* f : A ==> C
     g : B ==> C
     case f g : A + B ==> C
   *)
  val case : hom -> hom -> hom

  (* unit A : A ==> 1 *)
  val unit : obj -> hom

  (* fst A B : A * B ==> A *)
  val fst  : obj -> obj -> hom

  (* snd A B : A * B ==> B *)
  val snd  : obj -> obj -> hom

  (* f : C ==> A
     g : C ==> B
     pair f g : C ==> A * B
   *)
  val pair : hom -> hom -> hom

  (* f : A ==> C
     g : B ==> D
     bimmap_prod A B : A * B ==> C * D
     ===
     pair (fst A B >>> f) (snd A B >>> g)
  *)
  (* val bimap_prod : obj -> obj -> hom -> hom -> hom *)
      
  (* f : A * B ==> C 
     curry f : A ==> [B -> C]
   *)
  val curry : hom -> hom

  (* apply A B : [A -> B] * A ==> B *)
  val apply : obj -> obj -> hom

  (* For debugging *)  
  val pp_obj : Format.formatter -> obj -> unit
  val string_of_obj : obj -> string
  val pp_hom : Format.formatter -> hom -> unit
  val string_of_hom : hom -> string

end

module OCaml : CCC =

  struct
    type obj = unit
    type hom =
      | Fun : ('a -> 'b) -> hom

    let b x = ()
    let one = ()
    let zero = ()
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
    
    let abort _ = Fun (fun (z:void) -> begin match z with | _ -> . end)

    let inl _ _  = Fun (fun x -> Inl x)
    let inr _ _ = Fun (fun y -> Inr y)
    let case (Fun f) (Fun g) = Fun (fun a -> begin match a with | Inl x -> f x | Inr y -> (Obj.magic g y) end)

    let unit _ = Fun (fun _ -> ())

    let fst _ _ = Fun fst
    let snd _ _ = Fun snd
    let pair (Fun f) (Fun g) = Fun (fun c -> (f c, (Obj.magic g c)))

    let bimap_prod (Fun f) (Fun g) = Fun (fun (x,y) -> (f x, g y))
        
    let curry (Fun f) = Fun (fun x y -> (Obj.magic f (x, y)))
    let apply _ _ = Fun (fun (f, x) -> f x)

    let pp_obj _ _ = ()
    let pp_hom _ _ = ()                     
    let string_of_obj _ = "<obj>"
    let string_of_hom _ = "<in -> out>"
  end
