;; open FinSet
;; open STLC
;; open Typecheck
;; open CCC
;; open Denotation

;; open Ast
;; open AstLib

module D = Denote(FinSet)

;; D.denote_tm (fun _ -> failwith "const") [] STLC.ex4
