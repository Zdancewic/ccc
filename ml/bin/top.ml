;; open Syntax
;; open Semantics    
;; open FinSet
;; open STLC
;; open Typecheck
;; open CCC
;; open Denotation

;; open Ast
;; open AstLib

;; open DiGraph    
    
module DSet = Denote(FinSet)

;; DSet.denote_tm (fun _ -> failwith "const") [] STLC.ex4


module DGraph = Denote(DiGraph)

(* ;; DGraph.denote_tm (fun _ -> failwith "const") [] STLC.ex4 *)
  
