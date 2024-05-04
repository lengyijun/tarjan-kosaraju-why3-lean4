import Kosaraju.DirectedGraph
import ListHelper.Precede
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap

open Finmap
open Finset
open Finset List

structure Env (V Graph : Type*)
              [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V] [DecidableEq V]
              (graph : Graph)
where
  black: Finset V
  gray: Finset V
  stack: List V
  sccs: List (Finset V)
  sn: Nat
  num:  V -> Int

def subenv [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V] (e e': Env V Graph graph) : Prop :=
e.gray == e'.gray /\
e.black ⊆ e'.black /\
e.sccs ⊆ e'.sccs /\
(∀ x, x ∈ e.stack -> e.num x = e'.num x) /\
(∃ s, e'.stack = s ++ e.stack /\ ∀ x, x ∈ s → x ∈ e'.black)

def wf_env [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V] (e : Env V Graph graph) : Prop :=
let infty : Int := (DirectedGraph.vertices graph: List V).length
let sccs_union : Finset V := List.foldl (· ∪ ·) ∅ e.sccs
(∀ x, (-1 ≤ e.num x && e.num x < (e.sn: Int)) || e.num x == infty) /\
e.sn = Finset.card (e.gray ∪ e.black) /\
(∀ x, e.num x = infty <-> x ∈ sccs_union) /\
(∀ x, e.num x = (-1)  <-> ¬ x ∈ (e.gray ∪ e.black)) /\
(∀ x y, x ∈ e.stack → y ∈ e.stack → e.num x <= e.num y ↔ precedes y x e.stack) /\
(∀ x, x ∈ e.gray  -> x ∈ DirectedGraph.vertices graph) /\
(∀ x, x ∈ e.black -> x ∈ DirectedGraph.vertices graph) /\
e.black ∩ e.gray == ∅ /\
sccs_union ⊆ e.black /\
toFinset e.stack = (e.gray ∪ (e.black \ sccs_union)) /\
no_black_to_white graph e.black e.gray /\
simplelist e.stack /\
(∀ x y, x ∈ e.stack -> y ∈ e.stack -> e.num x <= e.num y -> reachable graph x y) /\
(∀ y, y ∈ e.stack -> ∃ x, x ∈ e.gray /\ e.num x <= e.num y /\ reachable graph y x) /\
(∀ cc, cc ∈ e.sccs <-> cc ⊆ e.black /\ is_scc graph cc) /\
(∀ cc₁ cc₂, cc₁ ∈ e.sccs -> cc₂ ∈ e.sccs -> cc₁ = cc₂ \/ cc₁ ∩ cc₂ = ∅)

def add_black [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V] [DecidableEq V]
              (x : V)
              (e : Env V Graph graph) : Env V Graph graph :=
{
  e with black := insert x e.black
         gray  := erase  e.gray x
}

def add_stack_incr [DirectedGraph V Graph]
                   [BEq V] [LawfulBEq V] [DecidableEq V]
                   (x : V)
                   (e : Env V Graph graph) : Env V Graph graph :=
{
  e with gray  := insert x e.gray
         stack := x :: e.stack
         sn    := e.sn + 1
         num   := fun y => if y = x then e.sn else e.num y
}

def num_of_reachable [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     (n: Int) (x: V) (e: Env V Graph graph) : Prop :=
∃ y, y ∈ e.stack /\ n = e.num y /\ reachable graph x y
