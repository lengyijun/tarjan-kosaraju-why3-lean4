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
  num: Finmap (fun (_ : V) => Int)

def subenv [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V] (e e': Env V Graph graph) : Prop :=
e.gray == e'.gray /\
e.black ⊆ e'.black /\
e.sccs ⊆ e'.sccs /\
(∀ x, x ∈ e.stack -> lookup x e.num  = lookup x e'.num) /\
(∃ s, e'.stack = s ++ e.stack /\ ∀ x, x ∈ s → x ∈ e'.black)

def wf_color [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V] (e : Env V Graph graph) : Prop :=
  (∀ x, x ∈ e.gray  -> x ∈ DirectedGraph.vertices graph) /\
  (∀ x, x ∈ e.black -> x ∈ DirectedGraph.vertices graph) /\
  e.black ∩ e.gray == ∅ /\
  let sccs_union : Finset V := List.foldl (· ∪ ·) ∅ e.sccs
  sccs_union ⊆ e.black /\
  toFinset e.stack = (e.gray ∪ (e.black \ sccs_union))

def wf_num [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V] (e : Env V Graph graph) : Prop :=
  let infty : Int := (DirectedGraph.vertices graph: List V).length
  let sccs_union : Finset V := List.foldl (· ∪ ·) ∅ e.sccs
  (all (fun _ y => (-1 ≤ y && y < (e.sn: Int)) || y == infty) e.num) /\
  e.sn = Finset.card (e.gray ∪ e.black) /\
  (∀ x, lookup x e.num = some infty <-> x ∈ sccs_union) /\
  (∀ x, lookup x e.num = some (-1)  <-> ¬ x ∈ (e.gray ∪ e.black)) /\
  (∀ x y, x ∈ e.stack → y ∈ e.stack → ∃ fx fy, lookup x e.num = some fx /\ lookup y e.num = some fy /\ fx <= fy ↔ precedes y x e.stack)

def wf_env [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V] (e : Env V Graph graph) : Prop :=
wf_color e /\
wf_num e /\
no_black_to_white graph e.black e.gray /\
simplelist e.stack /\
(∀ x y, x ∈ e.stack -> y ∈ e.stack -> e.num[x] <= e.num [y] -> reachable graph x y) /\
(∀ y, y ∈ e.stack -> ∃ x, x ∈ e.gray /\ e.num[x] <= e.num[y] /\ reachable graph y x) /\
(∀ cc, cc ∈ e.sccs <-> cc ⊆ e.black /\ is_scc graph cc)
