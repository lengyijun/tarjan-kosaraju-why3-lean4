import Kosaraju.DirectedGraph
import ListHelper.Precede
import ListHelper.Split
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Tarjan.Env

open Finmap
open Finset
open Finset List

structure Flair [DirectedGraph V Graph]
                [BEq V] [LawfulBEq V] [DecidableEq V]
                (graph : Graph) (x : V) (e : Env V Graph graph)
where
n : Int
e' : Env V Graph graph
p₁ : subenv e e'
p₂ : wf_env e'
p₃ : n ≤ e'.num x
p₄ : let infty : Int := (DirectedGraph.vertices graph: List V).length
     n = infty \/ num_of_reachable n x e'
p₅ : ∀ y,  xedge_to graph e'.stack e.stack y -> n <= e'.num y

structure Shuttle [DirectedGraph V Graph]
                  [BEq V] [LawfulBEq V] [DecidableEq V]
                  (graph : Graph) (roots: List V) (e : Env V Graph graph)
where
n : Int
e' : Env V Graph graph
p₁ : subenv e e'
p₂ : wf_env e'
p₃ : ∀ y, y ∈ roots -> y ∈ e'.gray ∪ e'.black
p₄ : ∀ y, y ∈ roots -> n ≤ e'.num y
p₅ : let infty : Int := (DirectedGraph.vertices graph: List V).length
     n = infty \/ ∃ x, x ∈ roots /\ num_of_reachable n x e'
p₆ : ∀ y,  xedge_to graph e'.stack e.stack y -> n <= e'.num y

mutual

def dfs1 [DirectedGraph V Graph]
         [BEq V] [LawfulBEq V] [DecidableEq V]
         (graph : Graph) (x : V) (e : Env V Graph graph)
         (a₁ : x ∈ DirectedGraph.vertices graph)
         (a₂ : access_to graph e.gray x)
         (a₃ : ¬ x ∈ e.black ∪ e.gray)
         (a₄ : wf_env e)
         : Int ×  Env V Graph graph :=
let n0 := e.sn
let (n1, e1) := dfs graph (DirectedGraph.succ graph x) (add_stack_incr x e) sorry sorry sorry
let (s2, s3) := split x e1.stack
let infty : Int := (DirectedGraph.vertices graph: List V).length
if n1 < n0 then
  (n1, add_black x e1)
else
  ((DirectedGraph.vertices graph: List V).length, {
    black := insert x e1.black
    gray := e.gray
    stack := s3
    sccs := (toFinset s2) :: e1.sccs
    sn := e1.sn
    num := fun (y: V) => if s2.contains y then infty else e1.num y
  })
termination_by (Finset.card (((toFinset (DirectedGraph.vertices graph : List V)) \ (e.black ∪ e.gray)) : Finset V), 0)


def dfs [DirectedGraph V Graph]
        [BEq V] [LawfulBEq V] [DecidableEq V]
        (graph : Graph) (roots: List V) (e : Env V Graph graph)
        (a₁ : roots ⊆ DirectedGraph.vertices graph)
        (a₂ : ∀ x, x ∈ roots -> access_to graph e.gray x)
        (a₃ : wf_env e)
        : Int × (Env V Graph graph) := match roots with
| [] => ((DirectedGraph.vertices graph: List V).length, e)
| x :: roots =>
  let (n1, e1) := if (e.num x) == -1 then
                    dfs1 graph x e sorry sorry sorry sorry
                  else
                    (e.num x, e)
  let (n2, e2) := dfs graph roots e1 sorry sorry sorry
  (min n1 n2, e2)
termination_by (Finset.card (((toFinset (DirectedGraph.vertices graph : List V)) \ (e.black ∪ e.gray)) : Finset V), roots.length)

end
