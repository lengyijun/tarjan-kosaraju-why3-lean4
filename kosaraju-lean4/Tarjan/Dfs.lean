import Kosaraju.DirectedGraph
import ListHelper.Precede
import ListHelper.Split
import ListHelper.Union
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Tarjan.Env

open Finmap
open Finset
open Finset List

set_option maxHeartbeats 0

structure Flair [DirectedGraph V Graph]
                [BEq V] [LawfulBEq V] [DecidableEq V]
                (graph : Graph) (x : V) (e : Env V Graph graph)
where
n : Int
e' : Env V Graph graph
p₁ : subenv e e'
p₂ : wf_env e'
p₃ : x ∈ e'.black
p₄ : n ≤ e'.num x
p₅ : let infty : Int := (DirectedGraph.vertices graph: List V).length
     n = infty \/ num_of_reachable n x e'
p₆ : ∀ y,  xedge_to graph e'.stack e.stack y -> n <= e'.num y

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
         (a₃ : ¬ x ∈ e.gray ∪ e.black)
         (a₄ : wf_env e)
         : Flair graph x e :=
let n0 := sn e
have h := by intros y hy z hz
             rw [DirectedGraph.edge_succ] at hy
             simp [add_stack_incr] at hz
             cases hz with
             | inl _ => subst z; tauto
             | inr hz => specialize a₂ z hz
                         apply reachable_trans graph z x y a₂
                         tauto
have h₁ : wf_env (add_stack_incr x e) := by
  simp [add_stack_incr]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := a₄
  repeat any_goals apply And.intro
  any_goals simp
  any_goals intros
  repeat any_goals split
  any_goals subst x
  any_goals tauto
  any_goals simp_all
  -- any_goals tauto
  any_goals intros
  all_goals sorry -- 11 goals

have termination_proof : ((add_stack_incr x e).gray ∪ (add_stack_incr x e).black).card > (e.gray ∪ e.black).card := by
  simp [add_stack_incr]
  have h := card_insert_of_not_mem a₃
  rw [h]
  omega

let ⟨n1, e1, p₁, p₂, p₃, p₄, p₅, p₆⟩ := dfs graph (DirectedGraph.succ graph x) (add_stack_incr x e) (by apply succ_valid; assumption) h h₁
let (s2, s3) := split x e1.stack
let infty : Int := (DirectedGraph.vertices graph: List V).length
if dite : n1 < n0 then
  {
    n := n1
    e' := add_black x e1
    p₁ := by sorry
    p₂ := by sorry
    p₃ := by sorry
    p₄ := by sorry
    p₅ := by sorry
    p₆ := by sorry
  }
else
  {
    n := (DirectedGraph.vertices graph: List V).length
    e' := {
            black := insert x e1.black
            gray := e.gray
            stack := s3
            sccs := (toFinset s2) :: e1.sccs
            -- sn := e1.sn
            num := fun (y: V) => if s2.contains y then infty else e1.num y
          }
    p₁ := by sorry
    p₂ := by sorry
    p₃ := by sorry
    p₄ := by sorry
    p₅ := by sorry
    p₆ := by sorry
  }
termination_by (Finset.card (((toFinset (DirectedGraph.vertices graph : List V)) \ (e.gray ∪ e.black)) : Finset V), 0)


def dfs [DirectedGraph V Graph]
        [BEq V] [LawfulBEq V] [DecidableEq V]
        (graph : Graph) (roots: List V) (e : Env V Graph graph)
        (a₁ : roots ⊆ DirectedGraph.vertices graph)
        (a₂ : ∀ x, x ∈ roots -> access_to graph e.gray x)
        (a₃ : wf_env e)
        : Shuttle graph roots e := match roots with
| [] => {
           n := (DirectedGraph.vertices graph: List V).length
           e' := e
           p₁ := by repeat any_goals apply And.intro
                    any_goals tauto
                    any_goals simp_all
           p₂ := a₃
           p₃ := by intros; tauto
           p₄ := by intros; tauto
           p₅ := by intros; tauto
           p₆ := by intros _ h
                    obtain ⟨⟨s2, h₁, ⟨x, h₃, _⟩⟩, _⟩ := h
                    symm at h₁
                    rw [List.append_left_eq_self] at h₁
                    subst s2
                    tauto
        }
| x :: roots =>
  if dite: (e.num x) == -1 then
    have h := by obtain ⟨_, _, h, _, _⟩ := a₃
                 rw [<- h]
                 simp at dite
                 exact dite
    let ⟨n1, e1, p₁, p₂, p₃, p₄, p₅, p₆⟩ := dfs1 graph x e (by tauto) (by apply a₂; tauto) h a₃
    have h := by obtain ⟨h, _, _⟩ := p₁
                 rw [<- h]
                 intros
                 apply a₂
                 tauto
    let ⟨n2, e2, p₆, p₇, p₈, p₉, pₐ, p⟩ := dfs graph roots e1 (by tauto) h p₂
    {
      n :=  min n1 n2
      e' := e2
      p₁ := subenv_trans p₁ p₆
      p₂ := p₇
      p₃ := by intros _ h
               cases h
               . simp [Union.union]
                 right
                 obtain ⟨_, p₆, _, _, _⟩ := p₆
                 apply p₆
                 assumption
               . tauto
      p₄ := by intros y h
               cases h
               . cases (stack_or_scc p₂ p₃) with
                 | inl h => obtain ⟨_, _, _, p₆, _⟩ := p₆
                            specialize p₆ x h
                            rw [p₆] at p₄
                            omega
                 | inr h => obtain ⟨cc, h₁, h₂⟩ := h
                            obtain ⟨_, _, p₆, _, _⟩ := p₆
                            specialize p₆ h₂
                            obtain ⟨_, p₇, _, _⟩ := p₇
                            specialize p₇ x
                            have h : e2.num x = (DirectedGraph.vertices graph: List V).length := by
                              rw [p₇, union_helper]
                              use cc
                            rw [h]
                            cases pₐ <;> try omega
                            rename_i h
                            obtain ⟨x, y, _, _, h, _⟩ := h
                            sorry
               . rename_i h
                 specialize p₉ y h
                 omega
      p₅ := by sorry
      p₆ := by sorry
    }
  else
    let n1 := e.num x
    have h := by intros
                 apply a₂
                 tauto
    let ⟨n2, e2, p₁, p₂, p₃, p₄, p₅, p₆⟩ := dfs graph roots e (by tauto) h a₃
    {
      n :=  min n1 n2
      e' := e2
      p₁ := p₁
      p₂ := p₂
      p₃ := by intros _ h
               cases h
               . have h : x ∈ e.gray ∪ e.black \/ ¬ x ∈ e.gray ∪ e.black := by tauto
                 cases h with
                 | inl h => obtain ⟨_, _, _⟩ := p₁
                            simp_all
                            cases h <;> tauto
                 | inr h => obtain ⟨_, _, a₃, _, _⟩ := a₃
                            rw [<- a₃] at h
                            simp_all
               . apply p₃; assumption
      p₄ := by intros y h
               cases h <;> rename_i h
               . sorry
               . specialize p₄ y h
                 omega
      p₅ := by sorry
      p₆ := by intros y h
               specialize p₆ y h
               omega
    }
termination_by (Finset.card (((toFinset (DirectedGraph.vertices graph : List V)) \ (e.gray ∪ e.black)) : Finset V), roots.length)

end
