import Kosaraju.DirectedGraph
import ListHelper.Precede
import ListHelper.Union
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap

open Finmap
open Finset
open Finset List

structure Env (V Graph : Type*)
              [DirectedGraph V Graph]
              (graph : Graph)
where
  black: Finset V
  gray: Finset V
  stack: List V
  sccs: List (Finset V)
  num:  V -> Int

def sn [DirectedGraph V Graph] (e: Env V Graph graph) : Int :=
Finset.card e.gray + Finset.card e.black

def subenv [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V] (e e': Env V Graph graph) : Prop :=
e.gray = e'.gray /\
e.black ⊆ e'.black /\
e.sccs ⊆ e'.sccs /\
(∀ x, x ∈ e.stack -> e.num x = e'.num x) /\
(∃ s, e'.stack = s ++ e.stack /\ ∀ x, x ∈ s → x ∈ e'.black)

theorem subenv_trans [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V]
                    {e1 e2 e3: Env V Graph graph}
                    (h12 : subenv e1 e2)
                    (h23 : subenv e2 e3)
                    : subenv e1 e3 := by
obtain ⟨ _,  _,  _, h₄, h₅, h₆, h₇⟩ := h12
obtain ⟨k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ := h23
repeat any_goals apply And.intro
any_goals tauto
any_goals simp_all
use (k₅ ++ h₅)
simp_all
intros _ h
cases h
. apply k₇; assumption
. apply k₂
  apply h₇
  assumption


def wf_env [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V] (e : Env V Graph graph) : Prop :=
let infty : Int := (DirectedGraph.vertices graph: List V).length
let sccs_union : Finset V := List.foldl (· ∪ ·) ∅ e.sccs
(∀ x, (-1 ≤ e.num x /\ e.num x < (sn e)) \/ e.num x == infty) /\
(∀ x, e.num x = infty <-> x ∈ sccs_union) /\
(∀ x, e.num x = (-1)  <-> ¬ x ∈ (e.gray ∪ e.black)) /\
(∀ x, x ∈ e.gray  -> x ∈ DirectedGraph.vertices graph) /\
(∀ x, x ∈ e.black -> x ∈ DirectedGraph.vertices graph) /\
Disjoint e.gray e.black  /\
sccs_union ⊆ e.black /\
toFinset e.stack = (e.gray ∪ (e.black \ sccs_union)) /\
no_black_to_white graph e.black e.gray /\
simplelist e.stack /\
(∀ x y, x ∈ e.stack → y ∈ e.stack → e.num x <= e.num y ↔ precedes y x e.stack) /\
(∀ x y, x ∈ e.stack → y ∈ e.stack → e.num x <= e.num y → reachable graph x y) /\
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
        --  sn    := e.sn + 1
         num   := fun y => if y = x then sn e else e.num y
}

def num_of_reachable [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     (n: Int) (x: V) (e: Env V Graph graph) : Prop :=
∃ y, y ∈ e.stack /\ n = e.num y /\ reachable graph x y

private theorem num_lmem_inner [DirectedGraph V Graph]
                               [BEq V] [LawfulBEq V] [DecidableEq V]
                               {e : Env V Graph graph}
                               (h : wf_env e)
                               (x : V) :
let infty : Int := (DirectedGraph.vertices graph: List V).length
(¬ e.num x = -1) /\ (¬ e.num x = infty) <-> x ∈ toFinset e.stack := by
obtain ⟨h₅, h₃, h₄, h₇, h₈, h₉, h₂, h, _⟩ := h
rw [h]
simp
have h₅ := not_congr (h₃ x)
have h₆ := not_congr (h₄ x)
rw [h₅, h₆]
simp
constructor
. tauto
. intros h
  cases h with
  | inl h =>
    constructor
    . tauto
    . intros h₁
      specialize h₂ h₁
      simp_all
      have h₂ : {x} ≤ e.gray := by simp; assumption
      have h : {x} ≤ e.black := by simp; assumption
      specialize h₉ h₂ h
      simp at h₉
  | inr _ => tauto

theorem num_lmem [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V] [DecidableEq V]
                 {e : Env V Graph graph}
                 (h : wf_env e)
                 (x : V) :
let infty : Int := (DirectedGraph.vertices graph: List V).length
(¬ e.num x = -1) /\ (¬ e.num x = infty) <-> x ∈ e.stack := by
intros
have h := num_lmem_inner h x
simp at h
rw [h]

theorem stack_or_scc [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     {e : Env V Graph graph}
                     (h : wf_env e)
                     {x : V}
                     (h₁ : x ∈ e.black) :
x ∈ e.stack \/ (∃ cc, x ∈ cc /\ cc ∈ e.sccs) := by
obtain ⟨_, _, _, _, _, _, _, h₃, _⟩ := h
have h₂ : x ∈ List.foldl (fun x x_1 => x ∪ x_1) ∅ e.sccs \/ ¬ x ∈ List.foldl (fun x x_1 => x ∪ x_1) ∅ e.sccs  := by tauto
cases h₂
. right
  rename_i h
  rw [union_helper] at h
  assumption
. left
  have h : x ∈ toFinset e.stack := by
    rw [h₃]
    simp
    tauto
  simp at h
  assumption

theorem jiqian [DirectedGraph V Graph]
               [BEq V] [LawfulBEq V] [DecidableEq V]
               {e : Env V Graph graph}
               (h : wf_env e) :
Finset.toList (e.gray ∪ e.black) ⊆ (DirectedGraph.vertices graph: List V) := by
intro x h₁
simp_all
obtain ⟨_, _, _, h₂, h₃, _⟩ := h
cases h₁ <;> tauto

theorem navel [DirectedGraph V Graph]
               [BEq V] [LawfulBEq V] [DecidableEq V]
               {e : Env V Graph graph}
               (h : wf_env e) :
(Finset.toList (e.gray ∪ e.black)).length ≤ (DirectedGraph.vertices graph: List V).length := by
apply List.Subperm.length_le
apply List.subperm_of_subset
. apply Finset.nodup_toList
. apply jiqian
  assumption


theorem sn_bound [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V] [DecidableEq V]
                 {e : Env V Graph graph}
                 (h : wf_env e) :
sn e ≤ (DirectedGraph.vertices graph: List V).length := by
simp [sn]
have h₁ := navel h
simp at h₁
obtain ⟨h, _, _, _, _, h₂, _⟩ := h
rw [Finset.card_union_of_disjoint h₂] at h₁
omega

theorem upper_bound [DirectedGraph V Graph]
                    [BEq V] [LawfulBEq V] [DecidableEq V]
                    {e : Env V Graph graph}
                    (h : wf_env e)
                    {x : V} :
e.num x ≤ (DirectedGraph.vertices graph: List V).length := by
have := sn_bound h
obtain ⟨h, _, _, _⟩ := h
specialize h x
cases h with
| inl h => omega
| inr h => simp at h
           omega
