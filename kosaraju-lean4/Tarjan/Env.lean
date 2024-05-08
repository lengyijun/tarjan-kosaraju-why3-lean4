import Kosaraju.DirectedGraph
import ListHelper.Precede
import ListHelper.Union
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap

open Finmap
open Finset
open Finset List

structure Env (V : Type*) {Graph : Type*}
              [BEq V] [LawfulBEq V] [DecidableEq V]
              [DirectedGraph V Graph]
              (graph : Graph)
where
  black: Finset V
  gray: Finset V
  stack: List V
  sccs: List (Finset V)
  num:  V -> Int
  num_clamp : ∀ x, (-1 ≤ num x /\ num x < gray.card + black.card) \/ num x = (DirectedGraph.vertices graph: List V).length
  num_1 : ∀ x, num x = (-1)  <-> ¬ x ∈ (gray ∪ black)
  num_infty : ∀ x, num x = (DirectedGraph.vertices graph: List V).length ↔ ∃ cc, x ∈ cc /\ cc ∈ sccs
  valid_gray  : ∀ x ∈ gray,  x ∈ DirectedGraph.vertices graph
  valid_black : ∀ x ∈ black, x ∈ DirectedGraph.vertices graph
  disjoint_gb : Disjoint gray black
  color₁ : no_black_to_white graph black gray
  -- color₆ : sccs_union ⊆ black
  stack_finset : toFinset stack = (gray ∪ (black \ sccs.foldl (· ∪ ·) ∅))
  simplelist_stack : simplelist stack
  wf_stack₁ : ∀ x ∈ stack, ∀ y ∈ stack, num x ≤ num y ↔ precedes y x stack
  wf_stack₂ : ∀ x ∈ stack, ∀ y ∈ stack, num x ≤ num y → reachable graph x y
  wf_stack₃ : ∀ y ∈ stack, ∃ x, x ∈ gray /\ num x ≤ num y /\ reachable graph y x
  wf_sccs₁ : ∀ cc, cc ∈ sccs ↔ cc ⊆ black /\ is_scc graph cc
  wf_sccs₂ : ∀ cc₁ ∈ sccs, ∀ cc₂ ∈ sccs, cc₁ = cc₂ \/ cc₁ ∩ cc₂ = ∅


def subenv [DirectedGraph V Graph] [BEq V] [LawfulBEq V] [DecidableEq V] {graph : Graph} (e e': Env V graph) : Prop :=
e.gray = e'.gray /\
e.black ⊆ e'.black /\
e.sccs ⊆ e'.sccs /\
(∀ x, x ∈ e.stack -> e.num x = e'.num x) /\
(∃ s, e'.stack = s ++ e.stack /\ ∀ x, x ∈ s → x ∈ e'.black)

theorem subenv_trans [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     {graph : Graph}
                    {e1 e2 e3: Env V graph}
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


/-
def add_black [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V] [DecidableEq V]
              {graph : Graph}
              (x : V)
              (e : Env V graph) : Env V graph :=
{
  e with black := insert x e.black
         gray  := erase  e.gray x
}

def add_stack_incr [DirectedGraph V Graph]
                   [BEq V] [LawfulBEq V] [DecidableEq V]
                   {graph : Graph}
                   (x : V)
                   (e : Env V graph) : Env V graph :=
{
  e with gray  := insert x e.gray
         stack := x :: e.stack
        --  sn    := e.sn + 1
         num   := fun y => if y = x then sn e else e.num y
}
-/

def num_of_reachable [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     {graph : Graph}
                     (n: Int) (x: V) (e: Env V graph) : Prop :=
∃ y, y ∈ e.stack /\ n = e.num y /\ reachable graph x y

theorem subenv_num_of_reachable
          [DirectedGraph V Graph]
          [BEq V] [LawfulBEq V] [DecidableEq V]
          {graph : Graph}
          {e e' : Env V graph}
          {x : V}
          {n : Int}
          (h : subenv e e') :
(num_of_reachable n x e) -> num_of_reachable n x e' := by
simp [num_of_reachable]
intros x _ _ _
use x
obtain ⟨_, _, _, h, ⟨s, h₂⟩⟩ := h
simp_all

theorem stack_or_scc [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     {graph : Graph}
                     {e : Env V graph}
                     (x : V)
                     (h₁ : x ∈ e.gray \/ x ∈ e.black) :
x ∈ e.stack \/ (∃ cc, x ∈ cc /\ cc ∈ e.sccs) := by
have h₂ : x ∈ List.foldl (fun x x_1 => x ∪ x_1) ∅ e.sccs \/ ¬ x ∈ List.foldl (fun x x_1 => x ∪ x_1) ∅ e.sccs  := by tauto
cases h₂
. right
  rename_i h
  rw [union_helper] at h
  assumption
. left
  have h : x ∈ toFinset e.stack := by
    rw [e.stack_finset]
    simp
    tauto
  simp at h
  assumption

theorem jiqian [DirectedGraph V Graph]
               [BEq V] [LawfulBEq V] [DecidableEq V]
               {graph : Graph}
               {e : Env V graph} :
Finset.toList (e.gray ∪ e.black) ⊆ (DirectedGraph.vertices graph: List V) := by
intro x h₁
simp_all
cases h₁
. apply e.valid_gray; assumption
. apply e.valid_black; assumption

theorem navel [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V] [DecidableEq V]
              {graph : Graph}
              (e : Env V graph) :
(Finset.toList (e.gray ∪ e.black)).length ≤ (DirectedGraph.vertices graph: List V).length := by
apply List.Subperm.length_le
apply List.subperm_of_subset
. apply Finset.nodup_toList
. apply jiqian

theorem sn_bound [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V] [DecidableEq V]
                 {graph : Graph}
                 (e : Env V graph) :
e.gray.card + e.black.card ≤ (DirectedGraph.vertices graph: List V).length := by
have h₁ := navel e
simp at h₁
rw [Finset.card_union_of_disjoint e.disjoint_gb] at h₁
omega

theorem num_bound [DirectedGraph V Graph]
                    [BEq V] [LawfulBEq V] [DecidableEq V]
                    {graph : Graph}
                    (e : Env V graph)
                    {x : V} :
e.num x ≤ (DirectedGraph.vertices graph: List V).length := by
have := sn_bound e
have h := e.num_clamp
cases (h x) with
| inl h => omega
| inr h => simp at h
           omega

private theorem num_lmem_inner [DirectedGraph V Graph]
                               [BEq V] [LawfulBEq V] [DecidableEq V]
                               {graph : Graph}
                               {e : Env V graph}
                               (x : V) :
(¬ e.num x = -1) /\ (¬ e.num x = (DirectedGraph.vertices graph: List V).length) ↔ x ∈ toFinset e.stack := by
rw [e.stack_finset]
simp
have h₅ := not_congr (e.num_1 x)
have h₆ := not_congr (e.num_infty x)
rw [h₅, h₆, <- union_helper]
simp
constructor
. tauto
. intros h
  cases h with
  | inl h =>
    constructor
    . tauto
    . intros h₁
      rw [union_helper] at h₁
      obtain ⟨cc, h₁, h₃⟩ := h₁
      have hg : {x} ≤ e.gray := by simp; assumption
      have hb : {x} ≤ e.black := by simp
                                    rw [e.wf_sccs₁] at h₃
                                    tauto
      have h := e.disjoint_gb hg hb
      simp at h
  | inr _ => tauto

theorem num_lmem [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V] [DecidableEq V]
                 {graph : Graph}
                 (e : Env V graph)
                 (x : V) :
(¬ e.num x = -1) /\ (¬ e.num x = (DirectedGraph.vertices graph: List V).length) ↔ x ∈ e.stack := by
rw [num_lmem_inner]
simp
