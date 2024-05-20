import Graph.DirectedGraph
import Graph.Scc
import ListHelper.Simplelist
import ListHelper.Union
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sort

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
  num_1 : ∀ x, ¬ num x = (-1) ↔ x ∈ gray \/ x ∈ black
  num_infty : ∀ x, num x = (DirectedGraph.vertices graph: List V).length ↔ ∃ cc, x ∈ cc /\ cc ∈ sccs
  valid_gray  : ∀ x ∈ gray,  x ∈ DirectedGraph.vertices graph
  valid_black : ∀ x ∈ black, x ∈ DirectedGraph.vertices graph
  disjoint_gb : Disjoint gray black
  color : no_black_to_white graph black gray
  stack_finset : ∀ x, x ∈ stack ↔ x ∈ (gray ∪ (black \ sccs.foldl Union.union ∅))
  simplelist_stack : simplelist stack
  decreasing_stack : List.Sorted (fun x y => num x ≥ num y) stack
  -- ∀ x ∈ stack, ∀ y ∈ stack, num x ≤ num y ↔ precedes y x stack
  wf_stack₂ : ∀ x ∈ stack, ∀ y ∈ stack, num x ≤ num y → reachable graph x y
  wf_stack₃ : ∀ y ∈ stack, ∃ x ∈ gray,  num x ≤ num y /\ reachable graph y x
  sccs_in_black : ∀ cc, cc ∈ sccs ↔ Nonempty cc /\ cc ⊆ black /\ is_scc graph cc
  sccs_disjoint : ∀ cc₁ ∈ sccs, ∀ cc₂ ∈ sccs, cc₁ = cc₂ \/ cc₁ ∩ cc₂ = ∅

structure SubEnv {V Graph : Type*}
                 [BEq V] [LawfulBEq V] [DecidableEq V]
                 [DirectedGraph V Graph]
                 {graph : Graph}
                 (e e': Env V graph)
where
  eq_gray : e.gray = e'.gray
  sub_black : e.black ⊆ e'.black
  sub_sccs : e.sccs ⊆ e'.sccs
  stack_num : ∀ x ∈ e.stack, e.num x = e'.num x
  sub_stack : ∃ s, e'.stack = s ++ e.stack /\ ∀ x ∈ s, x ∈ e'.black

def subenv_trans [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V] [DecidableEq V]
                 {graph : Graph}
                 {e1 e2 e3: Env V graph}
                 (h12 : SubEnv e1 e2)
                 (h23 : SubEnv e2 e3)
                 : SubEnv e1 e3 :=
{
  eq_gray := by rw [h12.eq_gray, h23.eq_gray]
  sub_black := Finset.Subset.trans h12.sub_black h23.sub_black
  sub_sccs := List.Subset.trans h12.sub_sccs h23.sub_sccs
  stack_num := by intros x h
                  rw [h12.stack_num x h]
                  apply h23.stack_num
                  obtain ⟨s, h, _⟩ := h12.sub_stack
                  rw [h]
                  simp
                  tauto
  sub_stack := by obtain ⟨l₁, h₁, h₂⟩ := h12.sub_stack
                  obtain ⟨l₂, h₃, h₄⟩ := h23.sub_stack
                  use (l₂ ++ l₁)
                  simp_all
                  intros x h
                  cases h with
                  | inl _ => tauto
                  | inr h => apply h23.sub_black
                             apply h₂ _ h
}


def num_of_reachable [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     {graph : Graph}
                     (n: Int) (x: V) (e: Env V graph) : Prop :=
∃ y ∈ e.stack, n = e.num y /\ reachable graph x y

theorem subenv_num_of_reachable
          [DirectedGraph V Graph]
          [BEq V] [LawfulBEq V] [DecidableEq V]
          {graph : Graph}
          {e e' : Env V graph}
          {x : V}
          {n : Int}
          (h : SubEnv e e') :
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
have h₂ : x ∈ List.foldl Union.union ∅ e.sccs \/ ¬ x ∈ List.foldl Union.union ∅ e.sccs := by tauto
cases h₂
. right
  rename_i h
  rw [union_helper] at h
  assumption
. left
  rw [e.stack_finset]
  simp
  tauto

theorem gray_le_stack [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     {graph : Graph}
                     {e : Env V graph}
                     {x : V}
                     (h₁ : x ∈ e.gray) : x ∈ e.stack := by
cases (stack_or_scc x (by tauto)) with
| inl h => tauto
| inr h => obtain ⟨cc, h, h₁⟩ := h
           rw [e.sccs_in_black] at h₁
           obtain ⟨_, h₁, _⟩ := h₁
           specialize h₁ h
           have hb : {x} ≤ e.black := by simp; assumption
           have hg : {x} ≤ e.gray := by simp; assumption
           have h := e.disjoint_gb hg hb
           simp at h

theorem barrel [DirectedGraph V Graph]
               [BEq V] [LawfulBEq V] [DecidableEq V]
               {graph : Graph}
               {e : Env V graph} :
Finset.toList (e.gray ∪ e.black) ⊆ (DirectedGraph.vertices graph: List V) := by
intro x h₁
simp_all
cases h₁
. apply e.valid_gray; assumption
. apply e.valid_black; assumption

theorem croissant [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V] [DecidableEq V]
              {graph : Graph}
              (e : Env V graph) :
(Finset.toList (e.gray ∪ e.black)).length ≤ (DirectedGraph.vertices graph: List V).length := by
apply List.Subperm.length_le
apply List.subperm_of_subset
. apply Finset.nodup_toList
. apply barrel

theorem shrewd [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V] [DecidableEq V]
              {graph : Graph}
              (e : Env V graph) :
e.gray ⊔ e.black = toFinset e.stack ⊔ e.sccs.foldl Union.union ∅ := by
apply Subset.antisymm
. intros x
  simp
  intros h
  cases h
  . left
    apply gray_le_stack
    assumption
  . have h₁ : x ∈ e.sccs.foldl Union.union ∅ \/ ¬ x ∈ e.sccs.foldl Union.union ∅ := by tauto
    cases h₁
    . tauto
    . rw [e.stack_finset]
      simp
      tauto
. intros x
  simp
  rw [e.stack_finset]
  simp
  intros h
  cases h with
  | inl h => cases h <;> tauto
  | inr h => right
             rw [union_helper] at h
             obtain ⟨cc, _, h⟩ := h
             rw [e.sccs_in_black] at h
             tauto

theorem stature [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V] [DecidableEq V]
              {graph : Graph}
              (e : Env V graph) :
e.gray ∪ e.black = toFinset e.stack ∪ e.sccs.foldl Union.union ∅ := by
have h := shrewd e
simp at h
tauto

theorem tepid [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V] [DecidableEq V]
              {graph : Graph}
              (e : Env V graph) :
e.black = (toFinset e.stack ⊔ e.sccs.foldl Union.union ∅) \ e.gray := by
rw [← shrewd, Disjoint.sup_sdiff_cancel_left]
exact e.disjoint_gb

theorem sn_bound [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V] [DecidableEq V]
                 {graph : Graph}
                 (e : Env V graph) :
e.gray.card + e.black.card ≤ (DirectedGraph.vertices graph: List V).length := by
have h₁ := croissant e
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
cases (e.num_clamp x) <;> omega

theorem stack_num [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V] [DecidableEq V]
                 {graph : Graph}
                 (e : Env V graph)
                 (x : V) :
(¬ e.num x = -1) /\ (¬ e.num x = (DirectedGraph.vertices graph: List V).length) ↔ x ∈ e.stack := by
rw [e.stack_finset]
simp
have h₆ := not_congr (e.num_infty x)
rw [(e.num_1 x), h₆, <- union_helper]
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
                                    rw [e.sccs_in_black] at h₃
                                    tauto
      have h := e.disjoint_gb hg hb
      simp at h
  | inr _ => tauto

def add_stack_incr [DirectedGraph V Graph]
                   [BEq V] [LawfulBEq V] [DecidableEq V]
                   {graph : Graph}
                   (e : Env V graph)
                   (x : V)
                   (a₁ : x ∈ DirectedGraph.vertices graph)
                   (a₂ : access_to graph e.gray x)
                   (a₃ : ¬ x ∈ e.gray)
                   (a₄ : ¬ x ∈ e.black)
                   : Env V graph :=
{
  gray  := insert x e.gray
  black := e.black
  stack := x :: e.stack
  sccs := e.sccs
  num   := fun y => if y = x then e.gray.card + e.black.card else e.num y
--  sn    := e.sn + 1
  num_clamp := by simp; intros y
                  rw [Finset.card_insert_of_not_mem a₃]
                  split
                  . omega
                  . cases (e.num_clamp y) <;> omega
  num_1 := by simp
              intros y
              constructor <;> intros h
              . split at h
                . tauto
                . rw [e.num_1] at h
                  tauto
              . split
                . omega
                . rw [e.num_1]
                  tauto
  num_infty := by simp
                  intros y
                  split
                  . subst y
                    rw [<-(e.num_infty x)]
                    constructor <;> intros <;> exfalso
                    . have : (e.gray ∪ e.black) ⊆ (toFinset (DirectedGraph.vertices graph)) := by
                        intros x h
                        have := e.valid_gray x
                        have := e.valid_black x
                        rw [List.mem_toFinset]
                        simp at h
                        cases h <;> tauto
                      have h : e.gray.card + e.black.card = (DirectedGraph.vertices graph : List V).length := by omega
                      have : (toFinset (DirectedGraph.vertices graph : List V)).card ≤ (e.gray ∪ e.black).card := by
                        rw [Finset.card_union_of_disjoint e.disjoint_gb, h]
                        apply List.toFinset_card_le
                      have h₁ : e.gray ∪ e.black = toFinset (DirectedGraph.vertices graph) := by apply Finset.eq_of_subset_of_card_le <;> assumption
                      have h : x ∈ toFinset (DirectedGraph.vertices graph) := by simp; assumption
                      rw [<- h₁] at h
                      simp at h
                      tauto
                    . have h : ¬ e.num x = -1 := by omega
                      rw [e.num_1] at h
                      tauto
                  . exact e.num_infty y
  valid_gray  := by intros _ h
                    simp at h
                    cases h
                    . subst x; tauto
                    . apply e.valid_gray; assumption
  valid_black := e.valid_black
  disjoint_gb := by simp_all; exact e.disjoint_gb
  color := by intros a b h h₁
              cases (e.color a b h h₁) <;> simp <;> tauto
  stack_finset := by intros y
                     simp
                     rw [e.stack_finset]
                     simp
  simplelist_stack := by rw [simplelist_tl]
                         constructor
                         . exact e.simplelist_stack
                         . intros h
                           rw [e.stack_finset] at h
                           simp at h
                           tauto
  decreasing_stack := by
                  simp
                  repeat any_goals apply And.intro
                  all_goals intros
                  any_goals split
                  any_goals subst x
                  repeat any_goals apply And.intro
                  any_goals intros
                  repeat any_goals apply And.intro
                  any_goals omega
                  all_goals rename_i y h₂ h₃
                  . have := e.num_clamp y
                    rw [<- stack_num] at h₂
                    omega
                  . have : ¬ x ∈ e.stack := by
                      intros h
                      rw [e.stack_finset] at h
                      simp at h
                      tauto
                    simp [Sorted]
                    rw [<- List.Pairwise.iff_of_mem]
                    . exact e.decreasing_stack
                    . intros a b ha hb
                      split <;> split
                      any_goals subst a
                      any_goals subst b
                      any_goals tauto
  wf_stack₂ := by simp
                  repeat any_goals apply And.intro
                  any_goals tauto
                  all_goals intros
                  repeat any_goals apply And.intro
                  any_goals intros
                  all_goals rename_i h
                  any_goals split at h
                  any_goals split at h
                  any_goals subst x
                  any_goals tauto
                  all_goals rename_i h₁ y h₃ h₄
                  . rw [<- stack_num] at h₃
                    have := e.num_clamp y
                    omega
                  . obtain ⟨z, h, _, h₂⟩:= e.wf_stack₃ y h₃
                    specialize a₂ z h
                    apply reachable_trans _ y z x <;> tauto
                  . rw [e.stack_finset] at h₁; simp at h₁; tauto
                  . rw [e.stack_finset] at h₃; simp at h₃; tauto
                  . apply e.wf_stack₂ <;> assumption
  wf_stack₃ := by intro y h
                  cases h <;> simp_all
                  . left; tauto
                  . split
                    . subst y
                      exfalso
                      have h : x ∈ e.stack := by tauto
                      rw [e.stack_finset] at h
                      simp at h
                      tauto
                    . obtain ⟨z, h⟩ := e.wf_stack₃ y (by tauto)
                      right
                      use z
                      split
                      . subst z
                        tauto
                      . tauto
  sccs_in_black := e.sccs_in_black
  sccs_disjoint := e.sccs_disjoint
}

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
-/
