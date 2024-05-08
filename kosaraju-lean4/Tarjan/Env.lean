import Kosaraju.DirectedGraph
import ListHelper.Precede
import ListHelper.Simplelist
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
  num_1 : ∀ x, ¬ num x = (-1) ↔ x ∈ gray \/ x ∈ black
  num_infty : ∀ x, num x = (DirectedGraph.vertices graph: List V).length ↔ ∃ cc, x ∈ cc /\ cc ∈ sccs
  valid_gray  : ∀ x ∈ gray,  x ∈ DirectedGraph.vertices graph
  valid_black : ∀ x ∈ black, x ∈ DirectedGraph.vertices graph
  disjoint_gb : Disjoint gray black
  color₁ : no_black_to_white graph black gray
  -- color₆ : sccs_union ⊆ black
  stack_finset : ∀ x, x ∈ stack ↔ x ∈ (gray ∪ (black \ sccs.foldl (· ∪ ·) ∅))
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
  rw [e.stack_finset]
  simp
  tauto

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

theorem num_lmem [DirectedGraph V Graph]
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
                                    rw [e.wf_sccs₁] at h₃
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
  color₁ := by intros a b h h₁
               cases (e.color₁ a b h h₁) <;> simp <;> tauto
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
  wf_stack₁ := by simp
                  repeat any_goals apply And.intro
                  all_goals intros
                  all_goals split
                  any_goals subst x
                  repeat any_goals apply And.intro
                  any_goals intros
                  repeat any_goals apply And.intro
                  any_goals split
                  any_goals subst x
                  any_goals simp
                  all_goals rename_i z h₂ h₃ y h₅ h₆
                  . constructor <;> intros h <;> exfalso
                    . rw [<- num_lmem] at h₅
                      have := e.num_clamp y
                      omega
                    . obtain ⟨s1, s2, h₁, h₂⟩ := h
                      cases h₂ <;> try tauto
                      have h : simplelist (x :: e.stack) := by
                        rw [simplelist_tl]
                        constructor
                        . apply e.simplelist_stack
                        . intros h
                          rw [e.stack_finset] at h
                          simp at h
                          tauto
                      cases s1 <;> simp at h₁ <;> try tauto
                      specialize h x
                      obtain ⟨_, h₁⟩ := h₁
                      rw [h₁] at h
                      simp [num_occ] at h
                      have : num_occ x s2 > 0 := by rw [<- mem_num_occ]; tauto
                      split at h <;> omega
                  . subst y; simp
                  . rw [e.stack_finset] at h₃
                    simp at h₃
                    tauto
                  . constructor <;> intros h
                    . use []; use e.stack; tauto
                    . rw [<- num_lmem] at h₅
                      have := e.num_clamp y
                      omega
                  . rw [e.stack_finset] at h₅
                    simp at h₅
                    tauto
                  . rw [e.wf_stack₁] <;> try assumption
                    constructor <;> intros h <;> obtain ⟨s1, s2, h₁, h₂⟩ := h
                    . rw [h₁]
                      use (x :: s1)
                      use s2
                      tauto
                    . cases s1 <;> simp at h₁
                      . tauto
                      . rename_i s1
                        use s1
                        use s2
                        tauto
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
                  . rw [<- num_lmem] at h₃
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
  wf_sccs₁ := e.wf_sccs₁
  wf_sccs₂ := e.wf_sccs₂
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
