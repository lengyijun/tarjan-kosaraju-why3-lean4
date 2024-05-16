import Graph.DirectedGraph
import ListHelper.Precede
import ListHelper.Rip
import ListHelper.Union
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finmap
import Std.Data.List.Lemmas
import Tarjan.Env

open Finmap
open Finset
open Finset List

set_option maxHeartbeats 0

structure Flair [DirectedGraph V Graph]
                [BEq V] [LawfulBEq V] [DecidableEq V]
                (graph : Graph) (x : V) (e : Env V graph)
where
n : Int
e' : Env V graph
p₁ : SubEnv e e'
p₃ : x ∈ e'.black
p₄ : n ≤ e'.num x
p₅ : let infty : Int := (DirectedGraph.vertices graph: List V).length
     n = infty \/ num_of_reachable n x e'
p₆ : ∀ y ∈ e.stack, (∃ s, e'.stack = s ++ e.stack /\ ∃ x ∈ s, DirectedGraph.edge graph x y) → n ≤ e'.num y

structure Shuttle [DirectedGraph V Graph]
                  [BEq V] [LawfulBEq V] [DecidableEq V]
                  (graph : Graph) (roots: List V) (e : Env V graph)
where
n : Int
e' : Env V graph
p₁ : SubEnv e e'
p₃ : ∀ y ∈ roots, y ∈ e'.gray ∪ e'.black
p₄ : ∀ y ∈ roots, n ≤ e'.num y
p₅ : let infty : Int := (DirectedGraph.vertices graph: List V).length
     n = infty \/ ∃ x ∈ roots, num_of_reachable n x e'
p₆ : ∀ y ∈ e.stack, (∃ s, e'.stack = s ++ e.stack /\ ∃ x ∈ s, DirectedGraph.edge graph x y) → n ≤ e'.num y

mutual

def dfs3 [DirectedGraph V Graph]
         [BEq V] [LawfulBEq V] [DecidableEq V]
         (graph : Graph) (x : V) (e : Env V graph)
         (a₁ : x ∈ DirectedGraph.vertices graph)
         (a₂ : access_to graph e.gray x)
         (a₃ : ¬ x ∈ e.gray)
         (a₄ : ¬ x ∈ e.black)
         : Flair graph x e :=
-- let n0 := e.gray.card + e.black.card
have h := by intros y hy z hz
             rw [DirectedGraph.edge_succ] at hy
             simp [add_stack_incr] at hz
             cases hz with
             | inl _ => subst z; tauto
             | inr hz => specialize a₂ z hz
                         apply reachable_trans graph z x y a₂
                         tauto
have : ¬ x ∈ e.stack := by
  intros h
  rw [e.stack_finset] at h
  simp at h
  tauto
have h₁ : e.gray ∪ e.black ⊆ toFinset (DirectedGraph.vertices graph) := by
  intros y h
  simp at h
  cases h <;> simp_all
  . apply e.valid_gray; assumption
  . apply e.valid_black; assumption

have h₂ : Insert.insert x (e.gray ∪ e.black) ⊆ toFinset (DirectedGraph.vertices graph) := by
  intros y h
  simp at h
  cases h <;> simp_all
  rename_i h
  cases h
  . apply e.valid_gray; assumption
  . apply e.valid_black; assumption

have termination_proof : (toFinset (DirectedGraph.vertices graph) \
  ((add_stack_incr e x a₁ a₂ a₃ a₄).gray ∪ (add_stack_incr e x a₁ a₂ a₃ a₄).black)).card <
  (toFinset (DirectedGraph.vertices graph) \ (e.gray ∪ e.black)).card := by
  rw [Finset.card_sdiff]
  rw [Finset.card_sdiff]
  any_goals simp [add_stack_incr]
  any_goals assumption
  . have h := Finset.card_le_card h₂
    rw [card_insert_of_not_mem] at *
    . omega
    . intros h; simp at h; cases h <;> tauto
    . intros h; simp at h; cases h <;> tauto


let ⟨n1, e1, p₁, p₃, p₄, p₅, p₆⟩ := dfs graph (DirectedGraph.succ graph x) (add_stack_incr e x a₁ a₂ a₃ a₄) (by apply succ_valid; assumption) h
have : x ∈ e1.gray := by
  rw [<- p₁.eq_gray]
  simp [add_stack_incr]
have not_x_in_black : ¬ x ∈ e1.black := by
  intros _
  have hb : {x} ≤ e1.black := by simp; assumption
  have hg : {x} ≤ e1.gray := by simp; assumption
  have h := e1.disjoint_gb hg hb
  simp at h
have h₈ : e1.num x = e.gray.card + e.black.card := by
  rw [<- p₁.stack_num]
  all_goals simp [add_stack_incr]
let ⟨s, last⟩ := split_once x e1.stack
have h₇ : s ++ x :: e.stack = e1.stack /\ ∀ y ∈ s, y ∈ e1.black := by
  obtain ⟨s, h, h₁⟩ := p₁.sub_stack
  simp [add_stack_incr] at h h₁
  obtain ⟨s3, h₂⟩ := last (by apply gray_le_stack; assumption)
  have h₃ := e1.simplelist_stack
  rw [h] at h₂ h₃
  symm at h₂
  obtain ⟨_, _⟩ := simplelist_uniq _ _ _ _ h₂ h₃
  subst s3 s
  tauto
if dite : n1 < e.gray.card + e.black.card then
  have p₅ : ∃ y ∈ DirectedGraph.succ graph x, ∃ z ∈ e1.stack, n1 = e1.num z ∧ reachable graph y z := by
    cases p₅ <;> try tauto
    subst n1
    have := sn_bound e
    omega
  have : erase e1.gray x ∪ insert x e1.black ⊆ e1.gray ∪ e1.black := by
    intros y h
    have hy : y = x \/ ¬ y = x := by tauto
    cases hy <;> simp_all
  have : e1.gray ∪ e1.black ⊆ erase e1.gray x ∪ insert x e1.black := by
    intros y h
    have hy : y = x \/ ¬ y = x := by tauto
    cases hy <;> simp_all
  have h₉ : erase e1.gray x ∪ insert x e1.black = e1.gray ∪ e1.black := by
    apply Finset.Subset.antisymm <;> assumption
  have disjoint_gb : Disjoint (erase e1.gray x) (insert x e1.black) := by
    simp
    rw [Finset.erase_eq e1.gray x]
    apply Disjoint.disjoint_sdiff_left e1.disjoint_gb
  have h₆ : ∃ y ∈ e1.gray, e1.num y < e1.num x /\ in_same_scc graph x y := by
    obtain ⟨y, p₅, z, h, h₁, h₂⟩ := p₅
    obtain ⟨k, h₃, h₄, h₅⟩ := e1.wf_stack₃ z h
    use k
    have : e1.num z < e1.num x := by rw [<- h₁]; omega
    have : e1.num k < e1.num x := by omega
    repeat any_goals apply And.intro
    any_goals assumption
    . apply reachable_trans _ x z k
      any_goals assumption
      apply reachable_trans _ x y z
      any_goals assumption
      rw [DirectedGraph.edge_succ] at p₅
      tauto
    . apply e1.wf_stack₂
      any_goals omega
      any_goals apply gray_le_stack
      any_goals assumption
  {
    n := n1
    e' := {
black := insert x e1.black
gray := erase e1.gray x
stack := e1.stack
sccs := e1.sccs
num := e1.num
num_clamp := by
  intros y
  have h := Finset.card_union_of_disjoint disjoint_gb
  rw [h₉, Finset.card_union_of_disjoint e1.disjoint_gb] at h
  have := e1.num_clamp y
  omega
num_1 := by intros y; rw [e1.num_1, ← Finset.mem_union, ← Finset.mem_union, h₉]
num_infty := e1.num_infty
valid_gray := by intros; apply e1.valid_gray; simp_all
valid_black := by intros _ h
                  simp at h
                  cases h
                  . subst x
                    tauto
                  . apply e1.valid_black; assumption
disjoint_gb := disjoint_gb
color₁ := by intros a b h₁ h₂
             rw [← Finset.mem_union, h₉]
             simp at h₂
             cases h₂
             . apply p₃
               rw [DirectedGraph.edge_succ]
               subst a
               assumption
             . rw [Finset.mem_union]
               apply e1.color₁ <;> assumption
stack_finset := by
  intros y
  rw [e1.stack_finset]
  have h : y = x \/ ¬ y = x := by tauto
  cases h <;> constructor <;> simp_all
  intros h
  rw [union_helper] at h
  apply not_x_in_black
  simp_all
  obtain ⟨cc, h, h₁⟩ := h
  rw [e1.sccs_in_black] at h₁
  tauto
simplelist_stack := e1.simplelist_stack
decreasing_stack := e1.decreasing_stack
wf_stack₂ := e1.wf_stack₂
wf_stack₃ := by intros y hy
                obtain ⟨z, _, _, _⟩ := e1.wf_stack₃ y hy
                have h₃ : x = z \/ ¬ x = z := by tauto
                cases h₃
                . subst z
                  obtain ⟨z, _, _, ⟨_, _⟩⟩ := h₆
                  use z
                  simp
                  repeat any_goals apply And.intro
                  any_goals omega
                  any_goals tauto
                  . intros h
                    subst z
                    omega
                  . apply reachable_trans _ y x z <;> assumption
                . use z
                  simp_all
                  tauto
sccs_in_black := by intros cc
                    rw [e1.sccs_in_black cc]
                    constructor <;> intros h₁ <;> simp_all <;> intros y h
                    . simp
                      right
                      tauto
                    . obtain ⟨h₁, _⟩ := h₁
                      have h₄ := h₁ h
                      simp at h₄
                      have h₃ : x = y \/ ¬ x = y := by tauto
                      cases h₃ <;> cases h₄
                      any_goals subst y
                      any_goals tauto
                      exfalso
                      obtain ⟨y, _, _, _⟩ := h₆
                      have h := scc_max graph x y cc (by assumption) (by assumption) (by assumption)
                      specialize h₁ h
                      simp at h₁
                      cases h₁
                      . subst y
                        simp_all
                      . have hg : {y} ≤ e1.gray := by simp; assumption
                        have hb : {y} ≤ e1.black := by simp; assumption
                        have h := e1.disjoint_gb hg hb
                        simp at h
sccs_disjoint := e1.sccs_disjoint
          }

    p₁ := {
            eq_gray := by simp
                          rw [<- p₁.eq_gray]
                          simp [add_stack_incr]
                          rw [Finset.erase_eq_of_not_mem]
                          all_goals tauto
            sub_black := by simp
                            have h := p₁.sub_black
                            simp [add_stack_incr] at h
                            intros y hy
                            specialize h hy
                            simp
                            tauto
            sub_sccs := by simp
                           have h := p₁.sub_sccs
                           simp [add_stack_incr] at h
                           assumption
            stack_num := by simp
                            have h := p₁.stack_num
                            simp [add_stack_incr] at h
                            obtain ⟨_, h⟩ := h
                            intros y hy
                            specialize h y hy
                            split at h
                            any_goals assumption
                            subst y
                            rw [e.stack_finset] at hy
                            simp at hy
                            cases hy <;> tauto
            sub_stack := by simp
                            use (s ++ [x])
                            simp_all
                            intros y h
                            cases h <;> tauto
          }
    p₃ := by simp
    p₄ := by simp; rw [h₈]; omega
    p₅ := by right
             obtain ⟨y, h₁, z, h₂, h₃, h₄⟩ := p₅
             use z
             rw [DirectedGraph.edge_succ] at h₁
             have := DirectedGraph.valid_edge _ _ _ h₁
             simp_all
             apply reachable_trans _ x y z <;> tauto
    p₆ := by simp
             intros y hy s hs z hz _
             have hxz : z = x \/ ¬ z = x := by tauto
             cases hxz
             . subst z
               apply p₄
               rw [DirectedGraph.edge_succ]
               assumption
             . apply p₆
               all_goals simp [add_stack_incr]
               any_goals tauto
               obtain ⟨s5, h₃, h₄⟩ := p₁.sub_stack
               simp [add_stack_incr] at h₃
               use s5
               constructor
               . tauto
               . use z
                 rw [hs, ← singleton_append, ← List.append_assoc] at h₃
                 have := append_inj_left' h₃ rfl
                 subst s
                 simp_all
  }
else
  have disjoint_s2_s3: ∀ x, x ∈ s -> x ∈ e.stack -> False := by
    intros y h₁ h₂
    have h := e1.simplelist_stack y
    obtain ⟨h₇, _⟩ := h₇
    rw [<- h₇] at h
    simp [num_occ] at h
    rw [mem_num_occ] at *
    split at h
    any_goals omega
  {
    n := (DirectedGraph.vertices graph: List V).length
    e' := {
            black := insert x e1.black
            gray := e.gray
            stack := e.stack
            sccs := (toFinset (x :: s)) :: e1.sccs
            -- sn := e1.sn
            num := fun (y: V) => if (x :: s).contains y then (DirectedGraph.vertices graph: List V).length else e1.num y
            num_clamp := by simp
                            intros y
                            rw [Finset.card_insert_of_not_mem]
                            any_goals assumption
                            split
                            any_goals tauto
                            all_goals sorry
            num_1 := by simp
                        intros y
                        split
                        all_goals sorry
            num_infty := by sorry
            valid_gray  := e.valid_gray
            valid_black := by intros _ h
                              simp at h
                              cases h
                              . subst x
                                tauto
                              . apply e1.valid_black; assumption
            disjoint_gb := by simp
                              constructor
                              . assumption
                              . have h := e1.disjoint_gb
                                rw [<- p₁.eq_gray] at h
                                simp [add_stack_incr] at h
                                tauto
            color₁ := by intros a b h₁ h₂
                         simp at h₂
                         simp
                         cases h₂ with
                         | inl h₂ => subst a
                                     rw [← DirectedGraph.edge_succ] at h₁
                                     specialize p₃ b h₁
                                     simp at p₃
                                     rw [← p₁.eq_gray] at p₃
                                     simp [add_stack_incr] at p₃
                                     tauto
                         | inr h₂ => have h := e1.color₁ a b h₁ h₂
                                     rw [← p₁.eq_gray] at h
                                     simp [add_stack_incr] at h
                                     tauto
            stack_finset := by sorry
            simplelist_stack := e.simplelist_stack
            decreasing_stack := by have h := e.decreasing_stack
                                   simp [Sorted] at h
                                   simp [Sorted]
                                   rw [<- List.Pairwise.iff_of_mem]
                                   . exact h
                                   . intros a b sa sb
                                     obtain ⟨h₇, _⟩ := h₇
                                     have ha := e1.simplelist_stack a
                                     have hb := e1.simplelist_stack b
                                     rw [<- h₇] at ha hb
                                     simp [num_occ] at ha hb
                                     split <;> split
                                     any_goals rw [mem_num_occ] at *
                                     any_goals rename_i h₁ h₂
                                     any_goals cases h₁
                                     any_goals cases h₂
                                     any_goals split at ha
                                     any_goals split at hb
                                     any_goals subst a
                                     any_goals subst b
                                     any_goals tauto
                                     any_goals omega
                                     all_goals sorry -- trival, use simplelist
            wf_stack₂ := by simp
                            intros a sa b sb h
                            obtain ⟨h₇, _⟩ := h₇
                            have := disjoint_s2_s3 a
                            have := disjoint_s2_s3 b
                            any_goals split at h
                            any_goals split at h
                            all_goals rename_i ha hb
                            any_goals cases ha
                            any_goals cases hb
                            any_goals subst a
                            any_goals subst b
                            any_goals tauto
                            any_goals apply e1.wf_stack₂
                            any_goals tauto
                            any_goals rw [<- h₇]
                            all_goals simp
                            all_goals tauto
            wf_stack₃ := by intros y hy
                            obtain ⟨z, hz, _, _⟩ := e.wf_stack₃ y hy
                            use z
                            repeat any_goals apply And.intro
                            any_goals tauto
                            any_goals simp
                            any_goals split
                            any_goals split
                            any_goals omega
                            any_goals apply num_bound
                            all_goals rename_i hz hy
                            . cases hz
                              . subst z
                                tauto
                              . exfalso
                                apply disjoint_s2_s3 z
                                any_goals assumption
                                apply gray_le_stack
                                assumption
                            . rw [← p₁.stack_num, ← p₁.stack_num]
                              any_goals simp [add_stack_incr]
                              any_goals tauto
                              . split <;> split
                                any_goals omega
                                all_goals tauto
                              . right
                                apply gray_le_stack
                                assumption
            sccs_in_black := by sorry
            sccs_disjoint := by intros
                                sorry
          }
    p₁ := {
            eq_gray := by simp
            sub_black := by simp
                            intros y hy
                            have h := p₁.sub_black
                            simp [add_stack_incr] at h
                            specialize h hy
                            simp
                            tauto
            sub_sccs := by simp
                           intros cc h
                           simp
                           right
                           apply p₁.sub_sccs
                           simp [add_stack_incr]
                           assumption
            stack_num := by simp
                            intros y h
                            rw [← p₁.stack_num]
                            any_goals simp [add_stack_incr]
                            any_goals split
                            any_goals split
                            any_goals subst y
                            any_goals tauto
                            all_goals rename_i h₁
                            obtain ⟨h₇, _⟩ := h₇
                            have h := e1.simplelist_stack y
                            rw [<- h₇] at h
                            simp [num_occ] at h
                            cases h₁
                            all_goals split at h
                            any_goals subst y
                            any_goals rw [mem_num_occ] at *
                            all_goals omega
            sub_stack := by simp
          }
    p₃ := by simp
    p₄ := by simp
    p₅ := by simp
    p₆ := by simp
  }
termination_by (Finset.card (((toFinset (DirectedGraph.vertices graph : List V)) \ (e.gray ∪ e.black)) : Finset V), 0)


def dfs [DirectedGraph V Graph]
        [BEq V] [LawfulBEq V] [DecidableEq V]
        (graph : Graph) (roots: List V) (e : Env V graph)
        (a₁ : roots ⊆ DirectedGraph.vertices graph)
        (a₂ : ∀ x, x ∈ roots -> access_to graph e.gray x)
        : Shuttle graph roots e := match roots with
| [] => {
           n := (DirectedGraph.vertices graph: List V).length
           e' := e
           p₁ := {
                    eq_gray := rfl
                    sub_black := by tauto
                    sub_sccs := by tauto
                    stack_num := by tauto
                    sub_stack := by use []
                                    simp_all
                 }
           p₃ := by intros; tauto
           p₄ := by intros; tauto
           p₅ := by intros; tauto
           p₆ := by intros _ _ h
                    obtain ⟨s2, h₁, ⟨x, h₃, _⟩⟩ := h
                    symm at h₁
                    rw [List.append_left_eq_self] at h₁
                    subst s2
                    tauto
        }
| x :: roots =>
  if dite: (e.num x) == -1 then
    have h : ¬ x ∈ e.gray ∪ e.black := by intros h
                                          simp at h
                                          rw [<- e.num_1] at h
                                          simp_all
    let ⟨n1, e1, p₁, p₃, p₄, p₅, pₕ⟩ := dfs3 graph x e (by tauto) (by apply a₂; tauto) (by intros _; apply h; simp_all) (by intros _; apply h; simp_all)
    have h₂ := by obtain ⟨h, _, _⟩ := p₁
                  rw [<- h]
                  intros
                  apply a₂
                  tauto

    have t₁ : e.gray ∪ e.black ⊆ toFinset (DirectedGraph.vertices graph) := by
      intros y h
      simp at h
      cases h <;> simp_all
      . apply e.valid_gray; assumption
      . apply e.valid_black; assumption

    have t₂ : e1.gray ∪ e1.black ⊆ toFinset (DirectedGraph.vertices graph) := by
      intros y h
      simp at h
      cases h <;> simp_all
      . apply e1.valid_gray; assumption
      . apply e1.valid_black; assumption

    have termination_proof : (toFinset (DirectedGraph.vertices graph) \ (e1.gray ∪ e1.black)).card < (toFinset (DirectedGraph.vertices graph) \ (e.gray ∪ e.black)).card := by
      rw [Finset.card_sdiff]
      rw [Finset.card_sdiff]
      any_goals assumption
      have t₁ := Finset.card_le_card t₁
      have t₂ := Finset.card_le_card t₂
      rw [Finset.card_union_of_disjoint e.disjoint_gb] at *
      rw [Finset.card_union_of_disjoint e1.disjoint_gb] at *
      obtain ⟨p₁, p₂, _⟩:= p₁
      rw [p₁] at t₁
      rw [p₁]
      have h : e.black ⊂ e1.black := by
        constructor
        . exact p₂
        . intros h₃
          specialize h₃ p₃
          apply h
          simp
          tauto
      have h := Finset.card_lt_card h
      simp_all
      omega

    let ⟨n2, e2, p₆, p₈, p₉, pₐ, p⟩ := dfs graph roots e1 (by tauto) h₂
    {
      n :=  min n1 n2
      e' := e2
      p₁ := subenv_trans p₁ p₆
      -- p₂ := p₇
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
               . cases (stack_or_scc x (by tauto)) with
                 | inl h => obtain ⟨_, _, _, p₆, _⟩ := p₆
                            specialize p₆ x h
                            rw [p₆] at p₄
                            simp_all
                 | inr h => obtain ⟨cc, h₁, h₂⟩ := h
                            obtain ⟨_, _, p₆, _, _⟩ := p₆
                            specialize p₆ h₂
                            have h : e2.num x = (DirectedGraph.vertices graph: List V).length := by
                              rw [e2.num_infty]
                              use cc
                            rw [h]
                            cases pₐ <;> try omega
                            rename_i h
                            obtain ⟨x, y, _, _, h, _⟩ := h
                            simp
                            right
                            rw [h]
                            apply num_bound
               . rename_i h
                 specialize p₉ y h
                 omega
      p₅ := by have h : min n1 n2 = n1 \/ min n1 n2 = n2 := by omega
               cases h
               all_goals rename_i h
               all_goals rw [h]
               all_goals cases pₐ
               any_goals tauto
               all_goals cases p₅
               any_goals tauto
               any_goals right
               . use x
                 constructor
                 . tauto
                 . apply subenv_num_of_reachable <;> assumption
               . use x
                 constructor
                 . tauto
                 . apply subenv_num_of_reachable <;> assumption
               . rename_i h _
                 obtain ⟨y, h⟩ := h
                 use y
                 tauto
               . rename_i h _
                 obtain ⟨y, h⟩ := h
                 use y
                 tauto
      p₆ := by obtain ⟨_, _, _, q₁, ⟨l₁, p₁, _⟩⟩ := p₁
               obtain ⟨_, _, _, q₂, ⟨l₂, p₆, _⟩⟩ := p₆
               intros y h h₁
               specialize p y
               specialize pₕ y
               obtain ⟨s2, h₁, ⟨x, h₂, h₃⟩⟩ := h₁
               rw [p₁, p₆] at *
               rw [<- List.append_assoc] at h₁
               have h₁ := List.append_inj_left' h₁ rfl
               subst s2
               specialize q₂ y (by simp; tauto)
               simp at h₂
               cases h₂
               . specialize p (by simp; tauto) ⟨l₂, (by tauto), x, (by assumption), (by assumption)⟩
                 omega
               . specialize pₕ (by tauto) ⟨l₁, (by tauto), x, (by assumption), (by assumption)⟩
                 rw [q₂] at *
                 simp_all
    }
  else
    let ⟨n2, e2, p₁, p₃, p₄, p₅, p₆⟩ := dfs graph roots e (by tauto) (by intros; apply a₂; tauto)
    have gray_or_black : x ∈ e.gray \/ x ∈ e.black := by
      rw [<- (e.num_1 x)]
      simp_all
    {
      n := min (e.num x) n2
      e' := e2
      p₁ := p₁
      p₃ := by intros _ h
               cases h
               . obtain ⟨h, _, _⟩ := p₁
                 rw [<- h]
                 simp
                 cases gray_or_black <;> tauto
               . apply p₃; assumption
      p₄ := by intros y h
               obtain ⟨_, _, p₇, p₈, _⟩ := p₁
               cases h <;> rename_i h
               . cases (stack_or_scc x gray_or_black) <;> rename_i h
                 . rw [(p₈ _ h)]
                   simp [*]
                 . have h₁ : e2.num x = (DirectedGraph.vertices graph: List V).length := by
                    rw [e2.num_infty]
                    tauto
                   rw [h₁]
                   have : e.num x ≤ (DirectedGraph.vertices graph: List V).length := by apply num_bound
                   omega
               . specialize p₄ y h
                 omega
      p₅ := by
              intros
              have h : n2 ≤ e.num x \/ e.num x < n2 := by omega
              cases h <;> simp [*] <;> cases p₅
              any_goals tauto
              all_goals have : e.num x ≤ n2 := by omega
              all_goals simp [*]
              all_goals have h : e.num x = (DirectedGraph.vertices graph: List V).length \/ ¬ e.num x = (DirectedGraph.vertices graph: List V).length := by tauto
              all_goals cases h
              any_goals tauto
              any_goals omega
              all_goals right; left; use x
              all_goals have h : x ∈ e.stack := by rw [<- stack_num]; simp_all
              all_goals have h : e.num x = e2.num x := by obtain ⟨_, _, _, p₁, _⟩ := p₁; apply p₁ _ h
              all_goals rename_i h₁ h₂ h₃ h₄ h₅
              all_goals rw [h] at *
              repeat any_goals apply And.intro
              any_goals tauto
              . obtain ⟨_, _, _, _, ⟨s, p₁, _⟩⟩ := p₁
                rw [p₁]
                simp
                tauto
              . have : e2.num x ≤ (DirectedGraph.vertices graph: List V).length := by apply num_bound
                simp_all
              . obtain ⟨_, _, _, _, ⟨s, p₁, _⟩⟩ := p₁
                rw [p₁]
                simp_all
      p₆ := by intros y hy h
               specialize p₆ y hy h
               omega
    }
termination_by (Finset.card (((toFinset (DirectedGraph.vertices graph : List V)) \ (e.gray ∪ e.black)) : Finset V), roots.length)

end
