import Kosaraju.DirectedGraph
import ListHelper.Precede
import ListHelper.Split
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
let (s2, s3) := split x e1.stack
let infty : Int := (DirectedGraph.vertices graph: List V).length
if dite : n1 < e.gray.card + e.black.card then
  have p₅ : ∃ y ∈ DirectedGraph.succ graph x, ∃ z ∈ e1.stack, n1 = e1.num z ∧ reachable graph y z := by
    cases p₅ <;> try tauto
    subst n1
    have := sn_bound e
    omega
  have : x ∈ e1.gray := by
    obtain ⟨p₁, _ ⟩ := p₁
    rw [<- p₁]
    simp [add_stack_incr]
  have not_x_in_black : ¬ x ∈ e1.black := by
    intros _
    have hb : {x} ≤ e1.black := by simp; assumption
    have hg : {x} ≤ e1.gray := by simp; assumption
    have h := e1.disjoint_gb hg hb
    simp at h
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
  have h₈ : e1.num x = e.gray.card + e.black.card := by
    obtain ⟨_, _, _, p₁, _⟩ := p₁
    rw [<- p₁]
    all_goals simp [add_stack_incr]
  have h₇ : ∃ s, e1.stack = s ++ x :: e.stack ∧ ∀ y ∈ s, y ∈ e1.black := by
    have h := p₁.sub_stack
    simp [add_stack_incr] at h
    obtain ⟨s, h, h₁⟩ := h
    use s
  have h₆ : ∃ y ∈ e1.gray, ¬ y = x /\ e1.num y < e1.num x /\ in_same_scc graph x y := by
    obtain ⟨y, p₅, z, h, _, _⟩ := p₅
    use z
    simp [in_same_scc]
    -- have : e1.num y < e1.num x := by
    --   rw [<- h]
    --   omega
    simp_all
    --  z in e.stack
      --  z in e.gray ok
      --  z in e.black ???
    sorry
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
  rw [e1.wf_sccs₁] at h₁
  tauto
simplelist_stack := e1.simplelist_stack
wf_stack₁ := e1.wf_stack₁
wf_stack₂ := e1.wf_stack₂
wf_stack₃ := by intros y hy
                obtain ⟨z, _⟩ := e1.wf_stack₃ y hy
                use z
                have h₃ : x = z \/ ¬ x = z := by tauto
                cases h₃
                . subst z
                  exfalso
                  sorry
                . simp_all
                  tauto
wf_sccs₁ := by intros cc
               rw [e1.wf_sccs₁ cc]
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
                 sorry
wf_sccs₂ := e1.wf_sccs₂
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
                            obtain ⟨s, h₇⟩ := h₇
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
             apply p₆ <;> try assumption
             all_goals simp [add_stack_incr]
             any_goals tauto
             obtain ⟨s5, h₃, h₄⟩ := p₁.sub_stack
             simp [add_stack_incr] at h₃
             use s5
             constructor
             . tauto
             . use z
               rw [hs] at h₃
               have : s = s5 ++ [x] := by simp at h₃
               subst s
               simp_all
               have hxz : z = x \/ ¬ z = x := by tauto
               cases hxz
               . subst z
                 sorry
               . tauto   -- trival
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
            num_clamp := by sorry
            num_1 := by sorry
            num_infty := by sorry
            valid_gray  := by sorry
            valid_black :=  by sorry
            disjoint_gb := by sorry
            color₁ := by sorry
            stack_finset := sorry
            simplelist_stack := by sorry
            wf_stack₁ := by sorry
            wf_stack₂ := by sorry
            wf_stack₃ := by sorry
            wf_sccs₁ := by sorry
            wf_sccs₂ := by sorry
          }
    p₁ := {
            eq_gray := by simp
            sub_black := by simp
                            sorry
            sub_sccs := by simp
                           sorry
            stack_num := by simp
                            sorry
            sub_stack := by simp
                            sorry
          }
    p₃ := by sorry
    p₄ := by sorry
    p₅ := by sorry
    p₆ := by sorry
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
      -- p₂ := p₂
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
              all_goals have h : x ∈ e.stack := by rw [<- num_lmem]; simp_all
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
