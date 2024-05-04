import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto
import Kosaraju.ListHelper

open Rank

-- finite directed graph
class DirectedGraph (V : Type u)(Graph : Type v) where
  vertices : Graph -> List V
  edge      : Graph -> V -> V -> Prop
  succ      : Graph -> V -> List V
  transpose : Graph -> Graph
  edge_succ : ∀ g a b, b ∈ succ g a <-> edge g a b
  valid_edge : ∀ (g: Graph) (a b: V), edge g a b -> a ∈ vertices g /\ b ∈ vertices g
  transpose_transpose : ∀ g, (g |> transpose |> transpose) = g
  same_vertices : ∀ g, (g |> transpose |> vertices) = (g |> vertices)
  reverse_edge :∀ g a b, edge g a b <-> edge (g |> transpose) b a

theorem succ_valid [DirectedGraph V Graph] (g : Graph) (a: V) : a ∈ DirectedGraph.vertices g -> DirectedGraph.succ g a ⊆ DirectedGraph.vertices g := by
intro _ b h
rw [DirectedGraph.edge_succ] at *
have : a ∈ DirectedGraph.vertices g /\ b ∈ DirectedGraph.vertices g := by
  apply DirectedGraph.valid_edge
  assumption
tauto

inductive path [DirectedGraph V Graph] : Graph -> V -> List V -> V -> Prop
  | edge: ∀ (g: Graph) (a b: V), DirectedGraph.edge g a b -> path g a List.nil b
  | cons: ∀ (g: Graph) (a b c: V) (l: List V), DirectedGraph.edge g a b -> path g b l c -> path g a (List.cons b l) c

theorem path_trans [DirectedGraph V Graph] (g : Graph) (a b c: V) (lab lbc: List V) :
        path g a lab b -> path g b lbc c -> path g a (lab ++ List.cons b lbc) c := by
intro h
induction h
. simp; intros; constructor <;> assumption
. intros; simp_all; constructor <;> assumption

theorem path_decomposition [DirectedGraph V Graph] (g : Graph) (a b c: V) (lab lbc: List V) :
  path g a (lab ++ List.cons b lbc) c -> path g a lab b /\ path g b lbc c := by
revert a b c lbc
induction lab <;> simp_all <;> intros a b c lbc h <;> cases h
. tauto
. rename_i x xs induction_step h₂ h₃
  specialize induction_step x b c lbc h₃
  tauto

theorem reverse_path [DirectedGraph V Graph] (g : Graph) (a b : V) (l : List V) :
        path g a l b -> path (DirectedGraph.transpose V g) b l.reverse a :=  by
intro h
induction h <;> simp
. constructor; rw [<- DirectedGraph.reverse_edge]; assumption
. apply path_trans
  . assumption
  . constructor; rw [<- DirectedGraph.reverse_edge]; assumption

theorem path_valid [DirectedGraph V Graph] (g : Graph) (a b: V)(l : List V):
        path g a l b ->
        a ∈ DirectedGraph.vertices g /\
        b ∈ DirectedGraph.vertices g /\
        l ⊆ DirectedGraph.vertices g
:= by
intros h
induction h <;> simp_all
. apply DirectedGraph.valid_edge
  assumption
. rename_i a b _ _ h _ _
  have : a ∈ DirectedGraph.vertices g /\ b ∈ DirectedGraph.vertices g := by
    apply DirectedGraph.valid_edge
    assumption
  tauto

def reachable [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V]
              (g : Graph)
              (a b : V)
                : Prop := (∃ l, path g a l b)
                          \/
                          (
                            let v : List V := DirectedGraph.vertices g
                            a = b /\ a ∈ v
                          )

theorem reachable_trans [DirectedGraph V Graph]
                        [BEq V] [LawfulBEq V]
                        (g : Graph)
                        (x y z : V) :
reachable g x y -> reachable g y z -> reachable g x z := by
simp [reachable]
intros xy yz
cases xy <;> cases yz <;> try simp_all
all_goals rename_i h g
. left
  obtain ⟨lyz, _⟩ := g
  obtain ⟨lxy, _⟩ := h
  use (lxy ++ y :: lyz)
  apply path_trans <;> assumption
. right
  obtain ⟨_, _⟩ := g
  subst z
  assumption

theorem reachable_valid [DirectedGraph V Graph]
                        [BEq V] [LawfulBEq V]
                        (g : Graph) (a b: V):
reachable g a b -> a ∈ DirectedGraph.vertices g /\ b ∈ DirectedGraph.vertices g
:= by
intros h
cases h with
| inl h => obtain ⟨l, h⟩ := h
           have := path_valid g _ _ _ h
           tauto
| inr h => cases h
           subst a
           tauto

def in_same_scc [DirectedGraph V Graph]
                [BEq V] [LawfulBEq V]
                (g : Graph)
                (a b : V)
                : Prop := reachable g a b /\ reachable g b a

theorem same_scc_trans [DirectedGraph V Graph]
                       [BEq V] [LawfulBEq V]
                       (g : Graph)
                       (x y z : V) :
in_same_scc g x y -> in_same_scc g y z -> in_same_scc g x z := by
simp [in_same_scc]
intros
constructor
all_goals apply reachable_trans
all_goals assumption

def is_subscc [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V]
              (g : Graph)
              (s : Finset V) : Prop :=
    ∀ x y, x ∈ s -> y ∈ s -> in_same_scc g x y

def is_scc [DirectedGraph V Graph]
           [BEq V] [LawfulBEq V]
           (g : Graph)
           (s : Finset V) : Prop :=
    is_subscc g s /\ (∀ s', s ⊆ s' -> is_subscc g s' -> s' ⊆ s)

def no_black_to_white [DirectedGraph V Graph]
                      [BEq V] [LawfulBEq V]
                      (g : Graph)
                      (blacks grays: List V) : Prop :=
    ∀ a b, DirectedGraph.edge g a b -> a ∈ blacks -> b ∈ blacks \/ b ∈ grays

def access_from_set [DirectedGraph V Graph]
                    [BEq V] [LawfulBEq V]
                    (g : Graph)
                    (roots b: List V) : Prop :=
∀ z, z ∈ b -> ∃ x, x ∈ roots /\ reachable g x z

def wff_color [DirectedGraph V Graph]
              [BEq V] [LawfulBEq V]
              (g : Graph)
              (blacks grays: List V) : Prop :=
              (∀ x, x ∈ blacks -> x ∈ grays -> False) /\
              no_black_to_white g blacks grays /\
              simplelist blacks /\
              simplelist grays

def reachable_before [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V]
                     (g : Graph)
                     (x y: V) (s: List V) : Prop :=
  let v : List V := DirectedGraph.vertices g
  let max_int : Nat := v.length
  (∃ l, path g x l y /\
       let xl := List.cons x l
       xl ⊆ s /\
       (∀ z, z ∈ xl -> rank z s max_int <= rank y s max_int))
  \/
  (x = y /\ x ∈ s)


def reachable_before_same_scc [DirectedGraph V Graph]
                              [BEq V] [LawfulBEq V]
                              (g : Graph)
                              (s: List V) : Prop :=
   ∀ x y, x ∈ s -> y ∈ s -> reachable_before g x y s -> in_same_scc g x y

def no_edge_out_of [DirectedGraph V Graph]
                   [BEq V] [LawfulBEq V]
                   (g : Graph)
                   (s3 s1: List V) : Prop :=
    ∀ s2, s1 = s2 ++ s3 -> ∀ x y, x ∈ s3 -> y ∈ s2 -> DirectedGraph.edge g x y -> False

def no_path_out_of_in [DirectedGraph V Graph]
                      [BEq V] [LawfulBEq V]
                      (g : Graph)
                      (s3 s1: List V) : Prop :=
    ∀ x y l s2, s1 = s2 ++ s3 -> x ∈ s3 -> y ∈ s2 -> path g x l y -> l ⊆ s1 -> False

def paths_in_set [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V]
                 (g : Graph)
                 (cc: List V) : Prop :=
    ∀ x l y, x ∈ cc -> y ∈ cc -> path g x l y -> l ⊆ cc

def wff_stack_G1 [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V]
                 (g : Graph)
                 (blacks grays: List V) :=
    wff_color g blacks grays
    /\ blacks ⊆ (DirectedGraph.vertices g)
    /\ reachable_before_same_scc g blacks

def wff_stack_G2 [DirectedGraph V Graph]
                 [BEq V] [LawfulBEq V]
                 (g : Graph)
                 (blacks grays s: List V) :=
    wff_color g blacks grays
    /\ simplelist s
    /\ s ⊆ DirectedGraph.vertices g
    /\ reachable_before_same_scc (DirectedGraph.transpose V g) s

theorem reachable_before_shrink [DirectedGraph V Graph]
                                [BEq V] [LawfulBEq V]
                                (g : Graph) :
∀ (x y z: V) s, reachable_before g x y (List.cons z s) -> y ∈ s -> reachable_before g x y s := by
  simp [reachable_before, rank]
  intros x y z s h₁ h₂
  cases h₁ with
  | inl h₁ =>
    obtain ⟨lxy, h₁, ⟨h₃, h₆⟩, h₄, h₅⟩ := h₁
    left
    use lxy
    split at h₄ <;> split at h₄ <;> simp_all
    . rename_i h₆
      obtain ⟨h₆, _⟩ := h₆
      subst z
      revert h₄
      obtain v : List V := DirectedGraph.vertices g
      have : rank y s (List.length v) < List.length s := by apply rank_range; assumption
      omega
    . constructor
      any_goals constructor
      . simp [Subset, List.Subset] at *
        cases h₃ <;> simp_all
      . simp [Subset, List.Subset]
        intros a h₉
        cases h₆ h₉
        . cases h₃
          . simp_all
          . specialize h₅ z h₉
            split at h₅ <;> simp_all
            revert h₅
            obtain v : List V := DirectedGraph.vertices g
            have : rank y s (List.length v) < List.length s := by apply rank_range; assumption
            omega
        . assumption
      . intros a h₇
        specialize h₅ a h₇
        split at h₅ <;> simp_all
        revert h₅
        obtain v : List V := DirectedGraph.vertices g
        have : rank y s (List.length v) < List.length s := by apply rank_range; assumption
        omega
  | inr h₁ => obtain ⟨_, h₁⟩ := h₁
              subst y
              tauto


theorem reachable_before_extension [DirectedGraph V Graph]
                                   [BEq V] [LawfulBEq V]
                                   (g : Graph) :
  ∀ (x y z: V) s, x ∈ s -> y ∈ s -> reachable_before g x y s -> reachable_before g x y (List.cons z s) := by
  intros x y z s _ h₂
  simp [reachable_before, rank]
  intros h₁
  cases h₁ with
  | inl h₁ =>
      obtain ⟨lxy, h₁, ⟨h₂, h₃⟩, h₄⟩ := h₁
      left
      use lxy
      constructor <;> try constructor
      . assumption
      . simp [Subset, List.Subset] at *
        simp_all
      . split <;> split <;> simp_all
        . intros a _
          split <;> simp_all
          rename_i h₉ h₆
          obtain ⟨ h₆, h₈⟩ := h₆
          subst a
          specialize h₃ h₉
          tauto
  | inr h₁ => obtain ⟨_, _⟩ := h₁
              subst y
              tauto

theorem no_edge_out_of_cons [DirectedGraph V Graph]
                            [BEq V] [LawfulBEq V]
                            (g : Graph) :
    ∀ s1 s2 (x : V), no_edge_out_of g s1 s2 ->
                        (∀ z, z ∈ s1 -> DirectedGraph.edge g z x -> False) ->
                        no_edge_out_of g s1 (List.cons x s2) := by
    simp [no_edge_out_of]
    intros s1 s2 x h₁ h₂ s5 h₃ a b h₄ h₅ h₆
    cases s5 with simp_all
    | cons a5 s5 => obtain ⟨h₃, h₇⟩ := h₃
                    subst a5 s2
                    have := h₁ a b h₄
                    cases h₅ <;> simp_all

theorem path_cross_sets [DirectedGraph V Graph]
                        [BEq V] [LawfulBEq V]
                        (g : Graph) :
   ∀ l (x y : V) s1 s2 ,
   -- simplelist (s1 ++ s2) ->
   y ∈ s2 ->
   x ∈ s1 ->
   path g y l x ->
   l ⊆ (s1 ++ s2) ->
   ∃ (y' x' : V), y' ∈ s2 /\ x' ∈ s1 /\ DirectedGraph.edge g y' x' := by
   intro l
   induction l <;> intros x y s1 s2 h₁ h₂ h₃ h₄ <;> cases h₃
   . use y
     use x
   . rename_i b bs induction_step h₅ h₆
     have : b ∈ (s1 ++ s2) := by apply h₄; simp_all
     have h₈ : b ∈ s1 \/ b ∈ s2 := by rw [<- List.mem_append_eq]; simp_all
     cases h₈
     . use y
       use b
     . apply induction_step x b <;> try assumption
       . simp [Subset, List.Subset]
         intros
         rw [<- List.mem_append_eq]
         apply h₄
         simp_all

theorem no_edge_out_of_no_path_out_of_in [DirectedGraph V Graph]
                                        [BEq V] [LawfulBEq V]
                                        (g : Graph) :
    ∀ (s1 s2 : List V),
   --  simplelist s2 ->
    no_edge_out_of g s1 s2 -> no_path_out_of_in g s1 s2 := by
simp [no_edge_out_of, no_path_out_of_in]
intros s2 s3 h₁ x y l s1 h₂ h₃ h₄ h₅ h₆
subst s3
specialize h₁ s1
simp_all
have h₇ := path_cross_sets g l y x s1 s2 h₃ h₄ h₅ h₆
obtain ⟨x, y, h₂, h₃, h₄⟩ := h₇
apply h₁ x y h₂ h₃ h₄


theorem no_black_to_white_no_path [DirectedGraph V Graph]
                                [BEq V] [LawfulBEq V]
                                (g : Graph) :
∀ (b : List V),
no_black_to_white g b List.nil ->
∀ l x y, x ∈ b -> ¬ y ∈ b -> path g x l y -> False := by
simp [no_black_to_white]
intros b h₁ l
induction l <;> intros x y h₂ h₃ h₄ <;> cases h₄
. tauto
. rename_i z zs induction_step h₄ h₅
  have h₆ : z ∈ b \/ ¬ z ∈ b := by tauto
  cases h₆ <;> tauto

theorem no_black_to_white_in_the_middle [DirectedGraph V Graph]
                                        [BEq V] [LawfulBEq V]
                                        (g : Graph) :
∀ (b b' : List V), no_black_to_white g b  List.nil ->
                      no_black_to_white g b' List.nil ->
                      b ⊆ b' ->
                      paths_in_set g (List.filter (fun x => !b.contains x) b') := by
simp [paths_in_set]
intros b b' h₁ h₂ _ x l y h₄ h₅ h₆ z h₇
rw [List.mem_filter] at *
simp_all
have h₈ := List.append_of_mem h₇
obtain ⟨l₁, l₂, h₈⟩:= h₈
subst l
have ⟨h₈, h₉⟩ := path_decomposition g x z y l₁ l₂ h₆
have g₁ : z ∈ b' \/ ¬ z ∈ b' := by tauto
have g₂ : z ∈ b  \/ ¬ z ∈ b  := by tauto
obtain ⟨h₄, _⟩ := h₄
obtain ⟨_, h₇⟩ := h₅
cases g₁ <;> cases g₂ <;> constructor <;> try assumption
. intros g₃
  apply no_black_to_white_no_path g b h₁ l₂ z y g₃ h₇ h₉
. exfalso
  apply no_black_to_white_no_path g b' h₂ l₁ x z h₄ <;> assumption
. intros _
  apply no_black_to_white_no_path g b' h₂ l₁ x z h₄ <;> assumption
. exfalso
  apply no_black_to_white_no_path g b' h₂ l₁ x z h₄ <;> assumption


theorem wff_stack_white_extension [DirectedGraph V Graph]
                                  [BEq V] [LawfulBEq V]
                                  (g : Graph) :
∀ grey grey' (s s': List V),
  wff_stack_G1 g s grey ->
  wff_stack_G1 g (s' ++ s) grey'  ->
  grey ⊆ grey' ->
  ∀ x, x ∈ s' -> x ∈ s \/ x ∈ grey -> False := by
simp [wff_stack_G1, reachable_before_same_scc, wff_color]
intros grey _ s s' _ _ _ _ _ _ h₅ _ g₂ _ _ _ _ g₁ x _ g₄
cases g₄ with
| inl g₄ => specialize g₂ x
            rw [num_occ_concat] at g₂
            rw [mem_num_occ] at *
            simp_all
            omega
| inr g₄ => apply h₅ x
            . simp_all
            . apply g₁ g₄

theorem reachable_transpose [DirectedGraph V Graph]
                              [BEq V] [LawfulBEq V]
                              (g : Graph)
                              (a b : V) :
reachable (DirectedGraph.transpose V g) a b <-> reachable g b a := by
simp [reachable]
rw [DirectedGraph.same_vertices]
constructor <;> intros h
all_goals cases h
all_goals rename_i h
any_goals simp_all
. left
  obtain ⟨l, h⟩ := h
  use l.reverse
  have h := reverse_path _ _ _ _ h
  rw [DirectedGraph.transpose_transpose] at h
  assumption
. obtain ⟨_, _⟩ := h
  subst a
  tauto
. left
  obtain ⟨l, h⟩ := h
  use l.reverse
  have h := reverse_path _ _ _ _ h
  assumption
. obtain ⟨_, _⟩ := h
  subst a
  tauto


theorem in_same_scc_transpose [DirectedGraph V Graph]
                              [BEq V] [LawfulBEq V]
                              (g : Graph)
                              (a b : V) :
in_same_scc (DirectedGraph.transpose V g) a b <-> in_same_scc g a b := by
simp [in_same_scc]
repeat rw [reachable_transpose]
tauto

theorem is_subscc_transpose [DirectedGraph V Graph]
                            [BEq V] [LawfulBEq V]
                            (g : Graph)
                            (cc : Finset V) :
is_subscc g cc <-> is_subscc (DirectedGraph.transpose V g) cc := by
simp [is_subscc]
constructor
all_goals intros h x y
all_goals specialize h x y
all_goals rw [in_same_scc_transpose] at *
all_goals tauto

private theorem is_scc_transpose_inner [DirectedGraph V Graph]
                                       [BEq V] [LawfulBEq V]
                                       (g : Graph)
                                       (cc : Finset V) :
is_scc g cc -> is_scc (DirectedGraph.transpose V g) cc := by
simp [is_scc]
intros
rw [<- is_subscc_transpose]
simp_all
intros
rw [<- is_subscc_transpose] at *
tauto

theorem is_scc_transpose [DirectedGraph V Graph]
                          [BEq V] [LawfulBEq V]
                          (g : Graph)
                          (cc : Finset V) :
is_scc g cc <-> is_scc (DirectedGraph.transpose V g) cc := by
constructor
. exact is_scc_transpose_inner g cc
. intros h
  have h := is_scc_transpose_inner _ _ h
  rw [DirectedGraph.transpose_transpose] at h
  assumption

theorem scc_max [DirectedGraph V Graph]
                [BEq V] [LawfulBEq V] [DecidableEq V]
                (g : Graph) :
∀ (x y : V) (cc : Finset V), is_scc g cc -> x ∈ cc -> in_same_scc g x y -> y ∈ cc := by
intros x y cc h₁ h₃ h₄
simp [is_scc] at *
obtain ⟨h₁, h₂⟩ := h₁

have h₅ : ∀ z, z ∈ cc -> in_same_scc g z y := by
  intros z h₅
  specialize h₁ x z h₃ h₅
  apply same_scc_trans <;> try assumption
  simp [in_same_scc] at *; tauto

have : is_subscc g (insert y cc) := by
  intros a b h₆ h₇
  simp_all
  cases h₇ <;> cases h₆ <;> try tauto
  all_goals subst y
  . subst b
    specialize h₅ x h₃
    obtain ⟨h₅, _ ⟩ := h₅
    have := reachable_valid _ _ _ h₅
    constructor
    all_goals right
    all_goals simp_all
  . apply h₅; assumption
  . specialize h₅ b
    simp [in_same_scc] at *
    simp_all

apply h₂ (insert y cc) <;> simp_all

theorem disjoint_scc [DirectedGraph V Graph]
                     [BEq V] [LawfulBEq V] [DecidableEq V]
                     (g : Graph)
                     (cc1 cc2 : Finset V) :
Nonempty (cc1 ∩ cc2 : Finset V) ->
is_scc g cc1 ->
is_scc g cc2 ->
cc1 = cc2 := by
intros h₁ h₂ h₄
obtain ⟨x, h₁⟩ := h₁
apply Finset.Subset.antisymm
all_goals intros y h₉
all_goals have h₈ : x = y \/ ¬ x = y := by tauto
all_goals cases h₈
any_goals simp_all
all_goals apply scc_max g x y
any_goals assumption
any_goals tauto
. obtain ⟨h₂, _⟩ := h₂
  apply h₂ <;> tauto
. obtain ⟨h₄, _⟩ := h₄
  apply h₄ <;> tauto
