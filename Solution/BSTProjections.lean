module

public import Challenge.Definitions

@[expose] public section

namespace Solution.BSTProjections

open SplayTree

/-! ## Private Structural, OrderDual, Projections, and Cascade Helpers -/

section Helpers

open BinaryTree

/-! ### 1. Unbounded BST helpers -/

private lemma isBSTAux_of_mem_bounds {α : Type} [LinearOrder α] {t : BinaryTree α}
    (h : t.IsBST) (lb ub : Option α)
    (hlo : ∀ x ∈ t, lb.elim True (· < x))
    (hhi : ∀ x ∈ t, ub.elim True (x < ·)) :
    t.IsBSTAux lb ub := by
  induction t generalizing lb ub with
  | nil => exact .nil lb ub
  | node k l r ihl ihr =>
    refine .node (hlo k .here) (hhi k .here) ?_ ?_
    · exact ihl (IsBST_left_of_IsBST h) lb (some k)
        (fun x hx => hlo x (.left hx))
        (fun _ hx => lt_of_IsBST_left l k r h hx)
    · exact ihr (IsBST_right_of_IsBST h) (some k) ub
        (fun _ hx => gt_of_IsBST_right l k r h hx)
        (fun x hx => hhi x (.right hx))

private lemma isBSTNil {α : Type} [LinearOrder α] : (BinaryTree.nil : BinaryTree α).IsBST :=
  .nil none none

private lemma isBST_node_iff {α : Type} [LinearOrder α] (k : α) (l r : BinaryTree α) :
    (BinaryTree.node k l r).IsBST ↔
      (∀ x ∈ l, x < k) ∧ (∀ x ∈ r, k < x) ∧ l.IsBST ∧ r.IsBST := by
  constructor
  · intro h
    exact ⟨fun _ hx => lt_of_IsBST_left l k r h hx,
      fun _ hx => gt_of_IsBST_right l k r h hx,
      IsBST_left_of_IsBST h, IsBST_right_of_IsBST h⟩
  · rintro ⟨hlt, hgt, hl, hr⟩
    refine IsBSTAux.node trivial trivial ?_ ?_
    · exact isBSTAux_of_mem_bounds hl none (some k) (by simp) hlt
    · exact isBSTAux_of_mem_bounds hr (some k) none hgt (by simp)

/-! ### 2. Mirror + OrderDual involution (`dualTree` / `undualTree`) -/

private def revMap {α β : Type} (f : α → β) : BinaryTree α → BinaryTree β
  | .nil => .nil
  | .node k l r => .node (f k) (revMap f r) (revMap f l)

private def dualTree {α : Type} (t : BinaryTree α) : BinaryTree αᵒᵈ :=
  revMap OrderDual.toDual t

private def undualTree {α : Type} (t : BinaryTree αᵒᵈ) : BinaryTree α :=
  revMap OrderDual.ofDual t

@[simp] private lemma dualTree_nil {α : Type} : dualTree (.nil : BinaryTree α) = .nil := rfl

@[simp] private lemma dualTree_node {α : Type} (k : α) (l r : BinaryTree α) :
    dualTree (.node k l r) = .node (OrderDual.toDual k) (dualTree r) (dualTree l) := rfl

@[simp] private lemma undualTree_nil {α : Type} : undualTree (.nil : BinaryTree αᵒᵈ) = .nil := rfl

@[simp] private lemma undualTree_node {α : Type} (k : αᵒᵈ) (l r : BinaryTree αᵒᵈ) :
    undualTree (.node k l r) = .node (OrderDual.ofDual k) (undualTree r) (undualTree l) := rfl

@[simp] private lemma undualTree_dualTree {α : Type} (t : BinaryTree α) :
    undualTree (dualTree t) = t := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr => simp [ihl, ihr]

@[simp] private lemma dualTree_undualTree {α : Type} (t : BinaryTree αᵒᵈ) :
    dualTree (undualTree t) = t := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr => simp [ihl, ihr]

@[simp] private lemma dualTree_eq_nil_iff {α : Type} (t : BinaryTree α) :
    dualTree t = .nil ↔ t = .nil := by
  cases t <;> simp

@[simp] private lemma mem_dualTree_iff {α : Type} (t : BinaryTree α) (v : α) :
    OrderDual.toDual v ∈ dualTree t ↔ v ∈ t := by
  induction t with
  | nil => simp
  | node k l r ihl ihr =>
    simp only [dualTree_node, mem_node_iff, OrderDual.toDual.injective.eq_iff, ihl, ihr]
    tauto

@[simp] private lemma mem_undualTree_iff {α : Type} (u : BinaryTree αᵒᵈ) (w : α) :
    w ∈ undualTree u ↔ OrderDual.toDual w ∈ u := by
  rw [← mem_dualTree_iff (undualTree u) w, dualTree_undualTree]

private lemma dualTree_isBST {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (dualTree t).IsBST := by
  induction t with
  | nil => exact isBSTNil
  | node k l r ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (isBST_node_iff k l r).mp ht
    rw [dualTree_node, isBST_node_iff]
    refine ⟨?_, ?_, ihr hr, ihl hl⟩
    · intro x hx
      have hxr : OrderDual.ofDual x ∈ r := (mem_dualTree_iff r (OrderDual.ofDual x)).mp hx
      exact hgt (OrderDual.ofDual x) hxr
    · intro x hx
      have hxl : OrderDual.ofDual x ∈ l := (mem_dualTree_iff l (OrderDual.ofDual x)).mp hx
      exact hlt (OrderDual.ofDual x) hxl

private lemma undualTree_isBST {α : Type} [LinearOrder α] {u : BinaryTree αᵒᵈ} (hu : u.IsBST) :
    (undualTree u).IsBST := by
  induction u with
  | nil => exact isBSTNil
  | node k l r ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (isBST_node_iff k l r).mp hu
    rw [undualTree_node, isBST_node_iff]
    refine ⟨?_, ?_, ihr hr, ihl hl⟩
    · intro w hw
      exact hgt (OrderDual.toDual w) ((mem_undualTree_iff r w).mp hw)
    · intro w hw
      exact hlt (OrderDual.toDual w) ((mem_undualTree_iff l w).mp hw)

private lemma lcaBST_dualTree {α : Type} [LinearOrder α] (t : BinaryTree α) (x y : α) :
    lcaBST (dualTree t) (OrderDual.toDual x) (OrderDual.toDual y) =
      (lcaBST t x y).map OrderDual.toDual := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [dualTree_node, lcaBST, OrderDual.toDual_lt_toDual]
    by_cases h1 : x < k ∧ y < k
    · have h2 : ¬(k < x ∧ k < y) := fun h => lt_asymm h1.1 h.1
      simp [h1, h2, ihl]
    · by_cases h2 : k < x ∧ k < y
      · simp [h1, h2, ihr]
      · simp [h1, h2]

private lemma isLCAClosed_dualTree_iff {α : Type} [LinearOrder α] (t : BinaryTree α) (S : Set α) :
    IsLCAClosed (dualTree t) (OrderDual.ofDual ⁻¹' S) ↔ IsLCAClosed t S := by
  constructor
  · intro hd x hx y hy hxS hyS z hz
    have hdx : OrderDual.toDual x ∈ dualTree t := (mem_dualTree_iff t x).mpr hx
    have hdy : OrderDual.toDual y ∈ dualTree t := (mem_dualTree_iff t y).mpr hy
    have hdz : lcaBST (dualTree t) (OrderDual.toDual x) (OrderDual.toDual y) =
        some (OrderDual.toDual z) := by
      rw [lcaBST_dualTree, hz]; rfl
    exact hd _ hdx _ hdy hxS hyS _ hdz
  · intro h x hx y hy hxS hyS z hz
    have hx' : OrderDual.ofDual x ∈ t := (mem_dualTree_iff t (OrderDual.ofDual x)).mp hx
    have hy' : OrderDual.ofDual y ∈ t := (mem_dualTree_iff t (OrderDual.ofDual y)).mp hy
    have hz' := lcaBST_dualTree t (OrderDual.ofDual x) (OrderDual.ofDual y)
    simp only [OrderDual.toDual_ofDual] at hz'
    rw [hz] at hz'
    cases h_lca : lcaBST t (OrderDual.ofDual x) (OrderDual.ofDual y) with
    | none => simp [h_lca] at hz'
    | some w =>
      simp only [h_lca, Option.map_some, Option.some.injEq] at hz'
      have hwS : w ∈ S := h _ hx' _ hy' hxS hyS w h_lca
      subst hz'
      exact hwS

/-! ### 3. `restrictTree` & `IsLCAClosed` basic lemmas -/

@[simp] private lemma restrictTree_nil {α : Type} (S : Set α) :
    restrictTree (.nil : BinaryTree α) S = .nil := rfl

private lemma restrictTree_node_mem {α : Type} {u : α} {A B : BinaryTree α} {S : Set α}
    (hu : u ∈ S) :
    restrictTree (.node u A B) S = .node u (restrictTree A S) (restrictTree B S) := by
  conv_lhs => unfold restrictTree
  simp [hu]

private lemma restrictTree_node_not_mem_right {α : Type} {u : α} {A B : BinaryTree α} {S : Set α}
    (hu : u ∉ S) (hB : ∃ b ∈ B, b ∈ S) :
    restrictTree (.node u A B) S = restrictTree B S := by
  conv_lhs => unfold restrictTree
  simp [hu, hB]

private lemma restrictTree_node_not_mem_not_right {α : Type} {u : α} {A B : BinaryTree α}
    {S : Set α} (hu : u ∉ S) (hB : ¬∃ b ∈ B, b ∈ S) :
    restrictTree (.node u A B) S = restrictTree A S := by
  conv_lhs => unfold restrictTree
  simp [hu, hB]

private lemma restrictTree_eq_nil_of_disjoint {α : Type} (t : BinaryTree α) (S : Set α)
    (h : ∀ x ∈ t, x ∉ S) : restrictTree t S = .nil := by
  induction t with
  | nil => rfl
  | node u A B ihA _ =>
    have hu : u ∉ S := h u .here
    have hB : ¬∃ b ∈ B, b ∈ S := by
      rintro ⟨b, hb, hbS⟩
      exact h b (.right hb) hbS
    rw [restrictTree_node_not_mem_not_right hu hB]
    exact ihA (fun a ha => h a (.left ha))

private lemma restrictTree_node_not_mem_right_disjoint {α : Type} {u : α} {A B : BinaryTree α}
    {S : Set α} (hu : u ∉ S) (hB : ∀ b ∈ B, b ∉ S) :
    restrictTree (.node u A B) S = restrictTree A S := by
  apply restrictTree_node_not_mem_not_right hu
  rintro ⟨b, hb, hbS⟩
  exact hB b hb hbS

private lemma restrictTree_node_not_mem_left_disjoint {α : Type} {u : α} {A B : BinaryTree α}
    {S : Set α} (hu : u ∉ S) (hA : ∀ a ∈ A, a ∉ S) :
    restrictTree (.node u A B) S = restrictTree B S := by
  by_cases hB : ∃ b ∈ B, b ∈ S
  · exact restrictTree_node_not_mem_right hu hB
  · rw [restrictTree_node_not_mem_not_right hu hB,
      restrictTree_eq_nil_of_disjoint A S hA,
      restrictTree_eq_nil_of_disjoint B S (fun b hb hbS => hB ⟨b, hb, hbS⟩)]

private lemma isLCAClosed_left {α : Type} [LinearOrder α] {u : α} {A B : BinaryTree α} {S : Set α}
    (ht : (BinaryTree.node u A B).IsBST) (hLCA : IsLCAClosed (.node u A B) S) :
    IsLCAClosed A S := by
  obtain ⟨hlt, _, _, _⟩ := (isBST_node_iff u A B).mp ht
  intro x hx y hy hxS hyS z hz
  have hxy : x < u ∧ y < u := ⟨hlt x hx, hlt y hy⟩
  have hz' : lcaBST (.node u A B) x y = some z := by simp [lcaBST, hxy, hz]
  exact hLCA x (.left hx) y (.left hy) hxS hyS z hz'

private lemma isLCAClosed_right {α : Type} [LinearOrder α] {u : α} {A B : BinaryTree α} {S : Set α}
    (ht : (BinaryTree.node u A B).IsBST) (hLCA : IsLCAClosed (.node u A B) S) :
    IsLCAClosed B S := by
  obtain ⟨_, hgt, _, _⟩ := (isBST_node_iff u A B).mp ht
  intro x hx y hy hxS hyS z hz
  have hxy : u < x ∧ u < y := ⟨hgt x hx, hgt y hy⟩
  have hnot : ¬(x < u ∧ y < u) := fun h => lt_asymm h.1 hxy.1
  have hz' : lcaBST (.node u A B) x y = some z := by simp [lcaBST, hnot, hxy, hz]
  exact hLCA x (.right hx) y (.right hy) hxS hyS z hz'

private lemma isLCAClosed_not_both_sides {α : Type} [LinearOrder α] {u : α} {A B : BinaryTree α}
    {S : Set α} (ht : (BinaryTree.node u A B).IsBST) (hLCA : IsLCAClosed (.node u A B) S)
    (hu : u ∉ S) {a b : α} (ha : a ∈ A) (haS : a ∈ S) (hb : b ∈ B) (hbS : b ∈ S) : False := by
  obtain ⟨hlt, hgt, _, _⟩ := (isBST_node_iff u A B).mp ht
  have hau : a < u := hlt a ha
  have hub : u < b := hgt b hb
  have h1 : ¬(a < u ∧ b < u) := fun h => lt_asymm hub h.2
  have h2 : ¬(u < a ∧ u < b) := fun h => lt_asymm hau h.1
  have hlca : lcaBST (.node u A B) a b = some u := by simp [lcaBST, h1, h2]
  exact hu (hLCA a (.left ha) b (.right hb) haS hbS u hlca)

private lemma mem_restrictTree_iff {α : Type} [LinearOrder α] (t : BinaryTree α) (S : Set α)
    (ht : t.IsBST) (hLCA : IsLCAClosed t S) (v : α) :
    v ∈ restrictTree t S ↔ v ∈ t ∧ v ∈ S := by
  induction t with
  | nil => simp
  | node u A B ihA ihB =>
    obtain ⟨_, _, hA, hB⟩ := (isBST_node_iff u A B).mp ht
    have hLCAA := isLCAClosed_left ht hLCA
    have hLCAB := isLCAClosed_right ht hLCA
    by_cases hu : u ∈ S
    · rw [restrictTree_node_mem hu, mem_node_iff, mem_node_iff, ihA hA hLCAA, ihB hB hLCAB]
      constructor
      · rintro (rfl | ⟨hv, hvS⟩ | ⟨hv, hvS⟩)
        · exact ⟨Or.inl rfl, hu⟩
        · exact ⟨Or.inr (Or.inl hv), hvS⟩
        · exact ⟨Or.inr (Or.inr hv), hvS⟩
      · rintro ⟨rfl | hv | hv, hvS⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hv, hvS⟩)
        · exact Or.inr (Or.inr ⟨hv, hvS⟩)
    · by_cases hBS : ∃ b ∈ B, b ∈ S
      · rw [restrictTree_node_not_mem_right hu hBS, ihB hB hLCAB, mem_node_iff]
        rcases hBS with ⟨b, hb, hbS⟩
        constructor
        · rintro ⟨hv, hvS⟩
          exact ⟨Or.inr (Or.inr hv), hvS⟩
        · rintro ⟨rfl | hv | hv, hvS⟩
          · exact absurd hvS hu
          · exact absurd (isLCAClosed_not_both_sides ht hLCA hu hv hvS hb hbS) id
          · exact ⟨hv, hvS⟩
      · rw [restrictTree_node_not_mem_not_right hu hBS, ihA hA hLCAA, mem_node_iff]
        constructor
        · rintro ⟨hv, hvS⟩
          exact ⟨Or.inr (Or.inl hv), hvS⟩
        · rintro ⟨rfl | hv | hv, hvS⟩
          · exact absurd hvS hu
          · exact ⟨hv, hvS⟩
          · exact absurd ⟨v, hv, hvS⟩ hBS

private lemma restrictTree_isBST {α : Type} [LinearOrder α] (t : BinaryTree α) (S : Set α)
    (ht : t.IsBST) (hLCA : IsLCAClosed t S) :
    (restrictTree t S).IsBST := by
  induction t with
  | nil => exact isBSTNil
  | node u A B ihA ihB =>
    obtain ⟨hlt, hgt, hA, hB⟩ := (isBST_node_iff u A B).mp ht
    have hLCAA := isLCAClosed_left ht hLCA
    have hLCAB := isLCAClosed_right ht hLCA
    by_cases hu : u ∈ S
    · rw [restrictTree_node_mem hu, isBST_node_iff]
      refine ⟨?_, ?_, ihA hA hLCAA, ihB hB hLCAB⟩
      · intro x hx
        exact hlt x ((mem_restrictTree_iff A S hA hLCAA x).mp hx).1
      · intro x hx
        exact hgt x ((mem_restrictTree_iff B S hB hLCAB x).mp hx).1
    · by_cases hBS : ∃ b ∈ B, b ∈ S
      · rw [restrictTree_node_not_mem_right hu hBS]
        exact ihB hB hLCAB
      · rw [restrictTree_node_not_mem_not_right hu hBS]
        exact ihA hA hLCAA

private lemma dualTree_restrictTree {α : Type} [LinearOrder α] (t : BinaryTree α) (S : Set α)
    (ht : t.IsBST) (hLCA : IsLCAClosed t S) :
    restrictTree (dualTree t) (OrderDual.ofDual ⁻¹' S) = dualTree (restrictTree t S) := by
  induction t with
  | nil => rfl
  | node u A B ihA ihB =>
    obtain ⟨_, _, hA, hB⟩ := (isBST_node_iff u A B).mp ht
    have hLCAA := isLCAClosed_left ht hLCA
    have hLCAB := isLCAClosed_right ht hLCA
    let Sod : Set αᵒᵈ := OrderDual.ofDual ⁻¹' S
    by_cases hu : u ∈ S
    · have hud : OrderDual.toDual u ∈ Sod := hu
      rw [dualTree_node, restrictTree_node_mem hud, restrictTree_node_mem hu, dualTree_node,
        ihA hA hLCAA, ihB hB hLCAB]
    · have hud : OrderDual.toDual u ∉ Sod := hu
      by_cases hBS : ∃ b ∈ B, b ∈ S
      · rcases hBS with ⟨b, hb, hbS⟩
        have hA_disj : ∀ a ∈ dualTree A, a ∉ Sod := by
          intro a ha haS
          have ha' : OrderDual.ofDual a ∈ A := (mem_dualTree_iff A (OrderDual.ofDual a)).mp ha
          exact isLCAClosed_not_both_sides ht hLCA hu ha' haS hb hbS
        rw [restrictTree_node_not_mem_right hu ⟨b, hb, hbS⟩, dualTree_node,
          restrictTree_node_not_mem_right_disjoint hud hA_disj]
        exact ihB hB hLCAB
      · have hB_disj : ∀ b ∈ dualTree B, b ∉ Sod := by
          intro b hb hbS
          have hb' : OrderDual.ofDual b ∈ B := (mem_dualTree_iff B (OrderDual.ofDual b)).mp hb
          exact hBS ⟨OrderDual.ofDual b, hb', hbS⟩
        rw [restrictTree_node_not_mem_not_right hu hBS, dualTree_node,
          restrictTree_node_not_mem_left_disjoint hud hB_disj]
        exact ihA hA hLCAA

/-! ### 4. Single rotations and Lemma 3.1(1) -/

private lemma mem_of_subtreeAtKey_node {α : Type} [LinearOrder α] {t L R : BinaryTree α} {p q : α}
    (h : subtreeAtKey t p = .node q L R) : p ∈ t ∧ q = p := by
  induction t with
  | nil => simp [subtreeAtKey] at h
  | node k l r ihl ihr =>
    simp only [subtreeAtKey] at h
    split_ifs at h with h1 h2
    · obtain ⟨hp, hq⟩ := ihl h
      exact ⟨.left hp, hq⟩
    · obtain ⟨hp, hq⟩ := ihr h
      exact ⟨.right hp, hq⟩
    · injection h with hqk _ _
      have hpk : p = k := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      exact ⟨hpk ▸ .here, hqk.symm.trans hpk.symm⟩

private lemma isRightRotEdge_iff {α : Type} [LinearOrder α] (t : BinaryTree α) (x p : α) :
    IsRightRotEdge t x p ↔ ∃ A B C, subtreeAtKey t p = .node p (.node x A B) C := by
  constructor
  · rintro ⟨A, B, C, _, h⟩; exact ⟨A, B, C, h⟩
  · rintro ⟨A, B, C, h⟩; exact ⟨A, B, C, (mem_of_subtreeAtKey_node h).1, h⟩

private lemma isLeftRotEdge_iff {α : Type} [LinearOrder α] (t : BinaryTree α) (x p : α) :
    IsLeftRotEdge t x p ↔ ∃ A B C, subtreeAtKey t p = .node p A (.node x B C) := by
  constructor
  · rintro ⟨A, B, C, _, h⟩; exact ⟨A, B, C, h⟩
  · rintro ⟨A, B, C, h⟩; exact ⟨A, B, C, (mem_of_subtreeAtKey_node h).1, h⟩

private lemma subtreeAtKey_dualTree {α : Type} [LinearOrder α] (t : BinaryTree α) (v : α) :
    subtreeAtKey (dualTree t) (OrderDual.toDual v) = dualTree (subtreeAtKey t v) := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [dualTree_node, subtreeAtKey, OrderDual.toDual_lt_toDual]
    by_cases h1 : v < k
    · have h2 : ¬(k < v) := lt_asymm h1
      simp [h1, h2, ihl]
    · by_cases h2 : k < v
      · simp [h1, h2, ihr]
      · simp [h1, h2]

private lemma isLeftRotEdge_iff_dual {α : Type} [LinearOrder α] (t : BinaryTree α) (x p : α) :
    IsLeftRotEdge t x p ↔ IsRightRotEdge (dualTree t) (OrderDual.toDual x) (OrderDual.toDual p) := by
  rw [isLeftRotEdge_iff, isRightRotEdge_iff]
  constructor
  · rintro ⟨A, B, C, h⟩
    refine ⟨dualTree C, dualTree B, dualTree A, ?_⟩
    rw [subtreeAtKey_dualTree, h]
    rfl
  · rintro ⟨A', B', C', h⟩
    refine ⟨undualTree C', undualTree B', undualTree A', ?_⟩
    have h' := congrArg undualTree h
    rw [subtreeAtKey_dualTree, undualTree_dualTree] at h'
    exact h'

private lemma mem_rotateRightEdge_iff {α : Type} [LinearOrder α] (t : BinaryTree α) (x p w : α) :
    w ∈ rotateRightEdge t x p ↔ w ∈ t := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [rotateRightEdge]
    split_ifs with h1 h2
    · simp [mem_node_iff, ihl]
    · simp [mem_node_iff, ihr]
    · rcases l with _ | ⟨lx, a, b⟩
      · rfl
      · dsimp only
        split_ifs with hlx
        · simp only [mem_node_iff]
          tauto
        · rfl

private lemma rotateRightEdge_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) (x p : α) : (rotateRightEdge t x p).IsBST := by
  induction t with
  | nil => exact isBSTNil
  | node k l r ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (isBST_node_iff k l r).mp ht
    simp only [rotateRightEdge]
    split_ifs with h1 h2
    · rw [isBST_node_iff]
      exact ⟨fun w hw => hlt w ((mem_rotateRightEdge_iff l x p w).mp hw), hgt, ihl hl, hr⟩
    · rw [isBST_node_iff]
      exact ⟨hlt, fun w hw => hgt w ((mem_rotateRightEdge_iff r x p w).mp hw), hl, ihr hr⟩
    · rcases l with _ | ⟨lx, a, b⟩
      · exact ht
      · dsimp only
        split_ifs with hlx
        · obtain ⟨ha_lt, hb_gt, ha_bst, hb_bst⟩ := (isBST_node_iff lx a b).mp hl
          have hlx_lt_k : lx < k := hlt lx .here
          have hb_lt_k : ∀ w ∈ b, w < k := fun w hw => hlt w (.right hw)
          have hkbr_bst : (BinaryTree.node k b r).IsBST :=
            (isBST_node_iff k b r).mpr ⟨hb_lt_k, hgt, hb_bst, hr⟩
          rw [isBST_node_iff]
          refine ⟨ha_lt, ?_, ha_bst, hkbr_bst⟩
          intro w hw
          rcases mem_node_iff.mp hw with rfl | hwb | hwr
          · exact hlx_lt_k
          · exact hb_gt w hwb
          · exact lt_trans hlx_lt_k (hgt w hwr)
        · exact ht

private lemma dualTree_rotateLeftEdge {α : Type} [LinearOrder α] (t : BinaryTree α) (x p : α) :
    dualTree (rotateLeftEdge t x p) =
      rotateRightEdge (dualTree t) (OrderDual.toDual x) (OrderDual.toDual p) := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [rotateLeftEdge, dualTree_node, rotateRightEdge, OrderDual.toDual_lt_toDual]
    by_cases h1 : p < k
    · have h2 : ¬(k < p) := lt_asymm h1
      simp [h1, h2, ihl]
    · by_cases h2 : k < p
      · simp [h1, h2, ihr]
      · simp only [h1, h2, ↓reduceIte]
        rcases r with _ | ⟨rx, b, c⟩
        · rfl
        · simp only [dualTree_node, OrderDual.toDual.injective.eq_iff]
          split_ifs <;> rfl

private lemma rotateLeftEdge_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) (x p : α) : (rotateLeftEdge t x p).IsBST := by
  have hd : (dualTree (rotateLeftEdge t x p)).IsBST := by
    rw [dualTree_rotateLeftEdge]
    exact rotateRightEdge_isBST (dualTree_isBST ht) _ _
  simpa using undualTree_isBST hd

private lemma lem_3_1_right {α : Type} [LinearOrder α]
    (t : BinaryTree α) (S : Set α) (ht : t.IsBST) (hLCA : IsLCAClosed t S)
    (x y : α) (hEdge : IsRightRotEdge t x y)
    (hLCA' : IsLCAClosed (rotateRightEdge t x y) S) :
    (x ∈ S ∧ y ∈ S →
      IsRightRotEdge (restrictTree t S) x y ∧
        restrictTree (rotateRightEdge t x y) S = rotateRightEdge (restrictTree t S) x y) ∧
    (¬(x ∈ S ∧ y ∈ S) →
      restrictTree (rotateRightEdge t x y) S = restrictTree t S) := by
  induction t with
  | nil =>
    rw [isRightRotEdge_iff] at hEdge
    rcases hEdge with ⟨_, _, _, h⟩
    simp [subtreeAtKey] at h
  | node k l r ihl ihr =>
    obtain ⟨_, _, hl, hr⟩ := (isBST_node_iff k l r).mp ht
    have hLCAl := isLCAClosed_left ht hLCA
    have hLCAr := isLCAClosed_right ht hLCA
    by_cases hyk : y < k
    · have hEdgel : IsRightRotEdge l x y := by
        rw [isRightRotEdge_iff] at hEdge ⊢
        simpa [subtreeAtKey, hyk] using hEdge
      have hrot : rotateRightEdge (.node k l r) x y = .node k (rotateRightEdge l x y) r := by
        simp [rotateRightEdge, hyk]
      rw [hrot] at hLCA' ⊢
      have ht'_bst : (BinaryTree.node k (rotateRightEdge l x y) r).IsBST := by
        rw [← hrot]; exact rotateRightEdge_isBST ht x y
      have hLCAl' : IsLCAClosed (rotateRightEdge l x y) S := isLCAClosed_left ht'_bst hLCA'
      obtain ⟨ih1, ih2⟩ := ihl hl hLCAl hEdgel hLCAl'
      have hyl : y ∈ l := hEdgel.choose_spec.choose_spec.choose_spec.1
      constructor
      · rintro ⟨hxS, hyS⟩
        obtain ⟨hEdge_lS, hEq_lS⟩ := ih1 ⟨hxS, hyS⟩
        by_cases hkS : k ∈ S
        · rw [restrictTree_node_mem hkS, restrictTree_node_mem hkS, hEq_lS]
          refine ⟨?_, ?_⟩
          · rw [isRightRotEdge_iff] at hEdge_lS ⊢
            simpa [subtreeAtKey, hyk] using hEdge_lS
          · simp [rotateRightEdge, hyk]
        · have hr_disj : ∀ b ∈ r, b ∉ S :=
            fun b hb hbS => isLCAClosed_not_both_sides ht hLCA hkS hyl hyS hb hbS
          rw [restrictTree_node_not_mem_right_disjoint hkS hr_disj,
            restrictTree_node_not_mem_right_disjoint hkS hr_disj]
          exact ⟨hEdge_lS, hEq_lS⟩
      · intro hnot
        have hEq_lS := ih2 hnot
        by_cases hkS : k ∈ S
        · rw [restrictTree_node_mem hkS, restrictTree_node_mem hkS, hEq_lS]
        · by_cases hrS : ∃ b ∈ r, b ∈ S
          · rw [restrictTree_node_not_mem_right hkS hrS,
              restrictTree_node_not_mem_right hkS hrS]
          · rw [restrictTree_node_not_mem_not_right hkS hrS,
              restrictTree_node_not_mem_not_right hkS hrS, hEq_lS]
    · by_cases hky : k < y
      · have hnot_yk : ¬(y < k) := lt_asymm hky
        have hEdger : IsRightRotEdge r x y := by
          rw [isRightRotEdge_iff] at hEdge ⊢
          simpa [subtreeAtKey, hnot_yk, hky] using hEdge
        have hrot : rotateRightEdge (.node k l r) x y = .node k l (rotateRightEdge r x y) := by
          simp [rotateRightEdge, hnot_yk, hky]
        rw [hrot] at hLCA' ⊢
        have ht'_bst : (BinaryTree.node k l (rotateRightEdge r x y)).IsBST := by
          rw [← hrot]; exact rotateRightEdge_isBST ht x y
        have hLCAr' : IsLCAClosed (rotateRightEdge r x y) S := isLCAClosed_right ht'_bst hLCA'
        obtain ⟨ih1, ih2⟩ := ihr hr hLCAr hEdger hLCAr'
        have hyr : y ∈ r := hEdger.choose_spec.choose_spec.choose_spec.1
        constructor
        · rintro ⟨hxS, hyS⟩
          obtain ⟨hEdge_rS, hEq_rS⟩ := ih1 ⟨hxS, hyS⟩
          by_cases hkS : k ∈ S
          · rw [restrictTree_node_mem hkS, restrictTree_node_mem hkS, hEq_rS]
            refine ⟨?_, ?_⟩
            · rw [isRightRotEdge_iff] at hEdge_rS ⊢
              simpa [subtreeAtKey, hnot_yk, hky] using hEdge_rS
            · simp [rotateRightEdge, hnot_yk, hky]
          · have hrS : ∃ b ∈ r, b ∈ S := ⟨y, hyr, hyS⟩
            have hr'S : ∃ b ∈ rotateRightEdge r x y, b ∈ S :=
              ⟨y, (mem_rotateRightEdge_iff r x y y).mpr hyr, hyS⟩
            rw [restrictTree_node_not_mem_right hkS hrS,
              restrictTree_node_not_mem_right hkS hr'S]
            exact ⟨hEdge_rS, hEq_rS⟩
        · intro hnot
          have hEq_rS := ih2 hnot
          by_cases hkS : k ∈ S
          · rw [restrictTree_node_mem hkS, restrictTree_node_mem hkS, hEq_rS]
          · have hr'_iff : (∃ b ∈ rotateRightEdge r x y, b ∈ S) ↔ (∃ b ∈ r, b ∈ S) := by
              constructor
              · rintro ⟨b, hb, hbS⟩; exact ⟨b, (mem_rotateRightEdge_iff r x y b).mp hb, hbS⟩
              · rintro ⟨b, hb, hbS⟩; exact ⟨b, (mem_rotateRightEdge_iff r x y b).mpr hb, hbS⟩
            by_cases hrS : ∃ b ∈ r, b ∈ S
            · rw [restrictTree_node_not_mem_right hkS hrS,
                restrictTree_node_not_mem_right hkS (hr'_iff.mpr hrS), hEq_rS]
            · rw [restrictTree_node_not_mem_not_right hkS hrS,
                restrictTree_node_not_mem_not_right hkS (mt hr'_iff.mp hrS)]
      · -- Base case: `y = k`
        have hy_eq : y = k := le_antisymm (not_lt.mp hky) (not_lt.mp hyk)
        subst hy_eq
        rw [isRightRotEdge_iff] at hEdge
        rcases hEdge with ⟨A, B, C, hsub⟩
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l r
        have hrot : rotateRightEdge (.node y (.node x A B) C) x y = .node x A (.node y B C) := by
          simp [rotateRightEdge]
        rw [hrot] at hLCA' ⊢
        have ht'_bst : (BinaryTree.node x A (.node y B C)).IsBST := by
          rw [← hrot]; exact rotateRightEdge_isBST ht x y
        constructor
        · rintro ⟨hxS, hyS⟩
          rw [restrictTree_node_mem hyS, restrictTree_node_mem hxS,
            restrictTree_node_mem hxS, restrictTree_node_mem hyS]
          refine ⟨?_, ?_⟩
          · rw [isRightRotEdge_iff]
            exact ⟨restrictTree A S, restrictTree B S, restrictTree C S, by simp [subtreeAtKey]⟩
          · simp [rotateRightEdge]
        · intro hnot
          by_cases hxS : x ∈ S
          · have hyS : y ∉ S := fun hyS => hnot ⟨hxS, hyS⟩
            have hC_disj : ∀ c ∈ C, c ∉ S :=
              fun c hc hcS => isLCAClosed_not_both_sides ht hLCA hyS .here hxS hc hcS
            rw [restrictTree_node_mem hxS,
              restrictTree_node_not_mem_right_disjoint hyS hC_disj,
              restrictTree_node_not_mem_right_disjoint hyS hC_disj,
              restrictTree_node_mem hxS]
          · by_cases hyS : y ∈ S
            · have hA_disj : ∀ a ∈ A, a ∉ S :=
                fun a ha haS => isLCAClosed_not_both_sides ht'_bst hLCA' hxS ha haS .here hyS
              rw [restrictTree_node_not_mem_left_disjoint hxS hA_disj,
                restrictTree_node_mem hyS,
                restrictTree_node_mem hyS,
                restrictTree_node_not_mem_left_disjoint hxS hA_disj]
            · by_cases hCS : ∃ c ∈ C, c ∈ S
              · rcases hCS with ⟨c, hc, hcS⟩
                have hA_disj : ∀ a ∈ A, a ∉ S :=
                  fun a ha haS => isLCAClosed_not_both_sides ht hLCA hyS (.left ha) haS hc hcS
                have hB_disj : ∀ b ∈ B, b ∉ S :=
                  fun b hb hbS => isLCAClosed_not_both_sides ht hLCA hyS (.right hb) hbS hc hcS
                rw [restrictTree_node_not_mem_left_disjoint hxS hA_disj,
                  restrictTree_node_not_mem_left_disjoint hyS hB_disj,
                  restrictTree_node_not_mem_right hyS ⟨c, hc, hcS⟩]
              · have hC_disj : ∀ c ∈ C, c ∉ S := fun c hc hcS => hCS ⟨c, hc, hcS⟩
                have hyBC_eq : restrictTree (.node y B C) S = restrictTree B S :=
                  restrictTree_node_not_mem_right_disjoint hyS hC_disj
                rw [restrictTree_node_not_mem_right_disjoint hyS hC_disj]
                by_cases hBS : ∃ b ∈ B, b ∈ S
                · rcases hBS with ⟨b, hb, hbS⟩
                  rw [restrictTree_node_not_mem_right hxS ⟨b, .left hb, hbS⟩, hyBC_eq,
                    restrictTree_node_not_mem_right hxS ⟨b, hb, hbS⟩]
                · have hyBC_not : ¬∃ d ∈ BinaryTree.node y B C, d ∈ S := by
                    rintro ⟨d, hd, hdS⟩
                    rcases mem_node_iff.mp hd with rfl | hdb | hdc
                    · exact hyS hdS
                    · exact hBS ⟨d, hdb, hdS⟩
                    · exact hC_disj d hdc hdS
                  rw [restrictTree_node_not_mem_not_right hxS hyBC_not,
                    restrictTree_node_not_mem_not_right hxS hBS]

/-! ### 5. Extremum splicing and Lemma 3.1(2) -/

private lemma minKey?_eq_none_iff {α : Type} (t : BinaryTree α) :
    t.minKey? = none ↔ t = .nil := by
  cases t with
  | nil => simp [minKey?]
  | node k l r =>
    simp only [minKey?, reduceCtorEq, iff_false]
    cases l.minKey? <;> simp

private lemma mem_of_minKey? {α : Type} {t : BinaryTree α} {m : α} (h : t.minKey? = some m) :
    m ∈ t := by
  induction t generalizing m with
  | nil => simp [minKey?] at h
  | node k l r ihl _ =>
    simp only [minKey?] at h
    cases hl : l.minKey? with
    | none =>
      rw [hl] at h
      injection h with hEq
      exact hEq ▸ .here
    | some m' =>
      rw [hl] at h
      injection h with hEq
      exact .left (ihl (hEq ▸ hl))

private lemma mem_spliceMin_sub {α : Type} {t : BinaryTree α} {v : α} (hv : v ∈ spliceMin t) :
    v ∈ t := by
  induction t with
  | nil => simp [spliceMin] at hv
  | node k l r ihl _ =>
    rcases l with _ | ⟨lk, ll, lr⟩
    · simp only [spliceMin] at hv
      exact .right hv
    · change v ∈ BinaryTree.node k (spliceMin (.node lk ll lr)) r at hv
      rw [mem_node_iff] at hv
      rcases hv with rfl | hvl | hvr
      · exact .here
      · exact .left (ihl hvl)
      · exact .right hvr

private lemma spliceMin_isBST {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (spliceMin t).IsBST := by
  induction t with
  | nil => exact isBSTNil
  | node k l r ihl _ =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (isBST_node_iff k l r).mp ht
    rcases l with _ | ⟨lk, ll, lr⟩
    · exact hr
    · simp only [spliceMin, isBST_node_iff]
      exact ⟨fun v hv => hlt v (mem_spliceMin_sub hv), hgt, ihl hl, hr⟩

private lemma lcaBST_spliceMin {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST)
    {x y : α} (hx : x ∈ spliceMin t) (hy : y ∈ spliceMin t) :
    lcaBST (spliceMin t) x y = lcaBST t x y := by
  induction t with
  | nil => simp [spliceMin] at hx
  | node k l r ihl _ =>
    obtain ⟨_, hgt, hl, _⟩ := (isBST_node_iff k l r).mp ht
    rcases l with _ | ⟨lk, ll, lr⟩
    · simp only [spliceMin] at hx hy ⊢
      have hkx : k < x := hgt x hx
      have hky : k < y := hgt y hy
      have hnot : ¬(x < k ∧ y < k) := fun h => lt_asymm hkx h.1
      simp [lcaBST, hnot, hkx, hky]
    · have hst : (BinaryTree.node k (spliceMin (.node lk ll lr)) r).IsBST := by
        simpa [spliceMin] using spliceMin_isBST ht
      obtain ⟨_, hgt', _, _⟩ := (isBST_node_iff k (spliceMin (.node lk ll lr)) r).mp hst
      simp only [spliceMin] at hx hy ⊢
      conv_lhs => unfold lcaBST
      conv_rhs => unfold lcaBST
      split_ifs with h1 h2
      · have hxl : x ∈ spliceMin (.node lk ll lr) := by
          rcases mem_node_iff.mp hx with rfl | hxl | hxr
          · exact absurd h1.1 (lt_irrefl _)
          · exact hxl
          · exact absurd h1.1 (not_lt.mpr (hgt' x hxr).le)
        have hyl : y ∈ spliceMin (.node lk ll lr) := by
          rcases mem_node_iff.mp hy with rfl | hyl | hyr
          · exact absurd h1.2 (lt_irrefl _)
          · exact hyl
          · exact absurd h1.2 (not_lt.mpr (hgt' y hyr).le)
        exact ihl hl hxl hyl
      · rfl
      · rfl

private lemma isLCAClosed_spliceMin {α : Type} [LinearOrder α] {t : BinaryTree α} (S : Set α)
    (ht : t.IsBST) (hLCA : IsLCAClosed t S) :
    IsLCAClosed (spliceMin t) S := by
  intro x hx y hy hxS hyS z hz
  rw [lcaBST_spliceMin ht hx hy] at hz
  exact hLCA x (mem_spliceMin_sub hx) y (mem_spliceMin_sub hy) hxS hyS z hz

private lemma lem_3_1_spliceMin_aux {α : Type} [LinearOrder α]
    (t : BinaryTree α) (S : Set α) (ht : t.IsBST) (hLCA : IsLCAClosed t S)
    (xMin : α) (hMin : t.minKey? = some xMin) :
    (xMin ∈ S →
      (restrictTree t S).minKey? = some xMin ∧
        restrictTree (spliceMin t) S = spliceMin (restrictTree t S)) ∧
    (xMin ∉ S → restrictTree (spliceMin t) S = restrictTree t S) := by
  induction t with
  | nil => simp [minKey?] at hMin
  | node k l r ihl _ =>
    obtain ⟨_, _, hl, _⟩ := (isBST_node_iff k l r).mp ht
    have hLCAl := isLCAClosed_left ht hLCA
    rcases l with _ | ⟨lk, ll, lr⟩
    · simp only [minKey?] at hMin
      injection hMin with hk
      subst hk
      simp only [spliceMin]
      constructor
      · intro hxS
        rw [restrictTree_node_mem hxS]
        simp [minKey?, spliceMin]
      · intro hxS
        rw [restrictTree_node_not_mem_left_disjoint hxS (by simp)]
    · have hl_ne : BinaryTree.node lk ll lr ≠ .nil := by simp
      have hl_min : (BinaryTree.node lk ll lr).minKey? = some xMin := by
        cases hlm : (BinaryTree.node lk ll lr).minKey? with
        | none => exact absurd ((minKey?_eq_none_iff _).mp hlm) hl_ne
        | some m =>
          have h1 : (BinaryTree.node k (.node lk ll lr) r).minKey? = some m := by
            change (match (BinaryTree.node lk ll lr).minKey? with
              | none => some k | some m => some m) = some m
            rw [hlm]
          rw [h1] at hMin
          exact hMin
      obtain ⟨ih1, ih2⟩ := ihl hl hLCAl hl_min
      have hxl : xMin ∈ BinaryTree.node lk ll lr := mem_of_minKey? hl_min
      simp only [spliceMin]
      constructor
      · intro hxS
        obtain ⟨hmin_lS, hEq_lS⟩ := ih1 hxS
        have hlS_ne : restrictTree (.node lk ll lr) S ≠ .nil := by
          intro hnil; simp [hnil, minKey?] at hmin_lS
        by_cases hkS : k ∈ S
        · rw [restrictTree_node_mem hkS, restrictTree_node_mem hkS, hEq_lS]
          rcases hrl : restrictTree (.node lk ll lr) S with _ | ⟨qk, ql, qr⟩
          · exact absurd hrl hlS_ne
          · rw [hrl] at hmin_lS
            refine ⟨?_, rfl⟩
            change (match (BinaryTree.node qk ql qr).minKey? with
              | none => some k | some m => some m) = some xMin
            rw [hmin_lS]
        · have hr_disj : ∀ b ∈ r, b ∉ S :=
            fun b hb hbS => isLCAClosed_not_both_sides ht hLCA hkS hxl hxS hb hbS
          rw [restrictTree_node_not_mem_right_disjoint hkS hr_disj,
            restrictTree_node_not_mem_right_disjoint hkS hr_disj]
          exact ⟨hmin_lS, hEq_lS⟩
      · intro hxS
        have hEq_lS := ih2 hxS
        by_cases hkS : k ∈ S
        · rw [restrictTree_node_mem hkS, restrictTree_node_mem hkS, hEq_lS]
        · by_cases hrS : ∃ b ∈ r, b ∈ S
          · rw [restrictTree_node_not_mem_right hkS hrS,
              restrictTree_node_not_mem_right hkS hrS]
          · rw [restrictTree_node_not_mem_not_right hkS hrS,
              restrictTree_node_not_mem_not_right hkS hrS, hEq_lS]

private lemma minKey?_dualTree {α : Type} (t : BinaryTree α) :
    (dualTree t).minKey? = t.maxKey?.map OrderDual.toDual := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    simp only [dualTree_node, minKey?, maxKey?, ihr]
    cases r.maxKey? <;> rfl

private lemma dualTree_spliceMax {α : Type} (t : BinaryTree α) :
    dualTree (spliceMax t) = spliceMin (dualTree t) := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    rcases r with _ | ⟨rk, rl, rr⟩
    · rfl
    · simp [spliceMax, spliceMin, ihr]

private lemma spliceMax_isBST {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (spliceMax t).IsBST := by
  have hd : (dualTree (spliceMax t)).IsBST := by
    rw [dualTree_spliceMax]
    exact spliceMin_isBST (dualTree_isBST ht)
  simpa using undualTree_isBST hd

/-! ### 6. Spine Decomposition & Cascade Equivalence Helpers (Lemma 3.2) -/

private def descendLeft {α : Type} : BinaryTree α → List (α × BinaryTree α) →
    BinaryTree α × List (α × BinaryTree α)
  | .nil, acc => (.nil, acc)
  | .node _ .nil r, acc => (r, acc)
  | .node k l@(.node _ _ _) r, acc => descendLeft l ((k, r) :: acc)

private def attachLeft {α : Type} : BinaryTree α → List (α × BinaryTree α) → BinaryTree α
  | c, [] => c
  | c, (k, r) :: rest => attachLeft (.node k c r) rest

private def splayLeft {α : Type} : BinaryTree α → List (α × BinaryTree α) → BinaryTree α
  | c, [] => c
  | c, [(k1, r1)] => .node k1 c r1
  | c, (k1, r1) :: (k2, r2) :: rest => splayLeft (.node k1 c (.node k2 r1 r2)) rest

private def toFrameL {α : Type} (p : α × BinaryTree α) : Frame α :=
  { dir := .L, key := p.1, sibling := p.2 }

private lemma descendLeft_attach {α : Type} (t : BinaryTree α) (k : α)
    (acc : List (α × BinaryTree α)) (hmin : t.minKey? = some k) :
    attachLeft (.node k .nil (descendLeft t acc).1) (descendLeft t acc).2 =
      attachLeft t acc := by
  induction t generalizing acc k with
  | nil => simp [minKey?] at hmin
  | node key l r ihl _ =>
    rcases l with _ | ⟨lk, ll, lr⟩
    · simp only [minKey?] at hmin
      injection hmin with hEq
      subst hEq
      simp [descendLeft]
    · have hl_ne : BinaryTree.node lk ll lr ≠ .nil := by simp
      cases hl : (BinaryTree.node lk ll lr).minKey? with
      | none => exact absurd ((minKey?_eq_none_iff _).mp hl) hl_ne
      | some m =>
        have h1 : (BinaryTree.node key (.node lk ll lr) r).minKey? = some m := by
          change (match (BinaryTree.node lk ll lr).minKey? with
            | none => some key | some m => some m) = some m
          rw [hl]
        rw [h1] at hmin
        injection hmin with hEq
        subst hEq
        simpa [descendLeft, attachLeft] using ihl m ((key, r) :: acc) hl

private lemma leftSpine_attachLeft {α : Type} (c : BinaryTree α) (path : List (α × BinaryTree α)) :
    leftSpine (attachLeft c path) = leftSpine c ++ path.map Prod.fst := by
  induction path generalizing c with
  | nil => simp [attachLeft]
  | cons hd rest ih =>
    rcases hd with ⟨v, R⟩
    simp [attachLeft, ih, leftSpine, List.append_assoc]

private lemma spliceMin_attachLeft {α : Type} (c : BinaryTree α) (path : List (α × BinaryTree α))
    (hc : c ≠ .nil) :
    spliceMin (attachLeft c path) = attachLeft (spliceMin c) path := by
  induction path generalizing c with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨v, R⟩
    simp only [attachLeft]
    rw [ih (.node v c R) (by simp)]
    rcases c with _ | ⟨ck, cl, cr⟩
    · exact absurd rfl hc
    · rfl

private lemma isBST_attachLeft_head {α : Type} [LinearOrder α] (c : BinaryTree α)
    (path : List (α × BinaryTree α)) (h : (attachLeft c path).IsBST) : c.IsBST := by
  induction path generalizing c with
  | nil => exact h
  | cons hd rest ih =>
    exact IsBST_left_of_IsBST (ih (.node hd.1 c hd.2) h)

private lemma rotateRightEdge_attachLeft {α : Type} [LinearOrder α] (c : BinaryTree α)
    (path : List (α × BinaryTree α)) (x p : α)
    (hbst : (attachLeft c path).IsBST) (hp : p ∈ c) :
    rotateRightEdge (attachLeft c path) x p = attachLeft (rotateRightEdge c x p) path := by
  induction path generalizing c with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨v, R⟩
    simp only [attachLeft]
    have hnode_bst : (BinaryTree.node v c R).IsBST := isBST_attachLeft_head (.node v c R) rest hbst
    have hpv : p < v := lt_of_IsBST_left c v R hnode_bst hp
    rw [ih (.node v c R) hbst (.left hp)]
    simp [rotateRightEdge, hpv]

private lemma splayLeft_eq_foldl_cascade {α : Type} [LinearOrder α] (c : BinaryTree α)
    (path : List (α × BinaryTree α)) (hbst : (attachLeft c path).IsBST) :
    splayLeft c path =
      (adjacentPairs (path.map Prod.fst)).foldl
        (fun acc p => rotateRightEdge acc p.1 p.2) (attachLeft c path) := by
  suffices ∀ (n : ℕ) (c : BinaryTree α) (path : List (α × BinaryTree α)),
      path.length ≤ n → (attachLeft c path).IsBST →
      splayLeft c path =
        (adjacentPairs (path.map Prod.fst)).foldl
          (fun acc p => rotateRightEdge acc p.1 p.2) (attachLeft c path) from
    this path.length c path le_rfl hbst
  intro n
  induction n with
  | zero =>
    intro c path hlen _
    rcases path with _ | _
    · rfl
    · simp at hlen
  | succ n ih =>
    intro c path hlen hbst
    rcases path with _ | ⟨⟨v1, R1⟩, _ | ⟨⟨v2, R2⟩, rest⟩⟩
    · rfl
    · rfl
    · have hrest : rest.length ≤ n := by simp at hlen; omega
      simp only [splayLeft, List.map_cons, adjacentPairs, List.foldl_cons, attachLeft]
      have hrot_eq :
          rotateRightEdge (attachLeft (.node v2 (.node v1 c R1) R2) rest) v1 v2 =
            attachLeft (.node v1 c (.node v2 R1 R2)) rest := by
        rw [rotateRightEdge_attachLeft (.node v2 (.node v1 c R1) R2) rest v1 v2 hbst .here]
        simp [rotateRightEdge]
      have hbst' : (attachLeft (.node v1 c (.node v2 R1 R2)) rest).IsBST := by
        rw [← hrot_eq]
        exact rotateRightEdge_isBST hbst v1 v2
      rw [hrot_eq]
      exact ih (.node v1 c (.node v2 R1 R2)) rest hrest hbst'

private lemma descend_go_minKey {α : Type} [LinearOrder α] (t : BinaryTree α) (k : α)
    (acc : List (α × BinaryTree α)) (ht : t.IsBST) (hmin : t.minKey? = some k) :
    descend.go k t (acc.map toFrameL) =
      (.node k .nil (descendLeft t acc).1, (descendLeft t acc).2.map toFrameL) := by
  induction t generalizing acc with
  | nil => simp [minKey?] at hmin
  | node key l r ihl _ =>
    obtain ⟨hlt, _, hl, _⟩ := (isBST_node_iff key l r).mp ht
    rcases l with _ | ⟨lk, ll, lr⟩
    · simp only [minKey?] at hmin
      injection hmin with hEq
      subst hEq
      simp [descend.go, descendLeft]
    · have hl_ne : BinaryTree.node lk ll lr ≠ .nil := by simp
      cases hlm : (BinaryTree.node lk ll lr).minKey? with
      | none => exact absurd ((minKey?_eq_none_iff _).mp hlm) hl_ne
      | some m =>
        have h1 : (BinaryTree.node key (.node lk ll lr) r).minKey? = some m := by
          change (match (BinaryTree.node lk ll lr).minKey? with
            | none => some key | some m => some m) = some m
          rw [hlm]
        rw [h1] at hmin
        injection hmin with hEq
        subst hEq
        have hm_lt : m < key := hlt m (mem_of_minKey? hlm)
        have hm_ne : m ≠ key := ne_of_lt hm_lt
        simp only [descend.go, hm_ne, hm_lt, ↓reduceIte, descendLeft]
        exact ihl ((key, r) :: acc) hl hlm

private lemma splayUp_toFrameL {α : Type} (k : α) (c : BinaryTree α)
    (path : List (α × BinaryTree α)) :
    splayUp (.node k .nil c) (path.map toFrameL) = .node k .nil (splayLeft c path) := by
  suffices ∀ (n : ℕ) (c : BinaryTree α) (path : List (α × BinaryTree α)),
      path.length ≤ n →
      splayUp (.node k .nil c) (path.map toFrameL) = .node k .nil (splayLeft c path) from
    this path.length c path le_rfl
  intro n
  induction n with
  | zero =>
    intro c path hlen
    rcases path with _ | _
    · rfl
    · simp at hlen
  | succ n ih =>
    intro c path hlen
    rcases path with _ | ⟨⟨v1, R1⟩, _ | ⟨⟨v2, R2⟩, rest⟩⟩
    · rfl
    · rfl
    · have hrest : rest.length ≤ n := by simp at hlen; omega
      simpa [splayUp, toFrameL, Frame.attach, Dir.bringUp, rotateRight, splayLeft] using
        ih (.node v1 c (.node v2 R1 R2)) rest hrest

private lemma adjacentPairs_length {α : Type} (xs : List α) :
    (adjacentPairs xs).length = xs.length / 2 := by
  suffices ∀ (n : ℕ) (xs : List α), xs.length ≤ n → (adjacentPairs xs).length = xs.length / 2 from
    this xs.length xs le_rfl
  intro n
  induction n with
  | zero =>
    intro xs hlen
    rcases xs with _ | _
    · simp [adjacentPairs]
    · simp at hlen
  | succ n ih =>
    intro xs hlen
    rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [adjacentPairs]
    · simp [adjacentPairs]
    · have hrest : rest.length ≤ n := by simp at hlen; omega
      simp only [adjacentPairs, List.length_cons]
      rw [ih rest hrest]
      omega

private lemma adjacentPairs_map {α β : Type} (f : α → β) (xs : List α) :
    adjacentPairs (xs.map f) = (adjacentPairs xs).map (Prod.map f f) := by
  suffices ∀ (n : ℕ) (xs : List α), xs.length ≤ n →
      adjacentPairs (xs.map f) = (adjacentPairs xs).map (Prod.map f f) from
    this xs.length xs le_rfl
  intro n
  induction n with
  | zero =>
    intro xs hlen
    rcases xs with _ | _
    · rfl
    · simp at hlen
  | succ n ih =>
    intro xs hlen
    rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · rfl
    · have hrest : rest.length ≤ n := by simp at hlen; omega
      simp [adjacentPairs, ih rest hrest]

private lemma leftSpine_dualTree {α : Type} (t : BinaryTree α) :
    leftSpine (dualTree t) = (rightSpineBottomUp t).map OrderDual.toDual := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    simp [leftSpine, rightSpineBottomUp, rightSpine, ihr]

private lemma popCascadePairs_dualTree {α : Type} (t : BinaryTree α) :
    popCascadePairs (dualTree t) =
      (ejectCascadePairs t).map (Prod.map OrderDual.toDual OrderDual.toDual) := by
  simp [popCascadePairs, ejectCascadePairs, leftSpine_dualTree, ← List.map_tail, adjacentPairs_map]

private lemma dualTree_ejectCascade {α : Type} [LinearOrder α] (t : BinaryTree α) :
    dualTree (ejectCascade t) = popCascade (dualTree t) := by
  unfold ejectCascade popCascade
  rw [popCascadePairs_dualTree, ← dualTree_spliceMax]
  generalize spliceMax t = init
  generalize ejectCascadePairs t = ps
  induction ps generalizing init with
  | nil => rfl
  | cons p rest ih =>
    simp [List.foldl_cons, ih, dualTree_rotateLeftEdge]

private def dualFrame {α : Type} (f : Frame α) : Frame αᵒᵈ :=
  { dir := f.dir.flip, key := OrderDual.toDual f.key, sibling := dualTree f.sibling }

private lemma descend_go_dualTree {α : Type} [LinearOrder α] (u : BinaryTree α) (q : α)
    (acc : List (Frame α)) :
    descend.go (OrderDual.toDual q) (dualTree u) (acc.map dualFrame) =
      (dualTree (descend.go q u acc).1, (descend.go q u acc).2.map dualFrame) := by
  induction u generalizing acc with
  | nil => rfl
  | node key l r ihl ihr =>
    simp only [dualTree_node, descend.go, OrderDual.toDual.injective.eq_iff,
      OrderDual.toDual_lt_toDual]
    by_cases hqk : q = key
    · subst hqk; simp
    · by_cases hqlt : q < key
      · have hnot : ¬(key < q) := lt_asymm hqlt
        simp only [hqk, hqlt, hnot, ↓reduceIte]
        exact ihl ({ dir := .L, key := key, sibling := r } :: acc)
      · have hklt : key < q := lt_of_le_of_ne (not_lt.mp hqlt) (Ne.symm hqk)
        simp only [hqk, hqlt, hklt, ↓reduceIte]
        exact ihr ({ dir := .R, key := key, sibling := l } :: acc)

private lemma dualTree_bringUp {α : Type} (d : Dir) (u : BinaryTree α) :
    dualTree (d.bringUp u) = d.flip.bringUp (dualTree u) := by
  rcases d with _ | _
  · rcases u with _ | ⟨y, _ | ⟨x, a, b⟩, c⟩ <;> rfl
  · rcases u with _ | ⟨x, a, _ | ⟨y, b, c⟩⟩ <;> rfl

private lemma dualTree_attach {α : Type} (c : BinaryTree α) (f : Frame α) :
    dualTree (f.attach c) = (dualFrame f).attach (dualTree c) := by
  rcases f with ⟨_ | _, k, sib⟩ <;> rfl

private lemma dualTree_applyChild_bringUp {α : Type} (d1 d2 : Dir) (u : BinaryTree α) :
    dualTree (applyChild d2 d1.bringUp u) =
      applyChild d2.flip d1.flip.bringUp (dualTree u) := by
  rcases d2 with _ | _ <;> rcases u with _ | ⟨k, l, r⟩ <;>
    simp [applyChild, dualTree_bringUp, Dir.flip]

private lemma dualTree_splayUp {α : Type} (c : BinaryTree α) (path : List (Frame α)) :
    dualTree (splayUp c path) = splayUp (dualTree c) (path.map dualFrame) := by
  suffices ∀ (n : ℕ) (c : BinaryTree α) (path : List (Frame α)),
      path.length ≤ n →
      dualTree (splayUp c path) = splayUp (dualTree c) (path.map dualFrame) from
    this path.length c path le_rfl
  intro n
  induction n with
  | zero =>
    intro c path hlen
    rcases path with _ | _
    · rfl
    · simp at hlen
  | succ n ih =>
    intro c path hlen
    rcases path with _ | ⟨f1, _ | ⟨f2, rest⟩⟩
    · rfl
    · simp [splayUp, dualTree_bringUp, dualTree_attach, dualFrame]
    · have hrest : rest.length ≤ n := by simp at hlen; omega
      have hdir_eq : (dualFrame f1).dir = f1.dir.flip := rfl
      have hdir2_eq : (dualFrame f2).dir = f2.dir.flip := rfl
      have hdir_iff : f1.dir.flip = f2.dir.flip ↔ f1.dir = f2.dir := by
        cases f1.dir <;> cases f2.dir <;> decide
      simp only [List.map_cons, splayUp, hdir_eq, hdir2_eq]
      by_cases hd : f1.dir = f2.dir
      · simp only [hd, ↓reduceIte]
        rw [ih _ rest hrest, dualTree_bringUp, dualTree_bringUp, dualTree_attach, dualTree_attach]
      · have hd' : ¬(f1.dir.flip = f2.dir.flip) := mt hdir_iff.mp hd
        simp only [hd, hd', ↓reduceIte]
        rw [ih _ rest hrest, dualTree_bringUp, dualTree_applyChild_bringUp,
          dualTree_attach, dualTree_attach]

private lemma dualTree_splay {α : Type} [LinearOrder α] (t : BinaryTree α) (k : α) :
    dualTree (splay t k) = splay (dualTree t) (OrderDual.toDual k) := by
  unfold splay descend
  have hd := descend_go_dualTree t k []
  simp only [List.map_nil] at hd
  rw [hd]
  rcases descend.go k t [] with ⟨_ | ⟨ck, cl, cr⟩, _ | ⟨f, rest⟩⟩
  · rfl
  · simp only [dualTree_nil, List.map_cons]
    rw [dualTree_splayUp, dualTree_attach, dualTree_nil]
  · rfl
  · simp only [List.map_cons]
    exact dualTree_splayUp (.node ck cl cr) (f :: rest)

private lemma splay_cost_dualTree {α : Type} [LinearOrder α] (t : BinaryTree α) (k : α) :
    splay.cost (dualTree t) (OrderDual.toDual k) = splay.cost t k := by
  unfold splay.cost descend
  have hd := descend_go_dualTree t k []
  simp only [List.map_nil] at hd
  rw [hd]
  rcases descend.go k t [] with ⟨_ | _, _ | _⟩ <;> simp

private lemma dualTree_eject {α : Type} [LinearOrder α] (t : BinaryTree α) :
    dualTree (SplayTree.eject t) = SplayTree.pop (dualTree t) := by
  unfold SplayTree.eject SplayTree.pop
  rw [minKey?_dualTree]
  cases t.maxKey? with
  | none => rfl
  | some k =>
    simp only [Option.map_some]
    rw [← dualTree_splay]
    rcases splay t k with _ | ⟨sk, sl, sr⟩ <;> rfl

private lemma ejectCost_eq_popCost_dualTree {α : Type} [LinearOrder α] (t : BinaryTree α) :
    ejectCost t = popCost (dualTree t) := by
  unfold ejectCost popCost
  rw [minKey?_dualTree]
  cases t.maxKey? with
  | none => rfl
  | some k =>
    simp only [Option.map_some]
    exact (splay_cost_dualTree t k).symm

private lemma lem_3_2_pop {α : Type} [LinearOrder α]
    (t : BinaryTree α) (ht : t.IsBST) (hne : t ≠ .nil) :
    let k := (leftSpine t).length - 1
    let r := k / 2
    (leftSpine t).length = k + 1 ∧
      (k = 2 * r ∨ k = 2 * r + 1) ∧
      (popCascadePairs t).length = r ∧
      popCost t = (k : ℝ) ∧
      SplayTree.pop t = popCascade t := by
  intro k r
  cases hmin : t.minKey? with
  | none => exact absurd ((minKey?_eq_none_iff t).mp hmin) hne
  | some v0 =>
    have hd := descend_go_minKey t v0 [] ht hmin
    simp only [List.map_nil] at hd
    set R0 := (descendLeft t []).1
    set path := (descendLeft t []).2
    have hatt : attachLeft (.node v0 .nil R0) path = t := by
      simpa [attachLeft] using descendLeft_attach t v0 [] hmin
    have hls : leftSpine t = v0 :: path.map Prod.fst := by
      rw [← hatt, leftSpine_attachLeft]
      simp [leftSpine]
    have hlen : (leftSpine t).length = path.length + 1 := by
      simp [hls]
    have hk_eq : k = path.length := by
      dsimp [k]; omega
    refine ⟨by omega, by dsimp [r]; omega, ?_, ?_, ?_⟩
    · simp [popCascadePairs, hls, adjacentPairs_length, r, hk_eq]
    · unfold popCost splay.cost descend
      rw [hmin]
      dsimp only
      rw [hd]
      simp [hk_eq]
    · have hpop : SplayTree.pop t = splayLeft R0 path := by
        unfold SplayTree.pop splay descend
        rw [hmin]
        dsimp only
        rw [hd]
        change (splayUp (.node v0 .nil R0) (path.map toFrameL)).right = splayLeft R0 path
        rw [splayUp_toFrameL]
        rfl
      have hsplice : spliceMin t = attachLeft R0 path := by
        rw [← hatt, spliceMin_attachLeft (.node v0 .nil R0) path (by simp)]
        rfl
      have hbst_R0 : (attachLeft R0 path).IsBST := by
        rw [← hsplice]
        exact spliceMin_isBST ht
      rw [hpop, splayLeft_eq_foldl_cascade R0 path hbst_R0]
      unfold popCascade popCascadePairs
      rw [hls, hsplice]
      rfl

end Helpers

/-! ## Exported Theorems -/

/-- **Lemma 3.1** (`lem:projection-stub`, BST Projection Under Rotations and Extremum Splicing):
`LCA`-closed subsets `S` induce valid BSTs `T|_S` on `V(T) ∩ S`, commute with single rotations
`[x, y]` whenever `S` remains `LCA`-closed in `T'`, and commute with splicing out `min V(T)` or
`max V(T)` while preserving `LCA`-closure. -/
theorem lem_3_1_bst_projection {α : Type} [LinearOrder α]
    (t : BinaryTree α) (S : Set α) (ht : t.IsBST) (hLCA : IsLCAClosed t S) :
    ((restrictTree t S).IsBST ∧ ∀ v : α, v ∈ restrictTree t S ↔ v ∈ t ∧ v ∈ S) ∧
    -- Part (1): single rotation `[x, y]`
    (∀ x y : α, IsSingleRotEdge t x y →
      let t' := rotateEdge t x y
      IsLCAClosed t' S →
        (x ∈ S ∧ y ∈ S →
          IsSingleRotEdge (restrictTree t S) x y ∧
            restrictTree t' S = rotateEdge (restrictTree t S) x y) ∧
        (¬ (x ∈ S ∧ y ∈ S) → restrictTree t' S = restrictTree t S)) ∧
    -- Part (2): extremum splicing
    (t ≠ .nil →
      (let tMin := spliceMin t
       IsLCAClosed tMin S ∧
         ∀ xMin : α, t.minKey? = some xMin →
           (xMin ∈ S →
             (restrictTree t S).minKey? = some xMin ∧
               restrictTree tMin S = spliceMin (restrictTree t S)) ∧
           (xMin ∉ S → restrictTree tMin S = restrictTree t S)) ∧
      (let tMax := spliceMax t
       IsLCAClosed tMax S ∧
         ∀ xMax : α, t.maxKey? = some xMax →
           (xMax ∈ S →
             (restrictTree t S).maxKey? = some xMax ∧
               restrictTree tMax S = spliceMax (restrictTree t S)) ∧
           (xMax ∉ S → restrictTree tMax S = restrictTree t S))) := by
  refine ⟨⟨restrictTree_isBST t S ht hLCA, mem_restrictTree_iff t S ht hLCA⟩, ?_, ?_⟩
  · intro x y hEdge t' hLCA'
    rcases hEdge with ⟨hxy, hRight⟩ | ⟨hyx, hLeft⟩
    · have ht'_eq : t' = rotateRightEdge t x y := by simp [t', rotateEdge, hxy]
      rw [ht'_eq] at hLCA' ⊢
      obtain ⟨h1, h2⟩ := lem_3_1_right t S ht hLCA x y hRight hLCA'
      refine ⟨fun hS => ?_, h2⟩
      obtain ⟨hEdgeS, hEqS⟩ := h1 hS
      exact ⟨Or.inl ⟨hxy, hEdgeS⟩, by simpa [rotateEdge, hxy] using hEqS⟩
    · have hnot_xy : ¬(x < y) := lt_asymm hyx
      have ht'_eq : t' = rotateLeftEdge t x y := by simp [t', rotateEdge, hnot_xy, hyx]
      rw [ht'_eq] at hLCA' ⊢
      let Sod : Set αᵒᵈ := OrderDual.ofDual ⁻¹' S
      have htd_bst : (dualTree t).IsBST := dualTree_isBST ht
      have htd_LCA : IsLCAClosed (dualTree t) Sod := (isLCAClosed_dualTree_iff t S).mpr hLCA
      have hRight_d : IsRightRotEdge (dualTree t) (OrderDual.toDual x) (OrderDual.toDual y) :=
        (isLeftRotEdge_iff_dual t x y).mp hLeft
      have htd'_LCA :
          IsLCAClosed (rotateRightEdge (dualTree t) (OrderDual.toDual x) (OrderDual.toDual y)) Sod := by
        rw [← dualTree_rotateLeftEdge]
        exact (isLCAClosed_dualTree_iff _ S).mpr hLCA'
      obtain ⟨h1, h2⟩ := lem_3_1_right (dualTree t) Sod htd_bst htd_LCA
        (OrderDual.toDual x) (OrderDual.toDual y) hRight_d htd'_LCA
      have ht'_bst : (rotateLeftEdge t x y).IsBST := rotateLeftEdge_isBST ht x y
      constructor
      · intro hS
        obtain ⟨hEdge_dS, hEq_dS⟩ := h1 hS
        rw [dualTree_restrictTree t S ht hLCA] at hEdge_dS hEq_dS
        rw [← dualTree_rotateLeftEdge,
          dualTree_restrictTree (rotateLeftEdge t x y) S ht'_bst hLCA',
          ← dualTree_rotateLeftEdge] at hEq_dS
        have hLeft_S : IsLeftRotEdge (restrictTree t S) x y :=
          (isLeftRotEdge_iff_dual (restrictTree t S) x y).mpr hEdge_dS
        have hEq_S : restrictTree (rotateLeftEdge t x y) S = rotateLeftEdge (restrictTree t S) x y := by
          have h := congrArg undualTree hEq_dS
          simpa using h
        exact ⟨Or.inr ⟨hyx, hLeft_S⟩, by simpa [rotateEdge, hnot_xy, hyx] using hEq_S⟩
      · intro hnotS
        have hEq_dS := h2 hnotS
        rw [dualTree_restrictTree t S ht hLCA,
          ← dualTree_rotateLeftEdge,
          dualTree_restrictTree (rotateLeftEdge t x y) S ht'_bst hLCA'] at hEq_dS
        have h := congrArg undualTree hEq_dS
        simpa using h
  · intro hne
    constructor
    · refine ⟨isLCAClosed_spliceMin S ht hLCA, ?_⟩
      intro xMin hMin
      exact lem_3_1_spliceMin_aux t S ht hLCA xMin hMin
    · let Sod : Set αᵒᵈ := OrderDual.ofDual ⁻¹' S
      have htd_bst : (dualTree t).IsBST := dualTree_isBST ht
      have htd_LCA : IsLCAClosed (dualTree t) Sod := (isLCAClosed_dualTree_iff t S).mpr hLCA
      have hLCA_max : IsLCAClosed (spliceMax t) S := by
        rw [← isLCAClosed_dualTree_iff, dualTree_spliceMax]
        exact isLCAClosed_spliceMin Sod htd_bst htd_LCA
      have htMax_bst : (spliceMax t).IsBST := spliceMax_isBST ht
      refine ⟨hLCA_max, ?_⟩
      intro xMax hMax
      have hMin_d : (dualTree t).minKey? = some (OrderDual.toDual xMax) := by
        rw [minKey?_dualTree, hMax]; rfl
      obtain ⟨h1, h2⟩ :=
        lem_3_1_spliceMin_aux (dualTree t) Sod htd_bst htd_LCA (OrderDual.toDual xMax) hMin_d
      constructor
      · intro hxS
        obtain ⟨hmin_dS, hEq_dS⟩ := h1 hxS
        rw [dualTree_restrictTree t S ht hLCA, minKey?_dualTree] at hmin_dS
        have hmax_S : (restrictTree t S).maxKey? = some xMax := by
          cases hm : (restrictTree t S).maxKey? with
          | none => simp [hm] at hmin_dS
          | some w =>
            simp only [hm, Option.map_some, Option.some.injEq,
              OrderDual.toDual.injective.eq_iff] at hmin_dS
            exact congrArg some hmin_dS
        rw [dualTree_restrictTree t S ht hLCA,
          ← dualTree_spliceMax,
          ← dualTree_spliceMax,
          dualTree_restrictTree (spliceMax t) S htMax_bst hLCA_max] at hEq_dS
        have hEq_S := congrArg undualTree hEq_dS
        simp only [undualTree_dualTree] at hEq_S
        exact ⟨hmax_S, hEq_S⟩
      · intro hxS
        have hEq_dS := h2 hxS
        rw [dualTree_restrictTree t S ht hLCA,
          ← dualTree_spliceMax,
          dualTree_restrictTree (spliceMax t) S htMax_bst hLCA_max] at hEq_dS
        have hEq_S := congrArg undualTree hEq_dS
        simpa using hEq_S

/-- **Lemma 3.2** (`lem:cascade-equiv`, Cascade Equivalence of `POP` and `EJECT`):
On any non-empty BST `t`, `POP` performs `k = |LS(t)| - 1` single rotations and produces the
exact same BST as `popCascade t` (splicing out `v_0 = min V(t)` and executing `⌊k / 2⌋`
vertex-disjoint right single rotations `[v_{2j-1}, v_{2j}]`), and symmetrically for `EJECT` and
`ejectCascade t`. -/
theorem lem_3_2_cascade_equiv {α : Type} [LinearOrder α]
    (t : BinaryTree α) (ht : t.IsBST) (hne : t ≠ .nil) :
    (let k := (leftSpine t).length - 1
     let r := k / 2
     (leftSpine t).length = k + 1 ∧
       (k = 2 * r ∨ k = 2 * r + 1) ∧
       (popCascadePairs t).length = r ∧
       popCost t = (k : ℝ) ∧
       SplayTree.pop t = popCascade t) ∧
    (let k' := (rightSpineBottomUp t).length - 1
     let r' := k' / 2
     (rightSpineBottomUp t).length = k' + 1 ∧
       (k' = 2 * r' ∨ k' = 2 * r' + 1) ∧
       (ejectCascadePairs t).length = r' ∧
       ejectCost t = (k' : ℝ) ∧
       SplayTree.eject t = ejectCascade t) := by
  refine ⟨lem_3_2_pop t ht hne, ?_⟩
  have htd_bst : (dualTree t).IsBST := dualTree_isBST ht
  have htd_ne : dualTree t ≠ .nil := mt (dualTree_eq_nil_iff t).mp hne
  obtain ⟨h1, h2, h3, h4, h5⟩ := lem_3_2_pop (dualTree t) htd_bst htd_ne
  have hls_len : (leftSpine (dualTree t)).length = (rightSpineBottomUp t).length := by
    simp [leftSpine_dualTree]
  have hpairs_len : (popCascadePairs (dualTree t)).length = (ejectCascadePairs t).length := by
    simp [popCascadePairs_dualTree]
  rw [hls_len] at h1 h2 h3 h4
  rw [hpairs_len] at h3
  rw [← ejectCost_eq_popCost_dualTree] at h4
  rw [← dualTree_eject, ← dualTree_ejectCascade] at h5
  have h5' : SplayTree.eject t = ejectCascade t := by
    have h := congrArg undualTree h5
    simpa using h
  exact ⟨h1, h2, h3, h4, h5'⟩

end Solution.BSTProjections
