module

public import Challenge.Definitions
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace Solution.TamariPreorder

open SplayTree
open BinaryTree

/-! ## 1. Basic BST, `toKeyList`, `keyFinset`, `maxKey?`, and `IsRangeBST` Lemmas -/

private theorem mem_keyFinset_iff {α : Type} [DecidableEq α] {t : BinaryTree α} {x : α} :
    x ∈ keyFinset t ↔ x ∈ t := by
  induction t with
  | nil => simp [keyFinset]
  | node k l r ihl ihr =>
    simp only [keyFinset, Finset.mem_insert, Finset.mem_union, ihl, ihr, mem_node_iff]

private theorem toKeyList_nodup_of_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) : t.toKeyList.Nodup :=
  ((IsBST_iff_toKeyList_sorted t).mp ht).imp ne_of_lt

private theorem toFinset_toKeyList_eq_keyFinset {α : Type} [DecidableEq α] (t : BinaryTree α) :
    t.toKeyList.toFinset = keyFinset t := by
  ext x
  simp [mem_keyFinset_iff, mem_iff_mem_toKeyList]

private theorem card_keyFinset_of_isBST {α : Type} [LinearOrder α] [DecidableEq α]
    {t : BinaryTree α} (ht : t.IsBST) : (keyFinset t).card = t.num_nodes := by
  rw [← toFinset_toKeyList_eq_keyFinset, List.toFinset_card_of_nodup (toKeyList_nodup_of_isBST ht),
    num_nodes_eq_length_toKeyList]

private theorem eq_of_pairwise_lt_of_mem_iff {α : Type} [LinearOrder α] {l₁ l₂ : List α}
    (h₁ : l₁.Pairwise (· < ·)) (h₂ : l₂.Pairwise (· < ·))
    (hm : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b bs =>
      exfalso
      exact List.not_mem_nil ((hm b).mpr List.mem_cons_self)
  | cons a as ih =>
    cases l₂ with
    | nil =>
      exfalso
      exact List.not_mem_nil ((hm a).mp List.mem_cons_self)
    | cons b bs =>
      rw [List.pairwise_cons] at h₁ h₂
      have hab : a = b := by
        have ha : a ∈ b :: bs := (hm a).mp List.mem_cons_self
        have hb : b ∈ a :: as := (hm b).mpr List.mem_cons_self
        simp only [List.mem_cons] at ha hb
        rcases ha with rfl | ha'
        · rfl
        · rcases hb with rfl | hb'
          · rfl
          · exact absurd (lt_trans (h₁.1 b hb') (h₂.1 a ha')) (lt_irrefl a)
      subst hab
      congr 1
      apply ih h₁.2 h₂.2
      intro x
      by_cases hxa : x = a
      · subst hxa
        exact ⟨fun hx => absurd (h₁.1 x hx) (lt_irrefl x),
          fun hx => absurd (h₂.1 x hx) (lt_irrefl x)⟩
      · have h := hm x
        simpa [List.mem_cons, hxa] using h

private theorem pairwise_lt_range' (a n : ℕ) : (List.range' a n).Pairwise (· < ·) := by
  induction n generalizing a with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    change (a :: List.range' (a + 1) n).Pairwise (· < ·)
    rw [List.pairwise_cons]
    refine ⟨fun x hx => ?_, ih (a + 1)⟩
    rw [List.mem_range'] at hx
    rcases hx with ⟨i, _, rfl⟩
    omega

/-- Contiguous range BST invariant: `t` stores `{a, ..., a + t.num_nodes - 1}` in BST order. -/
private def IsRangeBST (a : ℕ) : BinaryTree ℕ → Prop
  | .nil => True
  | .node k l r => k = a + l.num_nodes ∧ IsRangeBST a l ∧ IsRangeBST (k + 1) r

private theorem isRangeBST_iff_toKeyList {a : ℕ} {t : BinaryTree ℕ} :
    IsRangeBST a t ↔ t.toKeyList = List.range' a t.num_nodes := by
  induction t generalizing a with
  | nil => simp [IsRangeBST]
  | node k l r ihl ihr =>
    have hrng :
        List.range' a (1 + l.num_nodes + r.num_nodes) =
          List.range' a l.num_nodes ++ (a + l.num_nodes) ::
            List.range' (a + l.num_nodes + 1) r.num_nodes := by
      have h1 : 1 + l.num_nodes + r.num_nodes = l.num_nodes + (r.num_nodes + 1) := by omega
      rw [h1, ← @List.range'_append a l.num_nodes (r.num_nodes + 1) 1]
      have h2 : a + 1 * l.num_nodes = a + l.num_nodes := by omega
      rw [h2]
      rfl
    constructor
    · rintro ⟨hk, hl, hr⟩
      simp only [toKeyList_node, num_nodes_node, List.append_assoc, List.singleton_append]
      rw [ihl.mp hl, ihr.mp hr, hrng, hk]
    · intro h
      simp only [toKeyList_node, num_nodes_node, List.append_assoc, List.singleton_append] at h
      rw [hrng] at h
      have hlen : l.toKeyList.length = (List.range' a l.num_nodes).length := by
        rw [← num_nodes_eq_length_toKeyList, List.length_range']
      obtain ⟨hl_eq, hkr⟩ := List.append_inj h hlen
      injection hkr with hk hr_eq
      exact ⟨hk, ihl.mpr hl_eq, ihr.mpr (hk ▸ hr_eq)⟩

private theorem isBST_of_isRangeBST {a : ℕ} {t : BinaryTree ℕ} (h : IsRangeBST a t) :
    t.IsBST := by
  rw [IsBST_iff_toKeyList_sorted, isRangeBST_iff_toKeyList.mp h]
  exact pairwise_lt_range' a t.num_nodes

private theorem mem_of_isRangeBST {a : ℕ} {t : BinaryTree ℕ} (h : IsRangeBST a t) (x : ℕ) :
    x ∈ t ↔ a ≤ x ∧ x < a + t.num_nodes := by
  rw [mem_iff_mem_toKeyList, isRangeBST_iff_toKeyList.mp h, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨x - a, by omega, by omega⟩

private theorem isRangeBST_of_keyFinset_Icc {n : ℕ} {t : BinaryTree ℕ}
    (ht : t.IsBST) (hk : keyFinset t = Finset.Icc 1 n) :
    IsRangeBST 1 t ∧ t.num_nodes = n := by
  have heq : t.toKeyList = List.range' 1 n := by
    apply eq_of_pairwise_lt_of_mem_iff ((IsBST_iff_toKeyList_sorted t).mp ht) (pairwise_lt_range' 1 n)
    intro x
    rw [← mem_iff_mem_toKeyList, ← mem_keyFinset_iff, hk, Finset.mem_Icc, List.mem_range']
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega
  have hn : t.num_nodes = n := by
    rw [num_nodes_eq_length_toKeyList, heq, List.length_range']
  exact ⟨isRangeBST_iff_toKeyList.mpr (hn ▸ heq), hn⟩

private theorem maxKey?_eq_getLast?_toKeyList {α : Type} (t : BinaryTree α) :
    t.maxKey? = t.toKeyList.getLast? := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    simp only [BinaryTree.maxKey?, toKeyList_node, List.append_assoc, List.singleton_append]
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil k r.toKeyList)]
    cases hlast : r.toKeyList.getLast? with
    | none =>
      have hrnil : r.toKeyList = [] := List.getLast?_eq_none_iff.mp hlast
      rw [hlast] at ihr
      simp [ihr, hrnil]
    | some m =>
      rw [hlast] at ihr
      simp [ihr, List.getLast?_cons, hlast]

private theorem maxKey?_of_toKeyList_eq {α : Type} {t₁ t₂ : BinaryTree α}
    (h : t₁.toKeyList = t₂.toKeyList) : t₁.maxKey? = t₂.maxKey? := by
  rw [maxKey?_eq_getLast?_toKeyList, maxKey?_eq_getLast?_toKeyList, h]

private theorem maxKey?_isBST_spec {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (t = .nil ∧ t.maxKey? = none) ∨
      ∃ m ∈ t, t.maxKey? = some m ∧ ∀ x ∈ t, x ≤ m := by
  induction t with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | node k l r _ ihr =>
    right
    rcases ihr (IsBST_right_of_IsBST ht) with ⟨rfl, _⟩ | ⟨m, hmr, hmax, hub⟩
    · refine ⟨k, .here, rfl, fun x hx => ?_⟩
      rcases mem_node_iff.mp hx with rfl | hxl | hxr
      · exact le_rfl
      · exact le_of_lt (lt_of_IsBST_left l k .nil ht hxl)
      · cases hxr
    · refine ⟨m, .right hmr, ?_, fun x hx => ?_⟩
      · simp [BinaryTree.maxKey?, hmax]
      · have hkm : k < m := gt_of_IsBST_right l k r ht hmr
        rcases mem_node_iff.mp hx with rfl | hxl | hxr
        · exact le_of_lt hkm
        · exact le_of_lt (lt_trans (lt_of_IsBST_left l k r ht hxl) hkm)
        · exact hub x hxr

private theorem maxKey?_eq_some_iff_of_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) (m : α) :
    t.maxKey? = some m ↔ m ∈ t ∧ ∀ x ∈ t, x ≤ m := by
  rcases maxKey?_isBST_spec ht with ⟨rfl, hnone⟩ | ⟨m', hm', hmax, hub⟩
  · simp [hnone]
  · rw [hmax]
    constructor
    · intro h
      injection h with h
      subst h
      exact ⟨hm', hub⟩
    · rintro ⟨hm_in, hub'⟩
      exact congrArg some (le_antisymm (hub' m' hm') (hub m hm_in))

private theorem maxKey?_node_of_isRangeBST {a k : ℕ} {l r : BinaryTree ℕ}
    (h : IsRangeBST a (.node k l r)) :
    (BinaryTree.node k l r).maxKey? = some (k + r.num_nodes) := by
  rw [maxKey?_eq_some_iff_of_isBST (isBST_of_isRangeBST h)]
  have hmem := mem_of_isRangeBST h
  rcases h with ⟨hk, _, _⟩
  simp only [num_nodes_node] at hmem
  refine ⟨(hmem _).mpr ⟨by omega, by omega⟩, fun x hx => ?_⟩
  have hx' := (hmem x).mp hx
  omega

/-! ## 2. Subtrees, Right Rotations, and Right-Reach (`prop_4_1_right_reach`) -/

private theorem toKeyList_rotateRightEdge {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) :
    (rotateRightEdge t x p).toKeyList = t.toKeyList := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [rotateRightEdge]
    split_ifs with h1 h2
    · simp [ihl]
    · simp [ihr]
    · cases l with
      | nil => rfl
      | node lx a b =>
        dsimp only
        split_ifs with hlx
        · simp [toKeyList_node, List.append_assoc]
        · rfl

private theorem isBST_rotateRightEdge {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) (x p : α) : (rotateRightEdge t x p).IsBST :=
  IsBST_of_toKeyList_eq (toKeyList_rotateRightEdge t x p) ht

private theorem num_nodes_rotateRightEdge {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) :
    (rotateRightEdge t x p).num_nodes = t.num_nodes := by
  rw [num_nodes_eq_length_toKeyList, toKeyList_rotateRightEdge, ← num_nodes_eq_length_toKeyList]

private theorem keyFinset_rotateRightEdge {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) :
    keyFinset (rotateRightEdge t x p) = keyFinset t := by
  rw [← toFinset_toKeyList_eq_keyFinset, toKeyList_rotateRightEdge, toFinset_toKeyList_eq_keyFinset]

private theorem isRangeBST_rotateRightEdge {a : ℕ} {t : BinaryTree ℕ}
    (h : IsRangeBST a t) (x p : ℕ) : IsRangeBST a (rotateRightEdge t x p) := by
  rw [isRangeBST_iff_toKeyList, toKeyList_rotateRightEdge, num_nodes_rotateRightEdge]
  exact isRangeBST_iff_toKeyList.mp h

private theorem subtreeAtKey_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) (v : α) : (subtreeAtKey t v).IsBST := by
  induction t with
  | nil => exact ht
  | node k l r ihl ihr =>
    simp only [subtreeAtKey]
    split_ifs
    · exact ihl (IsBST_left_of_IsBST ht)
    · exact ihr (IsBST_right_of_IsBST ht)
    · exact ht

private theorem mem_of_mem_subtreeAtKey {α : Type} [LinearOrder α] {t : BinaryTree α}
    {v x : α} (hx : x ∈ subtreeAtKey t v) : x ∈ t := by
  induction t with
  | nil => cases hx
  | node k l r ihl ihr =>
    simp only [subtreeAtKey] at hx
    split_ifs at hx
    · exact .left (ihl hx)
    · exact .right (ihr hx)
    · exact hx

private theorem subtreeAtKey_mem_node {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) {v : α} (hv : v ∈ t) :
    ∃ l r, subtreeAtKey t v = .node v l r := by
  induction t with
  | nil => cases hv
  | node k l r ihl ihr =>
    rcases mem_node_iff.mp hv with rfl | hvl | hvr
    · simp [subtreeAtKey]
    · have hlt : v < k := lt_of_IsBST_left l k r ht hvl
      simpa [subtreeAtKey, hlt] using ihl (IsBST_left_of_IsBST ht) hvl
    · have hgt : k < v := gt_of_IsBST_right l k r ht hvr
      simpa [subtreeAtKey, not_lt.mpr hgt.le, hgt] using ihr (IsBST_right_of_IsBST ht) hvr

private theorem self_le_rightReach {t : BinaryTree ℕ} (ht : t.IsBST) {v : ℕ} (hv : v ∈ t) :
    v ≤ rightReach t v := by
  obtain ⟨l, r, hsub⟩ := subtreeAtKey_mem_node ht hv
  have hs_bst : (subtreeAtKey t v).IsBST := subtreeAtKey_isBST ht v
  rcases maxKey?_isBST_spec hs_bst with ⟨hemp, _⟩ | ⟨m, _, hmax, hub⟩
  · rw [hsub] at hemp; cases hemp
  · simp only [rightReach, hmax, Option.getD_some]
    exact hub v (by rw [hsub]; exact .here)

private theorem isRangeBST_subtreeAtKey {a : ℕ} {t : BinaryTree ℕ}
    (ht : IsRangeBST a t) {v : ℕ} (hv : v ∈ t) :
    ∃ a_v : ℕ, a ≤ a_v ∧ a_v ≤ v ∧ v ≤ rightReach t v ∧
      rightReach t v + 1 = a_v + (subtreeAtKey t v).num_nodes ∧
      a_v + (subtreeAtKey t v).num_nodes ≤ a + t.num_nodes ∧
      IsRangeBST a_v (subtreeAtKey t v) := by
  induction t generalizing a with
  | nil => cases hv
  | node k l r ihl ihr =>
    have hbst := isBST_of_isRangeBST ht
    rcases ht with ⟨hk, hl, hr⟩
    rcases mem_node_iff.mp hv with hvk | hvl | hvr
    · subst v
      have hmax : (BinaryTree.node k l r).maxKey? = some (k + r.num_nodes) :=
        maxKey?_node_of_isRangeBST ⟨hk, hl, hr⟩
      have hsub_k : subtreeAtKey (.node k l r) k = .node k l r := by simp [subtreeAtKey]
      have hrr : rightReach (.node k l r) k = k + r.num_nodes := by
        simp [rightReach, hsub_k, hmax]
      refine ⟨a, le_rfl, by omega, by omega, ?_, ?_, ?_⟩
      · rw [hsub_k, hrr]; simp only [num_nodes_node]; omega
      · rw [hsub_k]
      · rw [hsub_k]; exact ⟨hk, hl, hr⟩
    · have hlt : v < k := lt_of_IsBST_left l k r hbst hvl
      obtain ⟨a_v, h1, h2, h3, h4, h5, h6⟩ := ihl hl hvl
      have hsub : subtreeAtKey (.node k l r) v = subtreeAtKey l v := by simp [subtreeAtKey, hlt]
      have hrr : rightReach (.node k l r) v = rightReach l v := by simp [rightReach, hsub]
      refine ⟨a_v, h1, h2, hrr ▸ h3, ?_, ?_, hsub ▸ h6⟩
      · rw [hrr, hsub]; exact h4
      · rw [hsub]; simp only [num_nodes_node]; omega
    · have hgt : k < v := gt_of_IsBST_right l k r hbst hvr
      obtain ⟨a_v, h1, h2, h3, h4, h5, h6⟩ := ihr hr hvr
      have hsub : subtreeAtKey (.node k l r) v = subtreeAtKey r v := by
        simp [subtreeAtKey, not_lt.mpr hgt.le, hgt]
      have hrr : rightReach (.node k l r) v = rightReach r v := by simp [rightReach, hsub]
      refine ⟨a_v, by omega, h2, hrr ▸ h3, ?_, ?_, hsub ▸ h6⟩
      · rw [hrr, hsub]; exact h4
      · rw [hsub]; simp only [num_nodes_node]; omega

private theorem rightReach_node_eq {k : ℕ} {l r : BinaryTree ℕ} {v : ℕ} :
    rightReach (.node k l r) v =
      if v < k then rightReach l v
      else if k < v then rightReach r v
      else ((BinaryTree.node k l r).maxKey?).getD 0 := by
  simp only [rightReach, subtreeAtKey]
  split_ifs <;> rfl

private theorem isRightRotEdge_node_iff {α : Type} [LinearOrder α]
    {k : α} {l r : BinaryTree α} (ht : (BinaryTree.node k l r).IsBST) (x p : α) :
    IsRightRotEdge (.node k l r) x p ↔
      (p < k ∧ IsRightRotEdge l x p) ∨
      (k < p ∧ IsRightRotEdge r x p) ∨
      (p = k ∧ ∃ A B, l = .node x A B) := by
  constructor
  · rintro ⟨A, B, C, hp, hsub⟩
    rcases mem_node_iff.mp hp with rfl | hpl | hpr
    · right; right
      simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
      injection hsub with _ hl _
      exact ⟨rfl, A, B, hl⟩
    · left
      have hlt : p < k := lt_of_IsBST_left l k r ht hpl
      simp only [subtreeAtKey, hlt, ↓reduceIte] at hsub
      exact ⟨hlt, A, B, C, hpl, hsub⟩
    · right; left
      have hgt : k < p := gt_of_IsBST_right l k r ht hpr
      simp only [subtreeAtKey, not_lt.mpr hgt.le, hgt, ↓reduceIte] at hsub
      exact ⟨hgt, A, B, C, hpr, hsub⟩
  · rintro (⟨hlt, A, B, C, hpl, hsub⟩ | ⟨hgt, A, B, C, hpr, hsub⟩ | ⟨rfl, A, B, rfl⟩)
    · exact ⟨A, B, C, .left hpl, by simp [subtreeAtKey, hlt, hsub]⟩
    · exact ⟨A, B, C, .right hpr, by simp [subtreeAtKey, not_lt.mpr hgt.le, hgt, hsub]⟩
    · exact ⟨A, B, r, .here, by simp [subtreeAtKey]⟩

private theorem lt_of_isRightRotEdge {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) {x p : α} (he : IsRightRotEdge t x p) : x < p := by
  rcases he with ⟨A, B, C, _, hsub⟩
  have hs_bst : (subtreeAtKey t p).IsBST := subtreeAtKey_isBST ht p
  rw [hsub] at hs_bst
  exact lt_of_IsBST_left (.node x A B) p C hs_bst .here

private theorem rightReach_rotateRightEdge_spec {t : BinaryTree ℕ} (ht : t.IsBST)
    {x y : ℕ} (he : IsRightRotEdge t x y) :
    (∀ v : ℕ, v ≠ x → rightReach (rotateRightEdge t x y) v = rightReach t v) ∧
    rightReach (rotateRightEdge t x y) x = rightReach t y ∧
    rightReach t x < y ∧ y ≤ rightReach t y := by
  induction t with
  | nil =>
    rcases he with ⟨_, _, _, hy, _⟩
    cases hy
  | node k l r ihl ihr =>
    rcases (isRightRotEdge_node_iff ht x y).mp he with
      ⟨hylt, hel⟩ | ⟨hygt, her⟩ | ⟨rfl, A, B, rfl⟩
    · have hl_bst := IsBST_left_of_IsBST ht
      obtain ⟨heq, hrx, hxlt, hyle⟩ := ihl hl_bst hel
      have hrot : rotateRightEdge (.node k l r) x y = .node k (rotateRightEdge l x y) r := by
        simp [rotateRightEdge, hylt]
      have hxk : x < k := lt_trans (lt_of_isRightRotEdge hl_bst hel) hylt
      rw [hrot]
      refine ⟨fun v hv => ?_, ?_, ?_, ?_⟩
      · rw [rightReach_node_eq, rightReach_node_eq]
        split_ifs with h1 h2
        · exact heq v hv
        · rfl
        · simp [BinaryTree.maxKey?]
      · simp [rightReach_node_eq, hxk, hylt, hrx]
      · simpa [rightReach_node_eq, hxk] using hxlt
      · simpa [rightReach_node_eq, hylt] using hyle
    · have hr_bst := IsBST_right_of_IsBST ht
      obtain ⟨heq, hrx, hxlt, hyle⟩ := ihr hr_bst her
      have hrot : rotateRightEdge (.node k l r) x y = .node k l (rotateRightEdge r x y) := by
        simp [rotateRightEdge, not_lt.mpr hygt.le, hygt]
      have hmax_r : (rotateRightEdge r x y).maxKey? = r.maxKey? :=
        maxKey?_of_toKeyList_eq (toKeyList_rotateRightEdge r x y)
      have hx_in_r : x ∈ r := by
        rcases her with ⟨A, B, C, _, hsub⟩
        exact mem_of_mem_subtreeAtKey (by rw [hsub]; exact .left .here)
      have hkx : k < x := gt_of_IsBST_right l k r ht hx_in_r
      rw [hrot]
      refine ⟨fun v hv => ?_, ?_, ?_, ?_⟩
      · rw [rightReach_node_eq, rightReach_node_eq]
        split_ifs with h1 h2
        · rfl
        · exact heq v hv
        · simp [BinaryTree.maxKey?, hmax_r]
      · simp [rightReach_node_eq, not_lt.mpr hkx.le, hkx, not_lt.mpr hygt.le, hygt, hrx]
      · simpa [rightReach_node_eq, not_lt.mpr hkx.le, hkx] using hxlt
      · simpa [rightReach_node_eq, not_lt.mpr hygt.le, hygt] using hyle
    · have hrot : rotateRightEdge (.node y (.node x A B) r) x y = .node x A (.node y B r) := by
        simp [rotateRightEdge]
      have hxy : x < y := lt_of_IsBST_left (.node x A B) y r ht .here
      have hl_bst : (BinaryTree.node x A B).IsBST := IsBST_left_of_IsBST ht
      rw [hrot]
      refine ⟨fun v hv => ?_, ?_, ?_, ?_⟩
      · by_cases hvx : v < x
        · have hvy : v < y := lt_trans hvx hxy
          simp [rightReach, subtreeAtKey, hvx, hvy]
        · have hxv : x < v := lt_of_le_of_ne (not_lt.mp hvx) hv.symm
          by_cases hvy : v < y
          · simp [rightReach, subtreeAtKey, not_lt.mpr hxv.le, hxv, hvy]
          · by_cases hvy_eq : v = y
            · subst hvy_eq
              simp [rightReach, subtreeAtKey, not_lt.mpr hxy.le, hxy, BinaryTree.maxKey?]
            · have hyv : y < v := lt_of_le_of_ne (not_lt.mp hvy) (Ne.symm hvy_eq)
              simp [rightReach, subtreeAtKey, not_lt.mpr hxv.le, hxv, not_lt.mpr hyv.le, hyv]
      · simp only [rightReach, subtreeAtKey, lt_irrefl, ↓reduceIte, BinaryTree.maxKey?]
        cases r.maxKey? <;> rfl
      · rcases maxKey?_isBST_spec hl_bst with ⟨hemp, _⟩ | ⟨m, hm, hmax, _⟩
        · cases hemp
        · simp only [rightReach, subtreeAtKey, hxy, lt_irrefl, ↓reduceIte, hmax, Option.getD_some]
          exact lt_of_IsBST_left (.node x A B) y r ht hm
      · exact self_le_rightReach ht .here

private theorem rightReach_rotateRightEdge_u_of_isRangeBST {a : ℕ} {t : BinaryTree ℕ}
    (ht : IsRangeBST a t) {u v : ℕ} (he : IsRightRotEdge t u v) :
    rightReach t u + 1 = v := by
  induction t generalizing a with
  | nil =>
    rcases he with ⟨_, _, _, hv, _⟩
    cases hv
  | node k l r ihl ihr =>
    have hbst := isBST_of_isRangeBST ht
    rcases ht with ⟨hk, hl, hr⟩
    rcases (isRightRotEdge_node_iff hbst u v).mp he with
      ⟨hvlt, hel⟩ | ⟨hvgt, her⟩ | ⟨rfl, A, B, rfl⟩
    · have huk : u < k := lt_trans (lt_of_isRightRotEdge (isBST_of_isRangeBST hl) hel) hvlt
      simpa [rightReach_node_eq, huk] using ihl hl hel
    · have hu_r : u ∈ r := by
        rcases her with ⟨A, B, C, _, hsub⟩
        exact mem_of_mem_subtreeAtKey (by rw [hsub]; exact .left .here)
      have hku : k < u := gt_of_IsBST_right l k r hbst hu_r
      simpa [rightReach_node_eq, not_lt.mpr hku.le, hku] using ihr hr her
    · have huv : u < v := lt_of_IsBST_left (.node u A B) v r hbst .here
      have hmax := maxKey?_node_of_isRangeBST hl
      rcases hl with ⟨hu, _, _⟩
      simp only [num_nodes_node] at hk
      simp only [rightReach, subtreeAtKey, huv, lt_irrefl, ↓reduceIte, hmax, Option.getD_some]
      omega

private theorem rightRotStep_left {α : Type} [LinearOrder α] {k : α} {l l' r : BinaryTree α}
    (ht : (BinaryTree.node k l r).IsBST) (hs : RightRotStep l l') :
    RightRotStep (.node k l r) (.node k l' r) := by
  rcases hs with ⟨x, y, hxy, he, rfl⟩
  have hy_in_l : y ∈ l := by rcases he with ⟨_, _, _, hy, _⟩; exact hy
  have hyk : y < k := lt_of_IsBST_left l k r ht hy_in_l
  refine ⟨x, y, hxy, (isRightRotEdge_node_iff ht x y).mpr (Or.inl ⟨hyk, he⟩), ?_⟩
  simp [rotateRightEdge, hyk]

private theorem rightRotStep_right {α : Type} [LinearOrder α] {k : α} {l r r' : BinaryTree α}
    (ht : (BinaryTree.node k l r).IsBST) (hs : RightRotStep r r') :
    RightRotStep (.node k l r) (.node k l r') := by
  rcases hs with ⟨x, y, hxy, he, rfl⟩
  have hy_in_r : y ∈ r := by rcases he with ⟨_, _, _, hy, _⟩; exact hy
  have hky : k < y := gt_of_IsBST_right l k r ht hy_in_r
  refine ⟨x, y, hxy, (isRightRotEdge_node_iff ht x y).mpr (Or.inr (Or.inl ⟨hky, he⟩)), ?_⟩
  simp [rotateRightEdge, not_lt.mpr hky.le, hky]

private theorem rightRotReachable_toKeyList_and_isBST {α : Type} [LinearOrder α]
    {t₁ t₂ : BinaryTree α} (ht₁ : t₁.IsBST) (hr : RightRotReachable t₁ t₂) :
    t₂.toKeyList = t₁.toKeyList ∧ t₂.IsBST := by
  induction hr with
  | refl => exact ⟨rfl, ht₁⟩
  | tail _ hstep ih =>
    obtain ⟨hkl, hbst⟩ := ih
    rcases hstep with ⟨x, y, _, _, rfl⟩
    exact ⟨(toKeyList_rotateRightEdge _ x y).trans hkl, isBST_rotateRightEdge hbst x y⟩

private theorem rightRotReachable_left {α : Type} [LinearOrder α]
    {k : α} {l l' r : BinaryTree α} (ht : (BinaryTree.node k l r).IsBST)
    (hr : RightRotReachable l l') :
    RightRotReachable (.node k l r) (.node k l' r) := by
  induction hr with
  | refl => exact .refl
  | tail hprev hstep ih =>
    rename_i mid _
    have hmid_kl := (rightRotReachable_toKeyList_and_isBST (IsBST_left_of_IsBST ht) hprev).1
    have hmid_bst : (BinaryTree.node k mid r).IsBST :=
      IsBST_of_toKeyList_eq (by simp [toKeyList_node, hmid_kl]) ht
    exact ih.tail (rightRotStep_left hmid_bst hstep)

private theorem rightRotReachable_right {α : Type} [LinearOrder α]
    {k : α} {l r r' : BinaryTree α} (ht : (BinaryTree.node k l r).IsBST)
    (hr : RightRotReachable r r') :
    RightRotReachable (.node k l r) (.node k l r') := by
  induction hr with
  | refl => exact .refl
  | tail hprev hstep ih =>
    rename_i mid _
    have hmid_kl := (rightRotReachable_toKeyList_and_isBST (IsBST_right_of_IsBST ht) hprev).1
    have hmid_bst : (BinaryTree.node k l mid).IsBST :=
      IsBST_of_toKeyList_eq (by simp [toKeyList_node, hmid_kl]) ht
    exact ih.tail (rightRotStep_right hmid_bst hstep)

private theorem lift_root_of_rightReach_lt :
    ∀ (m a k₂ : ℕ) (t : BinaryTree ℕ),
      IsRangeBST a t → t.num_nodes = m →
      a ≤ k₂ → k₂ < a + m →
      (∀ v : ℕ, a ≤ v → v < k₂ → rightReach t v < k₂) →
      ∃ l' r' : BinaryTree ℕ,
        RightRotReachable t (.node k₂ l' r') ∧
        (∀ v : ℕ, v ≠ k₂ → rightReach (.node k₂ l' r') v = rightReach t v) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a k₂ t ht htm hak₂ hk₂lt hub
    rcases t with _ | ⟨k₁, l₁, r₁⟩
    · simp at htm; omega
    · have hbst := isBST_of_isRangeBST ht
      have hmax := maxKey?_node_of_isRangeBST ht
      rcases ht with ⟨hk₁, hl₁, hr₁⟩
      simp only [num_nodes_node] at htm
      have hrr_k₁ : rightReach (.node k₁ l₁ r₁) k₁ = k₁ + r₁.num_nodes := by
        simp [rightReach, subtreeAtKey, hmax]
      have hk₂_le_k₁ : k₂ ≤ k₁ := by
        by_contra hlt
        have hk₁_lt : k₁ < k₂ := by omega
        have hbad := hub k₁ (by omega) hk₁_lt
        omega
      rcases eq_or_lt_of_le hk₂_le_k₁ with rfl | hk₂_lt_k₁
      · exact ⟨l₁, r₁, .refl, fun _ _ => rfl⟩
      · have hub_l₁ : ∀ v : ℕ, a ≤ v → v < k₂ → rightReach l₁ v < k₂ := by
          intro v hav hvk₂
          have hvk₁ : v < k₁ := lt_trans hvk₂ hk₂_lt_k₁
          simpa [rightReach_node_eq, hvk₁] using hub v hav hvk₂
        obtain ⟨A, B, hreach_l, hrr_l⟩ :=
          ih l₁.num_nodes (by omega) a k₂ l₁ hl₁ rfl hak₂ (by omega) hub_l₁
        have hstep1 : RightRotReachable (.node k₁ l₁ r₁) (.node k₁ (.node k₂ A B) r₁) :=
          rightRotReachable_left hbst hreach_l
        have hmid_bst : (BinaryTree.node k₁ (.node k₂ A B) r₁).IsBST :=
          (rightRotReachable_toKeyList_and_isBST hbst hstep1).2
        have hedge_root : IsRightRotEdge (.node k₁ (.node k₂ A B) r₁) k₂ k₁ :=
          (isRightRotEdge_node_iff hmid_bst k₂ k₁).mpr (Or.inr (Or.inr ⟨rfl, A, B, rfl⟩))
        have hrot_eq :
            rotateRightEdge (.node k₁ (.node k₂ A B) r₁) k₂ k₁ = .node k₂ A (.node k₁ B r₁) := by
          simp [rotateRightEdge]
        have hstep2 : RightRotStep (.node k₁ (.node k₂ A B) r₁) (.node k₂ A (.node k₁ B r₁)) :=
          ⟨k₂, k₁, hk₂_lt_k₁, hedge_root, hrot_eq.symm⟩
        have hrr_step2 := (rightReach_rotateRightEdge_spec hmid_bst hedge_root).1
        rw [hrot_eq] at hrr_step2
        refine ⟨A, .node k₁ B r₁, hstep1.tail hstep2, fun v hv => ?_⟩
        rw [hrr_step2 v hv]
        conv_lhs => rw [rightReach_node_eq]
        conv_rhs => rw [rightReach_node_eq]
        split_ifs with h1 h2
        · exact hrr_l v hv
        · rfl
        · simp [BinaryTree.maxKey?]

private theorem rightRotReachable_of_rightReach_le_range :
    ∀ (m a : ℕ) (t₁ t₂ : BinaryTree ℕ),
      IsRangeBST a t₁ → IsRangeBST a t₂ →
      t₁.num_nodes = m → t₂.num_nodes = m →
      (∀ v : ℕ, a ≤ v → v < a + m → rightReach t₁ v ≤ rightReach t₂ v) →
      RightRotReachable t₁ t₂ := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a t₁ t₂ ht₁ ht₂ hn₁ hn₂ hle
    rcases t₂ with _ | ⟨k₂, l₂, r₂⟩
    · simp only [num_nodes_empty] at hn₂
      subst hn₂
      rcases t₁ with _ | ⟨_, _, _⟩
      · exact .refl
      · simp at hn₁
    · rcases ht₂ with ⟨hk₂, hl₂, hr₂⟩
      simp only [num_nodes_node] at hn₂
      have hub_t₁ : ∀ v : ℕ, a ≤ v → v < k₂ → rightReach t₁ v < k₂ := by
        intro v hav hvk₂
        have hv_l₂ : v ∈ l₂ := (mem_of_isRangeBST hl₂ v).mpr ⟨hav, by omega⟩
        obtain ⟨a_v, _, _, _, hrr_end, hend_le, _⟩ := isRangeBST_subtreeAtKey hl₂ hv_l₂
        have hle_v := hle v hav (by omega)
        simp only [rightReach_node_eq, hvk₂, ↓reduceIte] at hle_v
        omega
      obtain ⟨l₁', r₁', hreach_up, hrr_eq⟩ :=
        lift_root_of_rightReach_lt m a k₂ t₁ ht₁ hn₁ (by omega) (by omega) hub_t₁
      have ht₁'_rng : IsRangeBST a (.node k₂ l₁' r₁') := by
        have hkl := (rightRotReachable_toKeyList_and_isBST (isBST_of_isRangeBST ht₁) hreach_up).1
        have hn' : (BinaryTree.node k₂ l₁' r₁').num_nodes = t₁.num_nodes := by
          rw [num_nodes_eq_length_toKeyList, hkl, ← num_nodes_eq_length_toKeyList]
        exact isRangeBST_iff_toKeyList.mpr (by rw [hkl, hn']; exact isRangeBST_iff_toKeyList.mp ht₁)
      have ht₁'_bst := isBST_of_isRangeBST ht₁'_rng
      have ht₁'_n : (BinaryTree.node k₂ l₁' r₁').num_nodes = m := by
        have hkl := (rightRotReachable_toKeyList_and_isBST (isBST_of_isRangeBST ht₁) hreach_up).1
        rw [num_nodes_eq_length_toKeyList, hkl, ← num_nodes_eq_length_toKeyList, hn₁]
      rcases ht₁'_rng with ⟨hk₂', hl₁'_rng, hr₁'_rng⟩
      simp only [num_nodes_node] at ht₁'_n
      have hl_len : l₁'.num_nodes = l₂.num_nodes := by omega
      have hr_len : r₁'.num_nodes = r₂.num_nodes := by omega
      have hle_L : ∀ v : ℕ, a ≤ v → v < a + l₂.num_nodes → rightReach l₁' v ≤ rightReach l₂ v := by
        intro v hav hvk
        have hvk₂ : v < k₂ := by omega
        have h1 := hrr_eq v (ne_of_lt hvk₂)
        have h2 := hle v hav (by omega)
        simp only [rightReach_node_eq, hvk₂, ↓reduceIte] at h1 h2
        omega
      have hle_R : ∀ v : ℕ, k₂ + 1 ≤ v → v < (k₂ + 1) + r₂.num_nodes →
          rightReach r₁' v ≤ rightReach r₂ v := by
        intro v hkv hvr
        have hk₂v : k₂ < v := by omega
        have h1 := hrr_eq v (ne_of_gt hk₂v)
        have h2 := hle v (by omega) (by omega)
        simp only [rightReach_node_eq, not_lt.mpr hk₂v.le, hk₂v, ↓reduceIte] at h1 h2
        omega
      have hreach_L : RightRotReachable l₁' l₂ :=
        ih l₂.num_nodes (by omega) a l₁' l₂ hl₁'_rng hl₂ hl_len rfl hle_L
      have hreach_R : RightRotReachable r₁' r₂ :=
        ih r₂.num_nodes (by omega) (k₂ + 1) r₁' r₂ hr₁'_rng hr₂ hr_len rfl hle_R
      have hstep_L : RightRotReachable (.node k₂ l₁' r₁') (.node k₂ l₂ r₁') :=
        rightRotReachable_left ht₁'_bst hreach_L
      have hmid2_bst : (BinaryTree.node k₂ l₂ r₁').IsBST :=
        (rightRotReachable_toKeyList_and_isBST ht₁'_bst hstep_L).2
      have hstep_R : RightRotReachable (.node k₂ l₂ r₁') (.node k₂ l₂ r₂) :=
        rightRotReachable_right hmid2_bst hreach_R
      exact (hreach_up.trans hstep_L).trans hstep_R

/-- **Proposition 4.1** (`prop:right-reach`, Tamari Right-Reach Characterization):
On `{1, ..., n}` (`n ≥ 1`), BST `t₂` is reachable from BST `t₁` by zero or more right single
rotations if and only if `R_{t₁}(v) ≤ R_{t₂}(v)` for every `v ∈ {1, ..., n}`. -/
theorem prop_4_1_right_reach (n : ℕ) (hn : 1 ≤ n) (t₁ t₂ : BinaryTree ℕ)
    (ht₁ : t₁.IsBST) (ht₂ : t₂.IsBST)
    (hk₁ : keyFinset t₁ = Finset.Icc 1 n) (hk₂ : keyFinset t₂ = Finset.Icc 1 n) :
    RightRotReachable t₁ t₂ ↔ ∀ v ∈ Finset.Icc 1 n, rightReach t₁ v ≤ rightReach t₂ v := by
  have _ := hn
  constructor
  · intro hreach
    have hmono : ∀ {a b : BinaryTree ℕ}, a.IsBST → RightRotReachable a b →
        a.IsBST ∧ b.IsBST ∧ ∀ v : ℕ, rightReach a v ≤ rightReach b v := by
      intro a b ha hr
      induction hr with
      | refl => exact ⟨ha, ha, fun _ => le_rfl⟩
      | tail _ hstep ih =>
        obtain ⟨ha0, hmid, hle⟩ := ih
        rcases hstep with ⟨x, y, _, he, rfl⟩
        obtain ⟨heq, hrx, hxlt, hyle⟩ := rightReach_rotateRightEdge_spec hmid he
        refine ⟨ha0, isBST_rotateRightEdge hmid x y, fun v => ?_⟩
        by_cases hvx : v = x
        · subst hvx
          exact le_trans (hle v) (by omega)
        · rw [heq v hvx]
          exact hle v
    intro v _
    exact (hmono ht₁ hreach).2.2 v
  · intro hle
    obtain ⟨hr₁, hn₁⟩ := isRangeBST_of_keyFinset_Icc ht₁ hk₁
    obtain ⟨hr₂, hn₂⟩ := isRangeBST_of_keyFinset_Icc ht₂ hk₂
    apply rightRotReachable_of_rightReach_le_range n 1 t₁ t₂ hr₁ hr₂ hn₁ hn₂
    intro v h1 h2
    exact hle v (Finset.mem_Icc.mpr ⟨h1, by omega⟩)

/-! ## 3. `lcaBST`, `IsLCAClosed`, `restrictTree`, and Interval Projections -/

private theorem lcaBST_spec {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST)
    {x y z : α} (hx : x ∈ t) (hy : y ∈ t) (hlca : lcaBST t x y = some z) :
    z ∈ t ∧ min x y ≤ z ∧ z ≤ max x y ∧
      x ∈ subtreeAtKey t z ∧ y ∈ subtreeAtKey t z := by
  induction t with
  | nil => cases hx
  | node k l r ihl ihr =>
    simp only [lcaBST] at hlca
    split_ifs at hlca with hlt hgt
    · have hxl : x ∈ l := by
        rcases mem_node_iff.mp hx with rfl | hxl | hxr
        · exact absurd hlt.1 (lt_irrefl _)
        · exact hxl
        · exact absurd (lt_trans hlt.1 (gt_of_IsBST_right l k r ht hxr)) (lt_irrefl _)
      have hyl : y ∈ l := by
        rcases mem_node_iff.mp hy with rfl | hyl | hyr
        · exact absurd hlt.2 (lt_irrefl _)
        · exact hyl
        · exact absurd (lt_trans hlt.2 (gt_of_IsBST_right l k r ht hyr)) (lt_irrefl _)
      obtain ⟨hzl, hmin, hmax, hxs, hys⟩ := ihl (IsBST_left_of_IsBST ht) hxl hyl hlca
      have hzk : z < k := lt_of_IsBST_left l k r ht hzl
      exact ⟨.left hzl, hmin, hmax,
        by simpa [subtreeAtKey, hzk] using hxs,
        by simpa [subtreeAtKey, hzk] using hys⟩
    · have hxr : x ∈ r := by
        rcases mem_node_iff.mp hx with rfl | hxl | hxr
        · exact absurd hgt.1 (lt_irrefl _)
        · exact absurd (lt_trans (lt_of_IsBST_left l k r ht hxl) hgt.1) (lt_irrefl _)
        · exact hxr
      have hyr : y ∈ r := by
        rcases mem_node_iff.mp hy with rfl | hyl | hyr
        · exact absurd hgt.2 (lt_irrefl _)
        · exact absurd (lt_trans (lt_of_IsBST_left l k r ht hyl) hgt.2) (lt_irrefl _)
        · exact hyr
      obtain ⟨hzr, hmin, hmax, hxs, hys⟩ := ihr (IsBST_right_of_IsBST ht) hxr hyr hlca
      have hkz : k < z := gt_of_IsBST_right l k r ht hzr
      exact ⟨.right hzr, hmin, hmax,
        by simpa [subtreeAtKey, not_lt.mpr hkz.le, hkz] using hxs,
        by simpa [subtreeAtKey, not_lt.mpr hkz.le, hkz] using hys⟩
    · injection hlca with hkz
      subst hkz
      have hmin : min x y ≤ k := by
        by_cases hkx : k < x
        · have hyk : y ≤ k := not_lt.mp (fun hky => hgt ⟨hkx, hky⟩)
          exact le_trans (min_le_right x y) hyk
        · exact le_trans (min_le_left x y) (not_lt.mp hkx)
      have hmax : k ≤ max x y := by
        by_cases hxk : x < k
        · have hky : k ≤ y := not_lt.mp (fun hyk => hlt ⟨hxk, hyk⟩)
          exact le_trans hky (le_max_right x y)
        · exact le_trans (not_lt.mp hxk) (le_max_left x y)
      exact ⟨.here, hmin, hmax,
        by simpa [subtreeAtKey] using hx,
        by simpa [subtreeAtKey] using hy⟩

private theorem isLCAClosed_children {α : Type} [LinearOrder α] {k : α} {l r : BinaryTree α}
    {S : Set α} (ht : (BinaryTree.node k l r).IsBST) (hS : IsLCAClosed (.node k l r) S) :
    IsLCAClosed l S ∧ IsLCAClosed r S := by
  constructor
  · intro x hx y hy hxS hyS z hz
    have hxk : x < k := lt_of_IsBST_left l k r ht hx
    have hyk : y < k := lt_of_IsBST_left l k r ht hy
    exact hS x (.left hx) y (.left hy) hxS hyS z (by simp [lcaBST, hxk, hyk, hz])
  · intro x hx y hy hxS hyS z hz
    have hkx : k < x := gt_of_IsBST_right l k r ht hx
    have hky : k < y := gt_of_IsBST_right l k r ht hy
    exact hS x (.right hx) y (.right hy) hxS hyS z
      (by simp [lcaBST, not_lt.mpr hkx.le, hkx, hky, hz])

private theorem isLCAClosed_not_both {α : Type} [LinearOrder α] {k : α} {l r : BinaryTree α}
    {S : Set α} (ht : (BinaryTree.node k l r).IsBST) (hS : IsLCAClosed (.node k l r) S)
    (hk : k ∉ S) {a b : α} (ha : a ∈ l) (haS : a ∈ S) (hb : b ∈ r) (hbS : b ∈ S) : False := by
  have hak : a < k := lt_of_IsBST_left l k r ht ha
  have hkb : k < b := gt_of_IsBST_right l k r ht hb
  have hlca : lcaBST (.node k l r) a b = some k := by
    simp [lcaBST, hak, not_lt.mpr hak.le, not_lt.mpr hkb.le]
  exact hk (hS a (.left ha) b (.right hb) haS hbS k hlca)

private theorem isLCAClosed_subtreeAtKey {α : Type} [LinearOrder α] {t : BinaryTree α}
    {S : Set α} (ht : t.IsBST) (hS : IsLCAClosed t S) (v : α) :
    IsLCAClosed (subtreeAtKey t v) S := by
  induction t with
  | nil => exact hS
  | node k l r ihl ihr =>
    obtain ⟨hSl, hSr⟩ := isLCAClosed_children ht hS
    simp only [subtreeAtKey]
    split_ifs
    · exact ihl (IsBST_left_of_IsBST ht) hSl
    · exact ihr (IsBST_right_of_IsBST ht) hSr
    · exact hS

private theorem restrictTree_eq_nil_iff {α : Type} {t : BinaryTree α} {S : Set α} :
    restrictTree t S = .nil ↔ ∀ x ∈ t, x ∉ S := by
  induction t with
  | nil => simp [restrictTree]
  | node u A B ihA ihB =>
    simp only [restrictTree]
    split_ifs with hu hb
    · simp only [false_iff, not_forall]
      exact ⟨u, .here, not_not.mpr hu⟩
    · rcases hb with ⟨b, hbB, hbS⟩
      constructor
      · intro hnil
        exact absurd hbS ((ihB.mp hnil) b hbB)
      · intro hall
        exact absurd hbS (hall b (.right hbB))
    · rw [ihA]
      constructor
      · intro hallA x hx
        rcases mem_node_iff.mp hx with rfl | hxA | hxB
        · exact hu
        · exact hallA x hxA
        · exact fun hxS => hb ⟨x, hxB, hxS⟩
      · intro hall x hxA
        exact hall x (.left hxA)

private theorem toKeyList_restrictTree_of_isLCAClosed {α : Type} [LinearOrder α]
    {t : BinaryTree α} {S : Set α} (ht : t.IsBST) (hS : IsLCAClosed t S) :
    (restrictTree t S).toKeyList =
      (open Classical in t.toKeyList.filter (fun x => decide (x ∈ S))) := by
  classical
  induction t with
  | nil => simp [restrictTree]
  | node u A B ihA ihB =>
    obtain ⟨hSA, hSB⟩ := isLCAClosed_children ht hS
    have ihA' := ihA (IsBST_left_of_IsBST ht) hSA
    have ihB' := ihB (IsBST_right_of_IsBST ht) hSB
    by_cases hu : u ∈ S
    · simp [restrictTree, toKeyList_node, List.filter_append, hu, ihA', ihB']
    · by_cases hb : ∃ b ∈ B, b ∈ S
      · simp only [restrictTree, hu, hb, ↓reduceIte, ihB', toKeyList_node,
          List.filter_append, List.filter_cons, decide_eq_true_eq]
        rcases hb with ⟨b, hbB, hbS⟩
        have hA_empty : List.filter (fun x => decide (x ∈ S)) A.toKeyList = [] := by
          rw [List.filter_eq_nil_iff]
          intro a ha
          simp only [decide_eq_true_eq]
          exact fun haS => isLCAClosed_not_both ht hS hu
            (mem_iff_mem_toKeyList.mpr ha) haS hbB hbS
        simp [hA_empty]
      · simp only [restrictTree, hu, hb, ↓reduceIte, ihA', toKeyList_node,
          List.filter_append, List.filter_cons, decide_eq_true_eq]
        have hB_empty : List.filter (fun x => decide (x ∈ S)) B.toKeyList = [] := by
          rw [List.filter_eq_nil_iff]
          intro b hb_kl
          simp only [decide_eq_true_eq]
          exact fun hbS => hb ⟨b, mem_iff_mem_toKeyList.mpr hb_kl, hbS⟩
        simp [hB_empty]

private theorem isBST_restrictTree_of_isLCAClosed {α : Type} [LinearOrder α]
    {t : BinaryTree α} {S : Set α} (ht : t.IsBST) (hS : IsLCAClosed t S) :
    (restrictTree t S).IsBST := by
  rw [IsBST_iff_toKeyList_sorted, toKeyList_restrictTree_of_isLCAClosed ht hS]
  exact ((IsBST_iff_toKeyList_sorted t).mp ht).filter _

private theorem mem_restrictTree_of_isLCAClosed {α : Type} [LinearOrder α]
    {t : BinaryTree α} {S : Set α} (ht : t.IsBST) (hS : IsLCAClosed t S) (x : α) :
    x ∈ restrictTree t S ↔ x ∈ t ∧ x ∈ S := by
  classical
  rw [mem_iff_mem_toKeyList, toKeyList_restrictTree_of_isLCAClosed ht hS, List.mem_filter,
    decide_eq_true_eq, ← mem_iff_mem_toKeyList]

private theorem keyFinset_restrictTree_of_isLCAClosed {t : BinaryTree ℕ} {S : Finset ℕ}
    (ht : t.IsBST) (hS : IsLCAClosed t (S : Set ℕ)) (hsub : S ⊆ keyFinset t) :
    keyFinset (restrictTree t (S : Set ℕ)) = S := by
  ext x
  rw [mem_keyFinset_iff, mem_restrictTree_of_isLCAClosed ht hS, Finset.mem_coe]
  exact ⟨fun h => h.2, fun hx => ⟨mem_keyFinset_iff.mp (hsub hx), hx⟩⟩

private theorem subtreeAtKey_restrictTree_of_isLCAClosed {t : BinaryTree ℕ} {S : Set ℕ}
    (ht : t.IsBST) (hS : IsLCAClosed t S) {x : ℕ} (hx : x ∈ t) (hxS : x ∈ S) :
    subtreeAtKey (restrictTree t S) x = restrictTree (subtreeAtKey t x) S := by
  induction t with
  | nil => cases hx
  | node u A B ihA ihB =>
    obtain ⟨hSA, hSB⟩ := isLCAClosed_children ht hS
    by_cases hu : u ∈ S
    · simp only [restrictTree, hu, ↓reduceIte]
      rcases mem_node_iff.mp hx with rfl | hxA | hxB
      · simp [subtreeAtKey, restrictTree, hu]
      · have hlt : x < u := lt_of_IsBST_left A u B ht hxA
        simpa [subtreeAtKey, hlt] using ihA (IsBST_left_of_IsBST ht) hSA hxA
      · have hgt : u < x := gt_of_IsBST_right A u B ht hxB
        simpa [subtreeAtKey, not_lt.mpr hgt.le, hgt] using ihB (IsBST_right_of_IsBST ht) hSB hxB
    · rcases mem_node_iff.mp hx with rfl | hxA | hxB
      · exact absurd hxS hu
      · have hlt : x < u := lt_of_IsBST_left A u B ht hxA
        have hnoB : ¬ ∃ b ∈ B, b ∈ S := by
          rintro ⟨b, hbB, hbS⟩
          exact isLCAClosed_not_both ht hS hu hxA hxS hbB hbS
        simp only [restrictTree, hu, hnoB, ↓reduceIte, subtreeAtKey, hlt]
        exact ihA (IsBST_left_of_IsBST ht) hSA hxA
      · have hgt : u < x := gt_of_IsBST_right A u B ht hxB
        have hexB : ∃ b ∈ B, b ∈ S := ⟨x, hxB, hxS⟩
        simp only [restrictTree, hu, hexB, ↓reduceIte, subtreeAtKey, not_lt.mpr hgt.le, hgt]
        exact ihB (IsBST_right_of_IsBST ht) hSB hxB

private theorem restrictTree_rotateRightEdge {t : BinaryTree ℕ} {S : Set ℕ}
    (ht : t.IsBST) {u v : ℕ} (he : IsRightRotEdge t u v)
    (hS : IsLCAClosed t S) (hS' : IsLCAClosed (rotateRightEdge t u v) S) :
    (u ∈ S ∧ v ∈ S →
      IsRightRotEdge (restrictTree t S) u v ∧
      restrictTree (rotateRightEdge t u v) S = rotateRightEdge (restrictTree t S) u v) ∧
    (¬ (u ∈ S ∧ v ∈ S) →
      restrictTree (rotateRightEdge t u v) S = restrictTree t S) := by
  induction t with
  | nil =>
    rcases he with ⟨_, _, _, hv, _⟩
    cases hv
  | node k L R ihL ihR =>
    have ht' : (rotateRightEdge (.node k L R) u v).IsBST := isBST_rotateRightEdge ht u v
    have hres_bst : (restrictTree (.node k L R) S).IsBST := isBST_restrictTree_of_isLCAClosed ht hS
    obtain ⟨hSL, hSR⟩ := isLCAClosed_children ht hS
    rcases (isRightRotEdge_node_iff ht u v).mp he with
      ⟨hvlt, heL⟩ | ⟨hvgt, heR⟩ | ⟨rfl, A, M, rfl⟩
    · have hrot : rotateRightEdge (.node k L R) u v = .node k (rotateRightEdge L u v) R := by
        simp [rotateRightEdge, hvlt]
      rw [hrot] at hS' ht' ⊢
      obtain ⟨hSL', _⟩ := isLCAClosed_children ht' hS'
      obtain ⟨ih1, ih2⟩ := ihL (IsBST_left_of_IsBST ht) heL hSL hSL'
      constructor
      · rintro ⟨huS, hvS⟩
        obtain ⟨he_res, hrot_res⟩ := ih1 ⟨huS, hvS⟩
        by_cases hkS : k ∈ S
        · have hk_res_bst :
              (BinaryTree.node k (restrictTree L S) (restrictTree R S)).IsBST := by
            simpa [restrictTree, hkS] using hres_bst
          refine ⟨?_, ?_⟩
          · simp only [restrictTree, hkS, ↓reduceIte]
            exact (isRightRotEdge_node_iff hk_res_bst u v).mpr (Or.inl ⟨hvlt, he_res⟩)
          · simp [restrictTree, hkS, rotateRightEdge, hvlt, hrot_res]
        · have hv_in_L : v ∈ L := by rcases heL with ⟨_, _, _, hvL, _⟩; exact hvL
          have hnoR : ¬ ∃ b ∈ R, b ∈ S := by
            rintro ⟨b, hbR, hbS⟩
            exact isLCAClosed_not_both ht hS hkS hv_in_L hvS hbR hbS
          simp only [restrictTree, hkS, hnoR, ↓reduceIte]
          exact ⟨he_res, hrot_res⟩
      · intro hnot
        have h_eq := ih2 hnot
        simp only [restrictTree]
        split_ifs
        · rw [h_eq]
        · rfl
        · exact h_eq
    · have hrot : rotateRightEdge (.node k L R) u v = .node k L (rotateRightEdge R u v) := by
        simp [rotateRightEdge, not_lt.mpr hvgt.le, hvgt]
      rw [hrot] at hS' ht' ⊢
      obtain ⟨_, hSR'⟩ := isLCAClosed_children ht' hS'
      obtain ⟨ih1, ih2⟩ := ihR (IsBST_right_of_IsBST ht) heR hSR hSR'
      have hmemR' : ∀ b, b ∈ rotateRightEdge R u v ↔ b ∈ R := by
        intro b
        rw [mem_iff_mem_toKeyList, toKeyList_rotateRightEdge, ← mem_iff_mem_toKeyList]
      have hexR_iff : (∃ b ∈ rotateRightEdge R u v, b ∈ S) ↔ (∃ b ∈ R, b ∈ S) :=
        ⟨fun ⟨b, hb1, hb2⟩ => ⟨b, (hmemR' b).mp hb1, hb2⟩,
         fun ⟨b, hb1, hb2⟩ => ⟨b, (hmemR' b).mpr hb1, hb2⟩⟩
      constructor
      · rintro ⟨huS, hvS⟩
        obtain ⟨he_res, hrot_res⟩ := ih1 ⟨huS, hvS⟩
        have hv_in_R : v ∈ R := by rcases heR with ⟨_, _, _, hvR, _⟩; exact hvR
        have hexR : ∃ b ∈ R, b ∈ S := ⟨v, hv_in_R, hvS⟩
        have hexR' : ∃ b ∈ rotateRightEdge R u v, b ∈ S := hexR_iff.mpr hexR
        by_cases hkS : k ∈ S
        · have hk_res_bst :
              (BinaryTree.node k (restrictTree L S) (restrictTree R S)).IsBST := by
            simpa [restrictTree, hkS] using hres_bst
          refine ⟨?_, ?_⟩
          · simp only [restrictTree, hkS, ↓reduceIte]
            exact (isRightRotEdge_node_iff hk_res_bst u v).mpr (Or.inr (Or.inl ⟨hvgt, he_res⟩))
          · simp [restrictTree, hkS, rotateRightEdge, not_lt.mpr hvgt.le, hvgt, hrot_res]
        · simp only [restrictTree, hkS, hexR, hexR', ↓reduceIte]
          exact ⟨he_res, hrot_res⟩
      · intro hnot
        have h_eq := ih2 hnot
        by_cases hkS : k ∈ S
        · simp [restrictTree, hkS, h_eq]
        · by_cases hexR : ∃ b ∈ R, b ∈ S
          · have hexR' : ∃ b ∈ rotateRightEdge R u v, b ∈ S := hexR_iff.mpr hexR
            simp [restrictTree, hkS, hexR, hexR', h_eq]
          · have hexR' : ¬ ∃ b ∈ rotateRightEdge R u v, b ∈ S := fun h => hexR (hexR_iff.mp h)
            simp [restrictTree, hkS, hexR, hexR']
    · have hrot : rotateRightEdge (.node v (.node u A M) R) u v = .node u A (.node v M R) := by
        simp [rotateRightEdge]
      rw [hrot] at hS' ht' ⊢
      constructor
      · rintro ⟨huS, hvS⟩
        refine ⟨?_, ?_⟩
        · simp only [restrictTree, huS, hvS, ↓reduceIte]
          have hbst_root :
              (BinaryTree.node v (.node u (restrictTree A S) (restrictTree M S))
                (restrictTree R S)).IsBST := by
            simpa [restrictTree, huS, hvS] using hres_bst
          exact (isRightRotEdge_node_iff hbst_root u v).mpr
            (Or.inr (Or.inr ⟨rfl, restrictTree A S, restrictTree M S, rfl⟩))
        · simp [restrictTree, huS, hvS, rotateRightEdge]
      · intro hnot
        by_cases hvS : v ∈ S
        · have huS : u ∉ S := fun hu => hnot ⟨hu, hvS⟩
          have hex_vMR : ∃ b ∈ BinaryTree.node v M R, b ∈ S := ⟨v, BinaryTree.Mem.here, hvS⟩
          have hnoA : ∀ a ∈ A, a ∉ S := by
            intro a haA haS
            exact isLCAClosed_not_both ht' hS' huS haA haS
              (BinaryTree.Mem.here : v ∈ BinaryTree.node v M R) hvS
          have hA_nil : restrictTree A S = .nil := restrictTree_eq_nil_iff.mpr hnoA
          have h_uAM : restrictTree (.node u A M) S = restrictTree M S := by
            by_cases hexM : ∃ b ∈ M, b ∈ S
            · simp only [restrictTree, huS, hexM, ↓reduceIte]
            · have hM_nil : restrictTree M S = .nil :=
                restrictTree_eq_nil_iff.mpr (fun m hm hmS => hexM ⟨m, hm, hmS⟩)
              simp only [restrictTree, huS, hexM, ↓reduceIte, hA_nil, hM_nil]
          have hlhs : restrictTree (.node u A (.node v M R)) S =
              .node v (restrictTree M S) (restrictTree R S) := by
            simp only [restrictTree, huS, hvS, hex_vMR, ↓reduceIte]
          have hrhs : restrictTree (.node v (.node u A M) R) S =
              .node v (restrictTree M S) (restrictTree R S) := by
            rw [restrictTree]
            simp only [hvS, ↓reduceIte, h_uAM]
          exact hlhs.trans hrhs.symm
        · by_cases huS : u ∈ S
          · have hnoR : ¬ ∃ b ∈ R, b ∈ S := by
              rintro ⟨c, hcR, hcS⟩
              exact isLCAClosed_not_both ht hS hvS
                (BinaryTree.Mem.here : u ∈ BinaryTree.node u A M) huS hcR hcS
            simp only [restrictTree, huS, hvS, hnoR, ↓reduceIte]
          · by_cases hexR : ∃ b ∈ R, b ∈ S
            · have hex_vMR : ∃ b ∈ BinaryTree.node v M R, b ∈ S := by
                rcases hexR with ⟨c, hcR, hcS⟩
                exact ⟨c, BinaryTree.Mem.right hcR, hcS⟩
              simp only [restrictTree, huS, hvS, hex_vMR, hexR, ↓reduceIte]
            · by_cases hexM : ∃ b ∈ M, b ∈ S
              · have hex_vMR : ∃ b ∈ BinaryTree.node v M R, b ∈ S := by
                  rcases hexM with ⟨m, hmM, hmS⟩
                  exact ⟨m, BinaryTree.Mem.left hmM, hmS⟩
                simp only [restrictTree, huS, hvS, hexR, hexM, hex_vMR, ↓reduceIte]
              · have hno_vMR : ¬ ∃ b ∈ BinaryTree.node v M R, b ∈ S := by
                  rintro ⟨b, hb, hbS⟩
                  rcases mem_node_iff.mp hb with rfl | hbM | hbR
                  · exact hvS hbS
                  · exact hexM ⟨b, hbM, hbS⟩
                  · exact hexR ⟨b, hbR, hbS⟩
                simp only [restrictTree, huS, hvS, hexR, hexM, hno_vMR, ↓reduceIte]

/-! ## 4. Interval Blocks, Preorder Summaries, and Part (1) of Lemma 4.2 -/

private theorem mem_intervalBlock_toSet (C : IntervalBlock) (x : ℕ) :
    x ∈ C.toSet ↔ C.lo ≤ x ∧ x ≤ C.hi := Iff.rfl

private theorem mem_intervalBlock_toSet_iff (C : IntervalBlock) (x : ℕ) :
    x ∈ C.toSet ↔ x ∈ C.toFinset := by
  simp [IntervalBlock.toSet, IntervalBlock.toFinset]

private theorem coe_intervalBlock_toFinset (C : IntervalBlock) :
    (C.toFinset : Set ℕ) = C.toSet := by
  ext x
  simp [IntervalBlock.toSet, IntervalBlock.toFinset]

private theorem isLCAClosed_intervalBlock {t : BinaryTree ℕ} (ht : t.IsBST) (C : IntervalBlock) :
    IsLCAClosed t C.toSet := by
  intro x hx y hy hxC hyC z hz
  obtain ⟨_, hmin, hmax, _, _⟩ := lcaBST_spec ht hx hy hz
  rw [mem_intervalBlock_toSet] at hxC hyC ⊢
  omega

private theorem restrictTree_interval_isRangeBST {N : ℕ} {B : BinaryTree ℕ}
    (hB_rng : IsRangeBST 1 B) (hB_n : B.num_nodes = N)
    {C : IntervalBlock} (hC : 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N) :
    IsRangeBST C.lo (restrictTree B C.toSet) ∧
    (restrictTree B C.toSet).num_nodes = C.size ∧
    C.size = C.hi - C.lo + 1 ∧ 1 ≤ C.size := by
  have hB_bst := isBST_of_isRangeBST hB_rng
  have hLCA := isLCAClosed_intervalBlock hB_bst C
  have hres_bst := isBST_restrictTree_of_isLCAClosed hB_bst hLCA
  have hsz : C.size = C.hi - C.lo + 1 := by simp [IntervalBlock.size, hC.2.1]
  have hkl : (restrictTree B C.toSet).toKeyList = List.range' C.lo C.size := by
    apply eq_of_pairwise_lt_of_mem_iff
      ((IsBST_iff_toKeyList_sorted _).mp hres_bst) (pairwise_lt_range' C.lo C.size)
    intro x
    rw [← mem_iff_mem_toKeyList, mem_restrictTree_of_isLCAClosed hB_bst hLCA,
      mem_of_isRangeBST hB_rng, hB_n, mem_intervalBlock_toSet, List.mem_range', hsz]
    constructor
    · rintro ⟨_, hlo, hhi⟩; exact ⟨x - C.lo, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩; omega
  have hn : (restrictTree B C.toSet).num_nodes = C.size := by
    rw [num_nodes_eq_length_toKeyList, hkl, List.length_range']
  exact ⟨isRangeBST_iff_toKeyList.mpr (hn ▸ hkl), hn, hsz, by omega⟩

private theorem restrictTree_interval_root_dominates {B : BinaryTree ℕ} (hB : B.IsBST)
    {C : IntervalBlock} {rC : ℕ} {lC rC' : BinaryTree ℕ}
    (hres : restrictTree B C.toSet = .node rC lC rC') :
    rC ∈ B ∧ rC ∈ C.toSet ∧ ∀ z ∈ B, z ∈ C.toSet → z ∈ subtreeAtKey B rC := by
  induction B with
  | nil => simp [restrictTree] at hres
  | node u L R ihL ihR =>
    by_cases hu : u ∈ C.toSet
    · simp only [restrictTree, hu, ↓reduceIte] at hres
      injection hres with hu_eq _ _
      subst hu_eq
      exact ⟨.here, hu, fun z hz _ => by simpa [subtreeAtKey] using hz⟩
    · by_cases hexR : ∃ b ∈ R, b ∈ C.toSet
      · simp only [restrictTree, hu, hexR, ↓reduceIte] at hres
        obtain ⟨hrC_R, hrC_C, hdomR⟩ := ihR (IsBST_right_of_IsBST hB) hres
        have hurC : u < rC := gt_of_IsBST_right L u R hB hrC_R
        have hu_lt_lo : u < C.lo := by
          rw [mem_intervalBlock_toSet] at hu hrC_C
          omega
        refine ⟨.right hrC_R, hrC_C, fun z hz hzC => ?_⟩
        have huz : u < z := by
          rw [mem_intervalBlock_toSet] at hzC
          omega
        have hzR : z ∈ R := by
          rcases mem_node_iff.mp hz with rfl | hzL | hzR
          · exact absurd huz (lt_irrefl _)
          · exact absurd (lt_trans (lt_of_IsBST_left L u R hB hzL) huz) (lt_irrefl _)
          · exact hzR
        simpa [subtreeAtKey, not_lt.mpr hurC.le, hurC] using hdomR z hzR hzC
      · simp only [restrictTree, hu, hexR, ↓reduceIte] at hres
        obtain ⟨hrC_L, hrC_C, hdomL⟩ := ihL (IsBST_left_of_IsBST hB) hres
        have hrCu : rC < u := lt_of_IsBST_left L u R hB hrC_L
        have hhi_lt_u : C.hi < u := by
          rw [mem_intervalBlock_toSet] at hu hrC_C
          omega
        refine ⟨.left hrC_L, hrC_C, fun z hz hzC => ?_⟩
        have hzu : z < u := by
          rw [mem_intervalBlock_toSet] at hzC
          omega
        have hzL : z ∈ L := by
          rcases mem_node_iff.mp hz with rfl | hzL | hzR
          · exact absurd hzu (lt_irrefl _)
          · exact hzL
          · exact absurd (lt_trans hzu (gt_of_IsBST_right L u R hB hzR)) (lt_irrefl _)
        simpa [subtreeAtKey, hrCu] using hdomL z hzL hzC

private theorem bstPreorderList_mem_iff {α : Type} {t : BinaryTree α} {x : α} :
    x ∈ bstPreorderList t ↔ x ∈ t := by
  induction t with
  | nil => simp [bstPreorderList]
  | node k l r ihl ihr =>
    simp [bstPreorderList, mem_node_iff, ihl, ihr]

private theorem bstPreorderList_length {α : Type} (t : BinaryTree α) :
    (bstPreorderList t).length = t.num_nodes := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp [bstPreorderList, num_nodes_node, ihl, ihr]
    omega

private theorem bstPreorderList_nodup_of_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) : (bstPreorderList t).Nodup := by
  induction t with
  | nil => exact List.nodup_nil
  | node k l r ihl ihr =>
    simp only [bstPreorderList, List.nodup_cons, List.mem_append, bstPreorderList_mem_iff]
    refine ⟨?_, List.nodup_append.mpr ⟨ihl (IsBST_left_of_IsBST ht),
      ihr (IsBST_right_of_IsBST ht), ?_⟩⟩
    · rintro (hkl | hkr)
      · exact lt_irrefl k (lt_of_IsBST_left l k r ht hkl)
      · exact lt_irrefl k (gt_of_IsBST_right l k r ht hkr)
    · intro x hxl y hyr hxy
      rw [bstPreorderList_mem_iff] at hxl hyr
      subst hxy
      exact lt_irrefl x (lt_trans (lt_of_IsBST_left l k r ht hxl) (gt_of_IsBST_right l k r ht hyr))

private theorem listRank1_eq_zero_iff {α : Type} [DecidableEq α] (xs : List α) (x : α) :
    listRank1 xs x = 0 ↔ x ∉ xs := by
  induction xs with
  | nil => simp [listRank1]
  | cons y ys ih =>
    simp only [listRank1, List.mem_cons]
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, ↓reduceIte, false_or]
      split_ifs with hr
      · exact ⟨fun _ => ih.mp hr, fun _ => rfl⟩
      · exact ⟨False.elim, fun h => absurd (ih.mpr h) hr⟩

private theorem one_le_and_listRank1_le_iff_mem_take {α : Type} [DecidableEq α]
    (xs : List α) (x : α) (D : ℕ) :
    (1 ≤ listRank1 xs x ∧ listRank1 xs x ≤ D) ↔ x ∈ xs.take D := by
  induction xs generalizing D with
  | nil => simp [listRank1]
  | cons y ys ih =>
    cases D with
    | zero => simp; omega
    | succ d =>
      simp only [listRank1, List.take_succ_cons, List.mem_cons]
      by_cases hxy : x = y
      · simp [hxy]
      · simp only [hxy, ↓reduceIte, false_or]
        by_cases hr : listRank1 ys x = 0
        · have hnot : x ∉ ys := (listRank1_eq_zero_iff ys x).mp hr
          simp only [hr, ↓reduceIte]
          exact ⟨fun ⟨h1, _⟩ => by omega, fun h => absurd (List.mem_of_mem_take h) hnot⟩
        · simp only [hr, ↓reduceIte]
          have h1 : (1 ≤ listRank1 ys x + 1 ∧ listRank1 ys x + 1 ≤ d + 1) ↔
              (1 ≤ listRank1 ys x ∧ listRank1 ys x ≤ d) := by omega
          exact h1.trans (ih d)

private noncomputable def blockSummaryFinset (B : BinaryTree ℕ) (C : IntervalBlock) (D : ℕ) :
    Finset ℕ :=
  open Classical in
  C.toFinset.filter (fun w =>
    let rk := preorderRank (restrictTree B C.toSet) w
    1 ≤ rk ∧ rk ≤ D)

private theorem blockSummaryFinset_eq_take_toFinset {N : ℕ} {B : BinaryTree ℕ}
    (hB_rng : IsRangeBST 1 B) (hB_n : B.num_nodes = N)
    {C : IntervalBlock} (hC : 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N) (D : ℕ) :
    blockSummaryFinset B C D =
      ((bstPreorderList (restrictTree B C.toSet)).take D).toFinset ∧
    (blockSummaryFinset B C D).card = min D C.size := by
  obtain ⟨hBC_rng, hBC_n, _, _⟩ := restrictTree_interval_isRangeBST hB_rng hB_n hC
  have hBC_bst := isBST_of_isRangeBST hBC_rng
  have hB_bst := isBST_of_isRangeBST hB_rng
  have hLCA := isLCAClosed_intervalBlock hB_bst C
  have heq : blockSummaryFinset B C D =
      ((bstPreorderList (restrictTree B C.toSet)).take D).toFinset := by
    ext w
    simp only [blockSummaryFinset, Finset.mem_filter, preorderRank,
      one_le_and_listRank1_le_iff_mem_take, List.mem_toFinset]
    refine ⟨fun h => h.2, fun hw => ⟨?_, hw⟩⟩
    have hw_in : w ∈ restrictTree B C.toSet :=
      bstPreorderList_mem_iff.mp (List.mem_of_mem_take hw)
    exact (mem_intervalBlock_toSet_iff C w).mp
      ((mem_restrictTree_of_isLCAClosed hB_bst hLCA w).mp hw_in).2
  refine ⟨heq, ?_⟩
  rw [heq]
  have hnodup : ((bstPreorderList (restrictTree B C.toSet)).take D).Nodup :=
    (bstPreorderList_nodup_of_isBST hBC_bst).take
  rw [List.toFinset_card_of_nodup hnodup, List.length_take, bstPreorderList_length, hBC_n]

private theorem mem_take_bstPreorderList_of_subtree {t : BinaryTree ℕ} (ht : t.IsBST)
    {D a w : ℕ} (ha : a ∈ t) (hw_sub : w ∈ subtreeAtKey t a)
    (hw_take : w ∈ (bstPreorderList t).take D) :
    a ∈ (bstPreorderList t).take D := by
  induction t generalizing D with
  | nil => cases ha
  | node k l r ihl ihr =>
    cases D with
    | zero => simp at hw_take
    | succ d =>
      simp only [bstPreorderList, List.take_succ_cons, List.mem_cons] at hw_take ⊢
      rcases mem_node_iff.mp ha with rfl | hal | har
      · exact Or.inl rfl
      · right
        have hak : a < k := lt_of_IsBST_left l k r ht hal
        simp only [subtreeAtKey, hak, ↓reduceIte] at hw_sub
        have hwl : w ∈ l := mem_of_mem_subtreeAtKey hw_sub
        have hwk : w < k := lt_of_IsBST_left l k r ht hwl
        rcases hw_take with rfl | hw_app
        · exact absurd hwk (lt_irrefl _)
        · rw [List.take_append] at hw_app ⊢
          rw [List.mem_append] at hw_app ⊢
          rcases hw_app with hw_tl | hw_tr
          · exact Or.inl (ihl (IsBST_left_of_IsBST ht) hal hw_sub hw_tl)
          · have hw_in_r : w ∈ r := bstPreorderList_mem_iff.mp (List.mem_of_mem_take hw_tr)
            exact absurd (lt_trans hwk (gt_of_IsBST_right l k r ht hw_in_r)) (lt_irrefl _)
      · right
        have hka : k < a := gt_of_IsBST_right l k r ht har
        simp only [subtreeAtKey, not_lt.mpr hka.le, hka, ↓reduceIte] at hw_sub
        have hwr : w ∈ r := mem_of_mem_subtreeAtKey hw_sub
        have hkw : k < w := gt_of_IsBST_right l k r ht hwr
        rcases hw_take with rfl | hw_app
        · exact absurd hkw (lt_irrefl _)
        · rw [List.take_append] at hw_app ⊢
          rw [List.mem_append] at hw_app ⊢
          rcases hw_app with hw_tl | hw_tr
          · have hw_in_l : w ∈ l := bstPreorderList_mem_iff.mp (List.mem_of_mem_take hw_tl)
            exact absurd (lt_trans (lt_of_IsBST_left l k r ht hw_in_l) hkw) (lt_irrefl _)
          · exact Or.inr (ihr (IsBST_right_of_IsBST ht) har hw_sub hw_tr)

private theorem consecutiveBlocks_pairwise {blocks : List IntervalBlock}
    (hlo : ∀ C ∈ blocks, C.lo ≤ C.hi) (hcons : ConsecutiveBlocks blocks) :
    blocks.Pairwise (fun C₁ C₂ => C₁.hi < C₂.lo) := by
  induction blocks with
  | nil => exact List.Pairwise.nil
  | cons C₁ rest ih =>
    cases rest with
    | nil => exact List.pairwise_singleton _ C₁
    | cons C₂ rest' =>
      rcases hcons with ⟨h12, hcons'⟩
      have hp := ih (fun C hC => hlo C (List.mem_cons_of_mem C₁ hC)) hcons'
      rw [List.pairwise_cons] at hp ⊢
      refine ⟨fun C hC => ?_, List.pairwise_cons.mpr hp⟩
      rcases List.mem_cons.mp hC with rfl | hC'
      · omega
      · have h2C := hp.1 C hC'
        have hC₂_lo := hlo C₂ (List.mem_cons_of_mem C₁ List.mem_cons_self)
        omega

private theorem partition_blocks_union {N : ℕ} {blocks : List IntervalBlock}
    (hN : 1 ≤ N) (hPart : IsContiguousBlockPartition N blocks) :
    blocks ≠ [] ∧
    blocks.Pairwise (fun C₁ C₂ => C₁.hi < C₂.lo) ∧
    blocks.foldr (fun C acc => C.toFinset ∪ acc) ∅ = Finset.Icc 1 N := by
  rcases hPart with ⟨hbnds, hcons, hends⟩
  have hne : blocks ≠ [] := by
    intro hnil
    rw [hnil] at hends
    simp at hends
    omega
  have hpw : blocks.Pairwise (fun C₁ C₂ => C₁.hi < C₂.lo) :=
    consecutiveBlocks_pairwise (fun C hC => (hbnds C hC).2.1) hcons
  have hcov : ∀ (cs : List IntervalBlock) (hne_cs : cs ≠ []),
      (∀ C ∈ cs, C.lo ≤ C.hi) → ConsecutiveBlocks cs →
      cs.foldr (fun C acc => C.toFinset ∪ acc) ∅ =
        Finset.Icc (cs.head hne_cs).lo (cs.getLast hne_cs).hi := by
    intro cs
    induction cs with
    | nil => intro h; exact absurd rfl h
    | cons C₁ rest ih =>
      intro _ hlo_cs hcons_cs
      cases rest with
      | nil =>
        simp [IntervalBlock.toFinset]
      | cons C₂ rest' =>
        rcases hcons_cs with ⟨h12, hcons'⟩
        have hne2 : C₂ :: rest' ≠ [] := List.cons_ne_nil C₂ rest'
        have ih_eq := ih hne2 (fun C hC => hlo_cs C (List.mem_cons_of_mem C₁ hC)) hcons'
        simp only [List.foldr_cons, ih_eq, List.head_cons]
        have hlast_eq : (C₁ :: C₂ :: rest').getLast (List.cons_ne_nil _ _) =
            (C₂ :: rest').getLast hne2 := List.getLast_cons hne2
        rw [hlast_eq]
        have hlast_mem : (C₂ :: rest').getLast hne2 ∈ C₂ :: rest' := List.getLast_mem hne2
        have hpw2 := consecutiveBlocks_pairwise
          (fun C hC => hlo_cs C (List.mem_cons_of_mem C₁ hC)) hcons'
        have hC₁_le : C₁.lo ≤ C₁.hi := hlo_cs C₁ List.mem_cons_self
        have hC₂_le_last : C₂.lo ≤ ((C₂ :: rest').getLast hne2).hi := by
          rcases List.mem_cons.mp hlast_mem with h_eq | h_in
          · rw [h_eq]; exact hlo_cs C₂ (List.mem_cons_of_mem C₁ List.mem_cons_self)
          · rw [List.pairwise_cons] at hpw2
            have hlt := hpw2.1 _ h_in
            have h1 := hlo_cs C₂ (List.mem_cons_of_mem C₁ List.mem_cons_self)
            have h2 := hlo_cs _ (List.mem_cons_of_mem C₁ hlast_mem)
            omega
        ext x
        simp only [Finset.mem_union, IntervalBlock.toFinset, Finset.mem_Icc]
        omega
  have hcov_blocks := hcov blocks hne (fun C hC => (hbnds C hC).2.1) hcons
  have hhead : blocks.head? = some (blocks.head hne) := List.head?_eq_some_head hne
  have hlast : blocks.getLast? = some (blocks.getLast hne) := List.getLast?_eq_some_getLast hne
  rw [hhead, hlast] at hends
  rw [hends.1, hends.2] at hcov_blocks
  exact ⟨hne, hpw, hcov_blocks⟩

private theorem pairwise_symm_of_mem {α : Type} {R : α → α → Prop}
    (hsym : ∀ {a b}, R a b → R b a) {xs : List α} (hpw : xs.Pairwise R)
    {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) : R a b := by
  induction xs with
  | nil => cases ha
  | cons x rest ih =>
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hne
    · exact hpw.1 b hb'
    · exact hsym (hpw.1 a ha')
    · exact ih hpw.2 ha' hb'

private theorem mem_preorderSummarySet_iff (B : BinaryTree ℕ) (blocks : List IntervalBlock)
    (D w : ℕ) :
    w ∈ preorderSummarySet B blocks D ↔ ∃ C ∈ blocks, w ∈ blockSummaryFinset B C D := by
  unfold preorderSummarySet
  induction blocks with
  | nil => simp
  | cons C rest ih =>
    simp only [List.foldr_cons, Finset.mem_union, List.mem_cons, exists_eq_or_imp, ← ih]
    rfl

private theorem preorder_summary_part1 {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D)
    {B : BinaryTree ℕ} (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    {blocks : List IntervalBlock} (hPart : IsContiguousBlockPartition N blocks) :
    IsLCAClosed B (preorderSummarySet B blocks D : Set ℕ) ∧
    (preorderSummaryBST B blocks D).IsBST ∧
    keyFinset (preorderSummaryBST B blocks D) = preorderSummarySet B blocks D ∧
    (preorderSummarySet B blocks D).card = (blocks.map (fun C => min D C.size)).sum ∧
    (preorderSummarySet B blocks D).card ≤ D * blocks.length ∧
    1 ≤ (preorderSummarySet B blocks D).card := by
  obtain ⟨hB_rng, hB_n⟩ := isRangeBST_of_keyFinset_Icc hB hkB
  obtain ⟨hne_blk, hpw_blk, hcov_blk⟩ := partition_blocks_union hN hPart
  have hbnds := hPart.1
  -- Disjointness of distinct blocks in `blocks`
  have hdisj_pw : blocks.Pairwise (fun C₁ C₂ => Disjoint C₁.toFinset C₂.toFinset) := by
    refine hpw_blk.imp (fun {C₁ C₂} hlt => Finset.disjoint_left.mpr (fun x hx1 hx2 => ?_))
    simp only [IntervalBlock.toFinset, Finset.mem_Icc] at hx1 hx2
    omega
  have hmem_block_iff : ∀ {C : IntervalBlock}, C ∈ blocks → ∀ {w : ℕ}, w ∈ C.toFinset →
      (w ∈ preorderSummarySet B blocks D ↔ w ∈ blockSummaryFinset B C D) := by
    intro C hC w hwC
    rw [mem_preorderSummarySet_iff]
    constructor
    · rintro ⟨C', hC', hwC'⟩
      have hwC'_fin : w ∈ C'.toFinset := (Finset.mem_filter.mp hwC').1
      by_cases heq : C' = C
      · subst heq; exact hwC'
      · exfalso
        have hdisj : Disjoint C'.toFinset C.toFinset :=
          pairwise_symm_of_mem (fun h => h.symm) hdisj_pw hC' hC heq
        exact Finset.disjoint_left.mp hdisj hwC'_fin hwC
    · intro hw; exact ⟨C, hC, hw⟩
  have hsub_Icc : preorderSummarySet B blocks D ⊆ Finset.Icc 1 N := by
    intro w hw
    rw [mem_preorderSummarySet_iff] at hw
    rcases hw with ⟨C, hC, hw_sum⟩
    have hwC : w ∈ C.toFinset := (Finset.mem_filter.mp hw_sum).1
    have hb := hbnds C hC
    simp only [IntervalBlock.toFinset, Finset.mem_Icc] at hwC ⊢
    omega
  -- Prove LCA-closure of `preorderSummarySet B blocks D` in `B`
  have hLCA : IsLCAClosed B (preorderSummarySet B blocks D : Set ℕ) := by
    intro g₁ hg₁ g₂ hg₂ hg₁S hg₂S w hlca
    simp only [Finset.mem_coe] at hg₁S hg₂S ⊢
    obtain ⟨hwB, hmin, hmax, hg₁_sub, hg₂_sub⟩ := lcaBST_spec hB hg₁ hg₂ hlca
    have hw_Icc : w ∈ Finset.Icc 1 N := by rw [← hkB, mem_keyFinset_iff]; exact hwB
    rw [← hcov_blk] at hw_Icc
    have hexC_gen : ∀ (cs : List IntervalBlock),
        w ∈ cs.foldr (fun C acc => C.toFinset ∪ acc) ∅ → ∃ C ∈ cs, w ∈ C.toFinset := by
      intro cs
      induction cs with
      | nil => simp
      | cons C rest ih =>
        simp only [List.foldr_cons, Finset.mem_union]
        rintro (hwC | hrest)
        · exact ⟨C, List.mem_cons_self, hwC⟩
        · obtain ⟨C', hC', hwC'⟩ := ih hrest
          exact ⟨C', List.mem_cons_of_mem C hC', hwC'⟩
    obtain ⟨C, hC, hwC⟩ := hexC_gen blocks hw_Icc
    rw [hmem_block_iff hC hwC]
    obtain ⟨heq_C, _⟩ := blockSummaryFinset_eq_take_toFinset hB_rng hB_n (hbnds C hC) D
    rw [heq_C, List.mem_toFinset]
    have hLCA_C := isLCAClosed_intervalBlock hB C
    have hBC_bst := isBST_restrictTree_of_isLCAClosed hB hLCA_C
    have hw_Cset : w ∈ C.toSet := (mem_intervalBlock_toSet_iff C w).mpr hwC
    have hw_BC : w ∈ restrictTree B C.toSet :=
      (mem_restrictTree_of_isLCAClosed hB hLCA_C w).mpr ⟨hwB, hw_Cset⟩
    by_cases hg₁C : g₁ ∈ C.toFinset
    · have hg₁_sum : g₁ ∈ (bstPreorderList (restrictTree B C.toSet)).take D := by
        rw [← List.mem_toFinset, ← heq_C, ← hmem_block_iff hC hg₁C]
        exact hg₁S
      have hg₁_Cset : g₁ ∈ C.toSet := (mem_intervalBlock_toSet_iff C g₁).mpr hg₁C
      have hg₁_subBC : g₁ ∈ subtreeAtKey (restrictTree B C.toSet) w := by
        rw [subtreeAtKey_restrictTree_of_isLCAClosed hB hLCA_C hwB hw_Cset]
        exact (mem_restrictTree_of_isLCAClosed (subtreeAtKey_isBST hB w)
          (isLCAClosed_subtreeAtKey hB hLCA_C w) g₁).mpr ⟨hg₁_sub, hg₁_Cset⟩
      exact mem_take_bstPreorderList_of_subtree hBC_bst hw_BC hg₁_subBC hg₁_sum
    · by_cases hg₂C : g₂ ∈ C.toFinset
      · have hg₂_sum : g₂ ∈ (bstPreorderList (restrictTree B C.toSet)).take D := by
          rw [← List.mem_toFinset, ← heq_C, ← hmem_block_iff hC hg₂C]
          exact hg₂S
        have hg₂_Cset : g₂ ∈ C.toSet := (mem_intervalBlock_toSet_iff C g₂).mpr hg₂C
        have hg₂_subBC : g₂ ∈ subtreeAtKey (restrictTree B C.toSet) w := by
          rw [subtreeAtKey_restrictTree_of_isLCAClosed hB hLCA_C hwB hw_Cset]
          exact (mem_restrictTree_of_isLCAClosed (subtreeAtKey_isBST hB w)
            (isLCAClosed_subtreeAtKey hB hLCA_C w) g₂).mpr ⟨hg₂_sub, hg₂_Cset⟩
        exact mem_take_bstPreorderList_of_subtree hBC_bst hw_BC hg₂_subBC hg₂_sum
      · rcases hBC_eq : restrictTree B C.toSet with _ | ⟨rC, lC, rC'⟩
        · rw [hBC_eq] at hw_BC; cases hw_BC
        · obtain ⟨hrC_B, hrC_C, hdom⟩ := restrictTree_interval_root_dominates hB hBC_eq
          have hw_in_rC : w ∈ subtreeAtKey B rC := hdom w hwB hw_Cset
          obtain ⟨l_rC, r_rC, hsub_rC⟩ := subtreeAtKey_mem_node hB hrC_B
          have hrC_bst : (subtreeAtKey B rC).IsBST := subtreeAtKey_isBST hB rC
          have hw_eq_rC : w = rC := by
            simp only [IntervalBlock.toFinset, Finset.mem_Icc] at hwC hg₁C hg₂C
            rw [mem_intervalBlock_toSet] at hrC_C
            have h_lo_hi : (g₁ < C.lo ∧ C.hi < g₂) ∨ (g₂ < C.lo ∧ C.hi < g₁) := by omega
            rw [hsub_rC] at hw_in_rC hrC_bst
            rcases mem_node_iff.mp hw_in_rC with hwr | hwl | hwr'
            · exact hwr
            · exfalso
              have hw_lt_rC : w < rC := lt_of_IsBST_left l_rC rC r_rC hrC_bst hwl
              have hsub_w_eq : subtreeAtKey B w = subtreeAtKey l_rC w := by
                have hgen : ∀ (T : BinaryTree ℕ), T.IsBST → rC ∈ T →
                    subtreeAtKey T rC = .node rC l_rC r_rC → w ∈ l_rC →
                    subtreeAtKey T w = subtreeAtKey l_rC w := by
                  intro T hT hrCT hsubT hwlT
                  induction T with
                  | nil => cases hrCT
                  | node tk tl tr ihtl ihtr =>
                    rcases mem_node_iff.mp hrCT with rfl | hrCtl | hrCtr
                    · simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsubT
                      injection hsubT with _ hl_eq _
                      subst hl_eq
                      simp [subtreeAtKey, hw_lt_rC]
                    · have hlt1 : rC < tk := lt_of_IsBST_left tl tk tr hT hrCtl
                      have hlt2 : w < tk := lt_trans hw_lt_rC hlt1
                      simp only [subtreeAtKey, hlt1, hlt2, ↓reduceIte] at hsubT ⊢
                      exact ihtl (IsBST_left_of_IsBST hT) hrCtl hsubT
                    · have hgt1 : tk < rC := gt_of_IsBST_right tl tk tr hT hrCtr
                      simp only [subtreeAtKey, not_lt.mpr hgt1.le, hgt1, ↓reduceIte] at hsubT
                      have hw_in_tr : w ∈ tr :=
                        mem_of_mem_subtreeAtKey (by rw [hsubT]; exact .left hwlT)
                      have hgt2 : tk < w := gt_of_IsBST_right tl tk tr hT hw_in_tr
                      simp only [subtreeAtKey, not_lt.mpr hgt2.le, hgt2, ↓reduceIte]
                      exact ihtr (IsBST_right_of_IsBST hT) hrCtr hsubT
                exact hgen B hB hrC_B hsub_rC hwl
              rw [hsub_w_eq] at hg₁_sub hg₂_sub
              have hg₁_lt : g₁ < rC :=
                lt_of_IsBST_left l_rC rC r_rC hrC_bst (mem_of_mem_subtreeAtKey hg₁_sub)
              have hg₂_lt : g₂ < rC :=
                lt_of_IsBST_left l_rC rC r_rC hrC_bst (mem_of_mem_subtreeAtKey hg₂_sub)
              omega
            · exfalso
              have hrC_lt_w : rC < w := gt_of_IsBST_right l_rC rC r_rC hrC_bst hwr'
              have hsub_w_eq : subtreeAtKey B w = subtreeAtKey r_rC w := by
                have hgen : ∀ (T : BinaryTree ℕ), T.IsBST → rC ∈ T →
                    subtreeAtKey T rC = .node rC l_rC r_rC → w ∈ r_rC →
                    subtreeAtKey T w = subtreeAtKey r_rC w := by
                  intro T hT hrCT hsubT hwrT
                  induction T with
                  | nil => cases hrCT
                  | node tk tl tr ihtl ihtr =>
                    rcases mem_node_iff.mp hrCT with rfl | hrCtl | hrCtr
                    · simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsubT
                      injection hsubT with _ _ hr_eq
                      subst hr_eq
                      simp [subtreeAtKey, not_lt.mpr hrC_lt_w.le, hrC_lt_w]
                    · have hlt1 : rC < tk := lt_of_IsBST_left tl tk tr hT hrCtl
                      simp only [subtreeAtKey, hlt1, ↓reduceIte] at hsubT
                      have hw_in_tl : w ∈ tl :=
                        mem_of_mem_subtreeAtKey (by rw [hsubT]; exact .right hwrT)
                      have hlt2 : w < tk := lt_of_IsBST_left tl tk tr hT hw_in_tl
                      simp only [subtreeAtKey, hlt2, ↓reduceIte]
                      exact ihtl (IsBST_left_of_IsBST hT) hrCtl hsubT
                    · have hgt1 : tk < rC := gt_of_IsBST_right tl tk tr hT hrCtr
                      have hgt2 : tk < w := lt_trans hgt1 hrC_lt_w
                      simp only [subtreeAtKey, not_lt.mpr hgt1.le, hgt1,
                        not_lt.mpr hgt2.le, hgt2, ↓reduceIte] at hsubT ⊢
                      exact ihtr (IsBST_right_of_IsBST hT) hrCtr hsubT
                exact hgen B hB hrC_B hsub_rC hwr'
              rw [hsub_w_eq] at hg₁_sub hg₂_sub
              have hg₁_gt : rC < g₁ :=
                gt_of_IsBST_right l_rC rC r_rC hrC_bst (mem_of_mem_subtreeAtKey hg₁_sub)
              have hg₂_gt : rC < g₂ :=
                gt_of_IsBST_right l_rC rC r_rC hrC_bst (mem_of_mem_subtreeAtKey hg₂_sub)
              omega
          subst hw_eq_rC
          cases D with
          | zero => omega
          | succ d => simp [bstPreorderList]
  -- Card calculation along disjoint `blocks`
  have hcard_eq : (preorderSummarySet B blocks D).card =
      (blocks.map (fun C => min D C.size)).sum := by
    unfold preorderSummarySet
    have hfold_card : ∀ (cs : List IntervalBlock),
        (∀ C ∈ cs, 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N) →
        cs.Pairwise (fun C₁ C₂ => Disjoint C₁.toFinset C₂.toFinset) →
        (cs.foldr (fun C acc => blockSummaryFinset B C D ∪ acc) ∅).card =
          (cs.map (fun C => min D C.size)).sum := by
      intro cs
      induction cs with
      | nil => simp
      | cons C rest ih =>
        intro hb_cs hpw_cs
        rw [List.pairwise_cons] at hpw_cs
        simp only [List.foldr_cons, List.map_cons, List.sum_cons]
        have hdisj_head : Disjoint (blockSummaryFinset B C D)
            (rest.foldr (fun C' acc => blockSummaryFinset B C' D ∪ acc) ∅) := by
          refine Finset.disjoint_left.mpr (fun x hx1 hx2 => ?_)
          have hxC : x ∈ C.toFinset := (Finset.mem_filter.mp hx1).1
          have hex_rest : ∃ C' ∈ rest, x ∈ C'.toFinset := by
            clear ih hpw_cs hb_cs
            induction rest with
            | nil => simp at hx2
            | cons C' rs ihrs =>
              simp only [List.foldr_cons, Finset.mem_union] at hx2
              rcases hx2 with h1 | h2
              · exact ⟨C', List.mem_cons_self, (Finset.mem_filter.mp h1).1⟩
              · obtain ⟨C'', hC'', hx''⟩ := ihrs h2
                exact ⟨C'', List.mem_cons_of_mem C' hC'', hx''⟩
          obtain ⟨C', hC', hxC'⟩ := hex_rest
          exact Finset.disjoint_left.mp (hpw_cs.1 C' hC') hxC hxC'
        rw [Finset.card_union_of_disjoint hdisj_head,
          (blockSummaryFinset_eq_take_toFinset hB_rng hB_n (hb_cs C List.mem_cons_self) D).2,
          ih (fun C' hC' => hb_cs C' (List.mem_cons_of_mem C hC')) hpw_cs.2]
    exact hfold_card blocks hbnds hdisj_pw
  have hcard_le : (preorderSummarySet B blocks D).card ≤ D * blocks.length := by
    rw [hcard_eq]
    have hsum_le : ∀ (cs : List IntervalBlock),
        (cs.map (fun C => min D C.size)).sum ≤ D * cs.length := by
      intro cs
      induction cs with
      | nil => simp
      | cons C rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have hmin : min D C.size ≤ D := Nat.min_le_left D C.size
        have hmul : D * (rest.length + 1) = D + D * rest.length := by
          rw [Nat.mul_succ, Nat.add_comm]
        rw [hmul]
        exact Nat.add_le_add hmin ih
    exact hsum_le blocks
  have hcard_pos : 1 ≤ (preorderSummarySet B blocks D).card := by
    rw [hcard_eq]
    cases blocks with
    | nil => exact absurd rfl hne_blk
    | cons C₁ rest =>
      simp only [List.map_cons, List.sum_cons]
      obtain ⟨_, _, _, hsz_pos⟩ :=
        restrictTree_interval_isRangeBST hB_rng hB_n (hbnds C₁ List.mem_cons_self)
      omega
  refine ⟨hLCA, isBST_restrictTree_of_isLCAClosed hB hLCA, ?_, hcard_eq, hcard_le, hcard_pos⟩
  exact keyFinset_restrictTree_of_isLCAClosed hB hLCA (hkB ▸ hsub_Icc)

/-! ## 5. `normalizeBST`, Rank Formula, and `lem_4_2_preorder_global` -/

private theorem toKeyList_map {α β : Type} (t : BinaryTree α) (f : α → β) :
    (t.map f).toKeyList = t.toKeyList.map f := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp [BinaryTree.map, toKeyList_node, ihl, ihr]

private theorem maxKey?_map {α β : Type} (t : BinaryTree α) (f : α → β) :
    (t.map f).maxKey? = t.maxKey?.map f := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    cases hr : r.maxKey? with
    | none =>
      rw [hr] at ihr
      simp [BinaryTree.map, BinaryTree.maxKey?, hr, ihr]
    | some m =>
      rw [hr] at ihr
      simp [BinaryTree.map, BinaryTree.maxKey?, hr, ihr]

private theorem subtreeAtKey_map_of_strictMono_on {t : BinaryTree ℕ} {f : ℕ → ℕ}
    (ht : t.IsBST) (hf : ∀ a ∈ t, ∀ b ∈ t, a < b → f a < f b)
    {x : ℕ} (hx : x ∈ t) :
    subtreeAtKey (t.map f) (f x) = (subtreeAtKey t x).map f := by
  induction t with
  | nil => cases hx
  | node k l r ihl ihr =>
    rcases mem_node_iff.mp hx with rfl | hxl | hxr
    · simp [BinaryTree.map, subtreeAtKey]
    · have hxk : x < k := lt_of_IsBST_left l k r ht hxl
      have hfxk : f x < f k := hf x (.left hxl) k .here hxk
      simpa [BinaryTree.map, subtreeAtKey, hxk, hfxk] using
        ihl (IsBST_left_of_IsBST ht) (fun a ha b hb h => hf a (.left ha) b (.left hb) h) hxl
    · have hkx : k < x := gt_of_IsBST_right l k r ht hxr
      have hfkx : f k < f x := hf k .here x (.right hxr) hkx
      simpa [BinaryTree.map, subtreeAtKey, not_lt.mpr hkx.le, hkx, not_lt.mpr hfkx.le, hfkx] using
        ihr (IsBST_right_of_IsBST ht) (fun a ha b hb h => hf a (.right ha) b (.right hb) h) hxr

private theorem map_succ_range' (a n : ℕ) :
    (List.range' a n).map (· + 1) = List.range' (a + 1) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    change (a + 1) :: (List.range' (a + 1) n).map (· + 1) = (a + 1) :: List.range' (a + 2) n
    rw [ih (a + 1)]

private theorem map_listRank1_eq_range' {α : Type} [DecidableEq α] {xs : List α}
    (hnodup : xs.Nodup) :
    xs.map (listRank1 xs) = List.range' 1 xs.length := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rw [List.nodup_cons] at hnodup
    rw [List.map_cons, List.length_cons]
    have hhead : listRank1 (y :: ys) y = 1 := by simp [listRank1]
    have hmap_tl : ys.map (listRank1 (y :: ys)) = (ys.map (listRank1 ys)).map (· + 1) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro z hz
      have hzy : z ≠ y := fun h => hnodup.1 (h ▸ hz)
      have hnz : listRank1 ys z ≠ 0 := fun h0 => ((listRank1_eq_zero_iff ys z).mp h0) hz
      simp [listRank1, hzy, hnz]
    rw [hhead, hmap_tl, ih hnodup.2, map_succ_range']
    rfl

private theorem listRank1_eq_card_filter_le {xs : List ℕ}
    (hsort : xs.Pairwise (· < ·)) {x : ℕ} (hx : x ∈ xs) :
    listRank1 xs x = (xs.toFinset.filter (· ≤ x)).card := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.pairwise_cons] at hsort
    by_cases hxy : x = y
    · subst hxy
      have hfilt : (x :: ys).toFinset.filter (· ≤ x) = {x} := by
        ext z
        simp only [List.toFinset_cons, Finset.mem_filter, Finset.mem_insert,
          List.mem_toFinset, Finset.mem_singleton]
        constructor
        · rintro ⟨ rfl | hzys, hzx ⟩
          · rfl
          · exact absurd (lt_of_lt_of_le (hsort.1 z hzys) hzx) (lt_irrefl _)
        · rintro rfl
          exact ⟨Or.inl rfl, le_rfl⟩
      rw [hfilt]
      simp [listRank1]
    · have hzys : x ∈ ys := by
        rcases List.mem_cons.mp hx with rfl | h
        · exact absurd rfl hxy
        · exact h
      have hyx : y < x := hsort.1 x hzys
      have hnz : listRank1 ys x ≠ 0 := fun h0 => ((listRank1_eq_zero_iff ys x).mp h0) hzys
      have hy_not_in : y ∉ ys.toFinset.filter (· ≤ x) := by
        simp only [Finset.mem_filter, List.mem_toFinset]
        rintro ⟨hy_in, _⟩
        exact lt_irrefl y (hsort.1 y hy_in)
      have hfilt : (y :: ys).toFinset.filter (· ≤ x) =
          insert y (ys.toFinset.filter (· ≤ x)) := by
        ext z
        simp only [List.toFinset_cons, Finset.mem_filter, Finset.mem_insert, List.mem_toFinset]
        constructor
        · rintro ⟨rfl | hzin, hzx⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hzin, hzx⟩
        · rintro (rfl | ⟨hzin, hzx⟩)
          · exact ⟨Or.inl rfl, hyx.le⟩
          · exact ⟨Or.inr hzin, hzx⟩
      have hdisj : Disjoint ({y} : Finset ℕ) (ys.toFinset.filter (· ≤ x)) :=
        Finset.disjoint_singleton_left.mpr hy_not_in
      have hcard_ins : (insert y (ys.toFinset.filter (· ≤ x))).card =
          (ys.toFinset.filter (· ≤ x)).card + 1 := by
        have hunion : insert y (ys.toFinset.filter (· ≤ x)) =
            ({y} : Finset ℕ) ∪ ys.toFinset.filter (· ≤ x) := by
          ext z; simp
        rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
        omega
      simp only [listRank1, hxy, hnz, ↓reduceIte]
      rw [hfilt, hcard_ins, ih hsort.2 hzys]

private theorem card_filter_le_strictMono_on {S : Finset ℕ} {a b : ℕ}
    (hb : b ∈ S) (hab : a < b) :
    (S.filter (· ≤ a)).card < (S.filter (· ≤ b)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨fun z hz => ?_, fun heq => ?_⟩
  · simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, le_trans hz.2 hab.le⟩
  · have hb_in : b ∈ S.filter (· ≤ b) := Finset.mem_filter.mpr ⟨hb, le_rfl⟩
    rw [← heq, Finset.mem_filter] at hb_in
    exact not_lt_of_ge hb_in.2 hab

private theorem normalizeBST_spec {G : BinaryTree ℕ} (hG : G.IsBST) :
    IsRangeBST 1 (normalizeBST G) ∧
    (normalizeBST G).IsBST ∧
    keyFinset (normalizeBST G) = Finset.Icc 1 (keyFinset G).card ∧
    (∀ x ∈ keyFinset G,
      listRank1 G.toKeyList x = ((keyFinset G).filter (· ≤ x)).card) := by
  have hsort : G.toKeyList.Pairwise (· < ·) := (IsBST_iff_toKeyList_sorted G).mp hG
  have hnodup : G.toKeyList.Nodup := toKeyList_nodup_of_isBST hG
  have hkl : (normalizeBST G).toKeyList = List.range' 1 G.num_nodes := by
    simp only [normalizeBST, toKeyList_map]
    rw [map_listRank1_eq_range' hnodup, ← num_nodes_eq_length_toKeyList]
  have hn : (normalizeBST G).num_nodes = G.num_nodes := by
    rw [num_nodes_eq_length_toKeyList, hkl, List.length_range']
  have hrng : IsRangeBST 1 (normalizeBST G) := isRangeBST_iff_toKeyList.mpr (hn ▸ hkl)
  have hbst : (normalizeBST G).IsBST := isBST_of_isRangeBST hrng
  have hk : keyFinset (normalizeBST G) = Finset.Icc 1 (keyFinset G).card := by
    rw [card_keyFinset_of_isBST hG]
    ext x
    rw [mem_keyFinset_iff, mem_of_isRangeBST hrng, hn, Finset.mem_Icc]
    omega
  refine ⟨hrng, hbst, hk, fun x hx => ?_⟩
  have hx_kl : x ∈ G.toKeyList := mem_iff_mem_toKeyList.mp (mem_keyFinset_iff.mp hx)
  rw [listRank1_eq_card_filter_le hsort hx_kl, toFinset_toKeyList_eq_keyFinset]

private theorem exists_mem_of_card_filter_le {G : BinaryTree ℕ} (hG : G.IsBST)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 (keyFinset G).card) :
    ∃ x ∈ keyFinset G, ((keyFinset G).filter (· ≤ x)).card = j := by
  obtain ⟨_, _, hk, hrk⟩ := normalizeBST_spec hG
  rw [← hk, mem_keyFinset_iff, mem_iff_mem_toKeyList] at hj
  simp only [normalizeBST, toKeyList_map, List.mem_map] at hj
  rcases hj with ⟨x, hx_kl, rfl⟩
  have hx_kf : x ∈ keyFinset G := mem_keyFinset_iff.mpr (mem_iff_mem_toKeyList.mpr hx_kl)
  exact ⟨x, hx_kf, (hrk x hx_kf).symm⟩

private theorem rightReach_normalizeBST_restrictTree {N : ℕ} {B : BinaryTree ℕ}
    (hB_rng : IsRangeBST 1 B) (hB_n : B.num_nodes = N)
    {S : Finset ℕ} (hsub : S ⊆ Finset.Icc 1 N) (hLCA : IsLCAClosed B (S : Set ℕ))
    {x : ℕ} (hxS : x ∈ S) :
    rightReach (normalizeBST (restrictTree B (S : Set ℕ))) ((S.filter (· ≤ x)).card) =
      (S.filter (· ≤ rightReach B x)).card := by
  let G := restrictTree B (S : Set ℕ)
  change rightReach (normalizeBST G) ((S.filter (· ≤ x)).card) =
    (S.filter (· ≤ rightReach B x)).card
  have hB : B.IsBST := isBST_of_isRangeBST hB_rng
  have hG : G.IsBST := isBST_restrictTree_of_isLCAClosed hB hLCA
  have hkB : keyFinset B = Finset.Icc 1 N := by
    ext z
    rw [mem_keyFinset_iff, mem_of_isRangeBST hB_rng, hB_n, Finset.mem_Icc]
    omega
  have hkG : keyFinset G = S := keyFinset_restrictTree_of_isLCAClosed hB hLCA (hkB ▸ hsub)
  obtain ⟨_, _, _, hrk⟩ := normalizeBST_spec hG
  rw [hkG] at hrk
  have hxG : x ∈ G := mem_keyFinset_iff.mp (hkG ▸ hxS)
  have hxB : x ∈ B := mem_keyFinset_iff.mp (hkB ▸ hsub hxS)
  have hf_mono : ∀ a ∈ G, ∀ b ∈ G, a < b →
      listRank1 G.toKeyList a < listRank1 G.toKeyList b := by
    intro a ha b hb hab
    have haS : a ∈ S := hkG ▸ mem_keyFinset_iff.mpr ha
    have hbS : b ∈ S := hkG ▸ mem_keyFinset_iff.mpr hb
    rw [hrk a haS, hrk b hbS]
    exact card_filter_le_strictMono_on hbS hab
  have hj_eq : (S.filter (· ≤ x)).card = listRank1 G.toKeyList x := (hrk x hxS).symm
  rw [hj_eq]
  have hsub_map : subtreeAtKey (normalizeBST G) (listRank1 G.toKeyList x) =
      (subtreeAtKey G x).map (listRank1 G.toKeyList) :=
    subtreeAtKey_map_of_strictMono_on hG hf_mono hxG
  have hsubG_bst : (subtreeAtKey G x).IsBST := subtreeAtKey_isBST hG x
  obtain ⟨lG, rG, hsubG_node⟩ := subtreeAtKey_mem_node hG hxG
  rcases maxKey?_isBST_spec hsubG_bst with ⟨hemp, _⟩ | ⟨m, hm_subG, hmaxG, hubG⟩
  · rw [hsubG_node] at hemp; cases hemp
  · have hmG : m ∈ G := mem_of_mem_subtreeAtKey hm_subG
    have hmS : m ∈ S := hkG ▸ mem_keyFinset_iff.mpr hmG
    have hrr_norm : rightReach (normalizeBST G) (listRank1 G.toKeyList x) =
        listRank1 G.toKeyList m := by
      simp [rightReach, hsub_map, maxKey?_map, hmaxG]
    rw [hrr_norm, hrk m hmS]
    congr 1
    have hsubG_eq : subtreeAtKey G x = restrictTree (subtreeAtKey B x) (S : Set ℕ) :=
      subtreeAtKey_restrictTree_of_isLCAClosed hB hLCA hxB hxS
    have hmem_subG : ∀ z : ℕ, z ∈ subtreeAtKey G x ↔ z ∈ subtreeAtKey B x ∧ z ∈ S := by
      intro z
      rw [hsubG_eq]
      exact mem_restrictTree_of_isLCAClosed (subtreeAtKey_isBST hB x)
        (isLCAClosed_subtreeAtKey hB hLCA x) z
    obtain ⟨a_x, _, hax_le_x, _, hrr_end, _, hsubB_rng⟩ := isRangeBST_subtreeAtKey hB_rng hxB
    have hmem_subB : ∀ z : ℕ, z ∈ subtreeAtKey B x ↔ a_x ≤ z ∧ z ≤ rightReach B x := by
      intro z
      rw [mem_of_isRangeBST hsubB_rng]
      omega
    have hm_le_rr : m ≤ rightReach B x := ((hmem_subB m).mp ((hmem_subG m).mp hm_subG).1).2
    have hx_le_m : x ≤ m := hubG x (by rw [hsubG_node]; exact .here)
    ext z
    simp only [Finset.mem_filter]
    refine ⟨fun ⟨hzS, hzm⟩ => ⟨hzS, le_trans hzm hm_le_rr⟩, fun ⟨hzS, hzrr⟩ => ⟨hzS, ?_⟩⟩
    by_contra hgt
    have hmz : m < z := Nat.lt_of_not_le hgt
    have hz_in_subB : z ∈ subtreeAtKey B x :=
      (hmem_subB z).mpr ⟨by omega, hzrr⟩
    have hz_in_subG : z ∈ subtreeAtKey G x := (hmem_subG z).mpr ⟨hz_in_subB, hzS⟩
    exact absurd (hubG z hz_in_subG) (not_le_of_gt hmz)

private theorem subtreeAtKey_idem_of_mem {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) {u z : α} (hz : z ∈ subtreeAtKey t u) :
    subtreeAtKey t z = subtreeAtKey (subtreeAtKey t u) z := by
  induction t with
  | nil => cases hz
  | node k l r ihl ihr =>
    simp only [subtreeAtKey] at hz
    split_ifs at hz with huk hku
    · have hzl : z ∈ l := mem_of_mem_subtreeAtKey hz
      have hzk : z < k := lt_of_IsBST_left l k r ht hzl
      simpa [subtreeAtKey, huk, hzk] using ihl (IsBST_left_of_IsBST ht) hz
    · have hzr : z ∈ r := mem_of_mem_subtreeAtKey hz
      have hkz : k < z := gt_of_IsBST_right l k r ht hzr
      simpa [subtreeAtKey, not_lt.mpr hku.le, hku, not_lt.mpr hkz.le, hkz] using
        ihr (IsBST_right_of_IsBST ht) hz
    · have h_uk : u = k := le_antisymm (not_lt.mp hku) (not_lt.mp huk)
      subst h_uk
      simp [subtreeAtKey]

private theorem rightReach_le_of_mem_subtreeAtKey {t : BinaryTree ℕ}
    (ht : t.IsBST) {u z : ℕ} (hz : z ∈ subtreeAtKey t u) :
    rightReach t z ≤ rightReach t u := by
  have hsub_eq := subtreeAtKey_idem_of_mem ht hz
  have hu_bst : (subtreeAtKey t u).IsBST := subtreeAtKey_isBST ht u
  have hz_bst : (subtreeAtKey t z).IsBST := subtreeAtKey_isBST ht z
  rcases maxKey?_isBST_spec hz_bst with ⟨_, hnone⟩ | ⟨mz, hmz, hmaxz, _⟩
  · simp [rightReach, hnone]
  · rcases maxKey?_isBST_spec hu_bst with ⟨hemp, _⟩ | ⟨mu, _, hmaxu, hubu⟩
    · rw [hemp] at hz; cases hz
    · rw [hsub_eq] at hmz
      have hmz_u : mz ∈ subtreeAtKey t u := mem_of_mem_subtreeAtKey hmz
      simp only [rightReach, hmaxz, hmaxu, Option.getD_some]
      exact hubu mz hmz_u

private theorem not_mem_take_bstPreorderList_of_gt_getElem :
    ∀ (bt : BinaryTree ℕ) (a m z y : ℕ),
      IsRangeBST a bt →
      (hm : m < (bstPreorderList bt).length) →
      z ∈ (bstPreorderList bt).take m →
      (bstPreorderList bt)[m] < z →
      z < y →
      y ≤ rightReach bt z →
      y ∉ (bstPreorderList bt).take m := by
  intro bt
  induction bt with
  | nil =>
    intro _ m _ _ _ hm
    simp [bstPreorderList] at hm
  | node k L R ihL ihR =>
    intro a m z y ⟨hk, hL, hR⟩ hm hz_mem hx0_lt hzy hy_max
    rcases m with _ | m'
    · simp at hz_mem
    · simp only [bstPreorderList, List.length_cons, List.length_append] at hm
      have hm'_len : m' < (bstPreorderList L ++ bstPreorderList R).length := by
        rw [List.length_append]
        omega
      simp only [bstPreorderList, List.getElem_cons_succ] at hx0_lt
      change z ∈ k :: (bstPreorderList L ++ bstPreorderList R).take m' at hz_mem
      change y ∉ k :: (bstPreorderList L ++ bstPreorderList R).take m'
      have hm'_lt_L_of_lt_k :
          (bstPreorderList L ++ bstPreorderList R)[m']'hm'_len < k →
          m' < (bstPreorderList L).length := by
        intro hlt_k
        by_contra hge
        have hle : (bstPreorderList L).length ≤ m' := by omega
        rw [List.getElem_append_right hle] at hlt_k
        have hmem_R :
            (bstPreorderList R)[m' - (bstPreorderList L).length]'(by omega) ∈ bstPreorderList R :=
          List.getElem_mem _
        rw [bstPreorderList_mem_iff, mem_of_isRangeBST hR] at hmem_R
        omega
      rcases lt_trichotomy z k with hzk | rfl | hkz
      · have hm'_L : m' < (bstPreorderList L).length := hm'_lt_L_of_lt_k (by omega)
        rw [List.take_append_of_le_length (by omega)] at hz_mem ⊢
        rw [List.getElem_append_left hm'_L] at hx0_lt
        simp only [List.mem_cons] at hz_mem ⊢
        have hz_L : z ∈ (bstPreorderList L).take m' := by
          rcases hz_mem with rfl | hz'
          · omega
          · exact hz'
        have hz_in_L : z ∈ L := bstPreorderList_mem_iff.mp (List.mem_of_mem_take hz_L)
        simp only [rightReach_node_eq, hzk, ↓reduceIte] at hy_max
        obtain ⟨a_z, _, _, _, hrr_end, hend_le, _⟩ := isRangeBST_subtreeAtKey hL hz_in_L
        rintro (rfl | hy_mem)
        · omega
        · exact ihL a m' z y hL hm'_L hz_L hx0_lt hzy hy_max hy_mem
      · have hm'_L : m' < (bstPreorderList L).length := hm'_lt_L_of_lt_k hx0_lt
        rw [List.take_append_of_le_length (by omega)]
        simp only [List.mem_cons]
        rintro (rfl | hy_mem)
        · omega
        · have hy_in_L : y ∈ L := bstPreorderList_mem_iff.mp (List.mem_of_mem_take hy_mem)
          rw [mem_of_isRangeBST hL] at hy_in_L
          omega
      · have hL_le_m' : (bstPreorderList L).length ≤ m' := by
          by_contra hlt_L
          rw [List.take_append_of_le_length (by omega)] at hz_mem
          simp only [List.mem_cons] at hz_mem
          rcases hz_mem with rfl | hz_L
          · omega
          · have hz_in_L : z ∈ L := bstPreorderList_mem_iff.mp (List.mem_of_mem_take hz_L)
            rw [mem_of_isRangeBST hL] at hz_in_L
            omega
        have hm''_R : m' - (bstPreorderList L).length < (bstPreorderList R).length := by omega
        rw [List.take_append] at hz_mem ⊢
        rw [List.take_of_length_le hL_le_m'] at hz_mem ⊢
        rw [List.getElem_append_right hL_le_m'] at hx0_lt
        simp only [List.mem_cons, List.mem_append] at hz_mem ⊢
        have hz_R : z ∈ (bstPreorderList R).take (m' - (bstPreorderList L).length) := by
          rcases hz_mem with rfl | hz_L | hz_R
          · omega
          · rw [bstPreorderList_mem_iff, mem_of_isRangeBST hL] at hz_L
            omega
          · exact hz_R
        simp only [rightReach_node_eq, not_lt.mpr hkz.le, hkz, ↓reduceIte] at hy_max
        rintro (rfl | hy_L | hy_R)
        · omega
        · rw [bstPreorderList_mem_iff, mem_of_isRangeBST hL] at hy_L
          omega
        · exact ihR (k + 1) (m' - (bstPreorderList L).length) z y hR hm''_R hz_R hx0_lt hzy hy_max hy_R

private theorem bstPreorderList_rotateRightEdge_infix :
    ∀ (T : BinaryTree ℕ) (a u v : ℕ),
      IsRangeBST a T → IsRightRotEdge T u v →
      ∃ (a_u : ℕ) (Aq Mq Rq : BinaryTree ℕ) (P_pre S_pre : List ℕ),
        a ≤ a_u ∧
        a_u + (BinaryTree.node v (.node u Aq Mq) Rq).num_nodes ≤ a + T.num_nodes ∧
        IsRangeBST a_u (.node v (.node u Aq Mq) Rq) ∧
        subtreeAtKey T v = .node v (.node u Aq Mq) Rq ∧
        (∀ z : ℕ, a_u ≤ z → z < a_u + (BinaryTree.node v (.node u Aq Mq) Rq).num_nodes →
          rightReach T z = rightReach (.node v (.node u Aq Mq) Rq) z) ∧
        bstPreorderList T =
          P_pre ++ bstPreorderList (.node v (.node u Aq Mq) Rq) ++ S_pre ∧
        bstPreorderList (rotateRightEdge T u v) =
          P_pre ++ bstPreorderList (.node u Aq (.node v Mq Rq)) ++ S_pre := by
  intro T
  induction T with
  | nil =>
    intro _ _ _ _ ⟨_, _, _, hv, _⟩
    cases hv
  | node k L R ihL ihR =>
    intro a u v hT he
    have hbst := isBST_of_isRangeBST hT
    rcases hT with ⟨hk, hL, hR⟩
    rcases (isRightRotEdge_node_iff hbst u v).mp he with
      ⟨hvlt, heL⟩ | ⟨hvgt, heR⟩ | ⟨rfl, Aq, Mq, rfl⟩
    · obtain ⟨a_u, Aq, Mq, Rq, P_pre, S_pre, ha1, ha2, hs, hsubL, hrrL, hp1, hp2⟩ :=
        ihL a u v hL heL
      have hrot : rotateRightEdge (.node k L R) u v = .node k (rotateRightEdge L u v) R := by
        simp [rotateRightEdge, hvlt]
      refine ⟨a_u, Aq, Mq, Rq, k :: P_pre, S_pre ++ bstPreorderList R,
        ha1, by simp only [num_nodes_node] at ha2 ⊢; omega, hs,
        by simpa [subtreeAtKey, hvlt] using hsubL, ?_, ?_, ?_⟩
      · intro z hz1 hz2
        have hzk : z < k := by omega
        simpa [rightReach_node_eq, hzk] using hrrL z hz1 hz2
      · simp [bstPreorderList, hp1, List.append_assoc]
      · rw [hrot]
        simp [bstPreorderList, hp2, List.append_assoc]
    · obtain ⟨a_u, Aq, Mq, Rq, P_pre, S_pre, ha1, ha2, hs, hsubR, hrrR, hp1, hp2⟩ :=
        ihR (k + 1) u v hR heR
      have hrot : rotateRightEdge (.node k L R) u v = .node k L (rotateRightEdge R u v) := by
        simp [rotateRightEdge, not_lt.mpr hvgt.le, hvgt]
      refine ⟨a_u, Aq, Mq, Rq, (k :: bstPreorderList L) ++ P_pre, S_pre,
        by omega, by simp only [num_nodes_node] at ha2 ⊢; omega, hs,
        by simpa [subtreeAtKey, not_lt.mpr hvgt.le, hvgt] using hsubR, ?_, ?_, ?_⟩
      · intro z hz1 hz2
        have hkz : k < z := by omega
        simpa [rightReach_node_eq, not_lt.mpr hkz.le, hkz] using hrrR z hz1 hz2
      · simp [bstPreorderList, hp1, List.append_assoc]
      · rw [hrot]
        simp [bstPreorderList, hp2, List.append_assoc]
    · have hrot : rotateRightEdge (.node v (.node u Aq Mq) R) u v =
          .node u Aq (.node v Mq R) := by
        simp [rotateRightEdge]
      refine ⟨a, Aq, Mq, R, [], [], le_rfl, le_rfl, ⟨hk, hL, hR⟩,
        by simp [subtreeAtKey], fun _ _ _ => rfl, by simp, ?_⟩
      rw [hrot]
      simp

private theorem filter_le_card_swap {S S' : Finset ℕ} {x' v : ℕ}
    (hx'v : x' < v) (hx'S : x' ∉ S) (hvS : v ∈ S)
    (hS' : S' = insert x' (S.erase v)) (b : ℕ) :
    ((b < x' ∨ v ≤ b) → (S'.filter (· ≤ b)).card = (S.filter (· ≤ b)).card) ∧
    ((x' ≤ b ∧ b < v) → (S'.filter (· ≤ b)).card = (S.filter (· ≤ b)).card + 1) ∧
    (S.filter (· ≤ b)).card ≤ (S'.filter (· ≤ b)).card := by
  have h1 : (b < x' ∨ v ≤ b) → (S'.filter (· ≤ b)).card = (S.filter (· ≤ b)).card := by
    rintro (hbx' | hvb)
    · have hfeq : S'.filter (· ≤ b) = S.filter (· ≤ b) := by
        rw [hS']
        ext z
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | ⟨_, hzS⟩, hzb⟩
          · omega
          · exact ⟨hzS, hzb⟩
        · rintro ⟨hzS, hzb⟩
          exact ⟨Or.inr ⟨by omega, hzS⟩, hzb⟩
      rw [hfeq]
    · let E := (S.filter (· ≤ b)).erase v
      have h1_eq : insert v E = S.filter (· ≤ b) :=
        Finset.insert_erase (Finset.mem_filter.mpr ⟨hvS, hvb⟩)
      have h2_eq : S'.filter (· ≤ b) = insert x' E := by
        rw [hS']
        ext z
        simp only [E, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | ⟨hzv, hzS⟩, hzb⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hzv, hzS, hzb⟩
        · rintro (rfl | ⟨hzv, hzS, hzb⟩)
          · exact ⟨Or.inl rfl, by omega⟩
          · exact ⟨Or.inr ⟨hzv, hzS⟩, hzb⟩
      have hvE : v ∉ E := Finset.notMem_erase v _
      have hx'E : x' ∉ E := fun h => hx'S (Finset.mem_filter.mp (Finset.mem_of_mem_erase h)).1
      have hc1 : (insert v E).card = E.card + 1 := by
        have hu : insert v E = ({v} : Finset ℕ) ∪ E := by ext z; simp
        rw [hu, Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hvE),
          Finset.card_singleton]
        omega
      have hc2 : (insert x' E).card = E.card + 1 := by
        have hu : insert x' E = ({x'} : Finset ℕ) ∪ E := by ext z; simp
        rw [hu, Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hx'E),
          Finset.card_singleton]
        omega
      exact (congrArg Finset.card h2_eq).trans
        (hc2.trans (hc1.symm.trans (congrArg Finset.card h1_eq)))
  have h2 : (x' ≤ b ∧ b < v) → (S'.filter (· ≤ b)).card = (S.filter (· ≤ b)).card + 1 := by
    rintro ⟨hx'b, hbv⟩
    have hfeq : S'.filter (· ≤ b) = insert x' (S.filter (· ≤ b)) := by
      rw [hS']
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨rfl | ⟨_, hzS⟩, hzb⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hzS, hzb⟩
      · rintro (rfl | ⟨hzS, hzb⟩)
        · exact ⟨Or.inl rfl, hx'b⟩
        · exact ⟨Or.inr ⟨by omega, hzS⟩, hzb⟩
    have hx'F : x' ∉ S.filter (· ≤ b) := fun h => hx'S (Finset.mem_filter.mp h).1
    have hu : insert x' (S.filter (· ≤ b)) = ({x'} : Finset ℕ) ∪ S.filter (· ≤ b) := by
      ext z; simp
    rw [hfeq, hu,
      Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hx'F),
      Finset.card_singleton]
    omega
  refine ⟨h1, h2, ?_⟩
  by_cases hbx' : b < x'
  · rw [h1 (Or.inl hbx')]
  · by_cases hbv : b < v
    · rw [h2 ⟨by omega, hbv⟩]; omega
    · rw [h1 (Or.inr (by omega))]

/-- **Lemma 4.2** (`lem:preorder-global`, Preorder-`D` Summary BST Simulation):
(1) `𝒢(B)` is `LCA`-closed in `B` with `|𝒢(B)| = ∑_q min(D, |C_q|) ≤ D K`, so `G(B) = B|_{𝒢(B)}`
is a valid BST on `𝒢(B)`;
(2) Under any right single rotation `[u, v]` on `B`, `normalizeBST (G(B'))` is reachable from
`normalizeBST (G(B))` by right single rotations, and inter-block rotations preserve `𝒢` while
acting directly as `[u, v]` (when `u, v ∈ 𝒢(B)`) or a no-op (otherwise) on `G(B)`. -/
theorem lem_4_2_preorder_global (N D : ℕ) (hN : 1 ≤ N) (hD : 1 ≤ D)
    (B : BinaryTree ℕ) (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    (blocks : List IntervalBlock) (hPart : IsContiguousBlockPartition N blocks) :
    -- Part (1)
    (IsLCAClosed B (preorderSummarySet B blocks D : Set ℕ) ∧
     (preorderSummaryBST B blocks D).IsBST ∧
     keyFinset (preorderSummaryBST B blocks D) = preorderSummarySet B blocks D ∧
     (preorderSummarySet B blocks D).card = (blocks.map (fun C => min D C.size)).sum ∧
     (preorderSummarySet B blocks D).card ≤ D * blocks.length) ∧
    -- Part (2)
    (∀ u v : ℕ, u < v → IsRightRotEdge B u v →
      let B' := rotateRightEdge B u v
      RightRotReachable
        (normalizeBST (preorderSummaryBST B blocks D))
        (normalizeBST (preorderSummaryBST B' blocks D)) ∧
      ((∀ C ∈ blocks, ¬ (u ∈ C.toFinset ∧ v ∈ C.toFinset)) →
        preorderSummarySet B' blocks D = preorderSummarySet B blocks D ∧
        (u ∈ preorderSummarySet B blocks D ∧ v ∈ preorderSummarySet B blocks D →
          IsRightRotEdge (preorderSummaryBST B blocks D) u v ∧
          preorderSummaryBST B' blocks D =
            rotateRightEdge (preorderSummaryBST B blocks D) u v) ∧
        (¬ (u ∈ preorderSummarySet B blocks D ∧ v ∈ preorderSummarySet B blocks D) →
          preorderSummaryBST B' blocks D = preorderSummaryBST B blocks D))) := by
  obtain ⟨hLCA, hG_bst, hkG, hcard, hcard_le, hM_pos⟩ :=
    preorder_summary_part1 hN hD hB hkB hPart
  refine ⟨⟨hLCA, hG_bst, hkG, hcard, hcard_le⟩, ?_⟩
  intro u v huv he
  dsimp only
  let B' := rotateRightEdge B u v
  have hB' : B'.IsBST := isBST_rotateRightEdge hB u v
  have hkB' : keyFinset B' = Finset.Icc 1 N := (keyFinset_rotateRightEdge B u v).trans hkB
  obtain ⟨hLCA', hG'_bst, hkG', hcard', _, _⟩ :=
    preorder_summary_part1 hN hD hB' hkB' hPart
  obtain ⟨hB_rng, hB_n⟩ := isRangeBST_of_keyFinset_Icc hB hkB
  obtain ⟨hB'_rng, hB'_n⟩ := isRangeBST_of_keyFinset_Icc hB' hkB'
  let S := preorderSummarySet B blocks D
  let S' := preorderSummarySet B' blocks D
  let G := preorderSummaryBST B blocks D
  let G' := preorderSummaryBST B' blocks D
  let M := S.card
  change IsLCAClosed B (S : Set ℕ) at hLCA
  change IsLCAClosed B' (S' : Set ℕ) at hLCA'
  change G.IsBST at hG_bst
  change G'.IsBST at hG'_bst
  change keyFinset G = S at hkG
  change keyFinset G' = S' at hkG'
  change 1 ≤ M at hM_pos
  have hcard_eq_M : S'.card = M := hcard'.trans hcard.symm
  have hsub_S : S ⊆ Finset.Icc 1 N := by
    rw [← hkB, ← hkG]
    intro x hx
    rw [mem_keyFinset_iff] at hx ⊢
    exact ((mem_restrictTree_of_isLCAClosed hB hLCA x).mp hx).1
  have hsub_S' : S' ⊆ Finset.Icc 1 N := by
    rw [← hkB', ← hkG']
    intro x hx
    rw [mem_keyFinset_iff] at hx ⊢
    exact ((mem_restrictTree_of_isLCAClosed hB' hLCA' x).mp hx).1
  obtain ⟨_, hnormG_bst, hk_normG, _⟩ := normalizeBST_spec hG_bst
  obtain ⟨_, hnormG'_bst, hk_normG', _⟩ := normalizeBST_spec hG'_bst
  rw [hkG] at hk_normG
  change keyFinset (normalizeBST G) = Finset.Icc 1 M at hk_normG
  rw [hkG', hcard_eq_M] at hk_normG'
  obtain ⟨hrr_neq, hrr_u, hrr_u_lt, hv_le_rr_v⟩ := rightReach_rotateRightEdge_spec hB he
  have hrr_mono : ∀ x : ℕ, rightReach B x ≤ rightReach B' x := by
    intro x
    by_cases hxu : x = u
    · subst hxu; change rightReach B x ≤ rightReach (rotateRightEdge B x v) x; omega
    · change rightReach B x ≤ rightReach (rotateRightEdge B u v) x
      rw [hrr_neq x hxu]
  -- Helper: when `S' = S`, right-reach monotonicity immediately implies `RightRotReachable`
  have hreach_of_eq : S' = S → RightRotReachable (normalizeBST G) (normalizeBST G') := by
    intro hSeq
    rw [prop_4_1_right_reach M hM_pos (normalizeBST G) (normalizeBST G')
      hnormG_bst hnormG'_bst hk_normG hk_normG']
    intro j hj
    have hjG : j ∈ Finset.Icc 1 (keyFinset G).card := by rw [hkG]; exact hj
    obtain ⟨x, hxS, hxj⟩ := exists_mem_of_card_filter_le hG_bst hjG
    rw [hkG] at hxS hxj
    have hxS' : x ∈ S' := hSeq ▸ hxS
    have hxj' : (S'.filter (· ≤ x)).card = j := by rw [hSeq, hxj]
    have h1 : rightReach (normalizeBST G) j = (S.filter (· ≤ rightReach B x)).card := by
      rw [← hxj]
      exact rightReach_normalizeBST_restrictTree hB_rng hB_n hsub_S hLCA hxS
    have h2 : rightReach (normalizeBST G') j = (S'.filter (· ≤ rightReach B' x)).card := by
      rw [← hxj']
      exact rightReach_normalizeBST_restrictTree hB'_rng hB'_n hsub_S' hLCA' hxS'
    rw [h1, h2, hSeq]
    exact Finset.card_le_card (fun z hz => by
      simp only [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, le_trans hz.2 (hrr_mono x)⟩)
  -- Blockwise invariance whenever `¬ (u ∈ C.toFinset ∧ v ∈ C.toFinset)`
  have hblk_eq_of_not : ∀ {C : IntervalBlock}, ¬ (u ∈ C.toFinset ∧ v ∈ C.toFinset) →
      blockSummaryFinset B' C D = blockSummaryFinset B C D := by
    intro C hnotC
    have hnot_set : ¬ (u ∈ C.toSet ∧ v ∈ C.toSet) := by
      rw [mem_intervalBlock_toSet_iff, mem_intervalBlock_toSet_iff]
      exact hnotC
    have hres_eq : restrictTree B' C.toSet = restrictTree B C.toSet :=
      (restrictTree_rotateRightEdge hB he
        (isLCAClosed_intervalBlock hB C) (isLCAClosed_intervalBlock hB' C)).2 hnot_set
    simp only [blockSummaryFinset, hres_eq]
  -- Inter-block proof (used for both conjunct 2 and Case 1 of conjunct 1)
  have hinter_all : (∀ C ∈ blocks, ¬ (u ∈ C.toFinset ∧ v ∈ C.toFinset)) →
      S' = S ∧
      (u ∈ S ∧ v ∈ S → IsRightRotEdge G u v ∧ G' = rotateRightEdge G u v) ∧
      (¬ (u ∈ S ∧ v ∈ S) → G' = G) := by
    intro hinter
    have hSeq : S' = S := by
      ext w
      rw [mem_preorderSummarySet_iff, mem_preorderSummarySet_iff]
      exact ⟨fun ⟨C, hC, hw⟩ => ⟨C, hC, (hblk_eq_of_not (hinter C hC)) ▸ hw⟩,
             fun ⟨C, hC, hw⟩ => ⟨C, hC, (hblk_eq_of_not (hinter C hC)).symm ▸ hw⟩⟩
    have hLCA'_S : IsLCAClosed B' (S : Set ℕ) := hSeq ▸ hLCA'
    obtain ⟨hrot1, hrot2⟩ := restrictTree_rotateRightEdge hB he hLCA hLCA'_S
    have hG'_eq : G' = restrictTree B' (S : Set ℕ) := by
      change restrictTree B' (S' : Set ℕ) = restrictTree B' (S : Set ℕ)
      rw [hSeq]
    refine ⟨hSeq, ?_, ?_⟩
    · intro huvS
      have huv_coe : u ∈ (S : Set ℕ) ∧ v ∈ (S : Set ℕ) := huvS
      obtain ⟨heG, hrotG⟩ := hrot1 huv_coe
      exact ⟨heG, hG'_eq.trans hrotG⟩
    · intro hnotS
      have hnot_coe : ¬ (u ∈ (S : Set ℕ) ∧ v ∈ (S : Set ℕ)) := hnotS
      exact hG'_eq.trans (hrot2 hnot_coe)
  refine ⟨?_, hinter_all⟩
  -- Conjunct 1: `RightRotReachable (normalizeBST G) (normalizeBST G')`
  by_cases hinter : ∀ C ∈ blocks, ¬ (u ∈ C.toFinset ∧ v ∈ C.toFinset)
  · exact hreach_of_eq (hinter_all hinter).1
  · -- Intra-block rotation: `u, v ∈ Cq.toFinset` for a unique block `Cq ∈ blocks`
    push Not at hinter
    rcases hinter with ⟨Cq, hCq, huCq, hvCq⟩
    obtain ⟨_, hpw_blk, _⟩ := partition_blocks_union hN hPart
    have hbnds := hPart.1
    have hdisj_pw : blocks.Pairwise (fun C₁ C₂ => Disjoint C₁.toFinset C₂.toFinset) := by
      refine hpw_blk.imp (fun {C₁ C₂} hlt => Finset.disjoint_left.mpr (fun x hx1 hx2 => ?_))
      simp only [IntervalBlock.toFinset, Finset.mem_Icc] at hx1 hx2
      omega
    have hmem_Cq : ∀ (T : BinaryTree ℕ) (w : ℕ), w ∈ Cq.toFinset →
        (w ∈ preorderSummarySet T blocks D ↔ w ∈ blockSummaryFinset T Cq D) := by
      intro T w hwCq
      rw [mem_preorderSummarySet_iff]
      constructor
      · rintro ⟨C', hC', hwC'⟩
        by_cases heq : C' = Cq
        · subst heq; exact hwC'
        · exfalso
          have hdisj := pairwise_symm_of_mem (fun h => h.symm) hdisj_pw hC' hCq heq
          exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hwC').1 hwCq
      · intro hw; exact ⟨Cq, hCq, hw⟩
    have hmem_outside_Cq : ∀ w : ℕ, w ∉ Cq.toFinset → (w ∈ S' ↔ w ∈ S) := by
      intro w hw_not
      rw [mem_preorderSummarySet_iff, mem_preorderSummarySet_iff]
      have hne_Cq : ∀ {C : IntervalBlock}, C ∈ blocks → C ≠ Cq →
          blockSummaryFinset B' C D = blockSummaryFinset B C D := by
        intro C hC hne
        apply hblk_eq_of_not
        rintro ⟨huC, _⟩
        have hdisj := pairwise_symm_of_mem (fun h => h.symm) hdisj_pw hC hCq hne
        exact Finset.disjoint_left.mp hdisj huC huCq
      constructor
      · rintro ⟨C, hC, hwC⟩
        by_cases heq : C = Cq
        · subst heq; exact absurd (Finset.mem_filter.mp hwC).1 hw_not
        · exact ⟨C, hC, (hne_Cq hC heq) ▸ hwC⟩
      · rintro ⟨C, hC, hwC⟩
        by_cases heq : C = Cq
        · subst heq; exact absurd (Finset.mem_filter.mp hwC).1 hw_not
        · exact ⟨C, hC, (hne_Cq hC heq).symm ▸ hwC⟩
    let BC := restrictTree B Cq.toSet
    let BC' := restrictTree B' Cq.toSet
    obtain ⟨hBC_rng, hBC_n, _, _⟩ :=
      restrictTree_interval_isRangeBST hB_rng hB_n (hbnds Cq hCq)
    obtain ⟨hBC'_rng, _, _, _⟩ :=
      restrictTree_interval_isRangeBST hB'_rng hB'_n (hbnds Cq hCq)
    have hBC_bst := isBST_of_isRangeBST hBC_rng
    have hBC'_bst := isBST_of_isRangeBST hBC'_rng
    have hL_old_nodup := bstPreorderList_nodup_of_isBST hBC_bst
    have hL_new_nodup := bstPreorderList_nodup_of_isBST hBC'_bst
    have hu_Cset : u ∈ Cq.toSet := (mem_intervalBlock_toSet_iff Cq u).mpr huCq
    have hv_Cset : v ∈ Cq.toSet := (mem_intervalBlock_toSet_iff Cq v).mpr hvCq
    obtain ⟨he_BC, hBC'_rot⟩ :=
      (restrictTree_rotateRightEdge hB he
        (isLCAClosed_intervalBlock hB Cq) (isLCAClosed_intervalBlock hB' Cq)).1 ⟨hu_Cset, hv_Cset⟩
    change BC' = rotateRightEdge BC u v at hBC'_rot
    obtain ⟨heq_take_B, _⟩ := blockSummaryFinset_eq_take_toFinset hB_rng hB_n (hbnds Cq hCq) D
    obtain ⟨heq_take_B', _⟩ := blockSummaryFinset_eq_take_toFinset hB'_rng hB'_n (hbnds Cq hCq) D
    have hmem_Cq_take_B : ∀ w ∈ Cq.toFinset, w ∈ S ↔ w ∈ (bstPreorderList BC).take D := by
      intro w hw
      rw [hmem_Cq B w hw, heq_take_B, List.mem_toFinset]
    have hmem_Cq_take_B' : ∀ w ∈ Cq.toFinset, w ∈ S' ↔ w ∈ (bstPreorderList BC').take D := by
      intro w hw
      rw [hmem_Cq B' w hw, heq_take_B', List.mem_toFinset]
    obtain ⟨a_u, Aq, Mq, Rq, P_pre, S_pre, ha_lo, ha_hi, hs_rng, hsub_BC_v, hrr_BC_s,
      hL_old_raw, hL_new_raw⟩ := bstPreorderList_rotateRightEdge_infix BC Cq.lo u v hBC_rng he_BC
    rw [← hBC'_rot] at hL_new_raw
    rcases hs_rng with ⟨hv_eq_au, ⟨hu_eq_au, hAq_rng, hMq_rng⟩, hRq_rng⟩
    let UA := u :: bstPreorderList Aq
    let Rest := bstPreorderList Mq ++ bstPreorderList Rq ++ S_pre
    have hL_old : bstPreorderList BC = P_pre ++ (v :: (UA ++ Rest)) := by
      simpa [bstPreorderList, UA, Rest, List.append_assoc] using hL_old_raw
    have hL_new : bstPreorderList BC' = P_pre ++ (UA ++ (v :: Rest)) := by
      simpa [bstPreorderList, UA, Rest, List.append_assoc] using hL_new_raw
    let p0 := P_pre.length
    by_cases hD_le_p0 : D ≤ p0
    · apply hreach_of_eq
      ext w
      by_cases hwCq : w ∈ Cq.toFinset
      · rw [hmem_Cq_take_B' w hwCq, hmem_Cq_take_B w hwCq, hL_old, hL_new,
          List.take_append_of_le_length hD_le_p0, List.take_append_of_le_length hD_le_p0]
      · exact hmem_outside_Cq w hwCq
    · by_cases hD_ge_end : p0 + 1 + UA.length ≤ D
      · apply hreach_of_eq
        ext w
        by_cases hwCq : w ∈ Cq.toFinset
        · rw [hmem_Cq_take_B' w hwCq, hmem_Cq_take_B w hwCq]
          have htake_old2 :
              (bstPreorderList BC).take D =
                (P_pre ++ (v :: UA)) ++ Rest.take (D - (p0 + 1 + UA.length)) := by
            have h1 : bstPreorderList BC = (P_pre ++ (v :: UA)) ++ Rest := by
              simpa [List.append_assoc] using hL_old
            have hlen1 : (P_pre ++ (v :: UA)).length = p0 + 1 + UA.length := by
              simp [p0]; omega
            rw [h1, List.take_append, List.take_of_length_le (by omega), hlen1]
          have htake_new2 :
              (bstPreorderList BC').take D =
                (P_pre ++ (UA ++ [v])) ++ Rest.take (D - (p0 + 1 + UA.length)) := by
            have h2 : bstPreorderList BC' = (P_pre ++ (UA ++ [v])) ++ Rest := by
              simpa [List.append_assoc] using hL_new
            have hlen2 : (P_pre ++ (UA ++ [v])).length = p0 + 1 + UA.length := by
              simp [p0]; omega
            rw [h2, List.take_append, List.take_of_length_le (by omega), hlen2]
          rw [htake_new2, htake_old2]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rw [or_comm (a := w ∈ UA) (b := w = v)]
        · exact hmem_outside_Cq w hwCq
      · -- Critical shift case: `p0 + 1 ≤ D < p0 + 1 + UA.length`
        let r := D - (p0 + 1)
        have hr_lt : r < UA.length := by omega
        have hD_eq : D = p0 + (r + 1) := by omega
        let x' := UA[r]
        have htake_old : (bstPreorderList BC).take D = P_pre ++ (v :: UA.take r) := by
          rw [hL_old, hD_eq, List.take_append,
            List.take_of_length_le (by dsimp [p0]; omega)]
          have hsub_len : p0 + (r + 1) - P_pre.length = r + 1 := by dsimp [p0]; omega
          rw [hsub_len]
          change P_pre ++ (v :: List.take r (UA ++ Rest)) = _
          rw [List.take_append_of_le_length (by omega)]
        have htake_new : (bstPreorderList BC').take D = P_pre ++ (UA.take r ++ [x']) := by
          rw [hL_new, hD_eq, List.take_append,
            List.take_of_length_le (by dsimp [p0]; omega)]
          have hsub_len : p0 + (r + 1) - P_pre.length = r + 1 := by dsimp [p0]; omega
          rw [hsub_len, List.take_append_of_le_length (by omega),
            List.take_succ_eq_append_getElem hr_lt]
        have hUA_split : UA = UA.take r ++ (x' :: UA.drop (r + 1)) := by
          conv_lhs => rw [← List.take_append_drop r UA, List.drop_eq_getElem_cons hr_lt]
        have hUA_bounds : ∀ z ∈ UA, a_u ≤ z ∧ z ≤ u := by
          intro z hz
          simp only [UA, List.mem_cons] at hz
          rcases hz with rfl | hzA
          · omega
          · rw [bstPreorderList_mem_iff, mem_of_isRangeBST hAq_rng] at hzA
            omega
        have hx'_mem_UA : x' ∈ UA := List.getElem_mem hr_lt
        obtain ⟨hx'_au, hx'_le_u⟩ := hUA_bounds x' hx'_mem_UA
        have hx'_lt_v : x' < v := lt_of_le_of_lt hx'_le_u huv
        have hv_Cq_bounds : Cq.lo ≤ v ∧ v ≤ Cq.hi := by
          simpa [IntervalBlock.toFinset] using hvCq
        have hx'_Cq : x' ∈ Cq.toFinset := by
          simp only [IntervalBlock.toFinset, Finset.mem_Icc]
          omega
        have hx'_not_S : x' ∉ S := by
          rw [hmem_Cq_take_B x' hx'_Cq, htake_old]
          intro hx'_in
          have hnodup := hL_old_nodup
          rw [hL_old, hUA_split] at hnodup
          have h_grp :
              P_pre ++ (v :: ((UA.take r ++ (x' :: UA.drop (r + 1))) ++ Rest)) =
                (P_pre ++ (v :: UA.take r)) ++ (x' :: (UA.drop (r + 1) ++ Rest)) := by
            simp [List.append_assoc]
          rw [h_grp, List.nodup_append] at hnodup
          exact hnodup.2.2 x' hx'_in x' List.mem_cons_self rfl
        have hx'_S' : x' ∈ S' := by
          rw [hmem_Cq_take_B' x' hx'_Cq, htake_new]
          simp
        have hv_S : v ∈ S := by
          rw [hmem_Cq_take_B v hvCq, htake_old]
          simp
        have hv_not_S' : v ∉ S' := by
          rw [hmem_Cq_take_B' v hvCq, htake_new]
          intro hv_in
          have hnodup := hL_new_nodup
          rw [hL_new, hUA_split] at hnodup
          have h_grp :
              P_pre ++ ((UA.take r ++ (x' :: UA.drop (r + 1))) ++ (v :: Rest)) =
                (P_pre ++ (UA.take r ++ [x']) ++ UA.drop (r + 1)) ++ (v :: Rest) := by
            simp [List.append_assoc]
          rw [h_grp, List.nodup_append] at hnodup
          exact hnodup.2.2 v (List.mem_append_left _ hv_in)
            v List.mem_cons_self rfl
        have hS'_agree : ∀ y : ℕ, y ≠ x' → y ≠ v → (y ∈ S' ↔ y ∈ S) := by
          intro y hyx' hyv
          by_cases hyCq : y ∈ Cq.toFinset
          · rw [hmem_Cq_take_B' y hyCq, hmem_Cq_take_B y hyCq, htake_old, htake_new]
            simp [List.mem_append, List.mem_cons, hyx', hyv]
          · exact hmem_outside_Cq y hyCq
        have hS'_eq : S' = insert x' (S.erase v) := by
          ext y
          simp only [Finset.mem_insert, Finset.mem_erase]
          by_cases hyx' : y = x'
          · subst hyx'
            exact ⟨fun _ => Or.inl rfl, fun _ => hx'_S'⟩
          · by_cases hyv : y = v
            · rw [hyv] at hyx' ⊢
              exact ⟨fun h => absurd h hv_not_S',
                fun h => by rcases h with h1 | ⟨h2, _⟩; exact absurd h1 hyx'; exact absurd rfl h2⟩
            · rw [hS'_agree y hyx' hyv]
              exact ⟨fun h => Or.inr ⟨hyv, h⟩,
                fun h => by rcases h with h1 | ⟨_, h2⟩; exact absurd h1 hyx'; exact h2⟩
        have hu_S' : u ∈ S' := by
          rcases eq_or_lt_of_le hx'_le_u with h_eq | hlt
          · exact h_eq ▸ hx'_S'
          · rcases r with _ | r'
            · have : x' = u := rfl; omega
            · have hu_S : u ∈ S := by
                rw [hmem_Cq_take_B u huCq, htake_old]
                simp [UA]
              exact (hS'_agree u (ne_of_gt hlt) (ne_of_lt huv)).mpr hu_S
        have hmid_not_S : ∀ y : ℕ, u < y → y < v → y ∉ S := by
          intro y huy hyv
          have hyCq : y ∈ Cq.toFinset := by
            simp only [IntervalBlock.toFinset, Finset.mem_Icc] at huCq hvCq ⊢
            omega
          rw [hmem_Cq_take_B y hyCq, htake_old]
          have hyMq : y ∈ bstPreorderList Mq := by
            rw [bstPreorderList_mem_iff, mem_of_isRangeBST hMq_rng]
            simp only [num_nodes_node] at hv_eq_au
            omega
          intro hy_in
          have hnodup := hL_old_nodup
          have h_grp : bstPreorderList BC = (P_pre ++ (v :: UA)) ++ Rest := by
            simpa [List.append_assoc] using hL_old
          rw [h_grp, List.nodup_append] at hnodup
          have hy_left : y ∈ P_pre ++ (v :: UA) := by
            simp only [List.mem_append, List.mem_cons] at hy_in ⊢
            rcases hy_in with h1 | rfl | h2
            · exact Or.inl h1
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (List.mem_of_mem_take h2))
          have hy_right : y ∈ Rest := by simp [Rest, hyMq]
          exact hnodup.2.2 y hy_left y hy_right rfl
        have hrr_u_B_eq : rightReach B u + 1 = v :=
          rightReach_rotateRightEdge_u_of_isRangeBST hB_rng he
        -- Final verification of `RightRotReachable (normalizeBST G) (normalizeBST G')`
        rw [prop_4_1_right_reach M hM_pos (normalizeBST G) (normalizeBST G')
          hnormG_bst hnormG'_bst hk_normG hk_normG']
        intro j hj
        have hjG : j ∈ Finset.Icc 1 (keyFinset G).card := by rw [hkG]; exact hj
        obtain ⟨w, hwS, hwj⟩ := exists_mem_of_card_filter_le hG_bst hjG
        rw [hkG] at hwS hwj
        have hG_rr : rightReach (normalizeBST G) j = (S.filter (· ≤ rightReach B w)).card := by
          rw [← hwj]
          exact rightReach_normalizeBST_restrictTree hB_rng hB_n hsub_S hLCA hwS
        rw [hG_rr]
        have hwx' : w ≠ x' := fun h => hx'_not_S (h ▸ hwS)
        by_cases h_lt_x' : w < x'
        · have hwv : w ≠ v := by omega
          have hwS' : w ∈ S' := (hS'_agree w hwx' hwv).mpr hwS
          have hwj' : (S'.filter (· ≤ w)).card = j := by
            rw [(filter_le_card_swap hx'_lt_v hx'_not_S hv_S hS'_eq w).1 (Or.inl h_lt_x'), hwj]
          have hG'_rr : rightReach (normalizeBST G') j = (S'.filter (· ≤ rightReach B' w)).card := by
            rw [← hwj']
            exact rightReach_normalizeBST_restrictTree hB'_rng hB'_n hsub_S' hLCA' hwS'
          rw [hG'_rr]
          have hrr_eq : rightReach B' w = rightReach B w := hrr_neq w (by omega)
          rw [hrr_eq]
          exact (filter_le_card_swap hx'_lt_v hx'_not_S hv_S hS'_eq (rightReach B w)).2.2
        · by_cases h_gt_v : v < w
          · have hwv : w ≠ v := by omega
            have hwS' : w ∈ S' := (hS'_agree w hwx' hwv).mpr hwS
            have hwj' : (S'.filter (· ≤ w)).card = j := by
              rw [(filter_le_card_swap hx'_lt_v hx'_not_S hv_S hS'_eq w).1 (Or.inr h_gt_v.le), hwj]
            have hG'_rr : rightReach (normalizeBST G') j = (S'.filter (· ≤ rightReach B' w)).card := by
              rw [← hwj']
              exact rightReach_normalizeBST_restrictTree hB'_rng hB'_n hsub_S' hLCA' hwS'
            rw [hG'_rr]
            have hrr_eq : rightReach B' w = rightReach B w := hrr_neq w (by omega)
            rw [hrr_eq]
            exact (filter_le_card_swap hx'_lt_v hx'_not_S hv_S hS'_eq (rightReach B w)).2.2
          · by_cases hw_eq_v : w = v
            · rw [hw_eq_v] at hwj ⊢
              have hfilt_v : S.filter (· ≤ v) = insert v (S.filter (· ≤ u)) := by
                ext y
                simp only [Finset.mem_filter, Finset.mem_insert]
                constructor
                · rintro ⟨hyS, hyv⟩
                  rcases eq_or_lt_of_le hyv with rfl | hlt
                  · exact Or.inl rfl
                  · refine Or.inr ⟨hyS, ?_⟩
                    by_contra hgt
                    exact hmid_not_S y (Nat.lt_of_not_le hgt) hlt hyS
                · rintro (rfl | ⟨hyS, hyu⟩)
                  · exact ⟨hv_S, le_rfl⟩
                  · exact ⟨hyS, le_trans hyu huv.le⟩
              have hv_not_fu : v ∉ S.filter (· ≤ u) := by
                simp only [Finset.mem_filter]; omega
              have hcv_cu : (S.filter (· ≤ v)).card = (S.filter (· ≤ u)).card + 1 := by
                have hu_ins : insert v (S.filter (· ≤ u)) =
                    ({v} : Finset ℕ) ∪ S.filter (· ≤ u) := by ext z; simp
                rw [hfilt_v, hu_ins,
                  Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hv_not_fu),
                  Finset.card_singleton]
                omega
              have hc'u : (S'.filter (· ≤ u)).card = j := by
                rw [(filter_le_card_swap hx'_lt_v hx'_not_S hv_S hS'_eq u).2.1 ⟨hx'_le_u, huv⟩,
                  ← hcv_cu, hwj]
              have hG'_rr : rightReach (normalizeBST G') j = (S'.filter (· ≤ rightReach B' u)).card := by
                rw [← hc'u]
                exact rightReach_normalizeBST_restrictTree hB'_rng hB'_n hsub_S' hLCA' hu_S'
              rw [hG'_rr]
              change (S.filter (· ≤ rightReach B v)).card ≤
                (S'.filter (· ≤ rightReach (rotateRightEdge B u v) u)).card
              rw [hrr_u]
              exact (filter_le_card_swap hx'_lt_v hx'_not_S hv_S hS'_eq (rightReach B v)).2.2
            · -- Remaining case: `x' < w ∧ w < v`
              have hx'_lt_w : x' < w := by omega
              have hw_lt_v : w < v := by omega
              have hw_le_u : w ≤ u := by
                by_contra hgt
                exact hmid_not_S w (Nat.lt_of_not_le hgt) hw_lt_v hwS
              have hw_in_B : w ∈ B := mem_keyFinset_iff.mp (hkB ▸ hsub_S hwS)
              have hw_le_rrB : w ≤ rightReach B w := self_le_rightReach hB hw_in_B
              -- Show `w ∈ subtreeAtKey B u`, so `rightReach B w ≤ rightReach B u < v`
              have hw_sub_BC_u : w ∈ subtreeAtKey BC u := by
                have hv_in_BC : v ∈ BC := by
                  rcases he_BC with ⟨_, _, _, hv_in, _⟩; exact hv_in
                have hu_in_subv : u ∈ subtreeAtKey BC v := by
                  rw [hsub_BC_v]; exact .left .here
                have hsub_BC_u_eq : subtreeAtKey BC u = .node u Aq Mq := by
                  rw [subtreeAtKey_idem_of_mem hBC_bst hu_in_subv, hsub_BC_v]
                  simp [subtreeAtKey, huv]
                rw [hsub_BC_u_eq]
                rcases eq_or_lt_of_le hw_le_u with rfl | hw_lt_u
                · exact .here
                · exact .left ((mem_of_isRangeBST hAq_rng w).mpr ⟨by omega, by omega⟩)
              have hu_in_B : u ∈ B := by
                rw [← mem_keyFinset_iff, hkB, Finset.mem_Icc]
                have hbCq := hbnds Cq hCq
                simp only [IntervalBlock.toFinset, Finset.mem_Icc] at huCq
                omega
              have hw_sub_B_u : w ∈ subtreeAtKey B u := by
                rw [subtreeAtKey_restrictTree_of_isLCAClosed hB
                  (isLCAClosed_intervalBlock hB Cq) hu_in_B hu_Cset] at hw_sub_BC_u
                exact ((mem_restrictTree_of_isLCAClosed (subtreeAtKey_isBST hB u)
                  (isLCAClosed_subtreeAtKey hB (isLCAClosed_intervalBlock hB Cq) u) w).mp
                    hw_sub_BC_u).1
              have hrrB_w_lt_v : rightReach B w < v := by
                have hle := rightReach_le_of_mem_subtreeAtKey hB hw_sub_B_u
                omega
              -- Show no `y ∈ S` lies strictly between `w` and `rightReach B w`
              have hno_right_S : ∀ y : ℕ, w < y → y ≤ rightReach B w → y ∉ S := by
                intro y hwy hy_rr
                rcases eq_or_lt_of_le hw_le_u with rfl | hw_lt_u
                · exact hmid_not_S y hwy (lt_of_le_of_lt hy_rr hrrB_w_lt_v)
                · rcases r with _ | m
                  · have : x' = u := rfl; omega
                  · have hm_lt : m < (bstPreorderList Aq).length := by
                      simp only [UA, List.length_cons] at hr_lt; omega
                    have hx'_eq : x' = (bstPreorderList Aq)[m] := rfl
                    have hwCq : w ∈ Cq.toFinset := by
                      simp only [IntervalBlock.toFinset, Finset.mem_Icc]
                      omega
                    have hw_Aq : w ∈ bstPreorderList Aq := by
                      rw [bstPreorderList_mem_iff, mem_of_isRangeBST hAq_rng]
                      omega
                    have hw_not_Ppre : w ∉ P_pre := by
                      have hnodup := hL_old_nodup
                      rw [hL_old, List.nodup_append] at hnodup
                      intro hwP
                      exact hnodup.2.2 w hwP w (by simp [UA, hw_Aq]) rfl
                    have hw_take_m : w ∈ (bstPreorderList Aq).take m := by
                      have hw_in_take := (hmem_Cq_take_B w hwCq).mp hwS
                      rw [htake_old] at hw_in_take
                      change w ∈ P_pre ++ (v :: u :: (bstPreorderList Aq).take m) at hw_in_take
                      simp only [List.mem_append, List.mem_cons] at hw_in_take
                      rcases hw_in_take with hwP | rfl | rfl | hwm
                      · exact absurd hwP hw_not_Ppre
                      · omega
                      · omega
                      · exact hwm
                    -- Relate `rightReach B w = rightReach BC w = rightReach Aq w`
                    have hrr_BC_w : rightReach BC w = rightReach B w := by
                      have hw_Cset : w ∈ Cq.toSet := (mem_intervalBlock_toSet_iff Cq w).mpr hwCq
                      have hsub_eq := subtreeAtKey_restrictTree_of_isLCAClosed hB
                        (isLCAClosed_intervalBlock hB Cq) hw_in_B hw_Cset
                      obtain ⟨_, _, hsubB_w_node⟩ := subtreeAtKey_mem_node hB hw_in_B
                      rcases maxKey?_isBST_spec (subtreeAtKey_isBST hB w) with
                        ⟨hemp, _⟩ | ⟨mw, hmw_B, hmax_wB, hub_wB⟩
                      · rw [hsubB_w_node] at hemp; cases hemp
                      · have hrr_Bw_eq : rightReach B w = mw := by simp [rightReach, hmax_wB]
                        have hmw_ge_w : w ≤ mw := hub_wB w (by rw [hsubB_w_node]; exact .here)
                        have hmw_Cset : mw ∈ Cq.toSet := by
                          rw [mem_intervalBlock_toSet]
                          omega
                        have hmw_BC : mw ∈ subtreeAtKey BC w := by
                          change mw ∈ subtreeAtKey (restrictTree B Cq.toSet) w
                          rw [hsub_eq]
                          exact (mem_restrictTree_of_isLCAClosed (subtreeAtKey_isBST hB w)
                            (isLCAClosed_subtreeAtKey hB (isLCAClosed_intervalBlock hB Cq) w)
                              mw).mpr ⟨hmw_B, hmw_Cset⟩
                        have hmax_wBC : (subtreeAtKey BC w).maxKey? = some mw := by
                          rw [maxKey?_eq_some_iff_of_isBST (subtreeAtKey_isBST hBC_bst w)]
                          refine ⟨hmw_BC, fun z hz => hub_wB z ?_⟩
                          change z ∈ subtreeAtKey (restrictTree B Cq.toSet) w at hz
                          rw [hsub_eq] at hz
                          exact ((mem_restrictTree_of_isLCAClosed (subtreeAtKey_isBST hB w)
                            (isLCAClosed_subtreeAtKey hB (isLCAClosed_intervalBlock hB Cq) w)
                              z).mp hz).1
                        simp [rightReach, hmax_wBC, hmax_wB]
                    have hrr_Aq_w : rightReach B w = rightReach Aq w := by
                      rw [← hrr_BC_w, hrr_BC_s w (by omega)
                        (by simp only [num_nodes_node] at hv_eq_au ⊢; omega)]
                      simp [rightReach_node_eq, hw_lt_v, hw_lt_u]
                    have hy_rr_Aq : y ≤ rightReach Aq w := hrr_Aq_w ▸ hy_rr
                    have hy_not_take_m : y ∉ (bstPreorderList Aq).take m :=
                      not_mem_take_bstPreorderList_of_gt_getElem Aq a_u m w y
                        hAq_rng hm_lt hw_take_m (hx'_eq ▸ hx'_lt_w) hwy hy_rr_Aq
                    obtain ⟨_, _, _, hrrAq_end, hend_Aq, _⟩ :=
                      isRangeBST_subtreeAtKey hAq_rng (bstPreorderList_mem_iff.mp hw_Aq)
                    have hy_lt_u : y < u := by omega
                    have hyCq : y ∈ Cq.toFinset := by
                      simp only [IntervalBlock.toFinset, Finset.mem_Icc]
                      omega
                    have hy_Aq : y ∈ bstPreorderList Aq := by
                      rw [bstPreorderList_mem_iff, mem_of_isRangeBST hAq_rng]
                      omega
                    have hy_not_Ppre : y ∉ P_pre := by
                      have hnodup := hL_old_nodup
                      rw [hL_old, List.nodup_append] at hnodup
                      intro hyP
                      exact hnodup.2.2 y hyP y (by simp [UA, hy_Aq]) rfl
                    rw [hmem_Cq_take_B y hyCq, htake_old]
                    change y ∉ P_pre ++ (v :: u :: (bstPreorderList Aq).take m)
                    simp only [List.mem_append, List.mem_cons]
                    rintro (hyP | rfl | rfl | hym)
                    · exact hy_not_Ppre hyP
                    · omega
                    · omega
                    · exact hy_not_take_m hym
              have hfilt_w_eq : S.filter (· ≤ rightReach B w) = S.filter (· ≤ w) := by
                ext y
                simp only [Finset.mem_filter]
                refine ⟨fun ⟨hyS, hyrr⟩ => ⟨hyS, ?_⟩,
                  fun ⟨hyS, hyw⟩ => ⟨hyS, le_trans hyw hw_le_rrB⟩⟩
                by_contra hgt
                exact hno_right_S y (Nat.lt_of_not_le hgt) hyrr hyS
              rw [hfilt_w_eq, hwj]
              exact self_le_rightReach hnormG'_bst (mem_keyFinset_iff.mp (hk_normG' ▸ hj))

end Solution.TamariPreorder

