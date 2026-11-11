module

public import Challenge.Definitions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Pairwise

/-!
# Section 5.5 (Steps 1–3): Post-Depletion Exits, Escape Reduction, and Quotient BST

Formalization of `main_v1.tex`:
- **Lemma 5.5** (`lem_5_5_b3_post`): Post-depletion exits `|ℬ_{3,exit,post}| ≤ K_L < 2 P`.
- **Lemma 5.6** (`lem_5_6_b3_escape`): Unique scale per promoted key and secondary-exit reduction.
- **Lemma 5.7** (`lem_5_7_b3_quotient`): Insertion-time Cartesian extension and block-root summary BST `Ĝ_X`.
-/

@[expose] public section

namespace Solution.BucketB3PostEscape

open SplayTree

namespace Internal55
set_option maxHeartbeats 4000000

open SplayTree BinaryTree

/-! ## 1. Basic BST, `keyFinset`, `leftSpine`, `subtreeAtKey`, and Rotation Helpers -/

theorem isBSTAux_of_bounds {α : Type} [LinearOrder α] {t : BinaryTree α}
    (h : t.IsBST) (lb ub : Option α)
    (hlo : ∀ x ∈ t, lb.elim True (· < x))
    (hhi : ∀ x ∈ t, ub.elim True (x < ·)) :
    t.IsBSTAux lb ub := by
  induction t generalizing lb ub with
  | nil => exact .nil lb ub
  | node k l r ihl ihr =>
    refine .node (hlo k .here) (hhi k .here) ?_ ?_
    · exact ihl (BinaryTree.IsBST_left_of_IsBST h) lb (some k)
        (fun x hx => hlo x (.left hx))
        (fun _ hx => BinaryTree.lt_of_IsBST_left l k r h hx)
    · exact ihr (BinaryTree.IsBST_right_of_IsBST h) (some k) ub
        (fun _ hx => BinaryTree.gt_of_IsBST_right l k r h hx)
        (fun x hx => hhi x (.right hx))

theorem isBST_nil {α : Type} [LinearOrder α] : (BinaryTree.nil : BinaryTree α).IsBST :=
  .nil none none

theorem isBST_node_iff {α : Type} [LinearOrder α] {k : α} {l r : BinaryTree α} :
    (BinaryTree.node k l r).IsBST ↔
      l.IsBST ∧ r.IsBST ∧ (∀ a ∈ l, a < k) ∧ (∀ b ∈ r, k < b) := by
  constructor
  · intro h
    exact ⟨BinaryTree.IsBST_left_of_IsBST h, BinaryTree.IsBST_right_of_IsBST h,
      fun _ hx => BinaryTree.lt_of_IsBST_left l k r h hx,
      fun _ hx => BinaryTree.gt_of_IsBST_right l k r h hx⟩
  · rintro ⟨hl, hr, hlt, hgt⟩
    refine BinaryTree.IsBSTAux.node trivial trivial ?_ ?_
    · exact isBSTAux_of_bounds hl none (some k) (by simp) hlt
    · exact isBSTAux_of_bounds hr (some k) none hgt (by simp)

theorem mem_keyFinset_iff {α : Type} [DecidableEq α] (t : BinaryTree α) (x : α) :
    x ∈ keyFinset t ↔ x ∈ t := by
  induction t with
  | nil => simp [keyFinset]
  | node k l r ihl ihr =>
    simp [keyFinset, BinaryTree.mem_node_iff, ihl, ihr]

theorem keyFinset_eq_empty_iff {α : Type} [DecidableEq α] (t : BinaryTree α) :
    keyFinset t = ∅ ↔ t = .nil := by
  cases t with
  | nil => simp [keyFinset]
  | node k l r =>
    simp only [keyFinset, reduceCtorEq, iff_false]
    intro h
    have : k ∈ (∅ : Finset α) := h ▸ Finset.mem_insert_self k _
    exact Finset.notMem_empty k this

theorem mem_of_mem_leftSpine {α : Type} (t : BinaryTree α) {x : α}
    (hx : x ∈ leftSpine t) : x ∈ t := by
  induction t with
  | nil => simp [leftSpine] at hx
  | node k l r ihl _ =>
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact .left (ihl hx)
    · exact .here

theorem leftSpine_eq_nil_iff {α : Type} (t : BinaryTree α) :
    leftSpine t = [] ↔ t = .nil := by
  cases t <;> simp [leftSpine]

theorem leftSpine_sorted {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    rw [isBST_node_iff] at ht
    rcases ht with ⟨hl, _, hlt, _⟩
    simp only [leftSpine, List.pairwise_append, List.pairwise_singleton, true_and]
    exact ⟨ihl hl, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb
      exact hlt a (mem_of_mem_leftSpine l ha)⟩

theorem minKey?_eq_head?_leftSpine {α : Type} (t : BinaryTree α) :
    t.minKey? = (leftSpine t).head? := by
  induction t with
  | nil => rfl
  | node k l r ihl =>
    simp only [BinaryTree.minKey?, leftSpine]
    cases hl : leftSpine l with
    | nil =>
      have hlnil : l = .nil := (leftSpine_eq_nil_iff l).mp hl
      subst hlnil; rfl
    | cons a as =>
      rw [hl] at ihl
      simp only [List.head?_cons] at ihl
      simp [ihl]

theorem minKey?_mem {α : Type} {t : BinaryTree α} {m : α} (hm : t.minKey? = some m) :
    m ∈ t := by
  rw [minKey?_eq_head?_leftSpine] at hm
  cases hls : leftSpine t with
  | nil => rw [hls] at hm; simp at hm
  | cons a as =>
    rw [hls] at hm; simp at hm; subst hm
    exact mem_of_mem_leftSpine t (by rw [hls]; simp)

theorem minKey?_le_of_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) {m x : α} (hm : t.minKey? = some m) (hx : x ∈ t) : m ≤ x := by
  induction t generalizing m with
  | nil => simp [BinaryTree.minKey?] at hm
  | node k l r ihl _ =>
    rw [isBST_node_iff] at ht
    rcases ht with ⟨hl, _, hlt, hgt⟩
    rw [BinaryTree.mem_node_iff] at hx
    cases hlm : l.minKey? with
    | none =>
      have hkm : k = m := by
        simp only [BinaryTree.minKey?, hlm] at hm
        exact Option.some.inj hm
      subst hkm
      have hlnil : l = .nil := by
        rw [minKey?_eq_head?_leftSpine] at hlm
        cases hls : leftSpine l with
        | nil => exact (leftSpine_eq_nil_iff l).mp hls
        | cons _ _ => rw [hls] at hlm; simp at hlm
      subst hlnil
      rcases hx with rfl | hx | hx
      · exact le_rfl
      · cases hx
      · exact le_of_lt (hgt x hx)
    | some m' =>
      have hm'm : m' = m := by
        simp only [BinaryTree.minKey?, hlm] at hm
        exact Option.some.inj hm
      subst hm'm
      have hm'_lt_k : m' < k := hlt m' (minKey?_mem hlm)
      rcases hx with rfl | hx | hx
      · exact le_of_lt hm'_lt_k
      · exact ihl hl hlm hx
      · exact le_of_lt (lt_trans hm'_lt_k (hgt x hx))

theorem mem_of_mem_subtreeAtKey {α : Type} [LinearOrder α] {t : BinaryTree α} {a w : α}
    (hw : w ∈ subtreeAtKey t a) : w ∈ t := by
  induction t with
  | nil => simp [subtreeAtKey] at hw
  | node k l r ihl ihr =>
    simp only [subtreeAtKey] at hw
    split_ifs at hw with h1 h2
    · exact .left (ihl hw)
    · exact .right (ihr hw)
    · exact hw

theorem subtreeAtKey_nil_of_not_mem {α : Type} [LinearOrder α] {t : BinaryTree α} {a : α}
    (hna : a ∉ t) : subtreeAtKey t a = .nil := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [subtreeAtKey]
    split_ifs with h1 h2
    · exact ihl (fun h => hna (.left h))
    · exact ihr (fun h => hna (.right h))
    · have : a = k := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      subst this; exact absurd .here hna

theorem mem_subtreeAtKey_of_leftSpine {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) {i m : ℕ} (hi : i ≤ m) (hm : m < (leftSpine t).length) :
    (leftSpine t)[i]'(Nat.lt_of_le_of_lt hi hm) ∈ subtreeAtKey t ((leftSpine t)[m]'hm) := by
  induction t with
  | nil => simp [leftSpine] at hm
  | node k l r ihl _ =>
    rw [isBST_node_iff] at ht
    rcases ht with ⟨hl, _, hlt, _⟩
    have hlen : (leftSpine (.node k l r)).length = (leftSpine l).length + 1 := by
      simp [leftSpine]
    by_cases hml : m < (leftSpine l).length
    · have hil : i < (leftSpine l).length := Nat.lt_of_le_of_lt hi hml
      have h_eq_m : (leftSpine (.node k l r))[m]'hm = (leftSpine l)[m]'hml := by
        simp [leftSpine, List.getElem_append_left hml]
      have h_eq_i : (leftSpine (.node k l r))[i]'(Nat.lt_of_le_of_lt hi hm) =
          (leftSpine l)[i]'hil := by
        simp [leftSpine, List.getElem_append_left hil]
      rw [h_eq_m, h_eq_i]
      have hmk : (leftSpine l)[m]'hml < k :=
        hlt _ (mem_of_mem_leftSpine l (List.getElem_mem hml))
      unfold subtreeAtKey
      rw [ite_eq_left_of_eq_true _ _ (eq_true hmk)]
      exact ihl hl hml
    · have hm_eq : m = (leftSpine l).length := by omega
      subst hm_eq
      have h_eq_m : (leftSpine (.node k l r))[(leftSpine l).length]'hm = k := by
        simp [leftSpine]
      rw [h_eq_m]
      unfold subtreeAtKey
      rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl k)),
          ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl k))]
      exact mem_of_mem_leftSpine (.node k l r) (List.getElem_mem _)

theorem rotateRightEdge_isBST_and_keys {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) (x p : α) :
    (rotateRightEdge t x p).IsBST ∧ keyFinset (rotateRightEdge t x p) = keyFinset t := by
  induction t with
  | nil => exact ⟨ht, rfl⟩
  | node k l r ihl ihr =>
    have h_orig := ht
    rw [isBST_node_iff] at ht
    rcases ht with ⟨hl, hr, hlt, hgt⟩
    unfold rotateRightEdge
    split_ifs with hpk hkp
    · obtain ⟨hl', hkl'⟩ := ihl hl
      refine ⟨isBST_node_iff.mpr ⟨hl', hr, fun a ha => ?_, hgt⟩, ?_⟩
      · rw [← mem_keyFinset_iff, hkl', mem_keyFinset_iff] at ha; exact hlt a ha
      · simp [keyFinset, hkl']
    · obtain ⟨hr', hkr'⟩ := ihr hr
      refine ⟨isBST_node_iff.mpr ⟨hl, hr', hlt, fun b hb => ?_⟩, ?_⟩
      · rw [← mem_keyFinset_iff, hkr', mem_keyFinset_iff] at hb; exact hgt b hb
      · simp [keyFinset, hkr']
    · cases l with
      | nil => exact ⟨h_orig, rfl⟩
      | node lx a b =>
        dsimp only
        split_ifs with hlx
        · rw [isBST_node_iff] at hl
          rcases hl with ⟨ha, hb, halx, hblx⟩
          have hxk : lx < k := hlt lx .here
          have hbk : ∀ u ∈ b, u < k := fun u hu => hlt u (.right hu)
          have hk_bst : (BinaryTree.node k b r).IsBST :=
            isBST_node_iff.mpr ⟨hb, hr, hbk, hgt⟩
          refine ⟨isBST_node_iff.mpr ⟨ha, hk_bst, halx, fun u hu => ?_⟩, ?_⟩
          · rw [BinaryTree.mem_node_iff] at hu
            rcases hu with rfl | hu | hu
            · exact hxk
            · exact hblx u hu
            · exact lt_trans hxk (hgt u hu)
          · ext u; simp [keyFinset]; tauto
        · exact ⟨h_orig, rfl⟩

theorem rotateLeftEdge_isBST_and_keys {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) (x p : α) :
    (rotateLeftEdge t x p).IsBST ∧ keyFinset (rotateLeftEdge t x p) = keyFinset t := by
  induction t with
  | nil => exact ⟨ht, rfl⟩
  | node k l r ihl ihr =>
    have h_orig := ht
    rw [isBST_node_iff] at ht
    rcases ht with ⟨hl, hr, hlt, hgt⟩
    unfold rotateLeftEdge
    split_ifs with hpk hkp
    · obtain ⟨hl', hkl'⟩ := ihl hl
      refine ⟨isBST_node_iff.mpr ⟨hl', hr, fun a ha => ?_, hgt⟩, ?_⟩
      · rw [← mem_keyFinset_iff, hkl', mem_keyFinset_iff] at ha; exact hlt a ha
      · simp [keyFinset, hkl']
    · obtain ⟨hr', hkr'⟩ := ihr hr
      refine ⟨isBST_node_iff.mpr ⟨hl, hr', hlt, fun b hb => ?_⟩, ?_⟩
      · rw [← mem_keyFinset_iff, hkr', mem_keyFinset_iff] at hb; exact hgt b hb
      · simp [keyFinset, hkr']
    · cases r with
      | nil => exact ⟨h_orig, rfl⟩
      | node rx b c =>
        dsimp only
        split_ifs with hrx
        · rw [isBST_node_iff] at hr
          rcases hr with ⟨hb, hc, hbrx, hcrx⟩
          have hkx : k < rx := hgt rx .here
          have hkb : ∀ u ∈ b, k < u := fun u hu => hgt u (.left hu)
          have hk_bst : (BinaryTree.node k l b).IsBST :=
            isBST_node_iff.mpr ⟨hl, hb, hlt, hkb⟩
          refine ⟨isBST_node_iff.mpr ⟨hk_bst, hc, fun u hu => ?_, hcrx⟩, ?_⟩
          · rw [BinaryTree.mem_node_iff] at hu
            rcases hu with rfl | hu | hu
            · exact hkx
            · exact lt_trans (hlt u hu) hkx
            · exact hbrx u hu
          · ext u; simp [keyFinset]; tauto
        · exact ⟨h_orig, rfl⟩

theorem spliceMin_isBST_and_keys {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) {m : α} (hm : t.minKey? = some m) :
    (spliceMin t).IsBST ∧ keyFinset (spliceMin t) = keyFinset t \ {m} := by
  induction t generalizing m with
  | nil => simp [BinaryTree.minKey?] at hm
  | node k l r ihl _ =>
    rw [isBST_node_iff] at ht
    rcases ht with ⟨hl, hr, hlt, hgt⟩
    cases l with
    | nil =>
      have hkm : k = m := by
        simp only [BinaryTree.minKey?] at hm
        exact Option.some.inj hm
      subst hkm
      simp only [spliceMin, hr, true_and]
      ext u
      simp only [keyFinset, Finset.empty_union, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hu
        exact ⟨Or.inr hu, ne_of_gt (hgt u ((mem_keyFinset_iff r u).mp hu))⟩
      · rintro ⟨rfl | hu, hne⟩
        · exact absurd rfl hne
        · exact hu
    | node lk ll lr =>
      have hlm : (BinaryTree.node lk ll lr).minKey? = some m := by
        rw [minKey?_eq_head?_leftSpine] at hm ⊢
        cases hls : leftSpine (.node lk ll lr) with
        | nil => simp [leftSpine] at hls
        | cons x xs =>
          have hls_top : leftSpine (.node k (.node lk ll lr) r) = (x :: xs) ++ [k] := by
            change leftSpine (.node lk ll lr) ++ [k] = (x :: xs) ++ [k]
            rw [hls]
          rw [hls_top] at hm
          exact hm
      obtain ⟨hl', hkl'⟩ := ihl hl hlm
      have hm_lt_k : m < k := hlt m (minKey?_mem hlm)
      have hspl : spliceMin (BinaryTree.node k (.node lk ll lr) r) =
          .node k (spliceMin (.node lk ll lr)) r := rfl
      rw [hspl]
      refine ⟨isBST_node_iff.mpr ⟨hl', hr, fun a ha => ?_, hgt⟩, ?_⟩
      · rw [← mem_keyFinset_iff, hkl', Finset.mem_sdiff] at ha
        exact hlt a ((mem_keyFinset_iff _ a).mp ha.1)
      · ext u
        simp only [keyFinset, hkl', Finset.mem_insert, Finset.mem_union,
          Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro (rfl | ⟨hu, hum⟩ | hu)
          · exact ⟨Or.inl rfl, ne_of_gt hm_lt_k⟩
          · exact ⟨Or.inr (Or.inl hu), hum⟩
          · exact ⟨Or.inr (Or.inr hu),
              ne_of_gt (lt_trans hm_lt_k (hgt u ((mem_keyFinset_iff r u).mp hu)))⟩
        · rintro ⟨rfl | hu | hu, hum⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨hu, hum⟩)
          · exact Or.inr (Or.inr hu)

theorem mem_subtreeAtKey_rotateRightEdge_lt {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) {x p a w : α}
    (hwa : w < a) (hw : w ∈ subtreeAtKey (rotateRightEdge t x p) a) :
    w ∈ subtreeAtKey t a := by
  induction t with
  | nil => simp [rotateRightEdge, subtreeAtKey] at hw
  | node k l r ihl ihr =>
    rw [isBST_node_iff] at ht
    rcases ht with ⟨hl, hr, hlt, hgt⟩
    unfold rotateRightEdge at hw
    split_ifs at hw with hpk hkp
    · unfold subtreeAtKey at hw ⊢
      split_ifs at hw ⊢ with hak hka
      · exact ihl hl hw
      · exact hw
      · have hkl' := (rotateRightEdge_isBST_and_keys hl x p).2
        rw [BinaryTree.mem_node_iff] at hw ⊢
        rcases hw with rfl | hw | hw
        · exact Or.inl rfl
        · rw [← mem_keyFinset_iff, hkl', mem_keyFinset_iff] at hw
          exact Or.inr (Or.inl hw)
        · exact Or.inr (Or.inr hw)
    · unfold subtreeAtKey at hw ⊢
      split_ifs at hw ⊢ with hak hka
      · exact hw
      · exact ihr hr hw
      · have hkr' := (rotateRightEdge_isBST_and_keys hr x p).2
        rw [BinaryTree.mem_node_iff] at hw ⊢
        rcases hw with rfl | hw | hw
        · exact Or.inl rfl
        · exact Or.inr (Or.inl hw)
        · rw [← mem_keyFinset_iff, hkr', mem_keyFinset_iff] at hw
          exact Or.inr (Or.inr hw)
    · cases l with
      | nil => exact hw
      | node lx A B =>
        dsimp only at hw
        split_ifs at hw with hlx
        · rw [isBST_node_iff] at hl
          rcases hl with ⟨hA, hB, hAx, hBx⟩
          have hxk : lx < k := hlt lx .here
          unfold subtreeAtKey at hw
          split_ifs at hw with hax hxa
          · have hak : a < k := lt_trans hax hxk
            unfold subtreeAtKey
            rw [ite_eq_left_of_eq_true _ _ (eq_true hak)]
            unfold subtreeAtKey
            rw [ite_eq_left_of_eq_true _ _ (eq_true hax)]
            exact hw
          · unfold subtreeAtKey at hw
            split_ifs at hw with hak hka
            · unfold subtreeAtKey
              rw [ite_eq_left_of_eq_true _ _ (eq_true hak)]
              unfold subtreeAtKey
              rw [ite_eq_right_of_eq_false _ _ (eq_false hax), ite_eq_left_of_eq_true _ _ (eq_true hxa)]
              exact hw
            · have hnot_ak : ¬ (a < k) := not_lt.mpr (le_of_lt hka)
              unfold subtreeAtKey
              rw [ite_eq_right_of_eq_false _ _ (eq_false hnot_ak), ite_eq_left_of_eq_true _ _ (eq_true hka)]
              exact hw
            · unfold subtreeAtKey
              rw [ite_eq_right_of_eq_false _ _ (eq_false hak), ite_eq_right_of_eq_false _ _ (eq_false hka)]
              rw [BinaryTree.mem_node_iff] at hw
              rcases hw with rfl | hw | hw
              · exact .here
              · exact .left (.right hw)
              · exact .right hw
          · have hax_eq : a = lx := le_antisymm (not_lt.mp hxa) (not_lt.mp hax)
            subst hax_eq
            unfold subtreeAtKey
            rw [ite_eq_left_of_eq_true _ _ (eq_true hxk)]
            unfold subtreeAtKey
            rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl a)),
                ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl a))]
            rw [BinaryTree.mem_node_iff] at hw
            rcases hw with rfl | hw | hw
            · exact absurd rfl (ne_of_lt hwa)
            · exact .left hw
            · exfalso
              rw [BinaryTree.mem_node_iff] at hw
              rcases hw with rfl | hw | hw
              · exact absurd (lt_trans hwa hxk) (lt_irrefl _)
              · exact absurd (lt_trans hwa (hBx w hw)) (lt_irrefl _)
              · exact absurd (lt_trans hwa (lt_trans hxk (hgt w hw))) (lt_irrefl _)
        · exact hw

theorem mem_subtreeAtKey_rotateLeftEdge_ne {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) {y x a w : α}
    (hay : a ≠ y) (hw : w ∈ subtreeAtKey (rotateLeftEdge t y x) a) :
    w ∈ subtreeAtKey t a := by
  induction t with
  | nil => simp [rotateLeftEdge, subtreeAtKey] at hw
  | node k l r ihl ihr =>
    rw [isBST_node_iff] at ht
    rcases ht with ⟨hl, hr, hlt, hgt⟩
    unfold rotateLeftEdge at hw
    split_ifs at hw with hxk hkx
    · unfold subtreeAtKey at hw ⊢
      split_ifs at hw ⊢ with hak hka
      · exact ihl hl hw
      · exact hw
      · have hkl' := (rotateLeftEdge_isBST_and_keys hl y x).2
        rw [BinaryTree.mem_node_iff] at hw ⊢
        rcases hw with rfl | hw | hw
        · exact Or.inl rfl
        · rw [← mem_keyFinset_iff, hkl', mem_keyFinset_iff] at hw
          exact Or.inr (Or.inl hw)
        · exact Or.inr (Or.inr hw)
    · unfold subtreeAtKey at hw ⊢
      split_ifs at hw ⊢ with hak hka
      · exact hw
      · exact ihr hr hw
      · have hkr' := (rotateLeftEdge_isBST_and_keys hr y x).2
        rw [BinaryTree.mem_node_iff] at hw ⊢
        rcases hw with rfl | hw | hw
        · exact Or.inl rfl
        · exact Or.inr (Or.inl hw)
        · rw [← mem_keyFinset_iff, hkr', mem_keyFinset_iff] at hw
          exact Or.inr (Or.inr hw)
    · cases r with
      | nil => exact hw
      | node ry B C =>
        dsimp only at hw
        split_ifs at hw with hry
        · rw [isBST_node_iff] at hr
          rcases hr with ⟨hB, hC, hBy, hCy⟩
          have hky : k < ry := hgt ry .here
          unfold subtreeAtKey at hw
          split_ifs at hw with hay_lt hya_lt
          · unfold subtreeAtKey at hw
            split_ifs at hw with hak hka
            · unfold subtreeAtKey
              rw [ite_eq_left_of_eq_true _ _ (eq_true hak)]
              exact hw
            · unfold subtreeAtKey
              rw [ite_eq_right_of_eq_false _ _ (eq_false hak), ite_eq_left_of_eq_true _ _ (eq_true hka)]
              unfold subtreeAtKey
              rw [ite_eq_left_of_eq_true _ _ (eq_true hay_lt)]
              exact hw
            · unfold subtreeAtKey
              rw [ite_eq_right_of_eq_false _ _ (eq_false hak), ite_eq_right_of_eq_false _ _ (eq_false hka)]
              rw [BinaryTree.mem_node_iff] at hw
              rcases hw with rfl | hw | hw
              · exact .here
              · exact .left hw
              · exact .right (.left hw)
          · have hka : k < a := lt_trans hky hya_lt
            have hnot_ak : ¬ (a < k) := not_lt.mpr (le_of_lt hka)
            unfold subtreeAtKey
            rw [ite_eq_right_of_eq_false _ _ (eq_false hnot_ak), ite_eq_left_of_eq_true _ _ (eq_true hka)]
            unfold subtreeAtKey
            rw [ite_eq_right_of_eq_false _ _ (eq_false hay_lt), ite_eq_left_of_eq_true _ _ (eq_true hya_lt)]
            exact hw
          · exfalso
            have : a = ry := le_antisymm (not_lt.mp hya_lt) (not_lt.mp hay_lt)
            exact hay (this.trans hry)
        · exact hw

theorem mem_subtreeAtKey_spliceMin {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) {a w : α}
    (hw : w ∈ subtreeAtKey (spliceMin t) a) :
    w ∈ subtreeAtKey t a := by
  induction t with
  | nil => simp [spliceMin, subtreeAtKey] at hw
  | node k l r ihl _ =>
    rw [isBST_node_iff] at ht
    rcases ht with ⟨hl, hr, hlt, hgt⟩
    cases l with
    | nil =>
      simp only [spliceMin] at hw
      have ha_in_r : a ∈ r := by
        by_contra hna
        rw [subtreeAtKey_nil_of_not_mem hna] at hw
        cases hw
      have hka : k < a := hgt a ha_in_r
      have hnot_ak : ¬ (a < k) := not_lt.mpr (le_of_lt hka)
      unfold subtreeAtKey
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnot_ak), ite_eq_left_of_eq_true _ _ (eq_true hka)]
      exact hw
    | node lk ll lr =>
      have hspl : spliceMin (BinaryTree.node k (.node lk ll lr) r) =
          .node k (spliceMin (.node lk ll lr)) r := rfl
      rw [hspl] at hw
      unfold subtreeAtKey at hw ⊢
      split_ifs at hw ⊢ with hak hka
      · exact ihl hl hw
      · exact hw
      · rw [BinaryTree.mem_node_iff] at hw ⊢
        rcases hw with rfl | hw | hw
        · exact Or.inl rfl
        · obtain ⟨m, hm⟩ : ∃ m, (BinaryTree.node lk ll lr).minKey? = some m := by
            rw [minKey?_eq_head?_leftSpine]
            cases hls : leftSpine (.node lk ll lr) with
            | nil => simp [leftSpine] at hls
            | cons x xs => exact ⟨x, rfl⟩
          have hkl' := (spliceMin_isBST_and_keys hl hm).2
          rw [← mem_keyFinset_iff, hkl', Finset.mem_sdiff, mem_keyFinset_iff] at hw
          exact Or.inr (Or.inl hw.1)
        · exact Or.inr (Or.inr hw)

theorem popCascade_isBST_and_keys {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) {m : α} (hm : t.minKey? = some m) :
    (popCascade t).IsBST ∧ keyFinset (popCascade t) = keyFinset t \ {m} := by
  unfold popCascade
  obtain ⟨h0, hk0⟩ := spliceMin_isBST_and_keys ht hm
  suffices ∀ (pairs : List (α × α)) (acc : BinaryTree α),
      acc.IsBST →
      (pairs.foldl (fun s p => rotateRightEdge s p.1 p.2) acc).IsBST ∧
        keyFinset (pairs.foldl (fun s p => rotateRightEdge s p.1 p.2) acc) = keyFinset acc by
    obtain ⟨h1, hk1⟩ := this (popCascadePairs t) (spliceMin t) h0
    exact ⟨h1, hk1.trans hk0⟩
  intro pairs
  induction pairs with
  | nil => intro acc hacc; exact ⟨hacc, rfl⟩
  | cons p rest ih =>
    intro acc hacc
    obtain ⟨h1, hk1⟩ := rotateRightEdge_isBST_and_keys hacc p.1 p.2
    obtain ⟨h2, hk2⟩ := ih _ h1
    exact ⟨h2, hk2.trans hk1⟩

theorem mem_subtreeAtKey_popCascade_lt {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) {m a w : α}
    (hm : t.minKey? = some m) (hwa : w < a)
    (hw : w ∈ subtreeAtKey (popCascade t) a) :
    w ∈ subtreeAtKey t a := by
  unfold popCascade at hw
  obtain ⟨h0, _⟩ := spliceMin_isBST_and_keys ht hm
  have hfold : ∀ (pairs : List (α × α)) (acc : BinaryTree α),
      acc.IsBST →
      w ∈ subtreeAtKey (pairs.foldl (fun s p => rotateRightEdge s p.1 p.2) acc) a →
      w ∈ subtreeAtKey acc a := by
    intro pairs
    induction pairs with
    | nil => intro acc _ h; exact h
    | cons p rest ih =>
      intro acc hacc h
      have h1 := (rotateRightEdge_isBST_and_keys hacc p.1 p.2).1
      exact mem_subtreeAtKey_rotateRightEdge_lt hacc hwa (ih _ h1 h)
  exact mem_subtreeAtKey_spliceMin ht (hfold (popCascadePairs t) (spliceMin t) h0 hw)

/-! ### `adjacentPairs` and `popCascade` Structural Equations -/

theorem mem_adjacentPairs_snd {α : Type} :
    ∀ {xs : List α} {p : α × α}, p ∈ adjacentPairs xs → p.2 ∈ xs
  | [], _, hp => by simp [adjacentPairs] at hp
  | [_], _, hp => by simp [adjacentPairs] at hp
  | a :: b :: rest, p, hp => by
    simp only [adjacentPairs, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact List.mem_cons_of_mem a List.mem_cons_self
    · exact List.mem_cons_of_mem a (List.mem_cons_of_mem b (mem_adjacentPairs_snd hp))

theorem adjacentPairs_append_even {α : Type} :
    ∀ (xs ys : List α), xs.length % 2 = 0 →
      adjacentPairs (xs ++ ys) = adjacentPairs xs ++ adjacentPairs ys
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | a :: b :: rest, ys, h => by
    have hrest : rest.length % 2 = 0 := by simp at h; omega
    simp [adjacentPairs, adjacentPairs_append_even rest ys hrest]

theorem adjacentPairs_length {α : Type} :
    ∀ (xs : List α), (adjacentPairs xs).length = xs.length / 2
  | [] => by simp [adjacentPairs]
  | [_] => by simp [adjacentPairs]
  | _ :: _ :: rest => by
    simp only [adjacentPairs, List.length_cons, adjacentPairs_length rest]
    omega

theorem foldl_rotateRightEdge_node_lt {α : Type} [LinearOrder α]
    (pairs : List (α × α)) (r : α) (tL R : BinaryTree α)
    (hlt : ∀ p ∈ pairs, p.2 < r) :
    pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (.node r tL R) =
      .node r (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) tL) R := by
  induction pairs generalizing tL with
  | nil => rfl
  | cons p rest ih =>
    have hp : p.2 < r := hlt p List.mem_cons_self
    have hstep : rotateRightEdge (.node r tL R) p.1 p.2 = .node r (rotateRightEdge tL p.1 p.2) R := by
      conv_lhs => unfold rotateRightEdge
      rw [ite_eq_left_of_eq_true _ _ (eq_true hp)]
    rw [List.foldl_cons, hstep, List.foldl_cons]
    exact ih _ (fun q hq => hlt q (List.mem_cons_of_mem p hq))

/-- Equation 1: when `L ≠ .nil` has odd left-spine length, `popCascade` stays inside `L`. -/
theorem popCascade_node_odd {α : Type} [LinearOrder α]
    {r : α} {L R : BinaryTree α} (ht : (BinaryTree.node r L R).IsBST)
    (hodd : (leftSpine L).length % 2 = 1) :
    popCascade (.node r L R) = .node r (popCascade L) R := by
  have hLne : L ≠ .nil := by
    intro h; subst h; simp [leftSpine] at hodd
  have hls_ne : leftSpine L ≠ [] := (leftSpine_eq_nil_iff L).not.mpr hLne
  rw [isBST_node_iff] at ht
  rcases ht with ⟨hL, hR, hlt, _⟩
  have hspl : spliceMin (.node r L R) = .node r (spliceMin L) R := by
    cases L with
    | nil => contradiction
    | node _ _ _ => rfl
  have htail : (leftSpine (.node r L R)).tail = (leftSpine L).tail ++ [r] := by
    simp only [leftSpine]
    cases hls : leftSpine L with
    | nil => contradiction
    | cons a as => rfl
  have heven : (leftSpine L).tail.length % 2 = 0 := by
    have : 1 ≤ (leftSpine L).length := List.length_pos_of_ne_nil hls_ne
    simp only [List.length_tail]; omega
  have hpairs : popCascadePairs (.node r L R) = popCascadePairs L := by
    unfold popCascadePairs
    rw [htail, adjacentPairs_append_even _ [r] heven]
    simp [adjacentPairs]
  unfold popCascade
  rw [hspl, hpairs]
  apply foldl_rotateRightEdge_node_lt
  intro p hp
  have hp_mem : p.2 ∈ leftSpine L :=
    List.mem_of_mem_tail (mem_adjacentPairs_snd hp)
  exact hlt p.2 (mem_of_mem_leftSpine L hp_mem)

/-- Equation 2: when `L = .node lk ll lr` has even left-spine length (`≥ 2`), `popCascade`
rotates `lk` above `r` after running `popCascade ll`. -/
theorem popCascade_node_even {α : Type} [LinearOrder α]
    {r lk : α} {ll lr R : BinaryTree α}
    (ht : (BinaryTree.node r (.node lk ll lr) R).IsBST)
    (heven : (leftSpine (.node lk ll lr)).length % 2 = 0) :
    popCascade (.node r (.node lk ll lr) R) = .node lk (popCascade ll) (.node r lr R) := by
  have hll_odd : (leftSpine ll).length % 2 = 1 := by
    simp only [leftSpine, List.length_append, List.length_singleton] at heven
    omega
  have hll_ne : ll ≠ .nil := by
    intro h; subst h; simp [leftSpine] at hll_odd
  have hls_ll_ne : leftSpine ll ≠ [] := (leftSpine_eq_nil_iff ll).not.mpr hll_ne
  rw [isBST_node_iff] at ht
  rcases ht with ⟨hL, hR, hlt, _⟩
  have hL_pop : popCascade (.node lk ll lr) = .node lk (popCascade ll) lr :=
    popCascade_node_odd hL hll_odd
  have hspl : spliceMin (.node r (.node lk ll lr) R) =
      .node r (spliceMin (.node lk ll lr)) R := rfl
  have htail_L : (leftSpine (.node lk ll lr)).tail = (leftSpine ll).tail ++ [lk] := by
    simp only [leftSpine]
    cases hls : leftSpine ll with
    | nil => contradiction
    | cons a as => rfl
  have htail_H : (leftSpine (.node r (.node lk ll lr) R)).tail =
      (leftSpine ll).tail ++ [lk, r] := by
    simp only [leftSpine, List.append_assoc, List.singleton_append]
    cases hls : leftSpine ll with
    | nil => contradiction
    | cons a as => rfl
  have htail_ll_even : (leftSpine ll).tail.length % 2 = 0 := by
    have : 1 ≤ (leftSpine ll).length := List.length_pos_of_ne_nil hls_ll_ne
    simp only [List.length_tail]; omega
  have hpairs_L : popCascadePairs (.node lk ll lr) = adjacentPairs (leftSpine ll).tail := by
    unfold popCascadePairs
    rw [htail_L, adjacentPairs_append_even _ [lk] htail_ll_even]
    simp [adjacentPairs]
  have hpairs_H : popCascadePairs (.node r (.node lk ll lr) R) =
      popCascadePairs (.node lk ll lr) ++ [(lk, r)] := by
    change adjacentPairs (leftSpine (.node r (.node lk ll lr) R)).tail = _
    rw [htail_H, adjacentPairs_append_even _ [lk, r] htail_ll_even, ← hpairs_L]
    rfl
  conv_lhs => unfold popCascade
  rw [hspl, hpairs_H, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hfold_lt : ∀ p ∈ popCascadePairs (.node lk ll lr), p.2 < r := by
    intro p hp
    have hp_mem : p.2 ∈ leftSpine (.node lk ll lr) :=
      List.mem_of_mem_tail (mem_adjacentPairs_snd hp)
    exact hlt p.2 (mem_of_mem_leftSpine _ hp_mem)
  rw [foldl_rotateRightEdge_node_lt _ r _ R hfold_lt]
  change rotateRightEdge (.node r (popCascade (.node lk ll lr)) R) lk r = _
  rw [hL_pop]
  conv_lhs => unfold rotateRightEdge
  rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl r)),
      ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl r))]
  dsimp only
  rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]

/-- Post-exit subtree separation: after `popCascade H`, for any `1 ≤ j` with `2*j+1 < |LS(H)|`,
writing `(x, y, z) = (v_{2j-1}, v_{2j}, v_{2j+1})`, NO vertex `a ∈ (x, z)` retains a descendant
`w < x`! -/
theorem not_mem_subtreeAtKey_popCascade_between {H : BinaryTree ℕ} (hH : H.IsBST)
    {j : ℕ} (hj : 1 ≤ j) (hj_len : 2 * j + 1 < (leftSpine H).length)
    {a w : ℕ}
    (hxa : (leftSpine H)[2 * j - 1]'(by omega) < a)
    (haz : a < (leftSpine H)[2 * j + 1]'hj_len)
    (hwx : w < (leftSpine H)[2 * j - 1]'(by omega)) :
    w ∉ subtreeAtKey (popCascade H) a := by
  induction H with
  | nil => simp [leftSpine] at hj_len
  | node r L R ihL _ =>
    have hH_orig := hH
    rw [isBST_node_iff] at hH
    rcases hH with ⟨hL, hR, hlt, hgt⟩
    have hlen_H : (leftSpine (.node r L R)).length = (leftSpine L).length + 1 := by
      simp [leftSpine]
    by_cases hjL : 2 * j + 1 < (leftSpine L).length
    · -- `x, y, z` all lie inside `leftSpine L`
      have h_x_eq : (leftSpine (.node r L R))[2 * j - 1]'(by omega) =
          (leftSpine L)[2 * j - 1]'(by omega) := by
        simp [leftSpine, List.getElem_append_left (by omega : 2 * j - 1 < (leftSpine L).length)]
      have h_z_eq : (leftSpine (.node r L R))[2 * j + 1]'hj_len =
          (leftSpine L)[2 * j + 1]'hjL := by
        simp [leftSpine, List.getElem_append_left hjL]
      rw [h_x_eq] at hxa hwx
      rw [h_z_eq] at haz
      have hzr : (leftSpine L)[2 * j + 1]'hjL < r :=
        hlt _ (mem_of_mem_leftSpine L (List.getElem_mem hjL))
      have har : a < r := lt_trans haz hzr
      have hwa : w < a := lt_trans hwx hxa
      by_cases hpar : (leftSpine L).length % 2 = 1
      · rw [popCascade_node_odd hH_orig hpar]
        unfold subtreeAtKey
        rw [ite_eq_left_of_eq_true _ _ (eq_true har)]
        exact ihL hL hjL hxa haz hwx
      · have heven : (leftSpine L).length % 2 = 0 := by omega
        cases L with
        | nil => simp [leftSpine] at hjL
        | node lk ll lr =>
          have hrot : popCascade (.node r (.node lk ll lr) R) =
              rotateRightEdge (.node r (popCascade (.node lk ll lr)) R) lk r := by
            rw [popCascade_node_even hH_orig heven]
            have hll_odd : (leftSpine ll).length % 2 = 1 := by
              simp only [leftSpine, List.length_append, List.length_singleton] at heven; omega
            rw [popCascade_node_odd hL hll_odd]
            unfold rotateRightEdge
            rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl r)),
                ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl r))]
            dsimp only
            rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
          intro hw_in
          rw [hrot] at hw_in
          have hbst_inner : (BinaryTree.node r (popCascade (.node lk ll lr)) R).IsBST := by
            obtain ⟨m, hm⟩ : ∃ m, (BinaryTree.node lk ll lr).minKey? = some m := by
              rw [minKey?_eq_head?_leftSpine]
              cases hls : leftSpine (.node lk ll lr) with
              | nil => simp [leftSpine] at hls
              | cons u us => exact ⟨u, rfl⟩
            obtain ⟨hpop_bst, hpop_keys⟩ := popCascade_isBST_and_keys hL hm
            refine isBST_node_iff.mpr ⟨hpop_bst, hR, fun u hu => ?_, hgt⟩
            rw [← mem_keyFinset_iff, hpop_keys, Finset.mem_sdiff, mem_keyFinset_iff] at hu
            exact hlt u hu.1
          have hw_in' := mem_subtreeAtKey_rotateRightEdge_lt hbst_inner hwa hw_in
          unfold subtreeAtKey at hw_in'
          rw [ite_eq_left_of_eq_true _ _ (eq_true har)] at hw_in'
          exact ihL hL hjL hxa haz hwx hw_in'
    · -- `2 * j + 1 = (leftSpine L).length`, so `z = r`!
      have hj_eq : (leftSpine L).length = 2 * j + 1 := by omega
      have h_z_eq : (leftSpine (.node r L R))[2 * j + 1]'hj_len = r := by
        simp [leftSpine, hj_eq]
      rw [h_z_eq] at haz
      have hL_odd : (leftSpine L).length % 2 = 1 := by omega
      cases L with
      | nil => simp [leftSpine] at hj_eq
      | node y Ly Ry =>
        have hLy_len : (leftSpine Ly).length = 2 * j := by
          simp only [leftSpine, List.length_append, List.length_singleton] at hj_eq; omega
        have hL_even_Ly : (leftSpine Ly).length % 2 = 0 := by omega
        cases Ly with
        | nil => simp [leftSpine] at hLy_len; omega
        | node x Ax Rx =>
          have hAx_len : (leftSpine Ax).length = 2 * j - 1 := by
            simp only [leftSpine, List.length_append, List.length_singleton] at hLy_len; omega
          have h_x_eq : (leftSpine (.node r (.node y (.node x Ax Rx) Ry) R))[2 * j - 1]'(by omega)
              = x := by
            have hls_all : leftSpine (.node r (.node y (.node x Ax Rx) Ry) R) =
                leftSpine Ax ++ [x, y, r] := by
              simp [leftSpine, List.append_assoc]
            simp only [hls_all]
            rw [List.getElem_append_right (by omega)]
            simp [hAx_len]
          rw [h_x_eq] at hxa hwx
          have hpop_H : popCascade (.node r (.node y (.node x Ax Rx) Ry) R) =
              .node r (.node x (popCascade Ax) (.node y Rx Ry)) R := by
            rw [popCascade_node_odd hH_orig hL_odd]
            have hLy_even' : (leftSpine (.node x Ax Rx)).length % 2 = 0 := by
              rw [hLy_len]; omega
            rw [popCascade_node_even hL hLy_even']
          rw [hpop_H]
          intro hw_in
          unfold subtreeAtKey at hw_in
          rw [ite_eq_left_of_eq_true _ _ (eq_true haz)] at hw_in
          unfold subtreeAtKey at hw_in
          rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.mpr (le_of_lt hxa))),
              ite_eq_left_of_eq_true _ _ (eq_true hxa)] at hw_in
          have hw_mem_sub : w ∈ BinaryTree.node y Rx Ry := mem_of_mem_subtreeAtKey hw_in
          rw [isBST_node_iff] at hL
          rcases hL with ⟨hLy, hRy, hlt_y, hgt_y⟩
          rw [isBST_node_iff] at hLy
          rcases hLy with ⟨_, _, _, hgt_x⟩
          have hxy : x < y := hlt_y x .here
          have hwx_gt : x < w := by
            rw [BinaryTree.mem_node_iff] at hw_mem_sub
            rcases hw_mem_sub with rfl | hw_mem_sub | hw_mem_sub
            · exact hxy
            · exact hgt_x w hw_mem_sub
            · exact lt_trans hxy (hgt_y w hw_mem_sub)
          exact absurd (lt_trans hwx hwx_gt) (lt_irrefl w)

/-! ## 2. Spine-Folding Simulation (`spineFoldTree` ↔ `FoldedOp.step`) -/

def ValidFrames : ℕ → BinaryTree ℕ → List (ℕ × BinaryTree ℕ) → Prop
  | prev, acc, [] => acc.IsBST ∧ ∀ k ∈ acc, k < prev
  | prev, acc, (bNext, lNext) :: rest =>
    acc.IsBST ∧ (∀ k ∈ acc, k < prev) ∧ prev < bNext ∧
      lNext.IsBST ∧ (∀ k ∈ lNext, prev < k ∧ k < bNext) ∧
      ValidFrames bNext (.node prev acc lNext) rest

theorem validFrames_of_bst (prev : ℕ) (acc R : BinaryTree ℕ)
    (hacc : acc.IsBST) (hacc_lt : ∀ k ∈ acc, k < prev)
    (hR : R.IsBST) (hR_gt : ∀ k ∈ R, prev < k) :
    ValidFrames prev acc (rightSpineFrames R) := by
  induction R generalizing prev acc with
  | nil => exact ⟨hacc, hacc_lt⟩
  | node bNext lNext rNext _ ihr =>
    rw [isBST_node_iff] at hR
    rcases hR with ⟨hlNext, hrNext, hltNext, hgtNext⟩
    have hprev_lt : prev < bNext := hR_gt bNext .here
    have hl_bounds : ∀ k ∈ lNext, prev < k ∧ k < bNext :=
      fun k hk => ⟨hR_gt k (.left hk), hltNext k hk⟩
    have hnode_bst : (BinaryTree.node prev acc lNext).IsBST :=
      isBST_node_iff.mpr ⟨hacc, hlNext, hacc_lt, fun k hk => (hl_bounds k hk).1⟩
    have hnode_lt : ∀ k ∈ BinaryTree.node prev acc lNext, k < bNext := by
      intro k hk
      rw [BinaryTree.mem_node_iff] at hk
      rcases hk with rfl | hk | hk
      · exact hprev_lt
      · exact lt_trans (hacc_lt k hk) hprev_lt
      · exact (hl_bounds k hk).2
    exact ⟨hacc, hacc_lt, hprev_lt, hlNext, hl_bounds,
      ihr bNext (.node prev acc lNext) hnode_bst hnode_lt hrNext hgtNext⟩

theorem spineFoldGo_isBST {prev : ℕ} {acc : BinaryTree ℕ} {frames : List (ℕ × BinaryTree ℕ)}
    (hv : ValidFrames prev acc frames) : (spineFoldGo prev acc frames).IsBST := by
  induction frames generalizing prev acc with
  | nil =>
    exact isBST_node_iff.mpr ⟨hv.1, isBST_nil, hv.2, fun _ h => by cases h⟩
  | cons hd rest ih =>
    exact ih hv.2.2.2.2.2

theorem leftSpine_spineFoldGo (prev : ℕ) (acc : BinaryTree ℕ)
    (frames : List (ℕ × BinaryTree ℕ)) :
    leftSpine (spineFoldGo prev acc frames) = leftSpine acc ++ (prev :: frames.map Prod.fst) := by
  induction frames generalizing prev acc with
  | nil => simp [spineFoldGo, leftSpine]
  | cons hd rest ih =>
    rcases hd with ⟨bNext, lNext⟩
    simp only [spineFoldGo, ih, leftSpine, List.map_cons, List.append_assoc,
      List.singleton_append]

theorem rightSpineFrames_map_fst (t : BinaryTree ℕ) :
    (rightSpineFrames t).map Prod.fst = rightSpine t := by
  induction t with
  | nil => rfl
  | node k l r _ ih => simp [rightSpineFrames, rightSpine, ih]

theorem keyFinset_spineFoldGo (prev : ℕ) (acc : BinaryTree ℕ)
    (frames : List (ℕ × BinaryTree ℕ)) :
    keyFinset (spineFoldGo prev acc frames) =
      insert prev (keyFinset acc ∪
        frames.foldr (fun p s => insert p.1 (keyFinset p.2 ∪ s)) ∅) := by
  induction frames generalizing prev acc with
  | nil => simp [spineFoldGo, keyFinset]
  | cons hd rest ih =>
    rcases hd with ⟨bNext, lNext⟩
    simp only [spineFoldGo, ih, keyFinset, List.foldr_cons]
    ext u; simp [Finset.mem_insert, Finset.mem_union]; tauto

theorem keyFinset_spineFoldTree (H : BinaryTree ℕ) :
    keyFinset (spineFoldTree H).1 = keyFinset H := by
  cases H with
  | nil => rfl
  | node b1 L1 R1 =>
    simp only [spineFoldTree, rightSpineFrames, keyFinset_spineFoldGo, keyFinset]
    suffices ∀ R : BinaryTree ℕ,
        (rightSpineFrames R).foldr (fun p s => insert p.1 (keyFinset p.2 ∪ s)) ∅ = keyFinset R by
      rw [this R1]
    intro R
    induction R with
    | nil => rfl
    | node k l r _ ih => simp [rightSpineFrames, keyFinset, ih]

theorem spineFoldTree_isBST {H : BinaryTree ℕ} (hH : H.IsBST) :
    (spineFoldTree H).1.IsBST := by
  cases H with
  | nil => exact isBST_nil
  | node b1 L1 R1 =>
    rw [isBST_node_iff] at hH
    rcases hH with ⟨hL1, hR1, hlt, hgt⟩
    exact spineFoldGo_isBST (validFrames_of_bst b1 L1 R1 hL1 hlt hR1 hgt)

theorem spineFoldTree_eq_nil_iff (H : BinaryTree ℕ) :
    (spineFoldTree H).1 = .nil ↔ H = .nil := by
  cases H with
  | nil => simp [spineFoldTree]
  | node b1 L1 R1 =>
    simp only [spineFoldTree, rightSpineFrames, reduceCtorEq, iff_false]
    suffices ∀ prev acc frames, spineFoldGo prev acc frames ≠ .nil from
      this b1 L1 (rightSpineFrames R1)
    intro prev acc frames
    induction frames generalizing prev acc with
    | nil => simp [spineFoldGo]
    | cons hd rest ih => exact ih hd.1 (.node prev acc hd.2)

theorem modifyLeftAt_spineFoldGo {prev : ℕ} {acc : BinaryTree ℕ}
    {frames : List (ℕ × BinaryTree ℕ)} (hv : ValidFrames prev acc frames)
    {target : ℕ} (ht : target ≤ prev) (f : BinaryTree ℕ → BinaryTree ℕ) :
    modifyLeftAt (spineFoldGo prev acc frames) target f =
      if target < prev then spineFoldGo prev (modifyLeftAt acc target f) frames
      else spineFoldGo prev (f acc) frames := by
  induction frames generalizing prev acc with
  | nil =>
    simp only [spineFoldGo, modifyLeftAt]
    split_ifs with h1 h2
    · rfl
    · omega
    · rfl
  | cons hd rest ih =>
    rcases hd with ⟨bNext, lNext⟩
    have hprev_lt : prev < bNext := hv.2.2.1
    have ht_lt : target < bNext := lt_of_le_of_lt ht hprev_lt
    simp only [spineFoldGo]
    rw [ih hv.2.2.2.2.2 (le_of_lt ht_lt)]
    simp only [ht_lt, ↓reduceIte, modifyLeftAt]
    split_ifs with h1 h2
    · rfl
    · omega
    · rfl

theorem spliceMin_spineFoldGo (prev : ℕ) (acc : BinaryTree ℕ)
    (frames : List (ℕ × BinaryTree ℕ)) :
    spliceMin (spineFoldGo prev acc frames) =
      match acc with
      | .nil =>
        match frames with
        | [] => .nil
        | (b2, L2) :: rest2 => spineFoldGo b2 L2 rest2
      | .node _ _ _ => spineFoldGo prev (spliceMin acc) frames := by
  induction frames generalizing prev acc with
  | nil =>
    cases acc <;> rfl
  | cons hd rest ih =>
    rcases hd with ⟨b2, L2⟩
    simp only [spineFoldGo]
    rw [ih b2 (.node prev acc L2)]
    cases acc <;> rfl

theorem rotateRightEdge_spineFoldGo_lt {prev : ℕ} {acc : BinaryTree ℕ}
    {frames : List (ℕ × BinaryTree ℕ)} (hv : ValidFrames prev acc frames)
    (x : ℕ) {p : ℕ} (hp : p < prev) :
    rotateRightEdge (spineFoldGo prev acc frames) x p =
      spineFoldGo prev (rotateRightEdge acc x p) frames := by
  induction frames generalizing prev acc with
  | nil =>
    simp [spineFoldGo, rotateRightEdge, hp]
  | cons hd rest ih =>
    rcases hd with ⟨bNext, lNext⟩
    have hp_next : p < bNext := lt_trans hp hv.2.2.1
    simp only [spineFoldGo]
    rw [ih hv.2.2.2.2.2 hp_next]
    simp [rotateRightEdge, hp]

theorem rotateRightEdge_spineFoldGo_here {prev : ℕ} {acc : BinaryTree ℕ}
    {bNext : ℕ} {lNext : BinaryTree ℕ} {bAfter : ℕ} {lAfter : BinaryTree ℕ}
    {rest2 : List (ℕ × BinaryTree ℕ)}
    (hv : ValidFrames bNext (.node prev acc lNext) ((bAfter, lAfter) :: rest2)) :
    rotateRightEdge (spineFoldGo bNext (.node prev acc lNext) ((bAfter, lAfter) :: rest2))
        prev bNext =
      spineFoldGo bAfter (.node prev acc (.node bNext lNext lAfter)) rest2 := by
  have hb_lt : bNext < bAfter := hv.2.2.1
  change rotateRightEdge (spineFoldGo bAfter (.node bNext (.node prev acc lNext) lAfter) rest2)
      prev bNext = _
  rw [rotateRightEdge_spineFoldGo_lt hv.2.2.2.2.2 prev hb_lt]
  simp [rotateRightEdge]

/-! ## 3. Full `FoldedOp.step` Simulation, `tauEmpty`, and Partition Chain -/

theorem mem_of_mem_rightSpine {α : Type} (t : BinaryTree α) {x : α}
    (hx : x ∈ rightSpine t) : x ∈ t := by
  induction t with
  | nil => simp [rightSpine] at hx
  | node k l r _ ihr =>
    simp only [rightSpine, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact .here
    · exact .right (ihr hx)

theorem nextOnSpine_append_of_not_mem {b1 b2 : ℕ} {xs ys : List ℕ}
    (h : b1 ∉ xs) :
    nextOnSpine (xs ++ b1 :: b2 :: ys) b1 = some b2 := by
  induction xs with
  | nil => simp [nextOnSpine]
  | cons a xs ih =>
    have hne : a ≠ b1 := fun heq => h (heq ▸ List.mem_cons_self)
    have hnot : b1 ∉ xs := fun hm => h (List.mem_cons_of_mem a hm)
    cases htail : xs ++ b1 :: b2 :: ys with
    | nil =>
      cases xs <;> simp at htail
    | cons c cs =>
      simp only [List.cons_append]
      rw [htail]
      simp only [nextOnSpine]
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne), ← htail]
      exact ih hnot

theorem takeThrough_append_of_not_mem {b1 : ℕ} {xs ys : List ℕ}
    (h : b1 ∉ xs) :
    takeThrough (xs ++ b1 :: ys) b1 = xs ++ [b1] := by
  induction xs with
  | nil => simp [takeThrough]
  | cons a xs ih =>
    have hne : a ≠ b1 := fun heq => h (heq ▸ List.mem_cons_self)
    have hnot : b1 ∉ xs := fun hm => h (List.mem_cons_of_mem a hm)
    simp [takeThrough, hne, ih hnot]

theorem subtreeAtKey_spineFoldGo_lt {prev : ℕ} {acc : BinaryTree ℕ}
    {frames : List (ℕ × BinaryTree ℕ)} (hv : ValidFrames prev acc frames)
    {v : ℕ} (hv_lt : v < prev) :
    subtreeAtKey (spineFoldGo prev acc frames) v = subtreeAtKey acc v := by
  induction frames generalizing prev acc with
  | nil =>
    simp only [spineFoldGo]
    conv_lhs => unfold subtreeAtKey
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv_lt)]
  | cons hd rest ih =>
    rcases hd with ⟨bNext, lNext⟩
    have hv_next : v < bNext := lt_trans hv_lt hv.2.2.1
    simp only [spineFoldGo]
    rw [ih hv.2.2.2.2.2 hv_next]
    conv_lhs => unfold subtreeAtKey
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv_lt)]

theorem subtreeAtKey_spineFoldGo_here {prev : ℕ} {acc : BinaryTree ℕ}
    {frames : List (ℕ × BinaryTree ℕ)} (hv : ValidFrames prev acc frames) :
    subtreeAtKey (spineFoldGo prev acc frames) prev =
      match frames with
      | [] => .node prev acc .nil
      | (_, lNext) :: _ => .node prev acc lNext := by
  cases frames with
  | nil =>
    simp only [spineFoldGo]
    conv_lhs => unfold subtreeAtKey
    rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl prev)),
        ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl prev))]
  | cons hd rest =>
    rcases hd with ⟨bNext, lNext⟩
    simp only [spineFoldGo]
    rw [subtreeAtKey_spineFoldGo_lt hv.2.2.2.2.2 hv.2.2.1]
    conv_lhs => unfold subtreeAtKey
    rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl prev)),
        ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl prev))]

theorem le_of_isRightRotEdge_spineFoldGo {b2 : ℕ} {acc : BinaryTree ℕ}
    {frames : List (ℕ × BinaryTree ℕ)} (hv : ValidFrames b2 acc frames)
    {u v : ℕ} (hb2_lt : b2 < v)
    (hrot : IsRightRotEdge (spineFoldGo b2 acc frames) u v) :
    b2 ≤ u := by
  induction frames generalizing b2 acc with
  | nil =>
    rcases hrot with ⟨A, B, C, hv_mem, _⟩
    simp only [spineFoldGo, BinaryTree.mem_node_iff] at hv_mem
    rcases hv_mem with rfl | hv_mem | hv_mem
    · exact absurd hb2_lt (lt_irrefl _)
    · exact absurd (lt_trans hb2_lt (hv.2 v hv_mem)) (lt_irrefl _)
    · cases hv_mem
  | cons hd rest ih =>
    rcases hd with ⟨b3, L3⟩
    rcases lt_trichotomy v b3 with hvb3 | rfl | hb3v
    · rcases hrot with ⟨A, B, C, _, hsub⟩
      simp only [spineFoldGo] at hsub
      rw [subtreeAtKey_spineFoldGo_lt hv.2.2.2.2.2 hvb3] at hsub
      conv at hsub =>
        lhs
        unfold subtreeAtKey
      rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.mpr (le_of_lt hb2_lt))),
          ite_eq_left_of_eq_true _ _ (eq_true hb2_lt)] at hsub
      have hu_mem_sub : u ∈ subtreeAtKey L3 v := by
        rw [hsub]
        exact .left .here
      have hu_L3 : u ∈ L3 := mem_of_mem_subtreeAtKey hu_mem_sub
      exact le_of_lt (hv.2.2.2.2.1 u hu_L3).1
    · rcases hrot with ⟨A, B, C, _, hsub⟩
      simp only [spineFoldGo] at hsub
      rw [subtreeAtKey_spineFoldGo_here hv.2.2.2.2.2] at hsub
      cases rest with
      | nil =>
        injection hsub with _ hleft _
        injection hleft with hb2_eq _ _
        omega
      | cons _ _ =>
        injection hsub with _ hleft _
        injection hleft with hb2_eq _ _
        omega
    · exact le_of_lt (lt_of_lt_of_le hv.2.2.1 (ih hv.2.2.2.2.2 hb3v hrot))

theorem upperRot_spineFoldGo (prev : ℕ) (acc R : BinaryTree ℕ) :
    ∀ (_hbst : (BinaryTree.node prev acc R).IsBST) {u v r : ℕ},
    rootKey? (spineFoldGo prev acc (rightSpineFrames R)) = some r →
    prev ≤ u → u < v → v < r →
    u ∈ leftSpine (spineFoldGo prev acc (rightSpineFrames R)) →
    v ∈ leftSpine (spineFoldGo prev acc (rightSpineFrames R)) →
    IsRightRotEdge (spineFoldGo prev acc (rightSpineFrames R)) u v →
    ∃ x y, prev < x ∧ x < y ∧ y ∈ R ∧
      rotateRightEdge (spineFoldGo prev acc (rightSpineFrames R)) u v =
        spineFoldGo prev acc (rightSpineFrames (rotateLeftEdge R y x)) := by
  induction R generalizing prev acc with
  | nil =>
    intro _ u v r hroot hprev_u huv hvr _ _ _
    simp only [rightSpineFrames, spineFoldGo, rootKey?, Option.some.injEq] at hroot
    omega
  | node b2 L2 R2 _ ihR2 =>
    intro hbst u v r hroot hprev_u huv hvr hu_ls hv_ls hrot
    rw [isBST_node_iff] at hbst
    rcases hbst with ⟨hacc, hR_bst, hacc_lt, hR_gt⟩
    have hv_frames : ValidFrames prev acc (rightSpineFrames (.node b2 L2 R2)) :=
      validFrames_of_bst prev acc (.node b2 L2 R2) hacc hacc_lt hR_bst hR_gt
    rw [isBST_node_iff] at hR_bst
    rcases hR_bst with ⟨hL2, hR2, hL2_lt, hR2_gt⟩
    have hprev_b2 : prev < b2 := hR_gt b2 .here
    have hls_eq : leftSpine (spineFoldGo prev acc (rightSpineFrames (.node b2 L2 R2))) =
        leftSpine acc ++ (prev :: b2 :: rightSpine R2) := by
      rw [leftSpine_spineFoldGo, rightSpineFrames_map_fst]; rfl
    have hv_mem := hv_ls
    rw [hls_eq, List.mem_append, List.mem_cons, List.mem_cons] at hv_mem
    have hb2_le_v : b2 ≤ v := by
      rcases hv_mem with hv_acc | rfl | rfl | hv_rs
      · exfalso
        have : v < prev := hacc_lt v (mem_of_mem_leftSpine acc hv_acc)
        omega
      · omega
      · exact le_rfl
      · exact le_of_lt (hR2_gt v (mem_of_mem_rightSpine R2 hv_rs))
    rcases eq_or_lt_of_le hb2_le_v with hb2_eq_v | hb2_lt_v
    · -- `v = b2`, so `u = prev` and `R2 = .node b3 L3 R3`
      subst hb2_eq_v
      have hu_eq : u = prev := by
        have hu_mem := hu_ls
        rw [hls_eq, List.mem_append, List.mem_cons, List.mem_cons] at hu_mem
        rcases hu_mem with hu_acc | rfl | rfl | hu_rs
        · exfalso
          have : u < prev := hacc_lt u (mem_of_mem_leftSpine acc hu_acc)
          omega
        · rfl
        · omega
        · exfalso
          have : b2 < u := hR2_gt u (mem_of_mem_rightSpine R2 hu_rs)
          omega
      subst hu_eq
      cases R2 with
      | nil =>
        simp only [rightSpineFrames, spineFoldGo, rootKey?, Option.some.injEq] at hroot
        omega
      | node b3 L3 R3 =>
        have hb2_b3 : b2 < b3 := hR2_gt b3 .here
        refine ⟨b2, b3, hprev_b2, hb2_b3, .right .here, ?_⟩
        have h_lhs : rotateRightEdge
            (spineFoldGo u acc (rightSpineFrames (.node b2 L2 (.node b3 L3 R3)))) u b2 =
            spineFoldGo b3 (.node u acc (.node b2 L2 L3)) (rightSpineFrames R3) := by
          exact rotateRightEdge_spineFoldGo_here hv_frames.2.2.2.2.2
        rw [h_lhs]
        have h_rotL : rotateLeftEdge (.node b2 L2 (.node b3 L3 R3)) b3 b2 =
            .node b3 (.node b2 L2 L3) R3 := by
          conv_lhs => unfold rotateLeftEdge
          rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl b2)),
              ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl b2))]
          dsimp only
          rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
        rw [h_rotL]
        rfl
    · -- `b2 < v`, so `b2 ≤ u`, recurse into `R2`
      have hb2_le_u : b2 ≤ u :=
        le_of_isRightRotEdge_spineFoldGo hv_frames.2.2.2.2.2 hb2_lt_v hrot
      have hbst_next : (BinaryTree.node b2 (.node prev acc L2) R2).IsBST := by
        have hnode_bst : (BinaryTree.node prev acc L2).IsBST :=
          isBST_node_iff.mpr ⟨hacc, hL2, hacc_lt, fun k hk => hR_gt k (.left hk)⟩
        refine isBST_node_iff.mpr ⟨hnode_bst, hR2, ?_, hR2_gt⟩
        intro k hk
        rw [BinaryTree.mem_node_iff] at hk
        rcases hk with rfl | hk | hk
        · exact hprev_b2
        · exact lt_trans (hacc_lt k hk) hprev_b2
        · exact hL2_lt k hk
      obtain ⟨x, y, hb2_x, hxy, hy_R2, heq⟩ :=
        ihR2 b2 (.node prev acc L2) hbst_next hroot hb2_le_u huv hvr hu_ls hv_ls hrot
      refine ⟨x, y, lt_trans hprev_b2 hb2_x, hxy, .right hy_R2, ?_⟩
      have h_rotL : rotateLeftEdge (.node b2 L2 R2) y x =
          .node b2 L2 (rotateLeftEdge R2 y x) := by
        conv_lhs => unfold rotateLeftEdge
        rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.mpr (le_of_lt hb2_x))),
            ite_eq_left_of_eq_true _ _ (eq_true hb2_x)]
      rw [h_rotL]
      exact heq

theorem validFrames_acc {prev : ℕ} {acc : BinaryTree ℕ}
    {frames : List (ℕ × BinaryTree ℕ)} (hv : ValidFrames prev acc frames) :
    acc.IsBST ∧ ∀ k ∈ acc, k < prev := by
  cases frames with
  | nil => exact hv
  | cons _ _ => exact ⟨hv.1, hv.2.1⟩

theorem validFrames_preserve_bst {prev : ℕ} {acc acc' : BinaryTree ℕ}
    {frames : List (ℕ × BinaryTree ℕ)}
    (hv : ValidFrames prev acc frames)
    (hacc' : acc'.IsBST) (hkeys : keyFinset acc' = keyFinset acc) :
    ValidFrames prev acc' frames := by
  have hlt' : ∀ k ∈ acc', k < prev := by
    intro k hk
    rw [← mem_keyFinset_iff, hkeys, mem_keyFinset_iff] at hk
    exact (validFrames_acc hv).2 k hk
  cases frames with
  | nil => exact ⟨hacc', hlt'⟩
  | cons hd rest =>
    rcases hd with ⟨bNext, lNext⟩
    have hnode' : (BinaryTree.node prev acc' lNext).IsBST :=
      isBST_node_iff.mpr ⟨hacc', hv.2.2.2.1, hlt', fun k hk => (hv.2.2.2.2.1 k hk).1⟩
    have hkeys_node : keyFinset (BinaryTree.node prev acc' lNext) =
        keyFinset (BinaryTree.node prev acc lNext) := by
      simp [keyFinset, hkeys]
    exact ⟨hacc', hlt', hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1,
      validFrames_preserve_bst hv.2.2.2.2.2 hnode' hkeys_node⟩

theorem foldl_rotateRightEdge_spineFoldGo_lt
    (pairs : List (ℕ × ℕ)) {prev : ℕ} {acc : BinaryTree ℕ}
    {frames : List (ℕ × BinaryTree ℕ)}
    (hv : ValidFrames prev acc frames)
    (hlt : ∀ p ∈ pairs, p.2 < prev) :
    pairs.foldl (fun s p => rotateRightEdge s p.1 p.2) (spineFoldGo prev acc frames) =
      spineFoldGo prev (pairs.foldl (fun s p => rotateRightEdge s p.1 p.2) acc) frames := by
  induction pairs generalizing acc with
  | nil => rfl
  | cons p rest ih =>
    have hp : p.2 < prev := hlt p List.mem_cons_self
    simp only [List.foldl_cons]
    rw [rotateRightEdge_spineFoldGo_lt hv p.1 hp]
    obtain ⟨hacc', hkeys'⟩ := rotateRightEdge_isBST_and_keys (validFrames_acc hv).1 p.1 p.2
    have hv' := validFrames_preserve_bst hv hacc' hkeys'
    exact ih hv' (fun q hq => hlt q (List.mem_cons_of_mem p hq))

theorem step_push_spineFoldTree (H : BinaryTree ℕ) (hH : H.IsBST) (w : ℕ) :
    FoldedOp.step (spineFoldTree H) (.push w) = spineFoldTree (.node w .nil H) := by
  cases H with
  | nil => rfl
  | node b1 L1 R1 =>
    rw [isBST_node_iff] at hH
    rcases hH with ⟨hL1, hR1, hlt, hgt⟩
    have hv := validFrames_of_bst b1 L1 R1 hL1 hlt hR1 hgt
    simp only [spineFoldTree, rightSpineFrames, FoldedOp.step]
    rw [modifyLeftAt_spineFoldGo hv (le_refl b1)]
    simp [spineFoldGo]

theorem step_shift_spineFoldTree {H : BinaryTree ℕ} (hH : H.IsBST) {P : ℕ}
    (hval : FoldedOp.Valid P (spineFoldTree H) .shift) :
    ∃ x y, x < y ∧ y ∈ H ∧
      FoldedOp.step (spineFoldTree H) .shift = spineFoldTree (rotateLeftEdge H y x) := by
  rcases hval with ⟨b, hb, _, hroot_ne⟩
  cases H with
  | nil => simp [spineFoldTree] at hb
  | node b1 L1 R1 =>
    simp only [spineFoldTree, rightSpineFrames, Option.some.injEq] at hb
    subst hb
    cases R1 with
    | nil =>
      simp [spineFoldTree, rightSpineFrames, spineFoldGo, rootKey?] at hroot_ne
    | node b2 L2 R2 =>
      rw [isBST_node_iff] at hH
      rcases hH with ⟨hL1, hR1, hlt, hgt⟩
      have hb1_b2 : b1 < b2 := hgt b2 .here
      refine ⟨b1, b2, hb1_b2, .right .here, ?_⟩
      have hb1_not_mem : b1 ∉ leftSpine L1 := by
        intro hm
        exact absurd (hlt b1 (mem_of_mem_leftSpine L1 hm)) (lt_irrefl b1)
      have hls : leftSpine (spineFoldGo b1 L1 ((b2, L2) :: rightSpineFrames R2)) =
          leftSpine L1 ++ b1 :: b2 :: rightSpine R2 := by
        change leftSpine (spineFoldGo b1 L1 (rightSpineFrames (.node b2 L2 R2))) = _
        rw [leftSpine_spineFoldGo, rightSpineFrames_map_fst]; rfl
      have h_rotL : rotateLeftEdge (.node b1 L1 (.node b2 L2 R2)) b2 b1 =
          .node b2 (.node b1 L1 L2) R2 := by
        conv_lhs => unfold rotateLeftEdge
        rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl b1)),
            ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl b1))]
        dsimp only
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      rw [h_rotL]
      dsimp only [spineFoldTree, rightSpineFrames, FoldedOp.step]
      rw [hls, nextOnSpine_append_of_not_mem hb1_not_mem]
      rfl

theorem step_upperRot_spineFoldTree {H : BinaryTree ℕ} (hH : H.IsBST) {P u v : ℕ}
    (hval : FoldedOp.Valid P (spineFoldTree H) (.upperRot u v)) :
    ∃ x y, x < y ∧ y ∈ H ∧
      FoldedOp.step (spineFoldTree H) (.upperRot u v) = spineFoldTree (rotateLeftEdge H y x) := by
  rcases hval with ⟨b, r, hb, hroot, _, hbu, huv, hvr, hu_ls, hv_ls, hrot⟩
  cases H with
  | nil => simp [spineFoldTree] at hb
  | node b1 L1 R1 =>
    simp only [spineFoldTree, rightSpineFrames, Option.some.injEq] at hb
    subst hb
    simp only [spineFoldTree, rightSpineFrames] at hroot hu_ls hv_ls hrot
    obtain ⟨x, y, hb1_x, hxy, hy_R1, heq⟩ :=
      upperRot_spineFoldGo b1 L1 R1 hH hroot hbu huv hvr hu_ls hv_ls hrot
    refine ⟨x, y, hxy, .right hy_R1, ?_⟩
    have h_rotL : rotateLeftEdge (.node b1 L1 R1) y x = .node b1 L1 (rotateLeftEdge R1 y x) := by
      conv_lhs => unfold rotateLeftEdge
      rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.mpr (le_of_lt hb1_x))),
          ite_eq_left_of_eq_true _ _ (eq_true hb1_x)]
    rw [h_rotL]
    simp only [spineFoldTree, rightSpineFrames, FoldedOp.step, heq]

theorem step_pop_spineFoldTree {H : BinaryTree ℕ} (hH : H.IsBST) (hne : H ≠ .nil) (s : ℕ) :
    FoldedOp.step (spineFoldTree H) (.pop s) = spineFoldTree (popCascade H) := by
  cases H with
  | nil => contradiction
  | node b1 L1 R1 =>
    have hH_orig := hH
    rw [isBST_node_iff] at hH
    rcases hH with ⟨hL1, hR1, hlt, hgt⟩
    have hv := validFrames_of_bst b1 L1 R1 hL1 hlt hR1 hgt
    have hb1_not_mem : b1 ∉ leftSpine L1 := by
      intro hm
      exact absurd (hlt b1 (mem_of_mem_leftSpine L1 hm)) (lt_irrefl b1)
    have hls : leftSpine (spineFoldGo b1 L1 (rightSpineFrames R1)) =
        leftSpine L1 ++ (b1 :: rightSpine R1) := by
      rw [leftSpine_spineFoldGo, rightSpineFrames_map_fst]
    have hsub : takeThrough (leftSpine (spineFoldGo b1 L1 (rightSpineFrames R1))) b1 =
        leftSpine (.node b1 L1 R1) := by
      rw [hls, takeThrough_append_of_not_mem hb1_not_mem]
      rfl
    cases L1 with
    | nil =>
      have hpop_nil : popCascade (.node b1 .nil R1) = R1 := by
        simp [popCascade, popCascadePairs, leftSpine, adjacentPairs, spliceMin]
      rw [hpop_nil]
      dsimp only [spineFoldTree, rightSpineFrames, FoldedOp.step]
      rw [hsub]
      simp only [leftSpine, List.nil_append, List.length_singleton, Nat.sub_self, ↓reduceIte]
      cases R1 with
      | nil =>
        have ht0 : spliceMin (spineFoldGo b1 .nil (rightSpineFrames .nil)) = .nil := rfl
        rw [ht0]
        simp
      | node b2 L2 R2 =>
        have ht0 : spliceMin (spineFoldGo b1 .nil (rightSpineFrames (.node b2 L2 R2))) =
            spineFoldGo b2 L2 (rightSpineFrames R2) := by
          rw [spliceMin_spineFoldGo]; rfl
        rw [ht0]
        have ht0_ne : spineFoldGo b2 L2 (rightSpineFrames R2) ≠ .nil := by
          have hne_R : (BinaryTree.node b2 L2 R2) ≠ .nil := by simp
          exact (spineFoldTree_eq_nil_iff (.node b2 L2 R2)).not.mpr hne_R
        rw [ite_eq_right_of_eq_false _ _ (eq_false ht0_ne)]
        change (spineFoldGo b2 L2 (rightSpineFrames R2),
          nextOnSpine (leftSpine (spineFoldGo b1 .nil (rightSpineFrames (.node b2 L2 R2)))) b1) = _
        rw [hls]
        simp only [leftSpine, List.nil_append, rightSpine, nextOnSpine, ↓reduceIte]
        rfl
    | node lk ll lr =>
      have hk_pos : 1 ≤ (leftSpine (.node lk ll lr)).length := by
        simp [leftSpine]
      have hk_eq : (leftSpine (.node b1 (.node lk ll lr) R1)).length - 1 =
          (leftSpine (.node lk ll lr)).length := by
        simp [leftSpine]
      have hk_ne : (leftSpine (.node b1 (.node lk ll lr) R1)).length - 1 ≠ 0 := by
        omega
      obtain ⟨mL, hmL⟩ : ∃ m, (BinaryTree.node lk ll lr).minKey? = some m := by
        rw [minKey?_eq_head?_leftSpine]
        cases hls_L : leftSpine (.node lk ll lr) with
        | nil => simp [leftSpine] at hls_L
        | cons u us => exact ⟨u, rfl⟩
      obtain ⟨hspl_bst, hspl_keys⟩ := spliceMin_isBST_and_keys hL1 hmL
      have hv_spl : ValidFrames b1 (spliceMin (.node lk ll lr)) (rightSpineFrames R1) := by
        refine validFrames_of_bst b1 _ R1 hspl_bst ?_ hR1 hgt
        intro u hu
        rw [← mem_keyFinset_iff, hspl_keys, Finset.mem_sdiff, mem_keyFinset_iff] at hu
        exact hlt u hu.1
      have hfold_lt : ∀ p ∈ popCascadePairs (.node lk ll lr), p.2 < b1 := by
        intro p hp
        exact hlt p.2 (mem_of_mem_leftSpine _ (List.mem_of_mem_tail (mem_adjacentPairs_snd hp)))
      have take_append_len : ∀ {α : Type} (xs ys : List α), (xs ++ ys).take xs.length = xs := by
        intro α xs ys
        induction xs with
        | nil => rfl
        | cons a xs ih => simp only [List.cons_append, List.length_cons, List.take_succ_cons, ih]
      have getElem?_append_len : ∀ {α : Type} (xs : List α) (a : α) (ys : List α),
          (xs ++ a :: ys)[xs.length]? = some a := by
        intro α xs a ys
        induction xs with
        | nil => rfl
        | cons b xs ih => simp only [List.cons_append, List.length_cons, List.getElem?_cons_succ, ih]
      by_cases hpar : (leftSpine (.node lk ll lr)).length % 2 = 1
      · rw [popCascade_node_odd hH_orig hpar]
        dsimp only [spineFoldTree, rightSpineFrames, FoldedOp.step]
        rw [hsub, hk_eq]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega : (leftSpine (.node lk ll lr)).length ≠ 0))]
        have htail_H : (leftSpine (.node b1 (.node lk ll lr) R1)).tail =
            (leftSpine (.node lk ll lr)).tail ++ [b1] := by
          change (leftSpine (.node lk ll lr) ++ [b1]).tail = _
          cases hls_L : leftSpine (.node lk ll lr) with
          | nil => simp [leftSpine] at hls_L
          | cons u us => rfl
        have heven_tail : (leftSpine (.node lk ll lr)).tail.length % 2 = 0 := by
          simp only [List.length_tail]; omega
        have hpairs_eq : adjacentPairs (leftSpine (.node b1 (.node lk ll lr) R1)).tail =
            popCascadePairs (.node lk ll lr) := by
          rw [htail_H, adjacentPairs_append_even _ [b1] heven_tail]
          simp [adjacentPairs, popCascadePairs]
        have hlen_pairs : (popCascadePairs (.node lk ll lr)).length =
            ((leftSpine (.node lk ll lr)).length - 1) / 2 := by
          simp [popCascadePairs, adjacentPairs_length]
        have htake : (adjacentPairs (leftSpine (.node b1 (.node lk ll lr) R1)).tail).take
            (((leftSpine (.node lk ll lr)).length - 1) / 2) =
            popCascadePairs (.node lk ll lr) := by
          rw [hpairs_eq, ← hlen_pairs, List.take_length]
        have hnot_even_k : (leftSpine (.node lk ll lr)).length ≠
            2 * (((leftSpine (.node lk ll lr)).length - 1) / 2) + 2 := by
          omega
        rw [htake, spliceMin_spineFoldGo,
            foldl_rotateRightEdge_spineFoldGo_lt _ hv_spl hfold_lt,
            ite_eq_right_of_eq_false _ _ (eq_false hnot_even_k)]
        rfl
      · have heven : (leftSpine (.node lk ll lr)).length % 2 = 0 := by omega
        rw [popCascade_node_even hH_orig heven]
        have hll_odd : (leftSpine ll).length % 2 = 1 := by
          simp only [leftSpine, List.length_append, List.length_singleton] at heven; omega
        have hll_ne : ll ≠ .nil := by
          intro h; subst h; simp [leftSpine] at hll_odd
        have hls_ll_ne : leftSpine ll ≠ [] := (leftSpine_eq_nil_iff ll).not.mpr hll_ne
        have hL_pop : popCascade (.node lk ll lr) = .node lk (popCascade ll) lr :=
          popCascade_node_odd hL1 hll_odd
        dsimp only [spineFoldTree, rightSpineFrames, FoldedOp.step]
        rw [hsub, hk_eq]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega : (leftSpine (.node lk ll lr)).length ≠ 0))]
        have htail_L : (leftSpine (.node lk ll lr)).tail = (leftSpine ll).tail ++ [lk] := by
          simp only [leftSpine]
          cases hls_ll : leftSpine ll with
          | nil => contradiction
          | cons a as => rfl
        have htail_H : (leftSpine (.node b1 (.node lk ll lr) R1)).tail =
            (leftSpine ll).tail ++ [lk, b1] := by
          simp only [leftSpine, List.append_assoc, List.singleton_append]
          cases hls_ll : leftSpine ll with
          | nil => contradiction
          | cons a as => rfl
        have htail_ll_even : (leftSpine ll).tail.length % 2 = 0 := by
          have : 1 ≤ (leftSpine ll).length := List.length_pos_of_ne_nil hls_ll_ne
          simp only [List.length_tail]; omega
        have hpairs_L : popCascadePairs (.node lk ll lr) = adjacentPairs (leftSpine ll).tail := by
          unfold popCascadePairs
          rw [htail_L, adjacentPairs_append_even _ [lk] htail_ll_even]
          simp [adjacentPairs]
        have hpairs_H : adjacentPairs (leftSpine (.node b1 (.node lk ll lr) R1)).tail =
            popCascadePairs (.node lk ll lr) ++ [(lk, b1)] := by
          rw [htail_H, adjacentPairs_append_even _ [lk, b1] htail_ll_even, ← hpairs_L]
          rfl
        have hlen_pairs : (popCascadePairs (.node lk ll lr)).length =
            ((leftSpine (.node lk ll lr)).length - 1) / 2 := by
          simp [popCascadePairs, adjacentPairs_length]
        have htake : (adjacentPairs (leftSpine (.node b1 (.node lk ll lr) R1)).tail).take
            (((leftSpine (.node lk ll lr)).length - 1) / 2) =
            popCascadePairs (.node lk ll lr) := by
          rw [hpairs_H, ← hlen_pairs, take_append_len]
        have heven_k : (leftSpine (.node lk ll lr)).length =
            2 * (((leftSpine (.node lk ll lr)).length - 1) / 2) + 2 := by
          have : 1 ≤ (leftSpine ll).length := List.length_pos_of_ne_nil hls_ll_ne
          simp only [leftSpine, List.length_append, List.length_singleton] at heven ⊢
          omega
        have hll_len : 2 * (((leftSpine (.node lk ll lr)).length - 1) / 2) + 1 =
            (leftSpine ll).length := by
          simp only [leftSpine, List.length_append, List.length_singleton] at heven_k ⊢
          omega
        have hget_lk : (leftSpine (.node b1 (.node lk ll lr) R1))[
            2 * (((leftSpine (.node lk ll lr)).length - 1) / 2) + 1]? = some lk := by
          have hls_all : leftSpine (.node b1 (.node lk ll lr) R1) =
              leftSpine ll ++ lk :: [b1] := by
            simp [leftSpine, List.append_assoc]
          rw [hls_all, hll_len]
          exact getElem?_append_len (leftSpine ll) lk [b1]
        rw [htake, spliceMin_spineFoldGo,
            foldl_rotateRightEdge_spineFoldGo_lt _ hv_spl hfold_lt,
            ite_eq_left_of_eq_true _ _ (eq_true heven_k), hget_lk]
        change (spineFoldGo b1 (popCascade (.node lk ll lr)) (rightSpineFrames R1), some lk) = _
        rw [hL_pop]
        rfl

/-! ### Unfolded Trajectory `unfoldedAt`, `popStepIdx`, and `tauEmpty` -/

noncomputable def unfoldedStep (H : BinaryTree ℕ) (op : FoldedOp) : BinaryTree ℕ :=
  open Classical in
  match op with
  | .push w => .node w .nil H
  | .pop _ => popCascade H
  | .shift =>
    match H with
    | .node b1 _ (.node b2 _ _) => rotateLeftEdge H b2 b1
    | _ => H
  | .upperRot u v =>
    if h : ∃ x y, x < y ∧ y ∈ H ∧
        FoldedOp.step (spineFoldTree H) (.upperRot u v) = spineFoldTree (rotateLeftEdge H y x) then
      rotateLeftEdge H h.choose_spec.choose h.choose
    else H

noncomputable def unfoldedAt {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ) : BinaryTree ℕ :=
  (proc.steps.take τ).foldl unfoldedStep .nil

theorem validFoldedOps_getElem {P : ℕ} {steps : List FoldedOp}
    (st₀ : BinaryTree ℕ × Option ℕ) (hval : ValidFoldedOps P st₀ steps)
    {τ : ℕ} (hτ : τ < steps.length) :
    (steps[τ]).Valid P ((steps.take τ).foldl FoldedOp.step st₀) := by
  induction steps generalizing st₀ τ with
  | nil => simp at hτ
  | cons op rest ih =>
    cases τ with
    | zero => exact hval.1
    | succ τ' =>
      have hτ' : τ' < rest.length := by simp at hτ; omega
      exact ih (op.step st₀) hval.2 hτ'

theorem minKey?_spineFoldTree {H : BinaryTree ℕ} (hH : H.IsBST) :
    (spineFoldTree H).1.minKey? = H.minKey? := by
  cases H with
  | nil => rfl
  | node b1 L1 R1 =>
    rw [minKey?_eq_head?_leftSpine, minKey?_eq_head?_leftSpine]
    simp only [spineFoldTree, rightSpineFrames]
    rw [leftSpine_spineFoldGo, leftSpine]
    cases leftSpine L1 <;> rfl

theorem unfoldedStep_spec {P : ℕ} {H : BinaryTree ℕ} (hH : H.IsBST)
    (hbnd : ∀ k ∈ H, 1 ≤ k ∧ k ≤ P) {op : FoldedOp}
    (hval : op.Valid P (spineFoldTree H)) :
    let H' := unfoldedStep H op
    H'.IsBST ∧ (∀ k ∈ H', 1 ≤ k ∧ k ≤ P) ∧
      op.step (spineFoldTree H) = spineFoldTree H' := by
  cases op with
  | push w =>
    rcases hval with ⟨hw1, hwP, hlt_fold, _, _⟩
    have hlt_H : ∀ k ∈ H, w < k := by
      intro k hk
      apply hlt_fold k
      rw [← mem_keyFinset_iff, keyFinset_spineFoldTree, mem_keyFinset_iff]
      exact hk
    have hbst' : (BinaryTree.node w .nil H).IsBST :=
      isBST_node_iff.mpr ⟨isBST_nil, hH, (fun _ h => by cases h), hlt_H⟩
    have hbnd' : ∀ k ∈ BinaryTree.node w .nil H, 1 ≤ k ∧ k ≤ P := by
      intro k hk
      rw [BinaryTree.mem_node_iff] at hk
      rcases hk with rfl | hk | hk
      · exact ⟨hw1, hwP⟩
      · cases hk
      · exact hbnd k hk
    exact ⟨hbst', hbnd', step_push_spineFoldTree H hH w⟩
  | shift =>
    have hval_orig := hval
    rcases hval with ⟨b, hb, _, hroot_ne⟩
    cases H with
    | nil => simp [spineFoldTree] at hb
    | node b1 L1 R1 =>
      simp only [spineFoldTree, rightSpineFrames, Option.some.injEq] at hb
      subst hb
      cases R1 with
      | nil =>
        simp [spineFoldTree, rightSpineFrames, spineFoldGo, rootKey?] at hroot_ne
      | node b2 L2 R2 =>
        obtain ⟨hbst', hkeys'⟩ :=
          rotateLeftEdge_isBST_and_keys hH b2 b1
        have hbnd' : ∀ k ∈ rotateLeftEdge (.node b1 L1 (.node b2 L2 R2)) b2 b1,
            1 ≤ k ∧ k ≤ P := by
          intro k hk
          rw [← mem_keyFinset_iff, hkeys', mem_keyFinset_iff] at hk
          exact hbnd k hk
        have hstep : FoldedOp.step (spineFoldTree (.node b1 L1 (.node b2 L2 R2))) .shift =
            spineFoldTree (rotateLeftEdge (.node b1 L1 (.node b2 L2 R2)) b2 b1) := by
          have hb1_not_mem : b1 ∉ leftSpine L1 := by
            rw [isBST_node_iff] at hH
            intro hm
            exact absurd (hH.2.2.1 b1 (mem_of_mem_leftSpine L1 hm)) (lt_irrefl b1)
          have hls : leftSpine (spineFoldGo b1 L1 ((b2, L2) :: rightSpineFrames R2)) =
              leftSpine L1 ++ b1 :: b2 :: rightSpine R2 := by
            change leftSpine (spineFoldGo b1 L1 (rightSpineFrames (.node b2 L2 R2))) = _
            rw [leftSpine_spineFoldGo, rightSpineFrames_map_fst]; rfl
          have h_rotL : rotateLeftEdge (.node b1 L1 (.node b2 L2 R2)) b2 b1 =
              .node b2 (.node b1 L1 L2) R2 := by
            conv_lhs => unfold rotateLeftEdge
            rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl b1)),
                ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl b1))]
            dsimp only
            rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
          rw [h_rotL]
          dsimp only [spineFoldTree, rightSpineFrames, FoldedOp.step]
          rw [hls, nextOnSpine_append_of_not_mem hb1_not_mem]
          rfl
        exact ⟨hbst', hbnd', hstep⟩
  | upperRot u v =>
    have hex := step_upperRot_spineFoldTree hH hval
    dsimp only [unfoldedStep]
    simp only [hex, ↓reduceDIte]
    have hspec := hex.choose_spec.choose_spec
    obtain ⟨hbst', hkeys'⟩ :=
      rotateLeftEdge_isBST_and_keys hH hex.choose_spec.choose hex.choose
    refine ⟨hbst', ?_, hspec.2.2⟩
    intro k hk
    rw [← mem_keyFinset_iff, hkeys', mem_keyFinset_iff] at hk
    exact hbnd k hk
  | pop s =>
    rcases hval with ⟨b, hne_fold, hmin_fold, _, _⟩
    have hne_H : H ≠ .nil := (spineFoldTree_eq_nil_iff H).not.mp hne_fold
    have hmin_H : H.minKey? = some s := (minKey?_spineFoldTree hH).symm.trans hmin_fold
    obtain ⟨hbst', hkeys'⟩ := popCascade_isBST_and_keys hH hmin_H
    dsimp only [unfoldedStep]
    refine ⟨hbst', ?_, step_pop_spineFoldTree hH hne_H s⟩
    intro k hk
    rw [← mem_keyFinset_iff, hkeys', Finset.mem_sdiff, mem_keyFinset_iff] at hk
    exact hbnd k hk.1

theorem unfoldedAt_succ {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ < proc.steps.length) :
    unfoldedAt proc (τ + 1) = unfoldedStep (unfoldedAt proc τ) proc.steps[τ] := by
  unfold unfoldedAt
  rw [List.take_add_one, List.getElem?_eq_getElem hτ, Option.toList_some, List.foldl_append]
  rfl

theorem stateAt_succ {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ < proc.steps.length) :
    proc.stateAt (τ + 1) = proc.steps[τ].step (proc.stateAt τ) := by
  unfold FoldedPopProcess.stateAt
  rw [List.take_add_one, List.getElem?_eq_getElem hτ, Option.toList_some, List.foldl_append]
  rfl

theorem unfoldedAt_inv {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ ≤ proc.steps.length) :
    (unfoldedAt proc τ).IsBST ∧
      (∀ k ∈ unfoldedAt proc τ, 1 ≤ k ∧ k ≤ P) ∧
      proc.stateAt τ = spineFoldTree (unfoldedAt proc τ) := by
  induction τ with
  | zero =>
    exact ⟨isBST_nil, (fun _ h => by cases h), rfl⟩
  | succ τ ih =>
    have hτ_lt : τ < proc.steps.length := Nat.lt_of_succ_le hτ
    obtain ⟨hbst, hbnd, hst⟩ := ih (le_of_lt hτ_lt)
    have hval := validFoldedOps_getElem (.nil, none) proc.hValid hτ_lt
    change proc.steps[τ].Valid P (proc.stateAt τ) at hval
    rw [hst] at hval
    obtain ⟨hbst', hbnd', hstep⟩ := unfoldedStep_spec hbst hbnd hval
    rw [unfoldedAt_succ proc hτ_lt, stateAt_succ proc hτ_lt, hst, hstep]
    exact ⟨hbst', hbnd', rfl⟩

theorem unfoldedAt_end_nil {P : ℕ} (proc : FoldedPopProcess P) :
    unfoldedAt proc proc.steps.length = .nil := by
  have hst := (unfoldedAt_inv proc (le_refl _)).2.2
  have hend : proc.stateAt proc.steps.length = (.nil, none) := by
    simp [FoldedPopProcess.stateAt, proc.hEndEmpty]
  rw [hend] at hst
  have h1 : (spineFoldTree (unfoldedAt proc proc.steps.length)).1 = .nil :=
    congrArg Prod.fst hst.symm
  exact (spineFoldTree_eq_nil_iff _).mp h1

theorem keyFinset_treeAt_eq {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ ≤ proc.steps.length) :
    keyFinset (proc.treeAt τ) = keyFinset (unfoldedAt proc τ) := by
  have hst := (unfoldedAt_inv proc hτ).2.2
  have h1 : proc.treeAt τ = (spineFoldTree (unfoldedAt proc τ)).1 :=
    congrArg Prod.fst hst
  rw [h1, keyFinset_spineFoldTree]

theorem unfoldedStep_keys {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ < proc.steps.length) :
    match proc.steps[τ] with
    | .push w => keyFinset (unfoldedAt proc (τ + 1)) = insert w (keyFinset (unfoldedAt proc τ))
    | .shift => keyFinset (unfoldedAt proc (τ + 1)) = keyFinset (unfoldedAt proc τ)
    | .upperRot _ _ => keyFinset (unfoldedAt proc (τ + 1)) = keyFinset (unfoldedAt proc τ)
    | .pop s => keyFinset (unfoldedAt proc (τ + 1)) = keyFinset (unfoldedAt proc τ) \ {s} := by
  obtain ⟨hbst, _, hst⟩ := unfoldedAt_inv proc (le_of_lt hτ)
  have hval := validFoldedOps_getElem (.nil, none) proc.hValid hτ
  change proc.steps[τ].Valid P (proc.stateAt τ) at hval
  rw [hst] at hval
  rw [unfoldedAt_succ proc hτ]
  cases hop : proc.steps[τ] with
  | push w =>
    simp [unfoldedStep, keyFinset]
  | shift =>
    rw [hop] at hval
    dsimp only [unfoldedStep]
    cases H : unfoldedAt proc τ with
    | nil => rfl
    | node b1 L1 R1 =>
      cases R1 with
      | nil => rfl
      | node b2 L2 R2 =>
        rw [H] at hbst
        exact (rotateLeftEdge_isBST_and_keys hbst b2 b1).2
  | upperRot u v =>
    rw [hop] at hval
    have hex := step_upperRot_spineFoldTree hbst hval
    dsimp only [unfoldedStep]
    simp only [hex, ↓reduceDIte]
    exact (rotateLeftEdge_isBST_and_keys hbst _ _).2
  | pop s =>
    rw [hop] at hval
    rcases hval with ⟨_, _, hmin_fold, _, _⟩
    have hmin_H : (unfoldedAt proc τ).minKey? = some s :=
      (minKey?_spineFoldTree hbst).symm.trans hmin_fold
    exact (popCascade_isBST_and_keys hbst hmin_H).2

/-! ### `popStepIdx` Uniqueness, Monotonicity, and `tauEmpty` Depletion -/

def popOpt : FoldedOp → Option ℕ
  | .pop s => some s
  | _ => none

theorem filterMap_lt_of_idx_lt {α β : Type} (f : α → Option β) (R : β → β → Prop)
    (xs : List α) (hpw : (xs.filterMap f).Pairwise R)
    {i j : ℕ} (hij : i < j) (hj : j < xs.length)
    (b₁ b₂ : β) (hi_eq : f xs[i] = some b₁) (hj_eq : f xs[j] = some b₂) :
    R b₁ b₂ := by
  induction xs generalizing i j with
  | nil => simp at hj
  | cons hd tl ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        have hj' : j' < tl.length := by simp at hj; omega
        simp only [List.getElem_cons_zero] at hi_eq
        simp only [List.getElem_cons_succ] at hj_eq
        simp only [List.filterMap_cons, hi_eq, List.pairwise_cons] at hpw
        exact hpw.1 b₂ (List.mem_filterMap.mpr ⟨tl[j'], List.getElem_mem hj', hj_eq⟩)
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        have hij' : i' < j' := by omega
        have hj' : j' < tl.length := by simp at hj; omega
        have hpw_tl : (tl.filterMap f).Pairwise R := by
          simp only [List.filterMap_cons] at hpw
          cases hhd : f hd with
          | none => simp only [hhd] at hpw; exact hpw
          | some _ => simp only [hhd] at hpw; exact (List.pairwise_cons.mp hpw).2
        exact ih hpw_tl hij' hj' hi_eq hj_eq

theorem pairwise_lt_range' (a n : ℕ) : (List.range' a n).Pairwise (· < ·) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    simp only [List.range'_succ, List.pairwise_cons, List.mem_range']
    exact ⟨fun b ⟨i, _, hbi⟩ => by omega, ih (a + 1)⟩

theorem popStepIdx_spec {P : ℕ} (proc : FoldedPopProcess P) {s : ℕ}
    (hs1 : 1 ≤ s) (hsP : s ≤ P) :
    proc.popStepIdx s < proc.steps.length ∧
      proc.steps[proc.popStepIdx s]'
        (by
          have hmem_r : s ∈ List.range' 1 P :=
            List.mem_range'.mpr ⟨s - 1, by omega, by omega⟩
          rw [← proc.hPopSeq, List.mem_filterMap] at hmem_r
          rcases hmem_r with ⟨op, hop_mem, hop_eq⟩
          have hop_pop : op = .pop s := by
            cases op <;> simp at hop_eq; subst hop_eq; rfl
          subst hop_pop
          exact List.findIdx_lt_length_of_exists ⟨.pop s, hop_mem, by simp⟩) = .pop s := by
  have hmem_r : s ∈ List.range' 1 P :=
    List.mem_range'.mpr ⟨s - 1, by omega, by omega⟩
  rw [← proc.hPopSeq, List.mem_filterMap] at hmem_r
  rcases hmem_r with ⟨op, hop_mem, hop_eq⟩
  have hop_pop : op = .pop s := by
    cases op <;> simp at hop_eq; subst hop_eq; rfl
  subst hop_pop
  have hlt : proc.popStepIdx s < proc.steps.length :=
    List.findIdx_lt_length_of_exists ⟨.pop s, hop_mem, by simp⟩
  refine ⟨hlt, ?_⟩
  have hlt' : proc.steps.findIdx (fun op => op == .pop s) < proc.steps.length := hlt
  have hget := List.findIdx_getElem (xs := proc.steps) (p := fun op => op == .pop s) (w := hlt')
  simp at hget
  exact hget

theorem eq_popStepIdx_of_getElem {P : ℕ} (proc : FoldedPopProcess P) {τ s : ℕ}
    (hτ : τ < proc.steps.length) (hop : proc.steps[τ] = .pop s) :
    1 ≤ s ∧ s ≤ P ∧ τ = proc.popStepIdx s := by
  have hs_mem : s ∈ List.range' 1 P := by
    rw [← proc.hPopSeq, List.mem_filterMap]
    exact ⟨proc.steps[τ], List.getElem_mem hτ, by rw [hop]⟩
  rw [List.mem_range'] at hs_mem
  rcases hs_mem with ⟨idx, hidx_lt, hidx_eq⟩
  have hs1 : 1 ≤ s := by omega
  have hsP : s ≤ P := by omega
  obtain ⟨hlt_pop, hget_pop⟩ := popStepIdx_spec proc hs1 hsP
  have hpw : (proc.steps.filterMap popOpt).Pairwise (· < ·) := by
    have heq : proc.steps.filterMap popOpt = List.range' 1 P := proc.hPopSeq
    rw [heq]
    exact pairwise_lt_range' 1 P
  refine ⟨hs1, hsP, ?_⟩
  rcases lt_trichotomy τ (proc.popStepIdx s) with hlt | heq | hgt
  · exfalso
    have := filterMap_lt_of_idx_lt popOpt (· < ·) proc.steps hpw hlt hlt_pop s s
      (by simp [popOpt, hop]) (by simp [popOpt, hget_pop])
    exact lt_irrefl s this
  · exact heq
  · exfalso
    have := filterMap_lt_of_idx_lt popOpt (· < ·) proc.steps hpw hgt hτ s s
      (by simp [popOpt, hget_pop]) (by simp [popOpt, hop])
    exact lt_irrefl s this

theorem popStepIdx_strictMono {P : ℕ} (proc : FoldedPopProcess P) {s₁ s₂ : ℕ}
    (h1 : 1 ≤ s₁) (h12 : s₁ < s₂) (h2 : s₂ ≤ P) :
    proc.popStepIdx s₁ < proc.popStepIdx s₂ := by
  obtain ⟨hlt1, hget1⟩ := popStepIdx_spec proc h1 (le_trans (le_of_lt h12) h2)
  obtain ⟨hlt2, hget2⟩ := popStepIdx_spec proc (by omega) h2
  have hpw : (proc.steps.filterMap popOpt).Pairwise (· < ·) := by
    have heq : proc.steps.filterMap popOpt = List.range' 1 P := proc.hPopSeq
    rw [heq]
    exact pairwise_lt_range' 1 P
  rcases lt_trichotomy (proc.popStepIdx s₁) (proc.popStepIdx s₂) with hlt | heq | hgt
  · exact hlt
  · exfalso
    have : proc.steps[proc.popStepIdx s₁] = proc.steps[proc.popStepIdx s₂] := by
      simp [heq]
    rw [hget1, hget2] at this
    injection this with hs_eq
    omega
  · exfalso
    have := filterMap_lt_of_idx_lt popOpt (· < ·) proc.steps hpw hgt hlt1 s₂ s₁
      (by simp [popOpt, hget2]) (by simp [popOpt, hget1])
    omega

theorem popStepIdx_mono {P : ℕ} (proc : FoldedPopProcess P) {s₁ s₂ : ℕ}
    (h1 : 1 ≤ s₁) (h12 : s₁ ≤ s₂) (h2 : s₂ ≤ P) :
    proc.popStepIdx s₁ ≤ proc.popStepIdx s₂ := by
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (popStepIdx_strictMono proc h1 hlt h2)

/-- If `w ∈ unfoldedAt proc τ` and no `.pop w` occurs at or after `τ`, `w` survives to the end
(contradicting `unfoldedAt_end_nil`). -/
theorem mem_persists_without_pop {P : ℕ} (proc : FoldedPopProcess P) {w τ₁ τ₂ : ℕ}
    (h12 : τ₁ ≤ τ₂) (h2 : τ₂ ≤ proc.steps.length)
    (hw : w ∈ keyFinset (unfoldedAt proc τ₁))
    (hnopop : ∀ (t : ℕ) (_ : τ₁ ≤ t) (ht2 : t < τ₂),
      proc.steps[t]'(Nat.lt_of_lt_of_le ht2 h2) ≠ .pop w) :
    w ∈ keyFinset (unfoldedAt proc τ₂) := by
  induction τ₂ with
  | zero =>
    have : τ₁ = 0 := by omega
    subst this; exact hw
  | succ τ₂ ih =>
    rcases eq_or_lt_of_le h12 with rfl | hlt
    · exact hw
    · have h12' : τ₁ ≤ τ₂ := by omega
      have h2' : τ₂ < proc.steps.length := Nat.lt_of_succ_le h2
      have hw_prev := ih h12' (le_of_lt h2') (fun t ht1 ht2 => hnopop t ht1 (by omega))
      have hkeys := unfoldedStep_keys proc h2'
      cases hop : proc.steps[τ₂] with
      | push w' =>
        rw [hop] at hkeys; rw [hkeys]; exact Finset.mem_insert_of_mem hw_prev
      | shift =>
        rw [hop] at hkeys; rw [hkeys]; exact hw_prev
      | upperRot u v =>
        rw [hop] at hkeys; rw [hkeys]; exact hw_prev
      | pop s =>
        rw [hop] at hkeys; rw [hkeys]
        have hne_op : proc.steps[τ₂] ≠ .pop w := hnopop τ₂ h12' (Nat.lt_succ_self _)
        have hsw : w ≠ s := by
          intro heq; subst heq; exact hne_op hop
        exact Finset.mem_sdiff.mpr ⟨hw_prev, Finset.notMem_singleton.mpr hsw⟩

theorem not_mem_after_popStepIdx {P : ℕ} (proc : FoldedPopProcess P) {w τ : ℕ}
    (hw1 : 1 ≤ w) (hwP : w ≤ P)
    (hgt : proc.popStepIdx w < τ) (hτ : τ ≤ proc.steps.length) :
    w ∉ keyFinset (unfoldedAt proc τ) := by
  obtain ⟨hlt_w, hget_w⟩ := popStepIdx_spec proc hw1 hwP
  induction τ with
  | zero => omega
  | succ τ ih =>
    have hτ_lt : τ < proc.steps.length := Nat.lt_of_succ_le hτ
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hgt) with heq | hgt'
    · -- `τ = proc.popStepIdx w`
      subst heq
      have hkeys := unfoldedStep_keys proc hlt_w
      rw [hget_w] at hkeys
      rw [hkeys]
      simp
    · -- `proc.popStepIdx w < τ`
      have hnot_prev := ih hgt' (le_of_lt hτ_lt)
      have hkeys := unfoldedStep_keys proc hτ_lt
      cases hop : proc.steps[τ] with
      | push w' =>
        rw [hop] at hkeys; rw [hkeys]
        intro hmem
        rcases Finset.mem_insert.mp hmem with rfl | hmem
        · -- If `w` was pushed at `τ > popStepIdx w`, `w` persists to `steps.length`!
          have hmem_next : w ∈ keyFinset (unfoldedAt proc (τ + 1)) := by
            rw [hkeys]; exact Finset.mem_insert_self w _
          have hmem_end := mem_persists_without_pop proc (Nat.succ_le_of_lt hτ_lt) (le_refl _)
            hmem_next (by
              intro t ht1 ht2 hpop
              have ⟨_, _, ht_eq⟩ := eq_popStepIdx_of_getElem proc ht2 hpop
              omega)
          rw [unfoldedAt_end_nil] at hmem_end
          simp [keyFinset] at hmem_end
        · exact hnot_prev hmem
      | shift =>
        rw [hop] at hkeys; rw [hkeys]; exact hnot_prev
      | upperRot _ _ =>
        rw [hop] at hkeys; rw [hkeys]; exact hnot_prev
      | pop s =>
        rw [hop] at hkeys; rw [hkeys]
        intro hmem
        exact hnot_prev (Finset.mem_sdiff.mp hmem).1

theorem finset_sup_id_mem {s : Finset ℕ} (hs : s.Nonempty) : s.sup id ∈ s := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | @insert a s' _ ih =>
    rw [Finset.sup_insert]
    rcases s'.eq_empty_or_nonempty with rfl | hne
    · simp
    · have hmem := ih hne
      change max a (s'.sup id) ∈ insert a s'
      rcases le_total a (s'.sup id) with hle | hle
      · rw [max_eq_right hle]; exact Finset.mem_insert_of_mem hmem
      · rw [max_eq_left hle]; exact Finset.mem_insert_self a s'

theorem tauEmpty_bounds_and_disjoint {P : ℕ} (proc : FoldedPopProcess P)
    {Sp : IntervalBlock} (hlo1 : 1 ≤ Sp.lo) (hlohi : Sp.lo ≤ Sp.hi) (hhiP : Sp.hi ≤ P) :
    1 ≤ tauEmpty proc Sp ∧ tauEmpty proc Sp ≤ proc.steps.length ∧
      proc.popStepIdx Sp.lo < tauEmpty proc Sp ∧
      ∀ w ∈ Sp.toFinset, w ∉ unfoldedAt proc (tauEmpty proc Sp) := by
  obtain ⟨hlt_lo, hget_lo⟩ := popStepIdx_spec proc hlo1 (le_trans hlohi hhiP)
  let tStart := proc.popStepIdx Sp.lo
  have hval_lo := validFoldedOps_getElem (.nil, none) proc.hValid hlt_lo
  change proc.steps[tStart].Valid P (proc.stateAt tStart) at hval_lo
  rw [hget_lo] at hval_lo
  rcases hval_lo with ⟨_, _, hmin_lo, _, _⟩
  have hlo_mem_tree : Sp.lo ∈ keyFinset (proc.treeAt tStart) :=
    (mem_keyFinset_iff _ _).mpr (minKey?_mem hmin_lo)
  have hlo_mem_Sp : Sp.lo ∈ Sp.toFinset :=
    Finset.mem_Icc.mpr ⟨le_rfl, hlohi⟩
  let S_init := keyFinset (proc.treeAt tStart) ∩ Sp.toFinset
  have hlo_S : Sp.lo ∈ S_init := Finset.mem_inter.mpr ⟨hlo_mem_tree, hlo_mem_Sp⟩
  have hsMax_mem : sMax proc Sp ∈ S_init := finset_sup_id_mem ⟨Sp.lo, hlo_S⟩
  have hsMax_Sp : sMax proc Sp ∈ Sp.toFinset := (Finset.mem_inter.mp hsMax_mem).2
  have hsMax_lo : Sp.lo ≤ sMax proc Sp := (Finset.mem_Icc.mp hsMax_Sp).1
  have hsMax_hi : sMax proc Sp ≤ Sp.hi := (Finset.mem_Icc.mp hsMax_Sp).2
  have hsMax_unfold : sMax proc Sp ∈ keyFinset (unfoldedAt proc tStart) := by
    rw [← keyFinset_treeAt_eq proc (le_of_lt hlt_lo)]
    exact (Finset.mem_inter.mp hsMax_mem).1
  obtain ⟨hlt_smax, _⟩ := popStepIdx_spec proc (le_trans hlo1 hsMax_lo) (le_trans hsMax_hi hhiP)
  have hmono_smax : tStart ≤ proc.popStepIdx (sMax proc Sp) :=
    popStepIdx_mono proc hlo1 hsMax_lo (le_trans hsMax_hi hhiP)
  have htau_pos : 1 ≤ tauEmpty proc Sp := by unfold tauEmpty; omega
  have htau_le : tauEmpty proc Sp ≤ proc.steps.length := by unfold tauEmpty; omega
  have htau_gt : tStart < tauEmpty proc Sp := by unfold tauEmpty; omega
  refine ⟨htau_pos, htau_le, htau_gt, ?_⟩
  have hsMax_active : ∀ t, tStart ≤ t → t ≤ proc.popStepIdx (sMax proc Sp) →
      sMax proc Sp ∈ keyFinset (unfoldedAt proc t) := by
    intro t ht1 ht2
    exact mem_persists_without_pop proc ht1 (le_of_lt (Nat.lt_of_le_of_lt ht2 hlt_smax))
      hsMax_unfold (fun u _ hu2 hpop => by
        have hu_lt : u < proc.steps.length := lt_trans hu2 (Nat.lt_of_le_of_lt ht2 hlt_smax)
        have ⟨_, _, hu_eq⟩ := eq_popStepIdx_of_getElem proc hu_lt hpop
        omega)
  intro w hw_Sp hw_mem
  rw [← mem_keyFinset_iff] at hw_mem
  have hw_lo : Sp.lo ≤ w := (Finset.mem_Icc.mp hw_Sp).1
  have hw_hi : w ≤ Sp.hi := (Finset.mem_Icc.mp hw_Sp).2
  rcases le_or_gt w (sMax proc Sp) with hw_le | hw_gt
  · have hpop_le : proc.popStepIdx w ≤ proc.popStepIdx (sMax proc Sp) :=
      popStepIdx_mono proc (le_trans hlo1 hw_lo) hw_le (le_trans hsMax_hi hhiP)
    exact not_mem_after_popStepIdx proc (le_trans hlo1 hw_lo) (le_trans hw_hi hhiP)
      (by unfold tauEmpty; omega) htau_le hw_mem
  · have hw_not_start : w ∉ keyFinset (unfoldedAt proc tStart) := by
      intro hw_in
      rw [← keyFinset_treeAt_eq proc (le_of_lt hlt_lo)] at hw_in
      have hw_S : w ∈ S_init := Finset.mem_inter.mpr ⟨hw_in, hw_Sp⟩
      have : w ≤ sMax proc Sp := Finset.le_sup (f := id) hw_S
      omega
    have hw_never : ∀ t, tStart ≤ t → t ≤ tauEmpty proc Sp →
        w ∉ keyFinset (unfoldedAt proc t) := by
      intro t ht1 ht2
      induction t with
      | zero =>
        have h0 : 0 = tStart := by omega
        rw [h0]; exact hw_not_start
      | succ t ih =>
        rcases eq_or_lt_of_le ht1 with heq | hlt_t
        · rw [← heq]; exact hw_not_start
        · have ht1' : tStart ≤ t := by omega
          have ht_le_smax : t ≤ proc.popStepIdx (sMax proc Sp) := by
            unfold tauEmpty at ht2; omega
          have ht_lt_len : t < proc.steps.length := Nat.lt_of_le_of_lt ht_le_smax hlt_smax
          have hnot_t := ih ht1' (by omega)
          have hkeys := unfoldedStep_keys proc ht_lt_len
          cases hop : proc.steps[t] with
          | push w' =>
            rw [hop] at hkeys; rw [hkeys]
            intro hmem
            rcases Finset.mem_insert.mp hmem with rfl | hmem
            · have hsmax_t : sMax proc Sp ∈ unfoldedAt proc t :=
                (mem_keyFinset_iff _ _).mp (hsMax_active t ht1' ht_le_smax)
              have hval_t := validFoldedOps_getElem (.nil, none) proc.hValid ht_lt_len
              change proc.steps[t].Valid P (proc.stateAt t) at hval_t
              rw [hop, (unfoldedAt_inv proc (le_of_lt ht_lt_len)).2.2] at hval_t
              have hsmax_fold : sMax proc Sp ∈ (spineFoldTree (unfoldedAt proc t)).1 := by
                rw [← mem_keyFinset_iff, keyFinset_spineFoldTree, mem_keyFinset_iff]
                exact hsmax_t
              have : w < sMax proc Sp := hval_t.2.2.1 (sMax proc Sp) hsmax_fold
              omega
            · exact hnot_t hmem
          | shift =>
            rw [hop] at hkeys; rw [hkeys]; exact hnot_t
          | upperRot _ _ =>
            rw [hop] at hkeys; rw [hkeys]; exact hnot_t
          | pop s =>
            rw [hop] at hkeys; rw [hkeys]
            intro hmem
            exact hnot_t (Finset.mem_sdiff.mp hmem).1
    exact hw_never (tauEmpty proc Sp) (le_of_lt htau_gt) le_rfl hw_mem

/-! ### Partition Chain & `partSepScale` Lemmas -/

theorem consecutiveBlocks_append {xs ys : List IntervalBlock}
    (hxs : ConsecutiveBlocks xs) (hys : ConsecutiveBlocks ys)
    (hlink : ∀ a ∈ xs.getLast?, ∀ b ∈ ys.head?, a.hi + 1 = b.lo) :
    ConsecutiveBlocks (xs ++ ys) := by
  induction xs with
  | nil => exact hys
  | cons x rest ih =>
    cases rest with
    | nil =>
      cases ys with
      | nil => trivial
      | cons y yrest =>
        exact ⟨hlink x rfl y rfl, hys⟩
    | cons x2 rest2 =>
      exact ⟨hxs.1, ih hxs.2 (fun a ha b hb => hlink a ha b hb)⟩

theorem splitIntervalBySize_props (X : IntervalBlock) (S : ℕ) (hlo : X.lo ≤ X.hi) :
    let ys := splitIntervalBySize X S
    ys ≠ [] ∧
      (∀ Y ∈ ys, X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi) ∧
      ConsecutiveBlocks ys ∧
      (ys.head?).map IntervalBlock.lo = some X.lo ∧
      (ys.getLast?).map IntervalBlock.hi = some X.hi := by
  dsimp only [splitIntervalBySize]
  by_cases hcond : S = 0 ∨ X.size < 2 * S
  · simp only [hcond, ↓reduceIte]
    simp [ConsecutiveBlocks, hlo]
  · simp only [hcond, ↓reduceIte]
    have hS_ne : S ≠ 0 := fun h => hcond (Or.inl h)
    have hsz_ge : 2 * S ≤ X.size := not_lt.mp (fun h => hcond (Or.inr h))
    have hS_pos : 1 ≤ S := by omega
    have hsz_eq : X.size = X.hi - X.lo + 1 := by simp [IntervalBlock.size, hlo]
    have hK_ge2 : 2 ≤ X.size / S := (Nat.le_div_iff_mul_le hS_pos).mpr (by omega)
    have hKS_le : (X.size / S) * S ≤ X.hi - X.lo + 1 := by
      have := Nat.div_mul_le_self X.size S
      omega
    let f : ℕ → IntervalBlock := fun idx =>
      if idx + 1 < X.size / S then ⟨X.lo + idx * S, X.lo + (idx + 1) * S - 1⟩
      else ⟨X.lo + idx * S, X.hi⟩
    change (List.range (X.size / S)).map f ≠ [] ∧
      (∀ Y ∈ (List.range (X.size / S)).map f, X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi) ∧
      ConsecutiveBlocks ((List.range (X.size / S)).map f) ∧
      (((List.range (X.size / S)).map f).head?).map IntervalBlock.lo = some X.lo ∧
      (((List.range (X.size / S)).map f).getLast?).map IntervalBlock.hi = some X.hi
    have hlen : ((List.range (X.size / S)).map f).length = X.size / S := by simp
    have hne : (List.range (X.size / S)).map f ≠ [] :=
      List.ne_nil_of_length_pos (by omega)
    have hbnds : ∀ Y ∈ (List.range (X.size / S)).map f,
        X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi := by
      intro Y hY
      rw [List.mem_map] at hY
      rcases hY with ⟨idx, hidx_mem, rfl⟩
      have hidx_lt : idx < X.size / S := List.mem_range.mp hidx_mem
      dsimp only [f]
      split_ifs with hlt
      · dsimp only
        have h1 : (idx + 1) * S < (X.size / S) * S := (Nat.mul_lt_mul_right hS_pos).mpr hlt
        have h2 : idx * S + S = (idx + 1) * S := (Nat.succ_mul idx S).symm
        exact ⟨by omega, by omega, by omega⟩
      · dsimp only
        have hidx_eq : idx + 1 = X.size / S := by omega
        have h1 : idx * S + S = (X.size / S) * S := by rw [← hidx_eq, Nat.succ_mul]
        exact ⟨by omega, by omega, by omega⟩
    have hconsec : ConsecutiveBlocks ((List.range (X.size / S)).map f) := by
      rw [List.range_eq_range']
      suffices ∀ a n, a + n ≤ X.size / S → ConsecutiveBlocks ((List.range' a n).map f) from
        this 0 (X.size / S) (by omega)
      intro a n
      induction n generalizing a with
      | zero => intro _; simp [ConsecutiveBlocks]
      | succ n ih =>
        cases n with
        | zero => intro _; simp [ConsecutiveBlocks]
        | succ n' =>
          intro han
          simp only [List.range'_succ, List.map_cons, ConsecutiveBlocks]
          refine ⟨?_, ih (a + 1) (by omega)⟩
          have ha_lt : a + 1 < X.size / S := by omega
          have hpos_mul : 1 ≤ (a + 1) * S := by
            have := Nat.mul_le_mul_left (a + 1) hS_pos
            omega
          dsimp only [f]
          simp only [ha_lt, ↓reduceIte]
          split_ifs <;> dsimp only <;> omega
    have hhead : (((List.range (X.size / S)).map f).head?).map IntervalBlock.lo = some X.lo := by
      rw [List.head?_eq_getElem?]
      have h0 : 0 < ((List.range (X.size / S)).map f).length := by omega
      rw [List.getElem?_eq_getElem h0]
      simp [f, show 0 + 1 < X.size / S by omega]
    have hlast : (((List.range (X.size / S)).map f).getLast?).map IntervalBlock.hi = some X.hi := by
      rw [List.getLast?_eq_getElem?]
      have hlast_lt : ((List.range (X.size / S)).map f).length - 1 <
          ((List.range (X.size / S)).map f).length := by omega
      rw [List.getElem?_eq_getElem hlast_lt]
      simp [hlen, f, show ¬ (X.size / S - 1 + 1 < X.size / S) by omega]
    exact ⟨hne, hbnds, hconsec, hhead, hlast⟩

theorem flatMap_splitInterval_partition {P : ℕ} (hP : 1 ≤ P)
    {parts : List IntervalBlock} (hpart : IsContiguousBlockPartition P parts) (S : ℕ) :
    IsContiguousBlockPartition P (parts.flatMap (fun X => splitIntervalBySize X S)) ∧
      (∀ Y ∈ parts.flatMap (fun X => splitIntervalBySize X S),
        ∃ X ∈ parts, X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi) := by
  rcases hpart with ⟨hbnds, hconsec, hhl⟩
  have hparent : ∀ Y ∈ parts.flatMap (fun X => splitIntervalBySize X S),
      ∃ X ∈ parts, X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi := by
    intro Y hY
    rw [List.mem_flatMap] at hY
    rcases hY with ⟨X, hX, hYX⟩
    have hX_bnds := hbnds X hX
    have hp := splitIntervalBySize_props X S hX_bnds.2.1
    exact ⟨X, hX, hp.2.1 Y hYX⟩
  have hbnds_new : ∀ Y ∈ parts.flatMap (fun X => splitIntervalBySize X S),
      1 ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ P := by
    intro Y hY
    obtain ⟨X, hX, h1, h2, h3⟩ := hparent Y hY
    have hX_bnds := hbnds X hX
    exact ⟨by omega, h2, by omega⟩
  have hparts_ne : parts ≠ [] := by
    intro heq
    rw [heq] at hhl
    simp at hhl
    omega
  have haux : ∀ (xs : List IntervalBlock),
      xs ≠ [] →
      (∀ X ∈ xs, X.lo ≤ X.hi) →
      ConsecutiveBlocks xs →
      let out := xs.flatMap (fun X => splitIntervalBySize X S)
      out ≠ [] ∧
        ConsecutiveBlocks out ∧
        (out.head?).map IntervalBlock.lo = (xs.head?).map IntervalBlock.lo ∧
        (out.getLast?).map IntervalBlock.hi = (xs.getLast?).map IntervalBlock.hi := by
    intro xs
    induction xs with
    | nil => intro h; contradiction
    | cons X rest ih =>
      intro _ hlo_xs hcs
      have hpX := splitIntervalBySize_props X S (hlo_xs X List.mem_cons_self)
      cases rest with
      | nil =>
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.head?_cons, List.getLast?_singleton, Option.map_some]
        exact ⟨hpX.1, hpX.2.2.1, hpX.2.2.2.1, hpX.2.2.2.2⟩
      | cons X2 rest2 =>
        obtain ⟨hout_rest_ne, hcs_rest, hhead_rest, hlast_rest⟩ :=
          ih (by simp) (fun C hC => hlo_xs C (List.mem_cons_of_mem X hC)) hcs.2
        simp only [List.flatMap_cons]
        have hout_ne : splitIntervalBySize X S ++
            (X2 :: rest2).flatMap (fun C => splitIntervalBySize C S) ≠ [] :=
          List.append_ne_nil_of_left_ne_nil hpX.1 _
        have hcs_all : ConsecutiveBlocks (splitIntervalBySize X S ++
            (X2 :: rest2).flatMap (fun C => splitIntervalBySize C S)) := by
          refine consecutiveBlocks_append hpX.2.2.1 hcs_rest ?_
          intro a ha b hb
          have ha_hi : a.hi = X.hi := by
            have := hpX.2.2.2.2
            rw [ha] at this; exact Option.some.inj this
          have hb_lo : b.lo = X2.lo := by
            have := hhead_rest
            rw [hb] at this; simp at this; exact this
          rw [ha_hi, hb_lo]
          exact hcs.1
        have hhead_all : ((splitIntervalBySize X S ++
            (X2 :: rest2).flatMap (fun C => splitIntervalBySize C S)).head?).map IntervalBlock.lo =
            some X.lo := by
          rw [List.head?_append_of_ne_nil _ hpX.1]
          exact hpX.2.2.2.1
        have hlast_all : ((splitIntervalBySize X S ++
            (X2 :: rest2).flatMap (fun C => splitIntervalBySize C S)).getLast?).map IntervalBlock.hi =
            ((X2 :: rest2).getLast?).map IntervalBlock.hi := by
          rw [List.getLast?_append_of_ne_nil _ hout_rest_ne]
          exact hlast_rest
        refine ⟨hout_ne, hcs_all, hhead_all, ?_⟩
        simpa using hlast_all
  obtain ⟨hout_ne, hcs_new, hhead_new, hlast_new⟩ :=
    haux parts hparts_ne (fun X hX => (hbnds X hX).2.1) hconsec
  refine ⟨⟨hbnds_new, hcs_new, ?_⟩, fun Y hY => by
    obtain ⟨X, hX, h1, _, h3⟩ := hparent Y hY
    exact ⟨X, hX, h1, h3⟩⟩
  cases hhd_p : parts.head? with
  | none => exact absurd (List.head?_eq_none_iff.mp hhd_p) hparts_ne
  | some firstP =>
    cases hls_p : parts.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hls_p) hparts_ne
    | some lastP =>
      rw [hhd_p, hls_p] at hhl
      cases hhd_o : (parts.flatMap (fun X => splitIntervalBySize X S)).head? with
      | none => exact absurd (List.head?_eq_none_iff.mp hhd_o) hout_ne
      | some firstO =>
        cases hls_o : (parts.flatMap (fun X => splitIntervalBySize X S)).getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hls_o) hout_ne
        | some lastO =>
          rw [hhd_o, hhd_p] at hhead_new
          rw [hls_o, hls_p] at hlast_new
          simp only [Option.map_some, Option.some.injEq] at hhead_new hlast_new
          exact ⟨hhead_new.trans hhl.1, hlast_new.trans hhl.2⟩

theorem validScaleTree_isNestedPartitionChain {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) :
    IsNestedPartitionChain P (scaleTreePartitionChain T P M) := by
  have hP : 1 ≤ P := hValid.1
  have hlevel : ∀ k : ℕ, IsContiguousBlockPartition P (scaleTreePartitionLevel T P k) ∧
      (∀ Y ∈ scaleTreePartitionLevel T P (k + 1),
        ∃ X ∈ scaleTreePartitionLevel T P k, X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi) := by
    intro k
    induction k with
    | zero =>
      have h0 : scaleTreePartitionLevel T P 0 = [⟨1, P⟩] := by
        simp [scaleTreePartitionLevel, show P ≠ 0 by omega]
      have hpart0 : IsContiguousBlockPartition P (scaleTreePartitionLevel T P 0) := by
        rw [h0]
        refine ⟨?_, trivial, rfl, rfl⟩
        intro C hC; simp at hC; subst hC; exact ⟨le_rfl, hP, le_rfl⟩
      exact ⟨hpart0, (flatMap_splitInterval_partition hP hpart0 (scaleS T P 1)).2⟩
    | succ k ih =>
      have hpart_succ := (flatMap_splitInterval_partition hP ih.1 (scaleS T P (k + 1))).1
      exact ⟨hpart_succ, (flatMap_splitInterval_partition hP hpart_succ (scaleS T P (k + 2))).2⟩
  refine ⟨hP, ?_, ?_, ?_⟩
  · simp [scaleTreePartitionChain, scaleTreePartitionLevel, show P ≠ 0 by omega]
  · intro ℓ
    exact (hlevel ℓ.val).1
  · intro ℓ Y hY
    exact (hlevel ℓ.val).2 Y hY

/-! ## 4. Partition Lookup, `b3ExitPost` Characterization, `psiPost` Potential, and Lemma 5.5 -/

theorem consecutiveBlocks_pairwise :
    ∀ {xs : List IntervalBlock},
      (∀ C ∈ xs, C.lo ≤ C.hi) → ConsecutiveBlocks xs →
      xs.Pairwise (fun A B => A.hi < B.lo)
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | A :: B :: rest, hlo, hcs => by
    have ih := consecutiveBlocks_pairwise
      (fun C hC => hlo C (List.mem_cons_of_mem A hC)) hcs.2
    refine List.Pairwise.cons (fun C hC => ?_) ih
    rcases List.mem_cons.mp hC with rfl | hCr
    · have := hcs.1; omega
    · have hBC : B.hi < C.lo := (List.pairwise_cons.mp ih).1 C hCr
      have hBlo : B.lo ≤ B.hi := hlo B (List.mem_cons_of_mem A List.mem_cons_self)
      have := hcs.1
      omega

theorem consecutiveBlocks_cover :
    ∀ {xs : List IntervalBlock} {lo₀ hi₀ u : ℕ},
      xs ≠ [] →
      (∀ C ∈ xs, C.lo ≤ C.hi) →
      ConsecutiveBlocks xs →
      (xs.head?).map IntervalBlock.lo = some lo₀ →
      (xs.getLast?).map IntervalBlock.hi = some hi₀ →
      lo₀ ≤ u → u ≤ hi₀ →
      ∃ B ∈ xs, B.lo ≤ u ∧ u ≤ B.hi
  | [], _, _, _, hne, _, _, _, _, _, _ => absurd rfl hne
  | [A], lo₀, hi₀, u, _, _, _, hhd, hls, h1, h2 => by
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
    simp only [List.getLast?_singleton, Option.map_some, Option.some.injEq] at hls
    subst hhd; subst hls
    exact ⟨A, List.mem_cons_self, h1, h2⟩
  | A :: B :: rest, lo₀, hi₀, u, _, hlo, hcs, hhd, hls, h1, h2 => by
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
    subst hhd
    rcases le_or_gt u A.hi with hu | hu
    · exact ⟨A, List.mem_cons_self, h1, hu⟩
    · have hls' : ((B :: rest).getLast?).map IntervalBlock.hi = some hi₀ := by
        simpa using hls
      obtain ⟨C, hC, hClo, hChi⟩ := consecutiveBlocks_cover (List.cons_ne_nil _ _)
        (fun D hD => hlo D (List.mem_cons_of_mem A hD)) hcs.2 rfl hls'
        (by have := hcs.1; omega) h2
      exact ⟨C, List.mem_cons_of_mem A hC, hClo, hChi⟩

theorem blockAt_mem_and_unique {N : ℕ} {parts : List IntervalBlock}
    (_hN : 1 ≤ N) (hPart : IsContiguousBlockPartition N parts) :
    (∀ u ∈ Finset.Icc 1 N, blockAt parts u ∈ parts ∧
      (blockAt parts u).lo ≤ u ∧ u ≤ (blockAt parts u).hi) ∧
    (∀ B ∈ parts, ∀ u, B.lo ≤ u → u ≤ B.hi → blockAt parts u = B) := by
  have hpw := consecutiveBlocks_pairwise (fun C hC => (hPart.1 C hC).2.1) hPart.2.1
  have huniq : ∀ B₁ ∈ parts, ∀ B₂ ∈ parts, ∀ u,
      B₁.lo ≤ u → u ≤ B₁.hi → B₂.lo ≤ u → u ≤ B₂.hi → B₁ = B₂ := by
    have aux : ∀ (xs : List IntervalBlock), xs.Pairwise (fun A B => A.hi < B.lo) →
        ∀ B₁ ∈ xs, ∀ B₂ ∈ xs, ∀ u, B₁.lo ≤ u → u ≤ B₁.hi → B₂.lo ≤ u → u ≤ B₂.hi → B₁ = B₂ := by
      intro xs hpw_xs
      induction xs with
      | nil => intro _ h; cases h
      | cons head tail iht =>
        rw [List.pairwise_cons] at hpw_xs
        intro B₁ h1 B₂ h2 u l1 r1 l2 r2
        rcases List.mem_cons.mp h1 with rfl | h1t <;>
          rcases List.mem_cons.mp h2 with rfl | h2t
        · rfl
        · have := hpw_xs.1 B₂ h2t; omega
        · have := hpw_xs.1 B₁ h1t; omega
        · exact iht hpw_xs.2 B₁ h1t B₂ h2t u l1 r1 l2 r2
    exact aux parts hpw
  have hfind_of_mem : ∀ B ∈ parts, ∀ u, B.lo ≤ u → u ≤ B.hi → blockAt parts u = B := by
    intro B hB u hlo hhi
    unfold blockAt
    cases hf : parts.find? (fun C => decide (C.lo ≤ u ∧ u ≤ C.hi)) with
    | none =>
      exfalso
      have := List.find?_eq_none.mp hf B hB
      simp [hlo, hhi] at this
    | some C =>
      simp only [Option.getD_some]
      have hC_mem := List.mem_of_find?_eq_some hf
      have hC_pred := List.find?_some hf
      simp only [decide_eq_true_eq] at hC_pred
      exact huniq C hC_mem B hB u hC_pred.1 hC_pred.2 hlo hhi
  refine ⟨?_, hfind_of_mem⟩
  intro u hu
  rw [Finset.mem_Icc] at hu
  have hne : parts ≠ [] := by
    intro he; subst he
    have := hPart.2.2
    simp at this; omega
  cases hh : parts.head? with
  | none => exact absurd (List.head?_eq_none_iff.mp hh) hne
  | some first =>
    cases hl : parts.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
    | some last =>
      have hhl := hPart.2.2
      rw [hh, hl] at hhl
      obtain ⟨B, hB, hlo, hhi⟩ := consecutiveBlocks_cover hne
        (fun C hC => (hPart.1 C hC).2.1) hPart.2.1
        (by simp [hh, hhl.1]) (by simp [hl, hhl.2]) hu.1 hu.2
      rw [hfind_of_mem B hB u hlo hhi]
      exact ⟨hB, hlo, hhi⟩

theorem findIdx?_eq_some_spec {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {idx : ℕ}, xs.findIdx? p = some idx →
      ∃ hlt : idx < xs.length, p (xs[idx]'hlt) = true
  | [], _, h => by simp at h
  | x :: xs, idx, h => by
    simp only [List.findIdx?_cons] at h
    cases hpx : p x
    · simp only [hpx, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      obtain ⟨hk_lt, hpk⟩ := findIdx?_eq_some_spec p hk
      exact ⟨Nat.succ_lt_succ hk_lt, by simpa using hpk⟩
    · simp only [hpx, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨Nat.zero_lt_succ _, hpx⟩

theorem chain_blockAt_coarse {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hk : k₁ ≤ k₂) {u : ℕ} (hu : u ∈ Finset.Icc 1 P) :
    (blockAt (chain k₁) u).lo ≤ (blockAt (chain k₂) u).lo ∧
    (blockAt (chain k₂) u).hi ≤ (blockAt (chain k₁) u).hi := by
  rcases hChain with ⟨hP, _, hPart, hNest⟩
  obtain ⟨d, hd⟩ : ∃ d, k₂.val = k₁.val + d := ⟨k₂.val - k₁.val, by omega⟩
  induction d generalizing k₂ with
  | zero =>
    have hk_eq : k₁ = k₂ := Fin.ext (by omega)
    subst hk_eq; exact ⟨le_rfl, le_rfl⟩
  | succ d ih =>
    have hk_lt : k₁.val + d < M := by omega
    let km : Fin M := ⟨k₁.val + d, hk_lt⟩
    have hk₂_eq : k₂ = km.succ := Fin.ext (by simp [km]; omega)
    subst hk₂_eq
    obtain ⟨hB_mem, hB_lo, hB_hi⟩ := (blockAt_mem_and_unique hP (hPart km.succ)).1 u hu
    obtain ⟨X, hX_mem, hX_lo, hX_hi⟩ := hNest km _ hB_mem
    have hX_eq : blockAt (chain km.castSucc) u = X :=
      (blockAt_mem_and_unique hP (hPart km.castSucc)).2 X hX_mem u
        (le_trans hX_lo hB_lo) (le_trans hB_hi hX_hi)
    obtain ⟨ih1, ih2⟩ := ih (k₂ := km.castSucc) (Fin.mk_le_mk.mpr (by simp [km])) rfl
    rw [hX_eq] at ih1 ih2
    exact ⟨le_trans ih1 hX_lo, le_trans hX_hi ih2⟩

theorem partSepScale_eq_iff {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) {u v : ℕ}
    (hu : u ∈ Finset.Icc 1 P) (hv : v ∈ Finset.Icc 1 P) (ℓ : Fin M) :
    partSepScale P chain u v = ℓ.val + 1 ↔
      blockAt (chain ℓ.castSucc) u = blockAt (chain ℓ.castSucc) v ∧
      blockAt (chain ℓ.succ) u ≠ blockAt (chain ℓ.succ) v := by
  have hP := hChain.1
  have hu' := Finset.mem_Icc.mp hu
  have hv' := Finset.mem_Icc.mp hv
  have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
  have same_down : ∀ {k₁ k₂ : Fin (M + 1)}, k₁ ≤ k₂ →
      blockAt (chain k₂) u = blockAt (chain k₂) v →
      blockAt (chain k₁) u = blockAt (chain k₁) v := by
    intro k₁ k₂ hk hsame
    obtain ⟨l2, r2⟩ := chain_blockAt_coarse hChain hk hv
    obtain ⟨_, hu_lo, hu_hi⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 k₂)).1 u hu
    rw [hsame] at hu_lo hu_hi
    obtain ⟨hB1_mem, _, _⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 k₁)).1 v hv
    exact (blockAt_mem_and_unique hP (hChain.2.2.1 k₁)).2 _ hB1_mem u
      (le_trans l2 hu_lo) (le_trans hu_hi r2)
  have h0_same : blockAt (chain 0) u = blockAt (chain 0) v := by
    have h0 := hChain.2.1
    have hPart0 := hChain.2.2.1 0
    have hmem0 : ⟨1, P⟩ ∈ chain 0 := by rw [h0]; simp
    rw [(blockAt_mem_and_unique hP hPart0).2 ⟨1, P⟩ hmem0 u hu'.1 hu'.2,
        (blockAt_mem_and_unique hP hPart0).2 ⟨1, P⟩ hmem0 v hv'.1 hv'.2]
  have find_finRange : ∀ (p : Fin M → Bool),
      ((List.finRange M).find? p = none ↔ ∀ i : Fin M, p i = false) ∧
      (∀ i : Fin M, (List.finRange M).find? p = some i ↔
        p i = true ∧ ∀ j : Fin M, j < i → p j = false) := by
    intro p
    have aux : ∀ (xs : List (Fin M)), xs.Pairwise (· < ·) →
        (∀ i : Fin M, xs.find? p = some i →
          p i = true ∧ ∀ j ∈ xs, j < i → p j = false) := by
      intro xs
      induction xs with
      | nil => intro _ i h; simp at h
      | cons head tail iht =>
        intro hpw_xs i hf
        rw [List.pairwise_cons] at hpw_xs
        simp only [List.find?_cons] at hf
        cases hp : p head
        · simp [hp] at hf
          obtain ⟨hpi, hprev⟩ := iht hpw_xs.2 i hf
          refine ⟨hpi, fun j hj hjlt => ?_⟩
          rcases List.mem_cons.mp hj with rfl | hjt
          · exact hp
          · exact hprev j hjt hjlt
        · simp [hp] at hf; subst hf
          refine ⟨hp, fun j hj hjlt => ?_⟩
          rcases List.mem_cons.mp hj with rfl | hjt
          · exact absurd hjlt (lt_irrefl _)
          · exact absurd (lt_trans hjlt (hpw_xs.1 j hjt)) (lt_irrefl _)
    refine ⟨List.find?_eq_none.trans (by simp [List.mem_finRange]), fun i => ⟨fun hf => ?_, ?_⟩⟩
    · obtain ⟨hpi, hprev⟩ := aux (List.finRange M) (List.pairwise_lt_finRange M) i hf
      exact ⟨hpi, fun j hj => hprev j (List.mem_finRange j) hj⟩
    · rintro ⟨hp_i, hlt_i⟩
      cases hf : (List.finRange M).find? p with
      | none =>
        have := List.find?_eq_none.mp hf i (List.mem_finRange i)
        simp [hp_i] at this
      | some i' =>
        obtain ⟨hp_i', hprev'⟩ := aux (List.finRange M) (List.pairwise_lt_finRange M) i' hf
        rcases lt_trichotomy i' i with h1 | rfl | h2
        · rw [hlt_i i' h1] at hp_i'; contradiction
        · rfl
        · rw [hprev' i (List.mem_finRange i) h2] at hp_i; contradiction
  set pred : Fin M → Bool := fun j => decide (blockAt (chain j.succ) u ≠ blockAt (chain j.succ) v)
  have hsep_none : (List.finRange M).find? pred = none → partSepScale P chain u v = M + 1 := by
    intro hf
    unfold partSepScale
    simp only [hcond, ↓reduceIte]
    change (match (List.finRange M).find? pred with | some j => j.val + 1 | none => M + 1) = M + 1
    rw [hf]
  have hsep_some : ∀ j, (List.finRange M).find? pred = some j →
      partSepScale P chain u v = j.val + 1 := by
    intro j hf
    unfold partSepScale
    simp only [hcond, ↓reduceIte]
    change (match (List.finRange M).find? pred with | some j => j.val + 1 | none => M + 1) = j.val + 1
    rw [hf]
  obtain ⟨hnone, hsome⟩ := find_finRange pred
  cases hf : (List.finRange M).find? pred with
  | none =>
    rw [hsep_none hf]
    constructor
    · intro heq; have := ℓ.isLt; omega
    · rintro ⟨_, h_fine⟩
      have hall := hnone.mp hf ℓ
      simp only [pred, decide_eq_false_iff_not, not_not] at hall
      exact absurd hall h_fine
  | some ℓ' =>
    rw [hsep_some ℓ' hf]
    constructor
    · intro heq
      have hℓ_eq : ℓ' = ℓ := Fin.ext (by omega)
      subst ℓ'
      obtain ⟨hp_ℓ, hprev⟩ := (hsome ℓ).mp hf
      simp only [pred, decide_eq_true_eq] at hp_ℓ
      refine ⟨?_, hp_ℓ⟩
      rcases Nat.eq_zero_or_pos ℓ.val with hℓ0 | hℓ_pos
      · have hc0 : ℓ.castSucc = 0 := Fin.ext (by simp [hℓ0])
        rw [hc0]; exact h0_same
      · let j : Fin M := ⟨ℓ.val - 1, by omega⟩
        have hj_lt : j < ℓ := Fin.mk_lt_mk.mpr (by omega)
        have hp_j := hprev j hj_lt
        simp only [pred, decide_eq_false_iff_not, not_not] at hp_j
        have hcast_eq : ℓ.castSucc = j.succ := Fin.ext (by change ℓ.val = (ℓ.val - 1) + 1; omega)
        rw [hcast_eq]; exact hp_j
    · rintro ⟨h_coarse, h_fine⟩
      have h_iff : (List.finRange M).find? pred = some ℓ := by
        rw [hsome ℓ]
        refine ⟨by simp [pred, h_fine], fun j hj => ?_⟩
        simp only [pred, decide_eq_false_iff_not, not_not]
        exact same_down (Fin.succ_le_castSucc_iff.mpr hj) h_coarse
      rw [hf] at h_iff
      injection h_iff with h_eq
      rw [h_eq]

theorem childSubblocks_props {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    (ℓ : Fin M) {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc) :
    let subs := childSubblocks (chain ℓ.succ) X
    (1 ≤ X.lo ∧ X.lo ≤ X.hi ∧ X.hi ≤ P) ∧
    (∀ c ∈ Finset.Icc 1 subs.length,
      let Sc := subblock1 subs c
      Sc ∈ subs ∧ Sc ∈ chain ℓ.succ ∧
      1 ≤ Sc.lo ∧ X.lo ≤ Sc.lo ∧ Sc.lo ≤ Sc.hi ∧ Sc.hi ≤ X.hi ∧ Sc.hi ≤ P ∧
      (∀ w ∈ Sc.toFinset, subblockIndex1 subs w = c ∧
        blockAt (chain ℓ.succ) w = Sc ∧ blockAt (chain ℓ.castSucc) w = X)) ∧
    (∀ c₁ c₂ : ℕ, 1 ≤ c₁ → c₁ < c₂ → c₂ ≤ subs.length →
      (subblock1 subs c₁).hi < (subblock1 subs c₂).lo) ∧
    (∀ w ∈ X.toFinset,
      subblockIndex1 subs w ∈ Finset.Icc 1 subs.length ∧
      subblock1 subs (subblockIndex1 subs w) = blockAt (chain ℓ.succ) w ∧
      w ∈ (subblock1 subs (subblockIndex1 subs w)).toFinset) := by
  dsimp only
  have hP := hChain.1
  have hPartX := hChain.2.2.1 ℓ.castSucc
  have hPartY := hChain.2.2.1 ℓ.succ
  obtain ⟨hX1, hXle, hXP⟩ := hPartX.1 X hX
  set subs := childSubblocks (chain ℓ.succ) X
  have hpw_fine := consecutiveBlocks_pairwise (fun Y hY => (hPartY.1 Y hY).2.1) hPartY.2.1
  have hpw : subs.Pairwise (fun A B => A.hi < B.lo) := hpw_fine.filter _
  have hsub1_eq : ∀ c (_ : 1 ≤ c) (hclen : c ≤ subs.length),
      subblock1 subs c = subs[c - 1]'(by omega) := by
    intro c hc1 hclen
    unfold subblock1
    have hc0 : ¬ c = 0 := by omega
    simp [hc0, List.getElem?_eq_getElem (show c - 1 < subs.length by omega)]
  have hlt_idx : ∀ c₁ c₂ : ℕ, 1 ≤ c₁ → c₁ < c₂ → c₂ ≤ subs.length →
      (subblock1 subs c₁).hi < (subblock1 subs c₂).lo := by
    intro c₁ c₂ hc1 h12 hc2
    rw [hsub1_eq c₁ hc1 (by omega), hsub1_eq c₂ (by omega) hc2]
    exact List.pairwise_iff_getElem.mp hpw (c₁ - 1) (c₂ - 1) (by omega) (by omega) (by omega)
  have hfindIdx_of_mem : ∀ c, 1 ≤ c → c ≤ subs.length → ∀ w,
      (subblock1 subs c).lo ≤ w → w ≤ (subblock1 subs c).hi →
      subblockIndex1 subs w = c := by
    intro c hc1 hclen w hlo hhi
    unfold subblockIndex1
    have hex : ∃ Y ∈ subs, decide (Y.lo ≤ w ∧ w ≤ Y.hi) = true := by
      refine ⟨subblock1 subs c, ?_, by simp [hlo, hhi]⟩
      rw [hsub1_eq c hc1 hclen]; exact List.getElem_mem _
    cases hf : subs.findIdx? (fun S => decide (S.lo ≤ w ∧ w ≤ S.hi)) with
    | none =>
      exfalso
      rcases hex with ⟨Y, hY, hpY⟩
      have := (List.findIdx?_eq_none_iff.mp hf) Y hY
      simp [hpY] at this
    | some idx =>
      dsimp only
      obtain ⟨hidx_lt, hp_idx⟩ := findIdx?_eq_some_spec _ hf
      simp only [decide_eq_true_eq] at hp_idx
      have hidx1 : 1 ≤ idx + 1 := by omega
      have hidx_len : idx + 1 ≤ subs.length := by omega
      have hsub_idx : subblock1 subs (idx + 1) = subs[idx] := by
        simpa using hsub1_eq (idx + 1) hidx1 hidx_len
      rw [← hsub_idx] at hp_idx
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hlt_idx (idx + 1) c hidx1 hlt hclen; omega
      · have := hlt_idx c (idx + 1) hc1 hgt hidx_len; omega
  refine ⟨⟨hX1, hXle, hXP⟩, ?_, hlt_idx, ?_⟩
  · intro c hc
    rw [Finset.mem_Icc] at hc
    have hSc_mem : subblock1 subs c ∈ subs := by
      rw [hsub1_eq c hc.1 hc.2]; exact List.getElem_mem _
    have hSc_filt := List.mem_filter.mp hSc_mem
    have hSc_chain : subblock1 subs c ∈ chain ℓ.succ := hSc_filt.1
    have hSc_X : X.lo ≤ (subblock1 subs c).lo ∧ (subblock1 subs c).hi ≤ X.hi := by
      simpa using hSc_filt.2
    obtain ⟨h1, h2, h3⟩ := hPartY.1 _ hSc_chain
    refine ⟨hSc_mem, hSc_chain, h1, hSc_X.1, h2, hSc_X.2, h3, ?_⟩
    intro w hw
    rw [IntervalBlock.toFinset, Finset.mem_Icc] at hw
    refine ⟨hfindIdx_of_mem c hc.1 hc.2 w hw.1 hw.2, ?_, ?_⟩
    · exact (blockAt_mem_and_unique hP hPartY).2 _ hSc_chain w hw.1 hw.2
    · exact (blockAt_mem_and_unique hP hPartX).2 X hX w (by omega) (by omega)
  · intro w hw
    rw [IntervalBlock.toFinset, Finset.mem_Icc] at hw
    have hw_Icc : w ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    obtain ⟨hY_mem, hY_lo, hY_hi⟩ := (blockAt_mem_and_unique hP hPartY).1 w hw_Icc
    obtain ⟨X', hX'_mem, hX'_lo, hX'_hi⟩ := hChain.2.2.2 ℓ _ hY_mem
    have hX'_eq : X' = X := by
      have e1 := (blockAt_mem_and_unique hP hPartX).2 X' hX'_mem w (by omega) (by omega)
      have e2 := (blockAt_mem_and_unique hP hPartX).2 X hX w hw.1 hw.2
      exact e1.symm.trans e2
    subst hX'_eq
    have hY_subs : blockAt (chain ℓ.succ) w ∈ subs :=
      List.mem_filter.mpr ⟨hY_mem, by simp [hX'_lo, hX'_hi]⟩
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hY_subs
    have hc1 : 1 ≤ idx + 1 := by omega
    have hclen : idx + 1 ≤ subs.length := by omega
    have hsub_eq : subblock1 subs (idx + 1) = blockAt (chain ℓ.succ) w := by
      rw [hsub1_eq (idx + 1) hc1 hclen]
      simpa using hidx_eq
    have hc_eq : subblockIndex1 subs w = idx + 1 := by
      apply hfindIdx_of_mem (idx + 1) hc1 hclen w
      · rw [hsub_eq]; exact hY_lo
      · rw [hsub_eq]; exact hY_hi
    rw [hc_eq]
    exact ⟨Finset.mem_Icc.mpr ⟨hc1, hclen⟩, hsub_eq,
      by rw [hsub_eq]; exact Finset.mem_Icc.mpr ⟨hY_lo, hY_hi⟩⟩

/-! ### `rInt` Characterization on `leftSpine (unfoldedAt proc τ)` -/

theorem mem_rInt_iff {P : ℕ} (proc : FoldedPopProcess P) (e : InternalPopRot) :
    e ∈ proc.rInt ↔
      ∃ (hτ : e.stepIdx < proc.steps.length),
        e ∈ foldedPopRotsAt e.stepIdx (proc.stateAt e.stepIdx) (proc.steps[e.stepIdx]'hτ) := by
  have collect_iff : ∀ (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (ops : List FoldedOp),
      e ∈ collectFoldedPopRots idx st ops ↔
        ∃ (d : ℕ) (hd : d < ops.length),
          idx + d = e.stepIdx ∧
          e ∈ foldedPopRotsAt (idx + d) ((ops.take d).foldl FoldedOp.step st) (ops[d]'hd) := by
    intro idx st ops
    induction ops generalizing idx st with
    | nil => simp [collectFoldedPopRots]
    | cons op rest ih =>
      simp only [collectFoldedPopRots, List.mem_append, ih]
      constructor
      · rintro (h0 | ⟨d, hd, hstep, hmem⟩)
        · refine ⟨0, Nat.zero_lt_succ _, ?_, by simpa using h0⟩
          cases op with
          | pop s =>
            rcases st with ⟨tree, none | b⟩
            · simp [foldedPopRotsAt] at h0
            · simp only [foldedPopRotsAt, List.mem_filterMap, List.mem_range] at h0
              rcases h0 with ⟨i, _, hmatch⟩
              split at hmatch <;> simp at hmatch
              rcases hmatch with rfl
              dsimp only; omega
          | _ => simp [foldedPopRotsAt] at h0
        · refine ⟨d + 1, Nat.succ_lt_succ hd, by omega, ?_⟩
          simpa [List.take_succ_cons, List.foldl_cons, Nat.add_right_comm, Nat.add_assoc] using hmem
      · rintro ⟨d, hd, hstep, hmem⟩
        cases d with
        | zero => left; simpa using hmem
        | succ d' =>
          right
          refine ⟨d', Nat.lt_of_succ_lt_succ hd, by omega, ?_⟩
          simpa [List.take_succ_cons, List.foldl_cons, Nat.add_right_comm, Nat.add_assoc] using hmem
  unfold FoldedPopProcess.rInt
  rw [List.mem_toFinset, collect_iff]
  constructor
  · rintro ⟨d, hd, h0d, hmem⟩
    have hd_eq : d = e.stepIdx := by omega
    subst hd_eq
    exact ⟨hd, by simpa [FoldedPopProcess.stateAt] using hmem⟩
  · rintro ⟨hτ, hmem⟩
    exact ⟨e.stepIdx, hτ, by omega, by simpa [FoldedPopProcess.stateAt] using hmem⟩

theorem rInt_step_pop_spine {P : ℕ} (proc : FoldedPopProcess P) {τ s : ℕ}
    (hτ : τ < proc.steps.length) (hop : proc.steps[τ] = .pop s) :
    let H := unfoldedAt proc τ
    (∀ e ∈ proc.rInt, e.stepIdx = τ →
      ∃ (hj : 1 ≤ e.j) (hlen : 2 * e.j + 1 < (leftSpine H).length),
        e.s = s ∧
        (leftSpine H)[0]'(by omega) = s ∧
        e.x = (leftSpine H)[2 * e.j - 1]'(by omega) ∧
        e.y = (leftSpine H)[2 * e.j]'(by omega) ∧
        e.z = (leftSpine H)[2 * e.j + 1]'hlen ∧
        1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P) ∧
    (∀ e₁ ∈ proc.rInt, ∀ e₂ ∈ proc.rInt,
      e₁.stepIdx = τ → e₂.stepIdx = τ →
      (e₁.j = e₂.j → e₁ = e₂) ∧ (e₁.j < e₂.j → e₁.z ≤ e₂.x)) := by
  dsimp only
  obtain ⟨hbst, hbnd, hst⟩ := unfoldedAt_inv proc (le_of_lt hτ)
  have hval := validFoldedOps_getElem (.nil, none) proc.hValid hτ
  change proc.steps[τ].Valid P (proc.stateAt τ) at hval
  rw [hop, hst] at hval
  rcases hval with ⟨b, hne_fold, hmin_fold, hb_some, _⟩
  have hne_H : unfoldedAt proc τ ≠ .nil := (spineFoldTree_eq_nil_iff _).not.mp hne_fold
  have hmin_H : (unfoldedAt proc τ).minKey? = some s :=
    (minKey?_spineFoldTree hbst).symm.trans hmin_fold
  have hsub_eq : takeThrough (leftSpine (proc.stateAt τ).1) b = leftSpine (unfoldedAt proc τ) := by
    rw [hst]
    cases hH : unfoldedAt proc τ with
    | nil => exact absurd hH hne_H
    | node b1 L1 R1 =>
      rw [hH] at hb_some hbst
      simp only [spineFoldTree, rightSpineFrames, Option.some.injEq] at hb_some
      subst hb_some
      rw [isBST_node_iff] at hbst
      have hb1_not : b1 ∉ leftSpine L1 := fun hm =>
        absurd (hbst.2.2.1 b1 (mem_of_mem_leftSpine L1 hm)) (lt_irrefl b1)
      dsimp only [spineFoldTree, rightSpineFrames]
      rw [leftSpine_spineFoldGo, rightSpineFrames_map_fst, takeThrough_append_of_not_mem hb1_not]
      rfl
  have hpw_ls : (leftSpine (unfoldedAt proc τ)).Pairwise (· < ·) := leftSpine_sorted hbst
  have hls_lt : ∀ i₁ i₂ (h1 : i₁ < (leftSpine (unfoldedAt proc τ)).length)
      (h2 : i₂ < (leftSpine (unfoldedAt proc τ)).length),
      i₁ < i₂ → (leftSpine (unfoldedAt proc τ))[i₁]'h1 < (leftSpine (unfoldedAt proc τ))[i₂]'h2 :=
    fun i₁ i₂ h1 h2 hij => List.pairwise_iff_getElem.mp hpw_ls i₁ i₂ h1 h2 hij
  have hcore : ∀ e ∈ proc.rInt, e.stepIdx = τ →
      ∃ (hj : 1 ≤ e.j) (hlen : 2 * e.j + 1 < (leftSpine (unfoldedAt proc τ)).length),
        e.s = s ∧
        e.h = ((leftSpine (unfoldedAt proc τ)).length - 1 - 1) / 2 ∧
        (leftSpine (unfoldedAt proc τ))[0]'(by omega) = s ∧
        e.x = (leftSpine (unfoldedAt proc τ))[2 * e.j - 1]'(by omega) ∧
        e.y = (leftSpine (unfoldedAt proc τ))[2 * e.j]'(by omega) ∧
        e.z = (leftSpine (unfoldedAt proc τ))[2 * e.j + 1]'hlen := by
    intro e he he_τ
    obtain ⟨hτ_e, hmem⟩ := (mem_rInt_iff proc e).mp he
    have hmem' : e ∈ foldedPopRotsAt τ (proc.stateAt τ) (.pop s) := by
      have hop' : proc.steps[e.stepIdx]'hτ_e = .pop s := by simpa [he_τ] using hop
      rw [hop'] at hmem
      simpa [he_τ] using hmem
    have hb2 : (proc.stateAt τ).2 = some b := by rw [hst]; exact hb_some
    simp only [foldedPopRotsAt, hb2, hsub_eq, List.mem_filterMap, List.mem_range] at hmem'
    rcases hmem' with ⟨idx, hidx_lt, hmatch⟩
    have hj_len : 2 * (idx + 1) + 1 < (leftSpine (unfoldedAt proc τ)).length := by omega
    rw [List.getElem?_eq_getElem (show 2 * (idx + 1) - 1 < (leftSpine (unfoldedAt proc τ)).length by omega),
        List.getElem?_eq_getElem (show 2 * (idx + 1) < (leftSpine (unfoldedAt proc τ)).length by omega),
        List.getElem?_eq_getElem hj_len] at hmatch
    simp only [Option.some.injEq] at hmatch
    rw [← hmatch]
    dsimp only
    refine ⟨by omega, hj_len, rfl, rfl, ?_, rfl, rfl, rfl⟩
    rw [minKey?_eq_head?_leftSpine, List.head?_eq_getElem?,
        List.getElem?_eq_getElem (by omega)] at hmin_H
    exact Option.some.inj hmin_H
  refine ⟨fun e he he_τ => ?_, fun e₁ he₁ e₂ he₂ hτ₁ hτ₂ => ?_⟩
  · obtain ⟨hj, hlen, hs_eq, _, h0_eq, hx_eq, hy_eq, hz_eq⟩ := hcore e he he_τ
    have hs_lt_x : e.s < e.x := by
      rw [hs_eq, ← h0_eq, hx_eq]; exact hls_lt 0 (2 * e.j - 1) (by omega) (by omega) (by omega)
    have hx_lt_y : e.x < e.y := by
      rw [hx_eq, hy_eq]; exact hls_lt (2 * e.j - 1) (2 * e.j) (by omega) (by omega) (by omega)
    have hy_lt_z : e.y < e.z := by
      rw [hy_eq, hz_eq]; exact hls_lt (2 * e.j) (2 * e.j + 1) (by omega) hlen (by omega)
    have hs_mem : e.s ∈ unfoldedAt proc τ := by
      rw [hs_eq, ← h0_eq]; exact mem_of_mem_leftSpine _ (List.getElem_mem _)
    have hz_mem : e.z ∈ unfoldedAt proc τ := by
      rw [hz_eq]; exact mem_of_mem_leftSpine _ (List.getElem_mem _)
    exact ⟨hj, hlen, hs_eq, h0_eq, hx_eq, hy_eq, hz_eq,
      (hbnd e.s hs_mem).1, hs_lt_x, hx_lt_y, hy_lt_z, (hbnd e.z hz_mem).2⟩
  · obtain ⟨hj1, hlen1, hs1, hh1, _, hx1, hy1, hz1⟩ := hcore e₁ he₁ hτ₁
    obtain ⟨hj2, hlen2, hs2, hh2, _, hx2, hy2, hz2⟩ := hcore e₂ he₂ hτ₂
    refine ⟨fun hjeq => ?_, fun hjlt => ?_⟩
    · cases e₁; cases e₂
      dsimp only at hτ₁ hτ₂ hs1 hs2 hh1 hh2 hx1 hx2 hy1 hy2 hz1 hz2 hjeq
      subst hτ₁; subst hτ₂; subst hjeq
      simp_all
    · rw [hz1, hx2]
      rcases eq_or_lt_of_le (show 2 * e₁.j + 1 ≤ 2 * e₂.j - 1 by omega) with hidx_eq | hidx_lt
      · simp [hidx_eq]
      · exact le_of_lt (hls_lt (2 * e₁.j + 1) (2 * e₂.j - 1) hlen1 (by omega) hidx_lt)

/-! ### `postQSet` and `psiPost` Potential -/

noncomputable def postQSet {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p τ : ℕ) :
    Finset ℕ :=
  open Classical in
  let subs := childSubblocks (chain ℓ.succ) X
  let Sp := subblock1 subs p
  if tauEmpty proc Sp ≤ τ then
    (Finset.Icc (p + 1) subs.length).filter (fun q =>
      let Sq := subblock1 subs q
      ∃ a ∈ Sq.toFinset, ∃ w ∈ Sp.toFinset,
        w ∈ subtreeAtKey (unfoldedAt proc τ) a)
  else ∅

noncomputable def psiPost {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (τ : ℕ) : ℕ :=
  ∑ ℓ : Fin M,
    ∑ X ∈ (chain ℓ.castSucc).toFinset,
      ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
        (postQSet P proc chain ℓ X p τ).card

theorem postQSet_zero {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p : ℕ) :
    postQSet P proc chain ℓ X p 0 = ∅ := by
  classical
  unfold postQSet
  dsimp only
  split_ifs with h
  · rw [Finset.filter_eq_empty_iff]
    intro q _
    rintro ⟨a, _, w, _, hw⟩
    change w ∈ subtreeAtKey .nil a at hw
    simp [subtreeAtKey] at hw
  · rfl

theorem psiPost_zero {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) :
    psiPost P proc chain 0 = 0 := by
  unfold psiPost
  simp [postQSet_zero]

theorem postQSet_succ_empty_of_not_le {M P : ℕ} (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (ℓ : Fin M) {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1))
    {τ : ℕ} (hnot : ¬ (tauEmpty proc (subblock1 (childSubblocks (chain ℓ.succ) X) p) ≤ τ)) :
    postQSet P proc chain ℓ X p (τ + 1) = ∅ := by
  classical
  set subs := childSubblocks (chain ℓ.succ) X
  set Sp := subblock1 subs p
  rw [Finset.mem_Icc] at hp
  have hp_Icc : p ∈ Finset.Icc 1 subs.length := Finset.mem_Icc.mpr ⟨hp.1, by omega⟩
  obtain ⟨_, hsub_c, _, _⟩ := childSubblocks_props hChain ℓ hX
  obtain ⟨_, _, h1, _, h2, _, h3, _⟩ := hsub_c p hp_Icc
  obtain ⟨_, _, _, hdisj⟩ := tauEmpty_bounds_and_disjoint proc h1 h2 h3
  unfold postQSet
  dsimp only
  change (if tauEmpty proc Sp ≤ τ + 1 then _ else ∅) = ∅
  split_ifs with hle
  · have hτ_eq : τ + 1 = tauEmpty proc Sp := by omega
    rw [hτ_eq, Finset.filter_eq_empty_iff]
    intro q _
    rintro ⟨a, _, w, hw_Sp, hw_sub⟩
    exact hdisj w hw_Sp (mem_of_mem_subtreeAtKey hw_sub)
  · rfl

theorem mem_postQSet_iff {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p τ q : ℕ) :
    q ∈ postQSet P proc chain ℓ X p τ ↔
      let subs := childSubblocks (chain ℓ.succ) X
      let Sp := subblock1 subs p
      let Sq := subblock1 subs q
      tauEmpty proc Sp ≤ τ ∧
      q ∈ Finset.Icc (p + 1) subs.length ∧
      ∃ a ∈ Sq.toFinset, ∃ w ∈ Sp.toFinset,
        w ∈ subtreeAtKey (unfoldedAt proc τ) a := by
  classical
  unfold postQSet
  dsimp only
  split_ifs with h
  · simp [h]
  · simp [h]

theorem mem_b3ExitPost_iff {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (e : InternalPopRot) :
    e ∈ b3ExitPost P proc chain ↔
      e ∈ proc.rInt ∧
      ∃ ℓ : Fin M,
        partSepScale P chain e.s e.x = ℓ.val + 1 ∧
        partSepScale P chain e.x e.y = ℓ.val + 1 ∧
        (blockAt (chain ℓ.succ) e.y).hi < e.z ∧
        tauEmpty proc (blockAt (chain ℓ.succ) e.s) ≤ e.stepIdx := by
  unfold b3ExitPost b3Exit
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨he_rInt, hb3⟩, hpost⟩
    split_ifs at hb3 with h12
    · rcases hb3 with ⟨hs12, hhi⟩
      have h2M : partSepScale P chain e.x e.y ≤ M := h12.2
      simp only [h2M, ↓reduceDIte] at hpost
      let ℓ : Fin M := ⟨partSepScale P chain e.x e.y - 1, by omega⟩
      have hval_eq : partSepScale P chain e.x e.y = ℓ.val + 1 := by dsimp only [ℓ]; omega
      have hsucc_eq : (⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le h12.2⟩ : Fin (M + 1)) =
          ℓ.succ := Fin.ext (by dsimp only; exact hval_eq)
      rw [hsucc_eq] at hhi hpost
      exact ⟨he_rInt, ℓ, hs12.trans hval_eq, hval_eq, hhi, hpost⟩
  · rintro ⟨he_rInt, ℓ, hs1, hs2, hhi, hpost⟩
    have h12 : 1 ≤ partSepScale P chain e.x e.y ∧ partSepScale P chain e.x e.y ≤ M := by
      have := ℓ.isLt; omega
    have h2M : partSepScale P chain e.x e.y ≤ M := h12.2
    have hsucc_eq : (⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le h12.2⟩ : Fin (M + 1)) =
        ℓ.succ := Fin.ext (by dsimp only; exact hs2)
    refine ⟨⟨he_rInt, ?_⟩, ?_⟩
    · simp only [h12, and_self, ↓reduceDIte]
      exact ⟨hs1.trans hs2.symm, by rw [hsucc_eq]; exact hhi⟩
    · simp only [h2M, ↓reduceDIte]
      rw [hsucc_eq]; exact hpost

theorem sum_ite_eq_le {α : Type} [DecidableEq α] (s : Finset α) (a₀ : α) (c : ℕ) :
    (∑ a ∈ s, if a = a₀ then c else 0) ≤ c := by
  by_cases h : a₀ ∈ s
  · rw [Finset.sum_ite_eq' s a₀ (fun _ => c), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [Finset.sum_ite_eq' s a₀ (fun _ => c), ite_eq_right_of_eq_false _ _ (eq_false h)]
    exact Nat.zero_le c

theorem psiPost_step_push {M P : ℕ} (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    {τ w₀ : ℕ} (hτ : τ < proc.steps.length) (hop : proc.steps[τ] = .push w₀) :
    psiPost P proc chain (τ + 1) ≤ psiPost P proc chain τ := by
  obtain ⟨_, _, hst⟩ := unfoldedAt_inv proc (le_of_lt hτ)
  have hval := validFoldedOps_getElem (.nil, none) proc.hValid hτ
  change proc.steps[τ].Valid P (proc.stateAt τ) at hval
  rw [hop, hst] at hval
  have hw₀_lt : ∀ k ∈ unfoldedAt proc τ, w₀ < k := by
    intro k hk
    have hk_fold : k ∈ (spineFoldTree (unfoldedAt proc τ)).1 := by
      rw [← mem_keyFinset_iff, keyFinset_spineFoldTree, mem_keyFinset_iff]
      exact hk
    exact hval.2.2.1 k hk_fold
  have hstep_H : unfoldedAt proc (τ + 1) = .node w₀ .nil (unfoldedAt proc τ) := by
    rw [unfoldedAt_succ proc hτ, hop]; rfl
  unfold psiPost
  refine Finset.sum_le_sum fun ℓ _ => Finset.sum_le_sum fun X hX_fin =>
    Finset.sum_le_sum fun p hp => ?_
  have hX : X ∈ chain ℓ.castSucc := List.mem_toFinset.mp hX_fin
  by_cases htau : tauEmpty proc (subblock1 (childSubblocks (chain ℓ.succ) X) p) ≤ τ
  · apply Finset.card_le_card
    intro q hq
    rw [mem_postQSet_iff] at hq ⊢
    dsimp only at hq ⊢
    rcases hq with ⟨_, hq_Icc, a, ha_Sq, w, hw_Sp, hw_sub⟩
    refine ⟨htau, hq_Icc, a, ha_Sq, w, hw_Sp, ?_⟩
    rw [hstep_H] at hw_sub
    obtain ⟨_, _, hlt_idx, _⟩ := childSubblocks_props hChain ℓ hX
    have hp_Icc := Finset.mem_Icc.mp hp
    have hq_bnds := Finset.mem_Icc.mp hq_Icc
    have hSp_lt_Sq := hlt_idx p q hp_Icc.1 (by omega) hq_bnds.2
    have hwa : w < a := by
      have hw_b := Finset.mem_Icc.mp hw_Sp
      have ha_b := Finset.mem_Icc.mp ha_Sq
      omega
    unfold subtreeAtKey at hw_sub
    split_ifs at hw_sub with haw₀ hw₀a
    · simp [subtreeAtKey] at hw_sub
    · exact hw_sub
    · have ha_eq : a = w₀ := le_antisymm (not_lt.mp hw₀a) (not_lt.mp haw₀)
      subst a
      rw [BinaryTree.mem_node_iff] at hw_sub
      rcases hw_sub with rfl | hw_nil | hw_H
      · exact absurd hwa (lt_irrefl _)
      · cases hw_nil
      · exact absurd (lt_trans hwa (hw₀_lt w hw_H)) (lt_irrefl _)
  · rw [postQSet_succ_empty_of_not_le proc hChain ℓ hX hp htau]
    simp

theorem psiPost_rotateLeftEdge {M P : ℕ} (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    {τ x y : ℕ} (hτ : τ < proc.steps.length)
    (hy_mem : y ∈ unfoldedAt proc τ)
    (hstep_H : unfoldedAt proc (τ + 1) = rotateLeftEdge (unfoldedAt proc τ) y x) :
    psiPost P proc chain (τ + 1) ≤ psiPost P proc chain τ + 1 := by
  classical
  obtain ⟨hbst, hbnd, _⟩ := unfoldedAt_inv proc (le_of_lt hτ)
  have hne_H : unfoldedAt proc τ ≠ .nil := by
    intro heq; rw [heq] at hy_mem; cases hy_mem
  obtain ⟨m₀, hm₀⟩ : ∃ m, (unfoldedAt proc τ).minKey? = some m := by
    rw [minKey?_eq_head?_leftSpine]
    cases hls : leftSpine (unfoldedAt proc τ) with
    | nil => exact absurd ((leftSpine_eq_nil_iff _).mp hls) hne_H
    | cons a _ => exact ⟨a, rfl⟩
  have hm₀_mem : m₀ ∈ unfoldedAt proc τ := minKey?_mem hm₀
  have hm₀_Icc : m₀ ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr (hbnd m₀ hm₀_mem)
  have hy_Icc : y ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr (hbnd y hy_mem)
  let s₀ := partSepScale P chain m₀ y
  have hterm : ∀ (ℓ : Fin M), ∀ X ∈ (chain ℓ.castSucc).toFinset,
      ∀ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
        (postQSet P proc chain ℓ X p (τ + 1)).card ≤
          (postQSet P proc chain ℓ X p τ).card +
            (if hℓ : 1 ≤ s₀ ∧ s₀ ≤ M then
              if ℓ = ⟨s₀ - 1, by omega⟩ then
                if X = blockAt (chain ℓ.castSucc) m₀ then
                  if p = subblockIndex1 (childSubblocks (chain ℓ.succ) X) m₀ then 1 else 0
                else 0
              else 0
            else 0) := by
    intro ℓ X hX_fin p hp
    have hX : X ∈ chain ℓ.castSucc := List.mem_toFinset.mp hX_fin
    let subs := childSubblocks (chain ℓ.succ) X
    let Sp := subblock1 subs p
    by_cases htau : tauEmpty proc Sp ≤ τ
    · obtain ⟨_, hsub_c, hlt_idx, _⟩ := childSubblocks_props hChain ℓ hX
      have hp_bnds := Finset.mem_Icc.mp hp
      have hp_Icc : p ∈ Finset.Icc 1 subs.length :=
        Finset.mem_Icc.mpr ⟨hp_bnds.1, by dsimp only [subs]; omega⟩
      obtain ⟨_, _, hSp_1, _, hSp_le, _, hSp_P, hSp_mem_iff⟩ := hsub_c p hp_Icc
      obtain ⟨_, _, hpop_lt_tau, _⟩ := tauEmpty_bounds_and_disjoint proc hSp_1 hSp_le hSp_P
      have hdiff : ∀ q ∈ postQSet P proc chain ℓ X p (τ + 1),
          q ∉ postQSet P proc chain ℓ X p τ →
          s₀ = ℓ.val + 1 ∧
          X = blockAt (chain ℓ.castSucc) m₀ ∧
          p = subblockIndex1 subs m₀ ∧
          q = subblockIndex1 subs y := by
        intro q hq1 hq0
        rw [mem_postQSet_iff] at hq1 hq0
        dsimp only at hq1 hq0
        rcases hq1 with ⟨_, hq_Icc, a, ha_Sq, w, hw_Sp, hw_sub⟩
        rw [hstep_H] at hw_sub
        have hay : a = y := by
          by_contra hne_ay
          have hw_prev := mem_subtreeAtKey_rotateLeftEdge_ne hbst hne_ay hw_sub
          exact hq0 ⟨htau, hq_Icc, a, ha_Sq, w, hw_Sp, hw_prev⟩
        subst a
        have hw_H : w ∈ unfoldedAt proc τ := by
          have hw_rot := mem_of_mem_subtreeAtKey hw_sub
          rw [← mem_keyFinset_iff, (rotateLeftEdge_isBST_and_keys hbst y x).2,
              mem_keyFinset_iff] at hw_rot
          exact hw_rot
        have hm₀_le_w : m₀ ≤ w := minKey?_le_of_isBST hbst hm₀ hw_H
        have hSp_lo_m₀ : Sp.lo ≤ m₀ := by
          by_contra hlt_m₀
          have hm₀_b := Finset.mem_Icc.mp hm₀_Icc
          have hpop_m₀ : proc.popStepIdx m₀ < proc.popStepIdx Sp.lo :=
            popStepIdx_strictMono proc hm₀_b.1 (by omega) (le_trans hSp_le hSp_P)
          exact not_mem_after_popStepIdx proc hm₀_b.1 hm₀_b.2
            (lt_of_lt_of_le (lt_trans hpop_m₀ hpop_lt_tau) htau) (le_of_lt hτ)
            ((mem_keyFinset_iff _ _).mpr hm₀_mem)
        have hm₀_Sp : m₀ ∈ Sp.toFinset :=
          Finset.mem_Icc.mpr ⟨hSp_lo_m₀, le_trans hm₀_le_w (Finset.mem_Icc.mp hw_Sp).2⟩
        have hq_bnds := Finset.mem_Icc.mp hq_Icc
        have hq_full : q ∈ Finset.Icc 1 subs.length :=
          Finset.mem_Icc.mpr ⟨by omega, hq_bnds.2⟩
        obtain ⟨hp_idx, hbm₀_fine, hbm₀_coarse⟩ := hSp_mem_iff m₀ hm₀_Sp
        obtain ⟨hq_idx, hby_fine, hby_coarse⟩ := (hsub_c q hq_full).2.2.2.2.2.2.2 y ha_Sq
        have hSp_lt_Sq : Sp.hi < (subblock1 subs q).lo :=
          hlt_idx p q hp_bnds.1 (by omega) hq_bnds.2
        have hfine_ne : blockAt (chain ℓ.succ) m₀ ≠ blockAt (chain ℓ.succ) y := by
          rw [hbm₀_fine, hby_fine]
          intro heq
          have hhi_eq : Sp.hi = (subblock1 subs q).hi := congrArg IntervalBlock.hi heq
          have hq_lo_hi := (hsub_c q hq_full).2.2.2.2.1
          dsimp only [subs, Sp] at hhi_eq hSp_lt_Sq ⊢
          omega
        have hsep : s₀ = ℓ.val + 1 :=
          (partSepScale_eq_iff hChain hm₀_Icc hy_Icc ℓ).mpr
            ⟨hbm₀_coarse.trans hby_coarse.symm, hfine_ne⟩
        exact ⟨hsep, hbm₀_coarse.symm, hp_idx.symm, hq_idx.symm⟩
      by_cases hmatch : s₀ = ℓ.val + 1 ∧ X = blockAt (chain ℓ.castSucc) m₀ ∧
          p = subblockIndex1 subs m₀
      · rcases hmatch with ⟨hs₀_eq, hX_eq, hp_eq⟩
        have hs₀_bnds : 1 ≤ s₀ ∧ s₀ ≤ M := by have := ℓ.isLt; omega
        have hℓ_mk : ℓ = ⟨s₀ - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
        have hind_eq :
            (if hℓ : 1 ≤ s₀ ∧ s₀ ≤ M then
              if ℓ = ⟨s₀ - 1, by omega⟩ then
                if X = blockAt (chain ℓ.castSucc) m₀ then
                  if p = subblockIndex1 (childSubblocks (chain ℓ.succ) X) m₀ then 1 else 0
                else 0
              else 0
            else 0) = 1 := by
          dsimp only [subs] at hp_eq
          simp only [hs₀_bnds, and_self, ↓reduceDIte, hℓ_mk, hX_eq, hp_eq, ↓reduceIte]
        rw [hind_eq]
        have hsub_ins : postQSet P proc chain ℓ X p (τ + 1) ⊆
            insert (subblockIndex1 subs y) (postQSet P proc chain ℓ X p τ) := by
          intro q hq1
          by_cases hq0 : q ∈ postQSet P proc chain ℓ X p τ
          · exact Finset.mem_insert_of_mem hq0
          · exact Finset.mem_insert.mpr (Or.inl (hdiff q hq1 hq0).2.2.2)
        exact le_trans (Finset.card_le_card hsub_ins) (Finset.card_insert_le _ _)
      · have hsub_same : postQSet P proc chain ℓ X p (τ + 1) ⊆
            postQSet P proc chain ℓ X p τ := by
          intro q hq1
          by_contra hq0
          have hd := hdiff q hq1 hq0
          exact hmatch ⟨hd.1, hd.2.1, hd.2.2.1⟩
        exact le_trans (Finset.card_le_card hsub_same) (Nat.le_add_right _ _)
    · rw [postQSet_succ_empty_of_not_le proc hChain ℓ hX hp htau]
      simp
  unfold psiPost
  calc
    (∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
        ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
          (postQSet P proc chain ℓ X p (τ + 1)).card)
      ≤ ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            ((postQSet P proc chain ℓ X p τ).card +
              (if hℓ : 1 ≤ s₀ ∧ s₀ ≤ M then
                if ℓ = ⟨s₀ - 1, by omega⟩ then
                  if X = blockAt (chain ℓ.castSucc) m₀ then
                    if p = subblockIndex1 (childSubblocks (chain ℓ.succ) X) m₀ then 1 else 0
                  else 0
                else 0
              else 0)) :=
      Finset.sum_le_sum fun ℓ _ => Finset.sum_le_sum fun X hX =>
        Finset.sum_le_sum fun p hp => hterm ℓ X hX p hp
    _ = (∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (postQSet P proc chain ℓ X p τ).card) +
        (∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (if hℓ : 1 ≤ s₀ ∧ s₀ ≤ M then
              if ℓ = ⟨s₀ - 1, by omega⟩ then
                if X = blockAt (chain ℓ.castSucc) m₀ then
                  if p = subblockIndex1 (childSubblocks (chain ℓ.succ) X) m₀ then 1 else 0
                else 0
              else 0
            else 0)) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ (∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (postQSet P proc chain ℓ X p τ).card) + 1 := by
      apply Nat.add_le_add_left
      by_cases hℓ : 1 ≤ s₀ ∧ s₀ ≤ M
      · have hsum_eq :
            (∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
              ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
                (if hℓ' : 1 ≤ s₀ ∧ s₀ ≤ M then
                  if ℓ = ⟨s₀ - 1, by omega⟩ then
                    if X = blockAt (chain ℓ.castSucc) m₀ then
                      if p = subblockIndex1 (childSubblocks (chain ℓ.succ) X) m₀ then 1 else 0
                    else 0
                  else 0
                else 0)) =
            (∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
              ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
                (if ℓ = ⟨s₀ - 1, by omega⟩ then
                  if X = blockAt (chain ℓ.castSucc) m₀ then
                    if p = subblockIndex1 (childSubblocks (chain ℓ.succ) X) m₀ then 1 else 0
                  else 0
                else 0)) := by
          refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun X _ =>
            Finset.sum_congr rfl fun p _ => by simp only [hℓ, and_self, ↓reduceDIte]
        rw [hsum_eq]
        refine le_trans (Finset.sum_le_sum fun ℓ _ => ?_)
          (sum_ite_eq_le Finset.univ (⟨s₀ - 1, by omega⟩ : Fin M) 1)
        by_cases h1 : ℓ = ⟨s₀ - 1, by omega⟩
        · simp only [h1, ↓reduceIte]
          set ℓ₀ : Fin M := ⟨s₀ - 1, by omega⟩
          refine le_trans (Finset.sum_le_sum fun X _ => ?_)
            (sum_ite_eq_le (chain ℓ₀.castSucc).toFinset (blockAt (chain ℓ₀.castSucc) m₀) 1)
          by_cases h2 : X = blockAt (chain ℓ₀.castSucc) m₀
          · simp only [h2, ↓reduceIte]
            exact sum_ite_eq_le _ _ 1
          · simp [h2]
        · simp [h1]
      · simp [hℓ]

theorem psiPost_step_pop {M P : ℕ} (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    {τ s : ℕ} (hτ : τ < proc.steps.length) (hop : proc.steps[τ] = .pop s) :
    psiPost P proc chain (τ + 1) +
      ((b3ExitPost P proc chain).filter (fun e => e.stepIdx = τ)).card ≤
      psiPost P proc chain τ := by
  classical
  have hP := hChain.1
  obtain ⟨hbst, _, hst⟩ := unfoldedAt_inv proc (le_of_lt hτ)
  have hval := validFoldedOps_getElem (.nil, none) proc.hValid hτ
  change proc.steps[τ].Valid P (proc.stateAt τ) at hval
  rw [hop, hst] at hval
  rcases hval with ⟨_, _, hmin_fold, _, _⟩
  have hmin_H : (unfoldedAt proc τ).minKey? = some s :=
    (minKey?_spineFoldTree hbst).symm.trans hmin_fold
  have hstep_H : unfoldedAt proc (τ + 1) = popCascade (unfoldedAt proc τ) := by
    rw [unfoldedAt_succ proc hτ, hop]; rfl
  obtain ⟨hrInt_coords, hrInt_inj⟩ := rInt_step_pop_spine proc hτ hop
  let rots_τ := (b3ExitPost P proc chain).filter (fun e => e.stepIdx = τ)
  let fib (ℓ : Fin M) (X : IntervalBlock) (p : ℕ) : Finset InternalPopRot :=
    rots_τ.filter (fun e =>
      partSepScale P chain e.x e.y = ℓ.val + 1 ∧
      blockAt (chain ℓ.castSucc) e.s = X ∧
      subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.s = p)
  have hcell : ∀ (ℓ : Fin M), ∀ X ∈ (chain ℓ.castSucc).toFinset,
      ∀ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
        (postQSet P proc chain ℓ X p (τ + 1)).card + (fib ℓ X p).card ≤
          (postQSet P proc chain ℓ X p τ).card := by
    intro ℓ X hX_fin p hp
    have hX : X ∈ chain ℓ.castSucc := List.mem_toFinset.mp hX_fin
    let subs := childSubblocks (chain ℓ.succ) X
    let Sp := subblock1 subs p
    obtain ⟨_, _, hlt_idx, hcov_X⟩ := childSubblocks_props hChain ℓ hX
    have hsub_mono : postQSet P proc chain ℓ X p (τ + 1) ⊆ postQSet P proc chain ℓ X p τ := by
      by_cases htau : tauEmpty proc Sp ≤ τ
      · intro q hq1
        rw [mem_postQSet_iff] at hq1 ⊢
        dsimp only at hq1 ⊢
        rcases hq1 with ⟨_, hq_Icc, a, ha_Sq, w, hw_Sp, hw_sub⟩
        rw [hstep_H] at hw_sub
        have hp_bnds := Finset.mem_Icc.mp hp
        have hq_bnds := Finset.mem_Icc.mp hq_Icc
        have hSp_lt_Sq := hlt_idx p q hp_bnds.1 (by omega) hq_bnds.2
        have hwa : w < a := by
          have := Finset.mem_Icc.mp hw_Sp
          have := Finset.mem_Icc.mp ha_Sq
          omega
        exact ⟨htau, hq_Icc, a, ha_Sq, w, hw_Sp,
          mem_subtreeAtKey_popCascade_lt hbst hmin_H hwa hw_sub⟩
      · rw [postQSet_succ_empty_of_not_le proc hChain ℓ hX hp htau]
        exact Finset.empty_subset _
    have hfib_maps : Set.MapsTo (fun e : InternalPopRot => subblockIndex1 subs e.y)
        (fib ℓ X p : Set InternalPopRot)
        ((postQSet P proc chain ℓ X p τ \ postQSet P proc chain ℓ X p (τ + 1) : Finset ℕ) : Set ℕ) := by
      intro e he_set
      have he_fib : e ∈ fib ℓ X p := he_set
      simp only [fib, rots_τ, Finset.mem_filter] at he_fib
      rcases he_fib with ⟨⟨he_post, he_τ⟩, hsep_xy, hX_eq, hp_eq⟩
      obtain ⟨he_rInt, ℓ', hs1_eq, hs2_eq, hhi_lt_z, hpost_cond⟩ :=
        (mem_b3ExitPost_iff P proc chain e).mp he_post
      have hℓ'_eq : ℓ' = ℓ := Fin.ext (by omega)
      subst ℓ'
      obtain ⟨hj, hlen, hs_eq, h0_eq, hx_eq, hy_eq, hz_eq,
        hs1_bnd, hs_lt_x, hx_lt_y, hy_lt_z, hzP_bnd⟩ := hrInt_coords e he_rInt he_τ
      have hs_Icc : e.s ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨hs1_bnd, by omega⟩
      have hx_Icc : e.x ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hy_Icc : e.y ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      obtain ⟨hsx_coarse, hsx_fine⟩ :=
        (partSepScale_eq_iff hChain hs_Icc hx_Icc ℓ).mp hs1_eq
      obtain ⟨hxy_coarse, hxy_fine⟩ :=
        (partSepScale_eq_iff hChain hx_Icc hy_Icc ℓ).mp hs2_eq
      have hs_X : e.s ∈ X.toFinset := by
        obtain ⟨_, hlo, hhi⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 ℓ.castSucc)).1 e.s hs_Icc
        rw [hX_eq] at hlo hhi
        exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
      have hx_X : e.x ∈ X.toFinset := by
        obtain ⟨_, hlo, hhi⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 ℓ.castSucc)).1 e.x hx_Icc
        rw [← hsx_coarse, hX_eq] at hlo hhi
        exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
      have hy_X : e.y ∈ X.toFinset := by
        obtain ⟨_, hlo, hhi⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 ℓ.castSucc)).1 e.y hy_Icc
        rw [← hxy_coarse, ← hsx_coarse, hX_eq] at hlo hhi
        exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
      obtain ⟨hp_sub_Icc, hSp_block, hs_Sp⟩ := hcov_X e.s hs_X
      rw [hp_eq] at hp_sub_Icc hSp_block hs_Sp
      obtain ⟨hb_sub_Icc, hSb_block, hx_Sb⟩ := hcov_X e.x hx_X
      obtain ⟨hq_sub_Icc, hSq_block, hy_Sq⟩ := hcov_X e.y hy_X
      let b := subblockIndex1 subs e.x
      let q := subblockIndex1 subs e.y
      have hp_bnds := Finset.mem_Icc.mp hp_sub_Icc
      have hb_bnds := Finset.mem_Icc.mp hb_sub_Icc
      have hq_bnds := Finset.mem_Icc.mp hq_sub_Icc
      have hpb : p < b := by
        rcases lt_trichotomy p b with hlt | heq | hgt
        · exact hlt
        · exfalso
          exact hsx_fine (hSp_block.symm.trans ((congrArg (subblock1 subs) heq).trans hSb_block))
        · exfalso
          have h1 := hlt_idx b p hb_bnds.1 hgt hp_bnds.2
          have h2 := Finset.mem_Icc.mp hs_Sp
          have h3 := Finset.mem_Icc.mp hx_Sb
          dsimp only [subs, b] at h1 h2 h3
          omega
      have hbq : b < q := by
        rcases lt_trichotomy b q with hlt | heq | hgt
        · exact hlt
        · exfalso
          exact hxy_fine (hSb_block.symm.trans ((congrArg (subblock1 subs) heq).trans hSq_block))
        · exfalso
          have h1 := hlt_idx q b hq_bnds.1 hgt hb_bnds.2
          have h2 := Finset.mem_Icc.mp hx_Sb
          have h3 := Finset.mem_Icc.mp hy_Sq
          dsimp only [subs, b, q] at h1 h2 h3
          omega
      have htau_Sp : tauEmpty proc Sp ≤ τ := by
        rw [← hSp_block] at hpost_cond
        simpa [he_τ] using hpost_cond
      have hq_in_τ : q ∈ postQSet P proc chain ℓ X p τ := by
        rw [mem_postQSet_iff]
        dsimp only
        refine ⟨htau_Sp, Finset.mem_Icc.mpr ⟨by omega, hq_bnds.2⟩, e.y, hy_Sq, e.s, hs_Sp, ?_⟩
        have hs_sub := mem_subtreeAtKey_of_leftSpine hbst (Nat.zero_le (2 * e.j))
          (show 2 * e.j < (leftSpine (unfoldedAt proc τ)).length by omega)
        simpa [← hs_eq, h0_eq, ← hy_eq] using hs_sub
      have hq_not_τ1 : q ∉ postQSet P proc chain ℓ X p (τ + 1) := by
        intro hq1
        rw [mem_postQSet_iff] at hq1
        dsimp only at hq1
        rcases hq1 with ⟨_, _, a, ha_Sq, w, hw_Sp, hw_sub⟩
        rw [hstep_H] at hw_sub
        have hSp_lt_Sb := hlt_idx p b hp_bnds.1 hpb hb_bnds.2
        have hSb_lt_Sq := hlt_idx b q hb_bnds.1 hbq hq_bnds.2
        have hxa : (leftSpine (unfoldedAt proc τ))[2 * e.j - 1]'(by omega) < a := by
          rw [← hx_eq]
          have h1 := Finset.mem_Icc.mp hx_Sb
          have h2 := Finset.mem_Icc.mp ha_Sq
          dsimp only [subs, b, q] at hSb_lt_Sq h1 h2
          omega
        have haz : a < (leftSpine (unfoldedAt proc τ))[2 * e.j + 1]'hlen := by
          rw [← hz_eq]
          have ha_hi : a ≤ (subblock1 subs q).hi := (Finset.mem_Icc.mp ha_Sq).2
          rw [hSq_block] at ha_hi
          omega
        have hwx : w < (leftSpine (unfoldedAt proc τ))[2 * e.j - 1]'(by omega) := by
          rw [← hx_eq]
          have h1 := Finset.mem_Icc.mp hw_Sp
          have h2 := Finset.mem_Icc.mp hx_Sb
          dsimp only [subs, b] at hSp_lt_Sb h1 h2
          omega
        exact not_mem_subtreeAtKey_popCascade_between hbst hj hlen hxa haz hwx hw_sub
      exact Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨hq_in_τ, hq_not_τ1⟩)
    have hfib_inj : Set.InjOn (fun e : InternalPopRot => subblockIndex1 subs e.y)
        (fib ℓ X p : Set InternalPopRot) := by
      intro e₁ he₁_set e₂ he₂_set hq_eq
      have he₁ : e₁ ∈ fib ℓ X p := he₁_set
      have he₂ : e₂ ∈ fib ℓ X p := he₂_set
      simp only [fib, rots_τ, Finset.mem_filter] at he₁ he₂
      rcases he₁ with ⟨⟨he₁_post, he₁_τ⟩, _, _, _⟩
      rcases he₂ with ⟨⟨he₂_post, he₂_τ⟩, _, _, _⟩
      have he₁_rInt := ((mem_b3ExitPost_iff P proc chain e₁).mp he₁_post).1
      have he₂_rInt := ((mem_b3ExitPost_iff P proc chain e₂).mp he₂_post).1
      have hpair12 := hrInt_inj e₁ he₁_rInt e₂ he₂_rInt he₁_τ he₂_τ
      have hpair21 := hrInt_inj e₂ he₂_rInt e₁ he₁_rInt he₂_τ he₁_τ
      have habs : ∀ d₁ d₂ : InternalPopRot,
          d₁ ∈ fib ℓ X p → d₂ ∈ fib ℓ X p →
          d₁.z ≤ d₂.x →
          subblockIndex1 subs d₁.y = subblockIndex1 subs d₂.y → False := by
        intro d₁ d₂ hd1_fib hd2_fib hz_le_x hsub_eq
        simp only [fib, rots_τ, Finset.mem_filter] at hd1_fib hd2_fib
        rcases hd1_fib with ⟨⟨hd1_post, ht1⟩, hsp1, hx1, _⟩
        rcases hd2_fib with ⟨⟨hd2_post, ht2⟩, hsp2, hx2, _⟩
        obtain ⟨hd1, ℓ₁, hs1_1, _, hhi1, _⟩ := (mem_b3ExitPost_iff P proc chain d₁).mp hd1_post
        obtain ⟨hd2, ℓ₂, hs1_2, _, _, _⟩ := (mem_b3ExitPost_iff P proc chain d₂).mp hd2_post
        have hℓ1_eq : ℓ₁ = ℓ := Fin.ext (by omega)
        have hℓ2_eq : ℓ₂ = ℓ := Fin.ext (by omega)
        subst ℓ₁; subst ℓ₂
        obtain ⟨_, _, _, _, _, _, _, hds1, hdsx1, hdxy1, hdyz1, hdz1⟩ := hrInt_coords d₁ hd1 ht1
        obtain ⟨_, _, _, _, _, _, _, hds2, hdsx2, hdxy2, hdyz2, hdz2⟩ := hrInt_coords d₂ hd2 ht2
        have hs2_Icc : d₂.s ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨hds2, by omega⟩
        have hx2_Icc : d₂.x ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hy2_Icc : d₂.y ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hs1_Icc : d₁.s ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨hds1, by omega⟩
        have hx1_Icc : d₁.x ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hy1_Icc : d₁.y ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hc_sx1 := ((partSepScale_eq_iff hChain hs1_Icc hx1_Icc ℓ).mp hs1_1).1
        have hc_xy1 := ((partSepScale_eq_iff hChain hx1_Icc hy1_Icc ℓ).mp hsp1).1
        have hc_sx2 := ((partSepScale_eq_iff hChain hs2_Icc hx2_Icc ℓ).mp hs1_2).1
        have hc_xy2 := ((partSepScale_eq_iff hChain hx2_Icc hy2_Icc ℓ).mp hsp2).1
        have hy1_X : d₁.y ∈ X.toFinset := by
          obtain ⟨_, hlo, hhi⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 ℓ.castSucc)).1 d₁.y hy1_Icc
          rw [← hc_xy1, ← hc_sx1, hx1] at hlo hhi
          exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
        have hy2_X : d₂.y ∈ X.toFinset := by
          obtain ⟨_, hlo, hhi⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 ℓ.castSucc)).1 d₂.y hy2_Icc
          rw [← hc_xy2, ← hc_sx2, hx2] at hlo hhi
          exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
        obtain ⟨_, hSq1_eq, _⟩ := hcov_X d₁.y hy1_X
        obtain ⟨_, _, hy2_Sq2⟩ := hcov_X d₂.y hy2_X
        rw [← hsub_eq, hSq1_eq] at hy2_Sq2
        have hy2_hi : d₂.y ≤ (blockAt (chain ℓ.succ) d₁.y).hi := (Finset.mem_Icc.mp hy2_Sq2).2
        omega
      rcases lt_trichotomy e₁.j e₂.j with hlt | heq | hgt
      · exact False.elim (habs e₁ e₂ he₁_set he₂_set (hpair12.2 hlt) hq_eq)
      · exact hpair12.1 heq
      · exact False.elim (habs e₂ e₁ he₂_set he₁_set (hpair21.2 hgt) hq_eq.symm)
    have hcard_le : (fib ℓ X p).card ≤
        (postQSet P proc chain ℓ X p τ \ postQSet P proc chain ℓ X p (τ + 1)).card :=
      Finset.card_le_card_of_injOn _ hfib_maps hfib_inj
    have hsdiff_eq :
        (postQSet P proc chain ℓ X p τ \ postQSet P proc chain ℓ X p (τ + 1)).card +
          (postQSet P proc chain ℓ X p (τ + 1)).card =
        (postQSet P proc chain ℓ X p τ).card :=
      Finset.card_sdiff_add_card_eq_card hsub_mono
    omega
  have hrots_cover : rots_τ ⊆
      Finset.univ.biUnion (fun ℓ : Fin M =>
        (chain ℓ.castSucc).toFinset.biUnion (fun X =>
          (Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)).biUnion (fun p =>
            fib ℓ X p))) := by
    intro e he_rots
    have he_rots_orig := he_rots
    simp only [rots_τ, Finset.mem_filter] at he_rots
    rcases he_rots with ⟨he_post, he_τ⟩
    obtain ⟨he_rInt, ℓ_e, hs1_eq, hs2_eq, _, _⟩ :=
      (mem_b3ExitPost_iff P proc chain e).mp he_post
    obtain ⟨_, _, _, _, _, _, _, hs1_bnd, hs_lt_x, hx_lt_y, hy_lt_z, hzP_bnd⟩ :=
      hrInt_coords e he_rInt he_τ
    have hs_Icc : e.s ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨hs1_bnd, by omega⟩
    have hx_Icc : e.x ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    obtain ⟨hsx_coarse, hsx_fine⟩ :=
      (partSepScale_eq_iff hChain hs_Icc hx_Icc ℓ_e).mp hs1_eq
    let X_e := blockAt (chain ℓ_e.castSucc) e.s
    obtain ⟨hX_mem, hX_lo, hX_hi⟩ :=
      (blockAt_mem_and_unique hP (hChain.2.2.1 ℓ_e.castSucc)).1 e.s hs_Icc
    obtain ⟨_, _, hlt_e, hcov_e⟩ := childSubblocks_props hChain ℓ_e hX_mem
    have hs_Xe : e.s ∈ X_e.toFinset := Finset.mem_Icc.mpr ⟨hX_lo, hX_hi⟩
    have hx_Xe : e.x ∈ X_e.toFinset := by
      obtain ⟨_, hlo, hhi⟩ :=
        (blockAt_mem_and_unique hP (hChain.2.2.1 ℓ_e.castSucc)).1 e.x hx_Icc
      rw [← hsx_coarse] at hlo hhi
      exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
    obtain ⟨hp_Icc, hSp_eq, hs_Sp⟩ := hcov_e e.s hs_Xe
    obtain ⟨hb_Icc, hSb_eq, hx_Sb⟩ := hcov_e e.x hx_Xe
    let subs_e := childSubblocks (chain ℓ_e.succ) X_e
    let p_e := subblockIndex1 subs_e e.s
    let b_e := subblockIndex1 subs_e e.x
    have hp_bnds := Finset.mem_Icc.mp hp_Icc
    have hb_bnds := Finset.mem_Icc.mp hb_Icc
    have hpb : p_e < b_e := by
      rcases lt_trichotomy p_e b_e with hlt | heq | hgt
      · exact hlt
      · exfalso
        exact hsx_fine (hSp_eq.symm.trans ((congrArg (subblock1 subs_e) heq).trans hSb_eq))
      · exfalso
        have h1 := hlt_e b_e p_e hb_bnds.1 hgt hp_bnds.2
        have h2 := Finset.mem_Icc.mp hs_Sp
        have h3 := Finset.mem_Icc.mp hx_Sb
        dsimp only [X_e, subs_e, p_e, b_e] at h1 h2 h3
        omega
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨ℓ_e, X_e, List.mem_toFinset.mpr hX_mem, p_e,
      Finset.mem_Icc.mpr ⟨hp_bnds.1, by dsimp only [X_e, subs_e, p_e, b_e] at hpb hb_bnds ⊢; omega⟩, ?_⟩
    simp only [fib, Finset.mem_filter]
    exact ⟨he_rots_orig, hs2_eq, rfl, rfl⟩
  have hrots_card : rots_τ.card ≤
      ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
        ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
          (fib ℓ X p).card := by
    calc
      rots_τ.card ≤ _ := Finset.card_le_card hrots_cover
      _ ≤ ∑ ℓ : Fin M,
          ((chain ℓ.castSucc).toFinset.biUnion (fun X =>
            (Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)).biUnion (fun p =>
              fib ℓ X p))).card := Finset.card_biUnion_le
      _ ≤ ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ((Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)).biUnion (fun p =>
            fib ℓ X p)).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
      _ ≤ ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (fib ℓ X p).card :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
  have hsum_cells :
      psiPost P proc chain (τ + 1) +
        (∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (fib ℓ X p).card) ≤
      psiPost P proc chain τ := by
    unfold psiPost
    calc
      (∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (postQSet P proc chain ℓ X p (τ + 1)).card) +
        (∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (fib ℓ X p).card)
        = ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
            ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
              ((postQSet P proc chain ℓ X p (τ + 1)).card + (fib ℓ X p).card) := by
        simp only [Finset.sum_add_distrib]
      _ ≤ ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
            ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
              (postQSet P proc chain ℓ X p τ).card :=
        Finset.sum_le_sum fun ℓ _ => Finset.sum_le_sum fun X hX =>
          Finset.sum_le_sum fun p hp => hcell ℓ X hX p hp
  dsimp only [rots_τ] at hrots_card
  omega

def isUpperStep : FoldedOp → Bool
  | .shift => true
  | .upperRot _ _ => true
  | _ => false

theorem rots_at_non_pop_empty {M P : ℕ} (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) {τ : ℕ}
    (hτ : τ < proc.steps.length) (hnopop : ∀ s, proc.steps[τ] ≠ .pop s) :
    (b3ExitPost P proc chain).filter (fun e => e.stepIdx = τ) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro e he hτ_eq
  have he_rInt : e ∈ proc.rInt := ((mem_b3ExitPost_iff P proc chain e).mp he).1
  obtain ⟨hτ_e, hmem⟩ := (mem_rInt_iff proc e).mp he_rInt
  have hop_eq : proc.steps[e.stepIdx]'hτ_e = proc.steps[τ] := by simp [hτ_eq]
  rw [hop_eq] at hmem
  cases hop : proc.steps[τ] with
  | pop s => exact hnopop s hop
  | _ => rw [hop] at hmem; simp [foldedPopRotsAt] at hmem

theorem psiPost_step_unified {M P : ℕ} (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    {τ : ℕ} (hτ : τ < proc.steps.length) :
    psiPost P proc chain (τ + 1) +
      ((b3ExitPost P proc chain).filter (fun e => e.stepIdx = τ)).card ≤
      psiPost P proc chain τ + (if isUpperStep proc.steps[τ] then 1 else 0) := by
  obtain ⟨hbst, _, hst⟩ := unfoldedAt_inv proc (le_of_lt hτ)
  have hval := validFoldedOps_getElem (.nil, none) proc.hValid hτ
  change proc.steps[τ].Valid P (proc.stateAt τ) at hval
  rw [hst] at hval
  cases hop : proc.steps[τ] with
  | push w₀ =>
    rw [rots_at_non_pop_empty proc chain hτ (by intro s h; rw [hop] at h; cases h)]
    simp only [Finset.card_empty, Nat.add_zero, isUpperStep, Bool.false_eq_true, ↓reduceIte]
    exact psiPost_step_push proc hChain hτ hop
  | shift =>
    rw [rots_at_non_pop_empty proc chain hτ (by intro s h; rw [hop] at h; cases h)]
    simp only [Finset.card_empty, Nat.add_zero, isUpperStep, ↓reduceIte]
    rw [hop] at hval
    rcases hval with ⟨b, hb_some, _, hroot_ne⟩
    have hstep := unfoldedAt_succ proc hτ
    rw [hop] at hstep
    cases hH : unfoldedAt proc τ with
    | nil =>
      rw [hH] at hb_some; simp [spineFoldTree] at hb_some
    | node b1 L1 R1 =>
      cases R1 with
      | nil =>
        rw [hH] at hb_some hroot_ne
        simp only [spineFoldTree, rightSpineFrames, spineFoldGo, Option.some.injEq] at hb_some
        subst hb_some
        exact absurd rfl hroot_ne
      | node b2 L2 R2 =>
        have hb2_mem : b2 ∈ unfoldedAt proc τ := by
          rw [hH]; exact .right .here
        have hstep' : unfoldedAt proc (τ + 1) = rotateLeftEdge (unfoldedAt proc τ) b2 b1 := by
          rw [hH] at hstep ⊢
          exact hstep
        exact psiPost_rotateLeftEdge proc hChain hτ hb2_mem hstep'
  | upperRot u v =>
    rw [rots_at_non_pop_empty proc chain hτ (by intro s h; rw [hop] at h; cases h)]
    simp only [Finset.card_empty, Nat.add_zero, isUpperStep, ↓reduceIte]
    rw [hop] at hval
    have hex := step_upperRot_spineFoldTree hbst hval
    have hstep := unfoldedAt_succ proc hτ
    rw [hop] at hstep
    dsimp only [unfoldedStep] at hstep
    simp only [hex, ↓reduceDIte] at hstep
    exact psiPost_rotateLeftEdge proc hChain hτ hex.choose_spec.choose_spec.2.1 hstep
  | pop s =>
    simp only [isUpperStep, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact psiPost_step_pop proc hChain hτ hop

theorem kL_eq_filter_isUpperStep {P : ℕ} (proc : FoldedPopProcess P) :
    proc.kL = (proc.steps.filter isUpperStep).length := by
  unfold FoldedPopProcess.kL FoldedPopProcess.kShift FoldedPopProcess.kRot
  suffices ∀ xs : List FoldedOp,
      (xs.filter (fun | .shift => true | _ => false)).length +
        (xs.filter (fun | .upperRot _ _ => true | _ => false)).length =
      (xs.filter isUpperStep).length from this proc.steps
  intro xs
  induction xs with
  | nil => rfl
  | cons op rest ih =>
    cases op <;> simp [isUpperStep, List.filter_cons] <;> omega

theorem lem_5_5_b3_post (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (b3ExitPost P proc chain).card ≤ proc.kL ∧ proc.kL < 2 * P := by
  intro chain
  have hChain : IsNestedPartitionChain P chain := validScaleTree_isNestedPartitionChain hValid
  have hP : 1 ≤ P := hValid.1
  have hkL_lt : proc.kL < 2 * P := by
    rw [kL_eq_filter_isUpperStep]
    rcases proc.hKLBound with ⟨hP0, _⟩ | ⟨_, hlt⟩
    · omega
    · exact hlt
  have htele : ∀ m ≤ proc.steps.length,
      psiPost P proc chain m +
        ((b3ExitPost P proc chain).filter (fun e => e.stepIdx < m)).card ≤
      ((proc.steps.take m).filter isUpperStep).length := by
    intro m hm
    induction m with
    | zero =>
      rw [psiPost_zero]
      have hemp : (b3ExitPost P proc chain).filter (fun e => e.stepIdx < 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro e _ h; omega
      rw [hemp]
      simp
    | succ m ih =>
      have hm_lt : m < proc.steps.length := Nat.lt_of_succ_le hm
      have ih_m := ih (le_of_lt hm_lt)
      have hstep_m := psiPost_step_unified proc hChain hm_lt
      have hsplit_rots :
          (b3ExitPost P proc chain).filter (fun e => e.stepIdx < m + 1) =
          (b3ExitPost P proc chain).filter (fun e => e.stepIdx < m) ∪
            (b3ExitPost P proc chain).filter (fun e => e.stepIdx = m) := by
        ext e
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro ⟨he, hlt⟩
          rcases eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with heq | hlt'
          · exact Or.inr ⟨he, heq⟩
          · exact Or.inl ⟨he, hlt'⟩
        · rintro (⟨he, hlt⟩ | ⟨he, heq⟩)
          · exact ⟨he, by omega⟩
          · exact ⟨he, by omega⟩
      have hdisj_rots : Disjoint
          ((b3ExitPost P proc chain).filter (fun e => e.stepIdx < m))
          ((b3ExitPost P proc chain).filter (fun e => e.stepIdx = m)) := by
        rw [Finset.disjoint_filter]
        intro e _ h1 h2; omega
      have hcard_rots :
          ((b3ExitPost P proc chain).filter (fun e => e.stepIdx < m + 1)).card =
          ((b3ExitPost P proc chain).filter (fun e => e.stepIdx < m)).card +
            ((b3ExitPost P proc chain).filter (fun e => e.stepIdx = m)).card := by
        rw [hsplit_rots, Finset.card_union_of_disjoint hdisj_rots]
      have htake_len :
          ((proc.steps.take (m + 1)).filter isUpperStep).length =
          ((proc.steps.take m).filter isUpperStep).length +
            (if isUpperStep proc.steps[m] then 1 else 0) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hm_lt, Option.toList_some,
            List.filter_append, List.length_append]
        cases hup : isUpperStep proc.steps[m] <;> simp [hup]
      omega
  have hend := htele proc.steps.length le_rfl
  have hfilter_all :
      (b3ExitPost P proc chain).filter (fun e => e.stepIdx < proc.steps.length) =
        b3ExitPost P proc chain := by
    rw [Finset.filter_eq_self]
    intro e he
    have he_rInt : e ∈ proc.rInt := ((mem_b3ExitPost_iff P proc chain e).mp he).1
    exact ((mem_rInt_iff proc e).mp he_rInt).1
  rw [hfilter_all, List.take_length, ← kL_eq_filter_isUpperStep] at hend
  exact ⟨by omega, hkL_lt⟩
end Internal55

namespace Internal56
set_option maxHeartbeats 800000

open SplayTree BinaryTree

/-! ## Upstream Layer 0..1 Hypothesis Types (Exact `Challenge.lean` Statements) -/

abbrev Ty_lem_3_6 : Prop :=
  ∀ (P : ℕ), 1 ≤ P → ∀ (proc : FoldedPopProcess P),
    -- Part (1): Postorder and parent monotonicity
    ((∀ τ : ℕ, τ ≤ proc.steps.length →
        (proc.treeAt τ).IsBST ∧
        keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P ∧
        postorderL2OnV (proc.treeAt τ) = (proc.treeAt τ).toKeyList ∧
        ∀ v ∈ proc.treeAt τ, v < foldedParent P (proc.treeAt τ) v) ∧
     (∀ τ u v : ℕ, τ < proc.steps.length → proc.steps[τ]? = some (.upperRot u v) →
        let z := foldedParent P (proc.treeAt τ) v
        foldedParent P (proc.treeAt (τ + 1)) u = z ∧
        ∀ w ∈ proc.treeAt (τ + 1), w ≠ u →
          foldedParent P (proc.treeAt (τ + 1)) w = foldedParent P (proc.treeAt τ) w) ∧
     (∀ s : ℕ, 1 ≤ s → s ≤ P →
        let τ := proc.popStepIdx s
        (∀ e ∈ proc.rInt, e.stepIdx = τ →
          foldedParent P (proc.treeAt (τ + 1)) e.x = e.z) ∧
        (∀ w ∈ proc.treeAt (τ + 1), (∀ e ∈ proc.rInt, e.stepIdx = τ → w ≠ e.x) →
          foldedParent P (proc.treeAt (τ + 1)) w = foldedParent P (proc.treeAt τ) w)) ∧
     (∀ τ₁ τ₂ v : ℕ, τ₁ ≤ τ₂ → τ₂ ≤ proc.steps.length →
        v ∈ proc.treeAt τ₁ → v ∈ proc.treeAt τ₂ →
        foldedParent P (proc.treeAt τ₁) v ≤ foldedParent P (proc.treeAt τ₂) v ∧
        l2Ancestors P (proc.treeAt τ₂) v ⊆ l2Ancestors P (proc.treeAt τ₁) v)) ∧
    -- Part (2): Spine interval partition and `(x, z)` interval-freezing
    ((∀ τ : ℕ, τ ≤ proc.steps.length → proc.treeAt τ ≠ .nil →
        let ls := leftSpine (proc.treeAt τ)
        ∀ idx : Fin ls.length,
          let u_i := ls[idx]
          let u_next := if h : idx.val + 1 < ls.length then ls[idx.val + 1] else P + 1
          insert u_i (keyFinset ((subtreeAtKey (proc.treeAt τ) u_i).right)) =
            keyFinset (proc.treeAt τ) ∩ Finset.Icc u_i (u_next - 1)) ∧
     (∀ e ∈ proc.rInt,
        1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P ∧
        (∀ τ' ∈ Finset.Ico (e.stepIdx + 1) (proc.popStepIdx e.x),
          ∀ w : ℕ, proc.steps[τ']? = some (.push w) → w < e.x) ∧
        (∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
          ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z)))) ∧
    -- Part (3): Backward adjacent-pair injectivity
    (proc.mBase ⊆ proc.rInt ∧
     proc.mBase.card ≤ 2 * P + proc.kRot ∧
     2 * P + proc.kRot < 4 * P ∧
     ∃ eL eR : InternalPopRot → InternalPopRot,
       Set.InjOn eL (proc.rInt \ proc.mBase : Set InternalPopRot) ∧
       Set.InjOn eR (proc.rInt \ proc.mBase : Set InternalPopRot) ∧
       ∀ e ∈ proc.rInt \ proc.mBase,
         eL e ∈ proc.rInt ∧
         eR e ∈ proc.rInt ∧
         proc.nextCascadeRot? (eL e) = some (eR e) ∧
         (eL e).s = (eR e).s ∧
         (eL e).s < e.s ∧
         (∀ e' ∈ proc.rInt, e'.x = e.x → e'.s < e.s → e'.s ≤ (eL e).s) ∧
         (eL e).x = e.x ∧
         (eL e).z = e.y ∧
         (eR e).x = e.y ∧
         (eL e).s < e.x ∧ e.x < (eL e).y ∧ (eL e).y < e.y ∧
         e.y < (eR e).y ∧ (eR e).y < (eR e).z)

abbrev Ty_lem_5_1 : Prop :=
  ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
    let chain := scaleTreePartitionChain T P M
    (∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T ℓ : ℝ)) < (1 : ℝ) / 2 ∧
    (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) < 2 ∧
    (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50

/-! ## Section 1: Contiguous Block Partitions, Nested Chains, Ultrametric, & ScaleTree -/

theorem consecutiveBlocks_pairwise :
    ∀ (blocks : List IntervalBlock),
      (∀ C ∈ blocks, C.lo ≤ C.hi) →
      ConsecutiveBlocks blocks →
      blocks.Pairwise (fun A B => A.hi < B.lo)
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | _ :: C₂ :: rest, hle, ⟨h12, hcons⟩ => by
    have hp := consecutiveBlocks_pairwise (C₂ :: rest)
      (fun C hC => hle C (List.mem_cons_of_mem _ hC)) hcons
    refine List.Pairwise.cons (fun B hB => ?_) hp
    rcases List.mem_cons.mp hB with rfl | hBrest
    · omega
    · have h2B := (List.pairwise_cons.mp hp).1 B hBrest
      have hC2 : C₂.lo ≤ C₂.hi := hle C₂ (List.mem_cons_of_mem _ List.mem_cons_self)
      omega

theorem pairwise_blocks_nodup :
    ∀ {blocks : List IntervalBlock},
      (∀ C ∈ blocks, C.lo ≤ C.hi) →
      blocks.Pairwise (fun A B => A.hi < B.lo) →
      blocks.Nodup
  | [], _, _ => List.Pairwise.nil
  | C :: rest, hle, hp => by
    rw [List.pairwise_cons] at hp
    rw [List.nodup_cons]
    refine ⟨fun hmem => ?_,
      pairwise_blocks_nodup (fun X hX => hle X (List.mem_cons_of_mem _ hX)) hp.2⟩
    have hlt := hp.1 C hmem
    have hCle := hle C List.mem_cons_self
    omega

theorem pairwise_blocks_rel :
    ∀ {blocks : List IntervalBlock},
      blocks.Pairwise (fun A B => A.hi < B.lo) →
      ∀ {A B : IntervalBlock}, A ∈ blocks → B ∈ blocks →
        A = B ∨ A.hi < B.lo ∨ B.hi < A.lo
  | [], _, _, _, hA, _ => by cases hA
  | _ :: _, hp, A, B, hA, hB => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hA with rfl | hA' <;> rcases List.mem_cons.mp hB with rfl | hB'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (hp.1 B hB'))
    · exact Or.inr (Or.inr (hp.1 A hA'))
    · exact pairwise_blocks_rel hp.2 hA' hB'

theorem pairwise_blocks_unique {blocks : List IntervalBlock}
    (hp : blocks.Pairwise (fun A B => A.hi < B.lo))
    {A B : IntervalBlock} (hA : A ∈ blocks) (hB : B ∈ blocks)
    {u : ℕ} (huA : A.lo ≤ u ∧ u ≤ A.hi) (huB : B.lo ≤ u ∧ u ≤ B.hi) : A = B := by
  rcases pairwise_blocks_rel hp hA hB with rfl | hlt | hgt
  · rfl
  · omega
  · omega

theorem consecutiveBlocks_append :
    ∀ (xs ys : List IntervalBlock),
      ConsecutiveBlocks xs → ConsecutiveBlocks ys →
      (∀ a b, xs.getLast? = some a → ys.head? = some b → a.hi + 1 = b.lo) →
      ConsecutiveBlocks (xs ++ ys)
  | [], _, _, hys, _ => hys
  | [_], [], _, _, _ => trivial
  | [x], y :: _, _, hys, hlink =>
    ⟨hlink x y rfl rfl, hys⟩
  | _ :: x₂ :: xs, ys, ⟨h12, hxs⟩, hys, hlink =>
    ⟨h12, consecutiveBlocks_append (x₂ :: xs) ys hxs hys hlink⟩

theorem consecutiveBlocks_cover :
    ∀ (blocks : List IntervalBlock) (a b : ℕ),
      blocks ≠ [] →
      (∀ C ∈ blocks, C.lo ≤ C.hi) →
      ConsecutiveBlocks blocks →
      (blocks.head?.map IntervalBlock.lo) = some a →
      (blocks.getLast?.map IntervalBlock.hi) = some b →
      ∀ u, a ≤ u → u ≤ b → ∃ B ∈ blocks, B.lo ≤ u ∧ u ≤ B.hi
  | [], _, _, hne, _, _, _, _, _, _, _ => absurd rfl hne
  | [C], a, b, _, _, _, hhead, hlast, u, hau, hub => by
    simp at hhead hlast
    exact ⟨C, List.mem_singleton_self _, by omega, by omega⟩
  | C₁ :: C₂ :: rest, a, b, _, hle, ⟨h12, hcons⟩, hhead, hlast, u, hau, hub => by
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhead
    by_cases hu1 : u ≤ C₁.hi
    · exact ⟨C₁, List.mem_cons_self, by omega, hu1⟩
    · have hu2 : C₂.lo ≤ u := by omega
      obtain ⟨B, hB, hBlo, hBhi⟩ := consecutiveBlocks_cover (C₂ :: rest) C₂.lo b
        (List.cons_ne_nil _ _)
        (fun C hC => hle C (List.mem_cons_of_mem _ hC))
        hcons rfl hlast u hu2 hub
      exact ⟨B, List.mem_cons_of_mem _ hB, hBlo, hBhi⟩

theorem part_blocks_ne_nil {P : ℕ} {blocks : List IntervalBlock}
    (hP : 1 ≤ P) (hPart : IsContiguousBlockPartition P blocks) : blocks ≠ [] := by
  intro hnil
  subst hnil
  rcases hPart with ⟨_, _, h0⟩
  simp at h0
  omega

theorem part_blocks_pairwise {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks) :
    blocks.Pairwise (fun A B => A.hi < B.lo) :=
  consecutiveBlocks_pairwise blocks (fun C hC => (hPart.1 C hC).2.1) hPart.2.1

theorem part_blocks_nodup {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks) :
    blocks.Nodup :=
  pairwise_blocks_nodup (fun C hC => (hPart.1 C hC).2.1) (part_blocks_pairwise hPart)

theorem part_cover {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks)
    {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) :
    ∃ B ∈ blocks, B.lo ≤ u ∧ u ≤ B.hi := by
  have hP : 1 ≤ P := le_trans hu1 huP
  have hne := part_blocks_ne_nil hP hPart
  rcases hPart with ⟨hbounds, hcons, hhl⟩
  cases hhd : blocks.head? with
  | none => exact absurd (List.head?_eq_none_iff.mp hhd) hne
  | some first =>
    cases hlt : blocks.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hlt) hne
    | some last =>
      rw [hhd, hlt] at hhl
      exact consecutiveBlocks_cover blocks 1 P hne (fun C hC => (hbounds C hC).2.1) hcons
        (by simp [hhd, hhl.1]) (by simp [hlt, hhl.2]) u hu1 huP

theorem blockAt_mem_and_bounds {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks)
    {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) :
    blockAt blocks u ∈ blocks ∧
      (blockAt blocks u).lo ≤ u ∧ u ≤ (blockAt blocks u).hi := by
  obtain ⟨B, hB, hBlo, hBhi⟩ := part_cover hPart hu1 huP
  unfold blockAt
  cases hfind : blocks.find? (fun C => decide (C.lo ≤ u ∧ u ≤ C.hi)) with
  | none =>
    have hnone := (List.find?_eq_none.mp hfind) B hB
    simp [hBlo, hBhi] at hnone
  | some C =>
    have hmem := List.mem_of_find?_eq_some hfind
    have hsat := of_decide_eq_true (List.find?_eq_some_iff_append.mp hfind).1
    exact ⟨hmem, hsat.1, hsat.2⟩

theorem blockAt_eq_iff {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks)
    {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) {B : IntervalBlock} (hB : B ∈ blocks) :
    blockAt blocks u = B ↔ B.lo ≤ u ∧ u ≤ B.hi := by
  obtain ⟨hmem, hlo, hhi⟩ := blockAt_mem_and_bounds hPart hu1 huP
  constructor
  · rintro rfl; exact ⟨hlo, hhi⟩
  · intro ⟨hBlo, hBhi⟩
    exact pairwise_blocks_unique (part_blocks_pairwise hPart) hmem hB ⟨hlo, hhi⟩ ⟨hBlo, hBhi⟩

theorem blockAt_between {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks)
    {a b c : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ P)
    (heq : blockAt blocks a = blockAt blocks c) :
    blockAt blocks a = blockAt blocks b := by
  obtain ⟨hmem, hlo, _⟩ := blockAt_mem_and_bounds hPart ha (by omega)
  obtain ⟨_, _, hhi⟩ := blockAt_mem_and_bounds hPart (by omega) hc
  rw [← heq] at hhi
  exact ((blockAt_eq_iff hPart (by omega) (by omega) hmem).mpr ⟨by omega, by omega⟩).symm

theorem blockAt_hi_lt_lo_of_ne {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks)
    {u v : ℕ} (hu1 : 1 ≤ u) (huv : u ≤ v) (hvP : v ≤ P)
    (hne : blockAt blocks u ≠ blockAt blocks v) :
    (blockAt blocks u).hi < (blockAt blocks v).lo := by
  obtain ⟨hmu, hlou, hhiu⟩ := blockAt_mem_and_bounds hPart hu1 (by omega)
  obtain ⟨hmv, hlov, hhiv⟩ := blockAt_mem_and_bounds hPart (by omega) hvP
  rcases pairwise_blocks_rel (part_blocks_pairwise hPart) hmu hmv with heq | hlt | hgt
  · exact absurd heq hne
  · exact hlt
  · omega

/-! ### `splitIntervalBySize` and `IsNestedPartitionChain` for `scaleTreePartitionChain` -/

theorem splitIntervalBySize_props {P : ℕ} (X : IntervalBlock) (S : ℕ)
    (h1 : 1 ≤ X.lo) (hle : X.lo ≤ X.hi) (hP : X.hi ≤ P) :
    let sub := splitIntervalBySize X S
    sub ≠ [] ∧
    (∀ Y ∈ sub, X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi ∧ 1 ≤ Y.lo ∧ Y.hi ≤ P) ∧
    ConsecutiveBlocks sub ∧
    (sub.head?.map IntervalBlock.lo) = some X.lo ∧
    (sub.getLast?.map IntervalBlock.hi) = some X.hi := by
  dsimp only
  unfold splitIntervalBySize
  by_cases hcond : S = 0 ∨ X.size < 2 * S
  · simp only [hcond, ↓reduceIte]
    refine ⟨List.cons_ne_nil _ _, ?_, trivial, rfl, rfl⟩
    intro Y hY
    rw [List.mem_singleton] at hY
    subst hY
    exact ⟨le_rfl, hle, le_rfl, h1, hP⟩
  · simp only [hcond, ↓reduceIte]
    have hS : 1 ≤ S := by omega
    have h2S : 2 * S ≤ X.size := by omega
    have hXsz : X.size = X.hi - X.lo + 1 := by simp [IntervalBlock.size, hle]
    set K := X.size / S
    have hK2 : 2 ≤ K := (Nat.le_div_iff_mul_le hS).mpr h2S
    have hdiv : S * K + X.size % S = X.size := Nat.div_add_mod X.size S
    have hKS_comm : K * S = S * K := Nat.mul_comm K S
    have hKS : K * S ≤ X.size := by omega
    let mkBlock : ℕ → IntervalBlock := fun idx =>
      if idx + 1 < K then ⟨X.lo + idx * S, X.lo + (idx + 1) * S - 1⟩
      else ⟨X.lo + idx * S, X.hi⟩
    change (List.range K).map mkBlock ≠ [] ∧ _
    have hne : (List.range K).map mkBlock ≠ [] := by
      simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
      omega
    have hmem_bounds : ∀ Y ∈ (List.range K).map mkBlock,
        X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi ∧ 1 ≤ Y.lo ∧ Y.hi ≤ P := by
      intro Y hY
      rw [List.mem_map] at hY
      obtain ⟨idx, hidx, rfl⟩ := hY
      rw [List.mem_range] at hidx
      dsimp [mkBlock]
      by_cases hlt : idx + 1 < K
      · simp only [hlt, ↓reduceIte]
        have hmul : (idx + 1) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
        have hstep : idx * S + S = (idx + 1) * S := by ring
        omega
      · simp only [hlt, ↓reduceIte]
        have hidx_eq : idx = K - 1 := by omega
        subst hidx_eq
        have hmul : (K - 1) * S + S = K * S := by
          have : (K - 1) + 1 = K := by omega
          calc (K - 1) * S + S = ((K - 1) + 1) * S := by ring
            _ = K * S := by rw [this]
        omega
    have hcons : ConsecutiveBlocks ((List.range K).map mkBlock) := by
      suffices ∀ m, m ≤ K → ConsecutiveBlocks ((List.range m).map mkBlock) from this K le_rfl
      intro m
      induction m with
      | zero => intro _; trivial
      | succ m ihm =>
        intro hmK
        rw [List.range_succ, List.map_append, List.map_singleton]
        refine consecutiveBlocks_append _ _ (ihm (by omega)) trivial ?_
        intro a b ha hb
        rw [List.head?_singleton, Option.some.injEq] at hb
        subst hb
        cases m with
        | zero => simp at ha
        | succ m' =>
          have hlast : ((List.range (m' + 1)).map mkBlock).getLast? = some (mkBlock m') := by
            rw [List.range_succ, List.map_append, List.map_singleton,
              List.getLast?_append_of_ne_nil _ (by simp)]
            simp
          rw [hlast, Option.some.injEq] at ha
          subst ha
          have hm1 : m' + 1 < K := by omega
          have hposS : 1 ≤ (m' + 1) * S := Nat.mul_pos (by omega) hS
          dsimp [mkBlock]
          simp only [hm1, ↓reduceIte]
          by_cases hm2 : m' + 1 + 1 < K
          · simp only [hm2, ↓reduceIte]; omega
          · simp only [hm2, ↓reduceIte]; omega
    have hhead : (((List.range K).map mkBlock).head?.map IntervalBlock.lo) = some X.lo := by
      cases hK_eq : K with
      | zero => omega
      | succ k' =>
        rw [List.range_succ_eq_map, List.map_cons, List.head?_cons, Option.map_some]
        dsimp [mkBlock]
        have h1K : 0 + 1 < K := by omega
        simp [h1K]
    have hlast : (((List.range K).map mkBlock).getLast?.map IntervalBlock.hi) = some X.hi := by
      cases hK_eq : K with
      | zero => omega
      | succ k' =>
        rw [List.range_succ, List.map_append, List.map_singleton,
          List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton, Option.map_some]
        dsimp [mkBlock]
        have hnlt : ¬ (k' + 1 < K) := by omega
        simp [hnlt]
    exact ⟨hne, hmem_bounds, hcons, hhead, hlast⟩

theorem flatMap_preserves_partition {P : ℕ} (hP : 1 ≤ P)
    {blocks : List IntervalBlock} (hPart : IsContiguousBlockPartition P blocks)
    (S : ℕ) :
    IsContiguousBlockPartition P (blocks.flatMap (fun X => splitIntervalBySize X S)) ∧
    (∀ Y ∈ blocks.flatMap (fun X => splitIntervalBySize X S),
      ∃ X ∈ blocks, X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi) := by
  have hsub : ∀ Y ∈ blocks.flatMap (fun X => splitIntervalBySize X S),
      ∃ X ∈ blocks, X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi := by
    intro Y hY
    rw [List.mem_flatMap] at hY
    obtain ⟨X, hX, hYX⟩ := hY
    obtain ⟨h1, hle, hhiP⟩ := hPart.1 X hX
    obtain ⟨_, hb, _, _, _⟩ := splitIntervalBySize_props X S h1 hle hhiP
    obtain ⟨hXYlo, _, hYXhi, _, _⟩ := hb Y hYX
    exact ⟨X, hX, hXYlo, hYXhi⟩
  refine ⟨⟨?_, ?_, ?_⟩, hsub⟩
  · intro Y hY
    rw [List.mem_flatMap] at hY
    obtain ⟨X, hX, hYX⟩ := hY
    obtain ⟨h1, hle, hhiP⟩ := hPart.1 X hX
    obtain ⟨_, hb, _, _, _⟩ := splitIntervalBySize_props X S h1 hle hhiP
    obtain ⟨_, hYle, _, hY1, hYP⟩ := hb Y hYX
    exact ⟨hY1, hYle, hYP⟩
  · rcases hPart with ⟨hbounds, hcons, hhl⟩
    clear hsub hP hhl
    induction blocks with
    | nil => trivial
    | cons X rest ih =>
      simp only [List.flatMap_cons]
      obtain ⟨hX1, hXle, hXP⟩ := hbounds X List.mem_cons_self
      obtain ⟨_, _, hXcons, _, hXlast⟩ := splitIntervalBySize_props X S hX1 hXle hXP
      cases rest with
      | nil => simpa using hXcons
      | cons X₂ rest' =>
        rcases hcons with ⟨hlink, hcons'⟩
        have hrest := ih (fun C hC => hbounds C (List.mem_cons_of_mem _ hC)) hcons'
        obtain ⟨hX2_1, hX2_le, hX2_P⟩ := hbounds X₂ (List.mem_cons_of_mem _ List.mem_cons_self)
        obtain ⟨hX2_ne, _, _, hX2_head, _⟩ := splitIntervalBySize_props X₂ S hX2_1 hX2_le hX2_P
        refine consecutiveBlocks_append _ _ hXcons hrest ?_
        intro a b ha hb
        simp only [List.flatMap_cons] at hb
        rw [List.head?_append_of_ne_nil _ hX2_ne] at hb
        rw [ha] at hXlast
        rw [hb] at hX2_head
        simp only [Option.map_some, Option.some.injEq] at hXlast hX2_head
        omega
  · have hne := part_blocks_ne_nil hP hPart
    rcases hPart with ⟨hbounds, _, hhl⟩
    cases hhd : blocks.head? with
    | none => exact absurd (List.head?_eq_none_iff.mp hhd) hne
    | some first =>
      cases hlt : blocks.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp hlt) hne
      | some last =>
        rw [hhd, hlt] at hhl
        have hf_mem : first ∈ blocks := List.mem_of_head? hhd
        have hl_mem : last ∈ blocks := List.mem_of_getLast? hlt
        obtain ⟨hf1, hfle, hfP⟩ := hbounds first hf_mem
        obtain ⟨hl1, hlle, hlP⟩ := hbounds last hl_mem
        obtain ⟨hf_ne, _, _, hf_hd, _⟩ := splitIntervalBySize_props first S hf1 hfle hfP
        obtain ⟨hl_ne, _, _, _, hl_lt⟩ := splitIntervalBySize_props last S hl1 hlle hlP
        have h_head_fm :
            (blocks.flatMap (fun X => splitIntervalBySize X S)).head? =
              (splitIntervalBySize first S).head? := by
          cases blocks with
          | nil => simp at hhd
          | cons b bs =>
            simp only [List.head?_cons, Option.some.injEq] at hhd
            subst hhd
            simp [List.flatMap_cons, List.head?_append_of_ne_nil _ hf_ne]
        have h_last_fm :
            (blocks.flatMap (fun X => splitIntervalBySize X S)).getLast? =
              (splitIntervalBySize last S).getLast? := by
          have hrev := List.dropLast_append_getLast hne
          have hlast_eq : blocks.getLast hne = last := by
            rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at hlt
            exact hlt
          rw [← hrev, hlast_eq, List.flatMap_append, List.flatMap_singleton,
            List.getLast?_append_of_ne_nil _ hl_ne]
        rw [h_head_fm, h_last_fm]
        cases h1 : (splitIntervalBySize first S).head? with
        | none => exact absurd (List.head?_eq_none_iff.mp h1) hf_ne
        | some f0 =>
          cases h2 : (splitIntervalBySize last S).getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.mp h2) hl_ne
          | some l0 =>
            rw [h1] at hf_hd
            rw [h2] at hl_lt
            simp only [Option.map_some, Option.some.injEq] at hf_hd hl_lt
            exact ⟨hf_hd.trans hhl.1, hl_lt.trans hhl.2⟩

theorem scaleTreePartitionChain_isNested (T : ScaleTree) (P M : ℕ) (hP : 1 ≤ P) :
    IsNestedPartitionChain P (scaleTreePartitionChain T P M) := by
  have hPne : P ≠ 0 := by omega
  have h0_part : IsContiguousBlockPartition P (scaleTreePartitionLevel T P 0) := by
    simp only [scaleTreePartitionLevel, hPne, ↓reduceIte]
    refine ⟨?_, trivial, rfl, rfl⟩
    intro C hC
    rw [List.mem_singleton] at hC
    subst hC
    exact ⟨le_rfl, hP, le_rfl⟩
  have hAll : ∀ k : ℕ, IsContiguousBlockPartition P (scaleTreePartitionLevel T P k) ∧
      (∀ Y ∈ scaleTreePartitionLevel T P (k + 1),
        ∃ X ∈ scaleTreePartitionLevel T P k, X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi) := by
    intro k
    induction k with
    | zero =>
      exact ⟨h0_part, (flatMap_preserves_partition hP h0_part (scaleS T P 1)).2⟩
    | succ k ih =>
      have hstep1 := (flatMap_preserves_partition hP ih.1 (scaleS T P (k + 1))).1
      exact ⟨hstep1, (flatMap_preserves_partition hP hstep1 (scaleS T P (k + 2))).2⟩
  refine ⟨hP, ?_, fun ℓ => (hAll ℓ.val).1, fun ℓ => (hAll ℓ.val).2⟩
  change scaleTreePartitionLevel T P 0 = [⟨1, P⟩]
  simp [scaleTreePartitionLevel, hPne]

/-! ### Nested Chain & `partSepScale` Ultrametric Lemmas -/

theorem nested_enclosing_le {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hk : k₁.val ≤ k₂.val)
    {Q : IntervalBlock} (hQ : Q ∈ chain k₂) :
    ∃ X ∈ chain k₁, X.lo ≤ Q.lo ∧ Q.hi ≤ X.hi := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d generalizing k₂ Q with
  | zero =>
    have heq : k₁ = k₂ := Fin.ext (by omega)
    subst heq
    exact ⟨Q, hQ, le_rfl, le_rfl⟩
  | succ d ih =>
    have hk2_lt : k₂.val < M + 1 := k₂.is_lt
    have hk_lt : k₁.val + d < M := by omega
    let ℓ : Fin M := ⟨k₁.val + d, hk_lt⟩
    have hsucc : k₂ = ℓ.succ := Fin.ext (by dsimp [ℓ]; omega)
    subst hsucc
    obtain ⟨Y, hY, hYlo, hQhi⟩ := hChain.2.2.2 ℓ Q hQ
    obtain ⟨X, hX, hXlo, hYhi⟩ := ih (k₂ := ℓ.castSucc) hY (by dsimp [ℓ])
    exact ⟨X, hX, le_trans hXlo hYlo, le_trans hQhi hYhi⟩

theorem nested_blockAt_sub {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hk : k₁.val ≤ k₂.val)
    {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) :
    (blockAt (chain k₁) u).lo ≤ (blockAt (chain k₂) u).lo ∧
      (blockAt (chain k₂) u).hi ≤ (blockAt (chain k₁) u).hi := by
  obtain ⟨hm2, hlo2, hhi2⟩ := blockAt_mem_and_bounds (hChain.2.2.1 k₂) hu1 huP
  obtain ⟨X, hX, hXlo, hXhi⟩ := nested_enclosing_le hChain hk hm2
  have hXeq : blockAt (chain k₁) u = X :=
    (blockAt_eq_iff (hChain.2.2.1 k₁) hu1 huP hX).mpr ⟨le_trans hXlo hlo2, le_trans hhi2 hXhi⟩
  rw [hXeq]
  exact ⟨hXlo, hXhi⟩

theorem nested_blockAt_eq_mono {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hk : k₁.val ≤ k₂.val)
    {u v : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P)
    (heq : blockAt (chain k₂) u = blockAt (chain k₂) v) :
    blockAt (chain k₁) u = blockAt (chain k₁) v := by
  obtain ⟨hm2, hlo2u, hhi2u⟩ := blockAt_mem_and_bounds (hChain.2.2.1 k₂) hu1 huP
  obtain ⟨_, hlo2v, hhi2v⟩ := blockAt_mem_and_bounds (hChain.2.2.1 k₂) hv1 hvP
  rw [← heq] at hlo2v hhi2v
  obtain ⟨X, hX, hXlo, hXhi⟩ := nested_enclosing_le hChain hk hm2
  have huX := (blockAt_eq_iff (hChain.2.2.1 k₁) hu1 huP hX).mpr ⟨le_trans hXlo hlo2u, le_trans hhi2u hXhi⟩
  have hvX := (blockAt_eq_iff (hChain.2.2.1 k₁) hv1 hvP hX).mpr ⟨le_trans hXlo hlo2v, le_trans hhi2v hXhi⟩
  exact huX.trans hvX.symm

theorem finRange_find_before {M : ℕ} {p : Fin M → Bool} {ℓ₀ : Fin M}
    (hfind : (List.finRange M).find? p = some ℓ₀) {j : Fin M} (hj : j < ℓ₀) :
    p j = false := by
  rw [List.find?_eq_some_iff_append] at hfind
  obtain ⟨_, as, bs, heq, hall⟩ := hfind
  have hp : (List.finRange M).Pairwise (· < ·) := List.pairwise_lt_finRange M
  rw [heq, List.pairwise_append] at hp
  rcases hp with ⟨_, hp_cons, _⟩
  rw [List.pairwise_cons] at hp_cons
  have hjmem : j ∈ as ++ ℓ₀ :: bs := heq ▸ List.mem_finRange j
  rw [List.mem_append, List.mem_cons] at hjmem
  rcases hjmem with hjas | rfl | hjbs
  · simpa using hall j hjas
  · exact absurd hj (lt_irrefl _)
  · exact absurd (hp_cons.1 j hjbs) (not_lt_of_gt hj)

theorem lt_partSepScale_iff {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {u v : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P)
    (k : Fin (M + 1)) :
    k.val < partSepScale P chain u v ↔ blockAt (chain k) u = blockAt (chain k) v := by
  unfold partSepScale
  have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
  simp only [hcond, ↓reduceIte]
  have hk0 : blockAt (chain 0) u = blockAt (chain 0) v := by
    have h0mem : (⟨1, P⟩ : IntervalBlock) ∈ chain 0 := by rw [hChain.2.1]; simp
    have hu0 := (blockAt_eq_iff (hChain.2.2.1 0) hu1 huP h0mem).mpr ⟨hu1, huP⟩
    have hv0 := (blockAt_eq_iff (hChain.2.2.1 0) hv1 hvP h0mem).mpr ⟨hv1, hvP⟩
    exact hu0.trans hv0.symm
  cases hfind : (List.finRange M).find? (fun ℓ : Fin M =>
      decide (blockAt (chain ℓ.succ) u ≠ blockAt (chain ℓ.succ) v)) with
  | none =>
    simp only [Fin.is_lt, true_iff]
    rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
    · exact hk0
    · have hnone := (List.find?_eq_none.mp hfind) j (List.mem_finRange j)
      simpa using hnone
  | some ℓ₀ =>
    dsimp only
    constructor
    · intro hlt
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
      · exact hk0
      · have hjlt : j < ℓ₀ := by
          simp only [Fin.val_succ] at hlt
          exact Fin.lt_def.mpr (by omega)
        have hfalse := finRange_find_before hfind hjlt
        simpa using hfalse
    · intro heq
      by_contra hnlt
      have hle : ℓ₀.succ.val ≤ k.val := by simp [Fin.val_succ]; omega
      have heq0 := nested_blockAt_eq_mono hChain hle hu1 huP hv1 hvP heq
      have hsome := of_decide_eq_true (List.find?_eq_some_iff_append.mp hfind).1
      exact hsome heq0

theorem partSepScale_bounds {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    {u v : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P) :
    1 ≤ partSepScale P chain u v ∧ partSepScale P chain u v ≤ M + 1 := by
  unfold partSepScale
  have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
  simp only [hcond, ↓reduceIte]
  split <;> omega

theorem partSepScale_symm {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) (u v : ℕ) :
    partSepScale P chain u v = partSepScale P chain v u := by
  by_cases hbad : P < u ∨ P < v ∨ u = 0 ∨ v = 0
  · unfold partSepScale
    have hbad' : P < v ∨ P < u ∨ v = 0 ∨ u = 0 := by omega
    simp [hbad, hbad']
  · have hu1 : 1 ≤ u := by omega
    have huP : u ≤ P := by omega
    have hv1 : 1 ≤ v := by omega
    have hvP : v ≤ P := by omega
    obtain ⟨_, hle1⟩ := partSepScale_bounds (chain := chain) hu1 huP hv1 hvP
    obtain ⟨_, hle2⟩ := partSepScale_bounds (chain := chain) hv1 hvP hu1 huP
    have hiff : ∀ k : ℕ, k ≤ M → (k < partSepScale P chain u v ↔ k < partSepScale P chain v u) := by
      intro k hk
      let kf : Fin (M + 1) := ⟨k, by omega⟩
      rw [lt_partSepScale_iff hChain hu1 huP hv1 hvP kf,
        lt_partSepScale_iff hChain hv1 hvP hu1 huP kf, eq_comm]
    by_contra hne
    rcases lt_trichotomy (partSepScale P chain u v) (partSepScale P chain v u) with hlt | heq | hgt
    · have hkM : partSepScale P chain u v ≤ M := by omega
      exact (lt_irrefl _) ((hiff _ hkM).mpr hlt)
    · exact hne heq
    · have hkM : partSepScale P chain v u ≤ M := by omega
      exact (lt_irrefl _) ((hiff _ hkM).mp hgt)

theorem partSepScale_ultrametric_ord {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {a b c : ℕ} (ha1 : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    partSepScale P chain a c = min (partSepScale P chain a b) (partSepScale P chain b c) := by
  by_cases hcP : P < c
  · have hc1 : P < a ∨ P < c ∨ a = 0 ∨ c = 0 := Or.inr (Or.inl hcP)
    have hc2 : P < b ∨ P < c ∨ b = 0 ∨ c = 0 := Or.inr (Or.inl hcP)
    have h1 : partSepScale P chain a c = 0 := by unfold partSepScale; simp [hc1]
    have h2 : partSepScale P chain b c = 0 := by unfold partSepScale; simp [hc2]
    rw [h1, h2, Nat.min_zero]
  · have hc_le : c ≤ P := by omega
    have haP : a ≤ P := by omega
    have hb1 : 1 ≤ b := by omega
    have hbP : b ≤ P := by omega
    have hc1 : 1 ≤ c := by omega
    obtain ⟨_, hac_le⟩ := partSepScale_bounds (chain := chain) ha1 haP hc1 hc_le
    obtain ⟨_, hab_le⟩ := partSepScale_bounds (chain := chain) ha1 haP hb1 hbP
    obtain ⟨_, hbc_le⟩ := partSepScale_bounds (chain := chain) hb1 hbP hc1 hc_le
    have hmin_le : min (partSepScale P chain a b) (partSepScale P chain b c) ≤ M + 1 := by omega
    have hiff : ∀ k : ℕ, k ≤ M →
        (k < partSepScale P chain a c ↔
          k < min (partSepScale P chain a b) (partSepScale P chain b c)) := by
      intro k hk
      let kf : Fin (M + 1) := ⟨k, by omega⟩
      rw [Nat.lt_min, lt_partSepScale_iff hChain ha1 haP hc1 hc_le kf,
        lt_partSepScale_iff hChain ha1 haP hb1 hbP kf,
        lt_partSepScale_iff hChain hb1 hbP hc1 hc_le kf]
      constructor
      · intro hac_eq
        have hab_eq := blockAt_between (hChain.2.2.1 kf) ha1 hab hbc hc_le hac_eq
        exact ⟨hab_eq, hab_eq.symm.trans hac_eq⟩
      · rintro ⟨hab_eq, hbc_eq⟩
        exact hab_eq.trans hbc_eq
    by_contra hne
    rcases lt_trichotomy (partSepScale P chain a c)
        (min (partSepScale P chain a b) (partSepScale P chain b c)) with hlt | heq | hgt
    · exact (lt_irrefl _) ((hiff _ (by omega)).mpr hlt)
    · exact hne heq
    · exact (lt_irrefl _) ((hiff _ (by omega)).mp hgt)

theorem lt_partSepScale_iff_le_hi {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {u z : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) (huz : u ≤ z) (k : Fin (M + 1)) :
    k.val < partSepScale P chain u z ↔ z ≤ (blockAt (chain k) u).hi := by
  have hPart := hChain.2.2.1 k
  obtain ⟨hmu, hlou, _⟩ := blockAt_mem_and_bounds hPart hu1 huP
  have hhiP : (blockAt (chain k) u).hi ≤ P := (hPart.1 _ hmu).2.2
  constructor
  · intro hlt
    have hzP : z ≤ P := by
      by_contra hgt
      have hbad : P < u ∨ P < z ∨ u = 0 ∨ z = 0 := by omega
      have h0 : partSepScale P chain u z = 0 := by unfold partSepScale; simp [hbad]
      omega
    have heq := (lt_partSepScale_iff hChain hu1 huP (by omega) hzP k).mp hlt
    exact ((blockAt_eq_iff hPart (by omega) hzP hmu).mp heq.symm).2
  · intro hz_le
    have hzP : z ≤ P := le_trans hz_le hhiP
    rw [lt_partSepScale_iff hChain hu1 huP (by omega) hzP k]
    exact ((blockAt_eq_iff hPart (by omega) hzP hmu).mpr ⟨le_trans hlou huz, hz_le⟩).symm

theorem partSepScale_le_iff_hi_lt {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {u z : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) (huz : u ≤ z) (k : Fin (M + 1)) :
    partSepScale P chain u z ≤ k.val ↔ (blockAt (chain k) u).hi < z := by
  have h := lt_partSepScale_iff_le_hi hChain hu1 huP huz k
  omega

theorem lt_partSepScale_iff_lo_le {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {s x : ℕ} (hs1 : 1 ≤ s) (hsx : s ≤ x) (hxP : x ≤ P) (k : Fin (M + 1)) :
    k.val < partSepScale P chain s x ↔ (blockAt (chain k) x).lo ≤ s := by
  have hPart := hChain.2.2.1 k
  obtain ⟨hmx, _, hhix⟩ := blockAt_mem_and_bounds hPart (by omega) hxP
  constructor
  · intro hlt
    have heq := (lt_partSepScale_iff hChain hs1 (by omega) (by omega) hxP k).mp hlt
    exact ((blockAt_eq_iff hPart hs1 (by omega) hmx).mp heq).1
  · intro hlo_le
    rw [lt_partSepScale_iff hChain hs1 (by omega) (by omega) hxP k]
    exact (blockAt_eq_iff hPart hs1 (by omega) hmx).mpr ⟨hlo_le, le_trans hsx hhix⟩

theorem partSepScale_le_iff_lt_lo {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {s x : ℕ} (hs1 : 1 ≤ s) (hsx : s ≤ x) (hxP : x ≤ P) (k : Fin (M + 1)) :
    partSepScale P chain s x ≤ k.val ↔ s < (blockAt (chain k) x).lo := by
  have h := lt_partSepScale_iff_lo_le hChain hs1 hsx hxP k
  omega

/-! ### `childSubblocks`, `subblock1`, and `subblockIndex1` Lemmas -/

theorem childSubblocks_pairwise {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) (ℓ : Fin M) (X : IntervalBlock) :
    (childSubblocks (chain ℓ.succ) X).Pairwise (fun A B => A.hi < B.lo) :=
  (part_blocks_pairwise (hChain.2.2.1 ℓ.succ)).filter _

theorem blockAt_succ_mem_childSubblocks {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) (ℓ : Fin M)
    {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {w : ℕ} (hw : w ∈ X.toFinset) :
    blockAt (chain ℓ.succ) w ∈ childSubblocks (chain ℓ.succ) X := by
  rw [IntervalBlock.toFinset, Finset.mem_Icc] at hw
  obtain ⟨hX1, _, hXP⟩ := (hChain.2.2.1 ℓ.castSucc).1 X hX
  have hw1 : 1 ≤ w := le_trans hX1 hw.1
  have hwP : w ≤ P := le_trans hw.2 hXP
  obtain ⟨hmw, _, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 ℓ.succ) hw1 hwP
  have hXeq : blockAt (chain ℓ.castSucc) w = X :=
    (blockAt_eq_iff (hChain.2.2.1 ℓ.castSucc) hw1 hwP hX).mpr hw
  have hsub := nested_blockAt_sub hChain (k₁ := ℓ.castSucc) (k₂ := ℓ.succ)
    (Nat.le_succ ℓ.val) hw1 hwP
  rw [hXeq] at hsub
  unfold childSubblocks
  rw [List.mem_filter]
  exact ⟨hmw, decide_eq_true ⟨hsub.1, hsub.2⟩⟩

theorem subblock1_eq_getElem {subs : List IntervalBlock} {c : ℕ}
    (hc1 : 1 ≤ c) (hcL : c ≤ subs.length) :
    subblock1 subs c = subs[c - 1]'(by omega) := by
  unfold subblock1
  have hc0 : c ≠ 0 := by omega
  have hlt : c - 1 < subs.length := by omega
  simp only [hc0, ↓reduceIte]
  rw [List.getElem?_eq_getElem hlt]
  rfl

theorem subblock1_hi_lt_lo {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) (ℓ : Fin M) (X : IntervalBlock)
    {c₁ c₂ : ℕ} (hc1 : 1 ≤ c₁) (hlt : c₁ < c₂)
    (hc2 : c₂ ≤ (childSubblocks (chain ℓ.succ) X).length) :
    let subs := childSubblocks (chain ℓ.succ) X
    (subblock1 subs c₁).hi < (subblock1 subs c₂).lo := by
  dsimp only
  rw [subblock1_eq_getElem hc1 (by omega), subblock1_eq_getElem (by omega) hc2]
  exact (List.pairwise_iff_getElem.mp (childSubblocks_pairwise hChain ℓ X))
    (c₁ - 1) (c₂ - 1) (by omega) (by omega) (by omega)

theorem subblockIndex1_spec {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) (ℓ : Fin M)
    {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {w : ℕ} (hw : w ∈ X.toFinset) :
    let subs := childSubblocks (chain ℓ.succ) X
    1 ≤ subblockIndex1 subs w ∧
      subblockIndex1 subs w ≤ subs.length ∧
      subblock1 subs (subblockIndex1 subs w) = blockAt (chain ℓ.succ) w ∧
      w ∈ (subblock1 subs (subblockIndex1 subs w)).toFinset := by
  dsimp only
  set subs := childSubblocks (chain ℓ.succ) X
  have hmem : blockAt (chain ℓ.succ) w ∈ subs := blockAt_succ_mem_childSubblocks hChain ℓ hX hw
  rw [IntervalBlock.toFinset, Finset.mem_Icc] at hw
  obtain ⟨hX1, _, hXP⟩ := (hChain.2.2.1 ℓ.castSucc).1 X hX
  obtain ⟨_, hlow, hhiw⟩ := blockAt_mem_and_bounds (hChain.2.2.1 ℓ.succ)
    (le_trans hX1 hw.1) (le_trans hw.2 hXP)
  unfold subblockIndex1
  cases hfind : subs.findIdx? (fun S => decide (S.lo ≤ w ∧ w ≤ S.hi)) with
  | none =>
    have hnone := (List.findIdx?_eq_none_iff.mp hfind) (blockAt (chain ℓ.succ) w) hmem
    simp [hlow, hhiw] at hnone
  | some idx =>
    dsimp only
    rw [List.findIdx?_eq_some_iff_findIdx_eq] at hfind
    obtain ⟨hidx_lt, rfl⟩ := hfind
    set i0 := subs.findIdx (fun S => decide (S.lo ≤ w ∧ w ≤ S.hi))
    have hi0_lt : i0 < subs.length := hidx_lt
    have hsat : subs[i0].lo ≤ w ∧ w ≤ subs[i0].hi :=
      of_decide_eq_true (List.findIdx_getElem (w := hi0_lt))
    have hsub_eq : subs[i0] = blockAt (chain ℓ.succ) w :=
      pairwise_blocks_unique (childSubblocks_pairwise hChain ℓ X)
        (List.getElem_mem hi0_lt) hmem hsat ⟨hlow, hhiw⟩
    have hs1 : subblock1 subs (i0 + 1) = subs[i0] := by
      rw [subblock1_eq_getElem (by omega) (by omega)]
      simp
    refine ⟨by omega, by omega, hs1.trans hsub_eq, ?_⟩
    rw [hs1, IntervalBlock.toFinset, Finset.mem_Icc]
    exact hsat

theorem mem_subblock1_iff {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) (ℓ : Fin M)
    {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {c : ℕ} (hc1 : 1 ≤ c) (hcL : c ≤ (childSubblocks (chain ℓ.succ) X).length)
    {w : ℕ} :
    let subs := childSubblocks (chain ℓ.succ) X
    w ∈ (subblock1 subs c).toFinset ↔
      w ∈ X.toFinset ∧ subblockIndex1 subs w = c := by
  dsimp only
  set subs := childSubblocks (chain ℓ.succ) X
  have hSc_mem : subblock1 subs c ∈ subs := by
    rw [subblock1_eq_getElem hc1 hcL]
    exact List.getElem_mem _
  have hSc_filt := List.mem_filter.mp hSc_mem
  have hSc_bounds := of_decide_eq_true hSc_filt.2
  constructor
  · intro hw
    rw [IntervalBlock.toFinset, Finset.mem_Icc] at hw
    have hwX : w ∈ X.toFinset := by
      rw [IntervalBlock.toFinset, Finset.mem_Icc]
      exact ⟨le_trans hSc_bounds.1 hw.1, le_trans hw.2 hSc_bounds.2⟩
    have hspec := subblockIndex1_spec hChain ℓ hX hwX
    dsimp only at hspec
    obtain ⟨hi1, hiL, _, hwi⟩ := hspec
    rw [IntervalBlock.toFinset, Finset.mem_Icc] at hwi
    refine ⟨hwX, ?_⟩
    have heq_blk : subblock1 subs (subblockIndex1 subs w) = subblock1 subs c :=
      pairwise_blocks_unique (childSubblocks_pairwise hChain ℓ X)
        (by rw [subblock1_eq_getElem hi1 hiL]; exact List.getElem_mem _) hSc_mem hwi hw
    by_contra hne
    rcases lt_trichotomy (subblockIndex1 subs w) c with hlt | heq | hgt
    · have hlt_blk := subblock1_hi_lt_lo hChain ℓ X hi1 hlt hcL
      dsimp only at hlt_blk
      change (subblock1 subs (subblockIndex1 subs w)).hi < (subblock1 subs c).lo at hlt_blk
      rw [heq_blk] at hlt_blk
      omega
    · exact hne heq
    · have hgt_blk := subblock1_hi_lt_lo hChain ℓ X hc1 hgt hiL
      dsimp only at hgt_blk
      change (subblock1 subs c).hi < (subblock1 subs (subblockIndex1 subs w)).lo at hgt_blk
      rw [heq_blk] at hgt_blk
      omega
  · rintro ⟨hwX, rfl⟩
    exact (subblockIndex1_spec hChain ℓ hX hwX).2.2.2

/-! ### `ScaleTree` LCA, Child Subtrees, `mStart` / `mEnd`, and `sigmaScaleTree` -/

theorem range'_pairwise_lt :
    ∀ (a n : ℕ), (List.range' a n).Pairwise (· < ·)
  | _, 0 => List.Pairwise.nil
  | a, n + 1 => by
    rw [List.range'_succ, List.pairwise_cons]
    refine ⟨fun x hx => ?_, range'_pairwise_lt (a + 1) n⟩
    rw [List.mem_range'] at hx
    omega

mutual
  theorem leafEntries_iff_subtreeAtAddr :
      ∀ (T : ScaleTree) (s : ℕ) (addr : List ℕ),
        (s, addr) ∈ T.leafEntries ↔ subtreeAtAddr T addr = some (.leaf s)
    | .leaf _, _, [] => by
      simp [ScaleTree.leafEntries, subtreeAtAddr, eq_comm]
    | .leaf _, _, _ :: _ => by
      simp [ScaleTree.leafEntries, subtreeAtAddr]
    | .internal cs, s, [] => by
      simp only [ScaleTree.leafEntries, subtreeAtAddr]
      exact ⟨fun h => absurd h (leafEntriesChildren_ne_nil 1 cs s), fun h => by cases h⟩
    | .internal cs, s, c :: rest => by
      simp only [ScaleTree.leafEntries, subtreeAtAddr]
      rw [leafEntriesChildren_iff 1 cs s c rest]
      by_cases hc0 : c = 0
      · subst hc0
        simp only [↓reduceIte]
        exact ⟨fun ⟨_, _, hc, _⟩ => by omega, fun h => by cases h⟩
      · simp only [hc0, ↓reduceIte]
        cases hget : cs[c - 1]? with
        | none =>
          constructor
          · rintro ⟨i, hi, hc_eq, _⟩
            have hci : c - 1 = i := by omega
            rw [hci, List.getElem?_eq_getElem hi] at hget
            cases hget
          · intro h; cases h
        | some child =>
          rw [List.getElem?_eq_some_iff] at hget
          obtain ⟨hlt, hchild⟩ := hget
          rw [← hchild, ← leafEntries_iff_subtreeAtAddr cs[c - 1] s rest]
          constructor
          · rintro ⟨i, _, hc_eq, hmem⟩
            have hci : c - 1 = i := by omega
            simpa [hci] using hmem
          · intro hmem
            exact ⟨c - 1, hlt, by omega, hmem⟩

  theorem leafEntriesChildren_ne_nil :
      ∀ (c₀ : ℕ) (cs : List ScaleTree) (s : ℕ),
        (s, []) ∉ ScaleTree.leafEntriesChildren c₀ cs
    | _, [], _, h => by simp [ScaleTree.leafEntriesChildren] at h
    | c₀, _ :: cs, s, h => by
      simp only [ScaleTree.leafEntriesChildren, List.mem_append, List.mem_map] at h
      rcases h with ⟨⟨_, _⟩, _, heq⟩ | hrest
      · simp at heq
      · exact leafEntriesChildren_ne_nil (c₀ + 1) cs s hrest

  theorem leafEntriesChildren_iff :
      ∀ (c₀ : ℕ) (cs : List ScaleTree) (s c : ℕ) (rest : List ℕ),
        (s, c :: rest) ∈ ScaleTree.leafEntriesChildren c₀ cs ↔
          ∃ (i : ℕ) (hi : i < cs.length), c = c₀ + i ∧ (s, rest) ∈ cs[i].leafEntries
    | _, [], _, _, _ => by simp [ScaleTree.leafEntriesChildren]
    | c₀, _ :: cs, s, c, rest => by
      simp only [ScaleTree.leafEntriesChildren, List.mem_append, List.mem_map]
      rw [leafEntriesChildren_iff (c₀ + 1) cs s c rest]
      constructor
      · rintro (⟨⟨_, _⟩, hmem, heq⟩ | ⟨i, hi, hc_eq, hmem⟩)
        · simp only [Prod.mk.injEq, List.cons.injEq] at heq
          rcases heq with ⟨rfl, rfl, rfl⟩
          exact ⟨0, Nat.zero_lt_succ _, by omega, hmem⟩
        · exact ⟨i + 1, Nat.succ_lt_succ hi, by omega, hmem⟩
      · rintro ⟨i, hi, rfl, hmem⟩
        cases i with
        | zero =>
          exact Or.inl ⟨(s, rest), hmem, by simp⟩
        | succ i' =>
          have hi' : i' < cs.length := Nat.lt_of_succ_lt_succ hi
          exact Or.inr ⟨i', hi', by omega, hmem⟩
end

mutual
  theorem internalAddrList_iff_subtreeAtAddr :
      ∀ (T : ScaleTree) (ν : List ℕ),
        ν ∈ T.internalAddrList ↔ ∃ cs, subtreeAtAddr T ν = some (.internal cs)
    | .leaf _, [] => by simp [ScaleTree.internalAddrList, subtreeAtAddr]
    | .leaf _, _ :: _ => by simp [ScaleTree.internalAddrList, subtreeAtAddr]
    | .internal _, [] => by simp [ScaleTree.internalAddrList, subtreeAtAddr]
    | .internal cs, c :: rest => by
      simp only [ScaleTree.internalAddrList, List.mem_cons, reduceCtorEq, false_or, subtreeAtAddr]
      rw [internalAddrChildren_iff 1 cs c rest]
      by_cases hc0 : c = 0
      · subst hc0
        simp only [↓reduceIte]
        exact ⟨fun ⟨_, _, hc, _⟩ => by omega, fun ⟨_, h⟩ => by cases h⟩
      · simp only [hc0, ↓reduceIte]
        cases hget : cs[c - 1]? with
        | none =>
          constructor
          · rintro ⟨i, hi, hc_eq, _⟩
            have hci : c - 1 = i := by omega
            rw [hci, List.getElem?_eq_getElem hi] at hget
            cases hget
          · rintro ⟨_, h⟩; cases h
        | some child =>
          rw [List.getElem?_eq_some_iff] at hget
          obtain ⟨hlt, hchild⟩ := hget
          rw [← hchild, ← internalAddrList_iff_subtreeAtAddr cs[c - 1] rest]
          constructor
          · rintro ⟨i, _, hc_eq, hmem⟩
            have hci : c - 1 = i := by omega
            simpa [hci] using hmem
          · intro hmem
            exact ⟨c - 1, hlt, by omega, hmem⟩

  theorem internalAddrChildren_iff :
      ∀ (c₀ : ℕ) (cs : List ScaleTree) (c : ℕ) (rest : List ℕ),
        (c :: rest) ∈ ScaleTree.internalAddrChildren c₀ cs ↔
          ∃ (i : ℕ) (hi : i < cs.length), c = c₀ + i ∧ rest ∈ cs[i].internalAddrList
    | _, [], _, _ => by simp [ScaleTree.internalAddrChildren]
    | c₀, _ :: cs, c, rest => by
      simp only [ScaleTree.internalAddrChildren, List.mem_append, List.mem_map]
      rw [internalAddrChildren_iff (c₀ + 1) cs c rest]
      constructor
      · rintro (⟨_, hmem, heq⟩ | ⟨i, hi, hc_eq, hmem⟩)
        · simp only [List.cons.injEq] at heq
          rcases heq with ⟨rfl, rfl⟩
          exact ⟨0, Nat.zero_lt_succ _, by omega, hmem⟩
        · exact ⟨i + 1, Nat.succ_lt_succ hi, by omega, hmem⟩
      · rintro ⟨i, hi, rfl, hmem⟩
        cases i with
        | zero => exact Or.inl ⟨rest, hmem, by simp⟩
        | succ i' => exact Or.inr ⟨i', Nat.lt_of_succ_lt_succ hi, by omega, hmem⟩
end

theorem subtreeAtAddr_append :
    ∀ (T : ScaleTree) (ξ₁ ξ₂ : List ℕ),
      subtreeAtAddr T (ξ₁ ++ ξ₂) = (subtreeAtAddr T ξ₁).bind (fun sub => subtreeAtAddr sub ξ₂)
  | _, [], _ => by simp [subtreeAtAddr]
  | .leaf _, _ :: _, _ => by simp [subtreeAtAddr]
  | .internal cs, c :: rest, ξ₂ => by
    simp only [List.cons_append, subtreeAtAddr]
    by_cases hc0 : c = 0
    · simp [hc0]
    · simp only [hc0, ↓reduceIte]
      cases cs[c - 1]? with
      | none => rfl
      | some child => exact subtreeAtAddr_append child rest ξ₂

theorem allInternalNonempty_subtree :
    ∀ {T sub : ScaleTree} {ξ : List ℕ},
      T.AllInternalNonempty → subtreeAtAddr T ξ = some sub → sub.AllInternalNonempty
  | _, _, [], hne, hsub => by
    simp only [subtreeAtAddr, Option.some.injEq] at hsub
    exact hsub ▸ hne
  | .leaf _, _, _ :: _, _, hsub => by simp [subtreeAtAddr] at hsub
  | .internal cs, _, c :: _, hne, hsub => by
    unfold ScaleTree.AllInternalNonempty at hne
    simp only [subtreeAtAddr] at hsub
    split_ifs at hsub with hc0
    cases hget : cs[c - 1]? with
    | none => rw [hget] at hsub; cases hsub
    | some child =>
      rw [hget] at hsub
      exact allInternalNonempty_subtree (hne.2 child (List.mem_of_getElem? hget)) hsub

theorem leaves_ne_nil_of_nonempty :
    ∀ {T : ScaleTree}, T.AllInternalNonempty → T.leaves ≠ []
  | .leaf _, _ => by simp [ScaleTree.leaves, ScaleTree.leafEntries]
  | .internal [], hne => by
    unfold ScaleTree.AllInternalNonempty at hne
    exact absurd rfl hne.1
  | .internal (child :: cs), hne => by
    unfold ScaleTree.AllInternalNonempty at hne
    have hc := leaves_ne_nil_of_nonempty (hne.2 child List.mem_cons_self)
    unfold ScaleTree.leaves ScaleTree.leafEntries ScaleTree.leafEntriesChildren
    rw [List.map_append]
    intro h
    rw [List.append_eq_nil_iff] at h
    have h1 := h.1
    rw [List.map_map] at h1
    have hfun : (Prod.fst ∘ fun x : ℕ × List ℕ => (x.1, 1 :: x.2)) = Prod.fst := by
      funext ⟨_, _⟩; rfl
    rw [hfun] at h1
    exact hc h1

mutual
  theorem leaves_contiguous_of_subtree :
      ∀ (T : ScaleTree) (ξ : List ℕ) (sub : ScaleTree),
        subtreeAtAddr T ξ = some sub →
        ∃ pre suf : List ℕ, T.leaves = pre ++ sub.leaves ++ suf
    | _, [], sub, hsub => by
      simp only [subtreeAtAddr, Option.some.injEq] at hsub
      subst hsub
      exact ⟨[], [], by simp⟩
    | .leaf _, _ :: _, _, hsub => by simp [subtreeAtAddr] at hsub
    | .internal cs, c :: rest, sub, hsub => by
      simp only [subtreeAtAddr] at hsub
      split_ifs at hsub with hc0
      cases hget : cs[c - 1]? with
      | none => rw [hget] at hsub; cases hsub
      | some child =>
        rw [hget] at hsub
        rw [List.getElem?_eq_some_iff] at hget
        obtain ⟨hlt, hchild⟩ := hget
        subst hchild
        obtain ⟨pre₁, suf₁, hcs_split⟩ := leaves_children_split 1 cs (c - 1) hlt
        obtain ⟨pre₂, suf₂, hch_split⟩ := leaves_contiguous_of_subtree cs[c - 1] rest sub hsub
        refine ⟨pre₁ ++ pre₂, suf₂ ++ suf₁, ?_⟩
        change (ScaleTree.leafEntriesChildren 1 cs).map Prod.fst = _
        rw [hcs_split, hch_split]
        simp [List.append_assoc]

  theorem leaves_children_split :
      ∀ (c₀ : ℕ) (cs : List ScaleTree) (i : ℕ) (hi : i < cs.length),
        ∃ pre suf : List ℕ,
          (ScaleTree.leafEntriesChildren c₀ cs).map Prod.fst = pre ++ cs[i].leaves ++ suf
    | c₀, child :: cs, 0, _ => by
      refine ⟨[], (ScaleTree.leafEntriesChildren (c₀ + 1) cs).map Prod.fst, ?_⟩
      conv_lhs => unfold ScaleTree.leafEntriesChildren
      rw [List.map_append, List.map_map]
      have hfun : (Prod.fst ∘ fun x : ℕ × List ℕ => (x.1, c₀ :: x.2)) = Prod.fst := by
        funext ⟨_, _⟩; rfl
      rw [hfun]
      rfl
    | c₀, child :: cs, i + 1, hi => by
      have hi' : i < cs.length := Nat.lt_of_succ_lt_succ hi
      obtain ⟨pre, suf, ih⟩ := leaves_children_split (c₀ + 1) cs i hi'
      refine ⟨child.leaves ++ pre, suf, ?_⟩
      conv_lhs => unfold ScaleTree.leafEntriesChildren
      rw [List.map_append, List.map_map]
      have hfun : (Prod.fst ∘ fun x : ℕ × List ℕ => (x.1, c₀ :: x.2)) = Prod.fst := by
        funext ⟨_, _⟩; rfl
      rw [hfun]
      change child.leaves ++ (ScaleTree.leafEntriesChildren (c₀ + 1) cs).map Prod.fst =
        (child.leaves ++ pre) ++ cs[i].leaves ++ suf
      rw [ih]
      simp [List.append_assoc]
end

theorem append_eq_range' :
    ∀ (pre rest : List ℕ) (s N : ℕ),
      pre ++ rest = List.range' s N →
      pre.length ≤ N ∧ pre = List.range' s pre.length ∧
        rest = List.range' (s + pre.length) (N - pre.length)
  | [], rest, s, N, h => by simpa using h
  | _ :: _, _, _, 0, h => by simp at h
  | x :: xs, rest, s, N + 1, h => by
    simp only [List.cons_append, List.range'_succ, List.cons.injEq] at h
    obtain ⟨hx, htail⟩ := h
    subst x
    obtain ⟨hlen, hpre, hrest⟩ := append_eq_range' xs rest (s + 1) N htail
    simp only [List.length_cons]
    refine ⟨by omega, ?_, ?_⟩
    · rw [List.range'_succ, ← hpre]
    · have h1 : s + (xs.length + 1) = s + 1 + xs.length := by omega
      have h2 : N + 1 - (xs.length + 1) = N - xs.length := by omega
      rw [h1, h2, hrest]

theorem subtree_leaves_range' {r M : ℕ} {T sub : ScaleTree}
    (hT : IsScaleTree r M T) {ξ : List ℕ} (hsub : subtreeAtAddr T ξ = some sub) :
    ∃ a k : ℕ, 1 ≤ a ∧ 1 ≤ k ∧ a + k - 1 ≤ M ∧ sub.leaves = List.range' a k ∧
      mStart T ξ = a ∧ mEnd T ξ = a + k - 1 := by
  obtain ⟨pre, suf, hsplit⟩ := leaves_contiguous_of_subtree T ξ sub hsub
  rw [hT.2.2.2.1, List.append_assoc] at hsplit
  obtain ⟨hpre_len, _, hmid_suf⟩ := append_eq_range' pre (sub.leaves ++ suf) 1 M hsplit.symm
  obtain ⟨hmid_len, hmid_eq, _⟩ :=
    append_eq_range' sub.leaves suf (1 + pre.length) (M - pre.length) hmid_suf
  have hne : sub.leaves ≠ [] := leaves_ne_nil_of_nonempty (allInternalNonempty_subtree hT.2.2.1 hsub)
  have hk1 : 1 ≤ sub.leaves.length := List.length_pos_iff.mpr hne
  refine ⟨1 + pre.length, sub.leaves.length, by omega, hk1, by omega, hmid_eq, ?_, ?_⟩
  · unfold mStart
    rw [hsub]; dsimp only
    rw [hmid_eq]
    cases hk_eq : sub.leaves.length with
    | zero => omega
    | succ k' => simp [List.range'_succ]
  · unfold mEnd
    rw [hsub]; dsimp only
    cases hk_eq : sub.leaves.length with
    | zero => omega
    | succ k' =>
      have hmid_eq' : sub.leaves = List.range' (1 + pre.length) (k' + 1) := by
        simpa [hk_eq] using hmid_eq
      rw [hmid_eq']
      have hlast : (List.range' (1 + pre.length) (k' + 1)).getLast? = some (1 + pre.length + k') := by
        rw [List.range'_1_concat, List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton]
      rw [hlast]
      dsimp

theorem mem_subtree_leaves_iff {r M : ℕ} {T sub : ScaleTree}
    (hT : IsScaleTree r M T) {ξ : List ℕ} (hsub : subtreeAtAddr T ξ = some sub) (ℓ : ℕ) :
    ℓ ∈ sub.leaves ↔ mStart T ξ ≤ ℓ ∧ ℓ ≤ mEnd T ξ := by
  obtain ⟨a, k, _, hk1, _, heq, hst, hend⟩ := subtree_leaves_range' hT hsub
  rw [heq, hst, hend, List.mem_range'_1]
  omega

theorem leafAddr_subtreeAtAddr {r M : ℕ} {T : ScaleTree}
    (hT : IsScaleTree r M T) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hM : ℓ ≤ M) :
    subtreeAtAddr T (leafAddr T ℓ) = some (.leaf ℓ) := by
  have hmem_leaves : ℓ ∈ T.leaves := by
    rw [hT.2.2.2.1, List.mem_range'_1]
    exact ⟨h1, by omega⟩
  unfold ScaleTree.leaves at hmem_leaves
  rw [List.mem_map] at hmem_leaves
  obtain ⟨⟨s, addr⟩, hentry, hs⟩ := hmem_leaves
  dsimp at hs
  subst s
  unfold leafAddr
  cases hfind : T.leafEntries.find? (fun entry => entry.1 == ℓ) with
  | none =>
    have hnone := (List.find?_eq_none.mp hfind) (ℓ, addr) hentry
    simp at hnone
  | some pair =>
    have hpmem := List.mem_of_find?_eq_some hfind
    have hpeq : pair.1 = ℓ := of_decide_eq_true (List.find?_eq_some_iff_append.mp hfind).1
    rcases pair with ⟨s', addr'⟩
    dsimp at hpeq ⊢
    subst s'
    exact (leafEntries_iff_subtreeAtAddr T ℓ addr').mp hpmem

theorem longestCommonPrefix_spec :
    ∀ (xs ys : List ℕ),
      let p := longestCommonPrefix xs ys
      ∃ sx sy : List ℕ, xs = p ++ sx ∧ ys = p ++ sy ∧
        (sx = [] ∨ sy = [] ∨ ∃ c₁ r₁ c₂ r₂, sx = c₁ :: r₁ ∧ sy = c₂ :: r₂ ∧ c₁ ≠ c₂)
  | [], ys => ⟨[], ys, rfl, rfl, Or.inl rfl⟩
  | x :: xs, [] => ⟨x :: xs, [], rfl, rfl, Or.inr (Or.inl rfl)⟩
  | x :: xs, y :: ys => by
    dsimp only
    unfold longestCommonPrefix
    by_cases hxy : x = y
    · subst y
      simp only [↓reduceIte]
      obtain ⟨sx, sy, hx, hy, hdisj⟩ := longestCommonPrefix_spec xs ys
      exact ⟨sx, sy, congrArg (x :: ·) hx, congrArg (x :: ·) hy, hdisj⟩
    · simp only [hxy, ↓reduceIte]
      exact ⟨x :: xs, y :: ys, rfl, rfl, Or.inr (Or.inr ⟨x, xs, y, ys, rfl, rfl, hxy⟩)⟩

theorem children_order_leaves :
    ∀ (c₀ : ℕ) (cs : List ScaleTree) (i₁ i₂ : ℕ) (hi₁ : i₁ < i₂) (hi₂ : i₂ < cs.length)
      (x y : ℕ), x ∈ cs[i₁].leaves → y ∈ cs[i₂].leaves →
      ∃ pre mid suf : List ℕ,
        (ScaleTree.leafEntriesChildren c₀ cs).map Prod.fst = pre ++ [x] ++ mid ++ [y] ++ suf
  | c₀, child :: cs, 0, i₂ + 1, _, hi₂, x, y, hx, hy => by
    have hi₂' : i₂ < cs.length := Nat.lt_of_succ_lt_succ hi₂
    change x ∈ child.leaves at hx
    change y ∈ cs[i₂].leaves at hy
    obtain ⟨pre_x, suf_x, hx_sp⟩ := List.append_of_mem hx
    obtain ⟨pre_c, suf_c, hc_sp⟩ := leaves_children_split (c₀ + 1) cs i₂ hi₂'
    obtain ⟨pre_y, suf_y, hy_sp⟩ := List.append_of_mem hy
    refine ⟨pre_x, suf_x ++ pre_c ++ pre_y, suf_y ++ suf_c, ?_⟩
    unfold ScaleTree.leafEntriesChildren
    rw [List.map_append, List.map_map]
    have hfun : (Prod.fst ∘ fun p : ℕ × List ℕ => (p.1, c₀ :: p.2)) = Prod.fst := by
      funext ⟨_, _⟩; rfl
    rw [hfun]
    change child.leaves ++ (ScaleTree.leafEntriesChildren (c₀ + 1) cs).map Prod.fst = _
    rw [hx_sp, hc_sp, hy_sp]
    simp [List.append_assoc]
  | c₀, child :: cs, i₁ + 1, i₂ + 1, hi₁, hi₂, x, y, hx, hy => by
    obtain ⟨pre, mid, suf, ih⟩ := children_order_leaves (c₀ + 1) cs i₁ i₂
      (Nat.lt_of_succ_lt_succ hi₁) (Nat.lt_of_succ_lt_succ hi₂) x y hx hy
    refine ⟨child.leaves ++ pre, mid, suf, ?_⟩
    unfold ScaleTree.leafEntriesChildren
    rw [List.map_append, List.map_map]
    have hfun : (Prod.fst ∘ fun p : ℕ × List ℕ => (p.1, c₀ :: p.2)) = Prod.fst := by
      funext ⟨_, _⟩; rfl
    rw [hfun]
    change child.leaves ++ (ScaleTree.leafEntriesChildren (c₀ + 1) cs).map Prod.fst = _
    rw [ih]
    simp [List.append_assoc]

theorem pairwise_lt_of_sublist {pre mid suf : List ℕ} {x y : ℕ}
    (hp : (pre ++ [x] ++ mid ++ [y] ++ suf).Pairwise (· < ·)) : x < y := by
  have hp' : (pre ++ (x :: (mid ++ [y] ++ suf))).Pairwise (· < ·) := by
    simpa [List.append_assoc] using hp
  have hx := (List.pairwise_cons.mp (List.pairwise_append.mp hp').2.1).1
  exact hx y (by simp)

theorem lcaScaleTree_routing {r M : ℕ} {T : ScaleTree} (hT : IsScaleTree r M T)
    {ℓ₁ ℓ₂ : ℕ} (h1 : 1 ≤ ℓ₁) (hlt : ℓ₁ < ℓ₂) (h2 : ℓ₂ ≤ M) :
    let ν := lcaScaleTree T ℓ₁ ℓ₂
    let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 0
    ν ∈ internalAddrs T ∧
      1 ≤ c₂ ∧ c₂ ≤ numChildren T ν ∧
      ℓ₁ ≤ mStart T (ν ++ [c₂]) - 1 ∧
      mStart T (ν ++ [c₂]) ≤ ℓ₂ ∧
      ℓ₂ ≤ mEnd T ν ∧
      mEnd T ν ≤ M := by
  intro ν c₂
  have hsub1 := leafAddr_subtreeAtAddr hT h1 (by omega)
  have hsub2 := leafAddr_subtreeAtAddr hT (by omega) h2
  obtain ⟨sx, sy, hx_eq, hy_eq, hdisj⟩ := longestCommonPrefix_spec (leafAddr T ℓ₁) (leafAddr T ℓ₂)
  change leafAddr T ℓ₁ = ν ++ sx at hx_eq
  change leafAddr T ℓ₂ = ν ++ sy at hy_eq
  rcases hdisj with rfl | rfl | ⟨c₁, r₁, c₂', r₂, rfl, rfl, hc_ne⟩
  · exfalso
    rw [List.append_nil] at hx_eq
    rw [hy_eq, ← hx_eq, subtreeAtAddr_append, hsub1] at hsub2
    cases sy <;> simp [subtreeAtAddr] at hsub2
    omega
  · exfalso
    rw [List.append_nil] at hy_eq
    rw [hx_eq, ← hy_eq, subtreeAtAddr_append, hsub2] at hsub1
    cases sx <;> simp [subtreeAtAddr] at hsub1
    omega
  · have hc2_eq : c₂ = c₂' := by
      dsimp [c₂]
      rw [hy_eq, List.getElem?_append_right (le_rfl), Nat.sub_self]
      rfl
    rw [hc2_eq]
    rw [hx_eq, subtreeAtAddr_append] at hsub1
    rw [hy_eq, subtreeAtAddr_append] at hsub2
    cases hν : subtreeAtAddr T ν with
    | none => rw [hν] at hsub1; simp at hsub1
    | some subν =>
      rw [hν] at hsub1 hsub2
      dsimp at hsub1 hsub2
      cases subν with
      | leaf _ => simp [subtreeAtAddr] at hsub1
      | internal cs =>
        have hν_int : ν ∈ internalAddrs T := by
          unfold internalAddrs
          rw [List.mem_toFinset, internalAddrList_iff_subtreeAtAddr]
          exact ⟨cs, hν⟩
        simp only [subtreeAtAddr] at hsub1 hsub2
        have hc1_ne0 : c₁ ≠ 0 := by intro h; simp [h] at hsub1
        have hc2_ne0 : c₂' ≠ 0 := by intro h; simp [h] at hsub2
        simp only [hc1_ne0, hc2_ne0, ↓reduceIte] at hsub1 hsub2
        cases hg1 : cs[c₁ - 1]? with
        | none => rw [hg1] at hsub1; simp at hsub1
        | some ch₁ =>
          cases hg2 : cs[c₂' - 1]? with
          | none => rw [hg2] at hsub2; simp at hsub2
          | some ch₂ =>
            rw [hg1] at hsub1; rw [hg2] at hsub2
            obtain ⟨hi1_lt, hch1⟩ := List.getElem?_eq_some_iff.mp hg1
            obtain ⟨hi2_lt, hch2⟩ := List.getElem?_eq_some_iff.mp hg2
            subst hch1; subst hch2
            have hsub_c2 : subtreeAtAddr T (ν ++ [c₂']) = some cs[c₂' - 1] := by
              rw [subtreeAtAddr_append, hν]; simp [subtreeAtAddr, hc2_ne0, hg2]
            have hmem1 : ℓ₁ ∈ cs[c₁ - 1].leaves := by
              unfold ScaleTree.leaves; rw [List.mem_map]
              exact ⟨(ℓ₁, r₁), (leafEntries_iff_subtreeAtAddr _ _ _).mpr hsub1, rfl⟩
            have hmem2 : ℓ₂ ∈ cs[c₂' - 1].leaves := by
              unfold ScaleTree.leaves; rw [List.mem_map]
              exact ⟨(ℓ₂, r₂), (leafEntries_iff_subtreeAtAddr _ _ _).mpr hsub2, rfl⟩
            have hc1_lt_c2 : c₁ - 1 < c₂' - 1 := by
              rcases lt_trichotomy (c₁ - 1) (c₂' - 1) with h | h | h
              · exact h
              · omega
              · exfalso
                obtain ⟨pre', mid', suf', hord⟩ :=
                  children_order_leaves 1 cs (c₂' - 1) (c₁ - 1) h hi1_lt ℓ₂ ℓ₁ hmem2 hmem1
                obtain ⟨preν, sufν, hν_cont⟩ := leaves_contiguous_of_subtree T ν (.internal cs) hν
                have htotal : List.range' 1 M =
                    (preν ++ pre') ++ [ℓ₂] ++ mid' ++ [ℓ₁] ++ (suf' ++ sufν) := by
                  rw [← hT.2.2.2.1, hν_cont]; unfold ScaleTree.leaves ScaleTree.leafEntries
                  rw [hord]; simp [List.append_assoc]
                have hp_lt := range'_pairwise_lt 1 M
                rw [htotal] at hp_lt
                have h21 := pairwise_lt_of_sublist hp_lt
                omega
            have hstart_c2_mem : mStart T (ν ++ [c₂']) ∈ cs[c₂' - 1].leaves := by
              rw [mem_subtree_leaves_iff hT hsub_c2]
              obtain ⟨a, k, _, hk1, _, _, hst, hend⟩ := subtree_leaves_range' hT hsub_c2
              omega
            have h_l1_lt_start : ℓ₁ < mStart T (ν ++ [c₂']) := by
              obtain ⟨pre', mid', suf', hord⟩ :=
                children_order_leaves 1 cs (c₁ - 1) (c₂' - 1) hc1_lt_c2 hi2_lt
                  ℓ₁ (mStart T (ν ++ [c₂'])) hmem1 hstart_c2_mem
              obtain ⟨preν, sufν, hν_cont⟩ := leaves_contiguous_of_subtree T ν (.internal cs) hν
              have htotal : List.range' 1 M =
                  (preν ++ pre') ++ [ℓ₁] ++ mid' ++ [mStart T (ν ++ [c₂'])] ++ (suf' ++ sufν) := by
                rw [← hT.2.2.2.1, hν_cont]; unfold ScaleTree.leaves ScaleTree.leafEntries
                rw [hord]; simp [List.append_assoc]
              have hp_lt := range'_pairwise_lt 1 M
              rw [htotal] at hp_lt
              exact pairwise_lt_of_sublist hp_lt
            have hmem2_bounds := (mem_subtree_leaves_iff hT hsub_c2 ℓ₂).mp hmem2
            have hmem2_in_ν : ℓ₂ ∈ (ScaleTree.internal cs).leaves := by
              obtain ⟨pre_c, suf_c, hc_sp⟩ := leaves_children_split 1 cs (c₂' - 1) hi2_lt
              change (ScaleTree.leafEntriesChildren 1 cs).map Prod.fst = _ at hc_sp
              unfold ScaleTree.leaves ScaleTree.leafEntries
              rw [hc_sp]
              simp [hmem2]
            have hν_bounds := (mem_subtree_leaves_iff hT hν ℓ₂).mp hmem2_in_ν
            obtain ⟨_, _, _, _, hm_le_M, _, _, hend_ν⟩ := subtree_leaves_range' hT hν
            have hnum : numChildren T ν = cs.length := by simp [numChildren, hν]
            refine ⟨hν_int, by omega, by omega, by omega, hmem2_bounds.1, hν_bounds.2, ?_⟩
            omega

def sigmaTriples {M : ℕ} (T : ScaleTree)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset (List ℕ × ℕ × IntervalBlock) :=
  (internalAddrs T).biUnion (fun ν =>
    let m := mEnd T ν
    if h : m ≤ M then
      (Finset.Icc 1 (numChildren T ν)).biUnion (fun c =>
        ((chain ⟨m, Nat.lt_succ_of_le h⟩).toFinset).image (fun Q => (ν, c, Q)))
    else ∅)

theorem sigmaTriples_card_le {M : ℕ} (T : ScaleTree)
    (chain : Fin (M + 1) → List IntervalBlock) :
    (sigmaTriples T chain).card ≤ sigmaScaleTree T chain := by
  unfold sigmaTriples sigmaScaleTree
  refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun ν _ => ?_)
  dsimp only
  split_ifs with hm
  · refine le_trans Finset.card_biUnion_le ?_
    have hterm : ∀ c ∈ Finset.Icc 1 (numChildren T ν),
        (((chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩).toFinset).image (fun Q => (ν, c, Q))).card ≤
          (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩).length := fun _ _ =>
      le_trans Finset.card_image_le (List.toFinset_card_le _)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    simp [Nat.card_Icc]
  · simp

/-! ## Section 2: `FoldedPopProcess`, Active Keys, `rInt`, `leftSpine`, and `foldedParent` -/

theorem mem_keyFinset_iff :
    ∀ {t : BinaryTree ℕ} {x : ℕ}, x ∈ keyFinset t ↔ x ∈ t
  | .nil, _ => by
    simp only [keyFinset, Finset.notMem_empty, false_iff]
    intro h; cases h
  | .node k l r, x => by
    simp only [keyFinset, Finset.mem_insert, Finset.mem_union, mem_keyFinset_iff,
      BinaryTree.mem_node_iff]

theorem mem_of_mem_leftSpine :
    ∀ {t : BinaryTree ℕ} {x : ℕ}, x ∈ leftSpine t → x ∈ t
  | .nil, _, h => by simp [leftSpine] at h
  | .node _ l _, x, h => by
    simp only [leftSpine, List.mem_append, List.mem_singleton] at h
    rcases h with hl | rfl
    · exact .left (mem_of_mem_leftSpine hl)
    · exact .here

theorem mem_left_of_lt {k : ℕ} {l r : BinaryTree ℕ}
    (hbst : (BinaryTree.node k l r).IsBST) {u : ℕ}
    (hu : u ∈ BinaryTree.node k l r) (huk : u < k) : u ∈ l := by
  rcases BinaryTree.mem_node_iff.mp hu with rfl | hl | hr
  · omega
  · exact hl
  · have hgt := BinaryTree.gt_of_IsBST_right l k r hbst hr
    omega

theorem minKey?_ne_none_of_ne_nil :
    ∀ {t : BinaryTree ℕ}, t ≠ .nil → t.minKey? ≠ none
  | .nil, h => absurd rfl h
  | .node _ l _, _ => by
    unfold BinaryTree.minKey?
    cases l.minKey? <;> simp

theorem minKey?_mem_and_le :
    ∀ {t : BinaryTree ℕ} {s : ℕ}, t.IsBST → t.minKey? = some s →
      s ∈ t ∧ ∀ k ∈ t, s ≤ k
  | .nil, _, _, hm => by simp [BinaryTree.minKey?] at hm
  | .node k l r, s, hbst, hm => by
    unfold BinaryTree.minKey? at hm
    have hl_bst := BinaryTree.IsBST_left_of_IsBST hbst
    cases hlm : l.minKey? with
    | none =>
      have hl_nil : l = .nil := by
        by_contra hne
        exact minKey?_ne_none_of_ne_nil hne hlm
      subst hl_nil
      rw [hlm] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      refine ⟨.here, fun x hx => ?_⟩
      rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
      · exact le_rfl
      · cases hxl
      · exact le_of_lt (BinaryTree.gt_of_IsBST_right .nil k r hbst hxr)
    | some m =>
      rw [hlm] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      obtain ⟨hmem_l, hle_l⟩ := minKey?_mem_and_le hl_bst hlm
      have hmk : m < k := BinaryTree.lt_of_IsBST_left l k r hbst hmem_l
      refine ⟨.left hmem_l, fun x hx => ?_⟩
      rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
      · exact le_of_lt hmk
      · exact hle_l x hxl
      · have hkx := BinaryTree.gt_of_IsBST_right l k r hbst hxr
        omega

theorem keyFinset_spliceMin :
    ∀ {t : BinaryTree ℕ} {s : ℕ}, t.IsBST → t.minKey? = some s →
      keyFinset (spliceMin t) = (keyFinset t).erase s
  | .nil, _, _, hm => by simp [BinaryTree.minKey?] at hm
  | .node k .nil r, s, hbst, hm => by
    simp only [BinaryTree.minKey?, Option.some.injEq] at hm
    subst hm
    simp only [spliceMin, keyFinset, Finset.empty_union]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, mem_keyFinset_iff]
    constructor
    · intro hxr
      have hkx := BinaryTree.gt_of_IsBST_right .nil k r hbst hxr
      exact ⟨by omega, Or.inr hxr⟩
    · rintro ⟨hne, rfl | hxr⟩
      · exact absurd rfl hne
      · exact hxr
  | .node k (.node lk ll lr) r, s, hbst, hm => by
    set l := BinaryTree.node lk ll lr
    have hl_ne : l ≠ .nil := by simp [l]
    have hl_bst := BinaryTree.IsBST_left_of_IsBST hbst
    unfold BinaryTree.minKey? at hm
    cases hlm : l.minKey? with
    | none => exact absurd hlm (minKey?_ne_none_of_ne_nil hl_ne)
    | some m =>
      rw [hlm, Option.some.injEq] at hm
      subst hm
      have ih := keyFinset_spliceMin hl_bst hlm
      obtain ⟨hm_in_l, _⟩ := minKey?_mem_and_le hl_bst hlm
      have hmk : m < k := BinaryTree.lt_of_IsBST_left l k r hbst hm_in_l
      have hsplice : spliceMin (.node k l r) = .node k (spliceMin l) r := rfl
      rw [hsplice]
      simp only [keyFinset, ih]
      ext x
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase, mem_keyFinset_iff]
      constructor
      · rintro (rfl | ⟨hne, hxl⟩ | hxr)
        · exact ⟨by omega, Or.inl rfl⟩
        · exact ⟨hne, Or.inr (Or.inl hxl)⟩
        · have hkx := BinaryTree.gt_of_IsBST_right l k r hbst hxr
          exact ⟨by omega, Or.inr (Or.inr hxr)⟩
      · rintro ⟨hne, rfl | hxl | hxr⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hne, hxl⟩)
        · exact Or.inr (Or.inr hxr)

theorem keyFinset_rotateRightEdge :
    ∀ (t : BinaryTree ℕ) (x p : ℕ), keyFinset (rotateRightEdge t x p) = keyFinset t
  | .nil, _, _ => rfl
  | .node k l r, x, p => by
    unfold rotateRightEdge
    by_cases hpk : p < k
    · simp only [hpk, ↓reduceIte, keyFinset, keyFinset_rotateRightEdge l x p]
    · simp only [hpk, ↓reduceIte]
      by_cases hkp : k < p
      · simp only [hkp, ↓reduceIte, keyFinset, keyFinset_rotateRightEdge r x p]
      · simp only [hkp, ↓reduceIte]
        cases l with
        | nil => rfl
        | node lx a b =>
          by_cases hlx : lx = x
          · simp only [hlx, ↓reduceIte, keyFinset]
            ext z
            simp only [Finset.mem_insert, Finset.mem_union]
            tauto
          · simp [hlx]

theorem keyFinset_foldl_rotateRightEdge :
    ∀ (pairs : List (ℕ × ℕ)) (t : BinaryTree ℕ),
      keyFinset (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t) = keyFinset t
  | [], _ => rfl
  | p :: ps, t => by
    simp only [List.foldl_cons, keyFinset_foldl_rotateRightEdge ps, keyFinset_rotateRightEdge]

theorem modifyLeftAt_push_props :
    ∀ {t : BinaryTree ℕ} {b w : ℕ},
      t.IsBST → b ∈ leftSpine t → (∀ k ∈ t, w < k) →
      keyFinset (modifyLeftAt t b (fun L1 => .node w .nil L1)) = insert w (keyFinset t) ∧
        (∀ cur u, u ∈ t →
          foldedParentAux cur (modifyLeftAt t b (fun L1 => .node w .nil L1)) u =
            foldedParentAux cur t u)
  | .nil, _, _, _, hb, _ => by simp [leftSpine] at hb
  | .node k l r, b, w, hbst, hb, hw => by
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hb
    rcases hb with hbl | rfl
    · have hbk : b < k := BinaryTree.lt_of_IsBST_left l k r hbst (mem_of_mem_leftSpine hbl)
      obtain ⟨ih_kf, ih_fp⟩ := modifyLeftAt_push_props
        (BinaryTree.IsBST_left_of_IsBST hbst) hbl (fun x hx => hw x (.left hx))
      have hmod : modifyLeftAt (.node k l r) b (fun L1 => .node w .nil L1) =
          .node k (modifyLeftAt l b (fun L1 => .node w .nil L1)) r := by
        simp [modifyLeftAt, hbk]
      rw [hmod]
      refine ⟨?_, ?_⟩
      · simp only [keyFinset, ih_kf]
        ext z
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      · intro cur u hu
        unfold foldedParentAux
        by_cases huk : u < k
        · simp only [huk, ↓reduceIte]
          exact ih_fp k u (mem_left_of_lt hbst hu huk)
        · simp only [huk, ↓reduceIte]
    · have hmod : modifyLeftAt (.node b l r) b (fun L1 => .node w .nil L1) =
          .node b (.node w .nil l) r := by
        simp [modifyLeftAt]
      rw [hmod]
      refine ⟨?_, ?_⟩
      · simp only [keyFinset, Finset.empty_union]
        ext z
        simp only [Finset.mem_insert, Finset.mem_union]
        tauto
      · intro cur u hu
        have hwu : w < u := hw u hu
        have hnuw : ¬ (u < w) := by omega
        unfold foldedParentAux
        by_cases hub : u < b
        · simp only [hub, ↓reduceIte]
          conv_lhs => unfold foldedParentAux
          simp only [hnuw, hwu, ↓reduceIte]
        · simp only [hub, ↓reduceIte]

theorem leftSpine_pairwise_lt :
    ∀ {t : BinaryTree ℕ}, t.IsBST → (leftSpine t).Pairwise (· < ·)
  | .nil, _ => List.Pairwise.nil
  | .node k l r, hbst => by
    rw [leftSpine, List.pairwise_append]
    refine ⟨leftSpine_pairwise_lt (BinaryTree.IsBST_left_of_IsBST hbst),
      List.pairwise_singleton _ _, ?_⟩
    intro a ha x hx
    rw [List.mem_singleton] at hx
    subst x
    exact BinaryTree.lt_of_IsBST_left l k r hbst (mem_of_mem_leftSpine ha)

theorem foldedParentAux_leftSpine :
    ∀ {t : BinaryTree ℕ}, t.IsBST → ∀ (cur : ℕ) (idx : Fin (leftSpine t).length),
      foldedParentAux cur t ((leftSpine t)[idx]) =
        if h : idx.val + 1 < (leftSpine t).length then (leftSpine t)[idx.val + 1] else cur
  | .nil, _, _, idx => idx.elim0
  | .node k l r, hbst, cur, idx => by
    have hls_len : (leftSpine (.node k l r)).length = (leftSpine l).length + 1 := by
      simp [leftSpine]
    by_cases hlt : idx.val < (leftSpine l).length
    · have hget : (leftSpine (.node k l r))[idx] = (leftSpine l)[idx.val] := by
        rw [Fin.getElem_fin]
        simp only [leftSpine, List.getElem_append_left hlt]
      rw [hget]
      have hmem_l : (leftSpine l)[idx.val] ∈ l :=
        mem_of_mem_leftSpine (List.getElem_mem hlt)
      have hlt_k : (leftSpine l)[idx.val] < k :=
        BinaryTree.lt_of_IsBST_left l k r hbst hmem_l
      unfold foldedParentAux
      simp only [hlt_k, ↓reduceIte]
      have ih := foldedParentAux_leftSpine (BinaryTree.IsBST_left_of_IsBST hbst) k ⟨idx.val, hlt⟩
      dsimp at ih
      rw [ih]
      have h1 : idx.val + 1 < (leftSpine (.node k l r)).length := by omega
      simp only [h1, ↓reduceDIte]
      by_cases h2 : idx.val + 1 < (leftSpine l).length
      · simp only [h2, ↓reduceDIte, leftSpine, List.getElem_append_left h2]
      · simp only [h2, ↓reduceDIte]
        have heq_len : idx.val + 1 = (leftSpine l).length := by omega
        simp [leftSpine, heq_len]
    · have heq_len : idx.val = (leftSpine l).length := by omega
      have hget : (leftSpine (.node k l r))[idx] = k := by
        rw [Fin.getElem_fin]
        simp [leftSpine, heq_len]
      rw [hget]
      have hn1 : ¬ (idx.val + 1 < (leftSpine (.node k l r)).length) := by omega
      simp only [hn1, ↓reduceDIte]
      unfold foldedParentAux
      simp

theorem foldedParent_leftSpine {P : ℕ} {t : BinaryTree ℕ}
    (hbst : t.IsBST) (hsub : keyFinset t ⊆ Finset.Icc 1 P)
    (idx : Fin (leftSpine t).length) :
    foldedParent P t ((leftSpine t)[idx]) =
      if h : idx.val + 1 < (leftSpine t).length then (leftSpine t)[idx.val + 1] else P + 1 := by
  have hmem : (leftSpine t)[idx] ∈ keyFinset t :=
    mem_keyFinset_iff.mpr (mem_of_mem_leftSpine (List.getElem_mem idx.isLt))
  have hleP : (leftSpine t)[idx] ≤ P := (Finset.mem_Icc.mp (hsub hmem)).2
  have hne : (leftSpine t)[idx] ≠ P + 1 := by omega
  unfold foldedParent
  simp only [hne, ↓reduceIte]
  exact foldedParentAux_leftSpine hbst (P + 1) idx

theorem foldedParentAux_mem :
    ∀ (t : BinaryTree ℕ) (cur v : ℕ),
      foldedParentAux cur t v = cur ∨ foldedParentAux cur t v ∈ t
  | .nil, _, _ => Or.inl rfl
  | .node k l r, cur, v => by
    unfold foldedParentAux
    by_cases hvk : v < k
    · simp only [hvk, ↓reduceIte]
      rcases foldedParentAux_mem l k v with heq | hmem
      · rw [heq]; exact Or.inr .here
      · exact Or.inr (.left hmem)
    · simp only [hvk, ↓reduceIte]
      by_cases hkv : k < v
      · simp only [hkv, ↓reduceIte]
        rcases foldedParentAux_mem r cur v with heq | hmem
        · exact Or.inl heq
        · exact Or.inr (.right hmem)
      · simp [hkv]

theorem foldedParent_mem {P : ℕ} (t : BinaryTree ℕ) (v : ℕ) :
    foldedParent P t v = P + 1 ∨ foldedParent P t v ∈ keyFinset t := by
  unfold foldedParent
  by_cases hv : v = P + 1
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    rcases foldedParentAux_mem t (P + 1) v with heq | hmem
    · exact Or.inl heq
    · exact Or.inr (mem_keyFinset_iff.mpr hmem)

theorem subtreeAtKey_mem_sub :
    ∀ {t : BinaryTree ℕ} {p z : ℕ}, z ∈ subtreeAtKey t p → z ∈ t
  | .nil, _, _, hz => by simp [subtreeAtKey] at hz
  | .node k l r, p, z, hz => by
    unfold subtreeAtKey at hz
    by_cases hpk : p < k
    · simp only [hpk, ↓reduceIte] at hz
      exact .left (subtreeAtKey_mem_sub hz)
    · simp only [hpk, ↓reduceIte] at hz
      by_cases hkp : k < p
      · simp only [hkp, ↓reduceIte] at hz
        exact .right (subtreeAtKey_mem_sub hz)
      · simp only [hkp, ↓reduceIte] at hz
        exact hz

theorem foldedParentAux_of_subtreeAtKey :
    ∀ {t : BinaryTree ℕ} {x p : ℕ} {A B C : BinaryTree ℕ} (cur : ℕ),
      t.IsBST → x < p → subtreeAtKey t p = .node p (.node x A B) C →
      foldedParentAux cur t x = p
  | .nil, _, _, _, _, _, _, _, _, hsub => by simp [subtreeAtKey] at hsub
  | .node k l r, x, p, A, B, C, cur, hbst, hxp, hsub => by
    unfold subtreeAtKey at hsub
    by_cases hpk : p < k
    · simp only [hpk, ↓reduceIte] at hsub
      have hxk : x < k := lt_trans hxp hpk
      unfold foldedParentAux
      simp only [hxk, ↓reduceIte]
      exact foldedParentAux_of_subtreeAtKey k (BinaryTree.IsBST_left_of_IsBST hbst) hxp hsub
    · simp only [hpk, ↓reduceIte] at hsub
      by_cases hkp : k < p
      · simp only [hkp, ↓reduceIte] at hsub
        have hx_in_sub : x ∈ subtreeAtKey r p := by
          rw [hsub]; exact .left .here
        have hx_in_r : x ∈ r := subtreeAtKey_mem_sub hx_in_sub
        have hkx : k < x := BinaryTree.gt_of_IsBST_right l k r hbst hx_in_r
        have hnxk : ¬ (x < k) := by omega
        unfold foldedParentAux
        simp only [hnxk, hkx, ↓reduceIte]
        exact foldedParentAux_of_subtreeAtKey cur (BinaryTree.IsBST_right_of_IsBST hbst) hxp hsub
      · simp only [hkp, ↓reduceIte] at hsub
        injection hsub with hk hl hr
        subst hk; subst hl; subst hr
        unfold foldedParentAux
        simp only [hxp, ↓reduceIte]
        unfold foldedParentAux
        simp

theorem foldedParent_of_isRightRotEdge {P : ℕ} {t : BinaryTree ℕ} {x p : ℕ}
    (hbst : t.IsBST) (hxP : x ≤ P) (hxp : x < p) (hedge : IsRightRotEdge t x p) :
    foldedParent P t x = p := by
  obtain ⟨A, B, C, _, hsub⟩ := hedge
  have hne : x ≠ P + 1 := by omega
  unfold foldedParent
  simp only [hne, ↓reduceIte]
  exact foldedParentAux_of_subtreeAtKey (P + 1) hbst hxp hsub

/-! ### `FoldedPopProcess` Step Evolution, `popStepIdx`, Active Keys, and `sMax` / `tauEmpty` -/

theorem stateAt_zero {P : ℕ} (proc : FoldedPopProcess P) :
    proc.stateAt 0 = (.nil, none) := rfl

theorem treeAt_zero {P : ℕ} (proc : FoldedPopProcess P) :
    proc.treeAt 0 = .nil := rfl

theorem stateAt_succ {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ < proc.steps.length) :
    proc.stateAt (τ + 1) = (proc.steps[τ]).step (proc.stateAt τ) := by
  unfold FoldedPopProcess.stateAt
  rw [List.take_add_one, List.getElem?_eq_getElem hτ, Option.toList_some, List.foldl_append]
  rfl

theorem treeAt_end {P : ℕ} (proc : FoldedPopProcess P) :
    proc.treeAt proc.steps.length = .nil := by
  unfold FoldedPopProcess.treeAt FoldedPopProcess.stateAt
  rw [List.take_length, proc.hEndEmpty]

theorem validFoldedOps_getElem :
    ∀ {P : ℕ} (st : BinaryTree ℕ × Option ℕ) (ops : List FoldedOp) (i : ℕ)
      (hi : i < ops.length),
      ValidFoldedOps P st ops →
      (ops[i]).Valid P ((ops.take i).foldl FoldedOp.step st)
  | _, _, [], _, hi, _ => by simp at hi
  | P, st, op :: rest, 0, _, hval => hval.1
  | P, st, op :: rest, i + 1, hi, hval => by
    simp only [List.getElem_cons_succ, List.take_succ_cons, List.foldl_cons]
    exact validFoldedOps_getElem (op.step st) rest i (Nat.lt_of_succ_lt_succ hi) hval.2

theorem valid_at_step {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ < proc.steps.length) :
    (proc.steps[τ]).Valid P (proc.stateAt τ) :=
  validFoldedOps_getElem (.nil, none) proc.steps τ hτ proc.hValid

def popKey? : FoldedOp → Option ℕ
  | .pop s => some s
  | _ => none

def pushKey? : FoldedOp → Option ℕ
  | .push w => some w
  | _ => none

theorem popKey?_eq_some_iff {op : FoldedOp} {s : ℕ} :
    popKey? op = some s ↔ op = .pop s := by
  cases op <;> simp [popKey?, eq_comm]

theorem pushKey?_eq_some_iff {op : FoldedOp} {w : ℕ} :
    pushKey? op = some w ↔ op = .push w := by
  cases op <;> simp [pushKey?, eq_comm]

theorem filterMap_range'_lt_of_lt :
    ∀ (ops : List FoldedOp) (a n i₁ i₂ s₁ s₂ : ℕ)
      (_h₁ : i₁ < i₂) (h₂ : i₂ < ops.length),
      ops.filterMap popKey? = List.range' a n →
      popKey? ops[i₁] = some s₁ →
      popKey? ops[i₂] = some s₂ →
      s₁ < s₂
  | [], _, _, _, _, _, _, _, h₂, _, _, _ => by simp at h₂
  | op :: rest, a, n, 0, j + 1, s₁, s₂, _, h₂, hseq, he1, he2 => by
    simp only [List.getElem_cons_zero] at he1
    simp only [List.getElem_cons_succ] at he2
    simp only [List.filterMap_cons, he1] at hseq
    cases n with
    | zero => simp at hseq
    | succ n' =>
      rw [List.range'_succ, List.cons.injEq] at hseq
      obtain ⟨rfl, hrest⟩ := hseq
      have hj : j < rest.length := Nat.lt_of_succ_lt_succ h₂
      have hmem : s₂ ∈ rest.filterMap popKey? :=
        List.mem_filterMap.mpr ⟨rest[j], List.getElem_mem hj, he2⟩
      rw [hrest, List.mem_range'_1] at hmem
      omega
  | op :: rest, a, n, i₁ + 1, i₂ + 1, s₁, s₂, h₁, h₂, hseq, he1, he2 => by
    simp only [List.getElem_cons_succ] at he1 he2
    have h₁' : i₁ < i₂ := Nat.lt_of_succ_lt_succ h₁
    have h₂' : i₂ < rest.length := Nat.lt_of_succ_lt_succ h₂
    cases hfx : popKey? op with
    | none =>
      simp only [List.filterMap_cons, hfx] at hseq
      exact filterMap_range'_lt_of_lt rest a n i₁ i₂ s₁ s₂ h₁' h₂' hseq he1 he2
    | some v =>
      simp only [List.filterMap_cons, hfx] at hseq
      cases n with
      | zero => simp at hseq
      | succ n' =>
        rw [List.range'_succ, List.cons.injEq] at hseq
        exact filterMap_range'_lt_of_lt rest (a + 1) n' i₁ i₂ s₁ s₂ h₁' h₂' hseq.2 he1 he2

theorem popStep_bounds_of_getElem {P : ℕ} (proc : FoldedPopProcess P)
    {τ s : ℕ} (hτ : τ < proc.steps.length) (hop : proc.steps[τ] = .pop s) :
    1 ≤ s ∧ s ≤ P := by
  have hmem : s ∈ proc.steps.filterMap popKey? :=
    List.mem_filterMap.mpr ⟨proc.steps[τ], List.getElem_mem hτ, popKey?_eq_some_iff.mpr hop⟩
  have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
  rw [hseq, List.mem_range'_1] at hmem
  omega

theorem popStep_unique_idx {P : ℕ} (proc : FoldedPopProcess P)
    {τ₁ τ₂ s : ℕ} (h1 : τ₁ < proc.steps.length) (h2 : τ₂ < proc.steps.length)
    (hop1 : proc.steps[τ₁] = .pop s) (hop2 : proc.steps[τ₂] = .pop s) : τ₁ = τ₂ := by
  have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
  rcases lt_trichotomy τ₁ τ₂ with hlt | heq | hgt
  · exfalso
    exact (lt_irrefl s) (filterMap_range'_lt_of_lt proc.steps 1 P τ₁ τ₂ s s hlt h2 hseq
      (popKey?_eq_some_iff.mpr hop1) (popKey?_eq_some_iff.mpr hop2))
  · exact heq
  · exfalso
    exact (lt_irrefl s) (filterMap_range'_lt_of_lt proc.steps 1 P τ₂ τ₁ s s hgt h1 hseq
      (popKey?_eq_some_iff.mpr hop2) (popKey?_eq_some_iff.mpr hop1))

theorem popStepIdx_spec {P : ℕ} (proc : FoldedPopProcess P)
    {s : ℕ} (hs1 : 1 ≤ s) (hsP : s ≤ P) :
    ∃ (hlt : proc.popStepIdx s < proc.steps.length),
      proc.steps[proc.popStepIdx s] = .pop s := by
  have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
  have hmem_range : s ∈ List.range' 1 P := List.mem_range'_1.mpr ⟨hs1, by omega⟩
  rw [← hseq, List.mem_filterMap] at hmem_range
  obtain ⟨op, hop_mem, hop_eq⟩ := hmem_range
  rw [popKey?_eq_some_iff] at hop_eq
  subst hop_eq
  unfold FoldedPopProcess.popStepIdx
  have hlt : proc.steps.findIdx (fun o => o == FoldedOp.pop s) < proc.steps.length :=
    List.findIdx_lt_length_of_exists ⟨.pop s, hop_mem, by simp⟩
  have hget : (proc.steps[proc.steps.findIdx (fun o => o == FoldedOp.pop s)] == .pop s) = true :=
    List.findIdx_getElem (w := hlt)
  exact ⟨hlt, of_decide_eq_true hget⟩

theorem getElem_eq_pop_iff {P : ℕ} (proc : FoldedPopProcess P)
    {τ s : ℕ} (hτ : τ < proc.steps.length) :
    proc.steps[τ] = .pop s ↔ 1 ≤ s ∧ s ≤ P ∧ τ = proc.popStepIdx s := by
  constructor
  · intro hop
    obtain ⟨hs1, hsP⟩ := popStep_bounds_of_getElem proc hτ hop
    obtain ⟨hidx_lt, hidx_op⟩ := popStepIdx_spec proc hs1 hsP
    exact ⟨hs1, hsP, popStep_unique_idx proc hτ hidx_lt hop hidx_op⟩
  · rintro ⟨hs1, hsP, rfl⟩
    exact (popStepIdx_spec proc hs1 hsP).2

theorem popStepIdx_strictMono {P : ℕ} (proc : FoldedPopProcess P)
    {s₁ s₂ : ℕ} (h1 : 1 ≤ s₁) (h1P : s₁ ≤ P) (h2 : 1 ≤ s₂) (h2P : s₂ ≤ P) :
    s₁ < s₂ ↔ proc.popStepIdx s₁ < proc.popStepIdx s₂ := by
  have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
  obtain ⟨hi1, hop1⟩ := popStepIdx_spec proc h1 h1P
  obtain ⟨hi2, hop2⟩ := popStepIdx_spec proc h2 h2P
  constructor
  · intro hlt
    rcases lt_trichotomy (proc.popStepIdx s₁) (proc.popStepIdx s₂) with h | heq | hgt
    · exact h
    · exfalso
      have hop1' : proc.steps[proc.popStepIdx s₁]? = some (.pop s₁) := by
        rw [List.getElem?_eq_getElem hi1, hop1]
      have hop2' : proc.steps[proc.popStepIdx s₂]? = some (.pop s₂) := by
        rw [List.getElem?_eq_getElem hi2, hop2]
      rw [heq] at hop1'
      have heq_pop := Option.some.inj (hop1'.symm.trans hop2')
      injection heq_pop; omega
    · exfalso
      have hs21 := filterMap_range'_lt_of_lt proc.steps 1 P
        (proc.popStepIdx s₂) (proc.popStepIdx s₁) s₂ s₁ hgt hi1 hseq
        (popKey?_eq_some_iff.mpr hop2) (popKey?_eq_some_iff.mpr hop1)
      omega
  · intro hlt_idx
    exact filterMap_range'_lt_of_lt proc.steps 1 P
      (proc.popStepIdx s₁) (proc.popStepIdx s₂) s₁ s₂ hlt_idx hi2 hseq
      (popKey?_eq_some_iff.mpr hop1) (popKey?_eq_some_iff.mpr hop2)

theorem step_tree_props {P : ℕ} (proc : FoldedPopProcess P)
    (hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P)
    {τ : ℕ} (hτ : τ < proc.steps.length) :
    match proc.steps[τ] with
    | .shift => proc.treeAt (τ + 1) = proc.treeAt τ
    | .upperRot _ _ => keyFinset (proc.treeAt (τ + 1)) = keyFinset (proc.treeAt τ)
    | .pop s =>
      s ∈ keyFinset (proc.treeAt τ) ∧
        (∀ k ∈ keyFinset (proc.treeAt τ), s ≤ k) ∧
        keyFinset (proc.treeAt (τ + 1)) = (keyFinset (proc.treeAt τ)).erase s
    | .push w =>
      1 ≤ w ∧ w ≤ P ∧
        keyFinset (proc.treeAt (τ + 1)) = insert w (keyFinset (proc.treeAt τ)) ∧
        (∀ u ∈ proc.treeAt τ,
          foldedParent P (proc.treeAt (τ + 1)) u = foldedParent P (proc.treeAt τ) u) := by
  have hval := valid_at_step proc hτ
  have hsucc := stateAt_succ proc hτ
  obtain ⟨hbst, hsub⟩ := hbst_all τ (le_of_lt hτ)
  cases hop : proc.steps[τ] with
  | shift =>
    rw [hop] at hsucc
    unfold FoldedPopProcess.treeAt
    rw [hsucc]
    unfold FoldedOp.step
    cases (proc.stateAt τ).2 <;> rfl
  | upperRot u v =>
    rw [hop] at hsucc
    unfold FoldedPopProcess.treeAt
    rw [hsucc]
    exact keyFinset_rotateRightEdge (proc.treeAt τ) u v
  | pop s =>
    rw [hop] at hval hsucc
    obtain ⟨b, _, hmin, hb_eq, _⟩ := hval
    obtain ⟨hs_mem, hs_le⟩ := minKey?_mem_and_le hbst hmin
    refine ⟨mem_keyFinset_iff.mpr hs_mem, fun k hk => hs_le k (mem_keyFinset_iff.mp hk), ?_⟩
    unfold FoldedPopProcess.treeAt
    rw [hsucc]
    unfold FoldedOp.step
    rw [hb_eq]
    dsimp only
    by_cases hk0 : (takeThrough (leftSpine (proc.stateAt τ).1) b).length - 1 = 0
    · simp only [hk0, ↓reduceIte]
      exact keyFinset_spliceMin hbst hmin
    · simp only [hk0, ↓reduceIte]
      rw [keyFinset_foldl_rotateRightEdge]
      exact keyFinset_spliceMin hbst hmin
  | push w =>
    rw [hop] at hval hsucc
    obtain ⟨hw1, hwP, hw_lt, hnil_iff, hb_mem⟩ := hval
    refine ⟨hw1, hwP, ?_, ?_⟩
    · unfold FoldedPopProcess.treeAt
      rw [hsucc]
      unfold FoldedOp.step
      cases hb : (proc.stateAt τ).2 with
      | none =>
        have hnil : proc.treeAt τ = .nil := hnil_iff.mpr hb
        change keyFinset (.node w .nil .nil) = insert w (keyFinset (proc.treeAt τ))
        rw [hnil]
        simp [keyFinset]
      | some b =>
        exact (modifyLeftAt_push_props hbst (hb_mem b hb) hw_lt).1
    · intro u hu
      have huP : u ≤ P := (Finset.mem_Icc.mp (hsub (mem_keyFinset_iff.mpr hu))).2
      have hne : u ≠ P + 1 := by omega
      unfold FoldedPopProcess.treeAt
      rw [hsucc]
      unfold FoldedOp.step
      cases hb : (proc.stateAt τ).2 with
      | none =>
        have hnil : proc.treeAt τ = .nil := hnil_iff.mpr hb
        change u ∈ proc.treeAt τ at hu
        rw [hnil] at hu
        cases hu
      | some b =>
        change foldedParent P (modifyLeftAt (proc.treeAt τ) b (fun L1 => .node w .nil L1)) u =
          foldedParent P (proc.treeAt τ) u
        unfold foldedParent
        simp only [hne, ↓reduceIte]
        exact (modifyLeftAt_push_props hbst (hb_mem b hb) hw_lt).2 (P + 1) u hu

theorem pushed_before_of_mem_treeAt {P : ℕ} (proc : FoldedPopProcess P)
    (hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P) :
    ∀ {τ : ℕ}, τ ≤ proc.steps.length → ∀ {u : ℕ}, u ∈ keyFinset (proc.treeAt τ) →
      ∃ τ' < τ, ∃ (hτ' : τ' < proc.steps.length), proc.steps[τ'] = .push u
  | 0, _, _, hu => by simp [treeAt_zero, keyFinset] at hu
  | τ + 1, hle, u, hu => by
    have hτ : τ < proc.steps.length := Nat.lt_of_succ_le hle
    have hprops := step_tree_props proc hbst_all hτ
    cases hop : proc.steps[τ] with
    | shift =>
      rw [hop] at hprops
      rw [hprops] at hu
      obtain ⟨τ', hlt, hτ', hpush⟩ := pushed_before_of_mem_treeAt proc hbst_all (le_of_lt hτ) hu
      exact ⟨τ', by omega, hτ', hpush⟩
    | upperRot a b =>
      rw [hop] at hprops
      rw [hprops] at hu
      obtain ⟨τ', hlt, hτ', hpush⟩ := pushed_before_of_mem_treeAt proc hbst_all (le_of_lt hτ) hu
      exact ⟨τ', by omega, hτ', hpush⟩
    | pop s =>
      rw [hop] at hprops
      rw [hprops.2.2, Finset.mem_erase] at hu
      obtain ⟨τ', hlt, hτ', hpush⟩ := pushed_before_of_mem_treeAt proc hbst_all (le_of_lt hτ) hu.2
      exact ⟨τ', by omega, hτ', hpush⟩
    | push w =>
      rw [hop] at hprops
      rw [hprops.2.2.1, Finset.mem_insert] at hu
      rcases hu with rfl | hu_old
      · exact ⟨τ, Nat.lt_succ_self τ, hτ, hop⟩
      · obtain ⟨τ', hlt, hτ', hpush⟩ :=
          pushed_before_of_mem_treeAt proc hbst_all (le_of_lt hτ) hu_old
        exact ⟨τ', by omega, hτ', hpush⟩

theorem nodup_of_length_le_card_toFinset :
    ∀ {xs : List ℕ}, xs.length ≤ xs.toFinset.card → xs.Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    simp only [List.length_cons, List.toFinset_cons] at h
    rw [List.nodup_cons]
    by_cases hx : x ∈ xs.toFinset
    · rw [Finset.insert_eq_of_mem hx] at h
      have hle := List.toFinset_card_le xs
      omega
    · have hcard := Finset.card_insert_le x xs.toFinset
      exact ⟨by simpa using hx, nodup_of_length_le_card_toFinset (by omega)⟩

theorem filterMap_nodup_unique :
    ∀ (ops : List FoldedOp) (i₁ i₂ w : ℕ) (_h₁ : i₁ < i₂) (h₂ : i₂ < ops.length),
      (ops.filterMap pushKey?).Nodup →
      pushKey? ops[i₁] = some w →
      pushKey? ops[i₂] = some w →
      False
  | [], _, _, _, _, h₂, _, _, _ => by simp at h₂
  | op :: rest, 0, j + 1, w, _, h₂, hnd, he1, he2 => by
    simp only [List.getElem_cons_zero] at he1
    simp only [List.getElem_cons_succ] at he2
    simp only [List.filterMap_cons, he1, List.nodup_cons] at hnd
    have hj : j < rest.length := Nat.lt_of_succ_lt_succ h₂
    exact hnd.1 (List.mem_filterMap.mpr ⟨rest[j], List.getElem_mem hj, he2⟩)
  | op :: rest, i₁ + 1, i₂ + 1, w, h₁, h₂, hnd, he1, he2 => by
    simp only [List.getElem_cons_succ] at he1 he2
    have h₁' : i₁ < i₂ := Nat.lt_of_succ_lt_succ h₁
    have h₂' : i₂ < rest.length := Nat.lt_of_succ_lt_succ h₂
    have hnd_rest : (rest.filterMap pushKey?).Nodup := by
      cases hfx : pushKey? op with
      | none => simpa [List.filterMap_cons, hfx] using hnd
      | some _ => exact (List.nodup_cons.mp (by simpa [List.filterMap_cons, hfx] using hnd)).2
    exact filterMap_nodup_unique rest i₁ i₂ w h₁' h₂' hnd_rest he1 he2

theorem push_lt_popStepIdx {P : ℕ} (proc : FoldedPopProcess P)
    (hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P)
    {τ w : ℕ} (hτ : τ < proc.steps.length) (hop : proc.steps[τ] = .push w) :
    1 ≤ w ∧ w ≤ P ∧ τ < proc.popStepIdx w := by
  have hval := valid_at_step proc hτ
  rw [hop] at hval
  obtain ⟨hw1, hwP, _, _, _⟩ := hval
  have hpush_sub : Finset.Icc 1 P ⊆ (proc.steps.filterMap pushKey?).toFinset := by
    intro u hu
    rw [Finset.mem_Icc] at hu
    obtain ⟨hidx_lt, hidx_op⟩ := popStepIdx_spec proc hu.1 hu.2
    have hprops := step_tree_props proc hbst_all hidx_lt
    rw [hidx_op] at hprops
    obtain ⟨τ', _, hτ', hpush_u⟩ :=
      pushed_before_of_mem_treeAt proc hbst_all (le_of_lt hidx_lt) hprops.1
    rw [List.mem_toFinset, List.mem_filterMap]
    exact ⟨proc.steps[τ'], List.getElem_mem hτ', pushKey?_eq_some_iff.mpr hpush_u⟩
  have hcard_ge : P ≤ (proc.steps.filterMap pushKey?).toFinset.card := by
    have hc := Finset.card_le_card hpush_sub
    simpa [Nat.card_Icc] using hc
  have hlen_eq : (proc.steps.filterMap pushKey?).length = P := proc.hPushCount
  have hnd : (proc.steps.filterMap pushKey?).Nodup :=
    nodup_of_length_le_card_toFinset (by omega)
  obtain ⟨hpop_lt, hpop_op⟩ := popStepIdx_spec proc hw1 hwP
  have hprops := step_tree_props proc hbst_all hpop_lt
  rw [hpop_op] at hprops
  obtain ⟨τ₀, hτ₀_lt, hτ₀_len, hpush0⟩ :=
    pushed_before_of_mem_treeAt proc hbst_all (le_of_lt hpop_lt) hprops.1
  have hτ_eq : τ = τ₀ := by
    rcases lt_trichotomy τ τ₀ with hlt | heq | hgt
    · exfalso
      exact filterMap_nodup_unique proc.steps τ τ₀ w hlt hτ₀_len hnd
        (pushKey?_eq_some_iff.mpr hop) (pushKey?_eq_some_iff.mpr hpush0)
    · exact heq
    · exfalso
      exact filterMap_nodup_unique proc.steps τ₀ τ w hgt hτ hnd
        (pushKey?_eq_some_iff.mpr hpush0) (pushKey?_eq_some_iff.mpr hop)
  exact ⟨hw1, hwP, hτ_eq ▸ hτ₀_lt⟩

theorem all_keys_ge_of_ge_popStepIdx {P : ℕ} (proc : FoldedPopProcess P)
    (hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P)
    {s : ℕ} (hs1 : 1 ≤ s) (hsP : s ≤ P) :
    ∀ {τ : ℕ}, proc.popStepIdx s ≤ τ → τ ≤ proc.steps.length →
      ∀ k ∈ keyFinset (proc.treeAt τ), s ≤ k := by
  intro τ hge hle
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
  subst hd
  induction d with
  | zero =>
    rw [Nat.add_zero]
    obtain ⟨hpop_lt, hpop_op⟩ := popStepIdx_spec proc hs1 hsP
    have hprops := step_tree_props proc hbst_all hpop_lt
    rw [hpop_op] at hprops
    exact hprops.2.1
  | succ d ih =>
    set τ' := proc.popStepIdx s + d
    have hstep_eq : proc.popStepIdx s + (d + 1) = τ' + 1 := by omega
    have hτ' : τ' < proc.steps.length := by omega
    have ih' : ∀ k ∈ keyFinset (proc.treeAt τ'), s ≤ k := ih (by omega) (le_of_lt hτ')
    have hprops := step_tree_props proc hbst_all hτ'
    intro k hk
    rw [hstep_eq] at hk
    cases hop : proc.steps[τ'] with
    | shift =>
      rw [hop] at hprops; dsimp only at hprops
      rw [hprops] at hk
      exact ih' k hk
    | upperRot a b =>
      rw [hop] at hprops; dsimp only at hprops
      rw [hprops] at hk
      exact ih' k hk
    | pop s' =>
      rw [hop] at hprops; dsimp only at hprops
      rw [hprops.2.2, Finset.mem_erase] at hk
      exact ih' k hk.2
    | push w =>
      rw [hop] at hprops; dsimp only at hprops
      rw [hprops.2.2.1, Finset.mem_insert] at hk
      rcases hk with rfl | hk_old
      · obtain ⟨hw1, hwP, hlt_w⟩ := push_lt_popStepIdx proc hbst_all hτ' hop
        have hlt_idx : proc.popStepIdx s < proc.popStepIdx k := by omega
        exact le_of_lt ((popStepIdx_strictMono proc hs1 hsP hw1 hwP).mpr hlt_idx)
      · exact ih' k hk_old

theorem finset_sup_id_mem {S : Finset ℕ} (hne : S.Nonempty) : S.sup id ∈ S := by
  have heq : S.sup id = S.max' hne := by
    apply le_antisymm
    · exact Finset.sup_le fun x hx => Finset.le_max' S x hx
    · exact Finset.le_sup (f := id) (Finset.max'_mem S hne)
  rw [heq]
  exact Finset.max'_mem S hne

theorem sMax_and_tauEmpty_props {P : ℕ} (proc : FoldedPopProcess P)
    (hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P)
    {Sp : IntervalBlock} (h1 : 1 ≤ Sp.lo) (hle : Sp.lo ≤ Sp.hi) (hP : Sp.hi ≤ P) :
    sMax proc Sp ∈ Sp.toFinset ∧
    proc.popStepIdx Sp.lo < tauEmpty proc Sp ∧
    (∀ τ, proc.popStepIdx Sp.lo ≤ τ → τ < tauEmpty proc Sp →
      sMax proc Sp ∈ keyFinset (proc.treeAt τ)) ∧
    (∀ τ, proc.popStepIdx Sp.lo ≤ τ → τ < tauEmpty proc Sp →
      ∃ m₀ ∈ keyFinset (proc.treeAt τ),
        m₀ ∈ Sp.toFinset ∧ (proc.treeAt τ).minKey? = some m₀ ∧
        (∀ k ∈ keyFinset (proc.treeAt τ), m₀ ≤ k)) ∧
    (∀ t_L s, Sp.lo ≤ t_L → t_L < s → s ≤ P → proc.popStepIdx s < tauEmpty proc Sp →
      t_L ∈ Sp.toFinset ∧ proc.popStepIdx t_L < tauEmpty proc Sp) := by
  have hloP : Sp.lo ≤ P := le_trans hle hP
  obtain ⟨hlo_lt, hlo_op⟩ := popStepIdx_spec proc h1 hloP
  have hlo_props := step_tree_props proc hbst_all hlo_lt
  rw [hlo_op] at hlo_props
  have hlo_mem_inter :
      Sp.lo ∈ keyFinset (proc.treeAt (proc.popStepIdx Sp.lo)) ∩ Sp.toFinset := by
    rw [Finset.mem_inter, IntervalBlock.toFinset, Finset.mem_Icc]
    exact ⟨hlo_props.1, le_rfl, hle⟩
  have hsm_mem : sMax proc Sp ∈
      keyFinset (proc.treeAt (proc.popStepIdx Sp.lo)) ∩ Sp.toFinset :=
    finset_sup_id_mem ⟨Sp.lo, hlo_mem_inter⟩
  rw [Finset.mem_inter] at hsm_mem
  obtain ⟨hsm_init, hsm_Sp⟩ := hsm_mem
  have hsm_bounds := Finset.mem_Icc.mp hsm_Sp
  have hsm1 : 1 ≤ sMax proc Sp := le_trans h1 hsm_bounds.1
  have hsmP : sMax proc Sp ≤ P := le_trans hsm_bounds.2 hP
  obtain ⟨hsm_pop_lt, _⟩ := popStepIdx_spec proc hsm1 hsmP
  have hlo_le_sm_idx : proc.popStepIdx Sp.lo ≤ proc.popStepIdx (sMax proc Sp) := by
    rcases eq_or_lt_of_le hsm_bounds.1 with heq | hlt
    · rw [heq]
    · exact le_of_lt ((popStepIdx_strictMono proc h1 hloP hsm1 hsmP).mp hlt)
  have hactive : ∀ τ, proc.popStepIdx Sp.lo ≤ τ → τ < tauEmpty proc Sp →
      sMax proc Sp ∈ keyFinset (proc.treeAt τ) := by
    intro τ hge hlt_tau
    unfold tauEmpty at hlt_tau
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
    subst hd
    induction d with
    | zero => simpa using hsm_init
    | succ d ih =>
      set τ' := proc.popStepIdx Sp.lo + d
      have hstep_eq : proc.popStepIdx Sp.lo + (d + 1) = τ' + 1 := by omega
      have hτ'_lt_sm : τ' < proc.popStepIdx (sMax proc Sp) := by omega
      have hτ'_len : τ' < proc.steps.length := lt_trans hτ'_lt_sm hsm_pop_lt
      have hsm_in : sMax proc Sp ∈ keyFinset (proc.treeAt τ') := ih (by omega) (by omega)
      have hprops := step_tree_props proc hbst_all hτ'_len
      rw [hstep_eq]
      cases hop : proc.steps[τ'] with
      | shift => rw [hop] at hprops; dsimp only at hprops; rw [hprops]; exact hsm_in
      | upperRot a b => rw [hop] at hprops; dsimp only at hprops; rw [hprops]; exact hsm_in
      | push w =>
        rw [hop] at hprops; dsimp only at hprops
        rw [hprops.2.2.1, Finset.mem_insert]
        exact Or.inr hsm_in
      | pop s' =>
        rw [hop] at hprops; dsimp only at hprops
        obtain ⟨_, _, hidx_eq⟩ := (getElem_eq_pop_iff proc hτ'_len).mp hop
        have hne_s : sMax proc Sp ≠ s' := by
          intro heq
          rw [heq, ← hidx_eq] at hτ'_lt_sm
          exact lt_irrefl _ hτ'_lt_sm
        rw [hprops.2.2, Finset.mem_erase]
        exact ⟨hne_s, hsm_in⟩
  refine ⟨hsm_Sp, by unfold tauEmpty; omega, hactive, ?_, ?_⟩
  · intro τ hge hlt_tau
    unfold tauEmpty at hlt_tau
    have hτ_le : τ ≤ proc.steps.length := by omega
    have hsm_in := hactive τ hge hlt_tau
    have hne_tree : proc.treeAt τ ≠ .nil := by
      intro hnil
      rw [hnil] at hsm_in
      simp [keyFinset] at hsm_in
    cases hmin : (proc.treeAt τ).minKey? with
    | none => exact absurd hmin (minKey?_ne_none_of_ne_nil hne_tree)
    | some m₀ =>
      obtain ⟨hm0_t, hm0_le⟩ := minKey?_mem_and_le (hbst_all τ hτ_le).1 hmin
      have hm0_kf : m₀ ∈ keyFinset (proc.treeAt τ) := mem_keyFinset_iff.mpr hm0_t
      have hm0_ge : Sp.lo ≤ m₀ := all_keys_ge_of_ge_popStepIdx proc hbst_all h1 hloP hge hτ_le m₀ hm0_kf
      have hm0_le_sm : m₀ ≤ sMax proc Sp := hm0_le _ (mem_keyFinset_iff.mp hsm_in)
      refine ⟨m₀, hm0_kf, ?_, rfl, fun k hk => hm0_le k (mem_keyFinset_iff.mp hk)⟩
      rw [IntervalBlock.toFinset, Finset.mem_Icc]
      exact ⟨hm0_ge, le_trans hm0_le_sm hsm_bounds.2⟩
  · intro t_L s ht_lo hts hsP hs_tau
    have ht1 : 1 ≤ t_L := le_trans h1 ht_lo
    have htP : t_L ≤ P := by omega
    have hs1 : 1 ≤ s := by omega
    have hidx_lt : proc.popStepIdx t_L < proc.popStepIdx s :=
      (popStepIdx_strictMono proc ht1 htP hs1 hsP).mp hts
    have hidx_tau : proc.popStepIdx t_L < tauEmpty proc Sp := lt_trans hidx_lt hs_tau
    have ht_le_sm : t_L ≤ sMax proc Sp := by
      by_contra hgt
      have hsm_lt_t : sMax proc Sp < t_L := by omega
      have hsm_idx_lt := (popStepIdx_strictMono proc hsm1 hsmP ht1 htP).mp hsm_lt_t
      unfold tauEmpty at hidx_tau
      omega
    refine ⟨?_, hidx_tau⟩
    rw [IntervalBlock.toFinset, Finset.mem_Icc]
    exact ⟨ht_lo, le_trans ht_le_sm hsm_bounds.2⟩

/-! ### `rInt`, `foldedPopRotsAt`, and `nextCascadeRot?` Characterization -/

theorem takeThrough_isPrefix :
    ∀ (xs : List ℕ) (b : ℕ), ∃ suf, xs = takeThrough xs b ++ suf
  | [], _ => ⟨[], rfl⟩
  | x :: xs, b => by
    unfold takeThrough
    by_cases hxb : x = b
    · simp only [hxb, ↓reduceIte]
      exact ⟨xs, rfl⟩
    · simp only [hxb, ↓reduceIte]
      obtain ⟨suf, ih⟩ := takeThrough_isPrefix xs b
      exact ⟨suf, by rw [List.cons_append, ← ih]⟩

theorem getElem?_prefix {sub suf ls : List ℕ} (heq : ls = sub ++ suf)
    {i : ℕ} (hi : i < sub.length) : sub[i]? = ls[i]? := by
  subst heq
  rw [List.getElem?_append_left hi]

theorem mem_collectFoldedPopRots_iff :
    ∀ (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (ops : List FoldedOp) (e : InternalPopRot),
      e ∈ collectFoldedPopRots idx st ops ↔
        ∃ (i : ℕ) (hi : i < ops.length),
          e ∈ foldedPopRotsAt (idx + i) ((ops.take i).foldl FoldedOp.step st) ops[i]
  | _, _, [], _ => by simp [collectFoldedPopRots]
  | idx, st, op :: rest, e => by
    simp only [collectFoldedPopRots, List.mem_append]
    rw [mem_collectFoldedPopRots_iff (idx + 1) (op.step st) rest e]
    constructor
    · rintro (h0 | ⟨i, hi, hmem⟩)
      · exact ⟨0, Nat.zero_lt_succ _, by simpa using h0⟩
      · refine ⟨i + 1, Nat.succ_lt_succ hi, ?_⟩
        have hidx : idx + (i + 1) = idx + 1 + i := by omega
        simpa [hidx] using hmem
    · rintro ⟨i, hi, hmem⟩
      cases i with
      | zero => exact Or.inl (by simpa using hmem)
      | succ i' =>
        have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
        have hidx : idx + (i' + 1) = idx + 1 + i' := by omega
        exact Or.inr ⟨i', hi', by simpa [hidx] using hmem⟩

theorem mem_foldedPopRotsAt_spec (τ : ℕ) (st : BinaryTree ℕ × Option ℕ)
    (op : FoldedOp) (e : InternalPopRot)
    (hmem : e ∈ foldedPopRotsAt τ st op) :
    op = .pop e.s ∧ e.stepIdx = τ ∧
    ∃ b, st.2 = some b ∧
      let ls := leftSpine st.1
      let sub := takeThrough ls b
      e.h = (sub.length - 1 - 1) / 2 ∧
      1 ≤ e.j ∧ e.j ≤ e.h ∧
      ∃ (hx : 2 * e.j - 1 < ls.length) (hy : 2 * e.j < ls.length) (hz : 2 * e.j + 1 < ls.length),
        e = { stepIdx := τ, s := e.s, j := e.j, h := e.h,
              x := ls[2 * e.j - 1], y := ls[2 * e.j], z := ls[2 * e.j + 1] } := by
  cases op with
  | push _ => simp [foldedPopRotsAt] at hmem
  | shift => simp [foldedPopRotsAt] at hmem
  | upperRot _ _ => simp [foldedPopRotsAt] at hmem
  | pop s =>
    unfold foldedPopRotsAt at hmem
    cases hb : st.2 with
    | none => rw [hb] at hmem; simp at hmem
    | some b =>
      rw [hb] at hmem
      dsimp only at hmem
      rw [List.mem_filterMap] at hmem
      obtain ⟨idx, hidx_mem, hsome⟩ := hmem
      rw [List.mem_range] at hidx_mem
      set ls := leftSpine st.1
      set sub := takeThrough ls b
      set h := (sub.length - 1 - 1) / 2
      set j := idx + 1
      obtain ⟨suf, hls_eq0⟩ := takeThrough_isPrefix ls b
      have hls_eq : ls = sub ++ suf := hls_eq0
      have hsub_le : sub.length ≤ ls.length := by
        have hlen := congrArg List.length hls_eq
        rw [List.length_append] at hlen
        omega
      have hj1 : 1 ≤ j := by omega
      have hjh : j ≤ h := by omega
      have h2j1 : 2 * j + 1 < sub.length := by omega
      have hx_ls : 2 * j - 1 < ls.length := by omega
      have hy_ls : 2 * j < ls.length := by omega
      have hz_ls : 2 * j + 1 < ls.length := by omega
      have g1 : sub[2 * j - 1]? = some (ls[2 * j - 1]'hx_ls) := by
        rw [getElem?_prefix hls_eq (by omega), List.getElem?_eq_getElem hx_ls]
      have g2 : sub[2 * j]? = some (ls[2 * j]'hy_ls) := by
        rw [getElem?_prefix hls_eq (by omega), List.getElem?_eq_getElem hy_ls]
      have g3 : sub[2 * j + 1]? = some (ls[2 * j + 1]'hz_ls) := by
        rw [getElem?_prefix hls_eq h2j1, List.getElem?_eq_getElem hz_ls]
      rw [g1, g2, g3, Option.some.injEq] at hsome
      have he_eq := hsome.symm
      have hes : e.s = s := by rw [he_eq]
      have hestep : e.stepIdx = τ := by rw [he_eq]
      have hej : e.j = j := by rw [he_eq]
      have heh : e.h = h := by rw [he_eq]
      refine ⟨hes ▸ rfl, hestep, b, rfl, heh, by omega, by omega,
        by omega, by omega, by omega, ?_⟩
      simpa [hes, hej, heh] using he_eq

theorem rInt_props {P : ℕ} (proc : FoldedPopProcess P)
    (hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P)
    {e : InternalPopRot} (he : e ∈ proc.rInt) :
    e.stepIdx < proc.steps.length ∧
    proc.steps[e.stepIdx]? = some (.pop e.s) ∧
    1 ≤ e.s ∧ e.s ≤ P ∧
    e.stepIdx = proc.popStepIdx e.s ∧
    1 ≤ e.j ∧ e.j ≤ e.h ∧
    e.x ∈ leftSpine (proc.treeAt e.stepIdx) ∧
    e.y ∈ leftSpine (proc.treeAt e.stepIdx) ∧
    e.z ∈ leftSpine (proc.treeAt e.stepIdx) ∧
    foldedParent P (proc.treeAt e.stepIdx) e.x = e.y ∧
    foldedParent P (proc.treeAt e.stepIdx) e.y = e.z := by
  unfold FoldedPopProcess.rInt at he
  rw [List.mem_toFinset, mem_collectFoldedPopRots_iff] at he
  obtain ⟨τ, hτ, hmem⟩ := he
  rw [Nat.zero_add] at hmem
  change e ∈ foldedPopRotsAt τ (proc.stateAt τ) proc.steps[τ] at hmem
  obtain ⟨hop, hstep, b, _, _, hj1, hjh, hx_lt, hy_lt, hz_lt, he_rec⟩ :=
    mem_foldedPopRotsAt_spec τ (proc.stateAt τ) proc.steps[τ] e hmem
  subst hstep
  obtain ⟨hs1, hsP, hpop_eq⟩ := (getElem_eq_pop_iff proc hτ).mp hop
  obtain ⟨hbst, hsub⟩ := hbst_all e.stepIdx (le_of_lt hτ)
  set ls := leftSpine (proc.treeAt e.stepIdx)
  change 2 * e.j - 1 < ls.length at hx_lt
  change 2 * e.j < ls.length at hy_lt
  change 2 * e.j + 1 < ls.length at hz_lt
  have hex : e.x = ls[2 * e.j - 1] := congrArg InternalPopRot.x he_rec
  have hey : e.y = ls[2 * e.j] := congrArg InternalPopRot.y he_rec
  have hez : e.z = ls[2 * e.j + 1] := congrArg InternalPopRot.z he_rec
  have hfp_x := foldedParent_leftSpine hbst hsub ⟨2 * e.j - 1, hx_lt⟩
  have hfp_y := foldedParent_leftSpine hbst hsub ⟨2 * e.j, hy_lt⟩
  dsimp at hfp_x hfp_y
  change foldedParent P (proc.treeAt e.stepIdx) ls[2 * e.j - 1] =
    if h : 2 * e.j - 1 + 1 < ls.length then ls[2 * e.j - 1 + 1] else P + 1 at hfp_x
  change foldedParent P (proc.treeAt e.stepIdx) ls[2 * e.j] =
    if h : 2 * e.j + 1 < ls.length then ls[2 * e.j + 1] else P + 1 at hfp_y
  have h2j_eq : 2 * e.j - 1 + 1 = 2 * e.j := by omega
  simp only [h2j_eq, hy_lt, ↓reduceDIte] at hfp_x
  simp only [hz_lt, ↓reduceDIte] at hfp_y
  rw [← hex, ← hey] at hfp_x
  rw [← hey, ← hez] at hfp_y
  refine ⟨hτ, ?_, hs1, hsP, hpop_eq, hj1, hjh,
    hex ▸ List.getElem_mem hx_lt, hey ▸ List.getElem_mem hy_lt, hez ▸ List.getElem_mem hz_lt,
    hfp_x, hfp_y⟩
  rw [List.getElem?_eq_getElem hτ, hop]

theorem rInt_ext_stepIdx_j {P : ℕ} (proc : FoldedPopProcess P)
    {e₁ e₂ : InternalPopRot} (h1 : e₁ ∈ proc.rInt) (h2 : e₂ ∈ proc.rInt)
    (hstep : e₁.stepIdx = e₂.stepIdx) (hj : e₁.j = e₂.j) : e₁ = e₂ := by
  unfold FoldedPopProcess.rInt at h1 h2
  rw [List.mem_toFinset, mem_collectFoldedPopRots_iff] at h1 h2
  obtain ⟨τ₁, hτ₁, hm1⟩ := h1
  obtain ⟨τ₂, hτ₂, hm2⟩ := h2
  rw [Nat.zero_add] at hm1 hm2
  obtain ⟨hop1, hs1, b1, hb1, hh1, _, _, _, _, _, hrec1⟩ :=
    mem_foldedPopRotsAt_spec τ₁ (proc.stateAt τ₁) proc.steps[τ₁] e₁ hm1
  obtain ⟨hop2, hs2, b2, hb2, hh2, _, _, _, _, _, hrec2⟩ :=
    mem_foldedPopRotsAt_spec τ₂ (proc.stateAt τ₂) proc.steps[τ₂] e₂ hm2
  have hτ_eq : τ₁ = τ₂ := by omega
  subst hτ_eq
  have hb_eq : b1 = b2 := Option.some.inj (hb1.symm.trans hb2)
  subst hb_eq
  have hs_eq : e₁.s = e₂.s := by
    have : FoldedOp.pop e₁.s = FoldedOp.pop e₂.s := hop1.symm.trans hop2
    injection this
  have hh_eq : e₁.h = e₂.h := hh1.trans hh2.symm
  rw [hrec1, hrec2]
  simp only [hs_eq, hj, hh_eq]

theorem nextCascadeRot?_some_props {P : ℕ} (proc : FoldedPopProcess P)
    {e eNext : InternalPopRot} (he : e ∈ proc.rInt)
    (hnext : proc.nextCascadeRot? e = some eNext) :
    eNext ∈ proc.rInt ∧
    eNext.stepIdx = e.stepIdx ∧
    eNext.s = e.s ∧
    eNext.j = e.j + 1 ∧
    eNext.h = e.h ∧
    e.j < e.h ∧
    eNext.x = e.z := by
  unfold FoldedPopProcess.nextCascadeRot? at hnext
  have hmem_list := List.mem_of_find?_eq_some hnext
  have hpred := (List.find?_eq_some_iff_append.mp hnext).1
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨hstep_eq, hj_eq⟩ := hpred
  have heNext_rInt : eNext ∈ proc.rInt := List.mem_toFinset.mpr hmem_list
  unfold FoldedPopProcess.rInt at he
  rw [List.mem_toFinset] at he
  rw [mem_collectFoldedPopRots_iff] at he hmem_list
  obtain ⟨τ₁, hτ₁, hm1⟩ := he
  obtain ⟨τ₂, hτ₂, hm2⟩ := hmem_list
  rw [Nat.zero_add] at hm1 hm2
  obtain ⟨hop1, hs1, b1, hb1, hh1, _, _, _, _, _, hrec1⟩ :=
    mem_foldedPopRotsAt_spec τ₁ (proc.stateAt τ₁) proc.steps[τ₁] e hm1
  obtain ⟨hop2, hs2, b2, hb2, hh2, _, hjh2, _, _, _, hrec2⟩ :=
    mem_foldedPopRotsAt_spec τ₂ (proc.stateAt τ₂) proc.steps[τ₂] eNext hm2
  have hτ_eq : τ₁ = τ₂ := by omega
  subst hτ_eq
  have hb_eq : b1 = b2 := Option.some.inj (hb1.symm.trans hb2)
  subst hb_eq
  have hs_eq : eNext.s = e.s := by
    have : FoldedOp.pop eNext.s = FoldedOp.pop e.s := hop2.symm.trans hop1
    injection this
  have hh_eq : eNext.h = e.h := hh2.trans hh1.symm
  have hj_lt : e.j < e.h := by omega
  have hx_eq : eNext.x = e.z := by
    have hxNext : eNext.x = (leftSpine (proc.stateAt τ₁).1)[2 * eNext.j - 1] :=
      congrArg InternalPopRot.x hrec2
    have hze : e.z = (leftSpine (proc.stateAt τ₁).1)[2 * e.j + 1] :=
      congrArg InternalPopRot.z hrec1
    have hidx_eq : 2 * eNext.j - 1 = 2 * e.j + 1 := by omega
    simp only [hxNext, hze, hidx_eq]
  exact ⟨heNext_rInt, hstep_eq, hs_eq, hj_eq, hh_eq, hj_lt, hx_eq⟩

theorem nextCascadeRot?_eq_none_of_j_eq_h {P : ℕ} (proc : FoldedPopProcess P)
    {e : InternalPopRot} (he : e ∈ proc.rInt) (hjh : e.j = e.h) :
    proc.nextCascadeRot? e = none := by
  cases h : proc.nextCascadeRot? e with
  | none => rfl
  | some eNext =>
    obtain ⟨_, _, _, _, _, hlt, _⟩ := nextCascadeRot?_some_props proc he h
    omega

theorem nextCascadeRot?_isSome_of_j_lt_h {P : ℕ} (proc : FoldedPopProcess P)
    {e : InternalPopRot} (he : e ∈ proc.rInt) (hj_lt : e.j < e.h) :
    ∃ eNext, proc.nextCascadeRot? e = some eNext := by
  cases h : proc.nextCascadeRot? e with
  | some eNext => exact ⟨eNext, rfl⟩
  | none =>
    exfalso
    unfold FoldedPopProcess.nextCascadeRot? at h
    unfold FoldedPopProcess.rInt at he
    rw [List.mem_toFinset, mem_collectFoldedPopRots_iff] at he
    obtain ⟨τ, hτ, hm⟩ := he
    rw [Nat.zero_add] at hm
    obtain ⟨hop, hs, b, hb, hh, _, _, _, _, _, _⟩ :=
      mem_foldedPopRotsAt_spec τ (proc.stateAt τ) proc.steps[τ] e hm
    set st := proc.stateAt τ
    set ls := leftSpine st.1
    set sub := takeThrough ls b
    have hj1_lt : e.j < (sub.length - 1 - 1) / 2 := by omega
    have h2j_m1 : 2 * (e.j + 1) - 1 < sub.length := by omega
    have h2j_0 : 2 * (e.j + 1) < sub.length := by omega
    have h2j1 : 2 * (e.j + 1) + 1 < sub.length := by omega
    have hmem_at : ∃ e', e' ∈ foldedPopRotsAt τ st proc.steps[τ] ∧
        e'.stepIdx = τ ∧ e'.j = e.j + 1 := by
      rw [hop]
      unfold foldedPopRotsAt
      rw [hb]
      dsimp only
      refine ⟨{ stepIdx := τ, s := e.s, j := e.j + 1, h := (sub.length - 1 - 1) / 2,
                x := sub[2 * (e.j + 1) - 1]'h2j_m1,
                y := sub[2 * (e.j + 1)]'h2j_0,
                z := sub[2 * (e.j + 1) + 1]'h2j1 }, ?_, rfl, rfl⟩
      rw [List.mem_filterMap]
      refine ⟨e.j, List.mem_range.mpr hj1_lt, ?_⟩
      rw [List.getElem?_eq_getElem h2j_m1, List.getElem?_eq_getElem h2j_0,
        List.getElem?_eq_getElem h2j1]
    obtain ⟨e', he'_at, he'_step, he'_j⟩ := hmem_at
    have he'_coll : e' ∈ collectFoldedPopRots 0 (.nil, none) proc.steps := by
      rw [mem_collectFoldedPopRots_iff]
      refine ⟨τ, hτ, ?_⟩
      rw [Nat.zero_add]
      exact he'_at
    have hnone := (List.find?_eq_none.mp h) e' he'_coll
    simp [he'_step, hs, he'_j] at hnone

theorem nextCascadeRot?_inj {P : ℕ} (proc : FoldedPopProcess P)
    {e₁ e₂ eNext : InternalPopRot} (h1 : e₁ ∈ proc.rInt) (h2 : e₂ ∈ proc.rInt)
    (hn1 : proc.nextCascadeRot? e₁ = some eNext)
    (hn2 : proc.nextCascadeRot? e₂ = some eNext) : e₁ = e₂ := by
  obtain ⟨_, hs1, _, hj1, _, _, _⟩ := nextCascadeRot?_some_props proc h1 hn1
  obtain ⟨_, hs2, _, hj2, _, _, _⟩ := nextCascadeRot?_some_props proc h2 hn2
  exact rInt_ext_stepIdx_j proc h1 h2 (by omega) (by omega)

theorem rInt_same_stepIdx_props {P : ℕ} (proc : FoldedPopProcess P)
    (hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P)
    {e₁ e₂ : InternalPopRot} (h1 : e₁ ∈ proc.rInt) (h2 : e₂ ∈ proc.rInt)
    (hstep : e₁.stepIdx = e₂.stepIdx) :
    e₁.s = e₂.s ∧
    e₁.h = e₂.h ∧
    (e₁.j < e₂.j → e₁.z ≤ e₂.x) ∧
    (e₁.x = e₂.x → e₁ = e₂) ∧
    (e₁.y = e₂.y → e₁ = e₂) := by
  have hr1 := rInt_props proc hbst_all h1
  have hr2 := rInt_props proc hbst_all h2
  unfold FoldedPopProcess.rInt at h1 h2
  rw [List.mem_toFinset, mem_collectFoldedPopRots_iff] at h1 h2
  obtain ⟨τ₁, hτ₁, hm1⟩ := h1
  obtain ⟨τ₂, hτ₂, hm2⟩ := h2
  rw [Nat.zero_add] at hm1 hm2
  obtain ⟨hop1, hs1, b1, hb1, hh1, _, _, hx1_lt, hy1_lt, hz1_lt, hrec1⟩ :=
    mem_foldedPopRotsAt_spec τ₁ (proc.stateAt τ₁) proc.steps[τ₁] e₁ hm1
  obtain ⟨hop2, hs2, b2, hb2, hh2, _, _, hx2_lt, hy2_lt, hz2_lt, hrec2⟩ :=
    mem_foldedPopRotsAt_spec τ₂ (proc.stateAt τ₂) proc.steps[τ₂] e₂ hm2
  have hτ_eq : τ₁ = τ₂ := by omega
  subst hτ_eq
  have hb_eq : b1 = b2 := Option.some.inj (hb1.symm.trans hb2)
  subst hb_eq
  have hs_eq : e₁.s = e₂.s := by
    have : FoldedOp.pop e₁.s = FoldedOp.pop e₂.s := hop1.symm.trans hop2
    injection this
  have hh_eq : e₁.h = e₂.h := hh1.trans hh2.symm
  have hbst : ((proc.stateAt τ₁).1).IsBST := (hbst_all τ₁ (le_of_lt hτ₁)).1
  have hp_ls := List.pairwise_iff_getElem.mp (leftSpine_pairwise_lt hbst)
  set ls := leftSpine (proc.stateAt τ₁).1
  have hx1 : e₁.x = ls[2 * e₁.j - 1] := congrArg InternalPopRot.x hrec1
  have hy1 : e₁.y = ls[2 * e₁.j] := congrArg InternalPopRot.y hrec1
  have hz1 : e₁.z = ls[2 * e₁.j + 1] := congrArg InternalPopRot.z hrec1
  have hx2 : e₂.x = ls[2 * e₂.j - 1] := congrArg InternalPopRot.x hrec2
  have hy2 : e₂.y = ls[2 * e₂.j] := congrArg InternalPopRot.y hrec2
  have hz2 : e₂.z = ls[2 * e₂.j + 1] := congrArg InternalPopRot.z hrec2
  have hord : ∀ {a b : InternalPopRot},
      a.j < b.j →
      ∀ (haz : 2 * a.j + 1 < ls.length) (hbx : 2 * b.j - 1 < ls.length),
      a.z = ls[2 * a.j + 1] → b.x = ls[2 * b.j - 1] → a.z ≤ b.x := by
    intro a b hab haz hbx haz_eq hbx_eq
    rw [haz_eq, hbx_eq]
    rcases eq_or_lt_of_le (show 2 * a.j + 1 ≤ 2 * b.j - 1 by omega) with heq_idx | hlt_idx
    · simp only [heq_idx, le_rfl]
    · exact le_of_lt (hp_ls (2 * a.j + 1) (2 * b.j - 1) haz hbx hlt_idx)
  have h1_lt_y : e₁.x < e₁.y ∧ e₁.y < e₁.z := by
    rw [hx1, hy1, hz1]
    exact ⟨hp_ls _ _ hx1_lt hy1_lt (by omega), hp_ls _ _ hy1_lt hz1_lt (by omega)⟩
  have h2_lt_y : e₂.x < e₂.y ∧ e₂.y < e₂.z := by
    rw [hx2, hy2, hz2]
    exact ⟨hp_ls _ _ hx2_lt hy2_lt (by omega), hp_ls _ _ hy2_lt hz2_lt (by omega)⟩
  have heq_of_j : e₁.j = e₂.j → e₁ = e₂ := by
    intro hj
    rw [hrec1, hrec2]
    simp only [hs_eq, hj, hh_eq]
  refine ⟨hs_eq, hh_eq, fun hlt => hord hlt hz1_lt hx2_lt hz1 hx2, ?_, ?_⟩
  · intro hxeq
    rcases lt_trichotomy e₁.j e₂.j with hlt | hj | hgt
    · have := hord hlt hz1_lt hx2_lt hz1 hx2; omega
    · exact heq_of_j hj
    · have := hord hgt hz2_lt hx1_lt hz2 hx1; omega
  · intro hyeq
    rcases lt_trichotomy e₁.j e₂.j with hlt | hj | hgt
    · have := hord hlt hz1_lt hx2_lt hz1 hx2; omega
    · exact heq_of_j hj
    · have := hord hgt hz2_lt hx1_lt hz2 hx1; omega

/-! ## Section 3: Self-Contained Auxiliary Bounds (`bLeafPre`, `s1Set`, `eEnter`, `b3Intra`) -/

/-! ### Bound 1: `(bLeafPre P proc chain).card ≤ P` -/

theorem bLeafPre_card_le {M P : ℕ} (hP : 1 ≤ P)
    (h_3_6 : Ty_lem_3_6) (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain) :
    (bLeafPre P proc chain).card ≤ P := by
  obtain ⟨h36_1, h36_2, _⟩ := h_3_6 P hP proc
  have hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(h36_1.1 τ hτ).1, (h36_1.1 τ hτ).2.1⟩
  refine le_trans (Finset.card_le_card_of_injOn (t := Finset.Icc 1 P) InternalPopRot.y ?_ ?_)
    (by rw [Nat.card_Icc]; omega)
  · intro e he
    simp only [Finset.mem_coe, bLeafPre, Finset.mem_filter] at he
    obtain ⟨hs1, hsx, hxy, hyz, hzP, _, _⟩ := h36_2.2 e he.1
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  · intro e₁ he₁ e₂ he₂ hy_eq
    simp only [Finset.mem_coe, bLeafPre, Finset.mem_filter] at he₁ he₂
    obtain ⟨hr1, hsep1, hslt1⟩ := he₁
    obtain ⟨hr2, hsep2, hslt2⟩ := he₂
    obtain ⟨hs1_1, hsx1, hxy1, hyz1, hzP1, _, hfrz1⟩ := h36_2.2 e₁ hr1
    obtain ⟨hs1_2, hsx2, hxy2, hyz2, hzP2, _, hfrz2⟩ := h36_2.2 e₂ hr2
    obtain ⟨_, _, _, _, hpop1, _, _, _, hy_ls1, _, _, _⟩ := rInt_props proc hbst_all hr1
    obtain ⟨_, _, _, _, hpop2, _, _, _, hy_ls2, _, _, _⟩ := rInt_props proc hbst_all hr2
    have hQ1 : blockAt (chain (Fin.last M)) e₁.x = blockAt (chain (Fin.last M)) e₁.y :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) (Fin.last M)).mp
        (by simp [Fin.last, hsep1])
    have hQ2 : blockAt (chain (Fin.last M)) e₂.x = blockAt (chain (Fin.last M)) e₂.y :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) (Fin.last M)).mp
        (by simp [Fin.last, hsep2])
    have hQeq : blockAt (chain (Fin.last M)) e₁.x = blockAt (chain (Fin.last M)) e₂.x := by
      rw [hQ1, hQ2, hy_eq]
    have hx1_lo : (blockAt (chain (Fin.last M)) e₁.x).lo ≤ e₁.x :=
      (blockAt_mem_and_bounds (hChain.2.2.1 (Fin.last M)) (u := e₁.x) (by omega) (by omega)).2.1
    have hx2_lo : (blockAt (chain (Fin.last M)) e₂.x).lo ≤ e₂.x :=
      (blockAt_mem_and_bounds (hChain.2.2.1 (Fin.last M)) (u := e₂.x) (by omega) (by omega)).2.1
    rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with hlt | hstep_eq | hgt
    · exfalso
      have hs2_lt_x1 : e₂.s < e₁.x := by rw [← hQeq] at hslt2; omega
      have hidx_lt : e₂.stepIdx < proc.popStepIdx e₁.x := by
        rw [hpop2]
        exact (popStepIdx_strictMono proc (by omega) (by omega) (by omega) (by omega)).mp hs2_lt_x1
      have hmem_win : e₂.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) := by
        rw [Finset.mem_Icc]; omega
      exact hfrz1 e₂.stepIdx hmem_win e₂.y hy_ls2 ⟨by omega, by omega⟩
    · exact (rInt_same_stepIdx_props proc hbst_all hr1 hr2 hstep_eq).2.2.2.2 hy_eq
    · exfalso
      have hs1_lt_x2 : e₁.s < e₂.x := by rw [hQeq] at hslt1; omega
      have hidx_lt : e₁.stepIdx < proc.popStepIdx e₂.x := by
        rw [hpop1]
        exact (popStepIdx_strictMono proc (by omega) (by omega) (by omega) (by omega)).mp hs1_lt_x2
      have hmem_win : e₁.stepIdx ∈ Finset.Icc (e₂.stepIdx + 1) (proc.popStepIdx e₂.x) := by
        rw [Finset.mem_Icc]; omega
      exact hfrz2 e₁.stepIdx hmem_win e₁.y hy_ls1 ⟨by omega, by omega⟩

/-! ### Bound 2: `(s1Set P T proc chain).card ≤ P + 2 * sigmaScaleTree T chain` -/

def b1Triple {M : ℕ} (P : ℕ) (T : ScaleTree)
    (chain : Fin (M + 1) → List IntervalBlock) (e : InternalPopRot) :
    List ℕ × ℕ × IntervalBlock :=
  let ℓ₁ := partSepScale P chain e.s e.x
  let ℓ₂ := partSepScale P chain e.x e.y
  let ν := lcaScaleTree T ℓ₁ ℓ₂
  let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 0
  let m := mEnd T ν
  if hm : m ≤ M then
    (ν, c₂, blockAt (chain ⟨m, Nat.lt_succ_of_le hm⟩) e.y)
  else ([], 0, ⟨0, 0⟩)

theorem b1_routing_bounds {r M P : ℕ} {T : ScaleTree}
    (hT : IsScaleTree r M T) {proc : FoldedPopProcess P}
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (h36_2_rot : ∀ e ∈ proc.rInt,
      1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P ∧
      (∀ τ' ∈ Finset.Ico (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w : ℕ, proc.steps[τ']? = some (.push w) → w < e.x) ∧
      (∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z)))
    {e : InternalPopRot} (he : e ∈ b1 P proc chain) :
    let t := b1Triple P T chain e
    let ν := t.1
    let c₂ := t.2.1
    let Q₂ := t.2.2
    let m₀ := mStart T (ν ++ [c₂]) - 1
    t ∈ sigmaTriples T chain ∧
    ν = lcaScaleTree T (partSepScale P chain e.s e.x) (partSepScale P chain e.x e.y) ∧
    partSepScale P chain e.s e.x ≤ mEnd T ν ∧
    partSepScale P chain e.x e.y ≤ mEnd T ν ∧
    ∃ (hm : mEnd T ν ≤ M) (hm0 : m₀ ≤ M),
      Q₂ = blockAt (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩) e.y ∧
      let B₀ := blockAt (chain ⟨m₀, Nat.lt_succ_of_le hm0⟩) Q₂.lo
      e.s < B₀.lo ∧ B₀.lo ≤ e.x ∧ e.x < Q₂.lo ∧ Q₂.lo ≤ e.y ∧ e.y ≤ Q₂.hi := by
  rw [b1, Finset.mem_filter] at he
  obtain ⟨hr, hℓ1_1, hℓ12, hℓ2_M⟩ := he
  obtain ⟨hs1, hsx, hxy, hyz, hzP, _, _⟩ := h36_2_rot e hr
  set ℓ₁ := partSepScale P chain e.s e.x
  set ℓ₂ := partSepScale P chain e.x e.y
  set ν := lcaScaleTree T ℓ₁ ℓ₂
  set c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 0
  have hrout := lcaScaleTree_routing hT hℓ1_1 hℓ12 hℓ2_M
  change ν ∈ internalAddrs T ∧ 1 ≤ c₂ ∧ c₂ ≤ numChildren T ν ∧
    ℓ₁ ≤ mStart T (ν ++ [c₂]) - 1 ∧ mStart T (ν ++ [c₂]) ≤ ℓ₂ ∧
    ℓ₂ ≤ mEnd T ν ∧ mEnd T ν ≤ M at hrout
  obtain ⟨hν_int, hc2_1, hc2_num, hℓ1_m0, hm_st_ℓ2, hℓ2_mend, hmend_M⟩ := hrout
  set m := mEnd T ν
  set m₀ := mStart T (ν ++ [c₂]) - 1
  have hm0_lt_ℓ2 : m₀ < ℓ₂ := by omega
  have hm0_M : m₀ ≤ M := by omega
  set Q₂ := blockAt (chain ⟨m, Nat.lt_succ_of_le hmend_M⟩) e.y
  have ht_eq : b1Triple P T chain e = (ν, c₂, Q₂) := by
    unfold b1Triple
    dsimp only
    change (if hm : m ≤ M then (ν, c₂, blockAt (chain ⟨m, Nat.lt_succ_of_le hm⟩) e.y) else ([], 0, ⟨0, 0⟩)) = _
    simp only [hmend_M, ↓reduceDIte]
    rfl
  have hQ2_mem_bounds := blockAt_mem_and_bounds (hChain.2.2.1 ⟨m, Nat.lt_succ_of_le hmend_M⟩)
    (u := e.y) (by omega) (by omega)
  have hQ2_part_bounds := (hChain.2.2.1 ⟨m, Nat.lt_succ_of_le hmend_M⟩).1 Q₂ hQ2_mem_bounds.1
  have ht_mem : (ν, c₂, Q₂) ∈ sigmaTriples T chain := by
    unfold sigmaTriples
    rw [Finset.mem_biUnion]
    refine ⟨ν, hν_int, ?_⟩
    dsimp only
    have hm_le : mEnd T ν ≤ M := hmend_M
    simp only [hm_le, ↓reduceDIte]
    rw [Finset.mem_biUnion]
    refine ⟨c₂, Finset.mem_Icc.mpr ⟨hc2_1, hc2_num⟩, ?_⟩
    rw [Finset.mem_image]
    exact ⟨Q₂, List.mem_toFinset.mpr hQ2_mem_bounds.1, rfl⟩
  set km0 : Fin (M + 1) := ⟨m₀, Nat.lt_succ_of_le hm0_M⟩
  set km : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmend_M⟩
  set kℓ2 : Fin (M + 1) := ⟨ℓ₂, Nat.lt_succ_of_le hℓ2_M⟩
  have hxy_eq_m0 : blockAt (chain km0) e.x = blockAt (chain km0) e.y :=
    (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) km0).mp hm0_lt_ℓ2
  have hsub_m0_m := nested_blockAt_sub hChain (k₁ := km0) (k₂ := km)
    (by dsimp [km0, km]; omega) (u := e.y) (by omega) (by omega)
  have hB0_eq : blockAt (chain km0) Q₂.lo = blockAt (chain km0) e.y := by
    obtain ⟨hm_y0, _, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 km0) (u := e.y) (by omega) (by omega)
    exact (blockAt_eq_iff (hChain.2.2.1 km0) hQ2_part_bounds.1
      (le_trans hQ2_part_bounds.2.1 hQ2_part_bounds.2.2) hm_y0).mpr
      ⟨hsub_m0_m.1, le_trans hQ2_mem_bounds.2.1 (le_trans hQ2_mem_bounds.2.2 hsub_m0_m.2)⟩
  have hs_lt_B0 : e.s < (blockAt (chain km0) Q₂.lo).lo := by
    have hs_lt_x : e.s < (blockAt (chain km0) e.x).lo :=
      (partSepScale_le_iff_lt_lo hChain (by omega) (by omega) (by omega) km0).mp hℓ1_m0
    rw [hB0_eq, ← hxy_eq_m0]
    exact hs_lt_x
  have hB0_le_x : (blockAt (chain km0) Q₂.lo).lo ≤ e.x := by
    rw [hB0_eq, ← hxy_eq_m0]
    exact (blockAt_mem_and_bounds (hChain.2.2.1 km0) (u := e.x) (by omega) (by omega)).2.1
  have hxy_ne_ℓ2 : blockAt (chain kℓ2) e.x ≠ blockAt (chain kℓ2) e.y := by
    intro heq
    have hlt := (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) kℓ2).mpr heq
    dsimp [kℓ2] at hlt
    omega
  have hx_hi_lt_y_lo : (blockAt (chain kℓ2) e.x).hi < (blockAt (chain kℓ2) e.y).lo :=
    blockAt_hi_lt_lo_of_ne (hChain.2.2.1 kℓ2) (by omega) (by omega) (by omega) hxy_ne_ℓ2
  have hx_le_hi : e.x ≤ (blockAt (chain kℓ2) e.x).hi :=
    (blockAt_mem_and_bounds (hChain.2.2.1 kℓ2) (u := e.x) (by omega) (by omega)).2.2
  have hy_lo_sub := (nested_blockAt_sub hChain (k₁ := kℓ2) (k₂ := km)
    (by dsimp [kℓ2, km]; omega) (u := e.y) (by omega) (by omega)).1
  have hx_lt_Q2 : e.x < Q₂.lo := by
    change (blockAt (chain kℓ2) e.y).lo ≤ Q₂.lo at hy_lo_sub
    omega
  dsimp only
  rw [ht_eq]
  dsimp only
  exact ⟨ht_mem, rfl, by omega, hℓ2_mend, hmend_M, hm0_M, rfl,
    hs_lt_B0, hB0_le_x, hx_lt_Q2, hQ2_mem_bounds.2.1, hQ2_mem_bounds.2.2⟩

theorem s1Set_card_bound {r M P : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T)
    (h_3_6 : Ty_lem_3_6) (h_5_1 : Ty_lem_5_1)
    (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (s1Set P T proc chain).card ≤ P + 2 * sigmaScaleTree T chain ∧
    25 * (s1Set P T proc chain).card < 26 * P := by
  intro chain
  have hP : 1 ≤ P := hValid.1
  have hT : IsScaleTree r M T := hValid.2.1
  have hChain : IsNestedPartitionChain P chain := scaleTreePartitionChain_isNested T P M hP
  obtain ⟨h36_1, h36_2, _⟩ := h_3_6 P hP proc
  have hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(h36_1.1 τ hτ).1, (h36_1.1 τ hτ).2.1⟩
  set s1 := s1Set P T proc chain
  let s1B1 := s1.filter (fun e => e.j = e.h)
  let s1A := s1.filter (fun e => (b1Triple P T chain e).2.2.hi < e.z)
  let s1B2a := s1.filter (fun e =>
    e.z ≤ (b1Triple P T chain e).2.2.hi ∧ e.j < e.h ∧
      (proc.nextCascadeRot? e).elim false
        (fun eNext => decide ((b1Triple P T chain e).2.2.hi < eNext.y)) = true)
  have hcov : s1 ⊆ s1B1 ∪ s1A ∪ s1B2a := by
    intro e he
    have he_s1 : e ∈ s1Set P T proc chain := he
    unfold s1Set at he_s1
    rw [Finset.mem_filter] at he_s1
    obtain ⟨he_b1, hcond⟩ := he_s1
    have hr : e ∈ proc.rInt := (Finset.mem_filter.mp he_b1).1
    have hp := rInt_props proc hbst_all hr
    obtain ⟨_, hν_eq, _, _, hmend_M, _, hQ2_eq, _⟩ := b1_routing_bounds hT hChain h36_2.2 he_b1
    have hmend_raw : mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x)
        (partSepScale P chain e.x e.y)) ≤ M := hν_eq ▸ hmend_M
    dsimp only at hcond
    simp only [hmend_raw, ↓reduceDIte] at hcond
    have hQ2_eq' : (b1Triple P T chain e).2.2 =
        blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x)
          (partSepScale P chain e.x e.y)), Nat.lt_succ_of_le hmend_raw⟩) e.y := by
      rw [hQ2_eq]; congr 2; exact Fin.ext (congrArg (mEnd T) hν_eq)
    rw [← hQ2_eq'] at hcond
    by_cases hjh : e.j = e.h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hjh⟩))
    · have hj_lt : e.j < e.h := by omega
      by_cases hz_gt : (b1Triple P T chain e).2.2.hi < e.z
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, hz_gt⟩))
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, by omega, hj_lt, ?_⟩)
        obtain ⟨eNext, hnext⟩ := nextCascadeRot?_isSome_of_j_lt_h proc hr hj_lt
        rcases hcond with hA | hB1 | hB2a
        · exact absurd hA hz_gt
        · exact absurd hB1 hjh
        · rw [hnext] at hB2a ⊢
          exact hB2a
  have hcard_B1 : s1B1.card ≤ P := by
    refine le_trans (Finset.card_le_card_of_injOn (t := Finset.Icc 1 P) InternalPopRot.s ?_ ?_)
      (by rw [Nat.card_Icc]; omega)
    · intro e he
      rw [Finset.mem_coe] at he ⊢
      have hr : e ∈ proc.rInt := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1).1
      have hp := rInt_props proc hbst_all hr
      exact Finset.mem_Icc.mpr ⟨hp.2.2.1, hp.2.2.2.1⟩
    · intro e₁ he₁ e₂ he₂ hs_eq
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      have hr1 : e₁ ∈ proc.rInt := (Finset.mem_filter.mp (Finset.mem_filter.mp he₁.1).1).1
      have hr2 : e₂ ∈ proc.rInt := (Finset.mem_filter.mp (Finset.mem_filter.mp he₂.1).1).1
      have hp1 := rInt_props proc hbst_all hr1
      have hp2 := rInt_props proc hbst_all hr2
      have hstep_eq : e₁.stepIdx = e₂.stepIdx := by
        rw [hp1.2.2.2.2.1, hp2.2.2.2.2.1, hs_eq]
      have hh_eq := (rInt_same_stepIdx_props proc hbst_all hr1 hr2 hstep_eq).2.1
      exact rInt_ext_stepIdx_j proc hr1 hr2 hstep_eq (by omega)
  have hcard_A : s1A.card ≤ sigmaScaleTree T chain := by
    refine le_trans (Finset.card_le_card_of_injOn (b1Triple P T chain) ?_ ?_)
      (sigmaTriples_card_le T chain)
    · intro e he
      rw [Finset.mem_coe] at he ⊢
      have he_b1 : e ∈ b1 P proc chain := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
      exact (b1_routing_bounds hT hChain h36_2.2 he_b1).1
    · intro e₁ he₁ e₂ he₂ ht_eq
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      have hb1_1 : e₁ ∈ b1 P proc chain := (Finset.mem_filter.mp he₁.1).1
      have hb1_2 : e₂ ∈ b1 P proc chain := (Finset.mem_filter.mp he₂.1).1
      have hr1 : e₁ ∈ proc.rInt := (Finset.mem_filter.mp hb1_1).1
      have hr2 : e₂ ∈ proc.rInt := (Finset.mem_filter.mp hb1_2).1
      have hp1 := rInt_props proc hbst_all hr1
      have hp2 := rInt_props proc hbst_all hr2
      obtain ⟨_, _, _, _, _, hm0_1, _, hs1_B0, hB0_x1, hx1_Q2, hQ2_y1, hy1_Q2⟩ :=
        b1_routing_bounds hT hChain h36_2.2 hb1_1
      obtain ⟨_, _, _, _, _, hm0_2, _, hs2_B0, hB0_x2, hx2_Q2, hQ2_y2, hy2_Q2⟩ :=
        b1_routing_bounds hT hChain h36_2.2 hb1_2
      have hB0_eq :
          blockAt (chain ⟨mStart T ((b1Triple P T chain e₁).1 ++ [(b1Triple P T chain e₁).2.1]) - 1,
            Nat.lt_succ_of_le hm0_1⟩) (b1Triple P T chain e₁).2.2.lo =
          blockAt (chain ⟨mStart T ((b1Triple P T chain e₂).1 ++ [(b1Triple P T chain e₂).2.1]) - 1,
            Nat.lt_succ_of_le hm0_2⟩) (b1Triple P T chain e₂).2.2.lo := by
        congr 1
        · congr 1; ext; simp [ht_eq]
        · simp [ht_eq]
      have hz1_gt := he₁.2
      have hz2_gt := he₂.2
      rw [← ht_eq] at hx2_Q2 hQ2_y2 hy2_Q2 hz2_gt
      rw [← hB0_eq] at hs2_B0 hB0_x2
      rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with hlt | hstep_eq | hgt
      · exfalso
        have hidx_lt : e₂.stepIdx < proc.popStepIdx e₁.x := by
          rw [hp2.2.2.2.2.1]
          exact (popStepIdx_strictMono proc hp2.2.2.1 hp2.2.2.2.1 (by omega)
            (by have := h36_2.2 e₁ hr1; omega)).mp (lt_of_lt_of_le hs2_B0 hB0_x1)
        have hwin : e₂.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact (h36_2.2 e₁ hr1).2.2.2.2.2.2 e₂.stepIdx hwin e₂.y hp2.2.2.2.2.2.2.2.2.1
          ⟨by omega, by omega⟩
      · have hsame := rInt_same_stepIdx_props proc hbst_all hr1 hr2 hstep_eq
        rcases lt_trichotomy e₁.j e₂.j with hj_lt | hj_eq | hj_gt
        · have := hsame.2.2.1 hj_lt; omega
        · exact rInt_ext_stepIdx_j proc hr1 hr2 hstep_eq hj_eq
        · have := (rInt_same_stepIdx_props proc hbst_all hr2 hr1 hstep_eq.symm).2.2.1 hj_gt
          omega
      · exfalso
        have hidx_lt : e₁.stepIdx < proc.popStepIdx e₂.x := by
          rw [hp1.2.2.2.2.1]
          exact (popStepIdx_strictMono proc hp1.2.2.1 hp1.2.2.2.1 (by omega)
            (by have := h36_2.2 e₂ hr2; omega)).mp (lt_of_lt_of_le hs1_B0 hB0_x2)
        have hwin : e₁.stepIdx ∈ Finset.Icc (e₂.stepIdx + 1) (proc.popStepIdx e₂.x) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact (h36_2.2 e₂ hr2).2.2.2.2.2.2 e₁.stepIdx hwin e₁.y hp1.2.2.2.2.2.2.2.2.1
          ⟨by omega, by omega⟩
  have hcard_B2a : s1B2a.card ≤ sigmaScaleTree T chain := by
    refine le_trans (Finset.card_le_card_of_injOn (b1Triple P T chain) ?_ ?_)
      (sigmaTriples_card_le T chain)
    · intro e he
      rw [Finset.mem_coe] at he ⊢
      have he_b1 : e ∈ b1 P proc chain := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
      exact (b1_routing_bounds hT hChain h36_2.2 he_b1).1
    · intro e₁ he₁ e₂ he₂ ht_eq
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      have hb1_1 : e₁ ∈ b1 P proc chain := (Finset.mem_filter.mp he₁.1).1
      have hb1_2 : e₂ ∈ b1 P proc chain := (Finset.mem_filter.mp he₂.1).1
      have hr1 : e₁ ∈ proc.rInt := (Finset.mem_filter.mp hb1_1).1
      have hr2 : e₂ ∈ proc.rInt := (Finset.mem_filter.mp hb1_2).1
      have hp1 := rInt_props proc hbst_all hr1
      have hp2 := rInt_props proc hbst_all hr2
      obtain ⟨_, _, _, _, _, hm0_1, _, hs1_B0, hB0_x1, hx1_Q2, hQ2_y1, hy1_Q2⟩ :=
        b1_routing_bounds hT hChain h36_2.2 hb1_1
      obtain ⟨_, _, _, _, _, hm0_2, _, hs2_B0, hB0_x2, hx2_Q2, hQ2_y2, hy2_Q2⟩ :=
        b1_routing_bounds hT hChain h36_2.2 hb1_2
      have hB0_eq :
          blockAt (chain ⟨mStart T ((b1Triple P T chain e₁).1 ++ [(b1Triple P T chain e₁).2.1]) - 1,
            Nat.lt_succ_of_le hm0_1⟩) (b1Triple P T chain e₁).2.2.lo =
          blockAt (chain ⟨mStart T ((b1Triple P T chain e₂).1 ++ [(b1Triple P T chain e₂).2.1]) - 1,
            Nat.lt_succ_of_le hm0_2⟩) (b1Triple P T chain e₂).2.2.lo := by
        congr 1
        · congr 1; ext; simp [ht_eq]
        · simp [ht_eq]
      obtain ⟨hz1_le, hj1_lt, hnext1_cond⟩ := he₁.2
      obtain ⟨hz2_le, hj2_lt, hnext2_cond⟩ := he₂.2
      obtain ⟨eN1, hn1⟩ := nextCascadeRot?_isSome_of_j_lt_h proc hr1 hj1_lt
      obtain ⟨eN2, hn2⟩ := nextCascadeRot?_isSome_of_j_lt_h proc hr2 hj2_lt
      rw [hn1] at hnext1_cond
      rw [hn2] at hnext2_cond
      have hw1_gt : (b1Triple P T chain e₁).2.2.hi < eN1.y := of_decide_eq_true hnext1_cond
      have hw2_gt : (b1Triple P T chain e₂).2.2.hi < eN2.y := of_decide_eq_true hnext2_cond
      obtain ⟨hrN1, hstepN1, _, hjN1, _, _, hxN1⟩ := nextCascadeRot?_some_props proc hr1 hn1
      obtain ⟨hrN2, hstepN2, _, hjN2, _, _, hxN2⟩ := nextCascadeRot?_some_props proc hr2 hn2
      have hrot1 := h36_2.2 e₁ hr1
      have hrot2 := h36_2.2 e₂ hr2
      have hrotN1 := h36_2.2 eN1 hrN1
      have hrotN2 := h36_2.2 eN2 hrN2
      rw [← ht_eq] at hx2_Q2 hQ2_y2 hy2_Q2 hz2_le hw2_gt
      rw [← hB0_eq] at hs2_B0 hB0_x2
      rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with hlt | hstep_eq | hgt
      · exfalso
        have hidx_lt1 : e₂.stepIdx < proc.popStepIdx e₁.x := by
          rw [hp2.2.2.2.2.1]
          exact (popStepIdx_strictMono proc hp2.2.2.1 hp2.2.2.2.1 (by omega) (by omega)).mp
            (lt_of_lt_of_le hs2_B0 hB0_x1)
        have hidx_ltN1 : e₂.stepIdx < proc.popStepIdx eN1.x := by
          rw [hp2.2.2.2.2.1]
          exact (popStepIdx_strictMono proc hp2.2.2.1 hp2.2.2.2.1 (by omega) (by omega)).mp
            (by omega)
        have hwin1 : e₂.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hwinN1 : e₂.stepIdx ∈ Finset.Icc (eN1.stepIdx + 1) (proc.popStepIdx eN1.x) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hfrz_y1 := hrot1.2.2.2.2.2.2 e₂.stepIdx hwin1 e₂.y hp2.2.2.2.2.2.2.2.2.1
        have hfrz_yN1 := hrotN1.2.2.2.2.2.2 e₂.stepIdx hwinN1 e₂.y hp2.2.2.2.2.2.2.2.2.1
        have hfrz_z1 := hrot1.2.2.2.2.2.2 e₂.stepIdx hwin1 e₂.z hp2.2.2.2.2.2.2.2.2.2.1
        have hfrz_zN1 := hrotN1.2.2.2.2.2.2 e₂.stepIdx hwinN1 e₂.z hp2.2.2.2.2.2.2.2.2.2.1
        omega
      · rcases lt_trichotomy e₁.j e₂.j with hj_lt | hj_eq | hj_gt
        · exfalso
          have hN1_2 := rInt_same_stepIdx_props proc hbst_all hrN1 hr2 (hstepN1.trans hstep_eq)
          rcases eq_or_lt_of_le (show eN1.j ≤ e₂.j by omega) with hj_eq' | hj_lt'
          · have heq' := rInt_ext_stepIdx_j proc hrN1 hr2 (hstepN1.trans hstep_eq) hj_eq'
            rw [heq'] at hw1_gt; omega
          · have := hN1_2.2.2.1 hj_lt'; omega
        · exact rInt_ext_stepIdx_j proc hr1 hr2 hstep_eq hj_eq
        · exfalso
          have hN2_1 := rInt_same_stepIdx_props proc hbst_all hrN2 hr1 (hstepN2.trans hstep_eq.symm)
          rcases eq_or_lt_of_le (show eN2.j ≤ e₁.j by omega) with hj_eq' | hj_lt'
          · have heq' := rInt_ext_stepIdx_j proc hrN2 hr1 (hstepN2.trans hstep_eq.symm) hj_eq'
            rw [heq'] at hw2_gt; omega
          · have := hN2_1.2.2.1 hj_lt'; omega
      · exfalso
        have hidx_lt2 : e₁.stepIdx < proc.popStepIdx e₂.x := by
          rw [hp1.2.2.2.2.1]
          exact (popStepIdx_strictMono proc hp1.2.2.1 hp1.2.2.2.1 (by omega) (by omega)).mp
            (lt_of_lt_of_le hs1_B0 hB0_x2)
        have hidx_ltN2 : e₁.stepIdx < proc.popStepIdx eN2.x := by
          rw [hp1.2.2.2.2.1]
          exact (popStepIdx_strictMono proc hp1.2.2.1 hp1.2.2.2.1 (by omega) (by omega)).mp
            (by omega)
        have hwin2 : e₁.stepIdx ∈ Finset.Icc (e₂.stepIdx + 1) (proc.popStepIdx e₂.x) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hwinN2 : e₁.stepIdx ∈ Finset.Icc (eN2.stepIdx + 1) (proc.popStepIdx eN2.x) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hfrz_y2 := hrot2.2.2.2.2.2.2 e₁.stepIdx hwin2 e₁.y hp1.2.2.2.2.2.2.2.2.1
        have hfrz_yN2 := hrotN2.2.2.2.2.2.2 e₁.stepIdx hwinN2 e₁.y hp1.2.2.2.2.2.2.2.2.1
        have hfrz_z2 := hrot2.2.2.2.2.2.2 e₁.stepIdx hwin2 e₁.z hp1.2.2.2.2.2.2.2.2.2.1
        have hfrz_zN2 := hrotN2.2.2.2.2.2.2 e₁.stepIdx hwinN2 e₁.z hp1.2.2.2.2.2.2.2.2.2.1
        omega
  have hs1_le : s1.card ≤ P + 2 * sigmaScaleTree T chain := by
    have hc1 := Finset.card_le_card hcov
    have hc2 : (s1B1 ∪ s1A ∪ s1B2a).card ≤ s1B1.card + s1A.card + s1B2a.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    omega
  have hsig_real : (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50 := (h_5_1 P r M T hValid).2.2
  have hsig_nat : 50 * sigmaScaleTree T chain < P := by
    have hr : (50 * sigmaScaleTree T chain : ℝ) < (P : ℝ) := by linarith
    exact_mod_cast hr
  exact ⟨hs1_le, by omega⟩

/-! ### Bound 3: `(eEnter P T proc chain).card ≤ (s1Set P T proc chain).card + (bLeafPre P proc chain).card` -/

theorem eEnter_card_le {r M P : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T)
    (h_3_6 : Ty_lem_3_6) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (eEnter P T proc chain).card ≤
      (s1Set P T proc chain).card + (bLeafPre P proc chain).card := by
  intro chain
  have hP : 1 ≤ P := hValid.1
  have hT : IsScaleTree r M T := hValid.2.1
  have hChain : IsNestedPartitionChain P chain := scaleTreePartitionChain_isNested T P M hP
  obtain ⟨h36_1, h36_2, _⟩ := h_3_6 P hP proc
  have hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(h36_1.1 τ hτ).1, (h36_1.1 τ hτ).2.1⟩
  set s1 := s1Set P T proc chain
  set b1Set := b1 P proc chain
  set b1Only := b1Set \ s1
  set lpre := bLeafPre P proc chain
  set target := b1Set ∪ lpre
  set ee := eEnter P T proc chain
  have hdisj : Disjoint b1Only ee := by
    rw [Finset.disjoint_left]
    intro e he_b1 he_ee
    change e ∈ eEnter P T proc chain at he_ee
    unfold eEnter at he_ee
    rw [Finset.mem_filter, Finset.mem_sdiff] at he_ee
    exact he_ee.1.2 he_b1
  have hstep_map : ∀ e ∈ b1Only ∪ ee,
      e ∈ proc.rInt ∧ ∃ eNext, proc.nextCascadeRot? e = some eNext ∧ eNext ∈ target := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with he_b1o | he_ee
    · rw [Finset.mem_sdiff] at he_b1o
      obtain ⟨he_b1, he_ns1⟩ := he_b1o
      have hr : e ∈ proc.rInt := (Finset.mem_filter.mp he_b1).1
      have hp := rInt_props proc hbst_all hr
      have hrot := h36_2.2 e hr
      obtain ⟨_, hν_eq, hℓ1_le_m, _, hmend_M, _, hQ2_eq, _, _, _, hQ2_y, hy_Q2⟩ :=
        b1_routing_bounds hT hChain h36_2.2 he_b1
      have hmend_raw : mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x)
          (partSepScale P chain e.x e.y)) ≤ M := hν_eq ▸ hmend_M
      have hQ2_eq' : (b1Triple P T chain e).2.2 =
          blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x)
            (partSepScale P chain e.x e.y)), Nat.lt_succ_of_le hmend_raw⟩) e.y := by
        rw [hQ2_eq]; congr 2; exact Fin.ext (congrArg (mEnd T) hν_eq)
      have hns1_cond : ¬ ((b1Triple P T chain e).2.2.hi < e.z ∨ e.j = e.h ∨
          (proc.nextCascadeRot? e).elim true
            (fun eNext => decide ((b1Triple P T chain e).2.2.hi < eNext.y)) = true) := by
        intro hc
        apply he_ns1
        change e ∈ s1Set P T proc chain
        unfold s1Set
        rw [Finset.mem_filter]
        refine ⟨he_b1, ?_⟩
        dsimp only
        simp only [hmend_raw, ↓reduceDIte, ← hQ2_eq']
        exact hc
      have hz_le : e.z ≤ (b1Triple P T chain e).2.2.hi := by omega
      have hj_lt : e.j < e.h := by
        have := hp.2.2.2.2.2.2.1
        by_contra hge
        have heq_jh : e.j = e.h := by omega
        exact hns1_cond (Or.inr (Or.inl heq_jh))
      obtain ⟨eNext, hnext⟩ := nextCascadeRot?_isSome_of_j_lt_h proc hr hj_lt
      have hw_le : eNext.y ≤ (b1Triple P T chain e).2.2.hi := by
        by_contra hgt
        have hgt' : (b1Triple P T chain e).2.2.hi < eNext.y := by omega
        apply hns1_cond (Or.inr (Or.inr ?_))
        rw [hnext]
        exact decide_eq_true hgt'
      obtain ⟨hrN, _, hsN, _, _, _, hxN⟩ := nextCascadeRot?_some_props proc hr hnext
      have hrotN := h36_2.2 eNext hrN
      refine ⟨hr, eNext, hnext, ?_⟩
      have hsep_s_z : partSepScale P chain eNext.s eNext.x ≤
          mEnd T (b1Triple P T chain e).1 := by
        rw [hsN, hxN, partSepScale_ultrametric_ord hChain (a := e.s) (b := e.x) (c := e.z)
          (by omega) (by omega) (by omega)]
        exact le_trans (Nat.min_le_left _ _) hℓ1_le_m
      have hsN_bounds := partSepScale_bounds (P := P) (chain := chain) (u := eNext.s) (v := eNext.x)
        (by omega) (by omega) (by omega) (by omega)
      have hxN_bounds := partSepScale_bounds (P := P) (chain := chain) (u := eNext.x) (v := eNext.y)
        (by omega) (by omega) (by omega) (by omega)
      set km : Fin (M + 1) := ⟨_, Nat.lt_succ_of_le hmend_M⟩
      have hQ2_mem := (blockAt_mem_and_bounds (hChain.2.2.1 km) (u := e.y) (by omega) (by omega)).1
      have hQ2_z : blockAt (chain km) eNext.x = (b1Triple P T chain e).2.2 := by
        rw [hxN, hQ2_eq]
        exact (blockAt_eq_iff (hChain.2.2.1 km) (by omega) (by omega) hQ2_mem).mpr
          ⟨by rw [← hQ2_eq]; omega, by rw [← hQ2_eq]; omega⟩
      have hQ2_w : blockAt (chain km) eNext.y = (b1Triple P T chain e).2.2 := by
        rw [hQ2_eq]
        exact (blockAt_eq_iff (hChain.2.2.1 km) (by omega) (by omega) hQ2_mem).mpr
          ⟨by rw [← hQ2_eq]; omega, by rw [← hQ2_eq]; omega⟩
      have hm_lt_sepN : km.val < partSepScale P chain eNext.x eNext.y :=
        (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) km).mpr
          (hQ2_z.trans hQ2_w.symm)
      dsimp [km] at hm_lt_sepN
      by_cases hN_le_M : partSepScale P chain eNext.x eNext.y ≤ M
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrN, hsN_bounds.1, ?_, hN_le_M⟩)
        omega
      · have hN_M1 : partSepScale P chain eNext.x eNext.y = M + 1 := by omega
        refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrN, hN_M1, ?_⟩)
        exact (partSepScale_le_iff_lt_lo hChain (by omega) (by omega) (by omega)
          (Fin.last M)).mp (by simp [Fin.last]; omega)
    · change e ∈ eEnter P T proc chain at he_ee
      unfold eEnter at he_ee
      rw [Finset.mem_filter, Finset.mem_sdiff] at he_ee
      obtain ⟨⟨hr, _⟩, hcond⟩ := he_ee
      cases hnext : proc.nextCascadeRot? e with
      | none => rw [hnext] at hcond; simp at hcond
      | some eNext =>
        rw [hnext] at hcond
        exact ⟨hr, eNext, rfl, of_decide_eq_true hcond⟩
  let nextFn : InternalPopRot → InternalPopRot := fun e => (proc.nextCascadeRot? e).getD e
  have hcard_map : (b1Only ∪ ee).card ≤ target.card := by
    refine Finset.card_le_card_of_injOn nextFn ?_ ?_
    · intro e he
      rw [Finset.mem_coe] at he ⊢
      obtain ⟨_, eNext, hnext, hmem_t⟩ := hstep_map e he
      simp [nextFn, hnext, hmem_t]
    · intro e₁ he₁ e₂ he₂ hf_eq
      rw [Finset.mem_coe] at he₁ he₂
      obtain ⟨hr1, eN1, hn1, _⟩ := hstep_map e₁ he₁
      obtain ⟨hr2, eN2, hn2, _⟩ := hstep_map e₂ he₂
      dsimp [nextFn] at hf_eq
      rw [hn1, hn2] at hf_eq
      dsimp at hf_eq
      subst hf_eq
      exact nextCascadeRot?_inj proc hr1 hr2 hn1 hn2
  have hunion_eq : (b1Only ∪ ee).card = b1Only.card + ee.card :=
    Finset.card_union_of_disjoint hdisj
  have hs1_sub : s1 ⊆ b1Set := Finset.filter_subset _ _
  have hb1_split : b1Only.card + s1.card = b1Set.card :=
    Finset.card_sdiff_add_card_eq_card hs1_sub
  have htarget_le : target.card ≤ b1Set.card + lpre.card := Finset.card_union_le _ _
  omega

/-! ### Bound 4: `(b3Intra P proc chain).card ≤ 2 * P + proc.kRot + (eEnter P T proc chain).card` -/

theorem foldedParent_top (P : ℕ) (t : BinaryTree ℕ) :
    foldedParent P t (P + 1) = P + 1 := by
  unfold foldedParent; simp

def phiConfVertex {M : ℕ} (P : ℕ) (chain : Fin (M + 1) → List IntervalBlock)
    (t : BinaryTree ℕ) (v : ℕ) : ℕ :=
  if 1 ≤ partSepScale P chain v (foldedParent P t v) ∧
     partSepScale P chain v (foldedParent P t v) ≤ M ∧
     partSepScale P chain v (foldedParent P t v) <
       partSepScale P chain (foldedParent P t v) (foldedParent P t (foldedParent P t v))
  then 1 else 0

theorem phiConfVertex_eq {M : ℕ} (P : ℕ) (chain : Fin (M + 1) → List IntervalBlock)
    (t : BinaryTree ℕ) (v : ℕ) :
    phiConfVertex P chain t v =
      if 1 ≤ partSepScale P chain v (foldedParent P t v) ∧
         partSepScale P chain v (foldedParent P t v) ≤ M ∧
         partSepScale P chain v (foldedParent P t v) <
           partSepScale P chain (foldedParent P t v) (foldedParent P t (foldedParent P t v))
      then 1 else 0 := rfl

def phiConf {M : ℕ} (P : ℕ) (chain : Fin (M + 1) → List IntervalBlock)
    (t : BinaryTree ℕ) : ℕ :=
  ∑ v ∈ keyFinset t, phiConfVertex P chain t v

theorem phiConfVertex_le_one {M : ℕ} (P : ℕ)
    (chain : Fin (M + 1) → List IntervalBlock) (t : BinaryTree ℕ) (v : ℕ) :
    phiConfVertex P chain t v ≤ 1 := by
  rw [phiConfVertex_eq]
  split_ifs <;> omega

theorem telescope_range_le {a b Φ : ℕ → ℕ} :
    ∀ (N : ℕ), (∀ τ < N, a τ + Φ (τ + 1) ≤ Φ τ + b τ) →
      (∑ τ ∈ Finset.range N, a τ) + Φ N ≤ Φ 0 + ∑ τ ∈ Finset.range N, b τ
  | 0, _ => by simp
  | N + 1, hstep => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have ih := telescope_range_le N (fun τ hτ => hstep τ (Nat.lt_succ_of_lt hτ))
    have hN := hstep N (Nat.lt_succ_self N)
    omega

theorem sum_range_opt_ind_eq_filter_length (p : FoldedOp → Bool) :
    ∀ (ops : List FoldedOp),
      (∑ τ ∈ Finset.range ops.length,
        match ops[τ]? with | some op => if p op then 1 else 0 | none => 0) =
        (ops.filter p).length
  | [] => by simp
  | op :: rest => by
    rw [List.length_cons, Finset.sum_range_succ', List.filter_cons]
    have hsum :
        (∑ k ∈ Finset.range rest.length,
          match (op :: rest)[k + 1]? with | some o => if p o then 1 else 0 | none => 0) =
        (∑ k ∈ Finset.range rest.length,
          match rest[k]? with | some o => if p o then 1 else 0 | none => 0) :=
      Finset.sum_congr rfl fun k _ => rfl
    rw [hsum, sum_range_opt_ind_eq_filter_length p rest]
    simp only [List.getElem?_cons_zero]
    cases p op <;> simp

theorem filterMap_length_eq_filter_length {f : FoldedOp → Option ℕ} {p : FoldedOp → Bool}
    (hiff : ∀ op, (f op).isSome = p op) :
    ∀ (ops : List FoldedOp), (ops.filterMap f).length = (ops.filter p).length
  | [] => rfl
  | op :: rest => by
    simp only [List.filterMap_cons, List.filter_cons]
    have h := hiff op
    cases hf : f op with
    | none =>
      rw [hf] at h; dsimp at h
      simp [← h, filterMap_length_eq_filter_length hiff rest]
    | some v =>
      rw [hf] at h; dsimp at h
      simp [← h, filterMap_length_eq_filter_length hiff rest]

theorem card_eq_sum_range_stepIdx {P : ℕ} (proc : FoldedPopProcess P)
    (hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P)
    {S : Finset InternalPopRot} (hS : S ⊆ proc.rInt) :
    S.card = ∑ τ ∈ Finset.range proc.steps.length, (S.filter (fun e => e.stepIdx = τ)).card := by
  have hbi : (Finset.range proc.steps.length).biUnion (fun τ => S.filter (fun e => e.stepIdx = τ)) = S := by
    ext e
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨τ, _, he⟩
      exact (Finset.mem_filter.mp he).1
    · intro he
      have hlt := (rInt_props proc hbst_all (hS he)).1
      exact ⟨e.stepIdx, Finset.mem_range.mpr hlt, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
  conv_lhs => rw [← hbi]
  apply Finset.card_biUnion
  intro τ₁ _ τ₂ _ hne
  change Disjoint _ _
  rw [Finset.disjoint_left]
  intro e h1 h2
  have he1 := (Finset.mem_filter.mp h1).2
  have he2 := (Finset.mem_filter.mp h2).2
  exact hne (he1.symm.trans he2)

theorem b3Intra_card_le {r M P : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T)
    (h_3_6 : Ty_lem_3_6) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (b3Intra P proc chain).card ≤
      2 * P + proc.kRot + (eEnter P T proc chain).card := by
  intro chain
  have hP : 1 ≤ P := hValid.1
  have hT : IsScaleTree r M T := hValid.2.1
  have hChain : IsNestedPartitionChain P chain := scaleTreePartitionChain_isNested T P M hP
  obtain ⟨h36_1, h36_2, _⟩ := h_3_6 P hP proc
  have hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(h36_1.1 τ hτ).1, (h36_1.1 τ hτ).2.1⟩
  let isPush : FoldedOp → Bool := fun | .push _ => true | _ => false
  let isURot : FoldedOp → Bool := fun | .upperRot _ _ => true | _ => false
  let isPop : FoldedOp → Bool := fun | .pop _ => true | _ => false
  let stepCost : ℕ → ℕ := fun τ =>
    (match proc.steps[τ]? with | some op => if isPush op then 1 else 0 | none => 0) +
    (match proc.steps[τ]? with | some op => if isURot op then 1 else 0 | none => 0) +
    (match proc.steps[τ]? with | some op => if isPop op then 1 else 0 | none => 0) +
    ((eEnter P T proc chain).filter (fun e => e.stepIdx = τ)).card
  let stepGain : ℕ → ℕ := fun τ =>
    ((b3Intra P proc chain).filter (fun e => e.stepIdx = τ)).card
  have hlocal : ∀ τ < proc.steps.length,
      stepGain τ + phiConf P chain (proc.treeAt (τ + 1)) ≤
        phiConf P chain (proc.treeAt τ) + stepCost τ := by
    intro τ hτ
    dsimp only [stepGain, stepCost]
    rw [List.getElem?_eq_getElem hτ]
    have hprops := step_tree_props proc hbst_all hτ
    have hno_rot_of_ne_pop : (∀ s, proc.steps[τ] ≠ .pop s) →
        ((b3Intra P proc chain).filter (fun e => e.stepIdx = τ)).card = 0 := by
      intro hnpop
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he hstep_eq
      have hr : e ∈ proc.rInt := (Finset.mem_filter.mp he).1
      have hp := rInt_props proc hbst_all hr
      have hop_some := hp.2.1
      rw [hstep_eq, List.getElem?_eq_getElem hτ, Option.some.injEq] at hop_some
      exact hnpop e.s hop_some
    cases hop : proc.steps[τ] with
    | shift =>
      rw [hop] at hprops; dsimp only at hprops
      have h0 := hno_rot_of_ne_pop (by intro s h; rw [hop] at h; cases h)
      rw [h0, hprops]
      dsimp [isPush, isURot, isPop]
      omega
    | push w =>
      rw [hop] at hprops; dsimp only at hprops
      have h0 := hno_rot_of_ne_pop (by intro s h; rw [hop] at h; cases h)
      rw [h0]
      dsimp [isPush, isURot, isPop]
      set t₀ := proc.treeAt τ
      set t₁ := proc.treeAt (τ + 1)
      have hsame_v : ∀ u ∈ keyFinset t₀,
          phiConfVertex P chain t₁ u = phiConfVertex P chain t₀ u := by
        intro u hu
        have hfp1 : foldedParent P t₁ u = foldedParent P t₀ u :=
          hprops.2.2.2 u (mem_keyFinset_iff.mp hu)
        have hfp2 : foldedParent P t₁ (foldedParent P t₀ u) =
            foldedParent P t₀ (foldedParent P t₀ u) := by
          rcases foldedParent_mem t₀ u with htop | hmem_p
          · rw [htop, foldedParent_top, foldedParent_top]
          · exact hprops.2.2.2 _ (mem_keyFinset_iff.mp hmem_p)
        rw [phiConfVertex_eq, phiConfVertex_eq, hfp1, hfp2]
      have hphi_le : phiConf P chain t₁ ≤ 1 + phiConf P chain t₀ := by
        unfold phiConf
        rw [hprops.2.2.1]
        by_cases hw_mem : w ∈ keyFinset t₀
        · rw [Finset.insert_eq_of_mem hw_mem]
          exact le_trans (le_of_eq (Finset.sum_congr rfl hsame_v)) (Nat.le_add_left _ _)
        · rw [Finset.sum_insert hw_mem, Finset.sum_congr rfl hsame_v]
          exact Nat.add_le_add_right (phiConfVertex_le_one P chain t₁ w) _
      omega
    | upperRot u v =>
      rw [hop] at hprops; dsimp only at hprops
      have h0 := hno_rot_of_ne_pop (by intro s h; rw [hop] at h; cases h)
      rw [h0]
      dsimp [isPush, isURot, isPop]
      set t₀ := proc.treeAt τ
      set t₁ := proc.treeAt (τ + 1)
      have hval := valid_at_step proc hτ
      rw [hop] at hval
      obtain ⟨_, _, _, _, _, _, huv, _, hu_ls, hv_ls, hedge⟩ := hval
      have hu_t0 : u ∈ keyFinset t₀ := mem_keyFinset_iff.mpr (mem_of_mem_leftSpine hu_ls)
      have hv_t0 : v ∈ keyFinset t₀ := mem_keyFinset_iff.mpr (mem_of_mem_leftSpine hv_ls)
      have hu_bounds := Finset.mem_Icc.mp ((hbst_all τ (le_of_lt hτ)).2 hu_t0)
      have hfp0_u : foldedParent P t₀ u = v :=
        foldedParent_of_isRightRotEdge (hbst_all τ (le_of_lt hτ)).1 hu_bounds.2 huv hedge
      have hur_law := h36_1.2.1 τ u v hτ (by rw [List.getElem?_eq_getElem hτ, hop])
      dsimp only at hur_law
      set z := foldedParent P t₀ v
      have hvz : v < z := (h36_1.1 τ (le_of_lt hτ)).2.2.2 v (mem_of_mem_leftSpine hv_ls)
      have hsep_uz : partSepScale P chain u z ≤ partSepScale P chain u v := by
        rw [partSepScale_ultrametric_ord hChain (a := u) (b := v) (c := z)
          hu_bounds.1 (le_of_lt huv) (le_of_lt hvz)]
        exact Nat.min_le_left _ _
      have hother_le : ∀ a ∈ (keyFinset t₀).erase u,
          phiConfVertex P chain t₁ a ≤ phiConfVertex P chain t₀ a := by
        intro a ha
        rw [Finset.mem_erase] at ha
        obtain ⟨hane, ha_t0⟩ := ha
        have ha_t1 : a ∈ t₁ := mem_keyFinset_iff.mp (hprops.symm ▸ ha_t0)
        have hfp_a : foldedParent P t₁ a = foldedParent P t₀ a := hur_law.2 a ha_t1 hane
        by_cases hpu : foldedParent P t₀ a = u
        · rw [phiConfVertex_eq, phiConfVertex_eq, hfp_a, hpu, hur_law.1, hfp0_u]
          split_ifs with hc1 hc0
          · rfl
          · exfalso; exact hc0 ⟨hc1.1, hc1.2.1, lt_of_lt_of_le hc1.2.2 hsep_uz⟩
          · omega
          · rfl
        · have hfp_p : foldedParent P t₁ (foldedParent P t₀ a) =
              foldedParent P t₀ (foldedParent P t₀ a) := by
            rcases foldedParent_mem t₀ a with htop | hp_mem0
            · rw [htop, foldedParent_top, foldedParent_top]
            · exact hur_law.2 _ (mem_keyFinset_iff.mp (hprops.symm ▸ hp_mem0)) hpu
          rw [phiConfVertex_eq, phiConfVertex_eq, hfp_a, hfp_p]
      have hphi_le : phiConf P chain t₁ ≤ 1 + phiConf P chain t₀ := by
        unfold phiConf
        rw [hprops, ← Finset.add_sum_erase _ _ hu_t0,
          ← Finset.add_sum_erase _ (phiConfVertex P chain t₀) hu_t0]
        have hu_le := phiConfVertex_le_one P chain t₁ u
        have hsum_le := Finset.sum_le_sum hother_le
        omega
      omega
    | pop s =>
      rw [hop] at hprops; dsimp only at hprops
      dsimp [isPush, isURot, isPop]
      obtain ⟨hs1, hsP, hτ_eq⟩ := (getElem_eq_pop_iff proc hτ).mp hop
      have hpop_law := h36_1.2.2.1 s hs1 hsP
      dsimp only at hpop_law
      rw [← hτ_eq] at hpop_law
      set t₀ := proc.treeAt τ
      set t₁ := proc.treeAt (τ + 1)
      set rotsAt := proc.rInt.filter (fun e => e.stepIdx = τ)
      set X_prom := rotsAt.image InternalPopRot.x
      have hx_inj : Set.InjOn InternalPopRot.x (rotsAt : Set InternalPopRot) := by
        intro e₁ he₁ e₂ he₂ hx_eq
        rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
        exact (rInt_same_stepIdx_props proc hbst_all he₁.1 he₂.1 (he₁.2.trans he₂.2.symm)).2.2.2.1 hx_eq
      have hX_sub_t1 : X_prom ⊆ keyFinset t₁ := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨e, he, rfl⟩ := hx
        rw [Finset.mem_filter] at he
        have hp := rInt_props proc hbst_all he.1
        have hrot := h36_2.2 e he.1
        have hx_t0 : e.x ∈ keyFinset t₀ := by
          change e.x ∈ keyFinset (proc.treeAt τ)
          rw [← he.2]
          exact mem_keyFinset_iff.mpr (mem_of_mem_leftSpine hp.2.2.2.2.2.2.2.1)
        have hne_s : e.x ≠ s := by
          have hs_eq : e.s = s := by
            have h1 := hp.2.1
            rw [he.2, List.getElem?_eq_getElem hτ, hop, Option.some.injEq] at h1
            injection h1 with h1'; exact h1'.symm
          omega
        rw [hprops.2.2, Finset.mem_erase]
        exact ⟨hne_s, hx_t0⟩
      have hX_sub_t0 : X_prom ⊆ keyFinset t₀ := fun x hx =>
        (Finset.mem_erase.mp (hprops.2.2 ▸ hX_sub_t1 hx)).2
      have hnonprom_le : ∀ a ∈ keyFinset t₁ \ X_prom,
          phiConfVertex P chain t₁ a ≤ phiConfVertex P chain t₀ a := by
        intro a ha
        rw [Finset.mem_sdiff] at ha
        obtain ⟨ha_t1, ha_np⟩ := ha
        have ha_ne_all : ∀ e ∈ proc.rInt, e.stepIdx = τ → a ≠ e.x := by
          intro e hr hst heq
          apply ha_np
          rw [Finset.mem_image]
          exact ⟨e, Finset.mem_filter.mpr ⟨hr, hst⟩, heq.symm⟩
        have hfp_a : foldedParent P t₁ a = foldedParent P t₀ a :=
          hpop_law.2 a (mem_keyFinset_iff.mp ha_t1) ha_ne_all
        by_cases hp_in_X : foldedParent P t₀ a ∈ X_prom
        · rw [Finset.mem_image] at hp_in_X
          obtain ⟨e, he_at, hp_eq⟩ := hp_in_X
          rw [Finset.mem_filter] at he_at
          have hfp0_e : foldedParent P t₀ e.x = e.y := by
            change foldedParent P (proc.treeAt τ) e.x = e.y
            rw [← he_at.2]
            exact (rInt_props proc hbst_all he_at.1).2.2.2.2.2.2.2.2.2.2.1
          have hfp1_e : foldedParent P t₁ e.x = e.z := hpop_law.1 e he_at.1 he_at.2
          have hrot_e := h36_2.2 e he_at.1
          have hsep_ez : partSepScale P chain e.x e.z ≤ partSepScale P chain e.x e.y := by
            rw [partSepScale_ultrametric_ord hChain (a := e.x) (b := e.y) (c := e.z)
              (by omega) (by omega) (by omega)]
            exact Nat.min_le_left _ _
          rw [phiConfVertex_eq, phiConfVertex_eq, hfp_a, ← hp_eq, hfp1_e, hfp0_e]
          split_ifs with hc1 hc0
          · rfl
          · exfalso; exact hc0 ⟨hc1.1, hc1.2.1, lt_of_lt_of_le hc1.2.2 hsep_ez⟩
          · omega
          · rfl
        · by_cases hp_top : foldedParent P t₀ a = P + 1
          · rw [phiConfVertex_eq, phiConfVertex_eq, hfp_a, hp_top, foldedParent_top, foldedParent_top]
          · have hp_t0 : foldedParent P t₀ a ∈ keyFinset t₀ := by
              rcases foldedParent_mem t₀ a with htop | hmem
              · exact absurd htop hp_top
              · exact hmem
            have ha_t0 : a ∈ keyFinset t₀ := (Finset.mem_erase.mp (hprops.2.2 ▸ ha_t1)).2
            have hs_le_a : s ≤ a := hprops.2.1 a ha_t0
            have ha_lt_p : a < foldedParent P t₀ a :=
              (h36_1.1 τ (le_of_lt hτ)).2.2.2 a (mem_keyFinset_iff.mp ha_t0)
            have hp_t1 : foldedParent P t₀ a ∈ keyFinset t₁ := by
              rw [hprops.2.2, Finset.mem_erase]
              exact ⟨by omega, hp_t0⟩
            have hp_ne_all : ∀ e ∈ proc.rInt, e.stepIdx = τ → foldedParent P t₀ a ≠ e.x := by
              intro e hr hst heq
              apply hp_in_X
              rw [Finset.mem_image]
              exact ⟨e, Finset.mem_filter.mpr ⟨hr, hst⟩, heq.symm⟩
            have hfp_p : foldedParent P t₁ (foldedParent P t₀ a) =
                foldedParent P t₀ (foldedParent P t₀ a) :=
              hpop_law.2 _ (mem_keyFinset_iff.mp hp_t1) hp_ne_all
            rw [phiConfVertex_eq, phiConfVertex_eq, hfp_a, hfp_p]
      let topInd : InternalPopRot → ℕ := fun e => if e.j = e.h then 1 else 0
      let intraInd : InternalPopRot → ℕ := fun e => if e ∈ b3Intra P proc chain then 1 else 0
      let enterInd : InternalPopRot → ℕ := fun e => if e ∈ eEnter P T proc chain then 1 else 0
      have hrot_ptwise : ∀ e ∈ rotsAt,
          intraInd e + phiConfVertex P chain t₁ e.x ≤
            phiConfVertex P chain t₀ e.x + topInd e + enterInd e := by
        intro e he_at
        rw [Finset.mem_filter] at he_at
        obtain ⟨hr, hst_eq⟩ := he_at
        have hp := rInt_props proc hbst_all hr
        have hrot := h36_2.2 e hr
        have hfp0_x : foldedParent P t₀ e.x = e.y := by
          change foldedParent P (proc.treeAt τ) e.x = e.y
          rw [← hst_eq]
          exact hp.2.2.2.2.2.2.2.2.2.2.1
        have hfp0_y : foldedParent P t₀ e.y = e.z := by
          change foldedParent P (proc.treeAt τ) e.y = e.z
          rw [← hst_eq]
          exact hp.2.2.2.2.2.2.2.2.2.2.2
        have hfp1_x : foldedParent P t₁ e.x = e.z := hpop_law.1 e hr hst_eq
        have hintra_props : e ∈ b3Intra P proc chain →
            phiConfVertex P chain t₀ e.x = 1 ∧ e ∉ b1 P proc chain := by
          intro he_in
          unfold b3Intra at he_in
          rw [Finset.mem_filter] at he_in
          obtain ⟨_, hcond⟩ := he_in
          dsimp only at hcond
          split_ifs at hcond with hs2_bds
          obtain ⟨hs12_eq, hz_le_hi⟩ := hcond
          set kℓ : Fin (M + 1) := ⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le hs2_bds.2⟩
          have hℓ_lt_yz : kℓ.val < partSepScale P chain e.y e.z :=
            (lt_partSepScale_iff_le_hi hChain (by omega) (by omega) (by omega) kℓ).mpr hz_le_hi
          have hphi0_1 : phiConfVertex P chain t₀ e.x = 1 := by
            rw [phiConfVertex_eq, hfp0_x, hfp0_y]
            dsimp [kℓ] at hℓ_lt_yz
            simp [hs2_bds.1, hs2_bds.2, hℓ_lt_yz]
          have hnot_b1 : e ∉ b1 P proc chain := by
            rw [b1, Finset.mem_filter]
            rintro ⟨_, _, hlt, _⟩
            omega
          exact ⟨hphi0_1, hnot_b1⟩
        by_cases hjh : e.j = e.h
        · have htop1 : topInd e = 1 := by simp [topInd, hjh]
          have hphi1_le := phiConfVertex_le_one P chain t₁ e.x
          by_cases he_in : e ∈ b3Intra P proc chain
          · obtain ⟨hphi0_1, _⟩ := hintra_props he_in
            have hi1 : intraInd e = 1 := by simp [intraInd, he_in]
            omega
          · have hi0 : intraInd e = 0 := by simp [intraInd, he_in]
            omega
        · have hj_lt : e.j < e.h := by
            have := hp.2.2.2.2.2.2.1; omega
          have htop0 : topInd e = 0 := by simp [topInd, hjh]
          obtain ⟨eNext, hnext⟩ := nextCascadeRot?_isSome_of_j_lt_h proc hr hj_lt
          obtain ⟨hrN, hstN, hsN, _, _, _, hxN⟩ := nextCascadeRot?_some_props proc hr hnext
          have hrotN := h36_2.2 eNext hrN
          have hfp1_z : foldedParent P t₁ e.z = eNext.z := by
            rw [← hxN]
            exact hpop_law.1 eNext hrN (hstN.trans hst_eq)
          by_cases hphi1_eq1 : phiConfVertex P chain t₁ e.x = 1
          · have hcond1 : 1 ≤ partSepScale P chain e.x e.z ∧
                partSepScale P chain e.x e.z ≤ M ∧
                partSepScale P chain e.x e.z < partSepScale P chain e.z eNext.z := by
              rw [phiConfVertex_eq, hfp1_x, hfp1_z] at hphi1_eq1
              by_contra hc
              simp [hc] at hphi1_eq1
            have hsep_sz : partSepScale P chain eNext.s eNext.x ≤ partSepScale P chain e.x e.z := by
              rw [hsN, hxN, partSepScale_ultrametric_ord hChain (a := e.s) (b := e.x) (c := e.z)
                (by omega) (by omega) (by omega)]
              exact Nat.min_le_right _ _
            have hsep_zw : partSepScale P chain e.z eNext.z ≤ partSepScale P chain eNext.x eNext.y := by
              rw [← hxN, partSepScale_ultrametric_ord hChain (a := eNext.x) (b := eNext.y) (c := eNext.z)
                (by omega) (by omega) (by omega)]
              exact Nat.min_le_left _ _
            have hsN_bds := partSepScale_bounds (P := P) (chain := chain) (u := eNext.s) (v := eNext.x)
              (by omega) (by omega) (by omega) (by omega)
            have hxN_bds := partSepScale_bounds (P := P) (chain := chain) (u := eNext.x) (v := eNext.y)
              (by omega) (by omega) (by omega) (by omega)
            have heN_target : eNext ∈ b1 P proc chain ∪ bLeafPre P proc chain := by
              by_cases hN_M : partSepScale P chain eNext.x eNext.y ≤ M
              · exact Finset.mem_union_left _
                  (Finset.mem_filter.mpr ⟨hrN, hsN_bds.1, by omega, hN_M⟩)
              · have hN_M1 : partSepScale P chain eNext.x eNext.y = M + 1 := by omega
                refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrN, hN_M1, ?_⟩)
                exact (partSepScale_le_iff_lt_lo hChain (by omega) (by omega) (by omega)
                  (Fin.last M)).mp (by simp [Fin.last]; omega)
            by_cases he_in : e ∈ b3Intra P proc chain
            · obtain ⟨hphi0_1, hnot_b1⟩ := hintra_props he_in
              have he_enter : e ∈ eEnter P T proc chain := by
                unfold eEnter
                rw [Finset.mem_filter, Finset.mem_sdiff]
                refine ⟨⟨hr, fun hb1o => hnot_b1 (Finset.mem_sdiff.mp hb1o).1⟩, ?_⟩
                rw [hnext]
                exact decide_eq_true heN_target
              have hi1 : intraInd e = 1 := by simp [intraInd, he_in]
              have hen1 : enterInd e = 1 := by simp [enterInd, he_enter]
              omega
            · have hi0 : intraInd e = 0 := by simp [intraInd, he_in]
              by_cases hb1o : e ∈ b1 P proc chain \ s1Set P T proc chain
              · rw [Finset.mem_sdiff] at hb1o
                obtain ⟨he_b1, he_ns1⟩ := hb1o
                obtain ⟨_, hν_eq, _, hℓ2_le_m, hmend_M, _, hQ2_eq, _, _, _, _, _⟩ :=
                  b1_routing_bounds hT hChain h36_2.2 he_b1
                have hmend_raw : mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x)
                    (partSepScale P chain e.x e.y)) ≤ M := hν_eq ▸ hmend_M
                have hQ2_eq' : (b1Triple P T chain e).2.2 =
                    blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x)
                      (partSepScale P chain e.x e.y)), Nat.lt_succ_of_le hmend_raw⟩) e.y := by
                  rw [hQ2_eq]; congr 2; exact Fin.ext (congrArg (mEnd T) hν_eq)
                have hz_le_Q2 : e.z ≤ (b1Triple P T chain e).2.2.hi := by
                  by_contra hgt
                  apply he_ns1
                  unfold s1Set
                  rw [Finset.mem_filter]
                  refine ⟨he_b1, ?_⟩
                  dsimp only
                  simp only [hmend_raw, ↓reduceDIte, ← hQ2_eq']
                  exact Or.inl (by omega)
                have he_b1_cond := (Finset.mem_filter.mp he_b1).2
                set kℓ2 : Fin (M + 1) := ⟨partSepScale P chain e.x e.y,
                  Nat.lt_succ_of_le he_b1_cond.2.2⟩
                set km : Fin (M + 1) := ⟨_, Nat.lt_succ_of_le hmend_M⟩
                have hhi_sub := (nested_blockAt_sub hChain (k₁ := kℓ2) (k₂ := km)
                  (by dsimp [kℓ2, km]; exact hℓ2_le_m) (u := e.y) (by omega) (by omega)).2
                have hz_le_ℓ2 : e.z ≤ (blockAt (chain kℓ2) e.y).hi := by
                  rw [hQ2_eq] at hz_le_Q2
                  exact le_trans hz_le_Q2 hhi_sub
                have hℓ2_lt_yz : kℓ2.val < partSepScale P chain e.y e.z :=
                  (lt_partSepScale_iff_le_hi hChain (by omega) (by omega) (by omega) kℓ2).mpr hz_le_ℓ2
                have hphi0_1 : phiConfVertex P chain t₀ e.x = 1 := by
                  rw [phiConfVertex_eq, hfp0_x, hfp0_y]
                  dsimp [kℓ2] at hℓ2_lt_yz
                  simp [show 1 ≤ partSepScale P chain e.x e.y by omega, he_b1_cond.2.2, hℓ2_lt_yz]
                omega
              · have he_enter : e ∈ eEnter P T proc chain := by
                  unfold eEnter
                  rw [Finset.mem_filter, Finset.mem_sdiff]
                  refine ⟨⟨hr, hb1o⟩, ?_⟩
                  rw [hnext]
                  exact decide_eq_true heN_target
                have hen1 : enterInd e = 1 := by simp [enterInd, he_enter]
                omega
          · have hphi1_le := phiConfVertex_le_one P chain t₁ e.x
            have hphi1_0 : phiConfVertex P chain t₁ e.x = 0 := by omega
            by_cases he_in : e ∈ b3Intra P proc chain
            · obtain ⟨hphi0_1, _⟩ := hintra_props he_in
              have hi1 : intraInd e = 1 := by simp [intraInd, he_in]
              omega
            · have hi0 : intraInd e = 0 := by simp [intraInd, he_in]
              omega
      have hsum_top_le : (∑ e ∈ rotsAt, topInd e) ≤ 1 := by
        have htop_eq : (∑ e ∈ rotsAt, topInd e) = (rotsAt.filter (fun e => e.j = e.h)).card := by
          rw [Finset.card_filter]
        rw [htop_eq]
        refine Finset.card_le_one.mpr ?_
        intro e₁ he₁ e₂ he₂
        rw [Finset.mem_filter, Finset.mem_filter] at he₁ he₂
        have hst12 : e₁.stepIdx = e₂.stepIdx := he₁.1.2.trans he₂.1.2.symm
        have hh12 := (rInt_same_stepIdx_props proc hbst_all he₁.1.1 he₂.1.1 hst12).2.1
        exact rInt_ext_stepIdx_j proc he₁.1.1 he₂.1.1 hst12 (by omega)
      have hsum_intra : (∑ e ∈ rotsAt, intraInd e) =
          ((b3Intra P proc chain).filter (fun e => e.stepIdx = τ)).card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
        congr 1
        ext e
        simp only [rotsAt, Finset.mem_filter]
        exact ⟨fun ⟨⟨_, hst⟩, hb⟩ => ⟨hb, hst⟩,
          fun ⟨hb, hst⟩ => ⟨⟨(Finset.mem_filter.mp hb).1, hst⟩, hb⟩⟩
      have hsum_enter : (∑ e ∈ rotsAt, enterInd e) =
          ((eEnter P T proc chain).filter (fun e => e.stepIdx = τ)).card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
        congr 1
        ext e
        simp only [rotsAt, Finset.mem_filter]
        refine ⟨fun ⟨⟨_, hst⟩, he⟩ => ⟨he, hst⟩, fun ⟨he, hst⟩ => ⟨⟨?_, hst⟩, he⟩⟩
        unfold eEnter at he
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
      have hsum_phi1_X : (∑ v ∈ X_prom, phiConfVertex P chain t₁ v) =
          ∑ e ∈ rotsAt, phiConfVertex P chain t₁ e.x :=
        Finset.sum_image hx_inj
      have hsum_phi0_X : (∑ v ∈ X_prom, phiConfVertex P chain t₀ v) =
          ∑ e ∈ rotsAt, phiConfVertex P chain t₀ e.x :=
        Finset.sum_image hx_inj
      have hphi1_split : phiConf P chain t₁ =
          (∑ v ∈ X_prom, phiConfVertex P chain t₁ v) +
            (∑ v ∈ keyFinset t₁ \ X_prom, phiConfVertex P chain t₁ v) := by
        unfold phiConf
        rw [← Finset.sum_sdiff hX_sub_t1, add_comm]
      have hphi0_split : phiConf P chain t₀ =
          (∑ v ∈ X_prom, phiConfVertex P chain t₀ v) +
            (∑ v ∈ keyFinset t₀ \ X_prom, phiConfVertex P chain t₀ v) := by
        unfold phiConf
        rw [← Finset.sum_sdiff hX_sub_t0, add_comm]
      have hsdiff_sub : keyFinset t₁ \ X_prom ⊆ keyFinset t₀ \ X_prom := by
        intro a ha
        rw [Finset.mem_sdiff] at ha ⊢
        exact ⟨(Finset.mem_erase.mp (hprops.2.2 ▸ ha.1)).2, ha.2⟩
      have hnonprom_sum : (∑ v ∈ keyFinset t₁ \ X_prom, phiConfVertex P chain t₁ v) ≤
          (∑ v ∈ keyFinset t₀ \ X_prom, phiConfVertex P chain t₀ v) :=
        le_trans (Finset.sum_le_sum hnonprom_le)
          (Finset.sum_le_sum_of_subset hsdiff_sub)
      have hpt_sum := Finset.sum_le_sum hrot_ptwise
      simp only [Finset.sum_add_distrib] at hpt_sum
      omega
  have htele := telescope_range_le (a := stepGain) (b := stepCost)
    (Φ := fun τ => phiConf P chain (proc.treeAt τ)) proc.steps.length hlocal
  have hphi_start : phiConf P chain (proc.treeAt 0) = 0 := by
    simp [phiConf, treeAt_zero, keyFinset]
  have hphi_end : phiConf P chain (proc.treeAt proc.steps.length) = 0 := by
    simp [phiConf, treeAt_end, keyFinset]
  have hgain_sum : (∑ τ ∈ Finset.range proc.steps.length, stepGain τ) =
      (b3Intra P proc chain).card :=
    (card_eq_sum_range_stepIdx proc hbst_all (Finset.filter_subset _ _)).symm
  have henter_sum : (∑ τ ∈ Finset.range proc.steps.length,
      ((eEnter P T proc chain).filter (fun e => e.stepIdx = τ)).card) =
      (eEnter P T proc chain).card := by
    refine (card_eq_sum_range_stepIdx proc hbst_all ?_).symm
    intro e he
    unfold eEnter at he
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
  have hpush_sum : (∑ τ ∈ Finset.range proc.steps.length,
      match proc.steps[τ]? with | some op => if isPush op then 1 else 0 | none => 0) = P := by
    rw [sum_range_opt_ind_eq_filter_length isPush proc.steps,
      ← filterMap_length_eq_filter_length (f := pushKey?)
        (by intro op; cases op <;> rfl) proc.steps]
    exact proc.hPushCount
  have hurot_sum : (∑ τ ∈ Finset.range proc.steps.length,
      match proc.steps[τ]? with | some op => if isURot op then 1 else 0 | none => 0) =
      proc.kRot :=
    sum_range_opt_ind_eq_filter_length isURot proc.steps
  have hpop_sum : (∑ τ ∈ Finset.range proc.steps.length,
      match proc.steps[τ]? with | some op => if isPop op then 1 else 0 | none => 0) = P := by
    rw [sum_range_opt_ind_eq_filter_length isPop proc.steps,
      ← filterMap_length_eq_filter_length (f := popKey?)
        (by intro op; cases op <;> rfl) proc.steps]
    have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
    rw [hseq, List.length_range']
  dsimp only [stepCost] at htele
  simp only [Finset.sum_add_distrib] at htele
  rw [hgain_sum, hphi_start, hphi_end, hpush_sum, hurot_sum, hpop_sum, henter_sum] at htele
  omega

/-! ## Section 4: Lemma 5.6 (`lem_5_6_b3_escape`) -/

theorem list_nodup_map_sum_eq_toFinset_sum {α : Type} [DecidableEq α]
    {l : List α} (hn : l.Nodup) (f : α → ℕ) :
    (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hn
    simp [hn.1, ih hn.2]

theorem mem_treeAt_stay_until_pop {P : ℕ} (proc : FoldedPopProcess P)
    (hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P)
    {k : ℕ} (hk1 : 1 ≤ k) (hkP : k ≤ P)
    {τ₀ τ₁ : ℕ} (h01 : τ₀ ≤ τ₁) (h1pop : τ₁ ≤ proc.popStepIdx k)
    (hk0 : k ∈ keyFinset (proc.treeAt τ₀)) :
    k ∈ keyFinset (proc.treeAt τ₁) := by
  obtain ⟨hpop_lt, _⟩ := popStepIdx_spec proc hk1 hkP
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h01
  induction d with
  | zero => simpa using hk0
  | succ d ih =>
    set τ' := τ₀ + d
    have hstep_eq : τ₀ + (d + 1) = τ' + 1 := by omega
    have hτ'_pop : τ' < proc.popStepIdx k := by omega
    have hτ'_len : τ' < proc.steps.length := lt_trans hτ'_pop hpop_lt
    have hkin : k ∈ keyFinset (proc.treeAt τ') := ih (by omega) (le_of_lt hτ'_pop)
    have hprops := step_tree_props proc hbst_all hτ'_len
    rw [hstep_eq]
    cases hop : proc.steps[τ'] with
    | shift => rw [hop] at hprops; dsimp only at hprops; rwa [hprops]
    | upperRot u v => rw [hop] at hprops; dsimp only at hprops; rwa [hprops]
    | push w =>
      rw [hop] at hprops; dsimp only at hprops
      rw [hprops.2.2.1]
      exact Finset.mem_insert_of_mem hkin
    | pop s' =>
      rw [hop] at hprops; dsimp only at hprops
      obtain ⟨hs'1, hs'P, hτ'_eq⟩ := (getElem_eq_pop_iff proc hτ'_len).mp hop
      rw [hτ'_eq] at hτ'_pop
      have hs'_lt_k : s' < k := (popStepIdx_strictMono proc hs'1 hs'P hk1 hkP).mpr hτ'_pop
      rw [hprops.2.2, Finset.mem_erase]
      exact ⟨by omega, hkin⟩

theorem partSepScale_eq_succ_iff {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {u v : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P) (ℓ : Fin M) :
    partSepScale P chain u v = ℓ.val + 1 ↔
      blockAt (chain ℓ.castSucc) u = blockAt (chain ℓ.castSucc) v ∧
      blockAt (chain ℓ.succ) u ≠ blockAt (chain ℓ.succ) v := by
  have h1 := lt_partSepScale_iff hChain hu1 huP hv1 hvP ℓ.castSucc
  have h2 := lt_partSepScale_iff hChain hu1 huP hv1 hvP ℓ.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
  constructor
  · intro heq
    exact ⟨h1.mp (by omega), fun hfine => by have := h2.mpr hfine; omega⟩
  · rintro ⟨hcoarse, hfine⟩
    have hgt : ℓ.val < partSepScale P chain u v := h1.mpr hcoarse
    have hnlt : ¬ (ℓ.val + 1 < partSepScale P chain u v) := fun hlt => hfine (h2.mp hlt)
    omega

theorem subblock_pair_sepScale {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) (ℓ : Fin M)
    {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {c₁ c₂ : ℕ} (hc1 : 1 ≤ c₁) (hlt : c₁ < c₂)
    (hc2 : c₂ ≤ (childSubblocks (chain ℓ.succ) X).length)
    {u v : ℕ}
    (hu : u ∈ (subblock1 (childSubblocks (chain ℓ.succ) X) c₁).toFinset)
    (hv : v ∈ (subblock1 (childSubblocks (chain ℓ.succ) X) c₂).toFinset) :
    1 ≤ u ∧ u < v ∧ v ≤ P ∧
    blockAt (chain ℓ.castSucc) u = X ∧
    blockAt (chain ℓ.castSucc) v = X ∧
    blockAt (chain ℓ.succ) u = subblock1 (childSubblocks (chain ℓ.succ) X) c₁ ∧
    blockAt (chain ℓ.succ) v = subblock1 (childSubblocks (chain ℓ.succ) X) c₂ ∧
    partSepScale P chain u v = ℓ.val + 1 := by
  have hu_iff := (mem_subblock1_iff hChain ℓ hX hc1 (by omega)).mp hu
  have hv_iff := (mem_subblock1_iff hChain ℓ hX (by omega) hc2).mp hv
  obtain ⟨hX1, _, hXP⟩ := (hChain.2.2.1 ℓ.castSucc).1 X hX
  have hu_X := Finset.mem_Icc.mp hu_iff.1
  have hv_X := Finset.mem_Icc.mp hv_iff.1
  have hu1 : 1 ≤ u := le_trans hX1 hu_X.1
  have huP : u ≤ P := le_trans hu_X.2 hXP
  have hv1 : 1 ≤ v := le_trans hX1 hv_X.1
  have hvP : v ≤ P := le_trans hv_X.2 hXP
  have hX_u : blockAt (chain ℓ.castSucc) u = X :=
    (blockAt_eq_iff (hChain.2.2.1 ℓ.castSucc) hu1 huP hX).mpr hu_X
  have hX_v : blockAt (chain ℓ.castSucc) v = X :=
    (blockAt_eq_iff (hChain.2.2.1 ℓ.castSucc) hv1 hvP hX).mpr hv_X
  have hspec_u := subblockIndex1_spec hChain ℓ hX hu_iff.1
  have hspec_v := subblockIndex1_spec hChain ℓ hX hv_iff.1
  dsimp only at hspec_u hspec_v
  have hbu : blockAt (chain ℓ.succ) u = subblock1 (childSubblocks (chain ℓ.succ) X) c₁ := by
    rw [← hspec_u.2.2.1, hu_iff.2]
  have hbv : blockAt (chain ℓ.succ) v = subblock1 (childSubblocks (chain ℓ.succ) X) c₂ := by
    rw [← hspec_v.2.2.1, hv_iff.2]
  have hhi_lt := subblock1_hi_lt_lo hChain ℓ X hc1 hlt hc2
  dsimp only at hhi_lt
  have hu_b := Finset.mem_Icc.mp hu
  have hv_b := Finset.mem_Icc.mp hv
  have huv : u < v := by omega
  have hne_fine : blockAt (chain ℓ.succ) u ≠ blockAt (chain ℓ.succ) v := by
    rw [hbu, hbv]
    intro heq
    have hhi_eq : (subblock1 (childSubblocks (chain ℓ.succ) X) c₁).hi =
        (subblock1 (childSubblocks (chain ℓ.succ) X) c₂).hi := congrArg IntervalBlock.hi heq
    omega
  have hsep : partSepScale P chain u v = ℓ.val + 1 :=
    (partSepScale_eq_succ_iff hChain hu1 huP hv1 hvP ℓ).mpr ⟨hX_u.trans hX_v.symm, hne_fine⟩
  exact ⟨hu1, huv, hvP, hX_u, hX_v, hbu, hbv, hsep⟩

theorem mem_b3ExitAct_iff {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (e : InternalPopRot) :
    e ∈ b3ExitAct P proc chain ↔
      e ∈ proc.rInt ∧
      ∃ ℓ : Fin M,
        partSepScale P chain e.s e.x = ℓ.val + 1 ∧
        partSepScale P chain e.x e.y = ℓ.val + 1 ∧
        (blockAt (chain ℓ.succ) e.y).hi < e.z ∧
        e.stepIdx < tauEmpty proc (blockAt (chain ℓ.succ) e.s) := by
  unfold b3ExitAct b3Exit
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hr, hb3⟩, hact⟩
    split_ifs at hb3 with h12
    rcases hb3 with ⟨hs12, hhi⟩
    have h2M : partSepScale P chain e.x e.y ≤ M := h12.2
    simp only [h2M, ↓reduceDIte] at hact
    let ℓ : Fin M := ⟨partSepScale P chain e.x e.y - 1, by omega⟩
    have hval_eq : partSepScale P chain e.x e.y = ℓ.val + 1 := by dsimp only [ℓ]; omega
    have hsucc_eq : (⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le h12.2⟩ : Fin (M + 1)) =
        ℓ.succ := Fin.ext (by dsimp only; exact hval_eq)
    rw [hsucc_eq] at hhi hact
    exact ⟨hr, ℓ, hs12.trans hval_eq, hval_eq, hhi, hact⟩
  · rintro ⟨hr, ℓ, hs1, hs2, hhi, hact⟩
    have h12 : 1 ≤ partSepScale P chain e.x e.y ∧ partSepScale P chain e.x e.y ≤ M := by
      have := ℓ.isLt; omega
    have h2M : partSepScale P chain e.x e.y ≤ M := h12.2
    have hsucc_eq : (⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le h12.2⟩ : Fin (M + 1)) =
        ℓ.succ := Fin.ext (by dsimp only; exact hs2)
    refine ⟨⟨hr, ?_⟩, ?_⟩
    · simp only [h12, and_self, ↓reduceDIte]
      exact ⟨hs1.trans hs2.symm, by rw [hsucc_eq]; exact hhi⟩
    · simp only [h2M, ↓reduceDIte]
      rw [hsucc_eq]; exact hact

theorem vXp_cell_spec {M P : ℕ} {proc : FoldedPopProcess P}
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (h36_2_rot : ∀ e ∈ proc.rInt,
      1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P ∧
      (∀ τ' ∈ Finset.Ico (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w : ℕ, proc.steps[τ']? = some (.push w) → w < e.x) ∧
      (∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z)))
    (ℓ : Fin M) {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1))
    {e : InternalPopRot} (he : e ∈ vXp P proc chain (ℓ.val + 1) X p) :
    let subs := childSubblocks (chain ℓ.succ) X
    let b := subblockIndex1 subs e.x
    let q := subblockIndex1 subs e.y
    e ∈ b3ExitAct P proc chain ∧
    e ∈ proc.rInt ∧
    partSepScale P chain e.s e.x = ℓ.val + 1 ∧
    partSepScale P chain e.x e.y = ℓ.val + 1 ∧
    blockAt (chain ℓ.castSucc) e.s = X ∧
    blockAt (chain ℓ.castSucc) e.x = X ∧
    blockAt (chain ℓ.castSucc) e.y = X ∧
    subblockIndex1 subs e.s = p ∧
    1 ≤ p ∧ p < b ∧ b < q ∧ q ≤ subs.length ∧
    e.s ∈ (subblock1 subs p).toFinset ∧
    e.x ∈ (subblock1 subs b).toFinset ∧
    e.y ∈ (subblock1 subs q).toFinset ∧
    blockAt (chain ℓ.succ) e.s = subblock1 subs p ∧
    blockAt (chain ℓ.succ) e.x = subblock1 subs b ∧
    blockAt (chain ℓ.succ) e.y = subblock1 subs q ∧
    (subblock1 subs q).hi < e.z ∧
    e.stepIdx < tauEmpty proc (subblock1 subs p) := by
  have hℓ_bds : 1 ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  unfold vXp at he
  simp only [hℓ_bds, and_self, ↓reduceDIte, Finset.mem_filter] at he
  have hsucc_eq : (⟨ℓ.val + 1, Nat.lt_succ_of_le hℓ_bds.2⟩ : Fin (M + 1)) = ℓ.succ :=
    Fin.ext rfl
  rw [hsucc_eq] at he
  rcases he with ⟨he_act, hsep_xy, hs_Sp⟩
  obtain ⟨hr, ℓ', hs1_eq, hs2_eq, hhi_z, hact⟩ :=
    (mem_b3ExitAct_iff P proc chain e).mp he_act
  have hℓ'_eq : ℓ' = ℓ := Fin.ext (by omega)
  subst ℓ'
  obtain ⟨hs1_b, hsx, hxy, hyz, hzP, _, _⟩ := h36_2_rot e hr
  have hp_bds := Finset.mem_Icc.mp hp
  have hs_iff := (mem_subblock1_iff hChain ℓ hX hp_bds.1 (by omega)).mp hs_Sp
  obtain ⟨hX1, _, hXP⟩ := (hChain.2.2.1 ℓ.castSucc).1 X hX
  have hX_s : blockAt (chain ℓ.castSucc) e.s = X :=
    (blockAt_eq_iff (hChain.2.2.1 ℓ.castSucc) hs1_b (by omega) hX).mpr (Finset.mem_Icc.mp hs_iff.1)
  obtain ⟨hsx_coarse, hsx_fine⟩ :=
    (partSepScale_eq_succ_iff hChain hs1_b (by omega) (by omega) (by omega) ℓ).mp hs1_eq
  obtain ⟨hxy_coarse, hxy_fine⟩ :=
    (partSepScale_eq_succ_iff hChain (by omega) (by omega) (by omega) (by omega) ℓ).mp hs2_eq
  have hX_x : blockAt (chain ℓ.castSucc) e.x = X := hsx_coarse.symm.trans hX_s
  have hX_y : blockAt (chain ℓ.castSucc) e.y = X := hxy_coarse.symm.trans hX_x
  have hx_X : e.x ∈ X.toFinset := by
    obtain ⟨_, hlo, hhi⟩ := blockAt_mem_and_bounds (hChain.2.2.1 ℓ.castSucc)
      (u := e.x) (by omega) (by omega)
    rw [hX_x] at hlo hhi
    exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  have hy_X : e.y ∈ X.toFinset := by
    obtain ⟨_, hlo, hhi⟩ := blockAt_mem_and_bounds (hChain.2.2.1 ℓ.castSucc)
      (u := e.y) (by omega) (by omega)
    rw [hX_y] at hlo hhi
    exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  have hspec_s := subblockIndex1_spec hChain ℓ hX hs_iff.1
  have hspec_x := subblockIndex1_spec hChain ℓ hX hx_X
  have hspec_y := subblockIndex1_spec hChain ℓ hX hy_X
  dsimp only at hspec_s hspec_x hspec_y ⊢
  have hbs : blockAt (chain ℓ.succ) e.s = subblock1 (childSubblocks (chain ℓ.succ) X) p := by
    rw [← hspec_s.2.2.1, hs_iff.2]
  have hbx : blockAt (chain ℓ.succ) e.x =
      subblock1 (childSubblocks (chain ℓ.succ) X) (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x) :=
    hspec_x.2.2.1.symm
  have hby : blockAt (chain ℓ.succ) e.y =
      subblock1 (childSubblocks (chain ℓ.succ) X) (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.y) :=
    hspec_y.2.2.1.symm
  have hpb : p < subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x := by
    rcases lt_trichotomy p (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x) with hlt | heq | hgt
    · exact hlt
    · exfalso; apply hsx_fine; rw [hbs, hbx, heq]
    · exfalso
      have h1 := subblock1_hi_lt_lo hChain ℓ X hspec_x.1 hgt (by omega)
      dsimp only at h1
      have h2 := Finset.mem_Icc.mp hs_Sp
      have h3 := Finset.mem_Icc.mp hspec_x.2.2.2
      omega
  have hbq : subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x <
      subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.y := by
    rcases lt_trichotomy
        (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x)
        (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.y) with hlt | heq | hgt
    · exact hlt
    · exfalso; apply hxy_fine; rw [hbx, hby, heq]
    · exfalso
      have h1 := subblock1_hi_lt_lo hChain ℓ X hspec_y.1 hgt hspec_x.2.1
      dsimp only at h1
      have h2 := Finset.mem_Icc.mp hspec_x.2.2.2
      have h3 := Finset.mem_Icc.mp hspec_y.2.2.2
      omega
  rw [hby] at hhi_z
  rw [hbs] at hact
  exact ⟨he_act, hr, hs1_eq, hs2_eq, hX_s, hX_x, hX_y, hs_iff.2,
    hp_bds.1, hpb, hbq, hspec_y.2.1, hs_Sp, hspec_x.2.2.2, hspec_y.2.2.2,
    hbs, hbx, hby, hhi_z, hact⟩

theorem mem_vXp_of_b3ExitAct {M P : ℕ} {proc : FoldedPopProcess P}
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (h36_2_rot : ∀ e ∈ proc.rInt,
      1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P ∧
      (∀ τ' ∈ Finset.Ico (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w : ℕ, proc.steps[τ']? = some (.push w) → w < e.x) ∧
      (∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z)))
    {e : InternalPopRot} (he : e ∈ b3ExitAct P proc chain) :
    ∃ (ℓ : Fin M) (X : IntervalBlock),
      X ∈ chain ℓ.castSucc ∧
      ∃ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
        e ∈ vXp P proc chain (ℓ.val + 1) X p := by
  obtain ⟨hr, ℓ, hs1_eq, hs2_eq, _, _⟩ := (mem_b3ExitAct_iff P proc chain e).mp he
  obtain ⟨hs1_b, hsx, hxy, hyz, hzP, _, _⟩ := h36_2_rot e hr
  obtain ⟨hX_mem, hX_lo, hX_hi⟩ := blockAt_mem_and_bounds (hChain.2.2.1 ℓ.castSucc)
    (u := e.s) hs1_b (by omega)
  set X := blockAt (chain ℓ.castSucc) e.s
  have hs_X : e.s ∈ X.toFinset := Finset.mem_Icc.mpr ⟨hX_lo, hX_hi⟩
  obtain ⟨hsx_coarse, hsx_fine⟩ :=
    (partSepScale_eq_succ_iff hChain hs1_b (by omega) (by omega) (by omega) ℓ).mp hs1_eq
  have hx_X : e.x ∈ X.toFinset := by
    obtain ⟨_, hlo, hhi⟩ := blockAt_mem_and_bounds (hChain.2.2.1 ℓ.castSucc)
      (u := e.x) (by omega) (by omega)
    rw [← hsx_coarse] at hlo hhi
    exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  have hspec_s := subblockIndex1_spec hChain ℓ hX_mem hs_X
  have hspec_x := subblockIndex1_spec hChain ℓ hX_mem hx_X
  dsimp only at hspec_s hspec_x
  have hpb : subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.s <
      subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x := by
    rcases lt_trichotomy
        (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.s)
        (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x) with hlt | heq | hgt
    · exact hlt
    · exfalso; apply hsx_fine; rw [← hspec_s.2.2.1, ← hspec_x.2.2.1, heq]
    · exfalso
      have h1 := subblock1_hi_lt_lo hChain ℓ X hspec_x.1 hgt hspec_s.2.1
      dsimp only at h1
      have h2 := Finset.mem_Icc.mp hspec_s.2.2.2
      have h3 := Finset.mem_Icc.mp hspec_x.2.2.2
      omega
  refine ⟨ℓ, X, hX_mem, subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.s,
    Finset.mem_Icc.mpr ⟨hspec_s.1, by omega⟩, ?_⟩
  have hℓ_bds : 1 ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  unfold vXp
  simp only [hℓ_bds, and_self, ↓reduceDIte, Finset.mem_filter]
  have hsucc_eq : (⟨ℓ.val + 1, Nat.lt_succ_of_le hℓ_bds.2⟩ : Fin (M + 1)) = ℓ.succ :=
    Fin.ext rfl
  rw [hsucc_eq]
  exact ⟨he, hs2_eq, hspec_s.2.2.2⟩

theorem b3_z_le_y_and_same_scale {M P : ℕ} (hP : 1 ≤ P)
    (h_3_6 : Ty_lem_3_6) (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    {e₁ e₂ : InternalPopRot}
    (he₁ : e₁ ∈ b3 P proc chain) (he₂ : e₂ ∈ b3 P proc chain)
    (hx_eq : e₁.x = e₂.x) (hlt : e₁.stepIdx < e₂.stepIdx) :
    e₁.z ≤ e₂.y ∧
    partSepScale P chain e₁.x e₁.y = partSepScale P chain e₂.x e₂.y := by
  obtain ⟨h36_1, h36_2, _⟩ := h_3_6 P hP proc
  have hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(h36_1.1 τ hτ).1, (h36_1.1 τ hτ).2.1⟩
  rw [b3, Finset.mem_filter] at he₁ he₂
  rcases he₁ with ⟨hr₁, _, hs12_1, _⟩
  rcases he₂ with ⟨hr₂, _, hs12_2, _⟩
  have hp₁ := rInt_props proc hbst_all hr₁
  have hp₂ := rInt_props proc hbst_all hr₂
  obtain ⟨hs1_1, hsx1, hxy1, hyz1, hzP1, _, _⟩ := h36_2.2 e₁ hr₁
  obtain ⟨hs1_2, hsx2, hxy2, hyz2, hzP2, _, _⟩ := h36_2.2 e₂ hr₂
  have hs_lt : e₁.s < e₂.s := by
    rw [hp₁.2.2.2.2.1, hp₂.2.2.2.2.1] at hlt
    exact (popStepIdx_strictMono proc hs1_1 (by omega) hs1_2 (by omega)).mpr hlt
  have hx_mem1_next : e₁.x ∈ proc.treeAt (e₁.stepIdx + 1) := by
    have hprops := step_tree_props proc hbst_all hp₁.1
    obtain ⟨hop1⟩ : ∃ hop : proc.steps[e₁.stepIdx] = .pop e₁.s, True := by
      have h := hp₁.2.1
      rw [List.getElem?_eq_getElem hp₁.1, Option.some.injEq] at h
      exact ⟨h, trivial⟩
    rw [hop1] at hprops; dsimp only at hprops
    rw [← mem_keyFinset_iff, hprops.2.2, Finset.mem_erase]
    exact ⟨by omega, mem_keyFinset_iff.mpr (mem_of_mem_leftSpine hp₁.2.2.2.2.2.2.2.1)⟩
  have hx_mem2 : e₁.x ∈ proc.treeAt e₂.stepIdx := by
    rw [hx_eq]
    exact mem_of_mem_leftSpine hp₂.2.2.2.2.2.2.2.1
  have hpop1_law := h36_1.2.2.1 e₁.s hs1_1 (by omega)
  dsimp only at hpop1_law
  rw [← hp₁.2.2.2.2.1] at hpop1_law
  have hfp1 : foldedParent P (proc.treeAt (e₁.stepIdx + 1)) e₁.x = e₁.z :=
    hpop1_law.1 e₁ hr₁ rfl
  have hfp2 : foldedParent P (proc.treeAt e₂.stepIdx) e₁.x = e₂.y := by
    rw [hx_eq]
    exact hp₂.2.2.2.2.2.2.2.2.2.2.1
  have hmono := (h36_1.2.2.2 (e₁.stepIdx + 1) e₂.stepIdx e₁.x (by omega)
    (le_of_lt hp₂.1) hx_mem1_next hx_mem2).1
  rw [hfp1, hfp2] at hmono
  have hle1 : partSepScale P chain e₁.x e₁.y ≤ partSepScale P chain e₂.x e₂.y := by
    rw [← hs12_1, ← hs12_2, ← hx_eq,
      partSepScale_ultrametric_ord hChain (a := e₁.s) (b := e₂.s) (c := e₁.x)
        hs1_1 (le_of_lt hs_lt) (by omega)]
    exact Nat.min_le_right _ _
  have hle2 : partSepScale P chain e₂.x e₂.y ≤ partSepScale P chain e₁.x e₁.y := by
    rw [← hx_eq,
      partSepScale_ultrametric_ord hChain (a := e₁.x) (b := e₁.y) (c := e₂.y)
        (by omega) (le_of_lt hxy1) (by omega)]
    exact Nat.min_le_left _ _
  exact ⟨hmono, le_antisymm hle1 hle2⟩

theorem vXp_displaced_subblock_inj {M P : ℕ} (hP : 1 ≤ P)
    (h_3_6 : Ty_lem_3_6) (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (ℓ : Fin M) {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1))
    {e₁ e₂ : InternalPopRot}
    (he₁ : e₁ ∈ vXp P proc chain (ℓ.val + 1) X p)
    (he₂ : e₂ ∈ vXp P proc chain (ℓ.val + 1) X p)
    (hq_eq : subblockIndex1 (childSubblocks (chain ℓ.succ) X) e₁.y =
      subblockIndex1 (childSubblocks (chain ℓ.succ) X) e₂.y) :
    e₁ = e₂ := by
  obtain ⟨h36_1, h36_2, _⟩ := h_3_6 P hP proc
  have hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(h36_1.1 τ hτ).1, (h36_1.1 τ hτ).2.1⟩
  have hsp1 := vXp_cell_spec hChain h36_2.2 ℓ hX hp he₁
  have hsp2 := vXp_cell_spec hChain h36_2.2 ℓ hX hp he₂
  dsimp only at hsp1 hsp2
  have hr₁ := hsp1.2.1
  have hr₂ := hsp2.2.1
  have hp₁ := rInt_props proc hbst_all hr₁
  have hp₂ := rInt_props proc hbst_all hr₂
  have hrot1 := h36_2.2 e₁ hr₁
  have hrot2 := h36_2.2 e₂ hr₂
  rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with hlt | hstep_eq | hgt
  · exfalso
    have hSp_lt_Sb1 := subblock1_hi_lt_lo hChain ℓ X hsp1.2.2.2.2.2.2.2.2.1
      hsp1.2.2.2.2.2.2.2.2.2.1 (by omega)
    have hSb1_lt_Sq := subblock1_hi_lt_lo hChain ℓ X (by omega)
      hsp1.2.2.2.2.2.2.2.2.2.2.1 hsp1.2.2.2.2.2.2.2.2.2.2.2.1
    dsimp only at hSp_lt_Sb1 hSb1_lt_Sq
    have hs2_b := Finset.mem_Icc.mp hsp2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hx1_b := Finset.mem_Icc.mp hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hy2_Sq : e₂.y ∈ (subblock1 (childSubblocks (chain ℓ.succ) X)
        (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e₁.y)).toFinset := by
      rw [hq_eq]; exact hsp2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hy2_b := Finset.mem_Icc.mp hy2_Sq
    have hz1_gt := hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hidx_lt : e₂.stepIdx < proc.popStepIdx e₁.x := by
      rw [hp₂.2.2.2.2.1]
      exact (popStepIdx_strictMono proc (by omega) (by omega) (by omega) (by omega)).mp (by omega)
    have hwin : e₂.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact hrot1.2.2.2.2.2.2 e₂.stepIdx hwin e₂.y hp₂.2.2.2.2.2.2.2.2.1 ⟨by omega, by omega⟩
  · have hsame := rInt_same_stepIdx_props proc hbst_all hr₁ hr₂ hstep_eq
    rcases lt_trichotomy e₁.j e₂.j with hj_lt | hj_eq | hj_gt
    · exfalso
      have hz_le_x := hsame.2.2.1 hj_lt
      have hy2_Sq : e₂.y ∈ (subblock1 (childSubblocks (chain ℓ.succ) X)
          (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e₁.y)).toFinset := by
        rw [hq_eq]; exact hsp2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hy2_b := Finset.mem_Icc.mp hy2_Sq
      have hz1_gt := hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      omega
    · exact rInt_ext_stepIdx_j proc hr₁ hr₂ hstep_eq hj_eq
    · exfalso
      have hz_le_x := (rInt_same_stepIdx_props proc hbst_all hr₂ hr₁ hstep_eq.symm).2.2.1 hj_gt
      have hy1_Sq : e₁.y ∈ (subblock1 (childSubblocks (chain ℓ.succ) X)
          (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e₂.y)).toFinset := by
        rw [← hq_eq]; exact hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hy1_b := Finset.mem_Icc.mp hy1_Sq
      have hz2_gt := hsp2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      omega
  · exfalso
    have hSp_lt_Sb2 := subblock1_hi_lt_lo hChain ℓ X hsp2.2.2.2.2.2.2.2.2.1
      hsp2.2.2.2.2.2.2.2.2.2.1 (by omega)
    have hSb2_lt_Sq := subblock1_hi_lt_lo hChain ℓ X (by omega)
      hsp2.2.2.2.2.2.2.2.2.2.2.1 hsp2.2.2.2.2.2.2.2.2.2.2.2.1
    dsimp only at hSp_lt_Sb2 hSb2_lt_Sq
    have hs1_b := Finset.mem_Icc.mp hsp1.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hx2_b := Finset.mem_Icc.mp hsp2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hy1_Sq : e₁.y ∈ (subblock1 (childSubblocks (chain ℓ.succ) X)
        (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e₂.y)).toFinset := by
      rw [← hq_eq]; exact hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hy1_b := Finset.mem_Icc.mp hy1_Sq
    have hz2_gt := hsp2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hidx_lt : e₁.stepIdx < proc.popStepIdx e₂.x := by
      rw [hp₁.2.2.2.2.1]
      exact (popStepIdx_strictMono proc (by omega) (by omega) (by omega) (by omega)).mp (by omega)
    have hwin : e₁.stepIdx ∈ Finset.Icc (e₂.stepIdx + 1) (proc.popStepIdx e₂.x) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact hrot2.2.2.2.2.2.2 e₁.stepIdx hwin e₁.y hp₁.2.2.2.2.2.2.2.2.1 ⟨by omega, by omega⟩

theorem promoted_and_leadExitSet_props {M P : ℕ} (hP : 1 ≤ P)
    (h_3_6 : Ty_lem_3_6) (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (ℓ : Fin M) {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)) :
    (promotedSubblockIndices P proc chain (ℓ.val + 1) X p).card ≤
      (leadExitSet P proc chain (ℓ.val + 1) X p).card ∧
    (∀ e ∈ vXp P proc chain (ℓ.val + 1) X p \ leadExitSet P proc chain (ℓ.val + 1) X p,
      ∃ e₁ ∈ leadExitSet P proc chain (ℓ.val + 1) X p,
        e₁ ∈ vXp P proc chain (ℓ.val + 1) X p ∧
        subblockIndex1 (childSubblocks (chain ℓ.succ) X) e₁.x =
          subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x ∧
        e₁.stepIdx < e.stepIdx) := by
  obtain ⟨h36_1, h36_2, _⟩ := h_3_6 P hP proc
  have hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(h36_1.1 τ hτ).1, (h36_1.1 τ hτ).2.1⟩
  have hℓ_bds : 1 ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  have hsucc_eq : (⟨ℓ.val + 1, Nat.lt_succ_of_le hℓ_bds.2⟩ : Fin (M + 1)) = ℓ.succ :=
    Fin.ext rfl
  have hex_lead : ∀ b ∈ promotedSubblockIndices P proc chain (ℓ.val + 1) X p,
      ∃ e₀ ∈ leadExitSet P proc chain (ℓ.val + 1) X p,
        e₀ ∈ vXp P proc chain (ℓ.val + 1) X p ∧
        e₀.x ∈ (subblock1 (childSubblocks (chain ℓ.succ) X) b).toFinset ∧
        subblockIndex1 (childSubblocks (chain ℓ.succ) X) e₀.x = b ∧
        (∀ e' ∈ vXp P proc chain (ℓ.val + 1) X p,
          e'.x ∈ (subblock1 (childSubblocks (chain ℓ.succ) X) b).toFinset →
          e₀.stepIdx < e'.stepIdx ∨ (e₀.stepIdx = e'.stepIdx ∧ e₀.j ≤ e'.j)) := by
    intro b hb
    have hb_raw := hb
    unfold promotedSubblockIndices at hb_raw
    simp only [hℓ_bds, and_self, ↓reduceDIte, hsucc_eq, Finset.mem_filter] at hb_raw
    rcases hb_raw with ⟨hb_Icc, e_wit, he_wit_v, he_wit_Sb⟩
    let cands := (vXp P proc chain (ℓ.val + 1) X p).filter
      (fun e => e.x ∈ (subblock1 (childSubblocks (chain ℓ.succ) X) b).toFinset)
    have hne_c : cands.Nonempty := ⟨e_wit, Finset.mem_filter.mpr ⟨he_wit_v, he_wit_Sb⟩⟩
    let τ_min := (cands.image InternalPopRot.stepIdx).min' (hne_c.image _)
    have hτ_mem : τ_min ∈ cands.image InternalPopRot.stepIdx := Finset.min'_mem _ _
    obtain ⟨e_τ, he_τ_c, he_τ_eq⟩ := Finset.mem_image.mp hτ_mem
    let cands_τ := cands.filter (fun e => e.stepIdx = τ_min)
    have hne_τ : cands_τ.Nonempty := ⟨e_τ, Finset.mem_filter.mpr ⟨he_τ_c, he_τ_eq⟩⟩
    let j_min := (cands_τ.image InternalPopRot.j).min' (hne_τ.image _)
    have hj_mem : j_min ∈ cands_τ.image InternalPopRot.j := Finset.min'_mem _ _
    obtain ⟨e₀, he₀_cτ, he₀_j⟩ := Finset.mem_image.mp hj_mem
    obtain ⟨he₀_c, he₀_τ⟩ := Finset.mem_filter.mp he₀_cτ
    obtain ⟨he₀_v, he₀_Sb⟩ := Finset.mem_filter.mp he₀_c
    have hlex : ∀ e' ∈ cands,
        e₀.stepIdx < e'.stepIdx ∨ (e₀.stepIdx = e'.stepIdx ∧ e₀.j ≤ e'.j) := by
      intro e' he'
      have hτ_le : τ_min ≤ e'.stepIdx :=
        Finset.min'_le _ _ (Finset.mem_image_of_mem _ he')
      rcases eq_or_lt_of_le hτ_le with hτ_eq | hτ_lt
      · right
        refine ⟨he₀_τ.trans hτ_eq, ?_⟩
        rw [he₀_j]
        exact Finset.min'_le _ _ (Finset.mem_image_of_mem _
          (Finset.mem_filter.mpr ⟨he', hτ_eq.symm⟩))
      · left; omega
    have he₀_lead : e₀ ∈ leadExitSet P proc chain (ℓ.val + 1) X p := by
      unfold leadExitSet
      simp only [hℓ_bds, and_self, ↓reduceDIte, hsucc_eq, Finset.mem_biUnion]
      exact ⟨b, hb, Finset.mem_filter.mpr ⟨he₀_c, hlex⟩⟩
    have hb_bds := Finset.mem_Icc.mp hb_Icc
    have hb_idx := ((mem_subblock1_iff hChain ℓ hX (by omega) hb_bds.2).mp he₀_Sb).2
    refine ⟨e₀, he₀_lead, he₀_v, he₀_Sb, hb_idx, fun e' he'_v he'_Sb => ?_⟩
    exact hlex e' (Finset.mem_filter.mpr ⟨he'_v, he'_Sb⟩)
  constructor
  · classical
    let f : ℕ → InternalPopRot := fun b =>
      if hb : b ∈ promotedSubblockIndices P proc chain (ℓ.val + 1) X p then
        (hex_lead b hb).choose
      else ⟨0, 0, 0, 0, 0, 0, 0⟩
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro b hb
      rw [Finset.mem_coe] at hb ⊢
      simp only [f, hb, ↓reduceDIte]
      exact (hex_lead b hb).choose_spec.1
    · intro b₁ hb₁ b₂ hb₂ hfeq
      rw [Finset.mem_coe] at hb₁ hb₂
      simp only [f, hb₁, hb₂, ↓reduceDIte] at hfeq
      have h1 := (hex_lead b₁ hb₁).choose_spec.2.2.2.1
      have h2 := (hex_lead b₂ hb₂).choose_spec.2.2.2.1
      rw [hfeq] at h1
      exact h1.symm.trans h2
  · intro e he_diff
    rw [Finset.mem_sdiff] at he_diff
    rcases he_diff with ⟨he_v, he_not_lead⟩
    have hsp := vXp_cell_spec hChain h36_2.2 ℓ hX hp he_v
    dsimp only at hsp
    let b := subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x
    have hb_prom : b ∈ promotedSubblockIndices P proc chain (ℓ.val + 1) X p := by
      unfold promotedSubblockIndices
      simp only [hℓ_bds, and_self, ↓reduceDIte, hsucc_eq, Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨by have := hsp.2.2.2.2.2.2.2.2.2.1; omega,
        by have := hsp.2.2.2.2.2.2.2.2.2.2.1; have := hsp.2.2.2.2.2.2.2.2.2.2.2.1; omega⟩,
        e, he_v, hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    obtain ⟨e₁, he₁_lead, he₁_v, _, he₁_b, he₁_lex⟩ := hex_lead b hb_prom
    refine ⟨e₁, he₁_lead, he₁_v, he₁_b, ?_⟩
    rcases he₁_lex e he_v hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hlt | ⟨hstep_eq, hj_le⟩
    · exact hlt
    · exfalso
      have hsp1 := vXp_cell_spec hChain h36_2.2 ℓ hX hp he₁_v
      dsimp only at hsp1
      rcases eq_or_lt_of_le hj_le with hj_eq | hj_lt
      · have heq := rInt_ext_stepIdx_j proc hsp1.2.1 hsp.2.1 hstep_eq hj_eq
        exact he_not_lead (heq ▸ he₁_lead)
      · have hsame := rInt_same_stepIdx_props proc hbst_all hsp1.2.1 hsp.2.1 hstep_eq
        have hz_le_x := hsame.2.2.1 hj_lt
        have hSb_lt_Sq1 := subblock1_hi_lt_lo hChain ℓ X (by omega)
          hsp1.2.2.2.2.2.2.2.2.2.2.1 hsp1.2.2.2.2.2.2.2.2.2.2.2.1
        dsimp only at hSb_lt_Sq1
        rw [he₁_b] at hSb_lt_Sq1
        have hx_b := Finset.mem_Icc.mp hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hy1_b := Finset.mem_Icc.mp hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hz1_gt := hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        dsimp only [b] at hSb_lt_Sq1
        omega

theorem nonlead_active_window_props {M P : ℕ} (hP : 1 ≤ P)
    (h_3_6 : Ty_lem_3_6) (proc : FoldedPopProcess P)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    {eL eR : InternalPopRot → InternalPopRot}
    (heLR : ∀ e ∈ proc.rInt \ proc.mBase,
      eL e ∈ proc.rInt ∧ eR e ∈ proc.rInt ∧
      proc.nextCascadeRot? (eL e) = some (eR e) ∧
      (eL e).s = (eR e).s ∧ (eL e).s < e.s ∧
      (∀ e' ∈ proc.rInt, e'.x = e.x → e'.s < e.s → e'.s ≤ (eL e).s) ∧
      (eL e).x = e.x ∧ (eL e).z = e.y ∧ (eR e).x = e.y ∧
      (eL e).s < e.x ∧ e.x < (eL e).y ∧ (eL e).y < e.y ∧ e.y < (eR e).y ∧ (eR e).y < (eR e).z)
    (ℓ : Fin M) {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1))
    {e : InternalPopRot}
    (he_nl : e ∈ vXp P proc chain (ℓ.val + 1) X p \ leadExitSet P proc chain (ℓ.val + 1) X p)
    (he_nb : e ∉ proc.mBase) :
    let subs := childSubblocks (chain ℓ.succ) X
    (eR e).s ∈ (subblock1 subs p).toFinset ∧
    (eR e).stepIdx < e.stepIdx ∧
    (eR e).stepIdx < tauEmpty proc (subblock1 subs p) ∧
    partSepScale P chain (eR e).s (eR e).x = ℓ.val + 1 := by
  obtain ⟨h36_1, h36_2, _⟩ := h_3_6 P hP proc
  have hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(h36_1.1 τ hτ).1, (h36_1.1 τ hτ).2.1⟩
  have he_v : e ∈ vXp P proc chain (ℓ.val + 1) X p := (Finset.mem_sdiff.mp he_nl).1
  have hsp := vXp_cell_spec hChain h36_2.2 ℓ hX hp he_v
  dsimp only at hsp ⊢
  obtain ⟨e₁, _, he₁_v, he₁_b_eq, he₁_step_lt⟩ :=
    (promoted_and_leadExitSet_props hP h_3_6 proc hChain ℓ hX hp).2 e he_nl
  have hsp1 := vXp_cell_spec hChain h36_2.2 ℓ hX hp he₁_v
  dsimp only at hsp1
  have hr_diff : e ∈ proc.rInt \ proc.mBase := Finset.mem_sdiff.mpr ⟨hsp.2.1, he_nb⟩
  obtain ⟨hrL, hrR, _, hsLR, hsL_lt_s, hmax_L, hxL, hzL, hxR, _, _, _, _, _⟩ := heLR e hr_diff
  have hp_e := rInt_props proc hbst_all hsp.2.1
  have hp_e1 := rInt_props proc hbst_all hsp1.2.1
  have hp_L := rInt_props proc hbst_all hrL
  have hp_R := rInt_props proc hbst_all hrR
  have hs1_lt_s : e₁.s < e.s := by
    rw [hp_e1.2.2.2.2.1, hp_e.2.2.2.2.1] at he₁_step_lt
    exact (popStepIdx_strictMono proc hp_e1.2.2.1 hp_e1.2.2.2.1 hp_e.2.2.1 hp_e.2.2.2.1).mpr
      he₁_step_lt
  have hs_Sp_b := Finset.mem_Icc.mp hsp.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hs1_Sp_b := Finset.mem_Icc.mp hsp1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlo_le_tL : (subblock1 (childSubblocks (chain ℓ.succ) X) p).lo ≤ (eL e).s := by
    by_cases hxeq : e₁.x = e.x
    · exact le_trans hs1_Sp_b.1 (hmax_L e₁ hsp1.2.1 hxeq hs1_lt_s)
    · have hSb_lt_Sq1 := subblock1_hi_lt_lo hChain ℓ X (by omega)
        hsp1.2.2.2.2.2.2.2.2.2.2.1 hsp1.2.2.2.2.2.2.2.2.2.2.2.1
      have hSb_lt_Sq := subblock1_hi_lt_lo hChain ℓ X (by omega)
        hsp.2.2.2.2.2.2.2.2.2.2.1 hsp.2.2.2.2.2.2.2.2.2.2.2.1
      have hSp_lt_Sb := subblock1_hi_lt_lo hChain ℓ X hsp.2.2.2.2.2.2.2.2.1
        hsp.2.2.2.2.2.2.2.2.2.1 (by omega)
      dsimp only at hSb_lt_Sq1 hSb_lt_Sq hSp_lt_Sb
      rw [he₁_b_eq] at hSb_lt_Sq1
      have hx_Sb_b := Finset.mem_Icc.mp hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hx1_Sb : e₁.x ∈ (subblock1 (childSubblocks (chain ℓ.succ) X)
          (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.x)).toFinset := by
        rw [← he₁_b_eq]; exact hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hx1_Sb_b := Finset.mem_Icc.mp hx1_Sb
      have hy1_Sq1_b := Finset.mem_Icc.mp hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hy_Sq_b := Finset.mem_Icc.mp hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hz1_gt := hsp1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hx_lt_x1 : e.x < e₁.x := by
        by_contra hnlt
        have hx1_lt_x : e₁.x < e.x := by omega
        have hidx_lt : e.stepIdx < proc.popStepIdx e₁.x := by
          rw [hp_e.2.2.2.2.1]
          exact (popStepIdx_strictMono proc hp_e.2.2.1 hp_e.2.2.2.1
            (by have := h36_2.2 e₁ hsp1.2.1; omega)
            (by have := h36_2.2 e₁ hsp1.2.1; omega)).mp (by omega)
        have hwin : e.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        exact (h36_2.2 e₁ hsp1.2.1).2.2.2.2.2.2 e.stepIdx hwin e.x
          hp_e.2.2.2.2.2.2.2.1 ⟨hx1_lt_x, by omega⟩
      by_contra hlt_lo
      have htL_lt_s1 : (eL e).s < e₁.s := by omega
      have hstepL_lt_1 : (eL e).stepIdx < e₁.stepIdx := by
        rw [hp_L.2.2.2.2.1, hp_e1.2.2.2.2.1]
        exact (popStepIdx_strictMono proc hp_L.2.2.1 hp_L.2.2.2.1
          hp_e1.2.2.1 hp_e1.2.2.2.1).mp htL_lt_s1
      have hstep1_lt_xL : e₁.stepIdx < proc.popStepIdx (eL e).x := by
        rw [hp_e1.2.2.2.2.1, hxL]
        exact (popStepIdx_strictMono proc hp_e1.2.2.1 hp_e1.2.2.2.1
          (by have := h36_2.2 e hsp.2.1; omega)
          (by have := h36_2.2 e hsp.2.1; omega)).mp (by omega)
      have hwinL : e₁.stepIdx ∈ Finset.Icc ((eL e).stepIdx + 1) (proc.popStepIdx (eL e).x) :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact (h36_2.2 (eL e) hrL).2.2.2.2.2.2 e₁.stepIdx hwinL e₁.x
        hp_e1.2.2.2.2.2.2.2.1 ⟨by rw [hxL]; exact hx_lt_x1, by rw [hzL]; omega⟩
  have hsR_Sp : (eR e).s ∈ (subblock1 (childSubblocks (chain ℓ.succ) X) p).toFinset :=
    Finset.mem_Icc.mpr ⟨by rw [← hsLR]; exact hlo_le_tL, by omega⟩
  have hstepR_lt : (eR e).stepIdx < e.stepIdx := by
    rw [hp_R.2.2.2.2.1, hp_e.2.2.2.2.1]
    exact (popStepIdx_strictMono proc hp_R.2.2.1 hp_R.2.2.2.1 hp_e.2.2.1 hp_e.2.2.2.1).mp
      (by omega)
  have hxR_Sq : (eR e).x ∈ (subblock1 (childSubblocks (chain ℓ.succ) X)
      (subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.y)).toFinset := by
    rw [hxR]; exact hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsep_R := (subblock_pair_sepScale hChain ℓ hX hsp.2.2.2.2.2.2.2.2.1
    (lt_trans hsp.2.2.2.2.2.2.2.2.2.1 hsp.2.2.2.2.2.2.2.2.2.2.1)
    hsp.2.2.2.2.2.2.2.2.2.2.2.1 hsR_Sp hxR_Sq).2.2.2.2.2.2.2
  exact ⟨hsR_Sp, hstepR_lt, lt_trans hstepR_lt hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hsep_R⟩

theorem rot_in_s1_or_leafPre {r M P : ℕ} {T : ScaleTree}
    (hT : IsScaleTree r M T) {proc : FoldedPopProcess P}
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (h36_2_rot : ∀ e ∈ proc.rInt,
      1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P ∧
      (∀ τ' ∈ Finset.Ico (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w : ℕ, proc.steps[τ']? = some (.push w) → w < e.x) ∧
      (∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z)))
    (ℓ : Fin M) {X : IntervalBlock} (hX : X ∈ chain ℓ.castSucc)
    {p q : ℕ} (hp1 : 1 ≤ p) (hpq : p < q)
    (hqL : q ≤ (childSubblocks (chain ℓ.succ) X).length)
    {d : InternalPopRot} (hd : d ∈ proc.rInt)
    (hds : d.s ∈ (subblock1 (childSubblocks (chain ℓ.succ) X) p).toFinset)
    (hdx : d.x ∈ (subblock1 (childSubblocks (chain ℓ.succ) X) q).toFinset)
    (hdy : d.y ∈ (subblock1 (childSubblocks (chain ℓ.succ) X) q).toFinset)
    (hdz : (subblock1 (childSubblocks (chain ℓ.succ) X) q).hi < d.z) :
    d ∈ s1Set P T proc chain ∪ bLeafPre P proc chain := by
  obtain ⟨hs1_d, hsx_d, hxy_d, hyz_d, hzP_d, _, _⟩ := h36_2_rot d hd
  have hpair := subblock_pair_sepScale hChain ℓ hX hp1 hpq hqL hds hdx
  have hpair_y := subblock_pair_sepScale hChain ℓ hX hp1 hpq hqL hds hdy
  have hsep_sx : partSepScale P chain d.s d.x = ℓ.val + 1 := hpair.2.2.2.2.2.2.2
  have hbx : blockAt (chain ℓ.succ) d.x = subblock1 (childSubblocks (chain ℓ.succ) X) q :=
    hpair.2.2.2.2.2.2.1
  have hby : blockAt (chain ℓ.succ) d.y = subblock1 (childSubblocks (chain ℓ.succ) X) q :=
    hpair_y.2.2.2.2.2.2.1
  have hℓ_lt_xy : ℓ.val + 1 < partSepScale P chain d.x d.y := by
    have h := (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) ℓ.succ).mpr
      (hbx.trans hby.symm)
    simpa only [Fin.val_succ] using h
  have hxy_bds := partSepScale_bounds (P := P) (chain := chain) (u := d.x) (v := d.y)
    (by omega) (by omega) (by omega) (by omega)
  by_cases hleM : partSepScale P chain d.x d.y ≤ M
  · refine Finset.mem_union_left _ ?_
    have hd_b1 : d ∈ b1 P proc chain := by
      rw [b1, Finset.mem_filter]
      exact ⟨hd, by omega, by omega, hleM⟩
    unfold s1Set
    rw [Finset.mem_filter]
    refine ⟨hd_b1, ?_⟩
    have hrout := lcaScaleTree_routing hT (ℓ₁ := partSepScale P chain d.s d.x)
      (ℓ₂ := partSepScale P chain d.x d.y) (by omega) (by omega) hleM
    have hm_le : mEnd T (lcaScaleTree T (partSepScale P chain d.s d.x)
        (partSepScale P chain d.x d.y)) ≤ M := hrout.2.2.2.2.2.2
    have hℓ_le_m : ℓ.val + 1 ≤ mEnd T (lcaScaleTree T (partSepScale P chain d.s d.x)
        (partSepScale P chain d.x d.y)) := by
      have := hrout.2.2.2.2.2.1; omega
    dsimp only
    simp only [hm_le, ↓reduceDIte]
    left
    set km : Fin (M + 1) := ⟨_, Nat.lt_succ_of_le hm_le⟩
    have hhi_sub := (nested_blockAt_sub hChain (k₁ := ℓ.succ) (k₂ := km)
      (by simp only [Fin.val_succ, km]; exact hℓ_le_m)
      (u := d.y) (by omega) (by omega)).2
    rw [hby] at hhi_sub
    omega
  · refine Finset.mem_union_right _ ?_
    have heqM1 : partSepScale P chain d.x d.y = M + 1 := by omega
    rw [bLeafPre, Finset.mem_filter]
    refine ⟨hd, heqM1, ?_⟩
    have hlo_sub := (nested_blockAt_sub hChain (k₁ := ℓ.succ) (k₂ := Fin.last M)
      (by simp only [Fin.val_succ, Fin.last]; have := ℓ.isLt; omega)
      (u := d.x) (by omega) (by omega)).1
    rw [hbx] at hlo_sub
    have hSp_lt_Sq := subblock1_hi_lt_lo hChain ℓ X hp1 hpq hqL
    dsimp only at hSp_lt_Sq
    have hds_b := Finset.mem_Icc.mp hds
    omega

theorem exists_crossing_step {τ₀ τ₁ K : ℕ} {f : ℕ → ℕ}
    (hle : τ₀ ≤ τ₁) (h0 : f τ₀ ≤ K) (h1 : K < f τ₁) :
    ∃ τ, τ₀ ≤ τ ∧ τ < τ₁ ∧ f τ ≤ K ∧ K < f (τ + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => simp only [Nat.add_zero] at h1; omega
  | succ d ih =>
    by_cases hmid : K < f (τ₀ + d)
    · obtain ⟨τ, h1', h2', h3', h4'⟩ := ih (Nat.le_add_right _ _) hmid
      exact ⟨τ, h1', by omega, h3', h4'⟩
    · exact ⟨τ₀ + d, Nat.le_add_right _ _, by omega, by omega,
        by simpa [Nat.add_assoc] using h1⟩

/-- **Lemma 5.6** (`lem:b3-escape`, Step 2: Unique Scale per Promoted Key and Secondary-Exit
Reduction). -/
theorem lem_5_6_b3_escape
    (h_3_6 : Ty_lem_3_6) (h_5_1 : Ty_lem_5_1)
    (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    let leadSum := ∑ ℓ : Fin M,
      ((chain ℓ.castSucc).map (fun X =>
        let subs := childSubblocks (chain ℓ.succ) X
        ∑ p ∈ Finset.Icc 1 (subs.length - 1),
          (leadExitSet P proc chain (ℓ.val + 1) X p).card)).sum
    ∃ A_esc : Finset InternalPopRot,
      A_esc ⊆ b3ExitAct P proc chain ∧
      A_esc.card < 18 * P ∧
      (b3ExitAct P proc chain).card ≤ 2 * leadSum + A_esc.card := by
  classical
  intro chain leadSum
  have hP : 1 ≤ P := hValid.1
  have hT : IsScaleTree r M T := hValid.2.1
  have hChain : IsNestedPartitionChain P chain := scaleTreePartitionChain_isNested T P M hP
  obtain ⟨h36_1, h36_2, h36_3⟩ := h_3_6 P hP proc
  obtain ⟨hmBase_sub, hmBase_le, hkRot_4P, eL, eR, _, heR_inj, heLR⟩ := h36_3
  have hbst_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(h36_1.1 τ hτ).1, (h36_1.1 τ hτ).2.1⟩
  have hleadSum_eq : leadSum = ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
      ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
        (leadExitSet P proc chain (ℓ.val + 1) X p).card := by
    dsimp only [leadSum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    exact list_nodup_map_sum_eq_toFinset_sum
      (part_blocks_nodup (hChain.2.2.1 ℓ.castSucc)) _
  let derivedCell (ℓ : Fin M) (X : IntervalBlock) (p : ℕ) : Finset InternalPopRot :=
    (vXp P proc chain (ℓ.val + 1) X p \ leadExitSet P proc chain (ℓ.val + 1) X p).filter
      (fun e => e ∉ proc.mBase ∧ eR e ∈ b3ExitAct P proc chain)
  let leadAll : Finset InternalPopRot :=
    Finset.univ.biUnion (fun ℓ : Fin M =>
      (chain ℓ.castSucc).toFinset.biUnion (fun X =>
        (Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)).biUnion (fun p =>
          leadExitSet P proc chain (ℓ.val + 1) X p)))
  let derivedAll : Finset InternalPopRot :=
    Finset.univ.biUnion (fun ℓ : Fin M =>
      (chain ℓ.castSucc).toFinset.biUnion (fun X =>
        (Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)).biUnion (fun p =>
          derivedCell ℓ X p)))
  let A_esc : Finset InternalPopRot := b3ExitAct P proc chain \ (leadAll ∪ derivedAll)
  have hA_sub : A_esc ⊆ b3ExitAct P proc chain := Finset.sdiff_subset
  have hcov_act : b3ExitAct P proc chain ⊆ (leadAll ∪ derivedAll) ∪ A_esc := by
    intro e he
    by_cases hmem : e ∈ leadAll ∪ derivedAll
    · exact Finset.mem_union_left _ hmem
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, hmem⟩)
  have hleadAll_card : leadAll.card ≤ leadSum := by
    rw [hleadSum_eq]
    calc
      leadAll.card ≤ ∑ ℓ : Fin M,
          ((chain ℓ.castSucc).toFinset.biUnion (fun X =>
            (Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)).biUnion (fun p =>
              leadExitSet P proc chain (ℓ.val + 1) X p))).card := Finset.card_biUnion_le
      _ ≤ ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ((Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)).biUnion (fun p =>
            leadExitSet P proc chain (ℓ.val + 1) X p)).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
      _ ≤ ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (leadExitSet P proc chain (ℓ.val + 1) X p).card :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
  have hderived_cell_le : ∀ (ℓ : Fin M), ∀ X ∈ (chain ℓ.castSucc).toFinset,
      ∀ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
        (derivedCell ℓ X p).card ≤ (leadExitSet P proc chain (ℓ.val + 1) X p).card := by
    intro ℓ X hX_fin p hp
    have hX : X ∈ chain ℓ.castSucc := List.mem_toFinset.mp hX_fin
    have hprom_le := (promoted_and_leadExitSet_props hP h_3_6 proc hChain ℓ hX hp).1
    refine le_trans (Finset.card_le_card_of_injOn
      (t := promotedSubblockIndices P proc chain (ℓ.val + 1) X p)
      (fun e => subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.y) ?_ ?_) hprom_le
    · intro e he_d
      rw [Finset.mem_coe] at he_d ⊢
      simp only [derivedCell, Finset.mem_filter] at he_d
      rcases he_d with ⟨he_nl, he_nb, heR_act⟩
      have he_v : e ∈ vXp P proc chain (ℓ.val + 1) X p := (Finset.mem_sdiff.mp he_nl).1
      have hsp := vXp_cell_spec hChain h36_2.2 ℓ hX hp he_v
      dsimp only at hsp
      have haw := nonlead_active_window_props hP h_3_6 proc hChain heLR ℓ hX hp he_nl he_nb
      dsimp only at haw
      obtain ⟨_, ℓR, hs1R, hs2R, _, _⟩ := (mem_b3ExitAct_iff P proc chain (eR e)).mp heR_act
      have hℓR_eq : ℓR.val + 1 = ℓ.val + 1 := hs1R.symm.trans haw.2.2.2
      have heR_v : eR e ∈ vXp P proc chain (ℓ.val + 1) X p := by
        have hℓ_bds : 1 ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
        unfold vXp
        simp only [hℓ_bds, and_self, ↓reduceDIte, Finset.mem_filter]
        have hsucc_eq : (⟨ℓ.val + 1, Nat.lt_succ_of_le hℓ_bds.2⟩ : Fin (M + 1)) = ℓ.succ :=
          Fin.ext rfl
        rw [hsucc_eq]
        exact ⟨heR_act, hs2R.trans hℓR_eq, haw.1⟩
      have hr_diff : e ∈ proc.rInt \ proc.mBase := Finset.mem_sdiff.mpr ⟨hsp.2.1, he_nb⟩
      have hxR : (eR e).x = e.y := (heLR e hr_diff).2.2.2.2.2.2.2.2.1
      have hℓ_bds : 1 ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
      unfold promotedSubblockIndices
      simp only [hℓ_bds, and_self, ↓reduceDIte, Finset.mem_filter]
      have hsucc_eq : (⟨ℓ.val + 1, Nat.lt_succ_of_le hℓ_bds.2⟩ : Fin (M + 1)) = ℓ.succ :=
        Fin.ext rfl
      rw [hsucc_eq]
      have hq_ge_p1 : p + 1 ≤ subblockIndex1 (childSubblocks (chain ℓ.succ) X) e.y := by
        have := hsp.2.2.2.2.2.2.2.2.2.1
        have := hsp.2.2.2.2.2.2.2.2.2.2.1
        omega
      exact ⟨Finset.mem_Icc.mpr ⟨hq_ge_p1, hsp.2.2.2.2.2.2.2.2.2.2.2.1⟩,
        eR e, heR_v, hxR ▸ hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    · intro e₁ he₁ e₂ he₂ hq_eq
      rw [Finset.mem_coe] at he₁ he₂
      have hv1 : e₁ ∈ vXp P proc chain (ℓ.val + 1) X p :=
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp he₁).1).1
      have hv2 : e₂ ∈ vXp P proc chain (ℓ.val + 1) X p :=
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp he₂).1).1
      exact vXp_displaced_subblock_inj hP h_3_6 proc hChain ℓ hX hp hv1 hv2 hq_eq
  have hderivedAll_card : derivedAll.card ≤ leadSum := by
    rw [hleadSum_eq]
    calc
      derivedAll.card ≤ ∑ ℓ : Fin M,
          ((chain ℓ.castSucc).toFinset.biUnion (fun X =>
            (Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)).biUnion (fun p =>
              derivedCell ℓ X p))).card := Finset.card_biUnion_le
      _ ≤ ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ((Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1)).biUnion (fun p =>
            derivedCell ℓ X p)).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
      _ ≤ ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (derivedCell ℓ X p).card :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
      _ ≤ ∑ ℓ : Fin M, ∑ X ∈ (chain ℓ.castSucc).toFinset,
          ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
            (leadExitSet P proc chain (ℓ.val + 1) X p).card :=
        Finset.sum_le_sum fun ℓ _ => Finset.sum_le_sum fun X hX =>
          Finset.sum_le_sum fun p hp => hderived_cell_le ℓ X hX p hp
  have hact_total : (b3ExitAct P proc chain).card ≤ 2 * leadSum + A_esc.card := by
    have hc1 := Finset.card_le_card hcov_act
    have hc2 : ((leadAll ∪ derivedAll) ∪ A_esc).card ≤
        leadAll.card + derivedAll.card + A_esc.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    omega
  -- Now bound `A_esc.card < 18 * P` via Categories (a), (b), (c), (d)+(e_pop), and (e_urot)
  let catA := A_esc.filter (fun e => e ∈ proc.mBase)
  let catB := A_esc.filter (fun e =>
    e ∉ proc.mBase ∧
    ∃ ℓ : Fin M, partSepScale P chain e.x e.y = ℓ.val + 1 ∧
      (blockAt (chain ℓ.castSucc) e.s).hi < (eR e).y)
  let catC := A_esc.filter (fun e =>
    e ∉ proc.mBase ∧ eR e ∈ b3Intra P proc chain)
  let catDPop := A_esc.filter (fun e =>
    ∃ ℓ : Fin M, partSepScale P chain e.x e.y = ℓ.val + 1 ∧
      ∃ d ∈ s1Set P T proc chain ∪ bLeafPre P proc chain,
        d.s ∈ (blockAt (chain ℓ.succ) e.s).toFinset ∧ d.x = e.y)
  let catEUrot := A_esc.filter (fun e =>
    ∃ ℓ : Fin M, partSepScale P chain e.x e.y = ℓ.val + 1 ∧
      let Sp := blockAt (chain ℓ.succ) e.s
      ∃ τ < proc.steps.length,
        proc.popStepIdx Sp.lo ≤ τ ∧ τ < tauEmpty proc Sp ∧
        ∃ v, proc.steps[τ]? = some (.upperRot e.y v))
  have hA_cov : A_esc ⊆ catA ∪ catB ∪ catC ∪ catDPop ∪ catEUrot := by
    intro e heA
    by_cases hmb : e ∈ proc.mBase
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heA, hmb⟩))))
    · obtain ⟨he_act, hnot_ld⟩ := Finset.mem_sdiff.mp heA
      obtain ⟨ℓ, X, hX, p, hp, he_v⟩ := mem_vXp_of_b3ExitAct hChain h36_2.2 he_act
      have he_not_lead : e ∉ leadExitSet P proc chain (ℓ.val + 1) X p := by
        intro hlead
        apply hnot_ld; apply Finset.mem_union_left
        simp only [leadAll, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨ℓ, X, List.mem_toFinset.mpr hX, p, hp, hlead⟩
      have he_not_der : eR e ∉ b3ExitAct P proc chain := by
        intro hr_act
        apply hnot_ld; apply Finset.mem_union_right
        simp only [derivedAll, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨ℓ, X, List.mem_toFinset.mpr hX, p, hp,
          Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨he_v, he_not_lead⟩, hmb, hr_act⟩⟩
      have he_nl : e ∈ vXp P proc chain (ℓ.val + 1) X p \ leadExitSet P proc chain (ℓ.val + 1) X p :=
        Finset.mem_sdiff.mpr ⟨he_v, he_not_lead⟩
      have hsp := vXp_cell_spec hChain h36_2.2 ℓ hX hp he_v
      dsimp only at hsp
      have haw := nonlead_active_window_props hP h_3_6 proc hChain heLR ℓ hX hp he_nl hmb
      dsimp only at haw
      have hr_diff : e ∈ proc.rInt \ proc.mBase := Finset.mem_sdiff.mpr ⟨hsp.2.1, hmb⟩
      obtain ⟨_, hrR, _, _, _, _, _, _, hxR, _, _, _, hy_lt_w2, hw2_lt_zR⟩ := heLR e hr_diff
      have hrotR := h36_2.2 (eR e) hrR
      let subs := childSubblocks (chain ℓ.succ) X
      let q := subblockIndex1 subs e.y
      let Sp := subblock1 subs p
      let Sq := subblock1 subs q
      have hX_eq : blockAt (chain ℓ.castSucc) e.s = X := hsp.2.2.2.2.1
      have hSp_eq : blockAt (chain ℓ.succ) e.s = Sp := hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hSq_eq : blockAt (chain ℓ.succ) e.y = Sq := hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hsep_xy : partSepScale P chain e.x e.y = ℓ.val + 1 := hsp.2.2.2.1
      by_cases hw2_gt_X : X.hi < (eR e).y
      · -- Category (b)
        refine Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heA, hmb, ?_⟩))))
        exact ⟨ℓ, hsep_xy, by rw [hX_eq]; exact hw2_gt_X⟩
      · by_cases hw2_gt_Sq : Sq.hi < (eR e).y
        · -- Category (c): `Sq.hi < (eR e).y ≤ X.hi` and `eR e ∉ b3ExitAct` => `eR e ∈ b3Intra`
          refine Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heA, hmb, ?_⟩)))
          obtain ⟨hX1, _, hXP⟩ := (hChain.2.2.1 ℓ.castSucc).1 X hX
          have hy_X_b := Finset.mem_Icc.mp
            ((mem_subblock1_iff hChain ℓ hX (by omega) hsp.2.2.2.2.2.2.2.2.2.2.2.1).mp
              hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
          have hw2_X : (eR e).y ∈ X.toFinset :=
            Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have hspec_w2 := subblockIndex1_spec hChain ℓ hX hw2_X
          dsimp only at hspec_w2
          have hq_lt_c2 : q < subblockIndex1 subs (eR e).y := by
            rcases lt_trichotomy q (subblockIndex1 subs (eR e).y) with hlt | heq | hgt
            · exact hlt
            · exfalso
              have hw2_b := Finset.mem_Icc.mp hspec_w2.2.2.2
              dsimp only [subs, Sq, q] at hw2_gt_Sq heq
              rw [← heq] at hw2_b
              omega
            · exfalso
              dsimp only [subs, Sq, q] at hgt hw2_gt_Sq
              have h1 := subblock1_hi_lt_lo hChain ℓ X hspec_w2.1 hgt hsp.2.2.2.2.2.2.2.2.2.2.2.1
              dsimp only at h1
              have h2 := Finset.mem_Icc.mp hspec_w2.2.2.2
              have h3 := Finset.mem_Icc.mp hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              omega
          have hq1 : 1 ≤ q := by
            have := hsp.2.2.2.2.2.2.2.2.1
            have := hsp.2.2.2.2.2.2.2.2.2.1
            have := hsp.2.2.2.2.2.2.2.2.2.2.1
            dsimp only [q, subs]
            omega
          have hsep_R2 : partSepScale P chain (eR e).x (eR e).y = ℓ.val + 1 := by
            rw [hxR]
            exact (subblock_pair_sepScale hChain ℓ hX hq1 hq_lt_c2 hspec_w2.2.1
              hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hspec_w2.2.2.2).2.2.2.2.2.2.2
          have hℓ_bds : 1 ≤ partSepScale P chain (eR e).x (eR e).y ∧
              partSepScale P chain (eR e).x (eR e).y ≤ M := by
            have := ℓ.isLt; omega
          have hsucc_R : (⟨partSepScale P chain (eR e).x (eR e).y,
              Nat.lt_succ_of_le hℓ_bds.2⟩ : Fin (M + 1)) = ℓ.succ :=
            Fin.ext (by dsimp only; exact hsep_R2)
          have hzR_le : (eR e).z ≤ (blockAt (chain ℓ.succ) (eR e).y).hi := by
            by_contra hgt_zR
            apply he_not_der
            rw [mem_b3ExitAct_iff]
            have hxR_Sq : (eR e).x ∈ Sq.toFinset := by
              rw [hxR]; exact hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            have hbsR : blockAt (chain ℓ.succ) (eR e).s = Sp :=
              (subblock_pair_sepScale hChain ℓ hX hsp.2.2.2.2.2.2.2.2.1
                (lt_trans hsp.2.2.2.2.2.2.2.2.2.1 hsp.2.2.2.2.2.2.2.2.2.2.1)
                hsp.2.2.2.2.2.2.2.2.2.2.2.1 haw.1 hxR_Sq).2.2.2.2.2.1
            exact ⟨hrR, ℓ, haw.2.2.2, hsep_R2, by omega, by rw [hbsR]; exact haw.2.2.1⟩
          unfold b3Intra
          rw [Finset.mem_filter]
          refine ⟨hrR, ?_⟩
          simp only [hℓ_bds, and_self, ↓reduceDIte]
          exact ⟨haw.2.2.2.trans hsep_R2.symm, by rw [hsucc_R]; exact hzR_le⟩
        · -- `(eR e).y ≤ Sq.hi` => `(eR e).y ∈ Sq.toFinset`
          have hy_Sq_b := Finset.mem_Icc.mp hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have hw2_Sq : (eR e).y ∈ Sq.toFinset :=
            Finset.mem_Icc.mpr ⟨by dsimp only [Sq, subs, q]; omega, by omega⟩
          by_cases hzR_gt_Sq : Sq.hi < (eR e).z
          · -- Category (d)
            refine Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨heA, ℓ, hsep_xy, eR e, ?_, ?_, hxR⟩))
            · exact rot_in_s1_or_leafPre hT hChain h36_2.2 ℓ hX hsp.2.2.2.2.2.2.2.2.1
                (lt_trans hsp.2.2.2.2.2.2.2.2.2.1 hsp.2.2.2.2.2.2.2.2.2.2.1)
                hsp.2.2.2.2.2.2.2.2.2.2.2.1 hrR haw.1
                (hxR ▸ hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) hw2_Sq hzR_gt_Sq
            · rw [hSp_eq]; exact haw.1
          · -- Category (e): `(eR e).z ≤ Sq.hi` while `Sq.hi < e.z`
            have hp_R := rInt_props proc hbst_all hrR
            have hp_e := rInt_props proc hbst_all hsp.2.1
            have hrot_e := h36_2.2 e hsp.2.1
            have hpopR_law := h36_1.2.2.1 (eR e).s hp_R.2.2.1 hp_R.2.2.2.1
            dsimp only at hpopR_law
            rw [← hp_R.2.2.2.2.1] at hpopR_law
            have hfp_start : foldedParent P (proc.treeAt ((eR e).stepIdx + 1)) e.y ≤ Sq.hi := by
              have h := hpopR_law.1 (eR e) hrR rfl
              rw [hxR] at h
              omega
            have hfp_end : Sq.hi < foldedParent P (proc.treeAt e.stepIdx) e.y := by
              rw [hp_e.2.2.2.2.2.2.2.2.2.2.2]
              exact hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
            obtain ⟨τ, hτ_ge, hτ_lt, hfp_τ, hfp_τ1⟩ :=
              exists_crossing_step (τ₀ := (eR e).stepIdx + 1) (τ₁ := e.stepIdx)
                (K := Sq.hi) (f := fun t => foldedParent P (proc.treeAt t) e.y)
                (by omega) hfp_start hfp_end
            have hτ_len : τ < proc.steps.length := lt_trans hτ_lt hp_e.1
            have hy_mem_R : e.y ∈ keyFinset (proc.treeAt (eR e).stepIdx) := by
              rw [← hxR]
              exact mem_keyFinset_iff.mpr (mem_of_mem_leftSpine hp_R.2.2.2.2.2.2.2.1)
            have he_lt_y : e.stepIdx ≤ proc.popStepIdx e.y := by
              rw [hp_e.2.2.2.2.1]
              exact le_of_lt ((popStepIdx_strictMono proc (by omega) (by omega)
                (by omega) (by omega)).mp (lt_trans hrot_e.2.1 hrot_e.2.2.1))
            have hy_mem_τ : e.y ∈ keyFinset (proc.treeAt τ) :=
              mem_treeAt_stay_until_pop proc hbst_all (by omega) (by omega)
                (by omega) (le_trans (le_of_lt hτ_lt) he_lt_y) hy_mem_R
            have hy_mem_τ1 : e.y ∈ keyFinset (proc.treeAt (τ + 1)) :=
              mem_treeAt_stay_until_pop proc hbst_all (by omega) (by omega)
                (by omega) (le_trans (by omega) he_lt_y) hy_mem_R
            have hSp_lo_le_sR : Sp.lo ≤ (eR e).s := (Finset.mem_Icc.mp haw.1).1
            have hSp_mem : Sp ∈ chain ℓ.succ := hSp_eq ▸
              (blockAt_mem_and_bounds (hChain.2.2.1 ℓ.succ) hrot_e.1 (by omega)).1
            obtain ⟨hSp1, hSp_lohi, hSpP⟩ := (hChain.2.2.1 ℓ.succ).1 Sp hSp_mem
            have hlo_le_R_idx : proc.popStepIdx Sp.lo ≤ (eR e).stepIdx := by
              rw [hp_R.2.2.2.2.1]
              rcases eq_or_lt_of_le hSp_lo_le_sR with heq_s | hlt_s
              · rw [heq_s]
              · exact le_of_lt ((popStepIdx_strictMono proc hSp1 (le_trans hSp_lohi hSpP)
                  hp_R.2.2.1 hp_R.2.2.2.1).mp hlt_s)
            have hprops_τ := step_tree_props proc hbst_all hτ_len
            cases hop_τ : proc.steps[τ] with
            | shift =>
              exfalso
              rw [hop_τ] at hprops_τ; dsimp only at hprops_τ
              rw [hprops_τ] at hfp_τ1
              omega
            | push w =>
              exfalso
              rw [hop_τ] at hprops_τ; dsimp only at hprops_τ
              have hsame := hprops_τ.2.2.2 e.y (mem_keyFinset_iff.mp hy_mem_τ)
              omega
            | upperRot u v =>
              have hu_eq : e.y = u := by
                by_contra hne_u
                have hur := (h36_1.2.1 τ u v hτ_len
                  (by rw [List.getElem?_eq_getElem hτ_len, hop_τ])).2
                  e.y (mem_keyFinset_iff.mp hy_mem_τ1) hne_u
                omega
              subst u
              refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heA, ℓ, hsep_xy, ?_⟩)
              dsimp only
              rw [hSp_eq]
              refine ⟨τ, hτ_len, by omega, lt_trans hτ_lt
                hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, v, ?_⟩
              rw [List.getElem?_eq_getElem hτ_len, hop_τ]
            | pop s_t =>
              obtain ⟨hs_t1, hs_tP, hτ_pop_eq⟩ := (getElem_eq_pop_iff proc hτ_len).mp hop_τ
              have hpop_t_law := h36_1.2.2.1 s_t hs_t1 hs_tP
              dsimp only at hpop_t_law
              rw [← hτ_pop_eq] at hpop_t_law
              have hex_d : ∃ d ∈ proc.rInt, d.stepIdx = τ ∧ d.x = e.y := by
                by_contra hnone
                have hsame := hpop_t_law.2 e.y (mem_keyFinset_iff.mp hy_mem_τ1)
                  (fun d hd hst heq => hnone ⟨d, hd, hst, heq.symm⟩)
                omega
              obtain ⟨d, hd_rInt, hd_step, hd_x⟩ := hex_d
              have hp_d := rInt_props proc hbst_all hd_rInt
              have hd_s_eq : d.s = s_t := by
                have h1 := hp_d.2.1
                rw [hd_step, List.getElem?_eq_getElem hτ_len, hop_τ, Option.some.injEq] at h1
                injection h1 with h1'; exact h1'.symm
              have hs_t_gt_sR : (eR e).s < s_t := by
                apply (popStepIdx_strictMono proc hp_R.2.2.1 hp_R.2.2.2.1 hs_t1 hs_tP).mpr
                omega
              have hs_t_lt_s : s_t < e.s := by
                apply (popStepIdx_strictMono proc hs_t1 hs_tP hp_e.2.2.1 hp_e.2.2.2.1).mpr
                rw [← hτ_pop_eq, ← hp_e.2.2.2.2.1]
                exact hτ_lt
              have hs_Sp_b := Finset.mem_Icc.mp hsp.2.2.2.2.2.2.2.2.2.2.2.2.1
              have hds_Sp : d.s ∈ Sp.toFinset := by
                rw [hd_s_eq]
                refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
                dsimp only [Sp, subs]
                omega
              have hdy_eq : foldedParent P (proc.treeAt τ) e.y = d.y := by
                rw [← hd_x, ← hd_step]
                exact hp_d.2.2.2.2.2.2.2.2.2.2.1
              have hdz_eq : foldedParent P (proc.treeAt (τ + 1)) e.y = d.z := by
                rw [← hd_x]
                exact hpop_t_law.1 d hd_rInt hd_step
              have hd_xy_lt : e.y < d.y := by
                rw [← hd_x]; exact (h36_2.2 d hd_rInt).2.2.1
              have hdy_Sq : d.y ∈ Sq.toFinset :=
                Finset.mem_Icc.mpr ⟨by dsimp only [Sq, subs, q]; omega, by omega⟩
              have hdz_gt : Sq.hi < d.z := by omega
              refine Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_filter.mpr ⟨heA, ℓ, hsep_xy, d, ?_, ?_, hd_x⟩))
              · exact rot_in_s1_or_leafPre hT hChain h36_2.2 ℓ hX hsp.2.2.2.2.2.2.2.2.1
                  (lt_trans hsp.2.2.2.2.2.2.2.2.2.1 hsp.2.2.2.2.2.2.2.2.2.2.1)
                  hsp.2.2.2.2.2.2.2.2.2.2.2.1 hd_rInt hds_Sp
                  (hd_x ▸ hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) hdy_Sq hdz_gt
              · rw [hSp_eq]; exact hds_Sp
  -- Bound each of the 5 parts of `A_esc`
  have hcatA_le : catA.card ≤ proc.mBase.card :=
    Finset.card_le_card (fun e he => (Finset.mem_filter.mp he).2)
  have hcatB_le : catB.card ≤ P := by
    refine le_trans (Finset.card_le_card_of_injOn (t := Finset.Icc 1 P) InternalPopRot.x ?_ ?_)
      (by rw [Nat.card_Icc]; omega)
    · intro e he
      rw [Finset.mem_coe] at he ⊢
      have he_act : e ∈ b3ExitAct P proc chain := hA_sub (Finset.mem_filter.mp he).1
      have hr := ((mem_b3ExitAct_iff P proc chain e).mp he_act).1
      have hrot := h36_2.2 e hr
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro e₁ he₁ e₂ he₂ hx_eq
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      have he1_act : e₁ ∈ b3ExitAct P proc chain := hA_sub he₁.1
      have he2_act : e₂ ∈ b3ExitAct P proc chain := hA_sub he₂.1
      have hb3_sub : ∀ d ∈ b3ExitAct P proc chain, d ∈ b3 P proc chain := by
        intro d hd
        obtain ⟨hr, ℓ, hs1, hs2, _, _⟩ := (mem_b3ExitAct_iff P proc chain d).mp hd
        rw [b3, Finset.mem_filter]
        exact ⟨hr, by omega, hs1.trans hs2.symm, by have := ℓ.isLt; omega⟩
      have hb3_1 := hb3_sub e₁ he1_act
      have hb3_2 := hb3_sub e₂ he2_act
      have hz_gt_X : ∀ d ∈ A_esc, d ∉ proc.mBase →
          ∀ ℓ : Fin M, partSepScale P chain d.x d.y = ℓ.val + 1 →
          (blockAt (chain ℓ.castSucc) d.s).hi < (eR d).y →
          (blockAt (chain ℓ.castSucc) d.s).hi < d.z := by
        intro d hdA hd_nb ℓ hd_sep hw2_gt
        have hd_act : d ∈ b3ExitAct P proc chain := hA_sub hdA
        obtain ⟨ℓ', X, hX, p, hp, hd_v⟩ := mem_vXp_of_b3ExitAct hChain h36_2.2 hd_act
        have hsp_d := vXp_cell_spec hChain h36_2.2 ℓ' hX hp hd_v
        dsimp only at hsp_d
        have hℓ'_eq : ℓ' = ℓ := Fin.ext (by omega)
        subst ℓ'
        have hd_not_lead : d ∉ leadExitSet P proc chain (ℓ.val + 1) X p := by
          intro hlead
          apply (Finset.mem_sdiff.mp hdA).2; apply Finset.mem_union_left
          simp only [leadAll, Finset.mem_biUnion, Finset.mem_univ, true_and]
          exact ⟨ℓ, X, List.mem_toFinset.mpr hX, p, hp, hlead⟩
        have haw_d := nonlead_active_window_props hP h_3_6 proc hChain heLR ℓ hX hp
          (Finset.mem_sdiff.mpr ⟨hd_v, hd_not_lead⟩) hd_nb
        dsimp only at haw_d
        have hr_diff : d ∈ proc.rInt \ proc.mBase := Finset.mem_sdiff.mpr ⟨hsp_d.2.1, hd_nb⟩
        obtain ⟨_, hrR, _, _, _, _, _, _, hxR, _, _, _, _, hw2_lt_zR⟩ := heLR d hr_diff
        have hp_R := rInt_props proc hbst_all hrR
        have hp_d := rInt_props proc hbst_all hsp_d.2.1
        have hrot_d := h36_2.2 d hsp_d.2.1
        have hpopR_law := h36_1.2.2.1 (eR d).s hp_R.2.2.1 hp_R.2.2.2.1
        dsimp only at hpopR_law
        rw [← hp_R.2.2.2.2.1] at hpopR_law
        have hfp_R : foldedParent P (proc.treeAt ((eR d).stepIdx + 1)) d.y = (eR d).z := by
          rw [← hxR]; exact hpopR_law.1 (eR d) hrR rfl
        have hy_mem_R : d.y ∈ keyFinset (proc.treeAt (eR d).stepIdx) := by
          rw [← hxR]; exact mem_keyFinset_iff.mpr (mem_of_mem_leftSpine hp_R.2.2.2.2.2.2.2.1)
        have hd_lt_y : d.stepIdx ≤ proc.popStepIdx d.y := by
          rw [hp_d.2.2.2.2.1]
          exact le_of_lt ((popStepIdx_strictMono proc (by omega) (by omega)
            (by omega) (by omega)).mp (lt_trans hrot_d.2.1 hrot_d.2.2.1))
        have hy_mem_R1 : d.y ∈ proc.treeAt ((eR d).stepIdx + 1) :=
          mem_keyFinset_iff.mp (mem_treeAt_stay_until_pop proc hbst_all (by omega) (by omega)
            (by omega) (le_trans (by omega) hd_lt_y) hy_mem_R)
        have hy_mem_d : d.y ∈ proc.treeAt d.stepIdx :=
          mem_of_mem_leftSpine hp_d.2.2.2.2.2.2.2.2.1
        have hmono := (h36_1.2.2.2 ((eR d).stepIdx + 1) d.stepIdx d.y (by omega)
          (le_of_lt hp_d.1) hy_mem_R1 hy_mem_d).1
        rw [hfp_R, hp_d.2.2.2.2.2.2.2.2.2.2.2] at hmono
        omega
      rcases he₁.2 with ⟨he1_nb, ℓ₁, hsep1, hw2_1⟩
      rcases he₂.2 with ⟨he2_nb, ℓ₂, hsep2, hw2_2⟩
      have hz1_gt := hz_gt_X e₁ he₁.1 he1_nb ℓ₁ hsep1 hw2_1
      have hz2_gt := hz_gt_X e₂ he₂.1 he2_nb ℓ₂ hsep2 hw2_2
      rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with hlt | hstep_eq | hgt
      · exfalso
        obtain ⟨hz1_le_y2, hsame_sc⟩ :=
          b3_z_le_y_and_same_scale hP h_3_6 proc hChain hb3_1 hb3_2 hx_eq hlt
        have hℓ_eq : ℓ₁ = ℓ₂ := Fin.ext (by omega)
        subst ℓ₂
        obtain ⟨ℓ', X, hX, p, hp, hv2⟩ := mem_vXp_of_b3ExitAct hChain h36_2.2 he2_act
        have hsp2 := vXp_cell_spec hChain h36_2.2 ℓ' hX hp hv2
        dsimp only at hsp2
        have hℓ'_eq : ℓ' = ℓ₁ := Fin.ext (by omega)
        subst ℓ'
        obtain ⟨ℓ'', X1, hX1_m, p1, hp1_m, hv1⟩ := mem_vXp_of_b3ExitAct hChain h36_2.2 he1_act
        have hsp1 := vXp_cell_spec hChain h36_2.2 ℓ'' hX1_m hp1_m hv1
        dsimp only at hsp1
        have hℓ''_eq : ℓ'' = ℓ₁ := Fin.ext (by omega)
        subst ℓ''
        have hX_same : blockAt (chain ℓ₁.castSucc) e₁.s = blockAt (chain ℓ₁.castSucc) e₂.y := by
          rw [hsp1.2.2.2.2.1, ← hsp1.2.2.2.2.2.1, hx_eq, hsp2.2.2.2.2.2.1, hsp2.2.2.2.2.2.2.1]
        have hy2_hi : e₂.y ≤ (blockAt (chain ℓ₁.castSucc) e₂.y).hi :=
          (blockAt_mem_and_bounds (hChain.2.2.1 ℓ₁.castSucc) (u := e₂.y)
            (by have := h36_2.2 e₂ hsp2.2.1; omega)
            (by have := h36_2.2 e₂ hsp2.2.1; omega)).2.2
        rw [← hX_same] at hy2_hi
        omega
      · exact (rInt_same_stepIdx_props proc hbst_all
          ((mem_b3ExitAct_iff P proc chain e₁).mp he1_act).1
          ((mem_b3ExitAct_iff P proc chain e₂).mp he2_act).1 hstep_eq).2.2.2.1 hx_eq
      · exfalso
        obtain ⟨hz2_le_y1, hsame_sc⟩ :=
          b3_z_le_y_and_same_scale hP h_3_6 proc hChain hb3_2 hb3_1 hx_eq.symm hgt
        have hℓ_eq : ℓ₁ = ℓ₂ := Fin.ext (by omega)
        subst ℓ₂
        obtain ⟨ℓ', X, hX, p, hp, hv1⟩ := mem_vXp_of_b3ExitAct hChain h36_2.2 he1_act
        have hsp1 := vXp_cell_spec hChain h36_2.2 ℓ' hX hp hv1
        dsimp only at hsp1
        have hℓ'_eq : ℓ' = ℓ₁ := Fin.ext (by omega)
        subst ℓ'
        obtain ⟨ℓ'', X2, hX2_m, p2, hp2_m, hv2⟩ := mem_vXp_of_b3ExitAct hChain h36_2.2 he2_act
        have hsp2 := vXp_cell_spec hChain h36_2.2 ℓ'' hX2_m hp2_m hv2
        dsimp only at hsp2
        have hℓ''_eq : ℓ'' = ℓ₁ := Fin.ext (by omega)
        subst ℓ''
        have hX_same : blockAt (chain ℓ₁.castSucc) e₂.s = blockAt (chain ℓ₁.castSucc) e₁.y := by
          rw [hsp2.2.2.2.2.1, ← hsp2.2.2.2.2.2.1, ← hx_eq, hsp1.2.2.2.2.2.1, hsp1.2.2.2.2.2.2.1]
        have hy1_hi : e₁.y ≤ (blockAt (chain ℓ₁.castSucc) e₁.y).hi :=
          (blockAt_mem_and_bounds (hChain.2.2.1 ℓ₁.castSucc) (u := e₁.y)
            (by have := h36_2.2 e₁ hsp1.2.1; omega)
            (by have := h36_2.2 e₁ hsp1.2.1; omega)).2.2
        rw [← hX_same] at hy1_hi
        omega
  have hcatC_le : catC.card ≤ (b3Intra P proc chain).card := by
    refine Finset.card_le_card_of_injOn (t := b3Intra P proc chain) eR ?_ ?_
    · intro e he
      rw [Finset.mem_coe] at he ⊢
      exact (Finset.mem_filter.mp he).2.2
    · intro e₁ he₁ e₂ he₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      have hr1 := ((mem_b3ExitAct_iff P proc chain e₁).mp (hA_sub he₁.1)).1
      have hr2 := ((mem_b3ExitAct_iff P proc chain e₂).mp (hA_sub he₂.1)).1
      exact heR_inj ⟨hr1, he₁.2.1⟩ ⟨hr2, he₂.2.1⟩ heq
  -- Helper pinning `e ∈ A_esc` from a pair `(m₀, e.y)` with `m₀ ∈ (blockAt (chain ℓ.succ) e.s)`
  have hpin_by_m_and_y : ∀ {e₁ e₂ : InternalPopRot} {m₀ : ℕ} {ℓ₁ ℓ₂ : Fin M},
      e₁ ∈ A_esc → e₂ ∈ A_esc →
      partSepScale P chain e₁.x e₁.y = ℓ₁.val + 1 →
      partSepScale P chain e₂.x e₂.y = ℓ₂.val + 1 →
      m₀ ∈ (blockAt (chain ℓ₁.succ) e₁.s).toFinset →
      m₀ ∈ (blockAt (chain ℓ₂.succ) e₂.s).toFinset →
      e₁.y = e₂.y →
      e₁ = e₂ := by
    intro e₁ e₂ m₀ ℓ₁ ℓ₂ he1A he2A hsep1 hsep2 hm1 hm2 hy_eq
    obtain ⟨ℓ₁', X₁, hX₁, p₁, hp₁, hv₁⟩ := mem_vXp_of_b3ExitAct hChain h36_2.2 (hA_sub he1A)
    obtain ⟨ℓ₂', X₂, hX₂, p₂, hp₂, hv₂⟩ := mem_vXp_of_b3ExitAct hChain h36_2.2 (hA_sub he2A)
    have hsp₁ := vXp_cell_spec hChain h36_2.2 ℓ₁' hX₁ hp₁ hv₁
    have hsp₂ := vXp_cell_spec hChain h36_2.2 ℓ₂' hX₂ hp₂ hv₂
    dsimp only at hsp₁ hsp₂
    have hℓ1_eq : ℓ₁' = ℓ₁ := Fin.ext (by omega)
    have hℓ2_eq : ℓ₂' = ℓ₂ := Fin.ext (by omega)
    subst ℓ₁'; subst ℓ₂'
    rw [hsp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hm1
    rw [hsp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hm2
    have hp_pair1 := subblock_pair_sepScale hChain ℓ₁ hX₁ hsp₁.2.2.2.2.2.2.2.2.1
      (lt_trans hsp₁.2.2.2.2.2.2.2.2.2.1 hsp₁.2.2.2.2.2.2.2.2.2.2.1)
      hsp₁.2.2.2.2.2.2.2.2.2.2.2.1 hm1 hsp₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hp_pair2 := subblock_pair_sepScale hChain ℓ₂ hX₂ hsp₂.2.2.2.2.2.2.2.2.1
      (lt_trans hsp₂.2.2.2.2.2.2.2.2.2.1 hsp₂.2.2.2.2.2.2.2.2.2.2.1)
      hsp₂.2.2.2.2.2.2.2.2.2.2.2.1 hm2 hsp₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hsep_my1 : partSepScale P chain m₀ e₁.y = ℓ₁.val + 1 := hp_pair1.2.2.2.2.2.2.2
    have hsep_my2 : partSepScale P chain m₀ e₁.y = ℓ₂.val + 1 := by
      rw [hy_eq]; exact hp_pair2.2.2.2.2.2.2.2
    have hℓ12 : ℓ₁ = ℓ₂ := Fin.ext (by omega)
    subst ℓ₂
    have hX12 : X₁ = X₂ := hp_pair1.2.2.2.1.symm.trans hp_pair2.2.2.2.1
    subst X₂
    have hp1_idx := ((mem_subblock1_iff hChain ℓ₁ hX₁ hsp₁.2.2.2.2.2.2.2.2.1 (by omega)).mp hm1).2
    have hp2_idx := ((mem_subblock1_iff hChain ℓ₁ hX₁ hsp₂.2.2.2.2.2.2.2.2.1 (by omega)).mp hm2).2
    have hp12 : p₁ = p₂ := hp1_idx.symm.trans hp2_idx
    rw [← hp12] at hv₂
    exact vXp_displaced_subblock_inj hP h_3_6 proc hChain ℓ₁ hX₁ hp₁ hv₁ hv₂
      (by rw [hy_eq])
  have hcatDPop_le : catDPop.card ≤
      (s1Set P T proc chain).card + (bLeafPre P proc chain).card := by
    let target := s1Set P T proc chain ∪ bLeafPre P proc chain
    let fD : InternalPopRot → InternalPopRot := fun e =>
      if he : e ∈ catDPop then
        (Finset.mem_filter.mp he).2.choose_spec.2.choose
      else ⟨0, 0, 0, 0, 0, 0, 0⟩
    refine le_trans (Finset.card_le_card_of_injOn (t := target) fD ?_ ?_)
      (Finset.card_union_le _ _)
    · intro e he
      rw [Finset.mem_coe] at he ⊢
      simp only [fD, he, ↓reduceDIte]
      exact (Finset.mem_filter.mp he).2.choose_spec.2.choose_spec.1
    · intro e₁ he₁ e₂ he₂ hfeq
      rw [Finset.mem_coe] at he₁ he₂
      simp only [fD, he₁, he₂, ↓reduceDIte] at hfeq
      have h1_ex := (Finset.mem_filter.mp he₁).2
      have h2_ex := (Finset.mem_filter.mp he₂).2
      set ℓ₁ := h1_ex.choose
      set ℓ₂ := h2_ex.choose
      have hsep1 := h1_ex.choose_spec.1
      have hsep2 := h2_ex.choose_spec.1
      have hd1 := h1_ex.choose_spec.2.choose_spec.2
      have hd2 := h2_ex.choose_spec.2.choose_spec.2
      rw [hfeq] at hd1
      exact hpin_by_m_and_y (Finset.mem_filter.mp he₁).1 (Finset.mem_filter.mp he₂).1
        hsep1 hsep2 hd1.1 hd2.1 (hd1.2.symm.trans hd2.2)
  have hcatEUrot_le : catEUrot.card ≤ proc.kRot := by
    let isURot : FoldedOp → Bool := fun | .upperRot _ _ => true | _ => false
    let urotSteps := (Finset.range proc.steps.length).filter (fun τ =>
      match proc.steps[τ]? with | some op => isURot op | none => false)
    have hurot_card : urotSteps.card = proc.kRot := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      have hsum : (∑ τ ∈ Finset.range proc.steps.length,
          match proc.steps[τ]? with | some op => if isURot op then 1 else 0 | none => 0) =
          proc.kRot :=
        sum_range_opt_ind_eq_filter_length isURot proc.steps
      rw [← hsum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      cases proc.steps[τ]? with
      | none => simp
      | some op => cases op <;> simp [isURot]
    let fU : InternalPopRot → ℕ := fun e =>
      if he : e ∈ catEUrot then
        (Finset.mem_filter.mp he).2.choose_spec.2.choose
      else 0
    rw [← hurot_card]
    refine Finset.card_le_card_of_injOn (t := urotSteps) fU ?_ ?_
    · intro e he
      rw [Finset.mem_coe] at he ⊢
      simp only [fU, he, ↓reduceDIte]
      have hex := (Finset.mem_filter.mp he).2.choose_spec.2
      obtain ⟨hτ_len, _, _, v, hop⟩ := hex.choose_spec
      simp only [urotSteps, Finset.mem_filter, Finset.mem_range]
      refine ⟨hτ_len, ?_⟩
      rw [hop]
    · intro e₁ he₁ e₂ he₂ hfeq
      rw [Finset.mem_coe] at he₁ he₂
      simp only [fU, he₁, he₂, ↓reduceDIte] at hfeq
      have h1_ex := (Finset.mem_filter.mp he₁).2
      have h2_ex := (Finset.mem_filter.mp he₂).2
      set ℓ₁ := h1_ex.choose
      set ℓ₂ := h2_ex.choose
      have hsep1 := h1_ex.choose_spec.1
      have hsep2 := h2_ex.choose_spec.1
      obtain ⟨hτ1_len, hlo1, hhi1, v₁, hop1⟩ := h1_ex.choose_spec.2.choose_spec
      obtain ⟨_, hlo2, hhi2, v₂, hop2⟩ := h2_ex.choose_spec.2.choose_spec
      rw [hfeq] at hop1 hlo1 hhi1
      set τ := h2_ex.choose_spec.2.choose
      have hop_eq := Option.some.inj (hop1.symm.trans hop2)
      have hy_eq : e₁.y = e₂.y := by injection hop_eq
      have he1_act := hA_sub (Finset.mem_filter.mp he₁).1
      have he2_act := hA_sub (Finset.mem_filter.mp he₂).1
      have hs1_bds := h36_2.2 e₁ ((mem_b3ExitAct_iff P proc chain e₁).mp he1_act).1
      have hs2_bds := h36_2.2 e₂ ((mem_b3ExitAct_iff P proc chain e₂).mp he2_act).1
      obtain ⟨hm_sp1, _, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 ℓ₁.succ)
        (u := e₁.s) hs1_bds.1 (by omega)
      obtain ⟨hm_sp2, _, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 ℓ₂.succ)
        (u := e₂.s) hs2_bds.1 (by omega)
      have hsp1_part := (hChain.2.2.1 ℓ₁.succ).1 _ hm_sp1
      have hsp2_part := (hChain.2.2.1 ℓ₂.succ).1 _ hm_sp2
      obtain ⟨m₁, _, hm1_Sp, hm1_min, _⟩ := (sMax_and_tauEmpty_props proc hbst_all
        hsp1_part.1 hsp1_part.2.1 hsp1_part.2.2).2.2.2.1 τ hlo1 hhi1
      obtain ⟨m₂, _, hm2_Sp, hm2_min, _⟩ := (sMax_and_tauEmpty_props proc hbst_all
        hsp2_part.1 hsp2_part.2.1 hsp2_part.2.2).2.2.2.1 τ hlo2 hhi2
      have hm_eq : m₁ = m₂ := Option.some.inj (hm1_min.symm.trans hm2_min)
      rw [hm_eq] at hm1_Sp
      exact hpin_by_m_and_y (Finset.mem_filter.mp he₁).1 (Finset.mem_filter.mp he₂).1
        hsep1 hsep2 hm1_Sp hm2_Sp hy_eq
  -- Combine numerical bounds to deduce `A_esc.card < 18 * P`
  have hlpre := bLeafPre_card_le hP h_3_6 proc hChain
  have hs1_bds := s1Set_card_bound hValid h_3_6 h_5_1 proc
  have hee_le := eEnter_card_le hValid h_3_6 proc
  have hintra_le := b3Intra_card_le hValid h_3_6 proc
  dsimp only at hs1_bds hee_le hintra_le
  dsimp only [chain] at hcatC_le hcatDPop_le hlpre
  have hA_sum : A_esc.card ≤
      catA.card + catB.card + catC.card + catDPop.card + catEUrot.card := by
    have hc := Finset.card_le_card hA_cov
    have u1 := Finset.card_union_le (catA ∪ catB ∪ catC ∪ catDPop) catEUrot
    have u2 := Finset.card_union_le (catA ∪ catB ∪ catC) catDPop
    have u3 := Finset.card_union_le (catA ∪ catB) catC
    have u4 := Finset.card_union_le catA catB
    omega
  refine ⟨A_esc, hA_sub, ?_, hact_total⟩
  omega
end Internal56

namespace Internal57
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

open SplayTree BinaryTree

/-! ## Section 0: Exact Upstream Types (`Challenge.lean` L140–166 & L287–341) -/

abbrev Ty_lem_3_1 : Prop :=
  ∀ {α : Type} [LinearOrder α]
    (t : BinaryTree α) (S : Set α), t.IsBST → IsLCAClosed t S →
    ((restrictTree t S).IsBST ∧ ∀ v : α, v ∈ restrictTree t S ↔ v ∈ t ∧ v ∈ S) ∧
    (∀ x y : α, IsSingleRotEdge t x y →
      let t' := rotateEdge t x y
      IsLCAClosed t' S →
        (x ∈ S ∧ y ∈ S →
          IsSingleRotEdge (restrictTree t S) x y ∧
            restrictTree t' S = rotateEdge (restrictTree t S) x y) ∧
        (¬ (x ∈ S ∧ y ∈ S) → restrictTree t' S = restrictTree t S)) ∧
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
           (xMax ∉ S → restrictTree tMax S = restrictTree t S)))

abbrev Ty_lem_3_6 : Prop :=
  ∀ (P : ℕ), 1 ≤ P → ∀ (proc : FoldedPopProcess P),
    ((∀ τ : ℕ, τ ≤ proc.steps.length →
        (proc.treeAt τ).IsBST ∧
        keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P ∧
        postorderL2OnV (proc.treeAt τ) = (proc.treeAt τ).toKeyList ∧
        ∀ v ∈ proc.treeAt τ, v < foldedParent P (proc.treeAt τ) v) ∧
     (∀ τ u v : ℕ, τ < proc.steps.length → proc.steps[τ]? = some (.upperRot u v) →
        let z := foldedParent P (proc.treeAt τ) v
        foldedParent P (proc.treeAt (τ + 1)) u = z ∧
        ∀ w ∈ proc.treeAt (τ + 1), w ≠ u →
          foldedParent P (proc.treeAt (τ + 1)) w = foldedParent P (proc.treeAt τ) w) ∧
     (∀ s : ℕ, 1 ≤ s → s ≤ P →
        let τ := proc.popStepIdx s
        (∀ e ∈ proc.rInt, e.stepIdx = τ →
          foldedParent P (proc.treeAt (τ + 1)) e.x = e.z) ∧
        (∀ w ∈ proc.treeAt (τ + 1), (∀ e ∈ proc.rInt, e.stepIdx = τ → w ≠ e.x) →
          foldedParent P (proc.treeAt (τ + 1)) w = foldedParent P (proc.treeAt τ) w)) ∧
     (∀ τ₁ τ₂ v : ℕ, τ₁ ≤ τ₂ → τ₂ ≤ proc.steps.length →
        v ∈ proc.treeAt τ₁ → v ∈ proc.treeAt τ₂ →
        foldedParent P (proc.treeAt τ₁) v ≤ foldedParent P (proc.treeAt τ₂) v ∧
        l2Ancestors P (proc.treeAt τ₂) v ⊆ l2Ancestors P (proc.treeAt τ₁) v)) ∧
    ((∀ τ : ℕ, τ ≤ proc.steps.length → proc.treeAt τ ≠ .nil →
        let ls := leftSpine (proc.treeAt τ)
        ∀ idx : Fin ls.length,
          let u_i := ls[idx]
          let u_next := if h : idx.val + 1 < ls.length then ls[idx.val + 1] else P + 1
          insert u_i (keyFinset ((subtreeAtKey (proc.treeAt τ) u_i).right)) =
            keyFinset (proc.treeAt τ) ∩ Finset.Icc u_i (u_next - 1)) ∧
     (∀ e ∈ proc.rInt,
        1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P ∧
        (∀ τ' ∈ Finset.Ico (e.stepIdx + 1) (proc.popStepIdx e.x),
          ∀ w : ℕ, proc.steps[τ']? = some (.push w) → w < e.x) ∧
        (∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
          ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z)))) ∧
    (proc.mBase ⊆ proc.rInt ∧
     proc.mBase.card ≤ 2 * P + proc.kRot ∧
     2 * P + proc.kRot < 4 * P ∧
     ∃ eL eR : InternalPopRot → InternalPopRot,
       Set.InjOn eL (proc.rInt \ proc.mBase : Set InternalPopRot) ∧
       Set.InjOn eR (proc.rInt \ proc.mBase : Set InternalPopRot) ∧
       ∀ e ∈ proc.rInt \ proc.mBase,
         eL e ∈ proc.rInt ∧
         eR e ∈ proc.rInt ∧
         proc.nextCascadeRot? (eL e) = some (eR e) ∧
         (eL e).s = (eR e).s ∧
         (eL e).s < e.s ∧
         (∀ e' ∈ proc.rInt, e'.x = e.x → e'.s < e.s → e'.s ≤ (eL e).s) ∧
         (eL e).x = e.x ∧
         (eL e).z = e.y ∧
         (eR e).x = e.y ∧
         (eL e).s < e.x ∧ e.x < (eL e).y ∧ (eL e).y < e.y ∧
         e.y < (eR e).y ∧ (eR e).y < (eR e).z)


/-! ## Section 1: Core BST, `rotateRightEdge`, `leftSpine`, `spliceMin`, and `lcaBST` Helpers -/

theorem mem_iff_mem_keyFinset {α : Type} [DecidableEq α] (t : BinaryTree α) (x : α) :
    x ∈ t ↔ x ∈ keyFinset t := by
  induction t with
  | nil => simp [keyFinset]
  | node k l r ihl ihr =>
    simp [keyFinset, BinaryTree.mem_node_iff, ihl, ihr]

theorem toKeyList_map {α β : Type} (f : α → β) :
    ∀ t : BinaryTree α, (t.map f).toKeyList = t.toKeyList.map f
  | .nil => rfl
  | .node k l r => by
    simp [BinaryTree.map, BinaryTree.toKeyList, toKeyList_map f l, toKeyList_map f r]

theorem mem_map_iff {α β : Type} (f : α → β) (t : BinaryTree α) (y : β) :
    y ∈ t.map f ↔ ∃ x ∈ t, f x = y := by
  rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_map, List.mem_map]
  simp only [← BinaryTree.mem_iff_mem_toKeyList]

theorem keyFinset_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (t : BinaryTree α) :
    keyFinset (t.map f) = (keyFinset t).image f := by
  ext y
  simp [← mem_iff_mem_keyFinset, mem_map_iff]

theorem leftSpine_map {α β : Type} (f : α → β) :
    ∀ t : BinaryTree α, leftSpine (t.map f) = (leftSpine t).map f
  | .nil => rfl
  | .node k l r => by
    simp [BinaryTree.map, leftSpine, leftSpine_map f l]

theorem spliceMin_map {α β : Type} (f : α → β) :
    ∀ t : BinaryTree α, (spliceMin t).map f = spliceMin (t.map f)
  | .nil => rfl
  | .node _ .nil _ => rfl
  | .node k (.node lk ll lr) r => by
    simp [spliceMin, BinaryTree.map, spliceMin_map f (.node lk ll lr)]

theorem map_isBST_of_strictMonoOn {α β : Type} [LinearOrder α] [LinearOrder β]
    {t : BinaryTree α} (ht : t.IsBST) {f : α → β}
    (hf : ∀ x ∈ t, ∀ y ∈ t, x < y → f x < f y) :
    (t.map f).IsBST := by
  rw [SplayTree.IsBST_iff_toKeyList_sorted] at ht ⊢
  rw [toKeyList_map]
  have hmem : ∀ x ∈ t.toKeyList, x ∈ t := fun x hx => BinaryTree.mem_iff_mem_toKeyList.mpr hx
  have : ∀ (xs : List α), xs.Pairwise (· < ·) → (∀ x ∈ xs, x ∈ t) →
      (xs.map f).Pairwise (· < ·) := by
    intro xs hpw hsub
    induction xs with
    | nil => simp
    | cons a rest ih =>
      rw [List.pairwise_cons] at hpw
      simp only [List.map_cons, List.pairwise_cons, List.mem_map]
      refine ⟨?_, ih hpw.2 (fun x hx => hsub x (List.mem_cons_of_mem a hx))⟩
      rintro _ ⟨b, hb, rfl⟩
      exact hf a (hsub a List.mem_cons_self) b (hsub b (List.mem_cons_of_mem a hb)) (hpw.1 b hb)
  exact this t.toKeyList ht hmem

theorem toKeyList_rotateRightEdge {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) :
    (rotateRightEdge t x p).toKeyList = t.toKeyList := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    unfold rotateRightEdge
    split_ifs with h1 h2
    · simp [ihl]
    · simp [ihr]
    · cases l with
      | nil => rfl
      | node lx a b =>
        dsimp only
        split_ifs
        · simp [List.append_assoc]
        · rfl

theorem rotateRightEdge_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) (x p : α) : (rotateRightEdge t x p).IsBST :=
  SplayTree.IsBST_of_toKeyList_eq (toKeyList_rotateRightEdge t x p) ht

theorem mem_rotateRightEdge_iff {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p w : α) :
    w ∈ rotateRightEdge t x p ↔ w ∈ t := by
  rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_rotateRightEdge, ← BinaryTree.mem_iff_mem_toKeyList]

theorem keyFinset_rotateRightEdge {α : Type} [LinearOrder α] [DecidableEq α]
    (t : BinaryTree α) (x p : α) :
    keyFinset (rotateRightEdge t x p) = keyFinset t := by
  ext w
  simp [← mem_iff_mem_keyFinset, mem_rotateRightEdge_iff]

theorem isBSTAux_iff_forall_mem {α : Type} [LinearOrder α]
    (t : BinaryTree α) (lb ub : Option α) :
    IsBSTAux t lb ub ↔
      t.IsBST ∧ ∀ x ∈ t, lb.elim True (· < x) ∧ ub.elim True (x < ·) := by
  induction t generalizing lb ub with
  | nil =>
    simp [BinaryTree.IsBST]
  | node k l r ihl ihr =>
    rw [BinaryTree.IsBSTAux_node, ihl lb (some k), ihr (some k) ub]
    constructor
    · rintro ⟨hlb, hub, ⟨hl_bst, hl_b⟩, ⟨hr_bst, hr_b⟩⟩
      have hbst : (BinaryTree.node k l r).IsBST := by
        rw [BinaryTree.IsBST_node]
        exact ⟨(ihl none (some k)).mpr ⟨hl_bst, fun x hx => ⟨trivial, (hl_b x hx).2⟩⟩,
               (ihr (some k) none).mpr ⟨hr_bst, fun x hx => ⟨(hr_b x hx).1, trivial⟩⟩⟩
      refine ⟨hbst, fun x hx => ?_⟩
      rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
      · exact ⟨hlb, hub⟩
      · obtain ⟨h1, h2⟩ := hl_b x hxl
        refine ⟨h1, ?_⟩
        cases ub with
        | none => trivial
        | some u => exact lt_trans h2 hub
      · obtain ⟨h1, h2⟩ := hr_b x hxr
        refine ⟨?_, h2⟩
        cases lb with
        | none => trivial
        | some l0 => exact lt_trans hlb h1
    · rintro ⟨hbst, hbnds⟩
      have hl_bst := BinaryTree.IsBST_left_of_IsBST hbst
      have hr_bst := BinaryTree.IsBST_right_of_IsBST hbst
      obtain ⟨hlb, hub⟩ := hbnds k .here
      refine ⟨hlb, hub,
        ⟨hl_bst, fun x hx => ⟨(hbnds x (.left hx)).1, BinaryTree.lt_of_IsBST_left l k r hbst hx⟩⟩,
        ⟨hr_bst, fun x hx => ⟨BinaryTree.gt_of_IsBST_right l k r hbst hx, (hbnds x (.right hx)).2⟩⟩⟩

theorem isBST_node_iff {α : Type} [LinearOrder α] (k : α) (l r : BinaryTree α) :
    (BinaryTree.node k l r).IsBST ↔
      l.IsBST ∧ r.IsBST ∧ (∀ x ∈ l, x < k) ∧ (∀ x ∈ r, k < x) := by
  rw [BinaryTree.IsBST_node, isBSTAux_iff_forall_mem, isBSTAux_iff_forall_mem]
  simp only [Option.elim, true_and, and_true]
  tauto

theorem minKey?_eq_none_iff {α : Type} (t : BinaryTree α) :
    t.minKey? = none ↔ t = .nil := by
  induction t with
  | nil => simp [BinaryTree.minKey?]
  | node k l r _ =>
    unfold BinaryTree.minKey?
    cases l.minKey? <;> simp

theorem minKey?_node_of_ne_nil {α : Type} (k : α) (l r : BinaryTree α) (hl : l ≠ .nil) :
    (BinaryTree.node k l r).minKey? = l.minKey? := by
  cases l with
  | nil => contradiction
  | node lk ll lr =>
    rw [BinaryTree.minKey?]
    cases h : (BinaryTree.node lk ll lr).minKey? with
    | none => exact absurd ((minKey?_eq_none_iff _).mp h) (by simp)
    | some _ => rfl

theorem minKey?_mem_and_le {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) {m : α} :
    t.minKey? = some m ↔ m ∈ t ∧ ∀ v ∈ t, m ≤ v := by
  induction t generalizing m with
  | nil => simp [BinaryTree.minKey?]
  | node k l r ihl _ =>
    obtain ⟨hl, hr, hlt, hgt⟩ := (isBST_node_iff k l r).mp ht
    unfold BinaryTree.minKey?
    cases hlm : l.minKey? with
    | none =>
      have hl_nil : l = .nil := (minKey?_eq_none_iff l).mp hlm
      subst hl_nil
      simp only [Option.some.injEq, BinaryTree.mem_node_iff, BinaryTree.not_mem_nil, false_or]
      constructor
      · rintro rfl
        refine ⟨Or.inl rfl, ?_⟩
        rintro v (rfl | hvr)
        · exact le_rfl
        · exact le_of_lt (hgt v hvr)
      · rintro ⟨rfl | hmr, hle⟩
        · rfl
        · exact le_antisymm (le_of_lt (hgt m hmr)) (hle k (Or.inl rfl))
    | some ml =>
      obtain ⟨hml_in, hml_le⟩ := (ihl hl).mp hlm
      have hml_lt_k : ml < k := hlt ml hml_in
      simp only [Option.some.injEq]
      constructor
      · rintro rfl
        refine ⟨.left hml_in, fun v hv => ?_⟩
        rcases BinaryTree.mem_node_iff.mp hv with rfl | hvl | hvr
        · exact le_of_lt hml_lt_k
        · exact hml_le v hvl
        · exact le_of_lt (lt_trans hml_lt_k (hgt v hvr))
      · rintro ⟨hm_in, hm_le⟩
        have h1 : m ≤ ml := hm_le ml (.left hml_in)
        have h2 : ml ≤ m := by
          rcases BinaryTree.mem_node_iff.mp hm_in with rfl | hml' | hmr'
          · exact le_of_lt hml_lt_k
          · exact hml_le m hml'
          · exact le_of_lt (lt_trans hml_lt_k (hgt m hmr'))
        exact le_antisymm h2 h1

theorem spliceMin_spec {α : Type} [LinearOrder α] [DecidableEq α] {t : BinaryTree α}
    (ht : t.IsBST) {m : α} (hm : t.minKey? = some m) :
    (spliceMin t).IsBST ∧ keyFinset (spliceMin t) = (keyFinset t).erase m := by
  induction t with
  | nil => simp [BinaryTree.minKey?] at hm
  | node k l r ihl _ =>
    obtain ⟨hl, hr, hlt, hgt⟩ := (isBST_node_iff k l r).mp ht
    cases l with
    | nil =>
      simp only [BinaryTree.minKey?, Option.some.injEq] at hm
      subst hm
      refine ⟨hr, ?_⟩
      ext v
      simp only [spliceMin, keyFinset, Finset.empty_union, Finset.mem_erase, Finset.mem_insert]
      constructor
      · intro hv
        exact ⟨ne_of_gt (hgt v ((mem_iff_mem_keyFinset r v).mpr hv)), Or.inr hv⟩
      · rintro ⟨hne, rfl | hv⟩
        · exact absurd rfl hne
        · exact hv
    | node lk ll lr =>
      have hlm : (BinaryTree.node lk ll lr).minKey? = some m := by
        rwa [minKey?_node_of_ne_nil k _ r (by simp)] at hm
      obtain ⟨hl'_bst, hl'_keys⟩ := ihl hl hlm
      have hm_lt_k : m < k := hlt m ((minKey?_mem_and_le hl).mp hlm).1
      simp only [spliceMin]
      refine ⟨?_, ?_⟩
      · rw [isBST_node_iff]
        refine ⟨hl'_bst, hr, fun x hx => ?_, hgt⟩
        have hx_in : x ∈ BinaryTree.node lk ll lr := by
          rw [mem_iff_mem_keyFinset] at hx ⊢
          rw [hl'_keys] at hx
          exact Finset.mem_of_mem_erase hx
        exact hlt x hx_in
      · ext v
        simp only [keyFinset, hl'_keys, Finset.mem_insert, Finset.mem_union, Finset.mem_erase]
        by_cases hvm : v = m
        · rw [hvm]
          have hne_k : m ≠ k := ne_of_lt hm_lt_k
          have hnot_r : m ∉ keyFinset r := fun hmr =>
            lt_asymm hm_lt_k (hgt m ((mem_iff_mem_keyFinset r m).mpr hmr))
          simp [hne_k, hnot_r]
        · simp [hvm]

theorem mem_of_mem_leftSpine {α : Type} {t : BinaryTree α} {x : α}
    (hx : x ∈ leftSpine t) : x ∈ t := by
  induction t with
  | nil => simp [leftSpine] at hx
  | node k l r ihl _ =>
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with hl | rfl
    · exact .left (ihl hl)
    · exact .here

theorem leftSpine_pairwise_lt {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) : (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    obtain ⟨hl, _, hlt, _⟩ := (isBST_node_iff k l r).mp ht
    rw [leftSpine, List.pairwise_append]
    refine ⟨ihl hl, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton.mp hb]
    exact hlt a (mem_of_mem_leftSpine ha)

theorem leftSpine_spliceMin_suffix {α : Type} :
    ∀ t : BinaryTree α, t ≠ .nil → ∃ pref : List α, leftSpine (spliceMin t) = pref ++ (leftSpine t).tail
  | .nil, h => absurd rfl h
  | .node k .nil r, _ => ⟨leftSpine r, by simp [spliceMin, leftSpine]⟩
  | .node k (.node lk ll lr) r, _ => by
    obtain ⟨pref, hpref⟩ := leftSpine_spliceMin_suffix (.node lk ll lr) (by simp)
    refine ⟨pref, ?_⟩
    simp only [spliceMin, leftSpine, hpref, List.append_assoc]
    congr 1
    cases leftSpine ll <;> simp

theorem subtreeAtKey_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) (v : α) : (subtreeAtKey t v).IsBST := by
  induction t with
  | nil => exact ht
  | node k l r ihl ihr =>
    obtain ⟨hl, hr, _, _⟩ := (isBST_node_iff k l r).mp ht
    unfold subtreeAtKey
    split_ifs
    · exact ihl hl
    · exact ihr hr
    · exact ht

theorem mem_of_mem_subtreeAtKey {α : Type} [LinearOrder α] {t : BinaryTree α} {u v : α}
    (hv : v ∈ subtreeAtKey t u) : v ∈ t := by
  induction t with
  | nil => simp [subtreeAtKey] at hv
  | node k l r ihl ihr =>
    unfold subtreeAtKey at hv
    split_ifs at hv
    · exact .left (ihl hv)
    · exact .right (ihr hv)
    · exact hv

theorem mem_of_isRightRotEdge {α : Type} [LinearOrder α] {t : BinaryTree α} {x y : α}
    (h : IsRightRotEdge t x y) : x ∈ t ∧ y ∈ t := by
  rcases h with ⟨A, B, C, hy, hsub⟩
  have hx_sub : x ∈ subtreeAtKey t y := by rw [hsub]; exact .left .here
  exact ⟨mem_of_mem_subtreeAtKey hx_sub, hy⟩

theorem leftSpine_adj_edge {α : Type} [LinearOrder α] (S : BinaryTree α) (hS : S.IsBST)
    (j : ℕ) (hj : j + 1 < (leftSpine S).length) :
    let x := (leftSpine S)[j]
    let y := (leftSpine S)[j + 1]
    x < y ∧ IsRightRotEdge S x y := by
  induction S with
  | nil => simp [leftSpine] at hj
  | node k l r ihl _ =>
    obtain ⟨hl, _, hlt, _⟩ := (isBST_node_iff k l r).mp hS
    by_cases hjl : j + 1 < (leftSpine l).length
    · have hget_j : (leftSpine (.node k l r))[j] = (leftSpine l)[j] := by
        simp [leftSpine, List.getElem_append_left (by omega : j < (leftSpine l).length)]
      have hget_j1 : (leftSpine (.node k l r))[j + 1] = (leftSpine l)[j + 1] := by
        simp [leftSpine, List.getElem_append_left hjl]
      obtain ⟨hxy, A, B, C, hyl, hsub⟩ := ihl hl hjl
      have hyk : (leftSpine l)[j + 1] < k := hlt _ hyl
      refine ⟨?_, A, B, C, ?_, ?_⟩
      · simpa only [hget_j, hget_j1] using hxy
      · rw [hget_j1]; exact .left hyl
      · rw [hget_j, hget_j1]; simp [subtreeAtKey, hyk, hsub]
    · have hj_eq : j + 1 = (leftSpine l).length := by simp [leftSpine] at hj; omega
      cases l with
      | nil => simp [leftSpine] at hj_eq
      | node lx A B =>
        have hj_A : j = (leftSpine A).length := by simp [leftSpine] at hj_eq; omega
        have hx_eq : (leftSpine (.node k (.node lx A B) r))[j] = lx := by
          simp [leftSpine, hj_A]
        have hy_eq : (leftSpine (.node k (.node lx A B) r))[j + 1] = k := by
          simp [leftSpine, hj_A]
        refine ⟨?_, A, B, r, ?_, ?_⟩
        · simp only [hx_eq, hy_eq]; exact hlt lx .here
        · simp [hy_eq]
        · simp [hx_eq, hy_eq, subtreeAtKey]

def removeAt {α : Type} : List α → ℕ → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, i + 1 => x :: removeAt xs i

theorem removeAt_append_left {α : Type} (xs ys : List α) (i : ℕ) (hi : i < xs.length) :
    removeAt (xs ++ ys) i = removeAt xs i ++ ys := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [removeAt]
    | succ i =>
      simp only [List.length_cons] at hi
      simp [removeAt, ih i (by omega)]

theorem removeAt_append_two {α : Type} (xs : List α) (x y : α) (ys : List α) :
    removeAt (xs ++ x :: y :: ys) (xs.length + 1) = xs ++ x :: ys := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have heq : (a :: xs).length + 1 = (xs.length + 1) + 1 := by
      simp only [List.length_cons]
    rw [heq]
    simp [removeAt, ih]

theorem leftSpine_rotateRightEdge_removeAt {α : Type} [LinearOrder α] (S : BinaryTree α)
    (hS : S.IsBST) (j : ℕ) (hj : j + 1 < (leftSpine S).length) :
    leftSpine (rotateRightEdge S ((leftSpine S)[j]) ((leftSpine S)[j + 1])) =
      removeAt (leftSpine S) (j + 1) := by
  induction S with
  | nil => simp [leftSpine] at hj
  | node k l r ihl _ =>
    obtain ⟨hl, _, hlt, _⟩ := (isBST_node_iff k l r).mp hS
    by_cases hjl : j + 1 < (leftSpine l).length
    · have hget_j : (leftSpine (.node k l r))[j] = (leftSpine l)[j] := by
        simp [leftSpine, List.getElem_append_left (by omega : j < (leftSpine l).length)]
      have hget_j1 : (leftSpine (.node k l r))[j + 1] = (leftSpine l)[j + 1] := by
        simp [leftSpine, List.getElem_append_left hjl]
      have hyk : (leftSpine l)[j + 1] < k := hlt _ (mem_of_mem_leftSpine (List.getElem_mem hjl))
      rw [hget_j, hget_j1]
      simp only [rotateRightEdge, hyk, ↓reduceIte, leftSpine]
      rw [ihl hl hjl, removeAt_append_left (leftSpine l) [k] (j + 1) hjl]
    · have hj_eq : j + 1 = (leftSpine l).length := by simp [leftSpine] at hj; omega
      cases l with
      | nil => simp [leftSpine] at hj_eq
      | node lx A B =>
        have hj_A : j = (leftSpine A).length := by simp [leftSpine] at hj_eq; omega
        have hx_eq : (leftSpine (.node k (.node lx A B) r))[j] = lx := by
          simp [leftSpine, hj_A]
        have hy_eq : (leftSpine (.node k (.node lx A B) r))[j + 1] = k := by
          simp [leftSpine, hj_A]
        rw [hx_eq, hy_eq]
        simp only [rotateRightEdge, lt_irrefl, ↓reduceIte, leftSpine, List.append_assoc,
          List.singleton_append, hj_A]
        exact (removeAt_append_two (leftSpine A) lx k []).symm

theorem rightRotReachable_single {α : Type} [LinearOrder α] {t : BinaryTree α}
    {x y : α} (hxy : x < y) (hedge : IsRightRotEdge t x y) :
    RightRotReachable t (rotateRightEdge t x y) :=
  Relation.ReflTransGen.single ⟨x, y, hxy, hedge, rfl⟩

theorem rightRotReachable_isBST_and_mem {α : Type} [LinearOrder α]
    {t₁ t₂ : BinaryTree α} (ht₁ : t₁.IsBST) (h : RightRotReachable t₁ t₂) :
    t₂.IsBST ∧ ∀ w : α, w ∈ t₂ ↔ w ∈ t₁ := by
  induction h with
  | refl => exact ⟨ht₁, fun _ => Iff.rfl⟩
  | tail _ hstep ih =>
    rcases hstep with ⟨x, y, _, _, rfl⟩
    exact ⟨rotateRightEdge_isBST ih.1 x y, fun w => (mem_rotateRightEdge_iff _ x y w).trans (ih.2 w)⟩

theorem rightRotReachable_node_left {α : Type} [LinearOrder α]
    {k : α} {l₁ l₂ r : BinaryTree α} (hl₁ : l₁.IsBST) (hlt : ∀ z ∈ l₁, z < k)
    (h : RightRotReachable l₁ l₂) :
    RightRotReachable (.node k l₁ r) (.node k l₂ r) := by
  induction h with
  | refl => exact .refl
  | tail hprev hstep ih =>
    rcases hstep with ⟨x, y, hxy, hedge, rfl⟩
    rename_i mid
    obtain ⟨_, hmem_mid⟩ := rightRotReachable_isBST_and_mem hl₁ hprev
    have hy_lt_k : y < k := hlt y ((hmem_mid y).mp (mem_of_isRightRotEdge hedge).2)
    rcases hedge with ⟨A, B, C, hy_mid, hsub⟩
    have hedge_node : IsRightRotEdge (.node k mid r) x y :=
      ⟨A, B, C, .left hy_mid, by simp [subtreeAtKey, hy_lt_k, hsub]⟩
    have hrot_node : rotateRightEdge (.node k mid r) x y = .node k (rotateRightEdge mid x y) r := by
      simp [rotateRightEdge, hy_lt_k]
    exact ih.tail ⟨x, y, hxy, hedge_node, hrot_node.symm⟩

theorem rightRotReachable_node_right {α : Type} [LinearOrder α]
    {k : α} {l r₁ r₂ : BinaryTree α} (hr₁ : r₁.IsBST) (hgt : ∀ z ∈ r₁, k < z)
    (h : RightRotReachable r₁ r₂) :
    RightRotReachable (.node k l r₁) (.node k l r₂) := by
  induction h with
  | refl => exact .refl
  | tail hprev hstep ih =>
    rcases hstep with ⟨x, y, hxy, hedge, rfl⟩
    rename_i mid
    obtain ⟨_, hmem_mid⟩ := rightRotReachable_isBST_and_mem hr₁ hprev
    have hk_lt_y : k < y := hgt y ((hmem_mid y).mp (mem_of_isRightRotEdge hedge).2)
    have hnot : ¬ y < k := not_lt_of_gt hk_lt_y
    rcases hedge with ⟨A, B, C, hy_mid, hsub⟩
    have hedge_node : IsRightRotEdge (.node k l mid) x y :=
      ⟨A, B, C, .right hy_mid, by simp [subtreeAtKey, hnot, hk_lt_y, hsub]⟩
    have hrot_node : rotateRightEdge (.node k l mid) x y = .node k l (rotateRightEdge mid x y) := by
      simp [rotateRightEdge, hnot, hk_lt_y]
    exact ih.tail ⟨x, y, hxy, hedge_node, hrot_node.symm⟩

theorem rightRotReachable_rotMinToRoot {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) {m : α} (hm : t.minKey? = some m) :
    RightRotReachable t (.node m .nil (spliceMin t)) := by
  induction t with
  | nil => simp [BinaryTree.minKey?] at hm
  | node k l r ihl _ =>
    obtain ⟨hl, _, hlt, _⟩ := (isBST_node_iff k l r).mp ht
    cases l with
    | nil =>
      simp only [BinaryTree.minKey?, Option.some.injEq] at hm
      subst hm
      exact .refl
    | node lk ll lr =>
      have hlm : (BinaryTree.node lk ll lr).minKey? = some m := by
        rwa [minKey?_node_of_ne_nil k _ r (by simp)] at hm
      have h1 := rightRotReachable_node_left (r := r) hl hlt (ihl hl hlm)
      have hm_lt_k : m < k := hlt m ((minKey?_mem_and_le hl).mp hlm).1
      have hedge : IsRightRotEdge (.node k (.node m .nil (spliceMin (.node lk ll lr))) r) m k :=
        ⟨.nil, spliceMin (.node lk ll lr), r, .here, by simp [subtreeAtKey]⟩
      have hrot : rotateRightEdge (.node k (.node m .nil (spliceMin (.node lk ll lr))) r) m k =
          .node m .nil (spliceMin (.node k (.node lk ll lr) r)) := by
        simp [rotateRightEdge, spliceMin]
      exact h1.tail ⟨m, k, hm_lt_k, hedge, hrot.symm⟩

theorem leftSpine_adj_of_getElem? {α : Type} [LinearOrder α] {S : BinaryTree α}
    (hS : S.IsBST) {j : ℕ} {x y : α}
    (hx : (leftSpine S)[j]? = some x) (hy : (leftSpine S)[j + 1]? = some y) :
    x < y ∧ IsRightRotEdge S x y ∧
      leftSpine (rotateRightEdge S x y) = removeAt (leftSpine S) (j + 1) := by
  obtain ⟨hj1, rfl⟩ := List.getElem?_eq_some_iff.mp hy
  obtain ⟨_, hxeq⟩ := List.getElem?_eq_some_iff.mp hx
  subst hxeq
  obtain ⟨hxy, hedge⟩ := leftSpine_adj_edge S hS j hj1
  exact ⟨hxy, hedge, leftSpine_rotateRightEdge_removeAt S hS j hj1⟩

theorem getElem?_append_cons_zero {α : Type} (pref : List α) (a : α) (rest : List α) :
    (pref ++ a :: rest)[pref.length]? = some a := by
  simp

theorem getElem?_append_cons_one {α : Type} (pref : List α) (a b : α) (rest : List α) :
    (pref ++ a :: b :: rest)[pref.length + 1]? = some b := by
  rw [List.getElem?_append_right (by omega)]
  simp

theorem removeAt_append_add {α : Type} (u v : List α) (m : ℕ) :
    removeAt (u ++ v) (u.length + m) = u ++ removeAt v m := by
  induction u with
  | nil => simp
  | cons hd tl ih =>
    have heq : (hd :: tl).length + m = (tl.length + m) + 1 := by
      simp only [List.length_cons]; omega
    rw [heq]
    simp [removeAt, ih]

theorem foldl_adjacentPairs_reachable {α : Type} [LinearOrder α] :
    ∀ (n : ℕ) (ys : List α) (t : BinaryTree α) (pref suff : List α),
      t.IsBST → leftSpine t = pref ++ ys ++ suff →
      let out := ((adjacentPairs ys).take n).foldl (fun acc p => rotateRightEdge acc p.1 p.2) t
      RightRotReachable t out ∧
      ∃ pref', leftSpine out = pref' ++ (ys.drop (2 * n)) ++ suff
  | 0, ys, t, pref, suff, _, hls => ⟨.refl, pref, by simpa using hls⟩
  | _ + 1, [], t, pref, suff, _, hls => ⟨.refl, pref, by simpa [adjacentPairs] using hls⟩
  | n + 1, [a], t, pref, suff, _, hls =>
    ⟨.refl, pref ++ [a], by
      have hd : ([a] : List α).drop (2 * (n + 1)) = [] :=
        List.drop_eq_nil_of_le (by simp only [List.length_singleton]; omega)
      simpa [adjacentPairs, hd, List.append_assoc] using hls⟩
  | n + 1, a :: b :: ys, t, pref, suff, ht, hls => by
    have hls' : leftSpine t = pref ++ a :: b :: (ys ++ suff) := by
      simpa [List.append_assoc] using hls
    have hget0 : (leftSpine t)[pref.length]? = some a := by
      rw [hls']; exact getElem?_append_cons_zero pref a _
    have hget1 : (leftSpine t)[pref.length + 1]? = some b := by
      rw [hls']; exact getElem?_append_cons_one pref a b _
    obtain ⟨hab, hedge, hrem⟩ := leftSpine_adj_of_getElem? ht hget0 hget1
    set t₁ := rotateRightEdge t a b
    have ht₁ : t₁.IsBST := rotateRightEdge_isBST ht a b
    have hls₁ : leftSpine t₁ = (pref ++ [a]) ++ ys ++ suff := by
      rw [hrem, hls', removeAt_append_two]
      simp [List.append_assoc]
    obtain ⟨hreach_rest, pref', hls_out⟩ :=
      foldl_adjacentPairs_reachable n ys t₁ (pref ++ [a]) suff ht₁ hls₁
    have hdrop : (a :: b :: ys).drop (2 * (n + 1)) = ys.drop (2 * n) := by
      have : 2 * (n + 1) = (2 * n) + 2 := by omega
      rw [this]; rfl
    refine ⟨(rightRotReachable_single hab hedge).trans hreach_rest, pref', ?_⟩
    simpa [adjacentPairs, hdrop] using hls_out

theorem rotateRightEdge_comm_spine {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) {x₁ y₁ x₂ y₂ : α}
    (h12 : y₁ < x₂) (hy₂_ls : y₂ ∈ leftSpine t) (hedge₂ : IsRightRotEdge t x₂ y₂) :
    rotateRightEdge (rotateRightEdge t x₁ y₁) x₂ y₂ =
      rotateRightEdge (rotateRightEdge t x₂ y₂) x₁ y₁ := by
  rcases hedge₂ with ⟨A₂, B₂, C₂, -, hsub₂⟩
  induction t with
  | nil => simp [leftSpine] at hy₂_ls
  | node k l r ihl _ =>
    obtain ⟨hl, _, hlt, _⟩ := (isBST_node_iff k l r).mp ht
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hy₂_ls
    rcases hy₂_ls with hy₂_l | rfl
    · have hy₂_lt_k : y₂ < k := hlt y₂ (mem_of_mem_leftSpine hy₂_l)
      have hy₁_lt_k : y₁ < k := lt_trans h12 (lt_trans (by
        simp only [subtreeAtKey, hy₂_lt_k, ↓reduceIte] at hsub₂
        have hbst_sub := subtreeAtKey_isBST hl y₂
        rw [hsub₂] at hbst_sub
        exact (isBST_node_iff y₂ (.node x₂ A₂ B₂) C₂).mp hbst_sub |>.2.2.1 x₂ .here) hy₂_lt_k)
      simp only [subtreeAtKey, hy₂_lt_k, ↓reduceIte] at hsub₂
      simp only [rotateRightEdge, hy₁_lt_k, hy₂_lt_k, ↓reduceIte]
      rw [ihl hl hy₂_l hsub₂]
    · simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub₂
      injection hsub₂ with _ hl_eq hr_eq
      subst hl_eq hr_eq
      have hx₂_lt_y₂ : x₂ < y₂ := hlt x₂ .here
      have hy₁_lt_y₂ : y₁ < y₂ := lt_trans h12 hx₂_lt_y₂
      simp [rotateRightEdge, hy₁_lt_y₂, h12]

theorem pull_pair_to_front_reachable {α : Type} [LinearOrder α] :
    ∀ (idx h : ℕ) (ys : List α) (t : BinaryTree α) (pref suff : List α)
      (_ : t.IsBST) (_ : leftSpine t = pref ++ ys ++ suff)
      (_ : idx < h) (hlen : 2 * idx + 1 < ys.length),
      let x := ys[2 * idx]'(by omega)
      let y := ys[2 * idx + 1]'hlen
      let pairs := (adjacentPairs ys).take h
      x < y ∧ IsRightRotEdge t x y ∧
        RightRotReachable (rotateRightEdge t x y)
          (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t)
  | 0, h + 1, a :: b :: ys, t, pref, suff, ht, hls, _, _ => by
    have hls' : leftSpine t = pref ++ a :: b :: (ys ++ suff) := by
      simpa [List.append_assoc] using hls
    have hget0 : (leftSpine t)[pref.length]? = some a := by
      rw [hls']; exact getElem?_append_cons_zero pref a _
    have hget1 : (leftSpine t)[pref.length + 1]? = some b := by
      rw [hls']; exact getElem?_append_cons_one pref a b _
    obtain ⟨hab, hedge, hrem⟩ := leftSpine_adj_of_getElem? ht hget0 hget1
    set t₁ := rotateRightEdge t a b
    have ht₁ : t₁.IsBST := rotateRightEdge_isBST ht a b
    have hls₁ : leftSpine t₁ = (pref ++ [a]) ++ ys ++ suff := by
      rw [hrem, hls', removeAt_append_two]
      simp [List.append_assoc]
    obtain ⟨hreach, _⟩ := foldl_adjacentPairs_reachable h ys t₁ (pref ++ [a]) suff ht₁ hls₁
    exact ⟨hab, hedge, hreach⟩
  | idx + 1, h + 1, a :: b :: ys, t, pref, suff, ht, hls, hidx_lt, hlen => by
    have hidx' : idx < h := by omega
    have hlen' : 2 * idx + 1 < ys.length := by
      simp only [List.length_cons] at hlen; omega
    set x := ys[2 * idx]'(by omega)
    set y := ys[2 * idx + 1]'hlen'
    have hls' : leftSpine t = pref ++ a :: b :: (ys ++ suff) := by
      simpa [List.append_assoc] using hls
    have hget_a : (leftSpine t)[pref.length]? = some a := by
      rw [hls']; exact getElem?_append_cons_zero pref a _
    have hget_b : (leftSpine t)[pref.length + 1]? = some b := by
      rw [hls']; exact getElem?_append_cons_one pref a b _
    obtain ⟨hab, hedge_ab, hrem_ab⟩ := leftSpine_adj_of_getElem? ht hget_a hget_b
    have hls_split : leftSpine t = (pref ++ [a, b]) ++ (ys ++ suff) := by
      simpa [List.append_assoc] using hls
    have hget_x : (leftSpine t)[(pref ++ [a, b]).length + 2 * idx]? = some x := by
      rw [hls_split, List.getElem?_append_right (by omega)]
      have hk : (pref ++ [a, b]).length + 2 * idx - (pref ++ [a, b]).length = 2 * idx := by omega
      rw [hk, List.getElem?_append_left (by omega : 2 * idx < ys.length),
          List.getElem?_eq_getElem (by omega : 2 * idx < ys.length)]
    have hget_y : (leftSpine t)[((pref ++ [a, b]).length + 2 * idx) + 1]? = some y := by
      rw [hls_split, List.getElem?_append_right (by omega)]
      have hk : ((pref ++ [a, b]).length + 2 * idx) + 1 - (pref ++ [a, b]).length = 2 * idx + 1 := by omega
      rw [hk, List.getElem?_append_left hlen', List.getElem?_eq_getElem hlen']
    obtain ⟨hxy, hedge_xy, hrem_xy⟩ := leftSpine_adj_of_getElem? ht hget_x hget_y
    have hpw : (leftSpine t).Pairwise (· < ·) := leftSpine_pairwise_lt ht
    have hb_lt_x : b < x := by
      obtain ⟨hjb, hb_eq⟩ := List.getElem?_eq_some_iff.mp hget_b
      obtain ⟨hjx, hx_eq⟩ := List.getElem?_eq_some_iff.mp hget_x
      rw [← hb_eq, ← hx_eq]
      exact List.pairwise_iff_getElem.mp hpw (pref.length + 1) ((pref ++ [a, b]).length + 2 * idx)
        hjb hjx (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    have hy_ls : y ∈ leftSpine t := List.mem_of_getElem? hget_y
    have hcomm : rotateRightEdge (rotateRightEdge t a b) x y =
        rotateRightEdge (rotateRightEdge t x y) a b :=
      rotateRightEdge_comm_spine ht hb_lt_x hy_ls hedge_xy
    set t_xy := rotateRightEdge t x y
    have ht_xy : t_xy.IsBST := rotateRightEdge_isBST ht x y
    have hls_xy : leftSpine t_xy = pref ++ a :: b :: removeAt (ys ++ suff) (2 * idx + 1) := by
      have hidx_eq : ((pref ++ [a, b]).length + 2 * idx) + 1 =
          (pref ++ [a, b]).length + (2 * idx + 1) := by omega
      rw [hrem_xy, hls_split, hidx_eq, removeAt_append_add]
      simp [List.append_assoc]
    have hget_a_xy : (leftSpine t_xy)[pref.length]? = some a := by
      rw [hls_xy]; exact getElem?_append_cons_zero pref a _
    have hget_b_xy : (leftSpine t_xy)[pref.length + 1]? = some b := by
      rw [hls_xy]; exact getElem?_append_cons_one pref a b _
    obtain ⟨_, hedge_ab_xy, _⟩ := leftSpine_adj_of_getElem? ht_xy hget_a_xy hget_b_xy
    have hstep1 : RightRotReachable t_xy (rotateRightEdge t_xy a b) :=
      rightRotReachable_single hab hedge_ab_xy
    set t_ab := rotateRightEdge t a b
    have ht_ab : t_ab.IsBST := rotateRightEdge_isBST ht a b
    have hls_ab : leftSpine t_ab = (pref ++ [a]) ++ ys ++ suff := by
      rw [hrem_ab, hls', removeAt_append_two]
      simp [List.append_assoc]
    obtain ⟨_, _, hreach_ih⟩ :=
      pull_pair_to_front_reachable idx h ys t_ab (pref ++ [a]) suff ht_ab hls_ab hidx' hlen'
    rw [show ys[2 * idx] = x from rfl, show ys[2 * idx + 1] = y from rfl] at hreach_ih
    dsimp only [t_ab, t_xy] at hreach_ih hstep1
    rw [hcomm] at hreach_ih
    have hx_eq : (a :: b :: ys)[2 * (idx + 1)]'(by omega) = x := by
      have : 2 * (idx + 1) = (2 * idx) + 2 := by omega
      simp [this, x]
    have hy_eq : (a :: b :: ys)[2 * (idx + 1) + 1]'hlen = y := by
      have : 2 * (idx + 1) + 1 = (2 * idx + 1) + 2 := by omega
      simp [this, y]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hx_eq, hy_eq] using hxy
    · simpa only [hx_eq, hy_eq] using hedge_xy
    · rw [hx_eq, hy_eq]
      simp only [adjacentPairs, List.take_succ_cons, List.foldl_cons]
      exact hstep1.trans hreach_ih

theorem lcaBST_mem {α : Type} [LinearOrder α] :
    ∀ (t : BinaryTree α) (x y z : α), lcaBST t x y = some z → z ∈ t
  | .nil, _, _, _, h => by simp [lcaBST] at h
  | .node k l r, x, y, z, h => by
    unfold lcaBST at h
    split_ifs at h with h1 h2
    · exact .left (lcaBST_mem l x y z h)
    · exact .right (lcaBST_mem r x y z h)
    · injection h with hkz; subst hkz; exact .here

theorem lcaBST_between {α : Type} [LinearOrder α] :
    ∀ (t : BinaryTree α) (x y z : α), lcaBST t x y = some z → min x y ≤ z ∧ z ≤ max x y
  | .nil, _, _, _, h => by simp [lcaBST] at h
  | .node k l r, x, y, z, h => by
    unfold lcaBST at h
    split_ifs at h with h1 h2
    · exact lcaBST_between l x y z h
    · exact lcaBST_between r x y z h
    · injection h with hkz; subst hkz
      refine ⟨?_, ?_⟩
      · by_cases hkx : k < x
        · exact le_trans (min_le_right x y) (not_lt.mp (fun hky => h2 ⟨hkx, hky⟩))
        · exact le_trans (min_le_left x y) (not_lt.mp hkx)
      · by_cases hxk : x < k
        · exact le_trans (not_lt.mp (fun hyk => h1 ⟨hxk, hyk⟩)) (le_max_right x y)
        · exact le_trans (not_lt.mp hxk) (le_max_left x y)

theorem isLCAClosed_interval_oc (t : BinaryTree ℕ) (a b : ℕ) :
    IsLCAClosed t {u : ℕ | a < u ∧ u ≤ b} := by
  intro x _ y _ hx hy z hlca
  obtain ⟨hmin, hmax⟩ := lcaBST_between t x y z hlca
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  exact ⟨by omega, by omega⟩

theorem isLCAClosed_block (t : BinaryTree ℕ) (C : IntervalBlock) :
    IsLCAClosed t C.toSet := by
  intro x _ y _ hx hy z hlca
  obtain ⟨hmin, hmax⟩ := lcaBST_between t x y z hlca
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  exact ⟨by omega, by omega⟩


/-! ## Section 2: Scale-Tree Sub-blocks & `FoldedPopProcess` Exact Lifecycle Tracking -/

mutual
  theorem leafEntries_pos :
      ∀ (T : ScaleTree) (entry : ℕ × List ℕ), entry ∈ T.leafEntries → ∀ c ∈ entry.2, 1 ≤ c
    | .leaf s, entry, hentry, c, hc => by
      simp [ScaleTree.leafEntries] at hentry
      rcases hentry with ⟨_, rfl⟩
      cases hc
    | .internal cs, entry, hentry, c, hc =>
      leafEntriesChildren_pos 1 cs (by omega) entry hentry c hc

  theorem leafEntriesChildren_pos :
      ∀ (c₀ : ℕ) (cs : List ScaleTree), 1 ≤ c₀ →
        ∀ entry ∈ ScaleTree.leafEntriesChildren c₀ cs, ∀ c ∈ entry.2, 1 ≤ c
    | _, [], _, _, hentry, _, _ => by
      simp [ScaleTree.leafEntriesChildren] at hentry
    | c₀, child :: cs, hc₀, entry, hentry, c, hc => by
      simp only [ScaleTree.leafEntriesChildren, List.mem_append, List.mem_map] at hentry
      rcases hentry with ⟨⟨s, rest⟩, hmem, rfl⟩ | hrest
      · simp only [List.mem_cons] at hc
        rcases hc with rfl | hcrest
        · exact hc₀
        · exact leafEntries_pos child (s, rest) hmem c hcrest
      · exact leafEntriesChildren_pos (c₀ + 1) cs (by omega) entry hrest c hc
end

theorem pathWeight_pos (ξ : List ℕ) (hξ : ∀ c ∈ ξ, 1 ≤ c) : 1 ≤ pathWeight ξ := by
  unfold pathWeight
  suffices ∀ (xs : List ℕ), (∀ c ∈ xs, 1 ≤ c) → ∀ (init : ℕ), 1 ≤ init →
      1 ≤ xs.foldl (fun w c => w * (4 * c ^ 2)) init from
    this ξ hξ 1 (by omega)
  intro xs
  induction xs with
  | nil => intro _ init hinit; exact hinit
  | cons c rest ih =>
    intro hcons init hinit
    simp only [List.foldl_cons]
    have hc : 1 ≤ c := hcons c List.mem_cons_self
    have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => hcons x (List.mem_cons_of_mem c hx)
    apply ih hrest
    nlinarith

theorem scaleS_pos (T : ScaleTree) (P : ℕ) (hP : 1 ≤ P) : ∀ ℓ : ℕ, 1 ≤ scaleS T P ℓ
  | 0 => hP
  | ℓ + 1 => by
    unfold scaleS
    have hw : 1 ≤ leafWeight T (ℓ + 1) := by
      unfold leafWeight leafAddr
      split
      · next s addr hfind =>
        exact pathWeight_pos addr (leafEntries_pos T (s, addr) (List.mem_of_find?_eq_some hfind))
      · exact pathWeight_pos [] (by intro _ hc; cases hc)
    have hsq : 1 ≤ (alpha0 (2 * scaleS T P ℓ) + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    exact Nat.mul_le_mul hw hsq

theorem splitIntervalBySize_sizes (X : IntervalBlock) (S : ℕ)
    (_hXlo : 1 ≤ X.lo) (hS : 1 ≤ S) (h2S : 2 * S ≤ X.size) :
    2 ≤ (splitIntervalBySize X S).length ∧
    ∀ Y ∈ splitIntervalBySize X S,
      X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi ∧ S ≤ Y.size ∧ Y.size < 2 * S := by
  have hXle : X.lo ≤ X.hi := by
    unfold IntervalBlock.size at h2S
    split at h2S <;> omega
  have hXsz : X.size = X.hi - X.lo + 1 := by simp [IntervalBlock.size, hXle]
  unfold splitIntervalBySize
  have hcond : ¬ (S = 0 ∨ X.size < 2 * S) := by omega
  simp only [hcond, ↓reduceIte]
  set K := X.size / S
  have hK2 : 2 ≤ K := (Nat.le_div_iff_mul_le hS).mpr h2S
  have hdiv : S * K + X.size % S = X.size := Nat.div_add_mod X.size S
  have hmod : X.size % S < S := Nat.mod_lt X.size hS
  have hKS_comm : K * S = S * K := Nat.mul_comm K S
  refine ⟨by simp; exact hK2, ?_⟩
  intro Y hY
  rw [List.mem_map] at hY
  obtain ⟨idx, hidx, rfl⟩ := hY
  rw [List.mem_range] at hidx
  by_cases hlt : idx + 1 < K
  · simp only [hlt, ↓reduceIte]
    have hmul : (idx + 1) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
    have hstepS : idx * S + S = (idx + 1) * S := by ring
    have hlo_le_hi : X.lo + idx * S ≤ X.lo + (idx + 1) * S - 1 := by omega
    refine ⟨by omega, hlo_le_hi, by omega, ?_, ?_⟩
    · simp only [IntervalBlock.size, hlo_le_hi, ↓reduceIte]; omega
    · simp only [IntervalBlock.size, hlo_le_hi, ↓reduceIte]; omega
  · simp only [hlt, ↓reduceIte]
    have hidx_eq : idx = K - 1 := by omega
    subst hidx_eq
    have hK1S : (K - 1) * S + S = K * S := by
      have : (K - 1) + 1 = K := by omega
      calc (K - 1) * S + S = ((K - 1) + 1) * S := by ring
        _ = K * S := by rw [this]
    have hlo_le_hi : X.lo + (K - 1) * S ≤ X.hi := by omega
    refine ⟨by omega, hlo_le_hi, le_rfl, ?_, ?_⟩
    · simp only [IntervalBlock.size, hlo_le_hi, ↓reduceIte]; omega
    · simp only [IntervalBlock.size, hlo_le_hi, ↓reduceIte]; omega

theorem consecutiveBlocks_iff_getElem (xs : List IntervalBlock) :
    ConsecutiveBlocks xs ↔
      ∀ (i : ℕ) (h : i + 1 < xs.length), xs[i].hi + 1 = xs[i + 1].lo := by
  induction xs with
  | nil => simp [ConsecutiveBlocks]
  | cons c1 rest ih =>
    cases rest with
    | nil => simp [ConsecutiveBlocks]
    | cons c2 tl =>
      simp only [ConsecutiveBlocks, ih]
      constructor
      · rintro ⟨h01, hrest⟩ i hi
        cases i with
        | zero => exact h01
        | succ j => exact hrest j (by simpa using hi)
      · intro hall
        exact ⟨hall 0 (by simp), fun j hj => hall (j + 1) (by simpa using hj)⟩

theorem consecutiveBlocks_pairwise :
    ∀ {bs : List IntervalBlock}, (∀ B ∈ bs, B.lo ≤ B.hi) → ConsecutiveBlocks bs →
      bs.Pairwise (fun B₁ B₂ => B₁.hi < B₂.lo)
  | [], _, _ => .nil
  | [_], _, _ => List.pairwise_singleton _ _
  | B₁ :: B₂ :: rest, hle, ⟨h12, hrest⟩ => by
    have ih := consecutiveBlocks_pairwise (fun B hB => hle B (List.mem_cons_of_mem _ hB)) hrest
    refine List.Pairwise.cons (fun B hB => ?_) ih
    simp only [List.mem_cons] at hB
    rcases hB with rfl | hB_rest
    · omega
    · have h2B := (List.pairwise_cons.mp ih).1 B hB_rest
      have hB2 : B₂.lo ≤ B₂.hi := hle B₂ (List.mem_cons_of_mem _ List.mem_cons_self)
      omega

theorem consecutiveBlocks_cover {bs : List IntervalBlock} {a b u : ℕ}
    (hne : bs ≠ []) (hle : ∀ B ∈ bs, B.lo ≤ B.hi) (hc : ConsecutiveBlocks bs)
    (hhead : bs.head?.map IntervalBlock.lo = some a)
    (hlast : bs.getLast?.map IntervalBlock.hi = some b)
    (hau : a ≤ u) (hub : u ≤ b) :
    ∃ B ∈ bs, B.lo ≤ u ∧ u ≤ B.hi := by
  induction bs generalizing a with
  | nil => contradiction
  | cons B₁ rest ih =>
    cases rest with
    | nil =>
      simp at hhead hlast
      exact ⟨B₁, List.mem_cons_self, by omega, by omega⟩
    | cons B₂ rest' =>
      rcases hc with ⟨h12, hrest⟩
      simp at hhead
      by_cases hu1 : u ≤ B₁.hi
      · exact ⟨B₁, List.mem_cons_self, by omega, hu1⟩
      · have hu2 : B₂.lo ≤ u := by omega
        have hlast' : ((B₂ :: rest').getLast?.map IntervalBlock.hi) = some b := by
          simpa using hlast
        obtain ⟨B, hB, hlo, hhi⟩ := ih (List.cons_ne_nil _ _)
          (fun B h => hle B (List.mem_cons_of_mem _ h)) hrest (by simp) hlast' hu2
        exact ⟨B, List.mem_cons_of_mem _ hB, hlo, hhi⟩

theorem consecutiveBlocks_append {xs ys : List IntervalBlock}
    (hx : ConsecutiveBlocks xs) (hy : ConsecutiveBlocks ys)
    (hlink : ∀ last first, xs.getLast? = some last → ys.head? = some first →
      last.hi + 1 = first.lo) :
    ConsecutiveBlocks (xs ++ ys) := by
  induction xs with
  | nil => simpa using hy
  | cons x rest ih =>
    cases rest with
    | nil =>
      cases ys with
      | nil => simp [ConsecutiveBlocks]
      | cons y yrest =>
        simp only [List.singleton_append, ConsecutiveBlocks]
        exact ⟨hlink x y rfl rfl, hy⟩
    | cons x₂ rest' =>
      simp only [List.cons_append, ConsecutiveBlocks] at hx ⊢
      refine ⟨hx.1, ih hx.2 (fun last first hl hf => hlink last first ?_ hf)⟩
      simpa using hl

theorem splitIntervalBySize_props (X : IntervalBlock) (S : ℕ) (hX : X.lo ≤ X.hi) :
    let subs := splitIntervalBySize X S
    subs ≠ [] ∧
    (∀ Y ∈ subs, X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi) ∧
    ConsecutiveBlocks subs ∧
    subs.head?.map IntervalBlock.lo = some X.lo ∧
    subs.getLast?.map IntervalBlock.hi = some X.hi := by
  dsimp only
  unfold splitIntervalBySize
  dsimp only
  set sz := X.size
  have hsz : sz = X.hi - X.lo + 1 := by simp [sz, IntervalBlock.size, hX]
  split_ifs with hsmall
  · refine ⟨List.cons_ne_nil _ _, ?_, trivial, by simp, by simp⟩
    intro Y hY; simp at hY; subst hY; exact ⟨le_rfl, hX, le_rfl⟩
  · have hS1 : 1 ≤ S := by omega
    have h2S : 2 * S ≤ sz := by omega
    set K := sz / S
    have hK2 : 2 ≤ K := (Nat.le_div_iff_mul_le hS1).mpr h2S
    have hKS_le : K * S ≤ sz := Nat.div_mul_le_self sz S
    let f : ℕ → IntervalBlock := fun idx =>
      if idx + 1 < K then ⟨X.lo + idx * S, X.lo + (idx + 1) * S - 1⟩
      else ⟨X.lo + idx * S, X.hi⟩
    change (List.range K).map f ≠ [] ∧ _
    have hne : (List.range K).map f ≠ [] := by
      simp [List.map_eq_nil_iff, List.range_eq_nil]; omega
    refine ⟨hne, ?_, ?_, ?_, ?_⟩
    · intro Y hY
      rw [List.mem_map] at hY
      obtain ⟨idx, hidx, rfl⟩ := hY
      rw [List.mem_range] at hidx
      split_ifs with hlt <;> dsimp only
      · have h1 : (idx + 1) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
        have h2 : idx * S + 1 ≤ (idx + 1) * S := by nlinarith
        exact ⟨by omega, by omega, by omega⟩
      · have hidx_eq : idx = K - 1 := by omega
        subst hidx_eq
        have h1 : (K - 1) * S + S = K * S := by
          have : K - 1 + 1 = K := by omega
          nlinarith
        exact ⟨by omega, by omega, le_rfl⟩
    · rw [consecutiveBlocks_iff_getElem]
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      simp only [List.getElem_map, List.getElem_range]
      have hfi_hi : (f i).hi = X.lo + (i + 1) * S - 1 := by simp [f, hi]
      have hfi1_lo : (f (i + 1)).lo = X.lo + (i + 1) * S := by
        dsimp only [f]; split_ifs <;> rfl
      rw [hfi_hi, hfi1_lo]
      have hpos : 1 ≤ (i + 1) * S := by nlinarith
      omega
    · have hK_pos : 0 < K := by omega
      rw [List.head?_map, List.head?_range]
      simp only [Nat.pos_iff_ne_zero.mp hK_pos, ↓reduceIte, Option.map_some]
      have : 0 + 1 < K := by omega
      simp [this]
    · have hrange : List.range K = List.range (K - 1) ++ [K - 1] := by
        conv_lhs => rw [show K = (K - 1) + 1 by omega]
        exact List.range_succ
      rw [hrange, List.map_append, List.map_singleton,
        List.getLast?_append_of_ne_nil _ (by simp)]
      simp only [List.getLast?_singleton, Option.map_some]
      have : ¬ (K - 1 + 1 < K) := by omega
      simp [this]

theorem validScaleTree_chain {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) :
    IsNestedPartitionChain P (scaleTreePartitionChain T P M) := by
  have hP : 1 ≤ P := hValid.1
  have hlevel : ∀ n : ℕ,
      let parts := scaleTreePartitionLevel T P n
      parts ≠ [] ∧
      IsContiguousBlockPartition P parts ∧
      (∀ n' : ℕ, n = n' + 1 → ∀ Y ∈ parts,
        ∃ X ∈ scaleTreePartitionLevel T P n', X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi) := by
    intro n
    induction n with
    | zero =>
      dsimp only [scaleTreePartitionLevel]
      have hP0 : ¬ P = 0 := by omega
      simp only [hP0, ↓reduceIte]
      refine ⟨List.cons_ne_nil _ _, ?_, fun _ h => by omega⟩
      refine ⟨?_, trivial, by simp⟩
      intro C hC; simp at hC; subst hC; exact ⟨le_rfl, hP, le_rfl⟩
    | succ n ihn =>
      rcases ihn with ⟨hne, ⟨hbounds, hconsec, hhl⟩, _⟩
      set prev := scaleTreePartitionLevel T P n
      set S := scaleS T P (n + 1)
      change prev.flatMap (fun X => splitIntervalBySize X S) ≠ [] ∧ _
      have prev_head_tail : ∃ first last, prev.head? = some first ∧ prev.getLast? = some last ∧
          first.lo = 1 ∧ last.hi = P := by
        cases hh : prev.head? with
        | none => exact absurd (List.head?_eq_none_iff.mp hh) hne
        | some first =>
          cases hl : prev.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
          | some last =>
            rw [hh, hl] at hhl
            exact ⟨first, last, rfl, rfl, hhl.1, hhl.2⟩
      obtain ⟨firstP, lastP, hheadP, hlastP, hflo, hlhi⟩ := prev_head_tail
      have flat_props : ∀ (xs : List IntervalBlock),
          xs ≠ [] →
          (∀ X ∈ xs, 1 ≤ X.lo ∧ X.lo ≤ X.hi ∧ X.hi ≤ P) →
          ConsecutiveBlocks xs →
          let out := xs.flatMap (fun X => splitIntervalBySize X S)
          out ≠ [] ∧
          (∀ Y ∈ out, 1 ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ P) ∧
          ConsecutiveBlocks out ∧
          out.head?.map IntervalBlock.lo = xs.head?.map IntervalBlock.lo ∧
          out.getLast?.map IntervalBlock.hi = xs.getLast?.map IntervalBlock.hi := by
        intro xs
        induction xs with
        | nil => intro h; contradiction
        | cons X rest ihx =>
          intro _ hbx hcx
          obtain ⟨hX1, hXle, hXP⟩ := hbx X List.mem_cons_self
          obtain ⟨s_ne, s_b, s_c, s_hd, s_lt⟩ := splitIntervalBySize_props X S hXle
          cases rest with
          | nil =>
            simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
              List.head?_cons, List.getLast?_singleton, Option.map_some]
            refine ⟨s_ne, ?_, s_c, s_hd, s_lt⟩
            intro Y hY
            obtain ⟨h1, h2, h3⟩ := s_b Y hY
            exact ⟨by omega, h2, by omega⟩
          | cons X₂ rest' =>
            rcases hcx with ⟨hXX₂, hcrest⟩
            obtain ⟨r_ne, r_b, r_c, r_hd, r_lt⟩ := ihx (List.cons_ne_nil _ _)
              (fun B hB => hbx B (List.mem_cons_of_mem _ hB)) hcrest
            rw [List.flatMap_cons]
            refine ⟨List.append_ne_nil_of_left_ne_nil s_ne _, ?_, ?_, ?_, ?_⟩
            · intro Y hY
              rw [List.mem_append] at hY
              rcases hY with hY1 | hY2
              · obtain ⟨h1, h2, h3⟩ := s_b Y hY1
                exact ⟨by omega, h2, by omega⟩
              · exact r_b Y hY2
            · apply consecutiveBlocks_append s_c r_c
              intro last first hl hf
              have hl' : last.hi = X.hi := by rw [hl] at s_lt; simpa using s_lt
              have hf' : first.lo = X₂.lo := by rw [hf] at r_hd; simpa using r_hd
              omega
            · rw [List.head?_append_of_ne_nil _ s_ne]; simpa using s_hd
            · rw [List.getLast?_append_of_ne_nil _ r_ne]; simpa using r_lt
      obtain ⟨out_ne, out_b, out_c, out_hd, out_lt⟩ := flat_props prev hne hbounds hconsec
      refine ⟨out_ne, ⟨out_b, out_c, ?_⟩, ?_⟩
      · change match (prev.flatMap (fun X => splitIntervalBySize X S)).head?,
            (prev.flatMap (fun X => splitIntervalBySize X S)).getLast? with
          | some first, some last => first.lo = 1 ∧ last.hi = P
          | _, _ => _
        cases hh : (prev.flatMap (fun X => splitIntervalBySize X S)).head? with
        | none => exact absurd (List.head?_eq_none_iff.mp hh) out_ne
        | some fOut =>
          cases hl : (prev.flatMap (fun X => splitIntervalBySize X S)).getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.mp hl) out_ne
          | some lOut =>
            dsimp only
            have e1 : some fOut.lo = some 1 := by simpa [hh, hheadP, hflo] using out_hd
            have e2 : some lOut.hi = some P := by simpa [hl, hlastP, hlhi] using out_lt
            injection e1 with hf1
            injection e2 with hl1
            exact ⟨hf1, hl1⟩
      · intro n' hn' Y hY
        have hn_eq : n' = n := by omega
        subst n'
        change Y ∈ prev.flatMap (fun X => splitIntervalBySize X S) at hY
        rw [List.mem_flatMap] at hY
        obtain ⟨X, hX, hYX⟩ := hY
        obtain ⟨_, hXle, _⟩ := hbounds X hX
        obtain ⟨_, s_b, _, _, _⟩ := splitIntervalBySize_props X S hXle
        obtain ⟨h1, _, h3⟩ := s_b Y hYX
        exact ⟨X, hX, h1, h3⟩
  refine ⟨hP, ?_, ?_, ?_⟩
  · change scaleTreePartitionLevel T P 0 = [⟨1, P⟩]
    unfold scaleTreePartitionLevel
    have : ¬ P = 0 := by omega
    simp [this]
  · intro ℓ; exact (hlevel ℓ.val).2.1
  · intro ℓ Y hY; exact (hlevel (ℓ.val + 1)).2.2 ℓ.val rfl Y hY

theorem blockAt_mem_and_unique {N : ℕ} {parts : List IntervalBlock}
    (_hN : 1 ≤ N) (hPart : IsContiguousBlockPartition N parts) :
    (∀ u ∈ Finset.Icc 1 N, blockAt parts u ∈ parts ∧
      (blockAt parts u).lo ≤ u ∧ u ≤ (blockAt parts u).hi) ∧
    (∀ B ∈ parts, ∀ u, B.lo ≤ u → u ≤ B.hi → blockAt parts u = B) := by
  have hpw := consecutiveBlocks_pairwise (fun C hC => (hPart.1 C hC).2.1) hPart.2.1
  have huniq : ∀ B₁ ∈ parts, ∀ B₂ ∈ parts, ∀ u,
      B₁.lo ≤ u → u ≤ B₁.hi → B₂.lo ≤ u → u ≤ B₂.hi → B₁ = B₂ := by
    have aux : ∀ (xs : List IntervalBlock), xs.Pairwise (fun A B => A.hi < B.lo) →
        ∀ B₁ ∈ xs, ∀ B₂ ∈ xs, ∀ u, B₁.lo ≤ u → u ≤ B₁.hi → B₂.lo ≤ u → u ≤ B₂.hi → B₁ = B₂ := by
      intro xs hpw_xs
      induction xs with
      | nil => intro _ h; cases h
      | cons head tail iht =>
        rw [List.pairwise_cons] at hpw_xs
        intro B₁ h1 B₂ h2 u l1 r1 l2 r2
        rcases List.mem_cons.mp h1 with rfl | h1t <;>
          rcases List.mem_cons.mp h2 with rfl | h2t
        · rfl
        · have := hpw_xs.1 B₂ h2t; omega
        · have := hpw_xs.1 B₁ h1t; omega
        · exact iht hpw_xs.2 B₁ h1t B₂ h2t u l1 r1 l2 r2
    exact aux parts hpw
  have hfind_of_mem : ∀ B ∈ parts, ∀ u, B.lo ≤ u → u ≤ B.hi → blockAt parts u = B := by
    intro B hB u hlo hhi
    unfold blockAt
    cases hf : parts.find? (fun C => decide (C.lo ≤ u ∧ u ≤ C.hi)) with
    | none =>
      exfalso
      have := List.find?_eq_none.mp hf B hB
      simp [hlo, hhi] at this
    | some C =>
      simp only [Option.getD_some]
      have hC_mem := List.mem_of_find?_eq_some hf
      have hC_pred := List.find?_some hf
      simp only [decide_eq_true_eq] at hC_pred
      exact huniq C hC_mem B hB u hC_pred.1 hC_pred.2 hlo hhi
  refine ⟨?_, hfind_of_mem⟩
  intro u hu
  rw [Finset.mem_Icc] at hu
  have hne : parts ≠ [] := by
    intro he; subst he
    have := hPart.2.2
    simp at this; omega
  cases hh : parts.head? with
  | none => exact absurd (List.head?_eq_none_iff.mp hh) hne
  | some first =>
    cases hl : parts.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hne
    | some last =>
      have hhl := hPart.2.2
      rw [hh, hl] at hhl
      obtain ⟨B, hB, hlo, hhi⟩ := consecutiveBlocks_cover hne
        (fun C hC => (hPart.1 C hC).2.1) hPart.2.1
        (by simp [hh, hhl.1]) (by simp [hl, hhl.2]) hu.1 hu.2
      rw [hfind_of_mem B hB u hlo hhi]
      exact ⟨hB, hlo, hhi⟩

theorem childSubblocks_eq_split {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc) :
    childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X =
      splitIntervalBySize X (scaleS T P (ℓ.val + 1)) := by
  have hChain := validScaleTree_chain hValid
  have hPart := hChain.2.2.1 ℓ.castSucc
  have hpw := consecutiveBlocks_pairwise (fun C hC => (hPart.1 C hC).2.1) hPart.2.1
  set S := scaleS T P (ℓ.val + 1)
  unfold childSubblocks
  suffices ∀ (xs : List IntervalBlock),
      xs.Pairwise (fun B₁ B₂ => B₁.hi < B₂.lo) →
      (∀ X' ∈ xs, 1 ≤ X'.lo ∧ X'.lo ≤ X'.hi ∧ X'.hi ≤ P) →
      X ∈ xs →
      (xs.flatMap (fun X' => splitIntervalBySize X' S)).filter
        (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = splitIntervalBySize X S from
    this (scaleTreePartitionLevel T P ℓ.val) hpw hPart.1 hX
  clear hpw hPart hChain hX
  intro xs hpw hbounds hX
  induction xs with
  | nil => cases hX
  | cons X₁ rest ih =>
    rw [List.pairwise_cons] at hpw
    simp only [List.flatMap_cons, List.filter_append]
    rcases List.mem_cons.mp hX with rfl | hX_rest
    · obtain ⟨_, s_b, _, _, _⟩ := splitIntervalBySize_props X S (hbounds X List.mem_cons_self).2.1
      have hleft : (splitIntervalBySize X S).filter
          (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = splitIntervalBySize X S := by
        rw [List.filter_eq_self]
        intro Y hY
        obtain ⟨h1, _, h3⟩ := s_b Y hY
        simp [h1, h3]
      have hright : (rest.flatMap (fun X' => splitIntervalBySize X' S)).filter
          (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro Y hY
        rw [List.mem_flatMap] at hY
        obtain ⟨X', hX', hYX'⟩ := hY
        obtain ⟨_, s_b', _, _, _⟩ := splitIntervalBySize_props X' S
          (hbounds X' (List.mem_cons_of_mem _ hX')).2.1
        obtain ⟨h1, h2, _⟩ := s_b' Y hYX'
        have hlt := hpw.1 X' hX'
        have hXle := (hbounds X List.mem_cons_self).2.1
        simp; omega
      rw [hleft, hright, List.append_nil]
    · obtain ⟨_, s_b, _, _, _⟩ := splitIntervalBySize_props X₁ S (hbounds X₁ List.mem_cons_self).2.1
      have hleft : (splitIntervalBySize X₁ S).filter
          (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro Y hY
        obtain ⟨_, h2, h3⟩ := s_b Y hY
        have hlt := hpw.1 X hX_rest
        simp; omega
      rw [hleft, List.nil_append]
      exact ih hpw.2 (fun B hB => hbounds B (List.mem_cons_of_mem _ hB)) hX_rest

theorem validScaleTree_K_X_ge_two {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc) :
    2 ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length := by
  rcases hValid with ⟨hP, _, hHalf⟩
  have hLevel : ∀ k : ℕ, k ≤ M →
      ∀ Y ∈ scaleTreePartitionLevel T P k, 1 ≤ Y.lo ∧ scaleS T P k ≤ Y.size := by
    intro k
    induction k with
    | zero =>
      intro _ Y hY
      have hPne : P ≠ 0 := by omega
      simp only [scaleTreePartitionLevel, hPne, ↓reduceIte, List.mem_singleton] at hY
      subst hY
      refine ⟨le_rfl, ?_⟩
      change P ≤ (if 1 ≤ P then P - 1 + 1 else 0)
      split_ifs; omega
    | succ k ih =>
      intro hkM Y hY
      simp only [scaleTreePartitionLevel, List.mem_flatMap] at hY
      obtain ⟨parent, hparent, hchild⟩ := hY
      obtain ⟨hplo, hpsz⟩ := ih (by omega) parent hparent
      have hSpos : 1 ≤ scaleS T P (k + 1) := scaleS_pos T P hP (k + 1)
      have h2S : 2 * scaleS T P (k + 1) ≤ parent.size := le_trans (hHalf ⟨k, hkM⟩) hpsz
      obtain ⟨_, hbnds⟩ := splitIntervalBySize_sizes parent (scaleS T P (k + 1)) hplo hSpos h2S
      obtain ⟨h1, _, _, h4, _⟩ := hbnds Y hchild
      exact ⟨le_trans hplo h1, h4⟩
  rw [childSubblocks_eq_split ⟨hP, ‹_›, hHalf⟩ ℓ X hX]
  obtain ⟨hXlo, hXsz⟩ := hLevel ℓ.val (le_of_lt ℓ.isLt) X hX
  have hSpos : 1 ≤ scaleS T P (ℓ.val + 1) := scaleS_pos T P hP (ℓ.val + 1)
  have h2S : 2 * scaleS T P (ℓ.val + 1) ≤ X.size := le_trans (hHalf ℓ) hXsz
  exact (splitIntervalBySize_sizes X (scaleS T P (ℓ.val + 1)) hXlo hSpos h2S).1

theorem findIdx?_eq_some_spec {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {idx : ℕ}, xs.findIdx? p = some idx →
      ∃ hlt : idx < xs.length, p (xs[idx]'hlt) = true
  | [], _, h => by simp at h
  | x :: xs, idx, h => by
    simp only [List.findIdx?_cons] at h
    cases hpx : p x
    · simp only [hpx, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      obtain ⟨hk_lt, hpk⟩ := findIdx?_eq_some_spec p hk
      exact ⟨Nat.succ_lt_succ hk_lt, by simpa using hpk⟩
    · simp only [hpx, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨Nat.zero_lt_succ _, hpx⟩

theorem subblock1_props {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    1 ≤ X.lo ∧ X.lo ≤ X.hi ∧ X.hi ≤ P ∧
    subs ≠ [] ∧
    (∀ c ∈ Finset.Icc 1 subs.length,
      let Sc := subblock1 subs c
      Sc ∈ subs ∧ Sc ∈ chain ℓ.succ ∧
      X.lo ≤ Sc.lo ∧ Sc.lo ≤ Sc.hi ∧ Sc.hi ≤ X.hi ∧
      (∀ w ∈ Sc.toFinset, subblockIndex1 subs w = c ∧
        blockAt (chain ℓ.succ) w = Sc ∧ blockAt (chain ℓ.castSucc) w = X)) ∧
    (∀ c₁ c₂ : ℕ, 1 ≤ c₁ → c₁ < c₂ → c₂ ≤ subs.length →
      (subblock1 subs c₁).hi < (subblock1 subs c₂).lo) ∧
    (∀ c : ℕ, 1 ≤ c → c + 1 ≤ subs.length →
      (subblock1 subs c).hi + 1 = (subblock1 subs (c + 1)).lo) ∧
    (subblock1 subs 1).lo = X.lo ∧
    (subblock1 subs subs.length).hi = X.hi ∧
    (∀ w ∈ Finset.Icc X.lo X.hi,
      subblockIndex1 subs w ∈ Finset.Icc 1 subs.length ∧
      w ∈ (subblock1 subs (subblockIndex1 subs w)).toFinset) := by
  dsimp only
  set chain := scaleTreePartitionChain T P M
  set subs := childSubblocks (chain ℓ.succ) X
  have hChain := validScaleTree_chain hValid
  have hP := hValid.1
  have hPartX := hChain.2.2.1 ℓ.castSucc
  have hPartY := hChain.2.2.1 ℓ.succ
  obtain ⟨hX1, hXle, hXP⟩ := hPartX.1 X hX
  have hsplit : subs = splitIntervalBySize X (scaleS T P (ℓ.val + 1)) :=
    childSubblocks_eq_split hValid ℓ X hX
  obtain ⟨s_ne, s_b, s_c, s_hd, s_lt⟩ :=
    splitIntervalBySize_props X (scaleS T P (ℓ.val + 1)) hXle
  rw [← hsplit] at s_ne s_b s_c s_hd s_lt
  have hpw := consecutiveBlocks_pairwise (fun Y hY => (s_b Y hY).2.1) s_c
  have hsub_mem_chain : ∀ Y ∈ subs, Y ∈ chain ℓ.succ := fun Y hY =>
    (List.mem_filter.mp hY).1
  have hsub1_eq : ∀ c (_ : 1 ≤ c) (hclen : c ≤ subs.length),
      subblock1 subs c = subs[c - 1]'(by omega) := by
    intro c hc1 hclen
    unfold subblock1
    have hc0 : ¬ c = 0 := by omega
    simp [hc0, List.getElem?_eq_getElem (show c - 1 < subs.length by omega)]
  have hlt_idx : ∀ c₁ c₂ : ℕ, 1 ≤ c₁ → c₁ < c₂ → c₂ ≤ subs.length →
      (subblock1 subs c₁).hi < (subblock1 subs c₂).lo := by
    intro c₁ c₂ hc1 h12 hc2
    rw [hsub1_eq c₁ hc1 (by omega), hsub1_eq c₂ (by omega) hc2]
    exact List.pairwise_iff_getElem.mp hpw (c₁ - 1) (c₂ - 1) (by omega) (by omega) (by omega)
  have hconsec_idx : ∀ c : ℕ, 1 ≤ c → c + 1 ≤ subs.length →
      (subblock1 subs c).hi + 1 = (subblock1 subs (c + 1)).lo := by
    intro c hc1 hc2
    rw [hsub1_eq c hc1 (by omega), hsub1_eq (c + 1) (by omega) hc2]
    have hstep := (consecutiveBlocks_iff_getElem subs).mp s_c (c - 1) (by omega)
    have hidx : c - 1 + 1 = c + 1 - 1 := by omega
    simpa [hidx] using hstep
  have hfindIdx_of_mem : ∀ c, 1 ≤ c → c ≤ subs.length → ∀ w,
      (subblock1 subs c).lo ≤ w → w ≤ (subblock1 subs c).hi →
      subblockIndex1 subs w = c := by
    intro c hc1 hclen w hlo hhi
    unfold subblockIndex1
    have hex : ∃ Y ∈ subs, decide (Y.lo ≤ w ∧ w ≤ Y.hi) = true := by
      refine ⟨subblock1 subs c, ?_, by simp [hlo, hhi]⟩
      rw [hsub1_eq c hc1 hclen]; exact List.getElem_mem _
    cases hf : subs.findIdx? (fun S => decide (S.lo ≤ w ∧ w ≤ S.hi)) with
    | none =>
      exfalso
      rcases hex with ⟨Y, hY, hpY⟩
      have := (List.findIdx?_eq_none_iff.mp hf) Y hY
      simp [hpY] at this
    | some idx =>
      dsimp only
      obtain ⟨hidx_lt, hp_idx⟩ := findIdx?_eq_some_spec _ hf
      simp only [decide_eq_true_eq] at hp_idx
      have hidx1 : 1 ≤ idx + 1 := by omega
      have hidx_len : idx + 1 ≤ subs.length := by omega
      have hsub_idx : subblock1 subs (idx + 1) = subs[idx] := by
        simpa using hsub1_eq (idx + 1) hidx1 hidx_len
      rw [← hsub_idx] at hp_idx
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hlt_idx (idx + 1) c hidx1 hlt hclen; omega
      · have := hlt_idx c (idx + 1) hc1 hgt hidx_len; omega
  refine ⟨hX1, hXle, hXP, s_ne, ?_, hlt_idx, hconsec_idx, ?_, ?_, ?_⟩
  · intro c hc
    rw [Finset.mem_Icc] at hc
    have hSc_mem : subblock1 subs c ∈ subs := by
      rw [hsub1_eq c hc.1 hc.2]; exact List.getElem_mem _
    obtain ⟨h1, h2, h3⟩ := s_b _ hSc_mem
    refine ⟨hSc_mem, hsub_mem_chain _ hSc_mem, h1, h2, h3, ?_⟩
    intro w hw
    rw [IntervalBlock.toFinset, Finset.mem_Icc] at hw
    refine ⟨hfindIdx_of_mem c hc.1 hc.2 w hw.1 hw.2, ?_, ?_⟩
    · exact (blockAt_mem_and_unique hP hPartY).2 _ (hsub_mem_chain _ hSc_mem) w hw.1 hw.2
    · exact (blockAt_mem_and_unique hP hPartX).2 X hX w (by omega) (by omega)
  · have hlen_pos : 1 ≤ subs.length := List.length_pos_of_ne_nil s_ne
    rw [hsub1_eq 1 le_rfl hlen_pos]
    have hget0 : subs.head? = some (subs[0]'(by omega)) := by
      rw [List.head?_eq_getElem?]; exact List.getElem?_eq_getElem (by omega)
    rw [hget0] at s_hd
    simpa using s_hd
  · have hlen_pos : 1 ≤ subs.length := List.length_pos_of_ne_nil s_ne
    rw [hsub1_eq subs.length hlen_pos le_rfl]
    have hgetLast : subs.getLast? = some (subs[subs.length - 1]'(by omega)) := by
      rw [List.getLast?_eq_getElem?]; exact List.getElem?_eq_getElem (by omega)
    rw [hgetLast] at s_lt
    simpa using s_lt
  · intro w hw
    rw [Finset.mem_Icc] at hw
    obtain ⟨B, hB, hlo, hhi⟩ := consecutiveBlocks_cover s_ne
      (fun Y hY => (s_b Y hY).2.1) s_c s_hd s_lt hw.1 hw.2
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hB
    have hc1 : 1 ≤ idx + 1 := by omega
    have hclen : idx + 1 ≤ subs.length := by omega
    have hsub_eq : subblock1 subs (idx + 1) = subs[idx] := by
      simpa using hsub1_eq (idx + 1) hc1 hclen
    rw [← hsub_eq] at hlo hhi
    have hidx_eq := hfindIdx_of_mem (idx + 1) hc1 hclen w hlo hhi
    rw [hidx_eq]
    exact ⟨Finset.mem_Icc.mpr ⟨hc1, hclen⟩, Finset.mem_Icc.mpr ⟨hlo, hhi⟩⟩

theorem chain_blockAt_coarse {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hk : k₁ ≤ k₂) {u : ℕ} (hu : u ∈ Finset.Icc 1 P) :
    (blockAt (chain k₁) u).lo ≤ (blockAt (chain k₂) u).lo ∧
    (blockAt (chain k₂) u).hi ≤ (blockAt (chain k₁) u).hi := by
  rcases hChain with ⟨hP, _, hPart, hNest⟩
  obtain ⟨d, hd⟩ : ∃ d, k₂.val = k₁.val + d := ⟨k₂.val - k₁.val, by omega⟩
  induction d generalizing k₂ with
  | zero =>
    have hk_eq : k₁ = k₂ := Fin.ext (by omega)
    subst hk_eq; exact ⟨le_rfl, le_rfl⟩
  | succ d ih =>
    have hk_lt : k₁.val + d < M := by omega
    let km : Fin M := ⟨k₁.val + d, hk_lt⟩
    have hk₂_eq : k₂ = km.succ := Fin.ext (by simp [km]; omega)
    subst hk₂_eq
    obtain ⟨hB_mem, hB_lo, hB_hi⟩ := (blockAt_mem_and_unique hP (hPart km.succ)).1 u hu
    obtain ⟨X, hX_mem, hX_lo, hX_hi⟩ := hNest km _ hB_mem
    have hX_eq : blockAt (chain km.castSucc) u = X :=
      (blockAt_mem_and_unique hP (hPart km.castSucc)).2 X hX_mem u
        (le_trans hX_lo hB_lo) (le_trans hB_hi hX_hi)
    obtain ⟨ih1, ih2⟩ := ih (k₂ := km.castSucc) (Fin.mk_le_mk.mpr (by simp [km])) rfl
    rw [hX_eq] at ih1 ih2
    exact ⟨le_trans ih1 hX_lo, le_trans hX_hi ih2⟩

theorem partSepScale_eq_iff {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) {u v : ℕ}
    (hu : u ∈ Finset.Icc 1 P) (hv : v ∈ Finset.Icc 1 P) (ℓ : Fin M) :
    partSepScale P chain u v = ℓ.val + 1 ↔
      blockAt (chain ℓ.castSucc) u = blockAt (chain ℓ.castSucc) v ∧
      blockAt (chain ℓ.succ) u ≠ blockAt (chain ℓ.succ) v := by
  have hP := hChain.1
  have hu' := Finset.mem_Icc.mp hu
  have hv' := Finset.mem_Icc.mp hv
  have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
  have same_down : ∀ {k₁ k₂ : Fin (M + 1)}, k₁ ≤ k₂ →
      blockAt (chain k₂) u = blockAt (chain k₂) v →
      blockAt (chain k₁) u = blockAt (chain k₁) v := by
    intro k₁ k₂ hk hsame
    obtain ⟨l2, r2⟩ := chain_blockAt_coarse hChain hk hv
    obtain ⟨_, hu_lo, hu_hi⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 k₂)).1 u hu
    rw [hsame] at hu_lo hu_hi
    obtain ⟨hB1_mem, _, _⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 k₁)).1 v hv
    exact (blockAt_mem_and_unique hP (hChain.2.2.1 k₁)).2 _ hB1_mem u
      (le_trans l2 hu_lo) (le_trans hu_hi r2)
  have h0_same : blockAt (chain 0) u = blockAt (chain 0) v := by
    have h0 := hChain.2.1
    have hPart0 := hChain.2.2.1 0
    have hmem0 : ⟨1, P⟩ ∈ chain 0 := by rw [h0]; simp
    rw [(blockAt_mem_and_unique hP hPart0).2 ⟨1, P⟩ hmem0 u hu'.1 hu'.2,
        (blockAt_mem_and_unique hP hPart0).2 ⟨1, P⟩ hmem0 v hv'.1 hv'.2]
  have find_finRange : ∀ (p : Fin M → Bool),
      ((List.finRange M).find? p = none ↔ ∀ i : Fin M, p i = false) ∧
      (∀ i : Fin M, (List.finRange M).find? p = some i ↔
        p i = true ∧ ∀ j : Fin M, j < i → p j = false) := by
    intro p
    have aux : ∀ (xs : List (Fin M)), xs.Pairwise (· < ·) →
        (∀ i : Fin M, xs.find? p = some i →
          p i = true ∧ ∀ j ∈ xs, j < i → p j = false) := by
      intro xs
      induction xs with
      | nil => intro _ i h; simp at h
      | cons head tail iht =>
        intro hpw_xs i hf
        rw [List.pairwise_cons] at hpw_xs
        simp only [List.find?_cons] at hf
        cases hp : p head
        · simp [hp] at hf
          obtain ⟨hpi, hprev⟩ := iht hpw_xs.2 i hf
          refine ⟨hpi, fun j hj hjlt => ?_⟩
          rcases List.mem_cons.mp hj with rfl | hjt
          · exact hp
          · exact hprev j hjt hjlt
        · simp [hp] at hf; subst hf
          refine ⟨hp, fun j hj hjlt => ?_⟩
          rcases List.mem_cons.mp hj with rfl | hjt
          · exact absurd hjlt (lt_irrefl _)
          · exact absurd (lt_trans hjlt (hpw_xs.1 j hjt)) (lt_irrefl _)
    refine ⟨List.find?_eq_none.trans (by simp [List.mem_finRange]), fun i => ⟨fun hf => ?_, ?_⟩⟩
    · obtain ⟨hpi, hprev⟩ := aux (List.finRange M) (List.pairwise_lt_finRange M) i hf
      exact ⟨hpi, fun j hj => hprev j (List.mem_finRange j) hj⟩
    · rintro ⟨hp_i, hlt_i⟩
      cases hf : (List.finRange M).find? p with
      | none =>
        have := List.find?_eq_none.mp hf i (List.mem_finRange i)
        simp [hp_i] at this
      | some i' =>
        obtain ⟨hp_i', hprev'⟩ := aux (List.finRange M) (List.pairwise_lt_finRange M) i' hf
        rcases lt_trichotomy i' i with h1 | rfl | h2
        · rw [hlt_i i' h1] at hp_i'; contradiction
        · rfl
        · rw [hprev' i (List.mem_finRange i) h2] at hp_i; contradiction
  set pred : Fin M → Bool := fun j => decide (blockAt (chain j.succ) u ≠ blockAt (chain j.succ) v)
  have hsep_none : (List.finRange M).find? pred = none → partSepScale P chain u v = M + 1 := by
    intro hf
    unfold partSepScale
    simp only [hcond, ↓reduceIte]
    change (match (List.finRange M).find? pred with | some j => j.val + 1 | none => M + 1) = M + 1
    rw [hf]
  have hsep_some : ∀ j, (List.finRange M).find? pred = some j →
      partSepScale P chain u v = j.val + 1 := by
    intro j hf
    unfold partSepScale
    simp only [hcond, ↓reduceIte]
    change (match (List.finRange M).find? pred with | some j => j.val + 1 | none => M + 1) = j.val + 1
    rw [hf]
  obtain ⟨hnone, hsome⟩ := find_finRange pred
  cases hf : (List.finRange M).find? pred with
  | none =>
    rw [hsep_none hf]
    constructor
    · intro heq; have := ℓ.isLt; omega
    · rintro ⟨_, h_fine⟩
      have hall := hnone.mp hf ℓ
      simp only [pred, decide_eq_false_iff_not, not_not] at hall
      exact absurd hall h_fine
  | some ℓ' =>
    rw [hsep_some ℓ' hf]
    constructor
    · intro heq
      have hℓ_eq : ℓ' = ℓ := Fin.ext (by omega)
      subst ℓ'
      obtain ⟨hp_ℓ, hprev⟩ := (hsome ℓ).mp hf
      simp only [pred, decide_eq_true_eq] at hp_ℓ
      refine ⟨?_, hp_ℓ⟩
      rcases Nat.eq_zero_or_pos ℓ.val with hℓ0 | hℓ_pos
      · have hc0 : ℓ.castSucc = 0 := Fin.ext (by simp [hℓ0])
        rw [hc0]; exact h0_same
      · let j : Fin M := ⟨ℓ.val - 1, by omega⟩
        have hj_lt : j < ℓ := Fin.mk_lt_mk.mpr (by omega)
        have hp_j := hprev j hj_lt
        simp only [pred, decide_eq_false_iff_not, not_not] at hp_j
        have hcast_eq : ℓ.castSucc = j.succ := Fin.ext (by change ℓ.val = (ℓ.val - 1) + 1; omega)
        rw [hcast_eq]; exact hp_j
    · rintro ⟨h_coarse, h_fine⟩
      have h_iff : (List.finRange M).find? pred = some ℓ := by
        rw [hsome ℓ]
        refine ⟨by simp [pred, h_fine], fun j hj => ?_⟩
        simp only [pred, decide_eq_false_iff_not, not_not]
        exact same_down (Fin.succ_le_castSucc_iff.mpr hj) h_coarse
      rw [hf] at h_iff
      injection h_iff with h_eq
      rw [h_eq]

theorem validFoldedOps_take_step {P : ℕ} {st : BinaryTree ℕ × Option ℕ}
    {steps : List FoldedOp} (hV : ValidFoldedOps P st steps) {τ : ℕ} (hτ : τ < steps.length) :
    (steps[τ]).Valid P ((steps.take τ).foldl FoldedOp.step st) ∧
    (steps.take (τ + 1)).foldl FoldedOp.step st =
      (steps[τ]).step ((steps.take τ).foldl FoldedOp.step st) := by
  induction steps generalizing st τ with
  | nil => simp at hτ
  | cons op rest ih =>
    rcases hV with ⟨hop, hrest⟩
    cases τ with
    | zero => simp [hop]
    | succ τ' =>
      simp only [List.take_succ_cons, List.foldl_cons, List.getElem_cons_succ]
      exact ih hrest (Nat.lt_of_succ_lt_succ hτ)

theorem proc_step_at {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ < proc.steps.length) :
    (proc.steps[τ]).Valid P (proc.stateAt τ) ∧
    proc.stateAt (τ + 1) = (proc.steps[τ]).step (proc.stateAt τ) :=
  validFoldedOps_take_step proc.hValid hτ

theorem proc_stateAt_end {P : ℕ} (proc : FoldedPopProcess P) :
    proc.stateAt proc.steps.length = (.nil, none) := by
  unfold FoldedPopProcess.stateAt
  rw [List.take_length]
  exact proc.hEndEmpty

theorem head?_leftSpine_eq_minKey? {t : BinaryTree ℕ} (ht : t.IsBST) :
    (leftSpine t).head? = t.minKey? := by
  induction t with
  | nil => simp [leftSpine, BinaryTree.minKey?]
  | node k l r ihl _ =>
    obtain ⟨hl, _, _, _⟩ := (isBST_node_iff k l r).mp ht
    cases l with
    | nil => simp [leftSpine, BinaryTree.minKey?]
    | node lk ll lr =>
      have hne : leftSpine (.node lk ll lr) ≠ [] := by simp [leftSpine]
      rw [leftSpine, List.head?_append_of_ne_nil _ hne, ihl hl,
          minKey?_node_of_ne_nil k _ r (by simp)]

theorem getElem?_of_getElem {α : Type} {xs : List α} {i : ℕ} (hi : i < xs.length)
    {v : α} (h : xs[i]'hi = v) : xs[i]? = some v := by
  rw [List.getElem?_eq_getElem hi, h]

theorem modifyLeftAt_push_bst_keys {t : BinaryTree ℕ} (ht : t.IsBST)
    {b w : ℕ} (hb : b ∈ leftSpine t) (hw : ∀ x ∈ t, w < x) :
    let t' := modifyLeftAt t b (fun L1 => .node w .nil L1)
    t'.IsBST ∧ keyFinset t' = insert w (keyFinset t) := by
  induction t with
  | nil => simp [leftSpine] at hb
  | node k l r ihl _ =>
    obtain ⟨hl, hr, hlt, hgt⟩ := (isBST_node_iff k l r).mp ht
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb_l | rfl
    · have hbk : b < k := hlt b (mem_of_mem_leftSpine hb_l)
      obtain ⟨hl'_bst, hl'_keys⟩ := ihl hl hb_l (fun x hx => hw x (.left hx))
      dsimp only
      simp only [modifyLeftAt, hbk, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [isBST_node_iff]
        refine ⟨hl'_bst, hr, fun x hx => ?_, hgt⟩
        have hx_kf := (mem_iff_mem_keyFinset _ x).mp hx
        rw [hl'_keys, Finset.mem_insert] at hx_kf
        rcases hx_kf with rfl | hxl
        · exact hw k .here
        · exact hlt x ((mem_iff_mem_keyFinset l x).mpr hxl)
      · ext x; simp [keyFinset, hl'_keys, or_left_comm]
    · dsimp only
      simp only [modifyLeftAt, lt_irrefl, ↓reduceIte]
      have hwl_bst : (BinaryTree.node w .nil l).IsBST := by
        rw [isBST_node_iff]
        exact ⟨by simp [BinaryTree.IsBST], hl, by simp, fun x hx => hw x (.left hx)⟩
      refine ⟨?_, ?_⟩
      · rw [isBST_node_iff]
        refine ⟨hwl_bst, hr, fun x hx => ?_, hgt⟩
        rcases BinaryTree.mem_node_iff.mp hx with rfl | h0 | hxl
        · exact hw b .here
        · cases h0
        · exact hlt x hxl
      · ext x; simp [keyFinset, or_left_comm]

theorem foldl_rotateRightEdge_bst_keys (pairs : List (ℕ × ℕ)) :
    ∀ (t : BinaryTree ℕ), t.IsBST →
      let t' := pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t
      t'.IsBST ∧ keyFinset t' = keyFinset t := by
  induction pairs with
  | nil => intro t ht; exact ⟨ht, rfl⟩
  | cons p rest ih =>
    intro t ht
    simp only [List.foldl_cons]
    obtain ⟨hbst, hkeys⟩ := ih (rotateRightEdge t p.1 p.2) (rotateRightEdge_isBST ht p.1 p.2)
    exact ⟨hbst, hkeys.trans (keyFinset_rotateRightEdge t p.1 p.2)⟩

theorem proc_tree_bst_and_step_keys {P : ℕ} (proc : FoldedPopProcess P) :
    (∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST ∧
      keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P) ∧
    (∀ τ (hτ : τ < proc.steps.length),
      match proc.steps[τ]'hτ with
      | .push w =>
        1 ≤ w ∧ w ≤ P ∧ w ∉ keyFinset (proc.treeAt τ) ∧
        keyFinset (proc.treeAt (τ + 1)) = insert w (keyFinset (proc.treeAt τ))
      | .shift =>
        proc.treeAt (τ + 1) = proc.treeAt τ
      | .upperRot u v =>
        proc.treeAt (τ + 1) = rotateRightEdge (proc.treeAt τ) u v ∧
        keyFinset (proc.treeAt (τ + 1)) = keyFinset (proc.treeAt τ)
      | .pop s =>
        s ∈ keyFinset (proc.treeAt τ) ∧ (proc.treeAt τ).minKey? = some s ∧
        keyFinset (proc.treeAt (τ + 1)) = (keyFinset (proc.treeAt τ)).erase s) := by
  have one_step : ∀ (τ : ℕ) (hτ : τ < proc.steps.length),
      (proc.treeAt τ).IsBST → keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P →
      ((proc.treeAt (τ + 1)).IsBST ∧ keyFinset (proc.treeAt (τ + 1)) ⊆ Finset.Icc 1 P) ∧
      match proc.steps[τ]'hτ with
      | .push w =>
        1 ≤ w ∧ w ≤ P ∧ w ∉ keyFinset (proc.treeAt τ) ∧
        keyFinset (proc.treeAt (τ + 1)) = insert w (keyFinset (proc.treeAt τ))
      | .shift =>
        proc.treeAt (τ + 1) = proc.treeAt τ
      | .upperRot u v =>
        proc.treeAt (τ + 1) = rotateRightEdge (proc.treeAt τ) u v ∧
        keyFinset (proc.treeAt (τ + 1)) = keyFinset (proc.treeAt τ)
      | .pop s =>
        s ∈ keyFinset (proc.treeAt τ) ∧ (proc.treeAt τ).minKey? = some s ∧
        keyFinset (proc.treeAt (τ + 1)) = (keyFinset (proc.treeAt τ)).erase s := by
    intro τ hτ ht_bst ht_sub
    obtain ⟨hval, hst⟩ := proc_step_at proc hτ
    have ht_eq : proc.treeAt (τ + 1) = ((proc.steps[τ]'hτ).step (proc.stateAt τ)).1 :=
      congrArg Prod.fst hst
    cases hop : proc.steps[τ]'hτ with
    | push w =>
      rw [hop] at hval ht_eq
      rcases hval with ⟨hw1, hwP, hlt_all, hnil_iff, hb_ls⟩
      have hnot_in : w ∉ keyFinset (proc.treeAt τ) := fun h =>
        lt_irrefl w (hlt_all w ((mem_iff_mem_keyFinset _ w).mpr h))
      cases hb : (proc.stateAt τ).2 with
      | none =>
        have htree_nil : proc.treeAt τ = .nil := hnil_iff.mpr hb
        simp only [FoldedOp.step, hb] at ht_eq
        have hk1 : keyFinset (proc.treeAt (τ + 1)) = insert w (keyFinset (proc.treeAt τ)) := by
          rw [ht_eq, htree_nil]; simp [keyFinset]
        have hbst1 : (proc.treeAt (τ + 1)).IsBST := by
          rw [ht_eq, isBST_node_iff]; simp [BinaryTree.IsBST]
        refine ⟨⟨hbst1, ?_⟩, hw1, hwP, hnot_in, hk1⟩
        rw [hk1]; exact Finset.insert_subset_iff.mpr ⟨Finset.mem_Icc.mpr ⟨hw1, hwP⟩, ht_sub⟩
      | some b =>
        simp only [FoldedOp.step, hb] at ht_eq
        change proc.treeAt (τ + 1) = modifyLeftAt (proc.treeAt τ) b (fun L1 => .node w .nil L1) at ht_eq
        obtain ⟨hbst1, hk1⟩ := modifyLeftAt_push_bst_keys ht_bst (hb_ls b hb) hlt_all
        rw [← ht_eq] at hbst1 hk1
        refine ⟨⟨hbst1, ?_⟩, hw1, hwP, hnot_in, hk1⟩
        rw [hk1]; exact Finset.insert_subset_iff.mpr ⟨Finset.mem_Icc.mpr ⟨hw1, hwP⟩, ht_sub⟩
    | shift =>
      rw [hop] at ht_eq
      have hsame : proc.treeAt (τ + 1) = proc.treeAt τ := by
        rw [ht_eq]; unfold FoldedOp.step; cases (proc.stateAt τ).2 <;> rfl
      exact ⟨⟨hsame ▸ ht_bst, hsame ▸ ht_sub⟩, hsame⟩
    | upperRot u v =>
      rw [hop] at ht_eq
      have hbst1 : (proc.treeAt (τ + 1)).IsBST := ht_eq ▸ rotateRightEdge_isBST ht_bst u v
      have hk1 : keyFinset (proc.treeAt (τ + 1)) = keyFinset (proc.treeAt τ) :=
        ht_eq ▸ keyFinset_rotateRightEdge (proc.treeAt τ) u v
      exact ⟨⟨hbst1, hk1 ▸ ht_sub⟩, ht_eq, hk1⟩
    | pop s =>
      rw [hop] at hval ht_eq
      rcases hval with ⟨b, _, hmin, hb, _⟩
      have hs_mem : s ∈ proc.treeAt τ := ((minKey?_mem_and_le ht_bst).mp hmin).1
      have hs_kf : s ∈ keyFinset (proc.treeAt τ) := (mem_iff_mem_keyFinset _ s).mp hs_mem
      obtain ⟨hsp_bst, hsp_keys⟩ := spliceMin_spec ht_bst hmin
      simp only [FoldedOp.step, hb] at ht_eq
      by_cases hm0 : (takeThrough (leftSpine (proc.stateAt τ).1) b).length - 1 = 0
      · simp only [hm0, ↓reduceIte] at ht_eq
        change proc.treeAt (τ + 1) = spliceMin (proc.treeAt τ) at ht_eq
        rw [ht_eq]
        exact ⟨⟨hsp_bst, hsp_keys ▸ (Finset.erase_subset _ _).trans ht_sub⟩, hs_kf, hmin, hsp_keys⟩
      · simp only [hm0, ↓reduceIte] at ht_eq
        have ht_eq' : proc.treeAt (τ + 1) =
            (((adjacentPairs (takeThrough (leftSpine (proc.treeAt τ)) b).tail).take
              (((takeThrough (leftSpine (proc.treeAt τ)) b).length - 1 - 1) / 2)).foldl
              (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin (proc.treeAt τ))) :=
          ht_eq
        obtain ⟨hf_bst, hf_keys⟩ := foldl_rotateRightEdge_bst_keys _ _ hsp_bst
        rw [ht_eq']
        have hkeys_final := hf_keys.trans hsp_keys
        exact ⟨⟨hf_bst, hkeys_final ▸ (Finset.erase_subset _ _).trans ht_sub⟩,
          hs_kf, hmin, hkeys_final⟩
  have hinv : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P := by
    intro τ
    induction τ with
    | zero =>
      intro _; exact ⟨by simp [FoldedPopProcess.treeAt, FoldedPopProcess.stateAt, BinaryTree.IsBST],
        by simp [FoldedPopProcess.treeAt, FoldedPopProcess.stateAt, keyFinset]⟩
    | succ τ ih =>
      intro hle
      have hlt : τ < proc.steps.length := Nat.lt_of_succ_le hle
      obtain ⟨h1, h2⟩ := ih (le_of_lt hlt)
      exact (one_step τ hlt h1 h2).1
  exact ⟨hinv, fun τ hτ => (one_step τ hτ (hinv τ (le_of_lt hτ)).1 (hinv τ (le_of_lt hτ)).2).2⟩

def s0At {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ) : ℕ :=
  ((proc.steps.take τ).filter (fun | .pop _ => true | _ => false)).length

def uSetAt {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ) : Finset ℕ :=
  Finset.Icc (s0At proc τ + 1) P \ keyFinset (proc.treeAt τ)

theorem popStepIdx_and_insStep_props {P : ℕ} (proc : FoldedPopProcess P) :
    let popKey? : FoldedOp → Option ℕ := fun | .pop s => some s | _ => none
    (∀ τ ≤ proc.steps.length,
      s0At proc τ ≤ P ∧
      (proc.steps.take τ).filterMap popKey? = List.range' 1 (s0At proc τ) ∧
      (proc.steps.drop τ).filterMap popKey? = List.range' (s0At proc τ + 1) (P - s0At proc τ)) ∧
    (∀ s ∈ Finset.Icc 1 P,
      proc.popStepIdx s < proc.steps.length ∧
      proc.steps[proc.popStepIdx s]? = some (.pop s) ∧
      (∀ τ < proc.steps.length, proc.steps[τ]? = some (.pop s) ↔ τ = proc.popStepIdx s)) ∧
    (∀ s₁ ∈ Finset.Icc 1 P, ∀ s₂ ∈ Finset.Icc 1 P,
      (s₁ < s₂ ↔ proc.popStepIdx s₁ < proc.popStepIdx s₂) ∧
      (s₁ ≤ s₂ ↔ proc.popStepIdx s₁ ≤ proc.popStepIdx s₂)) ∧
    (∀ τ ≤ proc.steps.length, ∀ u ∈ Finset.Icc 1 P,
      s0At proc τ + 1 ≤ u ↔ τ ≤ proc.popStepIdx u) ∧
    (∀ u ∈ Finset.Icc 1 P,
      proc.insStep u < proc.popStepIdx u ∧
      proc.steps[proc.insStep u]? = some (.push u) ∧
      (∀ τ < proc.steps.length, proc.steps[τ]? = some (.push u) ↔ τ = proc.insStep u) ∧
      (∀ τ ≤ proc.steps.length,
        u ∈ keyFinset (proc.treeAt τ) ↔ proc.insStep u < τ ∧ τ ≤ proc.popStepIdx u)) := by
  dsimp only
  set popKey? : FoldedOp → Option ℕ := fun | .pop s => some s | _ => none
  set isPop : FoldedOp → Bool := fun | .pop _ => true | _ => false
  have len_fmap : ∀ (xs : List FoldedOp),
      (xs.filterMap popKey?).length = (xs.filter isPop).length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons op rest ih => cases op <;> simp [popKey?, isPop, ih]
  have split_prop : ∀ τ ≤ proc.steps.length,
      s0At proc τ ≤ P ∧
      (proc.steps.take τ).filterMap popKey? = List.range' 1 (s0At proc τ) ∧
      (proc.steps.drop τ).filterMap popKey? = List.range' (s0At proc τ + 1) (P - s0At proc τ) := by
    intro τ _
    set s₀ := s0At proc τ
    have happ : (proc.steps.take τ).filterMap popKey? ++ (proc.steps.drop τ).filterMap popKey? =
        List.range' 1 P := by
      rw [← List.filterMap_append, List.take_append_drop]
      exact proc.hPopSeq
    have hlen1 : ((proc.steps.take τ).filterMap popKey?).length = s₀ := len_fmap _
    have hs₀_le : s₀ ≤ P := by
      have := congrArg List.length happ
      rw [List.length_append, hlen1, List.length_range'] at this
      omega
    have hrange_split : List.range' 1 P = List.range' 1 s₀ ++ List.range' (1 + s₀) (P - s₀) := by
      have h := (List.range'_append (s := 1) (m := s₀) (n := P - s₀) (step := 1)).symm
      rw [one_mul, show s₀ + (P - s₀) = P by omega] at h
      exact h
    rw [hrange_split] at happ
    have heq_pair := List.append_inj happ (hlen1.trans List.length_range'.symm)
    refine ⟨hs₀_le, heq_pair.1, ?_⟩
    simpa [Nat.add_comm] using heq_pair.2
  have pop_in_list_iff : ∀ (xs : List FoldedOp) (s : ℕ),
       .pop s ∈ xs ↔ s ∈ xs.filterMap popKey? := by
    intro xs s
    rw [List.mem_filterMap]
    constructor
    · intro h; exact ⟨.pop s, h, rfl⟩
    · rintro ⟨op, hop, h⟩; cases op <;> simp [popKey?] at h; subst h; exact hop
  have findIdx_unique : ∀ (op₀ : FoldedOp),
      (∃ τ₀ < proc.steps.length, proc.steps[τ₀]? = some op₀ ∧
        ∀ τ < proc.steps.length, proc.steps[τ]? = some op₀ → τ = τ₀) →
      let idx := proc.steps.findIdx (fun op => op == op₀)
      idx < proc.steps.length ∧ proc.steps[idx]? = some op₀ ∧
      (∀ τ < proc.steps.length, proc.steps[τ]? = some op₀ ↔ τ = idx) := by
    rintro op₀ ⟨τ₀, hτ₀_lt, hτ₀_eq, huniq⟩
    dsimp only
    set idx := proc.steps.findIdx (fun op => op == op₀)
    have hmem : op₀ ∈ proc.steps := List.mem_of_getElem? hτ₀_eq
    have hex_b : ∃ op ∈ proc.steps, (op == op₀) = true := ⟨op₀, hmem, by simp⟩
    have hidx_lt : idx < proc.steps.length := List.findIdx_lt_length_of_exists hex_b
    have hidx_true : (proc.steps[idx]'hidx_lt == op₀) = true := List.findIdx_getElem (w := hidx_lt)
    simp only [beq_iff_eq] at hidx_true
    have hidx_some : proc.steps[idx]? = some op₀ := by
      rw [List.getElem?_eq_getElem hidx_lt, hidx_true]
    have hidx_eq_τ₀ : idx = τ₀ := huniq idx hidx_lt hidx_some
    refine ⟨hidx_lt, hidx_some, fun τ hτ => ⟨fun h => (huniq τ hτ h).trans hidx_eq_τ₀.symm, ?_⟩⟩
    rintro rfl; exact hidx_some
  have no_two_pops : ∀ {s a b : ℕ}, a < b → b < proc.steps.length →
      proc.steps[a]? = some (.pop s) → proc.steps[b]? = some (.pop s) → False := by
    intro s a b hab hb ha_some hb_some
    have ha : a < proc.steps.length := lt_trans hab hb
    have hin_take : s ∈ (proc.steps.take (a + 1)).filterMap popKey? := by
      rw [← pop_in_list_iff]
      have hlt_take : a < (proc.steps.take (a + 1)).length := by simp; omega
      have hget_take : (proc.steps.take (a + 1))[a]'hlt_take = .pop s := by
        rw [List.getElem_take]
        rw [List.getElem?_eq_getElem ha] at ha_some
        injection ha_some
      exact hget_take ▸ List.getElem_mem hlt_take
    have hin_drop : s ∈ (proc.steps.drop (a + 1)).filterMap popKey? := by
      rw [← pop_in_list_iff]
      have hlt_drop : b - (a + 1) < (proc.steps.drop (a + 1)).length := by simp; omega
      have hget_drop : (proc.steps.drop (a + 1))[b - (a + 1)]'hlt_drop = .pop s := by
        rw [List.getElem_drop]
        have hidx : a + 1 + (b - (a + 1)) = b := by omega
        rw [List.getElem?_eq_getElem hb] at hb_some
        injection hb_some with hb_eq
        simpa [hidx] using hb_eq
      exact hget_drop ▸ List.getElem_mem hlt_drop
    obtain ⟨_, htake_eq, hdrop_eq⟩ := split_prop (a + 1) (by omega)
    rw [htake_eq, List.mem_range'] at hin_take
    rw [hdrop_eq, List.mem_range'] at hin_drop
    rcases hin_take with ⟨i1, hi1, heq1⟩
    rcases hin_drop with ⟨i2, hi2, heq2⟩
    omega
  have pop_props : ∀ s ∈ Finset.Icc 1 P,
      proc.popStepIdx s < proc.steps.length ∧
      proc.steps[proc.popStepIdx s]? = some (.pop s) ∧
      (∀ τ < proc.steps.length, proc.steps[τ]? = some (.pop s) ↔ τ = proc.popStepIdx s) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    apply findIdx_unique (.pop s)
    have hs_in_all : .pop s ∈ proc.steps := by
      rw [pop_in_list_iff]
      have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
      rw [hseq]
      exact List.mem_range'.mpr ⟨s - 1, by omega, by omega⟩
    obtain ⟨τ₀, hτ₀_lt, hτ₀_get⟩ := List.getElem_of_mem hs_in_all
    refine ⟨τ₀, hτ₀_lt, getElem?_of_getElem hτ₀_lt hτ₀_get, fun τ hτ hτ_some => ?_⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact no_two_pops hlt hτ₀_lt hτ_some (getElem?_of_getElem hτ₀_lt hτ₀_get)
    · exact no_two_pops hgt hτ (getElem?_of_getElem hτ₀_lt hτ₀_get) hτ_some
  have s0_iff : ∀ τ ≤ proc.steps.length, ∀ u ∈ Finset.Icc 1 P,
      s0At proc τ + 1 ≤ u ↔ τ ≤ proc.popStepIdx u := by
    intro τ hτ u hu
    obtain ⟨hpop_lt, hpop_get, hpop_uniq⟩ := pop_props u hu
    obtain ⟨hs₀_le, htake_eq, _⟩ := split_prop τ hτ
    rw [Finset.mem_Icc] at hu
    have hnot_take_iff : .pop u ∉ proc.steps.take τ ↔ τ ≤ proc.popStepIdx u := by
      constructor
      · intro hnot
        by_contra hgt
        have hlt_τ : proc.popStepIdx u < τ := by omega
        have hlt_len : proc.popStepIdx u < (proc.steps.take τ).length := by simp [hτ, hlt_τ]
        have hget : (proc.steps.take τ)[proc.popStepIdx u]'hlt_len = .pop u := by
          rw [List.getElem_take]
          rw [List.getElem?_eq_getElem hpop_lt] at hpop_get
          injection hpop_get
        exact hnot (hget ▸ List.getElem_mem hlt_len)
      · intro hle hin
        obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hin
        have hk_τ : k < τ := by simp [List.length_take] at hk_lt; exact hk_lt.1
        have hk_len : k < proc.steps.length := lt_of_lt_of_le hk_τ hτ
        have hk_step : proc.steps[k]? = some (.pop u) := by
          rw [List.getElem?_eq_getElem hk_len]
          rw [List.getElem_take] at hk_eq
          exact congrArg some hk_eq
        have hk_eq_pop := (hpop_uniq k hk_len).mp hk_step
        omega
    rw [← hnot_take_iff, pop_in_list_iff, htake_eq, List.mem_range']
    constructor
    · intro hlo ⟨i, hi, heq⟩; omega
    · intro hnot; by_contra hlt; exact hnot ⟨u - 1, by omega, by omega⟩
  have pop_lt_iff : ∀ s₁ ∈ Finset.Icc 1 P, ∀ s₂ ∈ Finset.Icc 1 P,
      s₁ < s₂ ↔ proc.popStepIdx s₁ < proc.popStepIdx s₂ := by
    intro s₁ hs₁ s₂ hs₂
    obtain ⟨h1_lt, _, _⟩ := pop_props s₁ hs₁
    have h_iff := s0_iff (proc.popStepIdx s₁ + 1) (by omega) s₂ hs₂
    have hs1_false : ¬ (proc.popStepIdx s₁ + 1 ≤ proc.popStepIdx s₁) := by omega
    have hs1_le : ¬ (s0At proc (proc.popStepIdx s₁ + 1) + 1 ≤ s₁) :=
      mt (s0_iff (proc.popStepIdx s₁ + 1) (by omega) s₁ hs₁).mp hs1_false
    have hs1_prev : s0At proc (proc.popStepIdx s₁) + 1 ≤ s₁ :=
      (s0_iff (proc.popStepIdx s₁) (le_of_lt h1_lt) s₁ hs₁).mpr le_rfl
    have htake_succ : proc.steps.take (proc.popStepIdx s₁ + 1) =
        proc.steps.take (proc.popStepIdx s₁) ++ [proc.steps[proc.popStepIdx s₁]'h1_lt] :=
      List.take_succ_eq_append_getElem h1_lt
    have hs0_step : s0At proc (proc.popStepIdx s₁ + 1) ≤ s0At proc (proc.popStepIdx s₁) + 1 := by
      unfold s0At
      rw [htake_succ, List.filter_append, List.length_append]
      cases proc.steps[proc.popStepIdx s₁]'h1_lt <;> simp
    have hs0_exact : s0At proc (proc.popStepIdx s₁ + 1) = s₁ := by omega
    rw [hs0_exact] at h_iff
    omega
  have pop_mono : ∀ s₁ ∈ Finset.Icc 1 P, ∀ s₂ ∈ Finset.Icc 1 P,
      (s₁ < s₂ ↔ proc.popStepIdx s₁ < proc.popStepIdx s₂) ∧
      (s₁ ≤ s₂ ↔ proc.popStepIdx s₁ ≤ proc.popStepIdx s₂) := by
    intro s₁ hs₁ s₂ hs₂
    refine ⟨pop_lt_iff s₁ hs₁ s₂ hs₂, ?_⟩
    have hrev := pop_lt_iff s₂ hs₂ s₁ hs₁
    omega
  have htree_laws := (proc_tree_bst_and_step_keys proc).2
  have ins_props : ∀ u ∈ Finset.Icc 1 P,
      proc.insStep u < proc.popStepIdx u ∧
      proc.steps[proc.insStep u]? = some (.push u) ∧
      (∀ τ < proc.steps.length, proc.steps[τ]? = some (.push u) ↔ τ = proc.insStep u) ∧
      (∀ τ ≤ proc.steps.length,
        u ∈ keyFinset (proc.treeAt τ) ↔ proc.insStep u < τ ∧ τ ≤ proc.popStepIdx u) := by
    intro u hu
    obtain ⟨hp_lt, hp_some, hp_uniq⟩ := pop_props u hu
    have persist_no_pop : ∀ {τ₁ τ₂ : ℕ}, τ₁ ≤ τ₂ → τ₂ ≤ proc.steps.length →
        (∀ t, τ₁ ≤ t → t < τ₂ → t ≠ proc.popStepIdx u) →
        u ∈ keyFinset (proc.treeAt τ₁) → u ∈ keyFinset (proc.treeAt τ₂) := by
      intro τ₁ τ₂ h12 h2len hno hu1
      obtain ⟨d, rfl⟩ : ∃ d, τ₂ = τ₁ + d := ⟨τ₂ - τ₁, by omega⟩
      induction d with
      | zero => simpa using hu1
      | succ d ihd =>
        rw [← Nat.add_assoc]
        have ht_lt : τ₁ + d < proc.steps.length := by omega
        have hu_mid := ihd (by omega) (by omega) (fun t ht1 ht2 => hno t ht1 (by omega))
        have hstep := htree_laws (τ₁ + d) ht_lt
        cases hop : proc.steps[τ₁ + d]'ht_lt with
        | push w =>
          rw [hop] at hstep; rw [hstep.2.2.2]; exact Finset.mem_insert_of_mem hu_mid
        | shift =>
          rw [hop] at hstep; simpa [hstep] using hu_mid
        | upperRot a b =>
          rw [hop] at hstep; simpa [hstep.2] using hu_mid
        | pop s =>
          rw [hop] at hstep; rw [hstep.2.2, Finset.mem_erase]
          refine ⟨?_, hu_mid⟩
          rintro rfl
          exact hno (τ₁ + d) (by omega) (by omega)
            ((hp_uniq (τ₁ + d) ht_lt).mp (getElem?_of_getElem ht_lt hop))
    have absent_no_push : ∀ {τ₁ τ₂ : ℕ}, τ₁ ≤ τ₂ → τ₂ ≤ proc.steps.length →
        (∀ (t : ℕ) (ht : t < proc.steps.length), τ₁ ≤ t → t < τ₂ → proc.steps[t]'ht ≠ .push u) →
        u ∉ keyFinset (proc.treeAt τ₁) → u ∉ keyFinset (proc.treeAt τ₂) := by
      intro τ₁ τ₂ h12 h2len hno hu1
      obtain ⟨d, rfl⟩ : ∃ d, τ₂ = τ₁ + d := ⟨τ₂ - τ₁, by omega⟩
      induction d with
      | zero => simpa using hu1
      | succ d ihd =>
        rw [← Nat.add_assoc]
        have ht_lt : τ₁ + d < proc.steps.length := by omega
        have hu_mid := ihd (by omega) (by omega) (fun t ht ht1 ht2 => hno t ht ht1 (by omega))
        have hstep := htree_laws (τ₁ + d) ht_lt
        cases hop : proc.steps[τ₁ + d]'ht_lt with
        | push w =>
          rw [hop] at hstep; rw [hstep.2.2.2, Finset.mem_insert]
          rintro (rfl | h_in)
          · exact hno (τ₁ + d) ht_lt (by omega) (by omega) hop
          · exact hu_mid h_in
        | shift =>
          rw [hop] at hstep; simpa [hstep] using hu_mid
        | upperRot a b =>
          rw [hop] at hstep; simpa [hstep.2] using hu_mid
        | pop s =>
          rw [hop] at hstep; rw [hstep.2.2, Finset.mem_erase]
          exact fun h => hu_mid h.2
    have hu_at_pop : u ∈ keyFinset (proc.treeAt (proc.popStepIdx u)) := by
      have hstep := htree_laws (proc.popStepIdx u) hp_lt
      have hop : proc.steps[proc.popStepIdx u]'hp_lt = .pop u := by
        rw [List.getElem?_eq_getElem hp_lt] at hp_some; injection hp_some
      rw [hop] at hstep; exact hstep.1
    have hex_push : ∃ τ₀, τ₀ < proc.popStepIdx u ∧ proc.steps[τ₀]? = some (.push u) := by
      by_contra hnone
      have hu0 : u ∉ keyFinset (proc.treeAt 0) := by
        simp [FoldedPopProcess.treeAt, FoldedPopProcess.stateAt, keyFinset]
      refine absent_no_push (Nat.zero_le _) (le_of_lt hp_lt)
        (fun t ht _ ht2 hpush => hnone ⟨t, ht2, getElem?_of_getElem ht hpush⟩) hu0 hu_at_pop
    obtain ⟨τ₀, hτ₀_pop, hτ₀_some⟩ := hex_push
    have hτ₀_len : τ₀ < proc.steps.length := lt_trans hτ₀_pop hp_lt
    have hτ₀_push : proc.steps[τ₀]'hτ₀_len = .push u := by
      rw [List.getElem?_eq_getElem hτ₀_len] at hτ₀_some; injection hτ₀_some
    have hpush_uniq_τ₀ : ∀ τ < proc.steps.length, proc.steps[τ]? = some (.push u) → τ = τ₀ := by
      intro τ hτ hτ_some
      have hτ_eq : proc.steps[τ]'hτ = .push u := by
        rw [List.getElem?_eq_getElem hτ] at hτ_some; injection hτ_some
      by_contra hne
      have not_two_pushes : ∀ (a b : ℕ) (ha : a < proc.steps.length) (hb : b < proc.steps.length),
          a < b → proc.steps[a]'ha = .push u → proc.steps[b]'hb = .push u → False := by
        intro a b ha hb hab hpa hpb
        by_cases hb_le : b ≤ proc.popStepIdx u
        · have hu_a1 : u ∈ keyFinset (proc.treeAt (a + 1)) := by
            have hstep := htree_laws a ha; rw [hpa] at hstep; rw [hstep.2.2.2]
            exact Finset.mem_insert_self _ _
          have hu_b := persist_no_pop (by omega) (le_of_lt hb) (fun t _ htb => by omega) hu_a1
          have hstep_b := htree_laws b hb; rw [hpb] at hstep_b
          exact hstep_b.2.2.1 hu_b
        · have hu_b1 : u ∈ keyFinset (proc.treeAt (b + 1)) := by
            have hstep := htree_laws b hb; rw [hpb] at hstep; rw [hstep.2.2.2]
            exact Finset.mem_insert_self _ _
          have hu_end := persist_no_pop (by omega) le_rfl (fun t htb _ => by omega) hu_b1
          have hend : proc.treeAt proc.steps.length = .nil :=
            congrArg Prod.fst (proc_stateAt_end proc)
          simp [hend, keyFinset] at hu_end
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact not_two_pushes τ τ₀ hτ hτ₀_len hlt hτ_eq hτ₀_push
      · exact not_two_pushes τ₀ τ hτ₀_len hτ hgt hτ₀_push hτ_eq
    obtain ⟨hins_lt, hins_some, hins_uniq⟩ := findIdx_unique (.push u)
      ⟨τ₀, hτ₀_len, hτ₀_some, hpush_uniq_τ₀⟩
    change proc.insStep u < proc.steps.length at hins_lt
    change proc.steps[proc.insStep u]? = some (.push u) at hins_some
    change ∀ τ < proc.steps.length, proc.steps[τ]? = some (.push u) ↔ τ = proc.insStep u at hins_uniq
    have hins_eq_τ₀ : proc.insStep u = τ₀ := hpush_uniq_τ₀ (proc.insStep u) hins_lt hins_some
    have hins_lt_pop : proc.insStep u < proc.popStepIdx u := hins_eq_τ₀ ▸ hτ₀_pop
    refine ⟨hins_lt_pop, hins_some, hins_uniq, fun τ hτ => ?_⟩
    by_cases h1 : τ ≤ proc.insStep u
    · constructor
      · intro hu_in
        exfalso
        have hu0 : u ∉ keyFinset (proc.treeAt 0) := by
          simp [FoldedPopProcess.treeAt, FoldedPopProcess.stateAt, keyFinset]
        refine absent_no_push (Nat.zero_le τ) hτ (fun t ht _ ht2 hpush => ?_) hu0 hu_in
        have := (hins_uniq t ht).mp (getElem?_of_getElem ht hpush); omega
      · intro ⟨hlt, _⟩; omega
    · by_cases h2 : τ ≤ proc.popStepIdx u
      · refine ⟨fun _ => ⟨by omega, h2⟩, fun _ => ?_⟩
        have hins_push : proc.steps[proc.insStep u]'hins_lt = .push u := by
          rw [List.getElem?_eq_getElem hins_lt] at hins_some; injection hins_some
        have hu_after_ins : u ∈ keyFinset (proc.treeAt (proc.insStep u + 1)) := by
          have hstep := htree_laws (proc.insStep u) hins_lt
          rw [hins_push] at hstep; rw [hstep.2.2.2]; exact Finset.mem_insert_self _ _
        exact persist_no_pop (by omega) hτ (fun t _ _ => by omega) hu_after_ins
      · refine ⟨fun hu_in => ?_, fun ⟨_, hle⟩ => by omega⟩
        exfalso
        have hp_pop : proc.steps[proc.popStepIdx u]'hp_lt = .pop u := by
          rw [List.getElem?_eq_getElem hp_lt] at hp_some; injection hp_some
        have hu_after_pop : u ∉ keyFinset (proc.treeAt (proc.popStepIdx u + 1)) := by
          have hstep := htree_laws (proc.popStepIdx u) hp_lt
          rw [hp_pop] at hstep; simp [hstep.2.2]
        refine absent_no_push (by omega) hτ (fun t ht ht1 _ hpush => ?_) hu_after_pop hu_in
        have := (hins_uniq t ht).mp (getElem?_of_getElem ht hpush); omega
  exact ⟨split_prop, pop_props, pop_mono, s0_iff, ins_props⟩

theorem uSetAt_props {P : ℕ} (proc : FoldedPopProcess P) :
    (∀ τ ≤ proc.steps.length,
      keyFinset (proc.treeAt τ) ⊆ Finset.Icc (s0At proc τ + 1) P ∧
      ∀ u : ℕ, u ∈ uSetAt proc τ ↔ u ∈ Finset.Icc 1 P ∧ τ ≤ proc.insStep u) ∧
    (∀ τ (hτ : τ < proc.steps.length),
      match proc.steps[τ]'hτ with
      | .push w =>
        w ∈ uSetAt proc τ ∧
        uSetAt proc (τ + 1) = (uSetAt proc τ).erase w ∧
        ∀ y ∈ (uSetAt proc τ).erase w, proc.insStep w < proc.insStep y
      | .shift =>
        uSetAt proc (τ + 1) = uSetAt proc τ
      | .upperRot _ _ =>
        uSetAt proc (τ + 1) = uSetAt proc τ
      | .pop s =>
        uSetAt proc (τ + 1) = uSetAt proc τ ∧
        ∀ u ∈ uSetAt proc τ, s < u) := by
  obtain ⟨htree_inv, htree_step⟩ := proc_tree_bst_and_step_keys proc
  obtain ⟨_, hpop, hpop_mono, hs0_iff, hins⟩ := popStepIdx_and_insStep_props proc
  have hchar : ∀ τ ≤ proc.steps.length,
      keyFinset (proc.treeAt τ) ⊆ Finset.Icc (s0At proc τ + 1) P ∧
      ∀ u : ℕ, u ∈ uSetAt proc τ ↔ u ∈ Finset.Icc 1 P ∧ τ ≤ proc.insStep u := by
    intro τ hτ
    have hsub : keyFinset (proc.treeAt τ) ⊆ Finset.Icc (s0At proc τ + 1) P := by
      intro u hu
      have hu_Icc : u ∈ Finset.Icc 1 P := (htree_inv τ hτ).2 hu
      have h_alive := (hins u hu_Icc).2.2.2 τ hτ |>.mp hu
      have hs0 := (hs0_iff τ hτ u hu_Icc).mpr h_alive.2
      exact Finset.mem_Icc.mpr ⟨hs0, (Finset.mem_Icc.mp hu_Icc).2⟩
    refine ⟨hsub, fun u => ?_⟩
    unfold uSetAt
    rw [Finset.mem_sdiff]
    constructor
    · rintro ⟨hu_s0, hu_not⟩
      have hu_Icc : u ∈ Finset.Icc 1 P :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hu_s0).1; omega,
                            (Finset.mem_Icc.mp hu_s0).2⟩
      have hpop_u : τ ≤ proc.popStepIdx u := (hs0_iff τ hτ u hu_Icc).mp (Finset.mem_Icc.mp hu_s0).1
      have hnot_lt : ¬ (proc.insStep u < τ) := fun hlt =>
        hu_not (((hins u hu_Icc).2.2.2 τ hτ).mpr ⟨hlt, hpop_u⟩)
      exact ⟨hu_Icc, by omega⟩
    · rintro ⟨hu_Icc, hτ_ins⟩
      have hins_lt_pop := (hins u hu_Icc).1
      have hs0_u : s0At proc τ + 1 ≤ u := (hs0_iff τ hτ u hu_Icc).mpr (by omega)
      refine ⟨Finset.mem_Icc.mpr ⟨hs0_u, (Finset.mem_Icc.mp hu_Icc).2⟩, ?_⟩
      intro hu_in
      have := ((hins u hu_Icc).2.2.2 τ hτ).mp hu_in
      omega
  refine ⟨hchar, fun τ hτ => ?_⟩
  have hτ_le : τ ≤ proc.steps.length := le_of_lt hτ
  have hτ1_le : τ + 1 ≤ proc.steps.length := hτ
  have no_push_eq : (∀ u ∈ Finset.Icc 1 P, proc.steps[τ]'hτ ≠ .push u) →
      uSetAt proc (τ + 1) = uSetAt proc τ := by
    intro hno
    ext u
    rw [(hchar (τ + 1) hτ1_le).2 u, (hchar τ hτ_le).2 u]
    constructor
    · rintro ⟨hu, h⟩; exact ⟨hu, by omega⟩
    · rintro ⟨hu, h⟩
      refine ⟨hu, ?_⟩
      have hins_ne : proc.insStep u ≠ τ := by
        intro heq
        have hsome := (hins u hu).2.1
        rw [heq, List.getElem?_eq_getElem hτ] at hsome
        injection hsome with hop_eq
        exact hno u hu hop_eq
      omega
  cases hop : proc.steps[τ]'hτ with
  | shift =>
    exact no_push_eq (by intro _ _ h; rw [hop] at h; cases h)
  | upperRot a b =>
    exact no_push_eq (by intro _ _ h; rw [hop] at h; cases h)
  | pop s =>
    refine ⟨no_push_eq (by intro _ _ h; rw [hop] at h; cases h), fun u hu => ?_⟩
    obtain ⟨hu_Icc, hτ_ins⟩ := ((hchar τ hτ_le).2 u).mp hu
    have hstep := htree_step τ hτ
    rw [hop] at hstep
    have hs_Icc : s ∈ Finset.Icc 1 P := (htree_inv τ hτ_le).2 hstep.1
    have hpop_s : τ = proc.popStepIdx s :=
      ((hpop s hs_Icc).2.2 τ hτ).mp (getElem?_of_getElem hτ hop)
    have hins_lt_pop_u := (hins u hu_Icc).1
    exact (hpop_mono s hs_Icc u hu_Icc).1.mpr (by omega)
  | push w =>
    have hstep := htree_step τ hτ
    rw [hop] at hstep
    have hw_Icc : w ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨hstep.1, hstep.2.1⟩
    have hins_w : proc.insStep w = τ :=
      (((hins w hw_Icc).2.2.1 τ hτ).mp (getElem?_of_getElem hτ hop)).symm
    have hw_in : w ∈ uSetAt proc τ := ((hchar τ hτ_le).2 w).mpr ⟨hw_Icc, by omega⟩
    have herase : uSetAt proc (τ + 1) = (uSetAt proc τ).erase w := by
      ext y
      rw [(hchar (τ + 1) hτ1_le).2 y, Finset.mem_erase, (hchar τ hτ_le).2 y]
      constructor
      · rintro ⟨hy_Icc, hτ1_y⟩
        refine ⟨?_, hy_Icc, by omega⟩
        rintro rfl; omega
      · rintro ⟨hy_ne, hy_Icc, hτ_y⟩
        refine ⟨hy_Icc, ?_⟩
        have hins_y_ne : proc.insStep y ≠ τ := by
          intro heq
          have hsome := (hins y hy_Icc).2.1
          rw [heq, List.getElem?_eq_getElem hτ, hop] at hsome
          injection hsome with h_eq
          injection h_eq with hwy
          exact hy_ne hwy.symm
        omega
    refine ⟨hw_in, herase, fun y hy => ?_⟩
    rw [← herase, (hchar (τ + 1) hτ1_le).2 y] at hy
    omega

theorem tauEmpty_window_bounds {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1) :
    let subs := childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X
    let Sp := subblock1 subs p
    let tStart := proc.popStepIdx Sp.lo
    let tEnd := proc.popStepIdx (subblock1 subs (p + 1)).lo
    tStart < tauEmpty proc Sp ∧
    tauEmpty proc Sp ≤ tEnd ∧
    tEnd < proc.steps.length ∧
    ∀ τ ≤ tEnd, s0At proc τ ≤ Sp.hi := by
  dsimp only
  set chain := scaleTreePartitionChain T P M
  set subs := childSubblocks (chain ℓ.succ) X
  have hK2 : 2 ≤ subs.length := validScaleTree_K_X_ge_two hValid ℓ X hX
  have hp_len : p ≤ subs.length := by omega
  have hp1_len : p + 1 ≤ subs.length := by omega
  obtain ⟨hX1, _, hXP, _, hsub_c, _, hconsec, _, _, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨_, _, hX_Splo, hSplo_hi, hSphi_X, _⟩ := hsub_c p (Finset.mem_Icc.mpr ⟨hp1, hp_len⟩)
  obtain ⟨_, _, hX_Sp1lo, hSp1lo_hi, hSp1hi_X, _⟩ :=
    hsub_c (p + 1) (Finset.mem_Icc.mpr ⟨by omega, hp1_len⟩)
  have hlink : (subblock1 subs p).hi + 1 = (subblock1 subs (p + 1)).lo := hconsec p hp1 hp1_len
  set Sp := subblock1 subs p
  set Sp1 := subblock1 subs (p + 1)
  obtain ⟨_, hpop, hpop_mono, hs0_iff, _⟩ := popStepIdx_and_insStep_props proc
  obtain ⟨_, htree_step⟩ := proc_tree_bst_and_step_keys proc
  have hSplo_Icc : Sp.lo ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hSp1lo_Icc : Sp1.lo ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨htStart_lt, htStart_some, _⟩ := hpop Sp.lo hSplo_Icc
  obtain ⟨htEnd_lt, _, _⟩ := hpop Sp1.lo hSp1lo_Icc
  have hSplo_in_tree : Sp.lo ∈ keyFinset (proc.treeAt (proc.popStepIdx Sp.lo)) := by
    have hstep := htree_step (proc.popStepIdx Sp.lo) htStart_lt
    have hop : proc.steps[proc.popStepIdx Sp.lo]'htStart_lt = .pop Sp.lo := by
      rw [List.getElem?_eq_getElem htStart_lt] at htStart_some; injection htStart_some
    rw [hop] at hstep; exact hstep.1
  have hSplo_in_inter : Sp.lo ∈ keyFinset (proc.treeAt (proc.popStepIdx Sp.lo)) ∩ Sp.toFinset :=
    Finset.mem_inter.mpr ⟨hSplo_in_tree, Finset.mem_Icc.mpr ⟨le_rfl, hSplo_hi⟩⟩
  have hsMax_ge : Sp.lo ≤ sMax proc Sp := Finset.le_sup (f := id) hSplo_in_inter
  have hsMax_le : sMax proc Sp ≤ Sp.hi := by
    apply Finset.sup_le
    intro v hv
    exact (Finset.mem_Icc.mp (Finset.mem_inter.mp hv).2).2
  have hsMax_Icc : sMax proc Sp ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hle_pop1 : proc.popStepIdx Sp.lo ≤ proc.popStepIdx (sMax proc Sp) :=
    (hpop_mono Sp.lo hSplo_Icc (sMax proc Sp) hsMax_Icc).2.mp hsMax_ge
  have hlt_pop2 : proc.popStepIdx (sMax proc Sp) < proc.popStepIdx Sp1.lo :=
    (hpop_mono (sMax proc Sp) hsMax_Icc Sp1.lo hSp1lo_Icc).1.mp (by omega)
  refine ⟨by unfold tauEmpty; omega, by unfold tauEmpty; omega, htEnd_lt, fun τ hτ => ?_⟩
  have hs0_le : s0At proc τ + 1 ≤ Sp1.lo :=
    (hs0_iff τ (le_trans hτ (le_of_lt htEnd_lt)) Sp1.lo hSp1lo_Icc).mpr hτ
  omega

theorem takeThrough_props {xs : List ℕ} (hpw : xs.Pairwise (· < ·))
    {b : ℕ} (hb : b ∈ xs) :
    let sub := takeThrough xs b
    sub <+: xs ∧
    sub ≠ [] ∧
    sub.Pairwise (· < ·) ∧
    sub.head? = xs.head? ∧
    sub.getLast? = some b ∧
    (∀ w, w ∈ sub ↔ w ∈ xs ∧ w ≤ b) := by
  dsimp only
  induction xs with
  | nil => cases hb
  | cons x rest ih =>
    rw [List.pairwise_cons] at hpw
    unfold takeThrough
    split_ifs with hxb
    · subst x
      refine ⟨⟨rest, rfl⟩, List.cons_ne_nil _ _, List.pairwise_singleton _ _, rfl, rfl, fun w => ?_⟩
      rw [List.mem_singleton, List.mem_cons]
      constructor
      · rintro rfl; exact ⟨Or.inl rfl, le_rfl⟩
      · rintro ⟨rfl | hrest, hle⟩
        · rfl
        · exact absurd (lt_of_le_of_lt hle (hpw.1 w hrest)) (lt_irrefl w)
    · have hb_rest : b ∈ rest := by
        rcases List.mem_cons.mp hb with rfl | h
        · exact absurd rfl hxb
        · exact h
      obtain ⟨hpref, hne, hpw_sub, _, hlast, hmem_iff⟩ := ih hpw.2 hb_rest
      have hxb_lt : x < b := hpw.1 b hb_rest
      refine ⟨by rcases hpref with ⟨t, ht⟩; exact ⟨t, by simp [ht]⟩,
        List.cons_ne_nil _ _, ?_, rfl, ?_, fun w => ?_⟩
      · exact List.Pairwise.cons (fun w hw => hpw.1 w ((hmem_iff w).mp hw).1) hpw_sub
      · rw [List.getLast?_cons_of_ne_nil hne]; exact hlast
      · simp only [List.mem_cons, hmem_iff]
        constructor
        · rintro (rfl | ⟨hr, hle⟩)
          · exact ⟨Or.inl rfl, le_of_lt hxb_lt⟩
          · exact ⟨Or.inr hr, hle⟩
        · rintro ⟨rfl | hr, hle⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hr, hle⟩

theorem mem_rInt_iff {P : ℕ} (proc : FoldedPopProcess P) (e : InternalPopRot) :
    e ∈ proc.rInt ↔
      ∃ (hτ : e.stepIdx < proc.steps.length) (b : ℕ),
        proc.steps[e.stepIdx]'hτ = .pop e.s ∧
        proc.b1At e.stepIdx = some b ∧
        let sub := takeThrough (leftSpine (proc.treeAt e.stepIdx)) b
        e.h = (sub.length - 1 - 1) / 2 ∧
        1 ≤ e.j ∧ e.j ≤ e.h ∧
        sub[2 * e.j - 1]? = some e.x ∧
        sub[2 * e.j]? = some e.y ∧
        sub[2 * e.j + 1]? = some e.z := by
  have collect_iff : ∀ (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (ops : List FoldedOp),
      e ∈ collectFoldedPopRots idx st ops ↔
        ∃ (d : ℕ) (hd : d < ops.length),
          idx + d = e.stepIdx ∧
          e ∈ foldedPopRotsAt (idx + d) ((ops.take d).foldl FoldedOp.step st) (ops[d]'hd) := by
    intro idx st ops
    induction ops generalizing idx st with
    | nil => simp [collectFoldedPopRots]
    | cons op rest ih =>
      simp only [collectFoldedPopRots, List.mem_append, ih]
      constructor
      · rintro (h0 | ⟨d, hd, hstep, hmem⟩)
        · refine ⟨0, Nat.zero_lt_succ _, ?_, by simpa using h0⟩
          cases op with
          | pop s =>
            rcases st with ⟨tree, none | b⟩
            · simp [foldedPopRotsAt] at h0
            · simp only [foldedPopRotsAt, List.mem_filterMap, List.mem_range] at h0
              rcases h0 with ⟨i, _, hmatch⟩
              split at hmatch <;> simp at hmatch
              rcases hmatch with rfl
              dsimp only; omega
          | _ => simp [foldedPopRotsAt] at h0
        · refine ⟨d + 1, Nat.succ_lt_succ hd, by omega, ?_⟩
          simpa [List.take_succ_cons, List.foldl_cons, Nat.add_right_comm, Nat.add_assoc] using hmem
      · rintro ⟨d, hd, hstep, hmem⟩
        cases d with
        | zero => left; simpa using hmem
        | succ d' =>
          right
          refine ⟨d', Nat.lt_of_succ_lt_succ hd, by omega, ?_⟩
          simpa [List.take_succ_cons, List.foldl_cons, Nat.add_right_comm, Nat.add_assoc] using hmem
  unfold FoldedPopProcess.rInt
  rw [List.mem_toFinset, collect_iff]
  constructor
  · rintro ⟨d, hd, hidx, hmem⟩
    simp only [Nat.zero_add] at hidx hmem
    subst d
    change e ∈ foldedPopRotsAt e.stepIdx (proc.stateAt e.stepIdx) (proc.steps[e.stepIdx]'hd) at hmem
    cases hop : proc.steps[e.stepIdx]'hd with
    | pop s =>
      rw [hop] at hmem
      unfold foldedPopRotsAt at hmem
      cases hb : (proc.stateAt e.stepIdx).2 with
      | none => rw [hb] at hmem; simp at hmem
      | some b =>
        rw [hb] at hmem
        dsimp only at hmem
        rw [List.mem_filterMap] at hmem
        rcases hmem with ⟨idx, hidx_range, hmatch⟩
        rw [List.mem_range] at hidx_range
        set sub := takeThrough (leftSpine (proc.stateAt e.stepIdx).1) b
        cases hx : sub[2 * (idx + 1) - 1]? with
        | none => simp [hx] at hmatch
        | some x =>
          cases hy : sub[2 * (idx + 1)]? with
          | none => simp [hx, hy] at hmatch
          | some y =>
            cases hz : sub[2 * (idx + 1) + 1]? with
            | none => simp [hx, hy, hz] at hmatch
            | some z =>
              simp only [hx, hy, hz, Option.some.injEq] at hmatch
              have hs_eq := congrArg InternalPopRot.s hmatch
              have hj_eq := congrArg InternalPopRot.j hmatch
              have hh_eq := congrArg InternalPopRot.h hmatch
              have hx_eq := congrArg InternalPopRot.x hmatch
              have hy_eq := congrArg InternalPopRot.y hmatch
              have hz_eq := congrArg InternalPopRot.z hmatch
              dsimp only at hs_eq hj_eq hh_eq hx_eq hy_eq hz_eq
              rw [hs_eq] at hop
              rw [hj_eq] at hx hy hz
              rw [hx_eq] at hx; rw [hy_eq] at hy; rw [hz_eq] at hz
              exact ⟨hd, b, hop, hb, hh_eq.symm, by omega, by omega, hx, hy, hz⟩
    | _ => rw [hop] at hmem; simp [foldedPopRotsAt] at hmem
  · rintro ⟨hτ, b, hop, hb, hh_eq, hj1, hjh, hx, hy, hz⟩
    refine ⟨e.stepIdx, hτ, Nat.zero_add _, ?_⟩
    simp only [Nat.zero_add]
    change e ∈ foldedPopRotsAt e.stepIdx (proc.stateAt e.stepIdx) (proc.steps[e.stepIdx]'hτ)
    rw [hop]
    unfold foldedPopRotsAt
    change e ∈ match proc.b1At e.stepIdx with
      | none => []
      | some b => _
    rw [hb]
    dsimp only
    rw [List.mem_filterMap]
    dsimp only [FoldedPopProcess.treeAt] at hh_eq hx hy hz
    refine ⟨e.j - 1, List.mem_range.mpr (by omega), ?_⟩
    have hj_add : e.j - 1 + 1 = e.j := by omega
    simp only [hj_add, hx, hy, hz, ← hh_eq]

theorem mem_vXp_props {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1)
    {e : InternalPopRot} (he : e ∈ vXp P proc (scaleTreePartitionChain T P M) (ℓ.val + 1) X p) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    let Sp := subblock1 subs p
    let b := subblockIndex1 subs e.x
    let q := subblockIndex1 subs e.y
    e ∈ proc.rInt ∧
    proc.popStepIdx Sp.lo ≤ e.stepIdx ∧
    e.stepIdx < tauEmpty proc Sp ∧
    p + 1 ≤ b ∧ b < q ∧ q ≤ subs.length ∧
    e.x ∈ (subblock1 subs b).toFinset ∧
    e.y ∈ (subblock1 subs q).toFinset ∧
    (subblock1 subs b).hi < e.y ∧
    (subblock1 subs q).hi < e.z := by
  dsimp only
  have hChain := validScaleTree_chain hValid
  have hP := hValid.1
  have hℓ : 1 ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  have hfin_eq : (⟨ℓ.val + 1, Nat.lt_succ_of_le hℓ.2⟩ : Fin (M + 1)) = ℓ.succ := rfl
  have hK2 : 2 ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length :=
    validScaleTree_K_X_ge_two hValid ℓ X hX
  have hp_len : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length := by omega
  obtain ⟨hX1, _, hXP, _, hsub_c, hlt_idx, _, _, _, hcov⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨_, hSp_chain, hX_Splo, _, hSphi_X, hSp_mem⟩ :=
    hsub_c p (Finset.mem_Icc.mpr ⟨hp1, hp_len⟩)
  unfold vXp at he
  simp only [hℓ.1, hℓ.2, and_self, ↓reduceDIte, hfin_eq] at he
  obtain ⟨he_act, hsep_xy, hes_Sp⟩ := Finset.mem_filter.mp he
  unfold b3ExitAct at he_act
  obtain ⟨he_exit, hact_cond⟩ := Finset.mem_filter.mp he_act
  simp only [hsep_xy, hℓ.2, ↓reduceDIte, hfin_eq] at hact_cond
  obtain ⟨_, hblock_es_Sp, hblock_es_X⟩ := hSp_mem e.s hes_Sp
  rw [hblock_es_Sp] at hact_cond
  unfold b3Exit at he_exit
  obtain ⟨he_rInt, hexit_cond⟩ := Finset.mem_filter.mp he_exit
  simp only [hsep_xy, hℓ, and_self, ↓reduceDIte, hfin_eq] at hexit_cond
  obtain ⟨hsep_sx_eq, hz_gt⟩ := hexit_cond
  have hsep_sx : partSepScale P (scaleTreePartitionChain T P M) e.s e.x = ℓ.val + 1 := hsep_sx_eq
  -- Basic key bounds from `e ∈ proc.rInt`
  obtain ⟨hbst_all, _⟩ := proc_tree_bst_and_step_keys proc
  obtain ⟨_, hpop, hpop_mono, _, _⟩ := popStepIdx_and_insStep_props proc
  obtain ⟨hτ, b1, hop, hb1, _, hj1, _, hx_sub, hy_sub, hz_sub⟩ := (mem_rInt_iff proc e).mp he_rInt
  obtain ⟨hval, _⟩ := proc_step_at proc hτ
  rw [hop] at hval
  rcases hval with ⟨b1', _, hmin, hb1', hb1'_ls⟩
  change proc.b1At e.stepIdx = some b1' at hb1'
  rw [hb1] at hb1'; injection hb1' with hbb; subst b1'
  obtain ⟨ht_bst, ht_sub⟩ := hbst_all e.stepIdx (le_of_lt hτ)
  have hpw_ls := leftSpine_pairwise_lt ht_bst
  obtain ⟨_, _, hpw_sub, hhd_sub, _, hmem_sub⟩ := takeThrough_props hpw_ls hb1'_ls
  have hs_sub0 : (takeThrough (leftSpine (proc.treeAt e.stepIdx)) b1)[0]? = some e.s := by
    rw [← List.head?_eq_getElem?, hhd_sub, head?_leftSpine_eq_minKey? ht_bst]
    exact hmin
  have hlt_sub : ∀ {i₁ i₂ v₁ v₂ : ℕ}, i₁ < i₂ →
      (takeThrough (leftSpine (proc.treeAt e.stepIdx)) b1)[i₁]? = some v₁ →
      (takeThrough (leftSpine (proc.treeAt e.stepIdx)) b1)[i₂]? = some v₂ → v₁ < v₂ := by
    intro i₁ i₂ v₁ v₂ hi h1 h2
    obtain ⟨h1_lt, rfl⟩ := List.getElem?_eq_some_iff.mp h1
    obtain ⟨h2_lt, rfl⟩ := List.getElem?_eq_some_iff.mp h2
    exact List.pairwise_iff_getElem.mp hpw_sub i₁ i₂ h1_lt h2_lt hi
  have hs_lt_x : e.s < e.x := hlt_sub (by omega) hs_sub0 hx_sub
  have hx_lt_y : e.x < e.y := hlt_sub (by omega) hx_sub hy_sub
  have hz_in_Icc : e.z ∈ Finset.Icc 1 P :=
    ht_sub ((mem_iff_mem_keyFinset _ _).mp
      (mem_of_mem_leftSpine (((hmem_sub e.z).mp (List.mem_of_getElem? hz_sub)).1)))
  have hy_in_Icc : e.y ∈ Finset.Icc 1 P :=
    ht_sub ((mem_iff_mem_keyFinset _ _).mp
      (mem_of_mem_leftSpine (((hmem_sub e.y).mp (List.mem_of_getElem? hy_sub)).1)))
  have hx_in_Icc : e.x ∈ Finset.Icc 1 P :=
    ht_sub ((mem_iff_mem_keyFinset _ _).mp
      (mem_of_mem_leftSpine (((hmem_sub e.x).mp (List.mem_of_getElem? hx_sub)).1)))
  have hes_bounds := Finset.mem_Icc.mp hes_Sp
  have hs_in_Icc : e.s ∈ Finset.Icc 1 P :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hSplo_Icc : (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).lo ∈
      Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hstep_eq : e.stepIdx = proc.popStepIdx e.s :=
    ((hpop e.s hs_in_Icc).2.2 e.stepIdx hτ).mp (getElem?_of_getElem hτ hop)
  have htStart_le :
      proc.popStepIdx (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).lo ≤
        e.stepIdx := by
    rw [hstep_eq]
    exact (hpop_mono _ hSplo_Icc e.s hs_in_Icc).2.mp hes_bounds.1
  obtain ⟨hsx_coarse, hsx_fine⟩ :=
    (partSepScale_eq_iff hChain hs_in_Icc hx_in_Icc ℓ).mp hsep_sx
  obtain ⟨hxy_coarse, hxy_fine⟩ :=
    (partSepScale_eq_iff hChain hx_in_Icc hy_in_Icc ℓ).mp hsep_xy
  have hx_blockX : blockAt (scaleTreePartitionChain T P M ℓ.castSucc) e.x = X :=
    hsx_coarse.symm.trans hblock_es_X
  have hy_blockX : blockAt (scaleTreePartitionChain T P M ℓ.castSucc) e.y = X :=
    hxy_coarse.symm.trans hx_blockX
  have hx_in_X : e.x ∈ Finset.Icc X.lo X.hi := by
    obtain ⟨_, hlo, hhi⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 ℓ.castSucc)).1 e.x hx_in_Icc
    rw [hx_blockX] at hlo hhi
    exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  have hy_in_X : e.y ∈ Finset.Icc X.lo X.hi := by
    obtain ⟨_, hlo, hhi⟩ := (blockAt_mem_and_unique hP (hChain.2.2.1 ℓ.castSucc)).1 e.y hy_in_Icc
    rw [hy_blockX] at hlo hhi
    exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  obtain ⟨hb_Icc, hx_Sb⟩ := hcov e.x hx_in_X
  obtain ⟨hq_Icc, hy_Sq⟩ := hcov e.y hy_in_X
  obtain ⟨_, hblock_ex, _⟩ := hsub_c _ hb_Icc |>.2.2.2.2.2 e.x hx_Sb
  obtain ⟨_, hblock_ey, _⟩ := hsub_c _ hq_Icc |>.2.2.2.2.2 e.y hy_Sq
  have hx_Sb_bounds := Finset.mem_Icc.mp hx_Sb
  have hy_Sq_bounds := Finset.mem_Icc.mp hy_Sq
  have hp_lt_b : p < subblockIndex1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) e.x := by
    by_contra hle
    rcases eq_or_lt_of_le (Nat.not_lt.mp hle) with hpb | hbp
    · rw [hpb] at hblock_ex
      exact hsx_fine (hblock_es_Sp.trans hblock_ex.symm)
    · have := hlt_idx _ p (Finset.mem_Icc.mp hb_Icc).1 hbp hp_len
      omega
  have hb_lt_q :
      subblockIndex1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) e.x <
        subblockIndex1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) e.y := by
    by_contra hle
    rcases eq_or_lt_of_le (Nat.not_lt.mp hle) with hqb | hqp
    · rw [hqb] at hblock_ey
      exact hxy_fine (hblock_ex.trans hblock_ey.symm)
    · have := hlt_idx _ _ (Finset.mem_Icc.mp hq_Icc).1 hqp (Finset.mem_Icc.mp hb_Icc).2
      omega
  have hSb_lt_Sq := hlt_idx _ _ (Finset.mem_Icc.mp hb_Icc).1 hb_lt_q (Finset.mem_Icc.mp hq_Icc).2
  rw [hblock_ey] at hz_gt
  exact ⟨he_rInt, htStart_le, hact_cond, by omega, hb_lt_q, (Finset.mem_Icc.mp hq_Icc).2,
    hx_Sb, hy_Sq, by omega, hz_gt⟩

/-! ## Section 3: Cartesian BST & `cartesianExt` Laws -/

def cartLt (insFn : ℕ → ℕ) (a b : ℕ) : Prop :=
  insFn a < insFn b ∨ (insFn a = insFn b ∧ a < b)

def cartStep (insFn : ℕ → ℕ) (best y : ℕ) : ℕ :=
  if insFn y < insFn best ∨ (insFn y = insFn best ∧ y < best) then y else best

theorem cartLt_irrefl (insFn : ℕ → ℕ) (a : ℕ) : ¬ cartLt insFn a a := by
  unfold cartLt; omega

theorem cartLt_trans {insFn : ℕ → ℕ} {a b c : ℕ}
    (hab : cartLt insFn a b) (hbc : cartLt insFn b c) : cartLt insFn a c := by
  unfold cartLt at *; omega

theorem cartLt_trichotomy (insFn : ℕ → ℕ) (a b : ℕ) :
    cartLt insFn a b ∨ a = b ∨ cartLt insFn b a := by
  unfold cartLt; omega

theorem cartFold_spec (insFn : ℕ → ℕ) (rest : List ℕ) (x : ℕ) :
    let r := rest.foldl (cartStep insFn) x
    r ∈ x :: rest ∧ ∀ y ∈ x :: rest, r = y ∨ cartLt insFn r y := by
  induction rest generalizing x with
  | nil =>
    refine ⟨List.mem_singleton.mpr rfl, fun y hy => ?_⟩
    exact Or.inl (List.mem_singleton.mp hy).symm
  | cons a rs ih =>
    simp only [List.foldl_cons]
    unfold cartStep
    split_ifs with hax
    · have hax' : cartLt insFn a x := hax
      obtain ⟨hmem, hmin⟩ := ih a
      refine ⟨List.mem_cons_of_mem x hmem, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy_rest
      · rcases hmin a (.head _) with heq | hlt
        · exact Or.inr (heq.symm ▸ hax')
        · exact Or.inr (cartLt_trans hlt hax')
      · exact hmin y hy_rest
    · have hxa : x = a ∨ cartLt insFn x a := by
        rcases cartLt_trichotomy insFn a x with h1 | h2 | h3
        · exact absurd h1 hax
        · exact Or.inl h2.symm
        · exact Or.inr h3
      obtain ⟨hmem, hmin⟩ := ih x
      refine ⟨?_, fun y hy => ?_⟩
      · rcases List.mem_cons.mp hmem with heq | hrs
        · change rs.foldl (cartStep insFn) x ∈ x :: a :: rs
          rw [heq]; exact .head _
        · exact .tail _ (.tail _ hrs)
      · rcases List.mem_cons.mp hy with rfl | hy_rest
        · exact hmin y (.head _)
        · rcases List.mem_cons.mp hy_rest with rfl | hy_rs
          · rcases hmin x (.head _) with heq | hrx
            · change rs.foldl (cartStep insFn) x = y ∨
                cartLt insFn (rs.foldl (cartStep insFn) x) y
              rw [heq]; exact hxa
            · rcases hxa with hxy | hlt
              · rw [← hxy]; exact Or.inr hrx
              · exact Or.inr (cartLt_trans hrx hlt)
          · exact hmin y (.tail _ hy_rs)

theorem cartFold_eq_of_min (insFn : ℕ → ℕ) (rest : List ℕ) (x r₀ : ℕ)
    (hr₀ : r₀ ∈ x :: rest) (hmin : ∀ y ∈ x :: rest, y ≠ r₀ → cartLt insFn r₀ y) :
    rest.foldl (cartStep insFn) x = r₀ := by
  obtain ⟨hmem, hle⟩ := cartFold_spec insFn rest x
  rcases hle r₀ hr₀ with heq | hlt
  · exact heq
  · have hne : rest.foldl (cartStep insFn) x ≠ r₀ := by
      intro heq; rw [heq] at hlt; exact cartLt_irrefl insFn r₀ hlt
    exact absurd (cartLt_trans hlt (hmin _ hmem hne)) (cartLt_irrefl insFn _)

theorem filter_length_lt_of_mem_false {xs : List ℕ} (p : ℕ → Bool) {r : ℕ}
    (hr : r ∈ xs) (hp : p r = false) : (xs.filter p).length < xs.length := by
  induction xs with
  | nil => cases hr
  | cons y ys ih =>
    rcases List.mem_cons.mp hr with rfl | hys
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      have hle := List.length_filter_le p ys
      omega
    · have hlt := ih hys
      by_cases hpy : p y = true
      · simp only [List.filter_cons_of_pos hpy, List.length_cons]; omega
      · simp only [List.filter_cons_of_neg hpy, List.length_cons]; omega

theorem cartesianFromSortedGo_fuel_irrel (insFn : ℕ → ℕ) :
    ∀ (n : ℕ) (xs : List ℕ) (f₁ f₂ : ℕ),
      xs.length = n → n ≤ f₁ → n ≤ f₂ →
      cartesianFromSortedGo insFn f₁ xs = cartesianFromSortedGo insFn f₂ xs := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs f₁ f₂ hlen hf₁ hf₂
    cases xs with
    | nil =>
      cases f₁ <;> cases f₂ <;> rfl
    | cons x rest =>
      simp only [List.length_cons] at hlen
      cases f₁ with
      | zero => omega
      | succ f₁' =>
        cases f₂ with
        | zero => omega
        | succ f₂' =>
          simp only [cartesianFromSortedGo]
          set r := rest.foldl (cartStep insFn) x
          have hr_mem : r ∈ x :: rest := (cartFold_spec insFn rest x).1
          have hlt_L : ((x :: rest).filter (· < r)).length < n := by
            rw [← hlen]
            exact filter_length_lt_of_mem_false (· < r) hr_mem (by simp)
          have hlt_R : ((x :: rest).filter (r < ·)).length < n := by
            rw [← hlen]
            exact filter_length_lt_of_mem_false (r < ·) hr_mem (by simp)
          have heq_L := ih _ hlt_L ((x :: rest).filter (· < r)) f₁' f₂' rfl (by omega) (by omega)
          have heq_R := ih _ hlt_R ((x :: rest).filter (r < ·)) f₁' f₂' rfl (by omega) (by omega)
          change BinaryTree.node r (cartesianFromSortedGo insFn f₁' ((x :: rest).filter (· < r)))
              (cartesianFromSortedGo insFn f₁' ((x :: rest).filter (r < ·))) =
            BinaryTree.node r (cartesianFromSortedGo insFn f₂' ((x :: rest).filter (· < r)))
              (cartesianFromSortedGo insFn f₂' ((x :: rest).filter (r < ·)))
          rw [heq_L, heq_R]

theorem pairwise_lt_eq_of_mem_iff {l₁ l₂ : List ℕ}
    (hpw1 : l₁.Pairwise (· < ·)) (hpw2 : l₂.Pairwise (· < ·))
    (hmem : ∀ z, z ∈ l₁ ↔ z ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b bs => exfalso; exact List.not_mem_nil ((hmem b).mpr (.head _))
  | cons a as ih =>
    cases l₂ with
    | nil => exfalso; exact List.not_mem_nil ((hmem a).mp (.head _))
    | cons b bs =>
      rw [List.pairwise_cons] at hpw1 hpw2
      have hab : a = b := by
        have ha_in : a ∈ b :: bs := (hmem a).mp (.head _)
        have hb_in : b ∈ a :: as := (hmem b).mpr (.head _)
        rcases List.mem_cons.mp ha_in with rfl | ha_bs
        · rfl
        · rcases List.mem_cons.mp hb_in with rfl | hb_as
          · rfl
          · exact absurd (lt_trans (hpw2.1 a ha_bs) (hpw1.1 b hb_as)) (lt_irrefl b)
      subst hab
      congr 1
      apply ih hpw1.2 hpw2.2
      intro z
      constructor
      · intro hzas
        have hza : z ≠ a := ne_of_gt (hpw1.1 z hzas)
        rcases List.mem_cons.mp ((hmem z).mp (.tail _ hzas)) with rfl | hzbs
        · exact absurd rfl hza
        · exact hzbs
      · intro hzbs
        have hza : z ≠ a := ne_of_gt (hpw2.1 z hzbs)
        rcases List.mem_cons.mp ((hmem z).mpr (.tail _ hzbs)) with rfl | hzas
        · exact absurd rfl hza
        · exact hzas

def sortedListOfFinset (S : Finset ℕ) : List ℕ :=
  (List.range (S.sup id + 1)).filter (· ∈ S)

theorem sortedListOfFinset_spec (S : Finset ℕ) :
    (sortedListOfFinset S).Pairwise (· < ·) ∧
    ∀ z, z ∈ sortedListOfFinset S ↔ z ∈ S := by
  have hpw_range : ∀ m : ℕ, (List.range m).Pairwise (· < ·) := by
    intro m
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_range]
    exact hij
  refine ⟨(hpw_range _).filter _, fun z => ?_⟩
  unfold sortedListOfFinset
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hz
    have hle : z ≤ S.sup id := Finset.le_sup (f := id) hz
    exact ⟨by omega, hz⟩

theorem cartesianBSTWith_empty (insFn : ℕ → ℕ) :
    cartesianBSTWith insFn ∅ = .nil := by
  have hemp : sortedListOfFinset ∅ = [] := by
    apply pairwise_lt_eq_of_mem_iff (sortedListOfFinset_spec ∅).1 List.Pairwise.nil
    intro z
    rw [(sortedListOfFinset_spec ∅).2]
    simp
  change cartesianFromSortedGo insFn (sortedListOfFinset ∅).length (sortedListOfFinset ∅) = .nil
  rw [hemp]
  rfl

theorem cartesianBSTWith_step_of_min (insFn : ℕ → ℕ) (S : Finset ℕ) (r : ℕ)
    (hr : r ∈ S) (hmin : ∀ y ∈ S, y ≠ r → cartLt insFn r y) :
    cartesianBSTWith insFn S =
      .node r (cartesianBSTWith insFn (S.filter (· < r)))
              (cartesianBSTWith insFn (S.filter (r < ·))) := by
  obtain ⟨hpw, hmem⟩ := sortedListOfFinset_spec S
  have hr_xs : r ∈ sortedListOfFinset S := (hmem r).mpr hr
  cases hxs : sortedListOfFinset S with
  | nil => rw [hxs] at hr_xs; cases hr_xs
  | cons x rest =>
    have hmem' : ∀ z, z ∈ x :: rest ↔ z ∈ S := by intro z; rw [← hxs]; exact hmem z
    have hpw' : (x :: rest).Pairwise (· < ·) := hxs ▸ hpw
    have hr_cons : r ∈ x :: rest := hxs ▸ hr_xs
    have hr_fold : rest.foldl (cartStep insFn) x = r :=
      cartFold_eq_of_min insFn rest x r hr_cons
        (fun y hy hne => hmin y ((hmem' y).mp hy) hne)
    change cartesianFromSortedGo insFn (sortedListOfFinset S).length (sortedListOfFinset S) = _
    rw [hxs]
    simp only [List.length_cons, cartesianFromSortedGo]
    change BinaryTree.node (rest.foldl (cartStep insFn) x)
        (cartesianFromSortedGo insFn rest.length ((x :: rest).filter (· < rest.foldl (cartStep insFn) x)))
        (cartesianFromSortedGo insFn rest.length ((x :: rest).filter (rest.foldl (cartStep insFn) x < ·))) = _
    rw [hr_fold]
    have hL_eq : (x :: rest).filter (· < r) = sortedListOfFinset (S.filter (· < r)) := by
      apply pairwise_lt_eq_of_mem_iff (hpw'.filter _) (sortedListOfFinset_spec _).1
      intro z
      rw [List.mem_filter, decide_eq_true_eq, hmem', (sortedListOfFinset_spec _).2, Finset.mem_filter]
    have hR_eq : (x :: rest).filter (r < ·) = sortedListOfFinset (S.filter (r < ·)) := by
      apply pairwise_lt_eq_of_mem_iff (hpw'.filter _) (sortedListOfFinset_spec _).1
      intro z
      rw [List.mem_filter, decide_eq_true_eq, hmem', (sortedListOfFinset_spec _).2, Finset.mem_filter]
    have hL_lt : ((x :: rest).filter (· < r)).length < (x :: rest).length :=
      filter_length_lt_of_mem_false (· < r) hr_cons (by simp)
    have hR_lt : ((x :: rest).filter (r < ·)).length < (x :: rest).length :=
      filter_length_lt_of_mem_false (r < ·) hr_cons (by simp)
    simp only [List.length_cons] at hL_lt hR_lt
    have hL_tree : cartesianFromSortedGo insFn rest.length ((x :: rest).filter (· < r)) =
        cartesianBSTWith insFn (S.filter (· < r)) := by
      change _ = cartesianFromSortedGo insFn (sortedListOfFinset (S.filter (· < r))).length
        (sortedListOfFinset (S.filter (· < r)))
      rw [← hL_eq]
      exact cartesianFromSortedGo_fuel_irrel insFn _ _ _ _ rfl (by omega) le_rfl
    have hR_tree : cartesianFromSortedGo insFn rest.length ((x :: rest).filter (r < ·)) =
        cartesianBSTWith insFn (S.filter (r < ·)) := by
      change _ = cartesianFromSortedGo insFn (sortedListOfFinset (S.filter (r < ·))).length
        (sortedListOfFinset (S.filter (r < ·)))
      rw [← hR_eq]
      exact cartesianFromSortedGo_fuel_irrel insFn _ _ _ _ rfl (by omega) le_rfl
    rw [hL_tree, hR_tree]

theorem cartesianBSTWith_isBST_and_keys (insFn : ℕ → ℕ) (S : Finset ℕ) :
    (cartesianBSTWith insFn S).IsBST ∧ keyFinset (cartesianBSTWith insFn S) = S := by
  suffices ∀ n : ℕ, ∀ S : Finset ℕ, S.card = n →
      (cartesianBSTWith insFn S).IsBST ∧ keyFinset (cartesianBSTWith insFn S) = S from
    this S.card S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hcard
    by_cases hemp : S = ∅
    · subst hemp
      rw [cartesianBSTWith_empty]
      exact ⟨IsBSTAux.nil none none, rfl⟩
    · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      obtain ⟨_, hmem⟩ := sortedListOfFinset_spec S
      have hw_xs : w ∈ sortedListOfFinset S := (hmem w).mpr hw
      cases hxs : sortedListOfFinset S with
      | nil => rw [hxs] at hw_xs; cases hw_xs
      | cons x rest =>
        set r := rest.foldl (cartStep insFn) x
        obtain ⟨hr_cons, hr_min_cons⟩ := cartFold_spec insFn rest x
        have hr_S : r ∈ S := (hmem r).mp (hxs ▸ hr_cons)
        have hr_min : ∀ y ∈ S, y ≠ r → cartLt insFn r y := by
          intro y hy hne
          have hy_cons : y ∈ x :: rest := hxs ▸ (hmem y).mpr hy
          rcases hr_min_cons y hy_cons with rfl | hlt
          · exact absurd rfl hne
          · exact hlt
        rw [cartesianBSTWith_step_of_min insFn S r hr_S hr_min]
        have hcard_L : (S.filter (· < r)).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card
            ⟨Finset.filter_subset _ _, fun hsub => (Finset.mem_filter.mp (hsub hr_S)).2.false⟩
        have hcard_R : (S.filter (r < ·)).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card
            ⟨Finset.filter_subset _ _, fun hsub => (Finset.mem_filter.mp (hsub hr_S)).2.false⟩
        obtain ⟨hbst_L, hkeys_L⟩ := ih _ hcard_L (S.filter (· < r)) rfl
        obtain ⟨hbst_R, hkeys_R⟩ := ih _ hcard_R (S.filter (r < ·)) rfl
        refine ⟨(isBST_node_iff r _ _).mpr ⟨hbst_L, hbst_R, ?_, ?_⟩, ?_⟩
        · intro z hz
          have hz' : z ∈ S.filter (· < r) := hkeys_L ▸ (mem_iff_mem_keyFinset _ z).mp hz
          exact (Finset.mem_filter.mp hz').2
        · intro z hz
          have hz' : z ∈ S.filter (r < ·) := hkeys_R ▸ (mem_iff_mem_keyFinset _ z).mp hz
          exact (Finset.mem_filter.mp hz').2
        · simp only [keyFinset, hkeys_L, hkeys_R]
          ext z
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (rfl | ⟨hz, _⟩ | ⟨hz, _⟩) <;> assumption
          · intro hz
            rcases lt_trichotomy z r with hlt | rfl | hgt
            · exact Or.inr (Or.inl ⟨hz, hlt⟩)
            · exact Or.inl rfl
            · exact Or.inr (Or.inr ⟨hz, hgt⟩)

def slotSet (U : Finset ℕ) (lo hi : Option ℕ) : Finset ℕ :=
  U.filter (fun u => lo.elim true (· < u) ∧ hi.elim true (u < ·))

def inSlot (lo hi : Option ℕ) (v : ℕ) : Prop :=
  lo.elim True (· < v) ∧ hi.elim True (v < ·)

theorem mem_slotSet_iff (U : Finset ℕ) (lo hi : Option ℕ) (u : ℕ) :
    u ∈ slotSet U lo hi ↔ u ∈ U ∧ inSlot lo hi u := by
  cases lo <;> cases hi <;> simp [slotSet, inSlot]

theorem fillCartesianSlots_isBST_and_keys (insFn : ℕ → ℕ) (U : Finset ℕ)
    (lo hi : Option ℕ) (t : BinaryTree ℕ)
    (ht : t.IsBST) (hdisj : Disjoint (keyFinset t) U) (hslot : ∀ v ∈ t, inSlot lo hi v) :
    (fillCartesianSlots insFn U lo hi t).IsBST ∧
    keyFinset (fillCartesianSlots insFn U lo hi t) = keyFinset t ∪ slotSet U lo hi := by
  induction t generalizing lo hi with
  | nil =>
    obtain ⟨hbst, hkeys⟩ := cartesianBSTWith_isBST_and_keys insFn (slotSet U lo hi)
    exact ⟨hbst, hkeys.trans (Finset.empty_union _).symm⟩
  | node k l r ihl ihr =>
    obtain ⟨hl_bst, hr_bst, hlt, hgt⟩ := (isBST_node_iff k l r).mp ht
    have hk_slot : inSlot lo hi k := hslot k .here
    have hk_not_U : k ∉ U :=
      Finset.disjoint_left.mp hdisj ((mem_iff_mem_keyFinset (.node k l r) k).mp .here)
    have hdisj_l : Disjoint (keyFinset l) U :=
      Finset.disjoint_of_subset_left
        (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)) hdisj
    have hdisj_r : Disjoint (keyFinset r) U :=
      Finset.disjoint_of_subset_left
        (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz)) hdisj
    have hslot_l : ∀ v ∈ l, inSlot lo (some k) v := fun v hv =>
      ⟨(hslot v (.left hv)).1, hlt v hv⟩
    have hslot_r : ∀ v ∈ r, inSlot (some k) hi v := fun v hv =>
      ⟨hgt v hv, (hslot v (.right hv)).2⟩
    obtain ⟨hL_bst, hL_keys⟩ := ihl lo (some k) hl_bst hdisj_l hslot_l
    obtain ⟨hR_bst, hR_keys⟩ := ihr (some k) hi hr_bst hdisj_r hslot_r
    simp only [fillCartesianSlots]
    refine ⟨(isBST_node_iff k _ _).mpr ⟨hL_bst, hR_bst, ?_, ?_⟩, ?_⟩
    · intro z hz
      have hz_kf : z ∈ keyFinset l ∪ slotSet U lo (some k) :=
        hL_keys ▸ (mem_iff_mem_keyFinset _ z).mp hz
      rcases Finset.mem_union.mp hz_kf with hzl | hzs
      · exact hlt z ((mem_iff_mem_keyFinset l z).mpr hzl)
      · exact ((mem_slotSet_iff U lo (some k) z).mp hzs).2.2
    · intro z hz
      have hz_kf : z ∈ keyFinset r ∪ slotSet U (some k) hi :=
        hR_keys ▸ (mem_iff_mem_keyFinset _ z).mp hz
      rcases Finset.mem_union.mp hz_kf with hzr | hzs
      · exact hgt z ((mem_iff_mem_keyFinset r z).mpr hzr)
      · exact ((mem_slotSet_iff U (some k) hi z).mp hzs).2.1
    · simp only [keyFinset, hL_keys, hR_keys]
      ext z
      simp only [Finset.mem_insert, Finset.mem_union, mem_slotSet_iff]
      constructor
      · rintro (rfl | ((hzl | ⟨hzU, hlo, hzk⟩) | (hzr | ⟨hzU, hkz, hhi⟩)))
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr (Or.inl hzl))
        · refine Or.inr ⟨hzU, hlo, ?_⟩
          cases hi with
          | none => trivial
          | some b => exact lt_trans hzk hk_slot.2
        · exact Or.inl (Or.inr (Or.inr hzr))
        · refine Or.inr ⟨hzU, ?_, hhi⟩
          cases lo with
          | none => trivial
          | some a => exact lt_trans hk_slot.1 hkz
      · rintro ((rfl | (hzl | hzr)) | ⟨hzU, hlo, hhi⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inl hzl))
        · exact Or.inr (Or.inr (Or.inl hzr))
        · have hne : z ≠ k := fun h => hk_not_U (h ▸ hzU)
          rcases lt_or_gt_of_ne hne with hzk | hkz
          · exact Or.inr (Or.inl (Or.inr ⟨hzU, hlo, hzk⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨hzU, hkz, hhi⟩))

theorem cartesianExt_def {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ) :
    cartesianExt proc τ =
      fillCartesianSlots proc.insStep (uSetAt proc τ) none none (proc.treeAt τ) :=
  rfl

theorem cartesianExt_isBST_and_keys {P : ℕ} (proc : FoldedPopProcess P)
    {τ : ℕ} (hτ : τ ≤ proc.steps.length) :
    (cartesianExt proc τ).IsBST ∧
    keyFinset (cartesianExt proc τ) = Finset.Icc (s0At proc τ + 1) P := by
  rw [cartesianExt_def]
  obtain ⟨ht_bst, _⟩ := (proc_tree_bst_and_step_keys proc).1 τ hτ
  obtain ⟨hsub, _⟩ := (uSetAt_props proc).1 τ hτ
  have hdisj : Disjoint (keyFinset (proc.treeAt τ)) (uSetAt proc τ) :=
    Finset.disjoint_sdiff
  obtain ⟨hbst, hkeys⟩ := fillCartesianSlots_isBST_and_keys proc.insStep (uSetAt proc τ)
    none none (proc.treeAt τ) ht_bst hdisj (fun _ _ => ⟨trivial, trivial⟩)
  refine ⟨hbst, ?_⟩
  rw [hkeys]
  have hslot_all : slotSet (uSetAt proc τ) none none = uSetAt proc τ := by
    ext z; simp [mem_slotSet_iff, inSlot]
  rw [hslot_all]
  unfold uSetAt
  exact Finset.union_sdiff_of_subset hsub

theorem fillCartesianSlots_lo_some_eq_none (insFn : ℕ → ℕ) (U : Finset ℕ) (s : ℕ)
    (hgt : ∀ u ∈ U, s < u) (hi : Option ℕ) (t : BinaryTree ℕ) :
    fillCartesianSlots insFn U (some s) hi t = fillCartesianSlots insFn U none hi t := by
  induction t generalizing hi with
  | nil =>
    change cartesianBSTWith insFn (slotSet U (some s) hi) =
      cartesianBSTWith insFn (slotSet U none hi)
    have hset : slotSet U (some s) hi = slotSet U none hi := by
      ext u
      rw [mem_slotSet_iff, mem_slotSet_iff]
      simp only [inSlot, Option.elim, true_and]
      exact ⟨fun ⟨hu, _, hhi⟩ => ⟨hu, hhi⟩, fun ⟨hu, hhi⟩ => ⟨hu, hgt u hu, hhi⟩⟩
    rw [hset]
  | node k l r ihl _ =>
    simp only [fillCartesianSlots, ihl (some k)]

theorem fillCartesianSlots_pop_spine_min_splice (insFn : ℕ → ℕ) (U : Finset ℕ)
    {s : ℕ} (hgt : ∀ u ∈ U, s < u) (hi : Option ℕ) {t : BinaryTree ℕ}
    (ht : t.IsBST) (hmin : t.minKey? = some s) :
    leftSpine (fillCartesianSlots insFn U none hi t) = leftSpine t ∧
    (fillCartesianSlots insFn U none hi t).minKey? = some s ∧
    spliceMin (fillCartesianSlots insFn U none hi t) =
      fillCartesianSlots insFn U none hi (spliceMin t) := by
  induction t generalizing hi with
  | nil => simp [BinaryTree.minKey?] at hmin
  | node k l r ihl _ =>
    obtain ⟨hl_bst, _, _, _⟩ := (isBST_node_iff k l r).mp ht
    cases l with
    | nil =>
      simp only [BinaryTree.minKey?, Option.some.injEq] at hmin
      subst hmin
      have hslot_empty : slotSet U none (some k) = ∅ := by
        ext u
        rw [mem_slotSet_iff]
        simp only [inSlot, Option.elim, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hu, huk⟩
        exact absurd (lt_trans (hgt u hu) huk) (lt_irrefl _)
      have hL_nil : fillCartesianSlots insFn U none (some k) .nil = .nil := by
        change cartesianBSTWith insFn (slotSet U none (some k)) = .nil
        rw [hslot_empty, cartesianBSTWith_empty]
      have hout : fillCartesianSlots insFn U none hi (.node k .nil r) =
          .node k .nil (fillCartesianSlots insFn U (some k) hi r) := by
        change BinaryTree.node k (fillCartesianSlots insFn U none (some k) .nil)
          (fillCartesianSlots insFn U (some k) hi r) = _
        rw [hL_nil]
      rw [hout]
      exact ⟨rfl, rfl, fillCartesianSlots_lo_some_eq_none insFn U k hgt hi r⟩
    | node lk ll lr =>
      have hmin_l : (BinaryTree.node lk ll lr).minKey? = some s := by
        rwa [minKey?_node_of_ne_nil k _ r (by simp)] at hmin
      obtain ⟨hls_l, hmin_fill_l, hsp_l⟩ := ihl (some k) hl_bst hmin_l
      have hfill_l_ne : fillCartesianSlots insFn U none (some k) (.node lk ll lr) ≠ .nil := by
        simp [fillCartesianSlots]
      have hout : fillCartesianSlots insFn U none hi (.node k (.node lk ll lr) r) =
          .node k (fillCartesianSlots insFn U none (some k) (.node lk ll lr))
                  (fillCartesianSlots insFn U (some k) hi r) := rfl
      rw [hout]
      refine ⟨?_, ?_, ?_⟩
      · simp only [leftSpine, hls_l]
      · rw [minKey?_node_of_ne_nil k _ _ hfill_l_ne]
        exact hmin_fill_l
      · have hsp_node : ∀ (a : ℕ) (L R : BinaryTree ℕ), L ≠ .nil →
            spliceMin (.node a L R) = .node a (spliceMin L) R := by
          intro a L R hL
          cases L with
          | nil => exact absurd rfl hL
          | node _ _ _ => rfl
        rw [hsp_node k _ _ hfill_l_ne, hsp_l]
        rfl

theorem fillCartesianSlots_rotateRightEdge (insFn : ℕ → ℕ) (U : Finset ℕ)
    (lo hi : Option ℕ) {t : BinaryTree ℕ} (ht : t.IsBST) {u v : ℕ}
    (hedge : IsRightRotEdge t u v) :
    IsRightRotEdge (fillCartesianSlots insFn U lo hi t) u v ∧
    fillCartesianSlots insFn U lo hi (rotateRightEdge t u v) =
      rotateRightEdge (fillCartesianSlots insFn U lo hi t) u v := by
  rcases hedge with ⟨A, B, C, hv_mem, hsub⟩
  induction t generalizing lo hi with
  | nil => cases hv_mem
  | node k l r ihl ihr =>
    obtain ⟨hl_bst, hr_bst, hlt, hgt⟩ := (isBST_node_iff k l r).mp ht
    rcases lt_trichotomy v k with hvk | rfl | hkv
    · have hv_l : v ∈ l := by
        rcases hv_mem with _ | hvl | hvr
        · exact absurd rfl (ne_of_lt hvk)
        · exact hvl
        · exact absurd (lt_trans hvk (hgt v hvr)) (lt_irrefl v)
      simp only [subtreeAtKey, hvk, ↓reduceIte] at hsub
      obtain ⟨⟨A', B', C', hv_fill_l, hsub_fill_l⟩, hrot_l⟩ :=
        ihl lo (some k) hl_bst hv_l hsub
      refine ⟨⟨A', B', C', .left hv_fill_l, ?_⟩, ?_⟩
      · simp [fillCartesianSlots, subtreeAtKey, hvk, hsub_fill_l]
      · simp [fillCartesianSlots, rotateRightEdge, hvk, hrot_l]
    · simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
      injection hsub with _ hl_eq hr_eq
      subst hl_eq hr_eq
      refine ⟨⟨fillCartesianSlots insFn U lo (some u) A,
               fillCartesianSlots insFn U (some u) (some v) B,
               fillCartesianSlots insFn U (some v) hi r,
               .here, by simp [fillCartesianSlots, subtreeAtKey]⟩, ?_⟩
      simp [fillCartesianSlots, rotateRightEdge]
    · have hv_r : v ∈ r := by
        rcases hv_mem with _ | hvl | hvr
        · exact absurd rfl (ne_of_gt hkv)
        · exact absurd (lt_trans (hlt v hvl) hkv) (lt_irrefl v)
        · exact hvr
      have hnot : ¬ v < k := not_lt_of_gt hkv
      simp only [subtreeAtKey, hnot, hkv, ↓reduceIte] at hsub
      obtain ⟨⟨A', B', C', hv_fill_r, hsub_fill_r⟩, hrot_r⟩ :=
        ihr (some k) hi hr_bst hv_r hsub
      refine ⟨⟨A', B', C', .right hv_fill_r, ?_⟩, ?_⟩
      · simp [fillCartesianSlots, subtreeAtKey, hnot, hkv, hsub_fill_r]
      · simp [fillCartesianSlots, rotateRightEdge, hnot, hkv, hrot_r]

theorem fillCartesianSlots_foldl_adjacentPairs (insFn : ℕ → ℕ) (U : Finset ℕ) :
    ∀ (n : ℕ) (ys : List ℕ) (t : BinaryTree ℕ) (pref suff : List ℕ) (lo hi : Option ℕ),
      t.IsBST → leftSpine t = pref ++ ys ++ suff →
      fillCartesianSlots insFn U lo hi
          (((adjacentPairs ys).take n).foldl (fun acc p => rotateRightEdge acc p.1 p.2) t) =
        ((adjacentPairs ys).take n).foldl (fun acc p => rotateRightEdge acc p.1 p.2)
          (fillCartesianSlots insFn U lo hi t)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | _ + 1, [], _, _, _, _, _, _, _ => rfl
  | _ + 1, [_], _, _, _, _, _, _, _ => rfl
  | n + 1, a :: b :: ys, t, pref, suff, lo, hi, ht, hls => by
    have hls' : leftSpine t = pref ++ a :: b :: (ys ++ suff) := by
      simpa [List.append_assoc] using hls
    have hget0 : (leftSpine t)[pref.length]? = some a := by
      rw [hls']; exact getElem?_append_cons_zero pref a _
    have hget1 : (leftSpine t)[pref.length + 1]? = some b := by
      rw [hls']; exact getElem?_append_cons_one pref a b _
    obtain ⟨_, hedge, hrem⟩ := leftSpine_adj_of_getElem? ht hget0 hget1
    have hrot_eq := (fillCartesianSlots_rotateRightEdge insFn U lo hi ht hedge).2
    have ht₁ : (rotateRightEdge t a b).IsBST := rotateRightEdge_isBST ht a b
    have hls₁ : leftSpine (rotateRightEdge t a b) = (pref ++ [a]) ++ ys ++ suff := by
      rw [hrem, hls', removeAt_append_two]
      simp [List.append_assoc]
    simp only [adjacentPairs, List.take_succ_cons, List.foldl_cons]
    rw [fillCartesianSlots_foldl_adjacentPairs insFn U n ys (rotateRightEdge t a b)
      (pref ++ [a]) suff lo hi ht₁ hls₁, hrot_eq]

theorem fillCartesianSlots_erase_of_lt (insFn : ℕ → ℕ) (U : Finset ℕ)
    {w k : ℕ} (hwk : w < k) (hi : Option ℕ) {R : BinaryTree ℕ} (hR : ∀ z ∈ R, w < z) :
    fillCartesianSlots insFn (U.erase w) (some k) hi R =
      fillCartesianSlots insFn U (some k) hi R := by
  induction R generalizing k hi with
  | nil =>
    change cartesianBSTWith insFn (slotSet (U.erase w) (some k) hi) =
      cartesianBSTWith insFn (slotSet U (some k) hi)
    have hset : slotSet (U.erase w) (some k) hi = slotSet U (some k) hi := by
      ext u
      rw [mem_slotSet_iff, mem_slotSet_iff, Finset.mem_erase]
      simp only [inSlot, Option.elim]
      exact ⟨fun ⟨⟨_, hu⟩, hku, hhi⟩ => ⟨hu, hku, hhi⟩,
             fun ⟨hu, hku, hhi⟩ => ⟨⟨ne_of_gt (lt_trans hwk hku), hu⟩, hku, hhi⟩⟩
    rw [hset]
  | node kz lz rz ihl ihr =>
    simp only [fillCartesianSlots]
    rw [ihl hwk (some kz) (fun z hz => hR z (.left hz)),
        ihr (hR kz .here) hi (fun z hz => hR z (.right hz))]

theorem fillCartesianSlots_push_left (insFn : ℕ → ℕ) (U : Finset ℕ) {w : ℕ}
    (hw : w ∈ U) (hmin : ∀ y ∈ U, y ≠ w → cartLt insFn w y)
    (hi : Option ℕ) (hw_hi : hi.elim True (w < ·))
    (L : BinaryTree ℕ) (hL_bst : L.IsBST) (hdisj : Disjoint (keyFinset L) U)
    (hL_bounds : ∀ z ∈ L, w < z ∧ hi.elim True (z < ·)) :
    RightRotReachable
      (fillCartesianSlots insFn U none hi L)
      (.node w (cartesianBSTWith insFn (slotSet (U.erase w) none (some w)))
               (fillCartesianSlots insFn (U.erase w) (some w) hi L)) := by
  induction L generalizing hi with
  | nil =>
    simp only [fillCartesianSlots]
    have hw_slot : w ∈ slotSet U none hi :=
      (mem_slotSet_iff U none hi w).mpr ⟨hw, trivial, hw_hi⟩
    have hmin_slot : ∀ y ∈ slotSet U none hi, y ≠ w → cartLt insFn w y := fun y hy hne =>
      hmin y ((mem_slotSet_iff U none hi y).mp hy).1 hne
    have hstep := cartesianBSTWith_step_of_min insFn (slotSet U none hi) w hw_slot hmin_slot
    have hL_set : (slotSet U none hi).filter (· < w) = slotSet (U.erase w) none (some w) := by
      ext u
      simp only [Finset.mem_filter, mem_slotSet_iff, Finset.mem_erase, inSlot, Option.elim,
        true_and]
      constructor
      · rintro ⟨⟨hu, _⟩, huw⟩; exact ⟨⟨ne_of_lt huw, hu⟩, huw⟩
      · rintro ⟨⟨_, hu⟩, huw⟩
        refine ⟨⟨hu, ?_⟩, huw⟩
        cases hi with
        | none => trivial
        | some b => exact lt_trans huw hw_hi
    have hR_set : (slotSet U none hi).filter (w < ·) = slotSet (U.erase w) (some w) hi := by
      ext u
      rw [Finset.mem_filter, mem_slotSet_iff, mem_slotSet_iff, Finset.mem_erase]
      simp only [inSlot, Option.elim, true_and]
      exact ⟨fun ⟨⟨hu, hhi⟩, hwu⟩ => ⟨⟨ne_of_gt hwu, hu⟩, hwu, hhi⟩,
             fun ⟨⟨_, hu⟩, hwu, hhi⟩ => ⟨⟨hu, hhi⟩, hwu⟩⟩
    change RightRotReachable (cartesianBSTWith insFn (slotSet U none hi))
      (.node w (cartesianBSTWith insFn (slotSet (U.erase w) none (some w)))
               (cartesianBSTWith insFn (slotSet (U.erase w) (some w) hi)))
    rw [hstep, hL_set, hR_set]
    exact .refl
  | node k Ll Lr ihl _ =>
    obtain ⟨hLl_bst, _, hlt, _⟩ := (isBST_node_iff k Ll Lr).mp hL_bst
    have hwk : w < k := (hL_bounds k .here).1
    have hdisj_l : Disjoint (keyFinset Ll) U :=
      Finset.disjoint_of_subset_left
        (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)) hdisj
    have hLl_bounds : ∀ z ∈ Ll, w < z ∧ (some k : Option ℕ).elim True (z < ·) := fun z hz =>
      ⟨(hL_bounds z (.left hz)).1, hlt z hz⟩
    have hreach_l := ihl (some k) hwk hLl_bst hdisj_l hLl_bounds
    obtain ⟨hL_fill_bst, hL_fill_keys⟩ := fillCartesianSlots_isBST_and_keys insFn U
      none (some k) Ll hLl_bst hdisj_l (fun z hz => ⟨trivial, hlt z hz⟩)
    have hL_fill_lt_k : ∀ z ∈ fillCartesianSlots insFn U none (some k) Ll, z < k := by
      intro z hz
      have hzkf : z ∈ keyFinset Ll ∪ slotSet U none (some k) :=
        hL_fill_keys ▸ (mem_iff_mem_keyFinset _ z).mp hz
      rcases Finset.mem_union.mp hzkf with hzl | hzs
      · exact hlt z ((mem_iff_mem_keyFinset Ll z).mpr hzl)
      · exact ((mem_slotSet_iff U none (some k) z).mp hzs).2.2
    have h1 := rightRotReachable_node_left
      (r := fillCartesianSlots insFn U (some k) hi Lr)
      hL_fill_bst hL_fill_lt_k hreach_l
    have hLr_eq : fillCartesianSlots insFn U (some k) hi Lr =
        fillCartesianSlots insFn (U.erase w) (some k) hi Lr :=
      (fillCartesianSlots_erase_of_lt insFn U hwk hi (fun z hz => (hL_bounds z (.right hz)).1)).symm
    rw [hLr_eq] at h1
    set Aw := cartesianBSTWith insFn (slotSet (U.erase w) none (some w))
    set Bw := fillCartesianSlots insFn (U.erase w) (some w) (some k) Ll
    set Ck := fillCartesianSlots insFn (U.erase w) (some k) hi Lr
    have hedge : IsRightRotEdge (.node k (.node w Aw Bw) Ck) w k :=
      ⟨Aw, Bw, Ck, .here, by simp [subtreeAtKey]⟩
    have hrot : rotateRightEdge (.node k (.node w Aw Bw) Ck) w k =
        .node w Aw (.node k Bw Ck) := by
      simp [rotateRightEdge]
    have hstep_end : RightRotReachable (.node k (fillCartesianSlots insFn U none (some k) Ll) Ck)
        (.node w Aw (.node k Bw Ck)) :=
      h1.tail ⟨w, k, hwk, hedge, hrot.symm⟩
    dsimp only [fillCartesianSlots]
    rw [hLr_eq]
    exact hstep_end

theorem fillCartesianSlots_push_modifyLeftAt (insFn : ℕ → ℕ) (U : Finset ℕ) {w b : ℕ}
    (hw : w ∈ U) (hmin : ∀ y ∈ U, y ≠ w → cartLt insFn w y)
    (hi : Option ℕ) {t : BinaryTree ℕ}
    (ht : t.IsBST) (hdisj : Disjoint (keyFinset t) U)
    (hb : b ∈ leftSpine t) (hbounds : ∀ z ∈ t, w < z ∧ hi.elim True (z < ·)) :
    RightRotReachable
      (fillCartesianSlots insFn U none hi t)
      (fillCartesianSlots insFn (U.erase w) none hi
        (modifyLeftAt t b (fun L1 => .node w .nil L1))) := by
  induction t generalizing hi with
  | nil => simp [leftSpine] at hb
  | node k l r ihl _ =>
    obtain ⟨hl_bst, _, hlt, _⟩ := (isBST_node_iff k l r).mp ht
    have hwk : w < k := (hbounds k .here).1
    have hdisj_l : Disjoint (keyFinset l) U :=
      Finset.disjoint_of_subset_left
        (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)) hdisj
    obtain ⟨hl_fill_bst, hl_fill_keys⟩ := fillCartesianSlots_isBST_and_keys insFn U
      none (some k) l hl_bst hdisj_l (fun z hz => ⟨trivial, hlt z hz⟩)
    have hl_fill_lt_k : ∀ z ∈ fillCartesianSlots insFn U none (some k) l, z < k := by
      intro z hz
      have hzkf : z ∈ keyFinset l ∪ slotSet U none (some k) :=
        hl_fill_keys ▸ (mem_iff_mem_keyFinset _ z).mp hz
      rcases Finset.mem_union.mp hzkf with hzl | hzs
      · exact hlt z ((mem_iff_mem_keyFinset l z).mpr hzl)
      · exact ((mem_slotSet_iff U none (some k) z).mp hzs).2.2
    have hr_eq : fillCartesianSlots insFn U (some k) hi r =
        fillCartesianSlots insFn (U.erase w) (some k) hi r :=
      (fillCartesianSlots_erase_of_lt insFn U hwk hi (fun z hz => (hbounds z (.right hz)).1)).symm
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hb
    rcases hb with hbl | rfl
    · have hbk : b < k := hlt b (mem_of_mem_leftSpine hbl)
      have hreach_l := ihl (some k) hl_bst hdisj_l hbl
        (fun z hz => ⟨(hbounds z (.left hz)).1, hlt z hz⟩)
      simp only [modifyLeftAt, hbk, ↓reduceIte, fillCartesianSlots]
      rw [hr_eq]
      exact rightRotReachable_node_left hl_fill_bst hl_fill_lt_k hreach_l
    · simp only [modifyLeftAt, lt_irrefl, ↓reduceIte, fillCartesianSlots]
      rw [hr_eq]
      have hreach_l := fillCartesianSlots_push_left insFn U hw hmin (some b) hwk
        l hl_bst hdisj_l (fun z hz => ⟨(hbounds z (.left hz)).1, hlt z hz⟩)
      have hslot_eq : cartesianBSTWith insFn (slotSet (U.erase w) none (some w)) =
          fillCartesianSlots insFn (U.erase w) none (some w) .nil := rfl
      rw [hslot_eq] at hreach_l
      exact rightRotReachable_node_left hl_fill_bst hl_fill_lt_k hreach_l

theorem cartesianExt_step_laws {P : ℕ} (proc : FoldedPopProcess P)
    {τ : ℕ} (hτ : τ < proc.steps.length) :
    match proc.steps[τ]'hτ with
    | .push _ =>
      RightRotReachable (cartesianExt proc τ) (cartesianExt proc (τ + 1))
    | .shift =>
      cartesianExt proc (τ + 1) = cartesianExt proc τ
    | .upperRot u v =>
      u < v ∧
      IsRightRotEdge (cartesianExt proc τ) u v ∧
      cartesianExt proc (τ + 1) = rotateRightEdge (cartesianExt proc τ) u v
    | .pop s =>
      ∃ b : ℕ,
        proc.b1At τ = some b ∧
        b ∈ leftSpine (proc.treeAt τ) ∧
        leftSpine (cartesianExt proc τ) = leftSpine (proc.treeAt τ) ∧
        (cartesianExt proc τ).minKey? = some s ∧
        let sub := takeThrough (leftSpine (proc.treeAt τ)) b
        let h := (sub.length - 1 - 1) / 2
        let pairs := (adjacentPairs sub.tail).take h
        cartesianExt proc (τ + 1) =
          pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2)
            (spliceMin (cartesianExt proc τ)) ∧
        RightRotReachable (spliceMin (cartesianExt proc τ)) (cartesianExt proc (τ + 1)) := by
  obtain ⟨hval, hst⟩ := proc_step_at proc hτ
  obtain ⟨ht_bst, _⟩ := (proc_tree_bst_and_step_keys proc).1 τ (le_of_lt hτ)
  have hu_step := (uSetAt_props proc).2 τ hτ
  have ht_eq : proc.treeAt (τ + 1) = (FoldedOp.step (proc.stateAt τ) (proc.steps[τ]'hτ)).1 :=
    congrArg Prod.fst hst
  cases hop : proc.steps[τ]'hτ with
  | shift =>
    rw [hop] at hu_step ht_eq
    have ht_same : proc.treeAt (τ + 1) = proc.treeAt τ := by
      cases h2 : (proc.stateAt τ).2 <;> simp only [FoldedOp.step, h2] at ht_eq <;> exact ht_eq
    simp only [cartesianExt_def, hu_step, ht_same]
  | upperRot u v =>
    rw [hop] at hval hu_step ht_eq
    rcases hval with ⟨_, _, _, _, _, _, huv, _, _, _, hedge⟩
    change IsRightRotEdge (proc.treeAt τ) u v at hedge
    have ht_rot : proc.treeAt (τ + 1) = rotateRightEdge (proc.treeAt τ) u v := ht_eq
    obtain ⟨hedge_ext, hrot_ext⟩ := fillCartesianSlots_rotateRightEdge proc.insStep
      (uSetAt proc τ) none none ht_bst hedge
    refine ⟨huv, ?_, ?_⟩
    · rwa [cartesianExt_def]
    · simp only [cartesianExt_def, hu_step, ht_rot, hrot_ext]
  | push w =>
    rw [hop] at hval hu_step ht_eq
    rcases hval with ⟨_, _, hlt_all, hnil_iff, hb_ls⟩
    rcases hu_step with ⟨hw_U, hU_next, hmin_ins⟩
    have hmin_cart : ∀ y ∈ uSetAt proc τ, y ≠ w → cartLt proc.insStep w y := fun y hy hne =>
      Or.inl (hmin_ins y (Finset.mem_erase.mpr ⟨hne, hy⟩))
    have hdisj : Disjoint (keyFinset (proc.treeAt τ)) (uSetAt proc τ) :=
      Finset.disjoint_sdiff
    rw [cartesianExt_def, cartesianExt_def, hU_next]
    cases hb : (proc.stateAt τ).2 with
    | none =>
      have ht_nil : proc.treeAt τ = .nil := hnil_iff.mpr hb
      simp only [FoldedOp.step, hb] at ht_eq
      rw [ht_nil, ht_eq]
      exact fillCartesianSlots_push_left proc.insStep (uSetAt proc τ) hw_U hmin_cart
        none trivial .nil (IsBSTAux.nil none none) (by simp [keyFinset]) (by simp)
    | some b =>
      have hb_in : b ∈ leftSpine (proc.treeAt τ) := hb_ls b hb
      simp only [FoldedOp.step, hb] at ht_eq
      change proc.treeAt (τ + 1) = modifyLeftAt (proc.treeAt τ) b (fun L1 => .node w .nil L1)
        at ht_eq
      rw [ht_eq]
      exact fillCartesianSlots_push_modifyLeftAt proc.insStep (uSetAt proc τ) hw_U hmin_cart
        none ht_bst hdisj hb_in (fun z hz => ⟨hlt_all z hz, trivial⟩)
  | pop s =>
    rw [hop] at hval hu_step ht_eq
    rcases hval with ⟨b, ht_ne, hmin, hb, hb_ls⟩
    rcases hu_step with ⟨hU_next, hs_lt_U⟩
    change (proc.treeAt τ).minKey? = some s at hmin
    have hb_b1 : proc.b1At τ = some b := hb
    change b ∈ leftSpine (proc.treeAt τ) at hb_ls
    obtain ⟨hls_ext, hmin_ext, hsp_ext⟩ := fillCartesianSlots_pop_spine_min_splice
      proc.insStep (uSetAt proc τ) hs_lt_U none ht_bst hmin
    rw [← cartesianExt_def] at hls_ext hmin_ext hsp_ext
    refine ⟨b, hb_b1, hb_ls, hls_ext, hmin_ext, ?_⟩
    dsimp only
    set sub := takeThrough (leftSpine (proc.treeAt τ)) b
    set h := (sub.length - 1 - 1) / 2
    set pairs := (adjacentPairs sub.tail).take h
    have ht_fold : proc.treeAt (τ + 1) =
        pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin (proc.treeAt τ)) := by
      simp only [FoldedOp.step, hb] at ht_eq
      by_cases hm0 : (takeThrough (leftSpine (proc.stateAt τ).1) b).length - 1 = 0
      · simp only [hm0, ↓reduceIte] at ht_eq
        have hh0 : h = 0 := by
          change ((takeThrough (leftSpine (proc.stateAt τ).1) b).length - 1 - 1) / 2 = 0
          omega
        simp only [pairs, hh0, List.take_zero, List.foldl_nil]
        exact ht_eq
      · simp only [hm0, ↓reduceIte] at ht_eq
        exact ht_eq
    obtain ⟨hsp_bst, _⟩ := spliceMin_spec ht_bst hmin
    obtain ⟨hpref_sub, hne_sub, _, _, _, _⟩ := takeThrough_props (leftSpine_pairwise_lt ht_bst) hb_ls
    rcases hpref_sub with ⟨suff_ls, hsuff_eq⟩
    have htail_eq : (leftSpine (proc.treeAt τ)).tail = sub.tail ++ suff_ls := by
      rw [← hsuff_eq]
      dsimp only [sub]
      cases hsub : takeThrough (leftSpine (proc.treeAt τ)) b with
      | nil => exact absurd hsub hne_sub
      | cons hd tl => rfl
    obtain ⟨pref_sp, hls_sp⟩ := leftSpine_spliceMin_suffix (proc.treeAt τ) ht_ne
    have hls_sp' : leftSpine (spliceMin (proc.treeAt τ)) = pref_sp ++ sub.tail ++ suff_ls := by
      rw [hls_sp, htail_eq, List.append_assoc]
    have hcomm := fillCartesianSlots_foldl_adjacentPairs proc.insStep (uSetAt proc τ)
      h sub.tail (spliceMin (proc.treeAt τ)) pref_sp suff_ls none none hsp_bst hls_sp'
    have hext_next : cartesianExt proc (τ + 1) =
        pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin (cartesianExt proc τ)) := by
      rw [cartesianExt_def, hU_next, ht_fold, hcomm, ← hsp_ext]
    obtain ⟨hext_bst, _⟩ := cartesianExt_isBST_and_keys proc (le_of_lt hτ)
    obtain ⟨hsp_ext_bst, _⟩ := spliceMin_spec hext_bst hmin_ext
    have hext_ne : cartesianExt proc τ ≠ .nil := by
      intro hnil; rw [hnil] at hmin_ext; simp [BinaryTree.minKey?] at hmin_ext
    obtain ⟨pref_ext, hls_sp_ext⟩ := leftSpine_spliceMin_suffix (cartesianExt proc τ) hext_ne
    have hls_sp_ext' : leftSpine (spliceMin (cartesianExt proc τ)) =
        pref_ext ++ sub.tail ++ suff_ls := by
      rw [hls_sp_ext, hls_ext, htail_eq, List.append_assoc]
    obtain ⟨hreach_fold, _⟩ := foldl_adjacentPairs_reachable h sub.tail
      (spliceMin (cartesianExt proc τ)) pref_ext suff_ls hsp_ext_bst hls_sp_ext'
    exact ⟨hext_next, hext_next ▸ hreach_fold⟩


/-! ## Section 4: Direct `D = 1` Preorder Summary & `phaseSummaryBST` Projection -/

theorem isLCAClosed_children {α : Type} [LinearOrder α]
    {u : α} {A B : BinaryTree α} {S : Set α}
    (ht : (BinaryTree.node u A B).IsBST) (hLCA : IsLCAClosed (.node u A B) S) :
    IsLCAClosed A S ∧ IsLCAClosed B S := by
  obtain ⟨_, _, hlt, hgt⟩ := (isBST_node_iff u A B).mp ht
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxS hyS z hlca
    have hxu : x < u := hlt x hx
    have hyu : y < u := hlt y hy
    have hlca' : lcaBST (.node u A B) x y = some z := by
      simp [lcaBST, hxu, hyu, hlca]
    exact hLCA x (.left hx) y (.left hy) hxS hyS z hlca'
  · intro x hx y hy hxS hyS z hlca
    have hux : u < x := hgt x hx
    have huy : u < y := hgt y hy
    have hnot : ¬ (x < u ∧ y < u) := fun h => lt_asymm hux h.1
    have hlca' : lcaBST (.node u A B) x y = some z := by
      simp [lcaBST, hnot, hux, huy, hlca]
    exact hLCA x (.right hx) y (.right hy) hxS hyS z hlca'

theorem h_3_1_rightRot (h_3_1 : Ty_lem_3_1) {α : Type} [LinearOrder α]
    {t : BinaryTree α} {S : Set α} (ht : t.IsBST) (hLCA : IsLCAClosed t S)
    {u v : α} (huv : u < v) (hedge : IsRightRotEdge t u v)
    (hLCA' : IsLCAClosed (rotateRightEdge t u v) S) :
    (u ∈ S ∧ v ∈ S →
      IsRightRotEdge (restrictTree t S) u v ∧
      restrictTree (rotateRightEdge t u v) S = rotateRightEdge (restrictTree t S) u v) ∧
    (¬ (u ∈ S ∧ v ∈ S) →
      restrictTree (rotateRightEdge t u v) S = restrictTree t S) := by
  have hsingle : IsSingleRotEdge t u v := Or.inl ⟨huv, hedge⟩
  have hrot_eq : rotateEdge t u v = rotateRightEdge t u v := by
    simp [rotateEdge, huv]
  have hstep := (h_3_1 t S ht hLCA).2.1 u v hsingle
  dsimp only at hstep
  rw [hrot_eq] at hstep
  obtain ⟨hboth, hnot⟩ := hstep hLCA'
  refine ⟨fun hS => ?_, hnot⟩
  obtain ⟨hsingle_S, heq_S⟩ := hboth hS
  have hedge_S : IsRightRotEdge (restrictTree t S) u v := by
    rcases hsingle_S with ⟨_, hr⟩ | ⟨hvu, _⟩
    · exact hr
    · exact absurd hvu (not_lt_of_gt huv)
  have hrot_S : rotateEdge (restrictTree t S) u v = rotateRightEdge (restrictTree t S) u v := by
    simp [rotateEdge, huv]
  rw [hrot_S] at heq_S
  exact ⟨hedge_S, heq_S⟩

theorem h_3_1_rightRot_reachable (h_3_1 : Ty_lem_3_1) {α : Type} [LinearOrder α]
    {t₁ t₂ : BinaryTree α} {S : Set α} (ht₁ : t₁.IsBST)
    (hLCA_all : ∀ t : BinaryTree α, t.IsBST → IsLCAClosed t S)
    (hreach : RightRotReachable t₁ t₂) :
    RightRotReachable (restrictTree t₁ S) (restrictTree t₂ S) := by
  induction hreach with
  | refl => exact .refl
  | tail hprev hstep ih =>
    rcases hstep with ⟨u, v, huv, hedge, rfl⟩
    rename_i mid
    have hmid_bst : mid.IsBST := (rightRotReachable_isBST_and_mem ht₁ hprev).1
    have hnext_bst : (rotateRightEdge mid u v).IsBST := rotateRightEdge_isBST hmid_bst u v
    obtain ⟨hboth, hnot⟩ := h_3_1_rightRot h_3_1 hmid_bst (hLCA_all mid hmid_bst) huv hedge
      (hLCA_all (rotateRightEdge mid u v) hnext_bst)
    by_cases hS : u ∈ S ∧ v ∈ S
    · obtain ⟨hedge_S, heq_S⟩ := hboth hS
      exact ih.tail ⟨u, v, huv, hedge_S, heq_S⟩
    · rw [hnot hS]
      exact ih

theorem restrictTree_eq_nil_iff {α : Type} (t : BinaryTree α) (S : Set α) :
    restrictTree t S = .nil ↔ ∀ x ∈ t, x ∉ S := by
  induction t with
  | nil => simp [restrictTree]
  | node u A B ihA ihB =>
    unfold restrictTree
    by_cases hu : u ∈ S
    · simp only [hu, ↓reduceIte, reduceCtorEq, false_iff, not_forall]
      exact ⟨u, .here, not_not.mpr hu⟩
    · simp only [hu, ↓reduceIte]
      by_cases hB : ∃ b ∈ B, b ∈ S
      · simp only [hB, ↓reduceIte, ihB]
        rcases hB with ⟨b, hb, hbS⟩
        constructor
        · intro hall; exact absurd hbS (hall b hb)
        · intro hall; exfalso; exact hall b (.right hb) hbS
      · simp only [hB, ↓reduceIte, ihA]
        have hB' : ∀ b ∈ B, b ∉ S := fun b hb hbS => hB ⟨b, hb, hbS⟩
        constructor
        · intro hA x hx
          rcases BinaryTree.mem_node_iff.mp hx with rfl | hxA | hxB
          · exact hu
          · exact hA x hxA
          · exact hB' x hxB
        · intro hall x hxA
          exact hall x (.left hxA)

theorem restrictTree_congr_mem {α : Type} (t : BinaryTree α) (S₁ S₂ : Set α)
    (hiff : ∀ x ∈ t, x ∈ S₁ ↔ x ∈ S₂) :
    restrictTree t S₁ = restrictTree t S₂ := by
  induction t with
  | nil => rfl
  | node u A B ihA ihB =>
    have hu : u ∈ S₁ ↔ u ∈ S₂ := hiff u .here
    have hA : restrictTree A S₁ = restrictTree A S₂ :=
      ihA (fun x hx => hiff x (.left hx))
    have hB : restrictTree B S₁ = restrictTree B S₂ :=
      ihB (fun x hx => hiff x (.right hx))
    have hexB : (∃ b ∈ B, b ∈ S₁) ↔ (∃ b ∈ B, b ∈ S₂) :=
      exists_congr (fun b => and_congr_right (fun hb => hiff b (.right hb)))
    unfold restrictTree
    by_cases hu1 : u ∈ S₁
    · have hu2 : u ∈ S₂ := hu.mp hu1
      simp [hu1, hu2, hA, hB]
    · have hu2 : u ∉ S₂ := fun h => hu1 (hu.mpr h)
      by_cases hB1 : ∃ b ∈ B, b ∈ S₁
      · have hB2 : ∃ b ∈ B, b ∈ S₂ := hexB.mp hB1
        simp [hu1, hu2, hB1, hB2, hB]
      · have hB2 : ¬ ∃ b ∈ B, b ∈ S₂ := fun h => hB1 (hexB.mpr h)
        simp [hu1, hu2, hB1, hB2, hA]

theorem restrictTree_restrictTree_of_subset (h_3_1 : Ty_lem_3_1)
    {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST)
    {S₁ S₂ : Set α} (hLCA₁ : IsLCAClosed t S₁) (hsub : S₂ ⊆ S₁) :
    restrictTree (restrictTree t S₁) S₂ = restrictTree t S₂ := by
  induction t with
  | nil => simp [restrictTree]
  | node u A B ihA ihB =>
    obtain ⟨hl_bst, hr_bst, hlt, hgt⟩ := (isBST_node_iff u A B).mp ht
    obtain ⟨hLCA_A, hLCA_B⟩ := isLCAClosed_children ht hLCA₁
    have hmem_B₁ := (h_3_1 B S₁ hr_bst hLCA_B).1.2
    have hexB : (∃ b ∈ restrictTree B S₁, b ∈ S₂) ↔ (∃ b ∈ B, b ∈ S₂) := by
      constructor
      · rintro ⟨b, hb, hbS₂⟩
        exact ⟨b, ((hmem_B₁ b).mp hb).1, hbS₂⟩
      · rintro ⟨b, hb, hbS₂⟩
        exact ⟨b, (hmem_B₁ b).mpr ⟨hb, hsub hbS₂⟩, hbS₂⟩
    by_cases hu₁ : u ∈ S₁
    · have hstep₁ : restrictTree (.node u A B) S₁ =
          .node u (restrictTree A S₁) (restrictTree B S₁) := by
        simp [restrictTree, hu₁]
      rw [hstep₁]
      by_cases hu₂ : u ∈ S₂
      · simp [restrictTree, hu₂, ihA hl_bst hLCA_A, ihB hr_bst hLCA_B]
      · by_cases hB₂ : ∃ b ∈ B, b ∈ S₂
        · have hB₂' : ∃ b ∈ restrictTree B S₁, b ∈ S₂ := hexB.mpr hB₂
          simp [restrictTree, hu₂, hB₂, hB₂', ihB hr_bst hLCA_B]
        · have hB₂' : ¬ ∃ b ∈ restrictTree B S₁, b ∈ S₂ := fun h => hB₂ (hexB.mp h)
          simp [restrictTree, hu₂, hB₂, hB₂', ihA hl_bst hLCA_A]
    · have hu₂ : u ∉ S₂ := fun h => hu₁ (hsub h)
      by_cases hB₁ : ∃ b ∈ B, b ∈ S₁
      · have hstep₁ : restrictTree (.node u A B) S₁ = restrictTree B S₁ := by
          simp [restrictTree, hu₁, hB₁]
        rw [hstep₁, ihB hr_bst hLCA_B]
        by_cases hB₂ : ∃ b ∈ B, b ∈ S₂
        · simp [restrictTree, hu₂, hB₂]
        · have hstep₂ : restrictTree (.node u A B) S₂ = restrictTree A S₂ := by
            simp [restrictTree, hu₂, hB₂]
          rw [hstep₂]
          have hB₂' : ∀ b ∈ B, b ∉ S₂ := fun b hb hbS₂ => hB₂ ⟨b, hb, hbS₂⟩
          have hB_nil : restrictTree B S₂ = .nil :=
            (restrictTree_eq_nil_iff B S₂).mpr hB₂'
          have hA_nil : restrictTree A S₂ = .nil := by
            rw [restrictTree_eq_nil_iff]
            intro a ha haS₂
            rcases hB₁ with ⟨b, hb, hbS₁⟩
            have hau : a < u := hlt a ha
            have hub : u < b := hgt b hb
            have hnot1 : ¬ (a < u ∧ b < u) := fun h => lt_asymm hub h.2
            have hnot2 : ¬ (u < a ∧ u < b) := fun h => lt_asymm hau h.1
            have hlca : lcaBST (.node u A B) a b = some u := by
              simp [lcaBST, hnot1, hnot2]
            exact hu₁ (hLCA₁ a (.left ha) b (.right hb) (hsub haS₂) hbS₁ u hlca)
          rw [hB_nil, hA_nil]
      · have hB₂ : ¬ ∃ b ∈ B, b ∈ S₂ := by
          rintro ⟨b, hb, hbS₂⟩
          exact hB₁ ⟨b, hb, hsub hbS₂⟩
        simp [restrictTree, hu₁, hu₂, hB₁, hB₂, ihA hl_bst hLCA_A]

theorem mem_leftSpine_restrictTree {α : Type} [LinearOrder α]
    {t : BinaryTree α} {S : Set α} (ht : t.IsBST) (hLCA : IsLCAClosed t S)
    {x : α} (hx_ls : x ∈ leftSpine t) (hxS : x ∈ S) :
    x ∈ leftSpine (restrictTree t S) := by
  induction t with
  | nil => simp [leftSpine] at hx_ls
  | node u A B ihA _ =>
    obtain ⟨hl_bst, _, hlt, hgt⟩ := (isBST_node_iff u A B).mp ht
    obtain ⟨hLCA_A, _⟩ := isLCAClosed_children ht hLCA
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx_ls
    by_cases hu : u ∈ S
    · simp only [restrictTree, hu, ↓reduceIte, leftSpine, List.mem_append, List.mem_singleton]
      rcases hx_ls with hxA | rfl
      · exact Or.inl (ihA hl_bst hLCA_A hxA)
      · exact Or.inr rfl
    · have hxA : x ∈ leftSpine A := by
        rcases hx_ls with h | rfl
        · exact h
        · exact absurd hxS hu
      have hnotB : ¬ ∃ b ∈ B, b ∈ S := by
        rintro ⟨b, hb, hbS⟩
        have hx_in_A : x ∈ A := mem_of_mem_leftSpine hxA
        have hxu : x < u := hlt x hx_in_A
        have hub : u < b := hgt b hb
        have hnot1 : ¬ (x < u ∧ b < u) := fun h => lt_asymm hub h.2
        have hnot2 : ¬ (u < x ∧ u < b) := fun h => lt_asymm hxu h.1
        have hlca : lcaBST (.node u A B) x b = some u := by
          simp [lcaBST, hnot1, hnot2]
        exact hu (hLCA x (.left hx_in_A) b (.right hb) hxS hbS u hlca)
      simp only [restrictTree, hu, hnotB, ↓reduceIte]
      exact ihA hl_bst hLCA_A hxA

theorem map_isRightRotEdge_and_rotateRightEdge {α β : Type}
    [LinearOrder α] [LinearOrder β] {t : BinaryTree α} (ht : t.IsBST)
    {f : α → β} (hf : ∀ a ∈ t, ∀ b ∈ t, a < b → f a < f b)
    {u v : α} (huv : u < v) (hedge : IsRightRotEdge t u v) :
    f u < f v ∧
    IsRightRotEdge (t.map f) (f u) (f v) ∧
    (rotateRightEdge t u v).map f = rotateRightEdge (t.map f) (f u) (f v) := by
  obtain ⟨hu_in, hv_in⟩ := mem_of_isRightRotEdge hedge
  have hfuv : f u < f v := hf u hu_in v hv_in huv
  rcases hedge with ⟨L, Q, R, -, hsub⟩
  have haux : ∀ (W : BinaryTree α), W.IsBST →
      (∀ a ∈ W, ∀ b ∈ W, a < b → f a < f b) → v ∈ W →
      subtreeAtKey W v = .node v (.node u L Q) R →
      subtreeAtKey (W.map f) (f v) = .node (f v) (.node (f u) (L.map f) (Q.map f)) (R.map f) ∧
      (rotateRightEdge W u v).map f = rotateRightEdge (W.map f) (f u) (f v) := by
    intro W hW hfW hvW hsubW
    induction W with
    | nil => cases hvW
    | node k l r ihl ihr =>
      obtain ⟨hl_bst, hr_bst, hlt, hgt⟩ := (isBST_node_iff k l r).mp hW
      rcases lt_trichotomy v k with hvk | rfl | hkv
      · have hvl : v ∈ l := by
          rcases BinaryTree.mem_node_iff.mp hvW with rfl | h | h
          · exact absurd rfl (ne_of_lt hvk)
          · exact h
          · exact absurd hvk (not_lt_of_gt (hgt v h))
        have hfvk : f v < f k := hfW v hvW k .here hvk
        simp only [subtreeAtKey, hvk, ↓reduceIte] at hsubW
        obtain ⟨hsub_map, hrot_map⟩ := ihl hl_bst
          (fun a ha b hb => hfW a (.left ha) b (.left hb)) hvl hsubW
        refine ⟨?_, ?_⟩
        · simp [BinaryTree.map, subtreeAtKey, hfvk, hsub_map]
        · simp [BinaryTree.map, rotateRightEdge, hvk, hfvk, hrot_map]
      · simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsubW
        injection hsubW with _ hl_eq hr_eq
        subst hl_eq hr_eq
        refine ⟨?_, ?_⟩
        · simp [BinaryTree.map, subtreeAtKey]
        · simp [BinaryTree.map, rotateRightEdge]
      · have hvr : v ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hvW with rfl | h | h
          · exact absurd rfl (ne_of_gt hkv)
          · exact absurd hkv (not_lt_of_gt (hlt v h))
          · exact h
        have hfkv : f k < f v := hfW k .here v hvW hkv
        have hnot_vk : ¬ v < k := not_lt_of_gt hkv
        have hnot_fvk : ¬ f v < f k := not_lt_of_gt hfkv
        simp only [subtreeAtKey, hnot_vk, hkv, ↓reduceIte] at hsubW
        obtain ⟨hsub_map, hrot_map⟩ := ihr hr_bst
          (fun a ha b hb => hfW a (.right ha) b (.right hb)) hvr hsubW
        refine ⟨?_, ?_⟩
        · simp [BinaryTree.map, subtreeAtKey, hnot_fvk, hfkv, hsub_map]
        · simp [BinaryTree.map, rotateRightEdge, hnot_vk, hkv, hnot_fvk, hfkv, hrot_map]
  obtain ⟨hsub_map, hrot_map⟩ := haux t ht hf hv_in hsub
  have hfv_in : f v ∈ t.map f := (mem_map_iff f t (f v)).mpr ⟨v, hv_in, rfl⟩
  exact ⟨hfuv, ⟨L.map f, Q.map f, R.map f, hfv_in, hsub_map⟩, hrot_map⟩

theorem phaseBlockBST_eq {P M : ℕ} (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p τ : ℕ) :
    phaseBlockBST P proc chain (ℓ.val + 1) X p τ =
      restrictTree (cartesianExt proc τ)
        {u : ℕ | (subblock1 (childSubblocks (chain ℓ.succ) X) p).hi < u ∧ u ≤ X.hi} := by
  have hℓ : 1 ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  unfold phaseBlockBST
  simp only [hℓ.1, hℓ.2, and_self, ↓reduceDIte]
  rfl

theorem phaseSummaryBST_eq {P M : ℕ} (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p τ : ℕ) :
    phaseSummaryBST P proc chain (ℓ.val + 1) X p τ =
      (preorderSummaryBST (phaseBlockBST P proc chain (ℓ.val + 1) X p τ)
        ((childSubblocks (chain ℓ.succ) X).drop p) 1).map
        (subblockIndex1 (childSubblocks (chain ℓ.succ) X)) := by
  have hℓ : 1 ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  unfold phaseSummaryBST
  simp only [hℓ.1, hℓ.2, and_self, ↓reduceDIte]
  rfl

theorem phaseBlockBST_props (h_3_1 : Ty_lem_3_1) {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    let Sp := subblock1 subs p
    let tEnd := proc.popStepIdx (subblock1 subs (p + 1)).lo
    (∀ τ ≤ tEnd,
      (phaseBlockBST P proc chain (ℓ.val + 1) X p τ).IsBST ∧
      keyFinset (phaseBlockBST P proc chain (ℓ.val + 1) X p τ) =
        Finset.Icc (Sp.hi + 1) X.hi) ∧
    (∀ τ₁ τ₂ : ℕ, τ₁ ≤ τ₂ → τ₂ ≤ tEnd →
      RightRotReachable
        (phaseBlockBST P proc chain (ℓ.val + 1) X p τ₁)
        (phaseBlockBST P proc chain (ℓ.val + 1) X p τ₂)) := by
  dsimp only
  have hK2 := validScaleTree_K_X_ge_two hValid ℓ X hX
  obtain ⟨hX1, _, hXP, _, hsub_c, _, hconsec, _, _, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨_, _, htEnd_lt, hs0_le_all⟩ := tauEmpty_window_bounds hValid proc ℓ X hX hp1 hp2
  obtain ⟨_, hpop, hpop_mono, _, _⟩ := popStepIdx_and_insStep_props proc
  obtain ⟨hproc_inv, hproc_step⟩ := proc_tree_bst_and_step_keys proc
  set chain := scaleTreePartitionChain T P M
  set subs := childSubblocks (chain ℓ.succ) X
  have hp_len : p ≤ subs.length := by omega
  have hp1_len : p + 1 ≤ subs.length := by omega
  obtain ⟨_, _, hX_Splo, hSplo_hi, hSphi_X, _⟩ := hsub_c p (Finset.mem_Icc.mpr ⟨hp1, hp_len⟩)
  obtain ⟨_, _, hX_Sp1lo, hSp1lo_hi, hSp1hi_X, _⟩ :=
    hsub_c (p + 1) (Finset.mem_Icc.mpr ⟨by omega, hp1_len⟩)
  have hlink := hconsec p hp1 hp1_len
  set Sp := subblock1 subs p
  set Sp1 := subblock1 subs (p + 1)
  set tEnd := proc.popStepIdx Sp1.lo
  set I_Xp : Set ℕ := {u : ℕ | Sp.hi < u ∧ u ≤ X.hi}
  have hSp1lo_Icc : Sp1.lo ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hbst_keys : ∀ τ ≤ tEnd,
      (phaseBlockBST P proc chain (ℓ.val + 1) X p τ).IsBST ∧
      keyFinset (phaseBlockBST P proc chain (ℓ.val + 1) X p τ) = Finset.Icc (Sp.hi + 1) X.hi := by
    intro τ hτ
    have hτ_len : τ ≤ proc.steps.length := le_trans hτ (le_of_lt htEnd_lt)
    have hs0_le : s0At proc τ ≤ Sp.hi := hs0_le_all τ hτ
    obtain ⟨hext_bst, hext_keys⟩ := cartesianExt_isBST_and_keys proc hτ_len
    obtain ⟨hBp_bst, hBp_mem⟩ :=
      (h_3_1 (cartesianExt proc τ) I_Xp hext_bst (isLCAClosed_interval_oc _ _ _)).1
    rw [phaseBlockBST_eq]
    refine ⟨hBp_bst, ?_⟩
    ext v
    rw [← mem_iff_mem_keyFinset, hBp_mem, mem_iff_mem_keyFinset, hext_keys, Finset.mem_Icc,
        Finset.mem_Icc]
    change (s0At proc τ + 1 ≤ v ∧ v ≤ P) ∧ (Sp.hi < v ∧ v ≤ X.hi) ↔ Sp.hi + 1 ≤ v ∧ v ≤ X.hi
    omega
  have hstep_one : ∀ τ, τ + 1 ≤ tEnd →
      RightRotReachable
        (phaseBlockBST P proc chain (ℓ.val + 1) X p τ)
        (phaseBlockBST P proc chain (ℓ.val + 1) X p (τ + 1)) := by
    intro τ hτ1
    have hτ_lt_len : τ < proc.steps.length := lt_of_lt_of_le (Nat.lt_succ_self τ)
      (le_trans hτ1 (le_of_lt htEnd_lt))
    obtain ⟨hext_bst, _⟩ := cartesianExt_isBST_and_keys proc (le_of_lt hτ_lt_len)
    have hlaws := cartesianExt_step_laws proc hτ_lt_len
    rw [phaseBlockBST_eq, phaseBlockBST_eq]
    cases hop : proc.steps[τ]'hτ_lt_len with
    | push w =>
      rw [hop] at hlaws
      exact h_3_1_rightRot_reachable h_3_1 hext_bst
        (fun t _ => isLCAClosed_interval_oc t _ _) hlaws
    | shift =>
      rw [hop] at hlaws
      rw [hlaws]
      exact .refl
    | upperRot u v =>
      rw [hop] at hlaws
      rcases hlaws with ⟨huv, hedge, heq⟩
      rw [heq]
      exact h_3_1_rightRot_reachable h_3_1 hext_bst
        (fun t _ => isLCAClosed_interval_oc t _ _) (rightRotReachable_single huv hedge)
    | pop s =>
      rw [hop] at hlaws
      rcases hlaws with ⟨b, _, _, _, hmin_ext, _, hreach_sp⟩
      have hstep_s := hproc_step τ hτ_lt_len
      rw [hop] at hstep_s
      have hs_Icc : s ∈ Finset.Icc 1 P := (hproc_inv τ (le_of_lt hτ_lt_len)).2 hstep_s.1
      have hτ_eq_pop : τ = proc.popStepIdx s :=
        ((hpop s hs_Icc).2.2 τ hτ_lt_len).mp (getElem?_of_getElem hτ_lt_len hop)
      have hs_lt_Sp1 : s < Sp1.lo :=
        (hpop_mono s hs_Icc Sp1.lo hSp1lo_Icc).1.mpr (by omega)
      have hs_not_I : s ∉ I_Xp := by
        change ¬ (Sp.hi < s ∧ s ≤ X.hi)
        omega
      have hext_ne : cartesianExt proc τ ≠ .nil := by
        intro hnil; rw [hnil] at hmin_ext; simp [BinaryTree.minKey?] at hmin_ext
      have hsp_eq : restrictTree (spliceMin (cartesianExt proc τ)) I_Xp =
          restrictTree (cartesianExt proc τ) I_Xp :=
        ((h_3_1 (cartesianExt proc τ) I_Xp hext_bst
          (isLCAClosed_interval_oc _ _ _)).2.2 hext_ne).1.2 s hmin_ext |>.2 hs_not_I
      obtain ⟨hsp_bst, _⟩ := spliceMin_spec hext_bst hmin_ext
      rw [← hsp_eq]
      exact h_3_1_rightRot_reachable h_3_1 hsp_bst
        (fun t _ => isLCAClosed_interval_oc t _ _) hreach_sp
  refine ⟨hbst_keys, ?_⟩
  intro τ₁ τ₂ h12 h2end
  induction h12 with
  | refl => exact .refl
  | step hle ih =>
    rename_i m
    exact (ih (by omega)).trans (hstep_one m h2end)

def treeRootKey? {α : Type} : BinaryTree α → Option α
  | .nil => none
  | .node k _ _ => some k

theorem preorderRank_le_one_iff {α : Type} [DecidableEq α]
    (t : BinaryTree α) (w : α) :
    (1 ≤ preorderRank t w ∧ preorderRank t w ≤ 1) ↔ treeRootKey? t = some w := by
  cases t with
  | nil =>
    simp [preorderRank, bstPreorderList, listRank1, treeRootKey?]
  | node k l r =>
    simp only [preorderRank, bstPreorderList, listRank1, treeRootKey?, Option.some.injEq]
    by_cases hwk : w = k
    · subst hwk; simp
    · have hne : k ≠ w := fun h => hwk h.symm
      simp only [hwk, ↓reduceIte, hne, iff_false]
      cases listRank1 (bstPreorderList l ++ bstPreorderList r) w <;> simp

def firstInBlock? : BinaryTree ℕ → IntervalBlock → Option ℕ
  | .nil, _ => none
  | .node k l r, C =>
    if C.lo ≤ k ∧ k ≤ C.hi then some k
    else if k < C.lo then firstInBlock? r C
    else firstInBlock? l C

theorem firstInBlock?_mem {B : BinaryTree ℕ} {C : IntervalBlock} {w : ℕ}
    (h : firstInBlock? B C = some w) :
    w ∈ B ∧ w ∈ C.toSet := by
  induction B with
  | nil => simp [firstInBlock?] at h
  | node k l r ihl ihr =>
    unfold firstInBlock? at h
    split_ifs at h with hk hlt
    · injection h with hkw; subst hkw
      exact ⟨.here, hk⟩
    · obtain ⟨h1, h2⟩ := ihr h
      exact ⟨.right h1, h2⟩
    · obtain ⟨h1, h2⟩ := ihl h
      exact ⟨.left h1, h2⟩

theorem firstInBlock?_eq_none_iff {B : BinaryTree ℕ} (hB : B.IsBST) (C : IntervalBlock) :
    firstInBlock? B C = none ↔ ∀ x ∈ B, x ∉ C.toSet := by
  induction B with
  | nil => simp [firstInBlock?]
  | node k l r ihl ihr =>
    obtain ⟨hl, hr, hlt, hgt⟩ := (isBST_node_iff k l r).mp hB
    unfold firstInBlock?
    by_cases hk : C.lo ≤ k ∧ k ≤ C.hi
    · simp only [hk, and_self, ↓reduceIte, reduceCtorEq, false_iff, not_forall]
      exact ⟨k, .here, not_not.mpr hk⟩
    · simp only [hk, ↓reduceIte]
      by_cases hk_lt : k < C.lo
      · simp only [hk_lt, ↓reduceIte, ihr hr]
        constructor
        · intro hall x hx hxC
          rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
          · exact hk hxC
          · have := hlt x hxl; change C.lo ≤ x ∧ x ≤ C.hi at hxC; omega
          · exact hall x hxr hxC
        · intro hall x hxr
          exact hall x (.right hxr)
      · simp only [hk_lt, ↓reduceIte, ihl hl]
        constructor
        · intro hall x hx hxC
          rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
          · exact hk hxC
          · exact hall x hxl hxC
          · have := hgt x hxr; change C.lo ≤ x ∧ x ≤ C.hi at hxC; omega
        · intro hall x hxl
          exact hall x (.left hxl)

theorem treeRootKey?_restrictTree_eq_firstInBlock? {B : BinaryTree ℕ} (hB : B.IsBST)
    (C : IntervalBlock) :
    treeRootKey? (restrictTree B C.toSet) = firstInBlock? B C := by
  induction B with
  | nil => rfl
  | node k l r ihl ihr =>
    obtain ⟨hl, hr, hlt, hgt⟩ := (isBST_node_iff k l r).mp hB
    by_cases hk : k ∈ C.toSet
    · have hk' : C.lo ≤ k ∧ k ≤ C.hi := hk
      simp [restrictTree, firstInBlock?, hk, hk', treeRootKey?]
    · have hk' : ¬ (C.lo ≤ k ∧ k ≤ C.hi) := hk
      by_cases hk_lt : k < C.lo
      · by_cases hB_ex : ∃ b ∈ r, b ∈ C.toSet
        · simp [restrictTree, firstInBlock?, hk, hk', hk_lt, hB_ex, ihr hr]
        · have hr_nil : restrictTree r C.toSet = .nil :=
            (restrictTree_eq_nil_iff r C.toSet).mpr (fun b hb hbC => hB_ex ⟨b, hb, hbC⟩)
          have hl_nil : restrictTree l C.toSet = .nil := by
            rw [restrictTree_eq_nil_iff]
            intro a ha haC
            have := hlt a ha
            change C.lo ≤ a ∧ a ≤ C.hi at haC
            omega
          have hfb_r : firstInBlock? r C = none := by
            rw [← ihr hr, hr_nil]; rfl
          simp [restrictTree, firstInBlock?, hk, hk', hk_lt, hB_ex, hl_nil, hfb_r, treeRootKey?]
      · have hB_not : ¬ ∃ b ∈ r, b ∈ C.toSet := by
          rintro ⟨b, hb, hbC⟩
          have := hgt b hb
          change C.lo ≤ b ∧ b ≤ C.hi at hbC
          omega
        simp [restrictTree, firstInBlock?, hk, hk', hk_lt, hB_not, ihl hl]

theorem mem_preorderSummarySet_one_iff {B : BinaryTree ℕ} (hB : B.IsBST)
    (blocks : List IntervalBlock) (w : ℕ) :
    w ∈ preorderSummarySet B blocks 1 ↔ ∃ C ∈ blocks, firstInBlock? B C = some w := by
  unfold preorderSummarySet
  dsimp only
  induction blocks with
  | nil => simp
  | cons C rest ih =>
    rw [List.foldr_cons, Finset.mem_union, Finset.mem_filter, ih]
    simp only [preorderRank_le_one_iff, treeRootKey?_restrictTree_eq_firstInBlock? hB,
      List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (⟨_, hC⟩ | hrest)
      · exact Or.inl hC
      · exact Or.inr hrest
    · rintro (hC | hrest)
      · exact Or.inl ⟨Finset.mem_Icc.mpr (firstInBlock?_mem hC).2, hC⟩
      · exact Or.inr hrest

theorem firstInBlock?_of_lcaBST {B : BinaryTree ℕ} (hB : B.IsBST)
    {x y z : ℕ} {C : IntervalBlock}
    (hx_in : x ∈ B) (hy_in : y ∈ B) (hlca : lcaBST B x y = some z)
    (hzC : z ∈ C.toSet)
    (hxC : x ∈ C.toSet → firstInBlock? B C = some x)
    (hyC : y ∈ C.toSet → firstInBlock? B C = some y) :
    firstInBlock? B C = some z := by
  induction B with
  | nil => simp [lcaBST] at hlca
  | node k l r ihl ihr =>
    obtain ⟨hl, hr, hlt, hgt⟩ := (isBST_node_iff k l r).mp hB
    unfold lcaBST at hlca
    split_ifs at hlca with h_lt h_gt
    · rcases h_lt with ⟨hxk, hyk⟩
      have hxl : x ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hx_in with rfl | h | h
        · exact absurd rfl (ne_of_lt hxk)
        · exact h
        · exact absurd hxk (not_lt_of_gt (hgt x h))
      have hyl : y ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hy_in with rfl | h | h
        · exact absurd rfl (ne_of_lt hyk)
        · exact h
        · exact absurd hyk (not_lt_of_gt (hgt y h))
      obtain ⟨_, hz_max⟩ := lcaBST_between l x y z hlca
      change C.lo ≤ z ∧ z ≤ C.hi at hzC
      have hk_not_lt : ¬ k < C.lo := by omega
      have hk_not_C : ¬ (C.lo ≤ k ∧ k ≤ C.hi) := by
        intro hkC
        have hfb_k : firstInBlock? (.node k l r) C = some k := by
          simp [firstInBlock?, hkC]
        by_cases hxy : x ≤ y
        · have hy_ge : z ≤ y := by have := max_eq_right hxy; omega
          have hy_in_C : y ∈ C.toSet := ⟨by omega, by omega⟩
          have := hfb_k.symm.trans (hyC hy_in_C)
          injection this with hky; omega
        · have hx_ge : z ≤ x := by have := max_eq_left (le_of_not_ge hxy); omega
          have hx_in_C : x ∈ C.toSet := ⟨by omega, by omega⟩
          have := hfb_k.symm.trans (hxC hx_in_C)
          injection this with hkx; omega
      have hfb_eq : firstInBlock? (.node k l r) C = firstInBlock? l C := by
        simp [firstInBlock?, hk_not_C, hk_not_lt]
      rw [hfb_eq] at hxC hyC ⊢
      exact ihl hl hxl hyl hlca hxC hyC
    · rcases h_gt with ⟨hkx, hky⟩
      have hxr : x ∈ r := by
        rcases BinaryTree.mem_node_iff.mp hx_in with rfl | h | h
        · exact absurd rfl (ne_of_gt hkx)
        · exact absurd hkx (not_lt_of_gt (hlt x h))
        · exact h
      have hyr : y ∈ r := by
        rcases BinaryTree.mem_node_iff.mp hy_in with rfl | h | h
        · exact absurd rfl (ne_of_gt hky)
        · exact absurd hky (not_lt_of_gt (hlt y h))
        · exact h
      obtain ⟨hmin_z, _⟩ := lcaBST_between r x y z hlca
      change C.lo ≤ z ∧ z ≤ C.hi at hzC
      have hk_not_C : ¬ (C.lo ≤ k ∧ k ≤ C.hi) := by
        intro hkC
        have hfb_k : firstInBlock? (.node k l r) C = some k := by
          simp [firstInBlock?, hkC]
        by_cases hxy : x ≤ y
        · have hx_le : x ≤ z := by have := min_eq_left hxy; omega
          have hx_in_C : x ∈ C.toSet := ⟨by omega, by omega⟩
          have := hfb_k.symm.trans (hxC hx_in_C)
          injection this with hkx; omega
        · have hy_le : y ≤ z := by have := min_eq_right (le_of_not_ge hxy); omega
          have hy_in_C : y ∈ C.toSet := ⟨by omega, by omega⟩
          have := hfb_k.symm.trans (hyC hy_in_C)
          injection this with hky'; omega
      have hk_lt : k < C.lo := by omega
      have hfb_eq : firstInBlock? (.node k l r) C = firstInBlock? r C := by
        simp [firstInBlock?, hk_not_C, hk_lt]
      rw [hfb_eq] at hxC hyC ⊢
      exact ihr hr hxr hyr hlca hxC hyC
    · injection hlca with hkz; subst hkz
      change C.lo ≤ k ∧ k ≤ C.hi at hzC
      simp [firstInBlock?, hzC]

theorem isLCAClosed_preorderSummarySet_one {B : BinaryTree ℕ} (hB : B.IsBST)
    {blocks : List IntervalBlock}
    (hcov : ∀ w ∈ B, ∃ C ∈ blocks, w ∈ C.toSet)
    (hdisj : ∀ C₁ ∈ blocks, ∀ C₂ ∈ blocks, ∀ w, w ∈ C₁.toSet → w ∈ C₂.toSet → C₁ = C₂) :
    IsLCAClosed B (preorderSummarySet B blocks 1 : Set ℕ) := by
  intro x hxB y hyB hxS hyS z hlca
  change x ∈ preorderSummarySet B blocks 1 at hxS
  change y ∈ preorderSummarySet B blocks 1 at hyS
  change z ∈ preorderSummarySet B blocks 1
  rw [mem_preorderSummarySet_one_iff hB] at hxS hyS ⊢
  have hzB : z ∈ B := lcaBST_mem B x y z hlca
  obtain ⟨C, hC_mem, hzC⟩ := hcov z hzB
  refine ⟨C, hC_mem, firstInBlock?_of_lcaBST hB hxB hyB hlca hzC (fun hxC => ?_) (fun hyC => ?_)⟩
  · rcases hxS with ⟨Cx, hCx_mem, hfb_x⟩
    have hxCx : x ∈ Cx.toSet := (firstInBlock?_mem hfb_x).2
    rw [← hdisj Cx hCx_mem C hC_mem x hxCx hxC]
    exact hfb_x
  · rcases hyS with ⟨Cy, hCy_mem, hfb_y⟩
    have hyCy : y ∈ Cy.toSet := (firstInBlock?_mem hfb_y).2
    rw [← hdisj Cy hCy_mem C hC_mem y hyCy hyC]
    exact hfb_y

theorem remBlocks_mem_iff {P M : ℕ} {T : ScaleTree}
    (ℓ : Fin M) (X : IntervalBlock)
    {p : ℕ} (hp : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length)
    (C : IntervalBlock) :
    let subs := childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X
    C ∈ subs.drop p ↔ ∃ c ∈ Finset.Icc (p + 1) subs.length, C = subblock1 subs c := by
  dsimp only
  set subs := childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X
  have hsub1_eq : ∀ c (_ : 1 ≤ c) (hclen : c ≤ subs.length),
      subblock1 subs c = subs[c - 1]'(by omega) := by
    intro c hc1 hclen
    unfold subblock1
    have hc0 : ¬ c = 0 := by omega
    simp [hc0, List.getElem?_eq_getElem (show c - 1 < subs.length by omega)]
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hget⟩
    rw [List.length_drop] at hi
    rw [List.getElem_drop] at hget
    refine ⟨p + i + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [hsub1_eq (p + i + 1) (by omega) (by omega)]
    have hidx : p + i + 1 - 1 = p + i := by omega
    simpa [hidx] using hget.symm
  · rintro ⟨c, hc, rfl⟩
    rw [Finset.mem_Icc] at hc
    refine ⟨c - (p + 1), by rw [List.length_drop]; omega, ?_⟩
    rw [List.getElem_drop, hsub1_eq c (by omega) hc.2]
    have hidx : p + (c - (p + 1)) = c - 1 := by omega
    simp [hidx]

theorem summary_bst_and_keys_of_blockBST (h_3_1 : Ty_lem_3_1)
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1)
    {B : BinaryTree ℕ} (hB : B.IsBST)
    (hB_keys : keyFinset B =
      Finset.Icc ((subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).hi + 1)
        X.hi) :
    let subs := childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X
    let remBlocks := subs.drop p
    let S := (preorderSummarySet B remBlocks 1 : Set ℕ)
    let T_sum := preorderSummaryBST B remBlocks 1
    let G := T_sum.map (subblockIndex1 subs)
    IsLCAClosed B S ∧
    T_sum.IsBST ∧
    (∀ a ∈ T_sum, ∀ b ∈ T_sum, a < b → subblockIndex1 subs a < subblockIndex1 subs b) ∧
    G.IsBST ∧
    keyFinset G = Finset.Icc (p + 1) subs.length := by
  dsimp only
  have hK2 := validScaleTree_K_X_ge_two hValid ℓ X hX
  obtain ⟨_, _, _, _, hsub_c, hlt_idx, _, _, _, hcov_X⟩ := subblock1_props hValid ℓ X hX
  set subs := childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X
  have hp_len : p ≤ subs.length := by omega
  obtain ⟨_, _, hX_Splo, hSplo_hi, _, _⟩ := hsub_c p (Finset.mem_Icc.mpr ⟨hp1, hp_len⟩)
  set Sp := subblock1 subs p
  set remBlocks := subs.drop p
  have hcov : ∀ w ∈ B, ∃ C ∈ remBlocks, w ∈ C.toSet := by
    intro w hwB
    have hw_Icc : w ∈ Finset.Icc (Sp.hi + 1) X.hi := hB_keys ▸ (mem_iff_mem_keyFinset B w).mp hwB
    have hw_bounds := Finset.mem_Icc.mp hw_Icc
    have hw_X : w ∈ Finset.Icc X.lo X.hi := Finset.mem_Icc.mpr ⟨by omega, hw_bounds.2⟩
    obtain ⟨hc_Icc, hw_Sc⟩ := hcov_X w hw_X
    set c := subblockIndex1 subs w
    have hc_gt_p : p < c := by
      by_contra hle
      have hc_le_p : c ≤ p := Nat.not_lt.mp hle
      rcases eq_or_lt_of_le hc_le_p with hcp | hlt_cp
      · rw [hcp] at hw_Sc
        have hw_hi := (Finset.mem_Icc.mp hw_Sc).2
        dsimp only [Sp] at hw_bounds
        omega
      · have := hlt_idx c p (Finset.mem_Icc.mp hc_Icc).1 hlt_cp hp_len
        have hw_hi := (Finset.mem_Icc.mp hw_Sc).2
        dsimp only [Sp] at hSplo_hi hw_bounds
        omega
    refine ⟨subblock1 subs c, ?_, Finset.mem_Icc.mp hw_Sc⟩
    exact (remBlocks_mem_iff ℓ X hp_len _).mpr
      ⟨c, Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hc_Icc).2⟩, rfl⟩
  have hdisj : ∀ C₁ ∈ remBlocks, ∀ C₂ ∈ remBlocks, ∀ w, w ∈ C₁.toSet → w ∈ C₂.toSet → C₁ = C₂ := by
    intro C₁ hC₁ C₂ hC₂ w hw₁ hw₂
    obtain ⟨c₁, hc₁, rfl⟩ := (remBlocks_mem_iff ℓ X hp_len C₁).mp hC₁
    obtain ⟨c₂, hc₂, rfl⟩ := (remBlocks_mem_iff ℓ X hp_len C₂).mp hC₂
    have hc₁_full : c₁ ∈ Finset.Icc 1 subs.length :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc₁).1; omega, (Finset.mem_Icc.mp hc₁).2⟩
    have hc₂_full : c₂ ∈ Finset.Icc 1 subs.length :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc₂).1; omega, (Finset.mem_Icc.mp hc₂).2⟩
    have hidx₁ := ((hsub_c c₁ hc₁_full).2.2.2.2.2 w (Finset.mem_Icc.mpr hw₁)).1
    have hidx₂ := ((hsub_c c₂ hc₂_full).2.2.2.2.2 w (Finset.mem_Icc.mpr hw₂)).1
    rw [← hidx₁, hidx₂]
  have hLCA : IsLCAClosed B (preorderSummarySet B remBlocks 1 : Set ℕ) :=
    isLCAClosed_preorderSummarySet_one hB hcov hdisj
  obtain ⟨hT_bst, hT_mem⟩ := (h_3_1 B (preorderSummarySet B remBlocks 1 : Set ℕ) hB hLCA).1
  have hmono : ∀ a ∈ preorderSummaryBST B remBlocks 1,
      ∀ b ∈ preorderSummaryBST B remBlocks 1,
      a < b → subblockIndex1 subs a < subblockIndex1 subs b := by
    intro a ha b hb hab
    have haS : a ∈ preorderSummarySet B remBlocks 1 := ((hT_mem a).mp ha).2
    have hbS : b ∈ preorderSummarySet B remBlocks 1 := ((hT_mem b).mp hb).2
    obtain ⟨Ca, hCa, hfb_a⟩ := (mem_preorderSummarySet_one_iff hB remBlocks a).mp haS
    obtain ⟨Cb, hCb, hfb_b⟩ := (mem_preorderSummarySet_one_iff hB remBlocks b).mp hbS
    obtain ⟨c₁, hc₁, rfl⟩ := (remBlocks_mem_iff ℓ X hp_len Ca).mp hCa
    obtain ⟨c₂, hc₂, rfl⟩ := (remBlocks_mem_iff ℓ X hp_len Cb).mp hCb
    have hc₁_full : c₁ ∈ Finset.Icc 1 subs.length :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc₁).1; omega, (Finset.mem_Icc.mp hc₁).2⟩
    have hc₂_full : c₂ ∈ Finset.Icc 1 subs.length :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc₂).1; omega, (Finset.mem_Icc.mp hc₂).2⟩
    have ha_in := (firstInBlock?_mem hfb_a).2
    have hb_in := (firstInBlock?_mem hfb_b).2
    have hidx_a := ((hsub_c c₁ hc₁_full).2.2.2.2.2 a (Finset.mem_Icc.mpr ha_in)).1
    have hidx_b := ((hsub_c c₂ hc₂_full).2.2.2.2.2 b (Finset.mem_Icc.mpr hb_in)).1
    rw [hidx_a, hidx_b]
    by_contra hle
    rcases eq_or_lt_of_le (Nat.not_lt.mp hle) with rfl | hgt_c
    · rw [hfb_a] at hfb_b; injection hfb_b with heq; omega
    · have := hlt_idx c₂ c₁ (Finset.mem_Icc.mp hc₂_full).1 hgt_c (Finset.mem_Icc.mp hc₁_full).2
      change (subblock1 subs c₁).lo ≤ a ∧ a ≤ (subblock1 subs c₁).hi at ha_in
      change (subblock1 subs c₂).lo ≤ b ∧ b ≤ (subblock1 subs c₂).hi at hb_in
      omega
  have hG_bst : ((preorderSummaryBST B remBlocks 1).map (subblockIndex1 subs)).IsBST :=
    map_isBST_of_strictMonoOn hT_bst hmono
  refine ⟨hLCA, hT_bst, hmono, hG_bst, ?_⟩
  ext c
  rw [← mem_iff_mem_keyFinset, mem_map_iff]
  constructor
  · rintro ⟨w, hwT, rfl⟩
    have hwS : w ∈ preorderSummarySet B remBlocks 1 := ((hT_mem w).mp hwT).2
    obtain ⟨C, hC, hfb_w⟩ := (mem_preorderSummarySet_one_iff hB remBlocks w).mp hwS
    obtain ⟨c', hc', rfl⟩ := (remBlocks_mem_iff ℓ X hp_len C).mp hC
    have hc'_full : c' ∈ Finset.Icc 1 subs.length :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc').1; omega, (Finset.mem_Icc.mp hc').2⟩
    have hw_in := (firstInBlock?_mem hfb_w).2
    rw [((hsub_c c' hc'_full).2.2.2.2.2 w (Finset.mem_Icc.mpr hw_in)).1]
    exact hc'
  · intro hc
    have hc_bounds := Finset.mem_Icc.mp hc
    have hc_full : c ∈ Finset.Icc 1 subs.length :=
      Finset.mem_Icc.mpr ⟨by omega, hc_bounds.2⟩
    obtain ⟨_, _, _, hSc_le, hSchi_X, hSc_mem⟩ := hsub_c c hc_full
    have hSp_lt_Sc : Sp.hi < (subblock1 subs c).lo := hlt_idx p c hp1 (by omega) hc_bounds.2
    have hlo_in_B : (subblock1 subs c).lo ∈ B := by
      rw [mem_iff_mem_keyFinset, hB_keys, Finset.mem_Icc]
      omega
    have hfb_ne : firstInBlock? B (subblock1 subs c) ≠ none := by
      intro hnone
      exact (firstInBlock?_eq_none_iff hB (subblock1 subs c)).mp hnone
        (subblock1 subs c).lo hlo_in_B ⟨le_rfl, hSc_le⟩
    cases hfb : firstInBlock? B (subblock1 subs c) with
    | none => exact absurd hfb hfb_ne
    | some w =>
      obtain ⟨hwB, hwC⟩ := firstInBlock?_mem hfb
      have hSc_rem : subblock1 subs c ∈ remBlocks :=
        (remBlocks_mem_iff ℓ X hp_len _).mpr ⟨c, hc, rfl⟩
      have hwS : w ∈ preorderSummarySet B remBlocks 1 :=
        (mem_preorderSummarySet_one_iff hB remBlocks w).mpr ⟨subblock1 subs c, hSc_rem, hfb⟩
      have hwT : w ∈ preorderSummaryBST B remBlocks 1 := (hT_mem w).mpr ⟨hwB, hwS⟩
      exact ⟨w, hwT, (hSc_mem w (Finset.mem_Icc.mpr hwC)).1⟩

theorem firstInBlock?_rotateRightEdge {B : BinaryTree ℕ} (hB : B.IsBST)
    {u v : ℕ} (huv : u < v) (hedge : IsRightRotEdge B u v) (C : IntervalBlock) :
    (¬ (u ∈ C.toSet ∧ v ∈ C.toSet) →
      firstInBlock? (rotateRightEdge B u v) C = firstInBlock? B C) ∧
    (u ∈ C.toSet ∧ v ∈ C.toSet →
      firstInBlock? (rotateRightEdge B u v) C =
        if firstInBlock? B C = some v then some u else firstInBlock? B C) := by
  rcases hedge with ⟨L, Q, R, hv_in, hsub⟩
  induction B with
  | nil => cases hv_in
  | node k l r ihl ihr =>
    obtain ⟨hl_bst, hr_bst, hlt, hgt⟩ := (isBST_node_iff k l r).mp hB
    rcases lt_trichotomy v k with hvk | rfl | hkv
    · have hvl : v ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hv_in with rfl | h | h
        · exact absurd rfl (ne_of_lt hvk)
        · exact h
        · exact absurd hvk (not_lt_of_gt (hgt v h))
      simp only [subtreeAtKey, hvk, ↓reduceIte] at hsub
      simp only [rotateRightEdge, hvk, ↓reduceIte, firstInBlock?]
      by_cases hkC : C.lo ≤ k ∧ k ≤ C.hi
      · have hne : ¬ (some k = some v) := by simp [ne_of_gt hvk]
        simp [hkC, hne]
      · by_cases hk_lt : k < C.lo
        · have hv_not_C : v ∉ C.toSet := by
            change ¬ (C.lo ≤ v ∧ v ≤ C.hi); omega
          refine ⟨by simp [hkC, hk_lt], fun h => absurd h.2 hv_not_C⟩
        · simp only [hkC, hk_lt, ↓reduceIte]
          exact ihl hl_bst hvl hsub
    · simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
      injection hsub with _ hl_eq hr_eq
      rw [hl_eq, hr_eq]
      have hrot : rotateRightEdge (.node v (.node u L Q) R) u v =
          .node u L (.node v Q R) := by
        simp [rotateRightEdge]
      rw [hrot]
      by_cases huC : C.lo ≤ u ∧ u ≤ C.hi
      · by_cases hvC : C.lo ≤ v ∧ v ≤ C.hi
        · have hboth : u ∈ C.toSet ∧ v ∈ C.toSet := ⟨huC, hvC⟩
          refine ⟨fun h => absurd hboth h, fun _ => by simp [firstInBlock?, huC, hvC]⟩
        · have hnot_both : ¬ (u ∈ C.toSet ∧ v ∈ C.toSet) := fun h => hvC h.2
          have hv_not_lt : ¬ v < C.lo := by omega
          refine ⟨fun _ => by simp [firstInBlock?, huC, hvC, hv_not_lt],
                  fun h => absurd h hnot_both⟩
      · have hnot_both : ¬ (u ∈ C.toSet ∧ v ∈ C.toSet) := fun h => huC h.1
        refine ⟨fun _ => ?_, fun h => absurd h hnot_both⟩
        by_cases hvC : C.lo ≤ v ∧ v ≤ C.hi
        · have hu_lt : u < C.lo := by omega
          simp [firstInBlock?, huC, hvC, hu_lt]
        · by_cases hu_lt : u < C.lo
          · by_cases hv_lt : v < C.lo
            · simp [firstInBlock?, huC, hvC, hu_lt, hv_lt]
            · simp [firstInBlock?, huC, hvC, hu_lt, hv_lt]
          · have hv_not_lt : ¬ v < C.lo := by omega
            simp [firstInBlock?, huC, hvC, hu_lt, hv_not_lt]
    · have hvr : v ∈ r := by
        rcases BinaryTree.mem_node_iff.mp hv_in with rfl | h | h
        · exact absurd rfl (ne_of_gt hkv)
        · exact absurd hkv (not_lt_of_gt (hlt v h))
        · exact h
      have hnot_vk : ¬ v < k := not_lt_of_gt hkv
      simp only [subtreeAtKey, hnot_vk, hkv, ↓reduceIte] at hsub
      simp only [rotateRightEdge, hnot_vk, hkv, ↓reduceIte, firstInBlock?]
      by_cases hkC : C.lo ≤ k ∧ k ≤ C.hi
      · have hne : ¬ (some k = some v) := by simp [ne_of_lt hkv]
        simp [hkC, hne]
      · by_cases hk_lt : k < C.lo
        · simp only [hkC, hk_lt, ↓reduceIte]
          exact ihr hr_bst hvr hsub
        · have hv_not_C : v ∉ C.toSet := by
            change ¬ (C.lo ≤ v ∧ v ≤ C.hi); omega
          refine ⟨by simp [hkC, hk_lt], fun h => absurd h.2 hv_not_C⟩

theorem restrictTree_rotateRightEdge_swap_map {α β : Type} [LinearOrder α]
    {T : BinaryTree α} (hT : T.IsBST) {u v : α} (huv : u < v)
    {L Q R : BinaryTree α} (hv_in : v ∈ T)
    (hsub : subtreeAtKey T v = .node v (.node u L Q) R)
    {S S' : Set α} {f : α → β} (hf_uv : f u = f v)
    (hvS : v ∈ S) (huS_not : u ∉ S)
    (huS' : u ∈ S') (hvS'_not : v ∉ S')
    (hiff : ∀ w, w ≠ u → w ≠ v → (w ∈ S' ↔ w ∈ S))
    (hQ : ∀ q ∈ Q, q ∉ S) :
    (restrictTree (rotateRightEdge T u v) S').map f = (restrictTree T S).map f := by
  induction T with
  | nil => cases hv_in
  | node k l r ihl ihr =>
    obtain ⟨hl_bst, hr_bst, hlt, hgt⟩ := (isBST_node_iff k l r).mp hT
    rcases lt_trichotomy v k with hvk | rfl | hkv
    · have hvl : v ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hv_in with rfl | h | h
        · exact absurd rfl (ne_of_lt hvk)
        · exact h
        · exact absurd hvk (not_lt_of_gt (hgt v h))
      simp only [subtreeAtKey, hvk, ↓reduceIte] at hsub
      have huk : u < k := lt_trans huv hvk
      have hk_iff : k ∈ S' ↔ k ∈ S := hiff k (ne_of_gt huk) (ne_of_gt hvk)
      have hr_iff : ∀ w ∈ r, w ∈ S' ↔ w ∈ S := fun w hw =>
        hiff w (ne_of_gt (lt_trans huk (hgt w hw))) (ne_of_gt (lt_trans hvk (hgt w hw)))
      have hr_eq : restrictTree r S' = restrictTree r S := restrictTree_congr_mem r S' S hr_iff
      have hex_r : (∃ b ∈ r, b ∈ S') ↔ (∃ b ∈ r, b ∈ S) :=
        exists_congr (fun b => and_congr_right (fun hb => hr_iff b hb))
      have hrot : rotateRightEdge (.node k l r) u v = .node k (rotateRightEdge l u v) r := by
        simp [rotateRightEdge, hvk]
      rw [hrot]
      have h_ihl := ihl hl_bst hvl hsub
      by_cases hkS : k ∈ S
      · have hkS' : k ∈ S' := hk_iff.mpr hkS
        simp [restrictTree, hkS, hkS', BinaryTree.map, h_ihl, hr_eq]
      · have hkS' : k ∉ S' := fun h => hkS (hk_iff.mp h)
        by_cases hB : ∃ b ∈ r, b ∈ S
        · have hB' : ∃ b ∈ r, b ∈ S' := hex_r.mpr hB
          simp [restrictTree, hkS, hkS', hB, hB', hr_eq]
        · have hB' : ¬ ∃ b ∈ r, b ∈ S' := fun h => hB (hex_r.mp h)
          simp [restrictTree, hkS, hkS', hB, hB', h_ihl]
    · simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
      injection hsub with _ hl_eq hr_eq
      rw [hl_eq] at hlt hl_bst ⊢
      rw [hr_eq] at hgt ⊢
      obtain ⟨_, _, hL_lt_u, hQ_gt_u⟩ := (isBST_node_iff u L Q).mp hl_bst
      have hrot : rotateRightEdge (.node v (.node u L Q) R) u v = .node u L (.node v Q R) := by
        simp [rotateRightEdge]
      rw [hrot]
      have hL_eq : restrictTree L S' = restrictTree L S :=
        restrictTree_congr_mem L S' S (fun w hw =>
          hiff w (ne_of_lt (hL_lt_u w hw)) (ne_of_lt (lt_trans (hL_lt_u w hw) huv)))
      have hR_eq : restrictTree R S' = restrictTree R S :=
        restrictTree_congr_mem R S' S (fun w hw =>
          hiff w (ne_of_gt (lt_trans huv (hgt w hw))) (ne_of_gt (hgt w hw)))
      have hQ_not_S : ¬ ∃ q ∈ Q, q ∈ S := fun ⟨q, hq, hqS⟩ => hQ q hq hqS
      have hQ_not_S' : ∀ q ∈ Q, q ∉ S' := fun q hq hqS' =>
        hQ q hq ((hiff q (ne_of_gt (hQ_gt_u q hq)) (ne_of_lt (hlt q (.right hq)))).mp hqS')
      have hQ_nil_S' : restrictTree Q S' = .nil := (restrictTree_eq_nil_iff Q S').mpr hQ_not_S'
      have hRHS : restrictTree (.node v (.node u L Q) R) S =
          .node v (restrictTree L S) (restrictTree R S) := by
        simp [restrictTree, hvS, huS_not, hQ_not_S]
      have hLHS_right : restrictTree (.node v Q R) S' = restrictTree R S := by
        by_cases hR_ex : ∃ w ∈ R, w ∈ S'
        · simp [restrictTree, hvS'_not, hR_ex, hR_eq]
        · have hR_not : ∀ w ∈ R, w ∉ S' := fun w hw hwS' => hR_ex ⟨w, hw, hwS'⟩
          have hR_nil : restrictTree R S' = .nil := (restrictTree_eq_nil_iff R S').mpr hR_not
          simp [restrictTree, hvS'_not, hR_ex, hQ_nil_S', ← hR_eq, hR_nil]
      have hLHS : restrictTree (.node u L (.node v Q R)) S' =
          .node u (restrictTree L S) (restrictTree R S) := by
        have houter : restrictTree (.node u L (.node v Q R)) S' =
            .node u (restrictTree L S') (restrictTree (.node v Q R) S') := by
          conv_lhs => unfold restrictTree
          simp only [huS', ↓reduceIte]
        rw [houter, hL_eq, hLHS_right]
      rw [hLHS, hRHS]
      simp [BinaryTree.map, hf_uv]
    · have hvr : v ∈ r := by
        rcases BinaryTree.mem_node_iff.mp hv_in with rfl | h | h
        · exact absurd rfl (ne_of_gt hkv)
        · exact absurd hkv (not_lt_of_gt (hlt v h))
        · exact h
      have hnot_vk : ¬ v < k := not_lt_of_gt hkv
      simp only [subtreeAtKey, hnot_vk, hkv, ↓reduceIte] at hsub
      have hur : u ∈ r := (mem_of_isRightRotEdge ⟨L, Q, R, hvr, hsub⟩).1
      have hku : k < u := hgt u hur
      have hk_iff : k ∈ S' ↔ k ∈ S := hiff k (ne_of_lt hku) (ne_of_lt hkv)
      have hl_eq : restrictTree l S' = restrictTree l S :=
        restrictTree_congr_mem l S' S (fun w hw =>
          hiff w (ne_of_lt (lt_trans (hlt w hw) hku)) (ne_of_lt (lt_trans (hlt w hw) hkv)))
      have hex_r_S : ∃ b ∈ r, b ∈ S := ⟨v, hvr, hvS⟩
      have hex_r_S' : ∃ b ∈ rotateRightEdge r u v, b ∈ S' :=
        ⟨u, (mem_rotateRightEdge_iff r u v u).mpr hur, huS'⟩
      have hrot : rotateRightEdge (.node k l r) u v = .node k l (rotateRightEdge r u v) := by
        simp [rotateRightEdge, hnot_vk, hkv]
      rw [hrot]
      have h_ihr := ihr hr_bst hvr hsub
      by_cases hkS : k ∈ S
      · have hkS' : k ∈ S' := hk_iff.mpr hkS
        simp [restrictTree, hkS, hkS', BinaryTree.map, hl_eq, h_ihr]
      · have hkS' : k ∉ S' := fun h => hkS (hk_iff.mp h)
        simp [restrictTree, hkS, hkS', hex_r_S, hex_r_S', h_ihr]

theorem summary_singleRot_proj (h_3_1 : Ty_lem_3_1)
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1)
    {B : BinaryTree ℕ} (hB : B.IsBST)
    (hB_keys : keyFinset B =
      Finset.Icc ((subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).hi + 1)
        X.hi)
    {u v : ℕ} (huv : u < v) (hedge : IsRightRotEdge B u v) :
    let subs := childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X
    let remBlocks := subs.drop p
    let f := subblockIndex1 subs
    let G := (preorderSummaryBST B remBlocks 1).map f
    let B' := rotateRightEdge B u v
    let G' := (preorderSummaryBST B' remBlocks 1).map f
    RightRotReachable G G' ∧
    (f u < f v →
      u ∈ preorderSummarySet B remBlocks 1 →
      v ∈ preorderSummarySet B remBlocks 1 →
      IsRightRotEdge G (f u) (f v) ∧ G' = rotateRightEdge G (f u) (f v)) := by
  dsimp only
  have hK2 := validScaleTree_K_X_ge_two hValid ℓ X hX
  obtain ⟨_, _, _, _, hsub_c, hlt_idx, _, _, _, hcov_X⟩ := subblock1_props hValid ℓ X hX
  have hB' : (rotateRightEdge B u v).IsBST := rotateRightEdge_isBST hB u v
  have hB'_keys : keyFinset (rotateRightEdge B u v) =
      Finset.Icc ((subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).hi + 1)
        X.hi := by
    rw [keyFinset_rotateRightEdge, hB_keys]
  obtain ⟨hLCA_B, hT_bst, hmono_B, _, _⟩ :=
    summary_bst_and_keys_of_blockBST h_3_1 hValid ℓ X hX hp1 hp2 hB hB_keys
  obtain ⟨hLCA_B', _, _, _, _⟩ :=
    summary_bst_and_keys_of_blockBST h_3_1 hValid ℓ X hX hp1 hp2 hB' hB'_keys
  set subs := childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X
  have hp_len : p ≤ subs.length := by omega
  obtain ⟨_, _, hX_Splo, hSplo_hi, _, _⟩ := hsub_c p (Finset.mem_Icc.mpr ⟨hp1, hp_len⟩)
  set Sp := subblock1 subs p
  set remBlocks := subs.drop p
  set f := subblockIndex1 subs
  set B' := rotateRightEdge B u v
  obtain ⟨hu_in_B, hv_in_B⟩ := mem_of_isRightRotEdge hedge
  have hu_Icc : u ∈ Finset.Icc X.lo X.hi := by
    have := Finset.mem_Icc.mp (hB_keys ▸ (mem_iff_mem_keyFinset B u).mp hu_in_B)
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hv_Icc : v ∈ Finset.Icc X.lo X.hi := by
    have := Finset.mem_Icc.mp (hB_keys ▸ (mem_iff_mem_keyFinset B v).mp hv_in_B)
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  obtain ⟨hc1_Icc, hu_Sc1⟩ := hcov_X u hu_Icc
  obtain ⟨hc2_Icc, hv_Sc2⟩ := hcov_X v hv_Icc
  by_cases hc_eq : f u = f v
  · refine ⟨?_, fun hlt_f => absurd hc_eq (ne_of_lt hlt_f)⟩
    set c₀ := f u
    have hc₀_gt_p : p < c₀ := by
      have hu_gt : Sp.hi < u :=
        (Finset.mem_Icc.mp (hB_keys ▸ (mem_iff_mem_keyFinset B u).mp hu_in_B)).1
      by_contra hle
      rcases eq_or_lt_of_le (Nat.not_lt.mp hle) with hcp | hlt_cp
      · have hu_hi := (Finset.mem_Icc.mp hu_Sc1).2
        change u ≤ (subblock1 subs c₀).hi at hu_hi
        rw [hcp] at hu_hi
        dsimp only [Sp] at hu_gt
        omega
      · have := hlt_idx c₀ p (Finset.mem_Icc.mp hc1_Icc).1 hlt_cp hp_len
        have hu_hi := (Finset.mem_Icc.mp hu_Sc1).2
        change u ≤ (subblock1 subs c₀).hi at hu_hi
        dsimp only [Sp] at hSplo_hi hu_gt
        omega
    have hc₀_rem : subblock1 subs c₀ ∈ remBlocks :=
      (remBlocks_mem_iff ℓ X hp_len _).mpr
        ⟨c₀, Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hc1_Icc).2⟩, rfl⟩
    have hu_in_Sc₀ : u ∈ (subblock1 subs c₀).toSet := Finset.mem_Icc.mp hu_Sc1
    have hv_in_Sc₀ : v ∈ (subblock1 subs c₀).toSet := by
      have hv' : v ∈ (subblock1 subs (f v)).toSet := Finset.mem_Icc.mp hv_Sc2
      rwa [← hc_eq] at hv'
    have hother_not_both : ∀ C ∈ remBlocks, C ≠ subblock1 subs c₀ →
        ¬ (u ∈ C.toSet ∧ v ∈ C.toSet) := by
      intro C hC hne ⟨huC, _⟩
      obtain ⟨c', hc', rfl⟩ := (remBlocks_mem_iff ℓ X hp_len C).mp hC
      have hc'_full : c' ∈ Finset.Icc 1 subs.length :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc').1; omega, (Finset.mem_Icc.mp hc').2⟩
      have hidx_u : f u = c' := ((hsub_c c' hc'_full).2.2.2.2.2 u (Finset.mem_Icc.mpr huC)).1
      exact hne (congrArg (subblock1 subs) hidx_u.symm)
    by_cases hfb_v : firstInBlock? B (subblock1 subs c₀) = some v
    · rcases hedge with ⟨L, Q, R, hv_B, hsub⟩
      have hedge' : IsRightRotEdge B u v := ⟨L, Q, R, hv_B, hsub⟩
      set S := (preorderSummarySet B remBlocks 1 : Set ℕ)
      set S' := (preorderSummarySet B' remBlocks 1 : Set ℕ)
      have hvS : v ∈ S :=
        (mem_preorderSummarySet_one_iff hB remBlocks v).mpr ⟨subblock1 subs c₀, hc₀_rem, hfb_v⟩
      have hfb'_u : firstInBlock? B' (subblock1 subs c₀) = some u := by
        rw [(firstInBlock?_rotateRightEdge hB huv hedge' (subblock1 subs c₀)).2
              ⟨hu_in_Sc₀, hv_in_Sc₀⟩]
        simp [hfb_v]
      have huS' : u ∈ S' :=
        (mem_preorderSummarySet_one_iff hB' remBlocks u).mpr ⟨subblock1 subs c₀, hc₀_rem, hfb'_u⟩
      have honly_c₀_B : ∀ w ∈ (subblock1 subs c₀).toSet, w ∈ S → w = v := by
        intro w hwC hwS
        obtain ⟨C, hC, hfb_w⟩ := (mem_preorderSummarySet_one_iff hB remBlocks w).mp hwS
        obtain ⟨c', hc', rfl⟩ := (remBlocks_mem_iff ℓ X hp_len C).mp hC
        have hc'_full : c' ∈ Finset.Icc 1 subs.length :=
          Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc').1; omega, (Finset.mem_Icc.mp hc').2⟩
        have hidx1 : f w = c' :=
          ((hsub_c c' hc'_full).2.2.2.2.2 w (Finset.mem_Icc.mpr (firstInBlock?_mem hfb_w).2)).1
        have hidx2 : f w = c₀ :=
          ((hsub_c c₀ hc1_Icc).2.2.2.2.2 w (Finset.mem_Icc.mpr hwC)).1
        have hc_eq' : c' = c₀ := hidx1.symm.trans hidx2
        subst hc_eq'
        rw [hfb_v] at hfb_w; injection hfb_w with hwv; exact hwv.symm
      have honly_c₀_B' : ∀ w ∈ (subblock1 subs c₀).toSet, w ∈ S' → w = u := by
        intro w hwC hwS'
        obtain ⟨C, hC, hfb_w⟩ := (mem_preorderSummarySet_one_iff hB' remBlocks w).mp hwS'
        obtain ⟨c', hc', rfl⟩ := (remBlocks_mem_iff ℓ X hp_len C).mp hC
        have hc'_full : c' ∈ Finset.Icc 1 subs.length :=
          Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc').1; omega, (Finset.mem_Icc.mp hc').2⟩
        have hidx1 : f w = c' :=
          ((hsub_c c' hc'_full).2.2.2.2.2 w (Finset.mem_Icc.mpr (firstInBlock?_mem hfb_w).2)).1
        have hidx2 : f w = c₀ :=
          ((hsub_c c₀ hc1_Icc).2.2.2.2.2 w (Finset.mem_Icc.mpr hwC)).1
        have hc_eq' : c' = c₀ := hidx1.symm.trans hidx2
        subst hc_eq'
        rw [hfb'_u] at hfb_w; injection hfb_w with hwu; exact hwu.symm
      have huS_not : u ∉ S := fun h => ne_of_lt huv (honly_c₀_B u hu_in_Sc₀ h)
      have hvS'_not : v ∉ S' := fun h => ne_of_gt huv (honly_c₀_B' v hv_in_Sc₀ h)
      have hiff : ∀ w, w ≠ u → w ≠ v → (w ∈ S' ↔ w ∈ S) := by
        intro w hwu hwv
        change w ∈ preorderSummarySet B' remBlocks 1 ↔ w ∈ preorderSummarySet B remBlocks 1
        rw [mem_preorderSummarySet_one_iff hB', mem_preorderSummarySet_one_iff hB]
        constructor
        · rintro ⟨C, hC, hfb'⟩
          by_cases hC_eq : C = subblock1 subs c₀
          · subst hC_eq; rw [hfb'_u] at hfb'; injection hfb' with heq; exact absurd heq.symm hwu
          · rw [(firstInBlock?_rotateRightEdge hB huv hedge' C).1
                  (hother_not_both C hC hC_eq)] at hfb'
            exact ⟨C, hC, hfb'⟩
        · rintro ⟨C, hC, hfb⟩
          by_cases hC_eq : C = subblock1 subs c₀
          · subst hC_eq; rw [hfb_v] at hfb; injection hfb with heq; exact absurd heq.symm hwv
          · refine ⟨C, hC, ?_⟩
            rw [(firstInBlock?_rotateRightEdge hB huv hedge' C).1
                  (hother_not_both C hC hC_eq)]
            exact hfb
      have hQ : ∀ q ∈ Q, q ∉ S := by
        intro q hq hqS
        have hsub_bst := subtreeAtKey_isBST hB v
        rw [hsub] at hsub_bst
        obtain ⟨hu_bst, _, hlt_v, _⟩ := (isBST_node_iff v (.node u L Q) R).mp hsub_bst
        obtain ⟨_, _, _, hgt_u⟩ := (isBST_node_iff u L Q).mp hu_bst
        have huq : u < q := hgt_u q hq
        have hqv : q < v := hlt_v q (.right hq)
        have hq_Sc₀ : q ∈ (subblock1 subs c₀).toSet :=
          ⟨le_trans hu_in_Sc₀.1 (le_of_lt huq), le_trans (le_of_lt hqv) hv_in_Sc₀.2⟩
        exact ne_of_lt hqv (honly_c₀_B q hq_Sc₀ hqS)
      have hmap_eq : (preorderSummaryBST B' remBlocks 1).map f =
          (preorderSummaryBST B remBlocks 1).map f :=
        restrictTree_rotateRightEdge_swap_map hB huv hv_B hsub hc_eq hvS huS_not huS' hvS'_not
          hiff hQ
      rw [hmap_eq]
      exact .refl
    · have hS_eq : (preorderSummarySet B' remBlocks 1 : Set ℕ) =
          (preorderSummarySet B remBlocks 1 : Set ℕ) := by
        ext w
        change w ∈ preorderSummarySet B' remBlocks 1 ↔ w ∈ preorderSummarySet B remBlocks 1
        rw [mem_preorderSummarySet_one_iff hB', mem_preorderSummarySet_one_iff hB]
        refine exists_congr (fun C => and_congr_right (fun hC => ?_))
        by_cases hC_eq : C = subblock1 subs c₀
        · subst hC_eq
          rw [(firstInBlock?_rotateRightEdge hB huv hedge (subblock1 subs c₀)).2
                ⟨hu_in_Sc₀, hv_in_Sc₀⟩]
          simp [hfb_v]
        · rw [(firstInBlock?_rotateRightEdge hB huv hedge C).1 (hother_not_both C hC hC_eq)]
      have hv_not_S : v ∉ (preorderSummarySet B remBlocks 1 : Set ℕ) := by
        intro hvS
        obtain ⟨C, hC, hfb⟩ := (mem_preorderSummarySet_one_iff hB remBlocks v).mp hvS
        obtain ⟨c', hc', rfl⟩ := (remBlocks_mem_iff ℓ X hp_len C).mp hC
        have hc'_full : c' ∈ Finset.Icc 1 subs.length :=
          Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc').1; omega, (Finset.mem_Icc.mp hc').2⟩
        have hidx1 : f v = c' :=
          ((hsub_c c' hc'_full).2.2.2.2.2 v (Finset.mem_Icc.mpr (firstInBlock?_mem hfb).2)).1
        have hc_eq' : c' = c₀ := hidx1.symm.trans hc_eq.symm
        subst hc_eq'
        exact hfb_v hfb
      rw [hS_eq] at hLCA_B'
      have htree_eq : preorderSummaryBST B' remBlocks 1 = preorderSummaryBST B remBlocks 1 := by
        unfold preorderSummaryBST
        rw [hS_eq]
        exact (h_3_1_rightRot h_3_1 hB hLCA_B huv hedge hLCA_B').2 (fun h => hv_not_S h.2)
      rw [htree_eq]
      exact .refl
  · have hnot_same : ∀ C ∈ remBlocks, ¬ (u ∈ C.toSet ∧ v ∈ C.toSet) := by
      rintro C hC ⟨huC, hvC⟩
      obtain ⟨c', hc', rfl⟩ := (remBlocks_mem_iff ℓ X hp_len C).mp hC
      have hc'_full : c' ∈ Finset.Icc 1 subs.length :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc').1; omega, (Finset.mem_Icc.mp hc').2⟩
      have h1 := ((hsub_c c' hc'_full).2.2.2.2.2 u (Finset.mem_Icc.mpr huC)).1
      have h2 := ((hsub_c c' hc'_full).2.2.2.2.2 v (Finset.mem_Icc.mpr hvC)).1
      exact hc_eq (h1.trans h2.symm)
    have hS_eq : (preorderSummarySet B' remBlocks 1 : Set ℕ) =
        (preorderSummarySet B remBlocks 1 : Set ℕ) := by
      ext w
      change w ∈ preorderSummarySet B' remBlocks 1 ↔ w ∈ preorderSummarySet B remBlocks 1
      rw [mem_preorderSummarySet_one_iff hB', mem_preorderSummarySet_one_iff hB]
      refine exists_congr (fun C => and_congr_right (fun hC => ?_))
      rw [(firstInBlock?_rotateRightEdge hB huv hedge C).1 (hnot_same C hC)]
    rw [hS_eq] at hLCA_B'
    obtain ⟨hboth, hnot⟩ := h_3_1_rightRot h_3_1 hB hLCA_B huv hedge hLCA_B'
    by_cases h_in_S : u ∈ (preorderSummarySet B remBlocks 1 : Set ℕ) ∧
        v ∈ (preorderSummarySet B remBlocks 1 : Set ℕ)
    · obtain ⟨hedge_T, hrot_T⟩ := hboth h_in_S
      have htree_rot : preorderSummaryBST B' remBlocks 1 =
          rotateRightEdge (preorderSummaryBST B remBlocks 1) u v := by
        unfold preorderSummaryBST
        rw [hS_eq]
        exact hrot_T
      obtain ⟨hfuv, hedge_G, hrot_G⟩ :=
        map_isRightRotEdge_and_rotateRightEdge hT_bst hmono_B huv hedge_T
      have hG'_eq : (preorderSummaryBST B' remBlocks 1).map f =
          rotateRightEdge ((preorderSummaryBST B remBlocks 1).map f) (f u) (f v) := by
        rw [htree_rot, hrot_G]
      refine ⟨hG'_eq ▸ rightRotReachable_single hfuv hedge_G, fun _ _ _ => ⟨hedge_G, hG'_eq⟩⟩
    · have htree_eq : preorderSummaryBST B' remBlocks 1 = preorderSummaryBST B remBlocks 1 := by
        unfold preorderSummaryBST
        rw [hS_eq]
        exact hnot h_in_S
      refine ⟨by rw [htree_eq]; exact .refl, fun _ huS hvS => absurd ⟨huS, hvS⟩ h_in_S⟩

theorem summary_reachable_proj (h_3_1 : Ty_lem_3_1)
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1)
    {B₁ B₂ : BinaryTree ℕ} (hB₁ : B₁.IsBST)
    (hB₁_keys : keyFinset B₁ =
      Finset.Icc ((subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).hi + 1)
        X.hi)
    (hreach : RightRotReachable B₁ B₂) :
    let subs := childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X
    let remBlocks := subs.drop p
    let f := subblockIndex1 subs
    RightRotReachable
      ((preorderSummaryBST B₁ remBlocks 1).map f)
      ((preorderSummaryBST B₂ remBlocks 1).map f) := by
  dsimp only
  induction hreach with
  | refl => exact .refl
  | tail hprev hstep ih =>
    rcases hstep with ⟨u, v, huv, hedge, rfl⟩
    rename_i mid
    obtain ⟨hmid_bst, hmid_mem⟩ := rightRotReachable_isBST_and_mem hB₁ hprev
    have hmid_keys : keyFinset mid =
        Finset.Icc ((subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).hi + 1)
          X.hi := by
      rw [← hB₁_keys]; ext w; simp [← mem_iff_mem_keyFinset, hmid_mem]
    exact ih.trans (summary_singleRot_proj h_3_1 hValid ℓ X hX hp1 hp2 hmid_bst hmid_keys
      huv hedge).1

/-! ## Section 5: `vXp` Projection, Phase Bridge, and `topEmbedPhase` Trajectory Lifting -/

theorem firstInBlock?_of_leftSpine_next_gt {H : BinaryTree ℕ} (hH : H.IsBST)
    {C : IntervalBlock} {idx w w_next : ℕ}
    (hw : (leftSpine H)[idx]? = some w)
    (hw_next : (leftSpine H)[idx + 1]? = some w_next)
    (hwC : w ∈ C.toSet)
    (hhi_lt : C.hi < w_next) :
    firstInBlock? H C = some w := by
  induction H with
  | nil => simp [leftSpine] at hw
  | node k l r ihl _ =>
    obtain ⟨hl_bst, _, hlt, _⟩ := (isBST_node_iff k l r).mp hH
    obtain ⟨hidx1_len, _⟩ := List.getElem?_eq_some_iff.mp hw_next
    simp only [leftSpine, List.length_append, List.length_singleton] at hidx1_len
    have hidx_l : idx < (leftSpine l).length := by omega
    have hw_l : (leftSpine l)[idx]? = some w := by
      rw [leftSpine, List.getElem?_append_left hidx_l] at hw
      exact hw
    have hw_lt_k : w < k := hlt w (mem_of_mem_leftSpine (List.mem_of_getElem? hw_l))
    have hwC_bounds : C.lo ≤ w ∧ w ≤ C.hi := hwC
    by_cases hidx1_l : idx + 1 < (leftSpine l).length
    · have hw_next_l : (leftSpine l)[idx + 1]? = some w_next := by
        rw [leftSpine, List.getElem?_append_left hidx1_l] at hw_next
        exact hw_next
      have hwn_lt_k : w_next < k :=
        hlt w_next (mem_of_mem_leftSpine (List.mem_of_getElem? hw_next_l))
      have hk_not_C : ¬ (C.lo ≤ k ∧ k ≤ C.hi) := by omega
      have hk_not_lt : ¬ k < C.lo := by omega
      simp only [firstInBlock?, hk_not_C, hk_not_lt, ↓reduceIte]
      exact ihl hl_bst hw_l hw_next_l
    · have hidx1_eq : idx + 1 = (leftSpine l).length := by omega
      have hk_eq : k = w_next := by
        rw [leftSpine, hidx1_eq, List.getElem?_append_right le_rfl] at hw_next
        simpa using hw_next
      have hk_not_C : ¬ (C.lo ≤ k ∧ k ≤ C.hi) := by omega
      have hk_not_lt : ¬ k < C.lo := by omega
      cases l with
      | nil => simp [leftSpine] at hidx_l
      | node lk ll lr =>
        have hidx_ll : idx = (leftSpine ll).length := by
          simp [leftSpine] at hidx1_eq; omega
        have hlk_eq : lk = w := by
          rw [leftSpine, hidx_ll, List.getElem?_append_right le_rfl] at hw_l
          simpa using hw_l
        have hstep : firstInBlock? (.node k (.node lk ll lr) r) C =
            firstInBlock? (.node lk ll lr) C := by
          conv_lhs => unfold firstInBlock?
          simp only [hk_not_C, hk_not_lt, ↓reduceIte]
        rw [hstep, hlk_eq]
        unfold firstInBlock?
        simp only [hwC_bounds, and_self, ↓reduceIte]

theorem getElem_tail_of_succ_getElem? {α : Type} {xs : List α} {k : ℕ} {v : α}
    (h : xs[k + 1]? = some v) :
    ∃ hk : k < xs.tail.length, xs.tail[k]'hk = v := by
  cases xs with
  | nil => simp at h
  | cons _ tl =>
    simp only [List.getElem?_cons_succ] at h
    exact List.getElem?_eq_some_iff.mp h

theorem vXp_proj_step (h_3_1 : Ty_lem_3_1)
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1)
    {e : InternalPopRot}
    (he : e ∈ vXp P proc (scaleTreePartitionChain T P M) (ℓ.val + 1) X p) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    let K_X := subs.length
    let b := subblockIndex1 subs e.x
    let q := subblockIndex1 subs e.y
    let Gs := phaseSummaryBST P proc chain ℓ_val X p e.stepIdx
    let GsNext := phaseSummaryBST P proc chain ℓ_val X p (e.stepIdx + 1)
    p + 1 ≤ b ∧ b < q ∧ q ≤ K_X ∧
    b ∈ leftSpine Gs ∧ q ∈ leftSpine Gs ∧
    IsRightRotEdge Gs b q ∧
    RightRotReachable (rotateRightEdge Gs b q) GsNext := by
  dsimp only
  have hK2 := validScaleTree_K_X_ge_two hValid ℓ X hX
  obtain ⟨hX1, _, hXP, _, hsub_c, hlt_idx, hconsec, _, _, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨_, htau_le_tEnd, htEnd_lt, _⟩ := tauEmpty_window_bounds hValid proc ℓ X hX hp1 hp2
  obtain ⟨he_rInt, _, hτ_lt_tau, hp1_b, hb_lt_q, hq_le_K, hx_Sb, hy_Sq, hSb_lt_y, hSq_lt_z⟩ :=
    mem_vXp_props hValid proc ℓ X hX hp1 hp2 he
  obtain ⟨_, hpop, hpop_mono, _, _⟩ := popStepIdx_and_insStep_props proc
  obtain ⟨hproc_inv, hproc_step⟩ := proc_tree_bst_and_step_keys proc
  obtain ⟨hBp_all, _⟩ := phaseBlockBST_props h_3_1 hValid proc ℓ X hX hp1 hp2
  set chain := scaleTreePartitionChain T P M
  set subs := childSubblocks (chain ℓ.succ) X
  have hp_len : p ≤ subs.length := by omega
  have hp1_len : p + 1 ≤ subs.length := by omega
  obtain ⟨_, _, hX_Splo, hSplo_hi, hSphi_X, _⟩ := hsub_c p (Finset.mem_Icc.mpr ⟨hp1, hp_len⟩)
  obtain ⟨_, _, hX_Sp1lo, _, hSp1hi_X, _⟩ :=
    hsub_c (p + 1) (Finset.mem_Icc.mpr ⟨by omega, hp1_len⟩)
  have hlink := hconsec p hp1 hp1_len
  set Sp := subblock1 subs p
  set Sp1 := subblock1 subs (p + 1)
  set tEnd := proc.popStepIdx Sp1.lo
  set b := subblockIndex1 subs e.x
  set q := subblockIndex1 subs e.y
  set τ := e.stepIdx
  set I_Xp : Set ℕ := {u : ℕ | Sp.hi < u ∧ u ≤ X.hi}
  have hτ_lt_tEnd : τ < tEnd := lt_of_lt_of_le hτ_lt_tau htau_le_tEnd
  have hτ_le_tEnd : τ ≤ tEnd := le_of_lt hτ_lt_tEnd
  have hτ1_le_tEnd : τ + 1 ≤ tEnd := hτ_lt_tEnd
  obtain ⟨hτ_r, b1, hop_e, hb1_e, hh_eq, hj1, hjh, hx_sub, hy_sub, hz_sub⟩ :=
    (mem_rInt_iff proc e).mp he_rInt
  change proc.steps[τ]'hτ_r = .pop e.s at hop_e
  change proc.b1At τ = some b1 at hb1_e
  have hlaws := cartesianExt_step_laws proc hτ_r
  rw [hop_e] at hlaws
  rcases hlaws with ⟨b1', hb1', hb1'_ls, hls_ext, hmin_ext, hext_next, _⟩
  rw [hb1_e] at hb1'
  injection hb1' with hb1_eq; subst hb1_eq
  obtain ⟨ht_bst, _⟩ := hproc_inv τ (le_of_lt hτ_r)
  obtain ⟨hext_bst, _⟩ := cartesianExt_isBST_and_keys proc (le_of_lt hτ_r)
  set sub := takeThrough (leftSpine (proc.treeAt τ)) b1
  obtain ⟨⟨suff_ls, hsuff_eq⟩, hne_sub, _, _, _, _⟩ :=
    takeThrough_props (leftSpine_pairwise_lt ht_bst) hb1'_ls
  have hls_ext_sub : leftSpine (cartesianExt proc τ) = sub ++ suff_ls :=
    hls_ext.trans hsuff_eq.symm
  have hz_idx_lt : 2 * e.j + 1 < sub.length := (List.getElem?_eq_some_iff.mp hz_sub).1
  have hx_ls_ext : (leftSpine (cartesianExt proc τ))[2 * e.j - 1]? = some e.x := by
    rw [hls_ext_sub, List.getElem?_append_left (by omega)]
    exact hx_sub
  have hy_ls_ext : (leftSpine (cartesianExt proc τ))[(2 * e.j - 1) + 1]? = some e.y := by
    have hidx : (2 * e.j - 1) + 1 = 2 * e.j := by omega
    rw [hidx, hls_ext_sub, List.getElem?_append_left (by omega)]
    exact hy_sub
  have hy_ls_ext' : (leftSpine (cartesianExt proc τ))[2 * e.j]? = some e.y := by
    have hidx : (2 * e.j - 1) + 1 = 2 * e.j := by omega
    rwa [hidx] at hy_ls_ext
  have hz_ls_ext : (leftSpine (cartesianExt proc τ))[2 * e.j + 1]? = some e.z := by
    rw [hls_ext_sub, List.getElem?_append_left hz_idx_lt]
    exact hz_sub
  have hfb_ext_x : firstInBlock? (cartesianExt proc τ) (subblock1 subs b) = some e.x :=
    firstInBlock?_of_leftSpine_next_gt hext_bst hx_ls_ext hy_ls_ext
      (Finset.mem_Icc.mp hx_Sb) hSb_lt_y
  have hfb_ext_y : firstInBlock? (cartesianExt proc τ) (subblock1 subs q) = some e.y :=
    firstInBlock?_of_leftSpine_next_gt hext_bst hy_ls_ext' hz_ls_ext
      (Finset.mem_Icc.mp hy_Sq) hSq_lt_z
  set Bp := phaseBlockBST P proc chain (ℓ.val + 1) X p τ
  set BpNext := phaseBlockBST P proc chain (ℓ.val + 1) X p (τ + 1)
  obtain ⟨hBp_bst, hBp_keys⟩ := hBp_all τ hτ_le_tEnd
  have hSc_sub_I : ∀ c ∈ Finset.Icc (p + 1) subs.length, (subblock1 subs c).toSet ⊆ I_Xp := by
    intro c hc w hw
    have hc_bounds := Finset.mem_Icc.mp hc
    have hc_full : c ∈ Finset.Icc 1 subs.length := Finset.mem_Icc.mpr ⟨by omega, hc_bounds.2⟩
    obtain ⟨_, _, _, _, hSchi_X, _⟩ := hsub_c c hc_full
    have hSp_lt_Sc : Sp.hi < (subblock1 subs c).lo := hlt_idx p c hp1 (by omega) hc_bounds.2
    change (subblock1 subs c).lo ≤ w ∧ w ≤ (subblock1 subs c).hi at hw
    exact ⟨by omega, by omega⟩
  have hfb_Bp_eq : ∀ c ∈ Finset.Icc (p + 1) subs.length,
      firstInBlock? Bp (subblock1 subs c) = firstInBlock? (cartesianExt proc τ) (subblock1 subs c) := by
    intro c hc
    rw [← treeRootKey?_restrictTree_eq_firstInBlock? hBp_bst,
        ← treeRootKey?_restrictTree_eq_firstInBlock? hext_bst,
        phaseBlockBST_eq proc chain ℓ X p τ,
        restrictTree_restrictTree_of_subset h_3_1 hext_bst
          (isLCAClosed_interval_oc _ _ _) (hSc_sub_I c hc)]
  have hb_Icc : b ∈ Finset.Icc (p + 1) subs.length := Finset.mem_Icc.mpr ⟨hp1_b, by omega⟩
  have hq_Icc : q ∈ Finset.Icc (p + 1) subs.length := Finset.mem_Icc.mpr ⟨by omega, hq_le_K⟩
  set remBlocks := subs.drop p
  have hfb_Bp_x : firstInBlock? Bp (subblock1 subs b) = some e.x :=
    (hfb_Bp_eq b hb_Icc).trans hfb_ext_x
  have hfb_Bp_y : firstInBlock? Bp (subblock1 subs q) = some e.y :=
    (hfb_Bp_eq q hq_Icc).trans hfb_ext_y
  have hx_sum : e.x ∈ preorderSummarySet Bp remBlocks 1 :=
    (mem_preorderSummarySet_one_iff hBp_bst remBlocks e.x).mpr
      ⟨subblock1 subs b, (remBlocks_mem_iff ℓ X hp_len _).mpr ⟨b, hb_Icc, rfl⟩, hfb_Bp_x⟩
  have hy_sum : e.y ∈ preorderSummarySet Bp remBlocks 1 :=
    (mem_preorderSummarySet_one_iff hBp_bst remBlocks e.y).mpr
      ⟨subblock1 subs q, (remBlocks_mem_iff ℓ X hp_len _).mpr ⟨q, hq_Icc, rfl⟩, hfb_Bp_y⟩
  obtain ⟨hLCA_sum, _, _, _, _⟩ :=
    summary_bst_and_keys_of_blockBST h_3_1 hValid ℓ X hX hp1 hp2 hBp_bst hBp_keys
  have hx_IXp : e.x ∈ I_Xp := hSc_sub_I b hb_Icc (Finset.mem_Icc.mp hx_Sb)
  have hy_IXp : e.y ∈ I_Xp := hSc_sub_I q hq_Icc (Finset.mem_Icc.mp hy_Sq)
  have hx_ls_Bp : e.x ∈ leftSpine Bp := by
    rw [show Bp = restrictTree (cartesianExt proc τ) I_Xp from phaseBlockBST_eq proc chain ℓ X p τ]
    exact mem_leftSpine_restrictTree hext_bst (isLCAClosed_interval_oc _ _ _)
      (List.mem_of_getElem? hx_ls_ext) hx_IXp
  have hy_ls_Bp : e.y ∈ leftSpine Bp := by
    rw [show Bp = restrictTree (cartesianExt proc τ) I_Xp from phaseBlockBST_eq proc chain ℓ X p τ]
    exact mem_leftSpine_restrictTree hext_bst (isLCAClosed_interval_oc _ _ _)
      (List.mem_of_getElem? hy_ls_ext') hy_IXp
  have hx_ls_T : e.x ∈ leftSpine (preorderSummaryBST Bp remBlocks 1) :=
    mem_leftSpine_restrictTree hBp_bst hLCA_sum hx_ls_Bp hx_sum
  have hy_ls_T : e.y ∈ leftSpine (preorderSummaryBST Bp remBlocks 1) :=
    mem_leftSpine_restrictTree hBp_bst hLCA_sum hy_ls_Bp hy_sum
  set Gs := phaseSummaryBST P proc chain (ℓ.val + 1) X p τ
  set GsNext := phaseSummaryBST P proc chain (ℓ.val + 1) X p (τ + 1)
  have hGs_eq : Gs = (preorderSummaryBST Bp remBlocks 1).map (subblockIndex1 subs) :=
    phaseSummaryBST_eq proc chain ℓ X p τ
  have hGsNext_eq : GsNext = (preorderSummaryBST BpNext remBlocks 1).map (subblockIndex1 subs) :=
    phaseSummaryBST_eq proc chain ℓ X p (τ + 1)
  have hb_ls_Gs : b ∈ leftSpine Gs := by
    rw [hGs_eq, leftSpine_map]
    exact List.mem_map_of_mem hx_ls_T
  have hq_ls_Gs : q ∈ leftSpine Gs := by
    rw [hGs_eq, leftSpine_map]
    exact List.mem_map_of_mem hy_ls_T
  -- Splice minimum of `cartesianExt proc τ` and pull `(e.x, e.y)` to front
  set t₀ := spliceMin (cartesianExt proc τ)
  have hstep_s := hproc_step τ hτ_r
  rw [hop_e] at hstep_s
  have hs_Icc : e.s ∈ Finset.Icc 1 P := (hproc_inv τ (le_of_lt hτ_r)).2 hstep_s.1
  have hSp1lo_Icc : Sp1.lo ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hτ_eq_pop : τ = proc.popStepIdx e.s :=
    ((hpop e.s hs_Icc).2.2 τ hτ_r).mp (getElem?_of_getElem hτ_r hop_e)
  have hs_lt_Sp1 : e.s < Sp1.lo :=
    (hpop_mono e.s hs_Icc Sp1.lo hSp1lo_Icc).1.mpr (by omega)
  have hs_not_I : e.s ∉ I_Xp := by
    change ¬ (Sp.hi < e.s ∧ e.s ≤ X.hi)
    dsimp only [Sp, Sp1] at hlink hs_lt_Sp1 ⊢
    omega
  have hext_ne : cartesianExt proc τ ≠ .nil := by
    intro hnil; rw [hnil] at hmin_ext; simp [BinaryTree.minKey?] at hmin_ext
  have ht₀_proj : restrictTree t₀ I_Xp = Bp := by
    rw [show Bp = restrictTree (cartesianExt proc τ) I_Xp from phaseBlockBST_eq proc chain ℓ X p τ]
    exact ((h_3_1 (cartesianExt proc τ) I_Xp hext_bst
      (isLCAClosed_interval_oc _ _ _)).2.2 hext_ne).1.2 e.s hmin_ext |>.2 hs_not_I
  obtain ⟨ht₀_bst, _⟩ := spliceMin_spec hext_bst hmin_ext
  have htail_eq : (leftSpine (proc.treeAt τ)).tail = sub.tail ++ suff_ls := by
    rw [← hsuff_eq]
    dsimp only [sub]
    cases hsub : takeThrough (leftSpine (proc.treeAt τ)) b1 with
    | nil => exact absurd hsub hne_sub
    | cons _ _ => rfl
  obtain ⟨pref_ext, hls_sp_ext⟩ := leftSpine_spliceMin_suffix (cartesianExt proc τ) hext_ne
  have hls_t₀ : leftSpine t₀ = pref_ext ++ sub.tail ++ suff_ls := by
    rw [hls_sp_ext, hls_ext, htail_eq, List.append_assoc]
  have hx_sub' : sub[2 * (e.j - 1) + 1]? = some e.x := by
    have : 2 * (e.j - 1) + 1 = 2 * e.j - 1 := by omega
    rwa [this]
  have hy_sub' : sub[(2 * (e.j - 1) + 1) + 1]? = some e.y := by
    have : (2 * (e.j - 1) + 1) + 1 = 2 * e.j := by omega
    rwa [this]
  obtain ⟨hx_tl_lt, hx_tl_eq⟩ := getElem_tail_of_succ_getElem? hx_sub'
  obtain ⟨hy_tl_lt, hy_tl_eq⟩ := getElem_tail_of_succ_getElem? hy_sub'
  have hidx_lt : e.j - 1 < (sub.length - 1 - 1) / 2 := by omega
  obtain ⟨hxy_lt, hedge_t₀, hreach_t₀⟩ := pull_pair_to_front_reachable
    (e.j - 1) ((sub.length - 1 - 1) / 2) sub.tail t₀ pref_ext suff_ls
    ht₀_bst hls_t₀ hidx_lt hy_tl_lt
  rw [hx_tl_eq, hy_tl_eq] at hxy_lt hedge_t₀ hreach_t₀
  rw [← hext_next] at hreach_t₀
  obtain ⟨hedge_Bp, hrot_Bp⟩ :=
    (h_3_1_rightRot h_3_1 ht₀_bst (isLCAClosed_interval_oc _ _ _) hxy_lt hedge_t₀
      (isLCAClosed_interval_oc _ _ _)).1 ⟨hx_IXp, hy_IXp⟩
  rw [ht₀_proj] at hedge_Bp hrot_Bp
  have hreach_Bp : RightRotReachable (rotateRightEdge Bp e.x e.y) BpNext := by
    have hr := h_3_1_rightRot_reachable (S := I_Xp) h_3_1 (rotateRightEdge_isBST ht₀_bst e.x e.y)
      (fun t _ => isLCAClosed_interval_oc t Sp.hi X.hi) hreach_t₀
    rwa [hrot_Bp, ← phaseBlockBST_eq proc chain ℓ X p (τ + 1)] at hr
  obtain ⟨hedge_Gs, hG_rot⟩ :=
    (summary_singleRot_proj h_3_1 hValid ℓ X hX hp1 hp2 hBp_bst hBp_keys hxy_lt hedge_Bp).2
      hb_lt_q hx_sum hy_sum
  rw [← hGs_eq] at hedge_Gs hG_rot
  have hBmid_bst : (rotateRightEdge Bp e.x e.y).IsBST := rotateRightEdge_isBST hBp_bst e.x e.y
  have hBmid_keys : keyFinset (rotateRightEdge Bp e.x e.y) = Finset.Icc (Sp.hi + 1) X.hi := by
    rw [keyFinset_rotateRightEdge, hBp_keys]
  have hreach_Gs : RightRotReachable (rotateRightEdge Gs b q) GsNext := by
    have hr := summary_reachable_proj h_3_1 hValid ℓ X hX hp1 hp2 hBmid_bst hBmid_keys hreach_Bp
    dsimp only at hr
    change RightRotReachable
      ((preorderSummaryBST (rotateRightEdge Bp e.x e.y) remBlocks 1).map (subblockIndex1 subs))
      ((preorderSummaryBST BpNext remBlocks 1).map (subblockIndex1 subs)) at hr
    change ((preorderSummaryBST (rotateRightEdge Bp e.x e.y) remBlocks 1).map
      (subblockIndex1 subs)) = rotateRightEdge Gs b q at hG_rot
    rwa [hG_rot, ← hGsNext_eq] at hr
  exact ⟨hp1_b, hb_lt_q, hq_le_K, hb_ls_Gs, hq_ls_Gs, hedge_Gs, hreach_Gs⟩

theorem restrictTree_eq_self_of_forall_mem {α : Type} (t : BinaryTree α) (S : Set α)
    (hall : ∀ x ∈ t, x ∈ S) : restrictTree t S = t := by
  induction t with
  | nil => rfl
  | node u A B ihA ihB =>
    have hu : u ∈ S := hall u .here
    simp [restrictTree, hu, ihA (fun x hx => hall x (.left hx)),
      ihB (fun x hx => hall x (.right hx))]

theorem range'_succ_append (a m : ℕ) :
    List.range' a (m + 1) = List.range' a m ++ [a + m] := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    change a :: List.range' (a + 1) (m + 1) = a :: (List.range' (a + 1) m ++ [a + (m + 1)])
    rw [ih (a + 1)]
    have : a + 1 + m = a + (m + 1) := by omega
    rw [this]

theorem range'_foldr_bst_mem_and_rightRotReachable :
    ∀ (m a : ℕ) {H₁ H₂ : BinaryTree ℕ},
      H₁.IsBST → (∀ v ∈ H₁, a + m ≤ v) → RightRotReachable H₁ H₂ →
      let emb := fun X => (List.range' a m).foldr (fun c acc => BinaryTree.node c .nil acc) X
      (emb H₁).IsBST ∧
      (∀ v, v ∈ emb H₁ ↔ (a ≤ v ∧ v < a + m) ∨ v ∈ H₁) ∧
      RightRotReachable (emb H₁) (emb H₂)
  | 0, a, H₁, H₂, hH₁, _, hreach => by
    dsimp only [List.range', List.foldr_nil]
    refine ⟨hH₁, fun v => ?_, hreach⟩
    constructor
    · intro hv; exact Or.inr hv
    · rintro (h | hv)
      · omega
      · exact hv
  | m + 1, a, H₁, H₂, hH₁, hge, hreach => by
    dsimp only [List.range', List.foldr_cons]
    have hge' : ∀ v ∈ H₁, (a + 1) + m ≤ v := by
      intro v hv; have := hge v hv; omega
    obtain ⟨hemb_bst, hemb_mem, hemb_reach⟩ :=
      range'_foldr_bst_mem_and_rightRotReachable m (a + 1) hH₁ hge' hreach
    set emb' := fun X => (List.range' (a + 1) m).foldr (fun c acc => BinaryTree.node c .nil acc) X
    have hgt_a : ∀ v ∈ emb' H₁, a < v := by
      intro v hv
      rcases (hemb_mem v).mp hv with ⟨h1, _⟩ | hvH
      · omega
      · have := hge v hvH; omega
    have hnode_bst : (BinaryTree.node a .nil (emb' H₁)).IsBST :=
      (isBST_node_iff a .nil (emb' H₁)).mpr
        ⟨IsBSTAux.nil none none, hemb_bst, by simp, hgt_a⟩
    refine ⟨hnode_bst, fun v => ?_, rightRotReachable_node_right hemb_bst hgt_a hemb_reach⟩
    rw [BinaryTree.mem_node_iff]
    simp only [BinaryTree.not_mem_nil, false_or]
    rw [hemb_mem v]
    constructor
    · rintro (rfl | ⟨h1, h2⟩ | hvH)
      · exact Or.inl ⟨le_rfl, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr hvH
    · rintro (⟨h1, h2⟩ | hvH)
      · rcases eq_or_lt_of_le h1 with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr hvH)

theorem topEmbedPhase_bridge (h_3_1 : Ty_lem_3_1)
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ}
    (hp : p ∈ Finset.Icc 1 ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 2)) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    let tBridge := proc.popStepIdx (subblock1 subs (p + 1)).lo
    RightRotReachable
      (topEmbedPhase p (phaseSummaryBST P proc chain ℓ_val X p tBridge))
      (topEmbedPhase (p + 1) (phaseSummaryBST P proc chain ℓ_val X (p + 1) tBridge)) := by
  dsimp only
  have hp_bounds := Finset.mem_Icc.mp hp
  have hp1 : 1 ≤ p := hp_bounds.1
  have hK3 : 3 ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length := by omega
  have hp_le_K1 : p ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1 := by
    omega
  have hp1_ge1 : 1 ≤ p + 1 := by omega
  have hp1_le_K1 : p + 1 ≤
      (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1 := by omega
  obtain ⟨hX1, _, hXP, _, hsub_c, hlt_idx, hconsec, _, _, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨_, _, htBridge_lt_len, _⟩ := tauEmpty_window_bounds hValid proc ℓ X hX hp1 hp_le_K1
  obtain ⟨_, _, hpop_mono, _, _⟩ := popStepIdx_and_insStep_props proc
  obtain ⟨hBp_all, _⟩ := phaseBlockBST_props h_3_1 hValid proc ℓ X hX hp1 hp_le_K1
  obtain ⟨hBp1_all, _⟩ := phaseBlockBST_props h_3_1 hValid proc ℓ X hX hp1_ge1 hp1_le_K1
  set chain := scaleTreePartitionChain T P M
  set subs := childSubblocks (chain ℓ.succ) X
  have hp_len : p ≤ subs.length := by omega
  have hp1_len : p + 1 ≤ subs.length := by omega
  have hp2_len : p + 2 ≤ subs.length := by omega
  obtain ⟨_, _, hX_Sp1lo, hSp1lo_hi, hSp1hi_X, _⟩ :=
    hsub_c (p + 1) (Finset.mem_Icc.mpr ⟨hp1_ge1, hp1_len⟩)
  obtain ⟨_, _, hX_Sp2lo, hSp2lo_hi, hSp2hi_X, _⟩ :=
    hsub_c (p + 2) (Finset.mem_Icc.mpr ⟨by omega, hp2_len⟩)
  have hlink_p : (subblock1 subs p).hi + 1 = (subblock1 subs (p + 1)).lo := hconsec p hp1 hp1_len
  have hSp1_lt_Sp2 : (subblock1 subs (p + 1)).hi < (subblock1 subs (p + 2)).lo :=
    hlt_idx (p + 1) (p + 2) hp1_ge1 (by omega) hp2_len
  set Sp := subblock1 subs p
  set Sp1 := subblock1 subs (p + 1)
  set Sp2 := subblock1 subs (p + 2)
  set tBridge := proc.popStepIdx Sp1.lo
  have hSp1_Icc : Sp1.lo ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hSp2_Icc : Sp2.lo ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have htBridge_le_tEnd1 : tBridge ≤ proc.popStepIdx Sp2.lo :=
    (hpop_mono Sp1.lo hSp1_Icc Sp2.lo hSp2_Icc).2.mp (by omega)
  obtain ⟨hBp_bst, hBp_keys⟩ := hBp_all tBridge le_rfl
  obtain ⟨hBp1_bst, hBp1_keys⟩ := hBp1_all tBridge htBridge_le_tEnd1
  set Bp := phaseBlockBST P proc chain (ℓ.val + 1) X p tBridge
  set Bp1 := phaseBlockBST P proc chain (ℓ.val + 1) X (p + 1) tBridge
  set I_Xp : Set ℕ := {u : ℕ | Sp.hi < u ∧ u ≤ X.hi}
  set I_Xp1 : Set ℕ := {u : ℕ | Sp1.hi < u ∧ u ≤ X.hi}
  obtain ⟨hext_bst, _⟩ := cartesianExt_isBST_and_keys proc (le_of_lt htBridge_lt_len)
  have hI_sub : I_Xp1 ⊆ I_Xp := by
    intro u ⟨hu1, hu2⟩
    exact ⟨by omega, hu2⟩
  have hBp1_eq : Bp1 = restrictTree Bp I_Xp1 := by
    have h1 : Bp = restrictTree (cartesianExt proc tBridge) I_Xp :=
      phaseBlockBST_eq proc chain ℓ X p tBridge
    have h2 : Bp1 = restrictTree (cartesianExt proc tBridge) I_Xp1 :=
      phaseBlockBST_eq proc chain ℓ X (p + 1) tBridge
    rw [h1, h2]
    exact (restrictTree_restrictTree_of_subset h_3_1 hext_bst
      (isLCAClosed_interval_oc _ _ _) hI_sub).symm
  have hSc_sub_IXp1 : ∀ c ∈ Finset.Icc (p + 2) subs.length, (subblock1 subs c).toSet ⊆ I_Xp1 := by
    intro c hc w hw
    have hc_bounds := Finset.mem_Icc.mp hc
    have hc_full : c ∈ Finset.Icc 1 subs.length := Finset.mem_Icc.mpr ⟨by omega, hc_bounds.2⟩
    obtain ⟨_, _, _, _, hSchi_X, _⟩ := hsub_c c hc_full
    have hSp1_lt_Sc : Sp1.hi < (subblock1 subs c).lo := hlt_idx (p + 1) c hp1_ge1 (by omega) hc_bounds.2
    change (subblock1 subs c).lo ≤ w ∧ w ≤ (subblock1 subs c).hi at hw
    exact ⟨by omega, by omega⟩
  have hfb_Bp1_eq : ∀ c ∈ Finset.Icc (p + 2) subs.length,
      firstInBlock? Bp1 (subblock1 subs c) = firstInBlock? Bp (subblock1 subs c) := by
    intro c hc
    rw [← treeRootKey?_restrictTree_eq_firstInBlock? hBp1_bst,
        ← treeRootKey?_restrictTree_eq_firstInBlock? hBp_bst,
        hBp1_eq,
        restrictTree_restrictTree_of_subset h_3_1 hBp_bst
          (isLCAClosed_interval_oc _ _ _) (hSc_sub_IXp1 c hc)]
  have hSp1_in_Bp : Sp1.lo ∈ Bp := by
    rw [mem_iff_mem_keyFinset, hBp_keys, Finset.mem_Icc]
    dsimp only [Sp, Sp1] at hlink_p hSp1lo_hi hSp1hi_X ⊢
    omega
  have hfb_Sp1_ne : firstInBlock? Bp Sp1 ≠ none := by
    intro hnone
    exact (firstInBlock?_eq_none_iff hBp_bst Sp1).mp hnone Sp1.lo hSp1_in_Bp ⟨le_rfl, hSp1lo_hi⟩
  obtain ⟨r_p1, hfb_rp1⟩ : ∃ r_p1, firstInBlock? Bp Sp1 = some r_p1 :=
    Option.ne_none_iff_exists'.mp hfb_Sp1_ne
  obtain ⟨hrp1_Bp, hrp1_Sp1⟩ := firstInBlock?_mem hfb_rp1
  set S_p : Set ℕ := (preorderSummarySet Bp (subs.drop p) 1 : Set ℕ)
  set S_p1 : Set ℕ := (preorderSummarySet Bp1 (subs.drop (p + 1)) 1 : Set ℕ)
  have hSp_char : ∀ w, w ∈ S_p ↔
      ∃ c ∈ Finset.Icc (p + 1) subs.length, firstInBlock? Bp (subblock1 subs c) = some w := by
    intro w
    change w ∈ preorderSummarySet Bp (subs.drop p) 1 ↔ _
    rw [mem_preorderSummarySet_one_iff hBp_bst]
    constructor
    · rintro ⟨C, hC, hfb⟩
      obtain ⟨c, hc, rfl⟩ := (remBlocks_mem_iff ℓ X hp_len C).mp hC
      exact ⟨c, hc, hfb⟩
    · rintro ⟨c, hc, hfb⟩
      exact ⟨subblock1 subs c, (remBlocks_mem_iff ℓ X hp_len _).mpr ⟨c, hc, rfl⟩, hfb⟩
  have hSp1_char : ∀ w, w ∈ S_p1 ↔
      ∃ c ∈ Finset.Icc (p + 2) subs.length, firstInBlock? Bp (subblock1 subs c) = some w := by
    intro w
    change w ∈ preorderSummarySet Bp1 (subs.drop (p + 1)) 1 ↔ _
    rw [mem_preorderSummarySet_one_iff hBp1_bst]
    constructor
    · rintro ⟨C, hC, hfb⟩
      obtain ⟨c, hc, rfl⟩ := (remBlocks_mem_iff ℓ X hp1_len C).mp hC
      rw [hfb_Bp1_eq c hc] at hfb
      exact ⟨c, hc, hfb⟩
    · rintro ⟨c, hc, hfb⟩
      rw [← hfb_Bp1_eq c hc] at hfb
      exact ⟨subblock1 subs c, (remBlocks_mem_iff ℓ X hp1_len _).mpr ⟨c, hc, rfl⟩, hfb⟩
  have hSp1_sub_IXp1 : S_p1 ⊆ I_Xp1 := by
    intro w hw
    obtain ⟨c, hc, hfb⟩ := (hSp1_char w).mp hw
    exact hSc_sub_IXp1 c hc (firstInBlock?_mem hfb).2
  have hSp1_sub_Sp : S_p1 ⊆ S_p := by
    intro w hw
    obtain ⟨c, hc, hfb⟩ := (hSp1_char w).mp hw
    have hc_b := Finset.mem_Icc.mp hc
    exact (hSp_char w).mpr ⟨c, Finset.mem_Icc.mpr ⟨by omega, hc_b.2⟩, hfb⟩
  have hrp1_lt_Sp1 : ∀ w ∈ S_p1, r_p1 < w := by
    intro w hw
    have hw_gt : Sp1.hi < w := (hSp1_sub_IXp1 hw).1
    change Sp1.lo ≤ r_p1 ∧ r_p1 ≤ Sp1.hi at hrp1_Sp1
    omega
  have hrp1_not_Sp1 : r_p1 ∉ S_p1 := fun h => lt_irrefl r_p1 (hrp1_lt_Sp1 r_p1 h)
  have hSp_split : ∀ w, w ∈ S_p ↔ w = r_p1 ∨ w ∈ S_p1 := by
    intro w
    rw [hSp_char, hSp1_char]
    constructor
    · rintro ⟨c, hc, hfb⟩
      have hc_b := Finset.mem_Icc.mp hc
      rcases eq_or_lt_of_le hc_b.1 with hcp1 | hlt_c
      · rw [← hcp1] at hfb
        change firstInBlock? Bp Sp1 = some w at hfb
        rw [hfb_rp1] at hfb
        injection hfb with heq
        exact Or.inl heq.symm
      · exact Or.inr ⟨c, Finset.mem_Icc.mpr ⟨by omega, hc_b.2⟩, hfb⟩
    · rintro (rfl | ⟨c, hc, hfb⟩)
      · exact ⟨p + 1, Finset.mem_Icc.mpr ⟨le_rfl, hp1_len⟩, hfb_rp1⟩
      · have hc_b := Finset.mem_Icc.mp hc
        exact ⟨c, Finset.mem_Icc.mpr ⟨by omega, hc_b.2⟩, hfb⟩
  obtain ⟨hLCA_Bp_Sp, hTp_bst, _, hGp_bst, hGp_keys⟩ :=
    summary_bst_and_keys_of_blockBST h_3_1 hValid ℓ X hX hp1 hp_le_K1 hBp_bst hBp_keys
  set Tp := preorderSummaryBST Bp (subs.drop p) 1
  set Tp1 := preorderSummaryBST Bp1 (subs.drop (p + 1)) 1
  have hTp_mem : ∀ w, w ∈ Tp ↔ w ∈ S_p := by
    intro w
    have h1 := (h_3_1 Bp S_p hBp_bst hLCA_Bp_Sp).1.2 w
    change w ∈ Tp ↔ w ∈ Bp ∧ w ∈ S_p at h1
    rw [h1]
    refine ⟨And.right, fun hw => ⟨?_, hw⟩⟩
    obtain ⟨c, _, hfb⟩ := (hSp_char w).mp hw
    exact (firstInBlock?_mem hfb).1
  have hTp_min : Tp.minKey? = some r_p1 := by
    rw [minKey?_mem_and_le hTp_bst]
    refine ⟨(hTp_mem r_p1).mpr ((hSp_split r_p1).mpr (Or.inl rfl)), fun v hv => ?_⟩
    rcases (hSp_split v).mp ((hTp_mem v).mp hv) with rfl | hv_Sp1
    · exact le_rfl
    · exact le_of_lt (hrp1_lt_Sp1 v hv_Sp1)
  have hTp_ne : Tp ≠ .nil := by
    intro hnil; rw [hnil] at hTp_min; simp [BinaryTree.minKey?] at hTp_min
  have hLCA_Tp_Sp1 : IsLCAClosed Tp S_p1 := by
    intro x _ y _ hx hy z hlca
    have hz_Tp : z ∈ Tp := lcaBST_mem Tp x y z hlca
    obtain ⟨hmin_z, _⟩ := lcaBST_between Tp x y z hlca
    have hx_gt : r_p1 < x := hrp1_lt_Sp1 x hx
    have hy_gt : r_p1 < y := hrp1_lt_Sp1 y hy
    rcases (hSp_split z).mp ((hTp_mem z).mp hz_Tp) with rfl | hz_Sp1
    · exfalso; omega
    · exact hz_Sp1
  have hTp1_eq_Tp : Tp1 = restrictTree Tp S_p1 := by
    have h1 : Tp1 = restrictTree Bp S_p1 := by
      change restrictTree Bp1 S_p1 = restrictTree Bp S_p1
      rw [hBp1_eq]
      exact restrictTree_restrictTree_of_subset h_3_1 hBp_bst
        (isLCAClosed_interval_oc _ _ _) hSp1_sub_IXp1
    have h2 : restrictTree Tp S_p1 = restrictTree Bp S_p1 :=
      restrictTree_restrictTree_of_subset h_3_1 hBp_bst hLCA_Bp_Sp hSp1_sub_Sp
    exact h1.trans h2.symm
  have hsp_restrict : restrictTree (spliceMin Tp) S_p1 = restrictTree Tp S_p1 :=
    ((h_3_1 Tp S_p1 hTp_bst hLCA_Tp_Sp1).2.2 hTp_ne).1.2 r_p1 hTp_min |>.2 hrp1_not_Sp1
  have hsp_self : restrictTree (spliceMin Tp) S_p1 = spliceMin Tp := by
    apply restrictTree_eq_self_of_forall_mem
    intro w hw
    have hw_kf : w ∈ (keyFinset Tp).erase r_p1 :=
      (spliceMin_spec hTp_bst hTp_min).2 ▸ (mem_iff_mem_keyFinset _ w).mp hw
    obtain ⟨hw_ne, hw_Tp_kf⟩ := Finset.mem_erase.mp hw_kf
    have hw_Sp : w ∈ S_p := (hTp_mem w).mp ((mem_iff_mem_keyFinset Tp w).mpr hw_Tp_kf)
    rcases (hSp_split w).mp hw_Sp with rfl | hw_Sp1
    · exact absurd rfl hw_ne
    · exact hw_Sp1
  have hTp1_eq_sp : Tp1 = spliceMin Tp :=
    hTp1_eq_Tp.trans (hsp_restrict.symm.trans hsp_self)
  set Gp := phaseSummaryBST P proc chain (ℓ.val + 1) X p tBridge
  set Gp1 := phaseSummaryBST P proc chain (ℓ.val + 1) X (p + 1) tBridge
  have hGp_eq : Gp = Tp.map (subblockIndex1 subs) :=
    phaseSummaryBST_eq proc chain ℓ X p tBridge
  have hGp1_eq : Gp1 = Tp1.map (subblockIndex1 subs) :=
    phaseSummaryBST_eq proc chain ℓ X (p + 1) tBridge
  have hGp1_sp : Gp1 = spliceMin Gp := by
    rw [hGp1_eq, hGp_eq, hTp1_eq_sp, spliceMin_map]
  rw [← hGp_eq] at hGp_bst hGp_keys
  have hGp_min : Gp.minKey? = some (p + 1) := by
    rw [minKey?_mem_and_le hGp_bst]
    refine ⟨?_, ?_⟩
    · rw [mem_iff_mem_keyFinset, hGp_keys, Finset.mem_Icc]
      exact ⟨le_rfl, hp1_len⟩
    · intro v hv
      rw [mem_iff_mem_keyFinset, hGp_keys, Finset.mem_Icc] at hv
      exact hv.1
  have hreach_Gp : RightRotReachable Gp (.node (p + 1) .nil Gp1) := by
    rw [hGp1_sp]
    exact rightRotReachable_rotMinToRoot hGp_bst hGp_min
  have hGp_ge : ∀ v ∈ Gp, 2 + (p - 1) ≤ v := by
    intro v hv
    rw [mem_iff_mem_keyFinset, hGp_keys, Finset.mem_Icc] at hv
    omega
  have hreach_emb :=
    (range'_foldr_bst_mem_and_rightRotReachable (p - 1) 2 hGp_bst hGp_ge hreach_Gp).2.2
  have htop_step : topEmbedPhase (p + 1) Gp1 = topEmbedPhase p (.node (p + 1) .nil Gp1) := by
    unfold topEmbedPhase
    have hp1_sub : (p + 1) - 1 = (p - 1) + 1 := by omega
    have h2_add : 2 + (p - 1) = p + 1 := by omega
    rw [hp1_sub, range'_succ_append 2 (p - 1), h2_add, List.foldr_append]
    rfl
  rw [htop_step]
  exact hreach_emb

theorem traj_foldl_bst_and_mem {Δ' k : ℕ} :
    ∀ (traj : List (RightCascadeTrajStep ℕ)) {H : BinaryTree ℕ},
      H.IsBST → ValidRightCascadeTraj Δ' k H traj →
      (traj.foldl RightCascadeTrajStep.step H).IsBST ∧
      (∀ w, w ∈ traj.foldl RightCascadeTrajStep.step H ↔ w ∈ H)
  | [], _, hH, _ => ⟨hH, fun _ => Iff.rfl⟩
  | .singleRot x y :: rest, H, hH, ⟨_, _, hV_rest⟩ => by
    simp only [List.foldl_cons, RightCascadeTrajStep.step]
    obtain ⟨hbst, hmem⟩ := traj_foldl_bst_and_mem rest (rotateRightEdge_isBST hH x y) hV_rest
    exact ⟨hbst, fun w => (hmem w).trans (mem_rotateRightEdge_iff H x y w)⟩
  | .cascadeBatch pairs :: rest, H, hH, ⟨_, hV_rest⟩ => by
    simp only [List.foldl_cons, RightCascadeTrajStep.step]
    obtain ⟨hH'_bst, hH'_keys⟩ := foldl_rotateRightEdge_bst_keys pairs H hH
    change (execRightCascadeBatch H pairs).IsBST at hH'_bst
    change keyFinset (execRightCascadeBatch H pairs) = keyFinset H at hH'_keys
    obtain ⟨hbst, hmem⟩ := traj_foldl_bst_and_mem rest hH'_bst hV_rest
    refine ⟨hbst, fun w => (hmem w).trans ?_⟩
    rw [mem_iff_mem_keyFinset, mem_iff_mem_keyFinset, hH'_keys]

theorem nodeRight_execRightCascadeBatch (c : ℕ) (pairs : List (ℕ × ℕ))
    (hgt_pairs : ∀ pr ∈ pairs, c < pr.2) :
    ∀ (B : BinaryTree ℕ),
      execRightCascadeBatch (.node c .nil B) pairs =
        .node c .nil (execRightCascadeBatch B pairs) := by
  induction pairs with
  | nil => intro _; rfl
  | cons pr rest ih =>
    intro B
    have hc_pr : c < pr.2 := hgt_pairs pr List.mem_cons_self
    have hnot_pr : ¬ pr.2 < c := not_lt_of_gt hc_pr
    have hrot : rotateRightEdge (.node c .nil B) pr.1 pr.2 =
        .node c .nil (rotateRightEdge B pr.1 pr.2) := by
      simp [rotateRightEdge, hnot_pr, hc_pr]
    unfold execRightCascadeBatch
    simp only [List.foldl_cons, hrot]
    exact ih (fun q hq => hgt_pairs q (List.mem_cons_of_mem pr hq))
      (rotateRightEdge B pr.1 pr.2)

theorem nodeRight_traj_lift {Δ' k : ℕ} (c : ℕ) :
    ∀ (traj : List (RightCascadeTrajStep ℕ)) {H : BinaryTree ℕ},
      H.IsBST → (∀ v ∈ H, c < v) → ValidRightCascadeTraj Δ' k H traj →
      ValidRightCascadeTraj Δ' k (.node c .nil H) traj ∧
      traj.foldl RightCascadeTrajStep.step (.node c .nil H) =
        .node c .nil (traj.foldl RightCascadeTrajStep.step H)
  | [], _, _, _, _ => ⟨trivial, rfl⟩
  | .singleRot x y :: rest, H, hH, hgt, ⟨hxy, hedge, hV_rest⟩ => by
    rcases hedge with ⟨A, B, C, hy_H, hsub⟩
    have hcy : c < y := hgt y hy_H
    have hnot_yc : ¬ y < c := not_lt_of_gt hcy
    have hedge_node : IsRightRotEdge (.node c .nil H) x y :=
      ⟨A, B, C, .right hy_H, by simp [subtreeAtKey, hnot_yc, hcy, hsub]⟩
    have hrot_node : rotateRightEdge (.node c .nil H) x y =
        .node c .nil (rotateRightEdge H x y) := by
      simp [rotateRightEdge, hnot_yc, hcy]
    have hH' : (rotateRightEdge H x y).IsBST := rotateRightEdge_isBST hH x y
    have hgt' : ∀ v ∈ rotateRightEdge H x y, c < v := fun v hv =>
      hgt v ((mem_rotateRightEdge_iff H x y v).mp hv)
    obtain ⟨hV_node_rest, hfold_node⟩ := nodeRight_traj_lift c rest hH' hgt' hV_rest
    refine ⟨⟨hxy, hedge_node, hrot_node.symm ▸ hV_node_rest⟩, ?_⟩
    simp only [List.foldl_cons, RightCascadeTrajStep.step, hrot_node]
    exact hfold_node
  | .cascadeBatch pairs :: rest, H, hH, hgt, ⟨hcasc, hV_rest⟩ => by
    rcases hcasc with ⟨hk1, hlen_k, top, htop_H, idx, hpairs_idx, hgap⟩
    have hctop : c < top := hgt top htop_H
    have hnot_topc : ¬ top < c := not_lt_of_gt hctop
    have hsub_top : subtreeAtKey (.node c .nil H) top = subtreeAtKey H top := by
      simp [subtreeAtKey, hnot_topc, hctop]
    have hcasc_node : IsGappedRightCascade (.node c .nil H) Δ' k pairs :=
      ⟨hk1, hlen_k, top, .right htop_H, idx,
        by simpa only [hsub_top] using hpairs_idx, hgap⟩
    have hgt_pairs : ∀ pr ∈ pairs, c < pr.2 := by
      intro pr hpr
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hpr
      let r : Fin k := ⟨i, hlen_k ▸ hi⟩
      obtain ⟨hidx_len, hpairs_r⟩ := hpairs_idx r
      have hget? : pairs[i]? = some pr := getElem?_of_getElem hi hget
      change pairs[i]? = some _ at hpairs_r
      rw [hget?] at hpairs_r
      injection hpairs_r with hpr_eq
      have hpr2_eq : pr.2 = (leftSpine (subtreeAtKey H top))[idx r + 1]'hidx_len :=
        congrArg Prod.snd hpr_eq
      have hpr2_ls : pr.2 ∈ leftSpine (subtreeAtKey H top) := by
        rw [hpr2_eq]; exact List.getElem_mem hidx_len
      exact hgt pr.2 (mem_of_mem_subtreeAtKey (mem_of_mem_leftSpine hpr2_ls))
    have hexec_node : execRightCascadeBatch (.node c .nil H) pairs =
        .node c .nil (execRightCascadeBatch H pairs) :=
      nodeRight_execRightCascadeBatch c pairs hgt_pairs H
    obtain ⟨hH'_bst, hH'_keys⟩ := foldl_rotateRightEdge_bst_keys pairs H hH
    change (execRightCascadeBatch H pairs).IsBST at hH'_bst
    change keyFinset (execRightCascadeBatch H pairs) = keyFinset H at hH'_keys
    have hgt' : ∀ v ∈ execRightCascadeBatch H pairs, c < v := by
      intro v hv
      apply hgt v
      rw [mem_iff_mem_keyFinset, ← hH'_keys, ← mem_iff_mem_keyFinset]
      exact hv
    obtain ⟨hV_node_rest, hfold_node⟩ := nodeRight_traj_lift c rest hH'_bst hgt' hV_rest
    refine ⟨⟨hcasc_node, hexec_node.symm ▸ hV_node_rest⟩, ?_⟩
    simp only [List.foldl_cons, RightCascadeTrajStep.step, hexec_node]
    exact hfold_node

theorem range'_traj_lift {Δ' k : ℕ} {traj : List (RightCascadeTrajStep ℕ)} :
    ∀ (m a : ℕ) {H : BinaryTree ℕ}, H.IsBST → (∀ v ∈ H, a + m ≤ v) →
      ValidRightCascadeTraj Δ' k H traj →
      let emb := fun X => (List.range' a m).foldr (fun c acc => BinaryTree.node c .nil acc) X
      ValidRightCascadeTraj Δ' k (emb H) traj ∧
      traj.foldl RightCascadeTrajStep.step (emb H) =
        emb (traj.foldl RightCascadeTrajStep.step H)
  | 0, _, _, _, _, hV => ⟨hV, rfl⟩
  | m + 1, a, H, hH, hge, hV => by
    dsimp only [List.range', List.foldr_cons]
    have hge' : ∀ v ∈ H, (a + 1) + m ≤ v := by
      intro v hv; have := hge v hv; omega
    obtain ⟨hV_emb', hfold_emb'⟩ := range'_traj_lift m (a + 1) hH hge' hV
    obtain ⟨hemb'_bst, hemb'_mem, _⟩ :=
      range'_foldr_bst_mem_and_rightRotReachable m (a + 1) hH hge' .refl
    set emb' := fun X => (List.range' (a + 1) m).foldr (fun c acc => BinaryTree.node c .nil acc) X
    have hgt_a : ∀ v ∈ emb' H, a < v := by
      intro v hv
      rcases (hemb'_mem v).mp hv with ⟨h1, _⟩ | hvH
      · omega
      · have := hge v hvH; omega
    obtain ⟨hV_node, hfold_node⟩ := nodeRight_traj_lift a traj hemb'_bst hgt_a hV_emb'
    rw [hfold_emb'] at hfold_node
    exact ⟨hV_node, hfold_node⟩

theorem topEmbedPhase_traj_lift {K_X p Δ' k : ℕ}
    (hK2 : 2 ≤ K_X) (hp1 : 1 ≤ p) (hp2 : p ≤ K_X - 1)
    {G : BinaryTree ℕ} {traj : List (RightCascadeTrajStep ℕ)}
    (hG_bst : G.IsBST) (hG_keys : keyFinset G = Finset.Icc (p + 1) K_X)
    (hV : ValidRightCascadeTraj Δ' k G traj) :
    (topEmbedPhase p G).IsBST ∧
    keyFinset (topEmbedPhase p G) = Finset.Icc 2 K_X ∧
    ValidRightCascadeTraj Δ' k (topEmbedPhase p G) traj ∧
    traj.foldl RightCascadeTrajStep.step (topEmbedPhase p G) =
      topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G) := by
  have hge : ∀ v ∈ G, 2 + (p - 1) ≤ v := by
    intro v hv
    rw [mem_iff_mem_keyFinset, hG_keys, Finset.mem_Icc] at hv
    omega
  obtain ⟨hemb_bst, hemb_mem, _⟩ :=
    range'_foldr_bst_mem_and_rightRotReachable (p - 1) 2 hG_bst hge .refl
  obtain ⟨hV_emb, hfold_emb⟩ := range'_traj_lift (p - 1) 2 hG_bst hge hV
  unfold topEmbedPhase
  refine ⟨hemb_bst, ?_, hV_emb, hfold_emb⟩
  ext v
  rw [← mem_iff_mem_keyFinset, hemb_mem, mem_iff_mem_keyFinset, hG_keys,
      Finset.mem_Icc, Finset.mem_Icc]
  omega


/-! ## Section 6: Lemma 5.7 (`lem_5_7_from_deps`) -/

theorem lem_5_7_from_deps (h_3_1 : Ty_lem_3_1)
    (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    let K_X := subs.length
    2 ≤ K_X ∧
    (∀ p ∈ Finset.Icc 1 (K_X - 1),
      let tStart := proc.popStepIdx (subblock1 subs p).lo
      let tEnd := if p + 1 ≤ K_X then proc.popStepIdx (subblock1 subs (p + 1)).lo
                  else proc.steps.length
      tStart ≤ tauEmpty proc (subblock1 subs p) ∧
      tauEmpty proc (subblock1 subs p) ≤ tEnd ∧
      (∀ τ ∈ Finset.Icc tStart tEnd,
        let G := phaseSummaryBST P proc chain ℓ_val X p τ
        G.IsBST ∧ keyFinset G = Finset.Icc (p + 1) K_X) ∧
      (∀ τ₁ τ₂ : ℕ, tStart ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ tEnd →
        RightRotReachable
          (phaseSummaryBST P proc chain ℓ_val X p τ₁)
          (phaseSummaryBST P proc chain ℓ_val X p τ₂)) ∧
      (∀ e ∈ vXp P proc chain ℓ_val X p,
        let b := subblockIndex1 subs e.x
        let q := subblockIndex1 subs e.y
        let Gs := phaseSummaryBST P proc chain ℓ_val X p e.stepIdx
        let GsNext := phaseSummaryBST P proc chain ℓ_val X p (e.stepIdx + 1)
        p + 1 ≤ b ∧ b < q ∧ q ≤ K_X ∧
        b ∈ leftSpine Gs ∧ q ∈ leftSpine Gs ∧
        IsRightRotEdge Gs b q ∧
        RightRotReachable (rotateRightEdge Gs b q) GsNext)) ∧
    ((∀ p ∈ Finset.Icc 1 (K_X - 2),
        let tBridge := proc.popStepIdx (subblock1 subs (p + 1)).lo
        RightRotReachable
          (topEmbedPhase p (phaseSummaryBST P proc chain ℓ_val X p tBridge))
          (topEmbedPhase (p + 1) (phaseSummaryBST P proc chain ℓ_val X (p + 1) tBridge))) ∧
     (∀ p ∈ Finset.Icc 1 (K_X - 1), ∀ (Δ' k : ℕ) (G : BinaryTree ℕ)
        (traj : List (RightCascadeTrajStep ℕ)),
        G.IsBST → keyFinset G = Finset.Icc (p + 1) K_X →
        ValidRightCascadeTraj Δ' k G traj →
        (topEmbedPhase p G).IsBST ∧
        keyFinset (topEmbedPhase p G) = Finset.Icc 2 K_X ∧
        ValidRightCascadeTraj Δ' k (topEmbedPhase p G) traj ∧
        traj.foldl RightCascadeTrajStep.step (topEmbedPhase p G) =
          topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G))) := by
  dsimp only
  have hK2 := validScaleTree_K_X_ge_two hValid ℓ X hX
  refine ⟨hK2, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_Icc.mp hp
    have hp1_le_K : p + 1 ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length := by
      omega
    simp only [hp1_le_K, ↓reduceIte]
    obtain ⟨htStart_lt, htau_le, _, _⟩ := tauEmpty_window_bounds hValid proc ℓ X hX hp1 hp2
    obtain ⟨hBp_all, hBp_reach⟩ := phaseBlockBST_props h_3_1 hValid proc ℓ X hX hp1 hp2
    refine ⟨le_of_lt htStart_lt, htau_le, ?_, ?_, ?_⟩
    · intro τ hτ
      obtain ⟨_, hτ_le⟩ := Finset.mem_Icc.mp hτ
      obtain ⟨hBp_bst, hBp_keys⟩ := hBp_all τ hτ_le
      obtain ⟨_, _, _, hG_bst, hG_keys⟩ :=
        summary_bst_and_keys_of_blockBST h_3_1 hValid ℓ X hX hp1 hp2 hBp_bst hBp_keys
      rw [phaseSummaryBST_eq]
      exact ⟨hG_bst, hG_keys⟩
    · intro τ₁ τ₂ _ h12 h2end
      obtain ⟨hBp1_bst, hBp1_keys⟩ := hBp_all τ₁ (le_trans h12 h2end)
      have hreach_B := hBp_reach τ₁ τ₂ h12 h2end
      rw [phaseSummaryBST_eq, phaseSummaryBST_eq]
      exact summary_reachable_proj h_3_1 hValid ℓ X hX hp1 hp2 hBp1_bst hBp1_keys hreach_B
    · intro e he
      exact vXp_proj_step h_3_1 hValid proc ℓ X hX hp1 hp2 he
  · intro p hp
    exact topEmbedPhase_bridge h_3_1 hValid proc ℓ X hX hp
  · intro p hp Δ' k G traj hG_bst hG_keys hV
    obtain ⟨hp1, hp2⟩ := Finset.mem_Icc.mp hp
    exact topEmbedPhase_traj_lift hK2 hp1 hp2 hG_bst hG_keys hV
end Internal57

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

/-- **Lemma 5.5** (`lem:b3-post`, Step 1: Post-Depletion Exits):
Across all scales `1 ≤ ℓ ≤ M`, `|ℬ_{3,exit,post}| ≤ K_L < 2 P`. -/
theorem lem_5_5_b3_post (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (b3ExitPost P proc chain).card ≤ proc.kL ∧ proc.kL < 2 * P :=
  Internal55.lem_5_5_b3_post P r M T hValid proc

/-- **Lemma 5.6** (`lem:b3-escape`, Step 2: Unique Scale per Promoted Key and Secondary-Exit
Reduction):
There exists `A_esc ⊆ ℬ_{3,exit,act}` of size `|A_esc| < 18 P` (independent of `r, M, 𝒯`) with
`|ℬ_{3,exit,act}| ≤ 2 ∑_{ℓ, X, p} |𝒩̃_p^(ℓ)| + |A_esc|`. -/
theorem lem_5_6_b3_escape
    (h_lem_3_6 : ∀ (P : ℕ), 1 ≤ P → ∀ (proc : FoldedPopProcess P),
      ((∀ τ : ℕ, τ ≤ proc.steps.length →
          (proc.treeAt τ).IsBST ∧
          keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P ∧
          postorderL2OnV (proc.treeAt τ) = (proc.treeAt τ).toKeyList ∧
          ∀ v ∈ proc.treeAt τ, v < foldedParent P (proc.treeAt τ) v) ∧
       (∀ τ u v : ℕ, τ < proc.steps.length → proc.steps[τ]? = some (.upperRot u v) →
          let z := foldedParent P (proc.treeAt τ) v
          foldedParent P (proc.treeAt (τ + 1)) u = z ∧
          ∀ w ∈ proc.treeAt (τ + 1), w ≠ u →
            foldedParent P (proc.treeAt (τ + 1)) w = foldedParent P (proc.treeAt τ) w) ∧
       (∀ s : ℕ, 1 ≤ s → s ≤ P →
          let τ := proc.popStepIdx s
          (∀ e ∈ proc.rInt, e.stepIdx = τ →
            foldedParent P (proc.treeAt (τ + 1)) e.x = e.z) ∧
          (∀ w ∈ proc.treeAt (τ + 1), (∀ e ∈ proc.rInt, e.stepIdx = τ → w ≠ e.x) →
            foldedParent P (proc.treeAt (τ + 1)) w = foldedParent P (proc.treeAt τ) w)) ∧
       (∀ τ₁ τ₂ v : ℕ, τ₁ ≤ τ₂ → τ₂ ≤ proc.steps.length →
          v ∈ proc.treeAt τ₁ → v ∈ proc.treeAt τ₂ →
          foldedParent P (proc.treeAt τ₁) v ≤ foldedParent P (proc.treeAt τ₂) v ∧
          l2Ancestors P (proc.treeAt τ₂) v ⊆ l2Ancestors P (proc.treeAt τ₁) v)) ∧
      ((∀ τ : ℕ, τ ≤ proc.steps.length → proc.treeAt τ ≠ .nil →
          let ls := leftSpine (proc.treeAt τ)
          ∀ idx : Fin ls.length,
            let u_i := ls[idx]
            let u_next := if h : idx.val + 1 < ls.length then ls[idx.val + 1] else P + 1
            insert u_i (keyFinset ((subtreeAtKey (proc.treeAt τ) u_i).right)) =
              keyFinset (proc.treeAt τ) ∩ Finset.Icc u_i (u_next - 1)) ∧
       (∀ e ∈ proc.rInt,
          1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P ∧
          (∀ τ' ∈ Finset.Ico (e.stepIdx + 1) (proc.popStepIdx e.x),
            ∀ w : ℕ, proc.steps[τ']? = some (.push w) → w < e.x) ∧
          (∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
            ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z)))) ∧
      (proc.mBase ⊆ proc.rInt ∧
       proc.mBase.card ≤ 2 * P + proc.kRot ∧
       2 * P + proc.kRot < 4 * P ∧
       ∃ eL eR : InternalPopRot → InternalPopRot,
         Set.InjOn eL (proc.rInt \ proc.mBase : Set InternalPopRot) ∧
         Set.InjOn eR (proc.rInt \ proc.mBase : Set InternalPopRot) ∧
         ∀ e ∈ proc.rInt \ proc.mBase,
           eL e ∈ proc.rInt ∧
           eR e ∈ proc.rInt ∧
           proc.nextCascadeRot? (eL e) = some (eR e) ∧
           (eL e).s = (eR e).s ∧
           (eL e).s < e.s ∧
           (∀ e' ∈ proc.rInt, e'.x = e.x → e'.s < e.s → e'.s ≤ (eL e).s) ∧
           (eL e).x = e.x ∧
           (eL e).z = e.y ∧
           (eR e).x = e.y ∧
           (eL e).s < e.x ∧ e.x < (eL e).y ∧ (eL e).y < e.y ∧
           e.y < (eR e).y ∧ (eR e).y < (eR e).z))
    (h_lem_5_1 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      let chain := scaleTreePartitionChain T P M
      (∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T ℓ : ℝ)) < (1 : ℝ) / 2 ∧
      (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) < 2 ∧
      (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50)
    (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    let leadSum := ∑ ℓ : Fin M,
      ((chain ℓ.castSucc).map (fun X =>
        let subs := childSubblocks (chain ℓ.succ) X
        ∑ p ∈ Finset.Icc 1 (subs.length - 1),
          (leadExitSet P proc chain (ℓ.val + 1) X p).card)).sum
    ∃ A_esc : Finset InternalPopRot,
      A_esc ⊆ b3ExitAct P proc chain ∧
      A_esc.card < 18 * P ∧
      (b3ExitAct P proc chain).card ≤ 2 * leadSum + A_esc.card :=
  Internal56.lem_5_6_b3_escape h_lem_3_6 h_lem_5_1 P r M T hValid proc

/-- **Lemma 5.7** (`lem:b3-quotient`, Step 3: Insertion-Time Cartesian Extension `H̃*` and
Block-Root Summary BST `Ĝ_X`). -/
theorem lem_5_7_b3_quotient
    (h_lem_3_1 : ∀ {α : Type} [LinearOrder α]
      (t : BinaryTree α) (S : Set α), t.IsBST → IsLCAClosed t S →
      ((restrictTree t S).IsBST ∧ ∀ v : α, v ∈ restrictTree t S ↔ v ∈ t ∧ v ∈ S) ∧
      (∀ x y : α, IsSingleRotEdge t x y →
        let t' := rotateEdge t x y
        IsLCAClosed t' S →
          (x ∈ S ∧ y ∈ S →
            IsSingleRotEdge (restrictTree t S) x y ∧
              restrictTree t' S = rotateEdge (restrictTree t S) x y) ∧
          (¬ (x ∈ S ∧ y ∈ S) → restrictTree t' S = restrictTree t S)) ∧
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
             (xMax ∉ S → restrictTree tMax S = restrictTree t S))))
    (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    let K_X := subs.length
    2 ≤ K_X ∧
    (∀ p ∈ Finset.Icc 1 (K_X - 1),
      let tStart := proc.popStepIdx (subblock1 subs p).lo
      let tEnd := if p + 1 ≤ K_X then proc.popStepIdx (subblock1 subs (p + 1)).lo
                  else proc.steps.length
      tStart ≤ tauEmpty proc (subblock1 subs p) ∧
      tauEmpty proc (subblock1 subs p) ≤ tEnd ∧
      (∀ τ ∈ Finset.Icc tStart tEnd,
        let G := phaseSummaryBST P proc chain ℓ_val X p τ
        G.IsBST ∧ keyFinset G = Finset.Icc (p + 1) K_X) ∧
      (∀ τ₁ τ₂ : ℕ, tStart ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ tEnd →
        RightRotReachable
          (phaseSummaryBST P proc chain ℓ_val X p τ₁)
          (phaseSummaryBST P proc chain ℓ_val X p τ₂)) ∧
      (∀ e ∈ vXp P proc chain ℓ_val X p,
        let b := subblockIndex1 subs e.x
        let q := subblockIndex1 subs e.y
        let Gs := phaseSummaryBST P proc chain ℓ_val X p e.stepIdx
        let GsNext := phaseSummaryBST P proc chain ℓ_val X p (e.stepIdx + 1)
        p + 1 ≤ b ∧ b < q ∧ q ≤ K_X ∧
        b ∈ leftSpine Gs ∧ q ∈ leftSpine Gs ∧
        IsRightRotEdge Gs b q ∧
        RightRotReachable (rotateRightEdge Gs b q) GsNext)) ∧
    ((∀ p ∈ Finset.Icc 1 (K_X - 2),
        let tBridge := proc.popStepIdx (subblock1 subs (p + 1)).lo
        RightRotReachable
          (topEmbedPhase p (phaseSummaryBST P proc chain ℓ_val X p tBridge))
          (topEmbedPhase (p + 1) (phaseSummaryBST P proc chain ℓ_val X (p + 1) tBridge))) ∧
     (∀ p ∈ Finset.Icc 1 (K_X - 1), ∀ (Δ' k : ℕ) (G : BinaryTree ℕ)
        (traj : List (RightCascadeTrajStep ℕ)),
        G.IsBST → keyFinset G = Finset.Icc (p + 1) K_X →
        ValidRightCascadeTraj Δ' k G traj →
        (topEmbedPhase p G).IsBST ∧
        keyFinset (topEmbedPhase p G) = Finset.Icc 2 K_X ∧
        ValidRightCascadeTraj Δ' k (topEmbedPhase p G) traj ∧
        traj.foldl RightCascadeTrajStep.step (topEmbedPhase p G) =
          topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G))) :=
  Internal57.lem_5_7_from_deps h_lem_3_1 P r M T hValid proc ℓ X hX

end Solution.BucketB3PostEscape

end
