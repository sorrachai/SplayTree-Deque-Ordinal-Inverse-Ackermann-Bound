module

public import Challenge.Definitions
public import Solution.TreeFacts

set_option maxHeartbeats 1200000

@[expose] public section

namespace Solution.FoldedLaws

open SplayTree

/-! ## 1. Static BST, Spine, and Traversal Helpers -/

private theorem mem_keyFinset_iff {α : Type} [DecidableEq α] (t : BinaryTree α) (x : α) :
    x ∈ keyFinset t ↔ x ∈ t := by
  induction t with
  | nil =>
    simp [keyFinset]
  | node k l r ihl ihr =>
    simp [keyFinset, ihl, ihr, BinaryTree.mem_node_iff]

private theorem postorderL2OnV_eq_toKeyList (t : BinaryTree ℕ) :
    postorderL2OnV t = t.toKeyList := by
  unfold postorderL2OnV
  induction t with
  | nil => simp [toFCRSForest, roseForestPostorder]
  | node k l r ihl ihr =>
    simp [toFCRSForest, roseForestPostorder, ihl, ihr]

private theorem leftSpine_eq_nil_iff {α : Type} (t : BinaryTree α) :
    leftSpine t = [] ↔ t = .nil := by
  cases t <;> simp [leftSpine]

private theorem mem_of_mem_leftSpine {α : Type} {t : BinaryTree α} {x : α}
    (hx : x ∈ leftSpine t) : x ∈ t := by
  induction t with
  | nil => simp [leftSpine] at hx
  | node k l r ihl _ =>
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with hxl | rfl
    · exact .left (ihl hxl)
    · exact .here

private theorem leftSpine_pairwise_lt {t : BinaryTree ℕ} (ht : t.IsBST) :
    (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    rw [leftSpine, List.pairwise_append]
    refine ⟨ihl (BinaryTree.IsBST_left_of_IsBST ht), List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    rw [hb]
    exact BinaryTree.lt_of_IsBST_left l k r ht (mem_of_mem_leftSpine ha)

private theorem leftSpine_nodup {t : BinaryTree ℕ} (ht : t.IsBST) :
    (leftSpine t).Nodup :=
  (leftSpine_pairwise_lt ht).imp ne_of_lt

private theorem minKey?_eq_head?_leftSpine {α : Type} (t : BinaryTree α) :
    t.minKey? = (leftSpine t).head? := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    simp only [BinaryTree.minKey?, leftSpine]
    cases hl : leftSpine l with
    | nil =>
      have hl_nil : l = .nil := (leftSpine_eq_nil_iff l).mp hl
      subst hl_nil
      rfl
    | cons a as =>
      rw [ihl, hl]
      rfl

private theorem minKey?_mem {α : Type} {t : BinaryTree α} {s : α}
    (h : t.minKey? = some s) : s ∈ t := by
  rw [minKey?_eq_head?_leftSpine] at h
  exact mem_of_mem_leftSpine (List.mem_of_head? h)

private theorem minKey?_le_of_mem {t : BinaryTree ℕ} (ht : t.IsBST) {s x : ℕ}
    (hmin : t.minKey? = some s) (hx : x ∈ t) : s ≤ x := by
  induction t with
  | nil => simp [BinaryTree.minKey?] at hmin
  | node k l r ihl _ =>
    have hbst_l := BinaryTree.IsBST_left_of_IsBST ht
    cases hl : l.minKey? with
    | none =>
      have hl_nil : l = .nil := by
        cases l with
        | nil => rfl
        | node lk ll lr =>
          simp only [BinaryTree.minKey?] at hl
          cases hm : ll.minKey? <;> simp [hm] at hl
      subst hl_nil
      simp only [BinaryTree.minKey?] at hmin
      injection hmin with hks
      subst hks
      rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
      · exact le_rfl
      · cases hxl
      · exact le_of_lt (BinaryTree.gt_of_IsBST_right .nil k r ht hxr)
    | some m =>
      simp only [BinaryTree.minKey?, hl] at hmin
      injection hmin with hms
      subst hms
      have hm_in_l : m ∈ l := minKey?_mem hl
      have hm_lt_k : m < k := BinaryTree.lt_of_IsBST_left l k r ht hm_in_l
      rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
      · exact le_of_lt hm_lt_k
      · exact ihl hbst_l hl hxl
      · exact le_of_lt (lt_trans hm_lt_k (BinaryTree.gt_of_IsBST_right l k r ht hxr))

private theorem rootKey?_eq_getLast?_leftSpine {α : Type} (t : BinaryTree α) :
    rootKey? t = (leftSpine t).getLast? := by
  cases t <;> simp [rootKey?, leftSpine]

private theorem isRightRotEdge_of_leftSpine_adj {t : BinaryTree ℕ} (ht : t.IsBST)
    (i : ℕ) (hi : i + 1 < (leftSpine t).length) :
    IsRightRotEdge t ((leftSpine t)[i]'(by omega)) ((leftSpine t)[i + 1]'hi) := by
  induction t with
  | nil => simp [leftSpine] at hi
  | node k l r ihl _ =>
    have hl_bst := BinaryTree.IsBST_left_of_IsBST ht
    have hlen : (leftSpine (.node k l r)).length = (leftSpine l).length + 1 := by
      simp [leftSpine]
    by_cases hlt : i + 1 < (leftSpine l).length
    · have hu_eq : (leftSpine (.node k l r))[i]'(by omega) = (leftSpine l)[i]'(by omega) := by
        simp [leftSpine, List.getElem_append_left (by omega : i < (leftSpine l).length)]
      have hv_eq : (leftSpine (.node k l r))[i + 1]'hi = (leftSpine l)[i + 1]'hlt := by
        simp [leftSpine, List.getElem_append_left hlt]
      rw [hu_eq, hv_eq]
      obtain ⟨A, B, C, hv_in_l, hsub⟩ := ihl hl_bst hlt
      have hv_lt_k : (leftSpine l)[i + 1]'hlt < k :=
        BinaryTree.lt_of_IsBST_left l k r ht hv_in_l
      refine ⟨A, B, C, .left hv_in_l, ?_⟩
      simp [subtreeAtKey, hv_lt_k, hsub]
    · cases l with
      | nil =>
        simp [leftSpine] at hi
      | node lk ll lr =>
        have hlen_l : (leftSpine (.node lk ll lr)).length = (leftSpine ll).length + 1 := by
          simp [leftSpine]
        have hi_val : i = (leftSpine ll).length := by omega
        subst hi_val
        have hu_eq : (leftSpine (.node k (.node lk ll lr) r))[(leftSpine ll).length]'
            (by simp [leftSpine]) = lk := by
          simp [leftSpine]
        have hv_eq : (leftSpine (.node k (.node lk ll lr) r))[(leftSpine ll).length + 1]'hi = k := by
          simp [leftSpine]
        rw [hu_eq, hv_eq]
        exact ⟨ll, lr, r, .here, by simp [subtreeAtKey]⟩

/-! ## 2. Static `foldedParentAux`, `foldedParent`, and Spine Partition Lemmas -/

private theorem foldedParentAux_bounds {T : BinaryTree ℕ} (ht : T.IsBST) {c v : ℕ}
    (hc : ∀ w ∈ T, w < c) (hv : v ∈ T) :
    v < foldedParentAux c T v ∧
    foldedParentAux c T v ≤ c ∧
    (foldedParentAux c T v = c ∨ foldedParentAux c T v ∈ T) := by
  induction T generalizing c with
  | nil => cases hv
  | node k l r ihl ihr =>
    have hk_lt : k < c := hc k .here
    have hl_bst := BinaryTree.IsBST_left_of_IsBST ht
    have hr_bst := BinaryTree.IsBST_right_of_IsBST ht
    simp only [foldedParentAux]
    split_ifs with h1 h2
    · have hvl : v ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hv with rfl | hvl | hvr
        · omega
        · exact hvl
        · have := BinaryTree.gt_of_IsBST_right l k r ht hvr; omega
      obtain ⟨ha, hb, hc'⟩ := ihl hl_bst (fun w hw => BinaryTree.lt_of_IsBST_left l k r ht hw) hvl
      refine ⟨ha, le_trans hb (le_of_lt hk_lt), Or.inr ?_⟩
      rcases hc' with heq | hmem
      · rw [heq]; exact .here
      · exact .left hmem
    · have hvr : v ∈ r := by
        rcases BinaryTree.mem_node_iff.mp hv with rfl | hvl | hvr
        · omega
        · have := BinaryTree.lt_of_IsBST_left l k r ht hvl; omega
        · exact hvr
      obtain ⟨ha, hb, hc'⟩ := ihr hr_bst (fun w hw => hc w (.right hw)) hvr
      refine ⟨ha, hb, ?_⟩
      rcases hc' with heq | hmem
      · exact Or.inl heq
      · exact Or.inr (.right hmem)
    · have hvk : v = k := by omega
      subst hvk
      exact ⟨hk_lt, le_rfl, Or.inl rfl⟩

private theorem foldedParent_mem_props {P : ℕ} {T : BinaryTree ℕ} (ht : T.IsBST)
    (hkeys : ∀ x ∈ T, 1 ≤ x ∧ x ≤ P) {v : ℕ} (hv : v ∈ T) :
    v < foldedParent P T v ∧
    foldedParent P T v ≤ P + 1 ∧
    (foldedParent P T v = P + 1 ∨ foldedParent P T v ∈ T) := by
  have hvP : v ≤ P := (hkeys v hv).2
  have hne : v ≠ P + 1 := by omega
  simp only [foldedParent, hne, ↓reduceIte]
  exact foldedParentAux_bounds ht (fun w hw => by have := (hkeys w hw).2; omega) hv

private theorem foldedParentAux_leftSpine_adj {T : BinaryTree ℕ} (ht : T.IsBST)
    (c i : ℕ) (hi : i + 1 < (leftSpine T).length) :
    foldedParentAux c T ((leftSpine T)[i]'(by omega)) = (leftSpine T)[i + 1]'hi := by
  induction T generalizing c with
  | nil => simp [leftSpine] at hi
  | node k l r ihl _ =>
    have hl_bst := BinaryTree.IsBST_left_of_IsBST ht
    have hlen : (leftSpine (.node k l r)).length = (leftSpine l).length + 1 := by
      simp [leftSpine]
    by_cases hlt : i + 1 < (leftSpine l).length
    · have hu_eq : (leftSpine (.node k l r))[i]'(by omega) = (leftSpine l)[i]'(by omega) := by
        simp [leftSpine, List.getElem_append_left (by omega : i < (leftSpine l).length)]
      have hv_eq : (leftSpine (.node k l r))[i + 1]'hi = (leftSpine l)[i + 1]'hlt := by
        simp [leftSpine, List.getElem_append_left hlt]
      rw [hu_eq, hv_eq]
      have hu_in_l : (leftSpine l)[i]'(by omega) ∈ l :=
        mem_of_mem_leftSpine (List.getElem_mem _)
      have hu_lt_k : (leftSpine l)[i]'(by omega) < k :=
        BinaryTree.lt_of_IsBST_left l k r ht hu_in_l
      simp only [foldedParentAux, hu_lt_k, ↓reduceIte]
      exact ihl hl_bst k hlt
    · cases l with
      | nil => simp [leftSpine] at hi
      | node lk ll lr =>
        have hlen_l : (leftSpine (.node lk ll lr)).length = (leftSpine ll).length + 1 := by
          simp [leftSpine]
        have hi_val : i = (leftSpine ll).length := by omega
        subst hi_val
        have hu_eq : (leftSpine (.node k (.node lk ll lr) r))[(leftSpine ll).length]'
            (by simp [leftSpine]) = lk := by
          simp [leftSpine]
        have hv_eq : (leftSpine (.node k (.node lk ll lr) r))[(leftSpine ll).length + 1]'hi = k := by
          simp [leftSpine]
        rw [hu_eq, hv_eq]
        have hlk_lt_k : lk < k := BinaryTree.lt_of_IsBST_left _ k r ht .here
        simp [foldedParentAux, hlk_lt_k]

private theorem foldedParentAux_le_of_mem_leftSpine {T : BinaryTree ℕ} (ht : T.IsBST)
    {c x w : ℕ} (hx : x ∈ T) (hxw : x < w)
    (hcond : w ∈ leftSpine T ∨ (c ≤ w ∧ ∀ y ∈ T, y < c)) :
    foldedParentAux c T x ≤ w := by
  induction T generalizing c with
  | nil => cases hx
  | node k l r ihl ihr =>
    have hl_bst := BinaryTree.IsBST_left_of_IsBST ht
    have hr_bst := BinaryTree.IsBST_right_of_IsBST ht
    rcases hcond with hw_ls | ⟨hc_le, hall⟩
    · simp only [leftSpine, List.mem_append, List.mem_singleton] at hw_ls
      rcases hw_ls with hw_l | hwk_eq
      · have hwk : w < k := BinaryTree.lt_of_IsBST_left l k r ht (mem_of_mem_leftSpine hw_l)
        have hxk : x < k := lt_trans hxw hwk
        have hxl : x ∈ l := by
          rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
          · omega
          · exact hxl
          · have := BinaryTree.gt_of_IsBST_right l k r ht hxr; omega
        simp only [foldedParentAux, hxk, ↓reduceIte]
        exact ihl hl_bst hxl (Or.inl hw_l)
      · subst hwk_eq
        have hxl : x ∈ l := by
          rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
          · omega
          · exact hxl
          · have := BinaryTree.gt_of_IsBST_right l w r ht hxr; omega
        simp only [foldedParentAux, hxw, ↓reduceIte]
        exact ihl hl_bst hxl (Or.inr ⟨le_rfl, fun y hy => BinaryTree.lt_of_IsBST_left l w r ht hy⟩)
    · simp only [foldedParentAux]
      split_ifs with h1 h2
      · have hxl : x ∈ l := by
          rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
          · omega
          · exact hxl
          · have := BinaryTree.gt_of_IsBST_right l k r ht hxr; omega
        have hk_lt_c : k < c := hall k .here
        exact ihl hl_bst hxl (Or.inr ⟨by omega, fun y hy => BinaryTree.lt_of_IsBST_left l k r ht hy⟩)
      · have hxr : x ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
          · omega
          · have := BinaryTree.lt_of_IsBST_left l k r ht hxl; omega
          · exact hxr
        exact ihr hr_bst hxr (Or.inr ⟨hc_le, fun y hy => hall y (.right hy)⟩)
      · exact hc_le

private theorem leftSpine_interval_partition {T : BinaryTree ℕ} (ht : T.IsBST)
    {bound : ℕ} (hbound : ∀ x ∈ T, x < bound) (idx : Fin (leftSpine T).length) :
    let ls := leftSpine T
    let u_i := ls[idx]
    let u_next := if h : idx.val + 1 < ls.length then ls[idx.val + 1] else bound
    insert u_i (keyFinset ((subtreeAtKey T u_i).right)) =
      keyFinset T ∩ Finset.Icc u_i (u_next - 1) := by
  induction T generalizing bound with
  | nil => exact Fin.elim0 idx
  | node k l r ihl _ =>
    have hl_bst := BinaryTree.IsBST_left_of_IsBST ht
    have hk_lt_bound : k < bound := hbound k .here
    dsimp only
    by_cases hlast : idx.val < (leftSpine l).length
    · let idxL : Fin (leftSpine l).length := ⟨idx.val, hlast⟩
      have hui_eq : (leftSpine (.node k l r))[idx] = (leftSpine l)[idxL] := by
        change (leftSpine l ++ [k])[idx.val] = (leftSpine l)[idx.val]
        exact List.getElem_append_left hlast
      have hunext_eq :
          (if h : idx.val + 1 < (leftSpine (.node k l r)).length
           then (leftSpine (.node k l r))[idx.val + 1] else bound) =
          (if h : idxL.val + 1 < (leftSpine l).length
           then (leftSpine l)[idxL.val + 1] else k) := by
        have hlen : (leftSpine (.node k l r)).length = (leftSpine l).length + 1 := by
          simp [leftSpine]
        have hlt_tot : idx.val + 1 < (leftSpine (.node k l r)).length := by omega
        simp only [hlt_tot, ↓reduceDIte]
        by_cases hlt_l : idxL.val + 1 < (leftSpine l).length
        · simp only [hlt_l, ↓reduceDIte, leftSpine]
          exact List.getElem_append_left hlt_l
        · simp only [hlt_l, ↓reduceDIte]
          have heq : idx.val + 1 = (leftSpine l).length := by
            change ¬ (idx.val + 1 < (leftSpine l).length) at hlt_l
            omega
          simp [leftSpine, heq]
      have hui_in_l : (leftSpine l)[idxL] ∈ l :=
        mem_of_mem_leftSpine (List.getElem_mem _)
      have hui_lt_k : (leftSpine l)[idxL] < k :=
        BinaryTree.lt_of_IsBST_left l k r ht hui_in_l
      rw [hui_eq, hunext_eq]
      have hsub_eq : subtreeAtKey (.node k l r) ((leftSpine l)[idxL]) =
          subtreeAtKey l ((leftSpine l)[idxL]) := by
        simp only [subtreeAtKey, hui_lt_k, ↓reduceIte]
      rw [hsub_eq]
      have h_ih := ihl hl_bst (fun x hx => BinaryTree.lt_of_IsBST_left l k r ht hx) idxL
      dsimp only at h_ih
      rw [h_ih]
      set u_next_l := if h : idxL.val + 1 < (leftSpine l).length then (leftSpine l)[idxL.val + 1] else k
      have hunext_le_k : u_next_l ≤ k ∧ 1 ≤ u_next_l := by
        dsimp only [u_next_l]
        split_ifs with hlt_l
        · have hmem : (leftSpine l)[idxL.val + 1] ∈ l :=
            mem_of_mem_leftSpine (List.getElem_mem _)
          have hlt := BinaryTree.lt_of_IsBST_left l k r ht hmem
          have hpair := List.pairwise_iff_getElem.mp (leftSpine_pairwise_lt hl_bst)
            idxL.val (idxL.val + 1) hlast hlt_l (by omega)
          exact ⟨le_of_lt hlt, by omega⟩
        · exact ⟨le_rfl, by omega⟩
      ext x
      simp only [Finset.mem_inter, mem_keyFinset_iff, Finset.mem_Icc, BinaryTree.mem_node_iff]
      constructor
      · rintro ⟨hxl, hlo, hhi⟩
        exact ⟨Or.inr (Or.inl hxl), hlo, hhi⟩
      · rintro ⟨rfl | hxl | hxr, hlo, hhi⟩
        · omega
        · exact ⟨hxl, hlo, hhi⟩
        · have := BinaryTree.gt_of_IsBST_right l k r ht hxr
          omega
    · have hidx_eq : idx.val = (leftSpine l).length := by
        have := idx.isLt
        simp only [leftSpine, List.length_append, List.length_singleton] at this
        omega
      have hui_eq : (leftSpine (.node k l r))[idx] = k := by
        change (leftSpine l ++ [k])[idx.val] = k
        simp [hidx_eq]
      have hunext_eq :
          (if h : idx.val + 1 < (leftSpine (.node k l r)).length
           then (leftSpine (.node k l r))[idx.val + 1] else bound) = bound := by
        split_ifs with hlt
        · simp only [leftSpine, List.length_append, List.length_singleton, hidx_eq] at hlt
          omega
        · rfl
      rw [hui_eq, hunext_eq]
      have hsub : subtreeAtKey (.node k l r) k = .node k l r := by simp [subtreeAtKey]
      rw [hsub]
      ext x
      simp only [BinaryTree.right, Finset.mem_insert, mem_keyFinset_iff, Finset.mem_inter,
        Finset.mem_Icc, BinaryTree.mem_node_iff]
      constructor
      · rintro (rfl | hxr)
        · exact ⟨Or.inl rfl, le_rfl, by omega⟩
        · have hgt := BinaryTree.gt_of_IsBST_right l k r ht hxr
          have hlt := hbound x (.right hxr)
          exact ⟨Or.inr (Or.inr hxr), by omega, by omega⟩
      · rintro ⟨rfl | hxl | hxr, hlo, _⟩
        · exact Or.inl rfl
        · have := BinaryTree.lt_of_IsBST_left l k r ht hxl
          omega
        · exact Or.inr hxr

/-! ## 3. Single-Transformation Specs (`modifyLeftAt`, `spliceMin`, `rotateRightEdge`) -/

private def RootRightNil {α : Type} : BinaryTree α → Prop
  | .nil => True
  | .node _ _ r => r = .nil

private theorem modifyLeftAt_push_spec {T : BinaryTree ℕ} (ht : T.IsBST)
    {b w : ℕ} (hb : b ∈ leftSpine T) (hw : ∀ x ∈ T, w < x) :
    let T' := modifyLeftAt T b (fun L1 => .node w .nil L1)
    T'.IsBST ∧
    (∀ x, x ∈ T' ↔ x = w ∨ x ∈ T) ∧
    w ∈ leftSpine T' ∧
    (∀ c v, w < v → foldedParentAux c T' v = foldedParentAux c T v) := by
  induction T with
  | nil => simp [leftSpine] at hb
  | node k l r ihl _ =>
    obtain ⟨hlt, hgt, hl_bst, hr_bst⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb_l | hbk_eq
    · have hbk : b < k := BinaryTree.lt_of_IsBST_left l k r ht (mem_of_mem_leftSpine hb_l)
      have hw_l : ∀ x ∈ l, w < x := fun x hx => hw x (.left hx)
      obtain ⟨hl'_bst, hl'_mem, hw_ls, hl'_fp⟩ := ihl hl_bst hb_l hw_l
      have hwk : w < k := hw k .here
      have hlt' : SplayDeque.Direct.ForallTree (· < k)
          (modifyLeftAt l b (fun L1 => .node w .nil L1)) := by
        rw [SplayDeque.Direct.forallTree_iff] at hlt ⊢
        intro x hx
        rcases (hl'_mem x).mp hx with rfl | hxl
        · exact hwk
        · exact hlt x hxl
      have hmod_eq : modifyLeftAt (.node k l r) b (fun L1 => .node w .nil L1) =
          .node k (modifyLeftAt l b (fun L1 => .node w .nil L1)) r := by
        simp [modifyLeftAt, hbk]
      dsimp only
      rw [hmod_eq]
      refine ⟨BinaryTree.IsBST.node k _ r hlt' hgt hl'_bst hr_bst, ?_, ?_, ?_⟩
      · intro x
        simp only [BinaryTree.mem_node_iff, hl'_mem]
        tauto
      · simp [leftSpine, hw_ls]
      · intro c v hwv
        by_cases hvk : v < k
        · change (if v < k then foldedParentAux k (modifyLeftAt l b (fun L1 => .node w .nil L1)) v
              else if k < v then foldedParentAux c r v else c) =
            (if v < k then foldedParentAux k l v
              else if k < v then foldedParentAux c r v else c)
          simp only [hvk, ↓reduceIte]
          exact hl'_fp k v hwv
        · change (if v < k then foldedParentAux k (modifyLeftAt l b (fun L1 => .node w .nil L1)) v
              else if k < v then foldedParentAux c r v else c) =
            (if v < k then foldedParentAux k l v
              else if k < v then foldedParentAux c r v else c)
          simp only [hvk, ↓reduceIte]
    · subst hbk_eq
      have hmod_eq : modifyLeftAt (.node b l r) b (fun L1 => .node w .nil L1) =
          .node b (.node w .nil l) r := by
        simp [modifyLeftAt]
      dsimp only
      rw [hmod_eq]
      have hwb : w < b := hw b .here
      have hw_lt_l : SplayDeque.Direct.ForallTree (w < ·) l :=
        (SplayDeque.Direct.forallTree_iff _ _).mpr (fun x hx => hw x (.left hx))
      have hnode_w_bst : (BinaryTree.node w .nil l).IsBST :=
        BinaryTree.IsBST.node w .nil l .left hw_lt_l .left hl_bst
      have hlt' : SplayDeque.Direct.ForallTree (· < b) (.node w .nil l) := by
        rw [SplayDeque.Direct.forallTree_iff] at hlt ⊢
        intro x hx
        rcases BinaryTree.mem_node_iff.mp hx with rfl | hnil | hxl
        · exact hwb
        · cases hnil
        · exact hlt x hxl
      refine ⟨BinaryTree.IsBST.node b (.node w .nil l) r hlt' hgt hnode_w_bst hr_bst,
        ?_, ?_, ?_⟩
      · intro x
        simp only [BinaryTree.mem_node_iff, BinaryTree.not_mem_nil, false_or]
        tauto
      · simp [leftSpine]
      · intro c v hwv
        by_cases hvb : v < b
        · have hnot_vw : ¬ v < w := by omega
          change (if v < b then foldedParentAux b (.node w .nil l) v
              else if b < v then foldedParentAux c r v else c) =
            (if v < b then foldedParentAux b l v
              else if b < v then foldedParentAux c r v else c)
          simp only [hvb, ↓reduceIte, foldedParentAux, hnot_vw, hwv]
        · change (if v < b then foldedParentAux b (.node w .nil l) v
              else if b < v then foldedParentAux c r v else c) =
            (if v < b then foldedParentAux b l v
              else if b < v then foldedParentAux c r v else c)
          simp only [hvb, ↓reduceIte]

private theorem modifyLeftAt_rootRightNil {T : BinaryTree ℕ} (ht : T.IsBST)
    (hrr : RootRightNil T) {b : ℕ} (hb : b ∈ leftSpine T)
    (f : BinaryTree ℕ → BinaryTree ℕ) :
    RootRightNil (modifyLeftAt T b f) := by
  cases T with
  | nil => simp [leftSpine] at hb
  | node k l r =>
    have hr_nil : r = .nil := hrr
    subst hr_nil
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb_l | rfl
    · have hbk : b < k := BinaryTree.lt_of_IsBST_left l k .nil ht (mem_of_mem_leftSpine hb_l)
      simp [modifyLeftAt, hbk, RootRightNil]
    · simp [modifyLeftAt, RootRightNil]

private theorem spliceMin_spec {T : BinaryTree ℕ} (ht : T.IsBST) {s : ℕ}
    (hmin : T.minKey? = some s) :
    let T0 := spliceMin T
    T0.IsBST ∧
    (∀ x, x ∈ T0 ↔ x ∈ T ∧ x ≠ s) ∧
    (∃ r0 : List ℕ, leftSpine T0 = r0 ++ (leftSpine T).tail) ∧
    (∀ c v, s < v → foldedParentAux c T0 v = foldedParentAux c T v) := by
  induction T with
  | nil => simp [BinaryTree.minKey?] at hmin
  | node k l r ihl _ =>
    obtain ⟨hlt, hgt, hl_bst, hr_bst⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    cases l with
    | nil =>
      simp only [BinaryTree.minKey?] at hmin
      injection hmin with hks
      subst hks
      dsimp only [spliceMin]
      refine ⟨hr_bst, ?_, ⟨leftSpine r, by simp [leftSpine]⟩, ?_⟩
      · intro x
        simp only [BinaryTree.mem_node_iff, BinaryTree.not_mem_nil, false_or]
        constructor
        · intro hxr
          have := BinaryTree.gt_of_IsBST_right .nil k r ht hxr
          exact ⟨Or.inr hxr, by omega⟩
        · rintro ⟨rfl | hxr, hne⟩
          · exact absurd rfl hne
          · exact hxr
      · intro c v hkv
        have hnot : ¬ v < k := by omega
        change foldedParentAux c r v =
          (if v < k then foldedParentAux k .nil v else if k < v then foldedParentAux c r v else c)
        simp [hnot, hkv]
    | node lk ll lr =>
      have hl_min : (BinaryTree.node lk ll lr).minKey? = some s := by
        cases hm : ll.minKey? <;> simpa [BinaryTree.minKey?, hm] using hmin
      obtain ⟨hl0_bst, hl0_mem, ⟨r0, hl0_ls⟩, hl0_fp⟩ := ihl hl_bst hl_min
      have hs_in_l : s ∈ BinaryTree.node lk ll lr := minKey?_mem hl_min
      have hs_lt_k : s < k := BinaryTree.lt_of_IsBST_left _ k r ht hs_in_l
      have hlt0 : SplayDeque.Direct.ForallTree (· < k) (spliceMin (.node lk ll lr)) := by
        rw [SplayDeque.Direct.forallTree_iff] at hlt ⊢
        intro x hx
        exact hlt x ((hl0_mem x).mp hx).1
      have hsplice_eq : spliceMin (.node k (.node lk ll lr) r) =
          .node k (spliceMin (.node lk ll lr)) r := rfl
      dsimp only
      rw [hsplice_eq]
      refine ⟨BinaryTree.IsBST.node k _ r hlt0 hgt hl0_bst hr_bst, ?_, ?_, ?_⟩
      · intro x
        simp only [BinaryTree.mem_node_iff, hl0_mem]
        constructor
        · rintro (rfl | ⟨hxl, hne⟩ | hxr)
          · exact ⟨Or.inl rfl, by omega⟩
          · exact ⟨Or.inr (Or.inl hxl), hne⟩
          · have := BinaryTree.gt_of_IsBST_right _ k r ht hxr
            exact ⟨Or.inr (Or.inr hxr), by omega⟩
        · rintro ⟨rfl | hxl | hxr, hne⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨hxl, hne⟩)
          · exact Or.inr (Or.inr hxr)
      · refine ⟨r0, ?_⟩
        set lsL := leftSpine (.node lk ll lr)
        have hls_ne : lsL ≠ [] := by simp [lsL, leftSpine]
        have htail_append : lsL.tail ++ [k] = (lsL ++ [k]).tail := by
          cases hlsL : lsL with
          | nil => exact absurd hlsL hls_ne
          | cons hd tl => rfl
        calc leftSpine (.node k (spliceMin (.node lk ll lr)) r)
            = leftSpine (spliceMin (.node lk ll lr)) ++ [k] := rfl
          _ = (r0 ++ lsL.tail) ++ [k] := by rw [hl0_ls]
          _ = r0 ++ (lsL.tail ++ [k]) := List.append_assoc _ _ _
          _ = r0 ++ (lsL ++ [k]).tail := by rw [htail_append]
          _ = r0 ++ (leftSpine (.node k (.node lk ll lr) r)).tail := rfl
      · intro c v hsv
        by_cases hvk : v < k
        · change (if v < k then foldedParentAux k (spliceMin (.node lk ll lr)) v
              else if k < v then foldedParentAux c r v else c) =
            (if v < k then foldedParentAux k (.node lk ll lr) v
              else if k < v then foldedParentAux c r v else c)
          simp only [hvk, ↓reduceIte]
          exact hl0_fp k v hsv
        · change (if v < k then foldedParentAux k (spliceMin (.node lk ll lr)) v
              else if k < v then foldedParentAux c r v else c) =
            (if v < k then foldedParentAux k (.node lk ll lr) v
              else if k < v then foldedParentAux c r v else c)
          simp only [hvk, ↓reduceIte]

private theorem spliceMin_rootRightNil {T : BinaryTree ℕ} (hrr : RootRightNil T) :
    RootRightNil (spliceMin T) := by
  cases T with
  | nil => simp [spliceMin, RootRightNil]
  | node k l r =>
    have hr_nil : r = .nil := hrr
    subst hr_nil
    cases l <;> simp [spliceMin, RootRightNil]

private theorem foldedParentAux_rot_local (a b d : BinaryTree ℕ) (u p c w : ℕ)
    (hup : u < p) (hwu : w ≠ u) :
    foldedParentAux c (.node u a (.node p b d)) w =
      foldedParentAux c (.node p (.node u a b) d) w := by
  by_cases h1 : w < u
  · have h2 : w < p := lt_trans h1 hup
    simp [foldedParentAux, h1, h2]
  · have huw : u < w := by omega
    by_cases h2 : w < p
    · simp [foldedParentAux, h1, huw, h2]
    · by_cases h3 : p < w
      · simp [foldedParentAux, h1, huw, h2, h3]
      · have hwp : w = p := by omega
        subst hwp
        simp [foldedParentAux, h1, hup]

private theorem rotateRightEdge_spec {T : BinaryTree ℕ} (ht : T.IsBST) {u p : ℕ}
    (hedge : IsRightRotEdge T u p) :
    let T' := rotateRightEdge T u p
    u < p ∧ u ∈ T ∧ p ∈ T ∧
    T'.IsBST ∧
    (∀ x, x ∈ T' ↔ x ∈ T) ∧
    (∀ c, foldedParentAux c T u = p) ∧
    (∀ c, foldedParentAux c T' u = foldedParentAux c T p) ∧
    (∀ c w, w ≠ u → foldedParentAux c T' w = foldedParentAux c T w) ∧
    (p ∈ leftSpine T → leftSpine T' = (leftSpine T).erase p) := by
  rcases hedge with ⟨A, B, C, hp_in_T, hsub⟩
  induction T with
  | nil => cases hp_in_T
  | node k l r ihl ihr =>
    obtain ⟨hlt, hgt, hl_bst, hr_bst⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    by_cases hpk : p < k
    · have hp_in_l : p ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hp_in_T with rfl | hpl | hpr
        · omega
        · exact hpl
        · have := BinaryTree.gt_of_IsBST_right l k r ht hpr; omega
      simp only [subtreeAtKey, hpk, ↓reduceIte] at hsub
      obtain ⟨hup, hu_in_l, _, hl'_bst, hl'_mem, hfp_u, hfp'_u, hfp'_w, hls'⟩ :=
        ihl hl_bst hp_in_l hsub
      have huk : u < k := lt_trans hup hpk
      have hlt' : SplayDeque.Direct.ForallTree (· < k) (rotateRightEdge l u p) := by
        rw [SplayDeque.Direct.forallTree_iff] at hlt ⊢
        exact fun x hx => hlt x ((hl'_mem x).mp hx)
      have hrot_eq : rotateRightEdge (.node k l r) u p = .node k (rotateRightEdge l u p) r := by
        simp [rotateRightEdge, hpk]
      dsimp only
      rw [hrot_eq]
      refine ⟨hup, .left hu_in_l, .left hp_in_l,
        BinaryTree.IsBST.node k _ r hlt' hgt hl'_bst hr_bst, ?_, ?_, ?_, ?_, ?_⟩
      · intro x; simp [BinaryTree.mem_node_iff, hl'_mem]
      · intro c; simp [foldedParentAux, huk, hfp_u]
      · intro c; simp [foldedParentAux, huk, hpk, hfp'_u]
      · intro c w hwu
        by_cases hwk : w < k
        · change (if w < k then foldedParentAux k (rotateRightEdge l u p) w
              else if k < w then foldedParentAux c r w else c) =
            (if w < k then foldedParentAux k l w
              else if k < w then foldedParentAux c r w else c)
          simp only [hwk, ↓reduceIte]
          exact hfp'_w k w hwu
        · change (if w < k then foldedParentAux k (rotateRightEdge l u p) w
              else if k < w then foldedParentAux c r w else c) =
            (if w < k then foldedParentAux k l w
              else if k < w then foldedParentAux c r w else c)
          simp only [hwk, ↓reduceIte]
      · intro hp_ls
        simp only [leftSpine, List.mem_append, List.mem_singleton] at hp_ls
        have hp_ls_l : p ∈ leftSpine l := by
          rcases hp_ls with h | rfl
          · exact h
          · omega
        simp only [leftSpine, hls' hp_ls_l]
        exact (List.erase_append_left [k] hp_ls_l).symm
    · by_cases hkp : k < p
      · have hp_in_r : p ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hp_in_T with rfl | hpl | hpr
          · omega
          · have := BinaryTree.lt_of_IsBST_left l k r ht hpl; omega
          · exact hpr
        have hnot_pk : ¬ p < k := by omega
        simp only [subtreeAtKey, hnot_pk, ↓reduceIte, hkp] at hsub
        obtain ⟨hup, hu_in_r, _, hr'_bst, hr'_mem, hfp_u, hfp'_u, hfp'_w, _⟩ :=
          ihr hr_bst hp_in_r hsub
        have hku : k < u := BinaryTree.gt_of_IsBST_right l k r ht hu_in_r
        have hnot_uk : ¬ u < k := by omega
        have hgt' : SplayDeque.Direct.ForallTree (k < ·) (rotateRightEdge r u p) := by
          rw [SplayDeque.Direct.forallTree_iff] at hgt ⊢
          exact fun x hx => hgt x ((hr'_mem x).mp hx)
        have hrot_eq : rotateRightEdge (.node k l r) u p = .node k l (rotateRightEdge r u p) := by
          simp [rotateRightEdge, hnot_pk, hkp]
        dsimp only
        rw [hrot_eq]
        refine ⟨hup, .right hu_in_r, .right hp_in_r,
          BinaryTree.IsBST.node k l _ hlt hgt' hl_bst hr'_bst, ?_, ?_, ?_, ?_, ?_⟩
        · intro x; simp [BinaryTree.mem_node_iff, hr'_mem]
        · intro c; simp [foldedParentAux, hnot_uk, hku, hfp_u]
        · intro c; simp [foldedParentAux, hnot_uk, hku, hnot_pk, hkp, hfp'_u]
        · intro c w hwu
          by_cases hwk : w < k
          · change (if w < k then foldedParentAux k l w
                else if k < w then foldedParentAux c (rotateRightEdge r u p) w else c) =
              (if w < k then foldedParentAux k l w
                else if k < w then foldedParentAux c r w else c)
            simp only [hwk, ↓reduceIte]
          · by_cases hkw : k < w
            · change (if w < k then foldedParentAux k l w
                  else if k < w then foldedParentAux c (rotateRightEdge r u p) w else c) =
                (if w < k then foldedParentAux k l w
                  else if k < w then foldedParentAux c r w else c)
              simp only [hwk, ↓reduceIte, hkw]
              exact hfp'_w c w hwu
            · change (if w < k then foldedParentAux k l w
                  else if k < w then foldedParentAux c (rotateRightEdge r u p) w else c) =
                (if w < k then foldedParentAux k l w
                  else if k < w then foldedParentAux c r w else c)
              simp only [hwk, ↓reduceIte, hkw]
        · intro hp_ls
          simp only [leftSpine, List.mem_append, List.mem_singleton] at hp_ls
          rcases hp_ls with hp_l | rfl
          · have := BinaryTree.lt_of_IsBST_left l k r ht (mem_of_mem_leftSpine hp_l)
            omega
          · omega
      · have hpk_eq : p = k := by omega
        subst hpk_eq
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst hl_eq
        obtain ⟨hlt_A, hgt_B, hA_bst, hB_bst⟩ :=
          (SplayDeque.Direct.isBSTNode_iff u A B).mp hl_bst
        have hup : u < p := BinaryTree.lt_of_IsBST_left (.node u A B) p r ht .here
        have hlt_B_p : SplayDeque.Direct.ForallTree (· < p) B := by
          rw [SplayDeque.Direct.forallTree_iff] at hlt ⊢
          exact fun x hx => hlt x (.right hx)
        have hp_bst : (BinaryTree.node p B r).IsBST :=
          BinaryTree.IsBST.node p B r hlt_B_p hgt hB_bst hr_bst
        have hgt_u_pBr : SplayDeque.Direct.ForallTree (u < ·) (.node p B r) := by
          rw [SplayDeque.Direct.forallTree_iff] at hgt_B hgt ⊢
          intro x hx
          rcases BinaryTree.mem_node_iff.mp hx with rfl | hxB | hxr
          · exact hup
          · exact hgt_B x hxB
          · exact lt_trans hup (hgt x hxr)
        have hrot_bst : (BinaryTree.node u A (.node p B r)).IsBST :=
          BinaryTree.IsBST.node u A (.node p B r) hlt_A hgt_u_pBr hA_bst hp_bst
        have hrot_eq : rotateRightEdge (.node p (.node u A B) r) u p = .node u A (.node p B r) := by
          simp [rotateRightEdge]
        dsimp only
        rw [hrot_eq]
        refine ⟨hup, .left .here, .here, hrot_bst, ?_, ?_, ?_, ?_, ?_⟩
        · intro x
          simp only [BinaryTree.mem_node_iff]
          tauto
        · intro c
          simp [foldedParentAux, hup]
        · intro c
          simp [foldedParentAux]
        · intro c w hwu
          exact foldedParentAux_rot_local A B r u p c w hup hwu
        · intro _
          have hp_not_in : p ∉ leftSpine A ++ [u] := by
            intro hmem
            simp only [List.mem_append, List.mem_singleton] at hmem
            rcases hmem with hA | rfl
            · have := BinaryTree.lt_of_IsBST_left (.node u A B) p r ht
                (.left (mem_of_mem_leftSpine hA))
              omega
            · omega
          have herase : ((leftSpine A ++ [u]) ++ [p]).erase p = leftSpine A ++ [u] := by
            rw [List.erase_append_right _ hp_not_in]
            simp
          simpa [leftSpine] using herase.symm

private theorem rotateRightEdge_rootRightNil {T : BinaryTree ℕ} (hrr : RootRightNil T)
    {u p : ℕ} (hp_not_root : rootKey? T ≠ some p) (hp_in_ls : p ∈ leftSpine T)
    (ht : T.IsBST) :
    RootRightNil (rotateRightEdge T u p) := by
  cases T with
  | nil => simp [leftSpine] at hp_in_ls
  | node k l r =>
    have hr_nil : r = .nil := hrr
    subst hr_nil
    simp only [rootKey?, ne_eq, Option.some.injEq] at hp_not_root
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hp_in_ls
    rcases hp_in_ls with hp_l | rfl
    · have hpk : p < k := BinaryTree.lt_of_IsBST_left l k .nil ht (mem_of_mem_leftSpine hp_l)
      simp [rotateRightEdge, hpk, RootRightNil]
    · exact absurd rfl hp_not_root

/-! ## 4. `l2Ancestors` Shrinking and Cascade Fold Specs -/

private theorem foldedParent_iterate_mem_l2Ancestors {P : ℕ} {T : BinaryTree ℕ}
    (ht : T.IsBST) (hkeys : ∀ x ∈ T, 1 ≤ x ∧ x ≤ P) {v : ℕ}
    (hv : v ∈ T ∨ v = P + 1) (m : ℕ) :
    (foldedParent P T)^[m] v ∈ l2Ancestors P T v := by
  have h_iter : ∀ d : ℕ,
      ((foldedParent P T)^[d] v ∈ T ∨ (foldedParent P T)^[d] v = P + 1) ∧
      min (v + d) (P + 1) ≤ (foldedParent P T)^[d] v ∧
      (foldedParent P T)^[d] v ≤ P + 1 := by
    intro d
    induction d with
    | zero =>
      simp only [Function.iterate_zero, id_eq, Nat.add_zero]
      rcases hv with hvT | rfl
      · have hvP := (hkeys v hvT).2
        exact ⟨Or.inl hvT, by omega, by omega⟩
      · exact ⟨Or.inr rfl, by omega, le_rfl⟩
    | succ d ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hd_mem, hd_lo, hd_hi⟩ := ih
      rcases hd_mem with hdT | hdTop
      · obtain ⟨hlt, hle, hmem'⟩ := foldedParent_mem_props ht hkeys hdT
        refine ⟨hmem'.symm, ?_, hle⟩
        omega
      · rw [hdTop]
        have htop : foldedParent P T (P + 1) = P + 1 := by simp [foldedParent]
        rw [htop]
        exact ⟨Or.inr rfl, by omega, le_rfl⟩
  have hv1 : 1 ≤ v := by
    rcases hv with hvT | rfl
    · exact (hkeys v hvT).1
    · omega
  unfold l2Ancestors
  by_cases hm : m < P + 2
  · exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr hm)
  · have hm_eq : (foldedParent P T)^[m] v = P + 1 := by
      obtain ⟨_, hlo, hhi⟩ := h_iter m
      omega
    have hP1_eq : (foldedParent P T)^[P + 1] v = P + 1 := by
      obtain ⟨_, hlo, hhi⟩ := h_iter (P + 1)
      omega
    rw [hm_eq, ← hP1_eq]
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

private theorem l2Ancestors_subset_of_step {P : ℕ} {T T' : BinaryTree ℕ}
    (ht : T.IsBST) (hkeys : ∀ x ∈ T, 1 ≤ x ∧ x ≤ P)
    (S : ℕ → Prop)
    (hS_sub : ∀ a, S a → a ∈ T ∨ a = P + 1)
    (hS_closed : ∀ a, S a → S (foldedParent P T' a))
    (hS_step : ∀ a, S a →
      foldedParent P T' a = foldedParent P T a ∨
      foldedParent P T' a = foldedParent P T (foldedParent P T a))
    {v : ℕ} (hv : S v) :
    l2Ancestors P T' v ⊆ l2Ancestors P T v := by
  have h_sim : ∀ d : ℕ, S ((foldedParent P T')^[d] v) ∧
      ∃ m : ℕ, (foldedParent P T')^[d] v = (foldedParent P T)^[m] v := by
    intro d
    induction d with
    | zero =>
      exact ⟨hv, 0, rfl⟩
    | succ d ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨hSd, m, hmeq⟩ := ih
      refine ⟨hS_closed _ hSd, ?_⟩
      rcases hS_step _ hSd with h1 | h2
      · refine ⟨m + 1, ?_⟩
        rw [h1, hmeq, Function.iterate_succ_apply']
      · refine ⟨m + 2, ?_⟩
        rw [h2, hmeq, Function.iterate_succ_apply', Function.iterate_succ_apply']
  intro y hy
  unfold l2Ancestors at hy
  rcases Finset.mem_image.mp hy with ⟨d, _, rfl⟩
  obtain ⟨_, m, hmeq⟩ := h_sim d
  rw [hmeq]
  exact foldedParent_iterate_mem_l2Ancestors ht hkeys (hS_sub v hv) m

private theorem l2Ancestors_subset_rotateRightEdge {P : ℕ} {T : BinaryTree ℕ}
    (ht : T.IsBST) (hkeys : ∀ x ∈ T, 1 ≤ x ∧ x ≤ P) {u p v : ℕ}
    (hedge : IsRightRotEdge T u p) (hv : v ∈ T) :
    l2Ancestors P (rotateRightEdge T u p) v ⊆ l2Ancestors P T v := by
  obtain ⟨_, hu_in, hp_in, ht'_bst, hmem', hfp_u, hfp'_u, hfp'_w, _⟩ :=
    rotateRightEdge_spec ht hedge
  have hkeys' : ∀ x ∈ rotateRightEdge T u p, 1 ≤ x ∧ x ≤ P :=
    fun x hx => hkeys x ((hmem' x).mp hx)
  refine l2Ancestors_subset_of_step ht hkeys (fun a => a ∈ T ∨ a = P + 1)
    (fun a ha => ha) ?_ ?_ (Or.inl hv)
  · intro a ha
    rcases ha with haT | rfl
    · have haT' : a ∈ rotateRightEdge T u p := (hmem' a).mpr haT
      rcases (foldedParent_mem_props ht'_bst hkeys' haT').2.2 with htop | hmemT'
      · exact Or.inr htop
      · exact Or.inl ((hmem' _).mp hmemT')
    · exact Or.inr (by simp [foldedParent])
  · intro a ha
    by_cases hau : a = u
    · right
      rw [hau]
      have hu_ne : u ≠ P + 1 := by have := (hkeys u hu_in).2; omega
      have hp_ne : p ≠ P + 1 := by have := (hkeys p hp_in).2; omega
      simp [foldedParent, hu_ne, hp_ne, hfp_u, hfp'_u]
    · left
      by_cases ha_top : a = P + 1
      · simp [foldedParent, ha_top]
      · simp [foldedParent, ha_top, hfp'_w _ a hau]

private theorem adjacentPairs_take {α : Type} :
    ∀ (h : ℕ) (xs : List α), 2 * h ≤ xs.length →
      (adjacentPairs xs).take h = adjacentPairs (xs.take (2 * h))
  | 0, xs, _ => by simp [adjacentPairs]
  | h + 1, xs, hlen => by
    rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · have hlen' : 2 * h ≤ rest.length := by simp at hlen; omega
      have hmul : 2 * (h + 1) = 2 * h + 2 := by omega
      rw [hmul]
      simp only [adjacentPairs, List.take_succ_cons]
      rw [adjacentPairs_take h rest hlen']

private theorem mem_map_fst_adjacentPairs {α : Type} :
    ∀ (h : ℕ) (xs : List α) (_ : xs.length = 2 * h) (w : α),
      w ∈ (adjacentPairs xs).map Prod.fst ↔
        ∃ idx : Fin h, w = xs[2 * idx.val]'(by omega)
  | 0, xs, hlen, w => by
    cases xs with
    | nil =>
      simp only [adjacentPairs, List.map_nil, List.not_mem_nil, false_iff]
      rintro ⟨idx, _⟩; exact Fin.elim0 idx
    | cons _ _ => simp at hlen
  | h + 1, xs, hlen, w => by
    rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · have hlen' : rest.length = 2 * h := by simp at hlen; omega
      simp only [adjacentPairs, List.map_cons, List.mem_cons]
      rw [mem_map_fst_adjacentPairs h rest hlen' w]
      constructor
      · rintro (rfl | ⟨idx, rfl⟩)
        · exact ⟨⟨0, by omega⟩, rfl⟩
        · refine ⟨⟨idx.val + 1, by omega⟩, ?_⟩
          have : 2 * (idx.val + 1) = 2 * idx.val + 2 := by omega
          simp [this]
      · rintro ⟨⟨_ | idx', hlt⟩, rfl⟩
        · exact Or.inl rfl
        · right
          refine ⟨⟨idx', by omega⟩, ?_⟩
          have : 2 * (idx' + 1) = 2 * idx' + 2 := by omega
          simp [this]

private theorem cascade_fold_spec {P : ℕ} :
    ∀ (h : ℕ) (U : BinaryTree ℕ) (pre active kept : List ℕ),
      U.IsBST →
      RootRightNil U →
      (∀ x ∈ U, 1 ≤ x ∧ x ≤ P) →
      leftSpine U = pre ++ active ++ kept →
      (hlen : active.length = 2 * h) →
      (hkept : kept ≠ []) →
      let U_end := (adjacentPairs active).foldl (fun acc p => rotateRightEdge acc p.1 p.2) U
      let odds := (adjacentPairs active).map Prod.fst
      U_end.IsBST ∧
      RootRightNil U_end ∧
      (∀ x, x ∈ U_end ↔ x ∈ U) ∧
      leftSpine U_end = pre ++ odds ++ kept ∧
      (∀ idx : Fin h,
        foldedParent P U_end (active[2 * idx.val]'(by omega)) =
          (active ++ kept)[2 * idx.val + 2]'(by
            have hk_pos : 0 < kept.length := List.length_pos_iff.mpr hkept
            simp only [List.length_append]
            omega)) ∧
      (∀ w, w ∉ odds → foldedParent P U_end w = foldedParent P U w) ∧
      (∀ v ∈ U, l2Ancestors P U_end v ⊆ l2Ancestors P U v)
  | 0, U, pre, active, kept, hbst, hrr, _, hls, hlen, _ => by
    cases active with
    | nil =>
      refine ⟨hbst, hrr, fun _ => Iff.rfl, ?_, fun idx => Fin.elim0 idx, fun _ _ => rfl,
        fun _ _ => Finset.Subset.rfl⟩
      simpa [adjacentPairs] using hls
    | cons _ _ => simp at hlen
  | h + 1, U, pre, active, kept, hbst, hrr, hkeys, hls, hlen, hkept => by
    rcases active with _ | ⟨x, _ | ⟨y, activeRest⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · have hlen_rest : activeRest.length = 2 * h := by simp at hlen; omega
      have hk_pos : 0 < kept.length := List.length_pos_iff.mpr hkept
      set restAll := activeRest ++ kept
      have hrest_pos : 0 < restAll.length := by
        simp only [restAll, List.length_append]; omega
      have hls_split : leftSpine U = pre ++ [x, y] ++ restAll := by
        simpa [restAll, List.append_assoc] using hls
      have hlen_U : (leftSpine U).length = pre.length + 2 + restAll.length := by
        rw [hls_split]
        simp [List.length_append]
        omega
      have hx_at : (leftSpine U)[pre.length]'(by omega) = x := by
        simp [hls_split, List.append_assoc]
      have hy_at : (leftSpine U)[pre.length + 1]'(by omega) = y := by
        simp [hls_split, List.append_assoc]
      have hz_at : (leftSpine U)[pre.length + 2]'(by omega) = restAll[0]'hrest_pos := by
        have h1 : (pre ++ ([x, y] ++ restAll))[pre.length + 2]'(by simp; omega) =
            ([x, y] ++ restAll)[2]'(by simp; omega) := by
          rw [List.getElem_append_right (by omega)]
          simp
        simp [hls_split, List.append_assoc] at h1 ⊢
      have hedge_xy : IsRightRotEdge U x y := by
        rw [← hx_at, ← hy_at]
        exact isRightRotEdge_of_leftSpine_adj hbst pre.length (by omega)
      have hfp_y : foldedParentAux (P + 1) U y = restAll[0]'hrest_pos := by
        rw [← hy_at, ← hz_at]
        exact foldedParentAux_leftSpine_adj hbst (P + 1) (pre.length + 1) (by omega)
      have hy_in_ls : y ∈ leftSpine U := by
        rw [hls_split]; simp
      have hy_not_root : rootKey? U ≠ some y := by
        rw [rootKey?_eq_getLast?_leftSpine]
        have hpair := leftSpine_pairwise_lt hbst
        have hy_lt_z : y < restAll[0]'hrest_pos := by
          rw [← hy_at, ← hz_at]
          exact List.pairwise_iff_getElem.mp hpair (pre.length + 1) (pre.length + 2)
            (by omega) (by omega) (by omega)
        have hlast_mem : ∀ r, (leftSpine U).getLast? = some r → restAll[0]'hrest_pos ≤ r := by
          intro r hr
          have hne_U : leftSpine U ≠ [] := by intro hn; simp [hn] at hr
          have hr_eq : (leftSpine U)[(leftSpine U).length - 1]'(by omega) = r := by
            rw [List.getLast?_eq_getElem?] at hr
            simpa [List.getElem?_eq_getElem (by omega : (leftSpine U).length - 1 < (leftSpine U).length)] using hr
          subst hr_eq
          by_cases heq_idx : pre.length + 2 = (leftSpine U).length - 1
          · rw [← hz_at]
            exact le_of_eq (by simp [heq_idx])
          · rw [← hz_at]
            exact le_of_lt (List.pairwise_iff_getElem.mp hpair (pre.length + 2)
              ((leftSpine U).length - 1) (by omega) (by omega) (by omega))
        intro hroot_y
        have := hlast_mem y hroot_y
        omega
      set U1 := rotateRightEdge U x y
      obtain ⟨hxy, hx_in_U, hy_in_U, hU1_bst, hU1_mem, _, hU1_fp_x, hU1_fp_w, hU1_ls⟩ :=
        rotateRightEdge_spec hbst hedge_xy
      have hU1_rr : RootRightNil U1 := rotateRightEdge_rootRightNil hrr hy_not_root hy_in_ls hbst
      have hU1_keys : ∀ w ∈ U1, 1 ≤ w ∧ w ≤ P := fun w hw => hkeys w ((hU1_mem w).mp hw)
      have hy_not_prex : y ∉ pre ++ [x] := by
        have hpair := leftSpine_pairwise_lt hbst
        rw [hls_split, List.append_assoc, List.pairwise_append] at hpair
        have hpair_left : (pre ++ [x]).Pairwise (· < ·) ∧
            ∀ a ∈ pre ++ [x], ∀ b ∈ [y] ++ restAll, a < b := by
          have hp_full := leftSpine_pairwise_lt hbst
          have hrew : leftSpine U = (pre ++ [x]) ++ ([y] ++ restAll) := by
            simpa [List.append_assoc] using hls_split
          rw [hrew, List.pairwise_append] at hp_full
          exact ⟨hp_full.1, hp_full.2.2⟩
        intro hy_mem
        have := hpair_left.2 y hy_mem y (by simp)
        omega
      have hU1_ls_eq : leftSpine U1 = (pre ++ [x]) ++ activeRest ++ kept := by
        rw [hU1_ls hy_in_ls]
        have hrew : leftSpine U = (pre ++ [x]) ++ (y :: restAll) := by
          simpa [List.append_assoc] using hls_split
        rw [hrew, List.erase_append_right _ hy_not_prex]
        simp [restAll, List.append_assoc]
      obtain ⟨hEnd_bst, hEnd_rr, hEnd_mem, hEnd_ls, hEnd_idx, hEnd_other, hEnd_anc⟩ :=
        cascade_fold_spec h U1 (pre ++ [x]) activeRest kept
          hU1_bst hU1_rr hU1_keys hU1_ls_eq hlen_rest hkept
      have hx_not_oddsRest : x ∉ (adjacentPairs activeRest).map Prod.fst := by
        have hp_full := leftSpine_pairwise_lt hbst
        have hrew : leftSpine U = (pre ++ [x, y]) ++ (activeRest ++ kept) := by
          simpa [restAll, List.append_assoc] using hls_split
        rw [hrew, List.pairwise_append] at hp_full
        intro hx_mem
        obtain ⟨idx_ar, h_ar_eq⟩ :=
          (mem_map_fst_adjacentPairs h activeRest hlen_rest x).mp hx_mem
        have hx_in_ar : x ∈ activeRest := h_ar_eq ▸ List.getElem_mem _
        have := hp_full.2.2 x (by simp) x (List.mem_append_left _ hx_in_ar)
        omega
      dsimp only [adjacentPairs, List.foldl_cons, List.map_cons]
      refine ⟨hEnd_bst, hEnd_rr, ?_, ?_, ?_, ?_, ?_⟩
      · intro w; exact (hEnd_mem w).trans (hU1_mem w)
      · simpa [List.append_assoc] using hEnd_ls
      · intro idx
        rcases idx with ⟨_ | idx', hidx_lt⟩
        · simp only [Nat.mul_zero, Nat.zero_add]
          change foldedParent P _ x = restAll[0]'hrest_pos
          rw [hEnd_other x hx_not_oddsRest]
          have hx_ne : x ≠ P + 1 := by have := (hkeys x hx_in_U).2; omega
          simp only [foldedParent, hx_ne, ↓reduceIte]
          rw [hU1_fp_x, hfp_y]
        · have hidx'_lt : idx' < h := by omega
          have h_sub := hEnd_idx ⟨idx', hidx'_lt⟩
          have h1 : (x :: y :: activeRest)[2 * (idx' + 1)]'(by omega) =
              activeRest[2 * idx']'(by omega) := by
            have : 2 * (idx' + 1) = (2 * idx') + 2 := by omega
            simp [this]
          have h2 : ((x :: y :: activeRest) ++ kept)[2 * (idx' + 1) + 2]'(by
              simp only [List.length_append, List.length_cons]; omega) =
              (activeRest ++ kept)[2 * idx' + 2]'(by
                simp only [List.length_append]; omega) := by
            have : 2 * (idx' + 1) + 2 = (2 * idx' + 2) + 2 := by omega
            simp [this]
          rw [h1, h2]
          exact h_sub
      · intro w hw_not
        have hwx : w ≠ x := fun h => hw_not (by simp [h])
        have hw_rest : w ∉ (adjacentPairs activeRest).map Prod.fst :=
          fun h => hw_not (by simp [h])
        rw [hEnd_other w hw_rest]
        by_cases hw_top : w = P + 1
        · simp [foldedParent, hw_top]
        · simp [foldedParent, hw_top, U1, hU1_fp_w _ w hwx]
      · intro v hv
        have hv1 : v ∈ U1 := (hU1_mem v).mpr hv
        exact Finset.Subset.trans (hEnd_anc v hv1)
          (l2Ancestors_subset_rotateRightEdge hbst hkeys hedge_xy hv)

/-! ## 5. `takeThrough`, `FoldedStateInv`, Lifetimes (`insStep` / `popStepIdx`), and `rInt` -/

private theorem takeThrough_spec {ls : List ℕ} (hnodup : ls.Nodup) {b : ℕ} (hb : b ∈ ls) :
    let sub := takeThrough ls b
    ∃ upper : List ℕ,
      ls = sub ++ upper ∧
      sub ≠ [] ∧
      sub.head? = ls.head? ∧
      sub.getLast? = some b ∧
      nextOnSpine ls b = upper.head? := by
  induction ls with
  | nil => simp at hb
  | cons a rest ih =>
    rcases List.nodup_cons.mp hnodup with ⟨ha_not, hrest_nodup⟩
    by_cases hab : a = b
    · subst hab
      refine ⟨rest, ?_, by simp [takeThrough], by simp [takeThrough], by simp [takeThrough], ?_⟩
      · simp [takeThrough]
      · cases rest <;> simp [nextOnSpine]
    · have hb_rest : b ∈ rest := by
        rcases List.mem_cons.mp hb with rfl | h
        · exact absurd rfl hab
        · exact h
      obtain ⟨upper, hrest_eq, hsub_ne, _, hsub_last, hnext⟩ := ih hrest_nodup hb_rest
      have hba : b ≠ a := Ne.symm hab
      dsimp only
      simp only [takeThrough, hab, ↓reduceIte]
      refine ⟨upper, ?_, by simp, rfl, ?_, ?_⟩
      · rw [List.cons_append]
        exact congrArg (a :: ·) hrest_eq
      · cases htr : takeThrough rest b with
        | nil => exact absurd htr hsub_ne
        | cons _ _ =>
          rw [htr] at hsub_last
          exact hsub_last
      · cases rest with
        | nil => simp at hb_rest
        | cons c cs =>
          simp only [nextOnSpine, hab, ↓reduceIte]
          exact hnext

private theorem getElem_succ_eq_tail {α : Type} (xs : List α) (j : ℕ) (h : j + 1 < xs.length) :
    xs[j + 1]'h = xs.tail[j]'(by cases xs <;> simp at h ⊢; omega) := by
  cases xs with
  | nil => simp at h
  | cons _ _ => rfl

private theorem mem_foldedPopRotsAt_iff {stepIdx s b : ℕ} {st : BinaryTree ℕ × Option ℕ}
    (hb_some : st.2 = some b) (hsub_ne : takeThrough (leftSpine st.1) b ≠ [])
    (e : InternalPopRot) :
    let sub := takeThrough (leftSpine st.1) b
    let k := sub.length - 1
    let h := (k - 1) / 2
    e ∈ foldedPopRotsAt stepIdx st (.pop s) ↔
      ∃ idx : Fin h,
        e = { stepIdx := stepIdx
              s := s
              j := idx.val + 1
              h := h
              x := sub[2 * idx.val + 1]'(by have := List.length_pos_iff.mpr hsub_ne; omega)
              y := sub[2 * idx.val + 2]'(by have := List.length_pos_iff.mpr hsub_ne; omega)
              z := sub[2 * idx.val + 3]'(by have := List.length_pos_iff.mpr hsub_ne; omega) } := by
  dsimp only
  simp only [foldedPopRotsAt, hb_some, List.mem_filterMap, List.mem_range]
  have hlen_pos : 0 < (takeThrough (leftSpine st.1) b).length :=
    List.length_pos_iff.mpr hsub_ne
  constructor
  · rintro ⟨idx, hidx_lt, hmatch⟩
    have h1 : 2 * (idx + 1) - 1 < (takeThrough (leftSpine st.1) b).length := by omega
    have h2 : 2 * (idx + 1) < (takeThrough (leftSpine st.1) b).length := by omega
    have h3 : 2 * (idx + 1) + 1 < (takeThrough (leftSpine st.1) b).length := by omega
    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      List.getElem?_eq_getElem h3] at hmatch
    simp only [Option.some.injEq] at hmatch
    refine ⟨⟨idx, hidx_lt⟩, ?_⟩
    rw [← hmatch]
    have hi2 : 2 * (idx + 1) = 2 * idx + 2 := by omega
    have hi1 : 2 * idx + 2 - 1 = 2 * idx + 1 := by omega
    have hi3 : 2 * idx + 2 + 1 = 2 * idx + 3 := by omega
    simp only [hi2, hi1, hi3]
  · rintro ⟨⟨idx, hidx_lt⟩, rfl⟩
    refine ⟨idx, hidx_lt, ?_⟩
    have hi2 : 2 * (idx + 1) = 2 * idx + 2 := by omega
    have hi1 : 2 * idx + 2 - 1 = 2 * idx + 1 := by omega
    have hi3 : 2 * idx + 2 + 1 = 2 * idx + 3 := by omega
    have h1 : 2 * idx + 1 < (takeThrough (leftSpine st.1) b).length := by omega
    have h2 : 2 * idx + 2 < (takeThrough (leftSpine st.1) b).length := by omega
    have h3 : 2 * idx + 3 < (takeThrough (leftSpine st.1) b).length := by omega
    simp only [hi2, hi1, hi3, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      List.getElem?_eq_getElem h3]

private def FoldedStateInv (P : ℕ) (st : BinaryTree ℕ × Option ℕ) : Prop :=
  st.1.IsBST ∧
  RootRightNil st.1 ∧
  (∀ x ∈ st.1, 1 ≤ x ∧ x ≤ P) ∧
  ((st.1 = .nil ∧ st.2 = none) ∨ (∃ b, st.1 ≠ .nil ∧ st.2 = some b ∧ b ∈ leftSpine st.1))

private def FoldedOpStepSpec (P : ℕ) (st st' : BinaryTree ℕ × Option ℕ) : FoldedOp → Prop
  | .push w =>
    w ∉ st.1 ∧ (∀ x, x ∈ st'.1 ↔ x = w ∨ x ∈ st.1) ∧
    (∀ w', w' ∈ st.1 → foldedParent P st'.1 w' = foldedParent P st.1 w')
  | .shift => st'.1 = st.1
  | .upperRot u v =>
    (∀ x, x ∈ st'.1 ↔ x ∈ st.1) ∧
    foldedParent P st.1 u = v ∧
    foldedParent P st'.1 u = foldedParent P st.1 v ∧
    (∀ w, w ≠ u → foldedParent P st'.1 w = foldedParent P st.1 w)
  | .pop s =>
    s ∈ st.1 ∧ (∀ x, x ∈ st'.1 ↔ x ∈ st.1 ∧ x ≠ s) ∧
    (∀ stepIdx : ℕ, ∀ e ∈ foldedPopRotsAt stepIdx st (.pop s),
      foldedParent P st'.1 e.x = e.z) ∧
    (∀ stepIdx : ℕ, ∀ w ∈ st'.1,
      (∀ e ∈ foldedPopRotsAt stepIdx st (.pop s), w ≠ e.x) →
      foldedParent P st'.1 w = foldedParent P st.1 w)

private theorem foldedOp_step_preserves {P : ℕ} {st : BinaryTree ℕ × Option ℕ} {op : FoldedOp}
    (hinv : FoldedStateInv P st) (hval : op.Valid P st) :
    let st' := op.step st
    FoldedStateInv P st' ∧
    (∀ v ∈ st.1, v ∈ st'.1 →
      foldedParent P st.1 v ≤ foldedParent P st'.1 v ∧
      l2Ancestors P st'.1 v ⊆ l2Ancestors P st.1 v) ∧
    FoldedOpStepSpec P st st' op := by
  obtain ⟨hbst, hrr, hkeys, hcur⟩ := hinv
  cases op with
  | push w =>
    obtain ⟨hw1, hwP, hw_lt, hnil_iff, hb_ls⟩ := hval
    have hw_not_mem : w ∉ st.1 := fun h => Nat.lt_irrefl w (hw_lt w h)
    rcases hcur with ⟨hnil, hnone⟩ | ⟨b, hne, hsome, hb_in_ls⟩
    · dsimp only [FoldedOp.step, FoldedOpStepSpec]
      rw [hnone, hnil]
      dsimp only
      have hbst' : (BinaryTree.node w .nil .nil).IsBST :=
        BinaryTree.IsBST.node w .nil .nil .left .left .left .left
      refine ⟨⟨hbst', rfl, ?_, Or.inr ⟨w, by simp, rfl, by simp [leftSpine]⟩⟩, ?_, ?_⟩
      · intro x hx
        rcases BinaryTree.mem_node_iff.mp hx with rfl | h | h
        · exact ⟨hw1, hwP⟩
        · cases h
        · cases h
      · intro v hv; cases hv
      · refine ⟨by simp, ?_, fun w' hw' => by cases hw'⟩
        intro x; simp [BinaryTree.mem_node_iff]
    · dsimp only [FoldedOp.step]
      rw [hsome]
      dsimp only
      obtain ⟨hbst', hmem', hw_ls', hfp'⟩ := modifyLeftAt_push_spec hbst hb_in_ls hw_lt
      have hrr' := modifyLeftAt_rootRightNil hbst hrr hb_in_ls (fun L1 => .node w .nil L1)
      have hkeys' : ∀ x ∈ modifyLeftAt st.1 b (fun L1 => .node w .nil L1), 1 ≤ x ∧ x ≤ P := by
        intro x hx
        rcases (hmem' x).mp hx with rfl | hx_old
        · exact ⟨hw1, hwP⟩
        · exact hkeys x hx_old
      have hne' : modifyLeftAt st.1 b (fun L1 => .node w .nil L1) ≠ .nil :=
        BinaryTree.ne_nil_of_mem w ((hmem' w).mpr (Or.inl rfl))
      have hfp_eq : ∀ a, a ∈ st.1 ∨ a = P + 1 →
          foldedParent P (modifyLeftAt st.1 b (fun L1 => .node w .nil L1)) a =
            foldedParent P st.1 a := by
        intro a ha
        rcases ha with ha_old | rfl
        · have ha_ne : a ≠ P + 1 := by have := (hkeys a ha_old).2; omega
          simp only [foldedParent, ha_ne, ↓reduceIte]
          exact hfp' (P + 1) a (hw_lt a ha_old)
        · simp [foldedParent]
      refine ⟨⟨hbst', hrr', hkeys', Or.inr ⟨w, hne', rfl, hw_ls'⟩⟩, ?_, ?_⟩
      · intro v hv _
        refine ⟨le_of_eq (hfp_eq v (Or.inl hv)).symm, ?_⟩
        refine l2Ancestors_subset_of_step hbst hkeys (fun a => a ∈ st.1 ∨ a = P + 1)
          (fun a ha => ha) ?_ ?_ (Or.inl hv)
        · intro a ha
          rw [hfp_eq a ha]
          rcases ha with ha_old | rfl
          · exact (foldedParent_mem_props hbst hkeys ha_old).2.2.symm
          · exact Or.inr (by simp [foldedParent])
        · intro a ha
          exact Or.inl (hfp_eq a ha)
      · exact ⟨hw_not_mem, hmem', fun w' hw' => hfp_eq w' (Or.inl hw')⟩
  | shift =>
    obtain ⟨b, hsome, hb_ls, hnot_root⟩ := hval
    dsimp only [FoldedOp.step]
    rw [hsome]
    dsimp only
    obtain ⟨upper, hls_eq, hsub_ne, _, hsub_last, hnext⟩ :=
      takeThrough_spec (leftSpine_nodup hbst) hb_ls
    have hupper_ne : upper ≠ [] := by
      intro hu_nil
      rw [rootKey?_eq_getLast?_leftSpine, hls_eq, hu_nil, List.append_nil, hsub_last] at hnot_root
      exact hnot_root rfl
    cases upper with
    | nil => exact absurd rfl hupper_ne
    | cons b2 restU =>
      have hb2_ls : b2 ∈ leftSpine st.1 := by rw [hls_eq]; simp
      have hne : st.1 ≠ .nil := BinaryTree.ne_nil_of_mem b2 (mem_of_mem_leftSpine hb2_ls)
      refine ⟨⟨hbst, hrr, hkeys, Or.inr ⟨b2, hne, hnext, hb2_ls⟩⟩, ?_, rfl⟩
      intro v _ _
      exact ⟨le_rfl, Finset.Subset.rfl⟩
  | upperRot u v =>
    obtain ⟨b, r_root, hsome, hroot, hb_ls, hbu, huv, hvr, hu_ls, hv_ls, hedge⟩ := hval
    dsimp only [FoldedOp.step]
    obtain ⟨_, hu_in, hv_in, hbst', hmem', hfp_u, hfp'_u, hfp'_w, hls'⟩ :=
      rotateRightEdge_spec hbst hedge
    have hv_not_root : rootKey? st.1 ≠ some v := by
      rw [hroot]; intro heq; injection heq with h; omega
    have hrr' : RootRightNil (rotateRightEdge st.1 u v) :=
      rotateRightEdge_rootRightNil hrr hv_not_root hv_ls hbst
    have hkeys' : ∀ x ∈ rotateRightEdge st.1 u v, 1 ≤ x ∧ x ≤ P :=
      fun x hx => hkeys x ((hmem' x).mp hx)
    have hbv_ne : b ≠ v := by omega
    have hb_ls' : b ∈ leftSpine (rotateRightEdge st.1 u v) := by
      rw [hls' hv_ls]
      exact (List.mem_erase_of_ne hbv_ne).mpr hb_ls
    have hne' : rotateRightEdge st.1 u v ≠ .nil :=
      BinaryTree.ne_nil_of_mem b (mem_of_mem_leftSpine hb_ls')
    have hu_ne : u ≠ P + 1 := by have := (hkeys u hu_in).2; omega
    have hv_ne : v ≠ P + 1 := by have := (hkeys v hv_in).2; omega
    have hfp_u_eq : foldedParent P st.1 u = v := by
      simp [foldedParent, hu_ne, hfp_u]
    have hfp'_u_eq : foldedParent P (rotateRightEdge st.1 u v) u = foldedParent P st.1 v := by
      simp [foldedParent, hu_ne, hv_ne, hfp'_u]
    have hfp'_w_eq : ∀ w, w ≠ u →
        foldedParent P (rotateRightEdge st.1 u v) w = foldedParent P st.1 w := by
      intro w hwu
      by_cases hw_top : w = P + 1
      · simp [foldedParent, hw_top]
      · simp [foldedParent, hw_top, hfp'_w _ w hwu]
    refine ⟨⟨hbst', hrr', hkeys', Or.inr ⟨b, hne', hsome, hb_ls'⟩⟩, ?_, ?_⟩
    · intro x hx _
      refine ⟨?_, l2Ancestors_subset_rotateRightEdge hbst hkeys hedge hx⟩
      by_cases hxu : x = u
      · subst hxu
        rw [hfp_u_eq, hfp'_u_eq]
        exact le_of_lt (foldedParent_mem_props hbst hkeys hv_in).1
      · rw [hfp'_w_eq x hxu]
    · exact ⟨hmem', hfp_u_eq, hfp'_u_eq, hfp'_w_eq⟩
  | pop s =>
    obtain ⟨b, hne_st, hmin_s, hsome, hb_ls⟩ := hval
    have hs_mem : s ∈ st.1 := minKey?_mem hmin_s
    obtain ⟨upper, hls_eq, hsub_ne, hsub_head, hsub_last, hnext⟩ :=
      takeThrough_spec (leftSpine_nodup hbst) hb_ls
    set ls := leftSpine st.1
    set sub := takeThrough ls b
    set k := sub.length - 1
    set h := (k - 1) / 2
    set t0 := spliceMin st.1
    obtain ⟨ht0_bst, ht0_mem, ⟨r0, ht0_ls⟩, ht0_fp⟩ := spliceMin_spec hbst hmin_s
    have ht0_rr : RootRightNil t0 := spliceMin_rootRightNil hrr
    have ht0_keys : ∀ x ∈ t0, 1 ≤ x ∧ x ≤ P :=
      fun x hx => hkeys x ((ht0_mem x).mp hx).1
    have ht0_fp_eq : ∀ a, a ∈ t0 ∨ a = P + 1 →
        foldedParent P t0 a = foldedParent P st.1 a := by
      intro a ha
      rcases ha with ha0 | rfl
      · obtain ⟨ha_st, ha_ne_s⟩ := (ht0_mem a).mp ha0
        have hsa : s < a := lt_of_le_of_ne (minKey?_le_of_mem hbst hmin_s ha_st) (Ne.symm ha_ne_s)
        have ha_ne_top : a ≠ P + 1 := by have := (hkeys a ha_st).2; omega
        simp only [foldedParent, ha_ne_top, ↓reduceIte]
        exact ht0_fp (P + 1) a hsa
      · simp [foldedParent]
    have ht0_anc : ∀ v ∈ t0, l2Ancestors P t0 v ⊆ l2Ancestors P st.1 v := by
      intro v hv0
      refine l2Ancestors_subset_of_step hbst hkeys (fun a => a ∈ t0 ∨ a = P + 1)
        (fun a ha => ha.imp (fun h => ((ht0_mem a).mp h).1) id) ?_ ?_ (Or.inl hv0)
      · intro a ha
        rcases ha with ha0 | rfl
        · exact (foldedParent_mem_props ht0_bst ht0_keys ha0).2.2.symm
        · exact Or.inr (by simp [foldedParent])
      · intro a ha
        exact Or.inl (ht0_fp_eq a ha)
    have hsub_cons : sub = s :: sub.tail := by
      cases hsc : sub with
      | nil => exact absurd hsc hsub_ne
      | cons hd tl =>
        have hhd : some hd = some s := by
          calc some hd = sub.head? := by simp [hsc]
            _ = ls.head? := hsub_head
            _ = st.1.minKey? := (minKey?_eq_head?_leftSpine st.1).symm
            _ = some s := hmin_s
        injection hhd with hhd_eq
        subst hhd_eq
        simp
    have hsub_len_pos : 0 < sub.length := List.length_pos_iff.mpr hsub_ne
    have htail_len : sub.tail.length = k := by
      have := congrArg List.length hsub_cons
      simp only [List.length_cons] at this
      omega
    by_cases hk0 : k = 0
    · have hstep_eq : (FoldedOp.pop s).step st =
          (t0, if t0 = .nil then none else nextOnSpine ls b) := by
        simp [FoldedOp.step, hsome, ls, sub, k, t0, hk0]
      dsimp only
      rw [hstep_eq]
      have hh0 : h = 0 := by omega
      have hcur' : (t0 = .nil ∧ (if t0 = .nil then none else nextOnSpine ls b) = none) ∨
          (∃ b', t0 ≠ .nil ∧ (if t0 = .nil then none else nextOnSpine ls b) = some b' ∧
            b' ∈ leftSpine t0) := by
        by_cases ht0_nil : t0 = .nil
        · exact Or.inl ⟨ht0_nil, by simp [ht0_nil]⟩
        · right
          have hupper_ne : upper ≠ [] := by
            intro hu_nil
            have hsub_eq_s : sub = [s] := by
              have htl_nil : sub.tail = [] := List.eq_nil_of_length_eq_zero (by omega)
              rw [hsub_cons, htl_nil]
            have hls_single : leftSpine st.1 = [s] := by
              simpa [ls, hsub_eq_s, hu_nil] using hls_eq
            cases hst1 : st.1 with
            | nil => exact hne_st hst1
            | node rk rl rr =>
              rw [hst1] at hrr hls_single
              have hrr_nil : rr = .nil := hrr
              subst hrr_nil
              have hlen_ls := congrArg List.length hls_single
              simp only [leftSpine, List.length_append, List.length_singleton] at hlen_ls
              have hrl_nil : rl = .nil :=
                (leftSpine_eq_nil_iff rl).mp (List.eq_nil_of_length_eq_zero (by omega))
              subst hrl_nil
              simp only [leftSpine, List.nil_append, List.cons.injEq, and_true] at hls_single
              subst hls_single
              exact ht0_nil (by simp [t0, hst1, spliceMin])
          cases upper with
          | nil => exact absurd rfl hupper_ne
          | cons b2 restU =>
            refine ⟨b2, ht0_nil, by simp [ht0_nil, hnext], ?_⟩
            have htl_nil : sub.tail = [] := List.eq_nil_of_length_eq_zero (by omega)
            have hls_tail : ls.tail = b2 :: restU := by
              rw [hls_eq, hsub_cons, htl_nil]
              rfl
            rw [ht0_ls, hls_tail]
            simp
      refine ⟨⟨ht0_bst, ht0_rr, ht0_keys, hcur'⟩, ?_, ?_⟩
      · intro v _ hv0
        exact ⟨le_of_eq (ht0_fp_eq v (Or.inl hv0)).symm, ht0_anc v hv0⟩
      · refine ⟨hs_mem, ht0_mem, ?_, ?_⟩
        · intro stepIdx e he
          obtain ⟨idx, _⟩ := (mem_foldedPopRotsAt_iff hsome hsub_ne e).mp he
          have hh_zero : ((takeThrough (leftSpine st.1) b).length - 1 - 1) / 2 = 0 := hh0
          exact absurd idx.isLt (by omega)
        · intro _ w hw0 _
          exact ht0_fp_eq w (Or.inl hw0)
    · have hk_pos : 1 ≤ k := by omega
      have h2h_lt : 2 * h < k := by omega
      set active := sub.tail.take (2 * h)
      set kept := sub.tail.drop (2 * h) ++ upper
      have hactive_len : active.length = 2 * h := by
        simp [active, htail_len]; omega
      have hkept_ne : kept ≠ [] := by
        have hdrop_pos : 0 < (sub.tail.drop (2 * h)).length := by
          simp; omega
        have hkept_pos : 0 < kept.length := by
          simp only [kept, List.length_append]; omega
        exact List.ne_nil_of_length_pos hkept_pos
      have hls_tail_eq : ls.tail = active ++ kept := by
        have h1 : active ++ kept = (sub.tail.take (2 * h) ++ sub.tail.drop (2 * h)) ++ upper := by
          simp [active, kept, List.append_assoc]
        rw [h1, List.take_append_drop]
        rw [hls_eq, hsub_cons]
        rfl
      have ht0_ls_split : leftSpine t0 = r0 ++ active ++ kept := by
        rw [ht0_ls, hls_tail_eq, List.append_assoc]
      have hpairs_eq : (adjacentPairs sub.tail).take h = adjacentPairs active :=
        adjacentPairs_take h sub.tail (by omega)
      set tNew := (adjacentPairs active).foldl (fun acc p => rotateRightEdge acc p.1 p.2) t0
      set bNew := if k = 2 * h + 2 then sub[2 * h + 1]? else some b
      have hstep_eq : (FoldedOp.pop s).step st = (tNew, bNew) := by
        simp [FoldedOp.step, hsome, ls, sub, k, h, t0, hk0, hpairs_eq, tNew, bNew]
      dsimp only
      rw [hstep_eq]
      obtain ⟨htNew_bst, htNew_rr, htNew_mem0, htNew_ls, htNew_idx, htNew_other, htNew_anc0⟩ :=
        cascade_fold_spec h t0 r0 active kept
          ht0_bst ht0_rr ht0_keys ht0_ls_split hactive_len hkept_ne
      have htNew_mem : ∀ x, x ∈ tNew ↔ x ∈ st.1 ∧ x ≠ s :=
        fun x => (htNew_mem0 x).trans (ht0_mem x)
      have htNew_keys : ∀ x ∈ tNew, 1 ≤ x ∧ x ≤ P :=
        fun x hx => ht0_keys x ((htNew_mem0 x).mp hx)
      have hb_cand_in_kept : sub.tail[2 * h]'(by omega) ∈ kept := by
        have hdrop_pos : 0 < (sub.tail.drop (2 * h)).length := by
          simp; omega
        have heq_drop : (sub.tail.drop (2 * h))[0]'hdrop_pos = sub.tail[2 * h]'(by omega) := by
          simp
        rw [← heq_drop]
        exact List.mem_append_left _ (List.getElem_mem _)
      have hb_cand_in_ls : sub.tail[2 * h]'(by omega) ∈ leftSpine tNew := by
        rw [htNew_ls]
        exact List.mem_append_right _ hb_cand_in_kept
      have htNew_ne : tNew ≠ .nil :=
        BinaryTree.ne_nil_of_mem _ (mem_of_mem_leftSpine hb_cand_in_ls)
      have hb_at_sub : ∀ j : ℕ, (hj : j < k) →
          sub[j + 1]'(by omega) = sub.tail[j]'(by omega) := by
        intro j hj
        exact getElem_succ_eq_tail sub j (by omega)
      have hbNew_valid : ∃ b', tNew ≠ .nil ∧ bNew = some b' ∧ b' ∈ leftSpine tNew := by
        by_cases heven : k = 2 * h + 2
        · refine ⟨sub.tail[2 * h]'(by omega), htNew_ne, ?_, hb_cand_in_ls⟩
          simp only [bNew, heven, ↓reduceIte]
          rw [List.getElem?_eq_getElem (by omega : 2 * h + 1 < sub.length)]
          exact congrArg some (hb_at_sub (2 * h) h2h_lt)
        · have hk_odd : k = 2 * h + 1 := by omega
          have hb_eq_cand : b = sub.tail[2 * h]'(by omega) := by
            have hlast : sub.getLast? = some (sub[sub.length - 1]'(by omega)) := by
              rw [List.getLast?_eq_getElem?,
                List.getElem?_eq_getElem (by omega : sub.length - 1 < sub.length)]
            rw [hsub_last] at hlast
            injection hlast with hb_eq
            have hidx_eq : sub.length - 1 = 2 * h + 1 := by omega
            calc b = sub[sub.length - 1]'(by omega) := hb_eq
              _ = sub[2 * h + 1]'(by omega) := by simp [hidx_eq]
              _ = sub.tail[2 * h]'(by omega) := hb_at_sub (2 * h) h2h_lt
          refine ⟨b, htNew_ne, by simp [bNew, heven], ?_⟩
          rw [hb_eq_cand]
          exact hb_cand_in_ls
      have hactive_at : ∀ idx : Fin h,
          active[2 * idx.val]'(by omega) = sub[2 * idx.val + 1]'(by omega) := by
        intro idx
        have hlt_take : 2 * idx.val < 2 * h := by omega
        have h1 : active[2 * idx.val]'(by omega) = sub.tail[2 * idx.val]'(by omega) := by
          simp [active]
        rw [h1, ← hb_at_sub (2 * idx.val) (by omega)]
      have hkept_at : ∀ idx : Fin h,
          (active ++ kept)[2 * idx.val + 2]'(by
            have hk_pos' : 0 < kept.length := List.length_pos_iff.mpr hkept_ne
            simp only [List.length_append]; omega) =
          sub[2 * idx.val + 3]'(by omega) := by
        intro idx
        have hlt_k : 2 * idx.val + 2 < k := by omega
        have h1 : (active ++ kept)[2 * idx.val + 2]'(by
            have hk_pos' : 0 < kept.length := List.length_pos_iff.mpr hkept_ne
            simp only [List.length_append]; omega) =
            (sub.tail ++ upper)[2 * idx.val + 2]'(by simp [htail_len]; omega) := by
          have heq_ak : active ++ kept = sub.tail ++ upper := by
            rw [← hls_tail_eq, hls_eq, hsub_cons]; rfl
          simp [heq_ak]
        rw [h1, List.getElem_append_left (by omega : 2 * idx.val + 2 < sub.tail.length),
          ← hb_at_sub (2 * idx.val + 2) hlt_k]
      have hodds_iff : ∀ w, w ∈ (adjacentPairs active).map Prod.fst ↔
          ∃ idx : Fin h, w = sub[2 * idx.val + 1]'(by omega) := by
        intro w
        rw [mem_map_fst_adjacentPairs h active hactive_len w]
        constructor
        · rintro ⟨idx, rfl⟩; exact ⟨idx, hactive_at idx⟩
        · rintro ⟨idx, rfl⟩; exact ⟨idx, (hactive_at idx).symm⟩
      refine ⟨⟨htNew_bst, htNew_rr, htNew_keys, Or.inr hbNew_valid⟩, ?_, ?_⟩
      · intro v hv_st hv_new
        have hv0 : v ∈ t0 := (htNew_mem0 v).mp hv_new
        refine ⟨?_, Finset.Subset.trans (htNew_anc0 v hv0) (ht0_anc v hv0)⟩
        by_cases hv_odds : v ∈ (adjacentPairs active).map Prod.fst
        · obtain ⟨idx, rfl⟩ := (hodds_iff v).mp hv_odds
          have hfp_new : foldedParent P tNew (sub[2 * idx.val + 1]'(by omega)) =
              sub[2 * idx.val + 3]'(by omega) := by
            rw [← hactive_at idx, ← hkept_at idx]
            exact htNew_idx idx
          have hls_len : 2 * idx.val + 3 < (leftSpine st.1).length := by
            change 2 * idx.val + 3 < ls.length
            rw [hls_eq]; simp only [List.length_append]; omega
          have hls_len_sub : 2 * idx.val + 3 < ls.length := hls_len
          have hls_1 : ls[2 * idx.val + 1]'(by omega) = sub[2 * idx.val + 1]'(by omega) := by
            simp only [hls_eq]
            exact List.getElem_append_left (by omega)
          have hls_2 : ls[2 * idx.val + 2]'(by omega) = sub[2 * idx.val + 2]'(by omega) := by
            simp only [hls_eq]
            exact List.getElem_append_left (by omega)
          have hls_3 : ls[2 * idx.val + 3]'(by omega) = sub[2 * idx.val + 3]'(by omega) := by
            simp only [hls_eq]
            exact List.getElem_append_left (by omega)
          have hv_ne_top : sub[2 * idx.val + 1]'(by omega) ≠ P + 1 := by
            have := (hkeys _ hv_st).2; omega
          have hfp_old : foldedParent P st.1 (sub[2 * idx.val + 1]'(by omega)) =
              sub[2 * idx.val + 2]'(by omega) := by
            simp only [foldedParent, hv_ne_top, ↓reduceIte]
            rw [← hls_1, ← hls_2]
            exact foldedParentAux_leftSpine_adj hbst (P + 1) (2 * idx.val + 1) (by omega)
          have hlt23 : sub[2 * idx.val + 2]'(by omega) < sub[2 * idx.val + 3]'(by omega) := by
            rw [← hls_2, ← hls_3]
            exact List.pairwise_iff_getElem.mp (leftSpine_pairwise_lt hbst)
              (2 * idx.val + 2) (2 * idx.val + 3) (by omega) (by omega) (by omega)
          rw [hfp_old, hfp_new]
          exact le_of_lt hlt23
        · rw [htNew_other v hv_odds, ht0_fp_eq v (Or.inl hv0)]
      · refine ⟨hs_mem, htNew_mem, ?_, ?_⟩
        · intro stepIdx e he
          obtain ⟨idx, rfl⟩ := (mem_foldedPopRotsAt_iff hsome hsub_ne e).mp he
          dsimp only
          rw [← hactive_at idx, ← hkept_at idx]
          exact htNew_idx idx
        · intro stepIdx w hw_new hw_not_rot
          have hw0 : w ∈ t0 := (htNew_mem0 w).mp hw_new
          have hw_not_odds : w ∉ (adjacentPairs active).map Prod.fst := by
            intro hw_odds
            obtain ⟨idx, rfl⟩ := (hodds_iff w).mp hw_odds
            let e : InternalPopRot :=
              { stepIdx := stepIdx
                s := s
                j := idx.val + 1
                h := h
                x := sub[2 * idx.val + 1]'(by omega)
                y := sub[2 * idx.val + 2]'(by omega)
                z := sub[2 * idx.val + 3]'(by omega) }
            have he_mem : e ∈ foldedPopRotsAt stepIdx st (.pop s) :=
              (mem_foldedPopRotsAt_iff hsome hsub_ne e).mpr ⟨idx, rfl⟩
            exact hw_not_rot e he_mem rfl
          rw [htNew_other w hw_not_odds, ht0_fp_eq w (Or.inl hw0)]

/-! ### 5B. Trajectory Evolution, Key Lifetimes, and `rInt` Anatomy -/

private theorem validFoldedOps_step {P : ℕ} :
    ∀ (steps : List FoldedOp) (st : BinaryTree ℕ × Option ℕ) (τ : ℕ) (hτ : τ < steps.length),
      ValidFoldedOps P st steps →
      (steps[τ]'hτ).Valid P ((steps.take τ).foldl FoldedOp.step st) ∧
      (steps.take (τ + 1)).foldl FoldedOp.step st =
        (steps[τ]'hτ).step ((steps.take τ).foldl FoldedOp.step st)
  | [], _, _, hτ, _ => by simp at hτ
  | _ :: _, _, 0, _, hval => ⟨hval.1, rfl⟩
  | op :: rest, st, τ + 1, hτ, hval =>
    validFoldedOps_step rest (op.step st) τ (by simp at hτ; omega) hval.2

private theorem proc_step_valid {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ < proc.steps.length) :
    (proc.steps[τ]'hτ).Valid P (proc.stateAt τ) ∧
    proc.stateAt (τ + 1) = (proc.steps[τ]'hτ).step (proc.stateAt τ) :=
  validFoldedOps_step proc.steps (.nil, none) τ hτ proc.hValid

private theorem proc_stateAt_inv {P : ℕ} (proc : FoldedPopProcess P) :
    ∀ τ : ℕ, τ ≤ proc.steps.length → FoldedStateInv P (proc.stateAt τ)
  | 0, _ => by
    refine ⟨BinaryTree.IsBST.left, trivial, ?_, Or.inl ⟨rfl, rfl⟩⟩
    intro x hx
    simp [FoldedPopProcess.stateAt] at hx
  | τ + 1, hle => by
    have hτ : τ < proc.steps.length := by omega
    obtain ⟨hval, hstep⟩ := proc_step_valid proc hτ
    rw [hstep]
    exact (foldedOp_step_preserves (proc_stateAt_inv proc τ (by omega)) hval).1

private theorem mem_range'_iff (a start len : ℕ) :
    a ∈ List.range' start len ↔ start ≤ a ∧ a < start + len := by
  induction len generalizing start with
  | zero => simp [List.range']
  | succ len ih =>
    simp only [List.range', List.mem_cons, ih]
    omega

private theorem pairwise_range'_lt (start len : ℕ) :
    (List.range' start len).Pairwise (· < ·) := by
  induction len generalizing start with
  | zero => simp [List.range']
  | succ len ih =>
    simp only [List.range', List.pairwise_cons, mem_range'_iff]
    exact ⟨fun b hb => by omega, ih (start + 1)⟩

private theorem nodup_range' (start len : ℕ) : (List.range' start len).Nodup :=
  (pairwise_range'_lt start len).imp ne_of_lt

private theorem nodup_filterMap_findIdx {α β : Type} (f : α → Option β) (p : α → Bool) {b : β}
    (hp : ∀ x, p x = true ↔ f x = some b) :
    ∀ (xs : List α), (xs.filterMap f).Nodup → b ∈ xs.filterMap f →
      ∃ hlt : xs.findIdx p < xs.length,
        f (xs[xs.findIdx p]'hlt) = some b ∧
        ∀ (i : ℕ) (hi : i < xs.length), f (xs[i]'hi) = some b ↔ i = xs.findIdx p
  | [], _, hmem => by simp at hmem
  | x :: rest, hnodup, hmem => by
    by_cases hpx : p x = true
    · have hfx : f x = some b := (hp x).mp hpx
      have hfind : (x :: rest).findIdx p = 0 := by simp [List.findIdx_cons, hpx]
      simp only [List.filterMap_cons, hfx, List.nodup_cons] at hnodup
      refine ⟨by simp [hfind], by simp [hfind, hfx], ?_⟩
      intro i hi
      cases i with
      | zero => simp [hfind, hfx]
      | succ j =>
        have hj : j < rest.length := by simp at hi; omega
        simp only [hfind, Nat.succ_ne_zero, iff_false]
        intro hfj
        exact hnodup.1 (List.mem_filterMap.mpr ⟨rest[j]'hj, List.getElem_mem _, hfj⟩)
    · have hfx_ne : f x ≠ some b := fun h => hpx ((hp x).mpr h)
      have hpx_false : p x = false := Bool.eq_false_iff.mpr hpx
      have hfind : (x :: rest).findIdx p = rest.findIdx p + 1 := by
        simp [List.findIdx_cons, hpx_false]
      have ⟨hnodup_rest, hmem_rest⟩ : (rest.filterMap f).Nodup ∧ b ∈ rest.filterMap f := by
        cases hfx_opt : f x with
        | none =>
          simpa [List.filterMap_cons, hfx_opt] using And.intro hnodup hmem
        | some b' =>
          have hne_bb' : b ≠ b' := by rintro rfl; exact hfx_ne hfx_opt
          simp only [List.filterMap_cons, hfx_opt, List.nodup_cons, List.mem_cons] at hnodup hmem
          exact ⟨hnodup.2, hmem.resolve_left hne_bb'⟩
      obtain ⟨hlt_r, hf_r, huniq_r⟩ := nodup_filterMap_findIdx f p hp rest hnodup_rest hmem_rest
      refine ⟨by simp only [hfind, List.length_cons]; omega, ?_, ?_⟩
      · simp only [hfind, List.getElem_cons_succ, hf_r]
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero, hfind]
          exact ⟨fun h => absurd h hfx_ne, fun h => by omega⟩
        | succ j =>
          have hj : j < rest.length := by simp at hi; omega
          simp only [List.getElem_cons_succ, hfind, Nat.add_right_cancel_iff]
          exact huniq_r j hj

private theorem pairwise_filterMap_of_lt {α β : Type} (f : α → Option β) (R : β → β → Prop) :
    ∀ (xs : List α), (xs.filterMap f).Pairwise R →
      ∀ (i₁ i₂ : ℕ) (h1 : i₁ < xs.length) (h2 : i₂ < xs.length),
        i₁ < i₂ → ∀ b₁ b₂, f (xs[i₁]'h1) = some b₁ → f (xs[i₂]'h2) = some b₂ → R b₁ b₂
  | [], _, i₁, _, h1, _, _, _, _, _, _ => by simp at h1
  | _ :: rest, hpair, 0, i₂ + 1, _, h2, _, b₁, b₂, hb1, hb2 => by
    simp only [List.getElem_cons_zero] at hb1
    simp only [List.getElem_cons_succ] at hb2
    simp only [List.filterMap_cons, hb1, List.pairwise_cons] at hpair
    have hi2 : i₂ < rest.length := by simp at h2; omega
    exact hpair.1 b₂ (List.mem_filterMap.mpr ⟨rest[i₂]'hi2, List.getElem_mem _, hb2⟩)
  | x :: rest, hpair, i₁ + 1, i₂ + 1, h1, h2, hlt, b₁, b₂, hb1, hb2 => by
    have hpair_rest : (rest.filterMap f).Pairwise R := by
      cases hfx : f x with
      | none => simpa [List.filterMap_cons, hfx] using hpair
      | some val =>
        simp only [List.filterMap_cons, hfx, List.pairwise_cons] at hpair
        exact hpair.2
    exact pairwise_filterMap_of_lt f R rest hpair_rest i₁ i₂
      (by simp at h1; omega) (by simp at h2; omega) (by omega) b₁ b₂ hb1 hb2

private theorem nodup_of_length_le_toFinset_card {α : Type} [DecidableEq α] :
    ∀ (xs : List α), xs.length ≤ xs.toFinset.card → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: rest, hle => by
    simp only [List.toFinset_cons, List.length_cons] at hle
    have hcard_rest := List.toFinset_card_le rest
    by_cases hx : x ∈ rest.toFinset
    · rw [Finset.insert_eq_of_mem hx] at hle
      omega
    · have hcard_ins := Finset.card_insert_le x rest.toFinset
      exact List.nodup_cons.mpr ⟨fun h => hx (List.mem_toFinset.mpr h),
        nodup_of_length_le_toFinset_card rest (by omega)⟩

private def popKey? : FoldedOp → Option ℕ
  | .pop s => some s
  | _ => none

private def pushKey? : FoldedOp → Option ℕ
  | .push w => some w
  | _ => none

private theorem popKey?_eq_fn : popKey? = (fun | .pop s => some s | _ => none) := by
  funext op; cases op <;> rfl

private theorem pushKey?_eq_fn : pushKey? = (fun | .push w => some w | _ => none) := by
  funext op; cases op <;> rfl

private theorem popStepIdx_spec {P : ℕ} (proc : FoldedPopProcess P) {s : ℕ}
    (hs1 : 1 ≤ s) (hsP : s ≤ P) :
    ∃ hlt : proc.popStepIdx s < proc.steps.length,
      proc.steps[proc.popStepIdx s]'hlt = .pop s ∧
      ∀ (τ : ℕ) (hτ : τ < proc.steps.length),
        proc.steps[τ]'hτ = .pop s ↔ τ = proc.popStepIdx s := by
  have hpop_seq : proc.steps.filterMap popKey? = List.range' 1 P := by
    rw [popKey?_eq_fn]; exact proc.hPopSeq
  have hnodup : (proc.steps.filterMap popKey?).Nodup := by
    rw [hpop_seq]; exact nodup_range' 1 P
  have hmem : s ∈ proc.steps.filterMap popKey? := by
    rw [hpop_seq, mem_range'_iff]; omega
  have hp : ∀ op : FoldedOp, (op == .pop s) = true ↔ popKey? op = some s := by
    intro op; cases op <;> simp [popKey?]
  have hpop_iff : ∀ op : FoldedOp, popKey? op = some s ↔ op = .pop s := by
    intro op; cases op <;> simp [popKey?]
  obtain ⟨hlt, hf, huniq⟩ := nodup_filterMap_findIdx popKey? (fun op => op == .pop s)
    hp proc.steps hnodup hmem
  refine ⟨hlt, (hpop_iff _).mp hf, ?_⟩
  intro τ hτ
  rw [← hpop_iff]
  exact huniq τ hτ

private theorem popStepIdx_lt_iff {P : ℕ} (proc : FoldedPopProcess P) {s₁ s₂ : ℕ}
    (h1_lo : 1 ≤ s₁) (h1_hi : s₁ ≤ P) (h2_lo : 1 ≤ s₂) (h2_hi : s₂ ≤ P) :
    proc.popStepIdx s₁ < proc.popStepIdx s₂ ↔ s₁ < s₂ := by
  obtain ⟨hlt1, hop1, _⟩ := popStepIdx_spec proc h1_lo h1_hi
  obtain ⟨hlt2, hop2, _⟩ := popStepIdx_spec proc h2_lo h2_hi
  have hpop_seq : proc.steps.filterMap popKey? = List.range' 1 P := by
    rw [popKey?_eq_fn]; exact proc.hPopSeq
  have hpair : (proc.steps.filterMap popKey?).Pairwise (· < ·) := by
    rw [hpop_seq]; exact pairwise_range'_lt 1 P
  have hf1 : popKey? (proc.steps[proc.popStepIdx s₁]'hlt1) = some s₁ := by simp [hop1, popKey?]
  have hf2 : popKey? (proc.steps[proc.popStepIdx s₂]'hlt2) = some s₂ := by simp [hop2, popKey?]
  constructor
  · intro hidx_lt
    exact pairwise_filterMap_of_lt popKey? (· < ·) proc.steps hpair
      (proc.popStepIdx s₁) (proc.popStepIdx s₂) hlt1 hlt2 hidx_lt s₁ s₂ hf1 hf2
  · intro hslt
    rcases lt_trichotomy (proc.popStepIdx s₁) (proc.popStepIdx s₂) with hlt | heq | hgt
    · exact hlt
    · have hsame : (FoldedOp.pop s₁) = (FoldedOp.pop s₂) := by
        rw [← hop1, ← hop2]; simp [heq]
      injection hsame with hs_eq
      omega
    · have := pairwise_filterMap_of_lt popKey? (· < ·) proc.steps hpair
        (proc.popStepIdx s₂) (proc.popStepIdx s₁) hlt2 hlt1 hgt s₂ s₁ hf2 hf1
      omega

private theorem exists_push_before_of_mem_treeAt {P : ℕ} (proc : FoldedPopProcess P) :
    ∀ (τ : ℕ), τ ≤ proc.steps.length → ∀ v ∈ proc.treeAt τ,
      ∃ (i : ℕ) (hi : i < proc.steps.length), i < τ ∧ proc.steps[i]'hi = .push v
  | 0, _, v, hv => by cases hv
  | τ + 1, hle, v, hv => by
    have hτ : τ < proc.steps.length := by omega
    by_cases hv_prev : v ∈ proc.treeAt τ
    · obtain ⟨i, hi, hilt, heq⟩ := exists_push_before_of_mem_treeAt proc τ (by omega) v hv_prev
      exact ⟨i, hi, by omega, heq⟩
    · obtain ⟨hval, hstep⟩ := proc_step_valid proc hτ
      have hinv := proc_stateAt_inv proc τ (by omega)
      have hpres := foldedOp_step_preserves hinv hval
      have hv' : v ∈ ((proc.steps[τ]'hτ).step (proc.stateAt τ)).1 := by
        simpa [FoldedPopProcess.treeAt, hstep] using hv
      cases hop : proc.steps[τ]'hτ with
      | push w =>
        rw [hop] at hpres hv'
        rcases (hpres.2.2.2.1 v).mp hv' with rfl | hold
        · exact ⟨τ, hτ, by omega, hop⟩
        · exact absurd hold hv_prev
      | shift =>
        rw [hop] at hpres hv'
        dsimp only [FoldedOpStepSpec] at hpres
        rw [hpres.2.2] at hv'
        exact absurd hv' hv_prev
      | upperRot u u' =>
        rw [hop] at hpres hv'
        exact absurd ((hpres.2.2.1 v).mp hv') hv_prev
      | pop s =>
        rw [hop] at hpres hv'
        exact absurd ((hpres.2.2.2.1 v).mp hv').1 hv_prev

private theorem insStep_spec {P : ℕ} (proc : FoldedPopProcess P) {v : ℕ}
    (hv1 : 1 ≤ v) (hvP : v ≤ P) :
    (∃ hlt : proc.insStep v < proc.steps.length,
      proc.steps[proc.insStep v]'hlt = .push v ∧
      ∀ (τ : ℕ) (hτ : τ < proc.steps.length),
        proc.steps[τ]'hτ = .push v ↔ τ = proc.insStep v) ∧
    proc.insStep v < proc.popStepIdx v := by
  have hmem_push : ∀ u : ℕ, 1 ≤ u → u ≤ P → u ∈ proc.steps.filterMap pushKey? := by
    intro u hu1 huP
    obtain ⟨hlt_pop, hop_pop, _⟩ := popStepIdx_spec proc hu1 huP
    have hinv_pop := proc_stateAt_inv proc (proc.popStepIdx u) (by omega)
    obtain ⟨hval_pop, _⟩ := proc_step_valid proc hlt_pop
    have hpres_pop := foldedOp_step_preserves hinv_pop hval_pop
    rw [hop_pop] at hpres_pop
    have hu_in : u ∈ proc.treeAt (proc.popStepIdx u) := hpres_pop.2.2.1
    obtain ⟨i, hi, _, hipush⟩ :=
      exists_push_before_of_mem_treeAt proc (proc.popStepIdx u) (by omega) u hu_in
    exact List.mem_filterMap.mpr ⟨proc.steps[i]'hi, List.getElem_mem _, by simp [hipush, pushKey?]⟩
  have hpush_len : (proc.steps.filterMap pushKey?).length = P := by
    rw [pushKey?_eq_fn]; exact proc.hPushCount
  have hnodup_push : (proc.steps.filterMap pushKey?).Nodup := by
    apply nodup_of_length_le_toFinset_card
    rw [hpush_len]
    have hinj : Set.InjOn (· + 1) (Finset.range P : Set ℕ) :=
      fun a _ b _ hab => by dsimp only at hab; omega
    have hsub : (Finset.range P).image (· + 1) ⊆ (proc.steps.filterMap pushKey?).toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      have hi_lt : i < P := Finset.mem_range.mp hi
      exact List.mem_toFinset.mpr (hmem_push (i + 1) (by omega) (by omega))
    calc P = (Finset.range P).card := (Finset.card_range P).symm
      _ = ((Finset.range P).image (· + 1)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (proc.steps.filterMap pushKey?).toFinset.card := Finset.card_le_card hsub
  have hp : ∀ op : FoldedOp, (op == .push v) = true ↔ pushKey? op = some v := by
    intro op; cases op <;> simp [pushKey?]
  have hpush_iff : ∀ op : FoldedOp, pushKey? op = some v ↔ op = .push v := by
    intro op; cases op <;> simp [pushKey?]
  obtain ⟨hlt, hf, huniq⟩ := nodup_filterMap_findIdx pushKey? (fun op => op == .push v)
    hp proc.steps hnodup_push (hmem_push v hv1 hvP)
  have huniq' : ∀ (τ : ℕ) (hτ : τ < proc.steps.length),
      proc.steps[τ]'hτ = .push v ↔ τ = proc.insStep v := by
    intro τ hτ; rw [← hpush_iff]; exact huniq τ hτ
  refine ⟨⟨hlt, (hpush_iff _).mp hf, huniq'⟩, ?_⟩
  obtain ⟨hlt_pop, hop_pop, _⟩ := popStepIdx_spec proc hv1 hvP
  have hinv_pop := proc_stateAt_inv proc (proc.popStepIdx v) (by omega)
  obtain ⟨hval_pop, _⟩ := proc_step_valid proc hlt_pop
  have hpres_pop := foldedOp_step_preserves hinv_pop hval_pop
  rw [hop_pop] at hpres_pop
  obtain ⟨i, hi, hi_lt_pop, hipush⟩ :=
    exists_push_before_of_mem_treeAt proc (proc.popStepIdx v) (by omega) v hpres_pop.2.2.1
  have hi_eq : i = proc.insStep v := (huniq' i hi).mp hipush
  omega

private theorem mem_treeAt_iff {P : ℕ} (proc : FoldedPopProcess P) {v : ℕ}
    (hv1 : 1 ≤ v) (hvP : v ≤ P) :
    ∀ (τ : ℕ), τ ≤ proc.steps.length →
      (v ∈ proc.treeAt τ ↔ proc.insStep v < τ ∧ τ ≤ proc.popStepIdx v)
  | 0, _ => by
    simp only [FoldedPopProcess.treeAt, FoldedPopProcess.stateAt, List.take_zero,
      List.foldl_nil, BinaryTree.not_mem_nil, false_iff]
    omega
  | τ + 1, hle => by
    have hτ : τ < proc.steps.length := by omega
    have ih := mem_treeAt_iff proc hv1 hvP τ (by omega)
    obtain ⟨⟨_, _, hins_uniq⟩, hins_lt_pop⟩ := insStep_spec proc hv1 hvP
    obtain ⟨_, _, hpop_uniq⟩ := popStepIdx_spec proc hv1 hvP
    obtain ⟨hval, hstep⟩ := proc_step_valid proc hτ
    have hinv := proc_stateAt_inv proc τ (by omega)
    have hpres := foldedOp_step_preserves hinv hval
    have htree_step : proc.treeAt (τ + 1) = ((proc.steps[τ]'hτ).step (proc.stateAt τ)).1 := by
      simp [FoldedPopProcess.treeAt, hstep]
    rw [htree_step]
    cases hop : proc.steps[τ]'hτ with
    | push w =>
      rw [hop] at hpres
      rw [hpres.2.2.2.1 v]
      have hne_pop : τ ≠ proc.popStepIdx v := by
        intro heq
        have := (hpop_uniq τ hτ).mpr heq
        rw [hop] at this; cases this
      by_cases hvw : v = w
      · subst hvw
        have hτ_eq : τ = proc.insStep v := (hins_uniq τ hτ).mp hop
        simp only [true_or, true_iff]
        omega
      · have hne_ins : τ ≠ proc.insStep v := by
          intro heq
          have := (hins_uniq τ hτ).mpr heq
          rw [hop] at this
          injection this with hwv
          exact hvw hwv.symm
        simp only [hvw, false_or]
        change v ∈ proc.treeAt τ ↔ _
        rw [ih]
        omega
    | shift =>
      rw [hop] at hpres
      have hne_ins : τ ≠ proc.insStep v := by
        intro heq; have := (hins_uniq τ hτ).mpr heq; rw [hop] at this; cases this
      have hne_pop : τ ≠ proc.popStepIdx v := by
        intro heq; have := (hpop_uniq τ hτ).mpr heq; rw [hop] at this; cases this
      rw [hpres.2.2]
      change v ∈ proc.treeAt τ ↔ _
      rw [ih]
      omega
    | upperRot u u' =>
      rw [hop] at hpres
      have hne_ins : τ ≠ proc.insStep v := by
        intro heq; have := (hins_uniq τ hτ).mpr heq; rw [hop] at this; cases this
      have hne_pop : τ ≠ proc.popStepIdx v := by
        intro heq; have := (hpop_uniq τ hτ).mpr heq; rw [hop] at this; cases this
      rw [hpres.2.2.1 v]
      change v ∈ proc.treeAt τ ↔ _
      rw [ih]
      omega
    | pop s =>
      rw [hop] at hpres
      have hne_ins : τ ≠ proc.insStep v := by
        intro heq; have := (hins_uniq τ hτ).mpr heq; rw [hop] at this; cases this
      rw [hpres.2.2.2.1 v]
      change (v ∈ proc.treeAt τ ∧ v ≠ s) ↔ _
      by_cases hvs : v = s
      · subst hvs
        have hτ_eq : τ = proc.popStepIdx v := (hpop_uniq τ hτ).mp hop
        simp only [ne_eq, not_true_eq_false, and_false, false_iff]
        omega
      · have hne_pop : τ ≠ proc.popStepIdx v := by
          intro heq
          have := (hpop_uniq τ hτ).mpr heq
          rw [hop] at this
          injection this with hsv
          exact hvs hsv.symm
        simp only [ne_eq, hvs, not_false_eq_true, and_true]
        rw [ih]
        omega

private theorem multi_step_parent_anc {P : ℕ} (proc : FoldedPopProcess P) {τ₁ τ₂ v : ℕ}
    (h12 : τ₁ ≤ τ₂) (h2 : τ₂ ≤ proc.steps.length)
    (hv1 : v ∈ proc.treeAt τ₁) (hv2 : v ∈ proc.treeAt τ₂) :
    foldedParent P (proc.treeAt τ₁) v ≤ foldedParent P (proc.treeAt τ₂) v ∧
    l2Ancestors P (proc.treeAt τ₂) v ⊆ l2Ancestors P (proc.treeAt τ₁) v := by
  have ⟨hv_lo, hv_hi⟩ := (proc_stateAt_inv proc τ₁ (by omega)).2.2.1 v hv1
  have hins_lt : proc.insStep v < τ₁ := ((mem_treeAt_iff proc hv_lo hv_hi τ₁ (by omega)).mp hv1).1
  have hpop_ge : τ₂ ≤ proc.popStepIdx v := ((mem_treeAt_iff proc hv_lo hv_hi τ₂ h2).mp hv2).2
  induction τ₂ with
  | zero =>
    have h0 : τ₁ = 0 := by omega
    subst h0
    exact ⟨le_rfl, Finset.Subset.rfl⟩
  | succ m ih =>
    by_cases heq : τ₁ = m + 1
    · subst heq
      exact ⟨le_rfl, Finset.Subset.rfl⟩
    · have h1m : τ₁ ≤ m := by omega
      have hvm : v ∈ proc.treeAt m :=
        (mem_treeAt_iff proc hv_lo hv_hi m (by omega)).mpr ⟨by omega, by omega⟩
      obtain ⟨hfp_ih, hanc_ih⟩ := ih h1m (by omega) hvm (by omega)
      have hm_lt : m < proc.steps.length := by omega
      obtain ⟨hval, hstep⟩ := proc_step_valid proc hm_lt
      have hinv := proc_stateAt_inv proc m (by omega)
      have hpres := foldedOp_step_preserves hinv hval
      have hv_next : v ∈ ((proc.steps[m]'hm_lt).step (proc.stateAt m)).1 := by
        simpa [FoldedPopProcess.treeAt, hstep] using hv2
      obtain ⟨hfp_step, hanc_step⟩ := hpres.2.1 v hvm hv_next
      have htree_eq : proc.treeAt (m + 1) = ((proc.steps[m]'hm_lt).step (proc.stateAt m)).1 := by
        simp [FoldedPopProcess.treeAt, hstep]
      rw [htree_eq]
      exact ⟨le_trans hfp_ih hfp_step, Finset.Subset.trans hanc_step hanc_ih⟩

private theorem mem_collectFoldedPopRots_iff :
    ∀ (steps : List FoldedOp) (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (e : InternalPopRot),
      e ∈ collectFoldedPopRots idx st steps ↔
        ∃ (k : ℕ) (hk : k < steps.length),
          e ∈ foldedPopRotsAt (idx + k) ((steps.take k).foldl FoldedOp.step st) (steps[k]'hk)
  | [], _, _, _ => by simp [collectFoldedPopRots]
  | op :: rest, idx, st, e => by
    simp only [collectFoldedPopRots, List.mem_append]
    rw [mem_collectFoldedPopRots_iff rest (idx + 1) (op.step st) e]
    constructor
    · rintro (h0 | ⟨k, hk, hmem⟩)
      · exact ⟨0, by simp, by simpa using h0⟩
      · refine ⟨k + 1, by simp; omega, ?_⟩
        have hidx : idx + (k + 1) = idx + 1 + k := by omega
        rw [hidx]
        exact hmem
    · rintro ⟨_ | k, hk, hmem⟩
      · exact Or.inl (by simpa using hmem)
      · right
        refine ⟨k, by simp at hk; omega, ?_⟩
        have hidx : idx + 1 + k = idx + (k + 1) := by omega
        rw [hidx]
        exact hmem

private theorem foldedPopRotsAt_basic {idx : ℕ} {st : BinaryTree ℕ × Option ℕ} {op : FoldedOp}
    {e : InternalPopRot} (he : e ∈ foldedPopRotsAt idx st op) :
    ∃ s, op = .pop s ∧ e.stepIdx = idx ∧ e.s = s := by
  cases op with
  | push _ => simp [foldedPopRotsAt] at he
  | shift => simp [foldedPopRotsAt] at he
  | upperRot _ _ => simp [foldedPopRotsAt] at he
  | pop s =>
    refine ⟨s, rfl, ?_⟩
    cases hst2 : st.2 with
    | none => simp [foldedPopRotsAt, hst2] at he
    | some b =>
      simp only [foldedPopRotsAt, hst2, List.mem_filterMap, List.mem_range] at he
      rcases he with ⟨i, _, hmatch⟩
      cases h1 : (takeThrough (leftSpine st.1) b)[2 * (i + 1) - 1]? <;>
        cases h2 : (takeThrough (leftSpine st.1) b)[2 * (i + 1)]? <;>
        cases h3 : (takeThrough (leftSpine st.1) b)[2 * (i + 1) + 1]? <;>
        simp [h1, h2, h3] at hmatch
      subst hmatch
      exact ⟨rfl, rfl⟩

private theorem mem_rInt_stepIdx_iff {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ < proc.steps.length) (e : InternalPopRot) :
    (e ∈ proc.rInt ∧ e.stepIdx = τ) ↔
      e ∈ foldedPopRotsAt τ (proc.stateAt τ) (proc.steps[τ]'hτ) := by
  simp only [FoldedPopProcess.rInt, List.mem_toFinset, mem_collectFoldedPopRots_iff, Nat.zero_add]
  constructor
  · rintro ⟨⟨k, hk, hmem⟩, rfl⟩
    obtain ⟨_, _, hstep_eq, _⟩ := foldedPopRotsAt_basic hmem
    subst hstep_eq
    exact hmem
  · intro hmem
    obtain ⟨_, _, hstep_eq, _⟩ := foldedPopRotsAt_basic hmem
    exact ⟨⟨τ, hτ, hmem⟩, hstep_eq⟩

private theorem rInt_props {P : ℕ} (proc : FoldedPopProcess P) {e : InternalPopRot}
    (he : e ∈ proc.rInt) :
    e.stepIdx < proc.steps.length ∧
    1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P ∧
    e.stepIdx = proc.popStepIdx e.s ∧
    1 ≤ e.j ∧ e.j ≤ e.h ∧
    e.x ∈ proc.treeAt e.stepIdx ∧
    e.x ∈ proc.treeAt (e.stepIdx + 1) ∧
    foldedParent P (proc.treeAt e.stepIdx) e.x = e.y ∧
    foldedParent P (proc.treeAt (e.stepIdx + 1)) e.x = e.z := by
  have he_col : e ∈ collectFoldedPopRots 0 (.nil, none) proc.steps :=
    List.mem_toFinset.mp he
  obtain ⟨τ, hτ, hmem_at⟩ := (mem_collectFoldedPopRots_iff _ _ _ _).mp he_col
  simp only [Nat.zero_add] at hmem_at
  obtain ⟨s, hop_s, _, _⟩ := foldedPopRotsAt_basic hmem_at
  change e ∈ foldedPopRotsAt τ (proc.stateAt τ) (proc.steps[τ]'hτ) at hmem_at
  obtain ⟨hval, hstep⟩ := proc_step_valid proc hτ
  have hinv := proc_stateAt_inv proc τ (by omega)
  have hpres := foldedOp_step_preserves hinv hval
  obtain ⟨hbst, _, hkeys, _⟩ := hinv
  rw [hop_s] at hval hmem_at hpres
  obtain ⟨b, _, hmin_s, hsome, hb_ls⟩ := hval
  obtain ⟨upper, hls_eq, hsub_ne, hsub_head, _, _⟩ :=
    takeThrough_spec (leftSpine_nodup hbst) hb_ls
  obtain ⟨idx, he_struct⟩ := (mem_foldedPopRotsAt_iff hsome hsub_ne e).mp hmem_at
  let ls := leftSpine (proc.stateAt τ).1
  let sub := takeThrough ls b
  have hsub_cons : sub = e.s :: sub.tail := by
    have hse : e.s = s := congrArg InternalPopRot.s he_struct
    rw [hse]
    cases hsc : takeThrough (leftSpine (proc.stateAt τ).1) b with
    | nil => exact absurd hsc hsub_ne
    | cons hd tl =>
      have hhd : some hd = some s := by
        calc some hd = (takeThrough (leftSpine (proc.stateAt τ).1) b).head? := by simp [hsc]
          _ = (leftSpine (proc.stateAt τ).1).head? := hsub_head
          _ = (proc.stateAt τ).1.minKey? := (minKey?_eq_head?_leftSpine _).symm
          _ = some s := hmin_s
      injection hhd with hhd_eq
      subst hhd_eq
      change takeThrough (leftSpine (proc.stateAt τ).1) b =
        hd :: (takeThrough (leftSpine (proc.stateAt τ).1) b).tail
      simp [hsc]
  have hsub0 : sub[0]'(List.length_pos_iff.mpr hsub_ne) = e.s := by
    have h0_opt : sub[0]? = some e.s := by
      dsimp only [sub, ls]
      rw [show takeThrough (leftSpine (proc.stateAt τ).1) b = e.s :: sub.tail from hsub_cons]
      rfl
    rw [List.getElem?_eq_getElem (List.length_pos_iff.mpr hsub_ne)] at h0_opt
    exact Option.some.inj h0_opt
  have hls_len_eq : ls.length = sub.length + upper.length := by
    have h1 := congrArg List.length hls_eq
    simpa only [List.length_append] using h1
  have hls_len : 2 * idx.val + 3 < ls.length := by
    have := idx.isLt
    have := List.length_pos_iff.mpr hsub_ne
    dsimp only [sub, ls] at hls_len_eq ⊢
    omega
  have hls_at : ∀ m : ℕ, (hm : m < sub.length) →
      ls[m]'(by omega) = sub[m]'hm := by
    intro m hm
    have hopt : ls[m]? = (sub ++ upper)[m]? := congrArg (·[m]?) hls_eq
    rw [List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by simp only [List.length_append]; omega),
      List.getElem_append_left hm] at hopt
    exact Option.some.inj hopt
  have hpair := leftSpine_pairwise_lt hbst
  have hlt_sub : ∀ m₁ m₂ : ℕ, (hm1 : m₁ < sub.length) → (hm2 : m₂ < sub.length) →
      m₁ < m₂ → sub[m₁]'hm1 < sub[m₂]'hm2 := by
    intro m₁ m₂ hm1 hm2 h12
    rw [← hls_at m₁ hm1, ← hls_at m₂ hm2]
    exact List.pairwise_iff_getElem.mp hpair m₁ m₂ _ _ h12
  have hs_mem : s ∈ proc.treeAt τ := hpres.2.2.1
  have hs_bounds := hkeys s hs_mem
  have hx_eq : e.x = sub[2 * idx.val + 1]'(by dsimp only [sub, ls]; have := idx.isLt; omega) :=
    congrArg InternalPopRot.x he_struct
  have hy_eq : e.y = sub[2 * idx.val + 2]'(by dsimp only [sub, ls]; have := idx.isLt; omega) :=
    congrArg InternalPopRot.y he_struct
  have hz_eq : e.z = sub[2 * idx.val + 3]'(by dsimp only [sub, ls]; have := idx.isLt; omega) :=
    congrArg InternalPopRot.z he_struct
  have hs_field : e.s = s := congrArg InternalPopRot.s he_struct
  have hs_lt_x : e.s < e.x := by
    rw [← hsub0, hx_eq]
    exact hlt_sub 0 (2 * idx.val + 1) _ _ (by omega)
  have hx_lt_y : e.x < e.y := by
    rw [hx_eq, hy_eq]
    exact hlt_sub (2 * idx.val + 1) (2 * idx.val + 2) _ _ (by omega)
  have hy_lt_z : e.y < e.z := by
    rw [hy_eq, hz_eq]
    exact hlt_sub (2 * idx.val + 2) (2 * idx.val + 3) _ _ (by omega)
  have hx_in_ls : e.x ∈ ls := by
    rw [hx_eq, ← hls_at (2 * idx.val + 1) _]
    exact List.getElem_mem _
  have hz_in_ls : e.z ∈ ls := by
    rw [hz_eq, ← hls_at (2 * idx.val + 3) _]
    exact List.getElem_mem _
  have hx_in_tree : e.x ∈ proc.treeAt τ := mem_of_mem_leftSpine hx_in_ls
  have hz_in_tree : e.z ∈ proc.treeAt τ := mem_of_mem_leftSpine hz_in_ls
  have hz_le_P : e.z ≤ P := (hkeys e.z hz_in_tree).2
  have hτ_pop : τ = proc.popStepIdx e.s := by
    rw [hs_field]
    exact ((popStepIdx_spec proc hs_bounds.1 hs_bounds.2).2.2 τ hτ).mp hop_s
  have hj_bounds : 1 ≤ e.j ∧ e.j ≤ e.h := by
    have := idx.isLt
    have hj_eq : e.j = idx.val + 1 := congrArg InternalPopRot.j he_struct
    have hh_eq : e.h = ((takeThrough (leftSpine (proc.stateAt τ).1) b).length - 1 - 1) / 2 :=
      congrArg InternalPopRot.h he_struct
    omega
  have htree_next : proc.treeAt (τ + 1) = ((FoldedOp.pop s).step (proc.stateAt τ)).1 := by
    simp [FoldedPopProcess.treeAt, hstep, hop_s]
  have hx_in_next : e.x ∈ proc.treeAt (τ + 1) := by
    rw [htree_next]
    exact (hpres.2.2.2.1 e.x).mpr ⟨hx_in_tree, by omega⟩
  have hfp_before : foldedParent P (proc.treeAt τ) e.x = e.y := by
    unfold FoldedPopProcess.treeAt
    have hx_ne_top : e.x ≠ P + 1 := by omega
    simp only [foldedParent, hx_ne_top, ↓reduceIte]
    have h1 := hls_at (2 * idx.val + 1) (by dsimp only [sub, ls]; have := idx.isLt; omega)
    have h2 := hls_at (2 * idx.val + 2) (by dsimp only [sub, ls]; have := idx.isLt; omega)
    rw [hx_eq, hy_eq, ← h1, ← h2]
    exact foldedParentAux_leftSpine_adj hbst (P + 1) (2 * idx.val + 1)
      (by dsimp only [ls] at hls_len; omega)
  have hfp_after : foldedParent P (proc.treeAt (τ + 1)) e.x = e.z := by
    rw [htree_next]
    exact hpres.2.2.2.2.1 τ e hmem_at
  have hstep_field : e.stepIdx = τ := congrArg InternalPopRot.stepIdx he_struct
  rw [hstep_field]
  exact ⟨hτ, hs_field ▸ hs_bounds.1, hs_lt_x, hx_lt_y, hy_lt_z, hz_le_P,
    hτ_pop, hj_bounds.1, hj_bounds.2, hx_in_tree, hx_in_next, hfp_before, hfp_after⟩

private theorem rInt_same_step_h {P : ℕ} (proc : FoldedPopProcess P) {e₁ e₂ : InternalPopRot}
    (h1 : e₁ ∈ proc.rInt) (h2 : e₂ ∈ proc.rInt) (hstep : e₁.stepIdx = e₂.stepIdx) :
    e₁.h = e₂.h ∧ (e₁.j = e₂.j → e₁ = e₂) := by
  have hτ : e₁.stepIdx < proc.steps.length := (rInt_props proc h1).1
  have hm1 := (mem_rInt_stepIdx_iff proc hτ e₁).mp ⟨h1, rfl⟩
  have hm2 := (mem_rInt_stepIdx_iff proc hτ e₂).mp ⟨h2, hstep.symm⟩
  obtain ⟨s, hop_s, _, _⟩ := foldedPopRotsAt_basic hm1
  obtain ⟨hval, _⟩ := proc_step_valid proc hτ
  have hinv := proc_stateAt_inv proc e₁.stepIdx (by omega)
  rw [hop_s] at hval hm1 hm2
  obtain ⟨b, _, _, hsome, hb_ls⟩ := hval
  obtain ⟨_, _, hsub_ne, _, _, _⟩ := takeThrough_spec (leftSpine_nodup hinv.1) hb_ls
  obtain ⟨idx1, he1⟩ := (mem_foldedPopRotsAt_iff hsome hsub_ne e₁).mp hm1
  obtain ⟨idx2, he2⟩ := (mem_foldedPopRotsAt_iff hsome hsub_ne e₂).mp hm2
  refine ⟨by rw [he1, he2], ?_⟩
  intro hj
  have hidx_val : idx1.val = idx2.val := by
    rw [he1, he2] at hj; dsimp only at hj; omega
  have hidx_eq : idx1 = idx2 := Fin.ext hidx_val
  rw [he1, he2, hidx_eq]

private theorem rInt_ext_step_j {P : ℕ} (proc : FoldedPopProcess P) {e₁ e₂ : InternalPopRot}
    (h1 : e₁ ∈ proc.rInt) (h2 : e₂ ∈ proc.rInt)
    (hstep : e₁.stepIdx = e₂.stepIdx) (hj : e₁.j = e₂.j) : e₁ = e₂ :=
  (rInt_same_step_h proc h1 h2 hstep).2 hj

private theorem rInt_ext_step_x {P : ℕ} (proc : FoldedPopProcess P) {e₁ e₂ : InternalPopRot}
    (h1 : e₁ ∈ proc.rInt) (h2 : e₂ ∈ proc.rInt)
    (hstep : e₁.stepIdx = e₂.stepIdx) (hx : e₁.x = e₂.x) : e₁ = e₂ := by
  have hτ : e₁.stepIdx < proc.steps.length := (rInt_props proc h1).1
  have hm1 := (mem_rInt_stepIdx_iff proc hτ e₁).mp ⟨h1, rfl⟩
  have hm2 := (mem_rInt_stepIdx_iff proc hτ e₂).mp ⟨h2, hstep.symm⟩
  obtain ⟨s, hop_s, _, _⟩ := foldedPopRotsAt_basic hm1
  obtain ⟨hval, _⟩ := proc_step_valid proc hτ
  have hinv := proc_stateAt_inv proc e₁.stepIdx (by omega)
  rw [hop_s] at hval hm1 hm2
  obtain ⟨b, _, _, hsome, hb_ls⟩ := hval
  obtain ⟨upper, hls_eq, hsub_ne, _, _, _⟩ := takeThrough_spec (leftSpine_nodup hinv.1) hb_ls
  obtain ⟨idx1, he1⟩ := (mem_foldedPopRotsAt_iff hsome hsub_ne e₁).mp hm1
  obtain ⟨idx2, he2⟩ := (mem_foldedPopRotsAt_iff hsome hsub_ne e₂).mp hm2
  let sub := takeThrough (leftSpine (proc.stateAt e₁.stepIdx).1) b
  have hnodup_sub : sub.Nodup := by
    have hnodup_ls := leftSpine_nodup hinv.1
    rw [hls_eq, List.nodup_append] at hnodup_ls
    exact hnodup_ls.1
  have hx_sub : sub[2 * idx1.val + 1]'(by dsimp only [sub]; have := idx1.isLt; omega) =
      sub[2 * idx2.val + 1]'(by dsimp only [sub]; have := idx2.isLt; omega) := by
    have hx1 : e₁.x = sub[2 * idx1.val + 1]'(by dsimp only [sub]; have := idx1.isLt; omega) :=
      congrArg InternalPopRot.x he1
    have hx2 : e₂.x = sub[2 * idx2.val + 1]'(by dsimp only [sub]; have := idx2.isLt; omega) :=
      congrArg InternalPopRot.x he2
    exact hx1.symm.trans (hx.trans hx2)
  have hpos_eq : 2 * idx1.val + 1 = 2 * idx2.val + 1 :=
    (List.Nodup.getElem_inj_iff hnodup_sub).mp hx_sub
  have hidx_eq : idx1 = idx2 := Fin.ext (by omega)
  rw [he1, he2, hidx_eq]

private theorem rInt_stepIdx_lt_iff_s_lt {P : ℕ} (proc : FoldedPopProcess P)
    {e₁ e₂ : InternalPopRot} (h1 : e₁ ∈ proc.rInt) (h2 : e₂ ∈ proc.rInt) :
    e₁.stepIdx < e₂.stepIdx ↔ e₁.s < e₂.s := by
  have hp1 := rInt_props proc h1
  have hp2 := rInt_props proc h2
  rw [hp1.2.2.2.2.2.2.1, hp2.2.2.2.2.2.2.1]
  exact popStepIdx_lt_iff proc hp1.2.1 (by omega) hp2.2.1 (by omega)

private theorem rInt_nextCascadeRot_of_lt {P : ℕ} (proc : FoldedPopProcess P)
    {e₁ : InternalPopRot} (h1 : e₁ ∈ proc.rInt) (hj_lt : e₁.j < e₁.h) :
    ∃ e₂ ∈ proc.rInt,
      proc.nextCascadeRot? e₁ = some e₂ ∧
      e₂.stepIdx = e₁.stepIdx ∧
      e₂.s = e₁.s ∧
      e₂.j = e₁.j + 1 ∧
      e₂.x = e₁.z ∧
      e₁.z < e₂.y ∧
      e₂.y < e₂.z := by
  have hp1 := rInt_props proc h1
  have hτ : e₁.stepIdx < proc.steps.length := hp1.1
  have hm1 := (mem_rInt_stepIdx_iff proc hτ e₁).mp ⟨h1, rfl⟩
  obtain ⟨s, hop_s, _, _⟩ := foldedPopRotsAt_basic hm1
  obtain ⟨hval, _⟩ := proc_step_valid proc hτ
  have hinv := proc_stateAt_inv proc e₁.stepIdx (by omega)
  rw [hop_s] at hval hm1
  obtain ⟨b, _, _, hsome, hb_ls⟩ := hval
  obtain ⟨_, _, hsub_ne, _, _, _⟩ := takeThrough_spec (leftSpine_nodup hinv.1) hb_ls
  obtain ⟨idx1, he1⟩ := (mem_foldedPopRotsAt_iff hsome hsub_ne e₁).mp hm1
  let sub := takeThrough (leftSpine (proc.stateAt e₁.stepIdx).1) b
  let h := (sub.length - 1 - 1) / 2
  have hh_eq : e₁.h = h := congrArg InternalPopRot.h he1
  have hj_eq : e₁.j = idx1.val + 1 := congrArg InternalPopRot.j he1
  have hidx2_lt : idx1.val + 1 < h := by omega
  let idx2 : Fin h := ⟨idx1.val + 1, hidx2_lt⟩
  let cand : InternalPopRot :=
    { stepIdx := e₁.stepIdx
      s := s
      j := idx2.val + 1
      h := h
      x := sub[2 * idx2.val + 1]'(by
        have := List.length_pos_iff.mpr hsub_ne; dsimp only [idx2, h, sub] at *; omega)
      y := sub[2 * idx2.val + 2]'(by
        have := List.length_pos_iff.mpr hsub_ne; dsimp only [idx2, h, sub] at *; omega)
      z := sub[2 * idx2.val + 3]'(by
        have := List.length_pos_iff.mpr hsub_ne; dsimp only [idx2, h, sub] at *; omega) }
  have hcand_at : cand ∈ foldedPopRotsAt e₁.stepIdx (proc.stateAt e₁.stepIdx) (proc.steps[e₁.stepIdx]'hτ) := by
    rw [hop_s]
    exact (mem_foldedPopRotsAt_iff hsome hsub_ne cand).mpr ⟨idx2, rfl⟩
  have hcand_rInt : cand ∈ proc.rInt :=
    ((mem_rInt_stepIdx_iff proc hτ cand).mpr hcand_at).1
  have hcand_col : cand ∈ collectFoldedPopRots 0 (.nil, none) proc.steps :=
    List.mem_toFinset.mp hcand_rInt
  have hcand_pred : (cand.stepIdx == e₁.stepIdx && cand.j == e₁.j + 1) = true := by
    simp [cand, idx2, hj_eq]
  cases hfind : proc.nextCascadeRot? e₁ with
  | none =>
    unfold FoldedPopProcess.nextCascadeRot? at hfind
    have hfalse := List.find?_eq_none.mp hfind cand hcand_col
    exact absurd hcand_pred hfalse
  | some e₂ =>
    unfold FoldedPopProcess.nextCascadeRot? at hfind
    have he2_mem : e₂ ∈ proc.rInt :=
      List.mem_toFinset.mpr (List.mem_of_find?_eq_some hfind)
    have he2_pred := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq] at he2_pred
    have he2_eq_cand : e₂ = cand :=
      rInt_ext_step_j proc he2_mem hcand_rInt he2_pred.1 (by simp [cand, idx2, hj_eq, he2_pred.2])
    subst he2_eq_cand
    have hp_cand := rInt_props proc hcand_rInt
    have hcand_x : cand.x = e₁.z := by
      have hz1 : e₁.z = sub[2 * idx1.val + 3]'(by
          have := List.length_pos_iff.mpr hsub_ne; dsimp only [h, sub] at *; omega) :=
        congrArg InternalPopRot.z he1
      have hx2 : cand.x = sub[2 * (idx1.val + 1) + 1]'(by
          have := List.length_pos_iff.mpr hsub_ne; dsimp only [h, sub] at *; omega) := rfl
      have hidx_arith : 2 * (idx1.val + 1) + 1 = 2 * idx1.val + 3 := by omega
      rw [hx2, hz1]
      simp [hidx_arith]
    have hs1 : e₁.s = s := congrArg InternalPopRot.s he1
    exact ⟨cand, hcand_rInt, rfl, rfl, hs1.symm, by simp [cand, idx2, hj_eq],
      hcand_x, hcand_x ▸ hp_cand.2.2.2.1, hp_cand.2.2.2.2.1⟩

private theorem rInt_inj_of_nextCascadeRot_eq {P : ℕ} (proc : FoldedPopProcess P)
    {a₁ a₂ r : InternalPopRot} (ha1 : a₁ ∈ proc.rInt) (ha2 : a₂ ∈ proc.rInt)
    (hr1 : proc.nextCascadeRot? a₁ = some r) (hr2 : proc.nextCascadeRot? a₂ = some r) :
    a₁ = a₂ := by
  unfold FoldedPopProcess.nextCascadeRot? at hr1 hr2
  have hp1 := List.find?_some hr1
  have hp2 := List.find?_some hr2
  simp only [Bool.and_eq_true, beq_iff_eq] at hp1 hp2
  exact rInt_ext_step_j proc ha1 ha2 (by omega) (by omega)

/-! ## 6. Part (3): `mBase` Cardinality, `prevRot` Injectivity, and `(eL, eR)` -/

private def earlierRots {P : ℕ} (proc : FoldedPopProcess P) (e : InternalPopRot) :
    Finset InternalPopRot :=
  proc.rInt.filter (fun e' => e'.x = e.x ∧ e'.stepIdx < e.stepIdx)

private def prevRotIdx {P : ℕ} (proc : FoldedPopProcess P) (e : InternalPopRot) : ℕ :=
  (earlierRots proc e).sup InternalPopRot.stepIdx

private theorem exists_mem_eq_sup_nat {α : Type} [DecidableEq α] (s : Finset α)
    (hs : s.Nonempty) (f : α → ℕ) : ∃ a ∈ s, f a = s.sup f := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert x s' _ ih =>
    rcases s'.eq_empty_or_nonempty with rfl | hs'
    · exact ⟨x, Finset.mem_insert_self x ∅, by simp⟩
    · obtain ⟨b, hb, hfb⟩ := ih hs'
      by_cases hle : f b ≤ f x
      · refine ⟨x, Finset.mem_insert_self x s', le_antisymm ?_ ?_⟩
        · exact Finset.le_sup (Finset.mem_insert_self x s')
        · refine Finset.sup_le (fun y hy => ?_)
          rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact le_rfl
          · have hy_sup := Finset.le_sup (f := f) hy'
            omega
      · refine ⟨b, Finset.mem_insert_of_mem hb, le_antisymm ?_ ?_⟩
        · exact Finset.le_sup (Finset.mem_insert_of_mem hb)
        · refine Finset.sup_le (fun y hy => ?_)
          rcases Finset.mem_insert.mp hy with rfl | hy'
          · omega
          · have hy_sup := Finset.le_sup (f := f) hy'
            omega

private noncomputable def prevRot {P : ℕ} (proc : FoldedPopProcess P) (e : InternalPopRot) :
    InternalPopRot :=
  if h : (earlierRots proc e).Nonempty then
    Classical.choose (exists_mem_eq_sup_nat (earlierRots proc e) h InternalPopRot.stepIdx)
  else e

private theorem prevRot_spec {P : ℕ} (proc : FoldedPopProcess P) {e : InternalPopRot}
    (hne : (earlierRots proc e).Nonempty) :
    prevRot proc e ∈ earlierRots proc e ∧
    prevRot proc e ∈ proc.rInt ∧
    (prevRot proc e).x = e.x ∧
    (prevRot proc e).stepIdx < e.stepIdx ∧
    (prevRot proc e).stepIdx = prevRotIdx proc e ∧
    (∀ e' ∈ earlierRots proc e, e'.stepIdx = prevRotIdx proc e → e' = prevRot proc e) := by
  have hmem_eq : prevRot proc e ∈ earlierRots proc e ∧
      (prevRot proc e).stepIdx = prevRotIdx proc e := by
    simp only [prevRot, hne, ↓reduceDIte]
    exact Classical.choose_spec
      (exists_mem_eq_sup_nat (earlierRots proc e) hne InternalPopRot.stepIdx)
  obtain ⟨hmem_ear, hstep_sup⟩ := hmem_eq
  obtain ⟨hrInt, hx_eq, hstep_lt⟩ := Finset.mem_filter.mp hmem_ear
  refine ⟨hmem_ear, hrInt, hx_eq, hstep_lt, hstep_sup, ?_⟩
  intro e' he' he'_step
  obtain ⟨he'_rInt, he'_x, _⟩ := Finset.mem_filter.mp he'
  exact rInt_ext_step_x proc he'_rInt hrInt (he'_step.trans hstep_sup.symm) (he'_x.trans hx_eq.symm)

private theorem prevRot_inj {P : ℕ} (proc : FoldedPopProcess P) {e₁ e₂ : InternalPopRot}
    (h1 : e₁ ∈ proc.rInt) (h2 : e₂ ∈ proc.rInt)
    (hne1 : (earlierRots proc e₁).Nonempty) (hne2 : (earlierRots proc e₂).Nonempty)
    (heq : prevRot proc e₁ = prevRot proc e₂) : e₁ = e₂ := by
  obtain ⟨_, _, hx1, hlt1, hsup1, _⟩ := prevRot_spec proc hne1
  obtain ⟨_, _, hx2, hlt2, hsup2, _⟩ := prevRot_spec proc hne2
  have hx12 : e₁.x = e₂.x := by rw [← hx1, heq, hx2]
  rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with h12 | h12_eq | h21
  · have he1_in : e₁ ∈ earlierRots proc e₂ :=
      Finset.mem_filter.mpr ⟨h1, hx12, h12⟩
    have hle : e₁.stepIdx ≤ prevRotIdx proc e₂ :=
      Finset.le_sup (f := InternalPopRot.stepIdx) he1_in
    have hp_eq : (prevRot proc e₁).stepIdx = (prevRot proc e₂).stepIdx := by rw [heq]
    omega
  · exact rInt_ext_step_x proc h1 h2 h12_eq hx12
  · have he2_in : e₂ ∈ earlierRots proc e₁ :=
      Finset.mem_filter.mpr ⟨h2, hx12.symm, h21⟩
    have hle : e₂.stepIdx ≤ prevRotIdx proc e₁ :=
      Finset.le_sup (f := InternalPopRot.stepIdx) he2_in
    have hp_eq : (prevRot proc e₁).stepIdx = (prevRot proc e₂).stepIdx := by rw [heq]
    omega

private theorem card_filter_range_le_length_filter {α : Type} (p : α → Bool) :
    ∀ (xs : List α),
      ((Finset.range xs.length).filter (fun i => (xs[i]?).any p = true)).card ≤
        (xs.filter p).length
  | [] => by simp
  | x :: rest => by
    set S := (Finset.range rest.length).filter (fun j => (rest[j]?).any p = true)
    set S_shift := S.image (· + 1)
    have hshift_card : S_shift.card = S.card :=
      Finset.card_image_of_injOn (fun a _ b _ hab => by omega)
    have ih := card_filter_range_le_length_filter p rest
    cases hpx : p x
    · have hsub : (Finset.range (x :: rest).length).filter
          (fun i => ((x :: rest)[i]?).any p = true) ⊆ S_shift := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range, List.length_cons] at hi
        cases i with
        | zero => simp [hpx] at hi
        | succ j =>
          exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by omega), hi.2⟩, rfl⟩
      calc _ ≤ S_shift.card := Finset.card_le_card hsub
        _ = S.card := hshift_card
        _ ≤ (rest.filter p).length := ih
        _ = ((x :: rest).filter p).length := by simp [hpx]
    · have hsub : (Finset.range (x :: rest).length).filter
          (fun i => ((x :: rest)[i]?).any p = true) ⊆ insert 0 S_shift := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range, List.length_cons] at hi
        cases i with
        | zero => exact Finset.mem_insert_self 0 S_shift
        | succ j =>
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by omega), hi.2⟩, rfl⟩)
      calc _ ≤ (insert 0 S_shift).card := Finset.card_le_card hsub
        _ ≤ S_shift.card + 1 := Finset.card_insert_le 0 S_shift
        _ = S.card + 1 := by rw [hshift_card]
        _ ≤ (rest.filter p).length + 1 := Nat.add_le_add_right ih 1
        _ = ((x :: rest).filter p).length := by simp [hpx]

private theorem length_filter_le_of_imp {α : Type} (p q : α → Bool)
    (hpq : ∀ a, p a = true → q a = true) :
    ∀ (xs : List α), (xs.filter p).length ≤ (xs.filter q).length
  | [] => le_rfl
  | x :: rest => by
    have ih := length_filter_le_of_imp p q hpq rest
    cases hpx : p x
    · cases hqx : q x <;> simp [hpx, hqx] <;> omega
    · have hqx : q x = true := hpq x hpx
      simp [hpx, hqx]
      omega

private theorem mBase_card_bounds {P : ℕ} (hP : 1 ≤ P) (proc : FoldedPopProcess P) :
    proc.mBase ⊆ proc.rInt ∧
    proc.mBase.card ≤ 2 * P + proc.kRot ∧
    2 * P + proc.kRot < 4 * P := by
  have hsub_rInt : proc.mBase ⊆ proc.rInt := Finset.filter_subset _ _
  have hkrot_lt : proc.kRot < 2 * P := by
    rcases proc.hKLBound with ⟨rfl, _⟩ | ⟨_, hkl⟩
    · omega
    · unfold FoldedPopProcess.kRot
      refine lt_of_le_of_lt ?_ hkl
      apply length_filter_le_of_imp
      intro a ha
      cases a <;> simp at ha ⊢
  set M1 := proc.rInt.filter (fun e => earlierRots proc e = ∅)
  set M2 := proc.rInt.filter (fun e =>
    (earlierRots proc e).Nonempty ∧ (prevRot proc e).j = (prevRot proc e).h)
  set M3 := proc.rInt.filter (fun e =>
    (earlierRots proc e).Nonempty ∧
      ∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
        (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true)
  have hmBase_cover : proc.mBase ⊆ M1 ∪ M2 ∪ M3 := by
    intro e he
    obtain ⟨he_rInt, hcond⟩ := Finset.mem_filter.mp he
    change earlierRots proc e = ∅ ∨
      ((∃ ePrev ∈ earlierRots proc e, ePrev.stepIdx = prevRotIdx proc e ∧ ePrev.j = ePrev.h) ∨
        (∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
          (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true)) at hcond
    rcases (earlierRots proc e).eq_empty_or_nonempty with hemp | hne
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he_rInt, hemp⟩))
    · rcases hcond with hemp | ⟨ePrev, hePrev, hstep_eq, hjh⟩ | hrot
      · exact absurd hemp hne.ne_empty
      · have hePrev_eq := (prevRot_spec proc hne).2.2.2.2.2 ePrev hePrev hstep_eq
        subst hePrev_eq
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨he_rInt, hne, hjh⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he_rInt, hne, hrot⟩)
  have hM1_card : M1.card ≤ P := by
    have hinj : Set.InjOn (fun e : InternalPopRot => e.x - 1) (M1 : Set InternalPopRot) := by
      intro e₁ he1 e₂ he2 hfx
      simp only [Finset.mem_coe, M1, Finset.mem_filter] at he1 he2
      have hp1 := rInt_props proc he1.1
      have hp2 := rInt_props proc he2.1
      have hx_eq : e₁.x = e₂.x := by dsimp only at hfx; omega
      rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with h12 | h12_eq | h21
      · have : e₁ ∈ earlierRots proc e₂ := Finset.mem_filter.mpr ⟨he1.1, hx_eq, h12⟩
        rw [he2.2] at this; exact absurd this (Finset.notMem_empty e₁)
      · exact rInt_ext_step_x proc he1.1 he2.1 h12_eq hx_eq
      · have : e₂ ∈ earlierRots proc e₁ := Finset.mem_filter.mpr ⟨he2.1, hx_eq.symm, h21⟩
        rw [he1.2] at this; exact absurd this (Finset.notMem_empty e₂)
    have hsub : M1.image (fun e : InternalPopRot => e.x - 1) ⊆ Finset.range P := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨e, he, rfl⟩
      have hp := rInt_props proc (Finset.mem_filter.mp he).1
      exact Finset.mem_range.mpr (by omega)
    calc M1.card = (M1.image (fun e => e.x - 1)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range P).card := Finset.card_le_card hsub
      _ = P := Finset.card_range P
  have hM2_card : M2.card ≤ P := by
    have hinj : Set.InjOn (fun e : InternalPopRot => (prevRot proc e).s - 1)
        (M2 : Set InternalPopRot) := by
      intro e₁ he1 e₂ he2 hfs
      simp only [Finset.mem_coe, M2, Finset.mem_filter] at he1 he2
      obtain ⟨hr1, hne1, hjh1⟩ := he1
      obtain ⟨hr2, hne2, hjh2⟩ := he2
      have hp1_r := (prevRot_spec proc hne1).2.1
      have hp2_r := (prevRot_spec proc hne2).2.1
      have hpr1 := rInt_props proc hp1_r
      have hpr2 := rInt_props proc hp2_r
      have hs_eq : (prevRot proc e₁).s = (prevRot proc e₂).s := by dsimp only at hfs; omega
      have hstep_eq : (prevRot proc e₁).stepIdx = (prevRot proc e₂).stepIdx := by
        rw [hpr1.2.2.2.2.2.2.1, hpr2.2.2.2.2.2.2.1, hs_eq]
      have hh_eq := (rInt_same_step_h proc hp1_r hp2_r hstep_eq).1
      have hj_eq : (prevRot proc e₁).j = (prevRot proc e₂).j := by omega
      have hprev_eq := rInt_ext_step_j proc hp1_r hp2_r hstep_eq hj_eq
      exact prevRot_inj proc hr1 hr2 hne1 hne2 hprev_eq
    have hsub : M2.image (fun e => (prevRot proc e).s - 1) ⊆ Finset.range P := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨e, he, rfl⟩
      obtain ⟨_, hne, _⟩ := Finset.mem_filter.mp he
      have hp := rInt_props proc (prevRot_spec proc hne).2.1
      exact Finset.mem_range.mpr (by omega)
    calc M2.card = (M2.image (fun e => (prevRot proc e).s - 1)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range P).card := Finset.card_le_card hsub
      _ = P := Finset.card_range P
  have hM3_card : M3.card ≤ proc.kRot := by
    let isUR : FoldedOp → Bool := fun | .upperRot _ _ => true | _ => false
    let Trot := (Finset.range proc.steps.length).filter (fun τ => (proc.steps[τ]?).any isUR = true)
    let pickTau : InternalPopRot → ℕ := fun e =>
      if h : ∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
          (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true then
        Classical.choose h
      else 0
    have hpick_spec : ∀ e ∈ M3,
        prevRotIdx proc e < pickTau e ∧ pickTau e < e.stepIdx ∧
        (proc.steps[pickTau e]?).any (FoldedOp.isUpperRotOf e.x) = true := by
      intro e he
      obtain ⟨_, _, hex⟩ := Finset.mem_filter.mp he
      have hch : pickTau e ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx ∧
          (proc.steps[pickTau e]?).any (FoldedOp.isUpperRotOf e.x) = true := by
        simp only [pickTau, hex, ↓reduceDIte]
        exact Classical.choose_spec hex
      obtain ⟨hioo, hany⟩ := hch
      rw [Finset.mem_Ioo] at hioo
      exact ⟨hioo.1, hioo.2, hany⟩
    have hinj : Set.InjOn pickTau (M3 : Set InternalPopRot) := by
      intro e₁ he1 e₂ he2 htau
      simp only [Finset.mem_coe] at he1 he2
      obtain ⟨hr1, _, _⟩ := Finset.mem_filter.mp he1
      obtain ⟨hr2, _, _⟩ := Finset.mem_filter.mp he2
      obtain ⟨hlo1, hhi1, hany1⟩ := hpick_spec e₁ he1
      obtain ⟨hlo2, hhi2, hany2⟩ := hpick_spec e₂ he2
      rw [htau] at hany1
      have hx_eq : e₁.x = e₂.x := by
        cases hopt : proc.steps[pickTau e₂]? with
        | none => simp [hopt] at hany1
        | some op =>
          rw [hopt] at hany1 hany2
          cases op with
          | push _ => simp [FoldedOp.isUpperRotOf] at hany1
          | shift => simp [FoldedOp.isUpperRotOf] at hany1
          | pop _ => simp [FoldedOp.isUpperRotOf] at hany1
          | upperRot u v =>
            simp only [Option.any_some, FoldedOp.isUpperRotOf, beq_iff_eq] at hany1 hany2
            omega
      rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with h12 | h12_eq | h21
      · have he1_in : e₁ ∈ earlierRots proc e₂ := Finset.mem_filter.mpr ⟨hr1, hx_eq, h12⟩
        have hle := Finset.le_sup (f := InternalPopRot.stepIdx) he1_in
        change e₁.stepIdx ≤ prevRotIdx proc e₂ at hle
        omega
      · exact rInt_ext_step_x proc hr1 hr2 h12_eq hx_eq
      · have he2_in : e₂ ∈ earlierRots proc e₁ := Finset.mem_filter.mpr ⟨hr2, hx_eq.symm, h21⟩
        have hle := Finset.le_sup (f := InternalPopRot.stepIdx) he2_in
        change e₂.stepIdx ≤ prevRotIdx proc e₁ at hle
        omega
    have hsub : M3.image pickTau ⊆ Trot := by
      intro τ hτ
      rcases Finset.mem_image.mp hτ with ⟨e, he, rfl⟩
      obtain ⟨hr, _, _⟩ := Finset.mem_filter.mp he
      obtain ⟨_, hhi, hany⟩ := hpick_spec e he
      have hlen := (rInt_props proc hr).1
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
      cases hopt : proc.steps[pickTau e]? with
      | none => simp [hopt] at hany
      | some op =>
        rw [hopt] at hany
        cases op with
        | push _ => simp [FoldedOp.isUpperRotOf] at hany
        | shift => simp [FoldedOp.isUpperRotOf] at hany
        | pop _ => simp [FoldedOp.isUpperRotOf] at hany
        | upperRot _ _ => simp [isUR]
    have hTrot_le : Trot.card ≤ proc.kRot := by
      have hfn : isUR = (fun | .upperRot _ _ => true | _ => false) := by
        funext op; cases op <;> rfl
      calc Trot.card ≤ (proc.steps.filter isUR).length :=
            card_filter_range_le_length_filter isUR proc.steps
        _ = proc.kRot := by rw [hfn]; rfl
    calc M3.card = (M3.image pickTau).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Trot.card := Finset.card_le_card hsub
      _ ≤ proc.kRot := hTrot_le
  have htotal : proc.mBase.card ≤ 2 * P + proc.kRot := by
    calc proc.mBase.card ≤ (M1 ∪ M2 ∪ M3).card := Finset.card_le_card hmBase_cover
      _ ≤ (M1 ∪ M2).card + M3.card := Finset.card_union_le (M1 ∪ M2) M3
      _ ≤ M1.card + M2.card + M3.card := by
          have := Finset.card_union_le M1 M2; omega
      _ ≤ 2 * P + proc.kRot := by omega
  exact ⟨hsub_rInt, htotal, by omega⟩

private noncomputable def eLMap {P : ℕ} (proc : FoldedPopProcess P) (e : InternalPopRot) :
    InternalPopRot :=
  prevRot proc e

private noncomputable def eRMap {P : ℕ} (proc : FoldedPopProcess P) (e : InternalPopRot) :
    InternalPopRot :=
  match proc.nextCascadeRot? (prevRot proc e) with
  | some r => r
  | none => e

private theorem nonBase_parent_const {P : ℕ} (proc : FoldedPopProcess P) {e : InternalPopRot}
    (he_rInt : e ∈ proc.rInt) (hne : (earlierRots proc e).Nonempty)
    (hno_ur : ¬ ∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
      (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true) :
    (prevRot proc e).z = e.y := by
  obtain ⟨_, hp_rInt, hpx, hp_lt_e, hp_sup, _⟩ := prevRot_spec proc hne
  have hpe := rInt_props proc he_rInt
  have hpp := rInt_props proc hp_rInt
  set p := prevRot proc e
  have hx_lo : 1 ≤ e.x := by omega
  have hx_hi : e.x ≤ P := by omega
  obtain ⟨_, hpop_ge⟩ := (mem_treeAt_iff proc hx_lo hx_hi e.stepIdx (by omega)).mp
    hpe.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hins_lt, _⟩ := (mem_treeAt_iff proc hx_lo hx_hi (p.stepIdx + 1) (by omega)).mp
    (hpx ▸ hpp.2.2.2.2.2.2.2.2.2.2.1)
  have hconst : ∀ τ : ℕ, p.stepIdx + 1 ≤ τ → τ ≤ e.stepIdx →
      foldedParent P (proc.treeAt τ) e.x = p.z := by
    intro τ hlo hhi
    induction τ with
    | zero => omega
    | succ m ih =>
      by_cases hbase : m = p.stepIdx
      · subst hbase
        simpa [hpx] using hpp.2.2.2.2.2.2.2.2.2.2.2.2
      · have hm_ge : p.stepIdx + 1 ≤ m := by omega
        have hm_lt_e : m < e.stepIdx := by omega
        have hm_lt_len : m < proc.steps.length := by omega
        have ih_m := ih hm_ge (by omega)
        have hxm : e.x ∈ proc.treeAt m :=
          (mem_treeAt_iff proc hx_lo hx_hi m (by omega)).mpr ⟨by omega, by omega⟩
        have hxm1 : e.x ∈ proc.treeAt (m + 1) :=
          (mem_treeAt_iff proc hx_lo hx_hi (m + 1) (by omega)).mpr ⟨by omega, by omega⟩
        obtain ⟨hval, hstep⟩ := proc_step_valid proc hm_lt_len
        have hinv := proc_stateAt_inv proc m (by omega)
        have hpres := foldedOp_step_preserves hinv hval
        have htree_eq : proc.treeAt (m + 1) = ((proc.steps[m]'hm_lt_len).step (proc.stateAt m)).1 := by
          simp [FoldedPopProcess.treeAt, hstep]
        have hstep_eq_fp : foldedParent P (proc.treeAt (m + 1)) e.x =
            foldedParent P (proc.treeAt m) e.x := by
          rw [htree_eq]
          cases hop : proc.steps[m]'hm_lt_len with
          | push w =>
            rw [hop] at hpres
            exact hpres.2.2.2.2 e.x hxm
          | shift =>
            rw [hop] at hpres
            rw [hpres.2.2]
            rfl
          | upperRot u v =>
            rw [hop] at hpres
            have hxu : e.x ≠ u := by
              intro hxu_eq
              apply hno_ur
              refine ⟨m, Finset.mem_Ioo.mpr ⟨by omega, hm_lt_e⟩, ?_⟩
              rw [List.getElem?_eq_getElem hm_lt_len, hop]
              simp [FoldedOp.isUpperRotOf, hxu_eq]
            exact hpres.2.2.2.2.2 e.x hxu
          | pop s =>
            rw [hop] at hpres
            have hxm1' : e.x ∈ ((FoldedOp.pop s).step (proc.stateAt m)).1 := by
              simpa [htree_eq, hop] using hxm1
            refine hpres.2.2.2.2.2 m e.x hxm1' ?_
            intro e' he'_at hxe'
            have he'_rInt : e' ∈ proc.rInt ∧ e'.stepIdx = m := by
              rw [mem_rInt_stepIdx_iff proc hm_lt_len e', hop]
              exact he'_at
            have he'_ear : e' ∈ earlierRots proc e :=
              Finset.mem_filter.mpr ⟨he'_rInt.1, hxe'.symm, by omega⟩
            have hle_sup := Finset.le_sup (f := InternalPopRot.stepIdx) he'_ear
            change e'.stepIdx ≤ prevRotIdx proc e at hle_sup
            omega
        rw [hstep_eq_fp, ih_m]
  have h_at_e := hconst e.stepIdx (by omega) le_rfl
  rw [hpe.2.2.2.2.2.2.2.2.2.2.2.1] at h_at_e
  exact h_at_e.symm

/-! ## 7. Main Theorem: Lemma 3.6 (`lem_3_6_folded_laws`) -/

/-- **Lemma 3.6 (Postorder, Spine Intervals, and Parent Monotonicity in `H̃`)**.
Let `H̃` be a `FoldedPopProcess` of size `P ≥ 1`:
(1) `postorder(L''_τ)` on `V_τ` equals `in-order(H̃_τ)`, `v < π_τ(v)`, right rotations `[x, y]`
update only `π(x) : y ↦ z` while `π_τ(v)` is non-decreasing and `L''_τ`-ancestors shrink;
(2) `LS(H̃_τ)` partitions `V_τ` into `[u_i, u_{i+1} - 1]`, and after `e = (x, y, z) ∈ ℛ_int(H̃)`
at `POP(s)`, zero keys `> x` are inserted and `(x, z) ∩ LS(H̃_τ) = ∅` throughout `[s⁺, x⁻]`;
(3) `|ℳ_base| ≤ 2 P + K_rot < 4 P`, and on `ℛ_int(H̃) \ ℳ_base` the backward adjacent pair
`e_L = (x, w_1, y), e_R = e_L⁺ = (y, w_2, z')` satisfies global injectivity of both
`e ↦ e_L` and `e ↦ e_R`. -/
theorem lem_3_6_folded_laws (P : ℕ) (hP : 1 ≤ P) (proc : FoldedPopProcess P) :
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
         e.y < (eR e).y ∧ (eR e).y < (eR e).z) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · -- Part (1a)
    intro τ hτ
    obtain ⟨hbst, _, hkeys, _⟩ := proc_stateAt_inv proc τ hτ
    refine ⟨hbst, ?_, postorderL2OnV_eq_toKeyList _, ?_⟩
    · intro x hx
      rw [mem_keyFinset_iff] at hx
      exact Finset.mem_Icc.mpr (hkeys x hx)
    · intro v hv
      exact (foldedParent_mem_props hbst hkeys hv).1
  · -- Part (1b)
    intro τ u v hτ hop_opt
    rw [List.getElem?_eq_getElem hτ, Option.some.injEq] at hop_opt
    obtain ⟨hval, hstep⟩ := proc_step_valid proc hτ
    have hinv := proc_stateAt_inv proc τ (by omega)
    have hpres := foldedOp_step_preserves hinv hval
    have htree_eq : proc.treeAt (τ + 1) = ((proc.steps[τ]'hτ).step (proc.stateAt τ)).1 := by
      simp [FoldedPopProcess.treeAt, hstep]
    rw [htree_eq]
    rw [hop_opt] at hpres ⊢
    exact ⟨hpres.2.2.2.2.1, fun w _ hwu => hpres.2.2.2.2.2 w hwu⟩
  · -- Part (1c)
    intro s hs1 hsP
    dsimp only
    obtain ⟨hlt, hop_s, _⟩ := popStepIdx_spec proc hs1 hsP
    obtain ⟨hval, hstep⟩ := proc_step_valid proc hlt
    have hinv := proc_stateAt_inv proc (proc.popStepIdx s) (by omega)
    have hpres := foldedOp_step_preserves hinv hval
    have htree_eq : proc.treeAt (proc.popStepIdx s + 1) =
        ((proc.steps[proc.popStepIdx s]'hlt).step (proc.stateAt (proc.popStepIdx s))).1 := by
      simp [FoldedPopProcess.treeAt, hstep]
    rw [htree_eq]
    rw [hop_s] at hpres ⊢
    refine ⟨?_, ?_⟩
    · intro e he_rInt he_step
      have he_at := (mem_rInt_stepIdx_iff proc hlt e).mp ⟨he_rInt, he_step⟩
      rw [hop_s] at he_at
      exact hpres.2.2.2.2.1 (proc.popStepIdx s) e he_at
    · intro w hw hno_rot
      refine hpres.2.2.2.2.2 (proc.popStepIdx s) w hw ?_
      intro e he_at
      have he_pair : e ∈ proc.rInt ∧ e.stepIdx = proc.popStepIdx s := by
        rw [mem_rInt_stepIdx_iff proc hlt e, hop_s]
        exact he_at
      exact hno_rot e he_pair.1 he_pair.2
  · -- Part (1d)
    intro τ₁ τ₂ v h12 h2 hv1 hv2
    exact multi_step_parent_anc proc h12 h2 hv1 hv2
  · -- Part (2a)
    intro τ hτ _
    dsimp only
    intro idx
    obtain ⟨hbst, _, hkeys, _⟩ := proc_stateAt_inv proc τ hτ
    exact leftSpine_interval_partition (bound := P + 1) hbst
      (fun x hx => by have := (hkeys x hx).2; omega) idx
  · -- Part (2b)
    intro e he
    have hp := rInt_props proc he
    have hx_lo : 1 ≤ e.x := by omega
    have hx_hi : e.x ≤ P := by omega
    obtain ⟨hlt_popx, _, _⟩ := popStepIdx_spec proc hx_lo hx_hi
    obtain ⟨hins_lt, _⟩ := (mem_treeAt_iff proc hx_lo hx_hi (e.stepIdx + 1) (by omega)).mp
      hp.2.2.2.2.2.2.2.2.2.2.1
    refine ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, ?_, ?_⟩
    · intro τ' hτ'_mem w hpush_opt
      rw [Finset.mem_Ico] at hτ'_mem
      have hτ'_lt : τ' < proc.steps.length := by omega
      rw [List.getElem?_eq_getElem hτ'_lt, Option.some.injEq] at hpush_opt
      obtain ⟨hval, _⟩ := proc_step_valid proc hτ'_lt
      rw [hpush_opt] at hval
      have hx_in_τ' : e.x ∈ proc.treeAt τ' :=
        (mem_treeAt_iff proc hx_lo hx_hi τ' (by omega)).mpr ⟨by omega, by omega⟩
      exact hval.2.2.1 e.x hx_in_τ'
    · intro τ hτ_mem w hw_ls ⟨hxw, hwz⟩
      rw [Finset.mem_Icc] at hτ_mem
      have hτ_le : τ ≤ proc.steps.length := by omega
      have hx_in_τ : e.x ∈ proc.treeAt τ :=
        (mem_treeAt_iff proc hx_lo hx_hi τ hτ_le).mpr ⟨by omega, hτ_mem.2⟩
      have hmono := (multi_step_parent_anc proc hτ_mem.1 hτ_le
        hp.2.2.2.2.2.2.2.2.2.2.1 hx_in_τ).1
      rw [hp.2.2.2.2.2.2.2.2.2.2.2.2] at hmono
      obtain ⟨hbst_τ, _, _, _⟩ := proc_stateAt_inv proc τ hτ_le
      have hx_ne_top : e.x ≠ P + 1 := by omega
      have hfp_le_w : foldedParent P (proc.treeAt τ) e.x ≤ w := by
        simp only [foldedParent, hx_ne_top, ↓reduceIte]
        exact foldedParentAux_le_of_mem_leftSpine hbst_τ hx_in_τ hxw (Or.inl hw_ls)
      omega
  · -- Part (3)
    obtain ⟨hmb_sub, hmb_card, h4P⟩ := mBase_card_bounds hP proc
    refine ⟨hmb_sub, hmb_card, h4P, eLMap proc, eRMap proc, ?_, ?_, ?_⟩
    · -- Helper unpacker for `e ∈ proc.rInt \ proc.mBase`
      have h_unpack : ∀ e ∈ proc.rInt \ proc.mBase,
          e ∈ proc.rInt ∧ (earlierRots proc e).Nonempty ∧
          (prevRot proc e).j < (prevRot proc e).h ∧
          ¬ (∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
              (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true) := by
        intro e he
        obtain ⟨he_rInt, he_not_base⟩ := Finset.mem_sdiff.mp he
        have hnot_cond : ¬ (earlierRots proc e = ∅ ∨
            ((∃ ePrev ∈ earlierRots proc e, ePrev.stepIdx = prevRotIdx proc e ∧ ePrev.j = ePrev.h) ∨
              (∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
                (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true))) := by
          intro hc
          exact he_not_base (Finset.mem_filter.mpr ⟨he_rInt, hc⟩)
        rcases (earlierRots proc e).eq_empty_or_nonempty with hemp | hne
        · exact absurd (Or.inl hemp) hnot_cond
        · obtain ⟨hp_ear, hp_rInt, _, _, hp_sup, _⟩ := prevRot_spec proc hne
          have hp_props := rInt_props proc hp_rInt
          have hj_ne_h : (prevRot proc e).j ≠ (prevRot proc e).h := by
            intro hjh
            exact hnot_cond (Or.inr (Or.inl ⟨prevRot proc e, hp_ear, hp_sup, hjh⟩))
          have hno_ur : ¬ (∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
              (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true) :=
            fun hur => hnot_cond (Or.inr (Or.inr hur))
          exact ⟨he_rInt, hne, by omega, hno_ur⟩
      intro e₁ he1 e₂ he2 heq
      obtain ⟨hr1, hne1, _, _⟩ := h_unpack e₁ (Finset.mem_sdiff.mpr ⟨he1.1, he1.2⟩)
      obtain ⟨hr2, hne2, _, _⟩ := h_unpack e₂ (Finset.mem_sdiff.mpr ⟨he2.1, he2.2⟩)
      exact prevRot_inj proc hr1 hr2 hne1 hne2 heq
    · -- `Set.InjOn eR`
      have h_unpack : ∀ e ∈ proc.rInt \ proc.mBase,
          e ∈ proc.rInt ∧ (earlierRots proc e).Nonempty ∧
          (prevRot proc e).j < (prevRot proc e).h := by
        intro e he
        obtain ⟨he_rInt, he_not_base⟩ := Finset.mem_sdiff.mp he
        have hnot_cond : ¬ (earlierRots proc e = ∅ ∨
            ((∃ ePrev ∈ earlierRots proc e, ePrev.stepIdx = prevRotIdx proc e ∧ ePrev.j = ePrev.h) ∨
              (∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
                (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true))) :=
          fun hc => he_not_base (Finset.mem_filter.mpr ⟨he_rInt, hc⟩)
        rcases (earlierRots proc e).eq_empty_or_nonempty with hemp | hne
        · exact absurd (Or.inl hemp) hnot_cond
        · obtain ⟨hp_ear, hp_rInt, _, _, hp_sup, _⟩ := prevRot_spec proc hne
          have hp_props := rInt_props proc hp_rInt
          have hj_ne_h : (prevRot proc e).j ≠ (prevRot proc e).h :=
            fun hjh => hnot_cond (Or.inr (Or.inl ⟨prevRot proc e, hp_ear, hp_sup, hjh⟩))
          exact ⟨he_rInt, hne, by omega⟩
      intro e₁ he1 e₂ he2 heq
      obtain ⟨hr1, hne1, hjlt1⟩ := h_unpack e₁ (Finset.mem_sdiff.mpr ⟨he1.1, he1.2⟩)
      obtain ⟨hr2, hne2, hjlt2⟩ := h_unpack e₂ (Finset.mem_sdiff.mpr ⟨he2.1, he2.2⟩)
      have hp1_r := (prevRot_spec proc hne1).2.1
      have hp2_r := (prevRot_spec proc hne2).2.1
      obtain ⟨r₁, _, hnext1, _⟩ := rInt_nextCascadeRot_of_lt proc hp1_r hjlt1
      obtain ⟨r₂, _, hnext2, _⟩ := rInt_nextCascadeRot_of_lt proc hp2_r hjlt2
      have heR1 : eRMap proc e₁ = r₁ := by simp [eRMap, hnext1]
      have heR2 : eRMap proc e₂ = r₂ := by simp [eRMap, hnext2]
      have hr12 : r₁ = r₂ := by rw [← heR1, heq, heR2]
      subst hr12
      have hprev_eq := rInt_inj_of_nextCascadeRot_eq proc hp1_r hp2_r hnext1 hnext2
      exact prevRot_inj proc hr1 hr2 hne1 hne2 hprev_eq
    · -- Pointwise properties on `proc.rInt \ proc.mBase`
      intro e he
      obtain ⟨he_rInt, he_not_base⟩ := Finset.mem_sdiff.mp he
      have hnot_cond : ¬ (earlierRots proc e = ∅ ∨
          ((∃ ePrev ∈ earlierRots proc e, ePrev.stepIdx = prevRotIdx proc e ∧ ePrev.j = ePrev.h) ∨
            (∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
              (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true))) :=
        fun hc => he_not_base (Finset.mem_filter.mpr ⟨he_rInt, hc⟩)
      rcases (earlierRots proc e).eq_empty_or_nonempty with hemp | hne
      · exact absurd (Or.inl hemp) hnot_cond
      · obtain ⟨hp_ear, hp_rInt, hpx, hp_lt_e, hp_sup, _⟩ := prevRot_spec proc hne
        have hp_props := rInt_props proc hp_rInt
        have hj_ne_h : (prevRot proc e).j ≠ (prevRot proc e).h :=
          fun hjh => hnot_cond (Or.inr (Or.inl ⟨prevRot proc e, hp_ear, hp_sup, hjh⟩))
        have hj_lt_h : (prevRot proc e).j < (prevRot proc e).h := by omega
        have hno_ur : ¬ (∃ τ ∈ Finset.Ioo (prevRotIdx proc e) e.stepIdx,
            (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true) :=
          fun hur => hnot_cond (Or.inr (Or.inr hur))
        have hpz_eq_ey : (prevRot proc e).z = e.y :=
          nonBase_parent_const proc he_rInt hne hno_ur
        obtain ⟨r, hr_rInt, hnext, _, hrs, _, hrx, hry, hrz⟩ :=
          rInt_nextCascadeRot_of_lt proc hp_rInt hj_lt_h
        have heL_eq : eLMap proc e = prevRot proc e := rfl
        have heR_eq : eRMap proc e = r := by simp [eRMap, hnext]
        rw [heL_eq, heR_eq]
        have hps_lt_es : (prevRot proc e).s < e.s :=
          (rInt_stepIdx_lt_iff_s_lt proc hp_rInt he_rInt).mp hp_lt_e
        refine ⟨hp_rInt, hr_rInt, hnext, hrs.symm, hps_lt_es, ?_,
          hpx, hpz_eq_ey, hrx.trans hpz_eq_ey, ?_, ?_, ?_, ?_, hrz⟩
        · intro e' he'_rInt he'_x he'_s_lt
          have he'_step_lt : e'.stepIdx < e.stepIdx :=
            (rInt_stepIdx_lt_iff_s_lt proc he'_rInt he_rInt).mpr he'_s_lt
          have he'_ear : e' ∈ earlierRots proc e :=
            Finset.mem_filter.mpr ⟨he'_rInt, he'_x, he'_step_lt⟩
          have hle_sup := Finset.le_sup (f := InternalPopRot.stepIdx) he'_ear
          change e'.stepIdx ≤ prevRotIdx proc e at hle_sup
          rw [← hp_sup] at hle_sup
          rcases lt_or_eq_of_le hle_sup with hlt | heq_step
          · exact le_of_lt ((rInt_stepIdx_lt_iff_s_lt proc he'_rInt hp_rInt).mp hlt)
          · have he'_eq := rInt_ext_step_x proc he'_rInt hp_rInt heq_step (he'_x.trans hpx.symm)
            rw [he'_eq]
        · rw [← hpx]; exact hp_props.2.2.1
        · rw [← hpx]; exact hp_props.2.2.2.1
        · rw [← hpz_eq_ey]; exact hp_props.2.2.2.2.1
        · rw [← hpz_eq_ey]; exact hry

end Solution.FoldedLaws

