module

public import Challenge.Definitions
public import Solution.TreeFacts
public import Solution.DirectProof

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

@[expose] public section

namespace Solution.Cascades

open SplayTree

/-! ## 1. Basic BST, `keyFinset`, `subtreeAtKey`, `leftSpine`, and `rotateRightEdge` Facts -/

private theorem mem_keyFinset_iff [DecidableEq α] (t : BinaryTree α) (x : α) :
    x ∈ keyFinset t ↔ x ∈ t := by
  induction t with
  | nil => simp [keyFinset]
  | node k l r ihl ihr =>
    simp [keyFinset, BinaryTree.mem_node_iff, ihl, ihr]

private theorem bst_lt_left [LinearOrder α] {k : α} {l r : BinaryTree α}
    (h : (BinaryTree.node k l r).IsBST) {x : α} (hx : x ∈ l) : x < k := by
  obtain ⟨hlt, _, _, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp h
  exact (SplayDeque.Direct.forallTree_iff _ _).mp hlt x hx

private theorem bst_gt_right [LinearOrder α] {k : α} {l r : BinaryTree α}
    (h : (BinaryTree.node k l r).IsBST) {x : α} (hx : x ∈ r) : k < x := by
  obtain ⟨_, hgt, _, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp h
  exact (SplayDeque.Direct.forallTree_iff _ _).mp hgt x hx

private theorem bst_left [LinearOrder α] {k : α} {l r : BinaryTree α}
    (h : (BinaryTree.node k l r).IsBST) : l.IsBST :=
  ((SplayDeque.Direct.isBSTNode_iff k l r).mp h).2.2.1

private theorem bst_right [LinearOrder α] {k : α} {l r : BinaryTree α}
    (h : (BinaryTree.node k l r).IsBST) : r.IsBST :=
  ((SplayDeque.Direct.isBSTNode_iff k l r).mp h).2.2.2

private theorem card_keyFinset_eq_num_nodes [LinearOrder α] (t : BinaryTree α)
    (ht : t.IsBST) : (keyFinset t).card = t.num_nodes := by
  induction t with
  | nil => simp [keyFinset, BinaryTree.num_nodes]
  | node k l r ihl ihr =>
    have hkl : k ∉ keyFinset l := by
      intro hk
      exact lt_irrefl k (bst_lt_left ht ((mem_keyFinset_iff l k).mp hk))
    have hkr : k ∉ keyFinset r := by
      intro hk
      exact lt_irrefl k (bst_gt_right ht ((mem_keyFinset_iff r k).mp hk))
    have hdisj : Disjoint (keyFinset l) (keyFinset r) := by
      rw [Finset.disjoint_left]
      intro x hxl hxr
      exact lt_asymm
        (bst_lt_left ht ((mem_keyFinset_iff l x).mp hxl))
        (bst_gt_right ht ((mem_keyFinset_iff r x).mp hxr))
    have hku : k ∉ keyFinset l ∪ keyFinset r := by simp [hkl, hkr]
    simp only [keyFinset, Finset.card_insert_of_notMem hku,
      Finset.card_union_of_disjoint hdisj,
      ihl (bst_left ht), ihr (bst_right ht), BinaryTree.num_nodes]
    omega

private theorem subtreeAtKey_isBST [LinearOrder α] (t : BinaryTree α) (v : α)
    (ht : t.IsBST) : (subtreeAtKey t v).IsBST := by
  induction t with
  | nil => exact SplayDeque.Direct.isBSTNil
  | node k l r ihl ihr =>
    simp only [subtreeAtKey]
    split_ifs with h1 h2
    · exact ihl (bst_left ht)
    · exact ihr (bst_right ht)
    · exact ht

private theorem mem_of_mem_subtreeAtKey [LinearOrder α] (t : BinaryTree α) {v w : α}
    (hw : w ∈ subtreeAtKey t v) : w ∈ t := by
  induction t with
  | nil => simp [subtreeAtKey] at hw
  | node k l r ihl ihr =>
    simp only [subtreeAtKey] at hw
    split_ifs at hw with h1 h2
    · exact BinaryTree.mem_node_iff.mpr (Or.inr (Or.inl (ihl hw)))
    · exact BinaryTree.mem_node_iff.mpr (Or.inr (Or.inr (ihr hw)))
    · exact hw

private theorem subtreeAtKey_self_nonempty [LinearOrder α] (t : BinaryTree α) (v : α)
    (ht : t.IsBST) (hv : v ∈ t) :
    ∃ l r, subtreeAtKey t v = .node v l r := by
  induction t with
  | nil => simp at hv
  | node k l r ihl ihr =>
    rcases BinaryTree.mem_node_iff.mp hv with rfl | hvl | hvr
    · simp [subtreeAtKey]
    · have hlt := bst_lt_left ht hvl
      simp only [subtreeAtKey, hlt, ↓reduceIte]
      exact ihl (bst_left ht) hvl
    · have hgt := bst_gt_right ht hvr
      have hnlt : ¬ v < k := not_lt_of_gt hgt
      simp only [subtreeAtKey, hnlt, hgt, ↓reduceIte]
      exact ihr (bst_right ht) hvr

private theorem subtreeAtKey_trans [LinearOrder α] (t : BinaryTree α) {v w : α}
    (ht : t.IsBST) (hw : w ∈ subtreeAtKey t v) :
    subtreeAtKey t w = subtreeAtKey (subtreeAtKey t v) w := by
  induction t with
  | nil => simp [subtreeAtKey] at hw
  | node k l r ihl ihr =>
    by_cases hv1 : v < k
    · simp only [subtreeAtKey, hv1, ↓reduceIte] at hw ⊢
      have hw1 : w < k := bst_lt_left ht (mem_of_mem_subtreeAtKey l hw)
      simp only [hw1, ↓reduceIte]
      exact ihl (bst_left ht) hw
    · by_cases hv2 : k < v
      · simp only [subtreeAtKey, hv1, hv2, ↓reduceIte] at hw ⊢
        have hw2 : k < w := bst_gt_right ht (mem_of_mem_subtreeAtKey r hw)
        have hnw1 : ¬ w < k := not_lt_of_gt hw2
        simp only [hnw1, hw2, ↓reduceIte]
        exact ihr (bst_right ht) hw
      · simp only [subtreeAtKey, hv1, hv2, ↓reduceIte]

private theorem mem_of_mem_leftSpine (t : BinaryTree α) {x : α}
    (hx : x ∈ leftSpine t) : x ∈ t := by
  induction t with
  | nil => simp [leftSpine] at hx
  | node k l r ihl _ =>
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with hxl | rfl
    · exact BinaryTree.mem_node_iff.mpr (Or.inr (Or.inl (ihl hxl)))
    · exact BinaryTree.mem_node_iff.mpr (Or.inl rfl)

private theorem leftSpine_length_le_num_nodes (t : BinaryTree α) :
    (leftSpine t).length ≤ t.num_nodes := by
  induction t with
  | nil => simp [leftSpine, BinaryTree.num_nodes]
  | node k l r ihl _ =>
    simp only [leftSpine, List.length_append, List.length_singleton, BinaryTree.num_nodes]
    omega

private theorem leftSpine_pairwise_lt [LinearOrder α] (t : BinaryTree α)
    (ht : t.IsBST) : List.Pairwise (· < ·) (leftSpine t) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    rw [leftSpine, List.pairwise_append]
    refine ⟨ihl (bst_left ht), List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact bst_lt_left ht (mem_of_mem_leftSpine l ha)

private theorem leftSpine_adj_edge [LinearOrder α] (S : BinaryTree α) (hS : S.IsBST)
    (j : ℕ) (hj : j + 1 < (leftSpine S).length) :
    let x := (leftSpine S)[j]
    let y := (leftSpine S)[j + 1]
    x < y ∧ y ∈ S ∧
      ∃ A B C, subtreeAtKey S y = .node y (.node x A B) C ∧
        leftSpine A = (leftSpine S).take j := by
  induction S with
  | nil => simp [leftSpine] at hj
  | node k l r ihl _ =>
    have hlen : (leftSpine (.node k l r)).length = (leftSpine l).length + 1 := by
      simp [leftSpine]
    by_cases hjl : j + 1 < (leftSpine l).length
    · have hget_j : (leftSpine (.node k l r))[j] = (leftSpine l)[j] := by
        simp [leftSpine, List.getElem_append_left (by omega : j < (leftSpine l).length)]
      have hget_j1 : (leftSpine (.node k l r))[j + 1] = (leftSpine l)[j + 1] := by
        simp [leftSpine, List.getElem_append_left hjl]
      obtain ⟨hxy, hyl, A, B, C, hsub, htake⟩ := ihl (bst_left hS) hjl
      have hy_lt_k : (leftSpine l)[j + 1] < k := bst_lt_left hS hyl
      refine ⟨?_, ?_, A, B, C, ?_, ?_⟩
      · simpa only [hget_j, hget_j1] using hxy
      · rw [hget_j1]; exact BinaryTree.mem_node_iff.mpr (Or.inr (Or.inl hyl))
      · rw [hget_j, hget_j1]
        simp only [subtreeAtKey, hy_lt_k, ↓reduceIte]
        exact hsub
      · rw [htake]
        simp [leftSpine, List.take_append_of_le_length (by omega : j ≤ (leftSpine l).length)]
    · have hj_eq : j + 1 = (leftSpine l).length := by omega
      rcases l with _ | ⟨lx, A, B⟩
      · simp [leftSpine] at hj_eq
      · have hlen_l : (leftSpine (.node lx A B)).length = (leftSpine A).length + 1 := by
          simp [leftSpine]
        have hj_A : j = (leftSpine A).length := by omega
        have hx_eq : (leftSpine (.node k (.node lx A B) r))[j] = lx := by
          simp [leftSpine, hj_A]
        have hy_eq : (leftSpine (.node k (.node lx A B) r))[j + 1] = k := by
          simp [leftSpine, hj_A]
        have hlx_lt_k : lx < k := bst_lt_left hS (BinaryTree.mem_node_iff.mpr (Or.inl rfl))
        refine ⟨?_, ?_, A, B, r, ?_, ?_⟩
        · simp only [hx_eq, hy_eq]; exact hlx_lt_k
        · simp only [hy_eq]; exact BinaryTree.mem_node_iff.mpr (Or.inl rfl)
        · simp [hx_eq, hy_eq, subtreeAtKey]
        · simp [leftSpine, hj_A]

private theorem leftSpine_subtreeAtKey_of_mem_spine [LinearOrder α] (S : BinaryTree α)
    (hS : S.IsBST) (m : ℕ) (hm : m < (leftSpine S).length) :
    leftSpine (subtreeAtKey S ((leftSpine S)[m])) = (leftSpine S).take (m + 1) := by
  induction S with
  | nil => simp [leftSpine] at hm
  | node k l r ihl _ =>
    have hlen : (leftSpine (.node k l r)).length = (leftSpine l).length + 1 := by
      simp [leftSpine]
    by_cases hml : m < (leftSpine l).length
    · have hget : (leftSpine (.node k l r))[m] = (leftSpine l)[m] := by
        simp [leftSpine, List.getElem_append_left hml]
      have hw_lt : (leftSpine l)[m] < k :=
        bst_lt_left hS (mem_of_mem_leftSpine l (List.getElem_mem hml))
      rw [hget]
      simp only [subtreeAtKey, hw_lt, ↓reduceIte, ihl (bst_left hS) hml, leftSpine]
      rw [List.take_append_of_le_length (by omega)]
    · have hm_eq : m = (leftSpine l).length := by omega
      have hget : (leftSpine (.node k l r))[m] = k := by simp [leftSpine, hm_eq]
      rw [hget]
      simp [subtreeAtKey, leftSpine, hm_eq]

/-! ### `rotateRightEdge` preserves BST, keys, and `num_nodes` -/

private theorem rotateRightEdge_spec [LinearOrder α] (T : BinaryTree α)
    (x y : α) (hT : T.IsBST) (hxy : x < y) (hedge : IsRightRotEdge T x y) :
    (rotateRightEdge T x y).IsBST ∧
    (∀ w : α, w ∈ rotateRightEdge T x y ↔ w ∈ T) ∧
    (rotateRightEdge T x y).num_nodes = T.num_nodes := by
  rcases hedge with ⟨A, B, C, hy_mem, hsub⟩
  induction T with
  | nil => simp at hy_mem
  | node k l r ihl ihr =>
    by_cases hyk : y < k
    · simp only [subtreeAtKey, hyk, ↓reduceIte] at hsub
      have hy_l : y ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hy_mem with rfl | hyl | hyr
        · exact absurd hyk (lt_irrefl _)
        · exact hyl
        · exact absurd (lt_trans hyk (bst_gt_right hT hyr)) (lt_irrefl _)
      obtain ⟨hl', hmem_l', hn_l'⟩ := ihl (bst_left hT) hy_l hsub
      simp only [rotateRightEdge, hyk, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · refine SplayDeque.Direct.isBSTNode k _ r ?_ ?_ hl' (bst_right hT)
        · rw [SplayDeque.Direct.forallTree_iff]
          intro w hw
          exact bst_lt_left hT ((hmem_l' w).mp hw)
        · exact ((SplayDeque.Direct.isBSTNode_iff k l r).mp hT).2.1
      · intro w
        simp [BinaryTree.mem_node_iff, hmem_l']
      · simp [BinaryTree.num_nodes, hn_l']
    · by_cases hky : k < y
      · simp only [subtreeAtKey, hyk, hky, ↓reduceIte] at hsub
        have hy_r : y ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hy_mem with rfl | hyl | hyr
          · exact absurd hky (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hT hyl) hky) (lt_irrefl _)
          · exact hyr
        obtain ⟨hr', hmem_r', hn_r'⟩ := ihr (bst_right hT) hy_r hsub
        simp only [rotateRightEdge, hyk, hky, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · refine SplayDeque.Direct.isBSTNode k l _ ?_ ?_ (bst_left hT) hr'
          · exact ((SplayDeque.Direct.isBSTNode_iff k l r).mp hT).1
          · rw [SplayDeque.Direct.forallTree_iff]
            intro w hw
            exact bst_gt_right hT ((hmem_r' w).mp hw)
        · intro w
          simp [BinaryTree.mem_node_iff, hmem_r']
        · simp [BinaryTree.num_nodes, hn_r']
      · have hy_eq : y = k := le_antisymm (not_lt.mp hky) (not_lt.mp hyk)
        subst hy_eq
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l r
        simp only [rotateRightEdge, lt_irrefl, ↓reduceIte]
        have hl_bst : (BinaryTree.node x A B).IsBST := bst_left hT
        have hA_bst : A.IsBST := bst_left hl_bst
        have hB_bst : B.IsBST := bst_right hl_bst
        have hC_bst : C.IsBST := bst_right hT
        have hBC_bst : (BinaryTree.node y B C).IsBST := by
          refine SplayDeque.Direct.isBSTNode y B C ?_ ?_ hB_bst hC_bst
          · rw [SplayDeque.Direct.forallTree_iff]
            intro w hw
            exact bst_lt_left hT (BinaryTree.mem_node_iff.mpr (Or.inr (Or.inr hw)))
          · exact ((SplayDeque.Direct.isBSTNode_iff y _ C).mp hT).2.1
        refine ⟨?_, ?_, ?_⟩
        · refine SplayDeque.Direct.isBSTNode x A (.node y B C) ?_ ?_ hA_bst hBC_bst
          · exact ((SplayDeque.Direct.isBSTNode_iff x A B).mp hl_bst).1
          · rw [SplayDeque.Direct.forallTree_iff]
            intro w hw
            rcases BinaryTree.mem_node_iff.mp hw with rfl | hwB | hwC
            · exact hxy
            · exact bst_gt_right hl_bst hwB
            · exact lt_trans hxy (bst_gt_right hT hwC)
        · intro w
          simp only [BinaryTree.mem_node_iff]
          tauto
        · simp only [BinaryTree.num_nodes]
          omega

private theorem rotateRightEdge_keyFinset [LinearOrder α] (T : BinaryTree α)
    (x y : α) (hT : T.IsBST) (hxy : x < y) (hedge : IsRightRotEdge T x y) :
    keyFinset (rotateRightEdge T x y) = keyFinset T := by
  obtain ⟨_, hmem, _⟩ := rotateRightEdge_spec T x y hT hxy hedge
  ext w
  rw [mem_keyFinset_iff, mem_keyFinset_iff]
  exact hmem w

/-! ### List removal helper `removeAt` and Cascade Front-Peeling (`peel_cons`) -/

private def removeAt : List α → ℕ → List α
  | [], _ => []
  | _ :: xs, 0 => xs
  | x :: xs, i + 1 => x :: removeAt xs i

private theorem removeAt_length (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (removeAt xs i).length = xs.length - 1 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [removeAt]
    | succ i =>
      simp only [List.length_cons] at hi
      have hlen := ih i (by omega)
      simp only [removeAt, List.length_cons, hlen]
      omega

private theorem removeAt_append_left (xs ys : List α) (i : ℕ) (hi : i < xs.length) :
    removeAt (xs ++ ys) i = removeAt xs i ++ ys := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [removeAt]
    | succ i =>
      simp only [List.length_cons] at hi
      simp [removeAt, ih i (by omega)]

private theorem removeAt_append_two_last (xs : List α) (x y : α) :
    removeAt (xs ++ [x, y]) (xs.length + 1) = xs ++ [x] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have heq : (a :: xs).length + 1 = (xs.length + 1) + 1 := by simp
    rw [heq]
    simp [removeAt, ih]

private theorem removeAt_getElem_ge_eq (xs : List α) (i j : ℕ)
    (hj1 : j + 1 < xs.length) (hij : i ≤ j)
    (h : j < (removeAt xs i).length) :
    (removeAt xs i)[j] = xs[j + 1] := by
  induction xs generalizing i j with
  | nil => simp at hj1
  | cons a xs ih =>
    cases i with
    | zero => simp [removeAt]
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.length_cons] at hj1
        simp only [removeAt, List.getElem_cons_succ]
        exact ih i j (by omega) (by omega) _

private theorem leftSpine_rotateRightEdge_removeAt [LinearOrder α] (S : BinaryTree α)
    (hS : S.IsBST) (j : ℕ) (hj : j + 1 < (leftSpine S).length) :
    leftSpine (rotateRightEdge S ((leftSpine S)[j]) ((leftSpine S)[j + 1])) =
      removeAt (leftSpine S) (j + 1) := by
  induction S with
  | nil => simp [leftSpine] at hj
  | node k l r ihl _ =>
    have hlen : (leftSpine (.node k l r)).length = (leftSpine l).length + 1 := by
      simp [leftSpine]
    by_cases hjl : j + 1 < (leftSpine l).length
    · have hget_j : (leftSpine (.node k l r))[j] = (leftSpine l)[j] := by
        simp [leftSpine, List.getElem_append_left (by omega : j < (leftSpine l).length)]
      have hget_j1 : (leftSpine (.node k l r))[j + 1] = (leftSpine l)[j + 1] := by
        simp [leftSpine, List.getElem_append_left hjl]
      have hy_mem : (leftSpine l)[j + 1] ∈ l := mem_of_mem_leftSpine l (List.getElem_mem hjl)
      have hy_lt_k : (leftSpine l)[j + 1] < k := bst_lt_left hS hy_mem
      rw [hget_j, hget_j1]
      simp only [rotateRightEdge, hy_lt_k, ↓reduceIte, leftSpine]
      rw [ihl (bst_left hS) hjl, removeAt_append_left (leftSpine l) [k] (j + 1) hjl]
    · have hj_eq : j + 1 = (leftSpine l).length := by omega
      rcases l with _ | ⟨lx, A, B⟩
      · simp [leftSpine] at hj_eq
      · have hj_A : j = (leftSpine A).length := by simp [leftSpine] at hj_eq; omega
        have hx_eq : (leftSpine (.node k (.node lx A B) r))[j] = lx := by
          simp [leftSpine, hj_A]
        have hy_eq : (leftSpine (.node k (.node lx A B) r))[j + 1] = k := by
          simp [leftSpine, hj_A]
        rw [hx_eq, hy_eq]
        simp only [rotateRightEdge, lt_irrefl, ↓reduceIte, leftSpine, List.append_assoc,
          List.singleton_append, hj_A]
        exact (removeAt_append_two_last (leftSpine A) lx k).symm

private theorem subtreeAtKey_rotateRightEdge_below [LinearOrder α] (T : BinaryTree α)
    (hT : T.IsBST) {top x y : α} (htop : top ∈ T)
    (hy_sub : y ∈ subtreeAtKey T top) (hy_lt_top : y < top) :
    top ∈ rotateRightEdge T x y ∧
      subtreeAtKey (rotateRightEdge T x y) top =
        rotateRightEdge (subtreeAtKey T top) x y := by
  induction T with
  | nil => simp at htop
  | node k l r ihl ihr =>
    by_cases htk : top < k
    · simp only [subtreeAtKey, htk, ↓reduceIte] at hy_sub
      have hy_l : y ∈ l := mem_of_mem_subtreeAtKey l hy_sub
      have hyk : y < k := bst_lt_left hT hy_l
      have htop_l : top ∈ l := by
        rcases BinaryTree.mem_node_iff.mp htop with rfl | h | h
        · exact absurd htk (lt_irrefl _)
        · exact h
        · exact absurd (lt_trans htk (bst_gt_right hT h)) (lt_irrefl _)
      obtain ⟨htop', hsub'⟩ := ihl (bst_left hT) htop_l hy_sub
      simp only [rotateRightEdge, hyk, ↓reduceIte, subtreeAtKey, htk]
      exact ⟨BinaryTree.mem_node_iff.mpr (Or.inr (Or.inl htop')), hsub'⟩
    · by_cases hkt : k < top
      · simp only [subtreeAtKey, htk, hkt, ↓reduceIte] at hy_sub
        have hy_r : y ∈ r := mem_of_mem_subtreeAtKey r hy_sub
        have hky : k < y := bst_gt_right hT hy_r
        have hnyk : ¬ y < k := not_lt_of_gt hky
        have htop_r : top ∈ r := by
          rcases BinaryTree.mem_node_iff.mp htop with rfl | h | h
          · exact absurd hkt (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hT h) hkt) (lt_irrefl _)
          · exact h
        obtain ⟨htop', hsub'⟩ := ihr (bst_right hT) htop_r hy_sub
        simp only [rotateRightEdge, hnyk, hky, ↓reduceIte, subtreeAtKey, htk, hkt]
        exact ⟨BinaryTree.mem_node_iff.mpr (Or.inr (Or.inr htop')), hsub'⟩
      · have htop_eq : top = k := le_antisymm (not_lt.mp hkt) (not_lt.mp htk)
        subst htop_eq
        refine ⟨?_, ?_⟩
        · simp only [rotateRightEdge, hy_lt_top, ↓reduceIte]
          exact BinaryTree.mem_node_iff.mpr (Or.inl rfl)
        · simp only [rotateRightEdge, hy_lt_top, ↓reduceIte, subtreeAtKey, lt_irrefl]

private theorem idx_mono_of_gaps {k Δ' : ℕ} (idx : Fin k → ℕ)
    (hgaps : ∀ r₁ r₂ : Fin k, r₁.val + 1 = r₂.val →
      idx r₁ + 2 ≤ idx r₂ ∧ idx r₂ ≤ idx r₁ + Δ' + 2) :
    ∀ (r₁ r₂ : Fin k), r₁.val < r₂.val → idx r₁ + 2 ≤ idx r₂ := by
  intro r₁ r₂ hlt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, r₂.val = r₁.val + 1 + d := ⟨r₂.val - r₁.val - 1, by omega⟩
  induction d generalizing r₂ with
  | zero =>
    exact (hgaps r₁ r₂ (by omega)).1
  | succ d ih =>
    let rMid : Fin k := ⟨r₁.val + 1 + d, by omega⟩
    have hMid_val : rMid.val = r₁.val + 1 + d := rfl
    have h1 : idx r₁ + 2 ≤ idx rMid := ih rMid (by omega) hMid_val
    have h2 : idx rMid + 2 ≤ idx r₂ := (hgaps rMid r₂ (by omega)).1
    omega

private theorem cascade_head_edge [LinearOrder α] {T : BinaryTree α} (hT : T.IsBST)
    {Δ' k : ℕ} {p0 : α × α} {rest : List (α × α)}
    (hcasc : IsGappedRightCascade T Δ' k (p0 :: rest)) :
    p0.1 < p0.2 ∧ IsRightRotEdge T p0.1 p0.2 := by
  rcases hcasc with ⟨hk1, _, top, _, idx, hpairs, _⟩
  let r0 : Fin k := ⟨0, hk1⟩
  obtain ⟨hj0, hp0⟩ := hpairs r0
  simp only [r0, List.getElem?_cons_zero, Option.some.injEq] at hp0
  have hS_bst : (subtreeAtKey T top).IsBST := subtreeAtKey_isBST T top hT
  obtain ⟨hxy, hy_S, A, B, C, hsub_S, _⟩ := leftSpine_adj_edge (subtreeAtKey T top) hS_bst (idx r0) hj0
  have hp1 : p0.1 = (leftSpine (subtreeAtKey T top))[idx r0] := by rw [hp0]
  have hp2 : p0.2 = (leftSpine (subtreeAtKey T top))[idx r0 + 1] := by rw [hp0]
  rw [hp1, hp2]
  refine ⟨hxy, A, B, C, mem_of_mem_subtreeAtKey T hy_S, ?_⟩
  rw [subtreeAtKey_trans T hT hy_S]
  exact hsub_S

private theorem cascade_peel_cons [LinearOrder α] {T : BinaryTree α} (hT : T.IsBST)
    {Δ' k' : ℕ} (hk' : 1 ≤ k') {p0 : α × α} {rest : List (α × α)}
    (hcasc : IsGappedRightCascade T Δ' (k' + 1) (p0 :: rest)) :
    IsGappedRightCascade (rotateRightEdge T p0.1 p0.2) Δ' k' rest := by
  rcases hcasc with ⟨_, hlen, top, htop, idx, hpairs, hgaps⟩
  let r0 : Fin (k' + 1) := ⟨0, by omega⟩
  let r1 : Fin (k' + 1) := ⟨1, by omega⟩
  obtain ⟨hj0, hp0⟩ := hpairs r0
  obtain ⟨hj1, _⟩ := hpairs r1
  have hg01 : idx r0 + 2 ≤ idx r1 := (hgaps r0 r1 rfl).1
  simp only [r0, List.getElem?_cons_zero, Option.some.injEq] at hp0
  have hS_bst : (subtreeAtKey T top).IsBST := subtreeAtKey_isBST T top hT
  have hp1_eq : p0.1 = (leftSpine (subtreeAtKey T top))[idx r0] := by rw [hp0]
  have hp2_eq : p0.2 = (leftSpine (subtreeAtKey T top))[idx r0 + 1] := by rw [hp0]
  have hy0_S : p0.2 ∈ subtreeAtKey T top := by
    rw [hp2_eq]
    exact mem_of_mem_leftSpine (subtreeAtKey T top) (List.getElem_mem hj0)
  obtain ⟨l_top, r_top, hS_eq⟩ := subtreeAtKey_self_nonempty T top hT htop
  have hlen_pos : 0 < (leftSpine (subtreeAtKey T top)).length := by
    rw [hS_eq]; simp [leftSpine]
  have hlast : (leftSpine (subtreeAtKey T top))[(leftSpine (subtreeAtKey T top)).length - 1]'(by omega) = top := by
    simp [hS_eq, leftSpine]
  have hpairs_lt : List.Pairwise (· < ·) (leftSpine (subtreeAtKey T top)) :=
    leftSpine_pairwise_lt (subtreeAtKey T top) hS_bst
  have hy0_lt_top : p0.2 < top := by
    calc p0.2
      _ = (leftSpine (subtreeAtKey T top))[idx r0 + 1] := hp2_eq
      _ < (leftSpine (subtreeAtKey T top))[(leftSpine (subtreeAtKey T top)).length - 1]'(by omega) :=
        List.pairwise_iff_getElem.mp hpairs_lt (idx r0 + 1)
          ((leftSpine (subtreeAtKey T top)).length - 1) hj0 (by omega) (by omega)
      _ = top := hlast
  obtain ⟨htop', hsub'⟩ := subtreeAtKey_rotateRightEdge_below T hT htop hy0_S hy0_lt_top
  have hpath' : leftSpine (subtreeAtKey (rotateRightEdge T p0.1 p0.2) top) =
      removeAt (leftSpine (subtreeAtKey T top)) (idx r0 + 1) := by
    rw [hsub', hp1_eq, hp2_eq]
    exact leftSpine_rotateRightEdge_removeAt (subtreeAtKey T top) hS_bst (idx r0) hj0
  refine ⟨hk', by simp at hlen; omega, top, htop', ?_⟩
  refine ⟨fun r => idx r.succ - 1, ?_, ?_⟩
  · intro r
    obtain ⟨hjr, hpr⟩ := hpairs r.succ
    have hr_succ_val : r.succ.val = r.val + 1 := Fin.val_succ r
    have hr0_val : r0.val = 0 := rfl
    have hmono : idx r0 + 2 ≤ idx r.succ :=
      idx_mono_of_gaps idx hgaps r0 r.succ (by omega)
    have hlen' : (idx r.succ - 1) + 1 <
        (leftSpine (subtreeAtKey (rotateRightEdge T p0.1 p0.2) top)).length := by
      rw [hpath', removeAt_length (leftSpine (subtreeAtKey T top)) (idx r0 + 1) hj0]
      omega
    refine ⟨hlen', ?_⟩
    have hlt1 : idx r.succ - 1 <
        (removeAt (leftSpine (subtreeAtKey T top)) (idx r0 + 1)).length := by
      rw [removeAt_length _ _ hj0]; omega
    have hlt2 : idx r.succ <
        (removeAt (leftSpine (subtreeAtKey T top)) (idx r0 + 1)).length := by
      rw [removeAt_length _ _ hj0]; omega
    have hget1 := removeAt_getElem_ge_eq (leftSpine (subtreeAtKey T top)) (idx r0 + 1)
      (idx r.succ - 1) (by omega) (by omega) hlt1
    have hget2 := removeAt_getElem_ge_eq (leftSpine (subtreeAtKey T top)) (idx r0 + 1)
      (idx r.succ) hjr (by omega) hlt2
    have hidx1 : (idx r.succ - 1) + 1 = idx r.succ := by omega
    simp only [Fin.val_succ, List.getElem?_cons_succ] at hpr
    rw [hpr]
    congr 1
    apply Prod.ext
    · simp only [hpath']
      rw [hget1]
      congr 1; omega
    · simp only [hpath', hidx1]
      rw [hget2]
  · intro r₁ r₂ hr12
    dsimp only
    have hr0_val : r0.val = 0 := rfl
    have hr1_val : r₁.succ.val = r₁.val + 1 := Fin.val_succ r₁
    have hr2_val : r₂.succ.val = r₂.val + 1 := Fin.val_succ r₂
    have hsucc : r₁.succ.val + 1 = r₂.succ.val := by omega
    have hg := hgaps r₁.succ r₂.succ hsucc
    have hm1 := idx_mono_of_gaps idx hgaps r0 r₁.succ (by omega)
    have hm2 := idx_mono_of_gaps idx hgaps r0 r₂.succ (by omega)
    omega

/-! ## 2. Lemma 4.3 Part (1): Untruncated Left-Depth Potential `phiLeftDepth` -/

private def sumLeftDepthAux : ℕ → BinaryTree α → ℕ
  | _, .nil => 0
  | d, .node _ l r => d + sumLeftDepthAux (d + 1) l + sumLeftDepthAux d r

private theorem sumLeftDepthAux_succ (d : ℕ) (t : BinaryTree α) :
    sumLeftDepthAux (d + 1) t = sumLeftDepthAux d t + t.num_nodes := by
  induction t generalizing d with
  | nil => simp [sumLeftDepthAux, BinaryTree.num_nodes]
  | node k l r ihl ihr =>
    simp only [sumLeftDepthAux, ihl (d + 1), ihr d, BinaryTree.num_nodes]
    omega

private theorem sum_keyFinset_leftDepth_eq [LinearOrder α] (t : BinaryTree α)
    (ht : t.IsBST) (d : ℕ) :
    (keyFinset t).sum (fun v => d + leftDepth t v) = sumLeftDepthAux d t := by
  induction t generalizing d with
  | nil => simp [keyFinset, sumLeftDepthAux]
  | node k l r ihl ihr =>
    have hkl : k ∉ keyFinset l := by
      intro hk; exact lt_irrefl k (bst_lt_left ht ((mem_keyFinset_iff l k).mp hk))
    have hkr : k ∉ keyFinset r := by
      intro hk; exact lt_irrefl k (bst_gt_right ht ((mem_keyFinset_iff r k).mp hk))
    have hdisj : Disjoint (keyFinset l) (keyFinset r) := by
      rw [Finset.disjoint_left]
      intro x hxl hxr
      exact lt_asymm
        (bst_lt_left ht ((mem_keyFinset_iff l x).mp hxl))
        (bst_gt_right ht ((mem_keyFinset_iff r x).mp hxr))
    have hku : k ∉ keyFinset l ∪ keyFinset r := by simp [hkl, hkr]
    rw [keyFinset, Finset.sum_insert hku, Finset.sum_union hdisj]
    have hk0 : leftDepth (.node k l r) k = 0 := by simp [leftDepth]
    have hsum_l : (keyFinset l).sum (fun v => d + leftDepth (.node k l r) v) =
        sumLeftDepthAux (d + 1) l := by
      rw [← ihl (bst_left ht) (d + 1)]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hlt : v < k := bst_lt_left ht ((mem_keyFinset_iff l v).mp hv)
      simp only [leftDepth, hlt, ↓reduceIte]
      omega
    have hsum_r : (keyFinset r).sum (fun v => d + leftDepth (.node k l r) v) =
        sumLeftDepthAux d r := by
      rw [← ihr (bst_right ht) d]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hgt : k < v := bst_gt_right ht ((mem_keyFinset_iff r v).mp hv)
      have hnlt : ¬ v < k := not_lt_of_gt hgt
      simp only [leftDepth, hnlt, hgt, ↓reduceIte]
    simp only [hk0, Nat.add_zero, hsum_l, hsum_r, sumLeftDepthAux]
    omega

private theorem phiLeftDepth_eq_aux [LinearOrder α] (t : BinaryTree α) (ht : t.IsBST) :
    phiLeftDepth t = sumLeftDepthAux 0 t := by
  unfold phiLeftDepth
  simpa using sum_keyFinset_leftDepth_eq t ht 0

private theorem choose_two_superadd (a b : ℕ) :
    Nat.choose a 2 + a + Nat.choose b 2 ≤ Nat.choose (a + b + 1) 2 := by
  have h2 : ∀ n : ℕ, 2 * Nat.choose n 2 = n * (n - 1) := by
    intro n
    rw [Nat.choose_two_right, Nat.mul_comm, Nat.div_mul_cancel]
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact dvd_mul_of_dvd_left ⟨m, by omega⟩ _
    · exact dvd_mul_of_dvd_right ⟨m, by omega⟩ _
  have hmul : 2 * (Nat.choose a 2 + a + Nat.choose b 2) ≤ 2 * Nat.choose (a + b + 1) 2 := by
    have ha := h2 a
    have hb := h2 b
    have hab := h2 (a + b + 1)
    rcases a with _ | a' <;> rcases b with _ | b'
    · simp at ha hb hab ⊢
    · simp only [Nat.add_sub_cancel] at hb hab
      nlinarith
    · simp only [Nat.add_sub_cancel] at ha hab
      nlinarith
    · simp only [Nat.add_sub_cancel] at ha hb hab
      nlinarith
  omega

private theorem sumLeftDepthAux_le_choose (t : BinaryTree α) :
    sumLeftDepthAux 0 t ≤ Nat.choose t.num_nodes 2 := by
  induction t with
  | nil => simp [sumLeftDepthAux]
  | node k l r ihl ihr =>
    simp only [sumLeftDepthAux, Nat.zero_add, sumLeftDepthAux_succ 0 l]
    have hnode : (BinaryTree.node k l r).num_nodes = l.num_nodes + r.num_nodes + 1 := by
      simp [BinaryTree.num_nodes]; omega
    rw [hnode]
    exact le_trans (by omega) (choose_two_superadd l.num_nodes r.num_nodes)

private theorem sumLeftDepthAux_rot_drop [LinearOrder α] (T : BinaryTree α)
    (x y : α) (hT : T.IsBST) (hedge : IsRightRotEdge T x y) (d : ℕ) :
    sumLeftDepthAux d (rotateRightEdge T x y) + 1 ≤ sumLeftDepthAux d T := by
  rcases hedge with ⟨A, B, C, hy_mem, hsub⟩
  revert d
  induction T with
  | nil => simp at hy_mem
  | node k l r ihl ihr =>
    intro d
    by_cases hyk : y < k
    · simp only [subtreeAtKey, hyk, ↓reduceIte] at hsub
      have hy_l : y ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hy_mem with rfl | hyl | hyr
        · exact absurd hyk (lt_irrefl _)
        · exact hyl
        · exact absurd (lt_trans hyk (bst_gt_right hT hyr)) (lt_irrefl _)
      have hd := ihl (bst_left hT) hy_l hsub (d + 1)
      simp only [rotateRightEdge, hyk, ↓reduceIte, sumLeftDepthAux]
      omega
    · by_cases hky : k < y
      · simp only [subtreeAtKey, hyk, hky, ↓reduceIte] at hsub
        have hy_r : y ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hy_mem with rfl | hyl | hyr
          · exact absurd hky (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hT hyl) hky) (lt_irrefl _)
          · exact hyr
        have hd := ihr (bst_right hT) hy_r hsub d
        simp only [rotateRightEdge, hyk, hky, ↓reduceIte, sumLeftDepthAux]
        omega
      · have hy_eq : y = k := le_antisymm (not_lt.mp hky) (not_lt.mp hyk)
        subst hy_eq
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l r
        simp only [rotateRightEdge, lt_irrefl, ↓reduceIte, sumLeftDepthAux,
          sumLeftDepthAux_succ (d + 1) A]
        omega

private theorem lem_4_3_part1 {α : Type} [LinearOrder α] (T : BinaryTree α) (hT : T.IsBST) :
    phiLeftDepth T ≤ Nat.choose T.num_nodes 2 ∧
    (∀ x y : α, x < y → IsRightRotEdge T x y →
      phiLeftDepth (rotateRightEdge T x y) + 1 ≤ phiLeftDepth T) ∧
    (∀ (Δ' k : ℕ) (pairs : List (α × α)), IsGappedRightCascade T Δ' k pairs →
      phiLeftDepth (execRightCascadeBatch T pairs) + k ≤ phiLeftDepth T) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [phiLeftDepth_eq_aux T hT]
    exact sumLeftDepthAux_le_choose T
  · intro x y hxy hedge
    have hT' := (rotateRightEdge_spec T x y hT hxy hedge).1
    rw [phiLeftDepth_eq_aux _ hT', phiLeftDepth_eq_aux T hT]
    exact sumLeftDepthAux_rot_drop T x y hT hedge 0
  · intro Δ' k
    induction k generalizing T with
    | zero =>
      intro pairs hcasc
      exact absurd hcasc.1 (by omega)
    | succ k' ih =>
      intro pairs hcasc
      rcases pairs with _ | ⟨p0, rest⟩
      · simp [IsGappedRightCascade] at hcasc
      · obtain ⟨hxy, hedge⟩ := cascade_head_edge hT hcasc
        have hT1 : (rotateRightEdge T p0.1 p0.2).IsBST :=
          (rotateRightEdge_spec T p0.1 p0.2 hT hxy hedge).1
        have hdrop1 : phiLeftDepth (rotateRightEdge T p0.1 p0.2) + 1 ≤ phiLeftDepth T := by
          rw [phiLeftDepth_eq_aux _ hT1, phiLeftDepth_eq_aux T hT]
          exact sumLeftDepthAux_rot_drop T p0.1 p0.2 hT hedge 0
        rcases Nat.eq_zero_or_pos k' with rfl | hk'_pos
        · have hrest_nil : rest = [] := by
            have hlen := hcasc.2.1
            cases rest <;> simp at hlen ⊢
          subst hrest_nil
          simpa [execRightCascadeBatch] using hdrop1
        · have hcasc' := cascade_peel_cons hT hk'_pos hcasc
          have hdrop_rest := ih (rotateRightEdge T p0.1 p0.2) hT1 rest hcasc'
          simp only [execRightCascadeBatch, List.foldl_cons] at hdrop_rest ⊢
          omega

/-! ## 3. Lemma 4.3 Part (2): Block Truncated Left-Depth Potential `psiBlock` -/

/-! ### Interval Restriction `restrictTree _ C.toSet` on BSTs -/

private theorem restrictTree_eq_nil_of_disjoint (t : BinaryTree ℕ) (S : Set ℕ)
    (h : ∀ x ∈ t, x ∉ S) : restrictTree t S = .nil := by
  induction t with
  | nil => rfl
  | node u A B ihA _ =>
    conv_lhs => unfold restrictTree
    split_ifs with hu hb
    · exact absurd hu (h u (BinaryTree.mem_node_iff.mpr (Or.inl rfl)))
    · rcases hb with ⟨b, hbB, hbS⟩
      exact absurd hbS (h b (BinaryTree.mem_node_iff.mpr (Or.inr (Or.inr hbB))))
    · exact ihA (fun x hx => h x (BinaryTree.mem_node_iff.mpr (Or.inr (Or.inl hx))))

private theorem restrictTree_node_lt {k : ℕ} {l r : BinaryTree ℕ}
    (ht : (BinaryTree.node k l r).IsBST) (C : IntervalBlock) (hk : k < C.lo) :
    restrictTree (.node k l r) C.toSet = restrictTree r C.toSet := by
  conv_lhs => unfold restrictTree
  split_ifs with hkC hr
  · change C.lo ≤ k ∧ k ≤ C.hi at hkC
    omega
  · rfl
  · have hl_nil : restrictTree l C.toSet = .nil := by
      refine restrictTree_eq_nil_of_disjoint l C.toSet ?_
      intro x hxl hxC
      have hxk : x < k := bst_lt_left ht hxl
      change C.lo ≤ x ∧ x ≤ C.hi at hxC
      omega
    have hr_nil : restrictTree r C.toSet = .nil := by
      refine restrictTree_eq_nil_of_disjoint r C.toSet ?_
      intro x hxr hxC
      exact hr ⟨x, hxr, hxC⟩
    rw [hl_nil, hr_nil]

private theorem restrictTree_node_gt {k : ℕ} {l r : BinaryTree ℕ}
    (ht : (BinaryTree.node k l r).IsBST) (C : IntervalBlock) (hk : C.hi < k) :
    restrictTree (.node k l r) C.toSet = restrictTree l C.toSet := by
  conv_lhs => unfold restrictTree
  split_ifs with hkC hr
  · change C.lo ≤ k ∧ k ≤ C.hi at hkC
    omega
  · rcases hr with ⟨b, hbr, hbC⟩
    have hkb : k < b := bst_gt_right ht hbr
    change C.lo ≤ b ∧ b ≤ C.hi at hbC
    omega
  · rfl

private theorem restrictTree_node_mem {k : ℕ} {l r : BinaryTree ℕ}
    (C : IntervalBlock) (hk : C.lo ≤ k ∧ k ≤ C.hi) :
    restrictTree (.node k l r) C.toSet =
      .node k (restrictTree l C.toSet) (restrictTree r C.toSet) := by
  conv_lhs => unfold restrictTree
  have hkC : k ∈ C.toSet := hk
  simp only [hkC, ↓reduceIte]

private theorem mem_restrictTree_iff (t : BinaryTree ℕ) (ht : t.IsBST)
    (C : IntervalBlock) (x : ℕ) :
    x ∈ restrictTree t C.toSet ↔ x ∈ t ∧ C.lo ≤ x ∧ x ≤ C.hi := by
  induction t with
  | nil => simp [restrictTree]
  | node k l r ihl ihr =>
    by_cases hk_lt : k < C.lo
    · rw [restrictTree_node_lt ht C hk_lt, ihr (bst_right ht)]
      constructor
      · rintro ⟨hxr, hlo, hhi⟩
        exact ⟨BinaryTree.mem_node_iff.mpr (Or.inr (Or.inr hxr)), hlo, hhi⟩
      · rintro ⟨hx, hlo, hhi⟩
        rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
        · omega
        · have := bst_lt_left ht hxl; omega
        · exact ⟨hxr, hlo, hhi⟩
    · by_cases hk_gt : C.hi < k
      · rw [restrictTree_node_gt ht C hk_gt, ihl (bst_left ht)]
        constructor
        · rintro ⟨hxl, hlo, hhi⟩
          exact ⟨BinaryTree.mem_node_iff.mpr (Or.inr (Or.inl hxl)), hlo, hhi⟩
        · rintro ⟨hx, hlo, hhi⟩
          rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
          · omega
          · exact ⟨hxl, hlo, hhi⟩
          · have := bst_gt_right ht hxr; omega
      · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
        rw [restrictTree_node_mem C hk_mem]
        simp only [BinaryTree.mem_node_iff, ihl (bst_left ht), ihr (bst_right ht)]
        constructor
        · rintro (rfl | ⟨hxl, hlo, hhi⟩ | ⟨hxr, hlo, hhi⟩)
          · exact ⟨Or.inl rfl, hk_mem⟩
          · exact ⟨Or.inr (Or.inl hxl), hlo, hhi⟩
          · exact ⟨Or.inr (Or.inr hxr), hlo, hhi⟩
        · rintro ⟨rfl | hxl | hxr, hlo, hhi⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨hxl, hlo, hhi⟩)
          · exact Or.inr (Or.inr ⟨hxr, hlo, hhi⟩)

private theorem restrictTree_isBST (t : BinaryTree ℕ) (ht : t.IsBST)
    (C : IntervalBlock) : (restrictTree t C.toSet).IsBST := by
  induction t with
  | nil => exact SplayDeque.Direct.isBSTNil
  | node k l r ihl ihr =>
    by_cases hk_lt : k < C.lo
    · rw [restrictTree_node_lt ht C hk_lt]
      exact ihr (bst_right ht)
    · by_cases hk_gt : C.hi < k
      · rw [restrictTree_node_gt ht C hk_gt]
        exact ihl (bst_left ht)
      · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
        rw [restrictTree_node_mem C hk_mem]
        refine SplayDeque.Direct.isBSTNode k _ _ ?_ ?_ (ihl (bst_left ht)) (ihr (bst_right ht))
        · rw [SplayDeque.Direct.forallTree_iff]
          intro x hx
          exact bst_lt_left ht ((mem_restrictTree_iff l (bst_left ht) C x).mp hx).1
        · rw [SplayDeque.Direct.forallTree_iff]
          intro x hx
          exact bst_gt_right ht ((mem_restrictTree_iff r (bst_right ht) C x).mp hx).1

private theorem keyFinset_restrictTree (t : BinaryTree ℕ) (ht : t.IsBST)
    (C : IntervalBlock) :
    keyFinset (restrictTree t C.toSet) = keyFinset t ∩ C.toFinset := by
  ext x
  simp only [mem_keyFinset_iff, Finset.mem_inter, IntervalBlock.toFinset, Finset.mem_Icc,
    mem_restrictTree_iff t ht C x]

private theorem keyFinset_restrictTree_of_Icc {N : ℕ} {B : BinaryTree ℕ}
    (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    {C : IntervalBlock} (hC : 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N) :
    keyFinset (restrictTree B C.toSet) = C.toFinset := by
  rw [keyFinset_restrictTree B hB C, hkB]
  ext x
  simp only [Finset.mem_inter, Finset.mem_Icc, IntervalBlock.toFinset]
  omega

private theorem num_nodes_restrictTree_of_Icc {N : ℕ} {B : BinaryTree ℕ}
    (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    {C : IntervalBlock} (hC : 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N) :
    (restrictTree B C.toSet).num_nodes = C.size := by
  have hBC : (restrictTree B C.toSet).IsBST := restrictTree_isBST B hB C
  rw [← card_keyFinset_eq_num_nodes _ hBC, keyFinset_restrictTree_of_Icc hB hkB hC]
  simp only [IntervalBlock.toFinset, Nat.card_Icc, IntervalBlock.size, hC.2.1, ↓reduceIte]
  omega

/-! ### `sumTruncLD`, Upper Bound, Monotonicity, and Single-Rotation Drops -/

private def sumTruncLD (D : ℕ) : ℕ → BinaryTree ℕ → ℕ
  | _, .nil => 0
  | ld, .node _ l r => min ld D + sumTruncLD D (ld + 1) l + sumTruncLD D ld r

private theorem sum_keyFinset_min_leftDepth_eq (D : ℕ) (T : BinaryTree ℕ)
    (hT : T.IsBST) (ld : ℕ) :
    (keyFinset T).sum (fun v => min (ld + leftDepth T v) D) = sumTruncLD D ld T := by
  induction T generalizing ld with
  | nil => simp [keyFinset, sumTruncLD]
  | node k l r ihl ihr =>
    have hkl : k ∉ keyFinset l := by
      intro hk; exact lt_irrefl k (bst_lt_left hT ((mem_keyFinset_iff l k).mp hk))
    have hkr : k ∉ keyFinset r := by
      intro hk; exact lt_irrefl k (bst_gt_right hT ((mem_keyFinset_iff r k).mp hk))
    have hdisj : Disjoint (keyFinset l) (keyFinset r) := by
      rw [Finset.disjoint_left]
      intro x hxl hxr
      exact lt_asymm
        (bst_lt_left hT ((mem_keyFinset_iff l x).mp hxl))
        (bst_gt_right hT ((mem_keyFinset_iff r x).mp hxr))
    have hku : k ∉ keyFinset l ∪ keyFinset r := by simp [hkl, hkr]
    rw [keyFinset, Finset.sum_insert hku, Finset.sum_union hdisj]
    have hk0 : leftDepth (.node k l r) k = 0 := by simp [leftDepth]
    have hsum_l : (keyFinset l).sum (fun v => min (ld + leftDepth (.node k l r) v) D) =
        sumTruncLD D (ld + 1) l := by
      rw [← ihl (bst_left hT) (ld + 1)]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hlt : v < k := bst_lt_left hT ((mem_keyFinset_iff l v).mp hv)
      simp only [leftDepth, hlt, ↓reduceIte]
      congr 1; omega
    have hsum_r : (keyFinset r).sum (fun v => min (ld + leftDepth (.node k l r) v) D) =
        sumTruncLD D ld r := by
      rw [← ihr (bst_right hT) ld]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hgt : k < v := bst_gt_right hT ((mem_keyFinset_iff r v).mp hv)
      have hnlt : ¬ v < k := not_lt_of_gt hgt
      simp only [leftDepth, hnlt, hgt, ↓reduceIte]
    simp only [hk0, Nat.add_zero, hsum_l, hsum_r, sumTruncLD]
    omega

private theorem psiBlock_eq_aux {N D : ℕ} {B : BinaryTree ℕ}
    (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    {C : IntervalBlock} (hC : 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N) :
    psiBlock C D B =
      (leftSpine (restrictTree B C.toSet)).length +
        sumTruncLD D 0 (restrictTree B C.toSet) := by
  unfold psiBlock
  have hBC : (restrictTree B C.toSet).IsBST := restrictTree_isBST B hB C
  have hkBC : C.toFinset = keyFinset (restrictTree B C.toSet) :=
    (keyFinset_restrictTree_of_Icc hB hkB hC).symm
  dsimp only
  rw [hkBC]
  have hsum := sum_keyFinset_min_leftDepth_eq D (restrictTree B C.toSet) hBC 0
  simp only [Nat.zero_add] at hsum
  rw [hsum]

private theorem sumTruncLD_le (D ld : ℕ) (T : BinaryTree ℕ) :
    sumTruncLD D ld T ≤ D * T.num_nodes := by
  induction T generalizing ld with
  | nil => simp [sumTruncLD, BinaryTree.num_nodes]
  | node k l r ihl ihr =>
    simp only [sumTruncLD, BinaryTree.num_nodes]
    have h1 : min ld D ≤ D := Nat.min_le_right ld D
    have h2 := ihl (ld + 1)
    have h3 := ihr ld
    nlinarith

private theorem psiBlock_le_bound {N D : ℕ} {B : BinaryTree ℕ}
    (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    {C : IntervalBlock} (hC : 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N) :
    psiBlock C D B ≤ (D + 1) * C.size := by
  rw [psiBlock_eq_aux hB hkB hC]
  have hsp := leftSpine_length_le_num_nodes (restrictTree B C.toSet)
  have htr := sumTruncLD_le D 0 (restrictTree B C.toSet)
  have hnum := num_nodes_restrictTree_of_Icc hB hkB hC
  nlinarith

private theorem sumTruncLD_mono (D : ℕ) {ld₁ ld₂ : ℕ} (h : ld₁ ≤ ld₂)
    (T : BinaryTree ℕ) : sumTruncLD D ld₁ T ≤ sumTruncLD D ld₂ T := by
  induction T generalizing ld₁ ld₂ with
  | nil => exact le_rfl
  | node _ l r ihl ihr =>
    simp only [sumTruncLD]
    have hm : min ld₁ D ≤ min ld₂ D := by omega
    have hl := ihl (by omega : ld₁ + 1 ≤ ld₂ + 1)
    have hr := ihr h
    omega

private theorem leftSpine_rotateRightEdge_le_and_drop (T : BinaryTree ℕ) (hT : T.IsBST)
    (u v : ℕ) (hedge : IsRightRotEdge T u v) :
    (leftSpine (rotateRightEdge T u v)).length ≤ (leftSpine T).length ∧
      (v ∈ leftSpine T →
        (leftSpine (rotateRightEdge T u v)).length + 1 = (leftSpine T).length) := by
  rcases hedge with ⟨A, M, R, hv_mem, hsub⟩
  induction T with
  | nil => simp at hv_mem
  | node k l r ihl ihr =>
    by_cases hvk : v < k
    · simp only [subtreeAtKey, hvk, ↓reduceIte] at hsub
      have hv_l : v ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hv_mem with rfl | hvl | hvr
        · exact absurd hvk (lt_irrefl _)
        · exact hvl
        · exact absurd (lt_trans hvk (bst_gt_right hT hvr)) (lt_irrefl _)
      obtain ⟨hle, hdrop⟩ := ihl (bst_left hT) hv_l hsub
      simp only [rotateRightEdge, hvk, ↓reduceIte, leftSpine, List.length_append,
        List.length_singleton, List.mem_append, List.mem_singleton]
      refine ⟨by omega, ?_⟩
      rintro (hsp | rfl)
      · have := hdrop hsp; omega
      · exact absurd hvk (lt_irrefl _)
    · by_cases hkv : k < v
      · simp only [rotateRightEdge, hvk, hkv, ↓reduceIte, leftSpine, List.length_append,
          List.length_singleton, List.mem_append, List.mem_singleton]
        refine ⟨le_rfl, ?_⟩
        rintro (hsp | rfl)
        · have := bst_lt_left hT (mem_of_mem_leftSpine l hsp); omega
        · exact absurd hkv (lt_irrefl _)
      · have hv_eq : v = k := le_antisymm (not_lt.mp hkv) (not_lt.mp hvk)
        subst hv_eq
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l r
        simp only [rotateRightEdge, lt_irrefl, ↓reduceIte, leftSpine, List.length_append,
          List.length_singleton]
        exact ⟨by omega, fun _ => trivial⟩

private theorem sumTruncLD_rotateRightEdge_le_and_drop (D : ℕ) (T : BinaryTree ℕ)
    (hT : T.IsBST) (u v : ℕ) (hedge : IsRightRotEdge T u v) (ld : ℕ) :
    sumTruncLD D ld (rotateRightEdge T u v) ≤ sumTruncLD D ld T ∧
      (ld + leftDepth T v < D →
        sumTruncLD D ld (rotateRightEdge T u v) + 1 ≤ sumTruncLD D ld T) := by
  rcases hedge with ⟨A, M, R, hv_mem, hsub⟩
  revert ld
  induction T with
  | nil => simp at hv_mem
  | node k l r ihl ihr =>
    intro ld
    by_cases hvk : v < k
    · simp only [subtreeAtKey, hvk, ↓reduceIte] at hsub
      have hv_l : v ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hv_mem with rfl | hvl | hvr
        · exact absurd hvk (lt_irrefl _)
        · exact hvl
        · exact absurd (lt_trans hvk (bst_gt_right hT hvr)) (lt_irrefl _)
      obtain ⟨hle, hdrop⟩ := ihl (bst_left hT) hv_l hsub (ld + 1)
      simp only [rotateRightEdge, hvk, ↓reduceIte, sumTruncLD]
      refine ⟨by omega, fun hlt => ?_⟩
      simp only [leftDepth, hvk, ↓reduceIte] at hlt
      have hd := hdrop (by omega)
      omega
    · by_cases hkv : k < v
      · simp only [subtreeAtKey, hvk, hkv, ↓reduceIte] at hsub
        have hv_r : v ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hv_mem with rfl | hvl | hvr
          · exact absurd hkv (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hT hvl) hkv) (lt_irrefl _)
          · exact hvr
        obtain ⟨hle, hdrop⟩ := ihr (bst_right hT) hv_r hsub ld
        simp only [rotateRightEdge, hvk, hkv, ↓reduceIte, sumTruncLD]
        refine ⟨by omega, fun hlt => ?_⟩
        simp only [leftDepth, hvk, hkv, ↓reduceIte] at hlt
        have hd := hdrop hlt
        omega
      · have hv_eq : v = k := le_antisymm (not_lt.mp hkv) (not_lt.mp hvk)
        subst hv_eq
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l r
        have hmonoA : sumTruncLD D (ld + 1) A ≤ sumTruncLD D (ld + 1 + 1) A :=
          sumTruncLD_mono D (by omega) A
        simp only [rotateRightEdge, lt_irrefl, ↓reduceIte, sumTruncLD]
        refine ⟨by omega, fun hlt => ?_⟩
        simp only [leftDepth, lt_irrefl, ↓reduceIte, Nat.add_zero] at hlt
        omega

/-! ### Commutation of `restrictTree _ C.toSet` with `rotateRightEdge` -/

private theorem restrictTree_rotateRightEdge_out (B : BinaryTree ℕ) (hB : B.IsBST)
    (u v : ℕ) (huv : u < v) (hedge : IsRightRotEdge B u v) (C : IntervalBlock)
    (hout : ¬ ((C.lo ≤ u ∧ u ≤ C.hi) ∧ (C.lo ≤ v ∧ v ≤ C.hi))) :
    restrictTree (rotateRightEdge B u v) C.toSet = restrictTree B C.toSet := by
  have hB' : (rotateRightEdge B u v).IsBST := (rotateRightEdge_spec B u v hB huv hedge).1
  rcases hedge with ⟨A, M, R, hv_mem, hsub⟩
  induction B with
  | nil => simp at hv_mem
  | node k l r ihl ihr =>
    by_cases hvk : v < k
    · simp only [subtreeAtKey, hvk, ↓reduceIte] at hsub
      have hv_l : v ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hv_mem with rfl | hvl | hvr
        · exact absurd hvk (lt_irrefl _)
        · exact hvl
        · exact absurd (lt_trans hvk (bst_gt_right hB hvr)) (lt_irrefl _)
      simp only [rotateRightEdge, hvk, ↓reduceIte] at hB' ⊢
      have heq_l : restrictTree (rotateRightEdge l u v) C.toSet = restrictTree l C.toSet :=
        ihl (bst_left hB) (bst_left hB') hv_l hsub
      by_cases hk_lt : k < C.lo
      · rw [restrictTree_node_lt hB' C hk_lt, restrictTree_node_lt hB C hk_lt]
      · by_cases hk_gt : C.hi < k
        · rw [restrictTree_node_gt hB' C hk_gt, restrictTree_node_gt hB C hk_gt, heq_l]
        · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
          rw [restrictTree_node_mem C hk_mem, restrictTree_node_mem C hk_mem, heq_l]
    · by_cases hkv : k < v
      · simp only [subtreeAtKey, hvk, hkv, ↓reduceIte] at hsub
        have hv_r : v ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hv_mem with rfl | hvl | hvr
          · exact absurd hkv (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hB hvl) hkv) (lt_irrefl _)
          · exact hvr
        simp only [rotateRightEdge, hvk, hkv, ↓reduceIte] at hB' ⊢
        have heq_r : restrictTree (rotateRightEdge r u v) C.toSet = restrictTree r C.toSet :=
          ihr (bst_right hB) (bst_right hB') hv_r hsub
        by_cases hk_lt : k < C.lo
        · rw [restrictTree_node_lt hB' C hk_lt, restrictTree_node_lt hB C hk_lt, heq_r]
        · by_cases hk_gt : C.hi < k
          · rw [restrictTree_node_gt hB' C hk_gt, restrictTree_node_gt hB C hk_gt]
          · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
            rw [restrictTree_node_mem C hk_mem, restrictTree_node_mem C hk_mem, heq_r]
      · have hv_eq : v = k := le_antisymm (not_lt.mp hkv) (not_lt.mp hvk)
        subst hv_eq
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l r
        simp only [rotateRightEdge, lt_irrefl, ↓reduceIte] at hB' ⊢
        have huA_bst : (BinaryTree.node u A M).IsBST := bst_left hB
        have hvM_bst : (BinaryTree.node v M R).IsBST := bst_right hB'
        by_cases hv_lt : v < C.lo
        · have hu_lt : u < C.lo := by omega
          rw [restrictTree_node_lt hB' C hu_lt, restrictTree_node_lt hvM_bst C hv_lt,
            restrictTree_node_lt hB C hv_lt]
        · by_cases hu_lt : u < C.lo
          · by_cases hv_gt : C.hi < v
            · rw [restrictTree_node_lt hB' C hu_lt, restrictTree_node_gt hvM_bst C hv_gt,
                restrictTree_node_gt hB C hv_gt, restrictTree_node_lt huA_bst C hu_lt]
            · have hv_memC : C.lo ≤ v ∧ v ≤ C.hi := by omega
              rw [restrictTree_node_lt hB' C hu_lt, restrictTree_node_mem C hv_memC,
                restrictTree_node_mem C hv_memC, restrictTree_node_lt huA_bst C hu_lt]
          · by_cases hu_gt : C.hi < u
            · have hv_gt : C.hi < v := by omega
              rw [restrictTree_node_gt hB' C hu_gt,
                restrictTree_node_gt hB C hv_gt, restrictTree_node_gt huA_bst C hu_gt]
            · have hu_memC : C.lo ≤ u ∧ u ≤ C.hi := by omega
              have hv_gt : C.hi < v := by omega
              rw [restrictTree_node_mem C hu_memC, restrictTree_node_gt hvM_bst C hv_gt,
                restrictTree_node_gt hB C hv_gt, restrictTree_node_mem C hu_memC]

private theorem restrictTree_rotateRightEdge_in (B : BinaryTree ℕ) (hB : B.IsBST)
    (u v : ℕ) (huv : u < v) (hedge : IsRightRotEdge B u v) (C : IntervalBlock)
    (hin : (C.lo ≤ u ∧ u ≤ C.hi) ∧ (C.lo ≤ v ∧ v ≤ C.hi)) :
    IsRightRotEdge (restrictTree B C.toSet) u v ∧
      restrictTree (rotateRightEdge B u v) C.toSet =
        rotateRightEdge (restrictTree B C.toSet) u v := by
  have hB' : (rotateRightEdge B u v).IsBST := (rotateRightEdge_spec B u v hB huv hedge).1
  rcases hedge with ⟨A, M, R, hv_mem, hsub⟩
  induction B with
  | nil => simp at hv_mem
  | node k l r ihl ihr =>
    by_cases hvk : v < k
    · simp only [subtreeAtKey, hvk, ↓reduceIte] at hsub
      have hv_l : v ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hv_mem with rfl | hvl | hvr
        · exact absurd hvk (lt_irrefl _)
        · exact hvl
        · exact absurd (lt_trans hvk (bst_gt_right hB hvr)) (lt_irrefl _)
      simp only [rotateRightEdge, hvk, ↓reduceIte] at hB' ⊢
      obtain ⟨hedge_l, heq_l⟩ := ihl (bst_left hB) (bst_left hB') hv_l hsub
      by_cases hk_gt : C.hi < k
      · rw [restrictTree_node_gt hB' C hk_gt, restrictTree_node_gt hB C hk_gt]
        exact ⟨hedge_l, heq_l⟩
      · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
        rw [restrictTree_node_mem C hk_mem, restrictTree_node_mem C hk_mem]
        rcases hedge_l with ⟨A', M', R', hv_l', hsub_l'⟩
        refine ⟨⟨A', M', R', BinaryTree.mem_node_iff.mpr (Or.inr (Or.inl hv_l')), ?_⟩, ?_⟩
        · simp only [subtreeAtKey, hvk, ↓reduceIte]; exact hsub_l'
        · simp only [rotateRightEdge, hvk, ↓reduceIte, heq_l]
    · by_cases hkv : k < v
      · simp only [subtreeAtKey, hvk, hkv, ↓reduceIte] at hsub
        have hv_r : v ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hv_mem with rfl | hvl | hvr
          · exact absurd hkv (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hB hvl) hkv) (lt_irrefl _)
          · exact hvr
        have hu_sub : u ∈ subtreeAtKey r v := by
          rw [hsub]
          exact BinaryTree.mem_node_iff.mpr (Or.inr (Or.inl (BinaryTree.mem_node_iff.mpr (Or.inl rfl))))
        have hku : k < u := bst_gt_right hB (mem_of_mem_subtreeAtKey r hu_sub)
        simp only [rotateRightEdge, hvk, hkv, ↓reduceIte] at hB' ⊢
        obtain ⟨hedge_r, heq_r⟩ := ihr (bst_right hB) (bst_right hB') hv_r hsub
        by_cases hk_lt : k < C.lo
        · rw [restrictTree_node_lt hB' C hk_lt, restrictTree_node_lt hB C hk_lt]
          exact ⟨hedge_r, heq_r⟩
        · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
          rw [restrictTree_node_mem C hk_mem, restrictTree_node_mem C hk_mem]
          rcases hedge_r with ⟨A', M', R', hv_r', hsub_r'⟩
          refine ⟨⟨A', M', R', BinaryTree.mem_node_iff.mpr (Or.inr (Or.inr hv_r')), ?_⟩, ?_⟩
          · simp only [subtreeAtKey, hvk, hkv, ↓reduceIte]; exact hsub_r'
          · simp only [rotateRightEdge, hvk, hkv, ↓reduceIte, heq_r]
      · have hv_eq : v = k := le_antisymm (not_lt.mp hkv) (not_lt.mp hvk)
        subst hv_eq
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l r
        simp only [rotateRightEdge, lt_irrefl, ↓reduceIte]
        rw [restrictTree_node_mem C hin.2, restrictTree_node_mem C hin.1,
          restrictTree_node_mem C hin.1, restrictTree_node_mem C hin.2]
        refine ⟨⟨restrictTree A C.toSet, restrictTree M C.toSet, restrictTree R C.toSet,
          BinaryTree.mem_node_iff.mpr (Or.inl rfl), ?_⟩, ?_⟩
        · simp [subtreeAtKey]
        · simp [rotateRightEdge]

private theorem psiBlock_rotateRightEdge_le {N D : ℕ} {B : BinaryTree ℕ}
    (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    {u v : ℕ} (huv : u < v) (hedge : IsRightRotEdge B u v)
    {C : IntervalBlock} (hC : 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N) :
    psiBlock C D (rotateRightEdge B u v) ≤ psiBlock C D B := by
  have hB' : (rotateRightEdge B u v).IsBST := (rotateRightEdge_spec B u v hB huv hedge).1
  have hkB' : keyFinset (rotateRightEdge B u v) = Finset.Icc 1 N := by
    rw [rotateRightEdge_keyFinset B u v hB huv hedge, hkB]
  by_cases hin : (C.lo ≤ u ∧ u ≤ C.hi) ∧ (C.lo ≤ v ∧ v ≤ C.hi)
  · obtain ⟨hedgeC, heqC⟩ := restrictTree_rotateRightEdge_in B hB u v huv hedge C hin
    rw [psiBlock_eq_aux hB' hkB' hC, psiBlock_eq_aux hB hkB hC, heqC]
    have hBC : (restrictTree B C.toSet).IsBST := restrictTree_isBST B hB C
    have hsp := (leftSpine_rotateRightEdge_le_and_drop _ hBC u v hedgeC).1
    have htr := (sumTruncLD_rotateRightEdge_le_and_drop D _ hBC u v hedgeC 0).1
    omega
  · have heqC := restrictTree_rotateRightEdge_out B hB u v huv hedge C hin
    unfold psiBlock
    simp only [heqC, le_rfl]

private theorem psiBlock_rotateRightEdge_drop_spine {N D : ℕ} {B : BinaryTree ℕ}
    (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    {u v : ℕ} (huv : u < v) (hedge : IsRightRotEdge B u v)
    {C : IntervalBlock} (hC : 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N)
    (hin : (C.lo ≤ u ∧ u ≤ C.hi) ∧ (C.lo ≤ v ∧ v ≤ C.hi))
    (hsp_mem : v ∈ leftSpine (restrictTree B C.toSet)) :
    psiBlock C D (rotateRightEdge B u v) + 1 ≤ psiBlock C D B := by
  have hB' : (rotateRightEdge B u v).IsBST := (rotateRightEdge_spec B u v hB huv hedge).1
  have hkB' : keyFinset (rotateRightEdge B u v) = Finset.Icc 1 N := by
    rw [rotateRightEdge_keyFinset B u v hB huv hedge, hkB]
  obtain ⟨hedgeC, heqC⟩ := restrictTree_rotateRightEdge_in B hB u v huv hedge C hin
  rw [psiBlock_eq_aux hB' hkB' hC, psiBlock_eq_aux hB hkB hC, heqC]
  have hBC : (restrictTree B C.toSet).IsBST := restrictTree_isBST B hB C
  have hsp := (leftSpine_rotateRightEdge_le_and_drop _ hBC u v hedgeC).2 hsp_mem
  have htr := (sumTruncLD_rotateRightEdge_le_and_drop D _ hBC u v hedgeC 0).1
  omega

private theorem psiBlock_rotateRightEdge_drop_ld {N D : ℕ} {B : BinaryTree ℕ}
    (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    {u v : ℕ} (huv : u < v) (hedge : IsRightRotEdge B u v)
    {C : IntervalBlock} (hC : 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N)
    (hin : (C.lo ≤ u ∧ u ≤ C.hi) ∧ (C.lo ≤ v ∧ v ≤ C.hi))
    (hld_lt : leftDepth (restrictTree B C.toSet) v < D) :
    psiBlock C D (rotateRightEdge B u v) + 1 ≤ psiBlock C D B := by
  have hB' : (rotateRightEdge B u v).IsBST := (rotateRightEdge_spec B u v hB huv hedge).1
  have hkB' : keyFinset (rotateRightEdge B u v) = Finset.Icc 1 N := by
    rw [rotateRightEdge_keyFinset B u v hB huv hedge, hkB]
  obtain ⟨hedgeC, heqC⟩ := restrictTree_rotateRightEdge_in B hB u v huv hedge C hin
  rw [psiBlock_eq_aux hB' hkB' hC, psiBlock_eq_aux hB hkB hC, heqC]
  have hBC : (restrictTree B C.toSet).IsBST := restrictTree_isBST B hB C
  have hsp := (leftSpine_rotateRightEdge_le_and_drop _ hBC u v hedgeC).1
  have htr := (sumTruncLD_rotateRightEdge_le_and_drop D _ hBC u v hedgeC 0).2 (by omega)
  omega

/-! ### `searchAncestors` Formulas for `leftSpine` Membership and `leftDepth` in `restrictTree` -/

private def searchAncestors : BinaryTree ℕ → ℕ → List ℕ
  | .nil, _ => []
  | .node k l r, y =>
    if y < k then k :: searchAncestors l y
    else if k < y then k :: searchAncestors r y
    else []

private theorem mem_leftSpine_restrictTree_iff (T : BinaryTree ℕ) (hT : T.IsBST)
    (C : IntervalBlock) {y : ℕ} (hy : y ∈ T) (hyC : C.lo ≤ y ∧ y ≤ C.hi) :
    y ∈ leftSpine (restrictTree T C.toSet) ↔
      ∀ a ∈ searchAncestors T y, ¬ (C.lo ≤ a ∧ a < y) := by
  induction T with
  | nil => simp at hy
  | node k l r ihl ihr =>
    by_cases hyk : y < k
    · have hy_l : y ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hy with rfl | hyl | hyr
        · exact absurd hyk (lt_irrefl _)
        · exact hyl
        · exact absurd (lt_trans hyk (bst_gt_right hT hyr)) (lt_irrefl _)
      simp only [searchAncestors, hyk, ↓reduceIte, List.mem_cons]
      have hk_cond : ¬ (C.lo ≤ k ∧ k < y) := by omega
      have hrhs : (∀ a, a = k ∨ a ∈ searchAncestors l y → ¬ (C.lo ≤ a ∧ a < y)) ↔
          (∀ a ∈ searchAncestors l y, ¬ (C.lo ≤ a ∧ a < y)) := by
        constructor
        · intro h a ha; exact h a (Or.inr ha)
        · intro h a ha
          rcases ha with rfl | ha
          · exact hk_cond
          · exact h a ha
      rw [hrhs, ← ihl (bst_left hT) hy_l]
      by_cases hk_gt : C.hi < k
      · rw [restrictTree_node_gt hT C hk_gt]
      · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
        rw [restrictTree_node_mem C hk_mem]
        simp only [leftSpine, List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | rfl)
          · exact h
          · exact absurd hyk (lt_irrefl _)
        · exact Or.inl
    · by_cases hky : k < y
      · have hy_r : y ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hy with rfl | hyl | hyr
          · exact absurd hky (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hT hyl) hky) (lt_irrefl _)
          · exact hyr
        simp only [searchAncestors, hyk, hky, ↓reduceIte, List.mem_cons]
        by_cases hk_lt : k < C.lo
        · have hk_cond : ¬ (C.lo ≤ k ∧ k < y) := by omega
          have hrhs : (∀ a, a = k ∨ a ∈ searchAncestors r y → ¬ (C.lo ≤ a ∧ a < y)) ↔
              (∀ a ∈ searchAncestors r y, ¬ (C.lo ≤ a ∧ a < y)) := by
            constructor
            · intro h a ha; exact h a (Or.inr ha)
            · intro h a ha
              rcases ha with rfl | ha
              · exact hk_cond
              · exact h a ha
          rw [restrictTree_node_lt hT C hk_lt, hrhs, ihr (bst_right hT) hy_r]
        · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
          rw [restrictTree_node_mem C hk_mem]
          simp only [leftSpine, List.mem_append, List.mem_singleton]
          constructor
          · rintro (h | rfl)
            · have hy_in_l : y ∈ l :=
                ((mem_restrictTree_iff l (bst_left hT) C y).mp (mem_of_mem_leftSpine _ h)).1
              exact absurd (lt_trans hky (bst_lt_left hT hy_in_l)) (lt_irrefl _)
            · exact absurd hky (lt_irrefl _)
          · intro h
            exact absurd ⟨hk_mem.1, hky⟩ (h k (Or.inl rfl))
      · have hy_eq : y = k := le_antisymm (not_lt.mp hky) (not_lt.mp hyk)
        subst hy_eq
        rw [restrictTree_node_mem C hyC]
        simp [leftSpine, searchAncestors]

private theorem leftDepth_restrictTree_eq (T : BinaryTree ℕ) (hT : T.IsBST)
    (C : IntervalBlock) {y : ℕ} (hy : y ∈ T) (hyC : C.lo ≤ y ∧ y ≤ C.hi) :
    leftDepth (restrictTree T C.toSet) y =
      ((searchAncestors T y).filter (fun a => decide (y < a ∧ a ≤ C.hi))).length := by
  induction T with
  | nil => simp at hy
  | node k l r ihl ihr =>
    by_cases hyk : y < k
    · have hy_l : y ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hy with rfl | hyl | hyr
        · exact absurd hyk (lt_irrefl _)
        · exact hyl
        · exact absurd (lt_trans hyk (bst_gt_right hT hyr)) (lt_irrefl _)
      by_cases hk_gt : C.hi < k
      · have hnk : ¬ k ≤ C.hi := by omega
        rw [restrictTree_node_gt hT C hk_gt]
        simp only [searchAncestors, hyk, ↓reduceIte, List.filter_cons, true_and, hnk,
          decide_false, Bool.false_eq_true]
        exact ihl (bst_left hT) hy_l
      · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
        rw [restrictTree_node_mem C hk_mem]
        simp only [leftDepth, searchAncestors, hyk, ↓reduceIte, List.filter_cons, true_and,
          hk_mem.2, decide_true, List.length_cons, ihl (bst_left hT) hy_l]
        omega
    · by_cases hky : k < y
      · have hy_r : y ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hy with rfl | hyl | hyr
          · exact absurd hky (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hT hyl) hky) (lt_irrefl _)
          · exact hyr
        simp only [searchAncestors, hyk, hky, ↓reduceIte, List.filter_cons, false_and,
          decide_false, Bool.false_eq_true]
        by_cases hk_lt : k < C.lo
        · rw [restrictTree_node_lt hT C hk_lt]
          exact ihr (bst_right hT) hy_r
        · have hk_mem : C.lo ≤ k ∧ k ≤ C.hi := by omega
          rw [restrictTree_node_mem C hk_mem]
          simp only [leftDepth, hyk, hky, ↓reduceIte]
          exact ihr (bst_right hT) hy_r
      · have hy_eq : y = k := le_antisymm (not_lt.mp hky) (not_lt.mp hyk)
        subst hy_eq
        rw [restrictTree_node_mem C hyC]
        simp [leftDepth, searchAncestors]

private theorem searchAncestors_rotateRightEdge_below_left (T : BinaryTree ℕ)
    (hT : T.IsBST) {y a b : ℕ} (hy : y ∈ T)
    (hb_sub : b ∈ subtreeAtKey T y) (hb_lt : b < y) :
    searchAncestors (rotateRightEdge T a b) y = searchAncestors T y := by
  induction T with
  | nil => simp at hy
  | node k l r ihl ihr =>
    by_cases hyk : y < k
    · simp only [subtreeAtKey, hyk, ↓reduceIte] at hb_sub
      have hy_l : y ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hy with rfl | hyl | hyr
        · exact absurd hyk (lt_irrefl _)
        · exact hyl
        · exact absurd (lt_trans hyk (bst_gt_right hT hyr)) (lt_irrefl _)
      have hbk : b < k := bst_lt_left hT (mem_of_mem_subtreeAtKey l hb_sub)
      simp only [rotateRightEdge, hbk, ↓reduceIte, searchAncestors, hyk,
        ihl (bst_left hT) hy_l hb_sub]
    · by_cases hky : k < y
      · simp only [subtreeAtKey, hyk, hky, ↓reduceIte] at hb_sub
        have hy_r : y ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hy with rfl | hyl | hyr
          · exact absurd hky (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hT hyl) hky) (lt_irrefl _)
          · exact hyr
        have hkb : k < b := bst_gt_right hT (mem_of_mem_subtreeAtKey r hb_sub)
        have hnbk : ¬ b < k := not_lt_of_gt hkb
        simp only [rotateRightEdge, hnbk, hkb, ↓reduceIte, searchAncestors, hyk, hky,
          ihr (bst_right hT) hy_r hb_sub]
      · have hy_eq : y = k := le_antisymm (not_lt.mp hky) (not_lt.mp hyk)
        subst hy_eq
        simp [rotateRightEdge, hb_lt, searchAncestors]

private theorem below_left_rot_invariant (T : BinaryTree ℕ) (hT : T.IsBST)
    {y a b : ℕ} (hy : y ∈ T) (hab : a < b) (hedge : IsRightRotEdge T a b)
    (hb_sub : b ∈ subtreeAtKey T y) (hb_lt : b < y) :
    y ∈ rotateRightEdge T a b ∧
      (∀ w : ℕ, w ∈ subtreeAtKey (rotateRightEdge T a b) y ↔ w ∈ subtreeAtKey T y) ∧
      searchAncestors (rotateRightEdge T a b) y = searchAncestors T y := by
  obtain ⟨hy', hsub_rot⟩ := subtreeAtKey_rotateRightEdge_below T hT hy hb_sub hb_lt
  have hedge_sub : IsRightRotEdge (subtreeAtKey T y) a b := by
    rcases hedge with ⟨A, M, R, _, hsub_b⟩
    refine ⟨A, M, R, hb_sub, ?_⟩
    rw [← subtreeAtKey_trans T hT hb_sub, hsub_b]
  have hmem_sub :=
    (rotateRightEdge_spec (subtreeAtKey T y) a b (subtreeAtKey_isBST T y hT) hab hedge_sub).2.1
  rw [hsub_rot]
  exact ⟨hy', hmem_sub, searchAncestors_rotateRightEdge_below_left T hT hy hb_sub hb_lt⟩

private theorem searchAncestors_sub (B : BinaryTree ℕ) (hB : B.IsBST)
    {top v : ℕ} (htop : top ∈ B) (hv : v ∈ subtreeAtKey B top) :
    searchAncestors B v = searchAncestors B top ++ searchAncestors (subtreeAtKey B top) v := by
  induction B with
  | nil => simp at htop
  | node k l r ihl ihr =>
    by_cases htk : top < k
    · simp only [subtreeAtKey, htk, ↓reduceIte] at hv ⊢
      have hvk : v < k := bst_lt_left hB (mem_of_mem_subtreeAtKey l hv)
      have htop_l : top ∈ l := by
        rcases BinaryTree.mem_node_iff.mp htop with rfl | h | h
        · exact absurd htk (lt_irrefl _)
        · exact h
        · exact absurd (lt_trans htk (bst_gt_right hB h)) (lt_irrefl _)
      simp only [searchAncestors, hvk, htk, ↓reduceIte, List.cons_append,
        ihl (bst_left hB) htop_l hv]
    · by_cases hkt : k < top
      · simp only [subtreeAtKey, htk, hkt, ↓reduceIte] at hv ⊢
        have hkv : k < v := bst_gt_right hB (mem_of_mem_subtreeAtKey r hv)
        have hnvk : ¬ v < k := not_lt_of_gt hkv
        have htop_r : top ∈ r := by
          rcases BinaryTree.mem_node_iff.mp htop with rfl | h | h
          · exact absurd hkt (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hB h) hkt) (lt_irrefl _)
          · exact h
        simp only [searchAncestors, hnvk, hkv, htk, hkt, ↓reduceIte, List.cons_append,
          ihr (bst_right hB) htop_r hv]
      · have htop_eq : top = k := le_antisymm (not_lt.mp hkt) (not_lt.mp htk)
        subst htop_eq
        simp [searchAncestors, subtreeAtKey]

private theorem searchAncestors_top_outside (B : BinaryTree ℕ) (hB : B.IsBST)
    {top a : ℕ} (htop : top ∈ B) (ha : a ∈ searchAncestors B top) :
    (∀ w ∈ subtreeAtKey B top, w < a) ∨ (∀ w ∈ subtreeAtKey B top, a < w) := by
  induction B with
  | nil => simp [searchAncestors] at ha
  | node k l r ihl ihr =>
    by_cases htk : top < k
    · simp only [searchAncestors, htk, ↓reduceIte, List.mem_cons] at ha
      simp only [subtreeAtKey, htk, ↓reduceIte]
      have htop_l : top ∈ l := by
        rcases BinaryTree.mem_node_iff.mp htop with rfl | h | h
        · exact absurd htk (lt_irrefl _)
        · exact h
        · exact absurd (lt_trans htk (bst_gt_right hB h)) (lt_irrefl _)
      rcases ha with rfl | ha_l
      · exact Or.inl (fun w hw => bst_lt_left hB (mem_of_mem_subtreeAtKey l hw))
      · exact ihl (bst_left hB) htop_l ha_l
    · by_cases hkt : k < top
      · simp only [searchAncestors, htk, hkt, ↓reduceIte, List.mem_cons] at ha
        simp only [subtreeAtKey, htk, hkt, ↓reduceIte]
        have htop_r : top ∈ r := by
          rcases BinaryTree.mem_node_iff.mp htop with rfl | h | h
          · exact absurd hkt (lt_irrefl _)
          · exact absurd (lt_trans (bst_lt_left hB h) hkt) (lt_irrefl _)
          · exact h
        rcases ha with rfl | ha_r
        · exact Or.inr (fun w hw => bst_gt_right hB (mem_of_mem_subtreeAtKey r hw))
        · exact ihr (bst_right hB) htop_r ha_r
      · have htop_eq : top = k := le_antisymm (not_lt.mp hkt) (not_lt.mp htk)
        subst htop_eq
        simp [searchAncestors] at ha

private theorem searchAncestors_leftSpine_getElem (S : BinaryTree ℕ) (hS : S.IsBST)
    (m : ℕ) (hm : m < (leftSpine S).length) :
    searchAncestors S ((leftSpine S)[m]) = ((leftSpine S).drop (m + 1)).reverse := by
  induction S with
  | nil => simp [leftSpine] at hm
  | node k l r ihl _ =>
    have hlen : (leftSpine (.node k l r)).length = (leftSpine l).length + 1 := by
      simp [leftSpine]
    by_cases hml : m < (leftSpine l).length
    · have hget : (leftSpine (.node k l r))[m] = (leftSpine l)[m] := by
        simp [leftSpine, List.getElem_append_left hml]
      have hw_lt : (leftSpine l)[m] < k :=
        bst_lt_left hS (mem_of_mem_leftSpine l (List.getElem_mem hml))
      rw [hget]
      simp only [searchAncestors, hw_lt, ↓reduceIte, ihl (bst_left hS) hml, leftSpine]
      rw [List.drop_append_of_le_length (by omega : m + 1 ≤ (leftSpine l).length),
        List.reverse_append, List.reverse_singleton, List.singleton_append]
    · have hm_eq : m = (leftSpine l).length := by omega
      have hget : (leftSpine (.node k l r))[m] = k := by simp [leftSpine, hm_eq]
      rw [hget]
      have hdrop_nil : (leftSpine (.node k l r)).drop (m + 1) = [] :=
        List.drop_eq_nil_of_le (by omega)
      rw [hdrop_nil]
      simp [searchAncestors]

/-! ### Block Partition, Prefix Execution, and Telescoping Helpers -/

private theorem consecutiveBlocks_adj (blocks : List IntervalBlock)
    (hcons : ConsecutiveBlocks blocks) (i : ℕ) (hi : i + 1 < blocks.length) :
    blocks[i].hi + 1 = blocks[i + 1].lo := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons C₁ rest ih =>
    rcases rest with _ | ⟨C₂, tail⟩
    · simp at hi
    · rcases i with _ | i'
      · exact hcons.1
      · simp only [List.length_cons] at hi
        exact ih hcons.2 i' (by simp only [List.length_cons]; omega)

private theorem blocks_hi_lt_lo_of_lt {N : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition N blocks)
    (q₁ q₂ : Fin blocks.length) (hlt : q₁ < q₂) :
    blocks[q₁].hi < blocks[q₂].lo := by
  have hlt_val : q₁.val < q₂.val := hlt
  obtain ⟨d, hd⟩ : ∃ d : ℕ, q₂.val = q₁.val + 1 + d := ⟨q₂.val - q₁.val - 1, by omega⟩
  induction d generalizing q₂ with
  | zero =>
    have hadj := consecutiveBlocks_adj blocks hPart.2.1 q₁.val (by omega)
    have hq2_eq : q₂ = ⟨q₁.val + 1, by omega⟩ := Fin.ext (by omega)
    rw [hq2_eq]
    change blocks[q₁.val].hi < blocks[q₁.val + 1].lo
    omega
  | succ d ih =>
    let qMid : Fin blocks.length := ⟨q₁.val + 1 + d, by omega⟩
    have hMid_val : qMid.val = q₁.val + 1 + d := rfl
    have h1 : blocks[q₁].hi < blocks[qMid].lo := ih qMid (by omega) (by omega) hMid_val
    have hMid_mem : blocks[qMid] ∈ blocks := List.getElem_mem qMid.isLt
    have hlo_hi : blocks[qMid].lo ≤ blocks[qMid].hi := (hPart.1 _ hMid_mem).2.1
    have hadj := consecutiveBlocks_adj blocks hPart.2.1 qMid.val (by omega)
    have hq2_eq : q₂ = ⟨qMid.val + 1, by omega⟩ := Fin.ext (by omega)
    rw [hq2_eq]
    change blocks[q₁].hi < blocks[qMid.val + 1].lo
    change blocks[q₁].hi < blocks[qMid.val].lo at h1
    change blocks[qMid.val].lo ≤ blocks[qMid.val].hi at hlo_hi
    omega

private theorem take_succ_eq_append_getElem {β : Type} (xs : List β) (t : ℕ)
    (ht : t < xs.length) : xs.take (t + 1) = xs.take t ++ [xs[t]] := by
  induction xs generalizing t with
  | nil => simp at ht
  | cons x xs ih =>
    cases t with
    | zero => rfl
    | succ t =>
      simp only [List.length_cons] at ht
      change x :: xs.take (t + 1) = x :: (xs.take t ++ [xs[t]])
      rw [ih t (by omega)]

private theorem drop_eq_getElem_cons {β : Type} (xs : List β) (t : ℕ)
    (ht : t < xs.length) : xs.drop t = xs[t] :: xs.drop (t + 1) := by
  induction xs generalizing t with
  | nil => simp at ht
  | cons x xs ih =>
    cases t with
    | zero => rfl
    | succ t =>
      simp only [List.length_cons] at ht
      exact ih t (by omega)

private theorem getLast?_eq_getElem?_pred {β : Type} (xs : List β)
    (hne : 0 < xs.length) : xs.getLast? = xs[xs.length - 1]? := by
  induction xs with
  | nil => simp at hne
  | cons x rest ih =>
    rcases rest with _ | ⟨y, tail⟩
    · rfl
    · have hpos : 0 < (y :: tail).length := by simp
      have hlast : (x :: y :: tail).getLast? = (y :: tail).getLast? := rfl
      rw [hlast, ih hpos]
      simp

private theorem list_sum_map_le {β : Type} (xs : List β) (f g : β → ℕ)
    (hle : ∀ x ∈ xs, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := hle x List.mem_cons_self
    have hr := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    omega

private theorem list_sum_map_lt_of_idx {β : Type} (xs : List β) (f g : β → ℕ)
    (hle : ∀ x ∈ xs, f x ≤ g x) (q : Fin xs.length) (hlt : f xs[q] + 1 ≤ g xs[q]) :
    (xs.map f).sum + 1 ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Fin.elim0 q
  | cons x rest ih =>
    rcases q with ⟨_ | q', hq⟩
    · simp only [Fin.getElem_fin, List.getElem_cons_zero] at hlt
      simp only [List.map_cons, List.sum_cons]
      have hr := list_sum_map_le rest f g (fun y hy => hle y (List.mem_cons_of_mem x hy))
      omega
    · simp only [Fin.getElem_fin, List.getElem_cons_succ] at hlt
      simp only [List.map_cons, List.sum_cons]
      have hx := hle x List.mem_cons_self
      have hr := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
        ⟨q', by simp at hq; omega⟩ hlt
      omega

private theorem nat_seq_le_interval (F : ℕ → ℕ) (a d : ℕ)
    (hmono : ∀ t, a ≤ t → t < a + d → F (t + 1) ≤ F t) :
    F (a + d) ≤ F a := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (fun t hta htd => hmono t hta (by omega))
    have h2 := hmono (a + d) (by omega) (by omega)
    rw [← Nat.add_assoc]
    omega

private theorem nat_seq_drop_at (F : ℕ → ℕ) (k : ℕ)
    (hmono : ∀ t < k, F (t + 1) ≤ F t)
    (r : ℕ) (hr : r < k) (hdrop : F (r + 1) + 1 ≤ F r) :
    F k + 1 ≤ F 0 := by
  have hpre : F r ≤ F 0 := by
    have h := nat_seq_le_interval F 0 r (fun t _ ht => hmono t (by omega))
    simpa using h
  have hpost : F k ≤ F (r + 1) := by
    have h := nat_seq_le_interval F (r + 1) (k - (r + 1))
      (fun t _ ht => hmono t (by omega))
    have heq : (r + 1) + (k - (r + 1)) = k := by omega
    rwa [heq] at h
  omega

private theorem exists_adj_crossing {k : ℕ} (P : Fin k → Prop)
    (r₀ r₁ : Fin k) (hlt : r₀.val < r₁.val) (h0 : P r₀) (h1 : ¬ P r₁) :
    ∃ (r : Fin k) (hr1 : r.val + 1 < k),
      r₀.val ≤ r.val ∧ P r ∧ ¬ P ⟨r.val + 1, hr1⟩ := by
  open Classical in
  obtain ⟨d, hd⟩ : ∃ d : ℕ, r₁.val = r₀.val + 1 + d := ⟨r₁.val - r₀.val - 1, by omega⟩
  induction d generalizing r₁ with
  | zero =>
    have hr1_lt : r₀.val + 1 < k := by omega
    have heq : (⟨r₀.val + 1, hr1_lt⟩ : Fin k) = r₁ := Fin.ext (by dsimp only; omega)
    refine ⟨r₀, hr1_lt, le_rfl, h0, ?_⟩
    rwa [heq]
  | succ d ih =>
    let rMid : Fin k := ⟨r₀.val + 1 + d, by omega⟩
    have hMid_val : rMid.val = r₀.val + 1 + d := rfl
    by_cases hMid : P rMid
    · have hrMid1 : rMid.val + 1 < k := by omega
      have heq : (⟨rMid.val + 1, hrMid1⟩ : Fin k) = r₁ := Fin.ext (by dsimp only; omega)
      refine ⟨rMid, hrMid1, by omega, hMid, ?_⟩
      rwa [heq]
    · exact ih rMid (by omega) hMid hMid_val

private def execPrefix (B : BinaryTree ℕ) (pairs : List (ℕ × ℕ)) (t : ℕ) : BinaryTree ℕ :=
  (pairs.take t).foldl (fun acc p => rotateRightEdge acc p.1 p.2) B

private theorem execPrefix_succ (B : BinaryTree ℕ) (pairs : List (ℕ × ℕ))
    (t : ℕ) (ht : t < pairs.length) :
    execPrefix B pairs (t + 1) =
      rotateRightEdge (execPrefix B pairs t) (pairs[t]).1 (pairs[t]).2 := by
  unfold execPrefix
  rw [take_succ_eq_append_getElem pairs t ht, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem execPrefix_full (B : BinaryTree ℕ) (pairs : List (ℕ × ℕ)) {k : ℕ}
    (hlen : pairs.length = k) :
    execPrefix B pairs k = execRightCascadeBatch B pairs := by
  unfold execPrefix execRightCascadeBatch
  rw [← hlen, List.take_length]

private theorem execPrefix_cascade_valid (B : BinaryTree ℕ) (hB : B.IsBST)
    {Δ' k : ℕ} {pairs : List (ℕ × ℕ)} (hcasc : IsGappedRightCascade B Δ' k pairs) :
    ∀ t ≤ k,
      (execPrefix B pairs t).IsBST ∧
      keyFinset (execPrefix B pairs t) = keyFinset B ∧
      (t < k → IsGappedRightCascade (execPrefix B pairs t) Δ' (k - t) (pairs.drop t)) := by
  have hlen : pairs.length = k := hcasc.2.1
  intro t ht
  induction t with
  | zero =>
    refine ⟨hB, rfl, fun _ => ?_⟩
    simpa [execPrefix] using hcasc
  | succ t ih =>
    obtain ⟨hBt, hkBt, hcasct_fn⟩ := ih (by omega)
    have ht_lt_k : t < k := by omega
    have ht_len : t < pairs.length := by omega
    have hcasct := hcasct_fn ht_lt_k
    rw [drop_eq_getElem_cons pairs t ht_len] at hcasct
    obtain ⟨hxy_t, hedge_t⟩ := cascade_head_edge hBt hcasct
    rw [execPrefix_succ B pairs t ht_len]
    have hBt1 := (rotateRightEdge_spec (execPrefix B pairs t) (pairs[t]).1 (pairs[t]).2
      hBt hxy_t hedge_t).1
    have hkBt1 : keyFinset (rotateRightEdge (execPrefix B pairs t) (pairs[t]).1 (pairs[t]).2) =
        keyFinset B := by
      rw [rotateRightEdge_keyFinset _ _ _ hBt hxy_t hedge_t, hkBt]
    refine ⟨hBt1, hkBt1, fun ht1_lt => ?_⟩
    have hk_sub : k - t = (k - (t + 1)) + 1 := by omega
    rw [hk_sub] at hcasct
    exact cascade_peel_cons hBt (by omega) hcasct

private theorem execPrefix_step_edge (B : BinaryTree ℕ) (hB : B.IsBST)
    {Δ' k : ℕ} {pairs : List (ℕ × ℕ)} (hcasc : IsGappedRightCascade B Δ' k pairs)
    (t : ℕ) (ht : t < k) :
    have ht_len : t < pairs.length := by have := hcasc.2.1; omega
    (pairs[t]).1 < (pairs[t]).2 ∧
      IsRightRotEdge (execPrefix B pairs t) (pairs[t]).1 (pairs[t]).2 := by
  have ht_len : t < pairs.length := by have := hcasc.2.1; omega
  obtain ⟨hBt, _, hcasct_fn⟩ := execPrefix_cascade_valid B hB hcasc t (by omega)
  have hcasct := hcasct_fn ht
  rw [drop_eq_getElem_cons pairs t ht_len] at hcasct
  exact cascade_head_edge hBt hcasct

/-! ### Complete Proof of Lemma 4.3 Part (2) and Lemma 4.3 -/

private theorem getElem_le_of_idx_eq (xs : List ℕ) {i j : ℕ}
    (hi : i < xs.length) (hj : j < xs.length) (h : i = j) :
    xs[i] ≤ xs[j] := by
  subst h; exact le_rfl

private theorem lem_4_3_part2 (N Δ' : ℕ) (_hN : 1 ≤ N) :
    let D := Δ' + 2
    ∀ (B : BinaryTree ℕ) (blocks : List IntervalBlock),
      B.IsBST → keyFinset B = Finset.Icc 1 N →
      IsContiguousBlockPartition N blocks →
      (∀ C ∈ blocks, psiBlock C D B ≤ (D + 1) * C.size) ∧
      (∀ u v : ℕ, u < v → IsRightRotEdge B u v →
        ∀ C ∈ blocks, psiBlock C D (rotateRightEdge B u v) ≤ psiBlock C D B) ∧
      (∀ (k : ℕ) (pairs : List (ℕ × ℕ)),
        2 ≤ k → IsGappedRightCascade B Δ' k pairs →
        (∃ (pFirst pLast : ℕ × ℕ) (qMin qMax : Fin blocks.length),
          pairs.head? = some pFirst ∧ pairs.getLast? = some pLast ∧
          qMin < qMax ∧
          pFirst.1 ∈ blocks[qMin].toFinset ∧ pLast.2 ∈ blocks[qMax].toFinset) →
        (∃ p ∈ pairs, ∃ C ∈ blocks, p.1 ∈ C.toFinset ∧ p.2 ∈ C.toFinset) →
        (blocks.map (fun C => psiBlock C D (execRightCascadeBatch B pairs))).sum + 1 ≤
          (blocks.map (fun C => psiBlock C D B)).sum) := by
  dsimp only
  set D := Δ' + 2
  intro B blocks hB hkB hPart
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    exact psiBlock_le_bound hB hkB (hPart.1 C hC)
  · intro u v huv hedge C hC
    exact psiBlock_rotateRightEdge_le hB hkB huv hedge (hPart.1 C hC)
  · intro k pairs hk2 hcasc hcross hintra
    have hlen : pairs.length = k := hcasc.2.1
    rcases hcasc.2.2 with ⟨top, htop, idx, hpairs, hgaps⟩
    let S0 := subtreeAtKey B top
    have hS0_bst : S0.IsBST := subtreeAtKey_isBST B top hB
    let path := leftSpine S0
    have hpath_lt : List.Pairwise (· < ·) path := leftSpine_pairwise_lt S0 hS0_bst
    -- Helper linking `pairs[r.val]` to `(path[idx r], path[idx r + 1])`
    have hpair_at : ∀ r : Fin k, ∃ hj : idx r + 1 < path.length,
        pairs[r.val]'(by omega) = (path[idx r], path[idx r + 1]) := by
      intro r
      obtain ⟨hj, hpr⟩ := hpairs r
      rw [List.getElem?_eq_getElem (by omega)] at hpr
      exact ⟨hj, Option.some.inj hpr⟩
    -- Prefix total potential `F t`
    let F : ℕ → ℕ := fun t =>
      (blocks.map (fun C => psiBlock C D (execPrefix B pairs t))).sum
    have hF0 : F 0 = (blocks.map (fun C => psiBlock C D B)).sum := rfl
    have hFk : F k = (blocks.map (fun C => psiBlock C D (execRightCascadeBatch B pairs))).sum := by
      dsimp only [F]
      rw [execPrefix_full B pairs hlen]
    -- Every prefix step is non-increasing on every block
    have hstep_block_le : ∀ (t : ℕ) (ht : t < k) (C : IntervalBlock), C ∈ blocks →
        psiBlock C D (execPrefix B pairs (t + 1)) ≤ psiBlock C D (execPrefix B pairs t) := by
      intro t ht C hC
      have ht_len : t < pairs.length := by omega
      obtain ⟨hBt, hkBt, _⟩ := execPrefix_cascade_valid B hB hcasc t (by omega)
      rw [hkB] at hkBt
      obtain ⟨hxy_t, hedge_t⟩ := execPrefix_step_edge B hB hcasc t ht
      rw [execPrefix_succ B pairs t ht_len]
      exact psiBlock_rotateRightEdge_le hBt hkBt hxy_t hedge_t (hPart.1 C hC)
    have hF_mono : ∀ t < k, F (t + 1) ≤ F t := by
      intro t ht
      exact list_sum_map_le blocks _ _ (fun C hC => hstep_block_le t ht C hC)
    -- Suffices to exhibit one step `r : Fin k` and one block `q : Fin blocks.length` dropping by `≥ 1`
    suffices h_one_drop : ∃ (r : Fin k) (q : Fin blocks.length),
        psiBlock blocks[q] D (execPrefix B pairs (r.val + 1)) + 1 ≤
          psiBlock blocks[q] D (execPrefix B pairs r.val) by
      obtain ⟨r, q, hq_drop⟩ := h_one_drop
      have hF_drop : F (r.val + 1) + 1 ≤ F r.val :=
        list_sum_map_lt_of_idx blocks _ _ (fun C hC => hstep_block_le r.val r.isLt C hC) q hq_drop
      have htot := nat_seq_drop_at F k hF_mono r.val r.isLt hF_drop
      rwa [hFk, hF0] at htot
    -- `searchAncestors` invariance at step `r` for `y_r = (pairs[r.val]).2`
    have hanc_step : ∀ r : Fin k,
        let yr := (pairs[r.val]'(by omega)).2
        yr ∈ execPrefix B pairs r.val ∧
          searchAncestors (execPrefix B pairs r.val) yr = searchAncestors B yr := by
      intro r
      obtain ⟨hjr, hpr_eq⟩ := hpair_at r
      let yr := (pairs[r.val]'(by omega)).2
      have hyr_eq : yr = path[idx r + 1] := by dsimp [yr]; rw [hpr_eq]
      have hyr_S0 : yr ∈ S0 := by
        rw [hyr_eq]
        exact mem_of_mem_leftSpine S0 (List.getElem_mem hjr)
      have hyr_B : yr ∈ B := mem_of_mem_subtreeAtKey B hyr_S0
      have hsp_yr : leftSpine (subtreeAtKey B yr) = path.take (idx r + 2) := by
        rw [subtreeAtKey_trans B hB hyr_S0, hyr_eq]
        exact leftSpine_subtreeAtKey_of_mem_spine S0 hS0_bst (idx r + 1) hjr
      have hprev_in_yr : ∀ (i : ℕ) (hi : i < r.val),
          (pairs[i]'(by omega)).2 ∈ subtreeAtKey B yr ∧ (pairs[i]'(by omega)).2 < yr := by
        intro i hi
        let ri : Fin k := ⟨i, by omega⟩
        obtain ⟨hji, hpi_eq⟩ := hpair_at ri
        have hmono := idx_mono_of_gaps idx hgaps ri r hi
        have hyi_eq : (pairs[i]'(by omega)).2 = path[idx ri + 1] := by
          change (pairs[ri.val]'(by omega)).2 = _
          rw [hpi_eq]
        have hyi_lt : (pairs[i]'(by omega)).2 < yr := by
          rw [hyi_eq, hyr_eq]
          exact List.pairwise_iff_getElem.mp hpath_lt (idx ri + 1) (idx r + 1)
            hji hjr (by omega)
        have hyi_sp : (pairs[i]'(by omega)).2 ∈ leftSpine (subtreeAtKey B yr) := by
          rw [hsp_yr, hyi_eq]
          have htake_get : (path.take (idx r + 2))[idx ri + 1]'(by simp [List.length_take]; omega) =
              path[idx ri + 1] := List.getElem_take
          rw [← htake_get]
          exact List.getElem_mem (by simp [List.length_take]; omega)
        exact ⟨mem_of_mem_leftSpine _ hyi_sp, hyi_lt⟩
      suffices hinv : ∀ t ≤ r.val,
          yr ∈ execPrefix B pairs t ∧
            (∀ w : ℕ, w ∈ subtreeAtKey (execPrefix B pairs t) yr ↔ w ∈ subtreeAtKey B yr) ∧
            searchAncestors (execPrefix B pairs t) yr = searchAncestors B yr by
        obtain ⟨h1, _, h3⟩ := hinv r.val le_rfl
        exact ⟨h1, h3⟩
      intro t ht
      induction t with
      | zero => exact ⟨hyr_B, fun _ => Iff.rfl, rfl⟩
      | succ t ih =>
        obtain ⟨hyr_t, hsub_t, hanc_t⟩ := ih (by omega)
        have ht_lt_r : t < r.val := by omega
        have ht_lt_k : t < k := by omega
        have ht_len : t < pairs.length := by omega
        obtain ⟨hBt, _, _⟩ := execPrefix_cascade_valid B hB hcasc t (by omega)
        obtain ⟨hxy_t, hedge_t⟩ := execPrefix_step_edge B hB hcasc t ht_lt_k
        obtain ⟨hyt_B, hyt_lt⟩ := hprev_in_yr t ht_lt_r
        have hyt_t : (pairs[t]).2 ∈ subtreeAtKey (execPrefix B pairs t) yr :=
          (hsub_t _).mpr hyt_B
        rw [execPrefix_succ B pairs t ht_len]
        obtain ⟨hyr_t1, hsub_t1, hanc_t1⟩ :=
          below_left_rot_invariant (execPrefix B pairs t) hBt hyr_t hxy_t hedge_t hyt_t hyt_lt
        exact ⟨hyr_t1, fun w => (hsub_t1 w).trans (hsub_t w), hanc_t1.trans hanc_t⟩
    -- Extract endpoints `x_0 = pFirst.1` and `y_{k-1} = pLast.2`
    let rFirst : Fin k := ⟨0, by omega⟩
    let rLast : Fin k := ⟨k - 1, by omega⟩
    obtain ⟨hjFirst, hpFirst_at⟩ := hpair_at rFirst
    obtain ⟨hjLast, hpLast_at⟩ := hpair_at rLast
    rcases hcross with ⟨pFirst, pLast, qMin, qMax, hhead, hlast_opt, hq_lt, hx0_mem, hyLast_mem⟩
    have hpFirst_eq : pFirst = (path[idx rFirst], path[idx rFirst + 1]) := by
      have h0_len : 0 < pairs.length := by omega
      have hhead_eq : pairs.head? = some (pairs[0]'h0_len) := by
        cases pairs with
        | nil => simp at h0_len
        | cons a _ => rfl
      rw [hhead_eq] at hhead
      exact (Option.some.inj hhead).symm.trans hpFirst_at
    have hpLast_eq : pLast = (path[idx rLast], path[idx rLast + 1]) := by
      rw [getLast?_eq_getElem?_pred pairs (by omega)] at hlast_opt
      have hlen1 : pairs.length - 1 = rLast.val := by dsimp [rLast]; omega
      rw [hlen1, List.getElem?_eq_getElem (by omega)] at hlast_opt
      exact (Option.some.inj hlast_opt).symm.trans hpLast_at
    let x0 := path[idx rFirst]
    let yLast := path[idx rLast + 1]
    have hx0_pFirst : pFirst.1 = x0 := by rw [hpFirst_eq]
    have hyLast_pLast : pLast.2 = yLast := by rw [hpLast_eq]
    rw [hx0_pFirst] at hx0_mem
    rw [hyLast_pLast] at hyLast_mem
    simp only [IntervalBlock.toFinset, Finset.mem_Icc] at hx0_mem hyLast_mem
    have hx0_S0 : x0 ∈ S0 := mem_of_mem_leftSpine S0
      (List.getElem_mem (by change idx rFirst + 1 < (leftSpine S0).length at hjFirst; omega))
    have hyLast_S0 : yLast ∈ S0 := mem_of_mem_leftSpine S0 (List.getElem_mem hjLast)
    -- Every ancestor of `top` in `B` is either `< x0` or `> yLast`
    have hanc_top_out : ∀ a ∈ searchAncestors B top, a < x0 ∨ yLast < a := by
      intro a ha
      rcases searchAncestors_top_outside B hB htop ha with hlt_all | hgt_all
      · exact Or.inr (hlt_all yLast hyLast_S0)
      · exact Or.inl (hgt_all x0 hx0_S0)
    -- Extract the given intra-block pair `p ∈ pairs` and its block `C ∈ blocks`
    rcases hintra with ⟨pIntra, hpIntra_mem, CIntra, hCIntra_mem, hp1_C, hp2_C⟩
    obtain ⟨i0, hi0_len, rfl⟩ := List.getElem_of_mem hpIntra_mem
    obtain ⟨q0_idx, hq0_len, rfl⟩ := List.getElem_of_mem hCIntra_mem
    let r0 : Fin k := ⟨i0, by omega⟩
    let q0 : Fin blocks.length := ⟨q0_idx, hq0_len⟩
    obtain ⟨hjr0, hpr0_at⟩ := hpair_at r0
    have hidx_0_le_r0 : idx rFirst ≤ idx r0 := by
      by_cases hpos : 0 < r0.val
      · have := idx_mono_of_gaps idx hgaps rFirst r0 hpos
        omega
      · have heq : r0 = rFirst := Fin.ext (by dsimp [rFirst]; omega)
        rw [heq]
    have hx0_le_xr0 : x0 ≤ (pairs[r0.val]'hi0_len).1 := by
      have hx_eq : (pairs[r0.val]'hi0_len).1 = path[idx r0] := by rw [hpr0_at]
      rw [hx_eq]
      rcases Nat.eq_or_lt_of_le hidx_0_le_r0 with heq_idx | hlt_idx
      · exact getElem_le_of_idx_eq path _ _ heq_idx
      · exact le_of_lt (List.pairwise_iff_getElem.mp hpath_lt (idx rFirst) (idx r0)
          (by omega) (by omega) hlt_idx)
    simp only [IntervalBlock.toFinset, Finset.mem_Icc] at hp1_C hp2_C
    -- Cannot have `q0 < qMin` because `x0 ≤ pairs[r0].1 ≤ blocks[q0].hi`
    have hqMin_le_q0 : qMin ≤ q0 := by
      by_contra hnot
      have hlt_q : q0 < qMin := not_le.mp hnot
      have hhi_lt_lo : blocks[q0_idx].hi < blocks[qMin].lo :=
        blocks_hi_lt_lo_of_lt hPart q0 qMin hlt_q
      have hx0_le_i0 : x0 ≤ (pairs[i0]'hi0_len).1 := hx0_le_xr0
      omega
    -- Split into Case 1 (`qMin < q0`, Trigger 1) and Case 2 (`q0 = qMin`, Trigger 2)
    rcases lt_or_eq_of_le hqMin_le_q0 with hqMin_lt_q0 | hq0_eq
    · -- CASE 1 (Trigger 1): `qMin < q0`, so `x0 ≤ blocks[qMin].hi < blocks[q0].lo`
      refine ⟨r0, q0, ?_⟩
      have hx0_lt_lo : x0 < blocks[q0].lo := by
        have hhi_lt := blocks_hi_lt_lo_of_lt hPart qMin q0 hqMin_lt_q0
        omega
      obtain ⟨hBr0, hkBr0, _⟩ := execPrefix_cascade_valid B hB hcasc r0.val (by omega)
      rw [hkB] at hkBr0
      obtain ⟨hxy_r0, hedge_r0⟩ := execPrefix_step_edge B hB hcasc r0.val r0.isLt
      have hr0_len : r0.val < pairs.length := by omega
      rw [execPrefix_succ B pairs r0.val hr0_len]
      have hC_valid := hPart.1 blocks[q0] (List.getElem_mem q0.isLt)
      have hin_q0 : (blocks[q0].lo ≤ (pairs[r0.val]).1 ∧ (pairs[r0.val]).1 ≤ blocks[q0].hi) ∧
          (blocks[q0].lo ≤ (pairs[r0.val]).2 ∧ (pairs[r0.val]).2 ≤ blocks[q0].hi) :=
        ⟨hp1_C, hp2_C⟩
      refine psiBlock_rotateRightEdge_drop_spine hBr0 hkBr0 hxy_r0 hedge_r0 hC_valid hin_q0 ?_
      obtain ⟨hyr0_mem, hanc_eq⟩ := hanc_step r0
      rw [mem_leftSpine_restrictTree_iff (execPrefix B pairs r0.val) hBr0 blocks[q0] hyr0_mem hp2_C,
        hanc_eq]
      have hyr0_path : (pairs[r0.val]).2 = path[idx r0 + 1] := by rw [hpr0_at]
      have hyr0_S0 : (pairs[r0.val]).2 ∈ S0 := by
        rw [hyr0_path]
        exact mem_of_mem_leftSpine S0 (List.getElem_mem hjr0)
      rw [searchAncestors_sub B hB htop hyr0_S0, hyr0_path,
        searchAncestors_leftSpine_getElem S0 hS0_bst (idx r0 + 1) hjr0]
      change ∀ a ∈ searchAncestors B top ++ (path.drop (idx r0 + 2)).reverse,
        ¬ (blocks[q0].lo ≤ a ∧ a < path[idx r0 + 1])
      have hyr0_le_yLast : path[idx r0 + 1] ≤ yLast := by
        by_cases hlt_last : r0.val < rLast.val
        · have hm := idx_mono_of_gaps idx hgaps r0 rLast hlt_last
          exact le_of_lt (List.pairwise_iff_getElem.mp hpath_lt (idx r0 + 1) (idx rLast + 1)
            hjr0 hjLast (by omega))
        · have heq_r : r0 = rLast := Fin.ext (by dsimp [rLast] at hlt_last ⊢; omega)
          exact getElem_le_of_idx_eq path _ _ (congrArg (fun r => idx r + 1) heq_r)
      intro a ha
      rw [List.mem_append, List.mem_reverse] at ha
      rcases ha with ha_top | ha_drop
      · rcases hanc_top_out a ha_top with ha_lt_x0 | ha_gt_yLast
        · omega
        · omega
      · obtain ⟨d, hd_len, rfl⟩ := List.getElem_of_mem ha_drop
        rw [List.length_drop] at hd_len
        rw [List.getElem_drop]
        have hgt_yr0 : path[idx r0 + 1] < path[idx r0 + 2 + d]'(by omega) :=
          List.pairwise_iff_getElem.mp hpath_lt (idx r0 + 1) (idx r0 + 2 + d)
            hjr0 (by omega) (by omega)
        omega
    · -- CASE 2 (Trigger 2): `qMin = q0`, find last `r*` with `y_{r*} ≤ blocks[qMin].hi`
      have hq_hi : blocks[qMin].hi = (blocks[q0_idx]'hq0_len).hi :=
        congrArg (fun q : Fin blocks.length => blocks[q].hi) hq0_eq
      have hyr0_le_hi : (pairs[r0.val]'hi0_len).2 ≤ blocks[qMin].hi := by
        rw [hq_hi]
        exact hp2_C.2
      have hhi_lt_yLast : blocks[qMin].hi < yLast := by
        have hhi_lt_lo := blocks_hi_lt_lo_of_lt hPart qMin qMax hq_lt
        omega
      have hyLast_pair : (pairs[rLast.val]'(by omega)).2 = yLast := by rw [hpLast_at]
      have hr0_lt_rLast : r0.val < rLast.val := by
        by_contra hnot
        have heq_r : r0 = rLast := Fin.ext (by dsimp [rLast] at hnot ⊢; omega)
        have h1 : (pairs[r0.val]'hi0_len).2 = yLast := by
          have h2 : (pairs[r0.val]'(by omega)).2 = (pairs[rLast.val]'(by omega)).2 :=
            congrArg (fun (r : Fin k) => (pairs[r.val]'(by omega)).2) heq_r
          exact h2.trans hyLast_pair
        omega
      let P : Fin k → Prop := fun r => (pairs[r.val]'(by omega)).2 ≤ blocks[qMin].hi
      obtain ⟨rStar, hrStar1, _, hP_star, hnP_next⟩ :=
        exists_adj_crossing P r0 rLast hr0_lt_rLast hyr0_le_hi
          (by change ¬ (pairs[rLast.val]'(by omega)).2 ≤ blocks[qMin].hi; rw [hyLast_pair]; omega)
      let rNext : Fin k := ⟨rStar.val + 1, hrStar1⟩
      refine ⟨rStar, qMin, ?_⟩
      obtain ⟨hjrStar, hprStar_at⟩ := hpair_at rStar
      obtain ⟨hjrNext, hprNext_at⟩ := hpair_at rNext
      have hg_star := hgaps rStar rNext rfl
      have hidx_0_le_star : idx rFirst ≤ idx rStar := by
        by_cases hpos : 0 < rStar.val
        · have := idx_mono_of_gaps idx hgaps rFirst rStar hpos
          omega
        · have heq : rStar = rFirst := Fin.ext (by dsimp [rFirst]; omega)
          rw [heq]
      have hx0_le_xStar : x0 ≤ path[idx rStar] := by
        rcases Nat.eq_or_lt_of_le hidx_0_le_star with heq_idx | hlt_idx
        · exact getElem_le_of_idx_eq path _ _ heq_idx
        · exact le_of_lt (List.pairwise_iff_getElem.mp hpath_lt (idx rFirst) (idx rStar)
            (by omega) (by omega) hlt_idx)
      have hxStar_lt_yStar : path[idx rStar] < path[idx rStar + 1] :=
        List.pairwise_iff_getElem.mp hpath_lt (idx rStar) (idx rStar + 1)
          (by omega) hjrStar (by omega)
      have hyStar_le_hi : path[idx rStar + 1] ≤ blocks[qMin].hi := by
        change (pairs[rStar.val]'(by omega)).2 ≤ blocks[qMin].hi at hP_star
        rwa [hprStar_at] at hP_star
      have hhi_lt_yNext : blocks[qMin].hi < path[idx rNext + 1] := by
        change ¬ (pairs[rNext.val]'(by omega)).2 ≤ blocks[qMin].hi at hnP_next
        rw [hprNext_at] at hnP_next
        omega
      obtain ⟨hBStar, hkBStar, _⟩ := execPrefix_cascade_valid B hB hcasc rStar.val (by omega)
      rw [hkB] at hkBStar
      obtain ⟨hxy_star, hedge_star⟩ := execPrefix_step_edge B hB hcasc rStar.val rStar.isLt
      have hrStar_len : rStar.val < pairs.length := by omega
      rw [execPrefix_succ B pairs rStar.val hrStar_len]
      have hC0_valid := hPart.1 blocks[qMin] (List.getElem_mem qMin.isLt)
      have hin_C0 : (blocks[qMin].lo ≤ (pairs[rStar.val]).1 ∧ (pairs[rStar.val]).1 ≤ blocks[qMin].hi) ∧
          (blocks[qMin].lo ≤ (pairs[rStar.val]).2 ∧ (pairs[rStar.val]).2 ≤ blocks[qMin].hi) := by
        have hx_eq : (pairs[rStar.val]).1 = path[idx rStar] := by rw [hprStar_at]
        have hy_eq : (pairs[rStar.val]).2 = path[idx rStar + 1] := by rw [hprStar_at]
        rw [hx_eq, hy_eq]
        omega
      refine psiBlock_rotateRightEdge_drop_ld hBStar hkBStar hxy_star hedge_star
        hC0_valid hin_C0 ?_
      obtain ⟨hyStar_mem, hanc_eq⟩ := hanc_step rStar
      rw [leftDepth_restrictTree_eq (execPrefix B pairs rStar.val) hBStar blocks[qMin]
        hyStar_mem hin_C0.2, hanc_eq]
      have hyStar_eq : (pairs[rStar.val]).2 = path[idx rStar + 1] := by rw [hprStar_at]
      have hyStar_S0 : (pairs[rStar.val]).2 ∈ S0 := by
        rw [hyStar_eq]
        exact mem_of_mem_leftSpine S0 (List.getElem_mem hjrStar)
      rw [searchAncestors_sub B hB htop hyStar_S0, hyStar_eq,
        searchAncestors_leftSpine_getElem S0 hS0_bst (idx rStar + 1) hjrStar]
      -- Split `path.drop (idx rStar + 2)` into `near` (length `≤ Δ' + 1`) and `far` (`≥ yNext > blocks[qMin].hi`)
      let L := (idx rNext + 1) - (idx rStar + 2)
      let pred : ℕ → Bool := fun a => decide (path[idx rStar + 1] < a ∧ a ≤ blocks[qMin].hi)
      change ((searchAncestors B top ++ (path.drop (idx rStar + 2)).reverse).filter pred).length < D
      have htop_filter_nil : (searchAncestors B top).filter pred = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        simp only [pred, decide_eq_true_eq]
        rcases hanc_top_out a ha with ha_lt | ha_gt
        · omega
        · omega
      have hdrop_split : path.drop (idx rStar + 2) =
          (path.drop (idx rStar + 2)).take L ++ path.drop (idx rNext + 1) := by
        conv_lhs => rw [← List.take_append_drop L (path.drop (idx rStar + 2))]
        rw [List.drop_drop]
        have heq_idx : idx rStar + 2 + L = idx rNext + 1 := by dsimp [L]; omega
        rw [heq_idx]
      have hfar_filter_nil : ((path.drop (idx rNext + 1)).reverse).filter pred = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        rw [List.mem_reverse] at ha
        obtain ⟨d, hd_len, rfl⟩ := List.getElem_of_mem ha
        rw [List.length_drop] at hd_len
        rw [List.getElem_drop]
        have hyNext_le : path[idx rNext + 1] ≤ path[idx rNext + 1 + d]'(by omega) := by
          rcases Nat.eq_zero_or_pos d with rfl | hd_pos
          · simp
          · exact le_of_lt (List.pairwise_iff_getElem.mp hpath_lt (idx rNext + 1)
              (idx rNext + 1 + d) hjrNext (by omega) (by omega))
        simp only [pred, decide_eq_true_eq]
        omega
      rw [hdrop_split, List.reverse_append, List.filter_append, List.filter_append,
        htop_filter_nil, hfar_filter_nil, List.nil_append, List.nil_append]
      have hlen_filter : (((path.drop (idx rStar + 2)).take L).reverse.filter pred).length ≤
          (((path.drop (idx rStar + 2)).take L).reverse).length :=
        List.length_filter_le _ _
      have hlen_rev : (((path.drop (idx rStar + 2)).take L).reverse).length ≤ L := by
        rw [List.length_reverse, List.length_take]
        exact Nat.min_le_left _ _
      have hL_lt_D : L < D := by dsimp [L, D]; omega
      omega

/-- **Lemma 4.3** (`lem:cascade-potentials`, Untruncated and Truncated Left-Depth Potentials):
(1) `Φ_ld(T) ≤ C(|V(T)|, 2)` drops by at least `1` per single right rotation and by at least `k`
per simultaneous right `k`-cascade;
(2) For `D = Δ' + 2`, `Ψ_C(B) ≤ (D + 1)|C|` is non-increasing under right rotations, and any
block-crossing `Δ'`-gapped right `k`-cascade (`k ≥ 2`) with at least one intra-block edge drops
`∑_q Ψ_{C_q}(B)` by at least `1`. -/
theorem lem_4_3_cascade_potentials :
    -- Part (1)
    (∀ {α : Type} [LinearOrder α] (T : BinaryTree α), T.IsBST →
      phiLeftDepth T ≤ Nat.choose T.num_nodes 2 ∧
      (∀ x y : α, x < y → IsRightRotEdge T x y →
        phiLeftDepth (rotateRightEdge T x y) + 1 ≤ phiLeftDepth T) ∧
      (∀ (Δ' k : ℕ) (pairs : List (α × α)), IsGappedRightCascade T Δ' k pairs →
        phiLeftDepth (execRightCascadeBatch T pairs) + k ≤ phiLeftDepth T)) ∧
    -- Part (2)
    (∀ (N Δ' : ℕ), 1 ≤ N →
      let D := Δ' + 2
      ∀ (B : BinaryTree ℕ) (blocks : List IntervalBlock),
        B.IsBST → keyFinset B = Finset.Icc 1 N →
        IsContiguousBlockPartition N blocks →
        (∀ C ∈ blocks, psiBlock C D B ≤ (D + 1) * C.size) ∧
        (∀ u v : ℕ, u < v → IsRightRotEdge B u v →
          ∀ C ∈ blocks, psiBlock C D (rotateRightEdge B u v) ≤ psiBlock C D B) ∧
        (∀ (k : ℕ) (pairs : List (ℕ × ℕ)),
          2 ≤ k → IsGappedRightCascade B Δ' k pairs →
          (∃ (pFirst pLast : ℕ × ℕ) (qMin qMax : Fin blocks.length),
            pairs.head? = some pFirst ∧ pairs.getLast? = some pLast ∧
            qMin < qMax ∧
            pFirst.1 ∈ blocks[qMin].toFinset ∧ pLast.2 ∈ blocks[qMax].toFinset) →
          (∃ p ∈ pairs, ∃ C ∈ blocks, p.1 ∈ C.toFinset ∧ p.2 ∈ C.toFinset) →
          (blocks.map (fun C => psiBlock C D (execRightCascadeBatch B pairs))).sum + 1 ≤
            (blocks.map (fun C => psiBlock C D B)).sum)) :=
  ⟨fun T hT => lem_4_3_part1 T hT, lem_4_3_part2⟩

/-! ## 4. Bridge to `SplayDeque.Direct.gapped_right_cascade_bound` & Proof of Theorem 2.3 -/

private def posOfKey [LinearOrder α] : BinaryTree α → α → List Dir
  | .nil, _ => []
  | .node k l r, v =>
    if v < k then .L :: posOfKey l v
    else if k < v then .R :: posOfKey r v
    else []

private theorem subtreeAtPosGen_posOfKey [LinearOrder α] (B : BinaryTree α) (v : α) :
    SplayDeque.Direct.subtreeAtPosGen B (posOfKey B v) = subtreeAtKey B v := by
  induction B with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [posOfKey, subtreeAtKey]
    split_ifs <;> simp [SplayDeque.Direct.subtreeAtPosGen, ihl, ihr]

private theorem eraseKeys_num_nodes (B : BinaryTree α) :
    (SplayDeque.Direct.eraseKeys B).num_nodes = B.num_nodes := by
  induction B with
  | nil => rfl
  | node _ l r ihl ihr =>
    simp [SplayDeque.Direct.eraseKeys, BinaryTree.num_nodes, ihl, ihr]

private theorem eraseKeys_subtreeAtPosGen (B : BinaryTree α) (pos : List Dir) :
    SplayDeque.Direct.subtreeAtPos (SplayDeque.Direct.eraseKeys B) pos =
      SplayDeque.Direct.eraseKeys (SplayDeque.Direct.subtreeAtPosGen B pos) := by
  induction pos generalizing B with
  | nil => cases B <;> rfl
  | cons d rest ih =>
    cases B with
    | nil => cases d <;> rfl
    | node k l r =>
      cases d <;> exact ih _

private theorem eraseKeys_applyAtPosGen (B : BinaryTree α) (pos : List Dir)
    (fA : BinaryTree α → BinaryTree α)
    (fU : BinaryTree Unit → BinaryTree Unit)
    (hf : ∀ s, SplayDeque.Direct.eraseKeys (fA s) = fU (SplayDeque.Direct.eraseKeys s)) :
    SplayDeque.Direct.eraseKeys (SplayDeque.Direct.applyAtPosGen fA B pos) =
      SplayDeque.Direct.applyAtPos fU (SplayDeque.Direct.eraseKeys B) pos := by
  induction pos generalizing B with
  | nil => cases B <;> exact hf _
  | cons d rest ih =>
    cases B with
    | nil => cases d <;> rfl
    | node k l r =>
      cases d <;> simp [SplayDeque.Direct.applyAtPosGen, SplayDeque.Direct.applyAtPos,
        SplayDeque.Direct.eraseKeys, ih _]

private theorem eraseKeys_applyAtLeftDepthGen (B : BinaryTree α) (g : ℕ)
    (fA : BinaryTree α → BinaryTree α)
    (fU : BinaryTree Unit → BinaryTree Unit)
    (hf : ∀ s, SplayDeque.Direct.eraseKeys (fA s) = fU (SplayDeque.Direct.eraseKeys s)) :
    SplayDeque.Direct.eraseKeys (SplayDeque.Direct.applyAtLeftDepthGen fA B g) =
      SplayDeque.Direct.applyAtLeftDepth fU (SplayDeque.Direct.eraseKeys B) g := by
  induction g generalizing B with
  | zero => cases B <;> exact hf _
  | succ g ih =>
    cases B with
    | nil => rfl
    | node k l r =>
      simp [SplayDeque.Direct.applyAtLeftDepthGen, SplayDeque.Direct.applyAtLeftDepth,
        SplayDeque.Direct.eraseKeys, ih l]

private theorem eraseKeys_rotateRight (B : BinaryTree α) :
    SplayDeque.Direct.eraseKeys B.rotateRight =
      (SplayDeque.Direct.eraseKeys B).rotateRight := by
  rcases B with _ | ⟨y, _ | ⟨x, a, b⟩, c⟩ <;> rfl

private theorem eraseKeys_execGappedCascadeAtRootGen (gaps : List ℕ) (B : BinaryTree α) :
    SplayDeque.Direct.eraseKeys (SplayDeque.Direct.execGappedCascadeAtRootGen B gaps) =
      SplayDeque.Direct.execGappedCascadeAtRoot (SplayDeque.Direct.eraseKeys B) gaps := by
  induction gaps generalizing B with
  | nil => exact eraseKeys_rotateRight B
  | cons g rest ih =>
    rcases B with _ | ⟨y, _ | ⟨x, a, b⟩, c⟩
    · rfl
    · rfl
    · simp only [SplayDeque.Direct.execGappedCascadeAtRootGen,
        SplayDeque.Direct.execGappedCascadeAtRoot, SplayDeque.Direct.eraseKeys]
      rw [eraseKeys_applyAtLeftDepthGen a g
        (fun s => SplayDeque.Direct.execGappedCascadeAtRootGen s rest)
        (fun s => SplayDeque.Direct.execGappedCascadeAtRoot s rest)
        (fun s => ih s)]

private theorem foldl_rotateRightEdge_left [LinearOrder α] (k0 : α)
    (L R : BinaryTree α) (ps : List (α × α)) (hlt : ∀ p ∈ ps, p.2 < k0) :
    ps.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (.node k0 L R) =
      .node k0 (ps.foldl (fun acc p => rotateRightEdge acc p.1 p.2) L) R := by
  induction ps generalizing L with
  | nil => rfl
  | cons p rest ih =>
    have hp : p.2 < k0 := hlt p List.mem_cons_self
    simp only [List.foldl_cons, rotateRightEdge, hp, ↓reduceIte]
    exact ih _ (fun q hq => hlt q (List.mem_cons_of_mem p hq))

private theorem foldl_rotateRightEdge_right [LinearOrder α] (k0 : α)
    (L R : BinaryTree α) (ps : List (α × α)) (hgt : ∀ p ∈ ps, k0 < p.2) :
    ps.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (.node k0 L R) =
      .node k0 L (ps.foldl (fun acc p => rotateRightEdge acc p.1 p.2) R) := by
  induction ps generalizing R with
  | nil => rfl
  | cons p rest ih =>
    have hp : k0 < p.2 := hgt p List.mem_cons_self
    have hnp : ¬ p.2 < k0 := not_lt_of_gt hp
    simp only [List.foldl_cons, rotateRightEdge, hnp, hp, ↓reduceIte]
    exact ih _ (fun q hq => hgt q (List.mem_cons_of_mem p hq))

private theorem foldl_rotateRightEdge_posOfKey [LinearOrder α] (B : BinaryTree α)
    (hB : B.IsBST) (yTop : α) (ps : List (α × α))
    (hmem : ∀ p ∈ ps, p.2 ∈ subtreeAtKey B yTop) :
    ps.foldl (fun acc p => rotateRightEdge acc p.1 p.2) B =
      SplayDeque.Direct.applyAtPosGen
        (fun s => ps.foldl (fun acc p => rotateRightEdge acc p.1 p.2) s)
        B (posOfKey B yTop) := by
  induction B with
  | nil =>
    cases ps with
    | nil => rfl
    | cons p _ =>
      have := hmem p List.mem_cons_self
      simp [subtreeAtKey] at this
  | node k0 L R ihL ihR =>
    by_cases hy : yTop < k0
    · simp only [subtreeAtKey, hy, ↓reduceIte] at hmem
      have hlt : ∀ p ∈ ps, p.2 < k0 := fun p hp =>
        bst_lt_left hB (mem_of_mem_subtreeAtKey L (hmem p hp))
      simp only [posOfKey, hy, ↓reduceIte, SplayDeque.Direct.applyAtPosGen]
      rw [foldl_rotateRightEdge_left k0 L R ps hlt, ihL (bst_left hB) hmem]
    · by_cases hky : k0 < yTop
      · simp only [subtreeAtKey, hy, hky, ↓reduceIte] at hmem
        have hgt : ∀ p ∈ ps, k0 < p.2 := fun p hp =>
          bst_gt_right hB (mem_of_mem_subtreeAtKey R (hmem p hp))
        simp only [posOfKey, hy, hky, ↓reduceIte, SplayDeque.Direct.applyAtPosGen]
        rw [foldl_rotateRightEdge_right k0 L R ps hgt, ihR (bst_right hB) hmem]
      · simp only [posOfKey, hy, hky, ↓reduceIte]
        rfl

private theorem mem_of_mem_subtreeAtLeftDepthGen (t : BinaryTree α) (g : ℕ) {w : α}
    (hw : w ∈ SplayDeque.Direct.subtreeAtLeftDepthGen t g) : w ∈ t := by
  induction g generalizing t with
  | zero => cases t <;> exact hw
  | succ g ih =>
    cases t with
    | nil => simp [SplayDeque.Direct.subtreeAtLeftDepthGen] at hw
    | node k l r =>
      exact BinaryTree.mem_node_iff.mpr (Or.inr (Or.inl (ih l hw)))

private theorem subtreeAtLeftDepthGen_isBST [LinearOrder α] (t : BinaryTree α)
    (ht : t.IsBST) (g : ℕ) : (SplayDeque.Direct.subtreeAtLeftDepthGen t g).IsBST := by
  induction g generalizing t with
  | zero => cases t <;> exact ht
  | succ g ih =>
    cases t with
    | nil => exact SplayDeque.Direct.isBSTNil
    | node k l r => exact ih l (bst_left ht)

private theorem leftSpine_subtreeAtLeftDepthGen (t : BinaryTree α) (g : ℕ)
    (hg : g ≤ (leftSpine t).length) :
    leftSpine (SplayDeque.Direct.subtreeAtLeftDepthGen t g) =
      (leftSpine t).take ((leftSpine t).length - g) := by
  induction g generalizing t with
  | zero => cases t <;> simp [SplayDeque.Direct.subtreeAtLeftDepthGen]
  | succ g ih =>
    cases t with
    | nil => simp [leftSpine] at hg
    | node k l r =>
      simp only [leftSpine, List.length_append, List.length_singleton] at hg ⊢
      have hg' : g ≤ (leftSpine l).length := by omega
      simp only [SplayDeque.Direct.subtreeAtLeftDepthGen, ih l hg']
      have heq : (leftSpine l).length + 1 - (g + 1) = (leftSpine l).length - g := by omega
      rw [heq, List.take_append_of_le_length (by omega)]

private theorem foldl_rotateRightEdge_leftDepth [LinearOrder α] (A : BinaryTree α)
    (hA : A.IsBST) (g : ℕ) (ps : List (α × α))
    (hmem : ∀ p ∈ ps, p.2 ∈ SplayDeque.Direct.subtreeAtLeftDepthGen A g) :
    ps.foldl (fun acc p => rotateRightEdge acc p.1 p.2) A =
      SplayDeque.Direct.applyAtLeftDepthGen
        (fun s => ps.foldl (fun acc p => rotateRightEdge acc p.1 p.2) s) A g := by
  induction g generalizing A with
  | zero => cases A <;> rfl
  | succ g ih =>
    cases A with
    | nil =>
      cases ps with
      | nil => rfl
      | cons p _ =>
        have := hmem p List.mem_cons_self
        simp [SplayDeque.Direct.subtreeAtLeftDepthGen] at this
    | node k0 L R =>
      simp only [SplayDeque.Direct.subtreeAtLeftDepthGen] at hmem
      have hlt : ∀ p ∈ ps, p.2 < k0 := fun p hp =>
        bst_lt_left hA (mem_of_mem_subtreeAtLeftDepthGen L g (hmem p hp))
      simp only [SplayDeque.Direct.applyAtLeftDepthGen]
      rw [foldl_rotateRightEdge_left k0 L R ps hlt, ih L (bst_left hA) hmem]

private theorem applyAtLeftDepthGen_congr_on_subtree (f₁ f₂ : BinaryTree α → BinaryTree α)
    (g : ℕ) (A : BinaryTree α)
    (h : f₁ (SplayDeque.Direct.subtreeAtLeftDepthGen A g) =
      f₂ (SplayDeque.Direct.subtreeAtLeftDepthGen A g)) :
    SplayDeque.Direct.applyAtLeftDepthGen f₁ A g =
      SplayDeque.Direct.applyAtLeftDepthGen f₂ A g := by
  induction g generalizing A with
  | zero =>
    cases A <;> exact h
  | succ g ih =>
    cases A with
    | nil => rfl
    | node k0 l0 r0 =>
      simp only [SplayDeque.Direct.applyAtLeftDepthGen]
      rw [ih l0 h]

private theorem applyAtPosGen_congr_on_subtree (f₁ f₂ : BinaryTree α → BinaryTree α)
    (pos : List Dir) (B : BinaryTree α)
    (h : f₁ (SplayDeque.Direct.subtreeAtPosGen B pos) =
      f₂ (SplayDeque.Direct.subtreeAtPosGen B pos)) :
    SplayDeque.Direct.applyAtPosGen f₁ B pos =
      SplayDeque.Direct.applyAtPosGen f₂ B pos := by
  induction pos generalizing B with
  | nil =>
    cases B <;> exact h
  | cons d rest ih =>
    cases B with
    | nil => cases d <;> rfl
    | node _ l r =>
      cases d <;> simp only [SplayDeque.Direct.applyAtPosGen,
        SplayDeque.Direct.subtreeAtPosGen] at h ⊢ <;> rw [ih _ h]

private theorem cascade_root_to_gaps [LinearOrder α] (Δ' m : ℕ) (S : BinaryTree α)
    (hS : S.IsBST) (pairs : List (α × α)) (idx : Fin (m + 1) → ℕ)
    (hlen : pairs.length = m + 1)
    (htop_idx : (leftSpine S).length = idx ⟨m, Nat.lt_succ_self m⟩ + 2)
    (hpairs : ∀ r : Fin (m + 1), ∃ h : idx r + 1 < (leftSpine S).length,
      pairs[r.val]? = some ((leftSpine S)[idx r], (leftSpine S)[idx r + 1]))
    (hgaps : ∀ r₁ r₂ : Fin (m + 1), r₁.val + 1 = r₂.val →
      idx r₁ + 2 ≤ idx r₂ ∧ idx r₂ ≤ idx r₁ + Δ' + 2) :
    ∃ gaps : List ℕ,
      gaps.length = m ∧
      SplayDeque.Direct.validGappedCascadeAtRoot Δ' (SplayDeque.Direct.eraseKeys S) gaps ∧
      pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) S =
        SplayDeque.Direct.execGappedCascadeAtRootGen S gaps := by
  induction m generalizing S pairs with
  | zero =>
    let r0 : Fin 1 := ⟨0, Nat.lt_succ_self 0⟩
    rcases S with _ | ⟨y, _ | ⟨x, A, B⟩, C⟩
    · simp [leftSpine] at htop_idx
    · simp [leftSpine] at htop_idx
    · have hidx0 : idx r0 = (leftSpine A).length := by
        change (leftSpine (.node y (.node x A B) C)).length = idx r0 + 2 at htop_idx
        simp [leftSpine] at htop_idx; omega
      obtain ⟨_, hp0⟩ := hpairs r0
      rcases pairs with _ | ⟨p0, _ | _⟩
      · simp at hlen
      · simp only [r0, List.getElem?_cons_zero, Option.some.injEq] at hp0
        have hx_eq : (leftSpine (.node y (.node x A B) C))[idx r0]'(by simp [leftSpine, hidx0]) = x := by
          simp [leftSpine, hidx0]
        have hy_eq : (leftSpine (.node y (.node x A B) C))[idx r0 + 1]'(by simp [leftSpine, hidx0]) = y := by
          simp [leftSpine, hidx0]
        have hp0_eq : p0 = (x, y) := by
          rw [hp0]
          exact Prod.ext hx_eq hy_eq
        subst hp0_eq
        refine ⟨[], rfl, ?_, ?_⟩
        · simp only [SplayDeque.Direct.validGappedCascadeAtRoot, SplayDeque.Direct.eraseKeys,
            SplayDeque.Direct.leftSpineLen]
          omega
        · simp [rotateRightEdge, SplayDeque.Direct.execGappedCascadeAtRootGen,
            BinaryTree.rotateRight]
      · simp at hlen
  | succ m' ih =>
    let rLast : Fin (m' + 2) := ⟨m' + 1, Nat.lt_succ_self _⟩
    let rPrev : Fin (m' + 2) := ⟨m', by omega⟩
    have hg_step := hgaps rPrev rLast rfl
    rcases S with _ | ⟨yTop, _ | ⟨xTop, A, B⟩, C⟩
    · simp [leftSpine] at htop_idx
    · simp [leftSpine] at htop_idx
    · have hlen_A : (leftSpine A).length = idx rLast := by
        change (leftSpine (.node yTop (.node xTop A B) C)).length = idx rLast + 2 at htop_idx
        simp [leftSpine] at htop_idx; omega
      set g := idx rLast - (idx rPrev + 2)
      have hg_le : g ≤ Δ' := by omega
      have hg_len : g ≤ (leftSpine A).length := by omega
      set S' := SplayDeque.Direct.subtreeAtLeftDepthGen A g
      have hS'_bst : S'.IsBST := subtreeAtLeftDepthGen_isBST A (bst_left (bst_left hS)) g
      have hsp_S' : leftSpine S' = (leftSpine A).take (idx rPrev + 2) := by
        rw [leftSpine_subtreeAtLeftDepthGen A g hg_len]
        congr 1; omega
      have hlen_S' : (leftSpine S').length = idx rPrev + 2 := by
        rw [hsp_S', List.length_take]; omega
      have hpairs_split : pairs = pairs.take (m' + 1) ++ [(xTop, yTop)] := by
        obtain ⟨_, hlast_p⟩ := hpairs rLast
        have hx_eq : (leftSpine (.node yTop (.node xTop A B) C))[idx rLast]'(by simp [leftSpine, hlen_A]) = xTop := by
          simp [leftSpine, hlen_A]
        have hy_eq : (leftSpine (.node yTop (.node xTop A B) C))[idx rLast + 1]'(by simp [leftSpine, hlen_A]) = yTop := by
          simp [leftSpine, hlen_A]
        have hget : pairs[m' + 1]'(by omega) = (xTop, yTop) := by
          change pairs[m' + 1]? = _ at hlast_p
          rw [List.getElem?_eq_getElem (by omega)] at hlast_p
          have hpair := Option.some.inj hlast_p
          rw [hpair]
          exact Prod.ext hx_eq hy_eq
        have hdrop : pairs.drop (m' + 1) = [(xTop, yTop)] := by
          rw [← List.cons_getElem_drop_succ (h := by omega), hget]
          have : pairs.drop (m' + 2) = [] := List.drop_eq_nil_of_le (by omega)
          rw [this]
        conv_lhs => rw [← List.take_append_drop (m' + 1) pairs, hdrop]
      set lowerPairs := pairs.take (m' + 1)
      have hlower_len : lowerPairs.length = m' + 1 := by simp [lowerPairs]; omega
      let idx' : Fin (m' + 1) → ℕ := fun r => idx r.castSucc
      have hpairs' : ∀ r : Fin (m' + 1), ∃ h : idx' r + 1 < (leftSpine S').length,
          lowerPairs[r.val]? = some ((leftSpine S')[idx' r], (leftSpine S')[idx' r + 1]) := by
        intro r
        have hidx'_def : idx' r = idx r.castSucc := rfl
        have hr_le : idx' r ≤ idx rPrev := by
          by_cases hlt : r.val < m'
          · have hm := idx_mono_of_gaps idx hgaps r.castSucc rPrev hlt
            omega
          · have heq : r.castSucc = rPrev := Fin.ext (by simp [rPrev]; omega)
            rw [hidx'_def, heq]
        have hlt_S' : idx' r + 1 < (leftSpine S').length := by rw [hlen_S']; omega
        refine ⟨hlt_S', ?_⟩
        obtain ⟨_, hpr⟩ := hpairs r.castSucc
        have htake_get : lowerPairs[r.val]? = pairs[r.val]? := by
          rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
          simp [lowerPairs]
        rw [htake_get]
        simp only [Fin.val_castSucc] at hpr
        rw [hpr]
        congr 1
        have h1 : (leftSpine S')[idx' r] = (leftSpine (.node yTop (.node xTop A B) C))[idx' r] := by
          simp only [hsp_S', List.getElem_take]
          simp [leftSpine, List.getElem_append_left (by omega : idx' r < (leftSpine A).length)]
        have h2 : (leftSpine S')[idx' r + 1] =
            (leftSpine (.node yTop (.node xTop A B) C))[idx' r + 1] := by
          simp only [hsp_S', List.getElem_take]
          simp [leftSpine, List.getElem_append_left (by omega : idx' r + 1 < (leftSpine A).length)]
        exact Prod.ext h1.symm h2.symm
      have hgaps' : ∀ r₁ r₂ : Fin (m' + 1), r₁.val + 1 = r₂.val →
          idx' r₁ + 2 ≤ idx' r₂ ∧ idx' r₂ ≤ idx' r₁ + Δ' + 2 := by
        intro r₁ r₂ hr12
        exact hgaps r₁.castSucc r₂.castSucc hr12
      obtain ⟨restGaps, hrg_len, hrg_val, hrg_exec⟩ :=
        ih S' hS'_bst lowerPairs idx' hlower_len hlen_S' hpairs' hgaps'
      refine ⟨g :: restGaps, by simp [hrg_len], ?_, ?_⟩
      · simp only [SplayDeque.Direct.eraseKeys, SplayDeque.Direct.validGappedCascadeAtRoot]
        refine ⟨hg_le, ?_⟩
        have hek_sub : SplayDeque.Direct.subtreeAtLeftDepth (SplayDeque.Direct.eraseKeys A) g =
            SplayDeque.Direct.eraseKeys S' := by
          dsimp [S']
          clear * -
          induction g generalizing A with
          | zero => cases A <;> rfl
          | succ g ih =>
            cases A with
            | nil => rfl
            | node _ l _ => exact ih l
        rw [hek_sub]
        exact hrg_val
      · rw [hpairs_split, List.foldl_append, List.foldl_cons, List.foldl_nil]
        have hmem_S' : ∀ p ∈ lowerPairs, p.2 ∈ S' := by
          intro p hp
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
          obtain ⟨hlt_i, hpi⟩ := hpairs' ⟨i, by omega⟩
          rw [List.getElem?_eq_getElem hi] at hpi
          injection hpi with hpi_eq
          rw [hpi_eq]
          exact mem_of_mem_leftSpine S' (List.getElem_mem hlt_i)
        have hmem_A : ∀ p ∈ lowerPairs, p.2 ∈ A := fun p hp =>
          mem_of_mem_subtreeAtLeftDepthGen A g (hmem_S' p hp)
        have hlt_xTop : ∀ p ∈ lowerPairs, p.2 < xTop := fun p hp =>
          bst_lt_left (bst_left hS) (hmem_A p hp)
        have hlt_yTop : ∀ p ∈ lowerPairs, p.2 < yTop := fun p hp =>
          lt_trans (hlt_xTop p hp)
            (bst_lt_left hS (BinaryTree.mem_node_iff.mpr (Or.inl rfl)))
        rw [foldl_rotateRightEdge_left yTop (.node xTop A B) C lowerPairs hlt_yTop,
          foldl_rotateRightEdge_left xTop A B lowerPairs hlt_xTop,
          foldl_rotateRightEdge_leftDepth A (bst_left (bst_left hS)) g lowerPairs hmem_S']
        have hfun_eq := applyAtLeftDepthGen_congr_on_subtree
          (fun s => lowerPairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) s)
          (fun s => SplayDeque.Direct.execGappedCascadeAtRootGen s restGaps)
          g A hrg_exec
        rw [hfun_eq]
        simp [rotateRightEdge, SplayDeque.Direct.execGappedCascadeAtRootGen]

private theorem cascadeBatch_spec [LinearOrder α] (B : BinaryTree α) (hB : B.IsBST)
    {Δ' k : ℕ} {pairs : List (α × α)} (hcasc : IsGappedRightCascade B Δ' k pairs) :
    (execRightCascadeBatch B pairs).IsBST ∧
    (execRightCascadeBatch B pairs).num_nodes = B.num_nodes := by
  induction k generalizing B pairs with
  | zero => exact absurd hcasc.1 (by omega)
  | succ k' ih =>
    rcases pairs with _ | ⟨p0, rest⟩
    · simp [IsGappedRightCascade] at hcasc
    · obtain ⟨hxy, hedge⟩ := cascade_head_edge hB hcasc
      obtain ⟨hB1, _, hn1⟩ := rotateRightEdge_spec B p0.1 p0.2 hB hxy hedge
      rcases Nat.eq_zero_or_pos k' with rfl | hk'_pos
      · have hrest_nil : rest = [] := by
          have hlen := hcasc.2.1
          cases rest <;> simp at hlen ⊢
        subst hrest_nil
        simpa [execRightCascadeBatch] using ⟨hB1, hn1⟩
      · obtain ⟨hBf, hnf⟩ := ih (rotateRightEdge B p0.1 p0.2) hB1 (cascade_peel_cons hB hk'_pos hcasc)
        unfold execRightCascadeBatch at hBf hnf ⊢
        simp only [List.foldl_cons]
        exact ⟨hBf, hnf.trans hn1⟩

private theorem traj_to_rightRotSeq [LinearOrder α] (Δ' k : ℕ)
    (B : BinaryTree α) (traj : List (RightCascadeTrajStep α))
    (hB : B.IsBST) (htraj : ValidRightCascadeTraj Δ' k B traj) :
    ∃ seq : List SplayDeque.Direct.RightRotOp,
      SplayDeque.Direct.ValidRightRotSeq Δ' k (SplayDeque.Direct.eraseKeys B) seq ∧
      SplayDeque.Direct.countGappedCascades seq = countCascadeBatches traj := by
  induction traj generalizing B with
  | nil => exact ⟨[], trivial, rfl⟩
  | cons step rest ih =>
    cases step with
    | singleRot x y =>
      rcases htraj with ⟨hxy, hedge, hrest⟩
      obtain ⟨hB', _, _⟩ := rotateRightEdge_spec B x y hB hxy hedge
      obtain ⟨seqRest, hvRest, hcRest⟩ := ih (rotateRightEdge B x y) hB' hrest
      let pos := posOfKey B y
      rcases hedge with ⟨A, M, R, _, hsub⟩
      have hval1 : SplayDeque.Direct.validRightRotOp Δ' k
          (SplayDeque.Direct.eraseKeys B) (.single pos) := by
        dsimp only [SplayDeque.Direct.validRightRotOp]
        rw [eraseKeys_subtreeAtPosGen, subtreeAtPosGen_posOfKey, hsub]
        simp only [SplayDeque.Direct.eraseKeys, SplayDeque.Direct.leftSpineLen]
        omega
      have hexec1 : SplayDeque.Direct.execRightRotOp (SplayDeque.Direct.eraseKeys B) (.single pos) =
          SplayDeque.Direct.eraseKeys (rotateRightEdge B x y) := by
        have hrot_pos : rotateRightEdge B x y =
            SplayDeque.Direct.applyAtPosGen BinaryTree.rotateRight B pos := by
          have hmem : ∀ p ∈ [(x, y)], p.2 ∈ subtreeAtKey B y := by
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            rw [hsub]
            exact BinaryTree.mem_node_iff.mpr (Or.inl rfl)
          have hf := foldl_rotateRightEdge_posOfKey B hB y [(x, y)] hmem
          simp only [List.foldl_cons, List.foldl_nil] at hf
          rw [hf]
          refine applyAtPosGen_congr_on_subtree _ _ pos B ?_
          rw [subtreeAtPosGen_posOfKey, hsub]
          simp [rotateRightEdge, BinaryTree.rotateRight]
        rw [hrot_pos, eraseKeys_applyAtPosGen B pos _ _ eraseKeys_rotateRight]
        rfl
      refine ⟨.single pos :: seqRest, ⟨hval1, ?_⟩, hcRest⟩
      rw [hexec1]
      exact hvRest
    | cascadeBatch pairs =>
      rcases htraj with ⟨hcasc, hrest⟩
      obtain ⟨hB', _⟩ := cascadeBatch_spec B hB hcasc
      obtain ⟨seqRest, hvRest, hcRest⟩ := ih (execRightCascadeBatch B pairs) hB' hrest
      have hk_pos : 1 ≤ k := hcasc.1
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rcases hcasc with ⟨_, hlen, top, _, idx, hpairs, hgaps⟩
      let rTop : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      obtain ⟨hjTop, _⟩ := hpairs rTop
      have hS0_bst : (subtreeAtKey B top).IsBST := subtreeAtKey_isBST B top hB
      let yTop := (leftSpine (subtreeAtKey B top))[idx rTop + 1]
      have hyTop_S0 : yTop ∈ subtreeAtKey B top :=
        mem_of_mem_leftSpine (subtreeAtKey B top) (List.getElem_mem hjTop)
      let S := subtreeAtKey B yTop
      have hS_eq : S = subtreeAtKey (subtreeAtKey B top) yTop := subtreeAtKey_trans B hB hyTop_S0
      have hS_bst : S.IsBST := subtreeAtKey_isBST B yTop hB
      have hsp_S : leftSpine S = (leftSpine (subtreeAtKey B top)).take (idx rTop + 2) := by
        rw [hS_eq]
        exact leftSpine_subtreeAtKey_of_mem_spine (subtreeAtKey B top) hS0_bst (idx rTop + 1) hjTop
      have hlen_S : (leftSpine S).length = idx rTop + 2 := by
        rw [hsp_S, List.length_take]; omega
      have hpairs_S : ∀ r : Fin (m + 1), ∃ h : idx r + 1 < (leftSpine S).length,
          pairs[r.val]? = some ((leftSpine S)[idx r], (leftSpine S)[idx r + 1]) := by
        intro r
        have hr_le : idx r ≤ idx rTop := by
          by_cases hlt : r.val < m
          · have hm := idx_mono_of_gaps idx hgaps r rTop hlt
            omega
          · have heq : r = rTop := Fin.ext (by simp [rTop]; omega)
            rw [heq]
        have hlt_S : idx r + 1 < (leftSpine S).length := by rw [hlen_S]; omega
        refine ⟨hlt_S, ?_⟩
        obtain ⟨_, hpr⟩ := hpairs r
        rw [hpr]
        congr 1
        have h1 : (leftSpine S)[idx r] = (leftSpine (subtreeAtKey B top))[idx r] := by
          simp [hsp_S]
        have h2 : (leftSpine S)[idx r + 1] = (leftSpine (subtreeAtKey B top))[idx r + 1] := by
          simp [hsp_S]
        exact Prod.ext h1.symm h2.symm
      obtain ⟨gaps, hg_len, hg_val, hg_exec⟩ :=
        cascade_root_to_gaps Δ' m S hS_bst pairs idx hlen hlen_S hpairs_S hgaps
      let pos := posOfKey B yTop
      have hval1 : SplayDeque.Direct.validRightRotOp Δ' (m + 1)
          (SplayDeque.Direct.eraseKeys B) (.cascade pos gaps) := by
        refine ⟨by omega, ?_⟩
        rw [eraseKeys_subtreeAtPosGen, subtreeAtPosGen_posOfKey]
        exact hg_val
      have hexec1 : SplayDeque.Direct.execRightRotOp (SplayDeque.Direct.eraseKeys B) (.cascade pos gaps) =
          SplayDeque.Direct.eraseKeys (execRightCascadeBatch B pairs) := by
        have hmem_S : ∀ p ∈ pairs, p.2 ∈ S := by
          intro p hp
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
          obtain ⟨hlt_i, hpi⟩ := hpairs_S ⟨i, by omega⟩
          rw [List.getElem?_eq_getElem hi] at hpi
          injection hpi with hpi_eq
          rw [hpi_eq]
          exact mem_of_mem_leftSpine S (List.getElem_mem hlt_i)
        have hbatch_pos : execRightCascadeBatch B pairs =
            SplayDeque.Direct.applyAtPosGen
              (fun s => SplayDeque.Direct.execGappedCascadeAtRootGen s gaps) B pos := by
          unfold execRightCascadeBatch
          rw [foldl_rotateRightEdge_posOfKey B hB yTop pairs hmem_S]
          refine applyAtPosGen_congr_on_subtree _ _ pos B ?_
          rw [subtreeAtPosGen_posOfKey]
          exact hg_exec
        rw [hbatch_pos, eraseKeys_applyAtPosGen B pos
          (fun s => SplayDeque.Direct.execGappedCascadeAtRootGen s gaps)
          (fun s => SplayDeque.Direct.execGappedCascadeAtRoot s gaps)
          (fun s => eraseKeys_execGappedCascadeAtRootGen gaps s)]
        rfl
      refine ⟨.cascade pos gaps :: seqRest, ⟨hval1, ?_⟩, ?_⟩
      · rw [hexec1]
        exact hvRest
      · simp [SplayDeque.Direct.countGappedCascades, countCascadeBatches, hcRest]

private theorem countCascadeBatches_eq_zero_of_le_two [LinearOrder α] (Δ' : ℕ)
    (B : BinaryTree α) (traj : List (RightCascadeTrajStep α))
    (hB : B.IsBST) (hn : B.num_nodes ≤ 2) (htraj : ValidRightCascadeTraj Δ' 2 B traj) :
    countCascadeBatches traj = 0 := by
  induction traj generalizing B with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | singleRot x y =>
      rcases htraj with ⟨hxy, hedge, hrest⟩
      obtain ⟨hB', _, hn'⟩ := rotateRightEdge_spec B x y hB hxy hedge
      exact ih (rotateRightEdge B x y) hB' (by omega) hrest
    | cascadeBatch pairs =>
      rcases htraj with ⟨hcasc, _⟩
      rcases hcasc with ⟨_, _, top, _, idx, hpairs, hgaps⟩
      have hg01 : idx ⟨0, by omega⟩ + 2 ≤ idx ⟨1, by omega⟩ := (hgaps ⟨0, by omega⟩ ⟨1, by omega⟩ rfl).1
      obtain ⟨hj1, _⟩ := hpairs ⟨1, by omega⟩
      have hlen_sp : (leftSpine (subtreeAtKey B top)).length ≤ (subtreeAtKey B top).num_nodes :=
        leftSpine_length_le_num_nodes _
      have hsub_le : (subtreeAtKey B top).num_nodes ≤ B.num_nodes := by
        clear * -
        induction B with
        | nil => simp [subtreeAtKey]
        | node k l r ihl ihr =>
          simp only [subtreeAtKey]
          split_ifs
          · have := ihl; simp only [BinaryTree.num_nodes]; omega
          · have := ihr; simp only [BinaryTree.num_nodes]; omega
          · exact le_rfl
      omega

/-- **Theorem 2.3** (`thm:mod2-cascade`, Bounded-Gap Right-Cascade Bound):
There exists an absolute constant `C_casc > 0` such that for all `i ≥ 1`, `Δ' ≥ 0`, and
`1 ≤ N ≤ A_i(1)`, every pure-right-rotation trajectory on an `N`-node BST executes at most
`C_casc (Δ' + 1) N` `Δ'`-gapped right `(2i)`-cascades. -/
theorem thm_2_3_mod2_cascade :
    ∃ C_casc : ℝ, IsCascadeBoundConst C_casc := by
  refine ⟨32, by norm_num, ?_⟩
  intro i Δ' N α _ B₀ traj hi hN hN_ack hB₀ hn₀ htraj
  by_cases hi2 : 2 ≤ i
  · obtain ⟨seq, hval, hcnt⟩ := traj_to_rightRotSeq Δ' (2 * i) B₀ traj hB₀ htraj
    have hn_ek : (SplayDeque.Direct.eraseKeys B₀).num_nodes = N := by
      rw [eraseKeys_num_nodes, hn₀]
    have hbound := SplayDeque.Direct.gapped_right_cascade_bound
      i Δ' N (SplayDeque.Direct.eraseKeys B₀) seq hi2 hN hN_ack hn_ek hval
    have hnat : countCascadeBatches traj ≤ 32 * (Δ' + 1) * N := by
      rw [← hcnt]
      have : 8 * (Δ' + 4) ≤ 32 * (Δ' + 1) := by omega
      exact le_trans hbound (Nat.mul_le_mul_right N this)
    exact_mod_cast hnat
  · have hi1 : i = 1 := by omega
    subst hi1
    have hack1 : ackermann 1 1 = 2 := rfl
    have hzero := countCascadeBatches_eq_zero_of_le_two Δ' B₀ traj hB₀ (by omega) htraj
    rw [hzero, Nat.cast_zero]
    positivity

end Solution.Cascades
