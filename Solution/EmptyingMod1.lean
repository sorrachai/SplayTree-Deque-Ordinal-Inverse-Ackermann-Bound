module

public import Challenge.Definitions
public import Solution.TreeFacts

/-!
# Section 2.4 & Theorem 2.2: Emptying One-Sided Simulation, Spine-Folding Bijection, and Section 2 Reduction

This module proves:
- `lem_2_7_emptying_sim` (`main_v2.tex` Lemma 2.7 + `eq:cpop-folded`):
  (1) reverse-spine initialization of any BST on `{1, ..., P}`,
  (2) emptying one-sided `POP` simulation of the left interval projection `U_t`, and
  (3) spine-folding bijection `spineFoldTree` / `spineUnfoldTree` and dynamic reduction from
      `OneSidedPopExec P` to `FoldedPopProcess P` with `C_POP(H) ≤ P + J(H̃)` and `K_L ≤ 2P - 2`.
- `thm_2_2_mod1_reduction` (`main_v2.tex` Theorem 2.2):
  reduction from any valid two-sided deque execution `(init, ops)` to folded `POP` processes
  `HL : FoldedPopProcess (popCount ops)` and `HR : FoldedPopProcess (ejectCount ops)` via
  order-dual tree mirroring (`OrderDual α`, `flipTree`, `x ↦ -x` on `ℝ`).
-/

@[expose] public section

namespace Solution.EmptyingMod1

open SplayTree

namespace SpineFoldInternal

open SplayTree BinaryTree

/-! ## 1. Foundational `toKeyList`, `keyFinset`, `minKey?`, and Spine Lemmas -/

lemma mem_keyFinset_iff [DecidableEq α] {t : BinaryTree α} {x : α} :
    x ∈ keyFinset t ↔ x ∈ t := by
  induction t with
  | nil => simp [keyFinset]
  | node k l r ihl ihr =>
    simp [keyFinset, BinaryTree.mem_node_iff, ihl, ihr]

lemma keyFinset_eq_toKeyList_toFinset [DecidableEq α] (t : BinaryTree α) :
    keyFinset t = t.toKeyList.toFinset := by
  ext x
  simp [mem_keyFinset_iff, BinaryTree.mem_iff_mem_toKeyList]

lemma minKey_eq_head_toKeyList (t : BinaryTree α) :
    t.minKey? = t.toKeyList.head? := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    cases l with
    | nil => simp [BinaryTree.minKey?, toKeyList]
    | node lk ll lr =>
      have hne : (BinaryTree.node lk ll lr).toKeyList ≠ [] := by simp [toKeyList]
      have hhead : ((BinaryTree.node lk ll lr).toKeyList ++ [k] ++ r.toKeyList).head? =
          (BinaryTree.node lk ll lr).toKeyList.head? := by
        rw [List.append_assoc, List.head?_append_of_ne_nil _ hne]
      rw [toKeyList_node, hhead, ← ihl]
      simp only [BinaryTree.minKey?]
      cases ll.minKey? <;> rfl

lemma rightSpine_length_le_num_nodes (t : BinaryTree α) :
    (rightSpine t).length ≤ t.num_nodes := by
  induction t with
  | nil => simp [rightSpine]
  | node k l r _ ihr =>
    simp only [rightSpine, List.length_cons, num_nodes_node]
    omega

lemma mem_of_mem_leftSpine {t : BinaryTree α} {x : α} (hx : x ∈ leftSpine t) : x ∈ t := by
  induction t with
  | nil => simp [leftSpine] at hx
  | node k l r ihl _ =>
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with hl | rfl
    · exact .left (ihl hl)
    · exact .here

lemma mem_of_mem_rightSpine {t : BinaryTree α} {x : α} (hx : x ∈ rightSpine t) : x ∈ t := by
  induction t with
  | nil => simp [rightSpine] at hx
  | node k l r _ ihr =>
    simp only [rightSpine, List.mem_cons] at hx
    rcases hx with rfl | hr
    · exact .here
    · exact .right (ihr hr)

lemma leftSpine_eq_nil_iff (t : BinaryTree α) : leftSpine t = [] ↔ t = .nil := by
  cases t <;> simp [leftSpine]

lemma rightSpine_eq_nil_iff (t : BinaryTree α) : rightSpine t = [] ↔ t = .nil := by
  cases t <;> simp [rightSpine]

lemma pairwise_leftSpine [LinearOrder α] {t : BinaryTree α} (hBST : t.IsBST) :
    (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    rw [leftSpine, List.pairwise_append]
    refine ⟨ihl (IsBST_left_of_IsBST hBST), List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    rcases List.mem_singleton.mp hy with rfl
    exact lt_of_IsBST_left l y r hBST (mem_of_mem_leftSpine hx)

lemma pairwise_rightSpine [LinearOrder α] {t : BinaryTree α} (hBST : t.IsBST) :
    (rightSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [rightSpine]
  | node k l r _ ihr =>
    simp only [rightSpine, List.pairwise_cons]
    exact ⟨fun x hx => gt_of_IsBST_right l k r hBST (mem_of_mem_rightSpine hx),
      ihr (IsBST_right_of_IsBST hBST)⟩

/-! ## 2. Part 1: Reverse-Spine Initialization (`lem_3_5_part1`) -/

lemma validOneSidedOps_append (P : ℕ) (t : BinaryTree ℕ) (s1 s2 : List OneSidedOp) :
    ValidOneSidedOps P t (s1 ++ s2) ↔
      ValidOneSidedOps P t s1 ∧ ValidOneSidedOps P (s1.foldl OneSidedOp.step t) s2 := by
  induction s1 generalizing t with
  | nil => simp [ValidOneSidedOps]
  | cons op rest ih =>
    simp only [List.cons_append, ValidOneSidedOps, List.foldl_cons, ih, and_assoc]

def buildInitAux : ℕ → BinaryTree ℕ → List OneSidedOp
  | 0, _ => []
  | _ + 1, .nil => []
  | fuel + 1, .node u .nil B =>
    buildInitAux fuel B ++ [.push u]
  | fuel + 1, .node u (.node a aL aR) B =>
    buildInitAux fuel (.node a aL (.node u aR B)) ++ [.rightSpineLeftRot 1]

lemma buildInitAux_spec (P : ℕ) :
    ∀ (fuel : ℕ) (H : BinaryTree ℕ),
      2 * H.num_nodes - (rightSpine H).length ≤ fuel →
      H.IsBST →
      keyFinset H ⊆ Finset.Icc 1 P →
      let initSteps := buildInitAux fuel H
      ValidOneSidedOps P .nil initSteps ∧
      initSteps.foldl OneSidedOp.step .nil = H ∧
      (initSteps.filter (fun | .push _ => true | _ => false)).length = H.num_nodes ∧
      (initSteps.filter (fun | .pop _ => true | _ => false)).length = 0 ∧
      (initSteps.filter (fun | .rightSpineLeftRot _ => true | _ => false)).length =
        H.num_nodes - (rightSpine H).length ∧
      (∀ op ∈ initSteps, ∀ d : ℕ, op = .rightSpineLeftRot d → d = 1)
  | 0, .nil, _, _, _ => by simp [buildInitAux, ValidOneSidedOps, rightSpine]
  | 0, .node u l B, hfuel, _, _ => by
    have hrs := rightSpine_length_le_num_nodes B
    simp only [num_nodes_node, rightSpine, List.length_cons] at hfuel
    omega
  | fuel + 1, .nil, _, _, _ => by simp [buildInitAux, ValidOneSidedOps, rightSpine]
  | fuel + 1, .node u .nil B, hfuel, hBST, hKeys => by
    have hrsB := rightSpine_length_le_num_nodes B
    have hfuelB : 2 * B.num_nodes - (rightSpine B).length ≤ fuel := by
      simp only [num_nodes_node, num_nodes_empty, rightSpine, List.length_cons] at hfuel
      omega
    have hBSTB : B.IsBST := IsBST_right_of_IsBST hBST
    have hKeysB : keyFinset B ⊆ Finset.Icc 1 P := fun x hx => by
      apply hKeys
      rw [mem_keyFinset_iff] at hx ⊢
      exact .right hx
    have huMem : u ∈ Finset.Icc 1 P := hKeys (mem_keyFinset_iff.mpr .here)
    rw [Finset.mem_Icc] at huMem
    obtain ⟨hvB, hfoldB, hpushB, hpopB, hrotB, hd1B⟩ :=
      buildInitAux_spec P fuel B hfuelB hBSTB hKeysB
    dsimp only [buildInitAux]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [validOneSidedOps_append, hfoldB]
      refine ⟨hvB, ⟨huMem.1, huMem.2, ?_⟩, trivial⟩
      intro k hk
      exact gt_of_IsBST_right .nil u B hBST hk
    · rw [List.foldl_append, hfoldB]
      rfl
    · rw [List.filter_append]
      simp [hpushB]
      omega
    · rw [List.filter_append, List.length_append, hpopB]
      rfl
    · rw [List.filter_append]
      simp [hrotB, rightSpine]
      omega
    · intro op hop d hd
      rw [List.mem_append] at hop
      rcases hop with hop | hop
      · exact hd1B op hop d hd
      · simp at hop; subst hop; cases hd
  | fuel + 1, .node u (.node a aL aR) B, hfuel, hBST, hKeys => by
    let H' : BinaryTree ℕ := .node a aL (.node u aR B)
    have hkl : H'.toKeyList = (BinaryTree.node u (.node a aL aR) B).toKeyList := by
      simp [H', toKeyList]
    have hBST' : H'.IsBST := IsBST_of_toKeyList_eq hkl hBST
    have hKeys' : keyFinset H' ⊆ Finset.Icc 1 P := by
      rw [keyFinset_eq_toKeyList_toFinset H', hkl, ← keyFinset_eq_toKeyList_toFinset]
      exact hKeys
    have hrsB := rightSpine_length_le_num_nodes B
    have hfuel' : 2 * H'.num_nodes - (rightSpine H').length ≤ fuel := by
      simp only [H', num_nodes_node, rightSpine, List.length_cons] at hfuel ⊢
      omega
    obtain ⟨hv', hfold', hpush', hpop', hrot', hd1'⟩ :=
      buildInitAux_spec P fuel H' hfuel' hBST' hKeys'
    dsimp only [buildInitAux]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [validOneSidedOps_append, hfold']
      refine ⟨hv', ?_, trivial⟩
      simp [OneSidedOp.Valid, H', rightSpine]
    · rw [List.foldl_append, hfold']
      rfl
    · rw [List.filter_append]
      simp [hpush', H']
      omega
    · rw [List.filter_append, List.length_append]
      simpa [H'] using hpop'
    · rw [List.filter_append]
      simp only [H', num_nodes_node, rightSpine, List.length_cons] at hrot' ⊢
      simp [hrot']
      omega
    · intro op hop d hd
      rw [List.mem_append] at hop
      rcases hop with hop | hop
      · exact hd1' op hop d hd
      · simp at hop; subst hop; cases hd; rfl

theorem lem_3_5_part1 (P n₀ : ℕ) (H_init : BinaryTree ℕ)
    (hBST : H_init.IsBST) (hn₀ : H_init.num_nodes = n₀)
    (hKeys : keyFinset H_init ⊆ Finset.Icc 1 P) :
    ∃ initSteps : List OneSidedOp,
      ValidOneSidedOps P .nil initSteps ∧
      initSteps.foldl OneSidedOp.step .nil = H_init ∧
      (initSteps.filter (fun | .push _ => true | _ => false)).length = n₀ ∧
      (initSteps.filter (fun | .pop _ => true | _ => false)).length = 0 ∧
      (initSteps.filter (fun | .rightSpineLeftRot _ => true | _ => false)).length =
        n₀ - (rightSpine H_init).length ∧
      (∀ op ∈ initSteps, ∀ d : ℕ, op = .rightSpineLeftRot d → d = 1) := by
  subst hn₀
  refine ⟨buildInitAux (2 * H_init.num_nodes) H_init, ?_⟩
  exact buildInitAux_spec P (2 * H_init.num_nodes) H_init (Nat.sub_le _ _) hBST hKeys

/-! ## 3. Part 3a: Spine-Folding Bijection (`lem_3_5_part3a`) -/

def rebuildRight : List (α × BinaryTree α) → BinaryTree α → BinaryTree α
  | [], tailAcc => tailAcc
  | (b, l) :: rest, tailAcc => .node b l (rebuildRight rest tailAcc)

lemma rebuildRight_rightSpineFrames (t : BinaryTree α) :
    rebuildRight (rightSpineFrames t) .nil = t := by
  induction t with
  | nil => rfl
  | node b l r _ ihr => simp [rightSpineFrames, rebuildRight, ihr]

lemma toKeyList_spineFoldGo (prevKey : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) :
    (spineFoldGo prevKey acc frames).toKeyList =
      acc.toKeyList ++ [prevKey] ++ (rebuildRight frames .nil).toKeyList := by
  induction frames generalizing prevKey acc with
  | nil => simp [spineFoldGo, rebuildRight, toKeyList]
  | cons p rest ih =>
    rcases p with ⟨bNext, lNext⟩
    simp [spineFoldGo, rebuildRight, ih, toKeyList]

lemma toKeyList_spineFoldTree (H : BinaryTree α) :
    (spineFoldTree H).1.toKeyList = H.toKeyList := by
  cases H with
  | nil => rfl
  | node b1 l1 r1 =>
    simp [spineFoldTree, rightSpineFrames, toKeyList_spineFoldGo,
      rebuildRight_rightSpineFrames, toKeyList]

def unfoldTop [DecidableEq α] (b1 : α) (ft : BinaryTree α) (tailAcc : BinaryTree α) :
    BinaryTree α :=
  match ft with
  | .nil => .nil
  | .node bRoot lRoot _ =>
    if bRoot = b1 then .node bRoot lRoot tailAcc
    else spineUnfoldGo b1 bRoot tailAcc lRoot

lemma spineUnfoldTree_some_eq_unfoldTop [DecidableEq α] (ft : BinaryTree α) (b1 : α) :
    spineUnfoldTree ft (some b1) = unfoldTop b1 ft .nil := by
  cases ft <;> rfl

lemma unfoldTop_spineFoldGo [DecidableEq α] (b1 prevKey : α) (acc tailAcc : BinaryTree α)
    (frames : List (α × BinaryTree α))
    (hprev : prevKey ≠ b1) (hframes : ∀ p ∈ frames, p.1 ≠ b1) :
    unfoldTop b1 (spineFoldGo prevKey acc frames) tailAcc =
      spineUnfoldGo b1 prevKey (rebuildRight frames tailAcc) acc := by
  induction frames generalizing prevKey acc with
  | nil =>
    simp [spineFoldGo, unfoldTop, rebuildRight, hprev]
  | cons p rest ih =>
    rcases p with ⟨bNext, lNext⟩
    have hbNext : bNext ≠ b1 := hframes (bNext, lNext) List.mem_cons_self
    have hrest : ∀ q ∈ rest, q.1 ≠ b1 := fun q hq => hframes q (List.mem_cons_of_mem _ hq)
    simp only [spineFoldGo]
    rw [ih bNext (.node prevKey acc lNext) hbNext hrest]
    simp [spineUnfoldGo, rebuildRight, hprev]

lemma mem_rightSpineFrames_fst {t : BinaryTree α} {p : α × BinaryTree α}
    (hp : p ∈ rightSpineFrames t) : p.1 ∈ t := by
  induction t with
  | nil => simp [rightSpineFrames] at hp
  | node b l r _ ihr =>
    simp only [rightSpineFrames, List.mem_cons] at hp
    rcases hp with rfl | hr
    · exact .here
    · exact .right (ihr hr)

theorem lem_3_5_part3a (H : BinaryTree ℕ) (hBST : H.IsBST) :
    (spineFoldTree H).1.IsBST ∧
    keyFinset (spineFoldTree H).1 = keyFinset H ∧
    spineUnfoldTree (spineFoldTree H).1 (spineFoldTree H).2 = H := by
  have hkl := toKeyList_spineFoldTree H
  refine ⟨IsBST_of_toKeyList_eq hkl hBST, ?_, ?_⟩
  · rw [keyFinset_eq_toKeyList_toFinset, keyFinset_eq_toKeyList_toFinset H, hkl]
  · cases H with
    | nil => rfl
    | node b1 l1 r1 =>
      cases r1 with
      | nil =>
        simp [spineFoldTree, rightSpineFrames, spineFoldGo, spineUnfoldTree]
      | node b2 l2 r2 =>
        have hb2 : b2 ≠ b1 :=
          ne_of_gt (gt_of_IsBST_right l1 b1 (.node b2 l2 r2) hBST .here)
        have hfr : ∀ p ∈ rightSpineFrames r2, p.1 ≠ b1 := fun p hp =>
          ne_of_gt (gt_of_IsBST_right l1 b1 (.node b2 l2 r2) hBST
            (.right (mem_rightSpineFrames_fst hp)))
        simp only [spineFoldTree, rightSpineFrames, spineFoldGo]
        rw [spineUnfoldTree_some_eq_unfoldTop,
          unfoldTop_spineFoldGo b1 b2 (.node b1 l1 l2) .nil (rightSpineFrames r2) hb2 hfr,
          rebuildRight_rightSpineFrames]
        simp [spineUnfoldGo]

/-! ## 4. Part 3b: Potential Bound `exec.kL ≤ 2 * P - 2` and Dynamic Folded Simulation -/

lemma spliceMin_node_of_ne_nil (k : α) {l : BinaryTree α} (r : BinaryTree α) (hl : l ≠ .nil) :
    spliceMin (.node k l r) = .node k (spliceMin l) r := by
  cases l with
  | nil => exact absurd rfl hl
  | node _ _ _ => rfl

lemma toKeyList_spliceMin_of_ne_nil {t : BinaryTree α} (ht : t ≠ .nil) :
    ∃ m, t.minKey? = some m ∧ t.toKeyList = m :: (spliceMin t).toKeyList := by
  induction t with
  | nil => exact absurd rfl ht
  | node k l r ihl _ =>
    cases l with
    | nil =>
      refine ⟨k, rfl, ?_⟩
      simp [spliceMin, toKeyList]
    | node lk ll lr =>
      obtain ⟨m, hm, hkl⟩ := ihl (by simp)
      have hmin : (BinaryTree.node k (.node lk ll lr) r).minKey? = some m := by
        rw [BinaryTree.minKey?, hm]
      refine ⟨m, hmin, ?_⟩
      rw [spliceMin_node_of_ne_nil k r (by simp), toKeyList_node, hkl]
      simp [toKeyList]

lemma sublist_toKeyList_spliceMin (t : BinaryTree α) :
    List.Sublist (spliceMin t).toKeyList t.toKeyList := by
  by_cases ht : t = .nil
  · subst ht; simp [spliceMin]
  · obtain ⟨m, _, hkl⟩ := toKeyList_spliceMin_of_ne_nil ht
    rw [hkl]
    exact List.sublist_cons_self _ _

lemma isBST_spliceMin [LinearOrder α] {t : BinaryTree α} (hBST : t.IsBST) :
    (spliceMin t).IsBST := by
  rw [IsBST_iff_toKeyList_sorted] at hBST ⊢
  exact hBST.sublist (sublist_toKeyList_spliceMin t)

lemma keyFinset_spliceMin_subset [DecidableEq α] (t : BinaryTree α) :
    keyFinset (spliceMin t) ⊆ keyFinset t := by
  intro x hx
  rw [mem_keyFinset_iff, mem_iff_mem_toKeyList] at hx ⊢
  exact (sublist_toKeyList_spliceMin t).subset hx

lemma toKeyList_rotateRightEdge [LinearOrder α] (t : BinaryTree α) (x p : α) :
    (rotateRightEdge t x p).toKeyList = t.toKeyList := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [rotateRightEdge]
    split_ifs with h1 h2
    · simp [toKeyList, ihl]
    · simp [toKeyList, ihr]
    · cases l with
      | nil => rfl
      | node lx a b =>
        dsimp only []
        split_ifs <;> simp [toKeyList]

lemma toKeyList_foldl_rotateRightEdge [LinearOrder α] (pairs : List (α × α)) (t : BinaryTree α) :
    (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t).toKeyList = t.toKeyList := by
  induction pairs generalizing t with
  | nil => rfl
  | cons p rest ih =>
    rw [List.foldl_cons, ih, toKeyList_rotateRightEdge]

lemma toKeyList_popCascade [LinearOrder α] (t : BinaryTree α) :
    (popCascade t).toKeyList = (spliceMin t).toKeyList :=
  toKeyList_foldl_rotateRightEdge (popCascadePairs t) (spliceMin t)

lemma toKeyList_rotateLeftAtRightSpine1 (t : BinaryTree α) (d : ℕ) (hd : 1 ≤ d) :
    (rotateLeftAtRightSpine1 t d).toKeyList = t.toKeyList := by
  induction t generalizing d with
  | nil =>
    match d with
    | 0 => omega
    | 1 => rfl
    | _ + 2 => rfl
  | node k l r _ ihr =>
    match d with
    | 0 => omega
    | 1 => exact SplayTree.toKeyList_rotateLeft _
    | d' + 2 =>
      rw [rotateLeftAtRightSpine1, toKeyList_node, ihr (d' + 1) (by omega), toKeyList_node]

lemma oneSidedOp_preserves {P : ℕ} {t : BinaryTree ℕ} {op : OneSidedOp}
    (hBST : t.IsBST) (hKeys : keyFinset t ⊆ Finset.Icc 1 P) (hValid : op.Valid P t) :
    (op.step t).IsBST ∧ keyFinset (op.step t) ⊆ Finset.Icc 1 P := by
  cases op with
  | push w =>
    rcases hValid with ⟨hw1, hw2, hlt⟩
    refine ⟨?_, ?_⟩
    · rw [IsBST_iff_toKeyList_sorted] at hBST ⊢
      simp only [OneSidedOp.step, SplayTree.push, toKeyList_node, toKeyList_empty,
        List.nil_append, List.singleton_append, List.pairwise_cons]
      exact ⟨fun k hk => hlt k (mem_iff_mem_toKeyList.mpr hk), hBST⟩
    · intro x hx
      rw [mem_keyFinset_iff] at hx
      simp only [OneSidedOp.step, SplayTree.push, mem_node_iff, not_mem_nil, false_or] at hx
      rcases hx with rfl | hx
      · exact Finset.mem_Icc.mpr ⟨hw1, hw2⟩
      · exact hKeys (mem_keyFinset_iff.mpr hx)
  | pop s =>
    have hkl := toKeyList_popCascade t
    refine ⟨IsBST_of_toKeyList_eq hkl (isBST_spliceMin hBST), ?_⟩
    rw [OneSidedOp.step, keyFinset_eq_toKeyList_toFinset, hkl, ← keyFinset_eq_toKeyList_toFinset]
    exact (keyFinset_spliceMin_subset t).trans hKeys
  | rightSpineLeftRot d =>
    have hkl := toKeyList_rotateLeftAtRightSpine1 t d hValid.1
    refine ⟨IsBST_of_toKeyList_eq hkl hBST, ?_⟩
    rw [OneSidedOp.step, keyFinset_eq_toKeyList_toFinset, hkl, ← keyFinset_eq_toKeyList_toFinset]
    exact hKeys

lemma validOneSidedOps_preserves {P : ℕ} {t : BinaryTree ℕ} {ops : List OneSidedOp}
    (hBST : t.IsBST) (hKeys : keyFinset t ⊆ Finset.Icc 1 P) (hValid : ValidOneSidedOps P t ops) :
    (ops.foldl OneSidedOp.step t).IsBST ∧
    keyFinset (ops.foldl OneSidedOp.step t) ⊆ Finset.Icc 1 P := by
  induction ops generalizing t with
  | nil => exact ⟨hBST, hKeys⟩
  | cons op rest ih =>
    obtain ⟨hv1, hvRest⟩ := hValid
    obtain ⟨hBST1, hKeys1⟩ := oneSidedOp_preserves hBST hKeys hv1
    exact ih hBST1 hKeys1 hvRest

lemma rightSpine_rotateLeftAtRightSpine1 (t : BinaryTree α) (d : ℕ)
    (hd1 : 1 ≤ d) (hd2 : d + 1 ≤ (rightSpine t).length) :
    (rightSpine (rotateLeftAtRightSpine1 t d)).length + 1 = (rightSpine t).length := by
  induction t generalizing d with
  | nil => simp [rightSpine] at hd2
  | node k l r _ ihr =>
    match d with
    | 0 => omega
    | 1 =>
      cases r with
      | nil => simp [rightSpine] at hd2
      | node rk rl rr => simp [rotateLeftAtRightSpine1, BinaryTree.rotateLeft, rightSpine]
    | d' + 2 =>
      simp only [rotateLeftAtRightSpine1, rightSpine, List.length_cons] at hd2 ⊢
      have ih := ihr (d' + 1) (by omega) (by omega)
      omega

lemma rightSpine_foldl_adjacentPairs_snoc [LinearOrder α] (xs : List α) (rKey : α)
    (L R : BinaryTree α) (hlt : ∀ z ∈ xs, z < rKey) :
    (rightSpine ((adjacentPairs (xs ++ [rKey])).foldl
      (fun acc p => rotateRightEdge acc p.1 p.2) (.node rKey L R))).length ≤
      (rightSpine R).length + 2 := by
  induction xs using List.twoStepInduction generalizing L with
  | nil => simp [adjacentPairs, rightSpine]
  | singleton a =>
    simp only [List.singleton_append, adjacentPairs, List.foldl_cons, List.foldl_nil,
      rotateRightEdge, lt_irrefl, ite_false]
    cases L with
    | nil => simp [rightSpine]
    | node lx la lb =>
      dsimp only []
      split_ifs <;> simp [rightSpine]
  | cons_cons a b rest ih _ =>
    have hb : b < rKey := hlt b (by simp)
    have hrest : ∀ z ∈ rest, z < rKey := fun z hz => hlt z (by simp [hz])
    simp only [List.cons_append, adjacentPairs, List.foldl_cons, rotateRightEdge, hb, ↓reduceIte]
    exact ih (rotateRightEdge L a b) hrest

lemma rightSpine_popCascade_le [LinearOrder α] {t : BinaryTree α} (hBST : t.IsBST) :
    (rightSpine (popCascade t)).length ≤ (rightSpine t).length + 1 := by
  cases t with
  | nil =>
    dsimp [popCascade, popCascadePairs, leftSpine, adjacentPairs, spliceMin, rightSpine]
    omega
  | node rKey l r =>
    cases l with
    | nil =>
      dsimp [popCascade, popCascadePairs, leftSpine, adjacentPairs, spliceMin, rightSpine]
      omega
    | node lk ll lr =>
      have hne : leftSpine (BinaryTree.node lk ll lr) ≠ [] :=
        mt (leftSpine_eq_nil_iff _).mp (by simp)
      obtain ⟨v0, lsTail, hls⟩ := List.exists_cons_of_ne_nil hne
      have hlt : ∀ z ∈ lsTail, z < rKey := fun z hz => by
        have hmem : z ∈ leftSpine (BinaryTree.node lk ll lr) := by
          rw [hls]; exact List.mem_cons_of_mem _ hz
        exact lt_of_IsBST_left _ rKey r hBST (mem_of_mem_leftSpine hmem)
      have hpairs : popCascadePairs (.node rKey (.node lk ll lr) r) =
          adjacentPairs (lsTail ++ [rKey]) := by
        rw [popCascadePairs, leftSpine, hls, List.cons_append, List.tail_cons]
      have hsp : spliceMin (.node rKey (.node lk ll lr) r) =
          .node rKey (spliceMin (.node lk ll lr)) r := rfl
      rw [popCascade, hpairs, hsp]
      have hbound := rightSpine_foldl_adjacentPairs_snoc lsTail rKey
        (spliceMin (.node lk ll lr)) r hlt
      simp only [rightSpine, List.length_cons]
      omega

lemma rightSpine_potential_bound (P : ℕ) (t0 : BinaryTree ℕ) (ops : List OneSidedOp)
    (hBST : t0.IsBST) (hKeys : keyFinset t0 ⊆ Finset.Icc 1 P)
    (hValid : ValidOneSidedOps P t0 ops) :
    (rightSpine (ops.foldl OneSidedOp.step t0)).length +
      (ops.filter (fun | .rightSpineLeftRot _ => true | _ => false)).length ≤
    (rightSpine t0).length +
      (ops.filter (fun | .push _ => true | _ => false)).length +
      (ops.filter (fun | .pop _ => true | _ => false)).length := by
  induction ops generalizing t0 with
  | nil => simp
  | cons op rest ih =>
    obtain ⟨hv1, hvRest⟩ := hValid
    obtain ⟨hBST1, hKeys1⟩ := oneSidedOp_preserves hBST hKeys hv1
    have hrec := ih (op.step t0) hBST1 hKeys1 hvRest
    cases op with
    | push w =>
      simp only [List.foldl_cons, OneSidedOp.step, SplayTree.push, rightSpine, List.length_cons,
        List.filter_cons, Bool.false_eq_true, ↓reduceIte] at hrec ⊢
      omega
    | pop s =>
      have hpop := rightSpine_popCascade_le hBST
      simp only [List.foldl_cons, OneSidedOp.step, List.filter_cons, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] at hrec ⊢
      omega
    | rightSpineLeftRot d =>
      have hrot := rightSpine_rotateLeftAtRightSpine1 t0 d hv1.1 hv1.2
      simp only [List.foldl_cons, OneSidedOp.step, List.filter_cons, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] at hrec ⊢
      omega

lemma length_filterMap_push_eq (ops : List OneSidedOp) (f : OneSidedOp → Option ℕ)
    (hpush : ∀ w, f (.push w) = some w)
    (hpop : ∀ s, f (.pop s) = none)
    (hrot : ∀ d, f (.rightSpineLeftRot d) = none) :
    (ops.filterMap f).length =
      (ops.filter (fun | .push _ => true | _ => false)).length := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    cases op with
    | push w => simp [hpush, ih]
    | pop s => simp [hpop, ih]
    | rightSpineLeftRot d => simp [hrot, ih]

lemma length_filterMap_pop_eq (ops : List OneSidedOp) (f : OneSidedOp → Option ℕ)
    (hpush : ∀ w, f (.push w) = none)
    (hpop : ∀ s, f (.pop s) = some s)
    (hrot : ∀ d, f (.rightSpineLeftRot d) = none) :
    (ops.filterMap f).length =
      (ops.filter (fun | .pop _ => true | _ => false)).length := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    cases op with
    | push w => simp [hpush, ih]
    | pop s => simp [hpop, ih]
    | rightSpineLeftRot d => simp [hrot, ih]

lemma exec_pop_filter_len {P : ℕ} (exec : OneSidedPopExec P) :
    (exec.steps.filter (fun | .pop _ => true | _ => false)).length = P := by
  have h := congrArg List.length exec.hPopSeq
  rw [List.length_range',
    length_filterMap_pop_eq exec.steps _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)] at h
  exact h

lemma exec_push_filter_len {P : ℕ} (exec : OneSidedPopExec P) :
    (exec.steps.filter (fun | .push _ => true | _ => false)).length = P := by
  have h := exec.hPushCount
  rw [length_filterMap_push_eq exec.steps _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)] at h
  exact h

lemma filter_congr_len {α : Type} (xs : List α) (p q : α → Bool) (h : ∀ x, p x = q x) :
    (xs.filter p).length = (xs.filter q).length :=
  congrArg List.length (List.filter_congr fun x _ => h x)

lemma exec_kL_le_two_mul_sub_two (P : ℕ) (hP : 1 ≤ P) (exec : OneSidedPopExec P) :
    exec.kL ≤ 2 * P - 2 := by
  have hPopTotal := exec_pop_filter_len exec
  have hPushTotal := exec_push_filter_len exec
  have hne : exec.steps ≠ [] := by
    intro hnil; rw [hnil] at hPopTotal; simp at hPopTotal; omega
  rcases hrev : exec.steps.reverse with _ | ⟨lastOp, revPre⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hrev) hne
  have hdecomp : exec.steps = revPre.reverse ++ [lastOp] := by
    rw [← List.reverse_reverse exec.steps, hrev, List.reverse_cons]
  let pre := revPre.reverse
  change exec.steps = pre ++ [lastOp] at hdecomp
  have hvAll := exec.hValid
  rw [hdecomp, validOneSidedOps_append] at hvAll
  obtain ⟨hvPre, hvLast, _⟩ := hvAll
  let tPre := pre.foldl OneSidedOp.step .nil
  obtain ⟨hBSTPre, _⟩ := validOneSidedOps_preserves BinaryTree.IsBST.left (by simp [keyFinset]) hvPre
  have hEnd := exec.hEndEmpty
  rw [hdecomp, List.foldl_append, List.foldl_cons, List.foldl_nil] at hEnd
  change lastOp.step tPre = .nil at hEnd
  cases lastOp with
  | push w =>
    simp [OneSidedOp.step, SplayTree.push] at hEnd
  | rightSpineLeftRot d =>
    have hkl := toKeyList_rotateLeftAtRightSpine1 tPre d hvLast.1
    rw [OneSidedOp.step] at hEnd
    rw [hEnd] at hkl
    have hnum : tPre.num_nodes = 0 := by
      rw [num_nodes_eq_length_toKeyList, ← hkl]; rfl
    have hrs := rightSpine_length_le_num_nodes tPre
    have hd2 : d + 1 ≤ (rightSpine tPre).length := hvLast.2
    omega
  | pop s =>
    have htPreNe : tPre ≠ .nil := hvLast.1
    have hrsPos : 1 ≤ (rightSpine tPre).length := by
      cases ht : tPre with
      | nil => exact absurd ht htPreNe
      | node _ _ _ => simp [rightSpine]
    have hpot := rightSpine_potential_bound P .nil pre
      BinaryTree.IsBST.left (by simp [keyFinset]) hvPre
    have hPushAny : ∀ p : OneSidedOp → Bool,
        (∀ w, p (.push w) = true) → (∀ q, p (.pop q) = false) → (∀ d, p (.rightSpineLeftRot d) = false) →
        (pre.filter p).length = P := by
      intro p h1 h2 h3
      have heq : (exec.steps.filter p).length = P := by
        refine Eq.trans ?_ hPushTotal
        exact filter_congr_len exec.steps p _ (fun x => by cases x <;> simp [h1, h2, h3])
      rw [hdecomp, List.filter_append] at heq
      simpa [h2] using heq
    have hPopAny : ∀ p : OneSidedOp → Bool,
        (∀ w, p (.push w) = false) → (∀ q, p (.pop q) = true) → (∀ d, p (.rightSpineLeftRot d) = false) →
        (pre.filter p).length = P - 1 := by
      intro p h1 h2 h3
      have heq : (exec.steps.filter p).length = P := by
        refine Eq.trans ?_ hPopTotal
        exact filter_congr_len exec.steps p _ (fun x => by cases x <;> simp [h1, h2, h3])
      rw [hdecomp, List.filter_append] at heq
      simp only [List.filter_cons, List.filter_nil, h2, ↓reduceIte, List.length_append,
        List.length_singleton] at heq
      omega
    have hkLAny : ∀ p : OneSidedOp → Bool,
        (∀ w, p (.push w) = false) → (∀ q, p (.pop q) = false) → (∀ d, p (.rightSpineLeftRot d) = true) →
        (pre.filter p).length = exec.kL := by
      intro p h1 h2 h3
      have heq : (exec.steps.filter p).length = exec.kL := by
        unfold OneSidedPopExec.kL
        exact filter_congr_len exec.steps p _ (fun x => by cases x <;> simp [h1, h2, h3])
      rw [hdecomp, List.filter_append] at heq
      simpa [h2] using heq
    rw [hkLAny _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
        hPushAny _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
        hPopAny _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)] at hpot
    simp only [rightSpine, List.length_nil] at hpot
    change (rightSpine tPre).length + exec.kL ≤ 0 + P + (P - 1) at hpot
    omega

/-! ## 5. Structural Lemmas on `spineFoldGo` and Single-Step Simulation -/

lemma spineFoldGo_ne_nil (prev : α) (acc : BinaryTree α) (frames : List (α × BinaryTree α)) :
    spineFoldGo prev acc frames ≠ .nil := by
  induction frames generalizing prev acc with
  | nil => simp [spineFoldGo]
  | cons p rest ih => exact ih p.1 (.node prev acc p.2)

lemma map_fst_rightSpineFrames (t : BinaryTree α) :
    (rightSpineFrames t).map Prod.fst = rightSpine t := by
  induction t with
  | nil => rfl
  | node b l r _ ihr => simp [rightSpineFrames, rightSpine, ihr]

lemma rootKey_spineFoldGo (prev : α) (acc : BinaryTree α) (frames : List (α × BinaryTree α)) :
    rootKey? (spineFoldGo prev acc frames) =
      some ((prev :: frames.map Prod.fst).getLast (by simp)) := by
  induction frames generalizing prev acc with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨bNext, lNext⟩
    simp [spineFoldGo, ih]

lemma leftSpine_spineFoldGo (prev : α) (acc : BinaryTree α) (frames : List (α × BinaryTree α)) :
    leftSpine (spineFoldGo prev acc frames) = leftSpine acc ++ prev :: frames.map Prod.fst := by
  induction frames generalizing prev acc with
  | nil => simp [spineFoldGo, leftSpine]
  | cons p rest ih =>
    rcases p with ⟨bNext, lNext⟩
    simp [spineFoldGo, ih, leftSpine]

lemma takeThrough_append_of_not_mem [DecidableEq α] (xs ys : List α) (target : α)
    (hnot : target ∉ xs) :
    takeThrough (xs ++ target :: ys) target = xs ++ [target] := by
  induction xs with
  | nil => simp [takeThrough]
  | cons a rest ih =>
    have ha : a ≠ target := fun h => hnot (by simp [h])
    have hrest : target ∉ rest := fun h => hnot (by simp [h])
    simp [takeThrough, ha, ih hrest]

lemma nextOnSpine_append_of_not_mem [DecidableEq α] (xs ys : List α) (target : α)
    (hnot : target ∉ xs) :
    nextOnSpine (xs ++ target :: ys) target = ys.head? := by
  induction xs with
  | nil => cases ys <;> simp [nextOnSpine]
  | cons a rest ih =>
    have ha : a ≠ target := fun h => hnot (by simp [h])
    have hrest : target ∉ rest := fun h => hnot (by simp [h])
    rcases hne : rest ++ target :: ys with _ | ⟨c, tail'⟩
    · simp at hne
    · simp only [List.cons_append]
      rw [hne]
      simp only [nextOnSpine, ha, ite_false, ← hne]
      exact ih hrest

lemma modifyLeftAt_spineFoldGo_lt [LinearOrder α] (prev : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) (target : α) (f : BinaryTree α → BinaryTree α)
    (hprev : target < prev) (hframes : ∀ p ∈ frames, target < p.1) :
    modifyLeftAt (spineFoldGo prev acc frames) target f =
      spineFoldGo prev (modifyLeftAt acc target f) frames := by
  induction frames generalizing prev acc with
  | nil => simp [spineFoldGo, modifyLeftAt, hprev]
  | cons p rest ih =>
    rcases p with ⟨bNext, lNext⟩
    simp only [spineFoldGo]
    rw [ih bNext (.node prev acc lNext) (hframes _ List.mem_cons_self)
      (fun q hq => hframes q (List.mem_cons_of_mem _ hq))]
    simp [modifyLeftAt, hprev]

lemma modifyLeftAt_spineFoldGo_eq [LinearOrder α] (b1 : α) (l1 : BinaryTree α)
    (frames : List (α × BinaryTree α)) (f : BinaryTree α → BinaryTree α)
    (hframes : ∀ p ∈ frames, b1 < p.1) :
    modifyLeftAt (spineFoldGo b1 l1 frames) b1 f = spineFoldGo b1 (f l1) frames := by
  cases frames with
  | nil => simp [spineFoldGo, modifyLeftAt]
  | cons p rest =>
    rcases p with ⟨b2, l2⟩
    simp only [spineFoldGo]
    rw [modifyLeftAt_spineFoldGo_lt b2 (.node b1 l1 l2) rest b1 f
      (hframes _ List.mem_cons_self) (fun q hq => hframes q (List.mem_cons_of_mem _ hq))]
    simp [modifyLeftAt]

lemma spliceMin_spineFoldGo_of_ne_nil (prev : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) (hacc : acc ≠ .nil) :
    spliceMin (spineFoldGo prev acc frames) = spineFoldGo prev (spliceMin acc) frames := by
  induction frames generalizing prev acc with
  | nil => exact spliceMin_node_of_ne_nil prev .nil hacc
  | cons p rest ih =>
    rcases p with ⟨bNext, lNext⟩
    simp only [spineFoldGo]
    rw [ih bNext (.node prev acc lNext) (by simp), spliceMin_node_of_ne_nil prev lNext hacc]

lemma rotateRightEdge_spineFoldGo_lt [LinearOrder α] (prev : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) (x p : α)
    (hprev : p < prev) (hframes : ∀ q ∈ frames, p < q.1) :
    rotateRightEdge (spineFoldGo prev acc frames) x p =
      spineFoldGo prev (rotateRightEdge acc x p) frames := by
  induction frames generalizing prev acc with
  | nil => simp [spineFoldGo, rotateRightEdge, hprev]
  | cons q rest ih =>
    rcases q with ⟨bNext, lNext⟩
    simp only [spineFoldGo]
    rw [ih bNext (.node prev acc lNext) (hframes _ List.mem_cons_self)
      (fun q' hq' => hframes q' (List.mem_cons_of_mem _ hq'))]
    simp [rotateRightEdge, hprev]

lemma subtreeAtKey_spineFoldGo_lt [LinearOrder α] (prev : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) (p : α)
    (hprev : p < prev) (hframes : ∀ q ∈ frames, p < q.1) :
    subtreeAtKey (spineFoldGo prev acc frames) p = subtreeAtKey acc p := by
  induction frames generalizing prev acc with
  | nil => simp [spineFoldGo, subtreeAtKey, hprev]
  | cons q rest ih =>
    rcases q with ⟨bNext, lNext⟩
    simp only [spineFoldGo]
    rw [ih bNext (.node prev acc lNext) (hframes _ List.mem_cons_self)
      (fun q' hq' => hframes q' (List.mem_cons_of_mem _ hq'))]
    simp [subtreeAtKey, hprev]

lemma upperRot_spineFoldGo (prev : ℕ) (acc r : BinaryTree ℕ) (m : ℕ)
    (hsorted : (prev :: rightSpine r).Pairwise (· < ·))
    (hlen : m + 2 ≤ (rightSpine r).length) :
    ∃ u v : ℕ,
      (prev :: rightSpine r)[m]? = some u ∧
      (prev :: rightSpine r)[m + 1]? = some v ∧
      prev ≤ u ∧ u < v ∧
      v < (prev :: rightSpine r).getLast (by simp) ∧
      u ∈ prev :: rightSpine r ∧
      v ∈ prev :: rightSpine r ∧
      IsRightRotEdge (spineFoldGo prev acc (rightSpineFrames r)) u v ∧
      rotateRightEdge (spineFoldGo prev acc (rightSpineFrames r)) u v =
        spineFoldGo prev acc (rightSpineFrames (rotateLeftAtRightSpine1 r (m + 1))) := by
  induction m generalizing prev acc r with
  | zero =>
    rcases r with _ | ⟨b2, l2, _ | ⟨b3, l3, r3⟩⟩
    · simp [rightSpine] at hlen
    · simp [rightSpine] at hlen
    · simp only [rightSpine, List.pairwise_cons] at hsorted
      obtain ⟨hprevlt, hb2lt, hb3lt, _⟩ := hsorted
      have hprevb2 : prev < b2 := hprevlt b2 (by simp)
      have hb2b3 : b2 < b3 := hb2lt b3 (by simp)
      have hb2fr : ∀ q ∈ rightSpineFrames r3, b2 < q.1 := fun q hq => by
        have hmem : q.1 ∈ rightSpine r3 := by
          rw [← map_fst_rightSpineFrames]; exact List.mem_map_of_mem hq
        exact hb2lt q.1 (List.mem_cons_of_mem _ hmem)
      have hvlast : b2 < (prev :: rightSpine (.node b2 l2 (.node b3 l3 r3))).getLast (by simp) := by
        have hlast_eq : (prev :: b2 :: b3 :: rightSpine r3).getLast (by simp) =
            (b3 :: rightSpine r3).getLast (by simp) := by simp
        rw [show rightSpine (.node b2 l2 (.node b3 l3 r3)) = b2 :: b3 :: rightSpine r3 from rfl,
          hlast_eq]
        exact hb2lt _ (List.getLast_mem _)
      refine ⟨prev, b2, rfl, rfl, le_rfl, hprevb2, hvlast, by simp, by simp [rightSpine], ?_, ?_⟩
      · refine ⟨acc, l2, l3, ?_, ?_⟩
        · apply mem_of_mem_leftSpine
          simp [leftSpine_spineFoldGo, rightSpineFrames]
        · simp only [rightSpineFrames, spineFoldGo]
          rw [subtreeAtKey_spineFoldGo_lt b3 (.node b2 (.node prev acc l2) l3)
            (rightSpineFrames r3) b2 hb2b3 hb2fr]
          simp [subtreeAtKey]
      · simp only [rightSpineFrames, spineFoldGo, rotateLeftAtRightSpine1, BinaryTree.rotateLeft]
        rw [rotateRightEdge_spineFoldGo_lt b3 (.node b2 (.node prev acc l2) l3)
          (rightSpineFrames r3) prev b2 hb2b3 hb2fr]
        simp [rotateRightEdge]
  | succ m' ih =>
    rcases r with _ | ⟨b2, l2, r2⟩
    · simp [rightSpine] at hlen
    · simp only [rightSpine, List.length_cons] at hlen
      rw [rightSpine, List.pairwise_cons] at hsorted
      obtain ⟨hprevlt, hsorted2⟩ := hsorted
      have hprevb2 : prev < b2 := hprevlt b2 (by simp)
      obtain ⟨u, v, hu, hv, hb2u, huv, hvlast, humem, hvmem, hedge, hrot⟩ :=
        ih b2 (.node prev acc l2) r2 hsorted2 (by omega)
      refine ⟨u, v, hu, hv, le_of_lt (lt_of_lt_of_le hprevb2 hb2u), huv, ?_,
        List.mem_cons_of_mem _ humem, List.mem_cons_of_mem _ hvmem, hedge, hrot⟩
      simpa [rightSpine] using hvlast

lemma adjacentPairs_append_of_even (xs ys : List α) (heven : xs.length % 2 = 0) :
    adjacentPairs (xs ++ ys) = adjacentPairs xs ++ adjacentPairs ys := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp at heven
  | cons_cons a b rest ih _ =>
    have hrest : rest.length % 2 = 0 := by simp at heven; omega
    simp [adjacentPairs, ih hrest]

lemma length_adjacentPairs (xs : List α) :
    (adjacentPairs xs).length = xs.length / 2 := by
  induction xs using List.twoStepInduction with
  | nil => simp [adjacentPairs]
  | singleton a => simp [adjacentPairs]
  | cons_cons a b rest ih _ =>
    simp [adjacentPairs, ih]
    omega

lemma snd_mem_of_mem_adjacentPairs {xs : List α} {p : α × α} (hp : p ∈ adjacentPairs xs) :
    p.2 ∈ xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [adjacentPairs] at hp
  | singleton a => simp [adjacentPairs] at hp
  | cons_cons a b rest ih _ =>
    simp only [adjacentPairs, List.mem_cons] at hp
    rcases hp with rfl | hrest
    · simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih hrest))

lemma foldl_rotateRightEdge_node_lt [LinearOrder α] (pairs : List (α × α)) (k : α)
    (L R : BinaryTree α) (hlt : ∀ p ∈ pairs, p.2 < k) :
    pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (.node k L R) =
      .node k (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) L) R := by
  induction pairs generalizing L with
  | nil => rfl
  | cons p rest ih =>
    have hp : p.2 < k := hlt p List.mem_cons_self
    simp only [List.foldl_cons, rotateRightEdge, hp, ↓reduceIte]
    exact ih _ (fun q hq => hlt q (List.mem_cons_of_mem _ hq))

lemma foldl_rotateRightEdge_spineFoldGo_lt [LinearOrder α] (pairs : List (α × α)) (prev : α)
    (acc : BinaryTree α) (frames : List (α × BinaryTree α))
    (hprev : ∀ p ∈ pairs, p.2 < prev) (hframes : ∀ p ∈ pairs, ∀ q ∈ frames, p.2 < q.1) :
    pairs.foldl (fun t p => rotateRightEdge t p.1 p.2) (spineFoldGo prev acc frames) =
      spineFoldGo prev (pairs.foldl (fun t p => rotateRightEdge t p.1 p.2) acc) frames := by
  induction pairs generalizing acc with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.foldl_cons]
    rw [rotateRightEdge_spineFoldGo_lt prev acc frames p.1 p.2
      (hprev p List.mem_cons_self) (hframes p List.mem_cons_self)]
    exact ih _ (fun q hq => hprev q (List.mem_cons_of_mem _ hq))
      (fun q hq => hframes q (List.mem_cons_of_mem _ hq))

/-- Map a single `OneSidedOp` on `t` to the corresponding `FoldedOp` (matching `spineFoldOpList`). -/
def spineFoldSingleOp (t : BinaryTree ℕ) : OneSidedOp → FoldedOp
  | .push w => .push w
  | .pop s => .pop s
  | .rightSpineLeftRot d =>
    if d ≤ 1 then .shift
    else
      let rs := rightSpine t
      match rs[d - 2]?, rs[d - 1]? with
      | some u, some v => .upperRot u v
      | _, _ => .shift

lemma spineFoldOpList_cons (t : BinaryTree ℕ) (op : OneSidedOp) (rest : List OneSidedOp) :
    spineFoldOpList t (op :: rest) =
      spineFoldSingleOp t op :: spineFoldOpList (op.step t) rest := rfl

lemma length_filterMap_of_forall_isSome {α β : Type} (f : α → Option β) (l : List α)
    (h : ∀ a ∈ l, (f a).isSome) : (l.filterMap f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a List.mem_cons_self)
    simp [hb, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma spineFoldSingleOp_commute (P idx : ℕ) (H : BinaryTree ℕ) (op : OneSidedOp)
    (hBST : H.IsBST) (hValid : op.Valid P H) :
    let fop := spineFoldSingleOp H op
    let st := spineFoldTree H
    fop.Valid P st ∧
    fop.step st = spineFoldTree (op.step H) ∧
    op.cascadeRots H ≤
      (if match op with | .pop _ => true | _ => false then 1 else 0) +
        (foldedPopRotsAt idx st fop).length := by
  cases op with
  | push w =>
    rcases hValid with ⟨hw1, hw2, hlt⟩
    cases H with
    | nil =>
      refine ⟨?_, rfl, by simp [OneSidedOp.cascadeRots, spineFoldSingleOp, foldedPopRotsAt]⟩
      simp [spineFoldSingleOp, spineFoldTree, FoldedOp.Valid, hw1, hw2]
    | node b1 l1 r1 =>
      have hkl := toKeyList_spineFoldTree (.node b1 l1 r1)
      have hfr : ∀ p ∈ rightSpineFrames r1, b1 < p.1 := fun p hp =>
        gt_of_IsBST_right l1 b1 r1 hBST (mem_rightSpineFrames_fst hp)
      have hne := spineFoldGo_ne_nil b1 l1 (rightSpineFrames r1)
      refine ⟨?_, ?_, by simp [OneSidedOp.cascadeRots, spineFoldSingleOp, foldedPopRotsAt]⟩
      · refine ⟨hw1, hw2, ?_, ?_, ?_⟩
        · intro k hk
          rw [mem_iff_mem_toKeyList] at hk
          simp only [spineFoldTree, rightSpineFrames] at hk hkl
          rw [hkl, ← mem_iff_mem_toKeyList] at hk
          exact hlt k hk
        · simp [spineFoldTree, rightSpineFrames, hne]
        · intro b hb
          simp only [spineFoldTree, rightSpineFrames, Option.some.injEq] at hb
          subst hb
          simp [spineFoldTree, rightSpineFrames, leftSpine_spineFoldGo]
      · simp only [spineFoldSingleOp, spineFoldTree, rightSpineFrames, FoldedOp.step,
          OneSidedOp.step, SplayTree.push, spineFoldGo]
        rw [modifyLeftAt_spineFoldGo_eq b1 l1 (rightSpineFrames r1) _ hfr]
  | rightSpineLeftRot d =>
    rcases hValid with ⟨hd1, hd2⟩
    cases H with
    | nil => simp [rightSpine] at hd2
    | node b1 l1 r1 =>
      by_cases hdle1 : d ≤ 1
      · have hd_eq : d = 1 := by omega
        subst hd_eq
        cases r1 with
        | nil => simp [rightSpine] at hd2
        | node b2 l2 r2 =>
          have hb1not : b1 ∉ leftSpine l1 := fun h =>
            ne_of_lt (lt_of_IsBST_left l1 b1 _ hBST (mem_of_mem_leftSpine h)) rfl
          have hrs_sorted := pairwise_rightSpine hBST
          simp only [rightSpine, List.pairwise_cons] at hrs_sorted
          have hb1_lt_last :
              b1 < (b1 :: b2 :: rightSpine r2).getLast (by simp) := by
            have hlast_eq : (b1 :: b2 :: rightSpine r2).getLast (by simp) =
                (b2 :: rightSpine r2).getLast (by simp) := by simp
            rw [hlast_eq]
            exact hrs_sorted.1 _ (List.getLast_mem _)
          refine ⟨?_, ?_,
            by simp [OneSidedOp.cascadeRots, spineFoldSingleOp, foldedPopRotsAt]⟩
          · refine ⟨b1, rfl, ?_, ?_⟩
            · simp [spineFoldTree, rightSpineFrames, leftSpine_spineFoldGo]
            · simp only [spineFoldTree, rightSpineFrames, rootKey_spineFoldGo,
                List.map_cons, map_fst_rightSpineFrames, ne_eq, Option.some.injEq]
              exact ne_of_gt hb1_lt_last
          · simp only [spineFoldSingleOp, le_refl, ite_true, spineFoldTree, rightSpineFrames,
              FoldedOp.step, leftSpine_spineFoldGo, List.map_cons, map_fst_rightSpineFrames]
            rw [nextOnSpine_append_of_not_mem _ _ _ hb1not]
            simp [OneSidedOp.step, rotateLeftAtRightSpine1, BinaryTree.rotateLeft,
              rightSpineFrames, spineFoldGo]
      · obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
        have hrs_sorted := pairwise_rightSpine hBST
        simp only [rightSpine, List.length_cons] at hd2 hrs_sorted
        obtain ⟨u, v, hu, hv, hb1u, huv, hvlast, humem, hvmem, hedge, hrot⟩ :=
          upperRot_spineFoldGo b1 l1 r1 m hrs_sorted (by omega)
        have hfop : spineFoldSingleOp (.node b1 l1 r1) (.rightSpineLeftRot (m + 2)) =
            .upperRot u v := by
          simp [spineFoldSingleOp, hdle1, rightSpine, hu, hv]
        rw [hfop]
        refine ⟨?_, ?_, by simp [OneSidedOp.cascadeRots, foldedPopRotsAt]⟩
        · refine ⟨b1, (b1 :: rightSpine r1).getLast (by simp), rfl, ?_, ?_,
            hb1u, huv, hvlast, ?_, ?_, hedge⟩
          · simp [spineFoldTree, rightSpineFrames, rootKey_spineFoldGo, map_fst_rightSpineFrames]
          · simp [spineFoldTree, rightSpineFrames, leftSpine_spineFoldGo]
          · simp only [spineFoldTree, rightSpineFrames, leftSpine_spineFoldGo,
              map_fst_rightSpineFrames, List.mem_append]
            exact Or.inr humem
          · simp only [spineFoldTree, rightSpineFrames, leftSpine_spineFoldGo,
              map_fst_rightSpineFrames, List.mem_append]
            exact Or.inr hvmem
        · simp only [FoldedOp.step, spineFoldTree, rightSpineFrames, OneSidedOp.step,
            rotateLeftAtRightSpine1]
          rw [hrot]
  | pop s =>
    rcases hValid with ⟨hneH, hminH⟩
    cases H with
    | nil => exact absurd rfl hneH
    | node b1 l1 r1 =>
      let ft := spineFoldGo b1 l1 (rightSpineFrames r1)
      have hft_ne : ft ≠ .nil := spineFoldGo_ne_nil b1 l1 (rightSpineFrames r1)
      have hkl := toKeyList_spineFoldTree (.node b1 l1 r1)
      have hmin_ft : ft.minKey? = some s := by
        have hft_eq : ft = (spineFoldTree (.node b1 l1 r1)).1 := rfl
        rw [minKey_eq_head_toKeyList, hft_eq, hkl, ← minKey_eq_head_toKeyList]
        exact hminH
      have hb1not : b1 ∉ leftSpine l1 := fun h =>
        ne_of_lt (lt_of_IsBST_left l1 b1 r1 hBST (mem_of_mem_leftSpine h)) rfl
      have hls_ft : leftSpine ft = leftSpine l1 ++ b1 :: rightSpine r1 := by
        simp [ft, leftSpine_spineFoldGo, map_fst_rightSpineFrames]
      have hsub : takeThrough (leftSpine ft) b1 = leftSpine l1 ++ [b1] := by
        rw [hls_ft, takeThrough_append_of_not_mem _ _ _ hb1not]
      have hfr : ∀ q ∈ rightSpineFrames r1, b1 < q.1 := fun q hq =>
        gt_of_IsBST_right l1 b1 r1 hBST (mem_rightSpineFrames_fst hq)
      refine ⟨?_, ?_, ?_⟩
      · refine ⟨b1, hft_ne, hmin_ft, rfl, ?_⟩
        change b1 ∈ leftSpine ft
        rw [hls_ft]
        simp
      · simp only [spineFoldSingleOp, spineFoldTree, rightSpineFrames, FoldedOp.step]
        change (let ls := leftSpine ft
          let sub := takeThrough ls b1
          let k := sub.length - 1
          let h := (k - 1) / 2
          let t0 := spliceMin ft
          if k = 0 then (t0, if t0 = .nil then none else nextOnSpine ls b1)
          else
            let pairs := (adjacentPairs sub.tail).take h
            let tNew := pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t0
            let bNew := if k = 2 * h + 2 then sub[2 * h + 1]? else some b1
            (tNew, bNew)) = spineFoldTree (popCascade (.node b1 l1 r1))
        dsimp only []
        rw [hsub, List.length_append, List.length_singleton, Nat.add_sub_cancel]
        cases hl1 : l1 with
        | nil =>
          subst hl1
          simp only [leftSpine, List.length_nil, ↓reduceIte, popCascade, popCascadePairs,
            List.nil_append, List.tail_cons, adjacentPairs, List.foldl_nil, spliceMin]
          cases r1 with
          | nil =>
            simp [ft, rightSpineFrames, spineFoldGo, spliceMin, spineFoldTree]
          | node b2 l2 r2 =>
            have ht0 : spliceMin ft = spineFoldGo b2 l2 (rightSpineFrames r2) := by
              simp only [ft, rightSpineFrames, spineFoldGo]
              rw [spliceMin_spineFoldGo_of_ne_nil b2 (.node b1 .nil l2) (rightSpineFrames r2)
                (by simp)]
              rfl
            have ht0_ne : spineFoldGo b2 l2 (rightSpineFrames r2) ≠ .nil :=
              spineFoldGo_ne_nil _ _ _
            have hnext : nextOnSpine (leftSpine ft) b1 = some b2 := by
              rw [hls_ft, nextOnSpine_append_of_not_mem _ _ _ hb1not]
              rfl
            rw [ht0]
            simp only [ht0_ne, ↓reduceIte, hnext]
            rfl
        | node xLast l1L l1R =>
          have hk_pos : (leftSpine (.node xLast l1L l1R)).length ≠ 0 := by simp [leftSpine]
          simp only [hk_pos, ↓reduceIte]
          have ht0 : spliceMin ft =
              spineFoldGo b1 (spliceMin (.node xLast l1L l1R)) (rightSpineFrames r1) := by
            simpa [ft, hl1] using
              spliceMin_spineFoldGo_of_ne_nil b1 (.node xLast l1L l1R) (rightSpineFrames r1)
                (by simp)
          rw [ht0]
          let k := (leftSpine (.node xLast l1L l1R)).length
          let h := (k - 1) / 2
          by_cases heven_k : k = 2 * h + 2
          · -- Even `k = 2 * h + 2` (`k ≥ 2`, so `l1L ≠ .nil`)
            have hl1L_ne : l1L ≠ .nil := by
              intro hnil
              have hk1 : k = 1 := by simp [k, leftSpine, hnil]
              omega
            have hlsL_ne : leftSpine l1L ≠ [] := mt (leftSpine_eq_nil_iff _).mp hl1L_ne
            obtain ⟨v0, lsInit, hlsL⟩ := List.exists_cons_of_ne_nil hlsL_ne
            have hls1 : leftSpine (.node xLast l1L l1R) = v0 :: (lsInit ++ [xLast]) := by
              simp [leftSpine, hlsL]
            have hlen_init : lsInit.length = 2 * h := by
              have hk_eq : k = lsInit.length + 2 := by simp [k, hls1]
              omega
            have hsub_tail : (leftSpine (.node xLast l1L l1R) ++ [b1]).tail =
                lsInit ++ [xLast, b1] := by
              simp [hls1]
            have hadj : adjacentPairs (lsInit ++ [xLast, b1]) =
                adjacentPairs lsInit ++ [(xLast, b1)] := by
              rw [adjacentPairs_append_of_even lsInit [xLast, b1] (by omega)]
              rfl
            have hlen_adj : (adjacentPairs lsInit).length = h := by
              rw [length_adjacentPairs, hlen_init]; omega
            have hpairs : (adjacentPairs (leftSpine (.node xLast l1L l1R) ++ [b1]).tail).take h =
                adjacentPairs lsInit := by
              rw [hsub_tail, hadj, List.take_left' hlen_adj]
            have hsub_idx : (leftSpine (.node xLast l1L l1R) ++ [b1])[2 * h + 1]? = some xLast := by
              have hfull : leftSpine (.node xLast l1L l1R) ++ [b1] =
                  (v0 :: lsInit) ++ [xLast, b1] := by simp [hls1]
              have hlen_pre : (v0 :: lsInit).length = 2 * h + 1 := by simp [hlen_init]
              rw [hfull, List.getElem?_append_right (by omega), hlen_pre, Nat.sub_self]
              rfl
            have hBST_l1 : (BinaryTree.node xLast l1L l1R).IsBST :=
              IsBST_left_of_IsBST (hl1 ▸ hBST)
            have hp_lt_x : ∀ p ∈ adjacentPairs lsInit, p.2 < xLast := fun p hp => by
              have hmem : p.2 ∈ leftSpine l1L := by
                rw [hlsL]; exact List.mem_cons_of_mem _ (snd_mem_of_mem_adjacentPairs hp)
              exact lt_of_IsBST_left l1L xLast l1R hBST_l1 (mem_of_mem_leftSpine hmem)
            have hx_lt_b1 : xLast < b1 :=
              lt_of_IsBST_left (.node xLast l1L l1R) b1 r1 (hl1 ▸ hBST) .here
            have hp_lt_b1 : ∀ p ∈ adjacentPairs lsInit, p.2 < b1 :=
              fun p hp => lt_trans (hp_lt_x p hp) hx_lt_b1
            have hp_lt_fr : ∀ p ∈ adjacentPairs lsInit, ∀ q ∈ rightSpineFrames r1, p.2 < q.1 :=
              fun p hp q hq => lt_trans (hp_lt_b1 p hp) (hfr q hq)
            have hsp_l1 : spliceMin (.node xLast l1L l1R) = .node xLast (spliceMin l1L) l1R :=
              spliceMin_node_of_ne_nil xLast l1R hl1L_ne
            let A' := (adjacentPairs lsInit).foldl
              (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin l1L)
            have hfold_l1 : (adjacentPairs lsInit).foldl
                (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin (.node xLast l1L l1R)) =
                .node xLast A' l1R := by
              rw [hsp_l1, foldl_rotateRightEdge_node_lt _ xLast _ _ hp_lt_x]
            have hpopH : popCascade (.node b1 (.node xLast l1L l1R) r1) =
                .node xLast A' (.node b1 l1R r1) := by
              have hcp : popCascadePairs (.node b1 (.node xLast l1L l1R) r1) =
                  adjacentPairs lsInit ++ [(xLast, b1)] := by
                rw [popCascadePairs, leftSpine, hls1, List.cons_append, List.tail_cons]
                simpa [List.append_assoc] using hadj
              have hspH : spliceMin (.node b1 (.node xLast l1L l1R) r1) =
                  .node b1 (.node xLast (spliceMin l1L) l1R) r1 := by
                rw [spliceMin_node_of_ne_nil b1 r1 (by simp), hsp_l1]
              rw [popCascade, hcp, hspH, List.foldl_append, List.foldl_cons, List.foldl_nil,
                foldl_rotateRightEdge_node_lt _ b1 _ _ hp_lt_b1,
                foldl_rotateRightEdge_node_lt _ xLast _ _ hp_lt_x]
              simp only [rotateRightEdge, lt_irrefl, ↓reduceIte]
              rfl
            change (let pairs := (adjacentPairs (leftSpine (.node xLast l1L l1R) ++ [b1]).tail).take h
              let tNew := pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2)
                (spineFoldGo b1 (spliceMin (.node xLast l1L l1R)) (rightSpineFrames r1))
              let bNew := if k = 2 * h + 2 then
                (leftSpine (.node xLast l1L l1R) ++ [b1])[2 * h + 1]? else some b1
              (tNew, bNew)) = spineFoldTree (popCascade (.node b1 (.node xLast l1L l1R) r1))
            dsimp only []
            rw [hpairs]
            simp only [heven_k, ↓reduceIte, hsub_idx]
            rw [foldl_rotateRightEdge_spineFoldGo_lt _ b1 _ _ hp_lt_b1 hp_lt_fr,
              hfold_l1, hpopH]
            rfl
          · -- Odd `k = 2 * h + 1`
            have hls1_ne : leftSpine (.node xLast l1L l1R) ≠ [] := by simp [leftSpine]
            obtain ⟨v0, ls1, hls1⟩ := List.exists_cons_of_ne_nil hls1_ne
            have hlen_ls1 : ls1.length = 2 * h := by
              have hk_ge1 : 1 ≤ k := Nat.pos_of_ne_zero hk_pos
              have hk_eq : k = ls1.length + 1 := by simp [k, hls1]
              omega
            have hsub_tail : (leftSpine (.node xLast l1L l1R) ++ [b1]).tail = ls1 ++ [b1] := by
              simp [hls1]
            have hadj : adjacentPairs (ls1 ++ [b1]) = adjacentPairs ls1 := by
              rw [adjacentPairs_append_of_even ls1 [b1] (by omega)]
              simp [adjacentPairs]
            have hlen_adj : (adjacentPairs ls1).length = h := by
              rw [length_adjacentPairs, hlen_ls1]; omega
            have hpairs : (adjacentPairs (leftSpine (.node xLast l1L l1R) ++ [b1]).tail).take h =
                adjacentPairs ls1 := by
              rw [hsub_tail, hadj, List.take_of_length_le (le_of_eq hlen_adj)]
            have hp_lt_b1 : ∀ p ∈ adjacentPairs ls1, p.2 < b1 := fun p hp => by
              have hmem : p.2 ∈ leftSpine (.node xLast l1L l1R) := by
                rw [hls1]; exact List.mem_cons_of_mem _ (snd_mem_of_mem_adjacentPairs hp)
              exact lt_of_IsBST_left (.node xLast l1L l1R) b1 r1 (hl1 ▸ hBST)
                (mem_of_mem_leftSpine hmem)
            have hp_lt_fr : ∀ p ∈ adjacentPairs ls1, ∀ q ∈ rightSpineFrames r1, p.2 < q.1 :=
              fun p hp q hq => lt_trans (hp_lt_b1 p hp) (hfr q hq)
            let L_final := (adjacentPairs ls1).foldl
              (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin (.node xLast l1L l1R))
            have hpopH : popCascade (.node b1 (.node xLast l1L l1R) r1) =
                .node b1 L_final r1 := by
              have hcp : popCascadePairs (.node b1 (.node xLast l1L l1R) r1) =
                  adjacentPairs ls1 := by
                rw [popCascadePairs, leftSpine, hls1, List.cons_append, List.tail_cons, hadj]
              rw [popCascade, hcp, spliceMin_node_of_ne_nil b1 r1 (by simp),
                foldl_rotateRightEdge_node_lt _ b1 _ _ hp_lt_b1]
            change (let pairs := (adjacentPairs (leftSpine (.node xLast l1L l1R) ++ [b1]).tail).take h
              let tNew := pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2)
                (spineFoldGo b1 (spliceMin (.node xLast l1L l1R)) (rightSpineFrames r1))
              let bNew := if k = 2 * h + 2 then
                (leftSpine (.node xLast l1L l1R) ++ [b1])[2 * h + 1]? else some b1
              (tNew, bNew)) = spineFoldTree (popCascade (.node b1 (.node xLast l1L l1R) r1))
            dsimp only []
            rw [hpairs]
            simp only [heven_k, ↓reduceIte]
            rw [foldl_rotateRightEdge_spineFoldGo_lt _ b1 _ _ hp_lt_b1 hp_lt_fr, hpopH]
            rfl
      · -- Cascade rotation count bound `k / 2 ≤ 1 + h`
        let sub := leftSpine l1 ++ [b1]
        let k := (leftSpine l1).length
        let h := (k - 1) / 2
        have hcascade : (OneSidedOp.pop s).cascadeRots (.node b1 l1 r1) = k / 2 := by
          simp only [OneSidedOp.cascadeRots, popCascadePairs, leftSpine, length_adjacentPairs,
            List.length_tail, List.length_append, List.length_singleton]
          omega
        have hrots_len :
            (foldedPopRotsAt idx (spineFoldTree (.node b1 l1 r1))
              (spineFoldSingleOp (.node b1 l1 r1) (.pop s))).length = h := by
          simp only [spineFoldSingleOp, spineFoldTree, rightSpineFrames, foldedPopRotsAt]
          rw [show spineFoldGo b1 l1 (rightSpineFrames r1) = ft from rfl, hsub]
          simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
          rw [length_filterMap_of_forall_isSome]
          · exact List.length_range
          · intro idx' hidx'
            rw [List.mem_range] at hidx'
            have hsub_len : (leftSpine l1 ++ [b1]).length = k + 1 := by simp [k]
            have hj1 : 2 * (idx' + 1) - 1 < (leftSpine l1 ++ [b1]).length := by omega
            have hj2 : 2 * (idx' + 1) < (leftSpine l1 ++ [b1]).length := by omega
            have hj3 : 2 * (idx' + 1) + 1 < (leftSpine l1 ++ [b1]).length := by omega
            rw [List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2,
              List.getElem?_eq_getElem hj3]
            rfl
        rw [hcascade, hrots_len]
        simp only [↓reduceIte]
        omega

/-! ## 6. Trajectory Simulation, `Nodup` of `collectFoldedPopRots`, and `lem_3_5_part3b` -/

lemma spineFoldOpList_sim (P idx : ℕ) (t0 : BinaryTree ℕ) (ops : List OneSidedOp)
    (hBST : t0.IsBST) (hKeys : keyFinset t0 ⊆ Finset.Icc 1 P)
    (hValid : ValidOneSidedOps P t0 ops) :
    let fops := spineFoldOpList t0 ops
    ValidFoldedOps P (spineFoldTree t0) fops ∧
    fops.foldl FoldedOp.step (spineFoldTree t0) =
      spineFoldTree (ops.foldl OneSidedOp.step t0) ∧
    oneSidedCascadeCost t0 ops ≤
      (ops.filter (fun | .pop _ => true | _ => false)).length +
        (collectFoldedPopRots idx (spineFoldTree t0) fops).length := by
  induction ops generalizing idx t0 with
  | nil => simp [spineFoldOpList, ValidFoldedOps, oneSidedCascadeCost, collectFoldedPopRots]
  | cons op rest ih =>
    obtain ⟨hv1, hvRest⟩ := hValid
    obtain ⟨hBST1, hKeys1⟩ := oneSidedOp_preserves hBST hKeys hv1
    obtain ⟨hfv1, hstep1, hcost1⟩ := spineFoldSingleOp_commute P idx t0 op hBST hv1
    obtain ⟨hfvRest, hfoldRest, hcostRest⟩ := ih (idx + 1) (op.step t0) hBST1 hKeys1 hvRest
    rw [spineFoldOpList_cons]
    refine ⟨⟨hfv1, ?_⟩, ?_, ?_⟩
    · rwa [hstep1]
    · simp only [List.foldl_cons, hstep1, hfoldRest]
    · simp only [oneSidedCascadeCost, collectFoldedPopRots, List.length_append, hstep1]
      cases op with
      | push w =>
        simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte] at hcost1 ⊢
        omega
      | pop s =>
        simp only [List.filter_cons, ↓reduceIte, List.length_cons] at hcost1 ⊢
        omega
      | rightSpineLeftRot d =>
        simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte] at hcost1 ⊢
        omega

lemma spineFoldOpList_take (t0 : BinaryTree ℕ) (ops : List OneSidedOp) (τ : ℕ) :
    (spineFoldOpList t0 ops).take τ = spineFoldOpList t0 (ops.take τ) := by
  induction ops generalizing t0 τ with
  | nil => simp [spineFoldOpList]
  | cons op rest ih =>
    cases τ with
    | zero => rfl
    | succ τ' => simp [spineFoldOpList_cons, ih]

lemma validOneSidedOps_take (P : ℕ) (t0 : BinaryTree ℕ) (ops : List OneSidedOp) (τ : ℕ)
    (hValid : ValidOneSidedOps P t0 ops) :
    ValidOneSidedOps P t0 (ops.take τ) := by
  induction ops generalizing t0 τ with
  | nil => simp [ValidOneSidedOps]
  | cons op rest ih =>
    cases τ with
    | zero => trivial
    | succ τ' => exact ⟨hValid.1, ih (op.step t0) τ' hValid.2⟩

lemma filterMap_push_spineFoldOpList (f : FoldedOp → Option ℕ) (g : OneSidedOp → Option ℕ)
    (hpush : ∀ w, f (.push w) = g (.push w))
    (hpop : ∀ s, f (.pop s) = none ∧ g (.pop s) = none)
    (hrot : ∀ d, g (.rightSpineLeftRot d) = none)
    (hshift : f .shift = none)
    (hurot : ∀ u v, f (.upperRot u v) = none)
    (t0 : BinaryTree ℕ) (ops : List OneSidedOp) :
    (spineFoldOpList t0 ops).filterMap f = ops.filterMap g := by
  induction ops generalizing t0 with
  | nil => rfl
  | cons op rest ih =>
    rw [spineFoldOpList_cons]
    cases op with
    | push w => simp only [spineFoldSingleOp, List.filterMap_cons, hpush, ih]
    | pop s => simp [spineFoldSingleOp, (hpop s).1, (hpop s).2, ih]
    | rightSpineLeftRot d =>
      by_cases hd : d ≤ 1
      · simp [spineFoldSingleOp, hd, hshift, hrot, ih]
      · simp only [spineFoldSingleOp, hd, ↓reduceIte]
        cases (rightSpine t0)[d - 2]? <;> cases (rightSpine t0)[d - 1]? <;>
          simp [hshift, hurot, hrot, ih]

lemma filterMap_pop_spineFoldOpList (f : FoldedOp → Option ℕ) (g : OneSidedOp → Option ℕ)
    (hpush : ∀ w, f (.push w) = none ∧ g (.push w) = none)
    (hpop : ∀ s, f (.pop s) = g (.pop s))
    (hrot : ∀ d, g (.rightSpineLeftRot d) = none)
    (hshift : f .shift = none)
    (hurot : ∀ u v, f (.upperRot u v) = none)
    (t0 : BinaryTree ℕ) (ops : List OneSidedOp) :
    (spineFoldOpList t0 ops).filterMap f = ops.filterMap g := by
  induction ops generalizing t0 with
  | nil => rfl
  | cons op rest ih =>
    rw [spineFoldOpList_cons]
    cases op with
    | push w => simp [spineFoldSingleOp, (hpush w).1, (hpush w).2, ih]
    | pop s => simp only [spineFoldSingleOp, List.filterMap_cons, hpop, ih]
    | rightSpineLeftRot d =>
      by_cases hd : d ≤ 1
      · simp [spineFoldSingleOp, hd, hshift, hrot, ih]
      · simp only [spineFoldSingleOp, hd, ↓reduceIte]
        cases (rightSpine t0)[d - 2]? <;> cases (rightSpine t0)[d - 1]? <;>
          simp [hshift, hurot, hrot, ih]

lemma filter_upper_spineFoldOpList (p : FoldedOp → Bool) (q : OneSidedOp → Bool)
    (hp_sh : p .shift = true) (hp_ur : ∀ u v, p (.upperRot u v) = true)
    (hp_pu : ∀ w, p (.push w) = false) (hp_po : ∀ s, p (.pop s) = false)
    (hq_pu : ∀ w, q (.push w) = false) (hq_po : ∀ s, q (.pop s) = false)
    (hq_ro : ∀ d, q (.rightSpineLeftRot d) = true)
    (t0 : BinaryTree ℕ) (ops : List OneSidedOp) :
    ((spineFoldOpList t0 ops).filter p).length = (ops.filter q).length := by
  induction ops generalizing t0 with
  | nil => rfl
  | cons op rest ih =>
    rw [spineFoldOpList_cons]
    cases op with
    | push w => simp [spineFoldSingleOp, hp_pu, hq_pu, ih]
    | pop s => simp [spineFoldSingleOp, hp_po, hq_po, ih]
    | rightSpineLeftRot d =>
      by_cases hd : d ≤ 1
      · simp [spineFoldSingleOp, hd, hp_sh, hq_ro, ih]
      · simp only [spineFoldSingleOp, hd, ↓reduceIte]
        cases (rightSpine t0)[d - 2]? <;> cases (rightSpine t0)[d - 1]? <;>
          simp [hp_sh, hp_ur, hq_ro, ih]

lemma stepIdx_of_mem_foldedPopRotsAt {idx : ℕ} {st : BinaryTree ℕ × Option ℕ} {op : FoldedOp}
    {e : InternalPopRot} (he : e ∈ foldedPopRotsAt idx st op) : e.stepIdx = idx := by
  rcases st with ⟨t, _ | b⟩ <;> cases op <;> simp only [foldedPopRotsAt] at he
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · rw [List.mem_filterMap] at he
    obtain ⟨a, _, ha⟩ := he
    split at ha <;> simp at ha
    subst ha; rfl

lemma stepIdx_ge_of_mem_collectFoldedPopRots {idx : ℕ} {st : BinaryTree ℕ × Option ℕ}
    {fops : List FoldedOp} {e : InternalPopRot}
    (he : e ∈ collectFoldedPopRots idx st fops) : idx ≤ e.stepIdx := by
  induction fops generalizing idx st with
  | nil => simp [collectFoldedPopRots] at he
  | cons op rest ih =>
    simp only [collectFoldedPopRots, List.mem_append] at he
    rcases he with h1 | h2
    · rw [stepIdx_of_mem_foldedPopRotsAt h1]
    · exact le_of_lt (Nat.lt_of_succ_le (ih h2))

lemma nodup_foldedPopRotsAt (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (op : FoldedOp) :
    (foldedPopRotsAt idx st op).Nodup := by
  rcases st with ⟨t, _ | b⟩ <;> cases op <;> simp only [foldedPopRotsAt]
  · exact List.nodup_nil
  · exact List.nodup_nil
  · exact List.nodup_nil
  · exact List.nodup_nil
  · exact List.nodup_nil
  · exact List.nodup_nil
  · exact List.nodup_nil
  · apply List.Nodup.filterMap _ List.nodup_range
    intro a1 a2 e he1 he2
    have hj1 : e.j = a1 + 1 := by
      split at he1 <;> simp at he1; subst he1; rfl
    have hj2 : e.j = a2 + 1 := by
      split at he2 <;> simp at he2; subst he2; rfl
    omega

lemma nodup_collectFoldedPopRots (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (fops : List FoldedOp) :
    (collectFoldedPopRots idx st fops).Nodup := by
  induction fops generalizing idx st with
  | nil => exact List.nodup_nil
  | cons op rest ih =>
    simp only [collectFoldedPopRots, List.nodup_append]
    refine ⟨nodup_foldedPopRotsAt idx st op, ih (idx + 1) (op.step st), ?_⟩
    intro e1 he1 e2 he2 heq
    have h1 := stepIdx_of_mem_foldedPopRotsAt he1
    have h2 := stepIdx_ge_of_mem_collectFoldedPopRots he2
    rw [heq] at h1
    omega

theorem lem_3_5_part3b (P : ℕ) (hP : 1 ≤ P) (exec : OneSidedPopExec P) :
    exec.kL ≤ 2 * P - 2 ∧
    ∃ proc : FoldedPopProcess P,
      proc.steps = spineFoldOpList .nil exec.steps ∧
      (∀ τ : ℕ, τ ≤ exec.steps.length → proc.stateAt τ = spineFoldTree (exec.treeAt τ)) ∧
      exec.cPop ≤ P + proc.J := by
  have hkL := exec_kL_le_two_mul_sub_two P hP exec
  refine ⟨hkL, ?_⟩
  obtain ⟨hValidF, hEndF, hCostF⟩ :=
    spineFoldOpList_sim P 0 .nil exec.steps
      BinaryTree.IsBST.left (by simp [keyFinset]) exec.hValid
  rw [exec.hEndEmpty] at hEndF
  have hUpperLen :
      ∀ p : FoldedOp → Bool,
        p .shift = true → (∀ u v, p (.upperRot u v) = true) →
        (∀ w, p (.push w) = false) → (∀ s, p (.pop s) = false) →
        ((spineFoldOpList .nil exec.steps).filter p).length < 2 * P := by
    intro p h1 h2 h3 h4
    have hlen : ((spineFoldOpList .nil exec.steps).filter p).length = exec.kL := by
      unfold OneSidedPopExec.kL
      exact filter_upper_spineFoldOpList p _ h1 h2 h3 h4
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) .nil exec.steps
    omega
  let proc : FoldedPopProcess P := {
    steps := spineFoldOpList .nil exec.steps
    hValid := hValidF
    hEndEmpty := hEndF
    hPushCount :=
      Eq.trans (congrArg List.length (filterMap_push_spineFoldOpList _ _
        (fun _ => rfl) (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl) rfl (fun _ _ => rfl)
        .nil exec.steps)) exec.hPushCount
    hPopSeq :=
      Eq.trans (filterMap_pop_spineFoldOpList _ _
        (fun _ => ⟨rfl, rfl⟩) (fun _ => rfl) (fun _ => rfl) rfl (fun _ _ => rfl)
        .nil exec.steps) exec.hPopSeq
    hKLBound := Or.inr ⟨hP,
      hUpperLen _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)⟩
  }
  refine ⟨proc, rfl, ?_, ?_⟩
  · intro τ _
    simp only [FoldedPopProcess.stateAt, OneSidedPopExec.treeAt, proc]
    rw [spineFoldOpList_take]
    exact (spineFoldOpList_sim P 0 .nil (exec.steps.take τ)
      BinaryTree.IsBST.left (by simp [keyFinset])
      (validOneSidedOps_take P .nil exec.steps τ exec.hValid)).2.1
  · have hPopTotal := exec_pop_filter_len exec
    have hJ : proc.J =
        (collectFoldedPopRots 0 (.nil, none) (spineFoldOpList .nil exec.steps)).length := by
      unfold FoldedPopProcess.J FoldedPopProcess.rInt
      exact List.toFinset_card_of_nodup (nodup_collectFoldedPopRots 0 (.nil, none) proc.steps)
    have hPopEq :
        (exec.steps.filter (fun | .pop _ => true | _ => false)).length = P := by
      refine Eq.trans (congrArg List.length ?_) hPopTotal
      exact List.filter_congr fun x _ => by cases x <;> rfl
    unfold OneSidedPopExec.cPop
    rw [hJ]
    dsimp only [spineFoldTree] at hCostF
    omega

end SpineFoldInternal

namespace EmptyingSimInternal

open SplayTree BinaryTree

/-! ## Section 1: Basic Tree, Spine, Rotation, and Left-Interval Projection Lemmas -/

theorem mem_keyFinset_iff {α : Type} [DecidableEq α] (t : BinaryTree α) (x : α) :
    x ∈ keyFinset t ↔ x ∈ t := by
  induction t with
  | nil => simp [keyFinset]
  | node k l r ihl ihr =>
    simp [keyFinset, ihl, ihr, BinaryTree.mem_node_iff]

theorem toKeyList_toFinset_eq_keyFinset {α : Type} [DecidableEq α] (t : BinaryTree α) :
    t.toKeyList.toFinset = keyFinset t := by
  ext x
  simp [mem_keyFinset_iff, BinaryTree.mem_iff_mem_toKeyList]

theorem nodup_toKeyList_of_isBST {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    t.toKeyList.Nodup := by
  have h := (SplayTree.IsBST_iff_toKeyList_sorted t).mp ht
  exact h.imp (fun hab => ne_of_lt hab)

theorem card_keyFinset_of_isBST {α : Type} [LinearOrder α] [DecidableEq α]
    {t : BinaryTree α} (ht : t.IsBST) :
    (keyFinset t).card = t.num_nodes := by
  rw [← toKeyList_toFinset_eq_keyFinset, List.toFinset_card_of_nodup (nodup_toKeyList_of_isBST ht),
    BinaryTree.num_nodes_eq_length_toKeyList]

theorem num_nodes_map {α β : Type} (f : α → β) (t : BinaryTree α) :
    (t.map f).num_nodes = t.num_nodes := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    show 1 + (l.map f).num_nodes + (r.map f).num_nodes = 1 + l.num_nodes + r.num_nodes
    omega

theorem minKey_eq_head_toKeyList {α : Type} (t : BinaryTree α) :
    t.minKey? = t.toKeyList.head? := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    simp only [BinaryTree.minKey?, BinaryTree.toKeyList_node, ihl]
    cases l.toKeyList <;> rfl

theorem maxKey_eq_getLast_toKeyList {α : Type} (t : BinaryTree α) :
    t.maxKey? = t.toKeyList.getLast? := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    cases r with
    | nil =>
      simp [BinaryTree.maxKey?, BinaryTree.toKeyList_node]
    | node rk rl rr =>
      have hr_ne : (BinaryTree.node rk rl rr).toKeyList ≠ [] := by
        simp [BinaryTree.toKeyList_node]
      have hmax_some : ∃ m, (BinaryTree.node rk rl rr).maxKey? = some m := by
        rw [ihr]
        exact Option.ne_none_iff_exists'.mp (mt List.getLast?_eq_none_iff.mp hr_ne)
      obtain ⟨m, hm⟩ := hmax_some
      have h_eq : (BinaryTree.node k l (.node rk rl rr)).maxKey? = some m := by
        show (match (BinaryTree.node rk rl rr).maxKey? with
              | none => some k
              | some x => some x) = some m
        rw [hm]
      rw [h_eq, BinaryTree.toKeyList_node, List.append_assoc,
        List.getLast?_append_of_ne_nil _ (by simp),
        List.getLast?_append_of_ne_nil _ hr_ne, ← ihr, hm]

theorem minKey_eq_none_iff {α : Type} (t : BinaryTree α) :
    t.minKey? = none ↔ t = .nil := by
  rw [minKey_eq_head_toKeyList]
  cases h : t.toKeyList with
  | nil =>
    simp [BinaryTree.eq_nil_of_toKeyList_eq_nil h]
  | cons a as =>
    simp only [List.head?_cons, reduceCtorEq, false_iff]
    rintro rfl
    simp at h

theorem maxKey_eq_none_iff {α : Type} (t : BinaryTree α) :
    t.maxKey? = none ↔ t = .nil := by
  rw [maxKey_eq_getLast_toKeyList]
  cases h : t.toKeyList with
  | nil =>
    simp [BinaryTree.eq_nil_of_toKeyList_eq_nil h]
  | cons a as =>
    have hne : t.toKeyList ≠ [] := by simp [h]
    rw [← h]
    simp only [List.getLast?_eq_none_iff, hne, false_iff]
    rintro rfl
    simp at hne

theorem exists_minKey_of_ne_nil {α : Type} {t : BinaryTree α} (ht : t ≠ .nil) :
    ∃ x, t.minKey? = some x := by
  cases hm : t.minKey? with
  | none => exact absurd ((minKey_eq_none_iff t).mp hm) ht
  | some x => exact ⟨x, rfl⟩

theorem exists_maxKey_of_ne_nil {α : Type} {t : BinaryTree α} (ht : t ≠ .nil) :
    ∃ x, t.maxKey? = some x := by
  cases hm : t.maxKey? with
  | none => exact absurd ((maxKey_eq_none_iff t).mp hm) ht
  | some x => exact ⟨x, rfl⟩

theorem mem_of_minKey {α : Type} {t : BinaryTree α} {x : α} (h : t.minKey? = some x) :
    x ∈ t := by
  rw [BinaryTree.mem_iff_mem_toKeyList]
  rw [minKey_eq_head_toKeyList] at h
  exact List.mem_of_head? h

theorem mem_of_maxKey {α : Type} {t : BinaryTree α} {x : α} (h : t.maxKey? = some x) :
    x ∈ t := by
  rw [BinaryTree.mem_iff_mem_toKeyList]
  rw [maxKey_eq_getLast_toKeyList] at h
  exact List.mem_of_getLast? h

theorem minKey_le_of_mem {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST)
    {m x : α} (hmin : t.minKey? = some m) (hx : x ∈ t) : m ≤ x := by
  rw [minKey_eq_head_toKeyList] at hmin
  rw [BinaryTree.mem_iff_mem_toKeyList] at hx
  have hsort := (SplayTree.IsBST_iff_toKeyList_sorted t).mp ht
  cases hlist : t.toKeyList with
  | nil => simp [hlist] at hmin
  | cons a rest =>
    simp only [hlist, List.head?_cons, Option.some.injEq] at hmin
    subst hmin
    rw [hlist] at hsort hx
    rcases List.mem_cons.mp hx with rfl | hrest
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp hsort).1 x hrest)

theorem le_maxKey_of_mem {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST)
    {m x : α} (hmax : t.maxKey? = some m) (hx : x ∈ t) : x ≤ m := by
  rw [maxKey_eq_getLast_toKeyList] at hmax
  rw [BinaryTree.mem_iff_mem_toKeyList] at hx
  have hsort := (SplayTree.IsBST_iff_toKeyList_sorted t).mp ht
  have hrev : t.toKeyList.reverse.Pairwise (· > ·) := List.Pairwise.reverse hsort
  have hhead : t.toKeyList.reverse.head? = some m := by
    rwa [List.head?_reverse]
  have hxrev : x ∈ t.toKeyList.reverse := List.mem_reverse.mpr hx
  cases hlist : t.toKeyList.reverse with
  | nil => simp [hlist] at hhead
  | cons a rest =>
    simp only [hlist, List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rw [hlist] at hrev hxrev
    rcases List.mem_cons.mp hxrev with rfl | hrest
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp hrev).1 x hrest)

theorem mem_splay_pop_iff {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST)
    {q : α} (hmin : t.minKey? = some q) (x : α) :
    x ∈ SplayTree.pop t ↔ x ∈ t ∧ x ≠ q := by
  have hq_mem : q ∈ t := mem_of_minKey hmin
  obtain ⟨lr, rr, hsplay⟩ := SplayTree.splay_root_of_contains' t q ht hq_mem
  have hs_bst : (splay t q).IsBST := SplayTree.IsBST_splay t q ht
  have hs_keys : (splay t q).toKeyList = t.toKeyList := SplayTree.toKeyList_splay t q
  rw [hsplay] at hs_bst hs_keys
  have hlr_nil : lr = .nil := by
    cases lr with
    | nil => rfl
    | node lk ll lr' =>
      have hlt : lk < q := BinaryTree.lt_of_IsBST_left _ q rr hs_bst .here
      have hlk_mem : lk ∈ t := by
        rw [BinaryTree.mem_iff_mem_toKeyList, ← hs_keys]
        simp [BinaryTree.toKeyList_node]
      exact absurd (minKey_le_of_mem ht hmin hlk_mem) (not_le.mpr hlt)
  subst hlr_nil
  have hpop : SplayTree.pop t = rr := by
    simp [SplayTree.pop, hmin, hsplay]
  rw [hpop, BinaryTree.mem_iff_mem_toKeyList, BinaryTree.mem_iff_mem_toKeyList]
  have hlist : q :: rr.toKeyList = t.toKeyList := by
    simpa [BinaryTree.toKeyList_node] using hs_keys
  have hnodup : (q :: rr.toKeyList).Nodup := by
    rw [hlist]; exact nodup_toKeyList_of_isBST ht
  rw [← hlist]
  have hq_not_rr : q ∉ rr.toKeyList := (List.nodup_cons.mp hnodup).1
  simp only [List.mem_cons]
  constructor
  · intro hx
    exact ⟨Or.inr hx, fun heq => hq_not_rr (heq ▸ hx)⟩
  · rintro ⟨rfl | hx, hne⟩
    · exact absurd rfl hne
    · exact hx

theorem mem_splay_eject_iff {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST)
    {q : α} (hmax : t.maxKey? = some q) (x : α) :
    x ∈ SplayTree.eject t ↔ x ∈ t ∧ x ≠ q := by
  have hq_mem : q ∈ t := mem_of_maxKey hmax
  obtain ⟨lr, rr, hsplay⟩ := SplayTree.splay_root_of_contains' t q ht hq_mem
  have hs_bst : (splay t q).IsBST := SplayTree.IsBST_splay t q ht
  have hs_keys : (splay t q).toKeyList = t.toKeyList := SplayTree.toKeyList_splay t q
  rw [hsplay] at hs_bst hs_keys
  have hrr_nil : rr = .nil := by
    cases rr with
    | nil => rfl
    | node rk rl rr' =>
      have hgt : q < rk := BinaryTree.gt_of_IsBST_right lr q _ hs_bst .here
      have hrk_mem : rk ∈ t := by
        rw [BinaryTree.mem_iff_mem_toKeyList, ← hs_keys]
        simp [BinaryTree.toKeyList_node]
      exact absurd (le_maxKey_of_mem ht hmax hrk_mem) (not_le.mpr hgt)
  subst hrr_nil
  have hej : SplayTree.eject t = lr := by
    simp [SplayTree.eject, hmax, hsplay]
  rw [hej, BinaryTree.mem_iff_mem_toKeyList, BinaryTree.mem_iff_mem_toKeyList]
  have hlist : lr.toKeyList ++ [q] = t.toKeyList := by
    simpa [BinaryTree.toKeyList_node] using hs_keys
  have hnodup : (lr.toKeyList ++ [q]).Nodup := by
    rw [hlist]; exact nodup_toKeyList_of_isBST ht
  rw [← hlist]
  have hq_not_lr : q ∉ lr.toKeyList := by
    intro hmem
    have := (List.nodup_append.mp hnodup).2.2 q hmem q (List.mem_singleton_self q)
    exact this rfl
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · intro hx
    exact ⟨Or.inl hx, fun heq => hq_not_lr (heq ▸ hx)⟩
  · rintro ⟨hx | rfl, hne⟩
    · exact hx
    · exact absurd rfl hne

theorem toKeyList_rotateRightEdge {α : Type} [LinearOrder α]
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
        split_ifs
        · simp [BinaryTree.toKeyList_node, List.append_assoc]
        · rfl

theorem toKeyList_rotateLeftEdge {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) :
    (rotateLeftEdge t x p).toKeyList = t.toKeyList := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp only [rotateLeftEdge]
    split_ifs with h1 h2
    · simp [ihl]
    · simp [ihr]
    · cases r with
      | nil => rfl
      | node rx b c =>
        dsimp only
        split_ifs
        · simp [BinaryTree.toKeyList_node, List.append_assoc]
        · rfl

theorem isBST_rotateRightEdge {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) (x p : α) :
    (rotateRightEdge t x p).IsBST :=
  SplayTree.IsBST_of_toKeyList_eq (toKeyList_rotateRightEdge t x p) ht

theorem isBST_rotateLeftEdge {α : Type} [LinearOrder α]
    {t : BinaryTree α} (ht : t.IsBST) (x p : α) :
    (rotateLeftEdge t x p).IsBST :=
  SplayTree.IsBST_of_toKeyList_eq (toKeyList_rotateLeftEdge t x p) ht

theorem toKeyList_spliceMin_sub {α : Type} (t : BinaryTree α) :
    ∀ x ∈ (spliceMin t).toKeyList, x ∈ t.toKeyList := by
  induction t with
  | nil => intro x hx; cases hx
  | node k l r ihl _ =>
    cases l with
    | nil =>
      intro x hx
      simp [spliceMin, BinaryTree.toKeyList_node] at hx ⊢
      exact Or.inr hx
    | node lk ll lr =>
      intro x hx
      have hsp : spliceMin (.node k (.node lk ll lr) r) =
          .node k (spliceMin (.node lk ll lr)) r := rfl
      rw [hsp, BinaryTree.toKeyList_node] at hx
      rw [← BinaryTree.mem_iff_mem_toKeyList]
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (hxl | rfl) | hxr
      · exact .left (BinaryTree.mem_iff_mem_toKeyList.mpr (ihl x hxl))
      · exact .here
      · exact .right (BinaryTree.mem_iff_mem_toKeyList.mpr hxr)

theorem isBST_spliceMin {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (spliceMin t).IsBST := by
  induction t with
  | nil => exact ht
  | node k l r ihl _ =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    cases l with
    | nil => exact hr
    | node lk ll lr =>
      have hsp : spliceMin (.node k (.node lk ll lr) r) =
          .node k (spliceMin (.node lk ll lr)) r := rfl
      rw [hsp]
      refine SplayDeque.Direct.isBSTNode k _ r ?_ hgt (ihl hl) hr
      rw [SplayDeque.Direct.forallTree_iff] at hlt ⊢
      intro x hx
      apply hlt x
      rw [BinaryTree.mem_iff_mem_toKeyList] at hx ⊢
      exact toKeyList_spliceMin_sub _ x hx

theorem toKeyList_spliceMax_sub {α : Type} (t : BinaryTree α) :
    ∀ x ∈ (spliceMax t).toKeyList, x ∈ t.toKeyList := by
  induction t with
  | nil => intro x hx; cases hx
  | node k l r _ ihr =>
    cases r with
    | nil =>
      intro x hx
      simp [spliceMax, BinaryTree.toKeyList_node] at hx ⊢
      exact Or.inl hx
    | node rk rl rr =>
      intro x hx
      have hsp : spliceMax (.node k l (.node rk rl rr)) =
          .node k l (spliceMax (.node rk rl rr)) := rfl
      rw [hsp, BinaryTree.toKeyList_node] at hx
      rw [← BinaryTree.mem_iff_mem_toKeyList]
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (hxl | rfl) | hxr
      · exact .left (BinaryTree.mem_iff_mem_toKeyList.mpr hxl)
      · exact .here
      · exact .right (BinaryTree.mem_iff_mem_toKeyList.mpr (ihr x hxr))

theorem isBST_spliceMax {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (spliceMax t).IsBST := by
  induction t with
  | nil => exact ht
  | node k l r _ ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    cases r with
    | nil => exact hl
    | node rk rl rr =>
      have hsp : spliceMax (.node k l (.node rk rl rr)) =
          .node k l (spliceMax (.node rk rl rr)) := rfl
      rw [hsp]
      refine SplayDeque.Direct.isBSTNode k l _ hlt ?_ hl (ihr hr)
      rw [SplayDeque.Direct.forallTree_iff] at hgt ⊢
      intro x hx
      apply hgt x
      rw [BinaryTree.mem_iff_mem_toKeyList] at hx ⊢
      exact toKeyList_spliceMax_sub _ x hx

theorem restrictTree_eq_self_of_forall {α : Type} (t : BinaryTree α) (S : Set α)
    (h : ∀ x ∈ t, x ∈ S) : restrictTree t S = t := by
  induction t with
  | nil => simp [restrictTree]
  | node u A B ihA ihB =>
    have hu : u ∈ S := h u .here
    have hA : ∀ x ∈ A, x ∈ S := fun x hx => h x (.left hx)
    have hB : ∀ x ∈ B, x ∈ S := fun x hx => h x (.right hx)
    simp [restrictTree, hu, ihA hA, ihB hB]

/-- Downward-closed BST restriction `projL L t = restrictTree t {x | x ≤ L}`. -/
noncomputable abbrev projL {α : Type} [LinearOrder α] (L : α) (t : BinaryTree α) : BinaryTree α :=
  restrictTree t {x : α | x ≤ L}

@[simp] theorem projL_nil {α : Type} [LinearOrder α] (L : α) :
    projL L (.nil : BinaryTree α) = .nil := by
  simp [projL, restrictTree]

theorem projL_node_le {α : Type} [LinearOrder α] (L u : α) (A B : BinaryTree α)
    (ht : (BinaryTree.node u A B).IsBST) (hu : u ≤ L) :
    projL L (.node u A B) = .node u A (projL L B) := by
  have hA : ∀ x ∈ A, x ∈ {x : α | x ≤ L} := fun x hx =>
    le_trans (le_of_lt (BinaryTree.lt_of_IsBST_left A u B ht hx)) hu
  simp [projL, restrictTree, hu, restrictTree_eq_self_of_forall A _ hA]

theorem projL_node_gt {α : Type} [LinearOrder α] (L u : α) (A B : BinaryTree α)
    (ht : (BinaryTree.node u A B).IsBST) (hu : L < u) :
    projL L (.node u A B) = projL L A := by
  have hnotu : ¬ (u ≤ L) := not_le.mpr hu
  have hnotB : ¬ (∃ b ∈ B, b ≤ L) := by
    rintro ⟨b, hb, hbL⟩
    exact absurd (lt_trans hu (BinaryTree.gt_of_IsBST_right A u B ht hb)) (not_lt.mpr hbL)
  simp [projL, restrictTree, hnotu, hnotB]

theorem toKeyList_projL {α : Type} [LinearOrder α] (L : α) :
    ∀ {t : BinaryTree α}, t.IsBST →
      (projL L t).toKeyList = (open Classical in t.toKeyList.filter (fun x => decide (x ≤ L)))
  | .nil, _ => by simp
  | .node u A B, ht => by
    have hA_bst := BinaryTree.IsBST_left_of_IsBST ht
    have hB_bst := BinaryTree.IsBST_right_of_IsBST ht
    by_cases hu : u ≤ L
    · rw [projL_node_le L u A B ht hu, BinaryTree.toKeyList_node, BinaryTree.toKeyList_node,
        toKeyList_projL L hB_bst]
      have hA_all : (open Classical in A.toKeyList.filter (fun x => decide (x ≤ L))) =
          A.toKeyList := by
        open Classical in
        rw [List.filter_eq_self]
        intro x hx
        rw [← BinaryTree.mem_iff_mem_toKeyList] at hx
        simp [le_trans (le_of_lt (BinaryTree.lt_of_IsBST_left A u B ht hx)) hu]
      open Classical in
      simp [List.filter_append, hu, hA_all]
    · have hgt : L < u := lt_of_not_ge hu
      rw [projL_node_gt L u A B ht hgt, BinaryTree.toKeyList_node, toKeyList_projL L hA_bst]
      have hB_none : (open Classical in B.toKeyList.filter (fun x => decide (x ≤ L))) = [] := by
        open Classical in
        rw [List.filter_eq_nil_iff]
        intro x hx
        rw [← BinaryTree.mem_iff_mem_toKeyList] at hx
        simp [not_le.mpr (lt_trans hgt (BinaryTree.gt_of_IsBST_right A u B ht hx))]
      open Classical in
      simp [List.filter_append, hu, hB_none]

theorem isBST_projL {α : Type} [LinearOrder α] (L : α) {t : BinaryTree α} (ht : t.IsBST) :
    (projL L t).IsBST := by
  rw [SplayTree.IsBST_iff_toKeyList_sorted, toKeyList_projL L ht]
  open Classical in
  exact List.Pairwise.filter _ ((SplayTree.IsBST_iff_toKeyList_sorted t).mp ht)

theorem mem_projL_iff {α : Type} [LinearOrder α] (L : α) {t : BinaryTree α} (ht : t.IsBST)
    (x : α) : x ∈ projL L t ↔ x ∈ t ∧ x ≤ L := by
  open Classical in
  rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_projL L ht, List.mem_filter,
    ← BinaryTree.mem_iff_mem_toKeyList, decide_eq_true_eq]

theorem mem_leftSpine {α : Type} {t : BinaryTree α} {x : α} (hx : x ∈ leftSpine t) : x ∈ t := by
  induction t with
  | nil => simp [leftSpine] at hx
  | node k l r ihl _ =>
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with hl | rfl
    · exact .left (ihl hl)
    · exact .here

theorem mem_rightSpine {α : Type} {t : BinaryTree α} {x : α} (hx : x ∈ rightSpine t) : x ∈ t := by
  induction t with
  | nil => simp [rightSpine] at hx
  | node k l r _ ihr =>
    simp only [rightSpine, List.mem_cons] at hx
    rcases hx with rfl | hr
    · exact .here
    · exact .right (ihr hr)

theorem leftSpine_projL {α : Type} [LinearOrder α] (L : α) :
    ∀ {t : BinaryTree α}, t.IsBST →
      leftSpine (projL L t) = (open Classical in (leftSpine t).filter (fun x => decide (x ≤ L)))
  | .nil, _ => by simp [leftSpine]
  | .node u A B, ht => by
    have hA_bst := BinaryTree.IsBST_left_of_IsBST ht
    by_cases hu : u ≤ L
    · rw [projL_node_le L u A B ht hu]
      have hA_all : (open Classical in (leftSpine A).filter (fun x => decide (x ≤ L))) =
          leftSpine A := by
        open Classical in
        rw [List.filter_eq_self]
        intro x hx
        simp [le_trans (le_of_lt (BinaryTree.lt_of_IsBST_left A u B ht (mem_leftSpine hx))) hu]
      open Classical in
      simp [leftSpine, List.filter_append, hu, hA_all]
    · have hgt : L < u := lt_of_not_ge hu
      rw [projL_node_gt L u A B ht hgt, leftSpine_projL L hA_bst]
      open Classical in
      simp [leftSpine, List.filter_append, hu]

theorem pairwise_leftSpine {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    rw [leftSpine, List.pairwise_append]
    refine ⟨ihl (BinaryTree.IsBST_left_of_IsBST ht), List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    rw [hb]
    exact BinaryTree.lt_of_IsBST_left l k r ht (mem_leftSpine ha)

theorem pairwise_rightSpine {α : Type} [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (rightSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [rightSpine]
  | node k l r _ ihr =>
    simp only [rightSpine, List.pairwise_cons]
    refine ⟨?_, ihr (BinaryTree.IsBST_right_of_IsBST ht)⟩
    intro b hb
    exact BinaryTree.gt_of_IsBST_right l k r ht (mem_rightSpine hb)

theorem projL_spliceMin {α : Type} [LinearOrder α] (L : α) :
    ∀ {t : BinaryTree α} {xMin : α}, t.IsBST → t.minKey? = some xMin → xMin ≤ L →
      projL L (spliceMin t) = spliceMin (projL L t)
  | .nil, _, _, hmin, _ => by simp [BinaryTree.minKey?] at hmin
  | .node u .nil B, xMin, ht, hmin, hxL => by
    simp only [BinaryTree.minKey?, Option.some.injEq] at hmin
    subst hmin
    rw [projL_node_le L u .nil B ht hxL]
    rfl
  | .node u (.node lk ll lr) B, xMin, ht, hmin, hxL => by
    have hL_bst := BinaryTree.IsBST_left_of_IsBST ht
    have hsp_bst := isBST_spliceMin ht
    obtain ⟨m', hm'⟩ := exists_minKey_of_ne_nil (t := BinaryTree.node lk ll lr) (by simp)
    have hmin_eq : (BinaryTree.node u (.node lk ll lr) B).minKey? = some m' := by
      show (match (BinaryTree.node lk ll lr).minKey? with
            | none => some u | some x => some x) = some m'
      rw [hm']
    rw [hmin_eq, Option.some.injEq] at hmin
    subst m'
    have hx_memL : xMin ∈ BinaryTree.node lk ll lr := mem_of_minKey hm'
    have hx_mem_proj : xMin ∈ projL L (.node lk ll lr) :=
      (mem_projL_iff L hL_bst xMin).mpr ⟨hx_memL, hxL⟩
    have hproj_ne : projL L (.node lk ll lr) ≠ .nil := BinaryTree.ne_nil_of_mem xMin hx_mem_proj
    have hsp_eq : spliceMin (.node u (.node lk ll lr) B) =
        .node u (spliceMin (.node lk ll lr)) B := rfl
    rw [hsp_eq] at hsp_bst ⊢
    by_cases hu : u ≤ L
    · rw [projL_node_le L u _ B hsp_bst hu, projL_node_le L u _ B ht hu]
      cases hproj : projL L (.node lk ll lr) with
      | nil => exact absurd hproj hproj_ne
      | node pk pl pr =>
        have hproj_self : projL L (.node lk ll lr) = .node lk ll lr := by
          apply restrictTree_eq_self_of_forall
          intro y hy
          exact le_trans (le_of_lt (BinaryTree.lt_of_IsBST_left _ u B ht hy)) hu
        rw [hproj_self] at hproj
        cases hproj
        rfl
    · have hgt : L < u := lt_of_not_ge hu
      rw [projL_node_gt L u _ B hsp_bst hgt, projL_node_gt L u _ B ht hgt,
        projL_spliceMin L hL_bst hm' hxL]

theorem projL_spliceMax_of_gt {α : Type} [LinearOrder α] (L : α) :
    ∀ {t : BinaryTree α} {xMax : α}, t.IsBST → t.maxKey? = some xMax → L < xMax →
      projL L (spliceMax t) = projL L t
  | .nil, _, _, hmax, _ => by simp [BinaryTree.maxKey?] at hmax
  | .node u A .nil, xMax, ht, hmax, hxL => by
    simp only [BinaryTree.maxKey?, Option.some.injEq] at hmax
    subst hmax
    rw [projL_node_gt L u A .nil ht hxL]
    rfl
  | .node u A (.node rk rl rr), xMax, ht, hmax, hxL => by
    have hR_bst := BinaryTree.IsBST_right_of_IsBST ht
    have hsp_bst := isBST_spliceMax ht
    obtain ⟨m', hm'⟩ := exists_maxKey_of_ne_nil (t := BinaryTree.node rk rl rr) (by simp)
    have hmax_eq : (BinaryTree.node u A (.node rk rl rr)).maxKey? = some m' := by
      show (match (BinaryTree.node rk rl rr).maxKey? with
            | none => some u | some x => some x) = some m'
      rw [hm']
    rw [hmax_eq, Option.some.injEq] at hmax
    subst m'
    have hsp_eq : spliceMax (.node u A (.node rk rl rr)) =
        .node u A (spliceMax (.node rk rl rr)) := rfl
    rw [hsp_eq] at hsp_bst ⊢
    by_cases hu : u ≤ L
    · rw [projL_node_le L u A _ hsp_bst hu, projL_node_le L u A _ ht hu,
        projL_spliceMax_of_gt L hR_bst hm' hxL]
    · have hgt : L < u := lt_of_not_ge hu
      rw [projL_node_gt L u A _ hsp_bst hgt, projL_node_gt L u A _ ht hgt]

theorem projL_rotateRightEdge {α : Type} [LinearOrder α] (L : α) :
    ∀ {t : BinaryTree α}, t.IsBST → ∀ {x p : α}, x < p →
      projL L (rotateRightEdge t x p) =
        if p ≤ L then rotateRightEdge (projL L t) x p else projL L t
  | .nil, _, x, p, _ => by
    split_ifs <;> simp [rotateRightEdge]
  | .node k l r, ht, x, p, hxp => by
    have hl_bst := BinaryTree.IsBST_left_of_IsBST ht
    have hr_bst := BinaryTree.IsBST_right_of_IsBST ht
    have hrot_bst := isBST_rotateRightEdge ht x p
    by_cases hpk : p < k
    · have hrot_eq : rotateRightEdge (.node k l r) x p = .node k (rotateRightEdge l x p) r := by
        simp [rotateRightEdge, hpk]
      rw [hrot_eq] at hrot_bst ⊢
      by_cases hkL : k ≤ L
      · have hpL : p ≤ L := le_trans (le_of_lt hpk) hkL
        simp only [hpL, ↓reduceIte]
        rw [projL_node_le L k _ r hrot_bst hkL, projL_node_le L k l r ht hkL]
        simp [rotateRightEdge, hpk]
      · have hgt : L < k := lt_of_not_ge hkL
        rw [projL_node_gt L k _ r hrot_bst hgt, projL_node_gt L k l r ht hgt]
        exact projL_rotateRightEdge L hl_bst hxp
    · by_cases hkp : k < p
      · have hrot_eq : rotateRightEdge (.node k l r) x p = .node k l (rotateRightEdge r x p) := by
          simp [rotateRightEdge, hpk, hkp]
        rw [hrot_eq] at hrot_bst ⊢
        by_cases hkL : k ≤ L
        · rw [projL_node_le L k l _ hrot_bst hkL, projL_node_le L k l r ht hkL,
            projL_rotateRightEdge L hr_bst hxp]
          split_ifs with hpL
          · simp [rotateRightEdge, hpk, hkp]
          · rfl
        · have hgt : L < k := lt_of_not_ge hkL
          have hp_gt : ¬ (p ≤ L) := not_le.mpr (lt_trans hgt hkp)
          simp only [hp_gt, ↓reduceIte]
          rw [projL_node_gt L k l _ hrot_bst hgt, projL_node_gt L k l r ht hgt]
      · have hpk_eq : p = k := le_antisymm (not_lt.mp hkp) (not_lt.mp hpk)
        subst hpk_eq
        cases l with
        | nil =>
          have hrot_eq : rotateRightEdge (.node p .nil r) x p = .node p .nil r := by
            simp [rotateRightEdge]
          rw [hrot_eq]
          split_ifs with hpL
          · rw [projL_node_le L p .nil r ht hpL]
            simp [rotateRightEdge]
          · rfl
        | node lx a b =>
          by_cases hlx : lx = x
          · subst hlx
            have hrot_eq : rotateRightEdge (.node p (.node lx a b) r) lx p =
                .node lx a (.node p b r) := by
              simp [rotateRightEdge]
            rw [hrot_eq] at hrot_bst ⊢
            have hx_bst := hl_bst
            have hpr_bst : (BinaryTree.node p b r).IsBST :=
              BinaryTree.IsBST_right_of_IsBST hrot_bst
            by_cases hpL : p ≤ L
            · have hxL : lx ≤ L := le_trans (le_of_lt hxp) hpL
              simp only [hpL, ↓reduceIte]
              rw [projL_node_le L lx a _ hrot_bst hxL,
                projL_node_le L p b r hpr_bst hpL,
                projL_node_le L p (.node lx a b) r ht hpL]
              simp [rotateRightEdge]
            · simp only [hpL, ↓reduceIte]
              have hp_gt : L < p := lt_of_not_ge hpL
              by_cases hxL : lx ≤ L
              · rw [projL_node_le L lx a _ hrot_bst hxL,
                  projL_node_gt L p b r hpr_bst hp_gt,
                  projL_node_gt L p (.node lx a b) r ht hp_gt,
                  projL_node_le L lx a b hx_bst hxL]
              · have hx_gt : L < lx := lt_of_not_ge hxL
                rw [projL_node_gt L lx a _ hrot_bst hx_gt,
                  projL_node_gt L p (.node lx a b) r ht hp_gt,
                  projL_node_gt L lx a b hx_bst hx_gt]
          · have hrot_eq : rotateRightEdge (.node p (.node lx a b) r) x p =
                .node p (.node lx a b) r := by
              simp [rotateRightEdge, hlx]
            rw [hrot_eq]
            split_ifs with hpL
            · rw [projL_node_le L p (.node lx a b) r ht hpL]
              simp [rotateRightEdge, hlx]
            · rfl

theorem mem_rightSpine_rotateLeftEdge {α : Type} [LinearOrder α] :
    ∀ {t : BinaryTree α} {x p u : α},
      u ∈ rightSpine t → u ≠ p → u ∈ rightSpine (rotateLeftEdge t x p)
  | .nil, _, _, _, hu, _ => hu
  | .node k l r, x, p, u, hu, hup => by
    simp only [rotateLeftEdge]
    split_ifs with hpk hkp
    · exact hu
    · simp only [rightSpine, List.mem_cons] at hu ⊢
      rcases hu with rfl | hur
      · exact Or.inl rfl
      · exact Or.inr (mem_rightSpine_rotateLeftEdge hur hup)
    · cases r with
      | nil => exact hu
      | node rx b c =>
        dsimp only
        split_ifs with hrx
        · subst hrx
          have hpk_eq : p = k := le_antisymm (not_lt.mp hkp) (not_lt.mp hpk)
          subst hpk_eq
          simp only [rightSpine, List.mem_cons] at hu ⊢
          rcases hu with rfl | rfl | huc
          · exact absurd rfl hup
          · exact Or.inl rfl
          · exact Or.inr huc
        · exact hu

theorem projL_rotateLeftEdge {α : Type} [LinearOrder α] (L : α) :
    ∀ {t : BinaryTree α}, t.IsBST → ∀ {x p : α}, p < x →
      p ∈ rightSpine t → x ∈ rightSpine t →
      projL L (rotateLeftEdge t x p) =
        if x ≤ L then rotateLeftEdge (projL L t) x p else projL L t
  | .nil, _, _, _, _, hp, _ => by simp [rightSpine] at hp
  | .node k l r, ht, x, p, hpx, hp, hx => by
    have hr_bst := BinaryTree.IsBST_right_of_IsBST ht
    have hrot_bst := isBST_rotateLeftEdge ht x p
    have hkp_le : k ≤ p := by
      simp only [rightSpine, List.mem_cons] at hp
      rcases hp with rfl | hpr
      · exact le_rfl
      · exact le_of_lt (BinaryTree.gt_of_IsBST_right l k r ht (mem_rightSpine hpr))
    have hnot_pk : ¬ (p < k) := not_lt.mpr hkp_le
    by_cases hkp : k < p
    · have hpr : p ∈ rightSpine r := by
        simp only [rightSpine, List.mem_cons] at hp
        rcases hp with rfl | hpr
        · exact absurd hkp (lt_irrefl _)
        · exact hpr
      have hxr : x ∈ rightSpine r := by
        simp only [rightSpine, List.mem_cons] at hx
        rcases hx with rfl | hxr
        · exact absurd (lt_trans hkp hpx) (lt_irrefl _)
        · exact hxr
      have hrot_eq : rotateLeftEdge (.node k l r) x p = .node k l (rotateLeftEdge r x p) := by
        simp [rotateLeftEdge, hnot_pk, hkp]
      rw [hrot_eq] at hrot_bst ⊢
      by_cases hkL : k ≤ L
      · rw [projL_node_le L k l _ hrot_bst hkL, projL_node_le L k l r ht hkL,
          projL_rotateLeftEdge L hr_bst hpx hpr hxr]
        split_ifs with hxL
        · simp [rotateLeftEdge, hnot_pk, hkp]
        · rfl
      · have hgt : L < k := lt_of_not_ge hkL
        have hx_gt : ¬ (x ≤ L) := not_le.mpr (lt_trans (lt_trans hgt hkp) hpx)
        simp only [hx_gt, ↓reduceIte]
        rw [projL_node_gt L k l _ hrot_bst hgt, projL_node_gt L k l r ht hgt]
    · have hpk_eq : p = k := le_antisymm (not_lt.mp hkp) hkp_le
      subst hpk_eq
      have hxr : x ∈ rightSpine r := by
        simp only [rightSpine, List.mem_cons] at hx
        rcases hx with rfl | hxr
        · exact absurd hpx (lt_irrefl _)
        · exact hxr
      cases r with
      | nil => simp [rightSpine] at hxr
      | node rx b c =>
        by_cases hrx : rx = x
        · subst hrx
          have hrot_eq : rotateLeftEdge (.node p l (.node rx b c)) rx p =
              .node rx (.node p l b) c := by
            simp [rotateLeftEdge]
          rw [hrot_eq] at hrot_bst ⊢
          have hplb_bst : (BinaryTree.node p l b).IsBST :=
            BinaryTree.IsBST_left_of_IsBST hrot_bst
          by_cases hxL : rx ≤ L
          · have hpL : p ≤ L := le_trans (le_of_lt hpx) hxL
            simp only [hxL, ↓reduceIte]
            rw [projL_node_le L rx _ c hrot_bst hxL,
              projL_node_le L p l (.node rx b c) ht hpL,
              projL_node_le L rx b c hr_bst hxL]
            simp [rotateLeftEdge]
          · simp only [hxL, ↓reduceIte]
            have hx_gt : L < rx := lt_of_not_ge hxL
            by_cases hpL : p ≤ L
            · rw [projL_node_gt L rx _ c hrot_bst hx_gt,
                projL_node_le L p l b hplb_bst hpL,
                projL_node_le L p l (.node rx b c) ht hpL,
                projL_node_gt L rx b c hr_bst hx_gt]
            · have hp_gt : L < p := lt_of_not_ge hpL
              rw [projL_node_gt L rx _ c hrot_bst hx_gt,
                projL_node_gt L p l b hplb_bst hp_gt,
                projL_node_gt L p l (.node rx b c) ht hp_gt]
        · have hrot_eq : rotateLeftEdge (.node p l (.node rx b c)) x p =
              .node p l (.node rx b c) := by
            simp [rotateLeftEdge, hrx]
          rw [hrot_eq]
          have hxc : x ∈ rightSpine c := by
            simp only [rightSpine, List.mem_cons] at hxr
            rcases hxr with rfl | hxc
            · exact absurd rfl hrx
            · exact hxc
          have hrx_lt_x : rx < x :=
            BinaryTree.gt_of_IsBST_right b rx c hr_bst (mem_rightSpine hxc)
          split_ifs with hxL
          · have hrxL : rx ≤ L := le_trans (le_of_lt hrx_lt_x) hxL
            have hpL : p ≤ L := le_trans (le_of_lt hpx) hxL
            rw [projL_node_le L p l (.node rx b c) ht hpL,
              projL_node_le L rx b c hr_bst hrxL]
            simp [rotateLeftEdge, hrx]
          · rfl

/-! ## Section 2: Fresh Inserted Keys and `lt_of_mem_U_before_inject` -/

theorem dequeSeq_zero {α : Type} [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin m → DequeOp α) :
    dequeSeq init ops 0 = init := rfl

theorem dequeSeq_succ {α : Type} [LinearOrder α] {m : ℕ}
    (init : BinaryTree α) (ops : Fin m → DequeOp α) (i : Fin m) :
    dequeSeq init ops i.succ = (ops i).step (dequeSeq init ops i.castSucc) := by
  show (if h : i.val < m then (ops ⟨i.val, h⟩).step (dequeSeq init ops i.castSucc) else _) = _
  simp [i.isLt]

def isInsertOp {α : Type} : DequeOp α → Bool
  | .push _ => true
  | .inject _ => true
  | _ => false

/-- Cumulative visited keys across times `0 .. k` (`k ≤ m`). -/
noncomputable def visitedKeys {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) : (k : ℕ) → k ≤ m → Finset ℝ
  | 0, _ => open Classical in keyFinset asn.T0
  | k + 1, hk =>
    open Classical in
    visitedKeys asn k (Nat.le_of_succ_le hk) ∪ keyFinset (asn.treeAt ⟨k + 1, Nat.succ_lt_succ hk⟩)

theorem subset_visitedKeys {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (s : Fin (m + 1)) (k : ℕ) (hk : k ≤ m)
    (hsk : s.val ≤ k) :
    (open Classical in keyFinset (asn.treeAt s)) ⊆ visitedKeys asn k hk := by
  induction k with
  | zero =>
    have hs0 : s = 0 := Fin.ext (Nat.eq_zero_of_le_zero hsk)
    subst hs0
    exact Finset.Subset.refl _
  | succ k ih =>
    by_cases hlt : s.val ≤ k
    · exact Finset.Subset.trans (ih (Nat.le_of_succ_le hk) hlt)
        (open Classical in Finset.subset_union_left)
    · have hseq : s = ⟨k + 1, Nat.succ_lt_succ hk⟩ := Fin.ext (by dsimp; omega)
      subst hseq
      exact open Classical in Finset.subset_union_right

theorem visitedKeys_succ_eq {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m) :
    visitedKeys asn (i.val + 1) i.isLt =
      open Classical in
      match asn.opsR i with
      | .push x => insert x (visitedKeys asn i.val (Nat.le_of_lt i.isLt))
      | .inject x => insert x (visitedKeys asn i.val (Nat.le_of_lt i.isLt))
      | .pop => visitedKeys asn i.val (Nat.le_of_lt i.isLt)
      | .eject => visitedKeys asn i.val (Nat.le_of_lt i.isLt) := by
  open Classical in
  have hprev : keyFinset (asn.treeAt i.castSucc) ⊆ visitedKeys asn i.val (Nat.le_of_lt i.isLt) :=
    subset_visitedKeys asn i.castSucc i.val (Nat.le_of_lt i.isLt) le_rfl
  have hstep : asn.treeAt ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
      (asn.opsR i).step (asn.treeAt i.castSucc) :=
    dequeSeq_succ asn.T0 asn.opsR i
  have hbst : (asn.treeAt i.castSucc).IsBST := asn.hBST i.castSucc
  have hval : (asn.opsR i).Valid (asn.treeAt i.castSucc) := asn.hValidR i
  change visitedKeys asn i.val (Nat.le_of_lt i.isLt) ∪
      keyFinset (asn.treeAt ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) = _
  rw [hstep]
  rcases hop : asn.opsR i with _ | x | _ | x
  · rw [hop] at hval
    obtain ⟨q, hmin⟩ := exists_minKey_of_ne_nil hval
    apply Finset.union_eq_left.mpr
    intro y hy
    apply hprev
    rw [mem_keyFinset_iff] at hy ⊢
    exact ((mem_splay_pop_iff hbst hmin y).mp hy).1
  · ext y
    simp only [DequeOp.step, SplayTree.push, keyFinset, Finset.notMem_empty, false_or,
      Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (hy | rfl | hy)
      · exact Or.inr hy
      · exact Or.inl rfl
      · exact Or.inr (hprev hy)
    · rintro (rfl | hy)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hy
  · rw [hop] at hval
    obtain ⟨q, hmax⟩ := exists_maxKey_of_ne_nil hval
    apply Finset.union_eq_left.mpr
    intro y hy
    apply hprev
    rw [mem_keyFinset_iff] at hy ⊢
    exact ((mem_splay_eject_iff hbst hmax y).mp hy).1
  · ext y
    simp only [DequeOp.step, SplayTree.inject, keyFinset, Finset.notMem_empty, or_false,
      Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (hy | rfl | hy)
      · exact Or.inr hy
      · exact Or.inl rfl
      · exact Or.inr (hprev hy)
    · rintro (rfl | hy)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hy

theorem visitedKeys_last_eq_everPresent {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) :
    visitedKeys asn m le_rfl = asn.everPresentKeys := by
  open Classical in
  apply Finset.Subset.antisymm
  · have hsub : ∀ (k : ℕ) (hk : k ≤ m), visitedKeys asn k hk ⊆ asn.everPresentKeys := by
      intro k
      induction k with
      | zero =>
        intro _
        exact asn.hActiveSub 0
      | succ k ih =>
        intro hk
        exact Finset.union_subset (ih (Nat.le_of_succ_le hk))
          (asn.hActiveSub ⟨k + 1, Nat.succ_lt_succ hk⟩)
    exact hsub m le_rfl
  · intro x hx
    by_cases hxL : x ≤ asn.Lm
    · have hmem : x ∈ asn.everPresentKeys.filter (· ≤ asn.Lm) := Finset.mem_filter.mpr ⟨hx, hxL⟩
      rw [← asn.hPopOrder.2.2, List.mem_toFinset] at hmem
      simp only [popDeletedKeys, List.mem_filterMap, List.mem_finRange, true_and] at hmem
      obtain ⟨j, hj⟩ := hmem
      split_ifs at hj with hpop
      have hx_tree : x ∈ asn.treeAt j.castSucc := mem_of_minKey hj
      exact subset_visitedKeys asn j.castSucc m le_rfl (Nat.le_of_lt j.isLt)
        ((mem_keyFinset_iff _ x).mpr hx_tree)
    · by_cases hxR : asn.Rm ≤ x
      · have hmem : x ∈ asn.everPresentKeys.filter (asn.Rm ≤ ·) := Finset.mem_filter.mpr ⟨hx, hxR⟩
        rw [← asn.hEjectOrder.2.2, List.mem_toFinset] at hmem
        simp only [ejectDeletedKeys, List.mem_filterMap, List.mem_finRange, true_and] at hmem
        obtain ⟨j, hj⟩ := hmem
        split_ifs at hj with hej
        have hx_tree : x ∈ asn.treeAt j.castSucc := mem_of_maxKey hj
        exact subset_visitedKeys asn j.castSucc m le_rfl (Nat.le_of_lt j.isLt)
          ((mem_keyFinset_iff _ x).mpr hx_tree)
      · have hmid : asn.Lm < x ∧ x < asn.Rm := ⟨lt_of_not_ge hxL, lt_of_not_ge hxR⟩
        have hmem : x ∈ asn.everPresentKeys.filter (fun y => asn.Lm < y ∧ y < asn.Rm) :=
          Finset.mem_filter.mpr ⟨hx, hmid⟩
        rw [← asn.hSurviving] at hmem
        exact subset_visitedKeys asn (Fin.last m) m le_rfl le_rfl hmem

theorem visitedKeys_card_add_tail {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (k : ℕ) (hk : k ≤ m) :
    (visitedKeys asn m le_rfl).card ≤
      (visitedKeys asn k hk).card +
        (Finset.univ.filter (fun j : Fin m => k ≤ j.val ∧ isInsertOp (asn.opsR j))).card := by
  obtain ⟨d, hd⟩ : ∃ d, m - k = d := ⟨m - k, rfl⟩
  induction d generalizing k with
  | zero =>
    have hkm : k = m := by omega
    subst k
    have hemp : Finset.univ.filter (fun j : Fin m => m ≤ j.val ∧ isInsertOp (asn.opsR j)) = ∅ := by
      ext j; simp
    rw [hemp]; simp
  | succ d ih =>
    have hlt : k < m := by omega
    let ik : Fin m := ⟨k, hlt⟩
    have hih := ih (k + 1) hlt (by omega)
    have hstep := visitedKeys_succ_eq asn ik
    have hsplit :
        (Finset.univ.filter (fun j : Fin m => k ≤ j.val ∧ isInsertOp (asn.opsR j))).card =
        (if isInsertOp (asn.opsR ik) then 1 else 0) +
          (Finset.univ.filter (fun j : Fin m => k + 1 ≤ j.val ∧ isInsertOp (asn.opsR j))).card := by
      by_cases hins : isInsertOp (asn.opsR ik) = true
      · have h_eq : Finset.univ.filter (fun j : Fin m => k ≤ j.val ∧ isInsertOp (asn.opsR j)) =
            insert ik (Finset.univ.filter (fun j : Fin m => k + 1 ≤ j.val ∧ isInsertOp (asn.opsR j))) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hkj, hjins⟩
            by_cases hjk : j.val = k
            · exact Or.inl (Fin.ext hjk)
            · exact Or.inr ⟨by omega, hjins⟩
          · rintro (rfl | ⟨hkj, hjins⟩)
            · exact ⟨le_rfl, hins⟩
            · exact ⟨by omega, hjins⟩
        have hnotmem : ik ∉ Finset.univ.filter (fun j : Fin m => k + 1 ≤ j.val ∧ isInsertOp (asn.opsR j)) := by
          simp [ik]
        rw [h_eq, Finset.card_insert_of_notMem hnotmem]
        simp [hins]
        omega
      · have h_eq : Finset.univ.filter (fun j : Fin m => k ≤ j.val ∧ isInsertOp (asn.opsR j)) =
            Finset.univ.filter (fun j : Fin m => k + 1 ≤ j.val ∧ isInsertOp (asn.opsR j)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hkj, hjins⟩
            by_cases hjk : j.val = k
            · have : j = ik := Fin.ext hjk
              subst this
              exact absurd hjins hins
            · exact ⟨by omega, hjins⟩
          · rintro ⟨hkj, hjins⟩
            exact ⟨by omega, hjins⟩
        rw [h_eq]
        simp [hins]
    rw [hsplit]
    open Classical in
    rcases hop : asn.opsR ik with _ | x | _ | x
    · rw [hop] at hstep
      have heq_vis : visitedKeys asn (k + 1) hlt = visitedKeys asn k hk := hstep
      rw [heq_vis] at hih
      simpa [isInsertOp] using hih
    · rw [hop] at hstep
      have hins_le : (visitedKeys asn (k + 1) hlt).card ≤ (visitedKeys asn k hk).card + 1 := by
        change (visitedKeys asn (ik.val + 1) ik.isLt).card ≤ _
        rw [hstep]
        exact Finset.card_insert_le _ _
      have h1 : (if isInsertOp (DequeOp.push x) = true then 1 else 0) = 1 := rfl
      rw [h1]
      omega
    · rw [hop] at hstep
      have heq_vis : visitedKeys asn (k + 1) hlt = visitedKeys asn k hk := hstep
      rw [heq_vis] at hih
      simpa [isInsertOp] using hih
    · rw [hop] at hstep
      have hins_le : (visitedKeys asn (k + 1) hlt).card ≤ (visitedKeys asn k hk).card + 1 := by
        change (visitedKeys asn (ik.val + 1) ik.isLt).card ≤ _
        rw [hstep]
        exact Finset.card_insert_le _ _
      have h1 : (if isInsertOp (DequeOp.inject x) = true then 1 else 0) = 1 := rfl
      rw [h1]
      omega

theorem visitedKeys_card_prefix {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (k : ℕ) (hk : k ≤ m) :
    (visitedKeys asn k hk).card ≤
      init.tree.num_nodes +
        (Finset.univ.filter (fun j : Fin m => j.val < k ∧ isInsertOp (asn.opsR j))).card := by
  induction k with
  | zero =>
    open Classical in
    have hcard0 : (keyFinset asn.T0).card = asn.T0.num_nodes :=
      card_keyFinset_of_isBST (asn.hBST 0)
    have hshape0 : asn.T0.num_nodes = init.tree.num_nodes := by
      have hs := congrArg BinaryTree.num_nodes (asn.hShape 0)
      simpa [num_nodes_map, dequeSeq_zero] using hs
    have hemp : Finset.univ.filter (fun j : Fin m => j.val < 0 ∧ isInsertOp (asn.opsR j)) = ∅ := by
      ext j; simp
    rw [hemp]
    simp [visitedKeys, hcard0, hshape0]
  | succ k ih =>
    let ik : Fin m := ⟨k, hk⟩
    have hih := ih (Nat.le_of_succ_le hk)
    have hstep := visitedKeys_succ_eq asn ik
    have hsplit :
        (Finset.univ.filter (fun j : Fin m => j.val < k + 1 ∧ isInsertOp (asn.opsR j))).card =
        (Finset.univ.filter (fun j : Fin m => j.val < k ∧ isInsertOp (asn.opsR j))).card +
          (if isInsertOp (asn.opsR ik) then 1 else 0) := by
      by_cases hins : isInsertOp (asn.opsR ik) = true
      · have h_eq : Finset.univ.filter (fun j : Fin m => j.val < k + 1 ∧ isInsertOp (asn.opsR j)) =
            insert ik (Finset.univ.filter (fun j : Fin m => j.val < k ∧ isInsertOp (asn.opsR j))) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hkj, hjins⟩
            by_cases hjk : j.val = k
            · exact Or.inl (Fin.ext hjk)
            · exact Or.inr ⟨by omega, hjins⟩
          · rintro (rfl | ⟨hkj, hjins⟩)
            · exact ⟨by dsimp [ik]; omega, hins⟩
            · exact ⟨by omega, hjins⟩
        have hnotmem : ik ∉ Finset.univ.filter (fun j : Fin m => j.val < k ∧ isInsertOp (asn.opsR j)) := by
          simp [ik]
        rw [h_eq, Finset.card_insert_of_notMem hnotmem]
        simp [hins]
      · have h_eq : Finset.univ.filter (fun j : Fin m => j.val < k + 1 ∧ isInsertOp (asn.opsR j)) =
            Finset.univ.filter (fun j : Fin m => j.val < k ∧ isInsertOp (asn.opsR j)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hkj, hjins⟩
            by_cases hjk : j.val = k
            · have : j = ik := Fin.ext hjk
              subst this
              exact absurd hjins hins
            · exact ⟨by omega, hjins⟩
          · rintro ⟨hkj, hjins⟩
            exact ⟨by omega, hjins⟩
        rw [h_eq]
        simp [hins]
    rw [hsplit]
    open Classical in
    rcases hop : asn.opsR ik with _ | x | _ | x
    · rw [hop] at hstep
      have heq_vis : visitedKeys asn (k + 1) hk = visitedKeys asn k (Nat.le_of_succ_le hk) := hstep
      rw [heq_vis]
      simpa [isInsertOp] using hih
    · rw [hop] at hstep
      have heq_vis : visitedKeys asn (k + 1) hk =
          insert x (visitedKeys asn k (Nat.le_of_succ_le hk)) := hstep
      rw [heq_vis]
      have hins_le := Finset.card_insert_le x (visitedKeys asn k (Nat.le_of_succ_le hk))
      have h1 : (if isInsertOp (DequeOp.push x) = true then 1 else 0) = 1 := rfl
      rw [h1]
      omega
    · rw [hop] at hstep
      have heq_vis : visitedKeys asn (k + 1) hk = visitedKeys asn k (Nat.le_of_succ_le hk) := hstep
      rw [heq_vis]
      simpa [isInsertOp] using hih
    · rw [hop] at hstep
      have heq_vis : visitedKeys asn (k + 1) hk =
          insert x (visitedKeys asn k (Nat.le_of_succ_le hk)) := hstep
      rw [heq_vis]
      have hins_le := Finset.card_insert_le x (visitedKeys asn k (Nat.le_of_succ_le hk))
      have h1 : (if isInsertOp (DequeOp.inject x) = true then 1 else 0) = 1 := rfl
      rw [h1]
      omega

theorem insertCount_add_deletes_eq_m {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) :
    (Finset.univ.filter (fun i : Fin m => isInsertOp (asn.opsR i))).card +
      (popCount ops + ejectCount ops) = m := by
  unfold popCount ejectCount
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  have hsum :
      (∑ i : Fin m, if isInsertOp (asn.opsR i) then 1 else 0) +
      ((∑ i : Fin m, if (ops i).isPop then 1 else 0) +
       (∑ i : Fin m, if (ops i).isEject then 1 else 0)) =
      ∑ _i : Fin m, (1 : ℕ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hk := asn.hKind i
    rcases h1 : ops i with _ | _ | _ | _ <;> rcases h2 : asn.opsR i with _ | _ | _ | _ <;>
      · rw [h1, h2] at hk
        simp [DequeOp.sameKind, isInsertOp, DequeOp.isPop, DequeOp.isEject] at hk ⊢
  simpa using hsum

theorem fresh_of_inject {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m) (z : ℝ)
    (hop : asn.opsR i = .inject z) :
    z ∉ visitedKeys asn i.val (Nat.le_of_lt i.isLt) := by
  intro hmem
  open Classical in
  have hstep := visitedKeys_succ_eq asn i
  rw [hop] at hstep
  dsimp only at hstep
  rw [Finset.insert_eq_of_mem hmem] at hstep
  have hpre := visitedKeys_card_prefix asn i.val (Nat.le_of_lt i.isLt)
  have htail := visitedKeys_card_add_tail asn (i.val + 1) i.isLt
  rw [hstep] at htail
  have hsplit_all :
      (Finset.univ.filter (fun j : Fin m => j.val < i.val ∧ isInsertOp (asn.opsR j))).card + 1 +
      (Finset.univ.filter (fun j : Fin m => i.val + 1 ≤ j.val ∧ isInsertOp (asn.opsR j))).card =
      (Finset.univ.filter (fun j : Fin m => isInsertOp (asn.opsR j))).card := by
    have hins_i : isInsertOp (asn.opsR i) = true := by simp [hop, isInsertOp]
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
    have hpoint : ∀ j : Fin m,
        (if j.val < i.val ∧ isInsertOp (asn.opsR j) then 1 else 0) +
        (if j = i then 1 else 0) +
        (if i.val + 1 ≤ j.val ∧ isInsertOp (asn.opsR j) then 1 else 0) =
        (if isInsertOp (asn.opsR j) then 1 else 0) := by
      intro j
      by_cases hji : j = i
      · subst hji; simp [hins_i]
      · have hjne : j.val ≠ i.val := fun h => hji (Fin.ext h)
        by_cases hjlt : j.val < i.val
        · have hnotge : ¬ (i.val + 1 ≤ j.val) := by omega
          simp [hji, hjlt, hnotge]
        · have hge : i.val + 1 ≤ j.val := by omega
          simp [hji, hjlt, hge]
    have hsum :
        ∑ j : Fin m,
          ((if j.val < i.val ∧ isInsertOp (asn.opsR j) then 1 else 0) +
           (if j = i then 1 else 0) +
           (if i.val + 1 ≤ j.val ∧ isInsertOp (asn.opsR j) then 1 else 0)) =
        ∑ j : Fin m, (if isInsertOp (asn.opsR j) then 1 else 0) :=
      Finset.sum_congr rfl (fun j _ => hpoint j)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have hsingle : (∑ j : Fin m, if j = i then 1 else 0) = 1 := by simp
    omega
  have hever := visitedKeys_last_eq_everPresent asn
  have hcard_ever := asn.hEverCard
  have hm_eq := insertCount_add_deletes_eq_m asn
  rw [hever] at htail
  omega

theorem sublist_pair_of_lt {α : Type} [LinearOrder α] {xs : List α}
    (hsort : xs.Pairwise (· < ·)) {u z : α} (hu : u ∈ xs) (hz : z ∈ xs) (huz : u < z) :
    [u, z].Sublist xs := by
  induction xs with
  | nil => simp at hu
  | cons a as ih =>
    obtain ⟨ha_lt, has_sort⟩ := List.pairwise_cons.mp hsort
    rcases List.mem_cons.mp hu with rfl | hu_as
    · rcases List.mem_cons.mp hz with rfl | hz_as
      · exact absurd huz (lt_irrefl _)
      · exact List.Sublist.cons_cons u (List.singleton_sublist.mpr hz_as)
    · rcases List.mem_cons.mp hz with rfl | hz_as
      · exact absurd (lt_trans (ha_lt u hu_as) huz) (lt_irrefl _)
      · exact List.Sublist.cons a (ih has_sort hu_as hz_as)

/-- Key ordering lemma: if `opsR i = .inject z` with `z ≤ Lm`, then every key in `U_s`
for `s ≤ i` is strictly smaller than `z`. -/
theorem lt_of_mem_U_before_inject {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m) (z : ℝ)
    (hop : asn.opsR i = .inject z) (hzL : z ≤ asn.Lm)
    (s : Fin (m + 1)) (hsi : s.val ≤ i.val) (u : ℝ) (hu : u ∈ asn.U s) :
    u < z := by
  have hs_bst : (asn.treeAt s).IsBST := asn.hBST s
  obtain ⟨hu_tree, huL⟩ := (mem_projL_iff asn.Lm hs_bst u).mp hu
  by_cases hu_at_i : u ∈ asn.treeAt i.castSucc
  · have hval := asn.hValidR i
    rw [hop] at hval
    exact hval u hu_at_i
  · have hex_pop_u : ∃ ju : Fin m, ju.val < i.val ∧
        (asn.opsR ju).isPop = true ∧ (asn.treeAt ju.castSucc).minKey? = some u := by
      obtain ⟨d, hd⟩ : ∃ d, i.val - s.val = d := ⟨i.val - s.val, rfl⟩
      induction d generalizing s with
      | zero =>
        have hseq : s = i.castSucc := Fin.ext (by simp; omega)
        subst hseq
        exact absurd hu_tree hu_at_i
      | succ d ih =>
        have hslt : s.val < i.val := by omega
        let js : Fin m := ⟨s.val, lt_trans hslt i.isLt⟩
        have hjs_cs : js.castSucc = s := Fin.ext rfl
        by_cases hu_next : u ∈ asn.treeAt js.succ
        · have hu_U_next : u ∈ asn.U js.succ :=
            (mem_projL_iff asn.Lm (asn.hBST js.succ) u).mpr ⟨hu_next, huL⟩
          exact ih js.succ (by simp [js]; omega) hu_U_next (asn.hBST js.succ) hu_next
            (by simp [js]; omega)
        · have hstep : asn.treeAt js.succ = (asn.opsR js).step (asn.treeAt js.castSucc) :=
            dequeSeq_succ asn.T0 asn.opsR js
          rw [hjs_cs] at hstep
          have hval_js : (asn.opsR js).Valid (asn.treeAt s) := by
            rw [← hjs_cs]; exact asn.hValidR js
          rcases hop_js : asn.opsR js with _ | x | _ | x
          · rw [hop_js] at hval_js hstep
            obtain ⟨q, hmin⟩ := exists_minKey_of_ne_nil hval_js
            have hu_eq_q : u = q := by
              by_contra hne
              apply hu_next
              rw [hstep]
              exact (mem_splay_pop_iff hs_bst hmin u).mpr ⟨hu_tree, hne⟩
            subst hu_eq_q
            refine ⟨js, hslt, by simp [hop_js, DequeOp.isPop], ?_⟩
            rwa [hjs_cs]
          · exfalso; apply hu_next; rw [hstep, hop_js]
            exact .right hu_tree
          · exfalso
            rw [hop_js] at hval_js hstep
            obtain ⟨q, hmax⟩ := exists_maxKey_of_ne_nil hval_js
            have hq_ej : q ∈ ejectDeletedKeys asn.T0 asn.opsR := by
              simp only [ejectDeletedKeys, List.mem_filterMap, List.mem_finRange, true_and]
              refine ⟨js, ?_⟩
              have hmax' : (dequeSeq asn.T0 asn.opsR js.castSucc).maxKey? = some q := by
                change (asn.treeAt js.castSucc).maxKey? = some q
                rwa [hjs_cs]
              simp [hop_js, DequeOp.isEject, hmax']
            have hq_VR : asn.Rm ≤ q := by
              open Classical in
              have hmem : q ∈ (ejectDeletedKeys asn.T0 asn.opsR).toFinset :=
                List.mem_toFinset.mpr hq_ej
              rw [asn.hEjectOrder.2.2] at hmem
              exact (Finset.mem_filter.mp hmem).2
            have hu_ne_q : u ≠ q := ne_of_lt (lt_of_le_of_lt huL (lt_of_lt_of_le asn.hLmRm hq_VR))
            apply hu_next
            rw [hstep]
            exact (mem_splay_eject_iff hs_bst hmax u).mpr ⟨hu_tree, hu_ne_q⟩
          · exfalso; apply hu_next; rw [hstep, hop_js]
            exact .left hu_tree
    have hz_mem_succ : z ∈ asn.treeAt i.succ := by
      unfold ThreeWayKeyAssignment.treeAt
      rw [dequeSeq_succ asn.T0 asn.opsR i, hop]
      exact .here
    have hz_ever : z ∈ asn.everPresentKeys := by
      open Classical in
      exact asn.hActiveSub i.succ ((mem_keyFinset_iff _ z).mpr hz_mem_succ)
    have hz_pKeys : z ∈ popDeletedKeys asn.T0 asn.opsR := by
      open Classical in
      rw [← List.mem_toFinset, asn.hPopOrder.2.2]
      exact Finset.mem_filter.mpr ⟨hz_ever, hzL⟩
    simp only [popDeletedKeys, List.mem_filterMap, List.mem_finRange, true_and] at hz_pKeys
    obtain ⟨jz, hjz_pop⟩ := hz_pKeys
    split_ifs at hjz_pop with hjz_isPop
    have hz_fresh : z ∉ visitedKeys asn i.val (Nat.le_of_lt i.isLt) :=
      fresh_of_inject asn i z hop
    have hijz : i.val < jz.val := by
      by_contra hle
      have hjz_le : jz.castSucc.val ≤ i.val := by simp; omega
      have hz_tree : z ∈ asn.treeAt jz.castSucc := mem_of_minKey hjz_pop
      apply hz_fresh
      open Classical in
      exact subset_visitedKeys asn jz.castSucc i.val (Nat.le_of_lt i.isLt) hjz_le
        ((mem_keyFinset_iff _ z).mpr hz_tree)
    obtain ⟨ju, hju_lt, hju_isPop, hju_min⟩ := hex_pop_u
    have hju_lt_jz : ju < jz := lt_trans hju_lt hijz
    have hsublist : [ju, jz].Sublist (List.finRange m) :=
      sublist_pair_of_lt (List.pairwise_lt_finRange m)
        (List.mem_finRange ju) (List.mem_finRange jz) hju_lt_jz
    let f : Fin m → Option ℝ := fun j =>
      if (asn.opsR j).isPop then (dequeSeq asn.T0 asn.opsR j.castSucc).minKey? else none
    have hfm_sub : ([ju, jz].filterMap f).Sublist ((List.finRange m).filterMap f) :=
      List.Sublist.filterMap f hsublist
    have hju_min' : (dequeSeq asn.T0 asn.opsR ju.castSucc).minKey? = some u := hju_min
    have hfm_eq : [ju, jz].filterMap f = [u, z] := by
      simp [f, hju_isPop, hju_min', hjz_isPop, hjz_pop]
    rw [hfm_eq] at hfm_sub
    have huz_pair : [u, z].Pairwise (· < ·) := asn.hPopOrder.1.sublist hfm_sub
    exact (List.pairwise_cons.mp huz_pair).1 z (List.mem_singleton_self z)

/-! ## Section 3: Emptying One-Sided Simulation (`lem_3_5_part2`) -/

def listPos {α : Type} [DecidableEq α] (x : α) : List α → ℕ
  | [] => 0
  | b :: bs => if x = b then 0 else listPos x bs + 1

theorem listPos_lt_length {α : Type} [DecidableEq α] {x : α} {xs : List α} (hx : x ∈ xs) :
    listPos x xs < xs.length := by
  induction xs with
  | nil => cases hx
  | cons b bs ih =>
    simp only [listPos, List.length_cons]
    by_cases hxb : x = b
    · simp [hxb]
    · simp only [hxb, ↓reduceIte]
      rcases List.mem_cons.mp hx with rfl | hbs
      · exact absurd rfl hxb
      · exact Nat.succ_lt_succ (ih hbs)

theorem listPos_lt_of_pairwise {α : Type} [LinearOrder α] [DecidableEq α]
    {xs : List α} (hsort : xs.Pairwise (· < ·)) {x y : α}
    (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x < y) :
    listPos x xs < listPos y xs := by
  induction xs with
  | nil => cases hx
  | cons b bs ih =>
    obtain ⟨hb_lt, hbs_sort⟩ := List.pairwise_cons.mp hsort
    simp only [listPos]
    rcases List.mem_cons.mp hx with rfl | hx_bs
    · rcases List.mem_cons.mp hy with rfl | hy_bs
      · exact absurd hxy (lt_irrefl _)
      · have hyb : y ≠ x := ne_of_gt hxy
        simp [hyb]
    · have hxb : x ≠ b := ne_of_gt (hb_lt x hx_bs)
      rcases List.mem_cons.mp hy with rfl | hy_bs
      · exact absurd (lt_trans (hb_lt x hx_bs) hxy) (lt_irrefl _)
      · have hyb : y ≠ b := ne_of_gt (hb_lt y hy_bs)
        simp only [hxb, hyb, ↓reduceIte]
        exact Nat.succ_lt_succ (ih hbs_sort hx_bs hy_bs)

theorem map_listPos_add {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (c : ℕ), xs.Nodup →
      xs.map (fun x => listPos x xs + c) = List.range' c xs.length
  | [], _, _ => rfl
  | b :: bs, c, hnd => by
    obtain ⟨hb_not, hbs_nd⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, listPos, ↓reduceIte, zero_add, List.length_cons, List.range'_succ]
    congr 1
    have heq : bs.map (fun x => (if x = b then 0 else listPos x bs + 1) + c) =
        bs.map (fun x => listPos x bs + (c + 1)) := by
      apply List.map_congr_left
      intro x hx
      have hxb : x ≠ b := fun h => hb_not (h ▸ hx)
      simp only [hxb, ↓reduceIte]
      omega
    rw [heq]
    exact map_listPos_add bs (c + 1) hbs_nd

noncomputable def rankVL {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (x : ℝ) : ℕ :=
  open Classical in listPos x (popDeletedKeys asn.T0 asn.opsR) + 1

theorem mem_VL_iff_mem_pKeys {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (x : ℝ) :
    x ∈ asn.VL ↔ x ∈ popDeletedKeys asn.T0 asn.opsR := by
  open Classical in
  unfold ThreeWayKeyAssignment.VL
  rw [← asn.hPopOrder.2.2, List.mem_toFinset]

theorem rankVL_bounds {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) {x : ℝ} (hx : x ∈ asn.VL) :
    1 ≤ rankVL asn x ∧ rankVL asn x ≤ popCount ops := by
  open Classical in
  have hmem : x ∈ popDeletedKeys asn.T0 asn.opsR := (mem_VL_iff_mem_pKeys asn x).mp hx
  have hlt := listPos_lt_length hmem
  rw [asn.hPopOrder.2.1] at hlt
  unfold rankVL
  omega

theorem rankVL_lt_of_lt {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) {x y : ℝ}
    (hx : x ∈ asn.VL) (hy : y ∈ asn.VL) (hxy : x < y) :
    rankVL asn x < rankVL asn y := by
  open Classical in
  have hx' := (mem_VL_iff_mem_pKeys asn x).mp hx
  have hy' := (mem_VL_iff_mem_pKeys asn y).mp hy
  exact Nat.succ_lt_succ (listPos_lt_of_pairwise asn.hPopOrder.1 hx' hy' hxy)

theorem rankVL_lt_iff {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) {x y : ℝ}
    (hx : x ∈ asn.VL) (hy : y ∈ asn.VL) :
    rankVL asn x < rankVL asn y ↔ x < y := by
  constructor
  · intro hlt
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · exact hxy
    · exact absurd hlt (lt_irrefl _)
    · exact absurd (lt_trans hlt (rankVL_lt_of_lt asn hy hx hyx)) (lt_irrefl _)
  · exact rankVL_lt_of_lt asn hx hy

theorem rankVL_inj {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) {x y : ℝ}
    (hx : x ∈ asn.VL) (hy : y ∈ asn.VL) :
    rankVL asn x = rankVL asn y ↔ x = y := by
  constructor
  · intro heq
    rcases lt_trichotomy x y with hxy | h | hyx
    · exact absurd (rankVL_lt_of_lt asn hx hy hxy) (by rw [heq]; exact lt_irrefl _)
    · exact h
    · exact absurd (rankVL_lt_of_lt asn hy hx hyx) (by rw [heq]; exact lt_irrefl _)
  · rintro rfl; rfl

theorem mem_VL_of_mem_U {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (s : Fin (m + 1)) {u : ℝ} (hu : u ∈ asn.U s) :
    u ∈ asn.VL := by
  open Classical in
  obtain ⟨hu_tree, huL⟩ := (mem_projL_iff asn.Lm (asn.hBST s) u).mp hu
  exact Finset.mem_filter.mpr ⟨asn.hActiveSub s ((mem_keyFinset_iff _ u).mpr hu_tree), huL⟩

/-! ### Order-Preserving `BinaryTree.map` Lemmas -/

theorem toKeyList_map {α β : Type} (g : α → β) (t : BinaryTree α) :
    (t.map g).toKeyList = t.toKeyList.map g := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    show (l.map g).toKeyList ++ [g k] ++ (r.map g).toKeyList = _
    rw [ihl, ihr, BinaryTree.toKeyList_node]
    simp [List.map_append]

theorem mem_map_iff {α β : Type} (g : α → β) (t : BinaryTree α) (w : β) :
    w ∈ t.map g ↔ ∃ x ∈ t, g x = w := by
  rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_map, List.mem_map]
  simp [BinaryTree.mem_iff_mem_toKeyList]

theorem map_eq_nil_iff {α β : Type} (g : α → β) (t : BinaryTree α) :
    t.map g = .nil ↔ t = .nil := by
  cases t with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | node _ _ _ =>
    constructor
    · intro h; cases h
    · intro h; cases h

theorem minKey_map {α β : Type} (g : α → β) (t : BinaryTree α) :
    (t.map g).minKey? = t.minKey?.map g := by
  rw [minKey_eq_head_toKeyList, minKey_eq_head_toKeyList, toKeyList_map, List.head?_map]

theorem leftSpine_map {α β : Type} (g : α → β) (t : BinaryTree α) :
    leftSpine (t.map g) = (leftSpine t).map g := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    show leftSpine (l.map g) ++ [g k] = _
    rw [ihl, leftSpine, List.map_append]
    rfl

theorem rightSpine_map {α β : Type} (g : α → β) (t : BinaryTree α) :
    rightSpine (t.map g) = (rightSpine t).map g := by
  induction t with
  | nil => rfl
  | node k l r _ ihr =>
    show g k :: rightSpine (r.map g) = _
    rw [ihr]
    rfl

theorem adjacentPairs_map {α β : Type} (g : α → β) :
    ∀ xs : List α, adjacentPairs (xs.map g) = (adjacentPairs xs).map (fun p => (g p.1, g p.2))
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
    simp [adjacentPairs, adjacentPairs_map g rest]

theorem tail_map {α β : Type} (g : α → β) :
    ∀ xs : List α, (xs.map g).tail = xs.tail.map g
  | [] => rfl
  | _ :: _ => rfl

theorem popCascadePairs_map {α β : Type} (g : α → β) (t : BinaryTree α) :
    popCascadePairs (t.map g) = (popCascadePairs t).map (fun p => (g p.1, g p.2)) := by
  unfold popCascadePairs
  rw [leftSpine_map, tail_map, adjacentPairs_map]

theorem spliceMin_map {α β : Type} (g : α → β) :
    ∀ t : BinaryTree α, spliceMin (t.map g) = (spliceMin t).map g
  | .nil => rfl
  | .node _ .nil _ => rfl
  | .node k (.node lk ll lr) r => by
    show BinaryTree.node (g k) (spliceMin ((BinaryTree.node lk ll lr).map g)) (r.map g) =
      BinaryTree.node (g k) ((spliceMin (.node lk ll lr)).map g) (r.map g)
    rw [spliceMin_map g (.node lk ll lr)]

theorem isBST_map_of_strictMonoOn {α β : Type} [LinearOrder α] [LinearOrder β]
    {g : α → β} {S : Set α} (hmono : ∀ x ∈ S, ∀ y ∈ S, x < y → g x < g y)
    {t : BinaryTree α} (ht : t.IsBST) (hS : ∀ x ∈ t, x ∈ S) :
    (t.map g).IsBST := by
  rw [SplayTree.IsBST_iff_toKeyList_sorted, toKeyList_map]
  have hsort := (SplayTree.IsBST_iff_toKeyList_sorted t).mp ht
  have hmem : ∀ x ∈ t.toKeyList, x ∈ S := fun x hx =>
    hS x (BinaryTree.mem_iff_mem_toKeyList.mpr hx)
  clear ht hS
  generalize t.toKeyList = kl at hsort hmem
  induction kl with
  | nil => simp
  | cons a as ih =>
    obtain ⟨ha_lt, has_sort⟩ := List.pairwise_cons.mp hsort
    simp only [List.map_cons, List.pairwise_cons, List.mem_map]
    refine ⟨?_, ih has_sort (fun x hx => hmem x (List.mem_cons_of_mem _ hx))⟩
    rintro _ ⟨b, hb, rfl⟩
    exact hmono a (hmem a List.mem_cons_self) b (hmem b (List.mem_cons_of_mem _ hb)) (ha_lt b hb)

theorem strictMonoOn_inj {α β : Type} [LinearOrder α] [LinearOrder β]
    {g : α → β} {S : Set α} (hmono : ∀ x ∈ S, ∀ y ∈ S, x < y → g x < g y)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    (g x < g y ↔ x < y) ∧ (g x = g y ↔ x = y) := by
  have hlt : g x < g y ↔ x < y := by
    constructor
    · intro h
      rcases lt_trichotomy x y with hxy | rfl | hyx
      · exact hxy
      · exact absurd h (lt_irrefl _)
      · exact absurd (lt_trans h (hmono y hy x hx hyx)) (lt_irrefl _)
    · exact hmono x hx y hy
  refine ⟨hlt, ?_⟩
  constructor
  · intro heq
    rcases lt_trichotomy x y with hxy | h | hyx
    · exact absurd (hlt.mpr hxy) (by rw [heq]; exact lt_irrefl _)
    · exact h
    · exact absurd (hmono y hy x hx hyx) (by rw [heq]; exact lt_irrefl _)
  · rintro rfl; rfl

theorem rotateRightEdge_map_of_strictMonoOn {α β : Type} [LinearOrder α] [LinearOrder β]
    {g : α → β} {S : Set α} (hmono : ∀ x ∈ S, ∀ y ∈ S, x < y → g x < g y) :
    ∀ {t : BinaryTree α}, (∀ u ∈ t, u ∈ S) → ∀ {x p : α}, x ∈ S → p ∈ S →
      rotateRightEdge (t.map g) (g x) (g p) = (rotateRightEdge t x p).map g
  | .nil, _, _, _, _, _ => rfl
  | .node k l r, hS, x, p, hx, hp => by
    have hk : k ∈ S := hS k .here
    have hlS : ∀ u ∈ l, u ∈ S := fun u hu => hS u (.left hu)
    have hrS : ∀ u ∈ r, u ∈ S := fun u hu => hS u (.right hu)
    have hpk := (strictMonoOn_inj hmono hp hk).1
    have hkp := (strictMonoOn_inj hmono hk hp).1
    show rotateRightEdge (.node (g k) (l.map g) (r.map g)) (g x) (g p) = _
    simp only [rotateRightEdge, hpk, hkp]
    split_ifs with h1 h2
    · show BinaryTree.node (g k) (rotateRightEdge (l.map g) (g x) (g p)) (r.map g) =
        BinaryTree.node (g k) ((rotateRightEdge l x p).map g) (r.map g)
      rw [rotateRightEdge_map_of_strictMonoOn hmono hlS hx hp]
    · show BinaryTree.node (g k) (l.map g) (rotateRightEdge (r.map g) (g x) (g p)) =
        BinaryTree.node (g k) (l.map g) ((rotateRightEdge r x p).map g)
      rw [rotateRightEdge_map_of_strictMonoOn hmono hrS hx hp]
    · cases l with
      | nil => rfl
      | node lx a b =>
        have hlx : lx ∈ S := hlS lx .here
        have hlx_eq := (strictMonoOn_inj hmono hlx hx).2
        show (if g lx = g x then BinaryTree.node (g lx) (a.map g) (.node (g k) (b.map g) (r.map g))
              else .node (g k) (.node (g lx) (a.map g) (b.map g)) (r.map g)) = _
        simp only [hlx_eq]
        split_ifs <;> rfl

theorem rotateLeftEdge_map_of_strictMonoOn {α β : Type} [LinearOrder α] [LinearOrder β]
    {g : α → β} {S : Set α} (hmono : ∀ x ∈ S, ∀ y ∈ S, x < y → g x < g y) :
    ∀ {t : BinaryTree α}, (∀ u ∈ t, u ∈ S) → ∀ {x p : α}, x ∈ S → p ∈ S →
      rotateLeftEdge (t.map g) (g x) (g p) = (rotateLeftEdge t x p).map g
  | .nil, _, _, _, _, _ => rfl
  | .node k l r, hS, x, p, hx, hp => by
    have hk : k ∈ S := hS k .here
    have hlS : ∀ u ∈ l, u ∈ S := fun u hu => hS u (.left hu)
    have hrS : ∀ u ∈ r, u ∈ S := fun u hu => hS u (.right hu)
    have hpk := (strictMonoOn_inj hmono hp hk).1
    have hkp := (strictMonoOn_inj hmono hk hp).1
    show rotateLeftEdge (.node (g k) (l.map g) (r.map g)) (g x) (g p) = _
    simp only [rotateLeftEdge, hpk, hkp]
    split_ifs with h1 h2
    · show BinaryTree.node (g k) (rotateLeftEdge (l.map g) (g x) (g p)) (r.map g) =
        BinaryTree.node (g k) ((rotateLeftEdge l x p).map g) (r.map g)
      rw [rotateLeftEdge_map_of_strictMonoOn hmono hlS hx hp]
    · show BinaryTree.node (g k) (l.map g) (rotateLeftEdge (r.map g) (g x) (g p)) =
        BinaryTree.node (g k) (l.map g) ((rotateLeftEdge r x p).map g)
      rw [rotateLeftEdge_map_of_strictMonoOn hmono hrS hx hp]
    · cases r with
      | nil => rfl
      | node rx b c =>
        have hrx : rx ∈ S := hrS rx .here
        have hrx_eq := (strictMonoOn_inj hmono hrx hx).2
        show (if g rx = g x then BinaryTree.node (g rx) (.node (g k) (l.map g) (b.map g)) (c.map g)
              else .node (g k) (l.map g) (.node (g rx) (b.map g) (c.map g))) = _
        simp only [hrx_eq]
        split_ifs <;> rfl

theorem mem_of_mem_adjacentPairs {α : Type} :
    ∀ {xs : List α} {p : α × α}, p ∈ adjacentPairs xs → p.1 ∈ xs ∧ p.2 ∈ xs
  | [], _, hp => by simp [adjacentPairs] at hp
  | [_], _, hp => by simp [adjacentPairs] at hp
  | a :: b :: rest, p, hp => by
    simp only [adjacentPairs, List.mem_cons] at hp
    rcases hp with rfl | hrest
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
    · obtain ⟨h1, h2⟩ := mem_of_mem_adjacentPairs hrest
      exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h1),
             List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2)⟩

theorem popCascade_map_of_strictMonoOn {α β : Type} [LinearOrder α] [LinearOrder β]
    {g : α → β} {S : Set α} (hmono : ∀ x ∈ S, ∀ y ∈ S, x < y → g x < g y)
    {t : BinaryTree α} (hS : ∀ u ∈ t, u ∈ S) :
    popCascade (t.map g) = (popCascade t).map g := by
  unfold popCascade
  rw [popCascadePairs_map, spliceMin_map]
  have hspS : ∀ u ∈ spliceMin t, u ∈ S := fun u hu =>
    hS u (BinaryTree.mem_iff_mem_toKeyList.mpr
      (toKeyList_spliceMin_sub t u (BinaryTree.mem_iff_mem_toKeyList.mp hu)))
  have hpairsS : ∀ p ∈ popCascadePairs t, p.1 ∈ S ∧ p.2 ∈ S := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_of_mem_adjacentPairs hp
    exact ⟨hS _ (mem_leftSpine (List.mem_of_mem_tail h1)),
           hS _ (mem_leftSpine (List.mem_of_mem_tail h2))⟩
  generalize popCascadePairs t = pairs at hpairsS
  generalize spliceMin t = acc at hspS
  induction pairs generalizing acc with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨hp1, hp2⟩ := hpairsS p List.mem_cons_self
    simp only [List.map_cons, List.foldl_cons]
    rw [rotateRightEdge_map_of_strictMonoOn hmono hspS hp1 hp2]
    apply ih
    · intro q hq; exact hpairsS q (List.mem_cons_of_mem _ hq)
    · intro u hu
      rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_rotateRightEdge,
          ← BinaryTree.mem_iff_mem_toKeyList] at hu
      exact hspS u hu

/-! ### `rightSpineConcat`, `rightChain`, `pullUpOps`, and `rotLeftSpineOps` -/

theorem toKeyList_rightSpineConcat {α : Type} (A B : BinaryTree α) :
    (rightSpineConcat A B).toKeyList = A.toKeyList ++ B.toKeyList := by
  induction A with
  | nil => rfl
  | node k l r _ ihr =>
    simp [rightSpineConcat, BinaryTree.toKeyList_node, ihr, List.append_assoc]

theorem mem_rightSpineConcat_iff {α : Type} (A B : BinaryTree α) (x : α) :
    x ∈ rightSpineConcat A B ↔ x ∈ A ∨ x ∈ B := by
  rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_rightSpineConcat, List.mem_append,
    ← BinaryTree.mem_iff_mem_toKeyList, ← BinaryTree.mem_iff_mem_toKeyList]

theorem rightSpine_rightSpineConcat {α : Type} (A B : BinaryTree α) :
    rightSpine (rightSpineConcat A B) = rightSpine A ++ rightSpine B := by
  induction A with
  | nil => rfl
  | node k l r _ ihr =>
    simp [rightSpineConcat, rightSpine, ihr]

theorem isBST_rightSpineConcat {α : Type} [LinearOrder α] {A B : BinaryTree α}
    (hA : A.IsBST) (hB : B.IsBST) (hAB : ∀ x ∈ A, ∀ y ∈ B, x < y) :
    (rightSpineConcat A B).IsBST := by
  rw [SplayTree.IsBST_iff_toKeyList_sorted, toKeyList_rightSpineConcat, List.pairwise_append]
  refine ⟨(SplayTree.IsBST_iff_toKeyList_sorted A).mp hA,
          (SplayTree.IsBST_iff_toKeyList_sorted B).mp hB, ?_⟩
  intro x hx y hy
  exact hAB x (BinaryTree.mem_iff_mem_toKeyList.mpr hx)
    y (BinaryTree.mem_iff_mem_toKeyList.mpr hy)

def rightChain {α : Type} : List α → BinaryTree α
  | [] => .nil
  | z :: zs => .node z .nil (rightChain zs)

theorem toKeyList_rightChain {α : Type} : ∀ zs : List α, (rightChain zs).toKeyList = zs
  | [] => rfl
  | z :: zs => by simp [rightChain, BinaryTree.toKeyList_node, toKeyList_rightChain zs]

theorem mem_rightChain_iff {α : Type} (zs : List α) (x : α) :
    x ∈ rightChain zs ↔ x ∈ zs := by
  rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_rightChain]

theorem isBST_rightChain {α : Type} [LinearOrder α] {zs : List α} (h : zs.Pairwise (· < ·)) :
    (rightChain zs).IsBST := by
  rw [SplayTree.IsBST_iff_toKeyList_sorted, toKeyList_rightChain]
  exact h

def shiftRightSpineOp : OneSidedOp → OneSidedOp
  | .rightSpineLeftRot d => .rightSpineLeftRot (d + 1)
  | op => op

def isRightSpineRotOp : OneSidedOp → Bool
  | .rightSpineLeftRot _ => true
  | _ => false

theorem shiftRightSpineOp_sim (P k : ℕ) (l : BinaryTree ℕ) :
    ∀ (ops : List OneSidedOp) (T : BinaryTree ℕ),
      (∀ op ∈ ops, isRightSpineRotOp op = true) →
      ValidOneSidedOps P T ops →
      (∀ op ∈ ops.map shiftRightSpineOp, isRightSpineRotOp op = true) ∧
      ValidOneSidedOps P (.node k l T) (ops.map shiftRightSpineOp) ∧
      (ops.map shiftRightSpineOp).foldl OneSidedOp.step (.node k l T) =
        .node k l (ops.foldl OneSidedOp.step T) ∧
      oneSidedCascadeCost (.node k l T) (ops.map shiftRightSpineOp) = 0 ∧
      (ops.map shiftRightSpineOp).filterMap (fun | .pop s => some s | _ => none) = []
  | [], T, _, _ => by
    simp [ValidOneSidedOps, oneSidedCascadeCost]
  | op :: rest, T, hrot, hval => by
    have hop_rot := hrot op List.mem_cons_self
    cases op with
    | push _ => simp [isRightSpineRotOp] at hop_rot
    | pop _ => simp [isRightSpineRotOp] at hop_rot
    | rightSpineLeftRot d =>
      obtain ⟨⟨hd1, hd2⟩, hval_rest⟩ := hval
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      have hstep_eq :
          OneSidedOp.step (.node k l T) (.rightSpineLeftRot (d' + 2)) =
            .node k l (OneSidedOp.step T (.rightSpineLeftRot (d' + 1))) := rfl
      obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ :=
        shiftRightSpineOp_sim P k l rest (OneSidedOp.step T (.rightSpineLeftRot (d' + 1)))
          (fun x hx => hrot x (List.mem_cons_of_mem _ hx)) hval_rest
      simp only [List.map_cons, shiftRightSpineOp]
      refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · rfl
        · exact ih1 x hx'
      · simp only [OneSidedOp.Valid, rightSpine, List.length_cons]
        omega
      · rwa [hstep_eq]
      · simp only [List.foldl_cons, hstep_eq, ih3]
      · simp only [oneSidedCascadeCost, OneSidedOp.cascadeRots, zero_add, hstep_eq, ih4]
      · simp only [List.filterMap_cons, ih5]

def pullUpOps : BinaryTree ℕ → List OneSidedOp
  | .nil => []
  | .node _ _ r => (pullUpOps r).map shiftRightSpineOp ++ [.rightSpineLeftRot 1]

theorem validOneSidedOps_append (P : ℕ) :
    ∀ (xs ys : List OneSidedOp) (t : BinaryTree ℕ),
      ValidOneSidedOps P t (xs ++ ys) ↔
        ValidOneSidedOps P t xs ∧ ValidOneSidedOps P (xs.foldl OneSidedOp.step t) ys
  | [], ys, t => by simp [ValidOneSidedOps]
  | op :: xs, ys, t => by
    simp only [List.cons_append, ValidOneSidedOps, List.foldl_cons,
      validOneSidedOps_append P xs ys (op.step t), and_assoc]

theorem oneSidedCascadeCost_append :
    ∀ (xs ys : List OneSidedOp) (t : BinaryTree ℕ),
      oneSidedCascadeCost t (xs ++ ys) =
        oneSidedCascadeCost t xs + oneSidedCascadeCost (xs.foldl OneSidedOp.step t) ys
  | [], ys, t => by simp [oneSidedCascadeCost]
  | op :: xs, ys, t => by
    simp only [List.cons_append, oneSidedCascadeCost, List.foldl_cons,
      oneSidedCascadeCost_append xs ys (op.step t), Nat.add_assoc]

theorem pullUpOps_sim (P w : ℕ) (C : BinaryTree ℕ) :
    ∀ U : BinaryTree ℕ,
      (∀ op ∈ pullUpOps U, isRightSpineRotOp op = true) ∧
      ValidOneSidedOps P (rightSpineConcat U (.node w .nil C)) (pullUpOps U) ∧
      (pullUpOps U).foldl OneSidedOp.step (rightSpineConcat U (.node w .nil C)) = .node w U C ∧
      oneSidedCascadeCost (rightSpineConcat U (.node w .nil C)) (pullUpOps U) = 0 ∧
      (pullUpOps U).filterMap (fun | .pop s => some s | _ => none) = []
  | .nil => by
    simp [pullUpOps, rightSpineConcat, ValidOneSidedOps, oneSidedCascadeCost]
  | .node k l r => by
    obtain ⟨ih_rot, ih_val, ih_fold, _, _⟩ := pullUpOps_sim P w C r
    obtain ⟨sh_rot, sh_val, sh_fold, sh_cost, sh_pop⟩ :=
      shiftRightSpineOp_sim P k l (pullUpOps r) (rightSpineConcat r (.node w .nil C)) ih_rot ih_val
    rw [ih_fold] at sh_fold
    simp only [pullUpOps, rightSpineConcat]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro op hop
      rcases List.mem_append.mp hop with h1 | h2
      · exact sh_rot op h1
      · simp only [List.mem_singleton] at h2
        rw [h2]; rfl
    · rw [validOneSidedOps_append]
      refine ⟨sh_val, ?_⟩
      rw [sh_fold]
      simp [ValidOneSidedOps, OneSidedOp.Valid, rightSpine]
    · rw [List.foldl_append, sh_fold]
      rfl
    · rw [oneSidedCascadeCost_append, sh_cost, sh_fold]
      rfl
    · rw [List.filterMap_append, sh_pop]
      rfl

def rotLeftSpineOps : BinaryTree ℕ → ℕ → ℕ → List OneSidedOp
  | .nil, _, _ => []
  | .node k _ r, wx, wp =>
    if wp < k then []
    else if k < wp then (rotLeftSpineOps r wx wp).map shiftRightSpineOp
    else match r with
      | .node rx _ _ => if rx = wx then [.rightSpineLeftRot 1] else []
      | .nil => []

theorem rotLeftSpineOps_sim (P : ℕ) (C : BinaryTree ℕ) (wx wp : ℕ) :
    ∀ {U : BinaryTree ℕ}, U.IsBST → wp ∈ rightSpine U →
      (∀ op ∈ rotLeftSpineOps U wx wp, isRightSpineRotOp op = true) ∧
      ValidOneSidedOps P (rightSpineConcat U C) (rotLeftSpineOps U wx wp) ∧
      (rotLeftSpineOps U wx wp).foldl OneSidedOp.step (rightSpineConcat U C) =
        rightSpineConcat (rotateLeftEdge U wx wp) C ∧
      oneSidedCascadeCost (rightSpineConcat U C) (rotLeftSpineOps U wx wp) = 0 ∧
      (rotLeftSpineOps U wx wp).filterMap (fun | .pop s => some s | _ => none) = []
  | .nil, _, hwp => by simp [rightSpine] at hwp
  | .node k l r, hU, hwp => by
    have hr_bst := BinaryTree.IsBST_right_of_IsBST hU
    have hkp_le : k ≤ wp := by
      simp only [rightSpine, List.mem_cons] at hwp
      rcases hwp with rfl | hwpr
      · exact le_rfl
      · exact le_of_lt (BinaryTree.gt_of_IsBST_right l k r hU (mem_rightSpine hwpr))
    have hnot_lt : ¬ (wp < k) := not_lt.mpr hkp_le
    by_cases hkp : k < wp
    · have hwpr : wp ∈ rightSpine r := by
        simp only [rightSpine, List.mem_cons] at hwp
        rcases hwp with rfl | hwpr
        · exact absurd hkp (lt_irrefl _)
        · exact hwpr
      obtain ⟨ih_rot, ih_val, ih_fold, _, _⟩ := rotLeftSpineOps_sim P C wx wp hr_bst hwpr
      obtain ⟨sh_rot, sh_val, sh_fold, sh_cost, sh_pop⟩ :=
        shiftRightSpineOp_sim P k l (rotLeftSpineOps r wx wp) (rightSpineConcat r C) ih_rot ih_val
      rw [ih_fold] at sh_fold
      simp only [rotLeftSpineOps, rotateLeftEdge, rightSpineConcat, hnot_lt, hkp, ↓reduceIte]
      exact ⟨sh_rot, sh_val, sh_fold, sh_cost, sh_pop⟩
    · have hpk_eq : wp = k := le_antisymm (not_lt.mp hkp) hkp_le
      subst hpk_eq
      simp only [rotLeftSpineOps, rotateLeftEdge, lt_irrefl, ↓reduceIte]
      cases r with
      | nil =>
        simp [ValidOneSidedOps, oneSidedCascadeCost]
      | node rx b c =>
        dsimp only
        by_cases hrx : rx = wx
        · subst hrx
          simp only [↓reduceIte]
          refine ⟨?_, ?_, rfl, rfl, rfl⟩
          · intro op hop
            simp only [List.mem_singleton] at hop
            rw [hop]; rfl
          · simp [ValidOneSidedOps, OneSidedOp.Valid, rightSpineConcat, rightSpine]
        · simp [hrx, ValidOneSidedOps, oneSidedCascadeCost]

/-! ### `popCascade` on `rightSpineConcat` and `projL` Cascade Commutation -/

theorem leftSpine_rightSpineConcat_of_ne_nil {α : Type} {H : BinaryTree α} (C : BinaryTree α)
    (hne : H ≠ .nil) : leftSpine (rightSpineConcat H C) = leftSpine H := by
  cases H with
  | nil => exact absurd rfl hne
  | node k l r => rfl

theorem minKey_rightSpineConcat_of_ne_nil {α : Type} {H : BinaryTree α} (C : BinaryTree α)
    (hne : H ≠ .nil) : (rightSpineConcat H C).minKey? = H.minKey? := by
  cases H with
  | nil => exact absurd rfl hne
  | node k l r => rfl

theorem spliceMin_rightSpineConcat_of_ne_nil {α : Type} {H : BinaryTree α} (C : BinaryTree α)
    (hne : H ≠ .nil) :
    spliceMin (rightSpineConcat H C) = rightSpineConcat (spliceMin H) C := by
  cases H with
  | nil => exact absurd rfl hne
  | node k l r =>
    cases l <;> rfl

theorem rotateRightEdge_rightSpineConcat_of_mem {α : Type} [LinearOrder α]
    {A C : BinaryTree α} (hA : A.IsBST) {x p : α} (hp : p ∈ A) :
    rotateRightEdge (rightSpineConcat A C) x p = rightSpineConcat (rotateRightEdge A x p) C := by
  induction A with
  | nil => cases hp
  | node k l r _ ihr =>
    have hr_bst := BinaryTree.IsBST_right_of_IsBST hA
    simp only [rightSpineConcat, rotateRightEdge]
    split_ifs with hpk hkp
    · rfl
    · rcases BinaryTree.mem_node_iff.mp hp with rfl | hpl | hpr
      · exact absurd hkp (lt_irrefl _)
      · exact absurd (lt_trans (BinaryTree.lt_of_IsBST_left l k r hA hpl) hkp) (lt_irrefl _)
      · rw [ihr hr_bst hpr]; rfl
    · cases l with
      | nil => rfl
      | node lx a b =>
        dsimp only
        split_ifs <;> rfl

theorem mem_spliceMin_of_ne_minKey {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) {q x : α} (hmin : t.minKey? = some q) (hx : x ∈ t) (hne : x ≠ q) :
    x ∈ spliceMin t := by
  induction t with
  | nil => cases hx
  | node k l r ihl _ =>
    have hl_bst := BinaryTree.IsBST_left_of_IsBST ht
    cases l with
    | nil =>
      simp only [BinaryTree.minKey?, Option.some.injEq] at hmin
      subst hmin
      rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
      · exact absurd rfl hne
      · cases hxl
      · exact hxr
    | node lk ll lr =>
      obtain ⟨m', hm'⟩ := exists_minKey_of_ne_nil (t := BinaryTree.node lk ll lr) (by simp)
      have hmin_eq : (BinaryTree.node k (.node lk ll lr) r).minKey? = some m' := by
        show (match (BinaryTree.node lk ll lr).minKey? with
              | none => some k | some x => some x) = some m'
        rw [hm']
      rw [hmin_eq, Option.some.injEq] at hmin
      subst m'
      have hsp : spliceMin (.node k (.node lk ll lr) r) =
          .node k (spliceMin (.node lk ll lr)) r := rfl
      rw [hsp]
      rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
      · exact .here
      · exact .left (ihl hl_bst hm' hxl)
      · exact .right hxr

theorem popCascade_rightSpineConcat_of_ne_nil {α : Type} [LinearOrder α]
    {H : BinaryTree α} (C : BinaryTree α) (hH : H.IsBST) (hne : H ≠ .nil) :
    popCascade (rightSpineConcat H C) = rightSpineConcat (popCascade H) C := by
  unfold popCascade
  have hcp : popCascadePairs (rightSpineConcat H C) = popCascadePairs H := by
    simp [popCascadePairs, leftSpine_rightSpineConcat_of_ne_nil C hne]
  rw [hcp, spliceMin_rightSpineConcat_of_ne_nil C hne]
  obtain ⟨q, hmin⟩ := exists_minKey_of_ne_nil hne
  have hls_sort : (leftSpine H).Pairwise (· < ·) := pairwise_leftSpine hH
  have hsp_bst : (spliceMin H).IsBST := isBST_spliceMin hH
  have hpairs_in : ∀ p ∈ popCascadePairs H, p.2 ∈ spliceMin H := by
    intro p hp
    obtain ⟨_, h2⟩ := mem_of_mem_adjacentPairs hp
    cases hls : leftSpine H with
    | nil =>
      rw [hls] at h2
      simp at h2
    | cons v0 rest =>
      rw [hls] at h2 hls_sort
      simp only [List.tail_cons] at h2
      have hv0_mem : v0 ∈ H := mem_leftSpine (by rw [hls]; exact List.mem_cons_self)
      have hq_le_v0 : q ≤ v0 := minKey_le_of_mem hH hmin hv0_mem
      have hv0_lt_p2 : v0 < p.2 := (List.pairwise_cons.mp hls_sort).1 p.2 h2
      have hp2_mem : p.2 ∈ H := mem_leftSpine (by rw [hls]; exact List.mem_cons_of_mem _ h2)
      exact mem_spliceMin_of_ne_minKey hH hmin hp2_mem (ne_of_gt (lt_of_le_of_lt hq_le_v0 hv0_lt_p2))
  generalize popCascadePairs H = pairs at hpairs_in
  generalize spliceMin H = acc at hsp_bst hpairs_in
  induction pairs generalizing acc with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.foldl_cons]
    rw [rotateRightEdge_rightSpineConcat_of_mem hsp_bst (hpairs_in p List.mem_cons_self)]
    apply ih (rotateRightEdge acc p.1 p.2) (isBST_rotateRightEdge hsp_bst p.1 p.2)
    intro p' hp'
    rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_rotateRightEdge,
        ← BinaryTree.mem_iff_mem_toKeyList]
    exact hpairs_in p' (List.mem_cons_of_mem _ hp')

theorem adjacentPairs_filter_le_and_projL {α : Type} [LinearOrder α] (L : α) :
    ∀ (xs : List α), xs.Pairwise (· < ·) → ∀ (cur : BinaryTree α), cur.IsBST →
      (open Classical in
        adjacentPairs (xs.filter (fun x => decide (x ≤ L))) =
          (adjacentPairs xs).filter (fun p => decide (p.1 ≤ L ∧ p.2 ≤ L))) ∧
      projL L ((adjacentPairs xs).foldl (fun acc p => rotateRightEdge acc p.1 p.2) cur) =
        (open Classical in
          (adjacentPairs (xs.filter (fun x => decide (x ≤ L)))).foldl
            (fun acc p => rotateRightEdge acc p.1 p.2) (projL L cur)) := by
  open Classical in
  intro xs
  induction xs using List.twoStepInduction with
  | nil =>
    intro _ cur _
    simp [adjacentPairs]
  | singleton a =>
    intro _ cur _
    by_cases ha : a ≤ L <;> simp [adjacentPairs, ha]
  | cons_cons a b rest ih _ =>
    intro hsort cur hcur
    obtain ⟨hab_rest, hrest_sort⟩ := List.pairwise_cons.mp hsort
    obtain ⟨hb_rest, hrest_sort'⟩ := List.pairwise_cons.mp hrest_sort
    have hab : a < b := hab_rest b List.mem_cons_self
    by_cases hbL : b ≤ L
    · have haL : a ≤ L := le_trans (le_of_lt hab) hbL
      obtain ⟨ih1, ih2⟩ := ih hrest_sort' (rotateRightEdge cur a b) (isBST_rotateRightEdge hcur a b)
      have hrot : projL L (rotateRightEdge cur a b) = rotateRightEdge (projL L cur) a b := by
        rw [projL_rotateRightEdge L hcur hab]
        simp [hbL]
      rw [hrot] at ih2
      simp [adjacentPairs, haL, hbL, ih1, ih2]
    · have hgt : L < b := lt_of_not_ge hbL
      have hrest_nil : rest.filter (fun x => decide (x ≤ L)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c hc
        simp [not_le.mpr (lt_trans hgt (hb_rest c hc))]
      have hadj_nil : (adjacentPairs rest).filter (fun p => decide (p.1 ≤ L ∧ p.2 ≤ L)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        obtain ⟨_, hp2⟩ := mem_of_mem_adjacentPairs hp
        simp [not_le.mpr (lt_trans hgt (hb_rest p.2 hp2))]
      have hfold_noop :
          ∀ (ps : List (α × α)) (acc : BinaryTree α), acc.IsBST →
            (∀ p ∈ ps, p.1 < p.2 ∧ L < p.2) →
            projL L (ps.foldl (fun t p => rotateRightEdge t p.1 p.2) acc) = projL L acc := by
        intro ps
        induction ps with
        | nil => intro acc _ _; rfl
        | cons p ps' ihp =>
          intro acc hacc hps
          obtain ⟨hp12, hpL⟩ := hps p List.mem_cons_self
          simp only [List.foldl_cons]
          rw [ihp (rotateRightEdge acc p.1 p.2) (isBST_rotateRightEdge hacc p.1 p.2)
            (fun q hq => hps q (List.mem_cons_of_mem _ hq))]
          rw [projL_rotateRightEdge L hacc hp12]
          simp [not_le.mpr hpL]
      have hpairs_gt : ∀ p ∈ (a, b) :: adjacentPairs rest, p.1 < p.2 ∧ L < p.2 := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hprest
        · exact ⟨hab, hgt⟩
        · have hpair_adj : ∀ {ys : List α}, ys.Pairwise (· < ·) →
              ∀ q ∈ adjacentPairs ys, q.1 < q.2 ∧ q.2 ∈ ys := by
            intro ys
            induction ys using List.twoStepInduction with
            | nil => intro _ q hq; simp [adjacentPairs] at hq
            | singleton _ => intro _ q hq; simp [adjacentPairs] at hq
            | cons_cons u v ws ihw _ =>
              intro hys q hq
              obtain ⟨huv, hvw⟩ := List.pairwise_cons.mp hys
              rcases List.mem_cons.mp hq with rfl | hqw
              · exact ⟨huv v List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
              · obtain ⟨h1, h2⟩ := ihw (List.pairwise_cons.mp hvw).2 q hqw
                exact ⟨h1, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h2)⟩
          obtain ⟨hq12, hq2⟩ := hpair_adj hrest_sort' p hprest
          exact ⟨hq12, lt_trans hgt (hb_rest p.2 hq2)⟩
      have hb_dec : decide (b ≤ L) = false := decide_eq_false hbL
      have hlhs_nil : adjacentPairs ((a :: b :: rest).filter (fun x => decide (x ≤ L))) = [] := by
        simp only [List.filter_cons, hb_dec, Bool.false_eq_true, ↓reduceIte]
        rw [hrest_nil]
        cases decide (a ≤ L) <;> rfl
      have hrhs_nil : (adjacentPairs (a :: b :: rest)).filter (fun p => decide (p.1 ≤ L ∧ p.2 ≤ L)) = [] := by
        have hab_dec : decide ((a, b).1 ≤ L ∧ (a, b).2 ≤ L) = false :=
          decide_eq_false (fun h => hbL h.2)
        change ((a, b) :: adjacentPairs rest).filter (fun p => decide (p.1 ≤ L ∧ p.2 ≤ L)) = []
        simp only [List.filter_cons, hab_dec, Bool.false_eq_true, ↓reduceIte]
        exact hadj_nil
      refine ⟨by rw [hlhs_nil, hrhs_nil], ?_⟩
      rw [hlhs_nil]
      exact hfold_noop ((a, b) :: adjacentPairs rest) cur hcur hpairs_gt

theorem mem_rightSpine_spliceMax_of_mem_tail {α : Type} :
    ∀ (t : BinaryTree α) {u : α},
      u ∈ (rightSpineBottomUp t).tail → u ∈ rightSpine (spliceMax t)
  | .nil, _, hu => by simp [rightSpineBottomUp, rightSpine] at hu
  | .node k l .nil, _, hu => by simp [rightSpineBottomUp, rightSpine] at hu
  | .node k l (.node rk rl rr), u, hu => by
    let R := BinaryTree.node rk rl rr
    have hrsR_ne : rightSpineBottomUp R ≠ [] := by
      simp [R, rightSpineBottomUp, rightSpine]
    obtain ⟨u0, restR, hR⟩ := List.exists_cons_of_ne_nil hrsR_ne
    have hrsT : rightSpineBottomUp (.node k l R) = u0 :: (restR ++ [k]) := by
      unfold rightSpineBottomUp
      show (k :: rightSpine R).reverse = _
      rw [List.reverse_cons]
      change rightSpineBottomUp R ++ [k] = _
      rw [hR]
      rfl
    rw [hrsT, List.tail_cons, List.mem_append, List.mem_singleton] at hu
    have hsp : spliceMax (.node k l R) = .node k l (spliceMax R) := rfl
    rw [hsp]
    simp only [rightSpine, List.mem_cons]
    rcases hu with huR | rfl
    · refine Or.inr (mem_rightSpine_spliceMax_of_mem_tail R ?_)
      rw [hR]; exact huR
    · exact Or.inl rfl

theorem mem_rightSpine_projL_of_le {α : Type} [LinearOrder α] (L : α) :
    ∀ {t : BinaryTree α}, t.IsBST → ∀ {p : α}, p ∈ rightSpine t → p ≤ L →
      p ∈ rightSpine (projL L t)
  | .nil, _, _, hp, _ => by simp [rightSpine] at hp
  | .node k l r, ht, p, hp, hpL => by
    have hr_bst := BinaryTree.IsBST_right_of_IsBST ht
    simp only [rightSpine, List.mem_cons] at hp
    rcases hp with rfl | hpr
    · rw [projL_node_le L p l r ht hpL]
      exact List.mem_cons_self
    · have hkp : k < p := BinaryTree.gt_of_IsBST_right l k r ht (mem_rightSpine hpr)
      have hkL : k ≤ L := le_trans (le_of_lt hkp) hpL
      rw [projL_node_le L k l r ht hkL]
      exact List.mem_cons_of_mem _ (mem_rightSpine_projL_of_le L hr_bst hpr hpL)

/-! ### `tailInjectKeysR`, `simTreeAt`, Step Simulation, and Node Conservation -/

noncomputable def injectVLKey? {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m) : Option ℝ :=
  open Classical in
  match asn.opsR i with
  | .inject z => if z ≤ asn.Lm then some z else none
  | _ => none

noncomputable def tailInjectKeysR {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (k : ℕ) : List ℝ :=
  ((List.finRange m).drop k).filterMap (injectVLKey? asn)

theorem drop_finRange_cons {m k : ℕ} (hk : k < m) :
    (List.finRange m).drop k = ⟨k, hk⟩ :: (List.finRange m).drop (k + 1) := by
  have hlen : k < (List.finRange m).length := by simp [hk]
  rw [List.drop_eq_getElem_cons hlen]
  simp

theorem mem_drop_finRange {m : ℕ} :
    ∀ (k : ℕ) {j : Fin m}, j ∈ (List.finRange m).drop k → k ≤ j.val := by
  intro k
  obtain ⟨d, hd⟩ : ∃ d, m - k = d := ⟨m - k, rfl⟩
  induction d generalizing k with
  | zero =>
    intro j hj
    have hle : (List.finRange m).length ≤ k := by simp; omega
    rw [List.drop_eq_nil_of_le hle] at hj
    cases hj
  | succ d ih =>
    intro j hj
    have hk : k < m := by omega
    rw [drop_finRange_cons hk, List.mem_cons] at hj
    rcases hj with rfl | hj'
    · exact le_rfl
    · exact le_trans (Nat.le_succ k) (ih (k + 1) (by omega) hj')

theorem mem_tailInjectKeysR_props {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) {k : ℕ} {z : ℝ}
    (hz : z ∈ tailInjectKeysR asn k) :
    z ∈ asn.VL ∧ ∃ j : Fin m, k ≤ j.val ∧ asn.opsR j = .inject z ∧ z ≤ asn.Lm := by
  open Classical in
  unfold tailInjectKeysR at hz
  rw [List.mem_filterMap] at hz
  obtain ⟨j, hj_drop, hj_eq⟩ := hz
  have hkj : k ≤ j.val := mem_drop_finRange k hj_drop
  unfold injectVLKey? at hj_eq
  rcases hop : asn.opsR j with _ | _ | _ | z' <;> rw [hop] at hj_eq <;> simp at hj_eq
  obtain ⟨hzL, rfl⟩ := hj_eq
  have hz_mem_succ : z' ∈ asn.treeAt j.succ := by
    unfold ThreeWayKeyAssignment.treeAt
    rw [dequeSeq_succ asn.T0 asn.opsR j, hop]
    exact .here
  have hz_VL : z' ∈ asn.VL :=
    Finset.mem_filter.mpr ⟨asn.hActiveSub j.succ ((mem_keyFinset_iff _ z').mpr hz_mem_succ), hzL⟩
  exact ⟨hz_VL, j, hkj, hop, hzL⟩

noncomputable def tailRanks {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (k : ℕ) : List ℕ :=
  (tailInjectKeysR asn k).map (rankVL asn)

noncomputable def simU {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (s : Fin (m + 1)) : BinaryTree ℕ :=
  (asn.U s).map (rankVL asn)

noncomputable def simTreeAt {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (s : Fin (m + 1)) : BinaryTree ℕ :=
  rightSpineConcat (simU asn s) (rightChain (tailRanks asn s.val))

theorem pairwise_tailInjectKeysR {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (k : ℕ) :
    (tailInjectKeysR asn k).Pairwise (· < ·) := by
  open Classical in
  obtain ⟨d, hd⟩ : ∃ d, m - k = d := ⟨m - k, rfl⟩
  induction d generalizing k with
  | zero =>
    have hle : (List.finRange m).length ≤ k := by simp; omega
    simp [tailInjectKeysR, List.drop_eq_nil_of_le hle]
  | succ d ih =>
    have hk : k < m := by omega
    let ik : Fin m := ⟨k, hk⟩
    have hih := ih (k + 1) (by omega)
    unfold tailInjectKeysR
    rw [drop_finRange_cons hk, List.filterMap_cons]
    cases hinj : injectVLKey? asn ik with
    | none => exact hih
    | some z =>
      simp only [List.pairwise_cons]
      refine ⟨?_, hih⟩
      intro z' hz'
      obtain ⟨_, j, hkj, hop_j, hz'L⟩ := mem_tailInjectKeysR_props asn hz'
      unfold injectVLKey? at hinj
      rcases hop_ik : asn.opsR ik with _ | _ | _ | z0 <;> rw [hop_ik] at hinj <;> simp at hinj
      obtain ⟨hzL, rfl⟩ := hinj
      have hz_succ : z0 ∈ asn.treeAt ik.succ := by
        unfold ThreeWayKeyAssignment.treeAt
        rw [dequeSeq_succ asn.T0 asn.opsR ik, hop_ik]
        exact .here
      have hz_U : z0 ∈ asn.U ik.succ :=
        (mem_projL_iff asn.Lm (asn.hBST ik.succ) z0).mpr ⟨hz_succ, hzL⟩
      exact lt_of_mem_U_before_inject asn j z' hop_j hz'L ik.succ (by dsimp [ik]; omega) z0 hz_U

theorem simTreeAt_props {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (s : Fin (m + 1)) :
    (simU asn s).IsBST ∧
    (simTreeAt asn s).IsBST ∧
    keyFinset (simTreeAt asn s) ⊆ Finset.Icc 1 (popCount ops) := by
  have hmono : ∀ x ∈ (asn.VL : Set ℝ), ∀ y ∈ (asn.VL : Set ℝ), x < y → rankVL asn x < rankVL asn y :=
    fun x hx y hy hxy => rankVL_lt_of_lt asn hx hy hxy
  have hU_S : ∀ x ∈ asn.U s, x ∈ (asn.VL : Set ℝ) :=
    fun x hx => mem_VL_of_mem_U asn s hx
  have hsimU_bst : (simU asn s).IsBST :=
    isBST_map_of_strictMonoOn hmono (isBST_projL asn.Lm (asn.hBST s)) hU_S
  have htail_sort : (tailRanks asn s.val).Pairwise (· < ·) := by
    have hsortR := pairwise_tailInjectKeysR asn s.val
    have hmemR : ∀ z ∈ tailInjectKeysR asn s.val, z ∈ asn.VL :=
      fun z hz => (mem_tailInjectKeysR_props asn hz).1
    unfold tailRanks
    clear hU_S hsimU_bst
    generalize tailInjectKeysR asn s.val = zs at hsortR hmemR
    induction zs with
    | nil => simp
    | cons a as ih =>
      obtain ⟨ha_lt, has_sort⟩ := List.pairwise_cons.mp hsortR
      simp only [List.map_cons, List.pairwise_cons, List.mem_map]
      refine ⟨?_, ih has_sort (fun z hz => hmemR z (List.mem_cons_of_mem _ hz))⟩
      rintro _ ⟨b, hb, rfl⟩
      exact rankVL_lt_of_lt asn (hmemR a List.mem_cons_self)
        (hmemR b (List.mem_cons_of_mem _ hb)) (ha_lt b hb)
  have hchain_bst : (rightChain (tailRanks asn s.val)).IsBST := isBST_rightChain htail_sort
  have hcross : ∀ u ∈ simU asn s, ∀ w ∈ rightChain (tailRanks asn s.val), u < w := by
    intro u hu w hw
    obtain ⟨uR, huR, rfl⟩ := (mem_map_iff (rankVL asn) (asn.U s) u).mp hu
    rw [mem_rightChain_iff, tailRanks, List.mem_map] at hw
    obtain ⟨zR, hzR, rfl⟩ := hw
    obtain ⟨hz_VL, j, hsz, hop_j, hzL⟩ := mem_tailInjectKeysR_props asn hzR
    exact rankVL_lt_of_lt asn (mem_VL_of_mem_U asn s huR) hz_VL
      (lt_of_mem_U_before_inject asn j zR hop_j hzL s hsz uR huR)
  refine ⟨hsimU_bst, isBST_rightSpineConcat hsimU_bst hchain_bst hcross, ?_⟩
  intro w hw
  rw [mem_keyFinset_iff, simTreeAt, mem_rightSpineConcat_iff] at hw
  rw [Finset.mem_Icc]
  rcases hw with hu | hc
  · obtain ⟨uR, huR, rfl⟩ := (mem_map_iff _ _ _).mp hu
    exact rankVL_bounds asn (mem_VL_of_mem_U asn s huR)
  · rw [mem_rightChain_iff, tailRanks, List.mem_map] at hc
    obtain ⟨zR, hzR, rfl⟩ := hc
    exact rankVL_bounds asn (mem_tailInjectKeysR_props asn hzR).1

theorem simTreeAt_last_eq_nil {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) :
    simTreeAt asn (Fin.last m) = .nil := by
  have htail_nil : tailRanks asn (Fin.last m).val = [] := by
    unfold tailRanks tailInjectKeysR
    rw [List.drop_eq_nil_of_le (by simp)]
    rfl
  have hU_nil : asn.U (Fin.last m) = .nil := by
    apply BinaryTree.eq_nil_of_toKeyList_eq_nil
    cases hkl : (asn.U (Fin.last m)).toKeyList with
    | nil => rfl
    | cons x xs =>
      exfalso
      have hx_U : x ∈ asn.U (Fin.last m) :=
        BinaryTree.mem_iff_mem_toKeyList.mpr (by rw [hkl]; exact List.mem_cons_self)
      obtain ⟨hx_tree, hxL⟩ := (mem_projL_iff asn.Lm (asn.hBST (Fin.last m)) x).mp hx_U
      open Classical in
      have hx_surv : x ∈ keyFinset (dequeSeq asn.T0 asn.opsR (Fin.last m)) :=
        (mem_keyFinset_iff _ x).mpr hx_tree
      rw [asn.hSurviving, Finset.mem_filter] at hx_surv
      exact absurd hxL (not_le.mpr hx_surv.2.1)
  unfold simTreeAt simU
  rw [hU_nil, htail_nil]
  rfl

theorem eject_fold_sim {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (C : BinaryTree ℕ) :
    ∀ (eb : List ℝ), eb.Pairwise (· > ·) →
      ∀ (cur : BinaryTree ℝ), cur.IsBST →
        (∀ u ∈ cur, u ∈ asn.everPresentKeys) →
        (∀ u ∈ eb, u ∈ rightSpine cur) →
        ∃ stepOps : List OneSidedOp,
          ValidOneSidedOps (popCount ops)
            (rightSpineConcat ((projL asn.Lm cur).map (rankVL asn)) C) stepOps ∧
          stepOps.foldl OneSidedOp.step
            (rightSpineConcat ((projL asn.Lm cur).map (rankVL asn)) C) =
            rightSpineConcat
              ((projL asn.Lm ((adjacentPairs eb).foldl
                (fun acc p => rotateLeftEdge acc p.1 p.2) cur)).map (rankVL asn)) C ∧
          oneSidedCascadeCost
            (rightSpineConcat ((projL asn.Lm cur).map (rankVL asn)) C) stepOps = 0 ∧
          stepOps.filterMap (fun | .pop s => some s | _ => none) = [] := by
  intro eb
  induction eb using List.twoStepInduction with
  | nil =>
    intro _ cur _ _ _
    exact ⟨[], by simp [ValidOneSidedOps], rfl, rfl, rfl⟩
  | singleton _ =>
    intro _ cur _ _ _
    exact ⟨[], by simp [ValidOneSidedOps], rfl, rfl, rfl⟩
  | cons_cons x p rest ih _ =>
    intro hsort cur hcur hcur_ever hrs
    obtain ⟨hx_gt, hrest_sort⟩ := List.pairwise_cons.mp hsort
    obtain ⟨hp_gt, hrest_sort'⟩ := List.pairwise_cons.mp hrest_sort
    have hpx : p < x := hx_gt p List.mem_cons_self
    have hx_rs : x ∈ rightSpine cur := hrs x List.mem_cons_self
    have hp_rs : p ∈ rightSpine cur := hrs p (List.mem_cons_of_mem _ List.mem_cons_self)
    let cur' := rotateLeftEdge cur x p
    have hcur'_bst : cur'.IsBST := isBST_rotateLeftEdge hcur x p
    have hcur'_ever : ∀ u ∈ cur', u ∈ asn.everPresentKeys := by
      intro u hu
      rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_rotateLeftEdge,
          ← BinaryTree.mem_iff_mem_toKeyList] at hu
      exact hcur_ever u hu
    have hrs' : ∀ u ∈ rest, u ∈ rightSpine cur' := by
      intro u hu
      exact mem_rightSpine_rotateLeftEdge
        (hrs u (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu)))
        (ne_of_lt (hp_gt u hu))
    obtain ⟨restOps, hrest_val, hrest_fold, hrest_cost, hrest_pop⟩ :=
      ih hrest_sort' cur' hcur'_bst hcur'_ever hrs'
    have hproj_step := projL_rotateLeftEdge asn.Lm hcur hpx hp_rs hx_rs
    by_cases hxL : x ≤ asn.Lm
    · simp only [hxL, ↓reduceIte] at hproj_step
      have hpL : p ≤ asn.Lm := le_trans (le_of_lt hpx) hxL
      have hx_VL : x ∈ asn.VL :=
        Finset.mem_filter.mpr ⟨hcur_ever x (mem_rightSpine hx_rs), hxL⟩
      have hp_VL : p ∈ asn.VL :=
        Finset.mem_filter.mpr ⟨hcur_ever p (mem_rightSpine hp_rs), hpL⟩
      have hmono : ∀ a ∈ (asn.VL : Set ℝ), ∀ b ∈ (asn.VL : Set ℝ), a < b → rankVL asn a < rankVL asn b :=
        fun a ha b hb hab => rankVL_lt_of_lt asn ha hb hab
      have hproj_S : ∀ u ∈ projL asn.Lm cur, u ∈ (asn.VL : Set ℝ) := by
        intro u hu
        obtain ⟨hu_cur, huL⟩ := (mem_projL_iff asn.Lm hcur u).mp hu
        exact Finset.mem_filter.mpr ⟨hcur_ever u hu_cur, huL⟩
      have hU_bst : ((projL asn.Lm cur).map (rankVL asn)).IsBST :=
        isBST_map_of_strictMonoOn hmono (isBST_projL asn.Lm hcur) hproj_S
      have hwp_rs : rankVL asn p ∈ rightSpine ((projL asn.Lm cur).map (rankVL asn)) := by
        rw [rightSpine_map]
        exact List.mem_map_of_mem (mem_rightSpine_projL_of_le asn.Lm hcur hp_rs hpL)
      obtain ⟨_, h1_val, h1_fold, h1_cost, h1_pop⟩ :=
        rotLeftSpineOps_sim (popCount ops) C (rankVL asn x) (rankVL asn p) hU_bst hwp_rs
      have hmap_rot :
          rotateLeftEdge ((projL asn.Lm cur).map (rankVL asn)) (rankVL asn x) (rankVL asn p) =
            (projL asn.Lm cur').map (rankVL asn) := by
        rw [rotateLeftEdge_map_of_strictMonoOn hmono hproj_S hx_VL hp_VL, ← hproj_step]
      rw [hmap_rot] at h1_fold
      refine ⟨rotLeftSpineOps ((projL asn.Lm cur).map (rankVL asn)) (rankVL asn x) (rankVL asn p) ++ restOps,
        ?_, ?_, ?_, ?_⟩
      · rw [validOneSidedOps_append, h1_fold]
        exact ⟨h1_val, hrest_val⟩
      · rw [List.foldl_append, h1_fold]
        exact hrest_fold
      · rw [oneSidedCascadeCost_append, h1_cost, h1_fold, zero_add]
        exact hrest_cost
      · rw [List.filterMap_append, h1_pop, List.nil_append]
        exact hrest_pop
    · simp only [hxL, ↓reduceIte] at hproj_step
      change projL asn.Lm cur' = projL asn.Lm cur at hproj_step
      rw [hproj_step] at hrest_val hrest_fold hrest_cost
      exact ⟨restOps, hrest_val, hrest_fold, hrest_cost, hrest_pop⟩

abbrev Ty_lem_3_2 : Prop :=
  ∀ {α : Type} [LinearOrder α] (t : BinaryTree α), t.IsBST → t ≠ .nil →
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
       SplayTree.eject t = ejectCascade t)

theorem sim_single_step
    (h_3_2 : Ty_lem_3_2)
    {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (i : Fin m) :
    ∃ stepOps : List OneSidedOp,
      ValidOneSidedOps (popCount ops) (simTreeAt asn i.castSucc) stepOps ∧
      stepOps.foldl OneSidedOp.step (simTreeAt asn i.castSucc) = simTreeAt asn i.succ ∧
      oneSidedCascadeCost (simTreeAt asn i.castSucc) stepOps =
        (open Classical in
          if (asn.opsR i).isPop then
            ((popCascadePairs (asn.treeAt i.castSucc)).filter
              (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)).length
          else 0) ∧
      stepOps.filterMap (fun | .pop s => some s | _ => none) =
        (match (if (asn.opsR i).isPop then (dequeSeq asn.T0 asn.opsR i.castSucc).minKey? else none) with
         | some q => [rankVL asn q]
         | none => []) := by
  have htree_step : asn.treeAt i.succ = (asn.opsR i).step (asn.treeAt i.castSucc) :=
    dequeSeq_succ asn.T0 asn.opsR i
  have hT_bst : (asn.treeAt i.castSucc).IsBST := asn.hBST i.castSucc
  have hT'_bst : (asn.treeAt i.succ).IsBST := asn.hBST i.succ
  have hvalR : (asn.opsR i).Valid (asn.treeAt i.castSucc) := asn.hValidR i
  have htail_step :
      tailInjectKeysR asn i.val =
        match injectVLKey? asn i with
        | some z => z :: tailInjectKeysR asn (i.val + 1)
        | none => tailInjectKeysR asn (i.val + 1) := by
    unfold tailInjectKeysR
    rw [drop_finRange_cons i.isLt, List.filterMap_cons]
    simp only [Fin.eta]
    cases injectVLKey? asn i <;> rfl
  rcases hop : asn.opsR i with _ | y | _ | z
  · -- Case `.pop`
    rw [hop] at hvalR htree_step
    have hinj_none : injectVLKey? asn i = none := by simp [injectVLKey?, hop]
    have htail_eq : tailRanks asn i.val = tailRanks asn i.succ.val := by
      unfold tailRanks
      rw [htail_step, hinj_none]
      rfl
    let C := rightChain (tailRanks asn i.val)
    obtain ⟨q, hmin⟩ := exists_minKey_of_ne_nil hvalR
    have hmin' : (dequeSeq asn.T0 asn.opsR i.castSucc).minKey? = some q := hmin
    have hq_pKeys : q ∈ popDeletedKeys asn.T0 asn.opsR := by
      simp only [popDeletedKeys, List.mem_filterMap, List.mem_finRange, true_and]
      exact ⟨i, by simp [hop, DequeOp.isPop, hmin']⟩
    have hq_VL : q ∈ asn.VL := (mem_VL_iff_mem_pKeys asn q).mpr hq_pKeys
    have hqL : q ≤ asn.Lm := by
      unfold ThreeWayKeyAssignment.VL at hq_VL
      exact (Finset.mem_filter.mp hq_VL).2
    have hq_memU : q ∈ asn.U i.castSucc :=
      (mem_projL_iff asn.Lm hT_bst q).mpr ⟨mem_of_minKey hmin, hqL⟩
    have hU_ne : asn.U i.castSucc ≠ .nil := BinaryTree.ne_nil_of_mem q hq_memU
    have hsimU_ne : simU asn i.castSucc ≠ .nil := mt (map_eq_nil_iff _ _).mp hU_ne
    have hU_min : (asn.U i.castSucc).minKey? = some q := by
      obtain ⟨mU, hmU⟩ := exists_minKey_of_ne_nil hU_ne
      have hmU_mem : mU ∈ asn.U i.castSucc := mem_of_minKey hmU
      have hmU_T : mU ∈ asn.treeAt i.castSucc := (mem_projL_iff asn.Lm hT_bst mU).mp hmU_mem |>.1
      have hq_le_mU : q ≤ mU := minKey_le_of_mem hT_bst hmin hmU_T
      have hmU_le_q : mU ≤ q := minKey_le_of_mem (isBST_projL asn.Lm hT_bst) hmU hq_memU
      rw [le_antisymm hmU_le_q hq_le_mU] at hmU
      exact hmU
    have hsim_min : (simTreeAt asn i.castSucc).minKey? = some (rankVL asn q) := by
      unfold simTreeAt
      simp only [Fin.val_castSucc]
      rw [minKey_rightSpineConcat_of_ne_nil C hsimU_ne, simU, minKey_map, hU_min]
      rfl
    have hsim_ne : simTreeAt asn i.castSucc ≠ .nil := by
      intro hnil
      rw [hnil] at hsim_min
      simp [BinaryTree.minKey?] at hsim_min
    have hpop_eq : SplayTree.pop (asn.treeAt i.castSucc) = popCascade (asn.treeAt i.castSucc) :=
      (h_3_2 (asn.treeAt i.castSucc) hT_bst hvalR).1.2.2.2.2
    have hls_T_sort : ((leftSpine (asn.treeAt i.castSucc)).tail).Pairwise (· < ·) :=
      (pairwise_leftSpine hT_bst).tail
    have hls_U_tail :
        (open Classical in
          ((leftSpine (asn.treeAt i.castSucc)).tail).filter (fun x => decide (x ≤ asn.Lm))) =
        (leftSpine (asn.U i.castSucc)).tail := by
      open Classical in
      unfold ThreeWayKeyAssignment.U
      rw [leftSpine_projL asn.Lm hT_bst]
      cases hlsT : leftSpine (asn.treeAt i.castSucc) with
      | nil => simp
      | cons v0 rest =>
        have hv0_mem : v0 ∈ asn.treeAt i.castSucc :=
          mem_leftSpine (by rw [hlsT]; exact List.mem_cons_self)
        have hls_sort_full := pairwise_leftSpine hT_bst
        rw [hlsT] at hls_sort_full
        have hv0_le_q : v0 ≤ q := by
          have hhead_ls : ∀ t : BinaryTree ℝ, (leftSpine t).head? = t.minKey? := by
            intro t
            induction t with
            | nil => rfl
            | node k l r ihl _ =>
              simp only [leftSpine, BinaryTree.minKey?]
              cases hll : leftSpine l with
              | nil =>
                rw [hll] at ihl
                simp only [List.head?_nil] at ihl
                rw [← ihl]; rfl
              | cons a as =>
                rw [hll] at ihl
                simp only [List.head?_cons] at ihl
                rw [← ihl]; rfl
          have hv0_eq := hhead_ls (asn.treeAt i.castSucc)
          rw [hlsT, hmin] at hv0_eq
          simp only [List.head?_cons, Option.some.injEq] at hv0_eq
          exact le_of_eq hv0_eq
        have hv0L : v0 ≤ asn.Lm := le_trans hv0_le_q hqL
        simp [hv0L]
    obtain ⟨hadj_eq, hproj_fold⟩ :=
      adjacentPairs_filter_le_and_projL asn.Lm ((leftSpine (asn.treeAt i.castSucc)).tail)
        hls_T_sort (spliceMin (asn.treeAt i.castSucc)) (isBST_spliceMin hT_bst)
    have hU_succ : asn.U i.succ = popCascade (asn.U i.castSucc) := by
      unfold ThreeWayKeyAssignment.U
      rw [htree_step, DequeOp.step, hpop_eq]
      unfold popCascade popCascadePairs
      change projL asn.Lm _ = _
      rw [hproj_fold, hls_U_tail, projL_spliceMin asn.Lm hT_bst hmin hqL]
      rfl
    have hmono : ∀ a ∈ (asn.VL : Set ℝ), ∀ b ∈ (asn.VL : Set ℝ), a < b → rankVL asn a < rankVL asn b :=
      fun a ha b hb hab => rankVL_lt_of_lt asn ha hb hab
    have hU_S : ∀ u ∈ asn.U i.castSucc, u ∈ (asn.VL : Set ℝ) :=
      fun u hu => mem_VL_of_mem_U asn i.castSucc hu
    have hsimU_bst := (simTreeAt_props asn i.castSucc).1
    refine ⟨[.pop (rankVL asn q)], ?_, ?_, ?_, ?_⟩
    · exact ⟨⟨hsim_ne, hsim_min⟩, trivial⟩
    · simp only [List.foldl_cons, List.foldl_nil, OneSidedOp.step]
      unfold simTreeAt
      simp only [Fin.val_castSucc]
      rw [popCascade_rightSpineConcat_of_ne_nil C hsimU_bst hsimU_ne]
      unfold simU
      dsimp only [C]
      rw [popCascade_map_of_strictMonoOn hmono hU_S, ← hU_succ, htail_eq]
    · simp only [oneSidedCascadeCost, OneSidedOp.cascadeRots, Nat.add_zero, DequeOp.isPop, ↓reduceIte]
      have hcp_concat : popCascadePairs (simTreeAt asn i.castSucc) = popCascadePairs (simU asn i.castSucc) := by
        unfold simTreeAt popCascadePairs
        simp only [Fin.val_castSucc]
        rw [leftSpine_rightSpineConcat_of_ne_nil C hsimU_ne]
      rw [hcp_concat, simU, popCascadePairs_map, List.length_map]
      open Classical in
      have hcp_U : popCascadePairs (asn.U i.castSucc) =
          (popCascadePairs (asn.treeAt i.castSucc)).filter (fun p => decide (p.1 ≤ asn.Lm ∧ p.2 ≤ asn.Lm)) := by
        unfold popCascadePairs
        rw [← hls_U_tail]
        exact hadj_eq
      rw [hcp_U]
      congr 1
      apply List.filter_congr
      intro p hp
      obtain ⟨hp1, hp2⟩ := mem_of_mem_adjacentPairs hp
      have hp1_ever : p.1 ∈ asn.everPresentKeys :=
        asn.hActiveSub i.castSucc ((mem_keyFinset_iff _ p.1).mpr (mem_leftSpine (List.mem_of_mem_tail hp1)))
      have hp2_ever : p.2 ∈ asn.everPresentKeys :=
        asn.hActiveSub i.castSucc ((mem_keyFinset_iff _ p.2).mpr (mem_leftSpine (List.mem_of_mem_tail hp2)))
      simp [ThreeWayKeyAssignment.VL, Finset.mem_filter, hp1_ever, hp2_ever]
    · simp [DequeOp.isPop, hmin']
  · -- Case `.push y`
    rw [hop] at hvalR htree_step
    have hinj_none : injectVLKey? asn i = none := by simp [injectVLKey?, hop]
    have htail_eq : tailRanks asn i.val = tailRanks asn i.succ.val := by
      unfold tailRanks
      rw [htail_step, hinj_none]
      rfl
    by_cases hyL : y ≤ asn.Lm
    · have hy_succ : y ∈ asn.treeAt i.succ := by
        rw [htree_step]; exact .here
      have hy_VL : y ∈ asn.VL := by
        open Classical in
        exact Finset.mem_filter.mpr
          ⟨asn.hActiveSub i.succ ((mem_keyFinset_iff _ y).mpr hy_succ), hyL⟩
      obtain ⟨hy1, hy2⟩ := rankVL_bounds asn hy_VL
      have hbst_push : (BinaryTree.node y .nil (asn.treeAt i.castSucc)).IsBST := by
        have h := htree_step ▸ hT'_bst
        simpa [DequeOp.step, SplayTree.push] using h
      have hU_succ : asn.U i.succ = .node y .nil (asn.U i.castSucc) := by
        unfold ThreeWayKeyAssignment.U
        rw [htree_step]
        exact projL_node_le asn.Lm y .nil (asn.treeAt i.castSucc) hbst_push hyL
      have hy_U_succ : y ∈ asn.U i.succ := by rw [hU_succ]; exact .here
      refine ⟨[.push (rankVL asn y)], ?_, ?_, ?_, ?_⟩
      · refine ⟨⟨hy1, hy2, ?_⟩, trivial⟩
        intro k hk
        rw [simTreeAt, mem_rightSpineConcat_iff] at hk
        rcases hk with hkU | hkC
        · obtain ⟨uR, huR, rfl⟩ := (mem_map_iff _ _ _).mp hkU
          have hu_T : uR ∈ asn.treeAt i.castSucc := (mem_projL_iff asn.Lm hT_bst uR).mp huR |>.1
          exact rankVL_lt_of_lt asn hy_VL (mem_VL_of_mem_U asn i.castSucc huR) (hvalR uR hu_T)
        · rw [mem_rightChain_iff, tailRanks, List.mem_map] at hkC
          obtain ⟨zR, hzR, rfl⟩ := hkC
          have hzR_succ : zR ∈ tailInjectKeysR asn (i.val + 1) := by
            simp only [Fin.val_castSucc] at hzR
            rw [htail_step, hinj_none] at hzR
            exact hzR
          obtain ⟨hz_VL, j, hij, hop_j, hzL⟩ := mem_tailInjectKeysR_props asn hzR_succ
          exact rankVL_lt_of_lt asn hy_VL hz_VL
            (lt_of_mem_U_before_inject asn j zR hop_j hzL i.succ hij y hy_U_succ)
      · unfold simTreeAt simU
        simp only [List.foldl_cons, List.foldl_nil, OneSidedOp.step, SplayTree.push,
          Fin.val_castSucc, hU_succ, htail_eq]
        rfl
      · simp [oneSidedCascadeCost, OneSidedOp.cascadeRots, DequeOp.isPop]
      · simp [DequeOp.isPop]
    · have hy_gt : asn.Lm < y := lt_of_not_ge hyL
      have hbst_push : (BinaryTree.node y .nil (asn.treeAt i.castSucc)).IsBST := by
        have h := htree_step ▸ hT'_bst
        simpa [DequeOp.step, SplayTree.push] using h
      have hU_succ_nil : asn.U i.succ = .nil := by
        unfold ThreeWayKeyAssignment.U
        rw [htree_step]
        exact projL_node_gt asn.Lm y .nil (asn.treeAt i.castSucc) hbst_push hy_gt
      have hU_prev_nil : asn.U i.castSucc = .nil := by
        apply BinaryTree.eq_nil_of_toKeyList_eq_nil
        cases hkl : (asn.U i.castSucc).toKeyList with
        | nil => rfl
        | cons u us =>
          exfalso
          have hu_U : u ∈ asn.U i.castSucc :=
            BinaryTree.mem_iff_mem_toKeyList.mpr (by rw [hkl]; exact List.mem_cons_self)
          obtain ⟨hu_T, huL⟩ := (mem_projL_iff asn.Lm hT_bst u).mp hu_U
          exact absurd huL (not_le.mpr (lt_trans hy_gt (hvalR u hu_T)))
      refine ⟨[], trivial, ?_, ?_, ?_⟩
      · simp [simTreeAt, simU, hU_succ_nil, hU_prev_nil, htail_eq]
      · simp [oneSidedCascadeCost, DequeOp.isPop]
      · simp [DequeOp.isPop]
  · -- Case `.eject`
    rw [hop] at hvalR htree_step
    have hinj_none : injectVLKey? asn i = none := by simp [injectVLKey?, hop]
    have htail_eq : tailRanks asn i.val = tailRanks asn i.succ.val := by
      unfold tailRanks
      rw [htail_step, hinj_none]
      rfl
    let T := asn.treeAt i.castSucc
    let C := rightChain (tailRanks asn i.val)
    obtain ⟨q, hmax⟩ := exists_maxKey_of_ne_nil hvalR
    have hmax' : (dequeSeq asn.T0 asn.opsR i.castSucc).maxKey? = some q := hmax
    have hq_eKeys : q ∈ ejectDeletedKeys asn.T0 asn.opsR := by
      simp only [ejectDeletedKeys, List.mem_filterMap, List.mem_finRange, true_and]
      exact ⟨i, by simp [hop, DequeOp.isEject, hmax']⟩
    have hq_VR : asn.Rm ≤ q := by
      open Classical in
      have hmem : q ∈ (ejectDeletedKeys asn.T0 asn.opsR).toFinset := List.mem_toFinset.mpr hq_eKeys
      rw [asn.hEjectOrder.2.2] at hmem
      exact (Finset.mem_filter.mp hmem).2
    have hLm_lt_q : asn.Lm < q := lt_of_lt_of_le asn.hLmRm hq_VR
    have hsp_proj : projL asn.Lm (spliceMax T) = asn.U i.castSucc :=
      projL_spliceMax_of_gt asn.Lm hT_bst hmax hLm_lt_q
    have hej_eq : SplayTree.eject T = ejectCascade T :=
      (h_3_2 T hT_bst hvalR).2.2.2.2.2
    have heb_sort : ((rightSpineBottomUp T).tail).Pairwise (· > ·) :=
      (List.Pairwise.reverse (pairwise_rightSpine hT_bst)).tail
    have hsp_ever : ∀ u ∈ spliceMax T, u ∈ asn.everPresentKeys := by
      intro u hu
      open Classical in
      apply asn.hActiveSub i.castSucc
      rw [mem_keyFinset_iff, BinaryTree.mem_iff_mem_toKeyList]
      exact toKeyList_spliceMax_sub T u (BinaryTree.mem_iff_mem_toKeyList.mp hu)
    have heb_rs : ∀ u ∈ (rightSpineBottomUp T).tail, u ∈ rightSpine (spliceMax T) :=
      fun u hu => mem_rightSpine_spliceMax_of_mem_tail T hu
    obtain ⟨ejOps, hej_val, hej_fold, hej_cost, hej_pop⟩ :=
      eject_fold_sim asn C ((rightSpineBottomUp T).tail) heb_sort
        (spliceMax T) (isBST_spliceMax hT_bst) hsp_ever heb_rs
    rw [hsp_proj] at hej_val hej_fold hej_cost
    have hU_succ :
        projL asn.Lm ((adjacentPairs (rightSpineBottomUp T).tail).foldl
          (fun acc p => rotateLeftEdge acc p.1 p.2) (spliceMax T)) = asn.U i.succ := by
      unfold ThreeWayKeyAssignment.U
      rw [htree_step, DequeOp.step, hej_eq]
      rfl
    rw [hU_succ] at hej_fold
    refine ⟨ejOps, hej_val, ?_, ?_, ?_⟩
    · simpa [simTreeAt, simU, C, htail_eq] using hej_fold
    · simpa [simTreeAt, simU, C, DequeOp.isPop] using hej_cost
    · simpa [DequeOp.isPop] using hej_pop
  · -- Case `.inject z`
    rw [hop] at hvalR htree_step
    by_cases hzL : z ≤ asn.Lm
    · have hinj_some : injectVLKey? asn i = some z := by simp [injectVLKey?, hop, hzL]
      have htail_cons : tailRanks asn i.val = rankVL asn z :: tailRanks asn i.succ.val := by
        unfold tailRanks
        rw [htail_step, hinj_some, List.map_cons]
        rfl
      have hT_all_le : ∀ u ∈ asn.treeAt i.castSucc, u ≤ asn.Lm :=
        fun u hu => le_trans (le_of_lt (hvalR u hu)) hzL
      have hU_prev_eq : restrictTree (asn.treeAt i.castSucc) {x | x ≤ asn.Lm} = asn.treeAt i.castSucc :=
        restrictTree_eq_self_of_forall _ _ hT_all_le
      have hbst_inj : (BinaryTree.node z (asn.treeAt i.castSucc) .nil).IsBST := by
        have h := htree_step ▸ hT'_bst
        simpa [DequeOp.step, SplayTree.inject] using h
      have hU_succ : asn.U i.succ = .node z (asn.U i.castSucc) .nil := by
        unfold ThreeWayKeyAssignment.U
        rw [htree_step, DequeOp.step, SplayTree.inject]
        change projL asn.Lm (.node z (asn.treeAt i.castSucc) .nil) = _
        rw [projL_node_le asn.Lm z (asn.treeAt i.castSucc) .nil hbst_inj hzL, projL_nil, hU_prev_eq]
      let C' := rightChain (tailRanks asn i.succ.val)
      obtain ⟨_, hp_val, hp_fold, hp_cost, hp_pop⟩ :=
        pullUpOps_sim (popCount ops) (rankVL asn z) C' (simU asn i.castSucc)
      have hsim_prev : simTreeAt asn i.castSucc =
          rightSpineConcat (simU asn i.castSucc) (.node (rankVL asn z) .nil C') := by
        simp [simTreeAt, htail_cons, rightChain, C']
      have hsim_succ : simTreeAt asn i.succ =
          .node (rankVL asn z) (simU asn i.castSucc) C' := by
        unfold simTreeAt simU
        rw [hU_succ]
        rfl
      refine ⟨pullUpOps (simU asn i.castSucc), ?_, ?_, ?_, ?_⟩
      · rwa [hsim_prev]
      · rw [hsim_prev, hp_fold, hsim_succ]
      · rw [hsim_prev, hp_cost]
        simp [DequeOp.isPop]
      · rw [hp_pop]
        simp [DequeOp.isPop]
    · have hinj_none : injectVLKey? asn i = none := by simp [injectVLKey?, hop, hzL]
      have htail_eq : tailRanks asn i.val = tailRanks asn i.succ.val := by
        unfold tailRanks
        rw [htail_step, hinj_none]
        rfl
      have hz_gt : asn.Lm < z := lt_of_not_ge hzL
      have hbst_inj : (BinaryTree.node z (asn.treeAt i.castSucc) .nil).IsBST := by
        have h := htree_step ▸ hT'_bst
        simpa [DequeOp.step, SplayTree.inject] using h
      have hU_succ : asn.U i.succ = asn.U i.castSucc := by
        unfold ThreeWayKeyAssignment.U
        rw [htree_step, DequeOp.step, SplayTree.inject]
        exact projL_node_gt asn.Lm z (asn.treeAt i.castSucc) .nil hbst_inj hz_gt
      refine ⟨[], trivial, ?_, ?_, ?_⟩
      · simp [simTreeAt, simU, hU_succ, htail_eq]
      · simp [oneSidedCascadeCost, DequeOp.isPop]
      · simp [DequeOp.isPop]

theorem sim_prefix_steps
    (h_3_2 : Ty_lem_3_2)
    {α : Type} [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) :
    ∀ (k : ℕ) (hk : k ≤ m),
      ∃ simSteps : List OneSidedOp,
        ValidOneSidedOps (popCount ops) (simTreeAt asn 0) simSteps ∧
        simSteps.foldl OneSidedOp.step (simTreeAt asn 0) = simTreeAt asn ⟨k, Nat.lt_succ_of_le hk⟩ ∧
        oneSidedCascadeCost (simTreeAt asn 0) simSteps =
          (open Classical in
            ∑ i ∈ Finset.univ.filter (fun j : Fin m => j.val < k),
              if (asn.opsR i).isPop then
                ((popCascadePairs (asn.treeAt i.castSucc)).filter
                  (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)).length
              else 0) ∧
        simSteps.filterMap (fun | .pop s => some s | _ => none) =
          (((List.finRange m).take k).filterMap (fun i =>
            if (asn.opsR i).isPop then (dequeSeq asn.T0 asn.opsR i.castSucc).minKey? else none)).map
            (rankVL asn) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨[], trivial, rfl, ?_, rfl⟩
    open Classical in
    have hemp : Finset.univ.filter (fun j : Fin m => j.val < 0) = ∅ := by ext j; simp
    rw [hemp]; rfl
  | succ k ih =>
    intro hk
    let ik : Fin m := ⟨k, hk⟩
    obtain ⟨preSteps, hpre_val, hpre_fold, hpre_cost, hpre_pop⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨stOps, hst_val, hst_fold, hst_cost, hst_pop⟩ := sim_single_step h_3_2 asn ik
    have hik_cs : (⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk)⟩ : Fin (m + 1)) = ik.castSucc := rfl
    have hik_su : (⟨k + 1, Nat.lt_succ_of_le hk⟩ : Fin (m + 1)) = ik.succ := rfl
    rw [hik_cs] at hpre_fold
    refine ⟨preSteps ++ stOps, ?_, ?_, ?_, ?_⟩
    · rw [validOneSidedOps_append, hpre_fold]
      exact ⟨hpre_val, hst_val⟩
    · rw [List.foldl_append, hpre_fold, hst_fold, hik_su]
    · rw [oneSidedCascadeCost_append, hpre_cost, hpre_fold, hst_cost]
      open Classical in
      have hset : Finset.univ.filter (fun j : Fin m => j.val < k + 1) =
          insert ik (Finset.univ.filter (fun j : Fin m => j.val < k)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hj
          by_cases hjk : j.val = k
          · exact Or.inl (Fin.ext hjk)
          · exact Or.inr (by omega)
        · rintro (rfl | hj)
          · dsimp [ik]; omega
          · omega
      have hnotmem : ik ∉ Finset.univ.filter (fun j : Fin m => j.val < k) := by simp [ik]
      rw [hset, Finset.sum_insert hnotmem, Nat.add_comm]
    · rw [List.filterMap_append, hpre_pop, hst_pop]
      have hlen : k < (List.finRange m).length := by
        rw [List.length_finRange]
        exact hk
      have htake : (List.finRange m).take (k + 1) = (List.finRange m).take k ++ [ik] := by
        rw [List.take_succ_eq_append_getElem hlen]
        simp [ik]
      rw [htake, List.filterMap_append, List.map_append]
      congr 1
      simp only [List.filterMap_cons, List.filterMap_nil]
      cases (if (asn.opsR ik).isPop then (dequeSeq asn.T0 asn.opsR ik.castSucc).minKey? else none) <;>
        rfl

theorem num_nodes_spliceMin_add_one {α : Type} :
    ∀ {t : BinaryTree α}, t ≠ .nil → (spliceMin t).num_nodes + 1 = t.num_nodes
  | .nil, hne => absurd rfl hne
  | .node k .nil r, _ => by
    show r.num_nodes + 1 = 1 + 0 + r.num_nodes
    omega
  | .node k (.node lk ll lr) r, _ => by
    have ih := num_nodes_spliceMin_add_one (t := BinaryTree.node lk ll lr) (by simp)
    show (1 + (spliceMin (.node lk ll lr)).num_nodes + r.num_nodes) + 1 =
      1 + (BinaryTree.node lk ll lr).num_nodes + r.num_nodes
    omega

theorem num_nodes_popCascade_add_one {α : Type} [LinearOrder α] {t : BinaryTree α} (hne : t ≠ .nil) :
    (popCascade t).num_nodes + 1 = t.num_nodes := by
  unfold popCascade
  have hfold : ∀ (ps : List (α × α)) (acc : BinaryTree α),
      (ps.foldl (fun s p => rotateRightEdge s p.1 p.2) acc).num_nodes = acc.num_nodes := by
    intro ps
    induction ps with
    | nil => intro acc; rfl
    | cons p rest ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih]
      rw [BinaryTree.num_nodes_eq_length_toKeyList, BinaryTree.num_nodes_eq_length_toKeyList,
        toKeyList_rotateRightEdge]
  rw [hfold, num_nodes_spliceMin_add_one hne]

theorem num_nodes_rotateLeftAtRightSpine1 :
    ∀ (t : BinaryTree ℕ) (d : ℕ), 1 ≤ d → d + 1 ≤ (rightSpine t).length →
      (rotateLeftAtRightSpine1 t d).num_nodes = t.num_nodes
  | _, 0, hd1, _ => absurd hd1 (by omega)
  | t, 1, _, _ => by simp [rotateLeftAtRightSpine1]
  | .nil, _ + 2, _, hd2 => by simp [rightSpine] at hd2
  | .node k l r, d + 2, _, hd2 => by
    simp only [rightSpine, List.length_cons] at hd2
    have ih := num_nodes_rotateLeftAtRightSpine1 r (d + 1) (by omega) (by omega)
    show 1 + l.num_nodes + (rotateLeftAtRightSpine1 r (d + 1)).num_nodes = 1 + l.num_nodes + r.num_nodes
    omega

theorem num_nodes_add_pushes_eq (P : ℕ) :
    ∀ (ops : List OneSidedOp) (t : BinaryTree ℕ),
      ValidOneSidedOps P t ops →
      t.num_nodes + (ops.filterMap (fun | .push w => some w | _ => none)).length =
        (ops.foldl OneSidedOp.step t).num_nodes +
          (ops.filterMap (fun | .pop s => some s | _ => none)).length
  | [], t, _ => by simp
  | op :: rest, t, ⟨hv1, hv_rest⟩ => by
    have ih := num_nodes_add_pushes_eq P rest (op.step t) hv_rest
    cases op with
    | push w =>
      have hstep : (OneSidedOp.step t (.push w)).num_nodes = t.num_nodes + 1 := by
        show 1 + 0 + t.num_nodes = t.num_nodes + 1
        omega
      simp only [List.filterMap_cons, List.length_cons, List.foldl_cons] at ih ⊢
      omega
    | pop s =>
      have hstep := num_nodes_popCascade_add_one hv1.1
      change (OneSidedOp.step t (.pop s)).num_nodes + 1 = t.num_nodes at hstep
      simp only [List.filterMap_cons, List.length_cons, List.foldl_cons] at ih ⊢
      omega
    | rightSpineLeftRot d =>
      have hstep := num_nodes_rotateLeftAtRightSpine1 t d hv1.1 hv1.2
      change (OneSidedOp.step t (.rightSpineLeftRot d)).num_nodes = t.num_nodes at hstep
      simp only [List.filterMap_cons, List.foldl_cons] at ih ⊢
      omega

theorem no_pops_of_filter_pop_zero :
    ∀ (ops : List OneSidedOp) (t : BinaryTree ℕ),
      (ops.filter (fun | .pop _ => true | _ => false)).length = 0 →
      ops.filterMap (fun | .pop s => some s | _ => none) = [] ∧
      oneSidedCascadeCost t ops = 0
  | [], _, _ => ⟨rfl, rfl⟩
  | op :: rest, t, h0 => by
    cases op with
    | push w =>
      simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte] at h0
      obtain ⟨ih1, ih2⟩ := no_pops_of_filter_pop_zero rest (OneSidedOp.step t (.push w)) h0
      exact ⟨ih1, by simpa [oneSidedCascadeCost, OneSidedOp.cascadeRots] using ih2⟩
    | pop s =>
      simp at h0
    | rightSpineLeftRot d =>
      simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte] at h0
      obtain ⟨ih1, ih2⟩ := no_pops_of_filter_pop_zero rest (OneSidedOp.step t (.rightSpineLeftRot d)) h0
      exact ⟨ih1, by simpa [oneSidedCascadeCost, OneSidedOp.cascadeRots] using ih2⟩

theorem filterMap_congr_all {α β : Type} :
    ∀ (xs : List α) (f g : α → Option β), (∀ x, f x = g x) → xs.filterMap f = xs.filterMap g
  | [], _, _, _ => rfl
  | x :: xs, f, g, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x, filterMap_congr_all xs f g h]

theorem lem_3_5_part2
    (h_3_2 : Ty_lem_3_2)
    (h_part1 : ∀ (P n₀ : ℕ) (H_init : BinaryTree ℕ),
      H_init.IsBST → H_init.num_nodes = n₀ → keyFinset H_init ⊆ Finset.Icc 1 P →
      ∃ initSteps : List OneSidedOp,
        ValidOneSidedOps P .nil initSteps ∧
        initSteps.foldl OneSidedOp.step .nil = H_init ∧
        (initSteps.filter (fun | .push _ => true | _ => false)).length = n₀ ∧
        (initSteps.filter (fun | .pop _ => true | _ => false)).length = 0 ∧
        (initSteps.filter (fun | .rightSpineLeftRot _ => true | _ => false)).length =
          n₀ - (rightSpine H_init).length ∧
        (∀ op ∈ initSteps, ∀ d : ℕ, op = .rightSpineLeftRot d → d = 1))
    (h_kL : ∀ (P : ℕ), 1 ≤ P → ∀ exec : OneSidedPopExec P, exec.kL ≤ 2 * P - 2) :
    ∀ {α : Type} [LinearOrder α] {m : ℕ} (init : BST α) (ops : Fin m → DequeOp α)
       (asn : ThreeWayKeyAssignment init ops),
      ValidDequeSeq init.tree ops → 1 ≤ popCount ops →
      ∃ HL : OneSidedPopExec (popCount ops),
        HL.cPop = asn.cPopU ∧ HL.kL ≤ 2 * popCount ops - 2 ∧ HL.kL < 2 * popCount ops := by
  intro α _ m init ops asn _ hP
  let P := popCount ops
  let H_init := simTreeAt asn 0
  obtain ⟨_, hInit_bst, hInit_keys⟩ := simTreeAt_props asn 0
  obtain ⟨initSteps, hInit_val, hInit_fold, _, hInit_pop0, _, _⟩ :=
    h_part1 P H_init.num_nodes H_init hInit_bst rfl hInit_keys
  have hInit_pop0' : (initSteps.filter (fun | .pop _ => true | _ => false)).length = 0 := by
    rw [← hInit_pop0]
    exact congrArg List.length (List.filter_congr fun x _ => by cases x <;> rfl)
  obtain ⟨hInit_pop_nil, hInit_cost0⟩ := no_pops_of_filter_pop_zero initSteps .nil hInit_pop0'
  obtain ⟨simSteps, hSim_val, hSim_fold, hSim_cost, hSim_pop⟩ :=
    sim_prefix_steps h_3_2 asn m le_rfl
  have hlast_eq : (⟨m, Nat.lt_succ_of_le le_rfl⟩ : Fin (m + 1)) = Fin.last m := rfl
  rw [hlast_eq, simTreeAt_last_eq_nil asn] at hSim_fold
  have hAll_val : ValidOneSidedOps P .nil (initSteps ++ simSteps) := by
    rw [validOneSidedOps_append, hInit_fold]
    exact ⟨hInit_val, hSim_val⟩
  have hAll_end : (initSteps ++ simSteps).foldl OneSidedOp.step .nil = .nil := by
    rw [List.foldl_append, hInit_fold, hSim_fold]
  have hAll_pop :
      ∀ f : OneSidedOp → Option ℕ,
        (∀ w, f (.push w) = none) → (∀ s, f (.pop s) = some s) →
        (∀ d, f (.rightSpineLeftRot d) = none) →
        (initSteps ++ simSteps).filterMap f = List.range' 1 P := by
    intro f hf1 hf2 hf3
    have h1 : initSteps.filterMap f = [] := by
      rw [← hInit_pop_nil]
      exact filterMap_congr_all initSteps f _ (fun x => by cases x <;> simp [hf1, hf2, hf3])
    have h2 : simSteps.filterMap f =
        (((List.finRange m).take m).filterMap (fun i =>
          if (asn.opsR i).isPop then (dequeSeq asn.T0 asn.opsR i.castSucc).minKey? else none)).map
          (rankVL asn) := by
      rw [← hSim_pop]
      exact filterMap_congr_all simSteps f _ (fun x => by cases x <;> simp [hf1, hf2, hf3])
    rw [List.filterMap_append, h1, List.nil_append, h2]
    have htake_all : (List.finRange m).take m = List.finRange m :=
      List.take_of_length_le (by simp)
    rw [htake_all]
    change (popDeletedKeys asn.T0 asn.opsR).map (rankVL asn) = List.range' 1 P
    open Classical in
    have hnd : (popDeletedKeys asn.T0 asn.opsR).Nodup :=
      asn.hPopOrder.1.imp (fun hab => ne_of_lt hab)
    have hrange := map_listPos_add (popDeletedKeys asn.T0 asn.opsR) 1 hnd
    rw [asn.hPopOrder.2.1] at hrange
    exact hrange
  have hAll_push :
      ∀ g : OneSidedOp → Option ℕ,
        (∀ w, g (.push w) = some w) → (∀ s, g (.pop s) = none) →
        (∀ d, g (.rightSpineLeftRot d) = none) →
        ((initSteps ++ simSteps).filterMap g).length = P := by
    intro g hg1 hg2 hg3
    have hcons := num_nodes_add_pushes_eq P (initSteps ++ simSteps) .nil hAll_val
    rw [hAll_end] at hcons
    have hnil0 : (BinaryTree.nil : BinaryTree ℕ).num_nodes = 0 := rfl
    rw [hnil0, zero_add, zero_add] at hcons
    refine Eq.trans ?_ (Eq.trans hcons ?_)
    · exact congrArg List.length
        (filterMap_congr_all _ g _ (fun x => by cases x <;> simp [hg1, hg2, hg3]))
    · rw [hAll_pop _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), List.length_range']
  let HL : OneSidedPopExec P := {
    steps := initSteps ++ simSteps
    hValid := hAll_val
    hEndEmpty := hAll_end
    hPushCount := hAll_push _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    hPopSeq := hAll_pop _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  }
  have hcPop : HL.cPop = asn.cPopU := by
    unfold OneSidedPopExec.cPop
    change oneSidedCascadeCost .nil (initSteps ++ simSteps) = asn.cPopU
    rw [oneSidedCascadeCost_append, hInit_cost0, zero_add, hInit_fold, hSim_cost]
    open Classical in
    have huniv : Finset.univ.filter (fun j : Fin m => j.val < m) = Finset.univ := by
      ext j; simp
    rw [huniv]
    rfl
  have hkL_le : HL.kL ≤ 2 * P - 2 := h_kL P hP HL
  exact ⟨HL, hcPop, hkL_le, by omega⟩

/-! ## Section 4: Order-Dual Mirror Symmetry and `thm_2_2_mod1_reduction` -/

def flipTree {β γ : Type} (neg : β → γ) : BinaryTree β → BinaryTree γ
  | .nil => .nil
  | .node k l r => .node (neg k) (flipTree neg r) (flipTree neg l)

def flipFrame {β γ : Type} (neg : β → γ) (f : Frame β) : Frame γ :=
  { dir := f.dir.flip, key := neg f.key, sibling := flipTree neg f.sibling }

def flipOp {β γ : Type} (neg : β → γ) : DequeOp β → DequeOp γ
  | .pop => .eject
  | .push x => .inject (neg x)
  | .eject => .pop
  | .inject x => .push (neg x)

theorem antiMono_props {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x) :
    Function.Injective neg ∧
    (∀ x y : β, neg x = neg y ↔ x = y) ∧
    (∀ x y : β, neg x ≤ neg y ↔ y ≤ x) := by
  have hinj : Function.Injective neg := by
    intro x y hxy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact absurd ((hanti y x).mpr hlt) (by rw [hxy]; exact lt_irrefl _)
    · exact heq
    · exact absurd ((hanti x y).mpr hgt) (by rw [hxy]; exact lt_irrefl _)
  refine ⟨hinj, fun x y => hinj.eq_iff, fun x y => ?_⟩
  rw [← not_lt, hanti, not_lt]

theorem flipTree_eq_nil_iff {β γ : Type} (neg : β → γ) (t : BinaryTree β) :
    flipTree neg t = .nil ↔ t = .nil := by
  cases t <;> simp [flipTree]

theorem num_nodes_flipTree {β γ : Type} (neg : β → γ) (t : BinaryTree β) :
    (flipTree neg t).num_nodes = t.num_nodes := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    show 1 + (flipTree neg r).num_nodes + (flipTree neg l).num_nodes = 1 + l.num_nodes + r.num_nodes
    omega

theorem toKeyList_flipTree {β γ : Type} (neg : β → γ) (t : BinaryTree β) :
    (flipTree neg t).toKeyList = (t.toKeyList.map neg).reverse := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp [flipTree, BinaryTree.toKeyList_node, ihl, ihr, List.map_append,
      List.reverse_append, List.append_assoc]

theorem mem_flipTree_iff {β γ : Type} (neg : β → γ) (t : BinaryTree β) (y : γ) :
    y ∈ flipTree neg t ↔ ∃ x ∈ t, neg x = y := by
  rw [BinaryTree.mem_iff_mem_toKeyList, toKeyList_flipTree, List.mem_reverse, List.mem_map]
  simp [BinaryTree.mem_iff_mem_toKeyList]

theorem keyFinset_flipTree {β γ : Type} [DecidableEq β] [DecidableEq γ]
    (neg : β → γ) (t : BinaryTree β) :
    keyFinset (flipTree neg t) = (keyFinset t).image neg := by
  ext y
  simp [mem_keyFinset_iff, mem_flipTree_iff]

theorem isBST_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    {t : BinaryTree β} (ht : t.IsBST) :
    (flipTree neg t).IsBST := by
  rw [SplayTree.IsBST_iff_toKeyList_sorted, toKeyList_flipTree, List.pairwise_reverse]
  have hsort := (SplayTree.IsBST_iff_toKeyList_sorted t).mp ht
  clear ht
  generalize t.toKeyList = kl at hsort
  induction kl with
  | nil => simp
  | cons a as ih =>
    obtain ⟨ha_lt, has_sort⟩ := List.pairwise_cons.mp hsort
    simp only [List.map_cons, List.pairwise_cons, List.mem_map]
    refine ⟨?_, ih has_sort⟩
    rintro _ ⟨b, hb, rfl⟩
    exact (hanti b a).mpr (ha_lt b hb)

theorem minKey_flipTree {β γ : Type} (neg : β → γ) :
    ∀ t : BinaryTree β, (flipTree neg t).minKey? = t.maxKey?.map neg
  | .nil => rfl
  | .node k l r => by
    simp only [flipTree, BinaryTree.minKey?, BinaryTree.maxKey?, minKey_flipTree neg r]
    cases r.maxKey? <;> rfl

theorem maxKey_flipTree {β γ : Type} (neg : β → γ) :
    ∀ t : BinaryTree β, (flipTree neg t).maxKey? = t.minKey?.map neg
  | .nil => rfl
  | .node k l r => by
    simp only [flipTree, BinaryTree.maxKey?, BinaryTree.minKey?, maxKey_flipTree neg l]
    cases l.minKey? <;> rfl

theorem map_unit_flipTree {β γ : Type} (neg : β → γ) :
    ∀ t : BinaryTree β, (flipTree neg t).map (fun _ => ()) = (t.map (fun _ => ())).mirror
  | .nil => rfl
  | .node k l r => by
    show BinaryTree.node () ((flipTree neg r).map (fun _ => ())) ((flipTree neg l).map (fun _ => ())) =
      BinaryTree.node () ((r.map (fun _ => ())).mirror) ((l.map (fun _ => ())).mirror)
    rw [map_unit_flipTree neg r, map_unit_flipTree neg l]

theorem leftSpine_flipTree {β γ : Type} (neg : β → γ) :
    ∀ t : BinaryTree β, leftSpine (flipTree neg t) = (rightSpineBottomUp t).map neg
  | .nil => rfl
  | .node k l r => by
    unfold rightSpineBottomUp
    show leftSpine (flipTree neg r) ++ [neg k] = ((k :: rightSpine r).reverse).map neg
    rw [List.reverse_cons, List.map_append]
    change leftSpine (flipTree neg r) ++ [neg k] = (rightSpineBottomUp r).map neg ++ [neg k]
    rw [leftSpine_flipTree neg r]

theorem popCascadePairs_flipTree {β γ : Type} (neg : β → γ) (t : BinaryTree β) :
    popCascadePairs (flipTree neg t) = (ejectCascadePairs t).map (fun p => (neg p.1, neg p.2)) := by
  unfold popCascadePairs ejectCascadePairs
  rw [leftSpine_flipTree, tail_map, adjacentPairs_map]

theorem flipTree_right {β γ : Type} (neg : β → γ) (t : BinaryTree β) :
    (flipTree neg t).right = flipTree neg t.left := by
  cases t <;> rfl

theorem flipTree_left {β γ : Type} (neg : β → γ) (t : BinaryTree β) :
    (flipTree neg t).left = flipTree neg t.right := by
  cases t <;> rfl

theorem flipTree_bringUp {β γ : Type} (neg : β → γ) (d : Dir) (t : BinaryTree β) :
    flipTree neg (d.bringUp t) = d.flip.bringUp (flipTree neg t) := by
  cases d <;> rcases t with _ | ⟨k, _ | ⟨lk, ll, lr⟩, _ | ⟨rk, rl, rr⟩⟩ <;> rfl

theorem flipTree_attach {β γ : Type} (neg : β → γ) (c : BinaryTree β) (f : Frame β) :
    flipTree neg (f.attach c) = (flipFrame neg f).attach (flipTree neg c) := by
  cases f with
  | mk d k s => cases d <;> rfl

theorem flipTree_applyChild_bringUp {β γ : Type} (neg : β → γ)
    (d₁ d₂ : Dir) (t : BinaryTree β) :
    flipTree neg (applyChild d₁ d₂.bringUp t) =
      applyChild d₁.flip d₂.flip.bringUp (flipTree neg t) := by
  rcases t with _ | ⟨k, l, r⟩
  · cases d₁ <;> rfl
  · cases d₁ <;> simp [applyChild, Dir.flip, flipTree, flipTree_bringUp]

theorem flipFrame_dir {β γ : Type} (neg : β → γ) (f : Frame β) :
    (flipFrame neg f).dir = f.dir.flip := by
  cases f; rfl

theorem flipTree_splayUp {β γ : Type} (neg : β → γ) (c : BinaryTree β) (path : List (Frame β)) :
    flipTree neg (splayUp c path) = splayUp (flipTree neg c) (path.map (flipFrame neg)) := by
  induction c, path using splayUp_induction with
  | nil c => rfl
  | single c f =>
    simp [splayUp, flipTree_attach, flipTree_bringUp, flipFrame_dir]
  | step c f1 f2 rest ih =>
    have hdir : ((flipFrame neg f1).dir = (flipFrame neg f2).dir) ↔ (f1.dir = f2.dir) := by
      rw [flipFrame_dir, flipFrame_dir]
      cases f1.dir <;> cases f2.dir <;> decide
    simp only [List.map_cons, splayUp, hdir]
    split_ifs with h
    · rw [ih, flipTree_bringUp, flipTree_bringUp, flipTree_attach, flipTree_attach, flipFrame_dir]
    · rw [ih, flipTree_bringUp, flipTree_applyChild_bringUp, flipTree_attach, flipTree_attach,
        flipFrame_dir, flipFrame_dir]

theorem descend_go_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    (q : β) (t : BinaryTree β) (acc : List (Frame β)) :
    descend.go (neg q) (flipTree neg t) (acc.map (flipFrame neg)) =
      (flipTree neg (descend.go q t acc).1, (descend.go q t acc).2.map (flipFrame neg)) := by
  have heq_iff := (antiMono_props hanti).2.1
  induction t generalizing acc with
  | nil => rfl
  | node k l r ihl ihr =>
    unfold descend.go
    simp only [flipTree, heq_iff q k, hanti q k]
    by_cases hqk : q = k
    · simp only [hqk, ↓reduceIte]
      rfl
    · simp only [hqk, ↓reduceIte]
      by_cases hlt : q < k
      · have hnot_gt : ¬ (k < q) := not_lt.mpr (le_of_lt hlt)
        simp only [hlt, hnot_gt, ↓reduceIte]
        exact ihl ({ dir := .L, key := k, sibling := r } :: acc)
      · have hgt : k < q := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hqk)
        simp only [hlt, hgt, ↓reduceIte]
        exact ihr ({ dir := .R, key := k, sibling := l } :: acc)

theorem descend_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    (t : BinaryTree β) (q : β) :
    descend (flipTree neg t) (neg q) =
      (flipTree neg (descend t q).1, (descend t q).2.map (flipFrame neg)) :=
  descend_go_flipTree hanti q t []

theorem splay_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    (t : BinaryTree β) (q : β) :
    splay (flipTree neg t) (neg q) = flipTree neg (splay t q) := by
  unfold splay
  rw [descend_flipTree hanti t q]
  rcases h : descend t q with ⟨c, path⟩
  cases c with
  | nil =>
    cases path with
    | nil => rfl
    | cons f rest =>
      simp [flipTree, flipTree_splayUp, flipTree_attach]
  | node k l r =>
    simp [flipTree, flipTree_splayUp]

theorem splay_cost_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    (t : BinaryTree β) (q : β) :
    splay.cost (flipTree neg t) (neg q) = splay.cost t q := by
  unfold splay.cost
  rw [descend_flipTree hanti t q]
  rcases h : descend t q with ⟨c, path⟩
  cases c with
  | nil =>
    cases path with
    | nil => rfl
    | cons f rest => simp [flipTree]
  | node k l r =>
    simp [flipTree]

theorem pop_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    (t : BinaryTree β) :
    SplayTree.pop (flipTree neg t) = flipTree neg (SplayTree.eject t) := by
  unfold SplayTree.pop SplayTree.eject
  rw [minKey_flipTree]
  cases t.maxKey? with
  | none => rfl
  | some k =>
    dsimp only [Option.map]
    rw [splay_flipTree hanti t k]
    cases splay t k <;> rfl

theorem eject_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    (t : BinaryTree β) :
    SplayTree.eject (flipTree neg t) = flipTree neg (SplayTree.pop t) := by
  unfold SplayTree.eject SplayTree.pop
  rw [maxKey_flipTree]
  cases t.minKey? with
  | none => rfl
  | some k =>
    dsimp only [Option.map]
    rw [splay_flipTree hanti t k]
    cases splay t k <;> rfl

theorem flipOp_step {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    (t : BinaryTree β) (op : DequeOp β) :
    (flipOp neg op).step (flipTree neg t) = flipTree neg (op.step t) := by
  cases op with
  | pop => exact eject_flipTree hanti t
  | push x => rfl
  | eject => exact pop_flipTree hanti t
  | inject x => rfl

theorem flipOp_cost {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    (t : BinaryTree β) (op : DequeOp β) :
    (flipOp neg op).cost (flipTree neg t) = op.cost t := by
  cases op with
  | pop =>
    simp only [flipOp, DequeOp.cost, ejectCost, popCost, maxKey_flipTree]
    cases t.minKey? with
    | none => rfl
    | some k => exact splay_cost_flipTree hanti t k
  | push _ => rfl
  | eject =>
    simp only [flipOp, DequeOp.cost, popCost, ejectCost, minKey_flipTree]
    cases t.maxKey? with
    | none => rfl
    | some k => exact splay_cost_flipTree hanti t k
  | inject _ => rfl

theorem flipOp_valid {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    (t : BinaryTree β) (op : DequeOp β) :
    (flipOp neg op).Valid (flipTree neg t) ↔ op.Valid t := by
  cases op with
  | pop => simp [flipOp, DequeOp.Valid, flipTree_eq_nil_iff]
  | push x =>
    simp only [flipOp, DequeOp.Valid, mem_flipTree_iff]
    constructor
    · intro h k hk
      exact (hanti k x).mp (h (neg k) ⟨k, hk, rfl⟩)
    · rintro h _ ⟨k, hk, rfl⟩
      exact (hanti k x).mpr (h k hk)
  | eject => simp [flipOp, DequeOp.Valid, flipTree_eq_nil_iff]
  | inject x =>
    simp only [flipOp, DequeOp.Valid, mem_flipTree_iff]
    constructor
    · intro h k hk
      exact (hanti x k).mp (h (neg k) ⟨k, hk, rfl⟩)
    · rintro h _ ⟨k, hk, rfl⟩
      exact (hanti x k).mpr (h k hk)

theorem dequeSeq_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    {m : ℕ} (init : BinaryTree β) (ops : Fin m → DequeOp β) (s : Fin (m + 1)) :
    dequeSeq (flipTree neg init) (fun i => flipOp neg (ops i)) s =
      flipTree neg (dequeSeq init ops s) := by
  rcases s with ⟨k, hk⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_lt : k < m := Nat.lt_of_succ_lt_succ hk
    let ik : Fin m := ⟨k, hk_lt⟩
    have hik_cs : ik.castSucc = ⟨k, Nat.lt_of_succ_lt hk⟩ := rfl
    change dequeSeq (flipTree neg init) (fun i => flipOp neg (ops i)) ik.succ =
      flipTree neg (dequeSeq init ops ik.succ)
    rw [dequeSeq_succ, dequeSeq_succ, hik_cs, ih (Nat.lt_of_succ_lt hk), flipOp_step hanti]

theorem validDequeSeq_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    {m : ℕ} (init : BinaryTree β) (ops : Fin m → DequeOp β) :
    ValidDequeSeq (flipTree neg init) (fun i => flipOp neg (ops i)) ↔ ValidDequeSeq init ops := by
  unfold ValidDequeSeq
  constructor <;> intro h i
  · have hi := h i
    rwa [dequeSeq_flipTree hanti, flipOp_valid hanti] at hi
  · rw [dequeSeq_flipTree hanti, flipOp_valid hanti]
    exact h i

theorem dequeSequenceCost_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    {m : ℕ} (init : BinaryTree β) (ops : Fin m → DequeOp β) :
    dequeSequenceCost (flipTree neg init) (fun i => flipOp neg (ops i)) =
      dequeSequenceCost init ops := by
  unfold dequeSequenceCost
  apply Finset.sum_congr rfl
  intro i _
  rw [dequeSeq_flipTree hanti, flipOp_cost hanti]

theorem isPop_flipOp {β γ : Type} (neg : β → γ) (op : DequeOp β) :
    (flipOp neg op).isPop = op.isEject := by
  cases op <;> rfl

theorem isEject_flipOp {β γ : Type} (neg : β → γ) (op : DequeOp β) :
    (flipOp neg op).isEject = op.isPop := by
  cases op <;> rfl

theorem popCount_flipOp {β γ : Type} (neg : β → γ) {m : ℕ} (ops : Fin m → DequeOp β) :
    popCount (fun i => flipOp neg (ops i)) = ejectCount ops := by
  simp [popCount, ejectCount, isPop_flipOp]

theorem ejectCount_flipOp {β γ : Type} (neg : β → γ) {m : ℕ} (ops : Fin m → DequeOp β) :
    ejectCount (fun i => flipOp neg (ops i)) = popCount ops := by
  simp [popCount, ejectCount, isEject_flipOp]

theorem filterMap_optionMap {α β γ : Type} (f : α → Option β) (g : β → γ) :
    ∀ xs : List α, xs.filterMap (fun a => (f a).map g) = (xs.filterMap f).map g
  | [] => rfl
  | a :: xs => by
    simp only [List.filterMap_cons]
    cases f a <;> simp [filterMap_optionMap f g xs]

theorem popDeletedKeys_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    {m : ℕ} (init : BinaryTree β) (ops : Fin m → DequeOp β) :
    popDeletedKeys (flipTree neg init) (fun i => flipOp neg (ops i)) =
      (ejectDeletedKeys init ops).map neg := by
  unfold popDeletedKeys ejectDeletedKeys
  rw [← filterMap_optionMap]
  congr 1
  ext i
  simp only [isPop_flipOp, dequeSeq_flipTree hanti, minKey_flipTree]
  cases (ops i).isEject <;> rfl

theorem ejectDeletedKeys_flipTree {β γ : Type} [LinearOrder β] [LinearOrder γ]
    {neg : β → γ} (hanti : ∀ x y : β, neg x < neg y ↔ y < x)
    {m : ℕ} (init : BinaryTree β) (ops : Fin m → DequeOp β) :
    ejectDeletedKeys (flipTree neg init) (fun i => flipOp neg (ops i)) =
      (popDeletedKeys init ops).map neg := by
  unfold ejectDeletedKeys popDeletedKeys
  rw [← filterMap_optionMap]
  congr 1
  ext i
  simp only [isEject_flipOp, dequeSeq_flipTree hanti, maxKey_flipTree]
  cases (ops i).isPop <;> rfl

theorem list_toFinset_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (xs : List α) :
    (xs.map f).toFinset = xs.toFinset.image f := by
  ext y; simp

def castOneSidedPopExec {P Q : ℕ} (h : P = Q) (exec : OneSidedPopExec P) : OneSidedPopExec Q where
  steps := exec.steps
  hValid := h ▸ exec.hValid
  hEndEmpty := exec.hEndEmpty
  hPushCount := h ▸ exec.hPushCount
  hPopSeq := h ▸ exec.hPopSeq

theorem mirror_eject_to_oneSided
    (h_part2 : ∀ {α : Type} [LinearOrder α] {m : ℕ} (init : BST α) (ops : Fin m → DequeOp α)
       (asn : ThreeWayKeyAssignment init ops),
      ValidDequeSeq init.tree ops → 1 ≤ popCount ops →
      ∃ HL : OneSidedPopExec (popCount ops),
        HL.cPop = asn.cPopU ∧ HL.kL ≤ 2 * popCount ops - 2 ∧ HL.kL < 2 * popCount ops)
    {α : Type} [LinearOrder α] {m : ℕ} (init : BST α) (ops : Fin m → DequeOp α)
    (asn : ThreeWayKeyAssignment init ops)
    (hValid : ValidDequeSeq init.tree ops) (hdR : 1 ≤ ejectCount ops) :
    ∃ HR : OneSidedPopExec (ejectCount ops), HR.cPop = asn.cEjectW := by
  have hantiD : ∀ x y : α, OrderDual.toDual x < OrderDual.toDual y ↔ y < x :=
    fun _ _ => Iff.rfl
  have hantiR : ∀ x y : ℝ, -x < -y ↔ y < x :=
    fun _ _ => neg_lt_neg_iff
  let initDual : BST αᵒᵈ := {
    tree := flipTree OrderDual.toDual init.tree
    hBST := isBST_flipTree hantiD init.hBST
  }
  let opsDual : Fin m → DequeOp αᵒᵈ := fun i => flipOp OrderDual.toDual (ops i)
  let T0Dual : BinaryTree ℝ := flipTree (fun x => -x) asn.T0
  let opsRDual : Fin m → DequeOp ℝ := fun i => flipOp (fun x => -x) (asn.opsR i)
  have hValidDual : ValidDequeSeq initDual.tree opsDual :=
    (validDequeSeq_flipTree hantiD init.tree ops).mpr hValid
  have hpCountDual : popCount opsDual = ejectCount ops :=
    popCount_flipOp OrderDual.toDual ops
  have heCountDual : ejectCount opsDual = popCount ops :=
    ejectCount_flipOp OrderDual.toDual ops
  let asnDual : ThreeWayKeyAssignment initDual opsDual := {
    T0 := T0Dual
    opsR := opsRDual
    Lm := -asn.Rm
    Rm := -asn.Lm
    hLmRm := neg_lt_neg asn.hLmRm
    hKind := fun i => by
      have hk := asn.hKind i
      cases h1 : ops i <;> cases h2 : asn.opsR i <;>
        · rw [h1, h2] at hk
          simp [opsDual, opsRDual, h1, h2, flipOp, DequeOp.sameKind] at hk ⊢
    hValidR := (validDequeSeq_flipTree hantiR asn.T0 asn.opsR).mpr asn.hValidR
    hBST := fun t => by
      rw [dequeSeq_flipTree hantiR]
      exact isBST_flipTree hantiR (asn.hBST t)
    hShape := fun t => by
      change (dequeSeq T0Dual opsRDual t).map (fun _ => ()) =
        (dequeSeq (flipTree OrderDual.toDual init.tree) opsDual t).map (fun _ => ())
      rw [dequeSeq_flipTree hantiR, dequeSeq_flipTree hantiD,
        map_unit_flipTree, map_unit_flipTree, asn.hShape t]
    hCost := by
      change dequeSequenceCost T0Dual opsRDual =
        dequeSequenceCost (flipTree OrderDual.toDual init.tree) opsDual
      rw [dequeSequenceCost_flipTree hantiR, dequeSequenceCost_flipTree hantiD, asn.hCost]
    everPresentKeys := open Classical in asn.everPresentKeys.image (fun x => -x)
    hActiveSub := fun t => by
      open Classical in
      rw [dequeSeq_flipTree hantiR, keyFinset_flipTree]
      exact Finset.image_subset_iff.mpr (fun x hx =>
        Finset.mem_image_of_mem _ (asn.hActiveSub t hx))
    hEverCard := by
      open Classical in
      have hcard : (asn.everPresentKeys.image (fun x : ℝ => -x)).card = asn.everPresentKeys.card :=
        Finset.card_image_of_injective _ neg_injective
      have hnodes : initDual.tree.num_nodes = init.tree.num_nodes :=
        num_nodes_flipTree OrderDual.toDual init.tree
      have h_orig := asn.hEverCard
      rw [hcard, hpCountDual, heCountDual, hnodes]
      omega
    hSurviving := by
      open Classical in
      rw [dequeSeq_flipTree hantiR, keyFinset_flipTree, asn.hSurviving]
      ext y
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨hx, hL, hR⟩, rfl⟩
        exact ⟨⟨x, hx, rfl⟩, by linarith, by linarith⟩
      · rintro ⟨⟨x, hx, rfl⟩, hL, hR⟩
        exact ⟨x, ⟨hx, by linarith, by linarith⟩, rfl⟩
    hPopOrder := by
      open Classical in
      dsimp only
      rw [popDeletedKeys_flipTree hantiR]
      refine ⟨?_, ?_, ?_⟩
      · have he_sort := asn.hEjectOrder.1
        generalize ejectDeletedKeys asn.T0 asn.opsR = es at he_sort
        induction es with
        | nil => simp
        | cons a rest ih =>
          obtain ⟨ha_gt, hrest⟩ := List.pairwise_cons.mp he_sort
          simp only [List.map_cons, List.pairwise_cons, List.mem_map]
          refine ⟨?_, ih hrest⟩
          rintro _ ⟨b, hb, rfl⟩
          exact neg_lt_neg (ha_gt b hb)
      · rw [List.length_map, asn.hEjectOrder.2.1, hpCountDual]
      · rw [list_toFinset_map, asn.hEjectOrder.2.2]
        ext y
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨x, ⟨hx, hR⟩, rfl⟩
          exact ⟨⟨x, hx, rfl⟩, by linarith⟩
        · rintro ⟨⟨x, hx, rfl⟩, hR⟩
          exact ⟨x, ⟨hx, by linarith⟩, rfl⟩
    hEjectOrder := by
      open Classical in
      dsimp only
      rw [ejectDeletedKeys_flipTree hantiR]
      refine ⟨?_, ?_, ?_⟩
      · have hp_sort := asn.hPopOrder.1
        generalize popDeletedKeys asn.T0 asn.opsR = ps at hp_sort
        induction ps with
        | nil => simp
        | cons a rest ih =>
          obtain ⟨ha_lt, hrest⟩ := List.pairwise_cons.mp hp_sort
          simp only [List.map_cons, List.pairwise_cons, List.mem_map]
          refine ⟨?_, ih hrest⟩
          rintro _ ⟨b, hb, rfl⟩
          exact neg_lt_neg (ha_lt b hb)
      · rw [List.length_map, asn.hPopOrder.2.1, heCountDual]
      · rw [list_toFinset_map, asn.hPopOrder.2.2]
        ext y
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨x, ⟨hx, hL⟩, rfl⟩
          exact ⟨⟨x, hx, rfl⟩, by linarith⟩
        · rintro ⟨⟨x, hx, rfl⟩, hL⟩
          exact ⟨x, ⟨hx, by linarith⟩, rfl⟩
  }
  have hdLDual : 1 ≤ popCount opsDual := by omega
  obtain ⟨HLDual, hcPopDual, _, _⟩ := h_part2 initDual opsDual asnDual hValidDual hdLDual
  refine ⟨castOneSidedPopExec hpCountDual HLDual, ?_⟩
  change HLDual.cPop = asn.cEjectW
  rw [hcPopDual]
  open Classical in
  unfold ThreeWayKeyAssignment.cPopU ThreeWayKeyAssignment.cEjectW
  apply Finset.sum_congr rfl
  intro i _
  have hisPop : (asnDual.opsR i).isPop = (asn.opsR i).isEject := isPop_flipOp _ (asn.opsR i)
  rw [hisPop]
  split_ifs with hej
  · have htree : asnDual.treeAt i.castSucc = flipTree (fun x => -x) (asn.treeAt i.castSucc) :=
      dequeSeq_flipTree hantiR asn.T0 asn.opsR i.castSucc
    rw [htree, popCascadePairs_flipTree, List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro p _
    have hmem_iff : ∀ z : ℝ, (-z ∈ asnDual.VL) ↔ (z ∈ asn.VR) := by
      intro z
      simp only [ThreeWayKeyAssignment.VL, ThreeWayKeyAssignment.VR, Finset.mem_filter,
        asnDual, Finset.mem_image]
      constructor
      · rintro ⟨⟨x, hx, hxz⟩, hle⟩
        have hzx : x = z := neg_injective hxz
        subst hzx
        exact ⟨hx, by linarith⟩
      · rintro ⟨hz, hge⟩
        exact ⟨⟨z, hz, rfl⟩, by linarith⟩
    simp [Function.comp, hmem_iff]
  · rfl

/-! ### Zero-Size `FoldedPopProcess` Helper and `thm_2_2_mod1_reduction` -/

def emptyFoldedPopProcess : FoldedPopProcess 0 where
  steps := []
  hValid := trivial
  hEndEmpty := rfl
  hPushCount := rfl
  hPopSeq := rfl
  hKLBound := Or.inl ⟨rfl, rfl⟩

theorem foldedPopProcess_zero_J (proc : FoldedPopProcess 0) : proc.J = 0 := by
  rcases proc.hKLBound with ⟨_, hsteps⟩ | ⟨h1, _⟩
  · simp [FoldedPopProcess.J, FoldedPopProcess.rInt, hsteps, collectFoldedPopRots]
  · omega

theorem exists_foldedPopProcess_of_eq_zero {P : ℕ} (hP : P = 0) :
    ∃ proc : FoldedPopProcess P, proc.J = 0 := by
  subst hP
  exact ⟨emptyFoldedPopProcess, foldedPopProcess_zero_J emptyFoldedPopProcess⟩

theorem popCount_add_ejectCount_le {α : Type} {m : ℕ} (ops : Fin m → DequeOp α) :
    popCount ops + ejectCount ops ≤ m := by
  unfold popCount ejectCount
  have hdisj : Disjoint
      (Finset.univ.filter (fun i : Fin m => (ops i).isPop))
      (Finset.univ.filter (fun i : Fin m => (ops i).isEject)) := by
    rw [Finset.disjoint_filter]
    intro i _ hp he
    rcases h : ops i with _ | _ | _ | _ <;> simp_all [DequeOp.isPop, DequeOp.isEject]
  rw [← Finset.card_union_of_disjoint hdisj]
  exact le_trans (Finset.card_le_univ _) (by simp)

theorem thm_2_2_from_parts
    (h_3_3 : ∀ {α : Type} [LinearOrder α] {m : ℕ}
      (init : BST α) (ops : Fin m → DequeOp α),
      ValidDequeSeq init.tree ops →
      ∃ asn : ThreeWayKeyAssignment init ops,
        asn.VL.card = popCount ops ∧
        asn.VM.card + 2 * (popCount ops + ejectCount ops) = init.tree.num_nodes + m ∧
        asn.VR.card = ejectCount ops ∧
        asn.everPresentKeys = asn.VL ∪ asn.VM ∪ asn.VR ∧
        (∀ x ∈ asn.VL, ∀ y ∈ asn.VM, x < y) ∧
        (∀ y ∈ asn.VM, ∀ z ∈ asn.VR, y < z))
    (h_3_4 : ∀ {α : Type} [LinearOrder α] (n m : ℕ)
      (init : BST α) (ops : Fin m → DequeOp α),
      init.tree.num_nodes = n → ValidDequeSeq init.tree ops →
      ∀ asn : ThreeWayKeyAssignment init ops,
        dequeSequenceCost init.tree ops ≤
          2 * (asn.cPopU : ℝ) + 2 * (asn.cEjectW : ℝ) + 9 * ((n : ℝ) + (m : ℝ)) ∧
        asn.ejectInducedLeftRotsOnU ≤ 2 * popCount ops - 2 ∧
        asn.popInducedRightRotsOnW ≤ 2 * ejectCount ops - 2 ∧
        (∀ i : Fin m, (asn.opsR i).isEject →
          let pairs := (open Classical in
            (ejectCascadePairs (asn.treeAt i.castSucc)).filter
              (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL))
          (∀ p ∈ pairs, p.1 ∈ rightSpine (asn.U i.castSucc) ∧
            p.2 ∈ rightSpine (asn.U i.castSucc) ∧ p.2 < p.1) ∧
          asn.U i.succ = pairs.foldl (fun acc p => rotateLeftEdge acc p.1 p.2) (asn.U i.castSucc)) ∧
        (∀ i : Fin m, (asn.opsR i).isPop →
          let pairs := (open Classical in
            (popCascadePairs (asn.treeAt i.castSucc)).filter
              (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR))
          (∀ p ∈ pairs, p.1 ∈ leftSpine (asn.W i.castSucc) ∧
            p.2 ∈ leftSpine (asn.W i.castSucc) ∧ p.1 < p.2) ∧
          asn.W i.succ = pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (asn.W i.castSucc)))
    (h_part2 : ∀ {α : Type} [LinearOrder α] {m : ℕ} (init : BST α) (ops : Fin m → DequeOp α)
       (asn : ThreeWayKeyAssignment init ops),
      ValidDequeSeq init.tree ops → 1 ≤ popCount ops →
      ∃ HL : OneSidedPopExec (popCount ops),
        HL.cPop = asn.cPopU ∧ HL.kL ≤ 2 * popCount ops - 2 ∧ HL.kL < 2 * popCount ops)
    (h_part3b : ∀ (P : ℕ), 1 ≤ P → ∀ exec : OneSidedPopExec P,
      exec.kL ≤ 2 * P - 2 ∧
      ∃ proc : FoldedPopProcess P,
        proc.steps = spineFoldOpList .nil exec.steps ∧
        (∀ τ : ℕ, τ ≤ exec.steps.length → proc.stateAt τ = spineFoldTree (exec.treeAt τ)) ∧
        exec.cPop ≤ P + proc.J) :
    ∃ C_red : ℝ, 0 < C_red ∧
      ∀ {α : Type} [LinearOrder α] (n m : ℕ) (init : BST α) (ops : Fin m → DequeOp α),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        ∃ (HL : FoldedPopProcess (popCount ops)) (HR : FoldedPopProcess (ejectCount ops)),
          dequeSequenceCost init.tree ops ≤
            2 * (HL.J : ℝ) + 2 * (HR.J : ℝ) + C_red * ((n : ℝ) + (m : ℝ)) := by
  refine ⟨11, by norm_num, ?_⟩
  intro α _ n m init ops hn hValid
  obtain ⟨asn, _⟩ := h_3_3 init ops hValid
  have hCost := (h_3_4 n m init ops hn hValid asn).1
  have hHL_ex : ∃ HL : FoldedPopProcess (popCount ops),
      (asn.cPopU : ℝ) ≤ (popCount ops : ℝ) + (HL.J : ℝ) := by
    by_cases hdL : popCount ops = 0
    · obtain ⟨proc0, hJ0⟩ := exists_foldedPopProcess_of_eq_zero hdL
      have hcPop0 : asn.cPopU = 0 := by
        unfold ThreeWayKeyAssignment.cPopU
        apply Finset.sum_eq_zero
        intro i _
        rcases hp : (asn.opsR i).isPop with _ | _
        · rfl
        · exfalso
          have hkind := asn.hKind i
          have hp_orig : (ops i).isPop = true := by
            rcases h1 : ops i with _ | _ | _ | _ <;>
              rcases h2 : asn.opsR i with _ | _ | _ | _ <;>
              · rw [h1, h2] at hkind
                rw [h2] at hp
                cases hkind
                try rfl
                try cases hp
          have hpos : 0 < popCount ops :=
            Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp_orig⟩⟩
          omega
      refine ⟨proc0, ?_⟩
      rw [hcPop0, hJ0, hdL]
      norm_num
    · have hdL1 : 1 ≤ popCount ops := by omega
      obtain ⟨execL, heqL, _, _⟩ := h_part2 init ops asn hValid hdL1
      obtain ⟨_, procL, _, _, hleL⟩ := h_part3b (popCount ops) hdL1 execL
      refine ⟨procL, ?_⟩
      rw [← heqL]
      exact_mod_cast hleL
  have hHR_ex : ∃ HR : FoldedPopProcess (ejectCount ops),
      (asn.cEjectW : ℝ) ≤ (ejectCount ops : ℝ) + (HR.J : ℝ) := by
    by_cases hdR : ejectCount ops = 0
    · obtain ⟨proc0, hJ0⟩ := exists_foldedPopProcess_of_eq_zero hdR
      have hcEj0 : asn.cEjectW = 0 := by
        unfold ThreeWayKeyAssignment.cEjectW
        apply Finset.sum_eq_zero
        intro i _
        rcases he : (asn.opsR i).isEject with _ | _
        · rfl
        · exfalso
          have hkind := asn.hKind i
          have he_orig : (ops i).isEject = true := by
            rcases h1 : ops i with _ | _ | _ | _ <;>
              rcases h2 : asn.opsR i with _ | _ | _ | _ <;>
              · rw [h1, h2] at hkind
                rw [h2] at he
                cases hkind
                try rfl
                try cases he
          have hpos : 0 < ejectCount ops :=
            Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, he_orig⟩⟩
          omega
      refine ⟨proc0, ?_⟩
      rw [hcEj0, hJ0, hdR]
      norm_num
    · have hdR1 : 1 ≤ ejectCount ops := by omega
      obtain ⟨execR, heqR⟩ := mirror_eject_to_oneSided h_part2 init ops asn hValid hdR1
      obtain ⟨_, procR, _, _, hleR⟩ := h_part3b (ejectCount ops) hdR1 execR
      refine ⟨procR, ?_⟩
      rw [← heqR]
      exact_mod_cast hleR
  obtain ⟨HL, hHL⟩ := hHL_ex
  obtain ⟨HR, hHR⟩ := hHR_ex
  have hd_le : (popCount ops : ℝ) + (ejectCount ops : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (popCount_add_ejectCount_le ops)
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine ⟨HL, HR, ?_⟩
  linarith

end EmptyingSimInternal

/-! ## Exported Layer-2 Theorems (`lem_3_5_emptying_sim` and `thm_2_2_mod1_reduction`) -/

/-- **Lemma 3.5** (`lem:emptying-sim`, Emptying One-Sided Simulation and Spine-Folding Bijection):
(1) Any `n_0`-node BST on `{1, ..., P}` can be built from `∅` using `n_0` `PUSH` steps,
`n_0 - |RS(H_init)|` root right-spine left rotations (`d = 1`), and `0` `POP` steps;
(2) Whenever `P := d_L ≥ 1`, relabeling `V_L` in `POP` order yields `H_L : OneSidedPopExec P`
with `C_POP(U) = C_POP(H_L)` and `K_L ≤ 2 P - 2 < 2 P`;
(3) Spine folding `spineFoldTree` is inverted by `spineUnfoldTree` on BSTs and maps any
`H : OneSidedPopExec P` (`P ≥ 1`) to a `FoldedPopProcess P` `H̃` with `C_POP(H) ≤ P + J(H̃)`. -/
theorem lem_3_5_emptying_sim
    (h_3_2 : ∀ {α : Type} [LinearOrder α]
      (t : BinaryTree α), t.IsBST → t ≠ .nil →
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
         SplayTree.eject t = ejectCascade t)) :
    -- Part (1): Reverse-spine initialization
    (∀ (P n₀ : ℕ) (H_init : BinaryTree ℕ),
      H_init.IsBST → H_init.num_nodes = n₀ → keyFinset H_init ⊆ Finset.Icc 1 P →
      ∃ initSteps : List OneSidedOp,
        ValidOneSidedOps P .nil initSteps ∧
        initSteps.foldl OneSidedOp.step .nil = H_init ∧
        (initSteps.filter (fun | .push _ => true | _ => false)).length = n₀ ∧
        (initSteps.filter (fun | .pop _ => true | _ => false)).length = 0 ∧
        (initSteps.filter (fun | .rightSpineLeftRot _ => true | _ => false)).length =
          n₀ - (rightSpine H_init).length ∧
        (∀ op ∈ initSteps, ∀ d : ℕ, op = .rightSpineLeftRot d → d = 1)) ∧
    -- Part (2): Emptying one-sided simulation of `U_t`
    (∀ {α : Type} [LinearOrder α] {m : ℕ} (init : BST α) (ops : Fin m → DequeOp α)
       (asn : ThreeWayKeyAssignment init ops),
      ValidDequeSeq init.tree ops → 1 ≤ popCount ops →
      ∃ HL : OneSidedPopExec (popCount ops),
        HL.cPop = asn.cPopU ∧ HL.kL ≤ 2 * popCount ops - 2 ∧ HL.kL < 2 * popCount ops) ∧
    -- Part (3): Spine-folding bijection and `eq:cpop-folded`
    ((∀ H : BinaryTree ℕ, H.IsBST →
        (spineFoldTree H).1.IsBST ∧
        keyFinset (spineFoldTree H).1 = keyFinset H ∧
        spineUnfoldTree (spineFoldTree H).1 (spineFoldTree H).2 = H) ∧
     (∀ (P : ℕ), 1 ≤ P → ∀ exec : OneSidedPopExec P,
        exec.kL ≤ 2 * P - 2 ∧
        ∃ proc : FoldedPopProcess P,
          proc.steps = spineFoldOpList .nil exec.steps ∧
          (∀ τ : ℕ, τ ≤ exec.steps.length → proc.stateAt τ = spineFoldTree (exec.treeAt τ)) ∧
          exec.cPop ≤ P + proc.J)) :=
  ⟨fun P n₀ H_init hBST hn₀ hKeys => by
     obtain ⟨initSteps, h1, h2, h3, h4, h5, h6⟩ :=
       SpineFoldInternal.lem_3_5_part1 P n₀ H_init hBST hn₀ hKeys
     refine ⟨initSteps, h1, h2, ?_, ?_, ?_, h6⟩
     · exact Eq.trans (congrArg List.length (List.filter_congr fun x _ => by cases x <;> rfl)) h3
     · exact Eq.trans (congrArg List.length (List.filter_congr fun x _ => by cases x <;> rfl)) h4
     · exact Eq.trans (congrArg List.length (List.filter_congr fun x _ => by cases x <;> rfl)) h5,
   EmptyingSimInternal.lem_3_5_part2 h_3_2
     (fun P n₀ H_init hBST hn₀ hKeys => by
       obtain ⟨initSteps, h1, h2, h3, h4, h5, h6⟩ :=
         SpineFoldInternal.lem_3_5_part1 P n₀ H_init hBST hn₀ hKeys
       refine ⟨initSteps, h1, h2, ?_, ?_, ?_, h6⟩
       · exact Eq.trans (congrArg List.length (List.filter_congr fun x _ => by cases x <;> rfl)) h3
       · exact Eq.trans (congrArg List.length (List.filter_congr fun x _ => by cases x <;> rfl)) h4
       · exact Eq.trans (congrArg List.length (List.filter_congr fun x _ => by cases x <;> rfl)) h5)
     (fun P hP exec => (SpineFoldInternal.lem_3_5_part3b P hP exec).1),
   SpineFoldInternal.lem_3_5_part3a,
   SpineFoldInternal.lem_3_5_part3b⟩

/-- **Theorem 2.2** (`thm:mod1-reduction`, Reduction to the Folded `POP` Process):
There exists an absolute constant `C_red > 0` reducing any valid two-sided deque execution
`(init, ops)` with `d_L = popCount ops` and `d_R = ejectCount ops` to folded `POP` processes
`H̃_L` of size `d_L` and `H̃_R` of size `d_R` (`J(∅) = 0` when `d_L = 0` or `d_R = 0`) satisfying
`Rot(T_0, S) ≤ 2 J(H̃_L) + 2 J(H̃_R) + C_red (n + m)`. -/
theorem thm_2_2_mod1_reduction
    (h_3_2 : ∀ {α : Type} [LinearOrder α]
      (t : BinaryTree α), t.IsBST → t ≠ .nil →
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
         SplayTree.eject t = ejectCascade t))
    (h_3_3 : ∀ {α : Type} [LinearOrder α] {m : ℕ}
      (init : BST α) (ops : Fin m → DequeOp α), ValidDequeSeq init.tree ops →
      ∃ asn : ThreeWayKeyAssignment init ops,
        asn.VL.card = popCount ops ∧
        asn.VM.card + 2 * (popCount ops + ejectCount ops) = init.tree.num_nodes + m ∧
        asn.VR.card = ejectCount ops ∧
        asn.everPresentKeys = asn.VL ∪ asn.VM ∪ asn.VR ∧
        (∀ x ∈ asn.VL, ∀ y ∈ asn.VM, x < y) ∧
        (∀ y ∈ asn.VM, ∀ z ∈ asn.VR, y < z))
    (h_3_4 : ∀ {α : Type} [LinearOrder α] (n m : ℕ)
      (init : BST α) (ops : Fin m → DequeOp α),
      init.tree.num_nodes = n → ValidDequeSeq init.tree ops →
      ∀ (asn : ThreeWayKeyAssignment init ops),
      dequeSequenceCost init.tree ops ≤
        2 * (asn.cPopU : ℝ) + 2 * (asn.cEjectW : ℝ) + 9 * ((n : ℝ) + (m : ℝ)) ∧
      asn.ejectInducedLeftRotsOnU ≤ 2 * popCount ops - 2 ∧
      asn.popInducedRightRotsOnW ≤ 2 * ejectCount ops - 2 ∧
      (∀ i : Fin m, (asn.opsR i).isEject →
        let pairs := (open Classical in
          (ejectCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL))
        (∀ p ∈ pairs, p.1 ∈ rightSpine (asn.U i.castSucc) ∧
          p.2 ∈ rightSpine (asn.U i.castSucc) ∧ p.2 < p.1) ∧
        asn.U i.succ = pairs.foldl (fun acc p => rotateLeftEdge acc p.1 p.2) (asn.U i.castSucc)) ∧
      (∀ i : Fin m, (asn.opsR i).isPop →
        let pairs := (open Classical in
          (popCascadePairs (asn.treeAt i.castSucc)).filter
            (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR))
        (∀ p ∈ pairs, p.1 ∈ leftSpine (asn.W i.castSucc) ∧
          p.2 ∈ leftSpine (asn.W i.castSucc) ∧ p.1 < p.2) ∧
        asn.W i.succ = pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (asn.W i.castSucc))) :
    ∃ C_red : ℝ, 0 < C_red ∧
      ∀ {α : Type} [LinearOrder α] (n m : ℕ) (init : BST α) (ops : Fin m → DequeOp α),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        ∃ (HL : FoldedPopProcess (popCount ops)) (HR : FoldedPopProcess (ejectCount ops)),
          dequeSequenceCost init.tree ops ≤
            2 * (HL.J : ℝ) + 2 * (HR.J : ℝ) + C_red * ((n : ℝ) + (m : ℝ)) :=
  EmptyingSimInternal.thm_2_2_from_parts h_3_3 h_3_4
    (lem_3_5_emptying_sim h_3_2).2.1
    (lem_3_5_emptying_sim h_3_2).2.2.2

end Solution.EmptyingMod1
