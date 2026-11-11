module

public import Challenge.Definitions
public import Solution.TreeFacts
public import Mathlib

/-!
# Section 5.2–5.4: Leaf Subprocess Projection, `LCA_𝒯` Routing of `ℬ_1`, and `ℬ_{3,intra}`

Formalization of `main_v1.tex`:
- **Lemma 5.2** (`lem_5_2_bucket_leaf`): Intra-leaf rotations and leaf subprocess projection.
- **Lemma 5.3** (`lem_5_3_bucket_b1`): `LCA_𝒯` routing of `ℬ_1` and cascade-path sink counting.
- **Lemma 5.4** (`lem_5_4_bucket_b3_intra`): Height-independent potential bound on `ℬ_{3,intra}`.
-/

@[expose] public section

namespace Solution.BucketLeafB1

open SplayTree

namespace Subproc52
open BinaryTree

/-- Downward-closed BST projection onto `{x | x ≤ R}`. -/
def trimAbove (R : ℕ) : BinaryTree ℕ → BinaryTree ℕ
  | .nil => .nil
  | .node k l r => if k ≤ R then .node k l (trimAbove R r) else trimAbove R l

namespace HelperLeafSubproc

/-! ## Section 1: Basic BinaryTree, BST, Spine, and Cascade Lemmas -/

lemma mem_keyFinset_iff [DecidableEq α] {t : BinaryTree α} {x : α} :
    x ∈ keyFinset t ↔ x ∈ t := by
  induction t with
  | nil => simp [keyFinset]
  | node k l r ihl ihr =>
    simp only [keyFinset, Finset.mem_insert, Finset.mem_union, mem_node_iff, ihl, ihr]

lemma leftSpine_eq_nil_iff (t : BinaryTree α) :
    leftSpine t = [] ↔ t = .nil := by
  cases t <;> simp [leftSpine]

lemma rightSpine_eq_nil_iff (t : BinaryTree α) :
    rightSpine t = [] ↔ t = .nil := by
  cases t <;> simp [rightSpine]

lemma minKey?_eq_head?_toKeyList (t : BinaryTree α) :
    t.minKey? = t.toKeyList.head? := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    cases hl : l.toKeyList with
    | nil =>
      have hnil := eq_nil_of_toKeyList_eq_nil hl
      subst hnil
      rfl
    | cons a as =>
      simp [BinaryTree.minKey?, ihl, hl]

lemma getLast?_leftSpine (t : BinaryTree α) :
    (leftSpine t).getLast? = rootKey? t := by
  cases t <;> simp [leftSpine, rootKey?]

lemma mem_leftSpine_mem {t : BinaryTree α} {x : α} (hx : x ∈ leftSpine t) : x ∈ t := by
  induction t with
  | nil => simp [leftSpine] at hx
  | node k l r ihl _ =>
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with h | rfl
    · exact .left (ihl h)
    · exact .here

lemma mem_rightSpine_mem {t : BinaryTree α} {x : α} (hx : x ∈ rightSpine t) : x ∈ t := by
  induction t with
  | nil => simp [rightSpine] at hx
  | node k l r _ ihr =>
    simp only [rightSpine, List.mem_cons] at hx
    rcases hx with rfl | h
    · exact .here
    · exact .right (ihr h)

lemma leftSpine_pairwise [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    simp only [leftSpine, List.pairwise_append, List.pairwise_singleton, List.mem_singleton]
    refine ⟨ihl (IsBST_left_of_IsBST ht), trivial, ?_⟩
    rintro x hx y rfl
    exact lt_of_IsBST_left l y r ht (mem_leftSpine_mem hx)

lemma rightSpine_pairwise [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (rightSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [rightSpine]
  | node k l r _ ihr =>
    simp only [rightSpine, List.pairwise_cons]
    exact ⟨fun x hx => gt_of_IsBST_right l k r ht (mem_rightSpine_mem hx),
      ihr (IsBST_right_of_IsBST ht)⟩

lemma rightSpine_length_le_num_nodes (t : BinaryTree α) :
    (rightSpine t).length ≤ t.num_nodes := by
  induction t with
  | nil => simp [rightSpine]
  | node k l r _ ihr => simp [rightSpine]; omega

lemma toKeyList_spliceMin (t : BinaryTree α) :
    (spliceMin t).toKeyList = t.toKeyList.tail := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    cases l with
    | nil => simp [spliceMin]
    | node lk ll lr =>
      have hsp : spliceMin (BinaryTree.node k (.node lk ll lr) r) =
          .node k (spliceMin (.node lk ll lr)) r := rfl
      rw [hsp, toKeyList_node, ihl]
      change (BinaryTree.node lk ll lr).toKeyList.tail ++ [k] ++ r.toKeyList =
        ((BinaryTree.node lk ll lr).toKeyList ++ [k] ++ r.toKeyList).tail
      rcases h : (BinaryTree.node lk ll lr).toKeyList with _ | ⟨x, xs⟩
      · simp at h
      · simp

lemma toKeyList_rotateRightEdge [LinearOrder α] (t : BinaryTree α) (x p : α) :
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
        by_cases hlx : lx = x <;> simp [hlx, List.append_assoc]

lemma toKeyList_rotateRightEdge_foldl [LinearOrder α] (pairs : List (α × α)) (t : BinaryTree α) :
    (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t).toKeyList = t.toKeyList := by
  induction pairs generalizing t with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons, ih, toKeyList_rotateRightEdge]

lemma toKeyList_popCascade [LinearOrder α] (t : BinaryTree α) :
    (popCascade t).toKeyList = t.toKeyList.tail := by
  rw [popCascade, toKeyList_rotateRightEdge_foldl, toKeyList_spliceMin]

lemma toKeyList_rotateLeftAtRightSpine1 (t : BinaryTree α) {d : ℕ} (hd : 1 ≤ d) :
    (rotateLeftAtRightSpine1 t d).toKeyList = t.toKeyList := by
  induction d generalizing t with
  | zero => omega
  | succ d' ih =>
    cases d' with
    | zero => simp [rotateLeftAtRightSpine1]
    | succ d'' =>
      cases t with
      | nil => rfl
      | node k l r =>
        simp [rotateLeftAtRightSpine1, ih r (by omega)]

lemma isBST_push [LinearOrder α] {t : BinaryTree α} {w : α}
    (ht : t.IsBST) (hw : ∀ k ∈ t, w < k) : (SplayTree.push t w).IsBST := by
  rw [IsBST_iff_toKeyList_sorted] at ht ⊢
  simp only [SplayTree.push, toKeyList_node, toKeyList_empty, List.nil_append,
    List.singleton_append, List.pairwise_cons]
  exact ⟨fun x hx => hw x (mem_iff_mem_toKeyList.mpr hx), ht⟩

lemma isBST_spliceMin [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (spliceMin t).IsBST := by
  rw [IsBST_iff_toKeyList_sorted] at ht ⊢
  rw [toKeyList_spliceMin]
  exact ht.sublist (List.tail_sublist _)

lemma isBST_rotateRightEdge [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) (x p : α) :
    (rotateRightEdge t x p).IsBST :=
  IsBST_of_toKeyList_eq (toKeyList_rotateRightEdge t x p) ht

lemma isBST_popCascade [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (popCascade t).IsBST := by
  rw [IsBST_iff_toKeyList_sorted] at ht ⊢
  rw [toKeyList_popCascade]
  exact ht.sublist (List.tail_sublist _)

lemma isBST_rotateLeftAtRightSpine1 [LinearOrder α] {t : BinaryTree α} {d : ℕ}
    (ht : t.IsBST) (hd : 1 ≤ d) : (rotateLeftAtRightSpine1 t d).IsBST :=
  IsBST_of_toKeyList_eq (toKeyList_rotateLeftAtRightSpine1 t hd) ht

lemma minKey?_eq_some_iff_of_isBST [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) {s : α} :
    t.minKey? = some s ↔ s ∈ t ∧ ∀ k ∈ t, s ≤ k := by
  rw [minKey?_eq_head?_toKeyList]
  have hsort := (IsBST_iff_toKeyList_sorted t).mp ht
  cases hl : t.toKeyList with
  | nil =>
    have hnil := eq_nil_of_toKeyList_eq_nil hl
    subst hnil
    simp
  | cons a as =>
    rw [hl] at hsort
    rw [List.pairwise_cons] at hsort
    simp only [List.head?_cons, Option.some.injEq]
    constructor
    · rintro rfl
      refine ⟨mem_iff_mem_toKeyList.mpr (by simp [hl]), fun k hk => ?_⟩
      have hk' : k ∈ a :: as := hl ▸ mem_iff_mem_toKeyList.mp hk
      rcases List.mem_cons.mp hk' with rfl | hmem
      · exact le_rfl
      · exact le_of_lt (hsort.1 k hmem)
    · rintro ⟨hs, hle⟩
      have hs' : s ∈ a :: as := hl ▸ mem_iff_mem_toKeyList.mp hs
      rcases List.mem_cons.mp hs' with rfl | hmem
      · rfl
      · have ha : a ∈ t := mem_iff_mem_toKeyList.mpr (by simp [hl])
        exact absurd (hsort.1 s hmem) (not_lt.mpr (hle a ha))

lemma adjacentPairs_append_of_even {xs ys : List α} {h : ℕ} (hlen : xs.length = 2 * h) :
    adjacentPairs (xs ++ ys) = adjacentPairs xs ++ adjacentPairs ys ∧
    (adjacentPairs xs).length = h := by
  induction h generalizing xs with
  | zero =>
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp [adjacentPairs]
  | succ h' ih =>
    rcases xs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hlen
    · simp at hlen; omega
    · simp only [List.length_cons] at hlen
      obtain ⟨h1, h2⟩ := ih (xs := rest) (by omega)
      simp [adjacentPairs, h1, h2]

lemma foldl_rotateRightEdge_node_lt [LinearOrder α] (pairs : List (α × α))
    (k : α) (l r : BinaryTree α) (hlt : ∀ p ∈ pairs, p.2 < k) :
    pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (.node k l r) =
      .node k (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) l) r := by
  induction pairs generalizing l with
  | nil => rfl
  | cons p ps ih =>
    have hp : p.2 < k := hlt p (by simp)
    simp only [List.foldl_cons, rotateRightEdge, hp, ite_true]
    exact ih (rotateRightEdge l p.1 p.2) (fun q hq => hlt q (by simp [hq]))

lemma mem_adjacentPairs_snd {xs : List α} {p : α × α} (hp : p ∈ adjacentPairs xs) :
    p.2 ∈ xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [adjacentPairs] at hp
  | singleton a => simp [adjacentPairs] at hp
  | cons_cons a b rest ih _ =>
    simp only [adjacentPairs, List.mem_cons] at hp
    rcases hp with rfl | hrest
    · simp
    · exact List.mem_cons_of_mem a (List.mem_cons_of_mem b (ih hrest))

lemma mem_adjacentPairs_fst {xs : List α} {p : α × α} (hp : p ∈ adjacentPairs xs) :
    p.1 ∈ xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [adjacentPairs] at hp
  | singleton a => simp [adjacentPairs] at hp
  | cons_cons a b rest ih _ =>
    simp only [adjacentPairs, List.mem_cons] at hp
    rcases hp with rfl | hrest
    · simp
    · exact List.mem_cons_of_mem a (List.mem_cons_of_mem b (ih hrest))

/-! ## Section 2: Spine-Folding Commutation (`spineFoldTree` & `spineFoldOpList`) -/

/-- Single-step operation mapping matching `spineFoldOpList`. -/
def spineFoldOp (t : BinaryTree ℕ) : OneSidedOp → FoldedOp
  | .push w => .push w
  | .pop s => .pop s
  | .rightSpineLeftRot d =>
    if d ≤ 1 then .shift
    else
      let rs := rightSpine t
      match rs[d - 2]?, rs[d - 1]? with
      | some u, some v => .upperRot u v
      | _, _ => .shift

@[simp] lemma spineFoldOpList_nil (t : BinaryTree ℕ) :
    spineFoldOpList t [] = [] := rfl

@[simp] lemma spineFoldOpList_cons (t : BinaryTree ℕ) (op : OneSidedOp) (rest : List OneSidedOp) :
    spineFoldOpList t (op :: rest) = spineFoldOp t op :: spineFoldOpList (op.step t) rest := rfl

lemma spineFoldOpList_append (t : BinaryTree ℕ) (ops₁ ops₂ : List OneSidedOp) :
    spineFoldOpList t (ops₁ ++ ops₂) =
      spineFoldOpList t ops₁ ++ spineFoldOpList (ops₁.foldl OneSidedOp.step t) ops₂ := by
  induction ops₁ generalizing t with
  | nil => rfl
  | cons op rest ih =>
    simp [ih (op.step t)]

def framesKeyList : List (α × BinaryTree α) → List α
  | [] => []
  | (b, l) :: rest => l.toKeyList ++ [b] ++ framesKeyList rest

lemma framesKeyList_rightSpineFrames (t : BinaryTree α) :
    framesKeyList (rightSpineFrames t) = t.toKeyList := by
  induction t with
  | nil => rfl
  | node b l r _ ihr =>
    simp [rightSpineFrames, framesKeyList, ihr, List.append_assoc]

lemma toKeyList_spineFoldGo (prevKey : α) (acc : BinaryTree α) (frames : List (α × BinaryTree α)) :
    (spineFoldGo prevKey acc frames).toKeyList =
      acc.toKeyList ++ [prevKey] ++ framesKeyList frames := by
  induction frames generalizing prevKey acc with
  | nil => simp [spineFoldGo, framesKeyList]
  | cons f rest ih =>
    rcases f with ⟨bNext, lNext⟩
    simp [spineFoldGo, framesKeyList, ih, List.append_assoc]

lemma toKeyList_spineFoldTree (t : BinaryTree α) :
    (spineFoldTree t).1.toKeyList = t.toKeyList := by
  cases t with
  | nil => rfl
  | node b1 l1 r1 =>
    simp [spineFoldTree, rightSpineFrames, toKeyList_spineFoldGo,
      framesKeyList_rightSpineFrames, List.append_assoc]

lemma isBST_spineFoldTree [LinearOrder α] {t : BinaryTree α} (ht : t.IsBST) :
    (spineFoldTree t).1.IsBST :=
  IsBST_of_toKeyList_eq (toKeyList_spineFoldTree t) ht

lemma mem_spineFoldTree_iff {t : BinaryTree α} {x : α} :
    x ∈ (spineFoldTree t).1 ↔ x ∈ t := by
  rw [mem_iff_mem_toKeyList, toKeyList_spineFoldTree, ← mem_iff_mem_toKeyList]

lemma minKey?_spineFoldTree (t : BinaryTree α) :
    (spineFoldTree t).1.minKey? = t.minKey? := by
  rw [minKey?_eq_head?_toKeyList, toKeyList_spineFoldTree, ← minKey?_eq_head?_toKeyList]

lemma spineFoldGo_ne_nil (prevKey : α) (acc : BinaryTree α) (frames : List (α × BinaryTree α)) :
    spineFoldGo prevKey acc frames ≠ .nil := by
  induction frames generalizing prevKey acc with
  | nil => simp [spineFoldGo]
  | cons f rest ih => exact ih f.1 (.node prevKey acc f.2)

lemma spineFoldTree_fst_eq_nil_iff (t : BinaryTree α) :
    (spineFoldTree t).1 = .nil ↔ t = .nil := by
  cases t with
  | nil => simp [spineFoldTree]
  | node b1 l1 r1 =>
    simp [spineFoldTree, rightSpineFrames, spineFoldGo_ne_nil]

lemma spineFoldTree_snd_eq_none_iff (t : BinaryTree α) :
    (spineFoldTree t).2 = none ↔ t = .nil := by
  cases t <;> simp [spineFoldTree, rightSpineFrames]

lemma map_fst_rightSpineFrames (t : BinaryTree α) :
    (rightSpineFrames t).map Prod.fst = rightSpine t := by
  induction t with
  | nil => rfl
  | node b l r _ ihr => simp [rightSpineFrames, rightSpine, ihr]

lemma leftSpine_spineFoldGo (prevKey : α) (acc : BinaryTree α) (frames : List (α × BinaryTree α)) :
    leftSpine (spineFoldGo prevKey acc frames) =
      leftSpine acc ++ (prevKey :: frames.map Prod.fst) := by
  induction frames generalizing prevKey acc with
  | nil => simp [spineFoldGo, leftSpine]
  | cons f rest ih =>
    rcases f with ⟨bNext, lNext⟩
    simp [spineFoldGo, leftSpine, ih, List.append_assoc]

lemma rootKey?_spineFoldGo (prevKey : α) (acc : BinaryTree α) (frames : List (α × BinaryTree α)) :
    rootKey? (spineFoldGo prevKey acc frames) =
      (prevKey :: frames.map Prod.fst).getLast? := by
  rw [← getLast?_leftSpine, leftSpine_spineFoldGo]
  rw [List.getLast?_append_of_ne_nil _ (by simp)]

lemma takeThrough_append_of_not_mem [DecidableEq α] {xs ys : List α} {b : α} (hb : b ∉ xs) :
    takeThrough (xs ++ b :: ys) b = xs ++ [b] := by
  induction xs with
  | nil => simp [takeThrough]
  | cons x xs ih =>
    have hxb : x ≠ b := fun h => hb (by simp [h])
    simp [takeThrough, hxb, ih (fun h => hb (by simp [h]))]

lemma nextOnSpine_append_of_not_mem [DecidableEq α] {xs rest : List α} {b c : α} (hb : b ∉ xs) :
    nextOnSpine (xs ++ b :: c :: rest) b = some c := by
  induction xs with
  | nil => simp [nextOnSpine]
  | cons x xs ih =>
    have hxb : x ≠ b := fun h => hb (by simp [h])
    have htail := ih (fun h => hb (by simp [h]))
    rcases h : xs ++ b :: c :: rest with _ | ⟨y, zs⟩
    · simp at h
    · rw [List.cons_append]
      rw [h] at htail ⊢
      simp [nextOnSpine, hxb, htail]

lemma modifyLeftAt_spineFoldGo_lt [LinearOrder α] (prevKey : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) (target : α) (f : BinaryTree α → BinaryTree α)
    (hord : (prevKey :: frames.map Prod.fst).Pairwise (· < ·))
    (hlt : target < prevKey) :
    modifyLeftAt (spineFoldGo prevKey acc frames) target f =
      spineFoldGo prevKey (modifyLeftAt acc target f) frames := by
  induction frames generalizing prevKey acc with
  | nil =>
    simp [spineFoldGo, modifyLeftAt, hlt]
  | cons fr rest ih =>
    rcases fr with ⟨bNext, lNext⟩
    rw [List.map_cons, List.pairwise_cons] at hord
    have hltNext : target < bNext := lt_trans hlt (hord.1 bNext (by simp))
    dsimp only [spineFoldGo]
    rw [ih bNext (.node prevKey acc lNext) hord.2 hltNext]
    simp [modifyLeftAt, hlt]

lemma modifyLeftAt_spineFoldGo_eq [LinearOrder α] (prevKey : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) (f : BinaryTree α → BinaryTree α)
    (hord : (prevKey :: frames.map Prod.fst).Pairwise (· < ·)) :
    modifyLeftAt (spineFoldGo prevKey acc frames) prevKey f =
      spineFoldGo prevKey (f acc) frames := by
  cases frames with
  | nil =>
    simp [spineFoldGo, modifyLeftAt]
  | cons fr rest =>
    rcases fr with ⟨bNext, lNext⟩
    rw [List.map_cons, List.pairwise_cons] at hord
    have hpb : prevKey < bNext := hord.1 bNext (by simp)
    dsimp only [spineFoldGo]
    rw [modifyLeftAt_spineFoldGo_lt bNext (.node prevKey acc lNext) rest prevKey f hord.2 hpb]
    simp [modifyLeftAt]

lemma spliceMin_spineFoldGo (prevKey : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) (hne : acc ≠ .nil) :
    spliceMin (spineFoldGo prevKey acc frames) =
      spineFoldGo prevKey (spliceMin acc) frames := by
  induction frames generalizing prevKey acc with
  | nil =>
    cases acc with
    | nil => exact absurd rfl hne
    | node ak al ar => rfl
  | cons fr rest ih =>
    rcases fr with ⟨bNext, lNext⟩
    dsimp only [spineFoldGo]
    rw [ih bNext (.node prevKey acc lNext) (by simp)]
    cases acc with
    | nil => exact absurd rfl hne
    | node ak al ar => rfl

lemma rotateRightEdge_spineFoldGo_lt [LinearOrder α] (prevKey : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) (x p : α)
    (hord : (prevKey :: frames.map Prod.fst).Pairwise (· < ·))
    (hlt : p < prevKey) :
    rotateRightEdge (spineFoldGo prevKey acc frames) x p =
      spineFoldGo prevKey (rotateRightEdge acc x p) frames := by
  induction frames generalizing prevKey acc with
  | nil =>
    simp [spineFoldGo, rotateRightEdge, hlt]
  | cons fr rest ih =>
    rcases fr with ⟨bNext, lNext⟩
    rw [List.map_cons, List.pairwise_cons] at hord
    have hltNext : p < bNext := lt_trans hlt (hord.1 bNext (by simp))
    dsimp only [spineFoldGo]
    rw [ih bNext (.node prevKey acc lNext) hord.2 hltNext]
    simp [rotateRightEdge, hlt]

lemma foldl_rotateRightEdge_spineFoldGo_lt [LinearOrder α] (pairs : List (α × α))
    (prevKey : α) (acc : BinaryTree α) (frames : List (α × BinaryTree α))
    (hord : (prevKey :: frames.map Prod.fst).Pairwise (· < ·))
    (hlt : ∀ p ∈ pairs, p.2 < prevKey) :
    pairs.foldl (fun t p => rotateRightEdge t p.1 p.2) (spineFoldGo prevKey acc frames) =
      spineFoldGo prevKey (pairs.foldl (fun t p => rotateRightEdge t p.1 p.2) acc) frames := by
  induction pairs generalizing acc with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons, List.foldl_cons,
      rotateRightEdge_spineFoldGo_lt prevKey acc frames p.1 p.2 hord (hlt p (by simp))]
    exact ih (rotateRightEdge acc p.1 p.2) (fun q hq => hlt q (by simp [hq]))

lemma subtreeAtKey_spineFoldGo_lt [LinearOrder α] (prevKey : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α)) (v : α)
    (hord : (prevKey :: frames.map Prod.fst).Pairwise (· < ·))
    (hlt : v < prevKey) :
    subtreeAtKey (spineFoldGo prevKey acc frames) v = subtreeAtKey acc v := by
  induction frames generalizing prevKey acc with
  | nil =>
    simp [spineFoldGo, subtreeAtKey, hlt]
  | cons fr rest ih =>
    rcases fr with ⟨bNext, lNext⟩
    rw [List.map_cons, List.pairwise_cons] at hord
    have hltNext : v < bNext := lt_trans hlt (hord.1 bNext (by simp))
    dsimp only [spineFoldGo]
    rw [ih bNext (.node prevKey acc lNext) hord.2 hltNext]
    simp [subtreeAtKey, hlt]

lemma subtreeAtKey_spineFoldGo_eq [LinearOrder α] (prevKey : α) (acc : BinaryTree α)
    (bNext : α) (lNext : BinaryTree α) (rest : List (α × BinaryTree α))
    (hord : (prevKey :: bNext :: rest.map Prod.fst).Pairwise (· < ·)) :
    subtreeAtKey (spineFoldGo prevKey acc ((bNext, lNext) :: rest)) prevKey =
      .node prevKey acc lNext := by
  rw [List.pairwise_cons] at hord
  have hpb : prevKey < bNext := hord.1 bNext (by simp)
  dsimp only [spineFoldGo]
  rw [subtreeAtKey_spineFoldGo_lt bNext (.node prevKey acc lNext) rest prevKey hord.2 hpb]
  simp [subtreeAtKey]

def rotFramesAt : List (α × BinaryTree α) → ℕ → List (α × BinaryTree α)
  | (b1, l1) :: (b2, l2) :: rest, 0 => (b2, .node b1 l1 l2) :: rest
  | f :: rest, i + 1 => f :: rotFramesAt rest i
  | frames, _ => frames

lemma rotFramesAt_cons_succ (f : α × BinaryTree α) (rest : List (α × BinaryTree α)) (j : ℕ) :
    rotFramesAt (f :: rest) (j + 1) = f :: rotFramesAt rest j := by
  rcases f with ⟨_, _⟩
  rcases rest with _ | ⟨⟨_, _⟩, _⟩ <;> rfl

lemma rightSpineFrames_rotateLeftAtRightSpine1 (t : BinaryTree α) (i : ℕ) :
    rightSpineFrames (rotateLeftAtRightSpine1 t (i + 1)) =
      rotFramesAt (rightSpineFrames t) i := by
  induction i generalizing t with
  | zero =>
    rcases t with _ | ⟨b1, l1, _ | ⟨b2, l2, r2⟩⟩ <;>
      simp [rotateLeftAtRightSpine1, BinaryTree.rotateLeft, rightSpineFrames, rotFramesAt]
  | succ j ih =>
    cases t with
    | nil => rfl
    | node k l r =>
      simp [rotateLeftAtRightSpine1, rightSpineFrames, rotFramesAt, ih r]

lemma spineFoldGo_rotFramesAt [LinearOrder α] (j : ℕ) (prevKey : α) (acc : BinaryTree α)
    (frames : List (α × BinaryTree α))
    (hord : (prevKey :: frames.map Prod.fst).Pairwise (· < ·))
    (hlen : j + 2 ≤ frames.length) :
    ∃ u v : α,
      (prevKey :: frames.map Prod.fst)[j]? = some u ∧
      (prevKey :: frames.map Prod.fst)[j + 1]? = some v ∧
      IsRightRotEdge (spineFoldGo prevKey acc frames) u v ∧
      spineFoldGo prevKey acc (rotFramesAt frames j) =
        rotateRightEdge (spineFoldGo prevKey acc frames) u v := by
  induction j generalizing prevKey acc frames with
  | zero =>
    rcases frames with _ | ⟨⟨v, lv⟩, _ | ⟨⟨w, lw⟩, rest⟩⟩
    · simp at hlen
    · simp at hlen
    · rw [List.map_cons, List.map_cons, List.pairwise_cons] at hord
      have hord_vw : (v :: w :: rest.map Prod.fst).Pairwise (· < ·) := hord.2
      refine ⟨prevKey, v, rfl, rfl, ?_, ?_⟩
      · refine ⟨acc, lv, lw, ?_, ?_⟩
        · rw [mem_iff_mem_toKeyList, toKeyList_spineFoldGo]
          simp [framesKeyList]
        · dsimp only [spineFoldGo]
          exact subtreeAtKey_spineFoldGo_eq v (.node prevKey acc lv) w lw rest hord_vw
      · rw [List.pairwise_cons] at hord_vw
        have hvw : v < w := hord_vw.1 w (by simp)
        dsimp only [rotFramesAt, spineFoldGo]
        rw [rotateRightEdge_spineFoldGo_lt w (.node v (.node prevKey acc lv) lw)
          rest prevKey v hord_vw.2 hvw]
        simp [rotateRightEdge]
  | succ j' ih =>
    rcases frames with _ | ⟨⟨bNext, lNext⟩, rest⟩
    · simp at hlen
    · simp only [List.length_cons] at hlen
      rw [List.map_cons, List.pairwise_cons] at hord
      rw [rotFramesAt_cons_succ]
      dsimp only [spineFoldGo]
      obtain ⟨u, v, hu, hv, hedge, hrot⟩ :=
        ih bNext (.node prevKey acc lNext) rest hord.2 (by omega)
      exact ⟨u, v, hu, hv, hedge, hrot⟩

/-- Explicit structural decomposition of `popCascade` on `.node b1 l1 r1`. -/
lemma popCascade_node_cases [LinearOrder α] {b1 : α} {l1 r1 : BinaryTree α}
    (hBST : (BinaryTree.node b1 l1 r1).IsBST) :
    (l1 = .nil ∧ popCascade (.node b1 l1 r1) = r1) ∨
    (∃ h : ℕ, (leftSpine l1).length = 2 * h + 1 ∧ l1 ≠ .nil ∧
      (adjacentPairs (leftSpine l1 ++ [b1]).tail).take h = popCascadePairs l1 ∧
      (∀ p ∈ popCascadePairs l1, p.2 < b1) ∧
      popCascade (.node b1 l1 r1) = .node b1 (popCascade l1) r1) ∨
    (∃ (h : ℕ) (vTop : α) (aTop rTop : BinaryTree α),
      l1 = .node vTop aTop rTop ∧
      (leftSpine l1).length = 2 * h + 2 ∧
      (leftSpine aTop).length = 2 * h + 1 ∧ aTop ≠ .nil ∧
      (adjacentPairs (leftSpine l1 ++ [b1]).tail).take h = popCascadePairs aTop ∧
      (∀ p ∈ popCascadePairs aTop, p.2 < vTop) ∧
      (∀ p ∈ popCascadePairs aTop, p.2 < b1) ∧
      popCascade (.node b1 l1 r1) = .node vTop (popCascade aTop) (.node b1 rTop r1)) := by
  by_cases hk0 : (leftSpine l1).length = 0
  · left
    have hl1 : l1 = .nil := (leftSpine_eq_nil_iff l1).mp (List.eq_nil_of_length_eq_zero hk0)
    subst hl1
    exact ⟨rfl, by simp [popCascade, popCascadePairs, leftSpine, adjacentPairs, spliceMin]⟩
  · right
    have hl1_ne : l1 ≠ .nil := fun h => by simp [h, leftSpine] at hk0
    set k := (leftSpine l1).length
    set h := (k - 1) / 2
    rcases (show k = 2 * h + 1 ∨ k = 2 * h + 2 by omega) with hk_odd | hk_even
    · left
      have htail_len : (leftSpine l1).tail.length = 2 * h := by
        have : (leftSpine l1).length = k := rfl
        cases hls1 : leftSpine l1 with
        | nil => simp [hls1] at this; omega
        | cons v0 vs => simp [hls1] at this ⊢; omega
      have hsub_tail : (leftSpine l1 ++ [b1]).tail = (leftSpine l1).tail ++ [b1] := by
        cases hls1 : leftSpine l1 with
        | nil => exact absurd ((leftSpine_eq_nil_iff l1).mp hls1) hl1_ne
        | cons v0 vs => rfl
      obtain ⟨hadj, hlen_adj⟩ := adjacentPairs_append_of_even (ys := [b1]) htail_len
      have hadj1 : adjacentPairs [b1] = [] := rfl
      have hpairs : (adjacentPairs (leftSpine l1 ++ [b1]).tail).take h = popCascadePairs l1 := by
        rw [hsub_tail, hadj, hadj1, List.append_nil]
        exact List.take_of_length_le (by omega)
      have hpop_pairs : popCascadePairs (.node b1 l1 r1) = popCascadePairs l1 := by
        simp only [popCascadePairs, leftSpine]
        rw [hsub_tail, hadj, hadj1, List.append_nil]
      have hlt_b1 : ∀ p ∈ popCascadePairs l1, p.2 < b1 := fun p hp =>
        lt_of_IsBST_left l1 b1 r1 hBST
          (mem_leftSpine_mem (List.mem_of_mem_tail (mem_adjacentPairs_snd hp)))
      have hspH : spliceMin (.node b1 l1 r1) = .node b1 (spliceMin l1) r1 := by
        cases l1 with
        | nil => exact absurd rfl hl1_ne
        | node lk ll lr => rfl
      refine ⟨h, hk_odd, hl1_ne, hpairs, hlt_b1, ?_⟩
      rw [popCascade, hpop_pairs, hspH, foldl_rotateRightEdge_node_lt _ b1 (spliceMin l1) r1 hlt_b1]
      rfl
    · right
      cases l1 with
      | nil => exact absurd rfl hl1_ne
      | node vTop aTop rTop =>
        have ha_len : (leftSpine aTop).length = 2 * h + 1 := by
          have : (leftSpine (.node vTop aTop rTop)).length = k := rfl
          simp [leftSpine] at this; omega
        have ha_ne : aTop ≠ .nil := fun ha => by simp [ha, leftSpine] at ha_len
        have ha_tail_len : (leftSpine aTop).tail.length = 2 * h := by
          cases hlsa : leftSpine aTop with
          | nil => simp [hlsa] at ha_len
          | cons v0 vs => simp [hlsa] at ha_len ⊢; omega
        have hsub_tail : (leftSpine (.node vTop aTop rTop) ++ [b1]).tail =
            (leftSpine aTop).tail ++ [vTop, b1] := by
          simp only [leftSpine, List.append_assoc, List.singleton_append]
          cases hlsa : leftSpine aTop with
          | nil => exact absurd ((leftSpine_eq_nil_iff aTop).mp hlsa) ha_ne
          | cons v0 vs => rfl
        obtain ⟨hadj2, hlen_a⟩ := adjacentPairs_append_of_even (ys := [vTop, b1]) ha_tail_len
        have hadj_vb : adjacentPairs [vTop, b1] = [(vTop, b1)] := rfl
        have hpairs :
            (adjacentPairs (leftSpine (.node vTop aTop rTop) ++ [b1]).tail).take h =
              popCascadePairs aTop := by
          rw [hsub_tail, hadj2, hadj_vb, popCascadePairs]
          rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        have hpop_pairs : popCascadePairs (.node b1 (.node vTop aTop rTop) r1) =
            popCascadePairs aTop ++ [(vTop, b1)] := by
          simp only [popCascadePairs]
          change adjacentPairs (leftSpine (.node vTop aTop rTop) ++ [b1]).tail = _
          rw [hsub_tail, hadj2, hadj_vb]
        have hl1_bst : (BinaryTree.node vTop aTop rTop).IsBST := IsBST_left_of_IsBST hBST
        have hvTop_lt_b1 : vTop < b1 := lt_of_IsBST_left _ b1 r1 hBST .here
        have hlt_vTop : ∀ p ∈ popCascadePairs aTop, p.2 < vTop := fun p hp =>
          lt_of_IsBST_left aTop vTop rTop hl1_bst
            (mem_leftSpine_mem (List.mem_of_mem_tail (mem_adjacentPairs_snd hp)))
        have hlt_b1 : ∀ p ∈ popCascadePairs aTop, p.2 < b1 :=
          fun p hp => lt_trans (hlt_vTop p hp) hvTop_lt_b1
        have hspH : spliceMin (.node b1 (.node vTop aTop rTop) r1) =
            .node b1 (.node vTop (spliceMin aTop) rTop) r1 := by
          cases aTop with
          | nil => exact absurd rfl ha_ne
          | node ak al ar => rfl
        refine ⟨h, vTop, aTop, rTop, rfl, hk_even, ha_len, ha_ne, hpairs, hlt_vTop, hlt_b1, ?_⟩
        rw [popCascade, hpop_pairs, hspH, List.foldl_append,
          foldl_rotateRightEdge_node_lt _ b1 _ r1 hlt_b1,
          foldl_rotateRightEdge_node_lt _ vTop (spliceMin aTop) rTop hlt_vTop]
        simp [popCascade, rotateRightEdge]

/-- Forward single-step theorem: any valid `OneSidedOp` on BST `H` maps via `spineFoldOp` to a
valid `FoldedOp` on `spineFoldTree H` that commutes with `step`. -/
theorem spineFold_step_comm {P : ℕ} {H : BinaryTree ℕ} (hBST : H.IsBST)
    {uop : OneSidedOp} (hValid : uop.Valid P H) :
    (uop.step H).IsBST ∧
    (spineFoldOp H uop).Valid P (spineFoldTree H) ∧
    (spineFoldOp H uop).step (spineFoldTree H) = spineFoldTree (uop.step H) := by
  have hFoldEq : (spineFoldTree H).1 = .nil ↔ (spineFoldTree H).2 = none :=
    (spineFoldTree_fst_eq_nil_iff H).trans (spineFoldTree_snd_eq_none_iff H).symm
  have hFoldB1 : ∀ b, (spineFoldTree H).2 = some b → b ∈ leftSpine (spineFoldTree H).1 := by
    cases H with
    | nil => simp [spineFoldTree]
    | node b1 l1 r1 =>
      simp [spineFoldTree, rightSpineFrames, leftSpine_spineFoldGo]
  cases uop with
  | push w =>
    obtain ⟨hw1, hwP, hwlt⟩ := hValid
    have hNextBST : (SplayTree.push H w).IsBST := isBST_push hBST hwlt
    refine ⟨hNextBST, ?_, ?_⟩
    · refine ⟨hw1, hwP, fun k hk => hwlt k (mem_spineFoldTree_iff.mp hk), hFoldEq, hFoldB1⟩
    · cases H with
      | nil => rfl
      | node b1 l1 r1 =>
        dsimp only [spineFoldOp, FoldedOp.step, spineFoldTree, rightSpineFrames,
          OneSidedOp.step, SplayTree.push]
        have hord : (b1 :: (rightSpineFrames r1).map Prod.fst).Pairwise (· < ·) := by
          rw [map_fst_rightSpineFrames]
          exact rightSpine_pairwise hBST
        rw [modifyLeftAt_spineFoldGo_eq b1 l1 (rightSpineFrames r1) _ hord]
        rfl
  | pop s =>
    obtain ⟨hne, hmin⟩ := hValid
    have hNextBST : (popCascade H).IsBST := isBST_popCascade hBST
    cases H with
    | nil => exact absurd rfl hne
    | node b1 l1 r1 =>
      refine ⟨hNextBST, ?_, ?_⟩
      · refine ⟨b1, (spineFoldTree_fst_eq_nil_iff _).not.mpr (by simp), ?_, rfl,
          hFoldB1 b1 rfl⟩
        rw [minKey?_spineFoldTree]; exact hmin
      · have hb1_not_mem : b1 ∉ leftSpine l1 := by
          intro hmem
          exact absurd (lt_of_IsBST_left l1 b1 r1 hBST (mem_leftSpine_mem hmem)) (lt_irrefl b1)
        have hord : (b1 :: (rightSpineFrames r1).map Prod.fst).Pairwise (· < ·) := by
          rw [map_fst_rightSpineFrames]
          exact rightSpine_pairwise hBST
        have hls : leftSpine (spineFoldGo b1 l1 (rightSpineFrames r1)) =
            leftSpine l1 ++ (b1 :: rightSpine r1) := by
          rw [leftSpine_spineFoldGo, map_fst_rightSpineFrames]
        have hsub : takeThrough (leftSpine (spineFoldGo b1 l1 (rightSpineFrames r1))) b1 =
            leftSpine l1 ++ [b1] := by
          rw [hls]
          exact takeThrough_append_of_not_mem hb1_not_mem
        dsimp only [spineFoldOp, OneSidedOp.step, FoldedOp.step, spineFoldTree, rightSpineFrames]
        rw [hsub]
        have hk_eq : (leftSpine l1 ++ [b1]).length - 1 = (leftSpine l1).length := by simp
        rw [hk_eq]
        rcases popCascade_node_cases hBST with
          ⟨rfl, hpop⟩ | ⟨h, hk_odd, hl1_ne, hpairs, hlt_b1, hpop⟩ |
          ⟨h, vTop, aTop, rTop, rfl, hk_even, ha_len, ha_ne, hpairs, hlt_vTop, hlt_b1, hpop⟩
        · simp only [leftSpine, List.length_nil, ite_true]
          rw [hpop]
          cases r1 with
          | nil => simp [rightSpineFrames, spineFoldGo, spliceMin]
          | node b2 l2 r2 =>
            have hsp : spliceMin (spineFoldGo b1 .nil (rightSpineFrames (.node b2 l2 r2))) =
                spineFoldGo b2 l2 (rightSpineFrames r2) := by
              change spliceMin (spineFoldGo b2 (.node b1 .nil l2) (rightSpineFrames r2)) = _
              rw [spliceMin_spineFoldGo b2 (.node b1 .nil l2) _ (by simp)]
              rfl
            refine Prod.ext hsp ?_
            have hsp_ne :
                spliceMin (spineFoldGo b1 .nil (rightSpineFrames (.node b2 l2 r2))) ≠ .nil := by
              rw [hsp]
              exact spineFoldGo_ne_nil b2 l2 _
            simp only [hsp_ne, ite_false]
            rw [leftSpine_spineFoldGo]
            simp only [rightSpineFrames, List.map_cons, map_fst_rightSpineFrames]
            exact nextOnSpine_append_of_not_mem (xs := []) (by simp)
        · have hk_ne0 : (leftSpine l1).length ≠ 0 := by omega
          have hh_eq : ((leftSpine l1).length - 1) / 2 = h := by omega
          have hnot_even : (leftSpine l1).length ≠ 2 * h + 2 := by omega
          simp only [hk_ne0, ite_false, hh_eq, hnot_even]
          rw [hpairs, spliceMin_spineFoldGo b1 l1 _ hl1_ne,
            foldl_rotateRightEdge_spineFoldGo_lt _ b1 (spliceMin l1) _ hord hlt_b1, hpop]
          rfl
        · have hk_ne0 : (leftSpine (.node vTop aTop rTop)).length ≠ 0 := by omega
          have hh_eq : ((leftSpine (.node vTop aTop rTop)).length - 1) / 2 = h := by omega
          have hspL1 : spliceMin (.node vTop aTop rTop) = .node vTop (spliceMin aTop) rTop := by
            cases aTop with
            | nil => exact absurd rfl ha_ne
            | node ak al ar => rfl
          have hidx : (leftSpine (.node vTop aTop rTop) ++ [b1])[2 * h + 1]? = some vTop := by
            simp only [leftSpine, List.append_assoc, List.singleton_append]
            rw [List.getElem?_append_right (by omega)]
            simp [ha_len]
          simp only [hk_ne0, ite_false]
          rw [hh_eq]
          simp only [hk_even, ite_true]
          rw [hpairs, spliceMin_spineFoldGo b1 _ _ (by simp), hspL1,
            foldl_rotateRightEdge_spineFoldGo_lt _ b1 _ _ hord hlt_b1,
            foldl_rotateRightEdge_node_lt _ vTop (spliceMin aTop) rTop hlt_vTop, hidx, hpop]
          rfl
  | rightSpineLeftRot d =>
    obtain ⟨hd1, hdlen⟩ := hValid
    have hNextBST : (rotateLeftAtRightSpine1 H d).IsBST :=
      isBST_rotateLeftAtRightSpine1 hBST hd1
    cases H with
    | nil => simp [rightSpine] at hdlen
    | node b1 l1 r1 =>
      have hord : (b1 :: (rightSpineFrames r1).map Prod.fst).Pairwise (· < ·) := by
        rw [map_fst_rightSpineFrames]
        exact rightSpine_pairwise hBST
      by_cases hd_one : d ≤ 1
      · have hd_eq : d = 1 := by omega
        subst hd_eq
        cases r1 with
        | nil => simp [rightSpine] at hdlen
        | node b2 l2 r2 =>
          refine ⟨hNextBST, ?_, ?_⟩
          · dsimp only [spineFoldOp, FoldedOp.Valid, spineFoldTree, rightSpineFrames]
            refine ⟨b1, rfl, hFoldB1 b1 rfl, ?_⟩
            rw [rootKey?_spineFoldGo]
            simp only [List.map_cons, map_fst_rightSpineFrames]
            have hpw := rightSpine_pairwise hBST
            simp only [rightSpine, List.pairwise_cons] at hpw
            have hb1_lt : b1 < (b2 :: rightSpine r2).getLast (by simp) :=
              hpw.1 _ (List.getLast_mem (by simp))
            rw [List.getLast?_eq_some_getLast (by simp), List.getLast_cons (by simp)]
            intro heq
            injection heq with heq'
            omega
          · dsimp only [spineFoldOp, OneSidedOp.step, rotateLeftAtRightSpine1,
              BinaryTree.rotateLeft, FoldedOp.step, spineFoldTree, rightSpineFrames]
            have hb1_not_mem : b1 ∉ leftSpine l1 := by
              intro hmem
              exact absurd (lt_of_IsBST_left l1 b1 _ hBST (mem_leftSpine_mem hmem)) (lt_irrefl b1)
            have hnext : nextOnSpine
                (leftSpine (spineFoldGo b1 l1 ((b2, l2) :: rightSpineFrames r2))) b1 =
                some b2 := by
              rw [leftSpine_spineFoldGo]
              simp only [List.map_cons, map_fst_rightSpineFrames]
              exact nextOnSpine_append_of_not_mem hb1_not_mem
            rw [hnext]
            rfl
      · set j := d - 2
        have hd_eq : d = j + 2 := by omega
        rw [hd_eq] at hdlen hNextBST ⊢
        have hframes_len : j + 2 ≤ (rightSpineFrames r1).length := by
          have h1 : ((rightSpineFrames r1).map Prod.fst).length = (rightSpine r1).length :=
            congrArg List.length (map_fst_rightSpineFrames r1)
          simp only [List.length_map] at h1
          simp only [rightSpine, List.length_cons] at hdlen
          omega
        obtain ⟨u, v, hu, hv, hedge, hrot⟩ :=
          spineFoldGo_rotFramesAt j b1 l1 (rightSpineFrames r1) hord hframes_len
        have hrs_eq : b1 :: (rightSpineFrames r1).map Prod.fst = rightSpine (.node b1 l1 r1) := by
          rw [map_fst_rightSpineFrames]; rfl
        rw [hrs_eq] at hu hv hord
        have hpairs := List.pairwise_iff_getElem.mp hord
        have h_not_le : ¬ (j + 2 ≤ 1) := by omega
        have hop_eq : spineFoldOp (.node b1 l1 r1) (.rightSpineLeftRot (j + 2)) =
            .upperRot u v := by
          simp [spineFoldOp, h_not_le, hu, hv]
        refine ⟨hNextBST, ?_, ?_⟩
        · rw [hop_eq]
          set rs := rightSpine (.node b1 l1 r1)
          have hrs_ne : rs ≠ [] := by simp [rs, rightSpine]
          set rLast := rs.getLast hrs_ne
          obtain ⟨hj_lt, rfl⟩ := List.getElem?_eq_some_iff.mp hu
          obtain ⟨hj1_lt, rfl⟩ := List.getElem?_eq_some_iff.mp hv
          refine ⟨b1, rLast, rfl, ?_, hFoldB1 b1 rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [spineFoldTree, rightSpineFrames, rootKey?_spineFoldGo, hrs_eq]
            exact List.getLast?_eq_some_getLast hrs_ne
          · have hrs0 : rs[0]'(by simp [rs, rightSpine]) = b1 := rfl
            rw [← hrs0]
            rcases Nat.eq_zero_or_pos j with hj0 | hj_pos
            · simp [hj0]
            · exact le_of_lt (hpairs 0 j (by simp [rs, rightSpine]) hj_lt hj_pos)
          · exact hpairs j (j + 1) hj_lt hj1_lt (by omega)
          · have hlast_eq : rLast = rs[rs.length - 1]'(by simp [rs, rightSpine]) := by
              simp [rLast, List.getLast_eq_getElem]
            rw [hlast_eq]
            have hlt_idx : j + 1 < rs.length - 1 := by
              simp only [rs, rightSpine, List.length_cons] at hdlen ⊢
              omega
            exact hpairs (j + 1) (rs.length - 1) hj1_lt (by simp [rs, rightSpine]) hlt_idx
          · simp only [spineFoldTree, rightSpineFrames, leftSpine_spineFoldGo, hrs_eq]
            exact List.mem_append_right _ (List.getElem_mem hj_lt)
          · simp only [spineFoldTree, rightSpineFrames, leftSpine_spineFoldGo, hrs_eq]
            exact List.mem_append_right _ (List.getElem_mem hj1_lt)
          · simpa [spineFoldTree, rightSpineFrames] using hedge
        · rw [hop_eq]
          dsimp only [FoldedOp.step, OneSidedOp.step, spineFoldTree]
          have hrf := rightSpineFrames_rotateLeftAtRightSpine1 (.node b1 l1 r1) (j + 1)
          change (rotateRightEdge _ u v, some b1) =
            match rightSpineFrames (rotateLeftAtRightSpine1 (.node b1 l1 r1) (j + 2)) with
            | [] => (.nil, none)
            | (b1', l1') :: rest => (spineFoldGo b1' l1' rest, some b1')
          rw [hrf]
          dsimp only [rightSpineFrames]
          rw [rotFramesAt_cons_succ]
          dsimp only
          rw [hrot]

/-- Backward single-step lifting: any valid `FoldedOp` on `spineFoldTree H` comes from a valid
`OneSidedOp` on `H` via `spineFoldOp`. -/
theorem spineFold_lift_valid {P : ℕ} {H : BinaryTree ℕ} (hBST : H.IsBST)
    {fop : FoldedOp} (hValid : fop.Valid P (spineFoldTree H)) :
    ∃ uop : OneSidedOp, uop.Valid P H ∧ spineFoldOp H uop = fop := by
  cases fop with
  | push w =>
    obtain ⟨hw1, hwP, hwlt, _, _⟩ := hValid
    exact ⟨.push w, ⟨hw1, hwP, fun k hk => hwlt k (mem_spineFoldTree_iff.mpr hk)⟩, rfl⟩
  | pop s =>
    obtain ⟨_, hne, hmin, _, _⟩ := hValid
    rw [minKey?_spineFoldTree] at hmin
    exact ⟨.pop s, ⟨(spineFoldTree_fst_eq_nil_iff H).not.mp hne, hmin⟩, rfl⟩
  | shift =>
    obtain ⟨b, hb2, _, hroot⟩ := hValid
    cases H with
    | nil => simp [spineFoldTree] at hb2
    | node b1 l1 r1 =>
      simp only [spineFoldTree, rightSpineFrames, Option.some.injEq] at hb2
      subst hb2
      cases r1 with
      | nil =>
        simp [spineFoldTree, rightSpineFrames, spineFoldGo, rootKey?] at hroot
      | node b2 l2 r2 =>
        exact ⟨.rightSpineLeftRot 1, ⟨le_rfl, by simp [rightSpine]⟩, rfl⟩
  | upperRot u v =>
    obtain ⟨b, r, hb2, hroot, _, hbu, huv, hvr, _, hv_ls, hedge⟩ := hValid
    cases H with
    | nil => simp [spineFoldTree] at hb2
    | node b1 l1 r1 =>
      simp only [spineFoldTree, rightSpineFrames, Option.some.injEq] at hb2
      subst hb2
      have hord : (b1 :: (rightSpineFrames r1).map Prod.fst).Pairwise (· < ·) := by
        rw [map_fst_rightSpineFrames]
        exact rightSpine_pairwise hBST
      have hls : leftSpine (spineFoldTree (.node b1 l1 r1)).1 =
          leftSpine l1 ++ (b1 :: rightSpine r1) := by
        simp [spineFoldTree, rightSpineFrames, leftSpine_spineFoldGo, map_fst_rightSpineFrames]
      rw [hls] at hv_ls
      have hv_rs : v ∈ b1 :: rightSpine r1 := by
        rcases List.mem_append.mp hv_ls with hvl | hvr'
        · exfalso
          have := lt_of_IsBST_left l1 b1 r1 hBST (mem_leftSpine_mem hvl)
          omega
        · exact hvr'
      set rs := rightSpine (.node b1 l1 r1)
      change v ∈ rs at hv_rs
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hv_rs
      have hidx_pos : 0 < idx := by
        by_contra h0
        have h0' : idx = 0 := by omega
        subst h0'
        have : rs[0] = b1 := rfl
        omega
      have hr_eq : r = rs[rs.length - 1]'(by simp [rs, rightSpine]) := by
        simp only [spineFoldTree, rightSpineFrames, rootKey?_spineFoldGo,
          map_fst_rightSpineFrames] at hroot
        change (rs.getLast? = some r) at hroot
        rw [List.getLast?_eq_some_getLast (by simp [rs, rightSpine]),
          Option.some.injEq] at hroot
        rw [← hroot, List.getLast_eq_getElem]
      have hidx_last : idx < rs.length - 1 := by
        by_contra hge
        have heq : idx = rs.length - 1 := by omega
        have : v = r := by rw [← hidx_eq, hr_eq]; congr 1
        omega
      set d := idx + 1
      have hdlen : d + 1 ≤ rs.length := by omega
      have hrf_len : (rightSpineFrames r1).length + 1 = rs.length := by
        have h1 : ((rightSpineFrames r1).map Prod.fst).length = (rightSpine r1).length :=
          congrArg List.length (map_fst_rightSpineFrames r1)
        simp only [List.length_map] at h1
        simp [rs, rightSpine, h1]
      obtain ⟨u', v', hu', hv', hedge', _⟩ :=
        spineFoldGo_rotFramesAt (idx - 1) b1 l1 (rightSpineFrames r1) hord (by omega)
      have hrs_eq : b1 :: (rightSpineFrames r1).map Prod.fst = rs := by
        rw [map_fst_rightSpineFrames]; rfl
      rw [hrs_eq] at hu' hv'
      have hv'_eq : v' = v := by
        have h1 : idx - 1 + 1 = idx := by omega
        rw [h1, List.getElem?_eq_getElem hidx_lt, Option.some.injEq] at hv'
        exact hv'.symm.trans hidx_eq
      rw [hv'_eq] at hedge'
      have hu'_eq : u' = u := by
        obtain ⟨A, B, C, _, hsub⟩ := hedge
        obtain ⟨A', B', C', _, hsub'⟩ := hedge'
        dsimp only [spineFoldTree, rightSpineFrames] at hsub
        rw [hsub] at hsub'
        injection hsub' with _ hl_eq _
        injection hl_eq with hk_eq _ _
        exact hk_eq.symm
      rw [hu'_eq] at hu'
      refine ⟨.rightSpineLeftRot d, ⟨by omega, hdlen⟩, ?_⟩
      have hd_not_le : ¬ (d ≤ 1) := by omega
      have hd_sub2 : d - 2 = idx - 1 := by omega
      have hd_sub1 : d - 1 = idx := by omega
      have hv_some : rs[idx]? = some v := by
        rw [List.getElem?_eq_getElem hidx_lt, hidx_eq]
      dsimp only [spineFoldOp]
      simp only [hd_not_le, ite_false]
      change (match rs[d - 2]?, rs[d - 1]? with
        | some u0, some v0 => FoldedOp.upperRot u0 v0
        | _, _ => FoldedOp.shift) = FoldedOp.upperRot u v
      rw [hd_sub2, hd_sub1, hu', hv_some]

/-! ## Section 3: Multi-Step Trajectory Lifting & Window `[τ_start, τ_end]` -/

lemma spineFoldOpList_eq_cons (t : BinaryTree ℕ) (op : OneSidedOp) (rest : List OneSidedOp) :
    spineFoldOpList t (op :: rest) = spineFoldOp t op :: spineFoldOpList (op.step t) rest := by
  cases op <;> rfl

theorem spineFoldOpList_valid_and_foldl {P : ℕ} {H : BinaryTree ℕ} (hBST : H.IsBST)
    {uops : List OneSidedOp} (hValid : ValidOneSidedOps P H uops) :
    (uops.foldl OneSidedOp.step H).IsBST ∧
    ValidFoldedOps P (spineFoldTree H) (spineFoldOpList H uops) ∧
    (spineFoldOpList H uops).foldl FoldedOp.step (spineFoldTree H) =
      spineFoldTree (uops.foldl OneSidedOp.step H) := by
  induction uops generalizing H with
  | nil => exact ⟨hBST, trivial, rfl⟩
  | cons uop rest ih =>
    obtain ⟨hv1, hvRest⟩ := hValid
    obtain ⟨hNextBST, hfValid, hfStep⟩ := spineFold_step_comm hBST hv1
    obtain ⟨hEndBST, hfRestValid, hfRestFold⟩ := ih hNextBST hvRest
    rw [spineFoldOpList_eq_cons]
    refine ⟨hEndBST, ⟨hfValid, ?_⟩, ?_⟩
    · rw [hfStep]; exact hfRestValid
    · rw [List.foldl_cons, hfStep]; exact hfRestFold

theorem lift_validFoldedOps {P : ℕ} {H : BinaryTree ℕ} (hBST : H.IsBST)
    {fops : List FoldedOp} (hValid : ValidFoldedOps P (spineFoldTree H) fops) :
    ∃ uops : List OneSidedOp, ValidOneSidedOps P H uops ∧ spineFoldOpList H uops = fops := by
  induction fops generalizing H with
  | nil => exact ⟨[], trivial, rfl⟩
  | cons fop rest ih =>
    obtain ⟨hf1, hfRest⟩ := hValid
    obtain ⟨uop, hu1, huEq⟩ := spineFold_lift_valid hBST hf1
    obtain ⟨hNextBST, _, hfStep⟩ := spineFold_step_comm hBST hu1
    rw [← huEq, hfStep] at hfRest
    obtain ⟨urest, huRest, huRestEq⟩ := ih hNextBST hfRest
    exact ⟨uop :: urest, ⟨hu1, huRest⟩, by rw [spineFoldOpList_eq_cons, huEq, huRestEq]⟩

def pushOpt : OneSidedOp → Option ℕ
  | .push w => some w
  | _ => none

def popOpt : OneSidedOp → Option ℕ
  | .pop s => some s
  | _ => none

def isRightSpineRot : OneSidedOp → Bool
  | .rightSpineLeftRot _ => true
  | _ => false

lemma spineFoldOpList_filterMap_push (t : BinaryTree ℕ) (uops : List OneSidedOp) :
    (spineFoldOpList t uops).filterMap (fun | .push w => some w | _ => none) =
      uops.filterMap pushOpt := by
  induction uops generalizing t with
  | nil => rfl
  | cons op rest ih =>
    rw [spineFoldOpList_eq_cons, List.filterMap_cons, List.filterMap_cons]
    cases op with
    | push w => simp [spineFoldOp, pushOpt, ih]
    | pop s => simp [spineFoldOp, pushOpt, ih]
    | rightSpineLeftRot d =>
      dsimp only [spineFoldOp, pushOpt]
      split_ifs
      · simp [ih]
      · rcases (rightSpine t)[d - 2]?, (rightSpine t)[d - 1]? with ⟨_ | u, _ | v⟩ <;> simp [ih]

lemma spineFoldOpList_filterMap_pop (t : BinaryTree ℕ) (uops : List OneSidedOp) :
    (spineFoldOpList t uops).filterMap (fun | .pop s => some s | _ => none) =
      uops.filterMap popOpt := by
  induction uops generalizing t with
  | nil => rfl
  | cons op rest ih =>
    rw [spineFoldOpList_eq_cons, List.filterMap_cons, List.filterMap_cons]
    cases op with
    | push w => simp [spineFoldOp, popOpt, ih]
    | pop s => simp [spineFoldOp, popOpt, ih]
    | rightSpineLeftRot d =>
      dsimp only [spineFoldOp, popOpt]
      split_ifs
      · simp [ih]
      · rcases (rightSpine t)[d - 2]?, (rightSpine t)[d - 1]? with ⟨_ | u, _ | v⟩ <;> simp [ih]

lemma spineFoldOpList_filter_upper (t : BinaryTree ℕ) (uops : List OneSidedOp) :
    ((spineFoldOpList t uops).filter
      (fun | .shift => true | .upperRot _ _ => true | _ => false)).length =
      (uops.filter isRightSpineRot).length := by
  induction uops generalizing t with
  | nil => rfl
  | cons op rest ih =>
    rw [spineFoldOpList_eq_cons, List.filter_cons, List.filter_cons]
    cases op with
    | push w => simp [spineFoldOp, isRightSpineRot, ih]
    | pop s => simp [spineFoldOp, isRightSpineRot, ih]
    | rightSpineLeftRot d =>
      dsimp only [spineFoldOp, isRightSpineRot]
      by_cases hd : d ≤ 1
      · simp [hd, ih]
      · simp only [hd, ite_false]
        rcases (rightSpine t)[d - 2]?, (rightSpine t)[d - 1]? with ⟨_ | u, _ | v⟩ <;>
          simp [ih]

lemma validOneSidedOps_append {P : ℕ} {t : BinaryTree ℕ} {ops₁ ops₂ : List OneSidedOp} :
    ValidOneSidedOps P t (ops₁ ++ ops₂) ↔
      ValidOneSidedOps P t ops₁ ∧ ValidOneSidedOps P (ops₁.foldl OneSidedOp.step t) ops₂ := by
  induction ops₁ generalizing t with
  | nil => simp [ValidOneSidedOps]
  | cons op rest ih =>
    simp [ValidOneSidedOps, ih (t := op.step t), and_assoc]

def uTree (init : BinaryTree ℕ) (ops : List OneSidedOp) (τ : ℕ) : BinaryTree ℕ :=
  (ops.take τ).foldl OneSidedOp.step init

lemma uTree_isBST {P : ℕ} {init : BinaryTree ℕ} (hInit : init.IsBST)
    {ops : List OneSidedOp} (hValid : ValidOneSidedOps P init ops) (τ : ℕ) :
    (uTree init ops τ).IsBST := by
  have hsplit : ops = ops.take τ ++ ops.drop τ := (List.take_append_drop τ ops).symm
  rw [hsplit, validOneSidedOps_append] at hValid
  exact (spineFoldOpList_valid_and_foldl hInit hValid.1).1

lemma uTree_step {init : BinaryTree ℕ} {ops : List OneSidedOp} {τ : ℕ} {op : OneSidedOp}
    (hop : ops[τ]? = some op) :
    uTree init ops (τ + 1) = op.step (uTree init ops τ) := by
  simp [uTree, List.take_add_one, hop]

lemma uTree_valid_at {P : ℕ} {init : BinaryTree ℕ} {ops : List OneSidedOp}
    (hValid : ValidOneSidedOps P init ops) {τ : ℕ} {op : OneSidedOp}
    (hop : ops[τ]? = some op) :
    op.Valid P (uTree init ops τ) := by
  obtain ⟨hτ, rfl⟩ := List.getElem?_eq_some_iff.mp hop
  have hsplit : ops = ops.take τ ++ (ops[τ] :: ops.drop (τ + 1)) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  rw [hsplit, validOneSidedOps_append] at hValid
  exact hValid.2.1

lemma exists_pop_of_mem_not_mem {P : ℕ} {init : BinaryTree ℕ} (hInit : init.IsBST)
    {ops : List OneSidedOp} (hValid : ValidOneSidedOps P init ops)
    {τ₁ τ₂ k : ℕ} (h12 : τ₁ ≤ τ₂) (h2 : τ₂ ≤ ops.length)
    (hmem1 : k ∈ uTree init ops τ₁) (hmem2 : k ∉ uTree init ops τ₂) :
    ∃ τ : ℕ, τ₁ ≤ τ ∧ τ < τ₂ ∧ ops[τ]? = some (.pop k) := by
  induction τ₂ with
  | zero =>
    have : τ₁ = 0 := by omega
    subst this
    exact absurd hmem1 hmem2
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le h12 with rfl | hlt
    · exact absurd hmem1 hmem2
    · by_cases hm : k ∈ uTree init ops m
      · have hm_lt : m < ops.length := by omega
        obtain ⟨op, hop⟩ : ∃ op, ops[m]? = some op :=
          ⟨ops[m], List.getElem?_eq_getElem hm_lt⟩
        rw [uTree_step hop] at hmem2
        have hT_bst : (uTree init ops m).IsBST := uTree_isBST hInit hValid m
        have hop_val : op.Valid P (uTree init ops m) := uTree_valid_at hValid hop
        cases op with
        | push w =>
          exact absurd (BinaryTree.Mem.right hm) hmem2
        | rightSpineLeftRot d =>
          have hk_eq : k ∈ rotateLeftAtRightSpine1 (uTree init ops m) d := by
            rw [mem_iff_mem_toKeyList, toKeyList_rotateLeftAtRightSpine1 _ hop_val.1,
              ← mem_iff_mem_toKeyList]
            exact hm
          exact absurd hk_eq hmem2
        | pop s =>
          obtain ⟨_, hmin⟩ := hop_val
          rw [minKey?_eq_head?_toKeyList] at hmin
          have hk_list : k ∈ (uTree init ops m).toKeyList := mem_iff_mem_toKeyList.mp hm
          have hk_not_tail : k ∉ (uTree init ops m).toKeyList.tail := by
            rw [← toKeyList_popCascade, ← mem_iff_mem_toKeyList]
            exact hmem2
          cases hkl : (uTree init ops m).toKeyList with
          | nil => simp [hkl] at hmin
          | cons a as =>
            rw [hkl, List.head?_cons, Option.some.injEq] at hmin
            subst hmin
            rw [hkl] at hk_list hk_not_tail
            rcases List.mem_cons.mp hk_list with rfl | htail
            · exact ⟨m, by omega, by omega, hop⟩
            · exact absurd htail hk_not_tail
      · obtain ⟨τ, hτ1, hτ2, hτop⟩ := ih (by omega) (by omega) hm
        exact ⟨τ, hτ1, by omega, hτop⟩

lemma exists_pop_idx {P s : ℕ} {ops : List OneSidedOp}
    (hPopSeq : ops.filterMap popOpt = List.range' 1 P)
    (hs1 : 1 ≤ s) (hsP : s ≤ P) :
    ∃ τ : ℕ, τ < ops.length ∧ ops[τ]? = some (.pop s) := by
  have hs_mem : s ∈ ops.filterMap popOpt := by
    rw [hPopSeq, List.mem_range']
    exact ⟨s - 1, by omega, by omega⟩
  obtain ⟨op, hop_mem, hop_eq⟩ := List.mem_filterMap.mp hs_mem
  have hop_pop : op = .pop s := by
    cases op <;> simp [popOpt] at hop_eq
    exact congrArg OneSidedOp.pop hop_eq
  subst hop_pop
  obtain ⟨τ, hτ_lt, hτ_eq⟩ := List.getElem_of_mem hop_mem
  exact ⟨τ, hτ_lt, by rw [List.getElem?_eq_getElem hτ_lt, hτ_eq]⟩

lemma pop_lt_of_idx_lt {P : ℕ} {ops : List OneSidedOp}
    (hPopSeq : ops.filterMap popOpt = List.range' 1 P)
    {τ₁ τ₂ s₁ s₂ : ℕ} (hlt : τ₁ < τ₂)
    (h1 : ops[τ₁]? = some (.pop s₁)) (h2 : ops[τ₂]? = some (.pop s₂)) :
    s₁ < s₂ := by
  obtain ⟨hτ1, heq1⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hτ2, heq2⟩ := List.getElem?_eq_some_iff.mp h2
  have hsplit1 : ops = ops.take τ₁ ++ (ops[τ₁] :: ops.drop (τ₁ + 1)) := by
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have hs2_drop : OneSidedOp.pop s₂ ∈ ops.drop (τ₁ + 1) := by
    have hidx : (ops.drop (τ₁ + 1))[τ₂ - (τ₁ + 1)]? = some (.pop s₂) := by
      rw [List.getElem?_drop, show τ₁ + 1 + (τ₂ - (τ₁ + 1)) = τ₂ by omega]
      exact h2
    exact List.mem_of_getElem? hidx
  have hs2_fm : s₂ ∈ (ops.drop (τ₁ + 1)).filterMap popOpt :=
    List.mem_filterMap.mpr ⟨.pop s₂, hs2_drop, rfl⟩
  have hpw : (ops.filterMap popOpt).Pairwise (· < ·) := by
    rw [hPopSeq]
    exact List.pairwise_lt_range'
  rw [hsplit1, List.filterMap_append, List.filterMap_cons, heq1] at hpw
  dsimp only [popOpt] at hpw
  rw [List.pairwise_append] at hpw
  rw [List.pairwise_cons] at hpw
  exact hpw.2.1.1 s₂ hs2_fm

lemma pop_idx_le_of_le {P : ℕ} {ops : List OneSidedOp}
    (hPopSeq : ops.filterMap popOpt = List.range' 1 P)
    {τ₁ τ₂ s₁ s₂ : ℕ} (hle : s₁ ≤ s₂)
    (h1 : ops[τ₁]? = some (.pop s₁)) (h2 : ops[τ₂]? = some (.pop s₂)) :
    τ₁ ≤ τ₂ := by
  by_contra hgt
  have := pop_lt_of_idx_lt hPopSeq (show τ₂ < τ₁ by omega) h2 h1
  omega

/-! ## Section 4: `trimAbove R`, Key Relabeling, Reverse-Spine Initialization, and `kL < 2 * Q` -/

lemma toKeyList_trimAbove {R : ℕ} {t : BinaryTree ℕ} (ht : t.IsBST) :
    (trimAbove R t).toKeyList = t.toKeyList.filter (· ≤ R) := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    have hl_bst := IsBST_left_of_IsBST ht
    have hr_bst := IsBST_right_of_IsBST ht
    simp only [trimAbove]
    split_ifs with hk
    · have hl_all : l.toKeyList.filter (· ≤ R) = l.toKeyList := by
        rw [List.filter_eq_self]
        intro x hx
        have hlt := lt_of_IsBST_left l k r ht (mem_iff_mem_toKeyList.mpr hx)
        simp; omega
      simp [ihr hr_bst, hl_all, hk]
    · have hr_empty : r.toKeyList.filter (· ≤ R) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have hgt := gt_of_IsBST_right l k r ht (mem_iff_mem_toKeyList.mpr hx)
        simp; omega
      simp [ihl hl_bst, hr_empty, hk]

lemma isBST_trimAbove {R : ℕ} {t : BinaryTree ℕ} (ht : t.IsBST) :
    (trimAbove R t).IsBST := by
  rw [IsBST_iff_toKeyList_sorted] at ht ⊢
  rw [toKeyList_trimAbove (IsBST_iff_toKeyList_sorted _ |>.mpr ht)]
  exact ht.filter _

lemma mem_trimAbove_iff {R : ℕ} {t : BinaryTree ℕ} (ht : t.IsBST) {x : ℕ} :
    x ∈ trimAbove R t ↔ x ∈ t ∧ x ≤ R := by
  rw [mem_iff_mem_toKeyList, toKeyList_trimAbove ht, List.mem_filter,
    decide_eq_true_eq, ← mem_iff_mem_toKeyList]

lemma trimAbove_eq_nil_of_gt {R : ℕ} {t : BinaryTree ℕ} (ht : t.IsBST)
    (hgt : ∀ x ∈ t, R < x) : trimAbove R t = .nil := by
  apply eq_nil_of_toKeyList_eq_nil
  rw [toKeyList_trimAbove ht, List.filter_eq_nil_iff]
  intro x hx
  have := hgt x (mem_iff_mem_toKeyList.mpr hx)
  simp; omega

lemma leftSpine_trimAbove {R : ℕ} {t : BinaryTree ℕ} (ht : t.IsBST) :
    leftSpine (trimAbove R t) = (leftSpine t).filter (· ≤ R) := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    simp only [trimAbove]
    split_ifs with hk
    · have hl_all : (leftSpine l).filter (· ≤ R) = leftSpine l := by
        rw [List.filter_eq_self]
        intro x hx
        have hlt := lt_of_IsBST_left l k r ht (mem_leftSpine_mem hx)
        simp; omega
      simp [leftSpine, hl_all, hk]
    · simp [leftSpine, ihl (IsBST_left_of_IsBST ht), hk]

lemma trimAbove_push {R w : ℕ} {t : BinaryTree ℕ} (ht : t.IsBST) (hw : ∀ k ∈ t, w < k) :
    trimAbove R (SplayTree.push t w) =
      if w ≤ R then SplayTree.push (trimAbove R t) w else trimAbove R t := by
  simp only [SplayTree.push, trimAbove]
  split_ifs with hwR
  · rfl
  · symm
    exact trimAbove_eq_nil_of_gt ht (fun k hk => lt_trans (by omega) (hw k hk))

lemma trimAbove_rotateLeftAtRightSpine1 {R d : ℕ} {t : BinaryTree ℕ}
    (ht : t.IsBST) (hd1 : 1 ≤ d) (hdlen : d + 1 ≤ (rightSpine t).length) :
    match (rightSpine t)[d]? with
    | some b =>
      if b ≤ R then
        d + 1 ≤ (rightSpine (trimAbove R t)).length ∧
        trimAbove R (rotateLeftAtRightSpine1 t d) = rotateLeftAtRightSpine1 (trimAbove R t) d
      else
        trimAbove R (rotateLeftAtRightSpine1 t d) = trimAbove R t
    | none => False := by
  induction d generalizing t with
  | zero => omega
  | succ d' ih =>
    cases d' with
    | zero =>
      rcases t with _ | ⟨b1, l1, _ | ⟨b2, l2, r2⟩⟩
      · simp [rightSpine] at hdlen
      · simp [rightSpine] at hdlen
      · have hb12 : b1 < b2 := gt_of_IsBST_right l1 b1 _ ht .here
        dsimp only [rightSpine, List.getElem?_cons_succ, List.getElem?_cons_zero]
        split_ifs with hb2R
        · have hb1R : b1 ≤ R := by omega
          refine ⟨by simp [trimAbove, hb1R, hb2R, rightSpine], ?_⟩
          simp [rotateLeftAtRightSpine1, BinaryTree.rotateLeft, trimAbove, hb1R, hb2R]
        · by_cases hb1R : b1 ≤ R
          · simp [rotateLeftAtRightSpine1, BinaryTree.rotateLeft, trimAbove, hb1R, hb2R]
          · simp [rotateLeftAtRightSpine1, BinaryTree.rotateLeft, trimAbove, hb1R, hb2R]
    | succ d'' =>
      cases t with
      | nil => simp [rightSpine] at hdlen
      | node b1 l1 r1 =>
        have hr_bst := IsBST_right_of_IsBST ht
        simp only [rightSpine, List.length_cons] at hdlen
        have hrec := ih hr_bst (by omega) (by omega)
        dsimp only [rightSpine, List.getElem?_cons_succ]
        rcases hget : (rightSpine r1)[d'' + 1]? with _ | b
        · rw [hget] at hrec; exact hrec
        · rw [hget] at hrec
          dsimp only at hrec ⊢
          split_ifs at hrec ⊢ with hbR
          · have hb_mem : b ∈ r1 := mem_rightSpine_mem (List.mem_of_getElem? hget)
            have hb1_lt : b1 < b := gt_of_IsBST_right l1 b1 r1 ht hb_mem
            have hb1R : b1 ≤ R := by omega
            refine ⟨?_, ?_⟩
            · simp only [trimAbove, hb1R, ite_true, rightSpine, List.length_cons]
              omega
            · simp [rotateLeftAtRightSpine1, trimAbove, hb1R, hrec.2]
          · by_cases hb1R : b1 ≤ R
            · simp [rotateLeftAtRightSpine1, trimAbove, hb1R, hrec]
            · simp [rotateLeftAtRightSpine1, trimAbove, hb1R]

lemma trimAbove_spliceMin {R s : ℕ} {t : BinaryTree ℕ}
    (ht : t.IsBST) (hne : t ≠ .nil) (hmin : t.minKey? = some s) (hs : s ≤ R) :
    trimAbove R (spliceMin t) = spliceMin (trimAbove R t) := by
  induction t with
  | nil => exact absurd rfl hne
  | node k l r ihl _ =>
    cases l with
    | nil =>
      simp only [BinaryTree.minKey?, Option.some.injEq] at hmin
      subst hmin
      simp [spliceMin, trimAbove, hs]
    | node lk ll lr =>
      have hl_bst := IsBST_left_of_IsBST ht
      have hl_min : (BinaryTree.node lk ll lr).minKey? = some s := by
        simp only [BinaryTree.minKey?] at hmin ⊢
        cases hll : ll.minKey? <;> simp [hll] at hmin ⊢ <;> exact hmin
      have hsp_node : spliceMin (.node k (.node lk ll lr) r) =
          .node k (spliceMin (.node lk ll lr)) r := rfl
      rw [hsp_node]
      by_cases hk : k ≤ R
      · change (if k ≤ R then .node k (spliceMin (.node lk ll lr)) (trimAbove R r)
          else trimAbove R (spliceMin (.node lk ll lr))) =
          spliceMin (if k ≤ R then .node k (.node lk ll lr) (trimAbove R r)
          else trimAbove R (.node lk ll lr))
        simp [hk, spliceMin]
      · change (if k ≤ R then .node k (spliceMin (.node lk ll lr)) (trimAbove R r)
          else trimAbove R (spliceMin (.node lk ll lr))) =
          spliceMin (if k ≤ R then .node k (.node lk ll lr) (trimAbove R r)
          else trimAbove R (.node lk ll lr))
        simp only [hk, ite_false]
        exact ihl hl_bst (by simp) hl_min

lemma trimAbove_rotateRightEdge {R : ℕ} (x p : ℕ) {t : BinaryTree ℕ} (ht : t.IsBST) :
    trimAbove R (rotateRightEdge t x p) =
      if p ≤ R then rotateRightEdge (trimAbove R t) x p else trimAbove R t := by
  induction t with
  | nil => simp [rotateRightEdge, trimAbove]
  | node k l r ihl ihr =>
    have hl_bst := IsBST_left_of_IsBST ht
    have hr_bst := IsBST_right_of_IsBST ht
    by_cases hpk : p < k
    · have hlhs : rotateRightEdge (.node k l r) x p = .node k (rotateRightEdge l x p) r := by
        simp [rotateRightEdge, hpk]
      rw [hlhs]
      by_cases hkR : k ≤ R
      · have hpR : p ≤ R := by omega
        simp [trimAbove, hkR, hpR, rotateRightEdge, hpk]
      · simp only [trimAbove, hkR, ite_false]
        exact ihl hl_bst
    · by_cases hkp : k < p
      · have hlhs : rotateRightEdge (.node k l r) x p = .node k l (rotateRightEdge r x p) := by
          simp [rotateRightEdge, hpk, hkp]
        rw [hlhs]
        by_cases hkR : k ≤ R
        · by_cases hpR : p ≤ R
          · simp [trimAbove, hkR, hpR, rotateRightEdge, hpk, hkp, ihr hr_bst]
          · simp [trimAbove, hkR, hpR, ihr hr_bst]
        · have hpR : ¬ (p ≤ R) := by omega
          simp [trimAbove, hkR, hpR]
      · have hpk_eq : p = k := le_antisymm (not_lt.mp hkp) (not_lt.mp hpk)
        subst hpk_eq
        cases l with
        | nil =>
          by_cases hkR : p ≤ R
          · simp [rotateRightEdge, trimAbove, hkR]
          · simp [rotateRightEdge, trimAbove, hkR]
        | node lx a b =>
          by_cases hlx : lx = x
          · subst hlx
            have hx_lt_p : lx < p := lt_of_IsBST_left _ p r ht .here
            have hlhs : rotateRightEdge (.node p (.node lx a b) r) lx p =
                .node lx a (.node p b r) := by
              simp [rotateRightEdge]
            rw [hlhs]
            by_cases hpR : p ≤ R
            · have hxR : lx ≤ R := by omega
              simp [trimAbove, hpR, hxR, rotateRightEdge]
            · by_cases hxR : lx ≤ R
              · simp [trimAbove, hpR, hxR]
              · simp [trimAbove, hpR, hxR]
          · have hlhs : rotateRightEdge (.node p (.node lx a b) r) x p =
                .node p (.node lx a b) r := by
              simp [rotateRightEdge, hlx]
            rw [hlhs]
            by_cases hpR : p ≤ R
            · simp [trimAbove, hpR, rotateRightEdge, hlx]
            · simp [trimAbove, hpR]

lemma popCascadePairs_trimAbove_split {R : ℕ} {t : BinaryTree ℕ} (ht : t.IsBST)
    (hne : trimAbove R t ≠ .nil) :
    ∃ extra : List (ℕ × ℕ),
      popCascadePairs t = popCascadePairs (trimAbove R t) ++ extra ∧
      (∀ p ∈ popCascadePairs (trimAbove R t), p.2 ≤ R) ∧
      (∀ p ∈ extra, R < p.2) := by
  have hpw : (leftSpine t).Pairwise (· < ·) := leftSpine_pairwise ht
  have hls_trim : leftSpine (trimAbove R t) = (leftSpine t).filter (· ≤ R) :=
    leftSpine_trimAbove ht
  have hsplit : ∃ gtList : List ℕ,
      leftSpine t = leftSpine (trimAbove R t) ++ gtList ∧
      (∀ z ∈ gtList, R < z) := by
    rw [hls_trim]
    generalize leftSpine t = ls at hpw ⊢
    clear hne hls_trim t ht
    induction ls with
    | nil => exact ⟨[], rfl, by simp⟩
    | cons a as ih =>
      rw [List.pairwise_cons] at hpw
      by_cases ha : a ≤ R
      · obtain ⟨gtList, h1, h2⟩ := ih hpw.2
        refine ⟨gtList, ?_, h2⟩
        simp only [List.filter_cons, ha, decide_true, ite_true, List.cons_append]
        exact congrArg (a :: ·) h1
      · have hemp : as.filter (· ≤ R) = [] := by
          rw [List.filter_eq_nil_iff]
          intro z hz
          have := hpw.1 z hz
          simp; omega
        refine ⟨a :: as, ?_, ?_⟩
        · simp [ha, hemp]
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hmem
          · omega
          · have := hpw.1 z hmem; omega
  obtain ⟨gtList, hls_eq, hgt⟩ := hsplit
  have hle_all : ∀ p ∈ popCascadePairs (trimAbove R t), p.2 ≤ R := by
    intro p hp
    have hmem := List.mem_of_mem_tail (mem_adjacentPairs_snd hp)
    rw [hls_trim, List.mem_filter, decide_eq_true_eq] at hmem
    exact hmem.2
  have hls_ne : leftSpine (trimAbove R t) ≠ [] := (leftSpine_eq_nil_iff _).not.mpr hne
  have htail_eq : (leftSpine t).tail = (leftSpine (trimAbove R t)).tail ++ gtList := by
    rw [hls_eq]
    cases h : leftSpine (trimAbove R t) with
    | nil => exact absurd h hls_ne
    | cons v0 vs => rfl
  set tailLe := (leftSpine (trimAbove R t)).tail
  set m := tailLe.length / 2
  rcases (show tailLe.length = 2 * m ∨ tailLe.length = 2 * m + 1 by omega) with heven | hodd
  · obtain ⟨hadj, _⟩ := adjacentPairs_append_of_even (ys := gtList) heven
    refine ⟨adjacentPairs gtList, ?_, hle_all, ?_⟩
    · simp only [popCascadePairs, htail_eq]
      exact hadj
    · intro p hp
      exact hgt p.2 (mem_adjacentPairs_snd hp)
  · have hdrop_ne : tailLe ≠ [] := by intro h; simp [h] at hodd
    have hinit_len : tailLe.dropLast.length = 2 * m := by
      rw [List.length_dropLast]; omega
    have htailLe_split : tailLe = tailLe.dropLast ++ [tailLe.getLast hdrop_ne] :=
      (List.dropLast_append_getLast hdrop_ne).symm
    obtain ⟨hadj_le, _⟩ :=
      adjacentPairs_append_of_even (ys := [tailLe.getLast hdrop_ne]) hinit_len
    have hpcp_trim : popCascadePairs (trimAbove R t) = adjacentPairs tailLe.dropLast := by
      simp only [popCascadePairs]
      change adjacentPairs tailLe = _
      rw [htailLe_split, hadj_le]
      simp [adjacentPairs]
    cases gtList with
    | nil =>
      refine ⟨[], ?_, hle_all, by simp⟩
      simp [popCascadePairs, htail_eq, tailLe]
    | cons g0 gs =>
      obtain ⟨hadj_full, _⟩ :=
        adjacentPairs_append_of_even (ys := tailLe.getLast hdrop_ne :: g0 :: gs) hinit_len
      refine ⟨(tailLe.getLast hdrop_ne, g0) :: adjacentPairs gs, ?_, hle_all, ?_⟩
      · simp only [popCascadePairs, htail_eq]
        calc adjacentPairs (tailLe ++ g0 :: gs)
          _ = adjacentPairs ((tailLe.dropLast ++ [tailLe.getLast hdrop_ne]) ++ g0 :: gs) :=
              congrArg (fun xs => adjacentPairs (xs ++ g0 :: gs)) htailLe_split
          _ = adjacentPairs (tailLe.dropLast ++ tailLe.getLast hdrop_ne :: g0 :: gs) := by
              simp [List.append_assoc]
          _ = adjacentPairs tailLe.dropLast ++
                (tailLe.getLast hdrop_ne, g0) :: adjacentPairs gs := hadj_full
          _ = popCascadePairs (trimAbove R t) ++
                (tailLe.getLast hdrop_ne, g0) :: adjacentPairs gs := by
              rw [hpcp_trim]
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hrest
        · exact hgt g0 (by simp)
        · exact hgt p.2 (List.mem_cons_of_mem g0 (mem_adjacentPairs_snd hrest))

lemma trimAbove_popCascade {R s : ℕ} {t : BinaryTree ℕ}
    (ht : t.IsBST) (hne : t ≠ .nil) (hmin : t.minKey? = some s) (hs : s ≤ R) :
    trimAbove R (popCascade t) = popCascade (trimAbove R t) := by
  have hs_in : s ∈ t := ((minKey?_eq_some_iff_of_isBST ht).mp hmin).1
  have htrim_ne : trimAbove R t ≠ .nil :=
    ne_nil_of_mem s ((mem_trimAbove_iff ht).mpr ⟨hs_in, hs⟩)
  obtain ⟨extra, hpairs_eq, hle, hgt⟩ := popCascadePairs_trimAbove_split ht htrim_ne
  rw [popCascade, hpairs_eq, List.foldl_append]
  have h1 : ∀ (ps : List (ℕ × ℕ)) (acc : BinaryTree ℕ),
      acc.IsBST → (∀ p ∈ ps, p.2 ≤ R) →
      trimAbove R (ps.foldl (fun a p => rotateRightEdge a p.1 p.2) acc) =
        ps.foldl (fun a p => rotateRightEdge a p.1 p.2) (trimAbove R acc) := by
    intro ps
    induction ps with
    | nil => intro acc _ _; rfl
    | cons p ps ih =>
      intro acc hacc hp_le
      have hpR : p.2 ≤ R := hp_le p (by simp)
      rw [List.foldl_cons, List.foldl_cons,
        ih _ (isBST_rotateRightEdge hacc p.1 p.2) (fun q hq => hp_le q (by simp [hq])),
        trimAbove_rotateRightEdge p.1 p.2 hacc]
      simp only [hpR, ite_true]
  have h2 : ∀ (ps : List (ℕ × ℕ)) (acc : BinaryTree ℕ),
      acc.IsBST → (∀ p ∈ ps, R < p.2) →
      trimAbove R (ps.foldl (fun a p => rotateRightEdge a p.1 p.2) acc) = trimAbove R acc := by
    intro ps
    induction ps with
    | nil => intro acc _ _; rfl
    | cons p ps ih =>
      intro acc hacc hp_gt
      have hp_not : ¬ (p.2 ≤ R) := not_le.mpr (hp_gt p (by simp))
      rw [List.foldl_cons,
        ih _ (isBST_rotateRightEdge hacc p.1 p.2) (fun q hq => hp_gt q (by simp [hq])),
        trimAbove_rotateRightEdge p.1 p.2 hacc]
      simp only [hp_not, ite_false]
  have hmid_bst : ((popCascadePairs (trimAbove R t)).foldl
      (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin t)).IsBST := by
    refine IsBST_of_toKeyList_eq (toKeyList_rotateRightEdge_foldl _ _) (isBST_spliceMin ht)
  rw [h2 extra _ hmid_bst hgt, h1 _ (spliceMin t) (isBST_spliceMin ht) hle,
    trimAbove_spliceMin ht hne hmin hs]
  rfl

/-- Key relabeling map `x ↦ x - (L - 1)` mapping `[L, R]` onto `[1, R - L + 1]`. -/
def shiftKey (L x : ℕ) : ℕ := x - (L - 1)

def relabelTree (f : ℕ → ℕ) : BinaryTree ℕ → BinaryTree ℕ
  | .nil => .nil
  | .node k l r => .node (f k) (relabelTree f l) (relabelTree f r)

lemma toKeyList_relabelTree (f : ℕ → ℕ) (t : BinaryTree ℕ) :
    (relabelTree f t).toKeyList = t.toKeyList.map f := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr => simp [relabelTree, ihl, ihr]

lemma leftSpine_relabelTree (f : ℕ → ℕ) (t : BinaryTree ℕ) :
    leftSpine (relabelTree f t) = (leftSpine t).map f := by
  induction t with
  | nil => rfl
  | node k l r ihl _ => simp [relabelTree, leftSpine, ihl]

lemma rightSpine_relabelTree (f : ℕ → ℕ) (t : BinaryTree ℕ) :
    rightSpine (relabelTree f t) = (rightSpine t).map f := by
  induction t with
  | nil => rfl
  | node k l r _ ihr => simp [relabelTree, rightSpine, ihr]

lemma minKey?_relabelTree (f : ℕ → ℕ) (t : BinaryTree ℕ) :
    (relabelTree f t).minKey? = t.minKey?.map f := by
  rw [minKey?_eq_head?_toKeyList, toKeyList_relabelTree, List.head?_map, ← minKey?_eq_head?_toKeyList]

lemma relabelTree_eq_nil_iff (f : ℕ → ℕ) (t : BinaryTree ℕ) :
    relabelTree f t = .nil ↔ t = .nil := by
  cases t <;> simp [relabelTree]

lemma spliceMin_relabelTree (f : ℕ → ℕ) (t : BinaryTree ℕ) :
    spliceMin (relabelTree f t) = relabelTree f (spliceMin t) := by
  induction t with
  | nil => rfl
  | node k l r ihl _ =>
    cases l with
    | nil => rfl
    | node lk ll lr =>
      exact congrArg (fun u => BinaryTree.node (f k) u (relabelTree f r)) ihl

lemma rotateLeftAtRightSpine1_relabelTree (f : ℕ → ℕ) (t : BinaryTree ℕ) (d : ℕ) :
    rotateLeftAtRightSpine1 (relabelTree f t) d = relabelTree f (rotateLeftAtRightSpine1 t d) := by
  induction d generalizing t with
  | zero => cases t <;> rfl
  | succ d' ih =>
    cases d' with
    | zero =>
      rcases t with _ | ⟨k, l, _ | ⟨rk, rl, rr⟩⟩ <;>
        simp [relabelTree, rotateLeftAtRightSpine1, BinaryTree.rotateLeft]
    | succ d'' =>
      cases t with
      | nil => rfl
      | node k l r => simp [relabelTree, rotateLeftAtRightSpine1, ih r]

lemma rotateRightEdge_relabelTree {L : ℕ} (t : BinaryTree ℕ) (x p : ℕ)
    (ht_ge : ∀ k ∈ t, L ≤ k) (hx : L ≤ x) (hp : L ≤ p) :
    rotateRightEdge (relabelTree (shiftKey L) t) (shiftKey L x) (shiftKey L p) =
      relabelTree (shiftKey L) (rotateRightEdge t x p) := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    have hk : L ≤ k := ht_ge k .here
    have hl_ge : ∀ z ∈ l, L ≤ z := fun z hz => ht_ge z (.left hz)
    have hr_ge : ∀ z ∈ r, L ≤ z := fun z hz => ht_ge z (.right hz)
    have hlt1 : (shiftKey L p < shiftKey L k) ↔ (p < k) := by simp [shiftKey]; omega
    have hlt2 : (shiftKey L k < shiftKey L p) ↔ (k < p) := by simp [shiftKey]; omega
    simp only [relabelTree, rotateRightEdge, hlt1, hlt2]
    split_ifs with h1 h2
    · simp [relabelTree, ihl hl_ge]
    · simp [relabelTree, ihr hr_ge]
    · cases l with
      | nil => rfl
      | node lx a b =>
        have hlx : L ≤ lx := hl_ge lx .here
        have heq : (shiftKey L lx = shiftKey L x) ↔ (lx = x) := by simp [shiftKey]; omega
        dsimp only [relabelTree]
        by_cases hlx_eq : lx = x <;> simp [relabelTree, heq, hlx_eq]

lemma adjacentPairs_map (f : α → β) (xs : List α) :
    adjacentPairs (xs.map f) = (adjacentPairs xs).map (fun p => (f p.1, f p.2)) := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b rest ih _ => simp [adjacentPairs, ih]

lemma isBST_relabelTree_shiftKey {L : ℕ} {t : BinaryTree ℕ}
    (ht : t.IsBST) (hge : ∀ k ∈ t, L ≤ k) :
    (relabelTree (shiftKey L) t).IsBST := by
  rw [IsBST_iff_toKeyList_sorted] at ht ⊢
  rw [toKeyList_relabelTree, List.pairwise_map]
  refine ht.imp_of_mem ?_
  intro a b ha hb hab
  have haL := hge a (mem_iff_mem_toKeyList.mpr ha)
  have hbL := hge b (mem_iff_mem_toKeyList.mpr hb)
  simp only [shiftKey]; omega

lemma popCascade_relabelTree_shiftKey {L : ℕ} {t : BinaryTree ℕ}
    (hge : ∀ k ∈ t, L ≤ k) :
    popCascade (relabelTree (shiftKey L) t) = relabelTree (shiftKey L) (popCascade t) := by
  have hpcp : popCascadePairs (relabelTree (shiftKey L) t) =
      (popCascadePairs t).map (fun p => (shiftKey L p.1, shiftKey L p.2)) := by
    simp only [popCascadePairs, leftSpine_relabelTree]
    rcases leftSpine t with _ | ⟨_, _⟩ <;> simp [adjacentPairs, adjacentPairs_map]
  rw [popCascade, hpcp, spliceMin_relabelTree, popCascade]
  have hpairs_ge : ∀ p ∈ popCascadePairs t, L ≤ p.1 ∧ L ≤ p.2 := by
    intro p hp
    exact ⟨hge p.1 (mem_leftSpine_mem (List.mem_of_mem_tail (mem_adjacentPairs_fst hp))),
      hge p.2 (mem_leftSpine_mem (List.mem_of_mem_tail (mem_adjacentPairs_snd hp)))⟩
  have hsp_ge : ∀ k ∈ spliceMin t, L ≤ k := by
    intro k hk
    rw [mem_iff_mem_toKeyList, toKeyList_spliceMin] at hk
    exact hge k (mem_iff_mem_toKeyList.mpr (List.mem_of_mem_tail hk))
  generalize popCascadePairs t = ps at hpairs_ge ⊢
  generalize spliceMin t = acc at hsp_ge ⊢
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨hp1, hp2⟩ := hpairs_ge p (by simp)
    have hacc' : ∀ k ∈ rotateRightEdge acc p.1 p.2, L ≤ k := by
      intro k hk
      rw [mem_iff_mem_toKeyList, toKeyList_rotateRightEdge, ← mem_iff_mem_toKeyList] at hk
      exact hsp_ge k hk
    simp only [List.map_cons, List.foldl_cons,
      rotateRightEdge_relabelTree acc p.1 p.2 hsp_ge hp1 hp2]
    exact ih (fun q hq => hpairs_ge q (by simp [hq])) (rotateRightEdge acc p.1 p.2) hacc'

/-- Reverse-spine initialization (Lemma 3.5(1)). -/
def buildBST : BinaryTree ℕ → List OneSidedOp
  | .nil => []
  | .node u .nil b => buildBST b ++ [.push u]
  | .node u (.node a al ar) b =>
    buildBST (.node a al (.node u ar b)) ++ [.rightSpineLeftRot 1]
termination_by t => (t.num_nodes, t.num_nodes - (rightSpine t).length)
decreasing_by
  · simp [rightSpine]; omega
  · have := rightSpine_length_le_num_nodes b
    simp [rightSpine]
    omega

theorem buildBST_spec {Q : ℕ} (t : BinaryTree ℕ) (ht : t.IsBST)
    (hk : ∀ x ∈ t, 1 ≤ x ∧ x ≤ Q) :
    ValidOneSidedOps Q .nil (buildBST t) ∧
    (buildBST t).foldl OneSidedOp.step .nil = t ∧
    (buildBST t).filterMap popOpt = [] := by
  induction t using buildBST.induct with
  | case1 =>
    simp [buildBST, ValidOneSidedOps]
  | case2 u b ih =>
    have hb_bst : b.IsBST := IsBST_right_of_IsBST ht
    have hb_k : ∀ x ∈ b, 1 ≤ x ∧ x ≤ Q := fun x hx => hk x (.right hx)
    obtain ⟨hv, hf, hp⟩ := ih hb_bst hb_k
    obtain ⟨hu1, huQ⟩ := hk u .here
    have hult : ∀ k ∈ b, u < k := fun k hkb => gt_of_IsBST_right .nil u b ht hkb
    simp only [buildBST]
    refine ⟨?_, ?_, ?_⟩
    · rw [validOneSidedOps_append, hf]
      exact ⟨hv, ⟨⟨hu1, huQ, hult⟩, trivial⟩⟩
    · simp [List.foldl_append, hf, OneSidedOp.step, SplayTree.push]
    · simp [List.filterMap_append, hp, popOpt]
  | case3 u a al ar b ih =>
    set t' : BinaryTree ℕ := .node a al (.node u ar b)
    have ht'_keys : t'.toKeyList = (BinaryTree.node u (.node a al ar) b).toKeyList := by
      simp [t', List.append_assoc]
    have ht'_bst : t'.IsBST := IsBST_of_toKeyList_eq ht'_keys ht
    have ht'_k : ∀ x ∈ t', 1 ≤ x ∧ x ≤ Q := by
      intro x hx
      rw [mem_iff_mem_toKeyList, ht'_keys, ← mem_iff_mem_toKeyList] at hx
      exact hk x hx
    obtain ⟨hv, hf, hp⟩ := ih ht'_bst ht'_k
    simp only [buildBST]
    refine ⟨?_, ?_, ?_⟩
    · rw [validOneSidedOps_append, hf]
      exact ⟨hv, ⟨⟨le_rfl, by simp [t', rightSpine]⟩, trivial⟩⟩
    · simp [List.foldl_append, hf, t', OneSidedOp.step, rotateLeftAtRightSpine1,
        BinaryTree.rotateLeft]
    · rw [List.filterMap_append, hp]; rfl

lemma num_nodes_balance {Q : ℕ} {t : BinaryTree ℕ} (ht : t.IsBST)
    {ops : List OneSidedOp} (hValid : ValidOneSidedOps Q t ops) :
    (ops.foldl OneSidedOp.step t).num_nodes + (ops.filterMap popOpt).length =
      t.num_nodes + (ops.filterMap pushOpt).length := by
  induction ops generalizing t with
  | nil => simp
  | cons op rest ih =>
    obtain ⟨hv1, hvRest⟩ := hValid
    obtain ⟨hNextBST, _, _⟩ := spineFold_step_comm ht hv1
    have hrec := ih hNextBST hvRest
    cases op with
    | push w =>
      simp only [List.foldl_cons, OneSidedOp.step, SplayTree.push, num_nodes_node,
        num_nodes_empty, List.filterMap_cons, popOpt, pushOpt, List.length_cons] at hrec ⊢
      omega
    | rightSpineLeftRot d =>
      have hnn : (rotateLeftAtRightSpine1 t d).num_nodes = t.num_nodes := by
        rw [num_nodes_eq_length_toKeyList, num_nodes_eq_length_toKeyList,
          toKeyList_rotateLeftAtRightSpine1 t hv1.1]
      simp only [List.foldl_cons, OneSidedOp.step, hnn, List.filterMap_cons,
        popOpt, pushOpt] at hrec ⊢
      omega
    | pop s =>
      have ht_pos : 1 ≤ t.num_nodes := by
        cases t with
        | nil => exact absurd rfl hv1.1
        | node k l r => simp; omega
      have hnn : (popCascade t).num_nodes = t.num_nodes - 1 := by
        rw [num_nodes_eq_length_toKeyList, toKeyList_popCascade, List.length_tail,
          ← num_nodes_eq_length_toKeyList]
      simp only [List.foldl_cons, OneSidedOp.step, hnn, List.filterMap_cons,
        popOpt, pushOpt, List.length_cons] at hrec ⊢
      omega

lemma rightSpine_rotateLeft_len {t : BinaryTree ℕ} {d : ℕ}
    (hd1 : 1 ≤ d) (hdlen : d + 1 ≤ (rightSpine t).length) :
    (rightSpine (rotateLeftAtRightSpine1 t d)).length + 1 = (rightSpine t).length := by
  induction d generalizing t with
  | zero => omega
  | succ d' ih =>
    cases d' with
    | zero =>
      rcases t with _ | ⟨b1, l1, _ | ⟨b2, l2, r2⟩⟩
      · simp [rightSpine] at hdlen
      · simp [rightSpine] at hdlen
      · simp [rotateLeftAtRightSpine1, BinaryTree.rotateLeft, rightSpine]
    | succ d'' =>
      cases t with
      | nil => simp [rightSpine] at hdlen
      | node k l r =>
        simp only [rightSpine, List.length_cons] at hdlen
        have hrec := ih (t := r) (by omega) (by omega)
        simp only [rotateLeftAtRightSpine1, rightSpine, List.length_cons]
        omega

lemma rightSpine_popCascade_le {t : BinaryTree ℕ} (ht : t.IsBST) (hne : t ≠ .nil) :
    (rightSpine (popCascade t)).length ≤ (rightSpine t).length + 1 := by
  cases t with
  | nil => exact absurd rfl hne
  | node b1 l1 r1 =>
    rcases popCascade_node_cases ht with
      ⟨rfl, hpop⟩ | ⟨_, _, _, _, _, hpop⟩ | ⟨_, vTop, aTop, rTop, _, _, _, _, _, _, _, hpop⟩
    · simp [hpop, rightSpine]; omega
    · simp [hpop, rightSpine]
    · simp [hpop, rightSpine]

lemma rightSpine_potential_along {Q : ℕ} {t : BinaryTree ℕ} (ht : t.IsBST)
    {ops : List OneSidedOp} (hValid : ValidOneSidedOps Q t ops) :
    (rightSpine (ops.foldl OneSidedOp.step t)).length + (ops.filter isRightSpineRot).length ≤
      (rightSpine t).length + (ops.filterMap pushOpt).length + (ops.filterMap popOpt).length := by
  induction ops generalizing t with
  | nil => simp
  | cons op rest ih =>
    obtain ⟨hv1, hvRest⟩ := hValid
    obtain ⟨hNextBST, _, _⟩ := spineFold_step_comm ht hv1
    have hrec := ih hNextBST hvRest
    cases op with
    | push w =>
      simp only [List.foldl_cons, OneSidedOp.step, SplayTree.push, rightSpine, List.length_cons,
        List.filter_cons, isRightSpineRot, Bool.false_eq_true, ite_false, List.filterMap_cons,
        pushOpt, popOpt] at hrec ⊢
      omega
    | rightSpineLeftRot d =>
      have hrs := rightSpine_rotateLeft_len hv1.1 hv1.2
      simp only [List.foldl_cons, OneSidedOp.step, List.filter_cons, isRightSpineRot, ite_true,
        List.length_cons, List.filterMap_cons, pushOpt, popOpt] at hrec ⊢
      omega
    | pop s =>
      have hrs := rightSpine_popCascade_le ht hv1.1
      simp only [List.foldl_cons, OneSidedOp.step, List.filter_cons, isRightSpineRot,
        Bool.false_eq_true, ite_false, List.filterMap_cons, pushOpt, popOpt,
        List.length_cons] at hrec ⊢
      omega

lemma kL_lt_two_mul {Q : ℕ} (hQ : 1 ≤ Q) {allOps : List OneSidedOp}
    (hValid : ValidOneSidedOps Q .nil allOps)
    (hEnd : allOps.foldl OneSidedOp.step .nil = .nil)
    (hPush : (allOps.filterMap pushOpt).length = Q)
    (hPop : (allOps.filterMap popOpt).length = Q) :
    (allOps.filter isRightSpineRot).length < 2 * Q := by
  have hne : allOps ≠ [] := by
    intro hemp; simp [hemp] at hPop; omega
  set initPart := allOps.dropLast
  set lastOp := allOps.getLast hne
  have hsplit : allOps = initPart ++ [lastOp] := (List.dropLast_append_getLast hne).symm
  have hValidSplit := validOneSidedOps_append.mp (hsplit ▸ hValid)
  set tPrev := initPart.foldl OneSidedOp.step .nil
  have htPrev_bst : tPrev.IsBST :=
    (spineFoldOpList_valid_and_foldl SplayDeque.Direct.isBSTNil hValidSplit.1).1
  have hlastValid : lastOp.Valid Q tPrev := hValidSplit.2.1
  have hlastEnd : lastOp.step tPrev = .nil := by
    simpa [hsplit, List.foldl_append, tPrev] using hEnd
  have hpot := rightSpine_potential_along SplayDeque.Direct.isBSTNil hValidSplit.1
  change (rightSpine tPrev).length + (initPart.filter isRightSpineRot).length ≤
    (rightSpine (.nil : BinaryTree ℕ)).length + (initPart.filterMap pushOpt).length +
      (initPart.filterMap popOpt).length at hpot
  cases hlast : lastOp with
  | push w =>
    rw [hlast] at hlastEnd
    simp [OneSidedOp.step, SplayTree.push] at hlastEnd
  | rightSpineLeftRot d =>
    rw [hlast] at hlastValid hlastEnd
    have h1 := hlastValid.1
    have h2 := hlastValid.2
    have h3 := rightSpine_length_le_num_nodes tPrev
    have hnn : (rotateLeftAtRightSpine1 tPrev d).num_nodes = tPrev.num_nodes := by
      rw [num_nodes_eq_length_toKeyList, num_nodes_eq_length_toKeyList,
        toKeyList_rotateLeftAtRightSpine1 tPrev h1]
    simp only [OneSidedOp.step] at hlastEnd
    rw [hlastEnd] at hnn
    simp at hnn
    omega
  | pop s =>
    rw [hlast] at hlastValid hsplit
    have hrs_pos : 1 ≤ (rightSpine tPrev).length := by
      rcases htPrev : tPrev with _ | ⟨k, l, r⟩
      · exact absurd htPrev hlastValid.1
      · simp [rightSpine]
    rw [hsplit] at hPush hPop ⊢
    simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      List.filter_append, List.filter_cons, List.filter_nil, pushOpt, popOpt,
      isRightSpineRot, Bool.false_eq_true, ite_false, List.append_nil,
      List.length_append, List.length_singleton] at hPush hPop ⊢
    simp only [rightSpine, List.length_nil] at hpot
    omega

/-! ## Section 5: Counting `InternalPopRot`s and Assembling `exists_interval_subproc` -/

lemma mem_foldedPopRotsAt_stepIdx {idx : ℕ} {st : BinaryTree ℕ × Option ℕ}
    {op : FoldedOp} {e : InternalPopRot} (he : e ∈ foldedPopRotsAt idx st op) :
    e.stepIdx = idx := by
  cases op with
  | pop s =>
    rcases st with ⟨T, _ | b⟩
    · simp [foldedPopRotsAt] at he
    · simp only [foldedPopRotsAt] at he
      obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp he
      split at hi
      · injection hi with hi'; subst hi'; rfl
      · simp at hi
  | _ => simp [foldedPopRotsAt] at he

lemma mem_collectFoldedPopRots_stepIdx {idx : ℕ} {st : BinaryTree ℕ × Option ℕ}
    {ops : List FoldedOp} {e : InternalPopRot} (he : e ∈ collectFoldedPopRots idx st ops) :
    idx ≤ e.stepIdx := by
  induction ops generalizing idx st with
  | nil => simp [collectFoldedPopRots] at he
  | cons op rest ih =>
    simp only [collectFoldedPopRots, List.mem_append] at he
    rcases he with h1 | h2
    · have := mem_foldedPopRotsAt_stepIdx h1; omega
    · have := ih h2; omega

lemma nodup_foldedPopRotsAt (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (op : FoldedOp) :
    (foldedPopRotsAt idx st op).Nodup := by
  cases op with
  | pop s =>
    rcases st with ⟨T, _ | b⟩
    · simp [foldedPopRotsAt]
    · simp only [foldedPopRotsAt]
      refine List.Nodup.filterMap ?_ List.nodup_range
      intro i₁ i₂ e h1 h2
      rw [Option.mem_def] at h1 h2
      have hj1 : e.j = i₁ + 1 := by
        split at h1
        · injection h1 with h1'; subst h1'; rfl
        · simp at h1
      have hj2 : e.j = i₂ + 1 := by
        split at h2
        · injection h2 with h2'; subst h2'; rfl
        · simp at h2
      omega
  | _ => simp [foldedPopRotsAt]

lemma nodup_collectFoldedPopRots (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (ops : List FoldedOp) :
    (collectFoldedPopRots idx st ops).Nodup := by
  induction ops generalizing idx st with
  | nil => simp [collectFoldedPopRots]
  | cons op rest ih =>
    simp only [collectFoldedPopRots]
    refine List.nodup_append.mpr ⟨nodup_foldedPopRotsAt idx st op,
      ih (idx + 1) (op.step st), ?_⟩
    intro e1 he1 e2 he2 heq
    subst heq
    have h1 := mem_foldedPopRotsAt_stepIdx he1
    have h2 := mem_collectFoldedPopRots_stepIdx he2
    omega

lemma collectFoldedPopRots_append (idx : ℕ) (st : BinaryTree ℕ × Option ℕ)
    (ops₁ ops₂ : List FoldedOp) :
    collectFoldedPopRots idx st (ops₁ ++ ops₂) =
      collectFoldedPopRots idx st ops₁ ++
        collectFoldedPopRots (idx + ops₁.length) (ops₁.foldl FoldedOp.step st) ops₂ := by
  induction ops₁ generalizing idx st with
  | nil => simp [collectFoldedPopRots]
  | cons op rest ih =>
    simp only [List.cons_append, collectFoldedPopRots, List.length_cons, List.foldl_cons,
      List.append_assoc, ih (idx + 1) (op.step st)]
    rw [show idx + 1 + rest.length = idx + (rest.length + 1) by omega]

lemma sorted_getElem_le_iff_lt_filter_length {R : ℕ} {ls : List ℕ}
    (hpw : ls.Pairwise (· < ·)) {p : ℕ} (hp : p < ls.length) :
    ls[p] ≤ R ↔ p < (ls.filter (· ≤ R)).length := by
  induction ls generalizing p with
  | nil => simp at hp
  | cons a as ih =>
    rw [List.pairwise_cons] at hpw
    by_cases ha : a ≤ R
    · simp only [List.filter_cons, ha, decide_true, ite_true, List.length_cons]
      cases p with
      | zero => simp [ha]
      | succ p' =>
        have hp' : p' < as.length := by simp at hp; omega
        rw [List.getElem_cons_succ, ih hpw.2 hp']
        omega
    · have hemp : as.filter (· ≤ R) = [] := by
        rw [List.filter_eq_nil_iff]
        intro z hz
        have := hpw.1 z hz
        simp; omega
      simp only [List.filter_cons, ha, decide_false, Bool.false_eq_true, ite_false, hemp,
        List.length_nil, Nat.not_lt_zero, iff_false]
      cases p with
      | zero => simp [ha]
      | succ p' =>
        have hp' : p' < as.length := by simp at hp; omega
        rw [List.getElem_cons_succ]
        have := hpw.1 (as[p']'hp') (List.getElem_mem hp')
        omega

lemma length_filter_lt_range {h h' : ℕ} (hle : h' ≤ h) :
    ((List.range h).filter (fun i => decide (i < h'))).length = h' := by
  induction h with
  | zero =>
    have : h' = 0 := by omega
    subst this; simp
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · rw [List.filter_eq_self.mpr]
      · exact List.length_range
      · intro i hi
        simp [List.mem_range.mp hi]
    · rw [List.range_succ, List.filter_append, List.filter_singleton]
      have hn : ¬ (n < h') := by omega
      simp [hn, ih (by omega)]

lemma attach_map_val (xs : List α) : xs.attach.map Subtype.val = xs :=
  List.attach_map_subtype_val xs

lemma filterMap_eq_attach_map {α β : Type*} (xs : List α) (f : α → Option β)
    (g : {x // x ∈ xs} → β)
    (hfg : ∀ x : {x // x ∈ xs}, f x.1 = some (g x)) :
    xs.filterMap f = xs.attach.map g := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [List.filterMap_cons, hfg ⟨a, List.mem_cons_self⟩, List.attach_cons, List.map_cons,
      List.map_map]
    exact congrArg _ (ih (fun x => g ⟨x.1, List.mem_cons_of_mem a x.2⟩)
      (fun x => hfg ⟨x.1, List.mem_cons_of_mem a x.2⟩))

lemma foldedPopRotsAt_spineFold_eq {idx s : ℕ} {H : BinaryTree ℕ}
    (hBST : H.IsBST) (hne : H ≠ .nil) :
    let ls := leftSpine H
    let h := (ls.length - 2) / 2
    foldedPopRotsAt idx (spineFoldTree H) (.pop s) =
      (List.range h).attach.map (fun ⟨i, hi⟩ =>
        have hi_lt : i < h := List.mem_range.mp hi
        { stepIdx := idx
          s := s
          j := i + 1
          h := h
          x := ls[2 * (i + 1) - 1]'(by omega)
          y := ls[2 * (i + 1)]'(by omega)
          z := ls[2 * (i + 1) + 1]'(by omega) }) := by
  cases H with
  | nil => exact absurd rfl hne
  | node b1 l1 r1 =>
    have hb1_not_mem : b1 ∉ leftSpine l1 := by
      intro hmem
      exact absurd (lt_of_IsBST_left l1 b1 r1 hBST (mem_leftSpine_mem hmem)) (lt_irrefl b1)
    have hsub : takeThrough (leftSpine (spineFoldGo b1 l1 (rightSpineFrames r1))) b1 =
        leftSpine (.node b1 l1 r1) := by
      rw [leftSpine_spineFoldGo, map_fst_rightSpineFrames]
      exact takeThrough_append_of_not_mem hb1_not_mem
    dsimp only [foldedPopRotsAt, spineFoldTree, rightSpineFrames]
    rw [hsub]
    set ls := leftSpine (.node b1 l1 r1)
    have hh_eq : (ls.length - 1 - 1) / 2 = (ls.length - 2) / 2 := by omega
    rw [hh_eq]
    set h := (ls.length - 2) / 2
    refine filterMap_eq_attach_map (List.range h) _ _ ?_
    rintro ⟨i, hi⟩
    have hi_lt : i < h := List.mem_range.mp hi
    have h1 : 2 * (i + 1) - 1 < ls.length := by omega
    have h2 : 2 * (i + 1) < ls.length := by omega
    have h3 : 2 * (i + 1) + 1 < ls.length := by omega
    dsimp only [ls] at h1 h2 h3
    rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
      List.getElem?_eq_getElem h3]

lemma foldedPopRotsAt_spineFold_length {idx s : ℕ} {H : BinaryTree ℕ}
    (hBST : H.IsBST) (hne : H ≠ .nil) :
    (foldedPopRotsAt idx (spineFoldTree H) (.pop s)).length =
      ((leftSpine H).length - 2) / 2 := by
  rw [foldedPopRotsAt_spineFold_eq hBST hne]
  simp

lemma foldedPopRotsAt_filter_length {L R idx s : ℕ} {H : BinaryTree ℕ}
    (hBST : H.IsBST) (hne : H ≠ .nil) (hmin : H.minKey? = some s) :
    let pred := fun (e : InternalPopRot) => decide (L ≤ e.s ∧ e.z ≤ R)
    ((foldedPopRotsAt idx (spineFoldTree H) (.pop s)).filter pred).length =
      if L ≤ s ∧ s ≤ R then ((leftSpine (trimAbove R H)).length - 2) / 2 else 0 := by
  intro pred
  rw [foldedPopRotsAt_spineFold_eq hBST hne]
  set ls := leftSpine H
  set h := (ls.length - 2) / 2
  set mkRot : {i // i ∈ List.range h} → InternalPopRot := fun ⟨i, hi⟩ =>
    have hi_lt : i < h := List.mem_range.mp hi
    { stepIdx := idx
      s := s
      j := i + 1
      h := h
      x := ls[2 * (i + 1) - 1]'(by omega)
      y := ls[2 * (i + 1)]'(by omega)
      z := ls[2 * (i + 1) + 1]'(by omega) }
  change (((List.range h).attach.map mkRot).filter pred).length = _
  by_cases hs : L ≤ s ∧ s ≤ R
  · simp only [hs.1, hs.2, and_self, ite_true]
    have hls_pw : ls.Pairwise (· < ·) := leftSpine_pairwise hBST
    have hls_trim : leftSpine (trimAbove R H) = ls.filter (· ≤ R) := leftSpine_trimAbove hBST
    set m := (leftSpine (trimAbove R H)).length
    have hm_le : m ≤ ls.length := by
      dsimp only [m]
      rw [hls_trim]
      exact List.length_filter_le _ _
    have hh'_le : (m - 2) / 2 ≤ h := by omega
    rw [List.filter_map]
    have hcond : ∀ x : {i // i ∈ List.range h},
        (pred ∘ mkRot) x = decide (x.1 < (m - 2) / 2) := by
      rintro ⟨i, hi⟩
      have hi_lt : i < h := List.mem_range.mp hi
      have h3 : 2 * (i + 1) + 1 < ls.length := by omega
      have hsort := sorted_getElem_le_iff_lt_filter_length (R := R) hls_pw h3
      rw [← hls_trim] at hsort
      change decide (L ≤ s ∧ ls[2 * (i + 1) + 1] ≤ R) = decide (i < (m - 2) / 2)
      simp only [hs.1, true_and, decide_eq_decide]
      rw [hsort]
      change 2 * (i + 1) + 1 < m ↔ i < (m - 2) / 2
      omega
    have hfilt_eq :
        ((List.range h).attach.filter (pred ∘ mkRot)).map Subtype.val =
        (List.range h).filter (fun i => decide (i < (m - 2) / 2)) := by
      have h1 : (List.range h).attach.filter (pred ∘ mkRot) =
          (List.range h).attach.filter ((fun i => decide (i < (m - 2) / 2)) ∘ Subtype.val) :=
        List.filter_congr fun x _ => hcond x
      rw [h1, ← List.filter_map, attach_map_val]
    have hlen_eq :
        (((List.range h).attach.filter (pred ∘ mkRot)).map Subtype.val).length =
        ((List.range h).filter (fun i => decide (i < (m - 2) / 2))).length :=
      congrArg List.length hfilt_eq
    simp only [List.length_map] at hlen_eq ⊢
    rw [hlen_eq, length_filter_lt_range hh'_le]
  · simp only [hs, ite_false, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro e he
    obtain ⟨⟨i, hi⟩, _, rfl⟩ := List.mem_map.mp he
    have hi_lt : i < h := List.mem_range.mp hi
    have h3 : 2 * (i + 1) + 1 < ls.length := by omega
    change ¬ (decide (L ≤ s ∧ ls[2 * (i + 1) + 1] ≤ R) = true)
    rw [decide_eq_true_eq]
    rintro ⟨hLs, hzR⟩
    have hsR : R < s := by omega
    have hz_mem : ls[2 * (i + 1) + 1] ∈ H :=
      mem_leftSpine_mem (List.getElem_mem h3)
    have hsz : s ≤ ls[2 * (i + 1) + 1] :=
      ((minKey?_eq_some_iff_of_isBST hBST).mp hmin).2 _ hz_mem
    omega

lemma collectFoldedPopRots_no_pop (idx : ℕ) (st : BinaryTree ℕ × Option ℕ)
    {fops : List FoldedOp}
    (hNoPop : fops.filterMap (fun | .pop s => some s | _ => none) = []) :
    collectFoldedPopRots idx st fops = [] := by
  induction fops generalizing idx st with
  | nil => rfl
  | cons fop rest ih =>
    cases fop with
    | push w =>
      dsimp only [List.filterMap_cons, collectFoldedPopRots, foldedPopRotsAt] at hNoPop ⊢
      exact ih (idx + 1) _ hNoPop
    | pop s =>
      simp at hNoPop
    | shift =>
      dsimp only [List.filterMap_cons, collectFoldedPopRots, foldedPopRotsAt] at hNoPop ⊢
      exact ih (idx + 1) _ hNoPop
    | upperRot u v =>
      dsimp only [List.filterMap_cons, collectFoldedPopRots, foldedPopRotsAt] at hNoPop ⊢
      exact ih (idx + 1) _ hNoPop

lemma foldedPopRotsAt_non_pop {idx : ℕ} {st : BinaryTree ℕ × Option ℕ}
    {H : BinaryTree ℕ} {uop : OneSidedOp} (hNotPop : popOpt uop = none) :
    foldedPopRotsAt idx st (spineFoldOp H uop) = [] := by
  cases uop with
  | push w => rfl
  | pop s => simp [popOpt] at hNotPop
  | rightSpineLeftRot d =>
    dsimp only [spineFoldOp]
    split_ifs
    · rfl
    · rcases (rightSpine H)[d - 2]?, (rightSpine H)[d - 1]? with ⟨_ | u, _ | v⟩ <;> rfl

lemma collectFoldedPopRots_filter_outside {P L R : ℕ} (idx : ℕ) {H : BinaryTree ℕ}
    (hBST : H.IsBST) {uops : List OneSidedOp} (hValid : ValidOneSidedOps P H uops)
    (hOut : ∀ s ∈ uops.filterMap popOpt, ¬ (L ≤ s ∧ s ≤ R)) :
    (collectFoldedPopRots idx (spineFoldTree H) (spineFoldOpList H uops)).filter
      (fun e => decide (L ≤ e.s ∧ e.z ≤ R)) = [] := by
  induction uops generalizing idx H with
  | nil => rfl
  | cons op rest ih =>
    obtain ⟨hv1, hvRest⟩ := hValid
    obtain ⟨hNextBST, _, hfStep⟩ := spineFold_step_comm hBST hv1
    simp only [spineFoldOpList_cons, collectFoldedPopRots, List.filter_append, hfStep]
    have hRestNil : (collectFoldedPopRots (idx + 1) (spineFoldTree (op.step H))
        (spineFoldOpList (op.step H) rest)).filter
        (fun e => decide (L ≤ e.s ∧ e.z ≤ R)) = [] :=
      ih (idx + 1) hNextBST hvRest (fun s hs => hOut s (by
        simp only [List.filterMap_cons]
        cases popOpt op <;> simp [hs]))
    rw [hRestNil, List.append_nil]
    cases op with
    | push w => rfl
    | rightSpineLeftRot d =>
      rw [foldedPopRotsAt_non_pop (by rfl)]; rfl
    | pop s =>
      have hs_out : ¬ (L ≤ s ∧ s ≤ R) := hOut s (by simp [popOpt])
      have hlen := foldedPopRotsAt_filter_length (L := L) (R := R) (idx := idx)
        hBST hv1.1 hv1.2
      dsimp only at hlen
      simp only [hs_out, ite_false] at hlen
      exact List.eq_nil_of_length_eq_zero hlen

def projState (L R : ℕ) (H : BinaryTree ℕ) : BinaryTree ℕ :=
  relabelTree (shiftKey L) (trimAbove R H)

def projStepOps (L R : ℕ) (H : BinaryTree ℕ) : OneSidedOp → List OneSidedOp
  | .push w => if w ≤ R then [.push (shiftKey L w)] else []
  | .pop s => [.pop (shiftKey L s)]
  | .rightSpineLeftRot d =>
    match (rightSpine H)[d]? with
    | some b => if b ≤ R then [.rightSpineLeftRot d] else []
    | none => []

def projWindowTrajectory (L R : ℕ) : BinaryTree ℕ → List OneSidedOp → List OneSidedOp
  | _, [] => []
  | H, op :: rest => projStepOps L R H op ++ projWindowTrajectory L R (op.step H) rest

lemma projState_isBST {L R : ℕ} {H : BinaryTree ℕ} (hBST : H.IsBST)
    (hGeL : ∀ k ∈ H, L ≤ k) : (projState L R H).IsBST :=
  isBST_relabelTree_shiftKey (isBST_trimAbove hBST)
    (fun k hk => hGeL k ((mem_trimAbove_iff hBST).mp hk).1)

lemma projStepOps_spec {P L R : ℕ} (hL : 1 ≤ L) {H : BinaryTree ℕ}
    (hBST : H.IsBST) (hGeL : ∀ k ∈ H, L ≤ k) {op : OneSidedOp}
    (hValid : op.Valid P H)
    (hPushGeL : ∀ w, op = .push w → L ≤ w)
    (hPopInLR : ∀ s, op = .pop s → L ≤ s ∧ s ≤ R) :
    let Q := R - L + 1
    (∀ k ∈ op.step H, L ≤ k) ∧
    ValidOneSidedOps Q (projState L R H) (projStepOps L R H op) ∧
    (projStepOps L R H op).foldl OneSidedOp.step (projState L R H) =
      projState L R (op.step H) ∧
    (projStepOps L R H op).filterMap popOpt = (popOpt op).toList.map (shiftKey L) ∧
    (∀ idx₁ idx₂ : ℕ,
      (collectFoldedPopRots idx₁ (spineFoldTree (projState L R H))
        (spineFoldOpList (projState L R H) (projStepOps L R H op))).length =
      ((foldedPopRotsAt idx₂ (spineFoldTree H) (spineFoldOp H op)).filter
        (fun e => decide (L ≤ e.s ∧ e.z ≤ R))).length) := by
  intro Q
  cases op with
  | push w =>
    have hwL : L ≤ w := hPushGeL w rfl
    obtain ⟨_, _, hwlt⟩ := hValid
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rcases mem_node_iff.mp hk with rfl | hnil | hmem
      · exact hwL
      · simp at hnil
      · exact hGeL k hmem
    · dsimp only [projStepOps]
      split_ifs with hwR
      · refine ⟨⟨by simp [shiftKey]; omega, by simp [shiftKey, Q]; omega, ?_⟩, trivial⟩
        intro k' hk'
        rw [projState, mem_iff_mem_toKeyList, toKeyList_relabelTree, List.mem_map] at hk'
        obtain ⟨k, hk_list, rfl⟩ := hk'
        have hk_mem : k ∈ H :=
          ((mem_trimAbove_iff hBST).mp (mem_iff_mem_toKeyList.mpr hk_list)).1
        have hwk : w < k := hwlt k hk_mem
        simp only [shiftKey]; omega
      · trivial
    · dsimp only [projStepOps, OneSidedOp.step, projState]
      rw [trimAbove_push hBST hwlt]
      split_ifs with hwR <;> rfl
    · dsimp only [projStepOps, popOpt]
      split_ifs <;> rfl
    · intro idx₁ idx₂
      have hNoPop : ((projStepOps L R H (.push w)).filterMap popOpt) = [] := by
        dsimp only [projStepOps]; split_ifs <;> rfl
      have h1 : collectFoldedPopRots idx₁ (spineFoldTree (projState L R H))
          (spineFoldOpList (projState L R H) (projStepOps L R H (.push w))) = [] :=
        collectFoldedPopRots_no_pop idx₁ _
          (by rw [spineFoldOpList_filterMap_pop, hNoPop])
      rw [h1]; rfl
  | rightSpineLeftRot d =>
    obtain ⟨hd1, hdlen⟩ := hValid
    have hcomm := trimAbove_rotateLeftAtRightSpine1 (R := R) hBST hd1 hdlen
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [OneSidedOp.step, mem_iff_mem_toKeyList, toKeyList_rotateLeftAtRightSpine1 H hd1,
        ← mem_iff_mem_toKeyList] at hk
      exact hGeL k hk
    · dsimp only [projStepOps]
      rcases hget : (rightSpine H)[d]? with _ | b
      · trivial
      · rw [hget] at hcomm
        dsimp only at hcomm ⊢
        split_ifs with hbR
        · simp only [hbR, ite_true] at hcomm
          refine ⟨⟨hd1, ?_⟩, trivial⟩
          rw [projState, rightSpine_relabelTree, List.length_map]
          exact hcomm.1
        · trivial
    · dsimp only [projStepOps, OneSidedOp.step]
      rcases hget : (rightSpine H)[d]? with _ | b
      · rw [hget] at hcomm; exact False.elim hcomm
      · rw [hget] at hcomm
        dsimp only at hcomm ⊢
        split_ifs with hbR
        · simp only [hbR, ite_true] at hcomm
          simp [OneSidedOp.step, projState, rotateLeftAtRightSpine1_relabelTree, hcomm.2]
        · simp only [hbR, ite_false] at hcomm
          simp [projState, hcomm]
    · dsimp only [projStepOps, popOpt]
      rcases (rightSpine H)[d]? with _ | b
      · rfl
      · dsimp only
        split_ifs <;> rfl
    · intro idx₁ idx₂
      have hNoPop : ((projStepOps L R H (.rightSpineLeftRot d)).filterMap popOpt) = [] := by
        dsimp only [projStepOps]
        rcases (rightSpine H)[d]? with _ | b
        · rfl
        · dsimp only
          split_ifs <;> rfl
      have h1 : collectFoldedPopRots idx₁ (spineFoldTree (projState L R H))
          (spineFoldOpList (projState L R H) (projStepOps L R H (.rightSpineLeftRot d))) = [] :=
        collectFoldedPopRots_no_pop idx₁ _
          (by rw [spineFoldOpList_filterMap_pop, hNoPop])
      rw [h1, foldedPopRotsAt_non_pop (by rfl)]
      rfl
  | pop s =>
    have hsLR : L ≤ s ∧ s ≤ R := hPopInLR s rfl
    obtain ⟨hne, hmin⟩ := hValid
    have hs_in : s ∈ H := ((minKey?_eq_some_iff_of_isBST hBST).mp hmin).1
    have htrim_ne : trimAbove R H ≠ .nil :=
      ne_nil_of_mem s ((mem_trimAbove_iff hBST).mpr ⟨hs_in, hsLR.2⟩)
    have hS_ne : projState L R H ≠ .nil :=
      (relabelTree_eq_nil_iff _ _).not.mpr htrim_ne
    have htrim_min : (trimAbove R H).minKey? = some s := by
      rw [minKey?_eq_some_iff_of_isBST (isBST_trimAbove hBST)]
      refine ⟨(mem_trimAbove_iff hBST).mpr ⟨hs_in, hsLR.2⟩, fun k hk => ?_⟩
      exact ((minKey?_eq_some_iff_of_isBST hBST).mp hmin).2 k ((mem_trimAbove_iff hBST).mp hk).1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [OneSidedOp.step, mem_iff_mem_toKeyList, toKeyList_popCascade] at hk
      exact hGeL k (mem_iff_mem_toKeyList.mpr (List.mem_of_mem_tail hk))
    · refine ⟨⟨hS_ne, ?_⟩, trivial⟩
      rw [projState, minKey?_relabelTree, htrim_min]
      rfl
    · dsimp only [projStepOps, List.foldl_cons, List.foldl_nil, OneSidedOp.step]
      have htrim_ge : ∀ k ∈ trimAbove R H, L ≤ k :=
        fun k hk => hGeL k ((mem_trimAbove_iff hBST).mp hk).1
      rw [projState, popCascade_relabelTree_shiftKey htrim_ge,
        ← trimAbove_popCascade hBST hne hmin hsLR.2]
      rfl
    · rfl
    · intro idx₁ idx₂
      have hS_bst : (projState L R H).IsBST := projState_isBST hBST hGeL
      simp only [projStepOps, spineFoldOpList_cons, spineFoldOpList_nil, spineFoldOp,
        collectFoldedPopRots, List.append_nil]
      rw [foldedPopRotsAt_spineFold_length hS_bst hS_ne,
        foldedPopRotsAt_filter_length hBST hne hmin]
      simp [hsLR, projState, leftSpine_relabelTree]

lemma projWindowTrajectory_spec {P L R : ℕ} (hL : 1 ≤ L) {H : BinaryTree ℕ}
    (hBST : H.IsBST) (hGeL : ∀ k ∈ H, L ≤ k)
    {winOps : List OneSidedOp} (hValid : ValidOneSidedOps P H winOps)
    (hPushGeL : ∀ (i : ℕ) (w : ℕ), winOps[i]? = some (.push w) → L ≤ w)
    (hPopInLR : ∀ s ∈ winOps.filterMap popOpt, L ≤ s ∧ s ≤ R) :
    let Q := R - L + 1
    let subOps := projWindowTrajectory L R H winOps
    ValidOneSidedOps Q (projState L R H) subOps ∧
    subOps.foldl OneSidedOp.step (projState L R H) =
      projState L R (winOps.foldl OneSidedOp.step H) ∧
    subOps.filterMap popOpt = (winOps.filterMap popOpt).map (shiftKey L) ∧
    (∀ idx₁ idx₂ : ℕ,
      (collectFoldedPopRots idx₁ (spineFoldTree (projState L R H))
        (spineFoldOpList (projState L R H) subOps)).length =
      ((collectFoldedPopRots idx₂ (spineFoldTree H)
        (spineFoldOpList H winOps)).filter
        (fun e => decide (L ≤ e.s ∧ e.z ≤ R))).length) := by
  induction winOps generalizing H with
  | nil =>
    simp [projWindowTrajectory, ValidOneSidedOps, collectFoldedPopRots]
  | cons op rest ih =>
    obtain ⟨hv1, hvRest⟩ := hValid
    obtain ⟨hNextBST, _, hfStep⟩ := spineFold_step_comm hBST hv1
    have hp1 : ∀ w, op = .push w → L ≤ w := fun w hw => by
      subst hw; exact hPushGeL 0 w rfl
    have hpop1 : ∀ s, op = .pop s → L ≤ s ∧ s ≤ R := fun s hs => by
      subst hs; exact hPopInLR s (by simp [popOpt])
    obtain ⟨hNextGeL, hStepValid, hStepFold, hStepPop, hStepRots⟩ :=
      projStepOps_spec hL hBST hGeL hv1 hp1 hpop1
    have hpRest : ∀ (i : ℕ) (w : ℕ), rest[i]? = some (.push w) → L ≤ w :=
      fun i w hi => hPushGeL (i + 1) w (by simp [hi])
    have hpopRest : ∀ s ∈ rest.filterMap popOpt, L ≤ s ∧ s ≤ R :=
      fun s hs => hPopInLR s (by simp only [List.filterMap_cons]; cases popOpt op <;> simp [hs])
    obtain ⟨hRestValid, hRestFold, hRestPop, hRestRots⟩ :=
      ih hNextBST hNextGeL hvRest hpRest hpopRest
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [projWindowTrajectory, validOneSidedOps_append, hStepFold]
      exact ⟨hStepValid, hRestValid⟩
    · simp [projWindowTrajectory, List.foldl_append, hStepFold, hRestFold]
    · simp only [projWindowTrajectory, List.filterMap_append, hStepPop, hRestPop,
        List.filterMap_cons]
      cases popOpt op <;> rfl
    · intro idx₁ idx₂
      have hS_bst : (projState L R H).IsBST := projState_isBST hBST hGeL
      obtain ⟨_, _, hfSubFold⟩ := spineFoldOpList_valid_and_foldl hS_bst hStepValid
      simp only [projWindowTrajectory, spineFoldOpList_append, collectFoldedPopRots_append,
        hfSubFold, hStepFold, spineFoldOpList_cons, collectFoldedPopRots,
        List.filter_append, List.length_append, hfStep]
      rw [hStepRots idx₁ idx₂, hRestRots _ (idx₂ + 1)]

lemma range'_sub_filter (P L R : ℕ) (hL : 1 ≤ L) (hLR : L ≤ R) (hRP : R ≤ P) :
    (List.range' 1 P).filter (fun s => decide (L ≤ s ∧ s ≤ R)) =
      List.range' L (R - L + 1) := by
  have hsplit1 : List.range' 1 P =
      List.range' 1 (L - 1) ++ (List.range' L (R - L + 1) ++ List.range' (R + 1) (P - R)) := by
    have h2 : List.range' L (R - L + 1 + (P - R)) =
        List.range' L (R - L + 1) ++ List.range' (R + 1) (P - R) := by
      rw [← List.range'_append]
      congr 2
      omega
    have h1 : List.range' 1 (L - 1 + (R - L + 1 + (P - R))) =
        List.range' 1 (L - 1) ++ List.range' L (R - L + 1 + (P - R)) := by
      rw [← List.range'_append]
      congr 2
      omega
    have hP_eq : P = L - 1 + (R - L + 1 + (P - R)) := by omega
    conv_lhs => rw [hP_eq]
    rw [h1, h2]
  rw [hsplit1, List.filter_append, List.filter_append]
  have hf1 : (List.range' 1 (L - 1)).filter (fun s => decide (L ≤ s ∧ s ≤ R)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    rw [List.mem_range'_1] at hs
    simp; omega
  have hf2 : (List.range' L (R - L + 1)).filter (fun s => decide (L ≤ s ∧ s ≤ R)) =
      List.range' L (R - L + 1) := by
    rw [List.filter_eq_self]
    intro s hs
    rw [List.mem_range'_1] at hs
    simp; omega
  have hf3 : (List.range' (R + 1) (P - R)).filter (fun s => decide (L ≤ s ∧ s ≤ R)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro s hs
    rw [List.mem_range'_1] at hs
    simp; omega
  rw [hf1, hf2, hf3, List.nil_append, List.append_nil]

lemma map_shiftKey_range' (L Q : ℕ) (hL : 1 ≤ L) :
    (List.range' L Q).map (shiftKey L) = List.range' 1 Q := by
  induction Q generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 : List.range' L (n + 1) = L :: List.range' (L + 1) n := rfl
    have h2 : List.range' 1 (n + 1) = 1 :: List.range' 2 n := rfl
    rw [h1, h2, List.map_cons]
    congr 1
    · simp [shiftKey]; omega
    · clear ih
      have hgen : ∀ (a k : ℕ), L ≤ a →
          (List.range' a k).map (shiftKey L) = List.range' (a - (L - 1)) k := by
        intro a k
        induction k generalizing a with
        | zero => intro _; rfl
        | succ m ihm =>
          intro ha
          simp only [List.range'_succ, List.map_cons]
          congr 1
          rw [ihm (a + 1) (by omega)]
          congr 1
          omega
      rw [hgen (L + 1) n (by omega)]
      congr 1
      omega

end HelperLeafSubproc

open HelperLeafSubproc in
theorem exists_interval_subproc (P L R : ℕ) (hL : 1 ≤ L) (hLR : L ≤ R) (hRP : R ≤ P)
    (proc : FoldedPopProcess P)
    (hBST : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P) :
    ∃ subProc : FoldedPopProcess (R - L + 1),
      subProc.J = (proc.rInt.filter (fun e => L ≤ e.s ∧ e.z ≤ R)).card := by
  let _ := hBST
  have hP : 1 ≤ P := by omega
  set Q := R - L + 1
  have hQ : 1 ≤ Q := by omega
  -- Step 1: Lift `proc` from `(.nil, none) = spineFoldTree .nil` to unfolded `usteps`
  obtain ⟨usteps, hUValid, hUFold⟩ := lift_validFoldedOps SplayDeque.Direct.isBSTNil proc.hValid
  have hUFoldAll := spineFoldOpList_valid_and_foldl SplayDeque.Direct.isBSTNil hUValid
  have hUEnd : usteps.foldl OneSidedOp.step .nil = .nil := by
    have h1 := hUFoldAll.2.2
    rw [hUFold] at h1
    change proc.steps.foldl FoldedOp.step (.nil, none) = _ at h1
    rw [proc.hEndEmpty] at h1
    exact (spineFoldTree_fst_eq_nil_iff _).mp (congrArg Prod.fst h1.symm)
  have hUPopSeq : usteps.filterMap popOpt = List.range' 1 P := by
    rw [← spineFoldOpList_filterMap_pop .nil usteps, hUFold]
    exact proc.hPopSeq
  -- Step 2: Locate window `[τ_start, τ_end]` from `POP(L)` through `POP(R)`
  obtain ⟨τ_start, hτ_start_lt, hτ_start_op⟩ := exists_pop_idx hUPopSeq hL (by omega)
  obtain ⟨τ_R, hτ_R_lt, hτ_R_op⟩ := exists_pop_idx hUPopSeq (by omega) hRP
  have hτ_le : τ_start ≤ τ_R := pop_idx_le_of_le hUPopSeq hLR hτ_start_op hτ_R_op
  set τ_end := τ_R + 1
  have hτ_end_le : τ_end ≤ usteps.length := by omega
  set preOps := usteps.take τ_start
  set winOps := (usteps.drop τ_start).take (τ_end - τ_start)
  set postOps := usteps.drop τ_end
  have hWinAppendPost : winOps ++ postOps = usteps.drop τ_start := by
    have hdrop : postOps = (usteps.drop τ_start).drop (τ_end - τ_start) := by
      simp only [postOps, List.drop_drop, show τ_start + (τ_end - τ_start) = τ_end by omega]
    rw [hdrop]
    exact List.take_append_drop _ _
  have hUSplit : preOps ++ (winOps ++ postOps) = usteps := by
    rw [hWinAppendPost]
    exact List.take_append_drop _ _
  -- Step 2b: Establish window `.pop` and `.push` properties
  have hPreOut : ∀ s ∈ preOps.filterMap popOpt, s < L := by
    intro s hs
    obtain ⟨op, hop_mem, hop_eq⟩ := List.mem_filterMap.mp hs
    have hop_pop : op = .pop s := by
      cases op <;> simp [popOpt] at hop_eq; exact congrArg OneSidedOp.pop hop_eq
    subst hop_pop
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hop_mem
    have hi_lt_start : i < τ_start := by
      dsimp only [preOps] at hi_lt
      have := List.length_take_le τ_start usteps
      omega
    have hi_usteps : usteps[i]? = some (.pop s) := by
      have htake : preOps[i]? = some (.pop s) := by
        rw [List.getElem?_eq_getElem hi_lt, hi_eq]
      rw [List.getElem?_take_of_lt hi_lt_start] at htake
      exact htake
    exact pop_lt_of_idx_lt hUPopSeq hi_lt_start hi_usteps hτ_start_op
  have hPostOut : ∀ s ∈ postOps.filterMap popOpt, R < s := by
    intro s hs
    obtain ⟨op, hop_mem, hop_eq⟩ := List.mem_filterMap.mp hs
    have hop_pop : op = .pop s := by
      cases op <;> simp [popOpt] at hop_eq; exact congrArg OneSidedOp.pop hop_eq
    subst hop_pop
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hop_mem
    have hi_usteps : usteps[τ_end + i]? = some (.pop s) := by
      have hdrop : postOps[i]? = some (.pop s) := by
        rw [List.getElem?_eq_getElem hi_lt, hi_eq]
      rwa [List.getElem?_drop] at hdrop
    exact pop_lt_of_idx_lt hUPopSeq (show τ_R < τ_end + i by omega) hτ_R_op hi_usteps
  have hWinInLR : ∀ s ∈ winOps.filterMap popOpt, L ≤ s ∧ s ≤ R := by
    intro s hs
    obtain ⟨op, hop_mem, hop_eq⟩ := List.mem_filterMap.mp hs
    have hop_pop : op = .pop s := by
      cases op <;> simp [popOpt] at hop_eq; exact congrArg OneSidedOp.pop hop_eq
    subst hop_pop
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hop_mem
    have hi_bound : i < τ_end - τ_start := by
      dsimp only [winOps] at hi_lt
      have := List.length_take_le (τ_end - τ_start) (usteps.drop τ_start)
      omega
    have hi_usteps : usteps[τ_start + i]? = some (.pop s) := by
      have h1 : winOps[i]? = some (.pop s) := by
        rw [List.getElem?_eq_getElem hi_lt, hi_eq]
      rw [List.getElem?_take_of_lt hi_bound, List.getElem?_drop] at h1
      exact h1
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hi_pos
      · simp only [Nat.add_zero] at hi_usteps
        rw [hτ_start_op, Option.some.injEq, OneSidedOp.pop.injEq] at hi_usteps
        omega
      · exact le_of_lt (pop_lt_of_idx_lt hUPopSeq (by omega) hτ_start_op hi_usteps)
    · rcases (show τ_start + i = τ_R ∨ τ_start + i < τ_R by omega) with heq | hlt
      · rw [heq, hτ_R_op, Option.some.injEq, OneSidedOp.pop.injEq] at hi_usteps
        omega
      · exact le_of_lt (pop_lt_of_idx_lt hUPopSeq hlt hi_usteps hτ_R_op)
  have hWinPopSeq : winOps.filterMap popOpt = List.range' L Q := by
    have hfm : (preOps.filterMap popOpt ++ (winOps.filterMap popOpt ++ postOps.filterMap popOpt)) =
        List.range' 1 P := by
      rw [← List.filterMap_append, ← List.filterMap_append, hUSplit, hUPopSeq]
    have hfilt := congrArg (List.filter (fun s => decide (L ≤ s ∧ s ≤ R))) hfm
    rw [List.filter_append, List.filter_append, range'_sub_filter P L R hL hLR hRP] at hfilt
    have hf_pre : (preOps.filterMap popOpt).filter (fun s => decide (L ≤ s ∧ s ≤ R)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s hs; have := hPreOut s hs; simp; omega
    have hf_win : (winOps.filterMap popOpt).filter (fun s => decide (L ≤ s ∧ s ≤ R)) =
        winOps.filterMap popOpt := by
      rw [List.filter_eq_self]
      intro s hs; have := hWinInLR s hs; simp [this]
    have hf_post : (postOps.filterMap popOpt).filter (fun s => decide (L ≤ s ∧ s ≤ R)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro s hs; have := hPostOut s hs; simp; omega
    rw [hf_pre, hf_win, hf_post, List.nil_append, List.append_nil] at hfilt
    exact hfilt
  have hWinPushGeL : ∀ (i : ℕ) (w : ℕ), winOps[i]? = some (.push w) → L ≤ w := by
    intro i w hi
    have hi_lt_win : i < winOps.length := (List.getElem?_eq_some_iff.mp hi).1
    have hi_bound : i < τ_end - τ_start := by
      dsimp only [winOps] at hi_lt_win
      have := List.length_take_le (τ_end - τ_start) (usteps.drop τ_start)
      omega
    have hi_usteps : usteps[τ_start + i]? = some (.push w) := by
      rw [List.getElem?_take_of_lt hi_bound, List.getElem?_drop] at hi
      exact hi
    have hw_in : w ∈ uTree .nil usteps (τ_start + i + 1) := by
      rw [uTree_step hi_usteps]
      exact .here
    have hw_out : w ∉ uTree .nil usteps usteps.length := by
      simp [uTree, List.take_length, hUEnd]
    obtain ⟨τ', hτ'_ge, _, hτ'_pop⟩ :=
      exists_pop_of_mem_not_mem SplayDeque.Direct.isBSTNil hUValid (by omega) le_rfl hw_in hw_out
    exact le_of_lt (pop_lt_of_idx_lt hUPopSeq (by omega) hτ_start_op hτ'_pop)
  -- Step 3: States `H_start` and `H_end`
  set H_start := preOps.foldl OneSidedOp.step .nil
  set H_end := winOps.foldl OneSidedOp.step H_start
  have hValidPreWinPost := validOneSidedOps_append.mp (hUSplit ▸ hUValid)
  have hValidPre : ValidOneSidedOps P .nil preOps := hValidPreWinPost.1
  have hValidWinPost := validOneSidedOps_append.mp hValidPreWinPost.2
  have hValidWin : ValidOneSidedOps P H_start winOps := hValidWinPost.1
  have hValidPost : ValidOneSidedOps P H_end postOps := hValidWinPost.2
  have hH_start_bst : H_start.IsBST :=
    (spineFoldOpList_valid_and_foldl SplayDeque.Direct.isBSTNil hValidPre).1
  have hH_end_bst : H_end.IsBST := (spineFoldOpList_valid_and_foldl hH_start_bst hValidWin).1
  have hH_start_geL : ∀ k ∈ H_start, L ≤ k := by
    have hpopL_val : (OneSidedOp.pop L).Valid P (uTree .nil usteps τ_start) :=
      uTree_valid_at hUValid hτ_start_op
    change (OneSidedOp.pop L).Valid P H_start at hpopL_val
    exact ((minKey?_eq_some_iff_of_isBST hH_start_bst).mp hpopL_val.2).2
  have hH_end_gtR : ∀ k ∈ H_end, R < k := by
    have hH_end_eq : H_end = uTree .nil usteps τ_end := by
      have htake_end : usteps.take τ_end = preOps ++ winOps := by
        have h1 : (preOps ++ (winOps ++ postOps)).take τ_end = usteps.take τ_end :=
          congrArg (List.take τ_end) hUSplit
        have hpre_len : preOps.length = τ_start := List.length_take_of_le (by omega)
        have hwin_len : winOps.length = τ_end - τ_start := by
          simp [winOps, List.length_take, List.length_drop]; omega
        rw [← List.append_assoc,
          List.take_append_of_le_length (by rw [List.length_append, hpre_len, hwin_len]; omega),
          List.take_of_length_le (by rw [List.length_append, hpre_len, hwin_len]; omega)] at h1
        exact h1.symm
      simp [uTree, htake_end, List.foldl_append, H_end, H_start]
    intro k hk
    rw [hH_end_eq] at hk
    have hk_out : k ∉ uTree .nil usteps usteps.length := by
      simp [uTree, List.take_length, hUEnd]
    obtain ⟨τ', hτ'_ge, _, hτ'_pop⟩ :=
      exists_pop_of_mem_not_mem SplayDeque.Direct.isBSTNil hUValid hτ_end_le le_rfl hk hk_out
    exact pop_lt_of_idx_lt hUPopSeq (by omega) hτ_R_op hτ'_pop
  have hS_end_nil : projState L R H_end = .nil := by
    simp [projState, trimAbove_eq_nil_of_gt hH_end_bst hH_end_gtR, relabelTree]
  -- Step 4: Construct `allSubOps = initSteps ++ winSubSteps` and fold into `subProc`
  set S_start := projState L R H_start
  have hS_start_bst : S_start.IsBST := projState_isBST hH_start_bst hH_start_geL
  have hS_start_keys : ∀ x ∈ S_start, 1 ≤ x ∧ x ≤ Q := by
    intro x hx
    dsimp only [S_start] at hx
    rw [projState, mem_iff_mem_toKeyList, toKeyList_relabelTree, List.mem_map] at hx
    obtain ⟨k, hk_list, rfl⟩ := hx
    obtain ⟨hk_in, hk_leR⟩ :=
      (mem_trimAbove_iff hH_start_bst).mp (mem_iff_mem_toKeyList.mpr hk_list)
    have hk_geL := hH_start_geL k hk_in
    simp only [shiftKey]; omega
  set initSteps := buildBST S_start
  set winSubSteps := projWindowTrajectory L R H_start winOps
  set allSubOps := initSteps ++ winSubSteps
  obtain ⟨hInitValid, hInitFold, hInitNoPop⟩ := buildBST_spec S_start hS_start_bst hS_start_keys
  obtain ⟨hWinSubValid, hWinSubFold, hWinSubPop, hWinSubRots⟩ :=
    projWindowTrajectory_spec hL hH_start_bst hH_start_geL hValidWin hWinPushGeL hWinInLR
  have hAllValid : ValidOneSidedOps Q .nil allSubOps := by
    rw [validOneSidedOps_append, hInitFold]
    exact ⟨hInitValid, hWinSubValid⟩
  have hAllEnd : allSubOps.foldl OneSidedOp.step .nil = .nil := by
    rw [List.foldl_append, hInitFold, hWinSubFold, hS_end_nil]
  have hAllPopSeq : allSubOps.filterMap popOpt = List.range' 1 Q := by
    rw [List.filterMap_append, hInitNoPop, List.nil_append, hWinSubPop, hWinPopSeq,
      map_shiftKey_range' L Q hL]
  have hAllPopLen : (allSubOps.filterMap popOpt).length = Q := by
    rw [hAllPopSeq, List.length_range']
  have hAllPushLen : (allSubOps.filterMap pushOpt).length = Q := by
    have hbal := num_nodes_balance SplayDeque.Direct.isBSTNil hAllValid
    rw [hAllEnd, hAllPopLen] at hbal
    simp at hbal
    omega
  have hAllKL : (allSubOps.filter isRightSpineRot).length < 2 * Q :=
    kL_lt_two_mul hQ hAllValid hAllEnd hAllPushLen hAllPopLen
  set subSteps := spineFoldOpList .nil allSubOps
  obtain ⟨_, hSubFoldValid, hSubFoldEnd⟩ :=
    spineFoldOpList_valid_and_foldl SplayDeque.Direct.isBSTNil hAllValid
  let subProc : FoldedPopProcess Q :=
    { steps := subSteps
      hValid := hSubFoldValid
      hEndEmpty := by
        change subSteps.foldl FoldedOp.step (spineFoldTree .nil) = (.nil, none)
        rw [hSubFoldEnd, hAllEnd]
        rfl
      hPushCount := by
        dsimp only [subSteps]
        exact (congrArg List.length
          ((List.filterMap_congr fun x _ => by cases x <;> rfl).trans
            (spineFoldOpList_filterMap_push .nil allSubOps))).trans hAllPushLen
      hPopSeq := by
        dsimp only [subSteps]
        exact ((List.filterMap_congr fun x _ => by cases x <;> rfl).trans
          (spineFoldOpList_filterMap_pop .nil allSubOps)).trans hAllPopSeq
      hKLBound := Or.inr ⟨hQ, by
        dsimp only [subSteps]
        refine lt_of_eq_of_lt ?_ hAllKL
        exact (congrArg List.length (List.filter_congr fun x _ => by cases x <;> rfl)).trans
          (spineFoldOpList_filter_upper .nil allSubOps)⟩ }
  refine ⟨subProc, ?_⟩
  -- Step 5: Match `subProc.J` with `(proc.rInt.filter ...).card`
  set pred := fun (e : InternalPopRot) => decide (L ≤ e.s ∧ e.z ≤ R)
  have hSubJ : subProc.J = (collectFoldedPopRots 0 (.nil, none) subSteps).length := by
    unfold FoldedPopProcess.J FoldedPopProcess.rInt
    exact List.toFinset_card_of_nodup (nodup_collectFoldedPopRots 0 (.nil, none) subSteps)
  have hOrigCard : (proc.rInt.filter (fun e => L ≤ e.s ∧ e.z ≤ R)).card =
      ((collectFoldedPopRots 0 (.nil, none) proc.steps).filter pred).length := by
    have hfilt_eq : proc.rInt.filter (fun e => L ≤ e.s ∧ e.z ≤ R) =
        ((collectFoldedPopRots 0 (.nil, none) proc.steps).filter pred).toFinset := by
      ext e
      simp [FoldedPopProcess.rInt, pred]
    rw [hfilt_eq]
    exact List.toFinset_card_of_nodup
      ((nodup_collectFoldedPopRots 0 (.nil, none) proc.steps).filter pred)
  rw [hSubJ, hOrigCard]
  -- Expand `subSteps = spineFoldOpList .nil (initSteps ++ winSubSteps)`
  have hSubRotsEq : (collectFoldedPopRots 0 (.nil, none) subSteps).length =
      (collectFoldedPopRots (initSteps.length) (spineFoldTree S_start)
        (spineFoldOpList S_start winSubSteps)).length := by
    have h1 : subSteps = spineFoldOpList .nil initSteps ++ spineFoldOpList S_start winSubSteps := by
      simp only [subSteps, allSubOps, initSteps, spineFoldOpList_append, hInitFold]
    obtain ⟨_, _, hInitFoldStep⟩ :=
      spineFoldOpList_valid_and_foldl SplayDeque.Direct.isBSTNil hInitValid
    have hInitLen : (spineFoldOpList .nil initSteps).length = initSteps.length := by
      clear *-
      generalize (.nil : BinaryTree ℕ) = t
      induction initSteps generalizing t with
      | nil => rfl
      | cons op rest ih => simp [ih]
    have hInitRotsNil :
        collectFoldedPopRots 0 (spineFoldTree .nil) (spineFoldOpList .nil initSteps) = [] :=
      collectFoldedPopRots_no_pop 0 (spineFoldTree .nil)
        (by rw [spineFoldOpList_filterMap_pop, hInitNoPop])
    change (collectFoldedPopRots 0 (spineFoldTree .nil) subSteps).length = _
    rw [h1, collectFoldedPopRots_append, hInitRotsNil, List.nil_append, Nat.zero_add, hInitLen]
    dsimp only [initSteps]
    rw [hInitFoldStep, hInitFold]
  -- Expand `proc.steps = spineFoldOpList .nil (preOps ++ (winOps ++ postOps))`
  have hOrigRotsEq :
      ((collectFoldedPopRots 0 (.nil, none) proc.steps).filter pred).length =
      ((collectFoldedPopRots preOps.length (spineFoldTree H_start)
        (spineFoldOpList H_start winOps)).filter pred).length := by
    rw [← hUFold, ← hUSplit]
    have hsp1 : spineFoldOpList .nil (preOps ++ (winOps ++ postOps)) =
        spineFoldOpList .nil preOps ++
          (spineFoldOpList H_start winOps ++ spineFoldOpList H_end postOps) := by
      rw [spineFoldOpList_append, spineFoldOpList_append]
    obtain ⟨_, _, hPreFoldStep⟩ :=
      spineFoldOpList_valid_and_foldl SplayDeque.Direct.isBSTNil hValidPre
    obtain ⟨_, _, hWinFoldStep⟩ := spineFoldOpList_valid_and_foldl hH_start_bst hValidWin
    have hPreLen : (spineFoldOpList .nil preOps).length = preOps.length := by
      clear *-
      generalize (.nil : BinaryTree ℕ) = t
      induction preOps generalizing t with
      | nil => rfl
      | cons op rest ih => simp [ih]
    have hPreNil : (collectFoldedPopRots 0 (spineFoldTree .nil)
        (spineFoldOpList .nil preOps)).filter pred = [] :=
      collectFoldedPopRots_filter_outside 0 SplayDeque.Direct.isBSTNil hValidPre
        (fun s hs => by have := hPreOut s hs; omega)
    have hPostNil : ∀ idx', (collectFoldedPopRots idx' (spineFoldTree H_end)
        (spineFoldOpList H_end postOps)).filter pred = [] :=
      fun idx' => collectFoldedPopRots_filter_outside idx' hH_end_bst hValidPost
        (fun s hs => by have := hPostOut s hs; omega)
    change ((collectFoldedPopRots 0 (spineFoldTree .nil)
      (spineFoldOpList .nil (preOps ++ (winOps ++ postOps)))).filter pred).length = _
    rw [hsp1, collectFoldedPopRots_append, List.filter_append, hPreNil, List.nil_append,
      hPreFoldStep, Nat.zero_add, hPreLen, collectFoldedPopRots_append, List.filter_append,
      hWinFoldStep, hPostNil, List.append_nil]
  rw [hSubRotsEq, hOrigRotsEq]
  exact hWinSubRots initSteps.length preOps.length

end Subproc52

namespace ScaleLca53

/-!
## Part 1: `validScaleTree_chain`
-/

theorem consecutiveBlocks_iff_getElem (xs : List IntervalBlock) :
    ConsecutiveBlocks xs ↔
      ∀ (i : ℕ) (h : i + 1 < xs.length), xs[i].hi + 1 = xs[i + 1].lo := by
  induction xs with
  | nil =>
    simp [ConsecutiveBlocks]
  | cons c1 rest ih =>
    cases rest with
    | nil =>
      simp [ConsecutiveBlocks]
    | cons c2 tl =>
      simp only [ConsecutiveBlocks, ih]
      constructor
      · rintro ⟨h01, hrest⟩ i hi
        cases i with
        | zero => exact h01
        | succ j =>
          have hj : j + 1 < (c2 :: tl).length := by simpa using hi
          exact hrest j hj
      · intro hall
        refine ⟨hall 0 (by simp), fun j hj => ?_⟩
        have hj' : (j + 1) + 1 < (c1 :: c2 :: tl).length := by simpa using hj
        exact hall (j + 1) hj'

theorem consecutiveBlocks_append (xs ys : List IntervalBlock)
    (hxs : ConsecutiveBlocks xs) (hys : ConsecutiveBlocks ys)
    (hlink : ∀ last first, xs.getLast? = some last → ys.head? = some first →
      last.hi + 1 = first.lo) :
    ConsecutiveBlocks (xs ++ ys) := by
  induction xs with
  | nil => simpa using hys
  | cons x1 rest ih =>
    cases rest with
    | nil =>
      cases ys with
      | nil => simp [ConsecutiveBlocks]
      | cons y1 ytl =>
        simp only [List.singleton_append, ConsecutiveBlocks]
        exact ⟨hlink x1 y1 rfl rfl, hys⟩
    | cons x2 xtl =>
      simp only [List.cons_append, ConsecutiveBlocks] at hxs ⊢
      refine ⟨hxs.1, ih hxs.2 (fun last first hlast hfirst => ?_)⟩
      apply hlink last first _ hfirst
      simpa using hlast

theorem splitIntervalBySize_props (X : IntervalBlock) (S : ℕ)
    (hX : X.lo ≤ X.hi) :
    let subs := splitIntervalBySize X S
    (∀ Y ∈ subs, X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi) ∧
    ConsecutiveBlocks subs ∧
    ∃ first last, subs.head? = some first ∧ subs.getLast? = some last ∧
      first.lo = X.lo ∧ last.hi = X.hi := by
  dsimp only
  unfold splitIntervalBySize
  by_cases htriv : S = 0 ∨ X.size < 2 * S
  · simp only [htriv, ↓reduceIte]
    refine ⟨?_, by simp [ConsecutiveBlocks], X, X, rfl, rfl, rfl, rfl⟩
    intro Y hY
    simp only [List.mem_singleton] at hY
    subst Y
    exact ⟨le_rfl, hX, le_rfl⟩
  · simp only [htriv, ↓reduceIte]
    have hS : 1 ≤ S := by omega
    have h2S : 2 * S ≤ X.size := by omega
    have hXsz : X.size = X.hi - X.lo + 1 := by simp [IntervalBlock.size, hX]
    set K := X.size / S
    have hK2 : 2 ≤ K := (Nat.le_div_iff_mul_le hS).mpr h2S
    have hdiv : S * K + X.size % S = X.size := Nat.div_add_mod X.size S
    have hmod : X.size % S < S := Nat.mod_lt X.size hS
    have hKS : K * S = S * K := Nat.mul_comm K S
    let f : ℕ → IntervalBlock := fun idx =>
      if idx + 1 < K then ⟨X.lo + idx * S, X.lo + (idx + 1) * S - 1⟩
      else ⟨X.lo + idx * S, X.hi⟩
    change (∀ Y ∈ (List.range K).map f, X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi) ∧
      ConsecutiveBlocks ((List.range K).map f) ∧
      ∃ first last, ((List.range K).map f).head? = some first ∧
        ((List.range K).map f).getLast? = some last ∧ first.lo = X.lo ∧ last.hi = X.hi
    refine ⟨?_, ?_, ?_⟩
    · intro Y hY
      rw [List.mem_map] at hY
      obtain ⟨idx, hidx, rfl⟩ := hY
      rw [List.mem_range] at hidx
      dsimp only [f]
      by_cases hlt : idx + 1 < K
      · simp only [hlt, ↓reduceIte]
        have hmul : (idx + 1) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
        have hstep : idx * S + S = (idx + 1) * S := by ring
        exact ⟨by omega, by omega, by omega⟩
      · simp only [hlt, ↓reduceIte]
        have hidx_eq : idx = K - 1 := by omega
        subst idx
        have hK1S : (K - 1) * S + S = K * S := by
          have : (K - 1) + 1 = K := by omega
          calc (K - 1) * S + S = ((K - 1) + 1) * S := by ring
            _ = K * S := by rw [this]
        exact ⟨by omega, by omega, le_rfl⟩
    · rw [consecutiveBlocks_iff_getElem]
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      simp only [List.getElem_map, List.getElem_range]
      have hi1 : i + 1 < K := hi
      have hfi_hi : (f i).hi = X.lo + (i + 1) * S - 1 := by
        simp [f, hi1]
      have hfi1_lo : (f (i + 1)).lo = X.lo + (i + 1) * S := by
        dsimp only [f]
        split_ifs <;> rfl
      rw [hfi_hi, hfi1_lo]
      have hpos : 1 ≤ (i + 1) * S := by nlinarith
      omega
    · refine ⟨f 0, f (K - 1), ?_, ?_, ?_, ?_⟩
      · rw [List.head?_eq_getElem?]
        have h0 : 0 < ((List.range K).map f).length := by simp; omega
        rw [List.getElem?_eq_getElem h0]
        simp
      · have hKsplit : K = (K - 1) + 1 := by omega
        conv_lhs => rw [hKsplit, List.range_succ, List.map_append, List.map_singleton]
        simp
      · have h01 : 0 + 1 < K := by omega
        simp [f, h01]
      · have hnlt : ¬ ((K - 1) + 1 < K) := by omega
        simp [f, hnlt]

theorem flatMap_split_chain (blocks : List IntervalBlock) (S : ℕ)
    (hne : blocks ≠ [])
    (hvalid : ∀ X ∈ blocks, X.lo ≤ X.hi)
    (hconsec : ConsecutiveBlocks blocks) :
    let fine := blocks.flatMap (fun X => splitIntervalBySize X S)
    ConsecutiveBlocks fine ∧
    ∃ first last bFirst bLast,
      blocks.head? = some bFirst ∧ blocks.getLast? = some bLast ∧
      fine.head? = some first ∧ fine.getLast? = some last ∧
      first.lo = bFirst.lo ∧ last.hi = bLast.hi := by
  induction blocks with
  | nil => exact absurd rfl hne
  | cons X rest ih =>
    have hX : X.lo ≤ X.hi := hvalid X List.mem_cons_self
    obtain ⟨_, hXconsec, firstX, lastX, hXhead, hXlast, hXlo, hXhi⟩ :=
      splitIntervalBySize_props X S hX
    cases rest with
    | nil =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact ⟨hXconsec, firstX, lastX, X, X, rfl, rfl, hXhead, hXlast, hXlo, hXhi⟩
    | cons X2 tl =>
      simp only [ConsecutiveBlocks] at hconsec
      obtain ⟨hlink12, hconsecRest⟩ := hconsec
      have hvalidRest : ∀ Y ∈ X2 :: tl, Y.lo ≤ Y.hi :=
        fun Y hY => hvalid Y (List.mem_cons_of_mem X hY)
      obtain ⟨hfRestConsec, firstR, lastR, bFirstR, bLastR,
        hbFirstR, hbLastR, hfHeadR, hfLastR, hloR, hhiR⟩ :=
        ih (List.cons_ne_nil X2 tl) hvalidRest hconsecRest
      have hbFirstR_eq : bFirstR = X2 := by
        simp only [List.head?_cons, Option.some.injEq] at hbFirstR
        exact hbFirstR.symm
      subst bFirstR
      set xs := splitIntervalBySize X S
      set ys := (X2 :: tl).flatMap (fun Y => splitIntervalBySize Y S)
      have hxs_ne : xs ≠ [] := by intro h; simp [h] at hXhead
      have hys_ne : ys ≠ [] := by intro h; simp [h] at hfHeadR
      dsimp only
      rw [List.flatMap_cons]
      change ConsecutiveBlocks (xs ++ ys) ∧
        ∃ first last bFirst bLast,
          (X :: X2 :: tl).head? = some bFirst ∧ (X :: X2 :: tl).getLast? = some bLast ∧
          (xs ++ ys).head? = some first ∧ (xs ++ ys).getLast? = some last ∧
          first.lo = bFirst.lo ∧ last.hi = bLast.hi
      refine ⟨?_, firstX, lastR, X, bLastR, rfl, ?_, ?_, ?_, hXlo, hhiR⟩
      · apply consecutiveBlocks_append xs ys hXconsec hfRestConsec
        intro l f hl hf
        rw [hXlast, Option.some.injEq] at hl
        rw [hfHeadR, Option.some.injEq] at hf
        subst l; subst f
        omega
      · simpa using hbLastR
      · rw [List.head?_append_of_ne_nil xs hxs_ne]
        exact hXhead
      · rw [List.getLast?_append_of_ne_nil xs hys_ne]
        exact hfLastR

theorem scaleTreePartitionLevel_contiguous (T : ScaleTree) (P : ℕ) (hP : 1 ≤ P) :
    ∀ n : ℕ, IsContiguousBlockPartition P (scaleTreePartitionLevel T P n)
  | 0 => by
    have hP0 : P ≠ 0 := by omega
    unfold scaleTreePartitionLevel
    simp only [hP0, ↓reduceIte]
    refine ⟨?_, trivial, ⟨rfl, rfl⟩⟩
    intro C hC
    simp only [List.mem_singleton] at hC
    subst C
    exact ⟨le_rfl, hP, le_rfl⟩
  | n + 1 => by
    obtain ⟨hbounds, hconsec, hmatch⟩ := scaleTreePartitionLevel_contiguous T P hP n
    set blocks := scaleTreePartitionLevel T P n
    have hne : blocks ≠ [] := by
      intro hnil
      rw [hnil] at hmatch
      simp only [List.head?_nil] at hmatch
      omega
    have hvalid : ∀ X ∈ blocks, X.lo ≤ X.hi := fun X hX => (hbounds X hX).2.1
    set S := scaleS T P (n + 1)
    obtain ⟨hfConsec, first, last, bFirst, bLast,
      hbFirst, hbLast, hfHead, hfLast, hfirstLo, hlastHi⟩ :=
      flatMap_split_chain blocks S hne hvalid hconsec
    rw [hbFirst, hbLast] at hmatch
    obtain ⟨hbFirstLo, hbLastHi⟩ := hmatch
    simp only [scaleTreePartitionLevel, IsContiguousBlockPartition]
    refine ⟨?_, hfConsec, ?_⟩
    · intro Y hY
      rw [List.mem_flatMap] at hY
      obtain ⟨X, hX, hYX⟩ := hY
      obtain ⟨hX1, hXle, hXP⟩ := hbounds X hX
      obtain ⟨hXY1, hYle, hXY2⟩ := (splitIntervalBySize_props X S hXle).1 Y hYX
      exact ⟨le_trans hX1 hXY1, hYle, le_trans hXY2 hXP⟩
    · rw [hfHead, hfLast]
      exact ⟨by omega, by omega⟩

theorem validScaleTree_chain (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) :
    IsNestedPartitionChain P (scaleTreePartitionChain T P M) := by
  have hP : 1 ≤ P := hValid.1
  have hP0 : P ≠ 0 := by omega
  refine ⟨hP, ?_, ?_, ?_⟩
  · simp [scaleTreePartitionChain, scaleTreePartitionLevel, hP0]
  · intro ℓ
    exact scaleTreePartitionLevel_contiguous T P hP ℓ.val
  · intro ℓ Y hY
    simp only [scaleTreePartitionChain, Fin.val_succ, Fin.val_castSucc,
      scaleTreePartitionLevel, List.mem_flatMap] at hY ⊢
    obtain ⟨X, hX, hYX⟩ := hY
    have hXpart := scaleTreePartitionLevel_contiguous T P hP ℓ.val
    have hXle : X.lo ≤ X.hi := (hXpart.1 X hX).2.1
    obtain ⟨h1, _, h2⟩ := (splitIntervalBySize_props X (scaleS T P (ℓ.val + 1)) hXle).1 Y hYX
    exact ⟨X, hX, h1, h2⟩

/-!
## Part 2: `scaleTree_lca_props`
-/

theorem mem_leafEntriesChildren (c₀ : ℕ) (cs : List ScaleTree) (s : ℕ) (addr : List ℕ) :
    (s, addr) ∈ ScaleTree.leafEntriesChildren c₀ cs ↔
      ∃ (idx : ℕ) (hidx : idx < cs.length) (rest : List ℕ),
        addr = (c₀ + idx) :: rest ∧ (s, rest) ∈ cs[idx].leafEntries := by
  induction cs generalizing c₀ with
  | nil =>
    simp [ScaleTree.leafEntriesChildren]
  | cons child tl ih =>
    simp only [ScaleTree.leafEntriesChildren, List.mem_append, List.mem_map, ih (c₀ + 1)]
    constructor
    · rintro (⟨⟨s', rest⟩, hmem, heq⟩ | ⟨idx, hidx, rest, haddr, hmem⟩)
      · injection heq with hs haddr
        dsimp only at hs haddr
        subst s'; subst addr
        exact ⟨0, Nat.zero_lt_succ _, rest, by simp, hmem⟩
      · refine ⟨idx + 1, Nat.succ_lt_succ hidx, rest, ?_, hmem⟩
        rw [show c₀ + (idx + 1) = c₀ + 1 + idx by omega]
        exact haddr
    · rintro ⟨idx, hidx, rest, haddr, hmem⟩
      cases idx with
      | zero =>
        left
        refine ⟨(s, rest), hmem, ?_⟩
        simp at haddr
        rw [haddr]
      | succ idx =>
        right
        refine ⟨idx, Nat.lt_of_succ_lt_succ hidx, rest, ?_, hmem⟩
        rw [show c₀ + 1 + idx = c₀ + (idx + 1) by omega]
        exact haddr

theorem leafEntriesChildren_map_fst (c₀ : ℕ) (cs : List ScaleTree) :
    (ScaleTree.leafEntriesChildren c₀ cs).map Prod.fst = cs.flatMap ScaleTree.leaves := by
  induction cs generalizing c₀ with
  | nil => rfl
  | cons child tl ih =>
    simp [ScaleTree.leafEntriesChildren, List.map_append, List.map_map,
      Function.comp_def, ScaleTree.leaves, ih (c₀ + 1)]

theorem internal_leaves_eq (cs : List ScaleTree) :
    (ScaleTree.internal cs).leaves = cs.flatMap ScaleTree.leaves := by
  simp [ScaleTree.leaves, ScaleTree.leafEntries, leafEntriesChildren_map_fst]

theorem mem_internalAddrChildren (c₀ : ℕ) (cs : List ScaleTree) (addr : List ℕ) :
    addr ∈ ScaleTree.internalAddrChildren c₀ cs ↔
      ∃ (idx : ℕ) (hidx : idx < cs.length) (rest : List ℕ),
        addr = (c₀ + idx) :: rest ∧ rest ∈ cs[idx].internalAddrList := by
  induction cs generalizing c₀ with
  | nil =>
    simp [ScaleTree.internalAddrChildren]
  | cons child tl ih =>
    simp only [ScaleTree.internalAddrChildren, List.mem_append, List.mem_map, ih (c₀ + 1)]
    constructor
    · rintro (⟨rest, hmem, rfl⟩ | ⟨idx, hidx, rest, haddr, hmem⟩)
      · exact ⟨0, Nat.zero_lt_succ _, rest, by simp, hmem⟩
      · refine ⟨idx + 1, Nat.succ_lt_succ hidx, rest, ?_, hmem⟩
        rw [show c₀ + (idx + 1) = c₀ + 1 + idx by omega]
        exact haddr
    · rintro ⟨idx, hidx, rest, haddr, hmem⟩
      cases idx with
      | zero =>
        left
        refine ⟨rest, hmem, ?_⟩
        simp at haddr
        exact haddr.symm
      | succ idx =>
        right
        refine ⟨idx, Nat.lt_of_succ_lt_succ hidx, rest, ?_, hmem⟩
        rw [show c₀ + 1 + idx = c₀ + (idx + 1) by omega]
        exact haddr

theorem mem_leafEntries_iff_subtreeAtAddr (T : ScaleTree) (s : ℕ) (addr : List ℕ) :
    (s, addr) ∈ T.leafEntries ↔ subtreeAtAddr T addr = some (.leaf s) := by
  induction addr generalizing T with
  | nil =>
    cases T with
    | leaf s' =>
      simp [ScaleTree.leafEntries, subtreeAtAddr, eq_comm]
    | internal cs =>
      simp [ScaleTree.leafEntries, mem_leafEntriesChildren, subtreeAtAddr]
  | cons c rest ih =>
    cases T with
    | leaf s' =>
      simp [ScaleTree.leafEntries, subtreeAtAddr]
    | internal cs =>
      simp only [ScaleTree.leafEntries, mem_leafEntriesChildren, List.cons.injEq, subtreeAtAddr]
      by_cases hc0 : c = 0
      · subst c
        simp only [↓reduceIte, reduceCtorEq, iff_false, not_exists]
        rintro idx _ rest' ⟨⟨h0, _⟩, _⟩
        omega
      · simp only [hc0, ↓reduceIte]
        by_cases hlt : c - 1 < cs.length
        · rw [List.getElem?_eq_getElem hlt, ← ih cs[c - 1]]
          constructor
          · rintro ⟨idx, hidx, rest', ⟨hc, hrest⟩, hmem⟩
            subst rest'
            have hidx_eq : idx = c - 1 := by omega
            subst idx
            exact hmem
          · intro hmem
            exact ⟨c - 1, hlt, rest, ⟨by omega, rfl⟩, hmem⟩
        · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
          simp only [reduceCtorEq, iff_false, not_exists]
          rintro idx hidx rest' ⟨⟨hc, _⟩, _⟩
          omega

theorem mem_internalAddrs_iff_subtreeAtAddr (T : ScaleTree) (ν : List ℕ) :
    ν ∈ internalAddrs T ↔ ∃ cs, subtreeAtAddr T ν = some (.internal cs) := by
  rw [internalAddrs, List.mem_toFinset]
  induction ν generalizing T with
  | nil =>
    cases T with
    | leaf s => simp [ScaleTree.internalAddrList, subtreeAtAddr]
    | internal cs => simp [ScaleTree.internalAddrList, subtreeAtAddr]
  | cons c rest ih =>
    cases T with
    | leaf s => simp [ScaleTree.internalAddrList, subtreeAtAddr]
    | internal cs =>
      simp only [ScaleTree.internalAddrList, List.mem_cons, reduceCtorEq, false_or,
        mem_internalAddrChildren, List.cons.injEq, subtreeAtAddr]
      by_cases hc0 : c = 0
      · subst c
        simp only [↓reduceIte, reduceCtorEq, exists_false, iff_false, not_exists]
        rintro idx _ rest' ⟨⟨h0, _⟩, _⟩
        omega
      · simp only [hc0, ↓reduceIte]
        by_cases hlt : c - 1 < cs.length
        · rw [List.getElem?_eq_getElem hlt, ← ih cs[c - 1]]
          constructor
          · rintro ⟨idx, _, rest', ⟨hc, hrest⟩, hmem⟩
            subst rest'
            have hidx_eq : idx = c - 1 := by omega
            subst idx
            exact hmem
          · intro hmem
            exact ⟨c - 1, hlt, rest, ⟨by omega, rfl⟩, hmem⟩
        · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)]
          simp only [reduceCtorEq, exists_false, iff_false, not_exists]
          rintro idx hidx rest' ⟨⟨hc, _⟩, _⟩
          omega

theorem subtreeAtAddr_append (T : ScaleTree) (ξ₁ ξ₂ : List ℕ) :
    subtreeAtAddr T (ξ₁ ++ ξ₂) = (subtreeAtAddr T ξ₁).bind (fun sub => subtreeAtAddr sub ξ₂) := by
  induction ξ₁ generalizing T with
  | nil => rfl
  | cons c rest ih =>
    cases T with
    | leaf _ => rfl
    | internal cs =>
      simp only [List.cons_append, subtreeAtAddr]
      by_cases hc0 : c = 0
      · simp [hc0]
      · simp only [hc0, ↓reduceIte]
        cases cs[c - 1]? with
        | none => rfl
        | some child => exact ih child

mutual
  private theorem scaleTree_leaves_nonempty :
      ∀ (T : ScaleTree), T.AllInternalNonempty → T.leaves ≠ []
    | .leaf s, _ => by simp [ScaleTree.leaves, ScaleTree.leafEntries]
    | .internal cs, hT => by
      simp only [ScaleTree.AllInternalNonempty] at hT
      rw [internal_leaves_eq]
      exact children_flatMap_leaves_nonempty cs hT.1 hT.2

  private theorem children_flatMap_leaves_nonempty :
      ∀ (cs : List ScaleTree), cs ≠ [] → (∀ child ∈ cs, child.AllInternalNonempty) →
        cs.flatMap ScaleTree.leaves ≠ []
    | [], hne, _ => absurd rfl hne
    | child :: rest, _, hall => by
      simp only [List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
      intro hnil
      exact absurd hnil (scaleTree_leaves_nonempty child (hall child List.mem_cons_self))
end

theorem range'_add_eq (a n₁ n₂ : ℕ) :
    List.range' a (n₁ + n₂) = List.range' a n₁ ++ List.range' (a + n₁) n₂ := by
  induction n₁ generalizing a with
  | zero => simp
  | succ n₁ ih =>
    simp only [Nat.succ_add, List.range', List.cons_append, ih (a + 1)]
    congr 2

theorem eq_range'_of_append_eq_range' (xs ys : List ℕ) (a len : ℕ)
    (h : xs ++ ys = List.range' a len) :
    xs = List.range' a xs.length ∧
      ys = List.range' (a + xs.length) ys.length ∧
      xs.length + ys.length = len := by
  have hlen : xs.length + ys.length = len := by
    have := congrArg List.length h
    simpa using this
  subst len
  rw [range'_add_eq] at h
  have h1 : xs.length = (List.range' a xs.length).length := by simp
  obtain ⟨hxs, hys⟩ := List.append_inj h h1
  exact ⟨hxs, hys, rfl⟩

theorem flatMap_getElem_split {α β : Type*} (cs : List α) (f : α → List β)
    (idx : ℕ) (hidx : idx < cs.length) :
    cs.flatMap f =
      (cs.take idx).flatMap f ++ f cs[idx] ++ (cs.drop (idx + 1)).flatMap f := by
  conv_lhs => rw [← List.take_append_drop idx cs, List.drop_eq_getElem_cons hidx]
  rw [List.flatMap_append, List.flatMap_cons, ← List.append_assoc]

theorem subtreeAtAddr_leaves_range' (T : ScaleTree) (hne : T.AllInternalNonempty)
    (a len : ℕ) (hleaves : T.leaves = List.range' a len)
    (ξ : List ℕ) (sub : ScaleTree) (hsub : subtreeAtAddr T ξ = some sub) :
    ∃ aSub kSub : ℕ,
      sub.leaves = List.range' aSub kSub ∧
      1 ≤ kSub ∧ a ≤ aSub ∧ aSub + kSub ≤ a + len := by
  induction ξ generalizing T a len with
  | nil =>
    simp only [subtreeAtAddr, Option.some.injEq] at hsub
    subst sub
    have hnonempty : T.leaves ≠ [] := scaleTree_leaves_nonempty T hne
    have hlen : 1 ≤ len := by
      cases len with
      | zero => simp [List.range'] at hleaves; exact absurd hleaves hnonempty
      | succ k => omega
    exact ⟨a, len, hleaves, hlen, le_rfl, le_rfl⟩
  | cons c rest ih =>
    cases T with
    | leaf _ => simp [subtreeAtAddr] at hsub
    | internal cs =>
      simp only [ScaleTree.AllInternalNonempty] at hne
      simp only [subtreeAtAddr] at hsub
      by_cases hc0 : c = 0
      · simp [hc0] at hsub
      · simp only [hc0, ↓reduceIte] at hsub
        by_cases hlt : c - 1 < cs.length
        · rw [List.getElem?_eq_getElem hlt] at hsub
          rw [internal_leaves_eq, flatMap_getElem_split cs ScaleTree.leaves (c - 1) hlt] at hleaves
          set L1 := (cs.take (c - 1)).flatMap ScaleTree.leaves
          set L2 := (cs.drop (c - 1 + 1)).flatMap ScaleTree.leaves
          obtain ⟨h12, _, hlen12⟩ := eq_range'_of_append_eq_range' (L1 ++ cs[c - 1].leaves) L2 a len hleaves
          obtain ⟨_, hchild, hlen1⟩ := eq_range'_of_append_eq_range' L1 cs[c - 1].leaves a (L1 ++ cs[c - 1].leaves).length h12
          have hchild_ne : cs[c - 1].AllInternalNonempty := hne.2 cs[c - 1] (List.getElem_mem hlt)
          obtain ⟨aSub, kSub, hSubLeaves, hkSub, haSub, hhiSub⟩ :=
            ih cs[c - 1] hchild_ne (a + L1.length) cs[c - 1].leaves.length hchild hsub
          refine ⟨aSub, kSub, hSubLeaves, hkSub, by omega, ?_⟩
          simp only [List.length_append] at hlen12
          omega
        · rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hsub
          simp at hsub

theorem range'_head_last (a k : ℕ) (hk : 1 ≤ k) :
    (List.range' a k).head?.getD 0 = a ∧ (List.range' a k).getLast?.getD 0 = a + k - 1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hhead : (List.range' a (1 + d)).head?.getD 0 = a := by
    rw [show 1 + d = d + 1 by omega]
    rfl
  have hlast : (List.range' a (1 + d)).getLast?.getD 0 = a + (1 + d) - 1 := by
    rw [show 1 + d = d + 1 by omega, range'_add_eq a d 1]
    have h1 : List.range' (a + d) 1 = [a + d] := rfl
    rw [h1, List.getLast?_concat]
    simp
  exact ⟨hhead, hlast⟩

theorem children_two_ranges (cs : List ScaleTree) (a len : ℕ)
    (hcs : cs.flatMap ScaleTree.leaves = List.range' a len)
    (idx₁ idx₂ : ℕ) (h12 : idx₁ < idx₂) (h2 : idx₂ < cs.length) :
    ∃ a₁ k₁ a₂ k₂ : ℕ,
      cs[idx₁].leaves = List.range' a₁ k₁ ∧
      cs[idx₂].leaves = List.range' a₂ k₂ ∧
      a ≤ a₁ ∧ a₁ + k₁ ≤ a₂ ∧ a₂ + k₂ ≤ a + len := by
  rw [flatMap_getElem_split cs ScaleTree.leaves idx₂ h2] at hcs
  have h1_take : idx₁ < (cs.take idx₂).length := by simp [Nat.le_of_lt h2, h12]
  rw [flatMap_getElem_split (cs.take idx₂) ScaleTree.leaves idx₁ h1_take] at hcs
  simp only [List.getElem_take] at hcs
  set A := ((cs.take idx₂).take idx₁).flatMap ScaleTree.leaves
  set B := ((cs.take idx₂).drop (idx₁ + 1)).flatMap ScaleTree.leaves
  set C := (cs.drop (idx₂ + 1)).flatMap ScaleTree.leaves
  obtain ⟨hAB2, _, hlenC⟩ :=
    eq_range'_of_append_eq_range' (A ++ cs[idx₁].leaves ++ B ++ cs[idx₂].leaves) C a len hcs
  obtain ⟨hAB, hchild2, hlen2⟩ :=
    eq_range'_of_append_eq_range' (A ++ cs[idx₁].leaves ++ B) cs[idx₂].leaves a
      (A ++ cs[idx₁].leaves ++ B ++ cs[idx₂].leaves).length hAB2
  obtain ⟨hA1, _, hlenB⟩ :=
    eq_range'_of_append_eq_range' (A ++ cs[idx₁].leaves) B a
      (A ++ cs[idx₁].leaves ++ B).length hAB
  obtain ⟨_, hchild1, hlen1⟩ :=
    eq_range'_of_append_eq_range' A cs[idx₁].leaves a (A ++ cs[idx₁].leaves).length hA1
  refine ⟨a + A.length, cs[idx₁].leaves.length,
    a + (A ++ cs[idx₁].leaves ++ B).length, cs[idx₂].leaves.length,
    hchild1, hchild2, by omega, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · simp only [List.length_append] at hlenC ⊢
    omega

theorem leafAddr_spec (r M : ℕ) (T : ScaleTree) (hScale : IsScaleTree r M T)
    (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hM : ℓ ≤ M) :
    (ℓ, leafAddr T ℓ) ∈ T.leafEntries ∧
      subtreeAtAddr T (leafAddr T ℓ) = some (.leaf ℓ) ∧
      1 ≤ (leafAddr T ℓ).length ∧ (leafAddr T ℓ).length ≤ r := by
  have ⟨_, _, _, hLeaves, hDepth⟩ := hScale
  have hmem_leaves : ℓ ∈ T.leaves := by
    rw [hLeaves, List.mem_range'_1]
    omega
  unfold ScaleTree.leaves at hmem_leaves
  rw [List.mem_map] at hmem_leaves
  obtain ⟨⟨s₀, addr₀⟩, hmem₀, hs₀⟩ := hmem_leaves
  dsimp only at hs₀
  subst s₀
  have hfind_ne : T.leafEntries.find? (fun entry => entry.1 == ℓ) ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    have := hnone (ℓ, addr₀) hmem₀
    simp at this
  obtain ⟨⟨s, addr⟩, hfind⟩ := Option.ne_none_iff_exists'.mp hfind_ne
  have haddr_eq : leafAddr T ℓ = addr := by simp [leafAddr, hfind]
  have hmem : (s, addr) ∈ T.leafEntries := List.mem_of_find?_eq_some hfind
  have hs_eq : s = ℓ := by
    have := List.find?_some hfind
    simpa using this
  subst s
  rw [haddr_eq]
  exact ⟨hmem, (mem_leafEntries_iff_subtreeAtAddr T ℓ addr).mp hmem, hDepth (ℓ, addr) hmem⟩

theorem lcp_isPrefix_left [DecidableEq α] (as bs : List α) :
    longestCommonPrefix as bs <+: as := by
  induction as generalizing bs with
  | nil => simp [longestCommonPrefix]
  | cons a as ih =>
    cases bs with
    | nil => simp [longestCommonPrefix]
    | cons b bs =>
      simp only [longestCommonPrefix]
      by_cases hab : a = b
      · subst b
        simp only [↓reduceIte]
        obtain ⟨t, ht⟩ := ih bs
        exact ⟨t, by simp [ht]⟩
      · simp [hab]

theorem lcp_isPrefix_right [DecidableEq α] (as bs : List α) :
    longestCommonPrefix as bs <+: bs := by
  induction as generalizing bs with
  | nil => simp [longestCommonPrefix]
  | cons a as ih =>
    cases bs with
    | nil => simp [longestCommonPrefix]
    | cons b bs =>
      simp only [longestCommonPrefix]
      by_cases hab : a = b
      · subst b
        simp only [↓reduceIte]
        obtain ⟨t, ht⟩ := ih bs
        exact ⟨t, by simp [ht]⟩
      · simp [hab]

theorem prefix_of_common_prefix [DecidableEq α] (p as bs : List α)
    (h1 : p <+: as) (h2 : p <+: bs) :
    p <+: longestCommonPrefix as bs := by
  induction p generalizing as bs with
  | nil => exact ⟨_, rfl⟩
  | cons x ps ih =>
    obtain ⟨t1, rfl⟩ := h1
    obtain ⟨t2, rfl⟩ := h2
    simp only [List.cons_append, longestCommonPrefix, ↓reduceIte]
    obtain ⟨t, ht⟩ := ih (ps ++ t1) (ps ++ t2) ⟨t1, rfl⟩ ⟨t2, rfl⟩
    exact ⟨t, by simp [ht]⟩

theorem prefix_of_both_prefix {α : Type*} (p q xs : List α)
    (hp : p <+: xs) (hq : q <+: xs) (hlen : p.length ≤ q.length) :
    p <+: q := by
  induction p generalizing q xs with
  | nil => exact ⟨q, rfl⟩
  | cons a ps ih =>
    obtain ⟨t1, rfl⟩ := hp
    cases q with
    | nil => simp at hlen
    | cons b qs =>
      obtain ⟨t2, ht2⟩ := hq
      simp only [List.cons_append, List.cons.injEq] at ht2
      obtain ⟨hba, hq'⟩ := ht2
      subst b
      obtain ⟨t, ht⟩ := ih qs (ps ++ t1) ⟨t1, rfl⟩ ⟨t2, hq'⟩ (Nat.le_of_succ_le_succ hlen)
      exact ⟨t, by simp [ht]⟩

theorem not_leaf_prefix_of_ne (T : ScaleTree) (s₁ s₂ : ℕ) (hs : s₁ ≠ s₂)
    (addr₁ addr₂ : List ℕ)
    (h1 : subtreeAtAddr T addr₁ = some (.leaf s₁))
    (h2 : subtreeAtAddr T addr₂ = some (.leaf s₂)) :
    ¬ (addr₁ <+: addr₂) := by
  rintro ⟨rest, rfl⟩
  rw [subtreeAtAddr_append, h1, Option.bind_some] at h2
  cases rest with
  | nil =>
    simp only [subtreeAtAddr, Option.some.injEq, ScaleTree.leaf.injEq] at h2
    exact hs h2
  | cons c tl =>
    simp [subtreeAtAddr] at h2

theorem scaleTree_lca_props (r M : ℕ) (T : ScaleTree)
    (hScale : IsScaleTree r M T)
    (ℓ₁ ℓ₂ : ℕ) (h1 : 1 ≤ ℓ₁) (h12 : ℓ₁ < ℓ₂) (h2 : ℓ₂ ≤ M) :
    let ν := lcaScaleTree T ℓ₁ ℓ₂
    let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 0
    let mPrev := mStart T (ν ++ [c₂]) - 1
    let m := mEnd T ν
    ν ∈ internalAddrs T ∧
    ν.length < r ∧
    1 ≤ c₂ ∧ c₂ ≤ numChildren T ν ∧
    1 ≤ mStart T (ν ++ [c₂]) ∧
    ℓ₁ ≤ mPrev ∧ mPrev < ℓ₂ ∧ ℓ₂ ≤ m ∧ m ≤ M ∧
    (∀ ℓ₃ : ℕ, m < ℓ₃ → ℓ₃ ≤ M → (lcaScaleTree T ℓ₁ ℓ₃).length < ν.length) := by
  dsimp only
  set addr₁ := leafAddr T ℓ₁
  set addr₂ := leafAddr T ℓ₂
  set ν := lcaScaleTree T ℓ₁ ℓ₂
  have ⟨_, _, hNonempty, hLeaves, _⟩ := hScale
  obtain ⟨_, hSub1, _, hLen1⟩ := leafAddr_spec r M T hScale ℓ₁ h1 (by omega)
  obtain ⟨_, hSub2, _, _⟩ := leafAddr_spec r M T hScale ℓ₂ (by omega) h2
  have hne12 : ℓ₁ ≠ ℓ₂ := by omega
  have hnPref12 : ¬ (addr₁ <+: addr₂) := not_leaf_prefix_of_ne T ℓ₁ ℓ₂ hne12 addr₁ addr₂ hSub1 hSub2
  have hnPref21 : ¬ (addr₂ <+: addr₁) := not_leaf_prefix_of_ne T ℓ₂ ℓ₁ hne12.symm addr₂ addr₁ hSub2 hSub1
  obtain ⟨rest₁, haddr₁_eq⟩ : ν <+: addr₁ := lcp_isPrefix_left addr₁ addr₂
  obtain ⟨rest₂, haddr₂_eq⟩ : ν <+: addr₂ := lcp_isPrefix_right addr₁ addr₂
  cases rest₁ with
  | nil =>
    rw [List.append_nil] at haddr₁_eq
    exact absurd (haddr₁_eq ▸ ⟨rest₂, haddr₂_eq⟩) hnPref12
  | cons c₁ tail₁ =>
    cases rest₂ with
    | nil =>
      rw [List.append_nil] at haddr₂_eq
      exact absurd (haddr₂_eq ▸ ⟨c₁ :: tail₁, haddr₁_eq⟩) hnPref21
    | cons c₂_val tail₂ =>
      have hc12_ne : c₁ ≠ c₂_val := by
        intro heq
        subst c₂_val
        have hp1 : ν ++ [c₁] <+: addr₁ := ⟨tail₁, by simpa [List.append_assoc] using haddr₁_eq⟩
        have hp2 : ν ++ [c₁] <+: addr₂ := ⟨tail₂, by simpa [List.append_assoc] using haddr₂_eq⟩
        have hbad : ν ++ [c₁] <+: ν := prefix_of_common_prefix (ν ++ [c₁]) addr₁ addr₂ hp1 hp2
        have hlen := List.IsPrefix.length_le hbad
        simp at hlen
      have hc₂_eq : (addr₂[ν.length]?).getD 0 = c₂_val := by
        have hget : (ν ++ c₂_val :: tail₂)[ν.length]? = some c₂_val := by
          rw [List.getElem?_append_right le_rfl]
          simp
        rw [← haddr₂_eq, hget]
        rfl
      rw [hc₂_eq]
      have hSubν_bind : (subtreeAtAddr T ν).bind (fun sub => subtreeAtAddr sub (c₁ :: tail₁)) =
          some (.leaf ℓ₁) := by
        rw [← subtreeAtAddr_append, haddr₁_eq]
        exact hSub1
      obtain ⟨subν, hSubν, hSubν_c1⟩ : ∃ sub, subtreeAtAddr T ν = some sub ∧
          subtreeAtAddr sub (c₁ :: tail₁) = some (.leaf ℓ₁) := by
        cases h : subtreeAtAddr T ν with
        | none => rw [h] at hSubν_bind; simp at hSubν_bind
        | some sub => rw [h, Option.bind_some] at hSubν_bind; exact ⟨sub, rfl, hSubν_bind⟩
      obtain ⟨cs, rfl⟩ : ∃ cs, subν = .internal cs := by
        cases subν with
        | leaf _ => simp [subtreeAtAddr] at hSubν_c1
        | internal cs => exact ⟨cs, rfl⟩
      have hν_int : ν ∈ internalAddrs T :=
        (mem_internalAddrs_iff_subtreeAtAddr T ν).mpr ⟨cs, hSubν⟩
      have hν_len : ν.length < r := by
        have hlen_eq : addr₁.length = (ν ++ c₁ :: tail₁).length :=
          congrArg List.length haddr₁_eq.symm
        simp only [List.length_append, List.length_cons] at hlen_eq
        change addr₁.length ≤ r at hLen1
        omega
      have hSubν_c2 : subtreeAtAddr (.internal cs) (c₂_val :: tail₂) = some (.leaf ℓ₂) := by
        have hbind : (subtreeAtAddr T ν).bind (fun sub => subtreeAtAddr sub (c₂_val :: tail₂)) =
            some (.leaf ℓ₂) := by
          rw [← subtreeAtAddr_append, haddr₂_eq]
          exact hSub2
        rw [hSubν, Option.bind_some] at hbind
        exact hbind
      have hc₁_pos : 1 ≤ c₁ := by
        by_contra h0
        have hc0 : c₁ = 0 := by omega
        simp [subtreeAtAddr, hc0] at hSubν_c1
      have hc₁_lt : c₁ - 1 < cs.length := by
        by_contra hge
        have hc0 : c₁ ≠ 0 := by omega
        simp only [subtreeAtAddr, hc0, ↓reduceIte,
          List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hSubν_c1
        simp at hSubν_c1
      have hc₂_pos : 1 ≤ c₂_val := by
        by_contra h0
        have hc0 : c₂_val = 0 := by omega
        simp [subtreeAtAddr, hc0] at hSubν_c2
      have hc₂_lt : c₂_val - 1 < cs.length := by
        by_contra hge
        have hc0 : c₂_val ≠ 0 := by omega
        simp only [subtreeAtAddr, hc0, ↓reduceIte,
          List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hSubν_c2
        simp at hSubν_c2
      have hc₂_le_num : c₂_val ≤ numChildren T ν := by
        simp only [numChildren, hSubν]
        omega
      have hChild1_leaf : subtreeAtAddr cs[c₁ - 1] tail₁ = some (.leaf ℓ₁) := by
        have hc0 : c₁ ≠ 0 := by omega
        simpa [subtreeAtAddr, hc0, List.getElem?_eq_getElem hc₁_lt] using hSubν_c1
      have hChild2_leaf : subtreeAtAddr cs[c₂_val - 1] tail₂ = some (.leaf ℓ₂) := by
        have hc0 : c₂_val ≠ 0 := by omega
        simpa [subtreeAtAddr, hc0, List.getElem?_eq_getElem hc₂_lt] using hSubν_c2
      have hℓ₁_mem_c1 : ℓ₁ ∈ cs[c₁ - 1].leaves := by
        have hmem := (mem_leafEntries_iff_subtreeAtAddr cs[c₁ - 1] ℓ₁ tail₁).mpr hChild1_leaf
        exact List.mem_map_of_mem hmem
      have hℓ₂_mem_c2 : ℓ₂ ∈ cs[c₂_val - 1].leaves := by
        have hmem := (mem_leafEntries_iff_subtreeAtAddr cs[c₂_val - 1] ℓ₂ tail₂).mpr hChild2_leaf
        exact List.mem_map_of_mem hmem
      obtain ⟨aν, kν, hνLeaves, hkν, haν, hhiν⟩ :=
        subtreeAtAddr_leaves_range' T hNonempty 1 M hLeaves ν (.internal cs) hSubν
      have hcs_flat : cs.flatMap ScaleTree.leaves = List.range' aν kν := by
        rwa [← internal_leaves_eq]
      have hmEnd_eq : mEnd T ν = aν + kν - 1 := by
        simp only [mEnd, hSubν, hνLeaves]
        exact (range'_head_last aν kν hkν).2
      have hc1_lt_c2 : c₁ - 1 < c₂_val - 1 := by
        by_contra hge
        have hlt21 : c₂_val - 1 < c₁ - 1 := by omega
        obtain ⟨a₂, k₂, a₁, k₁, hL2, hL1, _, ha21, _⟩ :=
          children_two_ranges cs aν kν hcs_flat (c₂_val - 1) (c₁ - 1) hlt21 hc₁_lt
        rw [hL1, List.mem_range'_1] at hℓ₁_mem_c1
        rw [hL2, List.mem_range'_1] at hℓ₂_mem_c2
        omega
      obtain ⟨a₁, k₁, a₂, k₂, hL1, hL2, haν1, ha12, ha2ν⟩ :=
        children_two_ranges cs aν kν hcs_flat (c₁ - 1) (c₂_val - 1) hc1_lt_c2 hc₂_lt
      have hSub_νc2 : subtreeAtAddr T (ν ++ [c₂_val]) = some cs[c₂_val - 1] := by
        rw [subtreeAtAddr_append, hSubν, Option.bind_some]
        have hc0 : c₂_val ≠ 0 := by omega
        simp [subtreeAtAddr, hc0, List.getElem?_eq_getElem hc₂_lt]
      have hk₂_pos : 1 ≤ k₂ := by
        rw [hL2, List.mem_range'_1] at hℓ₂_mem_c2
        omega
      have hmStart_eq : mStart T (ν ++ [c₂_val]) = a₂ := by
        simp only [mStart, hSub_νc2, hL2]
        exact (range'_head_last a₂ k₂ hk₂_pos).1
      rw [hL1, List.mem_range'_1] at hℓ₁_mem_c1
      rw [hL2, List.mem_range'_1] at hℓ₂_mem_c2
      rw [hmStart_eq, hmEnd_eq]
      refine ⟨hν_int, hν_len, hc₂_pos, hc₂_le_num,
        by omega, by omega, by omega, by omega, by omega, ?_⟩
      intro ℓ₃ hm_lt hℓ₃_le
      obtain ⟨_, hSub3, _, _⟩ := leafAddr_spec r M T hScale ℓ₃ (by omega) hℓ₃_le
      set addr₃ := leafAddr T ℓ₃
      set μ := lcaScaleTree T ℓ₁ ℓ₃
      have hμ1 : μ <+: addr₁ := lcp_isPrefix_left addr₁ addr₃
      have hμ3 : μ <+: addr₃ := lcp_isPrefix_right addr₁ addr₃
      have hν1 : ν <+: addr₁ := ⟨c₁ :: tail₁, haddr₁_eq⟩
      by_contra hge
      have hν_le_μ : ν.length ≤ μ.length := by omega
      have hνμ : ν <+: μ := prefix_of_both_prefix ν μ addr₁ hν1 hμ1 hν_le_μ
      obtain ⟨rest₃, haddr₃_eq⟩ : ν <+: addr₃ := hνμ.trans hμ3
      have hSub3_ν : subtreeAtAddr (.internal cs) rest₃ = some (.leaf ℓ₃) := by
        have hbind : (subtreeAtAddr T ν).bind (fun sub => subtreeAtAddr sub rest₃) =
            some (.leaf ℓ₃) := by
          rw [← subtreeAtAddr_append, haddr₃_eq]
          exact hSub3
        rw [hSubν, Option.bind_some] at hbind
        exact hbind
      have hℓ₃_mem : ℓ₃ ∈ (ScaleTree.internal cs).leaves := by
        have hmem := (mem_leafEntries_iff_subtreeAtAddr (.internal cs) ℓ₃ rest₃).mpr hSub3_ν
        exact List.mem_map_of_mem hmem
      rw [hνLeaves, List.mem_range'_1] at hℓ₃_mem
      omega

end ScaleLca53

namespace Core
open BinaryTree

/-! ## Upstream Exact Types from `Challenge.lean` -/

abbrev Ty_lem_3_6_folded_laws :=
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

abbrev Ty_lem_5_1_tree_weights :=
  ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
    let chain := scaleTreePartitionChain T P M
    (∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T ℓ : ℝ)) < (1 : ℝ) / 2 ∧
    (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) < 2 ∧
    (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50

/-! ## Section 1: Contiguous Partitions, Nested Chains, and `partSepScale` Ultrametric -/

theorem pairwise_lt_or_gt :
    ∀ {blocks : List IntervalBlock},
      blocks.Pairwise (fun A B => A.hi < B.lo) →
      ∀ {A B : IntervalBlock}, A ∈ blocks → B ∈ blocks → A ≠ B →
        A.hi < B.lo ∨ B.hi < A.lo
  | [], _, _, _, hA, _, _ => by cases hA
  | x :: xs, List.Pairwise.cons hhead htail, A, B, hA, hB, hne => by
    rcases List.mem_cons.mp hA with rfl | hAxs
    · rcases List.mem_cons.mp hB with rfl | hBxs
      · exact (hne rfl).elim
      · exact Or.inl (hhead B hBxs)
    · rcases List.mem_cons.mp hB with rfl | hBxs
      · exact Or.inr (hhead A hAxs)
      · exact pairwise_lt_or_gt htail hAxs hBxs hne

theorem pairwise_getElem_lt {α : Type} {R : α → α → Prop} :
    ∀ {xs : List α}, xs.Pairwise R →
      ∀ (i j : ℕ) (hj : j < xs.length) (hlt : i < j),
        R (xs[i]'(Nat.lt_trans hlt hj)) (xs[j]'hj)
  | [], _, _, _, hj, _ => by simp at hj
  | x :: xs, List.Pairwise.cons hhead htail, i, j, hj, hlt => by
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.length_cons] at hj
        exact hhead (xs[j']'(by omega)) (List.getElem_mem _)
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        simp only [List.length_cons] at hj
        exact pairwise_getElem_lt htail i' j' (by omega) (by omega)

theorem consecutiveBlocks_props :
    ∀ (blocks : List IntervalBlock),
      (∀ C ∈ blocks, C.lo ≤ C.hi) →
      ConsecutiveBlocks blocks →
      blocks.Pairwise (fun B₁ B₂ => B₁.hi < B₂.lo) ∧
      ∀ hne : blocks ≠ [],
        (blocks.map IntervalBlock.size).sum = (blocks.getLast hne).hi - (blocks.head hne).lo + 1 ∧
        (blocks.head hne).lo ≤ (blocks.getLast hne).hi ∧
        (∀ u : ℕ, (blocks.head hne).lo ≤ u → u ≤ (blocks.getLast hne).hi →
          ∃ B ∈ blocks, B.lo ≤ u ∧ u ≤ B.hi)
  | [], _, _ => ⟨List.Pairwise.nil, fun h => (h rfl).elim⟩
  | [C], hle, _ => by
    have hC : C.lo ≤ C.hi := hle C List.mem_cons_self
    refine ⟨List.pairwise_singleton _ _, fun _ => ⟨?_, hC, ?_⟩⟩
    · simp [IntervalBlock.size, hC]
    · intro u hu1 hu2
      exact ⟨C, List.mem_cons_self, hu1, hu2⟩
  | C₁ :: C₂ :: rest, hle, ⟨hstep, hcons⟩ => by
    have hle' : ∀ C ∈ C₂ :: rest, C.lo ≤ C.hi :=
      fun C hC => hle C (List.mem_cons_of_mem _ hC)
    obtain ⟨hpair, hne_tail⟩ := consecutiveBlocks_props (C₂ :: rest) hle' hcons
    obtain ⟨hsum_tail, hlo_hi_tail, hex_tail⟩ := hne_tail (List.cons_ne_nil _ _)
    have hC₁ : C₁.lo ≤ C₁.hi := hle C₁ List.mem_cons_self
    have hC₂ : C₂.lo ≤ C₂.hi := hle' C₂ List.mem_cons_self
    have hpw_head : ∀ B ∈ C₂ :: rest, C₁.hi < B.lo := by
      intro B hB
      rcases List.mem_cons.mp hB with rfl | hBrest
      · omega
      · have h2lt : C₂.hi < B.lo := (List.pairwise_cons.mp hpair).1 B hBrest
        omega
    refine ⟨List.Pairwise.cons hpw_head hpair, fun _ => ?_⟩
    have hhead2 : (C₂ :: rest).head (List.cons_ne_nil _ _) = C₂ := rfl
    have hlast_eq : (C₁ :: C₂ :: rest).getLast (List.cons_ne_nil _ _) =
        (C₂ :: rest).getLast (List.cons_ne_nil _ _) := List.getLast_cons_cons
    rw [hhead2] at hsum_tail hlo_hi_tail hex_tail
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_cons, List.sum_cons, hsum_tail, hlast_eq]
      simp only [List.head_cons, IntervalBlock.size, hC₁, ↓reduceIte]
      omega
    · simp only [List.head_cons, hlast_eq]
      omega
    · intro u hu1 hu2
      simp only [List.head_cons] at hu1
      rw [hlast_eq] at hu2
      by_cases huC₁ : u ≤ C₁.hi
      · exact ⟨C₁, List.mem_cons_self, hu1, huC₁⟩
      · obtain ⟨B, hB, hBlo, hBhi⟩ := hex_tail u (by omega) hu2
        exact ⟨B, List.mem_cons_of_mem _ hB, hBlo, hBhi⟩

theorem contiguousPartition_nonempty {P : ℕ} {blocks : List IntervalBlock}
    (hP : 1 ≤ P) (hPart : IsContiguousBlockPartition P blocks) : blocks ≠ [] := by
  intro hnil
  subst hnil
  rcases hPart with ⟨_, _, hends⟩
  simp at hends
  omega

theorem contiguousPartition_sum_and_sizes {P : ℕ} {blocks : List IntervalBlock}
    (hP : 1 ≤ P) (hPart : IsContiguousBlockPartition P blocks) :
    (blocks.map IntervalBlock.size).sum = P ∧ ∀ Q ∈ blocks, 1 ≤ Q.size := by
  have hne := contiguousPartition_nonempty hP hPart
  rcases hPart with ⟨hbnds, hcons, hends⟩
  have hle : ∀ C ∈ blocks, C.lo ≤ C.hi := fun C hC => (hbnds C hC).2.1
  obtain ⟨_, hprops⟩ := consecutiveBlocks_props blocks hle hcons
  obtain ⟨hsum, _, _⟩ := hprops hne
  have hh1 : blocks.head? = some (blocks.head hne) := List.head?_eq_some_head hne
  have hl1 : blocks.getLast? = some (blocks.getLast hne) := List.getLast?_eq_some_getLast hne
  rw [hh1, hl1] at hends
  refine ⟨by omega, ?_⟩
  intro Q hQ
  have hQle := (hbnds Q hQ).2.1
  simp only [IntervalBlock.size, hQle, ↓reduceIte]
  omega

theorem contiguousPartition_unique_mem {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks)
    {B₁ B₂ : IntervalBlock} (h₁ : B₁ ∈ blocks) (h₂ : B₂ ∈ blocks)
    {u : ℕ} (hu₁ : B₁.lo ≤ u ∧ u ≤ B₁.hi) (hu₂ : B₂.lo ≤ u ∧ u ≤ B₂.hi) :
    B₁ = B₂ := by
  have hle : ∀ C ∈ blocks, C.lo ≤ C.hi := fun C hC => (hPart.1 C hC).2.1
  have hpair := (consecutiveBlocks_props blocks hle hPart.2.1).1
  by_contra hne
  rcases pairwise_lt_or_gt hpair h₁ h₂ hne with hlt | hgt <;> omega

theorem blockAt_mem_and_bounds {P : ℕ} {blocks : List IntervalBlock}
    (hP : 1 ≤ P) (hPart : IsContiguousBlockPartition P blocks)
    {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) :
    let B := blockAt blocks u
    B ∈ blocks ∧ B.lo ≤ u ∧ u ≤ B.hi ∧ 1 ≤ B.lo ∧ B.hi ≤ P := by
  have hne := contiguousPartition_nonempty hP hPart
  rcases hPart with ⟨hbnds, hcons, hends⟩
  have hle : ∀ C ∈ blocks, C.lo ≤ C.hi := fun C hC => (hbnds C hC).2.1
  obtain ⟨_, hprops⟩ := consecutiveBlocks_props blocks hle hcons
  obtain ⟨_, _, hex⟩ := hprops hne
  have hh1 : blocks.head? = some (blocks.head hne) := List.head?_eq_some_head hne
  have hl1 : blocks.getLast? = some (blocks.getLast hne) := List.getLast?_eq_some_getLast hne
  rw [hh1, hl1] at hends
  obtain ⟨B₀, hB₀, hlo₀, hhi₀⟩ := hex u (by omega) (by omega)
  dsimp only
  unfold blockAt
  have hsome : (blocks.find? (fun B => decide (B.lo ≤ u ∧ u ≤ B.hi))).isSome := by
    rw [List.find?_isSome]
    exact ⟨B₀, hB₀, decide_eq_true ⟨hlo₀, hhi₀⟩⟩
  obtain ⟨B, hfind⟩ := Option.isSome_iff_exists.mp hsome
  rw [hfind, Option.getD_some]
  have hmem : B ∈ blocks := List.mem_of_find?_eq_some hfind
  have hpred : B.lo ≤ u ∧ u ≤ B.hi :=
    of_decide_eq_true (List.find?_some (p := fun (B : IntervalBlock) => decide (B.lo ≤ u ∧ u ≤ B.hi)) hfind)
  exact ⟨hmem, hpred.1, hpred.2, (hbnds B hmem).1, (hbnds B hmem).2.2⟩

theorem blockAt_eq_of_mem {P : ℕ} {blocks : List IntervalBlock}
    (hP : 1 ≤ P) (hPart : IsContiguousBlockPartition P blocks)
    {B : IntervalBlock} (hB : B ∈ blocks) {u : ℕ} (hu : B.lo ≤ u ∧ u ≤ B.hi) :
    blockAt blocks u = B := by
  have hbnds := hPart.1 B hB
  have h := blockAt_mem_and_bounds hP hPart (by omega) (by omega) (u := u)
  exact contiguousPartition_unique_mem hPart h.1 hB ⟨h.2.1, h.2.2.1⟩ hu

theorem blockAt_lt_of_ne {P : ℕ} {blocks : List IntervalBlock}
    (hP : 1 ≤ P) (hPart : IsContiguousBlockPartition P blocks)
    {u v : ℕ} (hu1 : 1 ≤ u) (huv : u ≤ v) (hvP : v ≤ P)
    (hne : blockAt blocks u ≠ blockAt blocks v) :
    (blockAt blocks u).hi < (blockAt blocks v).lo := by
  have hu := blockAt_mem_and_bounds hP hPart hu1 (by omega)
  have hv := blockAt_mem_and_bounds hP hPart (by omega) hvP
  have hle : ∀ C ∈ blocks, C.lo ≤ C.hi := fun C hC => (hPart.1 C hC).2.1
  have hpair := (consecutiveBlocks_props blocks hle hPart.2.1).1
  rcases pairwise_lt_or_gt hpair hu.1 hv.1 hne with hlt | hgt
  · exact hlt
  · exfalso; omega

theorem blockAt_contiguous_iff {P : ℕ} {blocks : List IntervalBlock}
    (hP : 1 ≤ P) (hPart : IsContiguousBlockPartition P blocks)
    {a b c : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ P) :
    blockAt blocks a = blockAt blocks c ↔
      (blockAt blocks a = blockAt blocks b ∧ blockAt blocks b = blockAt blocks c) := by
  constructor
  · intro heq
    have haB := blockAt_mem_and_bounds hP hPart ha (by omega)
    have hcB := blockAt_mem_and_bounds hP hPart (by omega) hc
    dsimp only at haB hcB
    rw [heq] at haB
    have hb_eq : blockAt blocks b = blockAt blocks c :=
      blockAt_eq_of_mem hP hPart hcB.1 ⟨by omega, by omega⟩
    exact ⟨heq.trans hb_eq.symm, hb_eq⟩
  · rintro ⟨h1, h2⟩; exact h1.trans h2

theorem nestedChain_enclosing {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hle : k₁ ≤ k₂)
    {Y : IntervalBlock} (hY : Y ∈ chain k₂) :
    ∃ X ∈ chain k₁, X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Fin.le_iff_val_le_val.mp hle)
  induction d generalizing k₂ Y with
  | zero =>
    have hk : k₁ = k₂ := Fin.ext (by omega)
    subst hk
    exact ⟨Y, hY, le_rfl, le_rfl⟩
  | succ d ih =>
    have hk2_pos : 0 < k₂.val := by omega
    let prev : Fin M := ⟨k₂.val - 1, by omega⟩
    have hsucc : prev.succ = k₂ := Fin.ext (by simp [prev]; omega)
    rw [← hsucc] at hY
    obtain ⟨Z, hZ, hZlo, hZhi⟩ := hChain.2.2.2 prev Y hY
    have hprev_le : k₁ ≤ prev.castSucc := Fin.le_iff_val_le_val.mpr (by simp [prev]; omega)
    obtain ⟨X, hX, hXlo, hXhi⟩ := ih hprev_le hZ (by simp [prev]; omega)
    exact ⟨X, hX, le_trans hXlo hZlo, le_trans hZhi hXhi⟩

theorem nestedChain_blockAt_sub {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hle : k₁ ≤ k₂)
    {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) :
    (blockAt (chain k₁) u).lo ≤ (blockAt (chain k₂) u).lo ∧
    (blockAt (chain k₂) u).hi ≤ (blockAt (chain k₁) u).hi := by
  have hP := hChain.1
  have hB2 := blockAt_mem_and_bounds hP (hChain.2.2.1 k₂) hu1 huP
  dsimp only at hB2
  obtain ⟨X, hX, hlo, hhi⟩ := nestedChain_enclosing hChain hle hB2.1
  have hXeq : blockAt (chain k₁) u = X :=
    blockAt_eq_of_mem hP (hChain.2.2.1 k₁) hX ⟨by omega, by omega⟩
  rw [hXeq]
  exact ⟨hlo, hhi⟩

theorem nestedChain_blockAt_eq_mono {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hle : k₁ ≤ k₂)
    {u v : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P)
    (heq : blockAt (chain k₂) u = blockAt (chain k₂) v) :
    blockAt (chain k₁) u = blockAt (chain k₁) v := by
  have hP := hChain.1
  have hBu := blockAt_mem_and_bounds hP (hChain.2.2.1 k₂) hu1 huP
  have hBv := blockAt_mem_and_bounds hP (hChain.2.2.1 k₂) hv1 hvP
  dsimp only at hBu hBv
  obtain ⟨X, hX, hXlo, hXhi⟩ := nestedChain_enclosing hChain hle hBu.1
  have hXu : blockAt (chain k₁) u = X :=
    blockAt_eq_of_mem hP (hChain.2.2.1 k₁) hX ⟨by omega, by omega⟩
  rw [heq] at hXlo hXhi
  have hXv : blockAt (chain k₁) v = X :=
    blockAt_eq_of_mem hP (hChain.2.2.1 k₁) hX ⟨by omega, by omega⟩
  exact hXu.trans hXv.symm

theorem lt_partSepScale_iff {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {u v : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P)
    (k : Fin (M + 1)) :
    k.val < partSepScale P chain u v ↔ blockAt (chain k) u = blockAt (chain k) v := by
  have hP := hChain.1
  unfold partSepScale
  have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
  simp only [hcond, ↓reduceIte]
  rcases hfind : (List.finRange M).find?
      (fun ℓ : Fin M => decide (blockAt (chain ℓ.succ) u ≠ blockAt (chain ℓ.succ) v)) with _ | i
  · simp only [Nat.lt_succ_iff.mpr (Nat.le_of_lt_succ k.isLt), true_iff]
    by_cases hk0 : k.val = 0
    · have hk : k = 0 := Fin.ext hk0
      subst hk
      have h0u := (blockAt_mem_and_bounds hP (hChain.2.2.1 0) hu1 huP).1
      have h0v := (blockAt_mem_and_bounds hP (hChain.2.2.1 0) hv1 hvP).1
      rw [hChain.2.1] at h0u h0v ⊢
      exact (List.mem_singleton.mp h0u).trans (List.mem_singleton.mp h0v).symm
    · let idx : Fin M := ⟨k.val - 1, by omega⟩
      have hsucc : idx.succ = k := Fin.ext (by simp [idx]; omega)
      have hmem : idx ∈ List.finRange M := List.mem_finRange idx
      have hfalse := List.find?_eq_none.mp hfind idx hmem
      rw [← hsucc]
      simpa using hfalse
  · dsimp only
    obtain ⟨hi_true, as, bs, hsplit, has_false⟩ := List.find?_eq_some_iff_append.mp hfind
    have hi_ne : blockAt (chain i.succ) u ≠ blockAt (chain i.succ) v :=
      of_decide_eq_true hi_true
    constructor
    · intro hklt
      by_cases hk0 : k.val = 0
      · have hk : k = 0 := Fin.ext hk0
        subst hk
        have h0u := (blockAt_mem_and_bounds hP (hChain.2.2.1 0) hu1 huP).1
        have h0v := (blockAt_mem_and_bounds hP (hChain.2.2.1 0) hv1 hvP).1
        rw [hChain.2.1] at h0u h0v ⊢
        exact (List.mem_singleton.mp h0u).trans (List.mem_singleton.mp h0v).symm
      · let idx : Fin M := ⟨k.val - 1, by omega⟩
        have hsucc : idx.succ = k := Fin.ext (by simp [idx]; omega)
        have hidx_lt : idx < i := Fin.lt_def.mpr (by simp [idx]; omega)
        have hpw : (List.finRange M).Pairwise (· < ·) := List.pairwise_lt_finRange M
        rw [hsplit] at hpw
        have hmem : idx ∈ as ++ i :: bs := hsplit ▸ List.mem_finRange idx
        rcases List.mem_append.mp hmem with hin_as | hin_ibs
        · have hf := has_false idx hin_as
          rw [← hsucc]
          simpa using hf
        · exfalso
          rcases List.mem_cons.mp hin_ibs with heq_idx | hin_bs
          · rw [heq_idx] at hidx_lt; exact lt_irrefl _ hidx_lt
          · have hpw_tail := (List.pairwise_append.mp hpw).2.1
            have hi_lt_idx : i < idx := (List.pairwise_cons.mp hpw_tail).1 idx hin_bs
            exact lt_asymm hidx_lt hi_lt_idx
    · intro heq
      by_contra hge
      have hle_fin : i.succ ≤ k := Fin.le_iff_val_le_val.mpr (by simp; omega)
      exact hi_ne (nestedChain_blockAt_eq_mono hChain hle_fin hu1 huP hv1 hvP heq)

theorem partSepScale_bounds {M : ℕ} (P : ℕ) (chain : Fin (M + 1) → List IntervalBlock)
    {u v : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P) :
    1 ≤ partSepScale P chain u v ∧ partSepScale P chain u v ≤ M + 1 := by
  unfold partSepScale
  have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
  simp only [hcond, ↓reduceIte]
  split
  · next ℓ _ => exact ⟨by omega, by omega⟩
  · exact ⟨by omega, le_rfl⟩

theorem partSepScale_ultrametric {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {a b c : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ P + 1) :
    partSepScale P chain a c =
      min (partSepScale P chain a b) (partSepScale P chain b c) := by
  have hP := hChain.1
  by_cases hcP : c ≤ P
  · have hbP : b ≤ P := by omega
    have haP : a ≤ P := by omega
    have hbnd_ac := partSepScale_bounds P chain ha haP (by omega) hcP
    have hbnd_ab := partSepScale_bounds P chain ha haP (by omega) hbP
    have hbnd_bc := partSepScale_bounds P chain (by omega) hbP (by omega) hcP
    have hall : ∀ k : Fin (M + 1),
        (k.val < partSepScale P chain a c ↔
          k.val < min (partSepScale P chain a b) (partSepScale P chain b c)) := by
      intro k
      rw [lt_min_iff,
          lt_partSepScale_iff hChain ha haP (by omega) hcP k,
          lt_partSepScale_iff hChain ha haP (by omega) hbP k,
          lt_partSepScale_iff hChain (by omega) hbP (by omega) hcP k]
      exact blockAt_contiguous_iff hP (hChain.2.2.1 k) ha hab hbc hcP
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk : partSepScale P chain a c < M + 1 := by omega
      exact lt_irrefl _ ((hall ⟨partSepScale P chain a c, hk⟩).mpr hlt)
    · set m := min (partSepScale P chain a b) (partSepScale P chain b c)
      have hm : m < M + 1 := by omega
      exact lt_irrefl _ ((hall ⟨m, hm⟩).mp hgt)
  · have hc_top : c = P + 1 := by omega
    subst hc_top
    have hac0 : partSepScale P chain a (P + 1) = 0 := by simp [partSepScale]
    have hbc0 : partSepScale P chain b (P + 1) = 0 := by simp [partSepScale]
    rw [hac0, hbc0, Nat.min_zero]

/-! ## Section 2: `FoldedPopProcess` Step, `popStepIdx`, `rInt`, and `nextCascadeRot?` -/

theorem mem_iff_mem_keyFinset {α : Type} [DecidableEq α] (t : BinaryTree α) (x : α) :
    x ∈ t ↔ x ∈ keyFinset t := by
  induction t with
  | nil =>
    simp only [keyFinset, Finset.notMem_empty, iff_false]
    intro h; cases h
  | node k l r ihl ihr =>
    simp only [keyFinset, Finset.mem_insert, Finset.mem_union, ← ihl, ← ihr,
      BinaryTree.mem_node_iff]

theorem leftSpine_mem_and_pairwise {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) :
    (∀ x ∈ leftSpine t, x ∈ t) ∧ (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    obtain ⟨hmem_l, hpw_l⟩ := ihl (BinaryTree.IsBST_left_of_IsBST ht)
    simp only [leftSpine, List.mem_append, List.mem_singleton]
    refine ⟨?_, ?_⟩
    · rintro x (hxl | rfl)
      · exact BinaryTree.Mem.left (hmem_l x hxl)
      · exact BinaryTree.Mem.here
    · rw [List.pairwise_append]
      refine ⟨hpw_l, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton.mp hy]
      exact BinaryTree.lt_of_IsBST_left l k r ht (hmem_l x hx)

theorem takeThrough_isPrefix {α : Type} [DecidableEq α] :
    ∀ (ls : List α) (b : α), b ∈ ls → takeThrough ls b <+: ls
  | [], _, hb => by cases hb
  | x :: xs, b, hb => by
    unfold takeThrough
    by_cases hxb : x = b
    · simp [hxb]
    · simp only [hxb, ↓reduceIte]
      rcases List.mem_cons.mp hb with rfl | hbxs
      · exact (hxb rfl).elim
      · obtain ⟨rest, hrest⟩ := takeThrough_isPrefix xs b hbxs
        exact ⟨rest, by simp [hrest]⟩

theorem stateAt_zero {P : ℕ} (proc : FoldedPopProcess P) :
    proc.stateAt 0 = (.nil, none) := by
  simp [FoldedPopProcess.stateAt]

theorem stateAt_length {P : ℕ} (proc : FoldedPopProcess P) :
    proc.stateAt proc.steps.length = (.nil, none) := by
  simp [FoldedPopProcess.stateAt, proc.hEndEmpty]

theorem stateAt_succ {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ)
    (hτ : τ < proc.steps.length) :
    proc.stateAt (τ + 1) = (proc.steps[τ]).step (proc.stateAt τ) := by
  unfold FoldedPopProcess.stateAt
  rw [List.take_succ_eq_append_getElem hτ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem valid_stepAt {P : ℕ} (proc : FoldedPopProcess P) :
    ∀ (τ : ℕ) (hτ : τ < proc.steps.length), (proc.steps[τ]).Valid P (proc.stateAt τ) := by
  suffices ∀ (xs : List FoldedOp) (st : BinaryTree ℕ × Option ℕ),
      ValidFoldedOps P st xs →
      ∀ (τ : ℕ) (hτ : τ < xs.length), (xs[τ]).Valid P ((xs.take τ).foldl FoldedOp.step st) from
    this proc.steps (.nil, none) proc.hValid
  intro xs
  induction xs with
  | nil => intro _ _ τ hτ; simp at hτ
  | cons op rest ih =>
    intro st ⟨hval, hrest⟩ τ hτ
    cases τ with
    | zero => simpa using hval
    | succ τ' =>
      simp only [List.length_cons] at hτ
      simpa [List.take_succ_cons] using ih (op.step st) hrest τ' (by omega)

/-- FilterMap order helper on `proc.hPopSeq`: relates `.pop s` occurrences to `List.range' 1 P`. -/
def popKey? : FoldedOp → Option ℕ
  | .pop s => some s
  | _ => none

theorem popKey?_eq_some_iff {op : FoldedOp} {s : ℕ} :
    popKey? op = some s ↔ op = .pop s := by
  cases op <;> simp [popKey?]

theorem range'_pairwise_lt (a n : ℕ) : (List.range' a n).Pairwise (· < ·) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    simp only [List.range'_succ, List.pairwise_cons]
    refine ⟨?_, ih (a + 1)⟩
    intro x hx
    rw [List.mem_range'_1] at hx
    omega

theorem pop_step_lt_imp_key_lt {P : ℕ} (proc : FoldedPopProcess P)
    {τ₁ τ₂ s₁ s₂ : ℕ} (hlt : τ₁ < τ₂) (hτ₂ : τ₂ < proc.steps.length)
    (h₁ : proc.steps[τ₁]? = some (.pop s₁)) (h₂ : proc.steps[τ₂]? = some (.pop s₂)) :
    s₁ < s₂ := by
  have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
  have hsplit1 : proc.steps =
      proc.steps.take τ₁ ++ proc.steps[τ₁] :: proc.steps.drop (τ₁ + 1) := by
    conv_lhs => rw [← List.take_append_drop τ₁ proc.steps]
    rw [List.cons_getElem_drop_succ (h := by omega)]
  have hd_len : τ₂ - (τ₁ + 1) < (proc.steps.drop (τ₁ + 1)).length := by simp; omega
  have hsplit2 : proc.steps.drop (τ₁ + 1) =
      (proc.steps.drop (τ₁ + 1)).take (τ₂ - (τ₁ + 1)) ++
        (proc.steps.drop (τ₁ + 1))[τ₂ - (τ₁ + 1)] ::
          (proc.steps.drop (τ₁ + 1)).drop (τ₂ - (τ₁ + 1) + 1) := by
    conv_lhs => rw [← List.take_append_drop (τ₂ - (τ₁ + 1)) (proc.steps.drop (τ₁ + 1))]
    rw [List.cons_getElem_drop_succ (h := hd_len)]
  have hg1 : proc.steps[τ₁] = .pop s₁ := by
    rw [List.getElem?_eq_getElem (by omega)] at h₁; exact Option.some.inj h₁
  have hg2 : (proc.steps.drop (τ₁ + 1))[τ₂ - (τ₁ + 1)] = .pop s₂ := by
    rw [List.getElem_drop]
    have hidx : τ₁ + 1 + (τ₂ - (τ₁ + 1)) = τ₂ := by omega
    simp only [hidx]
    rw [List.getElem?_eq_getElem hτ₂] at h₂
    exact Option.some.inj h₂
  rw [hsplit2] at hsplit1
  have hpw := range'_pairwise_lt 1 P
  rw [← hseq, hsplit1] at hpw
  simp only [List.filterMap_append, List.filterMap_cons, hg1, hg2, popKey?] at hpw
  have htail1 := (List.pairwise_append.mp hpw).2.1
  rw [List.pairwise_cons] at htail1
  exact htail1.1 s₂ (by simp)

theorem popStepIdx_spec {P : ℕ} (proc : FoldedPopProcess P) {s : ℕ}
    (hs1 : 1 ≤ s) (hsP : s ≤ P) :
    proc.popStepIdx s < proc.steps.length ∧
    proc.steps[proc.popStepIdx s]? = some (.pop s) := by
  have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
  have hmem_range : s ∈ List.range' 1 P := by
    rw [List.mem_range'_1]
    omega
  rw [← hseq, List.mem_filterMap] at hmem_range
  obtain ⟨op, hop_mem, hop_eq⟩ := hmem_range
  rw [popKey?_eq_some_iff] at hop_eq
  subst hop_eq
  unfold FoldedPopProcess.popStepIdx
  have hex : ∃ op ∈ proc.steps, (op == FoldedOp.pop s) = true :=
    ⟨.pop s, hop_mem, by simp⟩
  have hlt : proc.steps.findIdx (fun op => op == FoldedOp.pop s) < proc.steps.length :=
    List.findIdx_lt_length_of_exists hex
  have hget : (proc.steps[proc.steps.findIdx (fun op => op == FoldedOp.pop s)] == .pop s) = true :=
    List.findIdx_getElem (w := hlt)
  have heq : proc.steps[proc.steps.findIdx (fun op => op == FoldedOp.pop s)] = .pop s :=
    beq_iff_eq.mp hget
  exact ⟨hlt, by rw [List.getElem?_eq_getElem hlt, heq]⟩

theorem eq_popStepIdx_of_getElem? {P : ℕ} (proc : FoldedPopProcess P) {τ s : ℕ}
    (h : proc.steps[τ]? = some (.pop s)) :
    1 ≤ s ∧ s ≤ P ∧ τ = proc.popStepIdx s := by
  have hτ : τ < proc.steps.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  have hg : proc.steps[τ] = .pop s := by
    rw [List.getElem?_eq_getElem hτ] at h; exact Option.some.inj h
  have hmem_op : FoldedOp.pop s ∈ proc.steps := hg ▸ List.getElem_mem hτ
  have hmem_range : s ∈ List.range' 1 P := by
    rw [← proc.hPopSeq, List.mem_filterMap]
    exact ⟨.pop s, hmem_op, rfl⟩
  rw [List.mem_range'_1] at hmem_range
  have hs1 : 1 ≤ s := by omega
  have hsP : s ≤ P := by omega
  obtain ⟨hlt_idx, hget_idx⟩ := popStepIdx_spec proc hs1 hsP
  refine ⟨hs1, hsP, ?_⟩
  rcases lt_trichotomy τ (proc.popStepIdx s) with hlt | heq | hgt
  · exfalso; exact lt_irrefl _ (pop_step_lt_imp_key_lt proc hlt hlt_idx h hget_idx)
  · exact heq
  · exfalso; exact lt_irrefl _ (pop_step_lt_imp_key_lt proc hgt hτ hget_idx h)

theorem popStepIdx_strictMono {P : ℕ} (proc : FoldedPopProcess P) {s₁ s₂ : ℕ}
    (h1 : 1 ≤ s₁) (h12 : s₁ < s₂) (h2 : s₂ ≤ P) :
    proc.popStepIdx s₁ < proc.popStepIdx s₂ := by
  obtain ⟨hlt1, hget1⟩ := popStepIdx_spec proc h1 (by omega)
  obtain ⟨hlt2, hget2⟩ := popStepIdx_spec proc (by omega) h2
  rcases lt_trichotomy (proc.popStepIdx s₁) (proc.popStepIdx s₂) with hlt | heq | hgt
  · exact hlt
  · rw [heq] at hget1
    rw [hget1] at hget2
    cases hget2
    omega
  · exfalso
    have := pop_step_lt_imp_key_lt proc hgt hlt1 hget2 hget1
    omega

/-- Characterize membership in `collectFoldedPopRots`. -/
theorem mem_collectFoldedPopRots_iff :
    ∀ (xs : List FoldedOp) (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (e : InternalPopRot),
      e ∈ collectFoldedPopRots idx st xs ↔
        ∃ (k : ℕ) (hk : k < xs.length),
          e ∈ foldedPopRotsAt (idx + k) ((xs.take k).foldl FoldedOp.step st) (xs[k]'hk)
  | [], _, _, _ => by simp [collectFoldedPopRots]
  | op :: rest, idx, st, e => by
    simp only [collectFoldedPopRots, List.mem_append, mem_collectFoldedPopRots_iff rest]
    constructor
    · rintro (h0 | ⟨k, hk, he⟩)
      · exact ⟨0, by simp, by simpa using h0⟩
      · refine ⟨k + 1, by simp [hk], ?_⟩
        have hadd : idx + (k + 1) = idx + 1 + k := by omega
        rw [hadd]
        simpa [List.take_succ_cons] using he
    · rintro ⟨k, hk, he⟩
      cases k with
      | zero => exact Or.inl (by simpa using he)
      | succ k' =>
        simp only [List.length_cons] at hk
        refine Or.inr ⟨k', by omega, ?_⟩
        have hadd : idx + 1 + k' = idx + (k' + 1) := by omega
        rw [hadd]
        simpa [List.take_succ_cons] using he

/-- Detailed structural breakdown of every `e ∈ proc.rInt`. -/
theorem mem_rInt_props {P : ℕ} (proc : FoldedPopProcess P) {e : InternalPopRot}
    (he : e ∈ proc.rInt) :
    e.stepIdx < proc.steps.length ∧
    1 ≤ e.s ∧ e.s ≤ P ∧
    e.stepIdx = proc.popStepIdx e.s ∧
    proc.steps[e.stepIdx]? = some (.pop e.s) ∧
    1 ≤ e.j ∧ e.j ≤ e.h ∧
    ∃ b : ℕ, proc.b1At e.stepIdx = some b ∧ b ∈ leftSpine (proc.treeAt e.stepIdx) ∧
      let sub := takeThrough (leftSpine (proc.treeAt e.stepIdx)) b
      e.h = (sub.length - 1 - 1) / 2 ∧
      ∃ hlen : 2 * e.j + 1 < sub.length,
      e = {
        stepIdx := e.stepIdx
        s := e.s
        j := e.j
        h := e.h
        x := sub[2 * e.j - 1]'(by omega)
        y := sub[2 * e.j]'(by omega)
        z := sub[2 * e.j + 1]'hlen
      } := by
  unfold FoldedPopProcess.rInt at he
  rw [List.mem_toFinset, mem_collectFoldedPopRots_iff] at he
  obtain ⟨τ, hτ, hrot⟩ := he
  simp only [Nat.zero_add] at hrot
  have hval := valid_stepAt proc τ hτ
  rcases hop : proc.steps[τ] with w | _ | ⟨u, v⟩ | s
  · rw [hop] at hrot; simp [foldedPopRotsAt] at hrot
  · rw [hop] at hrot; simp [foldedPopRotsAt] at hrot
  · rw [hop] at hrot; simp [foldedPopRotsAt] at hrot
  · rw [hop] at hrot hval
    obtain ⟨b, _, _, hb_eq, hb_mem⟩ := hval
    have hst_eq : (proc.steps.take τ).foldl FoldedOp.step (.nil, none) = proc.stateAt τ := rfl
    rw [hst_eq] at hrot
    unfold foldedPopRotsAt at hrot
    rw [hb_eq] at hrot
    dsimp only at hrot
    rw [List.mem_filterMap] at hrot
    obtain ⟨idx, hidx_mem, hidx_eq⟩ := hrot
    rw [List.mem_range] at hidx_mem
    have htree_eq : (proc.stateAt τ).1 = proc.treeAt τ := rfl
    rw [htree_eq] at hidx_mem hidx_eq
    set sub := takeThrough (leftSpine (proc.treeAt τ)) b
    set h := (sub.length - 1 - 1) / 2
    have h2j1 : 2 * (idx + 1) + 1 < sub.length := by omega
    have hx_some : sub[2 * (idx + 1) - 1]? = some (sub[2 * (idx + 1) - 1]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hy_some : sub[2 * (idx + 1)]? = some (sub[2 * (idx + 1)]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hz_some : sub[2 * (idx + 1) + 1]? = some (sub[2 * (idx + 1) + 1]'(by omega)) :=
      List.getElem?_eq_getElem h2j1
    change (match sub[2 * (idx + 1) - 1]?, sub[2 * (idx + 1)]?, sub[2 * (idx + 1) + 1]? with
      | some x, some y, some z =>
        some { stepIdx := τ, s := s, j := idx + 1, h := h, x := x, y := y, z := z }
      | _, _, _ => none) = some e at hidx_eq
    rw [hx_some, hy_some, hz_some] at hidx_eq
    have he_struct := (Option.some.inj hidx_eq).symm
    have hstep_eq : e.stepIdx = τ := by rw [he_struct]
    have hs_eq : e.s = s := by rw [he_struct]
    have hj_eq : e.j = idx + 1 := by rw [he_struct]
    have hh_eq : e.h = h := by rw [he_struct]
    have hget? : proc.steps[τ]? = some (.pop s) := by
      rw [List.getElem?_eq_getElem hτ, hop]
    obtain ⟨hs1, hsP, hτ_pop⟩ := eq_popStepIdx_of_getElem? proc hget?
    refine ⟨hstep_eq ▸ hτ, hs_eq ▸ hs1, hs_eq ▸ hsP, by rw [hstep_eq, hs_eq, hτ_pop],
      ?_, by omega, by omega, b, ?_, ?_, ?_⟩
    · rwa [hstep_eq, hs_eq]
    · rwa [FoldedPopProcess.b1At, hstep_eq]
    · rwa [FoldedPopProcess.treeAt, hstep_eq]
    · dsimp only
      refine ⟨by simpa [sub, h, hstep_eq] using hh_eq,
        ⟨by simpa [sub, hstep_eq, hj_eq] using h2j1, ?_⟩⟩
      conv_lhs => rw [he_struct]
      simp [sub, hstep_eq, hs_eq, hj_eq, hh_eq]

theorem rInt_mem_leftSpine {P : ℕ} (proc : FoldedPopProcess P) {e : InternalPopRot}
    (he : e ∈ proc.rInt) :
    e.x ∈ leftSpine (proc.treeAt e.stepIdx) ∧
    e.y ∈ leftSpine (proc.treeAt e.stepIdx) ∧
    e.z ∈ leftSpine (proc.treeAt e.stepIdx) := by
  obtain ⟨_, _, _, _, _, _, _, b, _, hb_mem, _, hlen, he_eq⟩ := mem_rInt_props proc he
  set sub := takeThrough (leftSpine (proc.treeAt e.stepIdx)) b
  have hpref : sub <+: leftSpine (proc.treeAt e.stepIdx) := takeThrough_isPrefix _ b hb_mem
  have hx : e.x = sub[2 * e.j - 1]'(by omega) := by conv_lhs => rw [he_eq]
  have hy : e.y = sub[2 * e.j]'(by omega) := by conv_lhs => rw [he_eq]
  have hz : e.z = sub[2 * e.j + 1]'hlen := by conv_lhs => rw [he_eq]
  exact ⟨hx ▸ hpref.mem (List.getElem_mem _),
         hy ▸ hpref.mem (List.getElem_mem _),
         hz ▸ hpref.mem (List.getElem_mem _)⟩

theorem rInt_ext_stepIdx_j {P : ℕ} (proc : FoldedPopProcess P) {e₁ e₂ : InternalPopRot}
    (h₁ : e₁ ∈ proc.rInt) (h₂ : e₂ ∈ proc.rInt)
    (hstep : e₁.stepIdx = e₂.stepIdx) (hj : e₁.j = e₂.j) :
    e₁ = e₂ := by
  obtain ⟨_, _, _, _, hpop1, _, _, b₁, hb1, _, hh1, _, heq1⟩ := mem_rInt_props proc h₁
  obtain ⟨_, _, _, _, hpop2, _, _, b₂, hb2, _, hh2, _, heq2⟩ := mem_rInt_props proc h₂
  have hs_eq : e₁.s = e₂.s := by
    rw [hstep, hpop2] at hpop1
    exact (FoldedOp.pop.inj (Option.some.inj hpop1)).symm
  have hb_eq : b₁ = b₂ := by
    rw [hstep, hb2] at hb1
    exact (Option.some.inj hb1).symm
  subst hb_eq
  conv_lhs => rw [heq1]
  conv_rhs => rw [heq2]
  simp only [hstep, hs_eq, hj, hh1, hh2]

theorem rInt_same_s_step_and_h {P : ℕ} (proc : FoldedPopProcess P) {e₁ e₂ : InternalPopRot}
    (h₁ : e₁ ∈ proc.rInt) (h₂ : e₂ ∈ proc.rInt) (hs : e₁.s = e₂.s) :
    e₁.stepIdx = e₂.stepIdx ∧ e₁.h = e₂.h := by
  obtain ⟨_, _, _, hst1, _, _, _, b₁, hb1, _, hh1, _, _⟩ := mem_rInt_props proc h₁
  obtain ⟨_, _, _, hst2, _, _, _, b₂, hb2, _, hh2, _, _⟩ := mem_rInt_props proc h₂
  have hstep : e₁.stepIdx = e₂.stepIdx := by rw [hst1, hst2, hs]
  have hb_eq : b₁ = b₂ := by rw [hstep, hb2] at hb1; exact (Option.some.inj hb1).symm
  subst hb_eq
  exact ⟨hstep, by rw [hh1, hh2, hstep]⟩

theorem rInt_same_step_lt {P : ℕ} (proc : FoldedPopProcess P)
    (hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST)
    {e₁ e₂ : InternalPopRot} (h₁ : e₁ ∈ proc.rInt) (h₂ : e₂ ∈ proc.rInt)
    (hstep : e₁.stepIdx = e₂.stepIdx) (hj : e₁.j < e₂.j) :
    e₁.z ≤ e₂.x ∧ e₂.x < e₂.y ∧ e₂.y < e₂.z := by
  obtain ⟨hτ, _, _, _, _, _, _, b₁, hb1, hb_mem, _, hlen1, heq1⟩ := mem_rInt_props proc h₁
  obtain ⟨_, _, _, _, _, _, _, b₂, hb2, _, _, hlen2, heq2⟩ := mem_rInt_props proc h₂
  have hb_eq : b₁ = b₂ := by rw [hstep, hb2] at hb1; exact (Option.some.inj hb1).symm
  subst hb_eq
  set τ := e₁.stepIdx
  have hstep' : e₂.stepIdx = τ := hstep.symm
  have hpw_ls := (leftSpine_mem_and_pairwise (hBST τ (le_of_lt hτ))).2
  obtain ⟨rest, hrest⟩ := takeThrough_isPrefix (leftSpine (proc.treeAt τ)) b₁ hb_mem
  rw [← hrest] at hpw_ls
  have hpw_sub := (List.pairwise_append.mp hpw_ls).1
  set sub := takeThrough (leftSpine (proc.treeAt τ)) b₁
  have hlen2' : 2 * e₂.j + 1 < sub.length := by simpa [sub, hstep'] using hlen2
  have hz1 : e₁.z = sub[2 * e₁.j + 1]'(hlen1) := by conv_lhs => rw [heq1]
  have hx2 : e₂.x = sub[2 * e₂.j - 1]'(by omega) := by
    conv_lhs => rw [heq2]; simp [sub, hstep']
  have hy2 : e₂.y = sub[2 * e₂.j]'(by omega) := by
    conv_lhs => rw [heq2]; simp [sub, hstep']
  have hz2 : e₂.z = sub[2 * e₂.j + 1]'hlen2' := by
    conv_lhs => rw [heq2]; simp [sub, hstep']
  have mono : ∀ i₁ i₂ : ℕ, (hi₂ : i₂ < sub.length) → (hlt : i₁ < i₂) →
      sub[i₁]'(Nat.lt_trans hlt hi₂) < sub[i₂]'hi₂ :=
    fun i₁ i₂ hi₂ hlt => pairwise_getElem_lt hpw_sub i₁ i₂ hi₂ hlt
  refine ⟨?_, ?_, ?_⟩
  · rw [hz1, hx2]
    by_cases hnext : 2 * e₁.j + 1 = 2 * e₂.j - 1
    · simp [hnext]
    · exact le_of_lt (mono _ _ (by omega) (by omega))
  · rw [hx2, hy2]; exact mono _ _ (by omega) (by omega)
  · rw [hy2, hz2]; exact mono _ _ hlen2' (by omega)

theorem nextCascadeRot?_eq_none_of_top {P : ℕ} (proc : FoldedPopProcess P)
    {e : InternalPopRot} (he : e ∈ proc.rInt) (htop : e.j = e.h) :
    proc.nextCascadeRot? e = none := by
  unfold FoldedPopProcess.nextCascadeRot?
  rw [List.find?_eq_none]
  intro e' he'_mem
  have he' : e' ∈ proc.rInt := List.mem_toFinset.mpr he'_mem
  simp only [Bool.and_eq_true, beq_iff_eq]
  rintro ⟨hstep, hj_eq⟩
  obtain ⟨_, _, _, _, _, _, _, b₁, hb1, _, hh1, _, _⟩ := mem_rInt_props proc he
  obtain ⟨_, _, _, _, _, _, hj2_le, b₂, hb2, _, hh2, _, _⟩ := mem_rInt_props proc he'
  have hb_eq : b₂ = b₁ := by rw [hstep, hb1] at hb2; exact (Option.some.inj hb2).symm
  subst hb_eq
  rw [hstep] at hh2
  omega

theorem nextCascadeRot?_eq_some_of_lt {P : ℕ} (proc : FoldedPopProcess P)
    {e : InternalPopRot} (he : e ∈ proc.rInt) (hlt : e.j < e.h) :
    ∃ eNext ∈ proc.rInt,
      proc.nextCascadeRot? e = some eNext ∧
      eNext.stepIdx = e.stepIdx ∧
      eNext.s = e.s ∧
      eNext.j = e.j + 1 ∧
      eNext.h = e.h ∧
      eNext.x = e.z := by
  obtain ⟨hτ, _, _, _, hpop, _, _, b, hb, _, hh, hlen_e, he_eq⟩ := mem_rInt_props proc he
  -- Construct the `(e.j + 1)`-st rotation at `e.stepIdx`
  have hmem_col : ∃ e₀ ∈ collectFoldedPopRots 0 (.nil, none) proc.steps,
      e₀.stepIdx = e.stepIdx ∧ e₀.j = e.j + 1 := by
    set sub := takeThrough (leftSpine (proc.treeAt e.stepIdx)) b
    have h2 : 2 * (e.j + 1) + 1 < sub.length := by omega
    let cand : InternalPopRot := {
      stepIdx := e.stepIdx
      s := e.s
      j := e.j + 1
      h := e.h
      x := sub[2 * (e.j + 1) - 1]'(by omega)
      y := sub[2 * (e.j + 1)]'(by omega)
      z := sub[2 * (e.j + 1) + 1]'h2
    }
    refine ⟨cand, ?_, rfl, rfl⟩
    rw [mem_collectFoldedPopRots_iff]
    refine ⟨e.stepIdx, hτ, ?_⟩
    simp only [Nat.zero_add]
    have hget : proc.steps[e.stepIdx] = .pop e.s := by
      rw [List.getElem?_eq_getElem hτ] at hpop; exact Option.some.inj hpop
    rw [hget]
    have hst_eq : (proc.steps.take e.stepIdx).foldl FoldedOp.step (.nil, none) =
        proc.stateAt e.stepIdx := rfl
    have hb' : (proc.stateAt e.stepIdx).2 = some b := hb
    have htr' : (proc.stateAt e.stepIdx).1 = proc.treeAt e.stepIdx := rfl
    rw [hst_eq]
    unfold foldedPopRotsAt
    rw [hb', htr']
    dsimp only
    rw [List.mem_filterMap]
    refine ⟨e.j, List.mem_range.mpr (hh ▸ hlt), ?_⟩
    have hx_s : sub[2 * (e.j + 1) - 1]? = some (sub[2 * (e.j + 1) - 1]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hy_s : sub[2 * (e.j + 1)]? = some (sub[2 * (e.j + 1)]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hz_s : sub[2 * (e.j + 1) + 1]? = some (sub[2 * (e.j + 1) + 1]'h2) :=
      List.getElem?_eq_getElem h2
    change (match sub[2 * (e.j + 1) - 1]?, sub[2 * (e.j + 1)]?, sub[2 * (e.j + 1) + 1]? with
      | some x, some y, some z =>
        some { stepIdx := e.stepIdx, s := e.s, j := e.j + 1,
               h := (sub.length - 1 - 1) / 2, x := x, y := y, z := z }
      | _, _, _ => none) = some cand
    rw [hx_s, hy_s, hz_s, ← hh]
  obtain ⟨e₀, he₀_mem, he₀_step, he₀_j⟩ := hmem_col
  have hsome : (proc.nextCascadeRot? e).isSome := by
    unfold FoldedPopProcess.nextCascadeRot?
    rw [List.find?_isSome]
    exact ⟨e₀, he₀_mem, by simp [he₀_step, he₀_j]⟩
  obtain ⟨eNext, hfind⟩ := Option.isSome_iff_exists.mp hsome
  have heNext_rInt : eNext ∈ proc.rInt :=
    List.mem_toFinset.mpr (List.mem_of_find?_eq_some hfind)
  have hpred := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  obtain ⟨_, _, _, _, hpopN, _, _, bN, hbN, _, hhN, hlenN, heN_eq⟩ :=
    mem_rInt_props proc heNext_rInt
  have hs_eq : eNext.s = e.s := by
    rw [hpred.1, hpop] at hpopN
    exact (FoldedOp.pop.inj (Option.some.inj hpopN)).symm
  have hb_eq : bN = b := by
    rw [hpred.1, hb] at hbN
    exact (Option.some.inj hbN).symm
  subst hb_eq
  have hh_eq : eNext.h = e.h := by rw [hpred.1] at hhN; omega
  have hlenN' : 2 * eNext.j + 1 < (takeThrough (leftSpine (proc.treeAt e.stepIdx)) bN).length := by
    simpa [hpred.1] using hlenN
  have hx_eq : eNext.x = e.z := by
    have h1 : eNext.x = (takeThrough (leftSpine (proc.treeAt e.stepIdx)) bN)[2 * eNext.j - 1]'(by omega) := by
      conv_lhs => rw [heN_eq]; simp [hpred.1]
    have h2 : e.z = (takeThrough (leftSpine (proc.treeAt e.stepIdx)) bN)[2 * e.j + 1]'hlen_e := by
      conv_lhs => rw [he_eq]
    rw [h1, h2]
    congr 1
    omega
  exact ⟨eNext, heNext_rInt, hfind, hpred.1, hs_eq, hpred.2, hh_eq, hx_eq⟩

theorem nextCascadeRot?_inj {P : ℕ} (proc : FoldedPopProcess P)
    {e₁ e₂ e' : InternalPopRot} (h₁ : e₁ ∈ proc.rInt) (h₂ : e₂ ∈ proc.rInt)
    (hn₁ : proc.nextCascadeRot? e₁ = some e') (hn₂ : proc.nextCascadeRot? e₂ = some e') :
    e₁ = e₂ := by
  have hp₁ := List.find?_some hn₁
  have hp₂ := List.find?_some hn₂
  simp only [Bool.and_eq_true, beq_iff_eq] at hp₁ hp₂
  exact rInt_ext_stepIdx_j proc h₁ h₂ (by omega) (by omega)

/-! ## Section 3: Lemma 5.2 (`lem_5_2_bucket_leaf`) -/

theorem bLeafPre_card_le {M : ℕ} (P : ℕ) (hP : 1 ≤ P)
    (proc : FoldedPopProcess P)
    (h36 : Ty_lem_3_6_folded_laws)
    (chain : Fin (M + 1) → List IntervalBlock)
    (hChain : IsNestedPartitionChain P chain) :
    (bLeafPre P proc chain).card ≤ P := by
  have hLaws := h36 P hP proc
  have hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST :=
    fun τ hτ => (hLaws.1.1 τ hτ).1
  have hOrdFreeze := hLaws.2.1.2
  set leaves := chain (Fin.last M)
  have hPartM : IsContiguousBlockPartition P leaves := hChain.2.2.1 (Fin.last M)
  -- Inject `bLeafPre` into `Finset.Icc 1 P` via `e ↦ e.y`.
  have hinj : Set.InjOn InternalPopRot.y (bLeafPre P proc chain : Set InternalPopRot) := by
    intro e₁ he₁ e₂ he₂ hy_eq
    rw [Finset.mem_coe, bLeafPre, Finset.mem_filter] at he₁ he₂
    obtain ⟨hr₁, hsep₁, hslo₁⟩ := he₁
    obtain ⟨hr₂, hsep₂, hslo₂⟩ := he₂
    obtain ⟨hs1_1, hsx1, hxy1, hyz1, hzP1, _, hfrz1⟩ := hOrdFreeze e₁ hr₁
    obtain ⟨hs1_2, hsx2, hxy2, hyz2, hzP2, _, hfrz2⟩ := hOrdFreeze e₂ hr₂
    have hQx1_eq_y : blockAt leaves e₁.x = blockAt leaves e₁.y :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) (Fin.last M)).mp
        (by simp [hsep₁])
    have hQx2_eq_y : blockAt leaves e₂.x = blockAt leaves e₂.y :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) (Fin.last M)).mp
        (by simp [hsep₂])
    have hQ12 : blockAt leaves e₁.x = blockAt leaves e₂.x := by
      rw [hQx1_eq_y, hQx2_eq_y, hy_eq]
    have hQ1_bnds := blockAt_mem_and_bounds hP hPartM (u := e₁.x) (by omega) (by omega)
    have hQ2_bnds := blockAt_mem_and_bounds hP hPartM (u := e₂.x) (by omega) (by omega)
    dsimp only at hQ1_bnds hQ2_bnds
    rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with hlt | hsame | hgt
    · exfalso
      have hy_ls2 : e₁.y ∈ leftSpine (proc.treeAt e₂.stepIdx) := by
        rw [hy_eq]; exact (rInt_mem_leftSpine proc hr₂).2.1
      have hnot_in : e₂.stepIdx ∉ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) := by
        intro hmem_icc
        exact hfrz1 e₂.stepIdx hmem_icc e₁.y hy_ls2 ⟨hxy1, hyz1⟩
      rw [Finset.mem_Icc] at hnot_in
      have hgt_pop : proc.popStepIdx e₁.x < e₂.stepIdx := by omega
      have hτ2_eq := (mem_rInt_props proc hr₂).2.2.2.1
      rw [hτ2_eq] at hgt_pop
      have hx1_lt_s2 : e₁.x < e₂.s := by
        by_contra hle
        rcases eq_or_lt_of_le (Nat.le_of_not_lt hle) with heq | hlt_s
        · rw [heq] at hgt_pop; exact lt_irrefl _ hgt_pop
        · exact lt_asymm hgt_pop (popStepIdx_strictMono proc hs1_2 hlt_s (by omega))
      rw [← hQ12] at hslo₂
      omega
    · rcases lt_trichotomy e₁.j e₂.j with hjlt | hjeq | hjgt
      · exfalso
        have := rInt_same_step_lt proc hBST hr₁ hr₂ hsame hjlt
        omega
      · exact rInt_ext_stepIdx_j proc hr₁ hr₂ hsame hjeq
      · exfalso
        have := rInt_same_step_lt proc hBST hr₂ hr₁ hsame.symm hjgt
        omega
    · exfalso
      have hy_ls1 : e₂.y ∈ leftSpine (proc.treeAt e₁.stepIdx) := by
        rw [← hy_eq]; exact (rInt_mem_leftSpine proc hr₁).2.1
      have hnot_in : e₁.stepIdx ∉ Finset.Icc (e₂.stepIdx + 1) (proc.popStepIdx e₂.x) := by
        intro hmem_icc
        exact hfrz2 e₁.stepIdx hmem_icc e₂.y hy_ls1 ⟨hxy2, hyz2⟩
      rw [Finset.mem_Icc] at hnot_in
      have hgt_pop : proc.popStepIdx e₂.x < e₁.stepIdx := by omega
      have hτ1_eq := (mem_rInt_props proc hr₁).2.2.2.1
      rw [hτ1_eq] at hgt_pop
      have hx2_lt_s1 : e₂.x < e₁.s := by
        by_contra hle
        rcases eq_or_lt_of_le (Nat.le_of_not_lt hle) with heq | hlt_s
        · rw [heq] at hgt_pop; exact lt_irrefl _ hgt_pop
        · exact lt_asymm hgt_pop (popStepIdx_strictMono proc hs1_1 hlt_s (by omega))
      rw [hQ12] at hslo₁
      omega
  have hmaps : Set.MapsTo InternalPopRot.y
      (bLeafPre P proc chain : Set InternalPopRot) (Finset.Icc 1 P : Set ℕ) := by
    intro e he
    rw [Finset.mem_coe, bLeafPre, Finset.mem_filter] at he
    obtain ⟨hs1, hsx, hxy, hyz, hzP, _, _⟩ := hOrdFreeze e he.1
    rw [Finset.mem_coe, Finset.mem_Icc]
    omega
  calc (bLeafPre P proc chain).card
      ≤ (Finset.Icc 1 P).card := Finset.card_le_card_of_injOn InternalPopRot.y hmaps hinj
    _ = P := by simp

theorem bLeafExit_card_le {M : ℕ} (P : ℕ) (hP : 1 ≤ P)
    (proc : FoldedPopProcess P)
    (h36 : Ty_lem_3_6_folded_laws)
    (chain : Fin (M + 1) → List IntervalBlock)
    (hChain : IsNestedPartitionChain P chain) :
    (bLeafExit P proc chain).card ≤ P := by
  have hLaws := h36 P hP proc
  have hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST :=
    fun τ hτ => (hLaws.1.1 τ hτ).1
  have hOrd := fun e he => (hLaws.2.1.2 e he).1
  have hPartM : IsContiguousBlockPartition P (chain (Fin.last M)) := hChain.2.2.1 (Fin.last M)
  -- Inject `bLeafExit` into `Finset.Icc 1 P` via `e ↦ e.s`.
  have hinj : Set.InjOn InternalPopRot.s (bLeafExit P proc chain : Set InternalPopRot) := by
    intro e₁ he₁ e₂ he₂ hs_eq
    rw [Finset.mem_coe, bLeafExit, Finset.mem_filter] at he₁ he₂
    obtain ⟨hr₁, hsep₁, hslo₁, hzhi₁⟩ := he₁
    obtain ⟨hr₂, hsep₂, hslo₂, hzhi₂⟩ := he₂
    obtain ⟨hs1_1, hsx1, hxy1, hyz1, hzP1, _, _⟩ := hLaws.2.1.2 e₁ hr₁
    obtain ⟨hs1_2, hsx2, hxy2, hyz2, hzP2, _, _⟩ := hLaws.2.1.2 e₂ hr₂
    have hstep : e₁.stepIdx = e₂.stepIdx := by
      rw [(mem_rInt_props proc hr₁).2.2.2.1, (mem_rInt_props proc hr₂).2.2.2.1, hs_eq]
    have hQx1 := blockAt_mem_and_bounds hP hPartM (u := e₁.x) (by omega) (by omega)
    have hQx2 := blockAt_mem_and_bounds hP hPartM (u := e₂.x) (by omega) (by omega)
    dsimp only at hQx1 hQx2
    have hQ1_eq_s : blockAt (chain (Fin.last M)) e₁.x = blockAt (chain (Fin.last M)) e₁.s :=
      (blockAt_eq_of_mem hP hPartM hQx1.1 ⟨hslo₁, by omega⟩).symm
    have hQ2_eq_s : blockAt (chain (Fin.last M)) e₂.x = blockAt (chain (Fin.last M)) e₂.s :=
      (blockAt_eq_of_mem hP hPartM hQx2.1 ⟨hslo₂, by omega⟩).symm
    have hQ12 : blockAt (chain (Fin.last M)) e₁.x = blockAt (chain (Fin.last M)) e₂.x := by
      rw [hQ1_eq_s, hQ2_eq_s, hs_eq]
    have hQy1 : blockAt (chain (Fin.last M)) e₁.x = blockAt (chain (Fin.last M)) e₁.y :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) (Fin.last M)).mp
        (by simp [hsep₁])
    have hQy2 : blockAt (chain (Fin.last M)) e₂.x = blockAt (chain (Fin.last M)) e₂.y :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) (Fin.last M)).mp
        (by simp [hsep₂])
    have hy1_le : e₁.y ≤ (blockAt (chain (Fin.last M)) e₁.x).hi := by
      rw [hQy1]
      exact (blockAt_mem_and_bounds hP hPartM (u := e₁.y) (by omega) (by omega)).2.2.1
    have hy2_le : e₂.y ≤ (blockAt (chain (Fin.last M)) e₁.x).hi := by
      rw [hQ12, hQy2]
      exact (blockAt_mem_and_bounds hP hPartM (u := e₂.y) (by omega) (by omega)).2.2.1
    rw [← hQ12] at hzhi₂
    rcases lt_trichotomy e₁.j e₂.j with hjlt | hjeq | hjgt
    · exfalso
      have := rInt_same_step_lt proc hBST hr₁ hr₂ hstep hjlt
      omega
    · exact rInt_ext_stepIdx_j proc hr₁ hr₂ hstep hjeq
    · exfalso
      have := rInt_same_step_lt proc hBST hr₂ hr₁ hstep.symm hjgt
      omega
  have hmaps : Set.MapsTo InternalPopRot.s
      (bLeafExit P proc chain : Set InternalPopRot) (Finset.Icc 1 P : Set ℕ) := by
    intro e he
    rw [Finset.mem_coe, bLeafExit, Finset.mem_filter] at he
    obtain ⟨_, hs1, hsP, _⟩ := mem_rInt_props proc he.1
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨hs1, hsP⟩
  calc (bLeafExit P proc chain).card
      ≤ (Finset.Icc 1 P).card := Finset.card_le_card_of_injOn InternalPopRot.s hmaps hinj
    _ = P := by simp

theorem bLeaf_card_split {M : ℕ} (P : ℕ)
    (proc : FoldedPopProcess P) (chain : Fin (M + 1) → List IntervalBlock) :
    (bLeaf P proc chain).card =
      (bLeafPre P proc chain).card + (bLeafExit P proc chain).card +
        (bLeafAct P proc chain).card := by
  have hdisj1 : Disjoint (bLeafPre P proc chain) (bLeafExit P proc chain) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [bLeafPre, bLeafExit, Finset.mem_filter] at h1 h2
    omega
  have hdisj2 : Disjoint (bLeafPre P proc chain ∪ bLeafExit P proc chain)
      (bLeafAct P proc chain) := by
    rw [Finset.disjoint_left]
    intro e h12 h3
    simp only [Finset.mem_union, bLeafPre, bLeafExit, bLeafAct, Finset.mem_filter] at h12 h3
    rcases h12 with h1 | h2 <;> omega
  have hunion : bLeaf P proc chain =
      bLeafPre P proc chain ∪ bLeafExit P proc chain ∪ bLeafAct P proc chain := by
    ext e
    simp only [Finset.mem_union, bLeaf, bLeafPre, bLeafExit, bLeafAct, Finset.mem_filter]
    constructor
    · rintro ⟨hr, hsep⟩
      set Q := blockAt (chain (Fin.last M)) e.x
      by_cases hs : e.s < Q.lo
      · exact Or.inl (Or.inl ⟨hr, hsep, hs⟩)
      · by_cases hz : Q.hi < e.z
        · exact Or.inl (Or.inr ⟨hr, hsep, by omega, hz⟩)
        · exact Or.inr ⟨hr, hsep, by omega, by omega⟩
    · rintro ((⟨hr, hsep, _⟩ | ⟨hr, hsep, _⟩) | ⟨hr, hsep, _⟩) <;> exact ⟨hr, hsep⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]

theorem sum_filter_disjoint_blocks {P : ℕ} (proc : FoldedPopProcess P)
    (hOrd : ∀ e ∈ proc.rInt, e.s < e.z) :
    ∀ (xs : List IntervalBlock),
      xs.Pairwise (fun A B => A.hi < B.lo) →
      (xs.map (fun Q => (proc.rInt.filter (fun e => Q.lo ≤ e.s ∧ e.z ≤ Q.hi)).card)).sum =
        (proc.rInt.filter (fun e => ∃ Q ∈ xs, Q.lo ≤ e.s ∧ e.z ≤ Q.hi)).card
  | [], _ => by simp
  | Q :: rest, List.Pairwise.cons hhead htail => by
    simp only [List.map_cons, List.sum_cons]
    rw [sum_filter_disjoint_blocks proc hOrd rest htail]
    set A := proc.rInt.filter (fun e => Q.lo ≤ e.s ∧ e.z ≤ Q.hi)
    set B := proc.rInt.filter (fun e => ∃ Q' ∈ rest, Q'.lo ≤ e.s ∧ e.z ≤ Q'.hi)
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro e hA hB
      simp only [A, B, Finset.mem_filter] at hA hB
      obtain ⟨hr, hQlo, hQhi⟩ := hA
      obtain ⟨_, Q', hQ'mem, hQ'lo, _⟩ := hB
      have hlt := hhead Q' hQ'mem
      have hsz := hOrd e hr
      omega
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext e
    simp only [A, B, Finset.mem_union, Finset.mem_filter, List.mem_cons, exists_eq_or_imp]
    tauto

theorem lem_5_2_from_subproc
    (hSubproc : ∀ (P L R : ℕ), 1 ≤ L → L ≤ R → R ≤ P →
      ∀ (proc : FoldedPopProcess P),
        (∀ τ ≤ proc.steps.length,
          (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P) →
        ∃ subProc : FoldedPopProcess (R - L + 1),
          subProc.J = (proc.rInt.filter (fun e => L ≤ e.s ∧ e.z ≤ R)).card)
    (h36 : Ty_lem_3_6_folded_laws)
    {M : ℕ} (P : ℕ) (hP : 1 ≤ P) (_hM : 1 ≤ M)
    (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock)
    (hChain : IsNestedPartitionChain P chain) :
    let leaves := chain (Fin.last M)
    (bLeafPre P proc chain).card ≤ P ∧
    (bLeafExit P proc chain).card ≤ P ∧
    (bLeaf P proc chain).card =
      (bLeafPre P proc chain).card + (bLeafExit P proc chain).card +
        (bLeafAct P proc chain).card ∧
    (leaves.map IntervalBlock.size).sum = P ∧
    (∀ Q ∈ leaves, 1 ≤ Q.size) ∧
    ∃ subProcs : (Q : IntervalBlock) → Q ∈ leaves → FoldedPopProcess Q.size,
      (bLeafAct P proc chain).card =
        (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum ∧
      (bLeaf P proc chain).card ≤
        2 * P + (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum := by
  dsimp only
  let leaves := chain (Fin.last M)
  have hPartM : IsContiguousBlockPartition P leaves := hChain.2.2.1 (Fin.last M)
  obtain ⟨hSum, hSizes⟩ := contiguousPartition_sum_and_sizes hP hPartM
  have hPre := bLeafPre_card_le P hP proc h36 chain hChain
  have hExit := bLeafExit_card_le P hP proc h36 chain hChain
  have hSplit := bLeaf_card_split P proc chain
  have hLaws := h36 P hP proc
  have hBSTSub : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => ⟨(hLaws.1.1 τ hτ).1, (hLaws.1.1 τ hτ).2.1⟩
  have hExQ : ∀ (Q : IntervalBlock), Q ∈ leaves →
      ∃ sp : FoldedPopProcess Q.size,
        sp.J = (proc.rInt.filter (fun e => Q.lo ≤ e.s ∧ e.z ≤ Q.hi)).card := by
    intro Q hQ
    obtain ⟨hlo, hle, hhi⟩ := hPartM.1 Q hQ
    have hsz : Q.size = Q.hi - Q.lo + 1 := by simp [IntervalBlock.size, hle]
    rw [hsz]
    exact hSubproc P Q.lo Q.hi hlo hle hhi proc hBSTSub
  let subProcs : (Q : IntervalBlock) → Q ∈ leaves → FoldedPopProcess Q.size :=
    fun Q hQ => Classical.choose (hExQ Q hQ)
  have hSubJ : ∀ (Q : IntervalBlock) (hQ : Q ∈ leaves),
      (subProcs Q hQ).J = (proc.rInt.filter (fun e => Q.lo ≤ e.s ∧ e.z ≤ Q.hi)).card :=
    fun Q hQ => Classical.choose_spec (hExQ Q hQ)
  have hAttachEq :
      (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum =
        (leaves.map (fun Q => (proc.rInt.filter (fun e => Q.lo ≤ e.s ∧ e.z ≤ Q.hi)).card)).sum := by
    have hmap : leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J) =
        leaves.attach.map ((fun Q => (proc.rInt.filter (fun e => Q.lo ≤ e.s ∧ e.z ≤ Q.hi)).card) ∘ Subtype.val) := by
      apply List.map_congr_left
      rintro ⟨Q, hQ⟩ _
      exact hSubJ Q hQ
    rw [hmap, ← List.map_map, List.attach_map_subtype_val]
  have hle_blocks : ∀ C ∈ leaves, C.lo ≤ C.hi := fun C hC => (hPartM.1 C hC).2.1
  have hpair := (consecutiveBlocks_props leaves hle_blocks hPartM.2.1).1
  have hOrd_sz : ∀ e ∈ proc.rInt, e.s < e.z := by
    intro e he
    obtain ⟨_, hsx, hxy, hyz, _⟩ := hLaws.2.1.2 e he
    omega
  have hFilterEq : bLeafAct P proc chain =
      proc.rInt.filter (fun e => ∃ Q ∈ leaves, Q.lo ≤ e.s ∧ e.z ≤ Q.hi) := by
    ext e
    simp only [bLeafAct, Finset.mem_filter]
    constructor
    · rintro ⟨hr, hsep, hlo, hhi⟩
      obtain ⟨hs1, hsx, hxy, hyz, hzP, _, _⟩ := hLaws.2.1.2 e hr
      have hQmem := (blockAt_mem_and_bounds hP hPartM (u := e.x) (by omega) (by omega)).1
      exact ⟨hr, blockAt leaves e.x, hQmem, hlo, hhi⟩
    · rintro ⟨hr, Q, hQ, hlo, hhi⟩
      obtain ⟨hs1, hsx, hxy, hyz, hzP, _, _⟩ := hLaws.2.1.2 e hr
      have hQx : blockAt leaves e.x = Q :=
        blockAt_eq_of_mem hP hPartM hQ ⟨by omega, by omega⟩
      have hQy : blockAt leaves e.y = Q :=
        blockAt_eq_of_mem hP hPartM hQ ⟨by omega, by omega⟩
      have hMlt : M < partSepScale P chain e.x e.y :=
        (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) (Fin.last M)).mpr
          (hQx.trans hQy.symm)
      have hbnd := partSepScale_bounds P chain (u := e.x) (v := e.y)
        (by omega) (by omega) (by omega) (by omega)
      refine ⟨hr, by omega, ?_, ?_⟩
      · change (blockAt leaves e.x).lo ≤ e.s; rw [hQx]; exact hlo
      · change e.z ≤ (blockAt leaves e.x).hi; rw [hQx]; exact hhi
  have hActEq : (bLeafAct P proc chain).card =
      (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum := by
    rw [hAttachEq, sum_filter_disjoint_blocks proc hOrd_sz leaves hpair, hFilterEq]
  refine ⟨hPre, hExit, hSplit, hSum, hSizes, subProcs, hActEq, ?_⟩
  calc (bLeaf P proc chain).card
      = (bLeafPre P proc chain).card + (bLeafExit P proc chain).card +
          (bLeafAct P proc chain).card := hSplit
    _ ≤ P + P + ((chain (Fin.last M)).attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum := by
        rw [← hActEq]; omega
    _ = 2 * P + ((chain (Fin.last M)).attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum := by
        omega

/-! ## Section 4: Lemma 5.3 (`lem_5_3_bucket_b1`) -/

abbrev Ty_scaleTree_lca_props :=
  ∀ (r M : ℕ) (T : ScaleTree),
    IsScaleTree r M T →
    ∀ (ℓ₁ ℓ₂ : ℕ), 1 ≤ ℓ₁ → ℓ₁ < ℓ₂ → ℓ₂ ≤ M →
      let ν := lcaScaleTree T ℓ₁ ℓ₂
      let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 0
      let mPrev := mStart T (ν ++ [c₂]) - 1
      let m := mEnd T ν
      ν ∈ internalAddrs T ∧
      ν.length < r ∧
      1 ≤ c₂ ∧ c₂ ≤ numChildren T ν ∧
      1 ≤ mStart T (ν ++ [c₂]) ∧
      ℓ₁ ≤ mPrev ∧ mPrev < ℓ₂ ∧ ℓ₂ ≤ m ∧ m ≤ M ∧
      (∀ ℓ₃ : ℕ, m < ℓ₃ → ℓ₃ ≤ M → (lcaScaleTree T ℓ₁ ℓ₃).length < ν.length)

def sigmaIdxSet {M : ℕ} (T : ScaleTree)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset (List ℕ × ℕ × ℕ) :=
  (internalAddrs T).biUnion (fun ν =>
    let m := mEnd T ν
    if hm : m ≤ M then
      (Finset.Icc 1 (numChildren T ν)).biUnion (fun c₂ =>
        (Finset.range (chain ⟨m, Nat.lt_succ_of_le hm⟩).length).image (fun qIdx => (ν, c₂, qIdx)))
    else ∅)

theorem sigmaIdxSet_card_le {M : ℕ} (T : ScaleTree)
    (chain : Fin (M + 1) → List IntervalBlock) :
    (sigmaIdxSet T chain).card ≤ sigmaScaleTree T chain := by
  unfold sigmaIdxSet sigmaScaleTree
  refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun ν _ => ?_)
  dsimp only
  split_ifs with hm
  · calc ((Finset.Icc 1 (numChildren T ν)).biUnion (fun c₂ =>
            (Finset.range (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩).length).image
              (fun qIdx => (ν, c₂, qIdx)))).card
        ≤ (Finset.Icc 1 (numChildren T ν)).sum (fun c₂ =>
            ((Finset.range (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩).length).image
              (fun qIdx => (ν, c₂, qIdx))).card) := Finset.card_biUnion_le
      _ ≤ (Finset.Icc 1 (numChildren T ν)).sum (fun _ =>
            (Finset.range (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩).length).card) :=
          Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ = numChildren T ν * (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩).length := by simp
  · simp

def b1Tuple {M : ℕ} (P : ℕ) (T : ScaleTree)
    (chain : Fin (M + 1) → List IntervalBlock) (e : InternalPopRot) : List ℕ × ℕ × ℕ :=
  let ℓ₁ := partSepScale P chain e.s e.x
  let ℓ₂ := partSepScale P chain e.x e.y
  let ν := lcaScaleTree T ℓ₁ ℓ₂
  let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 0
  let m := mEnd T ν
  if hm : m ≤ M then
    let blocks := chain ⟨m, Nat.lt_succ_of_le hm⟩
    (ν, c₂, blocks.idxOf (blockAt blocks e.y))
  else (ν, c₂, 0)

theorem b1_routing_bounds
    (hLca : Ty_scaleTree_lca_props)
    {P r M : ℕ} {T : ScaleTree} (hScale : IsScaleTree r M T)
    {proc : FoldedPopProcess P}
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P)
    {e : InternalPopRot} (he : e ∈ b1 P proc chain) :
    let ℓ₁ := partSepScale P chain e.s e.x
    let ℓ₂ := partSepScale P chain e.x e.y
    let ν := lcaScaleTree T ℓ₁ ℓ₂
    let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 0
    let mPrev := mStart T (ν ++ [c₂]) - 1
    let m := mEnd T ν
    ∃ (hm : m ≤ M) (hmPrev : mPrev ≤ M),
      let Q₂ := blockAt (chain ⟨m, Nat.lt_succ_of_le hm⟩) e.y
      let B_prev := blockAt (chain ⟨mPrev, Nat.lt_succ_of_le hmPrev⟩) Q₂.lo
      e ∈ proc.rInt ∧
      ν ∈ internalAddrs T ∧
      ν.length < r ∧
      1 ≤ c₂ ∧ c₂ ≤ numChildren T ν ∧
      ℓ₁ ≤ mPrev ∧ mPrev < ℓ₂ ∧ ℓ₂ ≤ m ∧
      b1Tuple P T chain e ∈ sigmaIdxSet T chain ∧
      Q₂ ∈ chain ⟨m, Nat.lt_succ_of_le hm⟩ ∧
      e.s < B_prev.lo ∧ B_prev.lo ≤ e.x ∧
      e.x < Q₂.lo ∧ Q₂.lo ≤ e.y ∧ e.y ≤ Q₂.hi ∧
      (∀ ℓ₃ : ℕ, m < ℓ₃ → ℓ₃ ≤ M → (lcaScaleTree T ℓ₁ ℓ₃).length < ν.length) := by
  dsimp only
  have hP := hChain.1
  rw [b1, Finset.mem_filter] at he
  obtain ⟨hr, hℓ₁_1, hℓ₁₂, hℓ₂_M⟩ := he
  obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e hr
  set ℓ₁ := partSepScale P chain e.s e.x
  set ℓ₂ := partSepScale P chain e.x e.y
  have hlca := hLca r M T hScale ℓ₁ ℓ₂ hℓ₁_1 hℓ₁₂ hℓ₂_M
  dsimp only at hlca
  obtain ⟨hν_int, hν_len, hc₂_1, hc₂_num, hmStart_1, hℓ₁_mPrev, hmPrev_ℓ₂, hℓ₂_m, hm_M, hdepth⟩ := hlca
  set ν := lcaScaleTree T ℓ₁ ℓ₂
  set c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 0
  set mPrev := mStart T (ν ++ [c₂]) - 1
  set m := mEnd T ν
  have hmPrev_M : mPrev ≤ M := by omega
  refine ⟨hm_M, hmPrev_M, ?_⟩
  let km : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hm_M⟩
  let kp : Fin (M + 1) := ⟨mPrev, Nat.lt_succ_of_le hmPrev_M⟩
  have hkp_le_km : kp ≤ km := Fin.le_iff_val_le_val.mpr (by simp [kp, km]; omega)
  have hQ₂_bnds := blockAt_mem_and_bounds hP (hChain.2.2.1 km) (u := e.y) (by omega) (by omega)
  dsimp only at hQ₂_bnds
  set Q₂ := blockAt (chain km) e.y
  obtain ⟨hQ₂_mem, hQ₂_lo_y, hy_Q₂_hi, hQ₂_lo_1, hQ₂_hi_P⟩ := hQ₂_bnds
  obtain ⟨X_prev, hX_mem, hX_lo, hX_hi⟩ := nestedChain_enclosing hChain hkp_le_km hQ₂_mem
  have hBprev_eq : blockAt (chain kp) Q₂.lo = X_prev :=
    blockAt_eq_of_mem hP (hChain.2.2.1 kp) hX_mem ⟨hX_lo, by omega⟩
  have hBprev_y : blockAt (chain kp) e.y = X_prev :=
    blockAt_eq_of_mem hP (hChain.2.2.1 kp) hX_mem ⟨by omega, by omega⟩
  have hkp_xy : blockAt (chain kp) e.x = blockAt (chain kp) e.y :=
    (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) kp).mp hmPrev_ℓ₂
  have hx_Bprev : X_prev.lo ≤ e.x := by
    have hBx := blockAt_mem_and_bounds hP (hChain.2.2.1 kp) (u := e.x) (by omega) (by omega)
    dsimp only at hBx
    rw [hkp_xy, hBprev_y] at hBx
    exact hBx.2.1
  have hkp_sx_ne : blockAt (chain kp) e.s ≠ blockAt (chain kp) e.x := by
    intro heq
    have hlt := (lt_partSepScale_iff hChain hs1 (by omega) (by omega) (by omega) kp).mpr heq
    simp [kp] at hlt
    omega
  have hs_lt_Bprev : e.s < X_prev.lo := by
    have hlt_blk := blockAt_lt_of_ne hP (hChain.2.2.1 kp) hs1 (le_of_lt hsx) (by omega) hkp_sx_ne
    have hBs := blockAt_mem_and_bounds hP (hChain.2.2.1 kp) (u := e.s) hs1 (by omega)
    dsimp only at hBs
    rw [hkp_xy, hBprev_y] at hlt_blk
    omega
  have hkm_xy_ne : blockAt (chain km) e.x ≠ blockAt (chain km) e.y := by
    intro heq
    have hlt := (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) km).mpr heq
    simp [km] at hlt
    omega
  have hx_lt_Q₂ : e.x < Q₂.lo := by
    have hlt_blk := blockAt_lt_of_ne hP (hChain.2.2.1 km) (by omega) (le_of_lt hxy) (by omega) hkm_xy_ne
    have hBx := blockAt_mem_and_bounds hP (hChain.2.2.1 km) (u := e.x) (by omega) (by omega)
    dsimp only at hBx
    change (blockAt (chain km) e.x).hi < Q₂.lo at hlt_blk
    omega
  have hTuple_mem : b1Tuple P T chain e ∈ sigmaIdxSet T chain := by
    unfold b1Tuple sigmaIdxSet
    simp only [Finset.mem_biUnion]
    refine ⟨ν, hν_int, ?_⟩
    have hm_M' : mEnd T ν ≤ M := hm_M
    have hm_M'' : mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x) (partSepScale P chain e.x e.y)) ≤ M := hm_M
    simp only [hm_M', hm_M'', ↓reduceDIte, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range]
    exact ⟨c₂, ⟨hc₂_1, hc₂_num⟩, (chain km).idxOf Q₂, List.idxOf_lt_length_of_mem hQ₂_mem, rfl⟩
  rw [hBprev_eq]
  exact ⟨hr, hν_int, hν_len, hc₂_1, hc₂_num, hℓ₁_mPrev, hmPrev_ℓ₂, hℓ₂_m,
    hTuple_mem, hQ₂_mem, hs_lt_Bprev, hx_Bprev, hx_lt_Q₂, hQ₂_lo_y, hy_Q₂_hi, hdepth⟩

theorem b1Tuple_same_blocks
    {P : ℕ} {T : ScaleTree} {M : ℕ}
    {chain : Fin (M + 1) → List IntervalBlock}
    {e₁ e₂ : InternalPopRot}
    (htup : b1Tuple P T chain e₁ = b1Tuple P T chain e₂)
    {hm₁ : mEnd T (lcaScaleTree T (partSepScale P chain e₁.s e₁.x) (partSepScale P chain e₁.x e₁.y)) ≤ M}
    (hQ₁_mem : blockAt (chain ⟨_, Nat.lt_succ_of_le hm₁⟩) e₁.y ∈
      chain ⟨_, Nat.lt_succ_of_le hm₁⟩)
    {hm₂ : mEnd T (lcaScaleTree T (partSepScale P chain e₂.s e₂.x) (partSepScale P chain e₂.x e₂.y)) ≤ M}
    (hQ₂_mem : blockAt (chain ⟨_, Nat.lt_succ_of_le hm₂⟩) e₂.y ∈
      chain ⟨_, Nat.lt_succ_of_le hm₂⟩) :
    let ν₁ := lcaScaleTree T (partSepScale P chain e₁.s e₁.x) (partSepScale P chain e₁.x e₁.y)
    let ν₂ := lcaScaleTree T (partSepScale P chain e₂.s e₂.x) (partSepScale P chain e₂.x e₂.y)
    ν₁ = ν₂ ∧
    ((leafAddr T (partSepScale P chain e₁.x e₁.y))[ν₁.length]?).getD 0 =
      ((leafAddr T (partSepScale P chain e₂.x e₂.y))[ν₂.length]?).getD 0 ∧
    blockAt (chain ⟨_, Nat.lt_succ_of_le hm₁⟩) e₁.y =
      blockAt (chain ⟨_, Nat.lt_succ_of_le hm₂⟩) e₂.y := by
  unfold b1Tuple at htup
  simp only [hm₁, hm₂, ↓reduceDIte, Prod.mk.injEq] at htup
  obtain ⟨hν, hc₂, hidx⟩ := htup
  refine ⟨hν, hc₂, ?_⟩
  have hm_eq : mEnd T (lcaScaleTree T (partSepScale P chain e₁.s e₁.x) (partSepScale P chain e₁.x e₁.y)) =
      mEnd T (lcaScaleTree T (partSepScale P chain e₂.s e₂.x) (partSepScale P chain e₂.x e₂.y)) :=
    congrArg (mEnd T) hν
  have hfin_eq : (⟨_, Nat.lt_succ_of_le hm₁⟩ : Fin (M + 1)) = ⟨_, Nat.lt_succ_of_le hm₂⟩ :=
    Fin.ext hm_eq
  set k := (⟨_, Nat.lt_succ_of_le hm₁⟩ : Fin (M + 1))
  have hQ₂_mem' : blockAt (chain k) e₂.y ∈ chain k := by simpa [k, hfin_eq] using hQ₂_mem
  have hidx' : (chain k).idxOf (blockAt (chain k) e₁.y) =
      (chain k).idxOf (blockAt (chain k) e₂.y) := by simpa [k, ← hfin_eq] using hidx
  have hg1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hQ₁_mem)
  have hg2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hQ₂_mem')
  have heq_k : blockAt (chain k) e₁.y = blockAt (chain k) e₂.y := by
    rw [← hg1, ← hg2]
    congr 1
  simpa [k, hfin_eq] using heq_k

/-- Case B2b step-advancement for `e ∈ b1 \ s1`: `eNext` exists and either enters `bLeafPre`
or stays in `b1` with strictly smaller `lcaScaleTree` depth. -/
theorem b1_not_s1_step
    (hLca : Ty_scaleTree_lca_props)
    {P r M : ℕ} {T : ScaleTree} (hScale : IsScaleTree r M T)
    {proc : FoldedPopProcess P}
    (_hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P)
    {e : InternalPopRot} (hb1 : e ∈ b1 P proc chain) (hns1 : e ∉ s1Set P T proc chain) :
    ∃ eNext ∈ proc.rInt,
      proc.nextCascadeRot? e = some eNext ∧
      eNext.stepIdx = e.stepIdx ∧
      eNext.s = e.s ∧
      eNext.j = e.j + 1 ∧
      eNext.x = e.z ∧
      (eNext ∈ bLeafPre P proc chain ∨
        (eNext ∈ b1 P proc chain ∧
          (lcaScaleTree T (partSepScale P chain eNext.s eNext.x)
              (partSepScale P chain eNext.x eNext.y)).length <
            (lcaScaleTree T (partSepScale P chain e.s e.x)
              (partSepScale P chain e.x e.y)).length)) := by
  have hP := hChain.1
  obtain ⟨hm, hmPrev, hr, _, _, _, _, hℓ₁_mPrev, hmPrev_ℓ₂, hℓ₂_m, _,
    hQ₂_mem, hs_Bprev, hBprev_x, hx_Q₂, hQ₂_y, hy_Q₂, hdepth⟩ :=
    b1_routing_bounds hLca hScale hChain hOrd hb1
  obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e hr
  have hj_le := (mem_rInt_props proc hr).2.2.2.2.2.2.1
  -- Unpack `e ∉ s1Set`
  have hnot_cond :
      ¬ ((blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x)
            (partSepScale P chain e.x e.y)), Nat.lt_succ_of_le hm⟩) e.y).hi < e.z ∨
         e.j = e.h ∨
         (proc.nextCascadeRot? e).elim true (fun eNext =>
           decide ((blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x)
             (partSepScale P chain e.x e.y)), Nat.lt_succ_of_le hm⟩) e.y).hi < eNext.y)) = true) := by
    intro hc
    apply hns1
    rw [s1Set, Finset.mem_filter]
    refine ⟨hb1, ?_⟩
    simp only [hm, ↓reduceDIte]
    exact hc
  simp only [not_or, not_lt] at hnot_cond
  obtain ⟨hz_le_Q₂, hj_ne_h, hnext_le⟩ := hnot_cond
  have hj_lt_h : e.j < e.h := by omega
  obtain ⟨eNext, hrN, hfindN, hstepN, hsN, hjN, _, hxN⟩ :=
    nextCascadeRot?_eq_some_of_lt proc hr hj_lt_h
  rw [hfindN] at hnext_le
  simp only [Option.elim_some, Bool.not_eq_true, decide_eq_false_iff_not, not_lt] at hnext_le
  obtain ⟨hs1N, hsxN, hxyN, hyzN, hzPN⟩ := hOrd eNext hrN
  let km : Fin (M + 1) := ⟨mEnd T (lcaScaleTree T (partSepScale P chain e.s e.x)
    (partSepScale P chain e.x e.y)), Nat.lt_succ_of_le hm⟩
  set Q₂ := blockAt (chain km) e.y
  -- Both `eNext.x = e.z` and `eNext.y` lie in `Q₂`, so `m < sep(eNext.x, eNext.y)`
  have hQz : blockAt (chain km) e.z = Q₂ :=
    blockAt_eq_of_mem hP (hChain.2.2.1 km) hQ₂_mem ⟨by omega, hz_le_Q₂⟩
  have hQyN : blockAt (chain km) eNext.y = Q₂ :=
    blockAt_eq_of_mem hP (hChain.2.2.1 km) hQ₂_mem ⟨by omega, hnext_le⟩
  have hm_lt_sepN : km.val < partSepScale P chain eNext.x eNext.y :=
    (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) km).mpr
      (by rw [hxN, hQz, hQyN])
  -- Also `m < sep(e.y, e.z)`, so ultrametric gives `sep(eNext.s, eNext.x) = sep(e.s, e.z) = ℓ₁`
  have hm_lt_yz : km.val < partSepScale P chain e.y e.z :=
    (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) km).mpr hQz.symm
  have hsep_xz : partSepScale P chain e.x e.z = partSepScale P chain e.x e.y := by
    rw [partSepScale_ultrametric hChain (by omega) (le_of_lt hxy) (le_of_lt hyz) (by omega)]
    simp only [km] at hm_lt_yz
    omega
  have hsep_sz : partSepScale P chain eNext.s eNext.x = partSepScale P chain e.s e.x := by
    rw [hsN, hxN, partSepScale_ultrametric hChain hs1 (le_of_lt hsx) (by omega) (by omega), hsep_xz]
    omega
  have hbndN := partSepScale_bounds P chain (u := eNext.x) (v := eNext.y)
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨eNext, hrN, hfindN, hstepN, hsN, hjN, hxN, ?_⟩
  by_cases htopM : partSepScale P chain eNext.x eNext.y = M + 1
  · left
    rw [bLeafPre, Finset.mem_filter]
    refine ⟨hrN, htopM, ?_⟩
    have hsub_leaf := nestedChain_blockAt_sub hChain (Fin.le_last km) (u := eNext.x) (by omega) (by omega)
    rw [hxN] at hsub_leaf ⊢
    rw [hQz] at hsub_leaf
    dsimp only [Q₂, km] at hsub_leaf hx_Q₂
    omega
  · right
    have hℓ₂N_le : partSepScale P chain eNext.x eNext.y ≤ M := by omega
    have hb1_mem : eNext ∈ b1 P proc chain := by
      rw [b1, Finset.mem_filter]
      refine ⟨hrN, ?_⟩
      rw [hsep_sz]
      simp only [km] at hm_lt_sepN
      have hℓ₁_pos : 1 ≤ partSepScale P chain e.s e.x := by
        rw [b1, Finset.mem_filter] at hb1; exact hb1.2.1
      exact ⟨hℓ₁_pos, by omega, hℓ₂N_le⟩
    refine ⟨hb1_mem, ?_⟩
    rw [hsep_sz]
    exact hdepth (partSepScale P chain eNext.x eNext.y) hm_lt_sepN hℓ₂N_le

noncomputable def followB1 {M : ℕ} (P : ℕ) (T : ScaleTree) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : ℕ → InternalPopRot → InternalPopRot × ℕ
  | 0, e => (e, 0)
  | fuel + 1, e =>
    if e ∈ s1Set P T proc chain then (e, 0)
    else match proc.nextCascadeRot? e with
      | none => (e, 0)
      | some eNext =>
        if eNext ∈ bLeafPre P proc chain then (eNext, 0)
        else
          let res := followB1 P T proc chain fuel eNext
          (res.1, res.2 + 1)

theorem followB1_spec
    (hLca : Ty_scaleTree_lca_props)
    {P r M : ℕ} {T : ScaleTree} (hScale : IsScaleTree r M T)
    {proc : FoldedPopProcess P}
    (hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P) :
    ∀ (fuel : ℕ) {e : InternalPopRot},
      e ∈ b1 P proc chain →
      (lcaScaleTree T (partSepScale P chain e.s e.x) (partSepScale P chain e.x e.y)).length < fuel →
      let res := followB1 P T proc chain fuel e
      res.1 ∈ s1Set P T proc chain ∪ bLeafPre P proc chain ∧
      res.2 < fuel ∧
      res.1.stepIdx = e.stepIdx ∧
      res.1.j = e.j + res.2 + (if res.1 ∈ bLeafPre P proc chain then 1 else 0)
  | 0, _, _, hlt => by omega
  | fuel + 1, e, hb1, hlt => by
    dsimp only [followB1]
    by_cases hs1 : e ∈ s1Set P T proc chain
    · simp only [hs1, ↓reduceIte]
      have hnot_lpre : e ∉ bLeafPre P proc chain := by
        rw [b1, Finset.mem_filter] at hb1
        rw [bLeafPre, Finset.mem_filter]
        omega
      simp [hs1, hnot_lpre]
    · simp only [hs1, ↓reduceIte]
      obtain ⟨eNext, _, hfindN, hstepN, _, hjN, _, hdest⟩ :=
        b1_not_s1_step hLca hScale hBST hChain hOrd hb1 hs1
      rw [hfindN]
      dsimp only
      by_cases hlpre : eNext ∈ bLeafPre P proc chain
      · simp only [hlpre, ↓reduceIte]
        exact ⟨Finset.mem_union_right _ hlpre, Nat.zero_lt_succ _, hstepN, by omega⟩
      · simp only [hlpre, ↓reduceIte]
        rcases hdest with hbad | ⟨hb1N, hdepth_lt⟩
        · exact (hlpre hbad).elim
        · have hfuel_lt : (lcaScaleTree T (partSepScale P chain eNext.s eNext.x)
              (partSepScale P chain eNext.x eNext.y)).length < fuel := by omega
          have ih := followB1_spec hLca hScale hBST hChain hOrd fuel hb1N hfuel_lt
          dsimp only at ih
          exact ⟨ih.1, Nat.succ_lt_succ ih.2.1, ih.2.2.1.trans hstepN, by omega⟩

theorem lem_5_3_from_lca
    (hChainFromValid : ∀ (P r M : ℕ) (T : ScaleTree),
      ValidScaleTree P r M T → IsNestedPartitionChain P (scaleTreePartitionChain T P M))
    (hLca : Ty_scaleTree_lca_props)
    (h36 : Ty_lem_3_6_folded_laws)
    (h51 : Ty_lem_5_1_tree_weights)
    (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    let s1 := s1Set P T proc chain
    let ee := eEnter P T proc chain
    let lpre := bLeafPre P proc chain
    s1 ⊆ b1 P proc chain ∧
    s1.card ≤ P + 2 * sigmaScaleTree T chain ∧
    (s1.card : ℝ) < (26 : ℝ) / 25 * (P : ℝ) ∧
    (b1 P proc chain).card ≤ r * (s1.card + lpre.card) ∧
    ((b1 P proc chain).card : ℝ) < (51 : ℝ) / 25 * (r : ℝ) * (P : ℝ) ∧
    (b1 P proc chain).card < 3 * r * P ∧
    ee.card ≤ s1.card + lpre.card ∧
    (ee.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ) := by
  dsimp only
  let chain := scaleTreePartitionChain T P M
  let s1 := s1Set P T proc chain
  let ee := eEnter P T proc chain
  let lpre := bLeafPre P proc chain
  have hP : 1 ≤ P := hValid.1
  have hScale : IsScaleTree r M T := hValid.2.1
  have hr_pos : 1 ≤ r := hScale.1
  have hChain : IsNestedPartitionChain P chain := hChainFromValid P r M T hValid
  have hLaws := h36 P hP proc
  have hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST :=
    fun τ hτ => (hLaws.1.1 τ hτ).1
  have hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P := by
    intro e he
    obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := hLaws.2.1.2 e he
    exact ⟨h1, h2, h3, h4, h5⟩
  have hSigmaLt : (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50 := (h51 P r M T hValid).2.2
  have hLpreCard : lpre.card ≤ P := bLeafPre_card_le P hP proc h36 chain hChain
  -- 1. `s1 ⊆ b1`
  have hs1_sub : s1 ⊆ b1 P proc chain := Finset.filter_subset _ _
  -- 2. `s1.card ≤ P + 2 * sigmaScaleTree T chain`
  let s1Top := s1.filter (fun e => e.j = e.h)
  let s1CaseA := s1.filter (fun e =>
    let ν := lcaScaleTree T (partSepScale P chain e.s e.x) (partSepScale P chain e.x e.y)
    if hm : mEnd T ν ≤ M then
      (blockAt (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩) e.y).hi < e.z
    else False)
  let s1CaseB2a := s1.filter (fun e =>
    e.j ≠ e.h ∧ ¬ (
      let ν := lcaScaleTree T (partSepScale P chain e.s e.x) (partSepScale P chain e.x e.y)
      if hm : mEnd T ν ≤ M then
        (blockAt (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩) e.y).hi < e.z
      else False))
  have hs1Top_card : s1Top.card ≤ P := by
    have hinj : Set.InjOn InternalPopRot.s (s1Top : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ hs_eq
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      have hr₁ : e₁ ∈ proc.rInt := (Finset.mem_filter.mp (hs1_sub he₁.1)).1
      have hr₂ : e₂ ∈ proc.rInt := (Finset.mem_filter.mp (hs1_sub he₂.1)).1
      obtain ⟨hstep, hh_eq⟩ := rInt_same_s_step_and_h proc hr₁ hr₂ hs_eq
      exact rInt_ext_stepIdx_j proc hr₁ hr₂ hstep (by omega)
    have hmaps : Set.MapsTo InternalPopRot.s (s1Top : Set InternalPopRot) (Finset.Icc 1 P : Set ℕ) := by
      intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      have hr : e ∈ proc.rInt := (Finset.mem_filter.mp (hs1_sub he.1)).1
      obtain ⟨_, hs1_e, hsP_e, _⟩ := mem_rInt_props proc hr
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨hs1_e, hsP_e⟩
    calc s1Top.card ≤ (Finset.Icc 1 P).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = P := by simp
  have hs1CaseA_card : s1CaseA.card ≤ sigmaScaleTree T chain := by
    have hinj : Set.InjOn (b1Tuple P T chain) (s1CaseA : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ htup
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      have hb1_1 := hs1_sub he₁.1
      have hb1_2 := hs1_sub he₂.1
      obtain ⟨hm₁, hmPrev₁, hr₁, _, _, _, _, _, _, _, _, hQ₁_mem, hs₁_Bp, hBp_x₁, hx₁_Q, hQ_y₁, hy₁_Q, _⟩ :=
        b1_routing_bounds hLca hScale hChain hOrd hb1_1
      obtain ⟨hm₂, hmPrev₂, hr₂, _, _, _, _, _, _, _, _, hQ₂_mem, hs₂_Bp, hBp_x₂, hx₂_Q, hQ_y₂, hy₂_Q, _⟩ :=
        b1_routing_bounds hLca hScale hChain hOrd hb1_2
      have hA₁ : (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₁⟩) e₁.y).hi < e₁.z := by
        simpa [hm₁] using he₁.2
      have hA₂ : (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₂⟩) e₂.y).hi < e₂.z := by
        simpa [hm₂] using he₂.2
      obtain ⟨hν_eq, hc₂_eq, hQ_eq⟩ :=
        b1Tuple_same_blocks htup (hm₁ := hm₁) hQ₁_mem (hm₂ := hm₂) hQ₂_mem
      have hmPrev_eq : mStart T (lcaScaleTree T (partSepScale P chain e₁.s e₁.x) (partSepScale P chain e₁.x e₁.y) ++
          [((leafAddr T (partSepScale P chain e₁.x e₁.y))[(lcaScaleTree T (partSepScale P chain e₁.s e₁.x) (partSepScale P chain e₁.x e₁.y)).length]?).getD 0]) - 1 =
        mStart T (lcaScaleTree T (partSepScale P chain e₂.s e₂.x) (partSepScale P chain e₂.x e₂.y) ++
          [((leafAddr T (partSepScale P chain e₂.x e₂.y))[(lcaScaleTree T (partSepScale P chain e₂.s e₂.x) (partSepScale P chain e₂.x e₂.y)).length]?).getD 0]) - 1 := by
        rw [← hc₂_eq, hν_eq]
      have hBp_eq : blockAt (chain ⟨_, Nat.lt_succ_of_le hmPrev₁⟩) (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₁⟩) e₁.y).lo =
          blockAt (chain ⟨_, Nat.lt_succ_of_le hmPrev₂⟩) (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₂⟩) e₂.y).lo := by
        have hfin : (⟨_, Nat.lt_succ_of_le hmPrev₁⟩ : Fin (M + 1)) = ⟨_, Nat.lt_succ_of_le hmPrev₂⟩ :=
          Fin.ext hmPrev_eq
        rw [hfin, hQ_eq]
      rw [← hQ_eq] at hx₂_Q hQ_y₂ hy₂_Q hA₂
      rw [← hBp_eq] at hs₂_Bp hBp_x₂
      obtain ⟨hs1_1, _, _, _, _, _, hfrz1⟩ := hLaws.2.1.2 e₁ hr₁
      obtain ⟨hs1_2, _, _, _, _, _, hfrz2⟩ := hLaws.2.1.2 e₂ hr₂
      rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with hlt | hsame | hgt
      · exfalso
        have hs2_lt_x1 : e₂.s < e₁.x := by omega
        have hτ2_eq := (mem_rInt_props proc hr₂).2.2.2.1
        have hτ2_lt_pop : e₂.stepIdx < proc.popStepIdx e₁.x := by
          rw [hτ2_eq]; exact popStepIdx_strictMono proc hs1_2 hs2_lt_x1 (by omega)
        have hmem_icc : e₂.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) := by
          rw [Finset.mem_Icc]; omega
        exact hfrz1 e₂.stepIdx hmem_icc e₂.y (rInt_mem_leftSpine proc hr₂).2.1 ⟨by omega, by omega⟩
      · rcases lt_trichotomy e₁.j e₂.j with hjlt | hjeq | hjgt
        · exfalso; have := rInt_same_step_lt proc hBST hr₁ hr₂ hsame hjlt; omega
        · exact rInt_ext_stepIdx_j proc hr₁ hr₂ hsame hjeq
        · exfalso; have := rInt_same_step_lt proc hBST hr₂ hr₁ hsame.symm hjgt; omega
      · exfalso
        have hs1_lt_x2 : e₁.s < e₂.x := by omega
        have hτ1_eq := (mem_rInt_props proc hr₁).2.2.2.1
        have hτ1_lt_pop : e₁.stepIdx < proc.popStepIdx e₂.x := by
          rw [hτ1_eq]; exact popStepIdx_strictMono proc hs1_1 hs1_lt_x2 (by omega)
        have hmem_icc : e₁.stepIdx ∈ Finset.Icc (e₂.stepIdx + 1) (proc.popStepIdx e₂.x) := by
          rw [Finset.mem_Icc]; omega
        exact hfrz2 e₁.stepIdx hmem_icc e₁.y (rInt_mem_leftSpine proc hr₁).2.1 ⟨by omega, by omega⟩
    have hmaps : Set.MapsTo (b1Tuple P T chain) (s1CaseA : Set InternalPopRot)
        (sigmaIdxSet T chain : Set (List ℕ × ℕ × ℕ)) := by
      intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hmem_sig, _⟩ :=
        b1_routing_bounds hLca hScale hChain hOrd (hs1_sub he.1)
      exact Finset.mem_coe.mpr hmem_sig
    exact le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) (sigmaIdxSet_card_le T chain)
  have hs1CaseB2a_card : s1CaseB2a.card ≤ sigmaScaleTree T chain := by
    have hinj : Set.InjOn (b1Tuple P T chain) (s1CaseB2a : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ htup
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      have hb1_1 := hs1_sub he₁.1
      have hb1_2 := hs1_sub he₂.1
      obtain ⟨hm₁, hmPrev₁, hr₁, _, _, _, _, _, _, _, _, hQ₁_mem, hs₁_Bp, hBp_x₁, hx₁_Q, hQ_y₁, hy₁_Q, _⟩ :=
        b1_routing_bounds hLca hScale hChain hOrd hb1_1
      obtain ⟨hm₂, hmPrev₂, hr₂, _, _, _, _, _, _, _, _, hQ₂_mem, hs₂_Bp, hBp_x₂, hx₂_Q, hQ_y₂, hy₂_Q, _⟩ :=
        b1_routing_bounds hLca hScale hChain hOrd hb1_2
      have hj1_le := (mem_rInt_props proc hr₁).2.2.2.2.2.2.1
      have hj2_le := (mem_rInt_props proc hr₂).2.2.2.2.2.2.1
      have hz1_le : e₁.z ≤ (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₁⟩) e₁.y).hi := by
        have := he₁.2.2; simp only [hm₁, ↓reduceDIte, not_lt] at this; exact this
      have hz2_le : e₂.z ≤ (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₂⟩) e₂.y).hi := by
        have := he₂.2.2; simp only [hm₂, ↓reduceDIte, not_lt] at this; exact this
      obtain ⟨eN₁, hrN₁, hfindN₁, hstepN₁, _, hjN₁, _, hxN₁⟩ :=
        nextCascadeRot?_eq_some_of_lt proc hr₁ (Nat.lt_of_le_of_ne hj1_le he₁.2.1)
      obtain ⟨eN₂, hrN₂, hfindN₂, hstepN₂, _, hjN₂, _, hxN₂⟩ :=
        nextCascadeRot?_eq_some_of_lt proc hr₂ (Nat.lt_of_le_of_ne hj2_le he₂.2.1)
      have hyN₁_gt : (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₁⟩) e₁.y).hi < eN₁.y := by
        have hs1_1 : e₁ ∈ s1Set P T proc chain := he₁.1
        rw [s1Set, Finset.mem_filter] at hs1_1
        have hc := hs1_1.2
        simp only [hm₁, ↓reduceDIte, hfindN₁, Option.elim_some, decide_eq_true_eq] at hc
        rcases hc with hbad | hbad | hok
        · omega
        · exact (he₁.2.1 hbad).elim
        · exact hok
      have hyN₂_gt : (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₂⟩) e₂.y).hi < eN₂.y := by
        have hs1_2 : e₂ ∈ s1Set P T proc chain := he₂.1
        rw [s1Set, Finset.mem_filter] at hs1_2
        have hc := hs1_2.2
        simp only [hm₂, ↓reduceDIte, hfindN₂, Option.elim_some, decide_eq_true_eq] at hc
        rcases hc with hbad | hbad | hok
        · omega
        · exact (he₂.2.1 hbad).elim
        · exact hok
      obtain ⟨hν_eq, hc₂_eq, hQ_eq⟩ :=
        b1Tuple_same_blocks htup (hm₁ := hm₁) hQ₁_mem (hm₂ := hm₂) hQ₂_mem
      have hmPrev_eq : mStart T (lcaScaleTree T (partSepScale P chain e₁.s e₁.x) (partSepScale P chain e₁.x e₁.y) ++
          [((leafAddr T (partSepScale P chain e₁.x e₁.y))[(lcaScaleTree T (partSepScale P chain e₁.s e₁.x) (partSepScale P chain e₁.x e₁.y)).length]?).getD 0]) - 1 =
        mStart T (lcaScaleTree T (partSepScale P chain e₂.s e₂.x) (partSepScale P chain e₂.x e₂.y) ++
          [((leafAddr T (partSepScale P chain e₂.x e₂.y))[(lcaScaleTree T (partSepScale P chain e₂.s e₂.x) (partSepScale P chain e₂.x e₂.y)).length]?).getD 0]) - 1 := by
        rw [← hc₂_eq, hν_eq]
      have hBp_eq : blockAt (chain ⟨_, Nat.lt_succ_of_le hmPrev₁⟩) (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₁⟩) e₁.y).lo =
          blockAt (chain ⟨_, Nat.lt_succ_of_le hmPrev₂⟩) (blockAt (chain ⟨_, Nat.lt_succ_of_le hm₂⟩) e₂.y).lo := by
        have hfin : (⟨_, Nat.lt_succ_of_le hmPrev₁⟩ : Fin (M + 1)) = ⟨_, Nat.lt_succ_of_le hmPrev₂⟩ :=
          Fin.ext hmPrev_eq
        rw [hfin, hQ_eq]
      rw [← hQ_eq] at hx₂_Q hQ_y₂ hy₂_Q hz2_le hyN₂_gt
      rw [← hBp_eq] at hs₂_Bp hBp_x₂
      obtain ⟨hs1_1, _, _, hyz_1, _, _, hfrz1⟩ := hLaws.2.1.2 e₁ hr₁
      obtain ⟨hs1_2, _, _, hyz_2, _, _, hfrz2⟩ := hLaws.2.1.2 e₂ hr₂
      obtain ⟨_, _, _, hyz_N1, hzP_N1, _, hfrzN1⟩ := hLaws.2.1.2 eN₁ hrN₁
      obtain ⟨_, _, _, hyz_N2, hzP_N2, _, hfrzN2⟩ := hLaws.2.1.2 eN₂ hrN₂
      rcases lt_trichotomy e₁.stepIdx e₂.stepIdx with hlt | hsame | hgt
      · exfalso
        have hs2_lt_x1 : e₂.s < e₁.x := by omega
        have hτ2_eq := (mem_rInt_props proc hr₂).2.2.2.1
        have hτ2_lt_pop_x1 : e₂.stepIdx < proc.popStepIdx e₁.x := by
          rw [hτ2_eq]; exact popStepIdx_strictMono proc hs1_2 hs2_lt_x1 (by omega)
        have hτ2_lt_pop_z1 : e₂.stepIdx < proc.popStepIdx eN₁.x := by
          rw [hτ2_eq]; exact popStepIdx_strictMono proc hs1_2 (by omega) (by omega)
        have hicc1 : e₂.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) := by
          rw [Finset.mem_Icc]; omega
        have hiccN1 : e₂.stepIdx ∈ Finset.Icc (eN₁.stepIdx + 1) (proc.popStepIdx eN₁.x) := by
          rw [Finset.mem_Icc]; omega
        have hls_y2 := (rInt_mem_leftSpine proc hr₂).2.1
        have hls_z2 := (rInt_mem_leftSpine proc hr₂).2.2
        rcases lt_trichotomy e₂.y e₁.z with hy2_lt | hy2_eq | hy2_gt
        · exact hfrz1 e₂.stepIdx hicc1 e₂.y hls_y2 ⟨by omega, hy2_lt⟩
        · exact hfrzN1 e₂.stepIdx hiccN1 e₂.z hls_z2 ⟨by omega, by omega⟩
        · exact hfrzN1 e₂.stepIdx hiccN1 e₂.y hls_y2 ⟨by omega, by omega⟩
      · rcases lt_trichotomy e₁.j e₂.j with hjlt | hjeq | hjgt
        · exfalso
          rcases eq_or_lt_of_le (show eN₁.j ≤ e₂.j by omega) with hjeqN | hjltN
          · have heqN := rInt_ext_stepIdx_j proc hrN₁ hr₂ (hstepN₁.trans hsame) hjeqN
            have hy_eq : eN₁.y = e₂.y := congrArg InternalPopRot.y heqN
            omega
          · have := rInt_same_step_lt proc hBST hrN₁ hr₂ (hstepN₁.trans hsame) hjltN; omega
        · exact rInt_ext_stepIdx_j proc hr₁ hr₂ hsame hjeq
        · exfalso
          rcases eq_or_lt_of_le (show eN₂.j ≤ e₁.j by omega) with hjeqN | hjltN
          · have heqN := rInt_ext_stepIdx_j proc hrN₂ hr₁ (hstepN₂.trans hsame.symm) hjeqN
            have hy_eq : eN₂.y = e₁.y := congrArg InternalPopRot.y heqN
            omega
          · have := rInt_same_step_lt proc hBST hrN₂ hr₁ (hstepN₂.trans hsame.symm) hjltN; omega
      · exfalso
        have hs1_lt_x2 : e₁.s < e₂.x := by omega
        have hτ1_eq := (mem_rInt_props proc hr₁).2.2.2.1
        have hτ1_lt_pop_x2 : e₁.stepIdx < proc.popStepIdx e₂.x := by
          rw [hτ1_eq]; exact popStepIdx_strictMono proc hs1_1 hs1_lt_x2 (by omega)
        have hτ1_lt_pop_z2 : e₁.stepIdx < proc.popStepIdx eN₂.x := by
          rw [hτ1_eq]; exact popStepIdx_strictMono proc hs1_1 (by omega) (by omega)
        have hicc2 : e₁.stepIdx ∈ Finset.Icc (e₂.stepIdx + 1) (proc.popStepIdx e₂.x) := by
          rw [Finset.mem_Icc]; omega
        have hiccN2 : e₁.stepIdx ∈ Finset.Icc (eN₂.stepIdx + 1) (proc.popStepIdx eN₂.x) := by
          rw [Finset.mem_Icc]; omega
        have hls_y1 := (rInt_mem_leftSpine proc hr₁).2.1
        have hls_z1 := (rInt_mem_leftSpine proc hr₁).2.2
        rcases lt_trichotomy e₁.y e₂.z with hy1_lt | hy1_eq | hy1_gt
        · exact hfrz2 e₁.stepIdx hicc2 e₁.y hls_y1 ⟨by omega, hy1_lt⟩
        · exact hfrzN2 e₁.stepIdx hiccN2 e₁.z hls_z1 ⟨by omega, by omega⟩
        · exact hfrzN2 e₁.stepIdx hiccN2 e₁.y hls_y1 ⟨by omega, by omega⟩
    have hmaps : Set.MapsTo (b1Tuple P T chain) (s1CaseB2a : Set InternalPopRot)
        (sigmaIdxSet T chain : Set (List ℕ × ℕ × ℕ)) := by
      intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hmem_sig, _⟩ :=
        b1_routing_bounds hLca hScale hChain hOrd (hs1_sub he.1)
      exact Finset.mem_coe.mpr hmem_sig
    exact le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) (sigmaIdxSet_card_le T chain)
  have hs1_cov : s1 ⊆ s1Top ∪ (s1CaseA ∪ s1CaseB2a) := by
    intro e he
    simp only [s1Top, s1CaseA, s1CaseB2a, Finset.mem_union, Finset.mem_filter]
    by_cases htop : e.j = e.h
    · exact Or.inl ⟨he, htop⟩
    · by_cases hA : (let ν := lcaScaleTree T (partSepScale P chain e.s e.x) (partSepScale P chain e.x e.y)
        if hm : mEnd T ν ≤ M then (blockAt (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩) e.y).hi < e.z else False)
      · exact Or.inr (Or.inl ⟨he, hA⟩)
      · exact Or.inr (Or.inr ⟨he, htop, hA⟩)
  have hs1_card : s1.card ≤ P + 2 * sigmaScaleTree T chain := by
    have h1 := Finset.card_le_card hs1_cov
    have h2 := Finset.card_union_le s1Top (s1CaseA ∪ s1CaseB2a)
    have h3 := Finset.card_union_le s1CaseA s1CaseB2a
    omega
  -- 3. Part (1): `b1.card ≤ r * (s1.card + lpre.card)` via `followB1`
  have hb1_card : (b1 P proc chain).card ≤ r * (s1.card + lpre.card) := by
    have hinj_f : Set.InjOn (followB1 P T proc chain r) (b1 P proc chain : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ hfeq
      rw [Finset.mem_coe] at he₁ he₂
      obtain ⟨_, _, hr₁, _, hl₁, _⟩ := b1_routing_bounds hLca hScale hChain hOrd he₁
      obtain ⟨_, _, hr₂, _, hl₂, _⟩ := b1_routing_bounds hLca hScale hChain hOrd he₂
      have sp₁ := followB1_spec hLca hScale hBST hChain hOrd r he₁ hl₁
      have sp₂ := followB1_spec hLca hScale hBST hChain hOrd r he₂ hl₂
      dsimp only at sp₁ sp₂
      have h1 : (followB1 P T proc chain r e₁).1 = (followB1 P T proc chain r e₂).1 :=
        congrArg Prod.fst hfeq
      have h2 : (followB1 P T proc chain r e₁).2 = (followB1 P T proc chain r e₂).2 :=
        congrArg Prod.snd hfeq
      have hstep : e₁.stepIdx = e₂.stepIdx := by
        rw [← sp₁.2.2.1, ← sp₂.2.2.1, h1]
      have hj_eq : e₁.j = e₂.j := by
        have hj1 := sp₁.2.2.2
        have hj2 := sp₂.2.2.2
        rw [h1, h2] at hj1
        omega
      exact rInt_ext_stepIdx_j proc hr₁ hr₂ hstep hj_eq
    have hmaps_f : Set.MapsTo (followB1 P T proc chain r)
        (b1 P proc chain : Set InternalPopRot)
        (((s1 ∪ lpre) ×ˢ Finset.range r : Finset (InternalPopRot × ℕ)) : Set (InternalPopRot × ℕ)) := by
      intro e he
      rw [Finset.mem_coe] at he
      obtain ⟨_, _, _, _, hl, _⟩ := b1_routing_bounds hLca hScale hChain hOrd he
      have sp := followB1_spec hLca hScale hBST hChain hOrd r he hl
      dsimp only at sp
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      exact ⟨sp.1, sp.2.1⟩
    calc (b1 P proc chain).card
        ≤ ((s1 ∪ lpre) ×ˢ Finset.range r).card := Finset.card_le_card_of_injOn _ hmaps_f hinj_f
      _ = (s1 ∪ lpre).card * r := by rw [Finset.card_product, Finset.card_range]
      _ ≤ (s1.card + lpre.card) * r := Nat.mul_le_mul_right r (Finset.card_union_le s1 lpre)
      _ = r * (s1.card + lpre.card) := Nat.mul_comm _ _
  -- 4. Part (2): `ee.card ≤ s1.card + lpre.card`
  have hee_card : ee.card ≤ s1.card + lpre.card := by
    set b1Only := b1 P proc chain \ s1
    set target := b1 P proc chain ∪ lpre
    let nextFn : InternalPopRot → InternalPopRot := fun e => (proc.nextCascadeRot? e).getD e
    have hdisj : Disjoint b1Only ee := by
      rw [Finset.disjoint_left]
      intro e hb he
      rw [Finset.mem_sdiff] at hb
      simp only [ee, eEnter, Finset.mem_filter, Finset.mem_sdiff] at he
      exact he.1.2 hb
    have hex_next : ∀ e ∈ b1Only ∪ ee,
        e ∈ proc.rInt ∧ ∃ eNext ∈ target, proc.nextCascadeRot? e = some eNext := by
      intro e he
      rcases Finset.mem_union.mp he with hb | hee_mem
      · rw [Finset.mem_sdiff] at hb
        obtain ⟨eNext, _, hfindN, _, _, _, _, hdest⟩ :=
          b1_not_s1_step hLca hScale hBST hChain hOrd hb.1 hb.2
        have hr_e : e ∈ proc.rInt := (Finset.mem_filter.mp hb.1).1
        refine ⟨hr_e, eNext, ?_, hfindN⟩
        rcases hdest with hl | ⟨hb1N, _⟩
        · exact Finset.mem_union_right _ hl
        · exact Finset.mem_union_left _ hb1N
      · simp only [ee, eEnter, Finset.mem_filter, Finset.mem_sdiff] at hee_mem
        obtain ⟨⟨hr_e, _⟩, hcond⟩ := hee_mem
        cases hopt : proc.nextCascadeRot? e with
        | none => simp [hopt] at hcond
        | some eNext =>
          simp only [hopt, Option.elim_some, decide_eq_true_eq] at hcond
          exact ⟨hr_e, eNext, hcond, rfl⟩
    have hinj_n : Set.InjOn nextFn ((b1Only ∪ ee : Finset InternalPopRot) : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ hneq
      rw [Finset.mem_coe] at he₁ he₂
      obtain ⟨hr₁, eN₁, _, hf₁⟩ := hex_next e₁ he₁
      obtain ⟨hr₂, eN₂, _, hf₂⟩ := hex_next e₂ he₂
      simp only [nextFn, hf₁, hf₂, Option.getD_some] at hneq
      rw [hneq] at hf₁
      exact nextCascadeRot?_inj proc hr₁ hr₂ hf₁ hf₂
    have hmaps_n : Set.MapsTo nextFn
        ((b1Only ∪ ee : Finset InternalPopRot) : Set InternalPopRot)
        (target : Set InternalPopRot) := by
      intro e he
      rw [Finset.mem_coe] at he ⊢
      obtain ⟨_, eN, hmem_t, hf⟩ := hex_next e he
      simp [nextFn, hf, hmem_t]
    have hcard_le : (b1Only ∪ ee).card ≤ target.card :=
      Finset.card_le_card_of_injOn _ hmaps_n hinj_n
    rw [Finset.card_union_of_disjoint hdisj] at hcard_le
    have htarget_le : target.card ≤ (b1 P proc chain).card + lpre.card :=
      Finset.card_union_le _ _
    have hsdiff_eq : b1Only.card + s1.card = (b1 P proc chain).card :=
      Finset.card_sdiff_add_card_eq_card hs1_sub
    omega
  -- 5. Numerical & real inequalities
  have hs1_real : (s1.card : ℝ) < (26 : ℝ) / 25 * (P : ℝ) := by
    have hc : (s1.card : ℝ) ≤ (P : ℝ) + 2 * (sigmaScaleTree T chain : ℝ) := by exact_mod_cast hs1_card
    linarith
  have hlpre_real : (lpre.card : ℝ) ≤ (P : ℝ) := by exact_mod_cast hLpreCard
  have hee_real : (ee.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ) := by
    have hc : (ee.card : ℝ) ≤ (s1.card : ℝ) + (lpre.card : ℝ) := by exact_mod_cast hee_card
    linarith
  have hr_real_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr_pos
  have hP_real_pos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hb1_real : ((b1 P proc chain).card : ℝ) < (51 : ℝ) / 25 * (r : ℝ) * (P : ℝ) := by
    have hc : ((b1 P proc chain).card : ℝ) ≤ (r : ℝ) * ((s1.card : ℝ) + (lpre.card : ℝ)) := by
      exact_mod_cast hb1_card
    have hsum_lt : (s1.card : ℝ) + (lpre.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ) := by linarith
    have hmul_lt : (r : ℝ) * ((s1.card : ℝ) + (lpre.card : ℝ)) <
        (r : ℝ) * ((51 : ℝ) / 25 * (P : ℝ)) := mul_lt_mul_of_pos_left hsum_lt hr_real_pos
    linarith
  have hb1_3rP : (b1 P proc chain).card < 3 * r * P := by
    have hrP_pos : (0 : ℝ) < (r : ℝ) * (P : ℝ) := mul_pos hr_real_pos hP_real_pos
    have h3 : ((b1 P proc chain).card : ℝ) < ((3 * r * P : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast h3
  exact ⟨hs1_sub, hs1_card, hs1_real, hb1_card, hb1_real, hb1_3rP, hee_card, hee_real⟩

/-! ## Section 5: Lemma 5.4 (`lem_5_4_bucket_b3_intra`) -/

theorem foldedParentAux_mem_or_eq (cur : ℕ) :
    ∀ (t : BinaryTree ℕ) (v : ℕ),
      foldedParentAux cur t v = cur ∨ foldedParentAux cur t v ∈ t
  | .nil, _ => Or.inl rfl
  | .node k l r, v => by
    unfold foldedParentAux
    by_cases hlt : v < k
    · simp only [hlt, ↓reduceIte]
      rcases foldedParentAux_mem_or_eq k l v with heq | hm
      · rw [heq]; exact Or.inr BinaryTree.Mem.here
      · exact Or.inr (BinaryTree.Mem.left hm)
    · simp only [hlt, ↓reduceIte]
      by_cases hgt : k < v
      · simp only [hgt, ↓reduceIte]
        rcases foldedParentAux_mem_or_eq cur r v with heq | hm
        · exact Or.inl heq
        · exact Or.inr (BinaryTree.Mem.right hm)
      · simp [hgt]

theorem foldedParent_mem_or_top (P : ℕ) (t : BinaryTree ℕ) (v : ℕ) :
    foldedParent P t v = P + 1 ∨ foldedParent P t v ∈ t := by
  unfold foldedParent
  split_ifs with hv
  · exact Or.inl rfl
  · exact foldedParentAux_mem_or_eq (P + 1) t v

theorem keyFinset_modifyLeftAt_push_sub :
    ∀ (t : BinaryTree ℕ) (b w : ℕ),
      keyFinset (modifyLeftAt t b (fun L1 => .node w .nil L1)) ⊆ insert w (keyFinset t)
  | .nil, _, _ => by simp [modifyLeftAt, keyFinset]
  | .node k l r, b, w => by
    unfold modifyLeftAt
    intro x hx
    by_cases h1 : b < k
    · simp only [h1, ↓reduceIte, keyFinset, Finset.mem_insert, Finset.mem_union] at hx ⊢
      rcases hx with rfl | hxl | hxr
      · exact Or.inr (Or.inl rfl)
      · rcases Finset.mem_insert.mp (keyFinset_modifyLeftAt_push_sub l b w hxl) with rfl | hxl'
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl hxl'))
      · exact Or.inr (Or.inr (Or.inr hxr))
    · simp only [h1, ↓reduceIte] at hx
      by_cases h2 : k < b
      · simp only [h2, ↓reduceIte, keyFinset, Finset.mem_insert, Finset.mem_union] at hx ⊢
        rcases hx with rfl | hxl | hxr
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl hxl))
        · rcases Finset.mem_insert.mp (keyFinset_modifyLeftAt_push_sub r b w hxr) with rfl | hxr'
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inr hxr'))
      · simp only [h2, ↓reduceIte, keyFinset, Finset.mem_insert, Finset.mem_union,
          Finset.empty_union] at hx ⊢
        tauto

theorem foldedParentAux_modifyLeftAt_push :
    ∀ (t : BinaryTree ℕ) (b w cur u : ℕ), w < u →
      foldedParentAux cur (modifyLeftAt t b (fun L1 => .node w .nil L1)) u =
        foldedParentAux cur t u
  | .nil, _, _, _, _, _ => rfl
  | .node k l r, b, w, cur, u, hwu => by
    unfold modifyLeftAt
    by_cases h1 : b < k
    · simp only [h1, ↓reduceIte, foldedParentAux]
      by_cases hu1 : u < k
      · simp only [hu1, ↓reduceIte]
        exact foldedParentAux_modifyLeftAt_push l b w k u hwu
      · simp only [hu1, ↓reduceIte]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : k < b
      · simp only [h2, ↓reduceIte, foldedParentAux]
        by_cases hu1 : u < k
        · simp [hu1]
        · simp only [hu1, ↓reduceIte]
          by_cases hu2 : k < u
          · simp only [hu2, ↓reduceIte]
            exact foldedParentAux_modifyLeftAt_push r b w cur u hwu
          · simp [hu2]
      · simp only [h2, ↓reduceIte, foldedParentAux]
        by_cases hu1 : u < k
        · have hnot : ¬ u < w := by omega
          simp [hu1, hnot, hwu]
        · simp only [hu1, ↓reduceIte]

theorem keyFinset_rotateRightEdge :
    ∀ (t : BinaryTree ℕ) (x p : ℕ), keyFinset (rotateRightEdge t x p) = keyFinset t
  | .nil, _, _ => rfl
  | .node k l r, x, p => by
    unfold rotateRightEdge
    by_cases h1 : p < k
    · simp [h1, keyFinset, keyFinset_rotateRightEdge l x p]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : k < p
      · simp [h2, keyFinset, keyFinset_rotateRightEdge r x p]
      · simp only [h2, ↓reduceIte]
        cases l with
        | nil => rfl
        | node lx a b =>
          by_cases hx : lx = x
          · simp only [hx, ↓reduceIte, keyFinset]
            ext y; simp; tauto
          · simp [hx]

theorem keyFinset_foldl_rotateRightEdge (t0 : BinaryTree ℕ) :
    ∀ (pairs : List (ℕ × ℕ)),
      keyFinset (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t0) = keyFinset t0
  | [] => rfl
  | (x, p) :: rest => by
    simp only [List.foldl_cons]
    rw [keyFinset_foldl_rotateRightEdge (rotateRightEdge t0 x p) rest, keyFinset_rotateRightEdge]

theorem subtreeAtKey_mem :
    ∀ (t : BinaryTree ℕ) (v x : ℕ), x ∈ subtreeAtKey t v → x ∈ t
  | .nil, _, _, hx => by simp [subtreeAtKey] at hx
  | .node k l r, v, x, hx => by
    unfold subtreeAtKey at hx
    by_cases h1 : v < k
    · simp only [h1, ↓reduceIte] at hx
      exact BinaryTree.Mem.left (subtreeAtKey_mem l v x hx)
    · simp only [h1, ↓reduceIte] at hx
      by_cases h2 : k < v
      · simp only [h2, ↓reduceIte] at hx
        exact BinaryTree.Mem.right (subtreeAtKey_mem r v x hx)
      · simp only [h2, ↓reduceIte] at hx
        exact hx

theorem foldedParentAux_of_subtreeAtKey_rot :
    ∀ (t : BinaryTree ℕ), t.IsBST →
      ∀ (cur u v : ℕ) (A B C : BinaryTree ℕ),
        u < v → subtreeAtKey t v = .node v (.node u A B) C →
        foldedParentAux cur t u = v
  | .nil, _, _, _, _, _, _, _, _, hsub => by simp [subtreeAtKey] at hsub
  | .node k l r, ht, cur, u, v, A, B, C, huv, hsub => by
    unfold subtreeAtKey at hsub
    by_cases h1 : v < k
    · simp only [h1, ↓reduceIte] at hsub
      have huk : u < k := Nat.lt_trans huv h1
      simp only [foldedParentAux, huk, ↓reduceIte]
      exact foldedParentAux_of_subtreeAtKey_rot l (BinaryTree.IsBST_left_of_IsBST ht)
        k u v A B C huv hsub
    · simp only [h1, ↓reduceIte] at hsub
      by_cases h2 : k < v
      · simp only [h2, ↓reduceIte] at hsub
        have hu_in_sub : u ∈ subtreeAtKey r v := by
          rw [hsub]; exact BinaryTree.Mem.left BinaryTree.Mem.here
        have hu_in_r : u ∈ r := subtreeAtKey_mem r v u hu_in_sub
        have hku : k < u := BinaryTree.gt_of_IsBST_right l k r ht hu_in_r
        have hnuk : ¬ u < k := by omega
        simp only [foldedParentAux, hnuk, hku, ↓reduceIte]
        exact foldedParentAux_of_subtreeAtKey_rot r (BinaryTree.IsBST_right_of_IsBST ht)
          cur u v A B C huv hsub
      · simp only [h2, ↓reduceIte] at hsub
        injection hsub with hk hl _
        subst hk
        rw [hl]
        simp [foldedParentAux, huv]

theorem foldedParent_of_isRightRotEdge {P : ℕ} {t : BinaryTree ℕ}
    (ht : t.IsBST) {u v : ℕ} (huv : u < v) (huP : u ≤ P) (hrot : IsRightRotEdge t u v) :
    foldedParent P t u = v := by
  obtain ⟨A, B, C, _, hsub⟩ := hrot
  have hne : u ≠ P + 1 := by omega
  unfold foldedParent
  simp only [hne, ↓reduceIte]
  exact foldedParentAux_of_subtreeAtKey_rot t ht (P + 1) u v A B C huv hsub

theorem minKey?_node_isSome (k : ℕ) (l r : BinaryTree ℕ) :
    (BinaryTree.node k l r).minKey?.isSome = true := by
  unfold BinaryTree.minKey?
  cases l.minKey? <;> rfl

theorem minKey?_mem_and_le :
    ∀ (t : BinaryTree ℕ), t.IsBST → ∀ {s : ℕ}, t.minKey? = some s →
      s ∈ t ∧ (∀ x ∈ t, s ≤ x) ∧ keyFinset (spliceMin t) = (keyFinset t).erase s
  | .nil, _, _, hmin => by simp [BinaryTree.minKey?] at hmin
  | .node k .nil r, ht, s, hmin => by
    simp only [BinaryTree.minKey?, Option.some.injEq] at hmin
    subst hmin
    refine ⟨BinaryTree.Mem.here, ?_, ?_⟩
    · intro x hx
      rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
      · exact le_rfl
      · cases hxl
      · exact le_of_lt (BinaryTree.gt_of_IsBST_right .nil k r ht hxr)
    · simp only [spliceMin, keyFinset, Finset.empty_union]
      have hnot_in_r : k ∉ keyFinset r := by
        rw [← mem_iff_mem_keyFinset]
        intro hkr
        exact lt_irrefl _ (BinaryTree.gt_of_IsBST_right .nil k r ht hkr)
      exact (Finset.erase_insert hnot_in_r).symm
  | .node k (.node lk ll lr) r, ht, s, hmin => by
    set l := BinaryTree.node lk ll lr
    have hsome := minKey?_node_isSome lk ll lr
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
    have hmin_l : l.minKey? = some s := by
      simp only [BinaryTree.minKey?] at hmin
      rw [hm] at hmin
      exact hm.trans hmin
    obtain ⟨hs_in_l, hs_le_l, hsplice_l⟩ :=
      minKey?_mem_and_le l (BinaryTree.IsBST_left_of_IsBST ht) hmin_l
    have hsk : s < k := BinaryTree.lt_of_IsBST_left l k r ht hs_in_l
    refine ⟨BinaryTree.Mem.left hs_in_l, ?_, ?_⟩
    · intro x hx
      rcases BinaryTree.mem_node_iff.mp hx with rfl | hxl | hxr
      · exact le_of_lt hsk
      · exact hs_le_l x hxl
      · exact le_of_lt (Nat.lt_trans hsk (BinaryTree.gt_of_IsBST_right l k r ht hxr))
    · have hsplice_eq : spliceMin (.node k l r) = .node k (spliceMin l) r := rfl
      rw [hsplice_eq]
      simp only [keyFinset, hsplice_l]
      ext x
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase, ← mem_iff_mem_keyFinset]
      constructor
      · rintro (rfl | ⟨hne, hxl⟩ | hxr)
        · exact ⟨by omega, Or.inl rfl⟩
        · exact ⟨hne, Or.inr (Or.inl hxl)⟩
        · have hkx := BinaryTree.gt_of_IsBST_right l k r ht hxr
          exact ⟨by omega, Or.inr (Or.inr hxr)⟩
      · rintro ⟨hne, rfl | hxl | hxr⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨hne, hxl⟩)
        · exact Or.inr (Or.inr hxr)

theorem foldedParentAux_leftSpine :
    ∀ (t : BinaryTree ℕ), t.IsBST → ∀ (cur : ℕ),
      (∀ (idx : ℕ) (h : idx + 1 < (leftSpine t).length),
        foldedParentAux cur t ((leftSpine t)[idx]'(by omega)) = (leftSpine t)[idx + 1]'h) ∧
      (∀ (hne : (leftSpine t).length ≠ 0),
        foldedParentAux cur t ((leftSpine t)[(leftSpine t).length - 1]'(by omega)) = cur)
  | .nil, _, _ => by simp [leftSpine]
  | .node k l r, ht, cur => by
    have hlt_l : ∀ x ∈ leftSpine l, x < k := by
      intro x hx
      have hx_mem := (leftSpine_mem_and_pairwise (BinaryTree.IsBST_left_of_IsBST ht)).1 x hx
      exact BinaryTree.lt_of_IsBST_left l k r ht hx_mem
    obtain ⟨ih_mid, ih_last⟩ := foldedParentAux_leftSpine l (BinaryTree.IsBST_left_of_IsBST ht) k
    refine ⟨?_, ?_⟩
    · intro idx h
      simp only [leftSpine, List.length_append, List.length_singleton] at h
      by_cases h_in : idx + 1 < (leftSpine l).length
      · have hg0 : (leftSpine (.node k l r))[idx]'(by simp [leftSpine]; omega) =
            (leftSpine l)[idx]'(by omega) := by
          simp only [leftSpine]
          exact List.getElem_append_left (by omega)
        have hg1 : (leftSpine (.node k l r))[idx + 1]'(by simp [leftSpine]; omega) =
            (leftSpine l)[idx + 1]'h_in := by
          simp only [leftSpine]
          exact List.getElem_append_left h_in
        rw [hg0, hg1]
        have hxk : (leftSpine l)[idx]'(by omega) < k := hlt_l _ (List.getElem_mem _)
        simp only [foldedParentAux, hxk, ↓reduceIte]
        exact ih_mid idx h_in
      · have hidx_eq : idx = (leftSpine l).length - 1 := by omega
        have hlen_pos : (leftSpine l).length ≠ 0 := by omega
        have hg0 : (leftSpine (.node k l r))[idx]'(by simp [leftSpine]; omega) =
            (leftSpine l)[(leftSpine l).length - 1]'(by omega) := by
          simp only [leftSpine, hidx_eq]
          exact List.getElem_append_left (by omega)
        have hg1 : (leftSpine (.node k l r))[idx + 1]'(by simp [leftSpine]; omega) = k := by
          simp only [leftSpine]
          have heq_len : idx + 1 = (leftSpine l).length := by omega
          simp [heq_len]
        rw [hg0, hg1]
        have hxk : (leftSpine l)[(leftSpine l).length - 1]'(by omega) < k :=
          hlt_l _ (List.getElem_mem _)
        simp only [foldedParentAux, hxk, ↓reduceIte]
        exact ih_last hlen_pos
    · intro _
      have hlast : (leftSpine (.node k l r))[(leftSpine (.node k l r)).length - 1]'(by
          simp [leftSpine]) = k := by
        simp [leftSpine]
      rw [hlast]
      simp [foldedParentAux]

def phiNode {M : ℕ} (P : ℕ) (chain : Fin (M + 1) → List IntervalBlock)
    (t : BinaryTree ℕ) (v : ℕ) : ℕ :=
  let p1 := foldedParent P t v
  let p2 := foldedParent P t p1
  let s1 := partSepScale P chain v p1
  let s2 := partSepScale P chain p1 p2
  if 1 ≤ s1 ∧ s1 ≤ M ∧ s1 < s2 then 1 else 0

def phiConf {M : ℕ} (P : ℕ) (chain : Fin (M + 1) → List IntervalBlock)
    (t : BinaryTree ℕ) : ℕ :=
  (keyFinset t).sum (phiNode P chain t)

theorem phiNode_le_one {M : ℕ} (P : ℕ) (chain : Fin (M + 1) → List IntervalBlock)
    (t : BinaryTree ℕ) (v : ℕ) : phiNode P chain t v ≤ 1 := by
  unfold phiNode; dsimp only; split_ifs <;> omega

theorem phiNode_mono_p2 {M : ℕ} {P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    {t t' : BinaryTree ℕ} {a : ℕ}
    (hp1 : foldedParent P t' a = foldedParent P t a)
    (hs2 : partSepScale P chain (foldedParent P t' a) (foldedParent P t' (foldedParent P t' a)) ≤
           partSepScale P chain (foldedParent P t a) (foldedParent P t (foldedParent P t a))) :
    phiNode P chain t' a ≤ phiNode P chain t a := by
  unfold phiNode
  dsimp only
  rw [hp1] at hs2 ⊢
  split_ifs with h1 h2 <;> omega

theorem getElem_of_append_eq {α : Type} {a b c : List α} (h : a ++ b = c)
    (i : ℕ) (ha : i < a.length) (hc : i < c.length) :
    GetElem.getElem c i hc = GetElem.getElem a i ha := by
  subst h
  exact List.getElem_append_left ha

theorem rInt_foldedParent_before_pop {P : ℕ} (proc : FoldedPopProcess P)
    (hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST)
    {e : InternalPopRot} (he : e ∈ proc.rInt) (hxP : e.x ≤ P) (hyP : e.y ≤ P) :
    foldedParent P (proc.treeAt e.stepIdx) e.x = e.y ∧
    foldedParent P (proc.treeAt e.stepIdx) e.y = e.z := by
  obtain ⟨hτ, _, _, _, _, _, _, b, _, hb_mem, _, hlen, he_eq⟩ := mem_rInt_props proc he
  set t := proc.treeAt e.stepIdx
  set ls := leftSpine t
  set sub := takeThrough ls b
  have hlen_sub : 2 * e.j + 1 < sub.length := hlen
  obtain ⟨rest, hrest⟩ := takeThrough_isPrefix ls b hb_mem
  have hrest' : sub ++ rest = ls := hrest
  have hlen_ls : sub.length ≤ ls.length := by rw [← hrest']; simp
  have hlen_ls' : sub.length ≤ (leftSpine t).length := hlen_ls
  have hx : e.x = ls[2 * e.j - 1]'(by omega) := by
    have hx' : e.x = sub[2 * e.j - 1]'(by omega) := by conv_lhs => rw [he_eq]
    exact hx'.trans (getElem_of_append_eq hrest' (2 * e.j - 1) (by omega) (by omega)).symm
  have hy : e.y = ls[2 * e.j]'(by omega) := by
    have hy' : e.y = sub[2 * e.j]'(by omega) := by conv_lhs => rw [he_eq]
    exact hy'.trans (getElem_of_append_eq hrest' (2 * e.j) (by omega) (by omega)).symm
  have hz : e.z = ls[2 * e.j + 1]'(by omega) := by
    have hz' : e.z = sub[2 * e.j + 1]'hlen_sub := by conv_lhs => rw [he_eq]
    exact hz'.trans (getElem_of_append_eq hrest' (2 * e.j + 1) hlen_sub (by omega)).symm
  have hls_par := (foldedParentAux_leftSpine t (hBST e.stepIdx (le_of_lt hτ)) (P + 1)).1
  have hne_x : e.x ≠ P + 1 := by omega
  have hne_y : e.y ≠ P + 1 := by omega
  refine ⟨?_, ?_⟩
  · unfold foldedParent
    simp only [hne_x, ↓reduceIte]
    have hidx : 2 * e.j - 1 + 1 = 2 * e.j := by omega
    conv_lhs => rw [hx]
    have hstep := hls_par (2 * e.j - 1) (by omega)
    simpa [ls, hidx, hy] using hstep
  · unfold foldedParent
    simp only [hne_y, ↓reduceIte]
    conv_lhs => rw [hy]
    have hstep := hls_par (2 * e.j) (by omega)
    simpa [ls, hz] using hstep

theorem sum_range_getElem?_bool {α : Type} :
    ∀ (xs : List α) (p : α → Bool),
      (Finset.range xs.length).sum (fun i =>
        match xs[i]? with
        | some x => if p x then 1 else 0
        | none => 0) = (xs.filter p).length
  | [], _ => by simp
  | x :: rest, p => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.filter_cons]
    rw [sum_range_getElem?_bool rest p]
    cases p x <;> simp

theorem push_filterMap_len_eq_filter :
    ∀ (xs : List FoldedOp),
      (xs.filterMap (fun | .push w => some w | _ => none)).length =
        (xs.filter (fun | .push _ => true | _ => false)).length
  | [] => rfl
  | op :: rest => by
    cases op <;> simp [push_filterMap_len_eq_filter rest]

theorem sum_range_rInt_stepIdx_card {P : ℕ} (proc : FoldedPopProcess P)
    (pred : InternalPopRot → Prop) [DecidablePred pred] :
    (Finset.range proc.steps.length).sum (fun τ =>
      (proc.rInt.filter (fun e => e.stepIdx = τ ∧ pred e)).card) =
      (proc.rInt.filter pred).card := by
  let F : ℕ → Finset InternalPopRot := fun τ =>
    proc.rInt.filter (fun e => e.stepIdx = τ ∧ pred e)
  have hdisj : (Finset.range proc.steps.length : Set ℕ).PairwiseDisjoint F := by
    intro τ₁ _ τ₂ _ hne
    change Disjoint (F τ₁) (F τ₂)
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [F, Finset.mem_filter] at h1 h2
    exact hne (h1.2.1.symm.trans h2.2.1)
  have hbi : (Finset.range proc.steps.length).biUnion F = proc.rInt.filter pred := by
    ext e
    simp only [F, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨_, _, hr, _, hp⟩; exact ⟨hr, hp⟩
    · rintro ⟨hr, hp⟩
      exact ⟨e.stepIdx, (mem_rInt_props proc hr).1, hr, rfl, hp⟩
  rw [← hbi, Finset.card_biUnion hdisj]

theorem b3Intra_phi_before_eq_one
    {M P : ℕ} {proc : FoldedPopProcess P}
    (hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST)
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    (hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P)
    {e : InternalPopRot} (he : e ∈ b3Intra P proc chain) :
    phiNode P chain (proc.treeAt e.stepIdx) e.x = 1 := by
  have hP := hChain.1
  rw [b3Intra, Finset.mem_filter] at he
  obtain ⟨hr, hcond⟩ := he
  obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e hr
  dsimp only at hcond
  split_ifs at hcond with hbnd
  · obtain ⟨hs12, hz_le⟩ := hcond
    obtain ⟨hp1, hp2⟩ := rInt_foldedParent_before_pop proc hBST hr (by omega) (by omega)
    let kℓ : Fin (M + 1) := ⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le hbnd.2⟩
    have hSy := blockAt_mem_and_bounds hP (hChain.2.2.1 kℓ) (u := e.y) (by omega) (by omega)
    dsimp only at hSy
    have hSz : blockAt (chain kℓ) e.z = blockAt (chain kℓ) e.y :=
      blockAt_eq_of_mem hP (hChain.2.2.1 kℓ) hSy.1 ⟨by omega, hz_le⟩
    have hℓ_lt_yz : kℓ.val < partSepScale P chain e.y e.z :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) kℓ).mpr hSz.symm
    unfold phiNode
    dsimp only
    rw [hp1, hp2]
    simp only [kℓ] at hℓ_lt_yz
    have hc : 1 ≤ partSepScale P chain e.x e.y ∧ partSepScale P chain e.x e.y ≤ M ∧
        partSepScale P chain e.x e.y < partSepScale P chain e.y e.z :=
      ⟨hbnd.1, hbnd.2, hℓ_lt_yz⟩
    simp [hc]

theorem lem_5_4_from_5_3
    (hChainFromValid : ∀ (P r M : ℕ) (T : ScaleTree),
      ValidScaleTree P r M T → IsNestedPartitionChain P (scaleTreePartitionChain T P M))
    (hLca : Ty_scaleTree_lca_props)
    (h36 : Ty_lem_3_6_folded_laws)
    (h53 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        ((eEnter P T proc (scaleTreePartitionChain T P M)).card : ℝ) <
          (51 : ℝ) / 25 * (P : ℝ))
    (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (b3Intra P proc chain).card ≤ 2 * P + proc.kRot + (eEnter P T proc chain).card ∧
    ((b3Intra P proc chain).card : ℝ) < (151 : ℝ) / 25 * (P : ℝ) ∧
    (b3Intra P proc chain).card < 7 * P := by
  dsimp only
  let chain := scaleTreePartitionChain T P M
  let ee := eEnter P T proc chain
  have hP : 1 ≤ P := hValid.1
  have hScale : IsScaleTree r M T := hValid.2.1
  have hChain : IsNestedPartitionChain P chain := hChainFromValid P r M T hValid
  have hLaws := h36 P hP proc
  have hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST :=
    fun τ hτ => (hLaws.1.1 τ hτ).1
  have hSubIcc : ∀ τ ≤ proc.steps.length, keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P :=
    fun τ hτ => (hLaws.1.1 τ hτ).2.1
  have hParLt : ∀ τ ≤ proc.steps.length, ∀ v ∈ proc.treeAt τ,
      v < foldedParent P (proc.treeAt τ) v :=
    fun τ hτ => (hLaws.1.1 τ hτ).2.2.2
  have hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P := by
    intro e he
    obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := hLaws.2.1.2 e he
    exact ⟨h1, h2, h3, h4, h5⟩
  -- Stepwise `ℕ` potential inequality across `0 ≤ τ < L`
  let L := proc.steps.length
  let isPush : FoldedOp → Bool := fun | .push _ => true | _ => false
  let isUpper : FoldedOp → Bool := fun | .upperRot _ _ => true | _ => false
  let plusPred : InternalPopRot → Prop := fun e =>
    phiNode P chain (proc.treeAt e.stepIdx) e.x = 0 ∧
    phiNode P chain (proc.treeAt (e.stepIdx + 1)) e.x = 1
  let minusPred : InternalPopRot → Prop := fun e =>
    phiNode P chain (proc.treeAt e.stepIdx) e.x = 1 ∧
    phiNode P chain (proc.treeAt (e.stepIdx + 1)) e.x = 0
  let gainAt : ℕ → ℕ := fun τ =>
    (match proc.steps[τ]? with | some op => if isPush op then 1 else 0 | none => 0) +
    (match proc.steps[τ]? with | some op => if isUpper op then 1 else 0 | none => 0) +
    (proc.rInt.filter (fun e => e.stepIdx = τ ∧ plusPred e)).card
  let dropAt : ℕ → ℕ := fun τ =>
    (proc.rInt.filter (fun e => e.stepIdx = τ ∧ minusPred e)).card
  have hStepBound : ∀ τ < L,
      phiConf P chain (proc.treeAt (τ + 1)) + dropAt τ ≤
        phiConf P chain (proc.treeAt τ) + gainAt τ := by
    intro τ hτ
    have hget? : proc.steps[τ]? = some proc.steps[τ] := List.getElem?_eq_getElem hτ
    have hval := valid_stepAt proc τ hτ
    have hsucc := stateAt_succ proc τ hτ
    set t := proc.treeAt τ
    set t' := proc.treeAt (τ + 1)
    have ht_eq : (proc.stateAt τ).1 = t := rfl
    have ht'_eq : t' = ((proc.steps[τ]).step (proc.stateAt τ)).1 :=
      congrArg Prod.fst hsucc
    rcases hop : proc.steps[τ] with w | _ | ⟨u, v⟩ | s
    · -- `.push w`
      have hdrop0 : dropAt τ = 0 := by
        simp only [dropAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hbad
        have hpop := (mem_rInt_props proc he).2.2.2.2.1
        rw [hbad.1, hget?, hop] at hpop
        cases hpop
      have hgain_ge : 1 ≤ gainAt τ := by simp [gainAt, hget?, hop, isPush]
      rw [hop] at hval ht'_eq
      obtain ⟨_, _, hw_lt, hnil_iff, _⟩ := hval
      dsimp only [FoldedOp.step] at ht'_eq
      cases hb1 : (proc.stateAt τ).2 with
      | none =>
        rw [hb1] at ht'_eq hnil_iff
        have htnil : t = .nil := hnil_iff.mpr rfl
        have hkf' : keyFinset t' = {w} := by simp [ht'_eq, keyFinset]
        have hc1 : phiConf P chain t' ≤ 1 := by
          unfold phiConf; rw [hkf', Finset.sum_singleton]; exact phiNode_le_one P chain t' w
        rw [hdrop0]; omega
      | some b =>
        rw [hb1] at ht'_eq
        have hsub_kf : keyFinset t' ⊆ insert w (keyFinset t) := by
          rw [ht'_eq]; exact keyFinset_modifyLeftAt_push_sub t b w
        have hpar_eq : ∀ u : ℕ, w < u → foldedParent P t' u = foldedParent P t u := by
          intro u hwu
          unfold foldedParent
          split_ifs with hu_top
          · rfl
          · rw [ht'_eq]; exact foldedParentAux_modifyLeftAt_push t b w (P + 1) u hwu
        have hphi_eq : ∀ x ∈ keyFinset t, phiNode P chain t' x = phiNode P chain t x := by
          intro x hx
          have hx_mem : x ∈ t := (mem_iff_mem_keyFinset t x).mpr hx
          have hp1_eq : foldedParent P t' x = foldedParent P t x := hpar_eq x (hw_lt x hx_mem)
          have hp2_eq : foldedParent P t' (foldedParent P t x) =
              foldedParent P t (foldedParent P t x) := by
            rcases foldedParent_mem_or_top P t x with htop | hp1_mem
            · rw [htop]; simp [foldedParent]
            · exact hpar_eq _ (hw_lt _ hp1_mem)
          unfold phiNode; dsimp only; rw [hp1_eq, hp2_eq]
        have hsum_le : phiConf P chain t' ≤ (insert w (keyFinset t)).sum (phiNode P chain t') :=
          Finset.sum_le_sum_of_subset hsub_kf
        have hw_notin : w ∉ keyFinset t := by
          intro hw_in
          exact lt_irrefl _ (hw_lt w ((mem_iff_mem_keyFinset t w).mpr hw_in))
        rw [Finset.sum_insert hw_notin] at hsum_le
        have hsum_congr : (keyFinset t).sum (phiNode P chain t') = phiConf P chain t :=
          Finset.sum_congr rfl hphi_eq
        have hw_le1 : phiNode P chain t' w ≤ 1 := phiNode_le_one P chain t' w
        rw [hsum_congr] at hsum_le
        change phiConf P chain t' + dropAt τ ≤ phiConf P chain t + gainAt τ
        rw [hdrop0]; omega
    · -- `.shift`
      have hdrop0 : dropAt τ = 0 := by
        simp only [dropAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hbad
        have hpop := (mem_rInt_props proc he).2.2.2.2.1
        rw [hbad.1, hget?, hop] at hpop
        cases hpop
      rw [hop] at ht'_eq
      have ht_same : t' = t := by
        dsimp only [FoldedOp.step] at ht'_eq
        cases hb : (proc.stateAt τ).2 <;> simp [hb] at ht'_eq <;> exact ht'_eq
      change phiConf P chain t' + dropAt τ ≤ phiConf P chain t + gainAt τ
      rw [ht_same, hdrop0]
      omega
    · -- `.upperRot u v`
      have hdrop0 : dropAt τ = 0 := by
        simp only [dropAt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hbad
        have hpop := (mem_rInt_props proc he).2.2.2.2.1
        rw [hbad.1, hget?, hop] at hpop
        cases hpop
      have hgain_ge : 1 ≤ gainAt τ := by simp [gainAt, hget?, hop, isUpper]
      rw [hop] at hval ht'_eq
      obtain ⟨b, r_root, _, _, _, _, huv, _, hu_ls, hv_ls, hrot⟩ := hval
      have hkf_eq : keyFinset t' = keyFinset t := by
        rw [ht'_eq]; exact keyFinset_rotateRightEdge t u v
      have hup_law := hLaws.1.2.1 τ u v hτ (by rw [hget?, hop])
      dsimp only at hup_law
      obtain ⟨hpar_u, hpar_other⟩ := hup_law
      have hu_mem : u ∈ t := (leftSpine_mem_and_pairwise (hBST τ (le_of_lt hτ))).1 u hu_ls
      have hv_mem : v ∈ t := (leftSpine_mem_and_pairwise (hBST τ (le_of_lt hτ))).1 v hv_ls
      have hu_bounds : 1 ≤ u ∧ u ≤ P :=
        Finset.mem_Icc.mp (hSubIcc τ (le_of_lt hτ) ((mem_iff_mem_keyFinset t u).mp hu_mem))
      have hv_bounds : 1 ≤ v ∧ v ≤ P :=
        Finset.mem_Icc.mp (hSubIcc τ (le_of_lt hτ) ((mem_iff_mem_keyFinset t v).mp hv_mem))
      have hpar_tu : foldedParent P t u = v :=
        foldedParent_of_isRightRotEdge (hBST τ (le_of_lt hτ)) huv hu_bounds.2 hrot
      have hv_lt_z : v < foldedParent P t v := hParLt τ (le_of_lt hτ) v hv_mem
      have hz_le_top : foldedParent P t v ≤ P + 1 := by
        rcases foldedParent_mem_or_top P t v with htop | hm
        · omega
        · have := Finset.mem_Icc.mp (hSubIcc τ (le_of_lt hτ) ((mem_iff_mem_keyFinset t _).mp hm))
          omega
      have hmono_other : ∀ a ∈ (keyFinset t).erase u,
          phiNode P chain t' a ≤ phiNode P chain t a := by
        intro a ha
        obtain ⟨hane, ha_kf⟩ := Finset.mem_erase.mp ha
        have ha_mem' : a ∈ t' := (mem_iff_mem_keyFinset t' a).mpr (hkf_eq ▸ ha_kf)
        have hp1 : foldedParent P t' a = foldedParent P t a := hpar_other a ha_mem' hane
        apply phiNode_mono_p2 hp1
        rw [hp1]
        by_cases hp1_u : foldedParent P t a = u
        · rw [hp1_u, hpar_u, hpar_tu,
              partSepScale_ultrametric hChain hu_bounds.1 (le_of_lt huv) (le_of_lt hv_lt_z) hz_le_top]
          exact Nat.min_le_left _ _
        · rcases foldedParent_mem_or_top P t a with htop | hm
          · rw [htop]; simp [foldedParent]
          · have hm' : foldedParent P t a ∈ t' :=
              (mem_iff_mem_keyFinset t' _).mpr (hkf_eq ▸ (mem_iff_mem_keyFinset t _).mp hm)
            rw [hpar_other _ hm' hp1_u]
      have hu_kf : u ∈ keyFinset t := (mem_iff_mem_keyFinset t u).mp hu_mem
      have hsplit_t' : phiConf P chain t' =
          phiNode P chain t' u + ((keyFinset t).erase u).sum (phiNode P chain t') := by
        unfold phiConf
        rw [hkf_eq, ← Finset.add_sum_erase _ _ hu_kf]
      have hsplit_t : phiConf P chain t =
          phiNode P chain t u + ((keyFinset t).erase u).sum (phiNode P chain t) := by
        unfold phiConf
        rw [← Finset.add_sum_erase _ _ hu_kf]
      have herase_le : ((keyFinset t).erase u).sum (phiNode P chain t') ≤
          ((keyFinset t).erase u).sum (phiNode P chain t) :=
        Finset.sum_le_sum hmono_other
      have hu_le1 : phiNode P chain t' u ≤ 1 := phiNode_le_one P chain t' u
      rw [hdrop0]; omega
    · -- `.pop s`
      have hpop? : proc.steps[τ]? = some (.pop s) := by rw [hget?, hop]
      obtain ⟨hs1, hsP, hτ_pop⟩ := eq_popStepIdx_of_getElem? proc hpop?
      have hpop_law := hLaws.1.2.2.1 s hs1 hsP
      dsimp only at hpop_law
      rw [← hτ_pop] at hpop_law
      obtain ⟨hpar_prom, hpar_nonprom⟩ := hpop_law
      rw [hop] at hval ht'_eq
      obtain ⟨b, _, hmin_s, hb_eq, _⟩ := hval
      obtain ⟨hs_mem_t, hs_le_all, hkf_splice⟩ :=
        minKey?_mem_and_le t (hBST τ (le_of_lt hτ)) hmin_s
      have hkf_t' : keyFinset t' = (keyFinset t).erase s := by
        dsimp only [FoldedOp.step] at ht'_eq
        rw [hb_eq, ht_eq] at ht'_eq
        dsimp only at ht'_eq
        split_ifs at ht'_eq <;> dsimp only at ht'_eq <;> rw [ht'_eq] <;>
          simp only [keyFinset_foldl_rotateRightEdge, hkf_splice]
      set rots_s := proc.rInt.filter (fun e => e.stepIdx = τ)
      set X_s := rots_s.image InternalPopRot.x
      have hX_sub : X_s ⊆ keyFinset t' := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨e, he_rots, rfl⟩ := hx
        rw [Finset.mem_filter] at he_rots
        obtain ⟨hr_e, hstep_e⟩ := he_rots
        have hx_ls := (rInt_mem_leftSpine proc hr_e).1
        rw [hstep_e] at hx_ls
        have hx_t : e.x ∈ keyFinset t :=
          (mem_iff_mem_keyFinset t e.x).mp ((leftSpine_mem_and_pairwise (hBST τ (le_of_lt hτ))).1 _ hx_ls)
        have hs_e : e.s = s := by
          have hp := (mem_rInt_props proc hr_e).2.2.2.2.1
          rw [hstep_e, hpop?] at hp
          exact (FoldedOp.pop.inj (Option.some.inj hp)).symm
        have hs_lt_x : s < e.x := hs_e ▸ (hOrd e hr_e).2.1
        rw [hkf_t', Finset.mem_erase]
        exact ⟨by omega, hx_t⟩
      have hinj_x : Set.InjOn InternalPopRot.x (rots_s : Set InternalPopRot) := by
        intro e₁ he₁ e₂ he₂ hxeq
        rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
        have hsame : e₁.stepIdx = e₂.stepIdx := he₁.2.trans he₂.2.symm
        rcases lt_trichotomy e₁.j e₂.j with hjlt | hjeq | hjgt
        · exfalso
          have := rInt_same_step_lt proc hBST he₁.1 he₂.1 hsame hjlt
          have := hOrd e₁ he₁.1
          omega
        · exact rInt_ext_stepIdx_j proc he₁.1 he₂.1 hsame hjeq
        · exfalso
          have := rInt_same_step_lt proc hBST he₂.1 he₁.1 hsame.symm hjgt
          have := hOrd e₂ he₂.1
          omega
      -- Non-promoted keys `a ∈ keyFinset t' \ X_s` have `phiNode t' a ≤ phiNode t a`
      have hnonprom_mono : ∀ a ∈ keyFinset t' \ X_s,
          phiNode P chain t' a ≤ phiNode P chain t a := by
        intro a ha
        obtain ⟨ha_kf', ha_notX⟩ := Finset.mem_sdiff.mp ha
        have ha_mem' : a ∈ t' := (mem_iff_mem_keyFinset t' a).mpr ha_kf'
        have ha_mem_t : a ∈ t := by
          rw [hkf_t', Finset.mem_erase] at ha_kf'
          exact (mem_iff_mem_keyFinset t a).mpr ha_kf'.2
        have ha_not_prom : ∀ e ∈ proc.rInt, e.stepIdx = τ → a ≠ e.x := by
          intro e hr_e hst_e hax
          apply ha_notX
          rw [Finset.mem_image]
          exact ⟨e, Finset.mem_filter.mpr ⟨hr_e, hst_e⟩, hax.symm⟩
        have hp1 : foldedParent P t' a = foldedParent P t a := hpar_nonprom a ha_mem' ha_not_prom
        apply phiNode_mono_p2 hp1
        rw [hp1]
        by_cases hp1_in_X : foldedParent P t a ∈ X_s
        · rw [Finset.mem_image] at hp1_in_X
          obtain ⟨e, he_rots, hp1_eq_ex⟩ := hp1_in_X
          rw [Finset.mem_filter] at he_rots
          obtain ⟨hr_e, hst_e⟩ := he_rots
          obtain ⟨_, _, hxy, hyz, hzP⟩ := hOrd e hr_e
          have hx1 : 1 ≤ e.x := by have := hOrd e hr_e; omega
          have hp_before := (rInt_foldedParent_before_pop proc hBST hr_e (by omega) (by omega)).1
          rw [hst_e] at hp_before
          have hp_after := hpar_prom e hr_e hst_e
          rw [← hp1_eq_ex, hp_after, hp_before,
              partSepScale_ultrametric hChain hx1 (le_of_lt hxy) (le_of_lt hyz) (by omega)]
          exact Nat.min_le_left _ _
        · rcases foldedParent_mem_or_top P t a with htop | hp1_mem_t
          · rw [htop]; simp [foldedParent]
          · have hs_le_a : s ≤ a := hs_le_all a ha_mem_t
            have ha_lt_p1 : a < foldedParent P t a := hParLt τ (le_of_lt hτ) a ha_mem_t
            have hp1_kf' : foldedParent P t a ∈ keyFinset t' := by
              rw [hkf_t', Finset.mem_erase]
              exact ⟨by omega, (mem_iff_mem_keyFinset t _).mp hp1_mem_t⟩
            have hp1_mem' : foldedParent P t a ∈ t' :=
              (mem_iff_mem_keyFinset t' _).mpr hp1_kf'
            have hp1_not_prom : ∀ e ∈ proc.rInt, e.stepIdx = τ → foldedParent P t a ≠ e.x := by
              intro e hr_e hst_e heq
              exact hp1_in_X (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨hr_e, hst_e⟩, heq.symm⟩)
            rw [hpar_nonprom _ hp1_mem' hp1_not_prom]
      -- Promoted keys `X_s` accounting identity
      let plus_s := rots_s.filter plusPred
      let minus_s := rots_s.filter minusPred
      have hplus_eq : plus_s = proc.rInt.filter (fun e => e.stepIdx = τ ∧ plusPred e) := by
        ext e; simp [plus_s, rots_s, and_assoc]
      have hminus_eq : minus_s = proc.rInt.filter (fun e => e.stepIdx = τ ∧ minusPred e) := by
        ext e; simp [minus_s, rots_s, and_assoc]
      have hX_acct : X_s.sum (phiNode P chain t') + minus_s.card =
          X_s.sum (phiNode P chain t) + plus_s.card := by
        rw [Finset.sum_image hinj_x, Finset.sum_image hinj_x,
            Finset.card_filter, Finset.card_filter,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e he_rots
        have hstep_e : e.stepIdx = τ := (Finset.mem_filter.mp he_rots).2
        change phiNode P chain t' e.x +
            (if phiNode P chain (proc.treeAt e.stepIdx) e.x = 1 ∧
                phiNode P chain (proc.treeAt (e.stepIdx + 1)) e.x = 0 then 1 else 0) =
          phiNode P chain t e.x +
            (if phiNode P chain (proc.treeAt e.stepIdx) e.x = 0 ∧
                phiNode P chain (proc.treeAt (e.stepIdx + 1)) e.x = 1 then 1 else 0)
        rw [hstep_e]
        change phiNode P chain t' e.x +
            (if phiNode P chain t e.x = 1 ∧ phiNode P chain t' e.x = 0 then 1 else 0) =
          phiNode P chain t e.x +
            (if phiNode P chain t e.x = 0 ∧ phiNode P chain t' e.x = 1 then 1 else 0)
        have h0 := phiNode_le_one P chain t e.x
        have h1 := phiNode_le_one P chain t' e.x
        split_ifs <;> omega
      have hsplit_t' : phiConf P chain t' =
          (keyFinset t' \ X_s).sum (phiNode P chain t') + X_s.sum (phiNode P chain t') := by
        unfold phiConf
        exact (Finset.sum_sdiff hX_sub).symm
      have hX_sub_t : X_s ⊆ keyFinset t :=
        Finset.Subset.trans hX_sub (hkf_t' ▸ Finset.erase_subset s (keyFinset t))
      have hsdiff_sub : keyFinset t' \ X_s ⊆ keyFinset t \ X_s :=
        Finset.sdiff_subset_sdiff (hkf_t' ▸ Finset.erase_subset s (keyFinset t)) (Finset.Subset.refl _)
      have hsplit_t : (keyFinset t \ X_s).sum (phiNode P chain t) + X_s.sum (phiNode P chain t) =
          phiConf P chain t :=
        Finset.sum_sdiff hX_sub_t
      have hnonprom_sum_le : (keyFinset t' \ X_s).sum (phiNode P chain t') ≤
          (keyFinset t \ X_s).sum (phiNode P chain t) :=
        le_trans (Finset.sum_le_sum hnonprom_mono) (Finset.sum_le_sum_of_subset hsdiff_sub)
      have hgain_ge : plus_s.card ≤ gainAt τ := by
        simp only [gainAt, ← hplus_eq]; omega
      have hdrop_eq : dropAt τ = minus_s.card := by
        simp only [dropAt, ← hminus_eq]
      change phiConf P chain t' + dropAt τ ≤ phiConf P chain t + gainAt τ
      omega
  -- Telescope `hStepBound` from `0` to `L`
  have hTelescope : ∀ n ≤ L,
      phiConf P chain (proc.treeAt n) + (Finset.range n).sum dropAt ≤
        phiConf P chain (proc.treeAt 0) + (Finset.range n).sum gainAt := by
    intro n hn
    induction n with
    | zero => simp
    | succ k ih =>
      have ih_k := ih (by omega)
      have hst := hStepBound k (by omega)
      have hd : (Finset.range (k + 1)).sum dropAt = (Finset.range k).sum dropAt + dropAt k :=
        Finset.sum_range_succ dropAt k
      have hg : (Finset.range (k + 1)).sum gainAt = (Finset.range k).sum gainAt + gainAt k :=
        Finset.sum_range_succ gainAt k
      rw [hd, hg]
      omega
  have hAtL := hTelescope L le_rfl
  have hphi0 : phiConf P chain (proc.treeAt 0) = 0 := by
    simp [phiConf, FoldedPopProcess.treeAt, stateAt_zero, keyFinset]
  have hphiL : phiConf P chain (proc.treeAt L) = 0 := by
    simp [L, phiConf, FoldedPopProcess.treeAt, stateAt_length, keyFinset]
  rw [hphi0, hphiL, Nat.zero_add, Nat.zero_add] at hAtL
  -- Evaluate `(Finset.range L).sum gainAt` and `(Finset.range L).sum dropAt`
  have hSumGain : (Finset.range L).sum gainAt =
      P + proc.kRot + (proc.rInt.filter plusPred).card := by
    simp only [gainAt, Finset.sum_add_distrib]
    have hPushSum : (Finset.range L).sum (fun τ =>
        match proc.steps[τ]? with | some op => if isPush op then 1 else 0 | none => 0) = P := by
      refine (Finset.sum_congr rfl fun τ _ => ?_).trans
        ((sum_range_getElem?_bool proc.steps isPush).trans ?_)
      · cases proc.steps[τ]? <;> rfl
      · exact (congrArg List.length (List.filter_congr fun op _ => by cases op <;> rfl)).trans
          ((push_filterMap_len_eq_filter proc.steps).symm.trans
            ((congrArg List.length (List.filterMap_congr fun op _ => by cases op <;> rfl)).trans
              proc.hPushCount))
    have hUpperSum : (Finset.range L).sum (fun τ =>
        match proc.steps[τ]? with | some op => if isUpper op then 1 else 0 | none => 0) = proc.kRot := by
      refine (Finset.sum_congr rfl fun τ _ => ?_).trans
        ((sum_range_getElem?_bool proc.steps isUpper).trans ?_)
      · cases proc.steps[τ]? <;> rfl
      · unfold FoldedPopProcess.kRot
        exact congrArg List.length (List.filter_congr fun op _ => by cases op <;> rfl)
    rw [hPushSum, hUpperSum]
    dsimp only [L]
    rw [sum_range_rInt_stepIdx_card proc plusPred]
  have hSumDrop : (Finset.range L).sum dropAt = (proc.rInt.filter minusPred).card :=
    sum_range_rInt_stepIdx_card proc minusPred
  rw [hSumGain, hSumDrop] at hAtL
  -- Partition `plusAll` into `topPlus1` (`j = h`) and `intPlus1` (`j < h`)
  let topPlus1 := proc.rInt.filter (fun e => e.j = e.h ∧ plusPred e)
  let intPlus1 := proc.rInt.filter (fun e => e.j < e.h ∧ plusPred e)
  have hPlusLe : (proc.rInt.filter plusPred).card ≤ topPlus1.card + intPlus1.card := by
    have hsub : proc.rInt.filter plusPred ⊆ topPlus1 ∪ intPlus1 := by
      intro e he
      rw [Finset.mem_filter] at he
      have hj_le := (mem_rInt_props proc he.1).2.2.2.2.2.2.1
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases eq_or_lt_of_le hj_le with htop | hlt
      · exact Or.inl ⟨he.1, htop, he.2⟩
      · exact Or.inr ⟨he.1, hlt, he.2⟩
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  -- Partition `b3Intra` into Type 1 (`j = h`), Type 2 (`j < h` confined), Type 3 (`j < h` escaping)
  let b3_1 := (b3Intra P proc chain).filter (fun e => e.j = e.h)
  let isEscaping : InternalPopRot → Prop := fun e =>
    ∃ h : 1 ≤ partSepScale P chain e.x e.y ∧ partSepScale P chain e.x e.y ≤ M,
      ∃ eNext, proc.nextCascadeRot? e = some eNext ∧
        (blockAt (chain ⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le h.2⟩) e.y).hi < eNext.y
  let b3_2 := (b3Intra P proc chain).filter (fun e => e.j < e.h ∧ ¬ isEscaping e)
  let b3_3 := (b3Intra P proc chain).filter (fun e => e.j < e.h ∧ isEscaping e)
  have hb3_cov : b3Intra P proc chain ⊆ b3_1 ∪ (b3_2 ∪ b3_3) := by
    intro e he
    have hr : e ∈ proc.rInt := (Finset.mem_filter.mp he).1
    have hj_le := (mem_rInt_props proc hr).2.2.2.2.2.2.1
    simp only [b3_1, b3_2, b3_3, Finset.mem_union, Finset.mem_filter]
    rcases eq_or_lt_of_le hj_le with htop | hlt
    · exact Or.inl ⟨he, htop⟩
    · by_cases hesc : isEscaping e
      · exact Or.inr (Or.inr ⟨he, hlt, hesc⟩)
      · exact Or.inr (Or.inl ⟨he, hlt, hesc⟩)
  have hb3_card_le : (b3Intra P proc chain).card ≤ b3_1.card + b3_2.card + b3_3.card := by
    have h1 := Finset.card_le_card hb3_cov
    have h2 := Finset.card_union_le b3_1 (b3_2 ∪ b3_3)
    have h3 := Finset.card_union_le b3_2 b3_3
    omega
  -- Bound 1: `b3_1.card + topPlus1.card ≤ P`
  have hTopBound : b3_1.card + topPlus1.card ≤ P := by
    have hdisj : Disjoint b3_1 topPlus1 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      simp only [b3_1, topPlus1, plusPred, Finset.mem_filter] at h1 h2
      have hp1 := b3Intra_phi_before_eq_one hBST hChain hOrd h1.1
      omega
    have hinj : Set.InjOn InternalPopRot.s ((b3_1 ∪ topPlus1 : Finset InternalPopRot) : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ hs_eq
      rw [Finset.mem_coe, Finset.mem_union] at he₁ he₂
      have hr₁ : e₁ ∈ proc.rInt ∧ e₁.j = e₁.h := by
        rcases he₁ with h | h
        · rw [Finset.mem_filter] at h; exact ⟨(Finset.mem_filter.mp h.1).1, h.2⟩
        · rw [Finset.mem_filter] at h; exact ⟨h.1, h.2.1⟩
      have hr₂ : e₂ ∈ proc.rInt ∧ e₂.j = e₂.h := by
        rcases he₂ with h | h
        · rw [Finset.mem_filter] at h; exact ⟨(Finset.mem_filter.mp h.1).1, h.2⟩
        · rw [Finset.mem_filter] at h; exact ⟨h.1, h.2.1⟩
      obtain ⟨hstep, hh_eq⟩ := rInt_same_s_step_and_h proc hr₁.1 hr₂.1 hs_eq
      exact rInt_ext_stepIdx_j proc hr₁.1 hr₂.1 hstep (by omega)
    have hmaps : Set.MapsTo InternalPopRot.s
        ((b3_1 ∪ topPlus1 : Finset InternalPopRot) : Set InternalPopRot)
        (Finset.Icc 1 P : Set ℕ) := by
      intro e he
      rw [Finset.mem_coe, Finset.mem_union] at he
      have hr : e ∈ proc.rInt := by
        rcases he with h | h
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
        · exact (Finset.mem_filter.mp h).1
      obtain ⟨_, hs1_e, hsP_e, _⟩ := mem_rInt_props proc hr
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨hs1_e, hsP_e⟩
    rw [← Finset.card_union_of_disjoint hdisj]
    calc (b3_1 ∪ topPlus1).card
        ≤ (Finset.Icc 1 P).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = P := by simp
  -- Helper: if `1 ≤ sep(s, z) ≤ ℓ ≤ M` and `ℓ < sep(z, yN)`, then `eNext ∈ b1 ∪ bLeafPre`
  have hTargetOfSep : ∀ {eNext : InternalPopRot}, eNext ∈ proc.rInt →
      ∀ ℓ : ℕ, ℓ ≤ M →
        partSepScale P chain eNext.s eNext.x ≤ ℓ →
        ℓ < partSepScale P chain eNext.x eNext.y →
        eNext ∈ b1 P proc chain ∪ bLeafPre P proc chain := by
    intro eNext hrN ℓ hℓM hsz_le hxy_gt
    obtain ⟨hs1N, hsxN, hxyN, _, hzPN⟩ := hOrd eNext hrN
    have hbnd_sx := partSepScale_bounds P chain hs1N (by omega) (by omega) (by omega) (u := eNext.s) (v := eNext.x)
    have hbnd_xy := partSepScale_bounds P chain (by omega) (by omega) (by omega) (by omega) (u := eNext.x) (v := eNext.y)
    by_cases htopM : partSepScale P chain eNext.x eNext.y = M + 1
    · apply Finset.mem_union_right
      rw [bLeafPre, Finset.mem_filter]
      refine ⟨hrN, htopM, ?_⟩
      have hne_leaf : blockAt (chain (Fin.last M)) eNext.s ≠ blockAt (chain (Fin.last M)) eNext.x := by
        intro heq
        have hlt := (lt_partSepScale_iff hChain hs1N (by omega) (by omega) (by omega) (Fin.last M)).mpr heq
        simp at hlt; omega
      have hlt_blk := blockAt_lt_of_ne hP (hChain.2.2.1 (Fin.last M)) hs1N (le_of_lt hsxN) (by omega) hne_leaf
      have hBs := blockAt_mem_and_bounds hP (hChain.2.2.1 (Fin.last M)) hs1N (by omega) (u := eNext.s)
      dsimp only at hBs
      omega
    · apply Finset.mem_union_left
      rw [b1, Finset.mem_filter]
      exact ⟨hrN, hbnd_sx.1, by omega, by omega⟩
  -- Bound 2: `b3_2 ⊆ ee`, `intPlus1 ⊆ ee`, and `Disjoint b3_2 intPlus1`
  have hb3_2_sub_ee : b3_2 ⊆ ee := by
    intro e he
    simp only [b3_2, Finset.mem_filter] at he
    obtain ⟨hb3_e, hjlt, hnot_esc⟩ := he
    have hb3_orig := hb3_e
    rw [b3Intra, Finset.mem_filter] at hb3_e
    obtain ⟨hr, hcond⟩ := hb3_e
    dsimp only at hcond
    split_ifs at hcond with hbnd
    obtain ⟨hs12, hz_le⟩ := hcond
    obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e hr
    obtain ⟨eNext, hrN, hfindN, _, hsN, _, _, hxN⟩ := nextCascadeRot?_eq_some_of_lt proc hr hjlt
    obtain ⟨_, _, hxyN, _, hzPN⟩ := hOrd eNext hrN
    have hyN_le : eNext.y ≤ (blockAt (chain ⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le hbnd.2⟩) e.y).hi := by
      by_contra hgt
      exact hnot_esc ⟨hbnd, eNext, hfindN, Nat.lt_of_not_le hgt⟩
    let kℓ : Fin (M + 1) := ⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le hbnd.2⟩
    have hSy := blockAt_mem_and_bounds hP (hChain.2.2.1 kℓ) (u := e.y) (by omega) (by omega)
    dsimp only at hSy
    have hSz : blockAt (chain kℓ) e.z = blockAt (chain kℓ) e.y :=
      blockAt_eq_of_mem hP (hChain.2.2.1 kℓ) hSy.1 ⟨by omega, hz_le⟩
    have hSyN : blockAt (chain kℓ) eNext.y = blockAt (chain kℓ) e.y :=
      blockAt_eq_of_mem hP (hChain.2.2.1 kℓ) hSy.1 ⟨by omega, hyN_le⟩
    have hℓ_lt_yz : kℓ.val < partSepScale P chain e.y e.z :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) kℓ).mpr hSz.symm
    have hℓ_lt_xyN : kℓ.val < partSepScale P chain eNext.x eNext.y :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) kℓ).mpr
        (by rw [hxN, hSz, hSyN])
    have hsep_xz : partSepScale P chain e.x e.z = partSepScale P chain e.x e.y := by
      rw [partSepScale_ultrametric hChain (by omega) (le_of_lt hxy) (le_of_lt hyz) (by omega)]
      simp only [kℓ] at hℓ_lt_yz; omega
    have hsep_sz : partSepScale P chain eNext.s eNext.x = partSepScale P chain e.x e.y := by
      rw [hsN, hxN, partSepScale_ultrametric hChain hs1 (le_of_lt hsx) (by omega) (by omega), hsep_xz, hs12]
      simp
    have hmem_target := hTargetOfSep hrN (partSepScale P chain e.x e.y) hbnd.2
      (le_of_eq hsep_sz) (by simpa [kℓ] using hℓ_lt_xyN)
    have hnot_b1 : e ∉ b1 P proc chain := by
      rw [b1, Finset.mem_filter]; omega
    change e ∈ eEnter P T proc chain
    rw [eEnter, Finset.mem_filter, Finset.mem_sdiff]
    refine ⟨⟨hr, fun hb1_only => hnot_b1 (Finset.mem_sdiff.mp hb1_only).1⟩, ?_⟩
    rw [hfindN]
    simp only [Option.elim_some, decide_eq_true_eq]
    exact hmem_target
  have hintPlus1_sub_ee : intPlus1 ⊆ ee := by
    intro e he
    simp only [intPlus1, plusPred, Finset.mem_filter] at he
    obtain ⟨hr, hjlt, hphi0_e, hphi1_e⟩ := he
    obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e hr
    obtain ⟨eNext, hrN, hfindN, hstepN, hsN, _, _, hxN⟩ := nextCascadeRot?_eq_some_of_lt proc hr hjlt
    obtain ⟨_, _, hxyN, hyzN, hzPN⟩ := hOrd eNext hrN
    have hτ_eq := (mem_rInt_props proc hr).2.2.2.1
    have hpop_law := (hLaws.1.2.2.1 e.s hs1 (by omega)).1
    rw [← hτ_eq] at hpop_law
    have hp1'_x : foldedParent P (proc.treeAt (e.stepIdx + 1)) e.x = e.z := hpop_law e hr rfl
    have hp2'_x : foldedParent P (proc.treeAt (e.stepIdx + 1)) e.z = eNext.z := by
      rw [← hxN]; exact hpop_law eNext hrN hstepN
    unfold phiNode at hphi1_e
    dsimp only at hphi1_e
    rw [hp1'_x, hp2'_x] at hphi1_e
    split_ifs at hphi1_e with hcond1
    obtain ⟨hℓ'1, hℓ'M, hℓ'_lt_zzN⟩ := hcond1
    set ℓ' := partSepScale P chain e.x e.z
    have hsz_le : partSepScale P chain eNext.s eNext.x ≤ ℓ' := by
      rw [hsN, hxN, partSepScale_ultrametric hChain hs1 (le_of_lt hsx) (by omega) (by omega)]
      exact Nat.min_le_right _ _
    have hzzN_le : partSepScale P chain e.z eNext.z ≤ partSepScale P chain eNext.x eNext.y := by
      rw [← hxN, partSepScale_ultrametric hChain (by omega) (le_of_lt hxyN) (le_of_lt hyzN) (by omega)]
      exact Nat.min_le_left _ _
    have hmem_target := hTargetOfSep hrN ℓ' hℓ'M hsz_le (Nat.lt_of_lt_of_le hℓ'_lt_zzN hzzN_le)
    -- Also show `e ∉ b1 \ s1Set`
    have hnot_b1_only : e ∉ b1 P proc chain \ s1Set P T proc chain := by
      intro hb1o
      rw [Finset.mem_sdiff] at hb1o
      obtain ⟨hb1_e, hns1_e⟩ := hb1o
      obtain ⟨hm, _, _, _, _, _, _, _, _, hℓ₂_m, _, hQ₂_mem, _, _, _, hQ₂_y, _, _⟩ :=
        b1_routing_bounds hLca hScale hChain hOrd hb1_e
      have hz_le_Q₂ : e.z ≤ (blockAt (chain ⟨_, Nat.lt_succ_of_le hm⟩) e.y).hi := by
        by_contra hgt
        apply hns1_e
        rw [s1Set, Finset.mem_filter]
        refine ⟨hb1_e, ?_⟩
        simp only [hm, ↓reduceDIte]
        exact Or.inl (Nat.lt_of_not_le hgt)
      let km : Fin (M + 1) := ⟨_, Nat.lt_succ_of_le hm⟩
      have hQz : blockAt (chain km) e.z = blockAt (chain km) e.y :=
        blockAt_eq_of_mem hP (hChain.2.2.1 km) hQ₂_mem ⟨by omega, hz_le_Q₂⟩
      rw [b1, Finset.mem_filter] at hb1_e
      obtain ⟨_, hℓ₁_1, hℓ₁₂, hℓ₂_M⟩ := hb1_e
      let kℓ₂ : Fin (M + 1) := ⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le hℓ₂_M⟩
      have hk_le : kℓ₂ ≤ km := Fin.le_iff_val_le_val.mpr hℓ₂_m
      have hQℓ₂ := nestedChain_blockAt_eq_mono hChain hk_le (by omega) (by omega) (by omega) (by omega) hQz.symm
      have hℓ₂_lt_yz : kℓ₂.val < partSepScale P chain e.y e.z :=
        (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) kℓ₂).mpr hQℓ₂
      obtain ⟨hp1_b, hp2_b⟩ := rInt_foldedParent_before_pop proc hBST hr (by omega) (by omega)
      have hp1_val : phiNode P chain (proc.treeAt e.stepIdx) e.x = 1 := by
        unfold phiNode; dsimp only; rw [hp1_b, hp2_b]
        simp only [kℓ₂] at hℓ₂_lt_yz
        have hc : 1 ≤ partSepScale P chain e.x e.y ∧ partSepScale P chain e.x e.y ≤ M ∧
            partSepScale P chain e.x e.y < partSepScale P chain e.y e.z :=
          ⟨by omega, hℓ₂_M, hℓ₂_lt_yz⟩
        simp [hc]
      omega
    change e ∈ eEnter P T proc chain
    rw [eEnter, Finset.mem_filter, Finset.mem_sdiff]
    refine ⟨⟨hr, hnot_b1_only⟩, ?_⟩
    rw [hfindN]
    simp only [Option.elim_some, decide_eq_true_eq]
    exact hmem_target
  have hEeBound : b3_2.card + intPlus1.card ≤ ee.card := by
    have hdisj : Disjoint b3_2 intPlus1 := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      simp only [b3_2, intPlus1, plusPred, Finset.mem_filter] at h1 h2
      have hp1 := b3Intra_phi_before_eq_one hBST hChain hOrd h1.1
      omega
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hb3_2_sub_ee hintPlus1_sub_ee)
  -- Bound 3: `b3_3 ⊆ proc.rInt.filter minusPred`, so `b3_3.card ≤ (proc.rInt.filter minusPred).card`
  have hb3_3_sub_minus : b3_3 ⊆ proc.rInt.filter minusPred := by
    intro e he
    simp only [b3_3, Finset.mem_filter] at he
    obtain ⟨hb3_e, hjlt, hbnd, eNext, hfindN, hyN_gt⟩ := he
    have hp_before := b3Intra_phi_before_eq_one hBST hChain hOrd hb3_e
    rw [b3Intra, Finset.mem_filter] at hb3_e
    obtain ⟨hr, hcond⟩ := hb3_e
    dsimp only at hcond
    simp only [hbnd] at hcond
    obtain ⟨_, hz_le⟩ := hcond
    obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e hr
    obtain ⟨eN', hrN', hfindN', hstepN', _, _, _, hxN'⟩ := nextCascadeRot?_eq_some_of_lt proc hr hjlt
    rw [hfindN'] at hfindN
    have heN_eq := Option.some.inj hfindN
    subst heN_eq
    obtain ⟨_, _, hxyN, hyzN, hzPN⟩ := hOrd eN' hrN'
    have hτ_eq := (mem_rInt_props proc hr).2.2.2.1
    have hpop_law := (hLaws.1.2.2.1 e.s hs1 (by omega)).1
    rw [← hτ_eq] at hpop_law
    have hp1'_x : foldedParent P (proc.treeAt (e.stepIdx + 1)) e.x = e.z := hpop_law e hr rfl
    have hp2'_x : foldedParent P (proc.treeAt (e.stepIdx + 1)) e.z = eN'.z := by
      rw [← hxN']; exact hpop_law eN' hrN' hstepN'
    let kℓ : Fin (M + 1) := ⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le hbnd.2⟩
    have hSy := blockAt_mem_and_bounds hP (hChain.2.2.1 kℓ) (u := e.y) (by omega) (by omega)
    dsimp only at hSy
    have hSz : blockAt (chain kℓ) e.z = blockAt (chain kℓ) e.y :=
      blockAt_eq_of_mem hP (hChain.2.2.1 kℓ) hSy.1 ⟨by omega, hz_le⟩
    have hℓ_lt_yz : kℓ.val < partSepScale P chain e.y e.z :=
      (lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) kℓ).mpr hSz.symm
    have hsep_xz : partSepScale P chain e.x e.z = partSepScale P chain e.x e.y := by
      rw [partSepScale_ultrametric hChain (by omega) (le_of_lt hxy) (le_of_lt hyz) (by omega)]
      simp only [kℓ] at hℓ_lt_yz; omega
    have hne_zzN : blockAt (chain kℓ) e.z ≠ blockAt (chain kℓ) eN'.z := by
      intro heq
      have hBzN := blockAt_mem_and_bounds hP (hChain.2.2.1 kℓ) (u := eN'.z) (by omega) (by omega)
      dsimp only at hBzN
      rw [← heq, hSz] at hBzN
      dsimp only [kℓ] at hBzN
      omega
    have hnot_lt_zzN : ¬ (kℓ.val < partSepScale P chain e.z eN'.z) := by
      intro hlt_zzN
      exact hne_zzN ((lt_partSepScale_iff hChain (by omega) (by omega) (by omega) (by omega) kℓ).mp hlt_zzN)
    have hp_after : phiNode P chain (proc.treeAt (e.stepIdx + 1)) e.x = 0 := by
      unfold phiNode; dsimp only; rw [hp1'_x, hp2'_x, hsep_xz]
      simp only [kℓ] at hnot_lt_zzN
      have hnc : ¬ (1 ≤ partSepScale P chain e.x e.y ∧ partSepScale P chain e.x e.y ≤ M ∧
          partSepScale P chain e.x e.y < partSepScale P chain e.z eN'.z) := by omega
      simp [hnc]
    rw [Finset.mem_filter]
    exact ⟨hr, hp_before, hp_after⟩
  have hb3_3_le : b3_3.card ≤ (proc.rInt.filter minusPred).card :=
    Finset.card_le_card hb3_3_sub_minus
  -- Combine all bounds!
  have hMainCard : (b3Intra P proc chain).card ≤ 2 * P + proc.kRot + ee.card := by
    omega
  -- Numerical / real corollaries
  have h2PkRot_lt : 2 * P + proc.kRot < 4 * P := hLaws.2.2.2.2.1
  have hee_real : (ee.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ) := h53 P r M T hValid proc
  have hP_real_pos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hMainReal : ((b3Intra P proc chain).card : ℝ) < (151 : ℝ) / 25 * (P : ℝ) := by
    have hc1 : ((b3Intra P proc chain).card : ℝ) ≤ (2 * P + proc.kRot : ℕ) + (ee.card : ℝ) := by
      exact_mod_cast hMainCard
    have hc2 : ((2 * P + proc.kRot : ℕ) : ℝ) < ((4 * P : ℕ) : ℝ) := by exact_mod_cast h2PkRot_lt
    push_cast at hc1 hc2
    linarith
  have h7P : (b3Intra P proc chain).card < 7 * P := by
    have hr7 : ((b3Intra P proc chain).card : ℝ) < ((7 * P : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hr7
  exact ⟨hMainCard, hMainReal, h7P⟩


end Core

/-! ## Exported Theorems (`Challenge.lean` Exact Signatures with Layer `0..1` Hypotheses) -/

/-- **Lemma 5.2** (`lem:bucket-leaf`, Intra-Leaf Rotations and Leaf Subprocess Projection):
For any nested contiguous-interval partition chain `𝒫_0 ≻ ... ≻ 𝒫_M` of `{1, ..., P}`,
`|ℬ_{leaf,pre}| ≤ P`, `|ℬ_{leaf,exit}| ≤ P`, and leaf subprocesses `{H̃^(Q)}_{Q ∈ 𝒫_M}` satisfy
`|ℬ_leaf| = |ℬ_{leaf,pre}| + |ℬ_{leaf,exit}| + |ℬ_{leaf,act}| ≤ 2 P + ∑_Q J(H̃^(Q))`. -/
theorem lem_5_2_bucket_leaf
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
    {M : ℕ} (P : ℕ) (hP : 1 ≤ P) (hM : 1 ≤ M)
    (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock)
    (hChain : IsNestedPartitionChain P chain) :
    let leaves := chain (Fin.last M)
    (bLeafPre P proc chain).card ≤ P ∧
    (bLeafExit P proc chain).card ≤ P ∧
    (bLeaf P proc chain).card =
      (bLeafPre P proc chain).card + (bLeafExit P proc chain).card +
        (bLeafAct P proc chain).card ∧
    (leaves.map IntervalBlock.size).sum = P ∧
    (∀ Q ∈ leaves, 1 ≤ Q.size) ∧
    ∃ subProcs : (Q : IntervalBlock) → Q ∈ leaves → FoldedPopProcess Q.size,
      (bLeafAct P proc chain).card =
        (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum ∧
      (bLeaf P proc chain).card ≤
        2 * P + (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum := by
  let _ := hM
  exact Core.lem_5_2_from_subproc Subproc52.exists_interval_subproc h_lem_3_6 P hP hM proc chain hChain

/-- **Lemma 5.3** (`lem:bucket-b1`, `LCA_𝒯` Routing of `ℬ_1` and Cascade-Path Sink Counting):
`𝒮_1 ⊆ ℬ_1` satisfies `|𝒮_1| ≤ P + 2 Σ_𝒯 < (26 / 25) P`,
(1) `|ℬ_1| ≤ r (|𝒮_1| + |ℬ_{leaf,pre}|) < (51 / 25) r P < 3 r P`, and
(2) `|ℰ_enter| ≤ |𝒮_1| + |ℬ_{leaf,pre}| < (51 / 25) P`. -/
theorem lem_5_3_bucket_b1
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
    let s1 := s1Set P T proc chain
    let ee := eEnter P T proc chain
    let lpre := bLeafPre P proc chain
    s1 ⊆ b1 P proc chain ∧
    s1.card ≤ P + 2 * sigmaScaleTree T chain ∧
    (s1.card : ℝ) < (26 : ℝ) / 25 * (P : ℝ) ∧
    (b1 P proc chain).card ≤ r * (s1.card + lpre.card) ∧
    ((b1 P proc chain).card : ℝ) < (51 : ℝ) / 25 * (r : ℝ) * (P : ℝ) ∧
    (b1 P proc chain).card < 3 * r * P ∧
    ee.card ≤ s1.card + lpre.card ∧
    (ee.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ) :=
  Core.lem_5_3_from_lca ScaleLca53.validScaleTree_chain ScaleLca53.scaleTree_lca_props
    h_lem_3_6 h_lem_5_1 P r M T hValid proc

/-- **Lemma 5.4** (`lem:bucket-b3-intra`, Height-Independent Bound on `ℬ_{3,intra}`):
`|ℬ_{3,intra}| ≤ 2 P + K_rot + |ℰ_enter| < (151 / 25) P < 7 P`, independently of `r, M, 𝒯`. -/
theorem lem_5_4_bucket_b3_intra
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
    (b3Intra P proc chain).card ≤ 2 * P + proc.kRot + (eEnter P T proc chain).card ∧
    ((b3Intra P proc chain).card : ℝ) < (151 : ℝ) / 25 * (P : ℝ) ∧
    (b3Intra P proc chain).card < 7 * P :=
  Core.lem_5_4_from_5_3 ScaleLca53.validScaleTree_chain ScaleLca53.scaleTree_lca_props h_lem_3_6
    (fun P' r' M' T' hV' proc' =>
      (lem_5_3_bucket_b1 h_lem_3_6 h_lem_5_1 P' r' M' T' hV' proc').2.2.2.2.2.2.2)
    P r M T hValid proc

end Solution.BucketLeafB1

end
