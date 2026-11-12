module

public import Challenge.Definitions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Scale-Tree Weight Convergence (Lemma 4.3) and Dyadic Collapse (Proposition 6.1)

This module proves:
1. `lem_4_3_tree_weights` (`main_v2.tex` Lemma 4.3)
2. `prop_6_1_dyadic_collapse` (`main_v2.tex` Proposition 6.1)
unconditionally (`0` upstream hypotheses) from `Challenge.Definitions`.
-/

@[expose] public section

namespace Solution.ScaleWeights

open SplayTree

/-!
================================================================================
Section 1: Finite Reciprocal-Square Sum and `pathWeight` Algebra
================================================================================
-/

/-- Finite sum `∑_{i=0}^{n-1} 1 / (4 (c₀ + i)^2)` over `List.range' c₀ n`. -/
noncomputable def invSqSum (c₀ n : ℕ) : ℝ :=
  ((List.range' c₀ n).map (fun c => (1 : ℝ) / (4 * (c : ℝ) ^ 2))).sum

theorem invSqSum_zero (c₀ : ℕ) : invSqSum c₀ 0 = 0 := by
  simp [invSqSum]

theorem invSqSum_succ (c₀ n : ℕ) :
    invSqSum c₀ (n + 1) = (1 : ℝ) / (4 * (c₀ : ℝ) ^ 2) + invSqSum (c₀ + 1) n := by
  simp [invSqSum, List.range']

theorem invSqSum_le_of_two_le :
    ∀ (n c₀ : ℕ), 2 ≤ c₀ → invSqSum c₀ n ≤ (1 : ℝ) / (4 * ((c₀ : ℝ) - 1))
  | 0, c₀, hc₀ => by
    rw [invSqSum_zero]
    have hcR : (2 : ℝ) ≤ (c₀ : ℝ) := by exact_mod_cast hc₀
    have hpos : (0 : ℝ) < 4 * ((c₀ : ℝ) - 1) := by linarith
    exact div_nonneg zero_le_one (le_of_lt hpos)
  | n + 1, c₀, hc₀ => by
    rw [invSqSum_succ]
    have ih := invSqSum_le_of_two_le n (c₀ + 1) (by omega)
    have hsub : (((c₀ + 1 : ℕ) : ℝ) - 1) = (c₀ : ℝ) := by push_cast; ring
    rw [hsub] at ih
    have hcR : (2 : ℝ) ≤ (c₀ : ℝ) := by exact_mod_cast hc₀
    have hc_pos : (0 : ℝ) < (c₀ : ℝ) := by linarith
    have hc1_pos : (0 : ℝ) < (c₀ : ℝ) - 1 := by linarith
    have hstep :
        (1 : ℝ) / (4 * (c₀ : ℝ) ^ 2) + (1 : ℝ) / (4 * (c₀ : ℝ)) ≤
          (1 : ℝ) / (4 * ((c₀ : ℝ) - 1)) := by
      rw [div_add_div, div_le_div_iff₀]
      · nlinarith
      · positivity
      · positivity
      · positivity
      · positivity
    linarith

theorem invSqSum_one_lt_half (k : ℕ) : invSqSum 1 k < (1 : ℝ) / 2 := by
  cases k with
  | zero =>
    rw [invSqSum_zero]
    norm_num
  | succ k₁ =>
    cases k₁ with
    | zero =>
      rw [invSqSum_succ, invSqSum_zero]
      norm_num
    | succ k₂ =>
      rw [invSqSum_succ, invSqSum_succ]
      have h3 := invSqSum_le_of_two_le k₂ 3 (by omega)
      norm_num at h3 ⊢
      linarith

theorem pathWeight_nil : pathWeight [] = 1 := rfl

theorem pathWeight_foldl (ξ : List ℕ) (init : ℕ) :
    ξ.foldl (fun w c => w * (4 * c ^ 2)) init = init * pathWeight ξ := by
  induction ξ generalizing init with
  | nil => simp [pathWeight]
  | cons c rest ih =>
    simp only [pathWeight, List.foldl_cons, Nat.one_mul]
    rw [ih (init * (4 * c ^ 2)), ih (4 * c ^ 2)]
    ring

theorem pathWeight_cons (c : ℕ) (ξ : List ℕ) :
    pathWeight (c :: ξ) = 4 * c ^ 2 * pathWeight ξ := by
  unfold pathWeight
  simp only [List.foldl_cons, Nat.one_mul]
  exact pathWeight_foldl ξ (4 * c ^ 2)

theorem pathWeight_append (ξ₁ ξ₂ : List ℕ) :
    pathWeight (ξ₁ ++ ξ₂) = pathWeight ξ₁ * pathWeight ξ₂ := by
  unfold pathWeight
  rw [List.foldl_append]
  exact pathWeight_foldl ξ₂ (pathWeight ξ₁)

theorem pathWeight_pos (ξ : List ℕ) (hξ : ∀ c ∈ ξ, 1 ≤ c) : 1 ≤ pathWeight ξ := by
  induction ξ with
  | nil => simp [pathWeight]
  | cons c rest ih =>
    rw [pathWeight_cons]
    have hc : 1 ≤ c := hξ c List.mem_cons_self
    have hrest : 1 ≤ pathWeight rest := ih (fun x hx => hξ x (List.mem_cons_of_mem c hx))
    nlinarith


/-!
================================================================================
Section 2: `ScaleTree` Leaf Weights, Internal Weights, and Scale Floor
================================================================================
-/

mutual
  theorem leafEntries_coords_pos :
      ∀ (T : ScaleTree) (entry : ℕ × List ℕ), entry ∈ T.leafEntries → ∀ c ∈ entry.2, 1 ≤ c
    | .leaf _, entry, hentry, c, hc => by
      simp [ScaleTree.leafEntries] at hentry
      rcases hentry with ⟨_, rfl⟩
      cases hc
    | .internal cs, entry, hentry, c, hc =>
      leafEntriesChildren_coords_pos 1 cs (by omega) entry hentry c hc

  theorem leafEntriesChildren_coords_pos :
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
        · exact leafEntries_coords_pos child (s, rest) hmem c hcrest
      · exact leafEntriesChildren_coords_pos (c₀ + 1) cs (by omega) entry hrest c hc
end

private theorem list_sum_const_mul (a : ℝ) (xs : List β) (g : β → ℝ) :
    (xs.map (fun x => a * g x)).sum = a * (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

mutual
  theorem leafEntries_weight_sum_le_one :
      ∀ (sub : ScaleTree),
        (sub.leafEntries.map (fun e => (1 : ℝ) / (pathWeight e.2 : ℝ))).sum ≤ 1
    | .leaf _ => by
      simp [ScaleTree.leafEntries, pathWeight]
    | .internal cs => by
      simp only [ScaleTree.leafEntries]
      have h1 := leafEntriesChildren_weight_sum_le 1 cs
      have h2 := invSqSum_one_lt_half cs.length
      linarith

  theorem leafEntriesChildren_weight_sum_le :
      ∀ (c₀ : ℕ) (cs : List ScaleTree),
        ((ScaleTree.leafEntriesChildren c₀ cs).map
          (fun e => (1 : ℝ) / (pathWeight e.2 : ℝ))).sum ≤ invSqSum c₀ cs.length
    | c₀, [] => by
      simp [ScaleTree.leafEntriesChildren, invSqSum_zero]
    | c₀, child :: rest => by
      simp only [ScaleTree.leafEntriesChildren, List.map_append, List.sum_append, List.map_map,
        List.length_cons, invSqSum_succ]
      have hfactor :
          (child.leafEntries.map
            ((fun e : ℕ × List ℕ => (1 : ℝ) / (pathWeight e.2 : ℝ)) ∘
              fun x : ℕ × List ℕ => (x.1, c₀ :: x.2))).sum =
          ((1 : ℝ) / (4 * (c₀ : ℝ) ^ 2)) *
            (child.leafEntries.map (fun e => (1 : ℝ) / (pathWeight e.2 : ℝ))).sum := by
        rw [← list_sum_const_mul]
        congr 1
        apply List.map_congr_left
        rintro ⟨s, addr⟩ _
        simp only [Function.comp_apply, pathWeight_cons, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
        ring
      rw [hfactor]
      have hchild := leafEntries_weight_sum_le_one child
      have hrest := leafEntriesChildren_weight_sum_le (c₀ + 1) rest
      have hnonneg : (0 : ℝ) ≤ (1 : ℝ) / (4 * (c₀ : ℝ) ^ 2) := by positivity
      have hmul :
          ((1 : ℝ) / (4 * (c₀ : ℝ) ^ 2)) *
            (child.leafEntries.map (fun e => (1 : ℝ) / (pathWeight e.2 : ℝ))).sum ≤
          (1 : ℝ) / (4 * (c₀ : ℝ) ^ 2) := by
        calc ((1 : ℝ) / (4 * (c₀ : ℝ) ^ 2)) *
              (child.leafEntries.map (fun e => (1 : ℝ) / (pathWeight e.2 : ℝ))).sum
            ≤ ((1 : ℝ) / (4 * (c₀ : ℝ) ^ 2)) * 1 := mul_le_mul_of_nonneg_left hchild hnonneg
          _ = (1 : ℝ) / (4 * (c₀ : ℝ) ^ 2) := mul_one _
      linarith
end

mutual
  theorem internalAddrList_weight_sum_lt_two :
      ∀ (sub : ScaleTree),
        (sub.internalAddrList.map (fun ν => (1 : ℝ) / (pathWeight ν : ℝ))).sum < 2
    | .leaf _ => by
      simp [ScaleTree.internalAddrList]
    | .internal cs => by
      simp only [ScaleTree.internalAddrList, List.map_cons, List.sum_cons, pathWeight_nil,
        Nat.cast_one, div_one]
      have h1 := internalAddrChildren_weight_sum_le 1 cs
      have h2 := invSqSum_one_lt_half cs.length
      linarith

  theorem internalAddrChildren_weight_sum_le :
      ∀ (c₀ : ℕ) (cs : List ScaleTree),
        ((ScaleTree.internalAddrChildren c₀ cs).map
          (fun ν => (1 : ℝ) / (pathWeight ν : ℝ))).sum ≤ 2 * invSqSum c₀ cs.length
    | c₀, [] => by
      simp [ScaleTree.internalAddrChildren, invSqSum_zero]
    | c₀, child :: rest => by
      simp only [ScaleTree.internalAddrChildren, List.map_append, List.sum_append, List.map_map,
        List.length_cons, invSqSum_succ]
      have hfactor :
          (child.internalAddrList.map
            ((fun ν : List ℕ => (1 : ℝ) / (pathWeight ν : ℝ)) ∘ (c₀ :: ·))).sum =
          ((1 : ℝ) / (4 * (c₀ : ℝ) ^ 2)) *
            (child.internalAddrList.map (fun ν => (1 : ℝ) / (pathWeight ν : ℝ))).sum := by
        rw [← list_sum_const_mul]
        congr 1
        apply List.map_congr_left
        intro addr _
        simp only [Function.comp_apply, pathWeight_cons, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
        ring
      rw [hfactor]
      have hchild := le_of_lt (internalAddrList_weight_sum_lt_two child)
      have hrest := internalAddrChildren_weight_sum_le (c₀ + 1) rest
      have hnonneg : (0 : ℝ) ≤ (1 : ℝ) / (4 * (c₀ : ℝ) ^ 2) := by positivity
      have hmul :
          ((1 : ℝ) / (4 * (c₀ : ℝ) ^ 2)) *
            (child.internalAddrList.map (fun ν => (1 : ℝ) / (pathWeight ν : ℝ))).sum ≤
          ((1 : ℝ) / (4 * (c₀ : ℝ) ^ 2)) * 2 :=
        mul_le_mul_of_nonneg_left hchild hnonneg
      linarith
end

private theorem sum_toFinset_le_list_sum [DecidableEq α] (xs : List α) (f : α → ℝ)
    (hf : ∀ x ∈ xs, 0 ≤ f x) :
    (∑ x ∈ xs.toFinset, f x) ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    have hx : 0 ≤ f x := hf x List.mem_cons_self
    have hrest := ih (fun y hy => hf y (List.mem_cons_of_mem x hy))
    by_cases hmem : x ∈ rest.toFinset
    · rw [Finset.insert_eq_of_mem hmem]
      linarith
    · rw [Finset.sum_insert hmem]
      linarith

private theorem find_fst_of_nodup (xs : List (ℕ × List ℕ)) (hnd : (xs.map Prod.fst).Nodup)
    {s : ℕ} {addr : List ℕ} (hmem : (s, addr) ∈ xs) :
    xs.find? (fun e => e.1 == s) = some (s, addr) := by
  induction xs with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨s₀, a₀⟩
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases hnd with ⟨hnotmem, hnd_tl⟩
    simp only [List.mem_cons] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | htl
    · simp [List.find?]
    · have hne : s₀ ≠ s := by
        intro heq
        subst heq
        exact hnotmem (List.mem_map.mpr ⟨(s₀, addr), htl, rfl⟩)
      have hbeq : (s₀ == s) = false := beq_eq_false_iff_ne.mpr hne
      simp only [List.find?, hbeq]
      exact ih hnd_tl htl

private theorem sum_Icc_one_eq_range'_sum (M : ℕ) (f : ℕ → ℝ) :
    (∑ ℓ ∈ Finset.Icc 1 M, f ℓ) = ((List.range' 1 M).map f).sum := by
  induction M with
  | zero => simp
  | succ m ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_insert hnotmem, ih, List.range'_concat, List.map_append, List.sum_append]
    simp [Nat.add_comm 1 m, add_comm]

/-! ### Internal-node subtrees, `mEnd`, and Ackermann / scale floor -/

mutual
  theorem internalAddrList_spec :
      ∀ (T : ScaleTree), T.AllInternalNonempty →
        ∀ ν ∈ T.internalAddrList,
          (∀ c ∈ ν, 1 ≤ c) ∧
          ∃ cs : List ScaleTree, cs ≠ [] ∧ (ScaleTree.internal cs).AllInternalNonempty ∧
            subtreeAtAddr T ν = some (.internal cs)
    | .leaf _, _, ν, hν => by
      simp [ScaleTree.internalAddrList] at hν
    | .internal cs₀, hne, ν, hν => by
      have hne0 := hne
      rw [ScaleTree.AllInternalNonempty] at hne
      rcases hne with ⟨hcs_ne, hcs_all⟩
      simp only [ScaleTree.internalAddrList, List.mem_cons] at hν
      rcases hν with rfl | hchild
      · refine ⟨(by intro c hc; cases hc), cs₀, hcs_ne, hne0, rfl⟩
      · exact internalAddrChildren_spec 1 cs₀ cs₀ (by omega) rfl hcs_all ν hchild

  theorem internalAddrChildren_spec :
      ∀ (c₀ : ℕ) (cs₀ cs : List ScaleTree), 1 ≤ c₀ →
        cs₀.drop (c₀ - 1) = cs →
        (∀ ch ∈ cs, ch.AllInternalNonempty) →
        ∀ ν ∈ ScaleTree.internalAddrChildren c₀ cs,
          (∀ c ∈ ν, 1 ≤ c) ∧
          ∃ subCs : List ScaleTree, subCs ≠ [] ∧ (ScaleTree.internal subCs).AllInternalNonempty ∧
            subtreeAtAddr (.internal cs₀) ν = some (.internal subCs)
    | _, _, [], _, _, _, ν, hν => by
      simp [ScaleTree.internalAddrChildren] at hν
    | c₀, cs₀, child :: rest, hc₀, hdrop, hall, ν, hν => by
      simp only [ScaleTree.internalAddrChildren, List.mem_append, List.mem_map] at hν
      rcases hν with ⟨tailAddr, hmem, rfl⟩ | hrest
      · have hchild_ne : child.AllInternalNonempty := hall child List.mem_cons_self
        obtain ⟨hcoords, subCs, hsubNe, hsubAll, hsubAddr⟩ :=
          internalAddrList_spec child hchild_ne tailAddr hmem
        have hc₀_ne : c₀ ≠ 0 := by omega
        have hget : cs₀[c₀ - 1]? = some child := by
          have h1 : (cs₀.drop (c₀ - 1)).head? = some child := by rw [hdrop]; rfl
          rwa [List.head?_drop] at h1
        refine ⟨?_, subCs, hsubNe, hsubAll, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hxt
          · exact hc₀
          · exact hcoords x hxt
        · simp [subtreeAtAddr, hc₀_ne, hget, hsubAddr]
      · have hdrop' : cs₀.drop c₀ = rest := by
          have h1 : c₀ = (c₀ - 1) + 1 := by omega
          rw [h1, ← List.drop_drop, hdrop]
          rfl
        exact internalAddrChildren_spec (c₀ + 1) cs₀ rest (by omega) hdrop'
          (fun ch hch => hall ch (List.mem_cons_of_mem child hch)) ν hrest
end

private theorem leafEntriesChildren_mem_of_getElem :
    ∀ (c₀ : ℕ) (cs : List ScaleTree) (idx : ℕ) (hidx : idx < cs.length)
      {s : ℕ} {r : List ℕ},
      (s, r) ∈ cs[idx].leafEntries →
      (s, (c₀ + idx) :: r) ∈ ScaleTree.leafEntriesChildren c₀ cs
  | c₀, child :: _, 0, _, s, r, hmem => by
    simp only [ScaleTree.leafEntriesChildren, Nat.add_zero, List.mem_append, List.mem_map]
    exact Or.inl ⟨(s, r), hmem, rfl⟩
  | c₀, _ :: rest, idx + 1, hidx, s, r, hmem => by
    simp only [ScaleTree.leafEntriesChildren, List.mem_append]
    right
    have hidx' : idx < rest.length := Nat.lt_of_succ_lt_succ hidx
    have h := leafEntriesChildren_mem_of_getElem (c₀ + 1) rest idx hidx' hmem
    have heq : c₀ + 1 + idx = c₀ + (idx + 1) := by omega
    rwa [heq] at h

private theorem subtreeAtAddr_leafEntries :
    ∀ (T : ScaleTree) (ξ : List ℕ) (sub : ScaleTree),
      subtreeAtAddr T ξ = some sub →
      ∀ {s : ℕ} {r : List ℕ}, (s, r) ∈ sub.leafEntries → (s, ξ ++ r) ∈ T.leafEntries
  | T, [], sub, hsub, s, r, hmem => by
    simp only [subtreeAtAddr, Option.some.injEq] at hsub
    subst hsub
    simpa using hmem
  | .leaf _, _ :: _, _, hsub, _, _, _ => by
    simp [subtreeAtAddr] at hsub
  | .internal cs, c :: rest, sub, hsub, s, r, hmem => by
    simp only [subtreeAtAddr] at hsub
    split_ifs at hsub with hc0
    cases hget : cs[c - 1]? with
    | none => rw [hget] at hsub; simp at hsub
    | some child =>
      rw [hget] at hsub
      have hchild_mem := subtreeAtAddr_leafEntries child rest sub hsub hmem
      have ⟨hidx, hchild_eq⟩ := List.getElem?_eq_some_iff.mp hget
      subst hchild_eq
      have hstep := leafEntriesChildren_mem_of_getElem 1 cs (c - 1) hidx hchild_mem
      have hc_eq : 1 + (c - 1) = c := by omega
      rw [hc_eq] at hstep
      simpa [ScaleTree.leafEntries, List.cons_append] using hstep

private theorem allInternalNonempty_leafEntries_ne_nil :
    ∀ (sub : ScaleTree), sub.AllInternalNonempty → sub.leafEntries ≠ []
  | .leaf _, _ => by simp [ScaleTree.leafEntries]
  | .internal [], hne => by
    rw [ScaleTree.AllInternalNonempty] at hne
    exact absurd rfl hne.1
  | .internal (child :: rest), hne => by
    rw [ScaleTree.AllInternalNonempty] at hne
    have hch := allInternalNonempty_leafEntries_ne_nil child (hne.2 child List.mem_cons_self)
    simp only [ScaleTree.leafEntries, ScaleTree.leafEntriesChildren]
    intro hemp
    have h1 := (List.append_eq_nil_iff.mp hemp).1
    simp only [List.map_eq_nil_iff] at h1
    exact hch h1

private theorem getLast?_mem {α : Type} : ∀ {xs : List α} {x : α}, xs.getLast? = some x → x ∈ xs
  | [], _, h => by simp at h
  | [a], x, h => by simp at h; simp [h]
  | a :: b :: rest, x, h => List.mem_cons_of_mem a (getLast?_mem (xs := b :: rest) h)

private theorem getLast?_append_right {α : Type} (xs : List α) {ys : List α} (hys : ys ≠ []) :
    (xs ++ ys).getLast? = ys.getLast? := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hne : rest ++ ys ≠ [] := by
      intro h
      exact hys (List.append_eq_nil_iff.mp h).2
    cases h : rest ++ ys with
    | nil => exact absurd h hne
    | cons b bs =>
      have hstep : (x :: (rest ++ ys)).getLast? = (rest ++ ys).getLast? := by
        rw [h]
        rfl
      exact hstep.trans ih

private theorem leafEntriesChildren_getLast? :
    ∀ (c₀ : ℕ) (cs : List ScaleTree), cs ≠ [] →
      (∀ ch ∈ cs, ch.AllInternalNonempty) →
      ∃ ℓStar : ℕ, ∃ r : List ℕ,
        (ScaleTree.leafEntriesChildren c₀ cs).getLast? =
          some (ℓStar, (c₀ + cs.length - 1) :: r)
  | _, [], hne, _ => absurd rfl hne
  | c₀, [child], _, hall => by
    have hch := allInternalNonempty_leafEntries_ne_nil child (hall child List.mem_cons_self)
    rcases hlast : child.leafEntries.getLast? with _ | ⟨ℓStar, r⟩
    · exact absurd (List.getLast?_eq_none_iff.mp hlast) hch
    · refine ⟨ℓStar, r, ?_⟩
      simp only [ScaleTree.leafEntriesChildren, List.append_nil, List.length_singleton,
        Nat.add_sub_cancel, List.getLast?_map, hlast, Option.map_some]
  | c₀, child :: child₂ :: rest, _, hall => by
    obtain ⟨ℓStar, r, ih⟩ := leafEntriesChildren_getLast? (c₀ + 1) (child₂ :: rest)
      (by simp) (fun ch hch => hall ch (List.mem_cons_of_mem child hch))
    have hne_rhs : ScaleTree.leafEntriesChildren (c₀ + 1) (child₂ :: rest) ≠ [] := by
      intro hemp; rw [hemp] at ih; simp at ih
    refine ⟨ℓStar, r, ?_⟩
    rw [ScaleTree.leafEntriesChildren, getLast?_append_right _ hne_rhs, ih]
    have heq : c₀ + 1 + (child₂ :: rest).length - 1 = c₀ + (child :: child₂ :: rest).length - 1 := by
      simp only [List.length_cons]; omega
    rw [heq]

/-! ### Self-contained Ackermann & `alpha0` floor (`i_ℓ ≥ 5`) -/

private theorem ackermann_gt : ∀ (i j : ℕ), 1 ≤ j → j < ackermann i j
  | 0, j, hj => by simp [ackermann]; omega
  | 1, j, _ => by simp [ackermann]; exact Nat.lt_two_pow_self
  | i + 2, 0, hj => by omega
  | i + 2, 1, _ => by
    change 1 < ackermann (i + 1) 2
    exact lt_trans (by omega : 1 < 2) (ackermann_gt (i + 1) 2 (by omega))
  | i + 2, j + 2, _ => by
    change j + 2 < ackermann (i + 1) (ackermann (i + 2) (j + 1))
    have ihj := ackermann_gt (i + 2) (j + 1) (by omega)
    have ihi := ackermann_gt (i + 1) (ackermann (i + 2) (j + 1)) (by omega)
    omega

private theorem ackermann_lt_succ : ∀ (i j : ℕ), 1 ≤ j → ackermann i j < ackermann i (j + 1)
  | 0, j, _ => by simp [ackermann]
  | 1, j, _ => by
    simp only [ackermann]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  | i + 2, 0, hj => by omega
  | i + 2, 1, _ => by
    change ackermann (i + 2) 1 < ackermann (i + 1) (ackermann (i + 2) 1)
    have hpos : 1 ≤ ackermann (i + 2) 1 := by
      have := ackermann_gt (i + 2) 1 (by omega); omega
    exact ackermann_gt (i + 1) _ hpos
  | i + 2, j + 2, _ => by
    change ackermann (i + 2) (j + 2) < ackermann (i + 1) (ackermann (i + 2) (j + 2))
    have hpos : 1 ≤ ackermann (i + 2) (j + 2) := by
      have := ackermann_gt (i + 2) (j + 2) (by omega); omega
    exact ackermann_gt (i + 1) _ hpos

private theorem ackermann_col1_gt : ∀ (k : ℕ), 1 ≤ k → k < ackermann k 1
  | 0, hk => by omega
  | 1, _ => by decide
  | k + 2, _ => by
    have ih := ackermann_col1_gt (k + 1) (by omega)
    have hstep : ackermann (k + 1) 1 < ackermann (k + 1) 2 := ackermann_lt_succ (k + 1) 1 (by omega)
    change k + 2 < ackermann (k + 1) 2
    omega

private theorem alpha0_set_nonempty (n : ℕ) (hn : 1 ≤ n) :
    ({k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}).Nonempty :=
  ⟨n, hn, le_of_lt (ackermann_col1_gt n hn)⟩

private theorem alpha0_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ alpha0 n :=
  le_csInf (alpha0_set_nonempty n hn) (fun _ hk => hk.1)

private theorem alpha0_ge_four (n : ℕ) (hn : 17 ≤ n) : 4 ≤ alpha0 n := by
  have hmem := Nat.sInf_mem (alpha0_set_nonempty n (by omega))
  change 1 ≤ alpha0 n ∧ n ≤ ackermann (alpha0 n) 1 at hmem
  by_contra hlt
  have hcases : alpha0 n = 1 ∨ alpha0 n = 2 ∨ alpha0 n = 3 := by omega
  rcases hcases with h1 | h2 | h3
  · rw [h1] at hmem
    have hk : ackermann 1 1 = 2 := by decide
    rw [hk] at hmem
    omega
  · rw [h2] at hmem
    have hk : ackermann 2 1 = 4 := by decide
    rw [hk] at hmem
    omega
  · rw [h3] at hmem
    have hk : ackermann 3 1 = 16 := by decide
    rw [hk] at hmem
    omega

private theorem scaleS_pos (T : ScaleTree) (P : ℕ) (hP : 1 ≤ P) : ∀ ℓ : ℕ, 1 ≤ scaleS T P ℓ
  | 0 => hP
  | ℓ + 1 => by
    unfold scaleS
    have hw : 1 ≤ leafWeight T (ℓ + 1) := by
      unfold leafWeight leafAddr
      split
      · next s addr hfind =>
        exact pathWeight_pos addr (leafEntries_coords_pos T (s, addr) (List.mem_of_find?_eq_some hfind))
      · exact pathWeight_pos [] (by intro c hc; cases hc)
    have hsq : 1 ≤ (alpha0 (2 * scaleS T P ℓ) + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    exact Nat.mul_le_mul hw hsq

private theorem validScaleTree_scaleS_ge_25_weight (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓM : ℓ ≤ M) :
    25 * leafWeight T ℓ ≤ scaleS T P ℓ := by
  rcases hValid with ⟨hP, ⟨_, _, _, hLeaves, hDepth⟩, hHalf⟩
  have hmem_leaves : ℓ ∈ T.leaves := by
    rw [hLeaves]
    exact List.mem_range'.mpr ⟨ℓ - 1, by omega, by omega⟩
  unfold ScaleTree.leaves at hmem_leaves
  obtain ⟨⟨s, addr⟩, hentry, hs_eq⟩ := List.mem_map.mp hmem_leaves
  dsimp only at hs_eq
  subst s
  have hnd : (T.leafEntries.map Prod.fst).Nodup := by
    change T.leaves.Nodup
    rw [hLeaves]
    exact List.nodup_range'
  have hfind : leafAddr T ℓ = addr := by
    unfold leafAddr
    rw [find_fst_of_nodup T.leafEntries hnd hentry]
  have hlen1 : 1 ≤ addr.length := (hDepth (ℓ, addr) hentry).1
  have hw4 : 4 ≤ leafWeight T ℓ := by
    unfold leafWeight
    rw [hfind]
    cases addr with
    | nil => simp at hlen1
    | cons c rest =>
      rw [pathWeight_cons]
      have hcoords := leafEntries_coords_pos T (ℓ, c :: rest) hentry
      have hc1 : 1 ≤ c := hcoords c List.mem_cons_self
      have hr1 : 1 ≤ pathWeight rest :=
        pathWeight_pos rest (fun x hx => hcoords x (List.mem_cons_of_mem c hx))
      nlinarith
  obtain ⟨idx, rfl⟩ := Nat.exists_eq_add_of_le hℓ1
  rw [Nat.add_comm 1 idx] at hw4 hℓM ⊢
  set sPrev := scaleS T P idx
  have hsPrev1 : 1 ≤ sPrev := scaleS_pos T P hP idx
  have ha1 : 1 ≤ alpha0 (2 * sPrev) := alpha0_pos (2 * sPrev) (by omega)
  have hS_ge16 : 16 ≤ scaleS T P (idx + 1) := by
    unfold scaleS
    change 16 ≤ leafWeight T (idx + 1) * (alpha0 (2 * sPrev) + 1) ^ 2
    nlinarith
  have h2S_le : 2 * scaleS T P (idx + 1) ≤ sPrev := hHalf ⟨idx, by omega⟩
  have ha4 : 4 ≤ alpha0 (2 * sPrev) := alpha0_ge_four (2 * sPrev) (by omega)
  unfold scaleS
  change 25 * leafWeight T (idx + 1) ≤ leafWeight T (idx + 1) * (alpha0 (2 * sPrev) + 1) ^ 2
  have h25_sq : 25 ≤ (alpha0 (2 * sPrev) + 1) ^ 2 := by nlinarith
  calc 25 * leafWeight T (idx + 1)
      = leafWeight T (idx + 1) * 25 := by ring
    _ ≤ leafWeight T (idx + 1) * (alpha0 (2 * sPrev) + 1) ^ 2 :=
        Nat.mul_le_mul_left _ h25_sq

/-! ### Partition block-count bound on `scaleTreePartitionLevel` -/

private theorem splitIntervalBySize_props (X : IntervalBlock) (S : ℕ)
    (hXlo : 1 ≤ X.lo) (hS : 1 ≤ S) (h2S : 2 * S ≤ X.size) :
    (∀ Y ∈ splitIntervalBySize X S, 1 ≤ Y.lo ∧ S ≤ Y.size) ∧
      ((splitIntervalBySize X S).map IntervalBlock.size).sum = X.size := by
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
  have hK1S : (K - 1) * S + S = K * S := by
    have : (K - 1) + 1 = K := by omega
    calc (K - 1) * S + S = ((K - 1) + 1) * S := by ring
      _ = K * S := by rw [this]
  constructor
  · intro Y hY
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hY
    rw [List.mem_range] at hidx
    by_cases hlt : idx + 1 < K
    · simp only [hlt, ↓reduceIte]
      have hmul : (idx + 1) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
      have hstepS : idx * S + S = (idx + 1) * S := by ring
      have hlo_le : X.lo + idx * S ≤ X.lo + (idx + 1) * S - 1 := by omega
      exact ⟨by omega, by simp only [IntervalBlock.size, hlo_le, ↓reduceIte]; omega⟩
    · simp only [hlt, ↓reduceIte]
      have hidx_eq : idx = K - 1 := by omega
      subst hidx_eq
      have hlo_le : X.lo + (K - 1) * S ≤ X.hi := by omega
      exact ⟨by omega, by simp only [IntervalBlock.size, hlo_le, ↓reduceIte]; omega⟩
  · have hK_split : List.range K = List.range (K - 1) ++ [K - 1] := by
      have hK_eq : K = (K - 1) + 1 := by omega
      conv_lhs => rw [hK_eq, List.range_succ]
    rw [hK_split, List.map_append, List.map_append, List.sum_append]
    have hprefix :
        ((List.range (K - 1)).map (fun idx =>
          (if idx + 1 < K then
            ({ lo := X.lo + idx * S, hi := X.lo + (idx + 1) * S - 1 } : IntervalBlock)
          else { lo := X.lo + idx * S, hi := X.hi }).size)) =
        List.replicate (K - 1) S := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.length_map, List.length_range] at hi1
        simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
        have hlt : i + 1 < K := by omega
        simp only [hlt, ↓reduceIte]
        have hmul : (i + 1) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
        have hstepS : i * S + S = (i + 1) * S := by ring
        have hlo_le : X.lo + i * S ≤ X.lo + (i + 1) * S - 1 := by omega
        simp only [IntervalBlock.size, hlo_le, ↓reduceIte]
        omega
    have hmap_pref :
        (((List.range (K - 1)).map (fun idx =>
          if idx + 1 < K then
            ({ lo := X.lo + idx * S, hi := X.lo + (idx + 1) * S - 1 } : IntervalBlock)
          else { lo := X.lo + idx * S, hi := X.hi })).map IntervalBlock.size) =
        List.replicate (K - 1) S := by
      rw [List.map_map]
      exact hprefix
    rw [hmap_pref, List.sum_replicate, smul_eq_mul]
    simp only [List.map_singleton, List.sum_singleton]
    have hnlt : ¬ (K - 1 + 1 < K) := by omega
    simp only [hnlt, ↓reduceIte]
    have hlo_le : X.lo + (K - 1) * S ≤ X.hi := by omega
    rw [hXsz]
    simp only [IntervalBlock.size, hlo_le, ↓reduceIte]
    omega

private theorem flatMap_size_sum {α : Type} (xs : List α) (f : α → List IntervalBlock) :
    ((xs.flatMap f).map IntervalBlock.size).sum =
      (xs.map (fun x => ((f x).map IntervalBlock.size).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

private theorem length_mul_le_size_sum (xs : List IntervalBlock) (S : ℕ)
    (hS : ∀ X ∈ xs, S ≤ X.size) :
    xs.length * S ≤ (xs.map IntervalBlock.size).sum := by
  induction xs with
  | nil => simp
  | cons X rest ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have hX := hS X List.mem_cons_self
    have hrest := ih (fun Y hY => hS Y (List.mem_cons_of_mem X hY))
    calc (rest.length + 1) * S = S + rest.length * S := by ring
      _ ≤ X.size + (rest.map IntervalBlock.size).sum := Nat.add_le_add hX hrest

private theorem validScaleTree_level_size_props (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) :
    ∀ ℓ : ℕ, ℓ ≤ M →
      (∀ X ∈ scaleTreePartitionLevel T P ℓ, 1 ≤ X.lo ∧ scaleS T P ℓ ≤ X.size) ∧
      ((scaleTreePartitionLevel T P ℓ).map IntervalBlock.size).sum = P := by
  rcases hValid with ⟨hP, _, hHalf⟩
  intro ℓ
  induction ℓ with
  | zero =>
    intro _
    have hPne : P ≠ 0 := by omega
    simp only [scaleTreePartitionLevel, hPne, ↓reduceIte]
    constructor
    · intro X hX
      simp only [List.mem_singleton] at hX
      subst hX
      exact ⟨le_rfl, by simp [scaleS, IntervalBlock.size, hP]⟩
    · simp [IntervalBlock.size, hP]
  | succ ℓ ih =>
    intro hℓM
    obtain ⟨hPrevBlocks, hPrevSum⟩ := ih (by omega)
    have hSpos : 1 ≤ scaleS T P (ℓ + 1) := scaleS_pos T P hP (ℓ + 1)
    simp only [scaleTreePartitionLevel]
    constructor
    · intro Y hY
      obtain ⟨X, hX, hYsub⟩ := List.mem_flatMap.mp hY
      obtain ⟨hXlo, hXsz⟩ := hPrevBlocks X hX
      have h2S : 2 * scaleS T P (ℓ + 1) ≤ X.size := le_trans (hHalf ⟨ℓ, hℓM⟩) hXsz
      exact (splitIntervalBySize_props X (scaleS T P (ℓ + 1)) hXlo hSpos h2S).1 Y hYsub
    · rw [flatMap_size_sum]
      have hcongr :
          (scaleTreePartitionLevel T P ℓ).map
            (fun X => ((splitIntervalBySize X (scaleS T P (ℓ + 1))).map IntervalBlock.size).sum) =
          (scaleTreePartitionLevel T P ℓ).map IntervalBlock.size := by
        apply List.map_congr_left
        intro X hX
        obtain ⟨hXlo, hXsz⟩ := hPrevBlocks X hX
        have h2S : 2 * scaleS T P (ℓ + 1) ≤ X.size := le_trans (hHalf ⟨ℓ, hℓM⟩) hXsz
        exact (splitIntervalBySize_props X (scaleS T P (ℓ + 1)) hXlo hSpos h2S).2
      rw [hcongr, hPrevSum]

/-- **Lemma 5.1** (`lem:tree-weights`, Height-Independent Weight Convergence):
For every `ValidScaleTree P r M T`, `∑_{ℓ=1}^M 1 / w_ℓ < 1 / 2`,
`∑_{ν ∈ 𝒯_int} 1 / w(ν) < 2`, and `Σ_𝒯 < P / 50`. -/
theorem lem_5_1_tree_weights (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) :
    let chain := scaleTreePartitionChain T P M
    (∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T ℓ : ℝ)) < (1 : ℝ) / 2 ∧
    (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) < 2 ∧
    (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50 := by
  dsimp only
  have hP : 1 ≤ P := hValid.1
  obtain ⟨_, hM1, hAllNe, hLeaves, hDepth⟩ := hValid.2.1
  -- Claim 1: Leaf weight sum `< 1 / 2`
  have hClaim1 : (∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T ℓ : ℝ)) < (1 : ℝ) / 2 := by
    have hnd : (T.leafEntries.map Prod.fst).Nodup := by
      change T.leaves.Nodup
      rw [hLeaves]
      exact List.nodup_range'
    rw [sum_Icc_one_eq_range'_sum, ← hLeaves]
    unfold ScaleTree.leaves
    rw [List.map_map]
    have hcongr :
        T.leafEntries.map ((fun ℓ : ℕ => (1 : ℝ) / (leafWeight T ℓ : ℝ)) ∘ Prod.fst) =
          T.leafEntries.map (fun e => (1 : ℝ) / (pathWeight e.2 : ℝ)) := by
      apply List.map_congr_left
      rintro ⟨s, addr⟩ hmem
      simp only [Function.comp_apply, leafWeight, leafAddr,
        find_fst_of_nodup T.leafEntries hnd hmem]
    rw [hcongr]
    cases hT : T with
    | leaf s =>
      exfalso
      have hmem1 : 1 ∈ T.leaves := by
        rw [hLeaves]
        exact List.mem_range'.mpr ⟨0, hM1, rfl⟩
      rw [hT] at hmem1 hDepth
      have hd := hDepth (s, []) (by simp [ScaleTree.leafEntries])
      simp at hd
    | internal cs =>
      simp only [ScaleTree.leafEntries]
      exact lt_of_le_of_lt (leafEntriesChildren_weight_sum_le 1 cs) (invSqSum_one_lt_half cs.length)
  -- Claim 2: Internal-node weight sum `< 2`
  have hClaim2 : (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) < 2 := by
    unfold internalAddrs
    exact lt_of_le_of_lt
      (sum_toFinset_le_list_sum T.internalAddrList _ (fun _ _ => by positivity))
      (internalAddrList_weight_sum_lt_two T)
  -- Claim 3: `sigmaScaleTree T (scaleTreePartitionChain T P M) < P / 50`
  have hClaim3 : (sigmaScaleTree T (scaleTreePartitionChain T P M) : ℝ) < (P : ℝ) / 50 := by
    unfold sigmaScaleTree
    rw [Nat.cast_sum]
    have hTerm : ∀ ν ∈ internalAddrs T,
        ((let m := mEnd T ν
          if h : m ≤ M then
            numChildren T ν * (scaleTreePartitionChain T P M ⟨m, Nat.lt_succ_of_le h⟩).length
          else 0 : ℕ) : ℝ) ≤
        ((P : ℝ) / 100) * ((1 : ℝ) / (pathWeight ν : ℝ)) := by
      intro ν hν
      have hν_list : ν ∈ T.internalAddrList := List.mem_toFinset.mp hν
      obtain ⟨hν_coords, cs, hcs_ne, hcs_all, hsub⟩ :=
        internalAddrList_spec T hAllNe ν hν_list
      rw [ScaleTree.AllInternalNonempty] at hcs_all
      obtain ⟨_, hcs_children⟩ := hcs_all
      have hwν_pos : 1 ≤ pathWeight ν := pathWeight_pos ν hν_coords
      set k := cs.length
      have hk1 : 1 ≤ k := List.length_pos_of_ne_nil hcs_ne
      have hk_eq : numChildren T ν = k := by simp [numChildren, hsub, k]
      obtain ⟨ℓStar, rTail, hlast⟩ := leafEntriesChildren_getLast? 1 cs hcs_ne hcs_children
      have hk_sub : 1 + cs.length - 1 = k := by omega
      rw [hk_sub] at hlast
      have hmEnd_eq : mEnd T ν = ℓStar := by
        simp [mEnd, hsub, ScaleTree.leaves, ScaleTree.leafEntries, List.getLast?_map, hlast]
      have hmem_sub : (ℓStar, k :: rTail) ∈ (ScaleTree.internal cs).leafEntries :=
        getLast?_mem hlast
      have hmem_T : (ℓStar, ν ++ (k :: rTail)) ∈ T.leafEntries :=
        subtreeAtAddr_leafEntries T ν (.internal cs) hsub hmem_sub
      have hmem_leaves : ℓStar ∈ List.range' 1 M := by
        rw [← hLeaves]
        exact List.mem_map.mpr ⟨(ℓStar, ν ++ (k :: rTail)), hmem_T, rfl⟩
      obtain ⟨idx, hidxM, hℓ_eq⟩ := List.mem_range'.mp hmem_leaves
      have hℓ1 : 1 ≤ ℓStar := by omega
      have hℓM : ℓStar ≤ M := by omega
      have hnd : (T.leafEntries.map Prod.fst).Nodup := by
        change T.leaves.Nodup; rw [hLeaves]; exact List.nodup_range'
      have hleafAddr : leafAddr T ℓStar = ν ++ (k :: rTail) := by
        unfold leafAddr
        rw [find_fst_of_nodup T.leafEntries hnd hmem_T]
      have hr_pos : 1 ≤ pathWeight rTail := by
        have hcoords := leafEntries_coords_pos T (ℓStar, ν ++ (k :: rTail)) hmem_T
        exact pathWeight_pos rTail (fun x hx =>
          hcoords x (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem k hx))))
      have hw_bound : 4 * k ^ 2 * pathWeight ν ≤ leafWeight T ℓStar := by
        unfold leafWeight
        rw [hleafAddr, pathWeight_append, pathWeight_cons]
        calc 4 * k ^ 2 * pathWeight ν
            = pathWeight ν * (4 * k ^ 2 * 1) := by ring
          _ ≤ pathWeight ν * (4 * k ^ 2 * pathWeight rTail) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hr_pos)
      have hS_bound : 100 * k ^ 2 * pathWeight ν ≤ scaleS T P ℓStar := by
        have h25 := validScaleTree_scaleS_ge_25_weight P r M T hValid hℓ1 hℓM
        calc 100 * k ^ 2 * pathWeight ν
            = 25 * (4 * k ^ 2 * pathWeight ν) := by ring
          _ ≤ 25 * leafWeight T ℓStar := Nat.mul_le_mul_left 25 hw_bound
          _ ≤ scaleS T P ℓStar := h25
      obtain ⟨hLvlBlocks, hLvlSum⟩ := validScaleTree_level_size_props P r M T hValid ℓStar hℓM
      set L := (scaleTreePartitionLevel T P ℓStar).length
      have hLS_le_P : L * scaleS T P ℓStar ≤ P :=
        le_trans (length_mul_le_size_sum _ _ (fun X hX => (hLvlBlocks X hX).2)) (le_of_eq hLvlSum)
      have hNatBound : 100 * pathWeight ν * (k * L) ≤ P := by
        have hk_le_sq : k ≤ k ^ 2 := by
          calc k = k * 1 := (Nat.mul_one k).symm
            _ ≤ k * k := Nat.mul_le_mul_left k hk1
            _ = k ^ 2 := (sq k).symm
        have h1 : 100 * pathWeight ν * (k * L) ≤ L * (100 * k ^ 2 * pathWeight ν) := by
          calc 100 * pathWeight ν * (k * L)
              = L * (100 * pathWeight ν * k) := by ring
            _ ≤ L * (100 * pathWeight ν * k ^ 2) :=
                Nat.mul_le_mul_left L (Nat.mul_le_mul_left _ hk_le_sq)
            _ = L * (100 * k ^ 2 * pathWeight ν) := by ring
        exact le_trans h1 (le_trans (Nat.mul_le_mul_left L hS_bound) hLS_le_P)
      dsimp only
      simp only [hmEnd_eq, hℓM, ↓reduceDIte, hk_eq, scaleTreePartitionChain]
      change ((k * L : ℕ) : ℝ) ≤ ((P : ℝ) / 100) * ((1 : ℝ) / (pathWeight ν : ℝ))
      have hRealBound : (100 : ℝ) * (pathWeight ν : ℝ) * ((k * L : ℕ) : ℝ) ≤ (P : ℝ) := by
        exact_mod_cast hNatBound
      have hwR_pos : (0 : ℝ) < (pathWeight ν : ℝ) := by exact_mod_cast hwν_pos
      rw [div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
      linarith
    have hSumLe :
        (∑ ν ∈ internalAddrs T,
          ((let m := mEnd T ν
            if h : m ≤ M then
              numChildren T ν * (scaleTreePartitionChain T P M ⟨m, Nat.lt_succ_of_le h⟩).length
            else 0 : ℕ) : ℝ)) ≤
        ((P : ℝ) / 100) * (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) := by
      calc _ ≤ ∑ ν ∈ internalAddrs T, ((P : ℝ) / 100) * ((1 : ℝ) / (pathWeight ν : ℝ)) :=
            Finset.sum_le_sum hTerm
        _ = ((P : ℝ) / 100) * (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) := by
            rw [← Finset.mul_sum]
    have hPR_pos : (0 : ℝ) < (P : ℝ) / 100 := by
      have : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
      linarith
    have hStrict :
        ((P : ℝ) / 100) * (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) <
          ((P : ℝ) / 100) * 2 :=
      mul_lt_mul_of_pos_left hClaim2 hPR_pos
    linarith
  exact ⟨hClaim1, hClaim2, hClaim3⟩


/-!
================================================================================
Section 3: Self-Contained Ordering Invariant for `FoldedPopProcess.rInt`
================================================================================
-/

private theorem isBSTAux_of_bounds {t : BinaryTree ℕ} (h : t.IsBST) (lb ub : Option ℕ)
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

private theorem isBST_node_iff (k : ℕ) (l r : BinaryTree ℕ) :
    (BinaryTree.node k l r).IsBST ↔
      (∀ x ∈ l, x < k) ∧ (∀ x ∈ r, k < x) ∧ l.IsBST ∧ r.IsBST := by
  constructor
  · intro h
    exact ⟨fun _ hx => BinaryTree.lt_of_IsBST_left l k r h hx,
      fun _ hx => BinaryTree.gt_of_IsBST_right l k r h hx,
      BinaryTree.IsBST_left_of_IsBST h,
      BinaryTree.IsBST_right_of_IsBST h⟩
  · rintro ⟨hlt, hgt, hl, hr⟩
    exact BinaryTree.IsBSTAux.node trivial trivial
      (isBSTAux_of_bounds hl none (some k) (by simp) hlt)
      (isBSTAux_of_bounds hr (some k) none hgt (by simp))

private theorem mem_of_mem_leftSpine : ∀ {t : BinaryTree ℕ} {v : ℕ}, v ∈ leftSpine t → v ∈ t
  | .nil, _, hv => by simp [leftSpine] at hv
  | .node k l _, v, hv => by
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hv
    rcases hv with hvl | rfl
    · exact .left (mem_of_mem_leftSpine hvl)
    · exact .here

private theorem leftSpine_pairwise_lt :
    ∀ {t : BinaryTree ℕ}, t.IsBST → (leftSpine t).Pairwise (· < ·)
  | .nil, _ => by simp [leftSpine]
  | .node k l r, hbst => by
    obtain ⟨hlt, _, hl, _⟩ := (isBST_node_iff k l r).mp hbst
    simp only [leftSpine, List.pairwise_append, List.pairwise_singleton, true_and]
    exact ⟨leftSpine_pairwise_lt hl, fun u hu v hv => by
      simp only [List.mem_singleton] at hv
      subst hv
      exact hlt u (mem_of_mem_leftSpine hu)⟩

private theorem leftSpine_head?_eq_minKey? :
    ∀ (t : BinaryTree ℕ), (leftSpine t).head? = t.minKey?
  | .nil => rfl
  | .node k l r => by
    simp only [leftSpine, BinaryTree.minKey?]
    have ih := leftSpine_head?_eq_minKey? l
    cases hm : l.minKey? with
    | none =>
      rw [hm] at ih
      have hnil : leftSpine l = [] := List.head?_eq_none_iff.mp ih
      simp [hnil]
    | some m =>
      rw [hm] at ih
      cases hls : leftSpine l with
      | nil => rw [hls] at ih; simp at ih
      | cons a rest =>
        rw [hls] at ih
        simp only [List.head?_cons, Option.some.injEq] at ih
        subst ih
        rfl

private theorem modifyLeftAt_push_bst :
    ∀ (t : BinaryTree ℕ) (b w : ℕ),
      t.IsBST → b ∈ leftSpine t → (∀ x ∈ t, w < x) →
      let t' := modifyLeftAt t b (fun L1 => .node w .nil L1)
      t'.IsBST ∧ ∀ v ∈ t', v = w ∨ v ∈ t
  | .nil, _, _, _, hb, _ => by simp [leftSpine] at hb
  | .node k l r, b, w, hbst, hb, hw => by
    obtain ⟨hlt, hgt, hl, hr⟩ := (isBST_node_iff k l r).mp hbst
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hb
    rcases hb with hbl | rfl
    · have hbk : b < k := hlt b (mem_of_mem_leftSpine hbl)
      simp only [modifyLeftAt, hbk, ↓reduceIte]
      obtain ⟨hl'_bst, hl'_mem⟩ :=
        modifyLeftAt_push_bst l b w hl hbl (fun x hx => hw x (.left hx))
      refine ⟨(isBST_node_iff k _ r).mpr ⟨?_, hgt, hl'_bst, hr⟩, ?_⟩
      · intro x hx
        rcases hl'_mem x hx with rfl | hxl
        · exact hw k .here
        · exact hlt x hxl
      · intro v hv
        rcases BinaryTree.mem_node_iff.mp hv with rfl | hvl | hvr
        · exact Or.inr .here
        · rcases hl'_mem v hvl with rfl | hvl0
          · exact Or.inl rfl
          · exact Or.inr (.left hvl0)
        · exact Or.inr (.right hvr)
    · have hlt_irrefl : ¬ (b < b) := lt_irrefl b
      simp only [modifyLeftAt, hlt_irrefl, ↓reduceIte]
      have hwnode : (BinaryTree.node w .nil l).IsBST :=
        (isBST_node_iff w .nil l).mpr ⟨by simp, fun x hx => hw x (.left hx), .nil none none, hl⟩
      refine ⟨(isBST_node_iff b (.node w .nil l) r).mpr ⟨?_, hgt, hwnode, hr⟩, ?_⟩
      · intro x hx
        rcases BinaryTree.mem_node_iff.mp hx with rfl | hnil | hxl
        · exact hw b .here
        · cases hnil
        · exact hlt x hxl
      · intro v hv
        rcases BinaryTree.mem_node_iff.mp hv with rfl | hvl | hvr
        · exact Or.inr .here
        · rcases BinaryTree.mem_node_iff.mp hvl with rfl | hnil | hvl0
          · exact Or.inl rfl
          · cases hnil
          · exact Or.inr (.left hvl0)
        · exact Or.inr (.right hvr)

private theorem rotateRightEdge_bst :
    ∀ (t : BinaryTree ℕ) (x p : ℕ),
      t.IsBST → (rotateRightEdge t x p).IsBST ∧ ∀ v ∈ rotateRightEdge t x p, v ∈ t
  | .nil, _, _, hbst => ⟨hbst, fun _ hv => hv⟩
  | .node k l r, x, p, hbst => by
    obtain ⟨hlt, hgt, hl, hr⟩ := (isBST_node_iff k l r).mp hbst
    simp only [rotateRightEdge]
    split_ifs with hpk hkp
    · obtain ⟨hl', hmem'⟩ := rotateRightEdge_bst l x p hl
      refine ⟨(isBST_node_iff k _ r).mpr ⟨fun u hu => hlt u (hmem' u hu), hgt, hl', hr⟩, ?_⟩
      intro v hv
      rcases BinaryTree.mem_node_iff.mp hv with rfl | hvl | hvr
      · exact .here
      · exact .left (hmem' v hvl)
      · exact .right hvr
    · obtain ⟨hr', hmem'⟩ := rotateRightEdge_bst r x p hr
      refine ⟨(isBST_node_iff k l _).mpr ⟨hlt, fun u hu => hgt u (hmem' u hu), hl, hr'⟩, ?_⟩
      intro v hv
      rcases BinaryTree.mem_node_iff.mp hv with rfl | hvl | hvr
      · exact .here
      · exact .left hvl
      · exact .right (hmem' v hvr)
    · cases l with
      | nil => exact ⟨hbst, fun _ hv => hv⟩
      | node lx a b =>
        dsimp only
        split_ifs with hlx
        · obtain ⟨ha_lt, hb_gt, ha, hb⟩ := (isBST_node_iff lx a b).mp hl
          have hlx_lt_k : lx < k := hlt lx .here
          have hbk_bst : (BinaryTree.node k b r).IsBST :=
            (isBST_node_iff k b r).mpr ⟨fun u hu => hlt u (.right hu), hgt, hb, hr⟩
          refine ⟨(isBST_node_iff lx a (.node k b r)).mpr ⟨ha_lt, ?_, ha, hbk_bst⟩, ?_⟩
          · intro u hu
            rcases BinaryTree.mem_node_iff.mp hu with rfl | hub | hur
            · exact hlx_lt_k
            · exact hb_gt u hub
            · exact lt_trans hlx_lt_k (hgt u hur)
          · intro v hv
            rcases BinaryTree.mem_node_iff.mp hv with rfl | hva | hvkr
            · exact .left .here
            · exact .left (.left hva)
            · rcases BinaryTree.mem_node_iff.mp hvkr with rfl | hvb | hvr
              · exact .here
              · exact .left (.right hvb)
              · exact .right hvr
        · exact ⟨hbst, fun _ hv => hv⟩

private theorem spliceMin_bst :
    ∀ (t : BinaryTree ℕ), t.IsBST → (spliceMin t).IsBST ∧ ∀ v ∈ spliceMin t, v ∈ t
  | .nil, hbst => ⟨hbst, fun _ hv => hv⟩
  | .node k .nil r, hbst => by
    obtain ⟨_, _, _, hr⟩ := (isBST_node_iff k .nil r).mp hbst
    exact ⟨hr, fun _ hv => .right hv⟩
  | .node k (.node lk ll lr) r, hbst => by
    obtain ⟨hlt, hgt, hl, hr⟩ := (isBST_node_iff k (.node lk ll lr) r).mp hbst
    obtain ⟨hl', hmem'⟩ := spliceMin_bst (.node lk ll lr) hl
    change (BinaryTree.node k (spliceMin (.node lk ll lr)) r).IsBST ∧ _
    refine ⟨(isBST_node_iff k _ r).mpr ⟨fun u hu => hlt u (hmem' u hu), hgt, hl', hr⟩, ?_⟩
    intro v hv
    rcases BinaryTree.mem_node_iff.mp hv with rfl | hvl | hvr
    · exact .here
    · exact .left (hmem' v hvl)
    · exact .right hvr

private theorem foldl_rotateRightEdge_bst (pairs : List (ℕ × ℕ)) (t : BinaryTree ℕ)
    (ht : t.IsBST) :
    let t' := pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t
    t'.IsBST ∧ ∀ v ∈ t', v ∈ t := by
  induction pairs generalizing t with
  | nil => exact ⟨ht, fun _ hv => hv⟩
  | cons p rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨ht1, hm1⟩ := rotateRightEdge_bst t p.1 p.2 ht
    obtain ⟨ht2, hm2⟩ := ih (rotateRightEdge t p.1 p.2) ht1
    exact ⟨ht2, fun v hv => hm1 v (hm2 v hv)⟩

private theorem foldedOp_step_preserves_bst_range (P : ℕ) (st : BinaryTree ℕ × Option ℕ)
    (op : FoldedOp) (hValid : op.Valid P st)
    (hbst : st.1.IsBST) (hrange : ∀ v ∈ st.1, 1 ≤ v ∧ v ≤ P) :
    (op.step st).1.IsBST ∧ ∀ v ∈ (op.step st).1, 1 ≤ v ∧ v ≤ P := by
  cases op with
  | push w =>
    obtain ⟨hw1, hwP, hwlt, _, hb_mem⟩ := hValid
    simp only [FoldedOp.step]
    cases hb : st.2 with
    | none =>
      refine ⟨(isBST_node_iff w .nil .nil).mpr ⟨by simp, by simp, .nil none none, .nil none none⟩,
        ?_⟩
      intro v hv
      rcases BinaryTree.mem_node_iff.mp hv with rfl | hnil | hnil
      · exact ⟨hw1, hwP⟩
      · cases hnil
      · cases hnil
    | some b =>
      obtain ⟨ht', hmem'⟩ := modifyLeftAt_push_bst st.1 b w hbst (hb_mem b hb) hwlt
      refine ⟨ht', fun v hv => ?_⟩
      rcases hmem' v hv with rfl | hv0
      · exact ⟨hw1, hwP⟩
      · exact hrange v hv0
  | shift =>
    simp only [FoldedOp.step]
    cases st.2 <;> exact ⟨hbst, hrange⟩
  | upperRot u v =>
    simp only [FoldedOp.step]
    obtain ⟨ht', hmem'⟩ := rotateRightEdge_bst st.1 u v hbst
    exact ⟨ht', fun x hx => hrange x (hmem' x hx)⟩
  | pop s =>
    simp only [FoldedOp.step]
    cases st.2 with
    | none => exact ⟨hbst, hrange⟩
    | some b =>
      dsimp only
      obtain ⟨ht0, hm0⟩ := spliceMin_bst st.1 hbst
      by_cases hk0 : (takeThrough (leftSpine st.1) b).length - 1 = 0
      · simp only [hk0, ↓reduceIte]
        exact ⟨ht0, fun x hx => hrange x (hm0 x hx)⟩
      · simp only [hk0, ↓reduceIte]
        obtain ⟨htN, hmN⟩ := foldl_rotateRightEdge_bst _ _ ht0
        exact ⟨htN, fun x hx => hrange x (hm0 x (hmN x hx))⟩

private theorem takeThrough_isPrefix {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (b : α), takeThrough xs b <+: xs
  | [], _ => List.nil_prefix
  | x :: xs, b => by
    simp only [takeThrough]
    split_ifs with hxb
    · exact ⟨xs, rfl⟩
    · obtain ⟨t, ht⟩ := takeThrough_isPrefix xs b
      exact ⟨t, by simp [ht]⟩

private theorem foldedPopRotsAt_ord (P idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (op : FoldedOp)
    (hValid : op.Valid P st) (hbst : st.1.IsBST) (hrange : ∀ v ∈ st.1, 1 ≤ v ∧ v ≤ P) :
    ∀ e ∈ foldedPopRotsAt idx st op,
      1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P := by
  cases op with
  | push _ => simp [foldedPopRotsAt]
  | shift => simp [foldedPopRotsAt]
  | upperRot _ _ => simp [foldedPopRotsAt]
  | pop s =>
    obtain ⟨b, _, hmin, hb_eq, _⟩ := hValid
    simp only [foldedPopRotsAt, hb_eq, List.mem_filterMap, List.mem_range]
    rintro e ⟨idx', _, hmatch⟩
    set j := idx' + 1
    set sub := takeThrough (leftSpine st.1) b
    cases hx : sub[2 * j - 1]? with
    | none => rw [hx] at hmatch; simp at hmatch
    | some x =>
      cases hy : sub[2 * j]? with
      | none => rw [hx, hy] at hmatch; simp at hmatch
      | some y =>
        cases hz : sub[2 * j + 1]? with
        | none => rw [hx, hy, hz] at hmatch; simp at hmatch
        | some z =>
          rw [hx, hy, hz] at hmatch
          simp only [Option.some.injEq] at hmatch
          subst hmatch
          obtain ⟨tail, happend⟩ := takeThrough_isPrefix (leftSpine st.1) b
          have hls_pw : (leftSpine st.1).Pairwise (· < ·) := leftSpine_pairwise_lt hbst
          rw [← happend, List.pairwise_append] at hls_pw
          have hsub_pw : sub.Pairwise (· < ·) := hls_pw.1
          have hls_head : (leftSpine st.1).head? = some s := by
            rw [leftSpine_head?_eq_minKey?]; exact hmin
          have hsub0 : sub[0]? = some s := by
            cases hls_eq : leftSpine st.1 with
            | nil => rw [hls_eq] at hls_head; simp at hls_head
            | cons a rest =>
              rw [hls_eq] at hls_head
              simp only [List.head?_cons, Option.some.injEq] at hls_head
              subst hls_head
              dsimp only [sub]
              rw [hls_eq]
              simp only [takeThrough]
              split_ifs <;> rfl
          obtain ⟨h0_lt, hs_get⟩ := List.getElem?_eq_some_iff.mp hsub0
          obtain ⟨hx_lt, hx_get⟩ := List.getElem?_eq_some_iff.mp hx
          obtain ⟨hy_lt, hy_get⟩ := List.getElem?_eq_some_iff.mp hy
          obtain ⟨hz_lt, hz_get⟩ := List.getElem?_eq_some_iff.mp hz
          have hpw_idx := List.pairwise_iff_getElem.mp hsub_pw
          have hs_mem_sub : s ∈ sub := hs_get ▸ List.getElem_mem h0_lt
          have hz_mem_sub : z ∈ sub := hz_get ▸ List.getElem_mem hz_lt
          have hs_mem_t : s ∈ st.1 := mem_of_mem_leftSpine
            (happend ▸ List.mem_append_left tail hs_mem_sub)
          have hz_mem_t : z ∈ st.1 := mem_of_mem_leftSpine
            (happend ▸ List.mem_append_left tail hz_mem_sub)
          refine ⟨(hrange s hs_mem_t).1, ?_, ?_, ?_, (hrange z hz_mem_t).2⟩
          · rw [← hs_get, ← hx_get]
            exact hpw_idx 0 (2 * j - 1) h0_lt hx_lt (by omega)
          · rw [← hx_get, ← hy_get]
            exact hpw_idx (2 * j - 1) (2 * j) hx_lt hy_lt (by omega)
          · rw [← hy_get, ← hz_get]
            exact hpw_idx (2 * j) (2 * j + 1) hy_lt hz_lt (by omega)

private theorem collectFoldedPopRots_ord (P : ℕ) :
    ∀ (steps : List FoldedOp) (idx : ℕ) (st : BinaryTree ℕ × Option ℕ),
      ValidFoldedOps P st steps →
      st.1.IsBST → (∀ v ∈ st.1, 1 ≤ v ∧ v ≤ P) →
      ∀ e ∈ collectFoldedPopRots idx st steps,
        1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P
  | [], _, _, _, _, _, _, he => by simp [collectFoldedPopRots] at he
  | op :: rest, idx, st, ⟨hv, hrest⟩, hbst, hrange, e, he => by
    simp only [collectFoldedPopRots, List.mem_append] at he
    rcases he with hnow | hlater
    · exact foldedPopRotsAt_ord P idx st op hv hbst hrange e hnow
    · obtain ⟨hbst', hrange'⟩ := foldedOp_step_preserves_bst_range P st op hv hbst hrange
      exact collectFoldedPopRots_ord P rest (idx + 1) (op.step st) hrest hbst' hrange' e hlater

private theorem rInt_ord {P : ℕ} (proc : FoldedPopProcess P) :
    ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P := by
  intro e he
  exact collectFoldedPopRots_ord P proc.steps 0 (.nil, none) proc.hValid
    (.nil none none) (by simp) e (List.mem_toFinset.mp he)


/-!
================================================================================
Section 4: Dyadic Partition Properties and Proposition 7.1
================================================================================
-/

private theorem consecutiveBlocks_append :
    ∀ (xs ys : List IntervalBlock),
      ConsecutiveBlocks xs → ConsecutiveBlocks ys →
      (∀ l h, xs.getLast? = some l → ys.head? = some h → l.hi + 1 = h.lo) →
      ConsecutiveBlocks (xs ++ ys)
  | [], _, _, hys, _ => hys
  | [_], [], _, _, _ => trivial
  | [a], b :: _, _, hys, hbridge => ⟨hbridge a b rfl rfl, hys⟩
  | _ :: a₂ :: rest, ys, ⟨h12, hxs⟩, hys, hbridge =>
    ⟨h12, consecutiveBlocks_append (a₂ :: rest) ys hxs hys hbridge⟩

private theorem dyadicSplitBlock_props (X : IntervalBlock) (hXlo : 1 ≤ X.lo) (hXle : X.lo ≤ X.hi) :
    let sub := dyadicSplitBlock X
    sub ≠ [] ∧
    (∀ Y ∈ sub, X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi) ∧
    ConsecutiveBlocks sub ∧
    (∀ first, sub.head? = some first → first.lo = X.lo) ∧
    (∀ last, sub.getLast? = some last → last.hi = X.hi) ∧
    (sub.map IntervalBlock.size).foldr max 0 = (X.size + 1) / 2 := by
  have hsz : X.size = X.hi - X.lo + 1 := by simp [IntervalBlock.size, hXle]
  have hsz1 : 1 ≤ X.size := by omega
  dsimp only
  unfold dyadicSplitBlock
  dsimp only
  by_cases h1 : X.size ≤ 1
  · simp only [h1, ↓reduceIte]
    have hsz_eq : X.size = 1 := by omega
    refine ⟨by simp, ?_, trivial, ?_, ?_, ?_⟩
    · intro Y hY
      simp only [List.mem_singleton] at hY
      subst hY
      exact ⟨le_rfl, hXle, le_rfl⟩
    · intro first hf; simp at hf; subst hf; rfl
    · intro last hl; simp at hl; subst hl; rfl
    · simp [hsz_eq]
  · simp only [h1, ↓reduceIte]
    set half := X.size / 2
    have hhalf_def : half = X.size / 2 := rfl
    have hhalf1 : 1 ≤ half := by omega
    have h2half : 2 * half ≤ X.size := Nat.mul_div_le X.size 2
    have hlo1 : X.lo ≤ X.lo + half - 1 := by omega
    have hlo2 : X.lo + half ≤ X.hi := by omega
    refine ⟨by simp, ?_, ⟨by dsimp only; omega, trivial⟩, ?_, ?_, ?_⟩
    · intro Y hY
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
      rcases hY with rfl | rfl
      · dsimp only; exact ⟨le_rfl, hlo1, by omega⟩
      · dsimp only; exact ⟨by omega, hlo2, le_rfl⟩
    · intro first hf; simp at hf; subst hf; rfl
    · intro last hl; simp at hl; subst hl; rfl
    · simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
        IntervalBlock.size, hlo1, hlo2, hXle, ↓reduceIte]
      have hs1 : X.lo + half - 1 - X.lo + 1 = half := by omega
      have hs2 : X.hi - (X.lo + half) + 1 = X.size - half := by omega
      rw [hs1, hs2, max_eq_left (Nat.zero_le _)]
      have hle_rem : half ≤ X.size - half := by omega
      rw [max_eq_right hle_rem]
      omega

private theorem flatMap_dyadicSplitBlock_preserves_partition (P : ℕ) (hP : 1 ≤ P) :
    ∀ (blocks : List IntervalBlock),
      IsContiguousBlockPartition P blocks →
      IsContiguousBlockPartition P (blocks.flatMap dyadicSplitBlock) := by
  suffices ∀ (blocks : List IntervalBlock) (a b : ℕ),
      1 ≤ a → blocks ≠ [] →
      (∀ C ∈ blocks, a ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ b) →
      ConsecutiveBlocks blocks →
      (∀ first, blocks.head? = some first → first.lo = a) →
      (∀ last, blocks.getLast? = some last → last.hi = b) →
      let res := blocks.flatMap dyadicSplitBlock
      res ≠ [] ∧
      (∀ Y ∈ res, a ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ b) ∧
      ConsecutiveBlocks res ∧
      (∀ first, res.head? = some first → first.lo = a) ∧
      (∀ last, res.getLast? = some last → last.hi = b) by
    intro blocks ⟨hbnds, hcons, hhl⟩
    cases hhead : blocks.head? with
    | none =>
      rw [hhead] at hhl
      omega
    | some first =>
      cases hlast : blocks.getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp hlast
        rw [hnil] at hhead; simp at hhead
      | some last =>
        rw [hhead, hlast] at hhl
        obtain ⟨hflo, hlhi⟩ := hhl
        have hne : blocks ≠ [] := by intro h; rw [h] at hhead; simp at hhead
        have hbnds' : ∀ C ∈ blocks, 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ P := hbnds
        obtain ⟨hres_ne, hres_bnds, hres_cons, hres_hd, hres_lt⟩ :=
          this blocks 1 P le_rfl hne hbnds' hcons
            (fun f hf => by rw [hhead] at hf; injection hf with hf'; subst hf'; exact hflo)
            (fun l hl => by rw [hlast] at hl; injection hl with hl'; subst hl'; exact hlhi)
        refine ⟨hres_bnds, hres_cons, ?_⟩
        cases hh : (blocks.flatMap dyadicSplitBlock).head? with
        | none => exact absurd (List.head?_eq_none_iff.mp hh) hres_ne
        | some f' =>
          cases hl : (blocks.flatMap dyadicSplitBlock).getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.mp hl) hres_ne
          | some l' => exact ⟨hres_hd f' hh, hres_lt l' hl⟩
  intro blocks
  induction blocks with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons C rest ih =>
    intro a b ha _ hbnds hcons hhd hlt
    have hC := hbnds C List.mem_cons_self
    obtain ⟨hsub_ne, hsub_bnds, hsub_cons, hsub_hd, hsub_lt, _⟩ :=
      dyadicSplitBlock_props C (le_trans ha hC.1) hC.2.1
    have hCa : C.lo = a := hhd C rfl
    cases rest with
    | nil =>
      have hCb : C.hi = b := hlt C rfl
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine ⟨hsub_ne, ?_, hsub_cons, ?_, ?_⟩
      · intro Y hY
        obtain ⟨h1, h2, h3⟩ := hsub_bnds Y hY
        exact ⟨hCa ▸ h1, h2, hCb ▸ h3⟩
      · intro f hf; rw [hsub_hd f hf, hCa]
      · intro l hl; rw [hsub_lt l hl, hCb]
    | cons C₂ rest' =>
      obtain ⟨hC_C2, hcons_rest⟩ := hcons
      have ha2 : 1 ≤ C₂.lo := by omega
      have hbnds_rest : ∀ D ∈ C₂ :: rest', C₂.lo ≤ D.lo ∧ D.lo ≤ D.hi ∧ D.hi ≤ b := by
        intro D hD
        rcases List.mem_cons.mp hD with rfl | hDr
        · have hD0 := hbnds D (List.mem_cons_of_mem C hD)
          exact ⟨le_rfl, hD0.2.1, hD0.2.2⟩
        ·-- Prove `C₂.lo ≤ D.lo` from `ConsecutiveBlocks`!
          have hmono : ∀ (xs : List IntervalBlock),
              ConsecutiveBlocks xs → (∀ E ∈ xs, E.lo ≤ E.hi) →
              ∀ x, xs.head? = some x → ∀ E ∈ xs, x.lo ≤ E.lo := by
            intro xs
            induction xs with
            | nil => intro _ _ _ hx; simp at hx
            | cons x0 xs' ihx =>
              intro hcx hex x hx E hE
              simp only [List.head?_cons, Option.some.injEq] at hx
              subst hx
              rcases List.mem_cons.mp hE with rfl | hExs'
              · exact le_rfl
              · cases xs' with
                | nil => cases hExs'
                | cons x1 xs'' =>
                  have hx01 : x0.hi + 1 = x1.lo := hcx.1
                  have hx0le : x0.lo ≤ x0.hi := hex x0 List.mem_cons_self
                  have hx1E := ihx hcx.2 (fun F hF => hex F (List.mem_cons_of_mem x0 hF))
                    x1 rfl E hExs'
                  omega
          have hC2_le_D := hmono (C₂ :: rest') hcons_rest
            (fun E hE => (hbnds E (List.mem_cons_of_mem C hE)).2.1) C₂ rfl D hD
          have hD0 := hbnds D (List.mem_cons_of_mem C hD)
          exact ⟨hC2_le_D, hD0.2.1, hD0.2.2⟩
      obtain ⟨hrest_ne, hrest_bnds, hrest_cons, hrest_hd, hrest_lt⟩ :=
        ih C₂.lo b ha2 (by simp) hbnds_rest hcons_rest
          (fun f hf => by simp at hf; subst hf; rfl)
          (fun l hl => hlt l hl)
      rw [List.flatMap_cons]
      refine ⟨by intro h; exact hsub_ne (List.append_eq_nil_iff.mp h).1, ?_, ?_, ?_, ?_⟩
      · intro Y hY
        rcases List.mem_append.mp hY with hY1 | hY2
        · obtain ⟨h1, h2, h3⟩ := hsub_bnds Y hY1
          exact ⟨hCa ▸ h1, h2, le_trans h3 hC.2.2⟩
        · obtain ⟨h1, h2, h3⟩ := hrest_bnds Y hY2
          exact ⟨by omega, h2, h3⟩
      · apply consecutiveBlocks_append _ _ hsub_cons hrest_cons
        intro l h hl hh
        rw [hsub_lt l hl, hrest_hd h hh, hC_C2]
      · intro f hf
        cases hsub_eq : dyadicSplitBlock C with
        | nil => exact absurd hsub_eq hsub_ne
        | cons s0 ss =>
          rw [hsub_eq] at hf hsub_hd
          simp only [List.cons_append, List.head?_cons] at hf
          rw [hsub_hd f hf, hCa]
      · intro l hl
        rw [getLast?_append_right _ hrest_ne] at hl
        exact hrest_lt l hl

private theorem dyadicPartitionLevel_isPartition (P : ℕ) (hP : 1 ≤ P) :
    ∀ ℓ : ℕ, IsContiguousBlockPartition P (dyadicPartitionLevel P ℓ)
  | 0 => by
    have hPne : P ≠ 0 := by omega
    simp only [dyadicPartitionLevel, hPne, ↓reduceIte]
    refine ⟨?_, trivial, rfl, rfl⟩
    intro C hC
    simp only [List.mem_singleton] at hC
    subst hC
    exact ⟨le_rfl, hP, le_rfl⟩
  | ℓ + 1 =>
    flatMap_dyadicSplitBlock_preserves_partition P hP (dyadicPartitionLevel P ℓ)
      (dyadicPartitionLevel_isPartition P hP ℓ)

private theorem foldr_max_append :
    ∀ (xs ys : List ℕ), (xs ++ ys).foldr max 0 = max (xs.foldr max 0) (ys.foldr max 0)
  | [], ys => by simp
  | x :: xs, ys => by
    simp only [List.cons_append, List.foldr_cons, foldr_max_append xs ys, max_assoc]

private theorem foldr_max_flatMap {α : Type} (xs : List α) (f : α → List ℕ) :
    (xs.flatMap f).foldr max 0 = (xs.map (fun x => (f x).foldr max 0)).foldr max 0 := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.map_cons, List.foldr_cons, foldr_max_append, ih]

private theorem foldr_max_half_ceil :
    ∀ (ns : List ℕ), (ns.map (fun t => (t + 1) / 2)).foldr max 0 = (ns.foldr max 0 + 1) / 2
  | [] => rfl
  | x :: rest => by
    simp only [List.map_cons, List.foldr_cons, foldr_max_half_ceil rest]
    set y := rest.foldr max 0
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy, max_eq_right (by omega)]
    · rw [max_eq_left hyx, max_eq_left (by omega)]

private theorem le_foldr_max : ∀ {ns : List ℕ} {x : ℕ}, x ∈ ns → x ≤ ns.foldr max 0
  | [], _, hx => by cases hx
  | a :: rest, x, hx => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hxr
    · exact le_max_left x _
    · exact le_trans (le_foldr_max hxr) (le_max_right a _)

private theorem dyadicPartitionLevel_max_size (P : ℕ) (hP : 1 ≤ P) :
    ∀ ℓ : ℕ,
      ((dyadicPartitionLevel P ℓ).map IntervalBlock.size).foldr max 0 =
        (P + 2 ^ ℓ - 1) / 2 ^ ℓ
  | 0 => by
    have hPne : P ≠ 0 := by omega
    simp [dyadicPartitionLevel, hPne, IntervalBlock.size, hP]
  | ℓ + 1 => by
    have hPart := dyadicPartitionLevel_isPartition P hP ℓ
    simp only [dyadicPartitionLevel]
    have hmap_flat :
        ((dyadicPartitionLevel P ℓ).flatMap dyadicSplitBlock).map IntervalBlock.size =
          (dyadicPartitionLevel P ℓ).flatMap (fun X => (dyadicSplitBlock X).map IntervalBlock.size) := by
      induction (dyadicPartitionLevel P ℓ) with
      | nil => rfl
      | cons X rest ih => simp [List.flatMap_cons, List.map_append, ih]
    rw [hmap_flat, foldr_max_flatMap]
    have hcongr :
        (dyadicPartitionLevel P ℓ).map
          (fun X => ((dyadicSplitBlock X).map IntervalBlock.size).foldr max 0) =
        ((dyadicPartitionLevel P ℓ).map IntervalBlock.size).map (fun t => (t + 1) / 2) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro X hX
      obtain ⟨h1, h2, _⟩ := hPart.1 X hX
      exact (dyadicSplitBlock_props X h1 h2).2.2.2.2.2
    rw [hcongr, foldr_max_half_ceil, dyadicPartitionLevel_max_size P hP ℓ]
    set m := P - 1
    have hPm : P = m + 1 := by omega
    have hB_pos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
    have h2B_pos : 0 < 2 ^ (ℓ + 1) := Nat.two_pow_pos (ℓ + 1)
    have h1 : P + 2 ^ ℓ - 1 = m + 2 ^ ℓ := by omega
    have h2 : P + 2 ^ (ℓ + 1) - 1 = m + 2 ^ (ℓ + 1) := by omega
    rw [h1, h2, Nat.add_div_right m hB_pos, Nat.add_div_right m h2B_pos]
    have h3 : m / 2 ^ ℓ + 1 + 1 = m / 2 ^ ℓ + 2 := rfl
    rw [h3, Nat.add_div_right (m / 2 ^ ℓ) (by decide : 0 < 2), Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-! ### `blockAt` lookup and uniqueness on contiguous block partitions -/

private theorem consecutiveBlocks_pairwise_lt :
    ∀ (blocks : List IntervalBlock),
      ConsecutiveBlocks blocks → (∀ C ∈ blocks, C.lo ≤ C.hi) →
      blocks.Pairwise (fun A B => A.hi < B.lo)
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | C₁ :: C₂ :: rest, ⟨h12, hcons⟩, hle => by
    have ih := consecutiveBlocks_pairwise_lt (C₂ :: rest) hcons
      (fun C hC => hle C (List.mem_cons_of_mem C₁ hC))
    rw [List.pairwise_cons]
    refine ⟨?_, ih⟩
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hBrest
    · omega
    · have hC2_lt : C₂.hi < B.lo := (List.pairwise_cons.mp ih).1 B hBrest
      have hC2_le : C₂.lo ≤ C₂.hi := hle C₂ (List.mem_cons_of_mem C₁ List.mem_cons_self)
      omega

private theorem blockAt_mem_and_bounds {P : ℕ} {parts : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P parts) {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) :
    blockAt parts u ∈ parts ∧ (blockAt parts u).lo ≤ u ∧ u ≤ (blockAt parts u).hi := by
  obtain ⟨hbnds, hcons, hhl⟩ := hPart
  have hex : ∃ B ∈ parts, B.lo ≤ u ∧ u ≤ B.hi := by
    suffices ∀ (xs : List IntervalBlock) (a b : ℕ),
        xs ≠ [] → ConsecutiveBlocks xs →
        (∀ first, xs.head? = some first → first.lo = a) →
        (∀ last, xs.getLast? = some last → last.hi = b) →
        a ≤ u → u ≤ b → ∃ B ∈ xs, B.lo ≤ u ∧ u ≤ B.hi by
      cases hhead : parts.head? with
      | none => rw [hhead] at hhl; omega
      | some first =>
        cases hlast : parts.getLast? with
        | none =>
          have hnil := List.getLast?_eq_none_iff.mp hlast
          rw [hnil] at hhead; simp at hhead
        | some last =>
          rw [hhead, hlast] at hhl
          exact this parts 1 P (by intro h; rw [h] at hhead; simp at hhead) hcons
            (fun f hf => by rw [hhead] at hf; injection hf with hf'; subst hf'; exact hhl.1)
            (fun l hl => by rw [hlast] at hl; injection hl with hl'; subst hl'; exact hhl.2)
            hu1 huP
    intro xs
    induction xs with
    | nil => intro _ _ hne; exact absurd rfl hne
    | cons B₁ rest ih =>
      intro a b _ hcx hhd hlt hau hub
      have hB1a : B₁.lo = a := hhd B₁ rfl
      cases rest with
      | nil =>
        have hB1b : B₁.hi = b := hlt B₁ rfl
        exact ⟨B₁, List.mem_cons_self, hB1a ▸ hau, hB1b ▸ hub⟩
      | cons B₂ rest' =>
        by_cases huB1 : u ≤ B₁.hi
        · exact ⟨B₁, List.mem_cons_self, hB1a ▸ hau, huB1⟩
        · have h12 : B₁.hi + 1 = B₂.lo := hcx.1
          obtain ⟨B, hBm, hBlo, hBhi⟩ := ih B₂.lo b (by simp) hcx.2
            (fun f hf => by simp at hf; subst hf; rfl)
            (fun l hl => hlt l hl) (by omega) hub
          exact ⟨B, List.mem_cons_of_mem B₁ hBm, hBlo, hBhi⟩
  unfold blockAt
  cases hfind : parts.find? (fun B => decide (B.lo ≤ u ∧ u ≤ B.hi)) with
  | none =>
    exfalso
    obtain ⟨B, hBm, hBlo, hBhi⟩ := hex
    have hnone := List.find?_eq_none.mp hfind B hBm
    simp [hBlo, hBhi] at hnone
  | some B =>
    simp only [Option.getD_some]
    have hmem := List.mem_of_find?_eq_some hfind
    have hsat := List.find?_some hfind
    simp only [decide_eq_true_eq] at hsat
    exact ⟨hmem, hsat.1, hsat.2⟩

private theorem blockAt_eq_of_mem {P : ℕ} {parts : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P parts) {B : IntervalBlock} {u : ℕ}
    (hB : B ∈ parts) (hlo : B.lo ≤ u) (hhi : u ≤ B.hi) :
    blockAt parts u = B := by
  have hu1 : 1 ≤ u := le_trans (hPart.1 B hB).1 hlo
  have huP : u ≤ P := le_trans hhi (hPart.1 B hB).2.2
  obtain ⟨hAmem, hAlo, hAhi⟩ := blockAt_mem_and_bounds hPart hu1 huP
  set A := blockAt parts u
  have hpw := consecutiveBlocks_pairwise_lt parts hPart.2.1 (fun C hC => (hPart.1 C hC).2.1)
  obtain ⟨i, hi, hAi⟩ := List.mem_iff_getElem.mp hAmem
  obtain ⟨j, hj, hBj⟩ := List.mem_iff_getElem.mp hB
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hlt := List.pairwise_iff_getElem.mp hpw i j hi hj hij
    rw [hAi, hBj] at hlt
    omega
  · rw [← hAi, ← hBj]
  · have hlt := List.pairwise_iff_getElem.mp hpw j i hj hi hji
    rw [hAi, hBj] at hlt
    omega

private theorem find?_finRange_eq_some_before {M : ℕ} {p : Fin M → Bool} {idx : Fin M}
    (hfind : (List.finRange M).find? p = some idx) :
    p idx = true ∧ ∀ j : Fin M, j < idx → p j = false := by
  obtain ⟨hp, as, bs, heq, hbefore⟩ := List.find?_eq_some_iff_append.mp hfind
  refine ⟨hp, fun j hj => ?_⟩
  have hj_mem : j ∈ List.finRange M := List.mem_finRange j
  rw [heq] at hj_mem
  have hpw : (List.finRange M).Pairwise (· < ·) := List.pairwise_lt_finRange M
  rw [heq, List.pairwise_append] at hpw
  rcases List.mem_append.mp hj_mem with hjas | hjbs
  · simpa using hbefore j hjas
  · rcases List.mem_cons.mp hjbs with rfl | hjbs'
    · exact absurd hj (lt_irrefl _)
    · have hlt : idx < j := (List.pairwise_cons.mp hpw.2.1).1 j hjbs'
      exact absurd (lt_trans hj hlt) (lt_irrefl _)

private theorem rInt_subset_four_buckets {M P : ℕ} (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) :
    proc.rInt ⊆ bLeaf P proc chain ∪ b1 P proc chain ∪ b2 P proc chain ∪ b3 P proc chain := by
  have hSepRange : ∀ u v : ℕ, 1 ≤ u → u ≤ P → 1 ≤ v → v ≤ P →
      1 ≤ partSepScale P chain u v ∧ partSepScale P chain u v ≤ M + 1 := by
    intro u v hu1 huP hv1 hvP
    unfold partSepScale
    have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
    simp only [hcond, ↓reduceIte]
    split
    · next ℓ _ => exact ⟨by omega, by omega⟩
    · exact ⟨by omega, le_rfl⟩
  intro e he
  obtain ⟨hs1, hsx, hxy, _, hyz⟩ := rInt_ord proc e he
  have h1Range := hSepRange e.s e.x hs1 (by omega) (by omega) (by omega)
  have h2Range := hSepRange e.x e.y (by omega) (by omega) (by omega) (by omega)
  simp only [Finset.mem_union, bLeaf, b1, b2, b3, Finset.mem_filter]
  set s1 := partSepScale P chain e.s e.x
  set s2 := partSepScale P chain e.x e.y
  by_cases hs2M : s2 = M + 1
  · exact Or.inl (Or.inl (Or.inl ⟨he, hs2M⟩))
  · have hs2_le : s2 ≤ M := by omega
    rcases lt_trichotomy s1 s2 with hlt | heq | hgt
    · exact Or.inl (Or.inl (Or.inr ⟨he, h1Range.1, hlt, hs2_le⟩))
    · exact Or.inr ⟨he, h1Range.1, heq, hs2_le⟩
    · exact Or.inl (Or.inr ⟨he, h2Range.1, hgt, h1Range.2⟩)

/-- **Proposition 7.1** (`prop:dyadic-collapse`, Degeneration of `ℬ_leaf` and `ℬ_3` on the
Dyadic Partition):
On the dyadic partition `𝒫_0 ≻ ... ≻ 𝒫_M` (`M = ⌈log_2 max(P, 2)⌉`), `max_{X ∈ 𝒫_ℓ} |X| = ⌈P / 2^ℓ⌉`
for `0 ≤ ℓ ≤ M`, every leaf block `Q ∈ 𝒫_M` has `|Q| = 1`, and every `proc : FoldedPopProcess P`
has `ℬ_leaf = ∅`, `ℬ_3 = ∅`, `ℛ_int(H̃) = ℬ_1 ⊔ ℬ_2`, and `J(H̃) = |ℬ_1| + |ℬ_2|`. -/
theorem prop_7_1_dyadic_collapse (P : ℕ) (hP : 1 ≤ P) :
    let M := dyadicScaleCount P
    let chain := dyadicPartitionChain P
    1 ≤ M ∧
    IsNestedPartitionChain P chain ∧
    (∀ ℓ : Fin (M + 1),
      ((chain ℓ).map IntervalBlock.size).foldr max 0 =
        (P + 2 ^ ℓ.val - 1) / 2 ^ ℓ.val) ∧
    (∀ Q ∈ chain (Fin.last M), Q.size = 1) ∧
    (∀ proc : FoldedPopProcess P,
      bLeaf P proc chain = ∅ ∧
      b3 P proc chain = ∅ ∧
      Disjoint (b1 P proc chain) (b2 P proc chain) ∧
      proc.rInt = b1 P proc chain ∪ b2 P proc chain ∧
      proc.J = (b1 P proc chain).card + (b2 P proc chain).card) := by
  dsimp only
  set M := dyadicScaleCount P
  set chain := dyadicPartitionChain P
  -- 1. `1 ≤ M`
  have hM1 : 1 ≤ M := by
    by_contra hlt
    have h0 : Nat.clog 2 (max P 2) ≤ 0 := by dsimp [M, dyadicScaleCount] at hlt; omega
    rw [Nat.clog_le_iff_le_pow (by decide)] at h0
    simp at h0
  -- 2. `IsNestedPartitionChain P chain`
  have hNested : IsNestedPartitionChain P chain := by
    refine ⟨hP, ?_, fun ℓ => dyadicPartitionLevel_isPartition P hP ℓ.val, ?_⟩
    · have hPne : P ≠ 0 := by omega
      simp [chain, dyadicPartitionChain, dyadicPartitionLevel, hPne]
    · intro ℓ Y hY
      simp only [chain, dyadicPartitionChain, Fin.val_succ, dyadicPartitionLevel,
        List.mem_flatMap] at hY
      obtain ⟨X, hX, hYsub⟩ := hY
      have hPart := dyadicPartitionLevel_isPartition P hP ℓ.val
      obtain ⟨hXlo, hXle, _⟩ := hPart.1 X hX
      obtain ⟨_, hYbnds, _⟩ := dyadicSplitBlock_props X hXlo hXle
      obtain ⟨h1, _, h3⟩ := hYbnds Y hYsub
      exact ⟨X, hX, h1, h3⟩
  -- 3. Maximum block size formula
  have hMaxSize : ∀ ℓ : Fin (M + 1),
      ((chain ℓ).map IntervalBlock.size).foldr max 0 =
        (P + 2 ^ ℓ.val - 1) / 2 ^ ℓ.val :=
    fun ℓ => dyadicPartitionLevel_max_size P hP ℓ.val
  -- 4. Leaf blocks have size `1`
  have hLeafOne : ∀ Q ∈ chain (Fin.last M), Q.size = 1 := by
    have hP_le_pow : P ≤ 2 ^ M := by
      have hmax : max P 2 ≤ 2 ^ M :=
        (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp (le_rfl : Nat.clog 2 (max P 2) ≤ M)
      exact le_trans (le_max_left P 2) hmax
    have hCeilOne : (P + 2 ^ M - 1) / 2 ^ M = 1 := by
      set m := P - 1
      have hm_lt : m < 2 ^ M := by omega
      have h1 : P + 2 ^ M - 1 = m + 2 ^ M := by omega
      rw [h1, Nat.add_div_right m (Nat.two_pow_pos M), Nat.div_eq_of_lt hm_lt]
    intro Q hQ
    have hPartM := dyadicPartitionLevel_isPartition P hP M
    obtain ⟨_, hQle, _⟩ := hPartM.1 Q hQ
    have hQ1 : 1 ≤ Q.size := by simp [IntervalBlock.size, hQle]
    have hQ_le_max : Q.size ≤ ((chain (Fin.last M)).map IntervalBlock.size).foldr max 0 :=
      le_foldr_max (List.mem_map.mpr ⟨Q, hQ, rfl⟩)
    rw [hMaxSize (Fin.last M), Fin.val_last, hCeilOne] at hQ_le_max
    omega
  -- 5. Bucket collapse on every `proc : FoldedPopProcess P`
  refine ⟨hM1, hNested, hMaxSize, hLeafOne, ?_⟩
  intro proc
  have hbLeaf_empty : bLeaf P proc chain = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    simp only [bLeaf, Finset.mem_filter] at he
    obtain ⟨he_rInt, hsepM⟩ := he
    obtain ⟨_, _, hxy, _, hyz⟩ := rInt_ord proc e he_rInt
    have hx1 : 1 ≤ e.x := by omega
    have hxP : e.x ≤ P := by omega
    have hy1 : 1 ≤ e.y := by omega
    have hyP : e.y ≤ P := by omega
    unfold partSepScale at hsepM
    have hcond : ¬ (P < e.x ∨ P < e.y ∨ e.x = 0 ∨ e.y = 0) := by omega
    simp only [hcond, ↓reduceIte] at hsepM
    cases hfind : (List.finRange (dyadicScaleCount P)).find?
        (fun ℓ => decide (blockAt (chain ℓ.succ) e.x ≠ blockAt (chain ℓ.succ) e.y)) with
    | some ℓ =>
      rw [hfind] at hsepM
      dsimp only at hsepM
      have := ℓ.isLt
      omega
    | none =>
      let ℓLast : Fin (dyadicScaleCount P) := ⟨M - 1, by omega⟩
      have hfalse := List.find?_eq_none.mp hfind ℓLast (List.mem_finRange ℓLast)
      simp only [decide_eq_true_eq, not_not] at hfalse
      have hsucc_eq : ℓLast.succ = Fin.last M := by ext; simp [ℓLast]; omega
      rw [hsucc_eq] at hfalse
      have hPartM : IsContiguousBlockPartition P (chain (Fin.last M)) :=
        hNested.2.2.1 (Fin.last M)
      obtain ⟨hQmem, hQxlo, hQxhi⟩ := blockAt_mem_and_bounds hPartM hx1 hxP
      obtain ⟨_, hQylo, hQyhi⟩ := blockAt_mem_and_bounds hPartM hy1 hyP
      have hQsz := hLeafOne _ hQmem
      rw [← hfalse] at hQylo hQyhi
      set Q := blockAt (chain (Fin.last M)) e.x
      have hQle : Q.lo ≤ Q.hi := le_trans hQxlo hQxhi
      simp only [IntervalBlock.size, hQle, ↓reduceIte] at hQsz
      omega
  have hb3_empty : b3 P proc chain = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    simp only [b3, Finset.mem_filter] at he
    obtain ⟨he_rInt, hs1_pos, hs12_eq, hs2_le⟩ := he
    obtain ⟨hs_pos, hsx, hxy, _, hyz⟩ := rInt_ord proc e he_rInt
    have hsP : e.s ≤ P := by omega
    have hx1 : 1 ≤ e.x := by omega
    have hxP : e.x ≤ P := by omega
    have hy1 : 1 ≤ e.y := by omega
    have hyP : e.y ≤ P := by omega
    -- Helper extracting exact separating index `idx : Fin M` from `partSepScale = ℓ` (`1 ≤ ℓ ≤ M`)
    have hSepChar : ∀ (u v : ℕ), 1 ≤ u → u ≤ P → 1 ≤ v → v ≤ P →
        ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ M → partSepScale P chain u v = ℓ →
        ∃ idx : Fin M, idx.val + 1 = ℓ ∧
          blockAt (chain idx.succ) u ≠ blockAt (chain idx.succ) v ∧
          blockAt (chain idx.castSucc) u = blockAt (chain idx.castSucc) v := by
      intro u v hu1 huP hv1 hvP ℓ hℓ1 hℓM hsep
      unfold partSepScale at hsep
      have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
      simp only [hcond, ↓reduceIte] at hsep
      cases hfind : (List.finRange (dyadicScaleCount P)).find?
          (fun k => decide (blockAt (chain k.succ) u ≠ blockAt (chain k.succ) v)) with
      | none => rw [hfind] at hsep; dsimp only at hsep; omega
      | some idx =>
        rw [hfind] at hsep
        dsimp only at hsep
        obtain ⟨hidx_true, hbefore⟩ := find?_finRange_eq_some_before hfind
        simp only [decide_eq_true_eq] at hidx_true
        refine ⟨idx, hsep, hidx_true, ?_⟩
        by_cases hidx0 : idx.val = 0
        · have hc0 : idx.castSucc = 0 := by ext; exact hidx0
          rw [hc0, hNested.2.1]
          have h1u : 1 ≤ u ∧ u ≤ P := ⟨hu1, huP⟩
          have h1v : 1 ≤ v ∧ v ≤ P := ⟨hv1, hvP⟩
          simp [blockAt, h1u, h1v]
        · let prev : Fin (dyadicScaleCount P) := ⟨idx.val - 1, by omega⟩
          have hprev_lt : prev < idx := by change prev.val < idx.val; dsimp [prev]; omega
          have hpfalse := hbefore prev hprev_lt
          simp only [decide_eq_false_iff_not, not_not] at hpfalse
          have hsucc_eq : prev.succ = idx.castSucc := by ext; dsimp [prev]; omega
          rwa [hsucc_eq] at hpfalse
    set ℓ := partSepScale P chain e.x e.y
    obtain ⟨idx, hidx_eq, hne_sx, heq_sx_prev⟩ :=
      hSepChar e.s e.x hs_pos hsP hx1 hxP ℓ (hs12_eq ▸ hs1_pos) hs2_le hs12_eq
    obtain ⟨idx', hidx'_eq, hne_xy, heq_xy_prev⟩ :=
      hSepChar e.x e.y hx1 hxP hy1 hyP ℓ (hs12_eq ▸ hs1_pos) hs2_le rfl
    have hidx_same : idx = idx' := by ext; omega
    subst idx'
    -- All three keys `e.s < e.x < e.y` lie in the same parent block `X ∈ chain idx.castSucc`
    have hPartPrev := hNested.2.2.1 idx.castSucc
    have hPartCurr := hNested.2.2.1 idx.succ
    set X := blockAt (chain idx.castSucc) e.x
    obtain ⟨hXmem, hXxlo, hXxhi⟩ := blockAt_mem_and_bounds hPartPrev hx1 hxP
    obtain ⟨_, hXslo, hXshi⟩ := blockAt_mem_and_bounds hPartPrev hs_pos hsP
    obtain ⟨_, hXylo, hXyhi⟩ := blockAt_mem_and_bounds hPartPrev hy1 hyP
    rw [heq_sx_prev] at hXslo hXshi
    rw [← heq_xy_prev] at hXylo hXyhi
    -- Every key in `[X.lo, X.hi]` has its scale-`idx.succ` block inside `dyadicSplitBlock X`
    have hInSplit : ∀ w : ℕ, X.lo ≤ w → w ≤ X.hi →
        blockAt (chain idx.succ) w ∈ dyadicSplitBlock X := by
      intro w hwlo hwhi
      have hXle : X.lo ≤ X.hi := le_trans hXxlo hXxhi
      have hsz : X.size = X.hi - X.lo + 1 := by simp [IntervalBlock.size, hXle]
      have hsub_in_curr : ∀ Y ∈ dyadicSplitBlock X, Y ∈ chain idx.succ := by
        intro Y hY
        simp only [chain, dyadicPartitionChain, Fin.val_succ, dyadicPartitionLevel,
          List.mem_flatMap]
        exact ⟨X, hXmem, hY⟩
      by_cases h1 : X.size ≤ 1
      · have hsplit1 : dyadicSplitBlock X = [X] := by simp [dyadicSplitBlock, h1]
        rw [hsplit1, List.mem_singleton]
        exact blockAt_eq_of_mem hPartCurr (hsub_in_curr X (by simp [hsplit1])) hwlo hwhi
      · set half := X.size / 2
        let Y₁ : IntervalBlock := ⟨X.lo, X.lo + half - 1⟩
        let Y₂ : IntervalBlock := ⟨X.lo + half, X.hi⟩
        have hsplit2 : dyadicSplitBlock X = [Y₁, Y₂] := by simp [dyadicSplitBlock, h1, Y₁, Y₂, half]
        rw [hsplit2]
        by_cases hw1 : w ≤ X.lo + half - 1
        · have hY1 : blockAt (chain idx.succ) w = Y₁ :=
            blockAt_eq_of_mem hPartCurr (hsub_in_curr Y₁ (by simp [hsplit2])) hwlo hw1
          simp [hY1]
        · have hw2 : X.lo + half ≤ w := by omega
          have hY2 : blockAt (chain idx.succ) w = Y₂ :=
            blockAt_eq_of_mem hPartCurr (hsub_in_curr Y₂ (by simp [hsplit2])) hw2 hwhi
          simp [hY2]
    have hBs_in := hInSplit e.s hXslo hXshi
    have hBx_in := hInSplit e.x hXxlo hXxhi
    have hBy_in := hInSplit e.y hXylo hXyhi
    obtain ⟨_, hBs_lo, hBs_hi⟩ := blockAt_mem_and_bounds hPartCurr hs_pos hsP
    obtain ⟨_, hBx_lo, hBx_hi⟩ := blockAt_mem_and_bounds hPartCurr hx1 hxP
    obtain ⟨_, hBy_lo, hBy_hi⟩ := blockAt_mem_and_bounds hPartCurr hy1 hyP
    by_cases h1 : X.size ≤ 1
    · simp only [dyadicSplitBlock, h1, ↓reduceIte, List.mem_singleton] at hBs_in hBx_in
      exact hne_sx (hBs_in.trans hBx_in.symm)
    · simp only [dyadicSplitBlock, h1, ↓reduceIte, List.mem_cons, List.not_mem_nil,
        or_false] at hBs_in hBx_in hBy_in
      set half := X.size / 2
      have hhalf1 : 1 ≤ half := by omega
      rcases hBx_in with hBx1 | hBx2
      · rcases hBs_in with hBs1 | hBs2
        · exact hne_sx (hBs1.trans hBx1.symm)
        · rw [hBx1] at hBx_hi
          rw [hBs2] at hBs_lo
          dsimp only at hBx_hi hBs_lo
          omega
      · rcases hBy_in with hBy1 | hBy2
        · rw [hBy1] at hBy_hi
          rw [hBx2] at hBx_lo
          dsimp only at hBy_hi hBx_lo
          omega
        · exact hne_xy (hBx2.trans hBy2.symm)
  have hDisj : Disjoint (b1 P proc chain) (b2 P proc chain) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [b1, b2, Finset.mem_filter] at he1 he2
    omega
  have hrInt_eq : proc.rInt = b1 P proc chain ∪ b2 P proc chain := by
    apply Finset.Subset.antisymm
    · intro e he
      have h4 := rInt_subset_four_buckets proc chain he
      simpa [hbLeaf_empty, hb3_empty] using h4
    · exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hJ_eq : proc.J = (b1 P proc chain).card + (b2 P proc chain).card := by
    unfold FoldedPopProcess.J
    rw [hrInt_eq, Finset.card_union_of_disjoint hDisj]
  exact ⟨hbLeaf_empty, hb3_empty, hDisj, hrInt_eq, hJ_eq⟩

end Solution.ScaleWeights
