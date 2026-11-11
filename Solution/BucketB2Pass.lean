module

public import Challenge.Definitions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sigma

@[expose] public section

namespace Solution.BucketB2Pass

open SplayTree

/-!
## 1. Folded POP Process & Cascade Event Structural Lemmas
-/

private theorem takeThrough_prefix {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (b : α), takeThrough xs b <+: xs
  | [], _ => List.nil_prefix
  | x :: xs, b => by
    unfold takeThrough
    split
    · exact ⟨xs, rfl⟩
    · obtain ⟨t, ht⟩ := takeThrough_prefix xs b
      exact ⟨t, by simp [ht]⟩

private theorem mem_of_mem_leftSpine {α : Type} :
    ∀ (t : BinaryTree α) (x : α), x ∈ leftSpine t → x ∈ t
  | .nil, _, hx => by simp [leftSpine] at hx
  | .node k l r, x, hx => by
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with hxl | rfl
    · exact BinaryTree.Mem.left (mem_of_mem_leftSpine l x hxl)
    · exact BinaryTree.Mem.here

private theorem leftSpine_pairwise (t : BinaryTree ℕ) (hbst : t.IsBST) :
    (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node key l r ihl _ =>
    simp only [leftSpine]
    rw [List.pairwise_append]
    refine ⟨ihl (BinaryTree.IsBST_left_of_IsBST hbst),
      List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact BinaryTree.lt_of_IsBST_left l key r hbst (mem_of_mem_leftSpine l x hx)

private theorem stepIdx_of_mem_foldedPopRotsAt (stepIdx : ℕ)
    (st : BinaryTree ℕ × Option ℕ) (op : FoldedOp) (e : InternalPopRot)
    (he : e ∈ foldedPopRotsAt stepIdx st op) :
    e.stepIdx = stepIdx := by
  cases op with
  | push _ => simp [foldedPopRotsAt] at he
  | shift => simp [foldedPopRotsAt] at he
  | upperRot _ _ => simp [foldedPopRotsAt] at he
  | pop s =>
    simp only [foldedPopRotsAt] at he
    cases hb : st.2 with
    | none => rw [hb] at he; simp at he
    | some b =>
      rw [hb] at he
      rw [List.mem_filterMap] at he
      obtain ⟨idx, _, hsome⟩ := he
      revert hsome
      cases ((takeThrough (leftSpine st.1) b)[2 * (idx + 1) - 1]?) <;>
        cases ((takeThrough (leftSpine st.1) b)[2 * (idx + 1)]?) <;>
        cases ((takeThrough (leftSpine st.1) b)[2 * (idx + 1) + 1]?) <;>
        simp only [Option.some.injEq, reduceCtorEq, false_implies]
      intro h; rw [← h]

private theorem mem_collectFoldedPopRots_iff :
    ∀ (steps : List FoldedOp) (idx : ℕ) (st : BinaryTree ℕ × Option ℕ) (e : InternalPopRot),
      e ∈ collectFoldedPopRots idx st steps ↔
        ∃ (k : ℕ) (hk : k < steps.length),
          e.stepIdx = idx + k ∧
          e ∈ foldedPopRotsAt (idx + k) ((steps.take k).foldl FoldedOp.step st) steps[k]
  | [], _, _, _ => by simp [collectFoldedPopRots]
  | op :: rest, idx, st, e => by
    simp only [collectFoldedPopRots, List.mem_append]
    constructor
    · rintro (hhead | htail)
      · refine ⟨0, by simp, ?_, by simpa using hhead⟩
        simpa using stepIdx_of_mem_foldedPopRotsAt idx st op e hhead
      · rw [mem_collectFoldedPopRots_iff] at htail
        obtain ⟨k, hk, hstep, hmem⟩ := htail
        refine ⟨k + 1, Nat.succ_lt_succ hk, by omega, ?_⟩
        have hidx : idx + 1 + k = idx + (k + 1) := by omega
        rw [hidx] at hmem
        simpa [List.take_succ_cons, List.foldl_cons] using hmem
    · rintro ⟨k, hk, hstep, hmem⟩
      cases k with
      | zero =>
        left
        simpa using hmem
      | succ k' =>
        right
        rw [mem_collectFoldedPopRots_iff]
        have hk' : k' < rest.length := Nat.lt_of_succ_lt_succ hk
        have hidx : idx + (k' + 1) = idx + 1 + k' := by omega
        refine ⟨k', hk', by omega, ?_⟩
        rw [← hidx]
        simpa [List.take_succ_cons, List.foldl_cons] using hmem

private theorem mem_rInt_iff {P : ℕ} (proc : FoldedPopProcess P) (e : InternalPopRot) :
    e ∈ proc.rInt ↔
      ∃ hτ : e.stepIdx < proc.steps.length,
        e ∈ foldedPopRotsAt e.stepIdx (proc.stateAt e.stepIdx) proc.steps[e.stepIdx] := by
  unfold FoldedPopProcess.rInt
  rw [List.mem_toFinset, mem_collectFoldedPopRots_iff]
  constructor
  · rintro ⟨k, hk, hstep, hmem⟩
    simp only [Nat.zero_add] at hstep hmem
    subst hstep
    exact ⟨hk, hmem⟩
  · rintro ⟨hτ, hmem⟩
    exact ⟨e.stepIdx, hτ, by omega, by simpa [FoldedPopProcess.stateAt] using hmem⟩

private theorem rInt_unpack {P : ℕ} (proc : FoldedPopProcess P) {e : InternalPopRot}
    (he : e ∈ proc.rInt) :
    ∃ (hτ : e.stepIdx < proc.steps.length) (b : ℕ),
      proc.steps[e.stepIdx] = .pop e.s ∧
      (proc.stateAt e.stepIdx).2 = some b ∧
      let sub := takeThrough (leftSpine (proc.treeAt e.stepIdx)) b
      let k := sub.length - 1
      e.h = (k - 1) / 2 ∧
      1 ≤ e.j ∧ e.j ≤ e.h ∧
      sub[2 * e.j - 1]? = some e.x ∧
      sub[2 * e.j]? = some e.y ∧
      sub[2 * e.j + 1]? = some e.z ∧
      e = { stepIdx := e.stepIdx, s := e.s, j := e.j, h := e.h, x := e.x, y := e.y, z := e.z } := by
  obtain ⟨hτ, hmem⟩ := (mem_rInt_iff proc e).mp he
  rcases hop : proc.steps[e.stepIdx] with w | _ | ⟨u, v⟩ | s₀
  · rw [hop] at hmem; simp [foldedPopRotsAt] at hmem
  · rw [hop] at hmem; simp [foldedPopRotsAt] at hmem
  · rw [hop] at hmem; simp [foldedPopRotsAt] at hmem
  · rw [hop] at hmem
    simp only [foldedPopRotsAt] at hmem
    rcases hb : (proc.stateAt e.stepIdx).2 with _ | b
    · rw [hb] at hmem; simp at hmem
    · rw [hb, List.mem_filterMap] at hmem
      obtain ⟨idx, hidx, hsome⟩ := hmem
      rw [List.mem_range] at hidx
      let sub := takeThrough (leftSpine (proc.stateAt e.stepIdx).1) b
      change (match sub[2 * (idx + 1) - 1]?, sub[2 * (idx + 1)]?, sub[2 * (idx + 1) + 1]? with
        | some x, some y, some z =>
          some { stepIdx := e.stepIdx, s := s₀, j := idx + 1,
                 h := (sub.length - 1 - 1) / 2, x := x, y := y, z := z }
        | _, _, _ => none) = some e at hsome
      rcases hx : sub[2 * (idx + 1) - 1]? with _ | x <;>
        rcases hy : sub[2 * (idx + 1)]? with _ | y <;>
        rcases hz : sub[2 * (idx + 1) + 1]? with _ | z <;>
        rw [hx, hy, hz] at hsome <;>
        simp only [Option.some.injEq, reduceCtorEq] at hsome
      have hs : e.s = s₀ := by rw [← hsome]
      have hj : e.j = idx + 1 := by rw [← hsome]
      have hh : e.h = (sub.length - 1 - 1) / 2 := by rw [← hsome]
      have hex : e.x = x := by rw [← hsome]
      have hey : e.y = y := by rw [← hsome]
      have hez : e.z = z := by rw [← hsome]
      have heta : e = { stepIdx := e.stepIdx, s := e.s, j := e.j, h := e.h,
                        x := e.x, y := e.y, z := e.z } := by
        cases e; rfl
      dsimp only [sub] at hh
      refine ⟨hτ, b, ?_, rfl, hh, by omega, by omega, ?_, ?_, ?_, heta⟩
      · rwa [hs]
      · simpa [FoldedPopProcess.treeAt, hj, hex] using hx
      · simpa [FoldedPopProcess.treeAt, hj, hey] using hy
      · simpa [FoldedPopProcess.treeAt, hj, hez] using hz

private theorem rInt_mem_leftSpine {P : ℕ} (proc : FoldedPopProcess P) {e : InternalPopRot}
    (he : e ∈ proc.rInt) :
    e.x ∈ leftSpine (proc.treeAt e.stepIdx) ∧
    e.y ∈ leftSpine (proc.treeAt e.stepIdx) ∧
    e.z ∈ leftSpine (proc.treeAt e.stepIdx) := by
  obtain ⟨_, b, _, _, _, _, _, hx, hy, hz, _⟩ := rInt_unpack proc he
  have hpref := takeThrough_prefix (leftSpine (proc.treeAt e.stepIdx)) b
  exact ⟨hpref.mem (List.mem_of_getElem? hx),
    hpref.mem (List.mem_of_getElem? hy),
    hpref.mem (List.mem_of_getElem? hz)⟩

private theorem pairwise_lt_getElem? {xs : List ℕ} (hpw : xs.Pairwise (· < ·))
    {i₁ i₂ u v : ℕ} (hlt : i₁ < i₂) (hu : xs[i₁]? = some u) (hv : xs[i₂]? = some v) :
    u < v := by
  rw [List.getElem?_eq_some_iff] at hu hv
  obtain ⟨hi₁, rfl⟩ := hu
  obtain ⟨hi₂, rfl⟩ := hv
  exact List.pairwise_iff_getElem.mp hpw i₁ i₂ hi₁ hi₂ hlt

private theorem pairwise_le_getElem? {xs : List ℕ} (hpw : xs.Pairwise (· < ·))
    {i₁ i₂ u v : ℕ} (hle : i₁ ≤ i₂) (hu : xs[i₁]? = some u) (hv : xs[i₂]? = some v) :
    u ≤ v := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · rw [hu] at hv; exact le_of_eq (Option.some.inj hv)
  · exact le_of_lt (pairwise_lt_getElem? hpw hlt hu hv)

private theorem rInt_same_step_eq {P : ℕ} (proc : FoldedPopProcess P) {e₁ e₂ : InternalPopRot}
    (he₁ : e₁ ∈ proc.rInt) (he₂ : e₂ ∈ proc.rInt) (hstep : e₁.stepIdx = e₂.stepIdx)
    (hj : e₁.j = e₂.j) : e₁ = e₂ := by
  obtain ⟨hτ₁, b₁, hop₁, hb₁, hh₁, _, _, hx₁, hy₁, hz₁, heq₁⟩ := rInt_unpack proc he₁
  obtain ⟨_, b₂, hop₂, hb₂, hh₂, _, _, hx₂, hy₂, hz₂, heq₂⟩ := rInt_unpack proc he₂
  have hop_eq : FoldedOp.pop e₁.s = FoldedOp.pop e₂.s := by
    rw [← hop₁]; simpa [hstep] using hop₂
  injection hop_eq with hs_eq
  have hb_eq : some b₁ = some b₂ := by
    rw [← hb₁]; simpa [hstep] using hb₂
  injection hb_eq with hb_eq'
  subst hb_eq'
  have hsub_eq : takeThrough (leftSpine (proc.treeAt e₁.stepIdx)) b₁ =
      takeThrough (leftSpine (proc.treeAt e₂.stepIdx)) b₁ := by rw [hstep]
  have hh_eq : e₁.h = e₂.h := by rw [hh₁, hh₂, hsub_eq]
  have hx_eq : some e₁.x = some e₂.x := by rw [← hx₁, hsub_eq, hj, hx₂]
  have hy_eq : some e₁.y = some e₂.y := by rw [← hy₁, hsub_eq, hj, hy₂]
  have hz_eq : some e₁.z = some e₂.z := by rw [← hz₁, hsub_eq, hj, hz₂]
  have hx' : e₁.x = e₂.x := Option.some.inj hx_eq
  have hy' : e₁.y = e₂.y := Option.some.inj hy_eq
  have hz' : e₁.z = e₂.z := Option.some.inj hz_eq
  cases e₁; cases e₂
  simp only [InternalPopRot.mk.injEq] at *
  exact ⟨hstep, hs_eq, hj, hh_eq, hx', hy', hz'⟩

private theorem rInt_same_step_order {P : ℕ} (proc : FoldedPopProcess P)
    (hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST)
    {e₁ e₂ : InternalPopRot} (he₁ : e₁ ∈ proc.rInt) (he₂ : e₂ ∈ proc.rInt)
    (hstep : e₁.stepIdx = e₂.stepIdx) (hj : e₁.j < e₂.j) :
    e₁.y < e₂.x ∧ e₁.z ≤ e₂.x := by
  obtain ⟨hτ₁, b₁, _, hb₁, _, hj₁_ge, _, _, hy₁, hz₁, _⟩ := rInt_unpack proc he₁
  obtain ⟨_, b₂, _, hb₂, _, _, _, hx₂, _, _, _⟩ := rInt_unpack proc he₂
  have hb_eq : some b₁ = some b₂ := by rw [← hb₁]; simpa [hstep] using hb₂
  injection hb_eq with hb_eq'
  subst hb_eq'
  have hls_pw := leftSpine_pairwise (proc.treeAt e₁.stepIdx) (hBST e₁.stepIdx (le_of_lt hτ₁))
  have hsub_pw : (takeThrough (leftSpine (proc.treeAt e₁.stepIdx)) b₁).Pairwise (· < ·) := by
    obtain ⟨suf, hsuf⟩ := takeThrough_prefix (leftSpine (proc.treeAt e₁.stepIdx)) b₁
    rw [← hsuf, List.pairwise_append] at hls_pw
    exact hls_pw.1
  have hx₂' : (takeThrough (leftSpine (proc.treeAt e₁.stepIdx)) b₁)[2 * e₂.j - 1]? = some e₂.x := by
    simpa [hstep] using hx₂
  exact ⟨pairwise_lt_getElem? hsub_pw (by omega) hy₁ hx₂',
    pairwise_le_getElem? hsub_pw (by omega) hz₁ hx₂'⟩

private theorem rInt_nextCascadeRot {P : ℕ} (proc : FoldedPopProcess P) {e : InternalPopRot}
    (he : e ∈ proc.rInt) (hjne : e.j ≠ e.h) :
    ∃ eNext ∈ proc.rInt,
      proc.nextCascadeRot? e = some eNext ∧
      eNext.stepIdx = e.stepIdx ∧
      eNext.s = e.s ∧
      eNext.j = e.j + 1 ∧
      eNext.x = e.z := by
  obtain ⟨hτ, b, hop, hb, hh, hj1, hjle, _, _, hz, _⟩ := rInt_unpack proc he
  have hjlt : e.j < e.h := lt_of_le_of_ne hjle hjne
  unfold FoldedPopProcess.treeAt at hh hz
  set sub := takeThrough (leftSpine (proc.stateAt e.stepIdx).1) b
  have hlen : 2 * (e.j + 1) + 1 < sub.length := by omega
  let eCand : InternalPopRot := {
    stepIdx := e.stepIdx
    s := e.s
    j := e.j + 1
    h := e.h
    x := sub[2 * (e.j + 1) - 1]'(by omega)
    y := sub[2 * (e.j + 1)]'(by omega)
    z := sub[2 * (e.j + 1) + 1]'hlen
  }
  have heCand_at : eCand ∈ foldedPopRotsAt e.stepIdx (proc.stateAt e.stepIdx) proc.steps[e.stepIdx] := by
    rw [hop]
    simp only [foldedPopRotsAt, hb, List.mem_filterMap, List.mem_range]
    refine ⟨e.j, by change e.j < (sub.length - 1 - 1) / 2; omega, ?_⟩
    have hx' : sub[2 * (e.j + 1) - 1]? = some eCand.x := List.getElem?_eq_getElem (by omega)
    have hy' : sub[2 * (e.j + 1)]? = some eCand.y := List.getElem?_eq_getElem (by omega)
    have hz' : sub[2 * (e.j + 1) + 1]? = some eCand.z := List.getElem?_eq_getElem hlen
    change (match sub[2 * (e.j + 1) - 1]?, sub[2 * (e.j + 1)]?, sub[2 * (e.j + 1) + 1]? with
      | some x, some y, some z =>
        some { stepIdx := e.stepIdx, s := e.s, j := e.j + 1,
               h := (sub.length - 1 - 1) / 2, x := x, y := y, z := z }
      | _, _, _ => none) = some eCand
    rw [hx', hy', hz', ← hh]
  have heCand_rInt : eCand ∈ proc.rInt := (mem_rInt_iff proc eCand).mpr ⟨hτ, heCand_at⟩
  have heCand_list : eCand ∈ collectFoldedPopRots 0 (.nil, none) proc.steps :=
    List.mem_toFinset.mp heCand_rInt
  have hp_cand : (eCand.stepIdx == e.stepIdx && eCand.j == e.j + 1) = true := by
    simp [eCand]
  have hfind_some : ∃ eFound,
      (collectFoldedPopRots 0 (.nil, none) proc.steps).find?
        (fun e' => e'.stepIdx == e.stepIdx && e'.j == e.j + 1) = some eFound := by
    cases hfind : (collectFoldedPopRots 0 (.nil, none) proc.steps).find?
        (fun e' => e'.stepIdx == e.stepIdx && e'.j == e.j + 1) with
    | none =>
      exfalso
      exact List.find?_eq_none.mp hfind eCand heCand_list hp_cand
    | some eFound => exact ⟨eFound, rfl⟩
  obtain ⟨eFound, hfind⟩ := hfind_some
  have hmem_found : eFound ∈ proc.rInt :=
    List.mem_toFinset.mpr (List.mem_of_find?_eq_some hfind)
  have hp_found := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hp_found
  have heq_found : eFound = eCand :=
    rInt_same_step_eq proc hmem_found heCand_rInt hp_found.1 hp_found.2
  subst heq_found
  have hx_eq : eCand.x = e.z := by
    have hidx : 2 * (e.j + 1) - 1 = 2 * e.j + 1 := by omega
    have h1 : sub[2 * (e.j + 1) - 1]? = some eCand.x := List.getElem?_eq_getElem (by omega)
    rw [hidx, hz] at h1
    exact (Option.some.inj h1).symm
  exact ⟨eCand, heCand_rInt, hfind, rfl, rfl, rfl, hx_eq⟩

private theorem nextCascadeRot_inj {P : ℕ} (proc : FoldedPopProcess P)
    {e₁ e₂ eNext : InternalPopRot}
    (he₁ : e₁ ∈ proc.rInt) (he₂ : e₂ ∈ proc.rInt)
    (hn₁ : proc.nextCascadeRot? e₁ = some eNext)
    (hn₂ : proc.nextCascadeRot? e₂ = some eNext) :
    e₁ = e₂ := by
  unfold FoldedPopProcess.nextCascadeRot? at hn₁ hn₂
  have hp₁ := List.find?_some hn₁
  have hp₂ := List.find?_some hn₂
  simp only [Bool.and_eq_true, beq_iff_eq] at hp₁ hp₂
  exact rInt_same_step_eq proc he₁ he₂ (by omega) (by omega)

private def popKey? : FoldedOp → Option ℕ
  | .pop s => some s
  | _ => none

private theorem popSeq_findIdx_props :
    ∀ (steps : List FoldedOp) (a len : ℕ),
      steps.filterMap popKey? = List.range' a len →
      (∀ s, a ≤ s → s < a + len →
        steps.findIdx (· == .pop s) < steps.length ∧
        steps[steps.findIdx (· == .pop s)]? = some (.pop s)) ∧
      (∀ τ s, τ < steps.length → steps[τ]? = some (.pop s) →
        a ≤ s ∧ s < a + len ∧ τ = steps.findIdx (· == .pop s)) ∧
      (∀ s₁ s₂, a ≤ s₁ → s₁ < s₂ → s₂ < a + len →
        steps.findIdx (· == .pop s₁) < steps.findIdx (· == .pop s₂))
  | [], a, len, hseq => by
    simp only [List.filterMap_nil, List.nil_eq] at hseq
    have hlen : len = 0 := by
      have := congrArg List.length hseq
      simp at this
      omega
    subst hlen
    refine ⟨by intro s h1 h2; omega, by intro τ _ hτ; simp at hτ, by intro s₁ s₂ h1 h2 h3; omega⟩
  | op :: rest, a, len, hseq => by
    cases hop : popKey? op with
    | none =>
      have hne_pop : ∀ s, (op == .pop s) = false := by
        intro s
        cases op <;> simp_all [popKey?]
      have hseq' : rest.filterMap popKey? = List.range' a len := by
        simpa [List.filterMap_cons, hop] using hseq
      obtain ⟨ih1, ih2, ih3⟩ := popSeq_findIdx_props rest a len hseq'
      refine ⟨?_, ?_, ?_⟩
      · intro s ha hb
        obtain ⟨hlt, hget⟩ := ih1 s ha hb
        simp only [List.findIdx_cons, hne_pop s, Bool.false_eq_true, ↓reduceIte]
        exact ⟨Nat.succ_lt_succ hlt, by simpa using hget⟩
      · intro τ s hτ hget
        cases τ with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
          subst hget; simp [popKey?] at hop
        | succ τ' =>
          simp only [List.getElem?_cons_succ] at hget
          obtain ⟨ha, hb, heq⟩ := ih2 τ' s (Nat.lt_of_succ_lt_succ hτ) hget
          simp only [List.findIdx_cons, hne_pop s, Bool.false_eq_true, ↓reduceIte]
          exact ⟨ha, hb, by omega⟩
      · intro s₁ s₂ ha hlt hb
        have h := ih3 s₁ s₂ ha hlt hb
        simp only [List.findIdx_cons, hne_pop, Bool.false_eq_true, ↓reduceIte]
        omega
    | some s₀ =>
      have hop_eq : op = .pop s₀ := by
        cases op <;> simp_all [popKey?]
      subst hop_eq
      cases len with
      | zero => simp [popKey?] at hseq
      | succ len' =>
        simp only [List.filterMap_cons, popKey?, List.range'_succ, List.cons.injEq] at hseq
        rcases hseq with ⟨rfl, hseq'⟩
        obtain ⟨ih1, ih2, ih3⟩ := popSeq_findIdx_props rest (s₀ + 1) len' hseq'
        refine ⟨?_, ?_, ?_⟩
        · intro s ha hb
          rcases eq_or_lt_of_le ha with hs_eq | hgt
          · subst hs_eq
            simp [List.findIdx_cons]
          · have hne : (FoldedOp.pop s₀ == FoldedOp.pop s) = false := by
              simp [Nat.ne_of_lt hgt]
            obtain ⟨hlt, hget⟩ := ih1 s (by omega) (by omega)
            simp only [List.findIdx_cons, hne, Bool.false_eq_true, ↓reduceIte]
            exact ⟨Nat.succ_lt_succ hlt, by simpa using hget⟩
        · intro τ s hτ hget
          cases τ with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, FoldedOp.pop.injEq] at hget
            subst hget
            simp [List.findIdx_cons]
          | succ τ' =>
            simp only [List.getElem?_cons_succ] at hget
            obtain ⟨ha, hb, heq⟩ := ih2 τ' s (Nat.lt_of_succ_lt_succ hτ) hget
            have hne : (FoldedOp.pop s₀ == FoldedOp.pop s) = false := by
              simp [show s₀ ≠ s by omega]
            simp only [List.findIdx_cons, hne, Bool.false_eq_true, ↓reduceIte]
            exact ⟨by omega, by omega, by omega⟩
        · intro s₁ s₂ ha hlt hb
          rcases eq_or_lt_of_le ha with hs_eq | hgt
          · subst hs_eq
            have hne₂ : (FoldedOp.pop s₀ == FoldedOp.pop s₂) = false := by
              simp [Nat.ne_of_lt hlt]
            simp [List.findIdx_cons, hne₂]
          · have hne₁ : (FoldedOp.pop s₀ == FoldedOp.pop s₁) = false := by
              simp [show s₀ ≠ s₁ by omega]
            have hne₂ : (FoldedOp.pop s₀ == FoldedOp.pop s₂) = false := by
              simp [show s₀ ≠ s₂ by omega]
            have h := ih3 s₁ s₂ (by omega) hlt (by omega)
            simp only [List.findIdx_cons, hne₁, hne₂, Bool.false_eq_true, ↓reduceIte]
            omega

private theorem popStepIdx_strict_mono {P : ℕ} (proc : FoldedPopProcess P)
    {s₁ s₂ : ℕ} (hs₁ : 1 ≤ s₁) (hlt : s₁ < s₂) (hs₂ : s₂ ≤ P) :
    proc.popStepIdx s₁ < proc.popStepIdx s₂ := by
  have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
  exact (popSeq_findIdx_props proc.steps 1 P hseq).2.2 s₁ s₂ hs₁ hlt (by omega)

private theorem rInt_stepIdx_eq_popStepIdx {P : ℕ} (proc : FoldedPopProcess P)
    {e : InternalPopRot} (he : e ∈ proc.rInt) :
    e.stepIdx = proc.popStepIdx e.s := by
  obtain ⟨hτ, _, hop, _⟩ := rInt_unpack proc he
  have hseq : proc.steps.filterMap popKey? = List.range' 1 P := proc.hPopSeq
  have hget : proc.steps[e.stepIdx]? = some (.pop e.s) := by
    rw [List.getElem?_eq_getElem hτ, hop]
  exact ((popSeq_findIdx_props proc.steps 1 P hseq).2.1 e.stepIdx e.s hτ hget).2.2


/-!
## 2. Contiguous Block Partitions, Nested Chains, and Ultrametric `partSepScale`
-/

private theorem consecutiveBlocks_lt :
    ∀ (blocks : List IntervalBlock),
      (∀ C ∈ blocks, C.lo ≤ C.hi) →
      ConsecutiveBlocks blocks →
      ∀ (i j : ℕ) (hi : i < blocks.length) (hj : j < blocks.length),
        i < j → blocks[i].hi < blocks[j].lo
  | [], _, _, i, _, hi, _, _ => by simp at hi
  | [_], _, _, i, j, hi, hj, hlt => by simp at hi hj; omega
  | C₁ :: C₂ :: rest, hle, hcons, i, j, hi, hj, hlt => by
    rcases hcons with ⟨hstep, hrest⟩
    have hle' : ∀ C ∈ (C₂ :: rest), C.lo ≤ C.hi :=
      fun C hC => hle C (List.mem_cons_of_mem C₁ hC)
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' =>
        cases j' with
        | zero =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          omega
        | succ j'' =>
          have hj' : j'' + 1 < (C₂ :: rest).length := Nat.lt_of_succ_lt_succ hj
          have h0 : (C₂ :: rest)[0].hi < (C₂ :: rest)[j'' + 1].lo :=
            consecutiveBlocks_lt (C₂ :: rest) hle' hrest 0 (j'' + 1) (by simp) hj' (by omega)
          have hC₂ : C₂.lo ≤ C₂.hi := hle C₂ (List.mem_cons_of_mem C₁ List.mem_cons_self)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0 ⊢
          omega
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        exact consecutiveBlocks_lt (C₂ :: rest) hle' hrest i' j'
          (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) (by omega)

private theorem contiguous_blocks_nodup {N : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition N blocks) : blocks.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  simp only [List.get_eq_getElem] at heq
  have hle : ∀ C ∈ blocks, C.lo ≤ C.hi := fun C hC => (hPart.1 C hC).2.1
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have hlt_b := consecutiveBlocks_lt blocks hle hPart.2.1 i j hi hj hlt
    have hlo_hi := hle blocks[i] (List.getElem_mem hi)
    rw [heq] at hlt_b hlo_hi
    omega
  · rfl
  · have hgt_b := consecutiveBlocks_lt blocks hle hPart.2.1 j i hj hi hgt
    have hlo_hi := hle blocks[j] (List.getElem_mem hj)
    rw [heq] at hgt_b
    omega

private theorem exists_block_containing :
    ∀ (blocks : List IntervalBlock) (a b u : ℕ),
      blocks ≠ [] →
      (∀ C ∈ blocks, C.lo ≤ C.hi) →
      ConsecutiveBlocks blocks →
      (blocks.head?.map IntervalBlock.lo) = some a →
      (blocks.getLast?.map IntervalBlock.hi) = some b →
      a ≤ u → u ≤ b →
      ∃ B ∈ blocks, B.lo ≤ u ∧ u ≤ B.hi
  | [], _, _, _, hne, _, _, _, _, _, _ => absurd rfl hne
  | [C], a, b, u, _, _, _, hhead, hlast, hau, hub => by
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.map_some, Option.some.injEq] at hlast
    exact ⟨C, List.mem_singleton.mpr rfl, by omega, by omega⟩
  | C₁ :: C₂ :: rest, a, b, u, _, hle, hcons, hhead, hlast, hau, hub => by
    rcases hcons with ⟨hstep, hrest⟩
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhead
    by_cases hu1 : u ≤ C₁.hi
    · exact ⟨C₁, List.mem_cons_self, by omega, hu1⟩
    · have hlast' : ((C₂ :: rest).getLast?.map IntervalBlock.hi) = some b := by
        simpa using hlast
      have hle' : ∀ C ∈ (C₂ :: rest), C.lo ≤ C.hi :=
        fun C hC => hle C (List.mem_cons_of_mem C₁ hC)
      obtain ⟨B, hB, hBlo, hBhi⟩ := exists_block_containing (C₂ :: rest) C₂.lo b u
        (List.cons_ne_nil _ _) hle' hrest rfl hlast' (by omega) hub
      exact ⟨B, List.mem_cons_of_mem C₁ hB, hBlo, hBhi⟩

private theorem blockAt_mem_and_bounds {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks) {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) :
    blockAt blocks u ∈ blocks ∧
    (blockAt blocks u).lo ≤ u ∧ u ≤ (blockAt blocks u).hi ∧
    (∀ B ∈ blocks, B = blockAt blocks u ↔ (B.lo ≤ u ∧ u ≤ B.hi)) := by
  have hne : blocks ≠ [] := by
    intro hemp
    subst hemp
    have h0 := hPart.2.2
    simp at h0
    omega
  rcases hhead : blocks.head? with _ | first
  · exact absurd (List.head?_eq_none_iff.mp hhead) hne
  rcases hlast : blocks.getLast? with _ | last
  · exact absurd (List.getLast?_eq_none_iff.mp hlast) hne
  have hends : first.lo = 1 ∧ last.hi = P := by
    have h := hPart.2.2
    rw [hhead, hlast] at h
    exact h
  have hle : ∀ C ∈ blocks, C.lo ≤ C.hi := fun C hC => (hPart.1 C hC).2.1
  obtain ⟨B₀, hB₀, hB₀lo, hB₀hi⟩ := exists_block_containing blocks 1 P u hne hle hPart.2.1
    (by simp [hhead, hends.1]) (by simp [hlast, hends.2]) hu1 huP
  unfold blockAt
  generalize hfind : blocks.find? _ = res
  cases res with
  | none =>
    exfalso
    have hnone := List.find?_eq_none.mp hfind B₀ hB₀
    simp only [decide_eq_true_eq, not_and] at hnone
    exact absurd hB₀hi (hnone hB₀lo)
  | some Bf =>
    simp only [Option.getD_some]
    have hBf_mem : Bf ∈ blocks := List.mem_of_find?_eq_some hfind
    have hBf_bounds : Bf.lo ≤ u ∧ u ≤ Bf.hi := by
      have hp := List.find?_some hfind
      simpa using hp
    refine ⟨hBf_mem, hBf_bounds.1, hBf_bounds.2, ?_⟩
    intro B hB
    constructor
    · rintro rfl; exact hBf_bounds
    · rintro ⟨hBlo, hBhi⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hB
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hBf_mem
      subst hjeq
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · have := consecutiveBlocks_lt blocks hle hPart.2.1 i j hi hj hlt
        omega
      · rfl
      · have := consecutiveBlocks_lt blocks hle hPart.2.1 j i hj hi hgt
        omega

private theorem blockAt_hi_lt_lo_of_ne {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks) {u v : ℕ}
    (hu1 : 1 ≤ u) (huv : u ≤ v) (hvP : v ≤ P)
    (hne : blockAt blocks u ≠ blockAt blocks v) :
    (blockAt blocks u).hi < (blockAt blocks v).lo := by
  obtain ⟨hmem_u, _, hu_hi, _⟩ := blockAt_mem_and_bounds hPart hu1 (by omega)
  obtain ⟨hmem_v, hv_lo, _, _⟩ := blockAt_mem_and_bounds hPart (by omega) hvP
  obtain ⟨i, hi, heq_u⟩ := List.mem_iff_getElem.mp hmem_u
  obtain ⟨j, hj, heq_v⟩ := List.mem_iff_getElem.mp hmem_v
  have hle : ∀ C ∈ blocks, C.lo ≤ C.hi := fun C hC => (hPart.1 C hC).2.1
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · rw [← heq_u, ← heq_v]
    exact consecutiveBlocks_lt blocks hle hPart.2.1 i j hi hj hlt
  · exfalso; exact hne (heq_u.symm.trans heq_v)
  · exfalso
    have hgt_b := consecutiveBlocks_lt blocks hle hPart.2.1 j i hj hi hgt
    rw [heq_u] at hgt_b
    rw [heq_v] at hgt_b
    have hu_lo := (blockAt_mem_and_bounds hPart hu1 (by omega)).2.1
    have hv_hi := (blockAt_mem_and_bounds hPart (by omega) hvP).2.2.1
    omega

private theorem blockAt_convex {P : ℕ} {blocks : List IntervalBlock}
    (hPart : IsContiguousBlockPartition P blocks) {a b c : ℕ}
    (ha1 : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcP : c ≤ P) :
    blockAt blocks a = blockAt blocks c ↔
      (blockAt blocks a = blockAt blocks b ∧ blockAt blocks b = blockAt blocks c) := by
  constructor
  · intro heq
    obtain ⟨hmem_a, ha_lo, _, _⟩ := blockAt_mem_and_bounds hPart (u := a) ha1 (by omega)
    obtain ⟨_, _, hc_hi, _⟩ := blockAt_mem_and_bounds hPart (u := c) (by omega) hcP
    obtain ⟨_, _, _, huniq_b⟩ := blockAt_mem_and_bounds hPart (u := b) (by omega) (by omega)
    rw [← heq] at hc_hi
    have hab_eq : blockAt blocks a = blockAt blocks b :=
      (huniq_b (blockAt blocks a) hmem_a).mpr ⟨by omega, by omega⟩
    exact ⟨hab_eq, hab_eq.symm.trans heq⟩
  · rintro ⟨h1, h2⟩; exact h1.trans h2

private theorem nestedChain_refine_bounds {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hle : k₁ ≤ k₂) {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) :
    (blockAt (chain k₁) u).lo ≤ (blockAt (chain k₂) u).lo ∧
    (blockAt (chain k₂) u).hi ≤ (blockAt (chain k₁) u).hi := by
  rcases k₁ with ⟨v₁, hv₁⟩
  rcases k₂ with ⟨v₂, hv₂⟩
  change v₁ ≤ v₂ at hle
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero =>
    have heq : (⟨v₁, hv₁⟩ : Fin (M + 1)) = ⟨v₁ + 0, hv₂⟩ := Fin.ext (by simp)
    rw [heq]; exact ⟨le_rfl, le_rfl⟩
  | succ d ih =>
    have hvd : v₁ + d < M := by omega
    have hvd1 : v₁ + d < M + 1 := by omega
    obtain ⟨ih_lo, ih_hi⟩ := ih hvd1
    set fk : Fin M := ⟨v₁ + d, hvd⟩
    have hfk_succ : fk.succ = ⟨v₁ + (d + 1), hv₂⟩ := Fin.ext (by simp [fk]; omega)
    have hfk_cast : fk.castSucc = ⟨v₁ + d, hvd1⟩ := Fin.ext rfl
    obtain ⟨hY_mem, hY_lo, hY_hi, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 fk.succ) hu1 huP
    obtain ⟨X, hX_mem, hX_lo, hX_hi⟩ := hChain.2.2.2 fk (blockAt (chain fk.succ) u) hY_mem
    obtain ⟨_, _, _, huniq⟩ := blockAt_mem_and_bounds (hChain.2.2.1 fk.castSucc) hu1 huP
    have hX_eq : X = blockAt (chain fk.castSucc) u :=
      (huniq X hX_mem).mpr ⟨by omega, by omega⟩
    subst hX_eq
    rw [hfk_succ] at hX_lo hX_hi
    rw [hfk_cast] at hX_lo hX_hi
    exact ⟨le_trans ih_lo hX_lo, le_trans hX_hi ih_hi⟩

private theorem nestedChain_blockAt_coarse_of_fine {M P : ℕ}
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hle : k₁ ≤ k₂) {u v : ℕ}
    (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P)
    (hfine : blockAt (chain k₂) u = blockAt (chain k₂) v) :
    blockAt (chain k₁) u = blockAt (chain k₁) v := by
  obtain ⟨hlo_u, hhi_u⟩ := nestedChain_refine_bounds hChain hle hu1 huP
  obtain ⟨hmem_u1, _, _, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 k₁) hu1 huP
  obtain ⟨_, hv_lo2, hv_hi2, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 k₂) hv1 hvP
  obtain ⟨_, _, _, huniq_v1⟩ := blockAt_mem_and_bounds (hChain.2.2.1 k₁) hv1 hvP
  rw [← hfine] at hv_lo2 hv_hi2
  exact (huniq_v1 (blockAt (chain k₁) u) hmem_u1).mpr ⟨by omega, by omega⟩

private theorem blockAt_enclosing_eq {M P : ℕ}
    {chain : Fin (M + 1) → List IntervalBlock} (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hle : k₁ ≤ k₂) {u : ℕ} (hu1 : 1 ≤ u) (huP : u ≤ P) :
    blockAt (chain k₁) u = blockAt (chain k₁) (blockAt (chain k₂) u).lo := by
  obtain ⟨hmem2, hlo2, _, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 k₂) hu1 huP
  have hQ_bounds := (hChain.2.2.1 k₂).1 (blockAt (chain k₂) u) hmem2
  have hfine : blockAt (chain k₂) u = blockAt (chain k₂) (blockAt (chain k₂) u).lo := by
    obtain ⟨_, _, _, huniq⟩ :=
      blockAt_mem_and_bounds (hChain.2.2.1 k₂) hQ_bounds.1 (by omega)
    exact (huniq (blockAt (chain k₂) u) hmem2).mpr ⟨le_rfl, hQ_bounds.2.1⟩
  exact nestedChain_blockAt_coarse_of_fine hChain hle hu1 huP hQ_bounds.1 (by omega) hfine

private theorem partSepScale_range {M P : ℕ} (chain : Fin (M + 1) → List IntervalBlock)
    (u v : ℕ) (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P) :
    1 ≤ partSepScale P chain u v ∧ partSepScale P chain u v ≤ M + 1 := by
  unfold partSepScale
  have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
  simp only [hcond, ↓reduceIte]
  split
  · next ℓ _ => exact ⟨by omega, by omega⟩
  · exact ⟨by omega, le_rfl⟩

private theorem lt_partSepScale_iff {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    (u v : ℕ) (hu1 : 1 ≤ u) (huP : u ≤ P) (hv1 : 1 ≤ v) (hvP : v ≤ P)
    (k : Fin (M + 1)) :
    k.val < partSepScale P chain u v ↔ blockAt (chain k) u = blockAt (chain k) v := by
  rcases k with ⟨m, hm⟩
  cases m with
  | zero =>
    have hpos := (partSepScale_range chain u v hu1 huP hv1 hvP).1
    have h0 : chain 0 = [⟨1, P⟩] := hChain.2.1
    have heq0 : (⟨0, hm⟩ : Fin (M + 1)) = 0 := rfl
    rw [heq0]
    obtain ⟨hmem_u, _, _, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 0) (u := u) hu1 huP
    obtain ⟨hmem_v, _, _, _⟩ := blockAt_mem_and_bounds (hChain.2.2.1 0) (u := v) hv1 hvP
    rw [h0, List.mem_singleton] at hmem_u hmem_v
    rw [h0]
    simp only [Fin.val_zero]
    exact ⟨fun _ => hmem_u.trans hmem_v.symm, fun _ => by omega⟩
  | succ idx =>
    have hidx : idx < M := by omega
    let fidx : Fin M := ⟨idx, hidx⟩
    have hfsucc : fidx.succ = ⟨idx + 1, hm⟩ := rfl
    rw [← hfsucc]
    unfold partSepScale
    have hcond : ¬ (P < u ∨ P < v ∨ u = 0 ∨ v = 0) := by omega
    simp only [hcond, ↓reduceIte]
    split
    · next ℓ₀ hfind =>
      constructor
      · intro hlt
        have hlt_idx : idx < ℓ₀.val := by
          change idx + 1 < ℓ₀.val + 1 at hlt
          omega
        rw [List.find?_eq_some_iff_append] at hfind
        obtain ⟨_, xs, bs, hxs, hbefore⟩ := hfind
        have hlen_tot : (xs ++ ℓ₀ :: bs).length = M := by
          rw [← hxs, List.length_finRange]
        have hxs_lt : xs.length < M := by simp at hlen_tot; omega
        have hxs_lt_fr : xs.length < (List.finRange M).length := by simp [hxs_lt]
        have hget_ℓ₀ : (List.finRange M)[xs.length]'hxs_lt_fr = ℓ₀ := by
          simp [hxs]
        rw [List.getElem_finRange] at hget_ℓ₀
        have hxs_len : xs.length = ℓ₀.val := congrArg Fin.val hget_ℓ₀
        have hfidx_lt : idx < xs.length := by omega
        have hfidx_lt_fr : idx < (List.finRange M).length := by simp [hidx]
        have hget_fidx : (List.finRange M)[idx]'hfidx_lt_fr = xs[idx]'hfidx_lt := by
          simp [hxs, List.getElem_append_left hfidx_lt]
        rw [List.getElem_finRange] at hget_fidx
        have hmem_xs : fidx ∈ xs := by
          have hfidx_eq : xs[idx]'hfidx_lt = fidx :=
            Fin.ext (congrArg Fin.val hget_fidx).symm
          rw [← hfidx_eq]
          exact List.getElem_mem hfidx_lt
        have hfalse := hbefore fidx hmem_xs
        simpa using hfalse
      · intro heq
        have hp₀ : blockAt (chain ℓ₀.succ) u ≠ blockAt (chain ℓ₀.succ) v := by
          have hp := List.find?_some hfind
          simpa using hp
        by_contra hge
        have hle_fin : ℓ₀.succ ≤ fidx.succ := by
          change ¬ (idx + 1 < ℓ₀.val + 1) at hge
          change ℓ₀.val + 1 ≤ idx + 1
          omega
        exact hp₀ (nestedChain_blockAt_coarse_of_fine hChain hle_fin hu1 huP hv1 hvP heq)
    · next hfind =>
      constructor
      · intro _
        have hnone := List.find?_eq_none.mp hfind fidx (List.mem_finRange fidx)
        simpa using hnone
      · intro _
        change idx + 1 < M + 1
        omega

private theorem partSepScale_ultrametric {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {a b c : ℕ} (ha1 : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcP : c ≤ P) :
    partSepScale P chain a c = min (partSepScale P chain a b) (partSepScale P chain b c) := by
  have h1 := (partSepScale_range chain a c ha1 (by omega) (by omega) hcP).2
  have h2 := (partSepScale_range chain a b ha1 (by omega) (by omega) (by omega)).2
  have h3 := (partSepScale_range chain b c (by omega) (by omega) (by omega) hcP).2
  suffices hiff : ∀ m : ℕ, m ≤ M →
      (m < partSepScale P chain a c ↔
        m < min (partSepScale P chain a b) (partSepScale P chain b c)) by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := (hiff (partSepScale P chain a c) (by omega)).mpr hlt
      omega
    · have hm := (hiff (min (partSepScale P chain a b) (partSepScale P chain b c)) (by omega)).mp hgt
      omega
  intro m hm
  let k : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  rw [lt_min_iff]
  change k.val < partSepScale P chain a c ↔
    (k.val < partSepScale P chain a b ∧ k.val < partSepScale P chain b c)
  rw [lt_partSepScale_iff hChain a c ha1 (by omega) (by omega) hcP k,
      lt_partSepScale_iff hChain a b ha1 (by omega) (by omega) (by omega) k,
      lt_partSepScale_iff hChain b c (by omega) (by omega) (by omega) hcP k]
  exact blockAt_convex (hChain.2.2.1 k) ha1 hab hbc hcP


/-!
## 3. ScaleTree Addresses, `lcaScaleTree` Routing, and `scaleTreePartitionChain`
-/

private theorem subtreeAtAddr_append :
    ∀ (ξ₁ : List ℕ) (T : ScaleTree) (ξ₂ : List ℕ),
      subtreeAtAddr T (ξ₁ ++ ξ₂) = (subtreeAtAddr T ξ₁).bind (fun sub => subtreeAtAddr sub ξ₂)
  | [], T, ξ₂ => by simp [subtreeAtAddr]
  | c :: rest, .leaf _, ξ₂ => by simp [subtreeAtAddr]
  | c :: rest, .internal cs, ξ₂ => by
    simp only [List.cons_append, subtreeAtAddr]
    split
    · rfl
    · cases cs[c - 1]? with
      | none => rfl
      | some child => exact subtreeAtAddr_append rest child ξ₂

private theorem mem_leafEntriesChildren_iff :
    ∀ (cs : List ScaleTree) (c₀ s : ℕ) (addr : List ℕ),
      (s, addr) ∈ ScaleTree.leafEntriesChildren c₀ cs ↔
        ∃ (idx : ℕ) (hidx : idx < cs.length) (rest : List ℕ),
          addr = (c₀ + idx) :: rest ∧ (s, rest) ∈ cs[idx].leafEntries
  | [], _, _, _ => by simp [ScaleTree.leafEntriesChildren]
  | child :: restCs, c₀, s, addr => by
    simp only [ScaleTree.leafEntriesChildren, List.mem_append, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro (⟨⟨s', r⟩, hmem, rfl, rfl⟩ | htail)
      · exact ⟨0, by simp, r, by simp, hmem⟩
      · obtain ⟨idx, hidx, r, rfl, hmem⟩ :=
          (mem_leafEntriesChildren_iff restCs (c₀ + 1) s addr).mp htail
        refine ⟨idx + 1, Nat.succ_lt_succ hidx, r, ?_, by simpa using hmem⟩
        simp [Nat.add_assoc, Nat.add_comm 1 idx]
    · rintro ⟨idx, hidx, r, rfl, hmem⟩
      cases idx with
      | zero =>
        left
        exact ⟨(s, r), hmem, rfl, by simp⟩
      | succ idx' =>
        right
        rw [mem_leafEntriesChildren_iff]
        refine ⟨idx', Nat.lt_of_succ_lt_succ hidx, r, ?_, by simpa using hmem⟩
        simp [Nat.add_assoc, Nat.add_comm 1 idx']

private theorem mem_internalAddrChildren_iff :
    ∀ (cs : List ScaleTree) (c₀ : ℕ) (ν : List ℕ),
      ν ∈ ScaleTree.internalAddrChildren c₀ cs ↔
        ∃ (idx : ℕ) (hidx : idx < cs.length) (rest : List ℕ),
          ν = (c₀ + idx) :: rest ∧ rest ∈ cs[idx].internalAddrList
  | [], _, _ => by simp [ScaleTree.internalAddrChildren]
  | child :: restCs, c₀, ν => by
    simp only [ScaleTree.internalAddrChildren, List.mem_append, List.mem_map]
    constructor
    · rintro (⟨r, hmem, rfl⟩ | htail)
      · exact ⟨0, by simp, r, by simp, hmem⟩
      · obtain ⟨idx, hidx, r, rfl, hmem⟩ :=
          (mem_internalAddrChildren_iff restCs (c₀ + 1) ν).mp htail
        refine ⟨idx + 1, Nat.succ_lt_succ hidx, r, ?_, by simpa using hmem⟩
        simp [Nat.add_assoc, Nat.add_comm 1 idx]
    · rintro ⟨idx, hidx, r, rfl, hmem⟩
      cases idx with
      | zero =>
        left
        exact ⟨r, hmem, by simp⟩
      | succ idx' =>
        right
        rw [mem_internalAddrChildren_iff]
        refine ⟨idx', Nat.lt_of_succ_lt_succ hidx, r, ?_, by simpa using hmem⟩
        simp [Nat.add_assoc, Nat.add_comm 1 idx']

private theorem mem_leafEntries_iff_subtreeAtAddr :
    ∀ (addr : List ℕ) (T : ScaleTree) (s : ℕ),
      (s, addr) ∈ T.leafEntries ↔ subtreeAtAddr T addr = some (.leaf s)
  | [], .leaf s', s => by
    simp [ScaleTree.leafEntries, subtreeAtAddr, eq_comm]
  | [], .internal cs, s => by
    simp only [ScaleTree.leafEntries, subtreeAtAddr, Option.some.injEq, reduceCtorEq, iff_false]
    rw [mem_leafEntriesChildren_iff]
    rintro ⟨idx, _, r, h, _⟩
    cases h
  | c :: rest, .leaf s', s => by
    simp [ScaleTree.leafEntries, subtreeAtAddr]
  | c :: rest, .internal cs, s => by
    simp only [ScaleTree.leafEntries, mem_leafEntriesChildren_iff, subtreeAtAddr]
    by_cases hc0 : c = 0
    · subst hc0
      simp only [↓reduceIte, reduceCtorEq, iff_false]
      rintro ⟨idx, _, _, h, _⟩
      simp only [List.cons.injEq] at h
      omega
    · simp only [hc0, ↓reduceIte]
      constructor
      · rintro ⟨idx, hidx, r, hcons, hmem⟩
        simp only [List.cons.injEq] at hcons
        rcases hcons with ⟨hc_eq, rfl⟩
        have hidx_eq : idx = c - 1 := by omega
        subst hidx_eq
        rw [List.getElem?_eq_getElem hidx]
        exact (mem_leafEntries_iff_subtreeAtAddr rest cs[c - 1] s).mp hmem
      · intro hsub
        rcases hget : cs[c - 1]? with _ | child
        · rw [hget] at hsub; cases hsub
        · rw [hget] at hsub
          obtain ⟨hidx, rfl⟩ := List.getElem?_eq_some_iff.mp hget
          refine ⟨c - 1, hidx, rest, ?_, (mem_leafEntries_iff_subtreeAtAddr rest cs[c - 1] s).mpr hsub⟩
          simp [show 1 + (c - 1) = c by omega]

private theorem mem_internalAddrList_iff_subtreeAtAddr :
    ∀ (ν : List ℕ) (T : ScaleTree),
      ν ∈ T.internalAddrList ↔ ∃ cs, subtreeAtAddr T ν = some (.internal cs)
  | [], .leaf _ => by simp [ScaleTree.internalAddrList, subtreeAtAddr]
  | [], .internal cs => by simp [ScaleTree.internalAddrList, subtreeAtAddr]
  | c :: rest, .leaf _ => by simp [ScaleTree.internalAddrList, subtreeAtAddr]
  | c :: rest, .internal cs => by
    simp only [ScaleTree.internalAddrList, List.mem_cons, reduceCtorEq, false_or,
      mem_internalAddrChildren_iff, subtreeAtAddr]
    by_cases hc0 : c = 0
    · subst hc0
      simp only [↓reduceIte, reduceCtorEq, exists_false, iff_false]
      rintro ⟨idx, _, _, h, _⟩
      simp only [List.cons.injEq] at h
      omega
    · simp only [hc0, ↓reduceIte]
      constructor
      · rintro ⟨idx, hidx, r, hcons, hmem⟩
        simp only [List.cons.injEq] at hcons
        rcases hcons with ⟨hc_eq, rfl⟩
        have hidx_eq : idx = c - 1 := by omega
        subst hidx_eq
        rw [List.getElem?_eq_getElem hidx]
        exact (mem_internalAddrList_iff_subtreeAtAddr rest cs[c - 1]).mp hmem
      · rintro ⟨cs', hsub⟩
        rcases hget : cs[c - 1]? with _ | child
        · rw [hget] at hsub; cases hsub
        · rw [hget] at hsub
          obtain ⟨hidx, rfl⟩ := List.getElem?_eq_some_iff.mp hget
          refine ⟨c - 1, hidx, rest, ?_,
            (mem_internalAddrList_iff_subtreeAtAddr rest cs[c - 1]).mpr ⟨cs', hsub⟩⟩
          simp [show 1 + (c - 1) = c by omega]

private theorem leafEntriesChildren_split :
    ∀ (cs : List ScaleTree) (c₀ idx : ℕ) (hidx : idx < cs.length),
      ∃ pre suf,
        ScaleTree.leafEntriesChildren c₀ cs =
          pre ++ cs[idx].leafEntries.map (fun p => (p.1, (c₀ + idx) :: p.2)) ++ suf
  | [], _, _, hidx => by simp at hidx
  | child :: rest, c₀, 0, _ => by
    refine ⟨[], ScaleTree.leafEntriesChildren (c₀ + 1) rest, ?_⟩
    simp [ScaleTree.leafEntriesChildren]
  | child :: rest, c₀, idx + 1, hidx => by
    obtain ⟨pre', suf', heq⟩ :=
      leafEntriesChildren_split rest (c₀ + 1) idx (Nat.lt_of_succ_lt_succ hidx)
    refine ⟨child.leafEntries.map (fun p => (p.1, c₀ :: p.2)) ++ pre', suf', ?_⟩
    simp only [ScaleTree.leafEntriesChildren, List.getElem_cons_succ]
    have hfun : (fun (s, r) => (s, c₀ :: r)) = (fun p : ℕ × List ℕ => (p.1, c₀ :: p.2)) := rfl
    have hadd : c₀ + 1 + idx = c₀ + (idx + 1) := by omega
    rw [hfun, heq, hadd]
    simp [List.append_assoc]

private theorem leafEntries_sub_infix :
    ∀ (ξ : List ℕ) (T sub : ScaleTree),
      subtreeAtAddr T ξ = some sub →
      ∃ pre suf, T.leafEntries = pre ++ sub.leafEntries.map (fun p => (p.1, ξ ++ p.2)) ++ suf
  | [], T, sub, hsub => by
    simp only [subtreeAtAddr, Option.some.injEq] at hsub
    subst hsub
    refine ⟨[], [], ?_⟩
    simp
  | c :: rest, .leaf _, _, hsub => by simp [subtreeAtAddr] at hsub
  | c :: rest, .internal cs, sub, hsub => by
    simp only [subtreeAtAddr] at hsub
    split at hsub
    · cases hsub
    · next hc0 =>
      rcases hget : cs[c - 1]? with _ | child
      · rw [hget] at hsub; cases hsub
      · rw [hget] at hsub
        obtain ⟨hidx, rfl⟩ := List.getElem?_eq_some_iff.mp hget
        obtain ⟨pre₀, suf₀, hsplit₀⟩ := leafEntriesChildren_split cs 1 (c - 1) hidx
        obtain ⟨pre₁, suf₁, hsplit₁⟩ := leafEntries_sub_infix rest cs[c - 1] sub hsub
        have hc_eq : 1 + (c - 1) = c := by omega
        rw [hc_eq] at hsplit₀
        refine ⟨pre₀ ++ pre₁.map (fun p => (p.1, c :: p.2)),
          suf₁.map (fun p => (p.1, c :: p.2)) ++ suf₀, ?_⟩
        simp only [ScaleTree.leafEntries]
        rw [hsplit₀, hsplit₁]
        simp [List.map_append, List.map_map, List.append_assoc]

private theorem leaves_sub_infix {ξ : List ℕ} {T sub : ScaleTree}
    (hsub : subtreeAtAddr T ξ = some sub) :
    ∃ pre suf, T.leaves = pre ++ sub.leaves ++ suf := by
  obtain ⟨pre, suf, heq⟩ := leafEntries_sub_infix ξ T sub hsub
  refine ⟨pre.map Prod.fst, suf.map Prod.fst, ?_⟩
  unfold ScaleTree.leaves
  rw [heq]
  simp only [List.map_append, List.map_map]
  have hcomp : (Prod.fst ∘ fun p : ℕ × List ℕ => (p.1, ξ ++ p.2)) = Prod.fst := rfl
  rw [hcomp]

private theorem allInternalNonempty_of_subtreeAtAddr :
    ∀ (ξ : List ℕ) (T sub : ScaleTree),
      T.AllInternalNonempty → subtreeAtAddr T ξ = some sub → sub.AllInternalNonempty
  | [], T, sub, hall, hsub => by
    simp only [subtreeAtAddr, Option.some.injEq] at hsub
    rwa [← hsub]
  | _ :: _, .leaf _, _, _, hsub => by simp [subtreeAtAddr] at hsub
  | c :: rest, .internal cs, sub, hall, hsub => by
    unfold ScaleTree.AllInternalNonempty at hall
    simp only [subtreeAtAddr] at hsub
    split at hsub
    · cases hsub
    · rcases hget : cs[c - 1]? with _ | child
      · rw [hget] at hsub; cases hsub
      · rw [hget] at hsub
        exact allInternalNonempty_of_subtreeAtAddr rest child sub
          (hall.2 child (List.mem_of_getElem? hget)) hsub

private theorem leaves_ne_nil_of_allInternalNonempty :
    ∀ (T : ScaleTree), T.AllInternalNonempty → T.leaves ≠ []
  | .leaf s, _ => by simp [ScaleTree.leaves, ScaleTree.leafEntries]
  | .internal [], hall => by
    unfold ScaleTree.AllInternalNonempty at hall
    exact absurd rfl hall.1
  | .internal (child :: cs), hall => by
    unfold ScaleTree.AllInternalNonempty at hall
    have hc : child.leaves ≠ [] :=
      leaves_ne_nil_of_allInternalNonempty child (hall.2 child List.mem_cons_self)
    intro hemp
    simp only [ScaleTree.leaves, ScaleTree.leafEntries, ScaleTree.leafEntriesChildren,
      List.map_append, List.append_eq_nil_iff] at hemp
    have h1 := hemp.1
    rw [List.map_map] at h1
    have hcomp : (Prod.fst ∘ fun x : ℕ × List ℕ => (x.1, 1 :: x.2)) = Prod.fst := rfl
    rw [hcomp] at h1
    exact hc h1

private theorem getLast?_range' (a : ℕ) :
    ∀ (k : ℕ), (List.range' a (k + 1)).getLast? = some (a + k)
  | 0 => by simp
  | k + 1 => by
    rw [List.range'_succ, List.range'_succ, List.getLast?_cons_cons, ← List.range'_succ,
      getLast?_range' (a + 1) k]
    congr 1; omega

private theorem range'_split_mid {a N : ℕ} {pre mid suf : List ℕ}
    (heq : List.range' a N = pre ++ mid ++ suf) :
    mid = List.range' (a + pre.length) mid.length ∧
    pre.length + mid.length + suf.length = N := by
  have hlen : N = (pre ++ mid).length + suf.length := by
    have := congrArg List.length heq
    simp only [List.length_range', List.length_append] at this ⊢
    omega
  have h1 : List.range' a (pre ++ mid).length = pre ++ mid := by
    rw [hlen, ← List.range'_append] at heq
    exact (List.append_inj heq (by simp)).1
  have hlen2 : (pre ++ mid).length = pre.length + mid.length := List.length_append
  rw [hlen2, ← List.range'_append] at h1
  have h2 := (List.append_inj h1 (by simp)).2
  simp only [Nat.one_mul] at h2
  exact ⟨h2.symm, by simp only [List.length_append] at hlen; omega⟩

private theorem subtree_range_props {r M : ℕ} {T sub : ScaleTree} {ξ : List ℕ}
    (hScale : IsScaleTree r M T) (hsub : subtreeAtAddr T ξ = some sub) :
    ∃ a k : ℕ,
      sub.leaves = List.range' a (k + 1) ∧
      mStart T ξ = a ∧
      mEnd T ξ = a + k ∧
      1 ≤ a ∧ a + k ≤ M ∧
      (∀ s : ℕ, s ∈ sub.leaves ↔ mStart T ξ ≤ s ∧ s ≤ mEnd T ξ) := by
  obtain ⟨pre, suf, hinfix⟩ := leaves_sub_infix hsub
  rw [hScale.2.2.2.1] at hinfix
  obtain ⟨hmid, hsum⟩ := range'_split_mid hinfix
  have hne : sub.leaves ≠ [] :=
    leaves_ne_nil_of_allInternalNonempty sub
      (allInternalNonempty_of_subtreeAtAddr ξ T sub hScale.2.2.1 hsub)
  have hpos : 0 < sub.leaves.length := List.length_pos_iff.mpr hne
  set k := sub.leaves.length - 1
  have hlen_eq : sub.leaves.length = k + 1 := by omega
  rw [hlen_eq] at hmid
  set a := 1 + pre.length
  have hmStart : mStart T ξ = a := by
    unfold mStart
    rw [hsub]
    dsimp only
    rw [hmid, List.range'_succ]
    rfl
  have hmEnd : mEnd T ξ = a + k := by
    unfold mEnd
    rw [hsub]
    dsimp only
    rw [hmid, getLast?_range' a k]
    rfl
  refine ⟨a, k, hmid, hmStart, hmEnd, by omega, by omega, ?_⟩
  intro s
  rw [hmid, hmStart, hmEnd, List.mem_range'_1]
  omega

private theorem eq_of_mem_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {xs : List α}, (xs.map f).Nodup → ∀ {x y : α}, x ∈ xs → y ∈ xs → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by cases hx
  | z :: zs, hnd, x, y, hx, hy, hfeq => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hxzs <;>
      rcases List.mem_cons.mp hy with rfl | hyzs
    · rfl
    · exfalso; exact hnd.1 (hfeq ▸ List.mem_map_of_mem hyzs)
    · exfalso; exact hnd.1 (hfeq.symm ▸ List.mem_map_of_mem hxzs)
    · exact eq_of_mem_of_nodup_map hnd.2 hxzs hyzs hfeq

private theorem leafAddr_props {r M : ℕ} {T : ScaleTree} (hScale : IsScaleTree r M T)
    {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓM : ℓ ≤ M) :
    (ℓ, leafAddr T ℓ) ∈ T.leafEntries ∧
    subtreeAtAddr T (leafAddr T ℓ) = some (.leaf ℓ) ∧
    1 ≤ (leafAddr T ℓ).length ∧ (leafAddr T ℓ).length ≤ r := by
  have hmem_leaves : ℓ ∈ T.leaves := by
    rw [hScale.2.2.2.1, List.mem_range'_1]
    omega
  obtain ⟨⟨s₀, addr₀⟩, hmem₀, hs₀⟩ := List.mem_map.mp hmem_leaves
  dsimp at hs₀
  subst s₀
  unfold leafAddr
  split
  · next s₁ addr₁ hfind =>
    have hmem₁ : (s₁, addr₁) ∈ T.leafEntries := List.mem_of_find?_eq_some hfind
    have hs₁ : s₁ = ℓ := by
      have hp := List.find?_some hfind
      simpa using hp
    subst s₁
    exact ⟨hmem₁, (mem_leafEntries_iff_subtreeAtAddr addr₁ T ℓ).mp hmem₁,
      hScale.2.2.2.2 (ℓ, addr₁) hmem₁⟩
  · next hfind =>
    exfalso
    have hnone := List.find?_eq_none.mp hfind (ℓ, addr₀) hmem₀
    simp at hnone

private theorem prefix_leafAddr_iff_mem_range {r M : ℕ} {T sub : ScaleTree} {ξ : List ℕ}
    (hScale : IsScaleTree r M T) (hsub : subtreeAtAddr T ξ = some sub)
    {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓM : ℓ ≤ M) :
    ξ <+: leafAddr T ℓ ↔ mStart T ξ ≤ ℓ ∧ ℓ ≤ mEnd T ξ := by
  obtain ⟨_, _, _, _, _, _, _, hrange_iff⟩ := subtree_range_props hScale hsub
  obtain ⟨hmem_ℓ, hsub_ℓ, _, _⟩ := leafAddr_props hScale hℓ1 hℓM
  rw [← hrange_iff]
  constructor
  · rintro ⟨rest, hpref⟩
    rw [← hpref, subtreeAtAddr_append, hsub] at hsub_ℓ
    dsimp only [Option.bind] at hsub_ℓ
    have hmem_sub := (mem_leafEntries_iff_subtreeAtAddr rest sub ℓ).mpr hsub_ℓ
    exact List.mem_map_of_mem (f := Prod.fst) hmem_sub
  · intro hmem_sub_leaves
    obtain ⟨⟨s', rest⟩, hmem_sub, hs'⟩ := List.mem_map.mp hmem_sub_leaves
    dsimp at hs'
    subst s'
    have hsub_rest := (mem_leafEntries_iff_subtreeAtAddr rest sub ℓ).mp hmem_sub
    have hsub_tot : subtreeAtAddr T (ξ ++ rest) = some (.leaf ℓ) := by
      rw [subtreeAtAddr_append, hsub]
      exact hsub_rest
    have hmem_tot := (mem_leafEntries_iff_subtreeAtAddr (ξ ++ rest) T ℓ).mpr hsub_tot
    have hnd : (T.leafEntries.map Prod.fst).Nodup := by
      change T.leaves.Nodup
      rw [hScale.2.2.2.1]
      exact List.nodup_range'
    have heq := eq_of_mem_of_nodup_map hnd hmem_tot hmem_ℓ rfl
    injection heq with _ haddr_eq
    exact ⟨rest, haddr_eq⟩

private theorem lcp_prefix_left {α : Type} [DecidableEq α] :
    ∀ (as bs : List α), longestCommonPrefix as bs <+: as
  | [], _ => List.nil_prefix
  | _ :: _, [] => List.nil_prefix
  | a :: as, b :: bs => by
    unfold longestCommonPrefix
    split
    · exact List.cons_prefix_cons.mpr ⟨rfl, lcp_prefix_left as bs⟩
    · exact List.nil_prefix

private theorem prefix_lcp_of_prefix {α : Type} [DecidableEq α] :
    ∀ {p as bs : List α}, p <+: as → p <+: bs → p <+: longestCommonPrefix as bs
  | [], _, _, _, _ => List.nil_prefix
  | x :: xs, [], _, h1, _ => by cases List.prefix_nil.mp h1
  | x :: xs, _, [], _, h2 => by cases List.prefix_nil.mp h2
  | x :: xs, a :: as, b :: bs, h1, h2 => by
    obtain ⟨rfl, h1'⟩ := List.cons_prefix_cons.mp h1
    obtain ⟨hxb, h2'⟩ := List.cons_prefix_cons.mp h2
    subst hxb
    simp only [longestCommonPrefix, ↓reduceIte]
    exact List.cons_prefix_cons.mpr ⟨rfl, prefix_lcp_of_prefix h1' h2'⟩

private theorem lcp_diverge :
    ∀ {as bs : List ℕ}, ¬ (as <+: bs) → ¬ (bs <+: as) →
      ∃ cA rA cB rB,
        as = longestCommonPrefix as bs ++ (cA :: rA) ∧
        bs = longestCommonPrefix as bs ++ (cB :: rB) ∧
        cA ≠ cB
  | [], bs, h1, _ => absurd List.nil_prefix h1
  | as, [], _, h2 => absurd List.nil_prefix h2
  | a :: as, b :: bs, h1, h2 => by
    unfold longestCommonPrefix
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte, List.cons_append]
      have h1' : ¬ (as <+: bs) := fun h => h1 (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      have h2' : ¬ (bs <+: as) := fun h => h2 (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      obtain ⟨cA, rA, cB, rB, has, hbs, hne⟩ := lcp_diverge h1' h2'
      exact ⟨cA, rA, cB, rB, congrArg (a :: ·) has, congrArg (a :: ·) hbs, hne⟩
    · simp only [hab, ↓reduceIte, List.nil_append]
      exact ⟨a, as, b, bs, rfl, rfl, hab⟩

private theorem leafEntriesChildren_head_ge :
    ∀ (cs : List ScaleTree) (c₀ s c : ℕ) (r : List ℕ),
      (s, c :: r) ∈ ScaleTree.leafEntriesChildren c₀ cs → c₀ ≤ c
  | [], _, _, _, _, h => by simp [ScaleTree.leafEntriesChildren] at h
  | child :: rest, c₀, s, c, r, h => by
    simp only [ScaleTree.leafEntriesChildren, List.mem_append, List.mem_map, Prod.mk.injEq,
      List.cons.injEq] at h
    rcases h with ⟨⟨_, _⟩, _, _, ⟨rfl, _⟩⟩ | htail
    · exact le_rfl
    · exact le_trans (by omega) (leafEntriesChildren_head_ge rest (c₀ + 1) s c r htail)

private theorem leafEntriesChildren_order :
    ∀ (cs : List ScaleTree) (c₀ : ℕ),
      ((ScaleTree.leafEntriesChildren c₀ cs).map Prod.fst).Pairwise (· < ·) →
      ∀ {sA cA : ℕ} {rA : List ℕ} {sB cB : ℕ} {rB : List ℕ},
        (sA, cA :: rA) ∈ ScaleTree.leafEntriesChildren c₀ cs →
        (sB, cB :: rB) ∈ ScaleTree.leafEntriesChildren c₀ cs →
        cA < cB → sA < sB
  | [], _, _, _, _, _, _, _, _, hA, _, _ => by simp [ScaleTree.leafEntriesChildren] at hA
  | child :: rest, c₀, hpw, sA, cA, rA, sB, cB, rB, hA, hB, hlt => by
    simp only [ScaleTree.leafEntriesChildren, List.map_append, List.pairwise_append] at hpw
    simp only [ScaleTree.leafEntriesChildren, List.mem_append] at hA hB
    rcases hA with hA1 | hA2 <;> rcases hB with hB1 | hB2
    · simp only [List.mem_map, Prod.mk.injEq, List.cons.injEq] at hA1 hB1
      rcases hA1 with ⟨_, _, _, rfl, _⟩
      rcases hB1 with ⟨_, _, _, rfl, _⟩
      omega
    · exact hpw.2.2 sA (List.mem_map_of_mem hA1) sB (List.mem_map_of_mem hB2)
    · exfalso
      simp only [List.mem_map, Prod.mk.injEq, List.cons.injEq] at hB1
      rcases hB1 with ⟨_, _, _, rfl, _⟩
      have hge := leafEntriesChildren_head_ge rest (c₀ + 1) sA cA rA hA2
      omega
    · exact leafEntriesChildren_order rest (c₀ + 1) hpw.2.1 hA2 hB2 hlt

private theorem pairwise_lt_range' : ∀ (a n : ℕ), (List.range' a n).Pairwise (· < ·)
  | _, 0 => List.Pairwise.nil
  | a, n + 1 => by
    rw [List.range'_succ, List.pairwise_cons]
    refine ⟨?_, pairwise_lt_range' (a + 1) n⟩
    intro x hx
    rw [List.mem_range'] at hx
    omega

private theorem lcaScaleTree_routing {r M : ℕ} {T : ScaleTree} (hScale : IsScaleTree r M T)
    {ℓ₂ ℓ₁ : ℕ} (hℓ₂1 : 1 ≤ ℓ₂) (hlt : ℓ₂ < ℓ₁) (hℓ₁M : ℓ₁ ≤ M) :
    let ν := lcaScaleTree T ℓ₂ ℓ₁
    let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 1
    let mPrev := mStart T (ν ++ [c₂]) - 1
    let mMid := mEnd T (ν ++ [c₂])
    let mNu := mEnd T ν
    ν ∈ internalAddrs T ∧
    ν.length < r ∧
    1 ≤ c₂ ∧ c₂ ≤ numChildren T ν ∧
    mPrev < ℓ₂ ∧ ℓ₂ ≤ mMid ∧ mMid < ℓ₁ ∧ ℓ₁ ≤ mNu ∧ mNu ≤ M ∧
    (∀ ℓ₂' ℓ₁' : ℕ, mPrev < ℓ₂' → ℓ₂' < ℓ₁' → ℓ₁' ≤ mMid →
      ν.length < (lcaScaleTree T ℓ₂' ℓ₁').length) := by
  obtain ⟨_, hsub₂, _, hlen₂_r⟩ := leafAddr_props hScale hℓ₂1 (by omega)
  obtain ⟨_, hsub₁, _, _⟩ := leafAddr_props hScale (by omega) hℓ₁M
  have hnot_pref₂₁ : ¬ (leafAddr T ℓ₂ <+: leafAddr T ℓ₁) := by
    rintro ⟨rest, heq⟩
    rw [← heq, subtreeAtAddr_append, hsub₂] at hsub₁
    dsimp only [Option.bind] at hsub₁
    cases rest with
    | nil => simp [subtreeAtAddr] at hsub₁; omega
    | cons _ _ => simp [subtreeAtAddr] at hsub₁
  have hnot_pref₁₂ : ¬ (leafAddr T ℓ₁ <+: leafAddr T ℓ₂) := by
    rintro ⟨rest, heq⟩
    rw [← heq, subtreeAtAddr_append, hsub₁] at hsub₂
    dsimp only [Option.bind] at hsub₂
    cases rest with
    | nil => simp [subtreeAtAddr] at hsub₂; omega
    | cons _ _ => simp [subtreeAtAddr] at hsub₂
  obtain ⟨cA, rA, cB, rB, haddr₂, haddr₁, hc_ne⟩ := lcp_diverge hnot_pref₂₁ hnot_pref₁₂
  set ν := lcaScaleTree T ℓ₂ ℓ₁
  change leafAddr T ℓ₂ = ν ++ (cA :: rA) at haddr₂
  change leafAddr T ℓ₁ = ν ++ (cB :: rB) at haddr₁
  have hc₂_eq : ((leafAddr T ℓ₂)[ν.length]?).getD 1 = cA := by
    rw [haddr₂, List.getElem?_append_right (le_rfl)]
    simp
  have hsub₂_split : (subtreeAtAddr T ν).bind (fun sub => subtreeAtAddr sub (cA :: rA)) =
      some (.leaf ℓ₂) := by
    rw [← subtreeAtAddr_append, ← haddr₂, hsub₂]
  have hsub₁_split : (subtreeAtAddr T ν).bind (fun sub => subtreeAtAddr sub (cB :: rB)) =
      some (.leaf ℓ₁) := by
    rw [← subtreeAtAddr_append, ← haddr₁, hsub₁]
  have hν_int : ∃ cs, subtreeAtAddr T ν = some (.internal cs) := by
    rcases hsub_ν : subtreeAtAddr T ν with _ | sub_ν
    · rw [hsub_ν] at hsub₂_split; cases hsub₂_split
    · cases sub_ν with
      | leaf _ => rw [hsub_ν] at hsub₂_split; simp [subtreeAtAddr, Option.bind] at hsub₂_split
      | internal cs => exact ⟨cs, rfl⟩
  obtain ⟨cs, hsub_ν⟩ := hν_int
  have hmem_int : ν ∈ internalAddrs T :=
    List.mem_toFinset.mpr ((mem_internalAddrList_iff_subtreeAtAddr ν T).mpr ⟨cs, hsub_ν⟩)
  have hν_len_lt_r : ν.length < r := by
    have : (leafAddr T ℓ₂).length = ν.length + (1 + rA.length) := by
      rw [haddr₂, List.length_append, List.length_cons]; omega
    omega
  rw [hsub_ν] at hsub₂_split hsub₁_split
  dsimp only [Option.bind] at hsub₂_split hsub₁_split
  have hmem_cs₂ : (ℓ₂, cA :: rA) ∈ (ScaleTree.internal cs).leafEntries :=
    (mem_leafEntries_iff_subtreeAtAddr (cA :: rA) (.internal cs) ℓ₂).mpr hsub₂_split
  have hmem_cs₁ : (ℓ₁, cB :: rB) ∈ (ScaleTree.internal cs).leafEntries :=
    (mem_leafEntries_iff_subtreeAtAddr (cB :: rB) (.internal cs) ℓ₁).mpr hsub₁_split
  obtain ⟨a_ν, k_ν, hleaves_ν, _, hmEnd_ν, _, hNu_le_M, _⟩ := subtree_range_props hScale hsub_ν
  have hpw_ν : ((ScaleTree.leafEntriesChildren 1 cs).map Prod.fst).Pairwise (· < ·) := by
    change (ScaleTree.internal cs).leaves.Pairwise (· < ·)
    rw [hleaves_ν]
    exact pairwise_lt_range' a_ν (k_ν + 1)
  have hcA_lt_cB : cA < cB := by
    rcases lt_trichotomy cA cB with h | h | h
    · exact h
    · exact absurd h hc_ne
    · exfalso
      have := leafEntriesChildren_order cs 1 hpw_ν hmem_cs₁ hmem_cs₂ h
      omega
  have hcA_bounds : 1 ≤ cA ∧ cA ≤ cs.length ∧ ∃ child₂, subtreeAtAddr T (ν ++ [cA]) = some child₂ := by
    simp only [subtreeAtAddr] at hsub₂_split
    split at hsub₂_split
    · cases hsub₂_split
    · next hcA0 =>
      rcases hget : cs[cA - 1]? with _ | child₂
      · rw [hget] at hsub₂_split; cases hsub₂_split
      · obtain ⟨hidx, _⟩ := List.getElem?_eq_some_iff.mp hget
        refine ⟨by omega, by omega, child₂, ?_⟩
        rw [subtreeAtAddr_append, hsub_ν]
        simp [subtreeAtAddr, hcA0, hget, Option.bind]
  have hcB_le : cB ≤ cs.length := by
    simp only [subtreeAtAddr] at hsub₁_split
    split at hsub₁_split
    · cases hsub₁_split
    · rcases hget : cs[cB - 1]? with _ | _
      · rw [hget] at hsub₁_split; cases hsub₁_split
      · obtain ⟨hidx, _⟩ := List.getElem?_eq_some_iff.mp hget
        omega
  have hnum_ν : numChildren T ν = cs.length := by
    simp [numChildren, hsub_ν]
  obtain ⟨hcA1, hcA_le, child₂, hsub_child₂⟩ := hcA_bounds
  obtain ⟨a₂, k₂, _, hmStart_c₂, hmEnd_c₂, ha₂1, _, _⟩ := subtree_range_props hScale hsub_child₂
  have hpref_c₂_ℓ₂ : ν ++ [cA] <+: leafAddr T ℓ₂ := ⟨rA, by simp [haddr₂]⟩
  have hrange_ℓ₂ :=
    (prefix_leafAddr_iff_mem_range hScale hsub_child₂ hℓ₂1 (by omega)).mp hpref_c₂_ℓ₂
  have hmMid_lt_ℓ₁ : mEnd T (ν ++ [cA]) < ℓ₁ := by
    by_contra hge
    have hℓ₁_in : mStart T (ν ++ [cA]) ≤ ℓ₁ ∧ ℓ₁ ≤ mEnd T (ν ++ [cA]) := ⟨by omega, by omega⟩
    have hpref_c₂_ℓ₁ :=
      (prefix_leafAddr_iff_mem_range hScale hsub_child₂ (by omega) hℓ₁M).mpr hℓ₁_in
    obtain ⟨rest', heq'⟩ := hpref_c₂_ℓ₁
    have hget₁ : (leafAddr T ℓ₁)[ν.length]? = some cA := by
      rw [← heq', List.append_assoc, List.singleton_append, List.getElem?_append_right le_rfl]
      simp
    have hget₁' : (leafAddr T ℓ₁)[ν.length]? = some cB := by
      rw [haddr₁, List.getElem?_append_right le_rfl]
      simp
    rw [hget₁] at hget₁'
    exact hc_ne (Option.some.inj hget₁')
  have hpref_ν_ℓ₁ : ν <+: leafAddr T ℓ₁ := ⟨cB :: rB, haddr₁.symm⟩
  have hℓ₁_le_mNu : ℓ₁ ≤ mEnd T ν :=
    ((prefix_leafAddr_iff_mem_range hScale hsub_ν (by omega) hℓ₁M).mp hpref_ν_ℓ₁).2
  dsimp only
  rw [hc₂_eq]
  refine ⟨hmem_int, hν_len_lt_r, hcA1, by omega, by omega, hrange_ℓ₂.2,
    hmMid_lt_ℓ₁, hℓ₁_le_mNu, by omega, ?_⟩
  intro ℓ₂' ℓ₁' hgt_prev hlt' hle_mid
  have hℓ₂'_in : mStart T (ν ++ [cA]) ≤ ℓ₂' ∧ ℓ₂' ≤ mEnd T (ν ++ [cA]) := ⟨by omega, by omega⟩
  have hℓ₁'_in : mStart T (ν ++ [cA]) ≤ ℓ₁' ∧ ℓ₁' ≤ mEnd T (ν ++ [cA]) := ⟨by omega, hle_mid⟩
  have hpref₂' :=
    (prefix_leafAddr_iff_mem_range hScale hsub_child₂ (by omega) (by omega)).mpr hℓ₂'_in
  have hpref₁' :=
    (prefix_leafAddr_iff_mem_range hScale hsub_child₂ (by omega) (by omega)).mpr hℓ₁'_in
  have hpref_lcp : ν ++ [cA] <+: lcaScaleTree T ℓ₂' ℓ₁' :=
    prefix_lcp_of_prefix hpref₂' hpref₁'
  have hlen_le := hpref_lcp.length_le
  simp at hlen_le
  omega

mutual
  private theorem leafEntries_pos :
      ∀ (T : ScaleTree) (entry : ℕ × List ℕ), entry ∈ T.leafEntries → ∀ c ∈ entry.2, 1 ≤ c
    | .leaf s, entry, hentry, c, hc => by
      simp [ScaleTree.leafEntries] at hentry
      rcases hentry with ⟨_, rfl⟩
      cases hc
    | .internal cs, entry, hentry, c, hc =>
      leafEntriesChildren_pos 1 cs (by omega) entry hentry c hc

  private theorem leafEntriesChildren_pos :
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

private theorem pathWeight_pos (ξ : List ℕ) (hξ : ∀ c ∈ ξ, 1 ≤ c) : 1 ≤ pathWeight ξ := by
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

private theorem scaleS_pos (T : ScaleTree) (P : ℕ) (hP : 1 ≤ P) : ∀ ℓ : ℕ, 1 ≤ scaleS T P ℓ
  | 0 => hP
  | ℓ + 1 => by
    unfold scaleS
    have hw : 1 ≤ leafWeight T (ℓ + 1) := by
      unfold leafWeight leafAddr
      split
      · next s addr hfind =>
        have hmem := List.mem_of_find?_eq_some hfind
        exact pathWeight_pos addr (leafEntries_pos T (s, addr) hmem)
      · exact pathWeight_pos [] (by intro c hc; cases hc)
    have hsq : 1 ≤ (alpha0 (2 * scaleS T P ℓ) + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    exact Nat.mul_le_mul hw hsq

private theorem consecutiveBlocks_of_getElem :
    ∀ (ls : List IntervalBlock),
      (∀ (i : ℕ) (hi : i + 1 < ls.length), ls[i].hi + 1 = ls[i + 1].lo) →
      ConsecutiveBlocks ls
  | [], _ => trivial
  | [_], _ => trivial
  | C₁ :: C₂ :: rest, h =>
    ⟨h 0 (by simp),
     consecutiveBlocks_of_getElem (C₂ :: rest) (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))⟩

private theorem consecutiveBlocks_append :
    ∀ (xs ys : List IntervalBlock) (h₁ l₂ : ℕ),
      xs ≠ [] → ys ≠ [] →
      ConsecutiveBlocks xs → ConsecutiveBlocks ys →
      xs.getLast?.map IntervalBlock.hi = some h₁ →
      ys.head?.map IntervalBlock.lo = some l₂ →
      h₁ + 1 = l₂ →
      ConsecutiveBlocks (xs ++ ys)
  | [], _, _, _, hne, _, _, _, _, _, _ => absurd rfl hne
  | [X], [], _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | [X], Y :: ys, h₁, l₂, _, _, _, hys, hlast, hhead, hstep => by
    simp only [List.getLast?_singleton, Option.map_some, Option.some.injEq] at hlast
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhead
    exact ⟨by omega, hys⟩
  | X₁ :: X₂ :: xs, ys, h₁, l₂, _, hne_y, ⟨hs, hxs⟩, hys, hlast, hhead, hstep => by
    simp only [List.cons_append]
    refine ⟨hs, consecutiveBlocks_append (X₂ :: xs) ys h₁ l₂ (List.cons_ne_nil _ _)
      hne_y hxs hys ?_ hhead hstep⟩
    simpa using hlast

private theorem splitIntervalBySize_props (X : IntervalBlock) (S : ℕ) (hX : X.lo ≤ X.hi) :
    let subs := splitIntervalBySize X S
    subs ≠ [] ∧
    (∀ Y ∈ subs, X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi) ∧
    ConsecutiveBlocks subs ∧
    subs.head?.map IntervalBlock.lo = some X.lo ∧
    subs.getLast?.map IntervalBlock.hi = some X.hi := by
  unfold splitIntervalBySize
  by_cases hcond : S = 0 ∨ X.size < 2 * S
  · simp only [hcond, ↓reduceIte]
    refine ⟨List.cons_ne_nil _ _, ?_, trivial, rfl, rfl⟩
    intro Y hY
    rw [List.mem_singleton] at hY
    subst hY
    exact ⟨le_rfl, hX, le_rfl⟩
  · simp only [hcond, ↓reduceIte]
    have hS : 1 ≤ S := by omega
    have h2S : 2 * S ≤ X.size := by omega
    have hXsz : X.size = X.hi - X.lo + 1 := by simp [IntervalBlock.size, hX]
    set K := X.size / S
    have hK2 : 2 ≤ K := (Nat.le_div_iff_mul_le hS).mpr h2S
    have hdiv : S * K + X.size % S = X.size := Nat.div_add_mod X.size S
    have hmod : X.size % S < S := Nat.mod_lt X.size hS
    have hKS_comm : K * S = S * K := Nat.mul_comm K S
    let f : ℕ → IntervalBlock := fun idx =>
      if idx + 1 < K then ⟨X.lo + idx * S, X.lo + (idx + 1) * S - 1⟩
      else ⟨X.lo + idx * S, X.hi⟩
    change (List.range K).map f ≠ [] ∧ _ ∧ ConsecutiveBlocks ((List.range K).map f) ∧
      ((List.range K).map f).head?.map IntervalBlock.lo = some X.lo ∧
      ((List.range K).map f).getLast?.map IntervalBlock.hi = some X.hi
    have hlen : ((List.range K).map f).length = K := by simp
    refine ⟨by intro h; rw [h] at hlen; simp at hlen; omega, ?_, ?_, ?_, ?_⟩
    · intro Y hY
      obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hY
      rw [List.mem_range] at hidx
      split_ifs with hlt
      · dsimp only
        have hmul : (idx + 1) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
        have hstepS : idx * S + S = (idx + 1) * S := by ring
        exact ⟨by omega, by omega, by omega⟩
      · dsimp only
        have hidx_eq : idx = K - 1 := by omega
        subst hidx_eq
        have hK1S : (K - 1) * S + S = K * S := by
          calc (K - 1) * S + S = ((K - 1) + 1) * S := by ring
            _ = K * S := by rw [show K - 1 + 1 = K by omega]
        exact ⟨by omega, by omega, le_rfl⟩
    · apply consecutiveBlocks_of_getElem
      intro i hi
      rw [hlen] at hi
      simp only [List.getElem_map, List.getElem_range, f, hi, ↓reduceIte]
      have h1S : 1 ≤ (i + 1) * S := Nat.mul_le_mul (show 1 ≤ i + 1 by omega) hS
      split_ifs <;> simp <;> omega
    · rw [List.head?_eq_getElem?]
      simp [show 0 < K by omega, f, show 0 + 1 < K by omega]
    · rw [List.getLast?_eq_getElem?, hlen]
      simp [show K - 1 < K by omega, show ¬ (K - 1 + 1 < K) by omega, f]

private theorem flatMap_split_preserves_partition {P : ℕ} (hP : 1 ≤ P)
    {blocks : List IntervalBlock} (hPart : IsContiguousBlockPartition P blocks) (S : ℕ) :
    IsContiguousBlockPartition P (blocks.flatMap (fun X => splitIntervalBySize X S)) := by
  have hne : blocks ≠ [] := by
    intro hemp; subst hemp
    have h0 := hPart.2.2; simp at h0; omega
  have hBounds : ∀ Y ∈ blocks.flatMap (fun X => splitIntervalBySize X S),
      1 ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ P := by
    intro Y hY
    obtain ⟨X, hX, hYX⟩ := List.mem_flatMap.mp hY
    obtain ⟨hX1, hXle, hXP⟩ := hPart.1 X hX
    obtain ⟨_, hYbounds, _, _, _⟩ := splitIntervalBySize_props X S hXle
    obtain ⟨h1, h2, h3⟩ := hYbounds Y hYX
    exact ⟨by omega, h2, by omega⟩
  have hFlat : ∀ (bs : List IntervalBlock),
      bs ≠ [] → (∀ X ∈ bs, X.lo ≤ X.hi) → ConsecutiveBlocks bs →
      let out := bs.flatMap (fun X => splitIntervalBySize X S)
      out ≠ [] ∧
      ConsecutiveBlocks out ∧
      out.head?.map IntervalBlock.lo = bs.head?.map IntervalBlock.lo ∧
      out.getLast?.map IntervalBlock.hi = bs.getLast?.map IntervalBlock.hi := by
    intro bs
    induction bs with
    | nil => intro h; exact absurd rfl h
    | cons X rest ih =>
      intro _ hle hcons
      obtain ⟨hneX, _, hconsX, hheadX, hlastX⟩ :=
        splitIntervalBySize_props X S (hle X List.mem_cons_self)
      cases rest with
      | nil =>
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact ⟨hneX, hconsX, hheadX, hlastX⟩
      | cons X₂ rs =>
        rcases hcons with ⟨hstep, hcons_rest⟩
        obtain ⟨hneR, hconsR, hheadR, hlastR⟩ :=
          ih (List.cons_ne_nil _ _) (fun C hC => hle C (List.mem_cons_of_mem X hC)) hcons_rest
        dsimp only
        rw [List.flatMap_cons]
        have hheadR' : ((X₂ :: rs).flatMap (fun C => splitIntervalBySize C S)).head?.map
            IntervalBlock.lo = some X₂.lo := by simpa using hheadR
        refine ⟨List.append_ne_nil_of_left_ne_nil hneX _,
          consecutiveBlocks_append _ _ X.hi X₂.lo hneX hneR hconsX hconsR hlastX hheadR' hstep,
          ?_, ?_⟩
        · rw [List.head?_append_of_ne_nil _ hneX, hheadX]; rfl
        · rw [List.getLast?_append_of_ne_nil _ hneR, hlastR]; simp
  obtain ⟨hout_ne, hout_cons, hout_head, hout_last⟩ :=
    hFlat blocks hne (fun C hC => (hPart.1 C hC).2.1) hPart.2.1
  refine ⟨hBounds, hout_cons, ?_⟩
  rcases hbh : blocks.head? with _ | bFirst
  · exact absurd (List.head?_eq_none_iff.mp hbh) hne
  rcases hbl : blocks.getLast? with _ | bLast
  · exact absurd (List.getLast?_eq_none_iff.mp hbl) hne
  have hends : bFirst.lo = 1 ∧ bLast.hi = P := by
    have h := hPart.2.2; rw [hbh, hbl] at h; exact h
  rcases hoh : (blocks.flatMap (fun X => splitIntervalBySize X S)).head? with _ | oFirst
  · exact absurd (List.head?_eq_none_iff.mp hoh) hout_ne
  rcases hol : (blocks.flatMap (fun X => splitIntervalBySize X S)).getLast? with _ | oLast
  · exact absurd (List.getLast?_eq_none_iff.mp hol) hout_ne
  rw [hoh, hbh] at hout_head
  rw [hol, hbl] at hout_last
  simp only [Option.map_some, Option.some.injEq] at hout_head hout_last
  exact ⟨hout_head.trans hends.1, hout_last.trans hends.2⟩

private theorem validScaleTree_isNestedPartitionChain (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) :
    IsNestedPartitionChain P (scaleTreePartitionChain T P M) := by
  have hP : 1 ≤ P := hValid.1
  have hPne : P ≠ 0 := by omega
  have hLevelPart : ∀ n : ℕ, IsContiguousBlockPartition P (scaleTreePartitionLevel T P n) := by
    intro n
    induction n with
    | zero =>
      simp only [scaleTreePartitionLevel, hPne, ↓reduceIte]
      refine ⟨?_, trivial, rfl, rfl⟩
      intro C hC
      rw [List.mem_singleton] at hC
      subst hC
      exact ⟨le_rfl, hP, le_rfl⟩
    | succ n ih =>
      simp only [scaleTreePartitionLevel]
      exact flatMap_split_preserves_partition hP ih (scaleS T P (n + 1))
  refine ⟨hP, ?_, fun ℓ => hLevelPart ℓ.val, ?_⟩
  · simp [scaleTreePartitionChain, scaleTreePartitionLevel, hPne]
  · intro ℓ Y hY
    simp only [scaleTreePartitionChain, Fin.val_succ, scaleTreePartitionLevel,
      List.mem_flatMap] at hY
    obtain ⟨X, hX, hYX⟩ := hY
    have hXle : X.lo ≤ X.hi := ((hLevelPart ℓ.val).1 X hX).2.1
    obtain ⟨h1, _, h3⟩ := (splitIntervalBySize_props X (scaleS T P (ℓ.val + 1)) hXle).2.1 Y hYX
    exact ⟨X, hX, h1, h3⟩

private theorem splitIntervalBySize_sizes (X : IntervalBlock) (S : ℕ)
    (hXlo : 1 ≤ X.lo) (hS : 1 ≤ S) (h2S : 2 * S ≤ X.size) :
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
      calc (K - 1) * S + S = ((K - 1) + 1) * S := by ring
        _ = K * S := by rw [show K - 1 + 1 = K by omega]
    have hlo_le_hi : X.lo + (K - 1) * S ≤ X.hi := by omega
    refine ⟨by omega, hlo_le_hi, le_rfl, ?_, ?_⟩
    · simp only [IntervalBlock.size, hlo_le_hi, ↓reduceIte]; omega
    · simp only [IntervalBlock.size, hlo_le_hi, ↓reduceIte]; omega

private theorem validScaleTree_leaf_sizes (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) :
    ∀ Q ∈ scaleTreePartitionChain T P M (Fin.last M),
      1 ≤ Q.size ∧ Q.size < 2 * scaleS T P M := by
  rcases hValid with ⟨hP, hScale, hHalf⟩
  have hM1 : 1 ≤ M := hScale.2.1
  have hLevel : ∀ ℓ : ℕ, ℓ ≤ M →
      ∀ X ∈ scaleTreePartitionLevel T P ℓ,
        1 ≤ X.lo ∧ scaleS T P ℓ ≤ X.size ∧ (1 ≤ ℓ → X.size < 2 * scaleS T P ℓ) := by
    intro ℓ
    induction ℓ with
    | zero =>
      intro _ X hX
      have hPne : P ≠ 0 := by omega
      simp only [scaleTreePartitionLevel, hPne, ↓reduceIte, List.mem_singleton] at hX
      subst hX
      refine ⟨le_rfl, ?_, by intro h; omega⟩
      change P ≤ (if 1 ≤ P then P - 1 + 1 else 0)
      split_ifs; omega
    | succ ℓ ih =>
      intro hℓM X hX
      simp only [scaleTreePartitionLevel, List.mem_flatMap] at hX
      obtain ⟨parent, hparent, hchild⟩ := hX
      obtain ⟨hplo, hpsz, _⟩ := ih (by omega) parent hparent
      have hSpos : 1 ≤ scaleS T P (ℓ + 1) := scaleS_pos T P hP (ℓ + 1)
      have h2S : 2 * scaleS T P (ℓ + 1) ≤ parent.size :=
        le_trans (hHalf ⟨ℓ, hℓM⟩) hpsz
      obtain ⟨h1, _, _, h4, h5⟩ :=
        splitIntervalBySize_sizes parent (scaleS T P (ℓ + 1)) hplo hSpos h2S X hchild
      exact ⟨le_trans hplo h1, h4, fun _ => h5⟩
  intro Q hQ
  have hSpos : 1 ≤ scaleS T P M := scaleS_pos T P hP M
  obtain ⟨_, hge, hlt⟩ := hLevel M le_rfl Q hQ
  exact ⟨le_trans hSpos hge, hlt hM1⟩


/-!
## 4. Upstream Hypothesis Signatures (Layers 0..3) and `lem_5_10_bucket_b2`
-/

/-- Exact statement type of `Challenge.lem_3_6_folded_laws` (Layer 0). -/
abbrev Ty_lem_3_6_folded_laws : Prop :=
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

/-- Exact statement type of `Challenge.thm_2_3_mod2_cascade` (Layer 1). -/
abbrev Ty_thm_2_3_mod2_cascade : Prop :=
  ∃ C_casc : ℝ, IsCascadeBoundConst C_casc

/-- Exact statement type of `Challenge.lem_5_1_tree_weights` (Layer 1). -/
abbrev Ty_lem_5_1_tree_weights : Prop :=
  ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
    let chain := scaleTreePartitionChain T P M
    (∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T ℓ : ℝ)) < (1 : ℝ) / 2 ∧
    (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) < 2 ∧
    (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50

/-- Exact statement type of `Challenge.lem_5_2_bucket_leaf` (Layer 2). -/
abbrev Ty_lem_5_2_bucket_leaf : Prop :=
  ∀ {M : ℕ} (P : ℕ), 1 ≤ P → 1 ≤ M →
    ∀ (proc : FoldedPopProcess P) (chain : Fin (M + 1) → List IntervalBlock),
      IsNestedPartitionChain P chain →
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
          2 * P + (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum

/-- Exact statement type of `Challenge.lem_5_3_bucket_b1` (Layer 2). -/
abbrev Ty_lem_5_3_bucket_b1 : Prop :=
  ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T → ∀ (proc : FoldedPopProcess P),
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
    (ee.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ)

/-- Exact statement type of `Challenge.lem_5_9_bucket_b3_exit` (Layer 3). -/
abbrev Ty_lem_5_9_bucket_b3_exit : Prop :=
  ∀ (C_casc : ℝ), IsCascadeBoundConst C_casc →
    ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
    ∀ (proc : FoldedPopProcess P),
      let chain := scaleTreePartitionChain T P M
      (b3 P proc chain).card = (b3Intra P proc chain).card + (b3Exit P proc chain).card ∧
      ((b3Exit P proc chain).card : ℝ) < (9 * C_casc + 341) * (P : ℝ) ∧
      ((b3 P proc chain).card : ℝ) < (9 * C_casc + 348) * (P : ℝ)

private def chainFrom {α : Type} (V T_set : Finset α) (next? : α → Option α) :
    ℕ → α → α → Prop
  | 0, x, t => x = t
  | n + 1, x, t => x ∈ V ∧ x ∉ T_set ∧ ∃ y ∈ V, next? x = some y ∧ chainFrom V T_set next? n y t

private theorem chainFrom_inj {α : Type} {V T_set : Finset α} {next? : α → Option α}
    (hInj : ∀ x₁ ∈ V, ∀ x₂ ∈ V, ∀ y, next? x₁ = some y → next? x₂ = some y → x₁ = x₂) :
    ∀ (n : ℕ) {x₁ x₂ t : α}, x₁ ∈ V → x₂ ∈ V →
      chainFrom V T_set next? n x₁ t → chainFrom V T_set next? n x₂ t → x₁ = x₂
  | 0, _, _, _, _, _, h1, h2 => h1.trans h2.symm
  | n + 1, x₁, x₂, _, hx₁, hx₂, ⟨_, _, y₁, hy₁, hn₁, hc₁⟩, ⟨_, _, y₂, hy₂, hn₂, hc₂⟩ => by
    have hy_eq : y₁ = y₂ := chainFrom_inj hInj n hy₁ hy₂ hc₁ hc₂
    subst hy_eq
    exact hInj x₁ hx₁ x₂ hx₂ y₁ hn₁ hn₂

private theorem card_le_mul_of_bounded_rank_step {α : Type} [DecidableEq α]
    (V T_set : Finset α) (r : ℕ) (rk : α → ℕ) (next? : α → Option α)
    (hRk : ∀ x ∈ V, rk x < r)
    (hInj : ∀ x₁ ∈ V, ∀ x₂ ∈ V, ∀ y, next? x₁ = some y → next? x₂ = some y → x₁ = x₂)
    (hStep : ∀ x ∈ V, x ∉ T_set → ∃ y ∈ V, next? x = some y ∧ rk x < rk y) :
    V.card ≤ r * T_set.card := by
  have hex_fuel : ∀ (fuel : ℕ) (x : α), x ∈ V → r - rk x ≤ fuel →
      ∃ n < r - rk x, ∃ t ∈ T_set, chainFrom V T_set next? n x t := by
    intro fuel
    induction fuel with
    | zero =>
      intro x hx hle
      have := hRk x hx
      omega
    | succ fuel ih =>
      intro x hx hle
      by_cases hxT : x ∈ T_set
      · have hpos : 0 < r - rk x := by have := hRk x hx; omega
        exact ⟨0, hpos, x, hxT, rfl⟩
      · obtain ⟨y, hyV, hnext, hrk_lt⟩ := hStep x hx hxT
        have hy_rk : rk y < r := hRk y hyV
        obtain ⟨n, hn_lt, t, ht_T, hchain⟩ := ih y hyV (by omega)
        exact ⟨n + 1, by omega, t, ht_T, ⟨hx, hxT, y, hyV, hnext, hchain⟩⟩
  have hex : ∀ x ∈ V, ∃ p ∈ Finset.range r ×ˢ T_set, chainFrom V T_set next? p.1 x p.2 := by
    intro x hx
    obtain ⟨n, hn_lt, t, ht_T, hchain⟩ := hex_fuel (r - rk x) x hx le_rfl
    exact ⟨(n, t), Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), ht_T⟩, hchain⟩
  classical
  let f : α → ℕ × α := fun x =>
    if hx : x ∈ V then Classical.choose (hex x hx) else (0, x)
  have hmaps : ∀ x ∈ V, f x ∈ Finset.range r ×ˢ T_set := by
    intro x hx
    simp only [f, hx, ↓reduceDIte]
    exact (Classical.choose_spec (hex x hx)).1
  have hinj : Set.InjOn f (V : Set α) := by
    intro x₁ hx₁ x₂ hx₂ hfeq
    rw [Finset.mem_coe] at hx₁ hx₂
    have hc₁ : chainFrom V T_set next? (f x₁).1 x₁ (f x₁).2 := by
      simp only [f, hx₁, ↓reduceDIte]; exact (Classical.choose_spec (hex x₁ hx₁)).2
    have hc₂ : chainFrom V T_set next? (f x₂).1 x₂ (f x₂).2 := by
      simp only [f, hx₂, ↓reduceDIte]; exact (Classical.choose_spec (hex x₂ hx₂)).2
    rw [hfeq] at hc₁
    exact chainFrom_inj hInj (f x₂).1 hx₁ hx₂ hc₁ hc₂
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa [Finset.card_product, Finset.card_range] using hcard

private theorem b2_tree_geom {P r M : ℕ} {T : ScaleTree} (hScale : IsScaleTree r M T)
    {proc : FoldedPopProcess P} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    (hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P)
    {e : InternalPopRot} (he_b2 : e ∈ b2 P proc chain)
    (hℓ₁M : partSepScale P chain e.s e.x ≤ M) :
    let ℓ₁ := partSepScale P chain e.s e.x
    let ℓ₂ := partSepScale P chain e.x e.y
    let ν := lcaScaleTree T ℓ₂ ℓ₁
    let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 1
    let mPrev := mStart T (ν ++ [c₂]) - 1
    let mMid := mEnd T (ν ++ [c₂])
    let mNu := mEnd T ν
    ∃ (hmPrev : mPrev ≤ M) (hmMid : mMid ≤ M) (hmNu : mNu ≤ M),
      let fPrev : Fin (M + 1) := ⟨mPrev, Nat.lt_succ_of_le hmPrev⟩
      let fMid : Fin (M + 1) := ⟨mMid, Nat.lt_succ_of_le hmMid⟩
      let fNu : Fin (M + 1) := ⟨mNu, Nat.lt_succ_of_le hmNu⟩
      let Qstar := blockAt (chain fNu) e.s
      let B_mid := blockAt (chain fMid) Qstar.lo
      let B_prev := blockAt (chain fPrev) Qstar.lo
      ν ∈ internalAddrs T ∧
      ν.length < r ∧
      1 ≤ c₂ ∧ c₂ ≤ numChildren T ν ∧
      mPrev < ℓ₂ ∧ ℓ₂ ≤ mMid ∧ mMid < ℓ₁ ∧ ℓ₁ ≤ mNu ∧
      Qstar ∈ chain fNu ∧
      blockAt (chain fMid) e.s = B_mid ∧
      blockAt (chain fMid) e.x = B_mid ∧
      blockAt (chain fPrev) e.s = B_prev ∧
      blockAt (chain fPrev) e.y = B_prev ∧
      B_prev.lo ≤ e.s ∧ e.s ≤ Qstar.hi ∧ Qstar.hi < e.x ∧
      e.x ≤ B_mid.hi ∧ B_mid.hi < e.y ∧ e.y ≤ B_prev.hi ∧ B_prev.hi ≤ P ∧
      (∀ ℓ₂' ℓ₁' : ℕ, mPrev < ℓ₂' → ℓ₂' < ℓ₁' → ℓ₁' ≤ mMid →
        ν.length < (lcaScaleTree T ℓ₂' ℓ₁').length) := by
  have he_b2' := he_b2
  simp only [b2, Finset.mem_filter] at he_b2'
  obtain ⟨he, hℓ₂1, hℓ₂_lt_ℓ₁, _⟩ := he_b2'
  obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e he
  set ℓ₁ := partSepScale P chain e.s e.x
  set ℓ₂ := partSepScale P chain e.x e.y
  obtain ⟨hν_int, hν_len, hc₂1, hc₂_le, hmPrev_lt_ℓ₂, hℓ₂_le_mMid,
    hmMid_lt_ℓ₁, hℓ₁_le_mNu, hmNu_le_M, hdepth⟩ :=
    lcaScaleTree_routing hScale hℓ₂1 hℓ₂_lt_ℓ₁ hℓ₁M
  set ν := lcaScaleTree T ℓ₂ ℓ₁
  set c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 1
  set mPrev := mStart T (ν ++ [c₂]) - 1
  set mMid := mEnd T (ν ++ [c₂])
  set mNu := mEnd T ν
  have hmPrev : mPrev ≤ M := by omega
  have hmMid : mMid ≤ M := by omega
  have hmNu : mNu ≤ M := hmNu_le_M
  let fPrev : Fin (M + 1) := ⟨mPrev, Nat.lt_succ_of_le hmPrev⟩
  let fMid : Fin (M + 1) := ⟨mMid, Nat.lt_succ_of_le hmMid⟩
  let fNu : Fin (M + 1) := ⟨mNu, Nat.lt_succ_of_le hmNu⟩
  set Qstar := blockAt (chain fNu) e.s
  set B_mid := blockAt (chain fMid) Qstar.lo
  set B_prev := blockAt (chain fPrev) Qstar.lo
  obtain ⟨hQ_mem, _, hs_le_Q, _⟩ :=
    blockAt_mem_and_bounds (hChain.2.2.1 fNu) (u := e.s) hs1 (by omega)
  have hBmid_s : blockAt (chain fMid) e.s = B_mid :=
    blockAt_enclosing_eq hChain (show fMid ≤ fNu by change mMid ≤ mNu; omega) hs1 (by omega)
  have hBprev_s : blockAt (chain fPrev) e.s = B_prev :=
    blockAt_enclosing_eq hChain (show fPrev ≤ fNu by change mPrev ≤ mNu; omega) hs1 (by omega)
  have hBmid_sx : blockAt (chain fMid) e.s = blockAt (chain fMid) e.x :=
    (lt_partSepScale_iff hChain e.s e.x hs1 (by omega) (by omega) (by omega) fMid).mp hmMid_lt_ℓ₁
  have hBmid_x : blockAt (chain fMid) e.x = B_mid := hBmid_sx.symm.trans hBmid_s
  have hx_le_Bmid : e.x ≤ B_mid.hi := by
    rw [← hBmid_x]
    exact (blockAt_mem_and_bounds (hChain.2.2.1 fMid) (u := e.x) (by omega) (by omega)).2.2.1
  have hQ_ne_x : blockAt (chain fNu) e.s ≠ blockAt (chain fNu) e.x := by
    intro heq
    have := (lt_partSepScale_iff hChain e.s e.x hs1 (by omega) (by omega) (by omega) fNu).mpr heq
    change mNu < ℓ₁ at this
    omega
  have hQhi_lt_x : Qstar.hi < e.x := by
    have hlt := blockAt_hi_lt_lo_of_ne (hChain.2.2.1 fNu) hs1 (le_of_lt hsx) (by omega) hQ_ne_x
    change Qstar.hi < (blockAt (chain fNu) e.x).lo at hlt
    have hx_lo := (blockAt_mem_and_bounds (hChain.2.2.1 fNu) (u := e.x) (by omega) (by omega)).2.1
    omega
  have hBmid_ne_y : blockAt (chain fMid) e.x ≠ blockAt (chain fMid) e.y := by
    intro heq
    have := (lt_partSepScale_iff hChain e.x e.y (by omega) (by omega) (by omega) (by omega) fMid).mpr heq
    change mMid < ℓ₂ at this
    omega
  have hBmid_lt_y : B_mid.hi < e.y := by
    have hlt := blockAt_hi_lt_lo_of_ne (hChain.2.2.1 fMid) (by omega) (le_of_lt hxy) (by omega) hBmid_ne_y
    have hy_lo := (blockAt_mem_and_bounds (hChain.2.2.1 fMid) (u := e.y) (by omega) (by omega)).2.1
    rw [hBmid_x] at hlt
    omega
  have hsep_sy : partSepScale P chain e.s e.y = ℓ₂ := by
    rw [partSepScale_ultrametric hChain hs1 (le_of_lt hsx) (le_of_lt hxy) (by omega)]
    exact min_eq_right (le_of_lt hℓ₂_lt_ℓ₁)
  have hBprev_sy : blockAt (chain fPrev) e.s = blockAt (chain fPrev) e.y := by
    apply (lt_partSepScale_iff hChain e.s e.y hs1 (by omega) (by omega) (by omega) fPrev).mp
    change mPrev < partSepScale P chain e.s e.y
    omega
  have hBprev_y : blockAt (chain fPrev) e.y = B_prev := hBprev_sy.symm.trans hBprev_s
  obtain ⟨hBprev_mem, hs_ge_Bprev, _, _⟩ :=
    blockAt_mem_and_bounds (hChain.2.2.1 fPrev) (u := e.s) hs1 (by omega)
  have hy_le_Bprev : e.y ≤ B_prev.hi := by
    rw [← hBprev_y]
    exact (blockAt_mem_and_bounds (hChain.2.2.1 fPrev) (u := e.y) (by omega) (by omega)).2.2.1
  have hBprev_hi_le_P : B_prev.hi ≤ P := by
    rw [hBprev_s] at hBprev_mem
    exact ((hChain.2.2.1 fPrev).1 _ hBprev_mem).2.2
  rw [hBprev_s] at hs_ge_Bprev
  exact ⟨hmPrev, hmMid, hmNu, hν_int, hν_len, hc₂1, hc₂_le,
    hmPrev_lt_ℓ₂, hℓ₂_le_mMid, hmMid_lt_ℓ₁, hℓ₁_le_mNu,
    hQ_mem, hBmid_s, hBmid_x, hBprev_s, hBprev_y,
    hs_ge_Bprev, hs_le_Q, hQhi_lt_x, hx_le_Bmid, hBmid_lt_y, hy_le_Bprev, hBprev_hi_le_P,
    hdepth⟩

/-- **Lemma 5.10** (`lem:bucket-b2`, `LCA_𝒯` Routing of `ℬ_2`). -/
theorem lem_5_10_bucket_b2
    (h_3_6 : Ty_lem_3_6_folded_laws)
    (h_5_1 : Ty_lem_5_1_tree_weights)
    (h_5_3 : Ty_lem_5_3_bucket_b1)
    (h_5_9 : Ty_lem_5_9_bucket_b3_exit)
    (C_casc : ℝ) (hCcasc : IsCascadeBoundConst C_casc)
    (P r M : ℕ) (T : ScaleTree) (hValid : ValidScaleTree P r M T)
    (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    let s2 := s2Set P T proc chain
    s2 ⊆ b2 P proc chain ∧
    s2.card ≤ P + 2 * sigmaScaleTree T chain ∧
    (s2.card : ℝ) < (26 : ℝ) / 25 * (P : ℝ) ∧
    (b2 P proc chain).card ≤
      P + r * (s2.card + (eEnter P T proc chain).card + (b3 P proc chain).card) ∧
    ((b2 P proc chain).card : ℝ) < (9 * C_casc + 353) * (r : ℝ) * (P : ℝ) := by
  intro chain s2
  have hP : 1 ≤ P := hValid.1
  have hScale : IsScaleTree r M T := hValid.2.1
  have hr1 : 1 ≤ r := hScale.1
  have hChain : IsNestedPartitionChain P chain := validScaleTree_isNestedPartitionChain P r M T hValid
  have h36 := h_3_6 P hP proc
  have hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST :=
    fun τ hτ => (h36.1.1 τ hτ).1
  have hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P := by
    intro e he
    obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := h36.2.1.2 e he
    exact ⟨h1, h2, h3, h4, h5⟩
  have hFreeze : ∀ e ∈ proc.rInt, ∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
      ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z) :=
    fun e he => (h36.2.1.2 e he).2.2.2.2.2.2
  -- Conjunct 1: `s2 ⊆ b2`
  have hs2_sub : s2 ⊆ b2 P proc chain := Finset.filter_subset _ _
  -- Unpack `s2` membership
  have hs2_unpack : ∀ e ∈ s2,
      e ∈ b2 P proc chain ∧
      partSepScale P chain e.s e.x ≤ M ∧
      let ℓ₁ := partSepScale P chain e.s e.x
      let ℓ₂ := partSepScale P chain e.x e.y
      let ν := lcaScaleTree T ℓ₂ ℓ₁
      let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 1
      let mPrev := mStart T (ν ++ [c₂]) - 1
      ∃ hm : mPrev ≤ M,
        let hiShell := (blockAt (chain ⟨mPrev, Nat.lt_succ_of_le hm⟩) e.s).hi
        hiShell < e.z ∨ e.j = e.h ∨
          (proc.nextCascadeRot? e).elim true (fun eNext => decide (hiShell < eNext.y)) = true := by
    intro e he_s2
    have he_s2' : e ∈ s2Set P T proc chain := he_s2
    simp only [s2Set, Finset.mem_filter] at he_s2'
    obtain ⟨he_b2, hcond⟩ := he_s2'
    by_cases hℓ₁M : partSepScale P chain e.s e.x ≤ M
    · simp only [hℓ₁M, ↓reduceIte] at hcond
      split at hcond
      · next hm => exact ⟨he_b2, hℓ₁M, hm, hcond⟩
      · cases hcond
    · simp only [hℓ₁M, ↓reduceIte] at hcond
  -- Conjunct 2: `s2.card ≤ P + 2 * sigmaScaleTree T chain`
  let hiShellOf : InternalPopRot → ℕ := fun e =>
    let ℓ₁ := partSepScale P chain e.s e.x
    let ℓ₂ := partSepScale P chain e.x e.y
    let ν := lcaScaleTree T ℓ₂ ℓ₁
    let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 1
    let mPrev := mStart T (ν ++ [c₂]) - 1
    if hm : mPrev ≤ M then (blockAt (chain ⟨mPrev, Nat.lt_succ_of_le hm⟩) e.s).hi else 0
  let s2_top := s2.filter (fun e => e.j = e.h)
  let s2_2A := s2.filter (fun e => e.j ≠ e.h ∧ hiShellOf e < e.z)
  let s2_2B2a := s2.filter (fun e => e.j ≠ e.h ∧ ¬ (hiShellOf e < e.z))
  have hs2_cover : s2 ⊆ s2_top ∪ s2_2A ∪ s2_2B2a := by
    intro e he
    simp only [s2_top, s2_2A, s2_2B2a, Finset.mem_union, Finset.mem_filter]
    by_cases hjh : e.j = e.h
    · exact Or.inl (Or.inl ⟨he, hjh⟩)
    · by_cases hhi : hiShellOf e < e.z
      · exact Or.inl (Or.inr ⟨he, hjh, hhi⟩)
      · exact Or.inr ⟨he, hjh, hhi⟩
  -- 2a. `s2_top.card ≤ P`
  have hs2_top_card : s2_top.card ≤ P := by
    have hmaps : ∀ e ∈ s2_top, e.s ∈ Finset.Icc 1 P := by
      intro e he
      have he_rInt : e ∈ proc.rInt := (Finset.mem_filter.mp (hs2_sub (Finset.mem_filter.mp he).1)).1
      obtain ⟨hs1, hsx, _, _, hzP⟩ := hOrd e he_rInt
      exact Finset.mem_Icc.mpr ⟨hs1, by omega⟩
    have hinj : Set.InjOn InternalPopRot.s (s2_top : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ hs_eq
      rw [Finset.mem_coe, Finset.mem_filter] at he₁ he₂
      have hr₁ : e₁ ∈ proc.rInt := (Finset.mem_filter.mp (hs2_sub he₁.1)).1
      have hr₂ : e₂ ∈ proc.rInt := (Finset.mem_filter.mp (hs2_sub he₂.1)).1
      have hstep : e₁.stepIdx = e₂.stepIdx := by
        rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂, hs_eq]
      obtain ⟨_, b₁, _, hb₁, hh₁, _⟩ := rInt_unpack proc hr₁
      obtain ⟨_, b₂, _, hb₂, hh₂, _⟩ := rInt_unpack proc hr₂
      have hb_eq : some b₁ = some b₂ := by rw [← hb₁]; simpa [hstep] using hb₂
      injection hb_eq with hb_eq'
      subst hb_eq'
      have hh_eq : e₁.h = e₂.h := by rw [hh₁, hh₂, hstep]
      exact rInt_same_step_eq proc hr₁ hr₂ hstep (he₁.2.trans (hh_eq.trans he₂.2.symm))
    have hle := Finset.card_le_card_of_injOn InternalPopRot.s hmaps hinj
    rw [Nat.card_Icc] at hle
    omega
  -- Target Finset of cardinality `sigmaScaleTree T chain`
  let SigmaTarget : Finset (Σ _ : List ℕ, ℕ × IntervalBlock) :=
    (internalAddrs T).sigma (fun ν =>
      if hm : mEnd T ν ≤ M then
        Finset.Icc 1 (numChildren T ν) ×ˢ (chain ⟨mEnd T ν, Nat.lt_succ_of_le hm⟩).toFinset
      else ∅)
  have hSigma_card : SigmaTarget.card = sigmaScaleTree T chain := by
    dsimp only [SigmaTarget, sigmaScaleTree]
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl ?_
    intro ν _
    split_ifs with hm
    · rw [Finset.card_product, Nat.card_Icc,
        List.toFinset_card_of_nodup (contiguous_blocks_nodup (hChain.2.2.1 _))]
      simp
    · rfl
  let tauKey : InternalPopRot → Σ _ : List ℕ, ℕ × IntervalBlock := fun e =>
    let ℓ₁ := partSepScale P chain e.s e.x
    let ℓ₂ := partSepScale P chain e.x e.y
    let ν := lcaScaleTree T ℓ₂ ℓ₁
    let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 1
    let mNu := mEnd T ν
    let Qstar := if hm : mNu ≤ M then blockAt (chain ⟨mNu, Nat.lt_succ_of_le hm⟩) e.s else ⟨0, 0⟩
    ⟨ν, (c₂, Qstar)⟩
  have htau_maps : ∀ e ∈ s2, tauKey e ∈ SigmaTarget := by
    intro e he_s2
    obtain ⟨he_b2, hℓ₁M, _⟩ := hs2_unpack e he_s2
    obtain ⟨_, _, hmNu, hν_int, _, hc₂1, hc₂_le, _, _, _, _, hQ_mem, _⟩ :=
      b2_tree_geom hScale hChain hOrd he_b2 hℓ₁M
    dsimp only [tauKey, SigmaTarget]
    rw [Finset.mem_sigma]
    refine ⟨hν_int, ?_⟩
    simp only [hmNu, ↓reduceDIte, Finset.mem_product]
    exact ⟨Finset.mem_Icc.mpr ⟨hc₂1, hc₂_le⟩, List.mem_toFinset.mpr hQ_mem⟩
  -- 2b. `s2_2A.card ≤ sigmaScaleTree T chain`
  have hs2_2A_no_lt : ∀ {e₁ e₂ : InternalPopRot},
      e₁ ∈ s2_2A → e₂ ∈ s2_2A → tauKey e₁ = tauKey e₂ →
      (e₁.s < e₂.s ∨ (e₁.s = e₂.s ∧ e₁.j < e₂.j)) → False := by
    intro e₁ e₂ he₁ he₂ htau hord
    obtain ⟨he₁_s2, _, hhi₁_lt_z⟩ := Finset.mem_filter.mp he₁
    obtain ⟨he₂_s2, _, _⟩ := Finset.mem_filter.mp he₂
    obtain ⟨he₁_b2, hℓ₁M₁, _⟩ := hs2_unpack e₁ he₁_s2
    obtain ⟨he₂_b2, hℓ₁M₂, _⟩ := hs2_unpack e₂ he₂_s2
    have hr₁ : e₁ ∈ proc.rInt := (Finset.mem_filter.mp he₁_b2).1
    have hr₂ : e₂ ∈ proc.rInt := (Finset.mem_filter.mp he₂_b2).1
    obtain ⟨hmPrev₁, hmMid₁, hmNu₁, _, _, _, _, _, _, _, _, _, _, _, hBprev_s₁, _,
      _, hs₁_le_Q, hQ_lt_x₁, hx₁_le_Bmid, hBmid_lt_y₁, hy₁_le_Bprev, _, _⟩ :=
      b2_tree_geom hScale hChain hOrd he₁_b2 hℓ₁M₁
    obtain ⟨hmPrev₂, hmMid₂, hmNu₂, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, hs₂_le_Q, _, hx₂_le_Bmid, hBmid_lt_y₂, hy₂_le_Bprev, _, _⟩ :=
      b2_tree_geom hScale hChain hOrd he₂_b2 hℓ₁M₂
    dsimp only [tauKey] at htau
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at htau
    rcases htau with ⟨hν_eq, hc₂_eq, hQ_eq⟩
    simp only [hmNu₁, hmNu₂, ↓reduceDIte] at hQ_eq
    have hhi₁_eq : hiShellOf e₁ =
        (blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
            (partSepScale P chain e₁.s e₁.x) ++
            [((leafAddr T (partSepScale P chain e₁.x e₁.y))[(lcaScaleTree T
              (partSepScale P chain e₁.x e₁.y) (partSepScale P chain e₁.s e₁.x)).length]?).getD 1]) - 1,
          Nat.lt_succ_of_le hmPrev₁⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
            (partSepScale P chain e₁.s e₁.x)), Nat.lt_succ_of_le hmNu₁⟩) e₁.s).lo).hi := by
      simp only [hiShellOf, hmPrev₁, ↓reduceDIte]
      rw [hBprev_s₁]
    rw [hhi₁_eq] at hhi₁_lt_z
    -- Align `B_mid` and `B_prev` of `e₂` to `e₁` via `(hν_eq, hc₂_eq, hQ_eq)`
    have hBmid_eq :
        blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
          (partSepScale P chain e₂.s e₂.x) ++
          [((leafAddr T (partSepScale P chain e₂.x e₂.y))[(lcaScaleTree T
            (partSepScale P chain e₂.x e₂.y) (partSepScale P chain e₂.s e₂.x)).length]?).getD 1]),
          Nat.lt_succ_of_le hmMid₂⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
            (partSepScale P chain e₂.s e₂.x)), Nat.lt_succ_of_le hmNu₂⟩) e₂.s).lo =
        blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
          (partSepScale P chain e₁.s e₁.x) ++
          [((leafAddr T (partSepScale P chain e₁.x e₁.y))[(lcaScaleTree T
            (partSepScale P chain e₁.x e₁.y) (partSepScale P chain e₁.s e₁.x)).length]?).getD 1]),
          Nat.lt_succ_of_le hmMid₁⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
            (partSepScale P chain e₁.s e₁.x)), Nat.lt_succ_of_le hmNu₁⟩) e₁.s).lo := by
      rw [← hQ_eq]
      congr 2
      apply Fin.ext
      dsimp only
      rw [← hc₂_eq, ← hν_eq]
    have hBprev_eq :
        blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
          (partSepScale P chain e₂.s e₂.x) ++
          [((leafAddr T (partSepScale P chain e₂.x e₂.y))[(lcaScaleTree T
            (partSepScale P chain e₂.x e₂.y) (partSepScale P chain e₂.s e₂.x)).length]?).getD 1]) - 1,
          Nat.lt_succ_of_le hmPrev₂⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
            (partSepScale P chain e₂.s e₂.x)), Nat.lt_succ_of_le hmNu₂⟩) e₂.s).lo =
        blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
          (partSepScale P chain e₁.s e₁.x) ++
          [((leafAddr T (partSepScale P chain e₁.x e₁.y))[(lcaScaleTree T
            (partSepScale P chain e₁.x e₁.y) (partSepScale P chain e₁.s e₁.x)).length]?).getD 1]) - 1,
          Nat.lt_succ_of_le hmPrev₁⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
            (partSepScale P chain e₁.s e₁.x)), Nat.lt_succ_of_le hmNu₁⟩) e₁.s).lo := by
      rw [← hQ_eq]
      congr 2
      apply Fin.ext
      dsimp only
      rw [← hc₂_eq, ← hν_eq]
    rw [← hQ_eq] at hs₂_le_Q
    rw [hBmid_eq] at hx₂_le_Bmid hBmid_lt_y₂
    rw [hBprev_eq] at hy₂_le_Bprev
    rcases hord with hs_lt | ⟨hs_eq, hj_lt⟩
    · obtain ⟨hs₁1, _, _, _, hz₁P⟩ := hOrd e₁ hr₁
      have hstep₁_lt : e₁.stepIdx < e₂.stepIdx := by
        rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂]
        exact popStepIdx_strict_mono proc hs₁1 hs_lt (by omega)
      have hstep₂_lt : e₂.stepIdx < proc.popStepIdx e₁.x := by
        rw [rInt_stepIdx_eq_popStepIdx proc hr₂]
        exact popStepIdx_strict_mono proc (by omega) (by omega) (by omega)
      have hτ_in : e₂.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hy₂_ls := (rInt_mem_leftSpine proc hr₂).2.1
      exact hFreeze e₁ hr₁ e₂.stepIdx hτ_in e₂.y hy₂_ls ⟨by omega, by omega⟩
    · have hstep : e₁.stepIdx = e₂.stepIdx := by
        rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂, hs_eq]
      have hz₁_le_x₂ := (rInt_same_step_order proc hBST hr₁ hr₂ hstep hj_lt).2
      omega
  have hs2_2A_card : s2_2A.card ≤ sigmaScaleTree T chain := by
    have hmaps : ∀ e ∈ s2_2A, tauKey e ∈ SigmaTarget :=
      fun e he => htau_maps e (Finset.mem_filter.mp he).1
    have hinj : Set.InjOn tauKey (s2_2A : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ htau
      rw [Finset.mem_coe] at he₁ he₂
      rcases lt_trichotomy e₁.s e₂.s with hs_lt | hs_eq | hs_gt
      · exact absurd (Or.inl hs_lt) (hs2_2A_no_lt he₁ he₂ htau)
      · rcases lt_trichotomy e₁.j e₂.j with hj_lt | hj_eq | hj_gt
        · exact absurd (Or.inr ⟨hs_eq, hj_lt⟩) (hs2_2A_no_lt he₁ he₂ htau)
        · have hr₁ : e₁ ∈ proc.rInt :=
            (Finset.mem_filter.mp (hs2_sub (Finset.mem_filter.mp he₁).1)).1
          have hr₂ : e₂ ∈ proc.rInt :=
            (Finset.mem_filter.mp (hs2_sub (Finset.mem_filter.mp he₂).1)).1
          have hstep : e₁.stepIdx = e₂.stepIdx := by
            rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂, hs_eq]
          exact rInt_same_step_eq proc hr₁ hr₂ hstep hj_eq
        · exact absurd (Or.inr ⟨hs_eq.symm, hj_gt⟩) (hs2_2A_no_lt he₂ he₁ htau.symm)
      · exact absurd (Or.inl hs_gt) (hs2_2A_no_lt he₂ he₁ htau.symm)
    rw [← hSigma_card]
    exact Finset.card_le_card_of_injOn tauKey hmaps hinj
  -- 2c. `s2_2B2a.card ≤ sigmaScaleTree T chain`
  have hs2_2B2a_next : ∀ e ∈ s2_2B2a,
      ∃ eNext ∈ proc.rInt,
        proc.nextCascadeRot? e = some eNext ∧
        eNext.stepIdx = e.stepIdx ∧ eNext.s = e.s ∧ eNext.j = e.j + 1 ∧ eNext.x = e.z ∧
        e.z ≤ hiShellOf e ∧ hiShellOf e < eNext.y := by
    intro e he
    obtain ⟨he_s2, hjne, hnot_lt_z⟩ := Finset.mem_filter.mp he
    obtain ⟨he_b2, _, hmPrev, hdisj⟩ := hs2_unpack e he_s2
    have hr_e : e ∈ proc.rInt := (Finset.mem_filter.mp he_b2).1
    obtain ⟨eNext, hr_next, hnext_eq, hstep_next, hs_next, hj_next, hx_next⟩ :=
      rInt_nextCascadeRot proc hr_e hjne
    have hhi_eq : hiShellOf e =
        (blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e.x e.y)
            (partSepScale P chain e.s e.x) ++
            [((leafAddr T (partSepScale P chain e.x e.y))[(lcaScaleTree T
              (partSepScale P chain e.x e.y) (partSepScale P chain e.s e.x)).length]?).getD 1]) - 1,
          Nat.lt_succ_of_le hmPrev⟩) e.s).hi := by
      simp only [hiShellOf, hmPrev, ↓reduceDIte]
    rw [← hhi_eq] at hdisj
    rcases hdisj with h1 | h2 | h3
    · exact absurd h1 hnot_lt_z
    · exact absurd h2 hjne
    · rw [hnext_eq] at h3
      simp only [Option.elim_some, decide_eq_true_eq] at h3
      exact ⟨eNext, hr_next, hnext_eq, hstep_next, hs_next, hj_next, hx_next,
        Nat.le_of_not_lt hnot_lt_z, h3⟩
  have hs2_2B2a_no_lt : ∀ {e₁ e₂ : InternalPopRot},
      e₁ ∈ s2_2B2a → e₂ ∈ s2_2B2a → tauKey e₁ = tauKey e₂ →
      (e₁.s < e₂.s ∨ (e₁.s = e₂.s ∧ e₁.j < e₂.j)) → False := by
    intro e₁ e₂ he₁ he₂ htau hord
    obtain ⟨e₁Next, hr₁_next, _, hstep₁_next, _, hj₁_next, hx₁_next, hz₁_le_hi, hhi₁_lt_ynext⟩ :=
      hs2_2B2a_next e₁ he₁
    obtain ⟨_, _, _, _, _, _, _, hz₂_le_hi, _⟩ := hs2_2B2a_next e₂ he₂
    obtain ⟨he₁_b2, hℓ₁M₁, _⟩ := hs2_unpack e₁ (Finset.mem_filter.mp he₁).1
    obtain ⟨he₂_b2, hℓ₁M₂, _⟩ := hs2_unpack e₂ (Finset.mem_filter.mp he₂).1
    have hr₁ : e₁ ∈ proc.rInt := (Finset.mem_filter.mp he₁_b2).1
    have hr₂ : e₂ ∈ proc.rInt := (Finset.mem_filter.mp he₂_b2).1
    obtain ⟨hmPrev₁, hmMid₁, hmNu₁, _, _, _, _, _, _, _, _, _, _, _, hBprev_s₁, _,
      _, _, hQ_lt_x₁, hx₁_le_Bmid, hBmid_lt_y₁, _, _, _⟩ :=
      b2_tree_geom hScale hChain hOrd he₁_b2 hℓ₁M₁
    obtain ⟨hmPrev₂, hmMid₂, hmNu₂, _, _, _, _, _, _, _, _, _, _, _, hBprev_s₂, _,
      _, hs₂_le_Q, _, hx₂_le_Bmid, hBmid_lt_y₂, hy₂_le_Bprev, _, _⟩ :=
      b2_tree_geom hScale hChain hOrd he₂_b2 hℓ₁M₂
    dsimp only [tauKey] at htau
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at htau
    rcases htau with ⟨hν_eq, hc₂_eq, hQ_eq⟩
    simp only [hmNu₁, hmNu₂, ↓reduceDIte] at hQ_eq
    have hhi₁_eq : hiShellOf e₁ =
        (blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
            (partSepScale P chain e₁.s e₁.x) ++
            [((leafAddr T (partSepScale P chain e₁.x e₁.y))[(lcaScaleTree T
              (partSepScale P chain e₁.x e₁.y) (partSepScale P chain e₁.s e₁.x)).length]?).getD 1]) - 1,
          Nat.lt_succ_of_le hmPrev₁⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
            (partSepScale P chain e₁.s e₁.x)), Nat.lt_succ_of_le hmNu₁⟩) e₁.s).lo).hi := by
      simp only [hiShellOf, hmPrev₁, ↓reduceDIte]; rw [hBprev_s₁]
    have hhi₂_eq : hiShellOf e₂ =
        (blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
            (partSepScale P chain e₂.s e₂.x) ++
            [((leafAddr T (partSepScale P chain e₂.x e₂.y))[(lcaScaleTree T
              (partSepScale P chain e₂.x e₂.y) (partSepScale P chain e₂.s e₂.x)).length]?).getD 1]) - 1,
          Nat.lt_succ_of_le hmPrev₂⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
            (partSepScale P chain e₂.s e₂.x)), Nat.lt_succ_of_le hmNu₂⟩) e₂.s).lo).hi := by
      simp only [hiShellOf, hmPrev₂, ↓reduceDIte]; rw [hBprev_s₂]
    have hBmid_eq :
        blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
          (partSepScale P chain e₂.s e₂.x) ++
          [((leafAddr T (partSepScale P chain e₂.x e₂.y))[(lcaScaleTree T
            (partSepScale P chain e₂.x e₂.y) (partSepScale P chain e₂.s e₂.x)).length]?).getD 1]),
          Nat.lt_succ_of_le hmMid₂⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
            (partSepScale P chain e₂.s e₂.x)), Nat.lt_succ_of_le hmNu₂⟩) e₂.s).lo =
        blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
          (partSepScale P chain e₁.s e₁.x) ++
          [((leafAddr T (partSepScale P chain e₁.x e₁.y))[(lcaScaleTree T
            (partSepScale P chain e₁.x e₁.y) (partSepScale P chain e₁.s e₁.x)).length]?).getD 1]),
          Nat.lt_succ_of_le hmMid₁⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
            (partSepScale P chain e₁.s e₁.x)), Nat.lt_succ_of_le hmNu₁⟩) e₁.s).lo := by
      rw [← hQ_eq]; congr 2; apply Fin.ext; dsimp only; rw [← hc₂_eq, ← hν_eq]
    have hBprev_eq :
        blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
          (partSepScale P chain e₂.s e₂.x) ++
          [((leafAddr T (partSepScale P chain e₂.x e₂.y))[(lcaScaleTree T
            (partSepScale P chain e₂.x e₂.y) (partSepScale P chain e₂.s e₂.x)).length]?).getD 1]) - 1,
          Nat.lt_succ_of_le hmPrev₂⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₂.x e₂.y)
            (partSepScale P chain e₂.s e₂.x)), Nat.lt_succ_of_le hmNu₂⟩) e₂.s).lo =
        blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
          (partSepScale P chain e₁.s e₁.x) ++
          [((leafAddr T (partSepScale P chain e₁.x e₁.y))[(lcaScaleTree T
            (partSepScale P chain e₁.x e₁.y) (partSepScale P chain e₁.s e₁.x)).length]?).getD 1]) - 1,
          Nat.lt_succ_of_le hmPrev₁⟩)
          (blockAt (chain ⟨mEnd T (lcaScaleTree T (partSepScale P chain e₁.x e₁.y)
            (partSepScale P chain e₁.s e₁.x)), Nat.lt_succ_of_le hmNu₁⟩) e₁.s).lo := by
      rw [← hQ_eq]; congr 2; apply Fin.ext; dsimp only; rw [← hc₂_eq, ← hν_eq]
    rw [hhi₁_eq] at hz₁_le_hi hhi₁_lt_ynext
    rw [hhi₂_eq, hBprev_eq] at hz₂_le_hi
    rw [← hQ_eq] at hs₂_le_Q
    rw [hBmid_eq] at hx₂_le_Bmid hBmid_lt_y₂
    rw [hBprev_eq] at hy₂_le_Bprev
    obtain ⟨hs₁1, _, _, hy₁z₁, _⟩ := hOrd e₁ hr₁
    obtain ⟨_, _, _, hy₂z₂, _⟩ := hOrd e₂ hr₂
    obtain ⟨_, _, _, hynext_znext, hznext_P⟩ := hOrd e₁Next hr₁_next
    rcases hord with hs_lt | ⟨hs_eq, hj_lt⟩
    · have hstep₁_lt : e₁.stepIdx < e₂.stepIdx := by
        rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂]
        exact popStepIdx_strict_mono proc hs₁1 hs_lt (by omega)
      have hstep₂_lt_x₁ : e₂.stepIdx < proc.popStepIdx e₁.x := by
        rw [rInt_stepIdx_eq_popStepIdx proc hr₂]
        exact popStepIdx_strict_mono proc (by omega) (by omega) (by omega)
      have hstep₂_lt_xnext : e₂.stepIdx < proc.popStepIdx e₁Next.x := by
        rw [rInt_stepIdx_eq_popStepIdx proc hr₂]
        exact popStepIdx_strict_mono proc (by omega) (by omega) (by omega)
      have hτ₁ : e₂.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hτ_next : e₂.stepIdx ∈ Finset.Icc (e₁Next.stepIdx + 1) (proc.popStepIdx e₁Next.x) :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      obtain ⟨_, hy₂_ls, hz₂_ls⟩ := rInt_mem_leftSpine proc hr₂
      have hf1 := hFreeze e₁ hr₁ e₂.stepIdx hτ₁ e₂.y hy₂_ls
      have hf2 := hFreeze e₁ hr₁ e₂.stepIdx hτ₁ e₂.z hz₂_ls
      have hf3 := hFreeze e₁Next hr₁_next e₂.stepIdx hτ_next e₂.y hy₂_ls
      have hf4 := hFreeze e₁Next hr₁_next e₂.stepIdx hτ_next e₂.z hz₂_ls
      omega
    · have hstep : e₁.stepIdx = e₂.stepIdx := by
        rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂, hs_eq]
      rcases eq_or_lt_of_le (show e₁Next.j ≤ e₂.j by omega) with hj_eq | hj_lt'
      · have heq_next : e₁Next = e₂ :=
          rInt_same_step_eq proc hr₁_next hr₂ (hstep₁_next.trans hstep) hj_eq
        rw [heq_next] at hhi₁_lt_ynext
        omega
      · have hynext_lt_x₂ :=
          (rInt_same_step_order proc hBST hr₁_next hr₂ (hstep₁_next.trans hstep) hj_lt').1
        omega
  have hs2_2B2a_card : s2_2B2a.card ≤ sigmaScaleTree T chain := by
    have hmaps : ∀ e ∈ s2_2B2a, tauKey e ∈ SigmaTarget :=
      fun e he => htau_maps e (Finset.mem_filter.mp he).1
    have hinj : Set.InjOn tauKey (s2_2B2a : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ htau
      rw [Finset.mem_coe] at he₁ he₂
      rcases lt_trichotomy e₁.s e₂.s with hs_lt | hs_eq | hs_gt
      · exact absurd (Or.inl hs_lt) (hs2_2B2a_no_lt he₁ he₂ htau)
      · rcases lt_trichotomy e₁.j e₂.j with hj_lt | hj_eq | hj_gt
        · exact absurd (Or.inr ⟨hs_eq, hj_lt⟩) (hs2_2B2a_no_lt he₁ he₂ htau)
        · have hr₁ : e₁ ∈ proc.rInt :=
            (Finset.mem_filter.mp (hs2_sub (Finset.mem_filter.mp he₁).1)).1
          have hr₂ : e₂ ∈ proc.rInt :=
            (Finset.mem_filter.mp (hs2_sub (Finset.mem_filter.mp he₂).1)).1
          have hstep : e₁.stepIdx = e₂.stepIdx := by
            rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂, hs_eq]
          exact rInt_same_step_eq proc hr₁ hr₂ hstep hj_eq
        · exact absurd (Or.inr ⟨hs_eq.symm, hj_gt⟩) (hs2_2B2a_no_lt he₂ he₁ htau.symm)
      · exact absurd (Or.inl hs_gt) (hs2_2B2a_no_lt he₂ he₁ htau.symm)
    rw [← hSigma_card]
    exact Finset.card_le_card_of_injOn tauKey hmaps hinj
  have hs2_card_le : s2.card ≤ P + 2 * sigmaScaleTree T chain := by
    have h1 := Finset.card_le_card hs2_cover
    have h2 := Finset.card_union_le (s2_top ∪ s2_2A) s2_2B2a
    have h3 := Finset.card_union_le s2_top s2_2A
    omega
  -- Conjunct 3: `(s2.card : ℝ) < 26 / 25 * P`
  have hs2_real_lt : (s2.card : ℝ) < (26 : ℝ) / 25 * (P : ℝ) := by
    have hSigma_lt : (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50 :=
      (h_5_1 P r M T hValid).2.2
    have hcast : (s2.card : ℝ) ≤ (P : ℝ) + 2 * (sigmaScaleTree T chain : ℝ) := by
      exact_mod_cast hs2_card_le
    linarith
  -- Conjunct 4: `(b2 P proc chain).card ≤ P + r * (s2.card + ee.card + b3.card)`
  let b2_straddle := (b2 P proc chain).filter (fun e => partSepScale P chain e.s e.x = M + 1)
  let b2_tree := (b2 P proc chain).filter (fun e => partSepScale P chain e.s e.x ≤ M)
  have hb2_cover : b2 P proc chain ⊆ b2_straddle ∪ b2_tree := by
    intro e he
    simp only [b2_straddle, b2_tree, Finset.mem_union, Finset.mem_filter]
    have hle : partSepScale P chain e.s e.x ≤ M + 1 := (Finset.mem_filter.mp he).2.2.2
    by_cases hM1 : partSepScale P chain e.s e.x = M + 1
    · exact Or.inl ⟨he, hM1⟩
    · exact Or.inr ⟨he, by omega⟩
  have hb2_straddle_card : b2_straddle.card ≤ P := by
    have hstrad_bounds : ∀ e ∈ b2_straddle,
        e.x ≤ (blockAt (chain (Fin.last M)) e.s).hi ∧
        (blockAt (chain (Fin.last M)) e.s).hi < e.y := by
      intro e he
      obtain ⟨he_b2, hℓ₁_M1⟩ := Finset.mem_filter.mp he
      obtain ⟨hr_e, _, hℓ₂_lt_ℓ₁, _⟩ := Finset.mem_filter.mp he_b2
      obtain ⟨hs1, hsx, hxy, _, hzP⟩ := hOrd e hr_e
      have hlast_sx : blockAt (chain (Fin.last M)) e.s = blockAt (chain (Fin.last M)) e.x := by
        apply (lt_partSepScale_iff hChain e.s e.x hs1 (by omega) (by omega) (by omega)
          (Fin.last M)).mp
        change M < partSepScale P chain e.s e.x
        omega
      have hx_le : e.x ≤ (blockAt (chain (Fin.last M)) e.s).hi := by
        rw [hlast_sx]
        exact (blockAt_mem_and_bounds (hChain.2.2.1 (Fin.last M))
          (u := e.x) (by omega) (by omega)).2.2.1
      have hlast_ne_xy : blockAt (chain (Fin.last M)) e.x ≠ blockAt (chain (Fin.last M)) e.y := by
        intro heq
        have := (lt_partSepScale_iff hChain e.x e.y (by omega) (by omega) (by omega) (by omega)
          (Fin.last M)).mpr heq
        change M < partSepScale P chain e.x e.y at this
        omega
      have hlt_xy := blockAt_hi_lt_lo_of_ne (hChain.2.2.1 (Fin.last M))
        (by omega) (le_of_lt hxy) (by omega) hlast_ne_xy
      have hy_lo := (blockAt_mem_and_bounds (hChain.2.2.1 (Fin.last M))
        (u := e.y) (by omega) (by omega)).2.1
      rw [← hlast_sx] at hlt_xy
      exact ⟨hx_le, by omega⟩
    have hmaps : ∀ e ∈ b2_straddle, e.s ∈ Finset.Icc 1 P := by
      intro e he
      have hr_e : e ∈ proc.rInt := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
      obtain ⟨hs1, _, _, _, hzP⟩ := hOrd e hr_e
      exact Finset.mem_Icc.mpr ⟨hs1, by omega⟩
    have hinj : Set.InjOn InternalPopRot.s (b2_straddle : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ hs_eq
      rw [Finset.mem_coe] at he₁ he₂
      obtain ⟨hx₁_le, hy₁_gt⟩ := hstrad_bounds e₁ he₁
      obtain ⟨hx₂_le, hy₂_gt⟩ := hstrad_bounds e₂ he₂
      rw [hs_eq] at hx₁_le hy₁_gt
      have hr₁ : e₁ ∈ proc.rInt := (Finset.mem_filter.mp (Finset.mem_filter.mp he₁).1).1
      have hr₂ : e₂ ∈ proc.rInt := (Finset.mem_filter.mp (Finset.mem_filter.mp he₂).1).1
      have hstep : e₁.stepIdx = e₂.stepIdx := by
        rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂, hs_eq]
      rcases lt_trichotomy e₁.j e₂.j with hj_lt | hj_eq | hj_gt
      · have := (rInt_same_step_order proc hBST hr₁ hr₂ hstep hj_lt).1
        omega
      · exact rInt_same_step_eq proc hr₁ hr₂ hstep hj_eq
      · have := (rInt_same_step_order proc hBST hr₂ hr₁ hstep.symm hj_gt).1
        omega
    have hle := Finset.card_le_card_of_injOn InternalPopRot.s hmaps hinj
    rw [Nat.card_Icc] at hle
    omega
  -- Digraph rank step on `b2_tree`
  let b2_to_b3 := b2_tree.filter (fun e =>
    (proc.nextCascadeRot? e).elim false (fun eNext => decide (eNext ∈ b3 P proc chain)) = true)
  let T_set := s2 ∪ (b2_tree ∩ eEnter P T proc chain) ∪ b2_to_b3
  let rk : InternalPopRot → ℕ := fun e =>
    (lcaScaleTree T (partSepScale P chain e.x e.y) (partSepScale P chain e.s e.x)).length
  have hRk_b2 : ∀ e ∈ b2_tree, rk e < r := by
    intro e he
    obtain ⟨he_b2, hℓ₁M⟩ := Finset.mem_filter.mp he
    obtain ⟨_, _, _, _, hν_len, _⟩ := b2_tree_geom hScale hChain hOrd he_b2 hℓ₁M
    exact hν_len
  have hInj_b2 : ∀ e₁ ∈ b2_tree, ∀ e₂ ∈ b2_tree, ∀ y,
      proc.nextCascadeRot? e₁ = some y → proc.nextCascadeRot? e₂ = some y → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ y hn₁ hn₂
    have hr₁ : e₁ ∈ proc.rInt := (Finset.mem_filter.mp (Finset.mem_filter.mp he₁).1).1
    have hr₂ : e₂ ∈ proc.rInt := (Finset.mem_filter.mp (Finset.mem_filter.mp he₂).1).1
    exact nextCascadeRot_inj proc hr₁ hr₂ hn₁ hn₂
  have hStep_b2 : ∀ e ∈ b2_tree, e ∉ T_set →
      ∃ eNext ∈ b2_tree, proc.nextCascadeRot? e = some eNext ∧ rk e < rk eNext := by
    intro e he hnot_T
    obtain ⟨he_b2, hℓ₁M⟩ := Finset.mem_filter.mp he
    have hr_e : e ∈ proc.rInt := (Finset.mem_filter.mp he_b2).1
    obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e hr_e
    have hnot_s2 : e ∉ s2 := fun h => hnot_T (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hnot_ee : e ∉ eEnter P T proc chain :=
      fun h => hnot_T (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, h⟩)))
    have hnot_b3 : e ∉ b2_to_b3 := fun h => hnot_T (Finset.mem_union_right _ h)
    obtain ⟨hmPrev, hmMid, hmNu, _, _, _, _, hmPrev_lt_ℓ₂, hℓ₂_le_mMid, hmMid_lt_ℓ₁, _,
      _, hBmid_s, _, hBprev_s, _, hs_ge_Bprev, _, _, _, hBmid_lt_y, _, hBprev_hi_le_P, hdepth⟩ :=
      b2_tree_geom hScale hChain hOrd he_b2 hℓ₁M
    -- Unpack `e ∉ s2`
    have hnot_s2_cond : ¬ (
        (blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e.x e.y)
            (partSepScale P chain e.s e.x) ++
            [((leafAddr T (partSepScale P chain e.x e.y))[(lcaScaleTree T
              (partSepScale P chain e.x e.y) (partSepScale P chain e.s e.x)).length]?).getD 1]) - 1,
          Nat.lt_succ_of_le hmPrev⟩) e.s).hi < e.z ∨
        e.j = e.h ∨
        (proc.nextCascadeRot? e).elim true (fun eNext => decide (
          (blockAt (chain ⟨mStart T (lcaScaleTree T (partSepScale P chain e.x e.y)
              (partSepScale P chain e.s e.x) ++
              [((leafAddr T (partSepScale P chain e.x e.y))[(lcaScaleTree T
                (partSepScale P chain e.x e.y) (partSepScale P chain e.s e.x)).length]?).getD 1]) - 1,
            Nat.lt_succ_of_le hmPrev⟩) e.s).hi < eNext.y)) = true) := by
      intro hcond
      apply hnot_s2
      change e ∈ s2Set P T proc chain
      simp only [s2Set, Finset.mem_filter]
      refine ⟨he_b2, ?_⟩
      simp only [hℓ₁M, ↓reduceIte, hmPrev, ↓reduceDIte]
      exact hcond
    rw [hBprev_s] at hnot_s2_cond
    have hjne : e.j ≠ e.h := fun h => hnot_s2_cond (Or.inr (Or.inl h))
    have hz_le_Bprev : e.z ≤ (blockAt (chain ⟨_, Nat.lt_succ_of_le hmPrev⟩)
        (blockAt (chain ⟨_, Nat.lt_succ_of_le hmNu⟩) e.s).lo).hi :=
      Nat.le_of_not_lt (fun h => hnot_s2_cond (Or.inl h))
    obtain ⟨eNext, hr_next, hnext_eq, _, hs_next, _, hx_next⟩ :=
      rInt_nextCascadeRot proc hr_e hjne
    have hynext_le_Bprev : eNext.y ≤ (blockAt (chain ⟨_, Nat.lt_succ_of_le hmPrev⟩)
        (blockAt (chain ⟨_, Nat.lt_succ_of_le hmNu⟩) e.s).lo).hi := by
      by_contra hgt
      apply hnot_s2_cond
      right; right
      rw [hnext_eq]
      simpa using Nat.lt_of_not_le hgt
    obtain ⟨hs1_next, hsx_next, hxy_next, hyz_next, hzP_next⟩ := hOrd eNext hr_next
    let fPrev : Fin (M + 1) := ⟨_, Nat.lt_succ_of_le hmPrev⟩
    let fMid : Fin (M + 1) := ⟨_, Nat.lt_succ_of_le hmMid⟩
    let ℓ₁_next := partSepScale P chain eNext.s eNext.x
    let ℓ₂_next := partSepScale P chain eNext.x eNext.y
    have h1_range := partSepScale_range (P := P) chain eNext.s eNext.x
      (by omega) (by omega) (by omega) (by omega)
    have h2_range := partSepScale_range (P := P) chain eNext.x eNext.y
      (by omega) (by omega) (by omega) (by omega)
    -- `ℓ₁_next ≤ mMid`
    have hℓ₁_next_le_mMid : ℓ₁_next ≤ mEnd T (lcaScaleTree T (partSepScale P chain e.x e.y)
        (partSepScale P chain e.s e.x) ++
        [((leafAddr T (partSepScale P chain e.x e.y))[(lcaScaleTree T
          (partSepScale P chain e.x e.y) (partSepScale P chain e.s e.x)).length]?).getD 1]) := by
      by_contra hgt
      have hlt_fMid : fMid.val < ℓ₁_next := Nat.lt_of_not_le hgt
      have heq_fMid := (lt_partSepScale_iff hChain eNext.s eNext.x
        (by omega) (by omega) (by omega) (by omega) fMid).mp hlt_fMid
      rw [hs_next, hx_next, hBmid_s] at heq_fMid
      have hz_le := (blockAt_mem_and_bounds (hChain.2.2.1 fMid)
        (u := e.z) (by omega) (by omega)).2.2.1
      rw [← heq_fMid] at hz_le
      omega
    -- `mPrev < ℓ₁_next` and `mPrev < ℓ₂_next`
    obtain ⟨hBprev_mem, _, _, _⟩ :=
      blockAt_mem_and_bounds (hChain.2.2.1 fPrev) (u := e.s) hs1 (by omega)
    rw [hBprev_s] at hBprev_mem
    have hBprev_xnext : blockAt (chain fPrev) eNext.x = blockAt (chain fPrev) eNext.s := by
      rw [hs_next, hBprev_s]
      obtain ⟨_, _, _, huniq⟩ :=
        blockAt_mem_and_bounds (hChain.2.2.1 fPrev) (u := eNext.x) (by omega) (by omega)
      exact ((huniq _ hBprev_mem).mpr ⟨by omega, by omega⟩).symm
    have hBprev_ynext : blockAt (chain fPrev) eNext.y = blockAt (chain fPrev) eNext.x := by
      rw [hBprev_xnext, hs_next, hBprev_s]
      obtain ⟨_, _, _, huniq⟩ :=
        blockAt_mem_and_bounds (hChain.2.2.1 fPrev) (u := eNext.y) (by omega) (by omega)
      exact ((huniq _ hBprev_mem).mpr ⟨by omega, hynext_le_Bprev⟩).symm
    have hmPrev_lt_ℓ₁_next : fPrev.val < ℓ₁_next :=
      (lt_partSepScale_iff hChain eNext.s eNext.x
        (by omega) (by omega) (by omega) (by omega) fPrev).mpr hBprev_xnext.symm
    have hmPrev_lt_ℓ₂_next : fPrev.val < ℓ₂_next :=
      (lt_partSepScale_iff hChain eNext.x eNext.y
        (by omega) (by omega) (by omega) (by omega) fPrev).mpr hBprev_ynext.symm
    -- Trichotomy on `(ℓ₁_next, ℓ₂_next)`
    rcases lt_trichotomy ℓ₁_next ℓ₂_next with hlt_next | heq_next | hgt_next
    · -- Contradicts `e ∉ eEnter`
      exfalso
      apply hnot_ee
      simp only [eEnter, Finset.mem_filter, Finset.mem_sdiff]
      have he_not_b1 : e ∉ b1 P proc chain := by
        intro hb1_e
        have h1 := (Finset.mem_filter.mp hb1_e).2.2.1
        have h2 := (Finset.mem_filter.mp he_b2).2.2.1
        omega
      refine ⟨⟨hr_e, fun h => he_not_b1 h.1⟩, ?_⟩
      rw [hnext_eq]
      simp only [Option.elim_some, decide_eq_true_eq, Finset.mem_union]
      by_cases hℓ₂_next_M : ℓ₂_next ≤ M
      · left
        simp only [b1, Finset.mem_filter]
        exact ⟨hr_next, h1_range.1, hlt_next, hℓ₂_next_M⟩
      · right
        have hℓ₂_next_eq : ℓ₂_next = M + 1 := by omega
        simp only [bLeafPre, Finset.mem_filter]
        refine ⟨hr_next, hℓ₂_next_eq, ?_⟩
        have hne_fMid : blockAt (chain fMid) e.s ≠ blockAt (chain fMid) eNext.x := by
          intro heq
          rw [hBmid_s] at heq
          have hx_le := (blockAt_mem_and_bounds (hChain.2.2.1 fMid)
            (u := eNext.x) (by omega) (by omega)).2.2.1
          rw [← heq] at hx_le
          omega
        have hhi_lt_lo := blockAt_hi_lt_lo_of_ne (hChain.2.2.1 fMid)
          hs1 (by omega) (by omega) hne_fMid
        have hlo_mono := (nestedChain_refine_bounds hChain
          (show fMid ≤ Fin.last M by change fMid.val ≤ M; exact hmMid)
          (u := eNext.x) (by omega) (by omega)).1
        have hs_le_hi := (blockAt_mem_and_bounds (hChain.2.2.1 fMid)
          (u := e.s) hs1 (by omega)).2.2.1
        omega
    · -- Contradicts `e ∉ b2_to_b3`
      exfalso
      apply hnot_b3
      simp only [b2_to_b3, Finset.mem_filter]
      refine ⟨he, ?_⟩
      rw [hnext_eq]
      simp only [Option.elim_some, decide_eq_true_eq, b3, Finset.mem_filter]
      exact ⟨hr_next, h1_range.1, heq_next, by omega⟩
    · -- Stays in `b2_tree` with strictly deeper `LCA_𝒯`!
      have heNext_b2 : eNext ∈ b2_tree := by
        simp only [b2_tree, b2, Finset.mem_filter]
        exact ⟨⟨hr_next, h2_range.1, hgt_next, h1_range.2⟩, by omega⟩
      exact ⟨eNext, heNext_b2, hnext_eq, hdepth ℓ₂_next ℓ₁_next hmPrev_lt_ℓ₂_next hgt_next hℓ₁_next_le_mMid⟩
  have hb2_tree_card_T : b2_tree.card ≤ r * T_set.card :=
    card_le_mul_of_bounded_rank_step b2_tree T_set r rk proc.nextCascadeRot?
      hRk_b2 hInj_b2 hStep_b2
  have hb2_to_b3_card : b2_to_b3.card ≤ (b3 P proc chain).card := by
    let g : InternalPopRot → InternalPopRot := fun e => (proc.nextCascadeRot? e).getD e
    have hmaps : ∀ e ∈ b2_to_b3, g e ∈ b3 P proc chain := by
      intro e he
      obtain ⟨_, hcond⟩ := Finset.mem_filter.mp he
      dsimp only [g]
      rcases hnext : proc.nextCascadeRot? e with _ | eNext
      · rw [hnext] at hcond; simp at hcond
      · rw [hnext] at hcond
        simpa using hcond
    have hinj : Set.InjOn g (b2_to_b3 : Set InternalPopRot) := by
      intro e₁ he₁ e₂ he₂ hgeq
      rw [Finset.mem_coe] at he₁ he₂
      obtain ⟨he₁_tree, hcond₁⟩ := Finset.mem_filter.mp he₁
      obtain ⟨he₂_tree, hcond₂⟩ := Finset.mem_filter.mp he₂
      rcases hn₁ : proc.nextCascadeRot? e₁ with _ | n₁
      · rw [hn₁] at hcond₁; simp at hcond₁
      rcases hn₂ : proc.nextCascadeRot? e₂ with _ | n₂
      · rw [hn₂] at hcond₂; simp at hcond₂
      have hn_eq : n₁ = n₂ := by simpa [g, hn₁, hn₂] using hgeq
      subst hn_eq
      exact hInj_b2 e₁ he₁_tree e₂ he₂_tree n₁ hn₁ hn₂
    exact Finset.card_le_card_of_injOn g hmaps hinj
  have hT_card_le : T_set.card ≤
      s2.card + (eEnter P T proc chain).card + (b3 P proc chain).card := by
    dsimp only [T_set]
    have h1 := Finset.card_union_le (s2 ∪ (b2_tree ∩ eEnter P T proc chain)) b2_to_b3
    have h2 := Finset.card_union_le s2 (b2_tree ∩ eEnter P T proc chain)
    have h3 : (b2_tree ∩ eEnter P T proc chain).card ≤ (eEnter P T proc chain).card :=
      Finset.card_le_card Finset.inter_subset_right
    omega
  have hb2_card_le : (b2 P proc chain).card ≤
      P + r * (s2.card + (eEnter P T proc chain).card + (b3 P proc chain).card) := by
    have hc1 := Finset.card_le_card hb2_cover
    have hc2 := Finset.card_union_le b2_straddle b2_tree
    have hmul : r * T_set.card ≤
        r * (s2.card + (eEnter P T proc chain).card + (b3 P proc chain).card) :=
      Nat.mul_le_mul_left r hT_card_le
    omega
  -- Conjunct 5: `((b2 P proc chain).card : ℝ) < (9 * C_casc + 353) * r * P`
  have hb2_real_lt : ((b2 P proc chain).card : ℝ) < (9 * C_casc + 353) * (r : ℝ) * (P : ℝ) := by
    have hee_lt : ((eEnter P T proc chain).card : ℝ) < (51 : ℝ) / 25 * (P : ℝ) :=
      (h_5_3 P r M T hValid proc).2.2.2.2.2.2.2
    have hb3_lt : ((b3 P proc chain).card : ℝ) < (9 * C_casc + 348) * (P : ℝ) :=
      (h_5_9 C_casc hCcasc P r M T hValid proc).2.2
    have hcast : ((b2 P proc chain).card : ℝ) ≤
        (P : ℝ) + (r : ℝ) * ((s2.card : ℝ) + ((eEnter P T proc chain).card : ℝ) +
          ((b3 P proc chain).card : ℝ)) := by
      exact_mod_cast hb2_card_le
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hPR_pos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
    have hsum_lt : (s2.card : ℝ) + ((eEnter P T proc chain).card : ℝ) +
        ((b3 P proc chain).card : ℝ) < (9 * C_casc + 352) * (P : ℝ) := by
      linarith
    have hmul_lt : (r : ℝ) * ((s2.card : ℝ) + ((eEnter P T proc chain).card : ℝ) +
        ((b3 P proc chain).card : ℝ)) < (r : ℝ) * ((9 * C_casc + 352) * (P : ℝ)) :=
      mul_lt_mul_of_pos_left hsum_lt (by linarith)
    have hP_le_rP : (P : ℝ) ≤ (r : ℝ) * (P : ℝ) :=
      le_mul_of_one_le_left (le_of_lt hPR_pos) hrR
    linarith [show (r : ℝ) * (P : ℝ) + (r : ℝ) * ((9 * C_casc + 352) * (P : ℝ)) =
      (9 * C_casc + 353) * (r : ℝ) * (P : ℝ) by ring]
  exact ⟨hs2_sub, hs2_card_le, hs2_real_lt, hb2_card_le, hb2_real_lt⟩


/-!
## 5. `thm_2_5_mod3_pass` (Scale-Tree Contraction Pass & Elementary Bisection Bound)
-/

private theorem cast_list_sum (xs : List ℕ) :
    ((xs.sum : ℕ) : ℝ) = (xs.map (fun k : ℕ => (k : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem rInt_subset_four_buckets {M P : ℕ} (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock)
    (hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P) :
    proc.rInt ⊆ bLeaf P proc chain ∪ b1 P proc chain ∪ b2 P proc chain ∪ b3 P proc chain := by
  intro e he
  obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e he
  have h1Range := partSepScale_range (P := P) chain e.s e.x hs1 (by omega) (by omega) (by omega)
  have h2Range := partSepScale_range (P := P) chain e.x e.y (by omega) (by omega) (by omega) (by omega)
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

private theorem bisect_bound (h_3_6 : Ty_lem_3_6_folded_laws) (h_5_2 : Ty_lem_5_2_bucket_leaf) :
    ∀ (P : ℕ), 1 ≤ P → ∀ proc : FoldedPopProcess P, proc.J ≤ P * (Nat.clog 2 P - 1) := by
  intro P
  induction P using Nat.strong_induction_on with
  | h P ih =>
    intro hP proc
    have h36 := h_3_6 P hP proc
    have hBST : ∀ τ ≤ proc.steps.length, (proc.treeAt τ).IsBST :=
      fun τ hτ => (h36.1.1 τ hτ).1
    have hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P := by
      intro e he
      obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := h36.2.1.2 e he
      exact ⟨h1, h2, h3, h4, h5⟩
    have hFreeze : ∀ e ∈ proc.rInt, ∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z) :=
      fun e he => (h36.2.1.2 e he).2.2.2.2.2.2
    by_cases hP3 : P ≤ 3
    · have hemp : proc.rInt = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        obtain ⟨h1, h2, h3, h4, h5⟩ := hOrd e he
        omega
      simp [FoldedPopProcess.J, hemp]
    · have hP4 : 4 ≤ P := by omega
      let q₁ := P / 2
      have hq₁_ge2 : 2 ≤ q₁ := by omega
      have hq₁_lt : q₁ < P := by omega
      have hq₂_ge2 : 2 ≤ P - q₁ := by omega
      let Q₁ : IntervalBlock := ⟨1, q₁⟩
      let Q₂ : IntervalBlock := ⟨q₁ + 1, P⟩
      have hQ₁_sz : Q₁.size = q₁ := by
        simp [Q₁, IntervalBlock.size, show 1 ≤ q₁ by omega]
      have hQ₂_sz : Q₂.size = P - q₁ := by
        simp only [Q₂, IntervalBlock.size, show q₁ + 1 ≤ P by omega, ↓reduceIte]
        omega
      let bisectChain : Fin 2 → List IntervalBlock :=
        fun i => if i.val = 0 then [⟨1, P⟩] else [Q₁, Q₂]
      have hChain : IsNestedPartitionChain P bisectChain := by
        refine ⟨hP, rfl, ?_, ?_⟩
        · intro i
          dsimp only [bisectChain]
          split_ifs with hi0
          · refine ⟨?_, trivial, rfl, rfl⟩
            intro C hC
            rw [List.mem_singleton] at hC
            subst hC
            exact ⟨le_rfl, hP, le_rfl⟩
          · refine ⟨?_, ⟨rfl, trivial⟩, rfl, rfl⟩
            intro C hC
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
            rcases hC with rfl | rfl
            · exact ⟨le_rfl, by dsimp [Q₁]; omega, by dsimp [Q₁]; omega⟩
            · exact ⟨by dsimp [Q₂]; omega, by dsimp [Q₂]; omega, le_rfl⟩
        · intro ℓ Y hY
          have hℓ0 : ℓ = 0 := Fin.ext (by omega)
          subst hℓ0
          change Y ∈ [Q₁, Q₂] at hY
          change ∃ X ∈ ([⟨1, P⟩] : List IntervalBlock), X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
          rcases hY with rfl | rfl
          · exact ⟨⟨1, P⟩, List.mem_singleton.mpr rfl, le_rfl, by dsimp [Q₁]; omega⟩
          · exact ⟨⟨1, P⟩, List.mem_singleton.mpr rfl, by dsimp [Q₂]; omega, le_rfl⟩
      have hQ₁_mem : Q₁ ∈ bisectChain (Fin.last 1) := List.mem_cons.mpr (Or.inl rfl)
      have hQ₂_mem : Q₂ ∈ bisectChain (Fin.last 1) :=
        List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))
      have hblock_Q₁ : ∀ u, 1 ≤ u → u ≤ q₁ → blockAt (bisectChain (Fin.last 1)) u = Q₁ := by
        intro u hu1 huq
        obtain ⟨_, _, _, huniq⟩ :=
          blockAt_mem_and_bounds (hChain.2.2.1 (Fin.last 1)) (u := u) hu1 (by omega)
        exact ((huniq Q₁ hQ₁_mem).mpr ⟨hu1, huq⟩).symm
      have hblock_Q₂ : ∀ u, q₁ < u → u ≤ P → blockAt (bisectChain (Fin.last 1)) u = Q₂ := by
        intro u huq huP
        obtain ⟨_, _, _, huniq⟩ :=
          blockAt_mem_and_bounds (hChain.2.2.1 (Fin.last 1)) (u := u) (by omega) huP
        exact ((huniq Q₂ hQ₂_mem).mpr ⟨show q₁ + 1 ≤ u by omega, huP⟩).symm
      have hQ₁_ne_Q₂ : Q₁ ≠ Q₂ := by
        intro heq
        have : Q₁.lo = Q₂.lo := congrArg IntervalBlock.lo heq
        dsimp [Q₁, Q₂] at this
        omega
      -- Bucket partition on `bisectChain` (`M = 1`): `b1 = ∅` and `b3 = ∅`
      have hrInt_sub : proc.rInt ⊆
          (b2 P proc bisectChain ∪ bLeafExit P proc bisectChain) ∪
          bLeafPre P proc bisectChain ∪ bLeafAct P proc bisectChain := by
        intro e he
        have h4 := rInt_subset_four_buckets proc bisectChain hOrd he
        obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e he
        simp only [Finset.mem_union] at h4 ⊢
        rcases h4 with ((hleaf | hb1_e) | hb2_e) | hb3_e
        · simp only [bLeaf, Finset.mem_filter] at hleaf
          have hsep2 : partSepScale P bisectChain e.x e.y = 2 := hleaf.2
          set Q := blockAt (bisectChain (Fin.last 1)) e.x
          by_cases hsQ : e.s < Q.lo
          · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨he, hsep2, hsQ⟩))
          · by_cases hzQ : Q.hi < e.z
            · exact Or.inl (Or.inl (Or.inr
                (Finset.mem_filter.mpr ⟨he, hsep2, Nat.le_of_not_lt hsQ, hzQ⟩)))
            · exact Or.inr
                (Finset.mem_filter.mpr ⟨he, hsep2, Nat.le_of_not_lt hsQ, Nat.le_of_not_lt hzQ⟩)
        · exfalso
          simp only [b1, Finset.mem_filter] at hb1_e
          omega
        · exact Or.inl (Or.inl (Or.inl hb2_e))
        · exfalso
          simp only [b3, Finset.mem_filter] at hb3_e
          have hs1_eq1 : partSepScale P bisectChain e.s e.x = 1 := by omega
          have hs2_eq1 : partSepScale P bisectChain e.x e.y = 1 := by omega
          have hne_sx : blockAt (bisectChain (Fin.last 1)) e.s ≠
              blockAt (bisectChain (Fin.last 1)) e.x := by
            intro heq
            have := (lt_partSepScale_iff hChain e.s e.x hs1 (by omega) (by omega) (by omega)
              (Fin.last 1)).mpr heq
            change 1 < partSepScale P bisectChain e.s e.x at this
            omega
          have hne_xy : blockAt (bisectChain (Fin.last 1)) e.x ≠
              blockAt (bisectChain (Fin.last 1)) e.y := by
            intro heq
            have := (lt_partSepScale_iff hChain e.x e.y (by omega) (by omega) (by omega) (by omega)
              (Fin.last 1)).mpr heq
            change 1 < partSepScale P bisectChain e.x e.y at this
            omega
          by_cases hx_q : e.x ≤ q₁
          · exact hne_sx ((hblock_Q₁ e.s hs1 (by omega)).trans (hblock_Q₁ e.x (by omega) hx_q).symm)
          · exact hne_xy ((hblock_Q₂ e.x (by omega) (by omega)).trans
              (hblock_Q₂ e.y (by omega) (by omega)).symm)
      -- Bound `(b2 ∪ bLeafExit).card ≤ q₁ - 1` via `e ↦ e.s ∈ Icc 1 (q₁ - 1)`
      have hb2_exit_card :
          (b2 P proc bisectChain ∪ bLeafExit P proc bisectChain).card ≤ q₁ - 1 := by
        have hcross : ∀ e ∈ b2 P proc bisectChain ∪ bLeafExit P proc bisectChain,
            e ∈ proc.rInt ∧ 1 ≤ e.s ∧ e.s ≤ q₁ - 1 ∧ e.x ≤ q₁ ∧ q₁ < e.z := by
          intro e he_u
          rcases Finset.mem_union.mp he_u with hb2_e | hexit_e
          · simp only [b2, Finset.mem_filter] at hb2_e
            obtain ⟨he, hs2_1, hs2_lt_s1, hs1_le2⟩ := hb2_e
            obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e he
            have hne_xy : blockAt (bisectChain (Fin.last 1)) e.x ≠
                blockAt (bisectChain (Fin.last 1)) e.y := by
              intro heq
              have := (lt_partSepScale_iff hChain e.x e.y (by omega) (by omega) (by omega) (by omega)
                (Fin.last 1)).mpr heq
              change 1 < partSepScale P bisectChain e.x e.y at this
              omega
            have hx_le_q : e.x ≤ q₁ := by
              by_contra hgt
              exact hne_xy ((hblock_Q₂ e.x (by omega) (by omega)).trans
                (hblock_Q₂ e.y (by omega) (by omega)).symm)
            have hy_gt_q : q₁ < e.y := by
              by_contra hle
              exact hne_xy ((hblock_Q₁ e.x (by omega) hx_le_q).trans
                (hblock_Q₁ e.y (by omega) (by omega)).symm)
            exact ⟨he, hs1, by omega, hx_le_q, by omega⟩
          · simp only [bLeafExit, Finset.mem_filter] at hexit_e
            obtain ⟨he, _, _, hz_gt⟩ := hexit_e
            obtain ⟨hs1, hsx, _, _, hzP⟩ := hOrd e he
            have hx_le_q : e.x ≤ q₁ := by
              by_contra hgt
              rw [hblock_Q₂ e.x (by omega) (by omega)] at hz_gt
              dsimp [Q₂] at hz_gt
              omega
            rw [hblock_Q₁ e.x (by omega) hx_le_q] at hz_gt
            dsimp [Q₁] at hz_gt
            exact ⟨he, hs1, by omega, hx_le_q, hz_gt⟩
        have hmaps : ∀ e ∈ b2 P proc bisectChain ∪ bLeafExit P proc bisectChain,
            e.s ∈ Finset.Icc 1 (q₁ - 1) := by
          intro e he
          obtain ⟨_, h1, h2, _, _⟩ := hcross e he
          exact Finset.mem_Icc.mpr ⟨h1, h2⟩
        have hinj : Set.InjOn InternalPopRot.s
            ((b2 P proc bisectChain ∪ bLeafExit P proc bisectChain : Finset InternalPopRot) :
              Set InternalPopRot) := by
          intro e₁ he₁ e₂ he₂ hs_eq
          rw [Finset.mem_coe] at he₁ he₂
          obtain ⟨hr₁, _, _, hx₁_le, hz₁_gt⟩ := hcross e₁ he₁
          obtain ⟨hr₂, _, _, hx₂_le, hz₂_gt⟩ := hcross e₂ he₂
          have hstep : e₁.stepIdx = e₂.stepIdx := by
            rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂, hs_eq]
          rcases lt_trichotomy e₁.j e₂.j with hj_lt | hj_eq | hj_gt
          · have := (rInt_same_step_order proc hBST hr₁ hr₂ hstep hj_lt).2
            omega
          · exact rInt_same_step_eq proc hr₁ hr₂ hstep hj_eq
          · have := (rInt_same_step_order proc hBST hr₂ hr₁ hstep.symm hj_gt).2
            omega
        have hle := Finset.card_le_card_of_injOn InternalPopRot.s hmaps hinj
        rw [Nat.card_Icc] at hle
        omega
      -- Bound `bLeafPre.card ≤ (P - q₁) - 1` via `e ↦ e.y ∈ Icc (q₁ + 2) P`
      have hpre_card : (bLeafPre P proc bisectChain).card ≤ P - q₁ - 1 := by
        have hpre_bounds : ∀ e ∈ bLeafPre P proc bisectChain,
            e ∈ proc.rInt ∧ 1 ≤ e.s ∧ e.s ≤ q₁ ∧ q₁ + 1 ≤ e.x ∧ q₁ + 2 ≤ e.y ∧ e.y < e.z ∧ e.z ≤ P := by
          intro e he_pre
          simp only [bLeafPre, Finset.mem_filter] at he_pre
          obtain ⟨he, _, hs_lt_lo⟩ := he_pre
          obtain ⟨hs1, hsx, hxy, hyz, hzP⟩ := hOrd e he
          have hx_gt_q : q₁ < e.x := by
            by_contra hle
            rw [hblock_Q₁ e.x (by omega) (by omega)] at hs_lt_lo
            dsimp [Q₁] at hs_lt_lo
            omega
          rw [hblock_Q₂ e.x hx_gt_q (by omega)] at hs_lt_lo
          dsimp [Q₂] at hs_lt_lo
          exact ⟨he, hs1, by omega, by omega, by omega, hyz, hzP⟩
        have hpre_no_lt : ∀ {e₁ e₂ : InternalPopRot},
            e₁ ∈ bLeafPre P proc bisectChain → e₂ ∈ bLeafPre P proc bisectChain →
            e₁.y = e₂.y → (e₁.s < e₂.s ∨ (e₁.s = e₂.s ∧ e₁.j < e₂.j)) → False := by
          intro e₁ e₂ he₁ he₂ hy_eq hord_s
          obtain ⟨hr₁, hs₁1, _, hx₁_ge, _, hy₁z₁, hz₁P⟩ := hpre_bounds e₁ he₁
          obtain ⟨hr₂, _, hs₂_le_q, _, _, _, _⟩ := hpre_bounds e₂ he₂
          obtain ⟨_, _, hxy₁, _, _⟩ := hOrd e₁ hr₁
          obtain ⟨_, _, hxy₂, _, _⟩ := hOrd e₂ hr₂
          rcases hord_s with hs_lt | ⟨hs_eq, hj_lt⟩
          · have hstep₁_lt : e₁.stepIdx < e₂.stepIdx := by
              rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂]
              exact popStepIdx_strict_mono proc hs₁1 hs_lt (by omega)
            have hstep₂_lt : e₂.stepIdx < proc.popStepIdx e₁.x := by
              rw [rInt_stepIdx_eq_popStepIdx proc hr₂]
              exact popStepIdx_strict_mono proc (by omega) (by omega) (by omega)
            have hτ : e₂.stepIdx ∈ Finset.Icc (e₁.stepIdx + 1) (proc.popStepIdx e₁.x) :=
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            have hy₂_ls := (rInt_mem_leftSpine proc hr₂).2.1
            exact hFreeze e₁ hr₁ e₂.stepIdx hτ e₂.y hy₂_ls ⟨by omega, by omega⟩
          · have hstep : e₁.stepIdx = e₂.stepIdx := by
              rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂, hs_eq]
            have := (rInt_same_step_order proc hBST hr₁ hr₂ hstep hj_lt).1
            omega
        have hmaps : ∀ e ∈ bLeafPre P proc bisectChain, e.y ∈ Finset.Icc (q₁ + 2) P := by
          intro e he
          obtain ⟨_, _, _, _, hy_ge, hyz, hzP⟩ := hpre_bounds e he
          exact Finset.mem_Icc.mpr ⟨hy_ge, by omega⟩
        have hinj : Set.InjOn InternalPopRot.y
            (bLeafPre P proc bisectChain : Set InternalPopRot) := by
          intro e₁ he₁ e₂ he₂ hy_eq
          rw [Finset.mem_coe] at he₁ he₂
          rcases lt_trichotomy e₁.s e₂.s with hs_lt | hs_eq | hs_gt
          · exact absurd (Or.inl hs_lt) (hpre_no_lt he₁ he₂ hy_eq)
          · rcases lt_trichotomy e₁.j e₂.j with hj_lt | hj_eq | hj_gt
            · exact absurd (Or.inr ⟨hs_eq, hj_lt⟩) (hpre_no_lt he₁ he₂ hy_eq)
            · have hr₁ := (hpre_bounds e₁ he₁).1
              have hr₂ := (hpre_bounds e₂ he₂).1
              have hstep : e₁.stepIdx = e₂.stepIdx := by
                rw [rInt_stepIdx_eq_popStepIdx proc hr₁, rInt_stepIdx_eq_popStepIdx proc hr₂, hs_eq]
              exact rInt_same_step_eq proc hr₁ hr₂ hstep hj_eq
            · exact absurd (Or.inr ⟨hs_eq.symm, hj_gt⟩) (hpre_no_lt he₂ he₁ hy_eq.symm)
          · exact absurd (Or.inl hs_gt) (hpre_no_lt he₂ he₁ hy_eq.symm)
        have hle := Finset.card_le_card_of_injOn InternalPopRot.y hmaps hinj
        rw [Nat.card_Icc] at hle
        omega
      -- Active leaf subprocesses via `lem_5_2_bucket_leaf`
      obtain ⟨_, _, _, _, _, subProcs, hAct_eq, _⟩ :=
        h_5_2 P hP le_rfl proc bisectChain hChain
      have hAct_sum : (bLeafAct P proc bisectChain).card =
          (subProcs Q₁ hQ₁_mem).J + (subProcs Q₂ hQ₂_mem).J := by
        rw [hAct_eq]
        change (([Q₁, Q₂] : List IntervalBlock).attach.map
          (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum = _
        simp
      -- `Nat.clog 2` halving arithmetic
      set c := Nat.clog 2 P
      have hP_le_pow : P ≤ 2 ^ c := (Nat.clog_le_iff_le_pow (by omega)).mp le_rfl
      have hc_ge2 : 2 ≤ c := by
        by_contra hlt
        have hc_le1 : c ≤ 1 := by omega
        have : 2 ^ c ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hc_le1
        omega
      have hpow_split : 2 ^ c = 2 * 2 ^ (c - 1) := by
        have hc_eq : c = (c - 1) + 1 := by omega
        conv_lhs => rw [hc_eq, Nat.pow_succ]
        ring
      have hq₁_le_pow : q₁ ≤ 2 ^ (c - 1) := by omega
      have hq₂_le_pow : P - q₁ ≤ 2 ^ (c - 1) := by omega
      have hclog_q₁ : Nat.clog 2 Q₁.size ≤ c - 1 := by
        rw [hQ₁_sz]
        exact (Nat.clog_le_iff_le_pow (by omega)).mpr hq₁_le_pow
      have hclog_q₂ : Nat.clog 2 Q₂.size ≤ c - 1 := by
        rw [hQ₂_sz]
        exact (Nat.clog_le_iff_le_pow (by omega)).mpr hq₂_le_pow
      have ih₁ : (subProcs Q₁ hQ₁_mem).J ≤ q₁ * (c - 2) := by
        have h1 := ih Q₁.size (by omega) (by omega) (subProcs Q₁ hQ₁_mem)
        have h2 : Nat.clog 2 Q₁.size - 1 ≤ c - 2 := by omega
        calc (subProcs Q₁ hQ₁_mem).J
            ≤ Q₁.size * (Nat.clog 2 Q₁.size - 1) := h1
          _ ≤ Q₁.size * (c - 2) := Nat.mul_le_mul_left Q₁.size h2
          _ = q₁ * (c - 2) := by rw [hQ₁_sz]
      have ih₂ : (subProcs Q₂ hQ₂_mem).J ≤ (P - q₁) * (c - 2) := by
        have h1 := ih Q₂.size (by omega) (by omega) (subProcs Q₂ hQ₂_mem)
        have h2 : Nat.clog 2 Q₂.size - 1 ≤ c - 2 := by omega
        calc (subProcs Q₂ hQ₂_mem).J
            ≤ Q₂.size * (Nat.clog 2 Q₂.size - 1) := h1
          _ ≤ Q₂.size * (c - 2) := Nat.mul_le_mul_left Q₂.size h2
          _ = (P - q₁) * (c - 2) := by rw [hQ₂_sz]
      have hJ_le : proc.J ≤
          (b2 P proc bisectChain ∪ bLeafExit P proc bisectChain).card +
          (bLeafPre P proc bisectChain).card +
          (bLeafAct P proc bisectChain).card := by
        unfold FoldedPopProcess.J
        have hu1 := Finset.card_le_card hrInt_sub
        have hu2 := Finset.card_union_le
          ((b2 P proc bisectChain ∪ bLeafExit P proc bisectChain) ∪ bLeafPre P proc bisectChain)
          (bLeafAct P proc bisectChain)
        have hu3 := Finset.card_union_le
          (b2 P proc bisectChain ∪ bLeafExit P proc bisectChain)
          (bLeafPre P proc bisectChain)
        omega
      have hmul_sum : q₁ * (c - 2) + (P - q₁) * (c - 2) + P = P * (c - 1) := by
        have hq_sum : q₁ + (P - q₁) = P := by omega
        have hc_sum : (c - 2) + 1 = c - 1 := by omega
        calc q₁ * (c - 2) + (P - q₁) * (c - 2) + P
            = (q₁ + (P - q₁)) * (c - 2) + P := by ring
          _ = P * (c - 2) + P * 1 := by rw [hq_sum, Nat.mul_one]
          _ = P * ((c - 2) + 1) := by ring
          _ = P * (c - 1) := by rw [hc_sum]
      omega

/-- **Theorem 2.5** (`thm:mod3-pass`, Scale-Tree Contraction Pass and Bisection Bound). -/
theorem thm_2_5_mod3_pass
    (h_3_6 : Ty_lem_3_6_folded_laws)
    (h_2_3 : Ty_thm_2_3_mod2_cascade)
    (h_5_1 : Ty_lem_5_1_tree_weights)
    (h_5_2 : Ty_lem_5_2_bucket_leaf)
    (h_5_3 : Ty_lem_5_3_bucket_b1)
    (h_5_9 : Ty_lem_5_9_bucket_b3_exit) :
    ∃ C_pass : ℝ, 0 < C_pass ∧
      ∀ (P : ℕ), 1 ≤ P → ∀ proc : FoldedPopProcess P,
        (∀ (r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
          let leaves := scaleTreePartitionChain T P M (Fin.last M)
          (∀ Q ∈ leaves, 1 ≤ Q.size ∧ Q.size < 2 * scaleS T P M) ∧
          (leaves.map IntervalBlock.size).sum = P ∧
          ∃ subProcs : (Q : IntervalBlock) → Q ∈ leaves → FoldedPopProcess Q.size,
            (proc.J : ℝ) ≤
              C_pass * (r : ℝ) * (P : ℝ) +
                ((leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum : ℝ)) ∧
        proc.J ≤ P * (Nat.clog 2 P - 1) := by
  obtain ⟨C_casc, hCcasc⟩ := h_2_3
  have hCcasc_pos : 0 < C_casc := hCcasc.1
  let C_pass : ℝ := 18 * C_casc + 706
  refine ⟨C_pass, by dsimp [C_pass]; linarith, ?_⟩
  intro P hP proc
  refine ⟨?_, bisect_bound h_3_6 h_5_2 P hP proc⟩
  intro r M T hValid
  set chain := scaleTreePartitionChain T P M
  set leaves := chain (Fin.last M)
  have hr1 : 1 ≤ r := hValid.2.1.1
  have hM1 : 1 ≤ M := hValid.2.1.2.1
  have hSizes := validScaleTree_leaf_sizes P r M T hValid
  have hChain := validScaleTree_isNestedPartitionChain P r M T hValid
  obtain ⟨_, _, _, hSum, _, subProcs, _, hLeafBound⟩ := h_5_2 P hP hM1 proc chain hChain
  refine ⟨hSizes, hSum, subProcs, ?_⟩
  have hOrd : ∀ e ∈ proc.rInt, 1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P := by
    intro e he
    obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := (h_3_6 P hP proc).2.1.2 e he
    exact ⟨h1, h2, h3, h4, h5⟩
  have hSub := rInt_subset_four_buckets proc chain hOrd
  have hCardUnion : proc.J ≤
      (bLeaf P proc chain).card + (b1 P proc chain).card +
      (b2 P proc chain).card + (b3 P proc chain).card := by
    unfold FoldedPopProcess.J
    have h1 := Finset.card_le_card hSub
    have h2 := Finset.card_union_le (bLeaf P proc chain ∪ b1 P proc chain ∪ b2 P proc chain)
      (b3 P proc chain)
    have h3 := Finset.card_union_le (bLeaf P proc chain ∪ b1 P proc chain) (b2 P proc chain)
    have h4 := Finset.card_union_le (bLeaf P proc chain) (b1 P proc chain)
    omega
  have hb1 : ((b1 P proc chain).card : ℝ) ≤ 3 * (r : ℝ) * (P : ℝ) := by
    have := le_of_lt (h_5_3 P r M T hValid proc).2.2.2.2.2.1
    exact_mod_cast this
  have hb3 := le_of_lt (h_5_9 C_casc hCcasc P r M T hValid proc).2.2
  have hb2 := le_of_lt
    (lem_5_10_bucket_b2 h_3_6 h_5_1 h_5_3 h_5_9 C_casc hCcasc P r M T hValid proc).2.2.2.2
  have hbLeafR : ((bLeaf P proc chain).card : ℝ) ≤
      2 * (P : ℝ) + (leaves.attach.map (fun ⟨Q, hQ⟩ => ((subProcs Q hQ).J : ℝ))).sum := by
    have hcast : (((leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum : ℕ) : ℝ) =
        (leaves.attach.map (fun ⟨Q, hQ⟩ => ((subProcs Q hQ).J : ℝ))).sum := by
      rw [cast_list_sum, List.map_map]
      rfl
    have hR : ((bLeaf P proc chain).card : ℝ) ≤
        2 * (P : ℝ) + (((leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum : ℕ) : ℝ) := by
      exact_mod_cast hLeafBound
    rwa [hcast] at hR
  have hJR : (proc.J : ℝ) ≤ ((bLeaf P proc chain).card : ℝ) + ((b1 P proc chain).card : ℝ) +
      ((b2 P proc chain).card : ℝ) + ((b3 P proc chain).card : ℝ) := by
    exact_mod_cast hCardUnion
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hPR : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
  have hExtra : (9 * C_casc + 350) * (P : ℝ) ≤ (9 * C_casc + 350) * (r : ℝ) * (P : ℝ) := by
    have h_nonneg : 0 ≤ (9 * C_casc + 350) * ((r : ℝ) - 1) * (P : ℝ) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hPR
    linarith [show (9 * C_casc + 350) * ((r : ℝ) - 1) * (P : ℝ) =
      (9 * C_casc + 350) * (r : ℝ) * (P : ℝ) - (9 * C_casc + 350) * (P : ℝ) by ring]
  dsimp [C_pass]
  linarith

end Solution.BucketB2Pass
