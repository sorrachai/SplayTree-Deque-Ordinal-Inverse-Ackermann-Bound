module

public import Challenge.Definitions
public import Solution.TreeFacts
public import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

@[expose] public section

namespace Solution.BucketB3GapsExit

open SplayTree BinaryTree

/-! ## Section 1: Scale-Tree Floors, Contiguous Partitions, and Sub-block Indexing -/

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

private theorem pathWeight_ge_four_of_nonempty (ξ : List ℕ) (hne : ξ ≠ [])
    (hξ : ∀ c ∈ ξ, 1 ≤ c) : 4 ≤ pathWeight ξ := by
  cases ξ with
  | nil => contradiction
  | cons c rest =>
    unfold pathWeight
    simp only [List.foldl_cons]
    have hc : 1 ≤ c := hξ c List.mem_cons_self
    have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => hξ x (List.mem_cons_of_mem c hx)
    have hinit : 4 ≤ 1 * (4 * c ^ 2) := by nlinarith
    suffices ∀ (xs : List ℕ), (∀ x ∈ xs, 1 ≤ x) → ∀ (init : ℕ), 4 ≤ init →
        4 ≤ xs.foldl (fun w x => w * (4 * x ^ 2)) init from
      this rest hrest (1 * (4 * c ^ 2)) hinit
    intro xs
    induction xs with
    | nil => intro _ init h; exact h
    | cons x xs ih =>
      intro hx init h
      simp only [List.foldl_cons]
      have hx1 : 1 ≤ x := hx x List.mem_cons_self
      apply ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
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

private theorem ackermann_two_pow_le : ∀ j : ℕ, 2 ^ (j + 1) ≤ ackermann 2 (j + 1)
  | 0 => by decide
  | j + 1 => by
    have hstep : ackermann 2 (j + 2) = 2 ^ (ackermann 2 (j + 1)) := rfl
    rw [hstep]
    have hlt : j + 2 ≤ 2 ^ (j + 1) := Nat.lt_two_pow_self
    exact Nat.pow_le_pow_right (by decide) (le_trans hlt (ackermann_two_pow_le j))

private theorem ackermann_ge_two_pow_self : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1
  | 0, hk => by omega
  | 1, _ => by decide
  | 2, _ => by decide
  | k + 3, _ => by
    have hstep : ackermann (k + 3) 1 = ackermann (k + 2) 2 := rfl
    -- By induction on i: for all i ≥ 1 and j ≥ 1, 2 ^ j ≤ ackermann i j, and ackermann i 2 ≥ 2 ^ (ackermann (i-1) 1)
    suffices ∀ (i j : ℕ), 1 ≤ i → 1 ≤ j → 2 ^ j ≤ ackermann i j ∧
        (2 ≤ i → j = 1 → 2 ^ (i + 1) ≤ ackermann i 2) by
      rw [hstep]
      have h := (this (k + 2) 1 (by omega) (by omega)).2 (by omega) rfl
      exact h
    intro i
    induction i with
    | zero => intro j hj _; omega
    | succ i ih =>
      cases i with
      | zero =>
        intro j _ _
        exact ⟨le_rfl, fun h => by omega⟩
      | succ i' =>
        intro j _ hj1
        have hrec : ∀ m : ℕ, 1 ≤ m → 2 ^ m ≤ ackermann (i' + 2) m := by
          intro m
          induction m with
          | zero => intro hm; omega
          | succ m' ihm =>
            intro _
            cases m' with
            | zero =>
              change 2 ^ 1 ≤ ackermann (i' + 1) 2
              have h22 := (ih 2 (by omega) (by omega)).1
              omega
            | succ m'' =>
              have hdef : ackermann (i' + 2) (m'' + 2) =
                  ackermann (i' + 1) (ackermann (i' + 2) (m'' + 1)) := rfl
              rw [hdef]
              have prev := ihm (by omega)
              have hpos : 1 ≤ ackermann (i' + 2) (m'' + 1) :=
                le_trans (Nat.one_le_pow _ _ (by omega)) prev
              have h1 := (ih (ackermann (i' + 2) (m'' + 1)) (by omega) hpos).1
              have hlt : m'' + 2 ≤ 2 ^ (m'' + 1) := Nat.lt_two_pow_self
              exact le_trans (Nat.pow_le_pow_right (by omega) (le_trans hlt prev)) h1
        refine ⟨hrec j hj1, ?_⟩
        intro _ rfl
        have hdef : ackermann (i' + 2) 2 = ackermann (i' + 1) (ackermann (i' + 2) 1) := rfl
        rw [hdef]
        have hbase : ackermann (i' + 2) 1 = ackermann (i' + 1) 2 := rfl
        rw [hbase]
        cases i' with
        | zero => decide
        | succ i'' =>
          have prev2 := (ih 1 (by omega) (by omega)).2 (by omega) rfl
          have hpos : 1 ≤ ackermann (i'' + 2) 2 :=
            le_trans (Nat.one_le_pow _ _ (by omega)) prev2
          have h1 := (ih (ackermann (i'' + 2) 2) (by omega) hpos).1
          have hexp : i'' + 4 ≤ 2 ^ (i'' + 3) := by
            have := @Nat.lt_two_pow_self (i'' + 3)
            omega
          exact le_trans (Nat.pow_le_pow_right (by omega) (le_trans hexp prev2)) h1

private theorem alpha0_pos (n : ℕ) : 1 ≤ alpha0 n := by
  unfold alpha0 invAckermann
  have hne : ({k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}).Nonempty := by
    refine ⟨max n 1, by omega, ?_⟩
    have h1 : n ≤ 2 ^ (max n 1) := by
      calc n ≤ max n 1 := le_max_left n 1
        _ ≤ 2 ^ (max n 1) := le_of_lt Nat.lt_two_pow_self
    exact le_trans h1 (ackermann_ge_two_pow_self (max n 1) (by omega))
  exact (Nat.sInf_mem hne).1

private theorem alpha0_ge_four_of_ge_64 {n : ℕ} (hn : 64 ≤ n) : 4 ≤ alpha0 n := by
  unfold alpha0 invAckermann
  have hne : ({k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}).Nonempty := by
    refine ⟨max n 1, by omega, ?_⟩
    have h1 : n ≤ 2 ^ (max n 1) :=
      le_trans (le_max_left n 1) (le_of_lt Nat.lt_two_pow_self)
    exact le_trans h1 (ackermann_ge_two_pow_self (max n 1) (by omega))
  have hmem := Nat.sInf_mem hne
  rcases hmem with ⟨hk1, hkn⟩
  set k := sInf {k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}
  by_contra hlt
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk_cases with h | h | h
  · rw [h] at hkn; change n ≤ 2 at hkn; omega
  · rw [h] at hkn; change n ≤ 4 at hkn; omega
  · rw [h] at hkn; change n ≤ 16 at hkn; omega

private theorem leafWeight_ge_four {r M : ℕ} {T : ScaleTree}
    (hScale : IsScaleTree r M T) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hM : ℓ ≤ M) :
    4 ≤ leafWeight T ℓ := by
  rcases hScale with ⟨_, _, _, hLeaves, hDepths⟩
  have hmem_leaves : ℓ ∈ T.leaves := by
    rw [hLeaves]
    exact List.mem_range'.mpr ⟨ℓ - 1, by omega, by omega⟩
  unfold ScaleTree.leaves at hmem_leaves
  rw [List.mem_map] at hmem_leaves
  obtain ⟨⟨s, addr⟩, hentry, hs⟩ := hmem_leaves
  dsimp at hs; subst s
  unfold leafWeight leafAddr
  cases hfp : T.leafEntries.find? (fun entry => entry.1 == ℓ) with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hfp (ℓ, addr) hentry
    simp at this
  | some p =>
    rcases p with ⟨s', addr'⟩
    dsimp only
    have hp_mem := List.mem_of_find?_eq_some hfp
    have hlen := (hDepths (s', addr') hp_mem).1
    have hne : addr' ≠ [] := by intro h; simp [h] at hlen
    exact pathWeight_ge_four_of_nonempty addr' hne (leafEntries_pos T (s', addr') hp_mem)

private theorem scaleI_ge_five {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hM : ℓ ≤ M) :
    5 ≤ scaleI T P ℓ := by
  rcases hValid with ⟨hP, hScale, hHalf⟩
  have hw : 4 ≤ leafWeight T ℓ := leafWeight_ge_four hScale h1 hM
  have hSprev_pos : 1 ≤ scaleS T P (ℓ - 1) := scaleS_pos T P hP (ℓ - 1)
  have ha_pos : 1 ≤ alpha0 (2 * scaleS T P (ℓ - 1)) := alpha0_pos _
  have hS_eq : scaleS T P ℓ = leafWeight T ℓ * (alpha0 (2 * scaleS T P (ℓ - 1)) + 1) ^ 2 := by
    cases ℓ with
    | zero => omega
    | succ ℓ' => simp [scaleS]
  have hS_ge16 : 16 ≤ scaleS T P ℓ := by
    rw [hS_eq]
    have hsq : 4 ≤ (alpha0 (2 * scaleS T P (ℓ - 1)) + 1) ^ 2 := by nlinarith
    nlinarith
  have hHalf_ℓ : 2 * scaleS T P ℓ ≤ scaleS T P (ℓ - 1) := by
    have hfin : ℓ - 1 < M := by omega
    have := hHalf ⟨ℓ - 1, hfin⟩
    have heq : (ℓ - 1) + 1 = ℓ := by omega
    simpa [heq] using this
  have h64 : 64 ≤ 2 * scaleS T P (ℓ - 1) := by omega
  have ha4 : 4 ≤ alpha0 (2 * scaleS T P (ℓ - 1)) := alpha0_ge_four_of_ge_64 h64
  unfold scaleI
  omega

/-! ## Section 2: BST, `leftSpine`, `rightReach`, and `RightRotReachable` Helpers -/

private theorem mem_iff_mem_keyFinset {α : Type} [DecidableEq α] (t : BinaryTree α) (x : α) :
    x ∈ t ↔ x ∈ keyFinset t := by
  induction t with
  | nil =>
    simp only [keyFinset, Finset.notMem_empty, iff_false]
    intro h; cases h
  | node k l r ihl ihr =>
    simp only [keyFinset, Finset.mem_insert, Finset.mem_union, ← ihl, ← ihr]
    constructor
    · intro h; cases h with
      | here => exact Or.inl rfl
      | left hl => exact Or.inr (Or.inl hl)
      | right hr => exact Or.inr (Or.inr hr)
    · rintro (rfl | hl | hr)
      · exact BinaryTree.Mem.here
      · exact BinaryTree.Mem.left hl
      · exact BinaryTree.Mem.right hr

private theorem leftSpine_nonempty_of_ne_nil {α : Type} {t : BinaryTree α} (hne : t ≠ .nil) :
    1 ≤ (leftSpine t).length := by
  cases t with
  | nil => contradiction
  | node k l r => simp [leftSpine]

private theorem mem_of_mem_leftSpine {α : Type} {t : BinaryTree α} {x : α}
    (hx : x ∈ leftSpine t) : x ∈ t := by
  induction t with
  | nil => simp [leftSpine] at hx
  | node k l r ihl _ =>
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with hl | rfl
    · exact .left (ihl hl)
    · exact .here

private theorem leftSpine_pairwise_lt {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) : (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl _ =>
    obtain ⟨hlt, _, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    simp only [leftSpine, List.pairwise_append, List.pairwise_singleton]
    refine ⟨ihl hl, trivial, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    exact hlt' a (mem_of_mem_leftSpine ha)

private theorem mem_dropLast_of_lt_mem {α : Type} [LinearOrder α] {xs : List α}
    (hpw : xs.Pairwise (· < ·)) {c q : α} (hc : c ∈ xs) (hq : q ∈ xs) (hlt : c < q) :
    c ∈ xs.dropLast := by
  cases xs using List.reverseRecOn with
  | nil => simp at hc
  | append_singleton init last =>
    rw [List.dropLast_concat]
    simp only [List.mem_append, List.mem_singleton] at hc hq
    rcases hc with hc_init | rfl
    · exact hc_init
    · exfalso
      rcases hq with hq_init | rfl
      · simp only [List.pairwise_append] at hpw
        have := hpw.2.2 q hq_init c (List.mem_singleton.mpr rfl)
        exact lt_asymm hlt this
      · exact lt_irrefl _ hlt

private theorem subtreeAtKey_self {α : Type} [LinearOrder α] (k : α) (l r : BinaryTree α) :
    subtreeAtKey (.node k l r) k = .node k l r := by
  simp [subtreeAtKey]

private theorem mem_of_mem_subtreeAtKey {α : Type} [LinearOrder α] {t : BinaryTree α} {u v : α}
    (hv : v ∈ subtreeAtKey t u) : v ∈ t := by
  induction t with
  | nil => simp [subtreeAtKey] at hv
  | node k l r ihl ihr =>
    unfold subtreeAtKey at hv
    split_ifs at hv with h1 h2
    · exact .left (ihl hv)
    · exact .right (ihr hv)
    · exact hv

private theorem rotateRightEdge_isBST {α : Type} [LinearOrder α] {t : BinaryTree α}
    (ht : t.IsBST) (x p : α) : (rotateRightEdge t x p).IsBST := by
  induction t with
  | nil => exact ht
  | node k l r ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    have mem_rot : ∀ {s : BinaryTree α} {w : α}, w ∈ rotateRightEdge s x p → w ∈ s := by
      intro s
      induction s with
      | nil => intro w hw; exact hw
      | node ks ls rs ihls ihrs =>
        intro w hw
        unfold rotateRightEdge at hw
        split_ifs at hw with hp1 hp2
        · rcases BinaryTree.mem_node_iff.mp hw with rfl | hL | hR
          · exact .here
          · exact .left (ihls hL)
          · exact .right hR
        · rcases BinaryTree.mem_node_iff.mp hw with rfl | hL | hR
          · exact .here
          · exact .left hL
          · exact .right (ihrs hR)
        · cases ls with
          | nil => dsimp only at hw; exact hw
          | node lx a b =>
            dsimp only at hw
            split_ifs at hw with hlx
            · rcases BinaryTree.mem_node_iff.mp hw with rfl | hA | hBC
              · exact .left .here
              · exact .left (.left hA)
              · rcases BinaryTree.mem_node_iff.mp hBC with rfl | hB | hC
                · exact .here
                · exact .left (.right hB)
                · exact .right hC
            · exact hw
    unfold rotateRightEdge
    split_ifs with hp1 hp2
    · exact SplayDeque.Direct.isBSTNode k _ r
        ((SplayDeque.Direct.forallTree_iff _ _).mpr fun w hw => hlt' w (mem_rot hw))
        hgt (ihl hl) hr
    · exact SplayDeque.Direct.isBSTNode k l _
        hlt ((SplayDeque.Direct.forallTree_iff _ _).mpr fun w hw => hgt' w (mem_rot hw))
        hl (ihr hr)
    · cases l with
      | nil => dsimp only; exact ht
      | node lx a b =>
        dsimp only
        split_ifs with hlx
        · obtain ⟨hlx_a, hlx_b, ha, hb⟩ := (SplayDeque.Direct.isBSTNode_iff lx a b).mp hl
          have hlx_b' := (SplayDeque.Direct.forallTree_iff _ _).mp hlx_b
          have hk_pos : lx < k := hlt' lx .here
          have hkr : SplayDeque.Direct.ForallTree (· < k) b :=
            (SplayDeque.Direct.forallTree_iff _ _).mpr fun w hw => hlt' w (.right hw)
          have h_k_bst : (BinaryTree.node k b r).IsBST :=
            SplayDeque.Direct.isBSTNode k b r hkr hgt hb hr
          have hlx_right : SplayDeque.Direct.ForallTree (lx < ·) (.node k b r) :=
            (SplayDeque.Direct.forallTree_iff _ _).mpr fun w hw => by
              rcases BinaryTree.mem_node_iff.mp hw with rfl | hB | hR
              · exact hk_pos
              · exact hlx_b' w hB
              · exact lt_trans hk_pos (hgt' w hR)
          exact SplayDeque.Direct.isBSTNode lx a (.node k b r) hlx_a hlx_right ha h_k_bst
        · exact ht

private theorem leftSpine_rotateRightEdge_sublist {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) :
    (leftSpine (rotateRightEdge t x p)).Sublist (leftSpine t) := by
  induction t with
  | nil => simp [rotateRightEdge, leftSpine]
  | node k l r ihl _ =>
    unfold rotateRightEdge
    split_ifs with hp1 hp2
    · simp only [leftSpine]
      exact ihl.append (List.Sublist.refl _)
    · simp only [leftSpine]
      exact List.Sublist.refl _
    · cases l with
      | nil => dsimp only; exact List.Sublist.refl _
      | node lx a b =>
        dsimp only
        split_ifs with hlx
        · simp only [leftSpine, List.append_assoc]
          exact List.Sublist.append (List.Sublist.refl _)
            (List.cons_sublist_cons.mpr (List.nil_sublist [k]))
        · exact List.Sublist.refl _

private theorem leftSpine_sublist_of_reachable {α : Type} [LinearOrder α]
    {t₁ t₂ : BinaryTree α} (h : RightRotReachable t₁ t₂) :
    (leftSpine t₂).Sublist (leftSpine t₁) := by
  induction h with
  | refl => exact List.Sublist.refl _
  | tail _ hstep ih =>
    rcases hstep with ⟨x, y, _, _, rfl⟩
    exact (leftSpine_rotateRightEdge_sublist _ x y).trans ih

/-- On a BST `t`, if `p ∈ leftSpine t` and `IsRightRotEdge t x p`, then:
1. `p ∉ leftSpine (rotateRightEdge t x p)`,
2. no element of `leftSpine t` lies strictly between `x` and `p`, and
3. `rightReach (rotateRightEdge t x p) x = rightReach t p`. -/
private theorem rotateRightEdge_leftSpine_props {t : BinaryTree ℕ} (ht : t.IsBST)
    {x p : ℕ} (hp_ls : p ∈ leftSpine t) (hedge : IsRightRotEdge t x p) :
    p ∉ leftSpine (rotateRightEdge t x p) ∧
    (∀ w ∈ leftSpine t, ¬ (x < w ∧ w < p)) ∧
    rightReach (rotateRightEdge t x p) x = rightReach t p := by
  rcases hedge with ⟨A, B, C, hp_mem, hsub⟩
  induction t with
  | nil => simp [leftSpine] at hp_ls
  | node k l r ihl _ =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hp_ls
    rcases hp_ls with hp_l | rfl
    · have hpk : p < k := hlt' p (mem_of_mem_leftSpine hp_l)
      unfold subtreeAtKey at hsub
      simp only [hpk, ↓reduceIte] at hsub
      have hedge_l : IsRightRotEdge l x p := ⟨A, B, C, mem_of_mem_leftSpine hp_l, hsub⟩
      obtain ⟨hnot_l, hno_mid_l, hreach_l⟩ := ihl hl hp_l (mem_of_mem_leftSpine hp_l) hsub
      have hrot_eq : rotateRightEdge (.node k l r) x p = .node k (rotateRightEdge l x p) r := by
        simp [rotateRightEdge, hpk]
      have hx_in_l : x ∈ l := by
        have hx_sub : x ∈ subtreeAtKey l p := by rw [hsub]; exact .left .here
        exact mem_of_mem_subtreeAtKey hx_sub
      have hxk : x < k := hlt' x hx_in_l
      refine ⟨?_, ?_, ?_⟩
      · rw [hrot_eq]
        simp only [leftSpine, List.mem_append, List.mem_singleton]
        rintro (h_in | rfl)
        · exact hnot_l h_in
        · exact lt_irrefl p hpk
      · intro w hw ⟨hxw, hwp⟩
        simp only [leftSpine, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw_l | rfl
        · exact hno_mid_l w hw_l ⟨hxw, hwp⟩
        · omega
      · rw [hrot_eq]
        unfold rightReach
        simp only [subtreeAtKey, hxk, hpk, ↓reduceIte]
        exact hreach_l
    · -- `p = k`
      simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
      injection hsub with _ hl_eq hr_eq
      subst l; subst r
      obtain ⟨hlx_a, hlx_b, _, _⟩ := (SplayDeque.Direct.isBSTNode_iff x A B).mp hl
      have hlx_a' := (SplayDeque.Direct.forallTree_iff _ _).mp hlx_a
      have hxp : x < p := hlt' x .here
      have hrot_eq : rotateRightEdge (.node p (.node x A B) C) x p = .node x A (.node p B C) := by
        simp [rotateRightEdge]
      refine ⟨?_, ?_, ?_⟩
      · rw [hrot_eq]
        simp only [leftSpine, List.mem_append, List.mem_singleton]
        rintro (hA | rfl)
        · have := hlx_a' p (mem_of_mem_leftSpine hA)
          omega
        · omega
      · intro w hw ⟨hxw, hwp⟩
        simp only [leftSpine, List.mem_append, List.mem_singleton] at hw
        rcases hw with (hA | rfl) | rfl
        · have := hlx_a' w (mem_of_mem_leftSpine hA)
          omega
        · omega
        · omega
      · rw [hrot_eq]
        unfold rightReach
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte, BinaryTree.maxKey?]
        cases C.maxKey? <;> rfl

/-- Along `leftSpine t` of a BST `t`, `rightReach t` is non-decreasing with index. -/
private theorem rightReach_leftSpine_mono {t : BinaryTree ℕ} (ht : t.IsBST) :
    ∀ {i j : ℕ}, i ≤ j → j < (leftSpine t).length →
      rightReach t ((leftSpine t)[i]?.getD 0) ≤ rightReach t ((leftSpine t)[j]?.getD 0) := by
  have maxKey_mem : ∀ {s : BinaryTree ℕ} {m : ℕ}, s.maxKey? = some m → m ∈ s := by
    intro s
    induction s with
    | nil => intro m h; simp [BinaryTree.maxKey?] at h
    | node k l r _ ihr =>
      intro m h
      unfold BinaryTree.maxKey? at h
      cases hr : r.maxKey? with
      | none => rw [hr] at h; injection h with h1; subst h1; exact .here
      | some m' => rw [hr] at h; injection h with h1; subst h1; exact .right (ihr hr)
  have maxKey_ge_of_bst : ∀ {s : BinaryTree ℕ}, s.IsBST → ∀ v ∈ s, v ≤ (s.maxKey?.getD 0) := by
    intro s
    induction s with
    | nil => intro _ v hv; cases hv
    | node k l r _ ihr =>
      intro hs v hv
      obtain ⟨hlt, hgt, _, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp hs
      have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
      have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
      unfold BinaryTree.maxKey?
      cases hrm : r.maxKey? with
      | none =>
        have hr_nil : r = .nil := by
          cases r with
          | nil => rfl
          | node rk rl rr =>
            unfold BinaryTree.maxKey? at hrm
            cases hrr : rr.maxKey? <;> simp [hrr] at hrm
        subst hr_nil
        simp only [Option.getD_some]
        rcases BinaryTree.mem_node_iff.mp hv with rfl | hL | hR
        · exact le_rfl
        · exact le_of_lt (hlt' v hL)
        · cases hR
      | some m =>
        simp only [Option.getD_some]
        have hm_in_r : m ∈ r := maxKey_mem hrm
        have hkm : k < m := hgt' m hm_in_r
        rcases BinaryTree.mem_node_iff.mp hv with rfl | hL | hR
        · exact le_of_lt hkm
        · exact le_of_lt (lt_trans (hlt' v hL) hkm)
        · have := ihr hr v hR
          simpa [hrm] using this
  induction t with
  | nil => intro i j _ hj; simp [leftSpine] at hj
  | node k l r ihl _ =>
    obtain ⟨hlt, _, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    intro i j hij hj
    simp only [leftSpine, List.length_append, List.length_singleton] at hj
    by_cases hjl : j < (leftSpine l).length
    · have hil : i < (leftSpine l).length := lt_of_le_of_lt hij hjl
      have hget_i : (leftSpine (.node k l r))[i]? = (leftSpine l)[i]? := by
        rw [leftSpine, List.getElem?_append_left hil]
      have hget_j : (leftSpine (.node k l r))[j]? = (leftSpine l)[j]? := by
        rw [leftSpine, List.getElem?_append_left hjl]
      rw [hget_i, hget_j]
      have hmem_i : (leftSpine l)[i]?.getD 0 ∈ leftSpine l := by
        rw [List.getElem?_eq_getElem hil]; simp
      have hmem_j : (leftSpine l)[j]?.getD 0 ∈ leftSpine l := by
        rw [List.getElem?_eq_getElem hjl]; simp
      have hlt_i : (leftSpine l)[i]?.getD 0 < k := hlt' _ (mem_of_mem_leftSpine hmem_i)
      have hlt_j : (leftSpine l)[j]?.getD 0 < k := hlt' _ (mem_of_mem_leftSpine hmem_j)
      have hrr_i : rightReach (.node k l r) ((leftSpine l)[i]?.getD 0) =
          rightReach l ((leftSpine l)[i]?.getD 0) := by
        simp [rightReach, subtreeAtKey, hlt_i]
      have hrr_j : rightReach (.node k l r) ((leftSpine l)[j]?.getD 0) =
          rightReach l ((leftSpine l)[j]?.getD 0) := by
        simp [rightReach, subtreeAtKey, hlt_j]
      rw [hrr_i, hrr_j]
      exact ihl hl hij hjl
    · have hj_eq : j = (leftSpine l).length := by omega
      subst hj_eq
      have hget_j : (leftSpine (.node k l r))[(leftSpine l).length]?.getD 0 = k := by
        rw [leftSpine, List.getElem?_append_right le_rfl]
        simp
      rw [hget_j]
      by_cases hil : i < (leftSpine l).length
      · have hget_i : (leftSpine (.node k l r))[i]?.getD 0 = (leftSpine l)[i]?.getD 0 := by
          rw [leftSpine, List.getElem?_append_left hil]
        rw [hget_i]
        set u := (leftSpine l)[i]?.getD 0
        unfold rightReach
        rw [subtreeAtKey_self]
        cases hm : (subtreeAtKey (.node k l r) u).maxKey? with
        | none => simp
        | some m =>
          simp only [Option.getD_some]
          have hm_in_sub : m ∈ subtreeAtKey (.node k l r) u := maxKey_mem hm
          have hm_in_tree : m ∈ BinaryTree.node k l r := mem_of_mem_subtreeAtKey hm_in_sub
          exact maxKey_ge_of_bst ht m hm_in_tree
      · have hi_eq : i = (leftSpine l).length := by omega
        rw [hi_eq, hget_j]

private theorem maxKey_eq_of_bst_keyFinset_eq {t₁ t₂ : BinaryTree ℕ}
    (ht₁ : t₁.IsBST) (ht₂ : t₂.IsBST) (hk : keyFinset t₁ = keyFinset t₂) :
    t₁.maxKey? = t₂.maxKey? := by
  have max_spec : ∀ {s : BinaryTree ℕ}, s.IsBST →
      (s.maxKey? = none ↔ keyFinset s = ∅) ∧
      (∀ m, s.maxKey? = some m → m ∈ keyFinset s ∧ ∀ v ∈ keyFinset s, v ≤ m) := by
    intro s
    induction s with
    | nil =>
      intro _
      refine ⟨by simp [BinaryTree.maxKey?, keyFinset], fun m hm => by simp [BinaryTree.maxKey?] at hm⟩
    | node k l r _ ihr =>
      intro hs
      obtain ⟨hlt, hgt, _, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp hs
      have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
      have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
      refine ⟨?_, ?_⟩
      · constructor
        · intro hm
          unfold BinaryTree.maxKey? at hm
          cases hrm : r.maxKey? <;> simp [hrm] at hm
        · intro he
          simp [keyFinset] at he
      · intro m hm
        unfold BinaryTree.maxKey? at hm
        cases hrm : r.maxKey? with
        | none =>
          rw [hrm] at hm; injection hm with h1; subst h1
          have hr_empty : keyFinset r = ∅ := (ihr hr).1.mp hrm
          refine ⟨by simp [keyFinset], fun v hv => ?_⟩
          simp only [keyFinset, Finset.mem_insert, Finset.mem_union, hr_empty,
            Finset.notMem_empty, or_false] at hv
          rcases hv with rfl | hl
          · exact le_rfl
          · exact le_of_lt (hlt' v ((mem_iff_mem_keyFinset l v).mpr hl))
        | some mr =>
          rw [hrm] at hm; injection hm with h1; subst h1
          obtain ⟨hmr_in, hmr_ge⟩ := (ihr hr).2 mr hrm
          have hkm : k < mr := hgt' mr ((mem_iff_mem_keyFinset r mr).mpr hmr_in)
          refine ⟨by simp [keyFinset, hmr_in], fun v hv => ?_⟩
          simp only [keyFinset, Finset.mem_insert, Finset.mem_union] at hv
          rcases hv with rfl | hl | hr_v
          · exact le_of_lt hkm
          · exact le_of_lt (lt_trans (hlt' v ((mem_iff_mem_keyFinset l v).mpr hl)) hkm)
          · exact hmr_ge v hr_v
  cases hm₁ : t₁.maxKey? with
  | none =>
    have he₁ := (max_spec ht₁).1.mp hm₁
    have he₂ : keyFinset t₂ = ∅ := hk.symm.trans he₁
    exact ((max_spec ht₂).1.mpr he₂).symm
  | some m₁ =>
    obtain ⟨hm₁_in, hm₁_ge⟩ := (max_spec ht₁).2 m₁ hm₁
    cases hm₂ : t₂.maxKey? with
    | none =>
      have he₂ := (max_spec ht₂).1.mp hm₂
      rw [hk, he₂] at hm₁_in
      simp at hm₁_in
    | some m₂ =>
      obtain ⟨hm₂_in, hm₂_ge⟩ := (max_spec ht₂).2 m₂ hm₂
      have h12 : m₁ ≤ m₂ := hm₂_ge m₁ (hk ▸ hm₁_in)
      have h21 : m₂ ≤ m₁ := hm₁_ge m₂ (hk.symm ▸ hm₂_in)
      exact congrArg some (le_antisymm h12 h21)

private theorem keyFinset_rotateRightEdge {α : Type} [LinearOrder α] [DecidableEq α]
    (t : BinaryTree α) (x p : α) :
    keyFinset (rotateRightEdge t x p) = keyFinset t := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    unfold rotateRightEdge
    split_ifs with hp1 hp2
    · simp [keyFinset, ihl]
    · simp [keyFinset, ihr]
    · cases l with
      | nil => rfl
      | node lx a b =>
        dsimp only
        split_ifs with hlx
        · ext w
          simp only [keyFinset, Finset.mem_insert, Finset.mem_union]
          tauto
        · rfl

private theorem rightReach_le_of_rotateRightEdge {t : BinaryTree ℕ} (ht : t.IsBST)
    {x p : ℕ} (hxp : x < p) (hedge : IsRightRotEdge t x p) (v : ℕ) :
    rightReach t v ≤ rightReach (rotateRightEdge t x p) v := by
  have maxKey_mem : ∀ {s : BinaryTree ℕ} {m : ℕ}, s.maxKey? = some m → m ∈ s := by
    intro s
    induction s with
    | nil => intro m h; simp [BinaryTree.maxKey?] at h
    | node k l r _ ihr =>
      intro m h
      unfold BinaryTree.maxKey? at h
      cases hr : r.maxKey? with
      | none => rw [hr] at h; injection h with h1; subst h1; exact .here
      | some m' => rw [hr] at h; injection h with h1; subst h1; exact .right (ihr hr)
  rcases hedge with ⟨A, B, C, hp_mem, hsub⟩
  induction t with
  | nil => cases hp_mem
  | node k l r ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    by_cases hpk : p < k
    · have hp_l : p ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hp_mem with rfl | hL | hR
        · exact absurd hpk (lt_irrefl _)
        · exact hL
        · exact absurd (lt_trans hpk (hgt' p hR)) (lt_irrefl _)
      simp only [subtreeAtKey, hpk, ↓reduceIte] at hsub
      have hrot : rotateRightEdge (.node k l r) x p = .node k (rotateRightEdge l x p) r := by
        simp [rotateRightEdge, hpk]
      rw [hrot]
      by_cases hvk : v < k
      · simp only [rightReach, subtreeAtKey, hvk, ↓reduceIte]
        exact ihl hl hp_l hsub
      · by_cases hkv : k < v
        · have hnot : ¬ v < k := not_lt_of_gt hkv
          simp [rightReach, subtreeAtKey, hnot, hkv]
        · have hveq : v = k := by omega
          subst v
          simp only [rightReach, subtreeAtKey, lt_irrefl, ↓reduceIte, BinaryTree.maxKey?]
          cases r.maxKey? <;> exact le_rfl
    · by_cases hkp : k < p
      · have hp_r : p ∈ r := by
          rcases BinaryTree.mem_node_iff.mp hp_mem with rfl | hL | hR
          · exact absurd hkp (lt_irrefl _)
          · exact absurd (lt_trans (hlt' p hL) hkp) (lt_irrefl _)
          · exact hR
        have hnot_pk : ¬ p < k := not_lt_of_gt hkp
        simp only [subtreeAtKey, hnot_pk, hkp, ↓reduceIte] at hsub
        have hrot : rotateRightEdge (.node k l r) x p = .node k l (rotateRightEdge r x p) := by
          simp [rotateRightEdge, hnot_pk, hkp]
        rw [hrot]
        by_cases hvk : v < k
        · simp [rightReach, subtreeAtKey, hvk]
        · by_cases hkv : k < v
          · have hnot_vk : ¬ v < k := not_lt_of_gt hkv
            simp only [rightReach, subtreeAtKey, hnot_vk, hkv, ↓reduceIte]
            exact ihr hr hp_r hsub
          · have hveq : v = k := by omega
            subst v
            simp only [rightReach, subtreeAtKey, lt_irrefl, ↓reduceIte, BinaryTree.maxKey?]
            have hrm_eq : (rotateRightEdge r x p).maxKey? = r.maxKey? :=
              maxKey_eq_of_bst_keyFinset_eq (rotateRightEdge_isBST hr x p) hr
                (keyFinset_rotateRightEdge r x p)
            rw [hrm_eq]
      · have hpeq : p = k := by omega
        subst k
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l; subst r
        have hrot : rotateRightEdge (.node p (.node x A B) C) x p = .node x A (.node p B C) := by
          simp [rotateRightEdge]
        rw [hrot]
        rcases lt_trichotomy v x with hvx | hvx_eq | hx_lt_v
        · have hvp : v < p := lt_trans hvx hxp
          simp [rightReach, subtreeAtKey, hvx, hvp]
        · subst v
          simp only [rightReach, subtreeAtKey, hxp, lt_irrefl, ↓reduceIte]
          have h1 : ((BinaryTree.node x A B).maxKey?).getD 0 ≤ p := by
            unfold BinaryTree.maxKey?
            cases hbm : B.maxKey? with
            | none => simp; exact le_of_lt hxp
            | some mb =>
              simp only [Option.getD_some]
              exact le_of_lt (hlt' mb (.right (maxKey_mem hbm)))
          have h2 : p ≤ ((BinaryTree.node x A (.node p B C)).maxKey?).getD 0 := by
            simp only [BinaryTree.maxKey?]
            cases hcm : C.maxKey? with
            | none => simp
            | some mc =>
              simp only [Option.getD_some]
              exact le_of_lt (hgt' mc (maxKey_mem hcm))
          exact le_trans h1 h2
        · rcases lt_trichotomy v p with hvp | hvp_eq | hp_lt_v
          · have hnot_vx : ¬ v < x := not_lt_of_gt hx_lt_v
            simp [rightReach, subtreeAtKey, hvp, hnot_vx, hx_lt_v]
          · subst v
            have hnot_px : ¬ p < x := not_lt_of_gt hxp
            simp only [rightReach, subtreeAtKey, lt_irrefl, hnot_px, hxp, ↓reduceIte,
              BinaryTree.maxKey?]
            exact le_rfl
          · have hnot_vp : ¬ v < p := not_lt_of_gt hp_lt_v
            have hxv : x < v := lt_trans hxp hp_lt_v
            have hnot_vx : ¬ v < x := not_lt_of_gt hxv
            simp [rightReach, subtreeAtKey, hnot_vp, hp_lt_v, hnot_vx, hxv]

private theorem rightReach_le_of_reachable {t₁ t₂ : BinaryTree ℕ}
    (ht₁ : t₁.IsBST) (h : RightRotReachable t₁ t₂) (v : ℕ) :
    rightReach t₁ v ≤ rightReach t₂ v := by
  have bst_of_reach : ∀ {a b : BinaryTree ℕ}, a.IsBST → RightRotReachable a b → b.IsBST := by
    intro a b ha hab
    induction hab with
    | refl => exact ha
    | tail _ hstep ih =>
      rcases hstep with ⟨x, y, _, _, rfl⟩
      exact rotateRightEdge_isBST ih x y
  induction h with
  | refl => exact le_rfl
  | tail hprev hstep ih =>
    rcases hstep with ⟨x, y, hxy, hedge, rfl⟩
    exact le_trans ih (rightReach_le_of_rotateRightEdge (bst_of_reach ht₁ hprev) hxy hedge v)

/-! ## Section 2b: Partition Chain, Sub-blocks, `partSepScale`, and Scale-Tree `mEnd` -/

private theorem consecutiveBlocks_pairwise :
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

private theorem consecutiveBlocks_cover {bs : List IntervalBlock} {a b u : ℕ}
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
      exact ⟨B₁, List.mem_singleton_self _, by omega, by omega⟩
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

private theorem consecutiveBlocks_append {xs ys : List IntervalBlock}
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

private theorem splitIntervalBySize_props (X : IntervalBlock) (S : ℕ) (hX : X.lo ≤ X.hi) :
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
  · rw [not_or, not_lt] at hsmall
    rcases hsmall with ⟨hS0, h2S⟩
    have hS1 : 1 ≤ S := by omega
    set K := sz / S
    have hK2 : 2 ≤ K := by
      have : 2 * S ≤ sz := h2S
      exact (Nat.le_div_iff_mul_le hS1).mpr (by omega)
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
        omega
      · have hidx_eq : idx = K - 1 := by omega
        subst hidx_eq
        have h1 : (K - 1) * S + S = K * S := by
          have : K - 1 + 1 = K := by omega
          nlinarith
        omega
    · -- `ConsecutiveBlocks ((List.range K).map f)`
      suffices ∀ m : ℕ, m ≤ K → ConsecutiveBlocks ((List.range m).map f) from
        this K le_rfl
      intro m
      induction m with
      | zero => intro _; simp [ConsecutiveBlocks]
      | succ m ihm =>
        intro hmK
        rw [List.range_succ, List.map_append, List.map_singleton]
        apply consecutiveBlocks_append (ihm (by omega)) (by simp [ConsecutiveBlocks])
        intro last first hlast hfirst
        simp at hfirst; subst hfirst
        cases m with
        | zero => simp at hlast
        | succ m' =>
          rw [List.range_succ, List.map_append, List.map_singleton,
            List.getLast?_append_of_ne_nil _ (by simp)] at hlast
          simp at hlast; subst hlast
          have hm'_lt : m' + 1 < K := by omega
          have hpos_prod : 1 ≤ (m' + 1) * S := by nlinarith
          simp only [f, hm'_lt, ↓reduceIte]
          split_ifs <;> (dsimp only; omega)
    · -- `head?`
      have hK_pos : 0 < K := by omega
      rw [List.head?_map, List.head?_range]
      simp only [Nat.pos_iff_ne_zero.mp hK_pos, ↓reduceIte, Option.map_some]
      have : 0 + 1 < K := by omega
      simp [this]
    · -- `getLast?`
      have hrange : List.range K = List.range (K - 1) ++ [K - 1] := by
        conv_lhs => rw [show K = (K - 1) + 1 by omega]
        exact List.range_succ
      rw [hrange, List.map_append, List.map_singleton,
        List.getLast?_append_of_ne_nil _ (by simp)]
      simp only [List.getLast?_singleton, Option.map_some]
      have : ¬ (K - 1 + 1 < K) := by omega
      simp [this]

private theorem validScaleTree_chain {P r M : ℕ} {T : ScaleTree}
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
      intro C hC; simp at hC; subst hC; dsimp; exact ⟨le_rfl, hP, le_rfl⟩
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
      -- Prove flatMap properties by induction on `xs : List IntervalBlock`
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
              have hl' : last.hi = X.hi := by
                rw [hl] at s_lt
                simpa using s_lt
              have hf' : first.lo = X₂.lo := by
                rw [hf] at r_hd
                simpa using r_hd
              omega
            · rw [List.head?_append_of_ne_nil _ s_ne]
              simpa using s_hd
            · rw [List.getLast?_append_of_ne_nil _ r_ne]
              simpa using r_lt
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
            have e1 : some fOut.lo = some 1 := by
              simpa [hh, hheadP, hflo] using out_hd
            have e2 : some lOut.hi = some P := by
              simpa [hl, hlastP, hlhi] using out_lt
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
  · intro ℓ
    exact (hlevel ℓ.val).2.1
  · intro ℓ Y hY
    exact (hlevel (ℓ.val + 1)).2.2 ℓ.val rfl Y hY

private theorem contiguousPartition_nodup {N : ℕ} {parts : List IntervalBlock}
    (hPart : IsContiguousBlockPartition N parts) : parts.Nodup := by
  have hpw := consecutiveBlocks_pairwise (fun C hC => (hPart.1 C hC).2.1) hPart.2.1
  have hle : ∀ C ∈ parts, C.lo ≤ C.hi := fun C hC => (hPart.1 C hC).2.1
  clear hPart
  induction parts with
  | nil => exact .nil
  | cons C rest ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.nodup_cons]
    refine ⟨fun hmem => ?_, ih hpw.2 (fun B hB => hle B (List.mem_cons_of_mem _ hB))⟩
    have hlt := hpw.1 C hmem
    have hCle := hle C List.mem_cons_self
    omega

private theorem blockAt_mem_and_unique {N : ℕ} {parts : List IntervalBlock}
    (hN : 1 ≤ N) (hPart : IsContiguousBlockPartition N parts) :
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

private theorem childSubblocks_eq_split {P r M : ℕ} {T : ScaleTree}
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
    · -- `X = X₁`: every `Y ∈ splitIntervalBySize X S` satisfies predicate; every `Y` in `rest` fails!
      obtain ⟨_, s_b, _, _, _⟩ := splitIntervalBySize_props X S (hbounds X List.mem_cons_self).2.1
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
    · -- `X ∈ rest`: every `Y ∈ splitIntervalBySize X₁ S` fails predicate!
      obtain ⟨_, s_b, _, _, _⟩ := splitIntervalBySize_props X₁ S (hbounds X₁ List.mem_cons_self).2.1
      have hleft : (splitIntervalBySize X₁ S).filter
          (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro Y hY
        obtain ⟨_, h2, h3⟩ := s_b Y hY
        have hlt := hpw.1 X hX_rest
        simp; omega
      rw [hleft, List.nil_append]
      exact ih hpw.2 (fun B hB => hbounds B (List.mem_cons_of_mem _ hB)) hX_rest

private theorem findIdx?_eq_some_spec {α : Type*} (p : α → Bool) :
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

private theorem subblock1_props {P r M : ℕ} {T : ScaleTree}
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
      · have := hlt_idx (idx + 1) c hidx1 hlt hclen
        omega
      · have := hlt_idx c (idx + 1) hc1 hgt hidx_len
        omega
  refine ⟨hX1, hXle, hXP, s_ne, ?_, hlt_idx, ?_, ?_, ?_⟩
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
      rw [List.head?_eq_getElem?]
      exact List.getElem?_eq_getElem (by omega)
    rw [hget0] at s_hd
    simpa using s_hd
  · have hlen_pos : 1 ≤ subs.length := List.length_pos_of_ne_nil s_ne
    rw [hsub1_eq subs.length hlen_pos le_rfl]
    have hgetLast : subs.getLast? = some (subs[subs.length - 1]'(by omega)) := by
      rw [List.getLast?_eq_getElem?]
      exact List.getElem?_eq_getElem (by omega)
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

/-- Nested-chain coarsening: if `blockAt (chain k₂) u = blockAt (chain k₂) v` and `k₁ ≤ k₂`,
then `blockAt (chain k₁) u = blockAt (chain k₁) v`, and every `B₂ = blockAt (chain k₂) u` is
contained in `B₁ = blockAt (chain k₁) u`. -/
private theorem chain_blockAt_coarse {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain)
    {k₁ k₂ : Fin (M + 1)} (hk : k₁ ≤ k₂) {u : ℕ} (hu : u ∈ Finset.Icc 1 P) :
    (blockAt (chain k₁) u).lo ≤ (blockAt (chain k₂) u).lo ∧
    (blockAt (chain k₂) u).hi ≤ (blockAt (chain k₁) u).hi := by
  rcases hChain with ⟨hP, _, hPart, hNest⟩
  -- Prove by induction on `d := k₂.val - k₁.val`
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

private theorem partSepScale_props {M P : ℕ} {chain : Fin (M + 1) → List IntervalBlock}
    (hChain : IsNestedPartitionChain P chain) {u v : ℕ}
    (hu : u ∈ Finset.Icc 1 P) (hv : v ∈ Finset.Icc 1 P) :
    1 ≤ partSepScale P chain u v ∧ partSepScale P chain u v ≤ M + 1 ∧
    (partSepScale P chain u v = M + 1 ↔
      blockAt (chain (Fin.last M)) u = blockAt (chain (Fin.last M)) v) ∧
    (∀ ℓ : Fin M,
      (partSepScale P chain u v = ℓ.val + 1 ↔
        blockAt (chain ℓ.castSucc) u = blockAt (chain ℓ.castSucc) v ∧
        blockAt (chain ℓ.succ) u ≠ blockAt (chain ℓ.succ) v) ∧
      (ℓ.val + 1 < partSepScale P chain u v ↔
        blockAt (chain ℓ.succ) u = blockAt (chain ℓ.succ) v)) := by
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
    -- Prove on any `xs : List (Fin M)` with `xs.Pairwise (· < ·)`!
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
    refine ⟨List.find?_eq_none.trans ?_, fun i => ?_⟩
    · simp [List.mem_finRange]
    · constructor
      · intro hf
        obtain ⟨hpi, hprev⟩ := aux (List.finRange M) (List.pairwise_lt_finRange M) i hf
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
  set pred : Fin M → Bool := fun ℓ => decide (blockAt (chain ℓ.succ) u ≠ blockAt (chain ℓ.succ) v)
  have hsep_none : (List.finRange M).find? pred = none → partSepScale P chain u v = M + 1 := by
    intro hf
    unfold partSepScale
    simp only [hcond, ↓reduceIte]
    change (match (List.finRange M).find? pred with | some ℓ => ℓ.val + 1 | none => M + 1) = M + 1
    rw [hf]
  have hsep_some : ∀ ℓ, (List.finRange M).find? pred = some ℓ →
      partSepScale P chain u v = ℓ.val + 1 := by
    intro ℓ hf
    unfold partSepScale
    simp only [hcond, ↓reduceIte]
    change (match (List.finRange M).find? pred with | some ℓ => ℓ.val + 1 | none => M + 1) =
      ℓ.val + 1
    rw [hf]
  obtain ⟨hnone, hsome⟩ := find_finRange pred
  have hbounds : 1 ≤ partSepScale P chain u v ∧ partSepScale P chain u v ≤ M + 1 := by
    cases hf : (List.finRange M).find? pred with
    | none => rw [hsep_none hf]; omega
    | some ℓ => rw [hsep_some ℓ hf]; have := ℓ.isLt; omega
  refine ⟨hbounds.1, hbounds.2, ?_, ?_⟩
  · -- `partSepScale = M + 1 ↔ blockAt (Fin.last M) u = blockAt (Fin.last M) v`
    cases hf : (List.finRange M).find? pred with
    | none =>
      rw [hsep_none hf]
      constructor
      · intro _
        have hall := hnone.mp hf
        cases M with
        | zero => exact h0_same
        | succ M' =>
          have hlast := hall ⟨M', Nat.lt_succ_self M'⟩
          simp only [pred, decide_eq_false_iff_not, not_not] at hlast
          exact hlast
      · intro _; rfl
    | some ℓ =>
      rw [hsep_some ℓ hf]
      constructor
      · intro heq; have := ℓ.isLt; omega
      · intro hlast_same
        exfalso
        have hp_ℓ := (hsome ℓ).mp hf |>.1
        simp only [pred, decide_eq_true_eq] at hp_ℓ
        exact hp_ℓ (same_down (Fin.le_last _) hlast_same)
  · intro ℓ
    constructor
    · -- `partSepScale = ℓ.val + 1 ↔ ...`
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
    · -- `ℓ.val + 1 < partSepScale ↔ blockAt (chain ℓ.succ) u = blockAt (chain ℓ.succ) v`
      cases hf : (List.finRange M).find? pred with
      | none =>
        rw [hsep_none hf]
        constructor
        · intro _
          have hall := hnone.mp hf ℓ
          simp only [pred, decide_eq_false_iff_not, not_not] at hall
          exact hall
        · intro _; have := ℓ.isLt; omega
      | some ℓ' =>
        rw [hsep_some ℓ' hf]
        constructor
        · intro hlt
          obtain ⟨_, hprev⟩ := (hsome ℓ').mp hf
          have h_lt_fin : ℓ < ℓ' := Fin.mk_lt_mk.mpr (by omega)
          have hp_ℓ := hprev ℓ h_lt_fin
          simp only [pred, decide_eq_false_iff_not, not_not] at hp_ℓ
          exact hp_ℓ
        · intro hsame
          obtain ⟨hp_ℓ', _⟩ := (hsome ℓ').mp hf
          simp only [pred, decide_eq_true_eq] at hp_ℓ'
          by_contra hle
          have h_le_fin : ℓ'.succ ≤ ℓ.succ := Fin.mk_le_mk.mpr (by omega)
          exact hp_ℓ' (same_down h_le_fin hsame)

/-- Scale-tree LCA monotonicity needed for `𝒮_1` routing: for `1 ≤ ℓ₁ ≤ M`,
`ℓ₁ ≤ mEnd T (lcaScaleTree T ℓ₁ ℓ₂)`. -/
private theorem lcaScaleTree_mEnd_ge {r M : ℕ} {T : ScaleTree}
    (hScale : IsScaleTree r M T) {ℓ₁ : ℕ} (h1 : 1 ≤ ℓ₁) (hM : ℓ₁ ≤ M) (ℓ₂ : ℕ) :
    ℓ₁ ≤ mEnd T (lcaScaleTree T ℓ₁ ℓ₂) := by
  have lcp_prefix : ∀ (a b : List ℕ), longestCommonPrefix a b <+: a := by
    intro a
    induction a with
    | nil => intro _; exact List.nil_prefix
    | cons x xs ih =>
      intro b
      cases b with
      | nil => exact List.nil_prefix
      | cons y ys =>
        unfold longestCommonPrefix
        split_ifs with hxy
        · subst y
          rcases ih ys with ⟨t, ht⟩
          exact ⟨t, by simp [ht]⟩
        · exact List.nil_prefix
  -- Characterize `(s, c :: rest) ∈ leafEntriesChildren k cs`
  have child_step : ∀ (k : ℕ) (cs : List ScaleTree) (s c : ℕ) (rest : List ℕ),
      (s, c :: rest) ∈ ScaleTree.leafEntriesChildren k cs →
      k ≤ c ∧ ∃ hlt : c - k < cs.length,
        (s, rest) ∈ (cs[c - k]'hlt).leafEntries ∧
        (cs[c - k]'hlt).leaves.Sublist ((ScaleTree.leafEntriesChildren k cs).map Prod.fst) := by
    intro k cs
    induction cs generalizing k with
    | nil => intro s c rest h; simp [ScaleTree.leafEntriesChildren] at h
    | cons child tail ih =>
      intro s c rest h
      simp only [ScaleTree.leafEntriesChildren, List.mem_append, List.mem_map] at h
      rcases h with ⟨⟨s', r'⟩, hmem, heq⟩ | htail
      · injection heq with hs hc_eq
        injection hc_eq with hc_k hr_eq
        subst hs hc_k hr_eq
        refine ⟨le_rfl, ?_⟩
        refine ⟨by simp, by simpa using hmem, ?_⟩
        simp only [Nat.sub_self, List.getElem_cons_zero, ScaleTree.leafEntriesChildren,
          List.map_append, List.map_map]
        have hmap_eq : List.map (Prod.fst ∘ fun (x : ℕ × List ℕ) => (x.1, k :: x.2))
            child.leafEntries = child.leaves := rfl
        rw [hmap_eq]
        exact List.sublist_append_left _ _
      · obtain ⟨hkc, hlt_tail, hmem_c, hsub_c⟩ := ih (k + 1) s c rest htail
        refine ⟨by omega, ⟨by simp; omega, ?_, ?_⟩⟩
        · have hidx : c - k = (c - (k + 1)) + 1 := by omega
          simpa [hidx] using hmem_c
        · have hidx : c - k = (c - (k + 1)) + 1 := by omega
          simp only [hidx, List.getElem_cons_succ, ScaleTree.leafEntriesChildren, List.map_append]
          exact hsub_c.trans (List.sublist_append_right _ _)
  -- By structural induction on `ν : List ℕ`:
  have prefix_subtree : ∀ (ν addr : List ℕ) (S : ScaleTree) (s : ℕ),
      (s, addr) ∈ S.leafEntries → ν <+: addr →
      ∃ sub : ScaleTree, subtreeAtAddr S ν = some sub ∧
        s ∈ sub.leaves ∧ sub.leaves.Sublist S.leaves := by
    intro ν
    induction ν with
    | nil =>
      intro addr S s hmem _
      refine ⟨S, rfl, ?_, List.Sublist.refl _⟩
      unfold ScaleTree.leaves
      exact List.mem_map.mpr ⟨(s, addr), hmem, rfl⟩
    | cons c ν_rest ih =>
      intro addr S s hmem hpref
      rcases hpref with ⟨tail_addr, rfl⟩
      cases S with
      | leaf l =>
        simp [ScaleTree.leafEntries] at hmem
      | internal cs =>
        simp only [ScaleTree.leafEntries, List.cons_append] at hmem
        obtain ⟨hc1, hlt, hmem_child, hsub_child⟩ :=
          child_step 1 cs s c (ν_rest ++ tail_addr) hmem
        have hc0 : ¬ c = 0 := by omega
        obtain ⟨sub, hsub_at, hs_in, hsub_leaves⟩ :=
          ih (ν_rest ++ tail_addr) (cs[c - 1]'hlt) s hmem_child ⟨tail_addr, rfl⟩
        refine ⟨sub, ?_, hs_in, hsub_leaves.trans hsub_child⟩
        simp [subtreeAtAddr, hc0, List.getElem?_eq_getElem hlt, hsub_at]
  -- Apply to `ℓ₁` and `ν = lcaScaleTree T ℓ₁ ℓ₂`
  rcases hScale with ⟨_, _, _, hLeaves, _⟩
  have hmem_l1 : ℓ₁ ∈ T.leaves := by
    rw [hLeaves]
    exact List.mem_range'.mpr ⟨ℓ₁ - 1, by omega, by omega⟩
  obtain ⟨⟨s, addr⟩, hentry, hs⟩ := List.mem_map.mp hmem_l1
  dsimp at hs; subst s
  have haddr_mem : (ℓ₁, leafAddr T ℓ₁) ∈ T.leafEntries := by
    unfold leafAddr
    cases hfp : T.leafEntries.find? (fun entry => entry.1 == ℓ₁) with
    | none =>
      exfalso
      have := List.find?_eq_none.mp hfp (ℓ₁, addr) hentry
      simp at this
    | some p =>
      rcases p with ⟨s', addr'⟩
      have hp_mem := List.mem_of_find?_eq_some hfp
      have hp_eq := List.find?_some hfp
      simp at hp_eq; subst hp_eq
      exact hp_mem
  obtain ⟨sub, hsub_at, hs_in, hsub_list⟩ :=
    prefix_subtree (lcaScaleTree T ℓ₁ ℓ₂) (leafAddr T ℓ₁) T ℓ₁ haddr_mem
      (lcp_prefix _ _)
  unfold mEnd
  rw [hsub_at]
  dsimp only
  have hpw_T : T.leaves.Pairwise (· < ·) := by
    rw [hLeaves]
    exact List.pairwise_lt_range'
  have hpw_sub : sub.leaves.Pairwise (· < ·) := hpw_T.sublist hsub_list
  have hne_sub : sub.leaves ≠ [] := List.ne_nil_of_mem hs_in
  rw [List.getLast?_eq_some_getLast hne_sub, Option.getD_some]
  have le_last : ∀ (xs : List ℕ) (hne : xs ≠ []),
      xs.Pairwise (· < ·) → ℓ₁ ∈ xs → ℓ₁ ≤ xs.getLast hne := by
    intro xs
    induction xs with
    | nil => intro h; contradiction
    | cons a tail iht =>
      intro _ hpw_xs hmem_xs
      cases tail with
      | nil => simp at hmem_xs ⊢; omega
      | cons b tail' =>
        rw [List.pairwise_cons] at hpw_xs
        simp only [List.getLast_cons (List.cons_ne_nil _ _)]
        rcases List.mem_cons.mp hmem_xs with rfl | hmem_tail
        · exact le_of_lt (hpw_xs.1 _ (List.getLast_mem _))
        · exact iht (List.cons_ne_nil _ _) hpw_xs.2 hmem_tail
  exact le_last sub.leaves hne_sub hpw_sub hs_in

/-! ## Section 3: `FoldedPopProcess` Invariants, Lead-Exit Uniqueness, and Lemma 5.8 Part (1) -/

private theorem validFoldedOps_take_step {P : ℕ} {st : BinaryTree ℕ × Option ℕ}
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

private theorem proc_step_at {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ : τ < proc.steps.length) :
    (proc.steps[τ]).Valid P (proc.stateAt τ) ∧
    proc.stateAt (τ + 1) = (proc.steps[τ]).step (proc.stateAt τ) :=
  validFoldedOps_take_step proc.hValid hτ

private theorem proc_stateAt_zero {P : ℕ} (proc : FoldedPopProcess P) :
    proc.stateAt 0 = (.nil, none) := rfl

private theorem proc_stateAt_end {P : ℕ} (proc : FoldedPopProcess P) :
    proc.stateAt proc.steps.length = (.nil, none) := by
  unfold FoldedPopProcess.stateAt
  rw [List.take_length]
  exact proc.hEndEmpty

private theorem minKey_bst_props {t : BinaryTree ℕ} (ht : t.IsBST) :
    (t.minKey? = none ↔ t = .nil) ∧
    (∀ m, t.minKey? = some m → m ∈ t ∧ (∀ x ∈ t, m ≤ x) ∧ (leftSpine t).head? = some m ∧
      (spliceMin t).IsBST ∧ keyFinset (spliceMin t) = keyFinset t \ {m}) := by
  induction t with
  | nil =>
    refine ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun m h => ?_⟩
    simp [BinaryTree.minKey?] at h
  | node k l r ihl _ =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    obtain ⟨ihl_none, ihl_some⟩ := ihl hl
    have hnot_none : (BinaryTree.node k l r).minKey? ≠ none := by
      unfold BinaryTree.minKey?
      cases l.minKey? <;> simp
    refine ⟨⟨fun h => absurd h hnot_none, fun h => by cases h⟩, fun m hm => ?_⟩
    unfold BinaryTree.minKey? at hm
    cases hlm : l.minKey? with
    | none =>
      rw [hlm] at hm
      injection hm with hmk; subst m
      have hl_nil : l = .nil := ihl_none.mp hlm
      subst hl_nil
      refine ⟨.here, ?_, by simp [leftSpine], ?_, ?_⟩
      · intro x hx
        rcases BinaryTree.mem_node_iff.mp hx with rfl | hL | hR
        · exact le_rfl
        · cases hL
        · exact le_of_lt (hgt' x hR)
      · simpa [spliceMin] using hr
      · ext x
        simp only [spliceMin, keyFinset, Finset.empty_union, Finset.mem_sdiff,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hx
          refine ⟨Or.inr hx, ?_⟩
          rintro rfl
          exact lt_irrefl x (hgt' x ((mem_iff_mem_keyFinset r x).mpr hx))
        · rintro ⟨rfl | hx, hne⟩
          · exact absurd rfl hne
          · exact hx
    | some ml =>
      rw [hlm] at hm
      injection hm with hmk; subst hmk
      obtain ⟨hml_in, hml_le, hml_hd, hsp_bst, hsp_keys⟩ := ihl_some ml hlm
      have hl_ne : l ≠ .nil := by rintro rfl; simp [BinaryTree.minKey?] at hlm
      have hsp_eq : spliceMin (.node k l r) = .node k (spliceMin l) r := by
        cases l with
        | nil => contradiction
        | node lk ll lr => rfl
      have hml_lt_k : ml < k := hlt' ml hml_in
      refine ⟨.left hml_in, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rcases BinaryTree.mem_node_iff.mp hx with rfl | hL | hR
        · exact le_of_lt hml_lt_k
        · exact hml_le x hL
        · exact le_of_lt (lt_trans hml_lt_k (hgt' x hR))
      · simp only [leftSpine]
        have hls_ne : leftSpine l ≠ [] := by
          intro he; rw [he] at hml_hd; simp at hml_hd
        rw [List.head?_append_of_ne_nil _ hls_ne]
        exact hml_hd
      · rw [hsp_eq]
        refine SplayDeque.Direct.isBSTNode k (spliceMin l) r ?_ hgt hsp_bst hr
        rw [SplayDeque.Direct.forallTree_iff]
        intro x hx
        have hx_kf : x ∈ keyFinset (spliceMin l) := (mem_iff_mem_keyFinset _ x).mp hx
        rw [hsp_keys, Finset.mem_sdiff] at hx_kf
        exact hlt' x ((mem_iff_mem_keyFinset l x).mpr hx_kf.1)
      · rw [hsp_eq]
        ext x
        simp only [keyFinset, hsp_keys, Finset.mem_insert, Finset.mem_union,
          Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro (rfl | ⟨hxl, hxne⟩ | hxr)
          · exact ⟨Or.inl rfl, ne_of_gt hml_lt_k⟩
          · exact ⟨Or.inr (Or.inl hxl), hxne⟩
          · refine ⟨Or.inr (Or.inr hxr), ?_⟩
            rintro rfl
            exact absurd (lt_trans hml_lt_k (hgt' x ((mem_iff_mem_keyFinset r x).mpr hxr)))
              (lt_irrefl x)
        · rintro ⟨rfl | hxl | hxr, hxne⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨hxl, hxne⟩)
          · exact Or.inr (Or.inr hxr)

private theorem modifyLeftAt_push_bst_keys {t : BinaryTree ℕ} (ht : t.IsBST)
    {b w : ℕ} (hb : b ∈ leftSpine t) (hw : ∀ x ∈ t, w < x) :
    let t' := modifyLeftAt t b (fun L1 => .node w .nil L1)
    t'.IsBST ∧ keyFinset t' = insert w (keyFinset t) := by
  induction t with
  | nil => simp [leftSpine] at hb
  | node k l r ihl _ =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb_l | rfl
    · have hbk : b < k := hlt' b (mem_of_mem_leftSpine hb_l)
      obtain ⟨hl'_bst, hl'_keys⟩ := ihl hl hb_l (fun x hx => hw x (.left hx))
      have hmod : modifyLeftAt (.node k l r) b (fun L1 => .node w .nil L1) =
          .node k (modifyLeftAt l b (fun L1 => .node w .nil L1)) r := by
        simp [modifyLeftAt, hbk]
      dsimp only
      rw [hmod]
      refine ⟨?_, ?_⟩
      · refine SplayDeque.Direct.isBSTNode k _ r ?_ hgt hl'_bst hr
        rw [SplayDeque.Direct.forallTree_iff]
        intro x hx
        have hx_kf := (mem_iff_mem_keyFinset _ x).mp hx
        rw [hl'_keys, Finset.mem_insert] at hx_kf
        rcases hx_kf with rfl | hxl
        · exact hw k .here
        · exact hlt' x ((mem_iff_mem_keyFinset l x).mpr hxl)
      · ext x
        simp [keyFinset, hl'_keys, or_left_comm]
    · have hmod : modifyLeftAt (.node b l r) b (fun L1 => .node w .nil L1) =
          .node b (.node w .nil l) r := by
        simp [modifyLeftAt]
      dsimp only
      rw [hmod]
      have hwl_bst : (BinaryTree.node w .nil l).IsBST := by
        refine SplayDeque.Direct.isBSTNode w .nil l .left ?_ SplayDeque.Direct.isBSTNil hl
        rw [SplayDeque.Direct.forallTree_iff]
        exact fun x hx => hw x (.left hx)
      refine ⟨?_, ?_⟩
      · refine SplayDeque.Direct.isBSTNode b (.node w .nil l) r ?_ hgt hwl_bst hr
        rw [SplayDeque.Direct.forallTree_iff]
        intro x hx
        rcases BinaryTree.mem_node_iff.mp hx with rfl | h0 | hxl
        · exact hw b .here
        · cases h0
        · exact hlt' x hxl
      · ext x
        simp [keyFinset, or_left_comm]

private theorem foldl_rotateRightEdge_bst_keys (pairs : List (ℕ × ℕ)) :
    ∀ (t : BinaryTree ℕ), t.IsBST →
      let t' := pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t
      t'.IsBST ∧ keyFinset t' = keyFinset t := by
  induction pairs with
  | nil => intro t ht; exact ⟨ht, rfl⟩
  | cons p rest ih =>
    intro t ht
    simp only [List.foldl_cons]
    have ht1 : (rotateRightEdge t p.1 p.2).IsBST := rotateRightEdge_isBST ht p.1 p.2
    have hk1 : keyFinset (rotateRightEdge t p.1 p.2) = keyFinset t :=
      keyFinset_rotateRightEdge t p.1 p.2
    obtain ⟨hbst, hkeys⟩ := ih (rotateRightEdge t p.1 p.2) ht1
    exact ⟨hbst, hkeys.trans hk1⟩

private theorem proc_tree_bst_and_step_keys {P : ℕ} (proc : FoldedPopProcess P) :
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
        keyFinset (proc.treeAt (τ + 1)) = keyFinset (proc.treeAt τ) \ {s}) := by
  have step_one : ∀ (τ : ℕ) (hτ : τ < proc.steps.length),
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
        keyFinset (proc.treeAt (τ + 1)) = keyFinset (proc.treeAt τ) \ {s} := by
    intro τ hτ ht_bst ht_sub
    obtain ⟨hval, hst⟩ := proc_step_at proc hτ
    have ht_eq : proc.treeAt (τ + 1) = ((proc.steps[τ]'hτ).step (proc.stateAt τ)).1 :=
      congrArg Prod.fst hst
    cases hop : proc.steps[τ]'hτ with
    | push w =>
      rw [hop] at hval ht_eq
      rcases hval with ⟨hw1, hwP, hlt_all, hnil_iff, hb_ls⟩
      have hnot_in : w ∉ keyFinset (proc.treeAt τ) := by
        intro h; have := hlt_all w ((mem_iff_mem_keyFinset _ w).mpr h); exact lt_irrefl w this
      unfold FoldedOp.step at ht_eq
      cases hb : (proc.stateAt τ).2 with
      | none =>
        have htree_nil : proc.treeAt τ = .nil := hnil_iff.mpr hb
        rw [hb] at ht_eq
        dsimp only at ht_eq
        have hk1 : keyFinset (proc.treeAt (τ + 1)) = insert w (keyFinset (proc.treeAt τ)) := by
          rw [ht_eq, htree_nil]; simp [keyFinset]
        have hbst1 : (proc.treeAt (τ + 1)).IsBST := by
          rw [ht_eq]
          exact SplayDeque.Direct.isBSTNode w .nil .nil .left .left
            SplayDeque.Direct.isBSTNil SplayDeque.Direct.isBSTNil
        refine ⟨⟨hbst1, ?_⟩, hw1, hwP, hnot_in, hk1⟩
        rw [hk1]; exact Finset.insert_subset_iff.mpr ⟨Finset.mem_Icc.mpr ⟨hw1, hwP⟩, ht_sub⟩
      | some b =>
        rw [hb] at ht_eq
        dsimp only at ht_eq
        obtain ⟨hbst1, hk1⟩ := modifyLeftAt_push_bst_keys ht_bst (hb_ls b hb) hlt_all
        change (modifyLeftAt (proc.treeAt τ) b (fun L1 => .node w .nil L1)).IsBST at hbst1
        change keyFinset (modifyLeftAt (proc.treeAt τ) b (fun L1 => .node w .nil L1)) =
          insert w (keyFinset (proc.treeAt τ)) at hk1
        change proc.treeAt (τ + 1) = modifyLeftAt (proc.treeAt τ) b (fun L1 => .node w .nil L1) at ht_eq
        rw [← ht_eq] at hbst1 hk1
        refine ⟨⟨hbst1, ?_⟩, hw1, hwP, hnot_in, hk1⟩
        rw [hk1]; exact Finset.insert_subset_iff.mpr ⟨Finset.mem_Icc.mpr ⟨hw1, hwP⟩, ht_sub⟩
    | shift =>
      rw [hop] at hval ht_eq
      have hsame : proc.treeAt (τ + 1) = proc.treeAt τ := by
        rw [ht_eq]
        unfold FoldedOp.step
        cases (proc.stateAt τ).2 <;> rfl
      exact ⟨⟨hsame ▸ ht_bst, hsame ▸ ht_sub⟩, hsame⟩
    | upperRot u v =>
      rw [hop] at hval ht_eq
      have hrot : proc.treeAt (τ + 1) = rotateRightEdge (proc.treeAt τ) u v := ht_eq
      have hbst1 : (proc.treeAt (τ + 1)).IsBST := hrot ▸ rotateRightEdge_isBST ht_bst u v
      have hk1 : keyFinset (proc.treeAt (τ + 1)) = keyFinset (proc.treeAt τ) :=
        hrot ▸ keyFinset_rotateRightEdge (proc.treeAt τ) u v
      exact ⟨⟨hbst1, hk1 ▸ ht_sub⟩, hrot, hk1⟩
    | pop s =>
      rw [hop] at hval ht_eq
      rcases hval with ⟨b, _, hmin, hb, _⟩
      obtain ⟨hs_mem, _, _, hsp_bst, hsp_keys⟩ := (minKey_bst_props ht_bst).2 s hmin
      have hs_kf : s ∈ keyFinset (proc.treeAt τ) := (mem_iff_mem_keyFinset _ s).mp hs_mem
      unfold FoldedOp.step at ht_eq
      rw [hb] at ht_eq
      dsimp only at ht_eq
      by_cases hk0 : (takeThrough (leftSpine (proc.stateAt τ).1) b).length - 1 = 0
      · simp only [hk0, ↓reduceIte] at ht_eq
        change proc.treeAt (τ + 1) = spliceMin (proc.treeAt τ) at ht_eq
        rw [ht_eq]
        exact ⟨⟨hsp_bst, hsp_keys ▸ Finset.sdiff_subset.trans ht_sub⟩, hs_kf, hmin, hsp_keys⟩
      · simp only [hk0, ↓reduceIte] at ht_eq
        obtain ⟨hf_bst, hf_keys⟩ := foldl_rotateRightEdge_bst_keys
          ((adjacentPairs (takeThrough (leftSpine (proc.stateAt τ).1) b).tail).take
            (((takeThrough (leftSpine (proc.stateAt τ).1) b).length - 1 - 1) / 2))
          (spliceMin (proc.treeAt τ)) hsp_bst
        change proc.treeAt (τ + 1) = _ at ht_eq
        rw [ht_eq]
        have hkeys_final := hf_keys.trans hsp_keys
        exact ⟨⟨hf_bst, hkeys_final ▸ Finset.sdiff_subset.trans ht_sub⟩, hs_kf, hmin, hkeys_final⟩
  have inv_all : ∀ τ ≤ proc.steps.length,
      (proc.treeAt τ).IsBST ∧ keyFinset (proc.treeAt τ) ⊆ Finset.Icc 1 P := by
    intro τ
    induction τ with
    | zero =>
      intro _
      refine ⟨SplayDeque.Direct.isBSTNil, ?_⟩
      simp [FoldedPopProcess.treeAt, FoldedPopProcess.stateAt, keyFinset]
    | succ τ ih =>
      intro hle
      have hlt : τ < proc.steps.length := Nat.lt_of_succ_le hle
      obtain ⟨h1, h2⟩ := ih (le_of_lt hlt)
      exact (step_one τ hlt h1 h2).1
  exact ⟨inv_all, fun τ hτ =>
    (step_one τ hτ (inv_all τ (le_of_lt hτ)).1 (inv_all τ (le_of_lt hτ)).2).2⟩

private theorem popStepIdx_and_insStep_props {P : ℕ} (proc : FoldedPopProcess P) :
    let popKey? : FoldedOp → Option ℕ := fun | .pop s => some s | _ => none
    let isPop : FoldedOp → Bool := fun | .pop _ => true | _ => false
    (∀ τ ≤ proc.steps.length,
      let s₀ := ((proc.steps.take τ).filter isPop).length
      s₀ ≤ P ∧
      (proc.steps.take τ).filterMap popKey? = List.range' 1 s₀ ∧
      (proc.steps.drop τ).filterMap popKey? = List.range' (s₀ + 1) (P - s₀)) ∧
    (∀ s ∈ Finset.Icc 1 P,
      proc.popStepIdx s < proc.steps.length ∧
      proc.steps[proc.popStepIdx s]? = some (.pop s) ∧
      (∀ τ < proc.steps.length, proc.steps[τ]? = some (.pop s) ↔ τ = proc.popStepIdx s)) ∧
    (∀ s₁ ∈ Finset.Icc 1 P, ∀ s₂ ∈ Finset.Icc 1 P,
      (s₁ < s₂ ↔ proc.popStepIdx s₁ < proc.popStepIdx s₂) ∧
      (s₁ ≤ s₂ ↔ proc.popStepIdx s₁ ≤ proc.popStepIdx s₂)) ∧
    (∀ τ ≤ proc.steps.length, ∀ u ∈ Finset.Icc 1 P,
      ((proc.steps.take τ).filter isPop).length + 1 ≤ u ↔ τ ≤ proc.popStepIdx u) ∧
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
      let s₀ := ((proc.steps.take τ).filter isPop).length
      s₀ ≤ P ∧
      (proc.steps.take τ).filterMap popKey? = List.range' 1 s₀ ∧
      (proc.steps.drop τ).filterMap popKey? = List.range' (s₀ + 1) (P - s₀) := by
    intro τ hτ
    dsimp only
    set s₀ := ((proc.steps.take τ).filter isPop).length
    have happ : (proc.steps.take τ).filterMap popKey? ++ (proc.steps.drop τ).filterMap popKey? =
        List.range' 1 P := by
      rw [← List.filterMap_append, List.take_append_drop]
      exact proc.hPopSeq
    have hlen1 : ((proc.steps.take τ).filterMap popKey?).length = s₀ := len_fmap _
    have hs₀_le : s₀ ≤ P := by
      have := congrArg List.length happ
      rw [ List.length_append, hlen1, List.length_range'] at this
      omega
    have hrange_split : List.range' 1 P = List.range' 1 s₀ ++ List.range' (1 + s₀) (P - s₀) := by
      have hP_eq : P = s₀ + (P - s₀) := by omega
      conv_lhs => rw [hP_eq]
      have hr := (List.range'_append (s := 1) (m := s₀) (n := P - s₀) (step := 1)).symm
      rw [Nat.one_mul] at hr
      exact hr
    rw [hrange_split] at happ
    have hlen_r : (List.range' 1 s₀).length = s₀ := List.length_range'
    have heq_pair := List.append_inj happ (hlen1.trans hlen_r.symm)
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
    refine ⟨hidx_lt, hidx_some, fun τ hτ => ?_⟩
    constructor
    · intro h; exact (huniq τ hτ h).trans hidx_eq_τ₀.symm
    · rintro rfl; exact hidx_some
  have getElem?_of_eq : ∀ {i : ℕ} {v : FoldedOp} (hi : i < proc.steps.length),
      proc.steps[i]'hi = v → proc.steps[i]? = some v :=
    fun hi heq => (List.getElem?_eq_getElem hi).trans (congrArg some heq)
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
    have no_dup_pop : ∀ (a b : ℕ), a < b → b < proc.steps.length →
        proc.steps[a]? = some (.pop s) → proc.steps[b]? = some (.pop s) → False := by
      intro a b hab hb ha_some hb_some
      have ha : a < proc.steps.length := lt_trans hab hb
      have hin_take : s ∈ (proc.steps.take (a + 1)).filterMap popKey? := by
        rw [← pop_in_list_iff]
        have hget_take : (proc.steps.take (a + 1))[a]? = some (.pop s) := by
          rw [List.getElem?_take_of_lt (by omega)]; exact ha_some
        exact List.mem_of_getElem? hget_take
      have hin_drop : s ∈ (proc.steps.drop (a + 1)).filterMap popKey? := by
        rw [← pop_in_list_iff]
        have hget_drop : (proc.steps.drop (a + 1))[b - (a + 1)]? = some (.pop s) := by
          rw [List.getElem?_drop]
          have : a + 1 + (b - (a + 1)) = b := by omega
          rw [this]; exact hb_some
        exact List.mem_of_getElem? hget_drop
      obtain ⟨_, htake_eq, hdrop_eq⟩ := split_prop (a + 1) (by omega)
      rw [htake_eq, List.mem_range'] at hin_take
      rw [hdrop_eq, List.mem_range'] at hin_drop
      rcases hin_take with ⟨i1, hi1, heq1⟩
      rcases hin_drop with ⟨i2, hi2, heq2⟩
      omega
    have hτ₀_some : proc.steps[τ₀]? = some (.pop s) := getElem?_of_eq hτ₀_lt hτ₀_get
    refine ⟨τ₀, hτ₀_lt, hτ₀_some, fun τ hτ hτ_some => ?_⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact no_dup_pop τ τ₀ hlt hτ₀_lt hτ_some hτ₀_some
    · exact no_dup_pop τ₀ τ hgt hτ hτ₀_some hτ_some
  have s0_iff : ∀ τ ≤ proc.steps.length, ∀ u ∈ Finset.Icc 1 P,
      ((proc.steps.take τ).filter isPop).length + 1 ≤ u ↔ τ ≤ proc.popStepIdx u := by
    intro τ hτ u hu
    obtain ⟨hpop_lt, hpop_get, hpop_uniq⟩ := pop_props u hu
    obtain ⟨hs₀_le, htake_eq, _⟩ := split_prop τ hτ
    rw [Finset.mem_Icc] at hu
    set s₀ := ((proc.steps.take τ).filter isPop).length
    -- `τ ≤ proc.popStepIdx u ↔ .pop u ∉ proc.steps.take τ ↔ u ∉ List.range' 1 s₀ ↔ s₀ + 1 ≤ u`
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
    have hs1_le : ¬ (((proc.steps.take (proc.popStepIdx s₁ + 1)).filter isPop).length + 1 ≤ s₁) :=
      mt (s0_iff (proc.popStepIdx s₁ + 1) (by omega) s₁ hs₁).mp hs1_false
    have hs1_prev : ((proc.steps.take (proc.popStepIdx s₁)).filter isPop).length + 1 ≤ s₁ :=
      (s0_iff (proc.popStepIdx s₁) (le_of_lt h1_lt) s₁ hs₁).mpr le_rfl
    have htake_succ : proc.steps.take (proc.popStepIdx s₁ + 1) =
        proc.steps.take (proc.popStepIdx s₁) ++ [proc.steps[proc.popStepIdx s₁]'h1_lt] :=
      List.take_succ_eq_append_getElem h1_lt
    have hs0_step : ((proc.steps.take (proc.popStepIdx s₁ + 1)).filter isPop).length ≤
        ((proc.steps.take (proc.popStepIdx s₁)).filter isPop).length + 1 := by
      rw [htake_succ, List.filter_append, List.length_append]
      cases proc.steps[proc.popStepIdx s₁]'h1_lt <;> simp [isPop]
    have hs0_exact : ((proc.steps.take (proc.popStepIdx s₁ + 1)).filter isPop).length = s₁ := by
      omega
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
    -- Helper: if `u ∈ keyFinset (treeAt τ₁)` and `.pop u` never occurs in `[τ₁, τ₂)`, then `u ∈ keyFinset (treeAt τ₂)`
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
        have hu_mid : u ∈ keyFinset (proc.treeAt (τ₁ + d)) :=
          ihd (by omega) (by omega) (fun t ht1 ht2 => hno t ht1 (by omega))
        have hstep := htree_laws (τ₁ + d) ht_lt
        cases hop : proc.steps[τ₁ + d]'ht_lt with
        | push w =>
          rw [hop] at hstep
          rw [hstep.2.2.2]
          exact Finset.mem_insert_of_mem hu_mid
        | shift =>
          rw [hop] at hstep
          simpa [hstep] using hu_mid
        | upperRot a b =>
          rw [hop] at hstep
          simpa [hstep.2] using hu_mid
        | pop s =>
          rw [hop] at hstep
          rw [hstep.2.2, Finset.mem_sdiff, Finset.mem_singleton]
          refine ⟨hu_mid, ?_⟩
          rintro rfl
          have heq_pop : τ₁ + d = proc.popStepIdx u :=
            (hp_uniq (τ₁ + d) ht_lt).mp (getElem?_of_eq ht_lt hop)
          exact hno (τ₁ + d) (by omega) (by omega) heq_pop
    -- Also: if `u ∉ keyFinset (treeAt τ₁)` and `.push u` never occurs in `[τ₁, τ₂)`, then `u ∉ keyFinset (treeAt τ₂)`
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
        have hu_mid : u ∉ keyFinset (proc.treeAt (τ₁ + d)) :=
          ihd (by omega) (by omega) (fun t ht ht1 ht2 => hno t ht ht1 (by omega))
        have hstep := htree_laws (τ₁ + d) ht_lt
        cases hop : proc.steps[τ₁ + d]'ht_lt with
        | push w =>
          rw [hop] at hstep
          rw [hstep.2.2.2, Finset.mem_insert]
          rintro (rfl | h_in)
          · exact hno (τ₁ + d) ht_lt (by omega) (by omega) hop
          · exact hu_mid h_in
        | shift =>
          rw [hop] at hstep
          simpa [hstep] using hu_mid
        | upperRot a b =>
          rw [hop] at hstep
          simpa [hstep.2] using hu_mid
        | pop s =>
          rw [hop] at hstep
          rw [hstep.2.2, Finset.mem_sdiff]
          exact fun h => hu_mid h.1
    -- At `popStepIdx u`, `u ∈ keyFinset (treeAt (popStepIdx u))`!
    have hu_at_pop : u ∈ keyFinset (proc.treeAt (proc.popStepIdx u)) := by
      have hstep := htree_laws (proc.popStepIdx u) hp_lt
      have hop : proc.steps[proc.popStepIdx u]'hp_lt = .pop u := by
        rw [List.getElem?_eq_getElem hp_lt] at hp_some
        injection hp_some
      rw [hop] at hstep
      exact hstep.1
    have hex_push : ∃ (τ₀ : ℕ) (hτ₀ : τ₀ < proc.popStepIdx u),
        proc.steps[τ₀]'(lt_trans hτ₀ hp_lt) = .push u := by
      by_contra hnone
      have hnone' : ∀ (t : ℕ) (ht : t < proc.popStepIdx u),
          proc.steps[t]'(lt_trans ht hp_lt) ≠ .push u :=
        fun t ht h => hnone ⟨t, ht, h⟩
      have hu0 : u ∉ keyFinset (proc.treeAt 0) := by
        simp [FoldedPopProcess.treeAt, FoldedPopProcess.stateAt, keyFinset]
      have h_abs := absent_no_push (Nat.zero_le _) (le_of_lt hp_lt)
        (fun t _ _ ht2 => hnone' t ht2) hu0
      exact h_abs hu_at_pop
    obtain ⟨τ₀, hτ₀_pop, hτ₀_push⟩ := hex_push
    have hτ₀_len : τ₀ < proc.steps.length := lt_trans hτ₀_pop hp_lt
    -- Show `.push u` occurs ONLY at `τ₀`!
    have hpush_uniq_τ₀ : ∀ τ < proc.steps.length, proc.steps[τ]? = some (.push u) → τ = τ₀ := by
      intro τ hτ hτ_some
      have hτ_eq : proc.steps[τ]'hτ = .push u := by
        rw [List.getElem?_eq_getElem hτ] at hτ_some; injection hτ_some
      by_contra hne
      -- Either both `< popStepIdx u`, or the larger is `≥ popStepIdx u`!
      have not_two_pushes : ∀ (a b : ℕ) (ha : a < proc.steps.length) (hb : b < proc.steps.length),
          a < b → proc.steps[a]'ha = .push u → proc.steps[b]'hb = .push u → False := by
        intro a b ha hb hab hpa hpb
        by_cases hb_le : b ≤ proc.popStepIdx u
        · -- `a + 1 ≤ b ≤ popStepIdx u`: `u ∈ treeAt (a + 1)` persists to `b`, contradicting `.push u` at `b`!
          have hu_a1 : u ∈ keyFinset (proc.treeAt (a + 1)) := by
            have hstep := htree_laws a ha
            rw [hpa] at hstep
            rw [hstep.2.2.2]
            exact Finset.mem_insert_self _ _
          have hu_b : u ∈ keyFinset (proc.treeAt b) :=
            persist_no_pop (by omega) (le_of_lt hb) (fun t _ htb => by omega) hu_a1
          have hstep_b := htree_laws b hb
          rw [hpb] at hstep_b
          exact hstep_b.2.2.1 hu_b
        · -- `popStepIdx u < b`: `u ∈ treeAt (b + 1)` persists to `steps.length`, contradicting `hEndEmpty`!
          have hu_b1 : u ∈ keyFinset (proc.treeAt (b + 1)) := by
            have hstep := htree_laws b hb
            rw [hpb] at hstep
            rw [hstep.2.2.2]
            exact Finset.mem_insert_self _ _
          have hu_end : u ∈ keyFinset (proc.treeAt proc.steps.length) :=
            persist_no_pop (by omega) le_rfl (fun t htb _ => by omega) hu_b1
          have hend : proc.treeAt proc.steps.length = .nil :=
            congrArg Prod.fst (proc_stateAt_end proc)
          simp [hend, keyFinset] at hu_end
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact not_two_pushes τ τ₀ hτ hτ₀_len hlt hτ_eq hτ₀_push
      · exact not_two_pushes τ₀ τ hτ₀_len hτ hgt hτ₀_push hτ_eq
    obtain ⟨hins_lt, hins_some, hins_uniq⟩ := findIdx_unique (.push u)
      ⟨τ₀, hτ₀_len, getElem?_of_eq hτ₀_len hτ₀_push, hpush_uniq_τ₀⟩
    change proc.insStep u < proc.steps.length at hins_lt
    change proc.steps[proc.insStep u]? = some (.push u) at hins_some
    change ∀ τ < proc.steps.length, proc.steps[τ]? = some (.push u) ↔ τ = proc.insStep u at hins_uniq
    have hins_eq_τ₀ : proc.insStep u = τ₀ :=
      hpush_uniq_τ₀ (proc.insStep u) hins_lt hins_some
    have hins_lt_pop : proc.insStep u < proc.popStepIdx u := hins_eq_τ₀ ▸ hτ₀_pop
    refine ⟨hins_lt_pop, hins_some, hins_uniq, fun τ hτ => ?_⟩
    -- Prove `u ∈ keyFinset (treeAt τ) ↔ insStep u < τ ∧ τ ≤ popStepIdx u`!
    by_cases h1 : τ ≤ proc.insStep u
    · constructor
      · intro hu_in
        exfalso
        have hu0 : u ∉ keyFinset (proc.treeAt 0) := by
          simp [FoldedPopProcess.treeAt, FoldedPopProcess.stateAt, keyFinset]
        refine absent_no_push (Nat.zero_le τ) hτ (fun t ht _ htτ hpush => ?_) hu0 hu_in
        have := (hins_uniq t ht).mp (getElem?_of_eq ht hpush)
        omega
      · intro ⟨hlt, _⟩; omega
    · by_cases h2 : τ ≤ proc.popStepIdx u
      · constructor
        · intro _; exact ⟨by omega, h2⟩
        · intro _
          have hins_push : proc.steps[proc.insStep u]'hins_lt = .push u := by
            rw [List.getElem?_eq_getElem hins_lt] at hins_some; injection hins_some
          have hu_after_ins : u ∈ keyFinset (proc.treeAt (proc.insStep u + 1)) := by
            have hstep := htree_laws (proc.insStep u) hins_lt
            rw [hins_push] at hstep
            rw [hstep.2.2.2]
            exact Finset.mem_insert_self _ _
          exact persist_no_pop (by omega) hτ (fun t _ htτ => by omega) hu_after_ins
      · constructor
        · intro hu_in
          exfalso
          have hp_pop : proc.steps[proc.popStepIdx u]'hp_lt = .pop u := by
            rw [List.getElem?_eq_getElem hp_lt] at hp_some; injection hp_some
          have hu_after_pop : u ∉ keyFinset (proc.treeAt (proc.popStepIdx u + 1)) := by
            have hstep := htree_laws (proc.popStepIdx u) hp_lt
            rw [hp_pop] at hstep
            rw [hstep.2.2, Finset.mem_sdiff, Finset.mem_singleton]
            intro h; exact h.2 rfl
          refine absent_no_push (by omega) hτ (fun t ht htp _ hpush => ?_) hu_after_pop hu_in
          have := (hins_uniq t ht).mp (getElem?_of_eq ht hpush)
          omega
        · intro ⟨_, hle⟩; omega
  exact ⟨split_prop, pop_props, pop_mono, s0_iff, ins_props⟩

private theorem takeThrough_props {xs : List ℕ} (hpw : xs.Pairwise (· < ·))
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
    · subst hxb
      refine ⟨⟨rest, rfl⟩, List.cons_ne_nil _ _, List.pairwise_singleton _ _, rfl, rfl, fun w => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro rfl; exact ⟨Or.inl rfl, le_rfl⟩
      · rintro ⟨rfl | hrest, hle⟩
        · rfl
        · exact absurd (lt_of_le_of_lt hle (hpw.1 w hrest)) (lt_irrefl w)
    · have hb_rest : b ∈ rest := by
        rcases List.mem_cons.mp hb with rfl | h
        · exact absurd rfl hxb
        · exact h
      obtain ⟨⟨tl, htl⟩, hne, hpw_sub, hhd, hlast, hmem_iff⟩ := ih hpw.2 hb_rest
      have hxb_lt : x < b := hpw.1 b hb_rest
      refine ⟨⟨tl, congrArg (x :: ·) htl⟩, List.cons_ne_nil _ _, ?_, rfl, ?_, fun w => ?_⟩
      · refine List.Pairwise.cons (fun w hw => ?_) hpw_sub
        exact hpw.1 w ((hmem_iff w).mp hw).1
      · rw [List.getLast?_cons_of_ne_nil hne]
        exact hlast
      · simp only [List.mem_cons, hmem_iff]
        constructor
        · rintro (rfl | ⟨hr, hle⟩)
          · exact ⟨Or.inl rfl, le_of_lt hxb_lt⟩
          · exact ⟨Or.inr hr, hle⟩
        · rintro ⟨rfl | hr, hle⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hr, hle⟩

private theorem mem_rInt_iff {P : ℕ} (proc : FoldedPopProcess P) (e : InternalPopRot) :
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
          -- `e ∈ foldedPopRotsAt idx st op → e.stepIdx = idx`
          cases op with
          | pop s =>
            unfold foldedPopRotsAt at h0
            cases hst2 : st.2 with
            | none => rw [hst2] at h0; cases h0
            | some b =>
              rw [hst2] at h0
              dsimp only at h0
              rw [List.mem_filterMap] at h0
              rcases h0 with ⟨i, _, hmatch⟩
              split at hmatch
              · injection hmatch with he_eq; rw [← he_eq]; dsimp only; omega
              · cases hmatch
          | _ => simp [foldedPopRotsAt] at h0
        · refine ⟨d + 1, Nat.succ_lt_succ hd, by omega, ?_⟩
          simpa [List.take_succ_cons, List.foldl_cons, Nat.add_right_comm, Nat.add_assoc] using hmem
      · rintro ⟨d, hd, hstep, hmem⟩
        cases d with
        | zero =>
          left
          simpa using hmem
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
      | none => rw [hb] at hmem; cases hmem
      | some b =>
        rw [hb] at hmem
        dsimp only at hmem
        rw [List.mem_filterMap] at hmem
        rcases hmem with ⟨idx, hidx_range, hmatch⟩
        rw [List.mem_range] at hidx_range
        set sub := takeThrough (leftSpine (proc.stateAt e.stepIdx).1) b
        cases hx : sub[2 * (idx + 1) - 1]? with
        | none => rw [hx] at hmatch; cases hmatch
        | some x =>
          cases hy : sub[2 * (idx + 1)]? with
          | none => rw [hx, hy] at hmatch; cases hmatch
          | some y =>
            cases hz : sub[2 * (idx + 1) + 1]? with
            | none => rw [hx, hy, hz] at hmatch; cases hmatch
            | some z =>
              rw [hx, hy, hz] at hmatch
              injection hmatch with he_eq
              have hs0 : s = e.s := congrArg InternalPopRot.s he_eq
              have hj0 : idx + 1 = e.j := congrArg InternalPopRot.j he_eq
              have hh0 : (sub.length - 1 - 1) / 2 = e.h := congrArg InternalPopRot.h he_eq
              have hx0 : x = e.x := congrArg InternalPopRot.x he_eq
              have hy0 : y = e.y := congrArg InternalPopRot.y he_eq
              have hz0 : z = e.z := congrArg InternalPopRot.z he_eq
              subst hs0 hx0 hy0 hz0
              exact ⟨hd, b, hop, hb, hh0.symm, by omega, by omega,
                hj0 ▸ hx, hj0 ▸ hy, hj0 ▸ hz⟩
    | _ => rw [hop] at hmem; simp [foldedPopRotsAt] at hmem
  · rintro ⟨hτ, b, hop, hb, hh_eq, hj1, hjh, hx, hy, hz⟩
    refine ⟨e.stepIdx, hτ, Nat.zero_add _, ?_⟩
    simp only [Nat.zero_add]
    change e ∈ foldedPopRotsAt e.stepIdx (proc.stateAt e.stepIdx) (proc.steps[e.stepIdx]'hτ)
    rw [hop]
    unfold foldedPopRotsAt
    unfold FoldedPopProcess.b1At at hb
    unfold FoldedPopProcess.treeAt at hh_eq hx hy hz
    rw [hb]
    dsimp only
    rw [List.mem_filterMap]
    refine ⟨e.j - 1, List.mem_range.mpr (by omega), ?_⟩
    have hj_add : e.j - 1 + 1 = e.j := by omega
    cases e
    simp only [hj_add, hx, hy, hz, ← hh_eq]

private theorem rInt_basic_and_order {P : ℕ} (proc : FoldedPopProcess P) :
    (∀ e ∈ proc.rInt,
      e.s ∈ Finset.Icc 1 P ∧
      e.stepIdx = proc.popStepIdx e.s ∧
      1 ≤ e.s ∧ e.s < e.x ∧ e.x < e.y ∧ e.y < e.z ∧ e.z ≤ P) ∧
    (∀ e₁ ∈ proc.rInt, ∀ e₂ ∈ proc.rInt, e₁.stepIdx = e₂.stepIdx →
      (e₁.j = e₂.j → e₁ = e₂) ∧ (e₁.j < e₂.j → e₁.z ≤ e₂.x)) := by
  obtain ⟨hbst_all, _⟩ := proc_tree_bst_and_step_keys proc
  obtain ⟨_, hpop_props, _, _, _⟩ := popStepIdx_and_insStep_props proc
  refine ⟨?_, ?_⟩
  · intro e he
    obtain ⟨hτ, b, hop, hb, _, hj1, _, hx, hy, hz⟩ := (mem_rInt_iff proc e).mp he
    obtain ⟨hval, _⟩ := proc_step_at proc hτ
    rw [hop] at hval
    rcases hval with ⟨b', _, hmin, hb', hb'_ls⟩
    change proc.b1At e.stepIdx = some b' at hb'
    rw [hb] at hb'; injection hb' with hbb'; subst b'
    obtain ⟨ht_bst, ht_sub⟩ := hbst_all e.stepIdx (le_of_lt hτ)
    obtain ⟨hs_mem, _, hs_hd, _, _⟩ := (minKey_bst_props ht_bst).2 e.s hmin
    have hs_in_Icc : e.s ∈ Finset.Icc 1 P := ht_sub ((mem_iff_mem_keyFinset _ _).mp hs_mem)
    have hstep_eq : e.stepIdx = proc.popStepIdx e.s :=
      ((hpop_props e.s hs_in_Icc).2.2 e.stepIdx hτ).mp
        ((List.getElem?_eq_getElem hτ).trans (congrArg some hop))
    have hpw_ls : (leftSpine (proc.treeAt e.stepIdx)).Pairwise (· < ·) :=
      leftSpine_pairwise_lt ht_bst
    obtain ⟨hpref, _, hpw_sub, hhd_sub, _, hmem_sub⟩ := takeThrough_props hpw_ls hb'_ls
    set sub := takeThrough (leftSpine (proc.treeAt e.stepIdx)) b
    have hs_sub0 : sub[0]? = some e.s := by
      rw [← List.head?_eq_getElem?, hhd_sub]
      exact hs_hd
    have hlt_sub : ∀ {i₁ i₂ : ℕ} {v₁ v₂ : ℕ}, i₁ < i₂ →
        sub[i₁]? = some v₁ → sub[i₂]? = some v₂ → v₁ < v₂ := by
      intro i₁ i₂ v₁ v₂ hi h1 h2
      obtain ⟨h1_lt, rfl⟩ := List.getElem?_eq_some_iff.mp h1
      obtain ⟨h2_lt, rfl⟩ := List.getElem?_eq_some_iff.mp h2
      exact List.pairwise_iff_getElem.mp hpw_sub i₁ i₂ h1_lt h2_lt hi
    have hs_lt_x : e.s < e.x := hlt_sub (by omega) hs_sub0 hx
    have hx_lt_y : e.x < e.y := hlt_sub (by omega) hx hy
    have hy_lt_z : e.y < e.z := hlt_sub (by omega) hy hz
    have hz_in_sub : e.z ∈ sub := List.mem_of_getElem? hz
    have hz_in_ls : e.z ∈ leftSpine (proc.treeAt e.stepIdx) := ((hmem_sub e.z).mp hz_in_sub).1
    have hz_in_Icc : e.z ∈ Finset.Icc 1 P :=
      ht_sub ((mem_iff_mem_keyFinset _ _).mp (mem_of_mem_leftSpine hz_in_ls))
    exact ⟨hs_in_Icc, hstep_eq, (Finset.mem_Icc.mp hs_in_Icc).1,
      hs_lt_x, hx_lt_y, hy_lt_z, (Finset.mem_Icc.mp hz_in_Icc).2⟩
  · intro e₁ he₁ e₂ he₂ hsame
    obtain ⟨hτ₁, b₁, hop₁, hb₁, hh₁, hj1₁, _, hx₁, hy₁, hz₁⟩ := (mem_rInt_iff proc e₁).mp he₁
    obtain ⟨hτ₂, b₂, hop₂, hb₂, hh₂, _, _, hx₂, hy₂, hz₂⟩ := (mem_rInt_iff proc e₂).mp he₂
    have hop_eq : FoldedOp.pop e₁.s = FoldedOp.pop e₂.s := by
      have h1 : proc.steps[e₁.stepIdx]? = some (.pop e₁.s) :=
        (List.getElem?_eq_getElem hτ₁).trans (congrArg some hop₁)
      have h2 : proc.steps[e₂.stepIdx]? = some (.pop e₂.s) :=
        (List.getElem?_eq_getElem hτ₂).trans (congrArg some hop₂)
      rw [hsame] at h1
      rw [h1] at h2
      injection h2
    injection hop_eq with hs_eq
    have hb_eq : b₁ = b₂ := by
      rw [hsame, hb₂] at hb₁; injection hb₁ with h; exact h.symm
    subst b₂
    constructor
    · intro hj_eq
      cases e₁; cases e₂
      dsimp only at hsame hs_eq hj_eq hh₁ hh₂ hx₁ hy₁ hz₁ hx₂ hy₂ hz₂ ⊢
      subst hsame hs_eq hj_eq
      rw [hx₁] at hx₂; injection hx₂ with hx_eq
      rw [hy₁] at hy₂; injection hy₂ with hy_eq
      rw [hz₁] at hz₂; injection hz₂ with hz_eq
      subst hx_eq hy_eq hz_eq
      rw [hh₁, hh₂]
    · intro hj_lt
      obtain ⟨hval₁, _⟩ := proc_step_at proc hτ₁
      rw [hop₁] at hval₁
      rcases hval₁ with ⟨b', _, _, hb', hb'_ls⟩
      change proc.b1At e₁.stepIdx = some b' at hb'
      rw [hb₁] at hb'; injection hb' with hbb'; subst b'
      obtain ⟨ht_bst, _⟩ := hbst_all e₁.stepIdx (le_of_lt hτ₁)
      have hpw_ls : (leftSpine (proc.treeAt e₁.stepIdx)).Pairwise (· < ·) :=
        leftSpine_pairwise_lt ht_bst
      obtain ⟨_, _, hpw_sub, _, _, _⟩ := takeThrough_props hpw_ls hb'_ls
      rw [← hsame] at hx₂
      obtain ⟨h1_lt, hv1⟩ := List.getElem?_eq_some_iff.mp hz₁
      obtain ⟨h2_lt, hv2⟩ := List.getElem?_eq_some_iff.mp hx₂
      rw [← hv1, ← hv2]
      rcases eq_or_lt_of_le (show 2 * e₁.j + 1 ≤ 2 * e₂.j - 1 by omega) with heq_idx | hlt_idx
      · simp [heq_idx]
      · exact le_of_lt (List.pairwise_iff_getElem.mp hpw_sub _ _ h1_lt h2_lt hlt_idx)

private theorem leadExit_unique_and_popKey {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    (p : ℕ) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    let Fp := promotedSubblockIndices P proc chain ℓ_val X p
    ∀ c ∈ Fp,
      ∃ e ∈ leadExitSet P proc chain ℓ_val X p,
        e ∈ vXp P proc chain ℓ_val X p ∧
        e.x ∈ (subblock1 subs c).toFinset ∧
        leadPopKey P proc chain ℓ_val X p c = e.s ∧
        (∀ e' ∈ leadExitSet P proc chain ℓ_val X p,
          e'.x ∈ (subblock1 subs c).toFinset → e' = e) ∧
        (∀ e' ∈ vXp P proc chain ℓ_val X p,
          e'.x ∈ (subblock1 subs c).toFinset →
          e.s ≤ e'.s ∧ (e.stepIdx < e'.stepIdx ∨ (e.stepIdx = e'.stepIdx ∧ e.j ≤ e'.j))) := by
  dsimp only
  set chain := scaleTreePartitionChain T P M
  set ℓ_val := ℓ.val + 1
  set subs := childSubblocks (chain ℓ.succ) X
  have hℓ : 1 ≤ ℓ_val ∧ ℓ_val ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  have hfin_eq : (⟨ℓ_val, Nat.lt_succ_of_le hℓ.2⟩ : Fin (M + 1)) = ℓ.succ := rfl
  obtain ⟨_, _, _, _, hsub_c, hsub_lt, _, _, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨hrInt_basic, hrInt_ord⟩ := rInt_basic_and_order proc
  obtain ⟨_, _, hpop_mono, _, _⟩ := popStepIdx_and_insStep_props proc
  have hvXp_sub_rInt : vXp P proc chain ℓ_val X p ⊆ proc.rInt := by
    intro e he
    unfold vXp at he
    simp only [hℓ, and_self, ↓reduceDIte] at he
    have he1 := (Finset.mem_filter.mp he).1
    unfold b3ExitAct at he1
    have he2 := (Finset.mem_filter.mp he1).1
    unfold b3Exit at he2
    exact (Finset.mem_filter.mp he2).1
  intro c hc
  have hc_Icc : c ∈ Finset.Icc (p + 1) subs.length ∧
      ∃ e₀ ∈ vXp P proc chain ℓ_val X p, e₀.x ∈ (subblock1 subs c).toFinset := by
    unfold promotedSubblockIndices at hc
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq] at hc
    exact Finset.mem_filter.mp hc
  rcases hc_Icc with ⟨hc_range, ⟨e₀, he₀_v, he₀_x⟩⟩
  set cands := (vXp P proc chain ℓ_val X p).filter (fun e => e.x ∈ (subblock1 subs c).toFinset)
  have hcands_ne : cands.Nonempty := ⟨e₀, Finset.mem_filter.mpr ⟨he₀_v, he₀_x⟩⟩
  -- Minimize `e.stepIdx * (proc.steps.length + 1) + e.j` or use `Finset.exists_min_image` twice!
  obtain ⟨e₁, he₁_in, he₁_min_step⟩ := cands.exists_min_image InternalPopRot.stepIdx hcands_ne
  set candsStep := cands.filter (fun e => e.stepIdx = e₁.stepIdx)
  have hcandsStep_ne : candsStep.Nonempty := ⟨e₁, Finset.mem_filter.mpr ⟨he₁_in, rfl⟩⟩
  obtain ⟨e, he_in_step, he_min_j⟩ := candsStep.exists_min_image InternalPopRot.j hcandsStep_ne
  obtain ⟨he_in_cands, he_step_eq⟩ := Finset.mem_filter.mp he_in_step
  obtain ⟨he_vXp, he_x⟩ := Finset.mem_filter.mp he_in_cands
  have he_lex : ∀ e' ∈ cands,
      e.stepIdx < e'.stepIdx ∨ (e.stepIdx = e'.stepIdx ∧ e.j ≤ e'.j) := by
    intro e' he'
    have hle_step : e.stepIdx ≤ e'.stepIdx := he_step_eq ▸ he₁_min_step e' he'
    rcases lt_or_eq_of_le hle_step with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, he_min_j e' (Finset.mem_filter.mpr ⟨he', heq.symm.trans he_step_eq⟩)⟩
  -- Uniqueness inside `cands.filter lex` AND inside `(leadExitSet ...).filter (e'.x ∈ S_c)`!
  have hfilter_lead : (leadExitSet P proc chain ℓ_val X p).filter
      (fun e' => e'.x ∈ (subblock1 subs c).toFinset) = {e} := by
    ext e'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨he'_lead, he'_x⟩
      unfold leadExitSet at he'_lead
      simp only [hℓ, and_self, ↓reduceDIte, hfin_eq, Finset.mem_biUnion, Finset.mem_filter] at he'_lead
      rcases he'_lead with ⟨b, hb_Fp, ⟨he'_vXp, he'_xb⟩, he'_lex⟩
      -- Since `e'.x ∈ S_b` and `e'.x ∈ S_c`, `b = c`!
      have hb_range : b ∈ Finset.Icc (p + 1) subs.length := by
        unfold promotedSubblockIndices at hb_Fp
        simp only [hℓ, and_self, ↓reduceDIte, hfin_eq] at hb_Fp
        exact (Finset.mem_filter.mp hb_Fp).1
      have hbc : b = c := by
        have hb1 : 1 ≤ b := by rw [Finset.mem_Icc] at hb_range; omega
        have hb2 : b ≤ subs.length := (Finset.mem_Icc.mp hb_range).2
        have hc1 : 1 ≤ c := by rw [Finset.mem_Icc] at hc_range; omega
        have hc2 : c ≤ subs.length := (Finset.mem_Icc.mp hc_range).2
        have hidx_b := (hsub_c b (Finset.mem_Icc.mpr ⟨hb1, hb2⟩)).2.2.2.2.2 e'.x he'_xb |>.1
        have hidx_c := (hsub_c c (Finset.mem_Icc.mpr ⟨hc1, hc2⟩)).2.2.2.2.2 e'.x he'_x |>.1
        exact hidx_b.symm.trans hidx_c
      subst b
      have he'_in_cands : e' ∈ cands := Finset.mem_filter.mpr ⟨he'_vXp, he'_x⟩
      have h1 := he_lex e' he'_in_cands
      have h2 := he'_lex e ⟨he_vXp, he_x⟩
      have hsame_step : e'.stepIdx = e.stepIdx := by omega
      have hsame_j : e'.j = e.j := by omega
      exact ((hrInt_ord e' (hvXp_sub_rInt he'_vXp) e (hvXp_sub_rInt he_vXp) hsame_step).1 hsame_j)
    · rintro rfl
      refine ⟨?_, he_x⟩
      unfold leadExitSet
      simp only [hℓ, and_self, ↓reduceDIte, hfin_eq, Finset.mem_biUnion, Finset.mem_filter]
      refine ⟨c, hc, ⟨he_vXp, he_x⟩, fun e' ⟨he'1, he'2⟩ => he_lex e' (Finset.mem_filter.mpr ⟨he'1, he'2⟩)⟩
  have he_lead : e ∈ leadExitSet P proc chain ℓ_val X p := by
    have : e ∈ (leadExitSet P proc chain ℓ_val X p).filter
        (fun e' => e'.x ∈ (subblock1 subs c).toFinset) := by rw [hfilter_lead]; simp
    exact (Finset.mem_filter.mp this).1
  have hpopKey_eq : leadPopKey P proc chain ℓ_val X p c = e.s := by
    unfold leadPopKey
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq]
    change ((leadExitSet P proc chain ℓ_val X p).filter
      (fun e' => e'.x ∈ (subblock1 subs c).toFinset)).sup InternalPopRot.s = e.s
    rw [hfilter_lead, Finset.sup_singleton]
  refine ⟨e, he_lead, he_vXp, he_x, hpopKey_eq, ?_, ?_⟩
  · intro e' he'_lead he'_x
    have : e' ∈ (leadExitSet P proc chain ℓ_val X p).filter
        (fun e'' => e''.x ∈ (subblock1 subs c).toFinset) :=
      Finset.mem_filter.mpr ⟨he'_lead, he'_x⟩
    rw [hfilter_lead, Finset.mem_singleton] at this
    exact this
  · intro e' he'_vXp he'_x
    have hlex := he_lex e' (Finset.mem_filter.mpr ⟨he'_vXp, he'_x⟩)
    obtain ⟨hes_Icc, he_step, _⟩ := hrInt_basic e (hvXp_sub_rInt he_vXp)
    obtain ⟨he's_Icc, he'_step, _⟩ := hrInt_basic e' (hvXp_sub_rInt he'_vXp)
    have hstep_le : proc.popStepIdx e.s ≤ proc.popStepIdx e'.s := by omega
    exact ⟨(hpop_mono e.s hes_Icc e'.s he's_Icc).2.mpr hstep_le, hlex⟩

/-- Inclusion and Part (1) of Lemma 5.8 (`lem_5_8_b3_gaps`), using `h_5_7` (`lem_5_7_b3_quotient`). -/
private theorem lem_5_8_part1
    (h_5_7 : ∀ (P r M : ℕ) (T : ScaleTree),
      ValidScaleTree P r M T → ∀ (proc : FoldedPopProcess P)
      (ℓ : Fin M) (X : IntervalBlock), X ∈ scaleTreePartitionChain T P M ℓ.castSucc →
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
            topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G))))
    (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    ∀ p ∈ Finset.Icc 1 (subs.length - 1),
      let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
      let G_end := phaseSummaryBST P proc chain ℓ_val X p (tauEmpty proc (subblock1 subs p))
      let pi0 := leftSpine G₀
      let Fp := promotedSubblockIndices P proc chain ℓ_val X p
      1 ≤ pi0.length ∧
      (∀ c ∈ Fp, c ∈ pi0.dropLast) ∧
      (∀ a b : ℕ, a ≤ b → b + 1 < pi0.length →
        (∀ t : ℕ, a ≤ t → t ≤ b → (pi0[t]?).getD 0 ∈ Fp) →
        (a = 0 ∨ (pi0[a - 1]?).getD 0 ∉ Fp) →
        (pi0[b + 1]?).getD 0 ∉ Fp →
        (∀ t : ℕ, a ≤ t → t < b →
          leadPopKey P proc chain ℓ_val X p ((pi0[t + 1]?).getD 0) <
            leadPopKey P proc chain ℓ_val X p ((pi0[t]?).getD 0)) ∧
        (∀ t : ℕ, a ≤ t → t ≤ b →
          rightReach G₀ ((pi0[b + 1]?).getD 0) ≤ rightReach G_end ((pi0[t]?).getD 0))) := by
  dsimp only
  set chain := scaleTreePartitionChain T P M
  set ℓ_val := ℓ.val + 1
  set subs := childSubblocks (chain ℓ.succ) X
  set K_X := subs.length
  have hℓ : 1 ≤ ℓ_val ∧ ℓ_val ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  have hfin_eq : (⟨ℓ_val, Nat.lt_succ_of_le hℓ.2⟩ : Fin (M + 1)) = ℓ.succ := rfl
  obtain ⟨hX1, _, hXP, _, hsub_c, hsub_lt, _, _, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨hKX, h57_phase, _⟩ := h_5_7 P r M T hValid proc ℓ X hX
  obtain ⟨hrInt_basic, hrInt_ord⟩ := rInt_basic_and_order proc
  obtain ⟨_, _, hpop_mono, _, _⟩ := popStepIdx_and_insStep_props proc
  have hlead := leadExit_unique_and_popKey hValid proc ℓ X hX
  intro p hp
  obtain ⟨hp1, hp_hi⟩ := Finset.mem_Icc.mp hp
  obtain ⟨htStart_tau, htau_tEnd, hG_bst_keys, hG_reach, h57_vXp⟩ := h57_phase p hp
  set Sp := subblock1 subs p
  set tStart := proc.popStepIdx Sp.lo
  set tEnd := if p + 1 ≤ K_X then proc.popStepIdx (subblock1 subs (p + 1)).lo else proc.steps.length
  set G := phaseSummaryBST P proc chain ℓ_val X p
  set G₀ := G tStart
  set G_end := G (tauEmpty proc Sp)
  set pi0 := leftSpine G₀
  set Fp := promotedSubblockIndices P proc chain ℓ_val X p
  have hK_eq : (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length = K_X := rfl
  have mem_Fp_Icc : ∀ {c : ℕ}, c ∈ Fp → c ∈ Finset.Icc 1 K_X := by
    intro c hc
    dsimp only [Fp] at hc
    unfold promotedSubblockIndices at hc
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq, Finset.mem_filter, Finset.mem_Icc] at hc
    exact Finset.mem_Icc.mpr ⟨by omega, hc.1.2⟩
  -- Helper: every `e ∈ vXp` has `e ∈ rInt` and `tStart ≤ e.stepIdx` and `e.stepIdx + 1 ≤ tauEmpty proc Sp`!
  have hvXp_time : ∀ e ∈ vXp P proc chain ℓ_val X p,
      e ∈ proc.rInt ∧ e.s ∈ Finset.Icc 1 P ∧ e.stepIdx = proc.popStepIdx e.s ∧
      tStart ≤ e.stepIdx ∧ e.stepIdx < tauEmpty proc Sp ∧
      (subblock1 subs (subblockIndex1 subs e.y)).hi < e.z := by
    intro e he
    have he_orig := he
    unfold vXp at he
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq, Finset.mem_filter] at he
    rcases he with ⟨he_act, hsep_xy, hes_Sp⟩
    change e.s ∈ Sp.toFinset at hes_Sp
    unfold b3ExitAct at he_act
    rw [Finset.mem_filter] at he_act
    rcases he_act with ⟨he_exit, hstep_tau⟩
    simp only [hsep_xy, hℓ.2, ↓reduceDIte, hfin_eq] at hstep_tau
    unfold b3Exit at he_exit
    rw [Finset.mem_filter] at he_exit
    rcases he_exit with ⟨he_rInt, hexit_cond⟩
    simp only [hsep_xy, hℓ, and_self, ↓reduceDIte, hfin_eq] at hexit_cond
    obtain ⟨hes_Icc, he_step_eq, _⟩ := hrInt_basic e he_rInt
    -- `Sp` bounds:
    have hp_Icc : p ∈ Finset.Icc 1 K_X := Finset.mem_Icc.mpr ⟨hp1, by omega⟩
    have hp_Icc' : p ∈ Finset.Icc 1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length :=
      hK_eq.symm ▸ hp_Icc
    obtain ⟨_, hSp_in_chain, hSp_Xlo, hSp_lohi, hSp_Xhi, hSp_w⟩ := hsub_c p hp_Icc'
    change X.lo ≤ Sp.lo at hSp_Xlo
    change Sp.lo ≤ Sp.hi at hSp_lohi
    change Sp.hi ≤ X.hi at hSp_Xhi
    have hSp_lo_Icc : Sp.lo ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hes_ge : Sp.lo ≤ e.s := (Finset.mem_Icc.mp hes_Sp).1
    have htStart_le : tStart ≤ e.stepIdx := by
      rw [he_step_eq]
      exact (hpop_mono Sp.lo hSp_lo_Icc e.s hes_Icc).2.mp hes_ge
    -- Also `blockAt (chain ℓ.succ) e.s = Sp` so `hstep_tau` says `e.stepIdx < tauEmpty proc Sp`!
    have hblock_es : blockAt (chain ℓ.succ) e.s = Sp := (hSp_w e.s hes_Sp).2.1
    rw [hblock_es] at hstep_tau
    -- Also `q = subblockIndex1 subs e.y ∈ Icc (p + 1) K_X`, so `blockAt (chain ℓ.succ) e.y = subblock1 subs q`!
    have hq_bounds := h57_vXp e he_orig
    dsimp only at hq_bounds
    change p + 1 ≤ subblockIndex1 subs e.x ∧
      subblockIndex1 subs e.x < subblockIndex1 subs e.y ∧
      subblockIndex1 subs e.y ≤ K_X ∧ _ at hq_bounds
    have hq_pos : 1 ≤ subblockIndex1 subs e.y := by
      have := hq_bounds.1; have := hq_bounds.2.1; omega
    have hq_Icc : subblockIndex1 subs e.y ∈ Finset.Icc 1 K_X :=
      Finset.mem_Icc.mpr ⟨hq_pos, hq_bounds.2.2.1⟩
    have hey_in_Sq : e.y ∈ (subblock1 subs (subblockIndex1 subs e.y)).toFinset := by
      revert hq_pos
      unfold subblockIndex1
      cases hf : subs.findIdx? (fun S => decide (S.lo ≤ e.y ∧ e.y ≤ S.hi)) with
      | none => intro hq_pos; simp at hq_pos
      | some idx =>
        intro _
        obtain ⟨hidx_lt, hp_idx⟩ := findIdx?_eq_some_spec _ hf
        simp only [decide_eq_true_eq] at hp_idx
        have hsub1_idx : subblock1 subs (idx + 1) = subs[idx] := by
          unfold subblock1; simp [List.getElem?_eq_getElem hidx_lt]
        rw [hsub1_idx]
        exact Finset.mem_Icc.mpr hp_idx
    have hblock_ey : blockAt (chain ℓ.succ) e.y = subblock1 subs (subblockIndex1 subs e.y) :=
      (hsub_c _ (hK_eq.symm ▸ hq_Icc)).2.2.2.2.2 e.y hey_in_Sq |>.2.1
    rw [hblock_ey] at hexit_cond
    exact ⟨he_rInt, hes_Icc, he_step_eq, htStart_le, hstep_tau, hexit_cond.2⟩
  -- 1. `1 ≤ pi0.length`
  have hG0_bst_keys := hG_bst_keys tStart (Finset.mem_Icc.mpr ⟨le_rfl, le_trans htStart_tau htau_tEnd⟩)
  have hG0_bst : G₀.IsBST := hG0_bst_keys.1
  have hG0_ne : G₀ ≠ .nil := by
    intro hnil
    have hp1_in : p + 1 ∈ keyFinset G₀ := by
      rw [hG0_bst_keys.2, hK_eq, Finset.mem_Icc]; omega
    simp [hnil, keyFinset] at hp1_in
  have hpi0_len : 1 ≤ pi0.length := leftSpine_nonempty_of_ne_nil hG0_ne
  have hpi0_pw : pi0.Pairwise (· < ·) := leftSpine_pairwise_lt hG0_bst
  -- 2. `∀ c ∈ Fp, c ∈ pi0.dropLast`
  have hFp_dropLast : ∀ c ∈ Fp, c ∈ pi0.dropLast := by
    intro c hc
    obtain ⟨e, _, he_vXp, he_x, _, _, _⟩ := hlead p c hc
    obtain ⟨_, _, _, htStart_e, he_tau, _⟩ := hvXp_time e he_vXp
    have he_tEnd : e.stepIdx ≤ tEnd := le_of_lt (lt_of_lt_of_le he_tau htau_tEnd)
    have hreach0 : RightRotReachable G₀ (G e.stepIdx) := hG_reach tStart e.stepIdx le_rfl htStart_e he_tEnd
    have hsub_ls : (leftSpine (G e.stepIdx)).Sublist pi0 := leftSpine_sublist_of_reachable hreach0
    obtain ⟨hb1, hbq, _, hb_ls, hq_ls, _, _⟩ := h57_vXp e he_vXp
    have hc_Icc : c ∈ Finset.Icc 1 K_X := mem_Fp_Icc hc
    have hbx_eq : subblockIndex1 subs e.x = c :=
      (hsub_c c (hK_eq.symm ▸ hc_Icc)).2.2.2.2.2 e.x he_x |>.1
    change subblockIndex1 subs e.x < subblockIndex1 subs e.y at hbq
    change subblockIndex1 subs e.x ∈ leftSpine (G e.stepIdx) at hb_ls
    rw [hbx_eq] at hbq hb_ls
    exact mem_dropLast_of_lt_mem hpi0_pw (hsub_ls.subset hb_ls) (hsub_ls.subset hq_ls) hbq
  -- 3. Part (1) run properties
  refine ⟨hpi0_len, hFp_dropLast, ?_⟩
  intro a b hab hb1_lt hrun _ _
  -- Helper: `pi0[idx]?.getD 0 = pi0[idx]` and strictly increasing index correspondence
  have get_pi0 : ∀ {idx : ℕ} (h : idx < pi0.length), (pi0[idx]?).getD 0 = pi0[idx]'h := by
    intro idx h; simp [List.getElem?_eq_getElem h]
  have pi0_idx_of_mem : ∀ {w : ℕ}, w ∈ pi0 → ∃ idx : ℕ, ∃ h : idx < pi0.length, pi0[idx]'h = w := by
    intro w hw; exact List.getElem_of_mem hw
  have pi0_lt_iff_idx : ∀ {i₁ i₂ : ℕ} (h1 : i₁ < pi0.length) (h2 : i₂ < pi0.length),
      pi0[i₁]'h1 < pi0[i₂]'h2 ↔ i₁ < i₂ := by
    intro i₁ i₂ h1 h2
    constructor
    · intro hlt
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
      · exact lt_irrefl _ hlt
      · exact lt_asymm hlt (List.pairwise_iff_getElem.mp hpi0_pw i₂ i₁ h2 h1 hgt)
    · exact List.pairwise_iff_getElem.mp hpi0_pw i₁ i₂ h1 h2
  -- First prove strict reversal `leadPopKey pi0[t+1] < leadPopKey pi0[t]` for `a ≤ t < b`!
  have hrev_adj : ∀ t : ℕ, a ≤ t → t < b →
      leadPopKey P proc chain ℓ_val X p ((pi0[t + 1]?).getD 0) <
        leadPopKey P proc chain ℓ_val X p ((pi0[t]?).getD 0) := by
    intro t hat htb
    have ht_len : t < pi0.length := by omega
    have ht1_len : t + 1 < pi0.length := by omega
    set c₁ := (pi0[t]?).getD 0
    set c₂ := (pi0[t + 1]?).getD 0
    have hc₁_eq : c₁ = pi0[t]'ht_len := get_pi0 ht_len
    have hc₂_eq : c₂ = pi0[t + 1]'ht1_len := get_pi0 ht1_len
    have hc₁_lt_c₂ : c₁ < c₂ := by
      rw [hc₁_eq, hc₂_eq, pi0_lt_iff_idx ht_len ht1_len]; omega
    have hc₁_Fp : c₁ ∈ Fp := hrun t hat (le_of_lt htb)
    have hc₂_Fp : c₂ ∈ Fp := hrun (t + 1) (by omega) (by omega)
    obtain ⟨e₁, _, he₁_vXp, he₁_x, hkey₁, _, _⟩ := hlead p c₁ hc₁_Fp
    obtain ⟨e₂, _, he₂_vXp, he₂_x, hkey₂, _, _⟩ := hlead p c₂ hc₂_Fp
    rw [hkey₁, hkey₂]
    obtain ⟨he₁_rInt, he₁s_Icc, he₁_step, htStart_e₁, he₁_tau, he₁_exit_z⟩ := hvXp_time e₁ he₁_vXp
    obtain ⟨he₂_rInt, he₂s_Icc, he₂_step, htStart_e₂, he₂_tau, _⟩ := hvXp_time e₂ he₂_vXp
    by_contra hnot_lt
    have hs_le : e₁.s ≤ e₂.s := Nat.le_of_not_lt hnot_lt
    have hstep_le : e₁.stepIdx ≤ e₂.stepIdx := by
      rw [he₁_step, he₂_step]
      exact (hpop_mono e₁.s he₁s_Icc e₂.s he₂s_Icc).2.mp hs_le
    -- Unpack `h57_vXp` for `e₁` and `e₂`!
    obtain ⟨hb1_1, hbq_1, hq1_le, hb1_ls, hq1_ls, hedge_1, hreach_1_next⟩ := h57_vXp e₁ he₁_vXp
    obtain ⟨_, _, _, hb2_ls, _, _, _⟩ := h57_vXp e₂ he₂_vXp
    have hc₁_Icc : c₁ ∈ Finset.Icc 1 K_X := mem_Fp_Icc hc₁_Fp
    have hc₂_Icc : c₂ ∈ Finset.Icc 1 K_X := mem_Fp_Icc hc₂_Fp
    have hb1_eq : subblockIndex1 subs e₁.x = c₁ :=
      (hsub_c c₁ (hK_eq.symm ▸ hc₁_Icc)).2.2.2.2.2 e₁.x he₁_x |>.1
    have hb2_eq : subblockIndex1 subs e₂.x = c₂ :=
      (hsub_c c₂ (hK_eq.symm ▸ hc₂_Icc)).2.2.2.2.2 e₂.x he₂_x |>.1
    change subblockIndex1 subs e₁.x < subblockIndex1 subs e₁.y at hbq_1
    change subblockIndex1 subs e₁.x ∈ leftSpine (G e₁.stepIdx) at hb1_ls
    change subblockIndex1 subs e₁.y ∈ leftSpine (G e₁.stepIdx) at hq1_ls
    change IsRightRotEdge (G e₁.stepIdx) (subblockIndex1 subs e₁.x) (subblockIndex1 subs e₁.y) at hedge_1
    change RightRotReachable (rotateRightEdge (G e₁.stepIdx) (subblockIndex1 subs e₁.x)
      (subblockIndex1 subs e₁.y)) (G (e₁.stepIdx + 1)) at hreach_1_next
    change subblockIndex1 subs e₂.x ∈ leftSpine (G e₂.stepIdx) at hb2_ls
    rw [hb1_eq] at hbq_1 hb1_ls hedge_1 hreach_1_next
    rw [hb2_eq] at hb2_ls
    have he₁_tEnd : e₁.stepIdx ≤ tEnd := le_of_lt (lt_of_lt_of_le he₁_tau htau_tEnd)
    have he₂_tEnd : e₂.stepIdx ≤ tEnd := le_of_lt (lt_of_lt_of_le he₂_tau htau_tEnd)
    have hGs1_bst : (G e₁.stepIdx).IsBST :=
      (hG_bst_keys e₁.stepIdx (Finset.mem_Icc.mpr ⟨htStart_e₁, he₁_tEnd⟩)).1
    obtain ⟨hq1_not_rot, hno_mid, _⟩ := rotateRightEdge_leftSpine_props hGs1_bst hq1_ls hedge_1
    -- `subblockIndex1 subs e₁.y ∈ leftSpine (G e₁.stepIdx) ⊆ pi0` with `c₁ < q₁`, so `c₂ ≤ q₁`!
    have hq1_in_pi0 : subblockIndex1 subs e₁.y ∈ pi0 :=
      (leftSpine_sublist_of_reachable (hG_reach tStart e₁.stepIdx le_rfl htStart_e₁ he₁_tEnd)).subset hq1_ls
    obtain ⟨idx_q, hidx_q_len, hq1_pi0⟩ := pi0_idx_of_mem hq1_in_pi0
    have ht_lt_idx_q : t < idx_q := by
      rw [← pi0_lt_iff_idx ht_len hidx_q_len, ← hc₁_eq, hq1_pi0]
      exact hbq_1
    have hc₂_le_q₁ : c₂ ≤ subblockIndex1 subs e₁.y := by
      rcases eq_or_lt_of_le (show t + 1 ≤ idx_q by omega) with heq_q | hlt_q
      · subst idx_q; rw [hc₂_eq, hq1_pi0]
      · exact le_of_lt (by rw [hc₂_eq, ← hq1_pi0, pi0_lt_iff_idx ht1_len hidx_q_len]; exact hlt_q)
    rcases lt_or_eq_of_le hc₂_le_q₁ with hc₂_lt_q₁ | hq₁_eq_c₂
    · -- `c₁ < c₂ < q₁`: `c₂ ∉ leftSpine (G e₁.stepIdx)` by `hno_mid`, hence `c₂ ∉ leftSpine (G e₂.stepIdx)`!
      have hc₂_not_Gs1 : c₂ ∉ leftSpine (G e₁.stepIdx) := fun hc₂_in =>
        hno_mid c₂ hc₂_in ⟨hc₁_lt_c₂, hc₂_lt_q₁⟩
      have hsub12 := leftSpine_sublist_of_reachable
        (hG_reach e₁.stepIdx e₂.stepIdx htStart_e₁ hstep_le he₂_tEnd)
      exact hc₂_not_Gs1 (hsub12.subset hb2_ls)
    · -- `subblockIndex1 subs e₁.y = c₂`
      have hq₁_eq : subblockIndex1 subs e₁.y = c₂ := hq₁_eq_c₂.symm
      rw [hq₁_eq] at hq1_not_rot hreach_1_next he₁_exit_z
      rcases lt_or_eq_of_le hstep_le with hstep_lt | hstep_eq
      · -- `e₁.stepIdx + 1 ≤ e₂.stepIdx`: `c₂` is rotated off `leftSpine` at `e₁.stepIdx`!
        have hreach_rot_Gs2 : RightRotReachable (rotateRightEdge (G e₁.stepIdx) c₁ c₂) (G e₂.stepIdx) :=
          Relation.ReflTransGen.trans hreach_1_next
            (hG_reach (e₁.stepIdx + 1) e₂.stepIdx (by omega) (by omega) he₂_tEnd)
        exact hq1_not_rot ((leftSpine_sublist_of_reachable hreach_rot_Gs2).subset hb2_ls)
      · -- `e₁.stepIdx = e₂.stepIdx`: same `POP` step!
        have hex1_hi : e₁.x ≤ (subblock1 subs c₁).hi := (Finset.mem_Icc.mp he₁_x).2
        have hex2_lo : (subblock1 subs c₂).lo ≤ e₂.x := (Finset.mem_Icc.mp he₂_x).1
        have hSc1_lt_Sc2 : (subblock1 subs c₁).hi < (subblock1 subs c₂).lo := by
          have := hsub_lt c₁ c₂ (Finset.mem_Icc.mp hc₁_Icc).1 hc₁_lt_c₂
            (hK_eq.symm ▸ (Finset.mem_Icc.mp hc₂_Icc).2)
          exact this
        have hx1_lt_x2 : e₁.x < e₂.x := by omega
        obtain ⟨hj_eq_imp, hj_lt_imp⟩ := hrInt_ord e₁ he₁_rInt e₂ he₂_rInt hstep_eq
        rcases lt_trichotomy e₁.j e₂.j with hj_lt | hj_eq | hj_gt
        · have hz1_le_x2 : e₁.z ≤ e₂.x := hj_lt_imp hj_lt
          have hex2_hi : e₂.x ≤ (subblock1 subs c₂).hi := (Finset.mem_Icc.mp he₂_x).2
          omega
        · have he_eq := hj_eq_imp hj_eq
          rw [he_eq] at hx1_lt_x2
          exact lt_irrefl _ hx1_lt_x2
        · have hz2_le_x1 : e₂.z ≤ e₁.x :=
            (hrInt_ord e₂ he₂_rInt e₁ he₁_rInt hstep_eq.symm).2 hj_gt
          have he₂_xy := (hrInt_basic e₂ he₂_rInt).2.2
          omega
  -- Transitive strict reversal for `a ≤ t₁ < t₂ ≤ b`:
  have hrev_trans : ∀ {t₁ t₂ : ℕ}, a ≤ t₁ → t₁ < t₂ → t₂ ≤ b →
      leadPopKey P proc chain ℓ_val X p ((pi0[t₂]?).getD 0) <
        leadPopKey P proc chain ℓ_val X p ((pi0[t₁]?).getD 0) := by
    intro t₁ t₂ hat₁ ht₁₂ ht₂b
    obtain ⟨d, rfl⟩ : ∃ d, t₂ = t₁ + (d + 1) := ⟨t₂ - t₁ - 1, by omega⟩
    induction d with
    | zero => exact hrev_adj t₁ hat₁ (by omega)
    | succ d ihd =>
      exact lt_trans (hrev_adj (t₁ + d + 1) (by omega) (by omega)) (ihd (by omega) (by omega))
  refine ⟨hrev_adj, ?_⟩
  -- Part 1b: prove `rightReach G₀ c_{b+1} ≤ rightReach (G (popStepIdx (leadPopKey c_t) + 1)) c_t` by induction on `d = b - t`!
  have hstep_post : ∀ (d t : ℕ), b - t ≤ d → a ≤ t → t ≤ b →
      let ct := (pi0[t]?).getD 0
      let step_t := proc.popStepIdx (leadPopKey P proc chain ℓ_val X p ct)
      step_t < tauEmpty proc Sp ∧
      rightReach G₀ ((pi0[b + 1]?).getD 0) ≤ rightReach (G (step_t + 1)) ct := by
    intro d
    induction d with
    | zero =>
      intro t hbt hat htb
      have htb_eq : t = b := by omega
      subst t
      dsimp only
      have hb_len : b < pi0.length := by omega
      set cb := (pi0[b]?).getD 0
      have hcb_Fp : cb ∈ Fp := hrun b hat le_rfl
      obtain ⟨eb, _, heb_vXp, heb_x, hkey_b, _, _⟩ := hlead p cb hcb_Fp
      obtain ⟨_, _, heb_step, htStart_eb, heb_tau, _⟩ := hvXp_time eb heb_vXp
      rw [hkey_b, ← heb_step]
      obtain ⟨_, hbq_b, _, _, hqb_ls, hedge_b, hreach_b_next⟩ := h57_vXp eb heb_vXp
      have hcb_Icc : cb ∈ Finset.Icc 1 K_X := mem_Fp_Icc hcb_Fp
      have hbb_eq : subblockIndex1 subs eb.x = cb :=
        (hsub_c cb (hK_eq.symm ▸ hcb_Icc)).2.2.2.2.2 eb.x heb_x |>.1
      change subblockIndex1 subs eb.x < subblockIndex1 subs eb.y at hbq_b
      change IsRightRotEdge (G eb.stepIdx) (subblockIndex1 subs eb.x) (subblockIndex1 subs eb.y) at hedge_b
      change RightRotReachable (rotateRightEdge (G eb.stepIdx) (subblockIndex1 subs eb.x)
        (subblockIndex1 subs eb.y)) (G (eb.stepIdx + 1)) at hreach_b_next
      change subblockIndex1 subs eb.y ∈ leftSpine (G eb.stepIdx) at hqb_ls
      rw [hbb_eq] at hbq_b hedge_b hreach_b_next
      set qb := subblockIndex1 subs eb.y
      have heb_tEnd : eb.stepIdx ≤ tEnd := le_of_lt (lt_of_lt_of_le heb_tau htau_tEnd)
      have hGsb_bst : (G eb.stepIdx).IsBST :=
        (hG_bst_keys eb.stepIdx (Finset.mem_Icc.mpr ⟨htStart_eb, heb_tEnd⟩)).1
      have hqb_in_pi0 : qb ∈ pi0 :=
        (leftSpine_sublist_of_reachable (hG_reach tStart eb.stepIdx le_rfl htStart_eb heb_tEnd)).subset hqb_ls
      obtain ⟨idx_q, hidx_q_len, hqb_pi0⟩ := pi0_idx_of_mem hqb_in_pi0
      have hb_lt_idx_q : b < idx_q := by
        rw [← pi0_lt_iff_idx hb_len hidx_q_len, ← get_pi0 hb_len, hqb_pi0]
        exact hbq_b
      have h1 : rightReach G₀ ((pi0[b + 1]?).getD 0) ≤ rightReach G₀ qb := by
        have hqb_get : (pi0[idx_q]?).getD 0 = qb := by rw [get_pi0 hidx_q_len, hqb_pi0]
        rw [← hqb_get]
        exact rightReach_leftSpine_mono hG0_bst (by omega) hidx_q_len
      have h2 : rightReach G₀ qb ≤ rightReach (G eb.stepIdx) qb :=
        rightReach_le_of_reachable hG0_bst (hG_reach tStart eb.stepIdx le_rfl htStart_eb heb_tEnd) qb
      have h3 : rightReach (G eb.stepIdx) qb = rightReach (rotateRightEdge (G eb.stepIdx) cb qb) cb :=
        (rotateRightEdge_leftSpine_props hGsb_bst hqb_ls hedge_b).2.2.symm
      have h4 : rightReach (rotateRightEdge (G eb.stepIdx) cb qb) cb ≤ rightReach (G (eb.stepIdx + 1)) cb :=
        rightReach_le_of_reachable (rotateRightEdge_isBST hGsb_bst cb qb) hreach_b_next cb
      exact ⟨heb_tau, le_trans h1 (le_trans h2 (h3 ▸ h4))⟩
    | succ d ihd =>
      intro t hbt hat htb
      rcases eq_or_lt_of_le htb with rfl | htb_lt
      · exact ihd t (by omega) hat le_rfl
      dsimp only
      have ht_len : t < pi0.length := by omega
      set ct := (pi0[t]?).getD 0
      have hct_Fp : ct ∈ Fp := hrun t hat htb
      obtain ⟨et, _, het_vXp, het_x, hkey_t, _, _⟩ := hlead p ct hct_Fp
      obtain ⟨_, hets_Icc, het_step, htStart_et, het_tau, _⟩ := hvXp_time et het_vXp
      rw [hkey_t, ← het_step]
      obtain ⟨_, hbq_t, _, _, hqt_ls, hedge_t, hreach_t_next⟩ := h57_vXp et het_vXp
      have hct_Icc : ct ∈ Finset.Icc 1 K_X := mem_Fp_Icc hct_Fp
      have hbt_eq : subblockIndex1 subs et.x = ct :=
        (hsub_c ct (hK_eq.symm ▸ hct_Icc)).2.2.2.2.2 et.x het_x |>.1
      change subblockIndex1 subs et.x < subblockIndex1 subs et.y at hbq_t
      change IsRightRotEdge (G et.stepIdx) (subblockIndex1 subs et.x) (subblockIndex1 subs et.y) at hedge_t
      change RightRotReachable (rotateRightEdge (G et.stepIdx) (subblockIndex1 subs et.x)
        (subblockIndex1 subs et.y)) (G (et.stepIdx + 1)) at hreach_t_next
      change subblockIndex1 subs et.y ∈ leftSpine (G et.stepIdx) at hqt_ls
      rw [hbt_eq] at hbq_t hedge_t hreach_t_next
      set qt := subblockIndex1 subs et.y
      have het_tEnd : et.stepIdx ≤ tEnd := le_of_lt (lt_of_lt_of_le het_tau htau_tEnd)
      have hGst_bst : (G et.stepIdx).IsBST :=
        (hG_bst_keys et.stepIdx (Finset.mem_Icc.mpr ⟨htStart_et, het_tEnd⟩)).1
      have hqt_in_pi0 : qt ∈ pi0 :=
        (leftSpine_sublist_of_reachable (hG_reach tStart et.stepIdx le_rfl htStart_et het_tEnd)).subset hqt_ls
      obtain ⟨t', ht'_len, hqt_pi0⟩ := pi0_idx_of_mem hqt_in_pi0
      have ht_lt_t' : t < t' := by
        rw [← pi0_lt_iff_idx ht_len ht'_len, ← get_pi0 ht_len, hqt_pi0]
        exact hbq_t
      have hqt_get : (pi0[t']?).getD 0 = qt := by rw [get_pi0 ht'_len, hqt_pi0]
      have h3 : rightReach (G et.stepIdx) qt = rightReach (rotateRightEdge (G et.stepIdx) ct qt) ct :=
        (rotateRightEdge_leftSpine_props hGst_bst hqt_ls hedge_t).2.2.symm
      have h4 : rightReach (rotateRightEdge (G et.stepIdx) ct qt) ct ≤ rightReach (G (et.stepIdx + 1)) ct :=
        rightReach_le_of_reachable (rotateRightEdge_isBST hGst_bst ct qt) hreach_t_next ct
      by_cases ht'_gt_b : b + 1 ≤ t'
      · have h1 : rightReach G₀ ((pi0[b + 1]?).getD 0) ≤ rightReach G₀ qt := by
          rw [← hqt_get]
          exact rightReach_leftSpine_mono hG0_bst ht'_gt_b ht'_len
        have h2 : rightReach G₀ qt ≤ rightReach (G et.stepIdx) qt :=
          rightReach_le_of_reachable hG0_bst (hG_reach tStart et.stepIdx le_rfl htStart_et het_tEnd) qt
        exact ⟨het_tau, le_trans h1 (le_trans h2 (h3 ▸ h4))⟩
      · have ht'_le_b : t' ≤ b := by omega
        obtain ⟨het'_tau, hih_reach⟩ := ihd t' (by omega) (by omega) ht'_le_b
        rw [hqt_get] at het'_tau hih_reach
        -- `leadPopKey qt < leadPopKey ct`, so `popStepIdx (leadPopKey qt) + 1 ≤ et.stepIdx`!
        have hkey_lt : leadPopKey P proc chain ℓ_val X p qt < leadPopKey P proc chain ℓ_val X p ct := by
          rw [← hqt_get]
          exact hrev_trans hat ht_lt_t' ht'_le_b
        have hqt_Fp : qt ∈ Fp := by rw [← hqt_get]; exact hrun t' (by omega) ht'_le_b
        obtain ⟨et', _, het'_vXp, _, hkey_t', _, _⟩ := hlead p qt hqt_Fp
        obtain ⟨_, het's_Icc, het'_step, htStart_et', _, _⟩ := hvXp_time et' het'_vXp
        rw [hkey_t', ← het'_step] at het'_tau hih_reach
        rw [hkey_t', hkey_t] at hkey_lt
        have hstep_lt : et'.stepIdx < et.stepIdx := by
          rw [het'_step, het_step]
          exact (hpop_mono et'.s het's_Icc et.s hets_Icc).1.mp hkey_lt
        have hGst'_next_bst : (G (et'.stepIdx + 1)).IsBST :=
          (hG_bst_keys (et'.stepIdx + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).1
        have h2 : rightReach (G (et'.stepIdx + 1)) qt ≤ rightReach (G et.stepIdx) qt :=
          rightReach_le_of_reachable hGst'_next_bst
            (hG_reach (et'.stepIdx + 1) et.stepIdx (by omega) (by omega) het_tEnd) qt
        exact ⟨het_tau, le_trans hih_reach (le_trans h2 (h3 ▸ h4))⟩
  intro t hat htb
  obtain ⟨hstep_lt_tau, hrr_post⟩ := hstep_post (b - t) t le_rfl hat htb
  set ct := (pi0[t]?).getD 0
  set step_t := proc.popStepIdx (leadPopKey P proc chain ℓ_val X p ct)
  have hct_Fp : ct ∈ Fp := hrun t hat htb
  obtain ⟨et, _, het_vXp, _, hkey_t, _, _⟩ := hlead p ct hct_Fp
  obtain ⟨_, _, het_step, htStart_et, _, _⟩ := hvXp_time et het_vXp
  have htStart_post : tStart ≤ step_t + 1 := by
    have : step_t = et.stepIdx := by dsimp [step_t]; rw [hkey_t, het_step]
    omega
  have hpost_bst : (G (step_t + 1)).IsBST :=
    (hG_bst_keys (step_t + 1) (Finset.mem_Icc.mpr ⟨htStart_post, by omega⟩)).1
  have hreach_end : RightRotReachable (G (step_t + 1)) G_end :=
    hG_reach (step_t + 1) (tauEmpty proc Sp) htStart_post (by omega) htau_tEnd
  exact le_trans hrr_post (rightReach_le_of_reachable hpost_bst hreach_end ct)

/-! ## Section 4A: Active Window `I_p`, `cartesianExt`, and `phaseBlockBST` Transitions -/

private theorem proc_b1At_of_ne_nil {P : ℕ} (proc : FoldedPopProcess P) {τ : ℕ}
    (hτ_le : τ ≤ proc.steps.length) (hne : proc.treeAt τ ≠ .nil) :
    τ < proc.steps.length ∧ ∃ b, proc.b1At τ = some b ∧ b ∈ leftSpine (proc.treeAt τ) := by
  have hτ_lt : τ < proc.steps.length := by
    rcases lt_or_eq_of_le hτ_le with hlt | rfl
    · exact hlt
    · exact absurd (congrArg Prod.fst (proc_stateAt_end proc)) hne
  obtain ⟨hval, _⟩ := proc_step_at proc hτ_lt
  refine ⟨hτ_lt, ?_⟩
  cases hop : proc.steps[τ]'hτ_lt with
  | push w =>
    rw [hop] at hval
    rcases hval with ⟨_, _, _, hnil_iff, hb_ls⟩
    cases hb : (proc.stateAt τ).2 with
    | none => exact absurd (hnil_iff.mpr hb) hne
    | some b => exact ⟨b, hb, hb_ls b hb⟩
  | shift =>
    rw [hop] at hval
    rcases hval with ⟨b, hb, hb_ls, _⟩
    exact ⟨b, hb, hb_ls⟩
  | upperRot u v =>
    rw [hop] at hval
    rcases hval with ⟨b, _, hb, _, hb_ls, _⟩
    exact ⟨b, hb, hb_ls⟩
  | pop s =>
    rw [hop] at hval
    rcases hval with ⟨b, _, _, hb, hb_ls⟩
    exact ⟨b, hb, hb_ls⟩

private theorem active_window_props {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1
      ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1)) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    let Sp := subblock1 subs p
    let tStart := proc.popStepIdx Sp.lo
    let s_max := sMax proc Sp
    let tEmpty := tauEmpty proc Sp
    2 ≤ subs.length ∧ p < subs.length ∧
    1 ≤ Sp.lo ∧ Sp.lo ≤ s_max ∧ s_max ≤ Sp.hi ∧ Sp.hi < X.hi ∧ X.hi ≤ P ∧
    tStart < tEmpty ∧ tEmpty ≤ proc.steps.length ∧
    (∀ τ ≤ tEmpty, ∀ u ∈ Finset.Icc (Sp.hi + 1) P,
      ((proc.steps.take τ).filter (fun | .pop _ => true | _ => false)).length + 1 ≤ u) ∧
    (∀ τ, tStart ≤ τ → τ < tEmpty →
      s_max ∈ keyFinset (proc.treeAt τ) ∧
      proc.treeAt τ ≠ .nil ∧
      (∃ m₀ ∈ Sp.toFinset, (proc.treeAt τ).minKey? = some m₀ ∧ m₀ ≤ s_max) ∧
      (∀ w, proc.steps[τ]? = some (.push w) → w < s_max) ∧
      (∀ s', proc.steps[τ]? = some (.pop s') → s' ∈ Sp.toFinset ∧ s' ≤ s_max)) := by
  dsimp only
  set chain := scaleTreePartitionChain T P M
  set subs := childSubblocks (chain ℓ.succ) X
  set Sp := subblock1 subs p
  set tStart := proc.popStepIdx Sp.lo
  set s_max := sMax proc Sp
  set tEmpty := tauEmpty proc Sp
  obtain ⟨hp1, hp_sub1⟩ := Finset.mem_Icc.mp hp
  have hK2 : 2 ≤ subs.length := by omega
  have hp_lt_K : p < subs.length := by omega
  obtain ⟨hX1, _, hXP, _, hsub_c, hsub_lt, _, hlast_hi, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨_, hSp_in_chain, hSp_Xlo, hSp_lohi, _, _⟩ :=
    hsub_c p (Finset.mem_Icc.mpr ⟨hp1, le_of_lt hp_lt_K⟩)
  change X.lo ≤ Sp.lo at hSp_Xlo
  change Sp.lo ≤ Sp.hi at hSp_lohi
  have hSp_hi_lt_X : Sp.hi < X.hi := by
    have hlt := hsub_lt p subs.length hp1 hp_lt_K le_rfl
    have hlast_lohi := (hsub_c subs.length (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)).2.2.2.1
    change Sp.hi < (subblock1 subs subs.length).lo at hlt
    change (subblock1 subs subs.length).lo ≤ (subblock1 subs subs.length).hi at hlast_lohi
    change (subblock1 subs subs.length).hi = X.hi at hlast_hi
    omega
  obtain ⟨hbst_all, htree_laws⟩ := proc_tree_bst_and_step_keys proc
  obtain ⟨_, hpop_props, hpop_mono, hs0_iff, hins_props⟩ := popStepIdx_and_insStep_props proc
  have hSplo_Icc : Sp.lo ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨htStart_lt, htStart_some, _⟩ := hpop_props Sp.lo hSplo_Icc
  have hSplo_in_start : Sp.lo ∈ keyFinset (proc.treeAt tStart) := by
    have hstep := htree_laws tStart htStart_lt
    have hop : proc.steps[tStart]'htStart_lt = .pop Sp.lo := by
      rw [List.getElem?_eq_getElem htStart_lt] at htStart_some
      injection htStart_some
    rw [hop] at hstep
    exact hstep.1
  have hinter_ne : (keyFinset (proc.treeAt tStart) ∩ Sp.toFinset).Nonempty :=
    ⟨Sp.lo, Finset.mem_inter.mpr ⟨hSplo_in_start, Finset.mem_Icc.mpr ⟨le_rfl, hSp_lohi⟩⟩⟩
  obtain ⟨s_m, hs_m_mem, hs_m_eq⟩ := Finset.exists_mem_eq_sup _ hinter_ne id
  have hs_max_eq : s_max = s_m := hs_m_eq
  have hs_max_mem : s_max ∈ keyFinset (proc.treeAt tStart) ∩ Sp.toFinset := hs_max_eq ▸ hs_m_mem
  obtain ⟨hs_max_in_start, hs_max_Sp⟩ := Finset.mem_inter.mp hs_max_mem
  obtain ⟨hSplo_le_smax, hsmax_le_Sphi⟩ := Finset.mem_Icc.mp hs_max_Sp
  have hsmax_Icc : s_max ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨hpop_smax_lt, _, _⟩ := hpop_props s_max hsmax_Icc
  have htEmpty_eq : tEmpty = proc.popStepIdx s_max + 1 := rfl
  have htStart_le_popsmax : tStart ≤ proc.popStepIdx s_max :=
    (hpop_mono Sp.lo hSplo_Icc s_max hsmax_Icc).2.mp hSplo_le_smax
  have htStart_lt_tEmpty : tStart < tEmpty := by omega
  have htEmpty_le_len : tEmpty ≤ proc.steps.length := by omega
  have hins_smax : proc.insStep s_max < tStart :=
    ((hins_props s_max hsmax_Icc).2.2.2 tStart (le_of_lt htStart_lt)).mp hs_max_in_start |>.1
  refine ⟨hK2, hp_lt_K, by omega, hSplo_le_smax, hsmax_le_Sphi, hSp_hi_lt_X, hXP,
    htStart_lt_tEmpty, htEmpty_le_len, ?_, ?_⟩
  · intro τ hτ u hu
    have hu_Icc : u ∈ Finset.Icc 1 P :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hu).1; omega, (Finset.mem_Icc.mp hu).2⟩
    have hsmax_lt_u : s_max < u := by have := (Finset.mem_Icc.mp hu).1; omega
    have hpopsmax_lt_u : proc.popStepIdx s_max < proc.popStepIdx u :=
      (hpop_mono s_max hsmax_Icc u hu_Icc).1.mp hsmax_lt_u
    exact (hs0_iff τ (le_trans hτ htEmpty_le_len) u hu_Icc).mpr (by omega)
  · intro τ htStart_τ hτ_tEmpty
    have hτ_lt_len : τ < proc.steps.length := lt_of_lt_of_le hτ_tEmpty htEmpty_le_len
    have hsmax_in_τ : s_max ∈ keyFinset (proc.treeAt τ) :=
      ((hins_props s_max hsmax_Icc).2.2.2 τ (le_of_lt hτ_lt_len)).mpr
        ⟨lt_of_lt_of_le hins_smax htStart_τ, by omega⟩
    have hne_τ : proc.treeAt τ ≠ .nil := by
      intro hnil; simp [hnil, keyFinset] at hsmax_in_τ
    obtain ⟨ht_bst, ht_sub⟩ := hbst_all τ (le_of_lt hτ_lt_len)
    have hmin_ne : (proc.treeAt τ).minKey? ≠ none :=
      mt (minKey_bst_props ht_bst).1.mp hne_τ
    obtain ⟨m₀, hm₀⟩ := Option.ne_none_iff_exists'.mp hmin_ne
    obtain ⟨hm₀_mem, hm₀_le_all, _, _, _⟩ := (minKey_bst_props ht_bst).2 m₀ hm₀
    have hm₀_le_smax : m₀ ≤ s_max :=
      hm₀_le_all s_max ((mem_iff_mem_keyFinset _ s_max).mpr hsmax_in_τ)
    have hm₀_Icc : m₀ ∈ Finset.Icc 1 P :=
      ht_sub ((mem_iff_mem_keyFinset _ m₀).mp hm₀_mem)
    have hτ_le_popm₀ : τ ≤ proc.popStepIdx m₀ :=
      ((hins_props m₀ hm₀_Icc).2.2.2 τ (le_of_lt hτ_lt_len)).mp
        ((mem_iff_mem_keyFinset _ m₀).mp hm₀_mem) |>.2
    have hSplo_le_m₀ : Sp.lo ≤ m₀ :=
      (hpop_mono Sp.lo hSplo_Icc m₀ hm₀_Icc).2.mpr (le_trans htStart_τ hτ_le_popm₀)
    have hm₀_Sp : m₀ ∈ Sp.toFinset := Finset.mem_Icc.mpr ⟨hSplo_le_m₀, le_trans hm₀_le_smax hsmax_le_Sphi⟩
    refine ⟨hsmax_in_τ, hne_τ, ⟨m₀, hm₀_Sp, hm₀, hm₀_le_smax⟩, ?_, ?_⟩
    · intro w hw
      obtain ⟨hval, _⟩ := proc_step_at proc hτ_lt_len
      have hop : proc.steps[τ]'hτ_lt_len = .push w := by
        rw [List.getElem?_eq_getElem hτ_lt_len] at hw; injection hw
      rw [hop] at hval
      exact hval.2.2.1 s_max ((mem_iff_mem_keyFinset _ s_max).mpr hsmax_in_τ)
    · intro s' hs'
      obtain ⟨hval, _⟩ := proc_step_at proc hτ_lt_len
      have hop : proc.steps[τ]'hτ_lt_len = .pop s' := by
        rw [List.getElem?_eq_getElem hτ_lt_len] at hs'; injection hs'
      rw [hop] at hval
      rcases hval with ⟨_, _, hmin_s', _, _⟩
      change (proc.treeAt τ).minKey? = some s' at hmin_s'
      rw [hm₀] at hmin_s'
      injection hmin_s' with hs'_eq
      subst s'
      exact ⟨hm₀_Sp, hm₀_le_smax⟩

private theorem cartesianFromSortedGo_bst_and_mem (insFn : ℕ → ℕ) :
    ∀ (fuel : ℕ) (xs : List ℕ), xs.Pairwise (· < ·) → xs.length ≤ fuel →
      (cartesianFromSortedGo insFn fuel xs).IsBST ∧
      ∀ u, u ∈ cartesianFromSortedGo insFn fuel xs ↔ u ∈ xs := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs _ hlen
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hnil
    exact ⟨SplayDeque.Direct.isBSTNil, fun _ => ⟨(fun h => by cases h), (fun h => by cases h)⟩⟩
  | succ fuel ih =>
    intro xs hpw hlen
    cases xs with
    | nil =>
      exact ⟨SplayDeque.Direct.isBSTNil, fun _ => ⟨(fun h => by cases h), (fun h => by cases h)⟩⟩
    | cons x rest =>
      unfold cartesianFromSortedGo
      dsimp only
      set stepFn : ℕ → ℕ → ℕ := fun best y =>
        if insFn y < insFn best ∨ (insFn y = insFn best ∧ y < best) then y else best
      set r := rest.foldl stepFn x
      have hr_mem : r ∈ x :: rest := by
        suffices ∀ (ys : List ℕ) (acc : ℕ), acc ∈ x :: rest →
            (∀ y ∈ ys, y ∈ x :: rest) → ys.foldl stepFn acc ∈ x :: rest from
          this rest x List.mem_cons_self (fun y hy => List.mem_cons_of_mem x hy)
        intro ys
        induction ys with
        | nil => intro acc hacc _; exact hacc
        | cons y ys ihys =>
          intro acc hacc hsub
          simp only [List.foldl_cons]
          apply ihys
          · dsimp only [stepFn]
            split_ifs
            · exact hsub y List.mem_cons_self
            · exact hacc
          · exact fun z hz => hsub z (List.mem_cons_of_mem y hz)
      have len_filter_lt : ∀ (zs : List ℕ) (p : ℕ → Bool),
          r ∈ zs → p r = false → (zs.filter p).length < zs.length := by
        intro zs p
        induction zs with
        | nil => intro h; cases h
        | cons z zs ihz =>
          intro hrz hpr
          rcases List.mem_cons.mp hrz with rfl | hrz_tail
          · simp only [List.filter_cons, hpr, Bool.false_eq_true, ↓reduceIte, List.length_cons]
            exact Nat.lt_succ_of_le (List.length_filter_le p zs)
          · have hlt := ihz hrz_tail hpr
            rw [List.filter_cons, List.length_cons]
            cases hpz : p z
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact Nat.lt_succ_of_lt hlt
            · simp only [↓reduceIte, List.length_cons]
              exact Nat.succ_lt_succ hlt
      have hlen_l : ((x :: rest).filter (· < r)).length ≤ fuel := by
        have := len_filter_lt (x :: rest) (· < r) hr_mem (by simp)
        simp only [List.length_cons] at hlen this
        omega
      have hlen_r : ((x :: rest).filter (r < ·)).length ≤ fuel := by
        have := len_filter_lt (x :: rest) (r < ·) hr_mem (by simp)
        simp only [List.length_cons] at hlen this
        omega
      obtain ⟨hl_bst, hl_iff⟩ := ih ((x :: rest).filter (· < r)) (hpw.filter _) hlen_l
      obtain ⟨hr_bst, hr_iff⟩ := ih ((x :: rest).filter (r < ·)) (hpw.filter _) hlen_r
      refine ⟨?_, ?_⟩
      · refine SplayDeque.Direct.isBSTNode r _ _ ?_ ?_ hl_bst hr_bst
        · rw [SplayDeque.Direct.forallTree_iff]
          intro u hu
          have := List.mem_filter.mp ((hl_iff u).mp hu)
          simpa using this.2
        · rw [SplayDeque.Direct.forallTree_iff]
          intro u hu
          have := List.mem_filter.mp ((hr_iff u).mp hu)
          simpa using this.2
      · intro u
        rw [BinaryTree.mem_node_iff, hl_iff, hr_iff, List.mem_filter, List.mem_filter]
        constructor
        · rintro (rfl | ⟨hu, _⟩ | ⟨hu, _⟩)
          · exact hr_mem
          · exact hu
          · exact hu
        · intro hu
          rcases lt_trichotomy u r with hlt | rfl | hgt
          · exact Or.inr (Or.inl ⟨hu, by simpa using hlt⟩)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr ⟨hu, by simpa using hgt⟩)

private theorem cartesianBSTWith_bst_and_mem (insFn : ℕ → ℕ) (S : Finset ℕ) :
    (cartesianBSTWith insFn S).IsBST ∧
    ∀ u, u ∈ cartesianBSTWith insFn S ↔ u ∈ S := by
  unfold cartesianBSTWith
  dsimp only
  set xs := (List.range (S.sup id + 1)).filter (· ∈ S)
  have hpw : xs.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  obtain ⟨hbst, hmem⟩ := cartesianFromSortedGo_bst_and_mem insFn xs.length xs hpw le_rfl
  refine ⟨hbst, fun u => (hmem u).trans ?_⟩
  simp only [xs, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hu
    exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hu), hu⟩

private theorem cartesianBSTWith_empty (insFn : ℕ → ℕ) :
    cartesianBSTWith insFn ∅ = .nil := by
  cases h : cartesianBSTWith insFn ∅ with
  | nil => rfl
  | node k l r =>
    have hk : k ∈ cartesianBSTWith insFn ∅ := by rw [h]; exact .here
    have := (cartesianBSTWith_bst_and_mem insFn ∅).2 k |>.mp hk
    simp at this

private theorem slotFilter_mem_iff (U : Finset ℕ) (lo hi : Option ℕ) (u : ℕ) :
    u ∈ U.filter (fun x => lo.elim true (· < x) ∧ hi.elim true (x < ·)) ↔
      u ∈ U ∧ lo.elim True (· < u) ∧ hi.elim True (u < ·) := by
  cases lo <;> cases hi <;> simp

private theorem mem_fillCartesianSlots_lt_hi (insFn : ℕ → ℕ) (U : Finset ℕ) :
    ∀ (lo : Option ℕ) (b : ℕ) (t : BinaryTree ℕ),
      t.IsBST → (∀ x ∈ t, x < b) →
      ∀ w ∈ fillCartesianSlots insFn U lo (some b) t, w < b := by
  intro lo b t
  induction t generalizing lo b with
  | nil =>
    intro _ _ w hw
    unfold fillCartesianSlots at hw
    have hw' := (cartesianBSTWith_bst_and_mem insFn _).2 w |>.mp hw
    have := (slotFilter_mem_iff U lo (some b) w).mp hw'
    exact this.2.2
  | node k l r ihl ihr =>
    intro ht hlt_b w hw
    obtain ⟨hlt, _, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hkb : k < b := hlt_b k .here
    unfold fillCartesianSlots at hw
    rcases BinaryTree.mem_node_iff.mp hw with rfl | hL | hR
    · exact hkb
    · exact lt_trans (ihl lo k hl hlt' w hL) hkb
    · exact ihr (some k) b hr (fun x hx => hlt_b x (.right hx)) w hR

private theorem fillCartesianSlots_bst_and_mem (insFn : ℕ → ℕ) (U : Finset ℕ) :
    ∀ (lo hi : Option ℕ) (t : BinaryTree ℕ),
      t.IsBST →
      (∀ x ∈ t, lo.elim True (· < x) ∧ hi.elim True (x < ·)) →
      (∀ x ∈ t, x ∉ U) →
      (fillCartesianSlots insFn U lo hi t).IsBST ∧
      ∀ w, w ∈ fillCartesianSlots insFn U lo hi t ↔
        w ∈ t ∨ (w ∈ U ∧ lo.elim True (· < w) ∧ hi.elim True (w < ·)) := by
  intro lo hi t
  induction t generalizing lo hi with
  | nil =>
    intro _ _ _
    unfold fillCartesianSlots
    obtain ⟨hbst, hmem⟩ := cartesianBSTWith_bst_and_mem insFn _
    refine ⟨hbst, fun w => (hmem w).trans ?_⟩
    rw [slotFilter_mem_iff]
    exact ⟨Or.inr, fun h => h.elim (fun hm => by cases hm) id⟩
  | node k l r ihl ihr =>
    intro ht hbounds hdisj
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    obtain ⟨hlo_k, hhi_k⟩ := hbounds k .here
    have hk_not_U : k ∉ U := hdisj k .here
    obtain ⟨hl_bst, hl_mem⟩ := ihl lo (some k) hl
      (fun x hx => ⟨(hbounds x (.left hx)).1, hlt' x hx⟩)
      (fun x hx => hdisj x (.left hx))
    obtain ⟨hr_bst, hr_mem⟩ := ihr (some k) hi hr
      (fun x hx => ⟨hgt' x hx, (hbounds x (.right hx)).2⟩)
      (fun x hx => hdisj x (.right hx))
    unfold fillCartesianSlots
    refine ⟨?_, ?_⟩
    · refine SplayDeque.Direct.isBSTNode k _ _ ?_ ?_ hl_bst hr_bst
      · rw [SplayDeque.Direct.forallTree_iff]
        intro w hw
        rcases (hl_mem w).mp hw with hwl | ⟨_, _, hwk⟩
        · exact hlt' w hwl
        · exact hwk
      · rw [SplayDeque.Direct.forallTree_iff]
        intro w hw
        rcases (hr_mem w).mp hw with hwr | ⟨_, hkw, _⟩
        · exact hgt' w hwr
        · exact hkw
    · intro w
      rw [BinaryTree.mem_node_iff, hl_mem, hr_mem]
      constructor
      · rintro (rfl | (hwl | ⟨hwU, hlo_w, hwk⟩) | (hwr | ⟨hwU, hkw, hhi_w⟩))
        · exact Or.inl .here
        · exact Or.inl (.left hwl)
        · exact Or.inr ⟨hwU, hlo_w, by cases hi with | none => trivial | some b => exact lt_trans hwk hhi_k⟩
        · exact Or.inl (.right hwr)
        · exact Or.inr ⟨hwU, by cases lo with | none => trivial | some a => exact lt_trans hlo_k hkw, hhi_w⟩
      · rintro (hwt | ⟨hwU, hlo_w, hhi_w⟩)
        · rcases BinaryTree.mem_node_iff.mp hwt with rfl | hwl | hwr
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (Or.inl hwl))
          · exact Or.inr (Or.inr (Or.inl hwr))
        · rcases lt_trichotomy w k with hwk | rfl | hkw
          · exact Or.inr (Or.inl (Or.inr ⟨hwU, hlo_w, hwk⟩))
          · exact absurd hwU hk_not_U
          · exact Or.inr (Or.inr (Or.inr ⟨hwU, hkw, hhi_w⟩))

private theorem cartesianExt_bst_and_mem {P : ℕ} (proc : FoldedPopProcess P)
    {τ : ℕ} (hτ : τ ≤ proc.steps.length) :
    let s₀ := ((proc.steps.take τ).filter (fun | .pop _ => true | _ => false)).length
    (cartesianExt proc τ).IsBST ∧
    keyFinset (cartesianExt proc τ) = Finset.Icc (s₀ + 1) P := by
  dsimp only
  set s₀ := ((proc.steps.take τ).filter (fun | .pop _ => true | _ => false)).length
  obtain ⟨hbst_all, _⟩ := proc_tree_bst_and_step_keys proc
  obtain ⟨_, _, _, hs0_iff, hins_props⟩ := popStepIdx_and_insStep_props proc
  obtain ⟨ht_bst, ht_sub⟩ := hbst_all τ hτ
  have ht_sub_s0 : keyFinset (proc.treeAt τ) ⊆ Finset.Icc (s₀ + 1) P := by
    intro u hu
    have hu_Icc := ht_sub hu
    have hτ_le_pop := ((hins_props u hu_Icc).2.2.2 τ hτ).mp hu |>.2
    exact Finset.mem_Icc.mpr ⟨(hs0_iff τ hτ u hu_Icc).mpr hτ_le_pop, (Finset.mem_Icc.mp hu_Icc).2⟩
  set U := Finset.Icc (s₀ + 1) P \ keyFinset (proc.treeAt τ)
  obtain ⟨hext_bst, hext_mem⟩ := fillCartesianSlots_bst_and_mem proc.insStep U none none
    (proc.treeAt τ) ht_bst (fun _ _ => ⟨trivial, trivial⟩)
    (fun x hx hxU => (Finset.mem_sdiff.mp hxU).2 ((mem_iff_mem_keyFinset _ x).mp hx))
  change (cartesianExt proc τ).IsBST at hext_bst
  refine ⟨hext_bst, ?_⟩
  ext u
  rw [← mem_iff_mem_keyFinset]
  change u ∈ fillCartesianSlots proc.insStep U none none (proc.treeAt τ) ↔ _
  rw [hext_mem]
  simp only [Option.elim, and_true, mem_iff_mem_keyFinset]
  constructor
  · rintro (hu_t | hu_U)
    · exact ht_sub_s0 hu_t
    · exact (Finset.mem_sdiff.mp hu_U).1
  · intro hu_Icc
    by_cases hu_t : u ∈ keyFinset (proc.treeAt τ)
    · exact Or.inl hu_t
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hu_Icc, hu_t⟩)

private theorem lcaBST_between :
    ∀ (t : BinaryTree ℕ) (x y z : ℕ), lcaBST t x y = some z →
      (x ≤ z ∧ z ≤ y) ∨ (y ≤ z ∧ z ≤ x)
  | .nil, _, _, _, h => by simp [lcaBST] at h
  | .node k l r, x, y, z, h => by
    unfold lcaBST at h
    split_ifs at h with h1 h2
    · exact lcaBST_between l x y z h
    · exact lcaBST_between r x y z h
    · injection h with hkz; subst hkz; omega

private theorem isLCAClosed_interval (t : BinaryTree ℕ) (lo hi : ℕ) :
    IsLCAClosed t {u : ℕ | lo ≤ u ∧ u ≤ hi} := by
  intro x _ y _ hx hy z hz
  have hbet := lcaBST_between t x y z hz
  change lo ≤ x ∧ x ≤ hi at hx
  change lo ≤ y ∧ y ≤ hi at hy
  change lo ≤ z ∧ z ≤ hi
  omega

private theorem isLCAClosed_gt_le (t : BinaryTree ℕ) (lo_strict hi : ℕ) :
    IsLCAClosed t {u : ℕ | lo_strict < u ∧ u ≤ hi} := by
  intro x _ y _ hx hy z hz
  have hbet := lcaBST_between t x y z hz
  change lo_strict < x ∧ x ≤ hi at hx
  change lo_strict < y ∧ y ≤ hi at hy
  change lo_strict < z ∧ z ≤ hi
  omega

private theorem restrictTree_eq_nil_of_disjoint :
    ∀ (t : BinaryTree ℕ) (S : Set ℕ), (∀ x ∈ t, x ∉ S) → restrictTree t S = .nil
  | .nil, _, _ => rfl
  | .node u A B, S, hdisj => by
    have hu : u ∉ S := hdisj u .here
    have hnoB : ¬ ∃ b ∈ B, b ∈ S := fun ⟨b, hbB, hbS⟩ => hdisj b (.right hbB) hbS
    unfold restrictTree
    simp only [hu, hnoB, ↓reduceIte]
    exact restrictTree_eq_nil_of_disjoint A S (fun a ha => hdisj a (.left ha))

private theorem fillCartesianSlots_erase_of_lt_lo (insFn : ℕ → ℕ) (U : Finset ℕ) (w : ℕ) :
    ∀ (a : ℕ) (hi : Option ℕ) (t : BinaryTree ℕ),
      w < a → (∀ k ∈ t, w < k) →
      fillCartesianSlots insFn (U.erase w) (some a) hi t =
        fillCartesianSlots insFn U (some a) hi t := by
  intro a hi t hwa ht_gt
  induction t generalizing a hi with
  | nil =>
    unfold fillCartesianSlots
    congr 1
    ext u
    rw [slotFilter_mem_iff, slotFilter_mem_iff, Finset.mem_erase]
    simp only [Option.elim]
    constructor
    · rintro ⟨⟨_, huU⟩, hau, hhi⟩; exact ⟨huU, hau, hhi⟩
    · rintro ⟨huU, hau, hhi⟩; exact ⟨⟨by omega, huU⟩, hau, hhi⟩
  | node k l r ihl ihr =>
    unfold fillCartesianSlots
    rw [ihl a (some k) hwa (fun x hx => ht_gt x (.left hx)),
        ihr k hi (ht_gt k .here) (fun x hx => ht_gt x (.right hx))]

private theorem fillCartesianSlots_some_lo_eq_none (insFn : ℕ → ℕ) (U : Finset ℕ) (s' : ℕ)
    (hU_gt : ∀ u ∈ U, s' < u) :
    ∀ (hi : Option ℕ) (t : BinaryTree ℕ),
      fillCartesianSlots insFn U (some s') hi t = fillCartesianSlots insFn U none hi t := by
  intro hi t
  induction t generalizing hi with
  | nil =>
    unfold fillCartesianSlots
    congr 1
    ext u
    rw [slotFilter_mem_iff, slotFilter_mem_iff]
    simp only [Option.elim, true_and]
    exact ⟨fun ⟨hu, _, hh⟩ => ⟨hu, hh⟩, fun ⟨hu, hh⟩ => ⟨hu, hU_gt u hu, hh⟩⟩
  | node k l r ihl _ =>
    unfold fillCartesianSlots
    rw [ihl (some k)]

private theorem restrictTree_fill_erase_left (insFn : ℕ → ℕ) (U : Finset ℕ)
    {w s_max R_p X_hi : ℕ} (hsmax_Rp : s_max ≤ R_p) :
    let S_hi : Set ℕ := {u : ℕ | R_p < u ∧ u ≤ X_hi}
    ∀ (hi : Option ℕ) (L : BinaryTree ℕ),
      L.IsBST → s_max ∈ L → (∀ k ∈ L, w < k) →
      restrictTree (fillCartesianSlots insFn (U.erase w) (some w) hi L) S_hi =
        restrictTree (fillCartesianSlots insFn U none hi L) S_hi := by
  dsimp only
  set S_hi : Set ℕ := {u : ℕ | R_p < u ∧ u ≤ X_hi}
  intro hi L
  induction L generalizing hi with
  | nil => intro _ hsmax _; cases hsmax
  | node k l r ihl _ =>
    intro hL hsmax hgt_w
    obtain ⟨hlt, hgt, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp hL
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    have hwk : w < k := hgt_w k .here
    unfold fillCartesianSlots
    rw [fillCartesianSlots_erase_of_lt_lo insFn U w k hi r hwk (fun x hx => hgt_w x (.right hx))]
    set R' := fillCartesianSlots insFn U (some k) hi r
    set L₁ := fillCartesianSlots insFn (U.erase w) (some w) (some k) l
    set L₂ := fillCartesianSlots insFn U none (some k) l
    by_cases hk_le : k ≤ R_p
    · have hk_not : k ∉ S_hi := fun hS => by have := hS.1; omega
      have hL₁_nil : restrictTree L₁ S_hi = .nil := by
        apply restrictTree_eq_nil_of_disjoint
        intro u hu hS
        have huk := mem_fillCartesianSlots_lt_hi insFn (U.erase w) (some w) k l hl hlt' u hu
        have := hS.1; omega
      have hL₂_nil : restrictTree L₂ S_hi = .nil := by
        apply restrictTree_eq_nil_of_disjoint
        intro u hu hS
        have huk := mem_fillCartesianSlots_lt_hi insFn U none k l hl hlt' u hu
        have := hS.1; omega
      unfold restrictTree
      simp only [hk_not, ↓reduceIte, hL₁_nil, hL₂_nil]
    · have hRp_lt_k : R_p < k := by omega
      have hsmax_in_l : s_max ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hsmax with rfl | h_in_l | h_in_r
        · omega
        · exact h_in_l
        · have := hgt' s_max h_in_r; omega
      have hL_eq : restrictTree L₁ S_hi = restrictTree L₂ S_hi :=
        ihl (some k) hl hsmax_in_l (fun x hx => hgt_w x (.left hx))
      conv_lhs => unfold restrictTree
      conv_rhs => unfold restrictTree
      split_ifs <;> simp [hL_eq]

private theorem restrictTree_push_modifyLeftAt (insFn : ℕ → ℕ) (U : Finset ℕ)
    {w b s_max R_p X_hi : ℕ} (hw_Rp : w ≤ R_p) (hsmax_Rp : s_max ≤ R_p) :
    let S_hi : Set ℕ := {u : ℕ | R_p < u ∧ u ≤ X_hi}
    ∀ (hi : Option ℕ) (t : BinaryTree ℕ),
      t.IsBST → b ∈ leftSpine t → s_max ∈ t → (∀ k ∈ t, w < k) →
      restrictTree (fillCartesianSlots insFn (U.erase w) none hi
        (modifyLeftAt t b (fun L1 => .node w .nil L1))) S_hi =
      restrictTree (fillCartesianSlots insFn U none hi t) S_hi := by
  dsimp only
  set S_hi : Set ℕ := {u : ℕ | R_p < u ∧ u ≤ X_hi}
  intro hi t
  induction t generalizing hi with
  | nil => intro _ hb _ _; simp [leftSpine] at hb
  | node k l r ihl _ =>
    intro ht hb hsmax hgt_w
    obtain ⟨hlt, hgt, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    have hwk : w < k := hgt_w k .here
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb_l | rfl
    · have hbk : b < k := hlt' b (mem_of_mem_leftSpine hb_l)
      have hmod : modifyLeftAt (.node k l r) b (fun L1 => .node w .nil L1) =
          .node k (modifyLeftAt l b (fun L1 => .node w .nil L1)) r := by
        simp [modifyLeftAt, hbk]
      rw [hmod]
      unfold fillCartesianSlots
      rw [fillCartesianSlots_erase_of_lt_lo insFn U w k hi r hwk (fun x hx => hgt_w x (.right hx))]
      set R' := fillCartesianSlots insFn U (some k) hi r
      set L₁ := fillCartesianSlots insFn (U.erase w) none (some k)
        (modifyLeftAt l b (fun L1 => .node w .nil L1))
      set L₂ := fillCartesianSlots insFn U none (some k) l
      by_cases hk_le : k ≤ R_p
      · have hk_not : k ∉ S_hi := fun hS => by have := hS.1; omega
        obtain ⟨hmod_bst, hmod_keys⟩ :=
          modifyLeftAt_push_bst_keys hl hb_l (fun x hx => hgt_w x (.left hx))
        have hmod_lt_k : ∀ x ∈ modifyLeftAt l b (fun L1 => .node w .nil L1), x < k := by
          intro x hx
          have hx_kf := (mem_iff_mem_keyFinset _ x).mp hx
          rw [hmod_keys, Finset.mem_insert] at hx_kf
          rcases hx_kf with rfl | hxl
          · exact hwk
          · exact hlt' x ((mem_iff_mem_keyFinset l x).mpr hxl)
        have hL₁_nil : restrictTree L₁ S_hi = .nil := by
          apply restrictTree_eq_nil_of_disjoint
          intro u hu hS
          have huk := mem_fillCartesianSlots_lt_hi insFn (U.erase w) none k _
            hmod_bst hmod_lt_k u hu
          have := hS.1; omega
        have hL₂_nil : restrictTree L₂ S_hi = .nil := by
          apply restrictTree_eq_nil_of_disjoint
          intro u hu hS
          have huk := mem_fillCartesianSlots_lt_hi insFn U none k l hl hlt' u hu
          have := hS.1; omega
        unfold restrictTree
        simp only [hk_not, ↓reduceIte, hL₁_nil, hL₂_nil]
      · have hsmax_in_l : s_max ∈ l := by
          rcases BinaryTree.mem_node_iff.mp hsmax with rfl | h_in_l | h_in_r
          · omega
          · exact h_in_l
          · have := hgt' s_max h_in_r; omega
        have hL_eq : restrictTree L₁ S_hi = restrictTree L₂ S_hi :=
          ihl (some k) hl hb_l hsmax_in_l (fun x hx => hgt_w x (.left hx))
        conv_lhs => unfold restrictTree
        conv_rhs => unfold restrictTree
        split_ifs <;> simp [hL_eq]
    · -- `b = k`
      have hmod : modifyLeftAt (.node b l r) b (fun L1 => .node w .nil L1) =
          .node b (.node w .nil l) r := by
        simp [modifyLeftAt]
      rw [hmod]
      conv_lhs => unfold fillCartesianSlots
      conv_rhs => unfold fillCartesianSlots
      rw [fillCartesianSlots_erase_of_lt_lo insFn U w b hi r hwk (fun x hx => hgt_w x (.right hx))]
      set R' := fillCartesianSlots insFn U (some b) hi r
      by_cases hb_le : b ≤ R_p
      · have hb_not : b ∉ S_hi := fun hS => by have := hS.1; omega
        obtain ⟨hwl_bst, hwl_keys⟩ :
            (BinaryTree.node w .nil l).IsBST ∧ keyFinset (.node w .nil l) = insert w (keyFinset l) := by
          refine ⟨SplayDeque.Direct.isBSTNode w .nil l .left ?_ SplayDeque.Direct.isBSTNil hl, ?_⟩
          · rw [SplayDeque.Direct.forallTree_iff]
            exact fun x hx => hgt_w x (.left hx)
          · simp [keyFinset]
        have hwl_lt_b : ∀ x ∈ BinaryTree.node w .nil l, x < b := by
          intro x hx
          rcases BinaryTree.mem_node_iff.mp hx with rfl | h0 | hxl
          · exact hwk
          · cases h0
          · exact hlt' x hxl
        have hL₁_nil : restrictTree
            (fillCartesianSlots insFn (U.erase w) none (some b) (.node w .nil l)) S_hi = .nil := by
          apply restrictTree_eq_nil_of_disjoint
          intro u hu hS
          have hub := mem_fillCartesianSlots_lt_hi insFn (U.erase w) none b _ hwl_bst hwl_lt_b u hu
          have := hS.1; omega
        have hL₂_nil : restrictTree (fillCartesianSlots insFn U none (some b) l) S_hi = .nil := by
          apply restrictTree_eq_nil_of_disjoint
          intro u hu hS
          have hub := mem_fillCartesianSlots_lt_hi insFn U none b l hl hlt' u hu
          have := hS.1; omega
        conv_lhs => unfold restrictTree
        conv_rhs => unfold restrictTree
        simp only [hb_not, ↓reduceIte, hL₁_nil, hL₂_nil]
      · have hsmax_in_l : s_max ∈ l := by
          rcases BinaryTree.mem_node_iff.mp hsmax with rfl | h_in_l | h_in_r
          · omega
          · exact h_in_l
          · have := hgt' s_max h_in_r; omega
        set C_w := cartesianBSTWith insFn
          ((U.erase w).filter (fun u => (none : Option ℕ).elim true (· < u) ∧ (some w).elim true (u < ·)))
        set L₁ := fillCartesianSlots insFn (U.erase w) (some w) (some b) l
        set L₂ := fillCartesianSlots insFn U none (some b) l
        have hfill_w : fillCartesianSlots insFn (U.erase w) none (some b) (.node w .nil l) =
            .node w C_w L₁ := rfl
        rw [hfill_w]
        have hw_not : w ∉ S_hi := fun hS => by have := hS.1; omega
        have hCw_disj : ∀ u ∈ C_w, u ∉ S_hi := by
          intro u hu hS
          have hu' := (cartesianBSTWith_bst_and_mem insFn _).2 u |>.mp hu
          have huw := ((slotFilter_mem_iff (U.erase w) none (some w) u).mp hu').2.2
          change u < w at huw
          have := hS.1; omega
        have hCw_nil : restrictTree C_w S_hi = .nil := restrictTree_eq_nil_of_disjoint C_w S_hi hCw_disj
        have hnode_w : restrictTree (.node w C_w L₁) S_hi = restrictTree L₁ S_hi := by
          conv_lhs => unfold restrictTree
          simp only [hw_not, ↓reduceIte]
          split_ifs with hex
          · rfl
          · rw [hCw_nil]
            symm
            exact restrictTree_eq_nil_of_disjoint L₁ S_hi (fun x hx hxS => hex ⟨x, hx, hxS⟩)
        have hL_eq : restrictTree L₁ S_hi = restrictTree L₂ S_hi :=
          restrictTree_fill_erase_left insFn U hsmax_Rp (some b) l hl hsmax_in_l
            (fun x hx => hgt_w x (.left hx))
        have hcomb : restrictTree (.node w C_w L₁) S_hi = restrictTree L₂ S_hi :=
          hnode_w.trans hL_eq
        conv_lhs => unfold restrictTree
        conv_rhs => unfold restrictTree
        split_ifs <;> simp [hcomb]

private theorem fillCartesianSlots_rotateRightEdge (insFn : ℕ → ℕ) (U : Finset ℕ) :
    ∀ (lo hi : Option ℕ) (t : BinaryTree ℕ) {u v : ℕ},
      IsRightRotEdge t u v →
      IsRightRotEdge (fillCartesianSlots insFn U lo hi t) u v ∧
      fillCartesianSlots insFn U lo hi (rotateRightEdge t u v) =
        rotateRightEdge (fillCartesianSlots insFn U lo hi t) u v := by
  intro lo hi t u v hedge
  rcases hedge with ⟨A, B, C, hv_mem, hsub⟩
  induction t generalizing lo hi with
  | nil => cases hv_mem
  | node k l r ihl ihr =>
    by_cases hvk : v < k
    · unfold subtreeAtKey at hsub
      simp only [hvk, ↓reduceIte] at hsub
      have hv_l : v ∈ l := by
        have : v ∈ subtreeAtKey l v := by rw [hsub]; exact .here
        exact mem_of_mem_subtreeAtKey this
      obtain ⟨⟨A', B', C', hv_fl, hsub_fl⟩, hrot_fl⟩ := ihl lo (some k) hv_l hsub
      refine ⟨⟨A', B', C', .left hv_fl, ?_⟩, ?_⟩
      · unfold fillCartesianSlots subtreeAtKey
        simp [hvk, hsub_fl]
      · simp [rotateRightEdge, hvk, fillCartesianSlots, hrot_fl]
    · by_cases hkv : k < v
      · unfold subtreeAtKey at hsub
        simp only [hvk, hkv, ↓reduceIte] at hsub
        have hv_r : v ∈ r := by
          have : v ∈ subtreeAtKey r v := by rw [hsub]; exact .here
          exact mem_of_mem_subtreeAtKey this
        obtain ⟨⟨A', B', C', hv_fr, hsub_fr⟩, hrot_fr⟩ := ihr (some k) hi hv_r hsub
        refine ⟨⟨A', B', C', .right hv_fr, ?_⟩, ?_⟩
        · unfold fillCartesianSlots subtreeAtKey
          simp [hvk, hkv, hsub_fr]
        · simp [rotateRightEdge, hvk, hkv, fillCartesianSlots, hrot_fr]
      · have hkv_eq : k = v := by omega
        subst k
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l; subst r
        refine ⟨⟨fillCartesianSlots insFn U lo (some u) A,
          fillCartesianSlots insFn U (some u) (some v) B,
          fillCartesianSlots insFn U (some v) hi C,
          by simp [fillCartesianSlots],
          by simp [fillCartesianSlots, subtreeAtKey]⟩, ?_⟩
        simp [rotateRightEdge, fillCartesianSlots]

private theorem fillCartesianSlots_spliceMin (insFn : ℕ → ℕ) (U : Finset ℕ) {s' : ℕ}
    (hU_gt : ∀ u ∈ U, s' < u) :
    ∀ (hi : Option ℕ) (t : BinaryTree ℕ),
      t.IsBST → t.minKey? = some s' →
      let ft := fillCartesianSlots insFn U none hi t
      ft ≠ .nil ∧ ft.minKey? = some s' ∧
      fillCartesianSlots insFn U none hi (spliceMin t) = spliceMin ft := by
  intro hi t
  induction t generalizing hi with
  | nil => intro _ hm; simp [BinaryTree.minKey?] at hm
  | node k l r ihl _ =>
    intro ht hm
    obtain ⟨_, _, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    unfold BinaryTree.minKey? at hm
    cases hlm : l.minKey? with
    | none =>
      rw [hlm] at hm
      injection hm with hks; subst k
      have hl_nil : l = .nil := (minKey_bst_props hl).1.mp hlm
      subst hl_nil
      have hleft_nil : fillCartesianSlots insFn U none (some s') .nil = .nil := by
        unfold fillCartesianSlots
        have hemp : U.filter (fun u => (none : Option ℕ).elim true (· < u) ∧
            (some s').elim true (u < ·)) = ∅ := by
          ext u
          rw [slotFilter_mem_iff]
          simp only [Option.elim, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨huU, hus⟩
          exact lt_asymm (hU_gt u huU) hus
        rw [hemp, cartesianBSTWith_empty]
      dsimp only
      have hft_eq : fillCartesianSlots insFn U none hi (.node s' .nil r) =
          .node s' .nil (fillCartesianSlots insFn U (some s') hi r) := by
        conv_lhs => unfold fillCartesianSlots
        rw [hleft_nil]
      rw [hft_eq]
      refine ⟨by simp, by simp [BinaryTree.minKey?], ?_⟩
      simp only [spliceMin]
      exact (fillCartesianSlots_some_lo_eq_none insFn U s' hU_gt hi r).symm
    | some ml =>
      rw [hlm] at hm
      injection hm with hmls; subst ml
      have hl_ne : l ≠ .nil := by rintro rfl; simp [BinaryTree.minKey?] at hlm
      have hsp_t : spliceMin (.node k l r) = .node k (spliceMin l) r := by
        cases l with
        | nil => contradiction
        | node lk ll lr => rfl
      obtain ⟨hfl_ne, hfl_min, hfl_sp⟩ := ihl (some k) hl hlm
      dsimp only at hfl_ne hfl_min hfl_sp ⊢
      have hft_eq : fillCartesianSlots insFn U none hi (.node k l r) =
          .node k (fillCartesianSlots insFn U none (some k) l)
            (fillCartesianSlots insFn U (some k) hi r) := rfl
      have hsp_ft : spliceMin (fillCartesianSlots insFn U none hi (.node k l r)) =
          .node k (spliceMin (fillCartesianSlots insFn U none (some k) l))
            (fillCartesianSlots insFn U (some k) hi r) := by
        rw [hft_eq]
        cases hfl : fillCartesianSlots insFn U none (some k) l with
        | nil => exact absurd hfl hfl_ne
        | node lk ll lr => rfl
      refine ⟨by rw [hft_eq]; simp, ?_, ?_⟩
      · rw [hft_eq]
        unfold BinaryTree.minKey?
        rw [hfl_min]
      · have hfill_sp : fillCartesianSlots insFn U none hi (.node k (spliceMin l) r) =
            .node k (fillCartesianSlots insFn U none (some k) (spliceMin l))
              (fillCartesianSlots insFn U (some k) hi r) := rfl
        rw [hsp_t, hsp_ft, hfill_sp, hfl_sp]

private theorem isRightRotEdge_of_adj_leftSpine :
    ∀ (t : BinaryTree ℕ), t.IsBST →
      ∀ {idx : ℕ} {x y : ℕ},
        (leftSpine t)[idx]? = some x → (leftSpine t)[idx + 1]? = some y →
        IsRightRotEdge t x y := by
  intro t
  induction t with
  | nil => intro _ idx x y hx _; simp [leftSpine] at hx
  | node k l r ihl _ =>
    intro ht idx x y hx hy
    obtain ⟨hlt, _, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    simp only [leftSpine] at hx hy
    by_cases hidx1 : idx + 1 < (leftSpine l).length
    · have hidx : idx < (leftSpine l).length := by omega
      rw [List.getElem?_append_left hidx] at hx
      rw [List.getElem?_append_left hidx1] at hy
      obtain ⟨A, B, C, hy_l, hsub_l⟩ := ihl hl hx hy
      have hyk : y < k := hlt' y hy_l
      exact ⟨A, B, C, .left hy_l, by simp [subtreeAtKey, hyk, hsub_l]⟩
    · have hlen_hy : idx + 1 < (leftSpine l ++ [k]).length := (List.getElem?_eq_some_iff.mp hy).1
      simp only [List.length_append, List.length_singleton] at hlen_hy
      have hidx_eq : idx + 1 = (leftSpine l).length := by omega
      rw [List.getElem?_append_right (by omega), hidx_eq, Nat.sub_self] at hy
      simp only [List.getElem?_cons_zero] at hy
      injection hy with hky; subst k
      have hidx_lt : idx < (leftSpine l).length := by omega
      rw [List.getElem?_append_left hidx_lt] at hx
      -- `x` is the last element of `leftSpine l`, which is the root of `l`!
      cases l with
      | nil => simp [leftSpine] at hidx_lt
      | node lx A B =>
        simp only [leftSpine, List.length_append, List.length_singleton] at hidx_eq
        have hidx_A : idx = (leftSpine A).length := by omega
        rw [leftSpine, hidx_A, List.getElem?_append_right le_rfl, Nat.sub_self] at hx
        simp only [List.getElem?_cons_zero] at hx
        injection hx with hlx; subst lx
        exact ⟨A, B, r, .here, by simp [subtreeAtKey]⟩

private theorem isRightRotEdge_spliceMin_above :
    ∀ (t : BinaryTree ℕ) {s' x y : ℕ},
      t.IsBST → t.minKey? = some s' → s' < x → x < y →
      IsRightRotEdge t x y → IsRightRotEdge (spliceMin t) x y := by
  intro t s' x y ht hm hsx hxy ⟨A, B, C, hy_mem, hsub⟩
  induction t with
  | nil => cases hy_mem
  | node k l r ihl _ =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    obtain ⟨hs_mem, _, _, _, _⟩ := (minKey_bst_props ht).2 s' hm
    by_cases hyk : y < k
    · have hs_in_l : s' ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hs_mem with rfl | hL | hR
        · omega
        · exact hL
        · have := hgt' s' hR; omega
      have hl_ne : l ≠ .nil := fun h => by subst h; cases hs_in_l
      have hlm : l.minKey? = some s' := by
        unfold BinaryTree.minKey? at hm
        cases h : l.minKey? with
        | none => exact absurd ((minKey_bst_props hl).1.mp h) hl_ne
        | some ml => rw [h] at hm; exact hm
      have hsp : spliceMin (.node k l r) = .node k (spliceMin l) r := by
        cases l with
        | nil => contradiction
        | node _ _ _ => rfl
      unfold subtreeAtKey at hsub
      simp only [hyk, ↓reduceIte] at hsub
      have hy_l : y ∈ l := by
        have : y ∈ subtreeAtKey l y := by rw [hsub]; exact .here
        exact mem_of_mem_subtreeAtKey this
      obtain ⟨A', B', C', hy_sp, hsub_sp⟩ := ihl hl hlm hy_l hsub
      rw [hsp]
      exact ⟨A', B', C', .left hy_sp, by simp [subtreeAtKey, hyk, hsub_sp]⟩
    · by_cases hky : k < y
      · unfold subtreeAtKey at hsub
        simp only [hyk, hky, ↓reduceIte] at hsub
        have hy_r : y ∈ r := by
          have : y ∈ subtreeAtKey r y := by rw [hsub]; exact .here
          exact mem_of_mem_subtreeAtKey this
        cases l with
        | nil =>
          simp only [spliceMin]
          exact ⟨A, B, C, hy_r, hsub⟩
        | node lk ll lr =>
          have hsp : spliceMin (.node k (.node lk ll lr) r) =
              .node k (spliceMin (.node lk ll lr)) r := rfl
          rw [hsp]
          exact ⟨A, B, C, .right hy_r, by simp [subtreeAtKey, hyk, hky, hsub]⟩
      · have hky_eq : k = y := by omega
        subst k
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l; subst r
        obtain ⟨_, hgt_x, _, _⟩ := (SplayDeque.Direct.isBSTNode_iff x A B).mp hl
        have hgt_x' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt_x
        have hs_in_A : s' ∈ A := by
          rcases BinaryTree.mem_node_iff.mp hs_mem with rfl | hL | hR
          · omega
          · rcases BinaryTree.mem_node_iff.mp hL with rfl | hA | hB
            · omega
            · exact hA
            · have := hgt_x' s' hB; omega
          · have := hgt' s' hR; omega
        have hA_ne : A ≠ .nil := fun h => by subst h; cases hs_in_A
        have hsp_x : spliceMin (.node x A B) = .node x (spliceMin A) B := by
          cases A with
          | nil => contradiction
          | node _ _ _ => rfl
        have hsp_y : spliceMin (.node y (.node x A B) C) =
            .node y (.node x (spliceMin A) B) C := by
          rw [show spliceMin (.node y (.node x A B) C) =
            .node y (spliceMin (.node x A B)) C from rfl, hsp_x]
        rw [hsp_y]
        exact ⟨spliceMin A, B, C, .here, by simp [subtreeAtKey]⟩

private theorem isRightRotEdge_rotateRightEdge_above :
    ∀ (t : BinaryTree ℕ) {u v x y : ℕ},
      u < v → v < x → x < y →
      IsRightRotEdge t x y → IsRightRotEdge (rotateRightEdge t u v) x y := by
  intro t u v x y huv hvx hxy ⟨A, B, C, hy_mem, hsub⟩
  induction t with
  | nil => cases hy_mem
  | node k l r ihl ihr =>
    by_cases hyk : y < k
    · have hvk : v < k := by omega
      unfold subtreeAtKey at hsub
      simp only [hyk, ↓reduceIte] at hsub
      have hy_l : y ∈ l := by
        have : y ∈ subtreeAtKey l y := by rw [hsub]; exact .here
        exact mem_of_mem_subtreeAtKey this
      obtain ⟨A', B', C', hy_rl, hsub_rl⟩ := ihl hy_l hsub
      have hrot : rotateRightEdge (.node k l r) u v = .node k (rotateRightEdge l u v) r := by
        simp [rotateRightEdge, hvk]
      rw [hrot]
      exact ⟨A', B', C', .left hy_rl, by simp [subtreeAtKey, hyk, hsub_rl]⟩
    · by_cases hky : k < y
      · unfold subtreeAtKey at hsub
        simp only [hyk, hky, ↓reduceIte] at hsub
        have hy_r : y ∈ r := by
          have : y ∈ subtreeAtKey r y := by rw [hsub]; exact .here
          exact mem_of_mem_subtreeAtKey this
        unfold rotateRightEdge
        split_ifs with hvk hkv
        · exact ⟨A, B, C, .right hy_r, by simp [subtreeAtKey, hyk, hky, hsub]⟩
        · obtain ⟨A', B', C', hy_rr, hsub_rr⟩ := ihr hy_r hsub
          exact ⟨A', B', C', .right hy_rr, by simp [subtreeAtKey, hyk, hky, hsub_rr]⟩
        · have hkv_eq : k = v := by omega
          subst k
          cases l with
          | nil => exact ⟨A, B, C, .right hy_r, by simp [subtreeAtKey, hyk, hky, hsub]⟩
          | node lx a b =>
            dsimp only
            split_ifs with hlx
            · subst lx
              have huy : ¬ y < u := by omega
              have hlt_uy : u < y := by omega
              have hsub_u : subtreeAtKey (.node u a (.node v b r)) y = .node y (.node x A B) C := by
                unfold subtreeAtKey
                simp only [huy, hlt_uy, ↓reduceIte]
                unfold subtreeAtKey
                simp only [hyk, hky, ↓reduceIte, hsub]
              exact ⟨A, B, C, .right (.right hy_r), hsub_u⟩
            · exact ⟨A, B, C, .right hy_r, by simp [subtreeAtKey, hyk, hky, hsub]⟩
      · have hky_eq : k = y := by omega
        subst k
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l; subst r
        have hvy : v < y := by omega
        have hrot : rotateRightEdge (.node y (.node x A B) C) u v =
            .node y (.node x (rotateRightEdge A u v) B) C := by
          simp [rotateRightEdge, hvy, hvx]
        rw [hrot]
        exact ⟨rotateRightEdge A u v, B, C, .here, by simp [subtreeAtKey]⟩

private inductive PhaseBlockStepRel (S_hi : Set ℕ) (rInt_τ : Set InternalPopRot) :
    BinaryTree ℕ → BinaryTree ℕ → Prop where
  | refl (B : BinaryTree ℕ) : PhaseBlockStepRel S_hi rInt_τ B B
  | step {B₁ B₂ : BinaryTree ℕ} (e : InternalPopRot) :
      PhaseBlockStepRel S_hi rInt_τ B₁ B₂ →
      e ∈ rInt_τ → e.x < e.y → e.x ∈ S_hi → e.y ∈ S_hi →
      B₂.IsBST → IsRightRotEdge B₂ e.x e.y →
      PhaseBlockStepRel S_hi rInt_τ B₁ (rotateRightEdge B₂ e.x e.y)

private theorem adjacentPairs_getElem? {α : Type} :
    ∀ (xs : List α) (idx : ℕ) (h : 2 * idx + 1 < xs.length),
      (adjacentPairs xs)[idx]? =
        some (xs[2 * idx]'(by omega), xs[2 * idx + 1]'(by omega))
  | [], _, h => by have : ([] : List α).length = 0 := rfl; omega
  | [a], _, h => by have : ([a] : List α).length = 1 := rfl; omega
  | a :: b :: rest, 0, _ => by simp [adjacentPairs]
  | a :: b :: rest, idx + 1, h => by
    simp only [adjacentPairs, List.getElem?_cons_succ]
    have hrest : 2 * idx + 1 < rest.length := by simp at h; omega
    rw [adjacentPairs_getElem? rest idx hrest]
    rfl

private theorem adjacentPairs_length_ge {α : Type} :
    ∀ (xs : List α) (h : ℕ), 2 * h ≤ xs.length → h ≤ (adjacentPairs xs).length
  | _, 0, _ => Nat.zero_le _
  | [], _ + 1, hle => by have : ([] : List α).length = 0 := rfl; omega
  | [a], _ + 1, hle => by have : ([a] : List α).length = 1 := rfl; omega
  | _ :: _ :: rest, h + 1, hle => by
    simp only [adjacentPairs, List.length_cons]
    exact Nat.succ_le_succ (adjacentPairs_length_ge rest h (by simp at hle; omega))

private theorem phaseBlockBST_bst_and_step_in_Ip
    (h_3_1 : ∀ {α : Type} [LinearOrder α] (t : BinaryTree α) (S : Set α),
      t.IsBST → IsLCAClosed t S →
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
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1
      ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1)) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    let Sp := subblock1 subs p
    let tStart := proc.popStepIdx Sp.lo
    let tEmpty := tauEmpty proc Sp
    let S_hi : Set ℕ := {u : ℕ | Sp.hi < u ∧ u ≤ X.hi}
    (∀ τ ≤ tEmpty,
      (phaseBlockBST P proc chain ℓ_val X p τ).IsBST ∧
      keyFinset (phaseBlockBST P proc chain ℓ_val X p τ) = Finset.Icc (Sp.hi + 1) X.hi) ∧
    (∀ τ (_hτ_start : tStart ≤ τ) (hτ_empty : τ < tEmpty),
      let hτ := lt_of_lt_of_le hτ_empty (active_window_props hValid proc ℓ X hX hp).2.2.2.2.2.2.2.2.1
      let Bp := phaseBlockBST P proc chain ℓ_val X p τ
      let BpNext := phaseBlockBST P proc chain ℓ_val X p (τ + 1)
      match proc.steps[τ]'hτ with
      | .push _ => BpNext = Bp
      | .shift => BpNext = Bp
      | .upperRot u v =>
        BpNext = Bp ∨
          (u ∈ S_hi ∧ v ∈ S_hi ∧ u < v ∧ IsRightRotEdge Bp u v ∧
            BpNext = rotateRightEdge Bp u v)
      | .pop _ =>
        PhaseBlockStepRel S_hi {e : InternalPopRot | e ∈ proc.rInt ∧ e.stepIdx = τ} Bp BpNext) := by
  dsimp only
  have hwin_all := active_window_props hValid proc ℓ X hX hp
  dsimp only at hwin_all
  set chain := scaleTreePartitionChain T P M
  set ℓ_val := ℓ.val + 1
  set subs := childSubblocks (chain ℓ.succ) X
  set Sp := subblock1 subs p
  set tStart := proc.popStepIdx Sp.lo
  set s_max := sMax proc Sp
  set tEmpty := tauEmpty proc Sp
  set S_hi : Set ℕ := {u : ℕ | Sp.hi < u ∧ u ≤ X.hi}
  have hℓ : 1 ≤ ℓ_val ∧ ℓ_val ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  have hfin_eq : (⟨ℓ_val, Nat.lt_succ_of_le hℓ.2⟩ : Fin (M + 1)) = ℓ.succ := rfl
  obtain ⟨_, _, hSplo1, hSplo_smax, hsmax_Sphi, hSphi_X, hXP, _, htEmpty_len, hs0_above, hwin⟩ :=
    hwin_all
  obtain ⟨hbst_all, htree_laws⟩ := proc_tree_bst_and_step_keys proc
  have hBp_eq : ∀ τ, phaseBlockBST P proc chain ℓ_val X p τ =
      restrictTree (cartesianExt proc τ) S_hi := by
    intro τ
    unfold phaseBlockBST
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq]
    rfl
  have isSingle_iff_right : ∀ {t : BinaryTree ℕ} {x y : ℕ}, x < y →
      (IsSingleRotEdge t x y ↔ IsRightRotEdge t x y) ∧
      rotateEdge t x y = rotateRightEdge t x y := by
    intro t x y hxy
    refine ⟨?_, by simp [rotateEdge, hxy]⟩
    unfold IsSingleRotEdge
    constructor
    · rintro (⟨_, hr⟩ | ⟨hyx, _⟩)
      · exact hr
      · omega
    · intro hr; exact Or.inl ⟨hxy, hr⟩
  have hBp_bst_keys : ∀ τ ≤ tEmpty,
      (phaseBlockBST P proc chain ℓ_val X p τ).IsBST ∧
      keyFinset (phaseBlockBST P proc chain ℓ_val X p τ) = Finset.Icc (Sp.hi + 1) X.hi := by
    intro τ hτ
    rw [hBp_eq]
    obtain ⟨hext_bst, hext_keys⟩ := cartesianExt_bst_and_mem proc (le_trans hτ htEmpty_len)
    obtain ⟨⟨hres_bst, hres_mem⟩, _, _⟩ :=
      h_3_1 (cartesianExt proc τ) S_hi hext_bst (isLCAClosed_gt_le _ Sp.hi X.hi)
    refine ⟨hres_bst, ?_⟩
    ext u
    rw [← mem_iff_mem_keyFinset, hres_mem, mem_iff_mem_keyFinset, hext_keys]
    change (_ ∈ Finset.Icc _ _ ∧ (Sp.hi < u ∧ u ≤ X.hi)) ↔ _
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨_, h1, h2⟩; omega
    · intro ⟨h1, h2⟩
      have hu_Icc : u ∈ Finset.Icc (Sp.hi + 1) P := Finset.mem_Icc.mpr ⟨h1, le_trans h2 hXP⟩
      exact ⟨⟨hs0_above τ hτ u hu_Icc, le_trans h2 hXP⟩, by omega, h2⟩
  refine ⟨hBp_bst_keys, ?_⟩
  intro τ hτ_start hτ_empty
  have hτ : τ < proc.steps.length := lt_of_lt_of_le hτ_empty htEmpty_len
  obtain ⟨hsmax_in, hne_τ, ⟨m₀, hm₀_Sp, hm₀_min, hm₀_smax⟩, hpush_lt, hpop_Sp⟩ :=
    hwin τ hτ_start hτ_empty
  obtain ⟨hval, hst⟩ := proc_step_at proc hτ
  have htree_step := htree_laws τ hτ
  set isPop : FoldedOp → Bool := fun | .pop _ => true | _ => false
  have htake_succ : proc.steps.take (τ + 1) = proc.steps.take τ ++ [proc.steps[τ]'hτ] :=
    List.take_succ_eq_append_getElem hτ
  cases hop : proc.steps[τ]'hτ with
  | push w =>
    dsimp only
    rw [hop] at hval htree_step
    rcases hval with ⟨_, _, hgt_w, _, hb_ls⟩
    have hw_lt_smax : w < s_max := hpush_lt w ((List.getElem?_eq_getElem hτ).trans (congrArg some hop))
    obtain ⟨_, b, hb_eq, hb_in_ls⟩ := proc_b1At_of_ne_nil proc (le_of_lt hτ) hne_τ
    have ht1_eq : proc.treeAt (τ + 1) =
        modifyLeftAt (proc.treeAt τ) b (fun L1 => .node w .nil L1) := by
      have := congrArg Prod.fst hst
      rw [hop] at this
      unfold FoldedOp.step at this
      unfold FoldedPopProcess.b1At at hb_eq
      rw [hb_eq] at this
      exact this
    have hs0_eq : ((proc.steps.take (τ + 1)).filter isPop).length =
        ((proc.steps.take τ).filter isPop).length := by
      rw [htake_succ, hop, List.filter_append]; simp [isPop]
    set s₀ := ((proc.steps.take τ).filter isPop).length
    set U_τ := Finset.Icc (s₀ + 1) P \ keyFinset (proc.treeAt τ)
    have hU_next : Finset.Icc (((proc.steps.take (τ + 1)).filter isPop).length + 1) P \
        keyFinset (proc.treeAt (τ + 1)) = U_τ.erase w := by
      rw [hs0_eq, htree_step.2.2.2]
      ext x
      simp only [U_τ, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      tauto
    rw [hBp_eq, hBp_eq]
    unfold cartesianExt
    change restrictTree (fillCartesianSlots proc.insStep
        (Finset.Icc (((proc.steps.take (τ + 1)).filter isPop).length + 1) P \
          keyFinset (proc.treeAt (τ + 1))) none none (proc.treeAt (τ + 1))) S_hi =
      restrictTree (fillCartesianSlots proc.insStep U_τ none none (proc.treeAt τ)) S_hi
    rw [hU_next, ht1_eq]
    exact restrictTree_push_modifyLeftAt proc.insStep U_τ (by omega) hsmax_Sphi none
      (proc.treeAt τ) (hbst_all τ (le_of_lt hτ)).1 hb_in_ls
      ((mem_iff_mem_keyFinset _ s_max).mpr hsmax_in) hgt_w
  | shift =>
    dsimp only
    rw [hop] at htree_step
    have hs0_eq : ((proc.steps.take (τ + 1)).filter isPop).length =
        ((proc.steps.take τ).filter isPop).length := by
      rw [htake_succ, hop, List.filter_append]; simp [isPop]
    rw [hBp_eq, hBp_eq]
    unfold cartesianExt
    change restrictTree (fillCartesianSlots proc.insStep
        (Finset.Icc (((proc.steps.take (τ + 1)).filter isPop).length + 1) P \
          keyFinset (proc.treeAt (τ + 1))) none none (proc.treeAt (τ + 1))) S_hi =
      restrictTree (fillCartesianSlots proc.insStep
        (Finset.Icc (((proc.steps.take τ).filter isPop).length + 1) P \
          keyFinset (proc.treeAt τ)) none none (proc.treeAt τ)) S_hi
    rw [hs0_eq, htree_step]
  | upperRot u v =>
    dsimp only
    rw [hop] at hval htree_step
    rcases hval with ⟨_, _, _, _, _, _, huv, _, _, _, hedge_uv⟩
    have hs0_eq : ((proc.steps.take (τ + 1)).filter isPop).length =
        ((proc.steps.take τ).filter isPop).length := by
      rw [htake_succ, hop, List.filter_append]; simp [isPop]
    have hU_eq : Finset.Icc (((proc.steps.take (τ + 1)).filter isPop).length + 1) P \
        keyFinset (proc.treeAt (τ + 1)) =
        Finset.Icc (((proc.steps.take τ).filter isPop).length + 1) P \
          keyFinset (proc.treeAt τ) := by
      rw [hs0_eq, htree_step.2]
    obtain ⟨hedge_ext, hrot_ext⟩ := fillCartesianSlots_rotateRightEdge proc.insStep
      (Finset.Icc (((proc.steps.take τ).filter isPop).length + 1) P \ keyFinset (proc.treeAt τ))
      none none (proc.treeAt τ) hedge_uv
    have hext_next : cartesianExt proc (τ + 1) = rotateRightEdge (cartesianExt proc τ) u v := by
      unfold cartesianExt
      change fillCartesianSlots proc.insStep
          (Finset.Icc (((proc.steps.take (τ + 1)).filter isPop).length + 1) P \
            keyFinset (proc.treeAt (τ + 1))) none none (proc.treeAt (τ + 1)) =
        rotateRightEdge (fillCartesianSlots proc.insStep
          (Finset.Icc (((proc.steps.take τ).filter isPop).length + 1) P \
            keyFinset (proc.treeAt τ)) none none (proc.treeAt τ)) u v
      rw [hU_eq, htree_step.1, hrot_ext]
    obtain ⟨hext_bst, _⟩ := cartesianExt_bst_and_mem proc (le_of_lt hτ)
    obtain ⟨_, h31_rot, _⟩ :=
      h_3_1 (cartesianExt proc τ) S_hi hext_bst (isLCAClosed_gt_le _ Sp.hi X.hi)
    obtain ⟨hiff_s, hrot_s⟩ := isSingle_iff_right (t := cartesianExt proc τ) huv
    have h31_uv := h31_rot u v (hiff_s.mpr hedge_ext)
      (hrot_s.symm ▸ isLCAClosed_gt_le _ Sp.hi X.hi)
    rw [hBp_eq, hBp_eq, hext_next, ← hrot_s]
    by_cases huv_S : u ∈ S_hi ∧ v ∈ S_hi
    · right
      obtain ⟨hedge_res, hres_eq⟩ := h31_uv.1 huv_S
      obtain ⟨hiff_res, hrot_res⟩ := isSingle_iff_right
        (t := restrictTree (cartesianExt proc τ) S_hi) huv
      exact ⟨huv_S.1, huv_S.2, huv, hiff_res.mp hedge_res, hres_eq.trans hrot_res⟩
    · left
      exact h31_uv.2 huv_S
  | pop s' =>
    dsimp only
    rw [hop] at hval htree_step
    rcases hval with ⟨b, _, hmin_s', hb_eq, hb_ls⟩
    obtain ⟨hs'_Sp, hs'_smax⟩ :=
      hpop_Sp s' ((List.getElem?_eq_getElem hτ).trans (congrArg some hop))
    have hs'_not_S : s' ∉ S_hi := by
      intro hS
      have := (Finset.mem_Icc.mp hs'_Sp).2
      have := hS.1
      omega
    -- Relate `s₀(τ + 1)` and `s'`
    obtain ⟨_, hpop_props, _, hs0_iff, _⟩ := popStepIdx_and_insStep_props proc
    have hs'_Icc : s' ∈ Finset.Icc 1 P :=
      (hbst_all τ (le_of_lt hτ)).2 htree_step.1
    have hτ_eq_pop : τ = proc.popStepIdx s' :=
      ((hpop_props s' hs'_Icc).2.2 τ hτ).mp
        ((List.getElem?_eq_getElem hτ).trans (congrArg some hop))
    set s₀ := ((proc.steps.take τ).filter isPop).length
    have hs0_next : ((proc.steps.take (τ + 1)).filter isPop).length = s₀ + 1 := by
      rw [htake_succ, hop, List.filter_append]; simp [isPop, s₀]
    have hs0_le : s₀ + 1 ≤ s' := (hs0_iff τ (le_of_lt hτ) s' hs'_Icc).mpr (by omega)
    have hs0_not : ¬ ((s₀ + 1) + 1 ≤ s') := by
      rw [← hs0_next]
      exact mt (hs0_iff (τ + 1) (by omega) s' hs'_Icc).mp (by omega)
    have hs'_eq_s0 : s' = s₀ + 1 := by omega
    set U_τ := Finset.Icc (s₀ + 1) P \ keyFinset (proc.treeAt τ)
    have hU_gt : ∀ u ∈ U_τ, s' < u := by
      intro u hu
      obtain ⟨hu_Icc, hu_not⟩ := Finset.mem_sdiff.mp hu
      have hle : s' ≤ u := hs'_eq_s0 ▸ (Finset.mem_Icc.mp hu_Icc).1
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact absurd htree_step.1 hu_not
      · exact hlt
    have hU_next : Finset.Icc (((proc.steps.take (τ + 1)).filter isPop).length + 1) P \
        keyFinset (proc.treeAt (τ + 1)) = U_τ := by
      rw [hs0_next, htree_step.2.2, ← hs'_eq_s0]
      ext x
      simp only [U_τ, ← hs'_eq_s0, Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, hnot⟩
        exact ⟨⟨by omega, h2⟩, fun hx => hnot ⟨hx, by omega⟩⟩
      · rintro ⟨⟨h1, h2⟩, hnot⟩
        have hxs : x ≠ s' := fun h => hnot (h ▸ htree_step.1)
        exact ⟨⟨by omega, h2⟩, fun ⟨hx, _⟩ => hnot hx⟩
    obtain ⟨ht_bst, _⟩ := hbst_all τ (le_of_lt hτ)
    obtain ⟨hext_ne, hext_min, hsp_comm⟩ :=
      fillCartesianSlots_spliceMin proc.insStep U_τ hU_gt none (proc.treeAt τ) ht_bst hmin_s'
    obtain ⟨hext_bst, _⟩ := cartesianExt_bst_and_mem proc (le_of_lt hτ)
    have hsp_restrict : restrictTree (spliceMin (cartesianExt proc τ)) S_hi =
        restrictTree (cartesianExt proc τ) S_hi := by
      obtain ⟨_, _, h31_sp⟩ :=
        h_3_1 (cartesianExt proc τ) S_hi hext_bst (isLCAClosed_gt_le _ Sp.hi X.hi)
      exact ((h31_sp hext_ne).1.2 s' hext_min).2 hs'_not_S
    set ls := leftSpine (proc.treeAt τ)
    set sub := takeThrough ls b
    set k := sub.length - 1
    set h := (k - 1) / 2
    have ht1_eq : proc.treeAt (τ + 1) =
        if k = 0 then spliceMin (proc.treeAt τ)
        else ((adjacentPairs sub.tail).take h).foldl
          (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin (proc.treeAt τ)) := by
      have h1 := congrArg Prod.fst hst
      rw [hop] at h1
      dsimp only [FoldedOp.step] at h1
      have hb_st : (proc.stateAt τ).2 = some b := hb_eq
      have ht_st : (proc.stateAt τ).1 = proc.treeAt τ := rfl
      rw [hb_st, ht_st] at h1
      dsimp only at h1
      by_cases hk_test : (takeThrough (leftSpine (proc.treeAt τ)) b).length - 1 = 0
      · have hk_zero : k = 0 := hk_test
        simp only [hk_test, hk_zero, ↓reduceIte] at h1 ⊢
        exact h1
      · have hk_nz : k ≠ 0 := hk_test
        simp only [hk_test, hk_nz, ↓reduceIte] at h1 ⊢
        exact h1
    rw [hBp_eq, hBp_eq]
    by_cases hk0 : k = 0
    · simp only [hk0, ↓reduceIte] at ht1_eq
      change proc.treeAt (τ + 1) = spliceMin (proc.treeAt τ) at ht1_eq
      have hext_sp : cartesianExt proc (τ + 1) = spliceMin (cartesianExt proc τ) := by
        unfold cartesianExt
        change fillCartesianSlots proc.insStep
            (Finset.Icc (((proc.steps.take (τ + 1)).filter isPop).length + 1) P \
              keyFinset (proc.treeAt (τ + 1))) none none (proc.treeAt (τ + 1)) = _
        rw [hU_next, ht1_eq]
        exact hsp_comm
      rw [hext_sp, hsp_restrict]
      exact .refl _
    · simp only [hk0, ↓reduceIte] at ht1_eq
      set pairs := (adjacentPairs sub.tail).take h
      change proc.treeAt (τ + 1) =
        pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin (proc.treeAt τ)) at ht1_eq
      -- Sublist / pairwise facts on `sub`
      have hpw_ls : ls.Pairwise (· < ·) := leftSpine_pairwise_lt ht_bst
      obtain ⟨hsub_pref, hsub_ne, hpw_sub, hsub_hd, _, _⟩ := takeThrough_props hpw_ls hb_ls
      obtain ⟨_, _, hls_hd, hsp_t_bst, _⟩ := (minKey_bst_props ht_bst).2 s' hmin_s'
      have hsub0 : sub[0]? = some s' := by
        rw [← List.head?_eq_getElem?, hsub_hd]; exact hls_hd
      have hsub_len : sub.length = k + 1 := by
        have := List.length_pos_of_ne_nil hsub_ne; omega
      have h2h_le : 2 * h ≤ sub.tail.length := by
        simp only [List.length_tail, hsub_len]; omega
      have hpairs_len : pairs.length = h := by
        dsimp only [pairs]
        rw [List.length_take]
        have := adjacentPairs_length_ge sub.tail h h2h_le
        omega
      have hpairs_get : ∀ (idx : ℕ) (hidx : idx < h),
          pairs[idx]'(hpairs_len ▸ hidx) =
            (sub[2 * (idx + 1) - 1]'(by omega), sub[2 * (idx + 1)]'(by omega)) := by
        intro idx hidx
        have hget? : pairs[idx]? = some (pairs[idx]'(hpairs_len ▸ hidx)) :=
          List.getElem?_eq_getElem _
        dsimp only [pairs] at hget?
        rw [List.getElem?_take_of_lt hidx,
            adjacentPairs_getElem? sub.tail idx (by simp [List.length_tail, hsub_len]; omega)] at hget?
        injection hget? with hp_eq
        rw [← hp_eq]
        simp [List.getElem_tail, show 2 * (idx + 1) = 2 * idx + 1 + 1 by omega]
      -- Prove by induction on `m ≤ h` that folding `pairs.take m` commutes with `fillCartesianSlots`
      -- and satisfies `PhaseBlockStepRel`!
      suffices ∀ m ≤ h,
          let tm := (pairs.take m).foldl (fun acc p => rotateRightEdge acc p.1 p.2)
            (spliceMin (proc.treeAt τ))
          let extm := fillCartesianSlots proc.insStep U_τ none none tm
          tm.IsBST ∧ extm.IsBST ∧
          (∀ idx (hidx : idx < h), m ≤ idx →
            IsRightRotEdge tm (sub[2 * (idx + 1) - 1]'(by omega)) (sub[2 * (idx + 1)]'(by omega))) ∧
          PhaseBlockStepRel S_hi {e : InternalPopRot | e ∈ proc.rInt ∧ e.stepIdx = τ}
            (restrictTree (cartesianExt proc τ) S_hi) (restrictTree extm S_hi) by
        obtain ⟨_, _, _, hrel_h⟩ := this h le_rfl
        have htake_h : pairs.take h = pairs := List.take_of_length_le (by omega)
        rw [htake_h, ← ht1_eq] at hrel_h
        have hext1 : cartesianExt proc (τ + 1) =
            fillCartesianSlots proc.insStep U_τ none none (proc.treeAt (τ + 1)) := by
          unfold cartesianExt
          change fillCartesianSlots proc.insStep
              (Finset.Icc (((proc.steps.take (τ + 1)).filter isPop).length + 1) P \
                keyFinset (proc.treeAt (τ + 1))) none none (proc.treeAt (τ + 1)) = _
          rw [hU_next]
        rw [hext1]
        exact hrel_h
      intro m
      induction m with
      | zero =>
        intro _
        simp only [List.take_zero, List.foldl_nil]
        have hext0_eq : fillCartesianSlots proc.insStep U_τ none none (spliceMin (proc.treeAt τ)) =
            spliceMin (cartesianExt proc τ) := hsp_comm
        have hext0_bst : (spliceMin (cartesianExt proc τ)).IsBST :=
          ((minKey_bst_props hext_bst).2 s' hext_min).2.2.2.1
        refine ⟨hsp_t_bst, hext0_eq ▸ hext0_bst, ?_, ?_⟩
        · intro idx hidx _
          have hx_lt_len : 2 * (idx + 1) - 1 < sub.length := by omega
          have hy_lt_len : 2 * (idx + 1) < sub.length := by omega
          rcases hsub_pref with ⟨ls_tl, hls_eq⟩
          have hls_x : ls[2 * (idx + 1) - 1]? = some (sub[2 * (idx + 1) - 1]'hx_lt_len) := by
            rw [← hls_eq, List.getElem?_append_left hx_lt_len, List.getElem?_eq_getElem hx_lt_len]
          have hls_y : ls[2 * (idx + 1)]? = some (sub[2 * (idx + 1)]'hy_lt_len) := by
            have hadd : 2 * (idx + 1) = (2 * (idx + 1) - 1) + 1 := by omega
            rw [← hls_eq, List.getElem?_append_left hy_lt_len, List.getElem?_eq_getElem hy_lt_len]
          have hadd : 2 * (idx + 1) = (2 * (idx + 1) - 1) + 1 := by omega
          have hedge_orig : IsRightRotEdge (proc.treeAt τ)
              (sub[2 * (idx + 1) - 1]'hx_lt_len) (sub[2 * (idx + 1)]'hy_lt_len) :=
            isRightRotEdge_of_adj_leftSpine (proc.treeAt τ) ht_bst hls_x (hadd ▸ hls_y)
          have hs'_lt_x : s' < sub[2 * (idx + 1) - 1]'hx_lt_len := by
            obtain ⟨h0_lt, hs0_eq⟩ := List.getElem?_eq_some_iff.mp hsub0
            rw [← hs0_eq]
            exact List.pairwise_iff_getElem.mp hpw_sub 0 (2 * (idx + 1) - 1) h0_lt hx_lt_len (by omega)
          have hx_lt_y : sub[2 * (idx + 1) - 1]'hx_lt_len < sub[2 * (idx + 1)]'hy_lt_len :=
            List.pairwise_iff_getElem.mp hpw_sub _ _ hx_lt_len hy_lt_len (by omega)
          exact isRightRotEdge_spliceMin_above (proc.treeAt τ) ht_bst hmin_s' hs'_lt_x hx_lt_y hedge_orig
        · rw [hext0_eq, hsp_restrict]
          exact .refl _
      | succ m ihm =>
        intro hm_le
        have hm_lt : m < h := Nat.lt_of_succ_le hm_le
        obtain ⟨htm_bst, hextm_bst, hedge_m, hrel_m⟩ := ihm (le_of_lt hm_lt)
        set tm := (pairs.take m).foldl (fun acc p => rotateRightEdge acc p.1 p.2)
          (spliceMin (proc.treeAt τ))
        set extm := fillCartesianSlots proc.insStep U_τ none none tm
        have htake_m1 : pairs.take (m + 1) = pairs.take m ++ [pairs[m]'(hpairs_len ▸ hm_lt)] :=
          List.take_succ_eq_append_getElem (hpairs_len ▸ hm_lt)
        have hpm := hpairs_get m hm_lt
        have hx_lt_len : 2 * (m + 1) - 1 < sub.length := by omega
        have hy_lt_len : 2 * (m + 1) < sub.length := by omega
        have hz_lt_len : 2 * (m + 1) + 1 < sub.length := by omega
        set xm := sub[2 * (m + 1) - 1]'hx_lt_len
        set ym := sub[2 * (m + 1)]'hy_lt_len
        set zm := sub[2 * (m + 1) + 1]'hz_lt_len
        have hxy_m : xm < ym := List.pairwise_iff_getElem.mp hpw_sub _ _ hx_lt_len hy_lt_len (by omega)
        have hedge_cur : IsRightRotEdge tm xm ym := hedge_m m hm_lt le_rfl
        have htm1_eq : (pairs.take (m + 1)).foldl (fun acc p => rotateRightEdge acc p.1 p.2)
            (spliceMin (proc.treeAt τ)) = rotateRightEdge tm xm ym := by
          rw [htake_m1, List.foldl_append, List.foldl_cons, List.foldl_nil, hpm]
        obtain ⟨hedge_extm, hrot_extm⟩ :=
          fillCartesianSlots_rotateRightEdge proc.insStep U_τ none none tm hedge_cur
        dsimp only
        rw [htm1_eq, hrot_extm]
        refine ⟨rotateRightEdge_isBST htm_bst xm ym, rotateRightEdge_isBST hextm_bst xm ym, ?_, ?_⟩
        · intro idx hidx hsucc_le
          have hprev := hedge_m idx hidx (le_of_lt hsucc_le)
          have hidx_x_lt : 2 * (idx + 1) - 1 < sub.length := by omega
          have hidx_y_lt : 2 * (idx + 1) < sub.length := by omega
          have hvm_lt_x : ym < sub[2 * (idx + 1) - 1]'hidx_x_lt :=
            List.pairwise_iff_getElem.mp hpw_sub _ _ hy_lt_len hidx_x_lt (by omega)
          have hx_lt_y : sub[2 * (idx + 1) - 1]'hidx_x_lt < sub[2 * (idx + 1)]'hidx_y_lt :=
            List.pairwise_iff_getElem.mp hpw_sub _ _ hidx_x_lt hidx_y_lt (by omega)
          exact isRightRotEdge_rotateRightEdge_above tm hxy_m hvm_lt_x hx_lt_y hprev
        · -- Construct `em ∈ proc.rInt` with `em.stepIdx = τ`!
          let em : InternalPopRot :=
            { stepIdx := τ, s := s', j := m + 1, h := h, x := xm, y := ym, z := zm }
          have hem_rInt : em ∈ proc.rInt := by
            rw [mem_rInt_iff]
            exact ⟨hτ, b, hop, hb_eq, rfl, Nat.succ_pos m, hm_le,
              List.getElem?_eq_getElem hx_lt_len,
              List.getElem?_eq_getElem hy_lt_len,
              List.getElem?_eq_getElem hz_lt_len⟩
          obtain ⟨hres_extm, h31_rot, _⟩ :=
            h_3_1 extm S_hi hextm_bst (isLCAClosed_gt_le _ Sp.hi X.hi)
          obtain ⟨hiff_s, hrot_s⟩ := isSingle_iff_right (t := extm) hxy_m
          have h31_xy := h31_rot xm ym (hiff_s.mpr hedge_extm)
            (hrot_s.symm ▸ isLCAClosed_gt_le _ Sp.hi X.hi)
          rw [← hrot_s]
          by_cases hxy_S : xm ∈ S_hi ∧ ym ∈ S_hi
          · obtain ⟨hedge_res, hres_eq⟩ := h31_xy.1 hxy_S
            obtain ⟨hiff_res, hrot_res⟩ :=
              isSingle_iff_right (t := restrictTree extm S_hi) hxy_m
            rw [hres_eq, hrot_res]
            exact .step em hrel_m ⟨hem_rInt, rfl⟩ hxy_m hxy_S.1 hxy_S.2
              hres_extm.1 (hiff_res.mp hedge_res)
          · rw [h31_xy.2 hxy_S]
            exact hrel_m

/-! ## Section 4B: `phaseSummaryBST` Eviction, Left-Spine Correspondence, and `upperSpineSet` -/

private theorem mem_leftSpine_rotateRightEdge_iff_of_ne {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) {w : α} (hne : w ≠ p) :
    w ∈ leftSpine (rotateRightEdge t x p) ↔ w ∈ leftSpine t := by
  refine ⟨fun hw => (leftSpine_rotateRightEdge_sublist t x p).subset hw, ?_⟩
  induction t with
  | nil => exact id
  | node k l r ihl _ =>
    intro hw
    unfold rotateRightEdge
    split_ifs with hp1 hp2
    · simp only [leftSpine, List.mem_append, List.mem_singleton] at hw ⊢
      exact hw.imp_left ihl
    · exact hw
    · have hpk : k = p := le_antisymm (not_lt.mp hp1) (not_lt.mp hp2)
      subst k
      cases l with
      | nil => exact hw
      | node lx a b =>
        dsimp only
        split_ifs with hlx
        · simp only [leftSpine, List.mem_append, List.mem_singleton] at hw ⊢
          rcases hw with h_in_l | rfl
          · exact h_in_l
          · exact absurd rfl hne
        · exact hw

private theorem leftSpine_map {α β : Type} :
    ∀ (t : BinaryTree α) (f : α → β), leftSpine (t.map f) = (leftSpine t).map f
  | .nil, _ => rfl
  | .node k l r, f => by
    change leftSpine (.node (f k) (l.map f) (r.map f)) = (leftSpine (.node k l r)).map f
    simp only [leftSpine, List.map_append, List.map_singleton, leftSpine_map l f]

private theorem mem_of_mem_restrictTree {α : Type} :
    ∀ (t : BinaryTree α) (S : Set α) {w : α}, w ∈ restrictTree t S → w ∈ t ∧ w ∈ S
  | .nil, _, _, hw => by cases hw
  | .node u A B, S, w, hw => by
    unfold restrictTree at hw
    split_ifs at hw with huS hex
    · rcases BinaryTree.mem_node_iff.mp hw with rfl | hA | hB
      · exact ⟨.here, huS⟩
      · obtain ⟨h1, h2⟩ := mem_of_mem_restrictTree A S hA
        exact ⟨.left h1, h2⟩
      · obtain ⟨h1, h2⟩ := mem_of_mem_restrictTree B S hB
        exact ⟨.right h1, h2⟩
    · obtain ⟨h1, h2⟩ := mem_of_mem_restrictTree B S hw
      exact ⟨.right h1, h2⟩
    · obtain ⟨h1, h2⟩ := mem_of_mem_restrictTree A S hw
      exact ⟨.left h1, h2⟩

private theorem restrictTree_congr_mem {α : Type} :
    ∀ (t : BinaryTree α) (S₁ S₂ : Set α),
      (∀ x ∈ t, x ∈ S₁ ↔ x ∈ S₂) → restrictTree t S₁ = restrictTree t S₂
  | .nil, _, _, _ => rfl
  | .node u A B, S₁, S₂, hiff => by
    have hu : u ∈ S₁ ↔ u ∈ S₂ := hiff u .here
    have hex : (∃ b ∈ B, b ∈ S₁) ↔ (∃ b ∈ B, b ∈ S₂) :=
      ⟨fun ⟨b, hb, hbS⟩ => ⟨b, hb, (hiff b (.right hb)).mp hbS⟩,
       fun ⟨b, hb, hbS⟩ => ⟨b, hb, (hiff b (.right hb)).mpr hbS⟩⟩
    have hA := restrictTree_congr_mem A S₁ S₂ (fun a ha => hiff a (.left ha))
    have hB := restrictTree_congr_mem B S₁ S₂ (fun b hb => hiff b (.right hb))
    unfold restrictTree
    by_cases hu1 : u ∈ S₁
    · have hu2 : u ∈ S₂ := hu.mp hu1
      simp only [hu1, hu2, ↓reduceIte, hA, hB]
    · have hu2 : u ∉ S₂ := mt hu.mpr hu1
      simp only [hu1, hu2, ↓reduceIte]
      by_cases hex1 : ∃ b ∈ B, b ∈ S₁
      · have hex2 : ∃ b ∈ B, b ∈ S₂ := hex.mp hex1
        simp only [hex1, hex2, ↓reduceIte, hB]
      · have hex2 : ¬ ∃ b ∈ B, b ∈ S₂ := mt hex.mpr hex1
        simp only [hex1, hex2, ↓reduceIte, hA]

private theorem subtreeAtKey_bst_node {t : BinaryTree ℕ} (ht : t.IsBST) :
    ∀ {r : ℕ}, r ∈ t → ∃ L R, subtreeAtKey t r = .node r L R ∧ (BinaryTree.node r L R).IsBST := by
  induction t with
  | nil => intro _ h; cases h
  | node k l r_sub ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r_sub).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    intro r hmem
    rcases BinaryTree.mem_node_iff.mp hmem with rfl | hL | hR
    · exact ⟨l, r_sub, by simp [subtreeAtKey], ht⟩
    · have hrk : r < k := hlt' r hL
      unfold subtreeAtKey
      simp only [hrk, ↓reduceIte]
      exact ihl hl hL
    · have hkr : k < r := hgt' r hR
      have hnrk : ¬ r < k := by omega
      unfold subtreeAtKey
      simp only [hnrk, hkr, ↓reduceIte]
      exact ihr hr hR

private theorem subtreeAtKey_of_mem_subtreeAtKey {t : BinaryTree ℕ} (ht : t.IsBST) :
    ∀ {r z : ℕ}, z ∈ subtreeAtKey t r → subtreeAtKey t z = subtreeAtKey (subtreeAtKey t r) z := by
  induction t with
  | nil => intro _ _ hz; simp [subtreeAtKey] at hz
  | node k l r_sub ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r_sub).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    intro r z hz
    unfold subtreeAtKey at hz
    split_ifs at hz with hrk hkr
    · have hzk : z < k := hlt' z (mem_of_mem_subtreeAtKey hz)
      have h1 : subtreeAtKey (.node k l r_sub) z = subtreeAtKey l z := by simp [subtreeAtKey, hzk]
      have h2 : subtreeAtKey (.node k l r_sub) r = subtreeAtKey l r := by simp [subtreeAtKey, hrk]
      rw [h1, h2]
      exact ihl hl hz
    · have hkz : k < z := hgt' z (mem_of_mem_subtreeAtKey hz)
      have hnzk : ¬ z < k := by omega
      have h1 : subtreeAtKey (.node k l r_sub) z = subtreeAtKey r_sub z := by
        simp [subtreeAtKey, hnzk, hkz]
      have h2 : subtreeAtKey (.node k l r_sub) r = subtreeAtKey r_sub r := by
        simp [subtreeAtKey, hrk, hkr]
      rw [h1, h2]
      exact ihr hr hz
    · have h2 : subtreeAtKey (.node k l r_sub) r = .node k l r_sub := by
        simp [subtreeAtKey, hrk, hkr]
      rw [h2]

private theorem subtreeAtKey_antisymm {t : BinaryTree ℕ} (ht : t.IsBST) :
    ∀ {r₁ r₂ : ℕ}, r₂ ∈ subtreeAtKey t r₁ → r₁ ∈ subtreeAtKey t r₂ → r₁ = r₂ := by
  induction t with
  | nil => intro _ _ h; simp [subtreeAtKey] at h
  | node k l r_sub ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r_sub).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    intro r₁ r₂ h12 h21
    by_cases h1k : r₁ < k
    · unfold subtreeAtKey at h12
      simp only [h1k, ↓reduceIte] at h12
      have h2k : r₂ < k := hlt' r₂ (mem_of_mem_subtreeAtKey h12)
      unfold subtreeAtKey at h21
      simp only [h2k, ↓reduceIte] at h21
      exact ihl hl h12 h21
    · by_cases hk1 : k < r₁
      · unfold subtreeAtKey at h12
        simp only [h1k, hk1, ↓reduceIte] at h12
        have hk2 : k < r₂ := hgt' r₂ (mem_of_mem_subtreeAtKey h12)
        have hn2k : ¬ r₂ < k := by omega
        unfold subtreeAtKey at h21
        simp only [hn2k, hk2, ↓reduceIte] at h21
        exact ihr hr h12 h21
      · have hr1 : r₁ = k := by omega
        subst hr1
        by_cases h2k : r₁ < r₂
        · have hn21 : ¬ r₂ < r₁ := by omega
          unfold subtreeAtKey at h21
          simp only [hn21, h2k, ↓reduceIte] at h21
          exact absurd (hgt' r₁ (mem_of_mem_subtreeAtKey h21)) (lt_irrefl _)
        · by_cases hlt21 : r₂ < r₁
          · unfold subtreeAtKey at h21
            simp only [hlt21, ↓reduceIte] at h21
            exact absurd (hlt' r₁ (mem_of_mem_subtreeAtKey h21)) (lt_irrefl _)
          · omega

private theorem mem_leftSpine_of_leftSpine_in_subtree {t : BinaryTree ℕ} (ht : t.IsBST) :
    ∀ {x r : ℕ}, x ∈ leftSpine t → r ∈ t → x ∈ subtreeAtKey t r → r ∈ leftSpine t ∧ x ≤ r := by
  induction t with
  | nil => intro _ _ hx; simp [leftSpine] at hx
  | node k l r_sub ihl _ =>
    obtain ⟨hlt, hgt, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r_sub).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    intro x r hx_ls hr_mem hx_sub
    have hx_le_k : x ≤ k := by
      simp only [leftSpine, List.mem_append, List.mem_singleton] at hx_ls
      rcases hx_ls with hxl | rfl
      · exact le_of_lt (hlt' x (mem_of_mem_leftSpine hxl))
      · exact le_rfl
    rcases BinaryTree.mem_node_iff.mp hr_mem with rfl | hrL | hrR
    · exact ⟨by simp [leftSpine], hx_le_k⟩
    · have hrk : r < k := hlt' r hrL
      unfold subtreeAtKey at hx_sub
      simp only [hrk, ↓reduceIte] at hx_sub
      have hxk : x < k := hlt' x (mem_of_mem_subtreeAtKey hx_sub)
      have hx_ls_l : x ∈ leftSpine l := by
        simp only [leftSpine, List.mem_append, List.mem_singleton] at hx_ls
        rcases hx_ls with hxl | rfl
        · exact hxl
        · omega
      obtain ⟨hr_ls_l, hxr⟩ := ihl hl hx_ls_l hrL hx_sub
      exact ⟨by simp [leftSpine, hr_ls_l], hxr⟩
    · have hkr : k < r := hgt' r hrR
      have hnrk : ¬ r < k := by omega
      unfold subtreeAtKey at hx_sub
      simp only [hnrk, hkr, ↓reduceIte] at hx_sub
      have hkx : k < x := hgt' x (mem_of_mem_subtreeAtKey hx_sub)
      omega

private theorem lcaBST_mem_and_subtree {t : BinaryTree ℕ} (ht : t.IsBST) :
    ∀ {x y z : ℕ}, x ∈ t → y ∈ t → lcaBST t x y = some z →
      z ∈ t ∧ x ∈ subtreeAtKey t z ∧ y ∈ subtreeAtKey t z := by
  induction t with
  | nil => intro _ _ _ hx; cases hx
  | node k l r_sub ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r_sub).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    intro x y z hx hy hlca
    unfold lcaBST at hlca
    split_ifs at hlca with hboth_lt hboth_gt
    · have hx_l : x ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hx with rfl | hL | hR
        · omega
        · exact hL
        · have := hgt' x hR; omega
      have hy_l : y ∈ l := by
        rcases BinaryTree.mem_node_iff.mp hy with rfl | hL | hR
        · omega
        · exact hL
        · have := hgt' y hR; omega
      obtain ⟨hz_l, hxz, hyz⟩ := ihl hl hx_l hy_l hlca
      have hzk : z < k := hlt' z hz_l
      exact ⟨.left hz_l, by simp [subtreeAtKey, hzk, hxz], by simp [subtreeAtKey, hzk, hyz]⟩
    · have hx_r : x ∈ r_sub := by
        rcases BinaryTree.mem_node_iff.mp hx with rfl | hL | hR
        · omega
        · have := hlt' x hL; omega
        · exact hR
      have hy_r : y ∈ r_sub := by
        rcases BinaryTree.mem_node_iff.mp hy with rfl | hL | hR
        · omega
        · have := hlt' y hL; omega
        · exact hR
      obtain ⟨hz_r, hxz, hyz⟩ := ihr hr hx_r hy_r hlca
      have hkz : k < z := hgt' z hz_r
      have hnzk : ¬ z < k := by omega
      exact ⟨.right hz_r, by simp [subtreeAtKey, hnzk, hkz, hxz],
        by simp [subtreeAtKey, hnzk, hkz, hyz]⟩
    · injection hlca with hkz
      subst z
      exact ⟨.here, by simp [subtreeAtKey, hx], by simp [subtreeAtKey, hy]⟩

private theorem restrictTree_interval_root_props {B : BinaryTree ℕ} (hB : B.IsBST)
    {I : IntervalBlock} {w₀ : ℕ} (hw₀_B : w₀ ∈ B) (hw₀_I : w₀ ∈ I.toSet) :
    ∃ r : ℕ, rootKey? (restrictTree B I.toSet) = some r ∧
      r ∈ B ∧ r ∈ I.toSet ∧ ∀ w ∈ B, w ∈ I.toSet → w ∈ subtreeAtKey B r := by
  induction B with
  | nil => cases hw₀_B
  | node u A C ihA ihC =>
    obtain ⟨hlt, hgt, hA, hC⟩ := (SplayDeque.Direct.isBSTNode_iff u A C).mp hB
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    by_cases huI : u ∈ I.toSet
    · refine ⟨u, ?_, .here, huI, fun w hw _ => by simpa [subtreeAtKey] using hw⟩
      unfold restrictTree
      simp [huI, rootKey?]
    · change ¬ (I.lo ≤ u ∧ u ≤ I.hi) at huI
      change I.lo ≤ w₀ ∧ w₀ ≤ I.hi at hw₀_I
      rcases (show u < I.lo ∨ I.hi < u by omega) with hu_lt | hu_gt
      · have hw₀_C : w₀ ∈ C := by
          rcases BinaryTree.mem_node_iff.mp hw₀_B with rfl | hL | hR
          · omega
          · have := hlt' w₀ hL; omega
          · exact hR
        have hexC : ∃ b ∈ C, b ∈ I.toSet := ⟨w₀, hw₀_C, hw₀_I⟩
        obtain ⟨r, hr_root, hr_C, hr_I, hr_all⟩ := ihC hC hw₀_C
        have hur : u < r := hgt' r hr_C
        have hnr : ¬ r < u := by omega
        refine ⟨r, ?_, .right hr_C, hr_I, ?_⟩
        · unfold restrictTree
          have huI' : u ∉ I.toSet := huI
          simp only [huI', hexC, ↓reduceIte, hr_root]
        · intro w hw hwI
          change I.lo ≤ w ∧ w ≤ I.hi at hwI
          have hw_C : w ∈ C := by
            rcases BinaryTree.mem_node_iff.mp hw with rfl | hL | hR
            · omega
            · have := hlt' w hL; omega
            · exact hR
          unfold subtreeAtKey
          simp only [hnr, hur, ↓reduceIte]
          exact hr_all w hw_C hwI
      · have hw₀_A : w₀ ∈ A := by
          rcases BinaryTree.mem_node_iff.mp hw₀_B with rfl | hL | hR
          · omega
          · exact hL
          · have := hgt' w₀ hR; omega
        have hnoC : ¬ ∃ b ∈ C, b ∈ I.toSet := by
          rintro ⟨b, hbC, hbI⟩
          change I.lo ≤ b ∧ b ≤ I.hi at hbI
          have := hgt' b hbC; omega
        obtain ⟨r, hr_root, hr_A, hr_I, hr_all⟩ := ihA hA hw₀_A
        have hru : r < u := hlt' r hr_A
        refine ⟨r, ?_, .left hr_A, hr_I, ?_⟩
        · unfold restrictTree
          have huI' : u ∉ I.toSet := huI
          simp only [huI', hnoC, ↓reduceIte, hr_root]
        · intro w hw hwI
          change I.lo ≤ w ∧ w ≤ I.hi at hwI
          have hw_A : w ∈ A := by
            rcases BinaryTree.mem_node_iff.mp hw with rfl | hL | hR
            · omega
            · exact hL
            · have := hgt' w hR; omega
          unfold subtreeAtKey
          simp only [hru, ↓reduceIte]
          exact hr_all w hw_A hwI

private theorem preorderRank_eq_one_iff_rootKey (t : BinaryTree ℕ) (w : ℕ) :
    (1 ≤ preorderRank t w ∧ preorderRank t w ≤ 1) ↔ rootKey? t = some w := by
  cases t with
  | nil => simp [preorderRank, bstPreorderList, listRank1, rootKey?]
  | node r L R =>
    unfold preorderRank bstPreorderList listRank1 rootKey?
    by_cases hwr : w = r
    · subst hwr; simp
    · have hrw : ¬ r = w := fun h => hwr h.symm
      simp only [hwr, ↓reduceIte, Option.some.injEq, hrw, iff_false]
      set rk := listRank1 (bstPreorderList L ++ bstPreorderList R) w
      by_cases hrk0 : rk = 0
      · simp [hrk0]
      · simp [hrk0]

private noncomputable def blockRoot (subs : List IntervalBlock) (B : BinaryTree ℕ) (c : ℕ) : ℕ :=
  (rootKey? (restrictTree B (subblock1 subs c).toSet)).getD 0

private theorem summary1_roots_and_lcaClosed {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1
      ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1))
    {B : BinaryTree ℕ} (hB_bst : B.IsBST)
    (hB_keys : keyFinset B = Finset.Icc
      ((subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).hi + 1) X.hi) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    let K_X := subs.length
    let Gset := preorderSummarySet B (subs.drop p) 1
    (∀ c ∈ Finset.Icc (p + 1) K_X,
      let rc := blockRoot subs B c
      rootKey? (restrictTree B (subblock1 subs c).toSet) = some rc ∧
      rc ∈ B ∧
      rc ∈ (subblock1 subs c).toFinset ∧
      subblockIndex1 subs rc = c ∧
      (∀ w ∈ B, w ∈ (subblock1 subs c).toFinset → w ∈ subtreeAtKey B rc) ∧
      (∀ r' ∈ B, r' ∈ (subblock1 subs c).toFinset →
        (∀ w ∈ B, w ∈ (subblock1 subs c).toFinset → w ∈ subtreeAtKey B r') → r' = rc)) ∧
    (∀ w, w ∈ Gset ↔ ∃ c ∈ Finset.Icc (p + 1) K_X, w = blockRoot subs B c) ∧
    IsLCAClosed B (Gset : Set ℕ) := by
  dsimp only
  obtain ⟨_, _, _, _, hsub_c, hsub_lt, _, _, hsub_cover⟩ := subblock1_props hValid ℓ X hX
  set chain := scaleTreePartitionChain T P M
  set subs := childSubblocks (chain ℓ.succ) X
  set K_X := subs.length
  set Sp := subblock1 subs p
  set Gset := preorderSummarySet B (subs.drop p) 1
  obtain ⟨hp1, hp_sub1⟩ := Finset.mem_Icc.mp hp
  have hp_lt_K : p < K_X := by omega
  have mem_toSet_iff : ∀ (C : IntervalBlock) (w : ℕ), w ∈ C.toSet ↔ w ∈ C.toFinset := by
    intro C w; simp [IntervalBlock.toSet, IntervalBlock.toFinset]
  have hroots : ∀ c ∈ Finset.Icc (p + 1) K_X,
      let rc := blockRoot subs B c
      rootKey? (restrictTree B (subblock1 subs c).toSet) = some rc ∧
      rc ∈ B ∧
      rc ∈ (subblock1 subs c).toFinset ∧
      subblockIndex1 subs rc = c ∧
      (∀ w ∈ B, w ∈ (subblock1 subs c).toFinset → w ∈ subtreeAtKey B rc) ∧
      (∀ r' ∈ B, r' ∈ (subblock1 subs c).toFinset →
        (∀ w ∈ B, w ∈ (subblock1 subs c).toFinset → w ∈ subtreeAtKey B r') → r' = rc) := by
    intro c hc
    obtain ⟨hcp1, hcK⟩ := Finset.mem_Icc.mp hc
    have hc_Icc1 : c ∈ Finset.Icc 1 K_X := Finset.mem_Icc.mpr ⟨by omega, hcK⟩
    obtain ⟨_, _, hSc_Xlo, hSc_lohi, hSc_Xhi, hSc_w⟩ := hsub_c c hc_Icc1
    have hSp_lt_Sc : Sp.hi < (subblock1 subs c).lo := hsub_lt p c hp1 (by omega) hcK
    have hlo_B : (subblock1 subs c).lo ∈ B := by
      rw [mem_iff_mem_keyFinset, hB_keys, Finset.mem_Icc]
      omega
    have hlo_Set : (subblock1 subs c).lo ∈ (subblock1 subs c).toSet := ⟨le_rfl, hSc_lohi⟩
    obtain ⟨r₀, hr₀_some, hr₀_B, hr₀_Set, hr₀_sub⟩ :=
      restrictTree_interval_root_props hB_bst hlo_B hlo_Set
    have hrc_eq : blockRoot subs B c = r₀ := by simp [blockRoot, hr₀_some]
    rw [hrc_eq]
    have hr₀_Fin : r₀ ∈ (subblock1 subs c).toFinset := (mem_toSet_iff _ _).mp hr₀_Set
    refine ⟨hr₀_some, hr₀_B, hr₀_Fin, (hSc_w r₀ hr₀_Fin).1,
      fun w hwB hwF => hr₀_sub w hwB ((mem_toSet_iff _ _).mpr hwF), ?_⟩
    intro r' hr'_B hr'_F hr'_all
    exact subtreeAtKey_antisymm hB_bst
      (hr'_all r₀ hr₀_B hr₀_Fin) (hr₀_sub r' hr'_B ((mem_toSet_iff _ _).mpr hr'_F))
  have mem_drop_iff : ∀ C, C ∈ subs.drop p ↔ ∃ c ∈ Finset.Icc (p + 1) K_X, C = subblock1 subs c := by
    intro C
    constructor
    · intro hC
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
      rw [List.length_drop] at hi
      refine ⟨p + 1 + i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      unfold subblock1
      have hsub_idx : p + 1 + i - 1 = p + i := by omega
      simp [hsub_idx, List.getElem_drop, List.getElem?_eq_getElem (show p + i < subs.length by omega)]
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨hcp1, hcK⟩ := Finset.mem_Icc.mp hc
      unfold subblock1
      have hnz : ¬ (c = 0) := by omega
      simp only [hnz, ↓reduceIte, List.getElem?_eq_getElem (show c - 1 < subs.length by omega),
        Option.getD_some]
      have hdrop_get : (subs.drop p)[c - 1 - p]'(by rw [List.length_drop]; omega) =
          subs[c - 1]'(by omega) := by
        rw [List.getElem_drop]
        congr 1; omega
      rw [← hdrop_get]
      exact List.getElem_mem _
  have foldr_union_iff : ∀ (xs : List IntervalBlock) (f : IntervalBlock → Finset ℕ) (w : ℕ),
      w ∈ xs.foldr (fun C acc => f C ∪ acc) ∅ ↔ ∃ C ∈ xs, w ∈ f C := by
    intro xs f w
    induction xs with
    | nil => simp
    | cons head tail iht =>
      simp only [List.foldr_cons, Finset.mem_union, iht, List.mem_cons, exists_eq_or_imp]
  have hGset_iff : ∀ w, w ∈ Gset ↔ ∃ c ∈ Finset.Icc (p + 1) K_X, w = blockRoot subs B c := by
    intro w
    dsimp only [Gset]
    unfold preorderSummarySet
    rw [foldr_union_iff]
    constructor
    · rintro ⟨C, hC_drop, hw_filt⟩
      obtain ⟨c, hc_Icc, rfl⟩ := (mem_drop_iff C).mp hC_drop
      obtain ⟨_, hw_rk⟩ := Finset.mem_filter.mp hw_filt
      rw [preorderRank_eq_one_iff_rootKey, (hroots c hc_Icc).1] at hw_rk
      injection hw_rk with hw_eq
      exact ⟨c, hc_Icc, hw_eq.symm⟩
    · rintro ⟨c, hc_Icc, rfl⟩
      obtain ⟨hroot_c, _, hrc_Fin, _, _, _⟩ := hroots c hc_Icc
      refine ⟨subblock1 subs c, (mem_drop_iff _).mpr ⟨c, hc_Icc, rfl⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hrc_Fin, (preorderRank_eq_one_iff_rootKey _ _).mpr hroot_c⟩
  refine ⟨hroots, hGset_iff, ?_⟩
  -- Prove `IsLCAClosed B Gset`
  intro x hx_B y hy_B hx_G hy_G z hlca
  change z ∈ Gset
  change x ∈ Gset at hx_G
  change y ∈ Gset at hy_G
  obtain ⟨cx, hcx_Icc, rfl⟩ := (hGset_iff x).mp hx_G
  obtain ⟨cy, hcy_Icc, rfl⟩ := (hGset_iff y).mp hy_G
  obtain ⟨hz_B, hx_sub_z, hy_sub_z⟩ := lcaBST_mem_and_subtree hB_bst hx_B hy_B hlca
  have hbet := lcaBST_between B _ _ z hlca
  have hz_Icc_B : z ∈ Finset.Icc (Sp.hi + 1) X.hi :=
    hB_keys ▸ (mem_iff_mem_keyFinset B z).mp hz_B
  have hSp_Xlo : X.lo ≤ Sp.lo ∧ Sp.lo ≤ Sp.hi := by
    have := hsub_c p (Finset.mem_Icc.mpr ⟨hp1, le_of_lt hp_lt_K⟩)
    exact ⟨this.2.2.1, this.2.2.2.1⟩
  have hz_in_X : z ∈ Finset.Icc X.lo X.hi :=
    Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hz_Icc_B).1; omega,
      (Finset.mem_Icc.mp hz_Icc_B).2⟩
  obtain ⟨hcz_1K, hz_Scz⟩ := hsub_cover z hz_in_X
  set cz := subblockIndex1 subs z
  have hcz_Icc : cz ∈ Finset.Icc (p + 1) K_X := by
    refine Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp hcz_1K).2⟩
    by_contra hle_p
    have hcz_le_p : cz ≤ p := by omega
    have hz_le_Sphi : z ≤ Sp.hi := by
      change z ≤ (subblock1 subs p).hi
      rcases eq_or_lt_of_le hcz_le_p with rfl | hlt
      · exact (Finset.mem_Icc.mp hz_Scz).2
      · have := hsub_lt cz p (Finset.mem_Icc.mp hcz_1K).1 hlt (le_of_lt hp_lt_K)
        have := (hsub_c p (Finset.mem_Icc.mpr ⟨hp1, le_of_lt hp_lt_K⟩)).2.2.2.1
        have := (Finset.mem_Icc.mp hz_Scz).2
        omega
    have := (Finset.mem_Icc.mp hz_Icc_B).1
    omega
  obtain ⟨_, hrz_B, hrz_Fin, _, hrz_all, _⟩ := hroots cz hcz_Icc
  set rz := blockRoot subs B cz
  have hz_sub_rz : z ∈ subtreeAtKey B rz := hrz_all z hz_B hz_Scz
  suffices z = rz by
    rw [hGset_iff]
    exact ⟨cz, hcz_Icc, this⟩
  by_contra hne_z
  obtain ⟨L_r, R_r, hsub_rz, hbst_rz⟩ := subtreeAtKey_bst_node hB_bst hrz_B
  obtain ⟨hlt_rz, hgt_rz, _, _⟩ := (SplayDeque.Direct.isBSTNode_iff rz L_r R_r).mp hbst_rz
  have hlt_rz' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt_rz
  have hgt_rz' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt_rz
  have hsub_z_eq := subtreeAtKey_of_mem_subtreeAtKey hB_bst hz_sub_rz
  rw [hsub_rz] at hz_sub_rz hsub_z_eq
  rcases BinaryTree.mem_node_iff.mp hz_sub_rz with h_eq | hz_L | hz_R
  · exact hne_z h_eq
  · have hzl : z < rz := hlt_rz' z hz_L
    have hsub_z_L : subtreeAtKey B z = subtreeAtKey L_r z := by
      rw [hsub_z_eq]; simp [subtreeAtKey, hzl]
    rw [hsub_z_L] at hx_sub_z hy_sub_z
    have hx_lt_rz : blockRoot subs B cx < rz := hlt_rz' _ (mem_of_mem_subtreeAtKey hx_sub_z)
    have hy_lt_rz : blockRoot subs B cy < rz := hlt_rz' _ (mem_of_mem_subtreeAtKey hy_sub_z)
    rcases hbet with ⟨_, hzy⟩ | ⟨_, hzx⟩
    · have hy_Scz : blockRoot subs B cy ∈ (subblock1 subs cz).toFinset :=
        Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hz_Scz).1 hzy,
          le_trans (le_of_lt hy_lt_rz) (Finset.mem_Icc.mp hrz_Fin).2⟩
      have hcy_eq : cy = cz := by
        have h1 := (hroots cy hcy_Icc).2.2.2.1
        have h2 := (hsub_c cz hcz_1K).2.2.2.2.2 _ hy_Scz |>.1
        omega
      subst hcy_eq
      exact lt_irrefl _ hy_lt_rz
    · have hx_Scz : blockRoot subs B cx ∈ (subblock1 subs cz).toFinset :=
        Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hz_Scz).1 hzx,
          le_trans (le_of_lt hx_lt_rz) (Finset.mem_Icc.mp hrz_Fin).2⟩
      have hcx_eq : cx = cz := by
        have h1 := (hroots cx hcx_Icc).2.2.2.1
        have h2 := (hsub_c cz hcz_1K).2.2.2.2.2 _ hx_Scz |>.1
        omega
      subst hcx_eq
      exact lt_irrefl _ hx_lt_rz
  · have hrz_lt_z : rz < z := hgt_rz' z hz_R
    have hnzl : ¬ z < rz := by omega
    have hsub_z_R : subtreeAtKey B z = subtreeAtKey R_r z := by
      rw [hsub_z_eq]; simp [subtreeAtKey, hnzl, hrz_lt_z]
    rw [hsub_z_R] at hx_sub_z hy_sub_z
    have hrz_lt_x : rz < blockRoot subs B cx := hgt_rz' _ (mem_of_mem_subtreeAtKey hx_sub_z)
    have hrz_lt_y : rz < blockRoot subs B cy := hgt_rz' _ (mem_of_mem_subtreeAtKey hy_sub_z)
    rcases hbet with ⟨hxz, _⟩ | ⟨hyz, _⟩
    · have hx_Scz : blockRoot subs B cx ∈ (subblock1 subs cz).toFinset :=
        Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hrz_Fin).1 (le_of_lt hrz_lt_x),
          le_trans hxz (Finset.mem_Icc.mp hz_Scz).2⟩
      have hcx_eq : cx = cz := by
        have h1 := (hroots cx hcx_Icc).2.2.2.1
        have h2 := (hsub_c cz hcz_1K).2.2.2.2.2 _ hx_Scz |>.1
        omega
      subst hcx_eq
      exact lt_irrefl _ hrz_lt_x
    · have hy_Scz : blockRoot subs B cy ∈ (subblock1 subs cz).toFinset :=
        Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hrz_Fin).1 (le_of_lt hrz_lt_y),
          le_trans hyz (Finset.mem_Icc.mp hz_Scz).2⟩
      have hcy_eq : cy = cz := by
        have h1 := (hroots cy hcy_Icc).2.2.2.1
        have h2 := (hsub_c cz hcz_1K).2.2.2.2.2 _ hy_Scz |>.1
        omega
      subst hcy_eq
      exact lt_irrefl _ hrz_lt_y

private theorem mem_rotateRightEdge_iff {t : BinaryTree ℕ} {u v : ℕ}
    (hedge : IsRightRotEdge t u v) :
    ∀ w, w ∈ rotateRightEdge t u v ↔ w ∈ t := by
  rcases hedge with ⟨A, D_mid, C, hv_mem, hsub⟩
  induction t with
  | nil => cases hv_mem
  | node k l r_sub ihl ihr =>
    by_cases hvk : v < k
    · unfold subtreeAtKey at hsub
      simp only [hvk, ↓reduceIte] at hsub
      have hv_l : v ∈ l := mem_of_mem_subtreeAtKey (by rw [hsub]; exact .here)
      intro w
      simp [rotateRightEdge, hvk, BinaryTree.mem_node_iff, ihl hv_l hsub w]
    · by_cases hkv : k < v
      · unfold subtreeAtKey at hsub
        simp only [hvk, hkv, ↓reduceIte] at hsub
        have hv_r : v ∈ r_sub := mem_of_mem_subtreeAtKey (by rw [hsub]; exact .here)
        intro w
        simp [rotateRightEdge, hvk, hkv, BinaryTree.mem_node_iff, ihr hv_r hsub w]
      · have hkv_eq : k = v := by omega
        subst k
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l; subst r_sub
        intro w
        simp only [rotateRightEdge, lt_irrefl, ↓reduceIte, BinaryTree.mem_node_iff]
        tauto

private theorem mem_subtreeAtKey_rotateRightEdge {t : BinaryTree ℕ} (ht : t.IsBST)
    {u v : ℕ} (hedge : IsRightRotEdge t u v) :
    let t' := rotateRightEdge t u v
    u ∈ t ∧ v ∈ t ∧ u < v ∧
    (∀ r ∈ t, r ≠ u → r ≠ v → ∀ w, w ∈ subtreeAtKey t' r ↔ w ∈ subtreeAtKey t r) ∧
    (∀ w, w ∈ subtreeAtKey t' u ↔ w ∈ subtreeAtKey t v) ∧
    (∀ w, w ∈ subtreeAtKey t v → u < w → w ∈ subtreeAtKey t' v) ∧
    (v ∉ subtreeAtKey t u) := by
  dsimp only
  rcases hedge with ⟨A, D_mid, C, hv_mem, hsub⟩
  induction t with
  | nil => cases hv_mem
  | node k l r_sub ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r_sub).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    by_cases hvk : v < k
    · unfold subtreeAtKey at hsub
      simp only [hvk, ↓reduceIte] at hsub
      have hv_l : v ∈ l := mem_of_mem_subtreeAtKey (by rw [hsub]; exact .here)
      obtain ⟨hu_l, _, huv, hother_l, hu_eq_l, hv_gt_l, hv_not_u⟩ := ihl hl hv_l hsub
      have huk : u < k := hlt' u hu_l
      have hrot : rotateRightEdge (.node k l r_sub) u v = .node k (rotateRightEdge l u v) r_sub := by
        simp [rotateRightEdge, hvk]
      have hmem_l := mem_rotateRightEdge_iff ⟨A, D_mid, C, hv_l, hsub⟩
      refine ⟨.left hu_l, .left hv_l, huv, ?_, ?_, ?_, ?_⟩
      · intro r hr_mem hru hrv w
        rw [hrot]
        rcases BinaryTree.mem_node_iff.mp hr_mem with rfl | hrL | hrR
        · simp [subtreeAtKey, BinaryTree.mem_node_iff, hmem_l w]
        · have hrk : r < k := hlt' r hrL
          simp [subtreeAtKey, hrk, hother_l r hrL hru hrv w]
        · have hkr : k < r := hgt' r hrR
          have hnrk : ¬ r < k := by omega
          simp [subtreeAtKey, hnrk, hkr]
      · intro w
        rw [hrot]
        simp [subtreeAtKey, huk, hvk, hu_eq_l w]
      · intro w hw huw
        rw [hrot]
        simp only [subtreeAtKey, hvk, ↓reduceIte] at hw ⊢
        exact hv_gt_l w hw huw
      · simp [subtreeAtKey, huk, hv_not_u]
    · by_cases hkv : k < v
      · unfold subtreeAtKey at hsub
        simp only [hvk, hkv, ↓reduceIte] at hsub
        have hv_r : v ∈ r_sub := mem_of_mem_subtreeAtKey (by rw [hsub]; exact .here)
        obtain ⟨hu_r, _, huv, hother_r, hu_eq_r, hv_gt_r, hv_not_u⟩ := ihr hr hv_r hsub
        have hku : k < u := hgt' u hu_r
        have hnuk : ¬ u < k := by omega
        have hrot : rotateRightEdge (.node k l r_sub) u v = .node k l (rotateRightEdge r_sub u v) := by
          simp [rotateRightEdge, hvk, hkv]
        have hmem_r := mem_rotateRightEdge_iff ⟨A, D_mid, C, hv_r, hsub⟩
        refine ⟨.right hu_r, .right hv_r, huv, ?_, ?_, ?_, ?_⟩
        · intro r hr_mem hru hrv w
          rw [hrot]
          rcases BinaryTree.mem_node_iff.mp hr_mem with rfl | hrL | hrR
          · simp [subtreeAtKey, BinaryTree.mem_node_iff, hmem_r w]
          · have hrk : r < k := hlt' r hrL
            simp [subtreeAtKey, hrk]
          · have hkr : k < r := hgt' r hrR
            have hnrk : ¬ r < k := by omega
            simp [subtreeAtKey, hnrk, hkr, hother_r r hrR hru hrv w]
        · intro w
          rw [hrot]
          simp [subtreeAtKey, hnuk, hku, hvk, hkv, hu_eq_r w]
        · intro w hw huw
          rw [hrot]
          simp only [subtreeAtKey, hvk, hkv, ↓reduceIte] at hw ⊢
          exact hv_gt_r w hw huw
        · simp [subtreeAtKey, hnuk, hku, hv_not_u]
      · have hkv_eq : k = v := by omega
        subst k
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l; subst r_sub
        obtain ⟨hlt_u, hgt_u, _, _⟩ := (SplayDeque.Direct.isBSTNode_iff u A D_mid).mp hl
        have hlt_u' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt_u
        have hgt_u' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt_u
        have huv : u < v := hlt' u .here
        have hrot : rotateRightEdge (.node v (.node u A D_mid) C) u v =
            .node u A (.node v D_mid C) := by
          simp [rotateRightEdge]
        refine ⟨.left .here, .here, huv, ?_, ?_, ?_, ?_⟩
        · intro r hr_mem hru hrv w
          rw [hrot]
          rcases BinaryTree.mem_node_iff.mp hr_mem with rfl | hrL | hrC
          · exact absurd rfl hrv
          · rcases BinaryTree.mem_node_iff.mp hrL with rfl | hrA | hrD
            · exact absurd rfl hru
            · have hru_lt : r < u := hlt_u' r hrA
              have hrv_lt : r < v := lt_trans hru_lt huv
              simp [subtreeAtKey, hru_lt, hrv_lt]
            · have hur_lt : u < r := hgt_u' r hrD
              have hnru : ¬ r < u := by omega
              have hrv_lt : r < v := hlt' r (.right hrD)
              simp [subtreeAtKey, hnru, hur_lt, hrv_lt]
          · have hvr_lt : v < r := hgt' r hrC
            have hur_lt : u < r := lt_trans huv hvr_lt
            have hnru : ¬ r < u := by omega
            have hnrv : ¬ r < v := by omega
            simp [subtreeAtKey, hnru, hur_lt, hnrv, hvr_lt]
        · intro w
          rw [hrot]
          simp only [subtreeAtKey, lt_irrefl, ↓reduceIte, BinaryTree.mem_node_iff]
          tauto
        · intro w hw huw
          rw [hrot]
          have hnvu : ¬ v < u := by omega
          simp only [subtreeAtKey, lt_irrefl, hnvu, huv, ↓reduceIte, BinaryTree.mem_node_iff] at hw ⊢
          rcases hw with rfl | (rfl | hwA | hwD) | hwC
          · exact Or.inl rfl
          · omega
          · have := hlt_u' w hwA; omega
          · exact Or.inr (Or.inl hwD)
          · exact Or.inr (Or.inr hwC)
        · simp only [subtreeAtKey, huv, lt_irrefl, ↓reduceIte]
          intro hv_in
          rcases BinaryTree.mem_node_iff.mp hv_in with hvu | hvA | hvD
          · omega
          · exact absurd (hlt' v (.left hvA)) (lt_irrefl _)
          · exact absurd (hlt' v (.right hvD)) (lt_irrefl _)

private theorem restrictTree_map_intra_rot {t : BinaryTree ℕ} (ht : t.IsBST)
    {u v : ℕ} {A D_mid C : BinaryTree ℕ}
    (hv_mem : v ∈ t) (hsub : subtreeAtKey t v = .node v (.node u A D_mid) C)
    (S₀ : Set ℕ) (f : ℕ → ℕ) (hf_uv : f u = f v)
    (hu_not : u ∉ S₀) (hv_not : v ∉ S₀)
    (hD_disj : ∀ d ∈ D_mid, d ∉ S₀ ∧ d ≠ u ∧ d ≠ v) :
    (restrictTree (rotateRightEdge t u v) (insert u S₀)).map f =
      (restrictTree t (insert v S₀)).map f := by
  induction t with
  | nil => cases hv_mem
  | node k l r_sub ihl ihr =>
    obtain ⟨hlt, hgt, hl, hr⟩ := (SplayDeque.Direct.isBSTNode_iff k l r_sub).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    by_cases hvk : v < k
    · unfold subtreeAtKey at hsub
      simp only [hvk, ↓reduceIte] at hsub
      have hv_l : v ∈ l := mem_of_mem_subtreeAtKey (by rw [hsub]; exact .here)
      have hu_l : u ∈ l := mem_of_mem_subtreeAtKey (by rw [hsub]; exact .left .here)
      have huk : u < k := hlt' u hu_l
      have hrot : rotateRightEdge (.node k l r_sub) u v = .node k (rotateRightEdge l u v) r_sub := by
        simp [rotateRightEdge, hvk]
      rw [hrot]
      have hk_iff : k ∈ insert u S₀ ↔ k ∈ insert v S₀ := by
        simp [show k ≠ u by omega, show k ≠ v by omega]
      have hr_congr : ∀ b ∈ r_sub, b ∈ insert u S₀ ↔ b ∈ insert v S₀ := by
        intro b hb
        have hkb : k < b := hgt' b hb
        simp [show b ≠ u by omega, show b ≠ v by omega]
      have hr_eq : restrictTree r_sub (insert u S₀) = restrictTree r_sub (insert v S₀) :=
        restrictTree_congr_mem r_sub _ _ hr_congr
      have hex_iff : (∃ b ∈ r_sub, b ∈ insert u S₀) ↔ (∃ b ∈ r_sub, b ∈ insert v S₀) :=
        ⟨fun ⟨b, hb, hbS⟩ => ⟨b, hb, (hr_congr b hb).mp hbS⟩,
         fun ⟨b, hb, hbS⟩ => ⟨b, hb, (hr_congr b hb).mpr hbS⟩⟩
      have hihl := ihl hl hv_l hsub
      conv_lhs => unfold restrictTree
      conv_rhs => unfold restrictTree
      by_cases hk1 : k ∈ insert u S₀
      · have hk2 : k ∈ insert v S₀ := hk_iff.mp hk1
        simp only [hk1, hk2, ↓reduceIte]
        change BinaryTree.node (f k) ((restrictTree (rotateRightEdge l u v) (insert u S₀)).map f)
            ((restrictTree r_sub (insert u S₀)).map f) =
          BinaryTree.node (f k) ((restrictTree l (insert v S₀)).map f)
            ((restrictTree r_sub (insert v S₀)).map f)
        rw [hihl, hr_eq]
      · have hk2 : k ∉ insert v S₀ := mt hk_iff.mpr hk1
        simp only [hk1, hk2, ↓reduceIte]
        by_cases hex1 : ∃ b ∈ r_sub, b ∈ insert u S₀
        · have hex2 : ∃ b ∈ r_sub, b ∈ insert v S₀ := hex_iff.mp hex1
          simp only [hex1, hex2, ↓reduceIte, hr_eq]
        · have hex2 : ¬ ∃ b ∈ r_sub, b ∈ insert v S₀ := mt hex_iff.mpr hex1
          simp only [hex1, hex2, ↓reduceIte, hihl]
    · by_cases hkv : k < v
      · unfold subtreeAtKey at hsub
        simp only [hvk, hkv, ↓reduceIte] at hsub
        have hv_r : v ∈ r_sub := mem_of_mem_subtreeAtKey (by rw [hsub]; exact .here)
        have hu_r : u ∈ r_sub := mem_of_mem_subtreeAtKey (by rw [hsub]; exact .left .here)
        have hku : k < u := hgt' u hu_r
        have hrot : rotateRightEdge (.node k l r_sub) u v = .node k l (rotateRightEdge r_sub u v) := by
          simp [rotateRightEdge, hvk, hkv]
        rw [hrot]
        have hk_iff : k ∈ insert u S₀ ↔ k ∈ insert v S₀ := by
          simp [show k ≠ u by omega, show k ≠ v by omega]
        have hl_congr : ∀ a ∈ l, a ∈ insert u S₀ ↔ a ∈ insert v S₀ := by
          intro a ha
          have hak : a < k := hlt' a ha
          simp [show a ≠ u by omega, show a ≠ v by omega]
        have hl_eq : restrictTree l (insert u S₀) = restrictTree l (insert v S₀) :=
          restrictTree_congr_mem l _ _ hl_congr
        have hu_rot : u ∈ rotateRightEdge r_sub u v :=
          (mem_rotateRightEdge_iff ⟨A, D_mid, C, hv_r, hsub⟩ u).mpr hu_r
        have hex1 : ∃ b ∈ rotateRightEdge r_sub u v, b ∈ insert u S₀ := ⟨u, hu_rot, Set.mem_insert u S₀⟩
        have hex2 : ∃ b ∈ r_sub, b ∈ insert v S₀ := ⟨v, hv_r, Set.mem_insert v S₀⟩
        have hihr := ihr hr hv_r hsub
        conv_lhs => unfold restrictTree
        conv_rhs => unfold restrictTree
        by_cases hk1 : k ∈ insert u S₀
        · have hk2 : k ∈ insert v S₀ := hk_iff.mp hk1
          simp only [hk1, hk2, ↓reduceIte]
          change BinaryTree.node (f k) ((restrictTree l (insert u S₀)).map f)
              ((restrictTree (rotateRightEdge r_sub u v) (insert u S₀)).map f) =
            BinaryTree.node (f k) ((restrictTree l (insert v S₀)).map f)
              ((restrictTree r_sub (insert v S₀)).map f)
          rw [hl_eq, hihr]
        · have hk2 : k ∉ insert v S₀ := mt hk_iff.mpr hk1
          simp only [hk1, hk2, hex1, hex2, ↓reduceIte, hihr]
      · have hkv_eq : k = v := by omega
        subst k
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte] at hsub
        injection hsub with _ hl_eq hr_eq
        subst l; subst r_sub
        obtain ⟨hlt_u, _, _, _⟩ := (SplayDeque.Direct.isBSTNode_iff u A D_mid).mp hl
        have hlt_u' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt_u
        have huv : u < v := hlt' u .here
        have hrot : rotateRightEdge (.node v (.node u A D_mid) C) u v =
            .node u A (.node v D_mid C) := by
          simp [rotateRightEdge]
        rw [hrot]
        have hA_eq : restrictTree A (insert u S₀) = restrictTree A (insert v S₀) := by
          apply restrictTree_congr_mem
          intro a ha
          have hau : a < u := hlt_u' a ha
          simp [show a ≠ u by omega, show a ≠ v by omega]
        have hC_congr : ∀ c ∈ C, c ∈ insert u S₀ ↔ c ∈ insert v S₀ := by
          intro c hc
          have hvc : v < c := hgt' c hc
          simp [show c ≠ u by omega, show c ≠ v by omega]
        have hC_eq : restrictTree C (insert u S₀) = restrictTree C (insert v S₀) :=
          restrictTree_congr_mem C _ _ hC_congr
        have hu_in : u ∈ insert u S₀ := Set.mem_insert u S₀
        have hv_in : v ∈ insert v S₀ := Set.mem_insert v S₀
        have hu_notin_v : u ∉ insert v S₀ := by simp [show u ≠ v by omega, hu_not]
        have hv_notin_u : v ∉ insert u S₀ := by simp [show v ≠ u by omega, hv_not]
        have hD_not_v : ¬ ∃ d ∈ D_mid, d ∈ insert v S₀ := by
          rintro ⟨d, hd, hdS⟩
          obtain ⟨h0, _, hdv⟩ := hD_disj d hd
          rcases Set.mem_insert_iff.mp hdS with rfl | hd0
          · exact hdv rfl
          · exact h0 hd0
        have hD_nil_u : restrictTree D_mid (insert u S₀) = .nil := by
          apply restrictTree_eq_nil_of_disjoint
          intro d hd hdS
          obtain ⟨h0, hdu, _⟩ := hD_disj d hd
          rcases Set.mem_insert_iff.mp hdS with rfl | hd0
          · exact hdu rfl
          · exact h0 hd0
        have hlhs_sub : restrictTree (.node v D_mid C) (insert u S₀) =
            restrictTree C (insert v S₀) := by
          conv_lhs => unfold restrictTree
          simp only [hv_notin_u, ↓reduceIte]
          split_ifs with hexC
          · exact hC_eq
          · rw [hD_nil_u]
            symm
            exact restrictTree_eq_nil_of_disjoint C (insert v S₀)
              (fun c hc hcS => hexC ⟨c, hc, (hC_congr c hc).mpr hcS⟩)
        have hrhs_sub : restrictTree (.node u A D_mid) (insert v S₀) =
            restrictTree A (insert v S₀) := by
          conv_lhs => unfold restrictTree
          simp only [hu_notin_v, hD_not_v, ↓reduceIte]
        conv_lhs => unfold restrictTree
        conv_rhs => unfold restrictTree
        simp only [hu_in, hv_in, ↓reduceIte, hlhs_sub, hrhs_sub, hA_eq]
        change BinaryTree.node (f u) ((restrictTree A (insert v S₀)).map f)
            ((restrictTree C (insert v S₀)).map f) =
          BinaryTree.node (f v) ((restrictTree A (insert v S₀)).map f)
            ((restrictTree C (insert v S₀)).map f)
        rw [hf_uv]

private theorem phaseSummaryBST_eviction_in_Ip
    (h_3_1 : ∀ {α : Type} [LinearOrder α] (t : BinaryTree α) (S : Set α),
      t.IsBST → IsLCAClosed t S →
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
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1
      ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1))
    {idag : ℕ}
    (hidag_start : proc.popStepIdx
      (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).lo ≤ idag)
    (hidag_empty : idag ≤ tauEmpty proc
      (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p))
    {c : ℕ}
    (hc_start : c ∈ leftSpine (phaseSummaryBST P proc (scaleTreePartitionChain T P M) (ℓ.val + 1) X p
      (proc.popStepIdx (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).lo)))
    (hc_not : c ∉ leftSpine (phaseSummaryBST P proc (scaleTreePartitionChain T P M) (ℓ.val + 1) X p idag)) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    let Sp := subblock1 subs p
    let tStart := proc.popStepIdx Sp.lo
    ∃ τ ∈ Finset.Ico tStart idag, ∃ c' ∈ Finset.Icc (p + 1) (c - 1),
      (∃ u v, proc.steps[τ]? = some (.upperRot u v) ∧
        u ∈ (subblock1 subs c').toFinset ∧ v ∈ (subblock1 subs c).toFinset) ∨
      (∃ e ∈ proc.rInt, e.stepIdx = τ ∧
        e.x ∈ (subblock1 subs c').toFinset ∧ e.y ∈ (subblock1 subs c).toFinset) := by
  dsimp only
  have hBp_all := phaseBlockBST_bst_and_step_in_Ip h_3_1 hValid proc ℓ X hX hp
  dsimp only at hBp_all
  obtain ⟨hBp_bst_keys, hBp_step⟩ := hBp_all
  obtain ⟨_, _, _, _, hsub_c, hsub_lt, _, _, hsub_cover⟩ := subblock1_props hValid ℓ X hX
  set chain := scaleTreePartitionChain T P M
  set ℓ_val := ℓ.val + 1
  set subs := childSubblocks (chain ℓ.succ) X
  set K_X := subs.length
  set Sp := subblock1 subs p
  set tStart := proc.popStepIdx Sp.lo
  set tEmpty := tauEmpty proc Sp
  set S_hi : Set ℕ := {u : ℕ | Sp.hi < u ∧ u ≤ X.hi}
  have hℓ : 1 ≤ ℓ_val ∧ ℓ_val ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  have hfin_eq : (⟨ℓ_val, Nat.lt_succ_of_le hℓ.2⟩ : Fin (M + 1)) = ℓ.succ := rfl
  obtain ⟨hp1, hp_sub1⟩ := Finset.mem_Icc.mp hp
  have hp_lt_K : p < K_X := by omega
  let G_of : BinaryTree ℕ → BinaryTree ℕ :=
    fun B => (preorderSummaryBST B (subs.drop p) 1).map (subblockIndex1 subs)
  have hG_eq : ∀ τ, phaseSummaryBST P proc chain ℓ_val X p τ =
      G_of (phaseBlockBST P proc chain ℓ_val X p τ) := by
    intro τ
    unfold phaseSummaryBST
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq]
    rfl
  have mem_Shi_subblock : ∀ w : ℕ, w ∈ S_hi →
      subblockIndex1 subs w ∈ Finset.Icc (p + 1) K_X ∧
      w ∈ (subblock1 subs (subblockIndex1 subs w)).toFinset := by
    intro w hwS
    change (subblock1 subs p).hi < w ∧ w ≤ X.hi at hwS
    have hSp_bounds := hsub_c p (Finset.mem_Icc.mpr ⟨hp1, le_of_lt hp_lt_K⟩)
    have hw_X : w ∈ Finset.Icc X.lo X.hi :=
      Finset.mem_Icc.mpr ⟨by have := hSp_bounds.2.2.1; have := hSp_bounds.2.2.2.1; omega, hwS.2⟩
    obtain ⟨hcw_1K, hw_Scw⟩ := hsub_cover w hw_X
    refine ⟨Finset.mem_Icc.mpr ⟨?_, (Finset.mem_Icc.mp hcw_1K).2⟩, hw_Scw⟩
    by_contra hle_p
    have hcw_le_p : subblockIndex1 subs w ≤ p := by omega
    rcases eq_or_lt_of_le hcw_le_p with h_eq | hlt
    · rw [h_eq] at hw_Scw
      have := (Finset.mem_Icc.mp hw_Scw).2
      omega
    · have := hsub_lt (subblockIndex1 subs w) p (Finset.mem_Icc.mp hcw_1K).1 hlt (le_of_lt hp_lt_K)
      have := (Finset.mem_Icc.mp hw_Scw).2
      omega
  -- Single rotation step lemma on `B ↦ rotateRightEdge B u v`
  have single_rot_evict : ∀ {B : BinaryTree ℕ} {u v : ℕ},
      B.IsBST → keyFinset B = Finset.Icc (Sp.hi + 1) X.hi →
      u ∈ S_hi → v ∈ S_hi → u < v → IsRightRotEdge B u v →
      c ∈ leftSpine (G_of B) → c ∉ leftSpine (G_of (rotateRightEdge B u v)) →
      ∃ c' ∈ Finset.Icc (p + 1) (c - 1),
        u ∈ (subblock1 subs c').toFinset ∧ v ∈ (subblock1 subs c).toFinset := by
    intro B u v hB_bst hB_keys hu_S hv_S huv hedge hc_in hc_out
    set B' := rotateRightEdge B u v
    have hB'_bst : B'.IsBST := rotateRightEdge_isBST hB_bst u v
    have hB'_keys : keyFinset B' = Finset.Icc (Sp.hi + 1) X.hi := by
      rw [← hB_keys]
      ext w
      rw [← mem_iff_mem_keyFinset, ← mem_iff_mem_keyFinset]
      exact mem_rotateRightEdge_iff hedge w
    obtain ⟨hc1_Icc, hu_Sc1⟩ := mem_Shi_subblock u hu_S
    obtain ⟨hc2_Icc, hv_Sc2⟩ := mem_Shi_subblock v hv_S
    set c₁ := subblockIndex1 subs u
    set c₂ := subblockIndex1 subs v
    have hc1_le_c2 : c₁ ≤ c₂ := by
      by_contra hgt
      have hlt21 : c₂ < c₁ := by omega
      have := hsub_lt c₂ c₁ (by have := (Finset.mem_Icc.mp hc2_Icc).1; omega) hlt21
        (Finset.mem_Icc.mp hc1_Icc).2
      have := (Finset.mem_Icc.mp hu_Sc1).1
      have := (Finset.mem_Icc.mp hv_Sc2).2
      omega
    have hsum_B := summary1_roots_and_lcaClosed hValid ℓ X hX hp hB_bst hB_keys
    have hsum_B' := summary1_roots_and_lcaClosed hValid ℓ X hX hp hB'_bst hB'_keys
    dsimp only at hsum_B hsum_B'
    simp only [show scaleTreePartitionChain T P M = chain from rfl,
      show childSubblocks (chain ℓ.succ) X = subs from rfl,
      show subs.length = K_X from rfl] at hsum_B hsum_B'
    obtain ⟨hroots_B, hGset_B, hlca_B⟩ := hsum_B
    obtain ⟨hroots_B', hGset_B', hlca_B'⟩ := hsum_B'
    obtain ⟨hu_B, hv_B, _, hother, hu_eq_v, hv_gt_u, hv_not_u⟩ :=
      mem_subtreeAtKey_rotateRightEdge hB_bst hedge
    have hroot_other : ∀ d ∈ Finset.Icc (p + 1) K_X, d ≠ c₁ → d ≠ c₂ →
        blockRoot subs B' d = blockRoot subs B d := by
      intro d hd hdc1 hdc2
      obtain ⟨_, hrd_B, hrd_Fin, hrd_idx, hrd_all, _⟩ := hroots_B d hd
      have hrd_ne_u : blockRoot subs B d ≠ u := fun h => hdc1 (hrd_idx.symm.trans (congrArg _ h))
      have hrd_ne_v : blockRoot subs B d ≠ v := fun h => hdc2 (hrd_idx.symm.trans (congrArg _ h))
      have hrd_B' : blockRoot subs B d ∈ B' := (mem_rotateRightEdge_iff hedge _).mpr hrd_B
      symm
      refine (hroots_B' d hd).2.2.2.2.2 _ hrd_B' hrd_Fin (fun w hwB' hwFin => ?_)
      rw [hother _ hrd_B hrd_ne_u hrd_ne_v w]
      exact hrd_all w ((mem_rotateRightEdge_iff hedge w).mp hwB') hwFin
    rcases eq_or_lt_of_le hc1_le_c2 with hc_same | hc_lt
    · -- Intra-block (`c₁ = c₂`): `G_of B' = G_of B`, contradicting `hc_out`!
      exfalso
      have hv_Sc1 : v ∈ (subblock1 subs c₁).toFinset := hc_same ▸ hv_Sc2
      have hdc2_of : ∀ {d : ℕ}, d ≠ c₁ → d ≠ c₂ := fun h => hc_same ▸ h
      by_cases hrv : blockRoot subs B c₁ = v
      · -- `blockRoot subs B c₁ = v`, `blockRoot subs B' c₁ = u`
        have hru' : blockRoot subs B' c₁ = u := by
          have hu_B' : u ∈ B' := (mem_rotateRightEdge_iff hedge u).mpr hu_B
          symm
          refine (hroots_B' c₁ hc1_Icc).2.2.2.2.2 u hu_B' hu_Sc1 (fun w hwB' hwFin => ?_)
          rw [hu_eq_v w, ← hrv]
          exact (hroots_B c₁ hc1_Icc).2.2.2.2.1 w ((mem_rotateRightEdge_iff hedge w).mp hwB') hwFin
        set S₀ : Set ℕ := {w : ℕ | ∃ d ∈ Finset.Icc (p + 1) K_X, d ≠ c₁ ∧ w = blockRoot subs B d}
        have hGset_B_eq : (preorderSummarySet B (subs.drop p) 1 : Set ℕ) = insert v S₀ := by
          ext w
          change w ∈ preorderSummarySet B (subs.drop p) 1 ↔ w = v ∨ ∃ d ∈ Finset.Icc (p + 1) K_X, d ≠ c₁ ∧ w = blockRoot subs B d
          rw [hGset_B]
          constructor
          · rintro ⟨d, hd, rfl⟩
            by_cases hdc : d = c₁
            · subst d; exact Or.inl hrv
            · exact Or.inr ⟨d, hd, hdc, rfl⟩
          · rintro (rfl | ⟨d, hd, _, rfl⟩)
            · exact ⟨c₁, hc1_Icc, hrv.symm⟩
            · exact ⟨d, hd, rfl⟩
        have hGset_B'_eq : (preorderSummarySet B' (subs.drop p) 1 : Set ℕ) = insert u S₀ := by
          ext w
          change w ∈ preorderSummarySet B' (subs.drop p) 1 ↔ w = u ∨ ∃ d ∈ Finset.Icc (p + 1) K_X, d ≠ c₁ ∧ w = blockRoot subs B d
          rw [hGset_B']
          constructor
          · rintro ⟨d, hd, rfl⟩
            by_cases hdc : d = c₁
            · subst d; exact Or.inl hru'
            · exact Or.inr ⟨d, hd, hdc, hroot_other d hd hdc (hdc2_of hdc)⟩
          · rintro (rfl | ⟨d, hd, hdc, rfl⟩)
            · exact ⟨c₁, hc1_Icc, hru'.symm⟩
            · exact ⟨d, hd, (hroot_other d hd hdc (hdc2_of hdc)).symm⟩
        have hu_not_S0 : u ∉ S₀ := by
          rintro ⟨d, hd, hdc, hu_eq⟩
          have hidx := (hroots_B d hd).2.2.2.1
          rw [← hu_eq] at hidx
          exact hdc hidx.symm
        have hv_not_S0 : v ∉ S₀ := by
          rintro ⟨d, hd, hdc, hv_eq⟩
          have hidx := (hroots_B d hd).2.2.2.1
          rw [← hv_eq] at hidx
          exact hdc (hidx.symm.trans hc_same.symm)
        rcases hedge with ⟨A, D_mid, C, _, hsub_v⟩
        obtain ⟨L_v, R_v, hsub_v', hbst_v⟩ := subtreeAtKey_bst_node hB_bst hv_B
        rw [hsub_v] at hsub_v'
        injection hsub_v' with _ hL_eq hR_eq
        subst L_v; subst R_v
        obtain ⟨hlt_v, _, hl_u, _⟩ := (SplayDeque.Direct.isBSTNode_iff v (.node u A D_mid) C).mp hbst_v
        obtain ⟨_, hgt_u, _, _⟩ := (SplayDeque.Direct.isBSTNode_iff u A D_mid).mp hl_u
        have hlt_v' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt_v
        have hgt_u' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt_u
        have hD_disj : ∀ dw ∈ D_mid, dw ∉ S₀ ∧ dw ≠ u ∧ dw ≠ v := by
          intro dw hdw
          have hudw : u < dw := hgt_u' dw hdw
          have hdwv : dw < v := hlt_v' dw (.right hdw)
          refine ⟨?_, by omega, by omega⟩
          rintro ⟨d, hd, hdc, hdw_eq⟩
          have hdw_Sc1 : dw ∈ (subblock1 subs c₁).toFinset :=
            Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hu_Sc1).1 (le_of_lt hudw),
              le_trans (le_of_lt hdwv) (Finset.mem_Icc.mp hv_Sc1).2⟩
          have hidx1 := (hsub_c c₁ (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc1_Icc).1; omega,
            (Finset.mem_Icc.mp hc1_Icc).2⟩)).2.2.2.2.2 dw hdw_Sc1 |>.1
          have hidx2 := (hroots_B d hd).2.2.2.1
          rw [← hdw_eq] at hidx2
          exact hdc (hidx2.symm.trans hidx1)
        have hG_same : G_of B' = G_of B := by
          dsimp only [G_of, preorderSummaryBST]
          rw [hGset_B'_eq, hGset_B_eq]
          exact restrictTree_map_intra_rot hB_bst hv_B hsub_v S₀ (subblockIndex1 subs) hc_same
            hu_not_S0 hv_not_S0 hD_disj
        exact hc_out (hG_same ▸ hc_in)
      · -- `blockRoot subs B c₁ ≠ v`, hence also `≠ u`!
        have hru : blockRoot subs B c₁ ≠ u := by
          intro h_eq
          have hv_sub := (hroots_B c₁ hc1_Icc).2.2.2.2.1 v hv_B hv_Sc1
          rw [h_eq] at hv_sub
          exact hv_not_u hv_sub
        have hrc1_same : blockRoot subs B' c₁ = blockRoot subs B c₁ := by
          obtain ⟨_, hrc_B, hrc_Fin, _, hrc_all, _⟩ := hroots_B c₁ hc1_Icc
          have hrc_B' : blockRoot subs B c₁ ∈ B' := (mem_rotateRightEdge_iff hedge _).mpr hrc_B
          symm
          refine (hroots_B' c₁ hc1_Icc).2.2.2.2.2 _ hrc_B' hrc_Fin (fun w hwB' hwFin => ?_)
          rw [hother _ hrc_B hru hrv w]
          exact hrc_all w ((mem_rotateRightEdge_iff hedge w).mp hwB') hwFin
        have hGset_same : preorderSummarySet B' (subs.drop p) 1 =
            preorderSummarySet B (subs.drop p) 1 := by
          ext w
          rw [hGset_B', hGset_B]
          constructor <;> rintro ⟨d, hd, rfl⟩
          · refine ⟨d, hd, ?_⟩
            by_cases hdc : d = c₁
            · subst d; exact hrc1_same
            · exact hroot_other d hd hdc (hdc2_of hdc)
          · refine ⟨d, hd, ?_⟩
            by_cases hdc : d = c₁
            · subst d; exact hrc1_same.symm
            · exact (hroot_other d hd hdc (hdc2_of hdc)).symm
        have hv_not_G : v ∉ (preorderSummarySet B (subs.drop p) 1 : Set ℕ) := by
          intro hvG
          change v ∈ preorderSummarySet B (subs.drop p) 1 at hvG
          obtain ⟨d, hd, hv_eq⟩ := (hGset_B v).mp hvG
          have hidx := (hroots_B d hd).2.2.2.1
          rw [← hv_eq] at hidx
          have hd_c1 : d = c₁ := hidx.symm.trans hc_same.symm
          subst hd_c1
          exact hrv hv_eq.symm
        obtain ⟨_, h31_rot, _⟩ := h_3_1 B _ hB_bst hlca_B
        have hedge_s : IsSingleRotEdge B u v := Or.inl ⟨huv, hedge⟩
        have hrot_s : rotateEdge B u v = B' := by simp [rotateEdge, huv, B']
        have hres_eq : restrictTree B' (preorderSummarySet B (subs.drop p) 1 : Set ℕ) =
            restrictTree B (preorderSummarySet B (subs.drop p) 1 : Set ℕ) := by
          rw [← hrot_s]
          exact (h31_rot u v hedge_s (hrot_s ▸ hGset_same ▸ hlca_B')).2
            (fun ⟨_, hvG⟩ => hv_not_G hvG)
        have hG_same : G_of B' = G_of B := by
          dsimp only [G_of, preorderSummaryBST]
          rw [hGset_same, hres_eq]
        exact hc_out (hG_same ▸ hc_in)
    · -- Inter-block (`c₁ < c₂`): `Gset B' = Gset B`!
      have hrc1_same : blockRoot subs B' c₁ = blockRoot subs B c₁ := by
        obtain ⟨_, hrc_B, hrc_Fin, hrc_idx, hrc_all, _⟩ := hroots_B c₁ hc1_Icc
        have hrc_ne_v : blockRoot subs B c₁ ≠ v := by
          intro h_eq; rw [h_eq] at hrc_idx; omega
        have hrc_B' : blockRoot subs B c₁ ∈ B' := (mem_rotateRightEdge_iff hedge _).mpr hrc_B
        symm
        refine (hroots_B' c₁ hc1_Icc).2.2.2.2.2 _ hrc_B' hrc_Fin (fun w hwB' hwFin => ?_)
        have hwB := (mem_rotateRightEdge_iff hedge w).mp hwB'
        by_cases hrc_u : blockRoot subs B c₁ = u
        · rw [hrc_u, hu_eq_v w]
          have hw_sub_u : w ∈ subtreeAtKey B u := hrc_u ▸ hrc_all w hwB hwFin
          rcases hedge with ⟨A, D_mid, C, _, hsub_v⟩
          have hu_sub_v : u ∈ subtreeAtKey B v := by rw [hsub_v]; exact .left .here
          have hsub_u_eq := subtreeAtKey_of_mem_subtreeAtKey hB_bst hu_sub_v
          rw [hsub_v] at hsub_u_eq ⊢
          rw [hsub_u_eq] at hw_sub_u
          simp only [subtreeAtKey, huv, ↓reduceIte] at hw_sub_u
          exact .left (mem_of_mem_subtreeAtKey hw_sub_u)
        · rw [hother _ hrc_B hrc_u hrc_ne_v w]
          exact hrc_all w hwB hwFin
      have hrc2_same : blockRoot subs B' c₂ = blockRoot subs B c₂ := by
        obtain ⟨_, hrc_B, hrc_Fin, hrc_idx, hrc_all, _⟩ := hroots_B c₂ hc2_Icc
        have hrc_ne_u : blockRoot subs B c₂ ≠ u := by
          intro h_eq; rw [h_eq] at hrc_idx; omega
        have hrc_B' : blockRoot subs B c₂ ∈ B' := (mem_rotateRightEdge_iff hedge _).mpr hrc_B
        symm
        refine (hroots_B' c₂ hc2_Icc).2.2.2.2.2 _ hrc_B' hrc_Fin (fun w hwB' hwFin => ?_)
        have hwB := (mem_rotateRightEdge_iff hedge w).mp hwB'
        by_cases hrc_v : blockRoot subs B c₂ = v
        · rw [hrc_v]
          have hu_lt_w : u < w := by
            have := hsub_lt c₁ c₂ (by have := (Finset.mem_Icc.mp hc1_Icc).1; omega) hc_lt
              (Finset.mem_Icc.mp hc2_Icc).2
            have := (Finset.mem_Icc.mp hu_Sc1).2
            have := (Finset.mem_Icc.mp hwFin).1
            omega
          exact hv_gt_u w (hrc_v ▸ hrc_all w hwB hwFin) hu_lt_w
        · rw [hother _ hrc_B hrc_ne_u hrc_v w]
          exact hrc_all w hwB hwFin
      have hGset_same : preorderSummarySet B' (subs.drop p) 1 =
          preorderSummarySet B (subs.drop p) 1 := by
        ext w
        rw [hGset_B', hGset_B]
        constructor <;> rintro ⟨d, hd, rfl⟩
        · refine ⟨d, hd, ?_⟩
          by_cases hd1 : d = c₁
          · subst d; exact hrc1_same
          · by_cases hd2 : d = c₂
            · subst d; exact hrc2_same
            · exact hroot_other d hd hd1 hd2
        · refine ⟨d, hd, ?_⟩
          by_cases hd1 : d = c₁
          · subst d; exact hrc1_same.symm
          · by_cases hd2 : d = c₂
            · subst d; exact hrc2_same.symm
            · exact (hroot_other d hd hd1 hd2).symm
      obtain ⟨_, h31_rot, _⟩ := h_3_1 B _ hB_bst hlca_B
      have hedge_s : IsSingleRotEdge B u v := Or.inl ⟨huv, hedge⟩
      have hrot_s : rotateEdge B u v = B' := by simp [rotateEdge, huv, B']
      have h31_uv := h31_rot u v hedge_s (hrot_s ▸ hGset_same ▸ hlca_B')
      by_cases huv_G : u ∈ (preorderSummarySet B (subs.drop p) 1 : Set ℕ) ∧
          v ∈ (preorderSummarySet B (subs.drop p) 1 : Set ℕ)
      · obtain ⟨_, hres_rot⟩ := h31_uv.1 huv_G
        have hrot_res : rotateEdge (restrictTree B (preorderSummarySet B (subs.drop p) 1 : Set ℕ)) u v =
            rotateRightEdge (restrictTree B (preorderSummarySet B (subs.drop p) 1 : Set ℕ)) u v := by
          simp [rotateEdge, huv]
        rw [hrot_s, hrot_res] at hres_rot
        set T₀ := restrictTree B (preorderSummarySet B (subs.drop p) 1 : Set ℕ)
        have hc_in' : c ∈ (leftSpine T₀).map (subblockIndex1 subs) := by
          rw [← leftSpine_map]; exact hc_in
        have hc_out' : c ∉ (leftSpine (rotateRightEdge T₀ u v)).map (subblockIndex1 subs) := by
          rw [← leftSpine_map, ← hres_rot]
          dsimp only [G_of, preorderSummaryBST] at hc_out
          rw [hGset_same] at hc_out
          exact hc_out
        obtain ⟨w, hw_ls, hfw_c⟩ := List.mem_map.mp hc_in'
        have hw_not_rot : w ∉ leftSpine (rotateRightEdge T₀ u v) :=
          fun hw' => hc_out' (List.mem_map_of_mem hw' |> fun h => hfw_c ▸ h)
        have hw_eq_v : w = v := by
          by_contra hne
          exact hw_not_rot ((mem_leftSpine_rotateRightEdge_iff_of_ne T₀ u v hne).mpr hw_ls)
        subst w
        change c₂ = c at hfw_c
        subst hfw_c
        exact ⟨c₁, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hc1_Icc).1, by omega⟩, hu_Sc1, hv_Sc2⟩
      · exfalso
        have hres_eq := h31_uv.2 huv_G
        rw [hrot_s] at hres_eq
        have hG_same : G_of B' = G_of B := by
          dsimp only [G_of, preorderSummaryBST]
          rw [hGset_same, hres_eq]
        exact hc_out (hG_same ▸ hc_in)
  -- Lift `single_rot_evict` across `PhaseBlockStepRel`
  have rel_evict : ∀ {τ : ℕ} {B₁ B₂ : BinaryTree ℕ},
      B₁.IsBST → keyFinset B₁ = Finset.Icc (Sp.hi + 1) X.hi →
      PhaseBlockStepRel S_hi {e : InternalPopRot | e ∈ proc.rInt ∧ e.stepIdx = τ} B₁ B₂ →
      B₂.IsBST ∧ keyFinset B₂ = Finset.Icc (Sp.hi + 1) X.hi ∧
      (c ∈ leftSpine (G_of B₁) → c ∉ leftSpine (G_of B₂) →
        ∃ c' ∈ Finset.Icc (p + 1) (c - 1), ∃ e ∈ proc.rInt, e.stepIdx = τ ∧
          e.x ∈ (subblock1 subs c').toFinset ∧ e.y ∈ (subblock1 subs c).toFinset) := by
    intro τ B₁ B₂ hB1_bst hB1_keys hrel
    induction hrel with
    | refl =>
      exact ⟨hB1_bst, hB1_keys, fun hc1 hc2 => absurd hc1 hc2⟩
    | @step B_mid e _ he hxy hxS hyS hBm_bst hedge ih =>
      obtain ⟨_, hBm_keys, ih_ev⟩ := ih
      have hBnext_bst : (rotateRightEdge B_mid e.x e.y).IsBST :=
        rotateRightEdge_isBST hBm_bst e.x e.y
      have hBnext_keys : keyFinset (rotateRightEdge B_mid e.x e.y) = Finset.Icc (Sp.hi + 1) X.hi := by
        rw [← hBm_keys]
        ext w
        rw [← mem_iff_mem_keyFinset, ← mem_iff_mem_keyFinset]
        exact mem_rotateRightEdge_iff hedge w
      refine ⟨hBnext_bst, hBnext_keys, fun hc1 hc_next => ?_⟩
      by_cases hc_mid : c ∈ leftSpine (G_of B_mid)
      · obtain ⟨c', hc'_Icc, hex, hey⟩ :=
          single_rot_evict hBm_bst hBm_keys hxS hyS hxy hedge hc_mid hc_next
        exact ⟨c', hc'_Icc, e, he.1, he.2, hex, hey⟩
      · exact ih_ev hc1 hc_mid
  -- Induct on `d := idag - tStart`
  rw [hG_eq] at hc_start hc_not
  obtain ⟨d, hd_eq⟩ : ∃ d, idag = tStart + d := ⟨idag - tStart, by omega⟩
  subst hd_eq
  induction d with
  | zero => simp only [Nat.add_zero] at hc_not; exact absurd hc_start hc_not
  | succ d ihd =>
    set τ := tStart + d
    have hτ_succ : tStart + (d + 1) = τ + 1 := by omega
    rw [hτ_succ] at hc_not
    have hτ_start : tStart ≤ τ := Nat.le_add_right tStart d
    have hτ_empty : τ < tEmpty := by omega
    by_cases hc_τ : c ∈ leftSpine (G_of (phaseBlockBST P proc chain ℓ_val X p τ))
    · have hstep := hBp_step τ hτ_start hτ_empty
      obtain ⟨hBp_bst, hBp_keys⟩ := hBp_bst_keys τ (le_of_lt hτ_empty)
      have hτ_len : τ < proc.steps.length :=
        lt_of_lt_of_le hτ_empty (active_window_props hValid proc ℓ X hX hp).2.2.2.2.2.2.2.2.1
      cases hop : proc.steps[τ]'hτ_len with
      | push w =>
        rw [hop] at hstep
        dsimp only at hstep
        exact absurd (hstep ▸ hc_τ) hc_not
      | shift =>
        rw [hop] at hstep
        dsimp only at hstep
        exact absurd (hstep ▸ hc_τ) hc_not
      | upperRot u v =>
        rw [hop] at hstep
        dsimp only at hstep
        rcases hstep with hsame | ⟨huS, hvS, huv, hedge, hrot_eq⟩
        · exact absurd (hsame ▸ hc_τ) hc_not
        · change phaseBlockBST P proc chain ℓ_val X p (τ + 1) =
              rotateRightEdge (phaseBlockBST P proc chain ℓ_val X p τ) u v at hrot_eq
          rw [hrot_eq] at hc_not
          obtain ⟨c', hc'_Icc, hu_Sc', hv_Sc⟩ :=
            single_rot_evict hBp_bst hBp_keys huS hvS huv hedge hc_τ hc_not
          exact ⟨τ, Finset.mem_Ico.mpr ⟨hτ_start, by omega⟩, c', hc'_Icc,
            Or.inl ⟨u, v, (List.getElem?_eq_getElem hτ_len).trans (congrArg some hop),
              hu_Sc', hv_Sc⟩⟩
      | pop s' =>
        rw [hop] at hstep
        dsimp only at hstep
        obtain ⟨_, _, hev⟩ := rel_evict hBp_bst hBp_keys hstep
        obtain ⟨c', hc'_Icc, e, he_rInt, he_step, hex, hey⟩ := hev hc_τ hc_not
        exact ⟨τ, Finset.mem_Ico.mpr ⟨hτ_start, by omega⟩, c', hc'_Icc,
          Or.inr ⟨e, he_rInt, he_step, hex, hey⟩⟩
    · obtain ⟨τ', hτ'_Ico, rest⟩ := ihd (by omega) (by omega) hc_τ
      exact ⟨τ', Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hτ'_Ico).1,
        lt_trans (Finset.mem_Ico.mp hτ'_Ico).2 (Nat.lt_succ_self _)⟩, rest⟩

private theorem leftSpine_fillCartesianSlots_above (insFn : ℕ → ℕ) (U : Finset ℕ) :
    ∀ (lo hi : Option ℕ) (t : BinaryTree ℕ) {m₀ : ℕ},
      t.IsBST → m₀ ∈ leftSpine t →
      ∀ {v : ℕ}, m₀ ≤ v →
        (v ∈ leftSpine (fillCartesianSlots insFn U lo hi t) ↔ v ∈ leftSpine t) := by
  intro lo hi t
  induction t generalizing lo hi with
  | nil => intro _ _ hm₀; cases hm₀
  | node k l r ihl _ =>
    intro m₀ ht hm₀ v hmv
    obtain ⟨hlt, _, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    unfold fillCartesianSlots
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hm₀ ⊢
    rcases hm₀ with hm₀_l | hm₀_eq
    · rw [ihl lo (some k) hl hm₀_l hmv]
    · subst hm₀_eq
      rcases eq_or_lt_of_le hmv with rfl | hkv
      · simp
      · have hnot1 : v ∉ leftSpine (fillCartesianSlots insFn U lo (some m₀) l) := by
          intro hv
          have := mem_fillCartesianSlots_lt_hi insFn U lo m₀ l hl hlt' v (mem_of_mem_leftSpine hv)
          omega
        have hnot2 : v ∉ leftSpine l := by
          intro hv
          have := hlt' v (mem_of_mem_leftSpine hv)
          omega
        exact ⟨fun h => Or.inr (h.resolve_left hnot1), fun h => Or.inr (h.resolve_left hnot2)⟩

private theorem leftSpine_restrictTree_above {t : BinaryTree ℕ} (ht : t.IsBST)
    {S : Set ℕ} (hlca : IsLCAClosed t S) {x₀ : ℕ}
    (hx₀_ls : x₀ ∈ leftSpine t) (hx₀_S : x₀ ∈ S) :
    ∀ {v : ℕ}, x₀ ≤ v →
      (v ∈ leftSpine (restrictTree t S) ↔ v ∈ leftSpine t ∧ v ∈ S) := by
  induction t with
  | nil => cases hx₀_ls
  | node u A B ihA _ =>
    obtain ⟨hlt, hgt, hA, _⟩ := (SplayDeque.Direct.isBSTNode_iff u A B).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    have hgt' := (SplayDeque.Direct.forallTree_iff _ _).mp hgt
    have hlca_A : IsLCAClosed A S := by
      intro x hx y hy hxS hyS z hz
      have hxu : x < u := hlt' x hx
      have hyu : y < u := hlt' y hy
      have hlca_node : lcaBST (.node u A B) x y = some z := by
        unfold lcaBST; simp [hxu, hyu, hz]
      exact hlca x (.left hx) y (.left hy) hxS hyS z hlca_node
    intro v hxv
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx₀_ls ⊢
    by_cases huS : u ∈ S
    · unfold restrictTree
      simp only [huS, ↓reduceIte, leftSpine, List.mem_append, List.mem_singleton]
      rcases hx₀_ls with hx₀_A | rfl
      · rw [ihA hA hlca_A hx₀_A hxv]
        constructor
        · rintro (⟨h1, h2⟩ | rfl)
          · exact ⟨Or.inl h1, h2⟩
          · exact ⟨Or.inr rfl, huS⟩
        · rintro ⟨h1 | rfl, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr rfl
      · have hnot_res : v ∉ leftSpine (restrictTree A S) := by
          intro hv
          have hvA := (mem_of_mem_restrictTree A S (mem_of_mem_leftSpine hv)).1
          have := hlt' v hvA; omega
        have hnot_A : v ∉ leftSpine A := by
          intro hv; have := hlt' v (mem_of_mem_leftSpine hv); omega
        simp only [hnot_res, hnot_A, false_or]
        exact ⟨fun h => ⟨h, h ▸ huS⟩, fun h => h.1⟩
    · have hx₀_A : x₀ ∈ leftSpine A := by
        rcases hx₀_ls with h | rfl
        · exact h
        · exact absurd hx₀_S huS
      have hnoB : ¬ ∃ b ∈ B, b ∈ S := by
        rintro ⟨b, hbB, hbS⟩
        have hx₀_in_A : x₀ ∈ A := mem_of_mem_leftSpine hx₀_A
        have hx₀u : x₀ < u := hlt' x₀ hx₀_in_A
        have hub : u < b := hgt' b hbB
        have hlca_u : lcaBST (.node u A B) x₀ b = some u := by
          unfold lcaBST
          have h1 : ¬ (x₀ < u ∧ b < u) := by omega
          have h2 : ¬ (u < x₀ ∧ u < b) := by omega
          simp [h1, h2]
        exact huS (hlca x₀ (.left hx₀_in_A) b (.right hbB) hx₀_S hbS u hlca_u)
      unfold restrictTree
      simp only [huS, hnoB, ↓reduceIte]
      rw [ihA hA hlca_A hx₀_A hxv]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
      · rintro ⟨h1 | rfl, h2⟩
        · exact ⟨h1, h2⟩
        · exact absurd h2 huS

private theorem spine_correspondence_at_lead
    (h_3_1 : ∀ {α : Type} [LinearOrder α] (t : BinaryTree α) (S : Set α),
      t.IsBST → IsLCAClosed t S →
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
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1
      ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1))
    {c_a : ℕ}
    (hca_Fp : c_a ∈ promotedSubblockIndices P proc (scaleTreePartitionChain T P M) (ℓ.val + 1) X p) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    let K_X := subs.length
    let Sp := subblock1 subs p
    let idag := proc.popStepIdx (leadPopKey P proc chain ℓ_val X p c_a)
    let Bp := phaseBlockBST P proc chain ℓ_val X p idag
    let G_idag := phaseSummaryBST P proc chain ℓ_val X p idag
    proc.popStepIdx Sp.lo ≤ idag ∧
    idag < tauEmpty proc Sp ∧
    (∃ e_a ∈ vXp P proc chain ℓ_val X p,
      e_a ∈ leadExitSet P proc chain ℓ_val X p ∧
      e_a ∈ proc.rInt ∧
      e_a.x ∈ (subblock1 subs c_a).toFinset ∧
      leadPopKey P proc chain ℓ_val X p c_a = e_a.s ∧
      e_a.stepIdx = idag ∧
      blockRoot subs Bp c_a = e_a.x ∧
      c_a ∈ leftSpine G_idag) ∧
    (∀ c ∈ Finset.Icc c_a K_X,
      blockRoot subs Bp c ∈ (subblock1 subs c).toFinset ∧
      subblockIndex1 subs (blockRoot subs Bp c) = c ∧
      (c ∈ leftSpine G_idag ↔ blockRoot subs Bp c ∈ leftSpine (proc.treeAt idag)) ∧
      (c ∈ leftSpine G_idag →
        ∀ z ∈ leftSpine (proc.treeAt idag), blockRoot subs Bp c < z → (subblock1 subs c).hi < z)) := by
  dsimp only
  have hChain := validScaleTree_chain hValid
  obtain ⟨hX1, _, hXP, _, hsub_c, hsub_lt, _, _, _⟩ := subblock1_props hValid ℓ X hX
  set chain := scaleTreePartitionChain T P M
  set ℓ_val := ℓ.val + 1
  set subs := childSubblocks (chain ℓ.succ) X
  set K_X := subs.length
  set Sp := subblock1 subs p
  set idag := proc.popStepIdx (leadPopKey P proc chain ℓ_val X p c_a)
  set Bp := phaseBlockBST P proc chain ℓ_val X p idag
  set G_idag := phaseSummaryBST P proc chain ℓ_val X p idag
  set S_hi : Set ℕ := {u : ℕ | Sp.hi < u ∧ u ≤ X.hi}
  have hℓ : 1 ≤ ℓ_val ∧ ℓ_val ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  have hfin_eq : (⟨ℓ_val, Nat.lt_succ_of_le hℓ.2⟩ : Fin (M + 1)) = ℓ.succ := rfl
  obtain ⟨hp1, hp_sub1⟩ := Finset.mem_Icc.mp hp
  obtain ⟨hrInt_basic, _⟩ := rInt_basic_and_order proc
  obtain ⟨_, _, hpop_mono, _, _⟩ := popStepIdx_and_insStep_props proc
  obtain ⟨hbst_all, _⟩ := proc_tree_bst_and_step_keys proc
  have hca_Icc : c_a ∈ Finset.Icc (p + 1) K_X := by
    have hca' := hca_Fp
    unfold promotedSubblockIndices at hca'
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq,
      show childSubblocks (chain ℓ.succ) X = subs from rfl] at hca'
    exact (Finset.mem_filter.mp hca').1
  have hlead_a := leadExit_unique_and_popKey hValid proc ℓ X hX p c_a hca_Fp
  simp only [show scaleTreePartitionChain T P M = chain from rfl,
    show ℓ.val + 1 = ℓ_val from rfl,
    show childSubblocks (chain ℓ.succ) X = subs from rfl] at hlead_a
  obtain ⟨e_a, hea_lead, hea_vXp, hea_x, hkey_a, _, _⟩ := hlead_a
  have hea_vXp' := hea_vXp
  unfold vXp at hea_vXp'
  simp only [hℓ, and_self, ↓reduceDIte, hfin_eq, Finset.mem_filter] at hea_vXp'
  rcases hea_vXp' with ⟨hea_act, hsep_xy, heas_Sp⟩
  unfold b3ExitAct at hea_act
  rw [Finset.mem_filter] at hea_act
  rcases hea_act with ⟨hea_exit, hea_tau⟩
  simp only [hsep_xy, hℓ.2, ↓reduceDIte, hfin_eq] at hea_tau
  unfold b3Exit at hea_exit
  rw [Finset.mem_filter] at hea_exit
  rcases hea_exit with ⟨hea_rInt, _⟩
  obtain ⟨heas_Icc, hea_step_eq, _, hs_lt_xa, hxa_lt_ya, hya_lt_za, hza_le_P⟩ :=
    hrInt_basic e_a hea_rInt
  have hidag_eq : e_a.stepIdx = idag := by dsimp [idag]; rw [hkey_a, hea_step_eq]
  obtain ⟨_, _, hSp_Xlo, hSp_lohi, hSp_Xhi, hSp_w⟩ :=
    hsub_c p (Finset.mem_Icc.mpr ⟨hp1, by omega⟩)
  have hblock_eas : blockAt (chain ℓ.succ) e_a.s = Sp := (hSp_w e_a.s heas_Sp).2.1
  rw [hblock_eas, hidag_eq] at hea_tau
  have hidag_start : proc.popStepIdx Sp.lo ≤ idag := by
    rw [← hidag_eq, hea_step_eq]
    have hSplo_Icc : Sp.lo ∈ Finset.Icc 1 P := by
      change (subblock1 subs p).lo ∈ Finset.Icc 1 P
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact (hpop_mono Sp.lo hSplo_Icc e_a.s heas_Icc).2.mp (Finset.mem_Icc.mp heas_Sp).1
  have hidag_len : idag ≤ proc.steps.length :=
    le_of_lt (lt_of_lt_of_le hea_tau (active_window_props hValid proc ℓ X hX hp).2.2.2.2.2.2.2.2.1)
  obtain ⟨ht_bst, _⟩ := hbst_all idag hidag_len
  obtain ⟨hτ_lt, b1, hop_a, hb1_eq, _, _, _, hsub_xa, hsub_ya, _⟩ :=
    (mem_rInt_iff proc e_a).mp hea_rInt
  obtain ⟨hval_a, _⟩ := proc_step_at proc hτ_lt
  rw [hop_a] at hval_a
  rcases hval_a with ⟨b1', _, hmin_s, hb1', hb1'_ls⟩
  change proc.b1At e_a.stepIdx = some b1' at hb1'
  rw [hidag_eq] at hb1_eq hsub_xa hsub_ya hmin_s hb1' hb1'_ls
  rw [hb1_eq] at hb1'; injection hb1' with hbb; subst b1'
  obtain ⟨_, _, hs_hd, _, _⟩ := (minKey_bst_props ht_bst).2 e_a.s hmin_s
  have hes_ls : e_a.s ∈ leftSpine (proc.treeAt idag) := List.mem_of_head? hs_hd
  have hpw_ls : (leftSpine (proc.treeAt idag)).Pairwise (· < ·) := leftSpine_pairwise_lt ht_bst
  obtain ⟨_, _, hpw_sub, _, _, hmem_sub⟩ := takeThrough_props hpw_ls hb1'_ls
  have hxa_ls : e_a.x ∈ leftSpine (proc.treeAt idag) :=
    ((hmem_sub e_a.x).mp (List.mem_of_getElem? hsub_xa)).1
  -- No element of `leftSpine (proc.treeAt idag)` strictly between `e_a.x` and `e_a.y`
  have hno_ls_between : ∀ w ∈ leftSpine (proc.treeAt idag), ¬ (e_a.x < w ∧ w < e_a.y) := by
    intro w hw_ls ⟨hxw, hwy⟩
    have hy_le_b1 : e_a.y ≤ b1 := ((hmem_sub e_a.y).mp (List.mem_of_getElem? hsub_ya)).2
    have hw_sub : w ∈ takeThrough (leftSpine (proc.treeAt idag)) b1 :=
      (hmem_sub w).mpr ⟨hw_ls, by omega⟩
    obtain ⟨iw, hiw_lt, rfl⟩ := List.getElem_of_mem hw_sub
    obtain ⟨hix_lt, hxa_eq⟩ := List.getElem?_eq_some_iff.mp hsub_xa
    obtain ⟨hiy_lt, hya_eq⟩ := List.getElem?_eq_some_iff.mp hsub_ya
    rw [← hxa_eq] at hxw
    rw [← hya_eq] at hwy
    have hix_lt_iw : 2 * e_a.j - 1 < iw := by
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
      · exact lt_irrefl _ hxw
      · exact lt_asymm hxw (List.pairwise_iff_getElem.mp hpw_sub iw (2 * e_a.j - 1) hiw_lt hix_lt hgt)
    have hiw_lt_iy : iw < 2 * e_a.j := by
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
      · exact lt_irrefl _ hwy
      · exact lt_asymm hwy (List.pairwise_iff_getElem.mp hpw_sub (2 * e_a.j) iw hiy_lt hiw_lt hgt)
    omega
  -- `(subblock1 subs c_a).hi < e_a.y`
  have hca_Icc1 : c_a ∈ Finset.Icc 1 K_X :=
    Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hca_Icc).1; omega, (Finset.mem_Icc.mp hca_Icc).2⟩
  obtain ⟨_, _, hSca_Xlo, _, hSca_Xhi, hSca_w⟩ := hsub_c c_a hca_Icc1
  have hxa_Icc : e_a.x ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hya_Icc : e_a.y ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsep_iff := ((partSepScale_props hChain hxa_Icc hya_Icc).2.2.2 ℓ).1.mp hsep_xy
  have hblock_xa_succ : blockAt (chain ℓ.succ) e_a.x = subblock1 subs c_a :=
    (hSca_w e_a.x hea_x).2.1
  have hSca_hi_lt_ya : (subblock1 subs c_a).hi < e_a.y := by
    by_contra hge
    have hya_Sca : e_a.y ∈ (subblock1 subs c_a).toFinset :=
      Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hea_x).1 (le_of_lt hxa_lt_ya), by omega⟩
    have hblock_ya_succ : blockAt (chain ℓ.succ) e_a.y = subblock1 subs c_a :=
      (hSca_w e_a.y hya_Sca).2.1
    exact hsep_iff.2 (hblock_xa_succ.trans hblock_ya_succ.symm)
  -- Left-spine correspondence between `proc.treeAt idag`, `cartesianExt proc idag`, `Bp`, and `G_idag`
  have hls_ext_iff : ∀ {v : ℕ}, e_a.s ≤ v →
      (v ∈ leftSpine (cartesianExt proc idag) ↔ v ∈ leftSpine (proc.treeAt idag)) := by
    intro v hsv
    unfold cartesianExt
    exact leftSpine_fillCartesianSlots_above proc.insStep _ none none (proc.treeAt idag)
      ht_bst hes_ls hsv
  obtain ⟨hext_bst, _⟩ := cartesianExt_bst_and_mem proc hidag_len
  have hBp_def : Bp = restrictTree (cartesianExt proc idag) S_hi := by
    dsimp [Bp, phaseBlockBST, S_hi]
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq]
    rfl
  have hSp_lt_Sca : Sp.hi < (subblock1 subs c_a).lo :=
    hsub_lt p c_a hp1 (Finset.mem_Icc.mp hca_Icc).1 (Finset.mem_Icc.mp hca_Icc).2
  have hxa_Shi : e_a.x ∈ S_hi :=
    ⟨lt_of_lt_of_le hSp_lt_Sca (Finset.mem_Icc.mp hea_x).1,
     le_trans (Finset.mem_Icc.mp hea_x).2 hSca_Xhi⟩
  have hxa_ls_ext : e_a.x ∈ leftSpine (cartesianExt proc idag) :=
    (hls_ext_iff (le_of_lt hs_lt_xa)).mpr hxa_ls
  have hls_Bp_iff : ∀ {v : ℕ}, e_a.x ≤ v →
      (v ∈ leftSpine Bp ↔ v ∈ leftSpine (proc.treeAt idag) ∧ v ∈ S_hi) := by
    intro v hxv
    rw [hBp_def, leftSpine_restrictTree_above hext_bst (isLCAClosed_gt_le _ Sp.hi X.hi)
      hxa_ls_ext hxa_Shi hxv, hls_ext_iff (le_trans (le_of_lt hs_lt_xa) hxv)]
  have hxa_ls_Bp : e_a.x ∈ leftSpine Bp := (hls_Bp_iff le_rfl).mpr ⟨hxa_ls, hxa_Shi⟩
  obtain ⟨hBp_bst, hBp_keys⟩ :=
    (phaseBlockBST_bst_and_step_in_Ip h_3_1 hValid proc ℓ X hX hp).1 idag (le_of_lt hea_tau)
  have hsum_idag := summary1_roots_and_lcaClosed hValid ℓ X hX hp hBp_bst hBp_keys
  dsimp only at hsum_idag
  simp only [show scaleTreePartitionChain T P M = chain from rfl,
    show ℓ.val + 1 = ℓ_val from rfl,
    show childSubblocks (chain ℓ.succ) X = subs from rfl,
    show subs.length = K_X from rfl,
    show phaseBlockBST P proc chain ℓ_val X p idag = Bp from rfl] at hsum_idag hBp_bst
  obtain ⟨hroots, hGset, hlca_G⟩ := hsum_idag
  -- Deduce `blockRoot subs Bp c_a = e_a.x`!
  obtain ⟨_, hra_Bp, hra_Fin, _, hra_sub, _⟩ := hroots c_a hca_Icc
  have hxa_sub_ra : e_a.x ∈ subtreeAtKey Bp (blockRoot subs Bp c_a) :=
    hra_sub e_a.x (mem_of_mem_leftSpine hxa_ls_Bp) hea_x
  obtain ⟨hra_ls_Bp, hxa_le_ra⟩ :=
    mem_leftSpine_of_leftSpine_in_subtree hBp_bst hxa_ls_Bp hra_Bp hxa_sub_ra
  have hra_ls_t : blockRoot subs Bp c_a ∈ leftSpine (proc.treeAt idag) :=
    ((hls_Bp_iff hxa_le_ra).mp hra_ls_Bp).1
  have hra_lt_ya : blockRoot subs Bp c_a < e_a.y :=
    lt_of_le_of_lt (Finset.mem_Icc.mp hra_Fin).2 hSca_hi_lt_ya
  have hra_eq_xa : blockRoot subs Bp c_a = e_a.x := by
    rcases eq_or_lt_of_le hxa_le_ra with h_eq | hlt
    · exact h_eq.symm
    · exact absurd ⟨hlt, hra_lt_ya⟩ (hno_ls_between _ hra_ls_t)
  -- `G_idag = (restrictTree Bp Gset).map (subblockIndex1 subs)`
  set Gset := preorderSummarySet Bp (subs.drop p) 1
  have hG_def : G_idag = (restrictTree Bp Gset).map (subblockIndex1 subs) := by
    dsimp [G_idag, phaseSummaryBST, preorderSummaryBST, Bp, Gset]
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq]
    rfl
  have hxa_Gset : e_a.x ∈ (Gset : Set ℕ) :=
    (hGset e_a.x).mpr ⟨c_a, hca_Icc, hra_eq_xa.symm⟩
  have hls_resG_iff : ∀ {v : ℕ}, e_a.x ≤ v →
      (v ∈ leftSpine (restrictTree Bp Gset) ↔ v ∈ leftSpine Bp ∧ v ∈ (Gset : Set ℕ)) :=
    fun hxv => leftSpine_restrictTree_above hBp_bst hlca_G hxa_ls_Bp hxa_Gset hxv
  have hca_Props : ∀ c ∈ Finset.Icc c_a K_X,
      blockRoot subs Bp c ∈ (subblock1 subs c).toFinset ∧
      subblockIndex1 subs (blockRoot subs Bp c) = c ∧
      (c ∈ leftSpine G_idag ↔ blockRoot subs Bp c ∈ leftSpine (proc.treeAt idag)) ∧
      (c ∈ leftSpine G_idag →
        ∀ z ∈ leftSpine (proc.treeAt idag), blockRoot subs Bp c < z → (subblock1 subs c).hi < z) := by
    intro c hc_Icc
    have hc_pK : c ∈ Finset.Icc (p + 1) K_X :=
      Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hca_Icc).1 (Finset.mem_Icc.mp hc_Icc).1,
        (Finset.mem_Icc.mp hc_Icc).2⟩
    obtain ⟨_, hrc_Bp, hrc_Fin, hrc_idx, hrc_sub, _⟩ := hroots c hc_pK
    have hxa_le_rc : e_a.x ≤ blockRoot subs Bp c := by
      rcases eq_or_lt_of_le (Finset.mem_Icc.mp hc_Icc).1 with rfl | hlt_c
      · exact le_of_eq hra_eq_xa.symm
      · have hhi_lt_lo := hsub_lt c_a c (Finset.mem_Icc.mp hca_Icc1).1 hlt_c
          (Finset.mem_Icc.mp hc_Icc).2
        have := (Finset.mem_Icc.mp hea_x).2
        have := (Finset.mem_Icc.mp hrc_Fin).1
        omega
    have hrc_Gset : blockRoot subs Bp c ∈ (Gset : Set ℕ) :=
      (hGset _).mpr ⟨c, hc_pK, rfl⟩
    have hrc_Shi : blockRoot subs Bp c ∈ S_hi := by
      have hc_Icc1 : c ∈ Finset.Icc 1 K_X :=
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc_pK).1; omega, (Finset.mem_Icc.mp hc_pK).2⟩
      have hSc_Xhi := (hsub_c c hc_Icc1).2.2.2.2.1
      exact ⟨lt_of_lt_of_le hxa_Shi.1 hxa_le_rc, le_trans (Finset.mem_Icc.mp hrc_Fin).2 hSc_Xhi⟩
    have hc_iff : c ∈ leftSpine G_idag ↔ blockRoot subs Bp c ∈ leftSpine (proc.treeAt idag) := by
      rw [hG_def, leftSpine_map, List.mem_map]
      constructor
      · rintro ⟨w, hw_ls, hw_idx⟩
        have hwG : w ∈ Gset := (mem_of_mem_restrictTree Bp Gset (mem_of_mem_leftSpine hw_ls)).2
        obtain ⟨d, hd_pK, rfl⟩ := (hGset w).mp hwG
        have hd_eq : d = c := (hroots d hd_pK).2.2.2.1.symm.trans hw_idx
        subst hd_eq
        exact ((hls_Bp_iff hxa_le_rc).mp ((hls_resG_iff hxa_le_rc).mp hw_ls).1).1
      · intro hrc_ls_t
        have hrc_ls_Bp : blockRoot subs Bp c ∈ leftSpine Bp :=
          (hls_Bp_iff hxa_le_rc).mpr ⟨hrc_ls_t, hrc_Shi⟩
        exact ⟨blockRoot subs Bp c, (hls_resG_iff hxa_le_rc).mpr ⟨hrc_ls_Bp, hrc_Gset⟩, hrc_idx⟩
    refine ⟨hrc_Fin, hrc_idx, hc_iff, ?_⟩
    intro hc_in z hz_ls hrc_lt_z
    by_contra hle_hi
    have hz_Sc : z ∈ (subblock1 subs c).toFinset :=
      Finset.mem_Icc.mpr ⟨le_trans (Finset.mem_Icc.mp hrc_Fin).1 (le_of_lt hrc_lt_z), by omega⟩
    have hc_Icc1 : c ∈ Finset.Icc 1 K_X :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc_pK).1; omega, (Finset.mem_Icc.mp hc_pK).2⟩
    have hSc_Xhi := (hsub_c c hc_Icc1).2.2.2.2.1
    have hxa_le_z : e_a.x ≤ z := le_trans hxa_le_rc (le_of_lt hrc_lt_z)
    have hz_Shi : z ∈ S_hi := ⟨lt_of_lt_of_le hxa_Shi.1 hxa_le_z, le_trans (by omega) hSc_Xhi⟩
    have hz_ls_Bp : z ∈ leftSpine Bp := (hls_Bp_iff hxa_le_z).mpr ⟨hz_ls, hz_Shi⟩
    have hz_sub_rc : z ∈ subtreeAtKey Bp (blockRoot subs Bp c) :=
      hrc_sub z (mem_of_mem_leftSpine hz_ls_Bp) hz_Sc
    obtain ⟨_, hz_le_rc⟩ :=
      mem_leftSpine_of_leftSpine_in_subtree hBp_bst hz_ls_Bp hrc_Bp hz_sub_rc
    omega
  have hca_in_G : c_a ∈ leftSpine G_idag :=
    (hca_Props c_a (Finset.mem_Icc.mpr ⟨le_rfl, (Finset.mem_Icc.mp hca_Icc).2⟩)).2.2.1.mpr
      (hra_eq_xa.symm ▸ hxa_ls)
  exact ⟨hidag_start, hea_tau,
    ⟨e_a, hea_vXp, hea_lead, hea_rInt, hea_x, hkey_a, hidag_eq, hra_eq_xa, hca_in_G⟩,
    hca_Props⟩

private def upperSpineSet {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ) : Set ℕ :=
  match proc.b1At τ with
  | some b => {v : ℕ | v ∈ leftSpine (proc.treeAt τ) ∧ b ≤ v}
  | none => ∅

private theorem leftSpine_modifyLeftAt_push {t : BinaryTree ℕ} (ht : t.IsBST)
    {b : ℕ} (hb : b ∈ leftSpine t) (w : ℕ) :
    ∀ u, u ∈ leftSpine (modifyLeftAt t b (fun L1 => .node w .nil L1)) ↔
      u = w ∨ (u ∈ leftSpine t ∧ b ≤ u) := by
  induction t with
  | nil => cases hb
  | node k l r ihl _ =>
    obtain ⟨hlt, _, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    intro u
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hb ⊢
    rcases hb with hb_l | rfl
    · have hbk : b < k := hlt' b (mem_of_mem_leftSpine hb_l)
      have hmod : modifyLeftAt (.node k l r) b (fun L1 => .node w .nil L1) =
          .node k (modifyLeftAt l b (fun L1 => .node w .nil L1)) r := by
        simp [modifyLeftAt, hbk]
      rw [hmod]
      simp only [leftSpine, List.mem_append, List.mem_singleton, ihl hl hb_l u]
      constructor
      · rintro ((rfl | ⟨hul, hbu⟩) | rfl)
        · exact Or.inl rfl
        · exact Or.inr ⟨Or.inl hul, hbu⟩
        · exact Or.inr ⟨Or.inr rfl, le_of_lt hbk⟩
      · rintro (rfl | ⟨hul | rfl, hbu⟩)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr ⟨hul, hbu⟩)
        · exact Or.inr rfl
    · have hmod : modifyLeftAt (.node b l r) b (fun L1 => .node w .nil L1) =
          .node b (.node w .nil l) r := by
        simp [modifyLeftAt]
      rw [hmod]
      simp only [leftSpine, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr ⟨Or.inr rfl, le_rfl⟩
      · rintro (rfl | ⟨hul | rfl, hbu⟩)
        · exact Or.inl rfl
        · have := hlt' u (mem_of_mem_leftSpine hul); omega
        · exact Or.inr rfl

private theorem leftSpine_spliceMin_above_second {t : BinaryTree ℕ} (ht : t.IsBST) :
    ∀ {v₁ u : ℕ}, (leftSpine t)[1]? = some v₁ → v₁ ≤ u →
      (u ∈ leftSpine (spliceMin t) ↔ u ∈ leftSpine t) := by
  induction t with
  | nil => intro _ _ h; simp [leftSpine] at h
  | node k l r ihl _ =>
    obtain ⟨hlt, _, hl, _⟩ := (SplayDeque.Direct.isBSTNode_iff k l r).mp ht
    have hlt' := (SplayDeque.Direct.forallTree_iff _ _).mp hlt
    intro v₁ u hv₁ hv₁u
    cases l with
    | nil => simp [leftSpine] at hv₁
    | node lk ll lr =>
      set l₀ := BinaryTree.node lk ll lr
      have hsp : spliceMin (.node k l₀ r) = .node k (spliceMin l₀) r := rfl
      rw [hsp]
      simp only [leftSpine, List.mem_append, List.mem_singleton] at hv₁ ⊢
      have hlen_pos : 1 ≤ (leftSpine l₀).length :=
        leftSpine_nonempty_of_ne_nil (by simp [l₀])
      rcases eq_or_lt_of_le hlen_pos with hlen1 | hlen2
      · -- `(leftSpine l₀).length = 1`, so `ll = .nil` and `v₁ = k`
        have hll_nil : ll = .nil := by
          cases ll with
          | nil => rfl
          | node a b c =>
            have hge := leftSpine_nonempty_of_ne_nil (t := .node a b c) (by simp)
            have hlen_eq : (leftSpine l₀).length = (leftSpine (.node a b c)).length + 1 := by
              simp [l₀, leftSpine]
            omega
        have hv₁_eq : v₁ = k := by
          have hls_l₀ : leftSpine l₀ = [lk] := by simp [l₀, hll_nil, leftSpine]
          rw [hls_l₀] at hv₁
          simpa using hv₁.symm
        subst hv₁_eq
        have hsp_l₀ : spliceMin l₀ = lr := by simp [l₀, hll_nil, spliceMin]
        rw [hsp_l₀]
        have hnot_lr : u ∉ leftSpine lr := by
          intro hu
          have := hlt' u (.right (mem_of_mem_leftSpine hu))
          omega
        have hnot_l₀ : u ∉ leftSpine l₀ := by
          intro hu
          have := hlt' u (mem_of_mem_leftSpine hu)
          omega
        simp [hnot_lr, hnot_l₀]
      · -- `1 < (leftSpine l₀).length`, so `(leftSpine l₀)[1]? = some v₁`
        rw [List.getElem?_append_left hlen2] at hv₁
        rw [ihl hl hv₁ hv₁u]

private theorem rootKey?_eq_getLast?_leftSpine :
    ∀ (t : BinaryTree ℕ), (leftSpine t).getLast? = rootKey? t
  | .nil => rfl
  | .node k l _ => by simp [leftSpine, rootKey?]

private theorem nextOnSpine_spec {xs : List ℕ} (hpw : xs.Pairwise (· < ·)) :
    (∀ {b : ℕ}, b ∈ xs → xs.getLast? ≠ some b → ∃ b', nextOnSpine xs b = some b') ∧
    (∀ {b b' : ℕ}, b ∈ xs → nextOnSpine xs b = some b' →
      b < b' ∧ b' ∈ xs ∧ ∀ u ∈ xs, (b' ≤ u ↔ b < u)) := by
  induction xs with
  | nil =>
    exact ⟨(by intro _ hb; cases hb), (by intro _ _ hb; cases hb)⟩
  | cons a rest ih =>
    rw [List.pairwise_cons] at hpw
    cases rest with
    | nil =>
      refine ⟨fun hb hlast => ?_, fun _ hnext => by simp [nextOnSpine] at hnext⟩
      simp at hb hlast
      exact absurd hb.symm hlast
    | cons c tl =>
      obtain ⟨ih_ex, ih_spec⟩ := ih hpw.2
      refine ⟨?_, ?_⟩
      · intro b hb hlast
        unfold nextOnSpine
        by_cases hab : a = b
        · exact ⟨c, by simp [hab]⟩
        · simp only [hab, ↓reduceIte]
          have hb_rest : b ∈ c :: tl := by
            rcases List.mem_cons.mp hb with rfl | h
            · exact absurd rfl hab
            · exact h
          exact ih_ex hb_rest (by simpa using hlast)
      · intro b b' hb hnext
        unfold nextOnSpine at hnext
        by_cases hab : a = b
        · subst hab
          simp only [↓reduceIte, Option.some.injEq] at hnext
          subst hnext
          have hac : a < c := hpw.1 c List.mem_cons_self
          have hpw_c := (List.pairwise_cons.mp hpw.2).1
          refine ⟨hac, List.mem_cons_of_mem a List.mem_cons_self, fun u hu => ?_⟩
          rcases List.mem_cons.mp hu with rfl | hrest
          · omega
          · rcases List.mem_cons.mp hrest with rfl | htl
            · omega
            · have hcu : c < u := hpw_c u htl
              omega
        · simp only [hab, ↓reduceIte] at hnext
          have hb_rest : b ∈ c :: tl := by
            rcases List.mem_cons.mp hb with rfl | h
            · exact absurd rfl hab
            · exact h
          obtain ⟨hbb', hb'_in, hiff⟩ := ih_spec hb_rest hnext
          have hab_lt : a < b := hpw.1 b hb_rest
          refine ⟨hbb', List.mem_cons_of_mem a hb'_in, fun u hu => ?_⟩
          rcases List.mem_cons.mp hu with rfl | hrest
          · omega
          · exact hiff u hrest

private theorem foldl_rotateRightEdge_leftSpine_above (pairs : List (ℕ × ℕ)) :
    ∀ (t : BinaryTree ℕ) {v : ℕ},
      (∀ p ∈ pairs, p.2 < v) →
      (v ∈ leftSpine (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t) ↔
        v ∈ leftSpine t) := by
  induction pairs with
  | nil => intro _ _ _; exact Iff.rfl
  | cons p rest ih =>
    intro t v hall
    simp only [List.foldl_cons]
    have hp_lt : p.2 < v := hall p List.mem_cons_self
    rw [ih _ (fun q hq => hall q (List.mem_cons_of_mem p hq)),
        mem_leftSpine_rotateRightEdge_iff_of_ne t p.1 p.2 (by omega)]

private theorem upperSpineSet_transition_between {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1
      ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1))
    {τ₁ τ₂ v : ℕ}
    (hτ₁_start : proc.popStepIdx
      (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).lo ≤ τ₁)
    (hτ_le : τ₁ ≤ τ₂)
    (hτ₂_empty : τ₂ < tauEmpty proc
      (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p))
    (hv_gt : (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).hi < v) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    let Sp := subblock1 subs p
    (v ∉ upperSpineSet proc τ₁ → v ∈ upperSpineSet proc τ₂ →
      ∃ τ ∈ Finset.Ico τ₁ τ₂, ∃ s' ∈ Sp.toFinset, ∃ b : ℕ,
        proc.steps[τ]? = some (.pop s') ∧
        proc.b1At τ = some b ∧
        let sub := takeThrough (leftSpine (proc.treeAt τ)) b
        let k := sub.length - 1
        let h := (k - 1) / 2
        k = 2 * h + 2 ∧ sub[2 * h + 1]? = some v) ∧
    (v ∈ upperSpineSet proc τ₁ → v ∉ upperSpineSet proc τ₂ →
      ∃ τ ∈ Finset.Ico τ₁ τ₂,
        (proc.steps[τ]? = some .shift ∧ proc.b1At τ = some v) ∨
        (∃ u, proc.steps[τ]? = some (.upperRot u v))) := by
  dsimp only
  obtain ⟨_, _, _, _, hsmax_le_Sphi, _, _, _, htEmpty_len, _, haw⟩ :=
    active_window_props hValid proc ℓ X hX hp
  set chain := scaleTreePartitionChain T P M
  set subs := childSubblocks (chain ℓ.succ) X
  set Sp := subblock1 subs p
  set tStart := proc.popStepIdx Sp.lo
  set tEmpty := tauEmpty proc Sp
  obtain ⟨hbst_all, _⟩ := proc_tree_bst_and_step_keys proc
  -- Single-step characterization across `τ ↦ τ + 1` with `tStart ≤ τ` and `τ + 1 < tEmpty`
  have step_U : ∀ {τ : ℕ}, tStart ≤ τ → τ + 1 < tEmpty →
      (v ∉ upperSpineSet proc τ → v ∈ upperSpineSet proc (τ + 1) →
        ∃ s' ∈ Sp.toFinset, ∃ b : ℕ,
          proc.steps[τ]? = some (.pop s') ∧
          proc.b1At τ = some b ∧
          let sub := takeThrough (leftSpine (proc.treeAt τ)) b
          let k := sub.length - 1
          let h := (k - 1) / 2
          k = 2 * h + 2 ∧ sub[2 * h + 1]? = some v) ∧
      (v ∈ upperSpineSet proc τ → v ∉ upperSpineSet proc (τ + 1) →
        (proc.steps[τ]? = some .shift ∧ proc.b1At τ = some v) ∨
        (∃ u, proc.steps[τ]? = some (.upperRot u v))) := by
    intro τ hτ_s hτ1_e
    have hτ_e : τ < tEmpty := by omega
    have hτ_len : τ < proc.steps.length := lt_of_lt_of_le hτ_e htEmpty_len
    have hτ1_len : τ + 1 ≤ proc.steps.length := le_of_lt (lt_of_lt_of_le hτ1_e htEmpty_len)
    obtain ⟨_, ht_ne, _, hpush_lt, hpop_Sp⟩ := haw τ hτ_s hτ_e
    obtain ⟨_, ht1_ne, _, _, _⟩ := haw (τ + 1) (by omega) hτ1_e
    obtain ⟨_, bNext, hbNext_eq, _⟩ := proc_b1At_of_ne_nil proc hτ1_len ht1_ne
    obtain ⟨ht_bst, _⟩ := hbst_all τ (le_of_lt hτ_len)
    have hpw_ls : (leftSpine (proc.treeAt τ)).Pairwise (· < ·) := leftSpine_pairwise_lt ht_bst
    obtain ⟨hval, hst⟩ := proc_step_at proc hτ_len
    have ht_st : (proc.stateAt τ).1 = proc.treeAt τ := rfl
    have ht1_eq : proc.treeAt (τ + 1) = ((proc.steps[τ]'hτ_len).step (proc.stateAt τ)).1 :=
      congrArg Prod.fst hst
    have hb1_next : proc.b1At (τ + 1) = ((proc.steps[τ]'hτ_len).step (proc.stateAt τ)).2 :=
      congrArg Prod.snd hst
    have hop_some : ∀ op, proc.steps[τ]'hτ_len = op → proc.steps[τ]? = some op :=
      fun op h => (List.getElem?_eq_getElem hτ_len).trans (congrArg some h)
    cases hop : proc.steps[τ]'hτ_len with
    | push w =>
      have hw_lt : w < v := lt_of_lt_of_le (hpush_lt w (hop_some _ hop))
        (le_trans hsmax_le_Sphi (le_of_lt hv_gt))
      rw [hop] at hval ht1_eq hb1_next
      rcases hval with ⟨_, _, _, hnil_iff, hb_ls⟩
      cases hb : (proc.stateAt τ).2 with
      | none => exact absurd (hnil_iff.mpr hb) ht_ne
      | some b =>
        have hb_eq : proc.b1At τ = some b := hb
        have hb_in_ls : b ∈ leftSpine (proc.treeAt τ) := hb_ls b hb
        unfold FoldedOp.step at ht1_eq hb1_next
        rw [hb, ht_st] at ht1_eq hb1_next
        dsimp only at ht1_eq hb1_next
        have hU_same : v ∈ upperSpineSet proc (τ + 1) ↔ v ∈ upperSpineSet proc τ := by
          unfold upperSpineSet
          rw [hb1_next, hb_eq, ht1_eq]
          change v ∈ leftSpine (modifyLeftAt (proc.treeAt τ) b (fun L1 => .node w .nil L1)) ∧ w ≤ v ↔
            v ∈ leftSpine (proc.treeAt τ) ∧ b ≤ v
          rw [leftSpine_modifyLeftAt_push ht_bst hb_in_ls w v]
          constructor
          · rintro ⟨rfl | ⟨h1, h2⟩, _⟩
            · omega
            · exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨Or.inr ⟨h1, h2⟩, le_of_lt hw_lt⟩
        exact ⟨fun h1 h2 => absurd (hU_same.mp h2) h1, fun h1 h2 => absurd (hU_same.mpr h1) h2⟩
    | shift =>
      rw [hop] at hval ht1_eq hb1_next
      rcases hval with ⟨b, hb, hb_in_ls, hnot_root⟩
      have hb_eq : proc.b1At τ = some b := hb
      unfold FoldedOp.step at ht1_eq hb1_next
      rw [hb, ht_st] at ht1_eq hb1_next
      dsimp only at ht1_eq hb1_next
      have hnext_some : nextOnSpine (leftSpine (proc.treeAt τ)) b = some bNext :=
        hb1_next.symm.trans hbNext_eq
      obtain ⟨_, _, hiff_next⟩ := (nextOnSpine_spec hpw_ls).2 hb_in_ls hnext_some
      have hU_iff : v ∈ upperSpineSet proc (τ + 1) ↔ v ∈ upperSpineSet proc τ ∧ v ≠ b := by
        unfold upperSpineSet
        rw [hbNext_eq, hb_eq, ht1_eq]
        change v ∈ leftSpine (proc.treeAt τ) ∧ bNext ≤ v ↔
          (v ∈ leftSpine (proc.treeAt τ) ∧ b ≤ v) ∧ v ≠ b
        constructor
        · rintro ⟨hv_ls, hbn_le⟩
          have hbv : b < v := (hiff_next v hv_ls).mp hbn_le
          exact ⟨⟨hv_ls, le_of_lt hbv⟩, by omega⟩
        · rintro ⟨⟨hv_ls, hbv⟩, hne⟩
          exact ⟨hv_ls, (hiff_next v hv_ls).mpr (by omega)⟩
      refine ⟨fun h1 h2 => absurd (hU_iff.mp h2).1 h1, fun h1 h2 => ?_⟩
      have hvb : v = b := by by_contra hne; exact h2 (hU_iff.mpr ⟨h1, hne⟩)
      subst hvb
      exact Or.inl ⟨hop_some _ hop, hb_eq⟩
    | upperRot u₀ v₀ =>
      rw [hop] at hval ht1_eq hb1_next
      rcases hval with ⟨b, _, hb, _, _, _, _, _, _, hv₀_ls, hedge⟩
      have hb_eq : proc.b1At τ = some b := hb
      unfold FoldedOp.step at ht1_eq hb1_next
      rw [ht_st] at ht1_eq
      dsimp only at ht1_eq hb1_next
      have hb1_eq' : proc.b1At (τ + 1) = some b := hb1_next.trans hb
      have hv₀_not : v₀ ∉ leftSpine (rotateRightEdge (proc.treeAt τ) u₀ v₀) :=
        (rotateRightEdge_leftSpine_props ht_bst hv₀_ls hedge).1
      have hU_iff : v ∈ upperSpineSet proc (τ + 1) ↔ v ∈ upperSpineSet proc τ ∧ v ≠ v₀ := by
        unfold upperSpineSet
        rw [hb1_eq', hb_eq, ht1_eq]
        change v ∈ leftSpine (rotateRightEdge (proc.treeAt τ) u₀ v₀) ∧ b ≤ v ↔
          (v ∈ leftSpine (proc.treeAt τ) ∧ b ≤ v) ∧ v ≠ v₀
        by_cases hvv₀ : v = v₀
        · subst hvv₀; simp [hv₀_not]
        · rw [mem_leftSpine_rotateRightEdge_iff_of_ne _ u₀ v₀ hvv₀]
          exact ⟨fun h => ⟨h, hvv₀⟩, fun h => h.1⟩
      refine ⟨fun h1 h2 => absurd (hU_iff.mp h2).1 h1, fun h1 h2 => ?_⟩
      have hvv₀ : v = v₀ := by by_contra hne; exact h2 (hU_iff.mpr ⟨h1, hne⟩)
      subst hvv₀
      exact Or.inr ⟨u₀, hop_some _ hop⟩
    | pop s' =>
      obtain ⟨hs'_Sp, hs'_le_smax⟩ := hpop_Sp s' (hop_some _ hop)
      have hs'_lt_v : s' < v := lt_of_le_of_lt (le_trans hs'_le_smax hsmax_le_Sphi) hv_gt
      rw [hop] at hval ht1_eq hb1_next
      rcases hval with ⟨b, _, hmin_s', hb, hb_in_ls⟩
      have hb_eq : proc.b1At τ = some b := hb
      obtain ⟨_, _, hs'_hd, _, _⟩ := (minKey_bst_props ht_bst).2 s' hmin_s'
      obtain ⟨hsub_pref, hsub_ne, hpw_sub, hsub_hd, hsub_last, hmem_sub⟩ :=
        takeThrough_props hpw_ls hb_in_ls
      set ls := leftSpine (proc.treeAt τ)
      set sub := takeThrough ls b
      set k := sub.length - 1
      set h := (k - 1) / 2
      unfold FoldedOp.step at ht1_eq hb1_next
      rw [hb, ht_st] at ht1_eq hb1_next
      dsimp only at ht1_eq hb1_next
      by_cases hk0 : (takeThrough (leftSpine (proc.treeAt τ)) b).length - 1 = 0
      · -- `k = 0`, so `sub = [s']`, `b = s'`, `tNew = spliceMin (treeAt τ) ≠ .nil`
        simp only [hk0, ↓reduceIte] at ht1_eq hb1_next
        have hk0' : k = 0 := hk0
        have hsub_len1 : sub.length = 1 := by
          have : 1 ≤ sub.length := List.length_pos_of_ne_nil hsub_ne
          omega
        have hbs' : b = s' := by
          have h0 : sub[0]? = some s' := by rw [← List.head?_eq_getElem?, hsub_hd]; exact hs'_hd
          have h1 : sub[0]? = some b := by
            have := @List.getLast?_eq_getElem? _ sub
            rw [hsub_last, hsub_len1] at this
            exact this.symm
          rw [h0] at h1; injection h1 with h_eq; exact h_eq.symm
        subst hbs'
        have ht0_ne : spliceMin (proc.treeAt τ) ≠ .nil := ht1_eq ▸ ht1_ne
        simp only [ht0_ne, ↓reduceIte] at hb1_next
        have hnext_some : nextOnSpine ls b = some bNext := hb1_next.symm.trans hbNext_eq
        obtain ⟨_, _, hiff_next⟩ := (nextOnSpine_spec hpw_ls).2 hb_in_ls hnext_some
        -- Since `ls.head? = some b` and `nextOnSpine ls b = some bNext`, `ls[1]? = some bNext`!
        have hls1 : ls[1]? = some bNext := by
          cases hls_eq : ls with
          | nil => rw [hls_eq] at hs'_hd; simp at hs'_hd
          | cons a rest =>
            rw [hls_eq] at hs'_hd hnext_some
            simp only [List.head?_cons, Option.some.injEq] at hs'_hd
            subst hs'_hd
            cases rest with
            | nil => simp [nextOnSpine] at hnext_some
            | cons c tl =>
              simp only [nextOnSpine, ↓reduceIte, Option.some.injEq] at hnext_some
              subst hnext_some
              rfl
        have hU_same : v ∈ upperSpineSet proc (τ + 1) ↔ v ∈ upperSpineSet proc τ := by
          unfold upperSpineSet
          rw [hbNext_eq, hb_eq, ht1_eq]
          change v ∈ leftSpine (spliceMin (proc.treeAt τ)) ∧ bNext ≤ v ↔ v ∈ ls ∧ b ≤ v
          constructor
          · rintro ⟨hv_sp, hbn_le⟩
            have hv_ls : v ∈ ls :=
              (leftSpine_spliceMin_above_second ht_bst hls1 hbn_le).mp hv_sp
            exact ⟨hv_ls, le_of_lt ((hiff_next v hv_ls).mp hbn_le)⟩
          · rintro ⟨hv_ls, _⟩
            have hbn_le : bNext ≤ v := (hiff_next v hv_ls).mpr hs'_lt_v
            exact ⟨(leftSpine_spliceMin_above_second ht_bst hls1 hbn_le).mpr hv_ls, hbn_le⟩
        exact ⟨fun h1 h2 => absurd (hU_same.mp h2) h1, fun h1 h2 => absurd (hU_same.mpr h1) h2⟩
      · -- `k ≥ 1`: unify `k = 2 * h + 1` and `k = 2 * h + 2` via `w_new = sub[2 * h + 1]`!
        simp only [hk0, ↓reduceIte] at ht1_eq hb1_next
        have hk0' : k ≠ 0 := hk0
        have hk_ge1 : 1 ≤ k := by omega
        have hsub_len : sub.length = k + 1 := by
          have : 1 ≤ sub.length := List.length_pos_of_ne_nil hsub_ne
          omega
        have hk_cases : k = 2 * h + 1 ∨ k = 2 * h + 2 := by dsimp [h]; omega
        have hw_lt_len : 2 * h + 1 < sub.length := by omega
        set w_new := sub[2 * h + 1]'hw_lt_len
        have hsub_k_b : sub[k]'(by omega) = b := by
          have hlast_get := @List.getLast?_eq_getElem? _ sub
          rw [hsub_last, show sub.length - 1 = k from rfl,
              List.getElem?_eq_getElem (by omega)] at hlast_get
          injection hlast_get with h_eq
          exact h_eq.symm
        have hb1_wnew : proc.b1At (τ + 1) = some w_new := by
          rw [hb1_next]
          change (if k = 2 * h + 2 then sub[2 * h + 1]? else some b) = some w_new
          rcases hk_cases with hk_odd | hk_even
          · have hnot : ¬ (k = 2 * h + 2) := by omega
            simp only [hnot, ↓reduceIte, Option.some.injEq]
            rw [← hsub_k_b]
            simp [w_new, hk_odd]
          · simp [hk_even, List.getElem?_eq_getElem hw_lt_len, w_new]
        have h1_lt_len : 1 < sub.length := by omega
        have hls1 : ls[1]? = some (sub[1]'h1_lt_len) := by
          rcases hsub_pref with ⟨tl, hls_eq⟩
          rw [← hls_eq, List.getElem?_append_left h1_lt_len, List.getElem?_eq_getElem h1_lt_len]
        have hv1_le_w : sub[1]'h1_lt_len ≤ w_new := by
          rcases eq_or_lt_of_le (show 1 ≤ 2 * h + 1 by omega) with heq | hlt
          · simp [w_new, ← heq]
          · exact le_of_lt (List.pairwise_iff_getElem.mp hpw_sub 1 (2 * h + 1) h1_lt_len hw_lt_len hlt)
        set pairs := (adjacentPairs sub.tail).take h
        have hpairs_lt_w : ∀ p ∈ pairs, p.2 < w_new := by
          intro p hp
          obtain ⟨idx, hidx_len, hp_eq⟩ := List.getElem_of_mem hp
          have htail_len : sub.tail.length = k := by simp [hsub_len]
          have hp_len_ge : h ≤ (adjacentPairs sub.tail).length :=
            adjacentPairs_length_ge sub.tail h (by omega)
          have hidx_lt_h : idx < h := by
            rw [List.length_take_of_le hp_len_ge] at hidx_len; exact hidx_len
          have hp_get : pairs[idx]'hidx_len =
              (sub[2 * idx + 1]'(by omega), sub[2 * idx + 2]'(by omega)) := by
            have h1 : pairs[idx]'hidx_len =
                (adjacentPairs sub.tail)[idx]'(lt_of_lt_of_le hidx_lt_h hp_len_ge) :=
              List.getElem_take
            have h2 := adjacentPairs_getElem? sub.tail idx (by omega)
            rw [List.getElem?_eq_getElem (lt_of_lt_of_le hidx_lt_h hp_len_ge)] at h2
            injection h2 with h2_eq
            simp only [List.getElem_tail] at h2_eq
            exact h1.trans h2_eq
          rw [← hp_eq, hp_get]
          exact List.pairwise_iff_getElem.mp hpw_sub (2 * idx + 2) (2 * h + 1)
            (by omega) hw_lt_len (by omega)
        have hU_next_iff : v ∈ upperSpineSet proc (τ + 1) ↔ v ∈ ls ∧ w_new ≤ v := by
          unfold upperSpineSet
          rw [hb1_wnew, ht1_eq]
          change v ∈ leftSpine (pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2)
            (spliceMin (proc.treeAt τ))) ∧ w_new ≤ v ↔ v ∈ ls ∧ w_new ≤ v
          constructor
          · rintro ⟨hv_f, hw_le⟩
            have hv_sp := (foldl_rotateRightEdge_leftSpine_above pairs _
              (fun p hp => lt_of_lt_of_le (hpairs_lt_w p hp) hw_le)).mp hv_f
            have hv_ls := (leftSpine_spliceMin_above_second ht_bst hls1
              (le_trans hv1_le_w hw_le)).mp hv_sp
            exact ⟨hv_ls, hw_le⟩
          · rintro ⟨hv_ls, hw_le⟩
            have hv_sp := (leftSpine_spliceMin_above_second ht_bst hls1
              (le_trans hv1_le_w hw_le)).mpr hv_ls
            exact ⟨(foldl_rotateRightEdge_leftSpine_above pairs _
              (fun p hp => lt_of_lt_of_le (hpairs_lt_w p hp) hw_le)).mpr hv_sp, hw_le⟩
        have hw_le_b : w_new ≤ b := by
          rw [← hsub_k_b]
          rcases eq_or_lt_of_le (show 2 * h + 1 ≤ k by omega) with heq | hlt
          · simp [w_new, heq]
          · exact le_of_lt (List.pairwise_iff_getElem.mp hpw_sub (2 * h + 1) k hw_lt_len (by omega) hlt)
        refine ⟨?_, ?_⟩
        · intro hv_not hv_in1
          obtain ⟨hv_ls, hw_le_v⟩ := hU_next_iff.mp hv_in1
          have hv_lt_b : v < b := by
            by_contra hge
            have hv_U : v ∈ upperSpineSet proc τ := by
              unfold upperSpineSet; rw [hb_eq]; exact ⟨hv_ls, Nat.le_of_not_lt hge⟩
            exact hv_not hv_U
          have hv_in_sub : v ∈ sub := (hmem_sub v).mpr ⟨hv_ls, le_of_lt hv_lt_b⟩
          obtain ⟨iv, hiv_lt, rfl⟩ := List.getElem_of_mem hv_in_sub
          rw [← hsub_k_b] at hv_lt_b
          have hiv_lt_k : iv < k := by
            by_contra hge
            rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
            · exact lt_irrefl _ hv_lt_b
            · exact lt_asymm hv_lt_b (List.pairwise_iff_getElem.mp hpw_sub k iv (by omega) hiv_lt hgt)
          have hw_le_iv : 2 * h + 1 ≤ iv := by
            by_contra hlt
            have hlt' := List.pairwise_iff_getElem.mp hpw_sub iv (2 * h + 1) hiv_lt hw_lt_len (by omega)
            change sub[iv] < w_new at hlt'
            omega
          have hk_even : k = 2 * h + 2 := by omega
          have hiv_eq : iv = 2 * h + 1 := by omega
          subst hiv_eq
          exact ⟨s', hs'_Sp, b, hop_some _ hop, hb_eq, hk_even,
            List.getElem?_eq_getElem hw_lt_len⟩
        · intro hv_in hv_not1
          unfold upperSpineSet at hv_in
          rw [hb_eq] at hv_in
          obtain ⟨hv_ls, hb_le_v⟩ := hv_in
          exact absurd (hU_next_iff.mpr ⟨hv_ls, le_trans hw_le_b hb_le_v⟩) hv_not1
  -- Induct on `d := τ₂ - τ₁`
  obtain ⟨d, rfl⟩ : ∃ d, τ₂ = τ₁ + d := ⟨τ₂ - τ₁, by omega⟩
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    exact ⟨fun h1 h2 => absurd h2 h1, fun h1 h2 => absurd h1 h2⟩
  | succ d ihd =>
    set τ := τ₁ + d
    have hτ_s : tStart ≤ τ := by omega
    have hτ1_e : τ + 1 < tEmpty := by omega
    obtain ⟨ih_gain, ih_loss⟩ := ihd (by omega) (by omega)
    obtain ⟨hstep_gain, hstep_loss⟩ := step_U hτ_s hτ1_e
    refine ⟨?_, ?_⟩
    · intro hv_not1 hv_in_succ
      by_cases hv_τ : v ∈ upperSpineSet proc τ
      · obtain ⟨τ', hτ'_Ico, rest⟩ := ih_gain hv_not1 hv_τ
        exact ⟨τ', Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hτ'_Ico).1,
          lt_trans (Finset.mem_Ico.mp hτ'_Ico).2 (Nat.lt_succ_self _)⟩, rest⟩
      · exact ⟨τ, Finset.mem_Ico.mpr ⟨by omega, Nat.lt_succ_self _⟩, hstep_gain hv_τ hv_in_succ⟩
    · intro hv_in1 hv_not_succ
      by_cases hv_τ : v ∈ upperSpineSet proc τ
      · exact ⟨τ, Finset.mem_Ico.mpr ⟨by omega, Nat.lt_succ_self _⟩, hstep_loss hv_τ hv_not_succ⟩
      · obtain ⟨τ', hτ'_Ico, rest⟩ := ih_loss hv_in1 hv_τ
        exact ⟨τ', Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hτ'_Ico).1,
          lt_trans (Finset.mem_Ico.mp hτ'_Ico).2 (Nat.lt_succ_self _)⟩, rest⟩

/-! ## Section 5: Gap-Witness Sets and Proof of Lemma 5.8 (`lem_5_8_b3_gaps`) -/

private theorem pin_witness_coords {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p c u v : ℕ}
    (hp : p ∈ Finset.Icc 1 ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1))
    (hc : c ∈ Finset.Icc (p + 1) (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length)
    (hu : u ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).toFinset)
    (hv : v ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c).toFinset) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    partSepScale P chain u v = ℓ.val + 1 ∧
    blockAt (chain ℓ.castSucc) v = X ∧
    subblockIndex1 subs u = p ∧
    subblockIndex1 subs v = c := by
  dsimp only
  have hChain := validScaleTree_chain hValid
  obtain ⟨hX1, _, hXP, _, hsub_c, hsub_lt, _, _, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨hp1, hp_sub1⟩ := Finset.mem_Icc.mp hp
  obtain ⟨hcp1, hc_le⟩ := Finset.mem_Icc.mp hc
  have hp_Icc : p ∈ Finset.Icc 1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length :=
    Finset.mem_Icc.mpr ⟨hp1, by omega⟩
  have hc_Icc : c ∈ Finset.Icc 1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length :=
    Finset.mem_Icc.mpr ⟨by omega, hc_le⟩
  obtain ⟨_, _, hSp_Xlo, _, hSp_Xhi, hSp_w⟩ := hsub_c p hp_Icc
  obtain ⟨_, _, hSc_Xlo, _, hSc_Xhi, hSc_w⟩ := hsub_c c hc_Icc
  obtain ⟨hidx_u, hblk_u_succ, hblk_u_cast⟩ := hSp_w u hu
  obtain ⟨hidx_v, hblk_v_succ, hblk_v_cast⟩ := hSc_w v hv
  have hu_Icc : u ∈ Finset.Icc 1 P :=
    Finset.mem_Icc.mpr ⟨le_trans hX1 (le_trans hSp_Xlo (Finset.mem_Icc.mp hu).1),
      le_trans (Finset.mem_Icc.mp hu).2 (le_trans hSp_Xhi hXP)⟩
  have hv_Icc : v ∈ Finset.Icc 1 P :=
    Finset.mem_Icc.mpr ⟨le_trans hX1 (le_trans hSc_Xlo (Finset.mem_Icc.mp hv).1),
      le_trans (Finset.mem_Icc.mp hv).2 (le_trans hSc_Xhi hXP)⟩
  have hlt_sub : (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).hi <
      (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c).lo :=
    hsub_lt p c hp1 (by omega) hc_le
  have hne_succ : blockAt (scaleTreePartitionChain T P M ℓ.succ) u ≠
      blockAt (scaleTreePartitionChain T P M ℓ.succ) v := by
    rw [hblk_u_succ, hblk_v_succ]
    intro heq
    rw [heq] at hlt_sub
    have hle := (hsub_c c hc_Icc).2.2.2.1
    omega
  have hsep : partSepScale P (scaleTreePartitionChain T P M) u v = ℓ.val + 1 :=
    ((partSepScale_props hChain hu_Icc hv_Icc).2.2.2 ℓ).1.mpr
      ⟨hblk_u_cast.trans hblk_v_cast.symm, hne_succ⟩
  exact ⟨hsep, hblk_v_cast, hidx_u, hidx_v⟩

private theorem pin_witness_coords_eq {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T)
    {ℓ₁ ℓ₂ : Fin M} {X₁ X₂ : IntervalBlock} {p₁ p₂ c₁ c₂ u v : ℕ}
    (hX₁ : X₁ ∈ scaleTreePartitionChain T P M ℓ₁.castSucc)
    (hX₂ : X₂ ∈ scaleTreePartitionChain T P M ℓ₂.castSucc)
    (hp₁ : p₁ ∈ Finset.Icc 1 ((childSubblocks (scaleTreePartitionChain T P M ℓ₁.succ) X₁).length - 1))
    (hp₂ : p₂ ∈ Finset.Icc 1 ((childSubblocks (scaleTreePartitionChain T P M ℓ₂.succ) X₂).length - 1))
    (hc₁ : c₁ ∈ Finset.Icc (p₁ + 1) (childSubblocks (scaleTreePartitionChain T P M ℓ₁.succ) X₁).length)
    (hc₂ : c₂ ∈ Finset.Icc (p₂ + 1) (childSubblocks (scaleTreePartitionChain T P M ℓ₂.succ) X₂).length)
    (hu₁ : u ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ₁.succ) X₁) p₁).toFinset)
    (hu₂ : u ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ₂.succ) X₂) p₂).toFinset)
    (hv₁ : v ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ₁.succ) X₁) c₁).toFinset)
    (hv₂ : v ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ₂.succ) X₂) c₂).toFinset) :
    (ℓ₁, X₁, p₁, c₁) = (ℓ₂, X₂, p₂, c₂) := by
  obtain ⟨hsep1, hX1_eq, hp1_eq, hc1_eq⟩ := pin_witness_coords hValid ℓ₁ X₁ hX₁ hp₁ hc₁ hu₁ hv₁
  obtain ⟨hsep2, hX2_eq, hp2_eq, hc2_eq⟩ := pin_witness_coords hValid ℓ₂ X₂ hX₂ hp₂ hc₂ hu₂ hv₂
  have hℓ_eq : ℓ₁ = ℓ₂ := Fin.ext (by omega)
  subst hℓ_eq
  have hX_eq : X₁ = X₂ := hX1_eq.symm.trans hX2_eq
  subst hX_eq
  have hp_eq : p₁ = p₂ := hp1_eq.symm.trans hp2_eq
  subst hp_eq
  have hc_eq : c₁ = c₂ := hc1_eq.symm.trans hc2_eq
  subst hc_eq
  rfl

private theorem b2_even_mem_s1_or_leafPre {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p c : ℕ}
    (hp : p ∈ Finset.Icc 1 ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1))
    (hc : c ∈ Finset.Icc (p + 1) (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length)
    {e : InternalPopRot} (he_rInt : e ∈ proc.rInt)
    (hes : e.s ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).toFinset)
    (hex : e.x ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c).toFinset)
    (hey : e.y ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c).toFinset)
    (hz : (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c).hi < e.z) :
    let chain := scaleTreePartitionChain T P M
    e ∈ s1Set P T proc chain ∪ bLeafPre P proc chain := by
  dsimp only
  have hChain := validScaleTree_chain hValid
  obtain ⟨hsep_sx, _, _, _⟩ := pin_witness_coords hValid ℓ X hX hp hc hes hex
  obtain ⟨_, _, _, _, hsub_c, hsub_lt, _, _, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨hrInt_basic, _⟩ := rInt_basic_and_order proc
  obtain ⟨_, _, hs1, hsx, hxy, hyz, hzP⟩ := hrInt_basic e he_rInt
  have hex_Icc : e.x ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hey_Icc : e.y ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨hp1, _⟩ := Finset.mem_Icc.mp hp
  obtain ⟨hcp1, hc_le⟩ := Finset.mem_Icc.mp hc
  have hc_Icc : c ∈ Finset.Icc 1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length :=
    Finset.mem_Icc.mpr ⟨by omega, hc_le⟩
  obtain ⟨_, _, _, _, _, hSc_w⟩ := hsub_c c hc_Icc
  have hbx : blockAt (scaleTreePartitionChain T P M ℓ.succ) e.x =
      subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c := (hSc_w e.x hex).2.1
  have hby : blockAt (scaleTreePartitionChain T P M ℓ.succ) e.y =
      subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c := (hSc_w e.y hey).2.1
  have hsep_xy_props := partSepScale_props hChain hex_Icc hey_Icc
  have hsep_xy_gt : ℓ.val + 1 < partSepScale P (scaleTreePartitionChain T P M) e.x e.y :=
    ((hsep_xy_props.2.2.2 ℓ).2).mpr (hbx.trans hby.symm)
  have hsep_xy_le : partSepScale P (scaleTreePartitionChain T P M) e.x e.y ≤ M + 1 :=
    hsep_xy_props.2.1
  by_cases hlast : partSepScale P (scaleTreePartitionChain T P M) e.x e.y = M + 1
  · refine Finset.mem_union_right _ ?_
    unfold bLeafPre
    rw [Finset.mem_filter]
    refine ⟨he_rInt, hlast, ?_⟩
    have hcoarse := (chain_blockAt_coarse hChain (Fin.le_last ℓ.succ) hex_Icc).1
    rw [hbx] at hcoarse
    have hlt_pc := hsub_lt p c hp1 (by omega) hc_le
    have hes_hi := (Finset.mem_Icc.mp hes).2
    omega
  · refine Finset.mem_union_left _ ?_
    have hsep_xy_M : partSepScale P (scaleTreePartitionChain T P M) e.x e.y ≤ M := by omega
    have hb1 : e ∈ b1 P proc (scaleTreePartitionChain T P M) := by
      unfold b1
      rw [Finset.mem_filter]
      exact ⟨he_rInt, by omega, by omega, hsep_xy_M⟩
    unfold s1Set
    rw [Finset.mem_filter]
    refine ⟨hb1, ?_⟩
    dsimp only
    set m := mEnd T (lcaScaleTree T
      (partSepScale P (scaleTreePartitionChain T P M) e.s e.x)
      (partSepScale P (scaleTreePartitionChain T P M) e.x e.y))
    split_ifs with hm
    left
    have hm_ge : ℓ.val + 1 ≤ m := by
      dsimp [m]
      rw [hsep_sx]
      exact lcaScaleTree_mEnd_ge hValid.2.1 (by omega) (by have := ℓ.isLt; omega) _
    have hfin_le : ℓ.succ ≤ (⟨m, Nat.lt_succ_of_le hm⟩ : Fin (M + 1)) :=
      Fin.mk_le_mk.mpr hm_ge
    have hhi_le := (chain_blockAt_coarse hChain hfin_le hey_Icc).2
    rw [hby] at hhi_le
    exact lt_of_le_of_lt hhi_le hz

private def isWitA1 {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p c : ℕ) : Prop :=
  let subs := childSubblocks (chain ℓ.succ) X
  ∃ τ < proc.steps.length, ∃ m₀ ∈ (subblock1 subs p).toFinset, ∃ u v : ℕ,
    (proc.treeAt τ).minKey? = some m₀ ∧
    proc.steps[τ]? = some (.upperRot u v) ∧
    v ∈ (subblock1 subs c).toFinset

private def isWitA2 {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p c : ℕ) : Prop :=
  let subs := childSubblocks (chain ℓ.succ) X
  ∃ e ∈ b3Intra P proc chain,
    e.s ∈ (subblock1 subs p).toFinset ∧ e.y ∈ (subblock1 subs c).toFinset

private def isWitB1 {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p c : ℕ) : Prop :=
  let subs := childSubblocks (chain ℓ.succ) X
  ∃ e ∈ b3Intra P proc chain,
    e.s ∈ (subblock1 subs p).toFinset ∧ e.x ∈ (subblock1 subs c).toFinset

private def isWitB2 {M : ℕ} (P : ℕ) (T : ScaleTree) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p c : ℕ) : Prop :=
  let subs := childSubblocks (chain ℓ.succ) X
  ∃ e ∈ s1Set P T proc chain ∪ bLeafPre P proc chain,
    e.s ∈ (subblock1 subs p).toFinset ∧ e.y ∈ (subblock1 subs c).toFinset

private def isWitC1 {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p c : ℕ) : Prop :=
  let subs := childSubblocks (chain ℓ.succ) X
  ∃ s' ∈ Finset.Icc 1 P, ∃ b v : ℕ,
    s' ∈ (subblock1 subs p).toFinset ∧
    v ∈ (subblock1 subs c).toFinset ∧
    proc.b1At (proc.popStepIdx s') = some b ∧
    let sub := takeThrough (leftSpine (proc.treeAt (proc.popStepIdx s'))) b
    let k := sub.length - 1
    let h := (k - 1) / 2
    k = 2 * h + 2 ∧ sub[2 * h + 1]? = some v

private def isWitC2 {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p c : ℕ) : Prop :=
  let subs := childSubblocks (chain ℓ.succ) X
  ∃ τ < proc.steps.length, ∃ m₀ ∈ (subblock1 subs p).toFinset, ∃ v ∈ (subblock1 subs c).toFinset,
    (proc.treeAt τ).minKey? = some m₀ ∧
    ((proc.steps[τ]? = some .shift ∧ proc.b1At τ = some v) ∨
      (∃ u, proc.steps[τ]? = some (.upperRot u v)))

private noncomputable def gapWitnessSet {M : ℕ} (P : ℕ) (T : ScaleTree) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : Fin M) (X : IntervalBlock) (p : ℕ) :
    Finset ℕ :=
  open Classical in
  let ℓ_val := ℓ.val + 1
  let subs := childSubblocks (chain ℓ.succ) X
  if X ∈ chain ℓ.castSucc ∧ p ∈ Finset.Icc 1 (subs.length - 1) then
    let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
    let pi0 := leftSpine G₀
    let Fp := promotedSubblockIndices P proc chain ℓ_val X p
    (pi0.toFinset \ Fp).filter (fun c =>
      isWitA1 P proc chain ℓ X p c ∨
      isWitA2 P proc chain ℓ X p c ∨
      isWitB1 P proc chain ℓ X p c ∨
      isWitB2 P T proc chain ℓ X p c ∨
      isWitC1 P proc chain ℓ X p c ∨
      isWitC2 P proc chain ℓ X p c)
  else ∅

private theorem same_scale_intra_or_vXp {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p c₁ c₂ : ℕ}
    (hp : p ∈ Finset.Icc 1 ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1))
    (hc₁ : c₁ ∈ Finset.Icc (p + 1) (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length)
    (hc₂ : c₂ ∈ Finset.Icc (c₁ + 1) (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length)
    {e : InternalPopRot} (he_rInt : e ∈ proc.rInt)
    (hes : e.s ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p).toFinset)
    (he_tau : e.stepIdx < tauEmpty proc (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p))
    (hex : e.x ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c₁).toFinset)
    (hey : e.y ∈ (subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c₂).toFinset) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    (e.z ≤ (subblock1 subs c₂).hi → e ∈ b3Intra P proc chain) ∧
    ((subblock1 subs c₂).hi < e.z →
      e ∈ vXp P proc chain (ℓ.val + 1) X p ∧
      c₁ ∈ promotedSubblockIndices P proc chain (ℓ.val + 1) X p) := by
  dsimp only
  have hChain := validScaleTree_chain hValid
  obtain ⟨hX1, _, hXP, _, hsub_c, hsub_lt, _, _, _⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨hp1, _⟩ := Finset.mem_Icc.mp hp
  obtain ⟨hc1_lo, hc1_hi⟩ := Finset.mem_Icc.mp hc₁
  obtain ⟨hc2_lo, hc2_hi⟩ := Finset.mem_Icc.mp hc₂
  obtain ⟨hsep_sx, _, _, _⟩ := pin_witness_coords hValid ℓ X hX hp hc₁ hes hex
  have hp_Icc : p ∈ Finset.Icc 1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length :=
    Finset.mem_Icc.mpr ⟨hp1, by omega⟩
  have hc1_Icc : c₁ ∈ Finset.Icc 1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length :=
    Finset.mem_Icc.mpr ⟨by omega, hc1_hi⟩
  have hc2_Icc : c₂ ∈ Finset.Icc 1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length :=
    Finset.mem_Icc.mpr ⟨by omega, hc2_hi⟩
  obtain ⟨_, _, _, _, _, hSp_w⟩ := hsub_c p hp_Icc
  obtain ⟨_, _, hSc1_Xlo, _, hSc1_Xhi, hSc1_w⟩ := hsub_c c₁ hc1_Icc
  obtain ⟨_, _, hSc2_Xlo, hSc2_lohi, hSc2_Xhi, hSc2_w⟩ := hsub_c c₂ hc2_Icc
  have hbp : blockAt (scaleTreePartitionChain T P M ℓ.succ) e.s =
      subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) p := (hSp_w e.s hes).2.1
  have hbx_succ : blockAt (scaleTreePartitionChain T P M ℓ.succ) e.x =
      subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c₁ := (hSc1_w e.x hex).2.1
  have hbx_cast : blockAt (scaleTreePartitionChain T P M ℓ.castSucc) e.x = X := (hSc1_w e.x hex).2.2
  have hby_succ : blockAt (scaleTreePartitionChain T P M ℓ.succ) e.y =
      subblock1 (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X) c₂ := (hSc2_w e.y hey).2.1
  have hby_cast : blockAt (scaleTreePartitionChain T P M ℓ.castSucc) e.y = X := (hSc2_w e.y hey).2.2
  have hex_Icc : e.x ∈ Finset.Icc 1 P :=
    Finset.mem_Icc.mpr ⟨le_trans hX1 (le_trans hSc1_Xlo (Finset.mem_Icc.mp hex).1),
      le_trans (Finset.mem_Icc.mp hex).2 (le_trans hSc1_Xhi hXP)⟩
  have hey_Icc : e.y ∈ Finset.Icc 1 P :=
    Finset.mem_Icc.mpr ⟨le_trans hX1 (le_trans hSc2_Xlo (Finset.mem_Icc.mp hey).1),
      le_trans (Finset.mem_Icc.mp hey).2 (le_trans hSc2_Xhi hXP)⟩
  have hlt_12 := hsub_lt c₁ c₂ (by omega) (by omega) hc2_hi
  have hne_xy : blockAt (scaleTreePartitionChain T P M ℓ.succ) e.x ≠
      blockAt (scaleTreePartitionChain T P M ℓ.succ) e.y := by
    rw [hbx_succ, hby_succ]
    intro heq; rw [heq] at hlt_12; omega
  have hsep_xy : partSepScale P (scaleTreePartitionChain T P M) e.x e.y = ℓ.val + 1 :=
    ((partSepScale_props hChain hex_Icc hey_Icc).2.2.2 ℓ).1.mpr
      ⟨hbx_cast.trans hby_cast.symm, hne_xy⟩
  have hℓ : 1 ≤ ℓ.val + 1 ∧ ℓ.val + 1 ≤ M := ⟨by omega, by have := ℓ.isLt; omega⟩
  have hfin_eq : (⟨ℓ.val + 1, Nat.lt_succ_of_le hℓ.2⟩ : Fin (M + 1)) = ℓ.succ := rfl
  refine ⟨?_, ?_⟩
  · intro hz_le
    unfold b3Intra
    rw [Finset.mem_filter]
    refine ⟨he_rInt, ?_⟩
    simp only [hsep_xy, hℓ, and_self, ↓reduceDIte, hfin_eq, hsep_sx, hby_succ]
    exact ⟨trivial, hz_le⟩
  · intro hz_gt
    have he_exit : e ∈ b3Exit P proc (scaleTreePartitionChain T P M) := by
      unfold b3Exit
      rw [Finset.mem_filter]
      refine ⟨he_rInt, ?_⟩
      simp only [hsep_xy, hℓ, and_self, ↓reduceDIte, hfin_eq, hsep_sx, hby_succ]
      exact ⟨trivial, hz_gt⟩
    have he_act : e ∈ b3ExitAct P proc (scaleTreePartitionChain T P M) := by
      unfold b3ExitAct
      rw [Finset.mem_filter]
      refine ⟨he_exit, ?_⟩
      simp only [hsep_xy, hℓ.2, ↓reduceDIte, hfin_eq, hbp]
      exact he_tau
    have he_vXp : e ∈ vXp P proc (scaleTreePartitionChain T P M) (ℓ.val + 1) X p := by
      unfold vXp
      simp only [hℓ, and_self, ↓reduceDIte, hfin_eq, Finset.mem_filter]
      exact ⟨he_act, hsep_xy, hes⟩
    refine ⟨he_vXp, ?_⟩
    unfold promotedSubblockIndices
    simp only [hℓ, and_self, ↓reduceDIte, hfin_eq, Finset.mem_filter]
    exact ⟨hc₁, e, he_vXp, hex⟩

private theorem gapWitnessSet_local
    (h_3_1 : ∀ {α : Type} [LinearOrder α] (t : BinaryTree α) (S : Set α),
      t.IsBST → IsLCAClosed t S →
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
    (h_5_7 : ∀ (P r M : ℕ) (T : ScaleTree),
      ValidScaleTree P r M T → ∀ (proc : FoldedPopProcess P)
      (ℓ : Fin M) (X : IntervalBlock), X ∈ scaleTreePartitionChain T P M ℓ.castSucc →
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
            topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G))))
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P)
    (h_freeze : ∀ e ∈ proc.rInt,
      ∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z))
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    {p : ℕ} (hp : p ∈ Finset.Icc 1
      ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1)) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
    let pi0 := leftSpine G₀
    let Fp := promotedSubblockIndices P proc chain ℓ_val X p
    gapWitnessSet P T proc chain ℓ X p ⊆ pi0.toFinset \ Fp ∧
    ∀ a b : ℕ, a < b → b < pi0.length →
      (pi0[a]?).getD 0 ∈ Fp → (pi0[b]?).getD 0 ∈ Fp →
      (∀ t : ℕ, a < t → t < b → (pi0[t]?).getD 0 ∉ Fp) →
      scaleI T P ℓ_val < b - a - 1 →
      let g := b - a - 1
      let gapSet := (Finset.Ioo a b).image (fun t => (pi0[t]?).getD 0)
      g - 3 ≤ (gapWitnessSet P T proc chain ℓ X p ∩ gapSet).card ∧
      scaleI T P ℓ_val < 2 * (g - 3) := by
  classical
  dsimp only
  have hU_eq : gapWitnessSet P T proc (scaleTreePartitionChain T P M) ℓ X p =
      (let ℓ_val := ℓ.val + 1
       let subs := childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X
       let G₀ := phaseSummaryBST P proc (scaleTreePartitionChain T P M) ℓ_val X p
         (proc.popStepIdx (subblock1 subs p).lo)
       let pi0 := leftSpine G₀
       let Fp := promotedSubblockIndices P proc (scaleTreePartitionChain T P M) ℓ_val X p
       (pi0.toFinset \ Fp).filter (fun c =>
         isWitA1 P proc (scaleTreePartitionChain T P M) ℓ X p c ∨
         isWitA2 P proc (scaleTreePartitionChain T P M) ℓ X p c ∨
         isWitB1 P proc (scaleTreePartitionChain T P M) ℓ X p c ∨
         isWitB2 P T proc (scaleTreePartitionChain T P M) ℓ X p c ∨
         isWitC1 P proc (scaleTreePartitionChain T P M) ℓ X p c ∨
         isWitC2 P proc (scaleTreePartitionChain T P M) ℓ X p c)) := by
    unfold gapWitnessSet
    simp only [hX, hp, and_self, ↓reduceIte]
  refine ⟨by rw [hU_eq]; exact Finset.filter_subset _ _, ?_⟩
  intro a b hab hb_lt ha_Fp hb_Fp hno_Fp hgap_gt
  have hi5 : 5 ≤ scaleI T P (ℓ.val + 1) :=
    scaleI_ge_five hValid (by omega) (by have := ℓ.isLt; omega)
  refine ⟨?_, by omega⟩
  obtain ⟨hX1, _, hXP, _, hsub_c, hsub_lt, _, _, hsub_cover⟩ := subblock1_props hValid ℓ X hX
  obtain ⟨_, hp_lt_K, hSplo1, hSplo_smax, hsmax_Sphi, _, _, _, htEmpty_len, _, haw⟩ :=
    active_window_props hValid proc ℓ X hX hp
  obtain ⟨_, h57_phase, _⟩ := h_5_7 P r M T hValid proc ℓ X hX
  obtain ⟨htStart_tau, htau_tEnd, hG_bst_keys, _, _⟩ := h57_phase p hp
  obtain ⟨_, hFp_drop, _⟩ := lem_5_8_part1 h_5_7 P r M T hValid proc ℓ X hX p hp
  obtain ⟨hrInt_basic, _⟩ := rInt_basic_and_order proc
  obtain ⟨_, hpop_props, hpop_mono, _, _⟩ := popStepIdx_and_insStep_props proc
  obtain ⟨hbst_all, _⟩ := proc_tree_bst_and_step_keys proc
  set chain := scaleTreePartitionChain T P M
  set ℓ_val := ℓ.val + 1
  set subs := childSubblocks (chain ℓ.succ) X
  set K_X := subs.length
  set tStart := proc.popStepIdx (subblock1 subs p).lo
  set tEmpty := tauEmpty proc (subblock1 subs p)
  set G₀ := phaseSummaryBST P proc chain ℓ_val X p tStart
  set pi0 := leftSpine G₀
  set Fp := promotedSubblockIndices P proc chain ℓ_val X p
  set gapSet := (Finset.Ioo a b).image (fun t => (pi0[t]?).getD 0)
  obtain ⟨hp1, _⟩ := Finset.mem_Icc.mp hp
  have hG0_bst_keys := hG_bst_keys tStart (Finset.mem_Icc.mpr ⟨le_rfl, le_trans htStart_tau htau_tEnd⟩)
  have hpi0_pw : pi0.Pairwise (· < ·) := leftSpine_pairwise_lt hG0_bst_keys.1
  have get_pi0 : ∀ {idx : ℕ} (h : idx < pi0.length), (pi0[idx]?).getD 0 = pi0[idx]'h := by
    intro idx h; simp [List.getElem?_eq_getElem h]
  have pi0_lt_iff : ∀ {i₁ i₂ : ℕ} (h1 : i₁ < pi0.length) (h2 : i₂ < pi0.length),
      pi0[i₁]'h1 < pi0[i₂]'h2 ↔ i₁ < i₂ := by
    intro i₁ i₂ h1 h2
    constructor
    · intro hlt
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
      · exact lt_irrefl _ hlt
      · exact lt_asymm hlt (List.pairwise_iff_getElem.mp hpi0_pw i₂ i₁ h2 h1 hgt)
    · exact List.pairwise_iff_getElem.mp hpi0_pw i₁ i₂ h1 h2
  have ha_lt : a < pi0.length := lt_trans hab hb_lt
  set c_a := (pi0[a]?).getD 0
  set c_b := (pi0[b]?).getD 0
  have hca_eq : c_a = pi0[a]'ha_lt := get_pi0 ha_lt
  have hcb_eq : c_b = pi0[b]'hb_lt := get_pi0 hb_lt
  have mem_of_dropLast : ∀ {xs : List ℕ} {w : ℕ}, w ∈ xs.dropLast → w ∈ xs := by
    intro xs
    induction xs with
    | nil => intro _ h; simp at h
    | cons x rest ih =>
      cases rest with
      | nil => intro _ h; simp at h
      | cons y rest' =>
        intro w h
        change w ∈ x :: (y :: rest').dropLast at h
        rcases List.mem_cons.mp h with rfl | hrest
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hrest)
  have hFp_lt_cb : ∀ d ∈ Fp, d < c_b → d ≤ c_a := by
    intro d hd_Fp hd_lt
    have hd_pi0 : d ∈ pi0 := mem_of_dropLast (hFp_drop d hd_Fp)
    obtain ⟨td, htd_lt, rfl⟩ := List.getElem_of_mem hd_pi0
    rw [hcb_eq, pi0_lt_iff htd_lt hb_lt] at hd_lt
    by_contra hgt_a
    have hgt_a' : c_a < pi0[td]'htd_lt := Nat.lt_of_not_le hgt_a
    rw [hca_eq, pi0_lt_iff ha_lt htd_lt] at hgt_a'
    have htd_Fp : (pi0[td]?).getD 0 ∈ Fp := by rw [get_pi0 htd_lt]; exact hd_Fp
    exact hno_Fp td hgt_a' hd_lt htd_Fp
  have hgap_card : gapSet.card = b - a - 1 := by
    have hinj : Set.InjOn (fun t => (pi0[t]?).getD 0) (Finset.Ioo a b : Set ℕ) := by
      intro t₁ ht₁ t₂ ht₂ heq
      dsimp only at heq
      have ht₁_lt : t₁ < pi0.length := lt_trans (Finset.mem_Ioo.mp ht₁).2 hb_lt
      have ht₂_lt : t₂ < pi0.length := lt_trans (Finset.mem_Ioo.mp ht₂).2 hb_lt
      rw [get_pi0 ht₁_lt, get_pi0 ht₂_lt] at heq
      rcases lt_trichotomy t₁ t₂ with h12 | rfl | h21
      · exact absurd ((pi0_lt_iff ht₁_lt ht₂_lt).mpr h12) (by rw [heq]; exact lt_irrefl _)
      · rfl
      · exact absurd ((pi0_lt_iff ht₂_lt ht₁_lt).mpr h21) (by rw [heq]; exact lt_irrefl _)
    rw [Finset.card_image_of_injOn hinj, Nat.card_Ioo]
  have hgap_props : ∀ c ∈ gapSet,
      c ∈ pi0 ∧ c ∉ Fp ∧ c ∈ Finset.Icc (p + 1) K_X ∧ c_a < c ∧ c < c_b := by
    intro c hc
    obtain ⟨t, ht_Ioo, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hat, htb⟩ := Finset.mem_Ioo.mp ht_Ioo
    have ht_lt : t < pi0.length := lt_trans htb hb_lt
    have hct : (pi0[t]?).getD 0 = pi0[t]'ht_lt := get_pi0 ht_lt
    have hc_pi0 : (pi0[t]?).getD 0 ∈ pi0 := hct ▸ List.getElem_mem ht_lt
    have hc_kf : (pi0[t]?).getD 0 ∈ Finset.Icc (p + 1) K_X :=
      hG0_bst_keys.2 ▸ (mem_iff_mem_keyFinset G₀ _).mp (mem_of_mem_leftSpine hc_pi0)
    refine ⟨hc_pi0, hno_Fp t hat htb, hc_kf, ?_, ?_⟩
    · rw [hca_eq, hct, pi0_lt_iff ha_lt ht_lt]; exact hat
    · rw [hct, hcb_eq, pi0_lt_iff ht_lt hb_lt]; exact htb
  -- Unpack `spine_correspondence_at_lead` at `c_a` and `c_b`
  have hcorr_ca := spine_correspondence_at_lead h_3_1 hValid proc ℓ X hX hp ha_Fp
  dsimp only at hcorr_ca
  obtain ⟨hidag_start, hidag_empty, ⟨e_a, _, hea_lead, hea_rInt, hea_x, hkey_a, hea_step, hra_eq, hca_ls_idag⟩, hcorr_a⟩ := hcorr_ca
  set idag := proc.popStepIdx (leadPopKey P proc chain ℓ_val X p c_a)
  set Bp_idag := phaseBlockBST P proc chain ℓ_val X p idag
  set G_idag := phaseSummaryBST P proc chain ℓ_val X p idag
  set rc : ℕ → ℕ := fun c => blockRoot subs Bp_idag c
  have hcorr_cb := spine_correspondence_at_lead h_3_1 hValid proc ℓ X hX hp hb_Fp
  dsimp only at hcorr_cb
  obtain ⟨histar_start, histar_empty, ⟨e_b, _, _, heb_rInt, heb_x, _, heb_step, _, _⟩, _⟩ := hcorr_cb
  set istar := proc.popStepIdx (leadPopKey P proc chain ℓ_val X p c_b)
  -- Unpack `e_a ∈ rInt` at `idag` and `e_b ∈ rInt` at `istar`
  obtain ⟨hτ_idag_raw, b1_idag, hop_idag_raw, hb1_idag_raw, hh_idag_raw, hj1_a, hjh_a, hxa_sub_raw, _, _⟩ :=
    (mem_rInt_iff proc e_a).mp hea_rInt
  have hidag_lt_len : idag < proc.steps.length := hea_step ▸ hτ_idag_raw
  have hop_idag : proc.steps[idag]? = some (.pop e_a.s) := by
    rw [← hea_step]; exact (List.getElem?_eq_getElem hτ_idag_raw).trans (congrArg some hop_idag_raw)
  have heas_Sp : e_a.s ∈ (subblock1 subs p).toFinset :=
    ((haw idag hidag_start hidag_empty).2.2.2.2 e_a.s hop_idag).1
  have hb1_idag : proc.b1At idag = some b1_idag := hea_step ▸ hb1_idag_raw
  obtain ⟨hval_idag, _⟩ := proc_step_at proc hτ_idag_raw
  rw [hop_idag_raw] at hval_idag
  rcases hval_idag with ⟨b1_tmp, _, _, hb1_tmp, hb1_idag_ls⟩
  change proc.b1At e_a.stepIdx = some b1_tmp at hb1_tmp
  rw [hea_step] at hb1_tmp hb1_idag_ls
  rw [hb1_idag] at hb1_tmp; injection hb1_tmp with htmp; subst b1_tmp
  set sub_idag := takeThrough (leftSpine (proc.treeAt idag)) b1_idag
  set k_idag := sub_idag.length - 1
  set h_idag := (k_idag - 1) / 2
  have hh_idag : e_a.h = h_idag := by dsimp [h_idag, k_idag, sub_idag]; rw [← hea_step]; exact hh_idag_raw
  have hxa_sub : sub_idag[2 * e_a.j - 1]? = some e_a.x := by dsimp [sub_idag]; rw [← hea_step]; exact hxa_sub_raw
  have hpw_ls_idag : (leftSpine (proc.treeAt idag)).Pairwise (· < ·) :=
    leftSpine_pairwise_lt (hbst_all idag (le_of_lt hidag_lt_len)).1
  obtain ⟨_, hsub_idag_ne, hpw_sub_idag, _, hsub_idag_last, hmem_sub_idag⟩ :=
    takeThrough_props hpw_ls_idag hb1_idag_ls
  obtain ⟨hτ_istar_raw, b1_istar, hop_istar_raw, hb1_istar_raw, _, _, _, _, hyb_sub_raw, _⟩ :=
    (mem_rInt_iff proc e_b).mp heb_rInt
  have hb1_istar : proc.b1At istar = some b1_istar := heb_step ▸ hb1_istar_raw
  obtain ⟨hval_istar, _⟩ := proc_step_at proc hτ_istar_raw
  rw [hop_istar_raw] at hval_istar
  rcases hval_istar with ⟨b1_stmp, _, _, hb1_stmp, hb1_istar_ls⟩
  change proc.b1At e_b.stepIdx = some b1_stmp at hb1_stmp
  rw [heb_step] at hb1_stmp hb1_istar_ls hyb_sub_raw
  rw [hb1_istar] at hb1_stmp; injection hb1_stmp with hstmp; subst b1_stmp
  have hpw_ls_istar : (leftSpine (proc.treeAt istar)).Pairwise (· < ·) :=
    leftSpine_pairwise_lt (hbst_all istar (le_of_lt (heb_step ▸ hτ_istar_raw))).1
  obtain ⟨_, _, _, _, _, hmem_sub_istar⟩ := takeThrough_props hpw_ls_istar hb1_istar_ls
  have heb_x_lt_b1 : e_b.x < b1_istar := by
    have hyb_le : e_b.y ≤ b1_istar :=
      ((hmem_sub_istar e_b.y).mp (List.mem_of_getElem? hyb_sub_raw)).2
    have hxy_b := (hrInt_basic e_b heb_rInt).2.2.2.2.1
    omega
  -- Define the 3 excluded subsets of `gapSet`
  let excl1 := gapSet.filter (fun c => k_idag = 2 * h_idag + 2 ∧ sub_idag[2 * h_idag + 1]? = some (rc c))
  let excl2 := gapSet.filter (fun c => ∃ j : ℕ, (1 ≤ j ∧ j ≤ h_idag) ∧
    sub_idag[2 * j - 1]? = some (rc c) ∧ ∃ y, sub_idag[2 * j]? = some y ∧ X.hi < y)
  let excl3 := gapSet.filter (fun c => ∃ j : ℕ, (1 ≤ j ∧ j ≤ h_idag) ∧
    sub_idag[2 * j]? = some (rc c) ∧ ∃ x, sub_idag[2 * j - 1]? = some x ∧ x ≤ e_a.x)
  have rc_props_gap : ∀ {c : ℕ}, c ∈ gapSet →
      rc c ∈ (subblock1 subs c).toFinset ∧ subblockIndex1 subs (rc c) = c := by
    intro c hc
    obtain ⟨_, _, hc_pK, hca_c, _⟩ := hgap_props c hc
    have hc_caK : c ∈ Finset.Icc c_a K_X := Finset.mem_Icc.mpr ⟨le_of_lt hca_c, (Finset.mem_Icc.mp hc_pK).2⟩
    exact ⟨(hcorr_a c hc_caK).1, (hcorr_a c hc_caK).2.1⟩
  have hexcl1_card : excl1.card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun c₁ hc₁ c₂ hc₂ => ?_)
    obtain ⟨hc₁_g, _, h1⟩ := Finset.mem_filter.mp hc₁
    obtain ⟨hc₂_g, _, h2⟩ := Finset.mem_filter.mp hc₂
    rw [h1] at h2; injection h2 with hrc_eq
    rw [← (rc_props_gap hc₁_g).2, ← (rc_props_gap hc₂_g).2, hrc_eq]
  have hexcl2_lt_false : ∀ {c₁ c₂ : ℕ}, c₁ ∈ excl2 → c₂ ∈ excl2 → c₁ < c₂ → False := by
    intro c₁ c₂ hc₁ hc₂ hlt12
    obtain ⟨hc₁_g, j₁, _, hj₁_x, y₁, hj₁_y, hy₁_gt⟩ := Finset.mem_filter.mp hc₁
    obtain ⟨hc₂_g, j₂, _, hj₂_x, _, _, _⟩ := Finset.mem_filter.mp hc₂
    obtain ⟨hrc₁_Fin, _⟩ := rc_props_gap hc₁_g
    obtain ⟨hrc₂_Fin, _⟩ := rc_props_gap hc₂_g
    have hc₁_pK := (hgap_props c₁ hc₁_g).2.2.1
    have hc₂_pK := (hgap_props c₂ hc₂_g).2.2.1
    have hlt_sub12 := hsub_lt c₁ c₂ (by have := (Finset.mem_Icc.mp hc₁_pK).1; omega)
      hlt12 (Finset.mem_Icc.mp hc₂_pK).2
    have hrc_lt : rc c₁ < rc c₂ :=
      lt_of_le_of_lt (Finset.mem_Icc.mp hrc₁_Fin).2 (lt_of_lt_of_le hlt_sub12 (Finset.mem_Icc.mp hrc₂_Fin).1)
    have hSc₂_Xhi := (hsub_c c₂ (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc₂_pK).1; omega,
      (Finset.mem_Icc.mp hc₂_pK).2⟩)).2.2.2.2.1
    have hrc₂_Xhi : rc c₂ ≤ X.hi := le_trans (Finset.mem_Icc.mp hrc₂_Fin).2 hSc₂_Xhi
    obtain ⟨h1x_lt, h1x_eq⟩ := List.getElem?_eq_some_iff.mp hj₁_x
    obtain ⟨h1y_lt, h1y_eq⟩ := List.getElem?_eq_some_iff.mp hj₁_y
    obtain ⟨h2x_lt, h2x_eq⟩ := List.getElem?_eq_some_iff.mp hj₂_x
    have hj_lt : 2 * j₁ - 1 < 2 * j₂ - 1 := by
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hgt
      · have : rc c₁ = rc c₂ := by rw [← h1x_eq, ← h2x_eq]; simp [heq]
        omega
      · have := List.pairwise_iff_getElem.mp hpw_sub_idag _ _ h2x_lt h1x_lt hgt
        rw [h2x_eq, h1x_eq] at this; omega
    have hy₁_lt_rc₂ : y₁ < rc c₂ := by
      have := List.pairwise_iff_getElem.mp hpw_sub_idag (2 * j₁) (2 * j₂ - 1) h1y_lt h2x_lt (by omega)
      rw [h1y_eq, h2x_eq] at this; exact this
    omega
  have hexcl2_card : excl2.card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun c₁ hc₁ c₂ hc₂ => ?_)
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h2
    · exact hexcl2_lt_false hc₁ hc₂ h1
    · exact hexcl2_lt_false hc₂ hc₁ h2
  have hexcl3_lt_false : ∀ {c₁ c₂ : ℕ}, c₁ ∈ excl3 → c₂ ∈ excl3 → c₁ < c₂ → False := by
    intro c₁ c₂ hc₁ hc₂ hlt12
    obtain ⟨hc₁_g, j₁, _, hj₁_y, _, _, _⟩ := Finset.mem_filter.mp hc₁
    obtain ⟨hc₂_g, j₂, ⟨hj2_pos, _⟩, hj₂_y, x₂, hj₂_x, hx₂_le⟩ := Finset.mem_filter.mp hc₂
    obtain ⟨hrc₁_Fin, _⟩ := rc_props_gap hc₁_g
    obtain ⟨hrc₂_Fin, _⟩ := rc_props_gap hc₂_g
    obtain ⟨_, _, hc₁_pK, hca_lt_c₁, _⟩ := hgap_props c₁ hc₁_g
    have hc₂_pK := (hgap_props c₂ hc₂_g).2.2.1
    have hca_pK : c_a ∈ Finset.Icc (p + 1) K_X :=
      hG0_bst_keys.2 ▸ (mem_iff_mem_keyFinset G₀ _).mp
        (mem_of_mem_leftSpine (hca_eq ▸ List.getElem_mem ha_lt))
    have hlt_ac₁ := hsub_lt c_a c₁ (by have := (Finset.mem_Icc.mp hca_pK).1; omega)
      hca_lt_c₁ (Finset.mem_Icc.mp hc₁_pK).2
    have hxa_lt_rc₁ : e_a.x < rc c₁ :=
      lt_of_le_of_lt (Finset.mem_Icc.mp hea_x).2 (lt_of_lt_of_le hlt_ac₁ (Finset.mem_Icc.mp hrc₁_Fin).1)
    have hlt_sub12 := hsub_lt c₁ c₂ (by have := (Finset.mem_Icc.mp hc₁_pK).1; omega)
      hlt12 (Finset.mem_Icc.mp hc₂_pK).2
    have hrc_lt : rc c₁ < rc c₂ :=
      lt_of_le_of_lt (Finset.mem_Icc.mp hrc₁_Fin).2 (lt_of_lt_of_le hlt_sub12 (Finset.mem_Icc.mp hrc₂_Fin).1)
    obtain ⟨h1y_lt, h1y_eq⟩ := List.getElem?_eq_some_iff.mp hj₁_y
    obtain ⟨h2y_lt, h2y_eq⟩ := List.getElem?_eq_some_iff.mp hj₂_y
    obtain ⟨h2x_lt, h2x_eq⟩ := List.getElem?_eq_some_iff.mp hj₂_x
    have hj_lt : 2 * j₁ < 2 * j₂ := by
      by_contra hge
      rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hgt
      · have : rc c₁ = rc c₂ := by rw [← h1y_eq, ← h2y_eq]; simp [heq]
        omega
      · have := List.pairwise_iff_getElem.mp hpw_sub_idag _ _ h2y_lt h1y_lt hgt
        rw [h2y_eq, h1y_eq] at this; omega
    have hrc₁_le_x₂ : rc c₁ ≤ x₂ := by
      rcases eq_or_lt_of_le (show 2 * j₁ ≤ 2 * j₂ - 1 by omega) with heq | hlt_idx
      · rw [← h1y_eq, ← h2x_eq]; simp [heq]
      · exact le_of_lt (by
          have := List.pairwise_iff_getElem.mp hpw_sub_idag _ _ h1y_lt h2x_lt hlt_idx
          rw [h1y_eq, h2x_eq] at this; exact this)
    omega
  have hexcl3_card : excl3.card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun c₁ hc₁ c₂ hc₂ => ?_)
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h2
    · exact hexcl3_lt_false hc₁ hc₂ h1
    · exact hexcl3_lt_false hc₂ hc₁ h2
  -- Show `gapSet ⊆ (gapWitnessSet ∩ gapSet) ∪ (excl1 ∪ excl2 ∪ excl3)`
  have hcover_gap : gapSet ⊆
      (gapWitnessSet P T proc chain ℓ X p ∩ gapSet) ∪ (excl1 ∪ excl2 ∪ excl3) := by
    intro c hc_gap
    by_cases hc_ex : c ∈ excl1 ∪ excl2 ∪ excl3
    · exact Finset.mem_union_right _ hc_ex
    · refine Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨?_, hc_gap⟩)
      simp only [Finset.mem_union, not_or] at hc_ex
      rcases hc_ex with ⟨⟨hc_ne1, hc_ne2⟩, hc_ne3⟩
      obtain ⟨hc_pi0, hc_not_Fp, hc_pK, hca_lt_c, hc_lt_cb⟩ := hgap_props c hc_gap
      have hc_caK : c ∈ Finset.Icc c_a K_X :=
        Finset.mem_Icc.mpr ⟨le_of_lt hca_lt_c, (Finset.mem_Icc.mp hc_pK).2⟩
      obtain ⟨hrc_Fin, _, hls_G_iff, hls_gt_hi⟩ := hcorr_a c hc_caK
      rw [hU_eq, Finset.mem_filter]
      refine ⟨Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hc_pi0, hc_not_Fp⟩, ?_⟩
      by_cases hc_Gidag : c ∈ leftSpine G_idag
      · -- `c ∈ leftSpine G_idag`: Class B (`rc c < b1_idag`) or Class C (`b1_idag ≤ rc c`)
        have hrc_ls : rc c ∈ leftSpine (proc.treeAt idag) := hls_G_iff.mp hc_Gidag
        by_cases hrc_lt_b1 : rc c < b1_idag
        · -- Class B: `rc c ∈ sub_idag`
          have hrc_in_sub : rc c ∈ sub_idag :=
            (hmem_sub_idag (rc c)).mpr ⟨hrc_ls, le_of_lt hrc_lt_b1⟩
          obtain ⟨iq, hiq_lt, hiq_eq⟩ := List.getElem_of_mem hrc_in_sub
          have hsub_last_get := @List.getLast?_eq_getElem? _ sub_idag
          rw [hsub_idag_last, show sub_idag.length - 1 = k_idag from rfl,
              List.getElem?_eq_getElem (by have := List.length_pos_of_ne_nil hsub_idag_ne; omega)] at hsub_last_get
          injection hsub_last_get with hb1_at_k
          have hiq_lt_k : iq < k_idag := by
            by_contra hge
            rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with rfl | hgt
            · omega
            · omega
          -- `e_a.x < rc c`, so `2 * e_a.j - 1 < iq`
          have hca_pK : c_a ∈ Finset.Icc (p + 1) K_X :=
            hG0_bst_keys.2 ▸ (mem_iff_mem_keyFinset G₀ _).mp
              (mem_of_mem_leftSpine (hca_eq ▸ List.getElem_mem ha_lt))
          have hlt_ac := hsub_lt c_a c (by have := (Finset.mem_Icc.mp hca_pK).1; omega)
            hca_lt_c (Finset.mem_Icc.mp hc_pK).2
          have hxa_lt_rc : e_a.x < rc c :=
            lt_of_le_of_lt (Finset.mem_Icc.mp hea_x).2 (lt_of_lt_of_le hlt_ac (Finset.mem_Icc.mp hrc_Fin).1)
          obtain ⟨hxa_idx_lt, hxa_idx_eq⟩ := List.getElem?_eq_some_iff.mp hxa_sub
          have hxa_lt_iq : 2 * e_a.j - 1 < iq := by
            by_contra hge
            rcases eq_or_lt_of_le (Nat.le_of_not_lt hge) with heq | hgt
            · rw [← hiq_eq, ← hxa_idx_eq] at hxa_lt_rc; simp [heq] at hxa_lt_rc
            · have := List.pairwise_iff_getElem.mp hpw_sub_idag _ _ hiq_lt hxa_idx_lt hgt
              rw [hiq_eq, hxa_idx_eq] at this; omega
          have hiq_le_2h : iq ≤ 2 * h_idag := by
            by_contra hgt_2h
            have hk_even : k_idag = 2 * h_idag + 2 ∧ iq = 2 * h_idag + 1 := by
              dsimp [h_idag] at *; omega
            exact hc_ne1 (Finset.mem_filter.mpr ⟨hc_gap, hk_even.1,
              by rw [← hk_even.2, List.getElem?_eq_getElem hiq_lt, hiq_eq]⟩)
          by_cases hmod : iq % 2 = 1
          · -- Subcase B1: `iq = 2 * j - 1` (`1 ≤ j ≤ h_idag`)
            set j := (iq + 1) / 2
            have hj_Icc : j ∈ Finset.Icc 1 h_idag := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            have hiq_odd : iq = 2 * j - 1 := by omega
            have hjy_lt : 2 * j < sub_idag.length := by omega
            have hjz_lt : 2 * j + 1 < sub_idag.length := by omega
            set y := sub_idag[2 * j]'hjy_lt
            set z := sub_idag[2 * j + 1]'hjz_lt
            let ej : InternalPopRot :=
              { stepIdx := idag, s := e_a.s, j := j, h := h_idag, x := rc c, y := y, z := z }
            have hej_rInt : ej ∈ proc.rInt := by
              rw [mem_rInt_iff]
              refine ⟨hidag_lt_len, b1_idag, ?_, hb1_idag, rfl,
                (Finset.mem_Icc.mp hj_Icc).1, (Finset.mem_Icc.mp hj_Icc).2,
                by rw [← hiq_odd, List.getElem?_eq_getElem hiq_lt, hiq_eq],
                List.getElem?_eq_getElem hjy_lt, List.getElem?_eq_getElem hjz_lt⟩
              rw [List.getElem?_eq_getElem hidag_lt_len] at hop_idag
              injection hop_idag
            have hy_le_Xhi : y ≤ X.hi := by
              by_contra hy_gt
              exact hc_ne2 (Finset.mem_filter.mpr ⟨hc_gap, j, Finset.mem_Icc.mp hj_Icc,
                by rw [← hiq_odd, List.getElem?_eq_getElem hiq_lt, hiq_eq],
                y, List.getElem?_eq_getElem hjy_lt, Nat.lt_of_not_le hy_gt⟩)
            have hrc_lt_y : rc c < y := by
              rw [← hiq_eq]
              exact List.pairwise_iff_getElem.mp hpw_sub_idag iq (2 * j) hiq_lt hjy_lt (by omega)
            have hy_ls : y ∈ leftSpine (proc.treeAt idag) :=
              ((hmem_sub_idag y).mp (List.getElem_mem hjy_lt)).1
            have hSc_lt_y : (subblock1 subs c).hi < y := hls_gt_hi hc_Gidag y hy_ls hrc_lt_y
            have hc_1K : c ∈ Finset.Icc 1 K_X :=
              Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc_pK).1; omega, (Finset.mem_Icc.mp hc_pK).2⟩
            have hy_X : y ∈ Finset.Icc X.lo X.hi :=
              Finset.mem_Icc.mpr ⟨le_trans (hsub_c c hc_1K).2.2.1
                (le_trans (hsub_c c hc_1K).2.2.2.1 (le_of_lt hSc_lt_y)), hy_le_Xhi⟩
            obtain ⟨hq_1K, hy_Sq⟩ := hsub_cover y hy_X
            set q := subblockIndex1 subs y
            have hq_gt_c : c + 1 ≤ q := by
              by_contra hle_c
              rcases eq_or_lt_of_le (show q ≤ c by omega) with heq_qc | hlt_qc
              · rw [heq_qc] at hy_Sq; have := (Finset.mem_Icc.mp hy_Sq).2; omega
              · have := hsub_lt q c (Finset.mem_Icc.mp hq_1K).1 hlt_qc (Finset.mem_Icc.mp hc_pK).2
                have := (Finset.mem_Icc.mp hy_Sq).2
                have := (hsub_c c hc_1K).2.2.2.1
                omega
            have hq_cK : q ∈ Finset.Icc (c + 1) K_X :=
              Finset.mem_Icc.mpr ⟨hq_gt_c, (Finset.mem_Icc.mp hq_1K).2⟩
            obtain ⟨hintra, hvxp_q⟩ := same_scale_intra_or_vXp hValid proc ℓ X hX hp hc_pK hq_cK
              hej_rInt heas_Sp hidag_empty hrc_Fin hy_Sq
            have hz_le_Sq : z ≤ (subblock1 subs q).hi := by
              by_contra hz_gt
              exact hc_not_Fp (hvxp_q (Nat.lt_of_not_le hz_gt)).2
            exact Or.inr (Or.inr (Or.inl ⟨ej, hintra hz_le_Sq, heas_Sp, hrc_Fin⟩))
          · -- Subcase B2: `iq = 2 * j` (`1 ≤ j ≤ h_idag`)
            set j := iq / 2
            have hj_Icc : j ∈ Finset.Icc 1 h_idag := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            have hiq_even : iq = 2 * j := by omega
            have hjx_lt : 2 * j - 1 < sub_idag.length := by omega
            have hjz_lt : 2 * j + 1 < sub_idag.length := by omega
            set x := sub_idag[2 * j - 1]'hjx_lt
            set z := sub_idag[2 * j + 1]'hjz_lt
            let ej : InternalPopRot :=
              { stepIdx := idag, s := e_a.s, j := j, h := h_idag, x := x, y := rc c, z := z }
            have hej_rInt : ej ∈ proc.rInt := by
              rw [mem_rInt_iff]
              refine ⟨hidag_lt_len, b1_idag, ?_, hb1_idag, rfl,
                (Finset.mem_Icc.mp hj_Icc).1, (Finset.mem_Icc.mp hj_Icc).2,
                List.getElem?_eq_getElem hjx_lt,
                by rw [← hiq_even, List.getElem?_eq_getElem hiq_lt, hiq_eq],
                List.getElem?_eq_getElem hjz_lt⟩
              rw [List.getElem?_eq_getElem hidag_lt_len] at hop_idag
              injection hop_idag
            have hxa_lt_x : e_a.x < x := by
              by_contra hx_le
              exact hc_ne3 (Finset.mem_filter.mpr ⟨hc_gap, j, Finset.mem_Icc.mp hj_Icc,
                by rw [← hiq_even, List.getElem?_eq_getElem hiq_lt, hiq_eq],
                x, List.getElem?_eq_getElem hjx_lt, Nat.le_of_not_lt hx_le⟩)
            have hx_lt_rc : x < rc c := by
              rw [← hiq_eq]
              exact List.pairwise_iff_getElem.mp hpw_sub_idag (2 * j - 1) iq hjx_lt hiq_lt (by omega)
            have hrc_lt_z : rc c < z := by
              rw [← hiq_eq]
              exact List.pairwise_iff_getElem.mp hpw_sub_idag iq (2 * j + 1) hiq_lt hjz_lt (by omega)
            have hx_ls : x ∈ leftSpine (proc.treeAt idag) :=
              ((hmem_sub_idag x).mp (List.getElem_mem hjx_lt)).1
            have hz_ls : z ∈ leftSpine (proc.treeAt idag) :=
              ((hmem_sub_idag z).mp (List.getElem_mem hjz_lt)).1
            have hSca_lt_x : (subblock1 subs c_a).hi < x :=
              (hcorr_a c_a (Finset.mem_Icc.mpr ⟨le_rfl, (Finset.mem_Icc.mp hca_pK).2⟩)).2.2.2
                hca_ls_idag x hx_ls (hra_eq.symm ▸ hxa_lt_x)
            have hSc_lt_z : (subblock1 subs c).hi < z := hls_gt_hi hc_Gidag z hz_ls hrc_lt_z
            have hc_1K : c ∈ Finset.Icc 1 K_X :=
              Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc_pK).1; omega, (Finset.mem_Icc.mp hc_pK).2⟩
            have hca_1K : c_a ∈ Finset.Icc 1 K_X :=
              Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hca_pK).1; omega, (Finset.mem_Icc.mp hca_pK).2⟩
            have hx_X : x ∈ Finset.Icc X.lo X.hi :=
              Finset.mem_Icc.mpr ⟨le_trans (hsub_c c_a hca_1K).2.2.1
                (le_trans (hsub_c c_a hca_1K).2.2.2.1 (le_of_lt hSca_lt_x)),
                le_trans (le_of_lt hx_lt_rc) (le_trans (Finset.mem_Icc.mp hrc_Fin).2 (hsub_c c hc_1K).2.2.2.2.1)⟩
            obtain ⟨hd_1K, hx_Sd⟩ := hsub_cover x hx_X
            set d := subblockIndex1 subs x
            have hca_lt_d : c_a < d := by
              by_contra hd_le
              rcases eq_or_lt_of_le (Nat.le_of_not_lt hd_le) with heq_da | hlt_da
              · rw [heq_da] at hx_Sd; have := (Finset.mem_Icc.mp hx_Sd).2; omega
              · have := hsub_lt d c_a (Finset.mem_Icc.mp hd_1K).1 hlt_da (Finset.mem_Icc.mp hca_pK).2
                have := (Finset.mem_Icc.mp hx_Sd).2
                have := (hsub_c c_a hca_1K).2.2.2.1
                omega
            have hd_le_c : d ≤ c := by
              by_contra hd_gt
              have hlt_cd := hsub_lt c d (Finset.mem_Icc.mp hc_1K).1 (Nat.lt_of_not_le hd_gt) (Finset.mem_Icc.mp hd_1K).2
              have hx_lo := (Finset.mem_Icc.mp hx_Sd).1
              have hrc_hi := (Finset.mem_Icc.mp (rc_props_gap hc_gap).1).2
              exact absurd (lt_of_le_of_lt hrc_hi (lt_of_lt_of_le hlt_cd hx_lo)) (not_lt_of_gt hx_lt_rc)
            have hd_eq_c : d = c := by
              rcases eq_or_lt_of_le hd_le_c with rfl | hd_lt_c
              · rfl
              · exfalso
                have hd_pK : d ∈ Finset.Icc (p + 1) K_X :=
                  Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hca_pK).1; omega, (Finset.mem_Icc.mp hd_1K).2⟩
                have hc_dK : c ∈ Finset.Icc (d + 1) K_X :=
                  Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hc_pK).2⟩
                have hd_Fp := ((same_scale_intra_or_vXp hValid proc ℓ X hX hp hd_pK hc_dK
                  hej_rInt heas_Sp hidag_empty hx_Sd hrc_Fin).2 hSc_lt_z).2
                have hd_le_ca := hFp_lt_cb d hd_Fp (lt_trans hd_lt_c hc_lt_cb)
                omega
            rw [hd_eq_c] at hx_Sd
            have hej_b2 := b2_even_mem_s1_or_leafPre hValid proc ℓ X hX hp hc_pK
              hej_rInt heas_Sp hx_Sd hrc_Fin hSc_lt_z
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ej, hej_b2, heas_Sp, hrc_Fin⟩)))
        · -- Class C: `b1_idag ≤ rc c`
          have hrc_U_idag : rc c ∈ upperSpineSet proc idag := by
            unfold upperSpineSet; rw [hb1_idag]; exact ⟨hrc_ls, Nat.le_of_not_lt hrc_lt_b1⟩
          have hcb_pK : c_b ∈ Finset.Icc (p + 1) K_X :=
            hG0_bst_keys.2 ▸ (mem_iff_mem_keyFinset G₀ _).mp
              (mem_of_mem_leftSpine (hcb_eq ▸ List.getElem_mem hb_lt))
          have hlt_ccb := hsub_lt c c_b (by have := (Finset.mem_Icc.mp hc_pK).1; omega)
            hc_lt_cb (Finset.mem_Icc.mp hcb_pK).2
          have hrc_lt_b1_star : rc c < b1_istar :=
            lt_of_le_of_lt (Finset.mem_Icc.mp hrc_Fin).2
              (lt_of_lt_of_le hlt_ccb (le_trans (Finset.mem_Icc.mp heb_x).1 (le_of_lt heb_x_lt_b1)))
          have hrc_not_U_istar : rc c ∉ upperSpineSet proc istar := by
            unfold upperSpineSet; rw [hb1_istar]; rintro ⟨_, hle⟩; omega
          have hrc_gt_Sp : (subblock1 subs p).hi < rc c :=
            lt_of_lt_of_le (hsub_lt p c hp1 (Finset.mem_Icc.mp hc_pK).1 (Finset.mem_Icc.mp hc_pK).2)
              (Finset.mem_Icc.mp hrc_Fin).1
          rcases lt_trichotomy istar idag with histar_lt | heq_star | hidag_lt
          · -- C1 (`istar < idag`): `upperSpineSet` gain
            obtain ⟨τ, hτ_Ico, s', hs'_Sp, b_τ, hop_τ, hb_τ, hk_τ, hsub_τ⟩ :=
              (upperSpineSet_transition_between hValid proc ℓ X hX hp
                histar_start (le_of_lt histar_lt) hidag_empty hrc_gt_Sp).1
                hrc_not_U_istar hrc_U_idag
            have hτ_len : τ < proc.steps.length :=
              lt_of_lt_of_le (lt_trans (Finset.mem_Ico.mp hτ_Ico).2 hidag_empty) htEmpty_len
            have hSp_1K : p ∈ Finset.Icc 1 K_X := Finset.mem_Icc.mpr ⟨hp1, le_of_lt hp_lt_K⟩
            have hs'_Icc : s' ∈ Finset.Icc 1 P :=
              Finset.mem_Icc.mpr ⟨le_trans hX1 (le_trans (hsub_c p hSp_1K).2.2.1 (Finset.mem_Icc.mp hs'_Sp).1),
                le_trans (Finset.mem_Icc.mp hs'_Sp).2 (le_trans (hsub_c p hSp_1K).2.2.2.2.1 hXP)⟩
            have hτ_eq_pop : τ = proc.popStepIdx s' :=
              ((hpop_props s' hs'_Icc).2.2 τ hτ_len).mp hop_τ
            subst hτ_eq_pop
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨s', hs'_Icc, b_τ, rc c, hs'_Sp, hrc_Fin, hb_τ, hk_τ, hsub_τ⟩))))
          · rw [heq_star] at hrc_not_U_istar
            exact absurd hrc_U_idag hrc_not_U_istar
          · -- C2 (`idag < istar`): `upperSpineSet` loss
            obtain ⟨τ, hτ_Ico, hloss⟩ :=
              (upperSpineSet_transition_between hValid proc ℓ X hX hp
                hidag_start (le_of_lt hidag_lt) histar_empty hrc_gt_Sp).2
                hrc_U_idag hrc_not_U_istar
            have hτ_s : tStart ≤ τ := le_trans hidag_start (Finset.mem_Ico.mp hτ_Ico).1
            have hτ_e : τ < tEmpty := lt_trans (Finset.mem_Ico.mp hτ_Ico).2 histar_empty
            have hτ_len : τ < proc.steps.length := lt_of_lt_of_le hτ_e htEmpty_len
            obtain ⟨_, _, ⟨m₀, hm₀_Sp, hm₀_min, _⟩, _, _⟩ := haw τ hτ_s hτ_e
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨τ, hτ_len, m₀, hm₀_Sp, rc c, hrc_Fin, hm₀_min, hloss⟩))))
      · -- Class A: `c ∉ leftSpine G_idag`
        obtain ⟨τ, hτ_Ico, c', hc'_Icc, hev⟩ :=
          phaseSummaryBST_eviction_in_Ip h_3_1 hValid proc ℓ X hX hp
            hidag_start (le_of_lt hidag_empty) hc_pi0 hc_Gidag
        have hτ_s : tStart ≤ τ := (Finset.mem_Ico.mp hτ_Ico).1
        have hτ_idag : τ < idag := (Finset.mem_Ico.mp hτ_Ico).2
        have hτ_e : τ < tEmpty := lt_trans hτ_idag hidag_empty
        have hτ_len : τ < proc.steps.length := lt_of_lt_of_le hτ_e htEmpty_len
        obtain ⟨_, _, ⟨m₀, hm₀_Sp, hm₀_min, _⟩, _, hpop_Sp⟩ := haw τ hτ_s hτ_e
        rcases hev with ⟨u, v, hop_uprot, _, hv_Sc⟩ | ⟨e, he_rInt, he_step, hex_Sc', hey_Sc⟩
        · -- Subcase A1 (`.upperRot u v`)
          exact Or.inl ⟨τ, hτ_len, m₀, hm₀_Sp, u, v, hm₀_min, hop_uprot, hv_Sc⟩
        · -- Subcase A2 (`e ∈ proc.rInt`, `e.stepIdx = τ < idag`)
          obtain ⟨hτ_e_lt, _, hop_e_raw, _⟩ := (mem_rInt_iff proc e).mp he_rInt
          have hop_e : proc.steps[τ]? = some (.pop e.s) := by
            rw [← he_step]; exact (List.getElem?_eq_getElem hτ_e_lt).trans (congrArg some hop_e_raw)
          have hes_Sp : e.s ∈ (subblock1 subs p).toFinset := (hpop_Sp e.s hop_e).1
          have hc'_pK : c' ∈ Finset.Icc (p + 1) K_X :=
            Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hc'_Icc).1,
              by have := (Finset.mem_Icc.mp hc'_Icc).2; have := (Finset.mem_Icc.mp hc_pK).2; omega⟩
          have hc_c'K : c ∈ Finset.Icc (c' + 1) K_X :=
            Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc'_Icc).2; have := (Finset.mem_Icc.mp hc'_Icc).1; omega,
              (Finset.mem_Icc.mp hc_pK).2⟩
          obtain ⟨hintra, hvxp_c'⟩ := same_scale_intra_or_vXp hValid proc ℓ X hX hp hc'_pK hc_c'K
            he_rInt hes_Sp (he_step ▸ hτ_e) hex_Sc' hey_Sc
          have hz_le_Sc : e.z ≤ (subblock1 subs c).hi := by
            by_contra hz_gt
            have hz_gt' : (subblock1 subs c).hi < e.z := Nat.lt_of_not_le hz_gt
            obtain ⟨he_vXp, hc'_Fp⟩ := hvxp_c' hz_gt'
            have hc'_lt_c : c' < c := by have := (Finset.mem_Icc.mp hc_c'K).1; omega
            have hc'_le_ca : c' ≤ c_a := hFp_lt_cb c' hc'_Fp (lt_trans hc'_lt_c hc_lt_cb)
            rcases eq_or_lt_of_le hc'_le_ca with heq_c' | hc'_lt_ca
            · -- `c' = c_a`: contradicts `e_a` being chronologically first in `vXp` on `S_{c_a}`!
              subst heq_c'
              obtain ⟨e_a', _, _, _, _, huniq_a, hmin_a⟩ :=
                leadExit_unique_and_popKey hValid proc ℓ X hX p c_a ha_Fp
              have hea'_eq : e_a' = e_a := (huniq_a e_a hea_lead hea_x).symm
              have hes_le : e_a.s ≤ e.s := hea'_eq ▸ (hmin_a e he_vXp hex_Sc').1
              have he_s_Icc := (hrInt_basic e he_rInt).1
              have he_step_eq := (hrInt_basic e he_rInt).2.1
              have hidag_le_τ : idag ≤ τ := by
                dsimp [idag]; rw [hkey_a, ← he_step, he_step_eq]
                exact (hpop_mono e_a.s (hrInt_basic e_a hea_rInt).1 e.s he_s_Icc).2.mp hes_le
              omega
            · -- `c' < c_a`: contradicts `h_freeze` at `idag`!
              have hca_pK : c_a ∈ Finset.Icc (p + 1) K_X :=
                hG0_bst_keys.2 ▸ (mem_iff_mem_keyFinset G₀ _).mp
                  (mem_of_mem_leftSpine (hca_eq ▸ List.getElem_mem ha_lt))
              have hlt_c'ca := hsub_lt c' c_a (by have := (Finset.mem_Icc.mp hc'_pK).1; omega)
                hc'_lt_ca (Finset.mem_Icc.mp hca_pK).2
              have hlt_cac := hsub_lt c_a c (by have := (Finset.mem_Icc.mp hca_pK).1; omega)
                hca_lt_c (Finset.mem_Icc.mp hc_pK).2
              have hc_1K : c ∈ Finset.Icc 1 K_X :=
                Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc_pK).1; omega, (Finset.mem_Icc.mp hc_pK).2⟩
              have hex_lt_xa : e.x < e_a.x :=
                lt_of_le_of_lt (Finset.mem_Icc.mp hex_Sc').2
                  (lt_of_lt_of_le hlt_c'ca (Finset.mem_Icc.mp hea_x).1)
              have hxa_lt_ez : e_a.x < e.z :=
                lt_of_le_of_lt (Finset.mem_Icc.mp hea_x).2
                  (lt_of_lt_of_le hlt_cac (le_trans (hsub_c c hc_1K).2.2.2.1 (le_of_lt hz_gt')))
              have hc'_1K : c' ∈ Finset.Icc 1 K_X :=
                Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hc'_pK).1; omega, (Finset.mem_Icc.mp hc'_pK).2⟩
              have hsmax_Icc : sMax proc (subblock1 subs p) ∈ Finset.Icc 1 P :=
                Finset.mem_Icc.mpr ⟨by omega,
                  le_trans hsmax_Sphi (le_trans (hsub_c p (Finset.mem_Icc.mpr ⟨hp1, le_of_lt hp_lt_K⟩)).2.2.2.2.1 hXP)⟩
              have hex_Icc : e.x ∈ Finset.Icc 1 P :=
                Finset.mem_Icc.mpr ⟨le_trans hX1 (le_trans (hsub_c c' hc'_1K).2.2.1 (Finset.mem_Icc.mp hex_Sc').1),
                  le_trans (Finset.mem_Icc.mp hex_Sc').2 (le_trans (hsub_c c' hc'_1K).2.2.2.2.1 hXP)⟩
              have hsmax_lt_ex : sMax proc (subblock1 subs p) < e.x :=
                lt_of_le_of_lt hsmax_Sphi
                  (lt_of_lt_of_le (hsub_lt p c' hp1 (Finset.mem_Icc.mp hc'_pK).1 (Finset.mem_Icc.mp hc'_pK).2)
                    (Finset.mem_Icc.mp hex_Sc').1)
              have hpop_smax_lt : proc.popStepIdx (sMax proc (subblock1 subs p)) < proc.popStepIdx e.x :=
                (hpop_mono _ hsmax_Icc _ hex_Icc).1.mp hsmax_lt_ex
              have hidag_le_popx : idag ≤ proc.popStepIdx e.x := by
                change idag < proc.popStepIdx (sMax proc (subblock1 subs p)) + 1 at hidag_empty
                omega
              have hidag_in_Icc : idag ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x) :=
                Finset.mem_Icc.mpr ⟨by omega, hidag_le_popx⟩
              have hxa_ls_idag : e_a.x ∈ leftSpine (proc.treeAt idag) :=
                hra_eq ▸ (hcorr_a c_a (Finset.mem_Icc.mpr ⟨le_rfl, (Finset.mem_Icc.mp hca_pK).2⟩)).2.2.1.mp hca_ls_idag
              exact h_freeze e he_rInt idag hidag_in_Icc e_a.x hxa_ls_idag ⟨hex_lt_xa, hxa_lt_ez⟩
          exact Or.inr (Or.inl ⟨e, hintra hz_le_Sc, hes_Sp, hey_Sc⟩)
  -- Conclude `g - 3 ≤ (gapWitnessSet ∩ gapSet).card`!
  have hcard_le : gapSet.card ≤
      (gapWitnessSet P T proc chain ℓ X p ∩ gapSet).card +
        excl1.card + excl2.card + excl3.card := by
    calc gapSet.card
        ≤ ((gapWitnessSet P T proc chain ℓ X p ∩ gapSet) ∪ (excl1 ∪ excl2 ∪ excl3)).card :=
          Finset.card_le_card hcover_gap
      _ ≤ (gapWitnessSet P T proc chain ℓ X p ∩ gapSet).card + (excl1 ∪ excl2 ∪ excl3).card :=
          Finset.card_union_le _ _
      _ ≤ (gapWitnessSet P T proc chain ℓ X p ∩ gapSet).card + ((excl1 ∪ excl2).card + excl3.card) :=
          Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ ≤ (gapWitnessSet P T proc chain ℓ X p ∩ gapSet).card + (excl1.card + excl2.card + excl3.card) :=
          Nat.add_le_add_left (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
      _ = (gapWitnessSet P T proc chain ℓ X p ∩ gapSet).card +
            excl1.card + excl2.card + excl3.card := by omega
  omega

private theorem card_le_of_injOn {α β : Type*}
    {s : Finset α} {t : Finset β} (f : α → β)
    (hmaps : ∀ x ∈ s, f x ∈ t)
    (hinj : ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂) :
    s.card ≤ t.card := by
  classical
  have hinj' : Set.InjOn f (s : Set α) := fun x₁ hx₁ x₂ hx₂ h => hinj x₁ hx₁ x₂ hx₂ h
  rw [← Finset.card_image_of_injOn hinj']
  exact Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)

private theorem card_range_filter_list {α : Type*} (xs : List α) (f : α → Bool) :
    ((Finset.range xs.length).filter (fun i => (xs[i]?.elim false f) = true)).card =
      (xs.filter f).length := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton rest a ih =>
    simp only [List.length_append, List.length_singleton, List.filter_append, List.filter_cons,
      List.filter_nil]
    rw [Finset.range_add_one, Finset.filter_insert]
    have hcongr : (Finset.range rest.length).filter (fun i => ((rest ++ [a])[i]?.elim false f) = true) =
        (Finset.range rest.length).filter (fun i => (rest[i]?.elim false f) = true) := by
      refine Finset.filter_congr (fun i hi => ?_)
      rw [List.getElem?_append_left (Finset.mem_range.mp hi)]
    rw [hcongr]
    have hlast : (rest ++ [a])[rest.length]? = some a := by
      rw [List.getElem?_append_right le_rfl, Nat.sub_self]; rfl
    have hnot : rest.length ∉
        (Finset.range rest.length).filter (fun i => (rest[i]?.elim false f) = true) := by
      intro hm
      exact absurd (Finset.mem_range.mp (Finset.mem_filter.mp hm).1) (lt_irrefl _)
    rw [hlast]
    cases hfa : f a
    · simp [hfa, ih]
    · simp only [Option.elim_some, hfa, ↓reduceIte, List.length_singleton]
      rw [← Finset.singleton_union,
          Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hnot),
          Finset.card_singleton, ih]
      omega

private theorem filter_or_length {α : Type*} (xs : List α) (f₁ f₂ : α → Bool)
    (hdisj : ∀ a, ¬ (f₁ a = true ∧ f₂ a = true)) :
    (xs.filter f₁).length + (xs.filter f₂).length =
      (xs.filter (fun a => f₁ a || f₂ a)).length := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    have hna := hdisj a
    cases h1 : f₁ a <;> cases h2 : f₂ a
    · simp [h1, h2, ih]
    · simp [h1, h2]; omega
    · simp [h1, h2]; omega
    · exact absurd ⟨h1, h2⟩ hna

private theorem kL_lt_two_P {P : ℕ} (hP : 1 ≤ P) (proc : FoldedPopProcess P) :
    proc.kRot ≤ proc.kL ∧ proc.kL < 2 * P ∧
    proc.kL = (proc.steps.filter (fun | .shift => true | .upperRot _ _ => true | _ => false)).length := by
  have hkl_eq : proc.kL =
      (proc.steps.filter (fun | .shift => true | .upperRot _ _ => true | _ => false)).length := by
    unfold FoldedPopProcess.kL FoldedPopProcess.kShift FoldedPopProcess.kRot
    have hor := filter_or_length proc.steps
      (fun | .shift => true | _ => false)
      (fun | .upperRot _ _ => true | _ => false)
      (by intro op; cases op <;> simp)
    have hfun : (fun a : FoldedOp =>
        (match a with | .shift => true | _ => false) ||
        (match a with | .upperRot _ _ => true | _ => false)) =
        (fun | .shift => true | .upperRot _ _ => true | _ => false) := by
      funext op; cases op <;> rfl
    rw [hfun] at hor
    exact hor
  have hkrot_le : proc.kRot ≤ proc.kL := by unfold FoldedPopProcess.kL; omega
  rcases proc.hKLBound with ⟨rfl, _⟩ | ⟨_, hlt⟩
  · omega
  · exact ⟨hkrot_le, hkl_eq ▸ hlt, hkl_eq⟩

private theorem sum_toFinset_eq_map_sum {α : Type*} [DecidableEq α] (f : α → ℕ) :
    ∀ {xs : List α}, xs.Nodup → ∑ x ∈ xs.toFinset, f x = (xs.map f).sum
  | [], _ => by simp
  | x :: xs, hnd => by
    obtain ⟨hx_not, hnd_xs⟩ := List.nodup_cons.mp hnd
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    rw [Finset.sum_insert (mt List.mem_toFinset.mp hx_not), sum_toFinset_eq_map_sum f hnd_xs]

private theorem pairwise_hi_lt_lo_nodup :
    ∀ {bs : List IntervalBlock}, (∀ B ∈ bs, B.lo ≤ B.hi) →
      bs.Pairwise (fun B₁ B₂ => B₁.hi < B₂.lo) → bs.Nodup
  | [], _, _ => .nil
  | B :: rest, hle, hpw => by
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
    refine List.nodup_cons.mpr ⟨fun hmem => ?_,
      pairwise_hi_lt_lo_nodup (fun B' hB' => hle B' (List.mem_cons_of_mem _ hB')) htail⟩
    have hlt := hhead B hmem
    have hleB := hle B List.mem_cons_self
    omega

private theorem gapWitnessSet_global
    (h_5_2 : ∀ {M : ℕ} (P : ℕ), 1 ≤ P → 1 ≤ M →
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
            2 * P + (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum)
    (h_5_3 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
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
        (ee.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ))
    (h_5_4 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        let chain := scaleTreePartitionChain T P M
        (b3Intra P proc chain).card ≤ 2 * P + proc.kRot + (eEnter P T proc chain).card ∧
        ((b3Intra P proc chain).card : ℝ) < (151 : ℝ) / 25 * (P : ℝ) ∧
        (b3Intra P proc chain).card < 7 * P)
    (h_5_7 : ∀ (P r M : ℕ) (T : ScaleTree),
      ValidScaleTree P r M T → ∀ (proc : FoldedPopProcess P)
      (ℓ : Fin M) (X : IntervalBlock), X ∈ scaleTreePartitionChain T P M ℓ.castSucc →
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
            topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G))))
    {P r M : ℕ} {T : ScaleTree}
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    let totalU := ∑ ℓ : Fin M,
      ((chain ℓ.castSucc).map (fun X =>
        let subs := childSubblocks (chain ℓ.succ) X
        ∑ p ∈ Finset.Icc 1 (subs.length - 1),
          (gapWitnessSet P T proc chain ℓ X p).card)).sum
    totalU ≤ 2 * (b3Intra P proc chain).card + (s1Set P T proc chain).card +
               (bLeafPre P proc chain).card + 2 * proc.kL + P ∧
    totalU < 20 * P := by
  classical
  dsimp only
  set chain := scaleTreePartitionChain T P M
  set totalU := ∑ ℓ : Fin M,
    ((chain ℓ.castSucc).map (fun X =>
      let subs := childSubblocks (chain ℓ.succ) X
      ∑ p ∈ Finset.Icc 1 (subs.length - 1),
        (gapWitnessSet P T proc chain ℓ X p).card)).sum
  have hChain := validScaleTree_chain hValid
  have hP : 1 ≤ P := hValid.1
  have hM : 1 ≤ M := hValid.2.1.2.1
  obtain ⟨hkRot_le_kL, hkL_lt, hkL_eq⟩ := kL_lt_two_P hP proc
  -- Collect all witness quadruples `(ℓ, X, p, c)` into a single `Finset`
  let allWitnesses : Finset (Fin M × IntervalBlock × ℕ × ℕ) :=
    Finset.univ.biUnion (fun ℓ : Fin M =>
      (chain ℓ.castSucc).toFinset.biUnion (fun X =>
        let subs := childSubblocks (chain ℓ.succ) X
        (Finset.Icc 1 (subs.length - 1)).biUnion (fun p =>
          (gapWitnessSet P T proc chain ℓ X p).image (fun c => (ℓ, X, p, c)))))
  have hall_card : allWitnesses.card = totalU := by
    dsimp only [allWitnesses, totalU]
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      have hPart := hChain.2.2.1 ℓ.castSucc
      have hnd : (chain ℓ.castSucc).Nodup :=
        pairwise_hi_lt_lo_nodup (fun B hB => (hPart.1 B hB).2.1)
          (consecutiveBlocks_pairwise (fun B hB => (hPart.1 B hB).2.1) hPart.2.1)
      rw [Finset.card_biUnion]
      · rw [← sum_toFinset_eq_map_sum _ hnd]
        refine Finset.sum_congr rfl (fun X _ => ?_)
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl (fun p _ => ?_)
          exact Finset.card_image_of_injective _ (fun c₁ c₂ h => by injection h with _ h2; injection h2 with _ h3; injection h3)
        · intro p₁ _ p₂ _ hpne
          refine Finset.disjoint_left.mpr (fun w hw₁ hw₂ => ?_)
          obtain ⟨c₁, _, rfl⟩ := Finset.mem_image.mp hw₁
          obtain ⟨c₂, _, heq⟩ := Finset.mem_image.mp hw₂
          injection heq with _ h2; injection h2 with _ h3; injection h3 with hp_eq _
          exact hpne hp_eq.symm
      · intro X₁ _ X₂ _ hXne
        refine Finset.disjoint_left.mpr (fun w hw₁ hw₂ => ?_)
        obtain ⟨p₁, _, hw₁'⟩ := Finset.mem_biUnion.mp hw₁
        obtain ⟨c₁, _, rfl⟩ := Finset.mem_image.mp hw₁'
        obtain ⟨p₂, _, hw₂'⟩ := Finset.mem_biUnion.mp hw₂
        obtain ⟨c₂, _, heq⟩ := Finset.mem_image.mp hw₂'
        injection heq with _ h2; injection h2 with hX_eq _
        exact hXne hX_eq.symm
    · intro ℓ₁ _ ℓ₂ _ hℓne
      refine Finset.disjoint_left.mpr (fun w hw₁ hw₂ => ?_)
      obtain ⟨X₁, _, hw₁'⟩ := Finset.mem_biUnion.mp hw₁
      obtain ⟨p₁, _, hw₁''⟩ := Finset.mem_biUnion.mp hw₁'
      obtain ⟨c₁, _, rfl⟩ := Finset.mem_image.mp hw₁''
      obtain ⟨X₂, _, hw₂'⟩ := Finset.mem_biUnion.mp hw₂
      obtain ⟨p₂, _, hw₂''⟩ := Finset.mem_biUnion.mp hw₂'
      obtain ⟨c₂, _, heq⟩ := Finset.mem_image.mp hw₂''
      injection heq with hℓ_eq _
      exact hℓne hℓ_eq.symm
  -- Unpack structural properties of any `w ∈ allWitnesses`
  have mem_allWitnesses : ∀ {w : Fin M × IntervalBlock × ℕ × ℕ}, w ∈ allWitnesses →
      w.2.1 ∈ chain w.1.castSucc ∧
      w.2.2.1 ∈ Finset.Icc 1 ((childSubblocks (chain w.1.succ) w.2.1).length - 1) ∧
      w.2.2.2 ∈ Finset.Icc (w.2.2.1 + 1) (childSubblocks (chain w.1.succ) w.2.1).length ∧
      (isWitA1 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 ∨
       isWitA2 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 ∨
       isWitB1 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 ∨
       isWitB2 P T proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 ∨
       isWitC1 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 ∨
       isWitC2 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2) := by
    intro w hw
    obtain ⟨ℓ, _, hw₁⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨X, hX_fin, hw₂⟩ := Finset.mem_biUnion.mp hw₁
    obtain ⟨p, hp, hw₃⟩ := Finset.mem_biUnion.mp hw₂
    obtain ⟨c, hc_U, rfl⟩ := Finset.mem_image.mp hw₃
    have hX : X ∈ chain ℓ.castSucc := List.mem_toFinset.mp hX_fin
    unfold gapWitnessSet at hc_U
    simp only [hX, hp, and_self, ↓reduceIte,
      Finset.mem_filter, Finset.mem_sdiff, List.mem_toFinset] at hc_U
    rcases hc_U with ⟨⟨hc_pi0, _⟩, hdisj⟩
    obtain ⟨_, h57_p, _⟩ := h_5_7 P r M T hValid proc ℓ X hX
    obtain ⟨htStart_tau, htau_tEnd, hG_bst_keys, _, _⟩ := h57_p p hp
    have hG0_keys := (hG_bst_keys (proc.popStepIdx (subblock1 (childSubblocks (chain ℓ.succ) X) p).lo)
      (Finset.mem_Icc.mpr ⟨le_rfl, le_trans htStart_tau htau_tEnd⟩)).2
    have hc_Icc : c ∈ Finset.Icc (p + 1) (childSubblocks (chain ℓ.succ) X).length :=
      hG0_keys ▸ (mem_iff_mem_keyFinset _ c).mp (mem_of_mem_leftSpine hc_pi0)
    exact ⟨hX, hp, hc_Icc, hdisj⟩
  have pin_w : ∀ {w₁ w₂ : Fin M × IntervalBlock × ℕ × ℕ} {u v : ℕ},
      w₁ ∈ allWitnesses → w₂ ∈ allWitnesses →
      u ∈ (subblock1 (childSubblocks (chain w₁.1.succ) w₁.2.1) w₁.2.2.1).toFinset →
      u ∈ (subblock1 (childSubblocks (chain w₂.1.succ) w₂.2.1) w₂.2.2.1).toFinset →
      v ∈ (subblock1 (childSubblocks (chain w₁.1.succ) w₁.2.1) w₁.2.2.2).toFinset →
      v ∈ (subblock1 (childSubblocks (chain w₂.1.succ) w₂.2.1) w₂.2.2.2).toFinset →
      w₁ = w₂ := by
    rintro ⟨ℓ₁, X₁, p₁, c₁⟩ ⟨ℓ₂, X₂, p₂, c₂⟩ u v hw₁ hw₂ hu₁ hu₂ hv₁ hv₂
    obtain ⟨hX₁, hp₁, hc₁, _⟩ := mem_allWitnesses hw₁
    obtain ⟨hX₂, hp₂, hc₂, _⟩ := mem_allWitnesses hw₂
    exact pin_witness_coords_eq hValid hX₁ hX₂ hp₁ hp₂ hc₁ hc₂ hu₁ hu₂ hv₁ hv₂
  -- Partition/cover `allWitnesses` by the 6 witness classes
  let WA1 := allWitnesses.filter (fun w => isWitA1 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2)
  let WA2 := allWitnesses.filter (fun w => isWitA2 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2)
  let WB1 := allWitnesses.filter (fun w => isWitB1 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2)
  let WB2 := allWitnesses.filter (fun w => isWitB2 P T proc chain w.1 w.2.1 w.2.2.1 w.2.2.2)
  let WC1 := allWitnesses.filter (fun w => isWitC1 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2)
  let WC2 := allWitnesses.filter (fun w => isWitC2 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2)
  have hcover_all : allWitnesses ⊆ WA1 ∪ (WA2 ∪ (WB1 ∪ (WB2 ∪ (WC1 ∪ WC2)))) := by
    intro w hw
    rcases (mem_allWitnesses hw).2.2.2 with h1 | h2 | h3 | h4 | h5 | h6
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h2⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h3⟩)))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h4⟩))))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h5⟩)))))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, h6⟩)))))
  have hall_sum : allWitnesses.card ≤
      WA1.card + WA2.card + WB1.card + WB2.card + WC1.card + WC2.card := by
    have h1 := Finset.card_le_card hcover_all
    have h2 := Finset.card_union_le WA1 (WA2 ∪ (WB1 ∪ (WB2 ∪ (WC1 ∪ WC2))))
    have h3 := Finset.card_union_le WA2 (WB1 ∪ (WB2 ∪ (WC1 ∪ WC2)))
    have h4 := Finset.card_union_le WB1 (WB2 ∪ (WC1 ∪ WC2))
    have h5 := Finset.card_union_le WB2 (WC1 ∪ WC2)
    have h6 := Finset.card_union_le WC1 WC2
    omega
  -- 1. Bound `WA1.card ≤ proc.kL`
  let uprotFin : Finset ℕ := (Finset.range proc.steps.length).filter (fun τ =>
    (proc.steps[τ]?.elim false (fun | .upperRot _ _ => true | _ => false)) = true)
  have huprot_card : uprotFin.card = proc.kRot :=
    card_range_filter_list proc.steps (fun | .upperRot _ _ => true | _ => false)
  have hWA1_card : WA1.card ≤ proc.kL := by
    refine le_trans (card_le_of_injOn
      (fun w => if h : isWitA1 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 then Classical.choose h else 0)
      (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ hfeq => ?_)) (huprot_card ▸ hkRot_le_kL)
    · obtain ⟨_, hwA1⟩ := Finset.mem_filter.mp hw
      simp only [hwA1, ↓reduceDIte]
      obtain ⟨hτ_lt, _, _, _, _, _, hop, _⟩ := Classical.choose_spec hwA1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hτ_lt, by rw [hop]; rfl⟩
    · obtain ⟨hw₁_all, hw₁_A1⟩ := Finset.mem_filter.mp hw₁
      obtain ⟨hw₂_all, hw₂_A1⟩ := Finset.mem_filter.mp hw₂
      simp only [hw₁_A1, hw₂_A1, ↓reduceDIte] at hfeq
      obtain ⟨_, m₁, hm₁, u₁, v₁, hmin₁, hop₁, hv₁⟩ := Classical.choose_spec hw₁_A1
      obtain ⟨_, m₂, hm₂, u₂, v₂, hmin₂, hop₂, hv₂⟩ := Classical.choose_spec hw₂_A1
      rw [← hfeq] at hmin₂ hop₂
      rw [hmin₁] at hmin₂; injection hmin₂ with hm_eq; subst hm_eq
      rw [hop₁] at hop₂; injection hop₂ with hrot_eq; injection hrot_eq with _ hv_eq; subst hv_eq
      exact pin_w hw₁_all hw₂_all hm₁ hm₂ hv₁ hv₂
  -- 2. Bound `WA2.card ≤ (b3Intra P proc chain).card`
  let dfltRot : InternalPopRot := ⟨0, 0, 0, 0, 0, 0, 0⟩
  have hWA2_card : WA2.card ≤ (b3Intra P proc chain).card := by
    refine card_le_of_injOn
      (fun w => if h : isWitA2 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 then Classical.choose h else dfltRot)
      (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ hfeq => ?_)
    · obtain ⟨_, hwA2⟩ := Finset.mem_filter.mp hw
      simp only [hwA2, ↓reduceDIte]
      exact (Classical.choose_spec hwA2).1
    · obtain ⟨hw₁_all, hw₁_A2⟩ := Finset.mem_filter.mp hw₁
      obtain ⟨hw₂_all, hw₂_A2⟩ := Finset.mem_filter.mp hw₂
      simp only [hw₁_A2, hw₂_A2, ↓reduceDIte] at hfeq
      obtain ⟨_, hs₁, hy₁⟩ := Classical.choose_spec hw₁_A2
      obtain ⟨_, hs₂, hy₂⟩ := Classical.choose_spec hw₂_A2
      rw [← hfeq] at hs₂ hy₂
      exact pin_w hw₁_all hw₂_all hs₁ hs₂ hy₁ hy₂
  -- 3. Bound `WB1.card ≤ (b3Intra P proc chain).card`
  have hWB1_card : WB1.card ≤ (b3Intra P proc chain).card := by
    refine card_le_of_injOn
      (fun w => if h : isWitB1 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 then Classical.choose h else dfltRot)
      (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ hfeq => ?_)
    · obtain ⟨_, hwB1⟩ := Finset.mem_filter.mp hw
      simp only [hwB1, ↓reduceDIte]
      exact (Classical.choose_spec hwB1).1
    · obtain ⟨hw₁_all, hw₁_B1⟩ := Finset.mem_filter.mp hw₁
      obtain ⟨hw₂_all, hw₂_B1⟩ := Finset.mem_filter.mp hw₂
      simp only [hw₁_B1, hw₂_B1, ↓reduceDIte] at hfeq
      obtain ⟨_, hs₁, hx₁⟩ := Classical.choose_spec hw₁_B1
      obtain ⟨_, hs₂, hx₂⟩ := Classical.choose_spec hw₂_B1
      rw [← hfeq] at hs₂ hx₂
      exact pin_w hw₁_all hw₂_all hs₁ hs₂ hx₁ hx₂
  -- 4. Bound `WB2.card ≤ (s1Set P T proc chain).card + (bLeafPre P proc chain).card`
  have hWB2_card : WB2.card ≤ (s1Set P T proc chain).card + (bLeafPre P proc chain).card := by
    refine le_trans (card_le_of_injOn
      (fun w => if h : isWitB2 P T proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 then Classical.choose h else dfltRot)
      (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ hfeq => ?_)) (Finset.card_union_le _ _)
    · obtain ⟨_, hwB2⟩ := Finset.mem_filter.mp hw
      simp only [hwB2, ↓reduceDIte]
      exact (Classical.choose_spec hwB2).1
    · obtain ⟨hw₁_all, hw₁_B2⟩ := Finset.mem_filter.mp hw₁
      obtain ⟨hw₂_all, hw₂_B2⟩ := Finset.mem_filter.mp hw₂
      simp only [hw₁_B2, hw₂_B2, ↓reduceDIte] at hfeq
      obtain ⟨_, hs₁, hy₁⟩ := Classical.choose_spec hw₁_B2
      obtain ⟨_, hs₂, hy₂⟩ := Classical.choose_spec hw₂_B2
      rw [← hfeq] at hs₂ hy₂
      exact pin_w hw₁_all hw₂_all hs₁ hs₂ hy₁ hy₂
  -- 5. Bound `WC1.card ≤ P`
  have hWC1_card : WC1.card ≤ P := by
    have hcard_Icc : (Finset.Icc 1 P).card = P := by rw [Nat.card_Icc]; omega
    refine le_trans (card_le_of_injOn
      (fun w => if h : isWitC1 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 then Classical.choose h else 0)
      (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ hfeq => ?_)) (le_of_eq hcard_Icc)
    · obtain ⟨_, hwC1⟩ := Finset.mem_filter.mp hw
      simp only [hwC1, ↓reduceDIte]
      exact (Classical.choose_spec hwC1).1
    · obtain ⟨hw₁_all, hw₁_C1⟩ := Finset.mem_filter.mp hw₁
      obtain ⟨hw₂_all, hw₂_C1⟩ := Finset.mem_filter.mp hw₂
      simp only [hw₁_C1, hw₂_C1, ↓reduceDIte] at hfeq
      obtain ⟨_, b₁, v₁, hs₁, hv₁, hb₁, _, hsub₁⟩ := Classical.choose_spec hw₁_C1
      obtain ⟨_, b₂, v₂, hs₂, hv₂, hb₂, _, hsub₂⟩ := Classical.choose_spec hw₂_C1
      dsimp only at hsub₁ hsub₂
      rw [← hfeq] at hs₂ hb₂ hsub₂
      rw [hb₁] at hb₂; injection hb₂ with hb_eq; subst hb_eq
      rw [hsub₁] at hsub₂; injection hsub₂ with hv_eq; subst hv_eq
      exact pin_w hw₁_all hw₂_all hs₁ hs₂ hv₁ hv₂
  -- 6. Bound `WC2.card ≤ proc.kL`
  let kLFin : Finset ℕ := (Finset.range proc.steps.length).filter (fun τ =>
    (proc.steps[τ]?.elim false (fun | .shift => true | .upperRot _ _ => true | _ => false)) = true)
  have hkLFin_card : kLFin.card = proc.kL :=
    (card_range_filter_list proc.steps (fun | .shift => true | .upperRot _ _ => true | _ => false)).trans hkL_eq.symm
  have hWC2_card : WC2.card ≤ proc.kL := by
    refine le_trans (card_le_of_injOn
      (fun w => if h : isWitC2 P proc chain w.1 w.2.1 w.2.2.1 w.2.2.2 then Classical.choose h else 0)
      (fun w hw => ?_) (fun w₁ hw₁ w₂ hw₂ hfeq => ?_)) (le_of_eq hkLFin_card)
    · obtain ⟨_, hwC2⟩ := Finset.mem_filter.mp hw
      simp only [hwC2, ↓reduceDIte]
      obtain ⟨hτ_lt, _, _, _, _, _, hcase⟩ := Classical.choose_spec hwC2
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hτ_lt, ?_⟩
      rcases hcase with ⟨hop, _⟩ | ⟨u, hop⟩ <;> (rw [hop]; rfl)
    · obtain ⟨hw₁_all, hw₁_C2⟩ := Finset.mem_filter.mp hw₁
      obtain ⟨hw₂_all, hw₂_C2⟩ := Finset.mem_filter.mp hw₂
      simp only [hw₁_C2, hw₂_C2, ↓reduceDIte] at hfeq
      obtain ⟨_, m₁, hm₁, v₁, hv₁, hmin₁, hcase₁⟩ := Classical.choose_spec hw₁_C2
      obtain ⟨_, m₂, hm₂, v₂, hv₂, hmin₂, hcase₂⟩ := Classical.choose_spec hw₂_C2
      rw [← hfeq] at hmin₂ hcase₂
      rw [hmin₁] at hmin₂; injection hmin₂ with hm_eq; subst hm_eq
      have hv_eq : v₁ = v₂ := by
        rcases hcase₁ with ⟨hop₁, hb₁⟩ | ⟨u₁, hop₁⟩ <;> rcases hcase₂ with ⟨hop₂, hb₂⟩ | ⟨u₂, hop₂⟩
        · rw [hb₁] at hb₂; injection hb₂
        · rw [hop₁] at hop₂; injection hop₂ with h; cases h
        · rw [hop₁] at hop₂; injection hop₂ with h; cases h
        · rw [hop₁] at hop₂; injection hop₂ with h; injection h
      subst hv_eq
      exact pin_w hw₁_all hw₂_all hm₁ hm₂ hv₁ hv₂
  -- Combine into `totalU ≤ ...` and `totalU < 20 * P`
  have htotalU_le : totalU ≤
      2 * (b3Intra P proc chain).card + (s1Set P T proc chain).card +
        (bLeafPre P proc chain).card + 2 * proc.kL + P := by omega
  have h_intra_real : ((b3Intra P proc chain).card : ℝ) < (151 : ℝ) / 25 * (P : ℝ) :=
    (h_5_4 P r M T hValid proc).2.1
  have h_s1_real : ((s1Set P T proc chain).card : ℝ) < (26 : ℝ) / 25 * (P : ℝ) :=
    (h_5_3 P r M T hValid proc).2.2.1
  have h_lpre_nat : (bLeafPre P proc chain).card ≤ P :=
    (h_5_2 P hP hM proc chain hChain).1
  have h_lpre_real : ((bLeafPre P proc chain).card : ℝ) ≤ (P : ℝ) := by exact_mod_cast h_lpre_nat
  have h_kL_real : (proc.kL : ℝ) < 2 * (P : ℝ) := by exact_mod_cast hkL_lt
  have h_tot_le_real : (totalU : ℝ) ≤
      2 * ((b3Intra P proc chain).card : ℝ) + ((s1Set P T proc chain).card : ℝ) +
        ((bLeafPre P proc chain).card : ℝ) + 2 * (proc.kL : ℝ) + (P : ℝ) := by
    exact_mod_cast htotalU_le
  have h_tot_lt_real : (totalU : ℝ) < 20 * (P : ℝ) := by linarith
  have h_tot_lt : totalU < 20 * P := by exact_mod_cast h_tot_lt_real
  exact ⟨htotalU_le, h_tot_lt⟩

/-- **Lemma 5.8** (`lem:b3-gaps`, Step 4: Contiguous Left-Spine Runs and Gap-Witness Sets). -/
public theorem lem_5_8_b3_gaps
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
    (h_lem_5_2 : ∀ {M : ℕ} (P : ℕ), 1 ≤ P → 1 ≤ M →
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
            2 * P + (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum)
    (h_lem_5_3 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
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
        (ee.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ))
    (h_lem_5_4 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        let chain := scaleTreePartitionChain T P M
        (b3Intra P proc chain).card ≤ 2 * P + proc.kRot + (eEnter P T proc chain).card ∧
        ((b3Intra P proc chain).card : ℝ) < (151 : ℝ) / 25 * (P : ℝ) ∧
        (b3Intra P proc chain).card < 7 * P)
    (h_lem_5_7 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P) (ℓ : Fin M) (X : IntervalBlock),
        X ∈ scaleTreePartitionChain T P M ℓ.castSucc →
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
              topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G))))
    (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (∀ (ℓ : Fin M) (X : IntervalBlock), X ∈ chain ℓ.castSucc →
      let ℓ_val := ℓ.val + 1
      let subs := childSubblocks (chain ℓ.succ) X
      ∀ p ∈ Finset.Icc 1 (subs.length - 1),
        let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
        let G_end := phaseSummaryBST P proc chain ℓ_val X p (tauEmpty proc (subblock1 subs p))
        let pi0 := leftSpine G₀
        let Fp := promotedSubblockIndices P proc chain ℓ_val X p
        1 ≤ pi0.length ∧
        (∀ c ∈ Fp, c ∈ pi0.dropLast) ∧
        (∀ a b : ℕ, a ≤ b → b + 1 < pi0.length →
          (∀ t : ℕ, a ≤ t → t ≤ b → (pi0[t]?).getD 0 ∈ Fp) →
          (a = 0 ∨ (pi0[a - 1]?).getD 0 ∉ Fp) →
          (pi0[b + 1]?).getD 0 ∉ Fp →
          (∀ t : ℕ, a ≤ t → t < b →
            leadPopKey P proc chain ℓ_val X p ((pi0[t + 1]?).getD 0) <
              leadPopKey P proc chain ℓ_val X p ((pi0[t]?).getD 0)) ∧
          (∀ t : ℕ, a ≤ t → t ≤ b →
            rightReach G₀ ((pi0[b + 1]?).getD 0) ≤ rightReach G_end ((pi0[t]?).getD 0)))) ∧
    (∃ U_witness : Fin M → IntervalBlock → ℕ → Finset ℕ,
      (∀ (ℓ : Fin M) (X : IntervalBlock), X ∈ chain ℓ.castSucc →
        let ℓ_val := ℓ.val + 1
        let subs := childSubblocks (chain ℓ.succ) X
        ∀ p ∈ Finset.Icc 1 (subs.length - 1),
          let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
          let pi0 := leftSpine G₀
          let Fp := promotedSubblockIndices P proc chain ℓ_val X p
          U_witness ℓ X p ⊆ pi0.toFinset \ Fp ∧
          ∀ a b : ℕ, a < b → b < pi0.length →
            (pi0[a]?).getD 0 ∈ Fp → (pi0[b]?).getD 0 ∈ Fp →
            (∀ t : ℕ, a < t → t < b → (pi0[t]?).getD 0 ∉ Fp) →
            scaleI T P ℓ_val < b - a - 1 →
            let g := b - a - 1
            let gapSet := (Finset.Ioo a b).image (fun t => (pi0[t]?).getD 0)
            g - 3 ≤ (U_witness ℓ X p ∩ gapSet).card ∧
            scaleI T P ℓ_val < 2 * (g - 3)) ∧
      (let totalU := ∑ ℓ : Fin M,
         ((chain ℓ.castSucc).map (fun X =>
           let subs := childSubblocks (chain ℓ.succ) X
           ∑ p ∈ Finset.Icc 1 (subs.length - 1), (U_witness ℓ X p).card)).sum
       totalU ≤ 2 * (b3Intra P proc chain).card + (s1Set P T proc chain).card +
                  (bLeafPre P proc chain).card + 2 * proc.kL + P ∧
       totalU < 20 * P)) := by
  dsimp only
  have h_freeze : ∀ e ∈ proc.rInt,
      ∀ τ ∈ Finset.Icc (e.stepIdx + 1) (proc.popStepIdx e.x),
        ∀ w ∈ leftSpine (proc.treeAt τ), ¬ (e.x < w ∧ w < e.z) :=
    fun e he => ((h_lem_3_6 P hValid.1 proc).2.1.2 e he).2.2.2.2.2.2
  refine ⟨fun ℓ X hX p hp => lem_5_8_part1 h_lem_5_7 P r M T hValid proc ℓ X hX p hp, ?_⟩
  refine ⟨gapWitnessSet P T proc (scaleTreePartitionChain T P M), ?_, ?_⟩
  · intro ℓ X hX p hp
    exact gapWitnessSet_local h_lem_3_1 h_lem_5_7 hValid proc h_freeze ℓ X hX hp
  · exact gapWitnessSet_global h_lem_5_2 h_lem_5_3 h_lem_5_4 h_lem_5_7 hValid proc


section ScaleAndPartitionHelpers

mutual
  private theorem lem59_leafEntries_pos :
      ∀ (T : ScaleTree) (entry : ℕ × List ℕ), entry ∈ T.leafEntries → ∀ c ∈ entry.2, 1 ≤ c
    | .leaf s, entry, hentry, c, hc => by
      simp [ScaleTree.leafEntries] at hentry
      rcases hentry with ⟨_, rfl⟩
      cases hc
    | .internal cs, entry, hentry, c, hc =>
      lem59_leafEntriesChildren_pos 1 cs (by omega) entry hentry c hc

  private theorem lem59_leafEntriesChildren_pos :
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
        · exact lem59_leafEntries_pos child (s, rest) hmem c hcrest
      · exact lem59_leafEntriesChildren_pos (c₀ + 1) cs (by omega) entry hrest c hc
end

private theorem lem59_foldl_weight_ge :
    ∀ (xs : List ℕ), (∀ c ∈ xs, 1 ≤ c) → ∀ (init : ℕ),
      init ≤ xs.foldl (fun w c => w * (4 * c ^ 2)) init
  | [], _, init => le_rfl
  | c :: rest, hcons, init => by
    simp only [List.foldl_cons]
    have hc : 1 ≤ c := hcons c List.mem_cons_self
    have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => hcons x (List.mem_cons_of_mem c hx)
    have h1 : 4 ≤ 4 * c ^ 2 := by nlinarith
    have h2 : init ≤ init * (4 * c ^ 2) := by nlinarith
    exact le_trans h2 (lem59_foldl_weight_ge rest hrest _)

private theorem lem59_pathWeight_pos (ξ : List ℕ) (hξ : ∀ c ∈ ξ, 1 ≤ c) :
    1 ≤ pathWeight ξ := by
  unfold pathWeight
  exact lem59_foldl_weight_ge ξ hξ 1

private theorem lem59_scaleS_pos (T : ScaleTree) (P : ℕ) (hP : 1 ≤ P) :
    ∀ ℓ : ℕ, 1 ≤ scaleS T P ℓ
  | 0 => hP
  | ℓ + 1 => by
    unfold scaleS
    have hw : 1 ≤ leafWeight T (ℓ + 1) := by
      unfold leafWeight leafAddr
      split
      · next s addr hfind =>
        have hmem := List.mem_of_find?_eq_some hfind
        exact lem59_pathWeight_pos addr (lem59_leafEntries_pos T (s, addr) hmem)
      · exact lem59_pathWeight_pos [] (by intro c hc; cases hc)
    have hsq : 1 ≤ (alpha0 (2 * scaleS T P ℓ) + 1) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    exact Nat.mul_le_mul hw hsq

private theorem lem59_leafWeight_ge_four (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓM : ℓ ≤ M) :
    4 ≤ leafWeight T ℓ := by
  rcases hValid.2.1 with ⟨_, _, _, hLeaves, hDepth⟩
  have hmem_leaves : ℓ ∈ T.leaves := by
    rw [hLeaves, List.mem_range']
    exact ⟨ℓ - 1, by omega, by omega⟩
  unfold ScaleTree.leaves at hmem_leaves
  rw [List.mem_map] at hmem_leaves
  obtain ⟨⟨s, addr0⟩, hmem0, hs0⟩ := hmem_leaves
  dsimp at hs0
  subst s
  have hex : ∃ entry ∈ T.leafEntries, (entry.1 == ℓ) = true :=
    ⟨(ℓ, addr0), hmem0, by simp⟩
  obtain ⟨⟨s', addr⟩, hfind⟩ : ∃ p, T.leafEntries.find? (fun entry => entry.1 == ℓ) = some p := by
    cases h : T.leafEntries.find? (fun entry => entry.1 == ℓ) with
    | some p => exact ⟨p, rfl⟩
    | none =>
      exfalso
      rw [List.find?_eq_none] at h
      obtain ⟨e, he1, he2⟩ := hex
      exact h e he1 he2
  unfold leafWeight leafAddr
  rw [hfind]
  have hmem := List.mem_of_find?_eq_some hfind
  have hlen : 1 ≤ addr.length := (hDepth (s', addr) hmem).1
  cases addr with
  | nil => simp at hlen
  | cons c rest =>
    unfold pathWeight
    simp only [List.foldl_cons]
    have hpos := lem59_leafEntries_pos T (s', c :: rest) hmem
    have hc : 1 ≤ c := hpos c List.mem_cons_self
    have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => hpos x (List.mem_cons_of_mem c hx)
    have h4 : 4 ≤ 1 * (4 * c ^ 2) := by nlinarith
    exact le_trans h4 (lem59_foldl_weight_ge rest hrest _)

private theorem lem59_alpha0_spec
    (hAckPow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1)
    (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ alpha0 n ∧ n ≤ ackermann (alpha0 n) 1 := by
  have hne : ({k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}).Nonempty :=
    ⟨n, hn, le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (hAckPow n hn)⟩
  exact Nat.sInf_mem hne

private theorem lem59_alpha0_ge_four
    (hAckPow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1)
    (n : ℕ) (hn : 64 ≤ n) :
    4 ≤ alpha0 n := by
  have hne : ({k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}).Nonempty :=
    ⟨n, by omega, le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (hAckPow n (by omega))⟩
  unfold alpha0 invAckermann
  apply le_csInf hne
  rintro k ⟨hk1, hkn⟩
  by_contra hlt
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · have hk : ackermann 1 1 = 2 := by decide
    rw [hk] at hkn; omega
  · have hk : ackermann 2 1 = 4 := by decide
    rw [hk] at hkn; omega
  · have hk : ackermann 3 1 = 16 := by decide
    rw [hk] at hkn; omega

private theorem lem59_scaleI_ge_five
    (hAckPow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1)
    (P r M : ℕ) (T : ScaleTree) (hValid : ValidScaleTree P r M T)
    (ℓ : Fin M) :
    5 ≤ scaleI T P (ℓ.val + 1) := by
  have hP := hValid.1
  have hHalf := hValid.2.2 ℓ
  have hw4 : 4 ≤ leafWeight T (ℓ.val + 1) :=
    lem59_leafWeight_ge_four P r M T hValid (ℓ.val + 1) (by omega) (by omega)
  have hs_pos : 1 ≤ scaleS T P ℓ.val := lem59_scaleS_pos T P hP ℓ.val
  have ha1 : 1 ≤ alpha0 (2 * scaleS T P ℓ.val) :=
    (lem59_alpha0_spec hAckPow (2 * scaleS T P ℓ.val) (by omega)).1
  have hS_next : 16 ≤ scaleS T P (ℓ.val + 1) := by
    unfold scaleS
    have hsq : 4 ≤ (alpha0 (2 * scaleS T P ℓ.val) + 1) ^ 2 := by nlinarith
    nlinarith
  have hS_prev : 32 ≤ scaleS T P ℓ.val := by omega
  have ha4 : 4 ≤ alpha0 (2 * scaleS T P ℓ.val) :=
    lem59_alpha0_ge_four hAckPow (2 * scaleS T P ℓ.val) (by omega)
  unfold scaleI
  have hsub : (ℓ.val + 1) - 1 = ℓ.val := by omega
  rw [hsub]
  omega

private theorem lem59_splitIntervalBySize_props (X : IntervalBlock) (S : ℕ)
    (hXlo : 1 ≤ X.lo) (hS : 1 ≤ S) (h2S : 2 * S ≤ X.size) :
    (splitIntervalBySize X S).length = X.size / S ∧
    ((splitIntervalBySize X S).map IntervalBlock.size).sum = X.size ∧
    (splitIntervalBySize X S).Pairwise (fun A B => A.hi < B.lo) ∧
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
  let f : ℕ → IntervalBlock := fun idx =>
    if idx + 1 < K then ⟨X.lo + idx * S, X.lo + (idx + 1) * S - 1⟩
    else ⟨X.lo + idx * S, X.hi⟩
  change ((List.range K).map f).length = K ∧
    (((List.range K).map f).map IntervalBlock.size).sum = X.size ∧
    ((List.range K).map f).Pairwise (fun A B => A.hi < B.lo) ∧
    ∀ Y ∈ (List.range K).map f,
      X.lo ≤ Y.lo ∧ Y.lo ≤ Y.hi ∧ Y.hi ≤ X.hi ∧ S ≤ Y.size ∧ Y.size < 2 * S
  have hlen : ((List.range K).map f).length = K := by simp
  have hsum : (((List.range K).map f).map IntervalBlock.size).sum = X.size := by
    have hK_eq : K = (K - 1) + 1 := by omega
    conv_lhs => rw [hK_eq, List.range_succ]
    simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
    have hprefix : ((List.range (K - 1)).map f).map IntervalBlock.size =
        List.replicate (K - 1) S := by
      rw [List.map_map]
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_range, List.getElem_replicate, Function.comp_apply]
        have hi_lt : i < K - 1 := by simpa using hi1
        have hlt : i + 1 < K := by omega
        dsimp [f]
        simp only [hlt, ↓reduceIte, IntervalBlock.size]
        have hmul : (i + 1) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
        have hstepS : i * S + S = (i + 1) * S := by ring
        have hlo_le : X.lo + i * S ≤ X.lo + (i + 1) * S - 1 := by omega
        simp only [hlo_le, ↓reduceIte]
        omega
    rw [hprefix, List.sum_replicate, smul_eq_mul]
    have hnlt : ¬ ((K - 1) + 1 < K) := by omega
    dsimp [f]
    simp only [hnlt, ↓reduceIte, IntervalBlock.size]
    have hK1S : (K - 1) * S + S = K * S := by
      calc (K - 1) * S + S = ((K - 1) + 1) * S := by ring
        _ = K * S := by rw [← hK_eq]
    have hlo_le : X.lo + (K - 1) * S ≤ X.hi := by omega
    simp only [hlo_le, hXle, ↓reduceIte]
    omega
  have hpw : ((List.range K).map f).Pairwise (fun A B => A.hi < B.lo) := by
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
    intro i j hi hj hij
    rw [List.mem_range] at hi hj
    have hlt_i : i + 1 < K := by omega
    have hmul1 : 1 * S ≤ (i + 1) * S := Nat.mul_le_mul_right S (by omega)
    have hmul2 : (i + 1) * S ≤ j * S := Nat.mul_le_mul_right S (by omega)
    dsimp [f]
    simp only [hlt_i, ↓reduceIte]
    split_ifs <;> (dsimp; omega)
  refine ⟨hlen, hsum, hpw, ?_⟩
  intro Y hY
  rw [List.mem_map] at hY
  obtain ⟨idx, hidx, rfl⟩ := hY
  rw [List.mem_range] at hidx
  dsimp [f]
  by_cases hlt : idx + 1 < K
  · simp only [hlt, ↓reduceIte]
    have hmul : (idx + 1) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
    have hstepS : idx * S + S = (idx + 1) * S := by ring
    have hlo_le_hi : X.lo + idx * S ≤ X.lo + (idx + 1) * S - 1 := by omega
    refine ⟨by omega, hlo_le_hi, by omega, ?_, ?_⟩ <;>
      · simp only [IntervalBlock.size, hlo_le_hi, ↓reduceIte]; omega
  · simp only [hlt, ↓reduceIte]
    have hidx_eq : idx = K - 1 := by omega
    subst hidx_eq
    have hK1S : (K - 1) * S + S = K * S := by
      have : (K - 1) + 1 = K := by omega
      calc (K - 1) * S + S = ((K - 1) + 1) * S := by ring
        _ = K * S := by rw [this]
    have hlo_le_hi : X.lo + (K - 1) * S ≤ X.hi := by omega
    refine ⟨by omega, hlo_le_hi, le_rfl, ?_, ?_⟩ <;>
      · simp only [IntervalBlock.size, hlo_le_hi, ↓reduceIte]; omega

private theorem lem59_pairwise_flatMap_blocks
    (xs : List IntervalBlock) (g : IntervalBlock → List IntervalBlock)
    (hpw : xs.Pairwise (fun A B => A.hi < B.lo))
    (hg_pw : ∀ X ∈ xs, (g X).Pairwise (fun A B => A.hi < B.lo))
    (hg_sub : ∀ X ∈ xs, ∀ Y ∈ g X, X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi) :
    (xs.flatMap g).Pairwise (fun A B => A.hi < B.lo) := by
  induction xs with
  | nil => simp
  | cons X rest ih =>
    rw [List.pairwise_cons] at hpw
    simp only [List.flatMap_cons, List.pairwise_append]
    refine ⟨hg_pw X List.mem_cons_self,
      ih hpw.2 (fun X' hX' => hg_pw X' (List.mem_cons_of_mem X hX'))
        (fun X' hX' => hg_sub X' (List.mem_cons_of_mem X hX')), ?_⟩
    intro Y₁ hY₁ Y₂ hY₂
    rw [List.mem_flatMap] at hY₂
    obtain ⟨X₂, hX₂, hY₂X₂⟩ := hY₂
    have h1 := (hg_sub X List.mem_cons_self Y₁ hY₁).2
    have h2 := (hg_sub X₂ (List.mem_cons_of_mem X hX₂) Y₂ hY₂X₂).1
    have h3 := hpw.1 X₂ hX₂
    omega

private theorem lem59_level_props (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) :
    ∀ k : ℕ, k ≤ M →
      let parts := scaleTreePartitionLevel T P k
      (parts.map IntervalBlock.size).sum = P ∧
      parts.Pairwise (fun A B => A.hi < B.lo) ∧
      (∀ X ∈ parts,
        1 ≤ X.lo ∧ X.lo ≤ X.hi ∧ scaleS T P k ≤ X.size ∧ X.size < 2 * scaleS T P k) := by
  rcases hValid with ⟨hP, _, hHalf⟩
  intro k
  induction k with
  | zero =>
    intro _
    have hPne : P ≠ 0 := by omega
    simp only [scaleTreePartitionLevel, hPne, ↓reduceIte, scaleS]
    have hsz : (IntervalBlock.mk 1 P).size = P := by
      simp only [IntervalBlock.size, hP, ↓reduceIte]; omega
    refine ⟨by simp [hsz], by simp, ?_⟩
    intro X hX
    simp only [List.mem_singleton] at hX
    subst hX
    exact ⟨le_rfl, hP, by omega, by omega⟩
  | succ k ih =>
    intro hkM
    obtain ⟨hSumPrev, hPwPrev, hMemPrev⟩ := ih (by omega)
    set prev := scaleTreePartitionLevel T P k
    set S := scaleS T P (k + 1)
    have hSpos : 1 ≤ S := lem59_scaleS_pos T P hP (k + 1)
    have h2S_all : ∀ X ∈ prev, 2 * S ≤ X.size := fun X hX =>
      le_trans (hHalf ⟨k, hkM⟩) (hMemPrev X hX).2.2.1
    have hSum : (((prev.flatMap (fun X => splitIntervalBySize X S)).map IntervalBlock.size)).sum = P := by
      have haux : ∀ xs : List IntervalBlock,
          (∀ X ∈ xs, 1 ≤ X.lo ∧ 2 * S ≤ X.size) →
          (((xs.flatMap (fun X => splitIntervalBySize X S)).map IntervalBlock.size)).sum =
            (xs.map IntervalBlock.size).sum := by
        intro xs; induction xs with
        | nil => simp
        | cons X rest ihx =>
          intro hxs
          simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
          have hX := hxs X List.mem_cons_self
          have hsp := (lem59_splitIntervalBySize_props X S hX.1 hSpos hX.2).2.1
          have hrest := ihx (fun Y hY => hxs Y (List.mem_cons_of_mem X hY))
          omega
      rw [haux prev (fun X hX => ⟨(hMemPrev X hX).1, h2S_all X hX⟩), hSumPrev]
    have hPw : (prev.flatMap (fun X => splitIntervalBySize X S)).Pairwise (fun A B => A.hi < B.lo) := by
      apply lem59_pairwise_flatMap_blocks prev _ hPwPrev
      · intro X hX
        exact (lem59_splitIntervalBySize_props X S (hMemPrev X hX).1 hSpos (h2S_all X hX)).2.2.1
      · intro X hX Y hY
        obtain ⟨h1, _, h3, _, _⟩ :=
          (lem59_splitIntervalBySize_props X S (hMemPrev X hX).1 hSpos (h2S_all X hX)).2.2.2 Y hY
        exact ⟨h1, h3⟩
    refine ⟨hSum, hPw, ?_⟩
    intro Y hY
    simp only [scaleTreePartitionLevel, List.mem_flatMap] at hY
    obtain ⟨X, hX, hYX⟩ := hY
    obtain ⟨h1, h2, _, h4, h5⟩ :=
      (lem59_splitIntervalBySize_props X S (hMemPrev X hX).1 hSpos (h2S_all X hX)).2.2.2 Y hYX
    exact ⟨le_trans (hMemPrev X hX).1 h1, h2, h4, h5⟩

private theorem lem59_childSubblocks_eq (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc) :
    childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X =
      splitIntervalBySize X (scaleS T P (ℓ.val + 1)) := by
  have hP := hValid.1
  have hLvl := lem59_level_props P r M T hValid ℓ.val (by omega)
  obtain ⟨_, hPw, hMem⟩ := hLvl
  set prev := scaleTreePartitionLevel T P ℓ.val
  set S := scaleS T P (ℓ.val + 1)
  have hSpos : 1 ≤ S := lem59_scaleS_pos T P hP (ℓ.val + 1)
  have h2S_all : ∀ Z ∈ prev, 2 * S ≤ Z.size := fun Z hZ =>
    le_trans (hValid.2.2 ℓ) (hMem Z hZ).2.2.1
  change (prev.flatMap (fun Z => splitIntervalBySize Z S)).filter
      (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = splitIntervalBySize X S
  have hgen : ∀ xs : List IntervalBlock,
      xs.Pairwise (fun A B => A.hi < B.lo) →
      (∀ Z ∈ xs, 1 ≤ Z.lo ∧ 2 * S ≤ Z.size) →
      (X ∈ xs → (xs.flatMap (fun Z => splitIntervalBySize Z S)).filter
          (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = splitIntervalBySize X S) ∧
      (X ∉ xs → (∀ Z ∈ xs, Z.hi < X.lo ∨ X.hi < Z.lo) →
        (xs.flatMap (fun Z => splitIntervalBySize Z S)).filter
          (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = []) := by
    intro xs; induction xs with
    | nil => simp
    | cons Z rest ih =>
      intro hpw_xs hmem_xs
      rw [List.pairwise_cons] at hpw_xs
      have hZ_props := (lem59_splitIntervalBySize_props Z S
        (hmem_xs Z List.mem_cons_self).1 hSpos (hmem_xs Z List.mem_cons_self).2).2.2.2
      have ih_rest := ih hpw_xs.2 (fun W hW => hmem_xs W (List.mem_cons_of_mem Z hW))
      constructor
      · intro hXin
        simp only [List.flatMap_cons, List.filter_append]
        rcases List.mem_cons.mp hXin with hXZ | hXrest
        · subst Z
          have hXle : X.lo ≤ X.hi := by
            have h2SX := (hmem_xs X List.mem_cons_self).2
            unfold IntervalBlock.size at h2SX
            split at h2SX <;> omega
          have hnot : X ∉ rest := fun h => by
            have := hpw_xs.1 X h
            omega
          have hself : (splitIntervalBySize X S).filter
              (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = splitIntervalBySize X S := by
            rw [List.filter_eq_self]
            intro Y hY
            obtain ⟨h1, _, h3, _, _⟩ := hZ_props Y hY
            simp only [decide_eq_true_eq]
            exact ⟨h1, h3⟩
          have htail : (rest.flatMap (fun W => splitIntervalBySize W S)).filter
              (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = [] :=
            ih_rest.2 hnot (fun W hW => Or.inr (hpw_xs.1 W hW))
          rw [hself, htail, List.append_nil]
        · have hZltX : Z.hi < X.lo := hpw_xs.1 X hXrest
          have hhead : (splitIntervalBySize Z S).filter
              (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro Y hY
            obtain ⟨_, h2, h3, _, _⟩ := hZ_props Y hY
            simp; omega
          rw [hhead, List.nil_append, ih_rest.1 hXrest]
      · intro hXnot hsep
        simp only [List.flatMap_cons, List.filter_append]
        have hhead : (splitIntervalBySize Z S).filter
            (fun Y => decide (X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro Y hY
          obtain ⟨h1, h2, h3, _, _⟩ := hZ_props Y hY
          rcases hsep Z List.mem_cons_self with hlt | hgt <;> (simp; omega)
        have hXnot_rest : X ∉ rest := fun h => hXnot (List.mem_cons_of_mem Z h)
        rw [hhead, List.nil_append,
          ih_rest.2 hXnot_rest (fun W hW => hsep W (List.mem_cons_of_mem Z hW))]
  exact (hgen prev hPw (fun Z hZ => ⟨(hMem Z hZ).1, h2S_all Z hZ⟩)).1 hX

private theorem lem59_sumKX_bound (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (ℓ : Fin M) :
    let chain := scaleTreePartitionChain T P M
    let sumKX := ((chain ℓ.castSucc).map (fun X =>
      (childSubblocks (chain ℓ.succ) X).length - 1)).sum
    let w := leafWeight T (ℓ.val + 1)
    let i_s := scaleI T P (ℓ.val + 1)
    (sumKX : ℝ) ≤ (P : ℝ) / ((w : ℝ) * (i_s : ℝ) ^ 2) := by
  intro chain sumKX w i_s
  have hP := hValid.1
  set S := scaleS T P (ℓ.val + 1)
  have hS_eq : S = w * i_s ^ 2 := by
    dsimp [S, w, i_s]
    unfold scaleS scaleI
    have hsub : (ℓ.val + 1) - 1 = ℓ.val := by omega
    rw [hsub]
  have hSpos : 1 ≤ S := lem59_scaleS_pos T P hP (ℓ.val + 1)
  have hLvl := lem59_level_props P r M T hValid ℓ.val (by omega)
  have hmul_le : S * sumKX ≤ P := by
    have hpt : ∀ X ∈ chain ℓ.castSucc,
        S * ((childSubblocks (chain ℓ.succ) X).length - 1) ≤ X.size := by
      intro X hX
      rw [lem59_childSubblocks_eq P r M T hValid ℓ X hX]
      have hXlo := (hLvl.2.2 X hX).1
      have h2S : 2 * S ≤ X.size := le_trans (hValid.2.2 ℓ) (hLvl.2.2 X hX).2.2.1
      have hlen := (lem59_splitIntervalBySize_props X S hXlo hSpos h2S).1
      rw [hlen]
      exact le_trans (Nat.mul_le_mul_left S (Nat.sub_le _ _)) (Nat.mul_div_le X.size S)
    have hlist : ∀ xs : List IntervalBlock,
        (∀ X ∈ xs, S * ((childSubblocks (chain ℓ.succ) X).length - 1) ≤ X.size) →
        S * (xs.map (fun X => (childSubblocks (chain ℓ.succ) X).length - 1)).sum ≤
          (xs.map IntervalBlock.size).sum := by
      intro xs; induction xs with
      | nil => simp
      | cons X rest ih =>
        intro hxs
        simp only [List.map_cons, List.sum_cons, Nat.mul_add]
        exact Nat.add_le_add (hxs X List.mem_cons_self)
          (ih (fun Y hY => hxs Y (List.mem_cons_of_mem X hY)))
    exact le_trans (hlist (chain ℓ.castSucc) hpt) (le_of_eq hLvl.1)
  have hSR_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hSpos
  have hmulR : (S : ℝ) * (sumKX : ℝ) ≤ (P : ℝ) := by exact_mod_cast hmul_le
  have hdivR : (sumKX : ℝ) ≤ (P : ℝ) / (S : ℝ) := by
    rw [le_div_iff₀ hSR_pos]
    linarith
  have hScast : (S : ℝ) = (w : ℝ) * (i_s : ℝ) ^ 2 := by exact_mod_cast hS_eq
  rwa [hScast] at hdivR

private theorem lem59_KX_sub_one_le_ack
    (hAckPow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1)
    (hAckStep : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      ackermann (i - 1) j ≤ ackermann i j ∧ 2 ^ j ≤ ackermann i j)
    (P r M : ℕ) (T : ScaleTree) (hValid : ValidScaleTree P r M T)
    (ℓ : Fin M) (X : IntervalBlock)
    (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc) :
    (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1 ≤
      ackermann (scaleI T P (ℓ.val + 1)) 1 := by
  have hP := hValid.1
  have hLvl := lem59_level_props P r M T hValid ℓ.val (by omega)
  set S := scaleS T P (ℓ.val + 1)
  have hSpos : 1 ≤ S := lem59_scaleS_pos T P hP (ℓ.val + 1)
  have hXlo := (hLvl.2.2 X hX).1
  have hXlt : X.size < 2 * scaleS T P ℓ.val := (hLvl.2.2 X hX).2.2.2
  have h2S : 2 * S ≤ X.size := le_trans (hValid.2.2 ℓ) (hLvl.2.2 X hX).2.2.1
  rw [lem59_childSubblocks_eq P r M T hValid ℓ X hX]
  rw [(lem59_splitIntervalBySize_props X S hXlo hSpos h2S).1]
  have hK_le : X.size / S ≤ X.size := Nat.div_le_self _ _
  set u := 2 * scaleS T P ℓ.val
  have hu_pos : 1 ≤ u := by have := lem59_scaleS_pos T P hP ℓ.val; omega
  obtain ⟨ha1, hu_ack⟩ := lem59_alpha0_spec hAckPow u hu_pos
  have hi_eq : scaleI T P (ℓ.val + 1) = alpha0 u + 1 := by
    unfold scaleI
    have hsub : (ℓ.val + 1) - 1 = ℓ.val := by omega
    rw [hsub]
  rw [hi_eq]
  have hstep := (hAckStep (alpha0 u + 1) 1 (by omega) (by omega)).1
  simp only [Nat.add_sub_cancel] at hstep
  omega

end ScaleAndPartitionHelpers

section BucketAndLeadHelpers

private theorem lem59_b3_card_split {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) :
    (b3 P proc chain).card = (b3Intra P proc chain).card + (b3Exit P proc chain).card := by
  have hdisj : Disjoint (b3Intra P proc chain) (b3Exit P proc chain) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [b3Intra, Finset.mem_filter] at h1
    simp only [b3Exit, Finset.mem_filter] at h2
    rcases h1 with ⟨_, h1⟩
    rcases h2 with ⟨_, h2⟩
    split_ifs at h1 h2 with hc
    omega
  have hunion : b3 P proc chain = b3Intra P proc chain ∪ b3Exit P proc chain := by
    ext e
    simp only [b3, b3Intra, b3Exit, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨he, hs1, heq, hs2⟩
      have hc : 1 ≤ partSepScale P chain e.x e.y ∧ partSepScale P chain e.x e.y ≤ M :=
        ⟨heq ▸ hs1, hs2⟩
      by_cases hz : e.z ≤ (blockAt (chain ⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le hc.2⟩) e.y).hi
      · left; exact ⟨he, by simp [hc, heq, hz]⟩
      · right; exact ⟨he, by simp [hc, heq, Nat.lt_of_not_ge hz]⟩
    · rintro (⟨he, h⟩ | ⟨he, h⟩)
      · split_ifs at h with hc
        exact ⟨he, h.1 ▸ hc.1, h.1, hc.2⟩
      · split_ifs at h with hc
        exact ⟨he, h.1 ▸ hc.1, h.1, hc.2⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj]

private theorem lem59_b3Exit_card_split {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) :
    (b3Exit P proc chain).card ≤
      (b3ExitPost P proc chain).card + (b3ExitAct P proc chain).card := by
  have hsub : b3Exit P proc chain ⊆ b3ExitPost P proc chain ∪ b3ExitAct P proc chain := by
    intro e he
    have he' := he
    simp only [b3Exit, Finset.mem_filter] at he'
    rcases he' with ⟨_, hc_if⟩
    split_ifs at hc_if with hc
    simp only [Finset.mem_union, b3ExitPost, b3ExitAct, Finset.mem_filter, hc.2, ↓reduceDIte]
    by_cases ht : tauEmpty proc (blockAt (chain ⟨partSepScale P chain e.x e.y, Nat.lt_succ_of_le hc.2⟩) e.s) ≤ e.stepIdx
    · exact Or.inl ⟨he, ht⟩
    · exact Or.inr ⟨he, Nat.lt_of_not_ge ht⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

private theorem lem59_foldedPopRotsAt_stepIdx (idx : ℕ) (st : BinaryTree ℕ × Option ℕ)
    (op : FoldedOp) :
    ∀ e ∈ foldedPopRotsAt idx st op, e.stepIdx = idx := by
  intro e he
  cases op with
  | pop s =>
    rcases st with ⟨t_st, _ | b⟩
    · simp [foldedPopRotsAt] at he
    · simp only [foldedPopRotsAt, List.mem_filterMap, List.mem_range] at he
      obtain ⟨i, _, hi⟩ := he
      split at hi
      · simp only [Option.some.injEq] at hi; subst hi; rfl
      · cases hi
  | _ => simp [foldedPopRotsAt] at he

private theorem lem59_collectFoldedPopRots_ge (steps : List FoldedOp) :
    ∀ (idx : ℕ) (st : BinaryTree ℕ × Option ℕ),
      ∀ e ∈ collectFoldedPopRots idx st steps, idx ≤ e.stepIdx := by
  induction steps with
  | nil => intro _ _ _ h; simp [collectFoldedPopRots] at h
  | cons op rest ih =>
    intro idx st e he
    simp only [collectFoldedPopRots, List.mem_append] at he
    rcases he with h1 | h2
    · have := lem59_foldedPopRotsAt_stepIdx idx st op e h1
      omega
    · have := ih (idx + 1) (op.step st) e h2
      omega

private theorem lem59_collectFoldedPopRots_unique (steps : List FoldedOp) :
    ∀ (idx : ℕ) (st : BinaryTree ℕ × Option ℕ),
      ∀ e₁ ∈ collectFoldedPopRots idx st steps,
      ∀ e₂ ∈ collectFoldedPopRots idx st steps,
        e₁.stepIdx = e₂.stepIdx → e₁.j = e₂.j → e₁ = e₂ := by
  induction steps with
  | nil => intro _ _ _ h; simp [collectFoldedPopRots] at h
  | cons op rest ih =>
    intro idx st e₁ he₁ e₂ he₂ hs hj
    simp only [collectFoldedPopRots, List.mem_append] at he₁ he₂
    rcases he₁ with h1 | h1 <;> rcases he₂ with h2 | h2
    · cases op with
      | pop s =>
        rcases st with ⟨t_st, _ | b⟩
        · simp [foldedPopRotsAt] at h1
        · simp only [foldedPopRotsAt, List.mem_filterMap, List.mem_range] at h1 h2
          obtain ⟨i₁, _, hi₁⟩ := h1
          obtain ⟨i₂, _, hi₂⟩ := h2
          have hj1 : e₁.j = i₁ + 1 := by
            split at hi₁
            · simp only [Option.some.injEq] at hi₁; subst hi₁; rfl
            · cases hi₁
          have hj2 : e₂.j = i₂ + 1 := by
            split at hi₂
            · simp only [Option.some.injEq] at hi₂; subst hi₂; rfl
            · cases hi₂
          have hi_eq : i₁ = i₂ := by omega
          subst hi_eq
          rw [hi₁] at hi₂
          exact Option.some.inj hi₂
      | _ => simp [foldedPopRotsAt] at h1
    · have s1 := lem59_foldedPopRotsAt_stepIdx idx st op e₁ h1
      have s2 := lem59_collectFoldedPopRots_ge rest (idx + 1) (op.step st) e₂ h2
      omega
    · have s1 := lem59_collectFoldedPopRots_ge rest (idx + 1) (op.step st) e₁ h1
      have s2 := lem59_foldedPopRotsAt_stepIdx idx st op e₂ h2
      omega
    · exact ih (idx + 1) (op.step st) e₁ h1 e₂ h2 hs hj

private theorem lem59_leadExitSet_card_le {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : ℕ) (X : IntervalBlock) (p : ℕ) :
    (leadExitSet P proc chain ℓ X p).card ≤
      (promotedSubblockIndices P proc chain ℓ X p).card := by
  unfold leadExitSet
  split_ifs with h
  · refine le_trans Finset.card_biUnion_le ?_
    calc ∑ b ∈ promotedSubblockIndices P proc chain ℓ X p, _
        ≤ ∑ _b ∈ promotedSubblockIndices P proc chain ℓ X p, 1 := by
          apply Finset.sum_le_sum
          intro b _
          rw [Finset.card_le_one]
          intro e₁ he₁ e₂ he₂
          simp only [Finset.mem_filter] at he₁ he₂
          have h12 := he₁.2 e₂ he₂.1
          have h21 := he₂.2 e₁ he₁.1
          have hstep_eq : e₁.stepIdx = e₂.stepIdx := by omega
          have hj_eq : e₁.j = e₂.j := by omega
          have hr_of_vXp : ∀ e₀ ∈ vXp P proc chain ℓ X p, e₀ ∈ proc.rInt := by
            intro e₀ hv
            unfold vXp at hv
            split_ifs at hv
            rw [Finset.mem_filter] at hv
            have hv2 := hv.1
            unfold b3ExitAct at hv2
            rw [Finset.mem_filter] at hv2
            have hv3 := hv2.1
            unfold b3Exit at hv3
            rw [Finset.mem_filter] at hv3
            exact hv3.1
          have hr1 : e₁ ∈ proc.rInt := hr_of_vXp e₁ he₁.1.1
          have hr2 : e₂ ∈ proc.rInt := hr_of_vXp e₂ he₂.1.1
          unfold FoldedPopProcess.rInt at hr1 hr2
          rw [List.mem_toFinset] at hr1 hr2
          exact lem59_collectFoldedPopRots_unique proc.steps 0 (.nil, none) e₁ hr1 e₂ hr2 hstep_eq hj_eq
      _ = (promotedSubblockIndices P proc chain ℓ X p).card := by simp
  · simp [promotedSubblockIndices, h]

private theorem lem59_reindex_weights (M : ℕ) (T : ScaleTree) :
    (∑ ℓ : Fin M, (1 : ℝ) / (leafWeight T (ℓ.val + 1) : ℝ)) =
      ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T k : ℝ) := by
  apply Finset.sum_bij (fun (ℓ : Fin M) _ => ℓ.val + 1)
  · intro ℓ _; rw [Finset.mem_Icc]; omega
  · intro ℓ₁ _ ℓ₂ _ h; ext; omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    exact ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  · intro _ _; rfl

end BucketAndLeadHelpers

section TreeSpineAndReachHelpers

private theorem lem59_mem_iff_mem_keyFinset {α : Type} [DecidableEq α]
    (t : BinaryTree α) (x : α) :
    x ∈ t ↔ x ∈ keyFinset t := by
  induction t with
  | nil =>
    simp only [keyFinset, Finset.notMem_empty, iff_false]
    intro h; cases h
  | node k l r ihl ihr =>
    simp only [keyFinset, Finset.mem_insert, Finset.mem_union, ← ihl, ← ihr, mem_node_iff]

private theorem lem59_keyFinset_eq_toKeyList_toFinset {α : Type} [DecidableEq α]
    (t : BinaryTree α) :
    keyFinset t = t.toKeyList.toFinset := by
  ext x
  rw [← lem59_mem_iff_mem_keyFinset, mem_iff_mem_toKeyList, List.mem_toFinset]

private theorem lem59_num_nodes_eq_card_keyFinset {α : Type} [LinearOrder α]
    (t : BinaryTree α) (ht : t.IsBST) :
    t.num_nodes = (keyFinset t).card := by
  rw [num_nodes_eq_length_toKeyList, lem59_keyFinset_eq_toKeyList_toFinset]
  have hpw := (SplayTree.IsBST_iff_toKeyList_sorted t).mp ht
  have hnd : t.toKeyList.Nodup := List.Pairwise.imp ne_of_lt hpw
  exact (List.toFinset_card_of_nodup hnd).symm

private theorem lem59_toKeyList_rotateRightEdge {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) :
    (rotateRightEdge t x p).toKeyList = t.toKeyList := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    unfold rotateRightEdge
    split_ifs with hlt hgt
    · simp [toKeyList, ihl]
    · simp [toKeyList, ihr]
    · cases l with
      | nil => rfl
      | node lx a b =>
        dsimp only
        split_ifs <;> simp [toKeyList, List.append_assoc]

private theorem lem59_isBST_rotateRightEdge {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) (ht : t.IsBST) :
    (rotateRightEdge t x p).IsBST :=
  SplayTree.IsBST_of_toKeyList_eq (lem59_toKeyList_rotateRightEdge t x p) ht

private theorem lem59_keyFinset_rotateRightEdge {α : Type} [LinearOrder α]
    (t : BinaryTree α) (x p : α) :
    keyFinset (rotateRightEdge t x p) = keyFinset t := by
  rw [lem59_keyFinset_eq_toKeyList_toFinset, lem59_keyFinset_eq_toKeyList_toFinset,
    lem59_toKeyList_rotateRightEdge]

private theorem lem59_mem_of_mem_leftSpine {α : Type} (t : BinaryTree α) :
    ∀ x ∈ leftSpine t, x ∈ t := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl =>
    intro x hx
    simp only [leftSpine, List.mem_append, List.mem_singleton] at hx
    rcases hx with hl | rfl
    · exact .left (ihl x hl)
    · exact .here

private theorem lem59_leftSpine_pairwise_lt {α : Type} [LinearOrder α]
    (t : BinaryTree α) (ht : t.IsBST) :
    (leftSpine t).Pairwise (· < ·) := by
  induction t with
  | nil => simp [leftSpine]
  | node k l r ihl =>
    simp only [leftSpine, List.pairwise_append, List.pairwise_singleton]
    refine ⟨ihl (IsBST_left_of_IsBST ht), trivial, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    exact lt_of_IsBST_left l k r ht (lem59_mem_of_mem_leftSpine l a ha)

private theorem lem59_snoc_inj {α : Type} {xs ys : List α} {a b : α}
    (h : xs ++ [a] = ys ++ [b]) : xs = ys ∧ a = b := by
  have hlen : xs.length = ys.length := by
    have := congrArg List.length h
    simp at this
    omega
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  exact ⟨h1, by simpa using h2⟩

private theorem lem59_spine_drop {α : Type} [LinearOrder α]
    (t : BinaryTree α) (ht : t.IsBST) (pref suff : List α) (x p : α)
    (hspine : leftSpine t = pref ++ [x, p] ++ suff) :
    leftSpine (rotateRightEdge t x p) = pref ++ [x] ++ suff := by
  induction t generalizing suff with
  | nil =>
    simp only [leftSpine] at hspine
    have hlen := congrArg List.length hspine
    simp at hlen
  | node k l r ihl =>
    simp only [leftSpine] at hspine
    rcases List.eq_nil_or_concat suff with rfl | ⟨suff', last, rfl⟩
    · simp only [List.append_nil] at hspine
      have hrew : pref ++ [x, p] = (pref ++ [x]) ++ [p] := by simp [List.append_assoc]
      rw [hrew] at hspine
      obtain ⟨hl_eq, hk_eq⟩ := lem59_snoc_inj hspine
      subst k
      cases l with
      | nil =>
        simp only [leftSpine] at hl_eq
        have hlen := congrArg List.length hl_eq
        simp at hlen
      | node lx a b =>
        simp only [leftSpine] at hl_eq
        obtain ⟨ha_eq, hlx_eq⟩ := lem59_snoc_inj hl_eq
        subst lx
        simp [rotateRightEdge, leftSpine, ha_eq]
    · rw [List.concat_eq_append] at hspine ⊢
      have hrew : pref ++ [x, p] ++ (suff' ++ [last]) = (pref ++ [x, p] ++ suff') ++ [last] := by
        simp [List.append_assoc]
      rw [hrew] at hspine
      obtain ⟨hl_eq, hk_eq⟩ := lem59_snoc_inj hspine
      subst last
      have hp_mem : p ∈ l := by
        apply lem59_mem_of_mem_leftSpine l
        rw [hl_eq]
        simp
      have hpk : p < k := lt_of_IsBST_left l k r ht hp_mem
      simp only [rotateRightEdge, hpk, ↓reduceIte, leftSpine]
      rw [ihl (IsBST_left_of_IsBST ht) suff' hl_eq]
      simp [List.append_assoc]

private theorem lem59_mem_of_maxKey?_eq_some {α : Type} :
    ∀ {t : BinaryTree α} {m : α}, t.maxKey? = some m → m ∈ t
  | .nil, _, h => by simp [BinaryTree.maxKey?] at h
  | .node k l r, m, h => by
    simp only [BinaryTree.maxKey?] at h
    cases hr : r.maxKey? with
    | none =>
      rw [hr] at h
      simp only [ Option.some.injEq ] at h
      subst h
      exact .here
    | some mr =>
      rw [hr] at h
      simp only [ Option.some.injEq ] at h
      subst h
      exact .right (lem59_mem_of_maxKey?_eq_some hr)

private theorem lem59_maxKey?_ne_none_of_node {α : Type} (k : α) (l r : BinaryTree α) :
    ∃ m, (BinaryTree.node k l r).maxKey? = some m := by
  simp only [BinaryTree.maxKey?]
  cases r.maxKey? <;> exact ⟨_, rfl⟩

private theorem lem59_le_maxKey?_of_mem {α : Type} [LinearOrder α] :
    ∀ {t : BinaryTree α}, t.IsBST → ∀ x ∈ t, ∃ m, t.maxKey? = some m ∧ x ≤ m
  | .nil, _, x, hx => by cases hx
  | .node k l r, ht, x, hx => by
    simp only [BinaryTree.maxKey?]
    cases hr : r.maxKey? with
    | none =>
      have hr_nil : r = .nil := by
        cases r with
        | nil => rfl
        | node rk rl rr =>
          obtain ⟨m, hm⟩ := lem59_maxKey?_ne_none_of_node rk rl rr
          rw [hm] at hr
          cases hr
      subst hr_nil
      refine ⟨k, rfl, ?_⟩
      rcases mem_node_iff.mp hx with rfl | hxl | hxr
      · exact le_rfl
      · exact le_of_lt (lt_of_IsBST_left l k .nil ht hxl)
      · cases hxr
    | some mr =>
      refine ⟨mr, rfl, ?_⟩
      have hmr_mem : mr ∈ r := lem59_mem_of_maxKey?_eq_some hr
      have hkmr : k < mr := gt_of_IsBST_right l k r ht hmr_mem
      rcases mem_node_iff.mp hx with rfl | hxl | hxr
      · exact le_of_lt hkmr
      · exact le_of_lt (lt_trans (lt_of_IsBST_left l k r ht hxl) hkmr)
      · obtain ⟨mr', hmr', hle⟩ := lem59_le_maxKey?_of_mem (IsBST_right_of_IsBST ht) x hxr
        rw [hr] at hmr'
        cases hmr'
        exact hle

private theorem lem59_maxKey?_eq_of_toKeyList_eq {α : Type} [LinearOrder α]
    {t₁ t₂ : BinaryTree α} (h₁ : t₁.IsBST) (h₂ : t₂.IsBST)
    (heq : t₁.toKeyList = t₂.toKeyList) :
    t₁.maxKey? = t₂.maxKey? := by
  cases hmax1 : t₁.maxKey? with
  | none =>
    have ht1 : t₁ = .nil := by
      cases t₁ with
      | nil => rfl
      | node k l r =>
        obtain ⟨m, hm⟩ := lem59_maxKey?_ne_none_of_node k l r
        rw [hm] at hmax1; cases hmax1
    subst ht1
    simp only [toKeyList_empty] at heq
    have ht2 : t₂ = .nil := eq_nil_of_toKeyList_eq_nil heq.symm
    subst ht2
    rfl
  | some m₁ =>
    have hm1_t1 : m₁ ∈ t₁ := lem59_mem_of_maxKey?_eq_some hmax1
    have hm1_t2 : m₁ ∈ t₂ := by
      rw [mem_iff_mem_toKeyList, ← heq, ← mem_iff_mem_toKeyList]
      exact hm1_t1
    obtain ⟨m₂, hmax2, hm1_le_m2⟩ := lem59_le_maxKey?_of_mem h₂ m₁ hm1_t2
    have hm2_t2 : m₂ ∈ t₂ := lem59_mem_of_maxKey?_eq_some hmax2
    have hm2_t1 : m₂ ∈ t₁ := by
      rw [mem_iff_mem_toKeyList, heq, ← mem_iff_mem_toKeyList]
      exact hm2_t2
    obtain ⟨m₁', hmax1', hm2_le_m1⟩ := lem59_le_maxKey?_of_mem h₁ m₂ hm2_t1
    rw [hmax1] at hmax1'
    cases hmax1'
    rw [hmax2]
    exact congrArg some (le_antisymm hm1_le_m2 hm2_le_m1)

private theorem lem59_maxKey?_getD_le_of_subset
    {s t : BinaryTree ℕ} (ht : t.IsBST) (hsub : ∀ z ∈ s, z ∈ t) :
    (s.maxKey?).getD 0 ≤ (t.maxKey?).getD 0 := by
  cases hs : s.maxKey? with
  | none => simp
  | some ms =>
    have hms_t : ms ∈ t := hsub ms (lem59_mem_of_maxKey?_eq_some hs)
    obtain ⟨mt, hmt, hle⟩ := lem59_le_maxKey?_of_mem ht ms hms_t
    rw [hmt]
    exact hle

private theorem lem59_mem_of_mem_subtreeAtKey {α : Type} [LinearOrder α] :
    ∀ (t : BinaryTree α) (u z : α), z ∈ subtreeAtKey t u → z ∈ t
  | .nil, _, _, hz => by simp [subtreeAtKey] at hz
  | .node k l r, u, z, hz => by
    simp only [subtreeAtKey] at hz
    split_ifs at hz with h1 h2
    · exact .left (lem59_mem_of_mem_subtreeAtKey l u z hz)
    · exact .right (lem59_mem_of_mem_subtreeAtKey r u z hz)
    · exact hz

private theorem lem59_rightReach_spine_rot
    (t : BinaryTree ℕ) (ht : t.IsBST) (pref suff : List ℕ) (x p : ℕ)
    (hspine : leftSpine t = pref ++ [x, p] ++ suff) :
    rightReach (rotateRightEdge t x p) x = rightReach t p ∧
    ∀ u : ℕ, u ≠ x → rightReach (rotateRightEdge t x p) u = rightReach t u := by
  unfold rightReach
  suffices hmax :
      (subtreeAtKey (rotateRightEdge t x p) x).maxKey? = (subtreeAtKey t p).maxKey? ∧
      ∀ u : ℕ, u ≠ x →
        (subtreeAtKey (rotateRightEdge t x p) u).maxKey? = (subtreeAtKey t u).maxKey? by
    exact ⟨congrArg (Option.getD · 0) hmax.1,
      fun u hu => congrArg (Option.getD · 0) (hmax.2 u hu)⟩
  induction t generalizing suff with
  | nil =>
    simp only [leftSpine] at hspine
    have hlen := congrArg List.length hspine
    simp at hlen
  | node k l r ihl =>
    have hl_bst : l.IsBST := IsBST_left_of_IsBST ht
    simp only [leftSpine] at hspine
    rcases List.eq_nil_or_concat suff with rfl | ⟨suff', last, rfl⟩
    · simp only [List.append_nil] at hspine
      have hrew : pref ++ [x, p] = (pref ++ [x]) ++ [p] := by simp [List.append_assoc]
      rw [hrew] at hspine
      obtain ⟨hl_eq, hk_eq⟩ := lem59_snoc_inj hspine
      subst k
      cases l with
      | nil =>
        simp only [leftSpine] at hl_eq
        have hlen := congrArg List.length hl_eq
        simp at hlen
      | node lx a b =>
        simp only [leftSpine] at hl_eq
        obtain ⟨_, hlx_eq⟩ := lem59_snoc_inj hl_eq
        subst lx
        have hxp : x < p := lt_of_IsBST_left (.node x a b) p r ht .here
        have hrot : rotateRightEdge (.node p (.node x a b) r) x p = .node x a (.node p b r) := by
          simp [rotateRightEdge]
        rw [hrot]
        constructor
        · have hs1 : subtreeAtKey (.node x a (.node p b r)) x = .node x a (.node p b r) := by
            simp [subtreeAtKey]
          have hs2 : subtreeAtKey (.node p (.node x a b) r) p = .node p (.node x a b) r := by
            simp [subtreeAtKey]
          rw [hs1, hs2]
          simp only [BinaryTree.maxKey?]
          cases r.maxKey? <;> rfl
        · intro u hux
          rcases lt_trichotomy u x with hux_lt | rfl | hxu_lt
          · have hup : u < p := lt_trans hux_lt hxp
            simp [subtreeAtKey, hux_lt, hup]
          · exact absurd rfl hux
          · have hnot_ux : ¬ (u < x) := not_lt.mpr (le_of_lt hxu_lt)
            rcases lt_trichotomy u p with hup_lt | rfl | hpu_lt
            · simp [subtreeAtKey, hnot_ux, hxu_lt, hup_lt]
            · have hnot_uu : ¬ (u < u) := lt_irrefl u
              simp only [subtreeAtKey, hnot_ux, hxp, ↓reduceIte, hnot_uu]
              simp only [BinaryTree.maxKey?]
            · have hnot_up : ¬ (u < p) := not_lt.mpr (le_of_lt hpu_lt)
              simp [subtreeAtKey, hnot_ux, hxu_lt, hnot_up, hpu_lt]
    · rw [List.concat_eq_append] at hspine
      have hrew : pref ++ [x, p] ++ (suff' ++ [last]) = (pref ++ [x, p] ++ suff') ++ [last] := by
        simp [List.append_assoc]
      rw [hrew] at hspine
      obtain ⟨hl_eq, hk_eq⟩ := lem59_snoc_inj hspine
      subst last
      have hx_mem : x ∈ l := by
        apply lem59_mem_of_mem_leftSpine l
        rw [hl_eq]; simp
      have hp_mem : p ∈ l := by
        apply lem59_mem_of_mem_leftSpine l
        rw [hl_eq]; simp
      have hxk : x < k := lt_of_IsBST_left l k r ht hx_mem
      have hpk : p < k := lt_of_IsBST_left l k r ht hp_mem
      have hrot : rotateRightEdge (.node k l r) x p = .node k (rotateRightEdge l x p) r := by
        simp [rotateRightEdge, hpk]
      rw [hrot]
      obtain ⟨ih1, ih2⟩ := ihl hl_bst suff' hl_eq
      constructor
      · simp [subtreeAtKey, hxk, hpk, ih1]
      · intro u hux
        rcases lt_trichotomy u k with huk | rfl | hku
        · simp [subtreeAtKey, huk, ih2 u hux]
        · simp [subtreeAtKey, BinaryTree.maxKey?]
        · have hnot : ¬ (u < k) := not_lt.mpr (le_of_lt hku)
          simp [subtreeAtKey, hnot, hku]

private theorem lem59_rightReach_mono_leftSpine
    (t : BinaryTree ℕ) (ht : t.IsBST) (u v : ℕ)
    (hu : u ∈ leftSpine t) (hv : v ∈ leftSpine t) (huv : u ≤ v) :
    rightReach t u ≤ rightReach t v := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · exact le_rfl
  · induction t with
    | nil => simp [leftSpine] at hu
    | node k l r ihl =>
      simp only [leftSpine, List.mem_append, List.mem_singleton] at hu hv
      have hu_l : u ∈ leftSpine l := by
        rcases hu with hul | rfl
        · exact hul
        · rcases hv with hvl | rfl
          · exfalso
            exact absurd (lt_of_IsBST_left l u r ht (lem59_mem_of_mem_leftSpine l v hvl))
              (not_lt.mpr (le_of_lt hlt))
          · exact absurd hlt (lt_irrefl _)
      have huk : u < k := lt_of_IsBST_left l k r ht (lem59_mem_of_mem_leftSpine l u hu_l)
      rcases hv with hv_l | hvk
      · have hvk : v < k := lt_of_IsBST_left l k r ht (lem59_mem_of_mem_leftSpine l v hv_l)
        unfold rightReach
        simp only [subtreeAtKey, huk, hvk, ↓reduceIte]
        exact ihl (IsBST_left_of_IsBST ht) hu_l hv_l
      · subst k
        unfold rightReach
        have hsub_u : subtreeAtKey (.node v l r) u = subtreeAtKey l u := by
          simp only [subtreeAtKey, huk, ↓reduceIte]
        have hsub_v : subtreeAtKey (.node v l r) v = .node v l r := by
          simp only [subtreeAtKey, lt_irrefl, ↓reduceIte]
        rw [hsub_u, hsub_v]
        apply lem59_maxKey?_getD_le_of_subset ht
        intro z hz
        exact .left (lem59_mem_of_mem_subtreeAtKey l u z hz)

private theorem lem59_rightReach_le_rotateRightEdge
    (t : BinaryTree ℕ) (ht : t.IsBST) (x y u : ℕ) :
    rightReach t u ≤ rightReach (rotateRightEdge t x y) u := by
  induction t with
  | nil => exact le_rfl
  | node k l r ihl ihr =>
    have hl_bst := IsBST_left_of_IsBST ht
    have hr_bst := IsBST_right_of_IsBST ht
    have ht'_bst := lem59_isBST_rotateRightEdge (.node k l r) x y ht
    unfold rotateRightEdge
    split_ifs with hyk hky
    · rcases lt_trichotomy u k with huk | rfl | hku
      · unfold rightReach
        simp only [subtreeAtKey, huk, ↓reduceIte]
        exact ihl hl_bst
      · unfold rightReach
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte, BinaryTree.maxKey?, le_rfl]
      · have hnot : ¬ (u < k) := not_lt.mpr (le_of_lt hku)
        unfold rightReach
        simp only [subtreeAtKey, hnot, hku, ↓reduceIte, le_rfl]
    · rcases lt_trichotomy u k with huk | rfl | hku
      · unfold rightReach
        simp only [subtreeAtKey, huk, ↓reduceIte, le_rfl]
      · unfold rightReach
        simp only [subtreeAtKey, lt_irrefl, ↓reduceIte]
        have heq_max : (BinaryTree.node u l r).maxKey? =
            (BinaryTree.node u l (rotateRightEdge r x y)).maxKey? := by
          apply lem59_maxKey?_eq_of_toKeyList_eq ht
          · exact SplayTree.IsBST_of_toKeyList_eq
              (by simp [toKeyList, lem59_toKeyList_rotateRightEdge]) ht
          · simp [toKeyList, lem59_toKeyList_rotateRightEdge]
        rw [heq_max]
      · have hnot : ¬ (u < k) := not_lt.mpr (le_of_lt hku)
        unfold rightReach
        simp only [subtreeAtKey, hnot, hku, ↓reduceIte]
        exact ihr hr_bst
    · have hy_eq : y = k := le_antisymm (not_lt.mp hky) (not_lt.mp hyk)
      subst hy_eq
      cases l with
      | nil => exact le_rfl
      | node lx a b =>
        dsimp only
        split_ifs with hlx
        · subst lx
          have hxy : x < y := lt_of_IsBST_left (.node x a b) y r ht .here
          have hrot_bst : (BinaryTree.node x a (.node y b r)).IsBST :=
            SplayTree.IsBST_of_toKeyList_eq (by simp [toKeyList, List.append_assoc]) ht
          rcases lt_trichotomy u x with hux | rfl | hxu
          · have huy : u < y := lt_trans hux hxy
            unfold rightReach
            simp [subtreeAtKey, hux, huy]
          · unfold rightReach
            have hs1 : subtreeAtKey (.node y (.node u a b) r) u = .node u a b := by
              simp [subtreeAtKey, hxy]
            have hs2 : subtreeAtKey (.node u a (.node y b r)) u = .node u a (.node y b r) := by
              simp [subtreeAtKey]
            rw [hs1, hs2]
            apply lem59_maxKey?_getD_le_of_subset hrot_bst
            intro z hz
            rw [mem_iff_mem_toKeyList] at hz ⊢
            simp only [toKeyList, List.mem_append, List.mem_singleton] at hz ⊢
            tauto
          · have hnot_ux : ¬ (u < x) := not_lt.mpr (le_of_lt hxu)
            rcases lt_trichotomy u y with huy | rfl | hyu
            · unfold rightReach
              simp [subtreeAtKey, hnot_ux, hxu, huy]
            · unfold rightReach
              simp [subtreeAtKey, hnot_ux, hxy, BinaryTree.maxKey?]
            · have hnot_uy : ¬ (u < y) := not_lt.mpr (le_of_lt hyu)
              unfold rightReach
              simp [subtreeAtKey, hnot_ux, hxu, hnot_uy, hyu]
        · exact le_rfl

private theorem lem59_rightRotReachable_bst_and_reach
    {t₁ t₂ : BinaryTree ℕ} (h : RightRotReachable t₁ t₂) (ht₁ : t₁.IsBST) :
    t₂.IsBST ∧ ∀ u : ℕ, rightReach t₁ u ≤ rightReach t₂ u := by
  induction h with
  | refl => exact ⟨ht₁, fun _ => le_rfl⟩
  | tail _ hstep ih =>
    obtain ⟨hb_mid, hreach_mid⟩ := ih
    rcases hstep with ⟨x, y, _, _, rfl⟩
    refine ⟨lem59_isBST_rotateRightEdge _ x y hb_mid, ?_⟩
    intro u
    exact le_trans (hreach_mid u) (lem59_rightReach_le_rotateRightEdge _ hb_mid x y u)

private def lem59_mapTree (f : ℕ → ℕ) : BinaryTree ℕ → BinaryTree ℕ
  | .nil => .nil
  | .node k l r => .node (f k) (lem59_mapTree f l) (lem59_mapTree f r)

private theorem lem59_toKeyList_mapTree (f : ℕ → ℕ) (t : BinaryTree ℕ) :
    (lem59_mapTree f t).toKeyList = t.toKeyList.map f := by
  induction t with
  | nil => rfl
  | node k l r ihl ihr =>
    simp [lem59_mapTree, toKeyList, ihl, ihr]

private theorem lem59_mapTree_sub_add (p : ℕ) :
    ∀ (t : BinaryTree ℕ), (∀ k ∈ t, p ≤ k) →
      lem59_mapTree (· + p) (lem59_mapTree (· - p) t) = t
  | .nil, _ => rfl
  | .node k l r, hk => by
    have hk0 : p ≤ k := hk k .here
    have hkl : ∀ x ∈ l, p ≤ x := fun x hx => hk x (.left hx)
    have hkr : ∀ x ∈ r, p ≤ x := fun x hx => hk x (.right hx)
    simp [lem59_mapTree, Nat.sub_add_cancel hk0,
      lem59_mapTree_sub_add p l hkl, lem59_mapTree_sub_add p r hkr]

private theorem lem59_isBST_map_add_iff (p : ℕ) (s : BinaryTree ℕ) :
    (lem59_mapTree (· + p) s).IsBST ↔ s.IsBST := by
  rw [SplayTree.IsBST_iff_toKeyList_sorted, SplayTree.IsBST_iff_toKeyList_sorted,
    lem59_toKeyList_mapTree, List.pairwise_map]
  constructor <;> (intro h; apply List.Pairwise.imp _ h; omega)

private theorem lem59_mem_map_add_iff (p : ℕ) (s : BinaryTree ℕ) (v : ℕ) :
    v + p ∈ lem59_mapTree (· + p) s ↔ v ∈ s := by
  rw [mem_iff_mem_toKeyList, mem_iff_mem_toKeyList, lem59_toKeyList_mapTree, List.mem_map]
  constructor
  · rintro ⟨w, hw, hw_eq⟩
    have : w = v := by omega
    subst this; exact hw
  · intro hv; exact ⟨v, hv, rfl⟩

private theorem lem59_maxKey?_mapTree (f : ℕ → ℕ) :
    ∀ (s : BinaryTree ℕ), (lem59_mapTree f s).maxKey? = (s.maxKey?).map f
  | .nil => rfl
  | .node k l r => by
    simp only [lem59_mapTree, BinaryTree.maxKey?, lem59_maxKey?_mapTree f r]
    cases r.maxKey? <;> rfl

private theorem lem59_subtreeAtKey_map_add (p : ℕ) :
    ∀ (s : BinaryTree ℕ) (v : ℕ),
      subtreeAtKey (lem59_mapTree (· + p) s) (v + p) =
        lem59_mapTree (· + p) (subtreeAtKey s v)
  | .nil, _ => rfl
  | .node k l r, v => by
    simp only [lem59_mapTree, subtreeAtKey]
    have h1 : (v + p < k + p) ↔ (v < k) := by omega
    have h2 : (k + p < v + p) ↔ (k < v) := by omega
    by_cases hvk : v < k
    · simp [h1.mpr hvk, hvk, lem59_subtreeAtKey_map_add p l v]
    · by_cases hkv : k < v
      · simp [h1.not.mpr hvk, hvk, h2.mpr hkv, hkv, lem59_subtreeAtKey_map_add p r v]
      · simp [h1.not.mpr hvk, hvk, h2.not.mpr hkv, hkv, lem59_mapTree]

private theorem lem59_mem_self_subtreeAtKey {α : Type} [LinearOrder α] :
    ∀ {t : BinaryTree α}, t.IsBST → ∀ {v : α}, v ∈ t → v ∈ subtreeAtKey t v
  | .nil, _, _, hv => by cases hv
  | .node k l r, ht, v, hv => by
    rcases mem_node_iff.mp hv with rfl | hvl | hvr
    · simp [subtreeAtKey]
    · have hvk : v < k := lt_of_IsBST_left l k r ht hvl
      simp only [subtreeAtKey, hvk, ↓reduceIte]
      exact lem59_mem_self_subtreeAtKey (IsBST_left_of_IsBST ht) hvl
    · have hkv : k < v := gt_of_IsBST_right l k r ht hvr
      have hnot : ¬ (v < k) := not_lt.mpr (le_of_lt hkv)
      simp only [subtreeAtKey, hnot, hkv, ↓reduceIte]
      exact lem59_mem_self_subtreeAtKey (IsBST_right_of_IsBST ht) hvr

private theorem lem59_rightReach_map_add (p : ℕ) (s : BinaryTree ℕ) (hs : s.IsBST)
    (v : ℕ) (hv : v ∈ s) :
    rightReach (lem59_mapTree (· + p) s) (v + p) = rightReach s v + p := by
  unfold rightReach
  rw [lem59_subtreeAtKey_map_add, lem59_maxKey?_mapTree]
  have hv_sub : v ∈ subtreeAtKey s v := lem59_mem_self_subtreeAtKey hs hv
  cases hmax : (subtreeAtKey s v).maxKey? with
  | none =>
    cases hsub : subtreeAtKey s v with
    | nil => rw [hsub] at hv_sub; cases hv_sub
    | node k l r =>
      obtain ⟨m, hm⟩ := lem59_maxKey?_ne_none_of_node k l r
      rw [hsub, hm] at hmax; cases hmax
  | some m => simp

private theorem lem59_rotateRightEdge_map_add (p : ℕ) :
    ∀ (s : BinaryTree ℕ) (x y : ℕ),
      rotateRightEdge (lem59_mapTree (· + p) s) (x + p) (y + p) =
        lem59_mapTree (· + p) (rotateRightEdge s x y)
  | .nil, _, _ => rfl
  | .node k l r, x, y => by
    simp only [lem59_mapTree, rotateRightEdge]
    have h1 : (y + p < k + p) ↔ (y < k) := by omega
    have h2 : (k + p < y + p) ↔ (k < y) := by omega
    by_cases hyk : y < k
    · simp [h1.mpr hyk, hyk, lem59_rotateRightEdge_map_add p l x y, lem59_mapTree]
    · by_cases hky : k < y
      · simp [h1.not.mpr hyk, hyk, h2.mpr hky, hky,
          lem59_rotateRightEdge_map_add p r x y, lem59_mapTree]
      · simp only [h1.not.mpr hyk, hyk, h2.not.mpr hky, hky, ↓reduceIte]
        cases l with
        | nil => rfl
        | node lx a b =>
          by_cases hlx : lx = x
          · subst lx; simp [lem59_mapTree]
          · simp [hlx, lem59_mapTree]

private theorem lem59_isRightRotEdge_map_add (p : ℕ) (s : BinaryTree ℕ) (x y : ℕ)
    (h : IsRightRotEdge s x y) :
    IsRightRotEdge (lem59_mapTree (· + p) s) (x + p) (y + p) := by
  rcases h with ⟨A, B, C, hy, hsub⟩
  refine ⟨lem59_mapTree (· + p) A, lem59_mapTree (· + p) B, lem59_mapTree (· + p) C,
    (lem59_mem_map_add_iff p s y).mpr hy, ?_⟩
  rw [lem59_subtreeAtKey_map_add, hsub]
  rfl

private theorem lem59_rightRotReachable_map_add (p : ℕ) {s₁ s₂ : BinaryTree ℕ}
    (h : RightRotReachable s₁ s₂) :
    RightRotReachable (lem59_mapTree (· + p) s₁) (lem59_mapTree (· + p) s₂) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    rcases hstep with ⟨x, y, hxy, hedge, rfl⟩
    refine .tail ih ⟨x + p, y + p, by omega, lem59_isRightRotEdge_map_add p _ x y hedge, ?_⟩
    exact (lem59_rotateRightEdge_map_add p _ x y).symm

private theorem lem59_rightRotReachable_shifted
    (h_4_1 : ∀ (n : ℕ), 1 ≤ n → ∀ (t₁ t₂ : BinaryTree ℕ),
      t₁.IsBST → t₂.IsBST →
      keyFinset t₁ = Finset.Icc 1 n → keyFinset t₂ = Finset.Icc 1 n →
      (RightRotReachable t₁ t₂ ↔ ∀ v ∈ Finset.Icc 1 n, rightReach t₁ v ≤ rightReach t₂ v))
    (p K_X : ℕ) (hpK : p + 1 ≤ K_X)
    (t₁ t₂ : BinaryTree ℕ) (ht₁ : t₁.IsBST) (ht₂ : t₂.IsBST)
    (hk₁ : keyFinset t₁ = Finset.Icc (p + 1) K_X)
    (hk₂ : keyFinset t₂ = Finset.Icc (p + 1) K_X)
    (hreach : ∀ u ∈ Finset.Icc (p + 1) K_X, rightReach t₁ u ≤ rightReach t₂ u) :
    RightRotReachable t₁ t₂ := by
  set n := K_X - p
  have hn1 : 1 ≤ n := by omega
  set s₁ := lem59_mapTree (· - p) t₁
  set s₂ := lem59_mapTree (· - p) t₂
  have hs1_inv : lem59_mapTree (· + p) s₁ = t₁ := by
    apply lem59_mapTree_sub_add p t₁
    intro k hk
    rw [lem59_mem_iff_mem_keyFinset, hk₁, Finset.mem_Icc] at hk
    omega
  have hs2_inv : lem59_mapTree (· + p) s₂ = t₂ := by
    apply lem59_mapTree_sub_add p t₂
    intro k hk
    rw [lem59_mem_iff_mem_keyFinset, hk₂, Finset.mem_Icc] at hk
    omega
  have hs1_bst : s₁.IsBST := (lem59_isBST_map_add_iff p s₁).mp (hs1_inv ▸ ht₁)
  have hs2_bst : s₂.IsBST := (lem59_isBST_map_add_iff p s₂).mp (hs2_inv ▸ ht₂)
  have hks : ∀ (t : BinaryTree ℕ) (s : BinaryTree ℕ),
      lem59_mapTree (· + p) s = t → keyFinset t = Finset.Icc (p + 1) K_X →
      keyFinset s = Finset.Icc 1 n := by
    intro t s hinv hkt
    ext v
    rw [← lem59_mem_iff_mem_keyFinset, Finset.mem_Icc]
    constructor
    · intro hvs
      have hvt : v + p ∈ t := hinv ▸ (lem59_mem_map_add_iff p s v).mpr hvs
      rw [lem59_mem_iff_mem_keyFinset, hkt, Finset.mem_Icc] at hvt
      omega
    · intro hvn
      have hvt : v + p ∈ t := by
        rw [lem59_mem_iff_mem_keyFinset, hkt, Finset.mem_Icc]
        omega
      rw [← hinv, lem59_mem_map_add_iff] at hvt
      exact hvt
  have hks₁ : keyFinset s₁ = Finset.Icc 1 n := hks t₁ s₁ hs1_inv hk₁
  have hks₂ : keyFinset s₂ = Finset.Icc 1 n := hks t₂ s₂ hs2_inv hk₂
  have hs_reach : RightRotReachable s₁ s₂ := by
    rw [h_4_1 n hn1 s₁ s₂ hs1_bst hs2_bst hks₁ hks₂]
    intro v hv
    have hv_s1 : v ∈ s₁ := by rw [lem59_mem_iff_mem_keyFinset, hks₁]; exact hv
    have hv_s2 : v ∈ s₂ := by rw [lem59_mem_iff_mem_keyFinset, hks₂]; exact hv
    rw [Finset.mem_Icc] at hv
    have hvp_mem : v + p ∈ Finset.Icc (p + 1) K_X := by rw [Finset.mem_Icc]; omega
    have hr := hreach (v + p) hvp_mem
    rw [← hs1_inv, ← hs2_inv, lem59_rightReach_map_add p s₁ hs1_bst v hv_s1,
      lem59_rightReach_map_add p s₂ hs2_bst v hv_s2] at hr
    omega
  have hmapped := lem59_rightRotReachable_map_add p hs_reach
  rwa [hs1_inv, hs2_inv] at hmapped

end TreeSpineAndReachHelpers


section CascadeBatchHelpers

private def lem59_ConsecGapLe (thr : ℕ) : List ℕ → Prop
  | a :: b :: rest => b - a - 1 ≤ thr ∧ lem59_ConsecGapLe thr (b :: rest)
  | _ => True

private def lem59_BatchGapValid (Δ' : ℕ) : List ℕ → Prop
  | a :: b :: rest => a + 2 ≤ b ∧ b ≤ a + Δ' + 2 ∧ lem59_BatchGapValid Δ' (b :: rest)
  | _ => True

private theorem lem59_batchGapValid_tail (Δ' : ℕ) :
    ∀ {xs : List ℕ}, lem59_BatchGapValid Δ' xs → lem59_BatchGapValid Δ' xs.tail
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, h => h.2.2

private theorem lem59_batchGapValid_take (Δ' : ℕ) :
    ∀ (n : ℕ) (xs : List ℕ), lem59_BatchGapValid Δ' xs → lem59_BatchGapValid Δ' (xs.take n)
  | 0, _, _ => trivial
  | 1, [], _ => trivial
  | 1, _ :: _, _ => trivial
  | _ + 2, [], _ => trivial
  | _ + 2, [_], _ => trivial
  | m + 2, a :: b :: rest, h => by
    simp only [List.take_succ_cons]
    refine ⟨h.1, h.2.1, ?_⟩
    have ih := lem59_batchGapValid_take Δ' (m + 1) (b :: rest) h.2.2
    simpa only [List.take_succ_cons] using ih

private theorem lem59_batchGapValid_drop (Δ' : ℕ) :
    ∀ (n : ℕ) (xs : List ℕ), lem59_BatchGapValid Δ' xs → lem59_BatchGapValid Δ' (xs.drop n)
  | 0, _, h => h
  | _ + 1, [], _ => trivial
  | m + 1, _ :: rest, h =>
    lem59_batchGapValid_drop Δ' m rest (lem59_batchGapValid_tail Δ' h)

private theorem lem59_batchGapValid_getElem (Δ' : ℕ) :
    ∀ (ch : List ℕ), lem59_BatchGapValid Δ' ch →
      (∀ (r : ℕ) (hr : r + 1 < ch.length),
        ch[r] + 2 ≤ ch[r + 1] ∧ ch[r + 1] ≤ ch[r] + Δ' + 2) ∧
      (∀ (r : ℕ) (hr : r < ch.length), ch[0] ≤ ch[r])
  | [], _ => ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
  | [a], _ =>
    ⟨fun _ h => by simp at h,
     fun r hr => by
       have : r = 0 := by simp at hr; omega
       subst r; exact le_rfl⟩
  | a :: b :: rest, h => by
    obtain ⟨ih_adj, ih_ge⟩ := lem59_batchGapValid_getElem Δ' (b :: rest) h.2.2
    refine ⟨?_, ?_⟩
    · intro r hr
      cases r with
      | zero => exact ⟨h.1, h.2.1⟩
      | succ r' =>
        have hr' : r' + 1 < (b :: rest).length := by simp at hr ⊢; omega
        exact ih_adj r' hr'
    · intro r hr
      cases r with
      | zero => exact le_rfl
      | succ r' =>
        have hr' : r' < (b :: rest).length := by simp at hr ⊢; omega
        have hbr := ih_ge r' hr'
        have hab : a + 2 ≤ b := h.1
        simp only [List.getElem_cons_zero] at hbr ⊢
        simp only [List.getElem_cons_succ]
        omega

private def lem59_cutPiecesAux (thr : ℕ) (cur : ℕ) : List ℕ → List ℕ × List (List ℕ)
  | [] => ([cur], [])
  | y :: rest =>
    let res := lem59_cutPiecesAux thr y rest
    if thr < y - cur - 1 then
      ([cur], res.1 :: res.2)
    else
      (cur :: res.1, res.2)

private theorem lem59_cutPiecesAux_spec (thr : ℕ) (hthr : 1 ≤ thr) (W : Finset ℕ) :
    ∀ (xs : List ℕ) (cur : ℕ),
      (cur :: xs).Pairwise (· < ·) →
      (∀ a ∈ cur :: xs, ∀ b ∈ cur :: xs, a < b →
        (∀ t ∈ cur :: xs, ¬ (a < t ∧ t < b)) →
        thr < b - a - 1 →
        thr < 2 * (W.filter (fun t => a < t ∧ t < b)).card) →
      let res := lem59_cutPiecesAux thr cur xs
      let pieces := res.1 :: res.2
      (∃ p1_tail, res.1 = cur :: p1_tail) ∧
      pieces.flatten = cur :: xs ∧
      (∀ pc ∈ pieces, pc ≠ [] ∧ pc.Pairwise (· < ·) ∧ lem59_ConsecGapLe thr pc) ∧
      pieces.Pairwise (fun q₁ q₂ => ∀ a ∈ q₁, ∀ b ∈ q₂, a + 2 ≤ b) ∧
      thr * res.2.length ≤ 2 * (W.filter (fun t => cur < t)).card
  | [], cur, _, _ => by
    dsimp only [lem59_cutPiecesAux]
    refine ⟨⟨[], rfl⟩, rfl, ?_, by simp, by simp⟩
    intro pc hpc
    simp only [List.mem_singleton] at hpc
    subst hpc
    exact ⟨by simp, by simp, trivial⟩
  | y :: rest, cur, hpw, hGap => by
    have hpw_cons := List.pairwise_cons.mp hpw
    have hcur_lt : ∀ z ∈ y :: rest, cur < z := hpw_cons.1
    have hcur_y : cur < y := hcur_lt y List.mem_cons_self
    have hpw_tail : (y :: rest).Pairwise (· < ·) := hpw_cons.2
    have hGap_tail : ∀ a ∈ y :: rest, ∀ b ∈ y :: rest, a < b →
        (∀ t ∈ y :: rest, ¬ (a < t ∧ t < b)) →
        thr < b - a - 1 →
        thr < 2 * (W.filter (fun t => a < t ∧ t < b)).card := by
      intro a ha b hb hab hadj hbig
      apply hGap a (List.mem_cons_of_mem cur ha) b (List.mem_cons_of_mem cur hb) hab _ hbig
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht_tail
      · have hca := hcur_lt a ha
        omega
      · exact hadj t ht_tail
    dsimp only [lem59_cutPiecesAux]
    obtain ⟨⟨p1_tail', hp1_eq⟩, hflat', hpc', hcross', hbound'⟩ :=
      lem59_cutPiecesAux_spec thr hthr W rest y hpw_tail hGap_tail
    set res' := lem59_cutPiecesAux thr y rest
    have hy_le_all : ∀ z ∈ y :: rest, y ≤ z := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz_rest
      · exact le_rfl
      · exact le_of_lt ((List.pairwise_cons.mp hpw_tail).1 z hz_rest)
    by_cases hcut : thr < y - cur - 1
    · simp only [hcut, ↓reduceIte]
      refine ⟨⟨[], rfl⟩, ?_, ?_, ?_, ?_⟩
      · simp only [List.flatten_cons, List.singleton_append]
        exact congrArg (cur :: ·) hflat'
      · intro pc hpc
        rcases List.mem_cons.mp hpc with rfl | hpc_rest
        · exact ⟨by simp, by simp, trivial⟩
        · exact hpc' pc hpc_rest
      · rw [List.pairwise_cons]
        refine ⟨?_, hcross'⟩
        intro q hq a ha b hb
        simp only [List.mem_singleton] at ha
        subst a
        have hb_flat : b ∈ (res'.1 :: res'.2).flatten := List.mem_flatten.mpr ⟨q, hq, hb⟩
        rw [hflat'] at hb_flat
        have hyb := hy_le_all b hb_flat
        omega
      · have hadj_cury : ∀ t ∈ cur :: y :: rest, ¬ (cur < t ∧ t < y) := by
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht'
          · omega
          · have hyt := hy_le_all t ht'
            omega
        have hw_cury : thr < 2 * (W.filter (fun t => cur < t ∧ t < y)).card :=
          hGap cur List.mem_cons_self y (List.mem_cons_of_mem cur List.mem_cons_self)
            hcur_y hadj_cury hcut
        set W₁ := W.filter (fun t => cur < t ∧ t < y)
        set W₂ := W.filter (fun t => y < t)
        have hdisj : Disjoint W₁ W₂ := by
          rw [Finset.disjoint_left]
          intro t ht1 ht2
          simp only [W₁, W₂, Finset.mem_filter] at ht1 ht2
          omega
        have hsub : W₁ ∪ W₂ ⊆ W.filter (fun t => cur < t) := by
          intro t ht
          simp only [W₁, W₂, Finset.mem_union, Finset.mem_filter] at ht ⊢
          rcases ht with ⟨htW, h1, _⟩ | ⟨htW, h2⟩
          · exact ⟨htW, h1⟩
          · exact ⟨htW, by omega⟩
        have hcard_union : W₁.card + W₂.card ≤ (W.filter (fun t => cur < t)).card := by
          rw [← Finset.card_union_of_disjoint hdisj]
          exact Finset.card_le_card hsub
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega
    · simp only [hcut, ↓reduceIte]
      refine ⟨⟨res'.1, rfl⟩, ?_, ?_, ?_, ?_⟩
      · simp only [List.flatten_cons, List.cons_append]
        exact congrArg (cur :: ·) hflat'
      · intro pc hpc
        rcases List.mem_cons.mp hpc with rfl | hpc_rest
        · have hp1_props := hpc' res'.1 List.mem_cons_self
          have hp1_sub : ∀ z ∈ res'.1, z ∈ y :: rest := by
            intro z hz
            rw [← hflat']
            exact List.mem_flatten.mpr ⟨res'.1, List.mem_cons_self, hz⟩
          refine ⟨by simp, ?_, ?_⟩
          · rw [List.pairwise_cons]
            exact ⟨fun z hz => hcur_lt z (hp1_sub z hz), hp1_props.2.1⟩
          · rw [hp1_eq]
            exact ⟨by omega, hp1_eq ▸ hp1_props.2.2⟩
        · exact hpc' pc (List.mem_cons_of_mem res'.1 hpc_rest)
      · rw [List.pairwise_cons] at hcross' ⊢
        refine ⟨?_, hcross'.2⟩
        intro q hq a ha b hb
        rcases List.mem_cons.mp ha with rfl | ha_p1
        · have hy_in_p1 : y ∈ res'.1 := by rw [hp1_eq]; exact List.mem_cons_self
          have hyb := hcross'.1 q hq y hy_in_p1 b hb
          omega
        · exact hcross'.1 q hq a ha_p1 b hb
      · have hsub : W.filter (fun t => y < t) ⊆ W.filter (fun t => cur < t) := by
          intro t ht
          simp only [Finset.mem_filter] at ht ⊢
          exact ⟨ht.1, by omega⟩
        have hcard_le := Finset.card_le_card hsub
        omega

private def lem59_evenIdx : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: _ :: rest => a :: lem59_evenIdx rest

private theorem lem59_evenIdx_head (c : ℕ) (xs : List ℕ) :
    ∃ tail, lem59_evenIdx (c :: xs) = c :: tail := by
  cases xs with
  | nil => exact ⟨[], rfl⟩
  | cons d rest => exact ⟨lem59_evenIdx rest, rfl⟩

private theorem lem59_evenIdx_spec (thr : ℕ) :
    ∀ (pc : List ℕ),
      pc.Pairwise (· < ·) →
      lem59_ConsecGapLe thr pc →
      (lem59_evenIdx pc).Sublist pc ∧
      pc.length ≤ 2 * (lem59_evenIdx pc).length ∧
      (lem59_evenIdx pc).Pairwise (fun a b => a + 2 ≤ b) ∧
      lem59_BatchGapValid (2 * thr) (lem59_evenIdx pc)
  | [], _, _ => ⟨.slnil, by simp [lem59_evenIdx], by simp [lem59_evenIdx], trivial⟩
  | [a], _, _ => ⟨List.Sublist.refl [a], by simp [lem59_evenIdx], by simp [lem59_evenIdx], trivial⟩
  | a :: b :: rest, hpw, hgap => by
    have hpw1 := List.pairwise_cons.mp hpw
    have hpw2 := List.pairwise_cons.mp hpw1.2
    have hab : a < b := hpw1.1 b List.mem_cons_self
    have hgap_ab : b - a - 1 ≤ thr := hgap.1
    have hpw_rest : rest.Pairwise (· < ·) := hpw2.2
    have hgap_rest : lem59_ConsecGapLe thr rest := by
      cases rest with
      | nil => exact trivial
      | cons c rest' => exact hgap.2.2
    obtain ⟨ih_sub, ih_len, ih_pw2, ih_bg⟩ := lem59_evenIdx_spec thr rest hpw_rest hgap_rest
    dsimp only [lem59_evenIdx]
    refine ⟨.cons_cons a (.cons b ih_sub), ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · rw [List.pairwise_cons]
      refine ⟨?_, ih_pw2⟩
      intro x hx
      have hx_rest : x ∈ rest := ih_sub.subset hx
      have hbx : b < x := hpw2.1 x hx_rest
      omega
    · cases rest with
      | nil => exact trivial
      | cons c rest' =>
        obtain ⟨tail, hhead⟩ := lem59_evenIdx_head c rest'
        rw [hhead]
        have hbc : b < c := hpw2.1 c List.mem_cons_self
        have hgap_bc : c - b - 1 ≤ thr := hgap.2.1
        refine ⟨by omega, by omega, hhead ▸ ih_bg⟩

private def lem59_fullChunks (k : ℕ) (xs : List ℕ) : List (List ℕ) :=
  if _h : 1 ≤ k ∧ k ≤ xs.length then
    xs.take k :: lem59_fullChunks k (xs.drop k)
  else
    []
termination_by xs.length
decreasing_by
  rw [List.length_drop]
  omega

private theorem lem59_fullChunks_spec (Δ' k : ℕ) (hk : 1 ≤ k) :
    ∀ (xs : List ℕ),
      lem59_BatchGapValid Δ' xs →
      (∀ ch ∈ lem59_fullChunks k xs, ch.length = k ∧ lem59_BatchGapValid Δ' ch) ∧
      (lem59_fullChunks k xs).flatten.Sublist xs ∧
      xs.length < k * (1 + (lem59_fullChunks k xs).length) := by
  intro xs
  induction hlen : xs.length using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    intro hbg
    rw [lem59_fullChunks]
    split_ifs with hcond
    · have hdrop_lt : (xs.drop k).length < n := by
        rw [List.length_drop, hlen]
        omega
      obtain ⟨ih_ch, ih_sub, ih_len⟩ :=
        ih (xs.drop k).length hdrop_lt (xs.drop k) rfl (lem59_batchGapValid_drop Δ' k xs hbg)
      refine ⟨?_, ?_, ?_⟩
      · intro ch hch
        rcases List.mem_cons.mp hch with rfl | hch_rest
        · exact ⟨by simp [hcond.2], lem59_batchGapValid_take Δ' k xs hbg⟩
        · exact ih_ch ch hch_rest
      · simp only [List.flatten_cons]
        simpa only [List.take_append_drop] using (List.Sublist.refl (xs.take k)).append ih_sub
      · simp only [List.length_cons]
        rw [List.length_drop] at ih_len
        have hmul : k * (1 + ((lem59_fullChunks k (xs.drop k)).length + 1)) =
            k * (1 + (lem59_fullChunks k (xs.drop k)).length) + k := by ring
        rw [hmul]
        have hk_le := hcond.2
        omega
    · have hlt : xs.length < k := by omega
      exact ⟨by simp, List.nil_sublist xs, by simp [← hlen, hlt]⟩

private theorem lem59_flatten_flatMap {α β : Type} (xs : List α) (g : α → List (List β)) :
    (xs.flatMap g).flatten = xs.flatMap (fun x => (g x).flatten) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp [List.flatMap_cons, List.flatten_append, ih]

private theorem lem59_pairwise_flatMap_nat (xs : List (List ℕ)) (g : List ℕ → List ℕ)
    (hpw : xs.Pairwise (fun q₁ q₂ => ∀ a ∈ q₁, ∀ b ∈ q₂, a + 2 ≤ b))
    (hg_pw : ∀ q ∈ xs, (g q).Pairwise (fun a b => a + 2 ≤ b))
    (hg_sub : ∀ q ∈ xs, ∀ a ∈ g q, a ∈ q) :
    (xs.flatMap g).Pairwise (fun a b => a + 2 ≤ b) := by
  induction xs with
  | nil => simp
  | cons q rest ih =>
    rw [List.pairwise_cons] at hpw
    simp only [List.flatMap_cons, List.pairwise_append]
    refine ⟨hg_pw q List.mem_cons_self,
      ih hpw.2 (fun q' hq' => hg_pw q' (List.mem_cons_of_mem q hq'))
        (fun q' hq' => hg_sub q' (List.mem_cons_of_mem q hq')), ?_⟩
    intro a ha b hb
    rw [List.mem_flatMap] at hb
    obtain ⟨q₂, hq₂, hb_q₂⟩ := hb
    exact hpw.1 q₂ hq₂ a (hg_sub q List.mem_cons_self a ha)
      b (hg_sub q₂ (List.mem_cons_of_mem q hq₂) b hb_q₂)

private theorem lem59_drop_step (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    xs.drop k = (xs[k]?).getD 0 :: xs.drop (k + 1) := by
  have hget : (xs[k]?).getD 0 = xs[k] := by simp [hk]
  rw [hget]
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    cases i with
    | zero => simp
    | succ j =>
      simp only [List.getElem_drop, List.getElem_cons_succ]
      congr 1
      omega

private theorem lem59_drop_take_drop (xs : List ℕ) (a b : ℕ) (hab : a ≤ b) :
    xs.drop a = (xs.drop a).take (b - a) ++ xs.drop b := by
  calc xs.drop a
      = (xs.drop a).take (b - a) ++ (xs.drop a).drop (b - a) :=
        (List.take_append_drop (b - a) (xs.drop a)).symm
    _ = (xs.drop a).take (b - a) ++ xs.drop b := by
        rw [List.drop_drop]
        congr 2
        omega

private theorem lem59_drop_split (xs : List ℕ) (m f : ℕ) (hmf : m ≤ f) (hf1 : f + 1 < xs.length) :
    xs.drop m =
      (xs.drop m).take (f - m) ++ [(xs[f]?).getD 0, (xs[f + 1]?).getD 0] ++ xs.drop (f + 2) := by
  have hd : xs.drop f = [(xs[f]?).getD 0, (xs[f + 1]?).getD 0] ++ xs.drop (f + 2) := by
    rw [lem59_drop_step xs f (by omega), lem59_drop_step xs (f + 1) hf1]
    rfl
  calc xs.drop m
      = (xs.drop m).take (f - m) ++ xs.drop f := lem59_drop_take_drop xs m f hmf
    _ = (xs.drop m).take (f - m) ++ ([(xs[f]?).getD 0, (xs[f + 1]?).getD 0] ++ xs.drop (f + 2)) :=
        congrArg ((xs.drop m).take (f - m) ++ ·) hd
    _ = (xs.drop m).take (f - m) ++ [(xs[f]?).getD 0, (xs[f + 1]?).getD 0] ++ xs.drop (f + 2) :=
        (List.append_assoc _ _ _).symm

private theorem lem59_append_drop_getElem (pref₀ pi0 : List ℕ) (f₀ f : ℕ)
    (h0 : f₀ ≤ f) (hf : f < pi0.length)
    (hb : pref₀.length + (f - f₀) < (pref₀ ++ pi0.drop f₀).length) :
    (pref₀ ++ pi0.drop f₀)[pref₀.length + (f - f₀)]'hb = (pi0[f]?).getD 0 := by
  rw [List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left, List.getElem_drop]
  have hget : (pi0[f]?).getD 0 = pi0[f] := by simp [hf]
  rw [hget]
  congr 1
  omega

private theorem lem59_path_pair_eq (path pref₀ pi0 : List ℕ) (f₀ f : ℕ)
    (hpath : path = pref₀ ++ pi0.drop f₀) (h0 : f₀ ≤ f) (hf1 : f + 1 < pi0.length) :
    ∃ h : (pref₀.length + (f - f₀)) + 1 < path.length,
      (path[pref₀.length + (f - f₀)], path[(pref₀.length + (f - f₀)) + 1]) =
        ((pi0[f]?).getD 0, (pi0[f + 1]?).getD 0) := by
  subst path
  have hb1 : (pref₀.length + (f - f₀)) + 1 < (pref₀ ++ pi0.drop f₀).length := by
    simp only [List.length_append, List.length_drop]; omega
  refine ⟨hb1, Prod.ext ?_ ?_⟩
  · exact lem59_append_drop_getElem pref₀ pi0 f₀ f h0 (by omega) (by omega)
  · have hidx : (pref₀.length + (f - f₀)) + 1 = pref₀.length + ((f + 1) - f₀) := by omega
    have hb2 : pref₀.length + ((f + 1) - f₀) < (pref₀ ++ pi0.drop f₀).length := by omega
    have heq : (pref₀ ++ pi0.drop f₀)[(pref₀.length + (f - f₀)) + 1]'hb1 =
        (pref₀ ++ pi0.drop f₀)[pref₀.length + ((f + 1) - f₀)]'hb2 := by
      congr 1
    rw [heq]
    exact lem59_append_drop_getElem pref₀ pi0 f₀ (f + 1) (by omega) hf1 hb2

private theorem lem59_getD_ne_of_pairwise_lt (xs : List ℕ) (hpw : xs.Pairwise (· < ·))
    (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length) (hij : i ≠ j) :
    (xs[i]?).getD 0 ≠ (xs[j]?).getD 0 := by
  have h1 : (xs[i]?).getD 0 = xs[i] := by simp [hi]
  have h2 : (xs[j]?).getD 0 = xs[j] := by simp [hj]
  rw [h1, h2]
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact ne_of_lt ((List.pairwise_iff_getElem.mp hpw) i j hi hj hlt)
  · exact absurd rfl hij
  · exact ne_of_gt ((List.pairwise_iff_getElem.mp hpw) j i hj hi hgt)

private theorem lem59_getD_le_of_pairwise_lt (xs : List ℕ) (hpw : xs.Pairwise (· < ·))
    (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length) (hij : i ≤ j) :
    (xs[i]?).getD 0 ≤ (xs[j]?).getD 0 := by
  have h1 : (xs[i]?).getD 0 = xs[i] := by simp [hi]
  have h2 : (xs[j]?).getD 0 = xs[j] := by simp [hj]
  rw [h1, h2]
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact le_of_lt ((List.pairwise_iff_getElem.mp hpw) i j hi hj hlt)

private theorem lem59_foldl_selected_reach
    (pi0 : List ℕ) (hpi0_pw : pi0.Pairwise (· < ·)) :
    ∀ (fs : List ℕ) (B : BinaryTree ℕ) (m m_end : ℕ) (pref : List ℕ),
      B.IsBST →
      leftSpine B = pref ++ pi0.drop m →
      fs.Pairwise (fun a b => a + 2 ≤ b) →
      (∀ f ∈ fs, m ≤ f ∧ f + 1 < pi0.length ∧ f + 2 ≤ m_end) →
      m ≤ m_end →
      let stepF := fun (acc : BinaryTree ℕ) (f : ℕ) =>
        rotateRightEdge acc ((pi0[f]?).getD 0) ((pi0[f + 1]?).getD 0)
      let B' := fs.foldl stepF B
      B'.IsBST ∧
      keyFinset B' = keyFinset B ∧
      (∃ pref', leftSpine B' = pref' ++ pi0.drop m_end) ∧
      (∀ f ∈ fs, rightReach B' ((pi0[f]?).getD 0) = rightReach B ((pi0[f + 1]?).getD 0)) ∧
      (∀ u : ℕ, (∀ f ∈ fs, u ≠ (pi0[f]?).getD 0) → rightReach B' u = rightReach B u)
  | [], B, m, m_end, pref, hB_bst, hspine, _, _, hm_le => by
    refine ⟨hB_bst, rfl, ⟨pref ++ (pi0.drop m).take (m_end - m), ?_⟩,
      by simp, fun _ _ => rfl⟩
    dsimp only [List.foldl_nil]
    calc leftSpine B
        = pref ++ pi0.drop m := hspine
      _ = pref ++ ((pi0.drop m).take (m_end - m) ++ pi0.drop m_end) :=
          congrArg (pref ++ ·) (lem59_drop_take_drop pi0 m m_end hm_le)
      _ = (pref ++ (pi0.drop m).take (m_end - m)) ++ pi0.drop m_end :=
          (List.append_assoc _ _ _).symm
  | f :: rest, B, m, m_end, pref, hB_bst, hspine, hpw, hfs, _ => by
    obtain ⟨hf_ge_m, hf_lt, hf_end⟩ := hfs f List.mem_cons_self
    rw [List.pairwise_cons] at hpw
    set x := (pi0[f]?).getD 0
    set y := (pi0[f + 1]?).getD 0
    have hsp_B : leftSpine B =
        (pref ++ (pi0.drop m).take (f - m)) ++ [x, y] ++ pi0.drop (f + 2) := by
      calc leftSpine B
          = pref ++ pi0.drop m := hspine
        _ = pref ++ ((pi0.drop m).take (f - m) ++ [x, y] ++ pi0.drop (f + 2)) :=
            congrArg (pref ++ ·) (lem59_drop_split pi0 m f hf_ge_m hf_lt)
        _ = (pref ++ (pi0.drop m).take (f - m)) ++ [x, y] ++ pi0.drop (f + 2) := by
            simp only [List.append_assoc]
    set B₁ := rotateRightEdge B x y
    have hB₁_bst : B₁.IsBST := lem59_isBST_rotateRightEdge B x y hB_bst
    have hB₁_keys : keyFinset B₁ = keyFinset B := lem59_keyFinset_rotateRightEdge B x y
    have hB₁_spine : leftSpine B₁ =
        ((pref ++ (pi0.drop m).take (f - m)) ++ [x]) ++ pi0.drop (f + 2) :=
      lem59_spine_drop B hB_bst _ _ x y hsp_B
    obtain ⟨hr_x, hr_other⟩ := lem59_rightReach_spine_rot B hB_bst _ _ x y hsp_B
    have hrest_bounds : ∀ g ∈ rest, f + 2 ≤ g ∧ g + 1 < pi0.length ∧ g + 2 ≤ m_end := by
      intro g hg
      have hg_all := hfs g (List.mem_cons_of_mem f hg)
      exact ⟨hpw.1 g hg, hg_all.2.1, hg_all.2.2⟩
    obtain ⟨ih_bst, ih_keys, ih_spine, ih_sel, ih_unsel⟩ :=
      lem59_foldl_selected_reach pi0 hpi0_pw rest B₁ (f + 2) m_end
        ((pref ++ (pi0.drop m).take (f - m)) ++ [x])
        hB₁_bst hB₁_spine hpw.2 hrest_bounds hf_end
    simp only [List.foldl_cons]
    refine ⟨ih_bst, ih_keys.trans hB₁_keys, ih_spine, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with hgf | hg_rest
      · subst g
        have hx_not_rest : ∀ h ∈ rest, x ≠ (pi0[h]?).getD 0 := by
          intro h hh
          have hfh : f + 2 ≤ h := hpw.1 h hh
          have hh_lt := (hrest_bounds h hh).2.1
          exact lem59_getD_ne_of_pairwise_lt pi0 hpi0_pw f h (by omega) (by omega) (by omega)
        rw [ih_unsel x hx_not_rest, hr_x]
      · have hg_ge : f + 2 ≤ g := hpw.1 g hg_rest
        have hg_lt : g + 1 < pi0.length := (hrest_bounds g hg_rest).2.1
        have hne : (pi0[g + 1]?).getD 0 ≠ x :=
          lem59_getD_ne_of_pairwise_lt pi0 hpi0_pw (g + 1) f hg_lt (by omega) (by omega)
        rw [ih_sel g hg_rest, hr_other _ hne]
    · intro u hu
      have hux : u ≠ x := hu f List.mem_cons_self
      have hu_rest : ∀ g ∈ rest, u ≠ (pi0[g]?).getD 0 :=
        fun g hg => hu g (List.mem_cons_of_mem f hg)
      rw [ih_unsel u hu_rest, hr_other u hux]

private theorem lem59_isGappedRightCascade_one_batch
    (pi0 : List ℕ) (Δ' k : ℕ) (hk : 1 ≤ k)
    (B : BinaryTree ℕ) (m : ℕ) (pref : List ℕ)
    (hspine : leftSpine B = pref ++ pi0.drop m)
    (ch : List ℕ) (hch_len : ch.length = k)
    (hch_bg : lem59_BatchGapValid Δ' ch)
    (hch_bounds : ∀ f ∈ ch, m ≤ f ∧ f + 1 < pi0.length) :
    let pairOf := fun (f : ℕ) => ((pi0[f]?).getD 0, (pi0[f + 1]?).getD 0)
    IsGappedRightCascade B Δ' k (ch.map pairOf) := by
  intro pairOf
  have h0_lt : 0 < ch.length := by omega
  set f₀ := ch[0]'h0_lt
  have hf₀_mem : f₀ ∈ ch := List.getElem_mem h0_lt
  obtain ⟨hm_le_f0, hf0_lt⟩ := hch_bounds f₀ hf₀_mem
  set pref₀ := pref ++ (pi0.drop m).take (f₀ - m)
  have hspine0 : leftSpine B = pref₀ ++ pi0.drop f₀ := by
    rw [hspine, lem59_drop_take_drop pi0 m f₀ hm_le_f0, List.append_assoc]
  have hB_nonempty : ∃ rootK lB rB, B = .node rootK lB rB := by
    cases B with
    | nil =>
      simp only [leftSpine] at hspine0
      have hlen := congrArg List.length hspine0
      simp only [List.length_nil, List.length_append, List.length_drop] at hlen
      omega
    | node rk rl rr => exact ⟨rk, rl, rr, rfl⟩
  obtain ⟨rootK, lB, rB, hB_eq⟩ := hB_nonempty
  have hroot_mem : rootK ∈ B := by rw [hB_eq]; exact .here
  have hsub_root : subtreeAtKey B rootK = B := by
    rw [hB_eq]; simp [subtreeAtKey]
  obtain ⟨hbg_adj, hbg_ge0⟩ := lem59_batchGapValid_getElem Δ' ch hch_bg
  refine ⟨hk, by simp [hch_len], rootK, hroot_mem, ?_⟩
  let idx : Fin k → ℕ := fun r => pref₀.length + (ch[r.val]'(by omega) - f₀)
  refine ⟨idx, ?_, ?_⟩
  · intro r
    have hr_lt : r.val < ch.length := by omega
    set f_r := ch[r.val]'hr_lt
    have hfr_mem : f_r ∈ ch := List.getElem_mem hr_lt
    have hfr_lt : f_r + 1 < pi0.length := (hch_bounds f_r hfr_mem).2
    have hf0_le_fr : f₀ ≤ f_r := hbg_ge0 r.val hr_lt
    have hpath_eq : leftSpine (subtreeAtKey B rootK) = pref₀ ++ pi0.drop f₀ := by
      rw [hsub_root, hspine0]
    obtain ⟨hb, hpair⟩ :=
      lem59_path_pair_eq (leftSpine (subtreeAtKey B rootK)) pref₀ pi0 f₀ f_r
        hpath_eq hf0_le_fr hfr_lt
    refine ⟨hb, ?_⟩
    have hmap_get : (ch.map pairOf)[r.val]? = some (pairOf f_r) := by
      rw [List.getElem?_eq_getElem (by simp [hr_lt]), List.getElem_map]
    rw [hmap_get, Option.some.injEq]
    exact hpair.symm
  · intro r₁ r₂ hr12
    have hr1_lt : r₁.val < ch.length := by omega
    have hr1_adj_lt : r₁.val + 1 < ch.length := by omega
    have hr2_eq : ch[r₂.val]'(by omega) = ch[r₁.val + 1]'hr1_adj_lt := by
      congr 1; exact hr12.symm
    have hadj := hbg_adj r₁.val hr1_adj_lt
    have hge0 := hbg_ge0 r₁.val hr1_lt
    dsimp only [idx]
    rw [hr2_eq]
    omega

private theorem lem59_validTraj_batches
    (pi0 : List ℕ) (hpi0_pw : pi0.Pairwise (· < ·))
    (Δ' k : ℕ) (hk : 1 ≤ k) :
    ∀ (batches : List (List ℕ)) (B : BinaryTree ℕ) (m : ℕ) (pref : List ℕ),
      B.IsBST →
      leftSpine B = pref ++ pi0.drop m →
      (batches.flatten).Pairwise (fun a b => a + 2 ≤ b) →
      (∀ ch ∈ batches, ch.length = k ∧ lem59_BatchGapValid Δ' ch) →
      (∀ f ∈ batches.flatten, m ≤ f ∧ f + 1 < pi0.length) →
      let pairOf := fun (f : ℕ) => ((pi0[f]?).getD 0, (pi0[f + 1]?).getD 0)
      let stepF := fun (acc : BinaryTree ℕ) (f : ℕ) =>
        rotateRightEdge acc ((pi0[f]?).getD 0) ((pi0[f + 1]?).getD 0)
      let traj := batches.map (fun ch => RightCascadeTrajStep.cascadeBatch (ch.map pairOf))
      ValidRightCascadeTraj Δ' k B traj ∧
      countCascadeBatches traj = batches.length ∧
      traj.foldl RightCascadeTrajStep.step B = (batches.flatten).foldl stepF B
  | [], B, _, _, _, _, _, _, _ => ⟨trivial, rfl, rfl⟩
  | ch :: rest, B, m, pref, hB_bst, hspine, hpw_flat, hch_all, hf_all => by
    simp only [List.flatten_cons] at hpw_flat hf_all
    obtain ⟨hch_len, hch_bg⟩ := hch_all ch List.mem_cons_self
    have hch_bounds : ∀ f ∈ ch, m ≤ f ∧ f + 1 < pi0.length :=
      fun f hf => hf_all f (List.mem_append_left _ hf)
    have hpw_append := List.pairwise_append.mp hpw_flat
    have hcasc : IsGappedRightCascade B Δ' k
        (ch.map (fun f => ((pi0[f]?).getD 0, (pi0[f + 1]?).getD 0))) :=
      lem59_isGappedRightCascade_one_batch pi0 Δ' k hk B m pref hspine ch hch_len hch_bg hch_bounds
    set m_next := (rest.flatten.head?).getD pi0.length
    have hch_lt_mnext : ∀ f ∈ ch, f + 2 ≤ m_next := by
      intro f hf
      dsimp only [m_next]
      cases hrf : rest.flatten with
      | nil =>
        have := (hch_bounds f hf).2
        simp; omega
      | cons g₀ gs =>
        have hg₀_mem : g₀ ∈ rest.flatten := by rw [hrf]; exact List.mem_cons_self
        have := hpw_append.2.2 f hf g₀ hg₀_mem
        simp [this]
    have hm_le_mnext : m ≤ m_next := by
      have h0_lt : 0 < ch.length := by omega
      have hf0_mem : ch[0]'h0_lt ∈ ch := List.getElem_mem h0_lt
      have := (hch_bounds _ hf0_mem).1
      have := hch_lt_mnext _ hf0_mem
      omega
    have hrest_bounds : ∀ g ∈ rest.flatten, m_next ≤ g ∧ g + 1 < pi0.length := by
      intro g hg
      have hg_lt := (hf_all g (List.mem_append_right _ hg)).2
      refine ⟨?_, hg_lt⟩
      dsimp only [m_next]
      cases hrf : rest.flatten with
      | nil => rw [hrf] at hg; cases hg
      | cons g₀ gs =>
        rw [hrf] at hg
        simp only [List.head?_cons, Option.getD_some]
        rcases List.mem_cons.mp hg with rfl | hgs
        · exact le_rfl
        · have hpw_gs := hpw_append.2.1
          rw [hrf, List.pairwise_cons] at hpw_gs
          have := hpw_gs.1 g hgs
          omega
    obtain ⟨hB₁_bst, _, ⟨pref₁, hB₁_spine⟩, _, _⟩ :=
      lem59_foldl_selected_reach pi0 hpi0_pw ch B m m_next pref
        hB_bst hspine hpw_append.1
        (fun f hf => ⟨(hch_bounds f hf).1, (hch_bounds f hf).2, hch_lt_mnext f hf⟩)
        hm_le_mnext
    have hexec_eq :
        execRightCascadeBatch B (ch.map (fun f => ((pi0[f]?).getD 0, (pi0[f + 1]?).getD 0))) =
        ch.foldl (fun acc f => rotateRightEdge acc ((pi0[f]?).getD 0) ((pi0[f + 1]?).getD 0)) B := by
      simp [execRightCascadeBatch, List.foldl_map]
    obtain ⟨ih_valid, ih_count, ih_fold⟩ :=
      lem59_validTraj_batches pi0 hpi0_pw Δ' k hk rest
        (execRightCascadeBatch B (ch.map (fun f => ((pi0[f]?).getD 0, (pi0[f + 1]?).getD 0))))
        m_next pref₁
        (hexec_eq.symm ▸ hB₁_bst) (hexec_eq.symm ▸ hB₁_spine)
        hpw_append.2.1
        (fun ch' hch' => hch_all ch' (List.mem_cons_of_mem ch hch'))
        hrest_bounds
    simp only [List.map_cons, ValidRightCascadeTraj, countCascadeBatches,
      List.length_cons, List.foldl_cons, RightCascadeTrajStep.step,
      List.flatten_cons, List.foldl_append]
    exact ⟨⟨hcasc, ih_valid⟩, by omega, by rw [ih_fold, hexec_eq]⟩

private theorem lem59_validTraj_append {α : Type} [LinearOrder α] (Δ' k : ℕ) :
    ∀ (t₁ t₂ : List (RightCascadeTrajStep α)) (B : BinaryTree α),
      ValidRightCascadeTraj Δ' k B t₁ →
      ValidRightCascadeTraj Δ' k (t₁.foldl RightCascadeTrajStep.step B) t₂ →
      ValidRightCascadeTraj Δ' k B (t₁ ++ t₂)
  | [], _, _, _, h₂ => h₂
  | .singleRot x y :: rest, t₂, B, h₁, h₂ =>
    ⟨h₁.1, h₁.2.1, lem59_validTraj_append Δ' k rest t₂ (rotateRightEdge B x y) h₁.2.2 h₂⟩
  | .cascadeBatch pairs :: rest, t₂, B, h₁, h₂ =>
    ⟨h₁.1, lem59_validTraj_append Δ' k rest t₂ (execRightCascadeBatch B pairs) h₁.2 h₂⟩

private theorem lem59_countCascadeBatches_append {α : Type} :
    ∀ (t₁ t₂ : List (RightCascadeTrajStep α)),
      countCascadeBatches (t₁ ++ t₂) = countCascadeBatches t₁ + countCascadeBatches t₂
  | [], _ => by simp [countCascadeBatches]
  | .singleRot _ _ :: rest, t₂ => lem59_countCascadeBatches_append rest t₂
  | .cascadeBatch _ :: rest, t₂ => by
    simp only [List.cons_append, countCascadeBatches, lem59_countCascadeBatches_append rest t₂]
    omega

private theorem lem59_exists_traj_of_rightRotReachable {α : Type} [LinearOrder α]
    (Δ' k : ℕ) {B₁ B₂ : BinaryTree α} (h : RightRotReachable B₁ B₂) :
    ∃ traj : List (RightCascadeTrajStep α),
      ValidRightCascadeTraj Δ' k B₁ traj ∧
      traj.foldl RightCascadeTrajStep.step B₁ = B₂ ∧
      countCascadeBatches traj = 0 := by
  induction h with
  | refl => exact ⟨[], trivial, rfl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨traj, hv, hf, hc⟩ := ih
    rcases hstep with ⟨x, y, hxy, hedge, rfl⟩
    refine ⟨traj ++ [.singleRot x y], ?_, ?_, ?_⟩
    · apply lem59_validTraj_append Δ' k traj [.singleRot x y] B₁ hv
      rw [hf]
      exact ⟨hxy, hedge, trivial⟩
    · simp [List.foldl_append, hf, RightCascadeTrajStep.step]
    · rw [lem59_countCascadeBatches_append, hc]
      rfl

private theorem lem59_maximal_run (P_in : ℕ → Prop) [DecidablePred P_in]
    (len : ℕ) (hlen : 1 ≤ len) (hlast : ¬ P_in (len - 1))
    (f : ℕ) (hf_lt : f + 1 < len) (hf : P_in f) :
    ∃ a b : ℕ,
      a ≤ f ∧ f ≤ b ∧ b + 1 < len ∧
      (∀ t : ℕ, a ≤ t → t ≤ b → P_in t) ∧
      (a = 0 ∨ ¬ P_in (a - 1)) ∧
      ¬ P_in (b + 1) := by
  have hleft : ∀ x : ℕ, P_in x →
      ∃ a : ℕ, a ≤ x ∧ (∀ t : ℕ, a ≤ t → t ≤ x → P_in t) ∧ (a = 0 ∨ ¬ P_in (a - 1)) := by
    intro x
    induction x with
    | zero =>
      intro hx
      refine ⟨0, le_rfl, ?_, Or.inl rfl⟩
      intro t _ ht0
      have : t = 0 := by omega
      subst t; exact hx
    | succ x' ih =>
      intro hx
      by_cases hprev : P_in x'
      · obtain ⟨a, ha_le, ha_all, ha_bd⟩ := ih hprev
        refine ⟨a, by omega, ?_, ha_bd⟩
        intro t hat htx
        rcases eq_or_lt_of_le htx with rfl | hlt
        · exact hx
        · exact ha_all t hat (by omega)
      · refine ⟨x' + 1, le_rfl, ?_, Or.inr hprev⟩
        intro t hat htx
        have : t = x' + 1 := by omega
        subst t; exact hx
  have hright : ∀ (d x : ℕ), x + d = len - 1 → P_in x →
      ∃ b : ℕ, x ≤ b ∧ b + 1 < len ∧ (∀ t : ℕ, x ≤ t → t ≤ b → P_in t) ∧ ¬ P_in (b + 1) := by
    intro d
    induction d with
    | zero =>
      intro x hxd hx
      exfalso
      have : x = len - 1 := by omega
      subst x; exact hlast hx
    | succ d' ih =>
      intro x hxd hx
      by_cases hnext : P_in (x + 1)
      · obtain ⟨b, hb_ge, hb_lt, hb_all, hb_bd⟩ := ih (x + 1) (by omega) hnext
        refine ⟨b, by omega, hb_lt, ?_, hb_bd⟩
        intro t hxt htb
        rcases eq_or_lt_of_le hxt with rfl | hlt
        · exact hx
        · exact hb_all t (by omega) htb
      · refine ⟨x, le_rfl, by omega, ?_, hnext⟩
        intro t hxt htx
        have : t = x := by omega
        subst t; exact hx
  obtain ⟨a, ha_le, ha_all, ha_bd⟩ := hleft f hf
  obtain ⟨b, hb_ge, hb_lt, hb_all, hb_bd⟩ := hright (len - 1 - f) f (by omega) hf
  refine ⟨a, b, ha_le, hb_ge, hb_lt, ?_, ha_bd, hb_bd⟩
  intro t hat htb
  by_cases htf : t ≤ f
  · exact ha_all t hat htf
  · exact hb_all t (by omega) htb

private theorem lem59_pairwise_sublist {α : Type} {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, l₁.Sublist l₂ → l₂.Pairwise R → l₁.Pairwise R
  | _, _, .slnil, _ => .nil
  | _, _ :: _, .cons _ hsub, hpw =>
    lem59_pairwise_sublist hsub (List.pairwise_cons.mp hpw).2
  | _ :: _, _ :: _, .cons_cons a hsub, hpw => by
    obtain ⟨ha, hrest⟩ := List.pairwise_cons.mp hpw
    exact List.pairwise_cons.mpr ⟨fun x hx => ha x (hsub.subset hx), lem59_pairwise_sublist hsub hrest⟩

private theorem lem59_sum_piece_bounds (c : ℕ) (pieces : List (List ℕ)) (nb : List ℕ → ℕ)
    (h : ∀ pc ∈ pieces, pc.length ≤ c * (1 + nb pc)) :
    (pieces.map List.length).sum ≤ c * pieces.length + c * (pieces.map nb).sum := by
  induction pieces with
  | nil => simp
  | cons pc rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hpc := h pc List.mem_cons_self
    have hrest := ih (fun q hq => h q (List.mem_cons_of_mem pc hq))
    nlinarith

end CascadeBatchHelpers

section PhaseAndMainProof

private theorem lem59_phase_traj
    (hAckPow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1)
    (h_4_1 : ∀ (n : ℕ), 1 ≤ n → ∀ (t₁ t₂ : BinaryTree ℕ),
      t₁.IsBST → t₂.IsBST →
      keyFinset t₁ = Finset.Icc 1 n → keyFinset t₂ = Finset.Icc 1 n →
      (RightRotReachable t₁ t₂ ↔ ∀ v ∈ Finset.Icc 1 n, rightReach t₁ v ≤ rightReach t₂ v))
    (P r M : ℕ) (T : ScaleTree) (hValid : ValidScaleTree P r M T)
    (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock)
    (U_witness : Finset ℕ)
    (p : ℕ)
    (hp : p ∈ Finset.Icc 1 ((childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length - 1))
    (hKX2 : 2 ≤ (childSubblocks (scaleTreePartitionChain T P M ℓ.succ) X).length)
    (h57_phase :
      let chain := scaleTreePartitionChain T P M
      let ℓ_val := ℓ.val + 1
      let subs := childSubblocks (chain ℓ.succ) X
      let K_X := subs.length
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
          (phaseSummaryBST P proc chain ℓ_val X p τ₂)))
    (h58_part1 :
      let chain := scaleTreePartitionChain T P M
      let ℓ_val := ℓ.val + 1
      let subs := childSubblocks (chain ℓ.succ) X
      let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
      let G_end := phaseSummaryBST P proc chain ℓ_val X p (tauEmpty proc (subblock1 subs p))
      let pi0 := leftSpine G₀
      let Fp := promotedSubblockIndices P proc chain ℓ_val X p
      1 ≤ pi0.length ∧
      (∀ c ∈ Fp, c ∈ pi0.dropLast) ∧
      (∀ a b : ℕ, a ≤ b → b + 1 < pi0.length →
        (∀ t : ℕ, a ≤ t → t ≤ b → (pi0[t]?).getD 0 ∈ Fp) →
        (a = 0 ∨ (pi0[a - 1]?).getD 0 ∉ Fp) →
        (pi0[b + 1]?).getD 0 ∉ Fp →
        (∀ t : ℕ, a ≤ t → t < b →
          leadPopKey P proc chain ℓ_val X p ((pi0[t + 1]?).getD 0) <
            leadPopKey P proc chain ℓ_val X p ((pi0[t]?).getD 0)) ∧
        (∀ t : ℕ, a ≤ t → t ≤ b →
          rightReach G₀ ((pi0[b + 1]?).getD 0) ≤ rightReach G_end ((pi0[t]?).getD 0))))
    (h58_part2 :
      let chain := scaleTreePartitionChain T P M
      let ℓ_val := ℓ.val + 1
      let subs := childSubblocks (chain ℓ.succ) X
      let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
      let pi0 := leftSpine G₀
      let Fp := promotedSubblockIndices P proc chain ℓ_val X p
      U_witness ⊆ pi0.toFinset \ Fp ∧
      ∀ a b : ℕ, a < b → b < pi0.length →
        (pi0[a]?).getD 0 ∈ Fp → (pi0[b]?).getD 0 ∈ Fp →
        (∀ t : ℕ, a < t → t < b → (pi0[t]?).getD 0 ∉ Fp) →
        scaleI T P ℓ_val < b - a - 1 →
        let g := b - a - 1
        let gapSet := (Finset.Ioo a b).image (fun t => (pi0[t]?).getD 0)
        g - 3 ≤ (U_witness ∩ gapSet).card ∧
        scaleI T P ℓ_val < 2 * (g - 3)) :
    let chain := scaleTreePartitionChain T P M
    let ℓ_val := ℓ.val + 1
    let subs := childSubblocks (chain ℓ.succ) X
    let i_ℓ := scaleI T P ℓ_val
    let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
    let G_fin := phaseSummaryBST P proc chain ℓ_val X p
      (proc.popStepIdx (subblock1 subs (p + 1)).lo)
    ∃ traj : List (RightCascadeTrajStep ℕ),
      ValidRightCascadeTraj (2 * i_ℓ) (2 * i_ℓ) G₀ traj ∧
      traj.foldl RightCascadeTrajStep.step G₀ = G_fin ∧
      (leadExitSet P proc chain ℓ_val X p).card ≤
        4 * i_ℓ * (1 + countCascadeBatches traj) + 8 * U_witness.card := by
  dsimp only at h57_phase h58_part1 h58_part2 ⊢
  set chain := scaleTreePartitionChain T P M
  set ℓ_val := ℓ.val + 1
  set subs := childSubblocks (chain ℓ.succ) X
  set K_X := subs.length
  set i_ℓ := scaleI T P ℓ_val
  have hi5 : 5 ≤ i_ℓ := lem59_scaleI_ge_five hAckPow P r M T hValid ℓ
  have hp_mem := Finset.mem_Icc.mp hp
  have hpK : p + 1 ≤ K_X := by omega
  set tStart := proc.popStepIdx (subblock1 subs p).lo
  set tEmpty := tauEmpty proc (subblock1 subs p)
  set tNext := proc.popStepIdx (subblock1 subs (p + 1)).lo
  obtain ⟨ht1, ht2, hBST_keys, hReach_seg⟩ := h57_phase
  have htEnd_eq : (if p + 1 ≤ K_X then tNext else proc.steps.length) = tNext := by simp [hpK]
  rw [htEnd_eq] at ht2 hBST_keys hReach_seg
  set G₀ := phaseSummaryBST P proc chain ℓ_val X p tStart
  set G_end := phaseSummaryBST P proc chain ℓ_val X p tEmpty
  set G_fin := phaseSummaryBST P proc chain ℓ_val X p tNext
  obtain ⟨hG₀_bst, hG₀_keys⟩ := hBST_keys tStart (Finset.mem_Icc.mpr ⟨le_rfl, le_trans ht1 ht2⟩)
  obtain ⟨hGend_bst, hGend_keys⟩ := hBST_keys tEmpty (Finset.mem_Icc.mpr ⟨ht1, ht2⟩)
  have hReach_0_end : RightRotReachable G₀ G_end := hReach_seg tStart tEmpty le_rfl ht1 ht2
  have hReach_end_fin : RightRotReachable G_end G_fin := hReach_seg tEmpty tNext ht1 ht2 le_rfl
  set pi0 := leftSpine G₀
  set Fp := promotedSubblockIndices P proc chain ℓ_val X p
  obtain ⟨hpi0_len1, hFp_dropLast, hRun⟩ := h58_part1
  obtain ⟨_, hWit⟩ := h58_part2
  have hpi0_pw : pi0.Pairwise (· < ·) := lem59_leftSpine_pairwise_lt G₀ hG₀_bst
  set Fpos : List ℕ := (List.range pi0.length).filter (fun t => decide ((pi0[t]?).getD 0 ∈ Fp))
  have hFpos_pw : Fpos.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
  have hFpos_iff : ∀ t : ℕ, t ∈ Fpos ↔ t < pi0.length ∧ (pi0[t]?).getD 0 ∈ Fp := by
    intro t
    simp [Fpos, List.mem_filter, List.mem_range]
  have hFpos_lt : ∀ t ∈ Fpos, t + 1 < pi0.length := by
    intro t ht
    obtain ⟨ht_lt, ht_in⟩ := (hFpos_iff t).mp ht
    have hdl := hFp_dropLast _ ht_in
    rw [List.dropLast_eq_take] at hdl
    obtain ⟨s, hs_lt, hs_eq⟩ := List.mem_iff_getElem.mp hdl
    rw [List.length_take] at hs_lt
    have hs_lt_pi : s < pi0.length := by omega
    have hs_get : (pi0.take (pi0.length - 1))[s] = (pi0[s]?).getD 0 := by
      rw [List.getElem_take]
      simp [hs_lt_pi]
    rw [hs_get] at hs_eq
    by_cases hst : s = t
    · omega
    · exact absurd hs_eq (lem59_getD_ne_of_pairwise_lt pi0 hpi0_pw s t hs_lt_pi ht_lt hst)
  have hFp_card_le : Fp.card ≤ Fpos.length := by
    have hsub_img : Fp ⊆ Fpos.toFinset.image (fun t => (pi0[t]?).getD 0) := by
      intro c hc
      have hc_dl := hFp_dropLast c hc
      rw [List.dropLast_eq_take] at hc_dl
      obtain ⟨t, ht_lt_tk, rfl⟩ := List.mem_iff_getElem.mp hc_dl
      rw [List.length_take] at ht_lt_tk
      have ht_lt : t < pi0.length := by omega
      have ht_get : (pi0[t]?).getD 0 = (pi0.take (pi0.length - 1))[t] := by
        rw [List.getElem_take]
        simp [ht_lt]
      rw [Finset.mem_image]
      refine ⟨t, ?_, ht_get⟩
      rw [List.mem_toFinset, hFpos_iff]
      exact ⟨ht_lt, ht_get.symm ▸ hc⟩
    calc Fp.card
        ≤ (Fpos.toFinset.image (fun t => (pi0[t]?).getD 0)).card := Finset.card_le_card hsub_img
      _ ≤ Fpos.toFinset.card := Finset.card_image_le
      _ ≤ Fpos.length := List.toFinset_card_le Fpos
  have hlead_le_Fp : (leadExitSet P proc chain ℓ_val X p).card ≤ Fp.card :=
    lem59_leadExitSet_card_le P proc chain ℓ_val X p
  cases hFpos_eq : Fpos with
  | nil =>
    rw [hFpos_eq, List.length_nil] at hFp_card_le
    have hReach_0_fin : RightRotReachable G₀ G_fin := hReach_0_end.trans hReach_end_fin
    obtain ⟨traj, hv, hf, hc⟩ :=
      lem59_exists_traj_of_rightRotReachable (2 * i_ℓ) (2 * i_ℓ) hReach_0_fin
    exact ⟨traj, hv, hf, by omega⟩
  | cons fhead ftail =>
    set W : Finset ℕ := (Finset.range pi0.length).filter (fun t => (pi0[t]?).getD 0 ∈ U_witness)
    have hW_card_le : W.card ≤ U_witness.card := by
      let f := fun t : ℕ => (pi0[t]?).getD 0
      have hinj : Set.InjOn f W := by
        intro t₁ ht₁ t₂ ht₂ hfeq
        simp only [W, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ht₁ ht₂
        by_contra hne
        exact lem59_getD_ne_of_pairwise_lt pi0 hpi0_pw t₁ t₂ ht₁.1 ht₂.1 hne hfeq
      have himg_sub : W.image f ⊆ U_witness := by
        intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨t, htW, rfl⟩ := hx
        simp only [W, Finset.mem_filter] at htW
        exact htW.2
      calc W.card = (W.image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ U_witness.card := Finset.card_le_card himg_sub
    have hGap_W : ∀ a ∈ fhead :: ftail, ∀ b ∈ fhead :: ftail, a < b →
        (∀ t ∈ fhead :: ftail, ¬ (a < t ∧ t < b)) →
        i_ℓ < b - a - 1 →
        i_ℓ < 2 * (W.filter (fun t => a < t ∧ t < b)).card := by
      intro a ha b hb hab hadj hbig
      rw [← hFpos_eq] at ha hb hadj
      obtain ⟨_, ha_Fp⟩ := (hFpos_iff a).mp ha
      obtain ⟨hb_lt, hb_Fp⟩ := (hFpos_iff b).mp hb
      have hno_mid : ∀ t : ℕ, a < t → t < b → (pi0[t]?).getD 0 ∉ Fp := by
        intro t hat htb ht_in
        have ht_Fpos : t ∈ Fpos := (hFpos_iff t).mpr ⟨by omega, ht_in⟩
        exact hadj t ht_Fpos ⟨hat, htb⟩
      have hwit_ab := hWit a b hab hb_lt ha_Fp hb_Fp hno_mid hbig
      obtain ⟨hg1, hg2⟩ := hwit_ab
      have hsub_gap : U_witness ∩ ((Finset.Ioo a b).image (fun t => (pi0[t]?).getD 0)) ⊆
          (W.filter (fun t => a < t ∧ t < b)).image (fun t => (pi0[t]?).getD 0) := by
        intro x hx
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_Ioo] at hx
        obtain ⟨hxU, t, ⟨hat, htb⟩, rfl⟩ := hx
        rw [Finset.mem_image]
        refine ⟨t, ?_, rfl⟩
        simp only [W, Finset.mem_filter, Finset.mem_range]
        exact ⟨⟨by omega, hxU⟩, hat, htb⟩
      have hcard_gap : (U_witness ∩ ((Finset.Ioo a b).image (fun t => (pi0[t]?).getD 0))).card ≤
          (W.filter (fun t => a < t ∧ t < b)).card :=
        le_trans (Finset.card_le_card hsub_gap) Finset.card_image_le
      omega
    have hpw_cons : (fhead :: ftail).Pairwise (· < ·) := hFpos_eq ▸ hFpos_pw
    obtain ⟨_, hflat_pieces, hpc_props, hcross_pieces, hps_bound⟩ :=
      lem59_cutPiecesAux_spec i_ℓ (by omega) W ftail fhead hpw_cons hGap_W
    set res := lem59_cutPiecesAux i_ℓ fhead ftail
    set pieces := res.1 :: res.2
    set chunksOf := fun pc : List ℕ => lem59_fullChunks (2 * i_ℓ) (lem59_evenIdx pc)
    set allBatches := pieces.flatMap chunksOf
    have hk_pos : 1 ≤ 2 * i_ℓ := by omega
    have hpiece_chunk_props : ∀ pc ∈ pieces,
        (∀ ch ∈ chunksOf pc, ch.length = 2 * i_ℓ ∧ lem59_BatchGapValid (2 * i_ℓ) ch) ∧
        (chunksOf pc).flatten.Sublist pc ∧
        ((chunksOf pc).flatten).Pairwise (fun a b => a + 2 ≤ b) ∧
        pc.length ≤ 4 * i_ℓ * (1 + (chunksOf pc).length) := by
      intro pc hpc
      obtain ⟨_, hpc_pw, hpc_gap⟩ := hpc_props pc hpc
      obtain ⟨hev_sub, hev_len, hev_pw2, hev_bg⟩ := lem59_evenIdx_spec i_ℓ pc hpc_pw hpc_gap
      obtain ⟨hch_all, hch_sub, hch_len⟩ :=
        lem59_fullChunks_spec (2 * i_ℓ) (2 * i_ℓ) hk_pos (lem59_evenIdx pc) hev_bg
      refine ⟨hch_all, hch_sub.trans hev_sub, lem59_pairwise_sublist hch_sub hev_pw2, ?_⟩
      dsimp only [chunksOf]
      nlinarith
    have hall_ch : ∀ ch ∈ allBatches, ch.length = 2 * i_ℓ ∧ lem59_BatchGapValid (2 * i_ℓ) ch := by
      intro ch hch
      rw [List.mem_flatMap] at hch
      obtain ⟨pc, hpc, hch_pc⟩ := hch
      exact (hpiece_chunk_props pc hpc).1 ch hch_pc
    have hall_flat_eq : allBatches.flatten = pieces.flatMap (fun pc => (chunksOf pc).flatten) :=
      lem59_flatten_flatMap pieces chunksOf
    have hall_flat_pw : (allBatches.flatten).Pairwise (fun a b => a + 2 ≤ b) := by
      rw [hall_flat_eq]
      apply lem59_pairwise_flatMap_nat pieces (fun pc => (chunksOf pc).flatten) hcross_pieces
      · intro pc hpc; exact (hpiece_chunk_props pc hpc).2.2.1
      · intro pc hpc a ha; exact (hpiece_chunk_props pc hpc).2.1.subset ha
    have hall_in_Fpos : ∀ f ∈ allBatches.flatten, f ∈ Fpos := by
      intro f hf
      rw [hall_flat_eq, List.mem_flatMap] at hf
      obtain ⟨pc, hpc, hf_ch⟩ := hf
      have hf_pc : f ∈ pc := (hpiece_chunk_props pc hpc).2.1.subset hf_ch
      have hf_flat : f ∈ pieces.flatten := List.mem_flatten.mpr ⟨pc, hpc, hf_pc⟩
      rw [hflat_pieces, ← hFpos_eq] at hf_flat
      exact hf_flat
    have hall_bounds : ∀ f ∈ allBatches.flatten, 0 ≤ f ∧ f + 1 < pi0.length :=
      fun f hf => ⟨Nat.zero_le f, hFpos_lt f (hall_in_Fpos f hf)⟩
    have hG₀_spine : leftSpine G₀ = [] ++ pi0.drop 0 := by simp [pi0]
    obtain ⟨hvalid₁, hcount₁, hfold₁⟩ :=
      lem59_validTraj_batches pi0 hpi0_pw (2 * i_ℓ) (2 * i_ℓ) hk_pos
        allBatches G₀ 0 [] hG₀_bst hG₀_spine hall_flat_pw hall_ch hall_bounds
    set pairOf := fun (f : ℕ) => ((pi0[f]?).getD 0, (pi0[f + 1]?).getD 0)
    set traj₁ := allBatches.map (fun ch => RightCascadeTrajStep.cascadeBatch (ch.map pairOf))
    set G₁ := traj₁.foldl RightCascadeTrajStep.step G₀
    obtain ⟨hG₁_bst, hG₁_keys_eq, _, hG₁_sel, hG₁_unsel⟩ :=
      lem59_foldl_selected_reach pi0 hpi0_pw allBatches.flatten G₀ 0 (pi0.length + 1) []
        hG₀_bst hG₀_spine hall_flat_pw
        (fun f hf => ⟨Nat.zero_le f, (hall_bounds f hf).2, by have := (hall_bounds f hf).2; omega⟩)
        (Nat.zero_le _)
    rw [← hfold₁] at hG₁_bst hG₁_keys_eq hG₁_sel hG₁_unsel
    have hG₁_keys : keyFinset G₁ = Finset.Icc (p + 1) K_X := hG₁_keys_eq.trans hG₀_keys
    have hlast_not_Fp : (pi0[pi0.length - 1]?).getD 0 ∉ Fp := by
      intro hlast_in
      have hmem_Fpos : pi0.length - 1 ∈ Fpos :=
        (hFpos_iff (pi0.length - 1)).mpr ⟨by omega, hlast_in⟩
      have hlt := hFpos_lt (pi0.length - 1) hmem_Fpos
      omega
    have hReach_G₁_end : RightRotReachable G₁ G_end := by
      apply lem59_rightRotReachable_shifted h_4_1 p K_X hpK G₁ G_end hG₁_bst hGend_bst
        hG₁_keys hGend_keys
      intro u hu
      by_cases hsel : ∃ f ∈ allBatches.flatten, u = (pi0[f]?).getD 0
      · obtain ⟨f, hf_sel, rfl⟩ := hsel
        rw [hG₁_sel f hf_sel]
        have hf_Fpos : f ∈ Fpos := hall_in_Fpos f hf_sel
        have hf_lt1 : f + 1 < pi0.length := hFpos_lt f hf_Fpos
        have hf_Fp : (pi0[f]?).getD 0 ∈ Fp := ((hFpos_iff f).mp hf_Fpos).2
        obtain ⟨a, b, haf, hfb, hb_lt1, hab_all, ha_left, hb_right⟩ :=
          lem59_maximal_run (fun t => (pi0[t]?).getD 0 ∈ Fp)
            pi0.length hpi0_len1 hlast_not_Fp f hf_lt1 hf_Fp
        have hrun_res := (hRun a b (le_trans haf hfb) hb_lt1 hab_all ha_left hb_right).2 f haf hfb
        have hf1_mem : (pi0[f + 1]?).getD 0 ∈ leftSpine G₀ := by
          have : (pi0[f + 1]?).getD 0 = pi0[f + 1] := by simp [hf_lt1]
          rw [this]; exact List.getElem_mem hf_lt1
        have hb1_mem : (pi0[b + 1]?).getD 0 ∈ leftSpine G₀ := by
          have : (pi0[b + 1]?).getD 0 = pi0[b + 1] := by simp [hb_lt1]
          rw [this]; exact List.getElem_mem hb_lt1
        have hf1_le_b1 : (pi0[f + 1]?).getD 0 ≤ (pi0[b + 1]?).getD 0 :=
          lem59_getD_le_of_pairwise_lt pi0 hpi0_pw (f + 1) (b + 1) hf_lt1 hb_lt1 (by omega)
        have hmono := lem59_rightReach_mono_leftSpine G₀ hG₀_bst _ _ hf1_mem hb1_mem hf1_le_b1
        exact le_trans hmono hrun_res
      · have hsel' : ∀ f ∈ allBatches.flatten, u ≠ (pi0[f]?).getD 0 :=
          fun f hf h => hsel ⟨f, hf, h⟩
        rw [hG₁_unsel u hsel']
        exact (lem59_rightRotReachable_bst_and_reach hReach_0_end hG₀_bst).2 u
    have hReach_G₁_fin : RightRotReachable G₁ G_fin := hReach_G₁_end.trans hReach_end_fin
    obtain ⟨traj₂, hvalid₂, hfold₂, hcount₂⟩ :=
      lem59_exists_traj_of_rightRotReachable (2 * i_ℓ) (2 * i_ℓ) hReach_G₁_fin
    refine ⟨traj₁ ++ traj₂,
      lem59_validTraj_append (2 * i_ℓ) (2 * i_ℓ) traj₁ traj₂ G₀ hvalid₁ hvalid₂,
      by rw [List.foldl_append]; exact hfold₂, ?_⟩
    rw [lem59_countCascadeBatches_append, hcount₁, hcount₂, Nat.add_zero]
    have hFpos_len : Fpos.length = (pieces.map List.length).sum := by
      rw [hFpos_eq, ← hflat_pieces, List.length_flatten]
    have hallBatches_len : allBatches.length =
        (pieces.map (fun pc => (chunksOf pc).length)).sum := by
      simp [allBatches, List.length_flatMap]
    have hsum_pieces := lem59_sum_piece_bounds (4 * i_ℓ) pieces
      (fun pc => (chunksOf pc).length)
      (fun pc hpc => (hpiece_chunk_props pc hpc).2.2.2)
    have hpieces_len : pieces.length = 1 + res.2.length := by simp [pieces]; omega
    have hW_fil_le : (W.filter (fun t => fhead < t)).card ≤ W.card :=
      Finset.card_filter_le _ _
    nlinarith

private theorem lem59_block_concat
    (C_casc : ℝ) (hCcasc : IsCascadeBoundConst C_casc)
    (hAckPow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1)
    (hAckStep : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
      ackermann (i - 1) j ≤ ackermann i j ∧ 2 ^ j ≤ ackermann i j)
    (h_4_1 : ∀ (n : ℕ), 1 ≤ n → ∀ (t₁ t₂ : BinaryTree ℕ),
      t₁.IsBST → t₂.IsBST →
      keyFinset t₁ = Finset.Icc 1 n → keyFinset t₂ = Finset.Icc 1 n →
      (RightRotReachable t₁ t₂ ↔ ∀ v ∈ Finset.Icc 1 n, rightReach t₁ v ≤ rightReach t₂ v))
    (P r M : ℕ) (T : ScaleTree) (hValid : ValidScaleTree P r M T)
    (proc : FoldedPopProcess P)
    (ℓ : Fin M) (X : IntervalBlock) (hX : X ∈ scaleTreePartitionChain T P M ℓ.castSucc)
    (U_witness : ℕ → Finset ℕ)
    (h57 :
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
            topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G))))
    (h58_1 :
      let chain := scaleTreePartitionChain T P M
      let ℓ_val := ℓ.val + 1
      let subs := childSubblocks (chain ℓ.succ) X
      ∀ p ∈ Finset.Icc 1 (subs.length - 1),
        let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
        let G_end := phaseSummaryBST P proc chain ℓ_val X p (tauEmpty proc (subblock1 subs p))
        let pi0 := leftSpine G₀
        let Fp := promotedSubblockIndices P proc chain ℓ_val X p
        1 ≤ pi0.length ∧
        (∀ c ∈ Fp, c ∈ pi0.dropLast) ∧
        (∀ a b : ℕ, a ≤ b → b + 1 < pi0.length →
          (∀ t : ℕ, a ≤ t → t ≤ b → (pi0[t]?).getD 0 ∈ Fp) →
          (a = 0 ∨ (pi0[a - 1]?).getD 0 ∉ Fp) →
          (pi0[b + 1]?).getD 0 ∉ Fp →
          (∀ t : ℕ, a ≤ t → t < b →
            leadPopKey P proc chain ℓ_val X p ((pi0[t + 1]?).getD 0) <
              leadPopKey P proc chain ℓ_val X p ((pi0[t]?).getD 0)) ∧
          (∀ t : ℕ, a ≤ t → t ≤ b →
            rightReach G₀ ((pi0[b + 1]?).getD 0) ≤ rightReach G_end ((pi0[t]?).getD 0))))
    (h58_2 :
      let chain := scaleTreePartitionChain T P M
      let ℓ_val := ℓ.val + 1
      let subs := childSubblocks (chain ℓ.succ) X
      ∀ p ∈ Finset.Icc 1 (subs.length - 1),
        let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
        let pi0 := leftSpine G₀
        let Fp := promotedSubblockIndices P proc chain ℓ_val X p
        U_witness p ⊆ pi0.toFinset \ Fp ∧
        ∀ a b : ℕ, a < b → b < pi0.length →
          (pi0[a]?).getD 0 ∈ Fp → (pi0[b]?).getD 0 ∈ Fp →
          (∀ t : ℕ, a < t → t < b → (pi0[t]?).getD 0 ∉ Fp) →
          scaleI T P ℓ_val < b - a - 1 →
          let g := b - a - 1
          let gapSet := (Finset.Ioo a b).image (fun t => (pi0[t]?).getD 0)
          g - 3 ≤ (U_witness p ∩ gapSet).card ∧
          scaleI T P ℓ_val < 2 * (g - 3)) :
    let chain := scaleTreePartitionChain T P M
    let subs := childSubblocks (chain ℓ.succ) X
    let i_ℓ := scaleI T P (ℓ.val + 1)
    ((∑ p ∈ Finset.Icc 1 (subs.length - 1),
        (leadExitSet P proc chain (ℓ.val + 1) X p).card : ℕ) : ℝ) ≤
      4 * (i_ℓ : ℝ) * (1 + C_casc * (2 * (i_ℓ : ℝ) + 1)) * ((subs.length - 1 : ℕ) : ℝ) +
      8 * ((∑ p ∈ Finset.Icc 1 (subs.length - 1), (U_witness p).card : ℕ) : ℝ) := by
  dsimp only at h57 h58_1 h58_2 ⊢
  set chain := scaleTreePartitionChain T P M
  set ℓ_val := ℓ.val + 1
  set subs := childSubblocks (chain ℓ.succ) X
  set K_X := subs.length
  set i_ℓ := scaleI T P ℓ_val
  have hi5 : 5 ≤ i_ℓ := lem59_scaleI_ge_five hAckPow P r M T hValid ℓ
  obtain ⟨hKX2, h57_phases, hBridge, hEmbed⟩ := h57
  let startT := fun p : ℕ =>
    phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
  let endT := fun p : ℕ =>
    phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs (p + 1)).lo)
  have hphase_lifted : ∀ p ∈ Finset.Icc 1 (K_X - 1),
      (topEmbedPhase p (startT p)).IsBST ∧
      keyFinset (topEmbedPhase p (startT p)) = Finset.Icc 2 K_X ∧
      ∃ traj : List (RightCascadeTrajStep ℕ),
        ValidRightCascadeTraj (2 * i_ℓ) (2 * i_ℓ) (topEmbedPhase p (startT p)) traj ∧
        traj.foldl RightCascadeTrajStep.step (topEmbedPhase p (startT p)) =
          topEmbedPhase p (endT p) ∧
        (leadExitSet P proc chain ℓ_val X p).card ≤
          4 * i_ℓ * (1 + countCascadeBatches traj) + 8 * (U_witness p).card := by
    intro p hp
    have hp_raw := h57_phases p hp
    obtain ⟨ht1, ht2, hbk, hreach, _⟩ := hp_raw
    obtain ⟨hG0_bst, hG0_keys⟩ :=
      hbk (proc.popStepIdx (subblock1 subs p).lo) (Finset.mem_Icc.mpr ⟨le_rfl, le_trans ht1 ht2⟩)
    obtain ⟨traj, hv, hf, hcard⟩ :=
      lem59_phase_traj hAckPow h_4_1 P r M T hValid proc ℓ X (U_witness p) p hp hKX2
        ⟨ht1, ht2, hbk, hreach⟩ (h58_1 p hp) (h58_2 p hp)
    obtain ⟨he_bst, he_keys, he_valid, he_fold⟩ :=
      hEmbed p hp (2 * i_ℓ) (2 * i_ℓ) (startT p) traj hG0_bst hG0_keys hv
    refine ⟨he_bst, he_keys, traj, he_valid, ?_, hcard⟩
    rw [he_fold, hf]
  have hind : ∀ d : ℕ, d + 1 ≤ K_X - 1 →
      ∃ T_acc : List (RightCascadeTrajStep ℕ),
        ValidRightCascadeTraj (2 * i_ℓ) (2 * i_ℓ) (topEmbedPhase 1 (startT 1)) T_acc ∧
        T_acc.foldl RightCascadeTrajStep.step (topEmbedPhase 1 (startT 1)) =
          topEmbedPhase (d + 1) (endT (d + 1)) ∧
        (∑ p ∈ Finset.Icc 1 (d + 1), (leadExitSet P proc chain ℓ_val X p).card) ≤
          4 * i_ℓ * ((d + 1) + countCascadeBatches T_acc) +
          8 * (∑ p ∈ Finset.Icc 1 (d + 1), (U_witness p).card) := by
    intro d
    induction d with
    | zero =>
      intro hd
      have h1_mem : 1 ∈ Finset.Icc 1 (K_X - 1) := Finset.mem_Icc.mpr ⟨le_rfl, hd⟩
      obtain ⟨_, _, traj₁, hv₁, hf₁, hcard₁⟩ := hphase_lifted 1 h1_mem
      refine ⟨traj₁, hv₁, hf₁, ?_⟩
      simp [hcard₁]
    | succ d' ih =>
      intro hd
      obtain ⟨T_prev, hv_prev, hf_prev, hcard_prev⟩ := ih (by omega)
      have hd1_bridge : d' + 1 ∈ Finset.Icc 1 (K_X - 2) :=
        Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hbr_reach := hBridge (d' + 1) hd1_bridge
      obtain ⟨T_br, hv_br, hf_br, hc_br⟩ :=
        lem59_exists_traj_of_rightRotReachable (2 * i_ℓ) (2 * i_ℓ) hbr_reach
      have hd2_mem : d' + 2 ∈ Finset.Icc 1 (K_X - 1) :=
        Finset.mem_Icc.mpr ⟨by omega, hd⟩
      obtain ⟨_, _, T_next, hv_next, hf_next, hcard_next⟩ := hphase_lifted (d' + 2) hd2_mem
      have hv_12 : ValidRightCascadeTraj (2 * i_ℓ) (2 * i_ℓ)
          (topEmbedPhase 1 (startT 1)) (T_prev ++ T_br) :=
        lem59_validTraj_append (2 * i_ℓ) (2 * i_ℓ) T_prev T_br _ hv_prev (hf_prev.symm ▸ hv_br)
      have hf_12 : (T_prev ++ T_br).foldl RightCascadeTrajStep.step (topEmbedPhase 1 (startT 1)) =
          topEmbedPhase (d' + 2) (startT (d' + 2)) := by
        rw [List.foldl_append, hf_prev]
        exact hf_br
      refine ⟨(T_prev ++ T_br) ++ T_next,
        lem59_validTraj_append (2 * i_ℓ) (2 * i_ℓ) (T_prev ++ T_br) T_next _ hv_12
          (hf_12.symm ▸ hv_next),
        by rw [List.foldl_append, hf_12, hf_next], ?_⟩
      rw [lem59_countCascadeBatches_append, lem59_countCascadeBatches_append, hc_br, Nat.add_zero]
      have hsum1 : (∑ p ∈ Finset.Icc 1 (d' + 2), (leadExitSet P proc chain ℓ_val X p).card) =
          (∑ p ∈ Finset.Icc 1 (d' + 1), (leadExitSet P proc chain ℓ_val X p).card) +
          (leadExitSet P proc chain ℓ_val X (d' + 2)).card := by
        have : d' + 2 = (d' + 1) + 1 := rfl
        rw [this, Finset.sum_Icc_succ_top (by omega)]
      have hsum2 : (∑ p ∈ Finset.Icc 1 (d' + 2), (U_witness p).card) =
          (∑ p ∈ Finset.Icc 1 (d' + 1), (U_witness p).card) + (U_witness (d' + 2)).card := by
        have : d' + 2 = (d' + 1) + 1 := rfl
        rw [this, Finset.sum_Icc_succ_top (by omega)]
      rw [hsum1, hsum2]
      nlinarith
  have hd_top : (K_X - 2) + 1 = K_X - 1 := by omega
  obtain ⟨T_block, hv_block, _, hcard_block⟩ := hind (K_X - 2) (by omega)
  rw [hd_top] at hcard_block
  have h1_mem : 1 ∈ Finset.Icc 1 (K_X - 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  obtain ⟨hGhat_bst, hGhat_keys, _⟩ := hphase_lifted 1 h1_mem
  have hGhat_nodes : (topEmbedPhase 1 (startT 1)).num_nodes = K_X - 1 := by
    rw [lem59_num_nodes_eq_card_keyFinset _ hGhat_bst, hGhat_keys, Nat.card_Icc]
    omega
  have hKX_ack : K_X - 1 ≤ ackermann i_ℓ 1 :=
    lem59_KX_sub_one_le_ack hAckPow hAckStep P r M T hValid ℓ X hX
  have hcasc_bound : (countCascadeBatches T_block : ℝ) ≤
      C_casc * (((2 * i_ℓ : ℕ) : ℝ) + 1) * ((K_X - 1 : ℕ) : ℝ) :=
    hCcasc.2 i_ℓ (2 * i_ℓ) (K_X - 1) (topEmbedPhase 1 (startT 1)) T_block
      (by omega) (by omega) hKX_ack hGhat_bst hGhat_nodes hv_block
  have hcasc_bound' : (countCascadeBatches T_block : ℝ) ≤
      C_casc * (2 * (i_ℓ : ℝ) + 1) * ((K_X - 1 : ℕ) : ℝ) := by
    push_cast at hcasc_bound
    exact hcasc_bound
  have hcard_R : ((∑ p ∈ Finset.Icc 1 (K_X - 1), (leadExitSet P proc chain ℓ_val X p).card : ℕ) : ℝ) ≤
      4 * (i_ℓ : ℝ) * (((K_X - 1 : ℕ) : ℝ) + (countCascadeBatches T_block : ℝ)) +
      8 * ((∑ p ∈ Finset.Icc 1 (K_X - 1), (U_witness p).card : ℕ) : ℝ) := by
    exact_mod_cast hcard_block
  have hi_nonneg : (0 : ℝ) ≤ 4 * (i_ℓ : ℝ) := by positivity
  nlinarith

private theorem lem59_list_sum_bound {α : Type} (xs : List α)
    (A B C : α → ℕ) (coeff : ℝ)
    (h : ∀ x ∈ xs, (A x : ℝ) ≤ coeff * (B x : ℝ) + 8 * (C x : ℝ)) :
    ((xs.map A).sum : ℝ) ≤ coeff * ((xs.map B).sum : ℝ) + 8 * ((xs.map C).sum : ℝ) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    have hx := h x List.mem_cons_self
    have hrest := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    linarith

private theorem lem59_compose_constants
    (C_casc : ℝ) (hCcasc_pos : 0 < C_casc)
    (P : ℕ) (hP : 1 ≤ P)
    (b3_card b3Intra_card b3Exit_card b3Post_card b3Act_card leadSum Aesc_card totalU : ℕ)
    (M : ℕ) (w i_scale sumKX : Fin M → ℕ)
    (hb3_split : b3_card = b3Intra_card + b3Exit_card)
    (hb3Exit_split : b3Exit_card ≤ b3Post_card + b3Act_card)
    (h54 : b3Intra_card < 7 * P)
    (h55 : b3Post_card < 2 * P)
    (h56_card : Aesc_card < 18 * P)
    (h56_bound : b3Act_card ≤ 2 * leadSum + Aesc_card)
    (h58_totalU : totalU < 20 * P)
    (hi_ge5 : ∀ ℓ : Fin M, 5 ≤ i_scale ℓ)
    (hw_pos : ∀ ℓ : Fin M, 1 ≤ w ℓ)
    (hKX_bound : ∀ ℓ : Fin M,
      (sumKX ℓ : ℝ) ≤ (P : ℝ) / ((w ℓ : ℝ) * (i_scale ℓ : ℝ) ^ 2))
    (h51_weights : (∑ ℓ : Fin M, (1 : ℝ) / (w ℓ : ℝ)) < (1 : ℝ) / 2)
    (hLeadPerScale : (leadSum : ℝ) ≤
      (∑ ℓ : Fin M,
        4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) * (sumKX ℓ : ℝ)) +
        8 * (totalU : ℝ)) :
    (b3Exit_card : ℝ) < (9 * C_casc + 341) * (P : ℝ) ∧
    (b3_card : ℝ) < (9 * C_casc + 348) * (P : ℝ) := by
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hTermBound : ∀ ℓ : Fin M,
      4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) * (sumKX ℓ : ℝ) ≤
        ((9 * C_casc + 1) * (P : ℝ)) * ((1 : ℝ) / (w ℓ : ℝ)) := by
    intro ℓ
    have hiR : (5 : ℝ) ≤ (i_scale ℓ : ℝ) := by exact_mod_cast hi_ge5 ℓ
    have hwR : (1 : ℝ) ≤ (w ℓ : ℝ) := by exact_mod_cast hw_pos ℓ
    have hcoeff_pos :
        0 ≤ 4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) := by positivity
    have hstep1 :
        4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) * (sumKX ℓ : ℝ) ≤
        4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) *
          ((P : ℝ) / ((w ℓ : ℝ) * (i_scale ℓ : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hKX_bound ℓ) hcoeff_pos
    have hi_sq :
        4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) ≤
          (9 * C_casc + 1) * (i_scale ℓ : ℝ) ^ 2 := by
      have h1 : 4 * (i_scale ℓ : ℝ) ≤ (i_scale ℓ : ℝ) ^ 2 := by nlinarith
      have h2 : (8 * (i_scale ℓ : ℝ) + 4) * (i_scale ℓ : ℝ) ≤ 9 * (i_scale ℓ : ℝ) ^ 2 := by
        nlinarith
      nlinarith
    have hstep2 :
        4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) *
          ((P : ℝ) / ((w ℓ : ℝ) * (i_scale ℓ : ℝ) ^ 2)) ≤
        ((9 * C_casc + 1) * (i_scale ℓ : ℝ) ^ 2) *
          ((P : ℝ) / ((w ℓ : ℝ) * (i_scale ℓ : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_right hi_sq
      positivity
    have hisq_ne : (i_scale ℓ : ℝ) ^ 2 ≠ 0 := by positivity
    have hw_ne : (w ℓ : ℝ) ≠ 0 := by positivity
    have hcancel :
        ((9 * C_casc + 1) * (i_scale ℓ : ℝ) ^ 2) *
          ((P : ℝ) / ((w ℓ : ℝ) * (i_scale ℓ : ℝ) ^ 2)) =
        ((9 * C_casc + 1) * (P : ℝ)) * ((1 : ℝ) / (w ℓ : ℝ)) := by
      field_simp
    linarith
  have hSumScales :
      (∑ ℓ : Fin M,
        4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) * (sumKX ℓ : ℝ)) ≤
        ((9 * C_casc + 1) * (P : ℝ)) * ((1 : ℝ) / 2) := by
    calc ∑ ℓ : Fin M,
          4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) * (sumKX ℓ : ℝ)
        ≤ ∑ ℓ : Fin M, ((9 * C_casc + 1) * (P : ℝ)) * ((1 : ℝ) / (w ℓ : ℝ)) :=
          Finset.sum_le_sum (fun ℓ _ => hTermBound ℓ)
      _ = ((9 * C_casc + 1) * (P : ℝ)) * (∑ ℓ : Fin M, (1 : ℝ) / (w ℓ : ℝ)) := by
          rw [← Finset.mul_sum]
      _ ≤ ((9 * C_casc + 1) * (P : ℝ)) * ((1 : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_left (le_of_lt h51_weights)
          positivity
  have hPostR : (b3Post_card : ℝ) < 2 * (P : ℝ) := by exact_mod_cast h55
  have hAescR : (Aesc_card : ℝ) < 18 * (P : ℝ) := by exact_mod_cast h56_card
  have hUR : (totalU : ℝ) < 20 * (P : ℝ) := by exact_mod_cast h58_totalU
  have hIntraR : (b3Intra_card : ℝ) < 7 * (P : ℝ) := by exact_mod_cast h54
  have hActR : (b3Act_card : ℝ) ≤ 2 * (leadSum : ℝ) + (Aesc_card : ℝ) := by exact_mod_cast h56_bound
  have hExitSplitR : (b3Exit_card : ℝ) ≤ (b3Post_card : ℝ) + (b3Act_card : ℝ) := by
    exact_mod_cast hb3Exit_split
  have hb3SplitR : (b3_card : ℝ) = (b3Intra_card : ℝ) + (b3Exit_card : ℝ) := by
    exact_mod_cast hb3_split
  have hExitBound : (b3Exit_card : ℝ) < (9 * C_casc + 341) * (P : ℝ) := by linarith
  exact ⟨hExitBound, by linarith⟩

private theorem lem_5_9_from_deps
    (h_A_1 :
      ((∀ i j : ℕ, 1 ≤ j → j < ackermann i j) ∧
       (∀ i j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → ackermann i j₁ < ackermann i j₂) ∧
       (∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
         ackermann (i - 1) j ≤ ackermann i j ∧ 2 ^ j ≤ ackermann i j) ∧
       (∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1) ∧
       (∀ m n : ℕ, 1 ≤ m → m ≤ n → alpha0 m ≤ alpha0 n) ∧
       alpha0 1 = 1 ∧
       (∀ n : ℕ, 2 ≤ n →
         alpha0 n ≤ Nat.clog 2 n ∧ (alpha0 n : ℝ) < Real.logb 2 (n : ℝ) + 1) ∧
       (∀ n : ℕ, 3 ≤ n → alpha0 n < n)) ∧
      ((∀ r k : ℕ, 1 ≤ k → 2 ^ k ≤ ackTower r k) ∧
       (∀ r k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → ackTower r k₁ < ackTower r k₂) ∧
       (∀ r₁ r₂ k : ℕ, 1 ≤ r₁ → r₁ ≤ r₂ → 1 ≤ k → ackTower r₁ k ≤ ackTower r₂ k) ∧
       (∀ r m n : ℕ, 1 ≤ r → 1 ≤ m → m ≤ n → alphaHierarchy r m ≤ alphaHierarchy r n) ∧
       (∀ r n : ℕ, 1 ≤ r → 4 < n → alphaHierarchy r n < n) ∧
       (∀ r k n : ℕ, 1 ≤ r → 1 ≤ k → 1 ≤ n →
         (alphaHierarchy r n ≤ k ↔ n ≤ ackTower r k)) ∧
       (∀ n : ℕ, 1 ≤ n → alphaHierarchy 1 (2 * n) ≤ alphaHierarchy 1 n + 1) ∧
       (∀ r n : ℕ, 1 ≤ r → 1 ≤ n →
         alphaHierarchy r n ≤ alphaHierarchy 1 n ∧
         alphaHierarchy 1 n ≤ Nat.log 2 (Nat.log 2 (n + 16)) + 2 ∧
         (alphaHierarchy 1 n : ℝ) ≤ Real.logb 2 (Real.logb 2 ((n : ℝ) + 16)) + 2) ∧
       (∀ n : ℕ, 1 ≤ n → alphaOmega n = sInf {r : ℕ | 1 ≤ r ∧ n ≤ ackTower r 2})) ∧
      ((∀ n : ℕ, 1 ≤ n → alpha0 (n + 2) ≤ alpha0 n + 1) ∧
       (∀ m u : ℕ, 1 ≤ m → 1 ≤ u →
         ((fun x : ℕ => alpha0 x + 1)^[m] u) ≤ (alpha0^[m] u) + 2) ∧
       (∀ u : ℕ, 5 ≤ u → alpha0 (2 ^ 20 * u ^ 6) ≤ alpha0 u + 1)))
    (h_4_1 : ∀ (n : ℕ), 1 ≤ n → ∀ (t₁ t₂ : BinaryTree ℕ),
      t₁.IsBST → t₂.IsBST →
      keyFinset t₁ = Finset.Icc 1 n → keyFinset t₂ = Finset.Icc 1 n →
      (RightRotReachable t₁ t₂ ↔ ∀ v ∈ Finset.Icc 1 n, rightReach t₁ v ≤ rightReach t₂ v))
    (h_5_1 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      let chain := scaleTreePartitionChain T P M
      (∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T ℓ : ℝ)) < (1 : ℝ) / 2 ∧
      (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) < 2 ∧
      (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50)
    (h_5_4 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        let chain := scaleTreePartitionChain T P M
        (b3Intra P proc chain).card ≤ 2 * P + proc.kRot + (eEnter P T proc chain).card ∧
        ((b3Intra P proc chain).card : ℝ) < (151 : ℝ) / 25 * (P : ℝ) ∧
        (b3Intra P proc chain).card < 7 * P)
    (h_5_5 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        let chain := scaleTreePartitionChain T P M
        (b3ExitPost P proc chain).card ≤ proc.kL ∧ proc.kL < 2 * P)
    (h_5_6 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        let chain := scaleTreePartitionChain T P M
        let leadSum := ∑ ℓ : Fin M,
          ((chain ℓ.castSucc).map (fun X =>
            let subs := childSubblocks (chain ℓ.succ) X
            ∑ p ∈ Finset.Icc 1 (subs.length - 1),
              (leadExitSet P proc chain (ℓ.val + 1) X p).card)).sum
        ∃ A_esc : Finset InternalPopRot,
          A_esc ⊆ b3ExitAct P proc chain ∧
          A_esc.card < 18 * P ∧
          (b3ExitAct P proc chain).card ≤ 2 * leadSum + A_esc.card)
    (h_5_7 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P) (ℓ : Fin M) (X : IntervalBlock),
        X ∈ scaleTreePartitionChain T P M ℓ.castSucc →
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
              topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G))))
    (h_5_8 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        let chain := scaleTreePartitionChain T P M
        (∀ (ℓ : Fin M) (X : IntervalBlock), X ∈ chain ℓ.castSucc →
          let ℓ_val := ℓ.val + 1
          let subs := childSubblocks (chain ℓ.succ) X
          ∀ p ∈ Finset.Icc 1 (subs.length - 1),
            let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
            let G_end := phaseSummaryBST P proc chain ℓ_val X p (tauEmpty proc (subblock1 subs p))
            let pi0 := leftSpine G₀
            let Fp := promotedSubblockIndices P proc chain ℓ_val X p
            1 ≤ pi0.length ∧
            (∀ c ∈ Fp, c ∈ pi0.dropLast) ∧
            (∀ a b : ℕ, a ≤ b → b + 1 < pi0.length →
              (∀ t : ℕ, a ≤ t → t ≤ b → (pi0[t]?).getD 0 ∈ Fp) →
              (a = 0 ∨ (pi0[a - 1]?).getD 0 ∉ Fp) →
              (pi0[b + 1]?).getD 0 ∉ Fp →
              (∀ t : ℕ, a ≤ t → t < b →
                leadPopKey P proc chain ℓ_val X p ((pi0[t + 1]?).getD 0) <
                  leadPopKey P proc chain ℓ_val X p ((pi0[t]?).getD 0)) ∧
              (∀ t : ℕ, a ≤ t → t ≤ b →
                rightReach G₀ ((pi0[b + 1]?).getD 0) ≤ rightReach G_end ((pi0[t]?).getD 0)))) ∧
        (∃ U_witness : Fin M → IntervalBlock → ℕ → Finset ℕ,
          (∀ (ℓ : Fin M) (X : IntervalBlock), X ∈ chain ℓ.castSucc →
            let ℓ_val := ℓ.val + 1
            let subs := childSubblocks (chain ℓ.succ) X
            ∀ p ∈ Finset.Icc 1 (subs.length - 1),
              let G₀ := phaseSummaryBST P proc chain ℓ_val X p (proc.popStepIdx (subblock1 subs p).lo)
              let pi0 := leftSpine G₀
              let Fp := promotedSubblockIndices P proc chain ℓ_val X p
              U_witness ℓ X p ⊆ pi0.toFinset \ Fp ∧
              ∀ a b : ℕ, a < b → b < pi0.length →
                (pi0[a]?).getD 0 ∈ Fp → (pi0[b]?).getD 0 ∈ Fp →
                (∀ t : ℕ, a < t → t < b → (pi0[t]?).getD 0 ∉ Fp) →
                scaleI T P ℓ_val < b - a - 1 →
                let g := b - a - 1
                let gapSet := (Finset.Ioo a b).image (fun t => (pi0[t]?).getD 0)
                g - 3 ≤ (U_witness ℓ X p ∩ gapSet).card ∧
                scaleI T P ℓ_val < 2 * (g - 3)) ∧
          (let totalU := ∑ ℓ : Fin M,
             ((chain ℓ.castSucc).map (fun X =>
               let subs := childSubblocks (chain ℓ.succ) X
               ∑ p ∈ Finset.Icc 1 (subs.length - 1), (U_witness ℓ X p).card)).sum
           totalU ≤ 2 * (b3Intra P proc chain).card + (s1Set P T proc chain).card +
                      (bLeafPre P proc chain).card + 2 * proc.kL + P ∧
           totalU < 20 * P)))
    (C_casc : ℝ) (hCcasc : IsCascadeBoundConst C_casc)
    (P r M : ℕ) (T : ScaleTree) (hValid : ValidScaleTree P r M T)
    (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (b3 P proc chain).card = (b3Intra P proc chain).card + (b3Exit P proc chain).card ∧
    ((b3Exit P proc chain).card : ℝ) < (9 * C_casc + 341) * (P : ℝ) ∧
    ((b3 P proc chain).card : ℝ) < (9 * C_casc + 348) * (P : ℝ) := by
  intro chain
  have hb3_split : (b3 P proc chain).card =
      (b3Intra P proc chain).card + (b3Exit P proc chain).card :=
    lem59_b3_card_split P proc chain
  have hb3Exit_split : (b3Exit P proc chain).card ≤
      (b3ExitPost P proc chain).card + (b3ExitAct P proc chain).card :=
    lem59_b3Exit_card_split P proc chain
  have hAckStep := h_A_1.1.2.2.1
  have hAckPow := h_A_1.1.2.2.2.1
  have h54 := (h_5_4 P r M T hValid proc).2.2
  have h55_raw := h_5_5 P r M T hValid proc
  have h55 : (b3ExitPost P proc chain).card < 2 * P := lt_of_le_of_lt h55_raw.1 h55_raw.2
  obtain ⟨A_esc, _, hAesc_card, hAct_bound⟩ := h_5_6 P r M T hValid proc
  obtain ⟨h58_part1, U_witness, h58_part2, _, htotalU_lt⟩ := h_5_8 P r M T hValid proc
  set leadSum := ∑ ℓ : Fin M,
    ((chain ℓ.castSucc).map (fun X =>
      let subs := childSubblocks (chain ℓ.succ) X
      ∑ p ∈ Finset.Icc 1 (subs.length - 1),
        (leadExitSet P proc chain (ℓ.val + 1) X p).card)).sum
  set totalU := ∑ ℓ : Fin M,
    ((chain ℓ.castSucc).map (fun X =>
      let subs := childSubblocks (chain ℓ.succ) X
      ∑ p ∈ Finset.Icc 1 (subs.length - 1), (U_witness ℓ X p).card)).sum
  let w : Fin M → ℕ := fun ℓ => leafWeight T (ℓ.val + 1)
  let i_scale : Fin M → ℕ := fun ℓ => scaleI T P (ℓ.val + 1)
  let sumKX : Fin M → ℕ := fun ℓ =>
    ((chain ℓ.castSucc).map (fun X => (childSubblocks (chain ℓ.succ) X).length - 1)).sum
  have hi_ge5 : ∀ ℓ : Fin M, 5 ≤ i_scale ℓ :=
    fun ℓ => lem59_scaleI_ge_five hAckPow P r M T hValid ℓ
  have hw_pos : ∀ ℓ : Fin M, 1 ≤ w ℓ := fun ℓ => by
    dsimp only [w]
    have := lem59_leafWeight_ge_four P r M T hValid (ℓ.val + 1) (by omega) (by omega)
    omega
  have hKX_bound : ∀ ℓ : Fin M,
      (sumKX ℓ : ℝ) ≤ (P : ℝ) / ((w ℓ : ℝ) * (i_scale ℓ : ℝ) ^ 2) :=
    fun ℓ => lem59_sumKX_bound P r M T hValid ℓ
  have h51_weights : (∑ ℓ : Fin M, (1 : ℝ) / (w ℓ : ℝ)) < (1 : ℝ) / 2 := by
    rw [lem59_reindex_weights M T]
    exact (h_5_1 P r M T hValid).1
  have hLeadPerScale : (leadSum : ℝ) ≤
      (∑ ℓ : Fin M,
        4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) * (sumKX ℓ : ℝ)) +
        8 * (totalU : ℝ) := by
    have hper_ℓ : ∀ ℓ : Fin M,
        (((chain ℓ.castSucc).map (fun X =>
          let subs := childSubblocks (chain ℓ.succ) X
          ∑ p ∈ Finset.Icc 1 (subs.length - 1),
            (leadExitSet P proc chain (ℓ.val + 1) X p).card)).sum : ℝ) ≤
        4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) * (sumKX ℓ : ℝ) +
        8 * (((chain ℓ.castSucc).map (fun X =>
          let subs := childSubblocks (chain ℓ.succ) X
          ∑ p ∈ Finset.Icc 1 (subs.length - 1), (U_witness ℓ X p).card)).sum : ℝ) := by
      intro ℓ
      apply lem59_list_sum_bound (chain ℓ.castSucc)
        (fun X => ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
          (leadExitSet P proc chain (ℓ.val + 1) X p).card)
        (fun X => (childSubblocks (chain ℓ.succ) X).length - 1)
        (fun X => ∑ p ∈ Finset.Icc 1 ((childSubblocks (chain ℓ.succ) X).length - 1),
          (U_witness ℓ X p).card)
        (4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)))
      intro X hX
      exact lem59_block_concat C_casc hCcasc hAckPow hAckStep h_4_1 P r M T hValid proc ℓ X hX
        (U_witness ℓ X) (h_5_7 P r M T hValid proc ℓ X hX)
        (h58_part1 ℓ X hX) (h58_part2 ℓ X hX)
    calc (leadSum : ℝ)
        = ∑ ℓ : Fin M, (((chain ℓ.castSucc).map (fun X =>
            let subs := childSubblocks (chain ℓ.succ) X
            ∑ p ∈ Finset.Icc 1 (subs.length - 1),
              (leadExitSet P proc chain (ℓ.val + 1) X p).card)).sum : ℝ) := by
          dsimp [leadSum]; push_cast; rfl
      _ ≤ ∑ ℓ : Fin M,
          (4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) * (sumKX ℓ : ℝ) +
           8 * (((chain ℓ.castSucc).map (fun X =>
             let subs := childSubblocks (chain ℓ.succ) X
             ∑ p ∈ Finset.Icc 1 (subs.length - 1), (U_witness ℓ X p).card)).sum : ℝ)) :=
          Finset.sum_le_sum (fun ℓ _ => hper_ℓ ℓ)
      _ = (∑ ℓ : Fin M,
            4 * (i_scale ℓ : ℝ) * (1 + C_casc * (2 * (i_scale ℓ : ℝ) + 1)) * (sumKX ℓ : ℝ)) +
          8 * (totalU : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          dsimp [totalU]; push_cast; rfl
  obtain ⟨hExit_lt, hb3_lt⟩ := lem59_compose_constants
    C_casc hCcasc.1 P hValid.1
    (b3 P proc chain).card (b3Intra P proc chain).card (b3Exit P proc chain).card
    (b3ExitPost P proc chain).card (b3ExitAct P proc chain).card
    leadSum A_esc.card totalU
    M w i_scale sumKX
    hb3_split hb3Exit_split h54 h55 hAesc_card hAct_bound htotalU_lt
    hi_ge5 hw_pos hKX_bound h51_weights hLeadPerScale
  exact ⟨hb3_split, hExit_lt, hb3_lt⟩

end PhaseAndMainProof

/-- **Lemma 5.9** (`lem:bucket-b3-exit`, Height-Independent Bound on `ℬ_{3,exit}` and `ℬ_3`):
For any constant `C_casc > 0` satisfying Theorem 2.3 (`IsCascadeBoundConst C_casc`),
`|ℬ_{3,exit}| < (9 C_casc + 341) P` and `|ℬ_3| = |ℬ_{3,intra}| + |ℬ_{3,exit}| < (9 C_casc + 348) P`
uniformly across all `r, M, 𝒯`. -/
public theorem lem_5_9_bucket_b3_exit
    (h_lem_A_1 :
      ((∀ i j : ℕ, 1 ≤ j → j < ackermann i j) ∧
       (∀ i j₁ j₂ : ℕ, 1 ≤ j₁ → j₁ < j₂ → ackermann i j₁ < ackermann i j₂) ∧
       (∀ i j : ℕ, 1 ≤ i → 1 ≤ j →
         ackermann (i - 1) j ≤ ackermann i j ∧ 2 ^ j ≤ ackermann i j) ∧
       (∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1) ∧
       (∀ m n : ℕ, 1 ≤ m → m ≤ n → alpha0 m ≤ alpha0 n) ∧
       alpha0 1 = 1 ∧
       (∀ n : ℕ, 2 ≤ n →
         alpha0 n ≤ Nat.clog 2 n ∧ (alpha0 n : ℝ) < Real.logb 2 (n : ℝ) + 1) ∧
       (∀ n : ℕ, 3 ≤ n → alpha0 n < n)) ∧
      ((∀ r k : ℕ, 1 ≤ k → 2 ^ k ≤ ackTower r k) ∧
       (∀ r k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → ackTower r k₁ < ackTower r k₂) ∧
       (∀ r₁ r₂ k : ℕ, 1 ≤ r₁ → r₁ ≤ r₂ → 1 ≤ k → ackTower r₁ k ≤ ackTower r₂ k) ∧
       (∀ r m n : ℕ, 1 ≤ r → 1 ≤ m → m ≤ n → alphaHierarchy r m ≤ alphaHierarchy r n) ∧
       (∀ r n : ℕ, 1 ≤ r → 4 < n → alphaHierarchy r n < n) ∧
       (∀ r k n : ℕ, 1 ≤ r → 1 ≤ k → 1 ≤ n →
         (alphaHierarchy r n ≤ k ↔ n ≤ ackTower r k)) ∧
       (∀ n : ℕ, 1 ≤ n → alphaHierarchy 1 (2 * n) ≤ alphaHierarchy 1 n + 1) ∧
       (∀ r n : ℕ, 1 ≤ r → 1 ≤ n →
         alphaHierarchy r n ≤ alphaHierarchy 1 n ∧
         alphaHierarchy 1 n ≤ Nat.log 2 (Nat.log 2 (n + 16)) + 2 ∧
         (alphaHierarchy 1 n : ℝ) ≤ Real.logb 2 (Real.logb 2 ((n : ℝ) + 16)) + 2) ∧
       (∀ n : ℕ, 1 ≤ n → alphaOmega n = sInf {r : ℕ | 1 ≤ r ∧ n ≤ ackTower r 2})) ∧
      ((∀ n : ℕ, 1 ≤ n → alpha0 (n + 2) ≤ alpha0 n + 1) ∧
       (∀ m u : ℕ, 1 ≤ m → 1 ≤ u →
         ((fun x : ℕ => alpha0 x + 1)^[m] u) ≤ (alpha0^[m] u) + 2) ∧
       (∀ u : ℕ, 5 ≤ u → alpha0 (2 ^ 20 * u ^ 6) ≤ alpha0 u + 1)))
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
    (h_lem_4_1 : ∀ (n : ℕ), 1 ≤ n → ∀ (t₁ t₂ : BinaryTree ℕ),
      t₁.IsBST → t₂.IsBST →
      keyFinset t₁ = Finset.Icc 1 n → keyFinset t₂ = Finset.Icc 1 n →
      (RightRotReachable t₁ t₂ ↔ ∀ v ∈ Finset.Icc 1 n, rightReach t₁ v ≤ rightReach t₂ v))
    (h_lem_5_1 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      let chain := scaleTreePartitionChain T P M
      (∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T ℓ : ℝ)) < (1 : ℝ) / 2 ∧
      (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) < 2 ∧
      (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50)
    (h_lem_5_2 : ∀ {M : ℕ} (P : ℕ), 1 ≤ P → 1 ≤ M →
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
            2 * P + (leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum)
    (h_lem_5_3 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
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
        (ee.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ))
    (h_lem_5_4 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        let chain := scaleTreePartitionChain T P M
        (b3Intra P proc chain).card ≤ 2 * P + proc.kRot + (eEnter P T proc chain).card ∧
        ((b3Intra P proc chain).card : ℝ) < (151 : ℝ) / 25 * (P : ℝ) ∧
        (b3Intra P proc chain).card < 7 * P)
    (h_lem_5_5 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        let chain := scaleTreePartitionChain T P M
        (b3ExitPost P proc chain).card ≤ proc.kL ∧ proc.kL < 2 * P)
    (h_lem_5_6 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P),
        let chain := scaleTreePartitionChain T P M
        let leadSum := ∑ ℓ : Fin M,
          ((chain ℓ.castSucc).map (fun X =>
            let subs := childSubblocks (chain ℓ.succ) X
            ∑ p ∈ Finset.Icc 1 (subs.length - 1),
              (leadExitSet P proc chain (ℓ.val + 1) X p).card)).sum
        ∃ A_esc : Finset InternalPopRot,
          A_esc ⊆ b3ExitAct P proc chain ∧
          A_esc.card < 18 * P ∧
          (b3ExitAct P proc chain).card ≤ 2 * leadSum + A_esc.card)
    (h_lem_5_7 : ∀ (P r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
      ∀ (proc : FoldedPopProcess P) (ℓ : Fin M) (X : IntervalBlock),
        X ∈ scaleTreePartitionChain T P M ℓ.castSucc →
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
              topEmbedPhase p (traj.foldl RightCascadeTrajStep.step G))))
    (C_casc : ℝ) (hCcasc : IsCascadeBoundConst C_casc)
    (P r M : ℕ) (T : ScaleTree) (hValid : ValidScaleTree P r M T)
    (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (b3 P proc chain).card = (b3Intra P proc chain).card + (b3Exit P proc chain).card ∧
    ((b3Exit P proc chain).card : ℝ) < (9 * C_casc + 341) * (P : ℝ) ∧
    ((b3 P proc chain).card : ℝ) < (9 * C_casc + 348) * (P : ℝ) :=
  lem_5_9_from_deps h_lem_A_1 h_lem_4_1 h_lem_5_1 h_lem_5_4 h_lem_5_5 h_lem_5_6 h_lem_5_7
    (lem_5_8_b3_gaps h_lem_3_1 h_lem_3_6 h_lem_5_2 h_lem_5_3 h_lem_5_4 h_lem_5_7)
    C_casc hCcasc P r M T hValid proc

end Solution.BucketB3GapsExit

end
