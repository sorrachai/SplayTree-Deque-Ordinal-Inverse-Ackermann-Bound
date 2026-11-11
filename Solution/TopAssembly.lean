module

public import Challenge.Definitions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Layer 5: Top-Level Assembly (`thm_1_4_main` and `deque_ordinal_omega_ackermann_bound`)

This module assembles:
1. **Theorem 1.4** (`thm_1_4_main`, deletion-sensitive splay-tree deque bound) from
   Theorem 2.2 (`thm_2_2_mod1_reduction`), Theorem 2.5 (`thm_2_5_mod3_pass`),
   Theorem 2.6 (`thm_2_6_mod4_contraction`), and Lemma A.1 (`lem_A_1_ack_basic`).
2. **Main Challenge Target** (`deque_ordinal_omega_ackermann_bound`) from
   Theorem 1.4 (`thm_1_4_main`), Proposition 1.3 (`prop_1_3_omega_properties`), and
   Lemma A.1 (`lem_A_1_ack_basic`).
-/

@[expose] public section

namespace Solution.TopAssembly

open SplayTree

/-! ## Exact Upstream Dependency Statement Types -/

/-- Statement type of `lem_A_1_ack_basic` (`Challenge.lean` L71–101). -/
abbrev Ty_lem_A_1 : Prop :=
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
   (∀ u : ℕ, 5 ≤ u → alpha0 (2 ^ 20 * u ^ 6) ≤ alpha0 u + 1))

/-- Statement type of `prop_1_3_omega_properties` (`Challenge.lean` L41–51). -/
abbrev Ty_prop_1_3 : Prop :=
  (∀ m n : ℕ, 1 ≤ m → m ≤ n → alphaOmega m ≤ alphaOmega n) ∧
  (ackermann 4 1 = ackermann 2 16 ∧ 2 ^ 65536 < ackermann 2 16 ∧
    ∀ n : ℕ, 1 ≤ n → n ≤ ackermann 4 1 → alphaOmega n = 1) ∧
  (∀ M : ℕ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → M ≤ alphaOmega n) ∧
  (∀ r : ℕ, 1 ≤ r →
    (∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 2 ^ alphaOmega n < alphaHierarchy r n) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (alphaOmega n : ℝ) ≤ ε * (alphaHierarchy r n : ℝ))) ∧
  (∀ n : ℕ, 1 ≤ n →
    alphaOmegaDiag n ≤ alphaOmega n + 1 ∧ alphaOmega n ≤ alphaOmegaDiag n + 2)

/-- Statement type of `thm_2_2_mod1_reduction` (`Challenge.lean` L126–133). -/
abbrev Ty_thm_2_2 : Prop :=
  ∃ C_red : ℝ, 0 < C_red ∧
    ∀ {α : Type} [LinearOrder α] (n m : ℕ) (init : BST α) (ops : Fin m → DequeOp α),
      init.tree.num_nodes = n →
      ValidDequeSeq init.tree ops →
      ∃ (HL : FoldedPopProcess (popCount ops)) (HR : FoldedPopProcess (ejectCount ops)),
        dequeSequenceCost init.tree ops ≤
          2 * (HL.J : ℝ) + 2 * (HR.J : ℝ) + C_red * ((n : ℝ) + (m : ℝ))

/-- Statement type of `thm_2_5_mod3_pass` (`Challenge.lean` L438–451). -/
abbrev Ty_thm_2_5 : Prop :=
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
      proc.J ≤ P * (Nat.clog 2 P - 1)

/-- Statement type of `thm_2_6_mod4_contraction` (`Challenge.lean` L700–715). -/
abbrev Ty_thm_2_6 : Prop :=
  ∃ C₀ : ℕ, 6 ≤ C₀ ∧
    ∀ P r : ℕ, 1 ≤ P → 1 ≤ r →
      let bound := (max (alphaHierarchy r P) (2 ^ (C₀ ^ (2 * r)))) ^ (6 ^ r)
      (2 * P < bound ∨
        ∃ (M : ℕ) (T : ScaleTree), ValidScaleTree P r M T ∧ 2 * scaleS T P M ≤ bound) ∧
      (r = alphaOmega P →
        P < 2 ^ (C₀ ^ (3 * r)) ∨
        ∃ (M : ℕ) (T : ScaleTree), ValidScaleTree P r M T ∧
          ∀ Q ∈ scaleTreePartitionChain T P M (Fin.last M),
            Q.size < 2 ^ (C₀ ^ (3 * r))) ∧
      (r = 1 →
        2 * P < (max (alphaHierarchy 1 P) (2 ^ (C₀ ^ 2))) ^ 6 ∨
        ∃ (M : ℕ) (T : ScaleTree), ValidScaleTree P 1 M T ∧
          ∀ Q ∈ scaleTreePartitionChain T P M (Fin.last M),
            Q.size < (max (alphaHierarchy 1 P) (2 ^ (C₀ ^ 2))) ^ 6)

/-! ## Elementary & Hierarchy Bridge Lemmas -/

/-- `popCount ops + ejectCount ops ≤ m` for any `m`-operation deque sequence `ops`. -/
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

/-- Any `FoldedPopProcess 0` has `J = 0`. -/
theorem foldedPopProcess_zero_J (proc : FoldedPopProcess 0) : proc.J = 0 := by
  rcases proc.hKLBound with ⟨_, hsteps⟩ | ⟨h1, _⟩
  · simp [FoldedPopProcess.J, FoldedPopProcess.rInt, hsteps, collectFoldedPopRots]
  · omega

/-- Real-cast linearity of `List.sum` on `List ℕ`. -/
private theorem cast_list_sum (xs : List ℕ) :
    ((xs.sum : ℕ) : ℝ) = (xs.map (fun k : ℕ => (k : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Elementary inequality `c ^ 3 ≤ 2 ^ (c ^ 2)` for all `c ≥ 6`. -/
private theorem cube_le_two_pow_sq (c : ℕ) (hc : 6 ≤ c) : c ^ 3 ≤ 2 ^ (c ^ 2) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  clear hc
  induction d with
  | zero => decide
  | succ d ih =>
    set x := 6 + d
    have hx6 : 6 ≤ x := by omega
    have hcube : (x + 1) ^ 3 ≤ 2 * x ^ 3 := by
      have hx3 : 6 * x ^ 2 ≤ x ^ 3 := by
        calc 6 * x ^ 2 ≤ x * x ^ 2 := Nat.mul_le_mul_right (x ^ 2) hx6
          _ = x ^ 3 := by ring
      nlinarith
    have hsq : x ^ 2 + 1 ≤ (x + 1) ^ 2 := by nlinarith
    calc (x + 1) ^ 3 ≤ 2 * x ^ 3 := hcube
      _ ≤ 2 * 2 ^ (x ^ 2) := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (x ^ 2 + 1) := by ring
      _ ≤ 2 ^ ((x + 1) ^ 2) := Nat.pow_le_pow_right (by omega) hsq

/-- Threshold tower `G_r(k)` for `iteratedInvAckermannHierarchy`. -/
private def pettieTower : ℕ → ℕ → ℕ
  | 0, k => ackTower 0 k
  | _ + 1, 0 => 1
  | r + 1, k + 1 => (pettieTower r)^[k + 1] 2

/-- Bridge between the paper's `alphaOmega` and `ordinalOmegaInvAckermann`:
for every `n ≥ 1`, `1 ≤ ordinalOmegaInvAckermann n` and
`alphaOmega n ≤ ordinalOmegaInvAckermann n + 2`. -/
theorem bridge_alphaOmega_ordinalOmega (hA : Ty_lem_A_1) :
    ∀ n : ℕ, 1 ≤ n →
      1 ≤ ordinalOmegaInvAckermann n ∧ alphaOmega n ≤ ordinalOmegaInvAckermann n + 2 := by
  rcases hA with ⟨⟨_, _, _, hAckPow, _, _, _, _⟩,
    ⟨hTowerPow, hTowerStrict, _, _, _, _, _, _, hAlphaOmegaSInf⟩, _⟩
  have hTowerMono : ∀ r k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ ≤ k₂ → ackTower r k₁ ≤ ackTower r k₂ := by
    intro r k₁ k₂ hk1 hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (hTowerStrict r k₁ k₂ hk1 hlt)
  have hTowerGe2 : ∀ r k : ℕ, 1 ≤ k → 2 ≤ ackTower r k := by
    intro r k hk
    exact le_trans (by have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk; omega) (hTowerPow r k hk)
  have hPettieProp : ∀ r : ℕ,
      (∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ pettieTower r k) ∧
      (∀ k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ ≤ k₂ → pettieTower r k₁ ≤ pettieTower r k₂) ∧
      (∀ n : ℕ, 1 ≤ n → 1 ≤ iteratedInvAckermannHierarchy r n) ∧
      (∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
        (iteratedInvAckermannHierarchy r n ≤ k ↔ n ≤ pettieTower r k)) := by
    intro r
    induction r with
    | zero =>
      have h0_pow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ pettieTower 0 k := fun k hk => hTowerPow 0 k hk
      have h0_mono : ∀ k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ ≤ k₂ → pettieTower 0 k₁ ≤ pettieTower 0 k₂ :=
        fun k₁ k₂ hk1 hle => hTowerMono 0 k₁ k₂ hk1 hle
      have h0_nonempty : ∀ n : ℕ, 1 ≤ n → ({k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}).Nonempty := by
        intro n hn
        exact ⟨n, hn, le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (hAckPow n hn)⟩
      have h0_pos : ∀ n : ℕ, 1 ≤ n → 1 ≤ iteratedInvAckermannHierarchy 0 n := by
        intro n hn
        exact le_csInf (h0_nonempty n hn) (fun k hk => hk.1)
      refine ⟨h0_pow, h0_mono, h0_pos, ?_⟩
      intro n k hn hk
      cases k with
      | zero => omega
      | succ k' =>
        simp only [iteratedInvAckermannHierarchy, pettieTower, ackTower, invAckermann]
        constructor
        · intro hle
          have hmem := Nat.sInf_mem (h0_nonempty n hn)
          have hmono_ack : ∀ a b : ℕ, 1 ≤ a → a ≤ b → ackermann a 1 ≤ ackermann b 1 := by
            intro a b ha hab
            have h := hTowerMono 0 a b ha hab
            cases a with
            | zero => omega
            | succ a' =>
              cases b with
              | zero => omega
              | succ b' => simpa [ackTower] using h
          exact le_trans hmem.2 (hmono_ack _ _ hmem.1 hle)
        · intro hnk
          exact Nat.sInf_le ⟨by omega, hnk⟩
    | succ r ih =>
      rcases ih with ⟨hr_pow, hr_mono, hr_pos, hr_iff⟩
      have hr_ge2 : ∀ k : ℕ, 1 ≤ k → 2 ≤ pettieTower r k := by
        intro k hk
        exact le_trans (by have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk; omega) (hr_pow k hk)
      have h_iter_pos : ∀ i n : ℕ, 1 ≤ n → 1 ≤ ((iteratedInvAckermannHierarchy r)^[i] n) := by
        intro i; induction i with
        | zero => intro n hn; exact hn
        | succ i ihi => intro n hn; rw [Function.iterate_succ_apply]; exact ihi _ (hr_pos n hn)
      have h_iter_ge2 : ∀ i t : ℕ, 1 ≤ t → 2 ≤ ((pettieTower r)^[i + 1] t) := by
        intro i; induction i with
        | zero => intro t ht; exact hr_ge2 t ht
        | succ i ihi =>
          intro t ht; rw [Function.iterate_succ_apply']
          exact hr_ge2 _ (by have := ihi t ht; omega)
      have h_iter_mono : ∀ i a b : ℕ, 1 ≤ a → a ≤ b →
          ((pettieTower r)^[i] a) ≤ ((pettieTower r)^[i] b) := by
        intro i; induction i with
        | zero => intro a b _ hab; exact hab
        | succ i ihi =>
          intro a b ha hab; rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          exact ihi _ _ (by have := hr_ge2 a ha; omega) (hr_mono a b ha hab)
      have h_iter_iff : ∀ i n t : ℕ, 1 ≤ i → 1 ≤ n → 1 ≤ t →
          (((iteratedInvAckermannHierarchy r)^[i] n) ≤ t ↔ n ≤ ((pettieTower r)^[i] t)) := by
        intro i; induction i with
        | zero => intro n t hi; omega
        | succ i ihi =>
          cases i with
          | zero => intro n t _ hn ht; exact hr_iff n t hn ht
          | succ i' =>
            intro n t _ hn ht
            rw [Function.iterate_succ_apply (iteratedInvAckermannHierarchy r) (i' + 1) n]
            rw [ihi (iteratedInvAckermannHierarchy r n) t (by omega) (hr_pos n hn) ht]
            rw [Function.iterate_succ_apply' (pettieTower r) (i' + 1) t]
            exact hr_iff n _ hn (by have := h_iter_ge2 i' t ht; omega)
      have h_succ_pow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ pettieTower (r + 1) k := by
        intro k hk
        cases k with
        | zero => omega
        | succ k' =>
          clear hk
          induction k' with
          | zero =>
            change 2 ≤ pettieTower r 2
            exact hr_ge2 2 (by omega)
          | succ m ihm =>
            have hstep : pettieTower (r + 1) (m + 2) = pettieTower r (pettieTower (r + 1) (m + 1)) := by
              simp [pettieTower, Function.iterate_succ_apply']
            rw [hstep]
            have h1 : 1 ≤ pettieTower (r + 1) (m + 1) := by
              have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
              omega
            have hp := hr_pow (pettieTower (r + 1) (m + 1)) h1
            have hexp : m + 2 ≤ pettieTower (r + 1) (m + 1) := by
              have hlt : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
              omega
            exact le_trans (Nat.pow_le_pow_right (by omega) hexp) hp
      have h_succ_mono : ∀ k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ ≤ k₂ →
          pettieTower (r + 1) k₁ ≤ pettieTower (r + 1) k₂ := by
        intro k₁ k₂ hk1 hle
        have hstep : ∀ m : ℕ, pettieTower (r + 1) (m + 1) ≤ pettieTower (r + 1) (m + 2) := by
          intro m
          simp only [pettieTower]
          rw [Function.iterate_succ_apply (pettieTower r) (m + 1) 2]
          exact h_iter_mono (m + 1) 2 (pettieTower r 2) (by omega) (hr_ge2 2 (by omega))
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
        clear hle
        induction d with
        | zero => exact le_rfl
        | succ d ihd =>
          cases k₁ with
          | zero => omega
          | succ k₁' =>
            have heq1 : k₁' + 1 + d = k₁' + d + 1 := by omega
            have heq2 : k₁' + 1 + (d + 1) = k₁' + d + 2 := by omega
            rw [heq2]
            rw [heq1] at ihd
            exact le_trans ihd (hstep (k₁' + d))
      have h_nonempty : ∀ n : ℕ, 1 ≤ n →
          ({i : ℕ | 1 ≤ i ∧ ((iteratedInvAckermannHierarchy r)^[i] n) ≤ 2}).Nonempty := by
        intro n hn
        refine ⟨n, hn, ?_⟩
        rw [h_iter_iff n n 2 hn hn (by omega)]
        cases n with
        | zero => omega
        | succ n' =>
          simpa [pettieTower] using
            le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (h_succ_pow (n' + 1) (by omega))
      have h_succ_pos : ∀ n : ℕ, 1 ≤ n → 1 ≤ iteratedInvAckermannHierarchy (r + 1) n := by
        intro n hn
        exact le_csInf (h_nonempty n hn) (fun i hi => hi.1)
      refine ⟨h_succ_pow, h_succ_mono, h_succ_pos, ?_⟩
      intro n k hn hk
      change sInf {i : ℕ | 1 ≤ i ∧ ((iteratedInvAckermannHierarchy r)^[i] n) ≤ 2} ≤ k ↔
        n ≤ pettieTower (r + 1) k
      constructor
      · intro hle
        set m0 := sInf {i : ℕ | 1 ≤ i ∧ ((iteratedInvAckermannHierarchy r)^[i] n) ≤ 2}
        have hmem : 1 ≤ m0 ∧ ((iteratedInvAckermannHierarchy r)^[m0] n) ≤ 2 :=
          Nat.sInf_mem (h_nonempty n hn)
        have hni : n ≤ (pettieTower r)^[m0] 2 :=
          (h_iter_iff m0 n 2 hmem.1 hn (by omega)).mp hmem.2
        have hrew : (pettieTower r)^[m0] 2 = pettieTower (r + 1) m0 := by
          cases hm0 : m0 with
          | zero => omega
          | succ m => simp [pettieTower]
        rw [hrew] at hni
        exact le_trans hni (h_succ_mono m0 k hmem.1 hle)
      · intro hnk
        apply Nat.sInf_le
        refine ⟨hk, ?_⟩
        rw [h_iter_iff k n 2 hk hn (by omega)]
        cases k with
        | zero => omega
        | succ k' => simpa [pettieTower] using hnk
  have h2x1_le_tower : ∀ r x : ℕ, 1 ≤ r → 1 ≤ x → 2 * x + 1 ≤ ackTower r x := by
    intro r x hr hx
    cases r with
    | zero => omega
    | succ r' =>
      by_cases hx3 : 3 ≤ x
      · have hpow : 2 * x + 1 ≤ 2 ^ x := by
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hx3
          clear hx hx3
          induction d with
          | zero => decide
          | succ d ihd =>
            have h2d : 2 ≤ 2 ^ (3 + d) := by
              have : 2 ^ 1 ≤ 2 ^ (3 + d) := Nat.pow_le_pow_right (by omega) (by omega)
              omega
            calc 2 * (3 + (d + 1)) + 1 = (2 * (3 + d) + 1) + 2 := by ring
              _ ≤ 2 ^ (3 + d) + 2 ^ (3 + d) := Nat.add_le_add ihd h2d
              _ = 2 ^ (3 + (d + 1)) := by ring
        exact le_trans hpow (hTowerPow (r' + 1) x hx)
      · have hx_cases : x = 1 ∨ x = 2 := by omega
        rcases hx_cases with rfl | rfl
        · simp [ackTower]
        · have h14 : ackTower (r' + 1) 1 < ackTower (r' + 1) 2 :=
            hTowerStrict (r' + 1) 1 2 (by omega) (by omega)
          have h4 : ackTower (r' + 1) 1 = 4 := by simp [ackTower]
          omega
  have hPettieLeAck_aux : ∀ r' k : ℕ, 1 ≤ k →
      pettieTower (r' + 1) k ≤ ackTower (r' + 1) (2 * k + 1) := by
    intro r'
    induction r' with
    | zero =>
      intro k hk
      have heq1 : ∀ m' : ℕ, pettieTower 1 (m' + 1) = ackTower 1 (m' + 1) := by
        intro m'
        induction m' with
        | zero => simp [pettieTower, ackTower, ackermann, ackermannStep]
        | succ m' ihm =>
          have hL : pettieTower 1 (m' + 2) = pettieTower 0 (pettieTower 1 (m' + 1)) := by
            simp [pettieTower, Function.iterate_succ_apply']
          rw [hL, ihm]
          have hpos : 1 ≤ ackTower 1 (m' + 1) :=
            le_trans (by omega) (hTowerGe2 1 (m' + 1) (by omega))
          cases hA1 : ackTower 1 (m' + 1) with
          | zero => omega
          | succ t => simp [pettieTower, ackTower, hA1]
      cases k with
      | zero => omega
      | succ k' =>
        rw [heq1 k']
        exact hTowerMono 1 (k' + 1) (2 * (k' + 1) + 1) (by omega) (by omega)
    | succ r' ihr =>
      intro k hk
      have h_one_step : ∀ x : ℕ, 1 ≤ x →
          pettieTower (r' + 1) x ≤ ackTower (r' + 1) (ackTower (r' + 1) x) := by
        intro x hx
        exact le_trans (ihr x hx)
          (hTowerMono (r' + 1) (2 * x + 1) (ackTower (r' + 1) x) (by omega)
            (h2x1_le_tower (r' + 1) x (by omega) hx))
      have h_iter_bound : ∀ m' : ℕ,
          ((pettieTower (r' + 1))^[m' + 1] 2) ≤ ((ackTower (r' + 1))^[2 * (m' + 1)] 2) := by
        intro m'
        induction m' with
        | zero =>
          simpa [Function.iterate_succ_apply'] using h_one_step 2 (by omega)
        | succ m' ihm =>
          have hL : (pettieTower (r' + 1))^[m' + 2] 2 =
              pettieTower (r' + 1) ((pettieTower (r' + 1))^[m' + 1] 2) :=
            Function.iterate_succ_apply' (pettieTower (r' + 1)) (m' + 1) 2
          rw [hL]
          have hposL : 1 ≤ (pettieTower (r' + 1))^[m' + 1] 2 := by
            have hpow := (hPettieProp (r' + 2)).1 (m' + 1) (by omega)
            simp only [pettieTower] at hpow
            exact le_trans Nat.one_le_two_pow hpow
          have h1 := h_one_step _ hposL
          have h2 : ackTower (r' + 1) (ackTower (r' + 1) ((pettieTower (r' + 1))^[m' + 1] 2)) ≤
              ackTower (r' + 1) (ackTower (r' + 1) ((ackTower (r' + 1))^[2 * (m' + 1)] 2)) := by
            apply hTowerMono (r' + 1) _ _
            · exact le_trans (by omega : 1 ≤ 2) (hTowerGe2 (r' + 1) _ hposL)
            · exact hTowerMono (r' + 1) _ _ hposL ihm
          have hR : ackTower (r' + 1) (ackTower (r' + 1) ((ackTower (r' + 1))^[2 * (m' + 1)] 2)) =
              (ackTower (r' + 1))^[2 * (m' + 2)] 2 := by
            have heq : 2 * (m' + 2) = 2 * (m' + 1) + 1 + 1 := by omega
            rw [heq, Function.iterate_succ_apply', Function.iterate_succ_apply']
          rw [← hR]
          exact le_trans h1 h2
      have h_ack_unroll : ∀ t : ℕ, ((ackTower (r' + 1))^[t] 4) = ackTower (r' + 2) (t + 1) := by
        intro t; induction t with
        | zero => simp [ackTower]
        | succ t iht =>
          rw [Function.iterate_succ_apply', iht]
          simp [ackTower]
      have h_mono_iter : ∀ t a b : ℕ, 1 ≤ a → a ≤ b →
          ((ackTower (r' + 1))^[t] a) ≤ ((ackTower (r' + 1))^[t] b) := by
        intro t; induction t with
        | zero => intro a b _ hab; exact hab
        | succ t iht =>
          intro a b ha hab
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          exact iht _ _ (le_trans (by omega : 1 ≤ 2) (hTowerGe2 (r' + 1) a ha))
            (hTowerMono (r' + 1) a b ha hab)
      cases k with
      | zero => omega
      | succ k' =>
        simp only [pettieTower]
        rw [← h_ack_unroll (2 * (k' + 1))]
        exact le_trans (h_iter_bound k') (h_mono_iter (2 * (k' + 1)) 2 4 (by omega) (by omega))
  intro n hn
  have h_omega_nonempty : ({r : ℕ | 1 ≤ r ∧ iteratedInvAckermannHierarchy r n ≤ 2}).Nonempty := by
    have h_diag_grow : ∀ m : ℕ, m + 2 ≤ pettieTower (m + 1) 2 := by
      intro m; induction m with
      | zero =>
        change 2 ≤ pettieTower 1 2
        exact le_trans (by decide : 2 ≤ 2 ^ 2) ((hPettieProp 1).1 2 (by omega))
      | succ m ihm =>
        have hstep : pettieTower (m + 2) 2 = pettieTower (m + 1) (pettieTower (m + 1) 2) := by
          simp [pettieTower]
        rw [hstep]
        have hp := (hPettieProp (m + 1)).1 (pettieTower (m + 1) 2) (by omega)
        have hlt : pettieTower (m + 1) 2 < 2 ^ (pettieTower (m + 1) 2) := Nat.lt_two_pow_self
        omega
    refine ⟨n + 1, by omega, ?_⟩
    rw [(hPettieProp (n + 1)).2.2.2 n 2 hn (by omega)]
    exact le_trans (by omega) (h_diag_grow n)
  have hu_ge1 : 1 ≤ ordinalOmegaInvAckermann n :=
    le_csInf h_omega_nonempty (fun r hr => hr.1)
  refine ⟨hu_ge1, ?_⟩
  have hu_mem := Nat.sInf_mem h_omega_nonempty
  set u := ordinalOmegaInvAckermann n
  have h_n_le_G : n ≤ pettieTower u 2 :=
    ((hPettieProp u).2.2.2 n 2 hn (by omega)).mp hu_mem.2
  have h_G_le_F5 : pettieTower u 2 ≤ ackTower u 5 := by
    cases hu_eq : u with
    | zero => omega
    | succ u' => exact hPettieLeAck_aux u' 2 (by omega)
  have h_F5_le_Fu2 : ackTower u 5 ≤ ackTower (u + 2) 2 := by
    have h8 : 8 ≤ ackTower (u + 1) 3 := by simpa using hTowerPow (u + 1) 3 (by omega)
    have h1 : ackTower u 5 ≤ ackTower u (ackTower (u + 1) 3) :=
      hTowerMono u 5 (ackTower (u + 1) 3) (by omega) (by omega)
    cases hu_eq : u with
    | zero => omega
    | succ u' =>
      have heq : ackTower (u' + 3) 2 = ackTower (u' + 1) (ackTower (u' + 2) 3) := by
        simp [ackTower]
      rw [hu_eq] at h1
      simpa [heq] using h1
  rw [hAlphaOmegaSInf n hn]
  apply Nat.sInf_le
  exact ⟨by omega, le_trans h_n_le_G (le_trans h_G_le_F5 h_F5_le_Fu2)⟩

/-! ## Owned Theorem 1: Theorem 1.4 (`thm_1_4_main`) -/

/-- **Theorem 1.4** (`thm_1_4_main`), derived from Theorems 2.2, 2.5, 2.6, and Lemma A.1. -/
theorem thm_1_4_main
    (h_2_2 : Ty_thm_2_2) (h_2_5 : Ty_thm_2_5) (h_2_6 : Ty_thm_2_6) (h_A_1 : Ty_lem_A_1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [LinearOrder α] (n m : ℕ) (init : BST α) (ops : Fin m → DequeOp α),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        dequeSequenceCost init.tree ops ≤
          C * ((n : ℝ) + (m : ℝ) +
            (popCount ops : ℝ) * (alphaOmega (max (popCount ops) 1) : ℝ) +
            (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ)) := by
  obtain ⟨C_red, hCred_pos, hCred⟩ := h_2_2
  obtain ⟨C_pass, hCpass_pos, hCpass⟩ := h_2_5
  obtain ⟨C₀, hC0_ge6, hC0⟩ := h_2_6
  rcases h_A_1 with ⟨_, ⟨hTowerPow, hTowerStrict, _, _, _, _, _, hAlphaBound1, hAlphaOmegaSInf⟩, _⟩
  let K_bis : ℕ := 6 * C₀ ^ 2 + 6
  let C_J : ℝ := 2 * C_pass + (K_bis : ℝ)
  have hFoldedBound : ∀ (P : ℕ), 1 ≤ P → ∀ proc : FoldedPopProcess P,
      (proc.J : ℝ) ≤ C_J * (alphaOmega P : ℝ) * (P : ℝ) := by
    intro P hP proc
    set r := alphaOmega P
    have hr1 : 1 ≤ r := by
      have h_nonempty : ({r' : ℕ | 1 ≤ r' ∧ P ≤ ackTower r' 2}).Nonempty := by
        have hgrow : ∀ m : ℕ, m + 1 ≤ ackTower (m + 1) 2 := by
          intro m; induction m with
          | zero =>
            change 1 ≤ ackTower 1 2
            exact le_trans (by decide : 1 ≤ 2 ^ 2) (hTowerPow 1 2 (by decide))
          | succ m ih =>
            have hstep : ackTower (m + 1) 2 < ackTower (m + 2) 2 := by
              have heq : ackTower (m + 2) 2 = ackTower (m + 1) 4 := by simp [ackTower]
              rw [heq]
              exact hTowerStrict (m + 1) 2 4 (by omega) (by omega)
            change m + 2 ≤ ackTower (m + 2) 2
            omega
        have hPP := hgrow (P - 1)
        have hP1 : P - 1 + 1 = P := by omega
        rw [hP1] at hPP
        exact ⟨P, hP, hPP⟩
      have hmem := Nat.sInf_mem h_nonempty
      rw [← hAlphaOmegaSInf P hP] at hmem
      exact hmem.1
    have hPass2 : ∀ (N₁ : ℕ), 1 ≤ N₁ → N₁ ≤ 2 ^ (K_bis * r) →
        ∀ p₁ : FoldedPopProcess N₁, (p₁.J : ℝ) ≤ (K_bis : ℝ) * (r : ℝ) * (N₁ : ℝ) := by
      intro N₁ hN1 hN1_le p₁
      have hbis := (hCpass N₁ hN1 p₁).2
      have hclog : Nat.clog 2 N₁ ≤ K_bis * r :=
        (Nat.clog_le_iff_le_pow (by omega)).mpr hN1_le
      have hnat : p₁.J ≤ (K_bis * r) * N₁ := by
        calc p₁.J ≤ N₁ * (Nat.clog 2 N₁ - 1) := hbis
          _ ≤ N₁ * Nat.clog 2 N₁ := Nat.mul_le_mul_left N₁ (Nat.sub_le _ _)
          _ ≤ N₁ * (K_bis * r) := Nat.mul_le_mul_left N₁ hclog
          _ = (K_bis * r) * N₁ := by ring
      exact_mod_cast hnat
    have hPass1 : ∀ (N₀ : ℕ), 1 ≤ N₀ → N₀ < 2 ^ (C₀ ^ (3 * r)) →
        ∀ p₀ : FoldedPopProcess N₀,
          (p₀.J : ℝ) ≤ C_pass * (N₀ : ℝ) + (K_bis : ℝ) * (r : ℝ) * (N₀ : ℝ) := by
      intro N₀ hN0 hN0_lt p₀
      have hMaxBound : (max (alphaHierarchy 1 N₀) (2 ^ (C₀ ^ 2))) ^ 6 ≤ 2 ^ (K_bis * r) := by
        have ha1 := (hAlphaBound1 1 N₀ (by omega) hN0).2.1
        have h3r_ge : 216 ≤ C₀ ^ (3 * r) := by
          have h1 : 6 ^ 3 ≤ C₀ ^ (3 * 1) := Nat.pow_le_pow_left hC0_ge6 3
          have h2 : C₀ ^ (3 * 1) ≤ C₀ ^ (3 * r) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          exact le_trans (by decide : 216 ≤ 6 ^ 3) (le_trans h1 h2)
        have h16_lt : 16 < 2 ^ (C₀ ^ (3 * r)) := by
          have : 2 ^ 5 ≤ 2 ^ (C₀ ^ (3 * r)) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hN0_16 : N₀ + 16 < 2 ^ (C₀ ^ (3 * r) + 1) := by
          have : 2 ^ (C₀ ^ (3 * r) + 1) = 2 ^ (C₀ ^ (3 * r)) + 2 ^ (C₀ ^ (3 * r)) := by ring
          omega
        have hlog1 : Nat.log 2 (N₀ + 16) ≤ C₀ ^ (3 * r) := by
          have hlt : Nat.log 2 (N₀ + 16) < C₀ ^ (3 * r) + 1 :=
            (Nat.log_lt_iff_lt_pow (by omega) (by omega)).mpr hN0_16
          omega
        have hc3 : C₀ ^ (3 * r) ≤ 2 ^ (C₀ ^ 2 * r) := by
          calc C₀ ^ (3 * r) = (C₀ ^ 3) ^ r := by rw [Nat.pow_mul]
            _ ≤ (2 ^ (C₀ ^ 2)) ^ r := Nat.pow_le_pow_left (cube_le_two_pow_sq C₀ hC0_ge6) r
            _ = 2 ^ (C₀ ^ 2 * r) := (Nat.pow_mul 2 (C₀ ^ 2) r).symm
        have hlog2 : Nat.log 2 (Nat.log 2 (N₀ + 16)) ≤ C₀ ^ 2 * r := by
          by_cases h0 : Nat.log 2 (N₀ + 16) = 0
          · simp [h0]
          · have hlt : Nat.log 2 (Nat.log 2 (N₀ + 16)) < C₀ ^ 2 * r + 1 := by
              rw [Nat.log_lt_iff_lt_pow (by omega) (by omega)]
              have hle := le_trans hlog1 hc3
              have : 2 ^ (C₀ ^ 2 * r) < 2 ^ (C₀ ^ 2 * r + 1) :=
                Nat.pow_lt_pow_right (by omega) (by omega)
              omega
            omega
        have ha1_le : alphaHierarchy 1 N₀ ≤ 2 ^ (C₀ ^ 2 + r) := by
          have hsq_ge : 36 ≤ C₀ ^ 2 := by nlinarith
          have hpow_c : C₀ ^ 2 + 2 ≤ 2 ^ (C₀ ^ 2) := by
            have hc2 : ∀ k : ℕ, 2 ≤ k → k + 2 ≤ 2 ^ k := by
              intro k hk; obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk; clear hk
              induction d with
              | zero => decide
              | succ d ih =>
                have h1 : 1 ≤ 2 ^ (2 + d) := Nat.one_le_two_pow
                calc 2 + (d + 1) + 2 = (2 + d + 2) + 1 := by ring
                  _ ≤ 2 ^ (2 + d) + 2 ^ (2 + d) := Nat.add_le_add ih h1
                  _ = 2 ^ (2 + (d + 1)) := by ring
            exact hc2 (C₀ ^ 2) (by omega)
          have hr_pow : r ≤ 2 ^ r := Nat.le_of_lt Nat.lt_two_pow_self
          calc alphaHierarchy 1 N₀ ≤ C₀ ^ 2 * r + 2 := le_trans ha1 (by omega)
            _ ≤ (C₀ ^ 2 + 2) * r := by nlinarith
            _ ≤ 2 ^ (C₀ ^ 2) * 2 ^ r := Nat.mul_le_mul hpow_c hr_pow
            _ = 2 ^ (C₀ ^ 2 + r) := (Nat.pow_add 2 (C₀ ^ 2) r).symm
        have hmax_le : max (alphaHierarchy 1 N₀) (2 ^ (C₀ ^ 2)) ≤ 2 ^ (C₀ ^ 2 + r) := by
          apply max_le ha1_le
          exact Nat.pow_le_pow_right (by omega) (by omega)
        calc (max (alphaHierarchy 1 N₀) (2 ^ (C₀ ^ 2))) ^ 6
            ≤ (2 ^ (C₀ ^ 2 + r)) ^ 6 := Nat.pow_le_pow_left hmax_le 6
          _ = 2 ^ ((C₀ ^ 2 + r) * 6) := (Nat.pow_mul 2 (C₀ ^ 2 + r) 6).symm
          _ ≤ 2 ^ (K_bis * r) := by
              apply Nat.pow_le_pow_right (by omega)
              dsimp [K_bis]
              nlinarith
      rcases (hC0 N₀ 1 hN0 (by omega)).2.2 rfl with hSmall | ⟨M₁, T₁, hVal1, hLeaves1⟩
      · have hN0_le : N₀ ≤ 2 ^ (K_bis * r) := by omega
        have h2 := hPass2 N₀ hN0 hN0_le p₀
        have : (0 : ℝ) ≤ C_pass * (N₀ : ℝ) := by positivity
        linarith
      · have hPass1Inst := (hCpass N₀ hN0 p₀).1 1 M₁ T₁ hVal1
        dsimp only at hPass1Inst
        obtain ⟨hSizes1, hSum1, subProcs1, hBound1⟩ := hPass1Inst
        have h_list : ∀ (xs : List {Q // Q ∈ scaleTreePartitionChain T₁ N₀ M₁ (Fin.last M₁)}),
            ((xs.map (fun x => ((subProcs1 x.1 x.2).J : ℝ))).sum) ≤
              (K_bis : ℝ) * (r : ℝ) * ((xs.map (fun x => (x.1.size : ℝ))).sum) := by
          intro xs; induction xs with
          | nil => simp
          | cons x xs ih =>
            simp only [List.map_cons, List.sum_cons]
            have hx := hPass2 x.1.size (hSizes1 x.1 x.2).1
              (le_of_lt (lt_of_lt_of_le (hLeaves1 x.1 x.2) hMaxBound)) (subProcs1 x.1 x.2)
            linarith
        have h_eq_size : ((scaleTreePartitionChain T₁ N₀ M₁ (Fin.last M₁)).attach.map
            (fun x => (x.1.size : ℝ))).sum =
            (((scaleTreePartitionChain T₁ N₀ M₁ (Fin.last M₁)).map IntervalBlock.size).sum : ℝ) := by
          rw [cast_list_sum, List.map_map]
          have hfun : (fun x : {Q // Q ∈ scaleTreePartitionChain T₁ N₀ M₁ (Fin.last M₁)} =>
              (x.1.size : ℝ)) =
              ((fun k : ℕ => (k : ℝ)) ∘ IntervalBlock.size) ∘ Subtype.val := rfl
          rw [hfun, ← List.map_map, List.attach_map_subtype_val]
        have hLeafSum := h_list (scaleTreePartitionChain T₁ N₀ M₁ (Fin.last M₁)).attach
        rw [h_eq_size, hSum1] at hLeafSum
        have h1cast : C_pass * ((1 : ℕ) : ℝ) * (N₀ : ℝ) = C_pass * (N₀ : ℝ) := by norm_num
        rw [h1cast] at hBound1
        have hfun_eq :
            (fun x : {Q // Q ∈ scaleTreePartitionChain T₁ N₀ M₁ (Fin.last M₁)} =>
              match x with | ⟨Q, hQ⟩ => ((subProcs1 Q hQ).J : ℝ)) =
            (fun x => ((subProcs1 x.1 x.2).J : ℝ)) := by
          funext ⟨Q, hQ⟩; rfl
        rw [hfun_eq] at hBound1
        linarith
    have hr_real : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hP_nonneg : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
    have h_extra : C_pass * (P : ℝ) ≤ C_pass * (r : ℝ) * (P : ℝ) := by
      have : 0 ≤ C_pass * ((r : ℝ) - 1) * (P : ℝ) :=
        mul_nonneg (mul_nonneg (le_of_lt hCpass_pos) (by linarith)) hP_nonneg
      linarith [show C_pass * ((r : ℝ) - 1) * (P : ℝ) =
        C_pass * (r : ℝ) * (P : ℝ) - C_pass * (P : ℝ) by ring]
    have hCrP_nonneg : 0 ≤ C_pass * (r : ℝ) * (P : ℝ) := by positivity
    have hCJ_expand : C_J * (r : ℝ) * (P : ℝ) =
        C_pass * (r : ℝ) * (P : ℝ) + C_pass * (r : ℝ) * (P : ℝ) +
          (K_bis : ℝ) * (r : ℝ) * (P : ℝ) := by
      dsimp [C_J]; ring
    rcases (hC0 P r hP hr1).2.1 rfl with hSmall0 | ⟨M₀, T₀, hVal0, hLeaves0⟩
    · have h1 := hPass1 P hP hSmall0 proc
      rw [hCJ_expand]
      linarith
    · have hPass0Inst := (hCpass P hP proc).1 r M₀ T₀ hVal0
      dsimp only at hPass0Inst
      obtain ⟨hSizes0, hSum0, subProcs0, hBound0⟩ := hPass0Inst
      have h_list : ∀ (xs : List {Q // Q ∈ scaleTreePartitionChain T₀ P M₀ (Fin.last M₀)}),
          ((xs.map (fun x => ((subProcs0 x.1 x.2).J : ℝ))).sum) ≤
            (C_pass + (K_bis : ℝ) * (r : ℝ)) * ((xs.map (fun x => (x.1.size : ℝ))).sum) := by
        intro xs; induction xs with
        | nil => simp
        | cons x xs ih =>
          simp only [List.map_cons, List.sum_cons]
          have hx := hPass1 x.1.size (hSizes0 x.1 x.2).1 (hLeaves0 x.1 x.2) (subProcs0 x.1 x.2)
          linarith [show (C_pass + (K_bis : ℝ) * (r : ℝ)) * ((x.1.size : ℝ) +
              (List.map (fun x => (x.1.size : ℝ)) xs).sum) =
            C_pass * (x.1.size : ℝ) + (K_bis : ℝ) * (r : ℝ) * (x.1.size : ℝ) +
              (C_pass + (K_bis : ℝ) * (r : ℝ)) *
                (List.map (fun x => (x.1.size : ℝ)) xs).sum by ring]
      have h_eq_size : ((scaleTreePartitionChain T₀ P M₀ (Fin.last M₀)).attach.map
          (fun x => (x.1.size : ℝ))).sum =
          (((scaleTreePartitionChain T₀ P M₀ (Fin.last M₀)).map IntervalBlock.size).sum : ℝ) := by
        rw [cast_list_sum, List.map_map]
        have hfun : (fun x : {Q // Q ∈ scaleTreePartitionChain T₀ P M₀ (Fin.last M₀)} =>
            (x.1.size : ℝ)) =
            ((fun k : ℕ => (k : ℝ)) ∘ IntervalBlock.size) ∘ Subtype.val := rfl
        rw [hfun, ← List.map_map, List.attach_map_subtype_val]
      have hLeafSum0 := h_list (scaleTreePartitionChain T₀ P M₀ (Fin.last M₀)).attach
      rw [h_eq_size, hSum0] at hLeafSum0
      have hfun_eq0 :
          (fun x : {Q // Q ∈ scaleTreePartitionChain T₀ P M₀ (Fin.last M₀)} =>
            match x with | ⟨Q, hQ⟩ => ((subProcs0 Q hQ).J : ℝ)) =
          (fun x => ((subProcs0 x.1 x.2).J : ℝ)) := by
        funext ⟨Q, hQ⟩; rfl
      rw [hfun_eq0] at hBound0
      rw [hCJ_expand]
      linarith [show (C_pass + (K_bis : ℝ) * (r : ℝ)) * (P : ℝ) =
        C_pass * (P : ℝ) + (K_bis : ℝ) * (r : ℝ) * (P : ℝ) by ring]
  have hCJ_pos : 0 < C_J := by dsimp [C_J, K_bis]; positivity
  refine ⟨max C_red (2 * C_J), lt_max_of_lt_left hCred_pos, ?_⟩
  intro α _ n m init ops hn hValid
  obtain ⟨HL, HR, hRed⟩ := hCred n m init ops hn hValid
  have hHL : (HL.J : ℝ) ≤ C_J * (popCount ops : ℝ) * (alphaOmega (max (popCount ops) 1) : ℝ) := by
    by_cases hdL : popCount ops = 0
    · revert HL
      rw [hdL]
      intro HL
      rw [foldedPopProcess_zero_J HL]
      simp
    · have hdL1 : 1 ≤ popCount ops := by omega
      have hmax : max (popCount ops) 1 = popCount ops := max_eq_left hdL1
      rw [hmax]
      have := hFoldedBound (popCount ops) hdL1 HL
      linarith
  have hHR : (HR.J : ℝ) ≤ C_J * (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ) := by
    by_cases hdR : ejectCount ops = 0
    · revert HR
      rw [hdR]
      intro HR
      rw [foldedPopProcess_zero_J HR]
      simp
    · have hdR1 : 1 ≤ ejectCount ops := by omega
      have hmax : max (ejectCount ops) 1 = ejectCount ops := max_eq_left hdR1
      rw [hmax]
      have := hFoldedBound (ejectCount ops) hdR1 HR
      linarith
  set C := max C_red (2 * C_J)
  have hCred_le : C_red ≤ C := le_max_left _ _
  have h2CJ_le : 2 * C_J ≤ C := le_max_right _ _
  have hnm_nonneg : (0 : ℝ) ≤ (n : ℝ) + (m : ℝ) := by positivity
  have hL_nonneg : (0 : ℝ) ≤ (popCount ops : ℝ) * (alphaOmega (max (popCount ops) 1) : ℝ) := by
    positivity
  have hR_nonneg : (0 : ℝ) ≤ (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ) := by
    positivity
  nlinarith

/-! ## Owned Theorem 2: `deque_ordinal_omega_ackermann_bound` -/

/-- Direct derivation of `deque_ordinal_omega_ackermann_bound` from `thm_1_4_main`,
`prop_1_3_omega_properties`, and `lem_A_1_ack_basic`. -/
theorem deque_ordinal_omega_ackermann_bound_of_thm_1_4
    (h_1_4 :
      ∃ C : ℝ, 0 < C ∧
        ∀ {α : Type} [LinearOrder α] (n m : ℕ) (init : BST α) (ops : Fin m → DequeOp α),
          init.tree.num_nodes = n →
          ValidDequeSeq init.tree ops →
          dequeSequenceCost init.tree ops ≤
            C * ((n : ℝ) + (m : ℝ) +
              (popCount ops : ℝ) * (alphaOmega (max (popCount ops) 1) : ℝ) +
              (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ)))
    (h_1_3 : Ty_prop_1_3)
    (h_A_1 : Ty_lem_A_1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) (init : BST ℤ) (ops : Fin m → DequeOp ℤ),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        dequeSequenceCost init.tree ops ≤
          C * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := h_1_4
  refine ⟨4 * C, by linarith, ?_⟩
  intro n m init ops hn hValid
  by_cases hmn0 : m + n = 0
  · have hm0 : m = 0 := by omega
    have hn0 : n = 0 := by omega
    subst hm0; subst hn0
    simp [dequeSequenceCost]
  · have hmn1 : 1 ≤ m + n := by omega
    have ⟨hu1, hubound⟩ := bridge_alphaOmega_ordinalOmega h_A_1 (m + n) hmn1
    have hd_le : popCount ops + ejectCount ops ≤ m := popCount_add_ejectCount_le ops
    have hmono := h_1_3.1
    have hL_le : alphaOmega (max (popCount ops) 1) ≤ alphaOmega (m + n) :=
      hmono _ _ (by omega) (by omega)
    have hR_le : alphaOmega (max (ejectCount ops) 1) ≤ alphaOmega (m + n) :=
      hmono _ _ (by omega) (by omega)
    have hstep := hC n m init ops hn hValid
    have h_om_le : (alphaOmega (m + n) : ℝ) ≤ 3 * (ordinalOmegaInvAckermann (m + n) : ℝ) := by
      have : alphaOmega (m + n) ≤ 3 * ordinalOmegaInvAckermann (m + n) := by omega
      exact_mod_cast this
    have hu1R : (1 : ℝ) ≤ (ordinalOmegaInvAckermann (m + n) : ℝ) := by exact_mod_cast hu1
    have hdL_R : (popCount ops : ℝ) + (ejectCount ops : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
      have : popCount ops + ejectCount ops ≤ m + n := by omega
      exact_mod_cast this
    have hL_R : (alphaOmega (max (popCount ops) 1) : ℝ) ≤ (alphaOmega (m + n) : ℝ) := by
      exact_mod_cast hL_le
    have hR_R : (alphaOmega (max (ejectCount ops) 1) : ℝ) ≤ (alphaOmega (m + n) : ℝ) := by
      exact_mod_cast hR_le
    have hsum_R : (n : ℝ) + (m : ℝ) +
        (popCount ops : ℝ) * (alphaOmega (max (popCount ops) 1) : ℝ) +
        (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ) ≤
        4 * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) := by
      have hp_nonneg : (0 : ℝ) ≤ (popCount ops : ℝ) := Nat.cast_nonneg _
      have he_nonneg : (0 : ℝ) ≤ (ejectCount ops : ℝ) := Nat.cast_nonneg _
      have hmn_nonneg : (0 : ℝ) ≤ (m : ℝ) + (n : ℝ) := by positivity
      have hom_nonneg : (0 : ℝ) ≤ (alphaOmega (m + n) : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc dequeSequenceCost init.tree ops
        ≤ C * ((n : ℝ) + (m : ℝ) +
            (popCount ops : ℝ) * (alphaOmega (max (popCount ops) 1) : ℝ) +
            (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ)) := hstep
      _ ≤ C * (4 * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hsum_R (le_of_lt hCpos)
      _ = 4 * C * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) := by ring

/-- **Ordinal-`ω` Inverse-Ackermann Deque Bound** (`deque_ordinal_omega_ackermann_bound`),
derived solely from strict upstream Layer `< 5` hypotheses (`thm_2_2_mod1_reduction`,
`thm_2_5_mod3_pass`, `thm_2_6_mod4_contraction`, `lem_A_1_ack_basic`, and
`prop_1_3_omega_properties`) via `thm_1_4_main`. -/
theorem deque_ordinal_omega_ackermann_bound
    (h_2_2 : Ty_thm_2_2) (h_2_5 : Ty_thm_2_5) (h_2_6 : Ty_thm_2_6)
    (h_A_1 : Ty_lem_A_1) (h_1_3 : Ty_prop_1_3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) (init : BST ℤ) (ops : Fin m → DequeOp ℤ),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        dequeSequenceCost init.tree ops ≤
          C * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) :=
  deque_ordinal_omega_ackermann_bound_of_thm_1_4
    (thm_1_4_main h_2_2 h_2_5 h_2_6 h_A_1) h_1_3 h_A_1

end Solution.TopAssembly
