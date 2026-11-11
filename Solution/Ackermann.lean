module

public import Challenge.Definitions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

/-!
# Section 1 & Appendix A: Ackermann Hierarchy, `α_ω`, and Löb–Wainer Bounds

Unconditional proofs of:
* `lem_A_1_ack_basic` (Lemma A.1)
* `prop_1_3_omega_properties` (Proposition 1.3)
* `prop_A_2_lob_wainer` (Proposition A.2)
-/

@[expose] public section

namespace Solution.Ackermann

open SplayTree

/-! ## 1. Elementary Arithmetic, Exponential, and Logarithm Helpers -/

private lemma two_mul_le_two_pow : ∀ j : ℕ, 1 ≤ j → 2 * j ≤ 2 ^ j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _
    rcases j with _ | m
    · norm_num
    · have hm := ih (by omega)
      have hpow : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
      omega

private lemma three_mul_le_two_pow_succ : ∀ k : ℕ, 2 ≤ k → 3 * k ≤ 2 ^ (k + 1) := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => norm_num
  | succ d ih =>
    have hpow : 2 ^ (2 + (d + 1) + 1) = 2 * 2 ^ (2 + d + 1) := by
      have : 2 + (d + 1) + 1 = (2 + d + 1) + 1 := by omega
      rw [this, pow_succ]; ring
    have hge8 : 8 ≤ 2 ^ (2 + d + 1) := by
      have : 2 ^ 3 ≤ 2 ^ (2 + d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    omega

private lemma three_mul_lt_two_pow_add3 : ∀ q : ℕ, 3 * q < 2 ^ (q + 3) := by
  intro q
  induction q with
  | zero => norm_num
  | succ q ih =>
    have hpow : 2 ^ (q + 1 + 3) = 2 * 2 ^ (q + 3) := by
      have : q + 1 + 3 = (q + 3) + 1 := by omega
      rw [this, pow_succ]; ring
    have hge8 : 8 ≤ 2 ^ (q + 3) := by
      have : 2 ^ 3 ≤ 2 ^ (q + 3) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    omega

private lemma three_mul_le_two_pow : ∀ m : ℕ, 4 ≤ m → 3 * m ≤ 2 ^ m := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction d with
  | zero => norm_num
  | succ d ih =>
    have hpow : 2 ^ (4 + (d + 1)) = 2 * 2 ^ (4 + d) := by
      have : 4 + (d + 1) = (4 + d) + 1 := by omega
      rw [this, pow_succ]; ring
    have hge16 : 16 ≤ 2 ^ (4 + d) := by
      have : 2 ^ 4 ≤ 2 ^ (4 + d) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    omega

private lemma self_le_two_pow_pred : ∀ n : ℕ, 5 ≤ n → n ≤ 2 ^ (n - 1) := by
  intro n hn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  have hsub : 5 + d - 1 = 4 + d := by omega
  rw [hsub]
  induction d with
  | zero => norm_num
  | succ d ih =>
    have hpow : 2 ^ (4 + (d + 1)) = 2 * 2 ^ (4 + d) := by
      have : 4 + (d + 1) = (4 + d) + 1 := by omega
      rw [this, pow_succ]; ring
    omega

private lemma linear_le_pow17 : ∀ d : ℕ, 20 + 6 * (d + 17) ≤ 2 ^ (d + 17) := by
  intro d
  induction d with
  | zero => norm_num
  | succ d ih =>
    have hpow : 2 ^ (d + 1 + 17) = 2 * 2 ^ (d + 17) := by
      have : d + 1 + 17 = (d + 17) + 1 := by omega
      rw [this, pow_succ]; ring
    omega

private lemma mul_lt_two_pow_of_ge : ∀ K u : ℕ, 2 * K + 6 ≤ u → K * u < 2 ^ u := by
  intro K u hu
  have h2u : ∀ d : ℕ, 2 * (d + 5) < 2 ^ (d + 5) := by
    intro d
    induction d with
    | zero => norm_num
    | succ d ih =>
      have : d + 1 + 5 = (d + 5) + 1 := by omega
      rw [this, pow_succ]; omega
  have hK1 : K + 1 ≤ 2 ^ (K + 1) := le_of_lt Nat.lt_two_pow_self
  set d := u - (K + 1) - 5
  have hd_eq : u - (K + 1) = d + 5 := by omega
  have h2 : u < 2 ^ (u - (K + 1)) := by
    calc u ≤ 2 * (d + 5) := by omega
      _ < 2 ^ (d + 5) := h2u d
      _ = 2 ^ (u - (K + 1)) := by rw [hd_eq]
  have hpos : 0 < 2 ^ (K + 1) := Nat.two_pow_pos (K + 1)
  calc K * u ≤ (K + 1) * u := Nat.mul_le_mul_right _ (by omega)
    _ < 2 ^ (K + 1) * 2 ^ (u - (K + 1)) := Nat.mul_lt_mul_of_le_of_lt hK1 h2 hpos
    _ = 2 ^ u := by rw [← pow_add]; congr 1; omega

private lemma cast_nat_log_le_logb (a : ℕ) (x : ℝ) (ha : 1 ≤ a) (hax : (a : ℝ) ≤ x) :
    (Nat.log 2 a : ℝ) ≤ Real.logb 2 x := by
  have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le ha_pos hax
  rw [Real.le_logb_iff_rpow_le (by norm_num) hx_pos, Real.rpow_natCast]
  have hpow : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 (by omega)
  exact le_trans (by exact_mod_cast hpow) hax


/-! ## 2. Foundational `ackermann` and `alpha0` (`invAckermann`) Properties -/

private lemma ack_ge_two_mul : ∀ i j : ℕ, 1 ≤ j → 2 * j ≤ ackermann i j := by
  intro i
  induction i with
  | zero => intro j _; simp [ackermann]
  | succ i ih_i =>
    rcases i with _ | r
    · intro j hj; simpa [ackermann] using two_mul_le_two_pow j hj
    · intro j
      induction j with
      | zero => intro h; omega
      | succ j ih_j =>
        intro _
        rcases j with _ | m
        · have h2 := ih_i 2 (by omega)
          change 2 * 1 ≤ ackermann (r + 1) 2; omega
        · have hm : 2 * (m + 1) ≤ ackermann (r + 2) (m + 1) := ih_j (by omega)
          have hx : 2 * ackermann (r + 2) (m + 1) ≤ ackermann (r + 1) (ackermann (r + 2) (m + 1)) :=
            ih_i (ackermann (r + 2) (m + 1)) (by omega)
          change 2 * (m + 2) ≤ ackermann (r + 1) (ackermann (r + 2) (m + 1)); omega

private lemma ack_strictMono_j : ∀ i : ℕ, StrictMono (ackermann i) := by
  intro i
  apply strictMono_nat_of_lt_succ
  intro j
  rcases i with _ | _ | r
  · simp [ackermann]
  · simp only [ackermann]; exact Nat.pow_lt_pow_right (by omega) (by omega)
  · rcases j with _ | m
    · have h2 := ack_ge_two_mul (r + 1) 2 (by omega)
      change 1 < ackermann (r + 1) 2; omega
    · have hm := ack_ge_two_mul (r + 2) (m + 1) (by omega)
      have hx := ack_ge_two_mul (r + 1) (ackermann (r + 2) (m + 1)) (by omega)
      change ackermann (r + 2) (m + 1) < ackermann (r + 1) (ackermann (r + 2) (m + 1)); omega

private lemma ack_mono_i_step : ∀ i j : ℕ, 1 ≤ j → ackermann i j ≤ ackermann (i + 1) j := by
  intro i
  induction i with
  | zero => intro j hj; simpa [ackermann] using two_mul_le_two_pow j hj
  | succ i ih_i =>
    rcases i with _ | r
    · intro j hj
      rcases j with _ | _ | m
      · omega
      · change 2 ^ 1 ≤ 2 ^ 2; norm_num
      · have hm := ack_ge_two_mul 2 (m + 1) (by omega)
        change 2 ^ (m + 2) ≤ 2 ^ (ackermann 2 (m + 1))
        exact Nat.pow_le_pow_right (by omega) (by omega)
    · intro j
      induction j with
      | zero => intro h; omega
      | succ j ih_j =>
        intro _
        rcases j with _ | m
        · change ackermann (r + 2) 1 ≤ ackermann (r + 2) 2
          exact (ack_strictMono_j (r + 2)).monotone (by omega)
        · have hm := ack_ge_two_mul (r + 2) (m + 1) (by omega)
          have h1 := ih_i (ackermann (r + 2) (m + 1)) (by omega)
          have h2 := (ack_strictMono_j (r + 2)).monotone (ih_j (by omega))
          change ackermann (r + 1) (ackermann (r + 2) (m + 1)) ≤
            ackermann (r + 2) (ackermann (r + 3) (m + 1))
          exact le_trans h1 h2

private lemma ack_mono_i : ∀ j : ℕ, 1 ≤ j → Monotone (fun i => ackermann i j) :=
  fun j hj => monotone_nat_of_le_succ (fun i => ack_mono_i_step i j hj)

private lemma ack_step_col1 {i : ℕ} (hi : 1 ≤ i) : ackermann (i + 1) 1 = ackermann i 2 := by
  rcases i with _ | d
  · omega
  · rfl

private lemma ack_step_succ {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) :
    ackermann (i + 1) (j + 1) = ackermann i (ackermann (i + 1) j) := by
  rcases i with _ | d
  · omega
  · rcases j with _ | m
    · omega
    · rfl

private lemma ack_col1_double : ∀ k : ℕ, 1 ≤ k → 2 * ackermann k 1 ≤ ackermann (k + 1) 1 := by
  intro k hk
  rcases k with _ | _ | r
  · omega
  · change 2 * 2 ≤ 4; omega
  · have h1 := ack_ge_two_mul (r + 2) 1 (by omega)
    exact ack_ge_two_mul (r + 1) (ackermann (r + 2) 1) (by omega)

private lemma ack_col1_exp : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ ackermann k 1 := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases k with _ | m
    · change 2 ^ 1 ≤ 2; omega
    · have hm := ih (by omega)
      have hd := ack_col1_double (m + 1) (by omega)
      have hpow : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
      omega

private lemma ack_col1_strictMono :
    ∀ k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → ackermann k₁ 1 < ackermann k₂ 1 := by
  have h_adj : ∀ k : ℕ, 1 ≤ k → ackermann k 1 < ackermann (k + 1) 1 := by
    intro k hk
    have hexp := ack_col1_exp k hk
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hd := ack_col1_double k hk
    omega
  intro k₁ k₂ hk₁ hlt
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.add_one_le_iff.mpr hlt)
  clear hlt
  induction d with
  | zero =>
    simpa using h_adj k₁ hk₁
  | succ d ih =>
    have heq : k₁ + 1 + (d + 1) = (k₁ + 1 + d) + 1 := by omega
    rw [heq]
    exact lt_trans ih (h_adj (k₁ + 1 + d) (by omega))

private lemma ack2_tower : ∀ j : ℕ, 1 ≤ j → 2 ^ (2 ^ j) ≤ ackermann 2 j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _
    rcases j with _ | m
    · change 2 ^ (2 ^ 1) ≤ 4; norm_num
    · have hm := ih (by omega)
      have hlt : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
      have h2 := two_mul_le_two_pow (2 ^ (m + 1)) (by omega)
      have hpow : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
      change 2 ^ (2 ^ (m + 2)) ≤ 2 ^ (ackermann 2 (m + 1))
      exact Nat.pow_le_pow_right (by omega) (by omega)

private lemma ack_col1_double_exp : ∀ m : ℕ, 4 ≤ m → 2 ^ (2 ^ m) ≤ ackermann m 1 := by
  intro m hm
  have h1 : m ≤ ackermann (m - 1) 1 := by
    have hlt : m - 1 < 2 ^ (m - 1) := Nat.lt_two_pow_self
    have hexp := ack_col1_exp (m - 1) (by omega)
    omega
  have h_eq : ackermann m 1 = ackermann (m - 2) (ackermann (m - 1) 1) := by
    have hm1 : m = (m - 1) + 1 := by omega
    have hm2 : m - 1 = (m - 2) + 1 := by omega
    calc ackermann m 1 = ackermann ((m - 1) + 1) 1 := by rw [← hm1]
      _ = ackermann (m - 1) 2 := ack_step_col1 (by omega)
      _ = ackermann ((m - 2) + 1) 2 := by rw [← hm2]
      _ = ackermann (m - 2) (ackermann ((m - 2) + 1) 1) := ack_step_succ (by omega) (by omega)
      _ = ackermann (m - 2) (ackermann (m - 1) 1) := by rw [← hm2]
  rw [h_eq]
  calc 2 ^ (2 ^ m) ≤ ackermann 2 m := ack2_tower m (by omega)
    _ ≤ ackermann 2 (ackermann (m - 1) 1) := (ack_strictMono_j 2).monotone h1
    _ ≤ ackermann (m - 2) (ackermann (m - 1) 1) := ack_mono_i _ (by omega) (by omega)

private lemma ack4_eq_ack2_16_and_gt :
    ackermann 4 1 = ackermann 2 16 ∧ 2 ^ 65536 < ackermann 2 16 := by
  have h31 : ackermann 3 1 = 16 := rfl
  have h41 : ackermann 4 1 = ackermann 2 16 := by
    calc ackermann 4 1 = ackermann 3 2 := ack_step_col1 (by decide)
      _ = ackermann 2 (ackermann 3 1) := ack_step_succ (by decide) (by decide)
      _ = ackermann 2 16 := by rw [h31]
  have h2_step : ∀ m : ℕ, ackermann 2 (m + 2) = 2 ^ ackermann 2 (m + 1) := fun _ => rfl
  have h22 : ackermann 2 2 = 16 := rfl
  have h23 : ackermann 2 3 = 65536 := by
    rw [h2_step 1, h22]; norm_num
  have h24 : ackermann 2 4 = 2 ^ 65536 := by
    rw [h2_step 2, h23]
  have hlt : 2 ^ 65536 < ackermann 2 16 := by
    rw [← h24]
    exact ack_strictMono_j 2 (by decide : 4 < 16)
  exact ⟨h41, hlt⟩

private lemma invAck_nonempty : ∀ n : ℕ, {k : ℕ | 1 ≤ k ∧ n ≤ ackermann k 1}.Nonempty := by
  intro n
  have hlt : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hexp := ack_col1_exp (n + 1) (by omega)
  exact ⟨n + 1, by omega, by omega⟩

private lemma invAck_spec :
    ∀ n : ℕ, 1 ≤ invAckermann n ∧ n ≤ ackermann (invAckermann n) 1 ∧
      ∀ k : ℕ, 1 ≤ k → k < invAckermann n → ackermann k 1 < n := by
  intro n
  obtain ⟨h1, h2⟩ := Nat.sInf_mem (invAck_nonempty n)
  refine ⟨h1, h2, ?_⟩
  intro k hk1 hklt
  by_contra hnot
  have hle : n ≤ ackermann k 1 := Nat.le_of_not_lt hnot
  have hinv_le : invAckermann n ≤ k := Nat.sInf_le ⟨hk1, hle⟩
  omega

private lemma invAck_galois : ∀ n k : ℕ, 1 ≤ k → (invAckermann n ≤ k ↔ n ≤ ackermann k 1) := by
  intro n k hk
  constructor
  · intro hle; exact le_trans (invAck_spec n).2.1 (ack_mono_i 1 (by omega) hle)
  · intro hle; exact Nat.sInf_le ⟨hk, hle⟩

private lemma invAck_mono : Monotone invAckermann := fun a b hab =>
  (invAck_galois a (invAckermann b) (invAck_spec b).1).mpr (le_trans hab (invAck_spec b).2.1)

private lemma invAck_lt : ∀ n : ℕ, 2 < n → invAckermann n < n := by
  intro n hn
  set k := invAckermann n
  have hk2 : 2 ≤ k := by
    by_contra hk1
    have := (invAck_galois n 1 (by omega)).mp (by omega)
    change n ≤ 2 at this; omega
  have hnot : ¬ (n ≤ ackermann (k - 1) 1) := fun hle =>
    absurd ((invAck_galois n (k - 1) (by omega)).mpr hle) (by omega)
  have hexp := ack_col1_exp (k - 1) (by omega)
  have hpow : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
  omega

private lemma invAck_shift : ∀ n : ℕ, invAckermann (n + 2) ≤ invAckermann n + 1 := by
  intro n
  set k := invAckermann n
  have hk1 : 1 ≤ k := (invAck_spec n).1
  have hn : n ≤ ackermann k 1 := (invAck_spec n).2.1
  have hexp : 2 ^ 1 ≤ ackermann k 1 :=
    le_trans (Nat.pow_le_pow_right (by omega) hk1) (ack_col1_exp k hk1)
  have hd := ack_col1_double k hk1
  exact (invAck_galois (n + 2) (k + 1) (by omega)).mpr (by omega)

private lemma invAck_poly : ∀ u : ℕ, 5 ≤ u → invAckermann (2 ^ 20 * u ^ 6) ≤ invAckermann u + 1 := by
  intro u hu5
  have h_ack21 : ackermann 2 1 = 4 := rfl
  have h_ack31 : ackermann 3 1 = 16 := rfl
  set r := invAckermann u
  have hu_le : u ≤ ackermann r 1 := (invAck_spec u).2.1
  have hr_not2 : ¬ (r ≤ 2) := by
    intro hr2
    have := (invAck_galois u 2 (by omega)).mp hr2
    rw [h_ack21] at this
    omega
  by_cases hr3 : r = 3
  · have hu16 : u ≤ 16 := by
      have := (invAck_galois u 3 (by omega)).mp (by omega)
      rw [h_ack31] at this
      exact this
    have hu6 : u ^ 6 ≤ 16 ^ 6 := Nat.pow_le_pow_left hu16 6
    have h1 : 2 ^ 20 * u ^ 6 ≤ 2 ^ 44 := by
      have h44 : 2 ^ 20 * 16 ^ 6 = 2 ^ 44 := by norm_num
      omega
    have h2 : 2 ^ 44 ≤ 2 ^ (2 ^ 6) :=
      Nat.pow_le_pow_right (by decide) (by decide)
    have h3 : 2 ^ (2 ^ 6) ≤ ackermann 2 6 := ack2_tower 6 (by decide)
    have h3' : ackermann 2 6 ≤ ackermann 2 16 := (ack_strictMono_j 2).monotone (by decide)
    obtain ⟨h41, _⟩ := ack4_eq_ack2_16_and_gt
    have hle4 : 2 ^ 20 * u ^ 6 ≤ ackermann 4 1 := by
      rw [h41]
      exact le_trans h1 (le_trans h2 (le_trans h3 h3'))
    have h5 : invAckermann (2 ^ 20 * u ^ 6) ≤ 4 :=
      (invAck_galois (2 ^ 20 * u ^ 6) 4 (by decide : 1 ≤ 4)).mpr hle4
    rw [hr3]
    exact h5
  · have hr4 : 4 ≤ r := by omega
    have hu17 : 17 ≤ u := by
      by_contra hlt
      have hu16 : u ≤ ackermann 3 1 := by rw [h_ack31]; omega
      have := (invAck_galois u 3 (by omega)).mpr hu16
      omega
    have hu_pow : u ≤ 2 ^ u := Nat.le_of_lt Nat.lt_two_pow_self
    have hu6 : 2 ^ 20 * u ^ 6 ≤ 2 ^ (20 + 6 * u) := by
      have hpow6 : u ^ 6 ≤ (2 ^ u) ^ 6 := Nat.pow_le_pow_left hu_pow 6
      have hmul := Nat.mul_le_mul_left (2 ^ 20) hpow6
      have hexp6 : 2 ^ 20 * (2 ^ u) ^ 6 = 2 ^ (20 + 6 * u) := by
        rw [← pow_mul, ← pow_add]; congr 1; omega
      omega
    have hlin : 20 + 6 * u ≤ 2 ^ u := by
      have hd := linear_le_pow17 (u - 17)
      have hsub : u - 17 + 17 = u := by omega
      rw [hsub] at hd
      exact hd
    have h_u_tower : 2 ^ 20 * u ^ 6 ≤ 2 ^ (2 ^ u) :=
      le_trans hu6 (Nat.pow_le_pow_right (by omega) hlin)
    have h_r_tower : 2 ^ (2 ^ u) ≤ 2 ^ (2 ^ (ackermann r 1)) :=
      Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hu_le)
    have h_ack2 : 2 ^ (2 ^ (ackermann r 1)) ≤ ackermann 2 (ackermann r 1) :=
      ack2_tower (ackermann r 1) (by omega)
    set m := r - 2
    have hm_eq : r = m + 2 := by omega
    have hm2 : 2 ≤ m + 1 := by omega
    have h_step_i : ackermann 2 (ackermann (m + 2) 1) ≤
        ackermann (m + 1) (ackermann (m + 2) 1) :=
      ack_mono_i (ackermann (m + 2) 1) (by rw [← hm_eq]; omega) hm2
    have h_def : ackermann (m + 1) (ackermann (m + 2) 1) = ackermann (m + 3) 1 := rfl
    have h_r1 : m + 3 = r + 1 := by omega
    have h_tot : 2 ^ 20 * u ^ 6 ≤ ackermann (r + 1) 1 := by
      rw [h_def, h_r1, ← hm_eq] at h_step_i
      exact le_trans h_u_tower (le_trans h_r_tower (le_trans h_ack2 h_step_i))
    exact (invAck_galois (2 ^ 20 * u ^ 6) (r + 1) (by omega)).mpr h_tot

private lemma alpha0_one : alpha0 1 = 1 := by
  have h1 : 1 ≤ alpha0 1 := (invAck_spec 1).1
  have h2 : alpha0 1 ≤ 1 := (invAck_galois 1 1 (by omega)).mpr (by decide)
  omega

private lemma alpha0_le_clog_and_logb (n : ℕ) (hn : 2 ≤ n) :
    alpha0 n ≤ Nat.clog 2 n ∧ (alpha0 n : ℝ) < Real.logb 2 (n : ℝ) + 1 := by
  set c := Nat.clog 2 n
  have hn_le_pow : n ≤ 2 ^ c := Nat.le_pow_clog (by omega) n
  have hc1 : 1 ≤ c := by
    by_contra hc0
    have hc_eq : c = 0 := by omega
    rw [hc_eq] at hn_le_pow
    omega
  have ha_le_c : alpha0 n ≤ c :=
    (invAck_galois n c hc1).mpr (le_trans hn_le_pow (ack_col1_exp c hc1))
  refine ⟨ha_le_c, ?_⟩
  have hpow_lt : 2 ^ (c - 1) < n := by
    by_contra hnot
    have hge : n ≤ 2 ^ (c - 1) := Nat.le_of_not_lt hnot
    have hle := (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).mpr hge
    change c ≤ c - 1 at hle
    omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h_rpow_lt : ((c - 1 : ℕ) : ℝ) < Real.logb 2 (n : ℝ) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) hn_pos, Real.rpow_natCast]
    exact_mod_cast hpow_lt
  have h_sub : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    have : (c - 1) + 1 = c := by omega
    have hcast : (((c - 1) + 1 : ℕ) : ℝ) = (c : ℝ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  have ha_R : (alpha0 n : ℝ) ≤ (c : ℝ) := by exact_mod_cast ha_le_c
  linarith

private lemma alpha0_plus1_iter :
    ∀ m u : ℕ, 1 ≤ m → 1 ≤ u →
      ((fun x : ℕ => alpha0 x + 1)^[m] u) ≤ (alpha0^[m] u) + 2 := by
  intro m u hm _hu
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have heq : 1 + (d + 1) = (1 + d) + 1 := by omega
    rw [heq, Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 : alpha0 ((fun x : ℕ => alpha0 x + 1)^[1 + d] u) ≤
        alpha0 ((alpha0^[1 + d] u) + 2) := invAck_mono ih
    have h2 : alpha0 ((alpha0^[1 + d] u) + 2) ≤ alpha0 (alpha0^[1 + d] u) + 1 :=
      invAck_shift (alpha0^[1 + d] u)
    omega


/-! ## 3. Parametric Star-Tower Hierarchy (`ackTower` and `diagTower`) -/

private lemma ackTower_zero_succ (m : ℕ) : ackTower 0 (m + 1) = ackermann (m + 1) 1 := by
  simp [ackTower]

private lemma ackTower_succ_one (r : ℕ) : ackTower (r + 1) 1 = 4 := by
  simp [ackTower]

private lemma ackTower_succ_add2 (r m : ℕ) :
    ackTower (r + 1) (m + 2) = ackTower r (ackTower (r + 1) (m + 1)) := by
  simp [ackTower]

private lemma ackTower_succ_step {r k : ℕ} (hk : 2 ≤ k) :
    ackTower (r + 1) k = ackTower r (ackTower (r + 1) (k - 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : 2 + m = m + 2 := by omega
  have h2 : 2 + m - 1 = m + 1 := by omega
  rw [h2, h1, ackTower_succ_add2]

private lemma starIterate_pos (f : ℕ → ℕ) (n : ℕ) : 1 ≤ starIterate f n := by
  rw [starIterate]
  split_ifs <;> omega

private lemma parametric_tower_props (F : ℕ → ℕ → ℕ)
    (hF0_1 : F 0 1 ≤ 4)
    (hF0_pow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ F 0 k)
    (hF0_strict : ∀ k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → F 0 k₁ < F 0 k₂)
    (hF_base1 : ∀ r : ℕ, F (r + 1) 1 = 4)
    (hF_step : ∀ r k : ℕ, F (r + 1) (k + 2) = F r (F (r + 1) (k + 1))) :
    (∀ r k : ℕ, 1 ≤ k → 2 ^ k ≤ F r k) ∧
    (∀ r k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → F r k₁ < F r k₂) ∧
    (∀ r₁ r₂ k : ℕ, r₁ ≤ r₂ → 1 ≤ k → F r₁ k ≤ F r₂ k) := by
  have h_pow_strict : ∀ r : ℕ,
      (∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ F r k) ∧
      (∀ k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → F r k₁ < F r k₂) := by
    intro r
    induction r with
    | zero => exact ⟨hF0_pow, hF0_strict⟩
    | succ r ihr =>
      rcases ihr with ⟨hr_pow, _⟩
      have h_adj : ∀ m : ℕ,
          2 ^ (m + 1) ≤ F (r + 1) (m + 1) ∧
          F (r + 1) (m + 1) < F (r + 1) (m + 2) := by
        intro m
        induction m with
        | zero =>
          have hb : F (r + 1) 1 = 4 := hF_base1 r
          have hs : F (r + 1) 2 = F r (F (r + 1) 1) := hF_step r 0
          have hp : 2 ^ 4 ≤ F r 4 := hr_pow 4 (by omega)
          rw [hb] at hs ⊢
          rw [hs]
          omega
        | succ m ihm =>
          have hpow1 : 2 ^ (m + 2) ≤ F (r + 1) (m + 2) := by
            have hs : F (r + 1) (m + 2) = F r (F (r + 1) (m + 1)) := hF_step r m
            rw [hs]
            have hlt : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
            have hx_ge : m + 2 ≤ F (r + 1) (m + 1) := by omega
            have hp : 2 ^ (F (r + 1) (m + 1)) ≤ F r (F (r + 1) (m + 1)) :=
              hr_pow _ (by omega)
            exact le_trans (Nat.pow_le_pow_right (by omega) hx_ge) hp
          have hlt2 : F (r + 1) (m + 2) < F (r + 1) (m + 3) := by
            have hs : F (r + 1) (m + 3) = F r (F (r + 1) (m + 2)) := hF_step r (m + 1)
            rw [hs]
            have hp : 2 ^ (F (r + 1) (m + 2)) ≤ F r (F (r + 1) (m + 2)) :=
              hr_pow _ (by have := Nat.one_le_two_pow (n := m + 2); omega)
            have hself : F (r + 1) (m + 2) < 2 ^ (F (r + 1) (m + 2)) := Nat.lt_two_pow_self
            omega
          exact ⟨hpow1, hlt2⟩
      refine ⟨?_, ?_⟩
      · intro k hk
        rcases k with _ | m
        · omega
        · exact (h_adj m).1
      · intro k₁ k₂ hk₁ hlt
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.add_one_le_iff.mpr hlt)
        clear hlt
        rcases k₁ with _ | m₁
        · omega
        · induction d with
          | zero =>
            simpa [Nat.add_assoc] using (h_adj m₁).2
          | succ d ihd =>
            have h1 : m₁ + 1 + 1 + d = (m₁ + 1 + d) + 1 := by omega
            have h2 : m₁ + 1 + 1 + (d + 1) = (m₁ + 1 + d) + 2 := by omega
            rw [h2]
            rw [h1] at ihd
            exact lt_trans ihd (h_adj (m₁ + 1 + d)).2
  have h_pow : ∀ r k : ℕ, 1 ≤ k → 2 ^ k ≤ F r k := fun r => (h_pow_strict r).1
  have h_strict : ∀ r k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → F r k₁ < F r k₂ :=
    fun r => (h_pow_strict r).2
  have h_mono_k : ∀ r k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ ≤ k₂ → F r k₁ ≤ F r k₂ := by
    intro r k₁ k₂ hk₁ hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (h_strict r k₁ k₂ hk₁ hlt)
  have h_step_r : ∀ r k : ℕ, 1 ≤ k → F r k ≤ F (r + 1) k := by
    intro r k hk
    rcases k with _ | _ | m
    · omega
    · rcases r with _ | s
      · rw [hF_base1 0]; exact hF0_1
      · rw [hF_base1 s, hF_base1 (s + 1)]
    · rw [hF_step r m]
      have hx : m + 2 ≤ F (r + 1) (m + 1) := by
        rcases m with _ | m'
        · rw [hF_base1 r]; omega
        · have hp : 2 ^ (m' + 2) ≤ F (r + 1) (m' + 1 + 1) := h_pow (r + 1) (m' + 2) (by omega)
          have hlt : m' + 2 < 2 ^ (m' + 2) := Nat.lt_two_pow_self
          omega
      exact h_mono_k r (m + 2) (F (r + 1) (m + 1)) (by omega) hx
  refine ⟨h_pow, h_strict, ?_⟩
  intro r₁ r₂ k hle hk
  exact monotone_nat_of_le_succ (fun r => h_step_r r k hk) hle

private lemma parametric_star_galois (f F : ℕ → ℕ → ℕ)
    (hF0_1 : F 0 1 ≤ 4)
    (hF0_pow : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ F 0 k)
    (hF0_strict : ∀ k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → F 0 k₁ < F 0 k₂)
    (hF_base1 : ∀ r : ℕ, F (r + 1) 1 = 4)
    (hF_step : ∀ r k : ℕ, F (r + 1) (k + 2) = F r (F (r + 1) (k + 1)))
    (hf_succ : ∀ r : ℕ, f (r + 1) = starIterate (f r))
    (hf0_pos : ∀ n : ℕ, 1 ≤ n → 1 ≤ f 0 n)
    (hf0_lt : ∀ n : ℕ, 4 < n → f 0 n < n)
    (hf0_galois : ∀ k n : ℕ, 1 ≤ k → 1 ≤ n → (f 0 n ≤ k ↔ n ≤ F 0 k)) :
    ∀ r : ℕ,
      (∀ n : ℕ, 1 ≤ n → 1 ≤ f r n) ∧
      (∀ n : ℕ, 4 < n → f r n < n) ∧
      (∀ k n : ℕ, 1 ≤ k → 1 ≤ n → (f r n ≤ k ↔ n ≤ F r k)) ∧
      (∀ m n : ℕ, 1 ≤ m → m ≤ n → f r m ≤ f r n) := by
  obtain ⟨hF_pow, hF_strict, _⟩ :=
    parametric_tower_props F hF0_1 hF0_pow hF0_strict hF_base1 hF_step
  have hF_mono_k : ∀ r k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ ≤ k₂ → F r k₁ ≤ F r k₂ := by
    intro r k₁ k₂ hk₁ hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (hF_strict r k₁ k₂ hk₁ hlt)
  intro r
  induction r with
  | zero =>
    refine ⟨hf0_pos, hf0_lt, hf0_galois, ?_⟩
    intro m n hm hmn
    have hk1 : 1 ≤ f 0 n := hf0_pos n (by omega)
    have hn_le : n ≤ F 0 (f 0 n) := (hf0_galois (f 0 n) n hk1 (by omega)).mp le_rfl
    exact (hf0_galois (f 0 n) m hk1 hm).mpr (le_trans hmn hn_le)
  | succ r ihr =>
    rcases ihr with ⟨hr_pos, hr_lt, hr_galois, _⟩
    have h_pos : ∀ n : ℕ, 1 ≤ n → 1 ≤ f (r + 1) n := by
      intro n _
      rw [hf_succ r]
      exact starIterate_pos (f r) n
    have h_galois : ∀ k n : ℕ, 1 ≤ k → 1 ≤ n → (f (r + 1) n ≤ k ↔ n ≤ F (r + 1) k) := by
      intro k
      rcases k with _ | k'
      · intro _ hk; omega
      · induction k' with
        | zero =>
          intro n _ hn
          rw [hf_succ r, starIterate, hF_base1 r]
          by_cases h4 : n ≤ 4
          · simp [h4]
          · have hgt4 : 4 < n := by omega
            have hlt_n : f r n < n := hr_lt n hgt4
            have hpos_sub : 1 ≤ starIterate (f r) (f r n) := starIterate_pos (f r) (f r n)
            simp [h4, hlt_n]
            omega
        | succ m ihm =>
          intro n _ hn
          by_cases h4 : n ≤ 4
          · have hval : f (r + 1) n = 1 := by rw [hf_succ r, starIterate]; simp [h4]
            have hF_ge4 : 4 ≤ F (r + 1) (m + 1 + 1) := by
              rw [← hF_base1 r]
              exact hF_mono_k (r + 1) 1 (m + 2) (by omega) (by omega)
            omega
          · rw [hF_step r m]
            have hgt4 : 4 < n := by omega
            have hlt_n : f r n < n := hr_lt n hgt4
            have hstep_val : f (r + 1) n = 1 + f (r + 1) (f r n) := by
              rw [hf_succ r]
              conv_lhs => rw [starIterate]
              simp [h4, hlt_n]
            have hfn_pos : 1 ≤ f r n := hr_pos n hn
            have hFk_pos : 1 ≤ F (r + 1) (m + 1) := by
              have hp := hF_pow (r + 1) (m + 1) (by omega)
              have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
              omega
            rw [hstep_val]
            have h1 : 1 + f (r + 1) (f r n) ≤ m + 2 ↔ f (r + 1) (f r n) ≤ m + 1 := by omega
            rw [h1, ihm (f r n) (by omega) hfn_pos, hr_galois (F (r + 1) (m + 1)) n hFk_pos hn]
    have h_lt : ∀ n : ℕ, 4 < n → f (r + 1) n < n := by
      intro n hn
      have hpow : n ≤ 2 ^ (n - 1) := self_le_two_pow_pred n (by omega)
      have hF : 2 ^ (n - 1) ≤ F (r + 1) (n - 1) := hF_pow (r + 1) (n - 1) (by omega)
      have hle : f (r + 1) n ≤ n - 1 :=
        (h_galois (n - 1) n (by omega) (by omega)).mpr (le_trans hpow hF)
      omega
    have h_mono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → f (r + 1) m ≤ f (r + 1) n := by
      intro m n hm hmn
      have hk1 : 1 ≤ f (r + 1) n := h_pos n (by omega)
      have hn_le : n ≤ F (r + 1) (f (r + 1) n) :=
        (h_galois (f (r + 1) n) n hk1 (by omega)).mp le_rfl
      exact (h_galois (f (r + 1) n) m hk1 hm).mpr (le_trans hmn hn_le)
    exact ⟨h_pos, h_lt, h_galois, h_mono⟩


/-! ## 4. Instantiating `ackTower`, `alphaHierarchy`, and `alphaOmega` (`lem_A_1_ack_basic`) -/

private lemma ackTower_all_props :
    (∀ r k : ℕ, 1 ≤ k → 2 ^ k ≤ ackTower r k) ∧
    (∀ r k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → ackTower r k₁ < ackTower r k₂) ∧
    (∀ r₁ r₂ k : ℕ, r₁ ≤ r₂ → 1 ≤ k → ackTower r₁ k ≤ ackTower r₂ k) := by
  apply parametric_tower_props ackTower
  · rw [ackTower_zero_succ 0]; change 2 ≤ 4; omega
  · intro k hk
    rcases k with _ | m
    · omega
    · rw [ackTower_zero_succ]; exact ack_col1_exp (m + 1) (by omega)
  · intro k₁ k₂ hk₁ hlt
    rcases k₁ with _ | m₁
    · omega
    · rcases k₂ with _ | m₂
      · omega
      · rw [ackTower_zero_succ, ackTower_zero_succ]
        exact ack_col1_strictMono (m₁ + 1) (m₂ + 1) (by omega) hlt
  · exact ackTower_succ_one
  · exact ackTower_succ_add2

private lemma ackTower_mono_k {r k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hle : k₁ ≤ k₂) :
    ackTower r k₁ ≤ ackTower r k₂ := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (ackTower_all_props.2.1 r k₁ k₂ hk₁ hlt)

private lemma alphaHierarchy_all_props :
    ∀ r : ℕ,
      (∀ n : ℕ, 1 ≤ n → 1 ≤ alphaHierarchy r n) ∧
      (∀ n : ℕ, 4 < n → alphaHierarchy r n < n) ∧
      (∀ k n : ℕ, 1 ≤ k → 1 ≤ n → (alphaHierarchy r n ≤ k ↔ n ≤ ackTower r k)) ∧
      (∀ m n : ℕ, 1 ≤ m → m ≤ n → alphaHierarchy r m ≤ alphaHierarchy r n) := by
  apply parametric_star_galois alphaHierarchy ackTower
  · rw [ackTower_zero_succ 0]; change 2 ≤ 4; omega
  · intro k hk
    rcases k with _ | m
    · omega
    · rw [ackTower_zero_succ]; exact ack_col1_exp (m + 1) (by omega)
  · intro k₁ k₂ hk₁ hlt
    rcases k₁ with _ | m₁
    · omega
    · rcases k₂ with _ | m₂
      · omega
      · rw [ackTower_zero_succ, ackTower_zero_succ]
        exact ack_col1_strictMono (m₁ + 1) (m₂ + 1) (by omega) hlt
  · exact ackTower_succ_one
  · exact ackTower_succ_add2
  · intro r; rfl
  · intro n _; exact (invAck_spec n).1
  · intro n hn; exact invAck_lt n (by omega)
  · intro k n hk _
    rcases k with _ | m
    · omega
    · rw [ackTower_zero_succ]; exact invAck_galois n (m + 1) (by omega)

private lemma alpha1_double_le (n : ℕ) (hn : 1 ≤ n) :
    alphaHierarchy 1 (2 * n) ≤ alphaHierarchy 1 n + 1 := by
  set k := alphaHierarchy 1 n
  have hk1 : 1 ≤ k := (alphaHierarchy_all_props 1).1 n hn
  have hn_le : n ≤ ackTower 1 k := ((alphaHierarchy_all_props 1).2.2.1 k n hk1 hn).mp le_rfl
  have hFk_ge4 : 4 ≤ ackTower 1 k := by
    have h4 : ackTower 1 1 = 4 := ackTower_succ_one 0
    rw [← h4]
    exact ackTower_mono_k (by omega) hk1
  have hstep : ackTower 1 (k + 1) = ackTower 0 (ackTower 1 k) := by
    simpa using ackTower_succ_step (r := 0) (k := k + 1) (by omega)
  have h0_pow : 2 ^ (ackTower 1 k) ≤ ackTower 0 (ackTower 1 k) :=
    ackTower_all_props.1 0 (ackTower 1 k) (by omega)
  have h2mul : 2 * ackTower 1 k ≤ 2 ^ (ackTower 1 k) :=
    two_mul_le_two_pow (ackTower 1 k) (by omega)
  have h2n_le : 2 * n ≤ ackTower 1 (k + 1) := by omega
  exact ((alphaHierarchy_all_props 1).2.2.1 (k + 1) (2 * n) (by omega) (by omega)).mpr h2n_le

private lemma alpha1_log_log_bounds (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    alphaHierarchy r n ≤ alphaHierarchy 1 n ∧
    alphaHierarchy 1 n ≤ Nat.log 2 (Nat.log 2 (n + 16)) + 2 ∧
    (alphaHierarchy 1 n : ℝ) ≤ Real.logb 2 (Real.logb 2 ((n : ℝ) + 16)) + 2 := by
  have hr_le_1 : alphaHierarchy r n ≤ alphaHierarchy 1 n := by
    set k := alphaHierarchy 1 n
    have hk1 : 1 ≤ k := (alphaHierarchy_all_props 1).1 n hn
    have hn_le : n ≤ ackTower 1 k := ((alphaHierarchy_all_props 1).2.2.1 k n hk1 hn).mp le_rfl
    have hF_le : ackTower 1 k ≤ ackTower r k := ackTower_all_props.2.2 1 r k hr hk1
    exact ((alphaHierarchy_all_props r).2.2.1 k n hk1 hn).mpr (le_trans hn_le hF_le)
  have ha1_nat : alphaHierarchy 1 n ≤ Nat.log 2 (Nat.log 2 (n + 16)) + 2 := by
    set k := alphaHierarchy 1 n
    by_cases hk2 : k ≤ 2
    · omega
    · have hk3 : 3 ≤ k := by omega
      have hnot : ¬ (n ≤ ackTower 1 (k - 1)) := fun hle => by
        have := ((alphaHierarchy_all_props 1).2.2.1 (k - 1) n (by omega) hn).mpr hle
        omega
      set m := ackTower 1 (k - 2)
      have hm_ge4 : 4 ≤ m := by
        have h4 : ackTower 1 1 = 4 := ackTower_succ_one 0
        rw [← h4]
        exact ackTower_mono_k (by omega) (by omega)
      have hm_ge_k2 : k - 2 ≤ m := by
        have hp := ackTower_all_props.1 1 (k - 2) (by omega)
        have hlt : k - 2 < 2 ^ (k - 2) := Nat.lt_two_pow_self
        omega
      have hstep : ackTower 1 (k - 1) = ackermann m 1 := by
        have hs := ackTower_succ_step (r := 0) (k := k - 1) (by omega)
        have hsub : k - 1 - 1 = k - 2 := by omega
        rw [hsub] at hs
        rw [hs]
        change ackTower 0 m = ackermann m 1
        rcases hm_eq : m with _ | m'
        · omega
        · exact ackTower_zero_succ m'
      have hdexp : 2 ^ (2 ^ m) ≤ ackermann m 1 := ack_col1_double_exp m hm_ge4
      have htower_lt : 2 ^ (2 ^ (k - 2)) ≤ n + 16 := by
        have hmono_pow : 2 ^ (2 ^ (k - 2)) ≤ 2 ^ (2 ^ m) :=
          Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hm_ge_k2)
        omega
      have hlog1 : 2 ^ (k - 2) ≤ Nat.log 2 (n + 16) :=
        Nat.le_log_of_pow_le (by omega) htower_lt
      have hlog2 : k - 2 ≤ Nat.log 2 (Nat.log 2 (n + 16)) :=
        Nat.le_log_of_pow_le (by omega) hlog1
      omega
  have ha1_real : (alphaHierarchy 1 n : ℝ) ≤ Real.logb 2 (Real.logb 2 ((n : ℝ) + 16)) + 2 := by
    have hlog1_ge4 : 4 ≤ Nat.log 2 (n + 16) :=
      Nat.le_log_of_pow_le (by omega) (show 2 ^ 4 ≤ n + 16 by omega)
    have h1 : (Nat.log 2 (n + 16) : ℝ) ≤ Real.logb 2 ((n : ℝ) + 16) := by
      apply cast_nat_log_le_logb (n + 16) ((n : ℝ) + 16) (by omega)
      push_cast; linarith
    have h2 : (Nat.log 2 (Nat.log 2 (n + 16)) : ℝ) ≤
        Real.logb 2 (Real.logb 2 ((n : ℝ) + 16)) :=
      cast_nat_log_le_logb (Nat.log 2 (n + 16)) (Real.logb 2 ((n : ℝ) + 16)) (by omega) h1
    have hnat_R : (alphaHierarchy 1 n : ℝ) ≤ (Nat.log 2 (Nat.log 2 (n + 16)) : ℝ) + 2 := by
      exact_mod_cast ha1_nat
    linarith
  exact ⟨hr_le_1, ha1_nat, ha1_real⟩

private lemma alphaOmega_eq_sInf_tower (n : ℕ) (hn : 1 ≤ n) :
    alphaOmega n = sInf {r : ℕ | 1 ≤ r ∧ n ≤ ackTower r 2} := by
  unfold alphaOmega
  congr 1
  ext r
  constructor
  · rintro ⟨hr, hle⟩
    exact ⟨hr, ((alphaHierarchy_all_props r).2.2.1 2 n (by omega) hn).mp hle⟩
  · rintro ⟨hr, hle⟩
    exact ⟨hr, ((alphaHierarchy_all_props r).2.2.1 2 n (by omega) hn).mpr hle⟩

/-- **Lemma A.1** (`lem:ack-basic`, Elementary Ackermann and Iterated-Inverse Estimates):
All subclaims of Parts (1), (2), and (3) on `A_i`, `α_0`, `F_r`, `α_r`, and `α_ω`. -/
theorem lem_A_1_ack_basic :
    -- Part (1)
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
    -- Part (2)
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
    -- Part (3)
    ((∀ n : ℕ, 1 ≤ n → alpha0 (n + 2) ≤ alpha0 n + 1) ∧
     (∀ m u : ℕ, 1 ≤ m → 1 ≤ u →
       ((fun x : ℕ => alpha0 x + 1)^[m] u) ≤ (alpha0^[m] u) + 2) ∧
     (∀ u : ℕ, 5 ≤ u → alpha0 (2 ^ 20 * u ^ 6) ≤ alpha0 u + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ack_col1_exp, ?_, alpha0_one, alpha0_le_clog_and_logb, ?_⟩
    · intro i j hj; have := ack_ge_two_mul i j hj; omega
    · intro i j₁ j₂ _ hlt; exact ack_strictMono_j i hlt
    · intro i j hi hj
      refine ⟨?_, ?_⟩
      · have heq : (i - 1) + 1 = i := by omega
        simpa [heq] using ack_mono_i_step (i - 1) j hj
      · simpa [ackermann] using ack_mono_i j hj hi
    · intro m n _ hmn; exact invAck_mono hmn
    · intro n hn; exact invAck_lt n (by omega)
  · refine ⟨ackTower_all_props.1, ackTower_all_props.2.1, ?_, ?_, ?_, ?_,
      alpha1_double_le, alpha1_log_log_bounds, alphaOmega_eq_sInf_tower⟩
    · intro r₁ r₂ k _ hr hk; exact ackTower_all_props.2.2 r₁ r₂ k hr hk
    · intro r m n _ hm hmn; exact (alphaHierarchy_all_props r).2.2.2 m n hm hmn
    · intro r n _ hn; exact (alphaHierarchy_all_props r).2.1 n hn
    · intro r k n _ hk hn; exact (alphaHierarchy_all_props r).2.2.1 k n hk hn
  · refine ⟨fun n _ => invAck_shift n, alpha0_plus1_iter, invAck_poly⟩


/-! ## 5. Level-`ω` Properties and Diagonal Convention Invariance (`prop_1_3_omega_properties`) -/

private lemma ackTower_succ_two (s : ℕ) : ackTower (s + 1) 2 = ackTower s 4 := by
  rw [ackTower_succ_add2 s 0, ackTower_succ_one s]

private lemma ackTower_two_gt_pow : ∀ t : ℕ, 1 ≤ t → 2 ^ (t + 2) < ackTower t 2 := by
  intro t ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction d with
  | zero =>
    have heq : ackTower 1 2 = ackermann 4 1 := by
      rw [ackTower_succ_two 0, ackTower_zero_succ 3]
    have h16 : 2 ^ 4 ≤ ackermann 4 1 := ack_col1_exp 4 (by decide)
    simp only [Nat.add_zero]
    rw [heq]
    omega
  | succ d ih =>
    set s := 1 + d
    have h_s3 : 2 ^ (ackTower s 2) ≤ ackTower s 3 := by
      have heq : ackTower s 3 = ackTower d (ackTower s 2) := by
        have hs1 : s = d + 1 := by omega
        rw [hs1, ackTower_succ_add2 d 1]
      have hs0 : s - 1 = d := by omega
      rw [heq, ← hs0]
      exact ackTower_all_props.1 (s - 1) (ackTower s 2)
        (by have := Nat.one_le_two_pow (n := s + 2); omega)
    have h_s4 : ackTower s 3 < ackTower (s + 1) 2 := by
      rw [ackTower_succ_two s]
      exact ackTower_all_props.2.1 s 3 4 (by omega) (by omega)
    have hexp_le : s + 1 + 2 ≤ ackTower s 2 := by
      have hlt : s + 2 < 2 ^ (s + 2) := Nat.lt_two_pow_self
      omega
    have hpow_le : 2 ^ (s + 1 + 2) ≤ 2 ^ (ackTower s 2) :=
      Nat.pow_le_pow_right (by omega) hexp_le
    have hidx : 1 + (d + 1) = s + 1 := by omega
    rw [hidx]
    omega

private lemma alphaOmega_nonempty (n : ℕ) (hn : 1 ≤ n) :
    {r : ℕ | 1 ≤ r ∧ n ≤ ackTower r 2}.Nonempty := by
  refine ⟨n, hn, ?_⟩
  have h1 : n < 2 ^ (n + 2) := lt_trans Nat.lt_two_pow_self
    (Nat.pow_lt_pow_right (by omega) (by omega))
  exact le_of_lt (lt_trans h1 (ackTower_two_gt_pow n hn))

private lemma alphaOmega_pos_and_galois (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ alphaOmega n ∧
    (∀ r : ℕ, 1 ≤ r → (alphaOmega n ≤ r ↔ n ≤ ackTower r 2)) := by
  rw [alphaOmega_eq_sInf_tower n hn]
  have hmem := Nat.sInf_mem (alphaOmega_nonempty n hn)
  refine ⟨hmem.1, ?_⟩
  intro r hr
  constructor
  · intro hle
    exact le_trans hmem.2 (ackTower_all_props.2.2 _ r 2 hle (by omega))
  · intro hle
    exact Nat.sInf_le ⟨hr, hle⟩

private def diagTower : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, k + 1 => ackermann (k + 1) (k + 1)
  | _ + 1, 0 => 1
  | _ + 1, 1 => 4
  | r + 1, k + 2 => diagTower r (diagTower (r + 1) (k + 1))

private lemma diagTower_zero_succ (m : ℕ) : diagTower 0 (m + 1) = ackermann (m + 1) (m + 1) := by
  simp [diagTower]

private lemma diagTower_succ_one (r : ℕ) : diagTower (r + 1) 1 = 4 := by
  simp [diagTower]

private lemma diagTower_succ_add2 (r m : ℕ) :
    diagTower (r + 1) (m + 2) = diagTower r (diagTower (r + 1) (m + 1)) := by
  simp [diagTower]

private lemma diag0_strictMono :
    ∀ k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → ackermann k₁ k₁ < ackermann k₂ k₂ := by
  intro k₁ k₂ hk₁ hlt
  have h1 : ackermann k₁ k₁ ≤ ackermann k₂ k₁ := ack_mono_i k₁ hk₁ (le_of_lt hlt)
  have h2 : ackermann k₂ k₁ < ackermann k₂ k₂ := ack_strictMono_j k₂ hlt
  exact lt_of_le_of_lt h1 h2

private lemma alphaDiag0_props :
    (∀ n : ℕ, 1 ≤ alphaDiag0 n) ∧
    (∀ k n : ℕ, 1 ≤ k → (alphaDiag0 n ≤ k ↔ n ≤ ackermann k k)) ∧
    (∀ n : ℕ, 4 < n → alphaDiag0 n < n) := by
  have hne : ∀ n : ℕ, {k : ℕ | 1 ≤ k ∧ n ≤ ackermann k k}.Nonempty := by
    intro n
    obtain ⟨k, hk1, hnk⟩ := invAck_nonempty n
    exact ⟨k, hk1, le_trans hnk ((ack_strictMono_j k).monotone hk1)⟩
  have hpos : ∀ n : ℕ, 1 ≤ alphaDiag0 n := fun n => (Nat.sInf_mem (hne n)).1
  have hgal : ∀ k n : ℕ, 1 ≤ k → (alphaDiag0 n ≤ k ↔ n ≤ ackermann k k) := by
    intro k n hk
    constructor
    · intro hle
      have hmem := Nat.sInf_mem (hne n)
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact hmem.2
      · exact le_trans hmem.2 (le_of_lt (diag0_strictMono _ k hmem.1 hlt))
    · intro hle
      exact Nat.sInf_le ⟨hk, hle⟩
  have hlt : ∀ n : ℕ, 4 < n → alphaDiag0 n < n := by
    intro n hn
    have hle0 : alphaDiag0 n ≤ alpha0 n := by
      have hk1 : 1 ≤ alpha0 n := (invAck_spec n).1
      have hn_le : n ≤ ackermann (alpha0 n) 1 := (invAck_spec n).2.1
      exact (hgal (alpha0 n) n hk1).mpr
        (le_trans hn_le ((ack_strictMono_j (alpha0 n)).monotone hk1))
    exact lt_of_le_of_lt hle0 (invAck_lt n (by omega))
  exact ⟨hpos, hgal, hlt⟩

private lemma diagTower_all_props :
    (∀ r k : ℕ, 1 ≤ k → 2 ^ k ≤ diagTower r k) ∧
    (∀ r k₁ k₂ : ℕ, 1 ≤ k₁ → k₁ < k₂ → diagTower r k₁ < diagTower r k₂) ∧
    (∀ r₁ r₂ k : ℕ, r₁ ≤ r₂ → 1 ≤ k → diagTower r₁ k ≤ diagTower r₂ k) := by
  apply parametric_tower_props diagTower
  · rw [diagTower_zero_succ 0]; change 2 ≤ 4; omega
  · intro k hk
    rcases k with _ | m
    · omega
    · rw [diagTower_zero_succ]
      exact le_trans (ack_col1_exp (m + 1) (by omega))
        ((ack_strictMono_j (m + 1)).monotone (by omega))
  · intro k₁ k₂ hk₁ hlt
    rcases k₁ with _ | m₁
    · omega
    · rcases k₂ with _ | m₂
      · omega
      · rw [diagTower_zero_succ, diagTower_zero_succ]
        exact diag0_strictMono (m₁ + 1) (m₂ + 1) (by omega) hlt
  · exact diagTower_succ_one
  · exact diagTower_succ_add2

private lemma alphaDiagHierarchy_all_props :
    ∀ r : ℕ,
      (∀ n : ℕ, 1 ≤ n → 1 ≤ alphaDiagHierarchy r n) ∧
      (∀ n : ℕ, 4 < n → alphaDiagHierarchy r n < n) ∧
      (∀ k n : ℕ, 1 ≤ k → 1 ≤ n → (alphaDiagHierarchy r n ≤ k ↔ n ≤ diagTower r k)) ∧
      (∀ m n : ℕ, 1 ≤ m → m ≤ n → alphaDiagHierarchy r m ≤ alphaDiagHierarchy r n) := by
  apply parametric_star_galois alphaDiagHierarchy diagTower
  · rw [diagTower_zero_succ 0]; change 2 ≤ 4; omega
  · intro k hk
    rcases k with _ | m
    · omega
    · rw [diagTower_zero_succ]
      exact le_trans (ack_col1_exp (m + 1) (by omega))
        ((ack_strictMono_j (m + 1)).monotone (by omega))
  · intro k₁ k₂ hk₁ hlt
    rcases k₁ with _ | m₁
    · omega
    · rcases k₂ with _ | m₂
      · omega
      · rw [diagTower_zero_succ, diagTower_zero_succ]
        exact diag0_strictMono (m₁ + 1) (m₂ + 1) (by omega) hlt
  · exact diagTower_succ_one
  · exact diagTower_succ_add2
  · intro r; rfl
  · intro n _; exact alphaDiag0_props.1 n
  · exact alphaDiag0_props.2.2
  · intro k n hk _
    rcases k with _ | m
    · omega
    · rw [diagTower_zero_succ]; exact alphaDiag0_props.2.1 (m + 1) n (by omega)

private lemma ackTower_le_diagTower :
    ∀ r k : ℕ, 1 ≤ k → ackTower r k ≤ diagTower r k := by
  intro r
  induction r with
  | zero =>
    intro k hk
    rcases k with _ | m
    · omega
    · rw [ackTower_zero_succ, diagTower_zero_succ]
      exact (ack_strictMono_j (m + 1)).monotone (by omega)
  | succ r ihr =>
    intro k hk
    rcases k with _ | m
    · omega
    · clear hk
      induction m with
      | zero =>
        simp only [Nat.zero_add, ackTower_succ_one, diagTower_succ_one, le_rfl]
      | succ m ihm =>
        rw [ackTower_succ_add2, diagTower_succ_add2]
        have hpos : 1 ≤ ackTower (r + 1) (m + 1) := by
          have := ackTower_all_props.1 (r + 1) (m + 1) (by omega)
          have := Nat.one_le_two_pow (n := m + 1)
          omega
        calc ackTower r (ackTower (r + 1) (m + 1))
            ≤ diagTower r (ackTower (r + 1) (m + 1)) := ihr _ hpos
          _ ≤ diagTower r (diagTower (r + 1) (m + 1)) := by
              rcases eq_or_lt_of_le ihm with heq | hlt
              · rw [heq]
              · exact le_of_lt (diagTower_all_props.2.1 r _ _ hpos hlt)

private lemma diagTower0_le_ackTower0 :
    ∀ k : ℕ, 1 ≤ k → diagTower 0 k ≤ ackTower 0 (k + 2) := by
  intro k hk
  rcases k with _ | m
  · omega
  · rw [diagTower_zero_succ, ackTower_zero_succ (m + 2)]
    have hlt : m + 1 < ackermann (m + 2) 1 := by
      have hexp := ack_col1_exp (m + 2) (by omega)
      have hp : m + 2 < 2 ^ (m + 2) := Nat.lt_two_pow_self
      omega
    have h1 : ackermann (m + 1) (m + 1) < ackermann (m + 1) (ackermann (m + 2) 1) :=
      ack_strictMono_j (m + 1) hlt
    have h2 : ackermann (m + 1) (ackermann (m + 2) 1) = ackermann (m + 3) 1 := by
      calc ackermann (m + 1) (ackermann (m + 2) 1)
          = ackermann (m + 2) 2 := (ack_step_succ (by omega) (by omega)).symm
        _ = ackermann (m + 3) 1 := (ack_step_col1 (by omega)).symm
    rw [h2] at h1
    exact le_of_lt h1

private lemma diagTower_le_ackTower :
    ∀ r' k : ℕ, 1 ≤ k → diagTower (r' + 1) k ≤ ackTower (r' + 1) (2 * k - 1) := by
  intro r'
  induction r' with
  | zero =>
    simp only [Nat.zero_add]
    intro k hk
    rcases k with _ | m
    · omega
    · clear hk
      induction m with
      | zero =>
        simp [diagTower_succ_one, ackTower_succ_one]
      | succ m ihm =>
        set M := ackTower 1 (2 * (m + 1) - 1)
        have hM_ge4 : 4 ≤ M := by
          have h4 : ackTower 1 1 = 4 := ackTower_succ_one 0
          rw [← h4]
          exact ackTower_mono_k (by omega) (by omega)
        have hd_pos : 1 ≤ diagTower 1 (m + 1) := by
          have := diagTower_all_props.1 1 (m + 1) (by omega)
          have := Nat.one_le_two_pow (n := m + 1)
          omega
        have hF_even : 2 ^ M ≤ ackTower 1 (2 * (m + 1)) := by
          have heq : ackTower 1 (2 * (m + 1)) = ackTower 0 M := by
            have hs := ackTower_succ_step (r := 0) (k := 2 * (m + 1)) (by omega)
            have hsub : 2 * (m + 1) - 1 = 2 * (m + 1) - 1 := rfl
            exact hs
          rw [heq]
          exact ackTower_all_props.1 0 M (by omega)
        have hM2_le : diagTower 1 (m + 1) + 2 ≤ ackTower 1 (2 * (m + 1)) := by
          have h2M : 2 * M ≤ 2 ^ M := two_mul_le_two_pow M (by omega)
          omega
        have hstep_d : diagTower 1 (m + 2) = diagTower 0 (diagTower 1 (m + 1)) :=
          diagTower_succ_add2 0 m
        have hstep_F : ackTower 1 (2 * (m + 2) - 1) = ackTower 0 (ackTower 1 (2 * (m + 1))) := by
          have hs := ackTower_succ_step (r := 0) (k := 2 * (m + 2) - 1) (by omega)
          have hsub : 2 * (m + 2) - 1 - 1 = 2 * (m + 1) := by omega
          rwa [hsub] at hs
        rw [hstep_d, hstep_F]
        exact le_trans (diagTower0_le_ackTower0 _ hd_pos) (ackTower_mono_k (by omega) hM2_le)
  | succ s ihs =>
    have hs2 : s + 1 + 1 = s + 2 := rfl
    rw [hs2]
    intro k hk
    rcases k with _ | m
    · omega
    · clear hk
      induction m with
      | zero =>
        simp [diagTower_succ_one, ackTower_succ_one]
      | succ m ihm =>
        set M := ackTower (s + 2) (2 * (m + 1) - 1)
        have hM_ge4 : 4 ≤ M := by
          have h4 : ackTower (s + 2) 1 = 4 := ackTower_succ_one (s + 1)
          rw [← h4]
          exact ackTower_mono_k (by omega) (by omega)
        have hd_pos : 1 ≤ diagTower (s + 2) (m + 1) := by
          have := diagTower_all_props.1 (s + 2) (m + 1) (by omega)
          have := Nat.one_le_two_pow (n := m + 1)
          omega
        have hF_even : 2 ^ M ≤ ackTower (s + 2) (2 * (m + 1)) := by
          have heq : ackTower (s + 2) (2 * (m + 1)) = ackTower (s + 1) M :=
            ackTower_succ_step (r := s + 1) (k := 2 * (m + 1)) (by omega)
          rw [heq]
          exact ackTower_all_props.1 (s + 1) M (by omega)
        have h2M1_le : 2 * diagTower (s + 2) (m + 1) - 1 ≤ ackTower (s + 2) (2 * (m + 1)) := by
          have h2M : 2 * M ≤ 2 ^ M := two_mul_le_two_pow M (by omega)
          omega
        have hstep_d : diagTower (s + 2) (m + 2) =
            diagTower (s + 1) (diagTower (s + 2) (m + 1)) := diagTower_succ_add2 (s + 1) m
        have hstep_F : ackTower (s + 2) (2 * (m + 2) - 1) =
            ackTower (s + 1) (ackTower (s + 2) (2 * (m + 1))) := by
          have hs := ackTower_succ_step (r := s + 1) (k := 2 * (m + 2) - 1) (by omega)
          have hsub : 2 * (m + 2) - 1 - 1 = 2 * (m + 1) := by omega
          rwa [hsub] at hs
        rw [hstep_d, hstep_F]
        exact le_trans (ihs _ hd_pos) (ackTower_mono_k (by omega) h2M1_le)

private lemma alphaOmegaDiag_comparison (n : ℕ) (hn : 1 ≤ n) :
    alphaOmegaDiag n ≤ alphaOmega n + 1 ∧ alphaOmega n ≤ alphaOmegaDiag n + 2 := by
  have hdiag_set :
      {r : ℕ | 1 ≤ r ∧ alphaDiagHierarchy r n ≤ r} =
      {r : ℕ | 1 ≤ r ∧ n ≤ diagTower r r} := by
    ext r
    constructor
    · rintro ⟨hr, hle⟩
      exact ⟨hr, ((alphaDiagHierarchy_all_props r).2.2.1 r n hr hn).mp hle⟩
    · rintro ⟨hr, hle⟩
      exact ⟨hr, ((alphaDiagHierarchy_all_props r).2.2.1 r n hr hn).mpr hle⟩
  have hdiag_ne : {r : ℕ | 1 ≤ r ∧ n ≤ diagTower r r}.Nonempty := by
    refine ⟨n, hn, ?_⟩
    have hp := diagTower_all_props.1 n n hn
    have hlt : n < 2 ^ n := Nat.lt_two_pow_self
    omega
  have hdiag_eq : alphaOmegaDiag n = sInf {r : ℕ | 1 ≤ r ∧ n ≤ diagTower r r} := by
    unfold alphaOmegaDiag
    rw [hdiag_set]
  obtain ⟨h_om_pos, h_om_gal⟩ := alphaOmega_pos_and_galois n hn
  refine ⟨?_, ?_⟩
  · set r := alphaOmega n
    have hn_le : n ≤ ackTower r 2 := (h_om_gal r h_om_pos).mp le_rfl
    have h1 : ackTower r 2 ≤ ackTower (r + 1) 2 :=
      ackTower_all_props.2.2 r (r + 1) 2 (by omega) (by omega)
    have h2 : ackTower (r + 1) 2 ≤ diagTower (r + 1) 2 :=
      ackTower_le_diagTower (r + 1) 2 (by omega)
    have h3 : diagTower (r + 1) 2 ≤ diagTower (r + 1) (r + 1) := by
      rcases eq_or_lt_of_le (show 2 ≤ r + 1 by omega) with heq | hlt
      · rw [heq]
      · exact le_of_lt (diagTower_all_props.2.1 (r + 1) 2 (r + 1) (by omega) hlt)
    rw [hdiag_eq]
    exact Nat.sInf_le ⟨by omega, le_trans hn_le (le_trans h1 (le_trans h2 h3))⟩
  · have hmem := Nat.sInf_mem hdiag_ne
    rw [← hdiag_eq] at hmem
    set r := alphaOmegaDiag n
    have hr1 : 1 ≤ r := hmem.1
    have hn_le : n ≤ diagTower r r := hmem.2
    have hd_le : diagTower r r ≤ ackTower r (2 * r - 1) := by
      rcases hr_eq : r with _ | r'
      · omega
      · exact diagTower_le_ackTower r' (r' + 1) (by omega)
    have hpow_gt : 2 * r - 1 ≤ ackTower (r + 1) 3 := by
      have hgt := ackTower_two_gt_pow (r + 1) (by omega)
      have hlt23 := ackTower_all_props.2.1 (r + 1) 2 3 (by omega) (by omega)
      have h2r : 2 * r - 1 ≤ 2 ^ (r + 1 + 2) := by
        have := two_mul_le_two_pow (r + 1) (by omega)
        have : 2 ^ (r + 1) ≤ 2 ^ (r + 1 + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      omega
    have hF_chain : ackTower r (2 * r - 1) ≤ ackTower (r + 2) 2 := by
      rw [ackTower_succ_two (r + 1), ackTower_succ_add2 r 2]
      exact ackTower_mono_k (by omega) hpow_gt
    exact (h_om_gal (r + 2) (by omega)).mpr (le_trans hn_le (le_trans hd_le hF_chain))

/-- **Proposition 1.3** (`prop:omega-properties`, Asymptotic Dominance and Convention Invariance):
`α_ω` is non-decreasing on `n ≥ 1`, equals `1` for `1 ≤ n ≤ A_4(1) = A_2(16) > 2^65536`, diverges
to `∞`, satisfies `α_ω(n) < log_2 α_r(n)` (`2^{α_ω(n)} < α_r(n)`) eventually and
`α_ω(n) = o(α_r(n))` for every fixed `r ≥ 1`, and satisfies
`α̃_{ω,diag}(n) - 1 ≤ α_ω(n) ≤ α̃_{ω,diag}(n) + 2` for every `n ≥ 1`. -/
theorem prop_1_3_omega_properties :
    (∀ m n : ℕ, 1 ≤ m → m ≤ n → alphaOmega m ≤ alphaOmega n) ∧
    (ackermann 4 1 = ackermann 2 16 ∧ 2 ^ 65536 < ackermann 2 16 ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ ackermann 4 1 → alphaOmega n = 1) ∧
    (∀ M : ℕ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → M ≤ alphaOmega n) ∧
    (∀ r : ℕ, 1 ≤ r →
      (∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 2 ^ alphaOmega n < alphaHierarchy r n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        (alphaOmega n : ℝ) ≤ ε * (alphaHierarchy r n : ℝ))) ∧
    (∀ n : ℕ, 1 ≤ n →
      alphaOmegaDiag n ≤ alphaOmega n + 1 ∧ alphaOmega n ≤ alphaOmegaDiag n + 2) := by
  have h_mono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → alphaOmega m ≤ alphaOmega n := by
    intro m n hm hmn
    obtain ⟨hn_pos, hn_gal⟩ := alphaOmega_pos_and_galois n (by omega)
    obtain ⟨_, hm_gal⟩ := alphaOmega_pos_and_galois m hm
    have hn_le : n ≤ ackTower (alphaOmega n) 2 := (hn_gal (alphaOmega n) hn_pos).mp le_rfl
    exact (hm_gal (alphaOmega n) hn_pos).mpr (le_trans hmn hn_le)
  have h_div : ∀ M : ℕ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → M ≤ alphaOmega n := by
    intro M
    by_cases hM1 : M ≤ 1
    · refine ⟨1, le_rfl, fun n hn => ?_⟩
      have hpos := (alphaOmega_pos_and_galois n hn).1
      omega
    · refine ⟨ackTower (M - 1) 2 + 1, by omega, fun n hn => ?_⟩
      obtain ⟨_, hgal⟩ := alphaOmega_pos_and_galois n (by omega)
      by_contra hlt
      have hle : alphaOmega n ≤ M - 1 := by omega
      have hn_le := (hgal (M - 1) (by omega)).mp hle
      omega
  have h_dom : ∀ r : ℕ, 1 ≤ r →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → 2 ^ alphaOmega n < alphaHierarchy r n := by
    intro r hr
    refine ⟨ackTower (r + 2) 2 + 1, by omega, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := by omega
    obtain ⟨hs_pos, hs_gal⟩ := alphaOmega_pos_and_galois n hn1
    set s := alphaOmega n
    have hs_gt : r + 2 < s := by
      by_contra hnot
      have hle : s ≤ r + 2 := Nat.le_of_not_lt hnot
      have := (hs_gal (r + 2) (by omega)).mp hle
      omega
    have hnot : ¬ (n ≤ ackTower (s - 1) 2) := fun hle => by
      have := (hs_gal (s - 1) (by omega)).mpr hle
      omega
    have h_eq1 : ackTower (s - 1) 2 = ackTower (s - 2) 4 := by
      have hs1 : s - 1 = (s - 2) + 1 := by omega
      rw [hs1, ackTower_succ_two]
    have h_lt34 : ackTower (s - 2) 3 < ackTower (s - 2) 4 :=
      ackTower_all_props.2.1 (s - 2) 3 4 (by omega) (by omega)
    have h_eq2 : ackTower (s - 2) 3 = ackTower (s - 3) (ackTower (s - 2) 2) := by
      have hs2 : s - 2 = (s - 3) + 1 := by omega
      rw [hs2, ackTower_succ_add2 (s - 3) 1]
    have h_s2_gt : 2 ^ s < ackTower (s - 2) 2 := by
      have hgt := ackTower_two_gt_pow (s - 2) (by omega)
      have hidx : s - 2 + 2 = s := by omega
      rwa [hidx] at hgt
    have h_r_le : ackTower r (2 ^ s) ≤ ackTower (s - 3) (ackTower (s - 2) 2) := by
      calc ackTower r (2 ^ s)
          ≤ ackTower r (ackTower (s - 2) 2) :=
            ackTower_mono_k Nat.one_le_two_pow (le_of_lt h_s2_gt)
        _ ≤ ackTower (s - 3) (ackTower (s - 2) 2) :=
            ackTower_all_props.2.2 r (s - 3) _ (by omega)
              (le_trans Nat.one_le_two_pow (le_of_lt h_s2_gt))
    have hFr_lt_n : ackTower r (2 ^ s) < n := by omega
    by_contra hnot_lt
    have hle : alphaHierarchy r n ≤ 2 ^ s := Nat.le_of_not_lt hnot_lt
    have := ((alphaHierarchy_all_props r).2.2.1 (2 ^ s) n Nat.one_le_two_pow hn1).mp hle
    omega
  refine ⟨h_mono, ?_, h_div, ?_, alphaOmegaDiag_comparison⟩
  · obtain ⟨h41, hgt⟩ := ack4_eq_ack2_16_and_gt
    refine ⟨h41, hgt, ?_⟩
    intro n hn hn_le
    obtain ⟨hpos, hgal⟩ := alphaOmega_pos_and_galois n hn
    have heq12 : ackTower 1 2 = ackermann 4 1 := by
      rw [ackTower_succ_two 0, ackTower_zero_succ 3]
    have hle1 : alphaOmega n ≤ 1 := (hgal 1 le_rfl).mpr (by rwa [heq12])
    exact le_antisymm hle1 hpos
  · intro r hr
    refine ⟨h_dom r hr, ?_⟩
    intro ε hε
    set K : ℕ := Nat.ceil (1 / ε) + 1
    obtain ⟨N₁, hN₁_pos, hN₁⟩ := h_div (2 * K + 6)
    obtain ⟨N₂, hN₂_pos, hN₂⟩ := h_dom r hr
    refine ⟨max N₁ N₂, by omega, fun n hn => ?_⟩
    set s := alphaOmega n
    have hs_ge : 2 * K + 6 ≤ s := hN₁ n (le_of_max_le_left hn)
    have h2s_lt : 2 ^ s < alphaHierarchy r n := hN₂ n (le_of_max_le_right hn)
    have hKs_lt : K * s < alphaHierarchy r n :=
      lt_trans (mul_lt_two_pow_of_ge K s hs_ge) h2s_lt
    have hKs_R : (K : ℝ) * (s : ℝ) ≤ (alphaHierarchy r n : ℝ) := by
      exact_mod_cast le_of_lt hKs_lt
    have h_ceil : 1 / ε ≤ (Nat.ceil (1 / ε) : ℝ) := Nat.le_ceil (1 / ε)
    have hK_ge : 1 / ε ≤ (K : ℝ) := by
      have : (K : ℝ) = (Nat.ceil (1 / ε) : ℝ) + 1 := by simp [K]
      linarith
    have hεK : 1 ≤ ε * (K : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hK_ge (le_of_lt hε)
      have h1 : ε * (1 / ε) = 1 := mul_one_div_cancel (ne_of_gt hε)
      linarith
    have hs_nonneg : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
    calc (s : ℝ) = 1 * (s : ℝ) := by ring
      _ ≤ (ε * (K : ℝ)) * (s : ℝ) := mul_le_mul_of_nonneg_right hεK hs_nonneg
      _ = ε * ((K : ℝ) * (s : ℝ)) := by ring
      _ ≤ ε * (alphaHierarchy r n : ℝ) := mul_le_mul_of_nonneg_left hKs_R (le_of_lt hε)


/-! ## 6. Löb–Wainer Fast-Growing Hierarchy Comparison (`prop_A_2_lob_wainer`) -/

private def GoodLW (g : ℕ → ℕ) : Prop :=
  g 1 = 2 ∧ (∀ n : ℕ, 1 ≤ n → n < g n) ∧ (∀ a b : ℕ, 1 ≤ a → a < b → g a < g b)

private lemma goodLW_mono {g : ℕ → ℕ} (hg : GoodLW g) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    g a ≤ g b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (hg.2.2 a b ha hlt)

private lemma goodLW_iter_props {g : ℕ → ℕ} (hg : GoodLW g) :
    (∀ t x : ℕ, 1 ≤ x → x ≤ (g^[t] x)) ∧
    (∀ t x : ℕ, 1 ≤ t → 1 ≤ x → g x ≤ (g^[t] x)) ∧
    (∀ t x : ℕ, 1 ≤ x → (g^[t] x) < (g^[t + 1] x)) ∧
    (∀ t a b : ℕ, 1 ≤ a → a < b → (g^[t] a) < (g^[t] b)) := by
  have h_ge : ∀ t x : ℕ, 1 ≤ x → x ≤ (g^[t] x) := by
    intro t
    induction t with
    | zero => intro x _; exact le_rfl
    | succ t ih =>
      intro x hx
      rw [Function.iterate_succ_apply']
      have hxt := ih x hx
      exact le_trans hxt (le_of_lt (hg.2.1 _ (by omega)))
  have h_ge1 : ∀ t x : ℕ, 1 ≤ t → 1 ≤ x → g x ≤ (g^[t] x) := by
    intro t x ht hx
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    clear ht
    induction d with
    | zero => simp
    | succ d ih =>
      have heq : 1 + (d + 1) = (1 + d) + 1 := by omega
      rw [heq, Function.iterate_succ_apply']
      have hpos : 1 ≤ g x := le_trans hx (le_of_lt (hg.2.1 x hx))
      exact le_trans ih (le_of_lt (hg.2.1 _ (le_trans hpos ih)))
  have h_step_lt : ∀ t x : ℕ, 1 ≤ x → (g^[t] x) < (g^[t + 1] x) := by
    intro t x hx
    rw [Function.iterate_succ_apply']
    exact hg.2.1 _ (le_trans hx (h_ge t x hx))
  have h_strict : ∀ t a b : ℕ, 1 ≤ a → a < b → (g^[t] a) < (g^[t] b) := by
    intro t
    induction t with
    | zero => intro a b _ hab; exact hab
    | succ t ih =>
      intro a b ha hab
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hg.2.2 _ _ (le_trans ha (h_ge t a ha)) (ih a b ha hab)
  exact ⟨h_ge, h_ge1, h_step_lt, h_strict⟩

private lemma goodLW_succ {g : ℕ → ℕ} (hg : GoodLW g) :
    GoodLW (fun n => (g^[n] n)) ∧ (∀ n : ℕ, 1 ≤ n → g n ≤ (g^[n] n)) := by
  obtain ⟨h_ge, h_ge1, h_step_lt, h_strict⟩ := goodLW_iter_props hg
  have h_le : ∀ n : ℕ, 1 ≤ n → g n ≤ (g^[n] n) := fun n hn => h_ge1 n n hn hn
  refine ⟨⟨?_, ?_, ?_⟩, h_le⟩
  · simpa using hg.1
  · intro n hn
    exact lt_of_lt_of_le (hg.2.1 n hn) (h_le n hn)
  · intro a b ha hab
    have h_adj : ∀ m : ℕ, 1 ≤ m → (g^[m] m) < (g^[m + 1] (m + 1)) := by
      intro m hm
      exact lt_trans (h_strict m m (m + 1) hm (by omega)) (h_step_lt m (m + 1) (by omega))
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.add_one_le_iff.mpr hab)
    clear hab
    induction d with
    | zero => simpa using h_adj a ha
    | succ d ih =>
      have heq : a + 1 + (d + 1) = (a + 1 + d) + 1 := by omega
      rw [heq]
      exact lt_trans ih (h_adj (a + 1 + d) (by omega))

private lemma lobWainer_good_all :
    (∀ m : ℕ, GoodLW (lobWainerFinite m)) ∧
    (∀ m n : ℕ, 1 ≤ n → lobWainerFinite m n ≤ lobWainerFinite (m + 1) n) ∧
    GoodLW lobWainerOmega ∧
    (∀ r : ℕ, GoodLW (lobWainerOmegaPlus r)) ∧
    (∀ r n : ℕ, 1 ≤ n → lobWainerOmegaPlus r n ≤ lobWainerOmegaPlus (r + 1) n) ∧
    GoodLW lobWainerOmegaTwo := by
  have h_fin : ∀ m : ℕ, GoodLW (lobWainerFinite m) := by
    intro m
    induction m with
    | zero =>
      refine ⟨rfl, ?_, ?_⟩
      · intro n _; simp [lobWainerFinite]
      · intro a b _ hab; simp [lobWainerFinite]; omega
    | succ m ih => exact (goodLW_succ ih).1
  have h_fin_step : ∀ m n : ℕ, 1 ≤ n → lobWainerFinite m n ≤ lobWainerFinite (m + 1) n :=
    fun m n hn => (goodLW_succ (h_fin m)).2 n hn
  have h_omega : GoodLW lobWainerOmega := by
    refine ⟨?_, ?_, ?_⟩
    · exact (h_fin 1).1
    · intro n hn; exact (h_fin n).2.1 n hn
    · intro a b ha hab
      have h1 : lobWainerFinite a a < lobWainerFinite a b := (h_fin a).2.2 a b ha hab
      have h2 : lobWainerFinite a b ≤ lobWainerFinite b b :=
        monotone_nat_of_le_succ (fun m => h_fin_step m b (by omega)) (le_of_lt hab)
      exact lt_of_lt_of_le h1 h2
  have h_plus : ∀ r : ℕ, GoodLW (lobWainerOmegaPlus r) := by
    intro r
    induction r with
    | zero => exact h_omega
    | succ r ih => exact (goodLW_succ ih).1
  have h_plus_step : ∀ r n : ℕ, 1 ≤ n →
      lobWainerOmegaPlus r n ≤ lobWainerOmegaPlus (r + 1) n :=
    fun r n hn => (goodLW_succ (h_plus r)).2 n hn
  have h_two : GoodLW lobWainerOmegaTwo := by
    refine ⟨?_, ?_, ?_⟩
    · exact (h_plus 1).1
    · intro r hr; exact (h_plus r).2.1 r hr
    · intro a b ha hab
      have h1 : lobWainerOmegaPlus a a < lobWainerOmegaPlus a b := (h_plus a).2.2 a b ha hab
      have h2 : lobWainerOmegaPlus a b ≤ lobWainerOmegaPlus b b :=
        monotone_nat_of_le_succ (fun r => h_plus_step r b (by omega)) (le_of_lt hab)
      exact lt_of_lt_of_le h1 h2
  exact ⟨h_fin, h_fin_step, h_omega, h_plus, h_plus_step, h_two⟩

private lemma lobWainerInv_props {f : ℕ → ℕ} (hf : GoodLW f) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ lobWainerInv f n ∧
    (∀ k : ℕ, 1 ≤ k → (lobWainerInv f n ≤ k ↔ n ≤ f k)) := by
  have hne : {k : ℕ | 1 ≤ k ∧ n ≤ f k}.Nonempty :=
    ⟨n, hn, le_of_lt (hf.2.1 n hn)⟩
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, ?_⟩
  intro k hk
  constructor
  · intro hle
    exact le_trans hmem.2 (goodLW_mono hf hmem.1 hle)
  · intro hle
    exact Nat.sInf_le ⟨hk, hle⟩

private lemma lw_fin1_eq : ∀ n : ℕ, lobWainerFinite 1 n = 2 * n := by
  have h0 : ∀ t x : ℕ, ((lobWainerFinite 0)^[t] x) = x + t := by
    intro t
    induction t with
    | zero => intro x; simp
    | succ t ih => intro x; rw [Function.iterate_succ_apply', ih]; simp [lobWainerFinite]; omega
  intro n
  change (lobWainerFinite 0)^[n] n = 2 * n
  rw [h0]; omega

private lemma lw_fin2_eq : ∀ n : ℕ, lobWainerFinite 2 n = 2 ^ n * n := by
  have h1 : ∀ t x : ℕ, ((lobWainerFinite 1)^[t] x) = 2 ^ t * x := by
    intro t
    induction t with
    | zero => intro x; simp
    | succ t ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, lw_fin1_eq]
      rw [pow_succ]; ring
  intro n
  exact h1 n n

private lemma lw_fin_ge_ack :
    ∀ m : ℕ, 1 ≤ m → ∀ n : ℕ, 2 ≤ n → ackermann m n ≤ lobWainerFinite (m + 1) n := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction d with
  | zero =>
    intro n hn
    simp only [Nat.add_zero]
    rw [lw_fin2_eq]
    change 2 ^ n ≤ 2 ^ n * n
    exact Nat.le_mul_of_pos_right _ (by omega)
  | succ d ih =>
    intro n hn
    have hidx : 1 + (d + 1) = (1 + d) + 1 := by omega
    rw [hidx]
    set g := lobWainerFinite ((1 + d) + 1)
    have h_iter : ∀ t : ℕ, 1 ≤ t → ackermann ((1 + d) + 1) t ≤ (g^[t] n) := by
      intro t ht
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      clear ht
      induction s with
      | zero =>
        simp only [Nat.add_zero, Function.iterate_one]
        calc ackermann ((1 + d) + 1) 1 = ackermann (1 + d) 2 := ack_step_col1 (by omega)
          _ ≤ ackermann (1 + d) n := (ack_strictMono_j (1 + d)).monotone hn
          _ ≤ g n := ih n hn
      | succ s ihs =>
        have hs_eq : 1 + (s + 1) = (1 + s) + 1 := by omega
        rw [hs_eq, Function.iterate_succ_apply']
        have h_yt_ge2 : 2 ≤ g^[1 + s] n := by
          have ha2 : 2 ≤ ackermann ((1 + d) + 1) (1 + s) :=
            le_trans (by omega : 2 ≤ 2 * (1 + s)) (ack_ge_two_mul _ (1 + s) (by omega))
          omega
        calc ackermann ((1 + d) + 1) ((1 + s) + 1)
            = ackermann (1 + d) (ackermann ((1 + d) + 1) (1 + s)) :=
              ack_step_succ (by omega) (by omega)
          _ ≤ ackermann (1 + d) (g^[1 + s] n) := (ack_strictMono_j (1 + d)).monotone ihs
          _ ≤ g (g^[1 + s] n) := ih (g^[1 + s] n) h_yt_ge2
    exact h_iter n (by omega)

private lemma lw_fin_le_ack :
    ∀ m : ℕ, 2 ≤ m → ∀ u : ℕ, 1 ≤ u → lobWainerFinite m u ≤ ackermann m (3 * u) := by
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction d with
  | zero =>
    intro u hu
    simp only [Nat.add_zero]
    rw [lw_fin2_eq]
    have hu_pow : u ≤ 2 ^ u := le_of_lt Nat.lt_two_pow_self
    have h1 : 2 ^ u * u ≤ 2 ^ (2 * u) := by
      calc 2 ^ u * u ≤ 2 ^ u * 2 ^ u := Nat.mul_le_mul_left _ hu_pow
        _ = 2 ^ (2 * u) := by rw [← pow_add]; congr 1; omega
    have h2 : 2 * u ≤ 2 ^ (3 * u) := by
      have hlt : 3 * u < 2 ^ (3 * u) := Nat.lt_two_pow_self
      omega
    calc 2 ^ u * u ≤ 2 ^ (2 * u) := h1
      _ ≤ 2 ^ (2 ^ (3 * u)) := Nat.pow_le_pow_right (by omega) h2
      _ ≤ ackermann 2 (3 * u) := ack2_tower (3 * u) (by omega)
  | succ d ih =>
    intro u hu
    have hidx : 2 + (d + 1) = (2 + d) + 1 := by omega
    rw [hidx]
    by_cases hu1 : u = 1
    · subst hu1
      have h1 : lobWainerFinite ((2 + d) + 1) 1 = 2 := (lobWainer_good_all.1 _).1
      have h2 : 2 ≤ ackermann ((2 + d) + 1) 3 :=
        le_trans (by omega : 2 ≤ 2 * 3) (ack_ge_two_mul _ 3 (by omega))
      simpa [h1] using h2
    · have hu2 : 2 ≤ u := by omega
      set g := lobWainerFinite (2 + d)
      have hg_good : GoodLW g := lobWainer_good_all.1 (2 + d)
      have h_iter : ∀ t : ℕ, (g^[t] u) ≤ ackermann ((2 + d) + 1) (u + 2 * t) := by
        intro t
        induction t with
        | zero =>
          simp only [Function.iterate_zero, id_eq, Nat.mul_zero, Nat.add_zero]
          exact le_trans (by omega : u ≤ 2 * u) (ack_ge_two_mul _ u (by omega))
        | succ t iht =>
          rw [Function.iterate_succ_apply']
          set M := ackermann ((2 + d) + 1) (u + 2 * t)
          have hM_ge4 : 4 ≤ M := by
            have h32 : 4 ≤ ackermann 3 2 :=
              le_trans (by decide : 4 ≤ 2 * 2) (ack_ge_two_mul 3 2 (by decide))
            have h1 : ackermann 3 2 ≤ ackermann ((2 + d) + 1) 2 :=
              ack_mono_i 2 (by omega) (by omega)
            have h2 : ackermann ((2 + d) + 1) 2 ≤ M :=
              (ack_strictMono_j ((2 + d) + 1)).monotone (by omega)
            omega
          have h3M : 3 * M ≤ ackermann ((2 + d) + 1) (u + 2 * t + 1) := by
            have hstep : ackermann ((2 + d) + 1) (u + 2 * t + 1) = ackermann (2 + d) M :=
              ack_step_succ (by omega) (by omega)
            rw [hstep]
            calc 3 * M ≤ 2 ^ M := three_mul_le_two_pow M hM_ge4
              _ ≤ ackermann 1 M := le_rfl
              _ ≤ ackermann (2 + d) M := ack_mono_i M (by omega) (by omega)
          have hxt_pos : 1 ≤ (g^[t] u) :=
            le_trans (by omega : 1 ≤ u) ((goodLW_iter_props hg_good).1 t u (by omega))
          have h_idx : u + 2 * (t + 1) = (u + 2 * t + 1) + 1 := by omega
          rw [h_idx, ack_step_succ (by omega) (by omega)]
          calc g (g^[t] u)
              ≤ ackermann (2 + d) (3 * (g^[t] u)) := ih (g^[t] u) hxt_pos
            _ ≤ ackermann (2 + d) (3 * M) :=
                (ack_strictMono_j (2 + d)).monotone (Nat.mul_le_mul_left 3 iht)
            _ ≤ ackermann (2 + d) (ackermann ((2 + d) + 1) (u + 2 * t + 1)) :=
                (ack_strictMono_j (2 + d)).monotone h3M
      have h3u : u + 2 * u = 3 * u := by omega
      change (g^[u] u) ≤ ackermann ((2 + d) + 1) (3 * u)
      rw [← h3u]
      exact h_iter u

private lemma lw_omega_bounds :
    ∀ k : ℕ, 1 ≤ k →
      ackTower 0 k ≤ lobWainerOmega k ∧ lobWainerOmega k ≤ ackTower 0 (k + 2) := by
  intro k hk
  rcases k with _ | _ | m
  · omega
  · simp [ackTower, lobWainerOmega, lobWainerFinite, ackermann, ackermannStep]
  · set k' := m + 2
    have hk'_lhs : ackTower 0 k' = ackermann k' 1 := ackTower_zero_succ (m + 1)
    have hk'_rhs : ackTower 0 (k' + 2) = ackermann (k' + 2) 1 := ackTower_zero_succ (m + 3)
    rw [hk'_lhs, hk'_rhs]
    change ackermann k' 1 ≤ lobWainerFinite k' k' ∧
      lobWainerFinite k' k' ≤ ackermann (k' + 2) 1
    refine ⟨?_, ?_⟩
    · have h1 : ackermann (k' - 1) 2 ≤ ackermann (k' - 1) k' :=
        (ack_strictMono_j (k' - 1)).monotone (by omega)
      have h2 : ackermann (k' - 1) k' ≤ lobWainerFinite k' k' := by
        have heq : (k' - 1) + 1 = k' := by omega
        simpa [heq] using lw_fin_ge_ack (k' - 1) (by omega) k' (by omega)
      have h3 : ackermann k' 1 = ackermann (k' - 1) 2 := by
        have heq : (k' - 1) + 1 = k' := by omega
        simpa [heq] using ack_step_col1 (i := k' - 1) (by omega)
      omega
    · have h1 : lobWainerFinite k' k' ≤ ackermann k' (3 * k') :=
        lw_fin_le_ack k' (by omega) k' (by omega)
      have h3k : 3 * k' ≤ ackermann (k' + 1) 1 :=
        le_trans (three_mul_le_two_pow_succ k' (by omega)) (ack_col1_exp (k' + 1) (by omega))
      have h2 : ackermann k' (3 * k') ≤ ackermann k' (ackermann (k' + 1) 1) :=
        (ack_strictMono_j k').monotone h3k
      have h3 : ackermann k' (ackermann (k' + 1) 1) = ackermann (k' + 2) 1 := by
        calc ackermann k' (ackermann (k' + 1) 1)
            = ackermann (k' + 1) 2 := (ack_step_succ (by omega) (by omega)).symm
          _ = ackermann (k' + 2) 1 := (ack_step_col1 (by omega)).symm
      omega

private lemma lw_omegaPlus_ge_tower :
    ∀ r k : ℕ, 2 ≤ k → ackTower r k ≤ lobWainerOmegaPlus r k := by
  intro r
  induction r with
  | zero =>
    intro k hk
    exact (lw_omega_bounds k (by omega)).1
  | succ r ihr =>
    intro k hk
    set g := lobWainerOmegaPlus r
    have hg_good : GoodLW g := lobWainer_good_all.2.2.2.1 r
    have h_iter : ∀ t : ℕ, 1 ≤ t → ackTower (r + 1) t ≤ (g^[t] k) := by
      intro t ht
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      clear ht
      induction s with
      | zero =>
        simp only [Nat.add_zero, Function.iterate_one]
        have h4 : ackTower (r + 1) 1 = 4 := ackTower_succ_one r
        have h8 : lobWainerOmega 2 = 8 := by
          change lobWainerFinite 2 2 = 8
          rw [lw_fin2_eq]; norm_num
        have h_om_le : lobWainerOmega 2 ≤ g 2 :=
          monotone_nat_of_le_succ (fun q => lobWainer_good_all.2.2.2.2.1 q 2 (by omega))
            (Nat.zero_le r)
        have hg_mono : g 2 ≤ g k := goodLW_mono hg_good (by omega) hk
        omega
      | succ s ihs =>
        have hs_eq : 1 + (s + 1) = (1 + s) + 1 := by omega
        rw [hs_eq, Function.iterate_succ_apply']
        have h4 : ackTower (r + 1) 1 = 4 := ackTower_succ_one r
        have hF_ge4 : 4 ≤ ackTower (r + 1) (1 + s) := by
          rw [← h4]
          exact ackTower_mono_k (by omega) (by omega)
        have h_yt_ge4 : 4 ≤ g^[1 + s] k := le_trans hF_ge4 ihs
        have hstep : ackTower (r + 1) ((1 + s) + 1) = ackTower r (ackTower (r + 1) (1 + s)) := by
          simpa using ackTower_succ_step (r := r) (k := (1 + s) + 1) (by omega)
        rw [hstep]
        calc ackTower r (ackTower (r + 1) (1 + s))
            ≤ ackTower r (g^[1 + s] k) := ackTower_mono_k (by omega) ihs
          _ ≤ g (g^[1 + s] k) := ihr (g^[1 + s] k) (by omega)
    exact h_iter k (by omega)

private lemma lw_omegaPlus_le_tower :
    ∀ r u : ℕ, 1 ≤ u → lobWainerOmegaPlus r u ≤ ackTower r (3 * u) := by
  intro r
  induction r with
  | zero =>
    intro u hu
    have h1 := (lw_omega_bounds u hu).2
    have h2 : ackTower 0 (u + 2) ≤ ackTower 0 (3 * u) :=
      ackTower_mono_k (by omega) (by omega)
    exact le_trans h1 h2
  | succ r ihr =>
    intro u hu
    by_cases hu1 : u = 1
    · subst hu1
      simp only [Nat.mul_one]
      have h1 : lobWainerOmegaPlus (r + 1) 1 = 2 := (lobWainer_good_all.2.2.2.1 (r + 1)).1
      have h2 : 4 ≤ ackTower (r + 1) 3 := by
        have h4 : ackTower (r + 1) 1 = 4 := ackTower_succ_one r
        rw [← h4]
        exact ackTower_mono_k (by omega) (by omega)
      omega
    · have hu2 : 2 ≤ u := by omega
      set g := lobWainerOmegaPlus r
      have hg_good : GoodLW g := lobWainer_good_all.2.2.2.1 r
      have h_iter : ∀ t : ℕ, (g^[t] u) ≤ ackTower (r + 1) (u + 2 * t) := by
        intro t
        induction t with
        | zero =>
          simp only [Function.iterate_zero, id_eq, Nat.mul_zero, Nat.add_zero]
          exact le_trans (le_of_lt Nat.lt_two_pow_self) (ackTower_all_props.1 (r + 1) u (by omega))
        | succ t iht =>
          rw [Function.iterate_succ_apply']
          set M := ackTower (r + 1) (u + 2 * t)
          have hM_ge8 : 8 ≤ M := by
            have hgt := ackTower_two_gt_pow (r + 1) (by omega)
            have h8 : 8 ≤ 2 ^ (r + 1 + 2) := by
              have : 2 ^ 3 ≤ 2 ^ (r + 1 + 2) := Nat.pow_le_pow_right (by omega) (by omega)
              omega
            have hmono := ackTower_mono_k (r := r + 1) (by omega : 1 ≤ 2) (by omega : 2 ≤ u + 2 * t)
            omega
          have hstep1 : ackTower (r + 1) (u + 2 * t + 1) = ackTower r M := by
            simpa using ackTower_succ_step (r := r) (k := u + 2 * t + 1) (by omega)
          have h3M : 3 * M ≤ ackTower (r + 1) (u + 2 * t + 1) := by
            rw [hstep1]
            exact le_trans (three_mul_le_two_pow M (by omega)) (ackTower_all_props.1 r M (by omega))
          have hxt_pos : 1 ≤ (g^[t] u) :=
            le_trans (by omega : 1 ≤ u) ((goodLW_iter_props hg_good).1 t u (by omega))
          have hstep2 : ackTower (r + 1) (u + 2 * (t + 1)) =
              ackTower r (ackTower (r + 1) (u + 2 * t + 1)) := by
            have hs := ackTower_succ_step (r := r) (k := u + 2 * (t + 1)) (by omega)
            have hsub : u + 2 * (t + 1) - 1 = u + 2 * t + 1 := by omega
            rwa [hsub] at hs
          rw [hstep2]
          calc g (g^[t] u)
              ≤ ackTower r (3 * (g^[t] u)) := ihr (g^[t] u) hxt_pos
            _ ≤ ackTower r (3 * M) := ackTower_mono_k (by omega) (Nat.mul_le_mul_left 3 iht)
            _ ≤ ackTower r (ackTower (r + 1) (u + 2 * t + 1)) := ackTower_mono_k (by omega) h3M
      have h3u : u + 2 * u = 3 * u := by omega
      change (g^[u] u) ≤ ackTower (r + 1) (3 * u)
      rw [← h3u]
      exact h_iter u

/-- **Proposition A.2** (`prop:lob-wainer`, Position of `α_0`, `α_r`, and `α_ω` in the
Löb–Wainer Fast-Growing Hierarchy):
Two-sided comparisons between `α_0, α_r, α_ω` and `f_ω⁻¹, f_{ω+r}⁻¹, f_{ω·2}⁻¹`. -/
theorem prop_A_2_lob_wainer :
    ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      (lobWainerInv lobWainerOmega n ≤ alpha0 n ∧
        alpha0 n ≤ lobWainerInv lobWainerOmega n + 2) ∧
      (alphaHierarchy r n ≤ 3 * lobWainerInv (lobWainerOmegaPlus r) n ∧
        (alphaHierarchy r n : ℝ) / 3 ≤ (lobWainerInv (lobWainerOmegaPlus r) n : ℝ) ∧
        lobWainerInv (lobWainerOmegaPlus r) n ≤ max (alphaHierarchy r n) 2) ∧
      (lobWainerInv lobWainerOmegaTwo n ≤ alphaOmega n + 1 ∧
        alphaOmega n ≤ lobWainerInv lobWainerOmegaTwo n + 2) := by
  intro n r hn hr
  obtain ⟨h_inv_om_pos, h_inv_om_gal⟩ := lobWainerInv_props lobWainer_good_all.2.2.1 n hn
  obtain ⟨h_inv_pl_pos, h_inv_pl_gal⟩ :=
    lobWainerInv_props (lobWainer_good_all.2.2.2.1 r) n hn
  obtain ⟨h_inv_tw_pos, h_inv_tw_gal⟩ :=
    lobWainerInv_props lobWainer_good_all.2.2.2.2.2 n hn
  obtain ⟨h_om_pos, h_om_gal⟩ := alphaOmega_pos_and_galois n hn
  refine ⟨?_, ?_, ?_⟩
  -- Part 1: `f_ω⁻¹(n) ≤ α_0(n) ≤ f_ω⁻¹(n) + 2`
  · refine ⟨?_, ?_⟩
    · set k := alpha0 n
      have hk1 : 1 ≤ k := (invAck_spec n).1
      have hn_le : n ≤ ackTower 0 k := by
        rcases hk_eq : k with _ | m
        · omega
        · rw [ackTower_zero_succ, ← hk_eq]
          exact (invAck_spec n).2.1
      exact (h_inv_om_gal k hk1).mpr (le_trans hn_le (lw_omega_bounds k hk1).1)
    · set k := lobWainerInv lobWainerOmega n
      have hn_le : n ≤ lobWainerOmega k := (h_inv_om_gal k h_inv_om_pos).mp le_rfl
      have h_ub : lobWainerOmega k ≤ ackermann (k + 2) 1 := by
        simpa [ackTower_zero_succ (k + 1)] using (lw_omega_bounds k h_inv_om_pos).2
      exact (invAck_galois n (k + 2) (by omega)).mpr (le_trans hn_le h_ub)
  -- Part 2: `α_r(n) ≤ 3 f_{ω+r}⁻¹(n)` and `f_{ω+r}⁻¹(n) ≤ max(α_r(n), 2)`
  · set u := lobWainerInv (lobWainerOmegaPlus r) n
    have hu_le3 : alphaHierarchy r n ≤ 3 * u := by
      have hn_le : n ≤ lobWainerOmegaPlus r u := (h_inv_pl_gal u h_inv_pl_pos).mp le_rfl
      have h_ub : lobWainerOmegaPlus r u ≤ ackTower r (3 * u) :=
        lw_omegaPlus_le_tower r u h_inv_pl_pos
      exact ((alphaHierarchy_all_props r).2.2.1 (3 * u) n (by omega) hn).mpr (le_trans hn_le h_ub)
    have hu_R : (alphaHierarchy r n : ℝ) / 3 ≤ (u : ℝ) := by
      have hcast : (alphaHierarchy r n : ℝ) ≤ 3 * (u : ℝ) := by exact_mod_cast hu_le3
      linarith
    have hu_ub : u ≤ max (alphaHierarchy r n) 2 := by
      set k := max (alphaHierarchy r n) 2
      have hk2 : 2 ≤ k := le_max_right _ _
      have ha_le : alphaHierarchy r n ≤ k := le_max_left _ _
      have hn_le : n ≤ ackTower r k :=
        ((alphaHierarchy_all_props r).2.2.1 k n (by omega) hn).mp ha_le
      exact (h_inv_pl_gal k (by omega)).mpr (le_trans hn_le (lw_omegaPlus_ge_tower r k hk2))
    exact ⟨hu_le3, hu_R, hu_ub⟩
  -- Part 3: `f_{ω·2}⁻¹(n) ≤ α_ω(n) + 1` and `α_ω(n) ≤ f_{ω·2}⁻¹(n) + 2`
  · refine ⟨?_, ?_⟩
    · set s := alphaOmega n
      have hn_le : n ≤ ackTower s 2 := (h_om_gal s h_om_pos).mp le_rfl
      have h1 : ackTower s 2 ≤ ackTower (s + 1) 2 :=
        ackTower_all_props.2.2 s (s + 1) 2 (by omega) (by omega)
      have h2 : ackTower (s + 1) 2 ≤ lobWainerOmegaPlus (s + 1) 2 :=
        lw_omegaPlus_ge_tower (s + 1) 2 (by omega)
      have h3 : lobWainerOmegaPlus (s + 1) 2 ≤ lobWainerOmegaTwo (s + 1) :=
        goodLW_mono (lobWainer_good_all.2.2.2.1 (s + 1)) (by omega) (by omega)
      exact (h_inv_tw_gal (s + 1) (by omega)).mpr
        (le_trans hn_le (le_trans h1 (le_trans h2 h3)))
    · set q := lobWainerInv lobWainerOmegaTwo n
      have hn_le : n ≤ lobWainerOmegaTwo q := (h_inv_tw_gal q h_inv_tw_pos).mp le_rfl
      have h1 : lobWainerOmegaTwo q ≤ ackTower q (3 * q) :=
        lw_omegaPlus_le_tower q q h_inv_tw_pos
      have h3q_le : 3 * q ≤ ackTower (q + 1) 3 := by
        have hlt1 : 3 * q < 2 ^ (q + 3) := three_mul_lt_two_pow_add3 q
        have hlt2 : 2 ^ (q + 1 + 2) < ackTower (q + 1) 2 := ackTower_two_gt_pow (q + 1) (by omega)
        have hlt3 : ackTower (q + 1) 2 < ackTower (q + 1) 3 :=
          ackTower_all_props.2.1 (q + 1) 2 3 (by omega) (by omega)
        have heq : q + 1 + 2 = q + 3 := by omega
        rw [heq] at hlt2
        omega
      have h2 : ackTower q (3 * q) ≤ ackTower (q + 2) 2 := by
        rw [ackTower_succ_two (q + 1), ackTower_succ_add2 q 2]
        exact ackTower_mono_k (by omega) h3q_le
      exact (h_om_gal (q + 2) (by omega)).mpr (le_trans hn_le (le_trans h1 h2))

end Solution.Ackermann
