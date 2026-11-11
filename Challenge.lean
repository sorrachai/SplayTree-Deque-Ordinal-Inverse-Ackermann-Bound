module

public import Challenge.Definitions

/-!
# Ordinal-`ω` Inverse-Ackermann Deque Bound for Splay Trees — Complete Blueprint

This module states the original `lake comparator` target theorem
(`deque_ordinal_omega_ackermann_bound`) verbatim together with all 29 Propositions,
Lemmas, and Theorems of `main_v1.tex` across Sections 1–7 and Appendix A.
-/

public section

open SplayTree

/-! ## Original Challenge Statement (preserved verbatim for `lake comparator`) -/

/-- **Ordinal-`ω` Inverse-Ackermann Deque Bound for Splay Trees**:
There exists an absolute constant `C > 0` such that for any initial binary search tree `init`
with `n` nodes and any valid sequence `ops` of `m` deque operations (`pop`, `push`, `eject`,
`inject`), the total rotation cost `dequeSequenceCost init.tree ops` is at most
`C * (m + n) * ordinalOmegaInvAckermann (m + n)`. -/
theorem deque_ordinal_omega_ackermann_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) (init : BST ℤ) (ops : Fin m → DequeOp ℤ),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        dequeSequenceCost init.tree ops ≤
          C * ((m : ℝ) + (n : ℝ)) * (ordinalOmegaInvAckermann (m + n) : ℝ) := by
  sorry


/-! ## 1. Section 1 & Appendix A: Ackermann Hierarchy, `α_ω`, and Löb–Wainer -/

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
  sorry

/-- **Theorem 1.4** (`thm:main`, Main Theorem — Deletion-Sensitive Bound):
There exists an absolute constant `C > 0` such that for every `n`-node BST `init` and every valid
`m`-operation splay-tree deque sequence `ops` with `d_L = popCount ops` and `d_R = ejectCount ops`,
`Rot(T_0, S) ≤ C (n + m + d_L α_ω(max(d_L, 1)) + d_R α_ω(max(d_R, 1)))`. -/
theorem thm_1_4_main :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type} [LinearOrder α] (n m : ℕ) (init : BST α) (ops : Fin m → DequeOp α),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        dequeSequenceCost init.tree ops ≤
          C * ((n : ℝ) + (m : ℝ) +
            (popCount ops : ℝ) * (alphaOmega (max (popCount ops) 1) : ℝ) +
            (ejectCount ops : ℝ) * (alphaOmega (max (ejectCount ops) 1) : ℝ)) := by
  sorry

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
  sorry

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
  sorry


/-! ## 2. Sections 2.1 & 3: Reduction from Two-Sided Deques to the Folded `POP` Process -/

/-- **Theorem 2.2** (`thm:mod1-reduction`, Reduction to the Folded `POP` Process):
There exists an absolute constant `C_red > 0` reducing any valid two-sided deque execution
`(init, ops)` with `d_L = popCount ops` and `d_R = ejectCount ops` to folded `POP` processes
`H̃_L` of size `d_L` and `H̃_R` of size `d_R` (`J(∅) = 0` when `d_L = 0` or `d_R = 0`) satisfying
`Rot(T_0, S) ≤ 2 J(H̃_L) + 2 J(H̃_R) + C_red (n + m)`. -/
theorem thm_2_2_mod1_reduction :
    ∃ C_red : ℝ, 0 < C_red ∧
      ∀ {α : Type} [LinearOrder α] (n m : ℕ) (init : BST α) (ops : Fin m → DequeOp α),
        init.tree.num_nodes = n →
        ValidDequeSeq init.tree ops →
        ∃ (HL : FoldedPopProcess (popCount ops)) (HR : FoldedPopProcess (ejectCount ops)),
          dequeSequenceCost init.tree ops ≤
            2 * (HL.J : ℝ) + 2 * (HR.J : ℝ) + C_red * ((n : ℝ) + (m : ℝ)) := by
  sorry

/-- **Lemma 3.1** (`lem:projection-stub`, BST Projection Under Rotations and Extremum Splicing):
`LCA`-closed subsets `S` induce valid BSTs `T|_S` on `V(T) ∩ S`, commute with single rotations
`[x, y]` whenever `S` remains `LCA`-closed in `T'`, and commute with splicing out `min V(T)` or
`max V(T)` while preserving `LCA`-closure. -/
theorem lem_3_1_bst_projection {α : Type} [LinearOrder α]
    (t : BinaryTree α) (S : Set α) (ht : t.IsBST) (hLCA : IsLCAClosed t S) :
    ((restrictTree t S).IsBST ∧ ∀ v : α, v ∈ restrictTree t S ↔ v ∈ t ∧ v ∈ S) ∧
    -- Part (1): single rotation `[x, y]`
    (∀ x y : α, IsSingleRotEdge t x y →
      let t' := rotateEdge t x y
      IsLCAClosed t' S →
        (x ∈ S ∧ y ∈ S →
          IsSingleRotEdge (restrictTree t S) x y ∧
            restrictTree t' S = rotateEdge (restrictTree t S) x y) ∧
        (¬ (x ∈ S ∧ y ∈ S) → restrictTree t' S = restrictTree t S)) ∧
    -- Part (2): extremum splicing
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
           (xMax ∉ S → restrictTree tMax S = restrictTree t S))) := by
  sorry

/-- **Lemma 3.2** (`lem:cascade-equiv`, Cascade Equivalence of `POP` and `EJECT`):
On any non-empty BST `t`, `POP` performs `k = |LS(t)| - 1` single rotations and produces the
exact same BST as `popCascade t` (splicing out `v_0 = min V(t)` and executing `⌊k / 2⌋`
vertex-disjoint right single rotations `[v_{2j-1}, v_{2j}]`), and symmetrically for `EJECT` and
`ejectCascade t`. -/
theorem lem_3_2_cascade_equiv {α : Type} [LinearOrder α]
    (t : BinaryTree α) (ht : t.IsBST) (hne : t ≠ .nil) :
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
       SplayTree.eject t = ejectCascade t) := by
  sorry

/-- **Lemma 3.3** (`lem:nested-keys`, Offline Nested-Interval Three-Way Key Assignment):
Every valid `m`-operation deque sequence `(init, ops)` on an `n`-node BST admits an offline
three-way real key assignment `V_L ⊔ V_M ⊔ V_R` (`Lm < Rm`) preserving all BST shapes and
rotation costs, with `|V_L| = d_L` in chronological `POP` order, `|V_M| = n + m - 2d` surviving
in `T_m`, `|V_R| = d_R` in reverse chronological `EJECT` order, and `V_L < V_M < V_R`. -/
theorem lem_3_3_nested_keys {α : Type} [LinearOrder α] {m : ℕ}
    (init : BST α) (ops : Fin m → DequeOp α) (hValid : ValidDequeSeq init.tree ops) :
    ∃ asn : ThreeWayKeyAssignment init ops,
      asn.VL.card = popCount ops ∧
      asn.VM.card + 2 * (popCount ops + ejectCount ops) = init.tree.num_nodes + m ∧
      asn.VR.card = ejectCount ops ∧
      asn.everPresentKeys = asn.VL ∪ asn.VM ∪ asn.VR ∧
      (∀ x ∈ asn.VL, ∀ y ∈ asn.VM, x < y) ∧
      (∀ y ∈ asn.VM, ∀ z ∈ asn.VR, y < z) := by
  sorry

/-- **Lemma 3.4** (`lem:spine-accounting`, Uncoupled Spine Potential Accounting):
Across `(init, ops)` under any `ThreeWayKeyAssignment`:
(1) `Rot(T_0, S) ≤ 2 C_POP(U) + 2 C_EJECT(W) + 9 (n + m)`;
(2) `EJECT` steps induce at most `max(0, 2 d_L - 2)` left single rotations on `U_t` (each along
`RS(U_t)`), and `POP` steps induce at most `max(0, 2 d_R - 2)` right single rotations on `W_t`
(each along `LS(W_t)`). -/
theorem lem_3_4_spine_accounting {α : Type} [LinearOrder α] (n m : ℕ)
    (init : BST α) (ops : Fin m → DequeOp α)
    (hn : init.tree.num_nodes = n) (hValid : ValidDequeSeq init.tree ops)
    (asn : ThreeWayKeyAssignment init ops) :
    -- Part (1)
    dequeSequenceCost init.tree ops ≤
      2 * (asn.cPopU : ℝ) + 2 * (asn.cEjectW : ℝ) + 9 * ((n : ℝ) + (m : ℝ)) ∧
    -- Part (2)
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
      asn.W i.succ = pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) (asn.W i.castSucc)) := by
  sorry

/-- **Lemma 3.5** (`lem:emptying-sim`, Emptying One-Sided Simulation and Spine-Folding Bijection):
(1) Any `n_0`-node BST on `{1, ..., P}` can be built from `∅` using `n_0` `PUSH` steps,
`n_0 - |RS(H_init)|` root right-spine left rotations (`d = 1`), and `0` `POP` steps;
(2) Whenever `P := d_L ≥ 1`, relabeling `V_L` in `POP` order yields `H_L : OneSidedPopExec P`
with `C_POP(U) = C_POP(H_L)` and `K_L ≤ 2 P - 2 < 2 P`;
(3) Spine folding `spineFoldTree` is inverted by `spineUnfoldTree` on BSTs and maps any
`H : OneSidedPopExec P` (`P ≥ 1`) to a `FoldedPopProcess P` `H̃` with `C_POP(H) ≤ P + J(H̃)`. -/
theorem lem_3_5_emptying_sim :
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
          exec.cPop ≤ P + proc.J)) := by
  sorry

/-- **Lemma 3.6** (`lem:folded-laws`, Structural Laws of `(H̃, L'')`):
For every folded `POP` process `proc : FoldedPopProcess P` of size `P ≥ 1`:
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
  sorry


/-! ## 3. Sections 2.2 & 4: Bounded-Gap Cascades Under Right Rotations -/

/-- **Theorem 2.3** (`thm:mod2-cascade`, Bounded-Gap Right-Cascade Bound):
There exists an absolute constant `C_casc > 0` such that for all `i ≥ 1`, `Δ' ≥ 0`, and
`1 ≤ N ≤ A_i(1)`, every pure-right-rotation trajectory on an `N`-node BST executes at most
`C_casc (Δ' + 1) N` `Δ'`-gapped right `(2i)`-cascades. -/
theorem thm_2_3_mod2_cascade :
    ∃ C_casc : ℝ, IsCascadeBoundConst C_casc := by
  sorry

/-- **Proposition 4.1** (`prop:right-reach`, Tamari Right-Reach Characterization):
On `{1, ..., n}` (`n ≥ 1`), BST `t₂` is reachable from BST `t₁` by zero or more right single
rotations if and only if `R_{t₁}(v) ≤ R_{t₂}(v)` for every `v ∈ {1, ..., n}`. -/
theorem prop_4_1_right_reach (n : ℕ) (hn : 1 ≤ n) (t₁ t₂ : BinaryTree ℕ)
    (ht₁ : t₁.IsBST) (ht₂ : t₂.IsBST)
    (hk₁ : keyFinset t₁ = Finset.Icc 1 n) (hk₂ : keyFinset t₂ = Finset.Icc 1 n) :
    RightRotReachable t₁ t₂ ↔ ∀ v ∈ Finset.Icc 1 n, rightReach t₁ v ≤ rightReach t₂ v := by
  sorry

/-- **Lemma 4.2** (`lem:preorder-global`, Preorder-`D` Summary BST Simulation):
(1) `𝒢(B)` is `LCA`-closed in `B` with `|𝒢(B)| = ∑_q min(D, |C_q|) ≤ D K`, so `G(B) = B|_{𝒢(B)}`
is a valid BST on `𝒢(B)`;
(2) Under any right single rotation `[u, v]` on `B`, `normalizeBST (G(B'))` is reachable from
`normalizeBST (G(B))` by right single rotations, and inter-block rotations preserve `𝒢` while
acting directly as `[u, v]` (when `u, v ∈ 𝒢(B)`) or a no-op (otherwise) on `G(B)`. -/
theorem lem_4_2_preorder_global (N D : ℕ) (hN : 1 ≤ N) (hD : 1 ≤ D)
    (B : BinaryTree ℕ) (hB : B.IsBST) (hkB : keyFinset B = Finset.Icc 1 N)
    (blocks : List IntervalBlock) (hPart : IsContiguousBlockPartition N blocks) :
    -- Part (1)
    (IsLCAClosed B (preorderSummarySet B blocks D : Set ℕ) ∧
     (preorderSummaryBST B blocks D).IsBST ∧
     keyFinset (preorderSummaryBST B blocks D) = preorderSummarySet B blocks D ∧
     (preorderSummarySet B blocks D).card = (blocks.map (fun C => min D C.size)).sum ∧
     (preorderSummarySet B blocks D).card ≤ D * blocks.length) ∧
    -- Part (2)
    (∀ u v : ℕ, u < v → IsRightRotEdge B u v →
      let B' := rotateRightEdge B u v
      RightRotReachable
        (normalizeBST (preorderSummaryBST B blocks D))
        (normalizeBST (preorderSummaryBST B' blocks D)) ∧
      ((∀ C ∈ blocks, ¬ (u ∈ C.toFinset ∧ v ∈ C.toFinset)) →
        preorderSummarySet B' blocks D = preorderSummarySet B blocks D ∧
        (u ∈ preorderSummarySet B blocks D ∧ v ∈ preorderSummarySet B blocks D →
          IsRightRotEdge (preorderSummaryBST B blocks D) u v ∧
          preorderSummaryBST B' blocks D =
            rotateRightEdge (preorderSummaryBST B blocks D) u v) ∧
        (¬ (u ∈ preorderSummarySet B blocks D ∧ v ∈ preorderSummarySet B blocks D) →
          preorderSummaryBST B' blocks D = preorderSummaryBST B blocks D))) := by
  sorry

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
            (blocks.map (fun C => psiBlock C D B)).sum)) := by
  sorry


/-! ## 4. Sections 2.3 & 5: Scale-Tree Contraction Pass and Rotation Bucket Bounds -/

/-- **Theorem 2.5** (`thm:mod3-pass`, Scale-Tree Contraction Pass and Bisection Bound):
There exists an absolute constant `C_pass > 0` (independent of `P, r, M, 𝒯`) such that for every
folded `POP` process `H̃` of size `P ≥ 1`:
(1) For every `r ≥ 1` and every `ValidScaleTree P r M T`, leaf subprocesses `{H̃^(Q)}_{Q ∈ 𝒫_M}`
of sizes `1 ≤ |Q| < 2 S_M` with `∑ |Q| = P` satisfy `J(H̃) ≤ C_pass r P + ∑_Q J(H̃^(Q))`;
(2) Elementary bisection gives `J(H̃) ≤ P max(0, ⌈log_2 P⌉ - 1)`. -/
theorem thm_2_5_mod3_pass :
    ∃ C_pass : ℝ, 0 < C_pass ∧
      ∀ (P : ℕ), 1 ≤ P → ∀ proc : FoldedPopProcess P,
        -- Part (1): Scale-tree contraction pass
        (∀ (r M : ℕ) (T : ScaleTree), ValidScaleTree P r M T →
          let leaves := scaleTreePartitionChain T P M (Fin.last M)
          (∀ Q ∈ leaves, 1 ≤ Q.size ∧ Q.size < 2 * scaleS T P M) ∧
          (leaves.map IntervalBlock.size).sum = P ∧
          ∃ subProcs : (Q : IntervalBlock) → Q ∈ leaves → FoldedPopProcess Q.size,
            (proc.J : ℝ) ≤
              C_pass * (r : ℝ) * (P : ℝ) +
                ((leaves.attach.map (fun ⟨Q, hQ⟩ => (subProcs Q hQ).J)).sum : ℝ)) ∧
        -- Part (2): Elementary bisection bound (`Nat.clog 2 P - 1 = max(0, ⌈log_2 P⌉ - 1)`)
        proc.J ≤ P * (Nat.clog 2 P - 1) := by
  sorry

/-- **Lemma 5.1** (`lem:tree-weights`, Height-Independent Weight Convergence):
For every `ValidScaleTree P r M T`, `∑_{ℓ=1}^M 1 / w_ℓ < 1 / 2`,
`∑_{ν ∈ 𝒯_int} 1 / w(ν) < 2`, and `Σ_𝒯 < P / 50`. -/
theorem lem_5_1_tree_weights (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) :
    let chain := scaleTreePartitionChain T P M
    (∑ ℓ ∈ Finset.Icc 1 M, (1 : ℝ) / (leafWeight T ℓ : ℝ)) < (1 : ℝ) / 2 ∧
    (∑ ν ∈ internalAddrs T, (1 : ℝ) / (pathWeight ν : ℝ)) < 2 ∧
    (sigmaScaleTree T chain : ℝ) < (P : ℝ) / 50 := by
  sorry

/-- **Lemma 5.2** (`lem:bucket-leaf`, Intra-Leaf Rotations and Leaf Subprocess Projection):
For any nested contiguous-interval partition chain `𝒫_0 ≻ ... ≻ 𝒫_M` of `{1, ..., P}`,
`|ℬ_{leaf,pre}| ≤ P`, `|ℬ_{leaf,exit}| ≤ P`, and leaf subprocesses `{H̃^(Q)}_{Q ∈ 𝒫_M}` satisfy
`|ℬ_leaf| = |ℬ_{leaf,pre}| + |ℬ_{leaf,exit}| + |ℬ_{leaf,act}| ≤ 2 P + ∑_Q J(H̃^(Q))`. -/
theorem lem_5_2_bucket_leaf {M : ℕ} (P : ℕ) (hP : 1 ≤ P) (hM : 1 ≤ M)
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
  sorry

/-- **Lemma 5.3** (`lem:bucket-b1`, `LCA_𝒯` Routing of `ℬ_1` and Cascade-Path Sink Counting):
`𝒮_1 ⊆ ℬ_1` satisfies `|𝒮_1| ≤ P + 2 Σ_𝒯 < (26 / 25) P`,
(1) `|ℬ_1| ≤ r (|𝒮_1| + |ℬ_{leaf,pre}|) < (51 / 25) r P < 3 r P`, and
(2) `|ℰ_enter| ≤ |𝒮_1| + |ℬ_{leaf,pre}| < (51 / 25) P`. -/
theorem lem_5_3_bucket_b1 (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    let s1 := s1Set P T proc chain
    let ee := eEnter P T proc chain
    let lpre := bLeafPre P proc chain
    s1 ⊆ b1 P proc chain ∧
    s1.card ≤ P + 2 * sigmaScaleTree T chain ∧
    (s1.card : ℝ) < (26 : ℝ) / 25 * (P : ℝ) ∧
    -- Part (1)
    (b1 P proc chain).card ≤ r * (s1.card + lpre.card) ∧
    ((b1 P proc chain).card : ℝ) < (51 : ℝ) / 25 * (r : ℝ) * (P : ℝ) ∧
    (b1 P proc chain).card < 3 * r * P ∧
    -- Part (2)
    ee.card ≤ s1.card + lpre.card ∧
    (ee.card : ℝ) < (51 : ℝ) / 25 * (P : ℝ) := by
  sorry

/-- **Lemma 5.4** (`lem:bucket-b3-intra`, Height-Independent Bound on `ℬ_{3,intra}`):
`|ℬ_{3,intra}| ≤ 2 P + K_rot + |ℰ_enter| < (151 / 25) P < 7 P`, independently of `r, M, 𝒯`. -/
theorem lem_5_4_bucket_b3_intra (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (b3Intra P proc chain).card ≤ 2 * P + proc.kRot + (eEnter P T proc chain).card ∧
    ((b3Intra P proc chain).card : ℝ) < (151 : ℝ) / 25 * (P : ℝ) ∧
    (b3Intra P proc chain).card < 7 * P := by
  sorry

/-- **Lemma 5.5** (`lem:b3-post`, Step 1: Post-Depletion Exits):
Across all scales `1 ≤ ℓ ≤ M`, `|ℬ_{3,exit,post}| ≤ K_L < 2 P`. -/
theorem lem_5_5_b3_post (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (b3ExitPost P proc chain).card ≤ proc.kL ∧ proc.kL < 2 * P := by
  sorry

/-- **Lemma 5.6** (`lem:b3-escape`, Step 2: Unique Scale per Promoted Key and Secondary-Exit
Reduction):
There exists `A_esc ⊆ ℬ_{3,exit,act}` of size `|A_esc| < 18 P` (independent of `r, M, 𝒯`) with
`|ℬ_{3,exit,act}| ≤ 2 ∑_{ℓ, X, p} |𝒩̃_p^(ℓ)| + |A_esc|`. -/
theorem lem_5_6_b3_escape (P r M : ℕ) (T : ScaleTree)
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
  sorry

/-- **Lemma 5.7** (`lem:b3-quotient`, Step 3: Insertion-Time Cartesian Extension `H̃*` and
Block-Root Summary BST `Ĝ_X`):
For each scale `ℓ ∈ {1, ..., M}`, parent block `X ∈ 𝒫_{ℓ-1}` (`K_X ≥ 2`), and `1 ≤ p ≤ K_X - 1`:
`G^(p)(τ) = phaseSummaryBST P proc chain ℓ X p τ` is a `(K_X - p)`-node BST on `{p + 1, ..., K_X}`
evolving purely by right single rotations across `τ ∈ [L_p⁻, L_{p+1}⁻]`, such that
(1) every `e = (x, y, z) ∈ V_{X, p}` (`x ∈ S_b, y ∈ S_q`) at `POP(s)` executes `[b, q]` along
`LS(G^(p)(s⁻))`, and
(2) embedding `G^(p)` via `topEmbedPhase p` onto `{2, ..., K_X}` concatenates all pure-right-rotation
phase trajectories sequentially into a single pure-right-rotation trajectory on `(K_X - 1)`-node
BST `Ĝ_X := phaseSummaryBST P proc chain ℓ X 1 (proc.popStepIdx (subblock1 subs 1).lo)`. -/
theorem lem_5_7_b3_quotient (P r M : ℕ) (T : ScaleTree)
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
      -- Part (1): `e ∈ V_{X, p}` executes `[b, q]` along `LS(G^(p)(s⁻))`
      (∀ e ∈ vXp P proc chain ℓ_val X p,
        let b := subblockIndex1 subs e.x
        let q := subblockIndex1 subs e.y
        let Gs := phaseSummaryBST P proc chain ℓ_val X p e.stepIdx
        let GsNext := phaseSummaryBST P proc chain ℓ_val X p (e.stepIdx + 1)
        p + 1 ≤ b ∧ b < q ∧ q ≤ K_X ∧
        b ∈ leftSpine Gs ∧ q ∈ leftSpine Gs ∧
        IsRightRotEdge Gs b q ∧
        RightRotReachable (rotateRightEdge Gs b q) GsNext)) ∧
    -- Part (2): Phase concatenation on `Ĝ_X` via `topEmbedPhase`
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
  sorry

/-- **Lemma 5.8** (`lem:b3-gaps`, Step 4: Contiguous Left-Spine Runs and Gap-Witness Sets):
On `G_0 = G^(p)(L_p⁻)` with `Π_0 = LS(G_0) = (c_1 < ... < c_m)` and `G_end = G^(p)(τ_empty(p))`:
`ℱ_p ⊆ {c_1, ..., c_{m-1}}`,
(1) maximal contiguous runs `c_a < ... < c_b` of `ℱ_p` on `Π_0` have `s(c_b) < ... < s(c_a)` and
`R_{G_end}(c_t) ≥ R_{G_0}(c_{b+1})`, and
(2) gap-witness sets `𝒰_ℓ(X, p) ⊆ Π_0 \ ℱ_p` satisfy `|𝒰_ℓ(X, p) ∩ gap| ≥ g - 3 > i_ℓ / 2` for
every consecutive gap of size `g > i_ℓ` and
`∑_ℓ |U_ℓ| ≤ 2 |ℬ_{3,intra}| + |𝒮_1| + |ℬ_{leaf,pre}| + 2 K_L + P < 20 P`. -/
theorem lem_5_8_b3_gaps (P r M : ℕ) (T : ScaleTree)
    (hValid : ValidScaleTree P r M T) (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    -- Inclusion & Part (1)
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
    -- Part (2)
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
  sorry

/-- **Lemma 5.9** (`lem:bucket-b3-exit`, Height-Independent Bound on `ℬ_{3,exit}` and `ℬ_3`):
For any constant `C_casc > 0` satisfying Theorem 2.3 (`IsCascadeBoundConst C_casc`),
`|ℬ_{3,exit}| < (9 C_casc + 341) P` and `|ℬ_3| = |ℬ_{3,intra}| + |ℬ_{3,exit}| < (9 C_casc + 348) P`
uniformly across all `r, M, 𝒯`. -/
theorem lem_5_9_bucket_b3_exit (C_casc : ℝ) (hCcasc : IsCascadeBoundConst C_casc)
    (P r M : ℕ) (T : ScaleTree) (hValid : ValidScaleTree P r M T)
    (proc : FoldedPopProcess P) :
    let chain := scaleTreePartitionChain T P M
    (b3 P proc chain).card = (b3Intra P proc chain).card + (b3Exit P proc chain).card ∧
    ((b3Exit P proc chain).card : ℝ) < (9 * C_casc + 341) * (P : ℝ) ∧
    ((b3 P proc chain).card : ℝ) < (9 * C_casc + 348) * (P : ℝ) := by
  sorry

/-- **Lemma 5.10** (`lem:bucket-b2`, `LCA_𝒯` Routing of `ℬ_2`):
`𝒮_2 ⊆ ℬ_2` satisfies `|𝒮_2| ≤ P + 2 Σ_𝒯 < (26 / 25) P` and, for any `C_casc > 0` satisfying
Theorem 2.3,
`|ℬ_2| ≤ P + r (|𝒮_2| + |ℰ_enter| + |ℬ_3|) < (9 C_casc + 353) r P`. -/
theorem lem_5_10_bucket_b2 (C_casc : ℝ) (hCcasc : IsCascadeBoundConst C_casc)
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
  sorry


/-! ## 5. Sections 2.4 & 6: Variable-Depth Scale-Tree Construction and Contraction -/

/-- **Theorem 2.6** (`thm:mod4-contraction`, Variable-Depth Scale-Tree Contraction):
There exists an absolute constant `C_0 ≥ 6` such that for all `P ≥ 1` and `r ≥ 1`, either
`2 P < (max(α_r(P), 2^{C_0^{2r}}))^{6^r}` already, or there exists `ValidScaleTree P r M T`
with `2 S_M ≤ (max(α_r(P), 2^{C_0^{2r}}))^{6^r}`; in particular, at `r = α_ω(P)` leaf blocks
have size `< 2^{C_0^{3r}}`, and at `r = 1` leaf blocks have size `< max(α_1(P), 2^{C_0^2})^6`. -/
theorem thm_2_6_mod4_contraction :
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
              Q.size < (max (alphaHierarchy 1 P) (2 ^ (C₀ ^ 2))) ^ 6) := by
  sorry

/-- **Lemma 6.1** (`lem:build-scale-tree`, Contraction and Empty-Return Bounds for
`BuildScaleTree`):
With `C_0 := 6` and `C_q := 2^{36^q}` (`1 ≤ q ≤ r`):
(1) Any empty return `(none, S') = buildScaleTree r δ' W' S'` (`q' = r - δ'`) satisfies
`2 S' < 4^{q'+1} W' (α_0(2 S') + 1)^2`;
(2) Every call `(τ?, S_out) = buildScaleTree r δ W S_in` (`q = r - δ`) satisfies
`1 ≤ S_out ≤ S_in` and `2 S_out ≤ (max(W, α_q(S_in), 2^{36^q}))^{6^q}`, and a non-empty root call
`buildScaleTreeRoot r P = (some T, S_out, M)` produces `ValidScaleTree P r M T` with
`S_M = S_out`. -/
theorem lem_6_1_build_scale_tree (r P : ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P) :
    -- Part (1): Empty-return bound
    (∀ δ' W' S' : ℕ, δ' < r → 1 ≤ W' → 1 ≤ S' →
      (buildScaleTree r δ' W' S').1 = none →
      let q' := r - δ'
      let w := 2 * S'
      (buildScaleTree r δ' W' S').2 = S' ∧
      w < 4 ^ (q' + 1) * W' * (alpha0 w + 1) ^ 2) ∧
    -- Part (2): Degree-6 contraction and root structural validity
    (∀ δ W S_in : ℕ, δ < r → 1 ≤ W → 1 ≤ S_in →
      let q := r - δ
      let C_q := 2 ^ (36 ^ q)
      let S_out := (buildScaleTree r δ W S_in).2
      1 ≤ S_out ∧ S_out ≤ S_in ∧
      2 * S_out ≤ (max W (max (alphaHierarchy q S_in) C_q)) ^ (6 ^ q)) ∧
    (match buildScaleTreeRoot r P with
     | (none, S_out, M) => M = 0 ∧ S_out = P ∧ (buildScaleTree r 0 1 P).1 = none
     | (some T, S_out, M) =>
       1 ≤ M ∧ ValidScaleTree P r M T ∧
       scaleS T P M = S_out ∧ S_out = (buildScaleTree r 0 1 P).2) := by
  sorry


/-! ## 6. Section 7: Structural Degeneration on the Dyadic Partition -/

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
  sorry
