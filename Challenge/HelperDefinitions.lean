module

public import Challenge.MainDefinitions
public import AlgoLib.DataStructures.SplayTree.Correctness
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

/-!
# Helper Definitions for `ChallengeHelpers` (`main_v2.tex`)

This module extends `Challenge.MainDefinitions` with all intermediate definitions,
structures, and validity predicates needed to state the 28 helper propositions,
lemmas, and reduction theorems of `main_v2.tex` in `ChallengeHelpers.lean`:

* **Section 1 & Appendix A**: `ackTower`, diagonal `α̃_r` / `α̃_{ω,diag}`, and the
  Löb–Wainer fast-growing hierarchy `f_m`, `f_ω`, `f_{ω+r}`, `f_{ω·2}`;
* **Section 2**: BST interval projections (`IsLCAClosed`, `restrictTree`), `POP`/`EJECT`
  cascades, offline three-way key assignments (`ThreeWayKeyAssignment`), emptying
  one-sided `POP` executions (`OneSidedPopExec`), spine folding (`spineFoldTree`),
  and folded `POP` processes (`FoldedPopProcess`, Definition 2.1);
* **Section 3**: Tamari right-reach (`rightReach`, `RightRotReachable`), preorder-`D`
  summary BSTs (`preorderSummaryBST`), left-depth potentials (`phiLeftDepth`, `psiBlock`),
  and `Δ'`-gapped right `k`-cascades (`IsCascadeBoundConst`);
* **Section 4**: Valid height-`r` scale trees (`ScaleTree`, `ValidScaleTree`, Definition 4.1),
  convergent weights, separating scales, and the four rotation classes `ℬ_leaf`, `ℬ_1`,
  `ℬ_2`, `ℬ_3` (`ℬ_{3,intra}`, `ℬ_{3,exit,post}`, lead/secondary exits, Cartesian extension
  `H̃*`, phase summary BSTs `G^(p)`, and gap-witness machinery);
* **Section 5**: Recursive arithmetic builder `buildScaleTree` / `buildScaleTreeRoot`;
* **Section 6**: Dyadic partition chain (`dyadicScaleCount`, `dyadicPartitionChain`).

Notice that `ChallengeMain.lean` does **not** import this file.
-/

@[expose] public section

variable {α : Type}

namespace SplayTree

open BinaryTree

/-!
================================================================================
1. Paper Section 1 & Appendix A: Auxiliary Inverse-Ackermann & Löb–Wainer Defs
================================================================================
-/

/-- Iterated inverse Ackermann function `α*(n) = min {i ≥ 1 | ᾱ^[i](n) ≤ 2}` (Pettie 2008,
Section 3). -/
noncomputable def iteratedInvAckermann (n : ℕ) : ℕ :=
  sInf {i : ℕ | 1 ≤ i ∧ (invAckermann^[i] n) ≤ 2}

/-- Double-iterated inverse Ackermann function `(α*)*(n) = min {i ≥ 1 | (α*)^[i](n) ≤ 2}`:
the minimum number of applications of `iteratedInvAckermann` (`α*`) required to map `n` to at
most `2` (applying Pettie's iteration operator `f*(n) = min {i ≥ 1 | f^[i](n) ≤ 2}` to `α*`). -/
noncomputable def doubleIteratedInvAckermann (n : ℕ) : ℕ :=
  sInf {i : ℕ | 1 ≤ i ∧ (iteratedInvAckermann^[i] n) ≤ 2}


/-- Whether two `DequeOp` values have the same operation kind (`pop`, `push`, `eject`, `inject`),
possibly over different key types. -/
def DequeOp.sameKind {β : Type} : DequeOp α → DequeOp β → Prop
  | .pop, .pop => True
  | .push _, .push _ => True
  | .eject, .eject => True
  | .inject _, .inject _ => True
  | _, _ => False


/-- Inverse-threshold tower `F_r(k)` for `α_r` (Lemma A.1(2)):
* `F_0(k) = A_k(1)` for `k ≥ 1` (with `F_0(0) = 1`),
* `F_r(1) = 4` for `r ≥ 1` (with `F_r(0) = 1`),
* `F_r(k) = F_{r-1}(F_r(k - 1))` for `r ≥ 1, k ≥ 2`. -/
def ackTower : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, k + 1 => ackermann (k + 1) 1
  | _ + 1, 0 => 1
  | _ + 1, 1 => 4
  | r + 1, k + 2 => ackTower r (ackTower (r + 1) (k + 1))

/-- Diagonal inverse Ackermann function `α̃_0(n) = min {k ≥ 1 : A_k(k) ≥ n}` (Proposition 1.3). -/
noncomputable def alphaDiag0 (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ n ≤ ackermann k k}

/-- Star-iterates `α̃_r` of the diagonal inverse Ackermann function `α̃_0` (Proposition 1.3). -/
noncomputable def alphaDiagHierarchy : ℕ → ℕ → ℕ
  | 0 => alphaDiag0
  | r + 1 => starIterate (alphaDiagHierarchy r)

/-- Diagonalized level-`ω` inverse `α̃_{ω,diag}(n) = min {r ≥ 1 : α̃_r(n) ≤ r}` (Proposition 1.3). -/
noncomputable def alphaOmegaDiag (n : ℕ) : ℕ :=
  sInf {r : ℕ | 1 ≤ r ∧ alphaDiagHierarchy r n ≤ r}

/-- Finite levels `f_m` (`m : ℕ`) of the Löb–Wainer fast-growing hierarchy (Proposition A.2):
`f_0(n) = n + 1` and `f_{m+1}(n) = f_m^[n](n)`. -/
def lobWainerFinite : ℕ → ℕ → ℕ
  | 0 => fun n => n + 1
  | m + 1 => fun n => (lobWainerFinite m)^[n] n

/-- Level `f_ω(n) = f_n(n)` of the Löb–Wainer hierarchy (Proposition A.2). -/
def lobWainerOmega (n : ℕ) : ℕ :=
  lobWainerFinite n n

/-- Levels `f_{ω + r}` (`r : ℕ`) of the Löb–Wainer hierarchy (Proposition A.2):
`f_{ω + 0} = f_ω` and `f_{ω + r + 1}(n) = f_{ω + r}^[n](n)`. -/
def lobWainerOmegaPlus : ℕ → ℕ → ℕ
  | 0 => lobWainerOmega
  | r + 1 => fun n => (lobWainerOmegaPlus r)^[n] n

/-- Level `f_{ω · 2}(r) = f_{ω + r}(r)` of the Löb–Wainer hierarchy (Proposition A.2). -/
def lobWainerOmegaTwo (r : ℕ) : ℕ :=
  lobWainerOmegaPlus r r

/-- Functional inverse `f_β⁻¹(n) = min {k ≥ 1 : f_β(k) ≥ n}` (Remark 1.2 & Proposition A.2). -/
noncomputable def lobWainerInv (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ n ≤ f k}


/-!
================================================================================
2. Paper Section 2: BST Projections, Cascades, and Folded `POP` Process
================================================================================
-/

/-- Finite set of keys `V(t)` stored in a `BinaryTree`. -/
def keyFinset [DecidableEq α] : BinaryTree α → Finset α
  | .nil => ∅
  | .node k l r => insert k (keyFinset l ∪ keyFinset r)

/-- Key at the root of `t`, or `none` if `t = .nil`. -/
def rootKey? : BinaryTree α → Option α
  | .nil => none
  | .node k _ _ => some k

/-- Left spine `LS(t)` ordered **bottom-up** from `min V(t)` to `root(t)`:
on a BST, `leftSpine t = [v_0, v_1, ..., v_k]` with `v_0 < v_1 < ... < v_k`. -/
def leftSpine : BinaryTree α → List α
  | .nil => []
  | .node k l _ => leftSpine l ++ [k]

/-- Right spine `RS(t)` ordered **top-down** from `root(t)` to `max V(t)`:
on a BST, `rightSpine t = [b_1, b_2, ..., b_β]` with `b_1 < b_2 < ... < b_β`. -/
def rightSpine : BinaryTree α → List α
  | .nil => []
  | .node k _ r => k :: rightSpine r

/-- Right spine `RS(t)` ordered **bottom-up** from `max V(t)` to `root(t)`:
on a BST, `rightSpineBottomUp t = [u_0, u_1, ..., u_k]` with `u_0 > u_1 > ... > u_k`
(matching Lemma 2.4). -/
def rightSpineBottomUp (t : BinaryTree α) : List α :=
  (rightSpine t).reverse

/-- Subtree `T_v` rooted at key `v` in BST `t` (`.nil` if `v` is not found along search path). -/
def subtreeAtKey [LinearOrder α] : BinaryTree α → α → BinaryTree α
  | .nil, _ => .nil
  | t@(.node k l r), v =>
    if v < k then subtreeAtKey l v
    else if k < v then subtreeAtKey r v
    else t

/-- Left depth `ld_T(v)`: number of left-child edges on the root-to-`v` search path in BST `t`
(Section 2.2). -/
def leftDepth [LinearOrder α] : BinaryTree α → α → ℕ
  | .nil, _ => 0
  | .node k l r, v =>
    if v < k then 1 + leftDepth l v
    else if k < v then leftDepth r v
    else 0

/-- Lowest common ancestor `LCA_T(x, y)` in a BST `t` for `x, y ∈ t` (Section 2.2). -/
def lcaBST [LinearOrder α] : BinaryTree α → α → α → Option α
  | .nil, _, _ => none
  | .node k l r, x, y =>
    if x < k ∧ y < k then lcaBST l x y
    else if k < x ∧ k < y then lcaBST r x y
    else some k

/-- `S` is `LCA`-closed in BST `t` if `x, y ∈ V(t) ∩ S` implies `LCA_t(x, y) ∈ S`
(Section 2.2). -/
def IsLCAClosed [LinearOrder α] (t : BinaryTree α) (S : Set α) : Prop :=
  ∀ x ∈ t, ∀ y ∈ t, x ∈ S → y ∈ S → ∀ z, lcaBST t x y = some z → z ∈ S

/-- Induced BST `T|_S` on `V(T) ∩ S` (Section 2.2):
for `u ∉ S`, takes `B|_S` if `V(B) ∩ S ≠ ∅` and `A|_S` otherwise. -/
noncomputable def restrictTree (t : BinaryTree α) (S : Set α) : BinaryTree α :=
  open Classical in
  match t with
  | .nil => .nil
  | .node u A B =>
    if u ∈ S then .node u (restrictTree A S) (restrictTree B S)
    else if ∃ b ∈ B, b ∈ S then restrictTree B S
    else restrictTree A S

/-- `[x, p]` is a valid right single rotation edge in BST `t` (`x` is the left child of `p`). -/
def IsRightRotEdge [LinearOrder α] (t : BinaryTree α) (x p : α) : Prop :=
  ∃ A B C : BinaryTree α, p ∈ t ∧ subtreeAtKey t p = .node p (.node x A B) C

/-- `[x, p]` is a valid left single rotation edge in BST `t` (`x` is the right child of `p`). -/
def IsLeftRotEdge [LinearOrder α] (t : BinaryTree α) (x p : α) : Prop :=
  ∃ A B C : BinaryTree α, p ∈ t ∧ subtreeAtKey t p = .node p A (.node x B C)

/-- `[x, p]` is a valid single rotation edge in BST `t`, promoting child `x` above parent `p`
(right rotation if `x < p`, left rotation if `p < x`). -/
def IsSingleRotEdge [LinearOrder α] (t : BinaryTree α) (x p : α) : Prop :=
  (x < p ∧ IsRightRotEdge t x p) ∨ (p < x ∧ IsLeftRotEdge t x p)

/-- Execute the right single rotation `[x, p]` promoting left child `x` above parent `p`
(no-op if `[x, p]` is not a right-child edge on the BST search path to `p`). -/
def rotateRightEdge [LinearOrder α] : BinaryTree α → α → α → BinaryTree α
  | .nil, _, _ => .nil
  | .node k l r, x, p =>
    if p < k then .node k (rotateRightEdge l x p) r
    else if k < p then .node k l (rotateRightEdge r x p)
    else match l with
      | .node lx a b => if lx = x then .node lx a (.node k b r) else .node k l r
      | .nil => .node k l r

/-- Execute the left single rotation `[x, p]` promoting right child `x` above parent `p`
(no-op if `[x, p]` is not a right-child edge on the BST search path to `p`). -/
def rotateLeftEdge [LinearOrder α] : BinaryTree α → α → α → BinaryTree α
  | .nil, _, _ => .nil
  | .node k l r, x, p =>
    if p < k then .node k (rotateLeftEdge l x p) r
    else if k < p then .node k l (rotateLeftEdge r x p)
    else match r with
      | .node rx b c => if rx = x then .node rx (.node k l b) c else .node k l r
      | .nil => .node k l r

/-- Execute the single rotation `[x, p]` promoting child `x` above parent `p`
(right rotation when `x < p`, left rotation when `p < x`). -/
def rotateEdge [LinearOrder α] (t : BinaryTree α) (x p : α) : BinaryTree α :=
  if x < p then rotateRightEdge t x p
  else if p < x then rotateLeftEdge t x p
  else t

/-- Splice out `min V(t)` by replacing `x_min(∅, R)` at the bottom of `LS(t)` with `R`
(Lemma 2.3(2) & Lemma 2.4). -/
def spliceMin : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node _ .nil r => r
  | .node k l r => .node k (spliceMin l) r

/-- Splice out `max V(t)` by replacing `x_max(L, ∅)` at the bottom of `RS(t)` with `L`
(Lemma 2.3(2) & Lemma 2.4). -/
def spliceMax : BinaryTree α → BinaryTree α
  | .nil => .nil
  | .node _ l .nil => l
  | .node k l r => .node k l (spliceMax r)

/-- Group consecutive disjoint pairs `(a_0, a_1), (a_2, a_3), ...` of a list, dropping a
trailing odd singleton if present. -/
def adjacentPairs : List α → List (α × α)
  | a :: b :: rest => (a, b) :: adjacentPairs rest
  | _ => []

/-- Vertex-disjoint right-rotation pairs `[v_1, v_2], [v_3, v_4], ...` of a `POP` cascade
along `leftSpine t = [v_0, v_1, ..., v_k]` (Lemma 2.4). -/
def popCascadePairs (t : BinaryTree α) : List (α × α) :=
  adjacentPairs (leftSpine t).tail

/-- Vertex-disjoint left-rotation pairs `[u_1, u_2], [u_3, u_4], ...` of an `EJECT` cascade
along `rightSpineBottomUp t = [u_0, u_1, ..., u_k]` (Lemma 2.4). -/
def ejectCascadePairs (t : BinaryTree α) : List (α × α) :=
  adjacentPairs (rightSpineBottomUp t).tail

/-- Cascade `POP` update: splice out `v_0 = min V(t)` and execute the `⌊k / 2⌋` vertex-disjoint
right single rotations `popCascadePairs t` (Lemma 2.4). -/
def popCascade [LinearOrder α] (t : BinaryTree α) : BinaryTree α :=
  (popCascadePairs t).foldl (fun acc p => rotateRightEdge acc p.1 p.2) (spliceMin t)

/-- Cascade `EJECT` update: splice out `u_0 = max V(t)` and execute the `⌊k / 2⌋` vertex-disjoint
left single rotations `ejectCascadePairs t` (Lemma 2.4). -/
def ejectCascade [LinearOrder α] (t : BinaryTree α) : BinaryTree α :=
  (ejectCascadePairs t).foldl (fun acc p => rotateLeftEdge acc p.1 p.2) (spliceMax t)

/-- Chronological list of keys deleted by `.pop` steps across `(init, ops)`. -/
def popDeletedKeys [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) : List α :=
  (List.finRange m).filterMap (fun i =>
    if (ops i).isPop then (dequeSeq init ops i.castSucc).minKey? else none)

/-- Chronological list of keys deleted by `.eject` steps across `(init, ops)`. -/
def ejectDeletedKeys [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) : List α :=
  (List.finRange m).filterMap (fun i =>
    if (ops i).isEject then (dequeSeq init ops i.castSucc).maxKey? else none)

/-- Offline nested-interval three-way key assignment `V_L ⊔ V_M ⊔ V_R` on `ℝ` for a valid
deque execution `(init, ops)` (Lemma 2.5 & Section 2.3):
re-keys the `n` initial vertices and `m - d` inserted vertices with pairwise distinct real keys
preserving all BST shapes, operation kinds, and rotation costs, separated by thresholds
`Lm < Rm` into `POP`-deleted keys `VL ⊆ (-∞, Lm]` (in chronological `POP` order), surviving keys
`VM ⊂ (Lm, Rm)`, and `EJECT`-deleted keys `VR ⊆ [Rm, +∞)` (in reverse chronological `EJECT` order). -/
structure ThreeWayKeyAssignment [LinearOrder α] {m : ℕ}
    (init : BST α) (ops : Fin m → DequeOp α) where
  T0 : BinaryTree ℝ
  opsR : Fin m → DequeOp ℝ
  Lm : ℝ
  Rm : ℝ
  hLmRm : Lm < Rm
  hKind : ∀ i : Fin m, DequeOp.sameKind (ops i) (opsR i)
  hValidR : ValidDequeSeq T0 opsR
  hBST : ∀ t : Fin (m + 1), (dequeSeq T0 opsR t).IsBST
  hShape : ∀ t : Fin (m + 1),
    (dequeSeq T0 opsR t).map (fun _ => ()) = (dequeSeq init.tree ops t).map (fun _ => ())
  hCost : dequeSequenceCost T0 opsR = dequeSequenceCost init.tree ops
  everPresentKeys : Finset ℝ :=
    open Classical in
    keyFinset T0 ∪ Finset.univ.biUnion (fun i : Fin m =>
      match opsR i with
      | .push x => {x}
      | .inject x => {x}
      | _ => ∅)
  hActiveSub : ∀ t : Fin (m + 1),
    (open Classical in keyFinset (dequeSeq T0 opsR t)) ⊆ everPresentKeys
  hEverCard : everPresentKeys.card + (popCount ops + ejectCount ops) = init.tree.num_nodes + m
  hSurviving :
    (open Classical in keyFinset (dequeSeq T0 opsR (Fin.last m))) =
      everPresentKeys.filter (fun x => Lm < x ∧ x < Rm)
  hPopOrder :
    let pKeys := popDeletedKeys T0 opsR
    pKeys.Pairwise (· < ·) ∧ pKeys.length = popCount ops ∧
      (open Classical in pKeys.toFinset) = everPresentKeys.filter (· ≤ Lm)
  hEjectOrder :
    let eKeys := ejectDeletedKeys T0 opsR
    eKeys.Pairwise (· > ·) ∧ eKeys.length = ejectCount ops ∧
      (open Classical in eKeys.toFinset) = everPresentKeys.filter (Rm ≤ ·)

/-- `V_L = κ(𝒱) ∩ (-∞, L_m]` in a `ThreeWayKeyAssignment` (Lemma 2.5). -/
noncomputable def ThreeWayKeyAssignment.VL [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) : Finset ℝ :=
  asn.everPresentKeys.filter (· ≤ asn.Lm)

/-- `V_M = κ(𝒱) ∩ (L_m, R_m)` in a `ThreeWayKeyAssignment` (Lemma 2.5). -/
noncomputable def ThreeWayKeyAssignment.VM [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) : Finset ℝ :=
  asn.everPresentKeys.filter (fun x => asn.Lm < x ∧ x < asn.Rm)

/-- `V_R = κ(𝒱) ∩ [R_m, +∞)` in a `ThreeWayKeyAssignment` (Lemma 2.5). -/
noncomputable def ThreeWayKeyAssignment.VR [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) : Finset ℝ :=
  asn.everPresentKeys.filter (asn.Rm ≤ ·)

/-- Intermediate re-keyed BST `T_t` (`0 ≤ t ≤ m`) of a `ThreeWayKeyAssignment`. -/
noncomputable def ThreeWayKeyAssignment.treeAt [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) : BinaryTree ℝ :=
  dequeSeq asn.T0 asn.opsR t

/-- Left interval projection `U_t = T_t|_{(-∞, L_m]}` (Section 2.3). -/
noncomputable def ThreeWayKeyAssignment.U [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) : BinaryTree ℝ :=
  restrictTree (asn.treeAt t) {x : ℝ | x ≤ asn.Lm}

/-- Middle interval projection `M_t = T_t|_{(L_m, R_m)}` (Section 2.3). -/
noncomputable def ThreeWayKeyAssignment.M [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) : BinaryTree ℝ :=
  restrictTree (asn.treeAt t) {x : ℝ | asn.Lm < x ∧ x < asn.Rm}

/-- Right interval projection `W_t = T_t|_{[R_m, +∞)}` (Section 2.3). -/
noncomputable def ThreeWayKeyAssignment.W [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) (t : Fin (m + 1)) : BinaryTree ℝ :=
  restrictTree (asn.treeAt t) {x : ℝ | asn.Rm ≤ x}

/-- Total internal `V_L × V_L` cascade right rotations `C_POP(U)` across all `POP` steps
(Section 2.3 & Lemma 2.6). -/
noncomputable def ThreeWayKeyAssignment.cPopU [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) : ℕ :=
  open Classical in
  ∑ i : Fin m,
    if (asn.opsR i).isPop then
      ((popCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)).length
    else 0

/-- Total internal `V_R × V_R` cascade left rotations `C_EJECT(W)` across all `EJECT` steps
(Section 2.3 & Lemma 2.6). -/
noncomputable def ThreeWayKeyAssignment.cEjectW [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) : ℕ :=
  open Classical in
  ∑ i : Fin m,
    if (asn.opsR i).isEject then
      ((ejectCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR)).length
    else 0

/-- Total `EJECT`-induced left single rotations on `U_t` (`V_L × V_L` pairs during `EJECT` steps,
Lemma 2.6(2)). -/
noncomputable def ThreeWayKeyAssignment.ejectInducedLeftRotsOnU [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) : ℕ :=
  open Classical in
  ∑ i : Fin m,
    if (asn.opsR i).isEject then
      ((ejectCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VL ∧ p.2 ∈ asn.VL)).length
    else 0

/-- Total `POP`-induced right single rotations on `W_t` (`V_R × V_R` pairs during `POP` steps,
Lemma 2.6(2)). -/
noncomputable def ThreeWayKeyAssignment.popInducedRightRotsOnW [LinearOrder α] {m : ℕ}
    {init : BST α} {ops : Fin m → DequeOp α}
    (asn : ThreeWayKeyAssignment init ops) : ℕ :=
  open Classical in
  ∑ i : Fin m,
    if (asn.opsR i).isPop then
      ((popCascadePairs (asn.treeAt i.castSucc)).filter
        (fun p => p.1 ∈ asn.VR ∧ p.2 ∈ asn.VR)).length
    else 0

/-- Right-spine concatenation `A ⊕_R B` (Section 2.4): attaches `B` in place of the rightmost
external leaf of `A` (`∅ ⊕_R B = B`, `A ⊕_R ∅ = A`). -/
def rightSpineConcat : BinaryTree α → BinaryTree α → BinaryTree α
  | .nil, b => b
  | .node k l r, b => .node k l (rightSpineConcat r b)

/-- Perform the right-spine left single rotation `[b_{d+1}, b_d]` along
`rightSpine t = [b_1, ..., b_β]` for `1 ≤ d ≤ β - 1` (`d = 1` rotates `[b_2, b_1]` at the root;
Section 2.4). -/
def rotateLeftAtRightSpine1 : BinaryTree α → ℕ → BinaryTree α
  | _, 0 => .nil
  | t, 1 => BinaryTree.rotateLeft t
  | .nil, _ + 2 => .nil
  | .node k l r, d + 2 => .node k l (rotateLeftAtRightSpine1 r (d + 1))

/-- Operation of a one-sided `POP` execution `H` on `{1, ..., P}` (Section 2.4). -/
inductive OneSidedOp where
  | push (w : ℕ) : OneSidedOp
  | pop (s : ℕ) : OneSidedOp
  | rightSpineLeftRot (d : ℕ) : OneSidedOp
  deriving DecidableEq, Repr

/-- Validity of a `OneSidedOp` on BST `t` over universe `{1, ..., P}`. -/
def OneSidedOp.Valid (P : ℕ) (t : BinaryTree ℕ) : OneSidedOp → Prop
  | .push w => 1 ≤ w ∧ w ≤ P ∧ ∀ k ∈ t, w < k
  | .pop s => t ≠ .nil ∧ t.minKey? = some s
  | .rightSpineLeftRot d => 1 ≤ d ∧ d + 1 ≤ (rightSpine t).length

/-- State transition of a `OneSidedOp` on `t` (using the cascade `POP` rule of Lemma 2.4). -/
def OneSidedOp.step (t : BinaryTree ℕ) : OneSidedOp → BinaryTree ℕ
  | .push w => SplayTree.push t w
  | .pop _ => popCascade t
  | .rightSpineLeftRot d => rotateLeftAtRightSpine1 t d

/-- Cascade right-rotation count of a single `OneSidedOp` on `t`. -/
def OneSidedOp.cascadeRots (t : BinaryTree ℕ) : OneSidedOp → ℕ
  | .pop _ => (popCascadePairs t).length
  | _ => 0

/-- Trajectory of states `[H_0, H_1, ..., H_L]` produced by `steps` from `t`. -/
def oneSidedTraj : BinaryTree ℕ → List OneSidedOp → List (BinaryTree ℕ)
  | t, [] => [t]
  | t, op :: rest => t :: oneSidedTraj (op.step t) rest

/-- Every step in `steps` is valid from `t`. -/
def ValidOneSidedOps (P : ℕ) : BinaryTree ℕ → List OneSidedOp → Prop
  | _, [] => True
  | t, op :: rest => op.Valid P t ∧ ValidOneSidedOps P (op.step t) rest

/-- Total `POP` cascade right rotations along `steps` starting from `t`. -/
def oneSidedCascadeCost : BinaryTree ℕ → List OneSidedOp → ℕ
  | _, [] => 0
  | t, op :: rest => op.cascadeRots t + oneSidedCascadeCost (op.step t) rest

/-- One-sided `POP` execution `H` of size `P ≥ 1` on `{1, ..., P}` starting from `∅` and
ending at `∅`, with `P` `PUSH` steps, `P` ordered `POP(1)..POP(P)` cascade steps, and `K_L`
right-spine left single rotations (Section 2.4). -/
structure OneSidedPopExec (P : ℕ) where
  steps : List OneSidedOp
  hValid : ValidOneSidedOps P .nil steps
  hEndEmpty : steps.foldl OneSidedOp.step .nil = .nil
  hPushCount :
    (steps.filterMap (fun | .push w => some w | _ => none)).length = P
  hPopSeq :
    steps.filterMap (fun | .pop s => some s | _ => none) = List.range' 1 P

/-- Total `POP` cascade right rotations `C_POP(H)` of a `OneSidedPopExec` (Section 2.4). -/
def OneSidedPopExec.cPop {P : ℕ} (exec : OneSidedPopExec P) : ℕ :=
  oneSidedCascadeCost .nil exec.steps

/-- Number `K_L` of right-spine left rotations in a `OneSidedPopExec` (Section 2.4). -/
def OneSidedPopExec.kL {P : ℕ} (exec : OneSidedPopExec P) : ℕ :=
  (exec.steps.filter (fun | .rightSpineLeftRot _ => true | _ => false)).length

/-- Tree state `H_τ` after `τ` steps of a `OneSidedPopExec`. -/
def OneSidedPopExec.treeAt {P : ℕ} (exec : OneSidedPopExec P) (τ : ℕ) : BinaryTree ℕ :=
  (exec.steps.take τ).foldl OneSidedOp.step .nil

/-- Apply `f` to the left subtree of the node with key `target` along its BST search path. -/
def modifyLeftAt [LinearOrder α] :
    BinaryTree α → α → (BinaryTree α → BinaryTree α) → BinaryTree α
  | .nil, _, _ => .nil
  | .node k l r, target, f =>
    if target < k then .node k (modifyLeftAt l target f) r
    else if k < target then .node k l (modifyLeftAt r target f)
    else .node k (f l) r

/-- Element immediately following `x` in `xs` (`parent` on `leftSpine`, or `none` at the end). -/
def nextOnSpine [DecidableEq α] : List α → α → Option α
  | a :: b :: rest, x => if a = x then some b else nextOnSpine (b :: rest) x
  | _, _ => none

/-- Prefix of `xs` up to and including the first occurrence of `target`. -/
def takeThrough [DecidableEq α] : List α → α → List α
  | [], _ => []
  | x :: xs, target => if x = target then [x] else x :: takeThrough xs target

/-- Operation of a folded `POP` process `H̃` on `{1, ..., P}` (Definition 2.1). -/
inductive FoldedOp where
  | push (w : ℕ) : FoldedOp
  | shift : FoldedOp
  | upperRot (u v : ℕ) : FoldedOp
  | pop (s : ℕ) : FoldedOp
  deriving DecidableEq, Repr

/-- An internal `POP` (cascade) right rotation `e = (x, y, z) = (v_{2j-1}, v_{2j}, v_{2j+1})`
(`1 ≤ j ≤ h`) executed during `POP(s)` at step index `stepIdx` of a `FoldedPopProcess`
(Definition 2.1). -/
structure InternalPopRot where
  stepIdx : ℕ
  s : ℕ
  j : ℕ
  h : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  deriving DecidableEq, Repr

/-- Validity of a `FoldedOp` on state `(tree, b1)` over universe `{1, ..., P}` (Definition 2.1). -/
def FoldedOp.Valid (P : ℕ) (st : BinaryTree ℕ × Option ℕ) : FoldedOp → Prop
  | .push w =>
    1 ≤ w ∧ w ≤ P ∧ (∀ k ∈ st.1, w < k) ∧
      (st.1 = .nil ↔ st.2 = none) ∧ (∀ b, st.2 = some b → b ∈ leftSpine st.1)
  | .shift =>
    ∃ b, st.2 = some b ∧ b ∈ leftSpine st.1 ∧ rootKey? st.1 ≠ some b
  | .upperRot u v =>
    ∃ b r, st.2 = some b ∧ rootKey? st.1 = some r ∧ b ∈ leftSpine st.1 ∧
      b ≤ u ∧ u < v ∧ v < r ∧ u ∈ leftSpine st.1 ∧ v ∈ leftSpine st.1 ∧
      IsRightRotEdge st.1 u v
  | .pop s =>
    ∃ b, st.1 ≠ .nil ∧ st.1.minKey? = some s ∧ st.2 = some b ∧ b ∈ leftSpine st.1

/-- State transition `(H̃_τ, b_1(τ)) ↦ (H̃_{τ+1}, b_1(τ+1))` of a `FoldedOp` (Definition 2.1). -/
def FoldedOp.step (st : BinaryTree ℕ × Option ℕ) : FoldedOp → BinaryTree ℕ × Option ℕ
  | .push w =>
    match st.2 with
    | none => (.node w .nil .nil, some w)
    | some b => (modifyLeftAt st.1 b (fun L1 => .node w .nil L1), some w)
  | .shift =>
    match st.2 with
    | none => st
    | some b => (st.1, nextOnSpine (leftSpine st.1) b)
  | .upperRot u v =>
    (rotateRightEdge st.1 u v, st.2)
  | .pop _ =>
    let ls := leftSpine st.1
    match st.2 with
    | none => st
    | some b =>
      let sub := takeThrough ls b
      let k := sub.length - 1
      let h := (k - 1) / 2
      let t0 := spliceMin st.1
      if k = 0 then
        (t0, if t0 = .nil then none else nextOnSpine ls b)
      else
        let pairs := (adjacentPairs sub.tail).take h
        let tNew := pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) t0
        let bNew := if k = 2 * h + 2 then sub[2 * h + 1]? else some b
        (tNew, bNew)

/-- Internal `POP` rotations `(v_{2j-1}, v_{2j}, v_{2j+1})` (`1 ≤ j ≤ h`) emitted at step
`stepIdx` on state `st` (Definition 2.1). -/
def foldedPopRotsAt (stepIdx : ℕ) (st : BinaryTree ℕ × Option ℕ) :
    FoldedOp → List InternalPopRot
  | .pop s =>
    match st.2 with
    | none => []
    | some b =>
      let sub := takeThrough (leftSpine st.1) b
      let k := sub.length - 1
      let h := (k - 1) / 2
      (List.range h).filterMap (fun idx =>
        let j := idx + 1
        match sub[2 * j - 1]?, sub[2 * j]?, sub[2 * j + 1]? with
        | some x, some y, some z =>
          some { stepIdx := stepIdx, s := s, j := j, h := h, x := x, y := y, z := z }
        | _, _, _ => none)
  | _ => []

/-- Collect all `InternalPopRot` events across `steps` starting from step index `idx` and state `st`. -/
def collectFoldedPopRots :
    ℕ → (BinaryTree ℕ × Option ℕ) → List FoldedOp → List InternalPopRot
  | _, _, [] => []
  | idx, st, op :: rest =>
    foldedPopRotsAt idx st op ++ collectFoldedPopRots (idx + 1) (op.step st) rest

/-- Every step in `steps` is valid from state `st` on universe `{1, ..., P}`. -/
def ValidFoldedOps (P : ℕ) : (BinaryTree ℕ × Option ℕ) → List FoldedOp → Prop
  | _, [] => True
  | st, op :: rest => op.Valid P st ∧ ValidFoldedOps P (op.step st) rest

/-- **Folded `POP` Process** `H̃` of size `P` (Definition 2.1 for `P ≥ 1`, together with the
empty process `steps = []` with `J(∅) = 0` when `P = 0` as in Theorem 2.2). -/
structure FoldedPopProcess (P : ℕ) where
  steps : List FoldedOp
  hValid : ValidFoldedOps P (.nil, none) steps
  hEndEmpty : steps.foldl FoldedOp.step (.nil, none) = (.nil, none)
  hPushCount :
    (steps.filterMap (fun | .push w => some w | _ => none)).length = P
  hPopSeq :
    steps.filterMap (fun | .pop s => some s | _ => none) = List.range' 1 P
  hKLBound :
    (P = 0 ∧ steps = []) ∨
      (1 ≤ P ∧
        (steps.filter (fun | .shift => true | .upperRot _ _ => true | _ => false)).length < 2 * P)

/-- Number `K_SHIFT` of `.shift` steps in `proc` (Definition 2.1(2)). -/
def FoldedPopProcess.kShift {P : ℕ} (proc : FoldedPopProcess P) : ℕ :=
  (proc.steps.filter (fun | .shift => true | _ => false)).length

/-- Number `K_rot` of `.upperRot` steps in `proc` (Definition 2.1(2)). -/
def FoldedPopProcess.kRot {P : ℕ} (proc : FoldedPopProcess P) : ℕ :=
  (proc.steps.filter (fun | .upperRot _ _ => true | _ => false)).length

/-- Total upper-spine steps `K_L = K_SHIFT + K_rot` in `proc` (Definition 2.1(2)). -/
def FoldedPopProcess.kL {P : ℕ} (proc : FoldedPopProcess P) : ℕ :=
  proc.kShift + proc.kRot

/-- State `(H̃_τ, b_1(τ))` after `τ` steps of `proc` (`0 ≤ τ ≤ proc.steps.length`). -/
def FoldedPopProcess.stateAt {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ) :
    BinaryTree ℕ × Option ℕ :=
  (proc.steps.take τ).foldl FoldedOp.step (.nil, none)

/-- Folded BST `H̃_τ` after `τ` steps of `proc`. -/
def FoldedPopProcess.treeAt {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ) : BinaryTree ℕ :=
  (proc.stateAt τ).1

/-- Fold boundary `b_1(τ)` after `τ` steps of `proc`. -/
def FoldedPopProcess.b1At {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ) : Option ℕ :=
  (proc.stateAt τ).2

/-- Step index `τ` at which `POP(s)` executes (`s⁻` is state `τ` and `s⁺` is state `τ + 1`). -/
def FoldedPopProcess.popStepIdx {P : ℕ} (proc : FoldedPopProcess P) (s : ℕ) : ℕ :=
  proc.steps.findIdx (fun op => op == .pop s)

/-- Step index `ins(u)` at which `PUSH(u)` executes. -/
def FoldedPopProcess.insStep {P : ℕ} (proc : FoldedPopProcess P) (u : ℕ) : ℕ :=
  proc.steps.findIdx (fun op => op == .push u)

/-- Set `ℛ_int(H̃)` of all internal `POP` rotations in `proc` (Definition 2.1). -/
def FoldedPopProcess.rInt {P : ℕ} (proc : FoldedPopProcess P) : Finset InternalPopRot :=
  (collectFoldedPopRots 0 (.nil, none) proc.steps).toFinset

/-- Total count `J(H̃) = |ℛ_int(H̃)|` of internal `POP` rotations (Definition 2.1). -/
def FoldedPopProcess.J {P : ℕ} (proc : FoldedPopProcess P) : ℕ :=
  proc.rInt.card

/-- Next rotation `e⁺ = e_{j+1}` along the same `POP(s)` cascade when `j < h` (Section 4.4). -/
def FoldedPopProcess.nextCascadeRot? {P : ℕ} (proc : FoldedPopProcess P)
    (e : InternalPopRot) : Option InternalPopRot :=
  (collectFoldedPopRots 0 (.nil, none) proc.steps).find?
    (fun e' => e'.stepIdx == e.stepIdx && e'.j == e.j + 1)

/-- Right-spine decomposition `[(b_1, L_1), ..., (b_β, L_β)]` of a BST `H`. -/
def rightSpineFrames : BinaryTree α → List (α × BinaryTree α)
  | .nil => []
  | .node b l r => (b, l) :: rightSpineFrames r

/-- Helper placing `b_1, ..., b_β` upside-down along `LS(H̃)` with `right(b_i) = L_{i+1}` and
`right(b_β) = ∅` (Section 2.4). -/
def spineFoldGo (prevKey : α) (acc : BinaryTree α) : List (α × BinaryTree α) → BinaryTree α
  | [] => .node prevKey acc .nil
  | (bNext, lNext) :: rest => spineFoldGo bNext (.node prevKey acc lNext) rest

/-- Spine-folding map `H_τ ↦ (H̃_τ, b_1(τ))` (Section 2.4). -/
def spineFoldTree : BinaryTree α → BinaryTree α × Option α
  | .nil => (.nil, none)
  | t =>
    match rightSpineFrames t with
    | [] => (.nil, none)
    | (b1, l1) :: rest => (spineFoldGo b1 l1 rest, some b1)

/-- Helper inverting `spineFoldTree` down to fold boundary `b1` (Section 2.4). -/
def spineUnfoldGo [DecidableEq α] (b1 : α) (pendingKey : α) (rightAcc : BinaryTree α) :
    BinaryTree α → BinaryTree α
  | .nil => .node pendingKey .nil rightAcc
  | .node b l r =>
    let newRight := .node pendingKey r rightAcc
    if b = b1 then .node b l newRight
    else spineUnfoldGo b1 b newRight l

/-- Inverse spine-folding map `(H̃_τ, b_1(τ)) ↦ H_τ` recovering the unfolded one-sided BST
(Section 2.4, Section 4.3, and Section 4.6). -/
def spineUnfoldTree [DecidableEq α] : BinaryTree α → Option α → BinaryTree α
  | .nil, _ => .nil
  | _, none => .nil
  | .node bRoot lRoot _, some b1 =>
    if bRoot = b1 then .node bRoot lRoot .nil
    else spineUnfoldGo b1 bRoot .nil lRoot

/-- Map a sequence of `OneSidedOp` steps from `H` to the corresponding `FoldedOp` steps on `H̃`
(Section 2.4). -/
def spineFoldOpList : BinaryTree ℕ → List OneSidedOp → List FoldedOp
  | _, [] => []
  | t, op :: rest =>
    let fop := match op with
      | .push w => FoldedOp.push w
      | .pop s => FoldedOp.pop s
      | .rightSpineLeftRot d =>
        if d ≤ 1 then FoldedOp.shift
        else
          let rs := rightSpine t
          match rs[d - 2]?, rs[d - 1]? with
          | some u, some v => FoldedOp.upperRot u v
          | _, _ => FoldedOp.shift
    fop :: spineFoldOpList (op.step t) rest

/-- Ordered general (rose) tree for Knuth's first-child/right-sibling dual `L''` (Section 2.4). -/
inductive OrderedRoseTree (α : Type) where
  | node (label : α) (children : List (OrderedRoseTree α)) : OrderedRoseTree α
  deriving Repr

/-- Convert a binary tree into an ordered forest via first-child = `.left`,
right-sibling = `.right` (Section 2.4). -/
def toFCRSForest : BinaryTree α → List (OrderedRoseTree α)
  | .nil => []
  | .node x l r => OrderedRoseTree.node x (toFCRSForest l) :: toFCRSForest r

/-- General ordered tree `L''_τ` on `V_τ ∪ {⊤}` rooted at super-root `⊤ := P + 1`
(Section 2.4). -/
def toL2Tree (P : ℕ) (t : BinaryTree ℕ) : OrderedRoseTree ℕ :=
  OrderedRoseTree.node (P + 1) (toFCRSForest t)

/-- Postorder traversal of an ordered forest (visiting each tree's children left-to-right
before its root). -/
def roseForestPostorder : List (OrderedRoseTree α) → List α
  | [] => []
  | OrderedRoseTree.node x cs :: rest => roseForestPostorder cs ++ [x] ++ roseForestPostorder rest

/-- Postorder traversal of `L''_τ` restricted to `V_τ` (i.e. `roseForestPostorder (toFCRSForest t)`,
which equals `(rosePostorder (toL2Tree P t)).dropLast`; Lemma 2.8(1)). -/
def postorderL2OnV (t : BinaryTree ℕ) : List ℕ :=
  roseForestPostorder (toFCRSForest t)

/-- Helper computing the `L''` parent of `v` in `t`: lowest ancestor `a` with `v ∈ left(a)`,
or `curParent` along right-sibling chains. -/
def foldedParentAux (curParent : ℕ) : BinaryTree ℕ → ℕ → ℕ
  | .nil, _ => curParent
  | .node k l r, v =>
    if v < k then foldedParentAux k l v
    else if k < v then foldedParentAux curParent r v
    else curParent

/-- Parent map `π_τ : V_τ → V_τ ∪ {P + 1}` of `L''_τ` under super-root `⊤ := P + 1`
(Section 2.4 & Section 4.5, with `π_τ(P + 1) = P + 1`). -/
def foldedParent (P : ℕ) (t : BinaryTree ℕ) (v : ℕ) : ℕ :=
  if v = P + 1 then P + 1 else foldedParentAux (P + 1) t v

/-- Ancestor set `{π_τ^[d](v) : d ≥ 0}` of `v` in `L''_τ` (Lemma 2.8(1)). -/
def l2Ancestors (P : ℕ) (t : BinaryTree ℕ) (v : ℕ) : Finset ℕ :=
  (Finset.range (P + 2)).image (fun d => (foldedParent P t)^[d] v)

/-- Whether a `FoldedOp` is an `.upperRot` promoting key `x`. -/
def FoldedOp.isUpperRotOf (x : ℕ) : FoldedOp → Bool
  | .upperRot u _ => u == x
  | _ => false

/-- Base rotation subset `ℳ_base ⊆ ℛ_int(H̃)` (Lemma 2.8(3)): internal `POP` rotations `e`
with promoted key `x = e.x` that are either (i) the first internal `POP` promotion of `x`,
(ii) preceded since `x`'s previous internal `POP` promotion by an `UPPERROT` `[x, v]`, or
(iii) preceded by an internal `POP` promotion of `x` that was topmost (`j = h`). -/
def FoldedPopProcess.mBase {P : ℕ} (proc : FoldedPopProcess P) : Finset InternalPopRot :=
  proc.rInt.filter (fun e =>
    let earlier := proc.rInt.filter (fun e' => e'.x = e.x ∧ e'.stepIdx < e.stepIdx)
    earlier = ∅ ∨
      (let prevIdx := earlier.sup InternalPopRot.stepIdx
       (∃ ePrev ∈ earlier, ePrev.stepIdx = prevIdx ∧ ePrev.j = ePrev.h) ∨
         (∃ τ ∈ Finset.Ioo prevIdx e.stepIdx,
           (proc.steps[τ]?).any (FoldedOp.isUpperRotOf e.x) = true)))


/-!
================================================================================
3. Paper Section 3: Right-Reach, Preorder-`D` Summaries, and Cascades
================================================================================
-/

/-- Right-reach `R_T(v) = max V(T_v)` of vertex `v` in a BST `T` on `ℕ`
(returns `0` if `T_v` is empty; Section 3.2). -/
def rightReach (t : BinaryTree ℕ) (v : ℕ) : ℕ :=
  ((subtreeAtKey t v).maxKey?).getD 0

/-- Single right rotation step `t → t'` on a BST (Section 3.2). -/
def RightRotStep [LinearOrder α] (t t' : BinaryTree α) : Prop :=
  ∃ x y : α, x < y ∧ IsRightRotEdge t x y ∧ t' = rotateRightEdge t x y

/-- Reflexive-transitive closure of single right rotations on BSTs
(Tamari right-rotation order; Proposition 3.2). -/
def RightRotReachable [LinearOrder α] (t₁ t₂ : BinaryTree α) : Prop :=
  Relation.ReflTransGen RightRotStep t₁ t₂

/-- 1-indexed position of `x` in `xs` (`0` if `x ∉ xs`). -/
def listRank1 [DecidableEq α] : List α → α → ℕ
  | [], _ => 0
  | y :: ys, x =>
    if x = y then 1
    else
      let r := listRank1 ys x
      if r = 0 then 0 else r + 1

/-- Relabel an `n`-node BST `t` onto `{1, ..., n}` by 1-indexed in-order rank (Section 3.2). -/
def normalizeBST [DecidableEq α] (t : BinaryTree α) : BinaryTree ℕ :=
  let keys := t.toKeyList
  t.map (listRank1 keys)

/-- Preorder key list (root, then left subtree, then right subtree). -/
def bstPreorderList : BinaryTree α → List α
  | .nil => []
  | .node k l r => k :: (bstPreorderList l ++ bstPreorderList r)

/-- 1-indexed preorder rank `pre_T(w) ∈ {1, ..., |V(T)|}` (`0` if `w ∉ T`; Section 3.2). -/
def preorderRank [DecidableEq α] (t : BinaryTree α) (w : α) : ℕ :=
  listRank1 (bstPreorderList t) w

/-- Closed integer interval `[lo, hi]` representing `{lo, ..., hi}`. -/
structure IntervalBlock where
  lo : ℕ
  hi : ℕ
  deriving DecidableEq, Repr

/-- `Finset ℕ` `{lo, ..., hi}` of an `IntervalBlock`. -/
def IntervalBlock.toFinset (C : IntervalBlock) : Finset ℕ :=
  Finset.Icc C.lo C.hi

/-- `Set ℕ` `{x | lo ≤ x ∧ x ≤ hi}` of an `IntervalBlock`. -/
def IntervalBlock.toSet (C : IntervalBlock) : Set ℕ :=
  {x : ℕ | C.lo ≤ x ∧ x ≤ C.hi}

/-- Cardinality `|C|` of an `IntervalBlock`. -/
def IntervalBlock.size (C : IntervalBlock) : ℕ :=
  if C.lo ≤ C.hi then C.hi - C.lo + 1 else 0

/-- Consecutive `IntervalBlock`s satisfy `C₁.hi + 1 = C₂.lo`. -/
def ConsecutiveBlocks : List IntervalBlock → Prop
  | C₁ :: C₂ :: rest => C₁.hi + 1 = C₂.lo ∧ ConsecutiveBlocks (C₂ :: rest)
  | _ => True

/-- `blocks = [C_1, ..., C_K]` partitions `{1, ..., N}` into non-empty contiguous key blocks
`C_1 < C_2 < ... < C_K` (Section 3.2 & Section 4.3). -/
def IsContiguousBlockPartition (N : ℕ) (blocks : List IntervalBlock) : Prop :=
  (∀ C ∈ blocks, 1 ≤ C.lo ∧ C.lo ≤ C.hi ∧ C.hi ≤ N) ∧
    ConsecutiveBlocks blocks ∧
    match blocks.head?, blocks.getLast? with
    | some first, some last => first.lo = 1 ∧ last.hi = N
    | _, _ => N = 0 ∧ blocks = []

/-- Preorder-`D` summary vertex set
`𝒢(B) = ⋃_{q=1}^K {w ∈ C_q : pre_{B|_{C_q}}(w) ≤ D}` (Lemma 3.3). -/
noncomputable def preorderSummarySet (B : BinaryTree ℕ) (blocks : List IntervalBlock)
    (D : ℕ) : Finset ℕ :=
  open Classical in
  blocks.foldr (fun C acc =>
    C.toFinset.filter (fun w =>
      let rk := preorderRank (restrictTree B C.toSet) w
      1 ≤ rk ∧ rk ≤ D) ∪ acc) ∅

/-- Preorder-`D` summary BST `G(B) = B|_{𝒢(B)}` (Lemma 3.3). -/
noncomputable def preorderSummaryBST (B : BinaryTree ℕ) (blocks : List IntervalBlock)
    (D : ℕ) : BinaryTree ℕ :=
  restrictTree B (preorderSummarySet B blocks D : Set ℕ)

/-- `pairs = [(x_1, y_1), ..., (x_k, y_k)]` is a `Δ'`-gapped right `k`-cascade on BST `B`
(Section 3.1 & Section 3.3): `k ≥ 1` vertex-disjoint right single rotations along a single
left-child subpath of `B` with at most `Δ'` subpath vertices strictly between `y_r` and `x_{r+1}`. -/
def IsGappedRightCascade [LinearOrder α] (B : BinaryTree α) (Δ' k : ℕ)
    (pairs : List (α × α)) : Prop :=
  1 ≤ k ∧ pairs.length = k ∧
    ∃ top ∈ B,
      let path := leftSpine (subtreeAtKey B top)
      ∃ idx : Fin k → ℕ,
        (∀ r : Fin k, ∃ h : idx r + 1 < path.length,
          pairs[r.val]? = some (path[idx r], path[idx r + 1])) ∧
        (∀ r₁ r₂ : Fin k, r₁.val + 1 = r₂.val →
          idx r₁ + 2 ≤ idx r₂ ∧ idx r₂ ≤ idx r₁ + Δ' + 2)

/-- Execute a simultaneous right-cascade batch `pairs` on `B` (Section 3.3). -/
def execRightCascadeBatch [LinearOrder α] (B : BinaryTree α)
    (pairs : List (α × α)) : BinaryTree α :=
  pairs.foldl (fun acc p => rotateRightEdge acc p.1 p.2) B

/-- Step in a pure-right-rotation trajectory on a BST with designated `Δ'`-gapped right
`k`-cascade batches (Theorem 3.1 & Section 3.3). -/
inductive RightCascadeTrajStep (α : Type) where
  | singleRot (x y : α) : RightCascadeTrajStep α
  | cascadeBatch (pairs : List (α × α)) : RightCascadeTrajStep α
  deriving DecidableEq, Repr

/-- Apply a `RightCascadeTrajStep` to BST `B`. -/
def RightCascadeTrajStep.step [LinearOrder α] (B : BinaryTree α) :
    RightCascadeTrajStep α → BinaryTree α
  | .singleRot x y => rotateRightEdge B x y
  | .cascadeBatch pairs => execRightCascadeBatch B pairs

/-- Validity of a pure-right-rotation trajectory `traj` with `Δ'`-gapped right `k`-cascades
starting from BST `B`. -/
def ValidRightCascadeTraj [LinearOrder α] (Δ' k : ℕ) :
    BinaryTree α → List (RightCascadeTrajStep α) → Prop
  | _, [] => True
  | B, .singleRot x y :: rest =>
    x < y ∧ IsRightRotEdge B x y ∧ ValidRightCascadeTraj Δ' k (rotateRightEdge B x y) rest
  | B, .cascadeBatch pairs :: rest =>
    IsGappedRightCascade B Δ' k pairs ∧
      ValidRightCascadeTraj Δ' k (execRightCascadeBatch B pairs) rest

/-- Number of `Δ'`-gapped right `k`-cascade batches executed in `traj`. -/
def countCascadeBatches : List (RightCascadeTrajStep α) → ℕ
  | [] => 0
  | .singleRot _ _ :: rest => countCascadeBatches rest
  | .cascadeBatch _ :: rest => 1 + countCascadeBatches rest

/-- Predicate asserting that `C_casc > 0` is a valid universal constant in Theorem 3.1
(`C^{Δ'}_{2i}(N) ≤ C_casc (Δ' + 1) N` for all `i ≥ 1, Δ' ≥ 0, 1 ≤ N ≤ A_i(1)`). -/
def IsCascadeBoundConst (C_casc : ℝ) : Prop :=
  0 < C_casc ∧
    ∀ (i Δ' N : ℕ) {α : Type} [LinearOrder α]
      (B₀ : BinaryTree α) (traj : List (RightCascadeTrajStep α)),
      1 ≤ i → 1 ≤ N → N ≤ ackermann i 1 →
      B₀.IsBST → B₀.num_nodes = N →
      ValidRightCascadeTraj Δ' (2 * i) B₀ traj →
      (countCascadeBatches traj : ℝ) ≤ C_casc * ((Δ' : ℝ) + 1) * (N : ℝ)

/-- Untruncated left-depth potential `Φ_ld(T) = ∑_{v ∈ V(T)} ld_T(v)` (Lemma 3.4(1)). -/
def phiLeftDepth [LinearOrder α] (t : BinaryTree α) : ℕ :=
  (keyFinset t).sum (leftDepth t)

/-- Block truncated left-depth potential
`Ψ_C(B) = |LS(B|_C)| + ∑_{v ∈ C} min(ld_{B|_C}(v), D)` (Lemma 3.4(2)). -/
noncomputable def psiBlock (C : IntervalBlock) (D : ℕ) (B : BinaryTree ℕ) : ℕ :=
  let BC := restrictTree B C.toSet
  (leftSpine BC).length + C.toFinset.sum (fun v => min (leftDepth BC v) D)


/-!
================================================================================
4. Paper Section 4: Scale Trees, Nested Partitions, and Rotation Buckets
================================================================================
-/

/-- `chain` (`𝒫_0 ≻ 𝒫_1 ≻ ... ≻ 𝒫_M`) is a nested chain of contiguous-interval partitions of
`{1, ..., P}` starting from `𝒫_0 = {{1, ..., P}}` (Section 4.3). -/
def IsNestedPartitionChain {M : ℕ} (P : ℕ) (chain : Fin (M + 1) → List IntervalBlock) : Prop :=
  1 ≤ P ∧
    chain 0 = [⟨1, P⟩] ∧
    (∀ ℓ : Fin (M + 1), IsContiguousBlockPartition P (chain ℓ)) ∧
    (∀ ℓ : Fin M, ∀ Y ∈ chain ℓ.succ, ∃ X ∈ chain ℓ.castSucc, X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)

/-- Unique block `B_ℓ(u) ∈ parts` containing `u` (`⟨0, 0⟩` if out of range; Section 4.3). -/
def blockAt (parts : List IntervalBlock) (u : ℕ) : IntervalBlock :=
  (parts.find? (fun B => B.lo ≤ u ∧ u ≤ B.hi)).getD ⟨0, 0⟩

/-- Enclosing block `B_ℓ(Q) := B_ℓ(min Q)` of a finer block `Q` (Section 4.3). -/
def enclosingBlock (parts : List IntervalBlock) (Q : IntervalBlock) : IntervalBlock :=
  blockAt parts Q.lo

/-- Ordered list `[S_1, ..., S_{K_X}]` of child sub-blocks of `X` in `fineParts` (Section 4.6). -/
def childSubblocks (fineParts : List IntervalBlock) (X : IntervalBlock) : List IntervalBlock :=
  fineParts.filter (fun Y => X.lo ≤ Y.lo ∧ Y.hi ≤ X.hi)

/-- 1-indexed child sub-block `S_c` (`1 ≤ c ≤ K_X`). -/
def subblock1 (subs : List IntervalBlock) (c : ℕ) : IntervalBlock :=
  if c = 0 then ⟨0, 0⟩ else (subs[c - 1]?).getD ⟨0, 0⟩

/-- 1-indexed sub-block index `c ∈ {1, ..., K_X}` of key `w` inside `subs` (`0` if absent). -/
def subblockIndex1 (subs : List IntervalBlock) (w : ℕ) : ℕ :=
  match subs.findIdx? (fun S => decide (S.lo ≤ w ∧ w ≤ S.hi)) with
  | some idx => idx + 1
  | none => 0

/-- Separating scale `sep(u, v) ∈ {1, ..., M + 1}` for `u, v ∈ {1, ..., P}` (Section 4.3,
extended by `sep(u, v) = 0` when `u > P` or `v > P` for super-root `⊤ = P + 1` in Section 4.5). -/
def partSepScale {M : ℕ} (P : ℕ) (chain : Fin (M + 1) → List IntervalBlock) (u v : ℕ) : ℕ :=
  if P < u ∨ P < v ∨ u = 0 ∨ v = 0 then 0
  else
    match (List.finRange M).find? (fun ℓ : Fin M =>
      blockAt (chain ℓ.succ) u ≠ blockAt (chain ℓ.succ) v) with
    | some ℓ => ℓ.val + 1
    | none => M + 1

/-- Pre-activation intra-leaf rotations `ℬ_{leaf,pre}` (`sep(x, y) = M + 1` and `s < min Q`;
Section 4.3). -/
def bLeafPre {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  proc.rInt.filter (fun e =>
    partSepScale P chain e.x e.y = M + 1 ∧
      e.s < (blockAt (chain (Fin.last M)) e.x).lo)

/-- Leaf-exit intra-leaf rotations `ℬ_{leaf,exit}` (`sep(x, y) = M + 1`, `s ∈ Q`, `z > max Q`;
Section 4.3). -/
def bLeafExit {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  proc.rInt.filter (fun e =>
    let Q := blockAt (chain (Fin.last M)) e.x
    partSepScale P chain e.x e.y = M + 1 ∧ Q.lo ≤ e.s ∧ Q.hi < e.z)

/-- Active intra-leaf rotations `ℬ_{leaf,act}` (`sep(x, y) = M + 1`, `s ∈ Q`, `z ≤ max Q`;
Section 4.3). -/
def bLeafAct {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  proc.rInt.filter (fun e =>
    let Q := blockAt (chain (Fin.last M)) e.x
    partSepScale P chain e.x e.y = M + 1 ∧ Q.lo ≤ e.s ∧ e.z ≤ Q.hi)

/-- All intra-leaf rotations `ℬ_leaf` (`sep(x, y) = M + 1`; Section 4.3). -/
def bLeaf {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  proc.rInt.filter (fun e => partSepScale P chain e.x e.y = M + 1)

/-- Coarse-trigger split-scale rotations `ℬ_1` (`1 ≤ sep(s, x) < sep(x, y) ≤ M`; Section 4.3). -/
def b1 {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  proc.rInt.filter (fun e =>
    let s1 := partSepScale P chain e.s e.x
    let s2 := partSepScale P chain e.x e.y
    1 ≤ s1 ∧ s1 < s2 ∧ s2 ≤ M)

/-- Fine-trigger split-scale rotations `ℬ_2` (`1 ≤ sep(x, y) < sep(s, x) ≤ M + 1`; Section 4.3). -/
def b2 {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  proc.rInt.filter (fun e =>
    let s1 := partSepScale P chain e.s e.x
    let s2 := partSepScale P chain e.x e.y
    1 ≤ s2 ∧ s2 < s1 ∧ s1 ≤ M + 1)

/-- Same-scale (three-block) rotations `ℬ_3` (`1 ≤ sep(s, x) = sep(x, y) ≤ M`; Section 4.3). -/
def b3 {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  proc.rInt.filter (fun e =>
    let s1 := partSepScale P chain e.s e.x
    let s2 := partSepScale P chain e.x e.y
    1 ≤ s1 ∧ s1 = s2 ∧ s2 ≤ M)

/-- Intra-block same-scale rotations `ℬ_{3,intra}` (`1 ≤ sep(s, x) = sep(x, y) = ℓ ≤ M` and
`z ∈ S_q = B_ℓ(y)`; Section 4.3 & Section 4.5). -/
def b3Intra {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  proc.rInt.filter (fun e =>
    let s1 := partSepScale P chain e.s e.x
    let s2 := partSepScale P chain e.x e.y
    if h : 1 ≤ s2 ∧ s2 ≤ M then
      s1 = s2 ∧ e.z ≤ (blockAt (chain ⟨s2, Nat.lt_succ_of_le h.2⟩) e.y).hi
    else False)

/-- Exiting same-scale rotations `ℬ_{3,exit}` (`1 ≤ sep(s, x) = sep(x, y) = ℓ ≤ M` and
`z > max S_q`; Section 4.3 & Section 4.6). -/
def b3Exit {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  proc.rInt.filter (fun e =>
    let s1 := partSepScale P chain e.s e.x
    let s2 := partSepScale P chain e.x e.y
    if h : 1 ≤ s2 ∧ s2 ≤ M then
      s1 = s2 ∧ (blockAt (chain ⟨s2, Nat.lt_succ_of_le h.2⟩) e.y).hi < e.z
    else False)

/-- Rooted ordered **Scale Tree** `𝒯` whose leaves index scales `{1, ..., M}` (Definition 4.1).
Nodes of `𝒯` are addressed by their 1-indexed child-index path `addr : List ℕ` from the root `[]`. -/
inductive ScaleTree where
  | leaf (scale : ℕ) : ScaleTree
  | internal (children : List ScaleTree) : ScaleTree
  deriving Repr

mutual
  /-- Leaves of a `ScaleTree` in left-to-right order, paired with their 1-indexed child-path
  addresses `addr : List ℕ` from the root. -/
  def ScaleTree.leafEntries : ScaleTree → List (ℕ × List ℕ)
    | .leaf s => [(s, [])]
    | .internal cs => ScaleTree.leafEntriesChildren 1 cs

  /-- Helper traversing children `cs` starting at 1-indexed child position `c`. -/
  def ScaleTree.leafEntriesChildren : ℕ → List ScaleTree → List (ℕ × List ℕ)
    | _, [] => []
    | c, child :: cs =>
      (child.leafEntries.map (fun (s, rest) => (s, c :: rest))) ++
        ScaleTree.leafEntriesChildren (c + 1) cs
end

/-- Leaves of `𝒯` in left-to-right order. -/
def ScaleTree.leaves (T : ScaleTree) : List ℕ :=
  T.leafEntries.map Prod.fst

mutual
  /-- All internal-node 1-indexed child-path addresses `ν ∈ 𝒯_int` (root is `[]`; Section 4.2). -/
  def ScaleTree.internalAddrList : ScaleTree → List (List ℕ)
    | .leaf _ => []
    | .internal cs => [] :: ScaleTree.internalAddrChildren 1 cs

  /-- Helper traversing children `cs` starting at 1-indexed child position `c` for `𝒯_int`. -/
  def ScaleTree.internalAddrChildren : ℕ → List ScaleTree → List (List ℕ)
    | _, [] => []
    | c, child :: cs =>
      (child.internalAddrList.map (c :: ·)) ++
        ScaleTree.internalAddrChildren (c + 1) cs
end

/-- `Finset` of internal-node addresses `𝒯_int` of `𝒯` (Section 4.2). -/
def internalAddrs (T : ScaleTree) : Finset (List ℕ) :=
  T.internalAddrList.toFinset

/-- Every `ScaleTree.internal` node in `𝒯` has at least one child (`k_ν ≥ 1`). -/
def ScaleTree.AllInternalNonempty : ScaleTree → Prop
  | .leaf _ => True
  | .internal cs => cs ≠ [] ∧ ∀ child ∈ cs, child.AllInternalNonempty

/-- `𝒯` is a valid **scale tree of height at most `r`** on scales `{1, ..., M}` (Definition 4.1):
`r ≥ 1, M ≥ 1`, every internal node is non-empty, leaves in left-to-right order are `[1, ..., M]`,
and every leaf sits at depth `δ(ℓ) ∈ {1, ..., r}`. -/
def IsScaleTree (r M : ℕ) (T : ScaleTree) : Prop :=
  1 ≤ r ∧ 1 ≤ M ∧
    T.AllInternalNonempty ∧
    T.leaves = List.range' 1 M ∧
    ∀ entry ∈ T.leafEntries, 1 ≤ entry.2.length ∧ entry.2.length ≤ r

/-- Subtree of `𝒯` at 1-indexed child-path address `addr`. -/
def subtreeAtAddr : ScaleTree → List ℕ → Option ScaleTree
  | T, [] => some T
  | .leaf _, _ :: _ => none
  | .internal cs, c :: rest =>
    if c = 0 then none
    else match cs[c - 1]? with
      | some child => subtreeAtAddr child rest
      | none => none

/-- Child count `k_ν` of internal node `ν ∈ 𝒯_int` (Section 4.2). -/
def numChildren (T : ScaleTree) (ν : List ℕ) : ℕ :=
  match subtreeAtAddr T ν with
  | some (.internal cs) => cs.length
  | _ => 0

/-- Leftmost (coarsest) scale in the subtree of node `ξ` in `𝒯`. -/
def mStart (T : ScaleTree) (ξ : List ℕ) : ℕ :=
  match subtreeAtAddr T ξ with
  | some sub => sub.leaves.head?.getD 0
  | none => 0

/-- Rightmost (finest) scale `M_end(ν)` in the subtree of `ν` in `𝒯` (Section 4.2). -/
def mEnd (T : ScaleTree) (ν : List ℕ) : ℕ :=
  match subtreeAtAddr T ν with
  | some sub => sub.leaves.getLast?.getD 0
  | none => 0

/-- 1-indexed child-path address of leaf `ℓ` in `𝒯`. -/
def leafAddr (T : ScaleTree) (ℓ : ℕ) : List ℕ :=
  match T.leafEntries.find? (fun entry => entry.1 == ℓ) with
  | some (_, addr) => addr
  | none => []

/-- Node path weight `w(ξ) = ∏_{q=1}^{δ(ξ)} (4 c_q^2)` (`w(root) = 1`; Definition 4.1). -/
def pathWeight (ξ : List ℕ) : ℕ :=
  ξ.foldl (fun w c => w * (4 * c ^ 2)) 1

/-- Leaf scale weight `w_ℓ = w(leafAddr T ℓ)` (Definition 4.1). -/
def leafWeight (T : ScaleTree) (ℓ : ℕ) : ℕ :=
  pathWeight (leafAddr T ℓ)

/-- Longest common prefix of two child-path addresses. -/
def longestCommonPrefix [DecidableEq α] : List α → List α → List α
  | a :: as, b :: bs => if a = b then a :: longestCommonPrefix as bs else []
  | _, _ => []

/-- Lowest common ancestor address `LCA_𝒯(ℓ_1, ℓ_2)` of leaves `ℓ_1, ℓ_2` in `𝒯` (Section 4.2). -/
def lcaScaleTree (T : ScaleTree) (ℓ₁ ℓ₂ : ℕ) : List ℕ :=
  longestCommonPrefix (leafAddr T ℓ₁) (leafAddr T ℓ₂)

/-- Scale size parameter `S_ℓ` (`0 ≤ ℓ ≤ M`) of `𝒯` on `{1, ..., P}` (Definition 4.1):
`S_0 = P`, and `S_ℓ = w_ℓ (α_0(2 S_{ℓ-1}) + 1)^2` for `ℓ ≥ 1`. -/
noncomputable def scaleS (T : ScaleTree) (P : ℕ) : ℕ → ℕ
  | 0 => P
  | ℓ + 1 =>
    let sPrev := scaleS T P ℓ
    leafWeight T (ℓ + 1) * (alpha0 (2 * sPrev) + 1) ^ 2

/-- Scale Ackermann level `i_ℓ = α_0(2 S_{ℓ-1}) + 1` for `ℓ ≥ 1` (Definition 4.1). -/
noncomputable def scaleI (T : ScaleTree) (P ℓ : ℕ) : ℕ :=
  alpha0 (2 * scaleS T P (ℓ - 1)) + 1

/-- Split an interval `X` of size `|X| ≥ 2 S` into `K_X = |X| / S ≥ 2` contiguous sub-blocks
where the first `K_X - 1` have size `S` and the last has size in `[S, 2S)` (Definition 4.1). -/
def splitIntervalBySize (X : IntervalBlock) (S : ℕ) : List IntervalBlock :=
  let sz := X.size
  if S = 0 ∨ sz < 2 * S then [X]
  else
    let K := sz / S
    (List.range K).map (fun idx =>
      if idx + 1 < K then ⟨X.lo + idx * S, X.lo + (idx + 1) * S - 1⟩
      else ⟨X.lo + idx * S, X.hi⟩)

/-- Nested partitions `𝒫_0, ..., 𝒫_M` generated by `𝒯` on `{1, ..., P}` (Definition 4.1). -/
noncomputable def scaleTreePartitionLevel (T : ScaleTree) (P : ℕ) : ℕ → List IntervalBlock
  | 0 => if P = 0 then [] else [⟨1, P⟩]
  | ℓ + 1 =>
    let S := scaleS T P (ℓ + 1)
    (scaleTreePartitionLevel T P ℓ).flatMap (fun X => splitIntervalBySize X S)

/-- Canonical `Fin (M + 1) → List IntervalBlock` partition chain of `𝒯` on `{1, ..., P}`
(Definition 4.1). -/
noncomputable def scaleTreePartitionChain (T : ScaleTree) (P M : ℕ) :
    Fin (M + 1) → List IntervalBlock :=
  fun ℓ => scaleTreePartitionLevel T P ℓ.val

/-- `𝒯` is a scale tree of height at most `r` on `M` scales that **validly partitions**
`{1, ..., P}` (`S_ℓ = w_ℓ i_ℓ^2 ≤ S_{ℓ-1} / 2` for all `1 ≤ ℓ ≤ M`; Definition 4.1). -/
def ValidScaleTree (P r M : ℕ) (T : ScaleTree) : Prop :=
  1 ≤ P ∧ IsScaleTree r M T ∧
    ∀ ℓ : Fin M, 2 * scaleS T P (ℓ.val + 1) ≤ scaleS T P ℓ.val

/-- Internal-node freeze-sink sum `Σ_𝒯 = ∑_{ν ∈ 𝒯_int} k_ν |𝒫_{M_end(ν)}|` (Lemma 4.3). -/
def sigmaScaleTree {M : ℕ} (T : ScaleTree)
    (chain : Fin (M + 1) → List IntervalBlock) : ℕ :=
  (internalAddrs T).sum (fun ν =>
    let m := mEnd T ν
    if h : m ≤ M then numChildren T ν * (chain ⟨m, Nat.lt_succ_of_le h⟩).length else 0)

/-- Coarse-trigger sink subset `𝒮_1 ⊆ ℬ_1` collecting Cases A, B1, and B2a across all
`ν ∈ 𝒯_int` (Lemma 4.5). -/
def s1Set {M : ℕ} (P : ℕ) (T : ScaleTree) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  (b1 P proc chain).filter (fun e =>
    let ℓ₁ := partSepScale P chain e.s e.x
    let ℓ₂ := partSepScale P chain e.x e.y
    let ν := lcaScaleTree T ℓ₁ ℓ₂
    let m := mEnd T ν
    if hm : m ≤ M then
      let Q₂ := blockAt (chain ⟨m, Nat.lt_succ_of_le hm⟩) e.y
      Q₂.hi < e.z ∨ e.j = e.h ∨
        (proc.nextCascadeRot? e).elim true (fun eNext => decide (Q₂.hi < eNext.y)) = true
    else True)

/-- External-entry set `ℰ_enter` into `ℬ_1 ⊔ ℬ_{leaf,pre}` from outside `ℬ_1 \ 𝒮_1`
(Lemma 4.5(2)). -/
def eEnter {M : ℕ} (P : ℕ) (T : ScaleTree) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  let s1 := s1Set P T proc chain
  let b1Only := b1 P proc chain \ s1
  let target := b1 P proc chain ∪ bLeafPre P proc chain
  (proc.rInt \ b1Only).filter (fun e =>
    (proc.nextCascadeRot? e).elim false (fun eNext => decide (eNext ∈ target)) = true)

/-- Fine-trigger sink subset `𝒮_2 ⊆ ℬ_2` collecting Cases 2A, 2B1, and 2B2a across all
`ν ∈ 𝒯_int` (Lemma 4.12). -/
def s2Set {M : ℕ} (P : ℕ) (T : ScaleTree) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  (b2 P proc chain).filter (fun e =>
    let ℓ₁ := partSepScale P chain e.s e.x
    let ℓ₂ := partSepScale P chain e.x e.y
    if ℓ₁ ≤ M then
      let ν := lcaScaleTree T ℓ₂ ℓ₁
      let c₂ := ((leafAddr T ℓ₂)[ν.length]?).getD 1
      let mPrev := mStart T (ν ++ [c₂]) - 1
      if hm : mPrev ≤ M then
        let hiShell := (blockAt (chain ⟨mPrev, Nat.lt_succ_of_le hm⟩) e.s).hi
        hiShell < e.z ∨ e.j = e.h ∨
          (proc.nextCascadeRot? e).elim true (fun eNext => decide (hiShell < eNext.y)) = true
      else False
    else False)

/-- `s_max = max(V_{L_p⁻} ∩ S_p)` at the start `L_p⁻` of sub-block `S_p` (Section 4.6). -/
def sMax {P : ℕ} (proc : FoldedPopProcess P) (Sp : IntervalBlock) : ℕ :=
  (keyFinset (proc.treeAt (proc.popStepIdx Sp.lo)) ∩ Sp.toFinset).sup id

/-- Depletion timestamp `τ_empty(p) = s_max⁺` immediately after `POP(s_max)` (Section 4.6). -/
def tauEmpty {P : ℕ} (proc : FoldedPopProcess P) (Sp : IntervalBlock) : ℕ :=
  proc.popStepIdx (sMax proc Sp) + 1

/-- Active-window exiting same-scale rotations `ℬ_{3,exit,act}` (`τ ∈ I_p = [L_p⁻, τ_empty(p))`;
Section 4.6). -/
def b3ExitAct {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  (b3Exit P proc chain).filter (fun e =>
    let ℓ := partSepScale P chain e.x e.y
    if h : ℓ ≤ M then
      let Sp := blockAt (chain ⟨ℓ, Nat.lt_succ_of_le h⟩) e.s
      e.stepIdx < tauEmpty proc Sp
    else False)

/-- Post-depletion exiting same-scale rotations `ℬ_{3,exit,post}`
(`τ ∈ [τ_empty(p), R_p⁺]`; Section 4.6 & Lemma 4.7). -/
def b3ExitPost {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) : Finset InternalPopRot :=
  (b3Exit P proc chain).filter (fun e =>
    let ℓ := partSepScale P chain e.x e.y
    if h : ℓ ≤ M then
      let Sp := blockAt (chain ⟨ℓ, Nat.lt_succ_of_le h⟩) e.s
      tauEmpty proc Sp ≤ e.stepIdx
    else False)

/-- Active-window exiting rotations `V_{X, p}` at scale `ℓ ∈ {1, ..., M}`, parent block `X`,
and 1-indexed trigger sub-block `p ∈ {1, ..., K_X - 1}` (Section 4.6). -/
def vXp {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : ℕ) (X : IntervalBlock) (p : ℕ) :
    Finset InternalPopRot :=
  if h : 1 ≤ ℓ ∧ ℓ ≤ M then
    let subs := childSubblocks (chain ⟨ℓ, Nat.lt_succ_of_le h.2⟩) X
    let Sp := subblock1 subs p
    (b3ExitAct P proc chain).filter (fun e =>
      partSepScale P chain e.x e.y = ℓ ∧ e.s ∈ Sp.toFinset)
  else ∅

/-- Promoted sub-block index set `ℱ_p ⊆ {p + 1, ..., K_X}` of `V_{X, p}` (Section 4.6). -/
def promotedSubblockIndices {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : ℕ) (X : IntervalBlock) (p : ℕ) :
    Finset ℕ :=
  if h : 1 ≤ ℓ ∧ ℓ ≤ M then
    let subs := childSubblocks (chain ⟨ℓ, Nat.lt_succ_of_le h.2⟩) X
    let vset := vXp P proc chain ℓ X p
    (Finset.Icc (p + 1) subs.length).filter (fun b =>
      ∃ e ∈ vset, e.x ∈ (subblock1 subs b).toFinset)
  else ∅

/-- Lead-exit set `𝒩̃_p^(ℓ) ⊆ V_{X, p}` consisting, for each `b ∈ ℱ_p`, of the chronologically
first rotation in `V_{X, p}` whose promoted key lies in `S_b` (Section 4.6). -/
def leadExitSet {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : ℕ) (X : IntervalBlock) (p : ℕ) :
    Finset InternalPopRot :=
  if h : 1 ≤ ℓ ∧ ℓ ≤ M then
    let subs := childSubblocks (chain ⟨ℓ, Nat.lt_succ_of_le h.2⟩) X
    let vset := vXp P proc chain ℓ X p
    (promotedSubblockIndices P proc chain ℓ X p).biUnion (fun b =>
      let cands := vset.filter (fun e => e.x ∈ (subblock1 subs b).toFinset)
      cands.filter (fun e => ∀ e' ∈ cands,
        e.stepIdx < e'.stepIdx ∨ (e.stepIdx = e'.stepIdx ∧ e.j ≤ e'.j)))
  else ∅

/-- Trigger `POP` key `s(c) ∈ S_p` of the unique lead-exit rotation in `𝒩̃_p^(ℓ)` promoting a key
in `S_c` (`c ∈ ℱ_p`; Lemma 4.10(1)). -/
def leadPopKey {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : ℕ) (X : IntervalBlock) (p c : ℕ) : ℕ :=
  if h : 1 ≤ ℓ ∧ ℓ ≤ M then
    let subs := childSubblocks (chain ⟨ℓ, Nat.lt_succ_of_le h.2⟩) X
    let nset := (leadExitSet P proc chain ℓ X p).filter
      (fun e => e.x ∈ (subblock1 subs c).toFinset)
    nset.sup InternalPopRot.s
  else 0

/-- Fuel-bounded Cartesian BST builder on a sorted key list `xs` under priority `(insFn x, x)`. -/
def cartesianFromSortedGo (insFn : ℕ → ℕ) : ℕ → List ℕ → BinaryTree ℕ
  | 0, _ => .nil
  | _, [] => .nil
  | fuel + 1, x :: rest =>
    let xs := x :: rest
    let r := rest.foldl (fun best y =>
      if insFn y < insFn best ∨ (insFn y = insFn best ∧ y < best) then y else best) x
    .node r
      (cartesianFromSortedGo insFn fuel (xs.filter (· < r)))
      (cartesianFromSortedGo insFn fuel (xs.filter (r < ·)))

/-- Vuillemin Cartesian BST `Cart(S)` on finite key set `S ⊆ ℕ` forming a min-heap under `insFn`
(Lemma 4.9). -/
def cartesianBSTWith (insFn : ℕ → ℕ) (S : Finset ℕ) : BinaryTree ℕ :=
  let xs := (List.range (S.sup id + 1)).filter (· ∈ S)
  cartesianFromSortedGo insFn xs.length xs

/-- Plug each external leaf slot `(lo, hi)` of `H̃_τ` with `Cart(U_τ ∩ (lo, hi))` (Lemma 4.9). -/
def fillCartesianSlots (insFn : ℕ → ℕ) (U : Finset ℕ) (lo hi : Option ℕ) :
    BinaryTree ℕ → BinaryTree ℕ
  | .nil =>
    cartesianBSTWith insFn (U.filter (fun u =>
      lo.elim true (· < u) ∧ hi.elim true (u < ·)))
  | .node k l r =>
    .node k (fillCartesianSlots insFn U lo (some k) l)
            (fillCartesianSlots insFn U (some k) hi r)

/-- Insertion-time Cartesian extension `H̃*_τ` on `{s_0 + 1, ..., P}` at timestamp `τ`
(Lemma 4.9). -/
def cartesianExt {P : ℕ} (proc : FoldedPopProcess P) (τ : ℕ) : BinaryTree ℕ :=
  let s₀ := ((proc.steps.take τ).filter (fun | .pop _ => true | _ => false)).length
  let tree := proc.treeAt τ
  let U := Finset.Icc (s₀ + 1) P \ keyFinset tree
  fillCartesianSlots proc.insStep U none none tree

/-- Interval-restricted Cartesian extension `B_p(τ) = H̃*_τ|_{(R_p, max X]}` (Lemma 4.9). -/
noncomputable def phaseBlockBST {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : ℕ) (X : IntervalBlock) (p τ : ℕ) :
    BinaryTree ℕ :=
  if h : 1 ≤ ℓ ∧ ℓ ≤ M then
    let subs := childSubblocks (chain ⟨ℓ, Nat.lt_succ_of_le h.2⟩) X
    let Sp := subblock1 subs p
    restrictTree (cartesianExt proc τ) {u : ℕ | Sp.hi < u ∧ u ≤ X.hi}
  else .nil

/-- Phase `(K_X - p)`-node block-root summary BST `G^(p)(τ)` on `{p + 1, ..., K_X}` formed by
the preorder-`1` block roots `r_c(τ) = root(B_p(τ)|_{S_c})` relabeled to `c ∈ {p + 1, ..., K_X}`
(Lemma 4.9 & Lemma 4.10). -/
noncomputable def phaseSummaryBST {M : ℕ} (P : ℕ) (proc : FoldedPopProcess P)
    (chain : Fin (M + 1) → List IntervalBlock) (ℓ : ℕ) (X : IntervalBlock) (p τ : ℕ) :
    BinaryTree ℕ :=
  if h : 1 ≤ ℓ ∧ ℓ ≤ M then
    let subs := childSubblocks (chain ⟨ℓ, Nat.lt_succ_of_le h.2⟩) X
    let Bp := phaseBlockBST P proc chain ℓ X p τ
    let remBlocks := subs.drop p
    (preorderSummaryBST Bp remBlocks 1).map (subblockIndex1 subs)
  else .nil

/-- Embed a phase-`p` BST `G` on `{p + 1, ..., K_X}` into `{2, ..., K_X}` by attaching the
frozen right-spine prefix `2 →_R ... →_R p` with empty left subtrees above `G` (Lemma 4.9(2)). -/
def topEmbedPhase (p : ℕ) (G : BinaryTree ℕ) : BinaryTree ℕ :=
  (List.range' 2 (p - 1)).foldr (fun c acc => .node c .nil acc) G


/-!
================================================================================
7. Paper Section 5: Recursive Scale-Tree Builder `BuildScaleTree`
================================================================================
-/

/-- Base-depth (`δ = r - 1`, `q = 1`) greedy loop of `BuildScaleTree` (Section 5.2):
appends leaf scales while `S_cand ≤ S_curr / 2`, returning `(τ?, S_out, M_out)`. -/
noncomputable def buildScaleBaseLoop (W c S_curr M_curr : ℕ)
    (accLeaves : List ScaleTree) : Option ScaleTree × ℕ × ℕ :=
  let w_cand := 4 * c ^ 2 * W
  let i_cand := alpha0 (2 * S_curr) + 1
  let S_cand := w_cand * i_cand ^ 2
  if _h : 0 < S_cand ∧ 2 * S_cand ≤ S_curr then
    buildScaleBaseLoop W (c + 1) S_cand (M_curr + 1)
      (accLeaves ++ [ScaleTree.leaf (M_curr + 1)])
  else
    match accLeaves with
    | [] => (none, S_curr, M_curr)
    | _ :: _ => (some (ScaleTree.internal accLeaves), S_curr, M_curr)
termination_by S_curr
decreasing_by
  dsimp only [S_cand, w_cand, i_cand] at *
  omega

/-- Internal-depth (`q = r - δ ≥ 2`) child loop of `BuildScaleTree` (Section 5.2). -/
noncomputable def buildScaleInternalLoop
    (recurse : ℕ → ℕ → ℕ → Option ScaleTree × ℕ × ℕ)
    (W S_curr M_curr : ℕ) (accChildren : List ScaleTree) :
    List ℕ → Option ScaleTree × ℕ × ℕ
  | [] =>
    match accChildren with
    | [] => (none, S_curr, M_curr)
    | _ :: _ => (some (ScaleTree.internal accChildren), S_curr, M_curr)
  | c :: cs =>
    let (child?, S_next, M_next) := recurse (4 * c ^ 2 * W) S_curr M_curr
    match child? with
    | none =>
      match accChildren with
      | [] => (none, S_curr, M_curr)
      | _ :: _ => (some (ScaleTree.internal accChildren), S_curr, M_curr)
    | some child =>
      buildScaleInternalLoop recurse W S_next M_next (accChildren ++ [child]) cs

/-- `BuildScaleTree` indexed by remaining height `q = r - δ ∈ {1, ..., r}` (Section 5.2),
threading the global leaf counter `M_in ↦ M_out`. -/
noncomputable def buildScaleTreeAtQ : ℕ → ℕ → ℕ → ℕ → Option ScaleTree × ℕ × ℕ
  | 0, _, S_in, M_in => (none, S_in, M_in)
  | 1, W, S_in, M_in => buildScaleBaseLoop W 1 S_in M_in []
  | q' + 2, W, S_in, M_in =>
    let mStar := alphaHierarchy (q' + 2) S_in
    buildScaleInternalLoop (buildScaleTreeAtQ (q' + 1)) W S_in M_in []
      (List.range' 1 (2 * mStar))

/-- Full call `BuildScaleTree(δ, W, S_in)` at height parameter `r` (`δ ∈ {0, ..., r - 1}`),
threading global scale counter `M_in ↦ M_out` (Section 5.2). -/
noncomputable def buildScaleTreeCall (r δ W S_in M_in : ℕ) : Option ScaleTree × ℕ × ℕ :=
  if δ < r then buildScaleTreeAtQ (r - δ) W S_in M_in else (none, S_in, M_in)

/-- Output pair `(τ?, S_out)` of `BuildScaleTree(δ, W, S_in)` at height parameter `r`
(Section 5.2 & Lemma 5.2). -/
noncomputable def buildScaleTree (r δ W S_in : ℕ) : Option ScaleTree × ℕ :=
  let (τ?, S_out, _) := buildScaleTreeCall r δ W S_in 0
  (τ?, S_out)

/-- Root call `(τ_root?, S_out, M) = BuildScaleTree(0, 1, P)` at height `r` (Section 5.2). -/
noncomputable def buildScaleTreeRoot (r P : ℕ) : Option ScaleTree × ℕ × ℕ :=
  buildScaleTreeCall r 0 1 P 0


/-!
================================================================================
6. Paper Section 6: Dyadic Partition
================================================================================
-/

/-- Number of dyadic levels `M := ⌈log_2 max(P, 2)⌉ ≥ 1` (Proposition 6.1). -/
def dyadicScaleCount (P : ℕ) : ℕ :=
  Nat.clog 2 (max P 2)

/-- Bisect `X` into two contiguous sub-blocks of sizes `⌊|X| / 2⌋` and `⌈|X| / 2⌉` when
`|X| ≥ 2`, keeping singleton blocks `|X| ≤ 1` intact (Proposition 6.1). -/
def dyadicSplitBlock (X : IntervalBlock) : List IntervalBlock :=
  let sz := X.size
  if sz ≤ 1 then [X]
  else
    let half := sz / 2
    [⟨X.lo, X.lo + half - 1⟩, ⟨X.lo + half, X.hi⟩]

/-- Level `ℓ` of the dyadic partition of `{1, ..., P}` (Proposition 6.1). -/
def dyadicPartitionLevel (P : ℕ) : ℕ → List IntervalBlock
  | 0 => if P = 0 then [] else [⟨1, P⟩]
  | ℓ + 1 => (dyadicPartitionLevel P ℓ).flatMap dyadicSplitBlock

/-- Dyadic partition chain `𝒫_0 ≻ 𝒫_1 ≻ ... ≻ 𝒫_M` (`M = dyadicScaleCount P`;
Proposition 6.1). -/
def dyadicPartitionChain (P : ℕ) : Fin (dyadicScaleCount P + 1) → List IntervalBlock :=
  fun ℓ => dyadicPartitionLevel P ℓ.val

end SplayTree
