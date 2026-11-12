# Splay-tree deque ordinal inverse-Ackermann bound

A Lean 4 formalization of *Breaking All Iterated Inverse-Ackermann Bounds for the
Deque Conjecture on Splay Trees*, built directly on the binary-tree, BST, and
bottom-up splay definitions from
[AlgoLib](https://github.com/cslib-community/AlgoLib).

The specification is split into two independent challenge blueprints:

1. **`ChallengeMain.lean`** (importing only minimal `Challenge/MainDefinitions.lean`):
   states the main deletion-sensitive bound (`thm_1_4_main`, Theorem 1.4) over any
   `LinearOrder α` and the standalone `BST ℤ` benchmark theorem
   (`deque_ordinal_omega_ackermann_bound`), with zero helper proof machinery.
2. **`ChallengeHelpers.lean`** (importing `Challenge/HelperDefinitions.lean`):
   states all **28** intermediate Propositions, Lemmas, and reduction Theorems across
   Sections 1–6 and Appendix A (`prop_1_3_omega_properties`, `thm_2_2_mod1_reduction`,
   `lem_2_3_bst_projection`–`lem_2_8_folded_laws`, `thm_3_1_mod2_cascade`,
   `prop_3_2_right_reach`–`lem_3_4_cascade_potentials`, `thm_4_2_mod3_pass`,
   `lem_4_3_tree_weights`–`lem_4_12_bucket_b2`, `thm_5_1_mod4_contraction`,
   `lem_5_2_build_scale_tree`, `prop_6_1_dyadic_collapse`, `lem_A_1_ack_basic`,
   `prop_A_2_lob_wainer`).

## Build

Install [Lean and its editor support](https://lean-lang.org/install/), then clone
this repository:

```sh
git clone https://github.com/sorrachai/SplayTree-Deque-Ordinal-Inverse-Ackermann-Bound.git
cd SplayTree-Deque-Ordinal-Inverse-Ackermann-Bound
lake update
lake exe cache get
lake build
```

The project uses Lean **4.35.0** and AlgoLib **v4.35.0**.

## Project layout

```text
ChallengeMain.lean             Minimal main challenge (Theorem 1.4 + benchmark bound)
ChallengeHelpers.lean          Helper blueprint (all 28 propositions, lemmas, theorems)
Challenge/
  MainDefinitions.lean         Minimal splay-deque & α_ω definitions using AlgoLib
  HelperDefinitions.lean       Intermediate helper structures & predicates (Secs 1–6, App A)
  Definitions.lean             4-line re-export of MainDefinitions + HelperDefinitions
SolutionMain.lean              Proves both main theorems in ChallengeMain
SolutionHelpers.lean           Proves all 28 helper theorems in ChallengeHelpers
Solution/
  Ackermann.lean               Ackermann hierarchy, α_ω, and Löb–Wainer comparison (Sec 1, App A)
  BSTProjections.lean          Subtree/key-set BST projections and cascade simulation (Sec 2.2)
  KeyAssignmentSpine.lean      Offline three-way key partition and spine accounting (Sec 2.3)
  EmptyingMod1.lean            Emptying simulation, spine folding, and Theorem 2.2 (Sec 2.1, 2.4)
  FoldedLaws.lean              Folded POP process invariants and rotation laws (Sec 2.4)
  TamariPreorder.lean          Right-reach characterization and preorder-D summaries (Sec 3.2)
  Cascades.lean                Bounded-gap right cascades and left-depth potentials (Sec 3.1, 3.3)
  ScaleWeights.lean            Height-r scale-tree weights and dyadic collapse (Sec 4.2, Sec 6)
  BucketLeafB1.lean            Intra-leaf, coarse-trigger B1, and intra-block B3 bounds (Sec 4.3–4.5)
  BucketB3PostEscape.lean      Post-depletion exits, lead exits, and phase summaries (Sec 4.6)
  BucketB3GapsExit.lean        Spine-run gap witnesses and B3 exit bound (Sec 4.6)
  BucketB2Pass.lean            Fine-trigger B2 routing and scale-tree pass Theorem 4.2 (Sec 4.7)
  Contraction.lean             BuildScaleTree and degree-6 contraction Theorem 5.1 (Sec 5.1–5.3)
  TopAssembly.lean             Three-pass proof of Theorem 1.4 and (m + n) α_ω bound (Sec 5.4)
  TreeFacts.lean               Structural induction facts for AlgoLib trees/BSTs
  DirectProof.lean             Auxiliary BST and cascade lemmas over AlgoLib trees
CheckSolution.lean             Axiom and import audit of all 30 proved theorems
comparator.json                Main comparator config (ChallengeMain vs SolutionMain)
comparator_helpers.json        Helper comparator config (ChallengeHelpers vs SolutionHelpers)
```

Neither `SolutionMain` nor `SolutionHelpers` imports `ChallengeMain` or `ChallengeHelpers`.

## Verification with Comparator and `CheckSolution`

Run from the repository root (with Linux `bubblewrap` installed; pass
`--inadvisably-no-sandbox` on macOS for trusted local builds):

```sh
# Verify the minimal main challenge (ChallengeMain vs SolutionMain):
lake comparator

# Verify all 28 helper theorems (ChallengeHelpers vs SolutionHelpers):
lake comparator --config=comparator_helpers.json

# Verify standard axioms and zero blueprint imports across all 30 theorems:
lake env lean -DwarningAsError=true CheckSolution.lean
```

Comparator checks statement and transitive definition identity, enforces standard
axioms (`propext`, `Quot.sound`, `Classical.choice`), and replays the exported
proofs in Lean's external kernel (`leanchecker`). Exit code **0** means accepted.
