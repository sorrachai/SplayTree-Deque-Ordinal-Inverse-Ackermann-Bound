# Breaking All Iterated Inverse-Ackermann Bounds for the Deque Conjecture on Splay Trees

**Authors:** Goran Žužić, Sorrachai Yingchareonthawornchai, David P. Woodruff, and Vahab Mirrokni

Paper and complete Lean 4 (`v4.35.0`) formal verification of the $O\big((m + n)\,\alpha_\omega(m + n)\big)$ rotation upper bound for Tarjan's Deque Conjecture on splay trees, built on [AlgoLib (`v4.35.0`)](https://github.com/cslib-community/AlgoLib).

- **Paper (PDF):** [`paper/paper.pdf`](paper/paper.pdf) (LaTeX source: [`paper/main.tex`](paper/main.tex), [`paper/references.bib`](paper/references.bib))
- **Minimal Main Specification:** [`ChallengeMain.lean`](ChallengeMain.lean) (definitions: [`Challenge/MainDefinitions.lean`](Challenge/MainDefinitions.lean); proof: [`SolutionMain.lean`](SolutionMain.lean))
- **Full 28-Helper Blueprint:** [`ChallengeHelpers.lean`](ChallengeHelpers.lean) (definitions: [`Challenge/HelperDefinitions.lean`](Challenge/HelperDefinitions.lean); proof: [`SolutionHelpers.lean`](SolutionHelpers.lean))

## Paper ↔ Lean 4 Correspondence

Every numbered proposition, lemma, and theorem in [`paper/paper.pdf`](paper/paper.pdf) matches its Lean 4 declaration 1-to-1:

| Paper Section | Verified Statements | Blueprint & Proof Modules |
| :--- | :--- | :--- |
| **§1 & App. A** (Main theorem & $\alpha_\omega$) | Theorem 1.4 (`thm_1_4_main`, `deque_ordinal_omega_ackermann_bound`), Prop. 1.3 (`prop_1_3_omega_properties`), Lemma A.1 (`lem_A_1_ack_basic`), Prop. A.2 (`prop_A_2_lob_wainer`) | [`ChallengeMain.lean`](ChallengeMain.lean), [`ChallengeHelpers.lean`](ChallengeHelpers.lean), [`Solution/TopAssembly.lean`](Solution/TopAssembly.lean), [`Solution/Ackermann.lean`](Solution/Ackermann.lean) |
| **§2 & App. B** (Folded $\textsc{Pop}$ reduction) | Theorem 2.2 (`thm_2_2_mod1_reduction`), Lemmas 2.3–2.8 (`lem_2_3_bst_projection`–`lem_2_8_folded_laws`) | [`Solution/EmptyingMod1.lean`](Solution/EmptyingMod1.lean), [`Solution/BSTProjections.lean`](Solution/BSTProjections.lean), [`Solution/KeyAssignmentSpine.lean`](Solution/KeyAssignmentSpine.lean), [`Solution/FoldedLaws.lean`](Solution/FoldedLaws.lean) |
| **§3 & App. C** (Bounded-gap cascades) | Theorem 3.1 (`thm_3_1_mod2_cascade`), Prop. 3.2 (`prop_3_2_right_reach`), Lemmas 3.3–3.4 (`lem_3_3_preorder_global`, `lem_3_4_cascade_potentials`) | [`Solution/Cascades.lean`](Solution/Cascades.lean), [`Solution/TamariPreorder.lean`](Solution/TamariPreorder.lean) |
| **§4** (Scale-tree contraction pass) | Theorem 4.2 (`thm_4_2_mod3_pass`), Lemmas 4.3–4.12 (`lem_4_3_tree_weights`–`lem_4_12_bucket_b2`) | [`Solution/ScaleWeights.lean`](Solution/ScaleWeights.lean), [`Solution/BucketLeafB1.lean`](Solution/BucketLeafB1.lean), [`Solution/BucketB3PostEscape.lean`](Solution/BucketB3PostEscape.lean), [`Solution/BucketB3GapsExit.lean`](Solution/BucketB3GapsExit.lean), [`Solution/BucketB2Pass.lean`](Solution/BucketB2Pass.lean) |
| **§5** ($\textsc{BuildScaleTree}$ & master bound) | Theorem 5.1 (`thm_5_1_mod4_contraction`), Lemma 5.2 (`lem_5_2_build_scale_tree`) | [`Solution/Contraction.lean`](Solution/Contraction.lean), [`Solution/TopAssembly.lean`](Solution/TopAssembly.lean) |
| **§6** (Dyadic partition) | Prop. 6.1 (`prop_6_1_dyadic_collapse`) | [`Solution/ScaleWeights.lean`](Solution/ScaleWeights.lean) |

Neither `SolutionMain` nor `SolutionHelpers` imports `ChallengeMain` or `ChallengeHelpers`.

## Repository Layout

```text
paper/
  paper.pdf                    Compiled manuscript (62 pages)
  main.tex                     LaTeX source of the manuscript
  references.bib               BibTeX bibliography (47 entries)
ChallengeMain.lean             Minimal main challenge (Theorem 1.4 + BST ℤ bound)
ChallengeHelpers.lean          Helper blueprint (all 28 propositions, lemmas, theorems)
Challenge/
  MainDefinitions.lean         Minimal splay-deque & α_ω definitions using AlgoLib
  HelperDefinitions.lean       Intermediate helper structures & predicates (Secs 1–6, App A)
  Definitions.lean             Shared re-export of MainDefinitions + HelperDefinitions
SolutionMain.lean              Proves both main theorems in ChallengeMain
SolutionHelpers.lean           Proves all 28 helper theorems in ChallengeHelpers
Solution/                      Modular proof development (16 modules, ~61.5K LOC)
CheckSolution.lean             Axiom and import audit across all 30 proved theorems
comparator.json                Comparator config (ChallengeMain vs SolutionMain)
comparator_helpers.json        Comparator config (ChallengeHelpers vs SolutionHelpers)
```

## Build & Verify

Requires [Lean `4.35.0`](https://lean-lang.org/install/) (configured automatically via [`lean-toolchain`](lean-toolchain)):

```sh
git clone https://github.com/sorrachai/SplayTree-Deque-Ordinal-Inverse-Ackermann-Bound.git
cd SplayTree-Deque-Ordinal-Inverse-Ackermann-Bound
lake update
lake exe cache get
lake build
```

To replay the proofs in Lean's external kernel (`leanchecker`) via `comparator` (requires Linux `bubblewrap`; pass `--inadvisably-no-sandbox` on macOS for trusted local builds) and run the axiom/import audit:

```sh
# Minimal main challenge (ChallengeMain vs SolutionMain):
lake comparator

# All 28 helper theorems (ChallengeHelpers vs SolutionHelpers):
lake comparator --config=comparator_helpers.json

# Standard axioms (propext, Quot.sound, Classical.choice) and zero blueprint imports:
lake env lean -DwarningAsError=true CheckSolution.lean
```
