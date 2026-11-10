# Splay-tree deque ordinal inverse-Ackermann bound

A Lean formulation of the ordinal-ω inverse-Ackermann deque-bound challenge,
using the existing binary-tree and splay definitions from
[AlgoLib](https://github.com/cslib-community/AlgoLib).

## Build

Install [Lean and its editor support](https://lean-lang.org/install/), then clone
this private repository using a GitHub account with access:

```sh
git clone https://github.com/sorrachai/SplayTree-Deque-Ordinal-Inverse-Ackermann-Bound.git
cd SplayTree-Deque-Ordinal-Inverse-Ackermann-Bound
lake update
lake exe cache get
lake build
```

The project uses Lean **4.35.0** and AlgoLib's **v4.35.0** release. The committed
`lake-manifest.json` records the resolved dependency commits. For subsequent
builds using that manifest, run `lake exe cache get` followed by `lake build`.
Open the repository folder in VS Code to work on `Challenge.lean`.

## Solution

`Challenge.lean` retains the supplied target theorem statement and obtains its
proof from `Solution.lean`. The solution gives the explicit constant **5757**
using the AlgoLib-based definitions.

The supplied long proof is preserved in `Solution/LegacyProof.lean`, under the
`SplayDeque.Legacy` namespace. Its original tree model is kept in
`Solution/LegacyDefinitions.lean`. `Solution/Bridge.lean` proves that converting
AlgoLib trees to that model preserves the BST invariant, deque operations,
sequence validity, rotation costs, and the inverse-Ackermann function. The public
theorem is therefore about AlgoLib's types and operations.

The legacy proof explicitly qualifies its `BinaryTree` references to avoid a
name collision with Mathlib. It also enables Lean's backward compatibility
options for elaboration and simplification; the proof terms are still checked
by Lean's kernel. Its `dsimp` steps tolerate already-normalized goals, and a few
rewrites now explicitly unfold definitions or normalize successor expressions.

After building, check the theorem's full axiom dependency closure with:

```sh
lake env lean CheckSolution.lean
```

This check rejects `sorryAx` and any axiom other than Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.

## Reused definitions

`Challenge/Definitions.lean` imports `AlgoLib.DataStructures.SplayTree.Complexity`, which
provides the existing binary tree, BST invariant, bottom-up splay operation and
rotation cost. It keeps the challenge's deque operations, operation sequences,
Ackermann hierarchy and theorem statement.

The adaptation uses AlgoLib's `.nil` empty constructor and `.node key left right`
argument order. Deque insertion preconditions use `∀ k ∈ t, ...` over AlgoLib's
tree membership relation. The BST invariant comes from AlgoLib's `BST` type.
