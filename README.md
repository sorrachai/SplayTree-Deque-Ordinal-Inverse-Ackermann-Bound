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
Open the repository folder in VS Code to work on `Solution.lean`.

## Project layout

```text
Challenge.lean                 Independent reference statement (intentional sorry)
Challenge/
  Definitions.lean             Shared definitions using AlgoLib
Solution.lean                  Completed theorem and explicit bound
Solution/
  TreeFacts.lean               Structural induction facts for AlgoLib trees/BSTs
  DirectProof.lean             Full proof directly over the shared definitions
CheckSolution.lean             Axiom audit of the completed theorem
comparator.json                Comparator modules, theorem, and allowed axioms
```

`Challenge` and `Solution` are separate environments with the same theorem name,
`deque_ordinal_omega_ackermann_bound`. They both use `Challenge.Definitions`;
the solution never imports the reference theorem. Import **`Solution`** when
using the proved result. Do not import both root modules in one Lean file,
because they intentionally declare the same name.

## Comparator check

Run from the repository root. On this Mac, for this trusted local project:

```sh
lake comparator --inadvisably-no-sandbox
```

The flag disables Comparator's Linux-only `bubblewrap` sandbox. Use it only for
code you trust. On Linux with `bubblewrap` installed and configured, use the
sandboxed command:

```sh
lake comparator
```

Both commands read `comparator.json` and build the required modules. Comparator
compares the theorem statements and their referenced definitions, rejects
solution axioms outside `propext`, `Quot.sound`, and `Classical.choice`, and
rechecks the exported proof with Lean's kernel. Exit code **0** means accepted.
See Lean's [proof validation documentation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

The `sorry` warning from `Challenge.lean` is intentional: it is the reference
proof hole, not part of the solution. `sorryAx` is **not** permitted in the
solution. A successful `lake build` alone is not a comparator verdict.

For additional checking with all external kernels bundled with Lean, add
`--paranoid` to the applicable command above; this can take longer.

## Solution

`Challenge.lean` retains the supplied target theorem statement as an independent
reference. `Solution.lean` proves that same statement and gives the explicit
constant **5757** using the AlgoLib-based definitions.

`Solution/DirectProof.lean` carries out the combinatorial argument directly on
AlgoLib's `BinaryTree`, `BST`, splay operation and rotation cost, using the shared
deque and inverse-Ackermann definitions from `Challenge/Definitions.lean`.
It introduces no replacement tree datatype and does not convert the input tree
to a legacy model. The proof retains the reductions to core operation sequences,
the cascade estimates, and the ordinal-ω contraction argument.

`Solution/TreeFacts.lean` supplies structural induction lemmas for AlgoLib's
bounded BST invariant and an auxiliary `ForallTree` predicate equivalent to
quantification over tree membership. All these facts concern the existing tree
type. The proof uses Lean's backward compatibility options for tactic
elaboration; the resulting proof terms are checked by Lean's kernel.

After building, check the theorem's full axiom dependency closure with:

```sh
lake env lean CheckSolution.lean
```

This check rejects legacy proof/conversion imports, `sorryAx`, and any axiom
other than Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Reused definitions

`Challenge/Definitions.lean` imports `AlgoLib.DataStructures.SplayTree.Complexity`, which
provides the existing binary tree, BST invariant, bottom-up splay operation and
rotation cost. It defines the challenge's deque operations, operation sequences,
and Ackermann hierarchy.

The adaptation uses AlgoLib's `.nil` empty constructor and `.node key left right`
argument order. Deque insertion preconditions use `∀ k ∈ t, ...` over AlgoLib's
tree membership relation. The BST invariant comes from AlgoLib's `BST` type.
