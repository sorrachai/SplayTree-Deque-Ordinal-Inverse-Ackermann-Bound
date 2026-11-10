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

## Challenge status

`deque_ordinal_omega_ackermann_bound` is the supplied target theorem. Its proof
still contains the original `sorry`. A successful build checks that the file
elaborates; it does not prove the bound or the asymptotic comparisons described
in the challenge.

## Reused definitions

`Challenge.lean` imports `AlgoLib.DataStructures.SplayTree.Complexity`, which
provides the existing binary tree, BST invariant, bottom-up splay operation and
rotation cost. It keeps the challenge's deque operations, operation sequences,
Ackermann hierarchy and theorem statement.

The adaptation uses AlgoLib's `.nil` empty constructor and `.node key left right`
argument order. Deque insertion preconditions use `∀ k ∈ t, ...` over AlgoLib's
tree membership relation. The BST invariant comes from AlgoLib's `BST` type.
