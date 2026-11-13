import ChallengeStandalone
import SolutionMain

/-!
# `ChallengeStandalone.lean` states the same theorem as `ChallengeMain.lean`

`ChallengeStandalone.lean` (printed as Appendix D of the paper) restates Theorem 1.4 in 82
self-contained lines inside `namespace SplayDeque`. This file proves that its statement is
equivalent to the statement of `thm_1_4_main` in `ChallengeMain.lean`, which `SolutionMain.lean`
proves, and hence that it holds.
-/

namespace SplayDeque

/-- Translate a standalone deque operation into the repository's `SplayTree.DequeOp`. -/
def toRepo {α : Type} : DequeOp α → SplayTree.DequeOp α
  | .pop => .pop | .push x => .push x | .eject => .eject | .inject x => .inject x

/-- Inverse translation. -/
def ofRepo {α : Type} : SplayTree.DequeOp α → DequeOp α
  | .pop => .pop | .push x => .push x | .eject => .eject | .inject x => .inject x

theorem toRepo_ofRepo {α : Type} (o : SplayTree.DequeOp α) : toRepo (ofRepo o) = o := by
  cases o <;> rfl

theorem minKey_eq {α : Type} (t : BinaryTree α) : minKey? t = BinaryTree.minKey? t := by
  induction t with
  | nil => rfl
  | node k l _ ihl _ =>
    dsimp [minKey?, BinaryTree.minKey?]; rw [ihl]; cases BinaryTree.minKey? l <;> rfl

theorem maxKey_eq {α : Type} (t : BinaryTree α) : maxKey? t = BinaryTree.maxKey? t := by
  induction t with
  | nil => rfl
  | node k _ r _ ihr =>
    dsimp [maxKey?, BinaryTree.maxKey?]; rw [ihr]; cases BinaryTree.maxKey? r <;> rfl

theorem step_eq {α : Type} [LinearOrder α] (t : BinaryTree α) (op : DequeOp α) :
    op.step t = (toRepo op).step t := by
  cases op <;> dsimp [DequeOp.step, toRepo, SplayTree.DequeOp.step,
    SplayTree.pop, SplayTree.push, SplayTree.eject, SplayTree.inject]
  · rw [minKey_eq]; cases BinaryTree.minKey? t <;> rfl
  · rw [maxKey_eq]; cases BinaryTree.maxKey? t <;> rfl

theorem cost_eq {α : Type} [LinearOrder α] (t : BinaryTree α) (op : DequeOp α) :
    op.cost t = (toRepo op).cost t := by
  cases op <;> dsimp [DequeOp.cost, toRepo, SplayTree.DequeOp.cost,
    SplayTree.popCost, SplayTree.ejectCost]
  · rw [minKey_eq]; cases BinaryTree.minKey? t <;> rfl
  · rw [maxKey_eq]; cases BinaryTree.maxKey? t <;> rfl

theorem valid_iff {α : Type} [LinearOrder α] (t : BinaryTree α) (op : DequeOp α) :
    op.Valid t ↔ (toRepo op).Valid t := by
  cases op <;> rfl

theorem dequeSeq_eq {α : Type} [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) (i : Fin (m + 1)) :
    dequeSeq init ops i = SplayTree.dequeSeq init (fun j => toRepo (ops j)) i := by
  rcases i with ⟨v, hv⟩
  dsimp [dequeSeq, SplayTree.dequeSeq]
  induction v with
  | zero => rfl
  | succ j ih =>
    dsimp only
    split_ifs with h
    · rw [ih (Nat.lt_of_succ_lt hv), step_eq]
    · exact ih (Nat.lt_of_succ_lt hv)

theorem validDequeSeq_iff {α : Type} [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) :
    ValidDequeSeq init ops ↔ SplayTree.ValidDequeSeq init (fun j => toRepo (ops j)) := by
  constructor
  · intro h i; rw [← dequeSeq_eq, ← valid_iff]; exact h i
  · intro h i; rw [valid_iff, dequeSeq_eq]; exact h i

theorem dequeSequenceCost_eq {α : Type} [LinearOrder α] {m : ℕ} (init : BinaryTree α)
    (ops : Fin m → DequeOp α) :
    dequeSequenceCost init ops =
      SplayTree.dequeSequenceCost init (fun j => toRepo (ops j)) :=
  Finset.sum_congr rfl fun i _ => by rw [dequeSeq_eq, cost_eq]

theorem popCount_eq {α : Type} {m : ℕ} (ops : Fin m → DequeOp α) :
    popCount ops = SplayTree.popCount (fun j => toRepo (ops j)) := by
  dsimp [popCount, SplayTree.popCount]; congr 1; ext i; simp; cases ops i <;> rfl

theorem ejectCount_eq {α : Type} {m : ℕ} (ops : Fin m → DequeOp α) :
    ejectCount ops = SplayTree.ejectCount (fun j => toRepo (ops j)) := by
  dsimp [ejectCount, SplayTree.ejectCount]; congr 1; ext i; simp; cases ops i <;> rfl

theorem ackermann_eq : ackermann = SplayTree.ackermann := by
  funext i j
  induction i generalizing j with
  | zero => rfl
  | succ i ih =>
    cases i with
    | zero => rfl
    | succ i =>
      dsimp [ackermann, SplayTree.ackermann]
      have hstep : ∀ f g : ℕ → ℕ, f = g →
          ∀ m, ackermannStep f m = SplayTree.ackermannStep g m := by
        intro f g hfg m; subst hfg
        induction m with
        | zero => rfl
        | succ m ihm =>
          cases m with
          | zero => rfl
          | succ m => simp [ackermannStep, SplayTree.ackermannStep, ihm]
      exact hstep _ _ (funext (ih ·)) j

theorem alpha0_eq : alpha0 = SplayTree.alpha0 := by
  funext n; simp [alpha0, SplayTree.alpha0, SplayTree.invAckermann, ackermann_eq]

theorem starIterate_eq (f : ℕ → ℕ) : starIterate f = SplayTree.starIterate f := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [starIterate, SplayTree.starIterate]
    split_ifs with h1 h2
    · rfl
    · rw [ih (f n) h2]
    · rfl

theorem alphaHierarchy_eq : alphaHierarchy = SplayTree.alphaHierarchy := by
  funext r
  induction r with
  | zero => exact alpha0_eq
  | succ r ih =>
    show starIterate (alphaHierarchy r) = SplayTree.starIterate (SplayTree.alphaHierarchy r)
    rw [ih, starIterate_eq]

theorem alphaOmega_eq : alphaOmega = SplayTree.alphaOmega := by
  funext n; simp [alphaOmega, SplayTree.alphaOmega, alphaHierarchy_eq]

/-- The statement of `ChallengeStandalone.lean` is equivalent to the statement of
`thm_1_4_main` in `ChallengeMain.lean` / `SolutionMain.lean`. -/
theorem thm_1_4_main_iff :
    (type_of% SplayDeque.thm_1_4_main) ↔ (type_of% _root_.thm_1_4_main) := by
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun {α} _ n m init ops' hn hval => ?_⟩
    obtain ⟨ops, rfl⟩ : ∃ ops : Fin m → DequeOp α, (fun j => toRepo (ops j)) = ops' :=
      ⟨fun j => ofRepo (ops' j), funext fun j => toRepo_ofRepo _⟩
    have key := h n m init ops hn ((validDequeSeq_iff init.tree ops).2 hval)
    rwa [dequeSequenceCost_eq, popCount_eq, ejectCount_eq, alphaOmega_eq] at key
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun {α} _ n m init ops hn hval => ?_⟩
    rw [dequeSequenceCost_eq, popCount_eq, ejectCount_eq, alphaOmega_eq]
    exact h n m init (fun j => toRepo (ops j)) hn ((validDequeSeq_iff init.tree ops).1 hval)

/-- Hence the statement of `ChallengeStandalone.lean` holds. -/
theorem thm_1_4_main_standalone : type_of% SplayDeque.thm_1_4_main :=
  thm_1_4_main_iff.2 _root_.thm_1_4_main

end SplayDeque

/--
info: 'SplayDeque.thm_1_4_main_standalone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms SplayDeque.thm_1_4_main_standalone
