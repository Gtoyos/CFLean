import CFLeanProof.FiniteScheduling

/-! Operation-level infinite executions. Time indexes operation steps; invocation
and response times delimit half-open pending intervals. Register-level refinement
is deliberately separate (SharedMemory.lean). -/
namespace ConflictFreedom

/-- An infinite operation-level execution.

`actor` is **partial**: at an instant where no operation is running -- the
instant right after a response is recorded, for instance -- no instance takes a
step.  A total `actor` would force every instant to be covered by some pending
operation, which no one-process run that completes an operation satisfies: the
process is idle for an instant after its response.  `live` is the manuscript's
standing assumption that the execution is infinite. -/
structure Execution (n : Nat) (Op : Type) where
  Instance : Type
  operation : Instance → Op
  owner : Instance → Fin n
  invoked : Instance → Nat
  returned : Instance → Option Nat
  actor : Nat → Option Instance
  live : ∀ N, ∃ t i, N ≤ t ∧ actor t = some i
  return_after : ∀ i r, returned i = some r → invoked i < r
  step_invoked : ∀ t i, actor t = some i → invoked i ≤ t
  step_pending : ∀ t i r, actor t = some i → returned i = some r → t < r
  sequential : ∀ i j t, owner i = owner j → invoked i ≤ t → invoked j ≤ t →
    (∀ r, returned i = some r → t < r) →
    (∀ r, returned j = some r → t < r) → i = j

namespace Execution
variable {n : Nat} {Op : Type} (e : Execution n Op)

/-- **There is no execution without processes**: some instance takes a step at
arbitrarily late times (`live`), and every instance belongs to a process.  So
with `n = 0` every implementation is empty and every statement about its
executions holds vacuously; the non-emptiness theorems are for `n = m + 1`. -/
theorem false_of_zero (e : Execution 0 Op) : False := by
  obtain ⟨_, i, -, -⟩ := e.live 0
  exact (e.owner i).elim0

/-- The instance has a matching response. -/
def Completes (i : e.Instance) : Prop := ∃ r, e.returned i = some r

/-- The instance is invoked by time `t` and has not returned by then. -/
def Pending (i : e.Instance) (t : Nat) : Prop :=
  e.invoked i ≤ t ∧ ∀ r, e.returned i = some r → t < r

/-- `p` takes infinitely many operation steps. -/
def InfiniteSteps (p : Fin n) : Prop :=
  ∀ N, ∃ t i, N ≤ t ∧ e.actor t = some i ∧ e.owner i = p

/-- An idle process is correct, as in the paper's definition. -/
def Correct (p : Fin n) : Prop :=
  e.InfiniteSteps p ∨ ∀ i, e.owner i = p → e.Completes i

/-- The manuscript's "eventually step-contention free": either the instance
completes, or there is a suffix in which no *other* instance takes a step.
Instants at which nothing runs are allowed. -/
def Solo (i : e.Instance) : Prop :=
  e.Completes i ∨ ∃ N, ∀ t j, N ≤ t → e.actor t = some j → j = i

/-- The manuscript's "eventually conflict-free": from some time on, no two
distinct instances pending at a common time — concurrent — conflict. -/
def EventuallyConflictFree (conflict : Op → Op → Prop) : Prop :=
  ∃ N, ∀ t, N ≤ t → ∀ i j, i ≠ j → e.Pending i t → e.Pending j t →
    ¬ conflict (e.operation i) (e.operation j)

/-- Infinite operation steps among finitely many processes imply that a process
steps infinitely often. No fairness or bound on crash failures is assumed. -/
theorem exists_infiniteSteps : ∃ p, e.InfiniteSteps p := by
  classical
  apply Classical.byContradiction
  intro h
  have bounds : ∀ p, ∃ N, ∀ t i, N ≤ t → e.actor t = some i → e.owner i ≠ p := by
    intro p
    have hp : ¬ e.InfiniteSteps p := fun hp => h ⟨p, hp⟩
    obtain ⟨N, hN⟩ := Classical.not_forall.mp hp
    refine ⟨N, ?_⟩
    intro t i ht hact he
    exact hN ⟨t, i, ht, hact, he⟩
  let f := fun p => Classical.choose (bounds p)
  obtain ⟨N, hN⟩ := fin_bounded n f
  obtain ⟨t, i, ht, hact⟩ := e.live N
  exact Classical.choose_spec (bounds (e.owner i)) t i
    (Nat.le_trans (hN (e.owner i)) ht) hact rfl

theorem exists_correct : ∃ p, e.Correct p := by
  obtain ⟨p, hp⟩ := e.exists_infiniteSteps
  exact ⟨p, Or.inl hp⟩

theorem empty_eventuallyConflictFree : e.EventuallyConflictFree (fun _ _ => False) :=
  ⟨0, fun _ _ _ _ _ _ _ h => h⟩

/-- With universal conflict, an uncompleted operation excludes every other
operation from the conflict-free suffix, hence runs solo. -/
theorem universal_solo (h : e.EventuallyConflictFree (fun _ _ => True)) (i : e.Instance) :
    e.Solo i := by
  classical
  by_cases hc : e.Completes i
  · exact Or.inl hc
  · right
    obtain ⟨N, hN⟩ := h
    refine ⟨max N (e.invoked i), ?_⟩
    intro t j ht hact
    apply Classical.byContradiction
    intro hne
    have pi : e.Pending i t := ⟨Nat.le_trans (Nat.le_max_right _ _) ht,
      fun r hr => False.elim (hc ⟨r, hr⟩)⟩
    have pa : e.Pending j t := ⟨e.step_invoked t j hact, fun r hr => e.step_pending t j r hact hr⟩
    exact hN t (Nat.le_trans (Nat.le_max_left _ _) ht) j i hne pa pi trivial

end Execution
end ConflictFreedom
