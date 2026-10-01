import CFLeanProof.Progress
import CFLeanProof.Sequential

/-! Why the §3 definitions read as they do.  Each example rules out a tempting
alternative reading.

* `intermittentlyStalled`: a solo operation with infinitely many steps need not
  be scheduled continuously, so `Solo` cannot be read as continuous scheduling.
* `stalled`: an idle correct process does not witness lock-freedom, which asks
  for a process taking infinitely many steps.
* `alternating`: weak conflict-freedom with *some correct process* in place of
  *some process taking infinitely many steps* (`IdleWeakConflictFree`) is met
  by an idle process, so for the empty conflict relation it does not reduce to
  lock-freedom as Proposition `prop:cf-degenerate` requires.
* `counter`: equivalent schedules can visit different intermediate states, so
  a trace determines responses, not state sequences.
-/
namespace ConflictFreedom.Counterexamples

/-- One pending operation takes infinitely many steps, separated by idle
instants. This is permitted by the partial-actor execution model. -/
def intermittentlyStalled : Execution 1 Unit where
  Instance := Unit
  operation := fun _ => ()
  owner := fun _ => 0
  invoked := fun _ => 0
  returned := fun _ => none
  actor := fun t => if t % 2 = 0 then some () else none
  live := by
    intro N
    refine ⟨2 * N, (), by omega, ?_⟩
    simp
  return_after := by intros; contradiction
  step_invoked := fun _ _ _ => Nat.zero_le _
  step_pending := by intros; contradiction
  sequential := by intros; rfl

theorem intermittentlyStalled_solo : intermittentlyStalled.Solo () :=
  Or.inr ⟨0, fun _ j _ _ => by cases j; rfl⟩

/-- Even with one process, `Solo` and infinite activity do not imply continuous
scheduling. A counting argument about other processes cannot close this gap. -/
theorem intermittentlyStalled_not_continuously_scheduled :
    ¬ ∃ N, ∀ t, N ≤ t → intermittentlyStalled.actor t = some () := by
  rintro ⟨N, hN⟩
  have h := hN (2 * N + 1) (by omega)
  simp [intermittentlyStalled] at h

/-- Process 0 spins forever on one operation; process 1 stays idle. -/
def stalled : Execution 2 Unit where
  Instance := Unit
  operation := fun _ => ()
  owner := fun _ => 0
  invoked := fun _ => 0
  returned := fun _ => none
  actor := fun _ => some ()
  live := fun N => ⟨N, (), Nat.le_refl _, rfl⟩
  return_after := by intros; contradiction
  step_invoked := fun _ _ _ => Nat.zero_le _
  step_pending := by intros; contradiction
  sequential := by intros; rfl

/-- The implementation whose only execution is `stalled`. -/
def stalledImplementation : Implementation 2 Unit := fun e => e = stalled

theorem idle_correct : stalled.Correct 1 := by
  right
  intro i hi
  have : (0 : Fin 2) = 1 := hi
  contradiction

theorem stalled_not_obstructionFree : ¬ ObstructionFree stalledImplementation := by
  intro h
  have correct : stalled.Correct 0 := Or.inl (fun N => ⟨N, (), Nat.le_refl _, rfl, rfl⟩)
  have solo : stalled.Solo () := Or.inr ⟨0, fun _ _ _ _ => rfl⟩
  obtain ⟨r, hr⟩ := h stalled rfl () correct solo
  cases hr

/-- The idle process `1` is correct, but it does not make `stalled` lock-free. -/
theorem stalled_not_lockFree : ¬ LockFree stalledImplementation :=
  fun h => stalled_not_obstructionFree (lockFree_obstructionFree h)

/-- Weak conflict-freedom read with *some correct process* in place of *some
process taking infinitely many steps*.  An idle process is correct. -/
def IdleWeakConflictFree {n : Nat} {Op : Type} (A : Implementation n Op)
    (conflict : Op → Op → Prop) : Prop :=
  ObstructionFree A ∧ ∀ e, A e → e.EventuallyConflictFree conflict →
    ∃ p, e.Correct p ∧ ∀ i, e.owner i = p → e.Completes i

/-- It is weaker than weak conflict-freedom… -/
theorem weakConflictFree_idleWeakConflictFree {n : Nat} {Op : Type} {A : Implementation n Op}
    {conflict : Op → Op → Prop} (h : WeakConflictFree A conflict) :
    IdleWeakConflictFree A conflict := by
  refine ⟨h.1, ?_⟩
  intro e he hc
  obtain ⟨p, hp, hall⟩ := h.2 e he hc
  exact ⟨p, Or.inl hp, hall⟩

/-- Two active processes alternate forever; a third process is idle. -/
def alternating : Execution 3 Unit where
  Instance := Fin 2
  operation := fun _ => ()
  owner := fun i => ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩
  invoked := fun _ => 0
  returned := fun _ => none
  actor := fun t => some ⟨t % 2, Nat.mod_lt _ (by decide)⟩
  live := fun N => ⟨N, _, Nat.le_refl _, rfl⟩
  return_after := by intros; contradiction
  step_invoked := fun _ _ _ => Nat.zero_le _
  step_pending := by intros; contradiction
  sequential := by
    intro i j _ h _ _ _ _
    exact Fin.ext (congrArg (fun p : Fin 3 => p.val) h)

/-- The implementation whose only execution is `alternating`. -/
def alternatingImplementation : Implementation 3 Unit := fun e => e = alternating

theorem alternating_not_solo (i : alternating.Instance) : ¬ alternating.Solo i := by
  rintro (⟨r, hr⟩ | ⟨N, hN⟩)
  · cases hr
  · have h0 := congrArg Fin.val (hN (2 * N) _ (by omega) rfl)
    have h1 := congrArg Fin.val (hN (2 * N + 1) _ (by omega) rfl)
    change (2 * N) % 2 = i.val at h0
    change (2 * N + 1) % 2 = i.val at h1
    omega

theorem alternating_idleWeakConflictFree :
    IdleWeakConflictFree alternatingImplementation (fun _ _ => False) := by
  constructor
  · intro e he i _ hs
    cases he
    exact False.elim (alternating_not_solo i hs)
  · intro e he _
    cases he
    have done : ∀ i : alternating.Instance, alternating.owner i = 2 → alternating.Completes i := by
      intro i hi
      have hh := congrArg Fin.val hi
      change i.val = 2 at hh
      have := i.isLt
      omega
    exact ⟨2, Or.inr done, done⟩

theorem alternating_not_lockFree : ¬ LockFree alternatingImplementation := by
  intro h
  obtain ⟨p, hp, hc⟩ := h alternating rfl
  obtain ⟨t, j, _, _, ht⟩ := hp 0
  obtain ⟨r, hr⟩ := hc j ht
  cases hr

/-- …strictly: for the empty conflict relation, the idle process `2` makes
`alternating` meet it, yet `alternating` is not lock-free. -/
theorem empty_idleWeakConflictFree_not_lockFree :
    IdleWeakConflictFree alternatingImplementation (fun _ _ => False) ∧
      ¬ LockFree alternatingImplementation :=
  ⟨alternating_idleWeakConflictFree, alternating_not_lockFree⟩

theorem alternating_not_weakConflictFree :
    ¬ WeakConflictFree alternatingImplementation (fun _ _ => False) :=
  fun h => alternating_not_lockFree (empty_weakConflictFree_iff_lockFree.mp h)

/-- Addition by a fixed amount, with a unit response. All operations commute. -/
def counter : Object Nat Nat Unit where
  initial := 0
  step := fun amount q => ((), q + amount)

theorem counter_independent (a b : Nat) : counter.Independent a b := by
  intro q
  refine ⟨rfl, rfl, ?_⟩
  simp [counter, Nat.add_comm, Nat.add_left_comm]

/-- Full intermediate-state sequences do not descend to the trace quotient:
[add 1, add 2] visits state 1 first; [add 2, add 1] visits state 2 first. -/
theorem equivalent_different_first_state :
    counter.TraceEq [1, 2] [2, 1] ∧
      (counter.step 1 counter.initial).2 ≠ (counter.step 2 counter.initial).2 := by
  exact ⟨Object.TraceEq.swap [] [] 1 2 (counter_independent 1 2), by decide⟩

end ConflictFreedom.Counterexamples
