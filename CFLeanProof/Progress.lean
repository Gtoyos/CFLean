import CFLeanProof.Execution

/-! §3 progress conditions, parameterized by the set of admitted executions:
the definitions, Proposition `prop:progress-hierarchy` (`progressHierarchy`) and
Proposition `prop:cf-degenerate` (`empty_conflictFree_iff_waitFree`,
`empty_weakConflictFree_iff_lockFree`, `universal_conflictFree_iff_obstructionFree`,
`universal_weakConflictFree_iff_obstructionFree`). -/
namespace ConflictFreedom
variable {n : Nat} {Op : Type}

/-- An implementation, given by the set of infinite executions it admits. -/
abbrev Implementation (n : Nat) (Op : Type) := Execution n Op → Prop

/-- Wait-freedom: every operation of a correct process completes.  The
manuscript restricts this to processes taking infinitely many steps; the two
readings agree (`waitFree_iff_infiniteSteps`). -/
def WaitFree (A : Implementation n Op) : Prop :=
  ∀ e, A e → ∀ i, e.Correct (e.owner i) → e.Completes i

/-- Lock-freedom: some process taking infinitely many steps completes each of
its operations. -/
def LockFree (A : Implementation n Op) : Prop :=
  ∀ e, A e → ∃ p, e.InfiniteSteps p ∧ ∀ i, e.owner i = p → e.Completes i

/-- Obstruction-freedom: an operation of a correct process completes whenever
it is eventually step-contention free. -/
def ObstructionFree (A : Implementation n Op) : Prop :=
  ∀ e, A e → ∀ i, e.Correct (e.owner i) → e.Solo i → e.Completes i

/-- **Definition (Conflict-freedom).**  An operation of a correct process
completes whenever it is eventually step-contention free *or* the execution is
eventually conflict-free. -/
def ConflictFree (A : Implementation n Op) (conflict : Op → Op → Prop) : Prop :=
  ∀ e, A e → ∀ i, e.Correct (e.owner i) →
    (e.Solo i ∨ e.EventuallyConflictFree conflict) → e.Completes i

variable {A : Implementation n Op} {conflict : Op → Op → Prop}

theorem waitFree_conflictFree (h : WaitFree A) : ConflictFree A conflict :=
  fun e he i hi _ => h e he i hi

theorem conflictFree_obstructionFree (h : ConflictFree A conflict) : ObstructionFree A :=
  fun e he i hi hs => h e he i hi (Or.inl hs)

theorem empty_conflictFree_iff_waitFree :
    ConflictFree A (fun _ _ => False) ↔ WaitFree A :=
  ⟨fun h e he i hi => h e he i hi (Or.inr e.empty_eventuallyConflictFree),
    waitFree_conflictFree⟩

/-- Lock-freedom implies obstruction-freedom: in a solo suffix, a process taking
infinitely many steps owns the solo operation. -/
theorem lockFree_obstructionFree (h : LockFree A) : ObstructionFree A := by
  intro e he i _ hs
  rcases hs with hc | ⟨N, hN⟩
  · exact hc
  · obtain ⟨p, hp, hc⟩ := h e he
    obtain ⟨t, j, ht, hact, htp⟩ := hp N
    exact hc i (by rw [← hN t j ht hact]; exact htp)

/-- **Definition (Weak conflict-freedom).**  (1) Obstruction-freedom, and (2) in
an eventually conflict-free execution some process taking infinitely many steps
completes all of its operations. -/
def WeakConflictFree (A : Implementation n Op) (conflict : Op → Op → Prop) : Prop :=
  ObstructionFree A ∧ ∀ e, A e → e.EventuallyConflictFree conflict →
    ∃ p, e.InfiniteSteps p ∧ ∀ i, e.owner i = p → e.Completes i

theorem conflictFree_weakConflictFree (h : ConflictFree A conflict) :
    WeakConflictFree A conflict := by
  refine ⟨conflictFree_obstructionFree h, ?_⟩
  intro e he hc
  obtain ⟨p, hp⟩ := e.exists_infiniteSteps
  exact ⟨p, hp, fun i hi => h e he i (Or.inl (hi.symm ▸ hp)) (Or.inr hc)⟩

theorem empty_weakConflictFree_iff_lockFree :
    WeakConflictFree A (fun _ _ => False) ↔ LockFree A := by
  constructor
  · exact fun h e he => h.2 e he e.empty_eventuallyConflictFree
  · exact fun h => ⟨lockFree_obstructionFree h, fun e he _ => h e he⟩

/-- Requiring progress only of infinitely stepping processes gives the same
wait-freedom predicate: idle correct processes already completed every call. -/
theorem waitFree_iff_infiniteSteps : WaitFree A ↔
    ∀ e, A e → ∀ i, e.InfiniteSteps (e.owner i) → e.Completes i := by
  constructor
  · exact fun h e he i hi => h e he i (Or.inl hi)
  · intro h e he i hi
    exact hi.elim (h e he i) (fun done => done i rfl)

theorem universal_conflictFree_iff_obstructionFree :
    ConflictFree A (fun _ _ => True) ↔ ObstructionFree A := by
  refine ⟨conflictFree_obstructionFree, ?_⟩
  intro h e he i hi hs
  exact h e he i hi (hs.elim id (fun hc => e.universal_solo hc i))

/-- **Proposition `prop:progress-hierarchy`**: wait-freedom ⟹ conflict-freedom
⟹ weak conflict-freedom ⟹ obstruction-freedom. -/
theorem progressHierarchy :
    (WaitFree A → ConflictFree A conflict) ∧
    (ConflictFree A conflict → WeakConflictFree A conflict) ∧
    (WeakConflictFree A conflict → ObstructionFree A) :=
  ⟨waitFree_conflictFree, conflictFree_weakConflictFree, fun h => h.1⟩

theorem weakConflictFree_obstructionFree (h : WeakConflictFree A conflict) :
    ObstructionFree A := h.1

theorem lockFree_weakConflictFree (h : LockFree A) : WeakConflictFree A conflict :=
  ⟨lockFree_obstructionFree h, fun e he _ => h e he⟩

theorem universal_weakConflictFree_iff_obstructionFree :
    WeakConflictFree A (fun _ _ => True) ↔ ObstructionFree A :=
  ⟨fun h => h.1, fun h => conflictFree_weakConflictFree
    (universal_conflictFree_iff_obstructionFree.mpr h)⟩

end ConflictFreedom
