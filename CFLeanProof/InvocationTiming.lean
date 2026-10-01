import CFLeanProof.UniversalIdentities

/-! Temporal bookkeeping for the two universal constructions.  The ledger
records the invocation before any response can be recorded, even when the
interleaved execution contains idle scheduler steps. -/
namespace ConflictFreedom
namespace InvocationLedger

variable {P Op : Type} [DecidableEq P]

/-- An interleaving of the abstract invocation and response actions. -/
structure Run (P Op : Type) [DecidableEq P] where
  state : Nat → State P Op
  initial_state : state 0 = initial
  next : ∀ t, state (t + 1) = state t ∨
    (∃ p op, (state t).active p = none ∧ state (t + 1) = invoke (state t) p op) ∨
    (∃ p cmd, (state t).active p = some cmd ∧ state (t + 1) = finish (state t) p cmd)

namespace Run
variable (e : Run P Op)

theorem valid (t : Nat) : Valid (e.state t) := by
  induction t with
  | zero => rw [e.initial_state]; exact initial_valid
  | succ t ih =>
    rcases e.next t with h | ⟨p, op, hp, h⟩ | ⟨p, cmd, hp, h⟩
    · exact h ▸ ih
    · rw [h]; exact valid_invoke ih p op hp
    · rw [h]; exact valid_finish ih p cmd hp

theorem invoked_step {cmd : Command P Op} {t : Nat}
    (h : cmd ∈ (e.state t).invoked) : cmd ∈ (e.state (t + 1)).invoked := by
  rcases e.next t with he | ⟨p, op, _, he⟩ | ⟨p, c, _, he⟩
  · simpa only [he] using h
  · rw [he]; exact List.mem_cons_of_mem _ h
  · simpa only [he, finish] using h

theorem returned_step {cmd : Command P Op} {t : Nat}
    (h : cmd ∈ (e.state t).returned) : cmd ∈ (e.state (t + 1)).returned := by
  rcases e.next t with he | ⟨p, op, _, he⟩ | ⟨p, c, _, he⟩
  · simpa only [he] using h
  · simpa only [he, invoke] using h
  · rw [he]; exact List.mem_cons_of_mem _ h

theorem invoked_mono {cmd : Command P Op} {t u : Nat} (htu : t ≤ u)
    (h : cmd ∈ (e.state t).invoked) : cmd ∈ (e.state u).invoked := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  induction d with
  | zero => simpa using h
  | succ d ih => exact e.invoked_step (ih (by omega))

theorem returned_mono {cmd : Command P Op} {t u : Nat} (htu : t ≤ u)
    (h : cmd ∈ (e.state t).returned) : cmd ∈ (e.state u).returned := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  induction d with
  | zero => simpa using h
  | succ d ih => exact e.returned_step (ih (by omega))

/-- A newly recorded response has an invocation in the previous state. -/
theorem invoked_before_new_return {cmd : Command P Op} {t : Nat}
    (hr : cmd ∈ (e.state (t + 1)).returned)
    (hn : cmd ∉ (e.state t).returned) : cmd ∈ (e.state t).invoked := by
  rcases e.next t with he | ⟨p, op, _, he⟩ | ⟨p, c, hc, he⟩
  · exact False.elim (hn (he ▸ hr))
  · exact False.elim (hn (by simpa only [he, invoke] using hr))
  · rw [he] at hr
    rcases List.mem_cons.mp hr with rfl | htail
    · exact ((e.valid t).active_tag p cmd hc).2.2
    · exact False.elim (hn htail)

/-- Every response visible at time `t` has an invocation visible at a strictly
earlier time.  This is the temporal part of response provenance. -/
theorem invoked_strictly_before_return {cmd : Command P Op} {t : Nat}
    (hr : cmd ∈ (e.state t).returned) :
    ∃ u, u < t ∧ cmd ∈ (e.state u).invoked := by
  induction t with
  | zero =>
    rw [e.initial_state] at hr
    cases hr
  | succ t ih =>
    by_cases hprev : cmd ∈ (e.state t).returned
    · obtain ⟨u, hu, hi⟩ := ih hprev
      exact ⟨u, by omega, hi⟩
    · exact ⟨t, by omega, e.invoked_before_new_return hr hprev⟩

end Run
end InvocationLedger

namespace WeakUniversal
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The invocation-ledger run of a run of Algorithm 1. -/
def Execution.ledgerRun {H : Environment (n := n) obj} (run : Execution obj H) :
    InvocationLedger.Run (Fin n) Op where
  state := fun t => ledger obj (run.state t)
  initial_state := by rw [run.initial_state]; rfl
  next := by
    intro t
    rcases run.next t with he | hs
    · exact Or.inl (congrArg (ledger obj) he)
    · exact ledger_step obj hs

theorem Execution.invoked_before_new_return {H : Environment (n := n) obj}
    (run : Execution obj H) {cmd : Cmd n Op} {t : Nat}
    (hr : ∃ ret ∈ (run.state (t + 1)).returns, ret.command = cmd)
    (hn : ¬ ∃ ret ∈ (run.state t).returns, ret.command = cmd) :
    cmd ∈ (run.state t).invocations := by
  have hret : cmd ∈ ((run.ledgerRun obj).state (t + 1)).returned := by
    obtain ⟨ret, hm, he⟩ := hr
    exact List.mem_map.mpr ⟨ret, hm, he⟩
  have hnot : cmd ∉ ((run.ledgerRun obj).state t).returned := by
    intro hm
    obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
    exact hn ⟨ret, hret, he⟩
  exact (run.ledgerRun obj).invoked_before_new_return hret hnot

theorem Execution.invoked_strictly_before_return {H : Environment (n := n) obj}
    (run : Execution obj H) {cmd : Cmd n Op} {t : Nat}
    (hr : ∃ ret ∈ (run.state t).returns, ret.command = cmd) :
    ∃ u, u < t ∧ cmd ∈ (run.state u).invocations := by
  obtain ⟨ret, hm, he⟩ := hr
  exact (run.ledgerRun obj).invoked_strictly_before_return
    (List.mem_map.mpr ⟨ret, hm, he⟩)

end WeakUniversal

namespace HelpingUniversal
open WeakUniversal (Cmd Return Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The invocation-ledger run of a run of Algorithm 3. -/
def Execution.ledgerRun {H : Environment (n := n) obj} (run : Execution obj H) :
    InvocationLedger.Run (Fin n) Op where
  state := fun t => ledger obj (run.state t)
  initial_state := by rw [run.initial_state]; rfl
  next := by
    intro t
    rcases run.next t with he | hs
    · exact Or.inl (congrArg (ledger obj) he)
    · exact ledger_step obj hs

theorem Execution.invoked_before_new_return {H : Environment (n := n) obj}
    (run : Execution obj H) {cmd : Cmd n Op} {t : Nat}
    (hr : ∃ ret ∈ (run.state (t + 1)).returns, ret.command = cmd)
    (hn : ¬ ∃ ret ∈ (run.state t).returns, ret.command = cmd) :
    cmd ∈ (run.state t).invocations := by
  have hret : cmd ∈ ((run.ledgerRun obj).state (t + 1)).returned := by
    obtain ⟨ret, hm, he⟩ := hr
    exact List.mem_map.mpr ⟨ret, hm, he⟩
  have hnot : cmd ∉ ((run.ledgerRun obj).state t).returned := by
    intro hm
    obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
    exact hn ⟨ret, hret, he⟩
  exact (run.ledgerRun obj).invoked_before_new_return hret hnot

theorem Execution.invoked_strictly_before_return {H : Environment (n := n) obj}
    (run : Execution obj H) {cmd : Cmd n Op} {t : Nat}
    (hr : ∃ ret ∈ (run.state t).returns, ret.command = cmd) :
    ∃ u, u < t ∧ cmd ∈ (run.state u).invocations := by
  obtain ⟨ret, hm, he⟩ := hr
  exact (run.ledgerRun obj).invoked_strictly_before_return
    (List.mem_map.mpr ⟨ret, hm, he⟩)

end HelpingUniversal
end ConflictFreedom
