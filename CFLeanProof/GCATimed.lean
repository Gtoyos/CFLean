import CFLeanProof.GCASnapshot

/-! A finite, partially completed execution of Algorithm 2 with atomic snapshots.
Optional event times allow a participant to stop between any two shared-memory
operations. Snapshot contents are computed from preceding writes. In particular,
containment and self-inclusion are proved, not supplied as safety hypotheses.
This models snapshots as primitives; their read/write implementation is separate. -/
namespace ConflictFreedom.GCA
open Object
variable {State Op Response P : Type} (obj : Object State Op Response)

/-- One run of Algorithm 2 with atomic snapshots, given by the times of each
participant's two updates, two scans and return — `none` for an event that
never happens. -/
structure TimedExecution (P : Type) where
  participants : List P
  input : P → obj.Trace
  writeA : P → Option Nat
  readA : P → Option Nat
  writeB : P → Option Nat
  readB : P → Option Nat
  finish : P → Option Nat
  readA_after : ∀ p t, readA p = some t → ∃ w, writeA p = some w ∧ w < t
  writeB_after : ∀ p t, writeB p = some t → ∃ r, readA p = some r ∧ r < t
  readB_after : ∀ p t, readB p = some t → ∃ w, writeB p = some w ∧ w < t
  finish_after : ∀ p t, finish p = some t → ∃ r, readB p = some r ∧ r < t

namespace TimedExecution
variable {obj} (e : TimedExecution obj P)

/-- The event happens. -/
def Present (t : Option Nat) : Prop := ∃ v, t = some v

/-- The write happens before the scan. -/
def Seen (write read : Option Nat) : Prop :=
  ∃ w r, write = some w ∧ read = some r ∧ w < r

/-- The processes whose write a scan sees. -/
noncomputable def snapshot (ids : List P) (writes : P → Option Nat) (read : Option Nat) : List P := by
  classical
  exact ids.filter (fun p => decide (Seen (writes p) read))

theorem mem_snapshot (ids : List P) (writes : P → Option Nat) (read : Option Nat) (p : P) :
    p ∈ snapshot ids writes read ↔ p ∈ ids ∧ Seen (writes p) read := by
  classical
  simp [snapshot]

/-- Atomic snapshots of write-once slots are ordered by their read times. -/
theorem snapshot_chain (ids : List P) (writes : P → Option Nat) (r s : Option Nat) :
    (∀ p ∈ snapshot ids writes r, p ∈ snapshot ids writes s) ∨
      (∀ p ∈ snapshot ids writes s, p ∈ snapshot ids writes r) := by
  cases r with
  | none =>
    left
    intro p hp
    obtain ⟨_, w, t, _, ht, _⟩ := (mem_snapshot _ _ _ _).mp hp
    cases ht
  | some r =>
    cases s with
    | none =>
      right
      intro p hp
      obtain ⟨_, w, t, _, ht, _⟩ := (mem_snapshot _ _ _ _).mp hp
      cases ht
    | some s =>
      by_cases hrs : r ≤ s
      · left
        intro p hp
        obtain ⟨hp, w, t, hw, ht, hlt⟩ := (mem_snapshot _ _ _ _).mp hp
        have he := Option.some.inj ht
        exact (mem_snapshot _ _ _ _).mpr ⟨hp, w, s, hw, rfl, by omega⟩
      · right
        intro p hp
        obtain ⟨hp, w, t, hw, ht, hlt⟩ := (mem_snapshot _ _ _ _).mp hp
        have he := Option.some.inj ht
        exact (mem_snapshot _ _ _ _).mpr ⟨hp, w, r, hw, rfl, by omega⟩

/-- The participants that wrote into `B`. -/
noncomputable def published : List P := by
  classical
  exact e.participants.filter (fun p => decide (Present (e.writeB p)))

/-- The participants that returned. -/
noncomputable def returned : List P := by
  classical
  exact e.participants.filter (fun p => decide (Present (e.finish p)))

theorem mem_published (p : P) :
    p ∈ e.published ↔ p ∈ e.participants ∧ Present (e.writeB p) := by
  classical
  simp [published]

theorem mem_returned (p : P) :
    p ∈ e.returned ↔ p ∈ e.participants ∧ Present (e.finish p) := by
  classical
  simp [returned]

/-- Evaluate the two snapshots from the timestamped shared-memory events. -/
noncomputable def views : SnapshotExecution obj P where
  participants := e.participants
  published := e.published
  returned := e.returned
  input := e.input
  aView := fun p => snapshot e.participants e.writeA (e.readA p)
  bView := fun p => snapshot e.participants e.writeB (e.readB p)
  published_invoked := fun p hp => ((e.mem_published p).mp hp).1
  returned_published := by
    intro p hp
    obtain ⟨hp, f, hf⟩ := (e.mem_returned p).mp hp
    obtain ⟨t, ht, _⟩ := e.finish_after p f hf
    obtain ⟨w, hw, _⟩ := e.readB_after p t ht
    exact (e.mem_published p).mpr ⟨hp, w, hw⟩
  a_self := by
    intro p hp
    obtain ⟨hp, t, ht⟩ := (e.mem_published p).mp hp
    obtain ⟨r, hr, _⟩ := e.writeB_after p t ht
    obtain ⟨w, hw, hwr⟩ := e.readA_after p r hr
    exact (mem_snapshot _ _ _ _).mpr ⟨hp, w, r, hw, hr, hwr⟩
  a_valid := fun _ _ q hq => ((mem_snapshot _ _ _ q).mp hq).1
  b_self := by
    intro p hp
    obtain ⟨hp, f, hf⟩ := (e.mem_returned p).mp hp
    obtain ⟨t, ht, _⟩ := e.finish_after p f hf
    obtain ⟨w, hw, hwt⟩ := e.readB_after p t ht
    exact (mem_snapshot _ _ _ _).mpr ⟨hp, w, t, hw, ht, hwt⟩
  b_valid := by
    intro _ _ q hq
    obtain ⟨hq, w, _, hw, _, _⟩ := (mem_snapshot _ _ _ _).mp hq
    exact (e.mem_published q).mpr ⟨hq, w, hw⟩
  a_chain := fun p _ q _ => snapshot_chain _ _ (e.readA p) (e.readA q)
  b_chain := fun p _ q _ => snapshot_chain _ _ (e.readB p) (e.readB q)

variable [DecidableEq Op]

/-- Kernel-checked Algorithm 2 safety at the atomic-snapshot boundary, including
partial participation and crashes between any two protocol events. -/
theorem specification : e.views.history.Specification := e.views.specification

end TimedExecution
end ConflictFreedom.GCA
