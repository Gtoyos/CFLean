import CFLeanProof.GCATimed

/-! Operational GCA above the assumed wait-free atomic-snapshot interface.

Each scheduled protocol step either completes a snapshot-object operation,
performs a local calculation, or stutters. Snapshot update/scan completion is
supplied by `SnapshotWaitFree`, the paper's explicit external assumption.
No implementation of the snapshot object is required or postulated as an axiom.
The six stages are A.update, A.scan, candidate calculation, B.update, B.scan,
and output calculation/return. Local calculations are total mathematical
operations, as in the paper's pseudocode.
-/
namespace ConflictFreedom.GCA
open Object
variable {State Op Response P : Type} (obj : Object State Op Response)

/-- One GCA instance run by Algorithm 2 above the snapshot interface: the
participants and their inputs, who is scheduled at each tick, and whether that
tick completes the caller's pending snapshot operation (`acknowledged`). -/
structure Protocol (P : Type) where
  participants : List P
  input : P → obj.Trace
  actor : Nat → Option P
  actor_valid : ∀ t p, actor t = some p → p ∈ participants
  acknowledged : Nat → Bool

namespace Protocol
variable {obj} [DecidableEq P] (e : Protocol obj P)

/-- Stages occupied by calls to the assumed snapshot implementation. -/
def SnapshotStage (k : Nat) : Prop := k = 0 ∨ k = 1 ∨ k = 3 ∨ k = 4

/-- Stages 2 and 5 are finite local calculations; stage 6 is terminal. -/
def advance (k : Nat) (ack : Bool) : Nat :=
  if k < 6 ∧ (k = 2 ∨ k = 5 ∨ ack = true) then k + 1 else k

/-- The stage each participant has reached after `t` ticks: `0`–`5` are the six
stages, and `6` means its call has returned. -/
def phase : Nat → P → Nat
  | 0, _ => 0
  | t + 1, p => if e.actor t = some p then advance (phase t p) (e.acknowledged t)
      else phase t p

/-- `p` is scheduled infinitely often. -/
def InfiniteSteps (p : P) : Prop := ∀ N, ∃ t, N ≤ t ∧ e.actor t = some p

/-- Interface assumption for the two snapshot updates and two scans. A caller
that continues taking steps completes each outstanding interface operation.
It imposes no obligation on a stopped process or on the other processes. -/
def SnapshotWaitFree : Prop :=
  ∀ p, e.InfiniteSteps p → ∀ k, SnapshotStage k → ∀ t, e.phase t p = k →
    ∃ u, t ≤ u ∧ e.phase u p = k ∧ e.actor u = some p ∧ e.acknowledged u = true

theorem phase_step_bounds (t : Nat) (p : P) :
    e.phase t p ≤ e.phase (t + 1) p ∧ e.phase (t + 1) p ≤ e.phase t p + 1 := by
  simp only [phase]
  split
  · unfold advance
    split <;> omega
  · omega

theorem phase_mono {t u : Nat} (htu : t ≤ u) (p : P) : e.phase t p ≤ e.phase u p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  clear htu
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans ih (e.phase_step_bounds (t + d) p).1

theorem phase_le_six (t : Nat) (p : P) : e.phase t p ≤ 6 := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    simp only [phase]
    split
    · unfold advance
      split <;> omega
    · exact ih

/-- With the snapshot assumption, an active caller reaches every protocol stage.
The proof supplies the local-stage progress itself. -/
theorem reaches_stage (hw : e.SnapshotWaitFree) {p : P} (hp : e.InfiniteSteps p)
    (k : Nat) (hk : k ≤ 6) : ∃ t, k ≤ e.phase t p := by
  induction k with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih (by omega)
    by_cases hdone : k + 1 ≤ e.phase t p
    · exact ⟨t, hdone⟩
    · have heq : e.phase t p = k := by omega
      by_cases hlocal : k = 2 ∨ k = 5
      · obtain ⟨u, htu, hu⟩ := hp t
        have hm := e.phase_mono htu p
        by_cases hdone : k + 1 ≤ e.phase u p
        · exact ⟨u, hdone⟩
        · have hequ : e.phase u p = k := by omega
          refine ⟨u + 1, ?_⟩
          simp only [phase, hu, ite_true, hequ, advance]
          split
          · exact Nat.le_refl _
          · rename_i hn
            exact False.elim (hn ⟨by omega, hlocal.elim Or.inl (fun h => Or.inr (Or.inl h))⟩)
      · have hstage : SnapshotStage k := by unfold SnapshotStage; omega
        obtain ⟨u, _, hequ, hu, hack⟩ := hw p hp k hstage t heq
        refine ⟨u + 1, ?_⟩
        simp only [phase, hu, ite_true, hequ, advance, hack]
        split
        · exact Nat.le_refl _
        · rename_i hn
          exact False.elim (hn ⟨by omega, Or.inr (Or.inr trivial)⟩)

/-- Wait-freedom of the GCA control flow, conditional only on wait-free snapshot
updates/scans and finite local calculation steps in this abstract machine. -/
theorem terminates (hw : e.SnapshotWaitFree) {p : P} (hp : e.InfiniteSteps p) :
    ∃ t, e.phase t p = 6 := by
  obtain ⟨t, ht⟩ := e.reaches_stage hw hp 6 (Nat.le_refl _)
  exact ⟨t, Nat.le_antisymm (e.phase_le_six t p) ht⟩

/-- The unique atomic protocol event that leaves stage k. -/
def Exits (p : P) (k t : Nat) : Prop :=
  e.phase t p = k ∧ e.phase (t + 1) p = k + 1

theorem exits_unique {p : P} {k t u : Nat} (ht : e.Exits p k t) (hu : e.Exits p k u) : t = u := by
  by_cases h : t < u
  · have hm := e.phase_mono h p
    rw [ht.2, hu.1] at hm
    omega
  · by_cases h' : u < t
    · have hm := e.phase_mono h' p
      rw [hu.2, ht.1] at hm
      omega
    · omega

/-- A stage cannot be skipped, even with arbitrarily many stuttering steps. -/
theorem crossed {p : P} {k t : Nat} (h : k < e.phase t p) :
    ∃ u, u < t ∧ e.Exits p k u := by
  induction t with
  | zero => simp [phase] at h
  | succ t ih =>
    by_cases hprev : k < e.phase t p
    · obtain ⟨u, hut, hu⟩ := ih hprev
      exact ⟨u, by omega, hu⟩
    · have bounds := e.phase_step_bounds t p
      exact ⟨t, by omega, by constructor <;> omega⟩

/-- A phase transition can only be caused by that process's own step. -/
theorem exits_actor {p : P} {k t : Nat} (h : e.Exits p k t) : e.actor t = some p := by
  by_cases ha : e.actor t = some p
  · exact ha
  · have hs : e.phase (t + 1) p = e.phase t p := by simp only [phase, ha, ite_false]
    have h₁ := h.1
    have h₂ := h.2
    omega

/-- The ideal atomic implementation satisfies the interface assumption under
any scheduler. Actual snapshot implementations may introduce arbitrary finite
stuttering; no bound on their number of internal steps is required. -/
theorem alwaysAcknowledged_waitFree (ha : ∀ t, e.acknowledged t = true) :
    e.SnapshotWaitFree := by
  intro p hp k _ t ht
  obtain ⟨u, htu, hu⟩ := hp t
  have hm := e.phase_mono htu p
  by_cases he : e.phase u p = k
  · exact ⟨u, htu, he, hu, ha u⟩
  · obtain ⟨v, _, hv⟩ := e.crossed (p := p) (k := k) (t := u) (by omega)
    have htv : t ≤ v := by
      apply Classical.byContradiction
      intro hn
      have hh := e.phase_mono (t := v + 1) (u := t) (by omega) p
      have hh₂ := hv.2
      omega
    exact ⟨v, htv, hv.1, e.exits_actor hv, ha v⟩

/-- The tick at which `p` leaves stage `k`, if it ever does. -/
noncomputable def eventTime (p : P) (k : Nat) : Option Nat := by
  classical
  exact if h : ∃ t, e.Exits p k t then some (Classical.choose h) else none

theorem eventTime_iff (p : P) (k t : Nat) : e.eventTime p k = some t ↔ e.Exits p k t := by
  classical
  unfold eventTime
  split
  · rename_i h
    constructor
    · intro he
      have ht := Option.some.inj he
      exact ht ▸ Classical.choose_spec h
    · intro ht
      exact congrArg some (e.exits_unique (Classical.choose_spec h) ht)
  · rename_i hn
    constructor
    · intro h; cases h
    · intro ht; exact False.elim (hn ⟨t, ht⟩)

theorem eventTime_before {p : P} {k l t : Nat} (hkl : k < l)
    (ht : e.eventTime p l = some t) : ∃ u, e.eventTime p k = some u ∧ u < t := by
  have he := ((e.eventTime_iff p l t).mp ht).1
  obtain ⟨u, hut, hu⟩ := e.crossed (p := p) (k := k) (t := t) (by omega)
  exact ⟨u, (e.eventTime_iff p k u).mpr hu, hut⟩

/-- Refinement into the timestamped GCA semantics used by the safety proof.
Stage 2 (candidate calculation) occurs between the first scan and B publication. -/
noncomputable def timed : TimedExecution obj P where
  participants := e.participants
  input := e.input
  writeA := fun p => e.eventTime p 0
  readA := fun p => e.eventTime p 1
  writeB := fun p => e.eventTime p 3
  readB := fun p => e.eventTime p 4
  finish := fun p => e.eventTime p 5
  readA_after := fun _ _ h => e.eventTime_before (by decide) h
  writeB_after := fun _ _ h => e.eventTime_before (by decide) h
  readB_after := fun _ _ h => e.eventTime_before (by decide) h
  finish_after := fun _ _ h => e.eventTime_before (by decide) h

theorem finish_of_infiniteSteps (hw : e.SnapshotWaitFree) {p : P} (hp : e.InfiniteSteps p) :
    TimedExecution.Present (e.timed.finish p) := by
  obtain ⟨t, ht⟩ := e.terminates hw hp
  obtain ⟨u, _, hu⟩ := e.crossed (p := p) (k := 5) (t := t) (by omega)
  exact ⟨u, (e.eventTime_iff p 5 u).mpr hu⟩

variable [DecidableEq Op]

/-- The GCA history the protocol produces, through its timed execution. -/
noncomputable def history : History obj P := e.timed.views.history

/-- All six GCA safety properties follow from the protocol's extracted events. -/
theorem specification : e.history.Specification := e.timed.specification

/-- Every participating process that keeps taking steps returns from GCA. -/
theorem returned_of_infiniteSteps (hw : e.SnapshotWaitFree) {p : P}
    (hp : e.InfiniteSteps p) : ∃ t c, e.history.output p = some (t, c) := by
  classical
  obtain ⟨u, _, hu⟩ := hp 0
  have hpP := e.actor_valid u p hu
  have hpR : p ∈ e.timed.returned := (e.timed.mem_returned p).mpr
    ⟨hpP, e.finish_of_infiniteSteps hw hp⟩
  exact ⟨_, _, (e.timed.views.output_iff p _ _).mpr ⟨hpR, rfl, rfl⟩⟩

/-- Algorithm 2 correctness above the paper's assumed wait-free snapshots. -/
theorem correctness (hw : e.SnapshotWaitFree) :
    e.history.Specification ∧
      ∀ p, e.InfiniteSteps p → ∃ t c, e.history.output p = some (t, c) :=
  ⟨e.specification, fun _ hp => e.returned_of_infiniteSteps hw hp⟩

end Protocol
end ConflictFreedom.GCA
