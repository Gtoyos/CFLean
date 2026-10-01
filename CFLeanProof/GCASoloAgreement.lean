import CFLeanProof.GCAProtocol

/-! # GCA property 7, Solo agreement, and Algorithm 2 (Lemma `GCA_soloagg`)

The manuscript adds a seventh GCA property, used only in the proof of
`th:WeakUCresolve`:

> **Solo agreement.**  If a process returns before any other process
> participates, every output trace equals its own.
> `P' = P'_r = {j} ⟹ ∀ i ∈ P_r, t_i = t_j`, where `P'` and `P'_r` are the sets
> of participants and returning participants in some prefix of the execution.

It is a statement about prefixes, so it needs the protocol's own clock:
`Protocol.SoloAgreement` reads the prefix as the protocol's first `T` steps.
`j` has returned in it when `phase T j = 6`, and `j` is its only participant
when no other process has taken a step before `T`.  The conclusion is about the
whole execution: every output trace is `j`'s.

Lemma `GCA_soloagg` — Algorithm 2 has the property — is `Protocol.soloAgreement`.
It follows the manuscript's proof at the level of the two snapshot views
(`SnapshotExecution.solo_result`, `SnapshotExecution.solo_agreement`): `j`'s own
views contain nothing but `j`, so it writes `(s_j, true)` to `B` and outputs
`s_j`; every flagged candidate written later extends `s_j`, because its writer's
`A` view contains `s_j`; and every later `B` view contains `(s_j, true)`, so the
meet of line 6 is `s_j`.  `Protocol.solo_output` records the part of the proof
that says `j` itself commits its input.

The six properties of `GCA.History.Specification` do not mention time, so they
cannot state this; the property is a genuinely new requirement.  For a caller
of the universal construction it says that once a process has run a round
alone, later callers of that round are pinned to its trace.
-/
namespace ConflictFreedom.GCA
open Object
variable {State Op Response : Type} {obj : Object State Op Response}

namespace SnapshotExecution
variable {P : Type} [DecidableEq Op] (e : SnapshotExecution obj P)

omit [DecidableEq Op] in
/-- A snapshot view in which only `j` appears makes every input it reports
`j`'s. -/
theorem flag_of_alone {j : P} (haj : ∀ q ∈ e.aView j, q = j) : e.Flag j :=
  ⟨e.input j, by
    intro s hs
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
    rw [haj q hq]
    exact obj.tracePrefix_refl _⟩

/-- **The solo caller's own output (first paragraph of Lemma `GCA_soloagg`).**
If `j`'s `A` and `B` views contain only `j`, then `A_j = A_j^co`, `j` writes
`(s_j, true)` to `B`, its output is `s_j`, and line 7's flag `w_j` holds, so it
commits. -/
theorem solo_result {j : P} (hj : j ∈ e.returned) (haj : ∀ q ∈ e.aView j, q = j)
    (hbj : ∀ q ∈ e.bView j, q = j) :
    e.candidate j = e.input j ∧ e.result j = e.input j ∧ e.Commits j := by
  have hpub := e.returned_published j hj
  have hcand : e.candidate j = e.input j :=
    e.candidate_eq_of_uniform hpub _ (fun q hq => by rw [haj q hq])
  have hflag := e.flag_of_alone haj
  have hres : e.result j = e.input j := by
    apply obj.tracePrefix_antisymm
    · exact hcand ▸ e.result_lower (e.b_self j hj) hflag
    · apply e.result_greatest ⟨j, e.b_self j hj, hflag⟩
      intro q hq _
      rw [hbj q hq, hcand]
      exact obj.tracePrefix_refl _
  refine ⟨hcand, hres, Or.inl ⟨fun q hq => by rw [haj q hq], fun q hq => ?_⟩⟩
  rw [hbj q hq, hcand]

/-- **Every output is the solo trace (second and third paragraphs of Lemma
`GCA_soloagg`).**  Besides `j`'s solo views, assume that every other returning
process's `B` view contains `j`, and that every other process that wrote `B`
had `j` in its `A` view.  Then every flagged candidate extends `s_j`, `(s_j,
true)` is among the candidates every returning process sees, and the meet of
line 6 is `s_j` for everyone. -/
theorem solo_agreement {j : P} (hj : j ∈ e.returned) (haj : ∀ q ∈ e.aView j, q = j)
    (hbj : ∀ q ∈ e.bView j, q = j)
    (hlate : ∀ q ∈ e.returned, q ≠ j → j ∈ e.bView q)
    (hseen : ∀ k ∈ e.published, k ≠ j → j ∈ e.aView k) :
    ∀ q ∈ e.returned, e.result q = e.input j := by
  obtain ⟨hcand, hres, -⟩ := e.solo_result hj haj hbj
  have hflag := e.flag_of_alone haj
  intro q hq
  by_cases hqj : q = j
  · subst hqj; exact hres
  · have hjB := hlate q hq hqj
    apply obj.tracePrefix_antisymm
    · exact hcand ▸ e.result_lower hjB hflag
    · apply e.result_greatest ⟨j, hjB, hflag⟩
      intro k hk hfk
      by_cases hkj : k = j
      · subst hkj; rw [hcand]; exact obj.tracePrefix_refl _
      · exact e.candidate_extends hfk (hseen k (e.b_valid q hq k hk) hkj)

end SnapshotExecution

namespace Protocol
variable {P : Type} [DecidableEq P] (e : Protocol obj P)

/-- Having passed stage `k` by clock `c` is having exited it before `c`. -/
theorem lt_phase_iff (k c : Nat) (q : P) :
    k < e.phase c q ↔ ∃ w, e.eventTime q k = some w ∧ w < c := by
  constructor
  · intro h
    obtain ⟨u, hu, hex⟩ := e.crossed h
    exact ⟨u, (e.eventTime_iff q k u).mpr hex, hu⟩
  · rintro ⟨w, hw, hwc⟩
    have hex := (e.eventTime_iff q k w).mp hw
    have := e.phase_mono (show w + 1 ≤ c by omega) q
    have := hex.2
    omega

/-- Every protocol event is a step of its process. -/
theorem eventTime_actor {q : P} {k w : Nat} (h : e.eventTime q k = some w) :
    e.actor w = some q :=
  e.exits_actor ((e.eventTime_iff q k w).mp h)

/-- **GCA property 7, Solo agreement.**  Read on the prefix formed by the
protocol's first `T` steps: if `j` has returned in it (`phase T j = 6`) and no
other process has taken a step in it, then every output trace of the whole
execution is `j`'s.  (`j`'s own output exists, since `j` returned.) -/
def SoloAgreement [DecidableEq Op] : Prop :=
  ∀ (T : Nat) (j : P), (∀ c k, c < T → e.actor c = some k → k = j) → e.phase T j = 6 →
    ∃ tj cj, e.history.output j = some (tj, cj) ∧
      ∀ i t c, e.history.output i = some (t, c) → t = tj

section Solo
variable {e} {T : Nat} {j : P}

/-- In the solo prefix, every event of another process comes at or after `T`. -/
theorem solo_other_late (hsolo : ∀ c k, c < T → e.actor c = some k → k = j)
    {k : P} (hk : k ≠ j) {s w : Nat} (hw : e.eventTime k s = some w) : T ≤ w :=
  Nat.le_of_not_lt (fun hlt => hk (hsolo w k hlt (e.eventTime_actor hw)))

/-- In the solo prefix, every event of `j` up to its return comes before `T`. -/
theorem solo_own_early (h6 : e.phase T j = 6) {s : Nat} (hs : s ≤ 5) :
    ∃ w, e.eventTime j s = some w ∧ w < T :=
  (e.lt_phase_iff s T j).mp (by rw [h6]; omega)

/-- The solo process returns in the extracted snapshot execution. -/
theorem solo_returned (h6 : e.phase T j = 6) : j ∈ e.timed.views.returned := by
  obtain ⟨f, hf, -⟩ := solo_own_early h6 (s := 5) (by omega)
  rw [show e.timed.views.returned = e.timed.returned from rfl, TimedExecution.mem_returned]
  exact ⟨e.actor_valid f j (e.eventTime_actor hf), f, hf⟩

variable (hsolo : ∀ c k, c < T → e.actor c = some k → k = j) (h6 : e.phase T j = 6)
include hsolo h6

/-- `j`'s `A` view contains only `j`: nobody else has written `A` when `j`
scans it. -/
theorem solo_aView : ∀ q ∈ e.timed.views.aView j, q = j := by
  intro q hq
  obtain ⟨-, w, r, hw, hr, hwr⟩ := (TimedExecution.mem_snapshot _ _ _ _).mp hq
  refine Classical.byContradiction fun hqj => ?_
  obtain ⟨r', hr', hr'T⟩ := solo_own_early h6 (s := 1) (by omega)
  have hrr : r = r' := Option.some.inj (hr.symm.trans hr')
  have := solo_other_late hsolo hqj (s := 0) hw
  omega

/-- `j`'s `B` view contains only `j`. -/
theorem solo_bView : ∀ q ∈ e.timed.views.bView j, q = j := by
  intro q hq
  obtain ⟨-, w, r, hw, hr, hwr⟩ := (TimedExecution.mem_snapshot _ _ _ _).mp hq
  refine Classical.byContradiction fun hqj => ?_
  obtain ⟨r', hr', hr'T⟩ := solo_own_early h6 (s := 4) (by omega)
  have hrr : r = r' := Option.some.inj (hr.symm.trans hr')
  have := solo_other_late hsolo hqj (s := 3) hw
  omega

/-- Every other returning process scans `B` after `j` wrote `(s_j, true)`. -/
theorem solo_late_bView : ∀ q ∈ e.timed.views.returned, q ≠ j → j ∈ e.timed.views.bView q := by
  intro q hq hqj
  have hq' : q ∈ e.timed.returned := hq
  obtain ⟨-, f, hf⟩ := (e.timed.mem_returned q).mp hq'
  obtain ⟨r4, hr4, -⟩ := e.eventTime_before (show 4 < 5 by decide) hf
  obtain ⟨w0, hw0, hw04⟩ := e.eventTime_before (show 0 < 4 by decide) hr4
  obtain ⟨w3, hw3, hw3T⟩ := solo_own_early h6 (s := 3) (by omega)
  have := solo_other_late hsolo hqj (s := 0) hw0
  exact (TimedExecution.mem_snapshot _ _ _ _).mpr
    ⟨e.actor_valid w3 j (e.eventTime_actor hw3), w3, r4, hw3, hr4, by omega⟩

/-- Every other process that wrote `B` scanned `A` after `j` wrote `s_j`. -/
theorem solo_late_aView : ∀ k ∈ e.timed.views.published, k ≠ j → j ∈ e.timed.views.aView k := by
  intro k hk hkj
  have hk' : k ∈ e.timed.published := hk
  obtain ⟨-, w3, hw3⟩ := (e.timed.mem_published k).mp hk'
  obtain ⟨r1, hr1, -⟩ := e.eventTime_before (show 1 < 3 by decide) hw3
  obtain ⟨w0, hw0, hw01⟩ := e.eventTime_before (show 0 < 1 by decide) hr1
  obtain ⟨v0, hv0, hv0T⟩ := solo_own_early h6 (s := 0) (by omega)
  have := solo_other_late hsolo hkj (s := 0) hw0
  exact (TimedExecution.mem_snapshot _ _ _ _).mpr
    ⟨e.actor_valid v0 j (e.eventTime_actor hv0), v0, r1, hv0, hr1, by omega⟩

variable [DecidableEq Op]

/-- **The solo process commits its own input.**  This is the step the manuscript
takes by Commitment and Validity on the prefix: with `j` the only participant,
`j` commits `s_j`. -/
theorem solo_output : e.history.output j = some (e.input j, true) := by
  obtain ⟨-, hres, hcom⟩ := e.timed.views.solo_result (solo_returned h6)
    (solo_aView hsolo h6) (solo_bView hsolo h6)
  refine (e.timed.views.output_iff j _ _).mpr ⟨solo_returned h6, hres.symm, ?_⟩
  exact (@decide_eq_true _ (Classical.propDecidable _) hcom).symm

/-- Every output trace is the solo process's input. -/
theorem solo_outputs {i : P} {t : obj.Trace} {c : Bool} (h : e.history.output i = some (t, c)) :
    t = e.input j := by
  obtain ⟨hiR, rfl, -⟩ := (e.timed.views.output_iff i t c).mp h
  exact e.timed.views.solo_agreement (solo_returned h6) (solo_aView hsolo h6)
    (solo_bView hsolo h6) (solo_late_bView hsolo h6) (solo_late_aView hsolo h6) i hiR

end Solo

/-- **Lemma `GCA_soloagg`: Algorithm 2 satisfies Solo agreement**, above the
assumed atomic snapshot objects, for every execution — including crashes
between any two protocol events and processes that never return. -/
theorem soloAgreement [DecidableEq Op] : e.SoloAgreement := by
  intro T j hsolo h6
  exact ⟨e.input j, true, solo_output hsolo h6, fun i t c h => solo_outputs hsolo h6 h⟩

/-- All seven GCA properties of Algorithm 2: the six of §4.2 and Solo agreement. -/
theorem specification_soloAgreement [DecidableEq Op] :
    e.history.Specification ∧ e.SoloAgreement :=
  ⟨e.specification, e.soloAgreement⟩

end Protocol
end ConflictFreedom.GCA
