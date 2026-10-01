import CFLeanProof.UniversalProgress
import CFLeanProof.GCACausality

/-! # Why fairness must be read on the projected protocol clock

`GlobalSchedule.Weak.Fair` requires a scheduled, waiting process to take its
program step only once the projected protocol clock shows the last stage.
`StrongFair` is the same condition with that guard removed — "this call
returns somewhere in the protocol's own timeline" instead of "it has returned
by now".  The manuscript's phrase is "has *already* produced its output", so
`StrongFair` is the wrong reading, and this module shows it is not merely
stronger but **unsatisfiable**: in a strongly fair schedule, a process that is
ever blocked in a GCA call and keeps being scheduled yields a contradiction,
so no operation can ever return.

The obstruction is structural.  `receive_ready` lets a caller leave `waiting`
only after six of its own protocol events, and those events are exactly the
instants at which it is scheduled while waiting.  `StrongFair` forces the
program step at the *first* such instant, when no event has happened yet.
-/
namespace ConflictFreedom.GlobalSchedule
open WeakUniversal (Cmd Tagged)
variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {f : UniversalProtocol.Family (n := n) obj}

namespace Weak
variable (g : Weak obj f)

/-- If `p` has contributed no round-`r` event before `T`, its protocol phase at
the projected clock is still zero.  Events of *other* processes advance the
round's clock but, by `gca_actor`, are attributed to those processes. -/
theorem phase_zero_of_no_event {p : Fin n} {r T : Nat}
    (hno : ∀ u, u < T → ¬ (g.actor u = some p ∧
      weakRound obj ((g.run.state u).localState p) = some r)) :
    (f.protocol r).phase (gcaClock obj g.run.state g.actor T r) p = 0 := by
  have key : ∀ c, c ≤ gcaClock obj g.run.state g.actor T r →
      (f.protocol r).phase c p = 0 := by
    intro c
    induction c with
    | zero => intro _; rfl
    | succ c ih =>
      intro hc
      have hlt : c < gcaClock obj g.run.state g.actor T r := by omega
      have hactor : ¬ (f.protocol r).actor c = some p := by
        intro hp
        obtain ⟨u, q, hu, hcu, he⟩ := g.inter.event_before_clock hlt
        have hq := g.inter.actor_matches u r q he
        rw [hcu] at hq
        have hqp : q = p := Option.some.inj (hq.symm.trans hp)
        subst q
        exact hno u hu (gcaEvent_inv obj he)
      rw [GCA.Protocol.phase, ite_eq_right hactor]
      exact ih (by omega)
  exact key _ (Nat.le_refl _)

/-- **A strongly fair schedule never schedules a waiting process whose round
has an output.**  Strong fairness would force the program step, and
`receive_ready` would then demand six protocol events which, at the earliest
such instant, the process has not taken. -/
theorem strongFair_no_event (hfair : g.StrongFair) {p : Fin n} {r : Nat}
    (hout : ∃ s flag, (f.environment obj r).output p = some (s, flag)) :
    ∀ t, ¬ (g.actor t = some p ∧
      weakRound obj ((g.run.state t).localState p) = some r) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    rintro ⟨hact, hround⟩
    obtain ⟨cmd, proposal, hl⟩ : ∃ cmd proposal,
        (g.run.state t).localState p = .waiting cmd r proposal := by
      cases hls : (g.run.state t).localState p <;> simp [weakRound, hls] at hround
      rename_i cmd round proposal
      exact ⟨cmd, proposal, by simp [hround]⟩
    have hstep := hfair t p cmd r proposal hact hl hout
    obtain ⟨s, flag, _, hnew⟩ := WeakUniversal.stepBy_from_waiting obj hstep hl
    have hchange : (g.run.state (t + 1)).localState p ≠ (g.run.state t).localState p := by
      rw [hnew, hl]
      split <;> simp
    have h6 := g.receive_ready t p r hround hchange
    rw [g.phase_zero_of_no_event (fun u hu => ih u hu)] at h6
    exact absurd h6 (by omega)

/-- Under strong fairness a process blocked in a GCA call stays blocked. -/
theorem strongFair_waiting_step (hfair : g.StrongFair) {u : Nat} {p : Fin n}
    {cmd : Cmd n Op} {r : Nat} {proposal : (Tagged obj).Trace}
    (hl : (g.run.state u).localState p = .waiting cmd r proposal) :
    (g.run.state (u + 1)).localState p = (g.run.state u).localState p := by
  rcases g.step_actor u with ⟨-, heq⟩ | ⟨q, hq, hstep⟩ | ⟨q, r', -, -, heq⟩
  · rw [heq]
  · by_cases hqp : q = p
    · subst q
      obtain ⟨s, flag, ho, -⟩ := WeakUniversal.stepBy_from_waiting obj hstep hl
      exact absurd ⟨hq, by rw [hl]; rfl⟩ (g.strongFair_no_event hfair ⟨s, flag, ho⟩ u)
    · exact hstep.2 p (fun he => hqp he.symm)
  · rw [heq]

theorem strongFair_waiting_frozen (hfair : g.StrongFair) {t : Nat} {p : Fin n}
    {cmd : Cmd n Op} {r : Nat} {proposal : (Tagged obj).Trace}
    (hl : (g.run.state t).localState p = .waiting cmd r proposal) :
    ∀ u, t ≤ u → (g.run.state u).localState p = .waiting cmd r proposal := by
  intro u htu
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  clear htu
  induction d with
  | zero => simpa using hl
  | succ d ih =>
    show (g.run.state ((t + d) + 1)).localState p = _
    rw [g.strongFair_waiting_step hfair ih]
    exact ih

/-- **Strong fairness is unsatisfiable once any process makes a GCA call and
keeps being scheduled.**  Every completing execution of Algorithm 1 does both,
so the unguarded reading of fairness would make the progress theorems vacuous.
This is why `Fair` carries the projected-clock guard. -/
theorem strongFair_absurd (hfair : g.StrongFair) (hw : f.SnapshotWaitFree obj)
    {p : Fin n} (hsched : ∀ M, ∃ t, M ≤ t ∧ g.actor t = some p)
    {t : Nat} {cmd : Cmd n Op} {r : Nat} {proposal : (Tagged obj).Trace}
    (hl : (g.run.state t).localState p = .waiting cmd r proposal) : False := by
  have hfroz := g.strongFair_waiting_frozen hfair hl
  obtain ⟨s, flag, ho⟩ := g.blocked_output' hw hfroz hsched
  obtain ⟨u, htu, hact⟩ := hsched t
  exact g.strongFair_no_event hfair ⟨s, flag, ho⟩ u ⟨hact, by rw [hfroz u htu]; rfl⟩

end Weak
end ConflictFreedom.GlobalSchedule
