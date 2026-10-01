import CFLeanProof.WeakConflictFreedom

/-!
# Weak conflict-freedom of Algorithm 1, assembled

`WeakConflictFreedom.lean` proves the hard half of Theorem `weakUCWCF`:
`no_stall` says that a run whose response history freezes at some time `T`,
while the commands of pending operations do not conflict and the processes that
still call GCA rounds keep stepping, is impossible.

This module supplies the bookkeeping the paper performs in one sentence --

> It follows that there exists a time `τ' ≥ τ` after which only correct
> processes take steps and all their operations are pending forever.

-- and turns `no_stall` into the positive statement of weak conflict-freedom:
*some process that takes infinitely many steps completes every operation it
invokes.*

The bookkeeping is the following.  Suppose, for contradiction, that no process
completes all of its operations.  Fix a process `q`.  Either `q` stops taking
steps at some time `N_q`, or `q` has an invoked command `a_q` that never gets a
response.  In the second case `q` is *stuck on* `a_q`: an invocation makes
`a_q` the process's active command, and a process's active command can change
only by a `finish` step, which would record `a_q`'s response
(`activeCmd_persists`).  So in either case there is a time beyond which `q`
performs no `finish`.  Since there are finitely many processes, the maximum `T`
of those times is a point after which the response history cannot change, and
`no_stall` closes the argument.

The final theorem is stated at the level of the global schedule, like
`solo_completes`.
-/

namespace ConflictFreedom.WeakUniversal
open Object
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The command a process is currently executing, if any.  `idle` is the only
state without one, and it is the only state an `invoke` step is enabled in. -/
abbrev activeCmd : Local (n := n) obj → Option (Cmd n Op) := Local.command obj

/-- Only the acting process can record a response, and it records the response
of the command it is currently executing. -/
theorem stepBy_records_return {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    (hne : d.returns ≠ c.returns) :
    ∃ cmd r s, c.localState p = .returning cmd r s ∧
      (⟨cmd, r, s⟩ : Return (n := n) obj) ∈ d.returns := by
  cases h.1 with
  | finish q cmd r s hq =>
      obtain rfl := eq_of_update_ne h.moves
      exact ⟨cmd, r, s, hq, List.mem_cons_self⟩
  | _ => exact (hne rfl).elim

/-- A step of `p` either keeps `p`'s active command or is the `finish` step that
records that command's response.  In particular `invoke`, which would change the
active command, is enabled only from `idle`. -/
theorem stepBy_activeCmd {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} (hc : activeCmd obj (c.localState p) = some cmd) :
    activeCmd obj (d.localState p) = some cmd ∨
      ∃ r s, (⟨cmd, r, s⟩ : Return (n := n) obj) ∈ d.returns := by
  obtain ⟨hstep, -⟩ := h
  cases hstep with
  | invoke q op hq =>
      by_cases hpq : p = q
      · subst hpq; rw [hq] at hc; exact absurd hc (by simp [activeCmd, Local.command])
      · left; show activeCmd obj (update _ q _ p) = _
        simpa [update, hpq] using hc
  | receive q cmd' r prop s flag hq ho =>
      by_cases hpq : p = q
      · subst hpq
        rw [hq] at hc
        left; show activeCmd obj (update _ p _ p) = _
        rw [update_self]
        by_cases hf : flag = true ∧ 0 < (Tagged obj).traceCount cmd' s
        · simpa [hf, activeCmd, Local.command] using hc
        · simpa [hf, activeCmd, Local.command] using hc
      · left; show activeCmd obj (update _ q _ p) = _
        simpa [update, hpq] using hc
  | read q _ _ _ _ hq | collected q _ _ hq | propose q _ _ hq _ | publish q _ _ _ hq =>
      by_cases hpq : p = q
      · subst hpq
        rw [hq] at hc
        left; show activeCmd obj (update _ p _ p) = _
        simpa [update, activeCmd, Local.command] using hc
      · left; show activeCmd obj (update _ q _ p) = _
        simpa [update, hpq] using hc
  | finish q cmd' r s hq =>
      by_cases hpq : p = q
      · subst hpq
        rw [hq] at hc
        have he : cmd' = cmd := by
          simpa [activeCmd, Local.command] using hc
        subst he
        exact Or.inr ⟨r, s, List.mem_cons_self⟩
      · left; show activeCmd obj (update _ q _ p) = _
        simpa [update, hpq] using hc

/-- Invocations are added only by `invoke`, which simultaneously makes the new
command its process's active command. -/
theorem step_invocation {H : Environment (n := n) obj}
    {c d : Configuration (n := n) obj} (h : Step obj H c d)
    {cmd : Cmd n Op} (hin : cmd ∈ d.invocations) (hout : cmd ∉ c.invocations) :
    activeCmd obj (d.localState cmd.process) = some cmd := by
  cases h with
  | invoke q op hq =>
      rcases List.mem_cons.mp hin with rfl | hm
      · show activeCmd obj (update _ q _ q) = _
        simp [update, activeCmd, Local.command]
      · exact absurd hm hout
  | _ => exact absurd hin hout

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace WeakRun
variable (g : WeakRun obj H)

/-- A command whose response this run records. -/
def Completes (a : WeakUniversal.Cmd n Op) : Prop :=
  ∃ t r s, (⟨a, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈ (g.run.state t).returns

/-- A process scheduled infinitely often: the schedule-level counterpart of
`Execution.InfiniteSteps`. -/
def Stepping (p : Fin n) : Prop := ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p

/-- The execution is infinite: some process is scheduled at arbitrarily late
times.  This is the paper's standing assumption on `α`. -/
def Live : Prop := ∀ N, ∃ t, N ≤ t ∧ g.actor t ≠ none

/-- An infinite execution of finitely many processes has a process that takes
infinitely many steps. -/
theorem exists_stepping (hlive : g.Live) : ∃ p, g.Stepping p := by
  classical
  apply Classical.byContradiction
  intro h
  have bounds : ∀ p : Fin n, ∃ N, ∀ t, N ≤ t → g.actor t ≠ some p := by
    intro p
    have hp : ¬ g.Stepping p := fun hp => h ⟨p, hp⟩
    obtain ⟨N, hN⟩ := Classical.not_forall.mp hp
    exact ⟨N, fun t ht he => hN ⟨t, ht, he⟩⟩
  obtain ⟨N, hN⟩ := fin_bounded n (fun p => Classical.choose (bounds p))
  obtain ⟨t, ht, hne⟩ := hlive N
  rcases hp : g.actor t with _ | p
  · exact hne hp
  · exact Classical.choose_spec (bounds p) t (Nat.le_trans (hN p) ht) hp

/-- Every invoked command was, at some time, its process's active command. -/
theorem invoked_active {a : WeakUniversal.Cmd n Op} (h : g.Invoked a) :
    ∃ τ, WeakUniversal.activeCmd obj ((g.run.state τ).localState a.process) = some a := by
  classical
  obtain ⟨t, ht⟩ := h
  induction t with
  | zero =>
      rw [g.run.initial_state] at ht
      simp [WeakUniversal.initial] at ht
  | succ t ih =>
      by_cases hprev : a ∈ (g.run.state t).invocations
      · exact ih hprev
      · rcases g.run.next t with he | hs
        · exact absurd (he ▸ ht) hprev
        · exact ⟨t + 1, WeakUniversal.step_invocation obj hs ht hprev⟩

/-- **A process is stuck on a command that never returns.**  An active command
can only be replaced by the `finish` step that records its response, so a
command with no response stays active forever. -/
theorem activeCmd_persists {p : Fin n} {a : WeakUniversal.Cmd n Op} {τ : Nat}
    (hτ : WeakUniversal.activeCmd obj ((g.run.state τ).localState p) = some a)
    (hnr : ¬ g.Completes a) :
    ∀ t, τ ≤ t → WeakUniversal.activeCmd obj ((g.run.state t).localState p) = some a := by
  intro t ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction d with
  | zero => exact hτ
  | succ d ih =>
      show WeakUniversal.activeCmd obj ((g.run.state ((τ + d) + 1)).localState p) = some a
      rcases g.step_actor (τ + d) with ⟨-, heq⟩ | ⟨q, -, hstep⟩ | ⟨q, r, -, -, heq⟩
      · rw [heq]; exact ih
      · by_cases hqp : q = p
        · subst hqp
          rcases WeakUniversal.stepBy_activeCmd obj hstep ih with hkeep | ⟨r, s, hmem⟩
          · exact hkeep
          · exact absurd ⟨τ + d + 1, r, s, hmem⟩ hnr
        · rw [hstep.2 p (fun e => hqp e.symm)]; exact ih
      · rw [heq]; exact ih

/-- A process stuck on a command that never returns performs no `finish` step,
so its steps leave the response history unchanged. -/
theorem returns_stable_of_stuck {p : Fin n} {a : WeakUniversal.Cmd n Op} {τ : Nat}
    (hτ : WeakUniversal.activeCmd obj ((g.run.state τ).localState p) = some a)
    (hnr : ¬ g.Completes a) :
    ∀ t, τ ≤ t → g.actor t = some p →
      (g.run.state (t + 1)).returns = (g.run.state t).returns := by
  intro t ht hact
  apply Classical.byContradiction
  intro hne
  rcases g.step_or_stutter hact with hstep | ⟨-, heq⟩
  · obtain ⟨cmd, r, s, hL, hmem⟩ := WeakUniversal.stepBy_records_return obj hstep hne
    have hcmd : WeakUniversal.activeCmd obj ((g.run.state t).localState p) = some cmd := by
      rw [hL]; rfl
    have : cmd = a := by
      have := g.activeCmd_persists hτ hnr t ht
      exact Option.some.inj (hcmd.symm.trans this)
    subst this
    exact hnr ⟨t + 1, r, s, hmem⟩
  · exact hne (congrArg WeakUniversal.Configuration.returns heq)

/-- A process that stops being scheduled trivially stops changing the response
history. -/
theorem returns_stable_of_silent {p : Fin n} {N : Nat}
    (h : ∀ t, N ≤ t → g.actor t ≠ some p) :
    ∀ t, N ≤ t → g.actor t = some p →
      (g.run.state (t + 1)).returns = (g.run.state t).returns :=
  fun t ht hact => absurd hact (h t ht)

/-- If every process eventually stops recording responses, the response history
freezes.  This produces the time `T` that `no_stall` refutes. -/
theorem returns_frozen (bnd : Fin n → Nat)
    (hb : ∀ p t, bnd p ≤ t → g.actor t = some p →
      (g.run.state (t + 1)).returns = (g.run.state t).returns)
    {T : Nat} (hT : ∀ p, bnd p ≤ T) :
    ∀ t, T ≤ t → (g.run.state t).returns = (g.run.state T).returns := by
  intro t ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction d with
  | zero => rfl
  | succ d ih =>
      show (g.run.state ((T + d) + 1)).returns = _
      refine Eq.trans ?_ ih
      rcases hact : g.actor (T + d) with _ | p
      · rcases g.step_actor (T + d) with ⟨-, heq⟩ | ⟨q, hq, -⟩ | ⟨q, r, hq, -, heq⟩
        · exact congrArg WeakUniversal.Configuration.returns heq
        · exact absurd (hq.symm.trans hact) (by simp)
        · exact congrArg WeakUniversal.Configuration.returns heq
      · exact hb p (T + d) (Nat.le_trans (hT p) (by omega)) hact

/-- **The response history freezes.**  This is the manuscript's "there exists a
time `τ'` after which only correct processes take steps and all their operations
are pending forever", in the contradiction setting where no process completes
every command it invokes. -/
theorem returns_freeze_of_not_completing
    (hgoal : ¬ ∃ p, g.Stepping p ∧ ∀ a, g.Invoked a → a.process = p → g.Completes a) :
    ∃ T, ∀ t, T ≤ t → (g.run.state t).returns = (g.run.state T).returns := by
  classical
  -- Each process eventually stops recording responses.
  have hstop : ∀ p : Fin n, ∃ N, ∀ t, N ≤ t → g.actor t = some p →
      (g.run.state (t + 1)).returns = (g.run.state t).returns := by
    intro p
    have hp : ¬ (g.Stepping p ∧ ∀ a, g.Invoked a → a.process = p → g.Completes a) :=
      fun h => hgoal ⟨p, h⟩
    by_cases hsteps : g.Stepping p
    · -- `p` is stuck on an invoked command that never returns.
      have hbad : ¬ ∀ a, g.Invoked a → a.process = p → g.Completes a :=
        fun h => hp ⟨hsteps, h⟩
      obtain ⟨a, ha⟩ := Classical.not_forall.mp hbad
      have hinv : g.Invoked a := by
        apply Classical.byContradiction
        intro hc; exact ha (fun h => absurd h hc)
      have ha2 : ¬ (a.process = p → g.Completes a) := fun h => ha (fun _ => h)
      have hproc : a.process = p := by
        apply Classical.byContradiction
        intro hc; exact ha2 (fun h => absurd h hc)
      have hnc : ¬ g.Completes a := fun h => ha2 (fun _ => h)
      obtain ⟨τ, hτ⟩ := g.invoked_active hinv
      rw [hproc] at hτ
      exact ⟨τ, g.returns_stable_of_stuck hτ hnc⟩
    · -- `p` stops taking steps.
      obtain ⟨N, hN⟩ := Classical.not_forall.mp hsteps
      refine ⟨N, fun t ht hact => absurd ⟨t, ht, hact⟩ hN⟩
  obtain ⟨T, hT⟩ := fin_bounded n (fun p => Classical.choose (hstop p))
  exact ⟨T, g.returns_frozen _ (fun p => Classical.choose_spec (hstop p)) hT⟩

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H)

/-- **Weak conflict-freedom of Algorithm 1, eventually-conflict-free half**, in
the form that takes compatibility of each round's proposals directly.  Some
process takes infinitely many steps and *every* command it invokes gets a
response -- the positive form of "it cannot be the case that no process
completes all its operations". -/
theorem some_process_completes_all_of_compatible (coverage : WeakUniversal.CallsCovered obj (H))
    (hlive : g.Live) {k₀ : Nat}
    (hk₀ : ∀ k, k₀ ≤ k →
      (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs)
    (hcallers : ∀ k, k₀ ≤ k →
      ∀ q, (∃ s, (H (k + 2)).input q = some s) →
        ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q) :
    ∃ p, g.Stepping p ∧ ∀ a, g.Invoked a → a.process = p → g.Completes a := by
  classical
  apply Classical.byContradiction
  intro hgoal
  obtain ⟨T, hfrozen⟩ := g.returns_freeze_of_not_completing hgoal
  obtain ⟨p, hp⟩ := g.exists_stepping hlive
  exact g.no_stall_of_compatible coverage hp hk₀ hcallers hfrozen

/-- **Theorem `weakUCWCF`, eventually-conflict-free half, from the manuscript's
own hypothesis.**  The conflict assumption is §3's -- beyond some time, two
simultaneously pending commands do not conflict -- not the round-indexed
`Pending k`.  The conversion is legitimate exactly here, because the
contradiction setting freezes the response history
(`returns_freeze_of_not_completing`), and that is what
`nonconflicting_pending_of_eventually` needs. -/
theorem some_process_completes_all_of_eventually (coverage : WeakUniversal.CallsCovered obj (H))
    (hlive : g.Live) {T₀ : Nat} (hC : g.EventuallyNonconflicting T₀) :
    ∃ p, g.Stepping p ∧ ∀ a, g.Invoked a → a.process = p → g.Completes a := by
  classical
  apply Classical.byContradiction
  intro hgoal
  obtain ⟨T, hfrozen⟩ := g.returns_freeze_of_not_completing hgoal
  obtain ⟨BR, hBR⟩ := WeakUniversal.returns_round_bound obj (g.run.state T).returns
  obtain ⟨B, hB⟩ := g.eventually_callers_stepping
  obtain ⟨p, hp⟩ := g.exists_stepping hlive
  refine g.no_stall_of_compatible coverage hp (k₀ := max BR B) ?_ ?_ hfrozen
  · intro k hk
    exact g.inputs_compatible_total coverage
      (g.nonconflicting_pending_of_eventually hC hfrozen
        (fun ret hret => Nat.le_trans (hBR ret hret) (by omega)))
  · intro k hk; exact hB k (by omega)

/-- `some_process_completes_all_of_compatible` under the paper's nonconflict
hypothesis: this is the eventually-conflict-free half of `weakUCWCF`. -/
theorem some_process_completes_all (coverage : WeakUniversal.CallsCovered obj (H))
    (hlive : g.Live)
    (hC : ∃ k₀, ∀ k, k₀ ≤ k →
      (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k)) :
    ∃ p, g.Stepping p ∧ ∀ a, g.Invoked a → a.process = p → g.Completes a := by
  obtain ⟨k₀, hk₀⟩ := hC
  obtain ⟨B, hB⟩ := g.eventually_callers_stepping
  exact g.some_process_completes_all_of_compatible coverage hlive (k₀ := max k₀ B)
    (fun k hk => g.inputs_compatible_total coverage (hk₀ k (by omega)))
    (fun k hk => hB k (by omega))

/-- **Theorem `weakUCWCF` for Algorithm 1, at the level of the global
schedule.**  Both halves of the manuscript's statement:

* *eventual step-contention-freedom* -- a process that eventually runs solo
  completes *its own* pending operation, after the solo phase begins
  (`solo_completes`);
* *eventual conflict-freedom* -- stated with the manuscript's own §3
  hypothesis, over **time**: beyond some instant, two simultaneously pending
  commands do not conflict.  (The round-indexed `Pending k` is a different and
  in general stronger condition; `nonconflicting_pending_of_eventually` derives
  it where the proof needs it.)  Some infinitely stepping process then completes
  every operation it invokes.

The conclusion is stated over the program run rather than over an extracted
`ConflictFreedom.Execution`.  Call coverage is *not* a hypothesis: it is derived from the
schedule (`WeakRun.callsCovered`), so the only assumptions left are the GCA
interface — the six properties and "every correct participant returns"
(`WeakRun.GCAInterface`), for any GCA objects — and the manuscript's own conflict
hypotheses.  For Algorithm 2 the interface is `Weak.gcaInterface`. -/
theorem weakUCWCF :
    (∀ (p : Fin n) (N : Nat), g.SoloFrom N p →
      ∃ u v cmd r s, N ≤ u ∧ u < v ∧ cmd.process = p ∧
        (g.run.state u).localState p = .returning cmd r s ∧
        (⟨cmd, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈
          (g.run.state v).returns) ∧
    (g.Live → (∃ T₀, g.EventuallyNonconflicting T₀) →
      ∃ p, g.Stepping p ∧ ∀ a, g.Invoked a → a.process = p → g.Completes a) :=
  ⟨fun _ _ hsolo => g.solo_completes hsolo,
    fun hlive ⟨_, hC⟩ =>
      g.some_process_completes_all_of_eventually g.callsCovered hlive hC⟩

end WeakGCA
end ConflictFreedom.GlobalSchedule
