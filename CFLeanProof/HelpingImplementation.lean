import CFLeanProof.HelpingProgress

/-!
# Algorithm 3 as an `Implementation`, and its obstruction-freedom

The helping construction's counterpart of `UniversalImplementation`: the solo
progress result is restated about the operation-level `Execution` model rather
than about the global schedule, so that `Progress.lean`'s `ObstructionFree`
applies to it by name.

Only the *solo* half is ported here.  The eventually-conflict-free half cannot
go the way Algorithm 1's does: `UCV2isCF` contradicts a *single* non-returning
command, so the response history does not freeze and the round/time conversion
of `nonconflicting_pending_of_eventually` is unavailable.  It is proved
separately, from the manuscript's two invariants
(`Algorithm3ConflictFree`, `algorithm3_conflictFree`).
-/

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Seed Environment update eq_of_update_ne apply_eq_of_update_ne)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

omit [DecidableEq Op] in
theorem localState_idle_of_command {c : Configuration (n := n) obj} {p : Fin n}
    (h : (c.localState p).command obj = none) : ∃ seed, c.localState p = .idle seed := by
  cases hl : c.localState p with
  | idle seed => exact ⟨seed, rfl⟩
  | _ => rw [hl] at h; exact absurd h (by simp [Local.command])

/-- A `StepBy` attributed to `p` really moves `p`: an idle process that takes a
step invokes, and is no longer idle. -/
theorem stepBy_from_idle {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {seed : Seed (n := n) obj} (hc : c.localState p = .idle seed) :
    (d.localState p).command obj ≠ none := by
  cases h.1 with
  | invoke q op s hq =>
      obtain rfl := eq_of_update_ne h.moves
      show Local.command obj (update _ q _ q) ≠ none
      simp [update, Local.command]
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingRun
variable (g : HelpingRun obj H) (hp : g.OpLive)

/-- The operation instance scheduled at operation time `t` belongs to the
process the global schedule runs at `t + 1`. -/
theorem execution_actor_val {t : Nat} {i : (g.execution hp).Instance}
    (h : (g.execution hp).actor t = some i) :
    g.actor (t + 1) = some i.val.process :=
  g.schedule_scheduled hp ((g.schedule hp).actorInst_val h)

/-- A scheduled instance is `Solo` in the extracted execution. -/
theorem execution_solo {i : (g.execution hp).Instance} {N : Nat}
    (hN : ∀ t, N ≤ t → (g.execution hp).actor t = some i) : (g.execution hp).Solo i :=
  Or.inr ⟨N, fun t _j ht hact => Option.some.inj (hact.symm.trans (hN t ht))⟩

/-- A process's local state does not move while it is not scheduled. -/
theorem localState_const_of_unscheduled {q : Fin n} {a b : Nat} (hab : a ≤ b)
    (hun : ∀ v, a ≤ v → v < b → g.actor v ≠ some q) :
    (g.run.state b).localState q = (g.run.state a).localState q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => rfl
  | succ d ih =>
      have hrest : ∀ v, a ≤ v → v < a + d → g.actor v ≠ some q :=
        fun v hv hvd => hun v hv (by omega)
      refine Eq.trans ?_ (ih (by omega) hrest)
      show (g.run.state ((a + d) + 1)).localState q = _
      rcases g.step_actor (a + d) with ⟨-, heq⟩ | ⟨q', hq', hstep⟩ | ⟨q', r, -, -, heq⟩
      · rw [heq]
      · have hne : q' ≠ q := by
          intro h; exact hun (a + d) (by omega) (by omega) (h ▸ hq')
        exact hstep.2 q (fun h => hne h.symm)
      · rw [heq]

/-- Under `Solo i`, every operation step after `M` is `i`'s own command. -/
theorem opActor_eq_of_solo {i : (g.execution hp).Instance} {M : Nat}
    (hM : ∀ t j, M ≤ t → (g.execution hp).actor t = some j → j = i)
    {t : Nat} (ht : M ≤ t) {c : WeakUniversal.Cmd n Op} (hc : g.opActor t = some c) :
    c = i.val := by
  obtain ⟨j, hj, hval⟩ := (g.schedule hp).actorInst_of_actor hc
  rw [← hval, hM t j ht hj]

/-- Whenever a process is scheduled after `M`, it is running `i`'s command or
nothing at all. -/
theorem active_of_solo {i : (g.execution hp).Instance} {M : Nat}
    (hM : ∀ t j, M ≤ t → (g.execution hp).actor t = some j → j = i)
    {u : Nat} (hu : M + 1 ≤ u) {q : Fin n} (hq : g.actor u = some q) :
    ((g.run.state u).localState q).command obj = none ∨
      ((g.run.state u).localState q).command obj = some i.val := by
  classical
  obtain ⟨t, rfl⟩ : ∃ t, u = t + 1 := ⟨u - 1, by omega⟩
  cases hcv : ((g.run.state (t + 1)).localState q).command obj with
  | none => exact Or.inl rfl
  | some c =>
      right
      have hop : g.opActor t = some c := by rw [HelpingRun.opActor, hq]; exact hcv
      rw [g.opActor_eq_of_solo hp hM (by omega) hop]

/-- **The bridge**, exactly as for Algorithm 1: from `Execution.Solo i` — no
other *instance* steps — to a `SoloFrom`, in which no other *process* is
scheduled and `i`'s process keeps being scheduled. -/
theorem soloFrom_of_solo {i : (g.execution hp).Instance} {M : Nat}
    (hM : ∀ t j, M ≤ t → (g.execution hp).actor t = some j → j = i) :
    ∃ N, M + 1 ≤ N ∧ g.SoloFrom N i.val.process := by
  classical
  obtain ⟨C, hC⟩ := FiniteScheduling.eventually_stepping g.actor
  have hidle : ∀ u q, M + 1 ≤ u → g.actor u = some q → q ≠ i.val.process →
      ((g.run.state u).localState q).command obj = none := by
    intro u q hu hqu hne
    rcases g.active_of_solo hp hM hu hqu with h | h
    · exact h
    · exact absurd ((HelpingUniversal.identity_invariant obj
        (g.run.reachable obj u)).active_tag q i.val h).1.symm hne
  refine ⟨max (M + 1) C, Nat.le_max_left _ _, ⟨?_, ?_⟩⟩
  · intro t q ht hq
    apply Classical.byContradiction
    intro hne
    have hstepping : FiniteScheduling.Stepping g.actor q :=
      hC t q (Nat.le_trans (Nat.le_max_right _ _) ht) hq
    have h0 : ((g.run.state t).localState q).command obj = none :=
      hidle t q (Nat.le_trans (Nat.le_max_left _ _) ht) hq hne
    have h1 : ((g.run.state (t + 1)).localState q).command obj ≠ none := by
      rcases g.step_actor t with ⟨hnone, -⟩ | ⟨q', hq', hstep⟩ | ⟨q', r, hq', hrd, -⟩
      · exact absurd (hnone.symm.trans hq) (by simp)
      · have hqq : q' = q := Option.some.inj (hq'.symm.trans hq)
        subst hqq
        obtain ⟨seed, hidle'⟩ := HelpingUniversal.localState_idle_of_command obj h0
        exact HelpingUniversal.stepBy_from_idle obj hstep hidle'
      · have hqq : q' = q := Option.some.inj (hq'.symm.trans hq)
        subst hqq
        obtain ⟨cmd, prop, hw⟩ := helpingRound_eq_some hrd
        rw [hw] at h0
        exact absurd h0 (by simp [HelpingUniversal.Local.command])
    obtain ⟨u, ⟨hu, hqu⟩, hmin⟩ :=
      exists_least (fun u => t + 1 ≤ u ∧ g.actor u = some q) (hstepping (t + 1))
    have hconst : (g.run.state u).localState q = (g.run.state (t + 1)).localState q :=
      g.localState_const_of_unscheduled hu
        (fun v hv hvu hqv => absurd (hmin v ⟨hv, hqv⟩) (by omega))
    exact h1 (hconst ▸ hidle u q (by omega) hqu hne)
  · intro Mx
    obtain ⟨t, j, ht, hact⟩ := (g.execution hp).live (max Mx (max (M + 1) C))
    have hji : j = i := hM t j (by omega) hact
    subst hji
    exact ⟨t + 1, by omega, g.schedule_scheduled hp ((g.schedule hp).actorInst_val hact)⟩

/-- Nothing happens at all while the solo process is not scheduled. -/
theorem state_frozen {N : Nat} {p : Fin n} (hsolo : g.SoloFrom N p)
    {a b : Nat} (hNa : N ≤ a) (hab : a ≤ b)
    (hun : ∀ v, a ≤ v → v < b → g.actor v ≠ some p) :
    g.run.state b = g.run.state a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => rfl
  | succ d ih =>
      have hrest : ∀ v, a ≤ v → v < a + d → g.actor v ≠ some p :=
        fun v hv hvd => hun v hv (by omega)
      refine Eq.trans ?_ (ih (by omega) hrest)
      show g.run.state ((a + d) + 1) = _
      rcases g.step_actor (a + d) with ⟨-, heq⟩ | ⟨q, hq, -⟩ | ⟨q, r, -, -, heq⟩
      · exact heq
      · exact absurd (hsolo.own (a + d) q (by omega) hq ▸ hq)
          (hun (a + d) (by omega) (by omega))
      · exact heq

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H) (hp : g.OpLive)

/-- **Obstruction-freedom of Algorithm 3**, in the operation-level model, from
the §3 notion `Execution.Solo i` itself. -/
theorem solo_instance_completes {i : (g.execution hp).Instance} (hsolo : (g.execution hp).Solo i) :
    (g.execution hp).Completes i := by
  classical
  rcases hsolo with hc | ⟨M, hM⟩
  · exact hc
  obtain ⟨N, hNM, hsf⟩ := g.soloFrom_of_solo hp hM
  obtain ⟨u, v, cmd, seed, seen, hu, huv, -, hL, hmem⟩ := g.solo_completes hsf
  obtain ⟨u', ⟨hu', hact⟩, hmin⟩ :=
    exists_least (fun w => u ≤ w ∧ g.actor w = some i.val.process) (hsf.sched u)
  have hfrozen : g.run.state u' = g.run.state u :=
    g.state_frozen hsf (by omega) hu'
      (fun w hw1 hw2 hqw => absurd (hmin w ⟨hw1, hqw⟩) (by omega))
  have hL' : (g.run.state u').localState i.val.process = .checking cmd seed [] seen := by
    rw [hfrozen]; exact hL
  have hcmd : cmd = i.val := by
    obtain ⟨w, rfl⟩ : ∃ w, u' = w + 1 := ⟨u' - 1, by omega⟩
    refine g.opActor_eq_of_solo hp hM (t := w) (by omega) ?_
    rw [HelpingRun.opActor, hact]
    show ((g.run.state (w + 1)).localState i.val.process).command obj = some cmd
    rw [hL']; rfl
  obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
  refine ((g.schedule hp).execution_completes_iff i).mpr ⟨v', ?_⟩
  exact List.mem_map.mpr ⟨⟨cmd, seen.round, seen.trace⟩, hmem, hcmd⟩

/-- **The §3 property, pointwise**, for Algorithm 3. -/
theorem execution_obstructionFree :
    ∀ i, (g.execution hp).Correct ((g.execution hp).owner i) →
      (g.execution hp).Solo i → (g.execution hp).Completes i :=
  fun _ _ hsolo => g.solo_instance_completes hp hsolo

end HelpingGCA
end ConflictFreedom.GlobalSchedule
