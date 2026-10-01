import CFLeanProof.UniversalLiveness

/-!
# Algorithm 1 as an `Implementation`, and its obstruction-freedom

The progress results are restated in the vocabulary of `Progress.lean`, about
the operation-level `Execution` model rather than about the global schedule.

`Execution.actor` is partial and `Execution.live` is the manuscript's
"infinite execution" assumption, so the extraction needs only `OpLive`: *some*
operation runs at arbitrarily late times.  Asking for an operation at every
instant would be contradictory with `n = 1`, since `Step.finish` leaves its
process idle for one instant.
-/

namespace ConflictFreedom.WeakUniversal
open Object
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

omit [DecidableEq Op] in
theorem localState_idle_of_command {c : Configuration (n := n) obj} {p : Fin n}
    (h : (c.localState p).command obj = none) : c.localState p = .idle := by
  cases hl : c.localState p with
  | idle => rfl
  | _ => rw [hl] at h; exact absurd h (by simp [Local.command])

/-- A `StepBy` attributed to `p` really moves `p`: an idle process that takes a
step invokes, and is no longer idle.  (`StepBy` pins every *other* process, so
the acting process must be `p` itself.) -/
theorem stepBy_from_idle {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    (hc : c.localState p = .idle) : (d.localState p).command obj ≠ none := by
  cases h.1 with
  | invoke q op hq =>
      obtain rfl := eq_of_update_ne h.moves
      show Local.command obj (update _ q _ q) ≠ none
      simp [update, Local.command]
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace WeakRun
variable (g : WeakRun obj H) (hp : g.OpLive)

/-- The operation instance scheduled at operation time `t` belongs to the
process the global schedule runs at `t + 1`. -/
theorem execution_actor_val {t : Nat} {i : (g.execution hp).Instance}
    (h : (g.execution hp).actor t = some i) :
    g.actor (t + 1) = some i.val.process :=
  g.schedule_scheduled hp ((g.schedule hp).actorInst_val h)

/-- If one instance is scheduled from `N` on, its process is scheduled from
`N + 1` on in the global schedule. -/
theorem solo_actor_of_solo_instance {i : (g.execution hp).Instance} {N : Nat}
    (hN : ∀ t, N ≤ t → (g.execution hp).actor t = some i) :
    ∀ t, N + 1 ≤ t → g.actor t = some i.val.process := by
  intro t ht
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact g.execution_actor_val hp (hN t' (by omega))

/-- While that instance is scheduled, it is the process's active command. -/
theorem active_of_solo_instance {i : (g.execution hp).Instance} {N : Nat}
    (hN : ∀ t, N ≤ t → (g.execution hp).actor t = some i) :
    ∀ t, N ≤ t →
      ((g.run.state (t + 1)).localState i.val.process).command obj = some i.val := by
  intro t ht
  exact (g.schedule hp).actor_active t i.val ((g.schedule hp).actorInst_val (hN t ht))

/-- A scheduled instance is `Solo` in the extracted execution. -/
theorem execution_solo {i : (g.execution hp).Instance} {N : Nat}
    (hN : ∀ t, N ≤ t → (g.execution hp).actor t = some i) : (g.execution hp).Solo i :=
  Or.inr ⟨N, fun t _j ht hact => Option.some.inj (hact.symm.trans (hN t ht))⟩

/-! ### From `Execution.Solo` to a solo schedule

`Execution.Solo i` only says that no *other* instance steps; the schedule may
idle, and other processes may still take the single `finish` step that answers
an operation invoked earlier.  These lemmas close that gap and produce a
`SoloFrom`, which is what the progress proofs consume. -/

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
      have hop : g.opActor t = some c := by rw [WeakRun.opActor, hq]; exact hcv
      rw [g.opActor_eq_of_solo hp hM (by omega) hop]

/-- **The bridge.**  From `Execution.Solo i` -- no other instance steps -- to a
`SoloFrom`: beyond a cutoff, nobody but `i`'s process is scheduled, and that
process keeps being scheduled.  The cutoff exists because a process scheduled
late is scheduled infinitely often (`FiniteScheduling.eventually_stepping`), and
a process other than `i`'s would have to be idle at each of those instants, yet
its own step out of `idle` gives it an active command. -/
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
    · exact absurd ((WeakUniversal.identity_invariant obj
        (g.run.reachable obj u)).active_tag q i.val h).1.symm hne
  refine ⟨max (M + 1) C, Nat.le_max_left _ _, ⟨?_, ?_⟩⟩
  · intro t q ht hq
    apply Classical.byContradiction
    intro hne
    have hstepping : FiniteScheduling.Stepping g.actor q :=
      hC t q (Nat.le_trans (Nat.le_max_right _ _) ht) hq
    -- `q` is idle at `t`, so its step at `t` is an invocation
    have h0 : ((g.run.state t).localState q).command obj = none :=
      hidle t q (Nat.le_trans (Nat.le_max_left _ _) ht) hq hne
    have h1 : ((g.run.state (t + 1)).localState q).command obj ≠ none := by
      rcases g.step_actor t with ⟨hnone, -⟩ | ⟨q', hq', hstep⟩ | ⟨q', r, hq', hrd, -⟩
      · exact absurd (hnone.symm.trans hq) (by simp)
      · have hqq : q' = q := Option.some.inj (hq'.symm.trans hq)
        subst hqq
        exact WeakUniversal.stepBy_from_idle obj hstep
          (WeakUniversal.localState_idle_of_command obj h0)
      · have hqq : q' = q := Option.some.inj (hq'.symm.trans hq)
        subst hqq
        obtain ⟨cmd, prop, hw⟩ := weakRound_eq_some hrd
        rw [hw] at h0
        exact absurd h0 (by simp [WeakUniversal.Local.command])
    -- but the next time `q` is scheduled it must be idle again
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

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H) (hp : g.OpLive)

/-- **Obstruction-freedom of Algorithm 1**, in the operation-level model.

The hypothesis is `Execution.Solo i` itself -- the §3 notion, which allows the
schedule to idle -- not "the instance is scheduled at every late instant".
`soloFrom_of_solo` bridges the two, and the whole solo chain was generalized to
`SoloFrom` so that it tolerates stuttering. -/
theorem solo_instance_completes {i : (g.execution hp).Instance} (hsolo : (g.execution hp).Solo i) :
    (g.execution hp).Completes i := by
  classical
  rcases hsolo with hc | ⟨M, hM⟩
  · exact hc
  obtain ⟨N, hNM, hsf⟩ := g.soloFrom_of_solo hp hM
  obtain ⟨u, hu, cmd, r, s, hL⟩ := g.solo_reaches_returning_from hsf N
  -- pin `cmd` to `i` at an instant where the process really is scheduled
  obtain ⟨u', ⟨hu', hact⟩, hmin⟩ :=
    exists_least (fun v => u ≤ v ∧ g.actor v = some i.val.process) (hsf.sched u)
  have hfrozen : g.run.state u' = g.run.state u :=
    g.state_frozen hsf (by omega) hu'
      (fun v hv hvu hqv => absurd (hmin v ⟨hv, hqv⟩) (by omega))
  have hL' : (g.run.state u').localState i.val.process = .returning cmd r s := by
    rw [hfrozen]; exact hL
  have hcmd : cmd = i.val := by
    obtain ⟨v, rfl⟩ : ∃ v, u' = v + 1 := ⟨u' - 1, by omega⟩
    refine g.opActor_eq_of_solo hp hM (t := v) (by omega) ?_
    rw [WeakRun.opActor, hact]
    show ((g.run.state (v + 1)).localState i.val.process).command obj = some cmd
    rw [hL']; rfl
  obtain ⟨w, -, hw2⟩ := g.returning_completes hsf.sched hL'
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := by
    refine ⟨w - 1, ?_⟩
    rcases Nat.eq_zero_or_pos w with rfl | hpos
    · rw [g.run.initial_state] at hw2; simp [WeakUniversal.initial] at hw2
    · omega
  refine ((g.schedule hp).execution_completes_iff i).mpr ⟨w', ?_⟩
  exact List.mem_map.mpr ⟨⟨cmd, r, s⟩, hw2, hcmd⟩

/-! ### The eventually-conflict-free half, in §3's vocabulary -/

end WeakGCA

namespace WeakRun
variable (g : WeakRun obj H) (hp : g.OpLive)

/-- Every instance of the extracted execution is a command this run invoked. -/
theorem invoked_of_instance (i : (g.execution hp).Instance) : g.Invoked i.val := by
  obtain ⟨t, ht⟩ := i.property
  exact ⟨t + 1, ht⟩

/-- A recorded response for an instance's command completes that instance. -/
theorem execution_completes_of_completes {i : (g.execution hp).Instance}
    (h : g.Completes i.val) : (g.execution hp).Completes i := by
  obtain ⟨t, r, s, hmem⟩ := h
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := by
    refine ⟨t - 1, ?_⟩
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rw [g.run.initial_state] at hmem; simp [WeakUniversal.initial] at hmem
    · omega
  refine ((g.schedule hp).execution_completes_iff i).mpr ⟨t', ?_⟩
  exact List.mem_map.mpr ⟨⟨i.val, r, s⟩, hmem, rfl⟩

/-- **§3's eventual conflict-freedom transfers to the program run.**  This is
the hypothesis `some_process_completes_all_of_eventually` consumes, so the
progress theorem is conditioned on the manuscript's own assumption about the
extracted execution rather than on a round-indexed surrogate. -/
theorem eventuallyNonconflicting_of_execution
    (h : (g.execution hp).EventuallyConflictFree obj.Conflict) :
    ∃ T₀, g.EventuallyNonconflicting T₀ := by
  obtain ⟨N, hN⟩ := ((g.schedule hp).execution_eventuallyConflictFree_iff obj.Conflict).mp h
  refine ⟨N + 1, ?_⟩
  intro t ht a b hai har hbi hbr hab
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  refine (obj.independent_iff_not_conflict a.operation b.operation).mpr ?_
  refine hN t' (by omega) a b hab hai (fun hm => ?_) hbi (fun hm => ?_)
  · obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
    exact har ret hret he
  · obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
    exact hbr ret hret he

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H) (hp : g.OpLive)

/-- **Theorem `weakUCWCF`, eventually-conflict-free half, in §3's vocabulary.**
Given `Execution.EventuallyConflictFree` on the extracted execution -- the
manuscript's own hypothesis -- some process takes infinitely many program steps
and completes *every* operation instance it owns. -/
theorem execution_some_process_completes_all (hlive : g.Live)
    (h : (g.execution hp).EventuallyConflictFree obj.Conflict) :
    ∃ p, g.Stepping p ∧ ∀ i : (g.execution hp).Instance,
      (g.execution hp).owner i = p → (g.execution hp).Completes i := by
  obtain ⟨T₀, hC⟩ := g.eventuallyNonconflicting_of_execution hp h
  obtain ⟨p, hstep, hall⟩ :=
    g.some_process_completes_all_of_eventually g.callsCovered hlive hC
  exact ⟨p, hstep, fun i hi =>
    g.execution_completes_of_completes hp
      (hall i.val (g.invoked_of_instance hp i) hi)⟩

/-- **The §3 property, pointwise.**  Every execution Algorithm 1 extracts from a
fair, operation-live global schedule satisfies `ConflictFreedom.ObstructionFree`
as unfolded at that execution. -/
theorem execution_obstructionFree :
    ∀ i, (g.execution hp).Correct ((g.execution hp).owner i) →
      (g.execution hp).Solo i → (g.execution hp).Completes i :=
  fun _ _ hsolo => g.solo_instance_completes hp hsolo

end WeakGCA
end ConflictFreedom.GlobalSchedule

/-! ## The `ConflictFreedom.ObstructionFree` wrapper

`WeakRun.soloFrom_of_solo` bridges `Execution.Solo` — which permits the idle
instants `Counterexamples.intermittentlyStalled` exhibits — to the continuous
`FiniteScheduling.SoloFrom` the progress chain needs, so
`execution_obstructionFree` holds from the §3 notion.  `Algorithm1.lean`
packages it as `algorithm1 : Implementation n Op` and proves
`ObstructionFree (algorithm1 obj n)`.  The wrapper is only meaningful with a
non-empty admitted set: `algorithm1_nonempty` supplies one from
`GlobalSchedule.Witness.rsched`, an infinite fair, operation-live, solo run
that completes one operation per cycle. -/
