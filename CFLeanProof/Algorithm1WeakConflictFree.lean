import CFLeanProof.Algorithm1

/-! # Algorithm 1 is weakly conflict-free, in §3's vocabulary

`WeakGCA.execution_some_process_completes_all` already proves the content of
Theorem `theorem:weakUCWCF`'s eventually-conflict-free half, but exhibits its
process as `g.Stepping p` — scheduled infinitely often in the global schedule.
§3's `WeakConflictFree` asks instead for `Execution.InfiniteSteps p`,
infinitely many *operation* steps owned by `p`.  This module supplies the
bridge: a scheduled process either holds a current command, and then the
operation clock ticks for it at once, or is idle, and then `step_actor` forces
it to `invoke`, so it holds one at its next scheduled tick. -/

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace WeakRun
variable (g : WeakRun obj H) (hp : g.OpLive)

include hp in
/-- Operation-level liveness is liveness. -/
theorem live_of_opLive : g.Live := by
  intro N
  obtain ⟨t, ht, hsome⟩ := hp N
  obtain ⟨cmd, hcmd⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨q, hq, -⟩ := g.opActor_eq_some hcmd
  exact ⟨t + 1, by omega, by rw [hq]; simp⟩

/-- A process scheduled infinitely often owns operation steps at arbitrarily
late times. -/
theorem opActor_infinitely {p : Fin n}
    (hstep : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (N : Nat) :
    ∃ t, N ≤ t ∧ ∃ cmd, g.opActor t = some cmd ∧ cmd.process = p := by
  classical
  obtain ⟨t₀, ht₀, hact₀⟩ := hstep (N + 1)
  obtain ⟨t, rfl⟩ : ∃ t, t₀ = t + 1 := ⟨t₀ - 1, by omega⟩
  cases hcmd : ((g.run.state (t + 1)).localState p).command obj with
  | some cmd =>
      refine ⟨t, by omega, cmd, ?_, ?_⟩
      · show g.opActor t = some cmd
        unfold WeakRun.opActor
        rw [hact₀]
        exact hcmd
      · exact (((g.run.ledgerRun obj).valid (t + 1)).active_tag p cmd hcmd).1
  | none =>
      -- `p` is idle; it invokes now and still holds the command when next run
      have hidle : (g.run.state (t + 1)).localState p = .idle :=
        WeakUniversal.localState_idle_of_command obj hcmd
      rcases g.step_or_stutter hact₀ with hstepby | ⟨⟨r, hrd⟩, -⟩
      · have hne := WeakUniversal.stepBy_from_idle obj hstepby hidle
        obtain ⟨t₁, ⟨ht₁, hact₁⟩, hmin⟩ :=
          exists_least (fun w => t + 2 ≤ w ∧ g.actor w = some p)
            (by obtain ⟨w, hw, hactw⟩ := hstep (t + 2); exact ⟨w, hw, hactw⟩)
        have hconst : (g.run.state t₁).localState p
            = (g.run.state (t + 2)).localState p :=
          g.localState_const_of_unscheduled ht₁
            (fun v hv hvt hq => absurd (hmin v ⟨hv, hq⟩) (by omega))
        obtain ⟨t₂, rfl⟩ : ∃ t₂, t₁ = t₂ + 1 := ⟨t₁ - 1, by omega⟩
        cases hcmd₁ : ((g.run.state (t₂ + 1)).localState p).command obj with
        | none => exact absurd (hconst ▸ hcmd₁) hne
        | some cmd =>
            refine ⟨t₂, by omega, cmd, ?_, ?_⟩
            · show g.opActor t₂ = some cmd
              unfold WeakRun.opActor
              rw [hact₁]
              exact hcmd₁
            · exact (((g.run.ledgerRun obj).valid (t₂ + 1)).active_tag p cmd hcmd₁).1
      · rw [hidle] at hrd
        exact absurd hrd (by simp [weakRound])

/-- **The bridge.**  Scheduling in the global schedule gives operation steps. -/
theorem infiniteSteps_of_stepping {p : Fin n}
    (hstep : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    (g.execution hp).InfiniteSteps p := by
  intro N
  obtain ⟨t, ht, cmd, hop, hproc⟩ := g.opActor_infinitely hstep N
  obtain ⟨i, hi, hval⟩ := (g.schedule hp).actorInst_of_actor hop
  exact ⟨t, i, ht, hi, by
    show i.val.process = p
    rw [hval]; exact hproc⟩

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H) (hp : g.OpLive)

/-- **Theorem `theorem:weakUCWCF`, conflict-free half, in §3's vocabulary.** -/
theorem execution_weakConflictFree_half (h : (g.execution hp).EventuallyConflictFree obj.Conflict) :
    ∃ p, (g.execution hp).InfiniteSteps p ∧
      ∀ i, (g.execution hp).owner i = p → (g.execution hp).Completes i := by
  obtain ⟨p, hstep, hall⟩ :=
    g.execution_some_process_completes_all hp (g.live_of_opLive hp) h
  exact ⟨p, g.infiniteSteps_of_stepping hp hstep, hall⟩

end WeakGCA
end ConflictFreedom.GlobalSchedule

namespace ConflictFreedom
variable {State Op Response : Type} [DecidableEq Op]

/-- **Theorem `theorem:weakUCWCF`: Algorithm 1 over any GCA meeting the
interface is weakly conflict-free**, in the manuscript's §3 sense. -/
theorem algorithm1AnyGCA_weakConflictFree (obj : Object State Op Response) (n : Nat) :
    WeakConflictFree (algorithm1AnyGCA obj n) obj.Conflict := by
  refine ⟨algorithm1AnyGCA_obstructionFree obj n, ?_⟩
  rintro e ⟨H, g, hp, rfl⟩ h
  exact g.execution_weakConflictFree_half hp h

/-- **Algorithm 1 is weakly conflict-free**, in the manuscript's §3 sense — over
Algorithm 2, which meets the interface (`algorithm1_anyGCA`). -/
theorem algorithm1_weakConflictFree (obj : Object State Op Response) (n : Nat) :
    WeakConflictFree (algorithm1 obj n) obj.Conflict :=
  ⟨fun e he => (algorithm1AnyGCA_weakConflictFree obj n).1 e (algorithm1_anyGCA obj n e he),
    fun e he => (algorithm1AnyGCA_weakConflictFree obj n).2 e (algorithm1_anyGCA obj n e he)⟩

end ConflictFreedom
