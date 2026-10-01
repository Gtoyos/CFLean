import CFLeanProof.HelpingInvariantTwo
import CFLeanProof.Algorithm3

/-! # Algorithm 3 is conflict-free, in §3's vocabulary

The manuscript's Lemma `lemma:UCV2isCF` restated over the extracted operation
level: every operation instance of a correct process completes as soon as the
run is eventually step-contention-free *or* eventually conflict-free.  The
second half rests on `HelpingInvariantTwo`, i.e. on the manuscript's two
invariants. -/

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingRun
variable (g : HelpingRun obj H) (hp : g.OpLive)

/-- A process that owns infinitely many operation steps is scheduled infinitely
often by the global schedule. -/
theorem stepping_of_infiniteSteps {p : Fin n}
    (h : (g.execution hp).InfiniteSteps p) :
    ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p := by
  intro N
  obtain ⟨t, i, ht, hact, hown⟩ := h N
  exact ⟨t + 1, by omega, by rw [g.execution_actor_val hp hact, ← hown]; rfl⟩

/-- §3's time-based hypothesis on the extracted execution gives the
schedule-level one. -/
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

/-- A schedule-level response for an instance's command is that instance's
completion. -/
theorem execution_completes_of_command {i : (g.execution hp).Instance}
    (h : g.Completes i.val) : (g.execution hp).Completes i := by
  obtain ⟨t, r, s, hmem⟩ := h
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := by
    refine ⟨t - 1, ?_⟩
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · rw [g.run.initial_state] at hmem
      simp [HelpingUniversal.initial] at hmem
    · omega
  exact ((g.schedule hp).execution_completes_iff i).mpr
    ⟨t', List.mem_map.mpr ⟨⟨i.val, r, s⟩, hmem, rfl⟩⟩

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H) (hp : g.OpLive)

/-- **The §3 property, pointwise: Algorithm 3 is conflict-free.** -/
theorem execution_conflictFree :
    ∀ i, (g.execution hp).Correct ((g.execution hp).owner i) →
      ((g.execution hp).Solo i ∨
        (g.execution hp).EventuallyConflictFree obj.Conflict) →
      (g.execution hp).Completes i := by
  rintro i hcorrect (hsolo | hcf)
  · exact g.solo_instance_completes hp hsolo
  · rcases hcorrect with hinf | hall
    · obtain ⟨T₀, hC⟩ := g.eventuallyNonconflicting_of_execution hp hcf
      obtain ⟨t, ht⟩ := i.property
      exact g.execution_completes_of_command hp
        (g.invoked_completes_time g.callsCovered
          (g.stepping_of_infiniteSteps hp hinf) hC ⟨t + 1, ht⟩ rfl)
    · exact hall i rfl

end HelpingGCA
end ConflictFreedom.GlobalSchedule

namespace ConflictFreedom
variable {State Op Response : Type} [DecidableEq Op]

/-- **Lemma `lemma:UCV2isCF`: Algorithm 3 over any GCA meeting the interface
is conflict-free**, in the manuscript's §3 sense: every operation of a correct
process completes whenever the operation is eventually step-contention-free
*or* the execution is eventually conflict-free. -/
theorem algorithm3AnyGCA_conflictFree (obj : Object State Op Response) (n : Nat) :
    ConflictFree (algorithm3AnyGCA obj n) obj.Conflict := by
  rintro e ⟨H, g, hp, rfl⟩ i hcorrect hor
  exact g.execution_conflictFree hp i hcorrect hor

/-- **Algorithm 3 is conflict-free**, in the manuscript's §3 sense — over
Algorithm 2, which meets the interface (`algorithm3_anyGCA`). -/
theorem algorithm3_conflictFree (obj : Object State Op Response) (n : Nat) :
    ConflictFree (algorithm3 obj n) obj.Conflict := fun e he =>
  algorithm3AnyGCA_conflictFree obj n e (algorithm3_anyGCA obj n e he)

end ConflictFreedom
