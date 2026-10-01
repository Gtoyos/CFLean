import CFLeanProof.ProgressWitness

/-! # Algorithm 1 as a §3 implementation

`Progress.lean` states the manuscript's progress conditions over a *set* of
admitted executions.  This module packages Algorithm 1 as such a set and
discharges `ObstructionFree` for it.

The wrapper is only meaningful if the admitted set is non-empty — otherwise
every progress condition would hold vacuously.
`algorithm1_nonempty` rules that out with `Witness.rsched`, an infinite run
over `n = m + 1` processes — one worker and `m` idle bystanders — that is
fair, operation-live, solo, above a wait-free snapshot interface, and
completes one operation per `m + 13`-step cycle.  It covers every process
count `n ≥ 1`.
-/
namespace ConflictFreedom
variable {State Op Response : Type} [DecidableEq Op]

/-- **Algorithm 1 over any GCA objects meeting the interface, as an
`Implementation`** — the manuscript's Algorithm 1, whose shared objects
`{GCA_k : k ≥ 1}` are used as a black box.  The admitted executions are the
operation-level executions of every operation-live run over any GCA histories
`H` whose objects satisfy `GlobalSchedule.WeakRun.GCAInterface`: the six
properties, Validity on every prefix, and every correct participant returns.
Nothing else about the GCA objects is fixed. -/
def algorithm1AnyGCA (obj : Object State Op Response) (n : Nat) : Implementation n Op :=
  fun e => ∃ (H : WeakUniversal.Environment (n := n) obj) (g : GlobalSchedule.WeakGCA obj H)
    (hp : g.OpLive), e = g.execution hp

/-- **Algorithm 1 over Algorithm 2, as an `Implementation`.**  The admitted
executions are the operation-level executions extracted from a fair,
operation-live global schedule of `WeakUniversal.Step` over the GCA protocol
family of Algorithm 2, above a wait-free snapshot interface. -/
def algorithm1 (obj : Object State Op Response) (n : Nat) : Implementation n Op :=
  fun e => ∃ (f : UniversalProtocol.Family (n := n) obj) (g : GlobalSchedule.Weak obj f)
    (hp : g.OpLive), g.Fair ∧ f.SnapshotWaitFree obj ∧ e = g.execution hp

/-- **Algorithm 2 is a GCA meeting the interface**: every execution of
Algorithm 1 over Algorithm 2 is an execution of Algorithm 1 over a GCA meeting
the interface (`GlobalSchedule.Weak.gcaInterface`). -/
theorem algorithm1_anyGCA (obj : Object State Op Response) (n : Nat) :
    ∀ e, algorithm1 obj n e → algorithm1AnyGCA obj n e := by
  rintro e ⟨f, g, hp, hfair, hw, rfl⟩
  exact ⟨f.environment obj, g.toGCA hfair hw, hp, rfl⟩

/-- **The admitted set is not empty**, at every process count `n = m + 1`. -/
theorem algorithm1_nonempty (obj : Object State Op Response) (op : Op) (m : Nat) :
    ∃ e, algorithm1 obj (m + 1) e :=
  ⟨_, GlobalSchedule.Witness.rfam m obj op, GlobalSchedule.Witness.rsched m obj op,
    GlobalSchedule.Witness.rsched_opLive m obj op,
    GlobalSchedule.Witness.rsched_fair m obj op,
    GlobalSchedule.Witness.rfam_waitFree m obj op, rfl⟩

/-- **Algorithm 1 over any GCA meeting the interface is obstruction-free**, in
the manuscript's §3 sense. -/
theorem algorithm1AnyGCA_obstructionFree (obj : Object State Op Response) (n : Nat) :
    ObstructionFree (algorithm1AnyGCA obj n) := by
  rintro e ⟨H, g, hp, rfl⟩ i hcorrect hsolo
  exact g.execution_obstructionFree hp i hcorrect hsolo

/-- The admitted set of Algorithm 1 over a GCA meeting the interface is not
empty either, at every process count `n = m + 1`. -/
theorem algorithm1AnyGCA_nonempty (obj : Object State Op Response) (op : Op) (m : Nat) :
    ∃ e, algorithm1AnyGCA obj (m + 1) e := by
  obtain ⟨e, he⟩ := algorithm1_nonempty obj op m
  exact ⟨e, algorithm1_anyGCA obj (m + 1) e he⟩

/-- **Algorithm 1 is obstruction-free**, in the manuscript's §3 sense. -/
theorem algorithm1_obstructionFree (obj : Object State Op Response) (n : Nat) :
    ObstructionFree (algorithm1 obj n) := fun e he =>
  algorithm1AnyGCA_obstructionFree obj n e (algorithm1_anyGCA obj n e he)

end ConflictFreedom
