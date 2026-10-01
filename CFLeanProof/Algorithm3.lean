import CFLeanProof.HelpingImplementation
import CFLeanProof.HelpingWitness

/-! # Algorithm 3 as a §3 implementation

The helping construction's counterpart of `Algorithm1.lean`.  The admitted
executions are those extracted from a fair, operation-live global schedule of
`HelpingUniversal.Step` over a wait-free snapshot interface, and
`algorithm3_nonempty` shows the set is not empty — at every process count
`n = m + 1` — with `WitnessH.hsched`.

`ObstructionFree` is proved here.  The stronger `ConflictFree` — both halves of
Lemma `lemma:UCV2isCF` in §3 vocabulary — is proved in
`Algorithm3ConflictFree.lean`, following the manuscript's two-invariant
argument; `algorithm3_obstructionFree` is a consequence of it via
`conflictFree_obstructionFree`, and is kept as a separate entry point.
-/
namespace ConflictFreedom
variable {State Op Response : Type} [DecidableEq Op]

/-- **Algorithm 3 over any GCA objects meeting the interface, as an
`Implementation`** — the manuscript's Algorithm 3 with its GCA objects used as a
black box (`GlobalSchedule.HelpingRun.GCAInterface`). -/
def algorithm3AnyGCA (obj : Object State Op Response) (n : Nat) : Implementation n Op :=
  fun e => ∃ (H : WeakUniversal.Environment (n := n) obj) (g : GlobalSchedule.HelpingGCA obj H)
    (hp : g.OpLive), e = g.execution hp

/-- **Algorithm 3 over Algorithm 2, as an `Implementation`.** -/
def algorithm3 (obj : Object State Op Response) (n : Nat) : Implementation n Op :=
  fun e => ∃ (f : UniversalProtocol.Family (n := n) obj) (g : GlobalSchedule.Helping obj f)
    (hp : g.OpLive), g.Fair ∧ f.SnapshotWaitFree obj ∧ e = g.execution hp

/-- **Algorithm 2 is a GCA meeting the interface**, for Algorithm 3
(`GlobalSchedule.Helping.gcaInterface`). -/
theorem algorithm3_anyGCA (obj : Object State Op Response) (n : Nat) :
    ∀ e, algorithm3 obj n e → algorithm3AnyGCA obj n e := by
  rintro e ⟨f, g, hp, hfair, hw, rfl⟩
  exact ⟨f.environment obj, g.toGCA hfair hw, hp, rfl⟩

/-- **The admitted set is not empty**, at every process count `n = m + 1`. -/
theorem algorithm3_nonempty (obj : Object State Op Response) (op : Op) (m : Nat) :
    ∃ e, algorithm3 obj (m + 1) e :=
  ⟨_, GlobalSchedule.WitnessH.hfam m obj op, GlobalSchedule.WitnessH.hsched m obj op,
    GlobalSchedule.WitnessH.hsched_opLive m obj op,
    GlobalSchedule.WitnessH.hsched_fair m obj op,
    GlobalSchedule.WitnessH.hfam_waitFree m obj op, rfl⟩

/-- **Algorithm 3 over any GCA meeting the interface is obstruction-free.** -/
theorem algorithm3AnyGCA_obstructionFree (obj : Object State Op Response) (n : Nat) :
    ObstructionFree (algorithm3AnyGCA obj n) := by
  rintro e ⟨H, g, hp, rfl⟩ i hcorrect hsolo
  exact g.execution_obstructionFree hp i hcorrect hsolo

/-- The admitted set of Algorithm 3 over a GCA meeting the interface is not
empty either, at every process count `n = m + 1`. -/
theorem algorithm3AnyGCA_nonempty (obj : Object State Op Response) (op : Op) (m : Nat) :
    ∃ e, algorithm3AnyGCA obj (m + 1) e := by
  obtain ⟨e, he⟩ := algorithm3_nonempty obj op m
  exact ⟨e, algorithm3_anyGCA obj (m + 1) e he⟩

/-- **Algorithm 3 is obstruction-free**, in the manuscript's §3 sense. -/
theorem algorithm3_obstructionFree (obj : Object State Op Response) (n : Nat) :
    ObstructionFree (algorithm3 obj n) := fun e he =>
  algorithm3AnyGCA_obstructionFree obj n e (algorithm3_anyGCA obj n e he)

end ConflictFreedom
