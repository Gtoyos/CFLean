import CFLeanProof.TraceAlgebra

/-! Invocation identities from the universal constructions: payload, process,
and monotonically increasing local sequence number. -/
namespace ConflictFreedom

/-- A command `(op, i, seq)`: an operation tagged with its invoking process and
that process's sequence number, which makes every invocation unique. -/
structure Command (P Op : Type) where
  operation : Op
  process : P
  sequence : Nat
  deriving DecidableEq

namespace Object
variable {State Op Response P : Type} (obj : Object State Op Response)

/-- Tags distinguish invocations; they do not alter the sequential object. -/
def commandObject (P : Type) : Object State (Command P Op) Response where
  initial := obj.initial
  step := fun cmd => obj.step cmd.operation

theorem command_independent_iff (a b : Command P Op) :
    (obj.commandObject P).Independent a b ↔ obj.Independent a.operation b.operation := Iff.rfl

theorem command_conflict_iff (a b : Command P Op) :
    (obj.commandObject P).Conflict a b ↔ obj.Conflict a.operation b.operation := Iff.rfl

variable [DecidableEq Op]

/-- Lines 7–8: append a command only if its trace has no occurrence yet. -/
def appendMissing (s : obj.Trace) (a : Op) : obj.Trace :=
  if obj.traceCount a s = 0 then obj.traceAppend s (Quotient.mk obj.traceSetoid [a]) else s

theorem appendMissing_extends (s : obj.Trace) (a : Op) :
    obj.TracePrefix s (obj.appendMissing s a) := by
  unfold appendMissing
  split
  · exact (obj.tracePrefix_iff_append _ _).mpr ⟨_, rfl⟩
  · exact obj.tracePrefix_refl _

theorem appendMissing_contains (s : obj.Trace) (a : Op) :
    0 < obj.traceCount a (obj.appendMissing s a) := by
  unfold appendMissing
  split
  · rename_i h
    rw [obj.traceCount_append a s (Quotient.mk obj.traceSetoid [a]), h]
    change 0 < 0 + ([a].count a)
    simp
  · rename_i h
    omega

theorem appendMissing_count (s : obj.Trace) (a : Op) :
    obj.traceCount a (obj.appendMissing s a) = max 1 (obj.traceCount a s) := by
  unfold appendMissing
  split
  · rename_i h
    rw [obj.traceCount_append a s (Quotient.mk obj.traceSetoid [a]), h]
    change 0 + ([a].count a) = max 1 0
    simp
  · rename_i h
    omega

/-- An occurrence known to be present has a defined response. -/
theorem traceReturn_defined (s : obj.Trace) (a : Op) (k : Nat)
    (hk : k < obj.traceCount a s) : ∃ v, obj.traceReturn a k s = some v := by
  have hlen : k < (obj.traceResponses a obj.initial s).length := by
    simpa only [obj.traceResponses_length] using hk
  exact ⟨_, List.getElem?_eq_some_iff.mpr ⟨hlen, rfl⟩⟩

end Object
end ConflictFreedom
