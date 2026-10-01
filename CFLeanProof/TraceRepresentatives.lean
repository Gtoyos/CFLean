import CFLeanProof.TraceOrder

/-! Trace prefixes can be realized by literal schedule prefixes while keeping
an already chosen representative. This is the representative-extension step
used to order committed rounds in a finite linearization. -/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : ConflictFreedom.Object State Op Response)

/-- Any chosen schedule for a prefix trace extends to a schedule for the
larger trace. -/
theorem tracePrefix_extend_representative {s t : obj.Trace}
    (hst : obj.TracePrefix s t) {x : List Op}
    (hx : Quotient.mk obj.traceSetoid x = s) :
    ∃ y : List Op, Quotient.mk obj.traceSetoid (x ++ y) = t := by
  obtain ⟨u, hu⟩ := (obj.tracePrefix_iff_append s t).mp hst
  induction u using Quotient.inductionOn with
  | h y =>
    refine ⟨y, ?_⟩
    rw [hu, ← hx]
    rfl

end ConflictFreedom.Object
