import CFLeanProof.TraceOrder

/-! A finite prefix chain has a greatest member. This packages the finite
maximal-commit argument used when linearizing a finite operation history. -/
namespace ConflictFreedom.Object

variable {State Op Response : Type} (obj : ConflictFreedom.Object State Op Response)

/-- Every pair of traces listed in `S` is prefix-comparable. -/
def PrefixChain (S : List obj.Trace) : Prop :=
  ∀ s ∈ S, ∀ t ∈ S, obj.TracePrefix s t ∨ obj.TracePrefix t s

/-- A nonempty finite prefix chain has a member above all its members. -/
theorem finiteChain_greatest_of_nonempty (S : List obj.Trace) (hne : S ≠ [])
    (hc : obj.PrefixChain S) :
    ∃ m ∈ S, ∀ s ∈ S, obj.TracePrefix s m := by
  induction S with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    by_cases hnil : xs = []
    · subst xs
      refine ⟨x, by simp, ?_⟩
      intro s hs
      have he : s = x := by simpa using hs
      subst s
      exact obj.tracePrefix_refl x
    · have htail : obj.PrefixChain xs := by
        intro s hs t ht
        exact hc s (List.mem_cons_of_mem x hs) t (List.mem_cons_of_mem x ht)
      obtain ⟨m, hm, hmax⟩ := ih hnil htail
      rcases hc x (by simp) m (List.mem_cons_of_mem x hm) with hxm | hmx
      · refine ⟨m, List.mem_cons_of_mem x hm, ?_⟩
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact hxm
        · exact hmax s hs
      · refine ⟨x, by simp, ?_⟩
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact obj.tracePrefix_refl s
        · exact obj.tracePrefix_trans (hmax s hs) hmx

/-- The empty chain is represented by the empty trace; otherwise the maximum
is one of the listed traces. -/
theorem finiteChain_greatest (S : List obj.Trace) (hc : obj.PrefixChain S) :
    ∃ m, (S = [] ∧ m = obj.emptyTrace ∨ m ∈ S) ∧
      ∀ s ∈ S, obj.TracePrefix s m := by
  by_cases hnil : S = []
  · subst S
    refine ⟨obj.emptyTrace, Or.inl ⟨rfl, rfl⟩, ?_⟩
    intro s hs
    cases hs
  · obtain ⟨m, hm, hmax⟩ := obj.finiteChain_greatest_of_nonempty S hnil hc
    exact ⟨m, Or.inr hm, hmax⟩

/-- Responses to occurrences present in an earlier chain member agree with
those obtained from the greatest member. -/
theorem finiteChain_response_stable [DecidableEq Op]
    {S : List obj.Trace} {m : obj.Trace}
    (hmax : ∀ s ∈ S, obj.TracePrefix s m)
    {s : obj.Trace} (hs : s ∈ S) (a : Op) (k : Nat)
    (hk : k < (obj.traceResponses a obj.initial s).length) :
    obj.traceReturn a k s = obj.traceReturn a k m :=
  obj.traceReturn_prefix (hmax s hs) a k hk

/-- The selected greatest trace preserves every defined occurrence response in
the finite chain. -/
theorem finiteChain_greatest_with_responses [DecidableEq Op]
    (S : List obj.Trace) (hc : obj.PrefixChain S) :
    ∃ m, (S = [] ∧ m = obj.emptyTrace ∨ m ∈ S) ∧
      (∀ s ∈ S, obj.TracePrefix s m) ∧
      ∀ s ∈ S, ∀ (a : Op) (k : Nat),
        k < (obj.traceResponses a obj.initial s).length →
        obj.traceReturn a k s = obj.traceReturn a k m := by
  obtain ⟨m, hmem, hmax⟩ := obj.finiteChain_greatest S hc
  refine ⟨m, hmem, hmax, ?_⟩
  intro s hs a k hk
  exact obj.finiteChain_response_stable hmax hs a k hk

end ConflictFreedom.Object
