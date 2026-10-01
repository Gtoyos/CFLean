import CFLeanProof.TraceCompatibility

/-! Concrete candidate computation (GCA lines 3–4), with finite snapshot views.
Absent slots are omitted from the list; occurrence order in the list is irrelevant. -/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- GCA lines 3–4: the candidate `⊔ A^co` computed from a view `S` of `A`. -/
noncomputable def gcaCandidate (S : List obj.Trace) : obj.Trace :=
  obj.traceLUB (fun t => t ∈ S.map (obj.compatiblePart (fun s => s ∈ S)))
    (obj.compatiblePart_family S)

theorem gcaCandidate_spec (S : List obj.Trace) :
    obj.IsLUB (fun t => t ∈ S.map (obj.compatiblePart (fun s => s ∈ S))) (obj.gcaCandidate S) :=
  obj.traceLUB_spec _ _

/-- Every occurrence in a candidate belongs to one of its snapshot inputs. -/
theorem gcaCandidate_validity (S : List obj.Trace) (a : Op) (k : Nat)
    (hk : k < obj.traceCount a (obj.gcaCandidate S)) :
    ∃ s ∈ S, k < obj.traceCount a s := by
  obtain ⟨t, ht, hk⟩ := obj.lub_content (obj.gcaCandidate_spec S) a k hk
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact ⟨s, hs, Nat.lt_of_lt_of_le hk (obj.traceCount_mono (obj.compatiblePart_prefix _ s) a)⟩

/-- A common prefix of a nonempty snapshot is preserved by its candidate. -/
theorem gcaCandidate_commonPrefix (S : List obj.Trace) (hne : ∃ s, s ∈ S)
    (l : obj.Trace) (hl : ∀ s ∈ S, obj.TracePrefix l s) :
    obj.TracePrefix l (obj.gcaCandidate S) := by
  obtain ⟨s, hs⟩ := hne
  have hp : obj.TracePrefix l (obj.compatiblePart (fun t => t ∈ S) s) := by
    apply (obj.compatiblePart_spec _ s).2
    intro t ht
    rcases ht with rfl | ⟨ht, _⟩
    · exact hl _ hs
    · exact hl t ht
  exact obj.tracePrefix_trans hp
    ((obj.gcaCandidate_spec S).1 _ (List.mem_map.mpr ⟨s, hs, rfl⟩))

theorem compatiblePart_eq_self {S : obj.Trace → Prop} (hc : obj.Compatible S)
    {s : obj.Trace} (hs : S s) : obj.compatiblePart S s = s := by
  apply obj.tracePrefix_antisymm (obj.compatiblePart_prefix S s)
  apply (obj.compatiblePart_spec S s).2
  intro t ht
  rcases ht with rfl | ⟨ht, hn⟩
  · exact obj.tracePrefix_refl _
  · obtain ⟨u, hu⟩ := hc
    exact False.elim (hn ⟨u, hu s hs, hu t ht⟩)

/-- For compatible inputs, no truncation occurs and the candidate is their LUB. -/
theorem gcaCandidate_of_compatible (S : List obj.Trace)
    (hc : obj.Compatible (fun s => s ∈ S)) :
    obj.IsLUB (fun s => s ∈ S) (obj.gcaCandidate S) := by
  have hm : S.map (obj.compatiblePart (fun s => s ∈ S)) = S := by
    exact (List.map_congr_left (fun s hs => obj.compatiblePart_eq_self hc hs)).trans (List.map_id S)
  simpa only [hm] using obj.gcaCandidate_spec S

/-- The line-4 compatibility flag is equivalent to actual compatibility. -/
theorem compatiblePart_fixed_iff (S : List obj.Trace) :
    S.map (obj.compatiblePart (fun s => s ∈ S)) = S ↔ obj.Compatible (fun s => s ∈ S) := by
  constructor
  · intro he
    simpa only [he] using obj.compatiblePart_family S
  · intro hc
    exact (List.map_congr_left (fun s hs => obj.compatiblePart_eq_self hc hs)).trans (List.map_id S)

/-- Truncated elements from nested snapshots are compatible across the views. -/
theorem compatiblePart_nested {S T : List obj.Trace}
    (hst : ∀ s ∈ S, s ∈ T) {s t : obj.Trace} (hs : s ∈ S) (_ht : t ∈ T) :
    obj.PairCompatible (obj.compatiblePart (fun s => s ∈ S) s)
      (obj.compatiblePart (fun t => t ∈ T) t) := by
  classical
  by_cases hc : obj.PairCompatible s t
  · exact obj.pairCompatible_prefix hc (obj.compatiblePart_prefix _ s) (obj.compatiblePart_prefix _ t)
  · exact ⟨s, obj.compatiblePart_prefix _ s,
      (obj.compatiblePart_spec _ t).1 s
        (Or.inr ⟨hst s hs, fun h => hc (obj.pairCompatible_symm h)⟩)⟩

/-- Candidates from nested snapshots have a simultaneous common extension. -/
theorem gcaCandidate_nested {S T : List obj.Trace} (hst : ∀ s ∈ S, s ∈ T) :
    obj.PairCompatible (obj.gcaCandidate S) (obj.gcaCandidate T) := by
  let CS := S.map (obj.compatiblePart (fun s => s ∈ S))
  let CT := T.map (obj.compatiblePart (fun t => t ∈ T))
  have cross : ∀ s ∈ CS, ∀ t ∈ CT, obj.PairCompatible s t := by
    intro s hs t ht
    obtain ⟨s, hsS, rfl⟩ := List.mem_map.mp hs
    obtain ⟨t, htT, rfl⟩ := List.mem_map.mp ht
    exact obj.compatiblePart_nested hst hsS htT
  have within : ∀ U : List obj.Trace, ∀ s ∈ U.map (obj.compatiblePart (fun t => t ∈ U)),
      ∀ t ∈ U.map (obj.compatiblePart (fun t => t ∈ U)), obj.PairCompatible s t := by
    intro U s hs t ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    exact obj.compatiblePart_pair hv hw
  obtain ⟨u, hu⟩ := obj.finite_pairwise_compatible (CS ++ CT) (by
    intro s hs t ht
    rcases List.mem_append.mp hs with hs | hs <;> rcases List.mem_append.mp ht with ht | ht
    · exact within S s hs t ht
    · exact cross s hs t ht
    · exact obj.pairCompatible_symm (cross t ht s hs)
    · exact within T s hs t ht)
  exact ⟨u, (obj.gcaCandidate_spec S).2 u (fun s hs => hu s (List.mem_append_left _ hs)),
    (obj.gcaCandidate_spec T).2 u (fun t ht => hu t (List.mem_append_right _ ht))⟩

/-- Compatible nested views produce monotonically increasing candidates. -/
theorem gcaCandidate_mono_of_compatible {S T : List obj.Trace}
    (hst : ∀ s ∈ S, s ∈ T) (hc : obj.Compatible (fun t => t ∈ T)) :
    obj.TracePrefix (obj.gcaCandidate S) (obj.gcaCandidate T) := by
  have hs : obj.Compatible (fun s => s ∈ S) := by
    obtain ⟨u, hu⟩ := hc
    exact ⟨u, fun s hs => hu s (hst s hs)⟩
  exact (obj.gcaCandidate_of_compatible S hs).2 _
    (fun s hs => (obj.gcaCandidate_of_compatible T hc).1 s (hst s hs))

end ConflictFreedom.Object
