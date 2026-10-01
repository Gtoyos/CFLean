import CFLeanProof.GCACandidate

/-! GCA line 6, and its validity, common-prefix and convergence invariants.
These statements isolate data-flow invariants from the temporal proof of the
commit decision, which is not assumed here. -/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The flagged candidates of GCA line 6: those computed from compatible views. -/
noncomputable def gcaFlagged (B : List (List obj.Trace)) : List obj.Trace := by
  classical
  exact (B.filter (fun S => decide (obj.Compatible (fun s => s ∈ S)))).map obj.gcaCandidate

/-- GCA line 6: the meet of the flagged candidates, or the caller's own
candidate when none is flagged. -/
noncomputable def gcaOutput (own : List obj.Trace) (B : List (List obj.Trace)) : obj.Trace := by
  classical
  exact if h : ∃ s, s ∈ obj.gcaFlagged B then
    obj.traceGLB (fun s => s ∈ obj.gcaFlagged B) h
  else obj.gcaCandidate own

theorem gcaFlagged_mem_iff (B : List (List obj.Trace)) (t : obj.Trace) :
    t ∈ obj.gcaFlagged B ↔
      ∃ S ∈ B, obj.Compatible (fun s => s ∈ S) ∧ obj.gcaCandidate S = t := by
  classical
  simp only [gcaFlagged, List.mem_map, List.mem_filter, decide_eq_true_eq]
  grind

/-- The line-6 output is a prefix of some candidate it uses. -/
theorem gcaOutput_below_candidate (own : List obj.Trace) (B : List (List obj.Trace)) :
    ∃ S, (S = own ∨ S ∈ B) ∧ obj.TracePrefix (obj.gcaOutput own B) (obj.gcaCandidate S) := by
  classical
  unfold gcaOutput
  split
  · rename_i h
    rcases hcopy : h with ⟨t, ht⟩
    obtain ⟨S, hS, _, he⟩ := (obj.gcaFlagged_mem_iff B t).mp ht
    exact ⟨S, Or.inr hS, he ▸ (obj.traceGLB_spec _ h).1 t ht⟩
  · exact ⟨own, Or.inl rfl, obj.tracePrefix_refl _⟩

/-- Validity of the output computation, with provenance in one observed input. -/
theorem gcaOutput_validity (own : List obj.Trace) (B : List (List obj.Trace))
    (a : Op) (k : Nat) (hk : k < obj.traceCount a (obj.gcaOutput own B)) :
    ∃ S, (S = own ∨ S ∈ B) ∧ ∃ s ∈ S, k < obj.traceCount a s := by
  obtain ⟨S, hS, hp⟩ := obj.gcaOutput_below_candidate own B
  exact ⟨S, hS, obj.gcaCandidate_validity S a k
    (Nat.lt_of_lt_of_le hk (obj.traceCount_mono hp a))⟩

/-- Common prefixes survive line 6 whenever each contributing A view is nonempty. -/
theorem gcaOutput_commonPrefix (own : List obj.Trace) (B : List (List obj.Trace))
    (l : obj.Trace)
    (hne : ∀ S, S = own ∨ S ∈ B → ∃ s, s ∈ S)
    (hl : ∀ S, S = own ∨ S ∈ B → ∀ s ∈ S, obj.TracePrefix l s) :
    obj.TracePrefix l (obj.gcaOutput own B) := by
  classical
  unfold gcaOutput
  split
  · rename_i h
    apply (obj.traceGLB_spec _ h).2
    intro t ht
    obtain ⟨S, hS, _, rfl⟩ := (obj.gcaFlagged_mem_iff B t).mp ht
    exact obj.gcaCandidate_commonPrefix S (hne S (Or.inr hS)) l (hl S (Or.inr hS))
  · exact obj.gcaCandidate_commonPrefix own (hne own (Or.inl rfl)) l (hl own (Or.inl rfl))

/-- Snapshot containment yields compatibility of all phase-one candidates. -/
theorem gcaCandidates_compatible (views : List (List obj.Trace))
    (chain : ∀ S ∈ views, ∀ T ∈ views,
      (∀ s ∈ S, s ∈ T) ∨ (∀ t ∈ T, t ∈ S)) :
    obj.Compatible (fun t => t ∈ views.map obj.gcaCandidate) := by
  apply obj.finite_pairwise_compatible
  intro s hs t ht
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hs
  obtain ⟨T, hT, rfl⟩ := List.mem_map.mp ht
  rcases chain S hS T hT with h | h
  · exact obj.gcaCandidate_nested h
  · exact obj.pairCompatible_symm (obj.gcaCandidate_nested h)

/-- Convergence for any outputs whose candidates come from a finite containment
chain of A snapshots, independently of B snapshot order and commit flags. -/
theorem gcaOutputs_convergence (views : List (List obj.Trace))
    (chain : ∀ S ∈ views, ∀ T ∈ views,
      (∀ s ∈ S, s ∈ T) ∨ (∀ t ∈ T, t ∈ S)) :
    obj.Compatible (fun t => ∃ own B, own ∈ views ∧
      (∀ S ∈ B, S ∈ views) ∧ t = obj.gcaOutput own B) := by
  obtain ⟨u, hu⟩ := obj.gcaCandidates_compatible views chain
  refine ⟨u, ?_⟩
  rintro t ⟨own, B, hown, hB, rfl⟩
  obtain ⟨S, hS, hp⟩ := obj.gcaOutput_below_candidate own B
  have hSv : S ∈ views := hS.elim (fun h => h ▸ hown) (hB S)
  exact obj.tracePrefix_trans hp (hu _ (List.mem_map.mpr ⟨S, hSv, rfl⟩))

end ConflictFreedom.Object
