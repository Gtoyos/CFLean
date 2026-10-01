import CFLeanProof.TraceLattice

/-! Compatibility.  `comp {s, t}` (`PairCompatible`) says that some trace
extends both; a finite family is compatible as soon as it is pairwise
compatible (`finite_pairwise_compatible`).  `compatiblePart` is GCA line 3,
`a^co = ⊓({a} ∪ {b : ¬comp {a, b}})`, specified as a greatest lower bound. -/

namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- `comp {s, t}`: some trace extends both `s` and `t`. -/
def PairCompatible (s t : obj.Trace) : Prop :=
  ∃ u, obj.TracePrefix s u ∧ obj.TracePrefix t u

omit [DecidableEq Op] in
theorem pairCompatible_symm {s t : obj.Trace} (h : obj.PairCompatible s t) :
    obj.PairCompatible t s := by
  obtain ⟨u, hs, ht⟩ := h
  exact ⟨u, ht, hs⟩

omit [DecidableEq Op] in
theorem pairCompatible_prefix {s t u v : obj.Trace}
    (h : obj.PairCompatible u v) (hs : obj.TracePrefix s u) (ht : obj.TracePrefix t v) :
    obj.PairCompatible s t := by
  obtain ⟨w, hu, hv⟩ := h
  exact ⟨w, obj.tracePrefix_trans hs hu, obj.tracePrefix_trans ht hv⟩

/-- The total length of a list of traces. -/
def traceWeight (S : List obj.Trace) : Nat := (S.map obj.traceLength).sum

theorem traceLength_erase_le (a : Op) (s : obj.Trace) :
    obj.traceLength (obj.traceErase a s) ≤ obj.traceLength s := by
  induction s using Quotient.inductionOn with | h s =>
    exact List.length_erase_le

private theorem weight_erase_le (a : Op) (S : List obj.Trace) :
    obj.traceWeight (S.map (obj.traceErase a)) ≤ obj.traceWeight S := by
  induction S with
  | nil => exact Nat.le_refl _
  | cons s S ih =>
    have hs := obj.traceLength_erase_le a s
    simp only [traceWeight, List.map_cons, List.sum_cons] at ih ⊢
    omega

private theorem weight_erase_lt (a : Op) (S : List obj.Trace)
    (ha : ∃ s ∈ S, obj.traceCanStart a s) :
    obj.traceWeight (S.map (obj.traceErase a)) < obj.traceWeight S := by
  induction S with
  | nil => simp at ha
  | cons s S ih =>
    obtain ⟨t, ht, ha⟩ := ha
    rcases List.mem_cons.mp ht with rfl | ht
    · have hs := obj.traceLength_erase_lt ha
      have hS := weight_erase_le obj a S
      simp only [traceWeight, List.map_cons, List.sum_cons] at hS ⊢
      omega
    · have hs := obj.traceLength_erase_le a s
      have hS := ih ⟨t, ht, ha⟩
      simp only [traceWeight, List.map_cons, List.sum_cons] at hS ⊢
      omega

/-- Finite pairwise-compatible families admit a simultaneous common extension. -/
theorem finite_pairwise_compatible (S : List obj.Trace)
    (hp : ∀ s ∈ S, ∀ t ∈ S, obj.PairCompatible s t) :
    obj.Compatible (fun s => s ∈ S) := by
  classical
  have main : ∀ n, ∀ S : List obj.Trace, obj.traceWeight S = n →
      (∀ s ∈ S, ∀ t ∈ S, obj.PairCompatible s t) → obj.Compatible (fun s => s ∈ S) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro S hn hp
      by_cases he : ∀ s ∈ S, s = obj.emptyTrace
      · exact ⟨obj.emptyTrace, fun s hs => (he s hs) ▸ obj.tracePrefix_refl obj.emptyTrace⟩
      · obtain ⟨s, hs, hne⟩ := show ∃ s, s ∈ S ∧ s ≠ obj.emptyTrace from by
          simpa using he
        obtain ⟨a, ha⟩ : ∃ a, obj.traceCanStart a s := by
          induction s using Quotient.inductionOn with | h xs =>
            cases xs with
            | nil => exact False.elim (hne rfl)
            | cons a xs => exact ⟨a, Or.inl rfl⟩
        have hlt : obj.traceWeight (S.map (obj.traceErase a)) < n := by
          rw [← hn]
          exact weight_erase_lt obj a S ⟨s, hs, ha⟩
        have herase : ∀ x ∈ S.map (obj.traceErase a),
            ∀ y ∈ S.map (obj.traceErase a), obj.PairCompatible x y := by
          intro x hx y hy
          obtain ⟨x, hxS, rfl⟩ := List.mem_map.mp hx
          obtain ⟨y, hyS, rfl⟩ := List.mem_map.mp hy
          obtain ⟨u, hu, hv⟩ := hp x hxS y hyS
          exact ⟨obj.traceErase a u, obj.traceErase_mono a hu, obj.traceErase_mono a hv⟩
        obtain ⟨u, hu⟩ := ih _ hlt _ rfl herase
        refine ⟨obj.traceCons a u, ?_⟩
        intro t ht
        obtain ⟨v, hsv, htv⟩ := hp s hs t ht
        have hav := obj.traceCanStart_mono hsv ha
        exact obj.tracePrefix_trans (obj.tracePrefix_head_completion htv hav)
          (obj.traceCons_mono a (hu _ (List.mem_map.mpr ⟨t, ht, rfl⟩)))
  exact main _ S rfl hp

/-- The family whose GLB replaces a particular input at GCA line 3. -/
def ConflictNeighborhood (S : obj.Trace → Prop) (s : obj.Trace) : obj.Trace → Prop :=
  fun t => t = s ∨ (S t ∧ ¬ obj.PairCompatible s t)

/-- GCA line 3: `s^co = ⊓ ({s} ∪ {t ∈ S : ¬ comp {s, t}})`. -/
noncomputable def compatiblePart (S : obj.Trace → Prop) (s : obj.Trace) : obj.Trace :=
  obj.traceGLB (obj.ConflictNeighborhood S s) ⟨s, Or.inl rfl⟩

theorem compatiblePart_spec (S : obj.Trace → Prop) (s : obj.Trace) :
    obj.IsGLB (obj.ConflictNeighborhood S s) (obj.compatiblePart S s) := obj.traceGLB_spec _ _

theorem compatiblePart_prefix (S : obj.Trace → Prop) (s : obj.Trace) :
    obj.TracePrefix (obj.compatiblePart S s) s := (obj.compatiblePart_spec S s).1 s (Or.inl rfl)

/-- The compatibility transformation makes every pair compatible. -/
theorem compatiblePart_pair {S : obj.Trace → Prop} {s t : obj.Trace} (hs : S s) (_ht : S t) :
    obj.PairCompatible (obj.compatiblePart S s) (obj.compatiblePart S t) := by
  classical
  by_cases hc : obj.PairCompatible s t
  · exact obj.pairCompatible_prefix hc (obj.compatiblePart_prefix S s) (obj.compatiblePart_prefix S t)
  · exact ⟨s, obj.compatiblePart_prefix S s,
      (obj.compatiblePart_spec S t).1 s (Or.inr ⟨hs, fun h => hc (obj.pairCompatible_symm h)⟩)⟩

/-- The concrete finite compatibility transformation in GCA line 3 always
produces a family with a well-defined LUB. -/
theorem compatiblePart_family (S : List obj.Trace) :
    obj.Compatible (fun t => t ∈ S.map (obj.compatiblePart (fun s => s ∈ S))) := by
  apply obj.finite_pairwise_compatible
  intro s hs t ht
  obtain ⟨s, hsS, rfl⟩ := List.mem_map.mp hs
  obtain ⟨t, htS, rfl⟩ := List.mem_map.mp ht
  exact obj.compatiblePart_pair hsS htS

end ConflictFreedom.Object
