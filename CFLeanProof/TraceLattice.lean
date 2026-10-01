import CFLeanProof.TraceErase

/-! Lattice existence derived from adjacent swaps, without lattice axioms. -/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- Compatible pairs have a least upper bound, constructed by removing enabled
heads. The minimality conclusion ranges over every common upper bound. -/
theorem pair_lub_exists_with_counts (u x y : obj.Trace)
    (hx : obj.TracePrefix x u) (hy : obj.TracePrefix y u) :
    ∃ z, obj.TracePrefix x z ∧ obj.TracePrefix y z ∧
      (∀ v, obj.TracePrefix x v → obj.TracePrefix y v → obj.TracePrefix z v) ∧
      ∀ a, obj.traceCount a z ≤ max (obj.traceCount a x) (obj.traceCount a y) := by
  have main : ∀ k, ∀ u x y : obj.Trace, obj.traceLength u = k →
      obj.TracePrefix x u → obj.TracePrefix y u →
      ∃ z, obj.TracePrefix x z ∧ obj.TracePrefix y z ∧
        (∀ v, obj.TracePrefix x v → obj.TracePrefix y v → obj.TracePrefix z v) ∧
      ∀ a, obj.traceCount a z ≤ max (obj.traceCount a x) (obj.traceCount a y) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro u x y hk hx hy
      induction x using Quotient.inductionOn with | h xs =>
        cases xs with
        | nil => exact ⟨y, obj.empty_tracePrefix y, obj.tracePrefix_refl y,
            (fun _ _ hv => hv), fun _ => Nat.le_max_right _ _⟩
        | cons a xs =>
          let x : obj.Trace := Quotient.mk obj.traceSetoid (a :: xs)
          have ha : obj.traceCanStart a x := Or.inl rfl
          have hu := obj.traceCanStart_mono hx ha
          have hlt : obj.traceLength (obj.traceErase a u) < k := by
            rw [← hk]
            exact obj.traceLength_erase_lt hu
          obtain ⟨z, hzx, hzy, hz, hcount⟩ := ih _ hlt
            (obj.traceErase a u) (obj.traceErase a x) (obj.traceErase a y) rfl
            (obj.traceErase_mono a hx) (obj.traceErase_mono a hy)
          refine ⟨obj.traceCons a z, ?_, ?_, ?_, ?_⟩
          · have h := obj.traceCons_mono a hzx
            rw [← obj.traceCanStart_move ha] at h
            exact h
          · exact obj.tracePrefix_trans (obj.tracePrefix_head_completion hy hu)
              (obj.traceCons_mono a hzy)
          · intro v hvx hvy
            have hav := obj.traceCanStart_mono hvx ha
            have h := obj.traceCons_mono a
              (hz (obj.traceErase a v) (obj.traceErase_mono a hvx) (obj.traceErase_mono a hvy))
            rw [← obj.traceCanStart_move hav] at h
            exact h
          · intro b
            have hc := hcount b
            rw [obj.traceCount_erase, obj.traceCount_erase] at hc
            rw [obj.traceCount_cons]
            by_cases hab : a = b
            · subst b
              have hp := obj.traceCount_pos_of_canStart ha
              simp only [ite_true] at hc ⊢
              have arithmetic : ∀ m n p : Nat, 0 < m → p ≤ max (m - 1) (n - 1) →
                  p + 1 ≤ max m n := by omega
              exact arithmetic _ _ _ hp hc
            · simp only [ite_eq_right hab, Nat.sub_zero, Nat.add_zero] at hc ⊢
              exact hc
  exact main (obj.traceLength u) u x y rfl hx hy

theorem pair_lub_exists (u x y : obj.Trace)
    (hx : obj.TracePrefix x u) (hy : obj.TracePrefix y u) :
    ∃ z, obj.TracePrefix x z ∧ obj.TracePrefix y z ∧
      ∀ v, obj.TracePrefix x v → obj.TracePrefix y v → obj.TracePrefix z v := by
  obtain ⟨z, hx, hy, hz, _⟩ := obj.pair_lub_exists_with_counts u x y hx hy
  exact ⟨z, hx, hy, hz⟩

omit [DecidableEq Op] in
/-- Any inhabited, length-bounded set of traces has a member of maximum length.
This finite-natural argument does not assume the trace alphabet is finite. -/
private theorem maximum_length (S : obj.Trace → Prop) (N : Nat)
    (bounded : ∀ s, S s → obj.traceLength s ≤ N) (inhabited : ∃ s, S s) :
    ∃ g, S g ∧ ∀ s, S s → obj.traceLength s ≤ obj.traceLength g := by
  classical
  induction N with
  | zero =>
    obtain ⟨g, hg⟩ := inhabited
    exact ⟨g, hg, fun s hs => Nat.le_trans (bounded s hs) (Nat.zero_le _)⟩
  | succ N ih =>
    by_cases he : ∃ g, S g ∧ obj.traceLength g = N + 1
    · obtain ⟨g, hg, hlen⟩ := he
      exact ⟨g, hg, fun s hs => hlen ▸ bounded s hs⟩
    · apply ih
      intro s hs
      have hb := bounded s hs
      have hn : obj.traceLength s ≠ N + 1 := fun hh => he ⟨s, hs, hh⟩
      omega

/-- Every nonempty family of finite traces has a GLB. The family and alphabet
may both be infinite. -/
theorem glb_exists (S : obj.Trace → Prop) (hne : ∃ s, S s) : ∃ g, obj.IsGLB S g := by
  obtain ⟨u, hu⟩ := hne
  let lower : obj.Trace → Prop := fun l => ∀ s, S s → obj.TracePrefix l s
  have bounded : ∀ l, lower l → obj.traceLength l ≤ obj.traceLength u :=
    fun l hl => obj.tracePrefix_length (hl u hu)
  have inhabited : ∃ l, lower l := ⟨obj.emptyTrace, fun s _ => obj.empty_tracePrefix s⟩
  obtain ⟨g, hg, hmax⟩ := maximum_length obj lower (obj.traceLength u) bounded inhabited
  refine ⟨g, hg, ?_⟩
  intro l hl
  obtain ⟨z, hgz, hlz, hz⟩ := obj.pair_lub_exists u g l (hg u hu) (hl u hu)
  have hzl : lower z := fun s hs => hz s (hg s hs) (hl s hs)
  have he : g = z := obj.tracePrefix_eq_of_length_eq hgz
    (Nat.le_antisymm (obj.tracePrefix_length hgz) (hmax z hzl))
  exact he ▸ hlz

/-- Every compatible family, including the empty family, has a LUB. It is the
GLB of its nonempty set of common upper bounds. -/
theorem lub_exists (S : obj.Trace → Prop) (hc : obj.Compatible S) : ∃ u, obj.IsLUB S u := by
  obtain ⟨bound, hb⟩ := hc
  let upper : obj.Trace → Prop := fun u => ∀ s, S s → obj.TracePrefix s u
  obtain ⟨u, hu, hgreat⟩ := obj.glb_exists upper ⟨bound, hb⟩
  exact ⟨u, (fun s hs => hgreat s (fun v hv => hv s hs)), hu⟩

/-- Every occurrence of a GLB occurs in every family member. -/
theorem glb_content {S : obj.Trace → Prop} {g : obj.Trace} (hg : obj.IsGLB S g)
    (a : Op) (k : Nat) (hk : k < obj.traceCount a g) :
    ∀ s, S s → k < obj.traceCount a s :=
  fun s hs => Nat.lt_of_lt_of_le hk (obj.traceCount_mono (hg.1 s hs) a)

/-- Every occurrence of a compatible family's LUB occurs in an input trace.
The proof constructs a maximum-length common lower bound of the upper bounds
that contains only input occurrences, then shows it is itself an upper bound. -/
theorem lub_content {S : obj.Trace → Prop} {u : obj.Trace} (hu : obj.IsLUB S u)
    (a : Op) (k : Nat) (hk : k < obj.traceCount a u) :
    ∃ s, S s ∧ k < obj.traceCount a s := by
  classical
  let safe : obj.Trace → Prop := fun t =>
    (∀ v, (∀ s, S s → obj.TracePrefix s v) → obj.TracePrefix t v) ∧
    (∀ b j, j < obj.traceCount b t → ∃ s, S s ∧ j < obj.traceCount b s)
  have emptySafe : safe obj.emptyTrace := by
    refine ⟨fun v _ => obj.empty_tracePrefix v, ?_⟩
    intro b j hj
    change j < 0 at hj
    omega
  have bounded : ∀ t, safe t → obj.traceLength t ≤ obj.traceLength u :=
    fun t ht => obj.tracePrefix_length (ht.1 u hu.1)
  obtain ⟨g, hg, hmax⟩ := maximum_length obj safe (obj.traceLength u) bounded
    ⟨obj.emptyTrace, emptySafe⟩
  have upper : ∀ s, S s → obj.TracePrefix s g := by
    intro s hs
    obtain ⟨z, hgz, hsz, hz, hcount⟩ :=
      obj.pair_lub_exists_with_counts u g s (hg.1 u hu.1) (hu.1 s hs)
    have hzsafe : safe z := by
      refine ⟨fun v hv => hz v (hg.1 v hv) (hv s hs), ?_⟩
      intro b j hj
      have hb := hcount b
      have hchoice : j < obj.traceCount b g ∨ j < obj.traceCount b s := by omega
      exact hchoice.elim (hg.2 b j) (fun h => ⟨s, hs, h⟩)
    have eq : g = z := obj.tracePrefix_eq_of_length_eq hgz
      (Nat.le_antisymm (obj.tracePrefix_length hgz) (hmax z hzsafe))
    exact eq ▸ hsz
  have eq : u = g := obj.tracePrefix_antisymm (hu.2 g upper) (hg.1 u hu.1)
  exact hg.2 a k (eq ▸ hk)

/-- The LUB contains precisely the union of occurrence sets. -/
theorem lub_occurs_iff {S : obj.Trace → Prop} {u : obj.Trace} (hu : obj.IsLUB S u)
    (a : Op) (k : Nat) :
    k < obj.traceCount a u ↔ ∃ s, S s ∧ k < obj.traceCount a s := by
  constructor
  · exact obj.lub_content hu a k
  · rintro ⟨s, hs, hk⟩
    exact Nat.lt_of_lt_of_le hk (obj.traceCount_mono (hu.1 s hs) a)

/-- Choice selects the already proved unique GLB; it is not an additional axiom
about traces. The nonempty-family proof is a required argument. -/
noncomputable def traceGLB (S : obj.Trace → Prop) (hne : ∃ s, S s) : obj.Trace :=
  Classical.choose (obj.glb_exists S hne)

theorem traceGLB_spec (S : obj.Trace → Prop) (hne : ∃ s, S s) :
    obj.IsGLB S (obj.traceGLB S hne) := Classical.choose_spec (obj.glb_exists S hne)

/-- The least upper bound of a compatible family (`lub_exists`). -/
noncomputable def traceLUB (S : obj.Trace → Prop) (hc : obj.Compatible S) : obj.Trace :=
  Classical.choose (obj.lub_exists S hc)

theorem traceLUB_spec (S : obj.Trace → Prop) (hc : obj.Compatible S) :
    obj.IsLUB S (obj.traceLUB S hc) := Classical.choose_spec (obj.lub_exists S hc)

end ConflictFreedom.Object
