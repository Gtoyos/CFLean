import CFLeanProof.TracePresentation

/-! The paper's occurrence-precedence presentation of finite traces. -/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- After prepending an `a`, every later occurrence of `a` moves up one index. -/
private def shiftLabel (a : Op) (p : Op × Nat) : Op × Nat :=
  (p.1, if p.1 = a then p.2 + 1 else p.2)

private theorem shiftLabel_injective (a : Op) : Function.Injective (shiftLabel a) := by
  intro ⟨b, i⟩ ⟨c, j⟩ h
  have hb : b = c := congrArg Prod.fst h
  subst c
  by_cases he : b = a
  · simp [shiftLabel, he] at h
    congr 1
  · simpa [shiftLabel, he] using h

/-- The `i`-th occurrence of `a` is labeled `(a,i)`, using zero-based indices. -/
def occurrenceLabels : List Op → List (Op × Nat)
  | [] => []
  | a :: s => (a, 0) :: (occurrenceLabels s).map (shiftLabel a)

theorem occurrenceLabels_mem (s : List Op) (a : Op) (i : Nat) :
    (a, i) ∈ occurrenceLabels s ↔ i < s.count a := by
  induction s generalizing i with
  | nil => simp [occurrenceLabels]
  | cons c s ih =>
    by_cases h : a = c
    · subst c
      simp only [occurrenceLabels, List.mem_cons, Prod.mk.injEq, true_and,
        List.mem_map, List.count_cons_self]
      constructor
      · intro hh
        rcases hh with hi | ⟨⟨b, k⟩, hk, hb⟩
        · omega
        · by_cases he : b = a
          · subst b
            simp [shiftLabel] at hb
            have hk' := (ih k).1 hk
            omega
          · simp [shiftLabel, he] at hb
      · intro hi
        by_cases hz : i = 0
        · exact Or.inl (by simp [hz])
        · right
          refine ⟨(a, i - 1), (ih (i - 1)).2 (by omega), ?_⟩
          simp [shiftLabel, Nat.sub_add_cancel (by omega : 1 ≤ i)]
    · simp only [occurrenceLabels, List.mem_cons, List.mem_map]
      constructor
      · intro hh
        rcases hh with hh | ⟨⟨b, k⟩, hk, hb⟩
        · have : a = c := by simpa using congrArg Prod.fst hh
          contradiction
        · simp only [shiftLabel] at hb
          by_cases he : b = c
          · simp [he] at hb
            exact False.elim (h hb.1.symm)
          · simp [he] at hb
            rcases hb with ⟨rfl, rfl⟩
            simpa [List.count_cons, h, Ne.symm h] using (ih k).1 hk
      · intro hi
        right
        refine ⟨(a, i), (ih i).2 (by simpa [List.count_cons, h, Ne.symm h] using hi), ?_⟩
        simp [shiftLabel, h]

/-- The order of labeled occurrences in the two-letter projection. The labels
are the same as in the original schedule, since removing other letters does not
change the occurrence number of either retained letter. -/
def OccurrencePrecedes (s : List Op) (a : Op) (i : Nat) (b : Op) (j : Nat) : Prop :=
  let labels := occurrenceLabels (dependencyProjection a b s)
  labels.idxOf (a, i) < labels.idxOf (b, j)

/-- Conditions (i) and (ii) of the paper's schedule equivalence, with zero-based
occurrence indices and the paper's one-way order implication.  The order `≺ₛ` is
read in the two-letter projection; `ScheduleEquiv` reads it in `s` itself, and
`occurrenceEq_iff_scheduleEquiv` shows the two readings agree. -/
def OccurrenceEq (s t : List Op) : Prop :=
  (∀ a, s.count a = t.count a) ∧
  ∀ a b i j, obj.Conflict a b → i < s.count a → j < s.count b →
    OccurrencePrecedes s a i b j → OccurrencePrecedes t a i b j

/-- The sequence of occurrence labels remembers the underlying schedule. -/
theorem occurrenceLabels_operations (s : List Op) :
    (occurrenceLabels s).map Prod.fst = s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simpa [occurrenceLabels, shiftLabel, Function.comp_def] using ih

theorem occurrenceLabels_injective :
    Function.Injective (occurrenceLabels (Op := Op)) := by
  intro s t h
  have hm := congrArg (List.map Prod.fst) h
  simpa only [occurrenceLabels_operations] using hm

/-- An equivalent, finite presentation of the paper's occurrence order: for
each conflicting pair, list the occurrences in their schedule order, labeling
the `i`-th occurrence of `a` by `(a,i)`. Equality of these lists says exactly
that the order of every conflicting pair of occurrences is preserved. -/
def LabeledOccurrenceEq (s t : List Op) : Prop :=
  (∀ a, s.count a = t.count a) ∧
  ∀ a b, obj.Conflict a b →
    occurrenceLabels (dependencyProjection a b s) =
      occurrenceLabels (dependencyProjection a b t)

theorem labeledOccurrenceEq_iff_dependencyEq (s t : List Op) :
    obj.LabeledOccurrenceEq s t ↔ obj.DependencyEq s t := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro a b hc
    exact occurrenceLabels_injective (h.2 a b hc)
  · intro h
    exact ⟨h.1, fun a b hc => congrArg occurrenceLabels (h.2 a b hc)⟩

/-- The adjacent-swap quotient is exactly the labeled conflicting-occurrence
order presentation used in the manuscript. -/
theorem traceEq_iff_labeledOccurrenceEq (s t : List Op) :
    obj.TraceEq s t ↔ obj.LabeledOccurrenceEq s t := by
  rw [obj.traceEq_iff_dependencyEq, obj.labeledOccurrenceEq_iff_dependencyEq]

/-- Equal labeled occurrence orders preserve the literal precedence predicate. -/
theorem LabeledOccurrenceEq.precedes {s t : List Op}
    (h : obj.LabeledOccurrenceEq s t) {a b : Op} {i j : Nat}
    (hc : obj.Conflict a b) :
    OccurrencePrecedes s a i b j ↔ OccurrencePrecedes t a i b j := by
  unfold OccurrencePrecedes
  rw [h.2 a b hc]

/-! ### The manuscript's definition, literally

`OccurrenceEq` is conditions (i) and (ii) of the manuscript's schedule
equivalence `s ∼ s'`; `traceEq_iff_occurrenceEq` identifies it with the
adjacent-swap quotient.  `OccurrencePrecedes` reads the order `≺ₛ` of (ii) in
the two-letter projection of `s`; the manuscript reads it in `s` itself.
`occurrencePrecedes_iff_schedulePrecedes` shows the two readings agree, so
`traceEq_iff_scheduleEquiv` states the equivalence with no presentation choice
left: occurrence multiplicities, and the order of conflicting occurrences in the
schedule.

The only combinatorial fact needed beyond the existing presentation is
`eq_of_nodup_of_order`: a duplicate-free list is determined by its members and
their relative order. -/

section Literal

omit [DecidableEq Op] in
private theorem idxOf_cons_of_ne {α : Type} [BEq α] [LawfulBEq α] {x y : α} {l : List α}
    (h : x ≠ y) : (x :: l).idxOf y = l.idxOf y + 1 := by
  rw [List.idxOf_cons]; simp [h]

omit [DecidableEq Op] in
/-- **A duplicate-free list is determined by its members and their order.** -/
theorem eq_of_nodup_of_order {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {L₁ L₂ : List α}, L₁.Nodup → L₂.Nodup → (∀ x, x ∈ L₁ ↔ x ∈ L₂) →
      (∀ x y, x ∈ L₁ → y ∈ L₁ → L₁.idxOf x < L₁.idxOf y → L₂.idxOf x < L₂.idxOf y) →
      L₁ = L₂
  | [], [], _, _, _, _ => rfl
  | [], y :: _, _, _, hmem, _ =>
      absurd ((hmem y).mpr (List.mem_cons_self ..)) (List.not_mem_nil)
  | x :: _, [], _, _, hmem, _ =>
      absurd ((hmem x).mp (List.mem_cons_self ..)) (List.not_mem_nil)
  | x :: L₁, y :: L₂, hn₁, hn₂, hmem, hord => by
      have hyx : y = x := by
        apply Classical.byContradiction
        intro hne
        have hy : y ∈ x :: L₁ := (hmem y).mpr (List.mem_cons_self ..)
        have hlt : (x :: L₁).idxOf x < (x :: L₁).idxOf y := by
          rw [List.idxOf_cons_self, idxOf_cons_of_ne (Ne.symm hne)]; omega
        have h := hord x y (List.mem_cons_self ..) hy hlt
        rw [List.idxOf_cons_self] at h
        omega
      subst hyx
      obtain ⟨hy₁, hn₁'⟩ := List.nodup_cons.mp hn₁
      obtain ⟨hy₂, hn₂'⟩ := List.nodup_cons.mp hn₂
      have hne₁ : ∀ z, z ∈ L₁ → y ≠ z := fun z hz he => hy₁ (he ▸ hz)
      have hne₂ : ∀ z, z ∈ L₂ → y ≠ z := fun z hz he => hy₂ (he ▸ hz)
      congr 1
      refine eq_of_nodup_of_order hn₁' hn₂' ?_ ?_
      · intro z
        constructor
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz)) with he | h
          · exact absurd he.symm (hne₁ z hz)
          · exact h
        · intro hz
          rcases List.mem_cons.mp ((hmem z).mpr (List.mem_cons_of_mem _ hz)) with he | h
          · exact absurd he.symm (hne₂ z hz)
          · exact h
      · intro z w hz hw hlt
        have h := hord z w (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ hw)
          (by rw [idxOf_cons_of_ne (hne₁ z hz), idxOf_cons_of_ne (hne₁ w hw)]; omega)
        have hz₂ : z ∈ L₂ := by
          rcases List.mem_cons.mp ((hmem z).mp (List.mem_cons_of_mem _ hz)) with he | h
          · exact absurd he.symm (hne₁ z hz)
          · exact h
        have hw₂ : w ∈ L₂ := by
          rcases List.mem_cons.mp ((hmem w).mp (List.mem_cons_of_mem _ hw)) with he | h
          · exact absurd he.symm (hne₁ w hw)
          · exact h
        rw [idxOf_cons_of_ne (hne₂ z hz₂), idxOf_cons_of_ne (hne₂ w hw₂)] at h
        omega

omit [DecidableEq Op] in
private theorem idxOf_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    {f : α → β} (hf : Function.Injective f) :
    ∀ (l : List α) (u : α), (l.map f).idxOf (f u) = l.idxOf u
  | [], _ => rfl
  | x :: l, u => by
      classical
      rw [List.map_cons]
      by_cases h : x = u
      · subst h; rw [List.idxOf_cons_self, List.idxOf_cons_self]
      · rw [idxOf_cons_of_ne (fun e => h (hf e)), idxOf_cons_of_ne h, idxOf_map_inj hf l u]

private theorem idxOf_shift_self (c : Op) (L : List (Op × Nat)) (k : Nat) :
    (L.map (shiftLabel c)).idxOf (c, k + 1) = L.idxOf (c, k) := by
  have h := idxOf_map_inj (shiftLabel_injective c) L (c, k)
  rwa [show shiftLabel c (c, k) = (c, k + 1) by simp [shiftLabel]] at h

private theorem idxOf_shift_other {c x : Op} (hx : x ≠ c) (L : List (Op × Nat)) (k : Nat) :
    (L.map (shiftLabel c)).idxOf (x, k) = L.idxOf (x, k) := by
  have h := idxOf_map_inj (shiftLabel_injective c) L (x, k)
  rwa [show shiftLabel c (x, k) = (x, k) by simp [shiftLabel, hx]] at h

/-- Every occurrence label is used once. -/
theorem occurrenceLabels_nodup : ∀ s : List Op, (occurrenceLabels s).Nodup
  | [] => List.nodup_nil
  | a :: s => by
      rw [occurrenceLabels, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hmem
        obtain ⟨⟨b, k⟩, -, hb⟩ := List.mem_map.mp hmem
        by_cases he : b = a
        · subst he
          simp [shiftLabel] at hb
        · have := congrArg Prod.fst hb
          simp [shiftLabel] at this
          exact he this
      · exact List.Pairwise.map (shiftLabel a)
          (fun u v huv h => huv (shiftLabel_injective a h)) (occurrenceLabels_nodup s)

/-- Occurrences of one operation are labeled in schedule order. -/
theorem occurrenceLabels_idxOf_lt (x : Op) : ∀ (s : List Op) {k m : Nat}, k < m →
    m < s.count x → (occurrenceLabels s).idxOf (x, k) < (occurrenceLabels s).idxOf (x, m)
  | [], _, _, _, hm => by simp at hm
  | c :: s, k, m, hkm, hm => by
      rw [occurrenceLabels]
      by_cases hc : c = x
      · subst hc
        have hm' : m < s.count c + 1 := by simpa [List.count_cons] using hm
        cases k with
        | zero =>
            rw [List.idxOf_cons_self, idxOf_cons_of_ne (by simp; omega)]
            omega
        | succ k =>
            obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
            rw [idxOf_cons_of_ne (by simp), idxOf_cons_of_ne (by simp),
              idxOf_shift_self, idxOf_shift_self]
            have := occurrenceLabels_idxOf_lt c s (k := k) (m := m') (by omega) (by omega)
            omega
      · have hm' : m < s.count x := by simpa [List.count_cons, hc] using hm
        rw [idxOf_cons_of_ne (by simp [hc]), idxOf_cons_of_ne (by simp [hc]),
          idxOf_shift_other (Ne.symm hc), idxOf_shift_other (Ne.symm hc)]
        have := occurrenceLabels_idxOf_lt x s hkm hm'
        omega

omit [DecidableEq Op] in
theorem dependencyProjection_comm (a b : Op) (s : List Op) [DecidableEq Op] :
    dependencyProjection a b s = dependencyProjection b a s := by
  unfold dependencyProjection
  apply List.filter_congr
  intro c _
  simp [or_comm]

theorem count_dependencyProjection (a b x : Op) (s : List Op) :
    (dependencyProjection a b s).count x = if x = a ∨ x = b then s.count x else 0 := by
  unfold dependencyProjection
  by_cases h : x = a ∨ x = b
  · rw [ite_eq_left h]; exact List.count_filter (by simpa using h)
  · rw [ite_eq_right h]
    apply List.count_eq_zero.mpr
    intro hm
    exact h (by simpa using (List.mem_filter.mp hm).2)

theorem mem_dependencyProjection {a b x : Op} {s : List Op}
    (h : x ∈ dependencyProjection a b s) : x = a ∨ x = b := by
  simpa using (List.mem_filter.mp h).2

/-- **The literal one-way condition already determines the projections.**  The
one-way implication of (ii), applied to both orders of a conflicting pair, fixes
the order of every cross pair; within one operation the order is fixed by the
occurrence index; so the labeled projections agree. -/
theorem OccurrenceEq.dependencyEq {s t : List Op} (h : obj.OccurrenceEq s t) :
    obj.DependencyEq s t := by
  refine ⟨h.1, ?_⟩
  intro a b hab
  apply occurrenceLabels_injective
  have hcount : ∀ x, (dependencyProjection a b s).count x
      = (dependencyProjection a b t).count x := by
    intro x; rw [count_dependencyProjection, count_dependencyProjection, h.1 x]
  refine eq_of_nodup_of_order (occurrenceLabels_nodup _) (occurrenceLabels_nodup _) ?_ ?_
  · rintro ⟨x, k⟩
    rw [occurrenceLabels_mem, occurrenceLabels_mem, hcount]
  · rintro ⟨x, k⟩ ⟨y, m⟩ hu hv hlt
    have hk : k < (dependencyProjection a b s).count x := (occurrenceLabels_mem _ x k).mp hu
    have hm : m < (dependencyProjection a b s).count y := (occurrenceLabels_mem _ y m).mp hv
    have hx : x = a ∨ x = b :=
      mem_dependencyProjection (List.count_pos_iff.mp (Nat.lt_of_le_of_lt (Nat.zero_le k) hk))
    have hy : y = a ∨ y = b :=
      mem_dependencyProjection (List.count_pos_iff.mp (Nat.lt_of_le_of_lt (Nat.zero_le m) hm))
    by_cases hxy : x = y
    · subst hxy
      have hkm : k < m := by
        rcases Nat.lt_trichotomy k m with h' | h' | h'
        · exact h'
        · subst h'; omega
        · have := occurrenceLabels_idxOf_lt x _ h' hk; omega
      exact occurrenceLabels_idxOf_lt x _ hkm (by rw [← hcount]; exact hm)
    · have hks : ∀ z, z = a ∨ z = b → (dependencyProjection a b s).count z = s.count z :=
        fun z hz => by rw [count_dependencyProjection, ite_eq_left hz]
      rcases hx with hxa | hxb
      · rcases hy with hya | hyb
        · exact absurd (hxa.trans hya.symm) hxy
        · subst hxa; subst hyb
          exact h.2 x y k m hab (by rw [← hks x (Or.inl rfl)]; exact hk)
            (by rw [← hks y (Or.inr rfl)]; exact hm) hlt
      · rcases hy with hya | hyb
        · subst hxb; subst hya
          have key : (occurrenceLabels (dependencyProjection x y s)).idxOf (x, k)
                < (occurrenceLabels (dependencyProjection x y s)).idxOf (y, m) →
              (occurrenceLabels (dependencyProjection x y t)).idxOf (x, k)
                < (occurrenceLabels (dependencyProjection x y t)).idxOf (y, m) :=
            h.2 x y k m (obj.conflict_symm hab)
              (by rw [← hks x (Or.inr rfl)]; exact hk)
              (by rw [← hks y (Or.inl rfl)]; exact hm)
          rw [dependencyProjection_comm x y s, dependencyProjection_comm x y t] at key
          exact key hlt
        · exact absurd (hxb.trans hyb.symm) hxy

theorem LabeledOccurrenceEq.occurrenceEq {s t : List Op}
    (h : obj.LabeledOccurrenceEq s t) : obj.OccurrenceEq s t :=
  ⟨h.1, fun _ _ _ _ hc _ _ hp => (LabeledOccurrenceEq.precedes obj h hc).mp hp⟩

/-- **The manuscript's schedule equivalence is the trace quotient**, with the
order read in the two-letter projection. -/
theorem traceEq_iff_occurrenceEq (s t : List Op) :
    obj.TraceEq s t ↔ obj.OccurrenceEq s t := by
  constructor
  · intro h
    exact LabeledOccurrenceEq.occurrenceEq obj ((obj.traceEq_iff_labeledOccurrenceEq s t).mp h)
  · intro h
    exact (obj.traceEq_iff_dependencyEq s t).mpr (OccurrenceEq.dependencyEq obj h)

/-! #### Reading `≺ₛ` in the schedule itself -/

/-- `a⁽ⁱ⁾ ≺ₛ b⁽ʲ⁾`: the manuscript's "total order on occurrences induced by `s`",
read in `s` itself. -/
def SchedulePrecedes (s : List Op) (a : Op) (i : Nat) (b : Op) (j : Nat) : Prop :=
  (occurrenceLabels s).idxOf (a, i) < (occurrenceLabels s).idxOf (b, j)

/-- **The manuscript's schedule equivalence `s ∼ s'`**, conditions (i) and (ii)
verbatim: equal multisets of operations, and every precedence `a⁽ⁱ⁾ ≺ₛ b⁽ʲ⁾`
between conflicting occurrences of `s` is kept in `s'`. -/
def ScheduleEquiv (s t : List Op) : Prop :=
  (∀ a, s.count a = t.count a) ∧
  ∀ a b i j, obj.Conflict a b → i < s.count a → j < s.count b →
    SchedulePrecedes s a i b j → SchedulePrecedes t a i b j

/-- Filtering a schedule keeps the labels of the occurrences it keeps: removing
other operations does not change how many earlier occurrences a kept one has. -/
theorem occurrenceLabels_filter (p : Op → Bool) : ∀ s : List Op,
    occurrenceLabels (s.filter p) = (occurrenceLabels s).filter (fun u => p u.1)
  | [] => rfl
  | c :: s => by
      have ih := occurrenceLabels_filter p s
      have hfst : (fun u : Op × Nat => p u.1) ∘ shiftLabel c = fun u => p u.1 := by
        funext u; simp [shiftLabel]
      rw [List.filter_cons]
      by_cases hpc : p c = true
      · rw [ite_eq_left hpc, occurrenceLabels, occurrenceLabels, ih, List.filter_cons, ite_eq_left hpc,
          List.filter_map, hfst]
      · rw [ite_eq_right hpc, occurrenceLabels, ih, List.filter_cons, ite_eq_right hpc, List.filter_map,
          hfst]
        have hid : ((occurrenceLabels s).filter (fun u => p u.1)).map (shiftLabel c)
            = ((occurrenceLabels s).filter (fun u => p u.1)).map id := by
          apply List.map_congr_left
          intro u hu
          have hpu := (List.mem_filter.mp hu).2
          have hne : u.1 ≠ c := fun e => hpc (e ▸ hpu)
          simp [shiftLabel, hne]
        rw [hid, List.map_id]

omit [DecidableEq Op] in
/-- Filtering preserves the relative order of the elements it keeps. -/
theorem idxOf_filter_lt_iff {α : Type} [BEq α] [LawfulBEq α] (q : α → Bool) :
    ∀ (L : List α) {u v : α}, u ∈ L → v ∈ L → q u = true → q v = true →
      ((L.filter q).idxOf u < (L.filter q).idxOf v ↔ L.idxOf u < L.idxOf v)
  | [], _, _, hu, _, _, _ => absurd hu List.not_mem_nil
  | w :: L, u, v, hu, hv, hqu, hqv => by
      classical
      by_cases huw : w = u
      · subst huw
        rw [List.filter_cons, ite_eq_left hqu, List.idxOf_cons_self, List.idxOf_cons_self]
        by_cases hvw : w = v
        · subst hvw; rw [List.idxOf_cons_self, List.idxOf_cons_self]
        · rw [idxOf_cons_of_ne hvw, idxOf_cons_of_ne hvw]; omega
      · by_cases hvw : w = v
        · subst hvw
          rw [List.filter_cons, ite_eq_left hqv, List.idxOf_cons_self, List.idxOf_cons_self]
          omega
        · have hu' : u ∈ L := by
            rcases List.mem_cons.mp hu with h | h
            · exact absurd h.symm huw
            · exact h
          have hv' : v ∈ L := by
            rcases List.mem_cons.mp hv with h | h
            · exact absurd h.symm hvw
            · exact h
          have ih := idxOf_filter_lt_iff q L hu' hv' hqu hqv
          rw [idxOf_cons_of_ne huw, idxOf_cons_of_ne hvw, List.filter_cons]
          by_cases hqw : q w = true
          · rw [ite_eq_left hqw, idxOf_cons_of_ne huw, idxOf_cons_of_ne hvw]; omega
          · rw [ite_eq_right hqw]; omega

/-- **The projection reading of `≺ₛ` is the schedule reading.** -/
theorem occurrencePrecedes_iff_schedulePrecedes {s : List Op} {a b : Op} {i j : Nat}
    (hi : i < s.count a) (hj : j < s.count b) :
    OccurrencePrecedes s a i b j ↔ SchedulePrecedes s a i b j := by
  show (occurrenceLabels (dependencyProjection a b s)).idxOf (a, i)
      < (occurrenceLabels (dependencyProjection a b s)).idxOf (b, j) ↔ _
  rw [dependencyProjection, occurrenceLabels_filter]
  exact idxOf_filter_lt_iff _ (occurrenceLabels s) ((occurrenceLabels_mem s a i).mpr hi)
    ((occurrenceLabels_mem s b j).mpr hj) (by simp) (by simp)

theorem occurrenceEq_iff_scheduleEquiv (s t : List Op) :
    obj.OccurrenceEq s t ↔ obj.ScheduleEquiv s t := by
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨hc, fun a b i j hab hi hj hs => ?_⟩
    have hi' : i < t.count a := by rw [← hc a]; exact hi
    have hj' : j < t.count b := by rw [← hc b]; exact hj
    exact (occurrencePrecedes_iff_schedulePrecedes hi' hj').mp
      (hp a b i j hab hi hj ((occurrencePrecedes_iff_schedulePrecedes hi hj).mpr hs))
  · rintro ⟨hc, hp⟩
    refine ⟨hc, fun a b i j hab hi hj hs => ?_⟩
    have hi' : i < t.count a := by rw [← hc a]; exact hi
    have hj' : j < t.count b := by rw [← hc b]; exact hj
    exact (occurrencePrecedes_iff_schedulePrecedes hi' hj').mpr
      (hp a b i j hab hi hj ((occurrencePrecedes_iff_schedulePrecedes hi hj).mp hs))

/-- **Schedule equivalence, exactly as the manuscript defines it, is the trace
quotient `O*/∼` used throughout.** -/
theorem traceEq_iff_scheduleEquiv (s t : List Op) :
    obj.TraceEq s t ↔ obj.ScheduleEquiv s t :=
  (obj.traceEq_iff_occurrenceEq s t).trans (obj.occurrenceEq_iff_scheduleEquiv s t)

end Literal

end ConflictFreedom.Object
