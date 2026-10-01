import CFLeanProof.TraceHeads

/-! A second characterization of trace equality: equal operation multiplicities
and equal two-letter projections for every conflicting pair. A two-letter word
records the relative order of all occurrences of those letters. -/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The two-letter word of the occurrences of `a` and `b` in `s`. -/
def dependencyProjection (a b : Op) (s : List Op) : List Op :=
  s.filter (fun c => decide (c = a ∨ c = b))

/-- Equal multiplicities, and equal two-letter projections for every conflicting
pair. -/
def DependencyEq (s t : List Op) : Prop :=
  (∀ a, s.count a = t.count a) ∧
  ∀ a b, obj.Conflict a b → dependencyProjection a b s = dependencyProjection a b t

private theorem projection_swap (a b p q : Op) (y : List Op)
    (hc : obj.Conflict a b) (hi : obj.Independent p q) :
    dependencyProjection a b (p :: q :: y) = dependencyProjection a b (q :: p :: y) := by
  have hn := (obj.independent_iff_not_conflict p q).mp hi
  by_cases hp : p = a ∨ p = b
  · by_cases hq : q = a ∨ q = b
    · have he : p = q := by
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
        · rfl
        · exact False.elim (hn hc)
        · exact False.elim (hn (obj.conflict_symm hc))
        · rfl
      subst q; rfl
    · simp [dependencyProjection, hp, hq]
  · by_cases hq : q = a ∨ q = b <;> simp [dependencyProjection, hp, hq]

theorem traceEq_dependencyEq {s t : List Op} (h : obj.TraceEq s t) : obj.DependencyEq s t := by
  refine ⟨obj.traceEq_count h, ?_⟩
  intro a b hc
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | swap x y p q hi =>
    have hs := projection_swap obj a b p q y hc hi
    unfold dependencyProjection at hs ⊢
    simp only [List.filter_append]
    rw [hs]

theorem dependencyEq_erase {s t : List Op} (h : obj.DependencyEq s t) (a : Op) :
    obj.DependencyEq (s.erase a) (t.erase a) := by
  constructor
  · intro b
    rw [List.count_erase, List.count_erase, h.1 b]
  · intro b c hc
    have hh := congrArg (fun l : List Op => l.erase a) (h.2 b c hc)
    simpa only [dependencyProjection, List.erase_filter] using hh

/-- Equal dependence projections preserve the set of enabled first letters. -/
theorem dependencyEq_canStart {a : Op} {s t : List Op}
    (h : obj.DependencyEq (a :: s) t) : obj.CanStart a t := by
  induction t generalizing s with
  | nil =>
    have hc := h.1 a
    simp at hc
  | cons b t ih =>
    by_cases hab : a = b
    · exact Or.inl hab
    · have hi : obj.Independent a b := by
        apply (obj.independent_iff_not_conflict a b).mpr
        intro hc
        have hh := h.2 a b hc
        simp only [dependencyProjection, List.filter_cons, decide_true, ite_true,
          true_or, or_true] at hh
        exact hab (List.cons.inj hh).1
      refine Or.inr ⟨hi, ?_⟩
      have he := obj.dependencyEq_erase h b
      simp only [List.erase_cons_head, List.erase_cons, beq_iff_eq, ite_eq_right hab] at he
      exact ih he

/-- Completeness of the dependence-projection presentation of finite traces. -/
theorem dependencyEq_traceEq {s t : List Op} (h : obj.DependencyEq s t) : obj.TraceEq s t := by
  induction s generalizing t with
  | nil =>
    have ht : t = [] := by
      cases t with
      | nil => rfl
      | cons a t =>
        have hc := h.1 a
        simp at hc
    subst t; exact TraceEq.refl _
  | cons a s ih =>
    have ha := obj.dependencyEq_canStart h
    have he := obj.dependencyEq_erase h a
    simp only [List.erase_cons_head] at he
    exact (obj.traceEq_append_left [a] (ih he)).trans (obj.canStart_move ha).symm

theorem traceEq_iff_dependencyEq (s t : List Op) : obj.TraceEq s t ↔ obj.DependencyEq s t :=
  ⟨obj.traceEq_dependencyEq, obj.dependencyEq_traceEq⟩

end ConflictFreedom.Object
