import CFLeanProof.TraceOrder

/-! Occurrence content and cancellation in the concrete trace monoid. -/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-- Swap equivalence preserves the multiset of operations. -/
theorem traceEq_perm {s t : List Op} (h : obj.TraceEq s t) : s.Perm t := by
  induction h with
  | refl => exact List.Perm.refl _
  | swap x y a b _ => exact List.Perm.append_left x (List.Perm.swap _ _ _)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem traceEq_count [DecidableEq Op] {s t : List Op} (h : obj.TraceEq s t) (a : Op) :
    s.count a = t.count a := (obj.traceEq_perm h).count_eq a

/-- The number of occurrences of `a` in a trace. -/
def traceCount [DecidableEq Op] (a : Op) : obj.Trace → Nat :=
  Quotient.lift (fun s => s.count a) (fun _ _ h => obj.traceEq_count h a)

theorem traceCount_append [DecidableEq Op] (a : Op) (s t : obj.Trace) :
    obj.traceCount a (obj.traceAppend s t) = obj.traceCount a s + obj.traceCount a t := by
  induction s using Quotient.inductionOn with | h s =>
    induction t using Quotient.inductionOn with | h t =>
      exact List.count_append

theorem responses_length [DecidableEq Op] (a : Op) (s : List Op) (q : State) :
    (obj.responses a s q).length = s.count a := by
  induction s generalizing q with
  | nil => rfl
  | cons b s ih =>
    by_cases h : b = a
    · subst b; simp [responses, ih]
    · simp [responses, ih, h]

theorem traceResponses_length [DecidableEq Op] (a : Op) (q : State) (t : obj.Trace) :
    (obj.traceResponses a q t).length = obj.traceCount a t := by
  induction t using Quotient.inductionOn with | h t => exact obj.responses_length a t q

theorem traceCount_mono [DecidableEq Op] {s t : obj.Trace}
    (h : obj.TracePrefix s t) (a : Op) : obj.traceCount a s ≤ obj.traceCount a t := by
  obtain ⟨u, rfl⟩ := (obj.tracePrefix_iff_append s t).mp h
  rw [obj.traceCount_append]
  omega

/-- A proper trace extension must introduce an additional occurrence. -/
theorem tracePrefix_eq_of_count_le [DecidableEq Op] {s t : obj.Trace}
    (hp : obj.TracePrefix s t) (hc : ∀ a, obj.traceCount a t ≤ obj.traceCount a s) : s = t := by
  obtain ⟨u, rfl⟩ := (obj.tracePrefix_iff_append s t).mp hp
  have empty : u = obj.emptyTrace := by
    induction u using Quotient.inductionOn with
    | h us =>
      cases us with
      | nil => rfl
      | cons a us =>
        have h := hc a
        rw [obj.traceCount_append a s (Quotient.mk obj.traceSetoid (a :: us))] at h
        have hpos : 0 < obj.traceCount a (Quotient.mk obj.traceSetoid (a :: us)) := by
          change 0 < (a :: us).count a
          simp
        omega
  rw [empty, obj.traceAppend_empty]

/-- Erasing the first occurrence of one operation respects swap equivalence. -/
theorem traceEq_erase [DecidableEq Op] {s t : List Op} (h : obj.TraceEq s t) (a : Op) :
    obj.TraceEq (s.erase a) (t.erase a) := by
  induction h with
  | refl => exact TraceEq.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | swap x y b c hi =>
    by_cases hx : a ∈ x
    · rw [List.erase_append_left _ hx, List.erase_append_left _ hx]
      exact TraceEq.swap _ _ _ _ hi
    · rw [List.erase_append_right _ hx, List.erase_append_right _ hx]
      by_cases hb : b = a
      · subst b
        by_cases hc : c = a
        · subst c; exact TraceEq.refl _
        · simp only [List.erase_cons_head, List.erase_cons, beq_iff_eq,
            ite_eq_right hc]
          exact TraceEq.refl _
      · by_cases hc : c = a
        · subst c
          simp only [List.erase_cons_head, List.erase_cons, beq_iff_eq,
            ite_eq_right hb]
          exact TraceEq.refl _
        · simp only [List.erase_cons, beq_iff_eq, ite_eq_right hb, ite_eq_right hc]
          exact TraceEq.swap _ _ _ _ hi

theorem traceEq_cancel_cons [DecidableEq Op] {a : Op} {s t : List Op}
    (h : obj.TraceEq (a :: s) (a :: t)) : obj.TraceEq s t := by
  simpa using obj.traceEq_erase h a

theorem traceEq_cancel_left [DecidableEq Op] (x : List Op) {s t : List Op}
    (h : obj.TraceEq (x ++ s) (x ++ t)) : obj.TraceEq s t := by
  induction x with
  | nil => exact h
  | cons a x ih => exact ih (obj.traceEq_cancel_cons h)

theorem traceEq_reverse {s t : List Op} (h : obj.TraceEq s t) :
    obj.TraceEq s.reverse t.reverse := by
  induction h with
  | refl => exact TraceEq.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | swap x y a b hi =>
    simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using
      (TraceEq.swap y.reverse x.reverse b a (obj.independent_symm hi))

theorem traceEq_cancel_right [DecidableEq Op] (x : List Op) {s t : List Op}
    (h : obj.TraceEq (s ++ x) (t ++ x)) : obj.TraceEq s t := by
  have hr := obj.traceEq_reverse h
  simp only [List.reverse_append] at hr
  have hc := obj.traceEq_reverse (obj.traceEq_cancel_left x.reverse hr)
  simpa using hc

theorem traceAppend_left_cancel [DecidableEq Op] {s t u : obj.Trace}
    (h : obj.traceAppend s t = obj.traceAppend s u) : t = u := by
  induction s using Quotient.inductionOn with | h s =>
    induction t using Quotient.inductionOn with | h t =>
      induction u using Quotient.inductionOn with | h u =>
        exact Quotient.sound (obj.traceEq_cancel_left s (Quotient.exact h))

theorem traceAppend_right_cancel [DecidableEq Op] {s t u : obj.Trace}
    (h : obj.traceAppend t s = obj.traceAppend u s) : t = u := by
  induction s using Quotient.inductionOn with | h s =>
    induction t using Quotient.inductionOn with | h t =>
      induction u using Quotient.inductionOn with | h u =>
        exact Quotient.sound (obj.traceEq_cancel_right s (Quotient.exact h))

/-- Trace suffixes are unique, even when a prefix has several representatives. -/
theorem traceSuffix_unique [DecidableEq Op] {s t u v : obj.Trace}
    (hu : t = obj.traceAppend s u) (hv : t = obj.traceAppend s v) : u = v :=
  obj.traceAppend_left_cancel (hu.symm.trans hv)

end ConflictFreedom.Object
