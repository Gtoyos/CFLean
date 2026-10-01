import CFLeanProof.TraceAlgebra

/-! Heads of a schedule.  An operation *can start* a schedule (`CanStart`) when
it occurs in it and commutes with every operation before its first occurrence:
swaps of independent operations then bring it to the front (`canStart_move`).
The property is invariant under trace equality (`traceEq_canStart`), and two
distinct heads commute (`canStart_diamond`). -/

namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-- An occurrence can move to the front by swapping past independent letters. -/
def CanStart (a : Op) : List Op → Prop
  | [] => False
  | b :: s => a = b ∨ (obj.Independent a b ∧ CanStart a s)

theorem canStart_append (a : Op) (s t : List Op) :
    obj.CanStart a (s ++ t) ↔
      obj.CanStart a s ∨ ((∀ b ∈ s, obj.Independent a b) ∧ obj.CanStart a t) := by
  induction s with
  | nil => simp [CanStart]
  | cons b s ih => simp only [List.cons_append, CanStart, ih, List.mem_cons]; grind

theorem canStart_swap (a b c : Op) (s : List Op) (h : obj.Independent b c) :
    obj.CanStart a (b :: c :: s) ↔ obj.CanStart a (c :: b :: s) := by
  by_cases hab : a = b
  · subst b
    simp [CanStart, h]
  · by_cases hac : a = c
    · subst c
      have hr := obj.independent_symm h
      simp [CanStart, hr]
    · simp only [CanStart, hab, hac, false_or]
      exact ⟨fun ⟨hb, hc, hs⟩ => ⟨hc, hb, hs⟩,
        fun ⟨hc, hb, hs⟩ => ⟨hb, hc, hs⟩⟩

theorem traceEq_canStart {s t : List Op} (h : obj.TraceEq s t) (a : Op) :
    obj.CanStart a s ↔ obj.CanStart a t := by
  induction h with
  | refl => exact Iff.rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | swap x y b c hi =>
    rw [obj.canStart_append, obj.canStart_append, obj.canStart_swap a b c y hi]

theorem canStart_mem {a : Op} {s : List Op} (h : obj.CanStart a s) : a ∈ s := by
  induction s with
  | nil => exact h.elim
  | cons b s ih =>
    rcases h with rfl | ⟨_, hs⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hs)

theorem canStart_move [DecidableEq Op] {a : Op} {s : List Op} (h : obj.CanStart a s) :
    obj.TraceEq s (a :: s.erase a) := by
  induction s with
  | nil => exact h.elim
  | cons b s ih =>
    by_cases hab : b = a
    · subst b; simp only [List.erase_cons_head]; exact TraceEq.refl _
    · rcases h with h | ⟨hi, hs⟩
      · exact False.elim (hab h.symm)
      · simp only [List.erase_cons, beq_iff_eq, ite_eq_right hab]
        exact (obj.traceEq_append_left [b] (ih hs)).trans
          (TraceEq.swap [] (s.erase a) b a (obj.independent_symm hi))

/-- A front operation of any equivalent schedule is enabled in this one. -/
theorem canStart_of_traceEq_cons {a : Op} {s t : List Op}
    (h : obj.TraceEq s (a :: t)) : obj.CanStart a s :=
  (obj.traceEq_canStart h a).mpr (Or.inl rfl)

/-- Distinct enabled heads commute and remain enabled after removing one. -/
theorem canStart_diamond [DecidableEq Op] {a b : Op} {s : List Op}
    (ha : obj.CanStart a s) (hb : obj.CanStart b s) (hne : a ≠ b) :
    obj.Independent a b ∧ obj.CanStart b (s.erase a) := by
  induction s with
  | nil => exact ha.elim
  | cons c s ih =>
    by_cases hac : c = a
    · subst c
      rcases hb with h | ⟨hi, hs⟩
      · exact False.elim (hne h.symm)
      · exact ⟨obj.independent_symm hi, by simpa using hs⟩
    · simp only [List.erase_cons, beq_iff_eq, ite_eq_right hac]
      rcases ha with h | ⟨hi, ha⟩
      · exact False.elim (hac h.symm)
      · rcases hb with rfl | ⟨hj, hb⟩
        · exact ⟨hi, Or.inl rfl⟩
        · obtain ⟨hab, hs⟩ := ih ha hb
          exact ⟨hab, Or.inr ⟨hj, hs⟩⟩

end ConflictFreedom.Object
