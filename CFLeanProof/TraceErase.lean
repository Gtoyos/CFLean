import CFLeanProof.TraceHeads

/-! Removing and prepending one occurrence on traces: `traceErase`,
`traceCons` and `traceCanStart`, the trace-level counterparts of
`List.erase`, `List.cons` and `CanStart`, with their effect on the prefix
order, on lengths and on counts.  The lattice and compatibility arguments
recurse on heads through `tracePrefix_head_completion`: if `a` can start an
extension of `s`, then `a · (s − a)` extends `s`. -/

namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The trace with one occurrence of `a` removed: erase the first `a` of any
representative. -/
def traceErase (a : Op) : obj.Trace → obj.Trace :=
  Quotient.lift (fun s => Quotient.mk obj.traceSetoid (s.erase a))
    (fun _ _ h => Quotient.sound (obj.traceEq_erase h a))

/-- `a` can be moved to the front of the trace (`CanStart`). -/
def traceCanStart (a : Op) : obj.Trace → Prop :=
  Quotient.lift (obj.CanStart a) (fun _ _ h => propext (obj.traceEq_canStart h a))

/-- The trace `a · s`. -/
def traceCons (a : Op) (s : obj.Trace) : obj.Trace :=
  obj.traceAppend (Quotient.mk obj.traceSetoid [a]) s

omit [DecidableEq Op] in
theorem traceCons_mono (a : Op) {s t : obj.Trace} (h : obj.TracePrefix s t) :
    obj.TracePrefix (obj.traceCons a s) (obj.traceCons a t) := by
  obtain ⟨u, rfl⟩ := (obj.tracePrefix_iff_append s t).mp h
  exact (obj.tracePrefix_iff_append _ _).mpr
    ⟨u, (obj.traceAppend_assoc _ _ _).symm⟩

theorem traceErase_mono (a : Op) {s t : obj.Trace} (h : obj.TracePrefix s t) :
    obj.TracePrefix (obj.traceErase a s) (obj.traceErase a t) := by
  obtain ⟨x, y, rfl, rfl⟩ := h
  by_cases hx : a ∈ x
  · change obj.TracePrefix (Quotient.mk _ (x.erase a)) (Quotient.mk _ ((x ++ y).erase a))
    rw [List.erase_append_left _ hx]
    exact ⟨_, _, rfl, rfl⟩
  · change obj.TracePrefix (Quotient.mk _ (x.erase a)) (Quotient.mk _ ((x ++ y).erase a))
    rw [List.erase_append_right _ hx, List.erase_of_not_mem hx]
    exact ⟨_, _, rfl, rfl⟩

omit [DecidableEq Op] in
theorem traceCanStart_cons (a : Op) (s : obj.Trace) : obj.traceCanStart a (obj.traceCons a s) := by
  induction s using Quotient.inductionOn with | h s => exact Or.inl rfl

theorem traceErase_cons (a : Op) (s : obj.Trace) : obj.traceErase a (obj.traceCons a s) = s := by
  induction s using Quotient.inductionOn with | h s =>
    change Quotient.mk _ ((a :: s).erase a) = Quotient.mk _ s
    simp

theorem traceCanStart_move {a : Op} {s : obj.Trace} (h : obj.traceCanStart a s) :
    s = obj.traceCons a (obj.traceErase a s) := by
  induction s using Quotient.inductionOn with | h s => exact Quotient.sound (obj.canStart_move h)

omit [DecidableEq Op] in
theorem traceCanStart_mono {a : Op} {s t : obj.Trace}
    (h : obj.TracePrefix s t) (hs : obj.traceCanStart a s) : obj.traceCanStart a t := by
  obtain ⟨x, y, rfl, rfl⟩ := h
  exact (obj.canStart_append a x y).mpr (Or.inl hs)

omit [DecidableEq Op] in
theorem canStart_of_mem_of_independent {a : Op} {s : List Op}
    (h : a ∈ s) (hi : ∀ b ∈ s, obj.Independent a b) : obj.CanStart a s := by
  induction s with
  | nil => simp at h
  | cons b s ih =>
    rcases List.mem_cons.mp h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hi b List.mem_cons_self, ih h (fun c hc => hi c (List.mem_cons_of_mem _ hc))⟩

omit [DecidableEq Op] in
theorem move_past_independent (a : Op) (s t : List Op)
    (hi : ∀ b ∈ s, obj.Independent a b) :
    obj.TraceEq (a :: (s ++ t)) (s ++ a :: t) := by
  induction s with
  | nil => exact TraceEq.refl _
  | cons b s ih =>
    exact (TraceEq.swap [] (s ++ t) a b (hi b List.mem_cons_self)).trans
      (obj.traceEq_append_left [b] (ih (fun c hc => hi c (List.mem_cons_of_mem _ hc))))

/-- If a is enabled above s, adding its missing first occurrence extends s;
if it already occurs in s, the resulting trace equals s. -/
theorem tracePrefix_head_completion {a : Op} {s t : obj.Trace}
    (hst : obj.TracePrefix s t) (ha : obj.traceCanStart a t) :
    obj.TracePrefix s (obj.traceCons a (obj.traceErase a s)) := by
  obtain ⟨x, y, rfl, rfl⟩ := hst
  change obj.CanStart a (x ++ y) at ha
  rcases (obj.canStart_append a x y).mp ha with hx | ⟨hi, _⟩
  · have he := Quotient.sound (s := obj.traceSetoid) (obj.canStart_move hx)
    change obj.TracePrefix (Quotient.mk obj.traceSetoid x)
      (Quotient.mk obj.traceSetoid (a :: x.erase a))
    rw [← he]
    exact obj.tracePrefix_refl _
  · by_cases hm : a ∈ x
    · have he := Quotient.sound (s := obj.traceSetoid) (obj.canStart_move (obj.canStart_of_mem_of_independent hm hi))
      change obj.TracePrefix (Quotient.mk obj.traceSetoid x)
        (Quotient.mk obj.traceSetoid (a :: x.erase a))
      rw [← he]
      exact obj.tracePrefix_refl _
    · change obj.TracePrefix (Quotient.mk obj.traceSetoid x)
        (Quotient.mk obj.traceSetoid (a :: x.erase a))
      rw [List.erase_of_not_mem hm]
      refine ⟨x, [a], rfl, ?_⟩
      apply Quotient.sound (s := obj.traceSetoid)
      change obj.TraceEq (x ++ [a]) (a :: x)
      simpa using (obj.move_past_independent a x [] hi).symm

omit [DecidableEq Op] in
theorem traceLength_cons (a : Op) (s : obj.Trace) :
    obj.traceLength (obj.traceCons a s) = obj.traceLength s + 1 := by
  induction s using Quotient.inductionOn with | h s =>
    change (a :: s).length = s.length + 1
    rfl

theorem traceLength_erase_lt {a : Op} {s : obj.Trace} (h : obj.traceCanStart a s) :
    obj.traceLength (obj.traceErase a s) < obj.traceLength s := by
  have he := congrArg obj.traceLength (obj.traceCanStart_move h)
  rw [obj.traceLength_cons] at he
  omega

theorem traceCount_cons (a b : Op) (s : obj.Trace) :
    obj.traceCount b (obj.traceCons a s) = obj.traceCount b s + if a = b then 1 else 0 := by
  induction s using Quotient.inductionOn with | h s =>
    change (a :: s).count b = s.count b + if a = b then 1 else 0
    simp [List.count_cons]

theorem traceCount_erase (a b : Op) (s : obj.Trace) :
    obj.traceCount b (obj.traceErase a s) = obj.traceCount b s - if a = b then 1 else 0 := by
  induction s using Quotient.inductionOn with | h s =>
    change (s.erase a).count b = s.count b - if a = b then 1 else 0
    simpa using (List.count_erase (a := b) (b := a) (l := s))

theorem traceCount_pos_of_canStart {a : Op} {s : obj.Trace} (ha : obj.traceCanStart a s) :
    0 < obj.traceCount a s := by
  have he := congrArg (obj.traceCount a) (obj.traceCanStart_move ha)
  rw [obj.traceCount_cons] at he
  simp only [ite_true] at he
  omega

end ConflictFreedom.Object
