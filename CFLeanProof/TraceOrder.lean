import CFLeanProof.Sequential

/-! Concrete prefix order and occurrence returns for the trace quotient. -/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-- The empty trace `ε`. -/
def emptyTrace : obj.Trace := Quotient.mk obj.traceSetoid []

theorem traceAppend_empty (s : obj.Trace) : obj.traceAppend s obj.emptyTrace = s := by
  induction s using Quotient.inductionOn with | h s =>
    change Quotient.mk _ (s ++ []) = Quotient.mk _ s
    simp

theorem empty_traceAppend (s : obj.Trace) : obj.traceAppend obj.emptyTrace s = s := by
  induction s using Quotient.inductionOn with | h s => rfl

theorem traceLength_append (s t : obj.Trace) :
    obj.traceLength (obj.traceAppend s t) = obj.traceLength s + obj.traceLength t := by
  induction s using Quotient.inductionOn with | h s =>
    induction t using Quotient.inductionOn with | h t =>
      exact List.length_append

theorem traceLength_zero_iff (s : obj.Trace) : obj.traceLength s = 0 ↔ s = obj.emptyTrace := by
  induction s using Quotient.inductionOn with | h s =>
    constructor
    · intro h
      change s.length = 0 at h
      have : s = [] := List.length_eq_zero_iff.mp h
      subst s
      rfl
    · intro h
      exact congrArg (obj.traceLength) h

/-- Equivalence with the paper's definition by a trace suffix. -/
theorem tracePrefix_iff_append (s t : obj.Trace) :
    obj.TracePrefix s t ↔ ∃ u, t = obj.traceAppend s u := by
  constructor
  · rintro ⟨x, y, rfl, rfl⟩
    exact ⟨Quotient.mk _ y, rfl⟩
  · rintro ⟨u, rfl⟩
    induction s using Quotient.inductionOn with | h s =>
      induction u using Quotient.inductionOn with | h u =>
        exact ⟨s, u, rfl, rfl⟩

theorem tracePrefix_refl (s : obj.Trace) : obj.TracePrefix s s :=
  (obj.tracePrefix_iff_append s s).mpr ⟨obj.emptyTrace, (obj.traceAppend_empty s).symm⟩

theorem tracePrefix_trans {s t u : obj.Trace}
    (hst : obj.TracePrefix s t) (htu : obj.TracePrefix t u) : obj.TracePrefix s u := by
  obtain ⟨v, rfl⟩ := (obj.tracePrefix_iff_append s t).mp hst
  obtain ⟨w, rfl⟩ := (obj.tracePrefix_iff_append _ u).mp htu
  exact (obj.tracePrefix_iff_append _ _).mpr
    ⟨obj.traceAppend v w, obj.traceAppend_assoc s v w⟩

theorem tracePrefix_length {s t : obj.Trace} (h : obj.TracePrefix s t) :
    obj.traceLength s ≤ obj.traceLength t := by
  obtain ⟨u, rfl⟩ := (obj.tracePrefix_iff_append s t).mp h
  rw [obj.traceLength_append]
  omega

theorem tracePrefix_eq_of_length_eq {s t : obj.Trace}
    (h : obj.TracePrefix s t) (hlen : obj.traceLength s = obj.traceLength t) : s = t := by
  obtain ⟨u, rfl⟩ := (obj.tracePrefix_iff_append s t).mp h
  rw [obj.traceLength_append] at hlen
  have hu : obj.traceLength u = 0 := by omega
  rw [(obj.traceLength_zero_iff u).mp hu, obj.traceAppend_empty]

theorem tracePrefix_antisymm {s t : obj.Trace}
    (hst : obj.TracePrefix s t) (hts : obj.TracePrefix t s) : s = t := by
  exact obj.tracePrefix_eq_of_length_eq hst
    (Nat.le_antisymm (obj.tracePrefix_length hst) (obj.tracePrefix_length hts))

theorem empty_tracePrefix (s : obj.Trace) : obj.TracePrefix obj.emptyTrace s :=
  (obj.tracePrefix_iff_append _ _).mpr ⟨s, (obj.empty_traceAppend s).symm⟩

/-- A compatible family has a finite trace extending every member. -/
def Compatible (S : obj.Trace → Prop) : Prop :=
  ∃ t, ∀ s, S s → obj.TracePrefix s t

/-- `g` is the greatest lower bound `⊓ S` in the prefix order. -/
def IsGLB (S : obj.Trace → Prop) (g : obj.Trace) : Prop :=
  (∀ s, S s → obj.TracePrefix g s) ∧
    ∀ l, (∀ s, S s → obj.TracePrefix l s) → obj.TracePrefix l g

/-- `u` is the least upper bound `⊔ S` in the prefix order. -/
def IsLUB (S : obj.Trace → Prop) (u : obj.Trace) : Prop :=
  (∀ s, S s → obj.TracePrefix s u) ∧
    ∀ v, (∀ s, S s → obj.TracePrefix s v) → obj.TracePrefix u v

theorem glb_unique {S : obj.Trace → Prop} {g h : obj.Trace}
    (hg : obj.IsGLB S g) (hh : obj.IsGLB S h) : g = h :=
  obj.tracePrefix_antisymm (hh.2 g hg.1) (hg.2 h hh.1)

theorem lub_unique {S : obj.Trace → Prop} {g h : obj.Trace}
    (hg : obj.IsLUB S g) (hh : obj.IsLUB S h) : g = h :=
  obj.tracePrefix_antisymm (hg.2 h hh.1) (hh.2 g hg.1)

/-- The empty family is compatible, but cannot have a GLB when an operation
exists. This formally checks the missing nonempty-family qualification. -/
theorem empty_compatible : obj.Compatible (fun _ => False) :=
  ⟨obj.emptyTrace, fun _ h => h.elim⟩

theorem no_empty_glb (a : Op) : ¬ ∃ g, obj.IsGLB (fun _ => False) g := by
  rintro ⟨g, _, hg⟩
  let one : obj.Trace := Quotient.mk obj.traceSetoid [a]
  have h := obj.tracePrefix_length (hg (obj.traceAppend g one) (fun _ h => h.elim))
  rw [obj.traceLength_append] at h
  have : obj.traceLength one = 1 := rfl
  omega

/-- A final-state interpretation, unlike intermediate-state sequences, is
well-defined on equivalence classes. -/
def traceFinalState [DecidableEq Op] (q : State) : obj.Trace → State :=
  Quotient.lift (fun s => obj.finalState s q) (fun _ _ h => (obj.traceEq_semantics h q).1)

/-- Zero-based occurrence number; `none` denotes an occurrence absent from t. -/
def traceReturn [DecidableEq Op] (a : Op) (k : Nat) (t : obj.Trace) : Option Response :=
  (obj.traceResponses a obj.initial t)[k]?

/-- RetTracePrefix, at the level of a particular operation occurrence. -/
theorem traceReturn_prefix [DecidableEq Op] {s t : obj.Trace}
    (h : obj.TracePrefix s t) (a : Op) (k : Nat)
    (hk : k < (obj.traceResponses a obj.initial s).length) :
    obj.traceReturn a k s = obj.traceReturn a k t := by
  obtain ⟨suffix, hs⟩ := obj.traceResponses_prefix h a obj.initial
  simp only [traceReturn, hs]
  symm
  exact List.getElem?_append_left hk

end ConflictFreedom.Object
