import CFLeanProof.TraceErase

/-!
# Compatibility of proposal families with pairwise independent content

The trace-theoretic step behind three compatibility claims of the manuscript:

* proof of Theorem `theorem:weakUCWCF`:
  "It follows that `S = ⋃_i {t_i · cmd_i ...}` only contains compatible traces";
* proof of Lemma `lemma:UCV2isCF`:
  "It follows that `S = ⋃_i {t · u_i · m_i}` only contains compatible traces";
* proof of Theorem `th:cr`: the same claim, for the operations invoked after
  `α'` and pending for ever.

All three arguments have the same shape: every command occurring in `u_i` and
`m_i` belongs to a *pending* operation, and after time `τ` pending operations
pairwise do not conflict; therefore the extensions `t · u_i · m_i` of the common
prefix `t` all fit below the single trace `t · D`, where `D` lists the pending
commands.

The key combinatorial fact is `tracePrefix_of_count_le` (and its converse,
`tracePrefix_iff_traceCount_le`): over an alphabet whose *distinct* letters are
pairwise independent, the trace monoid is free commutative, so the prefix order
is exactly multiset containment.  Independence is asked of distinct commands
only (`PairwiseIndependent`: an operation may conflict with itself,
`fetchAndIncrement_self_conflict`), and no duplicate-freedom hypothesis is
needed: a command contributed twice, say to `u_i` and to `m_j`, occurs twice in
the bound `D`.

The common prefix `t`, from GCA Convergence, cannot be dropped: with empty
`u_i` and `m_i` the independence hypothesis holds vacuously and the conclusion
fails (`incompatible_without_common_prefix`).
-/

namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-- A set of commands that pairwise commute.  This is the formal reading of the
manuscript's "these operations do not conflict between each other", restricted
(as it must be) to *distinct* commands. -/
def PairwiseIndependent (D : List Op) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, a ≠ b → obj.Independent a b

theorem pairwiseIndependent_of_not_conflict {D : List Op}
    (h : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → ¬ obj.Conflict a b) :
    obj.PairwiseIndependent D :=
  fun a ha b hb hab => (obj.independent_iff_not_conflict a b).mpr (h a ha b hb hab)

theorem pairwiseIndependent_subset {D E : List Op}
    (h : obj.PairwiseIndependent E) (hsub : ∀ a ∈ D, a ∈ E) :
    obj.PairwiseIndependent D :=
  fun a ha b hb hab => h a (hsub a ha) b (hsub b hb) hab

/-- Each participant's contribution is a sub-list of the concatenation of all
contributions, hence is bounded by it occurrence-wise. -/
theorem sublist_flatMap {ι : Type} {rep : ι → List Op} {L : List ι} {i : ι} (hi : i ∈ L) :
    (rep i).Sublist (L.flatMap rep) := by
  induction L with
  | nil => exact absurd hi (by simp)
  | cons j L ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp hi with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

/-- Inside a pairwise independent set of commands, every member is enabled at
the front of any schedule containing it. -/
theorem canStart_of_pairwiseIndependent {a : Op} {y : List Op}
    (hind : obj.PairwiseIndependent y) (ha : a ∈ y) : obj.CanStart a y := by
  induction y with
  | nil => exact absurd ha (by simp)
  | cons b y ih =>
    by_cases hab : a = b
    · exact Or.inl hab
    · have hmem : a ∈ y := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h hab
        · exact h
      refine Or.inr ⟨hind a ha b List.mem_cons_self hab, ?_⟩
      exact ih (fun c hc d hd hcd =>
        hind c (List.mem_cons_of_mem _ hc) d (List.mem_cons_of_mem _ hd) hcd) hmem

/-- Appending on the left is monotone for the prefix order. -/
theorem traceAppend_mono_right (u : obj.Trace) {s t : obj.Trace}
    (h : obj.TracePrefix s t) :
    obj.TracePrefix (obj.traceAppend u s) (obj.traceAppend u t) := by
  obtain ⟨w, rfl⟩ := (obj.tracePrefix_iff_append s t).mp h
  exact (obj.tracePrefix_iff_append _ _).mpr ⟨w, (obj.traceAppend_assoc u s w).symm⟩

section Nodup
variable [DecidableEq Op]

/-- A command absent from a schedule has zero occurrences. -/
theorem count_eq_zero_of_not_mem {x : List Op} {a : Op} (h : a ∉ x) : x.count a = 0 := by
  rcases Nat.eq_zero_or_pos (x.count a) with h0 | h0
  · exact h0
  · exact absurd (List.count_pos_iff.mp h0) h

/-- A duplicate-free schedule contains every command at most once. -/
theorem count_le_one_of_nodup {x : List Op} (hx : x.Nodup) (a : Op) : x.count a ≤ 1 := by
  induction x with
  | nil => simp
  | cons b x ih =>
    obtain ⟨hbx, hxn⟩ := List.nodup_cons.mp hx
    rw [List.count_cons]
    split
    · next h =>
        have hba : b = a := eq_of_beq h
        subst hba
        have h0 : x.count b = 0 := count_eq_zero_of_not_mem hbx
        omega
    · have h1 := ih hxn
      omega

/-- **Prefix = sub-multiset**, over pairwise independent letters.

This is the combinatorial core of the "only compatible traces are proposed"
claims of main.tex: inside a set of commands that pairwise commute, the prefix
order on traces is exactly multiset containment.  Note that no duplicate-freedom
hypothesis is needed once the independence hypothesis is read -- as it must be,
see `Independent` -- as a statement about *distinct* commands: swapping two
adjacent *equal* letters is the identity and needs no commutation rule. -/
theorem tracePrefix_of_count_le {x y : List Op}
    (hind : obj.PairwiseIndependent y)
    (hcount : ∀ a, x.count a ≤ y.count a) :
    obj.TracePrefix (Quotient.mk obj.traceSetoid x) (Quotient.mk obj.traceSetoid y) := by
  induction x generalizing y with
  | nil => exact obj.empty_tracePrefix _
  | cons a x ih =>
    have hpos : 0 < y.count a := by
      have h := hcount a
      have : 0 < (a :: x).count a := by
        rw [List.count_cons]; simp
      omega
    have ha : a ∈ y := List.count_pos_iff.mp hpos
    have hcs : obj.CanStart a y := obj.canStart_of_pairwiseIndependent hind ha
    have hyeq : Quotient.mk obj.traceSetoid y
        = Quotient.mk obj.traceSetoid (a :: y.erase a) :=
      Quotient.sound (obj.canStart_move hcs)
    rw [hyeq]
    have hind' : obj.PairwiseIndependent (y.erase a) :=
      obj.pairwiseIndependent_subset hind (fun c hc => List.mem_of_mem_erase hc)
    have hcount' : ∀ b, x.count b ≤ (y.erase a).count b := by
      intro b
      have hb := hcount b
      rw [List.count_cons] at hb
      rw [List.count_erase]
      by_cases hab : a = b
      · subst hab
        simp only [beq_self_eq_true, ite_true] at hb ⊢
        omega
      · simp only [beq_iff_eq, hab, ite_false] at hb ⊢
        omega
    exact obj.traceCons_mono a (ih hind' hcount')

/-- **Prefix = subset**, over pairwise independent, duplicate-free letters.
A convenience corollary of `tracePrefix_of_count_le`: `x.Nodup` makes set
inclusion imply multiset containment.  The hypothesis `hy` is not needed. -/
theorem tracePrefix_of_nodup_subset {x y : List Op} (hy : y.Nodup)
    (hind : ∀ a ∈ y, ∀ b ∈ y, a ≠ b → obj.Independent a b)
    (hsub : ∀ a ∈ x, a ∈ y) (hx : x.Nodup) :
    obj.TracePrefix (Quotient.mk obj.traceSetoid x) (Quotient.mk obj.traceSetoid y) := by
  have _ := hy
  refine obj.tracePrefix_of_count_le hind (fun a => ?_)
  by_cases hax : a ∈ x
  · have h1 : x.count a ≤ 1 := count_le_one_of_nodup hx a
    have h2 : 0 < y.count a := List.count_pos_iff.mpr (hsub a hax)
    omega
  · have h0 : x.count a = 0 := count_eq_zero_of_not_mem hax
    omega

/-- **Bonus.** Over pairwise independent letters the prefix order on traces is
*decided* by occurrence counts; the forward direction is `traceCount_mono`.
So the trace monoid generated by pairwise commuting commands is free
commutative, and every finite family of such traces is compatible. -/
theorem tracePrefix_iff_traceCount_le {x y : List Op}
    (hind : obj.PairwiseIndependent y) :
    obj.TracePrefix (Quotient.mk obj.traceSetoid x) (Quotient.mk obj.traceSetoid y)
      ↔ ∀ a, obj.traceCount a (Quotient.mk obj.traceSetoid x)
          ≤ obj.traceCount a (Quotient.mk obj.traceSetoid y) := by
  constructor
  · intro h a; exact obj.traceCount_mono h a
  · intro h; exact obj.tracePrefix_of_count_le hind h

/-- **Compatibility of a family of extensions of a common trace**, in its
sharpest form: no duplicate-freedom assumption at all, only that the commands
*occurring* above `t` pairwise commute when they are distinct.  The witness is
`t · D`, where `D` enumerates (with multiplicity) all commands contributed by
the family. -/
theorem compatible_append_of_content_count (t : obj.Trace)
    (V : obj.Trace → Prop) (D : List Op)
    (hind : obj.PairwiseIndependent D)
    (hV : ∀ v, V v → ∃ x : List Op,
      Quotient.mk obj.traceSetoid x = v ∧ ∀ a, x.count a ≤ D.count a) :
    obj.Compatible (fun s => ∃ v, V v ∧ s = obj.traceAppend t v) := by
  refine ⟨obj.traceAppend t (Quotient.mk obj.traceSetoid D), ?_⟩
  rintro s ⟨v, hv, rfl⟩
  obtain ⟨x, hx, hxc⟩ := hV v hv
  subst hx
  exact obj.traceAppend_mono_right t (obj.tracePrefix_of_count_le hind hxc)

/-- **Compatibility of a family of extensions of a common trace.**

Formalizes the manuscript's step "the set `⋃_i ops(u_i) ∪ ⋃_i ops(m_i)` only
contains pending operations, these do not conflict between each other, hence
`S = ⋃_i {t · u_i · m_i}` only contains compatible traces".  The witness is
`t · D`, where `D` enumerates the pending commands. -/
theorem compatible_append_of_independent_content (t : obj.Trace)
    (V : obj.Trace → Prop) (D : List Op) (hD : D.Nodup)
    (hind : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → obj.Independent a b)
    (hV : ∀ v, V v → ∃ x : List Op,
      Quotient.mk obj.traceSetoid x = v ∧ x.Nodup ∧ ∀ a ∈ x, a ∈ D) :
    obj.Compatible (fun s => ∃ v, V v ∧ s = obj.traceAppend t v) := by
  refine ⟨obj.traceAppend t (Quotient.mk obj.traceSetoid D), ?_⟩
  rintro s ⟨v, hv, rfl⟩
  obtain ⟨x, hx, hxn, hxs⟩ := hV v hv
  subst hx
  exact obj.traceAppend_mono_right t
    (obj.tracePrefix_of_nodup_subset hD hind hxs hxn)

/-- The same statement with the hypothesis phrased, as in the paper, by absence
of conflict rather than by independence. -/
theorem compatible_append_of_nonconflicting_content (t : obj.Trace)
    (V : obj.Trace → Prop) (D : List Op) (hD : D.Nodup)
    (hnc : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → ¬ obj.Conflict a b)
    (hV : ∀ v, V v → ∃ x : List Op,
      Quotient.mk obj.traceSetoid x = v ∧ x.Nodup ∧ ∀ a ∈ x, a ∈ D) :
    obj.Compatible (fun s => ∃ v, V v ∧ s = obj.traceAppend t v) :=
  obj.compatible_append_of_independent_content t V D hD
    (obj.pairwiseIndependent_of_not_conflict hnc) hV

end Nodup

section Indexed
variable [DecidableEq Op]
variable {ι : Type}

/-- **Indexed form.** Every participant `i ∈ L` extends the common trace `t` by
its own schedule `rep i`; the content bound `D` is the concatenation of all the
representatives, counted with multiplicity.  No duplicate-freedom hypothesis is
required: if the same command is contributed by two participants it simply
occurs twice in the bound. -/
theorem compatible_indexed_extensions (t : obj.Trace) (L : List ι) (rep : ι → List Op)
    (hind : ∀ a ∈ L.flatMap rep, ∀ b ∈ L.flatMap rep, a ≠ b → obj.Independent a b) :
    obj.Compatible
      (fun s => ∃ i ∈ L, s = obj.traceAppend t (Quotient.mk obj.traceSetoid (rep i))) := by
  obtain ⟨w, hw⟩ := obj.compatible_append_of_content_count t
    (fun v => ∃ i ∈ L, v = Quotient.mk obj.traceSetoid (rep i)) (L.flatMap rep) hind
    (by
      rintro v ⟨i, hi, rfl⟩
      exact ⟨rep i, rfl, fun a => List.Sublist.count_le a (sublist_flatMap hi)⟩)
  refine ⟨w, ?_⟩
  rintro s ⟨i, hi, rfl⟩
  exact hw _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩

/-- **The form used in the progress proofs.** `S = ⋃_{i ∈ L} { t · u_i · m_i }`
is compatible whenever any two *distinct* commands occurring in the `u_i` and
the `m_i` are independent.  This is literally the last line of
the invariant-(I) argument of Lemma `\ref{lemma:UCV2isCF}` and of Theorem
`\ref{th:cr}` in main.tex (and, with `m_i = [cmd_i]`, of Theorem `\WeakUCWCF`). -/
theorem compatible_round (t : obj.Trace) (L : List ι) (u m : ι → List Op)
    (hind : ∀ a ∈ L.flatMap (fun i => u i ++ m i),
      ∀ b ∈ L.flatMap (fun i => u i ++ m i), a ≠ b → obj.Independent a b) :
    obj.Compatible (fun s => ∃ i ∈ L,
      s = obj.traceAppend (obj.traceAppend t (Quotient.mk obj.traceSetoid (u i)))
        (Quotient.mk obj.traceSetoid (m i))) := by
  obtain ⟨w, hw⟩ := obj.compatible_indexed_extensions t L (fun i => u i ++ m i) hind
  refine ⟨w, ?_⟩
  rintro s ⟨i, hi, rfl⟩
  have hassoc : obj.traceAppend (obj.traceAppend t (Quotient.mk obj.traceSetoid (u i)))
      (Quotient.mk obj.traceSetoid (m i))
      = obj.traceAppend t (Quotient.mk obj.traceSetoid (u i ++ m i)) :=
    obj.traceAppend_assoc t _ _
  rw [hassoc]
  exact hw _ ⟨i, hi, rfl⟩

/-- Conflict-phrased version of `compatible_round`, matching the manuscript's
wording "these operations do not conflict between each other". -/
theorem compatible_round_of_not_conflict (t : obj.Trace) (L : List ι) (u m : ι → List Op)
    (hnc : ∀ a ∈ L.flatMap (fun i => u i ++ m i),
      ∀ b ∈ L.flatMap (fun i => u i ++ m i), a ≠ b → ¬ obj.Conflict a b) :
    obj.Compatible (fun s => ∃ i ∈ L,
      s = obj.traceAppend (obj.traceAppend t (Quotient.mk obj.traceSetoid (u i)))
        (Quotient.mk obj.traceSetoid (m i))) :=
  obj.compatible_round t L u m (obj.pairwiseIndependent_of_not_conflict hnc)

/-- The form closest to the manuscript's notation: process `i` retrieves `T i`
from `GCA_{r-1}` and proposes `T i · m_i`; `t` is the common prefix `⊓ 𝒯` and
`u i` is the unique trace with `T i = t · u_i`. -/
theorem compatible_proposals (t : obj.Trace) (L : List ι) (T : ι → obj.Trace)
    (u m : ι → List Op)
    (hT : ∀ i ∈ L, T i = obj.traceAppend t (Quotient.mk obj.traceSetoid (u i)))
    (hnc : ∀ a ∈ L.flatMap (fun i => u i ++ m i),
      ∀ b ∈ L.flatMap (fun i => u i ++ m i), a ≠ b → ¬ obj.Conflict a b) :
    obj.Compatible
      (fun s => ∃ i ∈ L, s = obj.traceAppend (T i) (Quotient.mk obj.traceSetoid (m i))) := by
  obtain ⟨w, hw⟩ := obj.compatible_round_of_not_conflict t L u m hnc
  refine ⟨w, ?_⟩
  rintro s ⟨i, hi, rfl⟩
  rw [hT i hi]
  exact hw _ ⟨i, hi, rfl⟩

/-- `Fin n`-indexed specialization: `n` participants, participant `i`
contributing `u i ++ m i` on top of the common prefix `t`. -/
theorem compatible_round_fin (t : obj.Trace) (n : Nat) (u m : Fin n → List Op)
    (hnc : ∀ a ∈ (List.finRange n).flatMap (fun i => u i ++ m i),
      ∀ b ∈ (List.finRange n).flatMap (fun i => u i ++ m i), a ≠ b → ¬ obj.Conflict a b) :
    obj.Compatible (fun s => ∃ i : Fin n,
      s = obj.traceAppend (obj.traceAppend t (Quotient.mk obj.traceSetoid (u i)))
        (Quotient.mk obj.traceSetoid (m i))) := by
  obtain ⟨w, hw⟩ := obj.compatible_round_of_not_conflict t (List.finRange n) u m hnc
  refine ⟨w, ?_⟩
  rintro s ⟨i, rfl⟩
  exact hw _ ⟨i, List.mem_finRange i, rfl⟩

end Indexed

end ConflictFreedom.Object

namespace ConflictFreedom

/-! ### Two witnesses backing the caveats reported on main.tex -/

/-- "Increment and return the new value": a single command that conflicts with
*itself*.  Consequently `Independent a a` is not free, and the manuscript's
"these operations do not conflict between each other" can only be read as a
statement about *distinct* commands (see `Object.PairwiseIndependent`). -/
def fetchAndIncrement : Object Nat Unit Nat where
  initial := 0
  step := fun _ q => (q + 1, q + 1)

theorem fetchAndIncrement_self_conflict : fetchAndIncrement.Conflict () () :=
  ⟨0, fun h => absurd h.1 (by decide)⟩

theorem fetchAndIncrement_not_self_independent :
    ¬ fetchAndIncrement.Independent () () :=
  fun h => ((fetchAndIncrement.independent_iff_not_conflict () ()).mp h)
    fetchAndIncrement_self_conflict

/-- A fully sequential object: the state records the whole schedule, so distinct
commands never commute and the trace quotient is trivial. -/
def history : Object (List Bool) Bool Unit where
  initial := []
  step := fun a q => ((), q ++ [a])

theorem history_finalState (s q : List Bool) : history.finalState s q = q ++ s := by
  induction s generalizing q with
  | nil => simp [Object.finalState]
  | cons a s ih =>
    show history.finalState s (q ++ [a]) = q ++ a :: s
    rw [ih]; simp

/-- Reading back the (unique) schedule of a trace of `history`. -/
def historyContent : history.Trace → List Bool := history.traceFinalState []

theorem historyContent_mk (x : List Bool) :
    historyContent (Quotient.mk history.traceSetoid x) = x := by
  show history.finalState x [] = x
  rw [history_finalState]; simp

theorem historyContent_prefix {s t : history.Trace} (h : history.TracePrefix s t) :
    ∃ y, historyContent t = historyContent s ++ y := by
  obtain ⟨x, y, rfl, rfl⟩ := h
  exact ⟨y, by rw [historyContent_mk, historyContent_mk]⟩

/-- **The common prefix hypothesis cannot be dropped.**  Here the extensions
`u_i` and `m_i` are empty, so the set of commands they contribute is empty and
*vacuously* pairwise non-conflicting; yet the two proposals are incompatible,
because the retrieved traces `t_i` themselves are.  This is exactly where the
manuscript's appeal to GCA Convergence (and to `t = ⊓ 𝒯`, which additionally
requires the family to be nonempty, cf. `no_empty_glb`) is indispensable. -/
theorem incompatible_without_common_prefix :
    ¬ history.Compatible (fun s =>
        s = Quotient.mk history.traceSetoid [true, false] ∨
        s = Quotient.mk history.traceSetoid [false, true]) := by
  rintro ⟨w, hw⟩
  obtain ⟨y₁, h₁⟩ := historyContent_prefix (hw _ (Or.inl rfl))
  obtain ⟨y₂, h₂⟩ := historyContent_prefix (hw _ (Or.inr rfl))
  rw [historyContent_mk] at h₁ h₂
  rw [h₁] at h₂
  simp at h₂

end ConflictFreedom
