import CFLeanProof.TraceCompatibility

/-! Compatibility of extensions built from pairwise non-conflicting operations.

This is the trace-theoretic core of invariant (I) in the progress proofs of
Theorem `theorem:weakUCWCF` and Lemma `lemma:UCV2isCF`: once every operation
that is still pending is non-conflicting with every other pending operation,
the proposals `t · u_i · m_i` built by the processes from a common prefix `t`
are mutually compatible, because each of them is a prefix of `t · W` for a
single arrangement `W` of the pending commands. -/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-- Distinct letters of a pairwise independent alphabet may be moved to the
front one at a time. Unlike `canStart_of_mem_of_independent`, no assumption
about `a` commuting with itself is needed. -/
theorem canStart_of_mem_of_pairwise {a : Op} {s : List Op} (h : a ∈ s)
    (hi : ∀ b ∈ s, b ≠ a → obj.Independent a b) : obj.CanStart a s := by
  induction s with
  | nil => simp at h
  | cons c s ih =>
    by_cases hac : a = c
    · exact Or.inl hac
    · have hmem : a ∈ s := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h hac
        · exact h
      refine Or.inr ⟨hi c List.mem_cons_self (fun hc => hac hc.symm), ?_⟩
      exact ih hmem (fun b hb hba => hi b (List.mem_cons_of_mem _ hb) hba)

variable [DecidableEq Op]

/-- Commands are unique invocation identifiers, so every trace handled by the
universal constructions carries each of them at most once. -/
def Simple (s : obj.Trace) : Prop := ∀ a, obj.traceCount a s ≤ 1

theorem simple_empty : obj.Simple obj.emptyTrace := by
  intro a
  change [].count a ≤ 1
  simp

theorem simple_of_prefix {s t : obj.Trace} (h : obj.TracePrefix s t)
    (ht : obj.Simple t) : obj.Simple s :=
  fun a => Nat.le_trans (obj.traceCount_mono h a) (ht a)

theorem simple_append {s u : obj.Trace} (h : obj.Simple (obj.traceAppend s u)) :
    obj.Simple u := by
  intro a
  have := h a
  rw [obj.traceCount_append] at this
  omega

/-- A duplicate-free selection from a pairwise independent alphabet is a trace
prefix of any arrangement of the whole alphabet. -/
theorem nodup_sublist_tracePrefix : ∀ (v W : List Op), v.Nodup → W.Nodup →
    (∀ a ∈ W, ∀ b ∈ W, a ≠ b → obj.Independent a b) → (∀ a ∈ v, a ∈ W) →
    obj.TracePrefix (Quotient.mk obj.traceSetoid v) (Quotient.mk obj.traceSetoid W) := by
  intro v
  induction v with
  | nil => intro W _ _ _ _; exact obj.empty_tracePrefix _
  | cons a v ih =>
    intro W hv hW hind hsub
    have haW : a ∈ W := hsub a List.mem_cons_self
    have hstart : obj.CanStart a W :=
      obj.canStart_of_mem_of_pairwise haW
        (fun b hb hba => obj.independent_symm (hind b hb a haW hba))
    have hmove : Quotient.mk obj.traceSetoid W
        = Quotient.mk obj.traceSetoid (a :: W.erase a) :=
      Quotient.sound (obj.canStart_move hstart)
    have hav : a ∉ v := (List.nodup_cons.mp hv).1
    have hsub' : ∀ b ∈ v, b ∈ W.erase a := by
      intro b hb
      have hba : b ≠ a := by
        intro hba
        exact hav (by rw [← hba]; exact hb)
      exact (List.mem_erase_of_ne hba).mpr (hsub b (List.mem_cons_of_mem _ hb))
    have hrest := ih (W.erase a) (List.nodup_cons.mp hv).2 (hW.erase a)
      (fun b hb c hc hbc => hind b (List.mem_of_mem_erase hb) c (List.mem_of_mem_erase hc) hbc)
      hsub'
    rw [hmove]
    have : obj.traceCons a (Quotient.mk obj.traceSetoid v)
        = Quotient.mk obj.traceSetoid (a :: v) := rfl
    have hcons := obj.traceCons_mono a hrest
    rw [this] at hcons
    exact hcons

/-- Trace form of the previous lemma: a trace with no repeated occurrence, all of
whose operations belong to a pairwise independent alphabet `W`, is a prefix of
any arrangement of `W`. -/
theorem tracePrefix_alphabet {u : obj.Trace} {W : List Op} (hW : W.Nodup)
    (hind : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → obj.Independent a b)
    (hsimple : ∀ a, obj.traceCount a u ≤ 1)
    (hletters : ∀ a, 0 < obj.traceCount a u → a ∈ W) :
    obj.TracePrefix u (Quotient.mk obj.traceSetoid W) := by
  induction u using Quotient.inductionOn with
  | h v =>
    have hcount : ∀ a, v.count a ≤ 1 := hsimple
    have hv : v.Nodup := List.nodup_iff_count.mpr hcount
    refine obj.nodup_sublist_tracePrefix v W hv hW hind ?_
    intro a ha
    refine hletters a ?_
    show 0 < v.count a
    exact List.count_pos_iff.mpr ha

/-- Invariant (I). Proposals obtained by extending one common trace `t` with
duplicate-free selections from a pairwise non-conflicting set of commands are
mutually compatible. The common upper bound is `t` followed by the whole set. -/
theorem compatible_of_independent_extensions (t : obj.Trace) (W : List Op)
    (hW : W.Nodup) (hind : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → obj.Independent a b)
    (S : obj.Trace → Prop)
    (hS : ∀ s, S s → ∃ u, s = obj.traceAppend t u ∧
      (∀ a, obj.traceCount a u ≤ 1) ∧ (∀ a, 0 < obj.traceCount a u → a ∈ W)) :
    obj.Compatible S := by
  refine ⟨obj.traceAppend t (Quotient.mk obj.traceSetoid W), ?_⟩
  intro s hs
  obtain ⟨u, rfl, hsimple, hletters⟩ := hS s hs
  obtain ⟨z, hz⟩ := (obj.tracePrefix_iff_append _ _).mp
    (obj.tracePrefix_alphabet hW hind hsimple hletters)
  refine (obj.tracePrefix_iff_append _ _).mpr ⟨z, ?_⟩
  rw [hz, obj.traceAppend_assoc]

omit [DecidableEq Op] in
/-- Pairwise non-conflict is exactly the hypothesis supplied by an eventually
conflict-free suffix, phrased with the conflict relation of the paper. -/
theorem independent_of_not_conflict {W : List Op}
    (h : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → ¬ obj.Conflict a b) :
    ∀ a ∈ W, ∀ b ∈ W, a ≠ b → obj.Independent a b :=
  fun a ha b hb hab => (obj.independent_iff_not_conflict a b).mpr (h a ha b hb hab)

end ConflictFreedom.Object
