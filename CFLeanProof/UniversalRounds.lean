import CFLeanProof.GCA

/-! The common safety invariant used by both universal constructions. Rounds are
zero-based here. Each proposal after round zero extends an output of the previous
round: either the caller's adopted trace, or a committed trace read from S.
Each program establishes it from its own transitions (`WeakUniversal.roundExecution`,
`HelpingUniversal.roundExecution`). -/
namespace ConflictFreedom.GCA
open Object
variable {State Op Response P : Type} (obj : Object State Op Response)

/-- A sequence of GCA instances linked as in both constructions: every input to
round `r + 1` extends some output of round `r`. -/
structure RoundExecution (P : Type) where
  round : Nat → History obj P
  predecessor : ∀ r p s, (round (r + 1)).input p = some s →
    ∃ q t c, (round r).output q = some (t, c) ∧ obj.TracePrefix t s

namespace RoundExecution
variable {obj} [DecidableEq Op] (e : RoundExecution obj P)
variable (spec : ∀ r, (e.round r).Specification)
include spec

/-- A committed trace is a prefix of every output in its own round. -/
theorem commit_below_same_round {r : Nat} {p q : P} {s t : obj.Trace} {c : Bool}
    (hs : (e.round r).output p = some (s, true))
    (ht : (e.round r).output q = some (t, c)) : obj.TracePrefix s t :=
  (spec r).adoption p s hs q t c ht

omit spec [DecidableEq Op] in
/-- An output lower bound is inherited by every proposal in the next round. -/
theorem lower_bound_next_inputs {r : Nat} {s : obj.Trace}
    (hl : ∀ t, (e.round r).Outputs t → obj.TracePrefix s t) :
    ∀ t, (e.round (r + 1)).Inputs t → obj.TracePrefix s t := by
  rintro t ⟨p, hp⟩
  obtain ⟨q, u, c, hu, hut⟩ := e.predecessor r p t hp
  exact obj.tracePrefix_trans (hl u ⟨q, c, hu⟩) hut

/-- Common-prefix preservation propagates the invariant through one round. -/
theorem lower_bound_next_outputs {r : Nat} {s : obj.Trace}
    (hl : ∀ t, (e.round r).Outputs t → obj.TracePrefix s t) :
    ∀ t, (e.round (r + 1)).Outputs t → obj.TracePrefix s t :=
  (spec (r + 1)).commonPrefix s (e.lower_bound_next_inputs hl)

/-- Prefix-rounds lemma: a committed trace is a prefix of all outputs in every
later round, with no assumptions of full participation or full return. -/
theorem commit_below_later_output {r k : Nat} (hrk : r ≤ k)
    {p q : P} {s t : obj.Trace} {c : Bool}
    (hs : (e.round r).output p = some (s, true))
    (ht : (e.round k).output q = some (t, c)) : obj.TracePrefix s t := by
  have invariant : ∀ d, ∀ u, (e.round (r + d)).Outputs u → obj.TracePrefix s u := by
    intro d
    induction d with
    | zero =>
      rintro u ⟨q, c, hq⟩
      exact (spec r).adoption p s hs q u c hq
    | succ d ih => exact e.lower_bound_next_outputs spec ih
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrk
  exact invariant d t ⟨q, c, ht⟩

/-- A commit is also a prefix of every proposal in every strictly later round. -/
theorem commit_below_later_input {r k : Nat} (hrk : r < k)
    {p q : P} {s t : obj.Trace}
    (hs : (e.round r).output p = some (s, true))
    (ht : (e.round k).input q = some t) : obj.TracePrefix s t := by
  cases k with
  | zero => omega
  | succ k =>
    obtain ⟨j, u, c, hu, hut⟩ := e.predecessor k q t ht
    exact obj.tracePrefix_trans (e.commit_below_later_output spec (by omega) hs hu) hut

/-- Every pair of committed traces is prefix-comparable. -/
theorem commits_comparable {r k : Nat} {p q : P} {s t : obj.Trace}
    (hs : (e.round r).output p = some (s, true))
    (ht : (e.round k).output q = some (t, true)) :
    obj.TracePrefix s t ∨ obj.TracePrefix t s := by
  by_cases h : r ≤ k
  · exact Or.inl (e.commit_below_later_output spec h hs ht)
  · exact Or.inr (e.commit_below_later_output spec (by omega) ht hs)

/-- A response extracted from a committed trace remains the same in every later
output containing that occurrence. This is the response part of the universal
constructions' prefix invariant, not a complete history linearizability proof. -/
theorem committed_return_stable {r k : Nat} (hrk : r ≤ k)
    {p q : P} {s t : obj.Trace} {c : Bool}
    (hs : (e.round r).output p = some (s, true))
    (ht : (e.round k).output q = some (t, c))
    (a : Op) (j : Nat) (hj : j < (obj.traceResponses a obj.initial s).length) :
    obj.traceReturn a j s = obj.traceReturn a j t :=
  obj.traceReturn_prefix (e.commit_below_later_output spec hrk hs ht) a j hj

/-! ### The chain of committed traces

The proof of `theorem:weakUCLin` fixes `t_0 = ε`, lets `t_k` be the trace
committed at round `k` — unique by Adoption — and sets `t_{k+1} = t_k` when no
trace is committed at round `k + 1`.  Here round `k + 1` is `e.round k`. -/

open Classical in
omit spec [DecidableEq Op] in
/-- The manuscript's `t_k`: `t_0 = ε`; `t_{k+1}` is a trace committed at round
`k + 1` if there is one, and `t_k` otherwise. -/
noncomputable def committedChain : Nat → obj.Trace
  | 0 => obj.emptyTrace
  | k + 1 =>
    if h : ∃ t p, (e.round k).output p = some (t, true) then h.choose
    else committedChain k

omit spec [DecidableEq Op] in
theorem committedChain_zero : e.committedChain 0 = obj.emptyTrace := rfl

omit spec [DecidableEq Op] in
/-- Each `t_k` is `ε` or a trace committed at some round `j + 1 ≤ k`. -/
theorem committedChain_cases (k : Nat) :
    e.committedChain k = obj.emptyTrace ∨
      ∃ j p, j < k ∧ (e.round j).output p = some (e.committedChain k, true) := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    by_cases h : ∃ t p, (e.round k).output p = some (t, true)
    · have he : e.committedChain (k + 1) = h.choose := by
        simp [committedChain, h]
      obtain ⟨p, hp⟩ := h.choose_spec
      exact Or.inr ⟨k, p, Nat.lt_succ_self k, he ▸ hp⟩
    · have he : e.committedChain (k + 1) = e.committedChain k := by
        simp [committedChain, h]
      rw [he]
      rcases ih with h0 | ⟨j, p, hj, hp⟩
      · exact Or.inl h0
      · exact Or.inr ⟨j, p, Nat.lt_succ_of_lt hj, hp⟩

/-- By Adoption, the trace committed at round `k + 1` is `t_{k+1}`, whichever
process committed it. -/
theorem committedChain_commit {k : Nat} {p : P} {s : obj.Trace}
    (hs : (e.round k).output p = some (s, true)) : e.committedChain (k + 1) = s := by
  have h : ∃ t p, (e.round k).output p = some (t, true) := ⟨s, p, hs⟩
  have he : e.committedChain (k + 1) = h.choose := by
    simp [committedChain, h]
  obtain ⟨q, hq⟩ := h.choose_spec
  rw [he]
  exact (e.round k).committed_equal (spec k).adoption hq hs

/-- `t_{k+1} = t_k · s_k` for some `s_k`: by `lemma:prefix-rounds`, `t_k` is a
prefix of every output of a later round. -/
theorem committedChain_mono (k : Nat) :
    obj.TracePrefix (e.committedChain k) (e.committedChain (k + 1)) := by
  by_cases h : ∃ t p, (e.round k).output p = some (t, true)
  · obtain ⟨s, p, hs⟩ := h
    rw [e.committedChain_commit spec hs]
    rcases e.committedChain_cases k with h0 | ⟨j, q, hj, hq⟩
    · rw [h0]; exact obj.empty_tracePrefix s
    · exact e.commit_below_later_output spec (Nat.le_of_lt hj) hq hs
  · have he : e.committedChain (k + 1) = e.committedChain k := by
      simp [committedChain, h]
    rw [he]
    exact obj.tracePrefix_refl _

end RoundExecution
end ConflictFreedom.GCA
