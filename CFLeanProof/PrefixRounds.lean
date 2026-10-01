import CFLeanProof.GlobalSchedule

/-!
# Lemma `lemma:prefix-rounds`, for both universal constructions

> **Lemma (`lemma:prefix-rounds`).**  Fix an execution of Algorithm 1 or
> Algorithm 3.  If `(s, True)` is returned by `GCA_r.propose(·)` for some round
> `r ≥ 1`, then for every round `r' ≥ r`, every trace `t` returned by
> `GCA_{r'}.propose(·)` satisfies `s ≤ t`.

The lemma is proved once, for any sequence of GCA histories in which every
proposal to round `r' + 1` extends an output of round `r'`
(`GCA.RoundExecution.commit_below_later_output`): the base case is Adoption, the
step is Common Prefix, exactly as in the manuscript's induction.  That
predecessor property is the manuscript's case analysis on the constructions — a
proposal extends a trace its proposer returned from `GCA_{r'}` or read, with
round `r'`, from `S` (Lines 4 and 7–8 of Algorithm 1, Lines 6 and 10–11 of
Algorithm 3) — and each construction establishes it from its own transitions,
as the `calls` field of its invariant (`WeakUniversal.invariant`,
`HelpingUniversal.invariant`).  This gives the lemma for each construction,
`WeakUniversal.committed_prefix` and `HelpingUniversal.committed_prefix`.

Stated over a whole GCA environment, those two carry the coverage hypothesis
"every input is a proposal of the run".  In an execution it is derived
(`WeakRun.callsCovered`, `HelpingRun.callsCovered`), so the lemma holds for every
execution of either construction over **any** GCA objects satisfying the six
properties (`WeakRun.prefix_rounds`, `HelpingRun.prefix_rounds`), and with no
hypothesis at all over Algorithm 2 (`Weak.prefix_rounds`, `Helping.prefix_rounds`).
They apply in particular to the algorithms run as machines
(`WeakUniversal.Forward.fsched`, `HelpingUniversal.Forward.fsched`), whose
executions are global schedules.

Rounds are the manuscript's: `H r` (for Algorithm 2, `f.environment obj r`) is
`GCA_r`, and round `0` is never called.
-/

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {f : Family (n := n) obj}

/-- **Lemma `lemma:prefix-rounds`, for an execution of Algorithm 1.** -/
theorem Weak.prefix_rounds (g : Weak obj f) {r r' : Nat} (hr : 1 ≤ r) (hrr : r ≤ r')
    {p q : Fin n} {s t : (WeakUniversal.Tagged (n := n) obj).Trace} {c : Bool}
    (hs : (f.environment obj r).output p = some (s, true))
    (ht : (f.environment obj r').output q = some (t, c)) :
    (WeakUniversal.Tagged obj).TracePrefix s t := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', r' = k' + 1 := ⟨r' - 1, by omega⟩
  exact WeakUniversal.committed_prefix obj g.callsCovered (f.specifications obj)
    (by omega) hs ht

/-- **Lemma `lemma:prefix-rounds`, for an execution of Algorithm 3.**  The same
statement; the predecessor property now also covers proposals built from
another process's published trace. -/
theorem Helping.prefix_rounds (g : Helping obj f) {r r' : Nat} (hr : 1 ≤ r) (hrr : r ≤ r')
    {p q : Fin n} {s t : (WeakUniversal.Tagged (n := n) obj).Trace} {c : Bool}
    (hs : (f.environment obj r).output p = some (s, true))
    (ht : (f.environment obj r').output q = some (t, c)) :
    (WeakUniversal.Tagged obj).TracePrefix s t := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', r' = k' + 1 := ⟨r' - 1, by omega⟩
  exact HelpingUniversal.committed_prefix obj g.callsCovered (f.specifications obj)
    (by omega) hs ht

/-- **Lemma `lemma:prefix-rounds`, for an execution of Algorithm 1 over any GCA
objects meeting the six properties** — the interface's `spec`, and nothing else. -/
theorem WeakRun.prefix_rounds {H : WeakUniversal.Environment (n := n) obj} (g : WeakRun obj H)
    (hspec : ∀ r, (H (r + 1)).Specification) {r r' : Nat} (hr : 1 ≤ r) (hrr : r ≤ r')
    {p q : Fin n} {s t : (WeakUniversal.Tagged (n := n) obj).Trace} {c : Bool}
    (hs : (H r).output p = some (s, true)) (ht : (H r').output q = some (t, c)) :
    (WeakUniversal.Tagged obj).TracePrefix s t := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', r' = k' + 1 := ⟨r' - 1, by omega⟩
  exact WeakUniversal.committed_prefix obj g.callsCovered hspec (by omega) hs ht

/-- **Lemma `lemma:prefix-rounds`, for an execution of Algorithm 3 over any GCA
objects meeting the six properties.** -/
theorem HelpingRun.prefix_rounds {H : WeakUniversal.Environment (n := n) obj}
    (g : HelpingRun obj H) (hspec : ∀ r, (H (r + 1)).Specification) {r r' : Nat}
    (hr : 1 ≤ r) (hrr : r ≤ r')
    {p q : Fin n} {s t : (WeakUniversal.Tagged (n := n) obj).Trace} {c : Bool}
    (hs : (H r).output p = some (s, true)) (ht : (H r').output q = some (t, c)) :
    (WeakUniversal.Tagged obj).TracePrefix s t := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', r' = k' + 1 := ⟨r' - 1, by omega⟩
  exact HelpingUniversal.committed_prefix obj g.callsCovered hspec (by omega) hs ht

end ConflictFreedom.GlobalSchedule
