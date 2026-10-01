import CFLeanProof.TraceCompatibility
import CFLeanProof.GCA

/-!
# Invariant (I): proposals built from pending commands are compatible

This module isolates the combinatorial core shared by the paper's proof of
Theorem `weakUCWCF` (Algorithm 1 is weakly conflict-free) and Lemma
`UCV2isCF` (Algorithm 3 is conflict-free).

Both proofs establish the same invariant: after the execution has become
conflict-free, for every round beyond a threshold, *only compatible traces are
proposed to the round's GCA object*.  The proposals have the shape
`t · u_i · cmd_i`, where `t` is the common prefix of the traces returned by the
previous round and every command occurring in `u_i`, together with `cmd_i`,
belongs to a still-pending operation.  Since no two pending operations conflict,
all of these commands pairwise commute, and the proposals are compatible.

The mathematical content is that a trace monoid restricted to an alphabet whose
*distinct* letters are independent is the free commutative monoid on that
alphabet: trace equivalence collapses to permutation.  Note that self-
independence is **not** assumed and does not hold in general (`Independent a a`
would force `a` to return the same response when run twice), so the statements
below are careful to require independence only for distinct commands.
-/

namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-- A set of commands is *nonconflicting* when distinct members commute.  This
is the paper's hypothesis "no two pending operations are conflicting"; it does
not, and must not, assert `Independent a a`. -/
def Nonconflicting (C : Op → Prop) : Prop :=
  ∀ a b, C a → C b → a ≠ b → obj.Independent a b

theorem nonconflicting_of_not_conflict {C : Op → Prop}
    (h : ∀ a b, C a → C b → a ≠ b → ¬ obj.Conflict a b) : obj.Nonconflicting C := by
  intro a b ha hb hab
  exact (obj.independent_iff_not_conflict a b).mpr (h a b ha hb hab)

/-- Over a nonconflicting alphabet, permutation implies trace equivalence.
Equal adjacent letters need no swap, so self-independence is never required. -/
theorem traceEq_of_perm_of_nonconflicting {C : Op → Prop} (hC : obj.Nonconflicting C) :
    ∀ {s t : List Op}, s.Perm t → (∀ a ∈ s, C a) → obj.TraceEq s t := by
  intro s t h
  induction h with
  | nil => exact fun _ => TraceEq.refl _
  | cons x _ ih =>
      intro hs
      have := obj.traceEq_append_left [x] (ih (fun a ha => hs a (List.mem_cons_of_mem x ha)))
      simpa using this
  | swap x y l =>
      intro hs
      by_cases hxy : y = x
      · subst hxy; exact TraceEq.refl _
      · have hy : C y := hs y (List.mem_cons_self ..)
        have hx : C x := hs x (List.mem_cons_of_mem y (List.mem_cons_self ..))
        simpa using TraceEq.swap [] l y x (hC y x hy hx hxy)
  | trans h₁ _ ih₁ ih₂ =>
      intro hs
      exact TraceEq.trans (ih₁ hs) (ih₂ (fun a ha => hs a (h₁.mem_iff.mpr ha)))

theorem traceAppend_mk (u v : List Op) :
    obj.traceAppend (Quotient.mk obj.traceSetoid u) (Quotient.mk obj.traceSetoid v)
      = Quotient.mk obj.traceSetoid (u ++ v) := rfl

/-- Concatenation of two words over a nonconflicting alphabet is commutative. -/
theorem traceAppend_comm_of_nonconflicting {C : Op → Prop} (hC : obj.Nonconflicting C)
    {u v : List Op} (hu : ∀ a ∈ u, C a) (hv : ∀ a ∈ v, C a) :
    (Quotient.mk obj.traceSetoid (u ++ v) : obj.Trace)
      = Quotient.mk obj.traceSetoid (v ++ u) := by
  refine Quotient.sound (obj.traceEq_of_perm_of_nonconflicting hC (List.perm_append_comm) ?_)
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hu a h
  · exact hv a h

/-- **Invariant (I), pairwise form.**  Two extensions of a common prefix by
pending commands are compatible; `t · u · v` is a common extension. -/
theorem pairCompatible_of_nonconflicting_extensions {C : Op → Prop}
    (hC : obj.Nonconflicting C) (t : obj.Trace) {u v : List Op}
    (hu : ∀ a ∈ u, C a) (hv : ∀ a ∈ v, C a) :
    obj.PairCompatible (obj.traceAppend t (Quotient.mk obj.traceSetoid u))
      (obj.traceAppend t (Quotient.mk obj.traceSetoid v)) := by
  refine ⟨obj.traceAppend t (Quotient.mk obj.traceSetoid (u ++ v)), ?_, ?_⟩
  · refine (obj.tracePrefix_iff_append _ _).mpr ⟨Quotient.mk obj.traceSetoid v, ?_⟩
    refine ((obj.traceAppend_assoc t (Quotient.mk obj.traceSetoid u)
      (Quotient.mk obj.traceSetoid v)).trans ?_).symm
    rw [obj.traceAppend_mk]
  · refine (obj.tracePrefix_iff_append _ _).mpr ⟨Quotient.mk obj.traceSetoid u, ?_⟩
    refine ((obj.traceAppend_assoc t (Quotient.mk obj.traceSetoid v)
      (Quotient.mk obj.traceSetoid u)).trans ?_).symm
    rw [obj.traceAppend_mk, ← obj.traceAppend_comm_of_nonconflicting hC hu hv]

variable [DecidableEq Op]

/-- **Invariant (I).**  A finite family of proposals, each obtained from the
common prefix `t` by appending pending commands, is compatible.  This is the
statement the paper feeds to the GCA Commitment property. -/
theorem compatible_of_nonconflicting_extensions {C : Op → Prop}
    (hC : obj.Nonconflicting C) (t : obj.Trace) (S : List obj.Trace)
    (hS : ∀ s ∈ S, ∃ u : List Op, (∀ a ∈ u, C a) ∧
      s = obj.traceAppend t (Quotient.mk obj.traceSetoid u)) :
    obj.Compatible (fun s => s ∈ S) := by
  refine obj.finite_pairwise_compatible S ?_
  intro s hs r hr
  obtain ⟨u, hu, rfl⟩ := hS s hs
  obtain ⟨v, hv, rfl⟩ := hS r hr
  exact obj.pairCompatible_of_nonconflicting_extensions hC t hu hv

omit [DecidableEq Op] in
/-- The shape actually produced by Algorithms 1 and 3 at lines 7–8: a process
either proposes the trace it retrieved from the previous round, or appends its
own still-pending command to it. -/
theorem proposal_has_pending_extension {C : Op → Prop} (t : obj.Trace)
    {u : List Op} (hu : ∀ a ∈ u, C a) {cmd : Op} (hcmd : C cmd) :
    ∃ w : List Op, (∀ a ∈ w, C a) ∧
      obj.traceAppend (obj.traceAppend t (Quotient.mk obj.traceSetoid u))
          (Quotient.mk obj.traceSetoid [cmd])
        = obj.traceAppend t (Quotient.mk obj.traceSetoid w) := by
  refine ⟨u ++ [cmd], ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hu a h
    · exact (List.mem_singleton.mp h) ▸ hcmd
  · refine (obj.traceAppend_assoc t (Quotient.mk obj.traceSetoid u)
      (Quotient.mk obj.traceSetoid [cmd])).trans ?_
    rw [obj.traceAppend_mk]

end ConflictFreedom.Object

namespace ConflictFreedom.GCA.History
open Object
variable {State Op Response : Type} {obj : Object State Op Response} [DecidableEq Op]
variable {Participant : Type} (h : History obj Participant)

/-- Occurrences are preserved by trace extension (Lemma `RetTracePrefix`). -/
theorem occurs_mono {a : Op} {k : Nat} {s t : obj.Trace}
    (hp : obj.TracePrefix s t) (ho : Occurs (obj := obj) a k s) :
    Occurs (obj := obj) a k t := by
  obtain ⟨suffix, hsuf⟩ := obj.traceResponses_prefix hp a obj.initial
  have : (obj.traceResponses a obj.initial s).length
      ≤ (obj.traceResponses a obj.initial t).length := by
    rw [hsuf, List.length_append]
    exact Nat.le_add_right _ _
  exact Nat.lt_of_lt_of_le ho this

/-- **Invariant (I) at a round.**  If every proposal to this GCA object extends
a common prefix `t` by still-pending, pairwise nonconflicting commands, then the
inputs are compatible.  `S` enumerates the (finitely many) proposals. -/
theorem inputs_compatible_of_pending_proposals {C : Op → Prop}
    (hC : obj.Nonconflicting C) (t : obj.Trace) (S : List obj.Trace)
    (hcover : ∀ s, h.Inputs s → s ∈ S)
    (hshape : ∀ s ∈ S, ∃ u : List Op, (∀ a ∈ u, C a) ∧
      s = obj.traceAppend t (Quotient.mk obj.traceSetoid u)) :
    obj.Compatible h.Inputs := by
  obtain ⟨w, hw⟩ := obj.compatible_of_nonconflicting_extensions hC t S hshape
  exact ⟨w, fun s hs => hw s (hcover s hs)⟩

/-- The paper's contradiction step in Theorem `weakUCWCF` and Lemma `UCV2isCF`:
once the execution is conflict-free, invariant (I) makes the proposals to the
next round compatible, so Commitment yields a participant whose own proposal is
a prefix of a committed output.  Every occurrence it proposed -- in particular
its own pending command -- occurs in that committed trace, so it leaves the
loop and its operation completes. -/
theorem exists_commit_of_pending_proposals {C : Op → Prop}
    (hC : obj.Nonconflicting C) (t : obj.Trace) (S : List obj.Trace)
    (hcover : ∀ s, h.Inputs s → s ∈ S)
    (hshape : ∀ s ∈ S, ∃ u : List Op, (∀ a ∈ u, C a) ∧
      s = obj.traceAppend t (Quotient.mk obj.traceSetoid u))
    (hcomm : h.Commitment) (hne : ∃ s, h.Inputs s) (hret : h.AllReturned) :
    ∃ p s c, h.input p = some s ∧ h.output p = some (c, true) ∧ obj.TracePrefix s c ∧
      ∀ a k, Occurs (obj := obj) a k s → Occurs (obj := obj) a k c := by
  obtain ⟨p, s, c, hin, hout, hpre⟩ :=
    hcomm hne (h.inputs_compatible_of_pending_proposals hC t S hcover hshape) hret
  exact ⟨p, s, c, hin, hout, hpre, fun _ _ ho => occurs_mono hpre ho⟩

end ConflictFreedom.GCA.History
