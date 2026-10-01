import CFLeanProof.TraceAlgebra

/-! The six GCA requirements, with partial participation and partial returns.
This is a specification, not a correctness proof for Algorithm 2. No existence
of lattice bounds or correct implementation is assumed. -/

namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response) [DecidableEq Op]

/-! ## Multisets of operations

main.tex §4.1: "Let `ops(s)` denote the multiset over `O` defined by `s`."  A
multiset over `O` is its multiplicity function `O → ℕ`; its union is the usual
one, whose multiplicity is the maximum. -/

/-- `ops(s)`: the multiset of operations of the trace `s` — how many times each
operation occurs in it. -/
def ops (s : obj.Trace) (a : Op) : Nat := obj.traceCount a s

/-- **Inclusion in a union of multisets**, `m ⊆ ⋃_{s ∈ S} ops(s)`, for the usual
multiset union: the multiplicity of an operation in the union is its **maximum**
multiplicity over the family, so the inclusion says that every operation occurs
in `m` at most as many times as in some member of the family — and not at all if
it occurs in none.  (Stated without writing the maximum, so the family may be
infinite; for a finite family it is `m a ≤ maxOps L a`,
`subsetUnion_iff_le_maxOps`.) -/
def SubsetUnion (m : Op → Nat) (S : obj.Trace → Prop) : Prop :=
  ∀ a, 0 < m a → ∃ s, S s ∧ m a ≤ obj.ops s a

/-- The multiplicity of `a` in the union `⋃_{s ∈ L} ops(s)` of a finite family:
its maximum multiplicity in the members. -/
def maxOps (L : List obj.Trace) (a : Op) : Nat := (L.map (obj.ops · a)).foldr max 0

theorem le_maxOps {L : List obj.Trace} {s : obj.Trace} (hs : s ∈ L) (a : Op) :
    obj.ops s a ≤ obj.maxOps L a := by
  induction L with
  | nil => cases hs
  | cons u L ih =>
      unfold maxOps
      rw [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hs) (Nat.le_max_right _ _)

theorem exists_eq_maxOps {L : List obj.Trace} {a : Op} (h : 0 < obj.maxOps L a) :
    ∃ s ∈ L, obj.ops s a = obj.maxOps L a := by
  induction L with
  | nil => simp [maxOps] at h
  | cons u L ih =>
      have hdef : obj.maxOps (u :: L) a = max (obj.ops u a) (obj.maxOps L a) := by
        unfold maxOps; rw [List.map_cons, List.foldr_cons]
      rw [hdef] at h ⊢
      by_cases hle : obj.maxOps L a ≤ obj.ops u a
      · exact ⟨u, List.mem_cons_self .., (Nat.max_eq_left hle).symm⟩
      · have hlt : obj.ops u a < obj.maxOps L a := Nat.lt_of_not_le hle
        obtain ⟨s, hs, heq⟩ := ih (by omega)
        exact ⟨s, List.mem_cons_of_mem _ hs, by rw [heq, Nat.max_eq_right (Nat.le_of_lt hlt)]⟩

/-- **For a finite family, inclusion in the union is bounded by the maximum**:
`m ⊆ ⋃_{s ∈ L} ops(s)` iff `m a ≤ max_{s ∈ L} ops(s)(a)` for every `a`. -/
theorem subsetUnion_iff_le_maxOps (m : Op → Nat) (L : List obj.Trace) :
    obj.SubsetUnion m (· ∈ L) ↔ ∀ a, m a ≤ obj.maxOps L a := by
  constructor
  · intro h a
    rcases Nat.eq_zero_or_pos (m a) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨s, hs, hle⟩ := h a hpos
      exact Nat.le_trans hle (obj.le_maxOps hs a)
  · intro h a hpos
    obtain ⟨s, hs, heq⟩ := obj.exists_eq_maxOps (Nat.lt_of_lt_of_le hpos (h a))
    exact ⟨s, hs, heq ▸ h a⟩

theorem subsetUnion_congr {m : Op → Nat} {S S' : obj.Trace → Prop} (hS : ∀ s, S s ↔ S' s) :
    obj.SubsetUnion m S ↔ obj.SubsetUnion m S' :=
  ⟨fun h a ha => by obtain ⟨s, hs, hle⟩ := h a ha; exact ⟨s, (hS s).mp hs, hle⟩,
    fun h a ha => by obtain ⟨s, hs, hle⟩ := h a ha; exact ⟨s, (hS s).mpr hs, hle⟩⟩

end ConflictFreedom.Object

namespace ConflictFreedom.GCA
open Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-- One GCA instance: each participant's input, and — once its call has
returned — its output, a trace it commits (`true`) or adopts (`false`).  Only
participants return. -/
structure History (Participant : Type) where
  input : Participant → Option obj.Trace
  output : Participant → Option (obj.Trace × Bool)
  returned_invoked : ∀ p t c, output p = some (t, c) → ∃ s, input p = some s

namespace History
variable {obj} {Participant : Type} (h : History obj Participant)

/-- `s` is some participant's input. -/
def Inputs (s : obj.Trace) : Prop := ∃ p, h.input p = some s

/-- `t` is some returned participant's output trace. -/
def Outputs (t : obj.Trace) : Prop := ∃ p c, h.output p = some (t, c)

/-- Every participant's call has returned (`P = P_r`). -/
def AllReturned : Prop := ∀ p s, h.input p = some s → ∃ t c, h.output p = some (t, c)

/-- Operation occurrences are indexed by their number among equal operations:
`Occurs a k t` says `t` has a `k`-th occurrence of `a` (counting from `0`). -/
def Occurs [DecidableEq Op] (a : Op) (k : Nat) (t : obj.Trace) : Prop :=
  k < (obj.traceResponses a obj.initial t).length

theorem occurs_iff_lt_ops [DecidableEq Op] {a : Op} {k : Nat} {t : obj.Trace} :
    Occurs (obj := obj) a k t ↔ k < obj.ops t a := by
  unfold Occurs Object.ops
  rw [obj.traceResponses_length]

/-- **Validity.**  Output traces contain only input operations — main.tex:
`∀ i ∈ P_r, ops(t_i) ⊆ ⋃_{j ∈ P} ops(s_j)`, with `ops(s)` the multiset of
operations of `s` (§4.1) and `⋃` the usual multiset union, whose multiplicity is
the maximum (`Object.SubsetUnion`): every operation occurs in an output trace at
most as many times as in some input trace.

Two equivalent readings are proved: with finitely many participants, the union's
multiplicity is literally the maximum over the inputs (`validity_iff_le_maxOps`,
`validity_iff_le_maxOps_fin`); occurrence by occurrence, the `k`-th occurrence of
`a` in an output is matched by a `k`-th occurrence of `a` in some input
(`validity_iff_occurs`), which is the form the proofs use (`Validity.occurs`,
`Validity.of_occurs`).

Here it is a condition on one history.  The manuscript requires Validity of
every execution, hence of every finite prefix, which also forbids an output to
contain an input proposed after the output is returned.  Applied to a whole-run
table only, that prefix instance is lost; the universal constructions use its
consequence `Execution.CausalGCA` (`CausalLinearization`,
`causalGCA_of_prefixValidity`), and Algorithm 3 needs it (`NonCausalWitness`). -/
def Validity [DecidableEq Op] : Prop :=
  ∀ p t c, h.output p = some (t, c) → obj.SubsetUnion (obj.ops t) h.Inputs

/-- **Validity, occurrence by occurrence**: the `k`-th occurrence of `a` in an
output is matched by a `k`-th occurrence of `a` in some input. -/
theorem validity_iff_occurs [DecidableEq Op] :
    h.Validity ↔ ∀ p t c, h.output p = some (t, c) → ∀ a k, Occurs a k t →
      ∃ s, h.Inputs s ∧ Occurs a k s := by
  constructor
  · intro hv p t c hp a k hk
    rw [occurs_iff_lt_ops] at hk
    obtain ⟨s, hs, hle⟩ := hv p t c hp a (by omega)
    exact ⟨s, hs, occurs_iff_lt_ops.mpr (by omega)⟩
  · intro ho p t c hp a hpos
    obtain ⟨s, hs, hk⟩ := ho p t c hp a (obj.ops t a - 1) (occurs_iff_lt_ops.mpr (by omega))
    rw [occurs_iff_lt_ops] at hk
    exact ⟨s, hs, by omega⟩

variable {h} in
theorem Validity.occurs [DecidableEq Op] (hv : h.Validity) :
    ∀ p t c, h.output p = some (t, c) → ∀ a k, Occurs a k t → ∃ s, h.Inputs s ∧ Occurs a k s :=
  (validity_iff_occurs h).mp hv

variable {h} in
theorem Validity.of_occurs [DecidableEq Op]
    (ho : ∀ p t c, h.output p = some (t, c) → ∀ a k, Occurs a k t →
      ∃ s, h.Inputs s ∧ Occurs a k s) : h.Validity :=
  (validity_iff_occurs h).mpr ho

/-- **Validity with the maximum written out**, for finitely many participants —
every participant is in the list `L`: each operation's multiplicity in an output
is at most its maximum multiplicity over the inputs,
`ops(t_i)(a) ≤ max_{j ∈ P} ops(s_j)(a)`. -/
theorem validity_iff_le_maxOps [DecidableEq Op] (L : List Participant)
    (hL : ∀ p s, h.input p = some s → p ∈ L) :
    h.Validity ↔ ∀ p t c, h.output p = some (t, c) →
      ∀ a, obj.ops t a ≤ obj.maxOps (L.filterMap h.input) a := by
  have hmem : ∀ s, h.Inputs s ↔ s ∈ L.filterMap h.input := by
    intro s
    rw [List.mem_filterMap]
    exact ⟨fun ⟨p, hp⟩ => ⟨p, hL p s hp, hp⟩, fun ⟨p, _, hp⟩ => ⟨p, hp⟩⟩
  constructor
  · intro hv p t c hp
    exact (obj.subsetUnion_iff_le_maxOps _ _).mp ((obj.subsetUnion_congr hmem).mp (hv p t c hp))
  · intro hle p t c hp
    exact (obj.subsetUnion_congr hmem).mpr ((obj.subsetUnion_iff_le_maxOps _ _).mpr (hle p t c hp))

omit h in
/-- **Validity for `n` processes**, the participants of every GCA object of the
universal constructions, with the maximum over the participants' inputs written
out: `ops(t_i)(a) ≤ max_{j ∈ P} ops(s_j)(a)`. -/
theorem validity_iff_le_maxOps_fin [DecidableEq Op] {n : Nat} (h' : History obj (Fin n)) :
    h'.Validity ↔ ∀ p t c, h'.output p = some (t, c) →
      ∀ a, obj.ops t a ≤ obj.maxOps ((List.finRange n).filterMap h'.input) a :=
  h'.validity_iff_le_maxOps (List.finRange n) (fun p _ _ => List.mem_finRange p)

/-- **Adoption.**  A committed trace is extended by every output trace. -/
def Adoption : Prop :=
  ∀ p t, h.output p = some (t, true) →
    ∀ q u c, h.output q = some (u, c) → obj.TracePrefix t u

/-- **Commitment without `P ≠ ∅`**:
`comp(⋃_{i∈P}{s_i}) ∧ P = P_r ⟹ ∃ j ∈ P_r, (s_j ≤ t_j) ∧ (c_j = True)`.
It is **not** the manuscript's Commitment, which is guarded by `P ≠ ∅`
(`Commitment`, below), and nothing could meet it: when nobody participates its
premises hold and nobody can commit
(`not_unguardedCommitment_of_no_participant`), so it fails in the execution of
every GCA object before its first call.  It records why the guard is needed. -/
def UnguardedCommitment : Prop :=
  obj.Compatible h.Inputs → h.AllReturned →
    ∃ p s t, h.input p = some s ∧ h.output p = some (t, true) ∧ obj.TracePrefix s t

/-- **Commitment**, as main.tex states it:
`comp(⋃_{i∈P}{s_i}) ∧ (P = P_r ≠ ∅) ⟹ ∃ j ∈ P_r, (s_j ≤ t_j) ∧ (c_j = True)`,
with `P ≠ ∅` read `∃ s, h.Inputs s` and `P = P_r` read `AllReturned`: if some
process participates, the inputs are compatible and every call returns, then
some participant commits an extension of its input. -/
def Commitment : Prop :=
  (∃ s, h.Inputs s) → h.UnguardedCommitment

/-- **Without `P ≠ ∅` the implication fails whenever nobody participates**: the
inputs are then vacuously compatible and all returned, and nobody can commit. -/
theorem not_unguardedCommitment_of_no_participant (hno : ∀ p, h.input p = none) :
    ¬ h.UnguardedCommitment := by
  intro hc
  obtain ⟨p, s, -, hs, -, -⟩ := hc
    ⟨obj.emptyTrace, fun _ ⟨q, hq⟩ => by rw [hno q] at hq; cases hq⟩
    (fun q _ hq => by rw [hno q] at hq; cases hq)
  rw [hno p] at hs
  cases hs

/-- **Convergence.**  Output traces are mutually compatible. -/
def Convergence : Prop := obj.Compatible h.Outputs

/-- **Common Prefix.**  Output traces preserve the common prefix of the inputs,
stated for every common lower bound: when a GLB exists this is equivalent to
preserving that GLB, without postulating an unconstructed lattice operation. -/
def CommonPrefix : Prop :=
  ∀ l, (∀ s, h.Inputs s → obj.TracePrefix l s) →
    ∀ t, h.Outputs t → obj.TracePrefix l t

/-- **Weak Agreement.**  If all input traces are equal, no process adopts. -/
def WeakAgreement : Prop :=
  (∀ s t, h.Inputs s → h.Inputs t → s = t) →
    ∀ p t c, h.output p = some (t, c) → c = true

/-- The manuscript's six GCA properties, on one history. -/
structure Specification [DecidableEq Op] : Prop where
  validity : h.Validity
  adoption : h.Adoption
  commitment : h.Commitment
  convergence : h.Convergence
  commonPrefix : h.CommonPrefix
  weakAgreement : h.WeakAgreement

/-- Adoption implies agreement of all committed traces. -/
theorem committed_equal (ha : h.Adoption) {p q : Participant} {s t : obj.Trace}
    (hp : h.output p = some (s, true)) (hq : h.output q = some (t, true)) : s = t :=
  obj.tracePrefix_antisymm (ha p s hp q t true hq) (ha q t hq p s true hp)

theorem commonPrefix_iff_glb {g : obj.Trace} (hg : obj.IsGLB h.Inputs g) :
    h.CommonPrefix ↔ ∀ t, h.Outputs t → obj.TracePrefix g t := by
  constructor
  · exact fun hc => hc g hg.1
  · intro hc l hl t ht
    exact obj.tracePrefix_trans (hg.2 l hl) (hc t ht)

end History

/-- The history with no process at all. -/
def emptyHistory : History obj Empty where
  input := fun p => nomatch p
  output := fun p => nomatch p
  returned_invoked := fun p => nomatch p

/-- On it the formula without `P ≠ ∅` fails… -/
theorem emptyHistory_not_unguardedCommitment : ¬ (emptyHistory obj).UnguardedCommitment :=
  (emptyHistory obj).not_unguardedCommitment_of_no_participant (fun p => nomatch p)

/-- …and the manuscript's Commitment holds, vacuously. -/
theorem emptyHistory_commitment : (emptyHistory obj).Commitment := by
  rintro ⟨s, p, hp⟩
  exact nomatch p

end ConflictFreedom.GCA
