import CFLeanProof.Linearization

/-! The finite-history argument of `theorem:weakUCLin`, as the manuscript
builds it: from the chain `t_0 ≤ t_1 ≤ ⋯` of traces committed at successive
rounds (`roundChain_linearizes`). Operations here are unique invocation
identities (instantiate `Op` with `Command`), not operation names. A completion
retains all returned operations and precisely those pending operations present
in the chosen representative. The sequential responses are computed by the
object, and real-time order is checked on the actual history.
-/
namespace ConflictFreedom

/-- History observations at configuration boundaries. `returned k a v` means
that the response `v` of invocation identity `a` is visible by boundary `k`. -/
structure FiniteHistory (Op Response : Type) where
  invoked : Nat → Op → Prop
  returned : Nat → Op → Response → Prop

namespace Object
variable {State Op Response : Type} (obj : Object State Op Response) [DecidableEq Op]

/-- Execute a schedule from the initial state, retaining identities and values. -/
def sequentialHistory (x : List Op) : List (Op × Response) :=
  x.mapIdx fun p a =>
    (a, (obj.step a (obj.finalState (x.take p) obj.initial)).1)

/-- The sequential response of an identity at its first position. -/
def sequentialResponse (x : List Op) (a : Op) : Response :=
  (obj.step a (obj.finalState (x.take (x.idxOf a)) obj.initial)).1

private theorem count_take_idxOf (x : List Op) (a : Op) :
    (x.take (x.idxOf a)).count a = 0 := by
  induction x with
  | nil => simp
  | cons b x ih =>
    by_cases h : b = a
    · subst b; simp
    · simp [List.idxOf_cons, h, List.take_succ_cons, ih]

theorem traceReturn_first_position {t : obj.Trace} {x : List Op}
    (hx : Quotient.mk obj.traceSetoid x = t) {a : Op} (ha : a ∈ x) :
    obj.traceReturn a 0 t = some (obj.sequentialResponse x a) := by
  have h := obj.traceReturn_of_representative hx a (x.idxOf a)
    (List.idxOf_lt_length_of_mem ha) (List.getElem_idxOf (List.idxOf_lt_length_of_mem ha))
  simpa [count_take_idxOf, sequentialResponse] using h

/-- A legal completion in command form. Its events are the alternating
invocation/response pairs obtained by executing `x` from `obj.initial`.
Every completed invocation retains its value; omitted invocations are pending.
The last field preserves response-before-invocation order, including retained
pending invocations as the second operation. -/
structure Linearizes (H : FiniteHistory Op Response) (N : Nat) (x : List Op) : Prop where
  unique : x.Nodup
  invoked : ∀ a ∈ x, H.invoked N a
  completed : ∀ a v, H.returned N a v → a ∈ x ∧ obj.sequentialResponse x a = v
  realTime : ∀ a b, a ∈ x → b ∈ x →
    (∃ k, k ≤ N ∧ (∃ v, H.returned k a v) ∧ ¬ H.invoked k b) →
    x.idxOf a < x.idxOf b

omit [DecidableEq Op] in
/-- The concrete alternating history contains exactly the chosen commands. -/
theorem sequentialHistory_commands (x : List Op) :
    (obj.sequentialHistory x).map Prod.fst = x := by
  apply List.ext_getElem
  · simp [sequentialHistory]
  · intro i hi hj
    simp [sequentialHistory]

/-- With unique identities, the response in the sequential event list is the
response at that identity's sole position. -/
theorem mem_sequentialHistory {x : List Op} (hx : x.Nodup) (a : Op) (v : Response) :
    (a, v) ∈ obj.sequentialHistory x ↔ a ∈ x ∧ obj.sequentialResponse x a = v := by
  constructor
  · intro h
    obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp h
    have ha : x[i] = a := congrArg Prod.fst he
    have hv := congrArg Prod.snd he
    refine ⟨ha ▸ List.getElem_mem hi, ?_⟩
    dsimp at hv
    rw [← ha, sequentialResponse, hx.idxOf_getElem i hi]
    exact hv
  · intro ⟨ha, hv⟩
    apply List.mem_mapIdx.mpr
    refine ⟨x.idxOf a, List.idxOf_lt_length_of_mem ha, ?_⟩
    simp only [List.getElem_idxOf]
    exact Prod.ext rfl hv

/-- Explicit completion: all observed responses are retained, and any newly
supplied response belongs to an invoked, still pending command. -/
theorem Linearizes.completion {H : FiniteHistory Op Response} {N : Nat} {x : List Op}
    (h : obj.Linearizes H N x) :
    (∀ a v, H.returned N a v → (a, v) ∈ obj.sequentialHistory x) ∧
    (∀ a v, (a, v) ∈ obj.sequentialHistory x →
      H.invoked N a ∧ (H.returned N a v ∨ ¬ ∃ w, H.returned N a w)) ∧
    (∀ a, H.invoked N a → a ∉ x → ¬ ∃ v, H.returned N a v) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a v hr
    exact (obj.mem_sequentialHistory h.unique a v).mpr (h.completed a v hr)
  · intro a v hv
    obtain ⟨ha, he⟩ := (obj.mem_sequentialHistory h.unique a v).mp hv
    refine ⟨h.invoked a ha, ?_⟩
    by_cases hr : ∃ w, H.returned N a w
    · obtain ⟨w, hw⟩ := hr
      have heq := (h.completed a w hw).2
      have : v = w := he.symm.trans heq
      exact Or.inl (this.symm ▸ hw)
    · exact Or.inr hr
  · intro a _ ha ⟨v, hv⟩
    exact ha (h.completed a v hv).1

omit [DecidableEq Op] in
/-- `t_k ≤ t_m` for `k ≤ m` along a chain of traces. -/
theorem chain_prefix_le (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) {k m : Nat} (h : k ≤ m) :
    obj.TracePrefix (t k) (t m) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact obj.tracePrefix_refl _
  | succ d ih => exact obj.tracePrefix_trans (ih (Nat.le_add_right _ _)) (hmono (k + d))

/-- **The proof of `theorem:weakUCLin`.**  `t_k` is the trace committed at round
`k` (`t_0 = ε`, `t_{k+1} = t_k · s_k`), and `r* N` the last round of the history
observed at boundary `N`.  The representative is `t̂ = ŝ_1 ⋯ ŝ_{r*}`, the
concatenation of representatives of the blocks `s_k` (`chainRep`), and
`S_t̂` executes it from the initial state.

Every operation that returns by boundary `j` is associated with a round
`k ≤ r* j`: its command is in `t_k`, its response is `ret*(cmd, t_k)`, and — the
real-time step — `t_k` contains only commands invoked by `j`.  Then:

* a completed operation keeps its response in `t_{r*}`, which extends `t_k`
  (`lemma:ret-trace-prefix`);
* if `Φ₁` returns at `j` before `Φ₂` is invoked, `cmd(Φ₁)` is in the block
  prefix `ŝ_1 ⋯ ŝ_k` of `t̂` and `cmd(Φ₂)` is not, so `cmd(Φ₁)` precedes
  `cmd(Φ₂)` in `t̂`;
* the pending operations kept are those whose command is in `t_{r*}`.

Because `r*` only grows, the representatives at successive boundaries are
literal prefixes of one another: one order linearizes the whole history. -/
theorem roundChain_linearizes (H : FiniteHistory Op Response)
    (t : Nat → obj.Trace) (h0 : t 0 = obj.emptyTrace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1)))
    (rstar : Nat → Nat) (hrstar : ∀ N, rstar N ≤ rstar (N + 1))
    (hunique : ∀ k a, obj.traceCount a (t k) ≤ 1)
    (hinvoked : ∀ N a, 0 < obj.traceCount a (t (rstar N)) → H.invoked N a)
    (hassoc : ∀ j a v, H.returned j a v → ∃ k, k ≤ rstar j ∧
      0 < obj.traceCount a (t k) ∧ obj.traceReturn a 0 (t k) = some v ∧
      ∀ b, 0 < obj.traceCount b (t k) → H.invoked j b) :
    (∀ N, obj.Linearizes H N (obj.chainRep t hmono (rstar N))) ∧
      (∀ k m, k ≤ m →
        ∃ z, obj.chainRep t hmono (rstar m) = obj.chainRep t hmono (rstar k) ++ z) := by
  have hrle : ∀ {j N}, j ≤ N → rstar j ≤ rstar N := by
    intro j N h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih => exact Nat.le_trans (ih (Nat.le_add_right _ _)) (hrstar (j + d))
  refine ⟨fun N => ?_, fun k m h => obj.chainRep_le t hmono (hrle h)⟩
  have hx := obj.chainRep_mk t hmono h0 (rstar N)
  have hcount (a : Op) : obj.traceCount a (t (rstar N)) =
      (obj.chainRep t hmono (rstar N)).count a := by rw [← hx]; rfl
  constructor
  · exact List.nodup_iff_count.mpr (fun a => by simpa [hcount] using hunique (rstar N) a)
  · intro a ha
    exact hinvoked N a (by simpa [hcount] using List.count_pos_iff.mpr ha)
  · intro a v hr
    obtain ⟨k, hk, hpos, hv, -⟩ := hassoc N a v hr
    have hp := obj.chain_prefix_le t hmono hk
    have ha : a ∈ obj.chainRep t hmono (rstar N) := List.count_pos_iff.mp (by
      simpa [hcount] using Nat.lt_of_lt_of_le hpos (obj.traceCount_mono hp a))
    refine ⟨ha, Option.some.inj ?_⟩
    rw [← obj.traceReturn_first_position hx ha, ← obj.traceReturn_prefix hp a 0 (by
      simpa only [obj.traceResponses_length] using hpos)]
    exact hv
  · intro a b _ _ ⟨j, hj, ⟨v, hv⟩, hnot⟩
    obtain ⟨k, hk, hpos, -, hprov⟩ := hassoc j a v hv
    have hkN : k ≤ rstar N := Nat.le_trans hk (hrle hj)
    have htake := obj.chainRep_take t hmono h0 hkN
    have hc (c : Op) : obj.traceCount c (t k) =
        ((obj.chainRep t hmono (rstar N)).take (obj.traceLength (t k))).count c := by
      rw [htake, ← obj.chainRep_mk t hmono h0 k]; rfl
    have ha : a ∈ (obj.chainRep t hmono (rstar N)).take (obj.traceLength (t k)) :=
      List.count_pos_iff.mp (by simpa [hc] using hpos)
    have hb : b ∉ (obj.chainRep t hmono (rstar N)).take (obj.traceLength (t k)) := by
      intro hb
      exact hnot (hprov b (by simpa [hc] using List.count_pos_iff.mpr hb))
    have hsplit := List.take_append_drop (obj.traceLength (t k)) (obj.chainRep t hmono (rstar N))
    have haidx := List.idxOf_lt_length_of_mem ha
    conv => lhs; rw [← hsplit, List.idxOf_append, ite_eq_left ha]
    conv => rhs; rw [← hsplit, List.idxOf_append, ite_eq_right hb]
    omega

/-! ### What coherence buys

A coherent chain is one linear order, presented by its finite prefixes: the
position an operation is given at one boundary is the position it keeps at every
later boundary. -/

omit [DecidableEq Op] in
theorem chain_mem_mono {x : Nat → List Op}
    (hmono : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z)
    {k m : Nat} (h : k ≤ m) {a : Op} (ha : a ∈ x k) : a ∈ x m := by
  obtain ⟨z, hz⟩ := hmono k m h
  rw [hz]; exact List.mem_append_left _ ha

/-- **The order never changes.**  An operation placed at a position by boundary
`k` is at that same position at every later boundary. -/
theorem chain_idxOf_stable {x : Nat → List Op}
    (hmono : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z)
    {k m : Nat} (h : k ≤ m) {a : Op} (ha : a ∈ x k) :
    (x m).idxOf a = (x k).idxOf a := by
  obtain ⟨z, hz⟩ := hmono k m h
  rw [hz, List.idxOf_append, ite_eq_left ha]

/-- Consequently the relative order of any two operations is fixed once both
appear. -/
theorem chain_order_stable {x : Nat → List Op}
    (hmono : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z)
    {k m : Nat} (h : k ≤ m) {a b : Op} (ha : a ∈ x k) (hb : b ∈ x k) :
    ((x m).idxOf a < (x m).idxOf b ↔ (x k).idxOf a < (x k).idxOf b) := by
  rw [chain_idxOf_stable hmono h ha, chain_idxOf_stable hmono h hb]

end Object
end ConflictFreedom
