import CFLeanProof.FiniteLinearization
import CFLeanProof.UniversalFiniteHistory
import CFLeanProof.HelpingConflictFreedom

/-! Finite linearizations for both universal constructions, conditional only on
chronological occurrence provenance in addition to their GCA contracts.
`ReturnsInvokedBy` is deliberately explicit: the abstract environment
contains whole-run outputs and does not itself enforce their availability at
receive time. Ordinary (untimed) occurrence provenance does not discharge this
obligation. It follows from the GCA causal contract
(`Execution.returnsInvokedBy_of_causalGCA`, in `CausalLinearization`) — the
manuscript's Validity on every prefix of the run — which the composed
Algorithm 2 meets; for Algorithm 1 it also follows from the whole-run properties
alone once the GCA history is the run's own (`returnsInvokedBy_of_covers`), and
for Algorithm 3 it does not (`NonCausalWitness`).
-/
namespace ConflictFreedom

namespace InvocationLedger.Run
variable {P Op : Type} [DecidableEq P]

/-- Process sequence order in a finite ledger is real-time order: the earlier
operation has returned at a boundary where the later one is not yet invoked. -/
theorem sequence_precedes (e : Run P Op) {N : Nat} {a b : Command P Op}
    (ha : a ∈ (e.state N).invoked) (hb : b ∈ (e.state N).invoked)
    (hp : a.process = b.process) (hs : a.sequence < b.sequence) :
    ∃ k, k ≤ N ∧ a ∈ (e.state k).returned ∧ b ∉ (e.state k).invoked := by
  induction N with
  | zero => rw [e.initial_state] at ha; cases ha
  | succ N ih =>
    have lift (ha : a ∈ (e.state N).invoked) (hb : b ∈ (e.state N).invoked) :
        ∃ k, k ≤ N + 1 ∧ a ∈ (e.state k).returned ∧ b ∉ (e.state k).invoked := by
      obtain ⟨k, hk, hr, hn⟩ := ih ha hb
      exact ⟨k, by omega, hr, hn⟩
    rcases e.next N with he | ⟨p, op, hidle, he⟩ | ⟨p, cmd, _, he⟩
    · exact lift (he ▸ ha) (he ▸ hb)
    · rw [he] at ha hb
      rcases List.mem_cons.mp hb with hb | hb
      · have hbproc : b.process = p := congrArg Command.process hb
        have hbseq : b.sequence = (e.state N).sequence p + 1 := congrArg Command.sequence hb
        have hanew : a ≠ (⟨op, p, (e.state N).sequence p + 1⟩ : Command P Op) := by
          intro h
          have := congrArg Command.sequence h
          dsimp at this
          omega
        have haold := (List.mem_cons.mp ha).resolve_left hanew
        have hret : a ∈ (e.state N).returned := by
          apply Classical.byContradiction
          intro hn
          have hactive := e.active_of_pending haold hn
          rw [hp, hbproc, hidle] at hactive
          cases hactive
        refine ⟨N, by omega, hret, ?_⟩
        intro hbOld
        have hbound := (e.valid N).invoked_bound b hbOld
        rw [hbproc, hbseq] at hbound
        omega
      · rcases List.mem_cons.mp ha with ha | ha
        · have haproc : a.process = p := congrArg Command.process ha
          have haseq : a.sequence = (e.state N).sequence p + 1 := congrArg Command.sequence ha
          have hbnd := (e.valid N).invoked_bound b hb
          rw [← hp, haproc] at hbnd
          omega
        · exact lift ha hb
    · exact lift (by simpa only [he, finish] using ha) (by simpa only [he, finish] using hb)

end InvocationLedger.Run


namespace WeakUniversal
open WeakUniversal (Cmd Tagged Return Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-! ### The manuscript's chain, for both constructions

Both constructions record a response `⟨cmd, r, s⟩` only for a trace `s`
committed at round `r ≥ 1` with `cmd` in it.  `r*` at boundary `k` is the last
round of those responses, and the chain is the manuscript's `t_k`,
`GCA.RoundExecution.committedChain`. -/

/-- The largest element of a list of rounds, `0` for the empty list. -/
def lastRound (rounds : List Nat) : Nat := rounds.foldr max 0

theorem le_lastRound {rounds : List Nat} {r : Nat} (h : r ∈ rounds) : r ≤ lastRound rounds := by
  induction rounds with
  | nil => cases h
  | cons s rounds ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem lastRound_cases (rounds : List Nat) : lastRound rounds = 0 ∨ lastRound rounds ∈ rounds := by
  induction rounds with
  | nil => exact Or.inl rfl
  | cons s rounds ih =>
    change max s (lastRound rounds) = 0 ∨ max s (lastRound rounds) ∈ s :: rounds
    rcases Nat.le_total s (lastRound rounds) with h | h
    · rw [Nat.max_eq_right h]
      rcases ih with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_cons_of_mem _ h')
    · rw [Nat.max_eq_left h]
      exact Or.inr List.mem_cons_self

/-- **Linearizability from the chain of committed traces**, the argument of
`theorem:weakUCLin`, for any construction whose responses are read off traces
committed at their rounds.  An operation returned with `⟨cmd, r, s⟩` is
associated with round `r`: `s = t_r` by Adoption (`committedChain_commit`), so
its response is `ret*(cmd, t_r)`, and every command of `t_r` was invoked before
it returned (`hcausal`).  `r*` is the last round of the responses observed. -/
theorem committedChain_linearizes {H : Environment (n := n) obj}
    (e : GCA.RoundExecution (Tagged (n := n) obj) (Fin n)) (he : ∀ r, e.round r = H (r + 1))
    (spec : ∀ r, (H (r + 1)).Specification)
    (returns : Nat → List (Return (n := n) obj)) (invocations : Nat → List (Cmd n Op))
    (hgrow : ∀ k, ∀ ret ∈ returns k, ret ∈ returns (k + 1))
    (hret : ∀ k, ∀ ret ∈ returns k, Committed obj H ret.round ret.trace ∧
      0 < (Tagged obj).traceCount ret.command ret.trace)
    (hunique : ∀ r p t flag a, (H (r + 1)).output p = some (t, flag) →
      (Tagged obj).traceCount a t ≤ 1)
    (hcausal : ∀ k, ∀ ret ∈ returns k, ∀ a,
      0 < (Tagged obj).traceCount a ret.trace → a ∈ invocations k) :
    ∃ x : Nat → List (Cmd n Op),
      (∀ N, (Tagged obj).Linearizes
        ⟨fun k a => a ∈ invocations k, fun k a v => ∃ ret ∈ returns k,
          ret.command = a ∧ (Tagged obj).traceReturn a 0 ret.trace = some v⟩ N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) := by
  have espec : ∀ r, (e.round r).Specification := fun r => he r ▸ spec r
  -- A response's trace is the chain's trace at its round.
  have hchain : ∀ {k ret}, ret ∈ returns k → e.committedChain ret.round = ret.trace := by
    intro k ret hr
    obtain ⟨hpos, p, hp⟩ := (hret k ret hr).1
    obtain ⟨r, hr'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    rw [hr'] at hp ⊢
    exact e.committedChain_commit espec (p := p) (by rw [he]; exact hp)
  have hle : ∀ {k ret}, ret ∈ returns k →
      ret.round ≤ lastRound ((returns k).map Return.round) := fun hr =>
    le_lastRound (List.mem_map.mpr ⟨_, hr, rfl⟩)
  obtain ⟨hlin, hcoh⟩ := (Tagged obj).roundChain_linearizes
    ⟨fun k a => a ∈ invocations k, fun k a v => ∃ ret ∈ returns k,
      ret.command = a ∧ (Tagged obj).traceReturn a 0 ret.trace = some v⟩
    e.committedChain e.committedChain_zero (e.committedChain_mono espec)
    (fun k => lastRound ((returns k).map Return.round))
    (fun N => by
      rcases lastRound_cases ((returns N).map Return.round) with h | h
      · rw [h]; exact Nat.zero_le _
      · obtain ⟨ret, hr, hround⟩ := List.mem_map.mp h
        rw [← hround]; exact hle (hgrow N ret hr))
    (fun k a => by
      rcases e.committedChain_cases k with h0 | ⟨j, p, -, hp⟩
      · rw [h0]; exact Nat.zero_le _
      · exact hunique j p _ true a (he j ▸ hp))
    (fun N a ha => by
      rcases lastRound_cases ((returns N).map Return.round) with h | h
      · rw [h, e.committedChain_zero] at ha
        exact absurd ha (Nat.lt_irrefl 0)
      · obtain ⟨ret, hr, hround⟩ := List.mem_map.mp h
        rw [← hround, hchain hr] at ha
        exact hcausal N ret hr a ha)
    (fun j a v ⟨ret, hr, hcmd, hv⟩ => ⟨ret.round, hle hr, by
      rw [hchain hr, ← hcmd]; exact (hret j ret hr).2, by rw [hchain hr]; exact hv,
      fun b hb => hcausal j ret hr b (by rw [← hchain hr]; exact hb)⟩)
  exact ⟨_, hlin, hcoh⟩

/-- The command history of this particular run, including response values. -/
def Execution.history {H : Environment (n := n) obj} (run : Execution obj H) :
    FiniteHistory (Cmd n Op) Response where
  invoked := fun k a => a ∈ (run.state k).invocations
  returned := fun k a v => ∃ ret ∈ (run.state k).returns,
    ret.command = a ∧ (Tagged obj).traceReturn a 0 ret.trace = some v

/-- Every command in a returned trace has already been invoked in this run.
This is a temporal property, stronger than existence in some reachable state. -/
def Execution.ReturnsInvokedBy {H : Environment (n := n) obj} (run : Execution obj H) : Prop :=
  ∀ k, ∀ ret ∈ (run.state k).returns, ∀ a,
    0 < (Tagged obj).traceCount a ret.trace → a ∈ (run.state k).invocations

/-- The paper's finite-history linearization argument. GCA safety supplies
comparability and stable responses; occurrence uniqueness is proved by the
construction. The remaining scheduler obligation is explicitly named. -/
theorem Execution.finite_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hcausal : run.ReturnsInvokedBy obj) (N : Nat) :
    ∃ x, (Tagged obj).Linearizes (run.history obj) N x := by
  obtain ⟨x, hx, -⟩ := committedChain_linearizes obj (roundExecution obj H coverage) (fun _ => rfl) spec
    (fun k => (run.state k).returns) (fun k => (run.state k).invocations)
    (fun k ret hr => by
      rcases run.next k with he | hs
      · rw [he]; exact hr
      · have hm : ∀ {c d : Configuration (n := n) obj}, Step obj H c d →
            ∀ ret ∈ c.returns, ret ∈ d.returns := by
          intro c d hs ret hr
          cases hs <;> first | exact List.mem_cons_of_mem _ hr | exact hr
        exact hm hs ret hr)
    (fun k ret hr => (invariant obj (run.reachable obj k)).returns ret hr)
    (output_count_le_one obj coverage spec) hcausal
  exact ⟨x N, hx N⟩
/-- The representative also preserves each process's invocation sequence.
Together with `Linearizes.completion`, this supplies the command/value form
of the paper's per-process equivalence with the completed history. -/
theorem Execution.linearization_process_order {H : Environment (n := n) obj}
    (run : Execution obj H) {N : Nat} {x : List (Cmd n Op)}
    (hx : (Tagged obj).Linearizes (run.history obj) N x)
    {a b : Cmd n Op} (ha : a ∈ x) (hb : b ∈ x)
    (hp : a.process = b.process) (hs : a.sequence < b.sequence) :
    x.idxOf a < x.idxOf b := by
  obtain ⟨k, hk, hr, hn⟩ := (run.ledgerRun obj).sequence_precedes
    (hx.invoked a ha) (hx.invoked b hb) hp hs
  obtain ⟨ret, hret, he⟩ := List.mem_map.mp hr
  obtain ⟨v, hv⟩ := response_defined obj (run.reachable obj k) hret
  apply hx.realTime a b ha hb
  refine ⟨k, hk, ⟨v, ret, hret, he, ?_⟩, hn⟩
  rw [← he]
  exact hv


/-- **Linearizability of the whole run.**  One sequential order linearizes every
boundary at once: `x N` is a linearization of the history observed at `N`, and
`x k` is a literal prefix of `x m` whenever `k ≤ m`, so growing the history
never reorders operations it had already placed.  This is the finite-to-infinite
closure of `Execution.finite_linearization`. -/
theorem Execution.chain_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hcausal : run.ReturnsInvokedBy obj) :
    ∃ x : Nat → List (Cmd n Op),
      (∀ N, (Tagged obj).Linearizes (run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) := by
  exact committedChain_linearizes obj (roundExecution obj H coverage) (fun _ => rfl) spec
    (fun k => (run.state k).returns) (fun k => (run.state k).invocations)
    (fun k ret hr => by
      rcases run.next k with he | hs
      · rw [he]; exact hr
      · have hm : ∀ {c d : Configuration (n := n) obj}, Step obj H c d →
            ∀ ret ∈ c.returns, ret ∈ d.returns := by
          intro c d hs ret hr
          cases hs <;> first | exact List.mem_cons_of_mem _ hr | exact hr
        exact hm hs ret hr)
    (fun k ret hr => (invariant obj (run.reachable obj k)).returns ret hr)
    (output_count_le_one obj coverage spec) hcausal
end WeakUniversal

namespace HelpingUniversal
open WeakUniversal (Cmd Tagged Return Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The command history of this particular run, including response values. -/
def Execution.history {H : Environment (n := n) obj} (run : Execution obj H) :
    FiniteHistory (Cmd n Op) Response where
  invoked := fun k a => a ∈ (run.state k).invocations
  returned := fun k a v => ∃ ret ∈ (run.state k).returns,
    ret.command = a ∧ (Tagged obj).traceReturn a 0 ret.trace = some v

/-- Every command in a returned trace has already been invoked in this run.
This is a temporal property, stronger than existence in some reachable state. -/
def Execution.ReturnsInvokedBy {H : Environment (n := n) obj} (run : Execution obj H) : Prop :=
  ∀ k, ∀ ret ∈ (run.state k).returns, ∀ a,
    0 < (Tagged obj).traceCount a ret.trace → a ∈ (run.state k).invocations

/-- The paper's finite-history linearization argument. GCA safety supplies
comparability and stable responses; occurrence uniqueness is proved by the
construction. The remaining scheduler obligation is explicitly named. -/
theorem Execution.finite_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hcausal : run.ReturnsInvokedBy obj) (N : Nat) :
    ∃ x, (Tagged obj).Linearizes (run.history obj) N x := by
  obtain ⟨x, hx, -⟩ := WeakUniversal.committedChain_linearizes obj (roundExecution obj H coverage) (fun _ => rfl) spec
    (fun k => (run.state k).returns) (fun k => (run.state k).invocations)
    (fun k ret hr => by
      rcases run.next k with he | hs
      · rw [he]; exact hr
      · have hm : ∀ {c d : Configuration (n := n) obj}, Step obj H c d →
            ∀ ret ∈ c.returns, ret ∈ d.returns := by
          intro c d hs ret hr
          cases hs <;> first | exact List.mem_cons_of_mem _ hr | exact hr
        exact hm hs ret hr)
    (fun k ret hr => (invariant obj (run.reachable obj k)).returns ret hr)
    (output_count_le_one obj coverage spec) hcausal
  exact ⟨x N, hx N⟩
/-- The representative also preserves each process's invocation sequence.
Together with `Linearizes.completion`, this supplies the command/value form
of the paper's per-process equivalence with the completed history. -/
theorem Execution.linearization_process_order {H : Environment (n := n) obj}
    (run : Execution obj H) {N : Nat} {x : List (Cmd n Op)}
    (hx : (Tagged obj).Linearizes (run.history obj) N x)
    {a b : Cmd n Op} (ha : a ∈ x) (hb : b ∈ x)
    (hp : a.process = b.process) (hs : a.sequence < b.sequence) :
    x.idxOf a < x.idxOf b := by
  obtain ⟨k, hk, hr, hn⟩ := (run.ledgerRun obj).sequence_precedes
    (hx.invoked a ha) (hx.invoked b hb) hp hs
  obtain ⟨ret, hret, he⟩ := List.mem_map.mp hr
  obtain ⟨v, hv⟩ := response_defined obj (run.reachable obj k) hret
  apply hx.realTime a b ha hb
  refine ⟨k, hk, ⟨v, ret, hret, he, ?_⟩, hn⟩
  rw [← he]
  exact hv


/-- **Linearizability of the whole run.**  One sequential order linearizes every
boundary at once: `x N` is a linearization of the history observed at `N`, and
`x k` is a literal prefix of `x m` whenever `k ≤ m`, so growing the history
never reorders operations it had already placed.  This is the finite-to-infinite
closure of `Execution.finite_linearization`. -/
theorem Execution.chain_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hcausal : run.ReturnsInvokedBy obj) :
    ∃ x : Nat → List (Cmd n Op),
      (∀ N, (Tagged obj).Linearizes (run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) := by
  exact WeakUniversal.committedChain_linearizes obj (roundExecution obj H coverage) (fun _ => rfl) spec
    (fun k => (run.state k).returns) (fun k => (run.state k).invocations)
    (fun k ret hr => by
      rcases run.next k with he | hs
      · rw [he]; exact hr
      · have hm : ∀ {c d : Configuration (n := n) obj}, Step obj H c d →
            ∀ ret ∈ c.returns, ret ∈ d.returns := by
          intro c d hs ret hr
          cases hs <;> first | exact List.mem_cons_of_mem _ hr | exact hr
        exact hm hs ret hr)
    (fun k ret hr => (invariant obj (run.reachable obj k)).returns ret hr)
    (output_count_le_one obj coverage spec) hcausal
end HelpingUniversal

namespace GlobalSchedule

/-- Operational GCA safety discharges the abstract environment hypotheses.
Only chronological provenance remains to be derived from protocol scheduling. -/
theorem Weak.finite_linearization_of_provenance
    {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
    [DecidableEq Op] {f : UniversalProtocol.Family (n := n) obj}
    (g : Weak obj f) (hcausal : g.run.ReturnsInvokedBy obj) (N : Nat) :
    ∃ x, (obj.commandObject (Fin n)).Linearizes (g.run.history obj) N x :=
  g.run.finite_linearization obj (g.composition.callsCovered obj)
    (f.specifications obj) hcausal N

/-- Operational GCA safety discharges the abstract environment hypotheses.
Only chronological provenance remains to be derived from protocol scheduling. -/
theorem Helping.finite_linearization_of_provenance
    {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
    [DecidableEq Op] {f : UniversalProtocol.Family (n := n) obj}
    (g : Helping obj f) (hcausal : g.run.ReturnsInvokedBy obj) (N : Nat) :
    ∃ x, (obj.commandObject (Fin n)).Linearizes (g.run.history obj) N x :=
  g.run.finite_linearization obj (g.composition.callsCovered obj)
    (f.specifications obj) hcausal N


/-- Operational GCA safety discharges the abstract environment hypotheses for
the whole-run linearization too. -/
theorem Weak.chain_linearization_of_provenance
    {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
    [DecidableEq Op] {f : UniversalProtocol.Family (n := n) obj}
    (g : Weak obj f) (hcausal : g.run.ReturnsInvokedBy obj) :
    ∃ x : Nat → List (WeakUniversal.Cmd n Op),
      (∀ N, (obj.commandObject (Fin n)).Linearizes (g.run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :=
  g.run.chain_linearization obj (g.composition.callsCovered obj)
    (f.specifications obj) hcausal

/-- The same for Algorithm 3. -/
theorem Helping.chain_linearization_of_provenance
    {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
    [DecidableEq Op] {f : UniversalProtocol.Family (n := n) obj}
    (g : Helping obj f) (hcausal : g.run.ReturnsInvokedBy obj) :
    ∃ x : Nat → List (WeakUniversal.Cmd n Op),
      (∀ N, (obj.commandObject (Fin n)).Linearizes (g.run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :=
  g.run.chain_linearization obj (g.composition.callsCovered obj)
    (f.specifications obj) hcausal

end GlobalSchedule

end ConflictFreedom
