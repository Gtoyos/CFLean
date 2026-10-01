import CFLeanProof.LedgerEvents
import CFLeanProof.CausalLinearization

/-! # `theorem:weakUCLin` in the manuscript's own terms

`UniversalLinearization` proves linearizability against a boundary-indexed
observation of a run.  This module states and proves it against the literal
invocation/response event sequence of the run, using the manuscript's own
definition: a completion `H̄`, a legal sequential history `S`, `H̄|ᵢ = S|ᵢ`
for every process `i`, and preservation of real-time order.
-/
namespace ConflictFreedom

namespace WeakUniversal
open WeakUniversal (Cmd Tagged Return Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- Recorded responses are never withdrawn. -/
theorem Execution.returns_step {H : Environment (n := n) obj} (run : Execution obj H)
    {k : Nat} {ret : Return (n := n) obj} (hr : ret ∈ (run.state k).returns) :
    ret ∈ (run.state (k + 1)).returns := by
  rcases run.next k with he | hs
  · rw [he]; exact hr
  · have hm : ∀ {c d : Configuration (n := n) obj}, Step obj H c d →
        ∀ ret ∈ c.returns, ret ∈ d.returns := by
      intro c d hs ret hr
      cases hs <;> first | exact List.mem_cons_of_mem _ hr | exact hr
    exact hm hs ret hr

theorem Execution.returns_mono {H : Environment (n := n) obj} (run : Execution obj H)
    {k m : Nat} (hkm : k ≤ m) {ret : Return (n := n) obj}
    (hr : ret ∈ (run.state k).returns) : ret ∈ (run.state m).returns := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  clear hkm
  induction d with
  | zero => simpa using hr
  | succ d ih => exact run.returns_step obj ih

/-- The literal event sequence records exactly the run's invocations and
responses.  The configuration-boundary observation used by
`UniversalLinearization` and this event sequence are therefore two
presentations of one history. -/
theorem Execution.history_observes {H : Environment (n := n) obj} (run : Execution obj H)
    {resp : Cmd n Op → Response} {N : Nat}
    (hresp : ∀ k, k ≤ N → ∀ a v, (run.history obj).returned k a v → v = resp a) :
    (∀ a, History.Invoked ((run.ledgerRun obj).history resp N) a ↔
        (run.history obj).invoked N a) ∧
    (∀ a v, History.Responded ((run.ledgerRun obj).history resp N) a v ↔
        (run.history obj).returned N a v) := by
  refine ⟨fun a => (run.ledgerRun obj).invoked_iff resp N a, fun a v => ?_⟩
  rw [(run.ledgerRun obj).responded_iff resp N a v]
  constructor
  · rintro ⟨ha, rfl⟩
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp ha
    obtain ⟨w, hw⟩ := response_defined obj (run.reachable obj N) hr
    have hvv : (run.history obj).returned N a w := ⟨ret, hr, hc, by rw [← hc]; exact hw⟩
    rw [← hresp N (Nat.le_refl N) a w hvv]
    exact hvv
  · intro hv
    obtain ⟨ret, hr, hc, _⟩ := id hv
    exact ⟨List.mem_map.mpr ⟨ret, hr, hc⟩, hresp N (Nat.le_refl N) a v hv⟩

/-- **The manuscript's linearizability for Algorithm 1.**  Up to any boundary,
the run's literal event sequence has a completion that matches a legal
sequential history process by process and preserves real-time order.  The
response assignment agrees with every value the run actually returned, and by
`InvocationLedger.Run.history_congr` the event sequence depends on nothing
else. -/
theorem Execution.event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hcausal : run.ReturnsInvokedBy obj) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ k, k ≤ N → ∀ a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).EventLinearizable Command.process
        ((run.ledgerRun obj).history resp N) := by
  obtain ⟨x, hx⟩ := run.finite_linearization obj coverage spec hcausal N
  have hstable : ∀ k, k ≤ N → ∀ a v, (run.history obj).returned k a v →
      v = (Tagged obj).sequentialResponse x a := by
    intro k hk a v hv
    obtain ⟨ret, hr, hc, ht⟩ := hv
    exact (hx.completed a v ⟨ret, run.returns_mono obj hk hr, hc, ht⟩).2.symm
  refine ⟨(Tagged obj).sequentialResponse x, hstable, ?_⟩
  refine (run.ledgerRun obj).eventLinearizable_of_linearizes _ (Tagged obj) hx
    (fun k _ a ha => ha) ?_ (fun a b ha hb hp hs => run.linearization_process_order obj hx ha hb hp hs)
  intro k hk a ha
  obtain ⟨ret, hr, hc⟩ := List.mem_map.mp ha
  obtain ⟨v, hv⟩ := response_defined obj (run.reachable obj k) hr
  have hvv : (run.history obj).returned k a v := ⟨ret, hr, hc, by rw [← hc]; exact hv⟩
  rw [← hstable k hk a v hvv]
  exact hvv

end WeakUniversal

namespace HelpingUniversal
open WeakUniversal (Cmd Tagged Return Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- Recorded responses are never withdrawn. -/
theorem Execution.returns_step {H : Environment (n := n) obj} (run : Execution obj H)
    {k : Nat} {ret : Return (n := n) obj} (hr : ret ∈ (run.state k).returns) :
    ret ∈ (run.state (k + 1)).returns := by
  rcases run.next k with he | hs
  · rw [he]; exact hr
  · have hm : ∀ {c d : Configuration (n := n) obj}, Step obj H c d →
        ∀ ret ∈ c.returns, ret ∈ d.returns := by
      intro c d hs ret hr
      cases hs <;> first | exact List.mem_cons_of_mem _ hr | exact hr
    exact hm hs ret hr

theorem Execution.returns_mono {H : Environment (n := n) obj} (run : Execution obj H)
    {k m : Nat} (hkm : k ≤ m) {ret : Return (n := n) obj}
    (hr : ret ∈ (run.state k).returns) : ret ∈ (run.state m).returns := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  clear hkm
  induction d with
  | zero => simpa using hr
  | succ d ih => exact run.returns_step obj ih

/-- The literal event sequence records exactly the run's invocations and
responses.  The configuration-boundary observation used by
`UniversalLinearization` and this event sequence are therefore two
presentations of one history. -/
theorem Execution.history_observes {H : Environment (n := n) obj} (run : Execution obj H)
    {resp : Cmd n Op → Response} {N : Nat}
    (hresp : ∀ k, k ≤ N → ∀ a v, (run.history obj).returned k a v → v = resp a) :
    (∀ a, History.Invoked ((run.ledgerRun obj).history resp N) a ↔
        (run.history obj).invoked N a) ∧
    (∀ a v, History.Responded ((run.ledgerRun obj).history resp N) a v ↔
        (run.history obj).returned N a v) := by
  refine ⟨fun a => (run.ledgerRun obj).invoked_iff resp N a, fun a v => ?_⟩
  rw [(run.ledgerRun obj).responded_iff resp N a v]
  constructor
  · rintro ⟨ha, rfl⟩
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp ha
    obtain ⟨w, hw⟩ := response_defined obj (run.reachable obj N) hr
    have hvv : (run.history obj).returned N a w := ⟨ret, hr, hc, by rw [← hc]; exact hw⟩
    rw [← hresp N (Nat.le_refl N) a w hvv]
    exact hvv
  · intro hv
    obtain ⟨ret, hr, hc, _⟩ := id hv
    exact ⟨List.mem_map.mpr ⟨ret, hr, hc⟩, hresp N (Nat.le_refl N) a v hv⟩

/-- **The manuscript's linearizability for Algorithm 3.**  Up to any boundary,
the run's literal event sequence has a completion that matches a legal
sequential history process by process and preserves real-time order.  The
response assignment agrees with every value the run actually returned, and by
`InvocationLedger.Run.history_congr` the event sequence depends on nothing
else. -/
theorem Execution.event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hcausal : run.ReturnsInvokedBy obj) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ k, k ≤ N → ∀ a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).EventLinearizable Command.process
        ((run.ledgerRun obj).history resp N) := by
  obtain ⟨x, hx⟩ := run.finite_linearization obj coverage spec hcausal N
  have hstable : ∀ k, k ≤ N → ∀ a v, (run.history obj).returned k a v →
      v = (Tagged obj).sequentialResponse x a := by
    intro k hk a v hv
    obtain ⟨ret, hr, hc, ht⟩ := hv
    exact (hx.completed a v ⟨ret, run.returns_mono obj hk hr, hc, ht⟩).2.symm
  refine ⟨(Tagged obj).sequentialResponse x, hstable, ?_⟩
  refine (run.ledgerRun obj).eventLinearizable_of_linearizes _ (Tagged obj) hx
    (fun k _ a ha => ha) ?_ (fun a b ha hb hp hs => run.linearization_process_order obj hx ha hb hp hs)
  intro k hk a ha
  obtain ⟨ret, hr, hc⟩ := List.mem_map.mp ha
  obtain ⟨v, hv⟩ := response_defined obj (run.reachable obj k) hr
  have hvv : (run.history obj).returned k a v := ⟨ret, hr, hc, by rw [← hc]; exact hv⟩
  rw [← hstable k hk a v hvv]
  exact hvv

end HelpingUniversal

namespace GlobalSchedule
open WeakUniversal (Cmd Tagged)
variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {f : UniversalProtocol.Family (n := n) obj}

/-- **Algorithm 1 is linearizable in the manuscript's own formulation**, with
no hypothesis beyond the operational scheduling rules.  For every boundary `N`
there is a literal sequence of invocation and response events that (1) records
exactly the operations the run has invoked, (2) records exactly the responses
the run has returned, (3) is well formed — unique instances, sequential per
process — and (4) is linearizable: it has a completion agreeing with a legal
sequential history on every process and preserving real-time order. -/
theorem Weak.event_linearization (g : Weak obj f) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ a, History.Invoked ((g.run.ledgerRun obj).history resp N) a ↔
          (g.run.history obj).invoked N a) ∧
      (∀ a v, History.Responded ((g.run.ledgerRun obj).history resp N) a v ↔
          (g.run.history obj).returned N a v) ∧
      History.WellFormed (Response := Response) Command.process
        ((g.run.ledgerRun obj).history resp N) ∧
      (Tagged obj).EventLinearizable Command.process
        ((g.run.ledgerRun obj).history resp N) := by
  obtain ⟨resp, hresp, hlin⟩ := g.run.event_linearization obj
    (g.composition.callsCovered obj) (f.specifications obj) g.returnsInvokedBy N
  obtain ⟨hinv, hret⟩ := g.run.history_observes obj hresp
  exact ⟨resp, hinv, hret, (g.run.ledgerRun obj).history_wellFormed resp N, hlin⟩

/-- The same for Algorithm 3. -/
theorem Helping.event_linearization (g : Helping obj f) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ a, History.Invoked ((g.run.ledgerRun obj).history resp N) a ↔
          (g.run.history obj).invoked N a) ∧
      (∀ a v, History.Responded ((g.run.ledgerRun obj).history resp N) a v ↔
          (g.run.history obj).returned N a v) ∧
      History.WellFormed (Response := Response) Command.process
        ((g.run.ledgerRun obj).history resp N) ∧
      (Tagged obj).EventLinearizable Command.process
        ((g.run.ledgerRun obj).history resp N) := by
  obtain ⟨resp, hresp, hlin⟩ := g.run.event_linearization obj
    (g.composition.callsCovered obj) (f.specifications obj) g.returnsInvokedBy N
  obtain ⟨hinv, hret⟩ := g.run.history_observes obj hresp
  exact ⟨resp, hinv, hret, (g.run.ledgerRun obj).history_wellFormed resp N, hlin⟩

/-- **Algorithm 1 over any GCA objects meeting the safety part of the interface
is linearizable**, in the manuscript's own formulation, at every finite prefix of
the run: only the six properties of every round and Validity on every prefix
(`causal`) are used — no fairness, termination or scheduling assumption. -/
theorem WeakRun.event_linearization {H : WeakUniversal.Environment (n := n) obj}
    (g : WeakRun obj H) (hspec : ∀ r, (H (r + 1)).Specification)
    (hcausal : g.run.CausalGCA obj) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ a, History.Invoked ((g.run.ledgerRun obj).history resp N) a ↔
          (g.run.history obj).invoked N a) ∧
      (∀ a v, History.Responded ((g.run.ledgerRun obj).history resp N) a v ↔
          (g.run.history obj).returned N a v) ∧
      History.WellFormed (Response := Response) Command.process
        ((g.run.ledgerRun obj).history resp N) ∧
      (Tagged obj).EventLinearizable Command.process
        ((g.run.ledgerRun obj).history resp N) := by
  obtain ⟨resp, hresp, hlin⟩ := g.run.event_linearization obj g.callsCovered hspec
    (g.run.returnsInvokedBy_of_causalGCA obj hcausal) N
  obtain ⟨hinv, hret⟩ := g.run.history_observes obj hresp
  exact ⟨resp, hinv, hret, (g.run.ledgerRun obj).history_wellFormed resp N, hlin⟩

/-- **Theorem `theorem:weakUCLin`, finite prefixes, over any GCA meeting the
interface.** -/
theorem WeakGCA.event_linearization {H : WeakUniversal.Environment (n := n) obj}
    (g : WeakGCA obj H) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ a, History.Invoked ((g.run.ledgerRun obj).history resp N) a ↔
          (g.run.history obj).invoked N a) ∧
      (∀ a v, History.Responded ((g.run.ledgerRun obj).history resp N) a v ↔
          (g.run.history obj).returned N a v) ∧
      History.WellFormed (Response := Response) Command.process
        ((g.run.ledgerRun obj).history resp N) ∧
      (Tagged obj).EventLinearizable Command.process
        ((g.run.ledgerRun obj).history resp N) :=
  g.toWeakRun.event_linearization g.gca.spec g.gca.causal N

/-- **Algorithm 3 over any GCA objects meeting the safety part of the interface
is linearizable**, at every finite prefix of the run. -/
theorem HelpingRun.event_linearization {H : WeakUniversal.Environment (n := n) obj}
    (g : HelpingRun obj H) (hspec : ∀ r, (H (r + 1)).Specification)
    (hcausal : g.run.CausalGCA obj) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ a, History.Invoked ((g.run.ledgerRun obj).history resp N) a ↔
          (g.run.history obj).invoked N a) ∧
      (∀ a v, History.Responded ((g.run.ledgerRun obj).history resp N) a v ↔
          (g.run.history obj).returned N a v) ∧
      History.WellFormed (Response := Response) Command.process
        ((g.run.ledgerRun obj).history resp N) ∧
      (Tagged obj).EventLinearizable Command.process
        ((g.run.ledgerRun obj).history resp N) := by
  obtain ⟨resp, hresp, hlin⟩ := g.run.event_linearization obj g.callsCovered hspec
    (g.run.returnsInvokedBy_of_causalGCA obj hcausal) N
  obtain ⟨hinv, hret⟩ := g.run.history_observes obj hresp
  exact ⟨resp, hinv, hret, (g.run.ledgerRun obj).history_wellFormed resp N, hlin⟩

/-- **The unlabeled lemma of §6 (Algorithm 3 is linearizable), finite prefixes,
over any GCA meeting the interface.** -/
theorem HelpingGCA.event_linearization {H : WeakUniversal.Environment (n := n) obj}
    (g : HelpingGCA obj H) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ a, History.Invoked ((g.run.ledgerRun obj).history resp N) a ↔
          (g.run.history obj).invoked N a) ∧
      (∀ a v, History.Responded ((g.run.ledgerRun obj).history resp N) a v ↔
          (g.run.history obj).returned N a v) ∧
      History.WellFormed (Response := Response) Command.process
        ((g.run.ledgerRun obj).history resp N) ∧
      (Tagged obj).EventLinearizable Command.process
        ((g.run.ledgerRun obj).history resp N) :=
  g.toHelpingRun.event_linearization g.gca.spec g.gca.causal N

/-- Every prefix of the run is a well-formed history in the manuscript's
sense: unique operation instances, sequential per process. -/
theorem Weak.history_wellFormed (g : Weak obj f) (resp : Cmd n Op → Response) (N : Nat) :
    History.WellFormed (Response := Response) Command.process
      ((g.run.ledgerRun obj).history resp N) :=
  (g.run.ledgerRun obj).history_wellFormed resp N

/-- The same for Algorithm 3. -/
theorem Helping.history_wellFormed (g : Helping obj f) (resp : Cmd n Op → Response) (N : Nat) :
    History.WellFormed (Response := Response) Command.process
      ((g.run.ledgerRun obj).history resp N) :=
  (g.run.ledgerRun obj).history_wellFormed resp N

end GlobalSchedule
end ConflictFreedom
