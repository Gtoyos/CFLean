import CFLeanProof.FiniteChain
import CFLeanProof.InvocationTiming

/-! Finite-history consequences of the universal constructions' committed
prefix chain.  A greatest returned trace exists at every finite configuration,
and each already returned operation has the same response in that trace. -/
namespace ConflictFreedom

namespace WeakUniversal
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

theorem return_prefix_chain {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    {c : Configuration (n := n) obj} (hc : Reachable obj H c) :
    (Tagged obj).PrefixChain (c.returns.map Return.trace) := by
  intro s hs t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  exact return_traces_comparable obj coverage spec hc ha hb

/-- A finite prefix's completed operations agree on one greatest response
trace. The trace is empty when no operation has returned. -/
theorem greatest_return_trace {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    {c : Configuration (n := n) obj} (hc : Reachable obj H c) :
    ∃ m : (Tagged (n := n) obj).Trace,
      ((c.returns.map Return.trace = [] ∧ m = (Tagged obj).emptyTrace) ∨
        m ∈ c.returns.map Return.trace) ∧
      ∀ ret ∈ c.returns,
        (Tagged obj).TracePrefix ret.trace m ∧
          response obj ret = (Tagged obj).traceReturn ret.command 0 m := by
  obtain ⟨m, hmem, hmax⟩ := (Tagged obj).finiteChain_greatest _
    (return_prefix_chain obj coverage spec hc)
  refine ⟨m, hmem, ?_⟩
  intro ret hr
  have hm : ret.trace ∈ c.returns.map Return.trace :=
    List.mem_map.mpr ⟨ret, hr, rfl⟩
  have hp := hmax ret.trace hm
  have hk : 0 < ((Tagged (n := n) obj).traceResponses ret.command
      (Tagged (n := n) obj).initial ret.trace).length := by
    simpa only [(Tagged obj).traceResponses_length] using
      ((invariant obj hc).returns ret hr).2
  exact ⟨hp, (Tagged obj).traceReturn_prefix hp ret.command 0 hk⟩

end WeakUniversal

namespace HelpingUniversal
open WeakUniversal (Tagged Return Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

theorem return_prefix_chain {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    {c : Configuration (n := n) obj} (hc : Reachable obj H c) :
    (Tagged obj).PrefixChain (c.returns.map Return.trace) := by
  intro s hs t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  exact return_traces_comparable obj coverage spec hc ha hb

/-- The helping construction also has one finite-history response trace that
agrees with every completed operation, including operations helped by peers. -/
theorem greatest_return_trace {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    {c : Configuration (n := n) obj} (hc : Reachable obj H c) :
    ∃ m : (Tagged (n := n) obj).Trace,
      ((c.returns.map Return.trace = [] ∧ m = (Tagged obj).emptyTrace) ∨
        m ∈ c.returns.map Return.trace) ∧
      ∀ ret ∈ c.returns,
        (Tagged obj).TracePrefix ret.trace m ∧
          WeakUniversal.response obj ret = (Tagged obj).traceReturn ret.command 0 m := by
  obtain ⟨m, hmem, hmax⟩ := (Tagged obj).finiteChain_greatest _
    (return_prefix_chain obj coverage spec hc)
  refine ⟨m, hmem, ?_⟩
  intro ret hr
  have hm : ret.trace ∈ c.returns.map Return.trace :=
    List.mem_map.mpr ⟨ret, hr, rfl⟩
  have hp := hmax ret.trace hm
  have hk : 0 < ((Tagged (n := n) obj).traceResponses ret.command
      (Tagged (n := n) obj).initial ret.trace).length := by
    simpa only [(Tagged obj).traceResponses_length] using
      ((invariant obj hc).returns ret hr).2
  exact ⟨hp, (Tagged obj).traceReturn_prefix hp ret.command 0 hk⟩

end HelpingUniversal
end ConflictFreedom
