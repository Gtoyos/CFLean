import CFLeanProof.UniversalProtocol
import CFLeanProof.UniversalFiniteHistory
import CFLeanProof.UniversalRoundTracking

/-! Composition boundary between a universal-construction run and the family
of operational GCA instances it calls.  The existing machines deliberately
have separate time axes, so composition records the exact call/input
correspondence.  All GCA safety facts are then derived from the protocol family;
they are not fields of this structure. -/
namespace ConflictFreedom.UniversalComposition

variable {State Op Response : Type} {n : Nat}
    (obj : Object State Op Response) [DecidableEq Op]

/-- The object `A_c` over commands (`WeakUniversal.Tagged`). -/
abbrev Tagged := obj.commandObject (Fin n)

/-- A composed Algorithm 1 run. Every abstract GCA input is exactly one call
recorded by the program run, and every recorded call is exposed as that input.
This rules out ghost protocol participants. -/
structure Weak where
  family : UniversalProtocol.Family (n := n) obj
  run : WeakUniversal.Execution obj (family.environment obj)
  input_iff_call : ∀ r p s,
    (family.environment obj (r + 1)).input p = some s ↔
      ∃ t, (⟨r + 1, p, s⟩ : WeakUniversal.Call obj) ∈ (run.state t).calls

namespace Weak
variable (e : Weak (n := n) obj)

theorem covers : e.run.Covers obj := by
  intro r p s hi
  exact (e.input_iff_call r p s).mp hi

theorem callsCovered :
    WeakUniversal.CallsCovered obj (e.family.environment obj) :=
  e.run.callsCovered obj e.covers

theorem specifications :
    ∀ r, (e.family.environment obj (r + 1)).Specification :=
  e.family.specifications obj

theorem call_unique (t : Nat) :
    (((e.run.state t).calls.map (WeakUniversal.Call.key obj))).Nodup :=
  WeakUniversal.gca_participation_unique obj (e.run.reachable obj t)

theorem return_traces_comparable (t : Nat)
    {a b : WeakUniversal.Return (n := n) obj}
    (ha : a ∈ (e.run.state t).returns) (hb : b ∈ (e.run.state t).returns) :
    (Tagged obj).TracePrefix a.trace b.trace ∨
      (Tagged obj).TracePrefix b.trace a.trace :=
  WeakUniversal.return_traces_comparable obj e.callsCovered e.specifications
    (e.run.reachable obj t) ha hb

theorem greatest_return_trace (t : Nat) :
    ∃ m : (Tagged (n := n) obj).Trace,
      ((((e.run.state t).returns.map WeakUniversal.Return.trace = [] ∧
          m = (Tagged obj).emptyTrace) ∨
        m ∈ (e.run.state t).returns.map WeakUniversal.Return.trace)) ∧
      ∀ ret ∈ (e.run.state t).returns,
        (Tagged obj).TracePrefix ret.trace m ∧
          WeakUniversal.response obj ret =
            (Tagged obj).traceReturn ret.command 0 m :=
  WeakUniversal.greatest_return_trace obj e.callsCovered e.specifications
    (e.run.reachable obj t)

theorem output_occurrence_invoked :
    ∀ r p t flag a,
      (e.family.environment obj (r + 1)).output p = some (t, flag) →
      0 < (Tagged obj).traceCount a t →
      ∃ c : WeakUniversal.Configuration (n := n) obj,
        WeakUniversal.Reachable obj (e.family.environment obj) c ∧
          a ∈ c.invocations :=
  WeakUniversal.output_occurrence_invoked obj e.callsCovered e.specifications

theorem output_count_le_one :
    ∀ r p t flag a,
      (e.family.environment obj (r + 1)).output p = some (t, flag) →
      (Tagged obj).traceCount a t ≤ 1 :=
  WeakUniversal.output_count_le_one obj e.callsCovered e.specifications

end Weak

/-- The corresponding composition contract for Algorithm 3. -/
structure Helping where
  family : UniversalProtocol.Family (n := n) obj
  run : HelpingUniversal.Execution obj (family.environment obj)
  input_iff_call : ∀ r p s,
    (family.environment obj (r + 1)).input p = some s ↔
      ∃ t, (⟨r + 1, p, s⟩ : WeakUniversal.Call obj) ∈ (run.state t).calls

namespace Helping
variable (e : Helping (n := n) obj)

theorem covers : e.run.Covers obj := by
  intro r p s hi
  exact (e.input_iff_call r p s).mp hi

theorem callsCovered :
    HelpingUniversal.CallsCovered obj (e.family.environment obj) :=
  e.run.callsCovered obj e.covers

theorem specifications :
    ∀ r, (e.family.environment obj (r + 1)).Specification :=
  e.family.specifications obj

theorem call_unique (t : Nat) :
    (((e.run.state t).calls.map (WeakUniversal.Call.key obj))).Nodup :=
  HelpingUniversal.gca_participation_unique obj (e.run.reachable obj t)

theorem return_traces_comparable (t : Nat)
    {a b : WeakUniversal.Return (n := n) obj}
    (ha : a ∈ (e.run.state t).returns) (hb : b ∈ (e.run.state t).returns) :
    (Tagged obj).TracePrefix a.trace b.trace ∨
      (Tagged obj).TracePrefix b.trace a.trace :=
  HelpingUniversal.return_traces_comparable obj e.callsCovered e.specifications
    (e.run.reachable obj t) ha hb

theorem greatest_return_trace (t : Nat) :
    ∃ m : (Tagged (n := n) obj).Trace,
      ((((e.run.state t).returns.map WeakUniversal.Return.trace = [] ∧
          m = (Tagged obj).emptyTrace) ∨
        m ∈ (e.run.state t).returns.map WeakUniversal.Return.trace)) ∧
      ∀ ret ∈ (e.run.state t).returns,
        (Tagged obj).TracePrefix ret.trace m ∧
          WeakUniversal.response obj ret =
            (Tagged obj).traceReturn ret.command 0 m :=
  HelpingUniversal.greatest_return_trace obj e.callsCovered e.specifications
    (e.run.reachable obj t)

theorem output_occurrence_invoked :
    ∀ r p t flag a,
      (e.family.environment obj (r + 1)).output p = some (t, flag) →
      0 < (Tagged obj).traceCount a t →
      ∃ c : HelpingUniversal.Configuration (n := n) obj,
        HelpingUniversal.Reachable obj (e.family.environment obj) c ∧
          a ∈ c.invocations :=
  HelpingUniversal.output_occurrence_invoked obj e.callsCovered e.specifications

end Helping
end ConflictFreedom.UniversalComposition
