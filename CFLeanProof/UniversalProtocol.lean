import CFLeanProof.GCAProtocol
import CFLeanProof.HelpingUniversal

/-! A family of operational GCA instances supplies the per-round histories for
either universal construction. The program-to-protocol call coverage remains an
explicit hypothesis: this module does not posit a composed scheduler. -/
namespace ConflictFreedom.UniversalProtocol

variable {State Op Response : Type} {n : Nat}
    (obj : Object State Op Response) [DecidableEq Op]

/-- One operational GCA object for each positive universal-construction round.
Index zero is included for convenient alignment with the environment type, but
the constructions only call positive rounds. -/
structure Family where
  protocol : Nat → GCA.Protocol (obj.commandObject (Fin n)) (Fin n)

/-- The histories exposed to the universal constructions are extracted from
the actual GCA protocol state machines, round by round. -/
noncomputable def Family.environment (f : Family (n := n) obj) :
    WeakUniversal.Environment (n := n) obj :=
  fun r => (f.protocol r).history

/-- Every round satisfies all six GCA safety requirements without a separate
specification assumption on the universal construction. -/
theorem Family.specification (f : Family (n := n) obj) (r : Nat) :
    (f.environment obj r).Specification :=
  (f.protocol r).specification

theorem Family.specifications (f : Family (n := n) obj) :
    ∀ r, (f.environment obj (r + 1)).Specification :=
  fun r => f.specification obj (r + 1)

/-- The author's assumed wait-free snapshot interface, uniformly across the
protocol family. It is needed for per-round termination, not GCA safety. -/
def Family.SnapshotWaitFree (f : Family (n := n) obj) : Prop :=
  ∀ r, (f.protocol r).SnapshotWaitFree

theorem Family.round_returned (f : Family (n := n) obj)
    (hw : f.SnapshotWaitFree obj) (r : Nat) (p : Fin n)
    (hp : (f.protocol r).InfiniteSteps p) :
    ∃ t c, (f.environment obj r).output p = some (t, c) :=
  (f.protocol r).returned_of_infiniteSteps (hw r) hp

/-- Algorithm 1 inherits the prefix-rounds lemma once its actual calls cover
the protocol inputs. -/
theorem Family.weak_committed_prefix (f : Family (n := n) obj)
    (coverage : WeakUniversal.CallsCovered obj (f.environment obj))
    {r k : Nat} (hrk : r ≤ k) {p q : Fin n}
    {s t : (obj.commandObject (Fin n)).Trace} {flag : Bool}
    (hs : (f.environment obj (r + 1)).output p = some (s, true))
    (ht : (f.environment obj (k + 1)).output q = some (t, flag)) :
    (obj.commandObject (Fin n)).TracePrefix s t :=
  WeakUniversal.committed_prefix obj coverage (f.specifications obj) hrk hs ht

/-- Algorithm 3 has the same prefix-rounds conclusion from its own call
coverage, including calls made while helping other operations. -/
theorem Family.helping_committed_prefix (f : Family (n := n) obj)
    (coverage : HelpingUniversal.CallsCovered obj (f.environment obj))
    {r k : Nat} (hrk : r ≤ k) {p q : Fin n}
    {s t : (obj.commandObject (Fin n)).Trace} {flag : Bool}
    (hs : (f.environment obj (r + 1)).output p = some (s, true))
    (ht : (f.environment obj (k + 1)).output q = some (t, flag)) :
    (obj.commandObject (Fin n)).TracePrefix s t :=
  HelpingUniversal.committed_prefix obj coverage (f.specifications obj) hrk hs ht

/-- All returned traces of a reachable Algorithm 1 configuration form a
prefix chain. -/
theorem Family.weak_return_traces_comparable (f : Family (n := n) obj)
    (coverage : WeakUniversal.CallsCovered obj (f.environment obj))
    {c : WeakUniversal.Configuration (n := n) obj}
    (hc : WeakUniversal.Reachable obj (f.environment obj) c)
    {a b : WeakUniversal.Return (n := n) obj}
    (ha : a ∈ c.returns) (hb : b ∈ c.returns) :
    (obj.commandObject (Fin n)).TracePrefix a.trace b.trace ∨
      (obj.commandObject (Fin n)).TracePrefix b.trace a.trace :=
  WeakUniversal.return_traces_comparable obj coverage (f.specifications obj) hc ha hb

/-- The corresponding prefix chain for Algorithm 3 includes returns obtained
from another process's published trace. -/
theorem Family.helping_return_traces_comparable (f : Family (n := n) obj)
    (coverage : HelpingUniversal.CallsCovered obj (f.environment obj))
    {c : HelpingUniversal.Configuration (n := n) obj}
    (hc : HelpingUniversal.Reachable obj (f.environment obj) c)
    {a b : WeakUniversal.Return (n := n) obj}
    (ha : a ∈ c.returns) (hb : b ∈ c.returns) :
    (obj.commandObject (Fin n)).TracePrefix a.trace b.trace ∨
      (obj.commandObject (Fin n)).TracePrefix b.trace a.trace :=
  HelpingUniversal.return_traces_comparable obj coverage (f.specifications obj) hc ha hb

end ConflictFreedom.UniversalProtocol
