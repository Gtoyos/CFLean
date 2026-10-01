import CFLeanProof.InfiniteEventLinearization
import CFLeanProof.WeakCoveredLinearization
import CFLeanProof.NonCausalWitness

/-! # What the universal constructions need from GCA

The manuscript presents Algorithms 1 and 3 as using GCA objects as black boxes,
specified by the six properties of §4.2, which must hold for every execution.
This module states exactly what the linearizability proofs consume from those
objects, so the modular claim can be read off.

**The interface.**  For a run over GCA histories `H`:

1. every round satisfies the six properties as a whole-run history:
   `∀ r, (H (r + 1)).Specification`;
2. every input is a proposal the construction makes: `CallsCovered`;
3. **causal validity**: an output a process receives contains only commands of
   proposals already made to that GCA object: `Execution.CausalGCA`.

(1) is the manuscript's specification applied to the whole run, and (3) is its
Validity applied to the prefix that ends with a receive
(`causalGCA_of_prefixValidity`): both are required by "the following properties
hold for every execution".  (3) is stated separately only because the model's
GCA histories are whole-run tables.  With (1)–(3), both constructions are
linearizable — at every boundary, as one growing chain, and for the whole,
possibly infinite, event history in the manuscript's own sense
(`causal_infinite_event_linearization`); stated with prefix Validity instead of
(3), over any GCA meeting the manuscript's specification
(`spec_infinite_event_linearization`).

**Algorithm 2 meets the interface** (`Weak.meets_interface`,
`Helping.meets_interface`).

**The prefix reading matters for Algorithm 3.**  `NonCausalWitness` gives a run
of Algorithm 3 over a GCA table satisfying (1) and (2) — every input a proposal
of the run itself — that is not linearizable
(`NonCausalWitness.whole_history_spec_not_enough`).  The table violates Validity
on a prefix, so the manuscript's specification excludes it; the whole-run
reading alone does not.  Helping is what makes the difference: a slow helper can
propose, to an old round, a command invoked after another process already
returned a value computed from it.

**Algorithm 1 does not need the prefix reading**, as long as the GCA history is
the run's own (`Execution.Covers`): without helping, the whole-run properties
alone make every returned command an invoked one
(`WeakUniversal.Execution.returnsInvokedBy_of_covers`, and
`covered_infinite_event_linearization`).
-/
namespace ConflictFreedom

namespace WeakUniversal
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- **Algorithm 1 over any GCA meeting the interface**, in the manuscript's own
definition, for every finite prefix of the run's event history. -/
theorem Execution.causal_event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hgca : run.CausalGCA obj) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ k, k ≤ N → ∀ a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).EventLinearizable Command.process ((run.ledgerRun obj).history resp N) :=
  run.event_linearization obj coverage spec (run.returnsInvokedBy_of_causalGCA obj hgca) N

/-- …and for the whole, possibly infinite, event history. -/
theorem Execution.causal_infinite_event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hgca : run.CausalGCA obj) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).InfEventLinearizable Command.process ((run.ledgerRun obj).events resp) :=
  run.infinite_event_linearization obj coverage spec (run.returnsInvokedBy_of_causalGCA obj hgca)

/-- **Algorithm 1 over any GCA meeting its specification in every execution** —
the six properties of the whole run and Validity of every prefix — has a
linearizable whole event history. -/
theorem Execution.spec_infinite_event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hpre : ∀ r T, (run.prefixHistory obj r T).Validity) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).InfEventLinearizable Command.process ((run.ledgerRun obj).events resp) :=
  run.causal_infinite_event_linearization obj coverage spec
    (run.causalGCA_of_prefixValidity obj hpre)

/-- **Algorithm 1 over any GCA meeting the six properties whose history is the
run's own**: no temporal condition, and the whole event history is
linearizable. -/
theorem Execution.covered_infinite_event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (hcov : run.Covers obj) (spec : ∀ r, (H (r + 1)).Specification) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).InfEventLinearizable Command.process ((run.ledgerRun obj).events resp) :=
  run.infinite_event_linearization obj (run.callsCovered obj hcov) spec
    (run.returnsInvokedBy_of_covers obj hcov spec)

end WeakUniversal

namespace HelpingUniversal
open WeakUniversal (Cmd Tagged Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- **Algorithm 3 over any GCA meeting the interface**, in the manuscript's own
definition, for every finite prefix of the run's event history. -/
theorem Execution.causal_event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hgca : run.CausalGCA obj) (N : Nat) :
    ∃ resp : Cmd n Op → Response,
      (∀ k, k ≤ N → ∀ a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).EventLinearizable Command.process ((run.ledgerRun obj).history resp N) :=
  run.event_linearization obj coverage spec (run.returnsInvokedBy_of_causalGCA obj hgca) N

/-- …and for the whole, possibly infinite, event history. -/
theorem Execution.causal_infinite_event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hgca : run.CausalGCA obj) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).InfEventLinearizable Command.process ((run.ledgerRun obj).events resp) :=
  run.infinite_event_linearization obj coverage spec (run.returnsInvokedBy_of_causalGCA obj hgca)

/-- **Algorithm 3 over any GCA meeting its specification in every execution** has
a linearizable whole event history. -/
theorem Execution.spec_infinite_event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hpre : ∀ r T, (run.prefixHistory obj r T).Validity) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).InfEventLinearizable Command.process ((run.ledgerRun obj).events resp) :=
  run.causal_infinite_event_linearization obj coverage spec
    (run.causalGCA_of_prefixValidity obj hpre)

end HelpingUniversal

namespace GlobalSchedule
open WeakUniversal (Cmd Tagged)
variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {f : UniversalProtocol.Family (n := n) obj}

/-- **The composed Algorithm 2 meets the GCA interface**, for Algorithm 1: the
six properties in every round, coverage of the inputs by the run's proposals,
and causal validity. -/
theorem Weak.meets_interface (g : Weak obj f) :
    (∀ r, (f.environment obj (r + 1)).Specification) ∧
      WeakUniversal.CallsCovered obj (f.environment obj) ∧ g.run.CausalGCA obj :=
  ⟨f.specifications obj, g.composition.callsCovered obj, g.causalGCA⟩

/-- The same for Algorithm 3. -/
theorem Helping.meets_interface (g : Helping obj f) :
    (∀ r, (f.environment obj (r + 1)).Specification) ∧
      HelpingUniversal.CallsCovered obj (f.environment obj) ∧ g.run.CausalGCA obj :=
  ⟨f.specifications obj, g.composition.callsCovered obj, g.causalGCA⟩

end GlobalSchedule
end ConflictFreedom
