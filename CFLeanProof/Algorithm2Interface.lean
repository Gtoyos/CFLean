import CFLeanProof.CausalLinearization
import CFLeanProof.WeakConflictForgetting

/-!
# The GCA interface: the manuscript's specification, and Algorithm 2

The universal constructions are proved over **any** GCA objects meeting the
interface (`GlobalSchedule.WeakRun.GCAInterface`,
`GlobalSchedule.HelpingRun.GCAInterface`):

* `spec` — each round's history satisfies the six properties of §4.2;
* `causal` — Validity on every prefix: an output a process receives contains
  only commands of proposals already made to that object;
* `returns` — every correct participant returns: a process that keeps taking
  steps does not stay inside a call for ever;

and, for Theorem `th:WeakUCresolve` only, GCA property 7, Solo agreement
(`GlobalSchedule.WeakRun.SoloAgreement`).

**The interface is implied by the manuscript's specification**
(`WeakRun.gcaInterface_of_prefixSpec`, `HelpingRun.gcaInterface_of_prefixSpec`).
§4.2 requires the six properties "for every execution", so for the history of
every prefix of the run (`Execution.prefixHistory`).  When the tables `H` record
exactly what the run's GCA objects did — every output was received — the whole
history of each round is the history of a long enough prefix
(`Execution.exists_prefixHistory_eq`), and Validity of the prefixes is `causal`
(`causalGCA_of_prefixValidity`).

**Algorithm 2 meets the interface.**  Run above the assumed wait-free snapshot
interface and composed with either construction by one global schedule:

| Requirement | Algorithm 2 | Proof |
| --- | --- | --- |
| six properties | every round is a `GCA.Protocol` | `UniversalProtocol.Family.specifications` |
| Validity on every prefix | a caller receives only after its protocol stages finish | `Weak.causalGCA`, `Helping.causalGCA` |
| calls return | wait-free snapshots, and fairness at the receive | `Weak.callsReturn`, `Helping.callsReturn` |
| Solo agreement | Lemma `GCA_soloagg` on the round's own clock | `Weak.soloAgreement` |

`Weak.toGCA` and `Helping.toGCA` package a schedule with the interface; they
change nothing about the run (`toGCA_toWeakRun`, `toGCA_toHelpingRun` are
`rfl`), so every theorem proved over the interface holds verbatim for the
composition with Algorithm 2, and in particular for the forward machines
(`WeakUniversal.Forward`, `HelpingUniversal.Forward`).

The interface is about one run.  As an implementation that can be run on —
which the existential statements of §7 need — Algorithm 2 is
`ForwardGCA.machine`, and meets the GCA specification and Solo agreement in
every run (`ForwardGCA.machine_isGCA`, `ForwardGCA.machine_soloAgreement`, in
`GCAMachineAlgorithm2`).
-/

namespace ConflictFreedom.GCA.History
variable {State Op Response P : Type} {obj : Object State Op Response}

/-- A GCA history is determined by its inputs and outputs. -/
theorem eq_of_input_output {h₁ h₂ : History obj P} (hi : h₁.input = h₂.input)
    (ho : h₁.output = h₂.output) : h₁ = h₂ := by
  cases h₁; cases h₂; cases hi; cases ho; rfl

end ConflictFreedom.GCA.History

namespace ConflictFreedom.WeakUniversal
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- `p` received an output from round `r`: it left its call to `r` at some
time. -/
def Execution.Received {H : Environment (n := n) obj} (run : Execution obj H)
    (r : Nat) (p : Fin n) : Prop :=
  ∃ u cmd prop, (run.state u).localState p = .waiting cmd r prop ∧
    (run.state (u + 1)).localState p ≠ (run.state u).localState p

/-- **A round's whole history is the history of a long enough prefix**, when
every input was proposed and every output received. -/
theorem Execution.exists_prefixHistory_eq {H : Environment (n := n) obj} (run : Execution obj H)
    (hcov : run.Covers obj) (r : Nat)
    (htight : ∀ p o, (H (r + 1)).output p = some o → run.Received obj (r + 1) p) :
    ∃ T, run.prefixHistory obj (r + 1) T = H (r + 1) := by
  classical
  have hin : ∀ p, ∃ t, ∀ s, (H (r + 1)).input p = some s →
      (⟨r + 1, p, s⟩ : Call (n := n) obj) ∈ (run.state t).calls := by
    intro p
    cases hp : (H (r + 1)).input p with
    | none => exact ⟨0, fun s h => by cases h⟩
    | some s =>
        obtain ⟨t, ht⟩ := hcov r p s hp
        exact ⟨t, fun s' h => by cases h; exact ht⟩
  have hout : ∀ p, ∃ t, ∀ o, (H (r + 1)).output p = some o →
      ∃ u, u < t ∧ ∃ cmd prop, (run.state u).localState p = .waiting cmd (r + 1) prop ∧
        (run.state (u + 1)).localState p ≠ (run.state u).localState p := by
    intro p
    cases hp : (H (r + 1)).output p with
    | none => exact ⟨0, fun o h => by cases h⟩
    | some o =>
        obtain ⟨u, cmd, prop, hl, hne⟩ := htight p o hp
        exact ⟨u + 1, fun o' _ => ⟨u, Nat.lt_succ_self u, cmd, prop, hl, hne⟩⟩
  obtain ⟨T, hT⟩ := fin_bounded n (fun p => Classical.choose (hin p) + Classical.choose (hout p))
  refine ⟨T, GCA.History.eq_of_input_output (funext fun q => ?_) (funext fun q => ?_)⟩
  · show @ite _ _ (Classical.propDecidable _) _ _ = _
    cases hq : (H (r + 1)).input q with
    | none => split <;> rfl
    | some s =>
        have hcall := Classical.choose_spec (hin q) s hq
        rw [ite_eq_left ⟨_, run.calls_mono obj (by have := hT q; omega) hcall, rfl, rfl⟩]
  · show @ite _ _ (Classical.propDecidable _) _ _ = _
    cases hq : (H (r + 1)).output q with
    | none => split <;> rfl
    | some o =>
        obtain ⟨u, hu, cmd, prop, hl, hne⟩ := Classical.choose_spec (hout q) o hq
        rw [ite_eq_left ⟨u, by have := hT q; omega, cmd, prop, hl, hne⟩]

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom.HelpingUniversal
open WeakUniversal (Cmd Tagged Environment Call)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- `p` received an output from round `r`, for Algorithm 3. -/
def Execution.Received {H : Environment (n := n) obj} (run : Execution obj H)
    (r : Nat) (p : Fin n) : Prop :=
  ∃ u cmd prop, (run.state u).localState p = .waiting cmd r prop ∧
    (run.state (u + 1)).localState p ≠ (run.state u).localState p

/-- **A round's whole history is the history of a long enough prefix**, for
Algorithm 3. -/
theorem Execution.exists_prefixHistory_eq {H : Environment (n := n) obj} (run : Execution obj H)
    (hcov : run.Covers obj) (r : Nat)
    (htight : ∀ p o, (H (r + 1)).output p = some o → run.Received obj (r + 1) p) :
    ∃ T, run.prefixHistory obj (r + 1) T = H (r + 1) := by
  classical
  have hin : ∀ p, ∃ t, ∀ s, (H (r + 1)).input p = some s →
      (⟨r + 1, p, s⟩ : Call (n := n) obj) ∈ (run.state t).calls := by
    intro p
    cases hp : (H (r + 1)).input p with
    | none => exact ⟨0, fun s h => by cases h⟩
    | some s =>
        obtain ⟨t, ht⟩ := hcov r p s hp
        exact ⟨t, fun s' h => by cases h; exact ht⟩
  have hout : ∀ p, ∃ t, ∀ o, (H (r + 1)).output p = some o →
      ∃ u, u < t ∧ ∃ cmd prop, (run.state u).localState p = .waiting cmd (r + 1) prop ∧
        (run.state (u + 1)).localState p ≠ (run.state u).localState p := by
    intro p
    cases hp : (H (r + 1)).output p with
    | none => exact ⟨0, fun o h => by cases h⟩
    | some o =>
        obtain ⟨u, cmd, prop, hl, hne⟩ := htight p o hp
        exact ⟨u + 1, fun o' _ => ⟨u, Nat.lt_succ_self u, cmd, prop, hl, hne⟩⟩
  obtain ⟨T, hT⟩ := fin_bounded n (fun p => Classical.choose (hin p) + Classical.choose (hout p))
  refine ⟨T, GCA.History.eq_of_input_output (funext fun q => ?_) (funext fun q => ?_)⟩
  · show @ite _ _ (Classical.propDecidable _) _ _ = _
    cases hq : (H (r + 1)).input q with
    | none => split <;> rfl
    | some s =>
        have hcall := Classical.choose_spec (hin q) s hq
        rw [ite_eq_left ⟨_, run.calls_mono obj (by have := hT q; omega) hcall, rfl, rfl⟩]
  · show @ite _ _ (Classical.propDecidable _) _ _ = _
    cases hq : (H (r + 1)).output q with
    | none => split <;> rfl
    | some o =>
        obtain ⟨u, hu, cmd, prop, hl, hne⟩ := Classical.choose_spec (hout q) o hq
        rw [ite_eq_left ⟨u, by have := hT q; omega, cmd, prop, hl, hne⟩]

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op]

/-- **The manuscript's GCA specification gives the interface**, for Algorithm 1.
Suppose the tables `H` record exactly what the run's GCA objects did — every
output was received by its caller (`no_ghost` already says every input was
proposed) — and that the six properties hold "for every execution", i.e. for the
history of every prefix of the run.  With "every correct participant returns",
the GCA objects meet the interface. -/
theorem WeakRun.gcaInterface_of_prefixSpec {H : WeakUniversal.Environment (n := n) obj}
    (g : WeakRun obj H)
    (htight : ∀ r p o, (H (r + 1)).output p = some o → g.run.Received obj (r + 1) p)
    (hpre : ∀ r T, (g.run.prefixHistory obj r T).Specification)
    (hret : g.CallsReturn) : g.GCAInterface where
  spec r := by
    obtain ⟨T, hT⟩ := g.run.exists_prefixHistory_eq obj
      (fun r p s hi => (g.input_iff_call r p s).mp hi) r (htight r)
    rw [← hT]
    exact hpre (r + 1) T
  causal := g.run.causalGCA_of_prefixValidity obj (fun r T => (hpre r T).validity)
  returns := hret

/-- **The manuscript's GCA specification gives the interface**, for Algorithm 3. -/
theorem HelpingRun.gcaInterface_of_prefixSpec {H : WeakUniversal.Environment (n := n) obj}
    (g : HelpingRun obj H)
    (htight : ∀ r p o, (H (r + 1)).output p = some o → g.run.Received obj (r + 1) p)
    (hpre : ∀ r T, (g.run.prefixHistory obj r T).Specification)
    (hret : g.CallsReturn) : g.GCAInterface where
  spec r := by
    obtain ⟨T, hT⟩ := g.run.exists_prefixHistory_eq obj
      (fun r p s hi => (g.input_iff_call r p s).mp hi) r (htight r)
    rw [← hT]
    exact hpre (r + 1) T
  causal := g.run.causalGCA_of_prefixValidity obj (fun r T => (hpre r T).validity)
  returns := hret

end ConflictFreedom.GlobalSchedule


namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {f : Family (n := n) obj}

namespace Weak
variable (g : Weak obj f)

/-- **Algorithm 2 meets the GCA interface**, composed with Algorithm 1: its six
properties hold in every round, it is causal, and — under fairness at the
receive and the wait-free snapshot assumption — every correct participant
returns. -/
theorem gcaInterface (hfair : g.Fair) (hw : f.SnapshotWaitFree obj) :
    g.toWeakRun.GCAInterface where
  spec := f.specifications obj
  causal := g.causalGCA
  returns := g.callsReturn hfair hw

/-- Algorithm 1 over Algorithm 2, as a run over GCA objects meeting the
interface. -/
def toGCA (hfair : g.Fair) (hw : f.SnapshotWaitFree obj) : WeakGCA obj (f.environment obj) where
  toWeakRun := g.toWeakRun
  gca := g.gcaInterface hfair hw

@[simp] theorem toGCA_toWeakRun (hfair : g.Fair) (hw : f.SnapshotWaitFree obj) :
    (g.toGCA hfair hw).toWeakRun = g.toWeakRun := rfl

end Weak

namespace Helping
variable (g : Helping obj f)

/-- **Algorithm 2 meets the GCA interface**, composed with Algorithm 3. -/
theorem gcaInterface (hfair : g.Fair) (hw : f.SnapshotWaitFree obj) :
    g.toHelpingRun.GCAInterface where
  spec := f.specifications obj
  causal := g.causalGCA
  returns := g.callsReturn hfair hw

/-- Algorithm 3 over Algorithm 2, as a run over GCA objects meeting the
interface. -/
def toGCA (hfair : g.Fair) (hw : f.SnapshotWaitFree obj) :
    HelpingGCA obj (f.environment obj) where
  toHelpingRun := g.toHelpingRun
  gca := g.gcaInterface hfair hw

@[simp] theorem toGCA_toHelpingRun (hfair : g.Fair) (hw : f.SnapshotWaitFree obj) :
    (g.toGCA hfair hw).toHelpingRun = g.toHelpingRun := rfl

end Helping

end ConflictFreedom.GlobalSchedule
