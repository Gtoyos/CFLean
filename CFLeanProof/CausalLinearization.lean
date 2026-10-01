import CFLeanProof.GCACausality
import CFLeanProof.UniversalProvenance
import CFLeanProof.UniversalLinearization

/-! # The GCA interface, and the causally synchronized constructions

**What the universal constructions need from GCA.**  Linearizability of
Algorithms 1 and 3 uses their GCA objects through three conditions only:

1. each round's history satisfies the six properties of §4.2
   (`(H (r + 1)).Specification`);
2. every input is a proposal the construction makes (`CallsCovered`);
3. **causal validity** (`Execution.CausalGCA`): an output a process receives
   contains only commands of proposals already made to that GCA object.

(3) is not an extra assumption: the manuscript requires the six properties for
every execution, hence for every finite prefix, and Validity of the prefix that
ends with a receive is (3) (`Execution.causalGCA_of_prefixValidity`).  It is
stated separately because the model's GCA histories are whole-run tables, and
`(H r).Specification` checks the properties on the whole run only — a reading
too weak for Algorithm 3 (`NonCausalWitness`).  (3) is what makes every command
of a returned trace an invoked one (`Execution.returnsInvokedBy_of_causalGCA`),
and with it both constructions are linearizable over any GCA meeting the
interface (`Execution.causal_finite_linearization`, `causal_chain_linearization`,
`spec_finite_linearization`).

**Algorithm 2 meets the interface.**  In a global schedule a caller leaves its
wait only after its call has finished on the projected protocol clock
(`receive_ready`) — an operational scheduling rule, not a trace-safety
assumption — and causal validity of the operational protocol
(`GCA.Protocol.output_occurrence_before`) then gives (3): `Weak.causalGCA`,
`Helping.causalGCA`.  (1) is `Family.specifications` and (2) is
`composition.callsCovered`.
-/
namespace ConflictFreedom

/-! ## The causal contract, for any GCA -/

namespace WeakUniversal
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- Over a causal GCA, every trace the program holds consists of commands
invoked so far: proposals are built from invoked commands and held traces, and
a causal output only returns material of earlier proposals. -/
theorem Execution.provenance_of_causalGCA {H : Environment (n := n) obj}
    (run : Execution obj H) (hgca : run.CausalGCA obj) (T : Nat) :
    Provenance obj (fun a => a ∈ (run.state T).invocations) (run.state T) := by
  induction T with
  | zero =>
    rw [run.initial_state]
    exact provenance_initial obj _
  | succ k ih =>
    rcases run.next k with he | hs
    · rw [he]; exact ih
    · refine provenance_step obj hs
        (ih.mono obj (fun a ha => (run.ledgerRun obj).invoked_step ha)) (fun _ ha => ha) ?_
      intro p cmd r proposal s flag hl hchange ho a ha
      obtain ⟨call, hcall, _, hca⟩ := hgca k p cmd r proposal s flag hl hchange ho a ha
      exact (run.ledgerRun obj).invoked_step (ih.calls call hcall a hca)

/-- **The obligation causal validity discharges**: every command of a returned
trace has been invoked. -/
theorem Execution.returnsInvokedBy_of_causalGCA {H : Environment (n := n) obj}
    (run : Execution obj H) (hgca : run.CausalGCA obj) : run.ReturnsInvokedBy obj :=
  fun k ret hr => (run.provenance_of_causalGCA obj hgca k).returns ret hr

/-- **Algorithm 1 over any GCA meeting the interface is linearizable**, at every
finite boundary. -/
theorem Execution.causal_finite_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hgca : run.CausalGCA obj) (N : Nat) :
    ∃ x, (Tagged obj).Linearizes (run.history obj) N x :=
  run.finite_linearization obj coverage spec (run.returnsInvokedBy_of_causalGCA obj hgca) N

/-- …and by one growing chain of sequential orders. -/
theorem Execution.causal_chain_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hgca : run.CausalGCA obj) :
    ∃ x : Nat → List (Cmd n Op),
      (∀ N, (Tagged obj).Linearizes (run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :=
  run.chain_linearization obj coverage spec (run.returnsInvokedBy_of_causalGCA obj hgca)

/-! ### The contract is the manuscript's Validity, on every prefix

The manuscript requires the six properties of GCA for every execution, so in
particular for the finite prefix of an execution that ends when an output is
received.  `prefixHistory r T` is round `r`'s history in the prefix up to time
`T`: the proposals made by `T`, and the outputs received by `T`.  Validity of
these prefix histories is causal validity (`causalGCA_of_prefixValidity`); the
whole-run table `H` alone, which is all `(H r).Specification` inspects, does not
see it. -/

/-- Calls are never withdrawn. -/
theorem step_calls_mono {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) {call : Call (n := n) obj} (h : call ∈ c.calls) : call ∈ d.calls := by
  cases hs with
  | propose => exact List.mem_cons_of_mem _ h
  | _ => exact h

theorem Execution.calls_mono {H : Environment (n := n) obj} (run : Execution obj H)
    {u t : Nat} (hut : u ≤ t) {call : Call (n := n) obj} (h : call ∈ (run.state u).calls) :
    call ∈ (run.state t).calls := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hut
  clear hut
  induction d with
  | zero => exact h
  | succ d ih =>
    rw [← Nat.add_assoc]
    rcases run.next (u + d) with he | hs
    · rw [he]; exact ih
    · exact step_calls_mono obj hs ih

/-- Only a receive leaves a wait, and it records no call. -/
theorem step_receive_calls {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) {p : Fin n} {cmd : Cmd n Op} {r : Nat}
    {prop : (Tagged (n := n) obj).Trace} (hl : c.localState p = .waiting cmd r prop)
    (hchange : d.localState p ≠ c.localState p) : d.calls = c.calls := by
  cases hs with
  | propose q cmd' seed h hi =>
    exfalso; apply hchange
    by_cases hq : p = q
    · subst hq; rw [hl] at h; cases h
    · simp [update, hq]
  | _ => rfl

/-- **GCA round `r` in the prefix of the run up to time `T`**: the participants
that have proposed to `r` by `T`, with their proposals, and the outputs received
by `T`. -/
noncomputable def Execution.prefixHistory {H : Environment (n := n) obj} (run : Execution obj H)
    (r T : Nat) : GCA.History (Tagged (n := n) obj) (Fin n) where
  input q := @ite _ (∃ call ∈ (run.state T).calls, call.round = r ∧ call.process = q)
    (Classical.propDecidable _) ((H r).input q) none
  output q := @ite _ (∃ u, u < T ∧ ∃ cmd prop, (run.state u).localState q = .waiting cmd r prop ∧
      (run.state (u + 1)).localState q ≠ (run.state u).localState q)
    (Classical.propDecidable _) ((H r).output q) none
  returned_invoked := by
    intro q t c h
    by_cases hrec : ∃ u, u < T ∧ ∃ cmd prop, (run.state u).localState q = .waiting cmd r prop ∧
        (run.state (u + 1)).localState q ≠ (run.state u).localState q
    · obtain ⟨u, hu, cmd, prop, hl, _⟩ := hrec
      have hcall := (waiting_call obj (run.reachable obj u) q cmd r prop hl).1
      refine ⟨prop, ?_⟩
      rw [ite_eq_left ⟨⟨r, q, prop⟩, run.calls_mono obj (Nat.le_of_lt hu) hcall, rfl, rfl⟩]
      exact call_input obj (run.reachable obj u) _ hcall
    · rw [ite_eq_right hrec] at h; cases h

/-- **Validity of every prefix is causal validity.**  Applied to the prefix that
ends with a receive, Validity says the received output contains only commands
of proposals made before it. -/
theorem Execution.causalGCA_of_prefixValidity {H : Environment (n := n) obj}
    (run : Execution obj H) (hpre : ∀ r T, (run.prefixHistory obj r T).Validity) :
    run.CausalGCA obj := by
  intro T p cmd r proposal s flag hl hchange ho a ha
  have hout : (run.prefixHistory obj r (T + 1)).output p = some (s, flag) := by
    unfold Execution.prefixHistory
    dsimp only
    rw [ite_eq_left ⟨T, Nat.lt_succ_self T, cmd, proposal, hl, hchange⟩]
    exact ho
  obtain ⟨s', ⟨q, hq⟩, hocc⟩ := (hpre r (T + 1)).occurs p s flag hout a 0
    (by change 0 < ((Tagged obj).traceResponses a _ _).length
        rw [(Tagged obj).traceResponses_length]; exact ha)
  unfold Execution.prefixHistory at hq
  dsimp only at hq
  by_cases hin : ∃ call ∈ (run.state (T + 1)).calls, call.round = r ∧ call.process = q
  · rw [ite_eq_left hin] at hq
    obtain ⟨call, hcall, hround, hproc⟩ := hin
    have htr := call_input obj (run.reachable obj (T + 1)) call hcall
    rw [hround, hproc, hq] at htr
    have hcalls : (run.state (T + 1)).calls = (run.state T).calls := by
      rcases run.next T with he | hs
      · rw [he]
      · exact step_receive_calls obj hs hl hchange
    refine ⟨call, hcalls ▸ hcall, hround, ?_⟩
    rw [← Option.some.inj htr]
    have := hocc
    change 0 < ((Tagged obj).traceResponses a _ _).length at this
    rwa [(Tagged obj).traceResponses_length] at this
  · rw [ite_eq_right hin] at hq; cases hq

/-- **Algorithm 1 over any GCA meeting its specification in every execution** —
the six properties of the whole run, and Validity of every prefix — is
linearizable, at every finite boundary. -/
theorem Execution.spec_finite_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hpre : ∀ r T, (run.prefixHistory obj r T).Validity) (N : Nat) :
    ∃ x, (Tagged obj).Linearizes (run.history obj) N x :=
  run.causal_finite_linearization obj coverage spec (run.causalGCA_of_prefixValidity obj hpre) N

end WeakUniversal

namespace HelpingUniversal
open WeakUniversal (Cmd Tagged Environment Call)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

theorem Execution.provenance_of_causalGCA {H : Environment (n := n) obj}
    (run : Execution obj H) (hgca : run.CausalGCA obj) (T : Nat) :
    Provenance obj (fun a => a ∈ (run.state T).invocations) (run.state T) := by
  induction T with
  | zero =>
    rw [run.initial_state]
    exact provenance_initial obj _
  | succ k ih =>
    rcases run.next k with he | hs
    · rw [he]; exact ih
    · refine provenance_step obj hs
        (ih.mono obj (fun a ha => (run.ledgerRun obj).invoked_step ha)) (fun _ ha => ha) ?_
      intro p cmd r proposal s flag hl hchange ho a ha
      obtain ⟨call, hcall, _, hca⟩ := hgca k p cmd r proposal s flag hl hchange ho a ha
      exact (run.ledgerRun obj).invoked_step (ih.calls call hcall a hca)

theorem Execution.returnsInvokedBy_of_causalGCA {H : Environment (n := n) obj}
    (run : Execution obj H) (hgca : run.CausalGCA obj) : run.ReturnsInvokedBy obj :=
  fun k ret hr => (run.provenance_of_causalGCA obj hgca k).returns ret hr

/-- **Algorithm 3 over any GCA meeting the interface is linearizable**, at every
finite boundary. -/
theorem Execution.causal_finite_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hgca : run.CausalGCA obj) (N : Nat) :
    ∃ x, (Tagged obj).Linearizes (run.history obj) N x :=
  run.finite_linearization obj coverage spec (run.returnsInvokedBy_of_causalGCA obj hgca) N

/-- …and by one growing chain of sequential orders. -/
theorem Execution.causal_chain_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hgca : run.CausalGCA obj) :
    ∃ x : Nat → List (Cmd n Op),
      (∀ N, (Tagged obj).Linearizes (run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :=
  run.chain_linearization obj coverage spec (run.returnsInvokedBy_of_causalGCA obj hgca)

/-! ### The contract is the manuscript's Validity, on every prefix -/

theorem step_calls_mono {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) {call : Call (n := n) obj} (h : call ∈ c.calls) : call ∈ d.calls := by
  cases hs with
  | propose => exact List.mem_cons_of_mem _ h
  | _ => exact h

theorem Execution.calls_mono {H : Environment (n := n) obj} (run : Execution obj H)
    {u t : Nat} (hut : u ≤ t) {call : Call (n := n) obj} (h : call ∈ (run.state u).calls) :
    call ∈ (run.state t).calls := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hut
  clear hut
  induction d with
  | zero => exact h
  | succ d ih =>
    rw [← Nat.add_assoc]
    rcases run.next (u + d) with he | hs
    · rw [he]; exact ih
    · exact step_calls_mono obj hs ih

/-- Only a receive leaves a wait, and it records no call. -/
theorem step_receive_calls {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) {p : Fin n} {cmd : Cmd n Op} {r : Nat}
    {prop : (Tagged (n := n) obj).Trace} (hl : c.localState p = .waiting cmd r prop)
    (hchange : d.localState p ≠ c.localState p) : d.calls = c.calls := by
  cases hs with
  | propose q cmd' seed commands h hi =>
    exfalso; apply hchange
    by_cases hq : p = q
    · subst hq; rw [hl] at h; cases h
    · simp [WeakUniversal.update, hq]
  | _ => rfl

/-- **GCA round `r` in the prefix of an Algorithm 3 run up to time `T`.** -/
noncomputable def Execution.prefixHistory {H : Environment (n := n) obj} (run : Execution obj H)
    (r T : Nat) : GCA.History (Tagged (n := n) obj) (Fin n) where
  input q := @ite _ (∃ call ∈ (run.state T).calls, call.round = r ∧ call.process = q)
    (Classical.propDecidable _) ((H r).input q) none
  output q := @ite _ (∃ u, u < T ∧ ∃ cmd prop, (run.state u).localState q = .waiting cmd r prop ∧
      (run.state (u + 1)).localState q ≠ (run.state u).localState q)
    (Classical.propDecidable _) ((H r).output q) none
  returned_invoked := by
    intro q t c h
    by_cases hrec : ∃ u, u < T ∧ ∃ cmd prop, (run.state u).localState q = .waiting cmd r prop ∧
        (run.state (u + 1)).localState q ≠ (run.state u).localState q
    · obtain ⟨u, hu, cmd, prop, hl, _⟩ := hrec
      have hcall := (waiting_call obj (run.reachable obj u) q cmd r prop hl).1
      refine ⟨prop, ?_⟩
      rw [ite_eq_left ⟨⟨r, q, prop⟩, run.calls_mono obj (Nat.le_of_lt hu) hcall, rfl, rfl⟩]
      exact call_input obj (run.reachable obj u) _ hcall
    · rw [ite_eq_right hrec] at h; cases h

/-- **Validity of every prefix is causal validity**, for Algorithm 3. -/
theorem Execution.causalGCA_of_prefixValidity {H : Environment (n := n) obj}
    (run : Execution obj H) (hpre : ∀ r T, (run.prefixHistory obj r T).Validity) :
    run.CausalGCA obj := by
  intro T p cmd r proposal s flag hl hchange ho a ha
  have hout : (run.prefixHistory obj r (T + 1)).output p = some (s, flag) := by
    unfold Execution.prefixHistory
    dsimp only
    rw [ite_eq_left ⟨T, Nat.lt_succ_self T, cmd, proposal, hl, hchange⟩]
    exact ho
  obtain ⟨s', ⟨q, hq⟩, hocc⟩ := (hpre r (T + 1)).occurs p s flag hout a 0
    (by change 0 < ((Tagged obj).traceResponses a _ _).length
        rw [(Tagged obj).traceResponses_length]; exact ha)
  unfold Execution.prefixHistory at hq
  dsimp only at hq
  by_cases hin : ∃ call ∈ (run.state (T + 1)).calls, call.round = r ∧ call.process = q
  · rw [ite_eq_left hin] at hq
    obtain ⟨call, hcall, hround, hproc⟩ := hin
    have htr := call_input obj (run.reachable obj (T + 1)) call hcall
    rw [hround, hproc, hq] at htr
    have hcalls : (run.state (T + 1)).calls = (run.state T).calls := by
      rcases run.next T with he | hs
      · rw [he]
      · exact step_receive_calls obj hs hl hchange
    refine ⟨call, hcalls ▸ hcall, hround, ?_⟩
    rw [← Option.some.inj htr]
    have := hocc
    change 0 < ((Tagged obj).traceResponses a _ _).length at this
    rwa [(Tagged obj).traceResponses_length] at this
  · rw [ite_eq_right hin] at hq; cases hq

/-- **Algorithm 3 over any GCA meeting its specification in every execution** is
linearizable, at every finite boundary. -/
theorem Execution.spec_finite_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification)
    (hpre : ∀ r T, (run.prefixHistory obj r T).Validity) (N : Nat) :
    ∃ x, (Tagged obj).Linearizes (run.history obj) N x :=
  run.causal_finite_linearization obj coverage spec (run.causalGCA_of_prefixValidity obj hpre) N

end HelpingUniversal

/-! ## Algorithm 2 meets the contract -/

namespace GlobalSchedule
open WeakUniversal (Cmd Tagged)
variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {f : UniversalProtocol.Family (n := n) obj}

namespace Weak
variable (g : Weak obj f)

/-- Available outputs are supported by proposals held at strictly earlier
global times. This connects protocol event-time validity to this program run. -/
theorem output_occurrence_past {T r : Nat} {p : Fin n}
    {s : (Tagged (n := n) obj).Trace} {flag : Bool} {a : Cmd n Op}
    (ho : (f.environment obj r).output p = some (s, flag))
    (hready : (f.protocol r).phase (g.inter.clock T r) p = 6)
    (ha : 0 < (Tagged obj).traceCount a s) :
    ∃ u q cmd proposal, u < T ∧
      (g.run.state u).localState q = .waiting cmd r proposal ∧
      0 < (Tagged obj).traceCount a proposal := by
  obtain ⟨q, w, hi, hw, hwt, ha⟩ :=
    (f.protocol r).output_occurrence_before ho hready ha
  obtain ⟨u, q', hu, hc, he⟩ := g.inter.event_before_clock hwt
  have hactor := g.inter.actor_matches u r q' he
  rw [hc] at hactor
  have hqq : q = q' := Option.some.inj ((f.protocol r).exits_actor hw |>.symm.trans hactor)
  subst q'
  have hround := (gcaEvent_inv obj he).2
  obtain ⟨cmd, proposal, hlocal⟩ : ∃ cmd proposal,
      (g.run.state u).localState q = .waiting cmd r proposal := by
    cases hl : (g.run.state u).localState q <;> simp [weakRound, hl] at hround
    rename_i cmd round proposal
    exact ⟨cmd, proposal, by simp [hround]⟩
  have hcall := (WeakUniversal.waiting_call obj (g.run.reachable obj u) q cmd r proposal hlocal).1
  have hinput := WeakUniversal.call_input obj (g.run.reachable obj u) _ hcall
  have hprop : (f.protocol r).input q = proposal := Option.some.inj (hi.symm.trans hinput)
  exact ⟨u, q, cmd, proposal, hu, hlocal, by simpa only [hprop] using ha⟩

/-- **The composed Algorithm 2 meets the GCA causal contract.**  A received
output's occurrences come from proposals held at strictly earlier global times
(`output_occurrence_past`), and a held proposal is a recorded call. -/
theorem causalGCA : g.run.CausalGCA obj := by
  intro T p cmd r proposal s flag hl hchange ho a ha
  have hr : weakRound obj ((g.run.state T).localState p) = some r := by
    simp only [hl, weakRound]
  obtain ⟨u, q, cmd', prop', hu, hlocal, hocc⟩ :=
    g.output_occurrence_past ho (g.receive_ready T p r hr hchange) ha
  exact ⟨⟨r, q, prop'⟩, g.calls_mono (Nat.le_of_lt hu)
    (WeakUniversal.waiting_call obj (g.run.reachable obj u) q cmd' r prop' hlocal).1, rfl, hocc⟩

/-- Every trace held by the program contains only commands invoked by this
boundary. -/
theorem provenance (T : Nat) :
    WeakUniversal.Provenance obj (fun a => a ∈ (g.run.state T).invocations) (g.run.state T) :=
  g.run.provenance_of_causalGCA obj g.causalGCA T

/-- Every command in a returned trace has been invoked (`ReturnsInvokedBy`,
the obligation the linearization argument needs) — a theorem of the
operational receive rule, not a hypothesis. -/
theorem returnsInvokedBy : g.run.ReturnsInvokedBy obj :=
  g.run.returnsInvokedBy_of_causalGCA obj g.causalGCA

/-- Finite-history linearizability with only operational scheduling conditions;
no assumed occurrence-provenance or real-time-order invariant remains. -/
theorem finite_linearization (N : Nat) :
    ∃ x, (Tagged obj).Linearizes (g.run.history obj) N x :=
  g.finite_linearization_of_provenance g.returnsInvokedBy N

/-- **Linearizability of the whole run, unconditionally.**  A single sequential
order linearizes every boundary, and it is presented by a chain of literal
prefixes, so no boundary reorders what an earlier one already placed
(`Object.chain_idxOf_stable`).  This is the finite-to-infinite closure. -/
theorem chain_linearization :
    ∃ x : Nat → List (Cmd n Op),
      (∀ N, (Tagged obj).Linearizes (g.run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :=
  g.chain_linearization_of_provenance g.returnsInvokedBy

end Weak

namespace Helping
variable (g : Helping obj f)

/-- Available outputs are supported by proposals held at strictly earlier
global times. This connects protocol event-time validity to this program run. -/
theorem output_occurrence_past {T r : Nat} {p : Fin n}
    {s : (Tagged (n := n) obj).Trace} {flag : Bool} {a : Cmd n Op}
    (ho : (f.environment obj r).output p = some (s, flag))
    (hready : (f.protocol r).phase (g.inter.clock T r) p = 6)
    (ha : 0 < (Tagged obj).traceCount a s) :
    ∃ u q cmd proposal, u < T ∧
      (g.run.state u).localState q = .waiting cmd r proposal ∧
      0 < (Tagged obj).traceCount a proposal := by
  obtain ⟨q, w, hi, hw, hwt, ha⟩ :=
    (f.protocol r).output_occurrence_before ho hready ha
  obtain ⟨u, q', hu, hc, he⟩ := g.inter.event_before_clock hwt
  have hactor := g.inter.actor_matches u r q' he
  rw [hc] at hactor
  have hqq : q = q' := Option.some.inj ((f.protocol r).exits_actor hw |>.symm.trans hactor)
  subst q'
  have hround := (gcaEventH_inv obj he).2
  obtain ⟨cmd, proposal, hlocal⟩ : ∃ cmd proposal,
      (g.run.state u).localState q = .waiting cmd r proposal := by
    cases hl : (g.run.state u).localState q <;> simp [helpingRound, hl] at hround
    rename_i cmd round proposal
    exact ⟨cmd, proposal, by simp [hround]⟩
  have hcall := (HelpingUniversal.waiting_call obj (g.run.reachable obj u) q cmd r proposal hlocal).1
  have hinput := HelpingUniversal.call_input obj (g.run.reachable obj u) _ hcall
  have hprop : (f.protocol r).input q = proposal := Option.some.inj (hi.symm.trans hinput)
  exact ⟨u, q, cmd, proposal, hu, hlocal, by simpa only [hprop] using ha⟩

/-- **The composed Algorithm 2 meets the GCA causal contract**, for Algorithm 3. -/
theorem causalGCA : g.run.CausalGCA obj := by
  intro T p cmd r proposal s flag hl hchange ho a ha
  have hr : helpingRound obj ((g.run.state T).localState p) = some r := by
    simp only [hl, helpingRound]
  obtain ⟨u, q, cmd', prop', hu, hlocal, hocc⟩ :=
    g.output_occurrence_past ho (g.receive_ready T p r hr hchange) ha
  exact ⟨⟨r, q, prop'⟩, g.calls_mono (Nat.le_of_lt hu)
    (HelpingUniversal.waiting_call obj (g.run.reachable obj u) q cmd' r prop' hlocal).1, rfl, hocc⟩

/-- Every trace held by the program contains only commands invoked by this
boundary. -/
theorem provenance (T : Nat) :
    HelpingUniversal.Provenance obj (fun a => a ∈ (g.run.state T).invocations) (g.run.state T) :=
  g.run.provenance_of_causalGCA obj g.causalGCA T

/-- Every command in a returned trace has been invoked (`ReturnsInvokedBy`,
the obligation the linearization argument needs) — a theorem of the
operational receive rule, not a hypothesis. -/
theorem returnsInvokedBy : g.run.ReturnsInvokedBy obj :=
  g.run.returnsInvokedBy_of_causalGCA obj g.causalGCA

/-- Finite-history linearizability with only operational scheduling conditions;
no assumed occurrence-provenance or real-time-order invariant remains. -/
theorem finite_linearization (N : Nat) :
    ∃ x, (Tagged obj).Linearizes (g.run.history obj) N x :=
  g.finite_linearization_of_provenance g.returnsInvokedBy N

/-- **Linearizability of the whole run, unconditionally.**  A single sequential
order linearizes every boundary, and it is presented by a chain of literal
prefixes, so no boundary reorders what an earlier one already placed
(`Object.chain_idxOf_stable`).  This is the finite-to-infinite closure. -/
theorem chain_linearization :
    ∃ x : Nat → List (Cmd n Op),
      (∀ N, (Tagged obj).Linearizes (g.run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :=
  g.chain_linearization_of_provenance g.returnsInvokedBy

end Helping

end GlobalSchedule
end ConflictFreedom
