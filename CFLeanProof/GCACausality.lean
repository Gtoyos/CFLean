import CFLeanProof.ProtocolInterleaving

/-! Causal validity of GCA: an output can only contain occurrences from inputs
whose A publications precede that output. This strengthens whole-history
validity with the event-time information needed for linearizability. -/
namespace ConflictFreedom.GCA
open Object
variable {State Op Response P : Type} {obj : Object State Op Response}
variable [DecidableEq Op]

namespace TimedExecution

/-- Every output occurrence comes from an input published before the output's
finish event, including inputs reached through another process's B snapshot. -/
theorem output_occurrence_before (e : TimedExecution obj P)
    {p : P} {s : obj.Trace} {flag : Bool} {a : Op} {j finish : Nat}
    (ho : e.views.history.output p = some (s, flag))
    (hf : e.finish p = some finish) (ha : j < obj.traceCount a s) :
    ∃ q w, q ∈ e.participants ∧ e.writeA q = some w ∧ w < finish ∧
      j < obj.traceCount a (e.input q) := by
  obtain ⟨_, rfl, _⟩ := (e.views.output_iff p s flag).mp ho
  obtain ⟨S, hS, input, hi, ha⟩ := obj.gcaOutput_validity _ _ a j ha
  have hsource : ∃ q scan, S = e.views.aTraces q ∧
      e.readA q = some scan ∧ scan < finish := by
    rcases hS with hS | hS
    · obtain ⟨b, hb, hbf⟩ := e.finish_after p finish hf
      obtain ⟨w, hw, hwb⟩ := e.readB_after p b hb
      obtain ⟨r, hr, hrw⟩ := e.writeB_after p w hw
      exact ⟨p, r, hS, hr, by omega⟩
    · obtain ⟨q, hq, he⟩ := List.mem_map.mp hS
      obtain ⟨_, w, b, hw, hb, hwb⟩ := (mem_snapshot _ _ _ _).mp hq
      obtain ⟨b', hb', hbf⟩ := e.finish_after p finish hf
      have hbb : b = b' := Option.some.inj (hb.symm.trans hb')
      obtain ⟨r, hr, hrw⟩ := e.writeB_after q w hw
      exact ⟨q, r, he.symm, hr, by omega⟩
  obtain ⟨q, scan, rfl, hscan, hsf⟩ := hsource
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hi
  obtain ⟨hr, w, scan', hw, hscan', hws⟩ := (mem_snapshot _ _ _ _).mp hr
  have hss : scan' = scan := Option.some.inj (hscan'.symm.trans hscan)
  exact ⟨r, w, hr, hw, by omega, ha⟩

end TimedExecution

namespace Protocol
variable [DecidableEq P]

/-- Availability is operational: the process has completed all six stages by
local protocol boundary `T`. Provenance is strictly earlier than that boundary. -/
theorem output_occurrence_before (e : Protocol obj P)
    {p : P} {s : obj.Trace} {flag : Bool} {a : Op} {j T : Nat}
    (ho : e.history.output p = some (s, flag))
    (hready : e.phase T p = 6) (ha : j < obj.traceCount a s) :
    ∃ q w, e.history.input q = some (e.input q) ∧ e.Exits q 0 w ∧
      w < T ∧ j < obj.traceCount a (e.input q) := by
  obtain ⟨finish, hft, hf⟩ := e.crossed (p := p) (k := 5) (t := T) (by omega)
  have hfinish := (e.eventTime_iff p 5 finish).mpr hf
  obtain ⟨q, w, hq, hw, hwf, ha⟩ := e.timed.output_occurrence_before ho hfinish ha
  refine ⟨q, w, ?_, (e.eventTime_iff q 0 w).mp hw, by omega, ha⟩
  classical
  change q ∈ e.participants at hq
  simp only [history, timed, TimedExecution.views, SnapshotExecution.history]
  exact ite_eq_left hq

end Protocol
end ConflictFreedom.GCA

namespace ConflictFreedom.UniversalProtocol.Interleaving
variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {f : Family (n := n) obj}

omit [DecidableEq Op] in
/-- Every local event before the current clock is the projection of a strictly
past global event; clocks cannot skip protocol events. -/
theorem event_before_clock (e : Interleaving obj f) {T r w : Nat}
    (hw : w < e.clock T r) :
    ∃ u p, u < T ∧ e.clock u r = w ∧ e.event u = some (r, p) := by
  induction T with
  | zero => rw [e.initial_clock] at hw; omega
  | succ T ih =>
    by_cases hprev : w < e.clock T r
    · obtain ⟨u, p, hu, hc, he⟩ := ih hprev
      exact ⟨u, p, by omega, hc, he⟩
    · rw [e.clock_next] at hw
      split at hw
      · obtain ⟨p, hp⟩ := ‹∃ p, e.event T = some (r, p)›
        exact ⟨T, p, by omega, by omega, hp⟩
      · omega

end ConflictFreedom.UniversalProtocol.Interleaving
