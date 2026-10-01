import CFLeanProof.UniversalProgress
import CFLeanProof.Scheduling

/-!
# Invariant (I) at the execution level

This module formalizes the second half of the paper's proof of Theorem
`weakUCWCF`, the part that establishes

> (I) for every `r > r_0`, only compatible traces are proposed to `GCA_r`.

The paper's argument is reproduced step for step.  Let `t_i` be the trace `i`
retrieves from `GCA_{r-1}` and `s_i` the trace it proposes to `GCA_r`; by lines
7-8, `s_i = t_i · cmd_i` when `cmd_i ∉ ops(t_i)` and `s_i = t_i` otherwise.  Let
`t = ⊓ 𝒯` be the greatest common prefix of the retrieved traces `𝒯 = {t_i}`
(`Retrieved`) and `t_i = t · u_i`.  If an operation `Φ` has already returned then
`cmd(Φ)` lies in a committed trace, which by the prefix-rounds lemma prefixes
every later output, hence prefixes `t`; since occurrences in an output are
unique, `cmd(Φ)` cannot occur in `u_i` as well.  So the residuals `u_i` and the
commands `cmd_i` all belong to operations that have not returned, and those do
not conflict.
-/

namespace ConflictFreedom.WeakUniversal
open Object
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- A command whose response has been recorded occupies every later committed
trace, hence the common prefix of any set of outputs of a later round. -/
theorem returned_below_glb {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H) (spec : ∀ r, (H (r + 1)).Specification)
    {ret : Return (n := n) obj}
    (hcom : Committed obj H ret.round ret.trace)
    {k : Nat} (hk : ret.round ≤ k + 1)
    {X : (Tagged (n := n) obj).Trace → Prop} (hX : ∀ x, X x → (H (k + 1)).Outputs x)
    {t : (Tagged (n := n) obj).Trace} (ht : (Tagged obj).IsGLB X t) :
    (Tagged obj).TracePrefix ret.trace t := by
  obtain ⟨hpos, q, hq⟩ := hcom
  obtain ⟨r, hr⟩ : ∃ r, ret.round = r + 1 := ⟨ret.round - 1, by omega⟩
  rw [hr] at hq hk
  refine ht.2 ret.trace ?_
  intro x hx
  obtain ⟨p', flag, hx⟩ := hX x hx
  exact committed_prefix obj coverage spec (by omega) hq hx

/-- A step never removes a recorded response. -/
theorem stepBy_returns {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) :
    ∀ ret ∈ c.returns, ret ∈ d.returns := by
  obtain ⟨hstep, -⟩ := h
  cases hstep with
  | finish q cmd r s hq => exact fun ret hret => List.mem_cons_of_mem _ hret
  | _ => exact fun _ h => h

/-- Only `finish` changes the response history. -/
theorem step_records_return {H : Environment (n := n) obj}
    {c d : Configuration (n := n) obj} (h : Step obj H c d)
    (hne : d.returns ≠ c.returns) :
    ∃ p cmd r s, c.localState p = .returning cmd r s ∧
      (⟨cmd, r, s⟩ : Return (n := n) obj) ∈ d.returns := by
  cases h with
  | finish p cmd r s hp => exact ⟨p, cmd, r, s, hp, List.mem_cons_self⟩
  | _ => exact (hne rfl).elim

/-- A step that records a new call leaves the caller waiting in that round. -/
theorem stepBy_new_call {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {call : Call (n := n) obj} (hin : call ∈ d.calls) (hout : call ∉ c.calls) :
    ∃ cmd, d.localState call.process = .waiting cmd call.round call.trace := by
  cases h.1 with
  | propose q cmd seed hq hi =>
      rcases List.mem_cons.mp hin with rfl | hm
      · exact ⟨cmd, by simp [update]⟩
      · exact absurd hm hout
  | _ => exact absurd hin hout

/-- A step that records a new call fires from the caller's `ready` state, and
the recorded call is exactly the proposal built there at Lines 7-8. -/
theorem stepBy_new_call_source {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {call : Call (n := n) obj} (hin : call ∈ d.calls) (hout : call ∉ c.calls) :
    ∃ cmd seed, c.localState call.process = .ready cmd seed ∧
      call.round = seed.round + 1 ∧
      call.trace = (Tagged obj).appendMissing seed.trace cmd := by
  cases h.1 with
  | propose q cmd seed hq hi =>
      rcases List.mem_cons.mp hin with rfl | hm
      · exact ⟨cmd, seed, hq, rfl, rfl⟩
      · exact absurd hm hout
  | _ => exact absurd hin hout

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace WeakRun
variable (g : WeakRun obj H)

/-- A command invoked by this particular scheduled run.  This must be
run-relative: existential reachability would include commands from alternative
executions and make the eventual nonconflict hypothesis unsatisfiable. -/
def Invoked (a : WeakUniversal.Cmd n Op) : Prop :=
  ∃ t, a ∈ (g.run.state t).invocations

/-- The paper's "operations that have already returned", relative to a round. -/
def ReturnedBy (k : Nat) (a : WeakUniversal.Cmd n Op) : Prop :=
  ∃ t, ∃ ret ∈ (g.run.state t).returns, ret.command = a ∧ ret.round ≤ k + 1

/-- **The manuscript's hypothesis, over time.**  §3 defines an execution to be
*eventually conflict-free* when some suffix contains no two conflicting
*concurrent* operations.  Transported to the program run: beyond `T₀`, two
distinct commands that are simultaneously invoked-and-unanswered do not
conflict.  This is exactly what `Execution.EventuallyConflictFree` says about
the extracted execution -- see `InvocationLedger.Schedule.execution_eventuallyConflictFree_iff`
and `eventuallyNonconflicting_of_execution` below.

The round-indexed `Pending k` used by `proposal_shape` is a *different*, in
general stronger, condition; `nonconflicting_pending_of_eventually` derives it
from this one in the situation the manuscript's proof is in, namely after the
response history has frozen. -/
def EventuallyNonconflicting (T₀ : Nat) : Prop :=
  ∀ t, T₀ ≤ t → ∀ a b : WeakUniversal.Cmd n Op,
    a ∈ (g.run.state t).invocations →
    (∀ ret ∈ (g.run.state t).returns, ret.command ≠ a) →
    b ∈ (g.run.state t).invocations →
    (∀ ret ∈ (g.run.state t).returns, ret.command ≠ b) →
    a ≠ b → (WeakUniversal.Tagged obj).Independent a b

/-- The paper's "pending operations": invoked, and not returned by round
`k + 1`.  Commands that were never invoked are deliberately excluded -- the
conflict-freedom hypothesis is about operations of the execution, not about
every operation the object admits. -/
def Pending (k : Nat) (a : WeakUniversal.Cmd n Op) : Prop :=
  g.Invoked a ∧ ¬ g.ReturnedBy k a

/-- **The manuscript's hypothesis implies the round-indexed one, in the setting
the manuscript's proof is in.**

`th:weakUCWCF` argues at a time `τ'` after which "all their operations are
pending forever", i.e. after which the response history no longer changes.
There, a command that is not returned *at a round below the bound* is not
returned *at all* after `τ'`, so any two such commands are simultaneously
pending at a late enough time and the §3 hypothesis applies to them directly.
No global bound on invocation times is needed: the witnessing time is chosen
per pair. -/
theorem nonconflicting_pending_of_eventually {T₀ T : Nat}
    (hC : g.EventuallyNonconflicting T₀)
    (hfrozen : ∀ t, T ≤ t → (g.run.state t).returns = (g.run.state T).returns)
    {k : Nat} (hk : ∀ ret ∈ (g.run.state T).returns, ret.round ≤ k + 1) :
    (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k) := by
  classical
  intro a b ha hb hab
  obtain ⟨ta, hta⟩ := ha.1
  obtain ⟨tb, htb⟩ := hb.1
  have hnr : ∀ c : WeakUniversal.Cmd n Op, ¬ g.ReturnedBy k c →
      ∀ ret ∈ (g.run.state T).returns, ret.command ≠ c := by
    intro c hc ret hret he
    exact hc ⟨T, ret, hret, he, hk ret hret⟩
  refine hC (max (max ta tb) (max T₀ T)) (by omega) a b ?_ ?_ ?_ ?_ hab
  · exact (g.run.ledgerRun obj).invoked_mono (by omega) hta
  · rw [hfrozen _ (by omega)]; exact hnr a ha.2
  · exact (g.run.ledgerRun obj).invoked_mono (by omega) htb
  · rw [hfrozen _ (by omega)]; exact hnr b hb.2

/-- The step at which a call is recorded: at `u` its caller is in the `ready`
state the proposal is built from (Lines 6–9), and the call appears at `u + 1`. -/
theorem call_proposed {t' : Nat} {call : WeakUniversal.Call (n := n) obj}
    (h : call ∈ (g.run.state t').calls) :
    ∃ u cmd seed, call ∉ (g.run.state u).calls ∧ call ∈ (g.run.state (u + 1)).calls ∧
      (g.run.state u).localState call.process = .ready cmd seed ∧
      call.round = seed.round + 1 ∧
      call.trace = (WeakUniversal.Tagged obj).appendMissing seed.trace cmd := by
  classical
  induction t' with
  | zero => rw [g.run.initial_state] at h; simp [WeakUniversal.initial] at h
  | succ t ih =>
      by_cases hprev : call ∈ (g.run.state t).calls
      · exact ih hprev
      · rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
        · rw [heq] at h; exact absurd h hprev
        · obtain ⟨cmd, seed, hsrc, hr, htr⟩ :=
            WeakUniversal.stepBy_new_call_source obj hstep h hprev
          exact ⟨t, cmd, seed, hprev, h, hsrc, hr, htr⟩
        · rw [heq] at h; exact absurd h hprev

/-- The manuscript's `t_i` for round `k + 2`: `b` is the trace a process
retrieved from round `k + 1` — its local `(r, s) = (k + 1, b)` — at the step
`u` at which it proposes to round `k + 2` the trace built from `b`. -/
def Retrieved (k : Nat) (b : (WeakUniversal.Tagged (n := n) obj).Trace) : Prop :=
  ∃ u cmd, ∃ call : WeakUniversal.Call (n := n) obj,
    call ∉ (g.run.state u).calls ∧ call ∈ (g.run.state (u + 1)).calls ∧
    (g.run.state u).localState call.process = .ready cmd ⟨k + 1, b⟩ ∧
    call.round = k + 2 ∧ call.trace = (WeakUniversal.Tagged obj).appendMissing b cmd

/-- A retrieved trace is an output of the previous round. -/
theorem retrieved_output {k : Nat} {b : (WeakUniversal.Tagged (n := n) obj).Trace}
    (h : g.Retrieved k b) : (H (k + 1)).Outputs b := by
  obtain ⟨u, cmd, call, -, -, hL, -, -⟩ := h
  have hsup : WeakUniversal.Supported obj H ⟨k + 1, b⟩ := by
    simpa only [hL, WeakUniversal.LocalInvariant] using
      (WeakUniversal.invariant obj (g.run.reachable obj u)).localState call.process
  rcases hsup with ⟨h0, -⟩ | ⟨-, q, flag, hq⟩
  · exact absurd h0 (Nat.succ_ne_zero k)
  · exact ⟨q, flag, hq⟩

/-- Every proposal to round `k + 2` is built from a retrieved trace, by its
caller's current command (Lines 7–8). -/
theorem input_retrieved {k : Nat} {p : Fin n} {s : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hs : (H (k + 2)).input p = some s) :
    ∃ b u cmd, g.Retrieved k b ∧
      (g.run.state u).localState p = .ready cmd ⟨k + 1, b⟩ ∧
      s = (WeakUniversal.Tagged obj).appendMissing b cmd := by
  obtain ⟨t', hcall⟩ := (g.input_iff_call (k + 1) p s).mp hs
  obtain ⟨u, cmd, seed, hno, hyes, hL, hr, htr⟩ := g.call_proposed hcall
  obtain ⟨sr, st⟩ := seed
  obtain rfl : sr = k + 1 := by simp only at hr; omega
  exact ⟨st, u, cmd, ⟨u, cmd, _, hno, hyes, hL, rfl, htr⟩, hL, htr⟩

/-- A round with a caller has a retrieved trace. -/
theorem retrieved_nonempty {k : Nat} (h : ∃ s, (H (k + 2)).Inputs s) :
    ∃ b, g.Retrieved k b := by
  obtain ⟨s, p, hp⟩ := h
  obtain ⟨b, -, -, hb, -⟩ := g.input_retrieved hp
  exact ⟨b, hb⟩

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H)

private theorem appendMissing_source
    (s : (WeakUniversal.Tagged (n := n) obj).Trace)
    (a cmd : WeakUniversal.Cmd n Op)
    (h : 0 < (WeakUniversal.Tagged obj).traceCount a
      ((WeakUniversal.Tagged obj).appendMissing s cmd)) :
    a = cmd ∨ 0 < (WeakUniversal.Tagged obj).traceCount a s := by
  by_cases he : a = cmd
  · exact Or.inl he
  · right
    by_cases hz : (WeakUniversal.Tagged obj).traceCount cmd s = 0
    · simp only [Object.appendMissing, hz, ↓reduceIte] at h
      let one : (WeakUniversal.Tagged (n := n) obj).Trace :=
        Quotient.mk (WeakUniversal.Tagged obj).traceSetoid [cmd]
      change 0 < (WeakUniversal.Tagged obj).traceCount a
        ((WeakUniversal.Tagged obj).traceAppend s one) at h
      rw [(WeakUniversal.Tagged obj).traceCount_append a s one] at h
      have hsingle : (WeakUniversal.Tagged obj).traceCount a one = 0 := by
        change [cmd].count a = 0
        simp [Ne.symm he]
      omega
    · simpa [Object.appendMissing, hz] using h

/-- Every command in a protocol output originated in an invocation of this
run.  Validity sends an occurrence to an input of the same round; exact
input/call correspondence then sends it to a recorded call in this run. -/
theorem output_occurrence_invoked :
    ∀ r p t flag a,
      (H (r + 1)).output p = some (t, flag) →
      0 < (WeakUniversal.Tagged obj).traceCount a t → g.Invoked a := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro p t flag a hout hpos
    have hocc : GCA.History.Occurs (obj := WeakUniversal.Tagged (n := n) obj) a 0 t := by
      simpa only [GCA.History.Occurs,
        (WeakUniversal.Tagged obj).traceResponses_length] using hpos
    obtain ⟨s, ⟨q, hinput⟩, hsocc⟩ :=
      (g.gca.spec r).validity.occurs p t flag hout a 0 hocc
    have hspos : 0 < (WeakUniversal.Tagged obj).traceCount a s := by
      simpa only [GCA.History.Occurs,
        (WeakUniversal.Tagged obj).traceResponses_length] using hsocc
    obtain ⟨u, hcall⟩ := (g.input_iff_call r q s).mp hinput
    obtain ⟨cmd, hcmd, seed, hseed, _, hround, htrace⟩ :=
      WeakUniversal.call_origin obj (g.run.reachable obj u) hcall
    change s = (WeakUniversal.Tagged obj).appendMissing seed.trace cmd at htrace
    rw [htrace] at hspos
    rcases appendMissing_source (obj := obj) seed.trace a cmd hspos with he | hbase
    · exact ⟨u, he ▸ hcmd⟩
    · rcases hseed with ⟨_, hempty⟩ | ⟨hpositive, q', b, hprev⟩
      · rw [hempty] at hbase
        change 0 < ([] : List (WeakUniversal.Cmd n Op)).count a at hbase
        simp at hbase
      · have hround' : r + 1 = seed.round + 1 := by simpa using hround
        have hseedr : seed.round = r := by omega
        have hrpos : 0 < r := by omega
        obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        have hprev' : (H (k + 1)).output q' =
            some (seed.trace, b) := by
          simpa only [hseedr, hk] using hprev
        exact ih k (by omega) q' seed.trace b a hprev' hbase

/-- **Invariant (I), one proposal.**  Let `t = ⊓ 𝒯` be the greatest common
prefix of the traces `t_i` retrieved from round `k + 1` by the processes
proposing to round `k + 2`, and `t_i = t · u_i`.  Every proposal `s_i` is
`t_i` or `t_i · cmd_i`, so it is `t` extended by commands of operations that
have not returned: a returned command lies in a committed trace, which prefixes
every `t_i` (`lemma:prefix-rounds`), hence `t`. -/
theorem proposal_shape
    (coverage : WeakUniversal.CallsCovered obj (H))
    {k : Nat} {t : (WeakUniversal.Tagged (n := n) obj).Trace}
    (ht : (WeakUniversal.Tagged obj).IsGLB (g.Retrieved k) t)
    {s : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hs : (H (k + 2)).Inputs s) :
    ∃ w : List (WeakUniversal.Cmd n Op),
      (∀ a ∈ w, g.Pending k a ∧ (WeakUniversal.Tagged obj).traceCount a t = 0) ∧
      s = (WeakUniversal.Tagged obj).traceAppend t (Quotient.mk _ w) := by
  classical
  obtain ⟨p, hp⟩ := hs
  -- the trace `t_p` that `p` retrieved, an output of round `k + 1`
  obtain ⟨b, t', cmd, hb, hL, hshape'⟩ := g.input_retrieved hp
  have hcmd : cmd ∈ (g.run.state t').invocations :=
    ((WeakUniversal.identity_invariant obj (g.run.reachable obj t')).active_tag p cmd
      (by simp [WeakUniversal.ledger, hL, WeakUniversal.Local.command])).2.2
  obtain ⟨q, flag, hq⟩ := g.retrieved_output hb
  -- the common prefix sits below it
  obtain ⟨v, hv⟩ := ((WeakUniversal.Tagged obj).tracePrefix_iff_append t b).mp (ht.1 b hb)
  obtain ⟨w0, hw0⟩ := Quotient.exists_rep v
  -- occurrences in an output are unique
  have hle1 : ∀ a, (WeakUniversal.Tagged obj).traceCount a b ≤ 1 :=
    fun a => WeakUniversal.output_count_le_one obj coverage (g.gca.spec) k q b flag a hq
  -- a returned command already sits in the common prefix
  have hret_t : ∀ a, g.ReturnedBy k a → 0 < (WeakUniversal.Tagged obj).traceCount a t := by
    rintro a ⟨t₀, ret, hmem, rfl, hrk⟩
    obtain ⟨hcom, hcount⟩ := (WeakUniversal.invariant obj (g.run.reachable obj t₀)).returns ret hmem
    exact Nat.lt_of_lt_of_le hcount
      ((WeakUniversal.Tagged obj).traceCount_mono
        (WeakUniversal.returned_below_glb obj coverage (g.gca.spec) hcom hrk
          (fun x hx => g.retrieved_output hx) ht) _)
  -- hence a returned command never occurs in the residual
  have hres : ∀ a ∈ w0, g.Pending k a ∧
      (WeakUniversal.Tagged obj).traceCount a t = 0 := by
    intro a ha
    have h2 : 0 < w0.count a := List.count_pos_iff.mpr ha
    have h3 : (WeakUniversal.Tagged obj).traceCount a b
        = (WeakUniversal.Tagged obj).traceCount a t + w0.count a := by
      rw [hv, ← hw0]
      exact (WeakUniversal.Tagged obj).traceCount_append a t (Quotient.mk _ w0)
    have hle := hle1 a
    refine ⟨⟨g.output_occurrence_invoked k q b flag a hq (by omega), ?_⟩, by omega⟩
    intro hbad
    have h1 : 0 < (WeakUniversal.Tagged obj).traceCount a t := hret_t a hbad
    omega
  by_cases hc : (WeakUniversal.Tagged obj).traceCount cmd b = 0
  · refine ⟨w0 ++ [cmd], ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hres a h
      · rw [List.mem_singleton.mp h]
        have hmono : (WeakUniversal.Tagged obj).traceCount cmd t
            ≤ (WeakUniversal.Tagged obj).traceCount cmd b :=
          (WeakUniversal.Tagged obj).traceCount_mono (ht.1 b hb) _
        refine ⟨⟨⟨t', hcmd⟩, ?_⟩, by omega⟩
        intro hbad
        have := hret_t cmd hbad
        omega
    · have h1 : (WeakUniversal.Tagged obj).appendMissing b cmd
          = (WeakUniversal.Tagged obj).traceAppend b (Quotient.mk _ [cmd]) := by
        simp [Object.appendMissing, hc]
      rw [hshape', h1, hv, ← hw0]
      exact ((WeakUniversal.Tagged obj).traceAppend_assoc t (Quotient.mk _ w0)
        (Quotient.mk _ [cmd])).trans (by rw [(WeakUniversal.Tagged obj).traceAppend_mk])
  · refine ⟨w0, hres, ?_⟩
    have h1 : (WeakUniversal.Tagged obj).appendMissing b cmd = b := by
      simp [Object.appendMissing, hc]
    rw [hshape', h1, hv, ← hw0]

end WeakGCA

namespace WeakRun
variable (g : WeakRun obj H)

/-- Every recorded call was made from a `waiting` state of its caller. -/
theorem call_was_waiting {t' : Nat} {call : WeakUniversal.Call (n := n) obj}
    (h : call ∈ (g.run.state t').calls) :
    ∃ u cmd, (g.run.state u).localState call.process
      = .waiting cmd call.round call.trace := by
  classical
  induction t' with
  | zero => rw [g.run.initial_state] at h; simp [WeakUniversal.initial] at h
  | succ t ih =>
      by_cases hprev : call ∈ (g.run.state t).calls
      · exact ih hprev
      · rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
        · rw [heq] at h; exact absurd h hprev
        · obtain ⟨cmd, hcmd⟩ := WeakUniversal.stepBy_new_call obj hstep h hprev
          exact ⟨t + 1, cmd, hcmd⟩
        · rw [heq] at h; exact absurd h hprev

/-- A call that was not yet recorded at time `T` was made from a `waiting` state
at or after `T`. -/
theorem call_was_waiting_after {T t' : Nat} {call : WeakUniversal.Call (n := n) obj}
    (h : call ∈ (g.run.state t').calls) (hT : call ∉ (g.run.state T).calls) :
    ∃ u, T ≤ u ∧ ∃ cmd, (g.run.state u).localState call.process
      = .waiting cmd call.round call.trace := by
  classical
  induction t' with
  | zero => rw [g.run.initial_state] at h; simp [WeakUniversal.initial] at h
  | succ t ih =>
      by_cases hprev : call ∈ (g.run.state t).calls
      · exact ih hprev
      · have hTt : T ≤ t + 1 := by
          refine Nat.le_of_not_lt (fun hlt => hT ?_)
          exact g.calls_mono (by omega) h
        rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
        · rw [heq] at h; exact absurd h hprev
        · obtain ⟨cmd, hcmd⟩ := WeakUniversal.stepBy_new_call obj hstep h hprev
          exact ⟨t + 1, hTt, cmd, hcmd⟩
        · rw [heq] at h; exact absurd h hprev

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H)

/-- A process waiting on a round whose output commits its own command reaches
the point of returning. -/
theorem waiting_committed_returns {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    {u : Nat} {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {prop : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hL : (g.run.state u).localState p = .waiting cmd r prop)
    (hcommit : ∀ x flag, (H r).output p = some (x, flag) →
      flag = true ∧ 0 < (WeakUniversal.Tagged obj).traceCount cmd x) :
    ∃ w x, (g.run.state w).localState p = .returning cmd r x := by
  obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched u
  obtain ⟨x, flag, hout, hnew⟩ :=
    WeakUniversal.stepBy_from_waiting obj hstep (hconst.trans hL)
  obtain ⟨hflag, hcount⟩ := hcommit x flag hout
  subst hflag
  have hnew' : (g.run.state (v + 1)).localState p = .publishing cmd r x := by
    rw [hnew]
    split
    · rfl
    · rename_i hneg
      exact absurd ⟨rfl, hcount⟩ hneg
  obtain ⟨w, hw2, hconst2, hstep2⟩ := g.next_step hsched (v + 1)
  exact ⟨w + 1, x, WeakUniversal.stepBy_from_publishing obj hstep2 (hconst2.trans hnew')⟩

end WeakGCA

namespace WeakRun
variable (g : WeakRun obj H)

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H)

/-- A caller that keeps taking steps gets an output from the round it called:
either it is still inside the call, and the call returns under the snapshot
assumption, or it has already taken its `receive` step, which required the
output. -/
theorem caller_returns {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    {u : Nat} {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {prop : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hL : (g.run.state u).localState p = .waiting cmd r prop) :
    ∃ y flag, (H r).output p = some (y, flag) := by
  obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched u
  obtain ⟨y, flag, hout, -⟩ :=
    WeakUniversal.stepBy_from_waiting obj hstep (hconst.trans hL)
  exact ⟨y, flag, hout⟩

/-- Every caller of a round that keeps taking steps returns from it. -/
theorem allReturned {k : Nat}
    (hsched : ∀ p, (∃ s, (H (k + 2)).input p = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    (H (k + 2)).AllReturned := by
  intro p s hin
  obtain ⟨t', hcall⟩ := (g.input_iff_call (k + 1) p s).mp hin
  obtain ⟨u, cmd, hL⟩ := g.call_was_waiting hcall
  exact g.caller_returns (hsched p ⟨s, hin⟩) hL

/-- **Invariant (I).**  If the commands of operations that have not returned
pairwise do not conflict -- the paper's eventual conflict-freedom -- then only
compatible traces are proposed to round `k + 2`: each is `t = ⊓ 𝒯` extended by
such commands (`proposal_shape`). -/
theorem inputs_compatible_at
    (coverage : WeakUniversal.CallsCovered obj (H)) {k : Nat}
    {t : (WeakUniversal.Tagged (n := n) obj).Trace}
    (ht : (WeakUniversal.Tagged obj).IsGLB (g.Retrieved k) t)
    (hC : (WeakUniversal.Tagged obj).Nonconflicting
      (fun a => g.Pending k a ∧ (WeakUniversal.Tagged obj).traceCount a t = 0)) :
    (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs := by
  classical
  refine (H (k + 2)).inputs_compatible_of_pending_proposals hC t
    ((List.finRange n).filterMap (fun p => (H (k + 2)).input p)) ?_ ?_
  · rintro s ⟨p, hp⟩
    exact List.mem_filterMap.mpr ⟨p, List.mem_finRange p, hp⟩
  · intro s hsm
    obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hsm
    exact g.proposal_shape coverage ht ⟨p, hp⟩

theorem inputs_compatible
    (coverage : WeakUniversal.CallsCovered obj (H)) {k : Nat}
    (hne : ∃ x, g.Retrieved k x)
    (hC : (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k)) :
    (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs := by
  classical
  obtain ⟨t, ht⟩ := (WeakUniversal.Tagged obj).glb_exists _ hne
  exact g.inputs_compatible_at coverage ht (fun a b ha hb hab => hC a b ha.1 hb.1 hab)

/-- Compatibility of the round's proposals, with no nonemptiness side
condition: a round nobody calls has compatible (vacuously) inputs. -/
theorem inputs_compatible_total
    (coverage : WeakUniversal.CallsCovered obj (H)) {k : Nat}
    (hC : (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k)) :
    (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs := by
  classical
  by_cases hcaller : ∃ s, (H (k + 2)).Inputs s
  · exact g.inputs_compatible coverage (g.retrieved_nonempty hcaller) hC
  · exact ⟨(WeakUniversal.Tagged obj).emptyTrace, fun s hs => absurd ⟨s, hs⟩ hcaller⟩

/-- **Theorem `weakUCWCF`, contradiction step.**  Under invariant (I) the
proposals to round `k + 2` are compatible, so by Commitment some caller's own
proposal is committed.  Its command occurs in the committed output, so that
caller leaves the while loop and records its response.  In the paper: "By
Commitment, there exists a correct process and an operation instance `Φ` such
that this process invokes `gcapropose(r*+1, s)`, with `cmd(Φ) ∈ s`, and returns
`(x, True)` such that `s ≤ x`.  Thus, the process invoking `Φ` exits the while
loop at Line 5, completing its operation---a contradiction." -/
theorem some_caller_completes_of_compatible (_coverage : WeakUniversal.CallsCovered obj (H)) {k : Nat}
    (hcompat : (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs)
    (hcaller : ∃ s, (H (k + 2)).Inputs s)
    (hcallers_sched : ∀ p, (∃ s, (H (k + 2)).input p = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    ∃ w cmd r s, (⟨cmd, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈
      (g.run.state w).returns := by
  obtain ⟨p, s, x, hin, hout, hpre⟩ :=
    (g.gca.spec (k + 1)).commitment hcaller hcompat
      (g.allReturned hcallers_sched)
  obtain ⟨t', hcall⟩ := (g.input_iff_call (k + 1) p s).mp hin
  obtain ⟨u, cmd, hL⟩ := g.call_was_waiting hcall
  obtain ⟨-, hcount⟩ :=
    WeakUniversal.waiting_call obj (g.run.reachable obj u) p cmd (k + 2) s hL
  have hcommit : ∀ y flag, (H (k + 2)).output p = some (y, flag) →
      flag = true ∧ 0 < (WeakUniversal.Tagged obj).traceCount cmd y := by
    intro y flag hy
    have he : (y, flag) = (x, true) := Option.some.inj (hy.symm.trans hout)
    have hy' : y = x := congrArg Prod.fst he
    have hf' : flag = true := congrArg Prod.snd he
    subst hy'; subst hf'
    exact ⟨rfl, Nat.lt_of_lt_of_le hcount
      ((WeakUniversal.Tagged obj).traceCount_mono hpre cmd)⟩
  have hsched := hcallers_sched p ⟨s, hin⟩
  obtain ⟨w, x2, hret⟩ := g.waiting_committed_returns hsched hL hcommit
  obtain ⟨w', -, hw'⟩ := g.returning_completes hsched hret
  exact ⟨w', cmd, k + 2, x2, hw'⟩

/-- `some_caller_completes_of_compatible` under the paper's nonconflict
hypothesis. -/
theorem some_caller_completes (coverage : WeakUniversal.CallsCovered obj (H)) {k : Nat}
    (hC : (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k))
    (hcaller : ∃ s, (H (k + 2)).Inputs s)
    (hcallers_sched : ∀ p, (∃ s, (H (k + 2)).input p = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    ∃ w cmd r s, (⟨cmd, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈
      (g.run.state w).returns :=
  g.some_caller_completes_of_compatible coverage
    (g.inputs_compatible coverage (g.retrieved_nonempty hcaller) hC)
    hcaller hcallers_sched

/-- A process that keeps taking steps either reaches the point of returning, or
waits on an arbitrarily large round. -/
theorem returning_or_waiting_above {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (B : Nat) :
    (∃ u cmd r s, (g.run.state u).localState p = .returning cmd r s) ∨
    (∃ u cmd r prop, (g.run.state u).localState p = .waiting cmd r prop ∧ B < r) := by
  rcases g.returning_or_rounds_unbounded hsched with hret | hunb
  · exact Or.inl hret
  obtain ⟨t, htB⟩ := hunb B
  cases hL : (g.run.state t).localState p with
  | idle => rw [hL] at htB; simp [WeakUniversal.nextRound] at htB
  | returning cmd r s => exact Or.inl ⟨t, cmd, r, s, hL⟩
  | publishing cmd r s =>
      obtain ⟨u, hu, hconst, hstep⟩ := g.next_step hsched t
      exact Or.inl ⟨u + 1, cmd, r, s,
        WeakUniversal.stepBy_from_publishing obj hstep (hconst.trans hL)⟩
  | waiting cmd r prop =>
      refine Or.inr ⟨t, cmd, r, prop, hL, ?_⟩
      rw [hL] at htB; exact htB
  | collecting _ _ _ | ready _ _ =>
      obtain ⟨u, hu, cmd', r', prop', hL', hr'⟩ :=
        g.reaches_waiting hsched _ t (Nat.le_refl _)
          (by rw [hL]; simp only [WeakUniversal.rank]; omega)
      exact Or.inr ⟨u, cmd', r', prop', hL', by omega⟩

end WeakGCA

namespace WeakRun
variable (g : WeakRun obj H)

/-- Recorded responses never disappear. -/
theorem returns_mono {a b : Nat} (hab : a ≤ b) {ret : WeakUniversal.Return (n := n) obj}
    (h : ret ∈ (g.run.state a).returns) : ret ∈ (g.run.state b).returns := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact h
  | succ d ih =>
      have hprev := ih (by omega)
      rcases g.step_actor (a + d) with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
      · rw [show a + (d + 1) = (a + d) + 1 from rfl, heq]; exact hprev
      · exact WeakUniversal.stepBy_returns obj hstep ret hprev
      · rw [show a + (d + 1) = (a + d) + 1 from rfl, heq]; exact hprev

/-- A process's current command has no recorded response yet. -/
theorem active_not_returned {u : Nat} {p : Fin n} {cmd : WeakUniversal.Cmd n Op}
    (h : ((g.run.state u).localState p).command obj = some cmd) :
    ∀ ret ∈ (g.run.state u).returns, ret.command ≠ cmd := by
  intro ret hret he
  have hv := (g.run.ledgerRun obj).valid u
  exact hv.active_pending p cmd h ret.command
    (List.mem_map.mpr ⟨ret, hret, rfl⟩) (by rw [he])

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H)

/-- Time-indexed form of `returning_or_waiting_above`. -/
theorem returning_or_waiting_above_from {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (B T : Nat) :
    (∃ u, T ≤ u ∧ ∃ cmd r s, (g.run.state u).localState p = .returning cmd r s) ∨
    (∃ u, T ≤ u ∧ ∃ cmd r prop,
      (g.run.state u).localState p = .waiting cmd r prop ∧ B < r) := by
  rcases g.returning_or_rounds_unbounded_from hsched T with hret | hunb
  · exact Or.inl hret
  obtain ⟨t, htT, htB⟩ := hunb B
  cases hL : (g.run.state t).localState p with
  | idle => rw [hL] at htB; simp [WeakUniversal.nextRound] at htB
  | returning cmd r s => exact Or.inl ⟨t, htT, cmd, r, s, hL⟩
  | publishing cmd r s =>
      obtain ⟨u, hu, hconst, hstep⟩ := g.next_step hsched t
      exact Or.inl ⟨u + 1, by omega, cmd, r, s,
        WeakUniversal.stepBy_from_publishing obj hstep (hconst.trans hL)⟩
  | waiting cmd r prop =>
      refine Or.inr ⟨t, htT, cmd, r, prop, hL, ?_⟩
      rw [hL] at htB; exact htB
  | collecting _ _ _ | ready _ _ =>
      obtain ⟨u, hu, cmd', r', prop', hL', hr'⟩ :=
        g.reaches_waiting hsched _ t (Nat.le_refl _)
          (by rw [hL]; simp only [WeakUniversal.rank]; omega)
      exact Or.inr ⟨u, by omega, cmd', r', prop', hL', by omega⟩

/-- **Theorem `weakUCWCF`, eventually-conflict-free half.**  If the commands of
pending operations pairwise do not conflict, and every process that still calls
a GCA round keeps taking steps, then some process records a response.  This is
the paper's contradiction: assuming that *no* process completes contradicts the
conclusion below. -/
theorem some_process_completes (coverage : WeakUniversal.CallsCovered obj (H))
    {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    (hC : ∃ k₀, ∀ k, k₀ ≤ k → (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k))
    (hcallers : ∀ k, (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k) →
      ∀ q, (∃ s, (H (k + 2)).input q = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q) :
    ∃ w cmd r s, (⟨cmd, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈
      (g.run.state w).returns := by
  obtain ⟨k₀, hk₀⟩ := hC
  rcases g.returning_or_waiting_above hsched (max 1 (k₀ + 1)) with
    ⟨u, cmd, r, s, hL⟩ | ⟨u, cmd, r, prop, hL, hr⟩
  · obtain ⟨w, -, hw2⟩ := g.returning_completes hsched hL
    exact ⟨w, cmd, r, s, hw2⟩
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by
      have := Nat.le_max_left 1 (k₀ + 1); omega⟩
    have hk : k₀ ≤ k := by have := Nat.le_max_right 1 (k₀ + 1); omega
    obtain ⟨hcall, -⟩ :=
      WeakUniversal.waiting_call obj (g.run.reachable obj u) p cmd (k + 2) prop hL
    have hin : (H (k + 2)).input p = some prop := by
      simpa using WeakUniversal.call_input obj (g.run.reachable obj u) _ hcall
    exact g.some_caller_completes coverage (hk₀ k hk) ⟨prop, p, hin⟩
      (hcallers k (hk₀ k hk))

/-- **The paper's contradiction.**  Suppose that from time `T` on no operation
returns, while the commands of pending operations do not conflict and every
process that still calls a GCA round keeps taking steps.  Invariant (I) then
forces a *new* response, which is impossible.  This is "for the sake of
contradiction, suppose no process completes all its operations in `α` … a
contradiction". -/
theorem no_stall_of_compatible (_coverage : WeakUniversal.CallsCovered obj (H))
    {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    {k₀ : Nat}
    (hk₀ : ∀ k, k₀ ≤ k →
      (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs)
    (hcallers : ∀ k, k₀ ≤ k →
      ∀ q, (∃ s, (H (k + 2)).input q = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q)
    {T : Nat}
    (hnoret : ∀ t, T ≤ t → (g.run.state t).returns = (g.run.state T).returns) :
    False := by
  classical
  obtain ⟨BT, hBT⟩ := WeakUniversal.calls_round_bound obj (g.run.state T).calls
  have hstall : ∀ u w cmd, T ≤ u →
      (∀ ret ∈ (g.run.state u).returns, ret.command ≠ cmd) →
      ∀ r s, (⟨cmd, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈ (g.run.state w).returns →
      False := by
    intro u w cmd hu hnot r s hmem
    have h1 : (⟨cmd, r, s⟩ : WeakUniversal.Return (n := n) obj)
        ∈ (g.run.state (max w T)).returns := g.returns_mono (Nat.le_max_left _ _) hmem
    rw [hnoret (max w T) (Nat.le_max_right _ _), ← hnoret u hu] at h1
    exact hnot _ h1 rfl
  rcases g.returning_or_waiting_above_from hsched
      (max (max 1 (k₀ + 1)) BT) T with
    ⟨u, hu, cmd, r, s, hL⟩ | ⟨u, hu, cmd, r, prop, hL, hr⟩
  · obtain ⟨w, -, hw2⟩ := g.returning_completes hsched hL
    exact hstall u w cmd hu (g.active_not_returned (by rw [hL]; rfl)) r s hw2
  · have hm1 := Nat.le_max_left 1 (k₀ + 1)
    have hm2 := Nat.le_max_right 1 (k₀ + 1)
    have hm3 := Nat.le_max_left (max 1 (k₀ + 1)) BT
    have hm4 := Nat.le_max_right (max 1 (k₀ + 1)) BT
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have hk : k₀ ≤ k := by omega
    obtain ⟨hcall, -⟩ :=
      WeakUniversal.waiting_call obj (g.run.reachable obj u) p cmd (k + 2) prop hL
    have hin : (H (k + 2)).input p = some prop := by
      simpa using WeakUniversal.call_input obj (g.run.reachable obj u) _ hcall
    obtain ⟨q, sq, x, hinq, houtq, hpreq⟩ :=
      (g.gca.spec (k + 1)).commitment ⟨prop, p, hin⟩ (hk₀ k hk)
        (g.allReturned (hcallers k hk))
    obtain ⟨t', hcallq⟩ := (g.input_iff_call (k + 1) q sq).mp hinq
    have hnew : (⟨k + 2, q, sq⟩ : WeakUniversal.Call (n := n) obj)
        ∉ (g.run.state T).calls := by
      intro hm
      have hle : k + 2 ≤ BT := hBT _ hm
      omega
    obtain ⟨uq, huq, cmdq, hLq⟩ := g.call_was_waiting_after hcallq hnew
    obtain ⟨-, hcountq⟩ :=
      WeakUniversal.waiting_call obj (g.run.reachable obj uq) q cmdq (k + 2) sq hLq
    have hcommit : ∀ y flag, (H (k + 2)).output q = some (y, flag) →
        flag = true ∧ 0 < (WeakUniversal.Tagged obj).traceCount cmdq y := by
      intro y flag hy
      have he : (y, flag) = (x, true) := Option.some.inj (hy.symm.trans houtq)
      have hy' : y = x := congrArg Prod.fst he
      have hf' : flag = true := congrArg Prod.snd he
      subst hy'; subst hf'
      exact ⟨rfl, Nat.lt_of_lt_of_le hcountq
        ((WeakUniversal.Tagged obj).traceCount_mono hpreq cmdq)⟩
    have hschedq := hcallers k hk q ⟨sq, hinq⟩
    obtain ⟨w1, x1, hret1⟩ := g.waiting_committed_returns hschedq hLq hcommit
    obtain ⟨w2, -, hw2⟩ := g.returning_completes hschedq hret1
    exact hstall uq w2 cmdq huq (g.active_not_returned (by rw [hLq]; rfl)) _ _ hw2

/-- `no_stall_of_compatible` under the paper's nonconflict hypothesis. -/
theorem no_stall (coverage : WeakUniversal.CallsCovered obj (H))
    {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    (hC : ∃ k₀, ∀ k, k₀ ≤ k → (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k))
    (hcallers : ∀ k, (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k) →
      ∀ q, (∃ s, (H (k + 2)).input q = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q)
    {T : Nat}
    (hnoret : ∀ t, T ≤ t → (g.run.state t).returns = (g.run.state T).returns) :
    False := by
  obtain ⟨k₀, hk₀⟩ := hC
  exact g.no_stall_of_compatible coverage hsched (k₀ := k₀)
    (fun k hk => g.inputs_compatible_total coverage (hk₀ k hk))
    (fun k hk => hcallers k (hk₀ k hk)) hnoret

/-- A directly usable, time-indexed form of `no_stall`: under the paper's
eventual-nonconflict and live-caller hypotheses, the response history must
strictly change at or after every proposed stall point. -/
theorem returns_progress_after (coverage : WeakUniversal.CallsCovered obj (H))
    {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    (hC : ∃ k₀, ∀ k, k₀ ≤ k →
      (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k))
    (hcallers : ∀ k, (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k) →
      ∀ q, (∃ s, (H (k + 2)).input q = some s) →
        ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q)
    (T : Nat) :
    ∃ t, T ≤ t ∧ (g.run.state t).returns ≠ (g.run.state T).returns := by
  apply Classical.byContradiction
  intro h
  have hall : ∀ t, T ≤ t → (g.run.state t).returns = (g.run.state T).returns := by
    intro t ht
    apply Classical.byContradiction
    intro hne
    exact h ⟨t, ht, hne⟩
  exact g.no_stall coverage hsched hC hcallers hall

/-- The response-history change is caused by an actual `finish` transition at
or after the proposed stall point.  This is the event-level conclusion used in
the manuscript's weak-conflict-freedom argument. -/
theorem finishes_after (coverage : WeakUniversal.CallsCovered obj (H))
    {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    (hC : ∃ k₀, ∀ k, k₀ ≤ k →
      (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k))
    (hcallers : ∀ k, (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k) →
      ∀ q, (∃ s, (H (k + 2)).input q = some s) →
        ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q)
    (T : Nat) :
    ∃ u, T ≤ u ∧ ∃ q p cmd r s,
      g.actor u = some q ∧
      (g.run.state u).localState p = .returning cmd r s ∧
      (⟨cmd, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈
        (g.run.state (u + 1)).returns := by
  classical
  obtain ⟨t, ht, hchange⟩ :=
    g.returns_progress_after coverage hsched hC hcallers T
  let P : Nat → Prop := fun v => (g.run.state v).returns ≠ (g.run.state T).returns
  have hnot : ¬ P T := by simp [P]
  obtain ⟨u, huT, _, hu0, hu1⟩ := first_appearance ht hnot hchange
  have hstepchange : (g.run.state (u + 1)).returns ≠ (g.run.state u).returns := by
    intro he
    apply hu1
    rw [he]
    exact Classical.not_not.mp hu0
  rcases g.step_actor u with ⟨_, he⟩ | ⟨q, hactor, hstep⟩ | ⟨_, _, _, _, he⟩
  · exact (hstepchange (congrArg WeakUniversal.Configuration.returns he)).elim
  · obtain ⟨hs, -⟩ := hstep
    obtain ⟨p, cmd, r, s, hlocal, hmem⟩ :=
      WeakUniversal.step_records_return obj hs hstepchange
    exact ⟨u, huT, q, p, cmd, r, s, hactor, hlocal, hmem⟩
  · exact (hstepchange (congrArg WeakUniversal.Configuration.returns he)).elim

end WeakGCA
end ConflictFreedom.GlobalSchedule
