import CFLeanProof.SharedScheduler
import CFLeanProof.UniversalComposition

/-!
# One global event schedule

A single global event sequence `actor : Nat → Option (Fin n)` drives both
projections: the program run of a universal construction and the GCA protocol
`Interleaving` it calls.  The interleaving's `event` and `clock` are *defined*
from the global sequence rather than supplied, so the routing property is a
theorem, and the input/call correspondence that `UniversalComposition` took as a
biconditional field is derived from a single no-ghost-participant condition.
-/

namespace ConflictFreedom.WeakUniversal
open Object
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- A step attributed to the process that takes it: no other process's local
state moves. -/
def StepBy (H : Environment (n := n) obj) (p : Fin n)
    (c d : Configuration (n := n) obj) : Prop :=
  Step obj H c d ∧ ∀ q, q ≠ p → d.localState q = c.localState q

/-- Every step is attributed to the process that takes it. -/
theorem exists_stepBy {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (h : Step obj H c d) : ∃ p, StepBy obj H p c d := by
  have hcopy := h
  cases hcopy with
  | invoke p | read p | collected p | propose p | receive p | publish p | finish p =>
      exact ⟨p, h, fun q hq => by simp [update, hq]⟩

/-- If an `update` at `q` changes the value at `p`, then `q = p`. -/
theorem eq_of_update_ne {α : Type} {l : Fin n → α} {p q : Fin n} {y : α}
    (h : update l q y p ≠ l p) : q = p :=
  Decidable.byContradiction fun hqp => h (by simp [update, Ne.symm hqp])

/-- If an `update` at `q` changes the value at `p`, then `p` held `q`'s old
value. -/
theorem apply_eq_of_update_ne {α : Type} {l : Fin n → α} {p q : Fin n} {x y : α}
    (h : update l q y p ≠ l p) (hq : l q = x) : l p = x := by
  obtain rfl := eq_of_update_ne h
  exact hq

variable {obj} in
/-- **A step attributed to `p` moves `p`.**  Every step changes its actor's
local state, and `StepBy` pins every other process.  So in a case analysis of
the underlying `Step`, `eq_of_update_ne h.moves` identifies the step's actor
with `p`, and `apply_eq_of_update_ne h.moves` puts `p` in the step's source
state. -/
theorem StepBy.moves {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) :
    d.localState p ≠ c.localState p := by
  obtain ⟨hstep, hother⟩ := h
  have moves : ∀ {q : Fin n} {x y : Local (n := n) obj}, c.localState q = x → y ≠ x →
      (∀ r, r ≠ p → update c.localState q y r = c.localState r) →
      update c.localState q y p ≠ c.localState p := by
    intro q x y hq hyx hframe
    by_cases hqp : q = p
    · subst hqp; simpa [update, hq] using hyx
    · exact absurd (hframe q hqp) (by simpa [update, hq] using hyx)
  cases hstep with
  | receive _ _ _ _ _ _ hq _ => exact moves hq (by split <;> simp) hother
  | _ => exact moves ‹_› (by simp) hother

/-- Every call the program records was matched by the environment's input.  This
is the direction of the composition contract that `Step.propose` already
enforces. -/
theorem call_input {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) :
    ∀ call ∈ c.calls, (H call.round).input call.process = some call.trace := by
  induction hc with
  | initial => intro call hcall; simp [WeakUniversal.initial] at hcall
  | step _ hs ih =>
      cases hs
      case propose p cmd seed h hi =>
        intro call hcall
        rcases List.mem_cons.mp hcall with rfl | hmem
        · exact hi
        · exact ih call hmem
      all_goals exact ih

/-- **Causal validity of the GCA objects of a run** — what Validity on every
prefix gives the constructions.  When a process receives an output from GCA
round `r`, every command occurring in that output occurs in a proposal already
made to round `r`.  It follows from the manuscript's Validity on the prefix of
the execution that ends with the receive (`causalGCA_of_prefixValidity`), which
says more — multiplicities too — than the constructions need here; a whole-run
table satisfying the six properties need not meet it (`NonCausalWitness`). -/
def Execution.CausalGCA {H : Environment (n := n) obj} (run : Execution obj H) : Prop :=
  ∀ T p cmd r proposal s flag,
    (run.state T).localState p = .waiting cmd r proposal →
    (run.state (T + 1)).localState p ≠ (run.state T).localState p →
    (H r).output p = some (s, flag) →
    ∀ a, 0 < (Tagged obj).traceCount a s →
      ∃ call ∈ (run.state T).calls, call.round = r ∧ 0 < (Tagged obj).traceCount a call.trace

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Call Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- Algorithm 3's step attribution. -/
def StepBy (H : Environment (n := n) obj) (p : Fin n)
    (c d : Configuration (n := n) obj) : Prop :=
  Step obj H c d ∧ ∀ q, q ≠ p → d.localState q = c.localState q

/-- Every step is attributed to the process that takes it. -/
theorem exists_stepBy {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (h : Step obj H c d) : ∃ p, StepBy obj H p c d := by
  have hcopy := h
  cases hcopy with
  | invoke p | announce p | readStart p | collectedStart p | readAnnouncement p | propose p
  | receive p | publish p | readCheck p | retry p | finish p =>
      exact ⟨p, h, fun q hq => by simp [WeakUniversal.update, hq]⟩

variable {obj} in
/-- **A step attributed to `p` moves `p`** — Algorithm 3's
`WeakUniversal.StepBy.moves`. -/
theorem StepBy.moves {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) :
    d.localState p ≠ c.localState p := by
  obtain ⟨hstep, hother⟩ := h
  have moves : ∀ {q : Fin n} {x y : Local (n := n) obj}, c.localState q = x → y ≠ x →
      (∀ r, r ≠ p → WeakUniversal.update c.localState q y r = c.localState r) →
      WeakUniversal.update c.localState q y p ≠ c.localState p := by
    intro q x y hq hyx hframe
    by_cases hqp : q = p
    · subst hqp; simpa [WeakUniversal.update, hq] using hyx
    · exact absurd (hframe q hqp) (by simpa [WeakUniversal.update, hq] using hyx)
  cases hstep with
  | receive _ _ _ _ _ _ hq _ => exact moves hq (by split <;> simp) hother
  | _ => exact moves ‹_› (by simp) hother

/-- Every call the program records was matched by the environment's input
(Algorithm 3's `WeakUniversal.call_input`). -/
theorem call_input {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) :
    ∀ call ∈ c.calls, (H call.round).input call.process = some call.trace := by
  induction hc with
  | initial => intro call hcall; simp [HelpingUniversal.initial] at hcall
  | step _ hs ih =>
      cases hs
      case propose p cmd seed commands h hi =>
        intro call hcall
        rcases List.mem_cons.mp hcall with rfl | hmem
        · exact hi
        · exact ih call hmem
      all_goals exact ih

/-- **Causal validity of the GCA objects of an Algorithm 3 run**: as for
Algorithm 1, an output a process receives from round `r` contains only
commands of proposals already made to round `r`. -/
def Execution.CausalGCA {H : Environment (n := n) obj} (run : Execution obj H) : Prop :=
  ∀ T p cmd r proposal s flag,
    (run.state T).localState p = .waiting cmd r proposal →
    (run.state (T + 1)).localState p ≠ (run.state T).localState p →
    (H r).output p = some (s, flag) →
    ∀ a, 0 < (WeakUniversal.Tagged obj).traceCount a s →
      ∃ call ∈ (run.state T).calls, call.round = r ∧
        0 < (WeakUniversal.Tagged obj).traceCount a call.trace

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The GCA round a process is currently blocked in, if any. -/
def weakRound : WeakUniversal.Local (n := n) obj → Option Nat
  | .waiting _ r _ => some r
  | _ => none

/-- Protocol projection of the global event sequence: a scheduled process that
is blocked in a GCA call contributes an event to that round. -/
def gcaEvent (st : Nat → WeakUniversal.Configuration (n := n) obj)
    (act : Nat → Option (Fin n)) (t : Nat) : Option (Nat × Fin n) :=
  match act t with
  | none => none
  | some p =>
      match weakRound obj ((st t).localState p) with
      | none => none
      | some r => some (r, p)

/-- Local clock of round `r`, counting that round's global events. -/
def gcaClock (st : Nat → WeakUniversal.Configuration (n := n) obj)
    (act : Nat → Option (Fin n)) : Nat → Nat → Nat
  | 0, _ => 0
  | (t + 1), r =>
      match gcaEvent obj st act t with
      | some (r', _) => if r' = r then gcaClock st act t r + 1 else gcaClock st act t r
      | none => gcaClock st act t r

omit [DecidableEq Op] in
theorem gcaEvent_spec {st : Nat → WeakUniversal.Configuration (n := n) obj}
    {act : Nat → Option (Fin n)} {t r : Nat} {p : Fin n}
    (h1 : act t = some p) (h2 : weakRound obj ((st t).localState p) = some r) :
    gcaEvent obj st act t = some (r, p) := by
  simp [gcaEvent, h1, h2]

omit [DecidableEq Op] in
theorem gcaEvent_inv {st : Nat → WeakUniversal.Configuration (n := n) obj}
    {act : Nat → Option (Fin n)} {t r : Nat} {p : Fin n}
    (h : gcaEvent obj st act t = some (r, p)) :
    act t = some p ∧ weakRound obj ((st t).localState p) = some r := by
  cases hact : act t with
  | none => simp [gcaEvent, hact] at h
  | some q =>
      cases hrd : weakRound obj ((st t).localState q) with
      | none => simp [gcaEvent, hact, hrd] at h
      | some r' =>
          simp [gcaEvent, hact, hrd] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2
          exact ⟨rfl, hrd⟩

/-- **Algorithm 1 over black-box GCA objects.**  A run of the program over
the whole-run GCA histories `H` — one table per round, whatever algorithm
implements the GCA objects — driven by one global event sequence `actor`.

`step_actor` records that a scheduled process either takes a program step or,
when it is inside a GCA call, takes a step of that call while the program
configuration stutters: `gcapropose` is a subroutine, and the steps a process
takes inside it are opaque here.  Omitting the third case makes "blocked in a
call" and "still taking steps" contradictory, because every program step out of
`.waiting` leaves `.waiting`.  `no_ghost` excludes ghost participants: every
input of a GCA object is a proposal of the run.

Nothing here constrains the GCA objects.  What the constructions require of
them is `WeakRun.GCAInterface`; `WeakGCA` bundles a run with it, and
`Weak` below is the composition with Algorithm 2, which meets it
(`Weak.gcaInterface`, in `Algorithm2Interface`). -/
structure WeakRun (H : WeakUniversal.Environment (n := n) obj) where
  run : WeakUniversal.Execution obj H
  actor : Nat → Option (Fin n)
  step_actor : ∀ t,
    (actor t = none ∧ run.state (t + 1) = run.state t) ∨
    (∃ p, actor t = some p ∧
      WeakUniversal.StepBy obj H p (run.state t) (run.state (t + 1))) ∨
    (∃ p r, actor t = some p ∧ weakRound obj ((run.state t).localState p) = some r ∧
      run.state (t + 1) = run.state t)
  no_ghost : ∀ r p s, (H (r + 1)).input p = some s →
    ∃ t s', (⟨r + 1, p, s'⟩ : WeakUniversal.Call obj) ∈ (run.state t).calls

namespace WeakRun
variable {obj} {H : WeakUniversal.Environment (n := n) obj} (g : WeakRun obj H)

/-- **The input/call correspondence of `UniversalComposition` is derived.**
`Step.propose` already forces every recorded call to match the environment's
input; `no_ghost` supplies the converse without mentioning traces. -/
theorem input_iff_call (r : Nat) (p : Fin n)
    (s : (WeakUniversal.Tagged (n := n) obj).Trace) :
    (H (r + 1)).input p = some s ↔
      ∃ t, (⟨r + 1, p, s⟩ : WeakUniversal.Call obj) ∈ (g.run.state t).calls := by
  constructor
  · intro hin
    obtain ⟨t, s', hcall⟩ := g.no_ghost r p s hin
    have hmatch : (H (r + 1)).input p = some s' :=
      WeakUniversal.call_input obj (g.run.reachable obj t) _ hcall
    have : s' = s := Option.some.inj (hmatch.symm.trans hin)
    exact ⟨t, this ▸ hcall⟩
  · rintro ⟨t, hcall⟩
    exact WeakUniversal.call_input obj (g.run.reachable obj t) _ hcall

/-- **Call coverage is derived, not assumed.**  `no_ghost` and `call_input`
already pin the program's calls to the environment's inputs, so every input
really was called by the run. -/
theorem callsCovered (gs : WeakRun obj H) : WeakUniversal.CallsCovered obj H :=
  gs.run.callsCovered obj (fun r p s hi => (gs.input_iff_call r p s).mp hi)

/-- The operation instance acting at global time `t`: the active command of the
process the schedule runs at `t + 1`, when it has one.

This is deliberately *partial*: `Step.finish` leaves its process idle for one
instant, so asking for an active command at every instant would be
contradictory with `n = 1`, and every theorem assuming it vacuous.  Since
`Execution.actor` is partial, no such condition is needed. -/
noncomputable def opActor (t : Nat) : Option (WeakUniversal.Cmd n Op) :=
  match g.actor (t + 1) with
  | none => none
  | some p => (WeakUniversal.ledger obj (g.run.state (t + 1))).active p

theorem opActor_eq_some {t : Nat} {cmd : WeakUniversal.Cmd n Op}
    (h : g.opActor t = some cmd) :
    ∃ p, g.actor (t + 1) = some p ∧
      (WeakUniversal.ledger obj (g.run.state (t + 1))).active p = some cmd := by
  revert h
  cases hp : g.actor (t + 1) with
  | none => intro h; rw [opActor, hp] at h; exact absurd h (by simp)
  | some p => intro h; exact ⟨p, rfl, by rw [opActor, hp] at h; exact h⟩

/-- The run is *live at the operation level* when a process with an active
command is scheduled at arbitrarily late times.  This is the manuscript's
standing "infinite execution" assumption, transported to the operation clock;
it does not ask for an active command at every instant. -/
def OpLive : Prop := ∀ N, ∃ t, N ≤ t ∧ (g.opActor t).isSome

/-- Operation-level liveness discharges the operation schedule: no extra choice
of actors, and no condition on instants where nothing is running. -/
noncomputable def schedule (hp : g.OpLive) :
    InvocationLedger.Schedule (g.run.ledgerRun obj) where
  actor := g.opActor
  actor_active := by
    intro t cmd hc
    obtain ⟨p, -, hact⟩ := g.opActor_eq_some hc
    have htag := ((WeakUniversal.identity_invariant obj
      (g.run.reachable obj (t + 1))).active_tag p cmd hact).1
    show (WeakUniversal.ledger obj (g.run.state (t + 1))).active cmd.process = some cmd
    rw [htag]; exact hact
  live := by
    intro N
    obtain ⟨t, ht, hs⟩ := hp N
    exact ⟨t, (g.opActor t).get hs, ht, (Option.some_get hs).symm⟩

theorem schedule_scheduled (hp : g.OpLive) {t : Nat} {cmd : WeakUniversal.Cmd n Op}
    (h : (g.schedule hp).actor t = some cmd) : g.actor (t + 1) = some cmd.process := by
  obtain ⟨p, hp', hact⟩ := g.opActor_eq_some h
  have htag := ((WeakUniversal.identity_invariant obj
    (g.run.reachable obj (t + 1))).active_tag p cmd hact).1
  rw [htag]; exact hp'

/-- **Projection onto the operation-level execution.** -/
noncomputable def execution (hp : g.OpLive) : _root_.ConflictFreedom.Execution n Op :=
  (g.schedule hp).execution

/-! ### The GCA interface

What Algorithms 1 and 3 require of their GCA objects is the specification of
§4.2 — the six properties, which "hold for every execution", and "every correct
participant eventually returns" — read on the GCA objects of the run.  Nothing
else: not how the objects are implemented, how many steps a call takes, or when
an output becomes available.

The interface speaks of one run.  Statements about the extensions a finite
execution *has* (§7) need the GCA objects as an implementation that can be run
on: `GCAMachine` (`GCAMachine.lean`), whose specification `GCAMachine.IsGCA`
gives this interface for every run over it (`WeakUniversal.Over.gcaInterface`,
`HelpingUniversal.Over.gcaInterface`). -/

/-- **Every correct participant returns.**  A process that is inside a GCA call
from some time on is scheduled only finitely often after it: a participant that
keeps taking steps leaves the call. -/
def CallsReturn (gs : WeakRun obj H) : Prop :=
  ∀ p cmd r proposal N,
    (∀ t, N ≤ t → (gs.run.state t).localState p = .waiting cmd r proposal) →
    ¬ ∀ M, ∃ t, M ≤ t ∧ gs.actor t = some p

/-- **The GCA interface**, for the GCA objects of one run of Algorithm 1: each
round's history satisfies the six properties of §4.2 (`spec`); an output a
process receives contains only commands of proposals already made to that object
(`causal` — what Validity on the prefix ending with the receive gives,
`causalGCA_of_prefixValidity`); and every correct participant returns
(`returns`). -/
structure GCAInterface (gs : WeakRun obj H) : Prop where
  spec : ∀ r, (H (r + 1)).Specification
  causal : gs.run.CausalGCA obj
  returns : gs.CallsReturn

/-- **GCA property 7, Solo agreement** (§7), for the GCA objects of the run.  If
process `i` has returned from round `R` in the prefix up to time `N` — it left
its call to `R` at some `v < N` — and no other process has called `R` in that
prefix, then every output of round `R`, in the whole run, is `i`'s output trace:
`P' = P'_r = {i}` for the prefix implies `t_q = t_i` for every `q ∈ P_r`.  Only
Theorem `th:WeakUCresolve` uses it. -/
def SoloAgreement (gs : WeakRun obj H) : Prop :=
  ∀ N v R i, (∀ call ∈ (gs.run.state N).calls, call.round = R → call.process = i) →
    v < N → weakRound obj ((gs.run.state v).localState i) = some R →
    (gs.run.state (v + 1)).localState i ≠ (gs.run.state v).localState i →
    ∃ tj cj, (H R).output i = some (tj, cj) ∧
      ∀ q y fl, (H R).output q = some (y, fl) → y = tj

end WeakRun

/-- **Algorithm 1 over any GCA objects meeting the interface**: a run over the
GCA histories `H`, and the proof that its GCA objects satisfy
`WeakRun.GCAInterface`.  The liveness theorems of Algorithm 1 are proved for
this structure; the composition with Algorithm 2 is one instance
(`Weak.toGCA`). -/
structure WeakGCA (H : WeakUniversal.Environment (n := n) obj) extends WeakRun obj H where
  gca : toWeakRun.GCAInterface

/-- **The single global schedule for Algorithm 1 over Algorithm 2.**  A run over
the histories of an operational GCA family `f` (Algorithm 2 above the snapshot
interface), with the family's protocol clocks projected from the same global
event sequence.  One event sequence `actor` drives both projections: the program
run is stepped by the scheduled process, and the GCA `Interleaving` is *defined*
from the same sequence, so routing is a theorem rather than an assumption.
`gca_actor` attributes each protocol step to its caller, and `receive_ready`
synchronizes output availability with the protocol clock.  Neither assumes a
trace-safety invariant. -/
structure Weak (f : Family (n := n) obj) extends WeakRun obj (f.environment obj) where
  gca_actor : ∀ t p r, actor t = some p →
    weakRound obj ((run.state t).localState p) = some r →
    (f.protocol r).actor (gcaClock obj run.state actor t r) = some p
  /-- A synchronous GCA call returns only after all its protocol stages have
  completed on the global projection. This prevents consuming future outputs. -/
  receive_ready : ∀ t p r, weakRound obj ((run.state t).localState p) = some r →
    (run.state (t + 1)).localState p ≠ (run.state t).localState p →
    (f.protocol r).phase (gcaClock obj run.state actor t r) p = 6

namespace Weak
variable {obj} {f : Family (n := n) obj} (g : Weak obj f)

/-- **Projection onto the protocol interleaving.**  Built from the global event
sequence; nothing is assumed about the clock. -/
def inter : Interleaving obj f where
  event := gcaEvent obj g.run.state g.actor
  clock := gcaClock obj g.run.state g.actor
  initial_clock := fun _ => rfl
  clock_next := by
    intro t r
    show gcaClock obj g.run.state g.actor (t + 1) r = _
    rw [gcaClock]
    cases hev : gcaEvent obj g.run.state g.actor t with
    | none => simp
    | some rp =>
        obtain ⟨r', p'⟩ := rp
        by_cases hr : r' = r
        · subst hr
          simp
        · simp [hr]
  actor_matches := by
    intro t r p hev
    obtain ⟨h1, h2⟩ := gcaEvent_inv obj hev
    exact g.gca_actor t p r h1 h2

/-- **Routing is a theorem.**  A scheduled process blocked in round `r`
contributes exactly that round's protocol event. -/
theorem routing (t : Nat) (p : Fin n) (cmd : WeakUniversal.Cmd n Op) (r : Nat)
    (proposal : (WeakUniversal.Tagged (n := n) obj).Trace)
    (hact : g.actor t = some p)
    (hw : (g.run.state t).localState p = .waiting cmd r proposal) :
    g.inter.event t = some (r, p) := by
  exact gcaEvent_spec obj hact (by rw [hw]; rfl)

/-- The composition contract of `UniversalComposition`: every field is a
projection of the single global schedule. -/
def composition : UniversalComposition.Weak (n := n) obj where
  family := f
  run := g.run
  input_iff_call := g.input_iff_call

/-- **Routing, now fully derived.**  A process that keeps taking operation steps
while blocked in a GCA call is scheduled in that round infinitely often, so
under the author's snapshot assumption the call produces its output. -/
theorem blocked_output (hw : f.SnapshotWaitFree obj) (hp : g.OpLive)
    {p : Fin n} {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {proposal : (WeakUniversal.Tagged (n := n) obj).Trace} {N : Nat}
    (hblock : ∀ t, N ≤ t → (g.run.state t).localState p = .waiting cmd r proposal)
    (hinf : (g.execution hp).InfiniteSteps p) :
    ∃ s flag, (f.environment obj r).output p = some (s, flag) := by
  refine g.inter.round_returned obj hw ?_
  intro M
  obtain ⟨t, i, ht, hact, hown⟩ := hinf (max M N)
  refine ⟨t + 1, by omega, ?_⟩
  refine g.routing (t + 1) p cmd r proposal ?_ (hblock (t + 1) (by omega))
  have hsch := g.schedule_scheduled hp ((g.schedule hp).actorInst_val hact)
  exact hsch.trans (congrArg some hown)

end Weak

/-! ### The global schedule is inhabited

As with `InvocationLedger.Schedule`, a structure this constrained is worth
exhibiting.  A family with no participants and a run that stutters satisfies
every field, so the derived projections above are not vacuous. -/

/-- A GCA family in which nobody participates. -/
def trivialFamily : Family (n := n) obj where
  protocol := fun _ =>
    { participants := []
      input := fun _ => (WeakUniversal.Tagged (n := n) obj).emptyTrace
      actor := fun _ => none
      actor_valid := by intro t p h; exact absurd h (by simp)
      acknowledged := fun _ => true }

/-- The run that never leaves its initial configuration. -/
def trivialRun :
    WeakUniversal.Execution (n := n) obj ((trivialFamily (n := n) obj).environment obj) where
  state := fun _ => WeakUniversal.initial obj
  initial_state := rfl
  next := fun _ => Or.inl rfl

/-- The schedule that never schedules anyone. -/
def trivialSchedule : Weak obj (trivialFamily (n := n) obj) where
  run := trivialRun (n := n) obj
  actor := fun _ => none
  step_actor := fun _ => Or.inl ⟨rfl, rfl⟩
  receive_ready := by intro t p r _ h; exact False.elim (h rfl)
  gca_actor := by intro t p r h; exact absurd h (by simp)
  no_ghost := by
    intro r p s hin
    have hI : ((trivialFamily (n := n) obj).protocol (r + 1)).history.Inputs s := ⟨p, hin⟩
    rw [GCA.Protocol.history, GCA.SnapshotExecution.inputs_iff] at hI
    simp [GCA.Protocol.timed, GCA.TimedExecution.views, trivialFamily] at hI

theorem schedule_nonempty : Nonempty (Weak obj (trivialFamily (n := n) obj)) :=
  ⟨trivialSchedule obj⟩

/-! ## The same global schedule for Algorithm 3 -/

/-- The GCA round a process is currently blocked in, if any. -/
def helpingRound : HelpingUniversal.Local (n := n) obj → Option Nat
  | .waiting _ r _ => some r
  | _ => none

/-- Protocol projection of the global event sequence: a scheduled process that
is blocked in a GCA call contributes an event to that round. -/
def gcaEventH (st : Nat → HelpingUniversal.Configuration (n := n) obj)
    (act : Nat → Option (Fin n)) (t : Nat) : Option (Nat × Fin n) :=
  match act t with
  | none => none
  | some p =>
      match helpingRound obj ((st t).localState p) with
      | none => none
      | some r => some (r, p)

/-- Local clock of round `r`, counting that round's global events. -/
def gcaClockH (st : Nat → HelpingUniversal.Configuration (n := n) obj)
    (act : Nat → Option (Fin n)) : Nat → Nat → Nat
  | 0, _ => 0
  | (t + 1), r =>
      match gcaEventH obj st act t with
      | some (r', _) => if r' = r then gcaClockH st act t r + 1 else gcaClockH st act t r
      | none => gcaClockH st act t r

omit [DecidableEq Op] in
theorem gcaEventH_spec {st : Nat → HelpingUniversal.Configuration (n := n) obj}
    {act : Nat → Option (Fin n)} {t r : Nat} {p : Fin n}
    (h1 : act t = some p) (h2 : helpingRound obj ((st t).localState p) = some r) :
    gcaEventH obj st act t = some (r, p) := by
  simp [gcaEventH, h1, h2]

omit [DecidableEq Op] in
theorem gcaEventH_inv {st : Nat → HelpingUniversal.Configuration (n := n) obj}
    {act : Nat → Option (Fin n)} {t r : Nat} {p : Fin n}
    (h : gcaEventH obj st act t = some (r, p)) :
    act t = some p ∧ helpingRound obj ((st t).localState p) = some r := by
  cases hact : act t with
  | none => simp [gcaEventH, hact] at h
  | some q =>
      cases hrd : helpingRound obj ((st t).localState q) with
      | none => simp [gcaEventH, hact, hrd] at h
      | some r' =>
          simp [gcaEventH, hact, hrd] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2
          exact ⟨rfl, hrd⟩

/-- **Algorithm 3 over black-box GCA objects** — `WeakRun` for the helping
construction.  See `WeakRun` for the meaning of `step_actor`'s third case and of
`no_ghost`; what the construction requires of its GCA objects is
`HelpingRun.GCAInterface`, and `Helping` below is the composition with
Algorithm 2. -/
structure HelpingRun (H : WeakUniversal.Environment (n := n) obj) where
  run : HelpingUniversal.Execution obj H
  actor : Nat → Option (Fin n)
  step_actor : ∀ t,
    (actor t = none ∧ run.state (t + 1) = run.state t) ∨
    (∃ p, actor t = some p ∧
      HelpingUniversal.StepBy obj H p (run.state t) (run.state (t + 1))) ∨
    (∃ p r, actor t = some p ∧ helpingRound obj ((run.state t).localState p) = some r ∧
      run.state (t + 1) = run.state t)
  no_ghost : ∀ r p s, (H (r + 1)).input p = some s →
    ∃ t s', (⟨r + 1, p, s'⟩ : WeakUniversal.Call obj) ∈ (run.state t).calls

namespace HelpingRun
variable {obj} {H : WeakUniversal.Environment (n := n) obj} (g : HelpingRun obj H)

/-- **The input/call correspondence of `UniversalComposition` is derived.**
`Step.propose` already forces every recorded call to match the environment's
input; `no_ghost` supplies the converse without mentioning traces. -/
theorem input_iff_call (r : Nat) (p : Fin n)
    (s : (WeakUniversal.Tagged (n := n) obj).Trace) :
    (H (r + 1)).input p = some s ↔
      ∃ t, (⟨r + 1, p, s⟩ : WeakUniversal.Call obj) ∈ (g.run.state t).calls := by
  constructor
  · intro hin
    obtain ⟨t, s', hcall⟩ := g.no_ghost r p s hin
    have hmatch : (H (r + 1)).input p = some s' :=
      HelpingUniversal.call_input obj (g.run.reachable obj t) _ hcall
    have : s' = s := Option.some.inj (hmatch.symm.trans hin)
    exact ⟨t, this ▸ hcall⟩
  · rintro ⟨t, hcall⟩
    exact HelpingUniversal.call_input obj (g.run.reachable obj t) _ hcall

/-- **Call coverage is derived, not assumed**, exactly as for Algorithm 1. -/
theorem callsCovered (gs : HelpingRun obj H) : HelpingUniversal.CallsCovered obj H :=
  gs.run.callsCovered obj (fun r p s hi => (gs.input_iff_call r p s).mp hi)

/-- The operation instance acting at global time `t`: the active command of the
process the schedule runs at `t + 1`, when it has one.

This is deliberately *partial*: `Step.finish` leaves its process idle for one
instant, so asking for an active command at every instant would be
contradictory with `n = 1`, and every theorem assuming it vacuous.  Since
`Execution.actor` is partial, no such condition is needed. -/
noncomputable def opActor (t : Nat) : Option (WeakUniversal.Cmd n Op) :=
  match g.actor (t + 1) with
  | none => none
  | some p => (HelpingUniversal.ledger obj (g.run.state (t + 1))).active p

theorem opActor_eq_some {t : Nat} {cmd : WeakUniversal.Cmd n Op}
    (h : g.opActor t = some cmd) :
    ∃ p, g.actor (t + 1) = some p ∧
      (HelpingUniversal.ledger obj (g.run.state (t + 1))).active p = some cmd := by
  revert h
  cases hp : g.actor (t + 1) with
  | none => intro h; rw [opActor, hp] at h; exact absurd h (by simp)
  | some p => intro h; exact ⟨p, rfl, by rw [opActor, hp] at h; exact h⟩

/-- The run is *live at the operation level* when a process with an active
command is scheduled at arbitrarily late times.  This is the manuscript's
standing "infinite execution" assumption, transported to the operation clock;
it does not ask for an active command at every instant. -/
def OpLive : Prop := ∀ N, ∃ t, N ≤ t ∧ (g.opActor t).isSome

/-- Operation-level liveness discharges the operation schedule: no extra choice
of actors, and no condition on instants where nothing is running. -/
noncomputable def schedule (hp : g.OpLive) :
    InvocationLedger.Schedule (g.run.ledgerRun obj) where
  actor := g.opActor
  actor_active := by
    intro t cmd hc
    obtain ⟨p, -, hact⟩ := g.opActor_eq_some hc
    have htag := ((HelpingUniversal.identity_invariant obj
      (g.run.reachable obj (t + 1))).active_tag p cmd hact).1
    show (HelpingUniversal.ledger obj (g.run.state (t + 1))).active cmd.process = some cmd
    rw [htag]; exact hact
  live := by
    intro N
    obtain ⟨t, ht, hs⟩ := hp N
    exact ⟨t, (g.opActor t).get hs, ht, (Option.some_get hs).symm⟩

theorem schedule_scheduled (hp : g.OpLive) {t : Nat} {cmd : WeakUniversal.Cmd n Op}
    (h : (g.schedule hp).actor t = some cmd) : g.actor (t + 1) = some cmd.process := by
  obtain ⟨p, hp', hact⟩ := g.opActor_eq_some h
  have htag := ((HelpingUniversal.identity_invariant obj
    (g.run.reachable obj (t + 1))).active_tag p cmd hact).1
  rw [htag]; exact hp'

/-- **Projection onto the operation-level execution.** -/
noncomputable def execution (hp : g.OpLive) : _root_.ConflictFreedom.Execution n Op :=
  (g.schedule hp).execution

/-- **Every correct participant returns**, for Algorithm 3's GCA calls. -/
def CallsReturn (gs : HelpingRun obj H) : Prop :=
  ∀ p cmd r proposal N,
    (∀ t, N ≤ t → (gs.run.state t).localState p = .waiting cmd r proposal) →
    ¬ ∀ M, ∃ t, M ≤ t ∧ gs.actor t = some p

/-- **The GCA interface**, for the GCA objects of one run of Algorithm 3 — the
same three requirements as `WeakRun.GCAInterface`. -/
structure GCAInterface (gs : HelpingRun obj H) : Prop where
  spec : ∀ r, (H (r + 1)).Specification
  causal : gs.run.CausalGCA obj
  returns : gs.CallsReturn

end HelpingRun

/-- **Algorithm 3 over any GCA objects meeting the interface.** -/
structure HelpingGCA (H : WeakUniversal.Environment (n := n) obj) extends HelpingRun obj H where
  gca : toHelpingRun.GCAInterface

/-- **The single global schedule for Algorithm 3 over Algorithm 2.**  See `Weak`
for the meaning of `gca_actor` and `receive_ready`. -/
structure Helping (f : Family (n := n) obj) extends HelpingRun obj (f.environment obj) where
  gca_actor : ∀ t p r, actor t = some p →
    helpingRound obj ((run.state t).localState p) = some r →
    (f.protocol r).actor (gcaClockH obj run.state actor t r) = some p
  /-- A synchronous GCA call returns only after all its protocol stages have
  completed on the global projection. This prevents consuming future outputs. -/
  receive_ready : ∀ t p r, helpingRound obj ((run.state t).localState p) = some r →
    (run.state (t + 1)).localState p ≠ (run.state t).localState p →
    (f.protocol r).phase (gcaClockH obj run.state actor t r) p = 6

namespace Helping
variable {obj} {f : Family (n := n) obj} (g : Helping obj f)

/-- **Projection onto the protocol interleaving.**  Built from the global event
sequence; nothing is assumed about the clock. -/
def inter : Interleaving obj f where
  event := gcaEventH obj g.run.state g.actor
  clock := gcaClockH obj g.run.state g.actor
  initial_clock := fun _ => rfl
  clock_next := by
    intro t r
    show gcaClockH obj g.run.state g.actor (t + 1) r = _
    rw [gcaClockH]
    cases hev : gcaEventH obj g.run.state g.actor t with
    | none => simp
    | some rp =>
        obtain ⟨r', p'⟩ := rp
        by_cases hr : r' = r
        · subst hr
          simp
        · simp [hr]
  actor_matches := by
    intro t r p hev
    obtain ⟨h1, h2⟩ := gcaEventH_inv obj hev
    exact g.gca_actor t p r h1 h2

/-- **Routing is a theorem.**  A scheduled process blocked in round `r`
contributes exactly that round's protocol event. -/
theorem routing (t : Nat) (p : Fin n) (cmd : WeakUniversal.Cmd n Op) (r : Nat)
    (proposal : (WeakUniversal.Tagged (n := n) obj).Trace)
    (hact : g.actor t = some p)
    (hw : (g.run.state t).localState p = .waiting cmd r proposal) :
    g.inter.event t = some (r, p) := by
  exact gcaEventH_spec obj hact (by rw [hw]; rfl)

/-- The composition contract of `UniversalComposition`: every field is a
projection of the single global schedule. -/
def composition : UniversalComposition.Helping (n := n) obj where
  family := f
  run := g.run
  input_iff_call := g.input_iff_call

/-- **Routing, now fully derived.**  A process that keeps taking operation steps
while blocked in a GCA call is scheduled in that round infinitely often, so
under the author's snapshot assumption the call produces its output. -/
theorem blocked_output (hw : f.SnapshotWaitFree obj) (hp : g.OpLive)
    {p : Fin n} {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {proposal : (WeakUniversal.Tagged (n := n) obj).Trace} {N : Nat}
    (hblock : ∀ t, N ≤ t → (g.run.state t).localState p = .waiting cmd r proposal)
    (hinf : (g.execution hp).InfiniteSteps p) :
    ∃ s flag, (f.environment obj r).output p = some (s, flag) := by
  refine g.inter.round_returned obj hw ?_
  intro M
  obtain ⟨t, i, ht, hact, hown⟩ := hinf (max M N)
  refine ⟨t + 1, by omega, ?_⟩
  refine g.routing (t + 1) p cmd r proposal ?_ (hblock (t + 1) (by omega))
  have hsch := g.schedule_scheduled hp ((g.schedule hp).actorInst_val hact)
  exact hsch.trans (congrArg some hown)

end Helping

/-! ### The global schedule is inhabited

As with `InvocationLedger.Schedule`, a structure this constrained is worth
exhibiting.  A family with no participants and a run that stutters satisfies
every field, so the derived projections above are not vacuous. -/

/-- A GCA family in which nobody participates. -/
def trivialFamilyH : Family (n := n) obj where
  protocol := fun _ =>
    { participants := []
      input := fun _ => (WeakUniversal.Tagged (n := n) obj).emptyTrace
      actor := fun _ => none
      actor_valid := by intro t p h; exact absurd h (by simp)
      acknowledged := fun _ => true }

/-- The run that never leaves its initial configuration. -/
def trivialRunH :
    HelpingUniversal.Execution (n := n) obj ((trivialFamilyH (n := n) obj).environment obj) where
  state := fun _ => HelpingUniversal.initial obj
  initial_state := rfl
  next := fun _ => Or.inl rfl

/-- Algorithm 3's `trivialSchedule`. -/
def trivialScheduleH : Helping obj (trivialFamilyH (n := n) obj) where
  run := trivialRunH (n := n) obj
  actor := fun _ => none
  step_actor := fun _ => Or.inl ⟨rfl, rfl⟩
  receive_ready := by intro t p r _ h; exact False.elim (h rfl)
  gca_actor := by intro t p r h; exact absurd h (by simp)
  no_ghost := by
    intro r p s hin
    have hI : ((trivialFamilyH (n := n) obj).protocol (r + 1)).history.Inputs s := ⟨p, hin⟩
    rw [GCA.Protocol.history, GCA.SnapshotExecution.inputs_iff] at hI
    simp [GCA.Protocol.timed, GCA.TimedExecution.views, trivialFamilyH] at hI

theorem schedule_nonemptyH : Nonempty (Helping obj (trivialFamilyH (n := n) obj)) :=
  ⟨trivialScheduleH obj⟩


/-! ### A blocked, still-stepping process: nonvacuity of `blocked_output`

`blocked_output` assumes a process is blocked in a GCA call forever while still
being scheduled.  With `step_actor`'s third case those assumptions are
consistent, and this section proves it by exhibiting a one-process schedule that
satisfies all of them.  (Without that third case they are contradictory, since
every program step out of `.waiting` leaves `.waiting`.) -/

namespace Witness
section
variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op] (op : Op)



abbrev Tg := WeakUniversal.Tagged (n := 1) obj
def wcmd : WeakUniversal.Cmd 1 Op := ⟨op, 0, 1⟩
noncomputable def wprop : (Tg obj).Trace :=
  (Tg obj).appendMissing (Tg obj).emptyTrace (wcmd op)

noncomputable def wfam : Family (n := 1) obj where
  protocol := fun r =>
    { participants := if r = 1 then [0] else []
      input := fun _ => wprop obj op
      actor := fun _ => if r = 1 then some 0 else none
      actor_valid := by
        intro t p h
        by_cases hr : r = 1 <;> simp [hr] at h ⊢
        exact h.symm
      acknowledged := fun _ => true }

def w0 : WeakUniversal.Configuration (n := 1) obj := WeakUniversal.initial obj

def w1 : WeakUniversal.Configuration (n := 1) obj :=
  { w0 obj with
    sequence := WeakUniversal.update (w0 obj).sequence 0 ((w0 obj).sequence 0 + 1)
    invocations := (⟨op, 0, (w0 obj).sequence 0 + 1⟩ : WeakUniversal.Cmd 1 Op) :: (w0 obj).invocations
    localState := WeakUniversal.update (w0 obj).localState 0
      (.collecting ⟨op, 0, (w0 obj).sequence 0 + 1⟩ (List.finRange 1) (WeakUniversal.zeroSeed obj)) }

def w2 : WeakUniversal.Configuration (n := 1) obj :=
  { w1 obj op with
    localState := WeakUniversal.update (w1 obj op).localState 0
      (.collecting (wcmd op) [] (WeakUniversal.best obj (WeakUniversal.zeroSeed obj)
        ((w1 obj op).slots 0))) }

def w3 : WeakUniversal.Configuration (n := 1) obj :=
  { w2 obj op with
    localState := WeakUniversal.update (w2 obj op).localState 0
      (.ready (wcmd op) (WeakUniversal.best obj (WeakUniversal.zeroSeed obj)
        ((w1 obj op).slots 0))) }

noncomputable def wseed : WeakUniversal.Seed (n := 1) obj :=
  WeakUniversal.best obj (WeakUniversal.zeroSeed obj) ((w1 obj op).slots 0)

omit [DecidableEq Op] in
theorem wseed_eq : wseed obj op = WeakUniversal.zeroSeed obj := by
  simp [wseed, w1, w0, WeakUniversal.initial, WeakUniversal.best]

noncomputable def w4 : WeakUniversal.Configuration (n := 1) obj :=
  { w3 obj op with
    localState := WeakUniversal.update (w3 obj op).localState 0
      (.waiting (wcmd op) ((wseed obj op).round + 1)
        ((Tg obj).appendMissing (wseed obj op).trace (wcmd op)))
    calls := (⟨(wseed obj op).round + 1, 0,
      (Tg obj).appendMissing (wseed obj op).trace (wcmd op)⟩ : WeakUniversal.Call obj)
        :: (w3 obj op).calls }

section Steps
variable {H : WeakUniversal.Environment (n := 1) obj}

example : WeakUniversal.Step obj H (w0 obj) (w1 obj op) :=
  WeakUniversal.Step.invoke (w0 obj) 0 op rfl (List.finRange 1) (List.Perm.refl _)

example : WeakUniversal.Step obj H (w1 obj op) (w2 obj op) :=
  WeakUniversal.Step.read (w1 obj op) 0 0 (wcmd op) [] (WeakUniversal.zeroSeed obj) rfl

example : WeakUniversal.Step obj H (w2 obj op) (w3 obj op) :=
  WeakUniversal.Step.collected (w2 obj op) 0 (wcmd op) (wseed obj op) rfl

theorem wfam_input :
    ((wfam obj op).environment obj 1).input 0 = some (wprop obj op) := by
  simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
    GCA.TimedExecution.views, GCA.SnapshotExecution.history, wfam]

example : WeakUniversal.Step obj ((wfam obj op).environment obj) (w3 obj op) (w4 obj op) :=
  WeakUniversal.Step.propose (w3 obj op) 0 (wcmd op) (wseed obj op) rfl (by
    rw [wseed_eq]
    exact wfam_input obj op)

noncomputable def wstate : Nat → WeakUniversal.Configuration (n := 1) obj
  | 0 => w0 obj
  | 1 => w1 obj op
  | 2 => w2 obj op
  | 3 => w3 obj op
  | _ => w4 obj op

noncomputable def wrun : WeakUniversal.Execution obj ((wfam obj op).environment obj) where
  state := wstate obj op
  initial_state := rfl
  next := by
    intro t
    match t with
    | 0 => exact Or.inr (WeakUniversal.Step.invoke (w0 obj) 0 op rfl (List.finRange 1) (List.Perm.refl _))
    | 1 => exact Or.inr (WeakUniversal.Step.read (w1 obj op) 0 0 (wcmd op) []
              (WeakUniversal.zeroSeed obj) rfl)
    | 2 => exact Or.inr (WeakUniversal.Step.collected (w2 obj op) 0 (wcmd op) (wseed obj op) rfl)
    | 3 => exact Or.inr (WeakUniversal.Step.propose (w3 obj op) 0 (wcmd op) (wseed obj op) rfl
              (by rw [wseed_eq]; exact wfam_input obj op))
    | (_ + 4) => exact Or.inl rfl

end Steps

theorem wfam_input_none (r : Nat) (hr : r + 1 ≠ 1) (p : Fin 1) :
    ((wfam obj op).environment obj (r + 1)).input p = none := by
  simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
    GCA.TimedExecution.views, GCA.SnapshotExecution.history, wfam]
  intro h
  exact absurd h (by omega)

theorem wstate_ge (t : Nat) (ht : 4 ≤ t) : wstate obj op t = w4 obj op := by
  match t, ht with
  | 0, h => omega
  | 1, h => omega
  | 2, h => omega
  | 3, h => omega
  | (_ + 4), _ => rfl

noncomputable def wsched : Weak obj (wfam obj op) where
  run := wrun obj op
  actor := fun _ => some 0
  step_actor := by
    intro t
    match t with
    | 0 => exact Or.inr (Or.inl ⟨0, rfl, WeakUniversal.Step.invoke (w0 obj) 0 op rfl (List.finRange 1) (List.Perm.refl _),
             fun q hq => absurd (Subsingleton.elim q 0) hq⟩)
    | 1 => exact Or.inr (Or.inl ⟨0, rfl, WeakUniversal.Step.read (w1 obj op) 0 0 (wcmd op) []
             (WeakUniversal.zeroSeed obj) rfl, fun q hq => absurd (Subsingleton.elim q 0) hq⟩)
    | 2 => exact Or.inr (Or.inl ⟨0, rfl, WeakUniversal.Step.collected (w2 obj op) 0 (wcmd op)
             (wseed obj op) rfl, fun q hq => absurd (Subsingleton.elim q 0) hq⟩)
    | 3 => exact Or.inr (Or.inl ⟨0, rfl, WeakUniversal.Step.propose (w3 obj op) 0 (wcmd op)
             (wseed obj op) rfl (wfam_input obj op),
             fun q hq => absurd (Subsingleton.elim q 0) hq⟩)
    | (_ + 4) => exact Or.inr (Or.inr ⟨0, 1, rfl, rfl, rfl⟩)
  gca_actor := by
    intro t p r hact hrd
    have hp : p = 0 := Subsingleton.elim p 0
    subst hp
    match t with
    | 0 => exact absurd (show (none : Option Nat) = some r from hrd) (by simp)
    | 1 => exact absurd (show (none : Option Nat) = some r from hrd) (by simp)
    | 2 => exact absurd (show (none : Option Nat) = some r from hrd) (by simp)
    | 3 => exact absurd (show (none : Option Nat) = some r from hrd) (by simp)
    | (_ + 4) =>
        have hr : r = 1 := (Option.some.inj hrd).symm
        subst hr
        rfl
  receive_ready := by
    intro t p r hrd hchange
    have hp : p = 0 := Subsingleton.elim p 0
    subst hp
    match t with
    | 0 => exact absurd (show (none : Option Nat) = some r from hrd) (by simp)
    | 1 => exact absurd (show (none : Option Nat) = some r from hrd) (by simp)
    | 2 => exact absurd (show (none : Option Nat) = some r from hrd) (by simp)
    | 3 => exact absurd (show (none : Option Nat) = some r from hrd) (by simp)
    | (_ + 4) => exact False.elim (hchange rfl)
  no_ghost := by
    intro r p s hin
    have hp : p = 0 := Subsingleton.elim p 0
    subst hp
    by_cases hr : r = 0
    · subst hr
      exact ⟨4, _, List.mem_cons_self ..⟩
    · rw [wfam_input_none obj op r (by omega)] at hin
      exact absurd hin (by simp)

theorem wopActor (t : Nat) : (wsched obj op).opActor t = some (wcmd op) := by
  show (WeakUniversal.ledger obj ((wsched obj op).run.state (t + 1))).active 0
      = some (wcmd op)
  match t with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (_ + 3) => rfl

theorem wopLive : (wsched obj op).OpLive := fun N =>
  ⟨N, Nat.le_refl _, by rw [wopActor obj op N]; rfl⟩

/-- **Nonvacuity of `blocked_output`.**  A process that is blocked in a GCA call
from time 4 onwards and is still scheduled at every step. -/
theorem blocked_and_stepping :
    ∃ s flag, ((wfam obj op).environment obj 1).output 0 = some (s, flag) := by
  refine (wsched obj op).blocked_output (fun r =>
      GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl))
    (wopLive obj op) (p := 0) (cmd := wcmd op) (r := 1)
    (proposal := wprop obj op) (N := 4) ?_ ?_
  · intro t ht
    have hst : (wsched obj op).run.state t = w4 obj op := wstate_ge obj op t ht
    rw [hst]
    rfl
  · intro N
    obtain ⟨i, hi, hval⟩ :=
      ((wsched obj op).schedule (wopLive obj op)).actorInst_of_actor
        (show ((wsched obj op).schedule (wopLive obj op)).actor N = some (wcmd op) from
          wopActor obj op N)
    exact ⟨N, i, Nat.le_refl _, hi, Subsingleton.elim _ _⟩

end
end Witness

end ConflictFreedom.GlobalSchedule
