# Formalization status

Lean 4.34.0 and Std only. No `sorry`, no project axioms: `KernelAudit.lean`
checks all 6652 project declarations and fails on anything beyond `propext`,
`Classical.choice` and `Quot.sound`.

**Every proposition, lemma and theorem of `main.tex` is formalized**, and **the
universal-construction theorems are proved as the manuscript states them: for
Algorithms 1 and 3 over any GCA objects meeting the GCA specification**, GCA
used as a black box, with Algorithm 2 proved to meet it (§0).  Two things are
assumed (§6).  The local trace calculations are classical functions, one step
each in the manuscript's own model; for every object whose independence
relation is decidable, every finite-state object among them, they are also
programs, which the kernel evaluates (§4).  And, by the author's scope
clarification, the snapshot objects are assumed: precisely, one fact from the
literature, used by no Lean theorem — that Algorithm 2 still meets the GCA
specification and Solo agreement when its atomic snapshot operations are
replaced by a wait-free linearizable read/write implementation.  The prose
sections (motivation, discussion, the figures' examples) are not formalized.

**Both constructions satisfy their progress condition in §3's own
vocabulary**, over any GCA meeting the specification and for the algorithms run
as deterministic machines: every non-halting run of Algorithm 1 or Algorithm 3,
for every client, every scheduler and every resolution of the choices the
manuscript leaves open (the order of each collect, and of `trace(M_i)`), is
admitted, with its GCA family reconstructed from the run (§1.4).
**Linearizability** holds for every run's whole, possibly infinite, event
history in the manuscript's own definition (§2), over any GCA meeting the
manuscript's specification (§2.1).

**§7 is formalized in full**, statement and proof, in the manuscript's form —
every finite execution *has* a finite conflict-forgetting (resp.
conflict-resolving) solo extension — over any GCA implementation meeting the
specification, with Solo agreement for Algorithm 1 as §7 assumes (§0.1, §5).
Conflict forgetting, Theorem `th:WeakUCresolve`, rests on GCA property 7, *Solo
agreement*, proved for Algorithm 2 (Lemma `GCA_soloagg`).  Conflict resolution,
Theorem `th:cr`, follows the manuscript's two-invariant proof.  Its invocation
point is stated openly — an operation's invocation may be placed at any point
of its code (`InvocationPoint`) — and the theorem places it where the proof
does, at the write of the command into `M` (Line 5), which is also the
instance's first operation step in §3's execution (§5.2).
`lemma:prefix-rounds` is proved once for both constructions (§5.3).

Nothing within scope is open (§6).

---

## 0. The constructions over any GCA

The manuscript presents Algorithms 1 and 3 over shared objects
`{GCA_k : k ≥ 1}` specified in §4.2, states their theorems before Algorithm 2
appears, and proves them from the specification alone.  The formalization states
and proves them the same way.

**The runs.**  `GlobalSchedule.WeakRun obj H` (Algorithm 1) and
`GlobalSchedule.HelpingRun obj H` (Algorithm 3) are runs of the program over the
whole-run GCA histories `H` — one table per round, whatever implements the
objects — driven by one global event sequence; the steps a process takes inside
a call are opaque (`step_actor`'s third case), and every input of a GCA object
is a proposal of the run (`no_ghost`).

**The interface** (`GlobalSchedule.lean`) is what the constructions require of
their GCA objects, and nothing else — not how they are implemented, how many
steps a call takes, or when an output becomes available:

| Field | Requirement | Manuscript |
| --- | --- | --- |
| `GCAInterface.spec` | each round's history satisfies the six properties | §4.2 |
| `GCAInterface.causal` | an output a process receives contains only commands of proposals already made to that object (`Execution.CausalGCA`) | implied by Validity, "for every execution", on the prefix ending with the receive |
| `GCAInterface.returns` | a process inside a call for ever is scheduled only finitely often (`CallsReturn`) | "every correct participant eventually returns" |
| `WeakRun.SoloAgreement` (only for `th:WeakUCresolve`) | if `i` returned from round `R` before anybody else called it, every output of `R` is `i`'s | GCA property 7, §7 |

The six properties are §4.2's as stated (`GCA.History.Specification`).  In
particular Validity is the manuscript's multiset inclusion,
`∀ i ∈ P_r, ops(t_i) ⊆ ⋃_{j∈P} ops(s_j)`, with `ops(s)` the multiset of
operations of `s` (§4.1) and `⋃` the usual multiset union, whose multiplicity is
the maximum (`Object.SubsetUnion`, `GCA.History.Validity`);
`validity_iff_le_maxOps_fin` writes the maximum out for `n` processes,
`ops(t_i)(a) ≤ max_{j∈P} ops(s_j)(a)`, and `validity_iff_occurs` gives the
equivalent occurrence-by-occurrence form the proofs use.

`WeakGCA obj H` and `HelpingGCA obj H` bundle a run with the interface, and
`algorithm1AnyGCA`, `algorithm3AnyGCA` are the §3 implementations they admit.

**The interface is implied by the manuscript's specification.**
`WeakRun.gcaInterface_of_prefixSpec` (and `HelpingRun.…`): if the six
properties hold for the history of every prefix of the run
(`Execution.prefixHistory`) — "the following properties hold for every
execution" — and the tables record exactly what the GCA objects did (every
output received), then the interface holds (whole histories are long prefixes,
`Execution.exists_prefixHistory_eq`; prefix Validity gives `causal`).

**The theorems, over any GCA meeting the interface.**

| Manuscript | Lean |
| --- | --- |
| Thm `weakUCWCF` | `algorithm1AnyGCA_weakConflictFree : WeakConflictFree (algorithm1AnyGCA obj n) obj.Conflict` |
| Lemma `UCV2isCF` | `algorithm3AnyGCA_conflictFree : ConflictFree (algorithm3AnyGCA obj n) obj.Conflict` |
| …obstruction-freedom | `algorithm1AnyGCA_obstructionFree`, `algorithm3AnyGCA_obstructionFree` |
| Thm `weakUCLin`, Algorithm 3's linearizability lemma | `WeakGCA.infinite_event_linearization`, `HelpingGCA.infinite_event_linearization` (whole history), `WeakGCA.event_linearization`, `HelpingGCA.event_linearization` (every finite prefix); only `spec` and `causal` are used: `WeakRun.infinite_event_linearization`, `HelpingRun.…` |
| `lemma:prefix-rounds` | `WeakRun.prefix_rounds`, `HelpingRun.prefix_rounds` (only `spec`) |
| Thm `th:WeakUCresolve` | as stated, over any GCA implementation with the specification and Solo agreement: `algorithm1Over_weakUCresolve` (§0.1); inside one run: `WeakGCA.weakUCresolve` |
| Thm `th:cr` | as stated, over any GCA implementation with the specification: `algorithm3Over_conflictResolution` (§0.1); inside one run: `HelpingGCA.conflictResolution` |

For §7 a finite execution `α` is the first `N` steps of a run `g`, and an
extension is any run over GCA objects meeting the interface (and, for
`th:WeakUCresolve`, Solo agreement) that takes the same first `N` steps
(`WeakRun.Extends`, `HelpingRun.Extends`).  `ConflictForgetting` and
`ConflictResolving` quantify over those extensions.  The theorems are in their
modular form: **every** `i`-solo continuation of `α` (`g.SoloFrom N i`) has a
finite conflict-forgetting (resp. conflict-resolving) prefix longer than `α`.
Whether a solo continuation exists is a property of the GCA implementation, not
of a table: §0.1 proves it exists for every implementation meeting the
specification, which gives the manuscript's existential statements.

**Algorithm 2 meets the interface** (`Algorithm2Interface.lean`), in its
composition with either construction (`GlobalSchedule.Weak`,
`GlobalSchedule.Helping`), under fairness at the receive and the wait-free
snapshot assumption:

| Requirement | Proof |
| --- | --- |
| six properties | `UniversalProtocol.Family.specifications` |
| Validity on every prefix | `Weak.causalGCA`, `Helping.causalGCA` |
| calls return | `Weak.callsReturn`, `Helping.callsReturn` |
| Solo agreement | `Weak.soloAgreement` (Lemma `GCA_soloagg`) |

`Weak.toGCA`, `Helping.toGCA` package it without changing the run, so
`algorithm1_anyGCA`, `algorithm3_anyGCA` include the Algorithm 2 admitted sets,
and `forward1_anyGCA`, `forward3_anyGCA` the executions of the machines.  Every
concrete theorem below — `algorithm1_weakConflictFree`,
`algorithm3_conflictFree`, `forward1_weakConflictFree`,
`forward3_conflictFree`, `Forward.weakUCresolve`, `Forward.conflictResolution`
— is a corollary of its modular form.
Linearizability of the composition needs no liveness assumption and is proved
directly (`Weak.infinite_event_linearization`, `Helping.…`).

**Where the assumptions enter.**  Besides the six properties, the liveness
proofs use three facts: a process scheduled infinitely often does not stay
inside a GCA call for ever — the interface's `returns`, proved for Algorithm 2
from fairness and the snapshot assumption (`callsReturn`); call coverage,
derived from `no_ghost`; and, for `th:WeakUCresolve` only, Solo agreement,
through `solo_round_outputs`.  The schedule-level lemmas are split accordingly between
the bare runs (`WeakRun`, `HelpingRun`: no assumption on the GCA objects), the
runs over the interface (`WeakGCA`, `HelpingGCA`), and the Algorithm 2
composition (`Weak`, `Helping`: `Fair`, `callsReturn`, the protocol clock).  The
solo extensions of §7 use only the Step-level invariants
`WeakUniversal.round_invariant` and `HelpingUniversal.call_tracking`, so they
are proved for any run over the interface (`WeakGCA.solo_extension`,
`HelpingGCA.solo_extension`).

### 0.1 GCA objects as an implementation: §7 in the manuscript's form

Theorems `th:WeakUCresolve` and `th:cr` assert that a finite execution **has** a
solo extension with a property.  A run over tables `H` fixed in advance cannot
provide one — the tables say nothing about what the objects would answer if the
run went differently — so the GCA objects must be something that can be run.

**The implementation** (`GCAMachine.lean`).  A `GCAMachine` is any GCA
implementation serving every round, as an abstract machine: a state, `step`
(one step of a caller's current call to round `r` with proposal `v`), `output`
(`some (t, c)` once that call has finished) and `leave` (the state after the
caller returns).  Nothing else is fixed.  A client drives it (`Driven`): at each
instant one process or none is scheduled; a caller whose call has not finished
takes a step of it, one whose call has finished returns; a process outside a
call takes a program step that leaves the machine alone and may enter a round it
has never been in, with any proposal.  The history of round `r` in a run
(`history`) has the proposals of the processes that entered it as inputs and
the outputs returned as outputs.

| Requirement on `G` | Lean | Manuscript |
| --- | --- | --- |
| six properties, in every run | `IsGCA.spec` | §4.2, "for every execution" |
| every correct participant returns, in every run | `IsGCA.returns` | §4.2 |
| Solo agreement, on every prefix of every run | `SoloAgreement` | GCA property 7, §7 |

Finite executions are runs: a run cut at `T` and idling afterwards is a run
(`Driven.cut`), whose histories are those of the prefix (`history_cut_input`,
`returned_cut_iff`), so `IsGCA.spec` holds on every prefix too.

**Algorithm 2 is one** (`GCAMachineAlgorithm2.lean`): `ForwardGCA.machine`
meets the specification (`machine_isGCA` — each round's history has the
reconstructed protocol's inputs and a subset of its outputs, and the six
properties survive dropping outputs, `GCA.History.Specification.of_outputs_sub`;
a caller finishes within six of its own steps) and Solo agreement
(`machine_soloAgreement`, from Lemma `GCA_soloagg` at the prefix's own clock).
So the hypotheses below are satisfiable.

**The constructions over any implementation** (`Algorithm1OverGCA.lean`,
`Algorithm3OverGCA.lean`).  `WeakUniversal.Over.mrun G ch client sched` and
`HelpingUniversal.Over.mrun G ch client sched` run Algorithm 1 (resp. 3) over `G`
for any rule `ch` for the choices the algorithm leaves open (§1.4), any client
and any scheduler.  Every run is a run over its own histories
(`weakRun`, `helpingRun`), each of its prefix histories is the history of a run
of `G` (`prefixHistory_eq`), so its GCA objects meet the interface of §0 when
`G.IsGCA` (`Over.gcaInterface`) and Solo agreement when `G.SoloAgreement`
(`Over.soloAgreement`).  Over Algorithm 2 these are the forward machines of
§1.4 (`Over.mrun_machine`).

| Manuscript | Lean, for every `G` with `G.IsGCA` |
| --- | --- |
| Thm `th:WeakUCresolve` (with Solo agreement) | `algorithm1Over_weakUCresolve` (`Over.weakUCresolve`) |
| Thm `th:cr`, with the invocation point at Line 5 | `algorithm3Over_conflictResolution` (`Over.conflictResolution`) |
| Thm `weakUCWCF`, Lemma `UCV2isCF` | `algorithm1Over_weakConflictFree`, `algorithm3Over_conflictFree` (admitted sets non-empty: `algorithm1Over_nonempty`, `algorithm3Over_nonempty`) |
| linearizability | `WeakUniversal.Over.infinite_event_linearization`, `HelpingUniversal.Over.…` |

The §7 statements: for every finite execution `α` — the first `N` steps of
`mrun G ch client sched`, any rule, any client, any scheduler — and every process `i`, there
is `N' > N` such that the run under `soloSched sched N i` extends `α`, schedules
only `i` from `N` to `N'`, and its first `N'` steps are conflict-forgetting
(resp. conflict-resolving): every eventually weakly `α'`-conflict-free (resp.
eventually `α'`-conflict-free) infinite extension of them **over the same `G`**
completes the operations of some process that takes infinitely many steps (resp.
of every correct process).  The definitions are those of §5, read on the run
over `G` (`Over.ConflictForgetting`, `Over.ConflictResolving`), and are not
vacuous over any `G` (`Over.conflictForgetting_hypothesis_satisfiable`,
`Over.conflictResolving_hypothesis_satisfiable`).  The proofs apply
`WeakGCA.weakUCresolve` and `HelpingGCA.conflictResolution` to the run under the
solo scheduler, and to every extension over `G`: only the six properties,
"calls return", and — for Algorithm 1 — Solo agreement are used.

---

## 1. Liveness of the universal constructions

### 1.1 What is proved

| Manuscript result | §3 statement about the construction | Lean |
| --- | --- | --- |
| **Thm `weakUCWCF`** (Algorithm 1, any GCA meeting the interface) | `WeakConflictFree (algorithm1AnyGCA obj n) obj.Conflict` | `algorithm1AnyGCA_weakConflictFree` (§0) |
| **Lemma `UCV2isCF`** (Algorithm 3, any GCA meeting the interface) | `ConflictFree (algorithm3AnyGCA obj n) obj.Conflict` | `algorithm3AnyGCA_conflictFree` (§0) |
| — over Algorithm 2 | `WeakConflictFree (algorithm1 obj n) obj.Conflict`, `ConflictFree (algorithm3 obj n) obj.Conflict` | `algorithm1_weakConflictFree`, `algorithm3_conflictFree` |
| — its solo half alone | `ObstructionFree (algorithm1 obj n)`, `ObstructionFree (algorithm3 obj n)` | `algorithm1_obstructionFree`, `algorithm3_obstructionFree` |
| Both, at the schedule level | — | `WeakGCA.weakUCWCF`, `HelpingGCA.UCV2isCF`, `HelpingGCA.operation_completes_time` |
| Conflict-free half over instances | — | `WeakGCA.execution_weakConflictFree_half`, `HelpingGCA.execution_conflictFree` |
| GCA termination | — | `GCA.Protocol.terminates`, `returned_of_infiniteSteps` |
| §3 hierarchy and the two reductions | — | `progressHierarchy`, `empty_*`, `universal_*` |
| **The same, for the algorithms as machines** | `WeakConflictFree (forward1 obj n) obj.Conflict`, `ConflictFree (forward3 obj n) obj.Conflict` | `forward1_weakConflictFree`, `forward3_conflictFree` (§1.4) |
| **Thm `WeakUCresolve`** (Algorithm 1, §7, any GCA meeting the interface and Solo agreement) | every `i`-solo continuation of a finite execution has a finite conflict-forgetting prefix | `WeakGCA.weakUCresolve` (§0) |
| **Thm `cr`** (Algorithm 3, §7, any GCA meeting the interface) | every `i`-solo continuation of a finite execution has a finite conflict-resolving prefix | `HelpingGCA.conflictResolution` (§0) |
| — for the machines | every finite execution of the machine has a finite conflict-forgetting (resp. conflict-resolving) `i`-solo extension, for every `i` | `Forward.weakUCresolve` (§5.1), `Forward.conflictResolution` (§5.2) |

Each of the two headline results implies obstruction-freedom through §3's own
hierarchy (`weakConflictFree_obstructionFree`, `conflictFree_obstructionFree`),
so `algorithm1_obstructionFree` and `algorithm3_obstructionFree` are corollaries
kept as separate entry points.

**Algorithm 1.** `WeakGCA.weakUCWCF` proves both halves at the schedule level.
Restating the conflict-free half in §3's vocabulary needs one bridge,
`WeakRun.infiniteSteps_of_stepping`: the schedule-level witness is
`g.Stepping p`, scheduling in the global schedule, whereas §3 asks for
`Execution.InfiniteSteps p`, infinitely many *operation* steps owned by `p`. A
scheduled process either holds a current command, and then the operation clock
ticks for it at once, or is idle, and then `step_actor` forces it to `invoke`,
so it holds one at its next scheduled tick — and `localState_const_of_unscheduled`
shows it cannot lose the command in between, since finishing would require being
scheduled. `WeakRun.live_of_opLive` discharges the remaining `g.Live` hypothesis.

**Algorithm 3.** `ConflictFree` is the manuscript's Lemma `UCV2isCF`. Its
conflict-free half follows the manuscript's **two invariants**:

* `HelpingGCA.output_contains_own` — invariant (II). With `M[i]` permanently
  announcing `cmd(Φ)`, every proposal to a high round contains it and commutes
  with the rest of its residual, so `t · cmd(Φ)` is below every proposal and GCA
  Common Prefix carries `cmd(Φ)` into every output.
* `HelpingGCA.commit_high_completes` — the step (II) unlocks: a commit above the
  bound carries `cmd(Φ)` into `S`, and `i`'s next collect completes `Φ`.
* `HelpingGCA.nonconflicting_pending_of_eventually` — with no commit above the
  bound, responses are frozen *as a conclusion*, so a command not returned
  below the bound is not returned at all, any two such are simultaneously
  pending, and §3's time-based hypothesis applies. That is invariant (I)'s
  input, and `inputs_compatible` is (I).

Algorithm 1's proof freezes responses by assumption; Algorithm 3's cannot, and
invariant (II) supplies the freeze.

### 1.2 Non-vacuity: what the witnesses exercise

By the refinement of §1.4, *every* non-halting run of the machines, for every
client, scheduler and rule for the open choices, is an admitted execution.  The
witness runs below have a different role: each is a concrete run in which a
specific phenomenon is *proved* to happen.  The three hand-built ones are full
`GlobalSchedule`s proved `Fair`, `OpLive` and snapshot-wait-free; the
adopt-branch runs are runs of the machines, computed, and admitted by §1.4.

The process count `n` is arbitrary.  At `n = 0` there is no execution at all —
some instance must take a step at arbitrarily late times, and every instance
belongs to a process (`Execution.false_of_zero`) — so every theorem about an
implementation's executions is vacuous there, as is every statement about a
process `i : Fin n`.  The non-emptiness theorems (`algorithm1_nonempty`,
`algorithm3_nonempty`, `forward1_nonempty`, `forward3_nonempty`,
`algorithm1Over_nonempty`, `algorithm3Over_nonempty`) hold for every
`n = m + 1`.  Assuming `0 < n` would only weaken the theorems.

**Algorithm 3, one stalled process** — `ContentionWitness.lean`, `WitnessC.wsched`,
two processes, cycle of 19 steps.  Process `1` invokes and announces, then takes
no further step: the faulty process with a forever-pending operation that the
helping mechanism exists for.  Process `0` cycles for ever, so its `M` collect
gathers process `1`'s command as well as its own, and round `1` commits both.

**Algorithm 1, one stalled process** — `WeakContentionWitness.lean`,
`WitnessW.vsched`, two processes, cycle of 14 steps after a one-step prologue.
Process `1` invokes and stops inside its collect; process `0` completes one
operation per cycle.  Algorithm 1 has no announcement array, so nobody helps:
the stalled command is invoked, never proposed and never answered — which is
exactly the contrast with `WitnessC`, where the same picture under Algorithm 3
has that command committed by round `1`.

**Algorithm 3, two callers sharing every round** — `SharedRoundWitness.lean`,
`WitnessS.ssched`, two processes in lockstep, cycle of 38 steps, no prologue.
Both announce, both collect the *same* `M`, so `observe` builds the same command
list for both and they propose the **identical** trace to round `k + 1`.  Both
are participants of that round; process `0` takes its six protocol events at the
round-clock positions `0 … 6` and process `1` at `7 … 13`; inputs being equal,
Weak Agreement forces both returns to be commits and Common Prefix with Validity
forces the returned trace to be the common proposal.  Both publish, both find
their own command, both respond.

| Claim | Lean |
| --- | --- |
| Algorithm 3: contended run admitted, two instances concurrently pending | `algorithm3_nonempty_contended`, `algorithm3_contended` |
| …two commands in flight, neither answered, `M[1]` non-empty | `WitnessC.two_in_flight` |
| …round `1` commits both commands | `WitnessC.round_one_commits_both` |
| Algorithm 1: contended run admitted, two instances concurrently pending | `algorithm1_nonempty_contended`, `algorithm1_contended` |
| …two commands in flight, neither answered | `WitnessW.two_in_flight` |
| …without helping the stalled command is never answered, at any time | `WitnessW.stalled_never_returns` |
| Algorithm 3: run whose every round has two GCA participants | `algorithm3_nonempty_sharedRound`, `algorithm3_sharedRound` |
| …both callers blocked in the same round on the same proposal | `WitnessS.shared_round` |
| …`participants = [0,1]`, equal inputs, both outputs commit, both commands in the committed trace | `WitnessS.round_commits_both` |
| …the two proposals really coincide | `WitnessS.proposal_eq` |

So contention, a non-trivial announcement array, a real pair for §3's conflict
hypothesis, and a genuinely shared GCA round are all exercised;
`algorithm1_weakConflictFree` and `algorithm3_conflictFree` apply to executions
that have them.

**The adopt branch** — `AdoptWitness.lean`.  In the three hand-built witnesses
every `Step.receive` gets `flag = true`.  An adopt needs two callers proposing
*incompatible* traces to one round, and a proof of it needs Algorithm 2's own
calculations evaluated rather than Weak Agreement invoked.  Both runs below are
runs of the machines (Algorithm 1 or 3 over Algorithm 2), for a counter no two
of whose operations commute and two processes invoking one operation each; they
are computed — independence is decidable for the object, so the machines are
programs (`MachineCompute`, §4) — and the kernel evaluates them (`decide`).

| Phenomenon | Lean |
| --- | --- |
| Algorithm 1: both callers of round 1 propose a one-command trace, incompatible; GCA answers process `0` `(ε, false)`; the receive keeps it in Line 5's loop, ready from `(1, ε)`; its next step proposes to round 2 | `AdoptWitness.Alg1.adopts` |
| Algorithm 3: process `1` has read both announcements and proposes `c₁ · c₀` against process `0`'s `c₀`; GCA answers process `0` `(ε, false)`; it collects `S` (Line 16), finds no trace with its command, and retries — collecting `M` again from `(1, ε)` | `AdoptWitness.Alg3.retries` |
| Both runs are admitted executions | `Alg1.admitted`, `Alg3.admitted` |

The Algorithm 3 run collects `M` in reverse index order, so the helper reads its
own announcement first.  In index order it would propose `c₀ · c₁`, which
extends `c₀`: the two inputs would be compatible.  Helping keeps proposals
compatible unless the arrangement of `trace(M_i)` — which the manuscript leaves
open (§1.4) — puts the helper's command first.

The witnesses' snapshot interface always acknowledges, but that is not a gap:
`GCA.Protocol.waitFree_of_acknowledged_cofinal` shows `SnapshotWaitFree` only
asks for *eventual* acknowledgement, and `alternating_waitFree` exhibits a
protocol that acknowledges on every other step and still satisfies it. So the
assumption is not silently the atomic special case.

### 1.3 The model the liveness results are proved in

Over any GCA (§0) the admitted sets are the operation-live runs over GCA objects
meeting the interface, and the interface is the only assumption.  The rest of
this section describes the composition with Algorithm 2, whose assumptions are
exactly what `Weak.gcaInterface` uses to prove Algorithm 2 meets the interface.

The Algorithm 2 admitted sets are the executions extracted from a global
schedule that carries the program run and the GCA protocol family on one clock,
joined by `step_actor`, `gca_actor`, `no_ghost` and `receive_ready`. Liveness
assumes:

* **`Fair`** — a scheduled process whose GCA call has produced its output *on
  the projected protocol clock* takes the corresponding step. The guard is
  essential, not cosmetic: `FairnessClock.lean` proves the unguarded reading
  (`StrongFair`, "the call has returned somewhere in the run") is
  **unsatisfiable** whenever a call returns (`Weak.strongFair_absurd`), so every
  theorem assuming it would be vacuous.
* **`OpLive`** — `∀ N, ∃ t ≥ N, (g.opActor t).isSome`: at arbitrarily late times
  *some* process with an active command is scheduled. Read the quantifiers
  carefully — this is **not** a per-process obligation, and it does **not** say
  that every pending process keeps taking steps. Crashed and stalled processes
  with forever-pending operations are allowed; `WitnessC` and `WitnessW` (§1.2)
  each have one. `Fair` is likewise a *scheduled* process's obligation to
  consume an already-ready subroutine result, not scheduler fairness for every
  process.
* **`SnapshotWaitFree`** — the author's explicit scope clarification: assume a
  wait-free linearizable snapshot interface; do not implement it or reprove the
  external result. It asks only that an active caller be acknowledged at
  arbitrarily late times, so a real snapshot algorithm's internal stuttering is
  admitted (`SnapshotStutter.lean`).

Call coverage is *not* assumed: `Weak.callsCovered` / `Helping.callsCovered`
derive it. Caller liveness is *not* assumed either:
`FiniteScheduling.eventually_stepping` derives it.

### 1.4 The algorithms as machines: refinement into the admitted model

`algorithm1` and `algorithm3` admit an execution when *there exists* a GCA
family and a global schedule consistent with it. The family — every round's
inputs — is data chosen before the run, and a `propose` step is enabled only if
the proposal happens to equal the pre-ordained input.  That every run of the
actual algorithms is admitted therefore needs a proof, and this section gives
it.

**The machines.** `WeakUniversal.Forward.frun` and
`HelpingUniversal.Forward.frun` are deterministic step functions driven by a
scheduler `sched : Nat → Option (Fin n)` (idle ticks, and a crash as never being
scheduled again) and a client `client : Fin n → Nat → Op` (the operation of each
process's `k`-th invocation), and by a rule `ch : Forward.Choices` for the
choices the manuscript leaves open, below: the order of each collect and, in
Algorithm 3, the order of `trace(M_i)`. Each step is a local computation followed by at
most one atomic access, to a register `S[j]` or `M[j]` or to a snapshot object
of the GCA round the process is in. GCA rounds run **Algorithm 2 literally**
(`ForwardGCA`): line 1 writes `A[i]`, line 2 scans `A`, lines 3–4 compute the
pair `(⊔ A_i^co, A_i = A_i^co)` and write it to `B[i]`, line 5 scans `B`, and
lines 6–8 compute the output from the caller's own two scans. No round has an
input before somebody proposes to it.

**The refinement.** From a run, the per-round `GCA.Protocol` is reconstructed
after the fact: participants are the processes that were ever blocked in the
round, inputs are what they proposed, and the actor sequence is the order in
which they took the round's steps (`ForwardGCA.retro`). The run itself is then a
`GlobalSchedule` for that family (`fsched`), and it is `Fair` and `OpLive` by
construction.

| Claim | Lean |
| --- | --- |
| What a caller computes from its own scans **is** the timed-execution output of the reconstructed protocol | `ForwardGCA.output_agrees` |
| …via the invariant that every snapshot object and frame is what the reconstruction says | `ForwardGCA.Inv.all` |
| No process ever calls a GCA object twice | `Forward.driven` (field `prog`), from `Good.bound` |
| The run is a global schedule for the reconstructed family, fair and operation-live | `Forward.fsched`, `fsched_fair`, `fsched_opLive` |
| **Every non-halting run is admitted** | `forward1_admitted`, `forward3_admitted` |
| Every run, halting or not, is linearizable — as a chain, and as one whole event history in the manuscript's sense | `Forward.forward_chain_linearization`, `Forward.forward_infinite_linearization` (both) |
| Hence the progress conditions hold for the machines | `forward1_weakConflictFree`, `forward3_conflictFree` |
| The machines have runs, for every client and every `n ≥ 1` | `forward1_nonempty`, `forward3_nonempty` |
| With no process there is no execution, so every statement about executions is vacuous at `n = 0` | `Execution.false_of_zero` |

**The collects, and Line 11 of Algorithm 3, are not fixed.** The manuscript
fixes neither the order in which a collect reads its registers — Line 4 of
Algorithm 1 collects `S`; in Algorithm 3, Lines 6 and 16 collect `S` and Line 10
collects `M` — nor the order of `trace(M_i)` at Line 11 of Algorithm 3, and the
model does not either.  Every collect reads the `n` registers in any order,
chosen when it starts (any permutation of the registers): in
`WeakUniversal.Step`, `invoke` for the collect of Line 4; in
`HelpingUniversal.Step`, `announce` for the collect of Line 6, `receive` on an
adopt and `publish` for that of Line 16, `collectedStart` and `retry` for that of
Line 10.  `HelpingUniversal.Step.propose` appends the missing announcements the
collect found in any order (any permutation `arranged` of them).  Every theorem
about runs of either algorithm — safety, liveness, `th:WeakUCresolve`, `th:cr` —
therefore holds whatever the choices, including choices that change from one
collect to the next.  The machines take the choices as a parameter, a rule that
may depend on the whole configuration and on the process:
`WeakUniversal.Forward.Choices` gives an order of the registers for a collect of
`S` (`slotOrder`); `HelpingUniversal.Forward.Choices` gives one for a collect of
`S` (`slotOrder`) and one for a collect of `M` (`announcementOrder`), and an
arrangement of any list of announcements.  Every theorem about the machines —
`forward1_admitted`, `forward1_weakConflictFree`, `Forward.weakUCresolve`,
`forward3_admitted`, `forward3_conflictFree`, `Forward.conflictResolution`, and
their counterparts over any GCA — is proved for every rule (`Choices.inOrder`,
index order and, in Algorithm 3, read order, is one for each).  What the proofs
use is only what every choice shares: a collect reads each register exactly once,
and every arrangement has the same operations with the same multiplicities
(`proposal_count_perm`); compatibility of proposals then comes from the
non-conflict of pending commands, as in the manuscript.

The execution admitted is literally the machine's: `fsched_state` and
`fsched_actor` are `rfl`, so histories, crashes, infinite stepping and eventual
conflict-freedom are the machine's own. Quantifying over all functions
`Fin n → Nat → Op` and `Nat → Option (Fin n)`, and over all rules `ch`, also
covers adaptive clients, adversarial schedulers and adversarial collect orders:
a run is determined by the choices actually made, and those choices are some
fixed client, schedule and rule.

**Invocations come from the environment, as in Herlihy and Wing.** The
manuscript's executions *induce* their histories (§2, "Histories and
linearizability"), and the machines realize the open reading of that model too.
An invocation is the `invoke` step (Lines 1–3), which touches no shared object —
it fixes the command, with the operation the client supplies — so where the
scheduler places it is exactly where an environment issues the invocation: an
idle process may be invoked at any time, and its first shared-memory step may
come arbitrarily later, or never.  In the §3 execution the `invoke` step is not
an operation step of the new instance — the actor of an operation step is the
command active before it (`opActor_eq_some`) — so a pending invocation never
followed by a step, a faulty process in Herlihy and Wing's model, is an
execution of the machines: schedule the process once and never again.
`WeakContentionWitness` exhibits one in Algorithm 1's admitted model (process
`1` invokes and never moves again).  A response is the `finish` step, local as
well.  With the client covering adaptive environments (above), every sequence
of invocations an environment can issue to well-formed processes is realized by
some client and schedule.  What is not in Lean is a separate open-environment
model and a theorem identifying its histories with the machines'; the
identification is the one just given, event for event (§6).

**What the machines assume.**
* Snapshot operations are **atomic**. That is the author's assumption — a
  wait-free *linearizable* snapshot object — taken at face value: by
  linearizability each update and scan takes effect at one point. The
  snapshot implementation itself is not modeled (`SnapshotStutter` separately
  shows the admitted model tolerates implementations with internal steps); §6
  states the one external fact this leaves.
* The local calculations are the classical `gcaCandidate`/`traceGLB`, as in the
  manuscript's model, where a local computation is one step.  For an object
  whose independence relation is decidable they are computed instead, and the
  machines are programs with the same runs (`MachineCompute`, §4).
* The flag `A_i = A_i^co` of line 4 is computed as "`A_i` is compatible", the
  reading `GCA.SnapshotExecution.Flag` already uses.

---

## 2. Safety

Complete for the modeled schedules, with no fairness, coverage or provenance
hypothesis.

| Result | Lean |
| --- | --- |
| Every finite boundary has a legal linearization | `Weak.finite_linearization`, `Helping.finite_linearization` |
| One order linearizes every boundary, as a chain of literal prefixes | `Weak.chain_linearization`, `Helping.chain_linearization` |
| Positions and relative order are never revised | `Object.chain_idxOf_stable`, `chain_order_stable` |
| Histories as the manuscript's invocation/response events, `H̄\|ᵢ = S\|ᵢ` and `≼_H ⊆ ≼_S` | `EventHistory.lean`, `LedgerEvents.lean`, `Weak.event_linearization`, `Helping.event_linearization` |
| The whole run as one, possibly infinite, event history — well formed, recording exactly what the run did | `Run.events`, `Run.events_upto`, `Run.events_wellFormed` |
| **The whole history is linearizable, as the manuscript defines it**: a completion `H̄`, a legal sequential history `S`, `H̄\|ᵢ = S\|ᵢ` for every process, `≼_H ⊆ ≼_S` | `Weak.infinite_event_linearization`, `Helping.infinite_event_linearization` |
| The infinite-history definition is the manuscript's on finite histories | `Object.infEventLinearizable_ofHistory_iff` |
| The safety statements have content, including on an infinite history | `Witness.completedSchedule`, `completed_linearization`, `completed_event_history`, `Witness.rsched_history_infinite` |

**The proof** follows `theorem:weakUCLin`'s.  The chain is the manuscript's
`t_k`, `GCA.RoundExecution.committedChain`: `t_0 = ε`, `t_k` the trace
committed at round `k` — unique by Adoption (`committedChain_commit`) — and
`t_k = t_{k-1}` when round `k` commits nothing; `lemma:prefix-rounds` gives
`t_k ≤ t_{k+1}` (`committedChain_mono`).  The representative at boundary `N` is
`t̂ = ŝ_1 ⋯ ŝ_{r*}`, one block per round (`chainRep`), with `r*` the last round
of the responses observed by `N`.  An operation that returned with a trace
committed at round `k` is associated with `t_k`: its response is
`ret*(cmd, t_k)`, kept in `t_{r*}` by `lemma:ret-trace-prefix`, and, since every
command of `t_k` was invoked before it returned, an operation invoked later is
outside the block prefix `ŝ_1 ⋯ ŝ_k`, so real-time order holds
(`Object.roundChain_linearizes`, `WeakUniversal.committedChain_linearizes`, used
by both constructions).  As `r*` only grows, the representatives at successive
boundaries are literal prefixes of one another, and their limit linearizes the
whole history.

The whole-run statement is literal. `InfiniteHistory.lean` states the
manuscript's notions — invocation, response, pending, `H|ᵢ`, `≼_H`,
well-formedness, completion, the sequential history `S_X` of a possibly infinite
schedule, linearizability — on possibly infinite event sequences, presented as
concatenations of finite blocks; `H̄|ᵢ = S|ᵢ` is `SameEvents`, equality of the
two event sequences. The completion `Run.completed` drops the invocations the
linearization never retains and answers each retained invocation the run never
answers right behind that invocation: an infinite history has no end to append
to, and a pending operation is the last of its process (`active_evolution`), so
the placement does not change `H̄|ᵢ`. `S` is `S_t̂` for the chain's limit
`t̂ = chainLimit x`, a single finite or infinite order. As is conventional, the
real-time clause of `EventLinearizable` and `InfEventLinearizable` ranges over
the operations the completion retains.

### 2.1 What the constructions need from GCA

The manuscript uses GCA as a black box specified by the six properties of §4.2,
which must hold for every execution. The linearizability proofs consume exactly
three conditions from it (`GCAInterface.lean`):

1. the six properties, of each round's whole-run history:
   `∀ r, (H (r + 1)).Specification`;
2. every input is a proposal of the construction: `CallsCovered`;
3. **causal validity**: an output a process receives contains only commands of
   proposals already made to that GCA object: `Execution.CausalGCA`.

(3) is not an assumption beyond the manuscript. Its properties hold for every
execution, so for every finite prefix, and Validity of the prefix that ends
with a receive implies (3) (`causalGCA_of_prefixValidity`). The model's GCA histories
are whole-run tables and `Specification` checks them as such, which captures
only the complete-execution instance; (3) supplies the prefix instance.

| Claim | Lean |
| --- | --- |
| With the interface, both constructions are linearizable over **any** GCA — per boundary, as a chain, in event form, and for the whole event history | `Execution.causal_finite_linearization`, `causal_chain_linearization`, `causal_event_linearization`, `causal_infinite_event_linearization` (both) |
| …in particular over any GCA meeting the manuscript's specification on every prefix | `Execution.causalGCA_of_prefixValidity`, `spec_finite_linearization`, `spec_infinite_event_linearization` (both) |
| …because causal validity is what makes every returned command an invoked one | `Execution.returnsInvokedBy_of_causalGCA` (both) |
| The composed Algorithm 2 meets the interface; the headline safety theorems go through it | `Weak.causalGCA`, `Helping.causalGCA`, `Weak.meets_interface`, `Helping.meets_interface` |
| **The whole-run reading alone is too weak for Algorithm 3**: a GCA table satisfying all six properties as a whole, whose inputs are all the run's own proposals, over which Algorithm 3 is not linearizable — the table fails Validity on a prefix | `NonCausalWitness.whole_history_spec_not_enough`, `validity_fails_at_output` |
| **Algorithm 1 needs only the whole-run reading**, once every GCA input is a proposal of the run | `Execution.returnsInvokedBy_of_covers`, `covered_finite_linearization`, `covered_chain_linearization`, `covered_infinite_event_linearization` |

The counterexample (`NonCausalWitness`) has three processes over a counter.
Process 1 reads, and its round-1 output already holds the increment of
process 0, so it returns 1. Only afterwards is the increment invoked and
announced, and a slow helper, process 2, proposes it to round 1: it collected
`S` before anything was published, and gathered the announcements late. The
table is consistent as a whole — every command of an output is in some input —
but in the prefix ending with process 1's receive no input holds the increment,
so it is not a GCA history in the manuscript's sense. The formalization must
therefore carry the prefix instance of Validity; the manuscript's "for every
execution" already does. Algorithm 1 has no helping: a command enters a
proposal only as its invoker's own, and the invoker collects `S` after invoking,
so it proposes above every round published before the invocation
(`Execution.floor`); by induction on rounds, every command of a returned trace
was proposed by its invoker to a round no higher (`Execution.own_proposal`), and
hence invoked before the return.

---

## 3. Supporting development

* Object semantics and the conflict relation: `Object.CommuteAt`,
  `Object.Conflict`, `command_conflict_iff` — response-sensitive, with
  invocation tags.
* Schedule equivalence, **as the manuscript defines it**:
  `traceEq_iff_scheduleEquiv` identifies the adjacent-swap quotient with
  `ScheduleEquiv` — equal multisets, and every precedence `a⁽ⁱ⁾ ≺ₛ b⁽ʲ⁾` between
  conflicting occurrences of `s` kept in `s'`, with `≺ₛ` read in `s` itself.
  `traceEq_iff_occurrenceEq` is the same statement with `≺ₛ` read in the
  two-letter projection, and `occurrencePrecedes_iff_schedulePrecedes` shows the
  two readings agree.
* Traces: `traceEq_iff_labeledOccurrenceEq`, `glb_exists`, `lub_exists`,
  response stability under extension.
* GCA / Algorithm 2: `GCA.Protocol.specification`, `Family.specifications` —
  all six properties, above the assumed snapshot interface.
* The constructions: `WeakUniversal.Step`, `HelpingUniversal.Step` —
  register-level transitions composed with operational GCA families.

---

## 4. The model/computation boundary

The manuscript's model says a *step* of a process is "a local computation
followed by at most one atomic (read or write) operation on a register"
(§"Algorithms and executions"). A local computation is therefore one step,
whatever it costs. `GCA.Protocol.advance` is faithful to that: stages `2` and `5`
— the candidate calculation of GCA line 4 and the output calculation of line 6 —
each advance in a single scheduled step, exactly as stages `0,1,3,4` are the
four assumed snapshot operations. So `traceGLB`, `traceLUB`, `compatiblePart`,
`gcaCandidate` and `gcaOutput` are `noncomputable` *mathematical specifications*
of those steps, in the manuscript's own convention — not a claim about running
code, and not an extra assumption.

`EffectiveInterface.lean` makes the boundary explicit, as the computational
counterpart of `Family.SnapshotWaitFree`.

| Claim | Lean |
| --- | --- |
| The local computations Algorithms 1–3 perform, bundled with their specifications | `Object.LocalCompute` |
| It **adds no mathematics**: bounds are unique, so each field is forced | `LocalCompute.glb_eq`, `lub_eq` |
| It is **sufficient**: GCA lines 3, 4 and 6 factor through it | `LocalCompute.compatiblePart_eq`, `candidate_eq`, `output_eq` |
| It is **consistent** | `LocalCompute.classical` |
| Independence — and so `Object.Conflict` — is decidable for a finite-state object | `FiniteState.decidableIndependent`, `independentTest_iff` |
| It is **realizable** whenever independence is decidable: every local computation is an algorithm on finite representatives | `LocalCompute.ofDecidable` |
| …so for every finite-state object | `LocalCompute.finite` |
| …and decidable independence is exactly what it needs: two distinct operations commute iff their one-operation traces are compatible, so a compatibility test decides independence | `independent_iff_pairCompatible` |
| Trace order and trace equality are decidable | `decTracePrefix`, `decEqTrace` |
| For a free trace monoid, without choice | `LocalCompute.free` (`propext`, `Quot.sound` only) |
| …and it runs: `⊓`, `⊔`, compatibility, GCA lines 3–4 and 6 evaluate by `rfl` or `decide` | `Object.CounterWitness` (free), `SetWitness` (commuting operations, four states), `IncReadWitness` (infinitely many states) |
| Algorithm 2 with both local calculations computed is Algorithm 2 | `ForwardGCA.machine_eq_machineC` |
| …so the runs of Algorithms 1 and 3 over it are computed runs | `WeakUniversal.Over.mrun_machineC`, `HelpingUniversal.Over.mrun_machineC` |

`LocalCompute.ofDecidable` walks representatives: an operation *can start* a
schedule when every operation before its first occurrence commutes with it;
`t` extends `s` iff each operation of `s` in turn can start `t` and is removed
from it; `s ⊓ t` repeatedly takes an operation that can start both; `s ⊔ t`, when
it exists, is `s` followed by what is left of `t` once the operations of `s` are
removed, and `s, t` are compatible iff that list extends `t`.  Nothing in it is
`noncomputable`, and the kernel evaluates it; `Classical.choice` occurs only in
its correctness proofs, through core list lemmas, never in the functions.

Traces are finite, so what executability needs is a decision procedure for
independence of operations — a property of the object, quantified over every
state.  A finite state space supplies one by enumeration; an infinite one may
supply one by an argument (`IncReadWitness`); an arbitrary computable object
need not: two operations of an object over `ℕ` can be made to commute exactly
when a given program never halts.

Two things are worth stating plainly. First, the *algorithms never test the
conflict relation*: no constructor of `WeakUniversal.Step` or
`HelpingUniversal.Step` mentions `Object.Conflict`. Conflict is a specification
relation, used to state §3's progress conditions; an implementation does not
need to decide it. What the pseudocode does need is the trace monoid, which is
generated by swaps of *independent* operations, and that is where decidability
has to come from — hence `LocalCompute.ofDecidable` from a decision procedure for
independence, and `FiniteState.decidableIndependent` for the automaton
presentation `A = (Q, q₀, O, R, σ)` the manuscript itself uses.

Second, everything else the pseudocode evaluates locally is already computable
from `DecidableEq Op`: `traceCount` and `traceResponses` are `Quotient.lift`s of
`List.count` and of the response fold, `traceAppend` is concatenation, and the
maximum of a collect compares round numbers. The interface is exactly the
residue.

The companion obligation — that every execution of the concrete algorithms
projects into the admitted schedules — is discharged in §1.4.

---

## 5. §7: conflict forgetting (Algorithm 1) and conflict resolution (Algorithm 3)

### 5.1 `th:WeakUCresolve` — proved

> For every finite execution `α` of Algorithm 1 and every process `i`, there is
> a finite conflict-forgetting `i`-solo extension of `α`.

| Manuscript | Lean |
| --- | --- |
| GCA property 7, **Solo agreement** | `GCA.Protocol.SoloAgreement` (`GCASoloAgreement.lean`) |
| **Lemma `GCA_soloagg`** — Algorithm 2 satisfies it | `GCA.Protocol.soloAgreement`; all seven properties: `GCA.Protocol.specification_soloAgreement` |
| "eventually weakly `α`-conflict-free" | `Execution.EventuallyWeaklyConflictFree` |
| Definition *conflict-forgetting execution* | `Forward.ConflictForgetting` |
| **Theorem `th:WeakUCresolve`** | `Forward.weakUCresolve` (also `forward1_weakUCresolve`) |
| …the solo extension, first paragraph of the proof | `Forward.solo_extension` |
| …the rest of the proof, inside an extension `α''` | `WeakGCA.forgetting_completes` (`WeakConflictForgetting.lean`) |
| …"by Solo agreement, every process that returns from `GCA_{r*}` in any extension of `α'` returns `s`" | `WeakRun.solo_round_outputs`, `WeakRun.solo_checkpoint` |
| …the induction on `r̂ ≥ r*` | `WeakGCA.origin_after` |
| …invariant (I) | `WeakGCA.inputs_compatible_after` |

**The statement.** The theorem is proved in the manuscript's form over any GCA
implementation meeting the specification and Solo agreement
(`algorithm1Over_weakUCresolve`, §0.1), and inside one run over any GCA meeting
the interface (`WeakGCA.weakUCresolve`, §0): every `i`-solo continuation of a
finite execution of any run has a finite conflict-forgetting prefix.  Below is
its instance on the machine of §1.4, where GCA rounds run Algorithm 2 literally
(`Forward.weakUCresolve`).  A finite execution `α` is the first `N` steps of
`frun ch client sched`, for any rule for the collect order, any client and any
scheduler. An extension (`Forward.Extends`) takes the same first `N` steps — the
same process at each step, reaching the same configurations — and may invoke
different operations, and order its collects differently, afterwards. The `i`-solo extension is the
first `N'` steps of `soloSched sched N i`, which follows `sched` for `N` steps
and then schedules only `i`. `ConflictForgetting` quantifies over every
non-halting extension, reads "eventually weakly `α'`-conflict-free" on its §3
execution, and concludes that **some process that takes infinitely many steps**
completes each of its operations — which a correct process must, and which an
idle process cannot satisfy vacuously.

Three facts check the definitions against the manuscript:

* `Forward.stepsFrom_iff` — the extracted execution's operation time `t` is the
  machine's step `t + 1`, so the end of `α'` is operation time `N' - 1`: an
  instance takes an operation step from `N' - 1` on exactly when its process is
  scheduled, running it, at a machine step `≥ N'`. "Takes steps after `α'`" is
  read neither earlier nor later.
* `Execution.EventuallyConflictFree.weakly` — the weak notion is implied by §3's.
* `Forward.conflictForgetting_hypothesis_satisfiable` — the solo continuation is
  an extension meeting the definition's hypothesis, so it is not vacuous.

**The proof** follows the manuscript's.

1. *The solo extension.* `i` runs alone, invoking new operations when it has
   none. A process that keeps taking steps waits on arbitrarily high rounds
   (`WeakGCA.waiting_above`, from the measure `WeakUniversal.roundLevel`, which does
   not fall back between operations because a collect reads the process's own
   register), so `i` waits on a round `r*` above every round called in `α`,
   possibly after completing operations below it. It is the only participant of
   `r*` in the solo run, so it receives `(s, true)` with its command in `s`,
   publishes `(r*, s)` and returns; `α'` ends there.
2. *Solo agreement in the extension.* In `α''`, other processes may still call
   `r*` — a process mid-operation at the end of `α'` does not re-read `S`. Before
   `i` returned nobody else had called `r*`, so every protocol step of `r*` up to
   then is `i`'s, and Lemma `GCA_soloagg` makes every output of `r*` equal `s`
   (`WeakRun.solo_round_outputs`).
3. *The descent and invariant (I).* Every command of an output of a round
   `r̂ ≥ r*` is in `s` or was appended at Line 8 by its own process, proposing
   above `r*` — after `α'`, since no call above `r*` exists at its end
   (`WeakGCA.origin_after`). A residual command misses the common prefix `t ⊇ s`,
   so its instance took a step after `α'`; with responses frozen it is pending
   forever, so the hypothesis makes the residuals nonconflicting and the
   proposals compatible (`WeakGCA.inputs_compatible_after`).
4. *The contradiction* is `theorem:weakUCWCF`'s, reused as is
   (`WeakGCA.no_stall_of_compatible`).

### 5.2 `th:cr` — proved

> For every finite execution `α` of Algorithm 3 and every process `i`, there is
> a finite conflict-resolving `i`-solo extension of `α`.

| Manuscript | Lean |
| --- | --- |
| the invocation point of an operation, which may be placed at any point of its code | `HelpingUniversal.InvocationPoint`; in the code: `InvocationPoint.InCode` (`InvocationPoint.lean`) |
| "we consider an operation instance as invoked once its associated command is written into `M` (Line 5)" | the invocation point `InvocationPoint.announce` (Lines 1–4: `InvocationPoint.invoke`); `Forward.InvokedBy .announce` (on a run: `HelpingRun.AnnouncedBy`) |
| "eventually `α`-conflict-free", at an invocation point | `Forward.EventuallyConflictFreeAfter ip` (on a run: `HelpingRun.EventuallyNonconflictingAfter`, at Line 5) |
| Definition `def:wcr`, *conflict-resolving execution*, at an invocation point | `Forward.ConflictResolving ip` |
| **Theorem `th:cr`**, with the invocation point at Line 5 | `Forward.conflictResolution` (also `forward3_conflictResolution`): `ConflictResolving .announce` |
| …the solo extension: `i` commits `s'` at `r₁ > r₀`, writes `(r₁, s')` in `S` and completes; every operation instance invoked before the end of `α'` has its command in `ops(s')` | `Forward.solo_extension` |
| …the rest of the proof, inside an extension `α''` | `HelpingGCA.resolving_completes` (`ConflictResolution.lean`) |
| …"from what precedes, `Φ` is invoked after `α'`" | `HelpingGCA.completes_of_slot` |
| …invariant (II) | `HelpingGCA.output_contains_own_of` |
| …no commit above `r₂`: it is written into `S`, and every trace later read from `S` contains `cmd(Φ)` by (II) | `HelpingGCA.commit_published`, `HelpingGCA.completes_of_high_slot` |
| …invariant (I) | `HelpingGCA.inputs_compatible_res` |
| …the contradiction, through GCA Commitment | `HelpingGCA.exists_commit_of_compatible`, in `HelpingGCA.resolving_completes` |

**The statement** is made as for `th:WeakUCresolve` — over any GCA
implementation meeting the specification it is
`algorithm3Over_conflictResolution` (§0.1) — here for Algorithm 3 as the
machine of §1.4: a finite execution `α` is the first `N` steps of
`frun ch client sched`, an extension (`Forward.Extends`) takes the same first `N`
steps, and the `i`-solo extension is the first `N'` steps of
`soloSched sched N i`. `ConflictResolving` quantifies over every non-halting
extension and concludes, on the extension's §3 execution, that every correct
process completes each of its operations.

**The invocation point is stated openly.** The history an execution induces
records each operation's invocation at some point of its code, and it is
standard that this point may be placed anywhere in the code.  The manuscript's
proof uses the freedom: "In the induced history of `α`, we consider an operation
instance as invoked once its associated command is written into `M`".  The
choice decides which instances of an extension are invoked after `α'` and which
are concurrent, so it shapes the hypothesis, not only the proof.  The
formalization therefore makes it a parameter.  An `InvocationPoint`
(`InvocationPoint.lean`) says which configurations show an instance as having
reached the point.  It lies in the operation's code (`InvocationPoint.InCode`)
when an instance reaches it only once invoked and by the time it returns.  The
definitions of §7 that mention invocation — `InvokedBy`, `PendingAt`,
`EventuallyConflictFreeAfter`, `ConflictResolving` — take the invocation point
as an argument, and **`th:cr` is proved with it at Line 5, the write of the
command into `M`** (`InvocationPoint.announce`): `ConflictResolving .announce`.
Two points are named: Lines 1–4, where the command is created and where §3's
execution and the linearizability theorems record the invocation
(`InvocationPoint.invoke`), and Line 5; both lie in the code (`invoke_inCode`,
`announce_inCode`), and Line 5 comes after Lines 1–4
(`invokedBy_invoke_of_announce`).  At Line 5 the definitions are, verbatim,
those the theorem was first stated with.  Five facts check the definitions and
the theorem:

* `Forward.invokedAfter_iff`: at Line 5, an instance is invoked after `α` exactly
  when it takes no operation step within `α`. The write into `M` is an
  instance's first operation step — Lines 1–4 are local — and the boundary is
  the one `Forward.stepsFrom_iff` places for Algorithm 1.
* `Forward.eventuallyConflictFreeAfter_of_eventuallyConflictFree`: at every
  invocation point in the code, Line 5 included, the hypothesis is implied by
  §3's eventual conflict-freedom, so the theorem strengthens `lemma:UCV2isCF`'s
  guarantee, as the manuscript says.
* `Forward.eventuallyConflictFreeAfter_strict`: the converse fails. For any
  object with two conflicting operations, a process that writes its command
  into `M` and crashes keeps a run from being eventually conflict-free in §3's
  sense, while the run is eventually conflict-free after its first two steps in
  `th:cr`'s.
* `Forward.conflictResolving_hypothesis_satisfiable`: the solo continuation
  meets the hypothesis, so the definition always has an extension to speak
  about.
* `Forward.resolution_beyond_conflictFreedom`: the theorem is not subsumed by
  `lemma:UCV2isCF`. It is the manuscript's execution (a) of Figure
  `fig:resolving` on the machine: for any object with an operation `o'` that
  conflicts with some `o` but not with itself (a counter's increment and read),
  process `1` invokes `o`, writes it into `M` and crashes; after the
  conflict-resolving `0`-solo extension `th:cr` provides, processes `0` and `2`
  run concurrently for ever, invoking `o'`. The run is not eventually
  conflict-free, and no instance ever runs alone, so neither half of
  `lemma:UCV2isCF` gives anything; it is eventually `α'`-conflict-free, and
  `th:cr` completes every operation of every correct process.

**Scope.** As for `th:WeakUCresolve`, the theorem is proved over any GCA
meeting the interface (`HelpingGCA.conflictResolution`, §0), and
`Forward.conflictResolution` is its corollary for the machine, whose GCA rounds
run Algorithm 2.  The proof uses of the GCA objects only what the manuscript's
does — the six properties of §4.2 and "every correct participant returns";
unlike `th:WeakUCresolve`, it does not need Solo agreement.

**The proof** follows the manuscript's.

1. *The solo extension.* `i` runs alone, invoking new operations when it has
   none, until it waits on a round `r₁` above every round any process reached in
   `α` (`HelpingGCA.rounds_unbounded_from`, `reaches_waiting_always`). It is that
   round's only participant in the solo run, so by Commitment and Validity it
   receives `(s', true)` (`HelpingGCA.solo_round_commits`), writes `(r₁, s')` in `S`, finds it at its final
   collect (`solo_check_collect`) and returns; `α'` ends there. Its collect of
   `M` for `r₁` started after `α`, while `M[j] = M₀[j]` for `j ≠ i`
   (`announcements_const_of_solo`, `helped_gathering`), so every command invoked
   by the end of `α'` is in `s'`: a completed one lies in a trace committed at a
   round at most `r₁` (`HelpingUniversal.returnsCalled`), which prefixes `s'`.
2. *Carrying `α'` to an extension.* The facts the rest needs are about the
   states of `α'`, so they carry over; `i`'s commit is re-read from its receive
   step in the extension's own GCA family (`HelpingRun.committed_of_publishing`).
3. *`Φ` is invoked after `α'`.* A command of a forever-pending operation of a
   correct process that was invoked by the end of `α'` is in `s'`, and the
   process's next final `S` collect adopts a committed trace extending it
   (`HelpingGCA.completes_of_slot`).
4. *Invariant (II)*, past the time `τ'` at which `cmd(Φ)` is in `M` and the
   rounds reached by then. A residual command misses the common prefix `t`,
   which contains `s'` (`lemma:prefix-rounds`), so it was invoked after `α'`;
   every command of a GCA input was written into `M` (`HelpingGCA.input_announced`)
   and is written before it is answered (`announced_before_answer`), so it is
   pending at a common time with `Φ` (`pendingAfter_witness`), and the hypothesis
   makes it independent of `cmd(Φ)`.
5. *Invariant (I).* A commit above the bound is written into `S`, and every
   trace later read from `S` is committed above the bound, so contains `cmd(Φ)`
   by (II) and completes `Φ`: there is no such commit.  So residual commands
   never complete; being invoked after `α'` and pending for ever, they do not
   conflict.
6. *The contradiction.* `Φ`'s process waits on a round above the bound, whose
   proposals are compatible by (I), so by Commitment some process commits
   there — excluded by step 5.

The proof reuses the lemmas of `lemma:UCV2isCF`'s proof in general form:
`output_contains_own_of` asks for independence only from residual commands, and
`inputs_compatible_res` takes an arbitrary nonconflicting set;
`output_contains_own` and `inputs_compatible_at` are their special cases, and
`commit_high_completes` factors through `commit_published` and
`completes_of_slot`, itself `completes_of_high_slot` with `lemma:prefix-rounds`.

### 5.3 `lemma:prefix-rounds`, for both constructions

The manuscript states the lemma for "an execution of Algorithm 1 or Algorithm
3", and the Lean development proves it once for both:
`GCA.RoundExecution.commit_below_later_output` proves it for any sequence of GCA
histories in which every proposal to round `r' + 1` extends an output of round
`r'` (base case Adoption, step Common Prefix, as in the manuscript), and each
construction derives that predecessor property from its own transitions — Lines
4 and 7–8 of Algorithm 1, Lines 6 and 10–11 of Algorithm 3 — as the `calls` field
of its invariant. The instances are `WeakUniversal.committed_prefix` and
`HelpingUniversal.committed_prefix`; `PrefixRounds.lean` states the lemma in the
manuscript's form for executions of either construction, with coverage derived
(`GlobalSchedule.Weak.prefix_rounds`, `GlobalSchedule.Helping.prefix_rounds`).

---

## 6. Assumptions, and what is left

Nothing within the scope of this document is open.

**Assumed by design.** The classical local calculations, in the manuscript's
own convention that a local computation is one step — computed rather than
assumed for every object whose independence relation is decidable, every
finite-state object among them (§4).  And, per the author's
scope clarification, the snapshot objects Algorithm 2 runs on (main.tex cites
Afek et al., `AADGMS93`).  What that leaves unproved is exactly one fact from the
literature, needed only for the claim that the constructions are *read-write*
implementations, and used by no Lean theorem:

> Algorithm 2, with each atomic snapshot operation (update, scan) replaced by a
> wait-free linearizable implementation from atomic read/write registers, is a
> `GCAMachine` `G` with `G.IsGCA` and `G.SoloAgreement`.

Everything around it is proved.  The universal-construction theorems take
exactly those two properties as their hypotheses on `G` (`algorithm1Over_*`,
`algorithm3Over_*`, §0.1; `IsGCA` alone except for `th:WeakUCresolve`).  Each
step of Algorithms 1 and 3 over `G` is a local computation with at most one
access to a register `S[j]` or `M[j]`, or a step of `G` or a return from it
(`Over.mstep`; §1.4 for the machines over Algorithm 2).  And Algorithm 2
over *atomic* snapshot objects is proved to have both properties
(`ForwardGCA.machine_isGCA`, `machine_soloAgreement`).  So a proof of the fact —
a `GCAMachine` built from registers with the two properties — would plug into
those theorems unchanged.

**Optional strengthenings.**
* A separate open-environment model in the style of Herlihy and Wing, with a
  theorem identifying its histories with the machines'.  §1.4 gives the
  identification, event for event: an invocation is the local `invoke` step,
  placed by the scheduler.
* Expressing the forward machines in `SharedMemory.lean`'s generic register
  machine. That machine has registers only, so snapshot objects and client
  inputs would have to be added to it; the forward machines follow its
  discipline already (§1.4).

---

## 7. Validation

```sh
lake build
lake env lean CFLeanProof/KernelAudit.lean
lake env lean CFLeanProof/Audit.lean
```

`KernelAudit.lean` is the exhaustive failing check: every module under
`CFLeanProof/` is imported by `CFLeanProof.lean`, and every project declaration
uses only the standard axioms. `Audit.lean` prints the axioms of each result
stated in `Paper.lean`. Neither checks a theorem's statement against the
manuscript; this document does that.

### Proof paths

* The GCA interface: `GlobalSchedule` (runs over any GCA, `GCAInterface`,
  `SoloAgreement`, `WeakGCA`, `HelpingGCA`) → the liveness chains below, all
  over `WeakGCA` / `HelpingGCA` → `Algorithm2Interface` (the manuscript's
  specification gives the interface; Algorithm 2 meets it; `toGCA`) →
  `Algorithm1`, `Algorithm3` (`algorithm1AnyGCA`, `algorithm3AnyGCA`,
  `algorithm1_anyGCA`, `algorithm3_anyGCA`) → `Algorithm1WeakConflictFree`,
  `Algorithm3ConflictFree`, `ForwardUniversal`, `ForwardHelping`.

* GCA as an implementation: `GCAMachine` (runs, histories, `IsGCA`,
  `SoloAgreement`, finite executions as runs) → `GCAMachineAlgorithm2`
  (Algorithm 2 meets both) → `Algorithm1OverGCA`, `Algorithm3OverGCA` (the
  constructions over any machine, the interface for every run, and §7 in the
  manuscript's form).

* Liveness, Algorithm 1: `UniversalProgress` → `UniversalLiveness` →
  `UniversalImplementation` → `Algorithm1` → `Algorithm1WeakConflictFree`.
* Liveness, Algorithm 3: `HelpingProgress` → `HelpingConflictFreedom` →
  `HelpingConflictFree` → `HelpingInvariantTwo` → `Algorithm3ConflictFree`.
* Refinement: `ForwardGCA` (Algorithm 2 run forward, and `output_agrees`) →
  `ForwardUniversal` (Algorithm 1) and `ForwardHelping` (Algorithm 3).
* §7, `th:WeakUCresolve`: `GCASoloAgreement` (property 7 and Lemma
  `GCA_soloagg`) → `WeakConflictForgetting` (the argument inside one run) →
  `WeakUCResolve` (the solo extension, the §3 definitions and the theorem).
* §7, `th:cr`: `HelpingInvariantTwo` (invariants (I) and (II) of
  `lemma:UCV2isCF`) → `ConflictResolution` (the argument inside one run, above a
  published checkpoint) → `InvocationPoint` (invocation points; Lines 1–4 and
  Line 5 lie in the code) → `UCResolve` (the solo extension, the definitions at
  any invocation point, and the theorem at Line 5).
* `lemma:prefix-rounds`: `UniversalRounds` (the generic lemma) →
  `WeakUniversal`, `HelpingUniversal` (one instance per construction) →
  `PrefixRounds` (for executions of either).
* Model/computation boundary: `EffectiveInterface` → `FreeTraceCompute`,
  `DecidableTraceCompute` → `MachineCompute` (the machines as programs); the
  snapshot assumption's models: `SnapshotStutter`.
* Non-vacuity of liveness: `FairnessClock` (justifying `Fair`), then the solo
  runs in `ProgressWitness` and `HelpingWitness`, then the contended runs —
  `ContentionWitness` (Algorithm 3, one stalled process),
  `WeakContentionWitness` (Algorithm 1, one stalled process) and
  `SharedRoundWitness` (Algorithm 3, two callers per GCA round); and the adopt
  branch, computed: `AdoptWitness`.
* Safety: `GCAProtocol` → `GCACausality` → `UniversalProvenance` →
  `CausalLinearization` (where the GCA causal contract is named and met);
  events via `EventHistory` → `LedgerEvents` → `UniversalEventLinearization`,
  and for the whole run `InfiniteHistory` → `InfiniteEventLinearization`, with
  `LinearizationWitness` for content.
* GCA interface: `CausalLinearization` → `WeakCoveredLinearization`
  (Algorithm 1 needs no temporal contract) and `NonCausalWitness` (Algorithm 3
  does) → `GCAInterface`.
* Operation extraction: `InvocationLedger` → `InvocationTiming` →
  `SharedScheduler` → `GlobalSchedule`.
