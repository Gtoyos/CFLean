import CFLeanProof.Algorithm1OverGCA
import CFLeanProof.Algorithm3OverGCA
import CFLeanProof.ForwardUniversal
import CFLeanProof.ForwardHelping
import CFLeanProof.InfiniteEventLinearization
import CFLeanProof.PrefixRounds
import CFLeanProof.TraceOccurrences

/-!
# The paper's results

Every numbered result of *Conflict-Freedom as a Progress Condition* (Kuznetsov,
Sutra, Toyos-Marfurt; extended version, `main.tex`), stated in the paper's terms
and proved from the rest of the development. To check the formalization against
the paper, read this file and the definitions it uses; each definition is
restated here next to the paper's own wording.

* §3: commutation and conflicts (`commuteAt_iff`, `conflict_iff`); correct
  processes, eventual step-contention freedom and eventual conflict freedom
  (`correct_iff`, `solo_iff`, `eventuallyConflictFree_iff`); the progress
  conditions (`waitFree_iff`, `lockFree_iff`, `obstructionFree_iff`,
  Definitions 3.1 and 3.2: `definition3_1`, `definition3_2`); Propositions 3.3
  and 3.4: `proposition3_3`, `proposition3_4_full`, `proposition3_4_empty`.
* §4.1: schedule equivalence (`scheduleEquiv_iff`, `traceEq_iff_scheduleEquiv`);
  Lemmas 4.1 and 4.2: `lemma4_1`, `lemma4_2`.
* §4.2: the six GCA properties (`gca_validity` … `gca_weakAgreement`), the GCA
  specification of an implementation (`isGCA_iff`), and Solo agreement
  (`soloAgreement_iff`).
* §4.3: Theorems 4.3 and 4.4: `theorem4_3`, `theorem4_4`.
* §5: Theorem 5.1: `theorem5_1`.
* §6: Lemmas 6.1 and 6.2: `lemma6_1`, `lemma6_2`.
* §7: Definitions 7.1 and 7.3, conflict-resolving and conflict-forgetting
  executions: `definition7_1`, `definition7_3`; Theorems 7.2 and 7.4: `theorem7_2`,
  `theorem7_4`.
* Appendix A: Lemma A.1 (`lemmaA_1_alg1`, `lemmaA_1_alg3`) and Lemmas A.2 to
  A.8 (`lemmaA_2` … `lemmaA_8`).
* Algorithm 2 is a GCA implementation: `algorithm2_isGCA`,
  `algorithm2_soloAgreement`; and the algorithms as machines:
  `theorem4_4_machine`, `lemma6_2_machine`.

The results about Algorithms 1 and 3 are stated, as in the paper, over any GCA
objects meeting the specification of §4.2: an arbitrary implementation `G`, of
which the theorems assume `G.IsGCA` and, for Theorem 7.4, `G.SoloAgreement`.
Algorithm 2 is one (`algorithm2_isGCA`, `algorithm2_soloAgreement`).
-/

namespace ConflictFreedom.Paper
open Object

variable {State Op Response : Type}

/-! ## Section 3: conflict-freedom -/

section Section3
variable (obj : Object State Op Response)

/-- "Operations `a, b ∈ O` commute in `q` if there exist responses `r_a, r_b ∈ R`
and states `q₁, q₂, q' ∈ Q` such that `σ(a,q) = (r_a,q₁)`, `σ(b,q₁) = (r_b,q')`,
`σ(b,q) = (r_b,q₂)` and `σ(a,q₂) = (r_a,q')`." -/
theorem commuteAt_iff (a b : Op) (q : State) :
    obj.CommuteAt a b q ↔
      ∃ (ra rb : Response) (q₁ q₂ q' : State),
        obj.step a q = (ra, q₁) ∧ obj.step b q₁ = (rb, q') ∧
        obj.step b q = (rb, q₂) ∧ obj.step a q₂ = (ra, q') := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨(obj.step a q).1, (obj.step b q).1, (obj.step a q).2, (obj.step b q).2,
      (obj.step b (obj.step a q).2).2, rfl, ?_, rfl, ?_⟩
    · exact Prod.ext h₂ rfl
    · exact Prod.ext h₁.symm h₃.symm
  · rintro ⟨ra, rb, q₁, q₂, q', ha, hb₁, hb, ha₂⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hb, ha, ha₂]
    · rw [ha, hb₁, hb]
    · rw [ha, hb₁, hb, ha₂]

/-- "Operations `a, b ∈ O` are conflicting, written `a ≍ b`, if there exists a
state `q ∈ Q` in which `a` and `b` do not commute." -/
theorem conflict_iff (a b : Op) : obj.Conflict a b ↔ ∃ q, ¬ obj.CommuteAt a b q :=
  Iff.rfl

variable {n : Nat} {Op' : Type} (e : Execution n Op')

/-- "In an infinite execution, a process is correct if it either takes infinitely
many steps or has no pending operation." -/
theorem correct_iff (p : Fin n) :
    e.Correct p ↔ e.InfiniteSteps p ∨ ∀ i, e.owner i = p → e.Completes i :=
  Iff.rfl

/-- "An operation instance `Φ` is eventually step-contention free in an execution
`α` if either `Φ` completes in `α`, or there exists a suffix of `α` in which only
`Φ` takes steps." -/
theorem solo_iff (i : e.Instance) :
    e.Solo i ↔ e.Completes i ∨ ∃ N, ∀ t j, N ≤ t → e.actor t = some j → j = i :=
  Iff.rfl

/-- "An infinite execution `α` is eventually conflict-free if there exists a
suffix of `α` in which no two concurrent operation instances `Φ = (o,i)` and
`Φ' = (o',j)` satisfy `o ≍ o'`." -/
theorem eventuallyConflictFree_iff (conflict : Op' → Op' → Prop) :
    e.EventuallyConflictFree conflict ↔
      ∃ N, ∀ t, N ≤ t → ∀ i j, i ≠ j → e.Pending i t → e.Pending j t →
        ¬ conflict (e.operation i) (e.operation j) :=
  Iff.rfl

variable (A : Implementation n Op') (conflict : Op' → Op' → Prop)

/-- "An implementation is wait-free if in each of its infinite executions, every
correct process that takes infinitely many steps completes each of its
operations." -/
theorem waitFree_iff :
    WaitFree A ↔ ∀ e, A e → ∀ i, e.InfiniteSteps (e.owner i) → e.Completes i :=
  waitFree_iff_infiniteSteps

/-- "An implementation is lock-free if in each of its infinite executions, at
least one correct process that takes infinitely many steps completes each of its
operations." -/
theorem lockFree_iff :
    LockFree A ↔ ∀ e, A e → ∃ p, e.InfiniteSteps p ∧ ∀ i, e.owner i = p → e.Completes i :=
  Iff.rfl

/-- "An implementation is obstruction-free if in each of its infinite executions,
any operation instance `Φ` invoked by a correct process completes in `α` whenever
`Φ` is eventually step-contention free." -/
theorem obstructionFree_iff :
    ObstructionFree A ↔ ∀ e, A e → ∀ i, e.Correct (e.owner i) → e.Solo i → e.Completes i :=
  Iff.rfl

/-- **Definition 3.1** (conflict-freedom). "An implementation is conflict-free if, in
every infinite execution, every operation invoked by a correct process completes
whenever the operation is eventually step-contention-free or the execution is
eventually conflict-free." -/
theorem definition3_1 :
    ConflictFree A conflict ↔ ∀ e, A e → ∀ i, e.Correct (e.owner i) →
      (e.Solo i ∨ e.EventuallyConflictFree conflict) → e.Completes i :=
  Iff.rfl

/-- **Definition 3.2** (weak conflict-freedom). "An implementation is weakly
conflict-free if, (1) in every infinite execution, every operation invoked by a
correct process completes whenever it is eventually step-contention-free, and (2)
if the execution is eventually conflict-free, then some correct process that
takes infinitely many steps completes all of its operations." -/
theorem definition3_2 :
    WeakConflictFree A conflict ↔
      ObstructionFree A ∧ ∀ e, A e → e.EventuallyConflictFree conflict →
        ∃ p, e.InfiniteSteps p ∧ ∀ i, e.owner i = p → e.Completes i :=
  Iff.rfl

/-- **Proposition 3.3** (`prop:progress-hierarchy`). "wait-freedom ⟹
conflict-freedom ⟹ weak conflict-freedom ⟹ obstruction-freedom." -/
theorem proposition3_3 :
    (WaitFree A → ConflictFree A conflict) ∧
    (ConflictFree A conflict → WeakConflictFree A conflict) ∧
    (WeakConflictFree A conflict → ObstructionFree A) :=
  progressHierarchy

/-- **Proposition 3.4** (`prop:cf-degenerate`), first item. "If `≍ = O × O`, then
conflict-freedom and weak conflict-freedom are equivalent to
obstruction-freedom." -/
theorem proposition3_4_full :
    (ConflictFree A (fun _ _ => True) ↔ ObstructionFree A) ∧
    (WeakConflictFree A (fun _ _ => True) ↔ ObstructionFree A) :=
  ⟨universal_conflictFree_iff_obstructionFree, universal_weakConflictFree_iff_obstructionFree⟩

/-- **Proposition 3.4**, second item. "If `≍ = ∅`, then conflict-freedom is
equivalent to wait-freedom, and weak conflict-freedom is equivalent to
lock-freedom." -/
theorem proposition3_4_empty :
    (ConflictFree A (fun _ _ => False) ↔ WaitFree A) ∧
    (WeakConflictFree A (fun _ _ => False) ↔ LockFree A) :=
  ⟨empty_conflictFree_iff_waitFree, empty_weakConflictFree_iff_lockFree⟩

end Section3

/-! ## Section 4.1: schedules and traces -/

section Section41
variable (obj : Object State Op Response) [DecidableEq Op]

/-- "Two schedules `s, s' ∈ O*` are equivalent, `s ∼ s'`, if (i)
`ops(s) = ops(s')` and (ii) for every pair of occurrences `a⁽ⁱ⁾, b⁽ʲ⁾` in `s`, if
`a ≍ b` and `a⁽ⁱ⁾ ≺ₛ b⁽ʲ⁾`, then `a⁽ⁱ⁾ ≺ₛ' b⁽ʲ⁾`." -/
theorem scheduleEquiv_iff (s t : List Op) :
    obj.ScheduleEquiv s t ↔
      (∀ a, s.count a = t.count a) ∧
      ∀ a b i j, obj.Conflict a b → i < s.count a → j < s.count b →
        SchedulePrecedes s a i b j → SchedulePrecedes t a i b j :=
  Iff.rfl

/-- Traces, the classes `O*/∼`, are the quotient `Object.Trace` used throughout:
its relation `TraceEq`, generated by swapping adjacent commuting operations, is
the paper's `∼`. -/
theorem traceEq_iff_scheduleEquiv (s t : List Op) :
    obj.TraceEq s t ↔ obj.ScheduleEquiv s t :=
  obj.traceEq_iff_scheduleEquiv s t

/-- **Lemma 4.1** (`lemma:ret-trace-eq`). "Let `s, t ∈ O*` be two schedules such
that `s ∼ t`. Then for any occurrence of an operation `o⁽ⁱ⁾` in `s`,
`ret*(o⁽ⁱ⁾, s) = ret*(o⁽ⁱ⁾, t)`." Here `responses o s q₀` lists `ret*(o⁽ⁱ⁾, s)`
for `i = 1, 2, …`. -/
theorem lemma4_1 {s t : List Op} (h : obj.ScheduleEquiv s t) (o : Op) :
    obj.responses o s obj.initial = obj.responses o t obj.initial :=
  (obj.traceEq_semantics ((obj.traceEq_iff_scheduleEquiv s t).mpr h) obj.initial).2 o

/-- **Lemma 4.2** (`lemma:ret-trace-prefix`). "Let `s, t ∈ O*/∼`, if `s ≤ t` then
for every occurrence `o⁽ⁱ⁾` in `s`, `ret*(o⁽ⁱ⁾, s) = ret*(o⁽ⁱ⁾, t)`." -/
theorem lemma4_2 {s t : obj.Trace} (h : obj.TracePrefix s t) (o : Op) (i : Nat)
    (hi : i < (obj.traceResponses o obj.initial s).length) :
    obj.traceReturn o i s = obj.traceReturn o i t :=
  obj.traceReturn_prefix h o i hi

end Section41

/-! ## Section 4.2: Generalized Commit-Adopt

A GCA history (`GCA.History`) records, for each participant, its input `s_i` and,
once its call has returned, its output `(t_i, c_i)`. -/

section Section42
variable {obj : Object State Op Response} {P : Type} (h : GCA.History obj P)

/-- "**Validity.** Output traces contain only input operations.
`∀ i ∈ P_r, ops(t_i) ⊆ ⋃_{j∈P} ops(s_j)`." -/
theorem gca_validity [DecidableEq Op] :
    h.Validity ↔ ∀ p t c, h.output p = some (t, c) → obj.SubsetUnion (obj.ops t) h.Inputs :=
  Iff.rfl

/-- "**Adoption.** A committed trace is extended by every output trace.
`∀ i ∈ P_r, c_i = True ⟹ ∀ j ∈ P_r, t_i ≤ t_j`." -/
theorem gca_adoption :
    h.Adoption ↔ ∀ p t, h.output p = some (t, true) →
      ∀ q u c, h.output q = some (u, c) → obj.TracePrefix t u :=
  Iff.rfl

/-- "**Commitment.** If all input traces are compatible, then some process
commits an extension of its input trace.
`comp(⋃_{i∈P}{s_i}) ∧ (P = P_r ≠ ∅) ⟹ ∃ j ∈ P_r, (s_j ≤ t_j) ∧ (c_j = True)`." -/
theorem gca_commitment :
    h.Commitment ↔ ((∃ s, h.Inputs s) → obj.Compatible h.Inputs → h.AllReturned →
      ∃ p s t, h.input p = some s ∧ h.output p = some (t, true) ∧ obj.TracePrefix s t) :=
  Iff.rfl

/-- "**Convergence.** Output traces are mutually compatible.
`comp(⋃_{i∈P_r}{t_i})`." -/
theorem gca_convergence : h.Convergence ↔ obj.Compatible h.Outputs :=
  Iff.rfl

/-- "**Common Prefix.** Output traces preserve the common prefix of the input
traces. `∀ i ∈ P_r, ⊓_{j∈P} s_j ≤ t_i`." Stated for every common lower bound
of the inputs, which is equivalent. -/
theorem gca_commonPrefix :
    h.CommonPrefix ↔ ∀ l, (∀ s, h.Inputs s → obj.TracePrefix l s) →
      ∀ t, h.Outputs t → obj.TracePrefix l t :=
  Iff.rfl

/-- "**Weak Agreement.** If all input traces are equal, then no process adopts.
`∀ i, j ∈ P, s_i = s_j ⟹ ∀ i ∈ P_r : c_i = True`." -/
theorem gca_weakAgreement :
    h.WeakAgreement ↔ ((∀ s t, h.Inputs s → h.Inputs t → s = t) →
      ∀ p t c, h.output p = some (t, c) → c = true) :=
  Iff.rfl

variable {n : Nat} {O : Object State Op Response} (G : GCAMachine O n)

/-- "The abstraction guarantees that every correct participant eventually
returns. […] The following properties hold for every execution." A GCA
implementation `G` meets the specification when, in every run, every round's
history has the six properties, and a participant that keeps taking steps does
not stay inside its call. -/
theorem isGCA_iff [DecidableEq Op] :
    G.IsGCA ↔
      (∀ act wr wv gs, G.Driven act wr wv gs → ∀ r, (G.history act wr wv gs r).Specification) ∧
      (∀ act wr wv gs, G.Driven act wr wv gs → ∀ p r N,
        (∀ t, N ≤ t → wr t p = some r) → ¬ ∀ M, ∃ t, M ≤ t ∧ act t = some p) :=
  ⟨fun h => ⟨h.spec, h.returns⟩, fun h => ⟨h.1, h.2⟩⟩

/-- "**Solo Agreement.** If a process returns before any other process
participates, every output trace equals its own. `P' = P'_r = {j} ⟹ ∀ i ∈ P_r,
t_i = t_j`, where `P'` and `P'_r` are the sets of participants and returning
participants in some prefix of the execution." The prefix is the run up to `T`. -/
theorem soloAgreement_iff :
    G.SoloAgreement ↔
      ∀ act wr wv gs, G.Driven act wr wv gs → ∀ T R j o,
        (∀ t q, t ≤ T → wr t q = some R → q = j) →
        (∃ t, t < T ∧ act t = some j ∧ wr t j = some R ∧ G.output (gs t) j R (wv t j) = some o) →
        ∀ q y c, (G.history act wr wv gs R).output q = some (y, c) → y = o.1 :=
  Iff.rfl

end Section42

/-! ## Section 4.3: the weakly conflict-free universal construction

`algorithm1Over obj G` is Algorithm 1 for the object `obj`, over the GCA
implementation `G`: the executions of its non-halting runs, for every client,
every scheduler, and every order of the collect of Line 4. -/

section Section43
variable (obj : Object State Op Response) [DecidableEq Op] {n : Nat}
  (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n)
open WeakUniversal.Over

/-- Algorithm 1 over `G`, as an implementation. -/
theorem algorithm1Over_iff (e : Execution n Op) :
    algorithm1Over obj G e ↔
      ∃ (ch : WeakUniversal.Forward.Choices (n := n) obj) (client : Fin n → Nat → Op)
        (sched : Nat → Option (Fin n)) (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome),
        e = execution obj G ch client sched hlive :=
  Iff.rfl

/-- **Theorem 4.3** (`theorem:weakUCLin`). "Algorithm 1 implements a linearizable
universal construction." For every run over any GCA implementation, halting or
not, its whole invocation/response history — the operations the run invoked,
answered with the responses the run returned — is well formed and linearizable. -/
theorem theorem4_3 (hG : G.IsGCA) (ch : WeakUniversal.Forward.Choices (n := n) obj)
    (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) :
    ∃ resp : WeakUniversal.Cmd n Op → Response,
      (∀ k a v, ((weakRun obj G ch client sched).run.history obj).returned k a v → v = resp a) ∧
      (∀ a, ((((weakRun obj G ch client sched).run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, ((weakRun obj G ch client sched).run.history obj).invoked N a)) ∧
      (∀ a v, ((((weakRun obj G ch client sched).run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, ((weakRun obj G ch client sched).run.history obj).returned N a v)) ∧
      (((weakRun obj G ch client sched).run.ledgerRun obj).events resp).WellFormed
        Command.process ∧
      (WeakUniversal.Tagged obj).InfEventLinearizable Command.process
        (((weakRun obj G ch client sched).run.ledgerRun obj).events resp) :=
  infinite_event_linearization obj G ch client sched hG

/-- **Theorem 4.4** (`theorem:weakUCWCF`). "Algorithm 1 ensures weak
conflict-freedom." -/
theorem theorem4_4 (hG : G.IsGCA) : WeakConflictFree (algorithm1Over obj G) obj.Conflict :=
  algorithm1Over_weakConflictFree obj G hG

end Section43

/-! ## Section 5: the GCA algorithm

`GCA.Protocol obj P` is one GCA instance run by Algorithm 2 over atomic snapshot
objects `A` and `B`: its participants and inputs, the process scheduled at each
tick, and whether that tick completes the caller's pending snapshot operation.
`SnapshotWaitFree` says the snapshot objects are wait-free. -/

section Section5
variable {obj : Object State Op Response} [DecidableEq Op] {P : Type} [DecidableEq P]
  (e : GCA.Protocol obj P)

/-- **Theorem 5.1** (`theorem:GCA_works`). "Algorithm 2 is an implementation of
Generalized Commit-Adopt": its history has the six properties, and every
participant that keeps taking steps returns. -/
theorem theorem5_1 (hw : e.SnapshotWaitFree) :
    e.history.Specification ∧
      ∀ p, e.InfiniteSteps p → ∃ t c, e.history.output p = some (t, c) :=
  e.correctness hw

/-- **Lemma A.2** (`lemma:GCA_adoption`), Adoption. -/
theorem lemmaA_2 : e.history.Adoption := e.specification.adoption

/-- **Lemma A.3** (`lemma:GCA_commit_input`), Commitment. -/
theorem lemmaA_3 : e.history.Commitment := e.specification.commitment

/-- **Lemma A.4**, Convergence. -/
theorem lemmaA_4 : e.history.Convergence := e.specification.convergence

/-- **Lemma A.5** (`lemma:GCA_common_prefix`), Common Prefix. -/
theorem lemmaA_5 : e.history.CommonPrefix := e.specification.commonPrefix

/-- **Lemma A.6** (`lemma:GCA_weak_agreement`), Weak Agreement. -/
theorem lemmaA_6 : e.history.WeakAgreement := e.specification.weakAgreement

/-- **Lemma A.7** (`lemma:GCA_validity`), Validity. -/
theorem lemmaA_7 : e.history.Validity := e.specification.validity

/-- **Lemma A.8** (`lemma:GCA_soloagg`). "If a process returns before any other
process participates, every output trace equals its own." -/
theorem lemmaA_8 : e.SoloAgreement := e.soloAgreement

variable (O : Object State Op Response) (n : Nat)

/-- Algorithm 2, run for every round over atomic snapshot objects
(`ForwardGCA.machine`), meets the GCA specification in every run. -/
theorem algorithm2_isGCA : (ForwardGCA.machine O n).IsGCA :=
  ForwardGCA.machine_isGCA

/-- …and Solo agreement, in every run. -/
theorem algorithm2_soloAgreement : (ForwardGCA.machine O n).SoloAgreement :=
  ForwardGCA.machine_soloAgreement

end Section5

/-! ## Section 6: the conflict-free universal construction

`algorithm3Over obj G` is Algorithm 3 over the GCA implementation `G`: the
executions of its non-halting runs, for every client, every scheduler, every
order of the collects of `S` and `M`, and every order of `trace(M_i)`. -/

section Section6
variable (obj : Object State Op Response) [DecidableEq Op] {n : Nat}
  (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n)
open HelpingUniversal.Over

/-- Algorithm 3 over `G`, as an implementation. -/
theorem algorithm3Over_iff (e : Execution n Op) :
    algorithm3Over obj G e ↔
      ∃ (ch : HelpingUniversal.Forward.Choices (n := n) obj) (client : Fin n → Nat → Op)
        (sched : Nat → Option (Fin n)) (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome),
        e = execution obj G ch client sched hlive :=
  Iff.rfl

/-- **Lemma 6.1.** "Algorithm 3 implements a linearizable universal
construction." -/
theorem lemma6_1 (hG : G.IsGCA) (ch : HelpingUniversal.Forward.Choices (n := n) obj)
    (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) :
    ∃ resp : WeakUniversal.Cmd n Op → Response,
      (∀ k a v, ((helpingRun obj G ch client sched).run.history obj).returned k a v →
        v = resp a) ∧
      (∀ a, ((((helpingRun obj G ch client sched).run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, ((helpingRun obj G ch client sched).run.history obj).invoked N a)) ∧
      (∀ a v, ((((helpingRun obj G ch client sched).run.ledgerRun obj).events resp).Responded
          a v ↔ ∃ N, ((helpingRun obj G ch client sched).run.history obj).returned N a v)) ∧
      (((helpingRun obj G ch client sched).run.ledgerRun obj).events resp).WellFormed
        Command.process ∧
      (WeakUniversal.Tagged obj).InfEventLinearizable Command.process
        (((helpingRun obj G ch client sched).run.ledgerRun obj).events resp) :=
  infinite_event_linearization obj G ch client sched hG

/-- **Lemma 6.2** (`lemma:UCV2isCF`). "Algorithm 3 is conflict-free." -/
theorem lemma6_2 (hG : G.IsGCA) : ConflictFree (algorithm3Over obj G) obj.Conflict :=
  algorithm3Over_conflictFree obj G hG

end Section6

/-! ## Section 7: resolving conflicts in step-contention-free runs

A finite execution `α` is the first `N` steps of a run `mrun G ch client sched`;
an extension of it (`Extends`) is a run over the same `G` that takes the same
first `N` steps, after which the client and the choices may differ. The `i`-solo
extension follows `α` and then schedules only `i` (`soloSched sched N i`). -/

section Section7
variable (obj : Object State Op Response) [DecidableEq Op] {n : Nat}
  (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n)

omit [DecidableEq Op] in
/-- "We say that `α'` is eventually weakly `α`-conflict-free if it has a suffix in
which no two concurrent operation instances `Φ = (o,i)` and `Φ' = (o',j)` that
take steps after `α` satisfy `o ≍ o'`." Here `α` ends at operation time `B`. -/
theorem eventuallyWeaklyConflictFree_iff (e : Execution n Op) (B : Nat) :
    e.EventuallyWeaklyConflictFree obj.Conflict B ↔
      ∃ N, ∀ t, N ≤ t → ∀ i j, i ≠ j → e.Pending i t → e.Pending j t →
        (∃ u, B ≤ u ∧ e.actor u = some i) → (∃ u, B ≤ u ∧ e.actor u = some j) →
        ¬ obj.Conflict (e.operation i) (e.operation j) :=
  Iff.rfl

/-- **Definition 7.3** (conflict-forgetting execution). "A finite execution `α` of `A`
is conflict-forgetting if in every eventually weakly `α`-conflict-free infinite
extension of `α`, some correct process that takes infinitely many steps completes
each of its operations." -/
theorem definition7_3 (ch : WeakUniversal.Forward.Choices (n := n) obj)
    (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) :
    WeakUniversal.Over.ConflictForgetting obj G ch client sched N ↔
      ∀ (ch' : WeakUniversal.Forward.Choices (n := n) obj) (client' : Fin n → Nat → Op)
        (sched' : Nat → Option (Fin n)) (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched' t).isSome),
        WeakUniversal.Over.Extends obj G ch' client' sched' ch client sched N →
        (WeakUniversal.Over.execution obj G ch' client' sched' hlive).EventuallyWeaklyConflictFree
          obj.Conflict (N - 1) →
        ∃ p, (WeakUniversal.Over.execution obj G ch' client' sched' hlive).InfiniteSteps p ∧
          ∀ i, (WeakUniversal.Over.execution obj G ch' client' sched' hlive).owner i = p →
            (WeakUniversal.Over.execution obj G ch' client' sched' hlive).Completes i :=
  Iff.rfl

/-- **Definition 7.1** (`def:wcr`, conflict-resolving execution). "A finite
execution `α` of `A` is conflict-resolving if in every eventually
`α`-conflict-free infinite extension of `α`, every correct process completes each
of its operations." "Invoked" is read at an invocation point `ip`; Theorem 7.2
places it where the paper does, at the write of the command into `M` (Line 5). -/
theorem definition7_1 (ip : HelpingUniversal.InvocationPoint (n := n) obj)
    (ch : HelpingUniversal.Forward.Choices (n := n) obj)
    (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) :
    HelpingUniversal.Over.ConflictResolving obj G ip ch client sched N ↔
      ∀ (ch' : HelpingUniversal.Forward.Choices (n := n) obj) (client' : Fin n → Nat → Op)
        (sched' : Nat → Option (Fin n)) (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched' t).isSome),
        HelpingUniversal.Over.Extends obj G ch' client' sched' ch client sched N →
        HelpingUniversal.Over.EventuallyConflictFreeAfter obj G ip ch' client' sched' N →
        ∀ j, (HelpingUniversal.Over.execution obj G ch' client' sched' hlive).Correct
            ((HelpingUniversal.Over.execution obj G ch' client' sched' hlive).owner j) →
          (HelpingUniversal.Over.execution obj G ch' client' sched' hlive).Completes j :=
  Iff.rfl

open WeakUniversal.Forward (soloSched)

/-- **Theorem 7.2** (`th:cr`, conflict resolution). "For every finite execution
`α` of Algorithm 3 and every process `i`, there is a finite conflict-resolving
`i`-solo extension of `α`." -/
theorem theorem7_2 (hG : G.IsGCA) (ch : HelpingUniversal.Forward.Choices (n := n) obj)
    (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      HelpingUniversal.Over.Extends obj G ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      HelpingUniversal.Over.ConflictResolving obj G .announce ch client (soloSched sched N i) N' :=
  algorithm3Over_conflictResolution obj G hG ch client sched N i

/-- **Theorem 7.4** (`th:WeakUCresolve`, conflict forgetting). "For every finite
execution `α` of Algorithm 1 and every process `i`, there is a finite
conflict-forgetting `i`-solo extension of `α`", the GCA objects satisfying Solo
agreement. -/
theorem theorem7_4 (hG : G.IsGCA) (hsa : G.SoloAgreement)
    (ch : WeakUniversal.Forward.Choices (n := n) obj)
    (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      WeakUniversal.Over.Extends obj G ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      WeakUniversal.Over.ConflictForgetting obj G ch client (soloSched sched N i) N' :=
  algorithm1Over_weakUCresolve obj G hG hsa ch client sched N i

end Section7

/-! ## Appendix A -/

section AppendixA
variable {obj : Object State Op Response} [DecidableEq Op] {n : Nat}
  {H : WeakUniversal.Environment (n := n) obj}

/-- **Lemma A.1** (`lemma:prefix-rounds`), for Algorithm 1. "If a trace `s` is
committed in `GCA_r`, then every trace returned in `GCA_{r'}` with `r' ≥ r`
extends `s`" — for every run over GCA objects `H r` meeting the six properties. -/
theorem lemmaA_1_alg1 (g : GlobalSchedule.WeakRun obj H) (hspec : ∀ r, (H (r + 1)).Specification)
    {r r' : Nat} (hr : 1 ≤ r) (hrr : r ≤ r') {p q : Fin n}
    {s t : (WeakUniversal.Tagged (n := n) obj).Trace} {c : Bool}
    (hs : (H r).output p = some (s, true)) (ht : (H r').output q = some (t, c)) :
    (WeakUniversal.Tagged obj).TracePrefix s t :=
  g.prefix_rounds hspec hr hrr hs ht

/-- **Lemma A.1**, for Algorithm 3. -/
theorem lemmaA_1_alg3 (g : GlobalSchedule.HelpingRun obj H)
    (hspec : ∀ r, (H (r + 1)).Specification)
    {r r' : Nat} (hr : 1 ≤ r) (hrr : r ≤ r') {p q : Fin n}
    {s t : (WeakUniversal.Tagged (n := n) obj).Trace} {c : Bool}
    (hs : (H r).output p = some (s, true)) (ht : (H r').output q = some (t, c)) :
    (WeakUniversal.Tagged obj).TracePrefix s t :=
  g.prefix_rounds hspec hr hrr hs ht

end AppendixA

/-! ## The algorithms as machines

`forward1 obj n` and `forward3 obj n` run Algorithms 1 and 3 over Algorithm 2 as
deterministic machines — every client, every scheduler, every resolution of the
choices the paper leaves open — with every step a local computation followed by
at most one access to a register or a snapshot object. -/

section Machines
variable (obj : Object State Op Response) [DecidableEq Op] (n : Nat)

/-- Theorem 4.4, for the machine running Algorithm 1 over Algorithm 2. -/
theorem theorem4_4_machine : WeakConflictFree (forward1 obj n) obj.Conflict :=
  forward1_weakConflictFree obj n

/-- Lemma 6.2, for the machine running Algorithm 3 over Algorithm 2. -/
theorem lemma6_2_machine : ConflictFree (forward3 obj n) obj.Conflict :=
  forward3_conflictFree obj n

end Machines

end ConflictFreedom.Paper
