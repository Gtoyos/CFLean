import CFLeanProof.InvocationPoint
import CFLeanProof.ForwardHelping
import CFLeanProof.WeakUCResolve

/-!
# Theorem `th:cr`: every finite execution of Algorithm 3 has a finite conflict-resolving solo extension

> **Theorem (`th:cr`, Conflict resolution).**  For every finite execution `α` of
> Algorithm 3 and every process `i`, there is a finite conflict-resolving
> `i`-solo extension of `α`.

The statement quantifies over finite executions and their extensions, so, as for
`th:WeakUCresolve` (`WeakUCResolve.lean`), it is stated for Algorithm 3 *as a
machine* (`ForwardHelping`): a finite execution is the first `N` steps of the run
`frun client sched`, for any client and any scheduler, and an extension is a run
that takes the same first `N` steps (`Extends`).  GCA rounds run Algorithm 2
literally inside the machine; nothing about GCA is assumed.

**The definitions, at an invocation point.**  "Eventually `α`-conflict-free"
speaks of the operation instances invoked after `α` and of concurrent ones, so
it depends on where an operation's invocation is placed in its code.  That point
may be placed anywhere in the code (`HelpingUniversal.InvocationPoint`, in
`InvocationPoint.lean`), and the definitions below take it as a parameter `ip`.
**Theorem `th:cr` is stated and proved with the invocation point at Line 5, the
write of the command into `M`** (`InvocationPoint.announce`), as the manuscript's
proof states: "In the induced history of `α`, we consider an operation instance
as invoked once its associated command is written into `M` (Line 5)."

* `InvokedBy ip` — invoked at the point `ip`.  An operation instance is its
  tagged command.  At Line 5 it is the instance's first operation step in §3's
  execution (`invokedAfter_iff`): Lines 1–4 are local.
* `EventuallyConflictFreeAfter ip` is the manuscript's "eventually
  `α`-conflict-free": a suffix in which no two concurrent operation instances
  invoked after `α` conflict, concurrency being pending at a common time, both
  read at the point `ip` (`PendingAt ip`).
* `ConflictResolving ip` is Definition `def:wcr`: in every eventually
  `α`-conflict-free infinite extension of `α`, every correct process completes
  each of its operations — in §3's vocabulary, on the extension's execution.

**The solo extension** (`solo_extension`).  `soloSched sched N i` runs `sched`
for `N` steps and then only `i`, which invokes a new operation whenever its
current one completes.  `i` reaches rounds above every round reached in `α`
(`HelpingGCA.rounds_unbounded_from`), so it proposes a trace `s'` to some round `r₁`
above them, possibly after completing operations below it.  It is the only
participant of `r₁` in the solo run, so it receives `(s', true)`
(`HelpingGCA.solo_round_commits`: Commitment and Validity),
writes `(r₁, s')` into `S`, finds its command in `S` and completes; `α'` ends
there.  Its collect for `r₁` started after `α`, while `M[j] = M₀[j]` for every
`j ≠ i`, so every command invoked before the end of `α'` occurs in `s'`: a
completed one in a trace committed at a round at most `r₁`, which prefixes `s'`
(`lemma:prefix-rounds`), and a pending one in `M`.

**Conflict resolution** (`conflictResolution`).  The facts about `α'` the proof
needs are facts about its states, so they carry over to an extension
(`Extends`); `i`'s commit is re-read from its receive step in the extension's
own GCA family (`HelpingRun.committed_of_publishing`).  `HelpingGCA.resolving_completes`
then runs the manuscript's argument in the extension: invariants (II) and (I)
above the rounds reached once the forever-pending command is announced, and the
Commitment contradiction.

**Checks on the definitions.**  `invokedAfter_iff`: at Line 5, "invoked after
`α`" places `α`'s end exactly.
`eventuallyConflictFreeAfter_of_eventuallyConflictFree`: at every invocation
point in the operation's code, Line 5 included, the hypothesis is implied by
§3's eventual conflict-freedom, so `th:cr` strengthens the liveness guarantee at
the level of statements; `eventuallyConflictFreeAfter_strict`
shows the converse fails, on a run with a crashed process.
`conflictResolving_hypothesis_satisfiable`: the solo continuation meets the
hypothesis, so the definition always has an extension to speak about.
`resolution_beyond_conflictFreedom`: in the manuscript's execution (a) of Figure
`fig:resolving` — a crashed process with a pending conflicting operation, and
two correct processes running concurrently for ever — neither half of
`lemma:UCV2isCF` applies, and `th:cr` completes every correct process's
operations.

**Model.**  That of `forward3`: snapshot operations are atomic (the author's
assumption of wait-free linearizable snapshot objects) and a local computation
is one step.

**Over any GCA implementation.**  The same theorem, for Algorithm 3 over any GCA
implementation meeting the specification of §4.2, is
`HelpingUniversal.Over.conflictResolution` (`Algorithm3OverGCA`); Algorithm 2
is one such implementation (`ForwardGCA.machine_isGCA`).
-/

/-! ## Theorem `th:cr` over any GCA meeting the interface

As for `th:WeakUCresolve` (`WeakUCResolve.lean`): a finite execution `α` is the
first `N` steps of a run `g`, an extension is any run over GCA objects meeting
the interface that takes the same first `N` steps (`HelpingRun.Extends`), and
`HelpingGCA.conflictResolution` is Theorem `th:cr` in its modular form: **every**
`i`-solo continuation of `α` has a finite conflict-resolving prefix longer than
`α`.  §7's point of invocation — an operation instance is invoked once its
command is written into `M` — is `HelpingRun.AnnouncedBy`.  Unlike
`th:WeakUCresolve`, no Solo agreement is needed.  A solo continuation exists
for any GCA implementation meeting the specification — its run under
`soloSched` — which gives the manuscript's statement for every such
implementation (`HelpingUniversal.Over.conflictResolution`, in
`Algorithm3OverGCA`). -/

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol
open WeakUniversal (Cmd Tagged Seed Call Return update zeroSeed best)

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}

namespace HelpingRun

/-- **An extension of a finite execution**, for Algorithm 3: the run `g'`, over
any GCA objects, takes the same first `N` steps as `g`. -/
def Extends {H' : WeakUniversal.Environment (n := n) obj} (g' : HelpingRun obj H')
    (g : HelpingRun obj H) (N : Nat) : Prop :=
  (∀ t, t < N → g'.actor t = g.actor t) ∧ ∀ t, t ≤ N → g'.run.state t = g.run.state t

/-- **Definition `def:wcr`, conflict-resolving execution, over any GCA meeting
the interface, at the invocation point `ip`.**  The finite execution `α` of the
first `N` steps of `g` is conflict-resolving if in every eventually
`α`-conflict-free infinite extension of `α` — a run over any GCA objects meeting
the interface, eventual `α`-conflict-freedom read at the invocation point `ip`
(`HelpingUniversal.EventuallyConflictFreeAfter`) — every correct process
completes each of its operations. -/
def ConflictResolving (g : HelpingRun obj H) (ip : HelpingUniversal.InvocationPoint (n := n) obj)
    (N : Nat) : Prop :=
  ∀ (H' : WeakUniversal.Environment (n := n) obj) (g' : HelpingGCA obj H') (hp : g'.OpLive),
    g'.Extends g N → HelpingUniversal.EventuallyConflictFreeAfter ip g'.run.state N →
    ∀ j, (g'.execution hp).Correct ((g'.execution hp).owner j) → (g'.execution hp).Completes j

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- **The solo extension, over any GCA meeting the interface.**  If only `i` is
scheduled after the first `N` steps, then at some time `N' > N` it has waited on
a round `R` above every round reached in the first `N` steps, received
`(s', true)` from it and published `(R, s')`, and returned: `S[i]` holds a round
`≥ R`, and every command written into `M` within the first `N'` steps occurs in
`s'` — "every operation instance invoked before the end of `α'` has its
associated command in `ops(s')`". -/
theorem solo_extension {N : Nat} {i : Fin n} (hsolo : g.SoloFrom N i) :
    ∃ N' v R cmd s', N < N' ∧ v < N' ∧
      (g.run.state v).localState i = .waiting cmd R s' ∧
      (g.run.state (v + 1)).localState i = .publishing cmd ⟨R, s'⟩ ∧
      R ≤ ((g.run.state N').slots i).round ∧
      (∀ a, g.AnnouncedBy N' a → 0 < (Tagged obj).traceCount a s') ∧
      (∀ call ∈ (g.run.state N).calls, call.round < R) ∧
      (∀ q, HelpingUniversal.nextRound obj ((g.run.state N).localState q) < R) ∧
      (⟨cmd, R, s'⟩ : Return (n := n) obj) ∈ (g.run.state N').returns ∧
      cmd.process = i := by
  classical
  have hsched := hsolo.sched
  -- every round reached in the first `N` steps is at most `B`
  obtain ⟨B, hB⟩ := WeakUniversal.calls_round_bound obj (g.run.state N).calls
  have hbound : ∀ q, HelpingUniversal.localRound obj ((g.run.state N).localState q) ≤ B := by
    intro q
    rcases (HelpingUniversal.roundsCalled obj (g.run.reachable obj N)).2 q with
      h0 | ⟨call, hmem, he⟩
    · omega
    · rw [← he]; exact hB call hmem
  have hown : ∀ (t : Nat) (call : WeakUniversal.Call (n := n) obj),
      call ∈ (g.run.state t).calls → B < call.round → call.process = i := by
    intro t call hcall hlt
    apply Classical.byContradiction
    intro hne
    rcases Nat.le_total N t with hNt | htN
    · exact absurd (hB call (g.calls_of_solo hsolo hNt hcall hne)) (by omega)
    · exact absurd (hB call (g.calls_mono htN hcall)) (by omega)
  -- `i` waits on a round `R > B + 1`, beyond every round any process was heading for
  obtain ⟨t, htN, htB⟩ := g.rounds_unbounded_from hsched N (B + 1)
  obtain ⟨u, hu, cmd, R, prop, hL, hR⟩ := g.reaches_waiting_always hsched t
  have hRB : B + 1 < R := by omega
  obtain ⟨hcall, hcount⟩ :=
    HelpingUniversal.waiting_call obj (g.run.reachable obj u) i cmd R prop hL
  have hin : (H R).input i = some prop := by
    simpa using HelpingUniversal.call_input obj (g.run.reachable obj u) _ hcall
  have hproc : cmd.process = i :=
    ((HelpingUniversal.identity_invariant obj (g.run.reachable obj u)).active_tag i cmd
      (by simp [HelpingUniversal.ledger, hL, HelpingUniversal.Local.command])).1
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  -- alone in `R`, it receives its own proposal, committed
  obtain ⟨v, hv, hconst, hstep⟩ := g.solo_next_step hsolo (show N ≤ u by omega)
  have hLv : (g.run.state v).localState i = .waiting cmd (R' + 1) prop := by
    rw [hconst]; exact hL
  obtain ⟨s, flag, hout, order, -, hnew⟩ := HelpingUniversal.stepBy_from_waiting obj hstep hLv
  obtain ⟨hs, hflag⟩ := g.solo_round_commits hown (show B < R' + 1 by omega) hin hout
  subst hs; subst hflag
  have hpub : (g.run.state (v + 1)).localState i = .publishing cmd ⟨R' + 1, s⟩ := by
    rw [hnew]; simp
  -- it writes `(R, s')` into `S`
  obtain ⟨v2, hv2, hconst2, hstep2⟩ :=
    g.solo_next_step hsolo (show N ≤ v + 1 by omega)
  obtain ⟨order2, horder2, hchk, hslots⟩ :=
    HelpingUniversal.stepBy_from_publishing obj hstep2 (by rw [hconst2]; exact hpub)
  have hslotp : (g.run.state (v2 + 1)).slots i = ⟨R' + 1, s⟩ := by
    rw [hslots]; exact WeakUniversal.update_self _ _ _
  -- its final collect adopts `(R, s')`, the highest round in `S`
  obtain ⟨z, hz, hLz⟩ := g.solo_check_collect hsolo hown order2
    (v2 + 1) (by omega) cmd ⟨R' + 1, s⟩ (WeakUniversal.zeroSeed obj) hchk hslotp
    (show B < R' + 1 by omega)
    (Or.inl ⟨horder2.mem_iff.mpr (List.mem_finRange i), by simp [WeakUniversal.zeroSeed]⟩)
  -- and it returns
  obtain ⟨z2, hz2, hconst3, hstep3⟩ := g.solo_next_step hsolo (show N ≤ z by omega)
  obtain ⟨hidle, -, hret⟩ :=
    HelpingUniversal.stepBy_finish obj hstep3 (by rw [hconst3]; exact hLz) hcount
  -- every call made by `N'` is to a round at most `R`
  have hcallsN' : ∀ call ∈ (g.run.state (z2 + 1)).calls, call.round ≤ R' + 1 := by
    intro call hc
    by_cases hci : call.process = i
    · have hbnd :=
        (HelpingUniversal.call_tracking obj (g.run.reachable obj (z2 + 1))).bounded call hc
      rw [hci, hidle] at hbnd
      exact hbnd
    · have := hB call (g.calls_of_solo hsolo (by omega) hc hci)
      omega
  -- a command answered by `N'` lies in a trace committed at a round at most `R`,
  -- which prefixes `s'` (`lemma:prefix-rounds`)
  have hanswered : ∀ a, (∃ ret ∈ (g.run.state (z2 + 1)).returns, ret.command = a) →
      0 < (Tagged obj).traceCount a s := by
    rintro a ⟨ret, hret, rfl⟩
    obtain ⟨⟨hpos, q, hq⟩, hcount'⟩ :=
      (HelpingUniversal.invariant obj (g.run.reachable obj (z2 + 1))).returns ret hret
    rcases (HelpingUniversal.returnsCalled obj (g.run.reachable obj (z2 + 1))).2 ret hret with
      h0 | ⟨call, hmem, he⟩
    · omega
    · have hle := hcallsN' call hmem
      obtain ⟨r, hr⟩ : ∃ r, ret.round = r + 1 := ⟨ret.round - 1, by omega⟩
      rw [hr] at hq
      have hpre := HelpingUniversal.committed_prefix obj g.callsCovered
        g.gca.spec (show r ≤ R' by omega) hq hout
      exact Nat.lt_of_lt_of_le hcount' ((Tagged obj).traceCount_mono hpre _)
  refine ⟨z2 + 1, v, R' + 1, cmd, s, by omega, by omega, hLv, hpub, ?_, ?_, ?_, ?_, hret,
    hproc⟩
  · have hmono := g.slots_mono (q := i) (show v2 + 1 ≤ z2 + 1 by omega)
    rw [hslotp] at hmono
    exact hmono
  · -- every command invoked by the end of `α'` occurs in `s'`
    intro a ha
    obtain ⟨u0, hu0, hm0⟩ := ha
    rcases g.announcement_or_answered hm0 (z2 + 1) hu0 with hM | hans
    · by_cases hqi : a.process = i
      · -- `i` has returned, so the command left in `M[i]` is answered
        refine hanswered a (HelpingUniversal.announcement_answered obj
          (g.run.reachable obj (z2 + 1)) a.process a hM ?_)
        rw [hqi]
        show HelpingUniversal.Unannounced obj ((g.run.state (z2 + 1)).localState i)
        rw [hidle]; trivial
      · -- `M[a.process]` has not moved since `α`, and `i` collected it for round `R`
        have hconstM := g.announcements_const_of_solo hsolo hqi
        have hMN : (g.run.state N).announcements a.process = some a := by
          rw [← hconstM (z2 + 1) (by omega)]; exact hM
        have hann : ∀ t, N ≤ t → (g.run.state t).announcements a.process = some a :=
          fun t ht => by rw [hconstM t ht]; exact hMN
        have hnewc : (⟨R' + 1, i, s⟩ : WeakUniversal.Call (n := n) obj)
            ∉ (g.run.state N).calls := by
          intro hm
          have := hB _ hm
          simp only at this
          omega
        obtain ⟨v', hv', cmd', seed, commands, arranged, hsrc, harr, hr, htr⟩ :=
          g.call_was_gathering_after hcall hnewc
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hv'
        have hround : R' + 1 = seed.round + 1 := hr
        rcases g.helped_gathering hann hbound d i cmd' seed [] commands hsrc (by omega) with
          hmem | hc
        · exact absurd hmem (by simp)
        · have hp : s = HelpingUniversal.proposal obj seed arranged := htr
          rw [hp, HelpingUniversal.proposal_count_perm obj a seed harr]; exact hc
    · exact hanswered a hans
  · intro call hc
    have := hB call hc
    omega
  · intro q
    have h1 := hbound q
    have h2 := HelpingUniversal.nextRound_le_localRound obj ((g.run.state N).localState q)
    show HelpingUniversal.nextRound obj ((g.run.state N).localState q) < R' + 1
    omega

/-- **Theorem `th:cr`, over any GCA meeting the interface.**  For every finite
execution `α` — the first `N` steps of a run `g` of Algorithm 3 — and every
process `i`: if only `i` is scheduled after `α`, then some prefix of `g` of length
`N' > N`, an `i`-solo extension of `α`, is conflict-resolving, with the
invocation point at Line 5 (`InvocationPoint.announce`). -/
theorem conflictResolution {N : Nat} {i : Fin n} (hsolo : g.SoloFrom N i) :
    ∃ N', N < N' ∧ g.ConflictResolving .announce N' := by
  obtain ⟨N', v, R, cmd, s', hNN', hv, hwait, hpub, hslot, hcover, -, -, -, -⟩ :=
    g.solo_extension hsolo
  refine ⟨N', hNN', ?_⟩
  intro H' g' hp hext hcf j hcorrect
  have hst := hext.2
  have hwait' : (g'.run.state v).localState i = .waiting cmd R s' := by
    rw [hst v (by omega)]; exact hwait
  have hpub' : (g'.run.state (v + 1)).localState i = .publishing cmd ⟨R, s'⟩ := by
    rw [hst (v + 1) (by omega)]; exact hpub
  have hpos : 0 < R := by
    have := (HelpingUniversal.invariant obj (g'.run.reachable obj v)).localState i
    rw [hwait'] at this
    exact this
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  -- `i`'s commit, read off its receive step in the extension's own GCA objects
  have hcom := g'.committed_of_publishing hwait' hpub'
  have hslot' : R' + 1 ≤ ((g'.run.state N').slots i).round := by
    rw [hst N' (Nat.le_refl _)]; exact hslot
  have hcover' : ∀ a, g'.AnnouncedBy N' a → 0 < (Tagged obj).traceCount a s' := by
    rintro a ⟨u, hu, hm⟩
    exact hcover a ⟨u, hu, by rw [← hst u hu]; exact hm⟩
  obtain ⟨T, hT⟩ := hcf
  have hC : g'.EventuallyNonconflictingAfter N' T := by
    intro t ht a b hab ha har hb hbr haN hbN
    exact (obj.independent_iff_not_conflict a.operation b.operation).mpr
      (hT t ht a b hab ⟨ha, har⟩ ⟨hb, hbr⟩ haN hbN)
  rcases hcorrect with hinf | hall
  · obtain ⟨t, ht⟩ := j.property
    exact g'.execution_completes_of_command hp
      (g'.resolving_completes hcom hslot' hcover' hC (g'.stepping_of_infiniteSteps hp hinf)
        ⟨t + 1, ht⟩ rfl)
  · exact hall j rfl

end HelpingGCA
end ConflictFreedom.GlobalSchedule

namespace ConflictFreedom.HelpingUniversal.Forward
open Object UniversalProtocol ForwardGCA
open WeakUniversal (Cmd Tagged Seed Call Return update zeroSeed best)
open WeakUniversal.Forward (soloSched soloSched_before soloSched_after soloSched_live)

variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-! ## Finite executions of the machine and their extensions -/

/-- The run's first `N` steps are determined by the scheduler's first `N`
choices. -/
theorem frun_congr {ch : Choices (n := n) obj} {client : Fin n → Nat → Op} {s₁ s₂ : Nat → Option (Fin n)} {N : Nat}
    (h : ∀ t, t < N → s₁ t = s₂ t) : ∀ t, t ≤ N → frun obj ch client s₁ t = frun obj ch client s₂ t
  | 0, _ => rfl
  | t + 1, ht => by
      rw [frun_succ, frun_succ, frun_congr h t (by omega), h t (by omega)]

/-- **An extension of a finite execution.**  The finite execution `α` is the
first `N` steps of `frun ch client sched`; the run of `ch'`, `client'` and
`sched'` extends it when it takes the same first `N` steps — the same process at
every step, reaching the same configurations.  The client may differ on
operations invoked after `α`, and the rule for the collect orders and
`trace(M_i)` on the choices made after `α`. -/
def Extends (ch' : Choices (n := n) obj) (client' : Fin n → Nat → Op) (sched' : Nat → Option (Fin n))
    (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) : Prop :=
  (∀ t, t < N → sched' t = sched t) ∧
    ∀ t, t ≤ N → frun obj ch' client' sched' t = frun obj ch client sched t

/-- The §3 execution of a non-halting run of the machine — an execution of
`forward3`. -/
noncomputable def execution (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome) : _root_.ConflictFreedom.Execution n Op :=
  (fsched obj ch client sched).execution (fsched_opLive obj ch client sched hlive)

theorem execution_forward3 (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome) :
    forward3 obj n (execution obj ch client sched hlive) :=
  ⟨client, ch, sched, hlive, rfl⟩

/-! ## §7's definitions, for Algorithm 3, at an invocation point

The definitions that mention invocation are read at an invocation point `ip`,
which may be placed anywhere in the operation's code
(`HelpingUniversal.InvocationPoint`); `th:cr` below places it at Line 5, the
write of the command into `M` (`InvocationPoint.announce`). -/

/-- The instance with command `a` is **invoked by time `t`** in the machine's
run, at the invocation point `ip`.  At Line 5 (`ip = .announce`): `a` has been
written into `M[a.process]` within the first `t` steps. -/
def InvokedBy (ip : HelpingUniversal.InvocationPoint (n := n) obj)
    (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (t : Nat) (a : Cmd n Op) : Prop :=
  HelpingUniversal.InvokedBy ip (fun t => (frun obj ch client sched t).1) t a

/-- Pending at time `t`, at the invocation point `ip`: invoked, and not yet
answered. -/
def PendingAt (ip : HelpingUniversal.InvocationPoint (n := n) obj)
    (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (t : Nat) (a : Cmd n Op) : Prop :=
  HelpingUniversal.PendingAt ip (fun t => (frun obj ch client sched t).1) t a

/-- **Eventually `α`-conflict-free**, at the invocation point `ip`, for the
finite execution `α` of the first `N` steps: the execution has a suffix in which
no two concurrent operation instances `Φ = (o, i)` and `Φ' = (o', j)` invoked
after `α` satisfy `o ≍ o'`.  Concurrent in the suffix means pending at a common
time of the suffix, as in §3's `EventuallyConflictFree`; "pending" and "invoked
after `α`" are read at the point `ip`. -/
def EventuallyConflictFreeAfter (ip : HelpingUniversal.InvocationPoint (n := n) obj)
    (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) : Prop :=
  HelpingUniversal.EventuallyConflictFreeAfter ip (fun t => (frun obj ch client sched t).1) N

/-- **Definition `def:wcr`, conflict-resolving execution, at the invocation point
`ip`.**  The finite execution `α` (the first `N` steps of `frun client sched`) is
conflict-resolving if in every eventually `α`-conflict-free infinite extension of
`α`, every correct process completes each of its operations.

"Infinite" is the scheduler not halting, as in `forward3`; correctness and
completion are §3's, on the extension's execution, and do not depend on `ip`. -/
def ConflictResolving (ip : HelpingUniversal.InvocationPoint (n := n) obj)
    (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) : Prop :=
  ∀ (ch' : Choices (n := n) obj) (client' : Fin n → Nat → Op) (sched' : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched' t).isSome),
    Extends obj ch' client' sched' ch client sched N →
    EventuallyConflictFreeAfter obj ip ch' client' sched' N →
    ∀ j, (execution obj ch' client' sched' hlive).Correct ((execution obj ch' client' sched' hlive).owner j) →
      (execution obj ch' client' sched' hlive).Completes j

/-! ## The solo extension -/

/-- **The solo extension.**  After the first `N` steps of any run, let `i` run
alone.  At some time `N' > N`, `i` has waited on a round `R` above every round
reached in the first `N` steps, received `(s', true)` from it and published
`(R, s')`, and returned: `S[i]` holds a round `≥ R`, and every command written
into `M` within the first `N'` steps occurs in `s'` — "every operation instance
invoked before the end of `α'` has its associated command in `ops(s')`". -/
theorem solo_extension (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (N : Nat) (i : Fin n) :
    ∃ N' v R cmd s', N < N' ∧ v < N' ∧
      (frun obj ch client (soloSched sched N i) v).1.localState i = .waiting cmd R s' ∧
      (frun obj ch client (soloSched sched N i) (v + 1)).1.localState i
        = .publishing cmd ⟨R, s'⟩ ∧
      R ≤ ((frun obj ch client (soloSched sched N i) N').1.slots i).round ∧
      (∀ a, InvokedBy obj .announce ch client (soloSched sched N i) N' a →
        0 < (Tagged obj).traceCount a s') ∧
      (∀ call ∈ (frun obj ch client (soloSched sched N i) N).1.calls, call.round < R) ∧
      (∀ q, HelpingUniversal.nextRound obj
        ((frun obj ch client (soloSched sched N i) N).1.localState q) < R) ∧
      (⟨cmd, R, s'⟩ : Return (n := n) obj) ∈ (frun obj ch client (soloSched sched N i) N').1.returns ∧
      cmd.process = i :=
  ((fsched obj ch client (soloSched sched N i)).toGCA (fsched_fair obj ch client _)
    (fam_waitFree obj ch client _)).solo_extension
    (FiniteScheduling.SoloFrom.of_continuous _ fun _ ht => soloSched_after ht)

/-! ## The theorem -/

/-- **Theorem `th:cr` (Conflict resolution).**  For every finite execution `α`
of Algorithm 3 — the first `N` steps of the machine's run for any client and any
scheduler — and every process `i`, there is a finite conflict-resolving `i`-solo
extension of `α`: the first `N'` steps of the run that follows `α` and then
schedules only `i`.  The invocation point is Line 5, the write of the command
into `M` (`InvocationPoint.announce`), as in the manuscript's proof. -/
theorem conflictResolution (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictResolving obj .announce ch client (soloSched sched N i) N' := by
  obtain ⟨N', hNN', hcr⟩ := ((fsched obj ch client (soloSched sched N i)).toGCA
    (fsched_fair obj ch client _) (fam_waitFree obj ch client _)).conflictResolution
    (FiniteScheduling.SoloFrom.of_continuous _ fun _ ht => soloSched_after ht)
  refine ⟨N', hNN', ⟨fun t ht => soloSched_before ht,
      frun_congr obj (fun t ht => soloSched_before ht)⟩,
    fun t ht _ => soloSched_after ht, ?_⟩
  intro ch' client' sched' hlive hext hcf
  exact hcr _ ((fsched obj ch' client' sched').toGCA (fsched_fair obj ch' client' sched')
      (fam_waitFree obj ch' client' sched')) (fsched_opLive obj ch' client' sched' hlive)
    ⟨fun t ht => hext.1 t ht, fun t ht => congrArg Prod.fst (hext.2 t ht)⟩ hcf

/-! ## The definitions, checked against the machine -/

/-- **The invocation point at Line 5, in §3's vocabulary.**  An instance of the
execution is invoked after `α` at Line 5 — its command is not written into `M`
within the first `N` steps — exactly when it takes no operation step within `α`,
that is, none before operation time `N - 1` (the boundary `Forward.stepsFrom_iff`
places for Algorithm 1).  An instance's first operation step is its write into
`M`: Lines 1–4 are local. -/
theorem invokedAfter_iff (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome)
    (j : (execution obj ch client sched hlive).Instance) (N : Nat) :
    ¬ InvokedBy obj .announce ch client sched N j.val ↔
      ∀ t, (execution obj ch client sched hlive).actor t = some j → N - 1 ≤ t := by
  have h := (fsched obj ch client sched).announcedBy_iff_step (fsched_opLive obj ch client sched hlive) j N
  constructor
  · intro hnot t hact
    apply Nat.le_of_not_lt
    intro hlt
    exact hnot (h.mpr ⟨t, by omega, hact⟩)
  · intro hall hinv
    obtain ⟨t, ht, hact⟩ := h.mp hinv
    have := hall t hact
    omega

/-- **The hypothesis is implied by §3's eventual conflict-freedom**, at every
invocation point in the operation's code — Line 5 (`InvocationPoint.announce_inCode`)
included.  So the theorem strengthens the liveness guarantee, as the manuscript
intends: only the conflicts among operations invoked after `α` are constrained. -/
theorem eventuallyConflictFreeAfter_of_eventuallyConflictFree
    {ip : HelpingUniversal.InvocationPoint (n := n) obj} (hip : ip.InCode)
    (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome) (N : Nat)
    (h : (execution obj ch client sched hlive).EventuallyConflictFree obj.Conflict) :
    EventuallyConflictFreeAfter obj ip ch client sched N :=
  (fsched obj ch client sched).eventuallyConflictFreeAfter_of_eventuallyConflictFree hip
    (fsched_opLive obj ch client sched hlive) N h

/-- In the solo continuation, every instance invoked after `N' ≥ N` is `i`'s,
and two of `i`'s instances are never pending at once, so the continuation is
eventually conflict-free after every such prefix. -/
theorem soloSched_conflictFreeAfter (ch : Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) {N' : Nat} (hN : N ≤ N') :
    EventuallyConflictFreeAfter obj .announce ch client (soloSched sched N i) N' := by
  let g := fsched obj ch client (soloSched sched N i)
  have hsolo : g.SoloFrom N i :=
    FiniteScheduling.SoloFrom.of_continuous _ fun _ ht => soloSched_after ht
  have own : ∀ t c, InvokedBy obj .announce ch client (soloSched sched N i) t c →
      ¬ InvokedBy obj .announce ch client (soloSched sched N i) N' c → c.process = i := by
    rintro t c ⟨u, hu, hm⟩ hnot
    apply Classical.byContradiction
    intro hne
    rcases Nat.le_total u N' with huN | hNu
    · exact hnot ⟨u, huN, hm⟩
    · have hconstM := g.announcements_const_of_solo hsolo hne
      have hmN' : (g.run.state N').announcements c.process = some c := by
        rw [hconstM N' hN, ← hconstM u (by omega)]; exact hm
      exact hnot ⟨N', Nat.le_refl _, hmN'⟩
  refine ⟨0, fun t _ a b hab ha hb haN hbN => absurd ?_ hab⟩
  exact g.announced_pending_unique ha.1 ha.2 hb.1 hb.2
    ((own t a ha.1 haN).trans (own t b hb.1 hbN).symm)

/-- A run extends each of its own prefixes. -/
theorem extends_refl (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) :
    Extends obj ch client sched ch client sched N :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **`ConflictResolving` is not vacuous.**  Every solo prefix of the form
`conflictResolution` produces has an infinite extension meeting the definition's
hypothesis — the solo continuation itself. -/
theorem conflictResolving_hypothesis_satisfiable (ch : Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) {N' : Nat} (hN : N ≤ N') :
    (∀ M, ∃ t, M ≤ t ∧ (soloSched sched N i t).isSome) ∧
      Extends obj ch client (soloSched sched N i) ch client (soloSched sched N i) N' ∧
      EventuallyConflictFreeAfter obj .announce ch client (soloSched sched N i) N' :=
  ⟨soloSched_live sched N i, extends_refl obj ch client _ N',
    soloSched_conflictFreeAfter obj ch client sched N i hN⟩

/-! ## The hypothesis is strictly weaker than §3's

`eventuallyConflictFreeAfter_of_eventuallyConflictFree` shows `th:cr`'s
hypothesis is implied by §3's eventual conflict-freedom.  The converse fails, on
a run of the machine: a process that crashes with a pending operation keeps the
run from ever being conflict-free in §3's sense, while `th:cr` only constrains
the operations invoked after the prefix. -/

/-- A program step invokes, if at all, the operation the client supplies, for
the stepping process. -/
theorem progStep_invocations (ch : Choices (n := n) obj) (c : Configuration (n := n) obj)
    (p : Fin n) (op : Op) :
    ∀ a ∈ (progStep obj ch c p op).invocations,
      a ∈ c.invocations ∨ (a.operation = op ∧ a.process = p) := by
  intro a ha
  unfold progStep at ha
  split at ha
  · rcases List.mem_cons.mp ha with rfl | hm
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl hm
  all_goals first
    | exact Or.inl ha
    | (split at ha <;> exact Or.inl ha)

/-- **Client provenance.**  Every operation a run invokes is one its client
supplied to the invoking process. -/
theorem invocation_client (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) :
    ∀ t, ∀ a ∈ (frun obj ch client sched t).1.invocations, ∃ k, a.operation = client a.process k := by
  intro t
  induction t with
  | zero => intro a ha; simp [frun, HelpingUniversal.initial] at ha
  | succ t ih =>
      intro a ha
      rcases frun_cases obj ch client sched t with
        ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, -, hw, he⟩
      · rw [he] at ha; exact ih a ha
      · rw [he] at ha; exact ih a ha
      · rw [he] at ha
        have hinv : (recvStep obj ch (frun obj ch client sched t).1 p
            (frameOutput (Tagged obj) n ((frun obj ch client sched t).2.frame p) v)).invocations
            = (frun obj ch client sched t).1.invocations := by
          unfold recvStep; split <;> rfl
        rw [hinv] at ha
        exact ih a ha
      · rw [he] at ha
        rcases progStep_invocations obj ch _ p _ a ha with hold | ⟨hop, hproc⟩
        · exact ih a hold
        · exact ⟨_, by rw [hop, hproc]⟩

section Strict
variable (o o' : Op)

/-- Process `1` invokes `o`; process `0` invokes `o'`, again and again. -/
def crashClient : Fin 2 → Nat → Op := fun p _ => if p = 1 then o else o'

/-- Process `1` takes the first two steps — it invokes and writes its command
into `M` — and then crashes; from then on process `0` runs alone. -/
def crashSched : Nat → Option (Fin 2) := soloSched (fun _ => some 1) 2 0

/-- **The hypothesis of `th:cr` is strictly weaker than §3's.**  For any object
with two conflicting operations `o` and `o'`: in the run where process `1`
invokes `o`, writes it into `M` and crashes, and process `0` then runs alone
invoking `o'` for ever, the run is eventually conflict-free after its first two
steps in `th:cr`'s sense — every instance invoked afterwards is process `0`'s —
but not in §3's: process `1`'s `o` stays pending, concurrently with process
`0`'s instances of `o'`. -/
theorem eventuallyConflictFreeAfter_strict (ch : Choices (n := 2) obj) (hconf : obj.Conflict o o') :
    ∃ hlive : ∀ M, ∃ t, M ≤ t ∧ (crashSched t).isSome,
      EventuallyConflictFreeAfter obj .announce ch (crashClient o o') crashSched 2 ∧
      ¬ (execution obj ch (crashClient o o') crashSched hlive).EventuallyConflictFree
          obj.Conflict := by
  classical
  have hlive := soloSched_live (fun _ => some (1 : Fin 2)) 2 0
  refine ⟨hlive, soloSched_conflictFreeAfter obj ch (crashClient o o') _ 2 0 (Nat.le_refl _), ?_⟩
  rintro ⟨M, hM⟩
  let g := fsched obj ch (crashClient o o') crashSched
  have hp := fsched_opLive obj ch (crashClient o o') crashSched hlive
  let c1 : Cmd 2 Op := ⟨o, 1, 1⟩
  -- process `1` has invoked `c1` after one step, and is stuck on it from step 2 on
  have h1 : c1 ∈ (g.run.state 1).invocations := by
    simp [g, fsched_state, frun, fstep, crashSched, soloSched, progStep,
      HelpingUniversal.initial, crashClient, c1]
  obtain ⟨todo, h2⟩ :
      ∃ todo, (g.run.state 2).localState 1 = .collecting c1 todo (zeroSeed obj) := by
    simp [g, fsched_state, frun, fstep, crashSched, soloSched, progStep,
      HelpingUniversal.initial, update, crashClient, c1]
  have hstuck : ∀ t, 2 ≤ t →
      (g.run.state t).localState 1 = .collecting c1 todo (zeroSeed obj) := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    refine (local_const obj ch (crashClient o o') crashSched d (fun w hw _ hs => ?_)).trans h2
    rw [show crashSched w = some 0 from soloSched_after hw] at hs
    exact absurd (Option.some.inj hs) (by decide)
  -- so `c1` is never answered
  have hnoret : ∀ t, ∀ ret ∈ (g.run.state t).returns, ret.command ≠ c1 :=
    g.never_answered_of_current fun t ht => by rw [hstuck t ht]; rfl
  -- process `0` holds an operation at arbitrarily late operation times
  obtain ⟨t, ht, hsome⟩ := hp (max M 2)
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨j, hj, hjval⟩ := (g.schedule hp).actorInst_of_actor hc0
  obtain ⟨q, hq, hactive⟩ := g.opActor_eq_some hc0
  have hq0 : q = 0 := by
    have : crashSched (t + 1) = some 0 := soloSched_after (by omega)
    exact Option.some.inj (hq.symm.trans this)
  subst hq0
  have hproc0 : c0.process = 0 :=
    ((HelpingUniversal.identity_invariant obj (g.run.reachable obj (t + 1))).active_tag
      0 c0 hactive).1
  have hop0 : c0.operation = o' := by
    have hin := ((HelpingUniversal.identity_invariant obj (g.run.reachable obj (t + 1))).active_tag
      0 c0 hactive).2.2
    obtain ⟨k, hk⟩ := invocation_client obj ch (crashClient o o') crashSched (t + 1) c0 hin
    rw [hk, hproc0]
    simp [crashClient]
  -- both are pending at operation time `t`, and they conflict
  let i1 : (execution obj ch (crashClient o o') crashSched hlive).Instance := ⟨c1, ⟨0, h1⟩⟩
  have hpend1 : (execution obj ch (crashClient o o') crashSched hlive).Pending i1 t := by
    refine ((g.schedule hp).execution_pending_iff i1 t).mpr ⟨?_, ?_⟩
    · exact (g.run.ledgerRun obj).invoked_mono (show 1 ≤ t + 1 by omega) h1
    · intro hm
      obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
      exact hnoret (t + 1) ret hret he
  have hpendj : (execution obj ch (crashClient o o') crashSched hlive).Pending j t :=
    ⟨(execution obj ch (crashClient o o') crashSched hlive).step_invoked t j hj,
      fun r hr => (execution obj ch (crashClient o o') crashSched hlive).step_pending t j r hj hr⟩
  have hne : i1 ≠ j := by
    intro he
    have : c1.process = c0.process := by rw [← hjval, ← he]
    rw [hproc0] at this
    exact (show (1 : Fin 2) ≠ 0 by decide) this
  refine hM t (by omega) i1 j hne hpend1 hpendj ?_
  show obj.Conflict c1.operation j.val.operation
  rw [hjval, hop0]
  exact hconf

end Strict

/-! ## Conflict resolution beyond conflict-freedom

`th:cr` is not subsumed by `lemma:UCV2isCF`: in the manuscript's execution (a)
of Figure `fig:resolving`, a crashed process's pending operation keeps the run
from being eventually conflict-free, no instance ever runs alone, and still
every correct process completes each of its operations, by `th:cr`. -/

/-- **A process the scheduler keeps choosing takes infinitely many operation
steps.**  When it is scheduled it holds a command, or it invokes one and holds
it until it is next scheduled. -/
theorem infiniteSteps_of_scheduled (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome) {p : Fin n}
    (hp : ∀ N, ∃ t, N ≤ t ∧ sched t = some p) :
    (execution obj ch client sched hlive).InfiniteSteps p := by
  classical
  let g := fsched obj ch client sched
  have hop := fsched_opLive obj ch client sched hlive
  -- an operation step of `p` at operation time `t`, from `p` holding a command at `t + 1`
  have hstep : ∀ t, sched (t + 1) = some p →
      ((frun obj ch client sched (t + 1)).1.localState p).command obj ≠ none →
      ∃ j, (execution obj ch client sched hlive).actor t = some j ∧
        (execution obj ch client sched hlive).owner j = p := by
    intro t hs hc
    cases hcmd : ((frun obj ch client sched (t + 1)).1.localState p).command obj with
    | none => exact absurd hcmd hc
    | some c =>
        have hopt : g.opActor t = some c := by
          show (match sched (t + 1) with
            | none => none
            | some q => (HelpingUniversal.ledger obj (frun obj ch client sched (t + 1)).1).active q)
              = some c
          rw [hs]; exact hcmd
        obtain ⟨j, hj, hval⟩ := (g.schedule hop).actorInst_of_actor hopt
        have hproc : c.process = p :=
          ((HelpingUniversal.identity_invariant obj (g.run.reachable obj (t + 1))).active_tag
            p c hcmd).1
        exact ⟨j, hj, by show j.val.process = p; rw [hval]; exact hproc⟩
  intro N
  obtain ⟨t₁, ⟨ht₁, hs₁⟩, -⟩ := exists_least (fun w => N + 1 ≤ w ∧ sched w = some p) (hp (N + 1))
  obtain ⟨t, rfl⟩ : ∃ t, t₁ = t + 1 := ⟨t₁ - 1, by omega⟩
  by_cases hc : ((frun obj ch client sched (t + 1)).1.localState p).command obj = none
  · -- idle and scheduled: it invokes, and holds the command until it is next scheduled
    obtain ⟨seed, hidle⟩ := command_none obj hc
    obtain ⟨t₂, ⟨ht₂, hs₂⟩, hmin⟩ :=
      exists_least (fun w => t + 2 ≤ w ∧ sched w = some p) (hp (t + 2))
    have hinv : ((frun obj ch client sched (t + 2)).1.localState p).command obj ≠ none := by
      have hw : GlobalSchedule.helpingRound obj
          ((frun obj ch client sched (t + 1)).1.localState p) = none := by
        rw [hidle]; rfl
      have he := fstep_prog obj ch client (frun obj ch client sched (t + 1)) hw
      rw [← hs₁, ← frun_succ] at he
      rw [he]
      simp [progStep, hidle, update, Local.command]
    have hconst := local_const obj ch client sched (a := t + 2) (p := p) (t₂ - (t + 2))
      (fun w hw hwd hsw => absurd (hmin w ⟨hw, hsw⟩) (by omega))
    rw [show t + 2 + (t₂ - (t + 2)) = t₂ from by omega] at hconst
    obtain ⟨t₃, rfl⟩ : ∃ t₃, t₂ = t₃ + 1 := ⟨t₂ - 1, by omega⟩
    obtain ⟨j, hj, hown⟩ := hstep t₃ hs₂ (by rw [hconst]; exact hinv)
    exact ⟨t₃, j, by omega, hj, hown⟩
  · obtain ⟨j, hj, hown⟩ := hstep t hs₁ hc
    exact ⟨t, j, by omega, hj, hown⟩


section Resolution
variable (o o' : Op)

/-- Process `1` invokes `o`; processes `0` and `2` invoke `o'`, again and again. -/
def figClient : Fin 3 → Nat → Op := fun p _ => if p = 1 then o else o'

/-- The finite execution `α`: process `1` invokes `o` and writes it into `M` in
its first two steps. -/
def figPrefix : Nat → Option (Fin 3) := fun _ => some 1

/-- The extension: the `0`-solo extension `α'` of `α` for its first `N'` steps,
then processes `0` and `2` alternate for ever.  Process `1` never steps again. -/
def figSched (N' : Nat) : Nat → Option (Fin 3) := fun t =>
  if t < N' then soloSched figPrefix 2 0 t else if t % 2 = 0 then some 0 else some 2

/-- **Conflict resolution beyond conflict-freedom** — execution (a) of the
manuscript's Figure `fig:resolving`, on the machine.  Take any object with
operations `o` and `o'` such that `o` conflicts with `o'` and `o'` does not
conflict with itself (a read and an increment of a counter, say).  Process `1`
invokes `o`, writes it into `M` and crashes; `th:cr` gives a conflict-resolving
`0`-solo extension `α'`; after `α'`, processes `0` and `2` run concurrently for
ever, invoking `o'`.

In that extension, neither half of `lemma:UCV2isCF` applies: the run is not
eventually conflict-free — process `1`'s `o` stays pending beside the others'
`o'` — and no instance ever runs alone, so `Solo j` holds only of instances
that complete anyway.  Yet it is eventually `α'`-conflict-free, and `th:cr`
completes every operation of every correct process. -/
theorem resolution_beyond_conflictFreedom (ch : Choices (n := 3) obj)
    (hconf : obj.Conflict o o') (hself : ¬ obj.Conflict o' o') :
    ∃ (N' : Nat) (hlive : ∀ M, ∃ t, M ≤ t ∧ (figSched N' t).isSome),
      ConflictResolving obj .announce ch (figClient o o') (soloSched figPrefix 2 0) N' ∧
      Extends obj ch (figClient o o') (figSched N') ch (figClient o o') (soloSched figPrefix 2 0) N' ∧
      EventuallyConflictFreeAfter obj .announce ch (figClient o o') (figSched N') N' ∧
      ¬ (execution obj ch (figClient o o') (figSched N') hlive).EventuallyConflictFree
          obj.Conflict ∧
      (∀ j, ¬ ∃ M, ∀ t j', M ≤ t →
        (execution obj ch (figClient o o') (figSched N') hlive).actor t = some j' → j' = j) ∧
      (execution obj ch (figClient o o') (figSched N') hlive).InfiniteSteps 0 ∧
      (execution obj ch (figClient o o') (figSched N') hlive).InfiniteSteps 2 ∧
      ∀ j, (execution obj ch (figClient o o') (figSched N') hlive).Correct
          ((execution obj ch (figClient o o') (figSched N') hlive).owner j) →
        (execution obj ch (figClient o o') (figSched N') hlive).Completes j := by
  classical
  obtain ⟨N', hN', -, -, hres⟩ := conflictResolution obj ch (figClient o o') figPrefix 2 0
  have hlate : ∀ t, N' ≤ t → figSched N' t = if t % 2 = 0 then some 0 else some 2 := by
    intro t ht
    simp [figSched, show ¬ t < N' by omega]
  have hlive : ∀ M, ∃ t, M ≤ t ∧ (figSched N' t).isSome := by
    intro M
    refine ⟨max M N', Nat.le_max_left _ _, ?_⟩
    rw [hlate _ (Nat.le_max_right _ _)]
    split <;> rfl
  have hext : Extends obj ch (figClient o o') (figSched N') ch (figClient o o')
      (soloSched figPrefix 2 0) N' :=
    ⟨fun t ht => by simp [figSched, ht],
      frun_congr obj (fun t ht => by simp [figSched, ht])⟩
  -- process `1` takes steps `0` and `1` only
  have hsched1 : ∀ t, 2 ≤ t → figSched N' t ≠ some 1 := by
    intro t ht
    unfold figSched
    split
    · rw [soloSched_after ht]; decide
    · split <;> decide
  have hs0 : figSched N' 0 = some 1 := by simp [figSched, soloSched, figPrefix, show 0 < N' by omega]
  have hs1 : figSched N' 1 = some 1 := by simp [figSched, soloSched, figPrefix, show 1 < N' by omega]
  let g := fsched obj ch (figClient o o') (figSched N')
  let c1 : Cmd 3 Op := ⟨o, 1, 1⟩
  have hst1 : (frun obj ch (figClient o o') (figSched N') 1).1.localState 1
        = .announcing c1 (zeroSeed obj) ∧
      (frun obj ch (figClient o o') (figSched N') 1).1.announcements 1 = none ∧
      c1 ∈ (frun obj ch (figClient o o') (figSched N') 1).1.invocations := by
    simp [frun, fstep, hs0, progStep, HelpingUniversal.initial, update, figClient, c1]
  obtain ⟨todo, hst2⟩ : ∃ todo, (frun obj ch (figClient o o') (figSched N') 2).1.localState 1
        = .collecting c1 todo (zeroSeed obj) ∧
      (frun obj ch (figClient o o') (figSched N') 2).1.announcements 1 = some c1 := by
    simp [frun, fstep, hs0, hs1, progStep, HelpingUniversal.initial, update, figClient, c1]
  have hM0 : (g.run.state 0).announcements 1 = none := by
    rw [g.run.initial_state]; rfl
  -- from step 2 on, process `1` is stuck on `c1`, which stays in `M[1]`
  have hstuck : ∀ t, 2 ≤ t →
      (g.run.state t).localState 1 = .collecting c1 todo (zeroSeed obj) :=
    fun t ht => (g.localState_const_of_unscheduled ht (fun v hv _ => hsched1 v hv)).trans hst2.1
  have hM1 : ∀ t, 2 ≤ t → (g.run.state t).announcements 1 = some c1 :=
    fun t ht => (g.announcements_const_of_unscheduled ht (fun v hv _ => hsched1 v hv)).trans
      hst2.2
  -- so every command of process `1` written into `M` is `c1`, written within `α`
  have hproc1 : ∀ t a, InvokedBy obj .announce ch (figClient o o') (figSched N') t a →
      a.process = 1 → InvokedBy obj .announce ch (figClient o o') (figSched N') N' a := by
    rintro t a ⟨u, hu, hm⟩ h1
    change (g.run.state u).announcements a.process = some a at hm
    rw [h1] at hm
    rcases Nat.lt_or_ge u 2 with hlt | hge
    · rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
      · rw [hM0] at hm; cases hm
      · rw [show (g.run.state 1).announcements 1 = none from hst1.2.1] at hm; cases hm
    · rw [hM1 u hge] at hm
      have hac : a = c1 := (Option.some.inj hm).symm
      refine ⟨2, by omega, ?_⟩
      change (g.run.state 2).announcements a.process = some a
      rw [hac]
      exact hst2.2
  -- the operations of processes `0` and `2` are `o'`
  have hop' : ∀ t a, a ∈ (g.run.state t).invocations → a.process ≠ 1 → a.operation = o' := by
    intro t a ha hne
    obtain ⟨k, hk⟩ := invocation_client obj ch (figClient o o') (figSched N') t a ha
    rw [hk]
    simp [figClient, hne]
  have hinvOf : ∀ t a, InvokedBy obj .announce ch (figClient o o') (figSched N') t a →
      a ∈ (g.run.state t).invocations := by
    rintro t a ⟨u, hu, hm⟩
    exact (g.run.ledgerRun obj).invoked_mono hu
      ((HelpingUniversal.proposal_provenance obj (g.run.reachable obj u)).announcements _ a hm)
  -- the hypothesis of `th:cr`: after `α'`, only `o'` is invoked
  have hcf : EventuallyConflictFreeAfter obj .announce ch (figClient o o') (figSched N') N' := by
    refine ⟨0, fun t _ a b _ ha hb haN hbN => ?_⟩
    rw [hop' t a (hinvOf t a ha.1) (fun h => haN (hproc1 t a ha.1 h)),
      hop' t b (hinvOf t b hb.1) (fun h => hbN (hproc1 t b hb.1 h))]
    exact hself
  -- processes `0` and `2` take infinitely many steps
  have hinf0 : (execution obj ch (figClient o o') (figSched N') hlive).InfiniteSteps 0 :=
    infiniteSteps_of_scheduled obj ch _ _ hlive (fun M => ⟨2 * (M + N'), by omega, by
      rw [hlate _ (by omega)]; simp [show 2 * (M + N') % 2 = 0 by omega]⟩)
  have hinf2 : (execution obj ch (figClient o o') (figSched N') hlive).InfiniteSteps 2 :=
    infiniteSteps_of_scheduled obj ch _ _ hlive (fun M => ⟨2 * (M + N') + 1, by omega, by
      rw [hlate _ (by omega)]; simp [show (2 * (M + N') + 1) % 2 = 1 by omega]⟩)
  have hp := fsched_opLive obj ch (figClient o o') (figSched N') hlive
  refine ⟨N', hlive, hres, hext, hcf, ?_, ?_, hinf0, hinf2, hres _ _ _ hlive hext hcf⟩
  · -- not eventually conflict-free: `c1` is pending for ever, beside process `0`'s `o'`
    rintro ⟨M, hM⟩
    have hnoret : ∀ t, ∀ ret ∈ (g.run.state t).returns, ret.command ≠ c1 :=
      g.never_answered_of_current fun t ht => by rw [hstuck t ht]; rfl
    obtain ⟨t, j, ht, hj, hown⟩ := hinf0 (max M 2)
    let i1 : (execution obj ch (figClient o o') (figSched N') hlive).Instance := ⟨c1, ⟨0, hst1.2.2⟩⟩
    have hpend1 : (execution obj ch (figClient o o') (figSched N') hlive).Pending i1 t := by
      refine ((g.schedule hp).execution_pending_iff i1 t).mpr ⟨?_, ?_⟩
      · exact (g.run.ledgerRun obj).invoked_mono (show 1 ≤ t + 1 by omega) hst1.2.2
      · intro hm
        obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
        exact hnoret (t + 1) ret hret he
    have hpendj : (execution obj ch (figClient o o') (figSched N') hlive).Pending j t :=
      ⟨(execution obj ch (figClient o o') (figSched N') hlive).step_invoked t j hj,
        fun r hr => (execution obj ch (figClient o o') (figSched N') hlive).step_pending t j r hj hr⟩
    have hj1 : j.val.process ≠ 1 := by
      intro h
      have : (0 : Fin 3) = 1 := hown.symm.trans h
      exact absurd this (by decide)
    have hopj : j.val.operation = o' := by
      obtain ⟨u, hu⟩ := j.property
      exact hop' (u + 1) j.val hu hj1
    have hne : i1 ≠ j := by
      intro he
      have : c1.process = j.val.process := by rw [← he]
      exact hj1 this.symm
    refine hM t (by omega) i1 j hne hpend1 hpendj ?_
    show obj.Conflict c1.operation j.val.operation
    rw [hopj]
    exact hconf
  · -- no instance runs alone: processes `0` and `2` both keep taking steps
    rintro j ⟨M, hM⟩
    obtain ⟨t0, j0, ht0, hj0, hown0⟩ := hinf0 M
    obtain ⟨t2, j2, ht2, hj2, hown2⟩ := hinf2 M
    have e0 := hM t0 j0 ht0 hj0
    have e2 := hM t2 j2 ht2 hj2
    subst e0
    subst e2
    have : (0 : Fin 3) = 2 := hown0.symm.trans hown2
    exact absurd this (by decide)

end Resolution

end ConflictFreedom.HelpingUniversal.Forward

namespace ConflictFreedom
open HelpingUniversal.Forward
open WeakUniversal.Forward (soloSched)
variable {State Op Response : Type} [DecidableEq Op]

/-- **Theorem `th:cr`** (the same statement as
`HelpingUniversal.Forward.conflictResolution`): for every finite execution of
Algorithm 3 as the machine runs it — the first `N` steps of `frun client sched` —
and every process `i`, the run that continues with `i` alone has a finite prefix
of length `N' > N` that is conflict-resolving. -/
theorem forward3_conflictResolution (obj : Object State Op Response) {n : Nat}
    (ch : Choices (n := n) obj)
    (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictResolving obj .announce ch client (soloSched sched N i) N' :=
  conflictResolution obj ch client sched N i

end ConflictFreedom
