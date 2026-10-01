import CFLeanProof.ConflictResolution

/-!
# Invocation points

§3: "Each execution induces a *history*, which is a sequence of operation
invocation and response events."  Where in an operation's code its invocation
event is placed is a choice, and it is standard that the invocation point may be
put at any point of the code: the induced history — and with it which operation
instances are pending, which are concurrent, and which are invoked after a finite
execution `α` — is then the one of the chosen point.  The proof of `th:cr` uses
this freedom openly: "In the induced history of `α`, we consider an operation
instance as invoked once its associated command is written into `M` (Line 5)."

This module states the choice explicitly, for Algorithm 3.

* `InvocationPoint` — a choice of invocation point: which configurations show an
  operation instance as having reached it.  An instance is invoked by time `t`
  when some configuration up to `t` does (`InvokedBy`).
* `InvocationPoint.InCode` — the point lies in the operation's code: in every
  run, an instance reaches it only once it has been invoked, and has reached it
  by the time it returns, so the pending interval it defines lies within the
  instance's own.
* The two points of `invoke(op)` that matter:
  - `InvocationPoint.invoke` — Lines 1–4, the command has been created: where
    the program's ledger, hence §3's execution (`InvocationLedger.Schedule`)
    and the linearizability theorems, record the invocation;
  - `InvocationPoint.announce` — **Line 5, the command has been written into
    `M`: the point Theorem `th:cr` is stated and proved with.**  Lines 1–4 are
    local, so it is the instance's first operation step in §3's execution
    (`HelpingRun.invokedBy_announce_iff_step`).
  Both lie in the code (`invoke_inCode`, `announce_inCode`), and Line 5 comes
  after Lines 1–4 (`invokedBy_invoke_of_announce`).
* The notions of §7 that mention invocation, for any invocation point:
  `PendingAt` and `EventuallyConflictFreeAfter`.  For every point in the code,
  §3's eventual conflict-freedom implies eventual `α`-conflict-freedom
  (`HelpingRun.eventuallyConflictFreeAfter_of_eventuallyConflictFree`).

`UCResolve` and `Algorithm3OverGCA` state *conflict-resolving* for any
invocation point and prove `th:cr` with the invocation point at Line 5.
-/

namespace ConflictFreedom.HelpingUniversal
open WeakUniversal (Cmd)

variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-- **An invocation point** of Algorithm 3's operations: `reached c a` says that
the configuration `c` shows the operation instance with command `a` as having
reached the point.  The instance counts as invoked from the first time a
configuration of the run does (`InvokedBy`). -/
structure InvocationPoint where
  reached : Configuration (n := n) obj → Cmd n Op → Prop

namespace InvocationPoint
variable {obj}

/-- **Lines 1–4 of `invoke(op)`**: the command `(op, i, seq)` has been created.
The program's ledger records the invocation here, so this is the invocation
point of §3's execution (`InvocationLedger.Schedule.execution`) and of the
linearizability theorems. -/
def invoke : InvocationPoint (n := n) obj := ⟨fun c a => a ∈ c.invocations⟩

/-- **Line 5 of `invoke(op)`**: the command has been written into `M` — "we
consider an operation instance as invoked once its associated command is written
into `M`".  Theorem `th:cr` is stated and proved with this invocation point. -/
def announce : InvocationPoint (n := n) obj :=
  ⟨fun c a => c.announcements a.process = some a⟩

end InvocationPoint

variable {obj}
variable (ip : InvocationPoint (n := n) obj) (st : Nat → Configuration (n := n) obj)

/-- The instance with command `a` is **invoked by time `t`**, at the invocation
point `ip`: some configuration up to `t` shows it having reached the point. -/
def InvokedBy (t : Nat) (a : Cmd n Op) : Prop := ∃ u, u ≤ t ∧ ip.reached (st u) a

/-- **Pending at time `t`**, at the invocation point `ip`: invoked, and not yet
answered. -/
def PendingAt (t : Nat) (a : Cmd n Op) : Prop :=
  InvokedBy ip st t a ∧ ∀ ret ∈ (st t).returns, ret.command ≠ a

/-- **Eventually `α`-conflict-free**, at the invocation point `ip`, for the
finite execution `α` of the first `N` steps: the run has a suffix in which no two
concurrent operation instances `Φ = (o, i)` and `Φ' = (o', j)` invoked after `α`
satisfy `o ≍ o'` — concurrency being pending at a common time.  Both "invoked
after `α`" and "pending" are read at the invocation point `ip`. -/
def EventuallyConflictFreeAfter (N : Nat) : Prop :=
  ∃ T, ∀ t, T ≤ t → ∀ a b : Cmd n Op, a ≠ b →
    PendingAt ip st t a → PendingAt ip st t b →
    ¬ InvokedBy ip st N a → ¬ InvokedBy ip st N b →
    ¬ obj.Conflict a.operation b.operation

variable {ip st} in
theorem InvokedBy.mono {t t' : Nat} (htt' : t ≤ t') {a : Cmd n Op} (h : InvokedBy ip st t a) :
    InvokedBy ip st t' a := by
  obtain ⟨u, hu, hr⟩ := h
  exact ⟨u, by omega, hr⟩

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.HelpingUniversal.InvocationPoint
open GlobalSchedule
open WeakUniversal (Cmd)

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op]

/-- **An invocation point lies in the operation's code** when, in every run of
Algorithm 3 over any GCA objects, an instance reaches it only once invoked, and
has reached it by the time it returns: the invocation it records is no earlier
than the instance's invocation, and no later than its response. -/
structure InCode (ip : InvocationPoint (n := n) obj) : Prop where
  invoked : ∀ (H : WeakUniversal.Environment (n := n) obj) (g : HelpingRun obj H) t a,
    InvokedBy ip g.run.state t a → a ∈ (g.run.state t).invocations
  answered : ∀ (H : WeakUniversal.Environment (n := n) obj) (g : HelpingRun obj H) t a,
    (∃ ret ∈ (g.run.state t).returns, ret.command = a) → InvokedBy ip g.run.state t a

/-- **Lines 1–4 lie in the code.** -/
theorem invoke_inCode : (invoke : InvocationPoint (n := n) obj).InCode where
  invoked := by
    rintro H g t a ⟨u, hu, hm⟩
    exact (g.run.ledgerRun obj).invoked_mono hu hm
  answered := by
    rintro H g t a ⟨ret, hret, he⟩
    have hm : a ∈ ((g.run.ledgerRun obj).state t).returned := List.mem_map.mpr ⟨ret, hret, he⟩
    obtain ⟨u, hu, hinv⟩ := (g.run.ledgerRun obj).invoked_strictly_before_return hm
    exact ⟨u, Nat.le_of_lt hu, hinv⟩

/-- **Line 5 lies in the code**: `M` holds only invoked commands, and an operation
writes its command into `M` before it returns. -/
theorem announce_inCode : (announce : InvocationPoint (n := n) obj).InCode where
  invoked := by
    rintro H g t a ⟨u, hu, hm⟩
    exact (g.run.ledgerRun obj).invoked_mono hu
      ((HelpingUniversal.proposal_provenance obj (g.run.reachable obj u)).announcements _ a hm)
  answered := by
    intro H g t a h
    obtain ⟨u, hu, hm⟩ := g.announced_before_answer h
    exact ⟨u, Nat.le_of_lt hu, hm⟩

/-- **Line 5 comes after Lines 1–4**: an instance invoked at Line 5 by time `t`
is invoked at Lines 1–4 by then.  So the instances invoked after `α` at Line 5
are those invoked after `α` at Lines 1–4, together with those invoked within `α`
whose command was not yet written into `M` at its end. -/
theorem invokedBy_invoke_of_announce {H : WeakUniversal.Environment (n := n) obj}
    (g : HelpingRun obj H) {t : Nat} {a : Cmd n Op}
    (h : InvokedBy announce g.run.state t a) : InvokedBy invoke g.run.state t a :=
  ⟨t, Nat.le_refl _, announce_inCode.invoked H g t a h⟩

end ConflictFreedom.HelpingUniversal.InvocationPoint

namespace ConflictFreedom.GlobalSchedule
open WeakUniversal (Cmd)
open HelpingUniversal (InvocationPoint InvokedBy PendingAt EventuallyConflictFreeAfter)

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}

namespace HelpingRun
variable (g : HelpingRun obj H)

/-- At Line 5, "invoked by time `t`" is `AnnouncedBy`, the notion the proof of
`th:cr` works with. -/
theorem invokedBy_announce {t : Nat} {a : Cmd n Op} :
    InvokedBy InvocationPoint.announce g.run.state t a ↔ g.AnnouncedBy t a := Iff.rfl

/-- **Line 5 is the instance's first operation step** in §3's execution: its
command has been written into `M` by time `N` exactly when it took an operation
step at an operation time `t` with `t + 1 < N` — operation time `t` being the
run's step `t + 1`.  Lines 1–4 are local steps, which §3's execution does not
attribute to the instance. -/
theorem invokedBy_announce_iff_step (hp : g.OpLive) (j : (g.execution hp).Instance) (N : Nat) :
    InvokedBy InvocationPoint.announce g.run.state N j.val ↔
      ∃ t, t + 1 < N ∧ (g.execution hp).actor t = some j :=
  g.announcedBy_iff_step hp j N

/-- **For every invocation point in the code, §3's eventual conflict-freedom
implies eventual `α`-conflict-freedom.**  An instance pending at the invocation
point is pending in §3's execution, where no two concurrent instances conflict
from some time on. -/
theorem eventuallyConflictFreeAfter_of_eventuallyConflictFree
    {ip : InvocationPoint (n := n) obj} (hip : ip.InCode) (hp : g.OpLive) (N : Nat)
    (h : (g.execution hp).EventuallyConflictFree obj.Conflict) :
    EventuallyConflictFreeAfter ip g.run.state N := by
  obtain ⟨M, hM⟩ := ((g.schedule hp).execution_eventuallyConflictFree_iff obj.Conflict).mp h
  refine ⟨M + 1, fun t ht a b hab ha hb _ _ => ?_⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  refine hM t' (by omega) a b hab (hip.invoked H g _ a ha.1) (fun hm => ?_)
    (hip.invoked H g _ b hb.1) (fun hm => ?_)
  · obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
    exact ha.2 ret hret he
  · obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
    exact hb.2 ret hret he

end HelpingRun

end ConflictFreedom.GlobalSchedule
