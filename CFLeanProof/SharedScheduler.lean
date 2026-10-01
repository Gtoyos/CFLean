import CFLeanProof.Progress
import CFLeanProof.InvocationTiming
import CFLeanProof.ProtocolInterleaving

/-!
# Operation-execution extraction and the shared scheduler

This module has three parts.

1. A *pending-implies-active* invariant for the invocation ledger: a command
   that has been invoked and has not yet returned is exactly the command the
   ledger records as active for its process.  This is the one-operation-per-
   process property that the operation-level `Execution` model calls
   `sequential`.
2. An extraction turning a ledger run, together with a schedule saying which
   operation instance takes each step, into a `ConflictFreedom.Execution`.
   Invocation and response times are the first time the ledger records the
   invocation and the response.  Because both universal constructions expose an
   `Execution.ledgerRun`, the extraction serves Algorithm 1 and Algorithm 3
   without duplication.
3. A single global schedule carrying the program run and the GCA protocol
   interleaving on one clock, together with the routing property that sends a
   process's infinitely many program steps to its currently outstanding GCA
   call.  This is what turns per-round `Interleaving.InfiniteSteps` into a
   consequence of operation-level `Execution.InfiniteSteps`.
-/

namespace ConflictFreedom

/-- Every satisfiable predicate on `Nat` has a least witness. -/
theorem exists_least (P : Nat → Prop) (h : ∃ t, P t) :
    ∃ m, P m ∧ ∀ k, P k → m ≤ k := by
  classical
  suffices H : ∀ t, P t → ∃ m, P m ∧ ∀ k, P k → m ≤ k by
    obtain ⟨t, ht⟩ := h
    exact H t ht
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    by_cases hlt : ∃ k, k < t ∧ P k
    · obtain ⟨k, hk, hPk⟩ := hlt
      exact ih k hk hPk
    · refine ⟨t, ht, fun k hPk => ?_⟩
      exact Nat.le_of_not_lt (fun hkt => hlt ⟨k, hkt, hPk⟩)

/-- First time a predicate on `Nat` holds. -/
noncomputable def firstTime (P : Nat → Prop) (h : ∃ t, P t) : Nat :=
  Classical.choose (exists_least P h)

theorem firstTime_spec (P : Nat → Prop) (h : ∃ t, P t) : P (firstTime P h) :=
  (Classical.choose_spec (exists_least P h)).1

theorem firstTime_le {P : Nat → Prop} {h : ∃ t, P t} {t : Nat} (ht : P t) :
    firstTime P h ≤ t :=
  (Classical.choose_spec (exists_least P h)).2 t ht

namespace InvocationLedger
variable {P Op : Type} [DecidableEq P]
omit [DecidableEq P] in

/-- Two entries of a key-injective list with the same key are equal. -/
theorem eq_of_key_nodup {l : List (Command P Op)} (h : (l.map Command.key).Nodup)
    {a b : Command P Op} (ha : a ∈ l) (hb : b ∈ l) (hk : a.key = b.key) : a = b := by
  induction l with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons x l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (hk ▸ List.mem_map.mpr ⟨b, hb', rfl⟩) h.1
    · exact absurd (hk ▸ List.mem_map.mpr ⟨a, ha', rfl⟩) h.1
    · exact ih h.2 ha' hb'

/-- An invoked, not-yet-returned command is the active command of its process. -/
def PendingActive (s : State P Op) : Prop :=
  ∀ cmd ∈ s.invoked, cmd ∉ s.returned → s.active cmd.process = some cmd

omit [DecidableEq P] in
theorem initial_pendingActive : PendingActive (initial : State P Op) := by
  intro cmd hcmd
  exact absurd hcmd (by simp [initial])

namespace Run
variable (e : Run P Op)

theorem pendingActive (t : Nat) : PendingActive (e.state t) := by
  induction t with
  | zero => rw [e.initial_state]; exact initial_pendingActive
  | succ t ih =>
    rcases e.next t with he | ⟨p, op, hp, he⟩ | ⟨p, c, hc, he⟩
    · exact he ▸ ih
    · rw [he]
      intro cmd hcmd hret
      rcases List.mem_cons.mp hcmd with rfl | hold
      · simp [invoke, InvocationLedger.update]
      · have hactive := ih cmd hold hret
        have hne : cmd.process ≠ p := by
          intro hpe
          rw [hpe, hp] at hactive
          exact absurd hactive (by simp)
        simpa [invoke, InvocationLedger.update, hne] using hactive
    · rw [he]
      intro cmd hcmd hret
      have hne : cmd ≠ c := fun h => hret (h ▸ List.mem_cons_self ..)
      have hactive := ih cmd hcmd (fun h => hret (List.mem_cons_of_mem _ h))
      have hproc : cmd.process ≠ p := by
        intro hpe
        rw [hpe, hc] at hactive
        exact hne (Option.some.inj hactive).symm
      simpa [finish, InvocationLedger.update, hproc] using hactive

/-- A command invoked by time `t` and not yet returned at time `t` is active. -/
theorem active_of_pending {cmd : Command P Op} {t : Nat}
    (hi : cmd ∈ (e.state t).invoked) (hr : cmd ∉ (e.state t).returned) :
    (e.state t).active cmd.process = some cmd :=
  e.pendingActive t cmd hi hr

/-- Distinct commands of one process cannot both be pending at the same time. -/
theorem pending_unique {a b : Command P Op} {t : Nat}
    (hia : a ∈ (e.state t).invoked) (hra : a ∉ (e.state t).returned)
    (hib : b ∈ (e.state t).invoked) (hrb : b ∉ (e.state t).returned)
    (hproc : a.process = b.process) : a = b := by
  have ha := e.active_of_pending hia hra
  have hb := e.active_of_pending hib hrb
  rw [hproc] at ha
  exact Option.some.inj (ha.symm.trans hb)

end Run

/-! ## Operation-execution extraction -/

variable {n : Nat}

/-- The operation clock runs one ledger tick behind: operation time `t` observes
ledger state `t + 1`.  The offset is a convention every theorem index follows;
with partial actors, alignment at time `0` would work as well, the empty initial
state having actor `none`. -/
abbrev obs (e : Run (Fin n) Op) (t : Nat) : State (Fin n) Op := e.state (t + 1)

theorem not_invoked_initial (e : Run (Fin n) Op) {cmd : Command (Fin n) Op}
    (h : cmd ∈ (e.state 0).invoked) : False := by
  rw [e.initial_state] at h
  exact absurd h (by simp [InvocationLedger.initial])

open Classical in
/-- First operation time at which the ledger records a response for `cmd`. -/
noncomputable def returnTime (e : Run (Fin n) Op) (cmd : Command (Fin n) Op) : Option Nat :=
  if h : ∃ t, cmd ∈ (obs e t).returned then some (firstTime _ h) else none

theorem returnTime_mem {e : Run (Fin n) Op} {cmd : Command (Fin n) Op} {r : Nat}
    (hr : returnTime e cmd = some r) : cmd ∈ (obs e r).returned := by
  classical
  unfold returnTime at hr
  split at hr
  · rename_i h
    exact (Option.some.inj hr) ▸ firstTime_spec _ h
  · exact absurd hr (by simp)

theorem returnTime_least {e : Run (Fin n) Op} {cmd : Command (Fin n) Op} {r u : Nat}
    (hr : returnTime e cmd = some r) (hm : cmd ∈ (obs e u).returned) : r ≤ u := by
  classical
  unfold returnTime at hr
  split at hr
  · rename_i h
    exact (Option.some.inj hr) ▸ firstTime_le (h := h) hm
  · exact absurd hr (by simp)

theorem returnTime_isSome {e : Run (Fin n) Op} {cmd : Command (Fin n) Op} {u : Nat}
    (hm : cmd ∈ (obs e u).returned) : ∃ r, returnTime e cmd = some r := by
  classical
  unfold returnTime
  split
  · exact ⟨_, rfl⟩
  · rename_i h
    exact absurd ⟨u, hm⟩ h

/-- Which operation instance takes the step at each global time.  The actor is
required to be the process's currently active command, so every global step is
attributed to a pending operation, exactly as the `Execution` model demands. -/
structure Schedule (e : Run (Fin n) Op) where
  actor : Nat → Option (Command (Fin n) Op)
  actor_active : ∀ t cmd, actor t = some cmd → (obs e t).active cmd.process = some cmd
  live : ∀ N, ∃ t cmd, N ≤ t ∧ actor t = some cmd

namespace Schedule
variable {e : Run (Fin n) Op} (s : Schedule e)

theorem actor_invoked {t : Nat} {cmd : Command (Fin n) Op} (h : s.actor t = some cmd) :
    cmd ∈ (obs e t).invoked :=
  ((e.valid (t + 1)).active_tag _ _ (s.actor_active t cmd h)).2.2

theorem actor_not_returned {t : Nat} {cmd : Command (Fin n) Op} (h : s.actor t = some cmd) :
    cmd ∉ (obs e t).returned := fun hm =>
  (e.valid (t + 1)).active_pending _ _ (s.actor_active t cmd h) _ hm rfl

/-- Instances of the extracted execution: the commands this run ever invokes. -/
abbrev Inst := { cmd : Command (Fin n) Op // ∃ t, cmd ∈ (obs e t).invoked }

/-- The scheduled command, carrying its invocation witness.  `none` at instants
where no operation runs -- for example right after a response is recorded. -/
noncomputable def actorInst (t : Nat) : Option (Inst (e := e)) := by
  classical
  exact if h : ∃ cmd, s.actor t = some cmd then
      some ⟨Classical.choose h, ⟨t, s.actor_invoked (Classical.choose_spec h)⟩⟩
    else none

theorem actorInst_val {t : Nat} {i : Inst (e := e)} (h : s.actorInst t = some i) :
    s.actor t = some i.val := by
  unfold actorInst at h
  split at h
  · rename_i hex
    rw [← Subtype.ext_iff.mp (Option.some.inj h)]
    exact Classical.choose_spec hex
  · cases h

theorem actorInst_of_actor {t : Nat} {cmd : Command (Fin n) Op}
    (h : s.actor t = some cmd) : ∃ i : Inst (e := e), s.actorInst t = some i ∧ i.val = cmd := by
  classical
  have hex : ∃ c, s.actor t = some c := ⟨cmd, h⟩
  refine ⟨⟨Classical.choose hex, ⟨t, s.actor_invoked (Classical.choose_spec hex)⟩⟩, ?_, ?_⟩
  · unfold actorInst; rw [dite_eq_left hex]
  · exact Option.some.inj ((Classical.choose_spec hex).symm.trans h)

/-- The operation-level execution induced by a ledger run and a schedule.
Instances are the invoked commands; the invocation time is the first time the
ledger records the invocation and the response time the first time it records
the response. -/
noncomputable def execution : _root_.ConflictFreedom.Execution n Op where
  Instance := Inst (e := e)
  operation := fun i => i.val.operation
  owner := fun i => i.val.process
  invoked := fun i => firstTime _ i.property
  returned := fun i => returnTime e i.val
  actor := s.actorInst
  live := by
    intro N
    obtain ⟨t, cmd, ht, hact⟩ := s.live N
    obtain ⟨i, hi, -⟩ := s.actorInst_of_actor hact
    exact ⟨t, i, ht, hi⟩
  return_after := by
    intro i r hr
    obtain ⟨u, hu, hiu⟩ := e.invoked_strictly_before_return (returnTime_mem hr)
    match u, hiu with
    | 0, hiu => exact absurd hiu (fun h => not_invoked_initial e h)
    | u + 1, hiu =>
        have := firstTime_le (h := i.property) hiu
        omega
  step_invoked := by
    intro t i hact
    exact firstTime_le (h := i.property) (s.actor_invoked (s.actorInst_val hact))
  step_pending := by
    intro t i r hact hr
    refine Nat.lt_of_not_le (fun hle => ?_)
    exact s.actor_not_returned (s.actorInst_val hact)
      (e.returned_mono (by omega) (returnTime_mem hr))
  sequential := by
    intro i j t hown hi hj hri hrj
    have mem : ∀ k : { cmd : Command (Fin n) Op // ∃ t, cmd ∈ (obs e t).invoked },
        firstTime _ k.property ≤ t → k.val ∈ (obs e t).invoked :=
      fun k hk => e.invoked_mono (by omega) (firstTime_spec _ k.property)
    have notret : ∀ k : { cmd : Command (Fin n) Op // ∃ t, cmd ∈ (obs e t).invoked },
        (∀ r, returnTime e k.val = some r → t < r) → k.val ∉ (obs e t).returned := by
      intro k hk hm
      obtain ⟨r, hr⟩ := returnTime_isSome hm
      exact absurd (returnTime_least hr hm) (by have := hk r hr; omega)
    exact Subtype.ext (e.pending_unique (mem i hi) (notret i hri)
      (mem j hj) (notret j hrj) hown)

/-- The extracted execution's instances, times and actors are the ledger's. -/
@[simp] theorem execution_owner (i : s.execution.Instance) :
    s.execution.owner i = i.val.process := rfl

@[simp] theorem execution_operation (i : s.execution.Instance) :
    s.execution.operation i = i.val.operation := rfl

@[simp] theorem execution_returned (i : s.execution.Instance) :
    s.execution.returned i = returnTime e i.val := rfl

/-- An operation completes exactly when the ledger eventually records it. -/
theorem execution_completes_iff (i : s.execution.Instance) :
    s.execution.Completes i ↔ ∃ t, i.val ∈ (obs e t).returned := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, returnTime_mem hr⟩
  · rintro ⟨t, ht⟩
    obtain ⟨r, hr⟩ := returnTime_isSome ht
    exact ⟨r, hr⟩

/-- Pending intervals in the extracted execution agree exactly with the ledger,
including the boundary at which a response is recorded. -/
theorem execution_pending_iff (i : s.execution.Instance) (t : Nat) :
    s.execution.Pending i t ↔
      i.val ∈ (obs e t).invoked ∧ i.val ∉ (obs e t).returned := by
  constructor
  · rintro ⟨hi, hr⟩
    refine ⟨e.invoked_mono (Nat.add_le_add_right hi 1) (firstTime_spec _ i.property), ?_⟩
    intro hm
    obtain ⟨r, hret⟩ := returnTime_isSome hm
    exact Nat.not_lt_of_ge (returnTime_least hret hm) (hr r hret)
  · rintro ⟨hi, hr⟩
    refine ⟨firstTime_le (h := i.property) hi, fun r hret => ?_⟩
    apply Nat.lt_of_not_ge
    intro hle
    exact hr (e.returned_mono (Nat.add_le_add_right hle 1) (returnTime_mem hret))

/-- The paper's time-indexed eventual conflict-freedom transports through the
extraction without any round-indexed hypothesis. Connecting this ledger
condition to the progress proofs' `Pending k` remains a separate obligation. -/
theorem execution_eventuallyConflictFree_iff (conflict : Op → Op → Prop) :
    s.execution.EventuallyConflictFree conflict ↔
      ∃ N, ∀ t, N ≤ t → ∀ a b : Command (Fin n) Op, a ≠ b →
        a ∈ (obs e t).invoked → a ∉ (obs e t).returned →
        b ∈ (obs e t).invoked → b ∉ (obs e t).returned →
        ¬ conflict a.operation b.operation := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun t ht a b hab hai har hbi hbr => ?_⟩
    let i : s.execution.Instance := ⟨a, ⟨t, hai⟩⟩
    let j : s.execution.Instance := ⟨b, ⟨t, hbi⟩⟩
    exact hN t ht i j (fun he => hab (congrArg Subtype.val he))
      ((s.execution_pending_iff i t).mpr ⟨hai, har⟩)
      ((s.execution_pending_iff j t).mpr ⟨hbi, hbr⟩)
  · rintro ⟨N, hN⟩
    refine ⟨N, fun t ht i j hij hi hj => ?_⟩
    obtain ⟨hai, har⟩ := (s.execution_pending_iff i t).mp hi
    obtain ⟨hbi, hbr⟩ := (s.execution_pending_iff j t).mp hj
    exact hN t ht i.val j.val (fun he => hij (Subtype.ext he)) hai har hbi hbr

end Schedule

/-! ### Nonvacuity

The witness is the run in which process `0` invokes once and then stutters
forever; its single operation is pending at every operation time. It witnesses
the ledger extraction only, not the universal constructions' progress claims. -/

/-- One process invokes at the first ledger step and the run then stutters. -/
def stuckRun {n : Nat} {Op : Type} (op : Op) : Run (Fin (n + 1)) Op where
  state := fun t => if t = 0 then initial else invoke initial (0 : Fin (n + 1)) op
  initial_state := rfl
  next := by
    intro t
    match t with
    | 0 => exact Or.inr (Or.inl ⟨0, op, by simp [InvocationLedger.initial], by simp⟩)
    | t + 1 => exact Or.inl (by simp)

/-- Its constant schedule: the lone pending command steps at every time. -/
def stuckSchedule {n : Nat} {Op : Type} (op : Op) :
    Schedule (stuckRun (n := n) op) where
  actor := fun _ => some ⟨op, 0, 1⟩
  actor_active := by
    intro t cmd h
    obtain rfl := (Option.some.inj h).symm
    simp [obs, stuckRun, InvocationLedger.invoke, InvocationLedger.initial,
      InvocationLedger.update]
  live := fun N => ⟨N, ⟨op, 0, 1⟩, Nat.le_refl _, rfl⟩

theorem schedule_nonempty {n : Nat} {Op : Type} (op : Op) :
    Nonempty (Schedule (stuckRun (n := n) op)) :=
  ⟨stuckSchedule op⟩

end InvocationLedger

/-! ## The shared scheduler -/

namespace SharedSchedule
open UniversalProtocol

variable {State Op Response : Type} {n : Nat}
    (obj : Object State Op Response) [DecidableEq Op]

/-- One global clock for Algorithm 1 and the family of GCA protocols it calls.
The program configuration, the protocol interleaving and the operation-level
schedule are all indexed by the same time.  `routing` is the scheduler
discipline that item 1 requires: whenever the process stepping at global time
`t` is blocked in a GCA call for round `r`, the global protocol event at `t`
belongs to that round and that process. -/
structure Weak (f : Family (n := n) obj) where
  run : WeakUniversal.Execution obj (f.environment obj)
  inter : Interleaving obj f
  opSchedule : InvocationLedger.Schedule (run.ledgerRun obj)
  routing : ∀ t p a cmd r proposal,
    opSchedule.actor t = some a → a.process = p →
    (run.state (t + 1)).localState p = .waiting cmd r proposal →
    inter.event (t + 1) = some (r, p)

namespace Weak
variable {obj} {f : Family (n := n) obj} (c : Weak obj f)

/-- The operation-level execution this shared schedule projects to. -/
noncomputable def execution : Execution n Op := c.opSchedule.execution

/-- **Routing, the progress transfer of item 1.**  A process that keeps taking
operation steps while blocked in a GCA call is scheduled in that round
infinitely often, so under the author's wait-free snapshot assumption the call
produces its output.  No process can be blocked in a GCA call forever while
still taking steps. -/
theorem blocked_output (hw : f.SnapshotWaitFree obj) {p : Fin n}
    {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {proposal : (WeakUniversal.Tagged (n := n) obj).Trace} {N : Nat}
    (hblock : ∀ t, N ≤ t → (c.run.state t).localState p = .waiting cmd r proposal)
    (hp : c.execution.InfiniteSteps p) :
    ∃ s flag, (f.environment obj r).output p = some (s, flag) := by
  refine c.inter.round_returned obj hw ?_
  intro M
  obtain ⟨t, i, ht, hact, hown⟩ := hp (max M N)
  refine ⟨t + 1, by omega, ?_⟩
  exact c.routing t p i.val cmd r proposal (c.opSchedule.actorInst_val hact) hown
    (hblock (t + 1) (by omega))

end Weak

/-- The same shared clock and routing discipline for Algorithm 3. -/
structure Helping (f : Family (n := n) obj) where
  run : HelpingUniversal.Execution obj (f.environment obj)
  inter : Interleaving obj f
  opSchedule : InvocationLedger.Schedule (run.ledgerRun obj)
  routing : ∀ t p a cmd r proposal,
    opSchedule.actor t = some a → a.process = p →
    (run.state (t + 1)).localState p = .waiting cmd r proposal →
    inter.event (t + 1) = some (r, p)

namespace Helping
variable {obj} {f : Family (n := n) obj} (c : Helping obj f)

/-- The operation-level execution this shared schedule projects to. -/
noncomputable def execution : Execution n Op := c.opSchedule.execution

theorem blocked_output (hw : f.SnapshotWaitFree obj) {p : Fin n}
    {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {proposal : (WeakUniversal.Tagged (n := n) obj).Trace} {N : Nat}
    (hblock : ∀ t, N ≤ t → (c.run.state t).localState p = .waiting cmd r proposal)
    (hp : c.execution.InfiniteSteps p) :
    ∃ s flag, (f.environment obj r).output p = some (s, flag) := by
  refine c.inter.round_returned obj hw ?_
  intro M
  obtain ⟨t, i, ht, hact, hown⟩ := hp (max M N)
  refine ⟨t + 1, by omega, ?_⟩
  exact c.routing t p i.val cmd r proposal (c.opSchedule.actorInst_val hact) hown
    (hblock (t + 1) (by omega))

end Helping
end SharedSchedule
end ConflictFreedom
