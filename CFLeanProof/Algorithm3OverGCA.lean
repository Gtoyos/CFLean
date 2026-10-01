import CFLeanProof.GCAMachineAlgorithm2
import CFLeanProof.UCResolve
import CFLeanProof.Algorithm1OverGCA

/-!
# Algorithm 3 over any GCA implementation, and Theorem `th:cr`

> **Theorem (`th:cr`, Conflict resolution).**  For every finite execution `α`
> of Algorithm 3 and every process `i`, there is a finite conflict-resolving
> `i`-solo extension of `α`.

The counterpart of `Algorithm1OverGCA` for Algorithm 3.  `mrun G client sched`
runs Algorithm 3 over any GCA implementation `G : GCAMachine`; every run is a run
of Algorithm 3 over GCA objects meeting `GlobalSchedule.HelpingRun.GCAInterface`
when `G` meets the specification of §4.2 (`gcaInterface`), so the theorems proved
over the interface hold for it (`algorithm3Over_conflictFree`,
`infinite_event_linearization`), and `conflictResolution` is the theorem for
every such `G`.  Unlike `th:WeakUCresolve`, Solo agreement is not needed.

The definitions of §7 are those of `HelpingUniversal.Forward`, read on the run
over `G`, at an invocation point `ip` — which may be placed anywhere in the
operation's code (`HelpingUniversal.InvocationPoint`): an operation instance is
invoked once it reaches `ip` (`InvokedBy`), "eventually `α`-conflict-free"
concerns instances invoked after `α` (`EventuallyConflictFreeAfter`), and a
conflict-resolving execution is one all of whose eventually `α`-conflict-free
infinite extensions over `G` complete every operation of every correct process
(`ConflictResolving`).  **Theorem `th:cr` is proved with the invocation point
at Line 5, the write of the command into `M`** (`InvocationPoint.announce`), as
in the manuscript's proof.

Algorithm 2 is an instance: Algorithm 3 over `ForwardGCA.machine` is the forward
machine of `ForwardHelping` (`mrun_machine`), and `conflictResolution_algorithm2`
is `th:cr` for the composition, with no hypothesis.
-/

namespace ConflictFreedom.HelpingUniversal.Over
open Object UniversalProtocol GCAMachine
open WeakUniversal (Cmd Tagged Seed Call Return update zeroSeed best)
open GlobalSchedule (helpingRound)

variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op] (G : GCAMachine (Tagged (n := n) obj) n)

/-- **One instant of Algorithm 3 over the GCA machine `G`.** -/
def mstep (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (x : Configuration (n := n) obj × G.State) :
    Option (Fin n) → Configuration (n := n) obj × G.State
  | none => x
  | some p =>
      match x.1.localState p with
      | .waiting _ r v =>
          match G.output x.2 p r v with
          | none => (x.1, G.step x.2 p r v)
          | some o => (Forward.recvStep obj ch x.1 p o, G.leave x.2 p)
      | _ => (Forward.progStep obj ch x.1 p (client p (x.1.sequence p)), x.2)

/-- **The run of Algorithm 3 over `G`** for a rule `ch` for the collect orders and
`trace(M_i)`, a client and a scheduler. -/
def mrun (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) :
    Nat → Configuration (n := n) obj × G.State
  | 0 => (HelpingUniversal.initial obj, G.init)
  | t + 1 => mstep obj G ch client (mrun ch client sched t) (sched t)

/-! ## One instant, case by case -/

section StepEqs
variable (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (x : Configuration (n := n) obj × G.State)

theorem mstep_step {p : Fin n} {cmd : Cmd n Op} {r : Nat} {v : (Tagged (n := n) obj).Trace}
    (hl : x.1.localState p = .waiting cmd r v) (ho : G.output x.2 p r v = none) :
    mstep obj G ch client x (some p) = (x.1, G.step x.2 p r v) := by
  simp only [mstep, hl, ho]

theorem mstep_ret {p : Fin n} {cmd : Cmd n Op} {r : Nat} {v : (Tagged (n := n) obj).Trace}
    {o : (Tagged (n := n) obj).Trace × Bool}
    (hl : x.1.localState p = .waiting cmd r v) (ho : G.output x.2 p r v = some o) :
    mstep obj G ch client x (some p) = (Forward.recvStep obj ch x.1 p o, G.leave x.2 p) := by
  simp only [mstep, hl, ho]

theorem mstep_prog {p : Fin n} (hl : helpingRound obj (x.1.localState p) = none) :
    mstep obj G ch client x (some p) =
      (Forward.progStep obj ch x.1 p (client p (x.1.sequence p)), x.2) := by
  cases h : x.1.localState p with
  | waiting cmd r v => rw [h] at hl; simp [helpingRound] at hl
  | _ => simp only [mstep, h]

end StepEqs

/-! ## The run -/

section Run
variable (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))

/-- The round each process is inside a call to at instant `t`. -/
def mwr (t : Nat) (p : Fin n) : Option Nat :=
  helpingRound obj ((mrun obj G ch client sched t).1.localState p)

/-- The proposal each process handed its current call at instant `t`. -/
def mwv (t : Nat) (p : Fin n) : (Tagged (n := n) obj).Trace :=
  Forward.waitProp obj ((mrun obj G ch client sched t).1.localState p)

/-- The machine's state at instant `t`. -/
def mgs (t : Nat) : G.State := (mrun obj G ch client sched t).2

theorem mrun_succ (t : Nat) :
    mrun obj G ch client sched (t + 1) = mstep obj G ch client (mrun obj G ch client sched t) (sched t) :=
  rfl

/-- **Every instant falls in one of four cases.** -/
theorem mrun_cases (t : Nat) :
    (sched t = none ∧ mrun obj G ch client sched (t + 1) = mrun obj G ch client sched t) ∨
    (∃ p cmd r v, sched t = some p ∧
      (mrun obj G ch client sched t).1.localState p = .waiting cmd r v ∧
      G.output (mrun obj G ch client sched t).2 p r v = none ∧
      mrun obj G ch client sched (t + 1) =
        ((mrun obj G ch client sched t).1, G.step (mrun obj G ch client sched t).2 p r v)) ∨
    (∃ p cmd r v o, sched t = some p ∧
      (mrun obj G ch client sched t).1.localState p = .waiting cmd r v ∧
      G.output (mrun obj G ch client sched t).2 p r v = some o ∧
      mrun obj G ch client sched (t + 1) =
        (Forward.recvStep obj ch (mrun obj G ch client sched t).1 p o,
          G.leave (mrun obj G ch client sched t).2 p)) ∨
    (∃ p, sched t = some p ∧ helpingRound obj ((mrun obj G ch client sched t).1.localState p) = none ∧
      mrun obj G ch client sched (t + 1) =
        (Forward.progStep obj ch (mrun obj G ch client sched t).1 p
          (client p ((mrun obj G ch client sched t).1.sequence p)),
          (mrun obj G ch client sched t).2)) := by
  rw [mrun_succ]
  cases hs : sched t with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some p =>
      cases hw : helpingRound obj ((mrun obj G ch client sched t).1.localState p) with
      | none => exact Or.inr (Or.inr (Or.inr ⟨p, rfl, hw, mstep_prog obj G ch client _ hw⟩))
      | some r =>
          obtain ⟨cmd, v, hl⟩ := Forward.waiting_of_round obj hw
          cases ho : G.output (mrun obj G ch client sched t).2 p r v with
          | none =>
              exact Or.inr (Or.inl ⟨p, cmd, r, v, rfl, hl, ho, mstep_step obj G ch client _ hl ho⟩)
          | some o =>
              exact Or.inr (Or.inr (Or.inl
                ⟨p, cmd, r, v, o, rfl, hl, ho, mstep_ret obj G ch client _ hl ho⟩))

theorem good_all : ∀ t, Forward.Good obj (mrun obj G ch client sched t).1 := by
  intro t
  induction t with
  | zero => exact Forward.good_initial obj
  | succ t ih =>
      rcases mrun_cases obj G ch client sched t with
        ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, o, -, hl, -, he⟩ | ⟨p, -, hw, he⟩
      · rw [he]; exact ih
      · rw [he]; exact ih
      · rw [he]; exact Forward.good_recvStep obj ch ih hl _
      · rw [he]; exact Forward.good_progStep obj ch ih _ hw

theorem calls_step (t : Nat) :
    ∀ call ∈ (mrun obj G ch client sched t).1.calls, call ∈ (mrun obj G ch client sched (t + 1)).1.calls := by
  intro call h
  rcases mrun_cases obj G ch client sched t with
    ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, o, -, hl, -, he⟩ | ⟨p, -, hw, he⟩
  · rw [he]; exact h
  · rw [he]; exact h
  · rw [he]; show call ∈ (Forward.recvStep obj ch _ p _).calls; rw [Forward.recvStep_calls]; exact h
  · rw [he]; exact Forward.progStep_calls obj ch _ p _ call h

theorem calls_mono {u t : Nat} (h : u ≤ t) :
    ∀ call ∈ (mrun obj G ch client sched u).1.calls, call ∈ (mrun obj G ch client sched t).1.calls := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact fun call h => h
  | succ d ih => exact fun call h => calls_step obj G ch client sched (u + d) call (ih call h)

/-- Only the scheduled process's local state moves. -/
theorem local_other (t : Nat) {p q : Fin n} (hs : sched t = some p) (hq : q ≠ p) :
    (mrun obj G ch client sched (t + 1)).1.localState q = (mrun obj G ch client sched t).1.localState q := by
  rcases mrun_cases obj G ch client sched t with
    ⟨h0, -⟩ | ⟨p', cmd, r, v, h0, hl, -, he⟩ | ⟨p', cmd, r, v, o, h0, hl, -, he⟩ | ⟨p', h0, hw, he⟩
  · rw [hs] at h0; cases h0
  · rw [he]
  · rw [hs] at h0; obtain rfl := Option.some.inj h0
    rw [he]; exact Forward.recvStep_other obj ch _ p _ hq
  · rw [hs] at h0; obtain rfl := Option.some.inj h0
    rw [he]; exact Forward.progStep_other obj ch _ p _ hq

/-- **The run drives `G`** by the discipline of `GCAMachine.Driven`. -/
theorem driven :
    G.Driven sched (mwr obj G ch client sched) (mwv obj G ch client sched) (mgs obj G ch client sched) := by
  refine ⟨rfl, fun p => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hs
    have he : mrun obj G ch client sched (t + 1) = mrun obj G ch client sched t := by
      rw [mrun_succ, hs]; rfl
    refine ⟨by show (mrun obj G ch client sched (t + 1)).2 = _; rw [he]; rfl, fun q => ⟨?_, ?_⟩⟩
    · show helpingRound obj _ = helpingRound obj _; rw [he]
    · show Forward.waitProp obj _ = Forward.waitProp obj _; rw [he]
  · intro t p q hs hq
    have hl := local_other obj G ch client sched t hs hq
    exact ⟨by show helpingRound obj _ = helpingRound obj _; rw [hl],
      by show Forward.waitProp obj _ = Forward.waitProp obj _; rw [hl]⟩
  · intro t p r hs hw ho
    obtain ⟨cmd, v, hl⟩ := Forward.waiting_of_round obj hw
    have hv : mwv obj G ch client sched t p = v := by
      show Forward.waitProp obj _ = v; rw [hl]; rfl
    rw [hv] at ho
    have he : mrun obj G ch client sched (t + 1) =
        ((mrun obj G ch client sched t).1, G.step (mrun obj G ch client sched t).2 p r v) := by
      rw [mrun_succ, hs]; exact mstep_step obj G ch client _ hl ho
    refine ⟨by show (mrun obj G ch client sched (t + 1)).2 = _; rw [he, hv]; rfl, ?_, ?_⟩
    · show helpingRound obj _ = _; rw [he]; exact hw
    · show Forward.waitProp obj _ = Forward.waitProp obj _; rw [he]
  · intro t p r o hs hw ho
    obtain ⟨cmd, v, hl⟩ := Forward.waiting_of_round obj hw
    have hv : mwv obj G ch client sched t p = v := by
      show Forward.waitProp obj _ = v; rw [hl]; rfl
    rw [hv] at ho
    have he := mstep_ret obj G ch client (mrun obj G ch client sched t) hl ho
    rw [← hs, ← mrun_succ] at he
    refine ⟨by show (mrun obj G ch client sched (t + 1)).2 = _; rw [he]; rfl, ?_⟩
    show helpingRound obj _ = none
    rw [he]
    exact Forward.recvStep_leaves obj ch _ p _ hl
  · intro t p hs hw
    have he := mstep_prog obj G ch client (mrun obj G ch client sched t) hw
    rw [← hs, ← mrun_succ] at he
    refine ⟨by show (mrun obj G ch client sched (t + 1)).2 = _; rw [he]; rfl, ?_⟩
    intro r hr u hu hru
    have hr' : helpingRound obj ((Forward.progStep obj ch (mrun obj G ch client sched t).1 p
        (client p ((mrun obj G ch client sched t).1.sequence p))).localState p) = some r := by
      have : mwr obj G ch client sched (t + 1) p = some r := hr
      unfold mwr at this; rw [he] at this; exact this
    obtain ⟨cmd, seed, commands, hgath, rfl, -, -⟩ := Forward.progStep_enters obj ch _ p _ hw hr'
    obtain ⟨cmd', v', hlu⟩ := Forward.waiting_of_round obj hru
    have hcall := (good_all obj G ch client sched u).wcall p cmd' (seed.round + 1) v' hlu
    have hcall' := calls_mono obj G ch client sched hu _ hcall
    have hb := (good_all obj G ch client sched t).bound p _ hcall' rfl
    rw [hgath] at hb
    dsimp only [Forward.baseRound] at hb
    omega

/-- A new call is made by a program step that enters its round with it. -/
theorem progStep_calls_new (c : Configuration (n := n) obj) (p : Fin n) (op : Op)
    {call : Call (n := n) obj} (h : call ∈ (Forward.progStep obj ch c p op).calls) :
    call ∈ c.calls ∨ (call.process = p ∧
      helpingRound obj ((Forward.progStep obj ch c p op).localState p) = some call.round ∧
      Forward.waitProp obj ((Forward.progStep obj ch c p op).localState p) = call.trace) := by
  cases hc : c.localState p with
  | gathering cmd seed todo commands =>
      cases todo with
      | nil =>
          simp only [Forward.progStep, hc] at h ⊢
          rcases List.mem_cons.mp h with rfl | h
          · right; simp [update, helpingRound, Forward.waitProp]
          · exact Or.inl h
      | cons q todo => left; simpa only [Forward.progStep, hc] using h
  | collecting cmd todo seed => left; cases todo <;> simpa only [Forward.progStep, hc] using h
  | checking cmd seed todo seen =>
      left
      cases todo with
      | cons q todo => simpa only [Forward.progStep, hc] using h
      | nil =>
          simp only [Forward.progStep, hc] at h
          split at h <;> exact h
  | _ => left; simpa only [Forward.progStep, hc] using h

/-- Every recorded call was made by a process that was inside that round, with
that proposal, by then. -/
theorem calls_entered (t : Nat) : ∀ call ∈ (mrun obj G ch client sched t).1.calls,
    ∃ u, u ≤ t ∧ mwr obj G ch client sched u call.process = some call.round ∧
      mwv obj G ch client sched u call.process = call.trace := by
  induction t with
  | zero => intro call h; simp [mrun, HelpingUniversal.initial] at h
  | succ t ih =>
      intro call h
      have old : call ∈ (mrun obj G ch client sched t).1.calls → ∃ u, u ≤ t + 1 ∧
          mwr obj G ch client sched u call.process = some call.round ∧
          mwv obj G ch client sched u call.process = call.trace := fun hc => by
        obtain ⟨u, hu, h1, h2⟩ := ih call hc
        exact ⟨u, by omega, h1, h2⟩
      rcases mrun_cases obj G ch client sched t with
        ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, o, -, hl, -, he⟩ | ⟨p, -, hw, he⟩
      · rw [he] at h; exact old h
      · rw [he] at h; exact old h
      · rw [he] at h
        have h' : call ∈ (Forward.recvStep obj ch (mrun obj G ch client sched t).1 p o).calls := h
        rw [Forward.recvStep_calls] at h'
        exact old h'
      · rw [he] at h
        rcases progStep_calls_new obj ch _ p _ h with hc | ⟨hp, hr, hv⟩
        · exact old hc
        · refine ⟨t + 1, Nat.le_refl _, ?_, ?_⟩
          · show helpingRound obj _ = _; rw [he, hp]; exact hr
          · show Forward.waitProp obj _ = _; rw [he, hp]; exact hv

/-- **A caller inside a call leaves it exactly when it returns**: scheduled, with
its call finished. -/
theorem leave_iff {u : Nat} {q : Fin n} {cmd : Cmd n Op} {r : Nat}
    {prop : (Tagged (n := n) obj).Trace}
    (hl : (mrun obj G ch client sched u).1.localState q = .waiting cmd r prop) :
    (mrun obj G ch client sched (u + 1)).1.localState q ≠ (mrun obj G ch client sched u).1.localState q ↔
      ∃ o, sched u = some q ∧ G.output (mrun obj G ch client sched u).2 q r prop = some o := by
  constructor
  · intro hne
    rcases mrun_cases obj G ch client sched u with
      ⟨-, he⟩ | ⟨p, cmd', r', v, hs, hl', -, he⟩ | ⟨p, cmd', r', v, o, hs, hl', ho, he⟩ |
        ⟨p, hs, hw, he⟩
    · exact absurd (by rw [he]) hne
    · exact absurd (by rw [he]) hne
    · by_cases hpq : q = p
      · subst hpq
        rw [hl] at hl'
        obtain ⟨-, rfl, rfl⟩ : cmd = cmd' ∧ r = r' ∧ prop = v := by
          simp only [Local.waiting.injEq] at hl'; exact hl'
        exact ⟨o, hs, ho⟩
      · exact absurd (local_other obj G ch client sched u hs hpq) hne
    · by_cases hpq : q = p
      · subst hpq; rw [hl] at hw; simp [helpingRound] at hw
      · exact absurd (local_other obj G ch client sched u hs hpq) hne
  · rintro ⟨o, hs, ho⟩ heq
    have he := mstep_ret obj G ch client (mrun obj G ch client sched u) hl ho
    rw [← hs, ← mrun_succ] at he
    have hleft : helpingRound obj ((mrun obj G ch client sched (u + 1)).1.localState q) = none := by
      rw [he]; exact Forward.recvStep_leaves obj ch (mrun obj G ch client sched u).1 q o hl
    rw [heq, hl] at hleft
    simp [helpingRound] at hleft

/-- A process's local state is constant while it is not scheduled. -/
theorem local_const {p : Fin n} {a : Nat} :
    ∀ d, (∀ w, a ≤ w → w < a + d → sched w ≠ some p) →
      (mrun obj G ch client sched (a + d)).1.localState p = (mrun obj G ch client sched a).1.localState p := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
      intro hno
      rw [show a + (d + 1) = (a + d) + 1 from by omega]
      have hih := ih (fun w hw hwd => hno w hw (by omega))
      cases hs : sched (a + d) with
      | none =>
          rw [show mrun obj G ch client sched (a + d + 1) = mrun obj G ch client sched (a + d) by
            rw [mrun_succ, hs]; rfl]
          exact hih
      | some q =>
          have hq : p ≠ q := fun h => hno (a + d) (by omega) (by omega) (h ▸ hs)
          rw [local_other obj G ch client sched (a + d) hs hq]
          exact hih

end Run

/-! ## The run is a run of Algorithm 3 over the GCA histories it produces -/

section Refinement
variable (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))

/-- **The GCA histories of the run**: round `r`'s is the history of round `r` in
the run of `G`. -/
noncomputable def env : WeakUniversal.Environment (n := n) obj := fun r =>
  G.history sched (mwr obj G ch client sched) (mwv obj G ch client sched) (mgs obj G ch client sched) r

theorem env_input_of_waiting {t : Nat} {p : Fin n} {r : Nat}
    (hw : mwr obj G ch client sched t p = some r) :
    (env obj G ch client sched r).input p = some (mwv obj G ch client sched t p) :=
  (driven obj G ch client sched).history_input hw

/-- **A program step outside a call is a step of `HelpingUniversal.Step`** for
the run's histories. -/
theorem prog_valid (t : Nat) {p : Fin n} (hs : sched t = some p)
    (hw : helpingRound obj ((mrun obj G ch client sched t).1.localState p) = none) :
    Step obj (env obj G ch client sched) (mrun obj G ch client sched t).1
      (mrun obj G ch client sched (t + 1)).1 := by
  have he := mstep_prog obj G ch client (mrun obj G ch client sched t) hw
  rw [← hs, ← mrun_succ] at he
  have hinput : ∀ cmd seed commands,
      (mrun obj G ch client sched t).1.localState p = .gathering cmd seed [] commands →
      (env obj G ch client sched (seed.round + 1)).input p
        = some (proposal obj seed (ch.arrange (mrun obj G ch client sched t).1 p commands)) := by
    intro cmd seed commands hg
    have hloc : (mrun obj G ch client sched (t + 1)).1.localState p = .waiting cmd (seed.round + 1)
        (proposal obj seed (ch.arrange (mrun obj G ch client sched t).1 p commands)) := by
      rw [he]; simp [Forward.progStep, hg, update]
    have hwr : mwr obj G ch client sched (t + 1) p = some (seed.round + 1) := by
      show helpingRound obj _ = _; rw [hloc]; rfl
    have hwv : mwv obj G ch client sched (t + 1) p
        = proposal obj seed (ch.arrange (mrun obj G ch client sched t).1 p commands) := by
      show Forward.waitProp obj _ = _; rw [hloc]; rfl
    rw [env_input_of_waiting obj G ch client sched hwr, hwv]
  rw [he]
  unfold Forward.progStep
  cases h : (mrun obj G ch client sched t).1.localState p with
  | idle seed => exact Step.invoke _ p _ seed h
  | announcing cmd seed => exact Step.announce _ p cmd seed h _ (ch.slotOrder_perm _ p)
  | collecting cmd todo seed =>
      cases todo with
      | nil => exact Step.collectedStart _ p cmd seed h _ (ch.announcementOrder_perm _ p)
      | cons q todo => exact Step.readStart _ p q cmd todo seed h
  | gathering cmd seed todo commands =>
      cases todo with
      | nil =>
          exact Step.propose _ p cmd seed commands h _ (ch.arrange_perm _ p commands)
            (hinput cmd seed commands h)
      | cons q todo => exact Step.readAnnouncement _ p q cmd seed todo commands h
  | waiting cmd r v => rw [h] at hw; simp [helpingRound] at hw
  | publishing cmd seed => exact Step.publish _ p cmd seed h _ (ch.slotOrder_perm _ p)
  | checking cmd seed todo seen =>
      cases todo with
      | cons q todo => exact Step.readCheck _ p q cmd seed todo seen h
      | nil =>
          dsimp only
          by_cases hc : (Tagged obj).traceCount cmd seen.trace = 0
          · rw [ite_eq_left hc]; exact Step.retry _ p cmd seed seen h hc _ (ch.announcementOrder_perm _ p)
          · rw [ite_eq_right hc]; exact Step.finish _ p cmd seed seen h (Nat.pos_of_ne_zero hc)

/-- **Returning is a step of `HelpingUniversal.Step`** for the run's histories. -/
theorem recv_valid (t : Nat) {p : Fin n} {cmd : Cmd n Op} {r : Nat}
    {v : (Tagged (n := n) obj).Trace} {o : (Tagged (n := n) obj).Trace × Bool}
    (hs : sched t = some p) (hl : (mrun obj G ch client sched t).1.localState p = .waiting cmd r v)
    (ho : G.output (mrun obj G ch client sched t).2 p r v = some o) :
    Step obj (env obj G ch client sched) (mrun obj G ch client sched t).1
      (mrun obj G ch client sched (t + 1)).1 := by
  have he := mstep_ret obj G ch client (mrun obj G ch client sched t) hl ho
  rw [← hs, ← mrun_succ] at he
  have hwr : mwr obj G ch client sched t p = some r := by show helpingRound obj _ = _; rw [hl]; rfl
  have hwv : mwv obj G ch client sched t p = v := by show Forward.waitProp obj _ = _; rw [hl]; rfl
  have hout : (env obj G ch client sched r).output p = some o :=
    (driven obj G ch client sched).history_output ⟨t, hs, hwr, by rw [hwv]; exact ho⟩
  rw [he]
  have hstep := Step.receive (H := env obj G ch client sched)
    (mrun obj G ch client sched t).1 p cmd r v o.1 o.2 hl hout
    _ (ch.slotOrder_perm (mrun obj G ch client sched t).1 p)
  unfold Forward.recvStep
  rw [hl]
  exact hstep

/-- The program run, as an execution of `HelpingUniversal.Step`. -/
noncomputable def mexec : HelpingUniversal.Execution obj (env obj G ch client sched) where
  state := fun t => (mrun obj G ch client sched t).1
  initial_state := rfl
  next := by
    intro t
    rcases mrun_cases obj G ch client sched t with
      ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, o, hs, hl, ho, -⟩ | ⟨p, hs, hw, -⟩
    · exact Or.inl (by show (mrun obj G ch client sched (t + 1)).1 = _; rw [he])
    · exact Or.inl (by show (mrun obj G ch client sched (t + 1)).1 = _; rw [he])
    · exact Or.inr (recv_valid obj G ch client sched t hs hl ho)
    · exact Or.inr (prog_valid obj G ch client sched t hs hw)

/-- **The run is a run of Algorithm 3 over its GCA histories**, with one global
schedule. -/
noncomputable def helpingRun : GlobalSchedule.HelpingRun obj (env obj G ch client sched) where
  run := mexec obj G ch client sched
  actor := sched
  step_actor := by
    intro t
    rcases mrun_cases obj G ch client sched t with
      ⟨hs, he⟩ | ⟨p, cmd, r, v, hs, hl, -, he⟩ | ⟨p, cmd, r, v, o, hs, hl, ho, -⟩ | ⟨p, hs, hw, he⟩
    · exact Or.inl ⟨hs, by show (mrun obj G ch client sched (t + 1)).1 = _; rw [he]; rfl⟩
    · refine Or.inr (Or.inr ⟨p, r, hs, ?_, ?_⟩)
      · show helpingRound obj ((mrun obj G ch client sched t).1.localState p) = some r
        rw [hl]; rfl
      · show (mrun obj G ch client sched (t + 1)).1 = _; rw [he]; rfl
    · exact Or.inr (Or.inl ⟨p, hs, recv_valid obj G ch client sched t hs hl ho,
        fun q hq => local_other obj G ch client sched t hs hq⟩)
    · exact Or.inr (Or.inl ⟨p, hs, prog_valid obj G ch client sched t hs hw,
        fun q hq => local_other obj G ch client sched t hs hq⟩)
  no_ghost := by
    intro r p s hi
    obtain ⟨t, hw, -⟩ := entered_of_history_input hi
    obtain ⟨cmd, v, hl⟩ := Forward.waiting_of_round obj hw
    exact ⟨t, v, (good_all obj G ch client sched t).wcall p cmd (r + 1) v hl⟩

theorem helpingRun_state (t : Nat) :
    (helpingRun obj G ch client sched).run.state t = (mrun obj G ch client sched t).1 := rfl

theorem helpingRun_actor : (helpingRun obj G ch client sched).actor = sched := rfl

/-! ## Its GCA objects meet the interface -/

/-- **Every prefix history of the run is a history of a run of `G`**: that of the
run cut at the prefix's end. -/
theorem prefixHistory_eq (r T : Nat) :
    (helpingRun obj G ch client sched).run.prefixHistory obj r T =
      G.history (cutAct sched T) (cut (mwr obj G ch client sched) T) (cut (mwv obj G ch client sched) T)
        (cut (mgs obj G ch client sched) T) r := by
  classical
  have hd := driven obj G ch client sched
  refine GCA.History.eq_of_input_output (funext fun q => ?_) (funext fun q => ?_)
  · show @ite _ (∃ call ∈ (mrun obj G ch client sched T).1.calls, call.round = r ∧ call.process = q)
      (Classical.propDecidable _) ((env obj G ch client sched r).input q) none = _
    by_cases hc : ∃ call ∈ (mrun obj G ch client sched T).1.calls, call.round = r ∧ call.process = q
    · rw [ite_eq_left hc]
      obtain ⟨call, hcall, hround, hproc⟩ := hc
      obtain ⟨u, hu, hw, hv⟩ := calls_entered obj G ch client sched T call hcall
      rw [hround, hproc] at hw
      rw [hproc] at hv
      rw [env_input_of_waiting obj G ch client sched hw]
      exact ((history_cut_input hd T r q _).mpr ⟨u, hu, hw, rfl⟩).symm
    · rw [ite_eq_right hc]
      cases hcut : (G.history (cutAct sched T) (cut (mwr obj G ch client sched) T)
          (cut (mwv obj G ch client sched) T) (cut (mgs obj G ch client sched) T) r).input q with
      | none => rfl
      | some s =>
          obtain ⟨u, hu, hw, -⟩ := (history_cut_input hd T r q s).mp hcut
          obtain ⟨cmd, v, hl⟩ := Forward.waiting_of_round obj hw
          exact absurd ⟨_, calls_mono obj G ch client sched hu _
            ((good_all obj G ch client sched u).wcall q cmd r v hl), rfl, rfl⟩ hc
  · show @ite _ (∃ u, u < T ∧ ∃ cmd prop, (mrun obj G ch client sched u).1.localState q =
        .waiting cmd r prop ∧ (mrun obj G ch client sched (u + 1)).1.localState q ≠
          (mrun obj G ch client sched u).1.localState q)
      (Classical.propDecidable _) ((env obj G ch client sched r).output q) none = _
    by_cases hc : ∃ u, u < T ∧ ∃ cmd prop, (mrun obj G ch client sched u).1.localState q =
        .waiting cmd r prop ∧ (mrun obj G ch client sched (u + 1)).1.localState q ≠
          (mrun obj G ch client sched u).1.localState q
    · rw [ite_eq_left hc]
      obtain ⟨u, hu, cmd, prop, hl, hne⟩ := hc
      obtain ⟨o, hs, ho⟩ := (leave_iff obj G ch client sched hl).mp hne
      have hwr : mwr obj G ch client sched u q = some r := by
        show helpingRound obj _ = _; rw [hl]; rfl
      have hwv : mwv obj G ch client sched u q = prop := by
        show Forward.waitProp obj _ = _; rw [hl]; rfl
      rw [← hwv] at ho
      have h1 : (env obj G ch client sched r).output q = some o := hd.history_output ⟨u, hs, hwr, ho⟩
      rw [h1]
      exact ((hd.cut T).history_output ((returned_cut_iff T r q o).mpr ⟨u, hu, hs, hwr, ho⟩)).symm
    · rw [ite_eq_right hc]
      cases hcut : (G.history (cutAct sched T) (cut (mwr obj G ch client sched) T)
          (cut (mwv obj G ch client sched) T) (cut (mgs obj G ch client sched) T) r).output q with
      | none => rfl
      | some o =>
          obtain ⟨u, hu, hs, hw, ho⟩ := (returned_cut_iff T r q o).mp
            (returned_of_history_output hcut)
          obtain ⟨cmd, v, hl⟩ := Forward.waiting_of_round obj hw
          have hwv : mwv obj G ch client sched u q = v := by
            show Forward.waitProp obj _ = _; rw [hl]; rfl
          rw [hwv] at ho
          exact absurd ⟨u, hu, cmd, v, hl, (leave_iff obj G ch client sched hl).mpr ⟨o, hs, ho⟩⟩ hc

/-- **The GCA objects of every run of Algorithm 3 over `G` meet the interface**,
when `G` meets the specification. -/
theorem gcaInterface (hG : G.IsGCA) : (helpingRun obj G ch client sched).GCAInterface :=
  (helpingRun obj G ch client sched).gcaInterface_of_prefixSpec
    (fun r p o ho => by
      obtain ⟨t, hs, hw, ho'⟩ := returned_of_history_output ho
      obtain ⟨cmd, v, hl⟩ := Forward.waiting_of_round obj hw
      have hwv : mwv obj G ch client sched t p = v := by
        show Forward.waitProp obj _ = _; rw [hl]; rfl
      rw [hwv] at ho'
      exact ⟨t, cmd, v, hl, (leave_iff obj G ch client sched hl).mpr ⟨o, hs, ho'⟩⟩)
    (fun r T => by
      rw [prefixHistory_eq]
      exact hG.spec _ _ _ _ ((driven obj G ch client sched).cut T) r)
    (fun p cmd r proposal N hN => hG.returns _ _ _ _ (driven obj G ch client sched) p r N
      (fun t ht => by
        have h := hN t ht
        show helpingRound obj ((mrun obj G ch client sched t).1.localState p) = some r
        rw [show (mrun obj G ch client sched t).1.localState p = .waiting cmd r proposal from h]
        rfl))

/-- **Algorithm 3 over `G`, as a run over GCA objects meeting the interface.** -/
noncomputable def toGCA (hG : G.IsGCA) : GlobalSchedule.HelpingGCA obj (env obj G ch client sched) where
  toHelpingRun := helpingRun obj G ch client sched
  gca := gcaInterface obj G ch client sched hG

@[simp] theorem toGCA_toHelpingRun (hG : G.IsGCA) :
    (toGCA obj G ch client sched hG).toHelpingRun = helpingRun obj G ch client sched := rfl

/-! ## Executions -/

omit [DecidableEq Op] in
theorem command_none {l : Local (n := n) obj} (h : l.command obj = none) : ∃ seed, l = .idle seed := by
  cases l with
  | idle seed => exact ⟨seed, rfl⟩
  | _ => cases h

/-- A scheduler that does not halt gives an operation-live run. -/
theorem opLive (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome) :
    (helpingRun obj G ch client sched).OpLive := by
  obtain ⟨p, hp⟩ := WeakUniversal.Forward.often_some hlive
  have hopActor : ∀ t, sched (t + 1) = some p →
      ((mrun obj G ch client sched (t + 1)).1.localState p).command obj ≠ none →
      ((helpingRun obj G ch client sched).opActor t).isSome = true := by
    intro t hs hc
    show (match sched (t + 1) with
      | none => none
      | some q => (HelpingUniversal.ledger obj (mrun obj G ch client sched (t + 1)).1).active q).isSome
        = true
    rw [hs]
    show (((mrun obj G ch client sched (t + 1)).1.localState p).command obj).isSome = true
    cases h : ((mrun obj G ch client sched (t + 1)).1.localState p).command obj with
    | none => exact absurd h hc
    | some _ => rfl
  intro N
  obtain ⟨t₁, ⟨ht₁, hs₁⟩, -⟩ := exists_least (fun w => N + 1 ≤ w ∧ sched w = some p) (hp (N + 1))
  obtain ⟨t, rfl⟩ : ∃ t, t₁ = t + 1 := ⟨t₁ - 1, by omega⟩
  by_cases hc : ((mrun obj G ch client sched (t + 1)).1.localState p).command obj = none
  · -- idle and scheduled: it invokes, and holds the command until it is next scheduled
    obtain ⟨seed, hidle⟩ := command_none obj hc
    obtain ⟨t₂, ⟨ht₂, hs₂⟩, hmin⟩ :=
      exists_least (fun w => t + 2 ≤ w ∧ sched w = some p) (hp (t + 2))
    have hinv : ((mrun obj G ch client sched (t + 2)).1.localState p).command obj ≠ none := by
      have hw : helpingRound obj ((mrun obj G ch client sched (t + 1)).1.localState p) = none := by
        rw [hidle]; rfl
      have he := mstep_prog obj G ch client (mrun obj G ch client sched (t + 1)) hw
      rw [← hs₁, ← mrun_succ] at he
      rw [he]
      simp [Forward.progStep, hidle, update, Local.command]
    have hconst := local_const obj G ch client sched (a := t + 2) (p := p) (t₂ - (t + 2))
      (fun w hw hwd hsw => absurd (hmin w ⟨hw, hsw⟩) (by omega))
    rw [show t + 2 + (t₂ - (t + 2)) = t₂ from by omega] at hconst
    obtain ⟨t₃, rfl⟩ : ∃ t₃, t₂ = t₃ + 1 := ⟨t₂ - 1, by omega⟩
    exact ⟨t₃, by omega, hopActor t₃ hs₂ (by rw [hconst]; exact hinv)⟩
  · exact ⟨t, by omega, hopActor t hs₁ hc⟩

/-- The §3 execution of a non-halting run of Algorithm 3 over `G`. -/
noncomputable def execution (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome) :
    _root_.ConflictFreedom.Execution n Op :=
  (helpingRun obj G ch client sched).execution (opLive obj G ch client sched hlive)

/-- **Linearizability**, of every run of Algorithm 3 over `G`, halting or not. -/
theorem infinite_event_linearization (hG : G.IsGCA) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, ((helpingRun obj G ch client sched).run.history obj).returned k a v → v = resp a) ∧
      (∀ a, ((((helpingRun obj G ch client sched).run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, ((helpingRun obj G ch client sched).run.history obj).invoked N a)) ∧
      (∀ a v, ((((helpingRun obj G ch client sched).run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, ((helpingRun obj G ch client sched).run.history obj).returned N a v)) ∧
      (((helpingRun obj G ch client sched).run.ledgerRun obj).events resp).WellFormed
        Command.process ∧
      (Tagged obj).InfEventLinearizable Command.process
        (((helpingRun obj G ch client sched).run.ledgerRun obj).events resp) :=
  (toGCA obj G ch client sched hG).infinite_event_linearization

end Refinement

/-! ## Theorem `th:cr` over `G` -/

/-- The run's first `N` steps are determined by the scheduler's first `N`
choices. -/
theorem mrun_congr {ch : Forward.Choices (n := n) obj} {client : Fin n → Nat → Op} {s₁ s₂ : Nat → Option (Fin n)} {N : Nat}
    (h : ∀ t, t < N → s₁ t = s₂ t) :
    ∀ t, t ≤ N → mrun obj G ch client s₁ t = mrun obj G ch client s₂ t
  | 0, _ => rfl
  | t + 1, ht => by
      rw [mrun_succ, mrun_succ, mrun_congr h t (by omega), h t (by omega)]

/-- **An extension of a finite execution**, over `G`: the run of `ch'`, `client'`
and `sched'` takes the same first `N` steps as `mrun G ch client sched`; after
them the client, and the rule for the collect orders and `trace(M_i)`, may
differ. -/
def Extends (ch' : Forward.Choices (n := n) obj) (client' : Fin n → Nat → Op) (sched' : Nat → Option (Fin n))
    (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) : Prop :=
  (∀ t, t < N → sched' t = sched t) ∧
    ∀ t, t ≤ N → mrun obj G ch' client' sched' t = mrun obj G ch client sched t

/-- The instance with command `a` is **invoked by time `t`** in the run over
`G`, at the invocation point `ip`.  At Line 5 (`ip = .announce`): `a` has been
written into `M[a.process]` within the first `t` steps. -/
def InvokedBy (ip : InvocationPoint (n := n) obj)
    (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (t : Nat) (a : Cmd n Op) : Prop :=
  HelpingUniversal.InvokedBy ip (fun t => (mrun obj G ch client sched t).1) t a

/-- Pending at time `t`, at the invocation point `ip`: invoked, and not yet
answered. -/
def PendingAt (ip : InvocationPoint (n := n) obj)
    (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (t : Nat) (a : Cmd n Op) : Prop :=
  HelpingUniversal.PendingAt ip (fun t => (mrun obj G ch client sched t).1) t a

/-- **Eventually `α`-conflict-free**, at the invocation point `ip`, for the
finite execution `α` of the first `N` steps: a suffix in which no two concurrent
operation instances invoked after `α` conflict, "pending" and "invoked after `α`"
read at the point `ip`. -/
def EventuallyConflictFreeAfter (ip : InvocationPoint (n := n) obj)
    (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) : Prop :=
  HelpingUniversal.EventuallyConflictFreeAfter ip (fun t => (mrun obj G ch client sched t).1) N

/-- **Definition `def:wcr`, conflict-resolving execution, over `G`, at the
invocation point `ip`.**  The finite execution `α` (the first `N` steps of
`mrun G client sched`) is conflict-resolving if in every eventually
`α`-conflict-free infinite extension of `α` over `G`, every correct process
completes each of its operations. -/
def ConflictResolving (ip : InvocationPoint (n := n) obj)
    (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) : Prop :=
  ∀ (ch' : Forward.Choices (n := n) obj) (client' : Fin n → Nat → Op) (sched' : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched' t).isSome),
    Extends obj G ch' client' sched' ch client sched N →
    EventuallyConflictFreeAfter obj G ip ch' client' sched' N →
    ∀ j, (execution obj G ch' client' sched' hlive).Correct
        ((execution obj G ch' client' sched' hlive).owner j) →
      (execution obj G ch' client' sched' hlive).Completes j

open WeakUniversal.Forward (soloSched soloSched_before soloSched_after) in
/-- **Theorem `th:cr`, over any GCA implementation meeting the specification.**
For every finite execution `α` of Algorithm 3 over `G` — the first `N` steps of
its run for any client and any scheduler — and every process `i`, there is a
finite conflict-resolving `i`-solo extension of `α`: the first `N'` steps of the
run that follows `α` and then schedules only `i`.  The invocation point is Line
5, the write of the command into `M` (`InvocationPoint.announce`). -/
theorem conflictResolution (hG : G.IsGCA)
    (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj G ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictResolving obj G .announce ch client (soloSched sched N i) N' := by
  obtain ⟨N', hNN', hcr⟩ := (toGCA obj G ch client (soloSched sched N i) hG).conflictResolution
    (FiniteScheduling.SoloFrom.of_continuous _ fun _ ht => soloSched_after ht)
  refine ⟨N', hNN', ⟨fun t ht => soloSched_before ht,
      mrun_congr obj G (fun t ht => soloSched_before ht)⟩,
    fun t ht _ => soloSched_after ht, ?_⟩
  intro ch' client' sched' hlive hext hcf
  exact hcr _ (toGCA obj G ch' client' sched' hG) (opLive obj G ch' client' sched' hlive)
    ⟨fun t ht => hext.1 t ht, fun t ht => congrArg Prod.fst (hext.2 t ht)⟩ hcf

/-! ## The definitions, checked -/

/-- **The invocation point at Line 5, in §3's vocabulary**, over any `G`: an
instance is invoked after `α` at Line 5 exactly when it takes no operation step
within `α` — its first operation step is its write into `M`, Lines 1–4 being
local. -/
theorem invokedAfter_iff (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome)
    (j : (execution obj G ch client sched hlive).Instance) (N : Nat) :
    ¬ InvokedBy obj G .announce ch client sched N j.val ↔
      ∀ t, (execution obj G ch client sched hlive).actor t = some j → N - 1 ≤ t := by
  have h := (helpingRun obj G ch client sched).announcedBy_iff_step
    (opLive obj G ch client sched hlive) j N
  constructor
  · intro hnot t hact
    apply Nat.le_of_not_lt
    intro hlt
    exact hnot (h.mpr ⟨t, by omega, hact⟩)
  · intro hall hinv
    obtain ⟨t, ht, hact⟩ := h.mp hinv
    have := hall t hact
    omega

/-- **The hypothesis is implied by §3's eventual conflict-freedom**, over any
`G`, at every invocation point in the operation's code — Line 5 included. -/
theorem eventuallyConflictFreeAfter_of_eventuallyConflictFree
    {ip : InvocationPoint (n := n) obj} (hip : ip.InCode)
    (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome) (N : Nat)
    (h : (execution obj G ch client sched hlive).EventuallyConflictFree obj.Conflict) :
    EventuallyConflictFreeAfter obj G ip ch client sched N :=
  (helpingRun obj G ch client sched).eventuallyConflictFreeAfter_of_eventuallyConflictFree hip
    (opLive obj G ch client sched hlive) N h

/-! ## The definitions are not vacuous -/

open WeakUniversal.Forward (soloSched soloSched_after) in
/-- In the solo continuation, every instance invoked after `N' ≥ N` is `i`'s,
and two of `i`'s instances are never pending at once, so the continuation is
eventually conflict-free after every such prefix. -/
theorem soloSched_conflictFreeAfter (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) {N' : Nat} (hN : N ≤ N') :
    EventuallyConflictFreeAfter obj G .announce ch client (soloSched sched N i) N' := by
  let g := helpingRun obj G ch client (soloSched sched N i)
  have hsolo : g.SoloFrom N i :=
    FiniteScheduling.SoloFrom.of_continuous _ fun _ ht => soloSched_after ht
  have own : ∀ t c, InvokedBy obj G .announce ch client (soloSched sched N i) t c →
      ¬ InvokedBy obj G .announce ch client (soloSched sched N i) N' c → c.process = i := by
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
theorem extends_refl (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) :
    Extends obj G ch client sched ch client sched N :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

open WeakUniversal.Forward (soloSched soloSched_live) in
/-- **`ConflictResolving` is not vacuous**, over any `G`: the solo continuation
is an extension meeting its hypothesis. -/
theorem conflictResolving_hypothesis_satisfiable (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) {N' : Nat} (hN : N ≤ N') :
    (∀ M, ∃ t, M ≤ t ∧ (soloSched sched N i t).isSome) ∧
      Extends obj G ch client (soloSched sched N i) ch client (soloSched sched N i) N' ∧
      EventuallyConflictFreeAfter obj G .announce ch client (soloSched sched N i) N' :=
  ⟨soloSched_live sched N i, extends_refl obj G ch client _ N',
    soloSched_conflictFreeAfter obj G ch client sched N i hN⟩

/-! ## Algorithm 2 is an instance -/

/-- **Algorithm 3 over Algorithm 2 is the forward machine**: run over
`ForwardGCA.machine`, it is `HelpingUniversal.Forward.frun`. -/
theorem mrun_machine (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) :
    mrun obj (ForwardGCA.machine (Tagged (n := n) obj) n) ch client sched =
      Forward.frun obj ch client sched := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [mrun_succ, Forward.frun_succ, ih]
      cases sched t with
      | none => rfl
      | some p =>
          cases hl : (Forward.frun obj ch client sched t).1.localState p with
          | waiting cmd r v =>
              by_cases hph : ((Forward.frun obj ch client sched t).2.frame p).phase < 6
              · rw [Forward.fstep_gca obj ch client _ hl hph]
                exact mstep_step obj _ ch client _ hl (ite_eq_left hph)
              · rw [Forward.fstep_recv obj ch client _ hl hph]
                exact mstep_ret obj _ ch client _ hl (ite_eq_right hph)
          | _ =>
              rw [Forward.fstep_prog obj ch client _ (by rw [hl]; rfl)]
              exact mstep_prog obj _ ch client _ (by rw [hl]; rfl)

open WeakUniversal.Forward (soloSched) in
/-- **Theorem `th:cr` for Algorithm 3 over Algorithm 2**, as an instance of the
modular theorem: Algorithm 2 meets the specification, and Algorithm 3 over it is
the forward machine (`mrun_machine`). -/
theorem conflictResolution_algorithm2 (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj (ForwardGCA.machine (Tagged (n := n) obj) n) ch client (soloSched sched N i)
        ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictResolving obj (ForwardGCA.machine (Tagged (n := n) obj) n) .announce ch client
        (soloSched sched N i) N' :=
  conflictResolution obj _ ForwardGCA.machine_isGCA ch client sched N i

end ConflictFreedom.HelpingUniversal.Over

namespace ConflictFreedom
open HelpingUniversal.Over
variable {State Op Response : Type} [DecidableEq Op]

/-- **Algorithm 3 over a GCA implementation `G`, as a §3 implementation**: the
executions of every non-halting run, for every rule for the collect orders and
`trace(M_i)`, every client and every scheduler. -/
def algorithm3Over (obj : Object State Op Response) {n : Nat}
    (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n) : Implementation n Op := fun e =>
  ∃ (ch : HelpingUniversal.Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome), e = execution obj G ch client sched hlive

/-- **Over an implementation meeting the GCA specification, every execution is
one of Algorithm 3 over a GCA meeting the interface.** -/
theorem algorithm3Over_anyGCA (obj : Object State Op Response) {n : Nat}
    (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n) (hG : G.IsGCA) :
    ∀ e, algorithm3Over obj G e → algorithm3AnyGCA obj n e := by
  rintro e ⟨ch, client, sched, hlive, rfl⟩
  exact ⟨_, toGCA obj G ch client sched hG, opLive obj G ch client sched hlive, rfl⟩

/-- **Lemma `lemma:UCV2isCF` over any GCA implementation meeting the
specification**: Algorithm 3 over it is conflict-free. -/
theorem algorithm3Over_conflictFree (obj : Object State Op Response) {n : Nat}
    (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n) (hG : G.IsGCA) :
    ConflictFree (algorithm3Over obj G) obj.Conflict := fun e he =>
  algorithm3AnyGCA_conflictFree obj n e (algorithm3Over_anyGCA obj G hG e he)

/-- The admitted set is not empty, for any `G`, at every process count
`n = m + 1`: any client, with one process scheduled for ever. -/
theorem algorithm3Over_nonempty (obj : Object State Op Response) (op : Op) (m : Nat)
    (G : GCAMachine (WeakUniversal.Tagged (n := m + 1) obj) (m + 1)) :
    ∃ e, algorithm3Over obj G e :=
  ⟨_, HelpingUniversal.Forward.Choices.inOrder obj, fun _ _ => op, fun _ => some 0,
    fun N => ⟨N, Nat.le_refl _, rfl⟩, rfl⟩

open WeakUniversal.Forward (soloSched) in
/-- **Theorem `th:cr`, for Algorithm 3 over any GCA implementation meeting the
specification of §4.2** (the same statement as
`HelpingUniversal.Over.conflictResolution`). -/
theorem algorithm3Over_conflictResolution (obj : Object State Op Response) {n : Nat}
    (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n) (hG : G.IsGCA)
    (ch : HelpingUniversal.Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj G ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictResolving obj G .announce ch client (soloSched sched N i) N' :=
  conflictResolution obj G hG ch client sched N i

end ConflictFreedom
