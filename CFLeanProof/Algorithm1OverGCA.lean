import CFLeanProof.GCAMachineAlgorithm2
import CFLeanProof.WeakUCResolve

/-!
# Algorithm 1 over any GCA implementation, and Theorem `th:WeakUCresolve`

> **Theorem (`th:WeakUCresolve`).**  For every finite execution `α` of
> Algorithm 1 and every process `i`, there is a finite conflict-forgetting
> `i`-solo extension of `α`.
>
> (§7: "the GCA objects used by Algorithm 1 are assumed to satisfy [Solo
> Agreement]".)

The theorem is about finite executions and the extensions they **have**, so the
GCA objects must be something that runs: an implementation `G : GCAMachine`
(`GCAMachine.lean`).  Nothing about `G` is assumed beyond the GCA specification
of §4.2 (`GCAMachine.IsGCA`: the six properties in every run, and every correct
participant returns) and Solo agreement (`GCAMachine.SoloAgreement`).

* `mrun G ch client sched` is Algorithm 1 run over `G`: at each instant the
  scheduled process takes a step of its GCA call — or returns from it once `G`
  says it has finished — or, outside a call, a step of Algorithm 1
  (`WeakUniversal.Forward.progStep`, literally the constructors of
  `WeakUniversal.Step`).
* Every run is a run of Algorithm 1 over the GCA histories it produces
  (`weakRun`), whose objects meet `GlobalSchedule.WeakRun.GCAInterface`
  (`gcaInterface`) and Solo agreement (`soloAgreement`): the run's histories,
  and those of its every prefix, are histories of runs of `G`
  (`prefixHistory_eq`), so the specification applies to them.  So every theorem
  proved over the interface holds for Algorithm 1 over `G`
  (`algorithm1Over_anyGCA`, `algorithm1Over_weakConflictFree`,
  `infinite_event_linearization`).
* `weakUCresolve` is the theorem, for every `G` meeting the specification and
  Solo agreement: the solo extension is the run that follows `α` and then
  schedules only `i` (`WeakUniversal.Forward.soloSched`); its prefix is
  conflict-forgetting among all extensions **over the same `G`**
  (`ConflictForgetting`).  The proof is `GlobalSchedule.WeakGCA.weakUCresolve`,
  which uses only the interface and Solo agreement.

**Algorithm 2 is an instance.**  `ForwardGCA.machine` meets both requirements
(`machine_isGCA`, `machine_soloAgreement`), and Algorithm 1 over it is exactly
the forward machine of `ForwardUniversal` (`mrun_machine`), so
`weakUCresolve_algorithm2` is `th:WeakUCresolve` for the composition, with no
hypothesis.
-/

namespace ConflictFreedom.WeakUniversal.Over
open Object UniversalProtocol GCAMachine
open GlobalSchedule (weakRound)

variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op] (G : GCAMachine (Tagged (n := n) obj) n)

/-- **One instant of Algorithm 1 over the GCA machine `G`.**  An idle tick
changes nothing; a caller whose call has not finished takes a step of it; a
caller whose call has finished consumes the output and returns; anybody else
takes its program step. -/
def mstep (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (x : Configuration (n := n) obj × G.State) :
    Option (Fin n) → Configuration (n := n) obj × G.State
  | none => x
  | some p =>
      match x.1.localState p with
      | .waiting _ r v =>
          match G.output x.2 p r v with
          | none => (x.1, G.step x.2 p r v)
          | some o => (Forward.recvStep obj x.1 p o, G.leave x.2 p)
      | _ => (Forward.progStep obj ch x.1 p (client p (x.1.sequence p)), x.2)

/-- **The run of Algorithm 1 over `G`** for a rule `ch` for the collect order, a
client and a scheduler. -/
def mrun (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) :
    Nat → Configuration (n := n) obj × G.State
  | 0 => (WeakUniversal.initial obj, G.init)
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
    mstep obj G ch client x (some p) = (Forward.recvStep obj x.1 p o, G.leave x.2 p) := by
  simp only [mstep, hl, ho]

theorem mstep_prog {p : Fin n} (hl : weakRound obj (x.1.localState p) = none) :
    mstep obj G ch client x (some p) =
      (Forward.progStep obj ch x.1 p (client p (x.1.sequence p)), x.2) := by
  cases h : x.1.localState p with
  | waiting cmd r v => rw [h] at hl; simp [weakRound] at hl
  | _ => simp only [mstep, h]

end StepEqs

/-! ## The run -/

section Run
variable (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))

/-- The round each process is inside a call to at instant `t`. -/
def mwr (t : Nat) (p : Fin n) : Option Nat :=
  weakRound obj ((mrun obj G ch client sched t).1.localState p)

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
        (Forward.recvStep obj (mrun obj G ch client sched t).1 p o,
          G.leave (mrun obj G ch client sched t).2 p)) ∨
    (∃ p, sched t = some p ∧ weakRound obj ((mrun obj G ch client sched t).1.localState p) = none ∧
      mrun obj G ch client sched (t + 1) =
        (Forward.progStep obj ch (mrun obj G ch client sched t).1 p
          (client p ((mrun obj G ch client sched t).1.sequence p)),
          (mrun obj G ch client sched t).2)) := by
  rw [mrun_succ]
  cases hs : sched t with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some p =>
      cases hw : weakRound obj ((mrun obj G ch client sched t).1.localState p) with
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
      · rw [he]; exact Forward.good_recvStep obj ih hl _
      · rw [he]; exact Forward.good_progStep obj ch ih _ hw

theorem calls_step (t : Nat) :
    ∀ call ∈ (mrun obj G ch client sched t).1.calls, call ∈ (mrun obj G ch client sched (t + 1)).1.calls := by
  intro call h
  rcases mrun_cases obj G ch client sched t with
    ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, o, -, hl, -, he⟩ | ⟨p, -, hw, he⟩
  · rw [he]; exact h
  · rw [he]; exact h
  · rw [he]; show call ∈ (Forward.recvStep obj _ p _).calls; rw [Forward.recvStep_calls]; exact h
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
    rw [he]; exact Forward.recvStep_other obj _ p _ hq
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
    · show weakRound obj _ = weakRound obj _; rw [he]
    · show Forward.waitProp obj _ = Forward.waitProp obj _; rw [he]
  · intro t p q hs hq
    have hl := local_other obj G ch client sched t hs hq
    exact ⟨by show weakRound obj _ = weakRound obj _; rw [hl],
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
    · show weakRound obj _ = _; rw [he]; exact hw
    · show Forward.waitProp obj _ = Forward.waitProp obj _; rw [he]
  · intro t p r o hs hw ho
    obtain ⟨cmd, v, hl⟩ := Forward.waiting_of_round obj hw
    have hv : mwv obj G ch client sched t p = v := by
      show Forward.waitProp obj _ = v; rw [hl]; rfl
    rw [hv] at ho
    have he := mstep_ret obj G ch client (mrun obj G ch client sched t) hl ho
    rw [← hs, ← mrun_succ] at he
    refine ⟨by show (mrun obj G ch client sched (t + 1)).2 = _; rw [he]; rfl, ?_⟩
    show weakRound obj _ = none
    rw [he]
    exact Forward.recvStep_leaves obj _ p _ hl
  · intro t p hs hw
    have he := mstep_prog obj G ch client (mrun obj G ch client sched t) hw
    rw [← hs, ← mrun_succ] at he
    refine ⟨by show (mrun obj G ch client sched (t + 1)).2 = _; rw [he]; rfl, ?_⟩
    intro r hr u hu hru
    have hr' : weakRound obj ((Forward.progStep obj ch (mrun obj G ch client sched t).1 p
        (client p ((mrun obj G ch client sched t).1.sequence p))).localState p) = some r := by
      have : mwr obj G ch client sched (t + 1) p = some r := hr
      unfold mwr at this; rw [he] at this; exact this
    obtain ⟨cmd, seed, hready, rfl, -, -⟩ := Forward.progStep_enters obj ch _ p _ hw hr'
    obtain ⟨cmd', v', hlu⟩ := Forward.waiting_of_round obj hru
    have hcall := (good_all obj G ch client sched u).wcall p cmd' (seed.round + 1) v' hlu
    have hcall' := calls_mono obj G ch client sched hu _ hcall
    have hb := (good_all obj G ch client sched t).bound p
    unfold Forward.RoundBound at hb
    rw [hready] at hb
    dsimp only at hb
    have := hb _ hcall' rfl
    dsimp only at this
    omega

/-- A new call is made by a program step that enters its round with it. -/
theorem progStep_calls_new (c : Configuration (n := n) obj) (p : Fin n) (op : Op)
    {call : Call (n := n) obj} (h : call ∈ (Forward.progStep obj ch c p op).calls) :
    call ∈ c.calls ∨ (call.process = p ∧
      weakRound obj ((Forward.progStep obj ch c p op).localState p) = some call.round ∧
      Forward.waitProp obj ((Forward.progStep obj ch c p op).localState p) = call.trace) := by
  cases hc : c.localState p with
  | ready cmd seed =>
      simp only [Forward.progStep, hc] at h ⊢
      rcases List.mem_cons.mp h with rfl | h
      · right; simp [update, weakRound, Forward.waitProp]
      · exact Or.inl h
  | collecting cmd todo seed =>
      left
      cases todo <;> simpa only [Forward.progStep, hc] using h
  | _ => left; simpa only [Forward.progStep, hc] using h

/-- Every recorded call was made by a process that was inside that round, with
that proposal, by then. -/
theorem calls_entered (t : Nat) : ∀ call ∈ (mrun obj G ch client sched t).1.calls,
    ∃ u, u ≤ t ∧ mwr obj G ch client sched u call.process = some call.round ∧
      mwv obj G ch client sched u call.process = call.trace := by
  induction t with
  | zero => intro call h; simp [mrun, WeakUniversal.initial] at h
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
        have h' : call ∈ (Forward.recvStep obj (mrun obj G ch client sched t).1 p o).calls := h
        rw [Forward.recvStep_calls] at h'
        exact old h'
      · rw [he] at h
        rcases progStep_calls_new obj ch _ p _ h with hc | ⟨hp, hr, hv⟩
        · exact old hc
        · refine ⟨t + 1, Nat.le_refl _, ?_, ?_⟩
          · show weakRound obj _ = _; rw [he, hp]; exact hr
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
      · subst hpq; rw [hl] at hw; simp [weakRound] at hw
      · exact absurd (local_other obj G ch client sched u hs hpq) hne
  · rintro ⟨o, hs, ho⟩ heq
    have he := mstep_ret obj G ch client (mrun obj G ch client sched u) hl ho
    rw [← hs, ← mrun_succ] at he
    have hleft : weakRound obj ((mrun obj G ch client sched (u + 1)).1.localState q) = none := by
      rw [he]; exact Forward.recvStep_leaves obj (mrun obj G ch client sched u).1 q o hl
    rw [heq, hl] at hleft
    simp [weakRound] at hleft

end Run

/-! ## The run is a run of Algorithm 1 over the GCA histories it produces -/

section Refinement
variable (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))

/-- **The GCA histories of the run**: round `r`'s is the history of round `r` in
the run of `G`. -/
noncomputable def env : Environment (n := n) obj := fun r =>
  G.history sched (mwr obj G ch client sched) (mwv obj G ch client sched) (mgs obj G ch client sched) r

theorem env_input_of_waiting {t : Nat} {p : Fin n} {r : Nat}
    (hw : mwr obj G ch client sched t p = some r) :
    (env obj G ch client sched r).input p = some (mwv obj G ch client sched t p) :=
  (driven obj G ch client sched).history_input hw

/-- **A program step outside a call is a step of `WeakUniversal.Step`** for the
run's histories: the only step that consults them is `propose`, and the input
of that round is, by definition, this proposal. -/
theorem prog_valid (t : Nat) {p : Fin n} (hs : sched t = some p)
    (hw : weakRound obj ((mrun obj G ch client sched t).1.localState p) = none) :
    Step obj (env obj G ch client sched) (mrun obj G ch client sched t).1
      (mrun obj G ch client sched (t + 1)).1 := by
  have he := mstep_prog obj G ch client (mrun obj G ch client sched t) hw
  rw [← hs, ← mrun_succ] at he
  have hinput : ∀ cmd seed, (mrun obj G ch client sched t).1.localState p = .ready cmd seed →
      (env obj G ch client sched (seed.round + 1)).input p
        = some ((Tagged obj).appendMissing seed.trace cmd) := by
    intro cmd seed hready
    have hloc : (mrun obj G ch client sched (t + 1)).1.localState p
        = .waiting cmd (seed.round + 1) ((Tagged obj).appendMissing seed.trace cmd) := by
      rw [he]; simp [Forward.progStep, hready, update]
    have hwr : mwr obj G ch client sched (t + 1) p = some (seed.round + 1) := by
      show weakRound obj _ = _; rw [hloc]; rfl
    have hwv : mwv obj G ch client sched (t + 1) p = (Tagged obj).appendMissing seed.trace cmd := by
      show Forward.waitProp obj _ = _; rw [hloc]; rfl
    rw [env_input_of_waiting obj G ch client sched hwr, hwv]
  rw [he]
  unfold Forward.progStep
  cases h : (mrun obj G ch client sched t).1.localState p with
  | idle => exact Step.invoke _ p _ h _ (ch.slotOrder_perm _ p)
  | collecting cmd todo seed =>
      cases todo with
      | nil => exact Step.collected _ p cmd seed h
      | cons q todo => exact Step.read _ p q cmd todo seed h
  | ready cmd seed => exact Step.propose _ p cmd seed h (hinput cmd seed h)
  | waiting cmd r v => rw [h] at hw; simp [weakRound] at hw
  | publishing cmd r s => exact Step.publish _ p cmd r s h
  | returning cmd r s => exact Step.finish _ p cmd r s h

/-- **Returning is a step of `WeakUniversal.Step`** for the run's histories: the
output `G` hands the caller is, by definition, its history output. -/
theorem recv_valid (t : Nat) {p : Fin n} {cmd : Cmd n Op} {r : Nat}
    {v : (Tagged (n := n) obj).Trace} {o : (Tagged (n := n) obj).Trace × Bool}
    (hs : sched t = some p) (hl : (mrun obj G ch client sched t).1.localState p = .waiting cmd r v)
    (ho : G.output (mrun obj G ch client sched t).2 p r v = some o) :
    Step obj (env obj G ch client sched) (mrun obj G ch client sched t).1
      (mrun obj G ch client sched (t + 1)).1 := by
  have he := mstep_ret obj G ch client (mrun obj G ch client sched t) hl ho
  rw [← hs, ← mrun_succ] at he
  have hwr : mwr obj G ch client sched t p = some r := by show weakRound obj _ = _; rw [hl]; rfl
  have hwv : mwv obj G ch client sched t p = v := by show Forward.waitProp obj _ = _; rw [hl]; rfl
  have hout : (env obj G ch client sched r).output p = some o :=
    (driven obj G ch client sched).history_output ⟨t, hs, hwr, by rw [hwv]; exact ho⟩
  rw [he]
  have hstep := Step.receive (H := env obj G ch client sched)
    (mrun obj G ch client sched t).1 p cmd r v o.1 o.2 hl hout
  unfold Forward.recvStep
  rw [hl]
  exact hstep

/-- The program run, as an execution of `WeakUniversal.Step`. -/
noncomputable def mexec : WeakUniversal.Execution obj (env obj G ch client sched) where
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

/-- **The run is a run of Algorithm 1 over its GCA histories**, with one global
schedule. -/
noncomputable def weakRun : GlobalSchedule.WeakRun obj (env obj G ch client sched) where
  run := mexec obj G ch client sched
  actor := sched
  step_actor := by
    intro t
    rcases mrun_cases obj G ch client sched t with
      ⟨hs, he⟩ | ⟨p, cmd, r, v, hs, hl, -, he⟩ | ⟨p, cmd, r, v, o, hs, hl, ho, -⟩ | ⟨p, hs, hw, he⟩
    · exact Or.inl ⟨hs, by show (mrun obj G ch client sched (t + 1)).1 = _; rw [he]; rfl⟩
    · refine Or.inr (Or.inr ⟨p, r, hs, ?_, ?_⟩)
      · show weakRound obj ((mrun obj G ch client sched t).1.localState p) = some r
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

theorem weakRun_state (t : Nat) :
    (weakRun obj G ch client sched).run.state t = (mrun obj G ch client sched t).1 := rfl

theorem weakRun_actor : (weakRun obj G ch client sched).actor = sched := rfl

/-! ## Its GCA objects meet the interface -/

/-- **Every prefix history of the run is a history of a run of `G`**: that of the
run cut at the prefix's end.  So the six properties, which `G` guarantees in
every run, hold of every prefix — the manuscript's "for every execution". -/
theorem prefixHistory_eq (r T : Nat) :
    (weakRun obj G ch client sched).run.prefixHistory obj r T =
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
      have hwr : mwr obj G ch client sched u q = some r := by show weakRound obj _ = _; rw [hl]; rfl
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

/-- **The GCA objects of every run of Algorithm 1 over `G` meet the interface**,
when `G` meets the specification. -/
theorem gcaInterface (hG : G.IsGCA) : (weakRun obj G ch client sched).GCAInterface :=
  (weakRun obj G ch client sched).gcaInterface_of_prefixSpec
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
        show weakRound obj ((mrun obj G ch client sched t).1.localState p) = some r
        rw [show (mrun obj G ch client sched t).1.localState p = .waiting cmd r proposal from h]
        rfl))

/-- **Algorithm 1 over `G`, as a run over GCA objects meeting the interface.** -/
noncomputable def toGCA (hG : G.IsGCA) : GlobalSchedule.WeakGCA obj (env obj G ch client sched) where
  toWeakRun := weakRun obj G ch client sched
  gca := gcaInterface obj G ch client sched hG

@[simp] theorem toGCA_toWeakRun (hG : G.IsGCA) :
    (toGCA obj G ch client sched hG).toWeakRun = weakRun obj G ch client sched := rfl

/-- **Solo agreement of `G` is Solo agreement of the run's GCA objects.**  A
caller that left round `R` returned from it; a process that entered `R` by `N`
recorded its call by `N`. -/
theorem soloAgreement (hsa : G.SoloAgreement) : (weakRun obj G ch client sched).SoloAgreement := by
  intro N v R i hsoloR hv hwait hleave
  have hd := driven obj G ch client sched
  obtain ⟨cmd, prop, hl⟩ := Forward.waiting_of_round obj hwait
  have hl : (mrun obj G ch client sched v).1.localState i = .waiting cmd R prop := hl
  obtain ⟨o, hs, ho⟩ := (leave_iff obj G ch client sched hl).mp hleave
  have hwr : mwr obj G ch client sched v i = some R := hwait
  have hwv : mwv obj G ch client sched v i = prop := by
    show Forward.waitProp obj _ = _; rw [hl]; rfl
  rw [← hwv] at ho
  refine ⟨o.1, o.2, hd.history_output ⟨v, hs, hwr, ho⟩, ?_⟩
  intro q y fl hq
  exact hsa _ _ _ _ hd N R i o
    (fun t q' ht hq' => by
      obtain ⟨cmd', v', hl'⟩ := Forward.waiting_of_round obj hq'
      exact hsoloR _ (calls_mono obj G ch client sched ht _
        ((good_all obj G ch client sched t).wcall q' cmd' R v' hl')) rfl)
    ⟨v, hv, hs, hwr, ho⟩ q y fl hq

/-! ## Executions -/

/-- A scheduler that does not halt gives an operation-live run. -/
theorem opLive (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome) :
    (weakRun obj G ch client sched).OpLive := by
  obtain ⟨p, hp⟩ := Forward.often_some hlive
  intro N
  obtain ⟨t, ht, cmd, hop, -⟩ := (weakRun obj G ch client sched).opActor_infinitely hp N
  exact ⟨t, ht, by rw [hop]; rfl⟩

/-- The §3 execution of a non-halting run of Algorithm 1 over `G`. -/
noncomputable def execution (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome) :
    _root_.ConflictFreedom.Execution n Op :=
  (weakRun obj G ch client sched).execution (opLive obj G ch client sched hlive)

/-- **Linearizability**, of every run of Algorithm 1 over `G`, halting or not:
its whole invocation/response event history is well formed and linearizable. -/
theorem infinite_event_linearization (hG : G.IsGCA) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, ((weakRun obj G ch client sched).run.history obj).returned k a v → v = resp a) ∧
      (∀ a, ((((weakRun obj G ch client sched).run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, ((weakRun obj G ch client sched).run.history obj).invoked N a)) ∧
      (∀ a v, ((((weakRun obj G ch client sched).run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, ((weakRun obj G ch client sched).run.history obj).returned N a v)) ∧
      (((weakRun obj G ch client sched).run.ledgerRun obj).events resp).WellFormed Command.process ∧
      (Tagged obj).InfEventLinearizable Command.process
        (((weakRun obj G ch client sched).run.ledgerRun obj).events resp) :=
  (toGCA obj G ch client sched hG).infinite_event_linearization

end Refinement

/-! ## Theorem `th:WeakUCresolve` over `G` -/

/-- The run's first `N` steps are determined by the scheduler's first `N`
choices. -/
theorem mrun_congr {ch : Forward.Choices (n := n) obj} {client : Fin n → Nat → Op} {s₁ s₂ : Nat → Option (Fin n)} {N : Nat}
    (h : ∀ t, t < N → s₁ t = s₂ t) :
    ∀ t, t ≤ N → mrun obj G ch client s₁ t = mrun obj G ch client s₂ t
  | 0, _ => rfl
  | t + 1, ht => by
      rw [mrun_succ, mrun_succ, mrun_congr h t (by omega), h t (by omega)]

/-- **An extension of a finite execution**, over `G`: the finite execution `α` is
the first `N` steps of `mrun G ch client sched`; the run of `ch'`, `client'`
and `sched'` extends it when it takes the same first `N` steps — the same
process at every step, reaching the same configurations and the same state of
`G`; after them the client, and the rule for the collect order, may differ. -/
def Extends (ch' : Forward.Choices (n := n) obj) (client' : Fin n → Nat → Op) (sched' : Nat → Option (Fin n))
    (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) : Prop :=
  (∀ t, t < N → sched' t = sched t) ∧
    ∀ t, t ≤ N → mrun obj G ch' client' sched' t = mrun obj G ch client sched t

/-- **Definition *conflict-forgetting execution*, over `G`.**  The finite
execution `α` (the first `N` steps of `mrun G ch client sched`) is
conflict-forgetting if in every eventually weakly `α`-conflict-free infinite
extension of `α`, some process that takes infinitely many steps (so a correct
one) completes each of its operations.  As in
`WeakUniversal.Forward.ConflictForgetting`, `α` ends at the extracted
execution's operation time `N - 1`. -/
def ConflictForgetting (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (N : Nat) : Prop :=
  ∀ (ch' : Forward.Choices (n := n) obj) (client' : Fin n → Nat → Op) (sched' : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched' t).isSome),
    Extends obj G ch' client' sched' ch client sched N →
    (execution obj G ch' client' sched' hlive).EventuallyWeaklyConflictFree obj.Conflict (N - 1) →
    ∃ p, (execution obj G ch' client' sched' hlive).InfiniteSteps p ∧
      ∀ i, (execution obj G ch' client' sched' hlive).owner i = p →
        (execution obj G ch' client' sched' hlive).Completes i

open Forward (soloSched soloSched_before soloSched_after) in
/-- **Theorem `th:WeakUCresolve`, over any GCA implementation meeting the
specification and Solo agreement.**  For every finite execution `α` of
Algorithm 1 over `G` — the first `N` steps of its run for any client and any
scheduler — and every process `i`, there is a finite conflict-forgetting
`i`-solo extension of `α`: the first `N'` steps of the run that follows `α` and
then schedules only `i`. -/
theorem weakUCresolve (hG : G.IsGCA) (hsa : G.SoloAgreement)
    (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj G ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictForgetting obj G ch client (soloSched sched N i) N' := by
  obtain ⟨N', hNN', hcf⟩ := (toGCA obj G ch client (soloSched sched N i) hG).weakUCresolve
    (FiniteScheduling.SoloFrom.of_continuous _ fun _ ht => soloSched_after ht)
  refine ⟨N', hNN', ⟨fun t ht => soloSched_before ht,
      mrun_congr obj G (fun t ht => soloSched_before ht)⟩,
    fun t ht _ => soloSched_after ht, ?_⟩
  intro ch' client' sched' hlive hext hweak
  exact hcf _ (toGCA obj G ch' client' sched' hG) (soloAgreement obj G ch' client' sched' hsa)
    (opLive obj G ch' client' sched' hlive)
    ⟨fun t ht => hext.1 t ht, fun t ht => congrArg Prod.fst (hext.2 t ht)⟩ hweak

/-! ## The definitions are not vacuous -/

/-- **"Takes steps after `α`", over `G`.**  An instance takes an operation step
from operation time `N - 1` on exactly when its process is scheduled at some
step `u ≥ N` while running it, so the boundary `N - 1` in `ConflictForgetting`
is the end of `α`. -/
theorem stepsFrom_iff (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome)
    (j : (execution obj G ch client sched hlive).Instance) (N : Nat) :
    (execution obj G ch client sched hlive).StepsFrom (N - 1) j ↔
      ∃ u, N ≤ u ∧ sched u = some j.val.process ∧
        Local.command obj ((mrun obj G ch client sched u).1.localState j.val.process) = some j.val :=
  (weakRun obj G ch client sched).stepsFrom_iff (opLive obj G ch client sched hlive) j N

open Forward (soloSched soloSched_after) in
/-- Letting `i` run alone for ever after `N` gives an extension of the first
`N'` steps, for every `N' ≥ N`, that is eventually weakly conflict-free. -/
theorem soloSched_weaklyConflictFree (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n)
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (soloSched sched N i t).isSome) {N' : Nat} (hN : N ≤ N') :
    (execution obj G ch client (soloSched sched N i) hlive).EventuallyWeaklyConflictFree
      obj.Conflict (N' - 1) := by
  refine ⟨0, fun t _ ja jb hab ha hb hsa hsb => absurd ?_ hab⟩
  have own : ∀ j, (execution obj G ch client (soloSched sched N i) hlive).StepsFrom (N' - 1) j →
      (execution obj G ch client (soloSched sched N i) hlive).owner j = i := by
    intro j hj
    obtain ⟨u, hu, hs, -⟩ := (stepsFrom_iff obj G ch client _ hlive j N').mp hj
    have := hs.symm.trans (soloSched_after (by omega))
    exact Option.some.inj this
  exact (execution obj G ch client (soloSched sched N i) hlive).sequential ja jb t
    ((own ja hsa).trans (own jb hsb).symm) ha.1 hb.1 ha.2 hb.2

/-- A run extends each of its own prefixes. -/
theorem extends_refl (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) :
    Extends obj G ch client sched ch client sched N :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

open Forward (soloSched soloSched_live) in
/-- **`ConflictForgetting` is not vacuous**, over any `G`: the solo continuation
is an extension meeting its hypothesis. -/
theorem conflictForgetting_hypothesis_satisfiable (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) {N' : Nat} (hN : N ≤ N') :
    ∃ hlive, Extends obj G ch client (soloSched sched N i) ch client (soloSched sched N i) N' ∧
      (execution obj G ch client (soloSched sched N i) hlive).EventuallyWeaklyConflictFree
        obj.Conflict (N' - 1) :=
  ⟨soloSched_live sched N i, extends_refl obj G ch client _ N',
    soloSched_weaklyConflictFree obj G ch client sched N i _ hN⟩

/-! ## Algorithm 2 is an instance -/

/-- **Algorithm 1 over Algorithm 2 is the forward machine**: run over
`ForwardGCA.machine`, it is `WeakUniversal.Forward.frun`. -/
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

open Forward (soloSched) in
/-- **Theorem `th:WeakUCresolve` for Algorithm 1 over Algorithm 2**, as an
instance of the modular theorem: Algorithm 2 meets the specification and Solo
agreement, and Algorithm 1 over it is the forward machine (`mrun_machine`). -/
theorem weakUCresolve_algorithm2 (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj (ForwardGCA.machine (Tagged (n := n) obj) n) ch client (soloSched sched N i)
        ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictForgetting obj (ForwardGCA.machine (Tagged (n := n) obj) n) ch client
        (soloSched sched N i) N' :=
  weakUCresolve obj _ ForwardGCA.machine_isGCA ForwardGCA.machine_soloAgreement ch client sched N i

end ConflictFreedom.WeakUniversal.Over

namespace ConflictFreedom
open WeakUniversal.Over
variable {State Op Response : Type} [DecidableEq Op]

/-- **Algorithm 1 over a GCA implementation `G`, as a §3 implementation**: the
executions of every non-halting run, for every rule for the collect order, every
client and every scheduler. -/
def algorithm1Over (obj : Object State Op Response) {n : Nat}
    (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n) : Implementation n Op := fun e =>
  ∃ (ch : WeakUniversal.Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome), e = execution obj G ch client sched hlive

/-- **Over an implementation meeting the GCA specification, every execution is
one of Algorithm 1 over a GCA meeting the interface.** -/
theorem algorithm1Over_anyGCA (obj : Object State Op Response) {n : Nat}
    (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n) (hG : G.IsGCA) :
    ∀ e, algorithm1Over obj G e → algorithm1AnyGCA obj n e := by
  rintro e ⟨ch, client, sched, hlive, rfl⟩
  exact ⟨_, toGCA obj G ch client sched hG, opLive obj G ch client sched hlive, rfl⟩

/-- **Theorem `theorem:weakUCWCF` over any GCA implementation meeting the
specification**: Algorithm 1 over it is weakly conflict-free. -/
theorem algorithm1Over_weakConflictFree (obj : Object State Op Response) {n : Nat}
    (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n) (hG : G.IsGCA) :
    WeakConflictFree (algorithm1Over obj G) obj.Conflict := by
  obtain ⟨hof, hcf⟩ := algorithm1AnyGCA_weakConflictFree obj n
  exact ⟨fun e he => hof e (algorithm1Over_anyGCA obj G hG e he),
    fun e he => hcf e (algorithm1Over_anyGCA obj G hG e he)⟩

/-- The admitted set is not empty, for any `G`, at every process count
`n = m + 1`: any client, with one process scheduled for ever. -/
theorem algorithm1Over_nonempty (obj : Object State Op Response) (op : Op) (m : Nat)
    (G : GCAMachine (WeakUniversal.Tagged (n := m + 1) obj) (m + 1)) :
    ∃ e, algorithm1Over obj G e :=
  ⟨_, WeakUniversal.Forward.Choices.inOrder obj, fun _ _ => op, fun _ => some 0,
    fun N => ⟨N, Nat.le_refl _, rfl⟩, rfl⟩

open WeakUniversal.Forward (soloSched) in
/-- **Theorem `th:WeakUCresolve`, for Algorithm 1 over any GCA implementation
meeting the specification of §4.2 and Solo agreement** (the same statement as
`WeakUniversal.Over.weakUCresolve`). -/
theorem algorithm1Over_weakUCresolve (obj : Object State Op Response) {n : Nat}
    (G : GCAMachine (WeakUniversal.Tagged (n := n) obj) n) (hG : G.IsGCA)
    (hsa : G.SoloAgreement) (ch : WeakUniversal.Forward.Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj G ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictForgetting obj G ch client (soloSched sched N i) N' :=
  weakUCresolve obj G hG hsa ch client sched N i

end ConflictFreedom
