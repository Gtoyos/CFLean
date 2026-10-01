import CFLeanProof.ForwardGCA
import CFLeanProof.Algorithm1WeakConflictFree
import CFLeanProof.CausalLinearization
import CFLeanProof.InfiniteEventLinearization

/-! # Algorithm 1 as a forward machine, and its refinement into the admitted model

`algorithm1` admits an execution when *there exists* a GCA family and a global
schedule consistent with it — the family, with every round's inputs, is data
chosen before the run, and a `propose` step is enabled only if the proposal
happens to equal the pre-ordained input.  That leaves open whether every run of
the actual algorithm is admitted.

This module answers it.  `frun ch client sched` is a *deterministic* machine:
the scheduler `sched` picks who moves at each instant (`none` for an idle tick,
omission for ever for a crash), the client says which operation each process
invokes next, the rule `ch` the order in which each collect of `S` reads the
registers (`Choices`), and each step is a local computation followed by at most one
atomic access — to a register `S[j]`, or to one of the snapshot objects of the
GCA round the process is in.  GCA rounds run Algorithm 2 (`ForwardGCA`), so no
round has an input before somebody proposes to it.

`forward_admitted` then shows that **every non-halting run is admitted**: the
family is reconstructed from the run after the fact (`fam`), the run itself is
the global schedule (`fsched`), and it is fair, operation-live and above an
atomic, hence wait-free, snapshot interface.  The weak conflict-freedom and
linearizability theorems therefore hold for the machine directly
(`forward1_weakConflictFree`, `forward_chain_linearization`,
`forward_infinite_linearization`).
-/
namespace ConflictFreedom.WeakUniversal.Forward
open Object UniversalProtocol ForwardGCA
open GlobalSchedule (weakRound gcaEvent gcaClock)

variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-- The GCA side of the machine. -/
abbrev GS := GState (Tagged (n := n) obj) n

/-- The proposal a caller handed its current call. -/
def waitProp : Local (n := n) obj → (Tagged (n := n) obj).Trace
  | .waiting _ _ v => v
  | _ => (Tagged obj).emptyTrace

variable [DecidableEq Op]

/-- **How the machine resolves the choice Algorithm 1 leaves open**: the order in
which the collect of `S` (Line 4) reads the registers.  Any rule will do — it may
depend on the whole configuration and on the process — as long as it orders all
`n` registers. -/
structure Choices where
  slotOrder : Configuration (n := n) obj → Fin n → List (Fin n)
  slotOrder_perm : ∀ c p, (slotOrder c p).Perm (List.finRange n)

/-- One such rule: collect `S` in index order. -/
def Choices.inOrder : Choices (n := n) obj :=
  ⟨fun _ _ => List.finRange n, fun _ _ => List.Perm.refl _⟩

variable (ch : Choices (n := n) obj)

/-- The program step of a process that is not inside a call.  Each branch is
literally the corresponding constructor of `WeakUniversal.Step`; the order of
the collect of `S` is the rule `ch`'s. -/
def progStep (c : Configuration (n := n) obj) (p : Fin n) (op : Op) : Configuration (n := n) obj :=
  match c.localState p with
  | .idle => { c with
      sequence := update c.sequence p (c.sequence p + 1)
      invocations := ⟨op, p, c.sequence p + 1⟩ :: c.invocations
      localState := update c.localState p (.collecting ⟨op, p, c.sequence p + 1⟩
        (ch.slotOrder c p) (zeroSeed obj)) }
  | .collecting cmd (q :: todo) seed => { c with
      localState := update c.localState p (.collecting cmd todo (best obj seed (c.slots q))) }
  | .collecting cmd [] seed => { c with localState := update c.localState p (.ready cmd seed) }
  | .ready cmd seed => { c with
      localState := update c.localState p
        (.waiting cmd (seed.round + 1) ((Tagged obj).appendMissing seed.trace cmd))
      calls := ⟨seed.round + 1, p, (Tagged obj).appendMissing seed.trace cmd⟩ :: c.calls }
  | .waiting _ _ _ => c
  | .publishing cmd r s => { c with
      localState := update c.localState p (.returning cmd r s)
      slots := update c.slots p ⟨r, s⟩ }
  | .returning cmd r s => { c with
      localState := update c.localState p .idle
      returns := ⟨cmd, r, s⟩ :: c.returns }

/-- The program step of a caller consuming its GCA output. -/
def recvStep (c : Configuration (n := n) obj) (p : Fin n) (out : (Tagged (n := n) obj).Trace × Bool) :
    Configuration (n := n) obj :=
  match c.localState p with
  | .waiting cmd r _ => { c with
      localState := update c.localState p
        (if out.2 = true ∧ 0 < (Tagged obj).traceCount cmd out.1 then .publishing cmd r out.1
        else .ready cmd ⟨r, out.1⟩) }
  | _ => c

/-- **One instant of the machine.**  An idle tick changes nothing; a caller below
the last GCA stage takes a GCA step; a caller at the last stage consumes the
output its own scans determine; anybody else takes its program step. -/
noncomputable def fstep (client : Fin n → Nat → Op)
    (x : Configuration (n := n) obj × GS (n := n) obj) : Option (Fin n) → Configuration (n := n) obj × GS (n := n) obj
  | none => x
  | some p =>
      match x.1.localState p with
      | .waiting _ r v =>
          if (x.2.frame p).phase < 6 then (x.1, gcaStep (Tagged obj) n x.2 p r v)
          else (recvStep obj x.1 p (frameOutput (Tagged obj) n (x.2.frame p) v),
            resetFrame (Tagged obj) n x.2 p)
      | _ => (progStep obj ch x.1 p (client p (x.1.sequence p)), x.2)

/-- **The run of the machine** for a client and a scheduler. -/
noncomputable def frun (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) :
    Nat → Configuration (n := n) obj × GS (n := n) obj
  | 0 => (WeakUniversal.initial obj, GState.initial (Tagged obj) n)
  | t + 1 => fstep obj ch client (frun client sched t) (sched t)

/-! ## One instant, case by case -/

section StepEqs
variable (client : Fin n → Nat → Op) (x : Configuration (n := n) obj × GS (n := n) obj)

theorem fstep_gca {p : Fin n} {cmd : Cmd n Op} {r : Nat} {v : (Tagged (n := n) obj).Trace}
    (hl : x.1.localState p = .waiting cmd r v) (hph : (x.2.frame p).phase < 6) :
    fstep obj ch client x (some p) = (x.1, gcaStep (Tagged obj) n x.2 p r v) := by
  simp only [fstep, hl, ite_eq_left hph]

theorem fstep_recv {p : Fin n} {cmd : Cmd n Op} {r : Nat} {v : (Tagged (n := n) obj).Trace}
    (hl : x.1.localState p = .waiting cmd r v) (hph : ¬ (x.2.frame p).phase < 6) :
    fstep obj ch client x (some p) =
      (recvStep obj x.1 p (frameOutput (Tagged obj) n (x.2.frame p) v),
        resetFrame (Tagged obj) n x.2 p) := by
  simp only [fstep, hl, ite_eq_right hph]

theorem fstep_prog {p : Fin n} (hl : weakRound obj (x.1.localState p) = none) :
    fstep obj ch client x (some p) = (progStep obj ch x.1 p (client p (x.1.sequence p)), x.2) := by
  cases h : x.1.localState p with
  | waiting cmd r v => rw [h] at hl; simp [weakRound] at hl
  | _ => simp only [fstep, h]

end StepEqs

/-! ## Program steps move only their process -/

theorem progStep_other (c : Configuration (n := n) obj) (p : Fin n) (op : Op) {q : Fin n}
    (hq : q ≠ p) : (progStep obj ch c p op).localState q = c.localState q := by
  unfold progStep; split <;> simp [update, hq]

theorem recvStep_other (c : Configuration (n := n) obj) (p : Fin n)
    (out : (Tagged (n := n) obj).Trace × Bool) {q : Fin n} (hq : q ≠ p) :
    (recvStep obj c p out).localState q = c.localState q := by
  unfold recvStep; split <;> simp [update, hq]

theorem recvStep_calls (c : Configuration (n := n) obj) (p : Fin n)
    (out : (Tagged (n := n) obj).Trace × Bool) : (recvStep obj c p out).calls = c.calls := by
  unfold recvStep; split <;> rfl

theorem progStep_calls (c : Configuration (n := n) obj) (p : Fin n) (op : Op) :
    ∀ call ∈ c.calls, call ∈ (progStep obj ch c p op).calls := by
  intro call h
  unfold progStep
  split
  all_goals first
    | exact h
    | exact List.mem_cons_of_mem _ h

/-- A caller leaves its call when it consumes the output. -/
theorem recvStep_leaves (c : Configuration (n := n) obj) (p : Fin n)
    (out : (Tagged (n := n) obj).Trace × Bool) {cmd : Cmd n Op} {r : Nat}
    {v : (Tagged (n := n) obj).Trace} (hl : c.localState p = .waiting cmd r v) :
    weakRound obj ((recvStep obj c p out).localState p) = none := by
  simp only [recvStep, hl, update, ite_eq_left]
  split <;> rfl

/-- A program step enters a call only from `ready`, and only into the next round. -/
theorem progStep_enters (c : Configuration (n := n) obj) (p : Fin n) (op : Op)
    (hl : weakRound obj (c.localState p) = none) {r : Nat}
    (hr : weakRound obj ((progStep obj ch c p op).localState p) = some r) :
    ∃ cmd seed, c.localState p = .ready cmd seed ∧ r = seed.round + 1 ∧
      (progStep obj ch c p op).localState p =
        .waiting cmd (seed.round + 1) ((Tagged obj).appendMissing seed.trace cmd) ∧
      (progStep obj ch c p op).calls =
        ⟨seed.round + 1, p, (Tagged obj).appendMissing seed.trace cmd⟩ :: c.calls := by
  unfold progStep at hr ⊢
  cases h : c.localState p with
  | collecting cmd todo seed =>
      rw [h] at hr
      cases todo <;> simp [update, weakRound] at hr
  | ready cmd seed =>
      rw [h] at hr
      simp [update, weakRound] at hr
      exact ⟨cmd, seed, rfl, by omega, by simp [update], by simp⟩
  | waiting cmd r' v => rw [h] at hl; simp [weakRound] at hl
  | _ => rw [h] at hr; simp [update, weakRound] at hr

/-! ## The program invariant: every proposal goes to a round never used -/

/-- Every call a process has made is at most the round its local state is at;
after publication, its own register records that round. -/
def RoundBound (c : Configuration (n := n) obj) (p : Fin n) : Prop :=
  match c.localState p with
  | .idle => ∀ call ∈ c.calls, call.process = p → call.round ≤ (c.slots p).round
  | .collecting _ todo seed =>
      (∀ call ∈ c.calls, call.process = p → call.round ≤ (c.slots p).round) ∧
        (p ∉ todo → (c.slots p).round ≤ seed.round)
  | .ready _ seed => ∀ call ∈ c.calls, call.process = p → call.round ≤ seed.round
  | .waiting _ r _ => ∀ call ∈ c.calls, call.process = p → call.round ≤ r
  | .publishing _ r _ => ∀ call ∈ c.calls, call.process = p → call.round ≤ r
  | .returning _ r _ =>
      (∀ call ∈ c.calls, call.process = p → call.round ≤ r) ∧ (c.slots p).round = r

/-- A caller inside a call has recorded that call. -/
def WaitCall (c : Configuration (n := n) obj) (p : Fin n) : Prop :=
  ∀ cmd r v, c.localState p = .waiting cmd r v → (⟨r, p, v⟩ : Call (n := n) obj) ∈ c.calls

/-- The program invariant, true all along the run (`good_all`). -/
structure Good (c : Configuration (n := n) obj) : Prop where
  bound : ∀ p, RoundBound obj c p
  wcall : ∀ p, WaitCall obj c p

omit [DecidableEq Op] in
theorem good_initial : Good obj (WeakUniversal.initial (n := n) obj) := by
  refine ⟨fun p => ?_, fun p cmd r v h => ?_⟩
  · show ∀ call ∈ ([] : List (Call (n := n) obj)), _ → _
    intro call h; cases h
  · cases h

omit [DecidableEq Op] in
theorem roundBound_transfer {c c' : Configuration (n := n) obj} {q : Fin n}
    (hl : c'.localState q = c.localState q) (hs : c'.slots q = c.slots q)
    (hc : ∀ call ∈ c'.calls, call.process = q → call ∈ c.calls) (h : RoundBound obj c q) :
    RoundBound obj c' q := by
  have tr : ∀ {P : Call (n := n) obj → Prop}, (∀ call ∈ c.calls, call.process = q → P call) →
      ∀ call ∈ c'.calls, call.process = q → P call :=
    fun h call hm hp => h call (hc call hm hp) hp
  unfold RoundBound at h ⊢
  rw [hl, hs]
  cases hq : c.localState q with
  | collecting _ _ _ => rw [hq] at h; exact ⟨tr h.1, h.2⟩
  | returning _ _ _ => rw [hq] at h; exact ⟨tr h.1, h.2⟩
  | _ => rw [hq] at h; exact tr h

theorem good_progStep {c : Configuration (n := n) obj} (hg : Good obj c) {p : Fin n} (op : Op)
    (hl : weakRound obj (c.localState p) = none) : Good obj (progStep obj ch c p op) := by
  have hcalls_other : ∀ q, q ≠ p → ∀ call ∈ (progStep obj ch c p op).calls,
      call.process = q → call ∈ c.calls := by
    intro q hq call hm hp
    unfold progStep at hm
    split at hm
    all_goals first
      | exact hm
      | (rcases List.mem_cons.mp hm with rfl | hm
         · exact absurd hp (by simpa using hq.symm)
         · exact hm)
  have hslots_other : ∀ q, q ≠ p → (progStep obj ch c p op).slots q = c.slots q := by
    intro q hq
    unfold progStep
    split <;> simp [update, hq]
  refine ⟨fun q => ?_, fun q => ?_⟩
  · by_cases hq : q = p
    · subst hq
      have hb := hg.bound q
      unfold RoundBound at hb ⊢
      unfold progStep
      cases h : c.localState q with
      | idle =>
          rw [h] at hb
          simp only [update]
          refine ⟨hb, fun hn => absurd ((ch.slotOrder_perm c q).mem_iff.mpr (List.mem_finRange q)) hn⟩
      | collecting cmd todo seed =>
          rw [h] at hb
          cases todo with
          | nil =>
              simp only [update]
              intro call hm hp
              exact Nat.le_trans (hb.1 call hm hp) (hb.2 (List.not_mem_nil))
          | cons q' todo =>
              simp only [update]
              refine ⟨hb.1, fun hn => ?_⟩
              rw [best_round]
              by_cases hqq : q' = q
              · subst hqq; exact Nat.le_max_right _ _
              · exact Nat.le_trans (hb.2 (by
                  intro hm
                  rcases List.mem_cons.mp hm with he | hm
                  · exact hqq he.symm
                  · exact hn hm)) (Nat.le_max_left _ _)
      | ready cmd seed =>
          rw [h] at hb
          simp only [update]
          intro call hm hp
          rcases List.mem_cons.mp hm with rfl | hm
          · exact Nat.le_refl _
          · exact Nat.le_trans (hb call hm hp) (Nat.le_succ _)
      | waiting cmd r v => rw [h] at hl; simp [weakRound] at hl
      | publishing cmd r s =>
          rw [h] at hb
          simp only [update]
          exact ⟨hb, rfl⟩
      | returning cmd r s =>
          rw [h] at hb
          simp only [update]
          intro call hm hp
          rw [hb.2]
          exact hb.1 call hm hp
    · exact roundBound_transfer obj (progStep_other obj ch c p op hq) (hslots_other q hq)
        (hcalls_other q hq) (hg.bound q)
  · by_cases hq : q = p
    · subst hq
      intro cmd r v hw
      obtain ⟨cmd', seed, hready, -, hloc, hcall⟩ := progStep_enters obj ch c q op hl
        (by rw [hw]; rfl)
      rw [hloc] at hw
      obtain ⟨rfl, rfl, rfl⟩ : cmd' = cmd ∧ seed.round + 1 = r ∧
          (Tagged obj).appendMissing seed.trace cmd' = v := by
        simp only [Local.waiting.injEq] at hw; exact hw
      rw [hcall]
      exact List.mem_cons_self ..
    · intro cmd r v hw
      rw [progStep_other obj ch c p op hq] at hw
      exact progStep_calls obj ch c p op _ (hg.wcall q cmd r v hw)

theorem good_recvStep {c : Configuration (n := n) obj} (hg : Good obj c) {p : Fin n}
    {cmd : Cmd n Op} {r : Nat} {v : (Tagged (n := n) obj).Trace}
    (hl : c.localState p = .waiting cmd r v) (out : (Tagged (n := n) obj).Trace × Bool) :
    Good obj (recvStep obj c p out) := by
  have hslots : (recvStep obj c p out).slots = c.slots := by
    unfold recvStep; split <;> rfl
  refine ⟨fun q => ?_, fun q => ?_⟩
  · by_cases hq : q = p
    · subst hq
      have hb := hg.bound q
      unfold RoundBound at hb
      rw [hl] at hb
      dsimp only at hb
      unfold RoundBound
      simp only [recvStep, hl, update, ite_eq_left]
      by_cases hc : out.2 = true ∧ 0 < (Tagged obj).traceCount cmd out.1
      · rw [ite_eq_left hc]; exact hb
      · rw [ite_eq_right hc]; exact hb
    · exact roundBound_transfer obj (recvStep_other obj c p out hq) (by rw [hslots])
        (fun call hm _ => by rw [recvStep_calls] at hm; exact hm) (hg.bound q)
  · by_cases hq : q = p
    · subst hq
      intro cmd' r' v' hw
      have := recvStep_leaves obj c q out hl
      rw [hw] at this
      cases this
    · intro cmd' r' v' hw
      rw [recvStep_other obj c p out hq] at hw
      rw [recvStep_calls]
      exact hg.wcall q cmd' r' v' hw

/-! ## The run -/

section Run
variable (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))

/-- The round each process is blocked in at instant `t`. -/
noncomputable def fwr (t : Nat) (p : Fin n) : Option Nat :=
  weakRound obj ((frun obj ch client sched t).1.localState p)

/-- The proposal each process handed its current call at instant `t`. -/
noncomputable def fwv (t : Nat) (p : Fin n) : (Tagged (n := n) obj).Trace :=
  waitProp obj ((frun obj ch client sched t).1.localState p)

theorem frun_succ (t : Nat) :
    frun obj ch client sched (t + 1) = fstep obj ch client (frun obj ch client sched t) (sched t) := rfl

omit [DecidableEq Op] in
theorem waiting_of_round {l : Local (n := n) obj} {r : Nat} (h : weakRound obj l = some r) :
    ∃ cmd v, l = .waiting cmd r v :=
  GlobalSchedule.weakRound_eq_some h

/-- **Every instant falls in one of four cases.** -/
theorem frun_cases (t : Nat) :
    (sched t = none ∧ frun obj ch client sched (t + 1) = frun obj ch client sched t) ∨
    (∃ p cmd r v, sched t = some p ∧ (frun obj ch client sched t).1.localState p = .waiting cmd r v ∧
      ((frun obj ch client sched t).2.frame p).phase < 6 ∧
      frun obj ch client sched (t + 1) =
        ((frun obj ch client sched t).1, gcaStep (Tagged obj) n (frun obj ch client sched t).2 p r v)) ∨
    (∃ p cmd r v, sched t = some p ∧ (frun obj ch client sched t).1.localState p = .waiting cmd r v ∧
      ¬ ((frun obj ch client sched t).2.frame p).phase < 6 ∧
      frun obj ch client sched (t + 1) =
        (recvStep obj (frun obj ch client sched t).1 p
          (frameOutput (Tagged obj) n ((frun obj ch client sched t).2.frame p) v),
          resetFrame (Tagged obj) n (frun obj ch client sched t).2 p)) ∨
    (∃ p, sched t = some p ∧ weakRound obj ((frun obj ch client sched t).1.localState p) = none ∧
      frun obj ch client sched (t + 1) =
        (progStep obj ch (frun obj ch client sched t).1 p
          (client p ((frun obj ch client sched t).1.sequence p)), (frun obj ch client sched t).2)) := by
  rw [frun_succ]
  cases hs : sched t with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some p =>
      cases hw : weakRound obj ((frun obj ch client sched t).1.localState p) with
      | none => exact Or.inr (Or.inr (Or.inr ⟨p, rfl, hw, fstep_prog obj ch client _ hw⟩))
      | some r =>
          obtain ⟨cmd, v, hl⟩ := waiting_of_round obj hw
          by_cases hph : ((frun obj ch client sched t).2.frame p).phase < 6
          · exact Or.inr (Or.inl ⟨p, cmd, r, v, rfl, hl, hph, fstep_gca obj ch client _ hl hph⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨p, cmd, r, v, rfl, hl, hph, fstep_recv obj ch client _ hl hph⟩))

theorem good_all : ∀ t, Good obj (frun obj ch client sched t).1 := by
  intro t
  induction t with
  | zero => exact good_initial obj
  | succ t ih =>
      rcases frun_cases obj ch client sched t with
        ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, -, hw, he⟩
      · rw [he]; exact ih
      · rw [he]; exact ih
      · rw [he]; exact good_recvStep obj ih hl _
      · rw [he]; exact good_progStep obj ch ih _ hw

theorem calls_step (t : Nat) :
    ∀ call ∈ (frun obj ch client sched t).1.calls, call ∈ (frun obj ch client sched (t + 1)).1.calls := by
  intro call h
  rcases frun_cases obj ch client sched t with
    ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, -, hw, he⟩
  · rw [he]; exact h
  · rw [he]; exact h
  · rw [he]; show call ∈ (recvStep obj _ p _).calls; rw [recvStep_calls]; exact h
  · rw [he]; exact progStep_calls obj ch _ p _ call h

theorem calls_mono {u t : Nat} (h : u ≤ t) :
    ∀ call ∈ (frun obj ch client sched u).1.calls, call ∈ (frun obj ch client sched t).1.calls := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact fun call h => h
  | succ d ih => exact fun call h => calls_step obj ch client sched (u + d) call (ih call h)

/-- Only the scheduled process's local state moves. -/
theorem local_other (t : Nat) {p q : Fin n} (hs : sched t = some p) (hq : q ≠ p) :
    (frun obj ch client sched (t + 1)).1.localState q = (frun obj ch client sched t).1.localState q := by
  rcases frun_cases obj ch client sched t with
    ⟨h0, -⟩ | ⟨p', cmd, r, v, h0, hl, -, he⟩ | ⟨p', cmd, r, v, h0, hl, -, he⟩ | ⟨p', h0, hw, he⟩
  · rw [hs] at h0; cases h0
  · rw [he]
  · rw [hs] at h0; obtain rfl := Option.some.inj h0
    rw [he]; exact recvStep_other obj _ p _ hq
  · rw [hs] at h0; obtain rfl := Option.some.inj h0
    rw [he]; exact progStep_other obj ch _ p _ hq

/-- **The machine drives its GCA rounds by the discipline of `ForwardGCA`.** -/
theorem driven :
    Driven sched (fwr obj ch client sched) (fwv obj ch client sched) (fun t => (frun obj ch client sched t).2) := by
  refine ⟨rfl, fun p => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hs
    have he : frun obj ch client sched (t + 1) = frun obj ch client sched t := by
      rw [frun_succ, hs]; rfl
    refine ⟨by show (frun obj ch client sched (t + 1)).2 = _; rw [he], fun q => ⟨?_, ?_⟩⟩
    · show weakRound obj _ = weakRound obj _; rw [he]
    · show waitProp obj _ = waitProp obj _; rw [he]
  · intro t p q hs hq
    have hl := local_other obj ch client sched t hs hq
    exact ⟨by show weakRound obj _ = weakRound obj _; rw [hl],
      by show waitProp obj _ = waitProp obj _; rw [hl]⟩
  · intro t p r hs hw hph
    obtain ⟨cmd, v, hl⟩ := waiting_of_round obj hw
    have he : frun obj ch client sched (t + 1) =
        ((frun obj ch client sched t).1, gcaStep (Tagged obj) n (frun obj ch client sched t).2 p r v) := by
      rw [frun_succ, hs]; exact fstep_gca obj ch client _ hl hph
    have hv : fwv obj ch client sched t p = v := by
      show waitProp obj _ = v; rw [hl]; rfl
    refine ⟨by show (frun obj ch client sched (t + 1)).2 = _; rw [he, hv], ?_, ?_⟩
    · show weakRound obj _ = _; rw [he]; exact hw
    · show waitProp obj _ = waitProp obj _; rw [he]
  · intro t p r hs hw hph
    obtain ⟨cmd, v, hl⟩ := waiting_of_round obj hw
    have he := fstep_recv obj ch client (frun obj ch client sched t) hl hph
    rw [← hs, ← frun_succ] at he
    refine ⟨by show (frun obj ch client sched (t + 1)).2 = _; rw [he], ?_⟩
    show weakRound obj _ = none
    rw [he]
    exact recvStep_leaves obj _ p _ hl
  · intro t p hs hw
    have he := fstep_prog obj ch client (frun obj ch client sched t) hw
    rw [← hs, ← frun_succ] at he
    refine ⟨by show (frun obj ch client sched (t + 1)).2 = _; rw [he], ?_⟩
    intro r hr u hu hru
    have hr' : weakRound obj ((progStep obj ch (frun obj ch client sched t).1 p
        (client p ((frun obj ch client sched t).1.sequence p))).localState p) = some r := by
      have : fwr obj ch client sched (t + 1) p = some r := hr
      unfold fwr at this; rw [he] at this; exact this
    obtain ⟨cmd, seed, hready, rfl, -, -⟩ := progStep_enters obj ch _ p _ hw hr'
    obtain ⟨cmd', v', hlu⟩ := waiting_of_round obj hru
    have hcall := (good_all obj ch client sched u).wcall p cmd' (seed.round + 1) v' hlu
    have hcall' := calls_mono obj ch client sched hu _ hcall
    have hb := (good_all obj ch client sched t).bound p
    unfold RoundBound at hb
    rw [hready] at hb
    dsimp only at hb
    have := hb _ hcall' rfl
    dsimp only at this
    omega

end Run

/-! ## The refinement -/

section Refinement
variable (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))

/-- **The GCA family, reconstructed from the run after the fact.** -/
noncomputable def fam : Family (n := n) obj :=
  ⟨fun r => retro sched (fwr obj ch client sched) (fwv obj ch client sched) r⟩

theorem fam_waitFree : (fam obj ch client sched).SnapshotWaitFree obj :=
  fun r => retro_waitFree sched (fwr obj ch client sched) (fwv obj ch client sched) r

theorem gcaEvent_eq (t : Nat) :
    gcaEvent obj (fun t => (frun obj ch client sched t).1) sched t = ev sched (fwr obj ch client sched) t := by
  unfold gcaEvent ev fwr
  cases sched t <;> rfl

theorem gcaClock_eq : ∀ t r,
    gcaClock obj (fun t => (frun obj ch client sched t).1) sched t r = clk sched (fwr obj ch client sched) t r
  | 0, _ => rfl
  | t + 1, r => by
      simp only [gcaClock, clk]
      rw [gcaEvent_eq, gcaClock_eq t r]
      cases ev sched (fwr obj ch client sched) t with
      | none => rfl
      | some rp => rfl

/-- The history of round `r` is the reconstructed protocol's. -/
theorem env_eq (r : Nat) : (fam obj ch client sched).environment obj r =
    (retro sched (fwr obj ch client sched) (fwv obj ch client sched) r).history := rfl

theorem env_input_of_waiting {t : Nat} {p : Fin n} {r : Nat}
    (hw : fwr obj ch client sched t p = some r) :
    ((fam obj ch client sched).environment obj r).input p = some (fwv obj ch client sched t p) := by
  rw [env_eq, retro_input_of_waited ⟨t, hw⟩, (driven obj ch client sched).rinput_eq hw]

theorem waited_of_input {r : Nat} {p : Fin n} {s : (Tagged (n := n) obj).Trace}
    (h : ((fam obj ch client sched).environment obj r).input p = some s) :
    ∃ t, fwr obj ch client sched t p = some r :=
  waited_of_retro_input (act := sched) (wv := fwv obj ch client sched) h

/-- **A program step outside a call is a step of `WeakUniversal.Step`** for the
reconstructed family.  The only step that consults the family is `propose`,
and the family's input for that round is, by construction, this proposal. -/
theorem prog_valid (t : Nat) {p : Fin n} (hs : sched t = some p)
    (hw : weakRound obj ((frun obj ch client sched t).1.localState p) = none) :
    Step obj ((fam obj ch client sched).environment obj) (frun obj ch client sched t).1
      (frun obj ch client sched (t + 1)).1 := by
  have he := fstep_prog obj ch client (frun obj ch client sched t) hw
  rw [← hs, ← frun_succ] at he
  have hinput : ∀ cmd seed, (frun obj ch client sched t).1.localState p = .ready cmd seed →
      ((fam obj ch client sched).environment obj (seed.round + 1)).input p
        = some ((Tagged obj).appendMissing seed.trace cmd) := by
    intro cmd seed hready
    have hloc : (frun obj ch client sched (t + 1)).1.localState p
        = .waiting cmd (seed.round + 1) ((Tagged obj).appendMissing seed.trace cmd) := by
      rw [he]; simp [progStep, hready, update]
    have hwr : fwr obj ch client sched (t + 1) p = some (seed.round + 1) := by
      show weakRound obj _ = _; rw [hloc]; rfl
    have hwv : fwv obj ch client sched (t + 1) p = (Tagged obj).appendMissing seed.trace cmd := by
      show waitProp obj _ = _; rw [hloc]; rfl
    rw [env_input_of_waiting obj ch client sched hwr, hwv]
  rw [he]
  unfold progStep
  cases h : (frun obj ch client sched t).1.localState p with
  | idle => exact Step.invoke _ p _ h _ (ch.slotOrder_perm _ p)
  | collecting cmd todo seed =>
      cases todo with
      | nil => exact Step.collected _ p cmd seed h
      | cons q todo => exact Step.read _ p q cmd todo seed h
  | ready cmd seed => exact Step.propose _ p cmd seed h (hinput cmd seed h)
  | waiting cmd r v => rw [h] at hw; simp [weakRound] at hw
  | publishing cmd r s => exact Step.publish _ p cmd r s h
  | returning cmd r s => exact Step.finish _ p cmd r s h

/-- **Consuming the output is a step of `WeakUniversal.Step`** for the
reconstructed family: the output the caller's own scans determine *is* the
family's output (`ForwardGCA.output_agrees`). -/
theorem recv_valid (t : Nat) {p : Fin n} {cmd : Cmd n Op} {r : Nat}
    {v : (Tagged (n := n) obj).Trace} (hs : sched t = some p)
    (hl : (frun obj ch client sched t).1.localState p = .waiting cmd r v)
    (hph : ¬ ((frun obj ch client sched t).2.frame p).phase < 6) :
    Step obj ((fam obj ch client sched).environment obj) (frun obj ch client sched t).1
      (frun obj ch client sched (t + 1)).1 := by
  have he := fstep_recv obj ch client (frun obj ch client sched t) hl hph
  rw [← hs, ← frun_succ] at he
  have hwr : fwr obj ch client sched t p = some r := by show weakRound obj _ = _; rw [hl]; rfl
  have hwv : fwv obj ch client sched t p = v := by show waitProp obj _ = _; rw [hl]; rfl
  have hout := output_agrees (driven obj ch client sched) hwr hph
  rw [hwv] at hout
  rw [he]
  have hstep := Step.receive (H := (fam obj ch client sched).environment obj)
    (frun obj ch client sched t).1 p cmd r v
    (frameOutput (Tagged obj) n ((frun obj ch client sched t).2.frame p) v).1
    (frameOutput (Tagged obj) n ((frun obj ch client sched t).2.frame p) v).2 hl hout
  unfold recvStep
  rw [hl]
  exact hstep

/-- The program run of the machine, as an execution of `WeakUniversal.Step`. -/
noncomputable def fexec : WeakUniversal.Execution obj ((fam obj ch client sched).environment obj) where
  state := fun t => (frun obj ch client sched t).1
  initial_state := rfl
  next := by
    intro t
    rcases frun_cases obj ch client sched t with
      ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, hs, hl, hph, -⟩ | ⟨p, hs, hw, -⟩
    · exact Or.inl (by show (frun obj ch client sched (t + 1)).1 = _; rw [he])
    · exact Or.inl (by show (frun obj ch client sched (t + 1)).1 = _; rw [he])
    · exact Or.inr (recv_valid obj ch client sched t hs hl hph)
    · exact Or.inr (prog_valid obj ch client sched t hs hw)

/-- **The run of the machine is a global schedule** for the family reconstructed
from it. -/
noncomputable def fsched : GlobalSchedule.Weak obj (fam obj ch client sched) where
  run := fexec obj ch client sched
  actor := sched
  step_actor := by
    intro t
    rcases frun_cases obj ch client sched t with
      ⟨hs, he⟩ | ⟨p, cmd, r, v, hs, hl, hph, he⟩ | ⟨p, cmd, r, v, hs, hl, hph, he⟩ | ⟨p, hs, hw, he⟩
    · exact Or.inl ⟨hs, by show (frun obj ch client sched (t + 1)).1 = _; rw [he]; rfl⟩
    · refine Or.inr (Or.inr ⟨p, r, hs, ?_, ?_⟩)
      · show weakRound obj ((frun obj ch client sched t).1.localState p) = some r
        rw [hl]; rfl
      · show (frun obj ch client sched (t + 1)).1 = _; rw [he]; rfl
    · exact Or.inr (Or.inl ⟨p, hs, recv_valid obj ch client sched t hs hl hph,
        fun q hq => local_other obj ch client sched t hs hq⟩)
    · exact Or.inr (Or.inl ⟨p, hs, prog_valid obj ch client sched t hs hw,
        fun q hq => local_other obj ch client sched t hs hq⟩)
  gca_actor := by
    intro t p r hs hw
    show ractor sched (fwr obj ch client sched) r
      (gcaClock obj (fun t => (frun obj ch client sched t).1) sched t r) = some p
    rw [gcaClock_eq]
    exact ractor_of_event sched (fwr obj ch client sched) (ev_spec sched (fwr obj ch client sched) hs hw)
  no_ghost := by
    intro r p s hi
    obtain ⟨t, hw⟩ := waited_of_input obj ch client sched hi
    obtain ⟨cmd, v, hl⟩ := waiting_of_round obj hw
    exact ⟨t, v, (good_all obj ch client sched t).wcall p cmd (r + 1) v hl⟩
  receive_ready := by
    intro t p r hw hchange
    show (retro sched (fwr obj ch client sched) (fwv obj ch client sched) r).phase
      (gcaClock obj (fun t => (frun obj ch client sched t).1) sched t r) p = 6
    rw [gcaClock_eq]
    have hchange' : (frun obj ch client sched (t + 1)).1.localState p
        ≠ (frun obj ch client sched t).1.localState p := hchange
    rcases frun_cases obj ch client sched t with
      ⟨hs, he⟩ | ⟨p', cmd, r', v, hs, hl, hph, he⟩ | ⟨p', cmd, r', v, hs, hl, hph, he⟩ | ⟨p', hs, hw', he⟩
    · exact absurd (by rw [he]) hchange'
    · exact absurd (by rw [he]) hchange'
    · by_cases hq : p = p'
      · subst hq
        have hr : r' = r := by
          have : weakRound obj ((frun obj ch client sched t).1.localState p) = some r := hw
          rw [hl] at this; exact Option.some.inj this
        subst hr
        have hinv := (Inv.all (driven obj ch client sched) t).phase p r' hw
        have h6 := (retro sched (fwr obj ch client sched) (fwv obj ch client sched) r').phase_le_six
          (clk sched (fwr obj ch client sched) t r') p
        have : ((frun obj ch client sched t).2.frame p).phase
            = (retro sched (fwr obj ch client sched) (fwv obj ch client sched) r').phase
              (clk sched (fwr obj ch client sched) t r') p := hinv
        omega
      · exact absurd (local_other obj ch client sched t hs hq) hchange'
    · by_cases hq : p = p'
      · subst hq
        have : weakRound obj ((frun obj ch client sched t).1.localState p) = some r := hw
        rw [hw'] at this; cases this
      · exact absurd (local_other obj ch client sched t hs hq) hchange'

theorem fsched_state (t : Nat) : (fsched obj ch client sched).run.state t = (frun obj ch client sched t).1 := rfl

theorem fsched_actor : (fsched obj ch client sched).actor = sched := rfl

/-- **Fairness holds by construction**: a scheduled caller whose round clock shows
the last stage consumes its output, because that is what the machine does. -/
theorem fsched_fair : (fsched obj ch client sched).Fair := by
  intro t p cmd r proposal hs hl hphase _
  have hl' : (frun obj ch client sched t).1.localState p = .waiting cmd r proposal := hl
  have hwr : fwr obj ch client sched t p = some r := by
    show weakRound obj _ = _; rw [hl']; rfl
  have hinv := (Inv.all (driven obj ch client sched) t).phase p r hwr
  have hphase' : (retro sched (fwr obj ch client sched) (fwv obj ch client sched) r).phase
      (clk sched (fwr obj ch client sched) t r) p = 6 := by
    have := hphase
    rw [show gcaClock obj (fsched obj ch client sched).run.state (fsched obj ch client sched).actor t r
      = clk sched (fwr obj ch client sched) t r from gcaClock_eq obj ch client sched t r] at this
    exact this
  have hph : ¬ ((frun obj ch client sched t).2.frame p).phase < 6 := by
    have : ((frun obj ch client sched t).2.frame p).phase
        = (retro sched (fwr obj ch client sched) (fwv obj ch client sched) r).phase
          (clk sched (fwr obj ch client sched) t r) p := hinv
    omega
  exact ⟨recv_valid obj ch client sched t hs hl' hph, fun q hq => local_other obj ch client sched t hs hq⟩

end Refinement

/-! ## Operation liveness from a scheduler that does not halt -/

omit [DecidableEq Op] in
theorem le_sum_map {α : Type} (f : α → Nat) : ∀ (L : List α), ∀ a ∈ L, f a ≤ (L.map f).sum
  | [], _, h => by cases h
  | b :: L, a, h => by
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := le_sum_map f L a h; omega

omit [DecidableEq Op] in
/-- A scheduler that keeps scheduling somebody schedules some process for ever. -/
theorem often_some {sched : Nat → Option (Fin n)} (h : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome) :
    ∃ p, ∀ N, ∃ t, N ≤ t ∧ sched t = some p := by
  apply Classical.byContradiction
  intro hno
  have hfin : ∀ p : Fin n, ∃ N, ∀ t, N ≤ t → sched t ≠ some p := by
    intro p
    apply Classical.byContradiction
    intro hp
    exact hno ⟨p, fun N => Classical.byContradiction fun hN =>
      hp ⟨N, fun t ht hs => hN ⟨t, ht, hs⟩⟩⟩
  let bound : Fin n → Nat := fun p => Classical.choose (hfin p)
  obtain ⟨t, ht, hsome⟩ := h (((List.finRange n).map bound).sum)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  have hle : bound p ≤ ((List.finRange n).map bound).sum :=
    le_sum_map bound (List.finRange n) p (List.mem_finRange p)
  exact Classical.choose_spec (hfin p) t (Nat.le_trans hle ht) hp

variable (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))

/-- **Operation liveness** follows from the scheduler not halting. -/
theorem fsched_opLive (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome) :
    (fsched obj ch client sched).OpLive := by
  obtain ⟨p, hp⟩ := often_some hlive
  intro N
  obtain ⟨t, ht, cmd, hop, -⟩ := (fsched obj ch client sched).opActor_infinitely hp N
  exact ⟨t, ht, by rw [hop]; rfl⟩

/-- **Refinement.**  Every run of the machine whose scheduler does not halt is
admitted by `algorithm1`. -/
theorem forward_admitted (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome) :
    algorithm1 obj n ((fsched obj ch client sched).execution (fsched_opLive obj ch client sched hlive)) :=
  ⟨fam obj ch client sched, fsched obj ch client sched, fsched_opLive obj ch client sched hlive,
    fsched_fair obj ch client sched, fam_waitFree obj ch client sched, rfl⟩

/-- Safety needs no liveness at all: every run of the machine, halting or not, is
linearizable by one growing chain of sequential orders. -/
theorem forward_chain_linearization :
    ∃ x : Nat → List (Cmd n Op),
      (∀ N, (Tagged obj).Linearizes ((fsched obj ch client sched).run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :=
  (fsched obj ch client sched).chain_linearization

/-- The same in the manuscript's own terms, for the whole run: the machine's
whole, possibly infinite, invocation/response event history is well formed and
linearizable — a completion `H̄` and a legal sequential history `S` with
`H̄|ᵢ = S|ᵢ` for every process and `≼_H ⊆ ≼_S`.  No liveness is needed. -/
theorem forward_infinite_linearization :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, ((fsched obj ch client sched).run.history obj).returned k a v → v = resp a) ∧
      (∀ a, (((fsched obj ch client sched).run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, ((fsched obj ch client sched).run.history obj).invoked N a) ∧
      (∀ a v, (((fsched obj ch client sched).run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, ((fsched obj ch client sched).run.history obj).returned N a v) ∧
      (((fsched obj ch client sched).run.ledgerRun obj).events resp).WellFormed Command.process ∧
      (Tagged obj).InfEventLinearizable Command.process
        (((fsched obj ch client sched).run.ledgerRun obj).events resp) :=
  (fsched obj ch client sched).infinite_event_linearization

end ConflictFreedom.WeakUniversal.Forward

namespace ConflictFreedom
open WeakUniversal.Forward
variable {State Op Response : Type} [DecidableEq Op]

/-- **Algorithm 1 as the machine runs it**: the executions of every non-halting
run of `frun`, for every client, every rule for the collect order and every
scheduler. -/
def forward1 (obj : Object State Op Response) (n : Nat) : Implementation n Op := fun e =>
  ∃ (client : Fin n → Nat → Op) (ch : Choices (n := n) obj) (sched : Nat → Option (Fin n))
    (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome),
    e = (fsched obj ch client sched).execution (fsched_opLive obj ch client sched hlive)

/-- **Every execution of the machine is admitted.** -/
theorem forward1_admitted (obj : Object State Op Response) (n : Nat) :
    ∀ e, forward1 obj n e → algorithm1 obj n e := by
  rintro e ⟨client, ch, sched, hlive, rfl⟩
  exact forward_admitted obj ch client sched hlive

/-- **The machine's GCA objects meet the interface**: every execution of the
machine is an execution of Algorithm 1 over a GCA meeting the interface, so
every theorem proved over the interface applies to it. -/
theorem forward1_anyGCA (obj : Object State Op Response) (n : Nat) :
    ∀ e, forward1 obj n e → algorithm1AnyGCA obj n e :=
  fun e he => algorithm1_anyGCA obj n e (forward1_admitted obj n e he)

/-- **Algorithm 1, as the machine runs it, is weakly conflict-free.** -/
theorem forward1_weakConflictFree (obj : Object State Op Response) (n : Nat) :
    WeakConflictFree (forward1 obj n) obj.Conflict := by
  obtain ⟨hof, hcf⟩ := algorithm1_weakConflictFree obj n
  exact ⟨fun e he => hof e (forward1_admitted obj n e he),
    fun e he => hcf e (forward1_admitted obj n e he)⟩

/-- The machine has runs: any client, with one process scheduled for ever. -/
theorem forward1_nonempty (obj : Object State Op Response) (op : Op) (m : Nat) :
    ∃ e, forward1 obj (m + 1) e :=
  ⟨_, fun _ _ => op, Choices.inOrder obj, fun _ => some 0, fun N => ⟨N, Nat.le_refl _, rfl⟩, rfl⟩

end ConflictFreedom
