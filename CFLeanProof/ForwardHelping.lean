import CFLeanProof.ForwardGCA
import CFLeanProof.Algorithm3ConflictFree
import CFLeanProof.CausalLinearization
import CFLeanProof.InfiniteEventLinearization
import CFLeanProof.ForwardUniversal

/-! # Algorithm 3 as a forward machine, and its refinement into the admitted model

The helping counterpart of `ForwardUniversal`.  `frun client sched` is a
deterministic machine running Algorithm 3 over atomic registers `S[j]` and
`M[j]` and, for its GCA rounds, Algorithm 2 over atomic snapshot objects
(`ForwardGCA`).  `forward_admitted` shows every non-halting run is admitted by
`algorithm3`, with the GCA family reconstructed from the run; the conflict-free
and linearizability theorems therefore hold for the machine directly
(`forward3_conflictFree`, `forward_chain_linearization`,
`forward_infinite_linearization`).

Freshness of proposals — no process ever calls a GCA object twice — is proved
here from the persistent local base: it only grows, and every proposal goes to
the round after it.
-/
namespace ConflictFreedom.HelpingUniversal.Forward
open Object UniversalProtocol ForwardGCA
open WeakUniversal (Cmd Tagged Seed Call Return update zeroSeed best best_round)
open GlobalSchedule (helpingRound gcaEventH gcaClockH)

variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-- The GCA side of the machine. -/
abbrev GS := GState (Tagged (n := n) obj) n

/-- The proposal a caller handed its current call. -/
def waitProp : Local (n := n) obj → (Tagged (n := n) obj).Trace
  | .waiting _ _ v => v
  | _ => (Tagged obj).emptyTrace

variable [DecidableEq Op]

/-- **How the machine resolves the choices Algorithm 3 leaves open**: the order
in which a collect of `S` (Lines 6 and 16) reads the registers, the order in
which a collect of `M` (Line 10) reads them, and the order of `trace(M_i)` at
Line 11.  Any rule will do — each may depend on the whole configuration and on
the process — as long as the two collect orders read all `n` registers and the
arrangement permutes the announcements the collect found. -/
structure Choices where
  slotOrder : Configuration (n := n) obj → Fin n → List (Fin n)
  slotOrder_perm : ∀ c p, (slotOrder c p).Perm (List.finRange n)
  announcementOrder : Configuration (n := n) obj → Fin n → List (Fin n)
  announcementOrder_perm : ∀ c p, (announcementOrder c p).Perm (List.finRange n)
  arrange : Configuration (n := n) obj → Fin n → List (Cmd n Op) → List (Cmd n Op)
  arrange_perm : ∀ c p l, (arrange c p l).Perm l

/-- One such rule: collect `S` and `M` in index order, and append the
announcements in the order the collect read them. -/
def Choices.inOrder : Choices (n := n) obj :=
  ⟨fun _ _ => List.finRange n, fun _ _ => List.Perm.refl _,
    fun _ _ => List.finRange n, fun _ _ => List.Perm.refl _,
    fun _ _ l => l, fun _ _ _ => List.Perm.refl _⟩

variable (ch : Choices (n := n) obj)

/-- The program step of a process that is not inside a call; each branch is the
corresponding constructor of `HelpingUniversal.Step`.  At the end of a check the
process retries if its command is still missing and returns otherwise, exactly
as the two constructors `retry` and `finish` split.  The order of each collect —
of `S` or of `M` — and the order of `trace(M_i)` are the rule `ch`'s. -/
def progStep (c : Configuration (n := n) obj) (p : Fin n) (op : Op) : Configuration (n := n) obj :=
  match c.localState p with
  | .idle seed => { c with
      sequence := update c.sequence p (c.sequence p + 1)
      invocations := ⟨op, p, c.sequence p + 1⟩ :: c.invocations
      localState := update c.localState p (.announcing ⟨op, p, c.sequence p + 1⟩ seed) }
  | .announcing cmd seed => { c with
      announcements := update c.announcements p (some cmd)
      localState := update c.localState p (.collecting cmd (ch.slotOrder c p) seed) }
  | .collecting cmd (q :: todo) seed => { c with
      localState := update c.localState p (.collecting cmd todo (best obj seed (c.slots q))) }
  | .collecting cmd [] seed => { c with
      localState := update c.localState p (.gathering cmd seed (ch.announcementOrder c p) []) }
  | .gathering cmd seed (q :: todo) commands => { c with
      localState := update c.localState p
        (.gathering cmd seed todo (observe obj seed (c.announcements q) commands)) }
  | .gathering cmd seed [] commands => { c with
      localState := update c.localState p
        (.waiting cmd (seed.round + 1) (proposal obj seed (ch.arrange c p commands)))
      calls := ⟨seed.round + 1, p, proposal obj seed (ch.arrange c p commands)⟩ :: c.calls }
  | .waiting _ _ _ => c
  | .publishing cmd seed => { c with
      slots := update c.slots p seed
      localState := update c.localState p (.checking cmd seed (ch.slotOrder c p) (zeroSeed obj)) }
  | .checking cmd seed (q :: todo) seen => { c with
      localState := update c.localState p (.checking cmd seed todo (best obj seen (c.slots q))) }
  | .checking cmd seed [] seen =>
      if (Tagged obj).traceCount cmd seen.trace = 0 then
        { c with localState := update c.localState p (.gathering cmd seed (ch.announcementOrder c p) []) }
      else
        { c with
          localState := update c.localState p (.idle seed)
          returns := ⟨cmd, seen.round, seen.trace⟩ :: c.returns }

/-- The program step of a caller consuming its GCA output; a caller that adopts
starts its check collect of `S` in the rule `ch`'s order. -/
def recvStep (c : Configuration (n := n) obj) (p : Fin n) (out : (Tagged (n := n) obj).Trace × Bool) :
    Configuration (n := n) obj :=
  match c.localState p with
  | .waiting cmd r _ => { c with
      localState := update c.localState p
        (if out.2 = true then .publishing cmd ⟨r, out.1⟩
        else .checking cmd ⟨r, out.1⟩ (ch.slotOrder c p) (zeroSeed obj)) }
  | _ => c

/-- **One instant of the machine.**  An idle tick changes nothing; a caller below
the last GCA stage takes a GCA step; a caller at the last stage consumes the
output its own scans determine; anybody else takes its program step. -/
noncomputable def fstep (client : Fin n → Nat → Op)
    (x : Configuration (n := n) obj × GS (n := n) obj) :
    Option (Fin n) → Configuration (n := n) obj × GS (n := n) obj
  | none => x
  | some p =>
      match x.1.localState p with
      | .waiting _ r v =>
          if (x.2.frame p).phase < 6 then (x.1, gcaStep (Tagged obj) n x.2 p r v)
          else (recvStep obj ch x.1 p (frameOutput (Tagged obj) n (x.2.frame p) v),
            resetFrame (Tagged obj) n x.2 p)
      | _ => (progStep obj ch x.1 p (client p (x.1.sequence p)), x.2)

/-- **The run of the machine** for a client and a scheduler. -/
noncomputable def frun (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) :
    Nat → Configuration (n := n) obj × GS (n := n) obj
  | 0 => (HelpingUniversal.initial obj, GState.initial (Tagged obj) n)
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
      (recvStep obj ch x.1 p (frameOutput (Tagged obj) n (x.2.frame p) v),
        resetFrame (Tagged obj) n x.2 p) := by
  simp only [fstep, hl, ite_eq_right hph]

theorem fstep_prog {p : Fin n} (hl : helpingRound obj (x.1.localState p) = none) :
    fstep obj ch client x (some p) = (progStep obj ch x.1 p (client p (x.1.sequence p)), x.2) := by
  cases h : x.1.localState p with
  | waiting cmd r v => rw [h] at hl; simp [helpingRound] at hl
  | _ => simp only [fstep, h]

end StepEqs

/-! ## Program steps move only their process -/

theorem progStep_other (c : Configuration (n := n) obj) (p : Fin n) (op : Op) {q : Fin n}
    (hq : q ≠ p) : (progStep obj ch c p op).localState q = c.localState q := by
  unfold progStep; split
  all_goals first
    | simp [update, hq]
    | (split <;> simp [update, hq])

omit [DecidableEq Op] in
theorem recvStep_other (c : Configuration (n := n) obj) (p : Fin n)
    (out : (Tagged (n := n) obj).Trace × Bool) {q : Fin n} (hq : q ≠ p) :
    (recvStep obj ch c p out).localState q = c.localState q := by
  unfold recvStep; split <;> simp [update, hq]

omit [DecidableEq Op] in
theorem recvStep_calls (c : Configuration (n := n) obj) (p : Fin n)
    (out : (Tagged (n := n) obj).Trace × Bool) : (recvStep obj ch c p out).calls = c.calls := by
  unfold recvStep; split <;> rfl

theorem progStep_calls (c : Configuration (n := n) obj) (p : Fin n) (op : Op) :
    ∀ call ∈ c.calls, call ∈ (progStep obj ch c p op).calls := by
  intro call h
  unfold progStep
  split
  all_goals first
    | exact h
    | exact List.mem_cons_of_mem _ h
    | (split <;> exact h)

omit [DecidableEq Op] in
theorem recvStep_leaves (c : Configuration (n := n) obj) (p : Fin n)
    (out : (Tagged (n := n) obj).Trace × Bool) {cmd : Cmd n Op} {r : Nat}
    {v : (Tagged (n := n) obj).Trace} (hl : c.localState p = .waiting cmd r v) :
    helpingRound obj ((recvStep obj ch c p out).localState p) = none := by
  simp only [recvStep, hl, update, ite_eq_left]
  split <;> rfl

theorem progStep_enters (c : Configuration (n := n) obj) (p : Fin n) (op : Op)
    (hl : helpingRound obj (c.localState p) = none) {r : Nat}
    (hr : helpingRound obj ((progStep obj ch c p op).localState p) = some r) :
    ∃ cmd seed commands, c.localState p = .gathering cmd seed [] commands ∧ r = seed.round + 1 ∧
      (progStep obj ch c p op).localState p =
        .waiting cmd (seed.round + 1) (proposal obj seed (ch.arrange c p commands)) ∧
      (progStep obj ch c p op).calls =
        ⟨seed.round + 1, p, proposal obj seed (ch.arrange c p commands)⟩ :: c.calls := by
  unfold progStep at hr ⊢
  cases h : c.localState p with
  | collecting cmd todo seed =>
      rw [h] at hr
      cases todo <;> simp [update, helpingRound] at hr
  | gathering cmd seed todo commands =>
      rw [h] at hr
      cases todo with
      | cons q todo => simp [update, helpingRound] at hr
      | nil =>
          simp [update, helpingRound] at hr
          exact ⟨cmd, seed, commands, rfl, by omega, by simp [update], by simp⟩
  | waiting cmd r' v => rw [h] at hl; simp [helpingRound] at hl
  | checking cmd seed todo seen =>
      rw [h] at hr
      cases todo with
      | cons q todo => simp [update, helpingRound] at hr
      | nil =>
          by_cases hc : (Tagged obj).traceCount cmd seen.trace = 0
          · simp [hc, update, helpingRound] at hr
          · simp [hc, update, helpingRound] at hr
  | _ => rw [h] at hr; simp [update, helpingRound] at hr

/-! ## The program invariant: the local base only grows -/

/-- The round a process's local state is based on: the round its next proposal
goes to is one more. -/
def baseRound : Local (n := n) obj → Nat
  | .idle b => b.round
  | .announcing _ b => b.round
  | .collecting _ _ s => s.round
  | .gathering _ s _ _ => s.round
  | .waiting _ r _ => r
  | .publishing _ s => s.round
  | .checking _ s _ _ => s.round

/-- Every call a process has made is at most the round of its local base. -/
def RoundBound (c : Configuration (n := n) obj) (p : Fin n) : Prop :=
  ∀ call ∈ c.calls, call.process = p → call.round ≤ baseRound obj (c.localState p)

/-- A caller inside a call has recorded that call. -/
def WaitCall (c : Configuration (n := n) obj) (p : Fin n) : Prop :=
  ∀ cmd r v, c.localState p = .waiting cmd r v → (⟨r, p, v⟩ : Call (n := n) obj) ∈ c.calls

/-- The program invariant, true all along the run (`good_all`). -/
structure Good (c : Configuration (n := n) obj) : Prop where
  bound : ∀ p, RoundBound obj c p
  wcall : ∀ p, WaitCall obj c p

omit [DecidableEq Op] in
theorem good_initial : Good obj (HelpingUniversal.initial (n := n) obj) := by
  refine ⟨fun p => ?_, fun p cmd r v h => ?_⟩
  · intro call h; cases h
  · cases h

/-- A program step never lowers its process's base round. -/
theorem baseRound_progStep (c : Configuration (n := n) obj) (p : Fin n) (op : Op)
    (hl : helpingRound obj (c.localState p) = none) :
    baseRound obj (c.localState p) ≤ baseRound obj ((progStep obj ch c p op).localState p) := by
  unfold progStep
  cases h : c.localState p with
  | collecting cmd todo seed =>
      cases todo with
      | nil => simp [update, baseRound]
      | cons q todo => simp [update, baseRound, best_round]; omega
  | gathering cmd seed todo commands =>
      cases todo with
      | nil => simp [update, baseRound]
      | cons q todo => simp [update, baseRound]
  | waiting cmd r v => rw [h] at hl; simp [helpingRound] at hl
  | checking cmd seed todo seen =>
      cases todo with
      | cons q todo => simp [update, baseRound]
      | nil =>
          by_cases hc : (Tagged obj).traceCount cmd seen.trace = 0 <;> simp [hc, update, baseRound]
  | _ => simp [update, baseRound]

/-- The only call a program step records is its process's, at the new base. -/
theorem calls_progStep (c : Configuration (n := n) obj) (p : Fin n) (op : Op) :
    ∀ call ∈ (progStep obj ch c p op).calls, call ∈ c.calls ∨
      (call.process = p ∧ call.round = baseRound obj ((progStep obj ch c p op).localState p)) := by
  intro call hm
  unfold progStep at hm ⊢
  cases h : c.localState p with
  | gathering cmd seed todo commands =>
      rw [h] at hm
      cases todo with
      | cons q todo => exact Or.inl hm
      | nil =>
          rcases List.mem_cons.mp hm with rfl | hm
          · exact Or.inr ⟨rfl, by simp [update, baseRound]⟩
          · exact Or.inl hm
  | checking cmd seed todo seen =>
      rw [h] at hm
      cases todo with
      | cons q todo => exact Or.inl hm
      | nil =>
          by_cases hc : (Tagged obj).traceCount cmd seen.trace = 0
          · simp only [hc, ite_true] at hm; exact Or.inl hm
          · simp only [hc] at hm; exact Or.inl hm
  | collecting cmd todo seed => rw [h] at hm; cases todo <;> exact Or.inl hm
  | _ => rw [h] at hm; exact Or.inl hm

theorem good_progStep {c : Configuration (n := n) obj} (hg : Good obj c) {p : Fin n} (op : Op)
    (hl : helpingRound obj (c.localState p) = none) : Good obj (progStep obj ch c p op) := by
  refine ⟨fun q => ?_, fun q => ?_⟩
  · by_cases hq : q = p
    · subst hq
      intro call hm hp
      rcases calls_progStep obj ch c q op call hm with hold | ⟨-, heq⟩
      · exact Nat.le_trans (hg.bound q call hold hp) (baseRound_progStep obj ch c q op hl)
      · exact Nat.le_of_eq heq
    · intro call hm hp
      rw [progStep_other obj ch c p op hq]
      rcases calls_progStep obj ch c p op call hm with hold | ⟨hpp, -⟩
      · exact hg.bound q call hold hp
      · exact absurd (hp.symm.trans hpp) hq
  · by_cases hq : q = p
    · subst hq
      intro cmd r v hw
      obtain ⟨cmd', seed, commands, -, -, hloc, hcall⟩ := progStep_enters obj ch c q op hl
        (by rw [hw]; rfl)
      rw [hloc] at hw
      obtain ⟨rfl, rfl, rfl⟩ : cmd' = cmd ∧ seed.round + 1 = r ∧
          proposal obj seed (ch.arrange c q commands) = v := by
        simp only [Local.waiting.injEq] at hw; exact hw
      rw [hcall]
      exact List.mem_cons_self ..
    · intro cmd r v hw
      rw [progStep_other obj ch c p op hq] at hw
      exact progStep_calls obj ch c p op _ (hg.wcall q cmd r v hw)

omit [DecidableEq Op] in
theorem good_recvStep {c : Configuration (n := n) obj} (hg : Good obj c) {p : Fin n}
    {cmd : Cmd n Op} {r : Nat} {v : (Tagged (n := n) obj).Trace}
    (hl : c.localState p = .waiting cmd r v) (out : (Tagged (n := n) obj).Trace × Bool) :
    Good obj (recvStep obj ch c p out) := by
  refine ⟨fun q => ?_, fun q => ?_⟩
  · by_cases hq : q = p
    · subst hq
      intro call hm hp
      rw [recvStep_calls] at hm
      have := hg.bound q call hm hp
      rw [hl] at this
      simp only [recvStep, hl, update, ite_eq_left]
      by_cases hc : out.2 = true
      · rw [ite_eq_left hc]; exact this
      · rw [ite_eq_right hc]; exact this
    · intro call hm hp
      rw [recvStep_other obj ch c p out hq]
      rw [recvStep_calls] at hm
      exact hg.bound q call hm hp
  · by_cases hq : q = p
    · subst hq
      intro cmd' r' v' hw
      have := recvStep_leaves obj ch c q out hl
      rw [hw] at this
      cases this
    · intro cmd' r' v' hw
      rw [recvStep_other obj ch c p out hq] at hw
      rw [recvStep_calls]
      exact hg.wcall q cmd' r' v' hw

/-! ## The run -/

section Run
variable (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))

/-- The round each process is blocked in at instant `t`. -/
noncomputable def fwr (t : Nat) (p : Fin n) : Option Nat :=
  helpingRound obj ((frun obj ch client sched t).1.localState p)

/-- The proposal each process handed its current call at instant `t`. -/
noncomputable def fwv (t : Nat) (p : Fin n) : (Tagged (n := n) obj).Trace :=
  waitProp obj ((frun obj ch client sched t).1.localState p)

theorem frun_succ (t : Nat) :
    frun obj ch client sched (t + 1) = fstep obj ch client (frun obj ch client sched t) (sched t) := rfl

omit [DecidableEq Op] in
theorem waiting_of_round {l : Local (n := n) obj} {r : Nat} (h : helpingRound obj l = some r) :
    ∃ cmd v, l = .waiting cmd r v :=
  GlobalSchedule.helpingRound_eq_some h

theorem frun_cases (t : Nat) :
    (sched t = none ∧ frun obj ch client sched (t + 1) = frun obj ch client sched t) ∨
    (∃ p cmd r v, sched t = some p ∧ (frun obj ch client sched t).1.localState p = .waiting cmd r v ∧
      ((frun obj ch client sched t).2.frame p).phase < 6 ∧
      frun obj ch client sched (t + 1) =
        ((frun obj ch client sched t).1, gcaStep (Tagged obj) n (frun obj ch client sched t).2 p r v)) ∨
    (∃ p cmd r v, sched t = some p ∧ (frun obj ch client sched t).1.localState p = .waiting cmd r v ∧
      ¬ ((frun obj ch client sched t).2.frame p).phase < 6 ∧
      frun obj ch client sched (t + 1) =
        (recvStep obj ch (frun obj ch client sched t).1 p
          (frameOutput (Tagged obj) n ((frun obj ch client sched t).2.frame p) v),
          resetFrame (Tagged obj) n (frun obj ch client sched t).2 p)) ∨
    (∃ p, sched t = some p ∧ helpingRound obj ((frun obj ch client sched t).1.localState p) = none ∧
      frun obj ch client sched (t + 1) =
        (progStep obj ch (frun obj ch client sched t).1 p
          (client p ((frun obj ch client sched t).1.sequence p)), (frun obj ch client sched t).2)) := by
  rw [frun_succ]
  cases hs : sched t with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some p =>
      cases hw : helpingRound obj ((frun obj ch client sched t).1.localState p) with
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
      · rw [he]; exact good_recvStep obj ch ih hl _
      · rw [he]; exact good_progStep obj ch ih _ hw

theorem calls_step (t : Nat) :
    ∀ call ∈ (frun obj ch client sched t).1.calls, call ∈ (frun obj ch client sched (t + 1)).1.calls := by
  intro call h
  rcases frun_cases obj ch client sched t with
    ⟨-, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, cmd, r, v, -, hl, -, he⟩ | ⟨p, -, hw, he⟩
  · rw [he]; exact h
  · rw [he]; exact h
  · rw [he]; show call ∈ (recvStep obj ch _ p _).calls; rw [recvStep_calls]; exact h
  · rw [he]; exact progStep_calls obj ch _ p _ call h

theorem calls_mono {u t : Nat} (h : u ≤ t) :
    ∀ call ∈ (frun obj ch client sched u).1.calls, call ∈ (frun obj ch client sched t).1.calls := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact fun call h => h
  | succ d ih => exact fun call h => calls_step obj ch client sched (u + d) call (ih call h)

theorem local_other (t : Nat) {p q : Fin n} (hs : sched t = some p) (hq : q ≠ p) :
    (frun obj ch client sched (t + 1)).1.localState q = (frun obj ch client sched t).1.localState q := by
  rcases frun_cases obj ch client sched t with
    ⟨h0, -⟩ | ⟨p', cmd, r, v, h0, hl, -, he⟩ | ⟨p', cmd, r, v, h0, hl, -, he⟩ | ⟨p', h0, hw, he⟩
  · rw [hs] at h0; cases h0
  · rw [he]
  · rw [hs] at h0; obtain rfl := Option.some.inj h0
    rw [he]; exact recvStep_other obj ch _ p _ hq
  · rw [hs] at h0; obtain rfl := Option.some.inj h0
    rw [he]; exact progStep_other obj ch _ p _ hq

theorem driven :
    Driven sched (fwr obj ch client sched) (fwv obj ch client sched) (fun t => (frun obj ch client sched t).2) := by
  refine ⟨rfl, fun p => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hs
    have he : frun obj ch client sched (t + 1) = frun obj ch client sched t := by
      rw [frun_succ, hs]; rfl
    refine ⟨by show (frun obj ch client sched (t + 1)).2 = _; rw [he], fun q => ⟨?_, ?_⟩⟩
    · show helpingRound obj _ = helpingRound obj _; rw [he]
    · show waitProp obj _ = waitProp obj _; rw [he]
  · intro t p q hs hq
    have hl := local_other obj ch client sched t hs hq
    exact ⟨by show helpingRound obj _ = helpingRound obj _; rw [hl],
      by show waitProp obj _ = waitProp obj _; rw [hl]⟩
  · intro t p r hs hw hph
    obtain ⟨cmd, v, hl⟩ := waiting_of_round obj hw
    have he : frun obj ch client sched (t + 1) =
        ((frun obj ch client sched t).1, gcaStep (Tagged obj) n (frun obj ch client sched t).2 p r v) := by
      rw [frun_succ, hs]; exact fstep_gca obj ch client _ hl hph
    have hv : fwv obj ch client sched t p = v := by
      show waitProp obj _ = v; rw [hl]; rfl
    refine ⟨by show (frun obj ch client sched (t + 1)).2 = _; rw [he, hv], ?_, ?_⟩
    · show helpingRound obj _ = _; rw [he]; exact hw
    · show waitProp obj _ = waitProp obj _; rw [he]
  · intro t p r hs hw hph
    obtain ⟨cmd, v, hl⟩ := waiting_of_round obj hw
    have he := fstep_recv obj ch client (frun obj ch client sched t) hl hph
    rw [← hs, ← frun_succ] at he
    refine ⟨by show (frun obj ch client sched (t + 1)).2 = _; rw [he], ?_⟩
    show helpingRound obj _ = none
    rw [he]
    exact recvStep_leaves obj ch _ p _ hl
  · intro t p hs hw
    have he := fstep_prog obj ch client (frun obj ch client sched t) hw
    rw [← hs, ← frun_succ] at he
    refine ⟨by show (frun obj ch client sched (t + 1)).2 = _; rw [he], ?_⟩
    intro r hr u hu hru
    have hr' : helpingRound obj ((progStep obj ch (frun obj ch client sched t).1 p
        (client p ((frun obj ch client sched t).1.sequence p))).localState p) = some r := by
      have : fwr obj ch client sched (t + 1) p = some r := hr
      unfold fwr at this; rw [he] at this; exact this
    obtain ⟨cmd, seed, commands, hgath, rfl, -, -⟩ := progStep_enters obj ch _ p _ hw hr'
    obtain ⟨cmd', v', hlu⟩ := waiting_of_round obj hru
    have hcall := (good_all obj ch client sched u).wcall p cmd' (seed.round + 1) v' hlu
    have hcall' := calls_mono obj ch client sched hu _ hcall
    have hb := (good_all obj ch client sched t).bound p _ hcall' rfl
    rw [hgath] at hb
    dsimp only [baseRound] at hb
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

theorem gcaEventH_eq (t : Nat) :
    gcaEventH obj (fun t => (frun obj ch client sched t).1) sched t = ev sched (fwr obj ch client sched) t := by
  unfold gcaEventH ev fwr
  cases sched t <;> rfl

theorem gcaClockH_eq : ∀ t r,
    gcaClockH obj (fun t => (frun obj ch client sched t).1) sched t r = clk sched (fwr obj ch client sched) t r
  | 0, _ => rfl
  | t + 1, r => by
      simp only [gcaClockH, clk]
      rw [gcaEventH_eq, gcaClockH_eq t r]
      cases ev sched (fwr obj ch client sched) t with
      | none => rfl
      | some rp => rfl

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

/-- **A program step outside a call is a step of `HelpingUniversal.Step`** for
the reconstructed family. -/
theorem prog_valid (t : Nat) {p : Fin n} (hs : sched t = some p)
    (hw : helpingRound obj ((frun obj ch client sched t).1.localState p) = none) :
    Step obj ((fam obj ch client sched).environment obj) (frun obj ch client sched t).1
      (frun obj ch client sched (t + 1)).1 := by
  have he := fstep_prog obj ch client (frun obj ch client sched t) hw
  rw [← hs, ← frun_succ] at he
  have hinput : ∀ cmd seed commands,
      (frun obj ch client sched t).1.localState p = .gathering cmd seed [] commands →
      ((fam obj ch client sched).environment obj (seed.round + 1)).input p
        = some (proposal obj seed (ch.arrange (frun obj ch client sched t).1 p commands)) := by
    intro cmd seed commands hg
    have hloc : (frun obj ch client sched (t + 1)).1.localState p = .waiting cmd (seed.round + 1)
        (proposal obj seed (ch.arrange (frun obj ch client sched t).1 p commands)) := by
      rw [he]; simp [progStep, hg, update]
    have hwr : fwr obj ch client sched (t + 1) p = some (seed.round + 1) := by
      show helpingRound obj _ = _; rw [hloc]; rfl
    have hwv : fwv obj ch client sched (t + 1) p
        = proposal obj seed (ch.arrange (frun obj ch client sched t).1 p commands) := by
      show waitProp obj _ = _; rw [hloc]; rfl
    rw [env_input_of_waiting obj ch client sched hwr, hwv]
  rw [he]
  unfold progStep
  cases h : (frun obj ch client sched t).1.localState p with
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

/-- **Consuming the output is a step of `HelpingUniversal.Step`.** -/
theorem recv_valid (t : Nat) {p : Fin n} {cmd : Cmd n Op} {r : Nat}
    {v : (Tagged (n := n) obj).Trace} (hs : sched t = some p)
    (hl : (frun obj ch client sched t).1.localState p = .waiting cmd r v)
    (hph : ¬ ((frun obj ch client sched t).2.frame p).phase < 6) :
    Step obj ((fam obj ch client sched).environment obj) (frun obj ch client sched t).1
      (frun obj ch client sched (t + 1)).1 := by
  have he := fstep_recv obj ch client (frun obj ch client sched t) hl hph
  rw [← hs, ← frun_succ] at he
  have hwr : fwr obj ch client sched t p = some r := by show helpingRound obj _ = _; rw [hl]; rfl
  have hwv : fwv obj ch client sched t p = v := by show waitProp obj _ = _; rw [hl]; rfl
  have hout := output_agrees (driven obj ch client sched) hwr hph
  rw [hwv] at hout
  rw [he]
  have hstep := Step.receive (H := (fam obj ch client sched).environment obj)
    (frun obj ch client sched t).1 p cmd r v
    (frameOutput (Tagged obj) n ((frun obj ch client sched t).2.frame p) v).1
    (frameOutput (Tagged obj) n ((frun obj ch client sched t).2.frame p) v).2 hl hout
    _ (ch.slotOrder_perm (frun obj ch client sched t).1 p)
  unfold recvStep
  rw [hl]
  exact hstep

/-- The program run of the machine, as an execution of `HelpingUniversal.Step`. -/
noncomputable def fexec : HelpingUniversal.Execution obj ((fam obj ch client sched).environment obj) where
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
noncomputable def fsched : GlobalSchedule.Helping obj (fam obj ch client sched) where
  run := fexec obj ch client sched
  actor := sched
  step_actor := by
    intro t
    rcases frun_cases obj ch client sched t with
      ⟨hs, he⟩ | ⟨p, cmd, r, v, hs, hl, hph, he⟩ | ⟨p, cmd, r, v, hs, hl, hph, he⟩ | ⟨p, hs, hw, he⟩
    · exact Or.inl ⟨hs, by show (frun obj ch client sched (t + 1)).1 = _; rw [he]; rfl⟩
    · refine Or.inr (Or.inr ⟨p, r, hs, ?_, ?_⟩)
      · show helpingRound obj ((frun obj ch client sched t).1.localState p) = some r
        rw [hl]; rfl
      · show (frun obj ch client sched (t + 1)).1 = _; rw [he]; rfl
    · exact Or.inr (Or.inl ⟨p, hs, recv_valid obj ch client sched t hs hl hph,
        fun q hq => local_other obj ch client sched t hs hq⟩)
    · exact Or.inr (Or.inl ⟨p, hs, prog_valid obj ch client sched t hs hw,
        fun q hq => local_other obj ch client sched t hs hq⟩)
  gca_actor := by
    intro t p r hs hw
    show ractor sched (fwr obj ch client sched) r
      (gcaClockH obj (fun t => (frun obj ch client sched t).1) sched t r) = some p
    rw [gcaClockH_eq]
    exact ractor_of_event sched (fwr obj ch client sched) (ev_spec sched (fwr obj ch client sched) hs hw)
  no_ghost := by
    intro r p s hi
    obtain ⟨t, hw⟩ := waited_of_input obj ch client sched hi
    obtain ⟨cmd, v, hl⟩ := waiting_of_round obj hw
    exact ⟨t, v, (good_all obj ch client sched t).wcall p cmd (r + 1) v hl⟩
  receive_ready := by
    intro t p r hw hchange
    show (retro sched (fwr obj ch client sched) (fwv obj ch client sched) r).phase
      (gcaClockH obj (fun t => (frun obj ch client sched t).1) sched t r) p = 6
    rw [gcaClockH_eq]
    have hchange' : (frun obj ch client sched (t + 1)).1.localState p
        ≠ (frun obj ch client sched t).1.localState p := hchange
    rcases frun_cases obj ch client sched t with
      ⟨hs, he⟩ | ⟨p', cmd, r', v, hs, hl, hph, he⟩ | ⟨p', cmd, r', v, hs, hl, hph, he⟩ | ⟨p', hs, hw', he⟩
    · exact absurd (by rw [he]) hchange'
    · exact absurd (by rw [he]) hchange'
    · by_cases hq : p = p'
      · subst hq
        have hr : r' = r := by
          have : helpingRound obj ((frun obj ch client sched t).1.localState p) = some r := hw
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
        have : helpingRound obj ((frun obj ch client sched t).1.localState p) = some r := hw
        rw [hw'] at this; cases this
      · exact absurd (local_other obj ch client sched t hs hq) hchange'

theorem fsched_state (t : Nat) : (fsched obj ch client sched).run.state t = (frun obj ch client sched t).1 := rfl

theorem fsched_actor : (fsched obj ch client sched).actor = sched := rfl

theorem fsched_fair : (fsched obj ch client sched).Fair := by
  intro t p cmd r proposal hs hl hphase _
  have hl' : (frun obj ch client sched t).1.localState p = .waiting cmd r proposal := hl
  have hwr : fwr obj ch client sched t p = some r := by
    show helpingRound obj _ = _; rw [hl']; rfl
  have hinv := (Inv.all (driven obj ch client sched) t).phase p r hwr
  have hphase' : (retro sched (fwr obj ch client sched) (fwv obj ch client sched) r).phase
      (clk sched (fwr obj ch client sched) t r) p = 6 := by
    have := hphase
    rw [show gcaClockH obj (fsched obj ch client sched).run.state (fsched obj ch client sched).actor t r
      = clk sched (fwr obj ch client sched) t r from gcaClockH_eq obj ch client sched t r] at this
    exact this
  have hph : ¬ ((frun obj ch client sched t).2.frame p).phase < 6 := by
    have : ((frun obj ch client sched t).2.frame p).phase
        = (retro sched (fwr obj ch client sched) (fwv obj ch client sched) r).phase
          (clk sched (fwr obj ch client sched) t r) p := hinv
    omega
  exact ⟨recv_valid obj ch client sched t hs hl' hph, fun q hq => local_other obj ch client sched t hs hq⟩

/-- A process's local state is constant while it is not scheduled. -/
theorem local_const {p : Fin n} {a : Nat} :
    ∀ d, (∀ w, a ≤ w → w < a + d → sched w ≠ some p) →
      (frun obj ch client sched (a + d)).1.localState p = (frun obj ch client sched a).1.localState p := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
      intro hno
      rw [show a + (d + 1) = (a + d) + 1 from by omega]
      have hih := ih (fun w hw hwd => hno w hw (by omega))
      cases hs : sched (a + d) with
      | none =>
          rw [show frun obj ch client sched (a + d + 1) = frun obj ch client sched (a + d) by
            rw [frun_succ, hs]; rfl]
          exact hih
      | some q =>
          have hq : p ≠ q := fun h => hno (a + d) (by omega) (by omega) (h ▸ hs)
          rw [local_other obj ch client sched (a + d) hs hq]
          exact hih

end Refinement

variable (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))

omit [DecidableEq Op] in
theorem command_none {l : Local (n := n) obj} (h : l.command obj = none) : ∃ seed, l = .idle seed := by
  cases l with
  | idle seed => exact ⟨seed, rfl⟩
  | _ => cases h

/-- **Operation liveness** follows from the scheduler not halting. -/
theorem fsched_opLive (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome) :
    (fsched obj ch client sched).OpLive := by
  obtain ⟨p, hp⟩ := WeakUniversal.Forward.often_some hlive
  have hopActor : ∀ t, sched (t + 1) = some p →
      ((frun obj ch client sched (t + 1)).1.localState p).command obj ≠ none →
      ((fsched obj ch client sched).opActor t).isSome = true := by
    intro t hs hc
    show (match sched (t + 1) with
      | none => none
      | some q => (HelpingUniversal.ledger obj (frun obj ch client sched (t + 1)).1).active q).isSome = true
    rw [hs]
    show (((frun obj ch client sched (t + 1)).1.localState p).command obj).isSome = true
    cases h : ((frun obj ch client sched (t + 1)).1.localState p).command obj with
    | none => exact absurd h hc
    | some _ => rfl
  intro N
  obtain ⟨t₁, ⟨ht₁, hs₁⟩, -⟩ := exists_least (fun w => N + 1 ≤ w ∧ sched w = some p) (hp (N + 1))
  obtain ⟨t, rfl⟩ : ∃ t, t₁ = t + 1 := ⟨t₁ - 1, by omega⟩
  by_cases hc : ((frun obj ch client sched (t + 1)).1.localState p).command obj = none
  · -- idle and scheduled: it invokes, and holds the command until it is next scheduled
    obtain ⟨seed, hidle⟩ := command_none obj hc
    obtain ⟨t₂, ⟨ht₂, hs₂⟩, hmin⟩ :=
      exists_least (fun w => t + 2 ≤ w ∧ sched w = some p) (hp (t + 2))
    have hinv : ((frun obj ch client sched (t + 2)).1.localState p).command obj ≠ none := by
      have hw : helpingRound obj ((frun obj ch client sched (t + 1)).1.localState p) = none := by
        rw [hidle]; rfl
      have he := fstep_prog obj ch client (frun obj ch client sched (t + 1)) hw
      rw [← hs₁, ← frun_succ] at he
      rw [he]
      simp [progStep, hidle, update, Local.command]
    have hconst := local_const obj ch client sched (a := t + 2) (p := p) (t₂ - (t + 2))
      (fun w hw hwd hsw => absurd (hmin w ⟨hw, hsw⟩) (by omega))
    rw [show t + 2 + (t₂ - (t + 2)) = t₂ from by omega] at hconst
    obtain ⟨t₃, rfl⟩ : ∃ t₃, t₂ = t₃ + 1 := ⟨t₂ - 1, by omega⟩
    exact ⟨t₃, by omega, hopActor t₃ hs₂ (by rw [hconst]; exact hinv)⟩
  · exact ⟨t, by omega, hopActor t hs₁ hc⟩

/-- **Refinement.**  Every run of the machine whose scheduler does not halt is
admitted by `algorithm3`. -/
theorem forward_admitted (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome) :
    algorithm3 obj n ((fsched obj ch client sched).execution (fsched_opLive obj ch client sched hlive)) :=
  ⟨fam obj ch client sched, fsched obj ch client sched, fsched_opLive obj ch client sched hlive,
    fsched_fair obj ch client sched, fam_waitFree obj ch client sched, rfl⟩

/-- Every run of the machine, halting or not, is linearizable by one growing chain. -/
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

end ConflictFreedom.HelpingUniversal.Forward

namespace ConflictFreedom
open HelpingUniversal.Forward
variable {State Op Response : Type} [DecidableEq Op]

/-- **Algorithm 3 as the machine runs it**: the executions of every non-halting
run of `frun`, for every client, every rule for the collect orders and
`trace(M_i)`, and every scheduler. -/
def forward3 (obj : Object State Op Response) (n : Nat) : Implementation n Op := fun e =>
  ∃ (client : Fin n → Nat → Op) (ch : Choices (n := n) obj) (sched : Nat → Option (Fin n))
    (hlive : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome),
    e = (fsched obj ch client sched).execution (fsched_opLive obj ch client sched hlive)

theorem forward3_admitted (obj : Object State Op Response) (n : Nat) :
    ∀ e, forward3 obj n e → algorithm3 obj n e := by
  rintro e ⟨client, ch, sched, hlive, rfl⟩
  exact forward_admitted obj ch client sched hlive

/-- **The machine's GCA objects meet the interface**: every execution of the
machine is an execution of Algorithm 3 over a GCA meeting the interface, so
every theorem proved over the interface applies to it. -/
theorem forward3_anyGCA (obj : Object State Op Response) (n : Nat) :
    ∀ e, forward3 obj n e → algorithm3AnyGCA obj n e :=
  fun e he => algorithm3_anyGCA obj n e (forward3_admitted obj n e he)

/-- **Algorithm 3, as the machine runs it, is conflict-free.** -/
theorem forward3_conflictFree (obj : Object State Op Response) (n : Nat) :
    ConflictFree (forward3 obj n) obj.Conflict :=
  fun e he => algorithm3_conflictFree obj n e (forward3_admitted obj n e he)

theorem forward3_nonempty (obj : Object State Op Response) (op : Op) (m : Nat) :
    ∃ e, forward3 obj (m + 1) e :=
  ⟨_, fun _ _ => op, Choices.inOrder obj, fun _ => some 0, fun N => ⟨N, Nat.le_refl _, rfl⟩, rfl⟩

end ConflictFreedom
