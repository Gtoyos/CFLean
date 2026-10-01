import CFLeanProof.GCAProtocol

/-! # Algorithm 2, run forward over atomic snapshot objects

The admitted model (`GlobalSchedule`) fixes every GCA round's inputs as data of a
`Family` chosen before the run; a program's `propose` step is enabled only when
its proposal equals that pre-ordained input.  This module removes the
pre-ordination for the GCA side.

* `GState` is the shared state of all GCA rounds at once: for each round `r` the
  two atomic snapshot objects `A_r` (inputs) and `B_r` (the pairs
  `(⊔ A_i^co, A_i = A_i^co)` of line 4), plus each process's *frame* — the stage
  it has reached in its current call, what its two scans returned, and the pair
  it computed for `B`.
* `gcaStep` is one scheduled step of a caller, one stage of Algorithm 2 per
  step: an atomic `update` or `scan` of `A_r` or `B_r`, or one of the two local
  calculations.  A caller uses only what its own scans returned.
* `frameOutput` is lines 6–8 of Algorithm 2 evaluated on the caller's frame:
  the meet of the flagged candidates it saw in `B`, or its own candidate, and
  the commit rule.

Nothing here refers to a protocol family.  The second half of the module drives
the machine along any run in which callers enter and leave rounds according to a
`Driven` discipline, *reconstructs* the per-round `GCA.Protocol` afterwards from
who took which round event when, and proves (`output_agrees`) that what the
machine hands a caller equals the timed-execution semantics
`GCA.Protocol.history` of the reconstructed protocol.  That is the fact the
refinement of the universal constructions rests on.

Snapshot operations are atomic.  That is the author's assumption — a wait-free
*linearizable* snapshot object — taken at face value: by linearizability each
update and scan takes effect at a single point.  `SnapshotStutter` separately
shows the admitted model tolerates implementations that take internal steps.

Line `k` of Algorithm 2 is the manuscript's label `line:gca:k`, typeset as
Line `k + 1`.
-/
namespace ConflictFreedom.ForwardGCA
open Object GCA

variable {S Op R : Type} (O : Object S Op R) (n : Nat)

/-- Pointwise update. -/
def fupdate {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- A caller's frame in its current GCA call: the stage it has reached, what its
`A` scan returned, the pair it computed for `B` (line 4), and what its `B` scan
returned. -/
structure Frame where
  phase : Nat
  aSnap : Fin n → Option O.Trace
  cand : O.Trace × Bool
  bSnap : Fin n → Option (O.Trace × Bool)

/-- The shared objects of every round — `A_r` holds inputs, `B_r` holds the
(candidate, compatibility flag) pairs of line 4 — and every process's frame. -/
structure GState where
  A : Nat → Fin n → Option O.Trace
  B : Nat → Fin n → Option (O.Trace × Bool)
  frame : Fin n → Frame O n

/-- The frame of a caller that has not started a call. -/
def Frame.fresh : Frame O n := ⟨0, fun _ => none, (O.emptyTrace, false), fun _ => none⟩

/-- Every snapshot slot `⊥`, every frame fresh. -/
def GState.initial : GState O n := ⟨fun _ _ => none, fun _ _ => none, fun _ => Frame.fresh O n⟩

namespace Frame
variable {O n} (fr : Frame O n)

/-- The processes whose `A` slot the caller's scan found written, in index order. -/
def aView : List (Fin n) := (List.finRange n).filter (fun q => (fr.aSnap q).isSome)

/-- The input traces the caller's `A` scan returned: `A_i` of line 2. -/
def aTraces : List O.Trace := fr.aView.map (fun q => (fr.aSnap q).getD O.emptyTrace)

/-- The processes whose `B` slot the caller's scan found written. -/
def bView : List (Fin n) := (List.finRange n).filter (fun q => (fr.bSnap q).isSome)

/-- The written `B` entry of `q`, as a pair. -/
def bEntry (q : Fin n) : O.Trace × Bool := (fr.bSnap q).getD (O.emptyTrace, false)

/-- The candidates of line 6: `{ b_k : b_k ≠ ⊥ ∧ c_k = true }`. -/
def flagged : List O.Trace := (fr.bView.filter (fun q => (fr.bEntry q).2)).map (fun q => (fr.bEntry q).1)

end Frame

variable [DecidableEq Op]

/-- One scheduled step of caller `p` in round `r` with input `v` — Algorithm 2,
one stage per step: line 1 (`A.update`), line 2 (`A.scan`), lines 3–4's local
calculation of `(⊔ A_i^co, A_i = A_i^co)`, line 4's `B.update`, line 5
(`B.scan`), and lines 6–8's local calculation.  The flag `A_i = A_i^co` is read
as `A_i` being compatible, as in `GCA.SnapshotExecution.Flag`. -/
noncomputable def gcaStep (g : GState O n) (p : Fin n) (r : Nat) (v : O.Trace) : GState O n :=
  match (g.frame p).phase with
  | 0 => { g with
      A := fupdate g.A r (fupdate (g.A r) p (some v))
      frame := fupdate g.frame p { g.frame p with phase := 1 } }
  | 1 => { g with
      frame := fupdate g.frame p { g.frame p with phase := 2, aSnap := g.A r } }
  | 2 => { g with
      frame := fupdate g.frame p { g.frame p with
        phase := 3
        cand := (O.gcaCandidate (g.frame p).aTraces,
          @decide (O.Compatible (fun s => s ∈ (g.frame p).aTraces)) (Classical.propDecidable _)) } }
  | 3 => { g with
      B := fupdate g.B r (fupdate (g.B r) p (some (g.frame p).cand))
      frame := fupdate g.frame p { g.frame p with phase := 4 } }
  | 4 => { g with
      frame := fupdate g.frame p { g.frame p with phase := 5, bSnap := g.B r } }
  | 5 => { g with frame := fupdate g.frame p { g.frame p with phase := 6 } }
  | _ => g

/-- After the caller consumes its output, its frame is fresh for the next call. -/
def resetFrame (g : GState O n) (p : Fin n) : GState O n :=
  { g with frame := fupdate g.frame p (Frame.fresh O n) }

/-- Line 6: the meet of the flagged candidates, or the caller's own candidate. -/
noncomputable def frameResult (fr : Frame O n) : O.Trace := by
  classical
  exact if h : ∃ s, s ∈ fr.flagged then O.traceGLB (fun s => s ∈ fr.flagged) h else fr.cand.1

/-- Lines 7–8. -/
def frameCommits (fr : Frame O n) (own : O.Trace) : Prop :=
  ((∀ q ∈ fr.aView, (fr.aSnap q).getD O.emptyTrace = own) ∧
      (∀ q ∈ fr.bView, (fr.bEntry q).1 = own)) ∨
    ((∀ q ∈ fr.aView,
        O.TracePrefix ((fr.aSnap q).getD O.emptyTrace) (frameResult O n fr) → q ∈ fr.bView) ∧
      ∀ q ∈ fr.bView, (fr.bEntry q).2 = true)

/-- What the caller returns: the output trace and the commit flag. -/
noncomputable def frameOutput (fr : Frame O n) (own : O.Trace) : O.Trace × Bool :=
  (frameResult O n fr, @decide (frameCommits O n fr own) (Classical.propDecidable _))

/-! ## Driving the machine along a run

A run supplies, at every global instant `t`, the scheduled process `act t`, the
round each process is blocked in (`wr t p`, `none` outside a call), and the
proposal it handed that call (`wv t p`). -/

section Driver
variable {O n}
variable (act : Nat → Option (Fin n)) (wr : Nat → Fin n → Option Nat)

/-- The round event at global instant `t`: a scheduled process that is inside a
call.  Same shape as `GlobalSchedule.gcaEvent`. -/
def ev (t : Nat) : Option (Nat × Fin n) :=
  match act t with
  | none => none
  | some p =>
      match wr t p with
      | none => none
      | some r => some (r, p)

/-- Round `r`'s own clock: the number of its events before `t`.  Same shape as
`GlobalSchedule.gcaClock`. -/
def clk : Nat → Nat → Nat
  | 0, _ => 0
  | (t + 1), r =>
      match ev act wr t with
      | some (r', _) => if r' = r then clk t r + 1 else clk t r
      | none => clk t r

omit [DecidableEq Op] in
theorem ev_spec {t : Nat} {p : Fin n} {r : Nat} (h1 : act t = some p) (h2 : wr t p = some r) :
    ev act wr t = some (r, p) := by
  simp [ev, h1, h2]

omit [DecidableEq Op] in
theorem ev_inv {t r : Nat} {p : Fin n} (h : ev act wr t = some (r, p)) :
    act t = some p ∧ wr t p = some r := by
  cases hact : act t with
  | none => simp [ev, hact] at h
  | some q =>
      cases hw : wr t q with
      | none => simp [ev, hact, hw] at h
      | some r' =>
          simp only [ev, hact, hw, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, hw⟩

omit [DecidableEq Op] in
theorem clk_succ_eq {t r : Nat} {p : Fin n} (h : ev act wr t = some (r, p)) :
    clk act wr (t + 1) r = clk act wr t r + 1 := by
  rw [clk, h]; simp

omit [DecidableEq Op] in
theorem clk_succ_ne {t r : Nat} (h : ∀ p, ev act wr t ≠ some (r, p)) :
    clk act wr (t + 1) r = clk act wr t r := by
  rw [clk]
  cases hev : ev act wr t with
  | none => rfl
  | some rp =>
      obtain ⟨r', p⟩ := rp
      have hne : ¬ r' = r := fun hr => h p (by rw [hev, hr])
      simp [hne]

omit [DecidableEq Op] in
theorem clk_step_le (t r : Nat) : clk act wr t r ≤ clk act wr (t + 1) r := by
  rw [clk]
  cases ev act wr t with
  | none => exact Nat.le_refl _
  | some rp =>
      obtain ⟨r', _⟩ := rp
      by_cases hr : r' = r <;> simp [hr]

omit [DecidableEq Op] in
theorem clk_mono {t u : Nat} (r : Nat) (h : t ≤ u) : clk act wr t r ≤ clk act wr u r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans ih (clk_step_le act wr (t + d) r)

omit [DecidableEq Op] in
/-- A round's events occupy distinct positions on its clock. -/
theorem clk_lt_of_event {t u r : Nat} {p : Fin n} (h : ev act wr t = some (r, p)) (htu : t < u) :
    clk act wr t r < clk act wr u r := by
  have h1 := clk_succ_eq act wr h
  have h2 := clk_mono act wr r (show t + 1 ≤ u by omega)
  omega

variable (wv : Nat → Fin n → O.Trace)

/-- `q` took part in round `r`: it was blocked in it at some instant. -/
def Waited (r : Nat) (q : Fin n) : Prop := ∃ t, wr t q = some r

/-- The participants of round `r`, in index order. -/
noncomputable def participants (r : Nat) : List (Fin n) := by
  classical
  exact (List.finRange n).filter (fun q => decide (Waited wr r q))

omit [DecidableEq Op] in
theorem mem_participants {r : Nat} {q : Fin n} : q ∈ participants wr r ↔ Waited wr r q := by
  classical
  simp [participants, List.mem_filter, List.mem_finRange]

/-- The input `q` gave round `r`, read off any instant it was blocked in it. -/
noncomputable def rinput (r : Nat) (q : Fin n) : O.Trace := by
  classical
  exact if h : Waited wr r q then wv (Classical.choose h) q else O.emptyTrace

/-- Round `r`'s event number `c` was taken by `p`. -/
def EventAt (r c : Nat) (p : Fin n) : Prop := ∃ t, ev act wr t = some (r, p) ∧ clk act wr t r = c

omit [DecidableEq Op] in
theorem eventAt_unique {r c : Nat} {p p' : Fin n} (h : EventAt act wr r c p)
    (h' : EventAt act wr r c p') : p = p' := by
  obtain ⟨t, ht, hc⟩ := h
  obtain ⟨t', ht', hc'⟩ := h'
  rcases Nat.lt_trichotomy t t' with hlt | rfl | hlt
  · have := clk_lt_of_event act wr ht hlt; omega
  · rw [ht] at ht'
    exact (Prod.mk.inj (Option.some.inj ht')).2
  · have := clk_lt_of_event act wr ht' hlt; omega

/-- The protocol's own actor sequence, read off the run. -/
noncomputable def ractor (r c : Nat) : Option (Fin n) := by
  classical
  exact if h : ∃ p, EventAt act wr r c p then some (Classical.choose h) else none

omit [DecidableEq Op] in
theorem ractor_spec {r c : Nat} {p : Fin n} (h : ractor act wr r c = some p) :
    EventAt act wr r c p := by
  classical
  unfold ractor at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    exact Classical.choose_spec hex
  · cases h

omit [DecidableEq Op] in
theorem ractor_of_eventAt {r c : Nat} {p : Fin n} (h : EventAt act wr r c p) :
    ractor act wr r c = some p := by
  classical
  have hex : ∃ p, EventAt act wr r c p := ⟨p, h⟩
  unfold ractor
  rw [dite_eq_left hex]
  exact congrArg some (eventAt_unique act wr (Classical.choose_spec hex) h)

omit [DecidableEq Op] in
theorem ractor_of_event {t r : Nat} {p : Fin n} (h : ev act wr t = some (r, p)) :
    ractor act wr r (clk act wr t r) = some p :=
  ractor_of_eventAt act wr ⟨t, h, rfl⟩

/-- **The protocol reconstructed from the run.**  Participants are the processes
that were ever blocked in the round, inputs are what they proposed, the actor
sequence is the order in which they took the round's events, and every snapshot
operation is acknowledged because snapshot operations are atomic. -/
noncomputable def retro (r : Nat) : GCA.Protocol O (Fin n) where
  participants := participants wr r
  input := rinput wr wv r
  actor := ractor act wr r
  actor_valid := by
    intro c p h
    obtain ⟨t, he, -⟩ := ractor_spec act wr h
    exact (mem_participants wr).mpr ⟨t, (ev_inv act wr he).2⟩
  acknowledged := fun _ => true

omit [DecidableEq Op] in
theorem retro_waitFree (r : Nat) : (retro act wr wv r).SnapshotWaitFree :=
  GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)

omit [DecidableEq Op] in
theorem retro_phase_succ (r c : Nat) (q : Fin n) :
    (retro act wr wv r).phase (c + 1) q =
      if ractor act wr r c = some q then GCA.Protocol.advance ((retro act wr wv r).phase c q) true
      else (retro act wr wv r).phase c q := rfl

omit [DecidableEq Op] in
theorem advance_true {k : Nat} (hk : k < 6) : GCA.Protocol.advance k true = k + 1 := by
  unfold GCA.Protocol.advance
  rw [ite_eq_left ⟨hk, Or.inr (Or.inr rfl)⟩]

omit [DecidableEq Op] in
theorem advance_six : GCA.Protocol.advance 6 true = 6 := by
  unfold GCA.Protocol.advance
  rw [ite_eq_right (by omega)]

end Driver

/-! ## Two facts about any `GCA.Protocol` -/

section ProtocolFacts
variable {O} {P : Type} [DecidableEq P] (e : GCA.Protocol O P)

omit [DecidableEq Op] in
/-- Having passed stage `k` by clock `c` is having exited it at an earlier clock. -/
theorem lt_phase_iff (k c : Nat) (q : P) :
    k < e.phase c q ↔ ∃ w, e.eventTime q k = some w ∧ w < c := by
  constructor
  · intro h
    obtain ⟨u, hu, hex⟩ := e.crossed h
    exact ⟨u, (e.eventTime_iff q k u).mpr hex, hu⟩
  · rintro ⟨w, hw, hwc⟩
    have hex := (e.eventTime_iff q k w).mp hw
    have := e.phase_mono (show w + 1 ≤ c by omega) q
    have := hex.2
    omega

omit [DecidableEq Op] in
theorem eventTime_of_advance {q : P} {k c : Nat} (h1 : e.phase c q = k) (h2 : e.phase (c + 1) q = k + 1) :
    e.eventTime q k = some c :=
  (e.eventTime_iff q k c).mpr ⟨h1, h2⟩

end ProtocolFacts

/-! ## The discipline a run must follow -/

section Discipline
variable {O n}
variable (act : Nat → Option (Fin n)) (wr : Nat → Fin n → Option Nat)
  (wv : Nat → Fin n → O.Trace) (gs : Nat → GState O n)

/-- **How a run drives the GCA machine.**  Only the scheduled process moves; a
caller inside a call below the last stage takes a GCA step and stays in the
call with the same proposal; a caller at the last stage consumes its output and
leaves; and a process outside any call takes a program step that leaves the GCA
state alone and, if it enters a round, enters a round it has never been in. -/
structure Driven : Prop where
  init_gs : gs 0 = GState.initial O n
  init_wr : ∀ p, wr 0 p = none
  idle : ∀ t, act t = none →
    gs (t + 1) = gs t ∧ ∀ q, wr (t + 1) q = wr t q ∧ wv (t + 1) q = wv t q
  other : ∀ t p q, act t = some p → q ≠ p → wr (t + 1) q = wr t q ∧ wv (t + 1) q = wv t q
  gca : ∀ t p r, act t = some p → wr t p = some r → ((gs t).frame p).phase < 6 →
    gs (t + 1) = gcaStep O n (gs t) p r (wv t p) ∧ wr (t + 1) p = some r ∧ wv (t + 1) p = wv t p
  recv : ∀ t p r, act t = some p → wr t p = some r → ¬ ((gs t).frame p).phase < 6 →
    gs (t + 1) = resetFrame O n (gs t) p ∧ wr (t + 1) p = none
  prog : ∀ t p, act t = some p → wr t p = none →
    gs (t + 1) = gs t ∧ ∀ r, wr (t + 1) p = some r → ∀ u, u ≤ t → wr u p ≠ some r

variable {act wr wv gs}

theorem Driven.unscheduled (hd : Driven act wr wv gs) {t : Nat} {q : Fin n}
    (hq : act t ≠ some q) : wr (t + 1) q = wr t q ∧ wv (t + 1) q = wv t q := by
  cases hact : act t with
  | none => exact (hd.idle t hact).2 q
  | some p => exact hd.other t p q hact (fun he => hq (he ▸ hact))

/-- A round is entered only through a program step, and only if it is new. -/
theorem Driven.entry (hd : Driven act wr wv gs) {t : Nat} {q : Fin n} {r : Nat}
    (h0 : wr t q ≠ some r) (h1 : wr (t + 1) q = some r) : ∀ u, u ≤ t → wr u q ≠ some r := by
  by_cases hact : act t = some q
  · cases hw : wr t q with
    | none => exact (hd.prog t q hact hw).2 r h1
    | some r' =>
        exfalso
        by_cases hph : ((gs t).frame q).phase < 6
        · have := (hd.gca t q r' hact hw hph).2.1
          rw [h1] at this
          exact h0 (hw.trans (congrArg some (Option.some.inj this).symm))
        · have := (hd.recv t q r' hact hw hph).2
          rw [h1] at this
          cases this
  · exact absurd ((hd.unscheduled hact).1.symm.trans h1) h0

/-- Inside a round, the proposal does not change from one instant to the next. -/
theorem Driven.stay (hd : Driven act wr wv gs) {t : Nat} {q : Fin n} {r : Nat}
    (h0 : wr t q = some r) (h1 : wr (t + 1) q = some r) : wv (t + 1) q = wv t q := by
  by_cases hact : act t = some q
  · by_cases hph : ((gs t).frame q).phase < 6
    · exact (hd.gca t q r hact h0 hph).2.2
    · have := (hd.recv t q r hact h0 hph).2
      rw [h1] at this
      cases this
  · exact (hd.unscheduled hact).2

/-- **A caller never returns to a round it has left.** -/
theorem Driven.never_return (hd : Driven act wr wv gs) {u : Nat} {q : Fin n} {r : Nat}
    (h0 : wr u q = some r) (h1 : wr (u + 1) q ≠ some r) : ∀ d, wr (u + 1 + d) q ≠ some r := by
  intro d
  induction d with
  | zero => exact h1
  | succ d ih =>
      intro hs
      exact hd.entry ih (by rw [show u + 1 + (d + 1) = (u + 1 + d) + 1 from by omega] at hs; exact hs)
        u (by omega) h0

/-- **A caller's time in a round is one stretch, with one proposal.** -/
theorem Driven.episode (hd : Driven act wr wv gs) {t t' : Nat} {q : Fin n} {r : Nat}
    (h : wr t q = some r) (h' : wr t' q = some r) : wv t q = wv t' q := by
  suffices key : ∀ {a b : Nat}, a ≤ b → wr a q = some r → wr b q = some r → wv a q = wv b q by
    rcases Nat.le_total t t' with hle | hle
    · exact key hle h h'
    · exact (key hle h' h).symm
  intro a b hab ha hb
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  have hall : ∀ e, e ≤ d → wr (a + e) q = some r ∧ wv (a + e) q = wv a q := by
    intro e
    induction e with
    | zero => intro _; exact ⟨ha, rfl⟩
    | succ e ih =>
        intro he
        obtain ⟨hw, hv⟩ := ih (by omega)
        have hstay : wr (a + e + 1) q = some r := by
          apply Classical.byContradiction
          intro hn
          have := hd.never_return hw hn (d - e - 1)
          rw [show a + e + 1 + (d - e - 1) = a + d from by omega] at this
          exact this hb
        refine ⟨hstay, ?_⟩
        rw [show a + (e + 1) = a + e + 1 from by omega, hd.stay hw hstay, hv]
  exact (hall d (Nat.le_refl d)).2.symm

/-- The reconstructed input is the proposal held at any instant inside the round. -/
theorem Driven.rinput_eq (hd : Driven act wr wv gs) {t : Nat} {q : Fin n} {r : Nat}
    (h : wr t q = some r) : rinput wr wv r q = wv t q := by
  classical
  have hw : Waited wr r q := ⟨t, h⟩
  unfold rinput
  rw [dite_eq_left hw]
  exact hd.episode (Classical.choose_spec hw) h

omit [DecidableEq Op] in
/-- A caller has taken no event of a round it has not yet entered. -/
theorem fresh_phase {q : Fin n} {r : Nat} :
    ∀ t, (∀ u, u < t → wr u q ≠ some r) → (retro act wr wv r).phase (clk act wr t r) q = 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro hnot
      have ih' := ih (fun u hu => hnot u (by omega))
      cases hev : ev act wr t with
      | none =>
          rw [clk_succ_ne act wr (fun p h => by rw [hev] at h; cases h)]
          exact ih'
      | some rp =>
          obtain ⟨r', p⟩ := rp
          by_cases hr : r' = r
          · subst hr
            rw [clk_succ_eq act wr hev, retro_phase_succ, ractor_of_event act wr hev]
            have hpq : p ≠ q := by
              intro he
              subst he
              exact hnot t (by omega) (ev_inv act wr hev).2
            rw [ite_eq_right (fun h => hpq (Option.some.inj h)), ih']
          · rw [clk_succ_ne act wr (fun p' h => by
              rw [hev] at h
              exact hr (Prod.mk.inj (Option.some.inj h)).1)]
            exact ih'

end Discipline

/-! ## One GCA step, and a reset -/

section StepFacts
variable {O n} (g : GState O n) (p : Fin n) (r : Nat) (v : O.Trace)

theorem gcaStep_A : (gcaStep O n g p r v).A =
    if (g.frame p).phase = 0 then fupdate g.A r (fupdate (g.A r) p (some v)) else g.A := by
  unfold gcaStep; split <;> simp_all

theorem gcaStep_B : (gcaStep O n g p r v).B =
    if (g.frame p).phase = 3 then fupdate g.B r (fupdate (g.B r) p (some (g.frame p).cand))
    else g.B := by
  unfold gcaStep; split <;> simp_all

theorem gcaStep_frame_ne {q : Fin n} (hq : q ≠ p) : (gcaStep O n g p r v).frame q = g.frame q := by
  unfold gcaStep; split <;> simp [fupdate, hq]

theorem gcaStep_phase (hk : (g.frame p).phase < 6) :
    ((gcaStep O n g p r v).frame p).phase = (g.frame p).phase + 1 := by
  unfold gcaStep; split <;> simp_all [fupdate] <;> omega

theorem gcaStep_aSnap : ((gcaStep O n g p r v).frame p).aSnap =
    if (g.frame p).phase = 1 then g.A r else (g.frame p).aSnap := by
  unfold gcaStep; split <;> simp_all [fupdate]

theorem gcaStep_cand : ((gcaStep O n g p r v).frame p).cand =
    if (g.frame p).phase = 2 then
      (O.gcaCandidate (g.frame p).aTraces,
        @decide (O.Compatible (fun s => s ∈ (g.frame p).aTraces)) (Classical.propDecidable _))
    else (g.frame p).cand := by
  unfold gcaStep; split <;> simp_all [fupdate]

theorem gcaStep_bSnap : ((gcaStep O n g p r v).frame p).bSnap =
    if (g.frame p).phase = 4 then g.B r else (g.frame p).bSnap := by
  unfold gcaStep; split <;> simp_all [fupdate]

omit [DecidableEq Op] in
theorem resetFrame_A : (resetFrame O n g p).A = g.A := rfl

omit [DecidableEq Op] in
theorem resetFrame_B : (resetFrame O n g p).B = g.B := rfl

omit [DecidableEq Op] in
theorem resetFrame_frame (q : Fin n) :
    (resetFrame O n g p).frame q = if q = p then Frame.fresh O n else g.frame q := rfl

end StepFacts

/-! ## A caller's scans are the reconstructed views -/

section Views
variable {O n}
variable (act : Nat → Option (Fin n)) (wr : Nat → Fin n → Option Nat) (wv : Nat → Fin n → O.Trace)

/-- The pair a participant writes to `B` in the reconstruction (line 4). -/
noncomputable def rcand (r : Nat) (q : Fin n) : O.Trace × Bool :=
  ((retro act wr wv r).timed.views.candidate q,
    @decide ((retro act wr wv r).timed.views.Flag q) (Classical.propDecidable _))

omit [DecidableEq Op] in
/-- Whoever wrote before some scan took part in the round. -/
theorem waited_of_seen {r : Nat} {q : Fin n} {w : Option Nat} {k : Nat}
    (h : TimedExecution.Seen ((retro act wr wv r).eventTime q k) w) : Waited wr r q := by
  obtain ⟨c, _, hc, _, _⟩ := h
  have hex := ((retro act wr wv r).eventTime_iff q k c).mp hc
  have hact := (retro act wr wv r).exits_actor hex
  obtain ⟨t, he, -⟩ := ractor_spec act wr hact
  exact ⟨t, (ev_inv act wr he).2⟩

omit [DecidableEq Op] in
theorem filter_finRange_congr (P Q : Fin n → Bool) (h : ∀ q, P q = true ↔ Q q = true) :
    (List.finRange n).filter P = (List.finRange n).filter Q :=
  List.filter_congr (fun q _ => Bool.eq_iff_iff.mpr (h q))

omit [DecidableEq Op] in
/-- A snapshot of write-once slots, as a filter of the process indices. -/
theorem snapshot_eq {r : Nat} (k : Nat) (read : Option Nat) :
    TimedExecution.snapshot (participants wr r) (fun q => (retro act wr wv r).eventTime q k) read
      = (List.finRange n).filter (fun q => @decide
          (TimedExecution.Seen ((retro act wr wv r).eventTime q k) read)
          (Classical.propDecidable _)) := by
  classical
  unfold TimedExecution.snapshot participants
  rw [List.filter_filter]
  apply filter_finRange_congr
  intro q
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, -⟩; exact hs
  · intro hs; exact ⟨hs, waited_of_seen act wr wv hs⟩

omit [DecidableEq Op] in
/-- **The `A` scan a caller holds is its reconstructed `A` view.** -/
theorem frame_aView {fr : Frame O n} {r : Nat} {p : Fin n}
    (hseen : ∀ q, (fr.aSnap q).isSome = true ↔
      TimedExecution.Seen ((retro act wr wv r).timed.writeA q) ((retro act wr wv r).timed.readA p)) :
    fr.aView = (retro act wr wv r).timed.views.aView p := by
  classical
  show _ = TimedExecution.snapshot (participants wr r)
    (fun q => (retro act wr wv r).eventTime q 0) ((retro act wr wv r).eventTime p 1)
  rw [snapshot_eq act wr wv 0]
  unfold Frame.aView
  apply filter_finRange_congr
  intro q
  rw [hseen q]
  simp only [decide_eq_true_eq]
  rfl

omit [DecidableEq Op] in
theorem frame_aTraces {fr : Frame O n} {r : Nat} {p : Fin n}
    (hval : ∀ q, fr.aSnap q = none ∨ fr.aSnap q = some (rinput wr wv r q))
    (hseen : ∀ q, (fr.aSnap q).isSome = true ↔
      TimedExecution.Seen ((retro act wr wv r).timed.writeA q) ((retro act wr wv r).timed.readA p)) :
    fr.aTraces = (retro act wr wv r).timed.views.aTraces p := by
  unfold Frame.aTraces SnapshotExecution.aTraces
  rw [← frame_aView act wr wv hseen]
  apply List.map_congr_left
  intro q hq
  have hsome : (fr.aSnap q).isSome = true := by
    unfold Frame.aView at hq
    exact (List.mem_filter.mp hq).2
  rcases hval q with h | h
  · rw [h] at hsome; cases hsome
  · rw [h]; rfl

omit [DecidableEq Op] in
theorem frame_bView {fr : Frame O n} {r : Nat} {p : Fin n}
    (hseen : ∀ q, (fr.bSnap q).isSome = true ↔
      TimedExecution.Seen ((retro act wr wv r).timed.writeB q) ((retro act wr wv r).timed.readB p)) :
    fr.bView = (retro act wr wv r).timed.views.bView p := by
  classical
  show _ = TimedExecution.snapshot (participants wr r)
    (fun q => (retro act wr wv r).eventTime q 3) ((retro act wr wv r).eventTime p 4)
  rw [snapshot_eq act wr wv 3]
  unfold Frame.bView
  apply filter_finRange_congr
  intro q
  rw [hseen q]
  simp only [decide_eq_true_eq]
  rfl

/-- **The flagged candidates a caller holds are the reconstructed ones.** -/
theorem frame_flagged_mem {fr : Frame O n} {r : Nat} {p : Fin n}
    (hval : ∀ q, fr.bSnap q = none ∨ fr.bSnap q = some (rcand act wr wv r q))
    (hseen : ∀ q, (fr.bSnap q).isSome = true ↔
      TimedExecution.Seen ((retro act wr wv r).timed.writeB q) ((retro act wr wv r).timed.readB p))
    (s : O.Trace) :
    s ∈ fr.flagged ↔ s ∈ O.gcaFlagged ((retro act wr wv r).timed.views.bViews p) := by
  classical
  have hentry : ∀ q ∈ fr.bView, fr.bEntry q = rcand act wr wv r q := by
    intro q hq
    have hsome : (fr.bSnap q).isSome = true := (List.mem_filter.mp hq).2
    rcases hval q with h | h
    · rw [h] at hsome; cases hsome
    · unfold Frame.bEntry; rw [h]; rfl
  rw [Object.gcaFlagged_mem_iff]
  unfold Frame.flagged
  rw [List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hqv, hflag⟩ := List.mem_filter.mp hq
    rw [hentry q hqv] at hflag ⊢
    refine ⟨(retro act wr wv r).timed.views.aTraces q, ?_, ?_, rfl⟩
    · unfold SnapshotExecution.bViews
      rw [← frame_bView act wr wv hseen]
      exact List.mem_map.mpr ⟨q, hqv, rfl⟩
    · unfold rcand at hflag
      exact of_decide_eq_true hflag
  · rintro ⟨S, hS, hc, rfl⟩
    unfold SnapshotExecution.bViews at hS
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hS
    rw [← frame_bView act wr wv hseen] at hq
    refine ⟨q, List.mem_filter.mpr ⟨hq, ?_⟩, ?_⟩
    · rw [hentry q hq]; unfold rcand; exact decide_eq_true hc
    · rw [hentry q hq]; rfl

end Views

/-! ## The invariant: the machine's state is the reconstructed protocol's -/

section Invariant
variable {O n}

/-- At instant `t`, every snapshot object and every frame is what the
reconstructed protocol says it is on the round's own clock. -/
structure Inv (act : Nat → Option (Fin n)) (wr : Nat → Fin n → Option Nat)
    (wv : Nat → Fin n → O.Trace) (gs : Nat → GState O n) (t : Nat) : Prop where
  fresh : ∀ q, wr t q = none → ((gs t).frame q).phase = 0
  phase : ∀ q r, wr t q = some r →
    ((gs t).frame q).phase = (retro act wr wv r).phase (clk act wr t r) q
  A : ∀ r q, (gs t).A r q =
    if 1 ≤ (retro act wr wv r).phase (clk act wr t r) q then some (rinput wr wv r q) else none
  B : ∀ r q, (gs t).B r q =
    if 4 ≤ (retro act wr wv r).phase (clk act wr t r) q then some (rcand act wr wv r q) else none
  aVal : ∀ q r, wr t q = some r → 2 ≤ ((gs t).frame q).phase → ∀ q',
    ((gs t).frame q).aSnap q' = none ∨ ((gs t).frame q).aSnap q' = some (rinput wr wv r q')
  aSeen : ∀ q r, wr t q = some r → 2 ≤ ((gs t).frame q).phase → ∀ q',
    (((gs t).frame q).aSnap q').isSome = true ↔
      TimedExecution.Seen ((retro act wr wv r).timed.writeA q') ((retro act wr wv r).timed.readA q)
  cand : ∀ q r, wr t q = some r → 3 ≤ ((gs t).frame q).phase →
    ((gs t).frame q).cand = rcand act wr wv r q
  bVal : ∀ q r, wr t q = some r → 5 ≤ ((gs t).frame q).phase → ∀ q',
    ((gs t).frame q).bSnap q' = none ∨ ((gs t).frame q).bSnap q' = some (rcand act wr wv r q')
  bSeen : ∀ q r, wr t q = some r → 5 ≤ ((gs t).frame q).phase → ∀ q',
    (((gs t).frame q).bSnap q').isSome = true ↔
      TimedExecution.Seen ((retro act wr wv r).timed.writeB q') ((retro act wr wv r).timed.readB q)

variable {act : Nat → Option (Fin n)} {wr : Nat → Fin n → Option Nat}
  {wv : Nat → Fin n → O.Trace} {gs : Nat → GState O n}

theorem Inv.initial (hd : Driven act wr wv gs) : Inv act wr wv gs 0 := by
  have hg := hd.init_gs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q _; rw [hg]; rfl
  · intro q r h; rw [hd.init_wr q] at h; cases h
  · intro r q; rw [hg]; rfl
  · intro r q; rw [hg]; rfl
  · intro q r h; rw [hd.init_wr q] at h; cases h
  · intro q r h; rw [hd.init_wr q] at h; cases h
  · intro q r h; rw [hd.init_wr q] at h; cases h
  · intro q r h; rw [hd.init_wr q] at h; cases h
  · intro q r h; rw [hd.init_wr q] at h; cases h

/-- No event, no change. -/
theorem Inv.step_idle (hd : Driven act wr wv gs) {t : Nat} (hi : Inv act wr wv gs t)
    (hact : act t = none) : Inv act wr wv gs (t + 1) := by
  obtain ⟨hg, hw⟩ := hd.idle t hact
  have hnoev : ∀ r p, ev act wr t ≠ some (r, p) := by
    intro r p h; rw [(ev_inv act wr h).1] at hact; cases hact
  have hclk : ∀ r, clk act wr (t + 1) r = clk act wr t r :=
    fun r => clk_succ_ne act wr (hnoev r)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q h; rw [hg]; exact hi.fresh q ((hw q).1 ▸ h)
  · intro q r h; rw [hg, hclk]; exact hi.phase q r ((hw q).1 ▸ h)
  · intro r q; rw [hg, hclk]; exact hi.A r q
  · intro r q; rw [hg, hclk]; exact hi.B r q
  · intro q r h; rw [hg]; exact hi.aVal q r ((hw q).1 ▸ h)
  · intro q r h; rw [hg]; exact hi.aSeen q r ((hw q).1 ▸ h)
  · intro q r h; rw [hg]; exact hi.cand q r ((hw q).1 ▸ h)
  · intro q r h; rw [hg]; exact hi.bVal q r ((hw q).1 ▸ h)
  · intro q r h; rw [hg]; exact hi.bSeen q r ((hw q).1 ▸ h)

/-- A program step outside any call. -/
theorem Inv.step_prog (hd : Driven act wr wv gs) {t : Nat} (hi : Inv act wr wv gs t)
    {p : Fin n} (hact : act t = some p) (hwp : wr t p = none) : Inv act wr wv gs (t + 1) := by
  obtain ⟨hg, hnew⟩ := hd.prog t p hact hwp
  have hnoev : ∀ r q, ev act wr t ≠ some (r, q) := by
    intro r q h
    obtain ⟨h1, h2⟩ := ev_inv act wr h
    rw [hact] at h1
    rw [← Option.some.inj h1, hwp] at h2
    cases h2
  have hclk : ∀ r, clk act wr (t + 1) r = clk act wr t r :=
    fun r => clk_succ_ne act wr (hnoev r)
  have hwq : ∀ q, q ≠ p → wr (t + 1) q = wr t q := fun q hq => (hd.other t p q hact hq).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q h
    rw [hg]
    by_cases hq : q = p
    · subst hq; exact hi.fresh q hwp
    · exact hi.fresh q ((hwq q hq) ▸ h)
  · intro q r h
    rw [hg]
    by_cases hq : q = p
    · subst hq
      rw [hi.fresh q hwp]
      exact (fresh_phase (t + 1) (fun u hu => hnew r h u (by omega))).symm
    · rw [hclk]; exact hi.phase q r ((hwq q hq) ▸ h)
  · intro r q; rw [hg, hclk]; exact hi.A r q
  · intro r q; rw [hg, hclk]; exact hi.B r q
  · intro q r h hph
    rw [hg] at hph ⊢
    by_cases hq : q = p
    · subst hq; rw [hi.fresh q hwp] at hph; omega
    · exact hi.aVal q r ((hwq q hq) ▸ h) hph
  · intro q r h hph
    rw [hg] at hph ⊢
    by_cases hq : q = p
    · subst hq; rw [hi.fresh q hwp] at hph; omega
    · exact hi.aSeen q r ((hwq q hq) ▸ h) hph
  · intro q r h hph
    rw [hg] at hph ⊢
    by_cases hq : q = p
    · subst hq; rw [hi.fresh q hwp] at hph; omega
    · exact hi.cand q r ((hwq q hq) ▸ h) hph
  · intro q r h hph
    rw [hg] at hph ⊢
    by_cases hq : q = p
    · subst hq; rw [hi.fresh q hwp] at hph; omega
    · exact hi.bVal q r ((hwq q hq) ▸ h) hph
  · intro q r h hph
    rw [hg] at hph ⊢
    by_cases hq : q = p
    · subst hq; rw [hi.fresh q hwp] at hph; omega
    · exact hi.bSeen q r ((hwq q hq) ▸ h) hph

omit [DecidableEq Op] in
theorem seen_some_iff {P : Type} [DecidableEq P] (e : GCA.Protocol O P) (k c : Nat) (q : P) :
    TimedExecution.Seen (e.eventTime q k) (some c) ↔ k < e.phase c q := by
  rw [lt_phase_iff]
  constructor
  · rintro ⟨w, r, hw, hr, hlt⟩
    exact ⟨w, hw, (Option.some.inj hr) ▸ hlt⟩
  · rintro ⟨w, hw, hlt⟩
    exact ⟨w, c, hw, rfl, hlt⟩

omit [DecidableEq Op] in
/-- Round clocks and reconstructed phases after one round event. -/
theorem phase_after_event {t r₀ : Nat} {p : Fin n} (hev : ev act wr t = some (r₀, p)) (r : Nat)
    (q : Fin n) (hne : ¬ (r = r₀ ∧ q = p)) :
    (retro act wr wv r).phase (clk act wr (t + 1) r) q = (retro act wr wv r).phase (clk act wr t r) q := by
  by_cases hr : r = r₀
  · subst hr
    have hq : q ≠ p := fun h => hne ⟨rfl, h⟩
    rw [clk_succ_eq act wr hev, retro_phase_succ, ractor_of_event act wr hev,
      ite_eq_right (fun h => hq (Option.some.inj h).symm)]
  · rw [clk_succ_ne act wr (fun q h => by
      rw [hev] at h
      exact hr (Prod.mk.inj (Option.some.inj h)).1.symm)]

omit [DecidableEq Op] in
theorem phase_after_own_event {t r₀ : Nat} {p : Fin n} (hev : ev act wr t = some (r₀, p)) :
    (retro act wr wv r₀).phase (clk act wr (t + 1) r₀) p
      = GCA.Protocol.advance ((retro act wr wv r₀).phase (clk act wr t r₀) p) true := by
  rw [clk_succ_eq act wr hev, retro_phase_succ, ractor_of_event act wr hev, ite_eq_left rfl]

/-- The caller consumes its output and leaves. -/
theorem Inv.step_recv (hd : Driven act wr wv gs) {t : Nat} (hi : Inv act wr wv gs t)
    {p : Fin n} {r₀ : Nat} (hact : act t = some p) (hwp : wr t p = some r₀)
    (hph : ¬ ((gs t).frame p).phase < 6) : Inv act wr wv gs (t + 1) := by
  obtain ⟨hg, hwp'⟩ := hd.recv t p r₀ hact hwp hph
  have hev := ev_spec act wr hact hwp
  have hwq : ∀ q, q ≠ p → wr (t + 1) q = wr t q := fun q hq => (hd.other t p q hact hq).1
  have hsix : (retro act wr wv r₀).phase (clk act wr t r₀) p = 6 := by
    have h1 := hi.phase p r₀ hwp
    have h2 := (retro act wr wv r₀).phase_le_six (clk act wr t r₀) p
    omega
  have hPH : ∀ r q, (retro act wr wv r).phase (clk act wr (t + 1) r) q
      = (retro act wr wv r).phase (clk act wr t r) q := by
    intro r q
    by_cases hrq : r = r₀ ∧ q = p
    · obtain ⟨rfl, rfl⟩ := hrq
      rw [phase_after_own_event hev, hsix, advance_six]
    · exact phase_after_event hev r q hrq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q h
    rw [hg, resetFrame_frame]
    by_cases hq : q = p
    · rw [ite_eq_left hq]; rfl
    · rw [ite_eq_right hq]; exact hi.fresh q ((hwq q hq) ▸ h)
  · intro q r h
    by_cases hq : q = p
    · subst hq; rw [hwp'] at h; cases h
    · rw [hg, resetFrame_frame, ite_eq_right hq, hPH]; exact hi.phase q r ((hwq q hq) ▸ h)
  · intro r q; rw [hg, resetFrame_A, hPH]; exact hi.A r q
  · intro r q; rw [hg, resetFrame_B, hPH]; exact hi.B r q
  · intro q r h hph'
    by_cases hq : q = p
    · subst hq; rw [hwp'] at h; cases h
    · rw [hg, resetFrame_frame, ite_eq_right hq] at hph' ⊢; exact hi.aVal q r ((hwq q hq) ▸ h) hph'
  · intro q r h hph'
    by_cases hq : q = p
    · subst hq; rw [hwp'] at h; cases h
    · rw [hg, resetFrame_frame, ite_eq_right hq] at hph' ⊢; exact hi.aSeen q r ((hwq q hq) ▸ h) hph'
  · intro q r h hph'
    by_cases hq : q = p
    · subst hq; rw [hwp'] at h; cases h
    · rw [hg, resetFrame_frame, ite_eq_right hq] at hph' ⊢; exact hi.cand q r ((hwq q hq) ▸ h) hph'
  · intro q r h hph'
    by_cases hq : q = p
    · subst hq; rw [hwp'] at h; cases h
    · rw [hg, resetFrame_frame, ite_eq_right hq] at hph' ⊢; exact hi.bVal q r ((hwq q hq) ▸ h) hph'
  · intro q r h hph'
    by_cases hq : q = p
    · subst hq; rw [hwp'] at h; cases h
    · rw [hg, resetFrame_frame, ite_eq_right hq] at hph' ⊢; exact hi.bSeen q r ((hwq q hq) ▸ h) hph'

/-- **One GCA step of a caller** — an atomic update or scan of `A_r` or `B_r`, or
a local calculation — keeps the machine and the reconstruction in step. -/
theorem Inv.step_gca (hd : Driven act wr wv gs) {t : Nat} (hi : Inv act wr wv gs t)
    {p : Fin n} {r₀ : Nat} (hact : act t = some p) (hwp : wr t p = some r₀)
    (hph : ((gs t).frame p).phase < 6) : Inv act wr wv gs (t + 1) := by
  obtain ⟨hg, hwp', -⟩ := hd.gca t p r₀ hact hwp hph
  obtain ⟨k, hk⟩ : ∃ k, ((gs t).frame p).phase = k := ⟨_, rfl⟩
  have hk6 : k < 6 := hk ▸ hph
  have hev := ev_spec act wr hact hwp
  have hwq : ∀ q, q ≠ p → wr (t + 1) q = wr t q := fun q hq => (hd.other t p q hact hq).1
  have hcur : (retro act wr wv r₀).phase (clk act wr t r₀) p = k := (hi.phase p r₀ hwp).symm.trans hk
  have hnext : (retro act wr wv r₀).phase (clk act wr (t + 1) r₀) p = k + 1 := by
    rw [phase_after_own_event hev, hcur, advance_true hk6]
  have hnext' : (retro act wr wv r₀).phase (clk act wr t r₀ + 1) p = k + 1 := by
    rw [← clk_succ_eq act wr hev]; exact hnext
  have hrinput : rinput wr wv r₀ p = wv t p := hd.rinput_eq hwp
  have hframe : ∀ q, q ≠ p → (gs (t + 1)).frame q = (gs t).frame q := by
    intro q hq; rw [hg]; exact gcaStep_frame_ne (gs t) p r₀ (wv t p) hq
  have hphase' : ((gs (t + 1)).frame p).phase = k + 1 := by
    rw [hg, gcaStep_phase (gs t) p r₀ (wv t p) hph, hk]
  have hwpr : ∀ r, wr (t + 1) p = some r → r = r₀ := by
    intro r h; rw [hwp'] at h; exact (Option.some.inj h).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- fresh
    intro q h
    by_cases hq : q = p
    · subst hq; rw [hwp'] at h; cases h
    · rw [hframe q hq]; exact hi.fresh q ((hwq q hq) ▸ h)
  · -- phase
    intro q r h
    by_cases hq : q = p
    · subst hq; obtain rfl := hwpr r h; rw [hphase', hnext]
    · rw [hframe q hq, phase_after_event hev r q (fun h' => hq h'.2)]
      exact hi.phase q r ((hwq q hq) ▸ h)
  · -- A
    intro r q
    rw [hg, gcaStep_A]
    by_cases hrq : r = r₀ ∧ q = p
    · obtain ⟨rfl, rfl⟩ := hrq
      rw [hnext]
      by_cases hk0 : k = 0
      · subst hk0
        rw [ite_eq_left hk, ite_eq_left (by omega)]
        simp [fupdate, hrinput]
      · rw [ite_eq_right (by rw [hk]; exact hk0), hi.A r q, hcur, ite_eq_left (by omega), ite_eq_left (by omega)]
    · rw [phase_after_event hev r q hrq]
      have hA : (if ((gs t).frame p).phase = 0
          then fupdate (gs t).A r₀ (fupdate ((gs t).A r₀) p (some (wv t p))) else (gs t).A) r q
          = (gs t).A r q := by
        split
        · by_cases hr : r = r₀
          · subst hr
            have hq : q ≠ p := fun h => hrq ⟨rfl, h⟩
            simp [fupdate, hq]
          · simp [fupdate, hr]
        · rfl
      rw [hA]; exact hi.A r q
  · -- B
    intro r q
    rw [hg, gcaStep_B]
    by_cases hrq : r = r₀ ∧ q = p
    · obtain ⟨rfl, rfl⟩ := hrq
      rw [hnext]
      by_cases hk3 : k = 3
      · subst hk3
        rw [ite_eq_left hk, ite_eq_left (by omega), hi.cand q r hwp (by omega)]
        simp [fupdate]
      · rw [ite_eq_right (by rw [hk]; exact hk3), hi.B r q, hcur]
        by_cases h4 : 4 ≤ k
        · rw [ite_eq_left h4, ite_eq_left (by omega)]
        · rw [ite_eq_right h4, ite_eq_right (by omega)]
    · rw [phase_after_event hev r q hrq]
      have hB : (if ((gs t).frame p).phase = 3
          then fupdate (gs t).B r₀ (fupdate ((gs t).B r₀) p (some ((gs t).frame p).cand))
          else (gs t).B) r q = (gs t).B r q := by
        split
        · by_cases hr : r = r₀
          · subst hr
            have hq : q ≠ p := fun h => hrq ⟨rfl, h⟩
            simp [fupdate, hq]
          · simp [fupdate, hr]
        · rfl
      rw [hB]; exact hi.B r q
  · -- aVal
    intro q r h hph'
    by_cases hq : q = p
    · subst hq
      obtain rfl := hwpr r h
      rw [hphase'] at hph'
      intro q'
      rw [hg, gcaStep_aSnap]
      by_cases hk1 : k = 1
      · rw [ite_eq_left (hk.trans hk1), hi.A r q']
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
      · rw [ite_eq_right (by rw [hk]; exact hk1)]
        exact hi.aVal q r hwp (by omega) q'
    · rw [hframe q hq] at hph' ⊢; exact hi.aVal q r ((hwq q hq) ▸ h) hph'
  · -- aSeen
    intro q r h hph'
    by_cases hq : q = p
    · subst hq
      obtain rfl := hwpr r h
      rw [hphase'] at hph'
      intro q'
      rw [hg, gcaStep_aSnap]
      by_cases hk1 : k = 1
      · subst hk1
        rw [ite_eq_left hk, hi.A r q']
        have hread : (retro act wr wv r).timed.readA q = some (clk act wr t r) :=
          eventTime_of_advance _ hcur hnext'
        show _ ↔ TimedExecution.Seen ((retro act wr wv r).eventTime q' 0)
          ((retro act wr wv r).timed.readA q)
        rw [hread, seen_some_iff]
        split
        · rename_i h1; simp only [Option.isSome_some, true_iff]; omega
        · rename_i h1; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]; omega
      · rw [ite_eq_right (by rw [hk]; exact hk1)]
        exact hi.aSeen q r hwp (by omega) q'
    · rw [hframe q hq] at hph' ⊢; exact hi.aSeen q r ((hwq q hq) ▸ h) hph'
  · -- cand
    intro q r h hph'
    by_cases hq : q = p
    · subst hq
      obtain rfl := hwpr r h
      rw [hphase'] at hph'
      rw [hg, gcaStep_cand]
      by_cases hk2 : k = 2
      · subst hk2
        rw [ite_eq_left hk]
        have htr := frame_aTraces act wr wv (hi.aVal q r hwp (by omega)) (hi.aSeen q r hwp (by omega))
        rw [htr]
        rfl
      · rw [ite_eq_right (by rw [hk]; exact hk2)]
        exact hi.cand q r hwp (by omega)
    · rw [hframe q hq] at hph' ⊢; exact hi.cand q r ((hwq q hq) ▸ h) hph'
  · -- bVal
    intro q r h hph'
    by_cases hq : q = p
    · subst hq
      obtain rfl := hwpr r h
      rw [hphase'] at hph'
      intro q'
      rw [hg, gcaStep_bSnap]
      by_cases hk4 : k = 4
      · rw [ite_eq_left (hk.trans hk4), hi.B r q']
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
      · rw [ite_eq_right (by rw [hk]; exact hk4)]
        exact hi.bVal q r hwp (by omega) q'
    · rw [hframe q hq] at hph' ⊢; exact hi.bVal q r ((hwq q hq) ▸ h) hph'
  · -- bSeen
    intro q r h hph'
    by_cases hq : q = p
    · subst hq
      obtain rfl := hwpr r h
      rw [hphase'] at hph'
      intro q'
      rw [hg, gcaStep_bSnap]
      by_cases hk4 : k = 4
      · subst hk4
        rw [ite_eq_left hk, hi.B r q']
        have hread : (retro act wr wv r).timed.readB q = some (clk act wr t r) :=
          eventTime_of_advance _ hcur hnext'
        show _ ↔ TimedExecution.Seen ((retro act wr wv r).eventTime q' 3)
          ((retro act wr wv r).timed.readB q)
        rw [hread, seen_some_iff]
        split
        · rename_i h1; simp only [Option.isSome_some, true_iff]; omega
        · rename_i h1; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]; omega
      · rw [ite_eq_right (by rw [hk]; exact hk4)]
        exact hi.bSeen q r hwp (by omega) q'
    · rw [hframe q hq] at hph' ⊢; exact hi.bSeen q r ((hwq q hq) ▸ h) hph'

/-- **The invariant holds at every instant.** -/
theorem Inv.all (hd : Driven act wr wv gs) : ∀ t, Inv act wr wv gs t := by
  intro t
  induction t with
  | zero => exact Inv.initial hd
  | succ t ih =>
      cases hact : act t with
      | none => exact ih.step_idle hd hact
      | some p =>
          cases hwp : wr t p with
          | none => exact ih.step_prog hd hact hwp
          | some r₀ =>
              by_cases hph : ((gs t).frame p).phase < 6
              · exact ih.step_gca hd hact hwp hph
              · exact ih.step_recv hd hact hwp hph

/-- **What the machine hands a caller is the timed-execution output of the
reconstructed protocol.**  The caller computes lines 6–8 from its own two scans;
the reconstruction computes them from the event times of the whole run; they
agree because a scan sees exactly the writes that precede it. -/
theorem output_agrees (hd : Driven act wr wv gs) {t : Nat} {p : Fin n} {r : Nat}
    (hw : wr t p = some r) (hph : ¬ ((gs t).frame p).phase < 6) :
    (retro act wr wv r).history.output p = some (frameOutput O n ((gs t).frame p) (wv t p)) := by
  classical
  have hi := Inv.all hd t
  have hsix : (retro act wr wv r).phase (clk act wr t r) p = 6 := by
    have h1 := hi.phase p r hw
    have h2 := (retro act wr wv r).phase_le_six (clk act wr t r) p
    omega
  have hge : 6 ≤ ((gs t).frame p).phase := by omega
  have hav := hi.aVal p r hw (by omega)
  have has := hi.aSeen p r hw (by omega)
  have hcd := hi.cand p r hw (by omega)
  have hbv := hi.bVal p r hw (by omega)
  have hbs := hi.bSeen p r hw (by omega)
  have hAV := frame_aView act wr wv has
  have hBV := frame_bView act wr wv hbs
  have hFL := frame_flagged_mem act wr wv hbv hbs
  have hret : p ∈ (retro act wr wv r).timed.returned := by
    rw [TimedExecution.mem_returned]
    refine ⟨(mem_participants wr).mpr ⟨t, hw⟩, ?_⟩
    obtain ⟨w, hw5, -⟩ := (lt_phase_iff (retro act wr wv r) 5 (clk act wr t r) p).mp
      (by rw [hsix]; omega)
    exact ⟨w, hw5⟩
  have hres : (retro act wr wv r).timed.views.result p = frameResult O n ((gs t).frame p) := by
    unfold SnapshotExecution.result Object.gcaOutput frameResult
    by_cases hex : ∃ s, s ∈ ((gs t).frame p).flagged
    · have hex' : ∃ s, s ∈ O.gcaFlagged ((retro act wr wv r).timed.views.bViews p) := by
        obtain ⟨s, hs⟩ := hex; exact ⟨s, (hFL s).mp hs⟩
      rw [dite_eq_left hex', dite_eq_left hex]
      refine O.glb_unique (O.traceGLB_spec _ hex') ?_
      have hspec := O.traceGLB_spec (fun s => s ∈ ((gs t).frame p).flagged) hex
      exact ⟨fun u hu => hspec.1 u ((hFL u).mpr hu),
        fun l hl => hspec.2 l (fun u hu => hl u ((hFL u).mp hu))⟩
    · have hex' : ¬ ∃ s, s ∈ O.gcaFlagged ((retro act wr wv r).timed.views.bViews p) := by
        rintro ⟨s, hs⟩; exact hex ⟨s, (hFL s).mpr hs⟩
      rw [dite_eq_right hex', dite_eq_right hex, hcd]
      rfl
  have P1 : ∀ q ∈ ((gs t).frame p).aView,
      (((gs t).frame p).aSnap q).getD O.emptyTrace = (retro act wr wv r).timed.views.input q := by
    intro q hq
    have hs : (((gs t).frame p).aSnap q).isSome = true := by
      unfold Frame.aView at hq; exact (List.mem_filter.mp hq).2
    rcases hav q with h | h
    · rw [h] at hs; cases hs
    · rw [h]; rfl
  have P2 : ∀ q ∈ ((gs t).frame p).bView, ((gs t).frame p).bEntry q = rcand act wr wv r q := by
    intro q hq
    have hs : (((gs t).frame p).bSnap q).isSome = true := by
      unfold Frame.bView at hq; exact (List.mem_filter.mp hq).2
    rcases hbv q with h | h
    · rw [h] at hs; cases hs
    · unfold Frame.bEntry; rw [h]; rfl
  have hown : (retro act wr wv r).timed.views.input p = wv t p := hd.rinput_eq hw
  have hcom : frameCommits O n ((gs t).frame p) (wv t p) ↔
      (retro act wr wv r).timed.views.Commits p := by
    unfold frameCommits SnapshotExecution.Commits SnapshotExecution.EqualViews
      SnapshotExecution.Flag SnapshotExecution.candidate
    rw [← hAV, ← hBV, hres]
    constructor
    · refine Or.imp (And.imp ?_ ?_) (And.imp ?_ ?_)
      · intro h q hq; rw [← P1 q hq, h q hq, hown]
      · intro h q hq
        have e1 := h q hq
        rw [P2 q hq] at e1
        rw [hown]; exact e1
      · intro h q hq hpre; exact h q hq (by rw [P1 q hq]; exact hpre)
      · intro h q hq
        have e1 := h q hq
        rw [P2 q hq] at e1
        exact of_decide_eq_true e1
    · refine Or.imp (And.imp ?_ ?_) (And.imp ?_ ?_)
      · intro h q hq; rw [P1 q hq, h q hq, hown]
      · intro h q hq
        rw [P2 q hq, ← hown]
        exact h q hq
      · intro h q hq hpre; exact h q hq (by rw [← P1 q hq]; exact hpre)
      · intro h q hq
        rw [P2 q hq]
        exact decide_eq_true (h q hq)
  show (retro act wr wv r).timed.views.history.output p = _
  refine ((retro act wr wv r).timed.views.output_iff p _ _).mpr ⟨hret, hres.symm, ?_⟩
  show @decide (frameCommits O n ((gs t).frame p) (wv t p)) (Classical.propDecidable _) = _
  exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq]; exact hcom)

/-- A caller that entered round `r` is one of its participants, with its proposal
as input. -/
theorem retro_input_of_waited {r : Nat} {q : Fin n} (h : Waited wr r q) :
    (retro act wr wv r).history.input q = some (rinput wr wv r q) := by
  have hmem : q ∈ participants wr r := (mem_participants wr).mpr h
  simp only [GCA.Protocol.history, SnapshotExecution.history]
  split
  · rfl
  · rename_i hn; exact absurd hmem hn

/-- Only processes that entered round `r` have an input to it. -/
theorem waited_of_retro_input {r : Nat} {q : Fin n} {s : O.Trace}
    (h : (retro act wr wv r).history.input q = some s) : Waited wr r q := by
  simp only [GCA.Protocol.history, SnapshotExecution.history] at h
  split at h
  · rename_i hm; exact (mem_participants wr).mp hm
  · cases h

end Invariant

end ConflictFreedom.ForwardGCA
