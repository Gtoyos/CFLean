import CFLeanProof.ForwardGCA
import CFLeanProof.GCASoloAgreement
import CFLeanProof.GCAMachine

/-!
# Algorithm 2 is a GCA machine meeting the specification and Solo agreement

`ForwardGCA` runs Algorithm 2 over atomic snapshot objects as a machine driven
by a client.  Packaged as a `GCAMachine` (`machine`) — a step is `gcaStep`, a
call has finished once its frame reaches the last stage, the output is
`frameOutput`, and returning resets the frame — it meets the GCA specification
(`machine_isGCA`) and Solo agreement (`machine_soloAgreement`):

* A run of `machine` follows `ForwardGCA.Driven` (`driven_of_machine`), so each
  round of it is the protocol `retro` reconstructed from the run, and what a
  caller returns is that protocol's output (`output_agrees`).  The round's
  history has the protocol's participants and inputs and a subset of its
  outputs — a caller may finish its call and never be scheduled again — so the
  six properties of the protocol (`GCA.Protocol.specification`) carry over
  (`GCA.History.Specification.of_outputs_sub`).
* A caller's stage advances at each of its steps and at nobody else's, so a
  caller that keeps being scheduled finishes within six steps and returns at the
  seventh (`machine_returns`).
* Solo agreement is Lemma `GCA_soloagg` (`GCA.Protocol.soloAgreement`) on the
  reconstructed protocol, read at the prefix's own clock.

Snapshot operations are atomic, the manuscript's assumption of wait-free
linearizable snapshot objects, as in `ForwardGCA`.  That `machine` keeps both
properties when they are replaced by a wait-free linearizable implementation
from read/write registers is the one fact the development takes from the
literature (see the assumptions in `MODEL.md`).  No theorem depends on it: the universal
constructions are proved over any `GCAMachine` meeting `IsGCA` (and
`SoloAgreement` for `th:WeakUCresolve`), so a register-level machine with those
properties would plug in unchanged.
-/

namespace ConflictFreedom.ForwardGCA
open Object GCA

variable {S Op R : Type} (O : Object S Op R) (n : Nat) [DecidableEq Op]

/-- **Algorithm 2 over atomic snapshots, as a GCA machine.** -/
noncomputable def machine : GCAMachine O n where
  State := GState O n
  init := GState.initial O n
  step := gcaStep O n
  output g p _ v := if (g.frame p).phase < 6 then none else some (frameOutput O n (g.frame p) v)
  leave := resetFrame O n

variable {O n}

theorem machine_output_none {g : GState O n} {p : Fin n} {r : Nat} {v : O.Trace}
    (h : (machine O n).output g p r v = none) : (g.frame p).phase < 6 := by
  apply Classical.byContradiction
  intro hph
  have : (machine O n).output g p r v = some (frameOutput O n (g.frame p) v) := ite_eq_right hph
  rw [h] at this
  cases this

theorem machine_output_some {g : GState O n} {p : Fin n} {r : Nat} {v : O.Trace}
    {o : O.Trace × Bool} (h : (machine O n).output g p r v = some o) :
    ¬ (g.frame p).phase < 6 ∧ o = frameOutput O n (g.frame p) v := by
  by_cases hph : (g.frame p).phase < 6
  · have : (machine O n).output g p r v = none := ite_eq_left hph
    rw [h] at this
    cases this
  · have : (machine O n).output g p r v = some (frameOutput O n (g.frame p) v) := ite_eq_right hph
    rw [h] at this
    exact ⟨hph, Option.some.inj this⟩

section Runs
variable {act : Nat → Option (Fin n)} {wr : Nat → Fin n → Option Nat}
  {wv : Nat → Fin n → O.Trace} {gs : Nat → GState O n}

/-- **A run of the machine follows `ForwardGCA`'s discipline.** -/
theorem driven_of_machine (hd : (machine O n).Driven act wr wv gs) : Driven act wr wv gs := by
  refine ⟨hd.init_gs, hd.init_wr, hd.idle, hd.other, ?_, ?_, hd.prog⟩
  · intro t p r hact hw hph
    exact hd.step t p r hact hw (ite_eq_left hph)
  · intro t p r hact hw hph
    exact hd.ret t p r _ hact hw (ite_eq_right hph)

/-- A round's history in a run of the machine: the reconstructed protocol's
participants and inputs, and some of its outputs. -/
theorem machine_history_input (hd : (machine O n).Driven act wr wv gs) (r : Nat) (q : Fin n) :
    ((machine O n).history act wr wv gs r).input q = (retro act wr wv r).history.input q := by
  by_cases hq : ∃ t, wr t q = some r
  · obtain ⟨t, ht⟩ := hq
    rw [hd.history_input ht, retro_input_of_waited ⟨t, ht⟩, (driven_of_machine hd).rinput_eq ht]
  · cases hr : (retro act wr wv r).history.input q with
    | some s => exact absurd (waited_of_retro_input hr) hq
    | none =>
        cases hm : ((machine O n).history act wr wv gs r).input q with
        | none => rfl
        | some s =>
            obtain ⟨t, ht, -⟩ := GCAMachine.entered_of_history_input hm
            exact absurd ⟨t, ht⟩ hq

theorem machine_history_output (hd : (machine O n).Driven act wr wv gs) {r : Nat} {q : Fin n}
    {o : O.Trace × Bool} (h : ((machine O n).history act wr wv gs r).output q = some o) :
    (retro act wr wv r).history.output q = some o := by
  obtain ⟨t, -, hw, ho⟩ := GCAMachine.returned_of_history_output h
  obtain ⟨hph, rfl⟩ := machine_output_some ho
  exact output_agrees (driven_of_machine hd) hw hph

/-- **The six properties**, for every round of every run of the machine. -/
theorem machine_spec (hd : (machine O n).Driven act wr wv gs) (r : Nat) :
    ((machine O n).history act wr wv gs r).Specification :=
  (retro act wr wv r).specification.of_outputs_sub (machine_history_input hd r)
    (fun _ _ h => machine_history_output hd h)

/-- Nobody but a caller moves its frame. -/
theorem machine_frame_other (hd : (machine O n).Driven act wr wv gs) {t : Nat} {p : Fin n}
    (hp : act t ≠ some p) : (gs (t + 1)).frame p = (gs t).frame p := by
  cases hact : act t with
  | none => rw [(hd.idle t hact).1]
  | some q =>
      have hqp : p ≠ q := fun h => hp (h ▸ hact)
      cases hw : wr t q with
      | none => rw [(hd.prog t q hact hw).1]
      | some r =>
          cases ho : (machine O n).output (gs t) q r (wv t q) with
          | none =>
              rw [(hd.step t q r hact hw ho).1]
              exact gcaStep_frame_ne (gs t) q r (wv t q) hqp
          | some o =>
              rw [(hd.ret t q r o hact hw ho).1]
              show (resetFrame O n (gs t) q).frame p = _
              rw [resetFrame_frame, ite_eq_right hqp]

/-- **Every correct participant returns**: a caller's stage advances at each of
its steps and at nobody else's, so a caller that is scheduled for ever finishes
and returns. -/
theorem machine_returns (hd : (machine O n).Driven act wr wv gs) {p : Fin n} {r N : Nat}
    (hin : ∀ t, N ≤ t → wr t p = some r) : ¬ ∀ M, ∃ t, M ≤ t ∧ act t = some p := by
  intro hinf
  have hstep : ∀ t, N ≤ t → ((gs t).frame p).phase ≤ ((gs (t + 1)).frame p).phase ∧
      (act t = some p → ((gs (t + 1)).frame p).phase = ((gs t).frame p).phase + 1) := by
    intro t ht
    by_cases hact : act t = some p
    · have hw := hin t ht
      cases ho : (machine O n).output (gs t) p r (wv t p) with
      | none =>
          have hph := machine_output_none ho
          rw [(hd.step t p r hact hw ho).1]
          have := gcaStep_phase (gs t) p r (wv t p) hph
          exact ⟨by show _ ≤ ((gcaStep O n (gs t) p r (wv t p)).frame p).phase; omega,
            fun _ => this⟩
      | some o =>
          have := (hd.ret t p r o hact hw ho).2
          rw [hin (t + 1) (by omega)] at this
          cases this
    · rw [machine_frame_other hd hact]
      exact ⟨Nat.le_refl _, fun h => absurd h hact⟩
  have mono : ∀ t d, N ≤ t → ((gs t).frame p).phase ≤ ((gs (t + d)).frame p).phase := by
    intro t d ht
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih => exact Nat.le_trans ih (hstep (t + d) (by omega)).1
  have grow : ∀ k, ∃ t, N ≤ t ∧ k ≤ ((gs t).frame p).phase := by
    intro k
    induction k with
    | zero => exact ⟨N, Nat.le_refl _, Nat.zero_le _⟩
    | succ k ih =>
        obtain ⟨t, ht, hk⟩ := ih
        obtain ⟨u, hu, hact⟩ := hinf t
        have h1 := mono t (u - t) ht
        rw [show t + (u - t) = u from by omega] at h1
        have h2 := (hstep u (by omega)).2 hact
        exact ⟨u + 1, by omega, by omega⟩
  obtain ⟨t, ht, h6⟩ := grow 6
  obtain ⟨u, hu, hact⟩ := hinf t
  have h1 := mono t (u - t) ht
  rw [show t + (u - t) = u from by omega] at h1
  have ho : (machine O n).output (gs u) p r (wv u p)
      = some (frameOutput O n ((gs u).frame p) (wv u p)) := ite_eq_right (by omega)
  have := (hd.ret u p r _ hact (hin u (by omega)) ho).2
  rw [hin (u + 1) (by omega)] at this
  cases this

end Runs

/-- **Algorithm 2 meets the GCA specification**: in every run of the machine —
every client, every schedule — each round's history satisfies the six properties
of §4.2, and every correct participant returns. -/
theorem machine_isGCA : (machine O n).IsGCA where
  spec := fun _ _ _ _ hd r => machine_spec hd r
  returns := fun _ _ _ _ hd _ _ _ hin => machine_returns hd hin

/-- **Algorithm 2 satisfies Solo agreement** (Lemma `GCA_soloagg`), in every run
of the machine.  The prefix up to `T` is the reconstructed protocol's prefix up
to its own clock at `T`: every event before it was taken by a process inside the
round before `T`, hence by `j`, and `j` has reached the last stage. -/
theorem machine_soloAgreement : (machine O n).SoloAgreement := by
  intro act wr wv gs hd T R j o honly hret q y c hq
  obtain ⟨t₀, ht₀, -, hw₀, ho₀⟩ := hret
  have hd' := driven_of_machine hd
  obtain ⟨hph₀, rfl⟩ := machine_output_some ho₀
  have hsolo : ∀ c k, c < clk act wr T R → (retro act wr wv R).actor c = some k → k = j := by
    intro c k hc hk
    obtain ⟨t, hev, hcl⟩ := ractor_spec act wr hk
    have htT : t < T := by
      apply Classical.byContradiction
      intro h
      have := clk_mono act wr R (show T ≤ t by omega)
      omega
    exact honly t k (Nat.le_of_lt htT) (ev_inv act wr hev).2
  have h6 : (retro act wr wv R).phase (clk act wr T R) j = 6 := by
    have hi := (Inv.all hd' t₀).phase j R hw₀
    have hle := (retro act wr wv R).phase_le_six (clk act wr t₀ R) j
    have hmono := (retro act wr wv R).phase_mono (clk_mono act wr R (Nat.le_of_lt ht₀)) j
    have hle' := (retro act wr wv R).phase_le_six (clk act wr T R) j
    omega
  obtain ⟨tj, cj, hj, hall⟩ := (retro act wr wv R).soloAgreement _ j hsolo h6
  rw [output_agrees hd' hw₀ hph₀] at hj
  rw [hall q y c (machine_history_output hd hq)]
  exact (congrArg Prod.fst (Option.some.inj hj)).symm

end ConflictFreedom.ForwardGCA
