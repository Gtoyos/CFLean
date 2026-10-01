import CFLeanProof.GCA

/-!
# GCA objects given by an implementation

`GlobalSchedule.WeakRun.GCAInterface` states what the universal constructions
need of their GCA objects on **one run**: the rounds' whole-run tables satisfy
the six properties, outputs are causal, and calls return.  That is enough for
every theorem about a given infinite run.  It is not enough for the two
theorems of §7, which assert that a finite execution **has** an extension: a
table fixed in advance says nothing about what the objects would answer if the
run went differently.  For that the GCA objects must be something that can be
run — an implementation.

A `GCAMachine` is such an implementation, for every round at once, as an
abstract shared-memory machine: `step g p r v` is one step of `p`'s current
call, to round `r` with proposal `v`; `output g p r v` is `some (t, c)` once that
call has finished, with output `t` and commit flag `c`; `leave g p` is the state
after `p` returns.  Nothing else is fixed — not the shared objects, how many
steps a call takes, or whether rounds share memory.  Algorithm 2 over atomic
snapshots is one such machine (`ForwardGCA.machine`, in `GCAMachineAlgorithm2`).

A client **drives** the machine (`Driven`): at each instant one process, or
nobody, is scheduled; a process inside a call takes a step of it, or returns
once the call has finished; a process outside a call takes a step of its own
program, which leaves the machine alone and may enter a round it has never been
in, with any proposal.  Every client of Algorithms 1 and 3 is of this form, and
so is every schedule — crashes, idle instants, and finite executions (idle for
ever after their last step) included.

The **history** of round `r` in a run (`history`) is what the paper calls the
execution of `GCA_r`: the participants' proposals, and the outputs returned.

**The GCA specification** (`IsGCA`), as §4.2 states it — "the following
properties hold for every execution", and "every correct participant eventually
returns" — for every run of the machine:

* `spec`: every round's history satisfies the six properties
  (`GCA.History.Specification`);
* `returns`: a participant that keeps taking steps does not stay inside a call
  for ever.

Because runs include every finite execution (`Driven.cut`), the six properties
hold of every prefix as well (`history_cut_input`, `returned_cut_iff`); in
particular Validity holds when an output is returned, which is the causality the
universal constructions use.  **Solo agreement** (`SoloAgreement`), GCA property
7 of §7, is stated the same way, on prefixes of runs.
-/

namespace ConflictFreedom
open Object

variable {S Op R : Type} (O : Object S Op R) (n : Nat)

/-- **A GCA implementation**, serving every round, as an abstract machine. -/
structure GCAMachine where
  /-- The implementation's state: its shared objects and every caller's local
  state. -/
  State : Type
  /-- The initial state. -/
  init : State
  /-- One step of `p`'s current call, to round `r` with proposal `v`. -/
  step : State → Fin n → Nat → O.Trace → State
  /-- `some (t, c)` once `p`'s current call, to round `r` with proposal `v`, has
  finished: `t` is its output trace and `c` whether it commits. -/
  output : State → Fin n → Nat → O.Trace → Option (O.Trace × Bool)
  /-- The state once `p` has returned from its call. -/
  leave : State → Fin n → State

namespace GCAMachine
variable {O n} (G : GCAMachine O n)

/-! ## Runs of the machine -/

/-- **How a client drives the machine.**  A run supplies, at every instant `t`,
the scheduled process `act t` (`none` for an idle instant), the round each
process is inside a call to (`wr t p`, `none` outside a call), the proposal it
handed that call (`wv t p`), and the machine's state `gs t`.

Only the scheduled process moves.  A caller whose call has not finished takes a
step of it and stays in the call with the same proposal; a caller whose call has
finished returns, leaving the call; a process outside any call takes a program
step that leaves the machine alone and, if it enters a round, enters a round it
has never been in — GCA objects are one-shot. -/
structure Driven (act : Nat → Option (Fin n)) (wr : Nat → Fin n → Option Nat)
    (wv : Nat → Fin n → O.Trace) (gs : Nat → G.State) : Prop where
  init_gs : gs 0 = G.init
  init_wr : ∀ p, wr 0 p = none
  idle : ∀ t, act t = none →
    gs (t + 1) = gs t ∧ ∀ q, wr (t + 1) q = wr t q ∧ wv (t + 1) q = wv t q
  other : ∀ t p q, act t = some p → q ≠ p → wr (t + 1) q = wr t q ∧ wv (t + 1) q = wv t q
  step : ∀ t p r, act t = some p → wr t p = some r → G.output (gs t) p r (wv t p) = none →
    gs (t + 1) = G.step (gs t) p r (wv t p) ∧ wr (t + 1) p = some r ∧ wv (t + 1) p = wv t p
  ret : ∀ t p r o, act t = some p → wr t p = some r → G.output (gs t) p r (wv t p) = some o →
    gs (t + 1) = G.leave (gs t) p ∧ wr (t + 1) p = none
  prog : ∀ t p, act t = some p → wr t p = none →
    gs (t + 1) = gs t ∧ ∀ r, wr (t + 1) p = some r → ∀ u, u ≤ t → wr u p ≠ some r

/-- `p` returned `o` from its call to round `r`: at some instant it was scheduled
inside that call, and the call had finished with output `o`. -/
def Returned (act : Nat → Option (Fin n)) (wr : Nat → Fin n → Option Nat)
    (wv : Nat → Fin n → O.Trace) (gs : Nat → G.State) (r : Nat) (p : Fin n)
    (o : O.Trace × Bool) : Prop :=
  ∃ t, act t = some p ∧ wr t p = some r ∧ G.output (gs t) p r (wv t p) = some o

/-- **The history of round `r` in a run**: every process that entered the round
is a participant, with the proposal it handed the call as input; every process
that returned from it has the output it returned. -/
noncomputable def history (act : Nat → Option (Fin n)) (wr : Nat → Fin n → Option Nat)
    (wv : Nat → Fin n → O.Trace) (gs : Nat → G.State) (r : Nat) : GCA.History O (Fin n) where
  input p := by
    classical
    exact if h : ∃ t, wr t p = some r then some (wv (Classical.choose h) p) else none
  output p := by
    classical
    exact if h : ∃ o, G.Returned act wr wv gs r p o then some (Classical.choose h) else none
  returned_invoked := by
    classical
    intro p t c h
    split at h
    · rename_i hex
      obtain ⟨u, -, hu, -⟩ := Classical.choose_spec hex
      exact ⟨_, dite_eq_left ⟨u, hu⟩⟩
    · cases h

/-- **The GCA specification of §4.2, for the machine**: in every run — every
client, every schedule — each round's history satisfies the six properties
(`spec`), and every correct participant eventually returns: a process inside a
call from some time on is scheduled only finitely often (`returns`). -/
structure IsGCA [DecidableEq Op] : Prop where
  spec : ∀ act wr wv gs, G.Driven act wr wv gs → ∀ r, (G.history act wr wv gs r).Specification
  returns : ∀ act wr wv gs, G.Driven act wr wv gs → ∀ p r N,
    (∀ t, N ≤ t → wr t p = some r) → ¬ ∀ M, ∃ t, M ≤ t ∧ act t = some p

/-- **GCA property 7, Solo agreement** (§7): "if a process returns before any
other process participates, every output trace equals its own",
`P' = P'_r = {j} ⟹ ∀ i ∈ P_r, t_i = t_j`, where `P'` and `P'_r` are the
participants and returning participants of a prefix.  The prefix is the run up
to `T`: `j` is the only process that has entered round `R`, and it has returned
`o` from it.  The conclusion is about the whole run: every output trace of `R`
is `o`'s. -/
def SoloAgreement : Prop :=
  ∀ act wr wv gs, G.Driven act wr wv gs → ∀ T R j o,
    (∀ t q, t ≤ T → wr t q = some R → q = j) →
    (∃ t, t < T ∧ act t = some j ∧ wr t j = some R ∧ G.output (gs t) j R (wv t j) = some o) →
    ∀ q y c, (G.history act wr wv gs R).output q = some (y, c) → y = o.1

/-! ## Facts about every run -/

section Facts
variable {G} {act : Nat → Option (Fin n)} {wr : Nat → Fin n → Option Nat}
  {wv : Nat → Fin n → O.Trace} {gs : Nat → G.State}

theorem Driven.unscheduled (hd : G.Driven act wr wv gs) {t : Nat} {q : Fin n}
    (hq : act t ≠ some q) : wr (t + 1) q = wr t q ∧ wv (t + 1) q = wv t q := by
  cases hact : act t with
  | none => exact (hd.idle t hact).2 q
  | some p => exact hd.other t p q hact (fun he => hq (he ▸ hact))

/-- A round is entered only through a program step, and only if it is new. -/
theorem Driven.entry (hd : G.Driven act wr wv gs) {t : Nat} {q : Fin n} {r : Nat}
    (h0 : wr t q ≠ some r) (h1 : wr (t + 1) q = some r) : ∀ u, u ≤ t → wr u q ≠ some r := by
  by_cases hact : act t = some q
  · cases hw : wr t q with
    | none => exact (hd.prog t q hact hw).2 r h1
    | some r' =>
        exfalso
        cases ho : G.output (gs t) q r' (wv t q) with
        | none =>
            have := (hd.step t q r' hact hw ho).2.1
            rw [h1] at this
            exact h0 (hw.trans (congrArg some (Option.some.inj this).symm))
        | some o =>
            have := (hd.ret t q r' o hact hw ho).2
            rw [h1] at this
            cases this
  · exact absurd ((hd.unscheduled hact).1.symm.trans h1) h0

/-- Inside a round, the proposal does not change from one instant to the next. -/
theorem Driven.stay (hd : G.Driven act wr wv gs) {t : Nat} {q : Fin n} {r : Nat}
    (h0 : wr t q = some r) (h1 : wr (t + 1) q = some r) : wv (t + 1) q = wv t q := by
  by_cases hact : act t = some q
  · cases ho : G.output (gs t) q r (wv t q) with
    | none => exact (hd.step t q r hact h0 ho).2.2
    | some o =>
        have := (hd.ret t q r o hact h0 ho).2
        rw [h1] at this
        cases this
  · exact (hd.unscheduled hact).2

/-- **A caller never returns to a round it has left.** -/
theorem Driven.never_return (hd : G.Driven act wr wv gs) {u : Nat} {q : Fin n} {r : Nat}
    (h0 : wr u q = some r) (h1 : wr (u + 1) q ≠ some r) : ∀ d, wr (u + 1 + d) q ≠ some r := by
  intro d
  induction d with
  | zero => exact h1
  | succ d ih =>
      intro hs
      exact hd.entry ih (by rw [show u + 1 + (d + 1) = (u + 1 + d) + 1 from by omega] at hs; exact hs)
        u (by omega) h0

/-- **A caller's time in a round is one stretch, with one proposal.** -/
theorem Driven.episode (hd : G.Driven act wr wv gs) {t t' : Nat} {q : Fin n} {r : Nat}
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

/-- A process's input to a round is the proposal it holds at any instant inside
the round. -/
theorem Driven.history_input (hd : G.Driven act wr wv gs) {t : Nat} {q : Fin n} {r : Nat}
    (h : wr t q = some r) : (G.history act wr wv gs r).input q = some (wv t q) := by
  classical
  have hex : ∃ t, wr t q = some r := ⟨t, h⟩
  show (if h : ∃ t, wr t q = some r then some (wv (Classical.choose h) q) else none) = _
  rw [dite_eq_left hex]
  exact congrArg some (hd.episode (Classical.choose_spec hex) h)

/-- Only processes that entered a round have an input to it. -/
theorem entered_of_history_input {r : Nat} {q : Fin n} {s : O.Trace}
    (h : (G.history act wr wv gs r).input q = some s) : ∃ t, wr t q = some r ∧ wv t q = s := by
  classical
  have h' : (if h : ∃ t, wr t q = some r then some (wv (Classical.choose h) q) else none)
      = some s := h
  split at h'
  · rename_i hex
    exact ⟨_, Classical.choose_spec hex, Option.some.inj h'⟩
  · cases h'

/-- **A call returns once**: after returning, a caller has left the round for
good, so the output it returned is unique. -/
theorem Driven.returned_unique (hd : G.Driven act wr wv gs) {r : Nat} {q : Fin n}
    {o o' : O.Trace × Bool} (h : G.Returned act wr wv gs r q o)
    (h' : G.Returned act wr wv gs r q o') : o = o' := by
  obtain ⟨t, hact, hw, ho⟩ := h
  obtain ⟨t', hact', hw', ho'⟩ := h'
  have left : ∀ {a b : Nat} {x : O.Trace × Bool}, a < b → act a = some q → wr a q = some r →
      G.output (gs a) q r (wv a q) = some x → wr b q ≠ some r := by
    intro a b x hab ha hwa hoa hb
    have hleave := (hd.ret a q r x ha hwa hoa).2
    have := hd.never_return hwa (by rw [hleave]; simp) (b - (a + 1))
    rw [show a + 1 + (b - (a + 1)) = b from by omega] at this
    exact this hb
  rcases Nat.lt_trichotomy t t' with hlt | rfl | hlt
  · exact absurd hw' (left hlt hact hw ho)
  · exact Option.some.inj (ho.symm.trans ho')
  · exact absurd hw (left hlt hact' hw' ho')

/-- The output a caller returned is its history output. -/
theorem Driven.history_output (hd : G.Driven act wr wv gs) {r : Nat} {q : Fin n}
    {o : O.Trace × Bool} (h : G.Returned act wr wv gs r q o) :
    (G.history act wr wv gs r).output q = some o := by
  classical
  have hex : ∃ o, G.Returned act wr wv gs r q o := ⟨o, h⟩
  show (if h : ∃ o, G.Returned act wr wv gs r q o then some (Classical.choose h) else none) = _
  rw [dite_eq_left hex]
  exact congrArg some (hd.returned_unique (Classical.choose_spec hex) h)

/-- Only processes that returned from a round have an output from it. -/
theorem returned_of_history_output {r : Nat} {q : Fin n} {o : O.Trace × Bool}
    (h : (G.history act wr wv gs r).output q = some o) : G.Returned act wr wv gs r q o := by
  classical
  have h' : (if h : ∃ o, G.Returned act wr wv gs r q o then some (Classical.choose h) else none)
      = some o := h
  split at h'
  · rename_i hex
    exact Option.some.inj h' ▸ Classical.choose_spec hex
  · cases h'

end Facts

/-! ## Finite executions are runs

A finite execution is a run that idles for ever after its last step.  Cutting a
run at `T` gives such a run, whose histories are the histories of the prefix of
length `T`: the six properties of §4.2, which hold "for every execution", hold
of every prefix. -/

/-- The schedule of the run cut at `T`: its first `T` steps, then idle for ever. -/
def cutAct (act : Nat → Option (Fin n)) (T : Nat) : Nat → Option (Fin n) :=
  fun t => if t < T then act t else none

/-- A component of the run cut at `T`: frozen from `T` on. -/
def cut {α : Type} (x : Nat → α) (T : Nat) : Nat → α := fun t => x (min t T)

section Cut
variable {G} {act : Nat → Option (Fin n)} {wr : Nat → Fin n → Option Nat}
  {wv : Nat → Fin n → O.Trace} {gs : Nat → G.State}

theorem cutAct_of_lt {T t : Nat} (h : t < T) : cutAct act T t = act t := ite_eq_left h

theorem cut_of_le {α : Type} {x : Nat → α} {T t : Nat} (h : t ≤ T) : cut x T t = x t := by
  unfold cut; rw [Nat.min_eq_left h]

theorem cut_of_ge {α : Type} {x : Nat → α} {T t : Nat} (h : T ≤ t) : cut x T t = x T := by
  unfold cut; rw [Nat.min_eq_right h]

/-- **The run cut at `T` is a run.** -/
theorem Driven.cut (hd : G.Driven act wr wv gs) (T : Nat) :
    G.Driven (cutAct act T) (GCAMachine.cut wr T) (GCAMachine.cut wv T)
      (GCAMachine.cut gs T) := by
  have low : ∀ {α : Type} (x : Nat → α) {t : Nat}, t < T →
      GCAMachine.cut x T (t + 1) = x (t + 1) ∧ GCAMachine.cut x T t = x t := by
    intro α x t ht
    exact ⟨cut_of_le (by omega), cut_of_le (by omega)⟩
  have high : ∀ {α : Type} (x : Nat → α) {t : Nat}, T ≤ t →
      GCAMachine.cut x T (t + 1) = GCAMachine.cut x T t := by
    intro α x t ht
    rw [cut_of_ge (by omega), cut_of_ge ht]
  refine ⟨?_, fun p => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cut_of_le (Nat.zero_le _)]; exact hd.init_gs
  · rw [cut_of_le (Nat.zero_le _)]; exact hd.init_wr p
  · intro t ha
    by_cases ht : t < T
    · rw [cutAct_of_lt ht] at ha
      obtain ⟨hg, hq⟩ := hd.idle t ha
      rw [(low gs ht).1, (low gs ht).2]
      refine ⟨hg, fun q => ?_⟩
      rw [(low wr ht).1, (low wr ht).2, (low wv ht).1, (low wv ht).2]
      exact hq q
    · have ht' : T ≤ t := by omega
      exact ⟨high gs ht', fun q => ⟨by rw [high wr ht'], by rw [high wv ht']⟩⟩
  all_goals first
    | (intro t p q ha hq
       have ht : t < T := Classical.byContradiction fun h => by
         rw [cutAct, ite_eq_right h] at ha; cases ha
       rw [cutAct_of_lt ht] at ha
       rw [(low wr ht).1, (low wr ht).2, (low wv ht).1, (low wv ht).2]
       exact hd.other t p q ha hq)
    | (intro t p r ha hw ho
       have ht : t < T := Classical.byContradiction fun h => by
         rw [cutAct, ite_eq_right h] at ha; cases ha
       rw [cutAct_of_lt ht] at ha
       rw [(low wr ht).2] at hw
       rw [(low gs ht).2, (low wv ht).2] at ho
       rw [(low gs ht).1, (low gs ht).2, (low wr ht).1, (low wv ht).1, (low wv ht).2]
       exact hd.step t p r ha hw ho)
    | (intro t p r o ha hw ho
       have ht : t < T := Classical.byContradiction fun h => by
         rw [cutAct, ite_eq_right h] at ha; cases ha
       rw [cutAct_of_lt ht] at ha
       rw [(low wr ht).2] at hw
       rw [(low gs ht).2, (low wv ht).2] at ho
       rw [(low gs ht).1, (low gs ht).2, (low wr ht).1]
       exact hd.ret t p r o ha hw ho)
    | (intro t p ha hw
       have ht : t < T := Classical.byContradiction fun h => by
         rw [cutAct, ite_eq_right h] at ha; cases ha
       rw [cutAct_of_lt ht] at ha
       rw [(low wr ht).2] at hw
       rw [(low gs ht).1, (low gs ht).2, (low wr ht).1]
       obtain ⟨hg, hfresh⟩ := hd.prog t p ha hw
       refine ⟨hg, fun r hr u hu => ?_⟩
       rw [cut_of_le (by omega)]
       exact hfresh r hr u hu)

/-- The participants of a round in the run cut at `T` are those that entered it
by time `T`. -/
theorem history_cut_input (hd : G.Driven act wr wv gs) (T r : Nat) (q : Fin n) (s : O.Trace) :
    (G.history (cutAct act T) (cut wr T) (cut wv T) (cut gs T) r).input q = some s ↔
      ∃ t, t ≤ T ∧ wr t q = some r ∧ wv t q = s := by
  constructor
  · intro h
    obtain ⟨t, hw, hv⟩ := entered_of_history_input h
    refine ⟨min t T, Nat.min_le_right _ _, hw, hv⟩
  · rintro ⟨t, ht, hw, rfl⟩
    have hw' : cut wr T t q = some r := by rw [cut_of_le ht]; exact hw
    rw [(hd.cut T).history_input hw', cut_of_le ht]

/-- The returns in the run cut at `T` are the returns before `T`. -/
theorem returned_cut_iff (T r : Nat) (q : Fin n) (o : O.Trace × Bool) :
    G.Returned (cutAct act T) (cut wr T) (cut wv T) (cut gs T) r q o ↔
      ∃ t, t < T ∧ act t = some q ∧ wr t q = some r ∧ G.output (gs t) q r (wv t q) = some o := by
  constructor
  · rintro ⟨t, ha, hw, ho⟩
    have ht : t < T := Classical.byContradiction fun h => by
      rw [cutAct, ite_eq_right h] at ha; cases ha
    rw [cutAct_of_lt ht] at ha
    rw [cut_of_le (Nat.le_of_lt ht)] at hw ho
    rw [cut_of_le (Nat.le_of_lt ht)] at ho
    exact ⟨t, ht, ha, hw, ho⟩
  · rintro ⟨t, ht, ha, hw, ho⟩
    refine ⟨t, by rw [cutAct_of_lt ht]; exact ha, by rw [cut_of_le (Nat.le_of_lt ht)]; exact hw, ?_⟩
    rw [cut_of_le (Nat.le_of_lt ht), cut_of_le (Nat.le_of_lt ht)]
    exact ho

end Cut

end GCAMachine

/-! ## Restricting a history's outputs -/

namespace GCA.History
variable {State Op' Response P : Type} {obj : Object State Op' Response}

/-- **The six properties survive dropping outputs.**  A history with the same
participants and inputs, and only some of the outputs, satisfies them too: every
property but Commitment only constrains outputs that exist, and Commitment's
premise that every participant returned carries over. -/
theorem Specification.of_outputs_sub [DecidableEq Op'] {h h' : History obj P}
    (hs : h.Specification) (hin : ∀ p, h'.input p = h.input p)
    (hout : ∀ p o, h'.output p = some o → h.output p = some o) : h'.Specification := by
  have hInputs : ∀ s, h'.Inputs s ↔ h.Inputs s := fun s =>
    ⟨fun ⟨p, hp⟩ => ⟨p, (hin p) ▸ hp⟩, fun ⟨p, hp⟩ => ⟨p, (hin p).symm ▸ hp⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p t c hp a ha
    obtain ⟨s, hsin, hle⟩ := hs.validity p t c (hout p _ hp) a ha
    exact ⟨s, (hInputs s).mpr hsin, hle⟩
  · intro p t hp q u c hq
    exact hs.adoption p t (hout p _ hp) q u c (hout q _ hq)
  · intro hne hcomp hall
    have hne' : ∃ s, h.Inputs s := by
      obtain ⟨s, hsin⟩ := hne; exact ⟨s, (hInputs s).mp hsin⟩
    have hcomp' : obj.Compatible h.Inputs := by
      obtain ⟨z, hz⟩ := hcomp; exact ⟨z, fun s hsin => hz s ((hInputs s).mpr hsin)⟩
    have hall' : h.AllReturned := by
      intro p s hp
      obtain ⟨t, c, htc⟩ := hall p s ((hin p).trans hp)
      exact ⟨t, c, hout p _ htc⟩
    obtain ⟨p, s, t, hps, hpt, hst⟩ := hs.commitment hne' hcomp' hall'
    obtain ⟨t', c', htc'⟩ := hall p s ((hin p).trans hps)
    have := (hout p _ htc').symm.trans hpt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj this)
    exact ⟨p, s, t', (hin p).trans hps, htc', hst⟩
  · obtain ⟨z, hz⟩ := hs.convergence
    exact ⟨z, fun t ⟨p, c, hp⟩ => hz t ⟨p, c, hout p _ hp⟩⟩
  · intro l hl t ⟨p, c, hp⟩
    exact hs.commonPrefix l (fun s hsin => hl s ((hInputs s).mpr hsin)) t ⟨p, c, hout p _ hp⟩
  · intro heq p t c hp
    exact hs.weakAgreement (fun s t hs' ht' => heq s t ((hInputs s).mpr hs') ((hInputs t).mpr ht'))
      p t c (hout p _ hp)

end GCA.History

end ConflictFreedom
