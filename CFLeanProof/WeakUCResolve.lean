import CFLeanProof.WeakConflictForgetting
import CFLeanProof.ForwardUniversal

/-!
# Theorem `th:WeakUCresolve`: every finite execution of Algorithm 1 has a finite conflict-forgetting solo extension

> **Theorem (`th:WeakUCresolve`).**  For every finite execution `α` of
> Algorithm 1 and every process `i`, there is a finite conflict-forgetting
> `i`-solo extension of `α`.

The statement quantifies over finite executions and their extensions, so it is
stated for Algorithm 1 *as a machine* (`ForwardUniversal`): a finite execution
is the first `N` steps of the run `frun ch client sched`, for any rule for the
collect order, any client and any scheduler, and an extension is a run that takes the same first `N` steps
(`Extends`).  GCA rounds run Algorithm 2 literally inside the machine, so
Solo agreement is not assumed: it is Lemma `GCA_soloagg`
(`GCA.Protocol.soloAgreement`), applied to the round the solo process ran.

* `Execution.EventuallyWeaklyConflictFree` is the manuscript's "eventually
  weakly `α`-conflict-free", in §3's vocabulary: a suffix in which no two
  concurrent operation instances **that take steps after `α`** conflict.
* `Forward.ConflictForgetting` is Definition *conflict-forgetting execution*:
  in every eventually weakly `α`-conflict-free infinite extension, some process
  that takes infinitely many steps completes each of its operations.
* `Forward.weakUCresolve` is the theorem.

**The solo extension** (`solo_extension`).  `soloSched sched N i` runs `sched`
for `N` steps and then only `i`, which invokes new operations when it has none.
A process that keeps taking steps waits on arbitrarily high rounds
(`WeakGCA.waiting_above`, from the measure `roundLevel`, which does not fall back
between operations), so `i` waits on some round `r*` above every round called in
`α` — possibly after completing some operations below it.  In the solo run `i`
is the only participant of `r*`, so it receives its own proposal `s`, committed
(`WeakGCA.solo_round_commits`: Commitment and Validity), then
publishes `(r*, s)` and returns.  `α'` ends right after that return.

**Conflict forgetting** (`weakUCresolve`).  For an extension `α''`, the facts
about `α'` that the proof needs are facts about its states, so they carry over
(`Extends`): `i` received `(s, true)` from `r*`, nobody else had called `r*`,
and no call above `r*` had been made.  `WeakGCA.forgetting_completes` then runs the
manuscript's argument in `α''` — Solo agreement for `r*`, the descent,
invariant (I), and the contradiction of `theorem:weakUCWCF`.

**Checks on the definitions.**  `stepsFrom_iff`: the operation time `N - 1` at
which `ConflictForgetting` places the end of `α` is exactly the end of the
machine's first `N` steps.  `EventuallyConflictFree.weakly`: the weak notion is
implied by §3's.  `conflictForgetting_hypothesis_satisfiable`: the solo
continuation is an extension meeting the hypothesis, so the definition is not
vacuous.

**Model.**  That of `forward1`: snapshot operations are atomic (the author's
assumption of wait-free linearizable snapshot objects) and a local computation
is one step.  Nothing about GCA is assumed: its seven properties are proved for
Algorithm 2.

**Over any GCA implementation.**  The same theorem, for Algorithm 1 over any GCA
implementation meeting the specification of §4.2 and Solo agreement — the
manuscript's hypothesis in §7 — is `WeakUniversal.Over.weakUCresolve`
(`Algorithm1OverGCA`); Algorithm 2 is one such implementation
(`ForwardGCA.machine_isGCA`, `ForwardGCA.machine_soloAgreement`).
-/

namespace ConflictFreedom.WeakUniversal
open Object
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-! ## A register-round invariant and a progress measure -/

/-- **`S[p]` never runs ahead of `p`'s current operation.**  Once `p` has read
its own register during a collect, its seed is at least as recent; every
proposal of the operation is to a later round; and after publishing, `S[p]`
holds exactly the committed round. -/
def SlotShape (c : Configuration (n := n) obj) (p : Fin n) : Prop :=
  match c.localState p with
  | .idle => True
  | .collecting _ todo seed => p ∉ todo → (c.slots p).round ≤ seed.round
  | .ready _ seed => (c.slots p).round ≤ seed.round
  | .waiting _ r _ => (c.slots p).round < r
  | .publishing _ r _ => (c.slots p).round < r
  | .returning _ r _ => (c.slots p).round = r

theorem slotShape_congr {c d : Configuration (n := n) obj} {p : Fin n}
    (hl : d.localState p = c.localState p) (hs : d.slots p = c.slots p)
    (h : SlotShape obj c p) : SlotShape obj d p := by
  unfold SlotShape at h ⊢
  rw [hl, hs]
  exact h

variable [DecidableEq Op]

/-- Only `p` writes `S[p]`. -/
theorem stepBy_slots_other {H : Environment (n := n) obj} {p q : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H q c d) (hpq : p ≠ q) :
    d.slots p = c.slots p := by
  cases h.1 with
  | publish q' cmd r s hq =>
      obtain rfl := eq_of_update_ne h.moves
      simp [update, hpq]
  | _ => rfl

theorem slotShape_step {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) (hc : ∀ p, SlotShape obj c p) : ∀ p, SlotShape obj d p := by
  intro p
  obtain ⟨q, hq⟩ := exists_stepBy obj hs
  by_cases hpq : p = q
  · subst hpq
    have hcp := hc p
    cases hq.1 with
    | read q' q'' cmd todo seed h =>
        obtain rfl := eq_of_update_ne hq.moves
        unfold SlotShape at hcp ⊢
        rw [h] at hcp
        simp only [update, ite_true]
        intro hnot
        rw [best_round]
        by_cases hself : q'' = q'
        · subst hself; exact Nat.le_max_right _ _
        · exact Nat.le_trans (hcp (by simp [hnot, Ne.symm hself])) (Nat.le_max_left _ _)
    | collected q' cmd seed h =>
        obtain rfl := eq_of_update_ne hq.moves
        unfold SlotShape at hcp ⊢
        rw [h] at hcp
        simp only [update, ite_true]
        exact hcp (by simp)
    | propose q' cmd seed h hi =>
        obtain rfl := eq_of_update_ne hq.moves
        unfold SlotShape at hcp ⊢
        rw [h] at hcp
        simp only [update, ite_true]
        omega
    | receive q' cmd r prop s flag h ho =>
        obtain rfl := eq_of_update_ne hq.moves
        have hlt : (c.slots q').round < r := by
          unfold SlotShape at hcp; rw [h] at hcp; exact hcp
        by_cases hf : flag = true ∧ 0 < (Tagged obj).traceCount cmd s
        · simp only [SlotShape, update, ite_true, ite_eq_left hf]
          exact hlt
        · simp only [SlotShape, update, ite_true, ite_eq_right hf]
          omega
    | invoke q' op h order horder =>
        obtain rfl := eq_of_update_ne hq.moves
        unfold SlotShape
        simp only [update, ite_true]
        exact fun hnot => absurd (horder.mem_iff.mpr (List.mem_finRange _)) hnot
    | publish _ _ _ _ _ | finish _ _ _ _ _ =>
        obtain rfl := eq_of_update_ne hq.moves
        simp [SlotShape, update]
  · exact slotShape_congr obj (hq.2 p hpq) (stepBy_slots_other obj hq hpq) (hc p)

theorem slotShape {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : ∀ p, SlotShape obj c p := by
  induction hc with
  | initial => intro p; simp [SlotShape, WeakUniversal.initial]
  | step _ hs ih => exact slotShape_step obj hs ih

/-- The round `p` is working towards, counting its register: the round it is
heading for, or one past the round `S[p]` records.  Unlike `nextRound`, it does
not fall back to `0` between operations. -/
def roundLevel (c : Configuration (n := n) obj) (p : Fin n) : Nat :=
  max (nextRound obj (c.localState p)) ((c.slots p).round + 1)

/-- Progress rank inside one level.  A finished operation ranks highest: the
next operation starts at the same level. -/
def levelRank : Local (n := n) obj → Nat
  | .idle => n + 5
  | .collecting _ todo _ => 4 + todo.length
  | .ready _ _ => 3
  | .waiting _ _ _ => 2
  | .publishing _ _ _ => 1
  | .returning _ _ _ => n + 6

omit [DecidableEq Op] in
theorem levelRank_le {c : Configuration (n := n) obj}
    (hb : ∀ p cmd todo seed, c.localState p = .collecting cmd todo seed → todo.length ≤ n)
    (p : Fin n) : levelRank obj (c.localState p) ≤ n + 6 := by
  cases h : c.localState p with
  | collecting cmd todo seed =>
      have := hb p cmd todo seed h
      simp only [levelRank]; omega
  | _ => simp only [levelRank]; omega

omit [DecidableEq Op] in
/-- A waiting process is at the level of the round it waits on. -/
theorem roundLevel_waiting {c : Configuration (n := n) obj} {p : Fin n}
    (hs : SlotShape obj c p) {cmd : Cmd n Op} {r : Nat} {prop : (Tagged (n := n) obj).Trace}
    (h : c.localState p = .waiting cmd r prop) : roundLevel obj c p = r := by
  unfold SlotShape at hs
  rw [h] at hs
  unfold roundLevel
  rw [h]
  simp only [nextRound]
  omega

/-- **Every step of `p` makes progress**: it raises `p`'s level or keeps it and
lowers its rank. -/
theorem stepBy_roundLevel {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) (hs : SlotShape obj c p) :
    roundLevel obj c p < roundLevel obj d p ∨
      (roundLevel obj c p = roundLevel obj d p ∧
        levelRank obj (d.localState p) < levelRank obj (c.localState p)) := by
  unfold SlotShape at hs
  cases h.1 with
  | invoke q op hq order horder =>
      obtain rfl := eq_of_update_ne h.moves
      right
      constructor
      · simp only [roundLevel, update, ite_true, hq, nextRound, zeroSeed]
        all_goals omega
      · simp only [levelRank, update, ite_true, hq, horder.length_eq, List.length_finRange]
        all_goals omega
  | read q q' cmd todo seed hq =>
      obtain rfl := eq_of_update_ne h.moves
      have hb := best_round_left obj seed (c.slots q')
      rcases Nat.lt_or_ge (max (seed.round + 1) ((c.slots q).round + 1))
          (max ((best obj seed (c.slots q')).round + 1) ((c.slots q).round + 1)) with hlt | hge
      · left
        simp only [roundLevel, update, ite_true, hq, nextRound]
        exact hlt
      · right
        constructor
        · simp only [roundLevel, update, ite_true, hq, nextRound]
          all_goals omega
        · simp only [levelRank, update, ite_true, hq, List.length_cons]
          all_goals omega
  | collected q cmd seed hq =>
      obtain rfl := eq_of_update_ne h.moves
      rw [hq] at hs
      dsimp only at hs
      have hle := hs (by simp)
      right
      constructor
      · simp only [roundLevel, update, ite_true, hq, nextRound]
        all_goals omega
      · simp only [levelRank, update, ite_true, hq, List.length_nil]
        all_goals omega
  | receive q cmd r prop s flag hq ho =>
      obtain rfl := eq_of_update_ne h.moves
      rw [hq] at hs
      dsimp only at hs
      by_cases hc : flag = true ∧ 0 < (Tagged obj).traceCount cmd s
      · right
        constructor
        · simp only [roundLevel, update, ite_true, hq, nextRound, ite_eq_left hc]
          all_goals omega
        · simp only [levelRank, update, ite_true, hq, ite_eq_left hc]
          all_goals omega
      · left
        simp only [roundLevel, update, ite_true, hq, nextRound, ite_eq_right hc]
        all_goals omega
  | publish q cmd r s hq =>
      obtain rfl := eq_of_update_ne h.moves
      rw [hq] at hs
      dsimp only at hs
      left
      simp only [roundLevel, update, ite_true, hq, nextRound]
      all_goals omega
  | propose _ _ _ hq _ | finish _ _ _ _ hq =>
      obtain rfl := eq_of_update_ne h.moves
      rw [hq] at hs
      dsimp only at hs
      right
      constructor
      · simp only [roundLevel, update, ite_true, hq, nextRound]
        all_goals omega
      · simp only [levelRank, update, ite_true, hq]
        all_goals omega

/-- From `idle` a process can only invoke, which starts a full collect, in some
order. -/
theorem stepBy_from_idle_collecting {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) (hc : c.localState p = .idle) :
    ∃ cmd, ∃ order : List (Fin n), order.Perm (List.finRange n) ∧
      d.localState p = .collecting cmd order (zeroSeed obj) := by
  cases h.1 with
  | invoke q op hq order horder =>
      obtain rfl := eq_of_update_ne h.moves
      exact ⟨⟨op, q, c.sequence q + 1⟩, order, horder, by simp [update]⟩
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- From `returning` a process can only finish: Line 11 records the response,
and neither the calls nor the registers change. -/
theorem stepBy_from_returning {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {r : Nat} {s : (Tagged (n := n) obj).Trace}
    (hc : c.localState p = .returning cmd r s) :
    d.localState p = .idle ∧ d.calls = c.calls ∧ d.slots = c.slots ∧
      (⟨cmd, r, s⟩ : Return (n := n) obj) ∈ d.returns := by
  cases h.1 with
  | finish q cmd' r' s' hq =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, rfl⟩ := Local.returning.inj (hq.symm.trans hc)
      exact ⟨by simp [update], rfl, rfl, List.mem_cons_self⟩
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace WeakRun
variable (g : WeakRun obj H)

/-- A process's level never decreases, whoever takes the step. -/
theorem roundLevel_step (p : Fin n) (t : Nat) :
    WeakUniversal.roundLevel obj (g.run.state t) p ≤
      WeakUniversal.roundLevel obj (g.run.state (t + 1)) p := by
  rcases g.step_actor t with ⟨-, heq⟩ | ⟨q, -, hstep⟩ | ⟨q, r, -, -, heq⟩
  · rw [heq]; exact Nat.le_refl _
  · by_cases hqp : q = p
    · subst hqp
      rcases WeakUniversal.stepBy_roundLevel obj hstep
          (WeakUniversal.slotShape obj (g.run.reachable obj t) q) with h | ⟨h, -⟩
      · exact Nat.le_of_lt h
      · exact Nat.le_of_eq h
    · have hl := hstep.2 p (fun h => hqp h.symm)
      have hs := WeakUniversal.stepBy_slots_other obj hstep (fun h => hqp h.symm)
      unfold WeakUniversal.roundLevel
      rw [hl, hs]; exact Nat.le_refl _
  · rw [heq]; exact Nat.le_refl _

theorem roundLevel_mono (p : Fin n) {a b : Nat} (hab : a ≤ b) :
    WeakUniversal.roundLevel obj (g.run.state a) p ≤
      WeakUniversal.roundLevel obj (g.run.state b) p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans (ih (by omega)) (g.roundLevel_step p (a + d))

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H)

private def lmu (g : WeakGCA obj H) (p : Fin n) (B t : Nat) : Nat :=
  (B - WeakUniversal.roundLevel obj (g.run.state t) p) * (n + 7)
    + WeakUniversal.levelRank obj ((g.run.state t).localState p)

/-- **A process that keeps taking steps reaches every level**, whether or not
its operations complete: each of its steps raises its level or lowers its rank,
and the rank is bounded. -/
theorem roundLevel_unbounded {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (T B : Nat) :
    ∃ t, T ≤ t ∧ B < WeakUniversal.roundLevel obj (g.run.state t) p := by
  classical
  apply Classical.byContradiction
  intro hcon
  have hbound : ∀ t, T ≤ t → WeakUniversal.roundLevel obj (g.run.state t) p ≤ B :=
    fun t ht => Nat.le_of_not_lt (fun h => hcon ⟨t, ht, h⟩)
  have hrankle : ∀ t, WeakUniversal.levelRank obj ((g.run.state t).localState p) ≤ n + 6 :=
    fun t => WeakUniversal.levelRank_le obj
      (WeakUniversal.todo_bound obj (g.run.reachable obj t)) p
  have hdec : ∀ t, T ≤ t → WeakUniversal.StepBy obj (H) p
      (g.run.state t) (g.run.state (t + 1)) → lmu g p B (t + 1) < lmu g p B t := by
    intro t ht hs
    rcases WeakUniversal.stepBy_roundLevel obj hs
        (WeakUniversal.slotShape obj (g.run.reachable obj t) p) with hlt | ⟨heq, hrk⟩
    · have h1 : (B - WeakUniversal.roundLevel obj (g.run.state (t + 1)) p) + 1
            ≤ B - WeakUniversal.roundLevel obj (g.run.state t) p := by
        have := hbound (t + 1) (by omega); have := hbound t ht; omega
      have h2 := Nat.mul_le_mul_right (n + 7) h1
      rw [Nat.succ_mul] at h2
      have h3 := hrankle (t + 1)
      simp only [lmu]
      omega
    · simp only [lmu, heq]
      omega
  have hmono : ∀ t, T ≤ t → lmu g p B (t + 1) ≤ lmu g p B t := by
    intro t ht
    by_cases hs : WeakUniversal.StepBy obj (H) p
        (g.run.state t) (g.run.state (t + 1))
    · exact Nat.le_of_lt (hdec t ht hs)
    · have hl := g.localState_stable_of_no_step hs
      have hlev : WeakUniversal.roundLevel obj (g.run.state (t + 1)) p
          = WeakUniversal.roundLevel obj (g.run.state t) p := by
        apply Nat.le_antisymm _ (g.roundLevel_step p t)
        have := hbound (t + 1) (by omega)
        rcases g.step_actor t with ⟨-, heq⟩ | ⟨q, -, hstep⟩ | ⟨q, r, -, -, heq⟩
        · rw [heq]; exact Nat.le_refl _
        · by_cases hqp : q = p
          · subst hqp; exact absurd hstep hs
          · have hs' := WeakUniversal.stepBy_slots_other obj hstep (fun h => hqp h.symm)
            unfold WeakUniversal.roundLevel
            rw [hl, hs']; exact Nat.le_refl _
        · rw [heq]; exact Nat.le_refl _
      simp only [lmu, hl, hlev]
      exact Nat.le_refl _
  refine no_infinite_decrease (μ := fun t => lmu g p B (T + t)) (fun t => ?_) (fun N => ?_)
  · exact hmono (T + t) (by omega)
  · obtain ⟨t, ht, hs⟩ := g.steps_infinitely hsched (T + N)
    refine ⟨t - T, by omega, ?_⟩
    rw [show T + (t - T) = t by omega, show T + (t - T + 1) = t + 1 by omega]
    exact hdec t (by omega) hs

/-- **A process that keeps taking steps waits in a GCA call again and again.**
From any local state, its next steps lead to `waiting`: through the collect of
the current operation, or through `publish`, `finish` and the next `invoke`. -/
theorem reaches_waiting_from {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (t : Nat) :
    ∃ u, t ≤ u ∧ ∃ cmd r prop, (g.run.state u).localState p = .waiting cmd r prop := by
  -- from `idle`, the next step invokes and the collect leads to `waiting`
  have from_idle : ∀ t, (g.run.state t).localState p = .idle →
      ∃ u, t ≤ u ∧ ∃ cmd r prop, (g.run.state u).localState p = .waiting cmd r prop := by
    intro t hL
    obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched t
    obtain ⟨cmd, order, -, hcol⟩ :=
      WeakUniversal.stepBy_from_idle_collecting obj hstep (hconst.trans hL)
    obtain ⟨u, hu, cmd', r', prop', hL', -⟩ :=
      g.reaches_waiting hsched _ (v + 1) (Nat.le_refl _)
        (by rw [hcol]; simp only [WeakUniversal.rank]; omega)
    exact ⟨u, by omega, cmd', r', prop', hL'⟩
  -- from `returning`, the next step finishes
  have from_returning : ∀ t cmd r s,
      (g.run.state t).localState p = .returning cmd r s →
      ∃ u, t ≤ u ∧ ∃ cmd r prop, (g.run.state u).localState p = .waiting cmd r prop := by
    intro t cmd r s hL
    obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched t
    obtain ⟨hidle, -⟩ := WeakUniversal.stepBy_from_returning obj hstep (hconst.trans hL)
    obtain ⟨u, hu, rest⟩ := from_idle (v + 1) hidle
    exact ⟨u, by omega, rest⟩
  cases hL : (g.run.state t).localState p with
  | waiting cmd r prop => exact ⟨t, Nat.le_refl _, cmd, r, prop, hL⟩
  | idle => exact from_idle t hL
  | returning cmd r s => exact from_returning t cmd r s hL
  | publishing cmd r s =>
      obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched t
      have hret := WeakUniversal.stepBy_from_publishing obj hstep (hconst.trans hL)
      obtain ⟨u, hu, rest⟩ := from_returning (v + 1) cmd r s hret
      exact ⟨u, by omega, rest⟩
  | collecting _ _ _ | ready _ _ =>
      obtain ⟨u, hu, cmd', r', prop', hL', -⟩ :=
        g.reaches_waiting hsched _ t (Nat.le_refl _)
          (by rw [hL]; simp only [WeakUniversal.rank]; omega)
      exact ⟨u, hu, cmd', r', prop', hL'⟩

/-- **A process that keeps taking steps waits on arbitrarily high rounds**,
whether or not its operations complete.  This is how the solo process of
`th:WeakUCresolve` "invokes `GCA_{r*}.propose` for some round `r*` greater than
every round reached in `α`". -/
theorem waiting_above {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (B T : Nat) :
    ∃ u, T ≤ u ∧ ∃ cmd r prop, (g.run.state u).localState p = .waiting cmd r prop ∧ B < r := by
  obtain ⟨t, ht, hlev⟩ := g.roundLevel_unbounded hsched T B
  obtain ⟨u, hu, cmd, r, prop, hL⟩ := g.reaches_waiting_from hsched t
  have hmono := g.roundLevel_mono p hu
  have hr := WeakUniversal.roundLevel_waiting obj
    (WeakUniversal.slotShape obj (g.run.reachable obj u) p) hL
  exact ⟨u, by omega, cmd, r, prop, hL, by omega⟩

end WeakGCA
end ConflictFreedom.GlobalSchedule

/-! ## "Eventually weakly `α`-conflict-free", in §3's vocabulary -/

namespace ConflictFreedom.Execution
variable {n : Nat} {Op : Type} (e : Execution n Op)

/-- The instance takes an operation step at or after operation time `B`. -/
def StepsFrom (B : Nat) (i : e.Instance) : Prop := ∃ t, B ≤ t ∧ e.actor t = some i

/-- **Eventually weakly `α`-conflict-free**, for the prefix `α` that ends at
operation time `B`: the execution has a suffix in which no two concurrent
operation instances *that take steps after `α`* are conflicting.  (Concurrent
in a suffix means simultaneously pending at a time of the suffix, as in
`EventuallyConflictFree`.) -/
def EventuallyWeaklyConflictFree (conflict : Op → Op → Prop) (B : Nat) : Prop :=
  ∃ N, ∀ t, N ≤ t → ∀ i j, i ≠ j → e.Pending i t → e.Pending j t →
    e.StepsFrom B i → e.StepsFrom B j → ¬ conflict (e.operation i) (e.operation j)

/-- The weak notion is implied by §3's: forgetting asks less of the execution. -/
theorem EventuallyConflictFree.weakly {conflict : Op → Op → Prop}
    (h : e.EventuallyConflictFree conflict) (B : Nat) :
    e.EventuallyWeaklyConflictFree conflict B := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun t ht i j hij hi hj _ _ => hN t ht i j hij hi hj⟩

/-- A later boundary constrains fewer instances. -/
theorem EventuallyWeaklyConflictFree.mono {conflict : Op → Op → Prop} {B B' : Nat}
    (h : e.EventuallyWeaklyConflictFree conflict B) (hB : B ≤ B') :
    e.EventuallyWeaklyConflictFree conflict B' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun t ht i j hij hi hj hsi hsj => hN t ht i j hij hi hj ?_ ?_⟩
  · obtain ⟨u, hu, hact⟩ := hsi; exact ⟨u, by omega, hact⟩
  · obtain ⟨u, hu, hact⟩ := hsj; exact ⟨u, by omega, hact⟩

end ConflictFreedom.Execution

/-! ## From the extracted execution to the program run -/

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace WeakRun
variable (g : WeakRun obj H) (hp : g.OpLive)

/-- **The boundary is exact.**  The extracted execution's operation time `t` is
the run's step `t + 1` (`InvocationLedger.obs`), so the prefix of the first `N`
steps of the run ends at operation time `N - 1`: an instance takes an operation
step from `N - 1` on exactly when its process is scheduled, running it, at a
time `≥ N`. -/
theorem stepsFrom_iff (i : (g.execution hp).Instance) (N : Nat) :
    (g.execution hp).StepsFrom (N - 1) i ↔ g.ActiveAfter N i.val := by
  constructor
  · rintro ⟨t, ht, hact⟩
    have hsch := (g.schedule hp).actorInst_val hact
    obtain ⟨p, hpt, hactive⟩ := g.opActor_eq_some hsch
    have htag := ((WeakUniversal.identity_invariant obj
      (g.run.reachable obj (t + 1))).active_tag p i.val hactive).1
    refine ⟨t + 1, by omega, by rw [htag]; exact hpt, ?_⟩
    rw [htag]
    exact hactive
  · rintro ⟨u, hu, hact, hcmd⟩
    obtain ⟨t, rfl⟩ : ∃ t, u = t + 1 := by
      refine ⟨u - 1, ?_⟩
      rcases Nat.eq_zero_or_pos u with rfl | hpos
      · rw [g.run.initial_state] at hcmd
        simp [WeakUniversal.initial, WeakUniversal.activeCmd, WeakUniversal.Local.command] at hcmd
      · omega
    have hop : g.opActor t = some i.val := by
      unfold WeakRun.opActor
      rw [hact]
      exact hcmd
    obtain ⟨i', hi', hval⟩ := (g.schedule hp).actorInst_of_actor hop
    have : i' = i := Subtype.ext hval
    subst this
    exact ⟨t, by omega, hi'⟩

/-- **The manuscript's hypothesis transfers to the program run.**  From §3's
eventual weak conflict-freedom of the extracted execution, for the prefix of
the first `N` steps, to `EventuallyWeaklyNonconflicting N`. -/
theorem eventuallyWeaklyNonconflicting_of_execution {N : Nat}
    (h : (g.execution hp).EventuallyWeaklyConflictFree obj.Conflict (N - 1)) :
    ∃ T₀, g.EventuallyWeaklyNonconflicting N T₀ := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M + 1, ?_⟩
  intro t ht a b hai har hbi hbr hab haA hbA
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  let ia : (g.execution hp).Instance := ⟨a, ⟨t', hai⟩⟩
  let ib : (g.execution hp).Instance := ⟨b, ⟨t', hbi⟩⟩
  have hpa : (g.execution hp).Pending ia t' := by
    refine ((g.schedule hp).execution_pending_iff ia t').mpr ⟨hai, fun hm => ?_⟩
    obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
    exact har ret hret he
  have hpb : (g.execution hp).Pending ib t' := by
    refine ((g.schedule hp).execution_pending_iff ib t').mpr ⟨hbi, fun hm => ?_⟩
    obtain ⟨ret, hret, he⟩ := List.mem_map.mp hm
    exact hbr ret hret he
  refine (obj.independent_iff_not_conflict a.operation b.operation).mpr ?_
  exact hM t' (by omega) ia ib (fun he => hab (congrArg Subtype.val he)) hpa hpb
    ((g.stepsFrom_iff hp ia N).mpr haA) ((g.stepsFrom_iff hp ib N).mpr hbA)

end WeakRun
end ConflictFreedom.GlobalSchedule

/-! ## Theorem `th:WeakUCresolve` over any GCA meeting the interface

A finite execution `α` is the first `N` steps of a run `g`; a run `g'` over any
GCA objects extends it when it takes the same first `N` steps (`Extends`).
`ConflictForgetting` is the manuscript's Definition *conflict-forgetting
execution*, quantifying over every such extension whose GCA objects meet the
interface and Solo agreement.  `WeakGCA.weakUCresolve` is Theorem
`th:WeakUCresolve` in its modular form: **every** `i`-solo continuation of `α`
has a finite conflict-forgetting prefix longer than `α`.  That a solo
continuation exists is a fact about the GCA objects' implementation, not about a
table: for **any** implementation meeting the specification of §4.2
(`GCAMachine.IsGCA`), it is the implementation's run under `soloSched`, which
gives the manuscript's statement for every such implementation with Solo
agreement (`WeakUniversal.Over.weakUCresolve`, in `Algorithm1OverGCA`), and for
Algorithm 2 in particular (`WeakUniversal.Forward.weakUCresolve` below, and
`WeakUniversal.Over.weakUCresolve_algorithm2`). -/

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}

namespace WeakRun

/-- **An extension of a finite execution.**  The finite execution is the first
`N` steps of `g`; the run `g'`, over any GCA objects, extends it when it takes
the same first `N` steps — the same process at every step, reaching the same
configurations. -/
def Extends {H' : WeakUniversal.Environment (n := n) obj} (g' : WeakRun obj H')
    (g : WeakRun obj H) (N : Nat) : Prop :=
  (∀ t, t < N → g'.actor t = g.actor t) ∧ ∀ t, t ≤ N → g'.run.state t = g.run.state t

/-- **Definition *conflict-forgetting execution*, over any GCA meeting the
interface.**  The finite execution `α` of the first `N` steps of `g` is
conflict-forgetting if in every eventually weakly `α`-conflict-free infinite
extension of `α` — a run over any GCA objects that meet the interface and Solo
agreement — some process that takes infinitely many steps (so a correct one)
completes each of its operations.  `α` ends at the extracted execution's
operation time `N - 1` (`stepsFrom_iff`). -/
def ConflictForgetting (g : WeakRun obj H) (N : Nat) : Prop :=
  ∀ (H' : WeakUniversal.Environment (n := n) obj) (g' : WeakGCA obj H'), g'.SoloAgreement →
    ∀ hp : g'.OpLive, g'.Extends g N →
    (g'.execution hp).EventuallyWeaklyConflictFree obj.Conflict (N - 1) →
    ∃ p, (g'.execution hp).InfiniteSteps p ∧
      ∀ j, (g'.execution hp).owner j = p → (g'.execution hp).Completes j

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H)

/-- **The solo extension, over any GCA meeting the interface.**  If only `i` is
scheduled after the first `N` steps, then at some time `N' > N` it has waited on
a round `R` above every round called in the first `N` steps, received
`(prop, true)` from it — it is that round's only participant — published, and
returned: its command `cmd` is answered.  At `N'` no call above `R` has been
made, and only `i` has called `R`.  This is the first paragraph of the
manuscript's proof; only the interface's six properties and termination are
used. -/
theorem solo_extension {N : Nat} {i : Fin n} (hsolo : g.SoloFrom N i) :
    ∃ N' v R cmd prop, N < N' ∧ v < N' ∧
      (g.run.state v).localState i = .waiting cmd R prop ∧
      (g.run.state (v + 1)).localState i = .publishing cmd R prop ∧
      (∀ call ∈ (g.run.state N).calls, call.round < R) ∧
      (∀ call ∈ (g.run.state N').calls, call.round ≤ R) ∧
      (∀ call ∈ (g.run.state N').calls, call.round = R → call.process = i) ∧
      (⟨cmd, R, prop⟩ : WeakUniversal.Return (n := n) obj) ∈ (g.run.state N').returns ∧
      cmd.process = i := by
  classical
  have hsched := hsolo.sched
  -- every round called in the first `N` steps is at most `B`
  obtain ⟨B, hB⟩ := WeakUniversal.calls_round_bound obj (g.run.state N).calls
  have hown : ∀ (t : Nat) (call : WeakUniversal.Call (n := n) obj),
      call ∈ (g.run.state t).calls → B < call.round → call.process = i := by
    intro t call hcall hlt
    apply Classical.byContradiction
    intro hne
    rcases Nat.le_total N t with hNt | htN
    · exact absurd (hB call (g.calls_of_solo hsolo hNt hcall hne)) (by omega)
    · exact absurd (hB call (g.calls_mono htN hcall)) (by omega)
  -- `i` waits on a round `R > B`
  obtain ⟨u, hu, cmd, R, prop, hL, hRB⟩ := g.waiting_above hsched B N
  obtain ⟨hcall, hcount⟩ :=
    WeakUniversal.waiting_call obj (g.run.reachable obj u) i cmd R prop hL
  have hin : (H R).input i = some prop := by
    simpa using WeakUniversal.call_input obj (g.run.reachable obj u) _ hcall
  have hproc : cmd.process = i :=
    ((WeakUniversal.identity_invariant obj (g.run.reachable obj u)).active_tag i cmd
      (by simp [WeakUniversal.ledger, hL, WeakUniversal.Local.command])).1
  obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
  -- alone in `R`, it receives its own proposal, committed
  obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched u
  obtain ⟨s, flag, hout, hnew⟩ :=
    WeakUniversal.stepBy_from_waiting obj hstep (hconst.trans hL)
  obtain ⟨hs, hflag⟩ := g.solo_round_commits hown (show B < R' + 1 by omega) hin hout
  subst hs; subst hflag
  have hpub : (g.run.state (v + 1)).localState i = .publishing cmd (R' + 1) s := by
    rw [hnew]
    split
    · rfl
    · rename_i hneg
      exact absurd ⟨rfl, hcount⟩ hneg
  -- it publishes, and returns
  obtain ⟨w, hw1, hconst1, hstep1⟩ := g.next_step hsched (v + 1)
  have hret : (g.run.state (w + 1)).localState i = .returning cmd (R' + 1) s :=
    WeakUniversal.stepBy_from_publishing obj hstep1 (hconst1.trans hpub)
  obtain ⟨z, hz, hconst2, hstep2⟩ := g.next_step hsched (w + 1)
  obtain ⟨-, hcalls, -, hmem⟩ :=
    WeakUniversal.stepBy_from_returning obj hstep2 (hconst2.trans hret)
  -- `i`'s own calls are at most `R`: a process never calls beyond its round
  have hbnd : ∀ call ∈ (g.run.state z).calls, call.process = i → call.round ≤ R' + 1 := by
    intro call hc hci
    have hb := (WeakUniversal.round_invariant obj (g.run.reachable obj z)).2.bounded call hc
    rw [hci] at hb
    simpa [WeakUniversal.currentRound, hconst2.trans hret, WeakUniversal.Local.round] using hb
  have hcallsN' : ∀ call ∈ (g.run.state (z + 1)).calls, call.round ≤ R' + 1 := by
    intro call hc
    rw [hcalls] at hc
    by_cases hci : call.process = i
    · exact hbnd call hc hci
    · have := hB call (g.calls_of_solo hsolo (by omega) hc hci)
      omega
  refine ⟨z + 1, v, R' + 1, cmd, s, by omega, by omega, hconst.trans hL, hpub, ?_, hcallsN', ?_,
    hmem, hproc⟩
  · intro call hc
    have := hB call hc
    omega
  · intro call hc hr
    apply Classical.byContradiction
    intro hci
    rw [hcalls] at hc
    have := hB call (g.calls_of_solo hsolo (by omega) hc hci)
    omega

/-- **Theorem `th:WeakUCresolve`, over any GCA meeting the interface and Solo
agreement.**  For every finite execution `α` — the first `N` steps of a run `g`
of Algorithm 1 — and every process `i`: if only `i` is scheduled after `α`, then
some prefix of `g` of length `N' > N`, an `i`-solo extension of `α`, is
conflict-forgetting.  The extension's GCA objects are only required to meet the
interface and Solo agreement; `g` itself need not meet Solo agreement. -/
theorem weakUCresolve {N : Nat} {i : Fin n} (hsolo : g.SoloFrom N i) :
    ∃ N', N < N' ∧ g.ConflictForgetting N' := by
  obtain ⟨N', v, R, cmd, prop, hNN', hv, hwait, hpub, -, hbound, hsoloR, -, -⟩ :=
    g.solo_extension hsolo
  refine ⟨N', hNN', ?_⟩
  intro H' g' hsa hp hext hweak
  have hst := hext.2
  obtain ⟨T₀, hC⟩ := g'.eventuallyWeaklyNonconflicting_of_execution hp hweak
  obtain ⟨p, hstep, hall⟩ := g'.forgetting_completes hsa (g'.live_of_opLive hp) hv
    (by rw [hst v (by omega)]; exact hwait) (by rw [hst (v + 1) (by omega)]; exact hpub)
    (by rw [hst N' (Nat.le_refl _)]; exact hsoloR) (by rw [hst N' (Nat.le_refl _)]; exact hbound)
    hC
  exact ⟨p, g'.infiniteSteps_of_stepping hp hstep, fun j hj =>
    g'.execution_completes_of_completes hp (hall j.val (g'.invoked_of_instance hp j) hj)⟩

end WeakGCA
end ConflictFreedom.GlobalSchedule

/-! ## Finite executions of the machine, their extensions, and the theorem -/

namespace ConflictFreedom.WeakUniversal.Forward
open Object UniversalProtocol ForwardGCA

variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

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
operations invoked after `α`, and the rule for the collect order on the choices
made after `α`. -/
def Extends (ch' : Choices (n := n) obj) (client' : Fin n → Nat → Op) (sched' : Nat → Option (Fin n))
    (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) : Prop :=
  (∀ t, t < N → sched' t = sched t) ∧
    ∀ t, t ≤ N → frun obj ch' client' sched' t = frun obj ch client sched t

/-- The §3 execution of a non-halting run of the machine — an execution of
`forward1`. -/
noncomputable def execution (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome) : _root_.ConflictFreedom.Execution n Op :=
  (fsched obj ch client sched).execution (fsched_opLive obj ch client sched hlive)

theorem execution_forward1 (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome) :
    forward1 obj n (execution obj ch client sched hlive) :=
  ⟨client, ch, sched, hlive, rfl⟩

/-- **Definition *conflict-forgetting execution*.**  The finite execution `α`
(the first `N` steps of `frun ch client sched`) is conflict-forgetting if in every
eventually weakly `α`-conflict-free infinite extension of `α`, some correct
process completes each of its operations.

"Infinite" is the scheduler not halting, as in `forward1`.  `α` ends at the
extracted execution's operation time `N - 1` (`stepsFrom_iff`).  The process
exhibited takes infinitely many steps, so it is correct
(`ConflictForgetting.correct` gives the literal wording), and it is not an idle
process that completes its operations vacuously. -/
def ConflictForgetting (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (N : Nat) : Prop :=
  ∀ (ch' : Choices (n := n) obj) (client' : Fin n → Nat → Op) (sched' : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched' t).isSome),
    Extends obj ch' client' sched' ch client sched N →
    (execution obj ch' client' sched' hlive).EventuallyWeaklyConflictFree obj.Conflict (N - 1) →
    ∃ p, (execution obj ch' client' sched' hlive).InfiniteSteps p ∧
      ∀ i, (execution obj ch' client' sched' hlive).owner i = p →
        (execution obj ch' client' sched' hlive).Completes i

/-- The manuscript's literal wording: in every such extension, *some correct
process* completes each of its operations. -/
theorem ConflictForgetting.correct {ch : Choices (n := n) obj} {client : Fin n → Nat → Op} {sched : Nat → Option (Fin n)}
    {N : Nat} (h : ConflictForgetting obj ch client sched N)
    (ch' : Choices (n := n) obj) (client' : Fin n → Nat → Op) (sched' : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched' t).isSome)
    (hext : Extends obj ch' client' sched' ch client sched N)
    (hweak : (execution obj ch' client' sched' hlive).EventuallyWeaklyConflictFree obj.Conflict (N - 1)) :
    ∃ p, (execution obj ch' client' sched' hlive).Correct p ∧
      ∀ i, (execution obj ch' client' sched' hlive).owner i = p →
        (execution obj ch' client' sched' hlive).Completes i := by
  obtain ⟨p, hp, hall⟩ := h ch' client' sched' hlive hext hweak
  exact ⟨p, Or.inl hp, hall⟩

/-- The scheduler that follows `sched` for `N` steps and then runs `i` alone. -/
def soloSched (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) : Nat → Option (Fin n) :=
  fun t => if t < N then sched t else some i

omit [DecidableEq Op] in
theorem soloSched_before {sched : Nat → Option (Fin n)} {N : Nat} {i : Fin n} {t : Nat}
    (ht : t < N) : soloSched sched N i t = sched t := by
  simp [soloSched, ht]

omit [DecidableEq Op] in
theorem soloSched_after {sched : Nat → Option (Fin n)} {N : Nat} {i : Fin n} {t : Nat}
    (ht : N ≤ t) : soloSched sched N i t = some i := by
  simp [soloSched, show ¬ t < N by omega]

/-- **The solo extension.**  After the first `N` steps of any run, let `i` run
alone.  At some time `N' > N`, `i` has waited on a round `R` above every round
called in the first `N` steps, received `(prop, true)` from it — it is the only
participant — published, and returned: its command `cmd` is answered.  At `N'`
no call above `R` has been made, and only `i` has called `R`. -/
theorem solo_extension (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (N : Nat) (i : Fin n) :
    ∃ N' v R cmd prop, N < N' ∧ v < N' ∧
      (frun obj ch client (soloSched sched N i) v).1.localState i = .waiting cmd R prop ∧
      (frun obj ch client (soloSched sched N i) (v + 1)).1.localState i = .publishing cmd R prop ∧
      (∀ call ∈ (frun obj ch client (soloSched sched N i) N).1.calls, call.round < R) ∧
      (∀ call ∈ (frun obj ch client (soloSched sched N i) N').1.calls, call.round ≤ R) ∧
      (∀ call ∈ (frun obj ch client (soloSched sched N i) N').1.calls,
        call.round = R → call.process = i) ∧
      (⟨cmd, R, prop⟩ : Return (n := n) obj) ∈ (frun obj ch client (soloSched sched N i) N').1.returns ∧
      cmd.process = i :=
  ((fsched obj ch client (soloSched sched N i)).toGCA (fsched_fair obj ch client _)
    (fam_waitFree obj ch client _)).solo_extension
    (FiniteScheduling.SoloFrom.of_continuous _ fun _ ht => soloSched_after ht)

/-- **Theorem `th:WeakUCresolve`.**  For every finite execution `α` of
Algorithm 1 — the first `N` steps of the machine's run for any client and any
scheduler — and every process `i`, there is a finite conflict-forgetting
`i`-solo extension of `α`: the first `N'` steps of the run that follows `α`
and then schedules only `i`. -/
theorem weakUCresolve (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictForgetting obj ch client (soloSched sched N i) N' := by
  obtain ⟨N', hNN', hcf⟩ := ((fsched obj ch client (soloSched sched N i)).toGCA
    (fsched_fair obj ch client _) (fam_waitFree obj ch client _)).weakUCresolve
    (FiniteScheduling.SoloFrom.of_continuous _ fun _ ht => soloSched_after ht)
  refine ⟨N', hNN', ⟨fun t ht => soloSched_before ht,
      frun_congr obj (fun t ht => soloSched_before ht)⟩,
    fun t ht _ => soloSched_after ht, ?_⟩
  intro ch' client' sched' hlive hext hweak
  exact hcf _ ((fsched obj ch' client' sched').toGCA (fsched_fair obj ch' client' sched')
      (fam_waitFree obj ch' client' sched')) (fsched obj ch' client' sched').soloAgreement
    (fsched_opLive obj ch' client' sched' hlive)
    ⟨fun t ht => hext.1 t ht, fun t ht => congrArg Prod.fst (hext.2 t ht)⟩ hweak

end ConflictFreedom.WeakUniversal.Forward

/-! ## The definitions, checked against the machine -/

namespace ConflictFreedom.WeakUniversal.Forward
open Object UniversalProtocol ForwardGCA

variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- **"Takes steps after `α`", on the machine.**  In the execution of a run,
an instance takes an operation step from operation time `N - 1` on exactly when
its process is scheduled at some machine step `u ≥ N` — after the first `N`
steps — while running that instance.  So the boundary `N - 1` in
`ConflictForgetting` is the end of `α`, no earlier and no later. -/
theorem stepsFrom_iff (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n))
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (sched t).isSome)
    (j : (execution obj ch client sched hlive).Instance) (N : Nat) :
    (execution obj ch client sched hlive).StepsFrom (N - 1) j ↔
      ∃ u, N ≤ u ∧ sched u = some j.val.process ∧
        Local.command obj ((frun obj ch client sched u).1.localState j.val.process) = some j.val :=
  (fsched obj ch client sched).stepsFrom_iff (fsched_opLive obj ch client sched hlive) j N

/-- **The hypothesis of `ConflictForgetting` is satisfiable.**  Letting `i`
run alone for ever after `N` gives an infinite extension of the first `N'`
steps, for every `N' ≥ N`, that is eventually weakly conflict-free: after the
prefix only `i`'s instances take steps, and two of them are never pending at
once. -/
theorem soloSched_weaklyConflictFree (ch : Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n)
    (hlive : ∀ M, ∃ t, M ≤ t ∧ (soloSched sched N i t).isSome) {N' : Nat} (hN : N ≤ N') :
    (execution obj ch client (soloSched sched N i) hlive).EventuallyWeaklyConflictFree
      obj.Conflict (N' - 1) := by
  refine ⟨0, fun t _ ja jb hab ha hb hsa hsb => absurd ?_ hab⟩
  have own : ∀ j, (execution obj ch client (soloSched sched N i) hlive).StepsFrom (N' - 1) j →
      (execution obj ch client (soloSched sched N i) hlive).owner j = i := by
    intro j hj
    obtain ⟨u, hu, hs, -⟩ := (stepsFrom_iff obj ch client _ hlive j N').mp hj
    have := hs.symm.trans (soloSched_after (by omega))
    exact Option.some.inj this
  exact (execution obj ch client (soloSched sched N i) hlive).sequential ja jb t
    ((own ja hsa).trans (own jb hsb).symm) ha.1 hb.1 ha.2 hb.2

/-- The solo continuation never halts. -/
theorem soloSched_live (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) :
    ∀ M, ∃ t, M ≤ t ∧ (soloSched sched N i t).isSome :=
  fun M => ⟨max M N, Nat.le_max_left _ _, by rw [soloSched_after (Nat.le_max_right _ _)]; rfl⟩

/-- A run extends each of its own prefixes. -/
theorem extends_refl (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) :
    Extends obj ch client sched ch client sched N :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **`ConflictForgetting` is not vacuous.**  Every solo prefix of the form
`weakUCresolve` produces has an infinite extension meeting the definition's
hypothesis — the solo continuation itself — so the definition always has at
least one extension to speak about. -/
theorem conflictForgetting_hypothesis_satisfiable (ch : Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) {N' : Nat} (hN : N ≤ N') :
    ∃ hlive, Extends obj ch client (soloSched sched N i) ch client (soloSched sched N i) N' ∧
      (execution obj ch client (soloSched sched N i) hlive).EventuallyWeaklyConflictFree
        obj.Conflict (N' - 1) :=
  ⟨soloSched_live sched N i, extends_refl obj ch client _ N',
    soloSched_weaklyConflictFree obj ch client sched N i _ hN⟩

end ConflictFreedom.WeakUniversal.Forward

namespace ConflictFreedom
open WeakUniversal.Forward
variable {State Op Response : Type} [DecidableEq Op]

/-- **Theorem `th:WeakUCresolve`** (the same statement as
`WeakUniversal.Forward.weakUCresolve`): for every finite execution of Algorithm 1
as the machine runs it — the first `N` steps of `frun ch client sched` — and every
process `i`, the run that continues with `i` alone has a finite prefix of length
`N' > N` that is conflict-forgetting. -/
theorem forward1_weakUCresolve (obj : Object State Op Response) {n : Nat}
    (ch : Choices (n := n) obj) (client : Fin n → Nat → Op) (sched : Nat → Option (Fin n)) (N : Nat) (i : Fin n) :
    ∃ N', N < N' ∧
      Extends obj ch client (soloSched sched N i) ch client sched N ∧
      (∀ t, N ≤ t → t < N' → soloSched sched N i t = some i) ∧
      ConflictForgetting obj ch client (soloSched sched N i) N' :=
  weakUCresolve obj ch client sched N i

end ConflictFreedom
