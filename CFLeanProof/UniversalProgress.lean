import CFLeanProof.GCAConsequences
import CFLeanProof.GlobalSchedule
import CFLeanProof.ProgressCompatibility

/-!
# Local progress of the universal constructions

The paper's progress proofs both begin the same way: a process that keeps taking
steps and never completes must reach arbitrarily large GCA rounds.  This module
proves that from Algorithm 1's transition relation, by exhibiting a measure that
every step either advances (the round it is heading for) or strictly decreases
(a rank inside the round).

The schedule-level lemmas come in three namespaces:

* `GlobalSchedule.WeakRun` — facts about any run over any GCA histories, with no
  assumption on the GCA objects (`localState_stable`, `calls_mono`, …);
* `GlobalSchedule.WeakGCA` — facts about runs over GCA objects meeting the GCA
  interface (`steps_infinitely`, `next_step`, `solo_completes`, …): the only
  termination fact used is the interface's "every correct participant
  returns";
* `GlobalSchedule.Weak` — the composition with Algorithm 2: fairness at the
  receive (`Fair`) and `callsReturn`, the proof that Algorithm 2's calls return
  under the wait-free snapshot assumption.
-/

namespace ConflictFreedom.WeakUniversal
open Object
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The GCA round a local state is heading for.  A process in `ready` will
propose to `seed.round + 1`, so that is the round it is heading for. -/
def nextRound : Local (n := n) obj → Nat
  | .idle => 0
  | .collecting _ _ s => s.round + 1
  | .ready _ s => s.round + 1
  | .waiting _ r _ => r
  | .publishing _ r _ => r
  | .returning _ r _ => r

/-- Progress rank inside one round.  Every step that does not advance the round
strictly decreases it. -/
def rank : Local (n := n) obj → Nat
  | .idle => 0
  | .collecting _ todo _ => 4 + todo.length
  | .ready _ _ => 3
  | .waiting _ _ _ => 2
  | .publishing _ _ _ => 1
  | .returning _ _ _ => 0

/-- **The local progress measure.**  Every step of `p` either fires from the
returning state, advances the round `p` heads for, or strictly decreases the
rank inside the current round. -/
theorem stepBy_progress {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) :
    (∃ cmd r s, c.localState p = .returning cmd r s) ∨
    nextRound obj (c.localState p) < nextRound obj (d.localState p) ∨
    (nextRound obj (c.localState p) = nextRound obj (d.localState p) ∧
      rank obj (d.localState p) < rank obj (c.localState p)) := by
  cases h.1 with
  | invoke q op hq =>
      obtain rfl := eq_of_update_ne h.moves
      refine Or.inr (Or.inl ?_)
      simp [update, hq, nextRound]
  | read q q' cmd todo seed hq =>
      obtain rfl := eq_of_update_ne h.moves
      have hb := best_round_left obj seed (c.slots q')
      rcases Nat.lt_or_ge seed.round (best obj seed (c.slots q')).round with hlt | hge
      · exact Or.inr (Or.inl (by simp [update, hq, nextRound]; omega))
      · refine Or.inr (Or.inr ⟨by simp [update, hq, nextRound]; omega, ?_⟩)
        simp [update, hq, rank]
  | receive q cmd r proposal s flag hq ho =>
      obtain rfl := eq_of_update_ne h.moves
      by_cases hc : flag = true ∧ 0 < (Tagged obj).traceCount cmd s
      · exact Or.inr (Or.inr ⟨by simp [update, hq, nextRound, hc],
          by simp [update, hq, rank, hc]⟩)
      · exact Or.inr (Or.inl (by simp [update, hq, nextRound, hc]))
  | collected _ _ _ hq | propose _ _ _ hq _ | publish _ _ _ _ hq =>
      obtain rfl := eq_of_update_ne h.moves
      exact Or.inr (Or.inr ⟨by simp [update, hq, nextRound], by simp [update, hq, rank]⟩)
  | finish q cmd r s hq =>
      obtain rfl := eq_of_update_ne h.moves
      exact Or.inl ⟨cmd, r, s, hq⟩

/-- The collect list never exceeds the number of processes, so `rank` is
bounded by `4 + n`. -/
theorem todo_bound {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) :
    ∀ p cmd todo seed, c.localState p = .collecting cmd todo seed → todo.length ≤ n := by
  induction hc with
  | initial => intro p cmd todo seed h; simp [WeakUniversal.initial] at h
  | step _ hs ih =>
      cases hs with
      | invoke q op hq order horder =>
          intro p cmd todo seed h
          by_cases hqp : q = p
          · subst hqp; simp [update] at h; simp [← h.2.1, horder.length_eq]
          · exact ih p cmd todo seed (by simpa [update, Ne.symm hqp] using h)
      | read q q' cmd' todo' seed' hq =>
          intro p cmd todo seed h
          by_cases hqp : q = p
          · subst hqp
            have hlen := ih q cmd' (q' :: todo') seed' hq
            simp only [List.length_cons] at hlen
            simp only [update] at h
            obtain ⟨-, hte, -⟩ := h
            omega
          · exact ih p cmd todo seed (by simpa [update, Ne.symm hqp] using h)
      | receive q cmd' r prop' s flag hq ho =>
          intro p cmd todo seed h
          by_cases hqp : q = p
          · subst hqp; simp [update] at h; split at h <;> simp at h
          · exact ih p cmd todo seed (by simpa [update, Ne.symm hqp] using h)
      | collected q _ _ _ | propose q _ _ _ _ | publish q _ _ _ _ | finish q _ _ _ _ =>
          intro p cmd todo seed h
          by_cases hqp : q = p
          · subst hqp; simp [update] at h
          · exact ih p cmd todo seed (by simpa [update, Ne.symm hqp] using h)

omit [DecidableEq Op] in
theorem rank_le {c : Configuration (n := n) obj}
    (hb : ∀ p cmd todo seed, c.localState p = .collecting cmd todo seed → todo.length ≤ n)
    (p : Fin n) : rank obj (c.localState p) ≤ 4 + n := by
  cases h : c.localState p with
  | collecting cmd todo seed =>
      have := hb p cmd todo seed h
      simp only [rank]; omega
  | _ => simp only [rank]; omega

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom.WeakUniversal
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- From `returning`, the only available step is `finish`, which records the
response. -/
theorem stepBy_returning {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {r : Nat} {s : (Tagged (n := n) obj).Trace}
    (hc : c.localState p = .returning cmd r s) :
    (⟨cmd, r, s⟩ : Return (n := n) obj) ∈ d.returns := by
  cases h.1 with
  | finish q cmd' r' s' hq =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, rfl⟩ := Local.returning.inj (hq.symm.trans hc)
      exact List.mem_cons_self ..
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- A step never removes a call, and any call it adds belongs to the acting
process. -/
theorem stepBy_calls {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) :
    (∀ call ∈ c.calls, call ∈ d.calls) ∧
      (∀ call ∈ d.calls, call ∈ c.calls ∨ call.process = p) := by
  cases h.1 with
  | propose q cmd seed hq hi =>
      obtain rfl := eq_of_update_ne h.moves
      exact ⟨fun call hcall => List.mem_cons_of_mem _ hcall, fun call hcall => by
        rcases List.mem_cons.mp hcall with rfl | hm
        · exact Or.inr rfl
        · exact Or.inl hm⟩
  | _ => exact ⟨fun _ h => h, fun _ h => Or.inl h⟩

/-- Leaving `waiting` is the `receive` step: the round's output exists and
determines the next local state. -/
theorem stepBy_from_waiting {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {r : Nat} {prop : (Tagged (n := n) obj).Trace}
    (hc : c.localState p = .waiting cmd r prop) :
    ∃ s flag, (H r).output p = some (s, flag) ∧
      d.localState p = (if flag = true ∧ 0 < (Tagged (n := n) obj).traceCount cmd s
        then .publishing cmd r s else .ready cmd ⟨r, s⟩) := by
  cases h.1 with
  | receive q cmd' r' prop' s flag hq ho =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, rfl⟩ := Local.waiting.inj (hq.symm.trans hc)
      exact ⟨s, flag, ho, by simp [update]⟩
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- Leaving `publishing` is the `publish` step. -/
theorem stepBy_from_publishing {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {r : Nat} {s : (Tagged (n := n) obj).Trace}
    (hc : c.localState p = .publishing cmd r s) :
    d.localState p = .returning cmd r s := by
  cases h.1 with
  | publish q cmd' r' s' hq =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, rfl⟩ := Local.publishing.inj (hq.symm.trans hc)
      simp [update]
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

omit [DecidableEq Op] in
theorem update_self {α : Type} (fn : Fin n → α) (p : Fin n) (v : α) :
    update fn p v p = v := by simp [update]

/-- A process waiting in a round has recorded the corresponding call, and its
proposal contains its own command. -/
theorem waiting_call {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) :
    ∀ p cmd r prop, c.localState p = .waiting cmd r prop →
      (⟨r, p, prop⟩ : Call (n := n) obj) ∈ c.calls ∧
        0 < (Tagged (n := n) obj).traceCount cmd prop := by
  induction hc with
  | initial => intro p cmd r prop h; simp [WeakUniversal.initial] at h
  | step _ hs ih =>
    cases hs with
    | propose q cmd' seed hq hi =>
        intro p cmd r prop h
        by_cases hqp : q = p
        · subst hqp
          simp [update] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨List.mem_cons_self .., (Tagged (n := n) obj).appendMissing_contains _ _⟩
        · obtain ⟨h1, h2⟩ := ih p cmd r prop (by simpa [update, Ne.symm hqp] using h)
          exact ⟨List.mem_cons_of_mem _ h1, h2⟩
    | receive q cmd' r' prop' s flag hq ho =>
        intro p cmd r prop h
        by_cases hqp : q = p
        · subst hqp; simp [update] at h; split at h <;> simp at h
        · exact ih p cmd r prop (by simpa [update, Ne.symm hqp] using h)
    | invoke q _ _ | read q _ _ _ _ _ | collected q _ _ _ | publish q _ _ _ _ | finish q _ _ _ _ =>
        intro p cmd r prop h
        by_cases hqp : q = p
        · subst hqp; simp [update] at h
        · exact ih p cmd r prop (by simpa [update, Ne.symm hqp] using h)

omit [DecidableEq Op] in
theorem rank_eq_two {l : Local (n := n) obj} (h : rank obj l = 2) :
    ∃ cmd r proposal, l = .waiting cmd r proposal := by
  cases l with
  | waiting cmd r proposal => exact ⟨cmd, r, proposal, rfl⟩
  | collecting _ _ _ => simp only [rank] at h; omega
  | _ => simp [rank] at h

/-- From a `collecting` or `ready` state every step keeps the process on its way
to a proposal: the round it heads for does not decrease, the rank strictly
decreases, and it stays at rank at least two (that is, at `waiting` or before). -/
theorem stepBy_from_high_rank {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    (hr : 3 ≤ rank obj (c.localState p)) :
    nextRound obj (c.localState p) ≤ nextRound obj (d.localState p) ∧
      rank obj (d.localState p) < rank obj (c.localState p) ∧
      2 ≤ rank obj (d.localState p) := by
  cases h.1 with
  | read q q' cmd todo seed hq =>
      obtain rfl := eq_of_update_ne h.moves
      have hb := best_round_left obj seed (c.slots q')
      refine ⟨by simp [update, hq, nextRound]; omega, ?_, ?_⟩
      · simp [update, hq, rank]
      · simp [update, rank]; omega
  | collected _ _ _ hq | propose _ _ _ hq _ =>
      obtain rfl := eq_of_update_ne h.moves
      exact ⟨by simp [update, hq, nextRound], by simp [update, hq, rank],
        by simp [update, rank]⟩
  | invoke _ _ hq | receive _ _ _ _ _ _ hq _ | publish _ _ _ _ hq | finish _ _ _ _ hq =>
      obtain rfl := eq_of_update_ne h.moves
      rw [hq] at hr; simp [rank] at hr

omit [DecidableEq Op] in
/-- Any finite list of returns has a largest round. -/
theorem returns_round_bound (l : List (Return (n := n) obj)) :
    ∃ B, ∀ ret ∈ l, ret.round ≤ B := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨max a.round B, fun ret hret => ?_⟩
      rcases List.mem_cons.mp hret with rfl | hm
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (hB ret hm) (Nat.le_max_right _ _)

omit [DecidableEq Op] in
/-- Any finite list of calls has a largest round. -/
theorem calls_round_bound (l : List (Call (n := n) obj)) :
    ∃ B, ∀ call ∈ l, call.round ≤ B := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨max a.round B, fun call hcall => ?_⟩
      rcases List.mem_cons.mp hcall with rfl | hm
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (hB call hm) (Nat.le_max_right _ _)

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom

/-- A non-increasing `Nat` sequence cannot strictly decrease infinitely often. -/
theorem no_infinite_decrease {μ : Nat → Nat} (hmono : ∀ t, μ (t + 1) ≤ μ t)
    (hinf : ∀ N, ∃ t, N ≤ t ∧ μ (t + 1) < μ t) : False := by
  have chain : ∀ a b, a ≤ b → μ b ≤ μ a := by
    intro a b hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih =>
        exact Nat.le_trans (hmono (a + d)) (ih (by omega))
  have key : ∀ k, ∃ t, μ t + k ≤ μ 0 := by
    intro k
    induction k with
    | zero => exact ⟨0, by omega⟩
    | succ k ih =>
        obtain ⟨t, ht⟩ := ih
        obtain ⟨u, hu, hlt⟩ := hinf t
        have h1 : μ u ≤ μ t := chain t u hu
        exact ⟨u + 1, by omega⟩
  obtain ⟨t, ht⟩ := key (μ 0 + 1)
  omega

namespace GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op]

omit [DecidableEq Op] in
theorem weakRound_eq_some {l : WeakUniversal.Local (n := n) obj} {r : Nat}
    (h : weakRound obj l = some r) :
    ∃ cmd proposal, l = .waiting cmd r proposal := by
  cases l with
  | waiting cmd r' proposal =>
      exact ⟨cmd, proposal, by simpa [weakRound] using (Option.some.inj h) ▸ rfl⟩
  | _ => exact absurd h (by simp [weakRound])

namespace WeakRun
variable {H : WeakUniversal.Environment (n := n) obj} (g : WeakRun obj H)

/-- A process's local state changes only when it is the scheduled process. -/
theorem localState_stable {t : Nat} {p : Fin n} (h : g.actor t ≠ some p) :
    (g.run.state (t + 1)).localState p = (g.run.state t).localState p := by
  rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, hq, hstep⟩ | ⟨q, r, _, _, heq⟩
  · rw [heq]
  · exact hstep.2 p (fun hpq => h (hpq ▸ hq))
  · rw [heq]

/-- "Only `p` takes steps from `N` on", allowing idle instants. -/
abbrev SoloFrom (N : Nat) (p : Fin n) : Prop := FiniteScheduling.SoloFrom g.actor N p

/-- Under `SoloFrom`, at every late instant either `p` takes a program step or
the whole configuration is frozen -- the schedule may idle, and no other
process can move. -/
theorem step_or_frozen {N : Nat} {p : Fin n} (hsolo : g.SoloFrom N p)
    {t : Nat} (ht : N ≤ t) :
    WeakUniversal.StepBy obj (H) p (g.run.state t) (g.run.state (t + 1)) ∨
      g.run.state (t + 1) = g.run.state t := by
  rcases g.step_actor t with ⟨-, heq⟩ | ⟨q, hq, hstep⟩ | ⟨q, r, hq, -, heq⟩
  · exact Or.inr heq
  · exact Or.inl (hsolo.own t q ht hq ▸ hstep)
  · exact Or.inr heq

/-- When the scheduled process is `p`, either `p` takes a program step or `p` is
inside a GCA call and the program configuration stutters. -/
theorem step_or_stutter {t : Nat} {p : Fin n} (h : g.actor t = some p) :
    WeakUniversal.StepBy obj (H) p (g.run.state t) (g.run.state (t + 1)) ∨
      ((∃ r, weakRound obj ((g.run.state t).localState p) = some r) ∧
        g.run.state (t + 1) = g.run.state t) := by
  rcases g.step_actor t with ⟨hnone, _⟩ | ⟨q, hq, hstep⟩ | ⟨q, r, hq, hrd, heq⟩
  · exact absurd (hnone.symm.trans h) (by simp)
  · have : q = p := Option.some.inj (hq.symm.trans h)
    subst this
    exact Or.inl hstep
  · have : q = p := Option.some.inj (hq.symm.trans h)
    subst this
    exact Or.inr ⟨⟨r, hrd⟩, heq⟩

/-- `p`'s local state changes only at its own program steps. -/
theorem localState_stable_of_no_step {t : Nat} {p : Fin n}
    (h : ¬ WeakUniversal.StepBy obj (H) p
            (g.run.state t) (g.run.state (t + 1))) :
    (g.run.state (t + 1)).localState p = (g.run.state t).localState p := by
  rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
  · rw [heq]
  · by_cases hqp : q = p
    · subst hqp; exact absurd hstep h
    · exact hstep.2 p (fun e => hqp e.symm)
  · rw [heq]

/-- `p`'s local state is constant across an interval containing none of its
steps. -/
theorem localState_const {a b : Nat} {p : Fin n} (hab : a ≤ b)
    (h : ∀ v, a ≤ v → v < b → ¬ WeakUniversal.StepBy obj (H) p
      (g.run.state v) (g.run.state (v + 1))) :
    (g.run.state b).localState p = (g.run.state a).localState p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [show a + (d + 1) = (a + d) + 1 from rfl,
        g.localState_stable_of_no_step (h (a + d) (by omega) (by omega))]
      exact ih (by omega) (fun v hv _ => h v hv (by omega))

/-- Recorded calls never disappear. -/
theorem calls_mono {a b : Nat} (hab : a ≤ b) {call : WeakUniversal.Call (n := n) obj}
    (h : call ∈ (g.run.state a).calls) : call ∈ (g.run.state b).calls := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact h
  | succ d ih =>
      have hprev := ih (by omega)
      rcases g.step_actor (a + d) with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
      · rw [show a + (d + 1) = (a + d) + 1 from rfl, heq]; exact hprev
      · exact (WeakUniversal.stepBy_calls obj hstep).1 call hprev
      · rw [show a + (d + 1) = (a + d) + 1 from rfl, heq]; exact hprev

/-- In sufficiently high rounds every caller keeps stepping. This is derived
from finite process membership and call insertion, without fairness. -/
theorem eventually_callers_stepping :
    ∃ B, ∀ k, B ≤ k → ∀ q,
      (∃ s, (H (k + 2)).input q = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q := by
  have inserted : ∀ t (call : WeakUniversal.Call (n := n) obj),
      call ∈ (g.run.state (t + 1)).calls → call ∉ (g.run.state t).calls →
      g.actor t = some call.process := by
    intro t call hin hout
    rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, hq, hs⟩ | ⟨q, r, _, _, heq⟩
    · exact (hout (heq ▸ hin)).elim
    · rcases (WeakUniversal.stepBy_calls obj hs).2 call hin with hold | howner
      · exact (hout hold).elim
      · exact howner ▸ hq
    · exact (hout (heq ▸ hin)).elim
  obtain ⟨B, hB⟩ := FiniteScheduling.high_records_stepping g.actor
    (fun t => (g.run.state t).calls) WeakUniversal.Call.process WeakUniversal.Call.round
    (fun h _ hc => g.calls_mono h hc) inserted
    (fun t => WeakUniversal.calls_round_bound obj (g.run.state t).calls)
  refine ⟨B, fun k hk q ⟨s, hs⟩ => ?_⟩
  obtain ⟨t, ht⟩ := (g.input_iff_call (k + 1) q s).mp hs
  exact hB t ⟨k + 2, q, s⟩ ht (by simp only; omega)

/-- While only `p` is scheduled, no other process records a new call. -/
theorem calls_of_solo {N : Nat} {p : Fin n} (hsolo : g.SoloFrom N p)
    {t : Nat} (ht : N ≤ t) {call : WeakUniversal.Call (n := n) obj}
    (hcall : call ∈ (g.run.state t).calls) (hne : call.process ≠ p) :
    call ∈ (g.run.state N).calls := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction d with
  | zero => exact hcall
  | succ d ih =>
      refine ih (by omega) ?_
      rcases g.step_or_frozen hsolo (show N ≤ N + d by omega) with hstep | heq
      · rcases (WeakUniversal.stepBy_calls obj hstep).2 call hcall with hm | hproc
        · exact hm
        · exact absurd hproc hne
      · rw [show N + (d + 1) = (N + d) + 1 from rfl, heq] at hcall; exact hcall

/-- **Solo rounds belong to the solo process.**  Beyond a bound determined by the
calls already recorded, every call is made by the process running alone.  This
is the paper's "let `r*` be the largest round reached by any process by time
`τ`". -/
theorem solo_calls_own {N : Nat} {p : Fin n} (hsolo : g.SoloFrom N p) :
    ∃ B, ∀ (t : Nat) (call : WeakUniversal.Call (n := n) obj),
      call ∈ (g.run.state t).calls → B < call.round → call.process = p := by
  classical
  obtain ⟨B, hB⟩ := WeakUniversal.calls_round_bound obj (g.run.state N).calls
  refine ⟨B, fun t call hcall hlt => ?_⟩
  by_cases hne : call.process = p
  · exact hne
  · exfalso
    rcases Nat.le_total N t with hNt | htN
    · exact absurd (hB call (g.calls_of_solo hsolo hNt hcall hne)) (by omega)
    · exact absurd (hB call (g.calls_mono htN hcall)) (by omega)

/-- Beyond the solo bound, the solo process is the only participant of a
round. -/
theorem solo_sole_participant {p : Fin n} {B : Nat}
    (hB : ∀ (t : Nat) (call : WeakUniversal.Call (n := n) obj),
      call ∈ (g.run.state t).calls → B < call.round → call.process = p)
    {r : Nat} (hr : B < r + 1) :
    ∀ q u, (H (r + 1)).input q = some u → q = p := by
  intro q u hq
  obtain ⟨t, hcall⟩ := (g.input_iff_call r q u).mp hq
  exact hB t _ hcall hr

end WeakRun

namespace Weak
variable {f : Family (n := n) obj} (g : Weak obj f)

/-- **Fairness.**  A scheduled process whose GCA call has already produced its
output *on the projected protocol clock* takes the corresponding program step
rather than continuing to advance a finished call.  Without this the transition
system permits a process to idle inside a completed subroutine forever.

The clock guard `phase (gcaClock … t r) p = 6` is not decorative.  `StrongFair`
below is the same condition without it — "this call returns somewhere in the
protocol's own timeline" rather than "it has returned by now" — and
`strongFair_no_event` proves that version cannot be satisfied by any run in
which a GCA call returns at all: it would force the `receive` step at the very
first instant the caller is scheduled while waiting, whereas `receive_ready`
demands six protocol events that, at that instant, the caller has not taken. -/
def Fair : Prop := ∀ t p cmd r proposal,
  g.actor t = some p →
  (g.run.state t).localState p = .waiting cmd r proposal →
  (f.protocol r).phase (gcaClock obj g.run.state g.actor t r) p = 6 →
  (∃ s flag, (f.environment obj r).output p = some (s, flag)) →
  WeakUniversal.StepBy obj (f.environment obj) p (g.run.state t) (g.run.state (t + 1))

/-- Fairness without the projected-clock guard.  Retained only to record that
it is unsatisfiable; see `strongFair_no_event`. -/
def StrongFair : Prop := ∀ t p cmd r proposal,
  g.actor t = some p →
  (g.run.state t).localState p = .waiting cmd r proposal →
  (∃ s flag, (f.environment obj r).output p = some (s, flag)) →
  WeakUniversal.StepBy obj (f.environment obj) p (g.run.state t) (g.run.state (t + 1))

theorem StrongFair.fair (h : g.StrongFair) : g.Fair :=
  fun t p cmd r proposal hact hl _ hout => h t p cmd r proposal hact hl hout

/-- A process parked in a GCA call and scheduled infinitely often contributes
infinitely many events to that round. -/
theorem blocked_infiniteSteps {p : Fin n}
    {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {proposal : (WeakUniversal.Tagged (n := n) obj).Trace} {N : Nat}
    (hblock : ∀ t, N ≤ t → (g.run.state t).localState p = .waiting cmd r proposal)
    (hsched : ∀ M, ∃ t, M ≤ t ∧ g.actor t = some p) :
    g.inter.InfiniteSteps obj r p := by
  intro M
  obtain ⟨t, ht, hact⟩ := hsched (max M N)
  exact ⟨t, Nat.le_trans (Nat.le_max_left _ _) ht,
    g.routing t p cmd r proposal hact (hblock t (Nat.le_trans (Nat.le_max_right _ _) ht))⟩

/-- `blocked_output` phrased directly in terms of the global schedule, with no
detour through the operation-level execution. -/
theorem blocked_output' (hw : f.SnapshotWaitFree obj) {p : Fin n}
    {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {proposal : (WeakUniversal.Tagged (n := n) obj).Trace} {N : Nat}
    (hblock : ∀ t, N ≤ t → (g.run.state t).localState p = .waiting cmd r proposal)
    (hsched : ∀ M, ∃ t, M ≤ t ∧ g.actor t = some p) :
    ∃ s flag, (f.environment obj r).output p = some (s, flag) := by
  exact g.inter.round_returned obj hw (g.blocked_infiniteSteps hblock hsched)

/-- **Algorithm 2's calls return** — termination of Algorithm 2 above the
wait-free snapshot interface, read on the global schedule.  A process that is
inside a call for ever and still scheduled infinitely often contributes
infinitely many protocol events to that round, so under the snapshot assumption
its call finishes on the projected protocol clock; fairness then forces its
receive step, which leaves the call. -/
theorem callsReturn (hfair : g.Fair) (hw : f.SnapshotWaitFree obj) :
    g.toWeakRun.CallsReturn := by
  intro p cmd r proposal N hblock hsched
  have hinf : g.inter.InfiniteSteps obj r p := g.blocked_infiniteSteps hblock hsched
  obtain ⟨s, flag, hout⟩ := g.inter.round_returned obj hw hinf
  -- the projected clock eventually shows the call has finished
  obtain ⟨c, hc⟩ := (f.protocol r).terminates (hw r) (g.inter.protocol_infiniteSteps obj hinf)
  obtain ⟨t₂, ht₂⟩ := g.inter.clock_unbounded obj hinf c
  obtain ⟨t₁, ht₁, hact₁⟩ := hsched (max N t₂)
  have hN : N ≤ t₁ := Nat.le_trans (Nat.le_max_left _ _) ht₁
  have hphase : (f.protocol r).phase (gcaClock obj g.run.state g.actor t₁ r) p = 6 := by
    have hcl : c ≤ gcaClock obj g.run.state g.actor t₁ r :=
      Nat.le_trans ht₂ (g.inter.clock_mono obj (Nat.le_trans (Nat.le_max_right _ _) ht₁))
    exact Nat.le_antisymm ((f.protocol r).phase_le_six _ p)
      (hc ▸ (f.protocol r).phase_mono hcl p)
  have hstep := hfair t₁ p cmd r proposal hact₁ (hblock t₁ hN) hphase ⟨s, flag, hout⟩
  exact hstep.moves (by rw [hblock (t₁ + 1) (by omega), hblock t₁ hN])

end Weak

namespace WeakGCA
variable {H : WeakUniversal.Environment (n := n) obj} (g : WeakGCA obj H)

/-- **A scheduled process cannot stop taking program steps.**  If it did, it
would be parked inside a GCA call forever while still being scheduled, which the
GCA interface excludes: every correct participant returns. -/
theorem steps_infinitely {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (N : Nat) :
    ∃ t, N ≤ t ∧
      WeakUniversal.StepBy obj H p (g.run.state t) (g.run.state (t + 1)) := by
  classical
  refine Classical.byContradiction (fun hcon => ?_)
  have hno : ∀ t, N ≤ t →
      ¬ WeakUniversal.StepBy obj H p (g.run.state t) (g.run.state (t + 1)) :=
    fun t ht hs => hcon ⟨t, ht, hs⟩
  -- from `N` on, `p`'s local state never changes
  have hconst : ∀ t, N ≤ t → (g.run.state t).localState p = (g.run.state N).localState p := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    induction d with
    | zero => rfl
    | succ d ih =>
        have hprev : N ≤ N + d := by omega
        by_cases hact : g.actor (N + d) = some p
        · rcases g.step_or_stutter hact with hstep | ⟨_, heq⟩
          · exact absurd hstep (hno (N + d) hprev)
          · rw [show N + (d + 1) = (N + d) + 1 from rfl, heq]
            exact ih hprev
        · rw [show N + (d + 1) = (N + d) + 1 from rfl, g.localState_stable hact]
          exact ih hprev
  -- so it is parked in a GCA call for ever, while still scheduled
  obtain ⟨t₀, ht₀, hact₀⟩ := hsched N
  rcases g.step_or_stutter hact₀ with hstep | ⟨⟨r, hrd⟩, _⟩
  · exact absurd hstep (hno t₀ ht₀)
  · rw [hconst t₀ ht₀] at hrd
    obtain ⟨cmd, proposal, hL⟩ := weakRound_eq_some hrd
    exact g.gca.returns p cmd r proposal N (fun t ht => (hconst t ht).trans hL) hsched

/-- Progress measure: the round `p` is heading for is bounded by `B`, so each of
`p`'s steps strictly decreases this quantity. -/
private def mu (g : WeakGCA obj H) (p : Fin n) (B t : Nat) : Nat :=
  (B - WeakUniversal.nextRound obj ((g.run.state t).localState p)) * (4 + n + 1)
    + WeakUniversal.rank obj ((g.run.state t).localState p)

/-- **Unbounded rounds, from a given time.**  A process scheduled infinitely
often either reaches the point of returning at or after `T`, or heads for
arbitrarily large GCA rounds at or after `T`. -/
theorem returning_or_rounds_unbounded_from {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (T : Nat) :
    (∃ t, T ≤ t ∧ ∃ cmd r s, (g.run.state t).localState p = .returning cmd r s) ∨
    (∀ B, ∃ t, T ≤ t ∧ B < WeakUniversal.nextRound obj ((g.run.state t).localState p)) := by
  classical
  by_cases hret : ∃ t, T ≤ t ∧ ∃ cmd r s, (g.run.state t).localState p = .returning cmd r s
  · exact Or.inl hret
  refine Or.inr (fun B => Classical.byContradiction (fun hcon => ?_))
  have hbound : ∀ t, T ≤ t → WeakUniversal.nextRound obj ((g.run.state t).localState p) ≤ B :=
    fun t ht => Nat.le_of_not_lt (fun h => hcon ⟨t, ht, h⟩)
  have hnoret : ∀ t, T ≤ t → ∀ cmd r s,
      (g.run.state t).localState p ≠ .returning cmd r s :=
    fun t ht cmd r s h => hret ⟨t, ht, cmd, r, s, h⟩
  have hrankle : ∀ t, WeakUniversal.rank obj ((g.run.state t).localState p) ≤ 4 + n :=
    fun t => WeakUniversal.rank_le obj (WeakUniversal.todo_bound obj (g.run.reachable obj t)) p
  have hdec : ∀ t, T ≤ t → WeakUniversal.StepBy obj (H) p
      (g.run.state t) (g.run.state (t + 1)) → mu g p B (t + 1) < mu g p B t := by
    intro t ht hs
    rcases WeakUniversal.stepBy_progress obj hs with ⟨cmd, r, s, hr⟩ | hlt | ⟨heq, hrk⟩
    · exact absurd hr (hnoret t ht cmd r s)
    · have h1 : (B - WeakUniversal.nextRound obj ((g.run.state (t + 1)).localState p)) + 1
            ≤ B - WeakUniversal.nextRound obj ((g.run.state t).localState p) := by
        have := hbound (t + 1) (by omega); have := hbound t ht; omega
      have h2 := Nat.mul_le_mul_right (4 + n + 1) h1
      rw [Nat.succ_mul] at h2
      have h3 := hrankle (t + 1)
      simp only [mu]
      omega
    · simp only [mu, heq]
      omega
  have hmono : ∀ t, T ≤ t → mu g p B (t + 1) ≤ mu g p B t := by
    intro t ht
    by_cases hs : WeakUniversal.StepBy obj (H) p
        (g.run.state t) (g.run.state (t + 1))
    · exact Nat.le_of_lt (hdec t ht hs)
    · simp only [mu, g.localState_stable_of_no_step hs]
      exact Nat.le_refl _
  refine no_infinite_decrease (μ := fun t => mu g p B (T + t)) (fun t => ?_) (fun N => ?_)
  · exact hmono (T + t) (by omega)
  · obtain ⟨t, ht, hs⟩ := g.steps_infinitely hsched (T + N)
    refine ⟨t - T, by omega, ?_⟩
    rw [show T + (t - T) = t by omega, show T + (t - T + 1) = t + 1 by omega]
    exact hdec t (by omega) hs

/-- **Unbounded rounds.** -/
theorem returning_or_rounds_unbounded {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    (∃ t cmd r s, (g.run.state t).localState p = .returning cmd r s) ∨
    (∀ B, ∃ t, B < WeakUniversal.nextRound obj ((g.run.state t).localState p)) := by
  rcases g.returning_or_rounds_unbounded_from hsched 0 with ⟨t, -, h⟩ | h
  · exact Or.inl ⟨t, h⟩
  · exact Or.inr (fun B => by obtain ⟨t, -, ht⟩ := h B; exact ⟨t, ht⟩)

/-- **A process that reaches `returning` completes its operation.** -/
theorem returning_completes {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    {t : Nat} {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {s : (WeakUniversal.Tagged (n := n) obj).Trace}
    (h : (g.run.state t).localState p = .returning cmd r s) :
    ∃ u, t < u ∧
      (⟨cmd, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈ (g.run.state u).returns := by
  classical
  obtain ⟨u, ⟨hu, hstep⟩, hmin⟩ :=
    exists_least _ (g.steps_infinitely hsched t)
  have hconst : (g.run.state u).localState p = (g.run.state t).localState p :=
    g.localState_const hu (fun v hv hvu hsv => absurd (hmin v ⟨hv, hsv⟩) (by omega))
  exact ⟨u + 1, by omega, WeakUniversal.stepBy_returning obj hstep (hconst.trans h)⟩

/-- **A process on its way to a proposal reaches one.**  From a `collecting` or
`ready` state, a process that keeps taking steps arrives at `waiting`, at a
round no smaller than the one it was heading for. -/
theorem reaches_waiting {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    ∀ k t, WeakUniversal.rank obj ((g.run.state t).localState p) ≤ k →
      3 ≤ WeakUniversal.rank obj ((g.run.state t).localState p) →
      ∃ u, t ≤ u ∧ ∃ cmd r proposal,
        (g.run.state u).localState p = .waiting cmd r proposal ∧
          WeakUniversal.nextRound obj ((g.run.state t).localState p) ≤ r := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro t hle hge
    obtain ⟨u, ⟨hu, hstep⟩, hmin⟩ := exists_least _ (g.steps_infinitely hsched t)
    have hconst : (g.run.state u).localState p = (g.run.state t).localState p :=
      g.localState_const hu (fun v hv hvu hsv => absurd (hmin v ⟨hv, hsv⟩) (by omega))
    have hge' : 3 ≤ WeakUniversal.rank obj ((g.run.state u).localState p) := by
      rw [hconst]; exact hge
    obtain ⟨hnr, hrk, hge2⟩ := WeakUniversal.stepBy_from_high_rank obj hstep hge'
    rw [hconst] at hnr hrk
    by_cases hnew : 3 ≤ WeakUniversal.rank obj ((g.run.state (u + 1)).localState p)
    · obtain ⟨w, hwu, cmd, r, proposal, hL, hr⟩ :=
        ih _ (by omega) (u + 1) (Nat.le_refl _) hnew
      exact ⟨w, by omega, cmd, r, proposal, hL, by omega⟩
    · obtain ⟨cmd, r, proposal, hL⟩ :=
        WeakUniversal.rank_eq_two obj (show
          WeakUniversal.rank obj ((g.run.state (u + 1)).localState p) = 2 by omega)
      refine ⟨u + 1, by omega, cmd, r, proposal, hL, ?_⟩
      rw [hL] at hnr
      simpa [WeakUniversal.nextRound] using hnr

/-- **The solo round commits.**  With a single participant, the GCA object
returns that participant's own proposal, flagged committed: by Commitment it
commits an extension of its proposal, and by Validity that extension is the
proposal (`GCA.History.solo_commit`). -/
theorem solo_round_commits {p : Fin n} {B : Nat}
    (hB : ∀ (t : Nat) (call : WeakUniversal.Call (n := n) obj),
      call ∈ (g.run.state t).calls → B < call.round → call.process = p)
    {r : Nat} (hr : B < r + 1)
    {s : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hin : (H (r + 1)).input p = some s)
    {out : (WeakUniversal.Tagged (n := n) obj).Trace} {flag : Bool}
    (hout : (H (r + 1)).output p = some (out, flag)) :
    out = s ∧ flag = true :=
  GCA.History.solo_commit (H (r + 1)) (g.gca.spec r) hin
    (g.solo_sole_participant hB hr) hout

/-- The first step `p` takes at or after `t`, with its state unchanged until
then. -/
theorem next_step {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (t : Nat) :
    ∃ u, t ≤ u ∧ (g.run.state u).localState p = (g.run.state t).localState p ∧
      WeakUniversal.StepBy obj (H) p (g.run.state u) (g.run.state (u + 1)) := by
  obtain ⟨u, ⟨hu, hstep⟩, hmin⟩ := exists_least _ (g.steps_infinitely hsched t)
  exact ⟨u, hu,
    g.localState_const hu (fun v hv hvu hsv => absurd (hmin v ⟨hv, hsv⟩) (by omega)), hstep⟩

/-- From a solo round, the process commits and proceeds to return. -/
theorem waiting_high_round_returns {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) {B : Nat}
    (hB : ∀ (t : Nat) (call : WeakUniversal.Call (n := n) obj),
      call ∈ (g.run.state t).calls → B < call.round → call.process = p)
    {u : Nat} {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {prop : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hL : (g.run.state u).localState p = .waiting cmd r prop) (hrB : B < r) :
    ∃ w, u ≤ w ∧ ∃ cmd' r' s', (g.run.state w).localState p = .returning cmd' r' s' := by
  obtain ⟨hcall, hcount⟩ :=
    WeakUniversal.waiting_call obj (g.run.reachable obj u) p cmd r prop hL
  have hin : (H r).input p = some prop := by
    simpa using WeakUniversal.call_input obj (g.run.reachable obj u) _ hcall
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched u
  obtain ⟨s, flag, hout, hnew⟩ :=
    WeakUniversal.stepBy_from_waiting obj hstep (hconst.trans hL)
  obtain ⟨hs, hflag⟩ := g.solo_round_commits hB hrB hin hout
  subst hs; subst hflag
  have hnew' : (g.run.state (v + 1)).localState p = .publishing cmd (r' + 1) s := by
    rw [hnew]
    split
    · rfl
    · rename_i hneg
      exact absurd ⟨rfl, hcount⟩ hneg
  obtain ⟨w, hw2, hconst2, hstep2⟩ := g.next_step hsched (v + 1)
  exact ⟨w + 1, by omega, _, _, _,
    WeakUniversal.stepBy_from_publishing obj hstep2 (hconst2.trans hnew')⟩

/-- **Obstruction-freedom, core, from a given time.**  A process running solo
reaches the point of returning at or after any chosen time. -/
theorem solo_reaches_returning_from {p : Fin n} {N : Nat} (hsolo : g.SoloFrom N p) (T : Nat) :
    ∃ u, T ≤ u ∧ ∃ cmd r s, (g.run.state u).localState p = .returning cmd r s := by
  classical
  have hsched : ∀ M, ∃ t, M ≤ t ∧ g.actor t = some p :=
    hsolo.sched
  obtain ⟨B, hB⟩ := g.solo_calls_own hsolo
  rcases g.returning_or_rounds_unbounded_from hsched T with hret | hunb
  · exact hret
  obtain ⟨t, htT, htB⟩ := hunb B
  cases hL : (g.run.state t).localState p with
  | idle => rw [hL] at htB; simp [WeakUniversal.nextRound] at htB
  | returning cmd r s => exact ⟨t, htT, cmd, r, s, hL⟩
  | publishing cmd r s =>
      obtain ⟨u, hu, hconst, hstep⟩ := g.next_step hsched t
      exact ⟨u + 1, by omega, cmd, r, s,
        WeakUniversal.stepBy_from_publishing obj hstep (hconst.trans hL)⟩
  | waiting cmd r prop =>
      obtain ⟨w, hwu, rest⟩ := g.waiting_high_round_returns hsched hB hL
        (by rw [hL] at htB; exact htB)
      exact ⟨w, by omega, rest⟩
  | collecting _ _ _ | ready _ _ =>
      obtain ⟨u, hu, cmd', r', prop', hL', hr'⟩ :=
        g.reaches_waiting hsched _ t (Nat.le_refl _)
          (by rw [hL]; simp only [WeakUniversal.rank]; omega)
      obtain ⟨w, hwu, rest⟩ := g.waiting_high_round_returns hsched hB hL' (by omega)
      exact ⟨w, by omega, rest⟩

/-- **Obstruction-freedom, core.**  The `returning` state is found *after* the
solo phase begins, so it belongs to the operation `p` is currently running and
not to an earlier one. -/
theorem solo_reaches_returning {p : Fin n} {N : Nat} (hsolo : g.SoloFrom N p) :
    ∃ u, N ≤ u ∧ ∃ cmd r s, (g.run.state u).localState p = .returning cmd r s :=
  g.solo_reaches_returning_from hsolo N

/-- **Obstruction-freedom for Algorithm 1.**  A process running solo from `N`
on completes *its own* operation: at some time `u ≥ N` it is in the `returning`
state of a command `cmd` it owns, and the response of that very command is
recorded at a strictly later time.

The conclusion deliberately names `p`, `N` and `cmd`.  An existential over an
unrelated response somewhere in the run would be implied by any single response
anywhere and would say nothing about the solo process. -/
theorem solo_completes {p : Fin n} {N : Nat} (hsolo : g.SoloFrom N p) :
    ∃ u v cmd r s, N ≤ u ∧ u < v ∧ cmd.process = p ∧
      (g.run.state u).localState p = .returning cmd r s ∧
      (⟨cmd, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈ (g.run.state v).returns := by
  have hsched : ∀ M, ∃ t, M ≤ t ∧ g.actor t = some p :=
    hsolo.sched
  obtain ⟨u, hu, cmd, r, s, hL⟩ := g.solo_reaches_returning hsolo
  obtain ⟨v, huv, hmem⟩ := g.returning_completes hsched hL
  refine ⟨u, v, cmd, r, s, hu, huv, ?_, hL, hmem⟩
  refine ((WeakUniversal.identity_invariant obj (g.run.reachable obj u)).active_tag p cmd ?_).1
  show WeakUniversal.Local.command obj ((g.run.state u).localState p) = some cmd
  rw [hL]; rfl

end WeakGCA
end GlobalSchedule
end ConflictFreedom
