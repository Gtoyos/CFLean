import CFLeanProof.UniversalProgress
import CFLeanProof.UniversalIdentities

/-!
# Local progress of Algorithm 3 (the helping construction)

This is the Algorithm 3 counterpart of the first half of `UniversalProgress`.
The argument for Lemma `UCV2isCF`'s step-contention-free half is Theorem
`weakUCWCF`'s, as in the manuscript; only the measure changes, since
Algorithm 3's loop is longer.

Algorithm 3's loop body is longer than Algorithm 1's: announce, collect `S`,
collect `M`, propose, receive, publish, re-collect `S`, and then either return
or retry.  `nextRound` is the GCA round a local state heads for and `rank` is a
progress rank inside that round; `stepBy_progress` shows that every step either
advances `nextRound` or strictly decreases `rank`, except at the state the
`finish` step fires from.

Two Algorithm-3-specific invariants are also proved here, both needed by the
solo argument:

* `covered` -- a process's own command is in its proposal.  The `M` collect
  reads the announcement array, and the process announced its own command before
  collecting, so by the time the collect is finished either the command was
  already in the adopted trace or it has been appended.
* `slot_call` -- a nonzero round stored in `S` was reached by a recorded GCA
  call of the very process that stored it.  This is what makes "the largest
  round reached by any process by time `τ`" bound the *slots*, not just the
  calls, which the final `S` re-collect of Algorithm 3 needs.

As in `UniversalProgress`, the schedule-level lemmas are split between
`GlobalSchedule.HelpingRun` (any run), `GlobalSchedule.HelpingGCA` (runs over GCA
objects meeting the interface) and `GlobalSchedule.Helping` (the composition
with Algorithm 2: `Fair` and `callsReturn`).
-/

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best Supported
  Committed Stored CallInvariant eq_of_update_ne best_round_left)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- The GCA round a local state is heading for.  A process that has adopted a
seed of round `k` will propose to round `k + 1`; a process that is inside, or
has just come back from, round `r` is still at `r` until it retries. -/
def nextRound : Local (n := n) obj → Nat
  | .idle s => s.round + 1
  | .announcing _ s => s.round + 1
  | .collecting _ _ s => s.round + 1
  | .gathering _ s _ _ => s.round + 1
  | .waiting _ r _ => r
  | .publishing _ s => s.round
  | .checking _ s _ _ => s.round

/-- Progress rank inside one round.  The three collects contribute their
outstanding lists, which `todo_bound` bounds by `n`. -/
def rank : Local (n := n) obj → Nat
  | .idle _ => 3 * n + 6
  | .announcing _ _ => 3 * n + 5
  | .collecting _ todo _ => 2 * n + 4 + todo.length
  | .gathering _ _ todo _ => n + 3 + todo.length
  | .waiting _ _ _ => n + 2
  | .publishing _ _ => n + 1
  | .checking _ _ todo _ => todo.length

/-- The state Algorithm 3 returns from: the final `S` collect is finished and
the adopted trace contains the process's own command. -/
def AtReturn (l : Local (n := n) obj) : Prop :=
  ∃ cmd seed seen, l = .checking cmd seed [] seen ∧
    0 < (Tagged obj).traceCount cmd seen.trace

/-- **The local progress measure.**  Every step of `p` either fires from the
returning state, advances the round `p` heads for, or strictly decreases the
rank inside the current round. -/
theorem stepBy_progress {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) :
    AtReturn obj (c.localState p) ∨
    nextRound obj (c.localState p) < nextRound obj (d.localState p) ∨
    (nextRound obj (c.localState p) = nextRound obj (d.localState p) ∧
      rank obj (d.localState p) < rank obj (c.localState p)) := by
  cases h.1 with
  | readStart q q' cmd todo seed hq =>
      obtain rfl := eq_of_update_ne h.moves
      have hb := best_round_left obj seed (c.slots q')
      rcases Nat.lt_or_ge seed.round (best obj seed (c.slots q')).round with hlt | hge
      · exact Or.inr (Or.inl (by simp [update, hq, nextRound]; omega))
      · refine Or.inr (Or.inr ⟨by simp [update, hq, nextRound]; omega, ?_⟩)
        simp [update, hq, rank]
  | announce _ _ _ hq order horder =>
      obtain rfl := eq_of_update_ne h.moves
      refine Or.inr (Or.inr ⟨by simp [update, hq, nextRound], ?_⟩)
      simp [update, hq, rank, horder.length_eq]
      omega
  | collectedStart _ _ _ hq order horder =>
      obtain rfl := eq_of_update_ne h.moves
      refine Or.inr (Or.inr ⟨by simp [update, hq, nextRound], ?_⟩)
      simp [update, hq, rank, horder.length_eq]
      omega
  | receive q cmd r prop s flag hq ho order horder =>
      obtain rfl := eq_of_update_ne h.moves
      by_cases hf : flag = true
      · exact Or.inr (Or.inr ⟨by simp [update, hq, nextRound, hf],
          by simp [update, hq, rank, hf]⟩)
      · refine Or.inr (Or.inr ⟨by simp [update, hq, nextRound, hf], ?_⟩)
        simp [update, hq, rank, hf, horder.length_eq]
  | publish q cmd seed hq order horder =>
      obtain rfl := eq_of_update_ne h.moves
      refine Or.inr (Or.inr ⟨by simp [update, hq, nextRound], ?_⟩)
      simp [update, hq, rank, horder.length_eq]
  | invoke _ _ _ hq | readAnnouncement _ _ _ _ _ _ hq | propose _ _ _ _ hq _
  | readCheck _ _ _ _ _ _ hq =>
      obtain rfl := eq_of_update_ne h.moves
      exact Or.inr (Or.inr ⟨by simp [update, hq, nextRound], by simp [update, hq, rank]⟩)
  | retry q cmd seed seen hq hmiss =>
      obtain rfl := eq_of_update_ne h.moves
      exact Or.inr (Or.inl (by simp [update, hq, nextRound]))
  | finish q cmd seed seen hq hcont =>
      obtain rfl := eq_of_update_ne h.moves
      exact Or.inl ⟨cmd, seed, seen, hq, hcont⟩

/-- Every outstanding collect list is bounded by the number of processes. -/
def TodoBounded : Local (n := n) obj → Prop
  | .collecting _ todo _ => todo.length ≤ n
  | .gathering _ _ todo _ => todo.length ≤ n
  | .checking _ _ todo _ => todo.length ≤ n
  | _ => True

omit [DecidableEq Op] in
private theorem todo_update {c : Configuration (n := n) obj}
    (hc : ∀ p, TodoBounded obj (c.localState p)) (p : Fin n) (l : Local (n := n) obj)
    (hl : TodoBounded obj l) : ∀ q, TodoBounded obj (update c.localState p l q) := by
  intro q
  unfold WeakUniversal.update
  split
  · exact hl
  · exact hc q

theorem todo_bound {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : ∀ p, TodoBounded obj (c.localState p) := by
  induction hc with
  | initial => intro p; simp [initial, TodoBounded]
  | step _ hs ih =>
      cases hs with
      | receive q cmd r prop s flag hq ho order horder =>
          refine todo_update obj ih q _ ?_
          split
          · trivial
          · simp [TodoBounded, horder.length_eq]
      | readStart q _ _ _ _ hq | readAnnouncement q _ _ _ _ _ hq | readCheck q _ _ _ _ _ hq =>
          have h := ih q
          rw [hq] at h
          refine todo_update obj ih q _ ?_
          simp only [TodoBounded] at h ⊢
          simp only [List.length_cons] at h
          omega
      | announce q _ _ _ order horder | publish q _ _ _ order horder =>
          exact todo_update obj ih q _ (by simp [TodoBounded, horder.length_eq])
      | collectedStart q _ _ _ order horder | retry q _ _ _ _ _ order horder =>
          exact todo_update obj ih q _ (by simp [TodoBounded, horder.length_eq])
      | invoke q _ _ _ | propose q _ _ _ _ _ _ _ | finish q _ _ _ _ _ =>
          exact todo_update obj ih q _ trivial

omit [DecidableEq Op] in
theorem rank_le {c : Configuration (n := n) obj}
    (hb : ∀ p, TodoBounded obj (c.localState p)) (p : Fin n) :
    rank obj (c.localState p) ≤ 3 * n + 6 := by
  have h := hb p
  cases hl : c.localState p with
  | collecting cmd todo seed =>
      rw [hl] at h; simp only [TodoBounded] at h; simp only [rank]; omega
  | gathering cmd seed todo cmds =>
      rw [hl] at h; simp only [TodoBounded] at h; simp only [rank]; omega
  | checking cmd seed todo seen =>
      rw [hl] at h; simp only [TodoBounded] at h; simp only [rank]; omega
  | _ => simp only [rank]; omega

end ConflictFreedom.HelpingUniversal

/-! ## Transition lemmas -/

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best Supported
  Committed Stored CallInvariant eq_of_update_ne apply_eq_of_update_ne)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- Leaving `waiting` is the `receive` step. -/
theorem stepBy_from_waiting {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {r : Nat} {prop : (Tagged (n := n) obj).Trace}
    (hc : c.localState p = .waiting cmd r prop) :
    ∃ s flag, (H r).output p = some (s, flag) ∧ ∃ order : List (Fin n),
      order.Perm (List.finRange n) ∧
      d.localState p = (if flag = true then .publishing cmd ⟨r, s⟩
        else .checking cmd ⟨r, s⟩ order (zeroSeed obj)) := by
  cases h.1 with
  | receive q cmd' r' prop' s flag hq ho order horder =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, rfl⟩ := Local.waiting.inj (hq.symm.trans hc)
      exact ⟨s, flag, ho, order, horder, by simp [update]⟩
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- Leaving `publishing` is the `publish` step: the seed is written to `S` and
the final collect starts, in some order. -/
theorem stepBy_from_publishing {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {seed : Seed (n := n) obj}
    (hc : c.localState p = .publishing cmd seed) :
    ∃ order : List (Fin n), order.Perm (List.finRange n) ∧
      d.localState p = .checking cmd seed order (zeroSeed obj) ∧
      d.slots = update c.slots p seed := by
  cases h.1 with
  | publish q cmd' seed' hq order horder =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl⟩ := Local.publishing.inj (hq.symm.trans hc)
      exact ⟨order, horder, by simp [update], rfl⟩
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- A step out of an unfinished final collect reads the next register. -/
theorem stepBy_from_checking {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {seed : Seed (n := n) obj} {q0 : Fin n} {todo : List (Fin n)}
    {seen : Seed (n := n) obj}
    (hc : c.localState p = .checking cmd seed (q0 :: todo) seen) :
    d.localState p = .checking cmd seed todo (best obj seen (c.slots q0)) ∧
      d.slots = c.slots := by
  cases h.1 with
  | readCheck q q' cmd' seed' todo' seen' hq =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩ := Local.checking.inj (hq.symm.trans hc)
      exact ⟨by simp [update], rfl⟩
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- From the returning state the only available step is `finish`, which records
the response. -/
theorem stepBy_at_return {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {seed seen : Seed (n := n) obj}
    (hc : c.localState p = .checking cmd seed [] seen)
    (hcount : 0 < (Tagged obj).traceCount cmd seen.trace) :
    (⟨cmd, seen.round, seen.trace⟩ : Return (n := n) obj) ∈ d.returns := by
  cases h.1 with
  | finish q cmd' seed' seen' hq hcont =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, -, rfl⟩ := Local.checking.inj (hq.symm.trans hc)
      exact List.mem_cons_self ..
  | retry q cmd' seed' seen' hq hmiss =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, -, -, rfl⟩ := Local.checking.inj (hq.symm.trans hc)
      omega
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- A step never removes a call, and any call it adds belongs to the acting
process.  A step also leaves every other process's `S` register alone. -/
theorem stepBy_calls {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) :
    (∀ call ∈ c.calls, call ∈ d.calls) ∧
      (∀ call ∈ d.calls, call ∈ c.calls ∨ call.process = p) ∧
      (∀ q, q ≠ p → d.slots q = c.slots q) := by
  cases h.1 with
  | propose q cmd seed commands hq hi =>
      obtain rfl := eq_of_update_ne h.moves
      refine ⟨fun call hcall => List.mem_cons_of_mem _ hcall, fun call hcall => ?_,
        fun q hq' => rfl⟩
      rcases List.mem_cons.mp hcall with rfl | hm
      · exact Or.inr rfl
      · exact Or.inl hm
  | publish q cmd seed hq =>
      obtain rfl := eq_of_update_ne h.moves
      exact ⟨fun _ h => h, fun _ h => Or.inl h, fun q' hq' => by simp [update, hq']⟩
  | _ => exact ⟨fun _ h => h, fun _ h => Or.inl h, fun _ _ => rfl⟩

end ConflictFreedom.HelpingUniversal

/-! ## Algorithm 3's own-command and slot-provenance invariants -/

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best
  Supported Committed Stored CallInvariant)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

theorem proposal_count (a : Cmd n Op) (seed : Seed (n := n) obj)
    (commands : List (Cmd n Op)) :
    (Tagged obj).traceCount a (proposal obj seed commands)
      = (Tagged obj).traceCount a seed.trace + commands.count a := by
  unfold proposal
  exact (Tagged obj).traceCount_append a seed.trace _

/-- Every arrangement of `trace(M_i)` gives the proposal the same operations,
with the same multiplicities. -/
theorem proposal_count_perm (a : Cmd n Op) (seed : Seed (n := n) obj)
    {arranged commands : List (Cmd n Op)} (h : arranged.Perm commands) :
    (Tagged obj).traceCount a (proposal obj seed arranged)
      = (Tagged obj).traceCount a (proposal obj seed commands) := by
  rw [proposal_count, proposal_count, h.count_eq]

theorem observe_count_le (a : Cmd n Op) (seed : Seed (n := n) obj)
    (x : Option (Cmd n Op)) (commands : List (Cmd n Op)) :
    commands.count a ≤ (observe obj seed x commands).count a := by
  cases x with
  | none => exact Nat.le_refl _
  | some cmd =>
      by_cases hz : (Tagged obj).traceCount cmd seed.trace = 0
      · simp only [observe, hz, ↓reduceIte, List.count_append]
        omega
      · simp [observe, hz]

/-- The announcement a process has published matches the command it is
executing, from the moment it announces until it returns. -/
def AnnouncedFor : Local (n := n) obj → Option (Cmd n Op) → Prop
  | .idle _, _ => True
  | .announcing _ _, _ => True
  | .collecting cmd _ _, a => a = some cmd
  | .gathering cmd _ _ _, a => a = some cmd
  | .waiting cmd _ _, a => a = some cmd
  | .publishing cmd _, a => a = some cmd
  | .checking cmd _ _ _, a => a = some cmd

theorem announced {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) :
    ∀ p, AnnouncedFor obj (c.localState p) (c.announcements p) := by
  induction hc with
  | initial => intro p; simp [initial, AnnouncedFor]
  | step _ hs ih =>
      cases hs with
      | receive q cmd r prop s flag hq ho =>
          intro p
          by_cases hqp : q = p
          · subst hqp
            have h := ih q; rw [hq] at h
            simp only [AnnouncedFor] at h
            show AnnouncedFor obj (update _ q _ q) _
            rw [WeakUniversal.update_self]
            by_cases hf : flag = true <;> simpa [hf, AnnouncedFor] using h
          · simpa [update, Ne.symm hqp] using ih p
      | readStart q _ _ _ _ hq | collectedStart q _ _ hq | readAnnouncement q _ _ _ _ _ hq
      | propose q _ _ _ hq _ | publish q _ _ hq | readCheck q _ _ _ _ _ hq | retry q _ _ _ hq _ =>
          intro p
          by_cases hqp : q = p
          · subst hqp
            have h := ih q; rw [hq] at h
            simpa [update, AnnouncedFor] using h
          · simpa [update, Ne.symm hqp] using ih p
      | invoke q _ _ _ | announce q _ _ _ | finish q _ _ _ _ _ =>
          intro p
          by_cases hqp : q = p
          · subst hqp; simp [update, AnnouncedFor]
          · simpa [update, Ne.symm hqp] using ih p

/-- **The helping collect covers the collector's own command.**  Either the
process still has itself on its announcement-collect list, or its own command
already occurs in the trace it is going to propose. -/
def Covered (p : Fin n) : Local (n := n) obj → Prop
  | .gathering own seed todo commands =>
      p ∈ todo ∨ 0 < (Tagged obj).traceCount own (proposal obj seed commands)
  | .waiting own _ prop => 0 < (Tagged obj).traceCount own prop
  | _ => True

theorem covered {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : ∀ p, Covered obj p (c.localState p) := by
  induction hc with
  | initial => intro p; simp [initial, Covered]
  | step hr hs ih =>
      cases hs with
      | readAnnouncement q q' cmd seed todo commands hq =>
          intro p
          by_cases hqp : q = p
          · subst hqp
            have h := ih q; rw [hq] at h
            simp only [Covered] at h
            show Covered obj q (update _ q _ q)
            rw [WeakUniversal.update_self]
            simp only [Covered]
            rcases h with hmem | hcov
            · rcases List.mem_cons.mp hmem with rfl | hmem'
              · right
                have hann := announced obj hr q
                rw [hq] at hann
                simp only [AnnouncedFor] at hann
                rw [hann]
                rw [proposal_count]
                by_cases hz : (Tagged obj).traceCount cmd seed.trace = 0
                · simp only [observe, hz, ↓reduceIte, List.count_append]
                  simp
                · omega
              · exact Or.inl hmem'
            · right
              rw [proposal_count] at hcov ⊢
              exact Nat.lt_of_lt_of_le hcov
                (Nat.add_le_add_left (observe_count_le obj cmd seed _ commands) _)
          · simpa [update, Ne.symm hqp] using ih p
      | propose q cmd seed commands hq arranged harr hi =>
          intro p
          by_cases hqp : q = p
          · subst hqp
            have h := ih q; rw [hq] at h
            simp only [Covered] at h
            show Covered obj q (update _ q _ q)
            rw [WeakUniversal.update_self]
            simp only [Covered]
            rcases h with hmem | hcov
            · exact absurd hmem (by simp)
            · rw [proposal_count_perm obj cmd seed harr]; exact hcov
          · simpa [update, Ne.symm hqp] using ih p
      | receive q cmd r prop s flag hq ho =>
          intro p
          by_cases hqp : q = p
          · subst hqp
            show Covered obj q (update _ q _ q)
            rw [WeakUniversal.update_self]
            by_cases hf : flag = true <;> simp [hf, Covered]
          · simpa [update, Ne.symm hqp] using ih p
      | collectedStart q _ _ _ order horder | retry q _ _ _ _ _ order horder =>
          intro p
          by_cases hqp : q = p
          · subst hqp
            show Covered obj q (update _ q _ q)
            rw [WeakUniversal.update_self]
            exact Or.inl (horder.mem_iff.mpr (List.mem_finRange q))
          · simpa [update, Ne.symm hqp] using ih p
      | invoke q _ _ _ | announce q _ _ _ | readStart q _ _ _ _ _ | publish q _ _ _
      | readCheck q _ _ _ _ _ _ | finish q _ _ _ _ _ =>
          intro p
          by_cases hqp : q = p
          · subst hqp; simp [update, Covered]
          · simpa [update, Ne.symm hqp] using ih p

/-- A process waiting in a round has recorded the corresponding call, and its
proposal contains its own command. -/
theorem waiting_call {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) :
    ∀ p cmd r prop, c.localState p = .waiting cmd r prop →
      (⟨r, p, prop⟩ : Call (n := n) obj) ∈ c.calls ∧
        0 < (Tagged (n := n) obj).traceCount cmd prop := by
  intro p cmd r prop h
  refine ⟨?_, by have := covered obj hc p; rw [h] at this; exact this⟩
  induction hc with
  | initial => simp [initial] at h
  | step hr hs ih =>
      cases hs with
      | propose q cmd' seed commands hq hi =>
          by_cases hqp : q = p
          · subst hqp
            simp [update] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih (by simpa [update, Ne.symm hqp] using h))
      | receive q cmd' r' prop' s flag hq ho =>
          by_cases hqp : q = p
          · subst hqp; simp [update] at h; split at h <;> simp at h
          · exact ih (by simpa [update, Ne.symm hqp] using h)
      | invoke q _ _ _ | announce q _ _ _ | readStart q _ _ _ _ _ | collectedStart q _ _ _
      | readAnnouncement q _ _ _ _ _ _ | publish q _ _ _ | readCheck q _ _ _ _ _ _
      | retry q _ _ _ _ _ | finish q _ _ _ _ _ =>
          by_cases hqp : q = p
          · subst hqp; simp [update] at h
          · exact ih (by simpa [update, Ne.symm hqp] using h)

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best
  Supported Committed Stored CallInvariant)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- A round `r` that process `q` is entitled to: either the initial round `0`,
or a round of a GCA call that `q` itself made. -/
def CallOf (c : Configuration (n := n) obj) (q : Fin n) (r : Nat) : Prop :=
  r = 0 ∨ ∃ call ∈ c.calls, call.process = q ∧ call.round = r

omit [DecidableEq Op] in
theorem callOf_mono {c d : Configuration (n := n) obj} {q : Fin n} {r : Nat}
    (hc : CallOf obj c q r) (hsub : ∀ call ∈ c.calls, call ∈ d.calls) :
    CallOf obj d q r := by
  rcases hc with h0 | ⟨call, hmem, h1, h2⟩
  · exact Or.inl h0
  · exact Or.inr ⟨call, hsub call hmem, h1, h2⟩

/-- The round a process is about to write to `S` is a round it called. -/
theorem publishing_call {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) :
    ∀ p cmd seed, c.localState p = .publishing cmd seed → CallOf obj c p seed.round := by
  intro p cmd seed h
  induction hc with
  | initial => simp [initial] at h
  | step hr hs ih =>
      cases hs with
      | propose q cmd' seed' commands hq hi =>
          by_cases hqp : q = p
          · subst hqp; simp [update] at h
          · exact callOf_mono obj (ih (by simpa [update, Ne.symm hqp] using h))
              (fun call hcall => List.mem_cons_of_mem _ hcall)
      | receive q cmd' r' prop' s flag hq ho =>
          by_cases hqp : q = p
          · subst hqp
            simp only [update, ↓reduceIte] at h
            split at h
            · injection h with e1 e2
              subst e1; subst e2
              exact Or.inr ⟨⟨r', q, prop'⟩,
                (waiting_call obj hr q cmd' r' prop' hq).1, rfl, rfl⟩
            · exact absurd h (by simp)
          · exact ih (by simpa [update, Ne.symm hqp] using h)
      | invoke q _ _ _ | announce q _ _ _ | readStart q _ _ _ _ _ | collectedStart q _ _ _
      | readAnnouncement q _ _ _ _ _ _ | publish q _ _ _ | readCheck q _ _ _ _ _ _
      | retry q _ _ _ _ _ | finish q _ _ _ _ _ =>
          by_cases hqp : q = p
          · subst hqp; simp [update] at h
          · exact ih (by simpa [update, Ne.symm hqp] using h)

/-- **Slot provenance.**  A nonzero round stored in `S[q]` is the round of a
GCA call made by `q` itself.  Together with "every call above the solo bound
belongs to the solo process", this bounds the rounds of every *other*
process's register, which is what Algorithm 3's final `S` collect needs. -/
theorem slot_call {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : ∀ p, CallOf obj c p (c.slots p).round := by
  induction hc with
  | initial => intro p; exact Or.inl rfl
  | step hr hs ih =>
      cases hs with
      | propose q cmd seed commands hq hi =>
          intro p
          exact callOf_mono obj (ih p) (fun call hcall => List.mem_cons_of_mem _ hcall)
      | publish q cmd seed hq =>
          intro p
          by_cases hqp : q = p
          · subst hqp
            show CallOf obj _ q (update _ q seed q).round
            rw [WeakUniversal.update_self]
            exact publishing_call obj hr q cmd seed hq
          · have hne : ¬ (p = q) := fun e => hqp e.symm
            simp only [WeakUniversal.update, hne, ↓reduceIte]
            exact ih p
      | _ => exact ih

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best Supported
  Committed Stored CallInvariant eq_of_update_ne apply_eq_of_update_ne best_round_left)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

omit [DecidableEq Op] in
theorem best_eq_left {s t : Seed (n := n) obj} (h : t.round ≤ s.round) :
    best obj s t = s := by
  simp [WeakUniversal.best, Nat.not_lt.mpr h]

omit [DecidableEq Op] in
theorem best_lt {s t : Seed (n := n) obj} {B : Nat} (hs : s.round < B) (ht : t.round < B) :
    (best obj s t).round < B := by
  unfold WeakUniversal.best; split
  · exact ht
  · exact hs

omit [DecidableEq Op] in
/-- Only the states at rank `n + 2` can be `waiting`, given the collect bound. -/
theorem rank_eq_waiting {l : Local (n := n) obj} (hb : TodoBounded obj l)
    (h : rank obj l = n + 2) : ∃ cmd r prop, l = .waiting cmd r prop := by
  cases l with
  | waiting cmd r prop => exact ⟨cmd, r, prop, rfl⟩
  | checking _ _ todo _ =>
      simp only [TodoBounded] at hb; simp only [rank] at h; omega
  | _ => simp only [rank] at h; omega

/-- Above rank `n + 3` the process is still on its way to a proposal: the round
it heads for does not decrease, the rank strictly decreases, and it does not
drop below `waiting`. -/
theorem stepBy_from_high_rank {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    (hr : n + 3 ≤ rank obj (c.localState p)) :
    nextRound obj (c.localState p) ≤ nextRound obj (d.localState p) ∧
      rank obj (d.localState p) < rank obj (c.localState p) ∧
      n + 2 ≤ rank obj (d.localState p) := by
  cases h.1 with
  | invoke q op seed hq =>
      obtain rfl := eq_of_update_ne h.moves
      refine ⟨by simp [update, hq, nextRound], ?_, ?_⟩
      · simp [update, hq, rank]
      · simp [update, rank]; try omega
  | readStart q q' cmd todo seed hq =>
      obtain rfl := eq_of_update_ne h.moves
      have hb := best_round_left obj seed (c.slots q')
      refine ⟨by simp [update, hq, nextRound]; try omega, ?_, ?_⟩
      · simp [update, hq, rank]
      · simp [update, rank]; try omega
  | announce _ _ _ hq order horder =>
      obtain rfl := eq_of_update_ne h.moves
      refine ⟨by simp [update, hq, nextRound], ?_, ?_⟩
      · simp [update, hq, rank, horder.length_eq]; try omega
      · simp [update, rank]; try omega
  | collectedStart _ _ _ hq order horder =>
      obtain rfl := eq_of_update_ne h.moves
      refine ⟨by simp [update, hq, nextRound], ?_, ?_⟩
      · simp [update, hq, rank, horder.length_eq]; try omega
      · simp [update, rank]; try omega
  | readAnnouncement q q' cmd seed todo commands hq =>
      obtain rfl := eq_of_update_ne h.moves
      rw [hq] at hr
      simp only [rank] at hr
      refine ⟨by simp [update, hq, nextRound], ?_, ?_⟩
      · simp [update, hq, rank]
      · simp [update, rank]; try omega
  | propose q cmd seed commands hq arranged harr hi =>
      obtain rfl := eq_of_update_ne h.moves
      refine ⟨by simp [update, hq, nextRound], ?_, ?_⟩
      · simp [update, hq, rank]; try omega
      · simp [update, rank]
  | receive _ _ _ _ _ _ hq _ | publish _ _ _ hq =>
      obtain rfl := eq_of_update_ne h.moves
      rw [hq] at hr; simp only [rank] at hr; omega
  | readCheck q q' cmd seed todo seen hq =>
      obtain rfl := eq_of_update_ne h.moves
      rw [hq] at hr
      simp only [rank, List.length_cons] at hr
      refine ⟨by simp [update, hq, nextRound], ?_, ?_⟩
      · simp [update, hq, rank]
      · simp [update, rank]; try omega
  | retry _ _ _ _ hq _ | finish _ _ _ _ hq _ =>
      obtain rfl := eq_of_update_ne h.moves
      rw [hq] at hr; simp [rank] at hr

/-- Leaving a finished final collect whose trace lacks the command is the
`retry` step: a new collect of `M` starts, in some order. -/
theorem stepBy_retry {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {seed seen : Seed (n := n) obj}
    (hc : c.localState p = .checking cmd seed [] seen)
    (hzero : (Tagged obj).traceCount cmd seen.trace = 0) :
    ∃ order : List (Fin n), order.Perm (List.finRange n) ∧
      d.localState p = .gathering cmd seed order [] := by
  cases h.1 with
  | retry q cmd' seed' seen' hq hmiss order horder =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, -, rfl⟩ := Local.checking.inj (hq.symm.trans hc)
      exact ⟨order, horder, by simp [update]⟩
  | finish q cmd' seed' seen' hq hcont =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, -, rfl⟩ := Local.checking.inj (hq.symm.trans hc)
      omega
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

end ConflictFreedom.HelpingUniversal

/-! ## Algorithm 3 at the level of the global schedule -/

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}

omit [DecidableEq Op] in
theorem helpingRound_eq_some {l : HelpingUniversal.Local (n := n) obj} {r : Nat}
    (h : helpingRound obj l = some r) :
    ∃ cmd proposal, l = .waiting cmd r proposal := by
  cases l with
  | waiting cmd r' proposal =>
      exact ⟨cmd, proposal, by simpa [helpingRound] using (Option.some.inj h) ▸ rfl⟩
  | _ => exact absurd h (by simp [helpingRound])


namespace HelpingRun
variable (g : HelpingRun obj H)

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
the whole configuration is frozen. -/
theorem step_or_frozen {N : Nat} {p : Fin n} (hsolo : g.SoloFrom N p)
    {t : Nat} (ht : N ≤ t) :
    HelpingUniversal.StepBy obj (H) p
        (g.run.state t) (g.run.state (t + 1)) ∨
      g.run.state (t + 1) = g.run.state t := by
  rcases g.step_actor t with ⟨-, heq⟩ | ⟨q, hq, hstep⟩ | ⟨q, r, hq, -, heq⟩
  · exact Or.inr heq
  · exact Or.inl (hsolo.own t q ht hq ▸ hstep)
  · exact Or.inr heq

/-- When the scheduled process is `p`, either `p` takes a program step or `p` is
inside a GCA call and the program configuration stutters. -/
theorem step_or_stutter {t : Nat} {p : Fin n} (h : g.actor t = some p) :
    HelpingUniversal.StepBy obj (H) p (g.run.state t) (g.run.state (t + 1)) ∨
      ((∃ r, helpingRound obj ((g.run.state t).localState p) = some r) ∧
        g.run.state (t + 1) = g.run.state t) := by
  rcases g.step_actor t with ⟨hnone, _⟩ | ⟨q, hq, hstep⟩ | ⟨q, r, hq, hrd, heq⟩
  · exact absurd (hnone.symm.trans h) (by simp)
  · have : q = p := Option.some.inj (hq.symm.trans h)
    subst this
    exact Or.inl hstep
  · have : q = p := Option.some.inj (hq.symm.trans h)
    subst this
    exact Or.inr ⟨⟨r, hrd⟩, heq⟩

end HelpingRun

namespace Helping
variable {f : Family (n := n) obj} (g : Helping obj f)

/-- **Fairness** for Algorithm 3: a scheduled process whose GCA call has
already produced its output *on the projected protocol clock* takes the
corresponding program step.  As for Algorithm 1, the clock guard is required:
`GlobalSchedule.Weak.strongFair_no_event` shows the unguarded version is
unsatisfiable in any run where a GCA call returns. -/
def Fair : Prop := ∀ t p cmd r proposal,
  g.actor t = some p →
  (g.run.state t).localState p = .waiting cmd r proposal →
  (f.protocol r).phase (gcaClockH obj g.run.state g.actor t r) p = 6 →
  (∃ s flag, (f.environment obj r).output p = some (s, flag)) →
  HelpingUniversal.StepBy obj (f.environment obj) p (g.run.state t) (g.run.state (t + 1))

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

theorem blocked_output' (hw : f.SnapshotWaitFree obj) {p : Fin n}
    {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {proposal : (WeakUniversal.Tagged (n := n) obj).Trace} {N : Nat}
    (hblock : ∀ t, N ≤ t → (g.run.state t).localState p = .waiting cmd r proposal)
    (hsched : ∀ M, ∃ t, M ≤ t ∧ g.actor t = some p) :
    ∃ s flag, (f.environment obj r).output p = some (s, flag) :=
  g.inter.round_returned obj hw (g.blocked_infiniteSteps hblock hsched)

/-- **Algorithm 2's calls return**, for Algorithm 3: as for Algorithm 1
(`Weak.callsReturn`), a process inside a call for ever and still scheduled
infinitely often finishes the call on the projected protocol clock, and fairness
then forces its receive step. -/
theorem callsReturn (hfair : g.Fair) (hw : f.SnapshotWaitFree obj) :
    g.toHelpingRun.CallsReturn := by
  intro p cmd r proposal N hblock hsched
  have hinf : g.inter.InfiniteSteps obj r p := g.blocked_infiniteSteps hblock hsched
  obtain ⟨s, flag, hout⟩ := g.inter.round_returned obj hw hinf
  obtain ⟨c, hc⟩ := (f.protocol r).terminates (hw r) (g.inter.protocol_infiniteSteps obj hinf)
  obtain ⟨t₂, ht₂⟩ := g.inter.clock_unbounded obj hinf c
  obtain ⟨t₁, ht₁, hact₁⟩ := hsched (max N t₂)
  have hN : N ≤ t₁ := Nat.le_trans (Nat.le_max_left _ _) ht₁
  have hphase : (f.protocol r).phase (gcaClockH obj g.run.state g.actor t₁ r) p = 6 := by
    have hcl : c ≤ gcaClockH obj g.run.state g.actor t₁ r :=
      Nat.le_trans ht₂ (g.inter.clock_mono obj (Nat.le_trans (Nat.le_max_right _ _) ht₁))
    exact Nat.le_antisymm ((f.protocol r).phase_le_six _ p)
      (hc ▸ (f.protocol r).phase_mono hcl p)
  have hstep := hfair t₁ p cmd r proposal hact₁ (hblock t₁ hN) hphase ⟨s, flag, hout⟩
  exact hstep.moves (by rw [hblock (t₁ + 1) (by omega), hblock t₁ hN])

end Helping

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- **A scheduled process cannot stop taking program steps.**  If it did, it
would be parked inside a GCA call forever while still being scheduled, which the
GCA interface excludes. -/
theorem steps_infinitely {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (N : Nat) :
    ∃ t, N ≤ t ∧
      HelpingUniversal.StepBy obj (H) p
        (g.run.state t) (g.run.state (t + 1)) := by
  classical
  refine Classical.byContradiction (fun hcon => ?_)
  have hno : ∀ t, N ≤ t →
      ¬ HelpingUniversal.StepBy obj (H) p
          (g.run.state t) (g.run.state (t + 1)) :=
    fun t ht hs => hcon ⟨t, ht, hs⟩
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
  obtain ⟨t₀, ht₀, hact₀⟩ := hsched N
  rcases g.step_or_stutter hact₀ with hstep | ⟨⟨r, hrd⟩, _⟩
  · exact absurd hstep (hno t₀ ht₀)
  · rw [hconst t₀ ht₀] at hrd
    obtain ⟨cmd, proposal, hL⟩ := helpingRound_eq_some hrd
    exact g.gca.returns p cmd r proposal N (fun t ht => (hconst t ht).trans hL) hsched

end HelpingGCA

namespace HelpingRun
variable (g : HelpingRun obj H)

theorem localState_stable_of_no_step {t : Nat} {p : Fin n}
    (h : ¬ HelpingUniversal.StepBy obj (H) p
            (g.run.state t) (g.run.state (t + 1))) :
    (g.run.state (t + 1)).localState p = (g.run.state t).localState p := by
  rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
  · rw [heq]
  · by_cases hqp : q = p
    · subst hqp; exact absurd hstep h
    · exact hstep.2 p (fun e => hqp e.symm)
  · rw [heq]

theorem localState_const {a b : Nat} {p : Fin n} (hab : a ≤ b)
    (h : ∀ v, a ≤ v → v < b → ¬ HelpingUniversal.StepBy obj (H) p
      (g.run.state v) (g.run.state (v + 1))) :
    (g.run.state b).localState p = (g.run.state a).localState p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [show a + (d + 1) = (a + d) + 1 from rfl,
        g.localState_stable_of_no_step (h (a + d) (by omega) (by omega))]
      exact ih (by omega) (fun v hv _ => h v hv (by omega))

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

private def muH (g : HelpingGCA obj H) (p : Fin n) (B t : Nat) : Nat :=
  (B - HelpingUniversal.nextRound obj ((g.run.state t).localState p)) * (3 * n + 6 + 1)
    + HelpingUniversal.rank obj ((g.run.state t).localState p)

/-- **Unbounded rounds, from a given time.** -/
theorem atReturn_or_rounds_unbounded_from {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (T : Nat) :
    (∃ t, T ≤ t ∧ HelpingUniversal.AtReturn obj ((g.run.state t).localState p)) ∨
    (∀ B, ∃ t, T ≤ t ∧
      B < HelpingUniversal.nextRound obj ((g.run.state t).localState p)) := by
  classical
  by_cases hret : ∃ t, T ≤ t ∧ HelpingUniversal.AtReturn obj ((g.run.state t).localState p)
  · exact Or.inl hret
  refine Or.inr (fun B => Classical.byContradiction (fun hcon => ?_))
  have hbound : ∀ t, T ≤ t →
      HelpingUniversal.nextRound obj ((g.run.state t).localState p) ≤ B :=
    fun t ht => Nat.le_of_not_lt (fun h => hcon ⟨t, ht, h⟩)
  have hnoret : ∀ t, T ≤ t → ¬ HelpingUniversal.AtReturn obj ((g.run.state t).localState p) :=
    fun t ht h => hret ⟨t, ht, h⟩
  have hrankle : ∀ t, HelpingUniversal.rank obj ((g.run.state t).localState p) ≤ 3 * n + 6 :=
    fun t => HelpingUniversal.rank_le obj
      (HelpingUniversal.todo_bound obj (g.run.reachable obj t)) p
  have hdec : ∀ t, T ≤ t → HelpingUniversal.StepBy obj (H) p
      (g.run.state t) (g.run.state (t + 1)) → muH g p B (t + 1) < muH g p B t := by
    intro t ht hs
    rcases HelpingUniversal.stepBy_progress obj hs with hat | hlt | ⟨heq, hrk⟩
    · exact absurd hat (hnoret t ht)
    · have h1 : (B - HelpingUniversal.nextRound obj ((g.run.state (t + 1)).localState p)) + 1
            ≤ B - HelpingUniversal.nextRound obj ((g.run.state t).localState p) := by
        have := hbound (t + 1) (by omega); have := hbound t ht; omega
      have h2 := Nat.mul_le_mul_right (3 * n + 6 + 1) h1
      rw [Nat.succ_mul] at h2
      have h3 := hrankle (t + 1)
      simp only [muH]
      omega
    · simp only [muH, heq]
      omega
  have hmono : ∀ t, T ≤ t → muH g p B (t + 1) ≤ muH g p B t := by
    intro t ht
    by_cases hs : HelpingUniversal.StepBy obj (H) p
        (g.run.state t) (g.run.state (t + 1))
    · exact Nat.le_of_lt (hdec t ht hs)
    · simp only [muH, g.localState_stable_of_no_step hs]
      exact Nat.le_refl _
  refine no_infinite_decrease (μ := fun t => muH g p B (T + t)) (fun t => ?_) (fun N => ?_)
  · exact hmono (T + t) (by omega)
  · obtain ⟨t, ht, hs⟩ := g.steps_infinitely hsched (T + N)
    refine ⟨t - T, by omega, ?_⟩
    rw [show T + (t - T) = t by omega, show T + (t - T + 1) = t + 1 by omega]
    exact hdec t (by omega) hs

/-- The first step `p` takes at or after `t`, with its state unchanged until
then. -/
theorem next_step {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (t : Nat) :
    ∃ u, t ≤ u ∧ (g.run.state u).localState p = (g.run.state t).localState p ∧
      HelpingUniversal.StepBy obj (H) p
        (g.run.state u) (g.run.state (u + 1)) := by
  obtain ⟨u, ⟨hu, hstep⟩, hmin⟩ := exists_least _ (g.steps_infinitely hsched t)
  exact ⟨u, hu,
    g.localState_const hu (fun v hv hvu hsv => absurd (hmin v ⟨hv, hsv⟩) (by omega)), hstep⟩

end HelpingGCA
end ConflictFreedom.GlobalSchedule

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- **A process on its way to a proposal reaches one.** -/
theorem reaches_waiting {p : Fin n}
    (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    ∀ k t, HelpingUniversal.rank obj ((g.run.state t).localState p) ≤ k →
      n + 3 ≤ HelpingUniversal.rank obj ((g.run.state t).localState p) →
      ∃ u, t ≤ u ∧ ∃ cmd r proposal,
        (g.run.state u).localState p = .waiting cmd r proposal ∧
          HelpingUniversal.nextRound obj ((g.run.state t).localState p) ≤ r := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro t hle hge
    obtain ⟨u, hu, hconst, hstep⟩ := g.next_step hsched t
    have hge' : n + 3 ≤ HelpingUniversal.rank obj ((g.run.state u).localState p) := by
      rw [hconst]; exact hge
    obtain ⟨hnr, hrk, hge2⟩ := HelpingUniversal.stepBy_from_high_rank obj hstep hge'
    rw [hconst] at hnr hrk
    by_cases hnew : n + 3 ≤ HelpingUniversal.rank obj ((g.run.state (u + 1)).localState p)
    · obtain ⟨w, hwu, cmd, r, proposal, hL, hr⟩ :=
        ih _ (by omega) (u + 1) (Nat.le_refl _) hnew
      exact ⟨w, by omega, cmd, r, proposal, hL, by omega⟩
    · obtain ⟨cmd, r, proposal, hL⟩ :=
        HelpingUniversal.rank_eq_waiting obj
          (HelpingUniversal.todo_bound obj (g.run.reachable obj (u + 1)) p)
          (show HelpingUniversal.rank obj ((g.run.state (u + 1)).localState p) = n + 2 by omega)
      refine ⟨u + 1, by omega, cmd, r, proposal, hL, ?_⟩
      rw [hL] at hnr
      simpa [HelpingUniversal.nextRound] using hnr

/-- **The whole loop body makes progress.**  From any state, a process that
keeps taking steps either reaches the point of returning or reaches a `waiting`
state at a round at least the one it was heading for. -/
theorem reaches_waiting_or_return {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    ∀ k t, HelpingUniversal.rank obj ((g.run.state t).localState p) ≤ k →
      (∃ u, t ≤ u ∧ HelpingUniversal.AtReturn obj ((g.run.state u).localState p)) ∨
      (∃ u, t ≤ u ∧ ∃ cmd r proposal,
        (g.run.state u).localState p = .waiting cmd r proposal ∧
          HelpingUniversal.nextRound obj ((g.run.state t).localState p) ≤ r) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro t hle
    cases hL : (g.run.state t).localState p with
    | idle _ | announcing _ _ | collecting _ _ _ | gathering _ _ _ _ =>
        rw [← hL]
        exact Or.inr (g.reaches_waiting hsched _ t (Nat.le_refl _)
          (by rw [hL]; simp only [HelpingUniversal.rank]; omega))
    | waiting cmd r proposal =>
        rw [← hL]
        exact Or.inr ⟨t, Nat.le_refl _, cmd, r, proposal, hL,
          by rw [hL]; simp only [HelpingUniversal.nextRound]; exact Nat.le_refl _⟩
    | publishing cmd seed =>
        rw [← hL]
        obtain ⟨u, hu, hconst, hstep⟩ := g.next_step hsched t
        obtain ⟨order, horder, hnew, -⟩ :=
          HelpingUniversal.stepBy_from_publishing obj hstep (hconst.trans hL)
        have hk : n < k := by
          have hr1 : HelpingUniversal.rank obj ((g.run.state t).localState p) = n + 1 := by
            rw [hL]; rfl
          omega
        have hrn : HelpingUniversal.rank obj ((g.run.state (u + 1)).localState p) ≤ n := by
          rw [hnew]; simp [HelpingUniversal.rank, horder.length_eq]
        have hnr : HelpingUniversal.nextRound obj ((g.run.state (u + 1)).localState p)
            = HelpingUniversal.nextRound obj ((g.run.state t).localState p) := by
          rw [hnew, hL]; rfl
        rcases ih n hk (u + 1) hrn with ⟨w, hw2, hat⟩ | ⟨w, hw2, cmd', r, prop, hLw, hr⟩
        · exact Or.inl ⟨w, by omega, hat⟩
        · exact Or.inr ⟨w, by omega, cmd', r, prop, hLw, by omega⟩
    | checking cmd seed todo seen =>
        rw [← hL]
        cases todo with
        | cons q0 rest =>
            obtain ⟨u, hu, hconst, hstep⟩ := g.next_step hsched t
            obtain ⟨hnew, -⟩ :=
              HelpingUniversal.stepBy_from_checking obj hstep (hconst.trans hL)
            have hk : rest.length < k := by
              have hr1 : HelpingUniversal.rank obj ((g.run.state t).localState p)
                  = rest.length + 1 := by rw [hL]; simp [HelpingUniversal.rank]
              omega
            have hrn : HelpingUniversal.rank obj ((g.run.state (u + 1)).localState p)
                ≤ rest.length := by rw [hnew]; simp [HelpingUniversal.rank]
            have hnr : HelpingUniversal.nextRound obj ((g.run.state (u + 1)).localState p)
                = HelpingUniversal.nextRound obj ((g.run.state t).localState p) := by
              rw [hnew, hL]; rfl
            rcases ih _ hk (u + 1) hrn with ⟨w, hw2, hat⟩ | ⟨w, hw2, cmd', r, prop, hLw, hr⟩
            · exact Or.inl ⟨w, by omega, hat⟩
            · exact Or.inr ⟨w, by omega, cmd', r, prop, hLw, by omega⟩
        | nil =>
            by_cases hc : 0 < (WeakUniversal.Tagged obj).traceCount cmd seen.trace
            · exact Or.inl ⟨t, Nat.le_refl _, cmd, seed, seen, hL, hc⟩
            · obtain ⟨u, hu, hconst, hstep⟩ := g.next_step hsched t
              obtain ⟨order, horder, hnew⟩ := HelpingUniversal.stepBy_retry obj hstep
                (hconst.trans hL) (by omega)
              have hnr : HelpingUniversal.nextRound obj ((g.run.state t).localState p) + 1
                  = HelpingUniversal.nextRound obj ((g.run.state (u + 1)).localState p) := by
                rw [hnew, hL]; rfl
              obtain ⟨w, hw2, cmd', r, prop, hLw, hr⟩ :=
                g.reaches_waiting hsched _ (u + 1) (Nat.le_refl _)
                  (by rw [hnew]; simp only [HelpingUniversal.rank, horder.length_eq,
                    List.length_finRange]; omega)
              exact Or.inr ⟨w, by omega, cmd', r, prop, hLw, by omega⟩

end HelpingGCA
end ConflictFreedom.GlobalSchedule

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingRun
variable (g : HelpingRun obj H)

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
      · exact (HelpingUniversal.stepBy_calls obj hstep).1 call hprev
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
    · rcases (HelpingUniversal.stepBy_calls obj hs).2.1 call hin with hold | howner
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
      · rcases (HelpingUniversal.stepBy_calls obj hstep).2.1 call hcall with hm | hproc
        · exact hm
        · exact absurd hproc hne
      · rw [show N + (d + 1) = (N + d) + 1 from rfl, heq] at hcall; exact hcall

/-- **Solo rounds belong to the solo process.** -/
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

/-- **Registers of other processes hold old rounds.**  A slot's round is a round
its owner called, and every call above the solo bound belongs to the solo
process. -/
theorem slots_bounded_of_solo {p : Fin n} {B : Nat}
    (hB : ∀ (t : Nat) (call : WeakUniversal.Call (n := n) obj),
      call ∈ (g.run.state t).calls → B < call.round → call.process = p)
    (t : Nat) (q : Fin n) (hq : q ≠ p) : ((g.run.state t).slots q).round ≤ B := by
  rcases HelpingUniversal.slot_call obj (g.run.reachable obj t) q with h0 | ⟨call, hmem, h1, h2⟩
  · omega
  · refine Nat.le_of_not_lt (fun hlt => hq ?_)
    rw [← h1]
    exact hB t call hmem (by omega)

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

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- **The solo round commits**, by Commitment and Validity
(`GCA.History.solo_commit`). -/
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

end HelpingGCA

namespace HelpingRun
variable (g : HelpingRun obj H)

/-- While only `p` is scheduled and `p` takes no step, nothing changes at all. -/
theorem solo_state_const {N : Nat} {p : Fin n} (hsolo : g.SoloFrom N p)
    {a b : Nat} (hNa : N ≤ a) (hab : a ≤ b)
    (h : ∀ v, a ≤ v → v < b → ¬ HelpingUniversal.StepBy obj (H) p
      (g.run.state v) (g.run.state (v + 1))) :
    g.run.state b = g.run.state a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [show a + (d + 1) = (a + d) + 1 from rfl]
      rcases g.step_or_frozen hsolo (show N ≤ a + d by omega) with hstep | heq
      · exact absurd hstep (h (a + d) (by omega) (by omega))
      · rw [heq]; exact ih (by omega) (fun v hv _ => h v hv (by omega))

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- The solo process's next step, with the whole configuration frozen until
then. -/
theorem solo_next_step {N : Nat} {p : Fin n} (hsolo : g.SoloFrom N p)
    {t : Nat} (ht : N ≤ t) :
    ∃ u, t ≤ u ∧ g.run.state u = g.run.state t ∧
      HelpingUniversal.StepBy obj (H) p
        (g.run.state u) (g.run.state (u + 1)) := by
  have hsched : ∀ M, ∃ v, M ≤ v ∧ g.actor v = some p :=
    hsolo.sched
  obtain ⟨u, ⟨hu, hstep⟩, hmin⟩ := exists_least _ (g.steps_infinitely hsched t)
  exact ⟨u, hu, g.solo_state_const hsolo ht hu
    (fun v hv hvu hsv => absurd (hmin v ⟨hv, hsv⟩) (by omega)), hstep⟩

/-- **Algorithm 3's final `S` collect adopts the solo process's own trace.**
The collect starts from the empty seed and folds the registers; the solo
process's own register holds the round it just committed, and every other
register holds an older round, so the fold returns the committed seed. -/
theorem solo_check_collect {N : Nat} {p : Fin n} (hsolo : g.SoloFrom N p) {B : Nat}
    (hB : ∀ (t : Nat) (call : WeakUniversal.Call (n := n) obj),
      call ∈ (g.run.state t).calls → B < call.round → call.process = p) :
    ∀ (todo : List (Fin n)) (t : Nat), N ≤ t →
      ∀ (cmd : WeakUniversal.Cmd n Op) (seed seen : WeakUniversal.Seed (n := n) obj),
      (g.run.state t).localState p = .checking cmd seed todo seen →
      (g.run.state t).slots p = seed → B < seed.round →
      ((p ∈ todo ∧ seen.round < seed.round) ∨ seen = seed) →
      ∃ u, t ≤ u ∧ (g.run.state u).localState p = .checking cmd seed [] seed := by
  intro todo
  induction todo with
  | nil =>
      intro t ht cmd seed seen hL hslot hBs hinv
      rcases hinv with ⟨hmem, -⟩ | rfl
      · exact absurd hmem (by simp)
      · exact ⟨t, Nat.le_refl _, hL⟩
  | cons q0 rest ih =>
      intro t ht cmd seed seen hL hslot hBs hinv
      obtain ⟨u, hu, hconst, hstep⟩ := g.solo_next_step hsolo ht
      have hLu : (g.run.state u).localState p = .checking cmd seed (q0 :: rest) seen := by
        rw [hconst]; exact hL
      obtain ⟨hnew, hslots⟩ := HelpingUniversal.stepBy_from_checking obj hstep hLu
      have hslotp : (g.run.state (u + 1)).slots p = seed := by
        rw [hslots, hconst]; exact hslot
      have hq0 : (g.run.state u).slots q0 = (g.run.state t).slots q0 := by rw [hconst]
      have hinv' : (p ∈ rest ∧
          (WeakUniversal.best obj seen ((g.run.state u).slots q0)).round < seed.round) ∨
          WeakUniversal.best obj seen ((g.run.state u).slots q0) = seed := by
        by_cases hq0p : q0 = p
        · right
          have hs0 : (g.run.state u).slots q0 = seed := by rw [hq0, hq0p]; exact hslot
          rw [hs0]
          rcases hinv with ⟨-, hlt⟩ | heq
          · simp [WeakUniversal.best, hlt]
          · rw [heq]; exact HelpingUniversal.best_eq_left obj (Nat.le_refl _)
        · have hbnd : ((g.run.state u).slots q0).round ≤ B := by
            rw [hq0]; exact g.slots_bounded_of_solo hB t q0 hq0p
          rcases hinv with ⟨hmem, hlt⟩ | heq
          · rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact absurd rfl hq0p
            · exact Or.inl ⟨hmem', HelpingUniversal.best_lt obj hlt (by omega)⟩
          · right
            rw [heq]
            exact HelpingUniversal.best_eq_left obj (by omega)
      obtain ⟨w, hw2, hLw⟩ := ih (u + 1) (by omega) cmd seed _ hnew hslotp hBs hinv'
      exact ⟨w, by omega, hLw⟩

/-- **Obstruction-freedom of Algorithm 3, core.**  A process running solo
reaches the state it returns from. -/
theorem solo_reaches_return {p : Fin n} {N : Nat} (hsolo : g.SoloFrom N p) :
    ∃ u, N ≤ u ∧ HelpingUniversal.AtReturn obj ((g.run.state u).localState p) := by
  classical
  have hsched : ∀ M, ∃ t, M ≤ t ∧ g.actor t = some p :=
    hsolo.sched
  obtain ⟨B, hB⟩ := g.solo_calls_own hsolo
  rcases g.atReturn_or_rounds_unbounded_from hsched N with hret | hunb
  · exact hret
  obtain ⟨t, htN, htB⟩ := hunb B
  rcases g.reaches_waiting_or_return hsched _ t (Nat.le_refl _) with
    ⟨u, hu, hat⟩ | ⟨u, hu, cmd, r, prop, hL, hr⟩
  · exact ⟨u, by omega, hat⟩
  · have hrB : B < r := by omega
    obtain ⟨hcall, hcount⟩ :=
      HelpingUniversal.waiting_call obj (g.run.reachable obj u) p cmd r prop hL
    have hin : (H r).input p = some prop := by
      simpa using HelpingUniversal.call_input obj (g.run.reachable obj u) _ hcall
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨v, hv, hconst, hstep⟩ := g.solo_next_step hsolo (show N ≤ u by omega)
    obtain ⟨s, flag, hout, order, -, hnew⟩ :=
      HelpingUniversal.stepBy_from_waiting obj hstep (by rw [hconst]; exact hL)
    obtain ⟨hs, hflag⟩ := g.solo_round_commits hB hrB hin hout
    subst hs; subst hflag
    have hnew' : (g.run.state (v + 1)).localState p = .publishing cmd ⟨r' + 1, s⟩ := by
      rw [hnew]; simp
    obtain ⟨v2, hv2, hconst2, hstep2⟩ :=
      g.solo_next_step hsolo (show N ≤ v + 1 by omega)
    obtain ⟨order2, horder2, hchk, hslots⟩ :=
      HelpingUniversal.stepBy_from_publishing obj hstep2 (by rw [hconst2]; exact hnew')
    have hslotp : (g.run.state (v2 + 1)).slots p = ⟨r' + 1, s⟩ := by
      rw [hslots]; exact WeakUniversal.update_self _ _ _
    obtain ⟨z, hz, hLz⟩ := g.solo_check_collect hsolo hB order2
      (v2 + 1) (by omega) cmd ⟨r' + 1, s⟩ (WeakUniversal.zeroSeed obj) hchk hslotp hrB
      (Or.inl ⟨horder2.mem_iff.mpr (List.mem_finRange p), by simp [WeakUniversal.zeroSeed]⟩)
    exact ⟨z, by omega, cmd, ⟨r' + 1, s⟩, ⟨r' + 1, s⟩, hLz, hcount⟩

/-- **Obstruction-freedom for Algorithm 3.**  A process running solo from `N`
on completes *its own* operation: at some time `u ≥ N` it is at the state it
returns from, holding a command `cmd` it owns, and the response of that very
command is recorded at a strictly later time.

As for Algorithm 1, the conclusion names `p`, `N` and `cmd`; an existential
over an unrelated response somewhere in the run would carry no information
about the solo process. -/
theorem solo_completes {p : Fin n} {N : Nat} (hsolo : g.SoloFrom N p) :
    ∃ u v cmd seed seen, N ≤ u ∧ u < v ∧ cmd.process = p ∧
      (g.run.state u).localState p = .checking cmd seed [] seen ∧
      (⟨cmd, seen.round, seen.trace⟩ : WeakUniversal.Return (n := n) obj) ∈
        (g.run.state v).returns := by
  obtain ⟨u, hu, cmd, seed, seen, hL, hcount⟩ := g.solo_reaches_return hsolo
  obtain ⟨v, hv, hconst, hstep⟩ := g.solo_next_step hsolo hu
  refine ⟨u, v + 1, cmd, seed, seen, hu, by omega, ?_, hL,
    HelpingUniversal.stepBy_at_return obj hstep (by rw [hconst]; exact hL) hcount⟩
  refine ((HelpingUniversal.identity_invariant obj (g.run.reachable obj u)).active_tag
    p cmd ?_).1
  show HelpingUniversal.Local.command obj ((g.run.state u).localState p) = some cmd
  rw [hL]; rfl

end HelpingGCA
end ConflictFreedom.GlobalSchedule
