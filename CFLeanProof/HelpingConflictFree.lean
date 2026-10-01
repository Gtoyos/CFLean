import CFLeanProof.HelpingConflictFreedom

/-!
# Conflict-freedom of Algorithm 3 (Lemma `UCV2isCF`)

This module completes Lemma `UCV2isCF`.  `HelpingProgress.lean` proves its
step-contention-free half and `HelpingConflictFreedom.lean` proves invariant (I)
and the Commitment step; what is added here is the *helping* argument, the part
of the paper that Algorithm 1 has no counterpart for:

> Since we are at some time after `τ'`, `M[i] = cmd(Φ)`.  If `cmd(Φ) ∉ t_j`,
> then `cmd(Φ) ∈ ops(trace(M_j))`. […] In any case, `cmd(Φ) ∈ ops(s_j)`.
> Therefore, process `j` commits `x` and `cmd(Φ) ∈ ops(x)`.  Then, process `j`
> writes `(x, r*+1)` in `S`.  As a result, at round `r*+1` process `i` will read
> `S` and `x = u`.  Thus, `cmd(Φ) ∈ u` and process `i` exits the while loop.

Four state-machine facts make this precise.

* `Local.command` persists (`command_persists`): a process's current command
  changes only through the `finish` step that answers it, so a forever-pending
  operation stays current forever.
* `announcement_persists`: consequently `M[i]` keeps holding `cmd(Φ)`.
* `roundsCalled`: a nonzero round stored in a local seed or in `S` is the round of
  a recorded GCA call.  This is what lets "the largest round reached by any
  process by time `τ'`" bound the *state*, not just the call list, and so makes
  the induction for `helped_input` start.
* `slots_le_nextRound` and `slots_mono`: a process's `S` register never goes
  backwards, so once `j` has written `(x, r)` every later value of `S[j]` is a
  committed trace of a round at least `r`, hence an extension of `x`.
-/

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best Supported
  Committed Stored CallInvariant eq_of_update_ne best_round_left)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- A step of `p` either keeps `p`'s current command or is the `finish` step
that records that command's response. -/
theorem stepBy_command {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} (hc : Local.command obj (c.localState p) = some cmd) :
    Local.command obj (d.localState p) = some cmd ∨
      ∃ r s, (⟨cmd, r, s⟩ : Return (n := n) obj) ∈ d.returns := by
  obtain ⟨hstep, -⟩ := h
  cases hstep with
  | invoke q op seed hq =>
      by_cases hpq : p = q
      · subst hpq; rw [hq] at hc; exact absurd hc (by simp [Local.command])
      · left; show Local.command obj (update _ q _ p) = _
        simpa [update, hpq] using hc
  | receive q cmd' r prop s flag hq ho =>
      by_cases hpq : p = q
      · subst hpq; rw [hq] at hc
        left; show Local.command obj (update _ p _ p) = _
        rw [WeakUniversal.update_self]
        by_cases hf : flag = true <;> simpa [hf, Local.command] using hc
      · left; show Local.command obj (update _ q _ p) = _
        simpa [update, hpq] using hc
  | announce q _ _ hq | readStart q _ _ _ _ hq | collectedStart q _ _ hq
  | readAnnouncement q _ _ _ _ _ hq | propose q _ _ _ hq _ | publish q _ _ hq
  | readCheck q _ _ _ _ _ hq | retry q _ _ _ hq _ =>
      by_cases hpq : p = q
      · subst hpq; rw [hq] at hc
        left; show Local.command obj (update _ p _ p) = _
        simpa [update, Local.command] using hc
      · left; show Local.command obj (update _ q _ p) = _
        simpa [update, hpq] using hc
  | finish q cmd' seed seen hq hcont =>
      by_cases hpq : p = q
      · subst hpq; rw [hq] at hc
        have he : cmd' = cmd := by simpa [Local.command] using hc
        subst he
        exact Or.inr ⟨seen.round, seen.trace, List.mem_cons_self ..⟩
      · left; show Local.command obj (update _ q _ p) = _
        simpa [update, hpq] using hc

/-- Only the acting process can change the announcement array, and only by its
own `announce` step. -/
theorem stepBy_announcement {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) (q : Fin n)
    (hq : q ≠ p) : d.announcements q = c.announcements q := by
  cases h.1 with
  | announce q' cmd seed hq' =>
      obtain rfl := eq_of_update_ne h.moves
      simp [update, hq]
  | _ => rfl

/-- Invocations are added only by `invoke`, which simultaneously makes the new
command its process's current command. -/
theorem step_invocation {H : Environment (n := n) obj}
    {c d : Configuration (n := n) obj} (h : Step obj H c d)
    {cmd : Cmd n Op} (hin : cmd ∈ d.invocations) (hout : cmd ∉ c.invocations) :
    Local.command obj (d.localState cmd.process) = some cmd := by
  cases h with
  | invoke q op seed hq =>
      rcases List.mem_cons.mp hin with rfl | hm
      · simp [update, Local.command]
      · exact absurd hm hout
  | _ => exact absurd hin hout

/-! ### Rounds stored in the state come from recorded calls -/

/-- The round a local state carries. -/
def localRound : Local (n := n) obj → Nat
  | .idle s => s.round
  | .announcing _ s => s.round
  | .collecting _ _ s => s.round
  | .gathering _ s _ _ => s.round
  | .waiting _ r _ => r
  | .publishing _ s => s.round
  | .checking _ s _ _ => s.round

omit [DecidableEq Op] in
theorem best_cases (s t : Seed (n := n) obj) : best obj s t = s ∨ best obj s t = t := by
  unfold WeakUniversal.best
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Every round stored in a local seed or in an `S` register is either the
initial round `0` or the round of a recorded GCA call.  This is what lets the
paper's "largest round reached by any process by time `τ`" bound the *state*
and not merely the list of calls. -/
def RoundsCalled (c : Configuration (n := n) obj) : Prop :=
  (∀ p, (c.slots p).round = 0 ∨ ∃ call ∈ c.calls, call.round = (c.slots p).round) ∧
  (∀ p, localRound obj (c.localState p) = 0 ∨
    ∃ call ∈ c.calls, call.round = localRound obj (c.localState p))

omit [DecidableEq Op] in
private theorem round_mono {c d : Configuration (n := n) obj} {r : Nat}
    (hsub : ∀ call ∈ c.calls, call ∈ d.calls)
    (h : r = 0 ∨ ∃ call ∈ c.calls, call.round = r) :
    r = 0 ∨ ∃ call ∈ d.calls, call.round = r := by
  rcases h with h0 | ⟨call, hmem, he⟩
  · exact Or.inl h0
  · exact Or.inr ⟨call, hsub call hmem, he⟩

theorem roundsCalled {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : RoundsCalled obj c := by
  induction hc with
  | initial => exact ⟨fun p => Or.inl rfl, fun p => Or.inl rfl⟩
  | step hprev hs ih =>
    rename_i prev next
    obtain ⟨ihs, ihl⟩ := ih
    cases hs with
    | readStart p q' cmd todo seed hq =>
        refine ⟨fun q => ihs q, fun q => ?_⟩
        by_cases he : q = p
        · subst he
          have h := ihl q; rw [hq] at h
          simp only [localRound] at h
          rcases best_cases obj seed (prev.slots q') with hb | hb
          · simpa [WeakUniversal.update, localRound, hb] using h
          · simpa [WeakUniversal.update, localRound, hb] using ihs q'
        · simpa [WeakUniversal.update, he] using ihl q
    | propose p cmd seed commands hq arranged harr hi =>
        have hsub : ∀ call ∈ prev.calls, call ∈
            (⟨seed.round + 1, p, proposal obj seed arranged⟩ : Call (n := n) obj) :: prev.calls :=
          fun call hcall => List.mem_cons_of_mem _ hcall
        refine ⟨fun q => round_mono obj hsub (ihs q), fun q => ?_⟩
        by_cases he : q = p
        · subst he
          refine Or.inr ⟨⟨seed.round + 1, q, proposal obj seed arranged⟩,
            List.mem_cons_self .., ?_⟩
          simp [WeakUniversal.update, localRound]
        · exact round_mono obj hsub (by simpa [WeakUniversal.update, he] using ihl q)
    | receive p cmd r prop s flag hq ho =>
        refine ⟨fun q => ihs q, fun q => ?_⟩
        by_cases he : q = p
        · subst he
          have h := ihl q; rw [hq] at h
          simp only [localRound] at h
          by_cases hf : flag = true <;> simpa [WeakUniversal.update, localRound, hf] using h
        · simpa [WeakUniversal.update, he] using ihl q
    | publish p cmd seed hq =>
        have hloc := ihl p
        rw [hq] at hloc
        simp only [localRound] at hloc
        refine ⟨fun q => ?_, fun q => ?_⟩
        · by_cases he : q = p
          · subst he; simpa [WeakUniversal.update] using hloc
          · simpa [WeakUniversal.update, he] using ihs q
        · by_cases he : q = p
          · subst he; simpa [WeakUniversal.update, localRound] using hloc
          · simpa [WeakUniversal.update, he] using ihl q
    | invoke p _ _ hq | announce p _ _ hq | collectedStart p _ _ hq
    | readAnnouncement p _ _ _ _ _ hq | readCheck p _ _ _ _ _ hq | retry p _ _ _ hq _
    | finish p _ _ _ hq _ =>
        refine ⟨fun q => ihs q, fun q => ?_⟩
        by_cases he : q = p
        · subst he
          have h := ihl q; rw [hq] at h
          simpa [WeakUniversal.update, localRound] using h
        · simpa [WeakUniversal.update, he] using ihl q

/-! ### `S` registers never go backwards -/

/-- The round in `S[p]` never exceeds the round `p` is heading for. -/
theorem slots_le_nextRound {H : Environment (n := n) obj}
    {c : Configuration (n := n) obj} (hc : Reachable obj H c) (p : Fin n) :
    (c.slots p).round ≤ nextRound obj (c.localState p) := by
  induction hc with
  | initial => simp [initial, nextRound, WeakUniversal.zeroSeed]
  | step hprev hs ih =>
    rename_i prev next
    cases hs with
    | readStart q q' cmd todo seed hq =>
        by_cases he : q = p
        · subst he
          have h := ih; rw [hq] at h
          simp only [nextRound] at h
          have hb := best_round_left obj seed (prev.slots q')
          have hgoal : (prev.slots q).round
              ≤ (best obj seed (prev.slots q')).round + 1 := by omega
          simpa [WeakUniversal.update, nextRound] using hgoal
        · have hne : ¬ (p = q) := fun e => he e.symm
          simpa [WeakUniversal.update, hne] using ih
    | receive q cmd r prop s flag hq ho =>
        by_cases he : q = p
        · subst he
          have h := ih; rw [hq] at h
          simp only [nextRound] at h
          by_cases hf : flag = true <;> simpa [WeakUniversal.update, nextRound, hf] using h
        · have hne : ¬ (p = q) := fun e => he e.symm
          simpa [WeakUniversal.update, hne] using ih
    | publish q cmd seed hq =>
        by_cases he : q = p
        · subst he
          simp [WeakUniversal.update, nextRound]
        · have hne : ¬ (p = q) := fun e => he e.symm
          simpa [WeakUniversal.update, hne] using ih
    | invoke q _ _ hq | announce q _ _ hq | collectedStart q _ _ hq
    | readAnnouncement q _ _ _ _ _ hq | propose q _ _ _ hq _ | readCheck q _ _ _ _ _ hq =>
        by_cases he : q = p
        · subst he
          have h := ih; rw [hq] at h
          simpa [WeakUniversal.update, nextRound] using h
        · have hne : ¬ (p = q) := fun e => he e.symm
          simpa [WeakUniversal.update, hne] using ih
    | retry q _ seed _ hq _ | finish q _ seed _ hq _ =>
        by_cases he : q = p
        · subst he
          have h := ih; rw [hq] at h
          simp only [nextRound] at h
          have hgoal : (prev.slots q).round ≤ seed.round + 1 := by omega
          simpa [WeakUniversal.update, nextRound] using hgoal
        · have hne : ¬ (p = q) := fun e => he e.symm
          simpa [WeakUniversal.update, hne] using ih

/-- A single step never decreases the round stored in an `S` register. -/
theorem step_slots_mono {H : Environment (n := n) obj}
    {c d : Configuration (n := n) obj} (hc : Reachable obj H c) (hs : Step obj H c d)
    (p : Fin n) : (c.slots p).round ≤ (d.slots p).round := by
  cases hs with
  | publish q cmd seed hq =>
      by_cases he : q = p
      · subst he
        have h := slots_le_nextRound obj hc q
        rw [hq] at h
        simp only [nextRound] at h
        show _ ≤ (update _ q seed q).round
        rw [WeakUniversal.update_self]
        exact h
      · have hne : ¬ (p = q) := fun e => he e.symm
        simp [update, hne]
  | _ => exact Nat.le_refl _

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best Supported
  Committed Stored CallInvariant eq_of_update_ne)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- Only an `announce` step changes the announcement array, and it writes the
announcing process's current command. -/
theorem step_announcement_self {H : Environment (n := n) obj}
    {c d : Configuration (n := n) obj} (h : Step obj H c d) (p : Fin n)
    {a : Cmd n Op} (hcmd : Local.command obj (c.localState p) = some a)
    (hann : c.announcements p = some a) : d.announcements p = some a := by
  cases h with
  | announce q cmd seed hq =>
      by_cases he : q = p
      · subst he
        rw [hq] at hcmd
        have : cmd = a := by simpa [Local.command] using hcmd
        subst this
        simp [update]
      · have hne : ¬ (p = q) := fun e => he e.symm
        simpa [update, hne] using hann
  | _ => exact hann

/-- The only steps that put a process into a `gathering` state are the two that
start a fresh `M` collect and the collect's own register read. -/
theorem stepBy_gathering_source {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {seed : Seed (n := n) obj} {todo : List (Fin n)}
    {commands : List (Cmd n Op)}
    (hd : d.localState p = .gathering cmd seed todo commands) :
    (todo.Perm (List.finRange n) ∧ commands = []) ∨
    (∃ q0 commands0, c.localState p = .gathering cmd seed (q0 :: todo) commands0 ∧
      commands = observe obj seed (c.announcements q0) commands0) := by
  cases h.1 with
  | collectedStart _ _ _ _ order horder | retry _ _ _ _ _ _ order horder =>
      obtain rfl := eq_of_update_ne h.moves
      simp only [WeakUniversal.update, ↓reduceIte] at hd
      injection hd with e1 e2 e3 e4
      exact Or.inl ⟨e3 ▸ horder, e4.symm⟩
  | readAnnouncement q q' cmd' seed' todo' commands' hq =>
      obtain rfl := eq_of_update_ne h.moves
      simp only [WeakUniversal.update, ↓reduceIte] at hd
      injection hd with e1 e2 e3 e4
      subst e1; subst e2; subst e3; subst e4
      exact Or.inr ⟨q', commands', hq, rfl⟩
  | receive q cmd' r prop s flag hq ho =>
      obtain rfl := eq_of_update_ne h.moves
      simp only [WeakUniversal.update, ↓reduceIte] at hd
      split at hd <;> exact absurd hd (by simp)
  | invoke _ _ _ _ | announce _ _ _ _ | readStart _ _ _ _ _ _ | propose _ _ _ _ _ _ _ _
  | publish _ _ _ _ | readCheck _ _ _ _ _ _ _ | finish _ _ _ _ _ _ =>
      obtain rfl := eq_of_update_ne h.moves
      simp only [WeakUniversal.update, ↓reduceIte] at hd
      exact absurd hd (by simp)

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingRun
variable (g : HelpingRun obj H)

/-- A command whose response this run records. -/
def Completes (a : WeakUniversal.Cmd n Op) : Prop :=
  ∃ t r s, (⟨a, r, s⟩ : WeakUniversal.Return (n := n) obj) ∈ (g.run.state t).returns

/-- **A process stays on a command that never returns.** -/
theorem command_persists {p : Fin n} {a : WeakUniversal.Cmd n Op} {τ : Nat}
    (hτ : HelpingUniversal.Local.command obj ((g.run.state τ).localState p) = some a)
    (hnr : ¬ g.Completes a) :
    ∀ t, τ ≤ t →
      HelpingUniversal.Local.command obj ((g.run.state t).localState p) = some a := by
  intro t ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction d with
  | zero => exact hτ
  | succ d ih =>
      show HelpingUniversal.Local.command obj
        ((g.run.state ((τ + d) + 1)).localState p) = some a
      rcases g.step_actor (τ + d) with ⟨-, heq⟩ | ⟨q, -, hstep⟩ | ⟨q, r, -, -, heq⟩
      · rw [heq]; exact ih
      · by_cases hqp : q = p
        · subst hqp
          rcases HelpingUniversal.stepBy_command obj hstep ih with hkeep | ⟨r, s, hmem⟩
          · exact hkeep
          · exact absurd ⟨τ + d + 1, r, s, hmem⟩ hnr
        · rw [hstep.2 p (fun e => hqp e.symm)]; exact ih
      · rw [heq]; exact ih

/-- **`M[i]` keeps holding a command that never returns.** -/
theorem announcement_persists {p : Fin n} {a : WeakUniversal.Cmd n Op} {τ : Nat}
    (hcmd : HelpingUniversal.Local.command obj ((g.run.state τ).localState p) = some a)
    (hann : (g.run.state τ).announcements p = some a)
    (hnr : ¬ g.Completes a) :
    ∀ t, τ ≤ t → (g.run.state t).announcements p = some a := by
  intro t ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction d with
  | zero => exact hann
  | succ d ih =>
      show (g.run.state ((τ + d) + 1)).announcements p = some a
      have hc := g.command_persists hcmd hnr (τ + d) (by omega)
      rcases g.run.next (τ + d) with heq | hstep
      · rw [heq]; exact ih
      · exact HelpingUniversal.step_announcement_self obj hstep p hc ih

/-- `S` registers never go backwards. -/
theorem slots_mono {q : Fin n} {a b : Nat} (hab : a ≤ b) :
    ((g.run.state a).slots q).round ≤ ((g.run.state b).slots q).round := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      refine Nat.le_trans ih ?_
      show ((g.run.state (a + d)).slots q).round ≤ ((g.run.state ((a + d) + 1)).slots q).round
      rcases g.run.next (a + d) with heq | hstep
      · rw [heq]; exact Nat.le_refl _
      · exact HelpingUniversal.step_slots_mono obj (g.run.reachable obj (a + d)) hstep q

/-- A call not yet recorded at `T` was proposed from a finished `M` collect at
or after `T`, for some arrangement of `trace(M_i)`. -/
theorem call_was_gathering_after {T t' : Nat} {call : WeakUniversal.Call (n := n) obj}
    (h : call ∈ (g.run.state t').calls) (hT : call ∉ (g.run.state T).calls) :
    ∃ v, T ≤ v ∧ ∃ cmd seed commands arranged,
      (g.run.state v).localState call.process = .gathering cmd seed [] commands ∧
      arranged.Perm commands ∧ call.round = seed.round + 1 ∧
      call.trace = HelpingUniversal.proposal obj seed arranged := by
  classical
  induction t' with
  | zero => rw [g.run.initial_state] at h; simp [HelpingUniversal.initial] at h
  | succ t ih =>
      by_cases hprev : call ∈ (g.run.state t).calls
      · exact ih hprev
      · have hTt : T ≤ t := by
          refine Nat.le_of_not_lt (fun hlt => hT ?_)
          exact g.calls_mono (by omega) h
        rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
        · rw [heq] at h; exact absurd h hprev
        · obtain ⟨cmd, seed, commands, arranged, hsrc, harr, hr, htr⟩ :=
            HelpingUniversal.stepBy_new_call_source obj hstep h hprev
          exact ⟨t, hTt, cmd, seed, commands, arranged, hsrc, harr, hr, htr⟩
        · rw [heq] at h; exact absurd h hprev

/-- **The helping invariant.**  Once `M[i]` permanently holds `a`, every `M`
collect for a round above the bound `B` already accounts for `a`: either the
collect still has `i` outstanding, or `a` occurs in the trace it will propose. -/
theorem helped_gathering {i : Fin n} {a : WeakUniversal.Cmd n Op} {T B : Nat}
    (hann : ∀ t, T ≤ t → (g.run.state t).announcements i = some a)
    (hbound : ∀ p, HelpingUniversal.localRound obj ((g.run.state T).localState p) ≤ B) :
    ∀ d p cmd seed todo commands,
      (g.run.state (T + d)).localState p = .gathering cmd seed todo commands →
      B < seed.round →
      i ∈ todo ∨ 0 < (WeakUniversal.Tagged obj).traceCount a
        (HelpingUniversal.proposal obj seed commands) := by
  intro d
  induction d with
  | zero =>
      intro p cmd seed todo commands hL hB
      simp only [Nat.add_zero] at hL
      have := hbound p
      rw [hL] at this
      simp only [HelpingUniversal.localRound] at this
      omega
  | succ d ih =>
      intro p cmd seed todo commands hL hB
      rw [show T + (d + 1) = (T + d) + 1 from rfl] at hL
      rcases g.step_actor (T + d) with ⟨-, heq⟩ | ⟨q, -, hstep⟩ | ⟨q, r, -, -, heq⟩
      · rw [heq] at hL; exact ih p cmd seed todo commands hL hB
      · by_cases hqp : q = p
        · subst hqp
          rcases HelpingUniversal.stepBy_gathering_source obj hstep hL with
            ⟨hfresh, -⟩ | ⟨q0, commands0, hsrc, hobs⟩
          · exact Or.inl (hfresh.mem_iff.mpr (List.mem_finRange i))
          · rcases ih q cmd seed (q0 :: todo) commands0 hsrc hB with hmem | hcount
            · rcases List.mem_cons.mp hmem with rfl | hmem'
              · right
                have hax := hann (T + d) (by omega)
                rw [hax] at hobs
                rw [HelpingUniversal.proposal_count]
                by_cases hz : (WeakUniversal.Tagged obj).traceCount a seed.trace = 0
                · rw [hobs]
                  simp only [HelpingUniversal.observe, hz, ↓reduceIte, List.count_append]
                  simp
                · omega
              · exact Or.inl hmem'
            · right
              rw [HelpingUniversal.proposal_count] at hcount ⊢
              rw [hobs]
              have := HelpingUniversal.observe_count_le obj a seed
                ((g.run.state (T + d)).announcements q0) commands0
              omega
        · rw [hstep.2 p (fun e => hqp e.symm)] at hL
          exact ih p cmd seed todo commands hL hB
      · rw [heq] at hL; exact ih p cmd seed todo commands hL hB

/-- Every trace proposed to a round above the bound already contains `a`. -/
theorem helped_input {i : Fin n} {a : WeakUniversal.Cmd n Op} {T B : Nat}
    (hann : ∀ t, T ≤ t → (g.run.state t).announcements i = some a)
    (hbound : ∀ p, HelpingUniversal.localRound obj ((g.run.state T).localState p) ≤ B)
    (hcallbound : ∀ call ∈ (g.run.state T).calls, call.round ≤ B)
    {R : Nat} (hR : B + 1 < R) {p : Fin n}
    {s : (WeakUniversal.Tagged (n := n) obj).Trace} {t' : Nat}
    (hcall : (⟨R, p, s⟩ : WeakUniversal.Call (n := n) obj) ∈ (g.run.state t').calls) :
    0 < (WeakUniversal.Tagged obj).traceCount a s := by
  have hnew : (⟨R, p, s⟩ : WeakUniversal.Call (n := n) obj) ∉ (g.run.state T).calls := by
    intro hm
    have := hcallbound _ hm
    simp only at this
    omega
  obtain ⟨v, hv, cmd, seed, commands, arranged, hsrc, harr, hr, htr⟩ :=
    g.call_was_gathering_after hcall hnew
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hv
  have hround : R = seed.round + 1 := hr
  rcases g.helped_gathering hann hbound d p cmd seed [] commands hsrc (by omega) with hmem | hc
  · exact absurd hmem (by simp)
  · have : s = HelpingUniversal.proposal obj seed arranged := htr
    rw [this, HelpingUniversal.proposal_count_perm obj a seed harr]; exact hc

end HelpingRun
end ConflictFreedom.GlobalSchedule

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- **The final `S` collect adopts a register of round at least `R`.**  Once
some register is known to hold a round at least `R`, the collect's `best` fold
returns a seed of round at least `R`. -/
theorem check_collect_above {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    {j : Fin n} {R w0 : Nat}
    (hslot : ∀ t, w0 ≤ t → R ≤ ((g.run.state t).slots j).round) :
    ∀ (todo : List (Fin n)) (t : Nat), w0 ≤ t →
      ∀ cmd seed seen, (g.run.state t).localState p = .checking cmd seed todo seen →
      (j ∈ todo ∨ R ≤ seen.round) →
      ∃ u, t ≤ u ∧ ∃ seen', (g.run.state u).localState p = .checking cmd seed [] seen' ∧
        R ≤ seen'.round := by
  intro todo
  induction todo with
  | nil =>
      intro t ht cmd seed seen hL hinv
      rcases hinv with hmem | hR
      · exact absurd hmem (by simp)
      · exact ⟨t, Nat.le_refl _, seen, hL, hR⟩
  | cons q0 rest ih =>
      intro t ht cmd seed seen hL hinv
      obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched t
      obtain ⟨hnew, -⟩ :=
        HelpingUniversal.stepBy_from_checking obj hstep (hconst.trans hL)
      have hinv' : j ∈ rest ∨
          R ≤ (WeakUniversal.best obj seen ((g.run.state v).slots q0)).round := by
        rcases hinv with hmem | hRs
        · rcases List.mem_cons.mp hmem with rfl | hmem'
          · exact Or.inr (Nat.le_trans (hslot v (by omega))
              (WeakUniversal.best_round_right obj seen _))
          · exact Or.inl hmem'
        · exact Or.inr (Nat.le_trans hRs (WeakUniversal.best_round_left obj seen _))
      obtain ⟨u, hu, seen', hLu, hR'⟩ := ih (v + 1) (by omega) cmd seed _ hnew hinv'
      exact ⟨u, by omega, seen', hLu, hR'⟩

/-- Reaching the returning state records the response. -/
theorem atReturn_completes {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) {u : Nat}
    (hat : HelpingUniversal.AtReturn obj ((g.run.state u).localState p)) :
    ∃ cmd, HelpingUniversal.Local.command obj ((g.run.state u).localState p) = some cmd ∧
      g.Completes cmd := by
  obtain ⟨cmd, seed, seen, hL, hcount⟩ := hat
  refine ⟨cmd, by rw [hL]; rfl, ?_⟩
  obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched u
  exact ⟨v + 1, seen.round, seen.trace,
    HelpingUniversal.stepBy_at_return obj hstep (hconst.trans hL) hcount⟩

/-- From a `waiting` state the process starts a fresh final `S` collect. -/
theorem reaches_fresh_collect {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    {u : Nat} {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {prop : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hL : (g.run.state u).localState p = .waiting cmd r prop) :
    ∃ v, u ≤ v ∧ ∃ seed, ∃ order : List (Fin n), order.Perm (List.finRange n) ∧
      (g.run.state v).localState p = .checking cmd seed order (WeakUniversal.zeroSeed obj) := by
  obtain ⟨v1, hv1, hconst1, hstep1⟩ := g.next_step hsched u
  obtain ⟨s, flag, hout, order, horder, hnew⟩ :=
    HelpingUniversal.stepBy_from_waiting obj hstep1 (hconst1.trans hL)
  by_cases hf : flag = true
  · have hpub : (g.run.state (v1 + 1)).localState p = .publishing cmd ⟨r, s⟩ := by
      rw [hnew]; simp [hf]
    obtain ⟨v2, hv2, hconst2, hstep2⟩ := g.next_step hsched (v1 + 1)
    obtain ⟨order2, horder2, hchk, -⟩ :=
      HelpingUniversal.stepBy_from_publishing obj hstep2 (hconst2.trans hpub)
    exact ⟨v2 + 1, by omega, ⟨r, s⟩, order2, horder2, hchk⟩
  · have hchk : (g.run.state (v1 + 1)).localState p =
        .checking cmd ⟨r, s⟩ order (WeakUniversal.zeroSeed obj) := by
      rw [hnew]; simp [hf]
    exact ⟨v1 + 1, by omega, ⟨r, s⟩, order, horder, hchk⟩

/-- **Lemma `UCV2isCF`, eventually-conflict-free half.**  In an eventually
conflict-free run of Algorithm 3, *every* operation of a process that keeps
taking steps completes.  This is the paper's argument in full: `M[i]` keeps
holding `cmd(Φ)`, so every proposal to a high enough round contains it; by
invariant (I) those proposals are compatible, so Commitment produces a
committed trace containing `cmd(Φ)`; its author writes that trace into `S`,
and `i`'s next `S` collect therefore adopts a committed trace of at least that
round, which extends it.  Process `i` leaves the loop. -/
theorem operation_completes_of_compatible (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} (hi : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some i)
    {k₀ : Nat}
    (hk₀ : ∀ k, k₀ ≤ k →
      (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs)
    (hcallers : ∀ k, k₀ ≤ k →
      ∀ q, (∃ s, (H (k + 2)).input q = some s) →
        ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q)
    {τ₀ : Nat} {a : WeakUniversal.Cmd n Op}
    (ha : HelpingUniversal.Local.command obj ((g.run.state τ₀).localState i) = some a) :
    g.Completes a := by
  classical
  apply Classical.byContradiction
  intro hnr
  have hcmd := g.command_persists ha hnr
  have hnoAt : ∀ u, τ₀ ≤ u →
      ¬ HelpingUniversal.AtReturn obj ((g.run.state u).localState i) := by
    intro u hu hat
    obtain ⟨cmd, hc, hcomp⟩ := g.atReturn_completes hi hat
    have he : cmd = a := Option.some.inj (hc.symm.trans (hcmd u hu))
    exact hnr (he ▸ hcomp)
  -- `i` reaches a `waiting` state, so it has announced `a`
  rcases g.reaches_waiting_or_return hi _ τ₀ (Nat.le_refl _) with
    ⟨u0, hu0, hat⟩ | ⟨τ₁, hτ₁, cmd₁, r₁, prop₁, hL₁, -⟩
  · exact hnoAt u0 hu0 hat
  have hcmd₁ : HelpingUniversal.Local.command obj ((g.run.state τ₁).localState i)
      = some cmd₁ := by rw [hL₁]; rfl
  have hc1a : cmd₁ = a := Option.some.inj (hcmd₁.symm.trans (hcmd τ₁ hτ₁))
  rw [hc1a] at hL₁
  have hann₁ : (g.run.state τ₁).announcements i = some a := by
    have hA := HelpingUniversal.announced obj (g.run.reachable obj τ₁) i
    rw [hL₁] at hA
    simpa only [HelpingUniversal.AnnouncedFor] using hA
  have hann : ∀ t, τ₁ ≤ t → (g.run.state t).announcements i = some a :=
    g.announcement_persists (by rw [hL₁]; rfl) hann₁ hnr
  -- the paper's `r_0`: a bound on every round stored anywhere at time `τ₁`
  obtain ⟨B, hB⟩ := WeakUniversal.calls_round_bound obj (g.run.state τ₁).calls
  have hbound : ∀ p, HelpingUniversal.localRound obj
      ((g.run.state τ₁).localState p) ≤ B := by
    intro p
    rcases (HelpingUniversal.roundsCalled obj (g.run.reachable obj τ₁)).2 p with
      h0 | ⟨call, hmem, he⟩
    · omega
    · rw [← he]; exact hB call hmem
  -- `i` eventually waits on a round above that bound
  rcases g.atReturn_or_rounds_unbounded_from hi τ₁ with ⟨u1, hu1, hat⟩ | hunb
  · exact hnoAt u1 (by omega) hat
  obtain ⟨t2, ht2, ht2B⟩ := hunb (max (k₀ + 1) (B + 1))
  rcases g.reaches_waiting_or_return hi _ t2 (Nat.le_refl _) with
    ⟨u2, hu2, hat⟩ | ⟨u3, hu3, cmd₃, R, prop₃, hL₃, hR⟩
  · exact hnoAt u2 (by omega) hat
  have hm1 : k₀ + 1 ≤ max (k₀ + 1) (B + 1) := Nat.le_max_left _ _
  have hm2 : B + 1 ≤ max (k₀ + 1) (B + 1) := Nat.le_max_right _ _
  obtain ⟨k, rfl⟩ : ∃ k, R = k + 2 := ⟨R - 2, by omega⟩
  have hCk := hk₀ k (show k₀ ≤ k by omega)
  obtain ⟨hcall₃, -⟩ :=
    HelpingUniversal.waiting_call obj (g.run.reachable obj u3) i cmd₃ (k + 2) prop₃ hL₃
  have hin₃ : (H (k + 2)).input i = some prop₃ := by
    simpa using HelpingUniversal.call_input obj (g.run.reachable obj u3) _ hcall₃
  -- Commitment
  obtain ⟨j, sj, x, hinj, houtj, hprej⟩ :=
    g.exists_commit_of_compatible hCk ⟨prop₃, i, hin₃⟩
      (hcallers k (show k₀ ≤ k by omega))
  obtain ⟨tj, hcallj⟩ := (g.input_iff_call (k + 1) j sj).mp hinj
  have hasj : 0 < (WeakUniversal.Tagged obj).traceCount a sj :=
    g.helped_input hann hbound hB (show B + 1 < k + 1 + 1 by omega) hcallj
  have hax : 0 < (WeakUniversal.Tagged obj).traceCount a x :=
    Nat.lt_of_lt_of_le hasj ((WeakUniversal.Tagged obj).traceCount_mono hprej a)
  -- the committing process writes `x` into `S`
  have hschedj := hcallers k (show k₀ ≤ k by omega) j ⟨sj, hinj⟩
  obtain ⟨uj, cmdj, hLj⟩ := g.call_was_waiting hcallj
  obtain ⟨v1, hv1, hconst1, hstep1⟩ := g.next_step hschedj uj
  obtain ⟨s', flag', hout', order', -, hnew'⟩ :=
    HelpingUniversal.stepBy_from_waiting obj hstep1 (hconst1.trans hLj)
  have hsx : (s', flag') = (x, true) := Option.some.inj (hout'.symm.trans houtj)
  have hs' : s' = x := congrArg Prod.fst hsx
  have hf' : flag' = true := congrArg Prod.snd hsx
  subst hs'; subst hf'
  have hpub : (g.run.state (v1 + 1)).localState j = .publishing cmdj ⟨k + 2, s'⟩ := by
    rw [hnew']; simp
  obtain ⟨v2, hv2, hconst2, hstep2⟩ := g.next_step hschedj (v1 + 1)
  obtain ⟨order2, -, hchk, hslots⟩ :=
    HelpingUniversal.stepBy_from_publishing obj hstep2 (hconst2.trans hpub)
  have hslotj : ((g.run.state (v2 + 1)).slots j) = ⟨k + 2, s'⟩ := by
    rw [hslots]; exact WeakUniversal.update_self _ _ _
  have hslotR : ∀ t, v2 + 1 ≤ t → k + 2 ≤ ((g.run.state t).slots j).round := by
    intro t ht
    have hmono := g.slots_mono (q := j) ht
    rw [hslotj] at hmono
    exact hmono
  -- `i` collects `S` again and finds a committed trace above round `k + 2`
  rcases g.reaches_waiting_or_return hi _ (max (v2 + 1) τ₀) (Nat.le_refl _) with
    ⟨u4, hu4, hat⟩ | ⟨u5, hu5, cmd₅, r₅, prop₅, hL₅, -⟩
  · exact hnoAt u4 (Nat.le_trans (Nat.le_max_right _ _) hu4) hat
  obtain ⟨v5, hv5, seed5, order5, horder5, hchk5⟩ := g.reaches_fresh_collect hi hL₅
  have hmax1 : v2 + 1 ≤ max (v2 + 1) τ₀ := Nat.le_max_left _ _
  have hmax2 : τ₀ ≤ max (v2 + 1) τ₀ := Nat.le_max_right _ _
  obtain ⟨z, hz, seen', hLz, hRz⟩ :=
    g.check_collect_above hi hslotR order5 v5 (by omega)
      cmd₅ seed5 _ hchk5 (Or.inl (horder5.mem_iff.mpr (List.mem_finRange j)))
  have hcmdz : HelpingUniversal.Local.command obj ((g.run.state z).localState i)
      = some cmd₅ := by rw [hLz]; rfl
  have hc5 : cmd₅ = a := Option.some.inj (hcmdz.symm.trans (hcmd z (by omega)))
  -- the adopted seed is a committed trace of a round at least `k + 2`
  have hloc := (HelpingUniversal.invariant obj (g.run.reachable obj z)).localState i
  rw [hLz] at hloc
  obtain ⟨-, hstoredz⟩ := hloc
  rcases hstoredz with ⟨h0, -⟩ | hcom
  · omega
  obtain ⟨hpos, q', hq'⟩ := hcom
  obtain ⟨k', hk'⟩ : ∃ k', seen'.round = k' + 1 := ⟨seen'.round - 1, by omega⟩
  rw [hk'] at hq'
  have hpre : (WeakUniversal.Tagged obj).TracePrefix s' seen'.trace :=
    HelpingUniversal.committed_prefix obj coverage (g.gca.spec)
      (show k + 1 ≤ k' by omega) houtj hq'
  have hfinal : 0 < (WeakUniversal.Tagged obj).traceCount a seen'.trace :=
    Nat.lt_of_lt_of_le hax ((WeakUniversal.Tagged obj).traceCount_mono hpre a)
  exact hnoAt z (by omega) ⟨cmd₅, seed5, seen', hLz, by rw [hc5]; exact hfinal⟩

end HelpingGCA
end ConflictFreedom.GlobalSchedule

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- `operation_completes_of_compatible` under the paper's nonconflict
hypothesis: the eventually-conflict-free half of Lemma `UCV2isCF`. -/
theorem operation_completes (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} (hi : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some i)
    (hC : ∃ k₀, ∀ k, k₀ ≤ k →
      (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k))
    {τ₀ : Nat} {a : WeakUniversal.Cmd n Op}
    (ha : HelpingUniversal.Local.command obj ((g.run.state τ₀).localState i) = some a) :
    g.Completes a := by
  obtain ⟨k₀, hk₀⟩ := hC
  obtain ⟨B, hB⟩ := g.eventually_callers_stepping
  exact g.operation_completes_of_compatible coverage hi (k₀ := max k₀ B)
    (fun k hk => g.inputs_compatible_total coverage (hk₀ k (by omega)))
    (fun k hk => hB k (by omega)) ha

end HelpingGCA

namespace HelpingRun
variable (g : HelpingRun obj H)

/-- Every invoked command was, at some time, its process's current command. -/
theorem invoked_command {a : WeakUniversal.Cmd n Op} (h : g.Invoked a) :
    ∃ τ, HelpingUniversal.Local.command obj
      ((g.run.state τ).localState a.process) = some a := by
  classical
  obtain ⟨t, ht⟩ := h
  induction t with
  | zero =>
      rw [g.run.initial_state] at ht
      simp [HelpingUniversal.initial] at ht
  | succ t ih =>
      by_cases hprev : a ∈ (g.run.state t).invocations
      · exact ih hprev
      · rcases g.run.next t with he | hs
        · exact absurd (he ▸ ht) hprev
        · exact ⟨t + 1, HelpingUniversal.step_invocation obj hs ht hprev⟩

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- **Conflict-freedom of Algorithm 3, invocation form.**  Every command a
process with infinitely many steps invokes eventually gets a response. -/
theorem invoked_completes (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} (hi : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some i)
    (hC : ∃ k₀, ∀ k, k₀ ≤ k →
      (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k))
    {a : WeakUniversal.Cmd n Op} (hinv : g.Invoked a) (hproc : a.process = i) :
    g.Completes a := by
  obtain ⟨τ, hτ⟩ := g.invoked_command hinv
  rw [hproc] at hτ
  exact g.operation_completes coverage hi hC hτ

/-- **Lemma `UCV2isCF` for Algorithm 3, at the level of the global schedule.**
Both halves of the manuscript's statement:

* *eventual step-contention-freedom* -- a process that eventually runs solo
  completes *its own* pending operation, after the solo phase begins
  (`solo_completes`);
* *eventual conflict-freedom* -- **every** operation of **every** process that
  keeps taking steps completes.

The second half is genuinely stronger than Algorithm 1's `weakUCWCF`, which
only produces *some* process that completes all its operations; the helping
array is what closes the gap.

Call coverage is *not* a hypothesis: it is derived from the schedule
(`HelpingRun.callsCovered`).  The GCA objects are only required to meet the
interface (`HelpingRun.GCAInterface`). -/
theorem UCV2isCF :
    (∀ (p : Fin n) (N : Nat), g.SoloFrom N p →
      ∃ u v cmd seed seen, N ≤ u ∧ u < v ∧ cmd.process = p ∧
        (g.run.state u).localState p = .checking cmd seed [] seen ∧
        (⟨cmd, seen.round, seen.trace⟩ : WeakUniversal.Return (n := n) obj) ∈
          (g.run.state v).returns) ∧
    ((∃ k₀, ∀ k, k₀ ≤ k → (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k)) →
      ∀ i : Fin n, (∀ N, ∃ t, N ≤ t ∧ g.actor t = some i) →
        ∀ a, g.Invoked a → a.process = i → g.Completes a) :=
  ⟨fun _ _ hsolo => g.solo_completes hsolo,
    fun hC _i hi _a hinv hproc =>
      g.invoked_completes g.callsCovered hi hC hinv hproc⟩

end HelpingGCA
end ConflictFreedom.GlobalSchedule
