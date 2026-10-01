import CFLeanProof.HelpingInvariantTwo

/-!
# `th:cr`: a solo checkpoint lets Algorithm 3 resolve every conflict (inside one run)

This module is the progress half of Theorem `th:cr`, proved inside one global
schedule (`GlobalSchedule.Helping`).  `UCResolve.lean` builds the finite solo
extension on the forward machine and quantifies over its extensions.

The manuscript's proof has a solo part and a resolution part.  After `α`,
process `i` runs alone until it proposes a trace `s'` to a round `r₁` above
every round reached in `α`; it is that round's only participant, so it commits
`s'`, writes `(r₁, s')` into `S` and completes; `α'` ends there.  Two facts about
`α'` are all the resolution part uses:

* `(r₁, s')` sits in `S`, committed; and
* **every operation instance invoked before the end of `α'` has its command in
  `ops(s')`** — with §7's point of invocation: "we consider an operation
  instance as invoked once its associated command is written into `M`
  (Line 5)" (`AnnouncedBy`).

The resolution part (`resolving_completes`) follows the manuscript's
contradiction.  Let `Φ`, with command `a`, be an operation of a correct process
that is pending forever.  Then `a` was not invoked before the end of `α'`: its
command would be in `s'`, and the next final `S` collect would find it
(`completes_of_slot`).  Past the time `a` is announced and the largest round
`r₂` reached by then:

* **(II)** every output of a round `r > r₂` contains `a`
  (`output_contains_own_of`).  A residual command `cmd(Φ')` of a proposal misses
  the common prefix `t`, which contains `s'` (`lemma:prefix-rounds`), so `Φ'`
  was invoked after `α'`; it had not completed before, so it is pending at a
  common time with `Φ` (`pendingAfter_witness`), and the hypothesis makes it
  independent of `a`.
* **(I)** the proposals to a round `r > r₂` are compatible.  A commit above
  `r₂` is written into `S` (`commit_published`), and every trace a process then
  reads from `S` is committed above `r₂`, so contains `a` by (II) and completes
  `Φ` (`completes_of_high_slot`): there is no such commit.  So residual commands
  never complete; being invoked after `α'` they do not conflict
  (`inputs_compatible_res`).

`Φ`'s process waits on a round above `r₂`, where by (I) and Commitment some
process commits, a contradiction.

The hypothesis is the manuscript's "eventually `α'`-conflict-free" with that
point of invocation: pending means written into `M` and not yet answered
(`EventuallyNonconflictingAfter`).  Three facts about `M` make it usable: every
command of a GCA input was written into `M` (`input_announced`), a command is
written into `M` before it is answered (`announced_before_answer`), and an
announcement stays in `M` until it is answered (`announcement_or_answered`).
-/

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best
  Supported Committed Stored CallInvariant)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- A trace committed at round `rc ≤ k + 1` prefixes the greatest common prefix
of any set of outputs of round `k + 1` (`lemma:prefix-rounds`). -/
theorem committed_below_glb {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H) (spec : ∀ r, (H (r + 1)).Specification)
    {rc : Nat} {sc : (Tagged (n := n) obj).Trace} (hcom : Committed obj H rc sc)
    {k : Nat} (hk : rc ≤ k + 1)
    {X : (Tagged (n := n) obj).Trace → Prop} (hX : ∀ x, X x → (H (k + 1)).Outputs x)
    {t : (Tagged (n := n) obj).Trace} (ht : (Tagged obj).IsGLB X t) :
    (Tagged obj).TracePrefix sc t := by
  obtain ⟨hpos, q, hq⟩ := hcom
  obtain ⟨r, hr⟩ : ∃ r, rc = r + 1 := ⟨rc - 1, by omega⟩
  rw [hr] at hq hk
  refine ht.2 sc ?_
  intro x hx
  obtain ⟨p', flag, hx⟩ := hX x hx
  exact committed_prefix obj coverage spec (by omega) hq hx

/-! ## What `M` records

Configuration invariants about the announcement array and the responses. -/

/-- A process that holds no announced command of its own: it is idle, or it
has invoked an operation and not yet written its command into `M` (Line 5). -/
def Unannounced : Local (n := n) obj → Prop
  | .idle _ => True
  | .announcing _ _ => True
  | _ => False

/-- **What `M[q]` holds between two operations of `q`.**  While `q` holds no
announced command of its own, the command left in `M[q]` has been answered. -/
theorem announcement_answered {H : Environment (n := n) obj}
    {c : Configuration (n := n) obj} (hc : Reachable obj H c) :
    ∀ q a, c.announcements q = some a → Unannounced obj (c.localState q) →
      ∃ ret ∈ c.returns, ret.command = a := by
  induction hc with
  | initial => intro q a h; simp [initial] at h
  | step hr hs ih =>
      cases hs with
      | invoke p op seed h =>
          intro q a hq hu
          by_cases hqp : q = p
          · subst hqp; exact ih q a hq (by rw [h]; trivial)
          · exact ih q a hq (by simpa [update, hqp] using hu)
      | announce p cmd seed h =>
          intro q a hq hu
          by_cases hqp : q = p
          · subst hqp; simp [update, Unannounced] at hu
          · exact ih q a (by simpa [update, hqp] using hq) (by simpa [update, hqp] using hu)
      | receive p cmd r prop s flag h ho =>
          intro q a hq hu
          by_cases hqp : q = p
          · subst hqp
            simp only [update, ↓reduceIte] at hu
            split at hu <;> simp [Unannounced] at hu
          · exact ih q a hq (by simpa [update, hqp] using hu)
      | readStart p _ _ _ _ _ | collectedStart p _ _ _ | readAnnouncement p _ _ _ _ _ _
      | propose p _ _ _ _ _ | publish p _ _ _ | readCheck p _ _ _ _ _ _ | retry p _ _ _ _ _ =>
          intro q a hq hu
          by_cases hqp : q = p
          · subst hqp; simp [update, Unannounced] at hu
          · exact ih q a hq (by simpa [update, hqp] using hu)
      | finish p cmd seed seen h hcont =>
          intro q a hq hu
          by_cases hqp : q = p
          · subst hqp
            have hann := announced obj hr q
            rw [h] at hann
            simp only [AnnouncedFor] at hann
            have hac : cmd = a := Option.some.inj (hann.symm.trans hq)
            exact ⟨⟨cmd, seen.round, seen.trace⟩, List.mem_cons_self .., hac⟩
          · obtain ⟨ret, hret, he⟩ := ih q a hq (by simpa [update, hqp] using hu)
            exact ⟨ret, List.mem_cons_of_mem _ hret, he⟩

/-- **Responses come from called rounds.**  The trace a final `S` collect
adopts is the initial seed or a register, and a nonzero round in a register is
the round of its owner's GCA call (`slot_call`); a response records the adopted
round.  So every nonzero round a response or an unfinished final collect holds
is the round of a recorded GCA call. -/
def ReturnsCalled (c : Configuration (n := n) obj) : Prop :=
  (∀ p cmd seed todo seen, c.localState p = .checking cmd seed todo seen →
    seen.round = 0 ∨ ∃ call ∈ c.calls, call.round = seen.round) ∧
  (∀ ret ∈ c.returns, ret.round = 0 ∨ ∃ call ∈ c.calls, call.round = ret.round)

omit [DecidableEq Op] in
private theorem called_mono {c d : Configuration (n := n) obj} {r : Nat}
    (hsub : ∀ call ∈ c.calls, call ∈ d.calls)
    (h : r = 0 ∨ ∃ call ∈ c.calls, call.round = r) :
    r = 0 ∨ ∃ call ∈ d.calls, call.round = r := by
  rcases h with h0 | ⟨call, hmem, he⟩
  · exact Or.inl h0
  · exact Or.inr ⟨call, hsub call hmem, he⟩

theorem returnsCalled {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : ReturnsCalled obj c := by
  induction hc with
  | initial =>
      exact ⟨fun p cmd seed todo seen h => by simp [initial] at h,
        fun ret h => by simp [initial] at h⟩
  | step hprev hs ih =>
    rename_i prev next
    obtain ⟨ihc, ihr⟩ := ih
    cases hs with
    | readCheck p q cmd seed todo seen h =>
        refine ⟨fun p' cmd' seed' todo' seen' h' => ?_, ihr⟩
        by_cases hp : p' = p
        · subst hp
          simp only [update, ↓reduceIte, Local.checking.injEq] at h'
          obtain ⟨-, -, -, rfl⟩ := h'
          rcases best_cases obj seen (prev.slots q) with hb | hb
          · rw [hb]; exact ihc p' cmd seed (q :: todo) seen h
          · rw [hb]
            rcases slot_call obj hprev q with h0 | ⟨call, hmem, -, he⟩
            · exact Or.inl h0
            · exact Or.inr ⟨call, hmem, he⟩
        · exact ihc p' cmd' seed' todo' seen' (by simpa [update, hp] using h')
    | receive p cmd r prop s flag h ho =>
        refine ⟨fun p' cmd' seed' todo' seen' h' => ?_, ihr⟩
        by_cases hp : p' = p
        · subst hp
          simp only [update, ↓reduceIte] at h'
          split at h'
          · cases h'
          · simp only [Local.checking.injEq] at h'
            obtain ⟨-, -, -, rfl⟩ := h'
            exact Or.inl rfl
        · exact ihc p' cmd' seed' todo' seen' (by simpa [update, hp] using h')
    | publish p cmd seed h =>
        refine ⟨fun p' cmd' seed' todo' seen' h' => ?_, ihr⟩
        by_cases hp : p' = p
        · subst hp
          simp only [update, ↓reduceIte, Local.checking.injEq] at h'
          obtain ⟨-, -, -, rfl⟩ := h'
          exact Or.inl rfl
        · exact ihc p' cmd' seed' todo' seen' (by simpa [update, hp] using h')
    | finish p cmd seed seen h hcont =>
        refine ⟨fun p' cmd' seed' todo' seen' h' => ?_, fun ret hret => ?_⟩
        · by_cases hp : p' = p
          · subst hp; simp [update] at h'
          · exact ihc p' cmd' seed' todo' seen' (by simpa [update, hp] using h')
        · rcases List.mem_cons.mp hret with rfl | hret
          · exact ihc p cmd seed [] seen h
          · exact ihr ret hret
    | propose p cmd seed commands h arranged harr hi =>
        have hsub : ∀ call ∈ prev.calls, call ∈
            (⟨seed.round + 1, p, proposal obj seed arranged⟩ : Call (n := n) obj) :: prev.calls :=
          fun call hcall => List.mem_cons_of_mem _ hcall
        refine ⟨fun p' cmd' seed' todo' seen' h' => ?_,
          fun ret hret => called_mono obj hsub (ihr ret hret)⟩
        by_cases hp : p' = p
        · subst hp; simp [update] at h'
        · exact called_mono obj hsub (ihc p' cmd' seed' todo' seen' (by simpa [update, hp] using h'))
    | invoke p _ _ _ | announce p _ _ _ | readStart p _ _ _ _ _ | collectedStart p _ _ _
    | readAnnouncement p _ _ _ _ _ _ | retry p _ _ _ _ _ =>
        refine ⟨fun p' cmd' seed' todo' seen' h' => ?_, ihr⟩
        by_cases hp : p' = p
        · subst hp; simp [update] at h'
        · exact ihc p' cmd' seed' todo' seen' (by simpa [update, hp] using h')

/-- Only an `announce` step of `q` changes `M[q]`, and it fires while `q` holds
no announced command. -/
theorem step_announcement {H : Environment (n := n) obj}
    {c d : Configuration (n := n) obj} (h : Step obj H c d) (q : Fin n) :
    d.announcements q = c.announcements q ∨ Unannounced obj (c.localState q) := by
  cases h with
  | announce p cmd seed hp =>
      by_cases hqp : q = p
      · subst hqp; right; rw [hp]; trivial
      · left; simp [update, hqp]
  | _ => exact Or.inl rfl

/-- A step that records a new response is the `finish` step of that command's
process, fired from a finished final collect. -/
theorem step_new_return {H : Environment (n := n) obj}
    {c d : Configuration (n := n) obj} (h : Step obj H c d)
    {ret : Return (n := n) obj} (hin : ret ∈ d.returns) (hout : ret ∉ c.returns) :
    ∃ p seed seen, c.localState p = .checking ret.command seed [] seen := by
  cases h with
  | finish p cmd seed seen hp hcont =>
      rcases List.mem_cons.mp hin with rfl | hm
      · exact ⟨p, seed, seen, hp⟩
      · exact absurd hm hout
  | _ => exact absurd hin hout

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingRun
variable (g : HelpingRun obj H)

/-! ## §7's point of invocation, on a run -/

/-- **§7's point of invocation.**  "We consider an operation instance as
invoked once its associated command is written into `M` (Line 5)":
`AnnouncedBy t a` says that by time `t` the command `a` has been written into
`M[a.process]`. -/
def AnnouncedBy (t : Nat) (a : WeakUniversal.Cmd n Op) : Prop :=
  ∃ u, u ≤ t ∧ (g.run.state u).announcements a.process = some a

theorem announcedBy_mono {t t' : Nat} (ht : t ≤ t') {a : WeakUniversal.Cmd n Op}
    (h : g.AnnouncedBy t a) : g.AnnouncedBy t' a := by
  obtain ⟨u, hu, hm⟩ := h
  exact ⟨u, by omega, hm⟩

/-- A response, once recorded, stays recorded. -/
theorem answered_mono {u v : Nat} (huv : u ≤ v) {a : WeakUniversal.Cmd n Op}
    (h : ∃ ret ∈ (g.run.state u).returns, ret.command = a) :
    ∃ ret ∈ (g.run.state v).returns, ret.command = a := by
  obtain ⟨ret, hret, he⟩ := h
  have hm : a ∈ ((g.run.ledgerRun obj).state u).returned := List.mem_map.mpr ⟨ret, hret, he⟩
  exact List.mem_map.mp ((g.run.ledgerRun obj).returned_mono huv hm)

/-- **A command a process keeps holding is never answered.**  If `p`'s current
command is `a` from time `T` on, no response for `a` is recorded at any time:
it would still be recorded later, while `a` is current and hence pending. -/
theorem never_answered_of_current {p : Fin n} {a : WeakUniversal.Cmd n Op} {T : Nat}
    (hcur : ∀ t, T ≤ t →
      HelpingUniversal.Local.command obj ((g.run.state t).localState p) = some a) :
    ∀ t, ∀ ret ∈ (g.run.state t).returns, ret.command ≠ a := by
  intro t ret hret he
  obtain ⟨ret', hret', he'⟩ := g.answered_mono (Nat.le_max_left t T) ⟨ret, hret, he⟩
  exact (HelpingUniversal.identity_invariant obj (g.run.reachable obj (max t T))).active_pending
    p a (hcur _ (Nat.le_max_right _ _)) ret'.command (List.mem_map.mpr ⟨ret', hret', rfl⟩)
    (by rw [he'])

/-- **An announcement stays until it is answered.**  Once `M[q]` holds `a`, at
every later time it still does, or `a` has been answered. -/
theorem announcement_or_answered {q : Fin n} {a : WeakUniversal.Cmd n Op} {u : Nat}
    (hu : (g.run.state u).announcements q = some a) :
    ∀ v, u ≤ v → (g.run.state v).announcements q = some a ∨
      ∃ ret ∈ (g.run.state v).returns, ret.command = a := by
  intro v huv
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huv
  clear huv
  induction d with
  | zero => exact Or.inl hu
  | succ d ih =>
      rw [show u + (d + 1) = (u + d) + 1 from rfl]
      rcases ih with hm | hans
      · rcases g.run.next (u + d) with heq | hstep
        · left; rw [heq]; exact hm
        · rcases HelpingUniversal.step_announcement obj hstep q with hsame | hun
          · left; rw [hsame]; exact hm
          · right
            exact g.answered_mono (Nat.le_succ _)
              (HelpingUniversal.announcement_answered obj (g.run.reachable obj (u + d)) q a hm hun)
      · right; exact g.answered_mono (Nat.le_succ _) hans

/-- `M[q]` does not move while `q` is not scheduled. -/
theorem announcements_const_of_unscheduled {q : Fin n} {a b : Nat} (hab : a ≤ b)
    (hun : ∀ v, a ≤ v → v < b → g.actor v ≠ some q) :
    (g.run.state b).announcements q = (g.run.state a).announcements q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => rfl
  | succ d ih =>
      have hrest : ∀ v, a ≤ v → v < a + d → g.actor v ≠ some q :=
        fun v hv hvd => hun v hv (by omega)
      refine Eq.trans ?_ (ih (by omega) hrest)
      show (g.run.state ((a + d) + 1)).announcements q = _
      rcases g.step_actor (a + d) with ⟨-, heq⟩ | ⟨q', hq', hstep⟩ | ⟨q', r, -, -, heq⟩
      · rw [heq]
      · have hne : q ≠ q' := by
          intro h; exact hun (a + d) (by omega) (by omega) (h ▸ hq')
        exact HelpingUniversal.stepBy_announcement obj hstep q hne
      · rw [heq]

/-- **A command is written into `M` before it is answered.** -/
theorem announced_before_answer {t : Nat} {a : WeakUniversal.Cmd n Op}
    (h : ∃ ret ∈ (g.run.state t).returns, ret.command = a) :
    ∃ u, u < t ∧ (g.run.state u).announcements a.process = some a := by
  induction t with
  | zero =>
      obtain ⟨ret, hret, -⟩ := h
      rw [g.run.initial_state] at hret
      simp [HelpingUniversal.initial] at hret
  | succ t ih =>
      by_cases hprev : ∃ ret ∈ (g.run.state t).returns, ret.command = a
      · obtain ⟨u, hu, hm⟩ := ih hprev
        exact ⟨u, by omega, hm⟩
      · obtain ⟨ret, hret, he⟩ := h
        have hnot : ret ∉ (g.run.state t).returns := fun hm => hprev ⟨ret, hm, he⟩
        rcases g.run.next t with heq | hstep
        · rw [heq] at hret; exact absurd hret hnot
        · obtain ⟨p, seed, seen, hL⟩ := HelpingUniversal.step_new_return obj hstep hret hnot
          have hann := HelpingUniversal.announced obj (g.run.reachable obj t) p
          rw [hL] at hann
          simp only [HelpingUniversal.AnnouncedFor] at hann
          have hproc : ret.command.process = p :=
            ((HelpingUniversal.identity_invariant obj (g.run.reachable obj t)).active_tag p
              ret.command (by simp [HelpingUniversal.ledger, hL, HelpingUniversal.Local.command])).1
          refine ⟨t, by omega, ?_⟩
          rw [← he, hproc]
          exact hann

/-- **The helping collect gathers announced commands.**  Every command in the
list a process is assembling at Line 10 was read from `M`, at or before now. -/
theorem gathered_announced : ∀ (t : Nat) (p : Fin n) own seed todo commands,
    (g.run.state t).localState p = .gathering own seed todo commands →
    ∀ b ∈ commands, ∃ u, u ≤ t ∧ (g.run.state u).announcements b.process = some b := by
  intro t
  induction t with
  | zero =>
      intro p own seed todo commands h
      rw [g.run.initial_state] at h
      simp [HelpingUniversal.initial] at h
  | succ t ih =>
      intro p own seed todo commands h b hb
      rcases g.step_actor t with ⟨-, heq⟩ | ⟨q, -, hstep⟩ | ⟨q, r, -, -, heq⟩
      · rw [heq] at h
        obtain ⟨u, hu, hm⟩ := ih p own seed todo commands h b hb
        exact ⟨u, by omega, hm⟩
      · by_cases hqp : q = p
        · subst hqp
          rcases HelpingUniversal.stepBy_gathering_source obj hstep h with
            ⟨-, rfl⟩ | ⟨q0, commands0, hsrc, hobs⟩
          · exact absurd hb (by simp)
          · rw [hobs] at hb
            rcases HelpingUniversal.observe_mem obj seed _ commands0 b hb with hm | ⟨hann, -⟩
            · obtain ⟨u, hu, hm'⟩ := ih q own seed (q0 :: todo) commands0 hsrc b hm
              exact ⟨u, by omega, hm'⟩
            · have hproc : b.process = q0 :=
                HelpingUniversal.announcement_process obj (g.run.reachable obj t) q0 b hann
              exact ⟨t, by omega, by rw [hproc]; exact hann⟩
        · rw [hstep.2 p (fun e => hqp e.symm)] at h
          obtain ⟨u, hu, hm⟩ := ih p own seed todo commands h b hb
          exact ⟨u, by omega, hm⟩
      · rw [heq] at h
        obtain ⟨u, hu, hm⟩ := ih p own seed todo commands h b hb
        exact ⟨u, by omega, hm⟩

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- **Every command of a GCA input was written into `M`.**  By Lines 10–11 a
proposal is an output of the previous round extended by commands read from
`M`; GCA Validity carries an occurrence in the output back to an input of the
round before, until the collect that read it from `M` is reached. -/
theorem input_announced : ∀ r (q : Fin n) (s : (WeakUniversal.Tagged (n := n) obj).Trace),
    (H (r + 1)).input q = some s →
    ∀ b, 0 < (WeakUniversal.Tagged obj).traceCount b s →
      ∃ u, (g.run.state u).announcements b.process = some b := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro q s hin b hb
    obtain ⟨t', hcall⟩ := (g.input_iff_call r q s).mp hin
    have hnew : (⟨r + 1, q, s⟩ : WeakUniversal.Call (n := n) obj) ∉ (g.run.state 0).calls := by
      rw [g.run.initial_state]; simp [HelpingUniversal.initial]
    obtain ⟨v, -, cmd, seed, commands, arranged, hsrc, harr, hr, htr⟩ :=
      g.call_was_gathering_after hcall hnew
    have hs : s = HelpingUniversal.proposal obj seed arranged := htr
    rw [hs, HelpingUniversal.proposal_count_perm obj b seed harr,
      HelpingUniversal.proposal_count] at hb
    by_cases hc : 0 < commands.count b
    · obtain ⟨u, -, hm⟩ :=
        g.gathered_announced v q cmd seed [] commands hsrc b (List.count_pos_iff.mp hc)
      exact ⟨u, hm⟩
    · have hbase : 0 < (WeakUniversal.Tagged obj).traceCount b seed.trace := by omega
      have hsup := (HelpingUniversal.invariant obj (g.run.reachable obj v)).localState q
      rw [hsrc] at hsup
      rcases hsup with ⟨-, hempty⟩ | ⟨hpos, q', flag, hq'⟩
      · rw [hempty] at hbase
        change 0 < ([] : List (WeakUniversal.Cmd n Op)).count b at hbase
        simp at hbase
      · have hseed : seed.round = r := by
          have : r + 1 = seed.round + 1 := hr
          omega
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        rw [hseed] at hq'
        have hocc : GCA.History.Occurs (obj := WeakUniversal.Tagged (n := n) obj) b 0
            seed.trace := by
          simpa only [GCA.History.Occurs,
            (WeakUniversal.Tagged obj).traceResponses_length] using hbase
        obtain ⟨s', ⟨q'', hin'⟩, hsocc⟩ :=
          (g.gca.spec r').validity.occurs q' seed.trace flag hq' b 0 hocc
        have hspos : 0 < (WeakUniversal.Tagged obj).traceCount b s' := by
          simpa only [GCA.History.Occurs,
            (WeakUniversal.Tagged obj).traceResponses_length] using hsocc
        exact ih r' (by omega) q'' s' hin' b hspos


end HelpingGCA

namespace HelpingRun
variable (g : HelpingRun obj H)

/-- A command written into `M` and not answered by `T` is pending, in §7's
sense, at some time at or after `T`: at `T` itself if it was written by then,
and otherwise at the moment it is written. -/
theorem pendingAfter_witness {T : Nat} {b : WeakUniversal.Cmd n Op}
    (hann : ∃ u, (g.run.state u).announcements b.process = some b)
    (hno : ∀ ret ∈ (g.run.state T).returns, ret.command ≠ b) :
    ∃ t, T ≤ t ∧ g.AnnouncedBy t b ∧ ∀ ret ∈ (g.run.state t).returns, ret.command ≠ b := by
  classical
  obtain ⟨v, hv, hmin⟩ := exists_least _ hann
  rcases Nat.le_total v T with hle | hge
  · exact ⟨T, Nat.le_refl _, ⟨v, hle, hv⟩, hno⟩
  · refine ⟨v, hge, ⟨v, Nat.le_refl _, hv⟩, fun ret hret he => ?_⟩
    obtain ⟨u, hu, hm⟩ := g.announced_before_answer ⟨ret, hret, he⟩
    exact absurd (hmin u hm) (by omega)

/-! ## The argument inside one run -/

/-- **The manuscript's hypothesis of `th:cr`, on the run.**  "Eventually
`α`-conflict-free", for the prefix `α` of the first `N` steps, with §7's point
of invocation: beyond `T₀`, two distinct commands that are both pending —
written into `M` and not yet answered — and both invoked after `α` — not written
into `M` within its first `N` steps — do not conflict. -/
def EventuallyNonconflictingAfter (N T₀ : Nat) : Prop :=
  ∀ t, T₀ ≤ t → ∀ a b : WeakUniversal.Cmd n Op, a ≠ b →
    g.AnnouncedBy t a → (∀ ret ∈ (g.run.state t).returns, ret.command ≠ a) →
    g.AnnouncedBy t b → (∀ ret ∈ (g.run.state t).returns, ret.command ≠ b) →
    ¬ g.AnnouncedBy N a → ¬ g.AnnouncedBy N b →
    (WeakUniversal.Tagged obj).Independent a b

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- **`th:cr`, inside one run.**  Suppose that at time `N`

* a register `S[j]` holds a round `≥ rc + 1`, where some process committed the
  trace `sc` at round `rc + 1` ("`(r₁, s')` is written in `S`"), and
* every command written into `M` by `N` occurs in `sc` ("every operation
  instance invoked before the end of `α'` has its associated command in
  `ops(s')`").

If beyond some time no two pending commands invoked after `N` conflict, then
every operation of every process that keeps taking steps completes.

This is the rest of the manuscript's proof.  A forever-pending command `a` of
such a process is not written into `M` by `N`, since otherwise it occurs in `sc`
and the next final `S` collect finds it.  Invariant (II) holds above the rounds
reached once `a` is announced: residual commands miss the common prefix, which
contains `sc` (`lemma:prefix-rounds`), so they are invoked after `N`, pending at a
common late time with `a`, and independent of it.  A commit above the bound is
written into `S`, and every trace `i` reads from `S` afterwards is committed
above the bound, so contains `a` by (II) and completes it: there is no such
commit.  So residual commands never complete, and invariant (I) follows the same
way; Commitment at a round `i` waits on then yields a commit above the bound, a
contradiction. -/
theorem resolving_completes {N rc : Nat} {qc : Fin n} {sc : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hcom : (H (rc + 1)).output qc = some (sc, true))
    {j : Fin n} (hslot : rc + 1 ≤ ((g.run.state N).slots j).round)
    (hcover : ∀ a, g.AnnouncedBy N a → 0 < (WeakUniversal.Tagged obj).traceCount a sc)
    {T₀ : Nat} (hC : g.EventuallyNonconflictingAfter N T₀)
    {i : Fin n} (hi : ∀ M, ∃ t, M ≤ t ∧ g.actor t = some i)
    {a : WeakUniversal.Cmd n Op} (hinv : g.Invoked a) (hproc : a.process = i) :
    g.Completes a := by
  classical
  have coverage := g.callsCovered
  apply Classical.byContradiction
  intro hnr
  obtain ⟨τ₀, hτ₀⟩ := g.invoked_command hinv
  rw [hproc] at hτ₀
  have hcmd := g.command_persists hτ₀ hnr
  have hslotR : ∀ t, N ≤ t → rc + 1 ≤ ((g.run.state t).slots j).round :=
    fun t ht => Nat.le_trans hslot (g.slots_mono ht)
  -- a command that never completes is answered at no time
  have hnotAnswered : ∀ c, ¬ g.Completes c →
      ∀ t, ∀ ret ∈ (g.run.state t).returns, ret.command ≠ c :=
    fun c hc t ret hret he => hc ⟨t, ret.round, ret.trace, by rw [← he]; exact hret⟩
  -- "from what precedes, `Φ` is invoked after `α'`"
  have hnotN : ¬ g.AnnouncedBy N a := fun hann =>
    hnr (g.completes_of_slot coverage hi hcmd hslotR hcom (Nat.le_refl _)
      (hcover a hann))
  have hnoAt : ∀ u, τ₀ ≤ u →
      ¬ HelpingUniversal.AtReturn obj ((g.run.state u).localState i) := by
    intro u hu hat
    obtain ⟨cmd, hc, hcomp⟩ := g.atReturn_completes hi hat
    exact hnr ((Option.some.inj (hc.symm.trans (hcmd u hu))) ▸ hcomp)
  -- `i` reaches a proposal, so it has written `a` into `M[i]`, for good
  rcases g.reaches_waiting_or_return hi _ τ₀ (Nat.le_refl _) with
    ⟨u0, hu0, hat⟩ | ⟨τ₁, hτ₁, cmd₁, r₁, prop₁, hL₁, -⟩
  · exact absurd hat (hnoAt u0 hu0)
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
  -- the manuscript's `r₂`: every round reached by `τ₁` is at most `B`
  obtain ⟨B, hB⟩ := WeakUniversal.calls_round_bound obj (g.run.state τ₁).calls
  have hbound : ∀ p, HelpingUniversal.localRound obj
      ((g.run.state τ₁).localState p) ≤ B := by
    intro p
    rcases (HelpingUniversal.roundsCalled obj (g.run.reachable obj τ₁)).2 p with
      h0 | ⟨call, hmem, he⟩
    · omega
    · rw [← he]; exact hB call hmem
  obtain ⟨Bc, hBc⟩ := g.eventually_callers_stepping
  let T := max τ₁ T₀
  have hT1 : τ₁ ≤ T := Nat.le_max_left _ _
  have hT2 : T₀ ≤ T := Nat.le_max_right _ _
  obtain ⟨Br, hBr⟩ := WeakUniversal.returns_round_bound obj (g.run.state T).returns
  have haT : g.AnnouncedBy T a := ⟨τ₁, hT1, by rw [hproc]; exact hann₁⟩
  let K := max (max (max (B + 1) Br) Bc) rc
  have hK1 : B + 1 ≤ K := by omega
  have hK2 : Br ≤ K := by omega
  have hK3 : Bc ≤ K := by omega
  have hK4 : rc ≤ K := by omega
  -- a command missing from `sc` was invoked after `N`
  have hresN : ∀ b, (WeakUniversal.Tagged obj).traceCount b sc = 0 → ¬ g.AnnouncedBy N b :=
    fun b hbsc hbann => by have := hcover b hbann; omega
  -- the checkpoint lies below the common prefix of the traces retrieved at every high round
  have hsc_glb : ∀ m, K ≤ m → ∀ t,
      (WeakUniversal.Tagged obj).IsGLB (g.Retrieved m) t →
      (WeakUniversal.Tagged obj).TracePrefix sc t :=
    fun m hm t ht => HelpingUniversal.committed_below_glb obj coverage (g.gca.spec)
      ⟨Nat.succ_pos rc, qc, hcom⟩ (by omega) (fun x hx => g.retrieved_output hx) ht
  -- `a` commutes with every residual command of a high round
  have hindep : ∀ m, K ≤ m →
      ∀ t, (WeakUniversal.Tagged obj).IsGLB (g.Retrieved m) t →
      ∀ s, (H (m + 2)).Inputs s → ∀ b, g.Pending m b →
        (WeakUniversal.Tagged obj).traceCount b t = 0 →
        0 < (WeakUniversal.Tagged obj).traceCount b s →
        a ≠ b → (WeakUniversal.Tagged obj).Independent a b := by
    intro m hm t ht s hs b hb hbt hbs hab
    have hnob : ∀ ret ∈ (g.run.state T).returns, ret.command ≠ b := by
      intro ret hret he
      exact hb.2 ⟨T, ret, hret, he, Nat.le_trans (hBr ret hret) (by omega)⟩
    have hbsc : (WeakUniversal.Tagged obj).traceCount b sc = 0 := by
      have := (WeakUniversal.Tagged obj).traceCount_mono (hsc_glb m hm t ht) b
      omega
    have hbN : ¬ g.AnnouncedBy N b := hresN b hbsc
    obtain ⟨sq, hsq⟩ := hs
    obtain ⟨t', ht', hbA, hbno⟩ :=
      g.pendingAfter_witness (g.input_announced (m + 1) sq s hsq b hbs) hnob
    exact hC t' (by omega) a b hab (g.announcedBy_mono (by omega) haT)
      (hnotAnswered a hnr t') hbA hbno hnotN hbN
  -- invariant (II)
  have hII : ∀ m, K ≤ m → ∀ y, (H (m + 2)).Outputs y →
      0 < (WeakUniversal.Tagged obj).traceCount a y :=
    fun m hm y hy => g.output_contains_own_of coverage hann hbound hB (hindep m hm)
      (by omega) hy
  -- no commit above the bound: its author writes it into `S`, and every trace
  -- `i` then reads from `S` is committed above the bound, so contains `a` by (II)
  have hnocommit : ∀ m, K ≤ m →
      ∀ q y, (H (m + 2)).output q ≠ some (y, true) := by
    intro m hm q y hout
    obtain ⟨w₀, hslotq⟩ := g.commit_published (hBc m (by omega)) hout
    refine hnr (g.completes_of_high_slot hi hcmd (by omega) hslotq fun k' hk' q' y' hy' => ?_)
    obtain ⟨m', rfl⟩ : ∃ m', k' = m' + 1 := ⟨k' - 1, by omega⟩
    exact hII m' (by omega) y' ⟨q', true, hy'⟩
  -- hence every recorded response was committed at most at round `K + 1`
  have hretlow : ∀ t (ret : WeakUniversal.Return (n := n) obj),
      ret ∈ (g.run.state t).returns → ret.round ≤ K + 1 := by
    intro t ret hret
    obtain ⟨hcom', -⟩ :=
      (HelpingUniversal.invariant obj (g.run.reachable obj t)).returns ret hret
    obtain ⟨hpos, q, hq⟩ := hcom'
    refine Nat.le_of_not_lt (fun hlt => ?_)
    obtain ⟨m, hm⟩ : ∃ m, ret.round = m + 2 := ⟨ret.round - 2, by omega⟩
    rw [hm] at hq
    exact hnocommit m (by omega) q ret.trace hq
  -- a residual command never completes
  have hnever : ∀ k, K ≤ k → ∀ c, g.Pending k c → ¬ g.Completes c := by
    rintro k hk c hc ⟨t, r, s, hmem⟩
    exact hc.2 ⟨t, ⟨c, r, s⟩, hmem, rfl,
      Nat.le_trans (hretlow t ⟨c, r, s⟩ hmem) (by omega)⟩
  -- invariant (I)
  have hI : ∀ k, K ≤ k → (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs := by
    intro k hk
    by_cases hcaller : ∃ s, (H (k + 2)).Inputs s
    · obtain ⟨t, ht⟩ :=
        (WeakUniversal.Tagged obj).glb_exists _ (g.retrieved_nonempty hcaller)
      have hsct := hsc_glb k hk t ht
      refine g.inputs_compatible_res coverage ht
        (C := fun b => ¬ g.Completes b ∧ (WeakUniversal.Tagged obj).traceCount b sc = 0 ∧
          ∃ u, (g.run.state u).announcements b.process = some b) ?_ ?_
      · rintro b b' ⟨hbn, hbsc, ub, hub⟩ ⟨hbn', hbsc', ub', hub'⟩ hbb'
        refine hC (max T₀ (max ub ub')) (Nat.le_max_left _ _) b b' hbb'
          ⟨ub, by omega, hub⟩ (hnotAnswered b hbn _) ⟨ub', by omega, hub'⟩
          (hnotAnswered b' hbn' _) ?_ ?_
        · exact hresN b hbsc
        · exact hresN b' hbsc'
      · intro s hs b hb hbt hbs
        obtain ⟨sq, hsq⟩ := hs
        refine ⟨hnever k hk b hb, ?_, g.input_announced (k + 1) sq s hsq b hbs⟩
        have := (WeakUniversal.Tagged obj).traceCount_mono hsct b
        omega
    · exact ⟨(WeakUniversal.Tagged obj).emptyTrace, fun s hs => absurd ⟨s, hs⟩ hcaller⟩
  -- "By Invariant (I), all proposals to `GCA_{r₂+1}` are compatible. … `j` is one of
  -- them since it never leaves its loop.  By GCA Commitment, some process thus
  -- commits": `i` waits on a round above the bound, where somebody commits
  rcases g.atReturn_or_rounds_unbounded_from hi τ₁ with ⟨u1, hu1, hat⟩ | hunb
  · exact hnoAt u1 (by omega) hat
  obtain ⟨t2, ht2, ht2K⟩ := hunb (K + 1)
  rcases g.reaches_waiting_or_return hi _ t2 (Nat.le_refl _) with
    ⟨u2, hu2, hat⟩ | ⟨u3, hu3, cmd₃, R, prop₃, hL₃, hR⟩
  · exact hnoAt u2 (by omega) hat
  obtain ⟨k, rfl⟩ : ∃ k, R = k + 2 := ⟨R - 2, by omega⟩
  obtain ⟨hcall₃, -⟩ :=
    HelpingUniversal.waiting_call obj (g.run.reachable obj u3) i cmd₃ (k + 2) prop₃ hL₃
  have hin₃ : (H (k + 2)).input i = some prop₃ := by
    simpa using HelpingUniversal.call_input obj (g.run.reachable obj u3) _ hcall₃
  obtain ⟨q, -, x, -, houtq, -⟩ :=
    g.exists_commit_of_compatible (hI k (by omega)) ⟨prop₃, i, hin₃⟩ (hBc k (by omega))
  exact hnocommit k (by omega) q x houtq

end HelpingGCA
end ConflictFreedom.GlobalSchedule

/-! ## The solo phase

Facts about a process that runs alone, used to build the solo extension. -/

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best Supported
  Committed Stored CallInvariant eq_of_update_ne apply_eq_of_update_ne)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- From a finished final collect a process either retries or returns; both
leave it heading for the next round. -/
theorem stepBy_from_check_end {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {seed seen : Seed (n := n) obj}
    (hc : c.localState p = .checking cmd seed [] seen) :
    (∃ order : List (Fin n), order.Perm (List.finRange n) ∧
      d.localState p = .gathering cmd seed order []) ∨
      d.localState p = .idle seed := by
  cases h.1 with
  | retry q cmd' seed' seen' hq hmiss order horder =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, -, rfl⟩ := Local.checking.inj (hq.symm.trans hc)
      exact Or.inl ⟨order, horder, by simp [update]⟩
  | finish q cmd' seed' seen' hq hcont =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, -, rfl⟩ := Local.checking.inj (hq.symm.trans hc)
      exact Or.inr (by simp [update])
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- **Unconditional local progress.**  Counting `finish` as round progress,
every step either advances the round a process heads for or strictly decreases
its rank inside that round. -/
theorem stepBy_progress_strong {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) :
    nextRound obj (c.localState p) < nextRound obj (d.localState p) ∨
    (nextRound obj (c.localState p) = nextRound obj (d.localState p) ∧
      rank obj (d.localState p) < rank obj (c.localState p)) := by
  rcases stepBy_progress obj h with hat | h'
  · obtain ⟨cmd, seed, seen, hL, hcount⟩ := hat
    left
    rcases stepBy_from_check_end obj h hL with ⟨order, -, hg⟩ | hi
    · rw [hL, hg]; simp [nextRound]
    · rw [hL, hi]; simp [nextRound]
  · exact h'

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingGCA
variable (g : HelpingGCA obj H)

private def mu2 (g : HelpingGCA obj H) (p : Fin n) (B t : Nat) : Nat :=
  (B - HelpingUniversal.nextRound obj ((g.run.state t).localState p)) * (3 * n + 6 + 1)
    + HelpingUniversal.rank obj ((g.run.state t).localState p)

/-- **A process that keeps stepping reaches arbitrarily large rounds.** -/
theorem rounds_unbounded_from {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (T B : Nat) :
    ∃ t, T ≤ t ∧ B < HelpingUniversal.nextRound obj ((g.run.state t).localState p) := by
  classical
  apply Classical.byContradiction
  intro hcon
  have hbound : ∀ t, T ≤ t →
      HelpingUniversal.nextRound obj ((g.run.state t).localState p) ≤ B :=
    fun t ht => Nat.le_of_not_lt (fun h => hcon ⟨t, ht, h⟩)
  have hrankle : ∀ t, HelpingUniversal.rank obj ((g.run.state t).localState p) ≤ 3 * n + 6 :=
    fun t => HelpingUniversal.rank_le obj
      (HelpingUniversal.todo_bound obj (g.run.reachable obj t)) p
  have hdec : ∀ t, T ≤ t → HelpingUniversal.StepBy obj (H) p
      (g.run.state t) (g.run.state (t + 1)) → mu2 g p B (t + 1) < mu2 g p B t := by
    intro t ht hs
    rcases HelpingUniversal.stepBy_progress_strong obj hs with hlt | ⟨heq, hrk⟩
    · have h1 : (B - HelpingUniversal.nextRound obj ((g.run.state (t + 1)).localState p)) + 1
            ≤ B - HelpingUniversal.nextRound obj ((g.run.state t).localState p) := by
        have := hbound (t + 1) (by omega); have := hbound t ht; omega
      have h2 := Nat.mul_le_mul_right (3 * n + 6 + 1) h1
      rw [Nat.succ_mul] at h2
      have h3 := hrankle (t + 1)
      simp only [mu2]
      omega
    · simp only [mu2, heq]
      omega
  have hmono : ∀ t, T ≤ t → mu2 g p B (t + 1) ≤ mu2 g p B t := by
    intro t ht
    by_cases hs : HelpingUniversal.StepBy obj (H) p
        (g.run.state t) (g.run.state (t + 1))
    · exact Nat.le_of_lt (hdec t ht hs)
    · simp only [mu2, g.localState_stable_of_no_step hs]
      exact Nat.le_refl _
  refine no_infinite_decrease (μ := fun t => mu2 g p B (T + t)) (fun t => ?_) (fun N => ?_)
  · exact hmono (T + t) (by omega)
  · obtain ⟨t, ht, hs⟩ := g.steps_infinitely hsched (T + N)
    refine ⟨t - T, by omega, ?_⟩
    rw [show T + (t - T) = t by omega, show T + (t - T + 1) = t + 1 by omega]
    exact hdec t (by omega) hs

/-- **A process that keeps stepping always reaches a proposal.**  The
`AtReturn` escape of `reaches_waiting_or_return` is not needed: a `finish`
leads to `idle`, from which the process invokes and collects again. -/
theorem reaches_waiting_always {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) (t : Nat) :
    ∃ u, t ≤ u ∧ ∃ cmd r proposal,
      (g.run.state u).localState p = .waiting cmd r proposal ∧
        HelpingUniversal.nextRound obj ((g.run.state t).localState p) ≤ r := by
  classical
  rcases g.reaches_waiting_or_return hsched _ t (Nat.le_refl _) with
    ⟨u, hu, hat⟩ | hres
  · obtain ⟨cmd, seed, seen, hL, hcount⟩ := hat
    obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched u
    have hnext := HelpingUniversal.stepBy_from_check_end obj hstep (hconst.trans hL)
    have hrank : HelpingUniversal.nextRound obj ((g.run.state t).localState p)
        ≤ seed.round := by
      have hmono : HelpingUniversal.nextRound obj ((g.run.state t).localState p)
          ≤ HelpingUniversal.nextRound obj ((g.run.state u).localState p) := by
        clear hL hcount hnext hconst hstep hv
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
        clear hu
        induction d with
        | zero => exact Nat.le_refl _
        | succ d ih =>
            refine Nat.le_trans ih ?_
            show HelpingUniversal.nextRound obj ((g.run.state (t + d)).localState p)
              ≤ HelpingUniversal.nextRound obj ((g.run.state ((t + d) + 1)).localState p)
            rcases g.step_actor (t + d) with ⟨-, heq⟩ | ⟨q, -, hs⟩ | ⟨q, r, -, -, heq⟩
            · rw [heq]; exact Nat.le_refl _
            · by_cases hqp : q = p
              · subst hqp
                rcases HelpingUniversal.stepBy_progress_strong obj hs with h1 | ⟨h1, -⟩
                · omega
                · omega
              · rw [hs.2 p (fun e => hqp e.symm)]; exact Nat.le_refl _
            · rw [heq]; exact Nat.le_refl _
      rw [hL] at hmono
      simpa only [HelpingUniversal.nextRound] using hmono
    have hge : n + 3 ≤ HelpingUniversal.rank obj ((g.run.state (v + 1)).localState p) := by
      rcases hnext with ⟨order, horder, hg⟩ | hi
      · rw [hg]; simp only [HelpingUniversal.rank, horder.length_eq, List.length_finRange]; omega
      · rw [hi]; simp only [HelpingUniversal.rank]; omega
    have hnr : HelpingUniversal.nextRound obj ((g.run.state (v + 1)).localState p)
        = seed.round + 1 := by
      rcases hnext with ⟨order, -, hg⟩ | hi
      · rw [hg]; rfl
      · rw [hi]; rfl
    obtain ⟨w, hw2, cmd', r, prop, hLw, hr⟩ :=
      g.reaches_waiting hsched _ (v + 1) (Nat.le_refl _) hge
    exact ⟨w, by omega, cmd', r, prop, hLw, by omega⟩
  · exact hres

end HelpingGCA
end ConflictFreedom.GlobalSchedule

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingRun
variable (g : HelpingRun obj H)

/-- While only `p` is scheduled, no other process's announcement changes. -/
theorem announcements_const_of_solo {N : Nat} {p : Fin n}
    (hsolo : g.SoloFrom N p) {q : Fin n} (hq : q ≠ p) :
    ∀ t, N ≤ t →
      (g.run.state t).announcements q = (g.run.state N).announcements q := by
  intro t ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction d with
  | zero => rfl
  | succ d ih =>
      show (g.run.state ((N + d) + 1)).announcements q = _
      rcases g.step_or_frozen hsolo (show N ≤ N + d by omega) with hstep | heq
      · rw [HelpingUniversal.stepBy_announcement obj hstep q hq]; exact ih
      · rw [heq]; exact ih

end HelpingRun
end ConflictFreedom.GlobalSchedule

/-! ## Steps used by the solo extension and by the checks on the definitions -/

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best Supported
  Committed Stored CallInvariant eq_of_update_ne apply_eq_of_update_ne)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

omit [DecidableEq Op] in
/-- The round a process heads for is at most one past the round it carries. -/
theorem nextRound_le_localRound (l : Local (n := n) obj) :
    nextRound obj l ≤ localRound obj l + 1 := by
  cases l <;> simp [nextRound, localRound]

/-- From a finished final collect whose trace contains the command, the step is
the return (Line 19): the process becomes idle on its local base, the registers
are unchanged, and the response is recorded. -/
theorem stepBy_finish {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {seed seen : Seed (n := n) obj}
    (hc : c.localState p = .checking cmd seed [] seen)
    (hcount : 0 < (Tagged obj).traceCount cmd seen.trace) :
    d.localState p = .idle seed ∧ d.slots = c.slots ∧
      (⟨cmd, seen.round, seen.trace⟩ : Return (n := n) obj) ∈ d.returns := by
  cases h.1 with
  | finish q cmd' seed' seen' hq hcont =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, rfl, -, rfl⟩ := Local.checking.inj (hq.symm.trans hc)
      exact ⟨by simp [update], rfl, List.mem_cons_self ..⟩
  | retry q cmd' seed' seen' hq hmiss =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, -, -, rfl⟩ := Local.checking.inj (hq.symm.trans hc)
      omega
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- From `announcing`, the step is Line 5: the command is written into `M`. -/
theorem stepBy_announce {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {cmd : Cmd n Op} {seed : Seed (n := n) obj}
    (hc : c.localState p = .announcing cmd seed) : d.announcements p = some cmd := by
  cases h.1 with
  | announce q cmd' seed' hq =>
      obtain rfl := eq_of_update_ne h.moves
      obtain ⟨rfl, -⟩ := Local.announcing.inj (hq.symm.trans hc)
      simp [update]
  -- no other step starts from this local state
  | _ => exact absurd (apply_eq_of_update_ne h.moves ‹_›) (by simp [hc])

/-- A step that writes a new command into `M[q]` is `q`'s own Line 5, taken
from `announcing` that command. -/
theorem stepBy_announcement_change {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d) {q : Fin n}
    {a : Cmd n Op} (hne : c.announcements q ≠ some a) (hd : d.announcements q = some a) :
    p = q ∧ ∃ seed, c.localState q = .announcing a seed := by
  cases h.1 with
  | announce p' cmd seed hp =>
      obtain rfl := eq_of_update_ne h.moves
      by_cases hqp : q = p'
      · subst hqp
        have hca : cmd = a := by simpa [update] using hd
        subst hca
        exact ⟨rfl, seed, hp⟩
      · exact absurd (by simpa [update, hqp] using hd) hne
  | _ => exact absurd hd hne

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingRun
variable (g : HelpingRun obj H)

/-- **A commit, read off the step that publishes it.**  If `i` goes from
waiting on round `R` to publishing `⟨R, x⟩`, it received `(x, true)` from
round `R`. -/
theorem committed_of_publishing {v R : Nat} {i : Fin n} {cmd : WeakUniversal.Cmd n Op}
    {prop x : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hwait : (g.run.state v).localState i = .waiting cmd R prop)
    (hpub : (g.run.state (v + 1)).localState i = .publishing cmd ⟨R, x⟩) :
    (H R).output i = some (x, true) := by
  rcases g.step_actor v with ⟨-, heq⟩ | ⟨q, -, hstep⟩ | ⟨q, r, -, -, heq⟩
  · rw [heq, hwait] at hpub; cases hpub
  · by_cases hqi : q = i
    · subst hqi
      obtain ⟨s, flag, hout, order, -, hnew⟩ := HelpingUniversal.stepBy_from_waiting obj hstep hwait
      rw [hpub] at hnew
      by_cases hf : flag = true
      · simp only [hf, ↓reduceIte] at hnew
        injection hnew with _ e2
        injection e2 with _ e4
        rw [hout, e4, hf]
      · simp [hf] at hnew
    · rw [hstep.2 i (fun e => hqi e.symm), hwait] at hpub; cases hpub
  · rw [heq, hwait] at hpub; cases hpub

/-- **A process has at most one pending command**, with §7's point of
invocation: two commands of one process, both written into `M` and neither
answered at time `t`, are the same. -/
theorem announced_pending_unique {t : Nat} {a b : WeakUniversal.Cmd n Op}
    (ha : g.AnnouncedBy t a) (har : ∀ ret ∈ (g.run.state t).returns, ret.command ≠ a)
    (hb : g.AnnouncedBy t b) (hbr : ∀ ret ∈ (g.run.state t).returns, ret.command ≠ b)
    (hab : a.process = b.process) : a = b := by
  obtain ⟨u, hu, hmu⟩ := ha
  obtain ⟨v, hv, hmv⟩ := hb
  have hat : (g.run.state t).announcements a.process = some a := by
    rcases g.announcement_or_answered hmu t hu with h | ⟨ret, hret, he⟩
    · exact h
    · exact absurd he (har ret hret)
  have hbt : (g.run.state t).announcements b.process = some b := by
    rcases g.announcement_or_answered hmv t hv with h | ⟨ret, hret, he⟩
    · exact h
    · exact absurd he (hbr ret hret)
  rw [hab, hbt] at hat
  exact (Option.some.inj hat).symm

/-- **§7's point of invocation is the instance's first operation step.**  In
the extracted §3 execution, an instance takes its first operation step when its
process writes its command into `M` (Line 5): the command has been written into
`M` by time `N` exactly when the instance took an operation step at an operation
time `t` with `t + 1 < N` — operation time `t` being the run's step `t + 1`. -/
theorem announcedBy_iff_step (hp : g.OpLive) (j : (g.execution hp).Instance) (N : Nat) :
    g.AnnouncedBy N j.val ↔ ∃ t, t + 1 < N ∧ (g.execution hp).actor t = some j := by
  classical
  constructor
  · intro hann
    obtain ⟨u, hu, hm⟩ := hann
    obtain ⟨w, ⟨hwN, hw⟩, hmin⟩ := exists_least
      (fun w => w ≤ N ∧ (g.run.state w).announcements j.val.process = some j.val) ⟨u, hu, hm⟩
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := by
      refine ⟨w - 1, ?_⟩
      rcases Nat.eq_zero_or_pos w with h0 | hpos
      · subst h0
        rw [g.run.initial_state] at hw
        simp [HelpingUniversal.initial] at hw
      · omega
    have hne : (g.run.state w').announcements j.val.process ≠ some j.val :=
      fun h => absurd (hmin w' ⟨by omega, h⟩) (by omega)
    rcases g.step_actor w' with ⟨-, heq⟩ | ⟨q, hq, hstep⟩ | ⟨q, r, -, -, heq⟩
    · rw [heq] at hw; exact absurd hw hne
    · obtain ⟨rfl, seed, hL⟩ := HelpingUniversal.stepBy_announcement_change obj hstep hne hw
      obtain ⟨t, rfl⟩ : ∃ t, w' = t + 1 := by
        refine ⟨w' - 1, ?_⟩
        rcases Nat.eq_zero_or_pos w' with h0 | hpos
        · subst h0
          rw [g.run.initial_state] at hL
          simp [HelpingUniversal.initial] at hL
        · omega
      have hop : g.opActor t = some j.val := by
        rw [HelpingRun.opActor, hq]
        show HelpingUniversal.Local.command obj ((g.run.state (t + 1)).localState _) = _
        rw [hL]; rfl
      obtain ⟨i', hi', hval⟩ := (g.schedule hp).actorInst_of_actor hop
      have : i' = j := Subtype.ext hval
      subst this
      exact ⟨t, by omega, hi'⟩
    · rw [heq] at hw; exact absurd hw hne
  · rintro ⟨t, ht, hact⟩
    have hsch := (g.schedule hp).actorInst_val hact
    obtain ⟨q, hq, hactive⟩ := g.opActor_eq_some hsch
    have htag := ((HelpingUniversal.identity_invariant obj
      (g.run.reachable obj (t + 1))).active_tag q j.val hactive).1
    subst htag
    have hcmd : HelpingUniversal.Local.command obj
        ((g.run.state (t + 1)).localState j.val.process) = some j.val := hactive
    have hA := HelpingUniversal.announced obj (g.run.reachable obj (t + 1)) j.val.process
    cases hL : (g.run.state (t + 1)).localState j.val.process with
    | idle seed => rw [hL] at hcmd; cases hcmd
    | announcing cmd seed =>
        have hcj : cmd = j.val := by
          rw [hL] at hcmd; exact Option.some.inj hcmd
        subst hcj
        rcases g.step_actor (t + 1) with ⟨hnone, -⟩ | ⟨q', hq', hstep⟩ | ⟨q', r, hq', hr, -⟩
        · rw [hq] at hnone; cases hnone
        · have hqq : q' = j.val.process := Option.some.inj (hq'.symm.trans hq)
          subst hqq
          exact ⟨t + 2, by omega, HelpingUniversal.stepBy_announce obj hstep hL⟩
        · have hqq : q' = j.val.process := Option.some.inj (hq'.symm.trans hq)
          subst hqq
          rw [hL] at hr; cases hr
    | collecting _ _ _ | gathering _ _ _ _ | waiting _ _ _ | publishing _ _ | checking _ _ _ _ =>
        rw [hL] at hA hcmd
        exact ⟨t + 1, by omega, by rw [hA]; exact hcmd⟩

end HelpingRun
end ConflictFreedom.GlobalSchedule
