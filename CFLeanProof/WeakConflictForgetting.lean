import CFLeanProof.UniversalLiveness
import CFLeanProof.GCASoloAgreement

/-!
# `th:WeakUCresolve`: a solo checkpoint round makes Algorithm 1 forget conflicts

This module is the progress half of `th:WeakUCresolve`, proved inside one
global schedule (`GlobalSchedule.Weak`).  `WeakUCResolve.lean` builds the finite
solo extension on the forward machine and quantifies over its extensions.

The manuscript's proof has three ingredients once `i` has run a round `r*` alone
and committed its trace `s` there.

1. **Solo agreement** (GCA property 7).  Every process that returns from
   `GCA_{r*}`, in any extension, returns `s` — even though later processes may
   join `GCA_{r*}` with other inputs.  `solo_round_outputs` derives this for the
   run's own rounds from `GCA.Protocol.soloAgreement` (Lemma `GCA_soloagg`):
   before `i` returns, nobody else has taken a step of that round.
   `solo_checkpoint` packages it with `i`'s commit.
2. **The descent** (`origin_after`).  Every command of an output of a round
   `r̂ ≥ r*` either occurs in `s` or was appended at Line 8 by its own process
   when proposing to a round above `r*`, after the checkpoint (`ActiveAfter`).
   The base case is Solo agreement; the step is GCA Validity with Lines 4–9.
3. **Invariant (I)** (`inputs_compatible_after`).  A command in a residual
   `u_j` does not occur in the common prefix `t`, which contains `s` by
   `lemma:prefix-rounds`; so by the descent it belongs to an instance that took
   a step after the checkpoint, and those do not conflict.

`forgetting_completes` assembles them into the contradiction of
`theorem:weakUCWCF`: some process that takes infinitely many steps completes
every operation it invokes.  Its hypothesis is the manuscript's own, carried to
the program run: beyond some time, two pending commands **that take steps after
the checkpoint** do not conflict (`EventuallyWeaklyNonconflicting`).

Assuming instead that *every input* to the checkpoint round equals `s` would
not do: it holds in `α'` but not in its extensions, where a process
mid-operation at the end of `α'` may still propose to `GCA_{r*}`.  Solo
agreement, a property of the GCA implementation, is what fixes the checkpoint
round's outputs in every extension.
-/

namespace ConflictFreedom.WeakUniversal
open Object
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

/-- Appending a missing command does not change any other command's count. -/
theorem appendMissing_count_ne (s : (Tagged (n := n) obj).Trace) (a cmd : Cmd n Op)
    (hne : a ≠ cmd) :
    (Tagged obj).traceCount a ((Tagged obj).appendMissing s cmd)
      = (Tagged obj).traceCount a s := by
  classical
  unfold Object.appendMissing
  split
  · rw [(Tagged obj).traceCount_append a s
      (Quotient.mk (Tagged obj).traceSetoid [cmd])]
    have : (Tagged obj).traceCount a
        (Quotient.mk (Tagged obj).traceSetoid [cmd]) = 0 :=
      List.count_eq_zero.mpr (by simp [hne])
    omega
  · rfl

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}

/-- A round's clock counts that round's events: every value below
`gcaClock … N r` is the clock of an event of round `r` before `N`. -/
theorem gcaClock_event (st : Nat → WeakUniversal.Configuration (n := n) obj)
    (act : Nat → Option (Fin n)) {r : Nat} :
    ∀ {N c : Nat}, c < gcaClock obj st act N r →
      ∃ t, t < N ∧ ∃ p, gcaEvent obj st act t = some (r, p) ∧ gcaClock obj st act t r = c := by
  intro N
  induction N with
  | zero => intro c hc; simp [gcaClock] at hc
  | succ N ih =>
      intro c hc
      by_cases hlow : c < gcaClock obj st act N r
      · obtain ⟨t, ht, p, hev, hcl⟩ := ih hlow
        exact ⟨t, by omega, p, hev, hcl⟩
      · cases hev : gcaEvent obj st act N with
        | none =>
            simp only [gcaClock, hev] at hc
            omega
        | some rp =>
            obtain ⟨r', p⟩ := rp
            by_cases hr : r' = r
            · subst hr
              simp only [gcaClock, hev, ite_true] at hc
              exact ⟨N, by omega, p, hev, by omega⟩
            · simp only [gcaClock, hev, hr, ite_false] at hc
              omega

variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace WeakRun
variable (g : WeakRun obj H)

/-- A caller whose program state moves out of `waiting` has taken that round's
`receive` step: it read the round's output and branched on it (Line 5). -/
theorem receive_of_leave {v : Nat} {i : Fin n} {cmd : WeakUniversal.Cmd n Op} {R : Nat}
    {prop : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hwait : (g.run.state v).localState i = .waiting cmd R prop)
    (hleave : (g.run.state (v + 1)).localState i ≠ (g.run.state v).localState i) :
    ∃ s flag, (H R).output i = some (s, flag) ∧
      (g.run.state (v + 1)).localState i =
        (if flag = true ∧ 0 < (WeakUniversal.Tagged obj).traceCount cmd s
          then .publishing cmd R s else .ready cmd ⟨R, s⟩) := by
  rcases g.step_actor v with ⟨-, heq⟩ | ⟨q, -, hstep⟩ | ⟨q, r, -, -, heq⟩
  · exact absurd (by rw [heq]) hleave
  · have hqi : q = i := by
      apply Classical.byContradiction
      intro hne
      exact hleave (hstep.2 i (fun h => hne h.symm))
    subst hqi
    exact WeakUniversal.stepBy_from_waiting obj hstep hwait
  · exact absurd (by rw [heq]) hleave

end WeakRun

namespace Weak
variable {f : Family (n := n) obj} (g : Weak obj f)

/-- **Solo agreement for a round of the run**, from GCA property 7 of that
round's object.  If `i` left round `R` before time `N` and no other process had
called `R` by `N`, then every output of round `R` — in the whole run, including
callers that join `R` after `N` — is `i`'s output trace.

The prefix of Solo agreement is the round's clock at `N`: every protocol step
before it is an event of the run before `N`, taken by a process that had called
`R`, hence by `i`; and `i` had finished its call (`receive_ready`).  Only
property 7 of the round's GCA object is used. -/
theorem solo_round_outputs_of {N v R : Nat} {i : Fin n}
    (hsa : (f.protocol R).SoloAgreement)
    (hsoloR : ∀ call ∈ (g.run.state N).calls, call.round = R → call.process = i)
    (hv : v < N) (hwait : weakRound obj ((g.run.state v).localState i) = some R)
    (hleave : (g.run.state (v + 1)).localState i ≠ (g.run.state v).localState i) :
    ∃ tj cj, (f.environment obj R).output i = some (tj, cj) ∧
      ∀ q y fl, (f.environment obj R).output q = some (y, fl) → y = tj := by
  classical
  let T := gcaClock obj g.run.state g.actor N R
  have hsolo : ∀ c k, c < T → (f.protocol R).actor c = some k → k = i := by
    intro c k hc hk
    obtain ⟨t, htN, p, hev, hcl⟩ := gcaClock_event g.run.state g.actor hc
    obtain ⟨h1, h2⟩ := gcaEvent_inv obj hev
    have hact := g.gca_actor t p R h1 h2
    rw [hcl] at hact
    have hkp : k = p := Option.some.inj (hk.symm.trans hact)
    subst hkp
    obtain ⟨cmd, prop, hL⟩ := weakRound_eq_some h2
    obtain ⟨hcall, -⟩ :=
      WeakUniversal.waiting_call obj (g.run.reachable obj t) k cmd R prop hL
    exact hsoloR _ (g.calls_mono (Nat.le_of_lt htN) hcall) rfl
  have h6 : (f.protocol R).phase T i = 6 := by
    have hready := g.receive_ready v i R hwait hleave
    have hmono := (f.protocol R).phase_mono
      (show gcaClock obj g.run.state g.actor v R ≤ T from
        g.inter.clock_mono obj (Nat.le_of_lt hv)) i
    have hle := (f.protocol R).phase_le_six T i
    omega
  exact hsa T i hsolo h6

/-- **Algorithm 2 satisfies Solo agreement on the run's rounds**: every round
of the run is Algorithm 2, which has GCA property 7 (Lemma `GCA_soloagg`). -/
theorem soloAgreement : g.toWeakRun.SoloAgreement :=
  fun _ _ R _ hsoloR hv hwait hleave =>
    g.solo_round_outputs_of (f.protocol R).soloAgreement hsoloR hv hwait hleave

end Weak

namespace WeakRun
variable (g : WeakRun obj H)

/-- **Solo agreement for a round of the run (GCA property 7)**, read off the
run's Solo agreement property (`WeakRun.SoloAgreement`). -/
theorem solo_round_outputs (hsa : g.SoloAgreement) {N v R : Nat} {i : Fin n}
    (hsoloR : ∀ call ∈ (g.run.state N).calls, call.round = R → call.process = i)
    (hv : v < N) (hwait : weakRound obj ((g.run.state v).localState i) = some R)
    (hleave : (g.run.state (v + 1)).localState i ≠ (g.run.state v).localState i) :
    ∃ tj cj, (H R).output i = some (tj, cj) ∧
      ∀ q y fl, (H R).output q = some (y, fl) → y = tj :=
  hsa N v R i hsoloR hv hwait hleave

/-- **The checkpoint of `th:WeakUCresolve`.**  If `i` committed `x` at round
`R` — it left `waiting` for `publishing` at time `v` — and no other process had
called `R` by time `N > v`, then `x` is committed at `R` and, by Solo agreement,
*every* output of round `R` is `x`. -/
theorem solo_checkpoint (hsa : g.SoloAgreement) {N v R : Nat} {i : Fin n}
    {cmd : WeakUniversal.Cmd n Op}
    {prop x : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hsoloR : ∀ call ∈ (g.run.state N).calls, call.round = R → call.process = i)
    (hv : v < N) (hwait : (g.run.state v).localState i = .waiting cmd R prop)
    (hpub : (g.run.state (v + 1)).localState i = .publishing cmd R x) :
    WeakUniversal.Committed obj (H) R x ∧
      ∀ q y fl, (H R).output q = some (y, fl) → y = x := by
  have hleave : (g.run.state (v + 1)).localState i ≠ (g.run.state v).localState i := by
    rw [hpub, hwait]; simp
  obtain ⟨s, flag, hout, hnext⟩ := g.receive_of_leave hwait hleave
  have hcommit : flag = true ∧ s = x := by
    rw [hpub] at hnext
    split at hnext
    · rename_i hc
      injection hnext with _ _ hs
      exact ⟨hc.1, hs.symm⟩
    · cases hnext
  obtain ⟨rfl, rfl⟩ := hcommit
  have hpos : 0 < R := by
    have := (WeakUniversal.invariant obj (g.run.reachable obj v)).localState i
    rw [hwait] at this
    exact this
  obtain ⟨tj, cj, houti, hall⟩ :=
    g.solo_round_outputs hsa hsoloR hv (by rw [hwait]; rfl) hleave
  have htj : s = tj := by
    have := Option.some.inj (hout.symm.trans houti)
    exact congrArg Prod.fst this
  refine ⟨⟨hpos, i, hout⟩, fun q y fl hq => ?_⟩
  rw [hall q y fl hq, ← htj]

/-- The manuscript's "the instance takes steps after `α'`": the command is its
process's current command at a time at or after the checkpoint `N` at which
that process is scheduled. -/
def ActiveAfter (N : Nat) (a : WeakUniversal.Cmd n Op) : Prop :=
  ∃ u, N ≤ u ∧ g.actor u = some a.process ∧
    WeakUniversal.activeCmd obj ((g.run.state u).localState a.process) = some a

/-- A call not yet recorded at time `T` was proposed from a `ready` state at or
after `T`, by its caller's own step. -/
theorem call_was_ready_after {T t' : Nat} {call : WeakUniversal.Call (n := n) obj}
    (h : call ∈ (g.run.state t').calls) (hT : call ∉ (g.run.state T).calls) :
    ∃ u, T ≤ u ∧ g.actor u = some call.process ∧ ∃ cmd seed,
      (g.run.state u).localState call.process = .ready cmd seed ∧
      call.round = seed.round + 1 ∧
      call.trace = (WeakUniversal.Tagged obj).appendMissing seed.trace cmd := by
  classical
  induction t' with
  | zero => rw [g.run.initial_state] at h; simp [WeakUniversal.initial] at h
  | succ t ih =>
      by_cases hprev : call ∈ (g.run.state t).calls
      · exact ih hprev
      · have hTt : T ≤ t := by
          refine Nat.le_of_not_lt (fun hlt => hT ?_)
          exact g.calls_mono (by omega) h
        rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, hq, hstep⟩ | ⟨q, r, _, _, heq⟩
        · rw [heq] at h; exact absurd h hprev
        · obtain ⟨cmd, seed, hsrc, hr, htr⟩ :=
            WeakUniversal.stepBy_new_call_source obj hstep h hprev
          have howner : call.process = q := by
            rcases (WeakUniversal.stepBy_calls obj hstep).2 call h with hold | hp
            · exact (hprev hold).elim
            · exact hp
          exact ⟨t, hTt, howner ▸ hq, cmd, seed, hsrc, hr, htr⟩
        · rw [heq] at h; exact absurd h hprev

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H)

section Checkpoint

variable {N rc : Nat} {sc : (WeakUniversal.Tagged (n := n) obj).Trace}

/-- **One descent step.**  An occurrence in an input of round `m + 1` either is
the proposing process's own command — appended at Line 8 after the checkpoint,
while that process was running it — or occurs in the output of round `m` the
proposal was built from (Lines 4–9). -/
theorem input_origin_step
    (hbound : ∀ call ∈ (g.run.state N).calls, call.round ≤ rc)
    {m : Nat} (hm : rc ≤ m)
    (hprev : ∀ q x flag a, (H m).output q = some (x, flag) →
      0 < (WeakUniversal.Tagged obj).traceCount a x →
      0 < (WeakUniversal.Tagged obj).traceCount a sc ∨ g.ActiveAfter N a)
    {s : (WeakUniversal.Tagged (n := n) obj).Trace} {a : WeakUniversal.Cmd n Op}
    (hs : (H (m + 1)).Inputs s)
    (hpos : 0 < (WeakUniversal.Tagged obj).traceCount a s) :
    0 < (WeakUniversal.Tagged obj).traceCount a sc ∨ g.ActiveAfter N a := by
  classical
  obtain ⟨p', hp'⟩ := hs
  obtain ⟨t', hcall⟩ := (g.input_iff_call m p' s).mp hp'
  have hnew : (⟨m + 1, p', s⟩ : WeakUniversal.Call (n := n) obj)
      ∉ (g.run.state N).calls := by
    intro hmem
    have := hbound _ hmem
    simp only at this
    omega
  obtain ⟨u, hu, hactor, cmd, seed, hready, hr, htr⟩ := g.call_was_ready_after hcall hnew
  have hseed : seed.round = m := by
    have : m + 1 = seed.round + 1 := hr
    omega
  have hs' : s = (WeakUniversal.Tagged obj).appendMissing seed.trace cmd := htr
  by_cases he : a = cmd
  · -- the caller appended its own command at Lines 7-8, after the checkpoint
    right
    subst he
    have hown : a.process = p' :=
      ((WeakUniversal.identity_invariant obj (g.run.reachable obj u)).active_tag p' a
        (by simp [WeakUniversal.ledger, hready, WeakUniversal.Local.command])).1
    exact ⟨u, hu, by simpa [hown] using hactor, by rw [hown, hready]; rfl⟩
  · -- the occurrence was already in the trace taken from the previous round
    rw [hs', WeakUniversal.appendMissing_count_ne obj seed.trace a cmd he] at hpos
    have hsup := (WeakUniversal.invariant obj (g.run.reachable obj u)).localState p'
    rw [hready] at hsup
    rcases hsup with ⟨-, hempty⟩ | ⟨-, q', b, hq'⟩
    · rw [hempty] at hpos
      change 0 < ([] : List (WeakUniversal.Cmd n Op)).count a at hpos
      simp at hpos
    · exact hprev q' seed.trace b a (by rwa [hseed] at hq') hpos

/-- **The descent** (`th:WeakUCresolve`, "by induction on `r̂ ≥ r*`").  If every
output of the checkpoint round `rc` is `sc` — Solo agreement — and no call above
`rc` was made by the checkpoint time `N`, then every occurrence in an output of
a round `r ≥ rc` either occurs in `sc` or belongs to an instance that took a
step after `N`. -/
theorem origin_after
    (hbound : ∀ call ∈ (g.run.state N).calls, call.round ≤ rc)
    (hout : ∀ q y fl, (H rc).output q = some (y, fl) → y = sc) :
    ∀ r, rc ≤ r → ∀ q x flag a, (H r).output q = some (x, flag) →
      0 < (WeakUniversal.Tagged obj).traceCount a x →
      0 < (WeakUniversal.Tagged obj).traceCount a sc ∨ g.ActiveAfter N a := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro hr q x flag a hx hpos
    rcases Nat.eq_or_lt_of_le hr with heq | hlt
    · -- the checkpoint round: by Solo agreement every output is `sc`
      subst heq
      left
      rwa [hout q x flag hx] at hpos
    · obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have hm : rc ≤ m := by omega
      have hocc : GCA.History.Occurs
          (obj := WeakUniversal.Tagged (n := n) obj) a 0 x := by
        simpa only [GCA.History.Occurs,
          (WeakUniversal.Tagged obj).traceResponses_length] using hpos
      obtain ⟨s, hsin, hsocc⟩ :=
        (g.gca.spec m).validity.occurs q x flag hx a 0 hocc
      have hspos : 0 < (WeakUniversal.Tagged obj).traceCount a s := by
        simpa only [GCA.History.Occurs,
          (WeakUniversal.Tagged obj).traceResponses_length] using hsocc
      exact g.input_origin_step hbound hm (ih m (by omega) hm) hsin hspos

/-- Compatibility of a round's proposals from a nonconflict hypothesis on an
arbitrary set `C`, given that every residual command of a proposal is in `C`. -/
theorem inputs_compatible_res
    (coverage : WeakUniversal.CallsCovered obj (H))
    {k : Nat} {t : (WeakUniversal.Tagged (n := n) obj).Trace}
    (ht : (WeakUniversal.Tagged obj).IsGLB (g.Retrieved k) t)
    {C : WeakUniversal.Cmd n Op → Prop}
    (hC : (WeakUniversal.Tagged obj).Nonconflicting C)
    (hsub : ∀ s, (H (k + 2)).Inputs s → ∀ a, g.Pending k a →
      (WeakUniversal.Tagged obj).traceCount a t = 0 →
      0 < (WeakUniversal.Tagged obj).traceCount a s → C a) :
    (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs := by
  classical
  refine (H (k + 2)).inputs_compatible_of_pending_proposals hC t
    ((List.finRange n).filterMap (fun p => (H (k + 2)).input p)) ?_ ?_
  · rintro s ⟨p, hp⟩
    exact List.mem_filterMap.mpr ⟨p, List.mem_finRange p, hp⟩
  · intro s hsm
    obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hsm
    obtain ⟨w, hw, he⟩ := g.proposal_shape coverage ht ⟨p, hp⟩
    refine ⟨w, ?_, he⟩
    intro a ha
    have hcount : 0 < (WeakUniversal.Tagged obj).traceCount a s := by
      have hwc : 0 < w.count a := List.count_pos_iff.mpr ha
      have : (WeakUniversal.Tagged obj).traceCount a s
          = (WeakUniversal.Tagged obj).traceCount a t + w.count a := by
        rw [he]
        exact (WeakUniversal.Tagged obj).traceCount_append a t (Quotient.mk _ w)
      omega
    exact hsub s ⟨p, hp⟩ a (hw a ha).1 (hw a ha).2 hcount

/-- **Invariant (I) of `th:WeakUCresolve`.**  Beyond a solo checkpoint round,
the proposals to a round are compatible as soon as the pending commands *that
took a step after the checkpoint* do not conflict.  Residual commands miss the
common prefix `t`, which contains `sc` (`lemma:prefix-rounds`), so the descent
places them after the checkpoint. -/
theorem inputs_compatible_after
    (coverage : WeakUniversal.CallsCovered obj (H))
    (hbound : ∀ call ∈ (g.run.state N).calls, call.round ≤ rc)
    (hout : ∀ q y fl, (H rc).output q = some (y, fl) → y = sc)
    (hcom : WeakUniversal.Committed obj (H) rc sc)
    {k : Nat} (hk : rc ≤ k + 1)
    (hC : (WeakUniversal.Tagged obj).Nonconflicting
      (fun a => g.Pending k a ∧ g.ActiveAfter N a)) :
    (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs := by
  classical
  by_cases hcaller : ∃ s, (H (k + 2)).Inputs s
  · obtain ⟨t, ht⟩ :=
      (WeakUniversal.Tagged obj).glb_exists _ (g.retrieved_nonempty hcaller)
    have hsc : (WeakUniversal.Tagged obj).TracePrefix sc t :=
      WeakUniversal.committed_below_glb obj coverage (g.gca.spec) hcom hk
        (fun x hx => g.retrieved_output hx) ht
    refine g.inputs_compatible_res coverage ht hC ?_
    intro s hs a hpend hzero hposs
    refine ⟨hpend, ?_⟩
    rcases g.input_origin_step hbound hk
        (g.origin_after hbound hout (k + 1) hk) hs hposs with hin | hact
    · have hmono := (WeakUniversal.Tagged obj).traceCount_mono hsc a
      exact absurd hin (by omega)
    · exact hact
  · exact ⟨(WeakUniversal.Tagged obj).emptyTrace, fun s hs => absurd ⟨s, hs⟩ hcaller⟩

end Checkpoint

end WeakGCA

namespace WeakRun
variable (g : WeakRun obj H)

/-- **The manuscript's hypothesis, carried to the program run.**  "Eventually
weakly `α'`-conflict-free": beyond `T₀`, two distinct commands that are
simultaneously invoked-and-unanswered, and that both take steps after the
checkpoint time `N`, do not conflict.  `WeakUCResolve.lean` derives it from the
§3 statement about the extracted execution. -/
def EventuallyWeaklyNonconflicting (N T₀ : Nat) : Prop :=
  ∀ t, T₀ ≤ t → ∀ a b : WeakUniversal.Cmd n Op,
    a ∈ (g.run.state t).invocations →
    (∀ ret ∈ (g.run.state t).returns, ret.command ≠ a) →
    b ∈ (g.run.state t).invocations →
    (∀ ret ∈ (g.run.state t).returns, ret.command ≠ b) →
    a ≠ b → g.ActiveAfter N a → g.ActiveAfter N b →
    (WeakUniversal.Tagged obj).Independent a b

/-- In the setting of the manuscript's contradiction — the response history is
frozen from `T` on — a command not returned by round `k + 1` is never returned,
so two such commands that take steps after `N` are simultaneously pending at a
late time, and the hypothesis applies to them. -/
theorem nonconflicting_active_of_eventually {N T₀ T : Nat}
    (hC : g.EventuallyWeaklyNonconflicting N T₀)
    (hfrozen : ∀ t, T ≤ t → (g.run.state t).returns = (g.run.state T).returns)
    {k : Nat} (hk : ∀ ret ∈ (g.run.state T).returns, ret.round ≤ k + 1) :
    (WeakUniversal.Tagged obj).Nonconflicting (fun a => g.Pending k a ∧ g.ActiveAfter N a) := by
  classical
  intro a b ha hb hab
  obtain ⟨ta, hta⟩ := ha.1.1
  obtain ⟨tb, htb⟩ := hb.1.1
  have hnr : ∀ c : WeakUniversal.Cmd n Op, ¬ g.ReturnedBy k c →
      ∀ ret ∈ (g.run.state T).returns, ret.command ≠ c := by
    intro c hc ret hret he
    exact hc ⟨T, ret, hret, he, hk ret hret⟩
  refine hC (max (max ta tb) (max T₀ T)) (by omega) a b ?_ ?_ ?_ ?_ hab ha.2 hb.2
  · exact (g.run.ledgerRun obj).invoked_mono (by omega) hta
  · rw [hfrozen _ (by omega)]; exact hnr a ha.1.2
  · exact (g.run.ledgerRun obj).invoked_mono (by omega) htb
  · rw [hfrozen _ (by omega)]; exact hnr b hb.1.2

end WeakRun

namespace WeakGCA
variable (g : WeakGCA obj H)

/-- **`th:WeakUCresolve`, progress half, inside one run.**  Suppose that by time
`N`

* `i` has committed `x` at round `R`, having left `waiting` for `publishing`
  at a time `v < N` (it "returns from `GCA_{r*}` and completes");
* no other process has called `R` (`i` "is the sole participant of `GCA_{r*}`
  in `α'`"); and
* no call above `R` has been made ("`r*` is greater than every round reached"),

and that beyond some time the pending commands that take steps after `N` do
not conflict.  Then some process that takes infinitely many steps completes
every operation it invokes.

This is the manuscript's contradiction: freeze the response history at `τ'`;
by invariant (I) every round above `max(r_0, r*)` has compatible proposals; by
Commitment one of them completes an operation after `τ'`. -/
theorem forgetting_completes (hsa : g.SoloAgreement) (hlive : g.Live) {N v R : Nat} {i : Fin n} {cmd : WeakUniversal.Cmd n Op}
    {prop x : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hv : v < N) (hwait : (g.run.state v).localState i = .waiting cmd R prop)
    (hpub : (g.run.state (v + 1)).localState i = .publishing cmd R x)
    (hsoloR : ∀ call ∈ (g.run.state N).calls, call.round = R → call.process = i)
    (hbound : ∀ call ∈ (g.run.state N).calls, call.round ≤ R)
    {T₀ : Nat} (hC : g.EventuallyWeaklyNonconflicting N T₀) :
    ∃ p, g.Stepping p ∧ ∀ a, g.Invoked a → a.process = p → g.Completes a := by
  classical
  obtain ⟨hcom, hout⟩ := g.solo_checkpoint hsa hsoloR hv hwait hpub
  apply Classical.byContradiction
  intro hgoal
  obtain ⟨T, hfrozen⟩ := g.returns_freeze_of_not_completing hgoal
  obtain ⟨BR, hBR⟩ := WeakUniversal.returns_round_bound obj (g.run.state T).returns
  obtain ⟨B, hB⟩ := g.eventually_callers_stepping
  obtain ⟨p, hp⟩ := g.exists_stepping hlive
  refine g.no_stall_of_compatible g.callsCovered hp (k₀ := max (max BR B) R) ?_ ?_
    hfrozen
  · intro k hk
    exact g.inputs_compatible_after g.callsCovered hbound hout hcom (by omega)
      (g.nonconflicting_active_of_eventually hC hfrozen
        (fun ret hret => Nat.le_trans (hBR ret hret) (by omega)))
  · intro k hk; exact hB k (by omega)

end WeakGCA
end ConflictFreedom.GlobalSchedule
