import CFLeanProof.TraceIndependence
import CFLeanProof.TraceIndependencePairwise
import CFLeanProof.HelpingConflictFree

/-!
# Algorithm 3's conflict-free progress from §3's hypothesis

The manuscript proves Lemma `lemma:UCV2isCF` with **two** invariants.  Fix a
forever-pending operation instance `Φ` of a correct process `i`, let `τ'` be a
time after which `M[i] = cmd(Φ)`, and let `r*` be the largest round reached by
`τ'`.  Then

* **(II)** for any `r > r*`, every output trace of `GCA_r` contains `cmd(Φ)`;
* **(I)** for any `r > r*`, only compatible traces are proposed to `GCA_r`.

The order matters.  (II) needs only that `cmd(Φ)` does not conflict with the
commands sitting in the residuals, and *those* are pending because a command
that had already returned by `τ'` was committed at a round `≤ r*` and therefore
lies below the common prefix.  (I) then uses (II) to rule out a commit at a
round above `r*`: such a commit would carry `cmd(Φ)` into `S`, and `i`'s next
collect would complete `Φ`.  With no commit above `r*`, a command that is not
returned below the bound is not returned at all, so any two residual commands
are simultaneously pending and §3's hypothesis applies.

Algorithm 1's proof does without (II): its contradiction hypothesis freezes
responses.  Algorithm 3's concerns a *single* operation, so responses do not
freeze on their own, and invariant (II) supplies the freeze.
-/

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingRun
variable (g : HelpingRun obj H)

/-- **§3's hypothesis, over time.**  Beyond `T₀`, two distinct commands that are
simultaneously invoked-and-unanswered do not conflict. -/
def EventuallyNonconflicting (T₀ : Nat) : Prop :=
  ∀ t, T₀ ≤ t → ∀ a b : WeakUniversal.Cmd n Op,
    a ∈ (g.run.state t).invocations →
    (∀ ret ∈ (g.run.state t).returns, ret.command ≠ a) →
    b ∈ (g.run.state t).invocations →
    (∀ ret ∈ (g.run.state t).returns, ret.command ≠ b) →
    a ≠ b → (WeakUniversal.Tagged obj).Independent a b

/-- A command with no response recorded by `T` is invoked-and-unanswered at some
time at or after `T`: either already at `T`, or at the moment it is invoked. -/
theorem pending_witness {T : Nat} {b : WeakUniversal.Cmd n Op} (hinv : g.Invoked b)
    (hno : ∀ ret ∈ (g.run.state T).returns, ret.command ≠ b) :
    ∃ u, T ≤ u ∧ b ∈ (g.run.state u).invocations ∧
      ∀ ret ∈ (g.run.state u).returns, ret.command ≠ b := by
  classical
  obtain ⟨tb, htb, hmin⟩ := exists_least _ hinv
  rcases Nat.le_total tb T with hle | hge
  · exact ⟨T, Nat.le_refl _, (g.run.ledgerRun obj).invoked_mono hle htb, hno⟩
  · refine ⟨tb, hge, htb, ?_⟩
    intro ret hret he
    have hmem : b ∈ ((g.run.ledgerRun obj).state tb).returned :=
      List.mem_map.mpr ⟨ret, hret, he⟩
    obtain ⟨u, hu, hiu⟩ :=
      (g.run.ledgerRun obj).invoked_strictly_before_return hmem
    exact absurd (hmin u hiu) (by omega)

/-- The forever-pending command does not conflict with any command that is
pending below the round bound.  Such a command had not returned by `T`, so it is
simultaneously pending with `a` at some later time. -/
theorem own_independent_of_pending {T₀ T k : Nat}
    (hC : g.EventuallyNonconflicting T₀) (hT : T₀ ≤ T)
    {a : WeakUniversal.Cmd n Op} (hainv : a ∈ (g.run.state T).invocations)
    (hnr : ¬ g.Completes a)
    (hretbound : ∀ ret ∈ (g.run.state T).returns, ret.round ≤ k + 1)
    {b : WeakUniversal.Cmd n Op} (hb : g.Pending k b) (hab : a ≠ b) :
    (WeakUniversal.Tagged obj).Independent a b := by
  have hnob : ∀ ret ∈ (g.run.state T).returns, ret.command ≠ b := by
    intro ret hret he
    exact hb.2 ⟨T, ret, hret, he, hretbound ret hret⟩
  obtain ⟨u, hu, hbinv, hbno⟩ := g.pending_witness hb.1 hnob
  refine hC u (by omega) a b
    ((g.run.ledgerRun obj).invoked_mono hu hainv) ?_ hbinv hbno hab
  intro ret hret he
  exact hnr ⟨u, ret.round, ret.trace, by rw [← he]; exact hret⟩

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

omit [DecidableEq Op] in
private theorem traceCons_eq (a : WeakUniversal.Cmd n Op)
    (u : (WeakUniversal.Tagged (n := n) obj).Trace) :
    (WeakUniversal.Tagged obj).traceCons a u
      = (WeakUniversal.Tagged obj).traceAppend (Quotient.mk _ [a]) u := by
  induction u using Quotient.inductionOn with | h u => rfl

/-- **Invariant (II), for residual commands.**  Once `M[i]` permanently
announces `a`, and `a` conflicts with no command in the residual of a proposal
to round `k + 2` — a command pending below the round bound, occurring in the
proposal but not in the common prefix `t` of the traces retrieved from round
`k + 1` — every
output trace of round `k + 2` contains `a`.

The manuscript's argument: each proposal is `t · u_j · m_j` with `a` occurring in
it, and `a` commutes with every other command there, so `t · a` is below every
proposal; GCA Common Prefix then carries `t · a` into every output. -/
theorem output_contains_own_of
    (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} {a : WeakUniversal.Cmd n Op} {T B k : Nat}
    (hann : ∀ t, T ≤ t → (g.run.state t).announcements i = some a)
    (hbound : ∀ p, HelpingUniversal.localRound obj ((g.run.state T).localState p) ≤ B)
    (hcallbound : ∀ call ∈ (g.run.state T).calls, call.round ≤ B)
    (hindep : ∀ t, (WeakUniversal.Tagged obj).IsGLB (g.Retrieved k) t →
      ∀ s, (H (k + 2)).Inputs s → ∀ b, g.Pending k b →
        (WeakUniversal.Tagged obj).traceCount b t = 0 →
        0 < (WeakUniversal.Tagged obj).traceCount b s →
        a ≠ b → (WeakUniversal.Tagged obj).Independent a b)
    (hk : B + 1 ≤ k)
    {y : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hy : (H (k + 2)).Outputs y) :
    0 < (WeakUniversal.Tagged obj).traceCount a y := by
  classical
  obtain ⟨p0, c0, hp0⟩ := hy
  obtain ⟨s0, hs0⟩ := (H (k + 2)).returned_invoked p0 y c0 hp0
  obtain ⟨t, ht⟩ := (WeakUniversal.Tagged obj).glb_exists _
    (g.retrieved_nonempty ⟨s0, p0, hs0⟩)
  -- every proposal is `t · w` with `w` pending and independent of `a`, and contains `a`
  have hstep : ∀ s, (H (k + 2)).Inputs s →
      ∃ w : List (WeakUniversal.Cmd n Op),
        (∀ b ∈ w, g.Pending k b ∧ (a ≠ b → (WeakUniversal.Tagged obj).Independent a b)) ∧
        s = (WeakUniversal.Tagged obj).traceAppend t (Quotient.mk _ w) ∧
        0 < (WeakUniversal.Tagged obj).traceCount a s := by
    intro s hs
    obtain ⟨w, hw, hsw⟩ := g.proposal_shape coverage ht hs
    have hins : ∀ b ∈ w, 0 < (WeakUniversal.Tagged obj).traceCount b s := by
      intro b hb
      have hwc : 0 < w.count b := List.count_pos_iff.mpr hb
      have : (WeakUniversal.Tagged obj).traceCount b s
          = (WeakUniversal.Tagged obj).traceCount b t + w.count b := by
        rw [hsw]
        exact (WeakUniversal.Tagged obj).traceCount_append b t (Quotient.mk _ w)
      omega
    have hs' := hs
    obtain ⟨q, hq⟩ := hs'
    obtain ⟨t', hcall⟩ := (g.input_iff_call (k + 1) q s).mp hq
    exact ⟨w, fun b hb => ⟨(hw b hb).1,
        hindep t ht s hs b (hw b hb).1 (hw b hb).2 (hins b hb)⟩, hsw,
      g.helped_input hann hbound hcallbound (by omega) hcall⟩
  by_cases hat : 0 < (WeakUniversal.Tagged obj).traceCount a t
  · -- `a` already sits in the common prefix
    have hlow : ∀ s, (H (k + 2)).Inputs s →
        (WeakUniversal.Tagged obj).TracePrefix t s := by
      intro s hs
      obtain ⟨w, -, hsw, -⟩ := hstep s hs
      exact ((WeakUniversal.Tagged obj).tracePrefix_iff_append t s).mpr ⟨_, hsw⟩
    exact Nat.lt_of_lt_of_le hat ((WeakUniversal.Tagged obj).traceCount_mono
      ((g.gca.spec (k + 1)).commonPrefix t hlow y ⟨p0, c0, hp0⟩) a)
  · -- otherwise pull `a` to the front of every residual
    have hat0 : (WeakUniversal.Tagged obj).traceCount a t = 0 := by omega
    have hlow : ∀ s, (H (k + 2)).Inputs s →
        (WeakUniversal.Tagged obj).TracePrefix
          ((WeakUniversal.Tagged obj).traceAppend t (Quotient.mk _ [a])) s := by
      intro s hs
      obtain ⟨w, hw, hsw, hcnt⟩ := hstep s hs
      have hsplit : (WeakUniversal.Tagged obj).traceCount a s
          = (WeakUniversal.Tagged obj).traceCount a t + w.count a := by
        rw [hsw]
        exact (WeakUniversal.Tagged obj).traceCount_append a t (Quotient.mk _ w)
      have hmem : a ∈ w := List.count_pos_iff.mp (by omega)
      have hcan : (WeakUniversal.Tagged obj).CanStart a w :=
        (WeakUniversal.Tagged obj).canStart_of_mem_of_pairwise hmem
          (fun b hb hba => (hw b hb).2 (fun he => hba he.symm))
      have hmove := (WeakUniversal.Tagged obj).traceCanStart_move
        (s := (Quotient.mk _ w : (WeakUniversal.Tagged (n := n) obj).Trace)) hcan
      rw [traceCons_eq] at hmove
      have hpre : (WeakUniversal.Tagged obj).TracePrefix (Quotient.mk _ [a])
          (Quotient.mk _ w) :=
        ((WeakUniversal.Tagged obj).tracePrefix_iff_append _ _).mpr ⟨_, hmove⟩
      rw [hsw]
      exact (WeakUniversal.Tagged obj).traceAppend_mono_right t hpre
    have hle := (g.gca.spec (k + 1)).commonPrefix _ hlow y ⟨p0, c0, hp0⟩
    have hcount : 0 < (WeakUniversal.Tagged obj).traceCount a
        ((WeakUniversal.Tagged obj).traceAppend t (Quotient.mk _ [a])) := by
      rw [(WeakUniversal.Tagged obj).traceCount_append a t (Quotient.mk _ [a])]
      have : ([a].count a) = 1 := by simp
      change 0 < (WeakUniversal.Tagged obj).traceCount a t + [a].count a
      omega
    exact Nat.lt_of_lt_of_le hcount ((WeakUniversal.Tagged obj).traceCount_mono hle a)

/-- **Invariant (II).**  Once `M[i]` permanently announces `a`, and `a` conflicts
with no command that is still pending below the round bound, every output trace
of every high enough round contains `a`. -/
theorem output_contains_own
    (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} {a : WeakUniversal.Cmd n Op} {T B k : Nat}
    (hann : ∀ t, T ≤ t → (g.run.state t).announcements i = some a)
    (hbound : ∀ p, HelpingUniversal.localRound obj ((g.run.state T).localState p) ≤ B)
    (hcallbound : ∀ call ∈ (g.run.state T).calls, call.round ≤ B)
    (hindep : ∀ b, g.Pending k b → a ≠ b → (WeakUniversal.Tagged obj).Independent a b)
    (hk : B + 1 ≤ k)
    {y : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hy : (H (k + 2)).Outputs y) :
    0 < (WeakUniversal.Tagged obj).traceCount a y :=
  g.output_contains_own_of coverage hann hbound hcallbound
    (fun _ _ _ _ b hb _ _ hab => hindep b hb hab) hk hy

/-- **A register of high round completes a command that every committed trace
of such rounds contains.**  If from time `w₀` on some register `S[j]` holds a
round at least `R`, every final `S` collect started after `w₀` adopts a trace
committed at a round at least `R`; if every such trace contains `a`, a process
that keeps taking steps while running `a` finds `a` and returns. -/
theorem completes_of_high_slot
    {i : Fin n} (hi : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some i)
    {a : WeakUniversal.Cmd n Op} {τ₀ : Nat}
    (hcmd : ∀ t, τ₀ ≤ t →
      HelpingUniversal.Local.command obj ((g.run.state t).localState i) = some a)
    {j : Fin n} {R w₀ : Nat} (hR : 0 < R)
    (hslot : ∀ t, w₀ ≤ t → R ≤ ((g.run.state t).slots j).round)
    (hall : ∀ k', R ≤ k' + 1 → ∀ q' y, (H (k' + 1)).output q' = some (y, true) →
      0 < (WeakUniversal.Tagged obj).traceCount a y) :
    g.Completes a := by
  classical
  have hmax1 : w₀ ≤ max w₀ τ₀ := Nat.le_max_left _ _
  have hmax2 : τ₀ ≤ max w₀ τ₀ := Nat.le_max_right _ _
  rcases g.reaches_waiting_or_return hi _ (max w₀ τ₀) (Nat.le_refl _) with
    ⟨u4, hu4, hat⟩ | ⟨u5, hu5, cmd₅, r₅, prop₅, hL₅, -⟩
  · obtain ⟨cmd, hc, hcomp⟩ := g.atReturn_completes hi hat
    exact (Option.some.inj (hc.symm.trans (hcmd u4 (by omega)))) ▸ hcomp
  obtain ⟨v5, hv5, seed5, order5, horder5, hchk5⟩ := g.reaches_fresh_collect hi hL₅
  obtain ⟨z, hz, seen', hLz, hRz⟩ :=
    g.check_collect_above hi hslot order5 v5 (by omega)
      cmd₅ seed5 _ hchk5 (Or.inl (horder5.mem_iff.mpr (List.mem_finRange j)))
  have hcmdz : HelpingUniversal.Local.command obj ((g.run.state z).localState i)
      = some cmd₅ := by rw [hLz]; rfl
  have hc5 : cmd₅ = a := Option.some.inj (hcmdz.symm.trans (hcmd z (by omega)))
  have hloc := (HelpingUniversal.invariant obj (g.run.reachable obj z)).localState i
  rw [hLz] at hloc
  obtain ⟨-, hstoredz⟩ := hloc
  rcases hstoredz with ⟨h0, -⟩ | hcom
  · omega
  obtain ⟨hpos, q', hq'⟩ := hcom
  obtain ⟨k', hk'⟩ : ∃ k', seen'.round = k' + 1 := ⟨seen'.round - 1, by omega⟩
  rw [hk'] at hq'
  have hfinal : 0 < (WeakUniversal.Tagged obj).traceCount a seen'.trace :=
    hall k' (by omega) q' seen'.trace hq'
  obtain ⟨cmd, hc, hcomp⟩ := g.atReturn_completes hi
    (show HelpingUniversal.AtReturn obj ((g.run.state z).localState i) from
      ⟨cmd₅, seed5, seen', hLz, by rw [hc5]; exact hfinal⟩)
  exact (Option.some.inj (hc.symm.trans (hcmd z (by omega)))) ▸ hcomp

/-- **A published trace completes the commands it contains.**  If from time
`w₀` on some register `S[j]` holds a round at least `R`, a trace committed at a
round `r + 1 ≤ R` is a prefix of every trace committed at a round at least `R`
(`lemma:prefix-rounds`), so `completes_of_high_slot` applies. -/
theorem completes_of_slot (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} (hi : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some i)
    {a : WeakUniversal.Cmd n Op} {τ₀ : Nat}
    (hcmd : ∀ t, τ₀ ≤ t →
      HelpingUniversal.Local.command obj ((g.run.state t).localState i) = some a)
    {j : Fin n} {R w₀ : Nat} (hslot : ∀ t, w₀ ≤ t → R ≤ ((g.run.state t).slots j).round)
    {r : Nat} {q : Fin n} {x : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hx : (H (r + 1)).output q = some (x, true)) (hrR : r + 1 ≤ R)
    (hax : 0 < (WeakUniversal.Tagged obj).traceCount a x) :
    g.Completes a :=
  g.completes_of_high_slot hi hcmd (by omega) hslot fun k' hk' q' y hy =>
    Nat.lt_of_lt_of_le hax ((WeakUniversal.Tagged obj).traceCount_mono
      (HelpingUniversal.committed_prefix obj coverage (g.gca.spec)
        (show r ≤ k' by omega) hx hy) a)

/-- **A committed trace is published.**  A process that commits at a round whose
callers keep stepping writes its trace into `S` (Line 14), and from then on its
register holds that round or a later one. -/
theorem commit_published
    {k : Nat}
    (hcallers : ∀ q, (∃ s, (H (k + 2)).input q = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q)
    {j : Fin n} {x : (WeakUniversal.Tagged (n := n) obj).Trace}
    (houtj : (H (k + 2)).output j = some (x, true)) :
    ∃ w₀, ∀ t, w₀ ≤ t → k + 2 ≤ ((g.run.state t).slots j).round := by
  classical
  obtain ⟨sj, hinj⟩ := (H (k + 2)).returned_invoked j x true houtj
  obtain ⟨tj, hcallj⟩ := (g.input_iff_call (k + 1) j sj).mp hinj
  have hschedj := hcallers j ⟨sj, hinj⟩
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
  refine ⟨v2 + 1, fun t ht => ?_⟩
  have hmono := g.slots_mono (q := j) ht
  rw [hslotj] at hmono
  exact hmono

/-- **The step invariant (II) unlocks.**  A trace committed at a round whose
callers keep stepping, and which contains `a`, is written into `S` by its
author; `i`'s next `S` collect therefore adopts a committed trace extending it,
so `i` leaves the loop and `a` completes. -/
theorem commit_high_completes (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} (hi : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some i)
    {a : WeakUniversal.Cmd n Op} {τ₀ : Nat}
    (hcmd : ∀ t, τ₀ ≤ t →
      HelpingUniversal.Local.command obj ((g.run.state t).localState i) = some a)
    {k : Nat}
    (hcallers : ∀ q, (∃ s, (H (k + 2)).input q = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some q)
    {j : Fin n} {x : (WeakUniversal.Tagged (n := n) obj).Trace}
    (houtj : (H (k + 2)).output j = some (x, true))
    (hax : 0 < (WeakUniversal.Tagged obj).traceCount a x) :
    g.Completes a := by
  obtain ⟨w₀, hslotR⟩ := g.commit_published hcallers houtj
  exact g.completes_of_slot coverage hi hcmd hslotR houtj (Nat.le_refl _) hax

/-- **From §3's hypothesis to the round-indexed one, for Algorithm 3.**  This is
the manuscript's two-invariant argument.  Under the contradiction hypothesis
that `a` never returns, invariant (II) holds at every high enough round; a
commit above the bound would then carry `a` into `S` and complete it, so no
such commit exists; hence a command not returned below the bound is not
returned at all, and any two such are simultaneously pending. -/
theorem nonconflicting_pending_of_eventually (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} (hi : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some i)
    {T₀ : Nat} (hC : g.EventuallyNonconflicting T₀)
    {τ₀ : Nat} {a : WeakUniversal.Cmd n Op}
    (ha : HelpingUniversal.Local.command obj ((g.run.state τ₀).localState i) = some a)
    (hnr : ¬ g.Completes a) :
    ∃ k₀, ∀ k, k₀ ≤ k → (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k) := by
  classical
  have hcmd := g.command_persists ha hnr
  have hnoAt : ∀ u, τ₀ ≤ u →
      ¬ HelpingUniversal.AtReturn obj ((g.run.state u).localState i) := by
    intro u hu hat
    obtain ⟨cmd, hc, hcomp⟩ := g.atReturn_completes hi hat
    exact hnr ((Option.some.inj (hc.symm.trans (hcmd u hu))) ▸ hcomp)
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
  obtain ⟨B, hB⟩ := WeakUniversal.calls_round_bound obj (g.run.state τ₁).calls
  have hbound : ∀ p, HelpingUniversal.localRound obj
      ((g.run.state τ₁).localState p) ≤ B := by
    intro p
    rcases (HelpingUniversal.roundsCalled obj (g.run.reachable obj τ₁)).2 p with
      h0 | ⟨call, hmem, he⟩
    · omega
    · rw [← he]; exact hB call hmem
  obtain ⟨Bc, hBc⟩ := g.eventually_callers_stepping
  obtain ⟨Br, hBr⟩ :=
    WeakUniversal.returns_round_bound obj (g.run.state (max τ₁ T₀)).returns
  have hainv : a ∈ (g.run.state (max τ₁ T₀)).invocations :=
    (((g.run.ledgerRun obj).valid (max τ₁ T₀)).active_tag i a
      (hcmd _ (Nat.le_trans hτ₁ (Nat.le_max_left _ _)))).2.2
  refine ⟨max (max (B + 1) Br) Bc, fun k hk => ?_⟩
  have hm1 : B + 1 ≤ max (B + 1) Br := Nat.le_max_left _ _
  have hm2 : Br ≤ max (B + 1) Br := Nat.le_max_right _ _
  have hm3 : max (B + 1) Br ≤ max (max (B + 1) Br) Bc := Nat.le_max_left _ _
  have hm4 : Bc ≤ max (max (B + 1) Br) Bc := Nat.le_max_right _ _
  -- the commands pending below the bound do not conflict with `a`
  have hindep : ∀ m, max (max (B + 1) Br) Bc ≤ m →
      ∀ c, g.Pending m c → a ≠ c → (WeakUniversal.Tagged obj).Independent a c := by
    intro m hm c hc hac
    exact g.own_independent_of_pending hC (Nat.le_max_right _ _) hainv hnr
      (fun ret hret => Nat.le_trans (hBr ret hret) (by omega)) hc hac
  -- invariant (II)
  have hII : ∀ m, max (max (B + 1) Br) Bc ≤ m →
      ∀ y, (H (m + 2)).Outputs y →
        0 < (WeakUniversal.Tagged obj).traceCount a y := by
    intro m hm y hy
    exact g.output_contains_own coverage hann hbound hB (hindep m hm) (by omega) hy
  -- no commit above the bound
  have hnocommit : ∀ m, max (max (B + 1) Br) Bc ≤ m →
      ∀ q y, (H (m + 2)).output q ≠ some (y, true) := by
    intro m hm q y hout
    exact hnr (g.commit_high_completes coverage hi hcmd
      (hBc m (by omega)) hout (hII m hm y ⟨q, true, hout⟩))
  -- hence every recorded response was committed below the bound
  have hretlow : ∀ t (ret : WeakUniversal.Return (n := n) obj),
      ret ∈ (g.run.state t).returns →
      ret.round ≤ max (max (B + 1) Br) Bc + 1 := by
    intro t ret hret
    obtain ⟨hcom, -⟩ :=
      (HelpingUniversal.invariant obj (g.run.reachable obj t)).returns ret hret
    obtain ⟨hpos, q, hq⟩ := hcom
    refine Nat.le_of_not_lt (fun hlt => ?_)
    obtain ⟨m, hm⟩ : ∃ m, ret.round = m + 2 := ⟨ret.round - 2, by omega⟩
    rw [hm] at hq
    exact hnocommit m (by omega) q ret.trace hq
  -- a command pending below the bound never returns at all
  have hnever : ∀ c, g.Pending k c → ¬ g.Completes c := by
    rintro c hc ⟨t, r, s, hmem⟩
    exact hc.2 ⟨t, ⟨c, r, s⟩, hmem, rfl,
      Nat.le_trans (hretlow t ⟨c, r, s⟩ hmem) (by omega)⟩
  intro b b' hb hb' hbb'
  obtain ⟨tb, htb⟩ := hb.1
  obtain ⟨tb', htb'⟩ := hb'.1
  refine hC (max T₀ (max tb tb')) (Nat.le_max_left _ _) b b'
    ((g.run.ledgerRun obj).invoked_mono (by omega) htb) ?_
    ((g.run.ledgerRun obj).invoked_mono (by omega) htb') ?_ hbb'
  · intro ret hret he
    exact hnever b hb ⟨_, ret.round, ret.trace, by rw [← he]; exact hret⟩
  · intro ret hret he
    exact hnever b' hb' ⟨_, ret.round, ret.trace, by rw [← he]; exact hret⟩

/-- **Lemma `lemma:UCV2isCF`, eventually-conflict-free half, under §3's own
hypothesis.**  In a run that is eventually conflict-free *in time*, every
operation of a process that keeps taking steps completes.  Unlike the earlier
round-indexed form, this takes exactly the manuscript's assumption. -/
theorem operation_completes_time (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} (hi : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some i)
    {T₀ : Nat} (hC : g.EventuallyNonconflicting T₀)
    {τ₀ : Nat} {a : WeakUniversal.Cmd n Op}
    (ha : HelpingUniversal.Local.command obj ((g.run.state τ₀).localState i) = some a) :
    g.Completes a := by
  classical
  refine Classical.byContradiction (fun hnr => hnr ?_)
  exact g.operation_completes coverage hi
    (g.nonconflicting_pending_of_eventually coverage hi hC ha hnr) ha

/-- Invocation form of the same statement. -/
theorem invoked_completes_time (coverage : HelpingUniversal.CallsCovered obj (H))
    {i : Fin n} (hi : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some i)
    {T₀ : Nat} (hC : g.EventuallyNonconflicting T₀)
    {a : WeakUniversal.Cmd n Op} (hinv : g.Invoked a) (hproc : a.process = i) :
    g.Completes a := by
  obtain ⟨τ, hτ⟩ := g.invoked_command hinv
  rw [hproc] at hτ
  exact g.operation_completes_time coverage hi hC hτ

end HelpingGCA
end ConflictFreedom.GlobalSchedule
