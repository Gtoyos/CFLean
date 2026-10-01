import CFLeanProof.CausalLinearization

/-! # Algorithm 1 needs no temporal contract from GCA

The manuscript's GCA properties hold for every execution, so on every prefix;
the model checks them on the whole-run table only, and `NonCausalWitness` shows
that for Algorithm 3 this weaker reading is not enough: the prefix instance of
Validity, causal validity, must be added.  Algorithm 1 does not need it: when
every GCA input is a proposal of the run itself (`Execution.Covers`), the six
properties of the whole run already make every returned trace consist of
invoked commands (`Execution.returnsInvokedBy_of_covers`), so the construction
is linearizable over any such GCA (`Execution.covered_finite_linearization`).

The reason is the absence of helping.  A command enters a proposal only as its
invoker's own command, or through the seed — a committed or received output of
the previous round, which by Validity comes from a proposal of that round.  By
induction on rounds, every command of a round-`r` output was proposed by its own
invoker to some round `≤ r` (`Execution.own_proposal`).  But the invoker
collects `S` after invoking and `S` only grows, so its proposals go to rounds
above every round published before the invocation (`Execution.floor`).  A trace
returned at round `r` was published at round `r` before the return; so each of
its commands was invoked before it.
-/
namespace ConflictFreedom.WeakUniversal
open Object
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

variable [DecidableEq Op]

/-! ## A process's own slot never exceeds the round it works in -/

/-- The bound a process's own slot satisfies, by the process's local state. -/
def ownAt (q : Fin n) (slot : Seed (n := n) obj) : Local (n := n) obj → Prop
  | .idle => True
  | .collecting _ todo seed => q ∉ todo → slot.round ≤ seed.round
  | .ready _ seed => slot.round ≤ seed.round
  | .waiting _ r _ => slot.round < r
  | .publishing _ r _ => slot.round < r
  | .returning _ r _ => slot.round = r

/-- `ownAt` for every process. -/
def OwnBound (c : Configuration (n := n) obj) : Prop :=
  ∀ q, ownAt obj q (c.slots q) (c.localState q)

omit [DecidableEq Op] in
theorem ownBound_initial : OwnBound (n := n) obj (initial obj) := fun _ => trivial

theorem ownBound_step {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hc : OwnBound obj c) (hs : Step obj H c d) : OwnBound obj d := by
  cases hs with
  | invoke p op h order horder =>
    intro q
    by_cases hq : q = p
    · subst hq
      simp only [update, ite_true, ownAt]
      exact fun hn => absurd (horder.mem_iff.mpr (List.mem_finRange _)) hn
    · simpa only [update, hq, ite_false] using hc q
  | read p q' cmd todo seed h =>
    intro q
    by_cases hq : q = p
    · subst hq
      simp only [update, ite_true, ownAt]
      intro hnot
      by_cases hqq : q = q'
      · subst hqq; exact best_round_right obj seed (c.slots q)
      · have hold := hc q
        rw [h] at hold
        exact Nat.le_trans (hold (by simp [hqq, hnot])) (best_round_left obj seed (c.slots q'))
    · simpa only [update, hq, ite_false] using hc q
  | collected p cmd seed h =>
    intro q
    by_cases hq : q = p
    · subst hq
      have hold := hc q
      rw [h] at hold
      simp only [update, ite_true, ownAt]
      exact hold (List.not_mem_nil)
    · simpa only [update, hq, ite_false] using hc q
  | propose p cmd seed h hi =>
    intro q
    by_cases hq : q = p
    · subst hq
      have hold := hc q
      rw [h] at hold
      simp only [update, ite_true, ownAt]
      exact Nat.lt_succ_of_le hold
    · simpa only [update, hq, ite_false] using hc q
  | receive p cmd r proposal s flag h ho =>
    intro q
    by_cases hq : q = p
    · subst hq
      have hold := hc q
      rw [h] at hold
      simp only [update, ite_true]
      split
      · exact hold
      · exact Nat.le_of_lt hold
    · simpa only [update, hq, ite_false] using hc q
  | publish p _ _ _ _ | finish p _ _ _ _ =>
    intro q
    by_cases hq : q = p
    · subst hq
      simp only [update, ite_true, ownAt]
    · simpa only [update, hq, ite_false] using hc q

theorem ownBound {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : OwnBound obj c := by
  induction hc with
  | initial => exact ownBound_initial obj
  | step _ hs ih => exact ownBound_step obj ih hs

/-- Slots only grow: a publication is at a round above its slot's. -/
theorem step_slots_mono {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hc : OwnBound obj c) (hs : Step obj H c d) (q : Fin n) :
    (c.slots q).round ≤ (d.slots q).round := by
  cases hs with
  | publish p cmd r s h =>
    by_cases hq : q = p
    · subst hq
      have hold := hc q
      rw [h] at hold
      simp only [update, ite_true]
      exact Nat.le_of_lt hold
    · simp only [update, hq, ite_false]; exact Nat.le_refl _
  | _ => exact Nat.le_refl _

theorem Execution.slots_mono {H : Environment (n := n) obj} (run : Execution obj H)
    {u t : Nat} (hut : u ≤ t) (q : Fin n) :
    ((run.state u).slots q).round ≤ ((run.state t).slots q).round := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hut
  clear hut
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    refine Nat.le_trans ih ?_
    rw [← Nat.add_assoc]
    rcases run.next (u + d) with he | hs
    · rw [he]; exact Nat.le_refl _
    · exact step_slots_mono obj (ownBound obj (run.reachable obj _)) hs q

/-- A returned trace has been published at its round, by its own process. -/
theorem Execution.returned_published {H : Environment (n := n) obj} (run : Execution obj H)
    {t : Nat} {ret : Return (n := n) obj} (hret : ret ∈ (run.state t).returns) :
    ret.round ≤ ((run.state t).slots ret.command.process).round := by
  induction t with
  | zero => rw [run.initial_state] at hret; cases hret
  | succ t ih =>
    rcases run.next t with he | hs
    · rw [he] at hret ⊢; exact ih hret
    · have hmono := step_slots_mono obj (ownBound obj (run.reachable obj t)) hs
      have hc := ownBound obj (run.reachable obj t)
      have key : ∀ {c d : Configuration (n := n) obj}, Reachable obj H c → OwnBound obj c →
          Step obj H c d → ∀ ret ∈ d.returns, ret ∉ c.returns →
            ret.round ≤ (d.slots ret.command.process).round := by
        intro c d hr hc hs ret hd hn
        cases hs with
        | finish p cmd r s h =>
          rcases List.mem_cons.mp hd with rfl | hd
          · have hproc : cmd.process = p :=
              ((identity_invariant obj hr).active_tag p cmd
                (by simp [ledger, h, Local.command])).1
            have hold := hc p
            rw [h] at hold
            show r ≤ (c.slots cmd.process).round
            rw [hproc, hold]; exact Nat.le_refl _
          · exact absurd hd hn
        | _ => exact absurd hd hn
      by_cases hold : ret ∈ (run.state t).returns
      · exact Nat.le_trans (ih hold) (hmono _)
      · exact key (run.reachable obj t) hc hs ret hret hold

/-! ## Every command of an output was proposed by its own invoker -/

/-- A call is added only by a proposal, from the proposer's `ready` state. -/
theorem step_new_call {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) {call : Call (n := n) obj} (hd : call ∈ d.calls) :
    call ∈ c.calls ∨ ∃ p cmd seed, c.localState p = .ready cmd seed ∧
      call = ⟨seed.round + 1, p, (Tagged obj).appendMissing seed.trace cmd⟩ := by
  cases hs with
  | propose p cmd seed h hi =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Or.inr ⟨p, cmd, seed, h, rfl⟩
    · exact Or.inl hd
  | _ => exact Or.inl hd

/-- Every recorded call was a proposal. -/
theorem Execution.call_proposed {H : Environment (n := n) obj} (run : Execution obj H)
    {t : Nat} {call : Call (n := n) obj} (h : call ∈ (run.state t).calls) :
    ∃ u p cmd seed, (run.state u).localState p = .ready cmd seed ∧
      call = ⟨seed.round + 1, p, (Tagged obj).appendMissing seed.trace cmd⟩ := by
  induction t with
  | zero => rw [run.initial_state] at h; cases h
  | succ t ih =>
    rcases run.next t with he | hs
    · rw [he] at h; exact ih h
    · rcases step_new_call obj hs h with h' | ⟨p, cmd, seed, hl, rfl⟩
      · exact ih h'
      · exact ⟨t, p, cmd, seed, hl, rfl⟩

/-- **Rounds.**  A command of a proposal to round `r` was proposed, as its own
invoker's command, to some round `≤ r`.  Validity carries a command of a seed
back to a proposal of the previous round, and coverage makes that proposal
this run's own. -/
theorem Execution.own_proposal {H : Environment (n := n) obj} (run : Execution obj H)
    (hcov : run.Covers obj) (spec : ∀ r, (H (r + 1)).Specification) :
    ∀ r t (call : Call (n := n) obj), call ∈ (run.state t).calls → call.round = r →
      ∀ b, 0 < (Tagged obj).traceCount b call.trace →
        ∃ u seed, (run.state u).localState b.process = .ready b seed ∧ seed.round + 1 ≤ r := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro t call hcall hround b hb
    obtain ⟨u, p, cmd, seed, hl, rfl⟩ := run.call_proposed obj hcall
    change seed.round + 1 = r at hround
    by_cases hbc : b = cmd
    · subst hbc
      have hproc : b.process = p :=
        (((run.ledgerRun obj).valid u).active_tag p b (by simp [Execution.ledgerRun, ledger, hl,
          Local.command])).1
      rw [hproc]
      exact ⟨u, seed, hl, Nat.le_of_eq hround⟩
    · have hbs : 0 < (Tagged obj).traceCount b seed.trace := by
        change 0 < (Tagged obj).traceCount b ((Tagged obj).appendMissing seed.trace cmd) at hb
        unfold Object.appendMissing at hb
        split at hb
        · rw [(Tagged obj).traceCount_append b seed.trace
            (Quotient.mk (Tagged obj).traceSetoid [cmd])] at hb
          have : (Tagged obj).traceCount b (Quotient.mk (Tagged obj).traceSetoid [cmd]) = 0 := by
            change [cmd].count b = 0
            simp [Ne.symm hbc]
          omega
        · exact hb
      have hsup : Supported obj H seed := by
        have := (invariant obj (run.reachable obj u)).localState p
        rw [hl] at this
        exact this
      rcases hsup with ⟨_, htr⟩ | ⟨hpos, q, flag, hq⟩
      · rw [htr] at hbs; exact absurd hbs (Nat.lt_irrefl 0)
      · obtain ⟨k, hk⟩ : ∃ k, seed.round = k + 1 := ⟨seed.round - 1, by omega⟩
        rw [hk] at hq
        obtain ⟨s', ⟨q', hq'⟩, hocc⟩ := (spec k).validity.occurs q seed.trace flag hq b 0
          (by change 0 < ((Tagged obj).traceResponses b _ _).length
              rw [(Tagged obj).traceResponses_length]; exact hbs)
        obtain ⟨t', ht'⟩ := hcov k q' s' hq'
        obtain ⟨u', seed', hl', hle⟩ := ih (k + 1) (by omega) t' ⟨k + 1, q', s'⟩ ht' rfl b
          (by
            have := hocc
            change 0 < ((Tagged obj).traceResponses b _ _).length at this
            rwa [(Tagged obj).traceResponses_length] at this)
        exact ⟨u', seed', hl', by omega⟩

/-! ## An invoker proposes above every round published before it invoked -/

/-- The floor on the rounds process `b.process` works in while running `b`:
above the round `ρ` of slot `q` when `b` was invoked, once `q` is read. -/
def floorAt (q : Fin n) (ρ : Nat) (b : Cmd n Op) : Local (n := n) obj → Prop
  | .idle => True
  | .collecting b' todo seed => b' = b → q ∉ todo → ρ ≤ seed.round
  | .ready b' seed => b' = b → ρ ≤ seed.round
  | .waiting b' r _ => b' = b → ρ < r
  | .publishing b' r _ => b' = b → ρ < r
  | .returning b' r _ => b' = b → ρ < r

theorem floor_step {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) {q : Fin n} {ρ : Nat} {b : Cmd n Op}
    (hf : floorAt obj q ρ b (c.localState b.process)) (hslot : ρ ≤ (c.slots q).round) :
    floorAt obj q ρ b (d.localState b.process) := by
  cases hs with
  | invoke p op h order horder =>
    by_cases hp : b.process = p
    · rw [hp]; simp only [update, ite_true, floorAt]
      exact fun _ hn => absurd (horder.mem_iff.mpr (List.mem_finRange _)) hn
    · simpa only [update, hp, ite_false] using hf
  | read p q' cmd todo seed h =>
    by_cases hp : b.process = p
    · rw [hp] at hf ⊢
      rw [h] at hf
      simp only [update, ite_true, floorAt]
      intro hb hnot
      by_cases hqq : q = q'
      · subst hqq; exact Nat.le_trans hslot (best_round_right obj seed (c.slots q))
      · exact Nat.le_trans (hf hb (by simp [hqq, hnot])) (best_round_left obj seed (c.slots q'))
    · simpa only [update, hp, ite_false] using hf
  | collected p cmd seed h =>
    by_cases hp : b.process = p
    · rw [hp] at hf ⊢
      rw [h] at hf
      simp only [update, ite_true, floorAt]
      exact fun hb => hf hb List.not_mem_nil
    · simpa only [update, hp, ite_false] using hf
  | propose p cmd seed h hi =>
    by_cases hp : b.process = p
    · rw [hp] at hf ⊢
      rw [h] at hf
      simp only [update, ite_true, floorAt]
      exact fun hb => Nat.lt_succ_of_le (hf hb)
    · simpa only [update, hp, ite_false] using hf
  | receive p cmd r proposal s flag h ho =>
    by_cases hp : b.process = p
    · rw [hp] at hf ⊢
      rw [h] at hf
      simp only [update, ite_true]
      split
      · exact hf
      · exact fun hb => Nat.le_of_lt (hf hb)
    · simpa only [update, hp, ite_false] using hf
  | publish p cmd r s h =>
    by_cases hp : b.process = p
    · rw [hp] at hf ⊢
      rw [h] at hf
      simp only [update, ite_true, floorAt]
      exact hf
    · simpa only [update, hp, ite_false] using hf
  | finish p cmd r s h =>
    by_cases hp : b.process = p
    · rw [hp]; simp only [update, ite_true, floorAt]
    · simpa only [update, hp, ite_false] using hf

/-- An invocation starts a collect of every slot, in some order. -/
theorem step_new_invocation {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) {b : Cmd n Op} (hd : b ∈ d.invocations) (hn : b ∉ c.invocations) :
    ∃ order : List (Fin n), order.Perm (List.finRange n) ∧
      d.localState b.process = .collecting b order (zeroSeed obj) := by
  cases hs with
  | invoke p op h order horder =>
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨order, horder, by simp [update]⟩
    · exact absurd hd hn
  | _ => exact absurd hd hn

/-- **The floor.**  From its invocation on, process `b.process` works on `b`
only in rounds above the round slot `q` had then. -/
theorem Execution.floor {H : Environment (n := n) obj} (run : Execution obj H)
    {b : Cmd n Op} {t0 : Nat} (hnot : b ∉ (run.state t0).invocations)
    (hin : b ∈ (run.state (t0 + 1)).invocations) (q : Fin n) :
    ∀ d, floorAt obj q ((run.state t0).slots q).round b
      ((run.state (t0 + 1 + d)).localState b.process) := by
  intro d
  induction d with
  | zero =>
    rcases run.next t0 with he | hs
    · rw [he] at hin; exact absurd hin hnot
    · obtain ⟨order, horder, hloc⟩ := step_new_invocation obj hs hin hnot
      rw [Nat.add_zero, hloc]
      exact fun _ hn => absurd (horder.mem_iff.mpr (List.mem_finRange _)) hn
  | succ d ih =>
    rw [← Nat.add_assoc]
    rcases run.next (t0 + 1 + d) with he | hs
    · rw [he]; exact ih
    · exact floor_step obj hs ih (run.slots_mono obj (by omega) q)

/-! ## Returned traces hold invoked commands -/

/-- **Algorithm 1 needs no temporal contract from GCA.**  If every GCA input is
a proposal of the run, the six properties make every command of a returned
trace an invoked one. -/
theorem Execution.returnsInvokedBy_of_covers {H : Environment (n := n) obj}
    (run : Execution obj H) (hcov : run.Covers obj) (spec : ∀ r, (H (r + 1)).Specification) :
    run.ReturnsInvokedBy obj := by
  intro k ret hret b hb
  apply Classical.byContradiction
  intro hnot
  obtain ⟨⟨hpos, q0, hq0⟩, _⟩ := (invariant obj (run.reachable obj k)).returns ret hret
  obtain ⟨m, hm⟩ : ∃ m, ret.round = m + 1 := ⟨ret.round - 1, by omega⟩
  rw [hm] at hq0
  obtain ⟨s', ⟨q', hq'⟩, hocc⟩ := (spec m).validity.occurs q0 ret.trace true hq0 b 0
    (by change 0 < ((Tagged obj).traceResponses b _ _).length
        rw [(Tagged obj).traceResponses_length]; exact hb)
  obtain ⟨t', ht'⟩ := hcov m q' s' hq'
  obtain ⟨u, seed, hl, hle⟩ := run.own_proposal obj hcov spec (m + 1) t' ⟨m + 1, q', s'⟩ ht' rfl b
    (by
      have := hocc
      change 0 < ((Tagged obj).traceResponses b _ _).length at this
      rwa [(Tagged obj).traceResponses_length] at this)
  have hbu : b ∈ (run.state u).invocations :=
    (((run.ledgerRun obj).valid u).active_tag b.process b (by
      simp [Execution.ledgerRun, ledger, hl, Local.command])).2.2
  -- The first tick at which `b` is invoked comes after the return.
  obtain ⟨m', hm', hleast⟩ := exists_least (fun t => b ∈ (run.state t).invocations) ⟨u, hbu⟩
  have hkm : k < m' := by
    apply Nat.lt_of_not_le
    intro hle'
    exact hnot ((run.ledgerRun obj).invoked_mono hle' hm')
  obtain ⟨t0, rfl⟩ : ∃ t0, m' = t0 + 1 := ⟨m' - 1, by omega⟩
  have hnot0 : b ∉ (run.state t0).invocations := fun h => by
    have := hleast t0 h; omega
  have hut : t0 + 1 ≤ u := hleast u hbu
  have hfl := run.floor obj hnot0 hm' ret.command.process (u - (t0 + 1))
  rw [show t0 + 1 + (u - (t0 + 1)) = u by omega, hl] at hfl
  have hρ := hfl rfl
  have h1 := run.returned_published obj hret
  have h2 := run.slots_mono obj (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hkm) : k ≤ t0 + 1)
    ret.command.process
  have h3 := run.slots_mono obj (by omega : k ≤ t0) ret.command.process
  omega

/-- **Algorithm 1 over any GCA meeting the six properties is linearizable**,
provided the GCA history is the run's own: at every finite boundary… -/
theorem Execution.covered_finite_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (hcov : run.Covers obj) (spec : ∀ r, (H (r + 1)).Specification)
    (N : Nat) : ∃ x, (Tagged obj).Linearizes (run.history obj) N x :=
  run.finite_linearization obj (run.callsCovered obj hcov) spec
    (run.returnsInvokedBy_of_covers obj hcov spec) N

/-- …and by one growing chain of sequential orders. -/
theorem Execution.covered_chain_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (hcov : run.Covers obj) (spec : ∀ r, (H (r + 1)).Specification) :
    ∃ x : Nat → List (Cmd n Op),
      (∀ N, (Tagged obj).Linearizes (run.history obj) N (x N)) ∧
      (∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :=
  run.chain_linearization obj (run.callsCovered obj hcov) spec
    (run.returnsInvokedBy_of_covers obj hcov spec)

end ConflictFreedom.WeakUniversal
