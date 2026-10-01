import CFLeanProof.HelpingUniversal

/-! Each process calls each GCA instance at most once. These facts follow from
control flow and register collects, independently of GCA safety or liveness. -/
namespace ConflictFreedom
namespace WeakUniversal
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-- A call's identity, its process and round. -/
def Call.key (call : Call (n := n) obj) : Fin n × Nat := (call.process, call.round)

/-- Every call is at most its process's current round, and no process calls a
round twice. -/
structure CallTracking (round : Fin n → Nat) (calls : List (Call (n := n) obj)) : Prop where
  bounded : ∀ call ∈ calls, call.round ≤ round call.process
  unique : (calls.map (Call.key obj)).Nodup

theorem CallTracking.advance {old next : Fin n → Nat} {calls : List (Call (n := n) obj)}
    (hc : CallTracking obj old calls) (hm : ∀ p, old p ≤ next p) : CallTracking obj next calls :=
  ⟨fun call hcall => Nat.le_trans (hc.bounded call hcall) (hm call.process), hc.unique⟩

theorem CallTracking.insert {old next : Fin n → Nat} {calls : List (Call (n := n) obj)}
    (hc : CallTracking obj old calls) (hm : ∀ p, old p ≤ next p) (call : Call (n := n) obj)
    (hfresh : old call.process < call.round) (hbound : call.round ≤ next call.process) :
    CallTracking obj next (call :: calls) := by
  constructor
  · intro c h
    rcases List.mem_cons.mp h with rfl | h
    · exact hbound
    · exact Nat.le_trans (hc.bounded c h) (hm c.process)
  · apply List.nodup_cons.mpr
    refine ⟨?_, hc.unique⟩
    intro h
    obtain ⟨prev, hprev, he⟩ := List.mem_map.mp h
    have hp := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    change prev.process = call.process at hp
    change prev.round = call.round at hr
    have hb := hc.bounded prev hprev
    rw [hp, hr] at hb
    omega

/-- During the initial collect, the process's own S slot preserves the last
completed round even before that slot has been read. -/
def Local.round : Local (n := n) obj → Nat → Nat
  | .idle, stored => stored
  | .collecting _ _ seed, stored => max stored seed.round
  | .ready _ seed, _ => seed.round
  | .waiting _ r _, _ | .publishing _ r _, _ | .returning _ r _, _ => r

/-- The round `p` has reached in Algorithm 1. -/
def currentRound (c : Configuration (n := n) obj) (p : Fin n) : Nat :=
  (c.localState p).round obj (c.slots p).round

/-- How `S[p]` relates to `p`'s local round: a collect that has read `S[p]`
carries at least its round, and a returning process has just written it. -/
def LocalRoundShape (p : Fin n) (slot : Seed (n := n) obj) : Local (n := n) obj → Prop
  | .collecting _ todo seed => p ∈ todo ∨ slot.round ≤ seed.round
  | .returning _ r _ => slot.round = r
  | _ => True

/-- `LocalRoundShape` for every process. -/
def RoundShape (c : Configuration (n := n) obj) : Prop :=
  ∀ p, LocalRoundShape obj p (c.slots p) (c.localState p)

private theorem shape_update (c : Configuration (n := n) obj) (hc : RoundShape obj c)
    (p : Fin n) (l : Local (n := n) obj)
    (hl : LocalRoundShape obj p (c.slots p) l) :
    ∀ q, LocalRoundShape obj q (c.slots q) (update c.localState p l q) := by
  intro q
  by_cases he : q = p
  · subst q; simpa [update] using hl
  · simpa [update, he] using hc q

private theorem shape_update_slot (c : Configuration (n := n) obj) (hc : RoundShape obj c)
    (p : Fin n) (l : Local (n := n) obj) (s : Seed (n := n) obj)
    (hl : LocalRoundShape obj p s l) :
    ∀ q, LocalRoundShape obj q (update c.slots p s q) (update c.localState p l q) := by
  intro q
  by_cases he : q = p
  · subst q; simpa [update] using hl
  · simpa [update, he] using hc q

variable [DecidableEq Op]

theorem round_shape_step {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hc : RoundShape obj c) (hs : Step obj H c d) : RoundShape obj d := by
  cases hs with
  | invoke p op h order horder =>
    apply shape_update obj c hc p
    left; exact horder.mem_iff.mpr (List.mem_finRange p)
  | read p q cmd todo seed h =>
    apply shape_update obj c hc p
    have hp := hc p
    rw [h] at hp
    rcases hp with hm | hb
    · rcases List.mem_cons.mp hm with he | hm
      · subst q
        right
        rw [best_round]
        exact Nat.le_max_right _ _
      · exact Or.inl hm
    · right
      rw [best_round]
      exact Nat.le_trans hb (Nat.le_max_left _ _)
  | receive p cmd r proposal s flag h ho =>
    apply shape_update obj c hc p
    split <;> trivial
  | publish p cmd r s h => exact shape_update_slot obj c hc p _ _ rfl
  | collected p _ _ _ | propose p _ _ _ _ | finish p _ _ _ _ =>
      exact shape_update obj c hc p _ trivial

omit [DecidableEq Op] in
private theorem round_update (c : Configuration (n := n) obj) (p : Fin n) (l : Local (n := n) obj)
    (h : currentRound obj c p ≤ l.round obj (c.slots p).round) :
    ∀ q, currentRound obj c q ≤ (update c.localState p l q).round obj (c.slots q).round := by
  intro q
  by_cases he : q = p
  · subst q; simpa [update] using h
  · simp [update, he, currentRound]

omit [DecidableEq Op] in
private theorem round_update_slot (c : Configuration (n := n) obj) (p : Fin n)
    (l : Local (n := n) obj) (s : Seed (n := n) obj)
    (h : currentRound obj c p ≤ l.round obj s.round) :
    ∀ q, currentRound obj c q ≤ (update c.localState p l q).round obj (update c.slots p s q).round := by
  intro q
  by_cases he : q = p
  · subst q; simpa [update] using h
  · simp [update, he, currentRound]

theorem step_round_mono {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hc : RoundShape obj c) (hs : Step obj H c d) : ∀ p, currentRound obj c p ≤ currentRound obj d p := by
  cases hs with
  | invoke p op h =>
    apply round_update obj c p
    simp [currentRound, h, Local.round, zeroSeed]
  | read p q cmd todo seed h =>
    apply round_update obj c p
    simp only [currentRound, h, Local.round, best_round]
    omega
  | collected p cmd seed h =>
    apply round_update obj c p
    have hp := hc p
    rw [h] at hp
    have hb : (c.slots p).round ≤ seed.round := hp.elim (fun hm => False.elim (List.not_mem_nil hm)) id
    simp only [currentRound, h, Local.round]
    omega
  | propose p cmd seed h hi =>
    apply round_update obj c p
    simp [currentRound, h, Local.round]
  | receive p cmd r proposal s flag h ho =>
    apply round_update obj c p
    by_cases he : flag = true ∧ 0 < (Tagged obj).traceCount cmd s <;>
      simp [currentRound, h, he, Local.round]
  | publish p cmd r s h =>
    apply round_update_slot obj c p
    simp [currentRound, h, Local.round]
  | finish p cmd r s h =>
    apply round_update obj c p
    have hp := hc p
    rw [h] at hp
    change (c.slots p).round = r at hp
    simp [currentRound, h, Local.round, hp]

theorem call_tracking_step {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hshape : RoundShape obj c) (hc : CallTracking obj (currentRound obj c) c.calls)
    (hs : Step obj H c d) : CallTracking obj (currentRound obj d) d.calls := by
  have hm := step_round_mono obj hshape hs
  cases hs with
  | propose p cmd seed h hi =>
    apply CallTracking.insert obj hc hm
    · simp [currentRound, h, Local.round]
    · simp [currentRound, update, Local.round]
  | _ => exact hc.advance obj hm

theorem round_invariant {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : RoundShape obj c ∧ CallTracking obj (currentRound obj c) c.calls := by
  induction hc with
  | initial => exact ⟨fun _ => trivial, (fun _ h => nomatch h), List.nodup_nil⟩
  | step _ hs ih => exact ⟨round_shape_step obj ih.1 hs, call_tracking_step obj ih.1 ih.2 hs⟩

/-- The weak construction also cannot call one GCA instance twice: every fresh
invocation's collect includes the process's own previous publication. -/
theorem gca_participation_unique {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : (c.calls.map (Call.key obj)).Nodup := (round_invariant obj hc).2.unique

end WeakUniversal

namespace HelpingUniversal
open WeakUniversal (Call Environment CallTracking update best)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-- The round an Algorithm 3 process is at: its base's, or that of its call. -/
def Local.round : Local (n := n) obj → Nat
  | .idle s | .announcing _ s | .collecting _ _ s | .gathering _ s _ _
  | .publishing _ s | .checking _ s _ _ => s.round
  | .waiting _ r _ => r

private theorem round_update (f : Fin n → Local (n := n) obj) (p : Fin n) (l : Local (n := n) obj)
    (h : (f p).round obj ≤ l.round obj) :
    ∀ q, (f q).round obj ≤ (update f p l q).round obj := by
  intro q
  by_cases he : q = p
  · subst q; simpa [update] using h
  · simp [update, he]

variable [DecidableEq Op]

theorem step_round_mono {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) : ∀ p, (c.localState p).round obj ≤ (d.localState p).round obj := by
  cases hs with
  | readStart p q cmd todo seed h =>
    apply round_update obj _ p _
    simpa only [h, Local.round, WeakUniversal.best_round] using Nat.le_max_left seed.round (c.slots q).round
  | receive p cmd r proposal s flag h ho =>
    apply round_update obj _ p _
    by_cases he : flag = true <;> simp [h, he, Local.round]
  | invoke p _ _ h | announce p _ _ h | collectedStart p _ _ h | readAnnouncement p _ _ _ _ _ h
  | propose p _ _ _ h _ | publish p _ _ h | readCheck p _ _ _ _ _ h | retry p _ _ _ h _
  | finish p _ _ _ h _ => exact round_update obj _ p _ (by simp [h, Local.round])

theorem call_tracking_step {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hc : CallTracking obj (fun p => (c.localState p).round obj) c.calls) (hs : Step obj H c d) :
    CallTracking obj (fun p => (d.localState p).round obj) d.calls := by
  have hm := step_round_mono obj hs
  cases hs with
  | propose p cmd seed commands h hi =>
    apply CallTracking.insert obj hc hm
    · simp [h, Local.round]
    · simp [update, Local.round]
  | _ => exact hc.advance obj hm

theorem call_tracking {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : CallTracking obj (fun p => (c.localState p).round obj) c.calls := by
  induction hc with
  | initial => exact ⟨(fun _ h => nomatch h), List.nodup_nil⟩
  | step _ hs ih => exact call_tracking_step obj ih hs

/-- The persistent local round prevents reusing a GCA instance after a helped return. -/
theorem gca_participation_unique {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : (c.calls.map (Call.key obj)).Nodup := (call_tracking obj hc).unique

end HelpingUniversal
end ConflictFreedom
