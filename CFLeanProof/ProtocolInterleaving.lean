import CFLeanProof.UniversalProtocol

/-! A single global scheduler interleaving all operational GCA instances. Each
global protocol event advances exactly one round's local clock, and its actor
must match the actor at that local protocol time. This supplies the clock
transfer that a family of independent `GCA.Protocol` values does not provide. -/
namespace ConflictFreedom.UniversalProtocol

variable {State Op Response : Type} {n : Nat}
    (obj : Object State Op Response) [DecidableEq Op]

/-- Global interleaving of the protocol family. Round numbers here are the
actual positive universal-construction round numbers (round zero is permitted
but unused by the programs). -/
structure Interleaving (f : Family (n := n) obj) where
  event : Nat → Option (Nat × Fin n)
  clock : Nat → Nat → Nat
  initial_clock : ∀ r, clock 0 r = 0
  clock_next : ∀ t r, clock (t + 1) r =
    if ∃ p, event t = some (r, p) then clock t r + 1 else clock t r
  actor_matches : ∀ t r p, event t = some (r, p) →
    (f.protocol r).actor (clock t r) = some p

namespace Interleaving
variable {f : Family (n := n) obj} (e : Interleaving obj f)

/-- Process `p` receives infinitely many global events in round `r`. -/
def InfiniteSteps (r : Nat) (p : Fin n) : Prop :=
  ∀ N, ∃ t, N ≤ t ∧ e.event t = some (r, p)

omit [DecidableEq Op] in
theorem clock_step_mono (t r : Nat) : e.clock t r ≤ e.clock (t + 1) r := by
  rw [e.clock_next]
  split <;> omega

omit [DecidableEq Op] in
theorem clock_mono {t u r : Nat} (htu : t ≤ u) :
    e.clock t r ≤ e.clock u r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      exact Nat.le_trans (ih (by omega)) (by
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          e.clock_step_mono obj (t + d) r)

omit [DecidableEq Op] in
theorem clock_succ_of_event {t r : Nat} {p : Fin n}
    (h : e.event t = some (r, p)) :
    e.clock (t + 1) r = e.clock t r + 1 := by
  rw [e.clock_next]
  simp [h]

omit [DecidableEq Op] in
/-- Infinitely many global events in one round make that round's local clock
unbounded. -/
theorem clock_unbounded {r : Nat} {p : Fin n} (hp : e.InfiniteSteps obj r p) :
    ∀ N, ∃ t, N ≤ e.clock t r := by
  intro N
  induction N with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ N ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨u, htu, hu⟩ := hp t
    refine ⟨u + 1, ?_⟩
    rw [e.clock_succ_of_event obj hu]
    exact Nat.succ_le_succ (Nat.le_trans ht (e.clock_mono obj htu))

omit [DecidableEq Op] in
/-- The global/local clock alignment transfers infinite scheduling to the
`GCA.Protocol` progress predicate. -/
theorem protocol_infiniteSteps {r : Nat} {p : Fin n}
    (hp : e.InfiniteSteps obj r p) : (f.protocol r).InfiniteSteps p := by
  intro N
  obtain ⟨t, ht⟩ := e.clock_unbounded obj hp N
  obtain ⟨u, htu, hu⟩ := hp t
  refine ⟨e.clock u r, Nat.le_trans ht (e.clock_mono obj htu), ?_⟩
  exact e.actor_matches u r p hu

/-- Under the author's wait-free snapshot assumption, a caller scheduled
infinitely often in the global interleaving returns from its GCA round. -/
theorem round_returned (hw : f.SnapshotWaitFree obj) {r : Nat} {p : Fin n}
    (hp : e.InfiniteSteps obj r p) :
    ∃ t c, (f.environment obj r).output p = some (t, c) :=
  f.round_returned obj hw r p (e.protocol_infiniteSteps obj hp)

end Interleaving
end ConflictFreedom.UniversalProtocol
