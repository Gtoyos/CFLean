import CFLeanProof.SharedScheduler

/-! # `SnapshotWaitFree` is satisfied by stuttering snapshot implementations

`GCA.Protocol.alwaysAcknowledged_waitFree` shows that the *ideal atomic*
interface — every scheduled step of a caller completes its outstanding snapshot
operation — satisfies the author's assumption.  All three witness schedules use
it, which invites the question of whether the assumption has any other models:
if the only protocol satisfying `SnapshotWaitFree` were the one that never
stutters, then "assume a wait-free snapshot object" would silently be "assume an
atomic one", and every result under the hypothesis would be about that special
case.

It is not.  `waitFree_of_acknowledged_cofinal` shows the assumption only asks
that an active caller be *eventually* acknowledged, arbitrarily often; a caller
may take any finite number of internal steps in between, which is exactly what a
real snapshot algorithm does.  `alternating` is a protocol that acknowledges only
every other step and still satisfies the interface.
-/
namespace ConflictFreedom.GCA.Protocol
open Object
variable {State Op Response P : Type} [DecidableEq P]
variable {obj : Object State Op Response} (e : Protocol obj P)

/-- A snapshot stage is never left by an unacknowledged step: stages `2` and `5`
are the local calculations, and only those advance without acknowledgement. -/
theorem phase_const_of_unacknowledged {p : P} {k : Nat} (hk : SnapshotStage k)
    {t : Nat} (ht : e.phase t p = k) {u : Nat} (htu : t ≤ u)
    (hno : ∀ w, t ≤ w → w < u → e.actor w = some p → e.acknowledged w = false) :
    e.phase u p = k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  induction d with
  | zero => exact ht
  | succ d ih =>
    have hprev : e.phase (t + d) p = k :=
      ih (by omega) (fun w hw hwu => hno w hw (by omega))
    rw [show t + (d + 1) = (t + d) + 1 from by omega, phase]
    by_cases hact : e.actor (t + d) = some p
    · rw [ite_eq_left hact, hprev, hno (t + d) (by omega) (by omega) hact]
      unfold advance
      have hk2 : ¬ (k = 2) := by unfold SnapshotStage at hk; omega
      have hk5 : ¬ (k = 5) := by unfold SnapshotStage at hk; omega
      rw [ite_eq_right]
      rintro ⟨-, h | h | h⟩
      · exact absurd h hk2
      · exact absurd h hk5
      · exact absurd h (by simp)
    · rw [ite_eq_right hact]; exact hprev

/-- **The interface assumption only asks for eventual acknowledgement.**  A
caller that keeps taking steps and is acknowledged at arbitrarily late times
satisfies `SnapshotWaitFree`, however many unacknowledged internal steps it
takes in between. -/
theorem waitFree_of_acknowledged_cofinal
    (h : ∀ p, e.InfiniteSteps p → ∀ N,
      ∃ u, N ≤ u ∧ e.actor u = some p ∧ e.acknowledged u = true) :
    e.SnapshotWaitFree := by
  intro p hp k hk t ht
  obtain ⟨u, ⟨hu, hact, hack⟩, hmin⟩ :=
    exists_least (fun u => t ≤ u ∧ e.actor u = some p ∧ e.acknowledged u = true) (h p hp t)
  refine ⟨u, hu, ?_, hact, hack⟩
  refine e.phase_const_of_unacknowledged hk ht hu ?_
  intro w hw hwu hactw
  cases hackw : e.acknowledged w with
  | false => rfl
  | true => exact absurd (hmin w ⟨hw, hactw, hackw⟩) (by omega)

/-- The ideal atomic interface is the special case in which every step is
acknowledged: `GCA.Protocol.alwaysAcknowledged_waitFree`, recovered as a
corollary of `waitFree_of_acknowledged_cofinal`. -/
theorem alwaysAcknowledged_waitFree' (ha : ∀ t, e.acknowledged t = true) :
    e.SnapshotWaitFree :=
  e.waitFree_of_acknowledged_cofinal (fun p hp N => by
    obtain ⟨u, hu, hact⟩ := hp N
    exact ⟨u, hu, hact, ha u⟩)

/-! ### A genuinely stuttering protocol -/

/-- One participant, scheduled at every tick, whose snapshot operations complete
only on even ticks: half of its steps are internal steps of the snapshot
implementation. -/
def alternating (p₀ : P) (input : P → obj.Trace) : Protocol obj P where
  participants := [p₀]
  input := input
  actor := fun _ => some p₀
  actor_valid := by
    intro t p hp
    have : p₀ = p := Option.some.inj hp
    subst this
    exact List.mem_cons_self ..
  acknowledged := fun t => decide (t % 2 = 0)

omit [DecidableEq P] in
theorem alternating_stutters (p₀ : P) (input : P → obj.Trace) :
    ∃ t, (alternating p₀ input).acknowledged t = false :=
  ⟨1, by simp [alternating]⟩

/-- **The assumption has stuttering models.** -/
theorem alternating_waitFree (p₀ : P) (input : P → obj.Trace) :
    (alternating (obj := obj) p₀ input).SnapshotWaitFree := by
  refine (alternating p₀ input).waitFree_of_acknowledged_cofinal ?_
  intro p hinf N
  obtain ⟨w, -, hw⟩ := hinf 0
  have hp : p₀ = p := Option.some.inj hw
  refine ⟨2 * N, by omega, ?_, ?_⟩
  · show some p₀ = some p
    rw [hp]
  · show decide (2 * N % 2 = 0) = true
    simp [Nat.mul_mod_right]

end ConflictFreedom.GCA.Protocol
