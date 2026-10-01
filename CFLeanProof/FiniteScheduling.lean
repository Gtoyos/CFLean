import CFLeanProof.Scheduling

/-! Finite-process scheduling facts shared by both universal constructions.
No fairness assumption is needed: processes that stop stepping have a common
finite cutoff, and can only have inserted records of bounded round number. -/
namespace ConflictFreedom

/-- A function on the finite process set has a uniform bound. -/
theorem fin_bounded : ∀ (m : Nat) (h : Fin m → Nat), ∃ N, ∀ p, h p ≤ N := by
  intro m
  induction m with
  | zero => intro h; exact ⟨0, fun p => Fin.elim0 p⟩
  | succ m ih =>
      intro h
      obtain ⟨N, hN⟩ := ih (fun p => h p.succ)
      refine ⟨max (h 0) N, ?_⟩
      intro p
      refine Fin.cases (Nat.le_max_left _ _) (fun p => ?_) p
      exact Nat.le_trans (hN p) (Nat.le_max_right _ _)

namespace FiniteScheduling
variable {n : Nat} (actor : Nat → Option (Fin n))

/-- `p` is scheduled infinitely often. -/
def Stepping (p : Fin n) : Prop := ∀ N, ∃ t, N ≤ t ∧ actor t = some p

/-- The manuscript's "there is a suffix in which only `Φ` takes steps",
**tolerating instants at which the scheduler idles**.

Requiring `actor t = some p` at *every* late instant is strictly stronger:
`Counterexamples.intermittentlyStalled` is `Execution.Solo` and live yet never
continuously scheduled.  Every solo argument below therefore takes `SoloFrom`,
not continuous scheduling. -/
structure SoloFrom (N : Nat) (p : Fin n) : Prop where
  /-- After `N`, nobody but `p` is scheduled. -/
  own : ∀ t q, N ≤ t → actor t = some q → q = p
  /-- `p` itself keeps being scheduled. -/
  sched : ∀ M, ∃ t, M ≤ t ∧ actor t = some p

/-- A continuously scheduled process is solo from that point on. -/
theorem SoloFrom.of_continuous {N : Nat} {p : Fin n}
    (h : ∀ t, N ≤ t → actor t = some p) : SoloFrom actor N p :=
  ⟨fun t _ ht hq => Option.some.inj (hq.symm.trans (h t ht)),
    fun M => ⟨max M N, Nat.le_max_left _ _, h _ (Nat.le_max_right _ _)⟩⟩

/-- After a finite cutoff, every scheduled process takes infinitely many steps. -/
theorem eventually_stepping : ∃ N, ∀ t p, N ≤ t → actor t = some p → Stepping actor p := by
  classical
  have bounds : ∀ p, ∃ N, ∀ t, N ≤ t → actor t = some p → Stepping actor p := by
    intro p
    by_cases hp : Stepping actor p
    · exact ⟨0, fun _ _ _ => hp⟩
    · obtain ⟨N, hN⟩ := Classical.not_forall.mp hp
      exact ⟨N, fun t ht ha => (hN ⟨t, ht, ha⟩).elim⟩
  obtain ⟨N, hN⟩ := fin_bounded n (fun p => Classical.choose (bounds p))
  exact ⟨N, fun t p ht ha => Classical.choose_spec (bounds p) t
    (Nat.le_trans (hN p) ht) ha⟩

/-- New records belong to their inserting actor. Consequently all sufficiently
high-round records belong to processes that keep stepping. This abstracts the
paper's choice of the largest round reached before faulty processes stop. -/
theorem high_records_stepping {Record : Type} (records : Nat → List Record)
    (owner : Record → Fin n) (round : Record → Nat)
    (mono : ∀ {s t}, s ≤ t → ∀ c ∈ records s, c ∈ records t)
    (inserted : ∀ t c, c ∈ records (t + 1) → c ∉ records t → actor t = some (owner c))
    (bounded : ∀ t, ∃ B, ∀ c ∈ records t, round c ≤ B) :
    ∃ B, ∀ t c, c ∈ records t → B < round c → Stepping actor (owner c) := by
  classical
  obtain ⟨N, hN⟩ := eventually_stepping actor
  obtain ⟨B, hB⟩ := bounded N
  refine ⟨B, fun t c hc hround => ?_⟩
  have hnew : c ∉ records N := fun hm => (Nat.not_lt_of_ge (hB c hm)) hround
  have hNt : N ≤ t := by
    apply Nat.le_of_not_gt
    intro ht
    exact hnew (mono (Nat.le_of_lt ht) c hc)
  obtain ⟨u, hu, -, hbefore, hafter⟩ := first_appearance (P := fun u => c ∈ records u) hNt hnew hc
  exact hN u (owner c) hu (inserted u c hafter hbefore)

end FiniteScheduling
end ConflictFreedom
