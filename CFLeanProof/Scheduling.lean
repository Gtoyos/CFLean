import Std

/-! Termination principles for the progress proofs.

The manuscript's progress arguments say that a process cannot stay inside one
iteration of its loop forever, and that its round number keeps growing until it
commits. Both are instances of the descent principles below: no sequence of
natural numbers decreases infinitely often, and no lexicographic pair whose
first component is bounded does either. -/
namespace ConflictFreedom

/-- A non-increasing sequence of naturals cannot strictly decrease infinitely
often. -/
theorem no_infinite_descent {f : Nat → Nat} (hmono : ∀ t, f (t + 1) ≤ f t)
    (hinf : ∀ N, ∃ t, N ≤ t ∧ f (t + 1) < f t) : False := by
  have hle : ∀ d a, f (a + d) ≤ f a := by
    intro d
    induction d with
    | zero => intro a; exact Nat.le_refl _
    | succ d ih => intro a; exact Nat.le_trans (hmono (a + d)) (ih a)
  have key : ∀ k, ∃ t, f t + k ≤ f 0 := by
    intro k
    induction k with
    | zero => exact ⟨0, Nat.le_refl _⟩
    | succ k ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨u, hu, hdec⟩ := hinf t
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hu
      exact ⟨t + d + 1, by have := hle d t; omega⟩
  obtain ⟨t, ht⟩ := key (f 0 + 1)
  omega

/-- Lexicographic descent. The first component never decreases and stays under a
bound; every step either raises it or leaves the second component no larger.
Then strict progress cannot happen infinitely often. -/
theorem no_infinite_lex_descent {r q : Nat → Nat} {B : Nat} (hbound : ∀ t, r t ≤ B)
    (hmono : ∀ t, r t ≤ r (t + 1))
    (hstep : ∀ t, r t < r (t + 1) ∨ q (t + 1) ≤ q t)
    (hinf : ∀ N, ∃ t, N ≤ t ∧ (r t < r (t + 1) ∨ q (t + 1) < q t)) : False := by
  classical
  by_cases hA : ∀ N, ∃ t, N ≤ t ∧ r t < r (t + 1)
  · refine no_infinite_descent (f := fun t => B - r t) ?_ ?_
    · intro t
      have := hmono t
      omega
    · intro N
      obtain ⟨t, ht, hlt⟩ := hA N
      have := hbound (t + 1)
      exact ⟨t, ht, by omega⟩
  · obtain ⟨N, hN⟩ := Classical.not_forall.mp hA
    have hflat : ∀ t, N ≤ t → ¬ r t < r (t + 1) := fun t ht hlt => hN ⟨t, ht, hlt⟩
    refine no_infinite_descent (f := fun k => q (N + k)) ?_ ?_
    · intro k
      rcases hstep (N + k) with h | h
      · exact absurd h (hflat _ (Nat.le_add_right _ _))
      · exact h
    · intro k
      obtain ⟨t, ht, hor⟩ := hinf (N + k)
      have hNt : N ≤ t := Nat.le_trans (Nat.le_add_right _ _) ht
      have hq : q (t + 1) < q t := by
        rcases hor with h | h
        · exact absurd h (hflat t hNt)
        · exact h
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNt
      exact ⟨d, by omega, hq⟩

/-- The first moment at which a monotone event becomes true. Used to locate the
transition that inserted a GCA call into the recorded call list. -/
theorem first_appearance_add {P : Nat → Prop} [∀ t, Decidable (P t)] {M : Nat}
    (hM : ¬ P M) : ∀ d, P (M + d) → ∃ u, M ≤ u ∧ u < M + d ∧ ¬ P u ∧ P (u + 1) := by
  intro d
  induction d with
  | zero => intro h; exact absurd h hM
  | succ d ih =>
    intro h
    by_cases hd : P (M + d)
    · obtain ⟨u, h1, h2, h3, h4⟩ := ih hd
      exact ⟨u, h1, by omega, h3, h4⟩
    · exact ⟨M + d, Nat.le_add_right _ _, by omega, hd, h⟩

theorem first_appearance {P : Nat → Prop} [∀ t, Decidable (P t)] {M t : Nat}
    (hMt : M ≤ t) (hM : ¬ P M) (ht : P t) :
    ∃ u, M ≤ u ∧ u < t ∧ ¬ P u ∧ P (u + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hMt
  exact first_appearance_add hM d ht

end ConflictFreedom
