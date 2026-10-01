import CFLeanProof.EffectiveInterface

/-! # A computable `LocalCompute`

`EffectiveInterface` names the local computations Algorithms 1–3 perform and
proves that the two classical GCA stages factor through them.  That interface is
*consistent* (`LocalCompute.classical`), but a classical witness shows only that
the boundary is one of effectivity rather than of mathematics.  This module
closes the remaining question — is the interface ever realizable by an
algorithm? — for the objects whose trace monoid is free: those in which no two
operations commute.  There the trace quotient collapses to lists, `⊓` is the
longest common prefix, `⊔` is the longest member of a compatible family, and the
independence test is the constant `false`.

Nothing here is `noncomputable`: `LocalCompute.free` evaluates.
-/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-- An object no two of whose operations commute — a counter, a stack, a queue
with a single consumer.  Nothing is lost in the quotient. -/
def TotallyConflicting : Prop := ∀ a b, ¬ obj.Independent a b

theorem eq_of_traceEq (h : obj.TotallyConflicting) {s t : List Op}
    (heq : obj.TraceEq s t) : s = t := by
  induction heq with
  | refl s => rfl
  | swap x y a b hab => exact absurd hab (h a b)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The trace quotient is the identity on lists. -/
def toList (h : obj.TotallyConflicting) : obj.Trace → List Op :=
  Quotient.lift id (fun _ _ hst => obj.eq_of_traceEq h hst)

theorem toList_mk (h : obj.TotallyConflicting) (x : List Op) :
    obj.toList h (Quotient.mk obj.traceSetoid x) = x := rfl

/-- The inverse map, typed at `obj.Trace` so that rewriting works. -/
def ofList (x : List Op) : obj.Trace := Quotient.mk obj.traceSetoid x

theorem toList_ofList (h : obj.TotallyConflicting) (x : List Op) :
    obj.toList h (obj.ofList x) = x := rfl

theorem mk_toList (h : obj.TotallyConflicting) (s : obj.Trace) :
    obj.ofList (obj.toList h s) = s := by
  induction s using Quotient.inductionOn with | h x => rfl

theorem tracePrefix_iff_isPrefix (h : obj.TotallyConflicting) (s t : obj.Trace) :
    obj.TracePrefix s t ↔ (obj.toList h s) <+: (obj.toList h t) := by
  constructor
  · rintro ⟨x, y, rfl, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨obj.toList h s, y, obj.mk_toList h s, ?_⟩
    show obj.ofList (obj.toList h s ++ y) = t
    rw [hy]
    exact obj.mk_toList h t

/-! ### Lists: the meet is the longest common prefix -/

theorem prefix_cons_cons {a : Op} {s t : List Op} (hp : s <+: t) :
    (a :: s) <+: (a :: t) := by
  obtain ⟨u, hu⟩ := hp
  exact ⟨u, by simp [hu]⟩

variable [DecidableEq Op]

/-- The longest common prefix of two lists. -/
def commonPrefix : List Op → List Op → List Op
  | [], _ => []
  | _, [] => []
  | a :: s, b :: t => if a = b then a :: commonPrefix s t else []

theorem commonPrefix_cons (a b : Op) (s t : List Op) :
    commonPrefix (a :: s) (b :: t) = if a = b then a :: commonPrefix s t else [] := rfl

theorem commonPrefix_left : ∀ s t : List Op, commonPrefix s t <+: s
  | [], _ => List.nil_prefix
  | _ :: _, [] => List.nil_prefix
  | a :: s, b :: t => by
      rw [commonPrefix_cons]
      split
      · exact prefix_cons_cons (commonPrefix_left s t)
      · exact List.nil_prefix

theorem commonPrefix_right : ∀ s t : List Op, commonPrefix s t <+: t
  | [], _ => List.nil_prefix
  | _ :: _, [] => List.nil_prefix
  | a :: s, b :: t => by
      rw [commonPrefix_cons]
      split
      · rename_i he
        subst he
        exact prefix_cons_cons (commonPrefix_right s t)
      · exact List.nil_prefix

theorem prefix_commonPrefix : ∀ {l s t : List Op}, l <+: s → l <+: t →
    l <+: commonPrefix s t
  | [], _, _, _, _ => List.nil_prefix
  | a :: l, s, t, hs, ht => by
      obtain ⟨u, hu⟩ := hs
      obtain ⟨v, hv⟩ := ht
      subst hu
      subst hv
      have hcp : commonPrefix ((a :: l) ++ u) ((a :: l) ++ v)
          = a :: commonPrefix (l ++ u) (l ++ v) := by
        rw [List.cons_append, List.cons_append, commonPrefix_cons, ite_eq_left rfl]
      rw [hcp]
      exact prefix_cons_cons (prefix_commonPrefix ⟨u, rfl⟩ ⟨v, rfl⟩)

/-- `⊓` of a nonempty finite family of lists. -/
def meetList (s : List Op) : List (List Op) → List Op
  | [] => s
  | u :: S => meetList (commonPrefix s u) S

theorem meetList_prefix_head : ∀ (S : List (List Op)) (s : List Op), meetList s S <+: s
  | [], s => List.prefix_refl s
  | u :: S, s => (meetList_prefix_head S (commonPrefix s u)).trans (commonPrefix_left s u)

theorem meetList_prefix : ∀ (S : List (List Op)) (s : List Op) (u : List Op),
    u ∈ s :: S → meetList s S <+: u
  | [], s, u, hu => by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact List.prefix_refl _
      · cases hu
  | v :: S, s, u, hu => by
      rcases List.mem_cons.mp hu with rfl | hu
      · exact meetList_prefix_head (v :: S) u
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact (meetList_prefix_head S (commonPrefix s u)).trans (commonPrefix_right s u)
        · exact meetList_prefix S (commonPrefix s v) u (List.mem_cons_of_mem _ hu)

theorem prefix_meetList : ∀ (S : List (List Op)) (s l : List Op),
    (∀ u, u ∈ s :: S → l <+: u) → l <+: meetList s S
  | [], s, l, hp => hp s (List.mem_cons_self ..)
  | v :: S, s, l, hp => by
      refine prefix_meetList S (commonPrefix s v) l ?_
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact prefix_commonPrefix (hp s (List.mem_cons_self ..))
          (hp v (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      · exact hp u (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu))

/-! ### Lists: the join is the longest member of a compatible family -/

/-- `⊔` of a finite family of lists, when they have a common extension.  The
empty family gets `ε`, matching the manuscript's convention for `⊔∅`. -/
def joinList : List (List Op) → List Op
  | [] => []
  | u :: S => if (joinList S).length < u.length then u else joinList S

omit [DecidableEq Op] in
theorem joinList_cons (u : List Op) (S : List (List Op)) :
    joinList (u :: S) = if (joinList S).length < u.length then u else joinList S := rfl

omit [DecidableEq Op] in
theorem joinList_mem : ∀ S : List (List Op), joinList S = [] ∨ joinList S ∈ S
  | [] => Or.inl rfl
  | u :: S => by
      rw [joinList_cons]
      by_cases hlt : (joinList S).length < u.length
      · rw [ite_eq_left hlt]
        exact Or.inr (List.mem_cons_self ..)
      · rw [ite_eq_right hlt]
        rcases joinList_mem S with he | hm
        · exact Or.inl he
        · exact Or.inr (List.mem_cons_of_mem _ hm)

omit [DecidableEq Op] in
theorem length_le_joinList : ∀ (S : List (List Op)) (u : List Op), u ∈ S →
    u.length ≤ (joinList S).length
  | [], u, hu => by cases hu
  | v :: S, u, hu => by
      rw [joinList_cons]
      by_cases hlt : (joinList S).length < v.length
      · rw [ite_eq_left hlt]
        rcases List.mem_cons.mp hu with rfl | hu
        · exact Nat.le_refl _
        · exact Nat.le_trans (length_le_joinList S u hu) (Nat.le_of_lt hlt)
      · rw [ite_eq_right hlt]
        rcases List.mem_cons.mp hu with rfl | hu
        · omega
        · exact length_le_joinList S u hu

omit [DecidableEq Op] in
theorem joinList_prefix_of_upper {S : List (List Op)} {t : List Op}
    (hp : ∀ u, u ∈ S → u <+: t) : joinList S <+: t := by
  rcases joinList_mem S with he | hm
  · rw [he]; exact List.nil_prefix
  · exact hp _ hm

omit [DecidableEq Op] in
theorem prefix_joinList {S : List (List Op)} {t : List Op}
    (hp : ∀ u, u ∈ S → u <+: t) (u : List Op) (hu : u ∈ S) : u <+: joinList S :=
  List.prefix_of_prefix_length_le (hp u hu) (joinList_prefix_of_upper hp)
    (length_le_joinList S u hu)

/-! ### The interface, realized -/

section Free
variable (h : obj.TotallyConflicting)

/-- The lists underlying a finite family of traces. -/
def lists (S : List obj.Trace) : List (List Op) := S.map (obj.toList h)

omit [DecidableEq Op] in
theorem mem_lists {S : List obj.Trace} {x : List Op} :
    x ∈ obj.lists h S ↔ ∃ s ∈ S, obj.toList h s = x := by
  simp [lists]

omit [DecidableEq Op] in
theorem compatible_iff_free (S : List obj.Trace) :
    obj.Compatible (fun s => s ∈ S) ↔
      ∀ x, x ∈ obj.lists h S → x <+: joinList (obj.lists h S) := by
  constructor
  · rintro ⟨t, ht⟩
    intro x hx
    refine prefix_joinList (t := obj.toList h t) ?_ x hx
    intro y hy
    obtain ⟨s, hs, rfl⟩ := (obj.mem_lists h).mp hy
    exact (obj.tracePrefix_iff_isPrefix h s t).mp (ht s hs)
  · intro hall
    refine ⟨obj.ofList (joinList (obj.lists h S)), ?_⟩
    intro s hs
    rw [obj.tracePrefix_iff_isPrefix h, toList_ofList]
    exact hall _ ((obj.mem_lists h).mpr ⟨s, hs, rfl⟩)

/-- **The interface is realizable.**  For an object whose trace monoid is free,
every local computation of Algorithms 1–3 is an ordinary list algorithm: `⊓` is
the longest common prefix, `⊔` is the longest member, compatibility is a prefix
test, and no two operations are independent. -/
def LocalCompute.free : LocalCompute obj where
  independent := fun _ _ => false
  independent_iff := fun a b => ⟨by simp, fun hi => absurd hi (h a b)⟩
  compatible := fun S =>
    (obj.lists h S).all (fun x => x.isPrefixOf (joinList (obj.lists h S)))
  compatible_iff := by
    intro S
    rw [obj.compatible_iff_free h S, List.all_eq_true]
    exact ⟨fun hb x hx => List.isPrefixOf_iff_prefix.mp (hb x hx),
      fun hp x hx => List.isPrefixOf_iff_prefix.mpr (hp x hx)⟩
  glb := fun s S =>
    obj.ofList (meetList (obj.toList h s) (obj.lists h S))
  glb_spec := by
    intro s S
    constructor
    · intro t ht
      rw [obj.tracePrefix_iff_isPrefix h, toList_ofList]
      refine meetList_prefix _ _ _ ?_
      rcases List.mem_cons.mp ht with rfl | ht
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ ((obj.mem_lists h).mpr ⟨t, ht, rfl⟩)
    · intro l hl
      rw [obj.tracePrefix_iff_isPrefix h, toList_ofList]
      refine prefix_meetList _ _ _ ?_
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (obj.tracePrefix_iff_isPrefix h l s).mp (hl s (List.mem_cons_self ..))
      · obtain ⟨t, ht, rfl⟩ := (obj.mem_lists h).mp hx
        exact (obj.tracePrefix_iff_isPrefix h l t).mp (hl t (List.mem_cons_of_mem _ ht))
  lub := fun S => obj.ofList (joinList (obj.lists h S))
  lub_spec := by
    intro S hc
    have hall := (obj.compatible_iff_free h S).mp hc
    constructor
    · intro s hs
      rw [obj.tracePrefix_iff_isPrefix h, toList_ofList]
      exact hall _ ((obj.mem_lists h).mpr ⟨s, hs, rfl⟩)
    · intro v hv
      rw [obj.tracePrefix_iff_isPrefix h, toList_ofList]
      refine joinList_prefix_of_upper ?_
      intro x hx
      obtain ⟨s, hs, rfl⟩ := (obj.mem_lists h).mp hx
      exact (obj.tracePrefix_iff_isPrefix h s v).mp (hv s hs)

end Free


/-! ### The interface, running

A counter: every operation increments, so no two operations commute and the
trace monoid is free.  The equalities below are `rfl`, so the kernel evaluates
GCA lines 3, 4 and 6 on concrete inputs. -/

namespace CounterWitness

/-- A counter: every operation returns the state and increments it, so no two
operations commute. -/
def ctr : Object Nat Nat Nat := ⟨0, fun _ q => (q, q + 1)⟩

theorem ctr_totallyConflicting : ctr.TotallyConflicting := by
  intro a b hi
  have h : (0 : Nat) = 1 := (hi 0).1
  exact absurd h (by decide)

/-- The realized interface for the counter; nothing here is `noncomputable`. -/
def E : Object.LocalCompute ctr := Object.LocalCompute.free ctr ctr_totallyConflicting

private def out (s : ctr.Trace) : List Nat := ctr.toList ctr_totallyConflicting s

/-- `⊓` is the longest common prefix. -/
example : out (E.glb (ctr.ofList [1, 2, 3])
    [ctr.ofList [1, 2, 9], ctr.ofList [1, 2, 3, 4]]) = [1, 2] := rfl

/-- `⊔` of a compatible family is its longest member. -/
example : out (E.lub [ctr.ofList [1, 2], ctr.ofList [1, 2, 3, 4], ctr.ofList [1]])
    = [1, 2, 3, 4] := rfl

example : E.compatible [ctr.ofList [1, 2], ctr.ofList [1, 2, 3, 4]] = true := rfl
example : E.compatible [ctr.ofList [1, 2], ctr.ofList [1, 9]] = false := rfl
example : E.independent 3 4 = false := rfl

/-- GCA lines 3–4 on a compatible view: the candidate is the join. -/
example : out (E.candidate [ctr.ofList [1, 2], ctr.ofList [1, 2, 3]]) = [1, 2, 3] := rfl

/-- GCA lines 3–4 on a conflicting view: each input is first cut down to its
meet with the inputs it conflicts with. -/
example : out (E.candidate [ctr.ofList [1, 2], ctr.ofList [1, 9]]) = [1] := rfl

/-- GCA line 6: the meet of the flagged candidates. -/
example : out (E.output [ctr.ofList [1]]
    [[ctr.ofList [1, 2]], [ctr.ofList [1, 2, 3]]]) = [1, 2] := rfl

/-- And these computed values *are* the classical ones. -/
theorem candidate_agrees (S : List ctr.Trace) : E.candidate S = ctr.gcaCandidate S :=
  E.candidate_eq S

theorem output_agrees (own : List ctr.Trace) (B : List (List ctr.Trace)) :
    E.output own B = ctr.gcaOutput own B := E.output_eq own B

end CounterWitness
end ConflictFreedom.Object
