import CFLeanProof.FreeTraceCompute
import CFLeanProof.Commands

/-! # Computable local computations, for every object with decidable independence

`FreeTraceCompute` realizes `LocalCompute` when no two operations commute.  This
module realizes it whenever **independence is decidable** — in particular for
every object with finitely many states (`LocalCompute.finite`), and for objects
with infinitely many states whose commutations are decided by an argument
(`IncReadWitness`).

Traces are finite, so everything is an algorithm on representatives once one
can decide whether two operations commute.  An operation `a` *can start* a
schedule `s` when every operation before its first occurrence commutes with it
(`CanStart`); then:

* `t` extends `s` iff each operation of `s` in turn can start `t`, and is
  removed from it (`prefixB`), so trace order and trace equality are decidable;
* `s ⊓ t` repeatedly takes an operation that can start both (`meetL`);
* `s ⊔ t`, when it exists, is `s` followed by what is left of `t` once each
  operation of `s` is removed from it (`joinL`), and `s, t` are compatible iff
  that list extends `t` (`compatB`);
* a finite family's meet and join are folds of the binary ones.

Nothing here is `noncomputable`, and the kernel evaluates every operation
(`decide`, below).  `Classical.choice` occurs only in correctness proofs — through
core list lemmas such as `List.erase_append_left` — never in the functions, which
evaluation could not pass through.

The converse holds too: a compatibility test decides independence, since two
distinct operations commute iff their one-operation traces are compatible
(`independent_iff_pairCompatible`).  So decidable independence is exactly what
executability needs.  It is a property of the sequential object, not of the
traces: `Independent` quantifies over every state.  A finite state space decides
it by enumeration (`FiniteState.decidableIndependent`); an arbitrary computable
object need not — two operations of a counter-like object can be made to commute
exactly when a given program never halts.
-/
namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-! ### Representatives and the trace operations on them -/

variable [DecidableEq Op]

omit [DecidableEq Op] in
theorem ofList_cons (a : Op) (x : List Op) :
    obj.traceCons a (obj.ofList x) = obj.ofList (a :: x) := rfl

theorem traceErase_ofList (a : Op) (x : List Op) :
    obj.traceErase a (obj.ofList x) = obj.ofList (x.erase a) := rfl

theorem traceErase_ofList_cons (a : Op) (x : List Op) :
    obj.traceErase a (obj.ofList (a :: x)) = obj.ofList x := by
  rw [traceErase_ofList, List.erase_cons_head]

theorem ofList_eq_of_canStart {a : Op} {x : List Op} (h : obj.CanStart a x) :
    obj.ofList x = obj.traceCons a (obj.ofList (x.erase a)) :=
  Quotient.sound (obj.canStart_move h)

omit [DecidableEq Op] in
theorem traceCanStart_ofList_cons (a : Op) (x : List Op) :
    obj.traceCanStart a (obj.ofList (a :: x)) := Or.inl rfl

/-- A greatest lower bound of two traces. -/
def IsMeet (s t g : obj.Trace) : Prop :=
  obj.TracePrefix g s ∧ obj.TracePrefix g t ∧
    ∀ l, obj.TracePrefix l s → obj.TracePrefix l t → obj.TracePrefix l g

/-- A least upper bound of two traces. -/
def IsJoin (s t u : obj.Trace) : Prop :=
  obj.TracePrefix s u ∧ obj.TracePrefix t u ∧
    ∀ v, obj.TracePrefix s v → obj.TracePrefix t v → obj.TracePrefix u v

omit [DecidableEq Op] in
theorem meet_unique {s t g h : obj.Trace} (hg : obj.IsMeet s t g) (hh : obj.IsMeet s t h) :
    g = h :=
  obj.tracePrefix_antisymm (hh.2.2 g hg.1 hg.2.1) (hg.2.2 h hh.1 hh.2.1)

omit [DecidableEq Op] in
theorem join_unique {s t g h : obj.Trace} (hg : obj.IsJoin s t g) (hh : obj.IsJoin s t h) :
    g = h :=
  obj.tracePrefix_antisymm (hg.2.2 h hh.1 hh.2.1) (hh.2.2 g hg.1 hg.2.1)

/-! ### Joins need no independence test -/

/-- `⊔` of two compatible traces, on representatives: `x`, then what is left of
`y` once each operation of `x` is removed from it. -/
def joinL : List Op → List Op → List Op
  | [], y => y
  | a :: x, y => a :: joinL x (y.erase a)

theorem joinL_extends : ∀ x y : List Op, ∃ z, joinL x y = x ++ z
  | [], y => ⟨y, rfl⟩
  | a :: x, y => by
      obtain ⟨z, hz⟩ := joinL_extends x (y.erase a)
      exact ⟨z, by rw [joinL, hz]; rfl⟩

theorem prefix_joinL (x y : List Op) :
    obj.TracePrefix (obj.ofList x) (obj.ofList (joinL x y)) := by
  obtain ⟨z, hz⟩ := joinL_extends x y
  exact ⟨x, z, rfl, by rw [hz]; rfl⟩

/-- **`joinL` is the least upper bound of any two traces that have one.** The
proof removes the first operation of `x` from everything, as `pair_lub_exists`
does. -/
theorem joinL_spec : ∀ (x y : List Op) (w : obj.Trace),
    obj.TracePrefix (obj.ofList x) w → obj.TracePrefix (obj.ofList y) w →
    obj.IsJoin (obj.ofList x) (obj.ofList y) (obj.ofList (joinL x y))
  | [], y, _, _, _ => ⟨obj.empty_tracePrefix _, obj.tracePrefix_refl _, fun _ _ hv => hv⟩
  | a :: x, y, w, hxw, hyw => by
      have haw := obj.traceCanStart_mono hxw (obj.traceCanStart_ofList_cons a x)
      have hx' : obj.TracePrefix (obj.ofList x) (obj.traceErase a w) := by
        have h := obj.traceErase_mono a hxw
        rwa [traceErase_ofList_cons] at h
      obtain ⟨j1, j2, j3⟩ := joinL_spec x (y.erase a) (obj.traceErase a w) hx'
        (obj.traceErase_mono a hyw)
      refine ⟨obj.traceCons_mono a j1, ?_, ?_⟩
      · exact obj.tracePrefix_trans (obj.tracePrefix_head_completion hyw haw)
          (obj.traceCons_mono a j2)
      · intro v hxv hyv
        have hav := obj.traceCanStart_mono hxv (obj.traceCanStart_ofList_cons a x)
        have hxv' : obj.TracePrefix (obj.ofList x) (obj.traceErase a v) := by
          have h := obj.traceErase_mono a hxv
          rwa [traceErase_ofList_cons] at h
        have h := obj.traceCons_mono a (j3 (obj.traceErase a v) hxv' (obj.traceErase_mono a hyv))
        rw [← obj.traceCanStart_move hav] at h
        exact h

/-! ### Deciding the trace order, given decidable independence -/

variable [DecidableRel obj.Independent]

/-- Whether `a` can move to the front of `s` (`CanStart`). -/
def canStartB (a : Op) : List Op → Bool
  | [] => false
  | b :: s => decide (a = b) || (decide (obj.Independent a b) && canStartB a s)

theorem canStartB_iff (a : Op) (s : List Op) : obj.canStartB a s = true ↔ obj.CanStart a s := by
  induction s with
  | nil => simp [canStartB, CanStart]
  | cons b s ih => simp [canStartB, CanStart, ih]

/-- The trace-prefix test on representatives: each operation of `x` in turn must
be able to start `y`, and is removed from it. -/
def prefixB : List Op → List Op → Bool
  | [], _ => true
  | a :: x, y => obj.canStartB a y && prefixB x (y.erase a)

theorem prefixB_iff : ∀ x y : List Op,
    obj.prefixB x y = true ↔ obj.TracePrefix (obj.ofList x) (obj.ofList y)
  | [], y => ⟨fun _ => obj.empty_tracePrefix _, fun _ => rfl⟩
  | a :: x, y => by
      rw [prefixB, Bool.and_eq_true, canStartB_iff, prefixB_iff x (y.erase a)]
      constructor
      · rintro ⟨ha, hx⟩
        rw [obj.ofList_eq_of_canStart ha]
        exact obj.traceCons_mono a hx
      · intro h
        refine ⟨obj.traceCanStart_mono h (obj.traceCanStart_ofList_cons a x), ?_⟩
        have h' := obj.traceErase_mono a h
        rwa [traceErase_ofList_cons, traceErase_ofList] at h'

/-- The trace-prefix test. -/
def tracePrefixB : obj.Trace → obj.Trace → Bool :=
  Quotient.lift₂ obj.prefixB (by
    intro x₁ y₁ x₂ y₂ hx hy
    have e1 : obj.ofList x₁ = obj.ofList x₂ := Quotient.sound hx
    have e2 : obj.ofList y₁ = obj.ofList y₂ := Quotient.sound hy
    apply Bool.eq_iff_iff.mpr
    rw [prefixB_iff, prefixB_iff, e1, e2])

theorem tracePrefixB_iff (s t : obj.Trace) :
    obj.tracePrefixB s t = true ↔ obj.TracePrefix s t := by
  induction s using Quotient.inductionOn with | h x =>
    induction t using Quotient.inductionOn with | h y =>
      exact obj.prefixB_iff x y

/-- **The trace order is decidable.** -/
instance decTracePrefix : DecidableRel obj.TracePrefix :=
  fun s t => decidable_of_iff _ (obj.tracePrefixB_iff s t)

/-- **Trace equality is decidable**: two traces are equal iff each extends the
other. -/
instance decEqTrace : DecidableEq obj.Trace := fun s t =>
  decidable_of_iff (obj.TracePrefix s t ∧ obj.TracePrefix t s)
    ⟨fun h => obj.tracePrefix_antisymm h.1 h.2,
      fun h => h ▸ ⟨obj.tracePrefix_refl _, obj.tracePrefix_refl _⟩⟩

/-! ### Meets -/

/-- `⊓` of two traces, on representatives: while some operation can start both,
take it and remove it from both.  `fuel` bounds the recursion; `meetL` gives it
the length of `x`, which each step shortens. -/
def meetAux : Nat → List Op → List Op → List Op
  | 0, _, _ => []
  | fuel + 1, x, y =>
      match x.find? (fun c => obj.canStartB c x && obj.canStartB c y) with
      | none => []
      | some c => c :: meetAux fuel (x.erase c) (y.erase c)

/-- `⊓` of two traces, on representatives. -/
def meetL (x y : List Op) : List Op := obj.meetAux x.length x y

theorem meetAux_spec : ∀ (fuel : Nat) (x y : List Op), x.length ≤ fuel →
    obj.IsMeet (obj.ofList x) (obj.ofList y) (obj.ofList (obj.meetAux fuel x y))
  | 0, x, y, h => by
      have hx : x = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
      subst hx
      exact ⟨obj.tracePrefix_refl _, obj.empty_tracePrefix _, fun _ hl _ => hl⟩
  | fuel + 1, x, y, h => by
      unfold meetAux
      split
      · rename_i hnone
        refine ⟨obj.empty_tracePrefix _, obj.empty_tracePrefix _, ?_⟩
        intro l hlx hly
        induction l using Quotient.inductionOn with | h ls =>
          cases ls with
          | nil => exact obj.tracePrefix_refl _
          | cons d ls =>
              exfalso
              have hdx : obj.CanStart d x :=
                obj.traceCanStart_mono hlx (obj.traceCanStart_ofList_cons d ls)
              have hdy : obj.CanStart d y :=
                obj.traceCanStart_mono hly (obj.traceCanStart_ofList_cons d ls)
              have hno := List.find?_eq_none.mp hnone d (obj.canStart_mem hdx)
              simp [obj.canStartB_iff, hdx, hdy] at hno
      · rename_i c hc
        have hmem : c ∈ x := List.mem_of_find?_eq_some hc
        have hp := List.find?_some hc
        rw [Bool.and_eq_true, canStartB_iff, canStartB_iff] at hp
        obtain ⟨hcx, hcy⟩ := hp
        have hlen : (x.erase c).length ≤ fuel := by
          rw [List.length_erase_of_mem hmem]
          omega
        obtain ⟨m1, m2, m3⟩ := meetAux_spec fuel (x.erase c) (y.erase c) hlen
        refine ⟨?_, ?_, ?_⟩
        · rw [obj.ofList_eq_of_canStart hcx]
          exact obj.traceCons_mono c m1
        · rw [obj.ofList_eq_of_canStart hcy]
          exact obj.traceCons_mono c m2
        · intro l hlx hly
          have hl := obj.tracePrefix_head_completion hlx (show obj.traceCanStart c (obj.ofList x) from hcx)
          refine obj.tracePrefix_trans hl (obj.traceCons_mono c (m3 _ ?_ ?_))
          · exact obj.traceErase_mono c hlx
          · exact obj.traceErase_mono c hly

theorem meetL_spec (x y : List Op) :
    obj.IsMeet (obj.ofList x) (obj.ofList y) (obj.ofList (obj.meetL x y)) :=
  obj.meetAux_spec x.length x y (Nat.le_refl _)

/-- `⊓` of two traces. -/
def meet2 : obj.Trace → obj.Trace → obj.Trace :=
  Quotient.lift₂ (fun x y => obj.ofList (obj.meetL x y)) (by
    intro x₁ y₁ x₂ y₂ hx hy
    have e1 : obj.ofList x₁ = obj.ofList x₂ := Quotient.sound hx
    have e2 : obj.ofList y₁ = obj.ofList y₂ := Quotient.sound hy
    have s1 := obj.meetL_spec x₁ y₁
    rw [e1, e2] at s1
    exact obj.meet_unique s1 (obj.meetL_spec x₂ y₂))

theorem meet2_spec (s t : obj.Trace) : obj.IsMeet s t (obj.meet2 s t) := by
  induction s using Quotient.inductionOn with | h x =>
    induction t using Quotient.inductionOn with | h y =>
      exact obj.meetL_spec x y

/-! ### Compatibility and joins -/

/-- Compatibility of two traces, on representatives: `joinL x y` extends `y`. -/
def compatB (x y : List Op) : Bool := obj.prefixB y (joinL x y)

theorem compatB_iff (x y : List Op) :
    obj.compatB x y = true ↔ obj.PairCompatible (obj.ofList x) (obj.ofList y) := by
  rw [compatB, prefixB_iff]
  constructor
  · intro h
    exact ⟨_, obj.prefix_joinL x y, h⟩
  · rintro ⟨w, hx, hy⟩
    exact (obj.joinL_spec x y w hx hy).2.1

/-- `⊔` of two traces, `none` when they are incompatible. -/
def join2? : obj.Trace → obj.Trace → Option obj.Trace :=
  Quotient.lift₂
    (fun x y => if obj.compatB x y then some (obj.ofList (joinL x y)) else none) (by
      intro x₁ y₁ x₂ y₂ hx hy
      have e1 : obj.ofList x₁ = obj.ofList x₂ := Quotient.sound hx
      have e2 : obj.ofList y₁ = obj.ofList y₂ := Quotient.sound hy
      have hc : obj.compatB x₁ y₁ = obj.compatB x₂ y₂ := by
        apply Bool.eq_iff_iff.mpr
        rw [compatB_iff, compatB_iff, e1, e2]
      simp only [hc]
      split
      · rename_i h
        obtain ⟨w, hw1, hw2⟩ := (obj.compatB_iff x₂ y₂).mp h
        have s1 := obj.joinL_spec x₁ y₁ w (e1 ▸ hw1) (e2 ▸ hw2)
        rw [e1, e2] at s1
        exact congrArg some (obj.join_unique s1 (obj.joinL_spec x₂ y₂ w hw1 hw2))
      · rfl)

theorem join2?_spec (s t : obj.Trace) :
    (∀ u, obj.join2? s t = some u → obj.IsJoin s t u) ∧
      (obj.PairCompatible s t → ∃ u, obj.join2? s t = some u) := by
  induction s using Quotient.inductionOn with | h x =>
    induction t using Quotient.inductionOn with | h y =>
      change (∀ u, (if obj.compatB x y then some (obj.ofList (joinL x y)) else none) = some u →
          obj.IsJoin (obj.ofList x) (obj.ofList y) u) ∧
        (obj.PairCompatible (obj.ofList x) (obj.ofList y) →
          ∃ u, (if obj.compatB x y then some (obj.ofList (joinL x y)) else none) = some u)
      cases hc : obj.compatB x y with
      | true =>
          obtain ⟨w, hw1, hw2⟩ := (obj.compatB_iff x y).mp hc
          refine ⟨?_, fun _ => ⟨_, rfl⟩⟩
          intro u hu
          simp only [ite_true, Option.some.injEq] at hu
          subst hu
          exact obj.joinL_spec x y w hw1 hw2
      | false =>
          refine ⟨fun u hu => by simp at hu, fun hp => ?_⟩
          have := (obj.compatB_iff x y).mpr hp
          rw [hc] at this
          cases this

/-! ### Finite families -/

/-- `⊓` of the nonempty family `s :: S`. -/
def glbL (s : obj.Trace) : List obj.Trace → obj.Trace
  | [] => s
  | t :: S => obj.meet2 s (glbL t S)

theorem glbL_spec : ∀ (S : List obj.Trace) (s : obj.Trace),
    obj.IsGLB (fun t => t ∈ s :: S) (obj.glbL s S)
  | [], s => by
      refine ⟨fun t ht => ?_, fun l hl => hl s (List.mem_cons_self ..)⟩
      rcases List.mem_singleton.mp ht with rfl
      exact obj.tracePrefix_refl _
  | t :: S, s => by
      obtain ⟨g1, g2⟩ := glbL_spec S t
      obtain ⟨m1, m2, m3⟩ := obj.meet2_spec s (obj.glbL t S)
      refine ⟨fun u hu => ?_, fun l hl => ?_⟩
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact m1
        · exact obj.tracePrefix_trans m2 (g1 u hu)
      · exact m3 l (hl s (List.mem_cons_self ..))
          (g2 l (fun u hu => hl u (List.mem_cons_of_mem _ hu)))

/-- `⊔` of a finite family, `none` when it is incompatible. -/
def joinAll? : List obj.Trace → Option obj.Trace
  | [] => some obj.emptyTrace
  | s :: S =>
      match joinAll? S with
      | none => none
      | some u => obj.join2? s u

theorem joinAll?_spec : ∀ S : List obj.Trace,
    (∀ u, obj.joinAll? S = some u → obj.IsLUB (fun t => t ∈ S) u) ∧
      (obj.Compatible (fun t => t ∈ S) → ∃ u, obj.joinAll? S = some u)
  | [] => by
      refine ⟨fun u hu => ?_, fun _ => ⟨_, rfl⟩⟩
      simp only [joinAll?, Option.some.injEq] at hu
      subst hu
      exact ⟨fun t ht => (by cases ht), fun v _ => obj.empty_tracePrefix v⟩
  | s :: S => by
      obtain ⟨ih1, ih2⟩ := joinAll?_spec S
      refine ⟨fun u hu => ?_, fun hc => ?_⟩
      · simp only [joinAll?] at hu
        split at hu
        · cases hu
        · rename_i w hw
          have hlub := ih1 w hw
          obtain ⟨j1, j2, j3⟩ := (obj.join2?_spec s w).1 u hu
          refine ⟨fun t ht => ?_, fun v hv => ?_⟩
          · rcases List.mem_cons.mp ht with rfl | ht
            · exact j1
            · exact obj.tracePrefix_trans (hlub.1 t ht) j2
          · exact j3 v (hv s (List.mem_cons_self ..))
              (hlub.2 v (fun t ht => hv t (List.mem_cons_of_mem _ ht)))
      · obtain ⟨b, hb⟩ := hc
        obtain ⟨w, hw⟩ := ih2 ⟨b, fun t ht => hb t (List.mem_cons_of_mem _ ht)⟩
        have hlub := ih1 w hw
        obtain ⟨u, hu⟩ := (obj.join2?_spec s w).2
          ⟨b, hb s (List.mem_cons_self ..), hlub.2 b (fun t ht => hb t (List.mem_cons_of_mem _ ht))⟩
        exact ⟨u, by simp only [joinAll?, hw]; exact hu⟩

/-! ### The interface, realized -/

/-- **The local computations of Algorithms 1–3, as algorithms, for every object
whose independence relation is decidable.**  Nothing here is `noncomputable`. -/
def LocalCompute.ofDecidable : LocalCompute obj where
  independent := fun a b => decide (obj.Independent a b)
  independent_iff := fun _ _ => decide_eq_true_iff
  compatible := fun S => (obj.joinAll? S).isSome
  compatible_iff := by
    intro S
    constructor
    · intro h
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h
      exact ⟨u, ((obj.joinAll?_spec S).1 u hu).1⟩
    · intro hc
      obtain ⟨u, hu⟩ := (obj.joinAll?_spec S).2 hc
      rw [hu]
      rfl
  glb := obj.glbL
  glb_spec := fun s S => obj.glbL_spec S s
  lub := fun S => (obj.joinAll? S).getD obj.emptyTrace
  lub_spec := by
    intro S hc
    obtain ⟨u, hu⟩ := (obj.joinAll?_spec S).2 hc
    rw [hu]
    exact (obj.joinAll?_spec S).1 u hu

/-- Commands commute exactly when their operations do, so the objects the
universal constructions hand to GCA inherit the decision. -/
instance commandObject_decidableIndependent (P : Type) :
    DecidableRel (obj.commandObject P).Independent :=
  fun a b => inferInstanceAs (Decidable (obj.Independent a.operation b.operation))

omit [DecidableRel obj.Independent] in
/-- **Deciding compatibility decides independence**: two distinct operations
commute exactly when their one-operation traces have a common extension.  So a
compatibility test — the line-6 test of GCA — is as hard as an independence
test, and decidable independence is exactly what an executable `LocalCompute`
needs. -/
theorem independent_iff_pairCompatible {a b : Op} (hab : a ≠ b) :
    obj.Independent a b ↔ obj.PairCompatible (obj.ofList [a]) (obj.ofList [b]) := by
  constructor
  · intro hi
    refine ⟨obj.ofList [a, b], ⟨[a], [b], rfl, rfl⟩, ⟨[b], [a], rfl, ?_⟩⟩
    exact Quotient.sound (TraceEq.swap [] [] b a (obj.independent_symm hi))
  · rintro ⟨u, hau, hbu⟩
    induction u using Quotient.inductionOn with | h w =>
      exact (obj.canStart_diamond (obj.traceCanStart_mono hau (obj.traceCanStart_ofList_cons a []))
        (obj.traceCanStart_mono hbu (obj.traceCanStart_ofList_cons b [])) hab).1

end ConflictFreedom.Object

namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response) [DecidableEq Op]

/-- **Every finite-state object has an executable `LocalCompute`.** -/
def LocalCompute.finite [DecidableEq State] [DecidableEq Response] (fs : FiniteState State) :
    LocalCompute obj :=
  @LocalCompute.ofDecidable _ _ _ obj _ (fs.decidableIndependent obj)

/-! ### The interface, running, with commuting operations

A grow-only set over two elements.  Adding either element commutes with
everything except testing that same element, so the trace monoid is not free,
and every operation below is evaluated by the kernel (`decide`). -/

namespace SetWitness

/-- Operations of a grow-only set over `Bool`: add an element, or test one. -/
inductive SetOp where
  | add (x : Bool)
  | has (x : Bool)
  deriving DecidableEq

/-- The set, as its two membership bits; adding answers `true`. -/
def gset : Object (Bool × Bool) SetOp Bool where
  initial := (false, false)
  step
    | .add x, (a, b) => (true, if x then (a, true) else (true, b))
    | .has x, (a, b) => (if x then b else a, (a, b))

/-- Its four states. -/
def states : FiniteState (Bool × Bool) where
  enum := [(false, false), (false, true), (true, false), (true, true)]
  complete := by
    rintro ⟨a, b⟩
    cases a <;> cases b <;> decide

instance : DecidableRel gset.Independent := states.decidableIndependent gset

/-- The realized interface; nothing here is `noncomputable`. -/
def E : LocalCompute gset := LocalCompute.finite gset states

private def t (x : List SetOp) : gset.Trace := gset.ofList x

open SetOp

/-- Adding two elements commutes; adding one does not commute with testing it. -/
example : E.independent (add true) (add false) = true := by decide
example : E.independent (add true) (has false) = true := by decide
example : E.independent (add true) (has true) = false := by decide

/-- Trace equality is decided, up to the commutations. -/
example : t [add true, has false] = t [has false, add true] := by decide
example : t [add true, has true] ≠ t [has true, add true] := by decide

/-- `⊓` keeps what both traces can start with. -/
example : E.glb (t [add true, has false]) [t [has false, add false]] = t [has false] := by decide

/-- Compatibility and `⊔` see through the commutations. -/
example : E.compatible [t [add false, add true], t [add true, has true]] = true := by decide
example : E.lub [t [add false, add true], t [add true, has true]]
    = t [add true, add false, has true] := by decide
example : E.compatible [t [add false], t [has false]] = false := by decide

/-- GCA lines 3–4: on a compatible view the candidate is the join… -/
example : E.candidate [t [add false, add true], t [add true, has true]]
    = t [add false, add true, has true] := by decide

/-- …and on a conflicting view each input is first cut down to its meet with
the inputs it conflicts with. -/
example : E.candidate [t [add false, has true], t [has false]] = t [] := by decide

/-- GCA line 6: the meet of the flagged candidates. -/
example : E.output [t [add true]] [[t [add false, has true]], [t [has true, add false, add true]]]
    = t [has true, add false] := by decide

end SetWitness

/-! ### Infinitely many states

Finiteness of the state space is sufficient, not necessary: a counter that can
be incremented and read has infinitely many states, yet which of its operations
commute is decided by an argument. -/

namespace IncReadWitness

/-- Increment (answering nothing of interest) or read. -/
inductive CtrOp where
  | inc
  | read
  deriving DecidableEq

/-- A counter: increments commute with each other, reads with each other. -/
def ctr : Object Nat CtrOp Nat where
  initial := 0
  step
    | .inc, q => (0, q + 1)
    | .read, q => (q, q)

theorem inc_read_conflict : ¬ ctr.Independent .inc .read := by
  intro h
  have := (h 0).2.1
  simp [ctr] at this

instance : DecidableRel ctr.Independent
  | .inc, .inc => isTrue fun q => by simp [CommuteAt, ctr]
  | .read, .read => isTrue fun q => by simp [CommuteAt, ctr]
  | .inc, .read => isFalse inc_read_conflict
  | .read, .inc => isFalse fun h => inc_read_conflict (ctr.independent_symm h)

/-- The realized interface, over infinitely many states. -/
def E : LocalCompute ctr := LocalCompute.ofDecidable ctr

private def t (x : List CtrOp) : ctr.Trace := ctr.ofList x

open CtrOp

example : t [inc, read, inc] ≠ t [inc, inc, read] := by decide
example : E.lub [t [inc, inc], t [inc]] = t [inc, inc] := by decide
example : E.compatible [t [inc, read], t [read, inc]] = false := by decide
example : E.glb (t [inc, read]) [t [inc, inc]] = t [inc] := by decide

end IncReadWitness
end ConflictFreedom.Object
