import CFLeanProof.FiniteLinearization

/-! # Histories as literal event sequences

The manuscript defines a history as "a sequence of operation invocation and
response events by the processes on the shared object", well formed when it is
sequential per process, and calls it linearizable when it has a completion
`H̄` and a legal sequential history `S` with `H̄|ᵢ = S|ᵢ` for every process `i`
and `≼_H ⊆ ≼_S`.

`FiniteLinearization` observes a run at configuration boundaries instead:
`H.invoked N a` and `H.returned N a v`.  That is convenient for the trace
argument but it is not the paper's object.  This module supplies the literal
event encoding, the paper's well-formedness and completion notions, and the
paper's definition of linearizability; `LedgerEvents` builds the event
sequence of an actual run and proves the two presentations agree.
-/
namespace ConflictFreedom

/-- An event of a history: an operation invocation, or a matching response.
Operation instances are identities (`Command`), so an event names the instance
it belongs to and a response carries the returned value. -/
inductive Event (Op Response : Type) where
  | invoke (a : Op)
  | respond (a : Op) (v : Response)

namespace Event
variable {Op Response : Type}

/-- The operation instance an event belongs to. -/
def op : Event Op Response → Op
  | invoke a => a
  | respond a _ => a

@[simp] theorem op_invoke (a : Op) : (invoke a : Event Op Response).op = a := rfl
@[simp] theorem op_respond (a : Op) (v : Response) : (respond a v).op = a := rfl

/-- The instance invoked by an event, if it is an invocation. -/
def invokedOp : Event Op Response → Option Op
  | invoke a => some a
  | respond _ _ => none

/-- The instance and value answered by an event, if it is a response. -/
def respondedOp : Event Op Response → Option (Op × Response)
  | invoke _ => none
  | respond a v => some (a, v)

@[simp] theorem invokedOp_invoke (a : Op) :
    (invoke a : Event Op Response).invokedOp = some a := rfl
@[simp] theorem invokedOp_respond (a : Op) (v : Response) :
    (respond a v).invokedOp = none := rfl
@[simp] theorem respondedOp_invoke (a : Op) :
    (invoke a : Event Op Response).respondedOp = none := rfl
@[simp] theorem respondedOp_respond (a : Op) (v : Response) :
    (respond a v).respondedOp = some (a, v) := rfl

end Event

/-- A finite history: a literal sequence of invocation and response events. -/
abbrev History (Op Response : Type) := List (Event Op Response)

namespace History
variable {Op Response P : Type}

/-- The instances invoked, in event order. -/
def invocations (h : History Op Response) : List Op := h.filterMap Event.invokedOp

/-- The instances answered with their values, in event order. -/
def responses (h : History Op Response) : List (Op × Response) :=
  h.filterMap Event.respondedOp

theorem mem_invocations {h : History Op Response} {a : Op} :
    a ∈ h.invocations ↔ Event.invoke a ∈ h := by
  constructor
  · intro ha
    obtain ⟨e, he, hv⟩ := List.mem_filterMap.mp ha
    cases e with
    | invoke b => cases hv; exact he
    | respond b v => cases hv
  · intro ha
    exact List.mem_filterMap.mpr ⟨Event.invoke a, ha, rfl⟩

theorem mem_responses {h : History Op Response} {a : Op} {v : Response} :
    (a, v) ∈ h.responses ↔ Event.respond a v ∈ h := by
  constructor
  · intro ha
    obtain ⟨e, he, hv⟩ := List.mem_filterMap.mp ha
    cases e with
    | invoke b => cases hv
    | respond b w =>
      have hb : b = a := congrArg Prod.fst (Option.some.inj hv)
      have hw : w = v := congrArg Prod.snd (Option.some.inj hv)
      subst hb; subst hw; exact he
  · intro ha
    exact List.mem_filterMap.mpr ⟨Event.respond a v, ha, rfl⟩

@[simp] theorem invocations_nil :
    invocations ([] : History Op Response) = [] := rfl
@[simp] theorem responses_nil :
    responses ([] : History Op Response) = [] := rfl

theorem invocations_append (h k : History Op Response) :
    invocations (h ++ k) = invocations h ++ invocations k :=
  List.filterMap_append

theorem responses_append (h k : History Op Response) :
    responses (h ++ k) = responses h ++ responses k :=
  List.filterMap_append

/-- `a` has an invocation event in `h`. -/
def Invoked (h : History Op Response) (a : Op) : Prop := Event.invoke a ∈ h

/-- `a` has a matching response event in `h` returning `v`. -/
def Responded (h : History Op Response) (a : Op) (v : Response) : Prop :=
  Event.respond a v ∈ h

/-- An invocation with no matching response: the paper's *pending* operation. -/
def Pending (h : History Op Response) (a : Op) : Prop :=
  h.Invoked a ∧ ¬ ∃ v, h.Responded a v

/-- `H|ᵢ`: the subsequence of events of process `i`. -/
def project [DecidableEq P] (proc : Op → P) (i : P) (h : History Op Response) :
    History Op Response :=
  h.filter (fun e => proc e.op = i)

variable [DecidableEq P]

@[simp] theorem project_nil (proc : Op → P) (i : P) :
    project (Response := Response) proc i [] = [] := rfl

theorem project_append (proc : Op → P) (i : P) (h k : History Op Response) :
    project proc i (h ++ k) = project proc i h ++ project proc i k :=
  List.filter_append _ _

theorem project_cons_pos {proc : Op → P} {i : P} {e : Event Op Response}
    {h : History Op Response} (he : proc e.op = i) :
    project proc i (e :: h) = e :: project proc i h := by
  simp [project, he]

theorem project_cons_neg {proc : Op → P} {i : P} {e : Event Op Response}
    {h : History Op Response} (he : proc e.op ≠ i) :
    project proc i (e :: h) = project proc i h := by
  simp [project, he]

/-- The alternating presentation of a well-formed per-process history: a list
of completed instances with their responses, followed by at most one pending
invocation. -/
def alternating (l : List (Op × Response)) (last : Option Op) : History Op Response :=
  l.flatMap (fun p => [Event.invoke p.1, Event.respond p.1 p.2]) ++
    (match last with | some a => [Event.invoke a] | none => [])

@[simp] theorem alternating_nil_none :
    alternating ([] : List (Op × Response)) none = [] := rfl

theorem alternating_none_append_invoke (l : List (Op × Response)) (a : Op) :
    alternating l none ++ [Event.invoke a] = alternating l (some a) := by
  simp [alternating]

theorem alternating_some_append_respond (l : List (Op × Response)) (a : Op) (v : Response) :
    alternating l (some a) ++ [Event.respond a v] = alternating (l ++ [(a, v)]) none := by
  simp [alternating]

/-- Filtering by a predicate on the underlying instance keeps the alternating
shape: completed blocks survive or vanish whole. -/
theorem filter_alternating (q : Op → Bool) (l : List (Op × Response)) (last : Option Op) :
    List.filter (fun e => q e.op) (alternating l last) =
      alternating (l.filter (fun p => q p.1))
        (match last with | some a => if q a then some a else none | none => none) := by
  unfold alternating
  rw [List.filter_append]
  congr 1
  · induction l with
    | nil => rfl
    | cons p l ih =>
      rw [List.flatMap_cons, List.filter_append, ih, List.filter_cons]
      by_cases h : q p.1 <;> simp [h]
  · cases last with
    | none => rfl
    | some a => by_cases h : q a <;> simp [h]

/-- Projection commutes with filtering on the underlying instance. -/
theorem project_filter (proc : Op → P) (i : P) (q : Op → Bool)
    (h : History Op Response) :
    project proc i (h.filter (fun ev => q ev.op)) =
      (project proc i h).filter (fun ev => q ev.op) := by
  unfold project
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext ev
  exact Bool.and_comm _ _

/-- Projecting a block of appended responses keeps the ones of process `i`. -/
theorem project_map_respond (proc : Op → P) (i : P)
    (l : List (Op × Response)) :
    project proc i (l.map (fun p => Event.respond p.1 p.2)) =
      (l.filter (fun p => proc p.1 = i)).map (fun p => Event.respond p.1 p.2) := by
  unfold project
  rw [List.filter_map]
  rfl

/-- The paper's well-formedness: every operation instance is invoked at most
once, and every process's projection is an alternating sequence of invocations
and matching responses, with at most a final pending invocation. -/
structure WellFormed (proc : Op → P) (h : History Op Response) : Prop where
  unique : h.invocations.Nodup
  sequential : ∀ i, ∃ l last, project proc i h = alternating l last

/-- Real-time order `≼_H`: a response event of `a` precedes an invocation
event of `b`. -/
def Precedes (h : History Op Response) (a b : Op) : Prop :=
  ∃ l r, h = l ++ r ∧ (∃ v, Event.respond a v ∈ l) ∧ Event.invoke b ∈ r

theorem Precedes.of_split {h l r : History Op Response} {a b : Op} {v : Response}
    (hsplit : h = l ++ r) (hv : Event.respond a v ∈ l) (hb : Event.invoke b ∈ r) :
    h.Precedes a b := ⟨l, r, hsplit, ⟨v, hv⟩, hb⟩

/-- A completion `H̄` of `H`: every pending invocation is either dropped or
extended with a matching response appended after the observed events.  Events
of completed instances, and the order of retained events, are untouched. -/
def IsCompletion (h hbar : History Op Response) : Prop :=
  ∃ (keep : Op → Bool) (ext : List (Op × Response)),
    hbar = h.filter (fun e => keep e.op) ++
      ext.map (fun p => Event.respond p.1 p.2) ∧
    (∀ a, h.Invoked a → keep a = false → h.Pending a) ∧
    (∀ p ∈ ext, h.Pending p.1 ∧ keep p.1 = true)

end History

/-! ## Two list utilities

Both are elementary but Mathlib-free: the development uses core and `Std`. -/

/-- Lists strictly increasing under an integer key are determined by their
members.  This is what makes "process `i`'s operations in invocation order"
and "process `i`'s operations in linearization order" the *same list*. -/
theorem pairwise_key_ext {α : Type} (key : α → Nat) :
    ∀ {l₁ l₂ : List α}, l₁.Pairwise (fun a b => key a < key b) →
      l₂.Pairwise (fun a b => key a < key b) →
      (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ _ hmem
    cases l₂ with
    | nil => rfl
    | cons b s => exact absurd ((hmem b).mpr (List.mem_cons_self ..)) (by simp)
  | cons a t ih =>
    intro l₂ h₁ h₂ hmem
    cases l₂ with
    | nil => exact absurd ((hmem a).mp (List.mem_cons_self ..)) (by simp)
    | cons b s =>
      obtain ⟨ha, h₁'⟩ := List.pairwise_cons.mp h₁
      obtain ⟨hb, h₂'⟩ := List.pairwise_cons.mp h₂
      have hab : a = b := by
        rcases List.mem_cons.mp ((hmem a).mp (List.mem_cons_self ..)) with h | h
        · exact h
        · rcases List.mem_cons.mp ((hmem b).mpr (List.mem_cons_self ..)) with h' | h'
          · exact h'.symm
          · exact absurd (Nat.lt_trans (ha b h') (hb a h)) (Nat.lt_irrefl _)
      subst b
      refine congrArg (a :: ·) (ih h₁' h₂' ?_)
      intro c
      constructor
      · intro hc
        rcases List.mem_cons.mp ((hmem c).mp (List.mem_cons_of_mem _ hc)) with rfl | h
        · exact absurd (ha c hc) (Nat.lt_irrefl _)
        · exact h
      · intro hc
        rcases List.mem_cons.mp ((hmem c).mpr (List.mem_cons_of_mem _ hc)) with rfl | h
        · exact absurd (hb c hc) (Nat.lt_irrefl _)
        · exact h

/-- A pair list whose second components are computed from the first is the
map of its first components. -/
theorem eq_map_of_snd {α β : Type} (g : α → β) :
    ∀ {R : List (α × β)}, (∀ p ∈ R, p.2 = g p.1) →
      R = (R.map Prod.fst).map (fun a => (a, g a)) := by
  intro R
  induction R with
  | nil => intro _; rfl
  | cons p t ih =>
    intro h
    rw [List.map_cons, List.map_cons, ← ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    exact congrArg (· :: t) (Prod.ext rfl (h p (List.mem_cons_self ..)))

/-- A duplicate-free list with a unique element satisfying `q` filters to it. -/
theorem filter_eq_singleton {α : Type} {q : α → Bool} :
    ∀ {l : List α} {c : α}, l.Nodup → c ∈ l → q c = true →
      (∀ a ∈ l, q a = true → a = c) → l.filter q = [c] := by
  intro l
  induction l with
  | nil => intro c _ hc _ _; cases hc
  | cons d l ih =>
    intro c hnd hc hq huniq
    obtain ⟨hd, hnd'⟩ := List.nodup_cons.mp hnd
    rw [List.filter_cons]
    by_cases hqd : q d = true
    · have hdc : d = c := huniq d (List.mem_cons_self ..) hqd
      subst d
      simp only [hqd, reduceIte]
      refine congrArg (c :: ·) (List.filter_eq_nil_iff.mpr ?_)
      intro a ha hqa
      exact hd ((huniq a (List.mem_cons_of_mem _ ha) hqa) ▸ ha)
    · simp only [hqd, Bool.false_eq_true, reduceIte]
      exact ih hnd' ((List.mem_cons.mp hc).resolve_left (fun h => hqd (h ▸ hq)))
        hq (fun a ha => huniq a (List.mem_cons_of_mem _ ha))

namespace Object
variable {State Op Response P : Type} (obj : Object State Op Response) [DecidableEq Op]

/-- The paper's `S_t̂`: the alternating invocation/response sequence obtained by
executing the schedule `x` from the initial state.  It is legal by
construction — `sequentialEvents_response` states exactly that each response is
the object's own answer in the state reached by the preceding prefix. -/
def sequentialEvents (x : List Op) : History Op Response :=
  History.alternating (obj.sequentialHistory x) none

/-- With unique identities, the concrete event list pairs each operation with
its response at its own position. -/
theorem sequentialHistory_eq_map {x : List Op} (hx : x.Nodup) :
    obj.sequentialHistory x = x.map (fun a => (a, obj.sequentialResponse x a)) := by
  apply List.ext_getElem
  · simp [sequentialHistory]
  · intro i hi hj
    simp only [sequentialHistory, List.getElem_mapIdx, List.getElem_map,
      sequentialResponse, hx.idxOf_getElem i (by simpa [sequentialHistory] using hi)]

omit [DecidableEq Op] in
/-- Legality of `S_t̂`: the value answered at position `p` is the object's
response to `x[p]` in the state reached by executing `x[0..p)`. -/
theorem sequentialEvents_response {x : List Op} {p : Nat} (hp : p < x.length) :
    (obj.sequentialHistory x)[p]? =
      some (x[p], (obj.step x[p] (obj.finalState (x.take p) obj.initial)).1) := by
  have hlen : (obj.sequentialHistory x).length = x.length := by
    simp [sequentialHistory]
  rw [List.getElem?_eq_getElem (by omega)]
  congr 1
  simp [sequentialHistory]

/-- The projection of `S_x` onto one process: its operations in schedule
order, each immediately followed by its response. -/
theorem project_sequentialEvents [DecidableEq P] (proc : Op → P) (i : P)
    {x : List Op} (hx : x.Nodup) :
    History.project proc i (obj.sequentialEvents x) =
      History.alternating
        ((x.filter (fun a => proc a = i)).map (fun a => (a, obj.sequentialResponse x a)))
        none := by
  rw [sequentialEvents, History.project,
    History.filter_alternating (fun a => decide (proc a = i)),
    obj.sequentialHistory_eq_map hx, List.filter_map]
  rfl

/-- Schedule order in `S_x` is real-time order in `S_x`. -/
theorem sequentialEvents_precedes {x : List Op} (hx : x.Nodup) {a b : Op}
    (_ha : a ∈ x) (hb : b ∈ x) (hlt : x.idxOf a < x.idxOf b) :
    (obj.sequentialEvents x).Precedes a b := by
  have hbj : x.idxOf b < x.length := List.idxOf_lt_length_of_mem hb
  have hsplit : obj.sequentialEvents x =
      ((obj.sequentialHistory x).take (x.idxOf b)).flatMap
          (fun p => [Event.invoke p.1, Event.respond p.1 p.2]) ++
        ((obj.sequentialHistory x).drop (x.idxOf b)).flatMap
          (fun p => [Event.invoke p.1, Event.respond p.1 p.2]) := by
    rw [← List.flatMap_append, List.take_append_drop]
    simp [sequentialEvents, History.alternating]
  refine History.Precedes.of_split hsplit (v := obj.sequentialResponse x a) ?_ ?_
  · refine List.mem_flatMap.mpr ⟨(a, obj.sequentialResponse x a), ?_, by simp⟩
    rw [obj.sequentialHistory_eq_map hx, ← List.map_take]
    refine List.mem_map.mpr ⟨a, ?_, rfl⟩
    have hai : x.idxOf a < (x.take (x.idxOf b)).length := by
      rw [List.length_take]; omega
    have hget : (x.take (x.idxOf b))[x.idxOf a] = a := by
      rw [List.getElem_take]
      exact List.getElem_idxOf (by omega)
    exact hget ▸ List.getElem_mem hai
  · refine List.mem_flatMap.mpr ⟨(b, obj.sequentialResponse x b), ?_, by simp⟩
    rw [obj.sequentialHistory_eq_map hx, ← List.map_drop]
    refine List.mem_map.mpr ⟨b, ?_, rfl⟩
    have hbi : 0 < (x.drop (x.idxOf b)).length := by
      rw [List.length_drop]; omega
    have hget : (x.drop (x.idxOf b))[0] = b := by
      rw [List.getElem_drop]
      simp [List.getElem_idxOf hbj]
    have hmem := List.getElem_mem hbi
    rwa [hget] at hmem

/-- **The paper's definition of linearizability**, on literal event sequences:
`h` has a completion `h̄` and a legal sequential history `S = S_x` such that
`h̄|ᵢ = S|ᵢ` for every process `i`, and the real-time order of `h` is preserved
in `S`.

The real-time clause is restricted to operations the completion retains.  That
is the usual convention (Herlihy–Wing order the *operations* of a history, and
a pending invocation dropped by the completion is not one); it is not a
restriction on the first operand, since `Precedes` already requires `a` to have
a response event. -/
def EventLinearizable [DecidableEq P] (proc : Op → P) (h : History Op Response) : Prop :=
  ∃ (hbar : History Op Response) (x : List Op),
    h.IsCompletion hbar ∧
    (∀ i, History.project proc i hbar = History.project proc i (obj.sequentialEvents x)) ∧
    (∀ a b, h.Precedes a b → History.Invoked hbar b →
      (obj.sequentialEvents x).Precedes a b)

end Object
end ConflictFreedom
