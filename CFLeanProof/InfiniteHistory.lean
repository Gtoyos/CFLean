import CFLeanProof.EventHistory

/-! # Infinite histories

The manuscript's history is "a sequence of operation invocation and response
events"; an infinite execution induces an infinite one.  `EventHistory` treats
finite sequences.  This module treats the general case: the paper's notions —
invocation, response, pending operation, per-process projection `H|ᵢ`,
real-time order `≼_H`, well-formedness, completion `H̄`, legal sequential
history `S` — and the paper's definition of linearizability, all stated on the
whole, possibly infinite, sequence of events.

A possibly infinite sequence is presented as the concatenation
`h 0 ++ h 1 ++ h 2 ++ ⋯` of finite blocks.  The history of a run has one block
per tick, holding at most one event; the sequential history of a schedule holds
an invocation and its response in one block.  A history is finite exactly when
its blocks are eventually empty (`ofHistory`).

The blocks are a presentation.  Invocation, response, pending operation,
real-time order and projection depend on the event sequence alone
(`SameEvents.invoked_iff`, `responded_iff`, `pending_iff`, `precedes_iff`,
`SameEvents.project`), and `SameEvents` — equality of event sequences — is the
equality used for `H̄|ᵢ = S|ᵢ`.  A completion is described block by block: its
added responses go at the ends of blocks, after their invocations.  For the
history of a run, whose blocks are single ticks, that is anywhere after the
invocation; for a finite history in one block, it is at the end, as in the
finite definition (`infEventLinearizable_ofHistory_iff`).
-/
namespace ConflictFreedom

/-- A possibly infinite history: the event sequence `h 0 ++ h 1 ++ ⋯`. -/
abbrev InfiniteHistory (Op Response : Type) := Nat → History Op Response

namespace InfiniteHistory
variable {Op Response P : Type}

/-- The finite history formed by the first `N` blocks. -/
def upto (h : InfiniteHistory Op Response) (N : Nat) : History Op Response :=
  (List.range N).flatMap h

@[simp] theorem upto_zero (h : InfiniteHistory Op Response) : h.upto 0 = [] := rfl

theorem upto_succ (h : InfiniteHistory Op Response) (N : Nat) :
    h.upto (N + 1) = h.upto N ++ h N := by
  simp [upto, List.range_succ, List.flatMap_append]

/-- The finite histories `h.upto N` are the prefixes of one sequence. -/
theorem upto_prefix (h : InfiniteHistory Op Response) {k m : Nat} (hkm : k ≤ m) :
    h.upto k <+: h.upto m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  clear hkm
  induction d with
  | zero => exact List.prefix_refl _
  | succ d ih =>
    refine List.IsPrefix.trans ih ?_
    rw [← Nat.add_assoc, upto_succ]
    exact List.prefix_append _ _

/-- `a` has an invocation event in `h`. -/
def Invoked (h : InfiniteHistory Op Response) (a : Op) : Prop :=
  ∃ N, (h.upto N).Invoked a

/-- `a` has a matching response event in `h` returning `v`. -/
def Responded (h : InfiniteHistory Op Response) (a : Op) (v : Response) : Prop :=
  ∃ N, (h.upto N).Responded a v

/-- An invocation of `h` with no matching response anywhere in `h`. -/
def Pending (h : InfiniteHistory Op Response) (a : Op) : Prop :=
  h.Invoked a ∧ ¬ ∃ v, h.Responded a v

/-- Real-time order `≼_H`: a response event of `a` precedes an invocation
event of `b`.  Both events sit in a finite prefix. -/
def Precedes (h : InfiniteHistory Op Response) (a b : Op) : Prop :=
  ∃ N, (h.upto N).Precedes a b

/-- `H|ᵢ`: the subsequence of events of process `i`. -/
def project [DecidableEq P] (proc : Op → P) (i : P) (h : InfiniteHistory Op Response) :
    InfiniteHistory Op Response :=
  fun t => History.project proc i (h t)

theorem upto_project [DecidableEq P] (proc : Op → P) (i : P)
    (h : InfiniteHistory Op Response) (N : Nat) :
    (h.project proc i).upto N = History.project proc i (h.upto N) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [upto_succ, upto_succ, ih, History.project_append]; rfl

/-- The paper's well-formedness, for a possibly infinite sequence: every
finite prefix has unique instances and is sequential per process. -/
def WellFormed [DecidableEq P] (proc : Op → P) (h : InfiniteHistory Op Response) : Prop :=
  ∀ N, (h.upto N).WellFormed proc

/-- `h` and `h'` are the same sequence of events: every finite prefix of each
is a prefix of a finite prefix of the other.  This is literal equality of the
two (finite or infinite) event sequences, whatever their block presentation. -/
def SameEvents (h h' : InfiniteHistory Op Response) : Prop :=
  (∀ N, ∃ M, h.upto N <+: h'.upto M) ∧ (∀ M, ∃ N, h'.upto M <+: h.upto N)

theorem SameEvents.refl (h : InfiniteHistory Op Response) : h.SameEvents h :=
  ⟨fun N => ⟨N, List.prefix_refl _⟩, fun M => ⟨M, List.prefix_refl _⟩⟩

theorem SameEvents.symm {h h' : InfiniteHistory Op Response} (e : h.SameEvents h') :
    h'.SameEvents h :=
  ⟨e.2, e.1⟩

theorem SameEvents.trans {h h' h'' : InfiniteHistory Op Response}
    (e : h.SameEvents h') (e' : h'.SameEvents h'') : h.SameEvents h'' := by
  refine ⟨fun N => ?_, fun M => ?_⟩
  · obtain ⟨M, hM⟩ := e.1 N
    obtain ⟨K, hK⟩ := e'.1 M
    exact ⟨K, hM.trans hK⟩
  · obtain ⟨K, hK⟩ := e'.2 M
    obtain ⟨N, hN⟩ := e.2 K
    exact ⟨N, hK.trans hN⟩

/-- A completion `H̄` of `H`, as in the finite case: every pending invocation
is either dropped or kept, and each kept one may receive a matching response,
added at the end of a block no earlier than its invocation's.  Every other event
keeps its place, and no other event is added.  In a finite history the added
responses can be appended at the end; an infinite history has no end, so they
are placed in the sequence. -/
def IsCompletion (h hbar : InfiniteHistory Op Response) : Prop :=
  ∃ (keep : Op → Bool) (ext : Nat → List (Op × Response)),
    (∀ t, hbar t = (h t).filter (fun e => keep e.op) ++
      (ext t).map (fun p => Event.respond p.1 p.2)) ∧
    (∀ a, h.Invoked a → keep a = false → h.Pending a) ∧
    (∀ t, ∀ p ∈ ext t, h.Pending p.1 ∧ keep p.1 = true ∧ (h.upto (t + 1)).Invoked p.1)

/-! ### Finite histories are infinite histories -/

/-- A finite history, as the sequence whose events all lie in the first block. -/
def ofHistory (l : History Op Response) : InfiniteHistory Op Response :=
  fun t => if t = 0 then l else []

theorem upto_ofHistory (l : History Op Response) {N : Nat} (hN : 0 < N) :
    (ofHistory l).upto N = l := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  clear hN
  induction M with
  | zero => rw [upto_succ, upto_zero]; simp [ofHistory]
  | succ M ih => rw [upto_succ, ih]; simp [ofHistory]

/-- On finite histories, `SameEvents` is equality. -/
theorem sameEvents_ofHistory_iff {l l' : History Op Response} :
    (ofHistory l).SameEvents (ofHistory l') ↔ l = l' := by
  constructor
  · intro ⟨h1, h2⟩
    have hle : ∀ {k k' : History Op Response}, (∀ N, ∃ M, (ofHistory k).upto N <+:
        (ofHistory k').upto M) → k <+: k' := by
      intro k k' hk
      obtain ⟨M, hM⟩ := hk 1
      rw [upto_ofHistory k (by omega)] at hM
      rcases Nat.eq_zero_or_pos M with rfl | hpos
      · rw [upto_zero, List.prefix_nil] at hM
        rw [hM]; exact List.nil_prefix
      · rwa [upto_ofHistory k' hpos] at hM
    have a := hle h1
    have b := hle h2
    exact a.eq_of_length (Nat.le_antisymm a.length_le b.length_le)
  · rintro rfl; exact SameEvents.refl _

@[simp] theorem invoked_ofHistory {l : History Op Response} {a : Op} :
    (ofHistory l).Invoked a ↔ l.Invoked a := by
  constructor
  · rintro ⟨N, hN⟩
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · cases hN
    · rwa [upto_ofHistory l hpos] at hN
  · intro ha; exact ⟨1, by rwa [upto_ofHistory l (by omega)]⟩

@[simp] theorem responded_ofHistory {l : History Op Response} {a : Op} {v : Response} :
    (ofHistory l).Responded a v ↔ l.Responded a v := by
  constructor
  · rintro ⟨N, hN⟩
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · cases hN
    · rwa [upto_ofHistory l hpos] at hN
  · intro ha; exact ⟨1, by rwa [upto_ofHistory l (by omega)]⟩

theorem precedes_ofHistory {l : History Op Response} {a b : Op} :
    (ofHistory l).Precedes a b ↔ l.Precedes a b := by
  constructor
  · rintro ⟨N, hN⟩
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · obtain ⟨l₁, l₂, hs, _, hb⟩ := hN
      rw [upto_zero] at hs
      rw [(List.append_eq_nil_iff.mp hs.symm).2] at hb
      cases hb
    · rwa [upto_ofHistory l hpos] at hN
  · intro h; exact ⟨1, by rwa [upto_ofHistory l (by omega)]⟩

end InfiniteHistory

/-! ## Alternating sequences grow by prefixes -/

namespace History
variable {Op Response : Type}

theorem alternating_none_prefix_append (l m : List (Op × Response)) (o : Option Op) :
    alternating l none <+: alternating (l ++ m) o := by
  simp only [alternating, List.flatMap_append, List.append_nil, List.append_assoc]
  exact List.prefix_append _ _

theorem alternating_none_prefix (l : List (Op × Response)) (o : Option Op) :
    alternating l none <+: alternating l o := by
  simpa using alternating_none_prefix_append l [] o

theorem alternating_some_prefix (l m : List (Op × Response)) (c : Op) (v : Response)
    (o : Option Op) :
    alternating l (some c) <+: alternating (l ++ (c, v) :: m) o := by
  simp only [alternating, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  refine List.prefix_append_right_inj _ |>.mpr ?_
  exact ⟨_, rfl⟩

end History

/-! ## The sequential history of a possibly infinite schedule -/

namespace Object
variable {State Op Response P : Type} (obj : Object State Op Response)

theorem sequentialHistory_concat (l : List Op) (a : Op) :
    obj.sequentialHistory (l ++ [a]) =
      obj.sequentialHistory l ++ [(a, (obj.step a (obj.finalState l obj.initial)).1)] := by
  unfold sequentialHistory
  rw [List.mapIdx_concat]
  congr 1
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_mapIdx]
      have hi : i < l.length := by simpa using h1
      rw [List.take_append_of_le_length (by omega)]
  · simp

theorem sequentialEvents_concat (l : List Op) (a : Op) :
    obj.sequentialEvents (l ++ [a]) = obj.sequentialEvents l ++
      [Event.invoke a, Event.respond a (obj.step a (obj.finalState l obj.initial)).1] := by
  simp [sequentialEvents, History.alternating, sequentialHistory_concat, List.flatMap_append]

/-- Executing more of a schedule extends the sequential history. -/
theorem sequentialEvents_prefix_append (l z : List Op) :
    obj.sequentialEvents l <+: obj.sequentialEvents (l ++ z) := by
  induction z generalizing l with
  | nil => simp
  | cons b z ih =>
    have h := ih (l ++ [b])
    rw [List.append_assoc, List.singleton_append] at h
    refine List.IsPrefix.trans ?_ h
    rw [sequentialEvents_concat]
    exact List.prefix_append _ _

theorem sequentialEvents_prefix {l l' : List Op} (h : l <+: l') :
    obj.sequentialEvents l <+: obj.sequentialEvents l' := by
  obtain ⟨z, rfl⟩ := h
  exact obj.sequentialEvents_prefix_append l z

/-- `S_X`: the paper's sequential history of a possibly infinite schedule `X`,
position `k` holding at most one operation instance.  Block `k` invokes the
operation at position `k` and at once returns the object's response in the
state reached by executing every earlier position from `q₀`: the history is
sequential and legal by construction, and its finite prefixes are the finite
sequential histories `S_x` (`sequentialStream_upto`). -/
def sequentialStream (X : Nat → Option Op) : InfiniteHistory Op Response := fun k =>
  match X k with
  | none => []
  | some a => [Event.invoke a,
      Event.respond a (obj.step a (obj.finalState ((List.range k).filterMap X) obj.initial)).1]

theorem sequentialStream_upto (X : Nat → Option Op) (N : Nat) :
    (obj.sequentialStream X).upto N = obj.sequentialEvents ((List.range N).filterMap X) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [InfiniteHistory.upto_succ, ih, List.range_succ, List.filterMap_append]
    cases hX : X N with
    | none => simp [sequentialStream, hX]
    | some a => simp [sequentialStream, hX, sequentialEvents_concat]

/-- **The paper's definition of linearizability, for a possibly infinite
history**: `h` has a completion `h̄` and a legal sequential history `S = S_X`
such that `h̄|ᵢ = S|ᵢ` for every process `i`, as sequences of events, and the
real-time order of `h` is preserved in `S`.

This is `EventLinearizable` with each finite object replaced by a possibly
infinite one: the schedule `X` is the linearization order (finite or
infinite), `S_X` its execution from `q₀`, and the real-time clause is again
restricted to operations the completion retains. -/
def InfEventLinearizable [DecidableEq P] (proc : Op → P) (h : InfiniteHistory Op Response) :
    Prop :=
  ∃ (hbar : InfiniteHistory Op Response) (X : Nat → Option Op),
    h.IsCompletion hbar ∧
    (∀ i, (hbar.project proc i).SameEvents ((obj.sequentialStream X).project proc i)) ∧
    (∀ a b, h.Precedes a b → hbar.Invoked b → (obj.sequentialStream X).Precedes a b)

end Object

/-! ## On finite histories the two definitions agree

`InfEventLinearizable` is a conservative extension of the manuscript's finite
definition `EventLinearizable`: a well-formed finite history is linearizable in
one sense exactly when it is in the other
(`Object.infEventLinearizable_ofHistory_iff`). -/

section Lists
variable {α β : Type}

/-- A list whose parts, split by a key, are duplicate-free is duplicate-free. -/
theorem nodup_of_filter_nodup [DecidableEq β] (f : α → β) {l : List α}
    (h : ∀ i, (l.filter (fun a => f a = i)).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    have ha := h (f a)
    rw [List.filter_cons_of_pos (by simp), List.nodup_cons] at ha
    refine List.nodup_cons.mpr ⟨fun hm => ha.1 (List.mem_filter.mpr ⟨hm, by simp⟩),
      ih (fun i => (h i).sublist ((List.sublist_cons_self a l).filter _))⟩

/-- A duplicate-free list drawn from `m` is no longer than `m`. -/
theorem length_le_of_nodup_subset {l m : List α} (hl : l.Nodup) (h : ∀ a ∈ l, a ∈ m) :
    l.length ≤ m.length := by
  classical
  induction l generalizing m with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    obtain ⟨hal, hnd⟩ := List.nodup_cons.mp hl
    have ham : a ∈ m := h a (List.mem_cons_self ..)
    have hle := ih hnd (m := m.erase a) (fun b hb =>
      (List.mem_erase_of_ne (fun hba : b = a => hal (hba ▸ hb))).mpr
        (h b (List.mem_cons_of_mem _ hb)))
    rw [List.length_erase_of_mem ham] at hle
    have := List.length_pos_of_mem ham
    simp only [List.length_cons]
    omega

theorem range_filterMap_prefix (f : Nat → Option α) {M K : Nat} (h : M ≤ K) :
    (List.range M).filterMap f <+: (List.range K).filterMap f := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact List.prefix_refl _
  | succ d ih =>
    refine List.IsPrefix.trans ih ?_
    rw [← Nat.add_assoc, List.range_succ, List.filterMap_append]
    exact List.prefix_append _ _

end Lists

namespace History
variable {Op Response P : Type}

theorem invocations_project [DecidableEq P] (proc : Op → P) (i : P) (h : History Op Response) :
    (project proc i h).invocations = h.invocations.filter (fun a => proc a = i) := by
  induction h with
  | nil => rfl
  | cons ev h ih =>
    by_cases hev : proc ev.op = i
    · rw [project_cons_pos hev]
      cases ev with
      | invoke a =>
        simp only [invocations, List.filterMap_cons, Event.invokedOp_invoke] at ih ⊢
        rw [List.filter_cons_of_pos (by simpa using hev), ih]
      | respond a v =>
        simp only [invocations, List.filterMap_cons, Event.invokedOp_respond] at ih ⊢
        exact ih
    · rw [project_cons_neg hev]
      cases ev with
      | invoke a =>
        simp only [invocations, List.filterMap_cons, Event.invokedOp_invoke] at ih ⊢
        rw [List.filter_cons_of_neg (by simpa using hev), ih]
      | respond a v =>
        simp only [invocations, List.filterMap_cons, Event.invokedOp_respond] at ih ⊢
        exact ih

theorem Precedes.of_prefix {l l' : History Op Response} {a b : Op} (h : l.Precedes a b)
    (hp : l <+: l') : l'.Precedes a b := by
  obtain ⟨l₁, l₂, rfl, hv, hb⟩ := h
  obtain ⟨z, rfl⟩ := hp
  exact ⟨l₁, l₂ ++ z, by simp, hv, List.mem_append_left _ hb⟩

theorem pairs_nodup (L : List (Op × Response)) (hL : (L.map Prod.fst).Nodup) :
    (L.flatMap (fun p => [Event.invoke p.1, Event.respond p.1 p.2])).Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons q L ih =>
    obtain ⟨hq, hL'⟩ := List.nodup_cons.mp hL
    have hop : ∀ ev ∈ L.flatMap (fun p => [Event.invoke p.1, Event.respond p.1 p.2]),
        ev.op ≠ q.1 := by
      intro ev hev heq
      obtain ⟨p, hp, hevp⟩ := List.mem_flatMap.mp hev
      have : ev.op = p.1 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hevp
        rcases hevp with rfl | rfl <;> rfl
      exact hq (List.mem_map.mpr ⟨p, hp, by rw [← this, heq]⟩)
    rw [List.flatMap_cons]
    refine List.nodup_append.mpr ⟨?_, ih hL', ?_⟩
    · simp [List.nodup_cons]
    · intro a ha b hb hab
      subst hab
      have : a.op = q.1 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> rfl
      exact hop a hb this

end History

namespace InfiniteHistory
variable {Op Response P : Type}

/-! ### The notions depend on the event sequence alone -/

theorem SameEvents.invoked_iff {h h' : InfiniteHistory Op Response} (e : h.SameEvents h')
    {a : Op} : h.Invoked a ↔ h'.Invoked a := by
  constructor
  · rintro ⟨N, hN⟩; obtain ⟨M, hM⟩ := e.1 N; exact ⟨M, hM.subset hN⟩
  · rintro ⟨M, hM⟩; obtain ⟨N, hN⟩ := e.2 M; exact ⟨N, hN.subset hM⟩

theorem SameEvents.responded_iff {h h' : InfiniteHistory Op Response} (e : h.SameEvents h')
    {a : Op} {v : Response} : h.Responded a v ↔ h'.Responded a v := by
  constructor
  · rintro ⟨N, hN⟩; obtain ⟨M, hM⟩ := e.1 N; exact ⟨M, hM.subset hN⟩
  · rintro ⟨M, hM⟩; obtain ⟨N, hN⟩ := e.2 M; exact ⟨N, hN.subset hM⟩

theorem SameEvents.pending_iff {h h' : InfiniteHistory Op Response} (e : h.SameEvents h')
    {a : Op} : h.Pending a ↔ h'.Pending a := by
  simp only [Pending, e.invoked_iff, e.responded_iff]

theorem SameEvents.precedes_iff {h h' : InfiniteHistory Op Response} (e : h.SameEvents h')
    {a b : Op} : h.Precedes a b ↔ h'.Precedes a b := by
  constructor
  · rintro ⟨N, hN⟩; obtain ⟨M, hM⟩ := e.1 N; exact ⟨M, hN.of_prefix hM⟩
  · rintro ⟨M, hM⟩; obtain ⟨N, hN⟩ := e.2 M; exact ⟨N, hM.of_prefix hN⟩

theorem SameEvents.project [DecidableEq P] {h h' : InfiniteHistory Op Response}
    (e : h.SameEvents h') (proc : Op → P) (i : P) :
    (h.project proc i).SameEvents (h'.project proc i) := by
  refine ⟨fun N => ?_, fun M => ?_⟩
  · obtain ⟨M, hM⟩ := e.1 N
    exact ⟨M, by rw [upto_project, upto_project]; exact hM.filter _⟩
  · obtain ⟨N, hN⟩ := e.2 M
    exact ⟨N, by rw [upto_project, upto_project]; exact hN.filter _⟩

@[simp] theorem pending_ofHistory {l : History Op Response} {a : Op} :
    (ofHistory l).Pending a ↔ l.Pending a := by
  simp [Pending, History.Pending]

theorem upto_ofHistory_zero (l : History Op Response) : (ofHistory l).upto 0 = [] := rfl

theorem project_ofHistory [DecidableEq P] (proc : Op → P) (i : P) (l : History Op Response) :
    (ofHistory l).project proc i = ofHistory (History.project proc i l) := by
  funext t
  by_cases ht : t = 0 <;> simp [project, ofHistory, ht]

/-- A history whose finite prefixes have bounded length is finite: its
prefixes are eventually constant. -/
theorem upto_stable_of_bounded (h : InfiniteHistory Op Response) {B : Nat}
    (hb : ∀ N, (h.upto N).length ≤ B) : ∃ T, ∀ N, T ≤ N → h.upto N = h.upto T := by
  suffices key : ∀ d K, B - (h.upto K).length ≤ d →
      ∃ T, ∀ N, T ≤ N → h.upto N = h.upto T from key B 0 (by omega)
  intro d
  induction d with
  | zero =>
    intro K hK
    refine ⟨K, fun N hN => ((h.upto_prefix hN).eq_of_length_le ?_).symm⟩
    have := hb N
    omega
  | succ d ih =>
    intro K hK
    by_cases hall : ∀ N, K ≤ N → (h.upto N).length = (h.upto K).length
    · exact ⟨K, fun N hN => ((h.upto_prefix hN).eq_of_length_le (Nat.le_of_eq (hall N hN))).symm⟩
    · obtain ⟨N, hN, hne⟩ : ∃ N, K ≤ N ∧ (h.upto N).length ≠ (h.upto K).length :=
        Classical.byContradiction fun hno =>
          hall fun N hN => Classical.byContradiction fun hne => hno ⟨N, hN, hne⟩
      have hle := (h.upto_prefix hN).length_le
      exact ih N (by have := hb N; omega)

end InfiniteHistory

namespace Object
variable {State Op Response P : Type} (obj : Object State Op Response)

theorem invocations_sequentialEvents (x : List Op) :
    (obj.sequentialEvents x).invocations = x := by
  have h : ∀ L : List (Op × Response),
      (L.flatMap (fun p => [Event.invoke p.1, Event.respond p.1 p.2])).filterMap
        Event.invokedOp = L.map Prod.fst := by
    intro L
    induction L with
    | nil => rfl
    | cons q L ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.filterMap_cons,
        Event.invokedOp_invoke, Event.invokedOp_respond, ih, List.map_cons]
  simp only [sequentialEvents, History.alternating, History.invocations, List.append_nil]
  rw [h, sequentialHistory_commands]

theorem length_sequentialEvents (x : List Op) :
    (obj.sequentialEvents x).length = 2 * x.length := by
  have h : ∀ L : List (Op × Response),
      (L.flatMap (fun p => [Event.invoke p.1, Event.respond p.1 p.2])).length = 2 * L.length := by
    intro L
    induction L with
    | nil => rfl
    | cons q L ih => simp [List.flatMap_cons, ih]; omega
  simp only [sequentialEvents, History.alternating, List.append_nil]
  rw [h]
  simp [sequentialHistory]

theorem sequentialEvents_nodup {x : List Op} (hx : x.Nodup) : (obj.sequentialEvents x).Nodup := by
  simp only [sequentialEvents, History.alternating, List.append_nil]
  exact History.pairs_nodup _ (by rw [sequentialHistory_commands]; exact hx)

/-- A finite linearizable history is linearizable as an infinite one. -/
theorem infEventLinearizable_ofHistory [DecidableEq P] {proc : Op → P}
    {l : History Op Response} (h : obj.EventLinearizable proc l) :
    obj.InfEventLinearizable proc (InfiniteHistory.ofHistory l) := by
  obtain ⟨hbar, x, ⟨keep, ext, rfl, hdrop, hext⟩, hproj, hrt⟩ := h
  have hX : ∀ M, (List.range M).filterMap (fun k => x[k]?) = x.take M := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih =>
      rw [List.range_succ, List.filterMap_append, ih, List.take_add_one]
      simp only [List.filterMap_cons, List.filterMap_nil]
      cases x[M]? <;> rfl
  refine ⟨InfiniteHistory.ofHistory (l.filter (fun e => keep e.op) ++
      ext.map (fun p => Event.respond p.1 p.2)), fun k => x[k]?,
    ⟨keep, fun t => if t = 0 then ext else [], fun t => ?_, fun a ha hk => ?_, fun t p hp => ?_⟩,
    fun i => ?_, fun a b hab hb => ?_⟩
  · by_cases ht : t = 0 <;> simp [InfiniteHistory.ofHistory, ht]
  · exact InfiniteHistory.pending_ofHistory.mpr
      (hdrop a (InfiniteHistory.invoked_ofHistory.mp ha) hk)
  · by_cases ht : t = 0
    · subst ht
      simp only [ite_true] at hp
      obtain ⟨hpend, hkeep⟩ := hext p hp
      refine ⟨InfiniteHistory.pending_ofHistory.mpr hpend, hkeep, ?_⟩
      rw [InfiniteHistory.upto_ofHistory l (by omega)]
      exact hpend.1
    · simp [ht] at hp
  · rw [InfiniteHistory.project_ofHistory, hproj i]
    refine ⟨fun N => ⟨x.length, ?_⟩, fun M => ⟨1, ?_⟩⟩
    · rw [InfiniteHistory.upto_project, sequentialStream_upto, hX, List.take_length]
      rcases Nat.eq_zero_or_pos N with rfl | hpos
      · exact List.nil_prefix
      · rw [InfiniteHistory.upto_ofHistory _ hpos]
        exact List.prefix_refl _
    · rw [InfiniteHistory.upto_project, sequentialStream_upto, hX,
        InfiniteHistory.upto_ofHistory _ (by omega)]
      exact (obj.sequentialEvents_prefix (List.take_prefix M x)).filter _
  · refine ⟨x.length, ?_⟩
    rw [sequentialStream_upto, hX, List.take_length]
    exact hrt a b (InfiniteHistory.precedes_ofHistory.mp hab)
      (InfiniteHistory.invoked_ofHistory.mp hb)

/-- A well-formed finite history linearizable as an infinite one is
linearizable.  The sequential history has finitely many events because each
of its invocations is one of the history's, at most once; the completion
then has finitely many because each of its events is one of the sequential
history's, at most once. -/
theorem eventLinearizable_of_ofHistory [DecidableEq P] {proc : Op → P}
    {l : History Op Response} (hwf : l.invocations.Nodup)
    (h : obj.InfEventLinearizable proc (InfiniteHistory.ofHistory l)) :
    obj.EventLinearizable proc l := by
  classical
  obtain ⟨hbar, X, ⟨keep, ext, hblock, hdrop, hext⟩, hproj, hrt⟩ := h
  -- The completion invokes only the history's operations, once each.
  have hbar_inv : ∀ N, List.Sublist (hbar.upto N).invocations l.invocations := by
    intro N
    have hform : ∀ N, (hbar.upto (N + 1)).invocations =
        History.invocations (l.filter (fun e => keep e.op)) := by
      intro N
      induction N with
      | zero =>
        rw [InfiniteHistory.upto_succ, InfiniteHistory.upto_zero, List.nil_append, hblock]
        simp [InfiniteHistory.ofHistory, History.invocations]
      | succ N ih =>
        rw [InfiniteHistory.upto_succ, History.invocations_append, ih, hblock]
        simp [InfiniteHistory.ofHistory, History.invocations]
    rcases N with _ | N
    · exact List.nil_sublist _
    · rw [hform N]
      exact List.filter_sublist.filterMap _
  -- The schedule of `S` is drawn from the history's invocations, once each.
  have hXinv : ∀ M i, List.Sublist (((List.range M).filterMap X).filter (fun a => proc a = i))
      l.invocations := by
    intro M i
    obtain ⟨N, hN⟩ := (hproj i).2 M
    rw [InfiniteHistory.upto_project, InfiniteHistory.upto_project, sequentialStream_upto] at hN
    have := hN.sublist.filterMap Event.invokedOp
    rw [← History.invocations, ← History.invocations, History.invocations_project,
      History.invocations_project, invocations_sequentialEvents] at this
    exact this.trans (List.filter_sublist.trans (hbar_inv N))
  have hXnd : ∀ M, ((List.range M).filterMap X).Nodup := fun M =>
    nodup_of_filter_nodup proc (fun i => hwf.sublist (hXinv M i))
  have hXmem : ∀ M, ∀ a ∈ (List.range M).filterMap X, a ∈ l.invocations := fun M a ha =>
    (hXinv M (proc a)).subset (List.mem_filter.mpr ⟨ha, by simp⟩)
  -- Hence `S` is finite.
  obtain ⟨K, hK⟩ := (obj.sequentialStream X).upto_stable_of_bounded
    (B := 2 * l.invocations.length) (fun M => by
      rw [sequentialStream_upto, length_sequentialEvents]
      have := length_le_of_nodup_subset (hXnd M) (hXmem M)
      omega)
  let x := (List.range K).filterMap X
  have hxnd : x.Nodup := hXnd K
  have hSK : (obj.sequentialStream X).upto K = obj.sequentialEvents x := sequentialStream_upto ..
  have hSle : ∀ M, (obj.sequentialStream X).upto M <+: obj.sequentialEvents x := by
    intro M
    rcases Nat.le_total M K with h | h
    · rw [← hSK]; exact (obj.sequentialStream X).upto_prefix h
    · rw [hK M h, hSK]
      exact List.prefix_refl _
  -- `H̄|ᵢ` never outgrows `S|ᵢ`.
  have hA : ∀ i N, (hbar.project proc i).upto N <+:
      History.project proc i (obj.sequentialEvents x) := by
    intro i N
    obtain ⟨M, hM⟩ := (hproj i).1 N
    rw [InfiniteHistory.upto_project proc i (obj.sequentialStream X)] at hM
    exact hM.trans ((hSle M).filter _)
  -- Hence `H̄` is finite too.
  obtain ⟨T, hT⟩ := hbar.upto_stable_of_bounded (B := (obj.sequentialEvents x).length)
    (fun N => by
      refine length_le_of_nodup_subset ?_ (fun ev hev => ?_)
      · refine nodup_of_filter_nodup (fun ev => proc ev.op) (fun i => ?_)
        have := hA i N
        rw [InfiniteHistory.upto_project] at this
        exact ((obj.sequentialEvents_nodup hxnd).sublist List.filter_sublist).sublist
          this.sublist
      · have := (hA (proc ev.op) N).subset
        rw [InfiniteHistory.upto_project] at this
        exact (List.mem_filter.mp (this (List.mem_filter.mpr ⟨hev, by simp⟩))).1)
  -- The finite completion: all of `H̄`.
  have hform : ∀ M, hbar.upto (M + 1) = l.filter (fun e => keep e.op) ++
      ((List.range (M + 1)).flatMap ext).map (fun p => Event.respond p.1 p.2) := by
    intro M
    induction M with
    | zero =>
      rw [InfiniteHistory.upto_succ, InfiniteHistory.upto_zero, List.nil_append, hblock]
      simp [InfiniteHistory.ofHistory]
    | succ M ih =>
      rw [InfiniteHistory.upto_succ, ih, hblock, List.range_succ (n := M + 1),
        List.flatMap_append]
      simp [InfiniteHistory.ofHistory]
  refine ⟨hbar.upto (T + 1), x, ⟨keep, (List.range (T + 1)).flatMap ext, hform T,
    fun a ha hk => ?_, fun p hp => ?_⟩, fun i => ?_, fun a b hab hb => ?_⟩
  · exact InfiniteHistory.pending_ofHistory.mp
      (hdrop a (InfiniteHistory.invoked_ofHistory.mpr ha) hk)
  · obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hp
    obtain ⟨hpend, hkeep, _⟩ := hext t p ht
    exact ⟨InfiniteHistory.pending_ofHistory.mp hpend, hkeep⟩
  · refine (List.IsPrefix.eq_of_length_le ?_ ?_)
    · have := hA i (T + 1); rwa [InfiniteHistory.upto_project] at this
    · obtain ⟨N, hN⟩ := (hproj i).2 K
      rw [InfiniteHistory.upto_project proc i (obj.sequentialStream X), hSK] at hN
      have h2 := hN.trans ((hbar.project proc i).upto_prefix (Nat.le_add_right N (T + 1)))
      rw [InfiniteHistory.upto_project, hT (N + (T + 1)) (by omega),
        ← hT (T + 1) (by omega)] at h2
      exact h2.length_le
  · obtain ⟨M, hM⟩ := hrt a b (InfiniteHistory.precedes_ofHistory.mpr hab) ⟨T + 1, hb⟩
    exact hM.of_prefix (hSle M)

/-- **The infinite definition is conservative**: on a well-formed finite
history it is the manuscript's definition of linearizability. -/
theorem infEventLinearizable_ofHistory_iff [DecidableEq P] {proc : Op → P}
    {l : History Op Response} (hwf : l.WellFormed proc) :
    obj.InfEventLinearizable proc (InfiniteHistory.ofHistory l) ↔
      obj.EventLinearizable proc l :=
  ⟨obj.eventLinearizable_of_ofHistory hwf.unique, obj.infEventLinearizable_ofHistory⟩

end Object

/-! ## The limit of a chain of finite linearizations -/

section Chain
variable {α : Type}

/-- The limit of a chain of lists, each a prefix of the next: position `k`
holds the `k`-th entry of any list of the chain long enough to have one, and
nothing if no list is.  For a chain of linearizations this is the paper's
`t̂ = ŝ₁ ŝ₂ ⋯`, a single (finite or infinite) sequential order. -/
noncomputable def chainLimit (x : Nat → List α) (k : Nat) : Option α :=
  @dite _ (∃ N, k < (x N).length) (Classical.propDecidable _)
    (fun h => (x (Classical.choose h))[k]?) (fun _ => none)

variable {x : Nat → List α}

theorem chain_getElem?_eq (hchain : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z)
    {N M k : Nat} (hN : k < (x N).length) (hM : k < (x M).length) :
    (x N)[k]? = (x M)[k]? := by
  rcases Nat.le_total N M with h | h
  · obtain ⟨z, hz⟩ := hchain N M h
    rw [hz, List.getElem?_append_left hN]
  · obtain ⟨z, hz⟩ := hchain M N h
    rw [hz, List.getElem?_append_left hM]

theorem chainLimit_eq (hchain : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z)
    {N k : Nat} (hk : k < (x N).length) : chainLimit x k = (x N)[k]? := by
  have h : ∃ N, k < (x N).length := ⟨N, hk⟩
  unfold chainLimit
  rw [dite_eq_left h]
  exact chain_getElem?_eq hchain (Classical.choose_spec h) hk

theorem range_filterMap_eq_take {l : List α} {f : Nat → Option α} {L : Nat}
    (hL : L ≤ l.length) (hf : ∀ k, k < L → f k = l[k]?) :
    (List.range L).filterMap f = l.take L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.filterMap_append, ih (by omega) (fun k hk => hf k (by omega)),
      List.take_add_one]
    simp [hf L (by omega), List.getElem?_eq_getElem (by omega : L < l.length)]

/-- Each list of the chain is an initial segment of the limit. -/
theorem chainLimit_range (hchain : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z) (N : Nat) :
    (List.range (x N).length).filterMap (chainLimit x) = x N := by
  rw [range_filterMap_eq_take (Nat.le_refl _) (fun k hk => chainLimit_eq hchain hk),
    List.take_length]

/-- Each initial segment of the limit lies in the chain. -/
theorem chainLimit_cofinal (hchain : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z) (M : Nat) :
    ∃ N, (List.range M).filterMap (chainLimit x) <+: x N := by
  induction M with
  | zero => exact ⟨0, List.nil_prefix⟩
  | succ M ih =>
    by_cases h : ∃ N, M < (x N).length
    · obtain ⟨N, hN⟩ := h
      refine ⟨N, ?_⟩
      rw [range_filterMap_eq_take (l := x N) (by omega)
        (fun k hk => chainLimit_eq hchain (by omega))]
      exact List.take_prefix _ _
    · obtain ⟨N, hN⟩ := ih
      refine ⟨N, ?_⟩
      have hnone : chainLimit x M = none := by
        unfold chainLimit
        rw [dite_eq_right h]
      rw [List.range_succ, List.filterMap_append]
      simpa [hnone] using hN

end Chain

namespace Object
variable {State Op Response : Type} (obj : Object State Op Response) [DecidableEq Op]

/-- A response computed in a schedule is unchanged by executing more of it. -/
theorem sequentialResponse_append {l : List Op} (z : List Op) {a : Op} (ha : a ∈ l) :
    obj.sequentialResponse (l ++ z) a = obj.sequentialResponse l a := by
  unfold sequentialResponse
  rw [List.idxOf_append, ite_eq_left ha,
    List.take_append_of_le_length (Nat.le_of_lt (List.idxOf_lt_length_of_mem ha))]

/-- The response of `a` in the limit order of a chain: its sequential response
in any list of the chain that contains it. -/
noncomputable def chainResponse (x : Nat → List Op) (a : Op) : Response :=
  @dite _ (∃ N, a ∈ x N) (Classical.propDecidable _)
    (fun h => obj.sequentialResponse (x (Classical.choose h)) a)
    (fun _ => obj.sequentialResponse [] a)

theorem sequentialResponse_chain {x : Nat → List Op}
    (hchain : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z) {N : Nat} {a : Op} (ha : a ∈ x N) :
    obj.sequentialResponse (x N) a = obj.chainResponse x a := by
  have h : ∃ N, a ∈ x N := ⟨N, ha⟩
  unfold chainResponse
  rw [dite_eq_left h]
  have hc := Classical.choose_spec h
  rcases Nat.le_total N (Classical.choose h) with hle | hle
  · obtain ⟨z, hz⟩ := hchain _ _ hle
    rw [hz, obj.sequentialResponse_append z ha]
  · obtain ⟨z, hz⟩ := hchain _ _ hle
    rw [hz, obj.sequentialResponse_append z hc]

end Object
end ConflictFreedom
