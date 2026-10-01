import CFLeanProof.InfiniteHistory
import CFLeanProof.UniversalEventLinearization

/-! # Linearizability of a whole run, as an infinite event history

`UniversalEventLinearization` proves the manuscript's linearizability for the
literal event history of every finite prefix of a run, and `CausalLinearization`
proves that one growing chain of sequential orders linearizes all prefixes at
once.  This module states and proves the manuscript's definition for the whole
run, as one possibly infinite history:

* `Run.events` is the run's whole invocation/response event sequence, one event
  at most per tick; its finite prefixes are the histories `Run.history`;
* `Run.completed` is its completion `H̄`: invocations the linearization never
  retains are dropped, and each retained invocation the run never answers is
  answered right behind the invocation, since an infinite history has no end to
  append to;
* the legal sequential history is `S_t̂`, the execution of the chain's limit
  order `t̂` (`chainLimit`), a single finite or infinite sequence;
* `H̄|ᵢ = S_t̂|ᵢ` holds for every process as equality of event sequences, and
  the real-time order of the run is preserved in `S_t̂`.

The per-process argument is the manuscript's: each process's operations are
sequential, a returned operation keeps its response, and a pending operation
is the last one of its process.
-/
namespace ConflictFreedom
namespace InvocationLedger
namespace Run

variable {P Op Response : Type} [DecidableEq P]
variable (e : Run P Op) (resp : Command P Op → Response)

/-- **The whole history of the run**: block `t` holds the invocation or
response event of tick `t`, if there is one. -/
def events : InfiniteHistory (Command P Op) Response := fun t => (e.event resp t).toList

/-- Its finite prefixes are the observed histories. -/
theorem events_upto (N : Nat) : (e.events resp).upto N = e.history resp N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [InfiniteHistory.upto_succ, ih, history_succ]; rfl

theorem events_invoked (a : Command P Op) :
    (e.events resp).Invoked a ↔ ∃ N, a ∈ (e.state N).invoked := by
  simp only [InfiniteHistory.Invoked, events_upto, invoked_iff]

theorem events_responded (a : Command P Op) (v : Response) :
    (e.events resp).Responded a v ↔ (∃ N, a ∈ (e.state N).returned) ∧ v = resp a := by
  simp only [InfiniteHistory.Responded, events_upto, responded_iff]
  constructor
  · rintro ⟨N, h, rfl⟩; exact ⟨⟨N, h⟩, rfl⟩
  · rintro ⟨⟨N, h⟩, rfl⟩; exact ⟨N, h, rfl⟩

/-- **The whole history is well formed**: unique instances, sequential per
process. -/
theorem events_wellFormed :
    (e.events resp).WellFormed (Response := Response) Command.process := fun N => by
  rw [events_upto]; exact e.history_wellFormed resp N

/-! ### One process at a time -/

/-- Process `i`'s answered operations by boundary `N`, in order, with their
responses: the completed part of `H|ᵢ` (`project_history`). -/
def answered (i : P) (N : Nat) : List (Command P Op × Response) :=
  (((e.state N).returned.filter (fun c => c.process = i)).reverse).map (fun c => (c, resp c))

theorem answered_step (i : P) (M : Nat) :
    ∃ z, e.answered resp i (M + 1) = e.answered resp i M ++ z := by
  rcases e.next M with h | ⟨p, op, _, h⟩ | ⟨p, cmd, _, h⟩
  · exact ⟨[], by simp [answered, h]⟩
  · exact ⟨[], by simp [answered, h, invoke]⟩
  · by_cases hc : cmd.process = i
    · exact ⟨[(cmd, resp cmd)], by simp [answered, h, finish, hc]⟩
    · exact ⟨[], by simp [answered, h, finish, hc]⟩

/-- While `c` is process `i`'s pending operation, process `i` does nothing
else: until `c` is answered its answered list is frozen, and once `c` is
answered the list has grown by `c` and then whatever follows. -/
theorem active_evolution {i : P} {c : Command P Op} {N : Nat}
    (hc : (e.state N).active i = some c) (d : Nat) :
    (c ∉ (e.state (N + d)).returned ∧ (e.state (N + d)).active i = some c ∧
        e.answered resp i (N + d) = e.answered resp i N) ∨
      (c ∈ (e.state (N + d)).returned ∧
        ∃ rest, e.answered resp i (N + d) = e.answered resp i N ++ (c, resp c) :: rest) := by
  have hci : c.process = i := ((e.valid N).active_tag i c hc).1
  induction d with
  | zero => exact Or.inl ⟨fun hm => (e.valid N).active_pending i c hc c hm rfl, hc, rfl⟩
  | succ d ih =>
    rw [← Nat.add_assoc]
    rcases ih with ⟨hnr, hact, hans⟩ | ⟨hr, rest, hrest⟩
    · rcases e.next (N + d) with h | ⟨p, op, hidle, h⟩ | ⟨p, cmd, hcmd, h⟩
      · refine Or.inl ⟨by rw [h]; exact hnr, by rw [h]; exact hact, ?_⟩
        rw [← hans]; simp [answered, h]
      · have hpi : p ≠ i := by rintro rfl; rw [hact] at hidle; cases hidle
        refine Or.inl ⟨?_, ?_, ?_⟩
        · rw [h]; exact hnr
        · rw [h]; simpa [invoke, update, Ne.symm hpi] using hact
        · rw [← hans]; simp [answered, h, invoke]
      · have hproc : cmd.process = p := ((e.valid (N + d)).active_tag p cmd hcmd).1
        by_cases hpi : p = i
        · subst hpi
          have hcc : cmd = c := Option.some.inj (hcmd.symm.trans hact)
          subst hcc
          refine Or.inr ⟨by rw [h]; exact List.mem_cons_self .., [], ?_⟩
          rw [← hans]; simp [answered, h, finish, hproc]
        · have hne : c ≠ cmd := by
            intro hce; subst hce
            exact hpi (hproc.symm.trans hci)
          refine Or.inl ⟨?_, ?_, ?_⟩
          · rw [h]; simp only [finish, List.mem_cons, not_or]; exact ⟨hne, hnr⟩
          · rw [h]; simpa [finish, update, Ne.symm hpi] using hact
          · rw [← hans]; simp [answered, h, finish, hproc, hpi]
    · obtain ⟨z, hz⟩ := e.answered_step resp i (N + d)
      exact Or.inr ⟨e.returned_step hr, rest ++ z, by rw [hz, hrest]; simp⟩

/-- Filtering the observed history by a predicate that keeps every answered
operation leaves process `i`'s answered operations and, possibly, its pending
invocation. -/
theorem project_filter_history (i : P) (N : Nat) (q : Command P Op → Bool)
    (hq : ∀ c ∈ (e.state N).returned, q c = true) :
    History.project Command.process i ((e.history resp N).filter (fun ev => q ev.op)) =
      History.alternating (e.answered resp i N)
        (match (e.state N).active i with | some c => if q c then some c else none | none => none) := by
  rw [History.project_filter, e.project_history resp i N, History.filter_alternating]
  congr 1
  · refine List.filter_eq_self.mpr ?_
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact hq c (List.mem_filter.mp (List.mem_reverse.mp hc)).1
  · cases (e.state N).active i <;> rfl

/-! ### The completion of the whole run

Relative to a chain `x` of boundary linearizations, an invocation is retained
when some linearization of the chain contains it; a retained invocation the run
never answers receives its response right behind the invocation. -/

section Completion
variable (x : Nat → List (Command P Op))

/-- The linearization eventually retains `a`. -/
noncomputable def kept (a : Command P Op) : Bool :=
  @decide (∃ N, a ∈ x N) (Classical.propDecidable _)

omit [DecidableEq P] in
theorem kept_iff {a : Command P Op} : kept x a = true ↔ ∃ N, a ∈ x N := by
  unfold kept; exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- `a` is retained by the linearization but never answered by the run: the
completion supplies its response. -/
def Supplied (a : Command P Op) : Prop := (∃ N, a ∈ x N) ∧ ∀ N, a ∉ (e.state N).returned

/-- The responses the completion adds to block `t`: one right behind the
invocation of each retained operation the run never answers. -/
noncomputable def supplied (t : Nat) : List (Command P Op × Response) :=
  match e.event resp t with
  | some (.invoke a) => @ite _ (e.Supplied x a) (Classical.propDecidable _) [(a, resp a)] []
  | _ => []

/-- **The completion `H̄` of the whole run.** -/
noncomputable def completed : InfiniteHistory (Command P Op) Response := fun t =>
  (e.events resp t).filter (fun ev => kept x ev.op) ++
    (e.supplied resp x t).map (fun p => Event.respond p.1 p.2)

/-- The response the completion supplies to process `i` by boundary `N`: that
of its pending operation, if the run never answers it. -/
noncomputable def suppliedAt (i : P) (N : Nat) : History (Command P Op) Response :=
  match (e.state N).active i with
  | some c => @ite _ (e.Supplied x c) (Classical.propDecidable _) [Event.respond c (resp c)] []
  | none => []

/-- Process `i`'s part of the completion's first `N` blocks: its retained
events of the observed history, then the supplied response, if any.  A
supplied response is the last event of its process. -/
theorem project_completed_upto (i : P) (N : Nat) :
    History.project Command.process i ((e.completed resp x).upto N) =
      History.project Command.process i ((e.history resp N).filter (fun ev => kept x ev.op)) ++
        e.suppliedAt resp x i N := by
  induction N with
  | zero =>
    simp only [InfiniteHistory.upto_zero, history_zero, List.filter_nil, History.project_nil,
      suppliedAt, e.initial_state]
    rfl
  | succ N ih =>
    rw [InfiniteHistory.upto_succ, History.project_append, ih, history_succ, List.filter_append,
      History.project_append]
    rcases e.next N with h | ⟨p, op, hidle, h⟩ | ⟨p, cmd, hcmd, h⟩
    · have hev := e.event_stutter resp h
      simp [completed, events, supplied, suppliedAt, hev, h]
    · have hev := e.event_invoke resp h
      by_cases hip : i = p
      · subst hip
        have hS : e.suppliedAt resp x i N = [] := by simp [suppliedAt, hidle]
        rw [hS]
        by_cases hs : e.Supplied x ⟨op, i, (e.state N).sequence i + 1⟩
        · simp [completed, events, supplied, suppliedAt, hev, h, invoke, update, hs,
            History.project]
        · simp [completed, events, supplied, suppliedAt, hev, h, invoke, update, hs,
            History.project]
      · have hS : e.suppliedAt resp x i (N + 1) = e.suppliedAt resp x i N := by
          simp [suppliedAt, h, invoke, update, hip]
        rw [hS]
        have hp : ∀ l : History (Command P Op) Response, (∀ ev ∈ l, ev.op.process = p) →
            History.project Command.process i l = [] := by
          intro l hl
          refine List.filter_eq_nil_iff.mpr (fun ev hm hq => hip ?_)
          rw [← hl ev hm]; exact (of_decide_eq_true hq).symm
        have h1 : History.project Command.process i ((e.completed resp x) N) = [] := by
          refine hp _ (fun ev hm => ?_)
          simp only [completed, events, supplied, hev, Option.toList_some, List.mem_append,
            List.mem_filter, List.mem_singleton, List.mem_map] at hm
          rcases hm with ⟨rfl, _⟩ | ⟨q, hq, rfl⟩
          · rfl
          · by_cases hs : e.Supplied x ⟨op, p, (e.state N).sequence p + 1⟩
            · rw [ite_eq_left hs, List.mem_singleton] at hq
              rw [hq]; rfl
            · rw [ite_eq_right hs] at hq
              cases hq
        have h2 : History.project Command.process i
            (((e.event resp N).toList).filter (fun ev => kept x ev.op)) = [] := by
          refine hp _ (fun ev hm => ?_)
          rw [hev] at hm
          simp only [Option.toList_some, List.mem_filter, List.mem_singleton] at hm
          rw [hm.1]; rfl
        rw [h1, h2]; simp
    · have hev := e.event_finish resp h
      have hproc : cmd.process = p := ((e.valid N).active_tag p cmd hcmd).1
      have hns : ¬ e.Supplied x cmd := fun hs =>
        hs.2 (N + 1) (by rw [h]; exact List.mem_cons_self ..)
      by_cases hip : i = p
      · subst hip
        have hS : e.suppliedAt resp x i N = [] := by simp [suppliedAt, hcmd, hns]
        have hS' : e.suppliedAt resp x i (N + 1) = [] := by simp [suppliedAt, h, finish, update]
        rw [hS, hS']
        simp [completed, events, supplied, hev]
      · have hS : e.suppliedAt resp x i (N + 1) = e.suppliedAt resp x i N := by
          simp [suppliedAt, h, finish, update, hip]
        rw [hS]
        have hne : ¬ cmd.process = i := by rw [hproc]; exact fun hx => hip hx.symm
        simp [completed, events, supplied, hev, History.project, hne]

end Completion

/-! ### A coherent chain of boundary linearizations -/

section Chain
variable {State : Type} [DecidableEq Op] (obj : Object State (Command P Op) Response)

/-- What `CausalLinearization` provides, in ledger terms: a chain `x` of finite
linearizations, one per boundary, each a literal prefix of the next, whose
responses are `resp`. -/
structure ChainLinearization (x : Nat → List (Command P Op)) : Prop where
  chain : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z
  nodup : ∀ N, (x N).Nodup
  invoked : ∀ N, ∀ a ∈ x N, a ∈ (e.state N).invoked
  returned : ∀ N, ∀ a ∈ (e.state N).returned, a ∈ x N
  response : ∀ N, ∀ a ∈ x N, obj.sequentialResponse (x N) a = resp a
  process : ∀ N a b, a ∈ x N → b ∈ x N → a.process = b.process →
    a.sequence < b.sequence → (x N).idxOf a < (x N).idxOf b
  realTime : ∀ N k a b, k ≤ N → a ∈ (e.state k).returned → b ∉ (e.state k).invoked →
    a ∈ x N → b ∈ x N → (x N).idxOf a < (x N).idxOf b


namespace ChainLinearization
variable {e resp obj} {x : Nat → List (Command P Op)}

/-- The pending operations a linearization retains, for one process: at most
its active operation. -/
theorem pending_filter (hx : e.ChainLinearization resp obj x) (i : P) (N : Nat) :
    ((e.pendingExtension obj N (x N)).filter (fun p => decide (p.1.process = i))) =
      (match (e.state N).active i with
        | some c => if c ∈ x N then [(c, resp c)] else []
        | none => []) := by
  unfold pendingExtension
  rw [List.filter_map]
  have hnd : ((x N).filter (fun a => decide (a ∉ (e.state N).returned))).Nodup :=
    (hx.nodup N).sublist List.filter_sublist
  have huniq : ∀ a ∈ (x N).filter (fun a => decide (a ∉ (e.state N).returned)),
      ((fun p : Command P Op × Response => decide (p.1.process = i)) ∘
        (fun a => (a, obj.sequentialResponse (x N) a))) a = true →
      (e.state N).active i = some a := by
    intro a ha hq
    obtain ⟨hax, hnr⟩ := List.mem_filter.mp ha
    have hp : a.process = i := of_decide_eq_true hq
    have := e.active_of_pending (hx.invoked N a hax) (of_decide_eq_true hnr)
    rwa [hp] at this
  cases hact : (e.state N).active i with
  | none =>
    rw [List.filter_eq_nil_iff.mpr (fun a ha hq => by rw [huniq a ha hq] at hact; cases hact)]
    rfl
  | some c =>
    by_cases hcx : c ∈ x N
    · have hcr : c ∉ (e.state N).returned := fun hm =>
        (e.valid N).active_pending i c hact c hm rfl
      have hcp : c.process = i := ((e.valid N).active_tag i c hact).1
      rw [filter_eq_singleton hnd (List.mem_filter.mpr ⟨hcx, decide_eq_true hcr⟩)
        (by simp [hcp]) (fun a ha hq => by
          have := huniq a ha hq; rw [hact] at this; exact (Option.some.inj this).symm)]
      simp [hcx, hx.response N c hcx]
    · rw [List.filter_eq_nil_iff.mpr (fun a ha hq => hcx (by
        have := huniq a ha hq; rw [hact] at this
        rw [Option.some.inj this]; exact (List.mem_filter.mp ha).1))]
      simp [hcx]

/-- `S|ᵢ` at boundary `N`, in normal form: process `i`'s answered operations,
then its pending operation with its sequential response if the linearization
retains it.  This is the finite theorem `project_completion`, read backwards. -/
theorem project_sequentialEvents (hx : e.ChainLinearization resp obj x) (i : P) (N : Nat) :
    History.project Command.process i (obj.sequentialEvents (x N)) =
      History.alternating (e.answered resp i N)
          (match (e.state N).active i with
            | some c => if c ∈ x N then some c else none
            | none => none) ++
        (match (e.state N).active i with
          | some c => if c ∈ x N then [Event.respond c (resp c)] else []
          | none => []) := by
  rw [← e.project_completion resp obj i (hx.nodup N) (hx.invoked N)
    (fun a ha => ⟨hx.returned N a ha, hx.response N a (hx.returned N a ha)⟩) (hx.process N)]
  have hf := e.project_filter_history resp i N (fun c => decide (c ∈ x N))
    (fun c hc => decide_eq_true (hx.returned N c hc))
  rw [completion, History.project_append, hf, History.project_map_respond, hx.pending_filter i N]
  cases (e.state N).active i with
  | none => rfl
  | some c => by_cases hcx : c ∈ x N <;> simp [hcx]

/-- The completion's `H̄|ᵢ` at boundary `N`, in normal form. -/
theorem project_completed (hx : e.ChainLinearization resp obj x) (i : P) (N : Nat) :
    History.project Command.process i ((e.completed resp x).upto N) =
      History.alternating (e.answered resp i N)
          (match (e.state N).active i with
            | some c => if kept x c then some c else none
            | none => none) ++
        e.suppliedAt resp x i N := by
  rw [e.project_completed_upto resp x i N, e.project_filter_history resp i N (kept x)
    (fun c hc => (kept_iff x).mpr ⟨N, hx.returned N c hc⟩)]

omit [DecidableEq Op] in
/-- A retained operation the completion does not have to answer is answered
by the run. -/
theorem answered_of_kept {c : Command P Op} (hk : kept x c = true) (hs : ¬ e.Supplied x c) :
    ∃ M, c ∈ (e.state M).returned :=
  Classical.byContradiction fun hno => hs ⟨(kept_iff x).mp hk, fun M hM => hno ⟨M, hM⟩⟩

/-- Every finite part of `H̄|ᵢ` is a prefix of a finite part of `S|ᵢ`. -/
theorem completed_prefix (hx : e.ChainLinearization resp obj x) (i : P) (N : Nat) :
    ∃ M, History.project Command.process i ((e.completed resp x).upto N) <+:
      History.project Command.process i (obj.sequentialEvents (x M)) := by
  rw [hx.project_completed i N]
  cases hact : (e.state N).active i with
  | none =>
    refine ⟨N, ?_⟩
    rw [hx.project_sequentialEvents i N, hact]
    simp [suppliedAt, hact]
  | some c =>
    by_cases hs : e.Supplied x c
    · obtain ⟨⟨N0, hN0⟩, hnever⟩ := id hs
      refine ⟨N + N0, ?_⟩
      rcases e.active_evolution resp hact N0 with ⟨_, hact', hans⟩ | ⟨hr, _⟩
      · have hcx : c ∈ x (N + N0) := Object.chain_mem_mono hx.chain (by omega) hN0
        have hk : kept x c = true := (kept_iff x).mpr ⟨N0, hN0⟩
        rw [hx.project_sequentialEvents i (N + N0), hact', hans]
        simp only [suppliedAt, hact, ite_eq_left hs, hk, hcx, ite_true]
        exact List.prefix_refl _
      · exact absurd hr (hnever _)
    · by_cases hk : kept x c = true
      · obtain ⟨M1, hM1⟩ := answered_of_kept hk hs
        refine ⟨N + M1, ?_⟩
        rcases e.active_evolution resp hact M1 with ⟨hnr, _⟩ | ⟨_, rest, hrest⟩
        · exact absurd (e.returned_mono (by omega) hM1) hnr
        · rw [hx.project_sequentialEvents i (N + M1), hrest]
          simp only [suppliedAt, hact, ite_eq_right hs, hk, ite_true, List.append_nil]
          exact (History.alternating_some_prefix _ rest c (resp c) _).trans
            (List.prefix_append _ _)
      · refine ⟨N, ?_⟩
        rw [hx.project_sequentialEvents i N, hact]
        simp only [suppliedAt, hact, ite_eq_right hs, hk, Bool.false_eq_true, ite_false,
          List.append_nil]
        exact (History.alternating_none_prefix _ _).trans (List.prefix_append _ _)

/-- Every finite part of `S|ᵢ` is a prefix of a finite part of `H̄|ᵢ`. -/
theorem sequentialEvents_prefix (hx : e.ChainLinearization resp obj x) (i : P) (N : Nat) :
    ∃ M, History.project Command.process i (obj.sequentialEvents (x N)) <+:
      History.project Command.process i ((e.completed resp x).upto M) := by
  rw [hx.project_sequentialEvents i N]
  cases hact : (e.state N).active i with
  | none =>
    refine ⟨N, ?_⟩
    rw [hx.project_completed i N, hact]
    simp [suppliedAt, hact]
  | some c =>
    by_cases hcx : c ∈ x N
    · have hk : kept x c = true := (kept_iff x).mpr ⟨N, hcx⟩
      by_cases hs : e.Supplied x c
      · refine ⟨N, ?_⟩
        rw [hx.project_completed i N, hact]
        simp only [suppliedAt, hact, ite_eq_left hs, hk, hcx, ite_true]
        exact List.prefix_refl _
      · obtain ⟨M1, hM1⟩ := answered_of_kept hk hs
        refine ⟨N + M1, ?_⟩
        rcases e.active_evolution resp hact M1 with ⟨hnr, _⟩ | ⟨_, rest, hrest⟩
        · exact absurd (e.returned_mono (by omega) hM1) hnr
        · rw [hx.project_completed i (N + M1), hrest]
          simp only [hcx, ite_true]
          rw [History.alternating_some_append_respond,
            show e.answered resp i N ++ (c, resp c) :: rest =
              (e.answered resp i N ++ [(c, resp c)]) ++ rest by simp]
          exact (History.alternating_none_prefix_append _ rest _).trans (List.prefix_append _ _)
    · refine ⟨N, ?_⟩
      rw [hx.project_completed i N, hact]
      simp only [hcx, ite_false, List.append_nil]
      exact (History.alternating_none_prefix _ _).trans (List.prefix_append _ _)

/-- **`H̄|ᵢ = S|ᵢ` for every process**, as sequences of events. -/
theorem sameEvents (hx : e.ChainLinearization resp obj x) (i : P) :
    ((e.completed resp x).project Command.process i).SameEvents
      ((obj.sequentialStream (chainLimit x)).project Command.process i) := by
  refine ⟨fun N => ?_, fun M => ?_⟩
  · obtain ⟨N', h⟩ := hx.completed_prefix i N
    refine ⟨(x N').length, ?_⟩
    rw [InfiniteHistory.upto_project, InfiniteHistory.upto_project, Object.sequentialStream_upto,
      chainLimit_range hx.chain]
    exact h
  · obtain ⟨N0, hN0⟩ := chainLimit_cofinal hx.chain M
    obtain ⟨N', h⟩ := hx.sequentialEvents_prefix i N0
    refine ⟨N', ?_⟩
    rw [InfiniteHistory.upto_project, InfiniteHistory.upto_project, Object.sequentialStream_upto]
    exact ((obj.sequentialEvents_prefix hN0).filter _).trans h

/-- **`H̄` is a completion of the run's whole history.** -/
theorem isCompletion (hx : e.ChainLinearization resp obj x) :
    (e.events resp).IsCompletion (e.completed resp x) := by
  refine ⟨kept x, e.supplied resp x, fun t => rfl, ?_, ?_⟩
  · intro a ha hk
    refine ⟨ha, ?_⟩
    rintro ⟨v, hv⟩
    obtain ⟨⟨N, hN⟩, _⟩ := (e.events_responded resp a v).mp hv
    have := (kept_iff x).mpr ⟨N, hx.returned N a hN⟩
    rw [hk] at this; cases this
  · intro t p hp
    unfold supplied at hp
    split at hp
    · rename_i a hev
      by_cases hs : e.Supplied x a
      · rw [ite_eq_left hs, List.mem_singleton] at hp
        subst hp
        have hinv : (e.history resp (t + 1)).Invoked a := by
          rw [history_succ, hev]; simp [History.Invoked]
        refine ⟨⟨⟨t + 1, by rw [events_upto]; exact hinv⟩, ?_⟩, (kept_iff x).mpr hs.1,
          by rw [events_upto]; exact hinv⟩
        rintro ⟨v, hv⟩
        obtain ⟨⟨N, hN⟩, _⟩ := (e.events_responded resp a v).mp hv
        exact hs.2 N hN
      · rw [ite_eq_right hs] at hp; cases hp
    · cases hp

omit [DecidableEq Op] in
/-- An invocation the completion keeps is retained by the linearization. -/
theorem kept_of_completed {b : Command P Op} (hb : (e.completed resp x).Invoked b) :
    ∃ N, b ∈ x N := by
  obtain ⟨N, hN⟩ := hb
  obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hN
  simp only [completed, List.mem_append, List.mem_filter, List.mem_map] at ht
  rcases ht with ⟨_, hk⟩ | ⟨q, _, hq⟩
  · exact (kept_iff x).mp hk
  · cases hq

/-- **The manuscript's linearizability of the whole run.**  A coherent chain of
boundary linearizations makes the run's whole, possibly infinite, event history
linearizable: `H̄ = completed`, `S = S_t̂` for the chain's limit `t̂`. -/
theorem infEventLinearizable (hx : e.ChainLinearization resp obj x) :
    obj.InfEventLinearizable Command.process (e.events resp) := by
  refine ⟨e.completed resp x, chainLimit x, hx.isCompletion, fun i => hx.sameEvents i, ?_⟩
  intro a b hab hb
  obtain ⟨N, hN⟩ := hab
  rw [e.events_upto] at hN
  obtain ⟨k, hk, ha, hbk⟩ := e.precedes_boundary resp hN
  obtain ⟨N0, hN0⟩ := kept_of_completed hb
  have haM : a ∈ x (N0 + k) := hx.returned _ a (e.returned_mono (by omega) ha)
  have hbM : b ∈ x (N0 + k) := Object.chain_mem_mono hx.chain (by omega) hN0
  refine ⟨(x (N0 + k)).length, ?_⟩
  rw [Object.sequentialStream_upto, chainLimit_range hx.chain]
  exact obj.sequentialEvents_precedes (hx.nodup _) haM hbM
    (hx.realTime (N0 + k) k a b (by omega) ha hbk haM hbM)

end ChainLinearization

end Chain

end Run
end InvocationLedger
namespace WeakUniversal
open WeakUniversal (Cmd Tagged Return Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- A chain of boundary linearizations of an Algorithm 1 run, in ledger terms;
its responses are those of the chain's limit order. -/
theorem Execution.chainLinearization {H : Environment (n := n) obj} (run : Execution obj H)
    {x : Nat → List (Cmd n Op)} (hx : ∀ N, (Tagged obj).Linearizes (run.history obj) N (x N))
    (hchain : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :
    (run.ledgerRun obj).ChainLinearization ((Tagged obj).chainResponse x) (Tagged obj) x where
  chain := hchain
  nodup N := (hx N).unique
  invoked N a ha := (hx N).invoked a ha
  returned N a ha := by
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp ha
    obtain ⟨v, hv⟩ := response_defined obj (run.reachable obj N) hr
    exact ((hx N).completed a v ⟨ret, hr, hc, by rw [← hc]; exact hv⟩).1
  response N a ha := (Tagged obj).sequentialResponse_chain hchain ha
  process N a b ha hb hp hs := run.linearization_process_order obj (hx N) ha hb hp hs
  realTime N k a b hk ha hb haN hbN := by
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp ha
    obtain ⟨v, hv⟩ := response_defined obj (run.reachable obj k) hr
    exact (hx N).realTime a b haN hbN ⟨k, hk, ⟨v, ret, hr, hc, by rw [← hc]; exact hv⟩, hb⟩

/-- **The manuscript's linearizability for Algorithm 1, for the whole run.**
The run's whole, possibly infinite, invocation/response event history has a
completion `H̄` and a legal sequential history `S` with `H̄|ᵢ = S|ᵢ` for every
process `i`, as sequences of events, and the real-time order of the run is
preserved in `S`.  The response assignment is the run's own: it agrees with
every value the run returns. -/
theorem Execution.infinite_event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hcausal : run.ReturnsInvokedBy obj) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).InfEventLinearizable Command.process ((run.ledgerRun obj).events resp) := by
  obtain ⟨x, hx, hchain⟩ := run.chain_linearization obj coverage spec hcausal
  refine ⟨(Tagged obj).chainResponse x, fun k a v h => ?_,
    (run.chainLinearization obj hx hchain).infEventLinearizable⟩
  obtain ⟨ha, hv⟩ := (hx k).completed a v h
  rw [← hv, (Tagged obj).sequentialResponse_chain hchain ha]

end WeakUniversal

namespace HelpingUniversal
open WeakUniversal (Cmd Tagged Return Environment)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- A chain of boundary linearizations of an Algorithm 3 run, in ledger terms. -/
theorem Execution.chainLinearization {H : Environment (n := n) obj} (run : Execution obj H)
    {x : Nat → List (Cmd n Op)} (hx : ∀ N, (Tagged obj).Linearizes (run.history obj) N (x N))
    (hchain : ∀ k m, k ≤ m → ∃ z, x m = x k ++ z) :
    (run.ledgerRun obj).ChainLinearization ((Tagged obj).chainResponse x) (Tagged obj) x where
  chain := hchain
  nodup N := (hx N).unique
  invoked N a ha := (hx N).invoked a ha
  returned N a ha := by
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp ha
    obtain ⟨v, hv⟩ := response_defined obj (run.reachable obj N) hr
    exact ((hx N).completed a v ⟨ret, hr, hc, by rw [← hc]; exact hv⟩).1
  response N a ha := (Tagged obj).sequentialResponse_chain hchain ha
  process N a b ha hb hp hs := run.linearization_process_order obj (hx N) ha hb hp hs
  realTime N k a b hk ha hb haN hbN := by
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp ha
    obtain ⟨v, hv⟩ := response_defined obj (run.reachable obj k) hr
    exact (hx N).realTime a b haN hbN ⟨k, hk, ⟨v, ret, hr, hc, by rw [← hc]; exact hv⟩, hb⟩

/-- **The manuscript's linearizability for Algorithm 3, for the whole run.** -/
theorem Execution.infinite_event_linearization {H : Environment (n := n) obj}
    (run : Execution obj H) (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) (hcausal : run.ReturnsInvokedBy obj) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (run.history obj).returned k a v → v = resp a) ∧
      (Tagged obj).InfEventLinearizable Command.process ((run.ledgerRun obj).events resp) := by
  obtain ⟨x, hx, hchain⟩ := run.chain_linearization obj coverage spec hcausal
  refine ⟨(Tagged obj).chainResponse x, fun k a v h => ?_,
    (run.chainLinearization obj hx hchain).infEventLinearizable⟩
  obtain ⟨ha, hv⟩ := (hx k).completed a v h
  rw [← hv, (Tagged obj).sequentialResponse_chain hchain ha]

end HelpingUniversal

namespace GlobalSchedule
open WeakUniversal (Cmd Tagged)
variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {f : UniversalProtocol.Family (n := n) obj}

/-- **Algorithm 1 is linearizable, as the manuscript defines it, on its whole
run**, with no hypothesis beyond the operational scheduling rules and no
liveness assumption.  The run's whole, possibly infinite, sequence of
invocation and response events (1) records exactly the operations the run
invokes, (2) records exactly the responses it returns, with their values,
(3) is well formed, and (4) has a completion `H̄` and a legal sequential
history `S` with `H̄|ᵢ = S|ᵢ` for every process `i` and `≼_H ⊆ ≼_S`. -/
theorem Weak.infinite_event_linearization (g : Weak obj f) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (g.run.history obj).returned k a v → v = resp a) ∧
      (∀ a, ((g.run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, (g.run.history obj).invoked N a) ∧
      (∀ a v, ((g.run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, (g.run.history obj).returned N a v) ∧
      ((g.run.ledgerRun obj).events resp).WellFormed Command.process ∧
      (Tagged obj).InfEventLinearizable Command.process ((g.run.ledgerRun obj).events resp) := by
  obtain ⟨x, hx, hchain⟩ := g.chain_linearization
  have hagree : ∀ k a v, (g.run.history obj).returned k a v →
      v = (Tagged obj).chainResponse x a := by
    intro k a v h
    obtain ⟨ha, hv⟩ := (hx k).completed a v h
    rw [← hv, (Tagged obj).sequentialResponse_chain hchain ha]
  refine ⟨(Tagged obj).chainResponse x, hagree,
    fun a => (g.run.ledgerRun obj).events_invoked _ a, fun a v => ?_,
    (g.run.ledgerRun obj).events_wellFormed _,
    (g.run.chainLinearization obj hx hchain).infEventLinearizable⟩
  rw [(g.run.ledgerRun obj).events_responded]
  constructor
  · rintro ⟨⟨N, hN⟩, rfl⟩
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp hN
    obtain ⟨w, hw⟩ := WeakUniversal.response_defined obj (g.run.reachable obj N) hr
    have hret : (g.run.history obj).returned N a w := ⟨ret, hr, hc, by rw [← hc]; exact hw⟩
    rw [← hagree N a w hret]
    exact ⟨N, hret⟩
  · rintro ⟨N, hN⟩
    obtain ⟨ret, hr, hc, _⟩ := id hN
    exact ⟨⟨N, List.mem_map.mpr ⟨ret, hr, hc⟩⟩, hagree N a v hN⟩

/-- **Algorithm 3 is linearizable, as the manuscript defines it, on its whole
run.** -/
theorem Helping.infinite_event_linearization (g : Helping obj f) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (g.run.history obj).returned k a v → v = resp a) ∧
      (∀ a, ((g.run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, (g.run.history obj).invoked N a) ∧
      (∀ a v, ((g.run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, (g.run.history obj).returned N a v) ∧
      ((g.run.ledgerRun obj).events resp).WellFormed Command.process ∧
      (Tagged obj).InfEventLinearizable Command.process ((g.run.ledgerRun obj).events resp) := by
  obtain ⟨x, hx, hchain⟩ := g.chain_linearization
  have hagree : ∀ k a v, (g.run.history obj).returned k a v →
      v = (Tagged obj).chainResponse x a := by
    intro k a v h
    obtain ⟨ha, hv⟩ := (hx k).completed a v h
    rw [← hv, (Tagged obj).sequentialResponse_chain hchain ha]
  refine ⟨(Tagged obj).chainResponse x, hagree,
    fun a => (g.run.ledgerRun obj).events_invoked _ a, fun a v => ?_,
    (g.run.ledgerRun obj).events_wellFormed _,
    (g.run.chainLinearization obj hx hchain).infEventLinearizable⟩
  rw [(g.run.ledgerRun obj).events_responded]
  constructor
  · rintro ⟨⟨N, hN⟩, rfl⟩
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp hN
    obtain ⟨w, hw⟩ := HelpingUniversal.response_defined obj (g.run.reachable obj N) hr
    have hret : (g.run.history obj).returned N a w := ⟨ret, hr, hc, by rw [← hc]; exact hw⟩
    rw [← hagree N a w hret]
    exact ⟨N, hret⟩
  · rintro ⟨N, hN⟩
    obtain ⟨ret, hr, hc, _⟩ := id hN
    exact ⟨⟨N, List.mem_map.mpr ⟨ret, hr, hc⟩⟩, hagree N a v hN⟩

/-- **Algorithm 1 over any GCA objects meeting the safety part of the interface is
linearizable, as the manuscript defines it, on its whole run**: only the six
properties of every round and Validity on every prefix are used. -/
theorem WeakRun.infinite_event_linearization {H : WeakUniversal.Environment (n := n) obj}
    (g : WeakRun obj H) (hspec : ∀ r, (H (r + 1)).Specification)
    (hcausal : g.run.CausalGCA obj) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (g.run.history obj).returned k a v → v = resp a) ∧
      (∀ a, ((g.run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, (g.run.history obj).invoked N a) ∧
      (∀ a v, ((g.run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, (g.run.history obj).returned N a v) ∧
      ((g.run.ledgerRun obj).events resp).WellFormed Command.process ∧
      (Tagged obj).InfEventLinearizable Command.process ((g.run.ledgerRun obj).events resp) := by
  obtain ⟨x, hx, hchain⟩ := g.run.causal_chain_linearization obj g.callsCovered hspec hcausal
  have hagree : ∀ k a v, (g.run.history obj).returned k a v →
      v = (Tagged obj).chainResponse x a := by
    intro k a v h
    obtain ⟨ha, hv⟩ := (hx k).completed a v h
    rw [← hv, (Tagged obj).sequentialResponse_chain hchain ha]
  refine ⟨(Tagged obj).chainResponse x, hagree,
    fun a => (g.run.ledgerRun obj).events_invoked _ a, fun a v => ?_,
    (g.run.ledgerRun obj).events_wellFormed _,
    (g.run.chainLinearization obj hx hchain).infEventLinearizable⟩
  rw [(g.run.ledgerRun obj).events_responded]
  constructor
  · rintro ⟨⟨N, hN⟩, rfl⟩
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp hN
    obtain ⟨w, hw⟩ := WeakUniversal.response_defined obj (g.run.reachable obj N) hr
    have hret : (g.run.history obj).returned N a w := ⟨ret, hr, hc, by rw [← hc]; exact hw⟩
    rw [← hagree N a w hret]
    exact ⟨N, hret⟩
  · rintro ⟨N, hN⟩
    obtain ⟨ret, hr, hc, _⟩ := id hN
    exact ⟨⟨N, List.mem_map.mpr ⟨ret, hr, hc⟩⟩, hagree N a v hN⟩

/-- **Algorithm 1 over any GCA meeting the interface is linearizable on its whole
run.** -/
theorem WeakGCA.infinite_event_linearization {H : WeakUniversal.Environment (n := n) obj}
    (g : WeakGCA obj H) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (g.run.history obj).returned k a v → v = resp a) ∧
      (∀ a, ((g.run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, (g.run.history obj).invoked N a) ∧
      (∀ a v, ((g.run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, (g.run.history obj).returned N a v) ∧
      ((g.run.ledgerRun obj).events resp).WellFormed Command.process ∧
      (Tagged obj).InfEventLinearizable Command.process ((g.run.ledgerRun obj).events resp) :=
  g.toWeakRun.infinite_event_linearization g.gca.spec g.gca.causal

/-- **Algorithm 3 over any GCA objects meeting the safety part of the interface is
linearizable, as the manuscript defines it, on its whole run**: only the six
properties of every round and Validity on every prefix are used. -/
theorem HelpingRun.infinite_event_linearization {H : WeakUniversal.Environment (n := n) obj}
    (g : HelpingRun obj H) (hspec : ∀ r, (H (r + 1)).Specification)
    (hcausal : g.run.CausalGCA obj) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (g.run.history obj).returned k a v → v = resp a) ∧
      (∀ a, ((g.run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, (g.run.history obj).invoked N a) ∧
      (∀ a v, ((g.run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, (g.run.history obj).returned N a v) ∧
      ((g.run.ledgerRun obj).events resp).WellFormed Command.process ∧
      (Tagged obj).InfEventLinearizable Command.process ((g.run.ledgerRun obj).events resp) := by
  obtain ⟨x, hx, hchain⟩ := g.run.causal_chain_linearization obj g.callsCovered hspec hcausal
  have hagree : ∀ k a v, (g.run.history obj).returned k a v →
      v = (Tagged obj).chainResponse x a := by
    intro k a v h
    obtain ⟨ha, hv⟩ := (hx k).completed a v h
    rw [← hv, (Tagged obj).sequentialResponse_chain hchain ha]
  refine ⟨(Tagged obj).chainResponse x, hagree,
    fun a => (g.run.ledgerRun obj).events_invoked _ a, fun a v => ?_,
    (g.run.ledgerRun obj).events_wellFormed _,
    (g.run.chainLinearization obj hx hchain).infEventLinearizable⟩
  rw [(g.run.ledgerRun obj).events_responded]
  constructor
  · rintro ⟨⟨N, hN⟩, rfl⟩
    obtain ⟨ret, hr, hc⟩ := List.mem_map.mp hN
    obtain ⟨w, hw⟩ := HelpingUniversal.response_defined obj (g.run.reachable obj N) hr
    have hret : (g.run.history obj).returned N a w := ⟨ret, hr, hc, by rw [← hc]; exact hw⟩
    rw [← hagree N a w hret]
    exact ⟨N, hret⟩
  · rintro ⟨N, hN⟩
    obtain ⟨ret, hr, hc, _⟩ := id hN
    exact ⟨⟨N, List.mem_map.mpr ⟨ret, hr, hc⟩⟩, hagree N a v hN⟩

/-- **Algorithm 3 over any GCA meeting the interface is linearizable on its whole
run.** -/
theorem HelpingGCA.infinite_event_linearization {H : WeakUniversal.Environment (n := n) obj}
    (g : HelpingGCA obj H) :
    ∃ resp : Cmd n Op → Response,
      (∀ k a v, (g.run.history obj).returned k a v → v = resp a) ∧
      (∀ a, ((g.run.ledgerRun obj).events resp).Invoked a ↔
          ∃ N, (g.run.history obj).invoked N a) ∧
      (∀ a v, ((g.run.ledgerRun obj).events resp).Responded a v ↔
          ∃ N, (g.run.history obj).returned N a v) ∧
      ((g.run.ledgerRun obj).events resp).WellFormed Command.process ∧
      (Tagged obj).InfEventLinearizable Command.process ((g.run.ledgerRun obj).events resp) :=
  g.toHelpingRun.infinite_event_linearization g.gca.spec g.gca.causal

end GlobalSchedule
end ConflictFreedom
