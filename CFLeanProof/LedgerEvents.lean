import CFLeanProof.EventHistory
import CFLeanProof.SharedScheduler

/-! # The literal event sequence of a run

`InvocationLedger.Run.next` already says that each tick either does nothing,
invokes one operation, or answers one: a run *is* a sequence of invocation and
response events.  This module reads that sequence off the ledger states,
proves it is a well-formed history in the manuscript's sense, and proves that
the boundary observation used by `FiniteLinearization` is exactly the
observation of this event sequence — including for the real-time order.
-/
namespace ConflictFreedom
namespace InvocationLedger
namespace Run

variable {P Op Response : Type} [DecidableEq P]
variable (e : Run P Op) (resp : Command P Op → Response)

/-- The event of tick `t`, read off two consecutive ledger states.  An
invocation conses onto `invoked`, a response conses onto `returned`, and an
idle tick changes neither. -/
def event (t : Nat) : Option (Event (Command P Op) Response) :=
  if ((e.state t).invoked).length < ((e.state (t + 1)).invoked).length then
    ((e.state (t + 1)).invoked).head?.map Event.invoke
  else if ((e.state t).returned).length < ((e.state (t + 1)).returned).length then
    ((e.state (t + 1)).returned).head?.map (fun c => Event.respond c (resp c))
  else
    none

/-- The literal history observed up to boundary `N`. -/
def history (N : Nat) : History (Command P Op) Response :=
  (List.range N).filterMap (e.event resp)

@[simp] theorem history_zero : e.history resp 0 = [] := rfl

theorem history_succ (N : Nat) :
    e.history resp (N + 1) = e.history resp N ++ (e.event resp N).toList := by
  unfold history
  rw [List.range_succ, List.filterMap_append]
  cases h : e.event resp N <;> simp [h]

theorem event_stutter {t : Nat} (h : e.state (t + 1) = e.state t) :
    e.event resp t = none := by
  simp [event, h]

theorem event_invoke {t : Nat} {p : P} {op : Op}
    (h : e.state (t + 1) = invoke (e.state t) p op) :
    e.event resp t =
      some (Event.invoke ⟨op, p, (e.state t).sequence p + 1⟩) := by
  simp [event, h, invoke]

theorem event_finish {t : Nat} {p : P} {cmd : Command P Op}
    (h : e.state (t + 1) = finish (e.state t) p cmd) :
    e.event resp t = some (Event.respond cmd (resp cmd)) := by
  simp [event, h, finish]

/-- The invocation events of the prefix are the ledger's invocations, in
chronological order. -/
theorem history_invocations (N : Nat) :
    History.invocations (e.history resp N) = ((e.state N).invoked).reverse := by
  induction N with
  | zero => rw [history_zero, e.initial_state]; rfl
  | succ N ih =>
    rw [history_succ, History.invocations_append, ih]
    rcases e.next N with h | ⟨p, op, _, h⟩ | ⟨p, cmd, _, h⟩
    · rw [e.event_stutter resp h, h]; simp
    · rw [e.event_invoke resp h, h]; simp [invoke, History.invocations]
    · rw [e.event_finish resp h, h]; simp [finish, History.invocations]

/-- The response events of the prefix are the ledger's responses, in
chronological order, each carrying its recorded value. -/
theorem history_responses (N : Nat) :
    History.responses (e.history resp N) =
      (((e.state N).returned).map (fun c => (c, resp c))).reverse := by
  induction N with
  | zero => rw [history_zero, e.initial_state]; rfl
  | succ N ih =>
    rw [history_succ, History.responses_append, ih]
    rcases e.next N with h | ⟨p, op, _, h⟩ | ⟨p, cmd, _, h⟩
    · rw [e.event_stutter resp h, h]; simp
    · rw [e.event_invoke resp h, h]; simp [invoke, History.responses]
    · rw [e.event_finish resp h, h]; simp [finish, History.responses]

/-- The observed history depends on the response assignment only through the
commands the run has actually answered.  An assignment is therefore not extra
data: it is the run's own response function, extended arbitrarily. -/
theorem history_congr {resp resp' : Command P Op → Response} {N : Nat}
    (hag : ∀ a ∈ (e.state N).returned, resp a = resp' a) :
    e.history resp N = e.history resp' N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hprev : ∀ a ∈ (e.state N).returned, resp a = resp' a :=
      fun a ha => hag a (e.returned_step ha)
    rw [history_succ, history_succ, ih hprev]
    refine congrArg (e.history resp' N ++ ·) (congrArg Option.toList ?_)
    rcases e.next N with h | ⟨p, op, _, h⟩ | ⟨p, cmd, _, h⟩
    · rw [e.event_stutter resp h, e.event_stutter resp' h]
    · rw [e.event_invoke resp h, e.event_invoke resp' h]
    · rw [e.event_finish resp h, e.event_finish resp' h,
        hag cmd (by rw [h]; exact List.mem_cons_self ..)]

/-- Invocation events and ledger invocations agree. -/
theorem invoked_iff (N : Nat) (a : Command P Op) :
    History.Invoked (e.history resp N) a ↔ a ∈ (e.state N).invoked := by
  rw [History.Invoked, ← History.mem_invocations, history_invocations, List.mem_reverse]

/-- Response events and ledger responses agree, with the recorded value. -/
theorem responded_iff (N : Nat) (a : Command P Op) (v : Response) :
    History.Responded (e.history resp N) a v ↔
      (a ∈ (e.state N).returned ∧ v = resp a) := by
  rw [History.Responded, ← History.mem_responses, history_responses, List.mem_reverse]
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := List.mem_map.mp h
    have h1 : c = a := congrArg Prod.fst he
    have h2 : resp c = v := congrArg Prod.snd he
    exact ⟨h1 ▸ hc, (h1 ▸ h2).symm⟩
  · intro ⟨h1, h2⟩
    exact List.mem_map.mpr ⟨a, h1, by rw [h2]⟩

/-- **Per-process well-formedness, proved.**  Process `i`'s events are its
returned commands in chronological order, each with its recorded value,
followed by its pending invocation if it has one.  This is exactly the
manuscript's "sequential per process". -/
theorem project_history (i : P) (N : Nat) :
    History.project Command.process i (e.history resp N) =
      History.alternating
        ((((e.state N).returned.filter (fun c => c.process = i)).reverse).map
          (fun c => (c, resp c)))
        ((e.state N).active i) := by
  induction N with
  | zero =>
    rw [history_zero, e.initial_state]
    simp [initial, History.alternating]
  | succ N ih =>
    rw [history_succ, History.project_append, ih]
    rcases e.next N with h | ⟨p, op, hidle, h⟩ | ⟨p, cmd, hc, h⟩
    · rw [e.event_stutter resp h, h]; simp
    · rw [e.event_invoke resp h, h]
      simp only [Option.toList_some]
      by_cases hip : i = p
      · subst i
        rw [History.project_cons_pos (by simp), History.project_nil, hidle,
          History.alternating_none_append_invoke]
        simp [invoke, update]
      · have hne : ¬ (⟨op, p, (e.state N).sequence p + 1⟩ :
            Command P Op).process = i := fun hx => hip hx.symm
        rw [History.project_cons_neg hne, History.project_nil]
        simp [invoke, update, hip]
    · have hproc : cmd.process = p := ((e.valid N).active_tag p cmd hc).1
      rw [e.event_finish resp h, h]
      simp only [Option.toList_some]
      by_cases hip : i = p
      · subst i
        rw [History.project_cons_pos (by simpa using hproc), History.project_nil, hc,
          History.alternating_some_append_respond]
        simp [finish, update, hproc]
      · have hne : ¬ cmd.process = i := by rw [hproc]; exact fun hx => hip hx.symm
        rw [History.project_cons_neg hne, History.project_nil]
        simp [finish, update, hne, hip]

/-- A process's pending command is later than every command it has returned. -/
theorem active_sequence_gt {N : Nat} {i : P} {c : Command P Op}
    (hc : (e.state N).active i = some c) {d : Command P Op}
    (hd : d ∈ (e.state N).returned) (hdp : d.process = i) :
    d.sequence < c.sequence := by
  obtain ⟨hcp, hcseq, _⟩ := (e.valid N).active_tag i c hc
  have hb := (e.valid N).invoked_bound d ((e.valid N).returned_invoked d hd)
  rw [hdp] at hb
  rcases Nat.lt_or_ge d.sequence c.sequence with h | h
  · exact h
  · exact absurd (show d.key = c.key from by
      unfold Command.key
      rw [hdp, hcp, show d.sequence = c.sequence from by omega])
      ((e.valid N).active_pending i c hc d hd)

/-- A process returns its commands in increasing sequence order, so the
chronological order of its responses is its invocation order. -/
theorem returned_pairwise (i : P) (N : Nat) :
    (((e.state N).returned.filter (fun c => c.process = i)).reverse).Pairwise
      (fun a b => a.sequence < b.sequence) := by
  induction N with
  | zero => rw [e.initial_state]; simp [initial]
  | succ N ih =>
    rcases e.next N with h | ⟨p, op, _, h⟩ | ⟨p, cmd, hc, h⟩
    · rw [h]; exact ih
    · rw [h]; exact ih
    · have hproc : cmd.process = p := ((e.valid N).active_tag p cmd hc).1
      rw [h, show (finish (e.state N) p cmd).returned = cmd :: (e.state N).returned from rfl]
      by_cases hip : i = p
      · subst i
        rw [List.filter_cons_of_pos (by simpa using hproc), List.reverse_cons]
        refine List.pairwise_append.mpr ⟨ih, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst b
        obtain ⟨har, hap⟩ := List.mem_filter.mp (List.mem_reverse.mp ha)
        exact e.active_sequence_gt hc har (of_decide_eq_true hap)
      · rw [List.filter_cons_of_neg (by simp [hproc]; exact fun hx => hip hx.symm)]
        exact ih

/-- The ledger's invocation list has no repeated command. -/
theorem invoked_nodup (N : Nat) : ((e.state N).invoked).Nodup :=
  (List.pairwise_map.mp (e.valid N).invoked_unique).imp
    (fun h he => h (congrArg Command.key he))

/-- **The event sequence of a run is a well-formed history** in the
manuscript's sense: every operation instance is invoked at most once, and
each process's projection is sequential. -/
theorem history_wellFormed (N : Nat) :
    History.WellFormed (Response := Response) Command.process (e.history resp N) where
  unique := by
    rw [history_invocations]
    exact List.pairwise_reverse.mpr ((e.invoked_nodup N).imp (fun h => Ne.symm h))
  sequential := fun i => ⟨_, _, e.project_history resp i N⟩

/-- The history grows by appending: boundary `k` is a literal prefix of any
later boundary. -/
theorem history_mono (k d : Nat) :
    ∃ z, e.history resp (k + d) = e.history resp k ++ z := by
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨z, hz⟩ := ih
    exact ⟨z ++ (e.event resp (k + d)).toList, by
      rw [show k + (d + 1) = (k + d) + 1 from rfl, history_succ, hz, List.append_assoc]⟩

/-- Conversely, every prefix of an observed history is itself an observed
history: list positions are boundaries. -/
theorem history_prefix {N : Nat} {l : History (Command P Op) Response}
    (hl : l <+: e.history resp N) : ∃ k, k ≤ N ∧ e.history resp k = l := by
  induction N with
  | zero =>
    obtain ⟨t, ht⟩ := hl
    rw [history_zero] at ht
    exact ⟨0, Nat.le_refl 0, by rw [history_zero, (List.append_eq_nil_iff.mp ht).1]⟩
  | succ N ih =>
    rw [history_succ] at hl
    cases hev : e.event resp N with
    | none =>
      rw [hev] at hl
      simp only [Option.toList_none, List.append_nil] at hl
      obtain ⟨k, hk, he⟩ := ih hl
      exact ⟨k, by omega, he⟩
    | some x =>
      rw [hev] at hl
      simp only [Option.toList_some] at hl
      rcases List.prefix_concat_iff.mp hl with heq | hpre
      · exact ⟨N + 1, Nat.le_refl _, by rw [history_succ, hev, Option.toList_some, heq]⟩
      · obtain ⟨k, hk, he⟩ := ih hpre
        exact ⟨k, by omega, he⟩

/-- **Event-order real-time precedence implies boundary precedence.**  If
`a`'s response event precedes `b`'s invocation event, then some boundary sees
`a` returned and `b` not yet invoked. -/
theorem precedes_boundary {N : Nat} {a b : Command P Op}
    (h : History.Precedes (e.history resp N) a b) :
    ∃ k, k ≤ N ∧ a ∈ (e.state k).returned ∧ b ∉ (e.state k).invoked := by
  obtain ⟨l, r, hsplit, ⟨v, hv⟩, hb⟩ := h
  obtain ⟨k, hk, hlk⟩ := e.history_prefix resp ⟨r, hsplit.symm⟩
  subst l
  refine ⟨k, hk, ((e.responded_iff resp k a v).mp hv).1, ?_⟩
  intro hbk
  have h1 : Event.invoke b ∈ e.history resp k := (e.invoked_iff resp k b).mpr hbk
  have hnodup : (History.invocations (e.history resp N)).Nodup :=
    (e.history_wellFormed resp N).unique
  rw [hsplit, History.invocations_append] at hnodup
  obtain ⟨_, _, hdisj⟩ := List.pairwise_append.mp hnodup
  exact hdisj b (History.mem_invocations.mpr h1) b (History.mem_invocations.mpr hb) rfl

/-- **Boundary precedence implies event-order precedence**, for operations the
history records.  With `precedes_boundary`, the two real-time orders agree. -/
theorem precedes_of_boundary {N k : Nat} (hk : k ≤ N) {a b : Command P Op}
    (ha : a ∈ (e.state k).returned) (hb : b ∉ (e.state k).invoked)
    (hbN : b ∈ (e.state N).invoked) :
    History.Precedes (e.history resp N) a b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨z, hz⟩ := e.history_mono resp k d
  refine History.Precedes.of_split hz
    ((e.responded_iff resp k a (resp a)).mpr ⟨ha, rfl⟩) ?_
  have h1 : Event.invoke b ∈ e.history resp (k + d) := (e.invoked_iff resp _ b).mpr hbN
  have h2 : Event.invoke b ∉ e.history resp k := fun hx => hb ((e.invoked_iff resp k b).mp hx)
  rw [hz] at h1
  exact (List.mem_append.mp h1).resolve_left h2

/-! ## The manuscript's linearizability, on the literal event sequence

`Object.Linearizes` states the paper's condition at a
configuration boundary.  The following turns it into the paper's own
statement: a completion of the literal event history, matching a legal
sequential history process by process, and preserving real-time order. -/

section Linearizability
variable {State : Type} [DecidableEq Op]

/-- The pending operations the linearization `x` retains, paired with the
values the completion supplies for them — `ret*(cmd(Φ), t)` in the paper. -/
def pendingExtension (obj : Object State (Command P Op) Response) (N : Nat)
    (x : List (Command P Op)) : List (Command P Op × Response) :=
  (x.filter (fun a => a ∉ (e.state N).returned)).map
    (fun a => (a, obj.sequentialResponse x a))

/-- The manuscript's completion `H̄`: pending invocations the linearization
omits are dropped, and the ones it retains receive a matching response. -/
def completion (obj : Object State (Command P Op) Response) (N : Nat)
    (x : List (Command P Op)) : History (Command P Op) Response :=
  (e.history resp N).filter (fun ev => ev.op ∈ x) ++
    (e.pendingExtension obj N x).map (fun p => Event.respond p.1 p.2)

variable (obj : Object State (Command P Op) Response) {N : Nat} {x : List (Command P Op)}

/-- `completion` really is a completion: it only drops pending invocations and
only appends responses to pending, retained ones. -/
theorem isCompletion
    (hxinv : ∀ a ∈ x, a ∈ (e.state N).invoked)
    (hretx : ∀ a ∈ (e.state N).returned, a ∈ x) :
    (e.history resp N).IsCompletion (e.completion resp obj N x) := by
  refine ⟨fun a => decide (a ∈ x), e.pendingExtension obj N x, rfl, ?_, ?_⟩
  · intro a hin hkeep
    have hax : a ∉ x := of_decide_eq_false hkeep
    refine ⟨hin, ?_⟩
    rintro ⟨v, hv⟩
    exact hax (hretx a ((e.responded_iff resp N a v).mp hv).1)
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hax, hnr⟩ := List.mem_filter.mp ha
    refine ⟨⟨(e.invoked_iff resp N a).mpr (hxinv a hax), ?_⟩, decide_eq_true hax⟩
    rintro ⟨v, hv⟩
    exact (of_decide_eq_true hnr) ((e.responded_iff resp N a v).mp hv).1

/-- Linearization order restricted to one process is increasing in the local
sequence number.  This is the converse of the manuscript's process-order
requirement, and it is what makes the two per-process views the same list. -/
theorem filter_pairwise_of_order (i : P) (hxnd : x.Nodup)
    (hxinv : ∀ a ∈ x, a ∈ (e.state N).invoked)
    (horder : ∀ a b, a ∈ x → b ∈ x → a.process = b.process →
      a.sequence < b.sequence → x.idxOf a < x.idxOf b) :
    (x.filter (fun a => a.process = i)).Pairwise (fun a b => a.sequence < b.sequence) := by
  refine List.pairwise_filter.mpr (List.pairwise_iff_getElem.mpr ?_)
  intro i' j' hi' hj' hlt hpi hpj
  have hmi : x[i'] ∈ x := List.getElem_mem hi'
  have hmj : x[j'] ∈ x := List.getElem_mem hj'
  have hproc : x[i'].process = x[j'].process := by
    rw [of_decide_eq_true hpi, of_decide_eq_true hpj]
  have hidxi : x.idxOf x[i'] = i' := hxnd.idxOf_getElem i' hi'
  have hidxj : x.idxOf x[j'] = j' := hxnd.idxOf_getElem j' hj'
  rcases Nat.lt_trichotomy x[i'].sequence x[j'].sequence with h | h | h
  · exact h
  · exfalso
    have hkey : x[i'].key = x[j'].key := by unfold Command.key; rw [hproc, h]
    have heq := InvocationLedger.key_injective (e.valid N) (hxinv _ hmi) (hxinv _ hmj) hkey
    rw [heq, hidxj] at hidxi
    omega
  · exfalso
    have hb := horder x[j'] x[i'] hmj hmi hproc.symm h
    rw [hidxi, hidxj] at hb
    omega

/-- **The manuscript's per-process condition** `H̄|ᵢ = S|ᵢ`.  Process `i`'s
completed history is literally its part of the sequential history: its
invocation order and its linearization order are the same order. -/
theorem project_completion (i : P) (hxnd : x.Nodup)
    (hxinv : ∀ a ∈ x, a ∈ (e.state N).invoked)
    (hretx : ∀ a ∈ (e.state N).returned, a ∈ x ∧ obj.sequentialResponse x a = resp a)
    (horder : ∀ a b, a ∈ x → b ∈ x → a.process = b.process →
      a.sequence < b.sequence → x.idxOf a < x.idxOf b) :
    History.project Command.process i (e.completion resp obj N x) =
      History.project Command.process i (obj.sequentialEvents x) := by
  classical
  have hRmem : ∀ a, a ∈ ((e.state N).returned.filter (fun c => c.process = i)).reverse ↔
      (a ∈ (e.state N).returned ∧ a.process = i) := by
    intro a; rw [List.mem_reverse, List.mem_filter]; simp
  have hXmem : ∀ a, a ∈ x.filter (fun a => a.process = i) ↔ (a ∈ x ∧ a.process = i) := by
    intro a; rw [List.mem_filter]; simp
  have hXpair := e.filter_pairwise_of_order i hxnd hxinv horder
  -- Any list of pairs with the right members, order and values *is* `S|ᵢ`.
  have key : ∀ R : List (Command P Op × Response),
      (R.map Prod.fst).Pairwise (fun a b => a.sequence < b.sequence) →
      (∀ a, a ∈ R.map Prod.fst ↔ a ∈ x.filter (fun a => a.process = i)) →
      (∀ p ∈ R, p.2 = obj.sequentialResponse x p.1) →
      R = (x.filter (fun a => a.process = i)).map
        (fun a => (a, obj.sequentialResponse x a)) := by
    intro R hpair hmem hval
    have hfst : R.map Prod.fst = x.filter (fun a => a.process = i) :=
      pairwise_key_ext Command.sequence hpair hXpair hmem
    calc R = (R.map Prod.fst).map (fun a => (a, obj.sequentialResponse x a)) :=
          eq_map_of_snd _ hval
      _ = _ := by rw [hfst]
  -- Unfold both sides into alternating normal form.
  rw [completion, History.project_append,
    History.project_filter Command.process i (fun a => decide (a ∈ x)) (e.history resp N),
    e.project_history resp i N,
    History.filter_alternating (fun a => decide (a ∈ x)),
    History.project_map_respond,
    obj.project_sequentialEvents Command.process i hxnd]
  have hself : ((((e.state N).returned.filter (fun c => c.process = i)).reverse).map
        (fun c => (c, resp c))).filter (fun p => decide (p.1 ∈ x)) =
      (((e.state N).returned.filter (fun c => c.process = i)).reverse).map
        (fun c => (c, resp c)) := by
    refine List.filter_eq_self.mpr ?_
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact decide_eq_true ((hretx c ((hRmem c).mp hc).1).1)
  have hQ : (e.pendingExtension obj N x).filter (fun p => decide (p.1.process = i)) =
      (x.filter (fun a => decide (a.process = i) &&
        decide (a ∉ (e.state N).returned))).map
        (fun a => (a, obj.sequentialResponse x a)) := by
    rw [pendingExtension, List.filter_map, List.filter_filter]
    rfl
  have hfstmap : ((((e.state N).returned.filter (fun c => c.process = i)).reverse).map
      (fun c => (c, resp c))).map Prod.fst =
      ((e.state N).returned.filter (fun c => c.process = i)).reverse := by
    rw [List.map_map]; exact List.map_id _
  have hvalR : ∀ p ∈ (((e.state N).returned.filter (fun c => c.process = i)).reverse).map
      (fun c => (c, resp c)), p.2 = obj.sequentialResponse x p.1 := by
    intro p hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    exact (hretx c ((hRmem c).mp hc).1).2.symm
  rw [hself, hQ]
  -- when `x` retains no pending operation of `i`, nothing is appended to either side
  have hnil (hret : ∀ a ∈ x, a.process = i → a ∈ (e.state N).returned) :
      x.filter (fun a => decide (a.process = i) && decide (a ∉ (e.state N).returned)) = [] :=
    List.filter_eq_nil_iff.mpr fun a ha hq => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      exact hq.2 (hret a ha hq.1)
  have hnopending (hret : ∀ a ∈ x, a.process = i → a ∈ (e.state N).returned) :
      History.alternating ((((e.state N).returned.filter (fun c => c.process = i)).reverse).map
          (fun c => (c, resp c))) none =
        History.alternating ((x.filter (fun a => a.process = i)).map
          (fun a => (a, obj.sequentialResponse x a))) none := by
    refine congrArg (fun l => History.alternating l none) (key _ ?_ ?_ hvalR)
    · rw [hfstmap]; exact e.returned_pairwise i N
    · intro a
      rw [hfstmap, hRmem, hXmem]
      exact ⟨fun h => ⟨(hretx a h.1).1, h.2⟩, fun h => ⟨hret a h.1 h.2, h.2⟩⟩
  cases hact : (e.state N).active i with
  | none =>
    -- `i` has no active operation, so none of its operations is pending
    have hret : ∀ a ∈ x, a.process = i → a ∈ (e.state N).returned := fun a ha hai =>
      Classical.byContradiction fun hnr => by
        have := e.active_of_pending (hxinv a ha) hnr
        rw [hai, hact] at this
        simp at this
    rw [hnil hret]
    simp only [List.map_nil, List.append_nil]
    exact hnopending hret
  | some c =>
    have hcp : c.process = i := ((e.valid N).active_tag i c hact).1
    have hcr : c ∉ (e.state N).returned := by
      intro hc
      exact (e.valid N).active_pending i c hact c hc rfl
    have huniq : ∀ a ∈ x, (decide (a.process = i) &&
        decide (a ∉ (e.state N).returned)) = true → a = c := by
      intro a ha hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      have h1 := e.active_of_pending (hxinv a ha) hq.2
      rw [hq.1, hact] at h1
      exact (Option.some.inj h1).symm
    by_cases hcx : c ∈ x
    · have hone : x.filter (fun a => decide (a.process = i) &&
          decide (a ∉ (e.state N).returned)) = [c] :=
        filter_eq_singleton hxnd hcx (by simp [hcp, hcr]) huniq
      rw [hone]
      simp only [List.map_cons, List.map_nil, hcx, decide_true, reduceIte,
        History.alternating_some_append_respond]
      refine congrArg (fun l => History.alternating l none) (key _ ?_ ?_ ?_)
      · rw [List.map_append, hfstmap]
        refine List.pairwise_append.mpr ⟨e.returned_pairwise i N, by simp, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst b
        exact e.active_sequence_gt hact ((hRmem a).mp ha).1 ((hRmem a).mp ha).2
      · intro a
        rw [List.map_append, hfstmap, List.mem_append, hXmem]
        simp only [List.map_cons, List.map_nil, List.mem_singleton]
        rw [hRmem]
        constructor
        · rintro (⟨h1, h2⟩ | rfl)
          · exact ⟨(hretx a h1).1, h2⟩
          · exact ⟨hcx, hcp⟩
        · rintro ⟨h1, h2⟩
          by_cases hnr : a ∈ (e.state N).returned
          · exact Or.inl ⟨hnr, h2⟩
          · have := e.active_of_pending (hxinv a h1) hnr
            rw [h2, hact] at this
            exact Or.inr (Option.some.inj this).symm
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hvalR p hp
        · simp only [List.mem_singleton] at hp
          subst p
          rfl
    · -- `i`'s only pending operation, `c`, is not in `x`
      have hret : ∀ a ∈ x, a.process = i → a ∈ (e.state N).returned := fun a ha hai =>
        Classical.byContradiction fun hnr => by
          have h1 := e.active_of_pending (hxinv a ha) hnr
          rw [hai, hact] at h1
          exact hcx ((Option.some.inj h1) ▸ ha)
      rw [hnil hret]
      simp only [List.map_nil, List.append_nil, hcx, decide_false]
      exact hnopending hret

/-- **The manuscript's linearizability, on the literal event history.**
A boundary-form linearization `x` of the observed history yields a completion
of the run's event sequence that matches the legal sequential history `S_x`
process by process and preserves real-time order — the definition recalled in
Appendix A of the paper, with no configuration boundaries in the statement. -/
theorem eventLinearizable_of_linearizes
    {Hobs : FiniteHistory (Command P Op) Response}
    (hx : obj.Linearizes Hobs N x)
    (hinv : ∀ k, k ≤ N → ∀ a, Hobs.invoked k a → a ∈ (e.state k).invoked)
    (hret : ∀ k, k ≤ N → ∀ a, a ∈ (e.state k).returned → Hobs.returned k a (resp a))
    (horder : ∀ a b, a ∈ x → b ∈ x → a.process = b.process →
      a.sequence < b.sequence → x.idxOf a < x.idxOf b) :
    obj.EventLinearizable Command.process (e.history resp N) := by
  have hxnd : x.Nodup := hx.unique
  have hxinv : ∀ a ∈ x, a ∈ (e.state N).invoked :=
    fun a ha => hinv N (Nat.le_refl N) a (hx.invoked a ha)
  have hretx : ∀ a ∈ (e.state N).returned, a ∈ x ∧ obj.sequentialResponse x a = resp a :=
    fun a ha => hx.completed a (resp a) (hret N (Nat.le_refl N) a ha)
  refine ⟨e.completion resp obj N x, x,
    e.isCompletion resp obj hxinv (fun a ha => (hretx a ha).1),
    fun i => e.project_completion resp obj i hxnd hxinv hretx horder, ?_⟩
  intro a b hprec hbinv
  have hbx : b ∈ x := by
    simp only [History.Invoked, completion, List.mem_append] at hbinv
    rcases hbinv with h | h
    · exact of_decide_eq_true (List.mem_filter.mp h).2
    · obtain ⟨p, _, hp⟩ := List.mem_map.mp h
      exact absurd hp (by simp)
  obtain ⟨k, hk, ha, hb⟩ := e.precedes_boundary resp hprec
  exact obj.sequentialEvents_precedes hxnd (hretx a (e.returned_mono hk ha)).1 hbx
    (hx.realTime a b (hretx a (e.returned_mono hk ha)).1 hbx
      ⟨k, hk, ⟨resp a, hret k hk a ha⟩, fun hbb => hb (hinv k hk b hbb)⟩)

end Linearizability

end Run
end InvocationLedger
end ConflictFreedom
