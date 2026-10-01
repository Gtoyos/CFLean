import CFLeanProof.Commands
import CFLeanProof.UniversalRounds

/-! Algorithm 1 as an interleaving transition system over atomic S registers and
GCA calls. The maximum-round collect consists of separate register reads, not
an assumed atomic snapshot, and — as the manuscript does not fix it — reads the
registers in any order, chosen when it starts (`Step.invoke`). GCA histories are
an explicit environment; calls and responses must match them. Predecessor
linkage is proved from transitions.

Line `k` of Algorithm 1 is the manuscript's label `line:uc:k`; the typeset
algorithm numbers the same lines one to three higher.
-/
namespace ConflictFreedom.WeakUniversal
open Object
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-- A command `(op, i, seq)`: an operation tagged with its process and that
process's sequence number (Line 3). -/
abbrev Cmd (n : Nat) (Op : Type) := Command (Fin n) Op

/-- The object `A_c` over commands, whose traces the GCA instances agree on. -/
abbrev Tagged := obj.commandObject (Fin n)

/-- A round and a trace `(r, s)`: the value of an `S` register, and a process's
local `(r, s)`. -/
structure Seed where
  round : Nat
  trace : (Tagged (n := n) obj).Trace

/-- Where a process is in Algorithm 1. -/
inductive Local where
  /-- Not executing an operation. -/
  | idle
  /-- Line 4: collecting the `S` registers one read at a time; `todo` are the
  registers still to read, in the order chosen when the collect started, and
  `best` the value of highest round read so far. -/
  | collecting (cmd : Cmd n Op) (todo : List (Fin n)) (best : Seed (n := n) obj)
  /-- About to run the loop body (Lines 6–9) from `(r, s) = base`. -/
  | ready (cmd : Cmd n Op) (base : Seed (n := n) obj)
  /-- Inside `GCA_round.propose(proposal)` (Line 9). -/
  | waiting (cmd : Cmd n Op) (round : Nat) (proposal : (Tagged (n := n) obj).Trace)
  /-- Out of the loop: about to write `(round, trace)` into `S[i]` (Line 10). -/
  | publishing (cmd : Cmd n Op) (round : Nat) (trace : (Tagged (n := n) obj).Trace)
  /-- About to return the response of `cmd` in `trace` (Line 11). -/
  | returning (cmd : Cmd n Op) (round : Nat) (trace : (Tagged (n := n) obj).Trace)

/-- A GCA call recorded by the run: `process` proposed `trace` to round
`round`. -/
structure Call where
  round : Nat
  process : Fin n
  trace : (Tagged (n := n) obj).Trace

/-- A response recorded by the run: `command` returned with `trace`, committed
at round `round`; its value is read off `trace` (`response`). -/
structure Return where
  command : Cmd n Op
  round : Nat
  trace : (Tagged (n := n) obj).Trace

/-- A global state: each process's sequence counter (`seq`, Line 2) and position,
the `S` registers (`slots`), and the history so far — GCA calls, responses and
invocations, most recent first. -/
structure Configuration where
  sequence : Fin n → Nat
  localState : Fin n → Local (n := n) obj
  slots : Fin n → Seed (n := n) obj
  calls : List (Call (n := n) obj)
  returns : List (Return (n := n) obj)
  invocations : List (Cmd n Op)

/-- The initial value `(0, ε)` of the registers and of the local `(r, s)`. -/
def zeroSeed : Seed (n := n) obj := ⟨0, (Tagged obj).emptyTrace⟩

/-- Every process idle, every register `(0, ε)`, nothing recorded yet. -/
def initial : Configuration (n := n) obj where
  sequence := fun _ => 0
  localState := fun _ => .idle
  slots := fun _ => zeroSeed obj
  calls := []
  returns := []
  invocations := []

/-- Point update of a per-process array: `p` gets `v`. -/
def update {α : Type} (f : Fin n → α) (p : Fin n) (v : α) : Fin n → α :=
  fun q => if q = p then v else f q

/-- The seed of higher round, the first one on a tie: one step of the maximum
of Line 4. -/
def best (s t : Seed (n := n) obj) : Seed (n := n) obj :=
  if s.round < t.round then t else s

theorem best_round (s t : Seed (n := n) obj) : (best obj s t).round = max s.round t.round := by
  unfold best; split <;> omega

theorem best_round_left (s t : Seed (n := n) obj) : s.round ≤ (best obj s t).round := by
  rw [best_round]; exact Nat.le_max_left _ _

theorem best_round_right (s t : Seed (n := n) obj) : t.round ≤ (best obj s t).round := by
  rw [best_round]; exact Nat.le_max_right _ _

variable [DecidableEq Op]

/-- The history of every GCA instance: round `r`'s inputs and outputs. -/
abbrev Environment := Nat → GCA.History (Tagged (n := n) obj) (Fin n)

/-- Finite local work is grouped between atomic register/GCA events. Round zero
is the initial register value; actual GCA instances have positive numbers. -/
inductive Step (H : Environment (n := n) obj) :
    Configuration (n := n) obj → Configuration (n := n) obj → Prop where
  /-- Lines 1–3: `op` is invoked with the next sequence number, and the collect
  of Line 4 starts, reading the `n` registers of `S` in any order `order`. -/
  | invoke (c) (p : Fin n) (op : Op) (h : c.localState p = .idle)
      (order : List (Fin n)) (horder : order.Perm (List.finRange n)) :
      Step H c { c with
        sequence := update c.sequence p (c.sequence p + 1)
        invocations := ⟨op, p, c.sequence p + 1⟩ :: c.invocations
        localState := update c.localState p (.collecting ⟨op, p, c.sequence p + 1⟩
          order (zeroSeed obj)) }
  /-- Line 4: one read of `S[q]`, keeping the value of higher round. -/
  | read (c) (p q : Fin n) cmd todo seed
      (h : c.localState p = .collecting cmd (q :: todo) seed) :
      Step H c { c with
        localState := update c.localState p
          (.collecting cmd todo (best obj seed (c.slots q))) }
  /-- Line 4 is done: every register has been read. -/
  | collected (c) (p : Fin n) cmd seed (h : c.localState p = .collecting cmd [] seed) :
      Step H c { c with localState := update c.localState p (.ready cmd seed) }
  /-- Lines 6–9: the proposal `s · cmd` (or `s`, if `cmd` already occurs in it)
  goes to round `r + 1`; the environment's input must match. -/
  | propose (c) (p : Fin n) cmd seed (h : c.localState p = .ready cmd seed)
      (hi : (H (seed.round + 1)).input p = some ((Tagged obj).appendMissing seed.trace cmd)) :
      Step H c { c with
        localState := update c.localState p
          (.waiting cmd (seed.round + 1) ((Tagged obj).appendMissing seed.trace cmd))
        calls := ⟨seed.round + 1, p, (Tagged obj).appendMissing seed.trace cmd⟩ :: c.calls }
  /-- Line 9 returns `(s, flag)`.  The loop (Line 5) exits when `flag` is set and
  `cmd` occurs in `s`, and runs again from `(r, s)` otherwise. -/
  | receive (c) (p : Fin n) cmd r proposal s flag
      (h : c.localState p = .waiting cmd r proposal)
      (ho : (H r).output p = some (s, flag)) :
      Step H c { c with
        localState := update c.localState p
          (if flag = true ∧ 0 < (Tagged obj).traceCount cmd s then .publishing cmd r s
          else .ready cmd ⟨r, s⟩) }
  /-- Line 10: `S[i] ← (r, s)`. -/
  | publish (c) (p : Fin n) cmd r s (h : c.localState p = .publishing cmd r s) :
      Step H c { c with
        localState := update c.localState p (.returning cmd r s)
        slots := update c.slots p ⟨r, s⟩ }
  /-- Line 11: the operation returns, and its response is recorded. -/
  | finish (c) (p : Fin n) cmd r s (h : c.localState p = .returning cmd r s) :
      Step H c { c with
        localState := update c.localState p .idle
        returns := ⟨cmd, r, s⟩ :: c.returns }

/-- Return interpretation is precisely line 11, using the command identity. -/
def response (ret : Return (n := n) obj) : Option Response :=
  (Tagged obj).traceReturn ret.command 0 ret.trace

/-- The configurations reachable from `initial`. -/
inductive Reachable (H : Environment (n := n) obj) : Configuration (n := n) obj → Prop where
  | initial : Reachable H (initial obj)
  | step {c d} : Reachable H c → Step obj H c d → Reachable H d

/-- A seed is either the initial empty trace or an actual output of its round. -/
def Supported (H : Environment (n := n) obj) (s : Seed (n := n) obj) : Prop :=
  (s.round = 0 ∧ s.trace = (Tagged obj).emptyTrace) ∨
    0 < s.round ∧ ∃ q flag, (H s.round).output q = some (s.trace, flag)

/-- `s` is committed at round `r`: some process received `(s, true)` from
`GCA_r`. -/
def Committed (H : Environment (n := n) obj) (r : Nat) (s : (Tagged (n := n) obj).Trace) : Prop :=
  0 < r ∧ ∃ q, (H r).output q = some (s, true)

/-- A possible register value: `(0, ε)`, or a trace committed at its round. -/
def Stored (H : Environment (n := n) obj) (s : Seed (n := n) obj) : Prop :=
  (s.round = 0 ∧ s.trace = (Tagged obj).emptyTrace) ∨ Committed obj H s.round s.trace

/-- What each position guarantees about the seed or trace it holds. -/
def LocalInvariant (H : Environment (n := n) obj) : Local (n := n) obj → Prop
  | .idle => True
  | .collecting _ _ s => Supported obj H s
  | .ready _ s => Supported obj H s
  | .waiting _ r _ => 0 < r
  | .publishing cmd r s => Committed obj H r s ∧ 0 < (Tagged obj).traceCount cmd s
  | .returning cmd r s => Committed obj H r s ∧ 0 < (Tagged obj).traceCount cmd s

/-- The predecessor obligation is a conclusion about each recorded proposal. -/
def CallInvariant (H : Environment (n := n) obj) (call : Call (n := n) obj) : Prop :=
  ∀ r, call.round = r + 2 → ∃ q t flag, (H (r + 1)).output q = some (t, flag) ∧
    (Tagged obj).TracePrefix t call.trace

/-- The configuration invariant of Algorithm 1, true in every reachable
configuration (`invariant`). -/
structure Invariant (H : Environment (n := n) obj) (c : Configuration (n := n) obj) : Prop where
  slots : ∀ p, Stored obj H (c.slots p)
  localState : ∀ p, LocalInvariant obj H (c.localState p)
  calls : ∀ call ∈ c.calls, CallInvariant obj H call
  returns : ∀ ret ∈ c.returns, Committed obj H ret.round ret.trace ∧
    0 < (Tagged obj).traceCount ret.command ret.trace

omit [DecidableEq Op] in
theorem stored_supported {H : Environment (n := n) obj} {s : Seed (n := n) obj}
    (h : Stored obj H s) : Supported obj H s := by
  rcases h with h | ⟨hr, q, hq⟩
  · exact Or.inl h
  · exact Or.inr ⟨hr, q, true, hq⟩

theorem invariant_initial (H : Environment (n := n) obj) : Invariant obj H (initial obj) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p; exact Or.inl ⟨rfl, rfl⟩
  · intro p; trivial
  · intro call h; cases h
  · intro ret h; cases h

private theorem local_update {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : ∀ p, LocalInvariant obj H (c.localState p)) (p : Fin n) (l : Local (n := n) obj)
    (hl : LocalInvariant obj H l) : ∀ q, LocalInvariant obj H (update c.localState p l q) := by
  intro q
  unfold update
  split
  · exact hl
  · exact hc q

theorem invariant_step {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hc : Invariant obj H c) (hs : Step obj H c d) : Invariant obj H d := by
  cases hs with
  | invoke p op h =>
    refine ⟨hc.slots, local_update obj hc.localState p _ ?_, hc.calls, hc.returns⟩
    exact Or.inl ⟨rfl, rfl⟩
  | read p q cmd todo seed h =>
    refine ⟨hc.slots, local_update obj hc.localState p _ ?_, hc.calls, hc.returns⟩
    have hseed := hc.localState p
    rw [h] at hseed
    change Supported obj H (best obj seed (c.slots q))
    unfold best
    split
    · exact stored_supported obj (hc.slots q)
    · exact hseed
  | collected p cmd seed h =>
    refine ⟨hc.slots, local_update obj hc.localState p _ ?_, hc.calls, hc.returns⟩
    have hseed := hc.localState p
    simpa only [h, LocalInvariant] using hseed
  | propose p cmd seed h hi =>
    refine ⟨hc.slots, local_update obj hc.localState p _ (by change 0 < seed.round + 1; omega), ?_, hc.returns⟩
    intro call hcall
    rcases List.mem_cons.mp hcall with rfl | hcall
    · intro r hr
      have hseed := hc.localState p
      rw [h] at hseed
      rcases hseed with ⟨hz, _⟩ | ⟨_, q, flag, hq⟩
      · change seed.round + 1 = r + 2 at hr
        omega
      · have he : seed.round = r + 1 := by change seed.round + 1 = r + 2 at hr; omega
        refine ⟨q, seed.trace, flag, ?_, (Tagged obj).appendMissing_extends seed.trace cmd⟩
        simpa only [he] using hq
    · exact hc.calls call hcall
  | receive p cmd r proposal s flag h ho =>
    have hpos : 0 < r := by simpa only [h, LocalInvariant] using hc.localState p
    refine ⟨hc.slots, local_update obj hc.localState p _ ?_, hc.calls, hc.returns⟩
    split
    · rename_i he
      exact ⟨⟨hpos, p, he.1 ▸ ho⟩, he.2⟩
    · exact Or.inr ⟨hpos, p, flag, ho⟩
  | publish p cmd r s h =>
    have hp := hc.localState p
    rw [h] at hp
    refine ⟨?_, local_update obj hc.localState p _ hp, hc.calls, hc.returns⟩
    · intro q
      change Stored obj H (update c.slots p ⟨r, s⟩ q)
      unfold update
      split
      · exact Or.inr hp.1
      · exact hc.slots q
  | finish p cmd r s h =>
    have hp := hc.localState p
    rw [h] at hp
    refine ⟨hc.slots, local_update obj hc.localState p _ trivial, hc.calls, ?_⟩
    intro ret hret
    rcases List.mem_cons.mp hret with rfl | hret
    · exact hp
    · exact hc.returns ret hret

theorem invariant {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : Invariant obj H c := by
  induction hc with
  | initial => exact invariant_initial obj H
  | step _ hs ih => exact invariant_step obj ih hs

/-- Coverage connects an environment history with the calls actually made by a
program execution. It is history bookkeeping, not a predecessor assumption. -/
def CallsCovered (H : Environment (n := n) obj) : Prop :=
  ∀ r p s, (H (r + 1)).input p = some s →
    ∃ c, Reachable obj H c ∧ (⟨r + 1, p, s⟩ : Call obj) ∈ c.calls

/-- Algorithm 1's transitions establish the predecessor linkage required by
`RoundExecution`. The zero-based round r here is manuscript GCA instance r+1. -/
def roundExecution (H : Environment (n := n) obj) (coverage : CallsCovered obj H) :
    GCA.RoundExecution (Tagged (n := n) obj) (Fin n) where
  round := fun r => H (r + 1)
  predecessor := by
    intro r p s hs
    obtain ⟨c, hc, hcall⟩ := coverage (r + 1) p s hs
    exact (invariant obj hc).calls _ hcall r rfl

/-- Prefix-rounds specialized to the weak universal-construction transition
system, deriving predecessor linkage rather than assuming it. -/
theorem committed_prefix {H : Environment (n := n) obj} (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) {r k : Nat} (hrk : r ≤ k)
    {p q : Fin n} {s t : (Tagged (n := n) obj).Trace} {flag : Bool}
    (hs : (H (r + 1)).output p = some (s, true))
    (ht : (H (k + 1)).output q = some (t, flag)) : (Tagged obj).TracePrefix s t :=
  (roundExecution obj H coverage).commit_below_later_output spec hrk hs ht

/-- An interleaved run of Algorithm 1, allowing idle scheduler steps. -/
structure Execution (H : Environment (n := n) obj) where
  state : Nat → Configuration (n := n) obj
  initial_state : state 0 = initial obj
  next : ∀ t, state (t + 1) = state t ∨ Step obj H (state t) (state (t + 1))

theorem Execution.reachable {H : Environment (n := n) obj} (run : Execution obj H)
    (t : Nat) : Reachable obj H (run.state t) := by
  induction t with
  | zero => rw [run.initial_state]; exact Reachable.initial
  | succ t ih =>
    rcases run.next t with he | hs
    · exact he ▸ ih
    · exact Reachable.step ih hs

/-- A faithful history has no input that was never called by this run. -/
def Execution.Covers {H : Environment (n := n) obj} (run : Execution obj H) : Prop :=
  ∀ r p s, (H (r + 1)).input p = some s →
    ∃ t, (⟨r + 1, p, s⟩ : Call obj) ∈ (run.state t).calls

theorem Execution.callsCovered {H : Environment (n := n) obj} (run : Execution obj H)
    (h : run.Covers obj) : CallsCovered obj H := by
  intro r p s hs
  obtain ⟨t, ht⟩ := h r p s hs
  exact ⟨run.state t, run.reachable obj t, ht⟩

/-- Any two committed traces are prefix-comparable. -/
theorem committed_comparable {H : Environment (n := n) obj} (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) {r k : Nat} {s t : (Tagged (n := n) obj).Trace}
    (hs : Committed obj H r s) (ht : Committed obj H k t) :
    (Tagged obj).TracePrefix s t ∨ (Tagged obj).TracePrefix t s := by
  obtain ⟨hr, p, hp⟩ := hs
  obtain ⟨hk, q, hq⟩ := ht
  cases r with
  | zero => omega
  | succ r =>
    cases k with
    | zero => omega
    | succ k => exact (roundExecution obj H coverage).commits_comparable spec hp hq

/-- All response traces recorded in a reachable state are prefix-comparable. -/
theorem return_traces_comparable {H : Environment (n := n) obj} (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) {a b : Return (n := n) obj} (ha : a ∈ c.returns) (hb : b ∈ c.returns) :
    (Tagged obj).TracePrefix a.trace b.trace ∨ (Tagged obj).TracePrefix b.trace a.trace :=
  committed_comparable obj coverage spec ((invariant obj hc).returns a ha).1
    ((invariant obj hc).returns b hb).1

/-- The return expression is defined for every completed invocation. -/
theorem response_defined {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) {ret : Return (n := n) obj} (hr : ret ∈ c.returns) :
    ∃ v, response obj ret = some v :=
  (Tagged obj).traceReturn_defined ret.trace ret.command 0 ((invariant obj hc).returns ret hr).2

end ConflictFreedom.WeakUniversal
