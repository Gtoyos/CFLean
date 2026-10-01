import CFLeanProof.WeakUniversal

/-! Algorithm 3, with persistent local round/trace state and separate atomic
reads of S and M.  The manuscript fixes neither the order in which its collects
read the registers nor the order of `trace(M_i)` at Line 11, and neither does the
model.  Each collect — of `S` at Lines 6 and 16, of `M` at Line 10 — reads the
`n` registers in any order, chosen when it starts (`Step.announce`,
`Step.receive`, `Step.publish` for `S`; `Step.collectedStart`, `Step.retry` for
`M`), and `trace(M_i)` is any ordering of the missing announcements the collect
of `M` found (`Step.propose`).  The local base survives a return even when the
returned command was found in another process's committed trace.

Line `k` of Algorithm 3 is the manuscript's label `line:cfuc:k`; these agree
with the typeset numbering, except that the return (`line:cfuc:19`) is typeset
as Line 18.
-/
namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best Supported Committed Stored CallInvariant)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-- Where a process is in Algorithm 3. -/
inductive Local where
  /-- Not executing an operation; `base` is the local `(r, s)`, kept across
  operations. -/
  | idle (base : Seed (n := n) obj)
  /-- Lines 1–4 done: about to write `cmd` into `M[i]` (Line 5). -/
  | announcing (cmd : Cmd n Op) (base : Seed (n := n) obj)
  /-- Line 6: collecting the `S` registers one read at a time, starting from the
  local `(r, s)`; `todo` is what is left of the order, chosen when the collect
  started, in which it reads the registers, and `best` is the value of highest
  round so far. -/
  | collecting (cmd : Cmd n Op) (todo : List (Fin n)) (best : Seed (n := n) obj)
  /-- Line 10: collecting `M` one read at a time from `(r, s) = base`; `todo`
  is what is left of the order, chosen when the collect started, in which it
  reads the registers, and `commands` are the announcements read so far that
  are missing from `s`. -/
  | gathering (cmd : Cmd n Op) (base : Seed (n := n) obj)
      (todo : List (Fin n)) (commands : List (Cmd n Op))
  /-- Inside `GCA_round.propose(proposal)` (Line 12). -/
  | waiting (cmd : Cmd n Op) (round : Nat) (proposal : (Tagged (n := n) obj).Trace)
  /-- `GCA_r` committed `base = (r, s)`: about to write it into `S[i]` (Line 14). -/
  | publishing (cmd : Cmd n Op) (base : Seed (n := n) obj)
  /-- Line 16: collecting `S` one read at a time to compute `u`, from
  `(r, s) = base`; `todo` is what is left of the order, chosen when the collect
  started, in which it reads the registers, and `best` is the value of highest
  round so far. -/
  | checking (cmd : Cmd n Op) (base : Seed (n := n) obj)
      (todo : List (Fin n)) (best : Seed (n := n) obj)

/-- A global state of Algorithm 3: that of Algorithm 1
(`WeakUniversal.Configuration`) plus the announcement array `M`. -/
structure Configuration where
  sequence : Fin n → Nat
  localState : Fin n → Local (n := n) obj
  slots : Fin n → Seed (n := n) obj
  announcements : Fin n → Option (Cmd n Op)
  calls : List (Call (n := n) obj)
  returns : List (Return (n := n) obj)
  invocations : List (Cmd n Op)

/-- Every process idle at `(0, ε)`, `S` all `(0, ε)`, `M` all `⊥`, nothing
recorded yet. -/
def initial : Configuration (n := n) obj where
  sequence := fun _ => 0
  localState := fun _ => .idle (zeroSeed obj)
  slots := fun _ => zeroSeed obj
  announcements := fun _ => none
  calls := []
  returns := []
  invocations := []

variable [DecidableEq Op]

/-- Line 11's `s · trace(M_i)`, for `trace(M_i)` the trace of the list
`commands` — the missing announcements, in the order Line 11 arranges them.
`Step.propose` allows any arrangement of the announcements the collect found. -/
def proposal (base : Seed (n := n) obj) (commands : List (Cmd n Op)) : (Tagged (n := n) obj).Trace :=
  (Tagged obj).traceAppend base.trace (Quotient.mk (Tagged obj).traceSetoid commands)

omit [DecidableEq Op] in
theorem proposal_extends (base : Seed (n := n) obj) (commands : List (Cmd n Op)) :
    (Tagged obj).TracePrefix base.trace (proposal obj base commands) :=
  ((Tagged obj).tracePrefix_iff_append _ _).mpr ⟨_, rfl⟩

/-- One read of Line 10: the announcement `seen` read from some `M[j]` joins the
command list when it is present and missing from the base trace. -/
def observe (base : Seed (n := n) obj) (seen : Option (Cmd n Op)) (commands : List (Cmd n Op)) :
    List (Cmd n Op) :=
  match seen with
  | none => commands
  | some cmd => if (Tagged obj).traceCount cmd base.trace = 0 then commands ++ [cmd] else commands

/-- One atomic step of Algorithm 3: an invocation, a register read or write, a
GCA call or return, or a response; local work is grouped with the next atomic
event, as in Algorithm 1 (`WeakUniversal.Step`). -/
inductive Step (H : Environment (n := n) obj) :
    Configuration (n := n) obj → Configuration (n := n) obj → Prop where
  /-- Lines 1–4: `op` is invoked with the next sequence number. -/
  | invoke (c) (p : Fin n) (op : Op) seed (h : c.localState p = .idle seed) :
      Step H c { c with
        sequence := update c.sequence p (c.sequence p + 1)
        invocations := ⟨op, p, c.sequence p + 1⟩ :: c.invocations
        localState := update c.localState p (.announcing ⟨op, p, c.sequence p + 1⟩ seed) }
  /-- Line 5: `M[i] ← cmd`; the collect of Line 6 starts from the local `(r, s)`,
  reading the `n` registers of `S` in any order `order`. -/
  | announce (c) (p : Fin n) cmd seed (h : c.localState p = .announcing cmd seed)
      (order : List (Fin n)) (horder : order.Perm (List.finRange n)) :
      Step H c { c with
        announcements := update c.announcements p (some cmd)
        localState := update c.localState p (.collecting cmd order seed) }
  /-- Line 6: one read of `S[q]`, keeping the value of higher round. -/
  | readStart (c) (p q : Fin n) cmd todo seed
      (h : c.localState p = .collecting cmd (q :: todo) seed) :
      Step H c { c with
        localState := update c.localState p (.collecting cmd todo (best obj seed (c.slots q))) }
  /-- Line 6 is done; the loop body starts with the collect of `M` (Line 10),
  which reads the `n` registers in any order `order`. -/
  | collectedStart (c) (p : Fin n) cmd seed (h : c.localState p = .collecting cmd [] seed)
      (order : List (Fin n)) (horder : order.Perm (List.finRange n)) :
      Step H c { c with
        localState := update c.localState p (.gathering cmd seed order []) }
  /-- Line 10: one read of `M[q]`. -/
  | readAnnouncement (c) (p q : Fin n) cmd seed todo commands
      (h : c.localState p = .gathering cmd seed (q :: todo) commands) :
      Step H c { c with
        localState := update c.localState p
          (.gathering cmd seed todo (observe obj seed (c.announcements q) commands)) }
  /-- Lines 9, 11 and 12: the base trace extended by `trace(M_i)` — the missing
  announcements the collect found, `commands`, arranged in any order `arranged`
  — goes to round `r + 1`; the environment's input must match. -/
  | propose (c) (p : Fin n) cmd seed commands
      (h : c.localState p = .gathering cmd seed [] commands)
      (arranged : List (Cmd n Op)) (harr : arranged.Perm commands)
      (hi : (H (seed.round + 1)).input p = some (proposal obj seed arranged)) :
      Step H c { c with
        localState := update c.localState p (.waiting cmd (seed.round + 1) (proposal obj seed arranged))
        calls := ⟨seed.round + 1, p, proposal obj seed arranged⟩ :: c.calls }
  /-- Line 12 returns `(s, flag)`, the new local `(r, s)`: on a commit `S[i]` is
  written next (Line 14); either way the collect of Line 16 follows — at once on
  an adopt, reading the registers of `S` in any order `order`. -/
  | receive (c) (p : Fin n) cmd r proposal s flag
      (h : c.localState p = .waiting cmd r proposal)
      (ho : (H r).output p = some (s, flag))
      (order : List (Fin n)) (horder : order.Perm (List.finRange n)) :
      Step H c { c with
        localState := update c.localState p
          (if flag = true then .publishing cmd ⟨r, s⟩
            else .checking cmd ⟨r, s⟩ order (zeroSeed obj)) }
  /-- Line 14: `S[i] ← (r, s)`; the collect of Line 16 starts, reading the
  registers of `S` in any order `order`. -/
  | publish (c) (p : Fin n) cmd seed (h : c.localState p = .publishing cmd seed)
      (order : List (Fin n)) (horder : order.Perm (List.finRange n)) :
      Step H c { c with
        slots := update c.slots p seed
        localState := update c.localState p (.checking cmd seed order (zeroSeed obj)) }
  /-- Line 16: one read of `S[q]`, keeping the value of higher round. -/
  | readCheck (c) (p q : Fin n) cmd seed todo seen
      (h : c.localState p = .checking cmd seed (q :: todo) seen) :
      Step H c { c with
        localState := update c.localState p (.checking cmd seed todo (best obj seen (c.slots q))) }
  /-- Line 8: `cmd` does not occur in `u`, so the loop runs again, starting
  with a collect of `M` (Line 10) in any order `order`. -/
  | retry (c) (p : Fin n) cmd seed seen (h : c.localState p = .checking cmd seed [] seen)
      (hmissing : (Tagged obj).traceCount cmd seen.trace = 0)
      (order : List (Fin n)) (horder : order.Perm (List.finRange n)) :
      Step H c { c with
        localState := update c.localState p (.gathering cmd seed order []) }
  /-- Line 8: `cmd` occurs in `u`; the operation returns `ret*(cmd, u)`
  (Line 19), and its response is recorded. -/
  | finish (c) (p : Fin n) cmd seed seen (h : c.localState p = .checking cmd seed [] seen)
      (hcontains : 0 < (Tagged obj).traceCount cmd seen.trace) :
      Step H c { c with
        localState := update c.localState p (.idle seed)
        returns := ⟨cmd, seen.round, seen.trace⟩ :: c.returns }

/-- The configurations reachable from `initial`. -/
inductive Reachable (H : Environment (n := n) obj) : Configuration (n := n) obj → Prop where
  | initial : Reachable H (initial obj)
  | step {c d} : Reachable H c → Step obj H c d → Reachable H d

/-- What each position guarantees about the seeds and traces it holds. -/
def LocalInvariant (H : Environment (n := n) obj) : Local (n := n) obj → Prop
  | .idle s => Supported obj H s
  | .announcing _ s => Supported obj H s
  | .collecting _ _ s => Supported obj H s
  | .gathering _ s _ _ => Supported obj H s
  | .waiting _ r _ => 0 < r
  | .publishing _ s => Committed obj H s.round s.trace
  | .checking _ s _ seen => Supported obj H s ∧ Stored obj H seen

/-- The configuration invariant of Algorithm 3, true in every reachable
configuration (`invariant`). -/
structure Invariant (H : Environment (n := n) obj) (c : Configuration (n := n) obj) : Prop where
  slots : ∀ p, Stored obj H (c.slots p)
  localState : ∀ p, LocalInvariant obj H (c.localState p)
  calls : ∀ call ∈ c.calls, CallInvariant obj H call
  returns : ∀ ret ∈ c.returns, Committed obj H ret.round ret.trace ∧
    0 < (Tagged obj).traceCount ret.command ret.trace

theorem invariant_initial (H : Environment (n := n) obj) : Invariant obj H (initial obj) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p; exact Or.inl ⟨rfl, rfl⟩
  · intro p; exact Or.inl ⟨rfl, rfl⟩
  · intro call h; cases h
  · intro ret h; cases h

omit [DecidableEq Op] in
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
  | readStart p q cmd todo seed h =>
    refine ⟨hc.slots, local_update obj hc.localState p _ ?_, hc.calls, hc.returns⟩
    have hseed := hc.localState p
    rw [h] at hseed
    change Supported obj H (best obj seed (c.slots q))
    unfold best
    split
    · exact WeakUniversal.stored_supported obj (hc.slots q)
    · exact hseed
  | invoke p _ _ h | announce p _ _ h | collectedStart p _ _ h | readAnnouncement p _ _ _ _ _ h =>
    refine ⟨hc.slots, local_update obj hc.localState p _ ?_, hc.calls, hc.returns⟩
    simpa only [h, LocalInvariant] using hc.localState p
  | propose p cmd seed commands h arranged harr hi =>
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
        refine ⟨q, seed.trace, flag, ?_, proposal_extends obj seed arranged⟩
        simpa only [he] using hq
    · exact hc.calls call hcall
  | receive p cmd r proposal s flag h ho =>
    have hpos : 0 < r := by simpa only [h, LocalInvariant] using hc.localState p
    refine ⟨hc.slots, local_update obj hc.localState p _ ?_, hc.calls, hc.returns⟩
    split
    · rename_i he
      exact ⟨hpos, p, he ▸ ho⟩
    · exact ⟨Or.inr ⟨hpos, p, flag, ho⟩, Or.inl ⟨rfl, rfl⟩⟩
  | publish p cmd seed h =>
    have hp := hc.localState p
    rw [h] at hp
    refine ⟨?_, local_update obj hc.localState p _ ?_, hc.calls, hc.returns⟩
    · intro q
      change Stored obj H (update c.slots p seed q)
      unfold update
      split
      · exact Or.inr hp
      · exact hc.slots q
    · exact ⟨WeakUniversal.stored_supported obj (Or.inr hp), Or.inl ⟨rfl, rfl⟩⟩
  | readCheck p q cmd seed todo seen h =>
    have hp := hc.localState p
    rw [h] at hp
    refine ⟨hc.slots, local_update obj hc.localState p _ ⟨hp.1, ?_⟩, hc.calls, hc.returns⟩
    change Stored obj H (best obj seen (c.slots q))
    unfold best
    split
    · exact hc.slots q
    · exact hp.2
  | retry p cmd seed seen h hmissing =>
    have hp := hc.localState p
    rw [h] at hp
    exact ⟨hc.slots, local_update obj hc.localState p _ hp.1, hc.calls, hc.returns⟩
  | finish p cmd seed seen h hcontains =>
    have hp := hc.localState p
    rw [h] at hp
    refine ⟨hc.slots, local_update obj hc.localState p _ hp.1, hc.calls, ?_⟩
    intro ret hret
    rcases List.mem_cons.mp hret with rfl | hret
    · refine ⟨?_, hcontains⟩
      rcases hp.2 with ⟨_, he⟩ | hc
      · rw [he] at hcontains
        change 0 < 0 at hcontains
        omega
      · exact hc
    · exact hc.returns ret hret

theorem invariant {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : Invariant obj H c := by
  induction hc with
  | initial => exact invariant_initial obj H
  | step _ hs ih => exact invariant_step obj ih hs

/-- Algorithm 3's `WeakUniversal.CallsCovered`: every environment input was
called by some reachable configuration. -/
def CallsCovered (H : Environment (n := n) obj) : Prop :=
  ∀ r p s, (H (r + 1)).input p = some s →
    ∃ c, Reachable obj H c ∧ (⟨r + 1, p, s⟩ : Call obj) ∈ c.calls

/-- Algorithm 3's `WeakUniversal.roundExecution`: its transitions establish the
predecessor linkage of `RoundExecution`. -/
def roundExecution (H : Environment (n := n) obj) (coverage : CallsCovered obj H) :
    GCA.RoundExecution (Tagged (n := n) obj) (Fin n) where
  round := fun r => H (r + 1)
  predecessor := by
    intro r p s hs
    obtain ⟨c, hc, hcall⟩ := coverage (r + 1) p s hs
    exact (invariant obj hc).calls _ hcall r rfl

/-- The prefix-rounds safety lemma also holds for the helping construction. -/
theorem committed_prefix {H : Environment (n := n) obj} (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) {r k : Nat} (hrk : r ≤ k)
    {p q : Fin n} {s t : (Tagged (n := n) obj).Trace} {flag : Bool}
    (hs : (H (r + 1)).output p = some (s, true))
    (ht : (H (k + 1)).output q = some (t, flag)) : (Tagged obj).TracePrefix s t :=
  (roundExecution obj H coverage).commit_below_later_output spec hrk hs ht

/-- An interleaved run of Algorithm 3, permitting idle scheduler steps. -/
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

/-- All response traces are comparable, including responses obtained by helping. -/
theorem return_traces_comparable {H : Environment (n := n) obj} (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) {a b : Return (n := n) obj} (ha : a ∈ c.returns) (hb : b ∈ c.returns) :
    (Tagged obj).TracePrefix a.trace b.trace ∨ (Tagged obj).TracePrefix b.trace a.trace := by
  obtain ⟨hra, p, hp⟩ := ((invariant obj hc).returns a ha).1
  obtain ⟨hrb, q, hq⟩ := ((invariant obj hc).returns b hb).1
  cases har : a.round with
  | zero => omega
  | succ r =>
    cases hbr : b.round with
    | zero => omega
    | succ k =>
      rw [har] at hp
      rw [hbr] at hq
      exact (roundExecution obj H coverage).commits_comparable spec hp hq

theorem response_defined {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) {ret : Return (n := n) obj} (hr : ret ∈ c.returns) :
    ∃ v, WeakUniversal.response obj ret = some v :=
  (Tagged obj).traceReturn_defined ret.trace ret.command 0 ((invariant obj hc).returns ret hr).2

end ConflictFreedom.HelpingUniversal
