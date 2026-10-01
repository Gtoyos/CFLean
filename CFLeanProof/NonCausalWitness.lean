import CFLeanProof.CausalLinearization
import CFLeanProof.UniversalEventLinearization
import CFLeanProof.InfiniteHistory

/-! # The whole-run reading of the GCA properties is too weak for Algorithm 3

The manuscript requires the six GCA properties for every execution, hence for
every finite prefix of one.  The constructions' model checks them only on the
whole-run table `H` (`(H r).Specification`).  That reading is strictly weaker:
Validity of a prefix ending with a receive says the received output contains
only commands already proposed, and the whole-run table cannot see this.
`CausalLinearization` therefore states the prefix instance separately
(`Execution.CausalGCA`, implied by `causalGCA_of_prefixValidity`).  This module
shows it cannot be omitted for Algorithm 3.

`run` is a run of Algorithm 3 with three processes over a counter.  Its GCA
table satisfies all six properties as a whole-run history, and its every input
is a proposal this very run makes (`run.Covers`), yet the run is not
linearizable: process `1` reads `1` before the only increment is even invoked.
Process `1`'s round-1 output already contains the increment of process `0`,
whose sole source is the round-1 proposal of a slow helper, process `2`: it
collected `S` before anything was published, and gathered the announcements
only after process `0` announced its increment.  In the prefix that ends with
process `1`'s receive, no input contains the increment, so the table is **not**
a GCA history in the manuscript's sense (`validity_fails_at_output`): the
manuscript's specification excludes it, the whole-run reading does not.

The run is built by `Act`/`apply`, a deterministic executor of Algorithm 3's
transitions, so that each step is checked by computation rather than by a
hand-written configuration.
-/
namespace ConflictFreedom.NonCausalWitness
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best)
open HelpingUniversal (Configuration Local Step proposal observe)

/-! ## An executor for Algorithm 3's transitions -/

section Machine
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

/-- A transition of Algorithm 3, by kind and acting process. -/
inductive Act (n : Nat) (Op : Type) where
  | invoke (p : Fin n) (op : Op)
  | announce (p : Fin n)
  | readStart (p : Fin n)
  | collectedStart (p : Fin n)
  | readAnnouncement (p : Fin n)
  | propose (p : Fin n)
  | receive (p : Fin n)
  | publish (p : Fin n)
  | readCheck (p : Fin n)
  | finish (p : Fin n)

/-- The configuration a transition leads to; a disabled transition changes
nothing.  Each branch is the target of the corresponding `Step` constructor. -/
def apply (H : Environment (n := n) obj) (c : Configuration (n := n) obj) :
    Act n Op → Configuration (n := n) obj
  | .invoke p op =>
    match c.localState p with
    | .idle seed => { c with
        sequence := update c.sequence p (c.sequence p + 1)
        invocations := ⟨op, p, c.sequence p + 1⟩ :: c.invocations
        localState := update c.localState p (.announcing ⟨op, p, c.sequence p + 1⟩ seed) }
    | _ => c
  | .announce p =>
    match c.localState p with
    | .announcing cmd seed => { c with
        announcements := update c.announcements p (some cmd)
        localState := update c.localState p (.collecting cmd (List.finRange n) seed) }
    | _ => c
  | .readStart p =>
    match c.localState p with
    | .collecting cmd (q :: todo) seed => { c with
        localState := update c.localState p (.collecting cmd todo (best obj seed (c.slots q))) }
    | _ => c
  | .collectedStart p =>
    match c.localState p with
    | .collecting cmd [] seed => { c with
        localState := update c.localState p (.gathering cmd seed (List.finRange n) []) }
    | _ => c
  | .readAnnouncement p =>
    match c.localState p with
    | .gathering cmd seed (q :: todo) commands => { c with
        localState := update c.localState p
          (.gathering cmd seed todo (observe obj seed (c.announcements q) commands)) }
    | _ => c
  | .propose p =>
    match c.localState p with
    | .gathering cmd seed [] commands => { c with
        localState := update c.localState p
          (.waiting cmd (seed.round + 1) (proposal obj seed commands))
        calls := ⟨seed.round + 1, p, proposal obj seed commands⟩ :: c.calls }
    | _ => c
  | .receive p =>
    match c.localState p with
    | .waiting cmd r _ =>
      match (H r).output p with
      | some (s, flag) => { c with
          localState := update c.localState p
            (if flag = true then .publishing cmd ⟨r, s⟩
              else .checking cmd ⟨r, s⟩ (List.finRange n) (zeroSeed obj)) }
      | none => c
    | _ => c
  | .publish p =>
    match c.localState p with
    | .publishing cmd seed => { c with
        slots := update c.slots p seed
        localState := update c.localState p (.checking cmd seed (List.finRange n) (zeroSeed obj)) }
    | _ => c
  | .readCheck p =>
    match c.localState p with
    | .checking cmd seed (q :: todo) seen => { c with
        localState := update c.localState p (.checking cmd seed todo (best obj seen (c.slots q))) }
    | _ => c
  | .finish p =>
    match c.localState p with
    | .checking cmd seed [] seen => { c with
        localState := update c.localState p (.idle seed)
        returns := ⟨cmd, seen.round, seen.trace⟩ :: c.returns }
    | _ => c

variable {obj} {H : Environment (n := n) obj} {c : Configuration (n := n) obj} {p : Fin n}

theorem step_invoke {op : Op} {seed : Seed (n := n) obj} (h : c.localState p = .idle seed) :
    Step obj H c (apply obj H c (.invoke p op)) := by
  simp only [apply, h]; exact Step.invoke c p op seed h

theorem step_announce {cmd : Cmd n Op} {seed : Seed (n := n) obj}
    (h : c.localState p = .announcing cmd seed) :
    Step obj H c (apply obj H c (.announce p)) := by
  simp only [apply, h]; exact Step.announce c p cmd seed h (List.finRange n) (List.Perm.refl _)

theorem step_readStart {cmd : Cmd n Op} {q : Fin n} {todo : List (Fin n)}
    {seed : Seed (n := n) obj} (h : c.localState p = .collecting cmd (q :: todo) seed) :
    Step obj H c (apply obj H c (.readStart p)) := by
  simp only [apply, h]; exact Step.readStart c p q cmd todo seed h

theorem step_collectedStart {cmd : Cmd n Op} {seed : Seed (n := n) obj}
    (h : c.localState p = .collecting cmd [] seed) :
    Step obj H c (apply obj H c (.collectedStart p)) := by
  simp only [apply, h]; exact Step.collectedStart c p cmd seed h (List.finRange n) (List.Perm.refl _)

theorem step_readAnnouncement {cmd : Cmd n Op} {seed : Seed (n := n) obj} {q : Fin n}
    {todo : List (Fin n)} {commands : List (Cmd n Op)}
    (h : c.localState p = .gathering cmd seed (q :: todo) commands) :
    Step obj H c (apply obj H c (.readAnnouncement p)) := by
  simp only [apply, h]; exact Step.readAnnouncement c p q cmd seed todo commands h

theorem step_propose {cmd : Cmd n Op} {seed : Seed (n := n) obj} {commands : List (Cmd n Op)}
    (h : c.localState p = .gathering cmd seed [] commands)
    (hi : (H (seed.round + 1)).input p = some (proposal obj seed commands)) :
    Step obj H c (apply obj H c (.propose p)) := by
  simp only [apply, h]; exact Step.propose c p cmd seed commands h commands (List.Perm.refl _) hi

theorem step_receive {cmd : Cmd n Op} {r : Nat} {prop s : (Tagged (n := n) obj).Trace}
    {flag : Bool} (h : c.localState p = .waiting cmd r prop) (ho : (H r).output p = some (s, flag)) :
    Step obj H c (apply obj H c (.receive p)) := by
  simp only [apply, h, ho]; exact Step.receive c p cmd r prop s flag h ho (List.finRange n)
    (List.Perm.refl _)

theorem step_publish {cmd : Cmd n Op} {seed : Seed (n := n) obj}
    (h : c.localState p = .publishing cmd seed) :
    Step obj H c (apply obj H c (.publish p)) := by
  simp only [apply, h]; exact Step.publish c p cmd seed h (List.finRange n) (List.Perm.refl _)

theorem step_readCheck {cmd : Cmd n Op} {seed : Seed (n := n) obj} {q : Fin n}
    {todo : List (Fin n)} {seen : Seed (n := n) obj}
    (h : c.localState p = .checking cmd seed (q :: todo) seen) :
    Step obj H c (apply obj H c (.readCheck p)) := by
  simp only [apply, h]; exact Step.readCheck c p q cmd seed todo seen h

theorem step_finish {cmd : Cmd n Op} {seed seen : Seed (n := n) obj}
    (h : c.localState p = .checking cmd seed [] seen)
    (hc : 0 < (Tagged obj).traceCount cmd seen.trace) :
    Step obj H c (apply obj H c (.finish p)) := by
  simp only [apply, h]; exact Step.finish c p cmd seed seen h hc

end Machine

/-! ## The counter, the GCA history and the run -/

/-- The operations of a counter. -/
inductive CounterOp where
  | inc
  | read
  deriving DecidableEq

/-- A counter: `inc` adds one and answers `0`; `read` answers the value. -/
def counter : Object Nat CounterOp Nat where
  initial := 0
  step op q := match op with
    | .inc => (0, q + 1)
    | .read => (q, q)

/-- The increment of process `0`, and the reads of processes `1` and `2`. -/
def cb : Cmd 3 CounterOp := ⟨.inc, 0, 1⟩
def ca : Cmd 3 CounterOp := ⟨.read, 1, 1⟩
def cc : Cmd 3 CounterOp := ⟨.read, 2, 1⟩

/-- Process `1`'s round-1 proposal. -/
def PR : (Tagged (n := 3) counter).Trace := proposal counter (zeroSeed counter) [ca, cc]

/-- The slow helper's round-1 proposal, which carries the increment. -/
def PH : (Tagged (n := 3) counter).Trace := proposal counter (zeroSeed counter) [cb, ca, cc]

/-- GCA round 1: inputs `PR` (process `1`) and `PH` (process `2`), and process
`1` receives the committed output `PH` — before `PH` is proposed. -/
def round1 : GCA.History (Tagged (n := 3) counter) (Fin 3) where
  input := fun p => if p = 1 then some PR else if p = 2 then some PH else none
  output := fun p => if p = 1 then some (PH, true) else none
  returned_invoked := by
    intro p t c h
    by_cases hp : p = 1
    · exact ⟨PR, by simp [hp]⟩
    · simp [hp] at h

/-- Every other round is silent. -/
def silent : GCA.History (Tagged (n := 3) counter) (Fin 3) where
  input := fun _ => none
  output := fun _ => none
  returned_invoked := by intro p t c h; cases h

def H : Environment (n := 3) counter := fun r => if r = 1 then round1 else silent

/-- The schedule. -/
def acts : List (Act 3 CounterOp) :=
  [ -- the helper starts, and collects `S` before anything is published
    .invoke 2 .read, .announce 2, .readStart 2, .readStart 2, .readStart 2, .collectedStart 2,
    -- process 1 runs a whole operation and reads the increment
    .invoke 1 .read, .announce 1, .readStart 1, .readStart 1, .readStart 1, .collectedStart 1,
    .readAnnouncement 1, .readAnnouncement 1, .readAnnouncement 1, .propose 1, .receive 1,
    .publish 1, .readCheck 1, .readCheck 1, .readCheck 1, .finish 1,
    -- only now is the increment invoked, and announced
    .invoke 0 .inc, .announce 0,
    -- the helper gathers the announcements, and proposes the increment to round 1
    .readAnnouncement 2, .readAnnouncement 2, .readAnnouncement 2, .propose 2 ]

/-- The configurations of the run: the schedule, then nothing. -/
def cfg : Nat → Configuration (n := 3) counter
  | 0 => HelpingUniversal.initial counter
  | t + 1 =>
    match acts[t]? with
    | some a => apply counter H (cfg t) a
    | none => cfg t

theorem cfg_succ {t : Nat} {a : Act 3 CounterOp} (h : acts[t]? = some a) :
    cfg (t + 1) = apply counter H (cfg t) a := by
  simp only [cfg, h]

theorem cfg_stop {t : Nat} (ht : 28 ≤ t) : cfg (t + 1) = cfg t := by
  have h : acts[t]? = none := List.getElem?_eq_none (by simp [acts]; omega)
  simp only [cfg, h]

theorem next_of {t : Nat} {a : Act 3 CounterOp} (ha : acts[t]? = some a)
    (hs : Step counter H (cfg t) (apply counter H (cfg t) a)) :
    Step counter H (cfg t) (cfg (t + 1)) := by
  rw [cfg_succ ha]; exact hs

/-- **The run.**  Every step is an Algorithm 3 transition over `H`. -/
def run : HelpingUniversal.Execution counter H where
  state := cfg
  initial_state := rfl
  next t := by
    rcases Nat.lt_or_ge t 28 with ht | ht
    · refine Or.inr ?_
      match t, ht with
      | 0, _ => exact next_of (t := 0) rfl (step_invoke (by rfl))
      | 1, _ => exact next_of (t := 1) rfl (step_announce (by rfl))
      | 2, _ => exact next_of (t := 2) rfl (step_readStart (by rfl))
      | 3, _ => exact next_of (t := 3) rfl (step_readStart (by rfl))
      | 4, _ => exact next_of (t := 4) rfl (step_readStart (by rfl))
      | 5, _ => exact next_of (t := 5) rfl (step_collectedStart (by rfl))
      | 6, _ => exact next_of (t := 6) rfl (step_invoke (by rfl))
      | 7, _ => exact next_of (t := 7) rfl (step_announce (by rfl))
      | 8, _ => exact next_of (t := 8) rfl (step_readStart (by rfl))
      | 9, _ => exact next_of (t := 9) rfl (step_readStart (by rfl))
      | 10, _ => exact next_of (t := 10) rfl (step_readStart (by rfl))
      | 11, _ => exact next_of (t := 11) rfl (step_collectedStart (by rfl))
      | 12, _ => exact next_of (t := 12) rfl (step_readAnnouncement (by rfl))
      | 13, _ => exact next_of (t := 13) rfl (step_readAnnouncement (by rfl))
      | 14, _ => exact next_of (t := 14) rfl (step_readAnnouncement (by rfl))
      | 15, _ => exact next_of (t := 15) rfl (step_propose (by rfl) (by rfl))
      | 16, _ => exact next_of (t := 16) rfl (step_receive (by rfl) (by rfl))
      | 17, _ => exact next_of (t := 17) rfl (step_publish (by rfl))
      | 18, _ => exact next_of (t := 18) rfl (step_readCheck (by rfl))
      | 19, _ => exact next_of (t := 19) rfl (step_readCheck (by rfl))
      | 20, _ => exact next_of (t := 20) rfl (step_readCheck (by rfl))
      | 21, _ => exact next_of (t := 21) rfl (step_finish (by rfl) (by decide))
      | 22, _ => exact next_of (t := 22) rfl (step_invoke (by rfl))
      | 23, _ => exact next_of (t := 23) rfl (step_announce (by rfl))
      | 24, _ => exact next_of (t := 24) rfl (step_readAnnouncement (by rfl))
      | 25, _ => exact next_of (t := 25) rfl (step_readAnnouncement (by rfl))
      | 26, _ => exact next_of (t := 26) rfl (step_readAnnouncement (by rfl))
      | 27, _ => exact next_of (t := 27) rfl (step_propose (by rfl) (by rfl))
      | t + 28, h => exact absurd h (by omega)
    · exact Or.inl (cfg_stop ht)

/-! ## As a whole-run history, the GCA table satisfies the six properties -/

theorem round1_output {p : Fin 3} {t : (Tagged (n := 3) counter).Trace} {c : Bool}
    (h : round1.output p = some (t, c)) : p = 1 ∧ t = PH ∧ c = true := by
  by_cases hp : p = 1
  · subst hp
    simp only [round1, ite_true, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨rfl, h.1.symm, h.2.symm⟩
  · simp [round1, hp] at h

theorem round1_spec : round1.Specification where
  validity := by
    intro p t c h a ha
    obtain ⟨_, rfl, _⟩ := round1_output h
    exact ⟨PH, ⟨2, rfl⟩, Nat.le_refl _⟩
  adoption := by
    intro p t h q u c h'
    obtain ⟨_, rfl, _⟩ := round1_output h
    obtain ⟨_, rfl, _⟩ := round1_output h'
    exact (Tagged (n := 3) counter).tracePrefix_refl _
  commitment := by
    intro _ _ hall
    obtain ⟨t, c, h⟩ := hall 2 PH rfl
    exact absurd (round1_output h).1 (by decide)
  convergence := ⟨PH, fun s ⟨p, c, h⟩ => by
    obtain ⟨_, rfl, _⟩ := round1_output h
    exact (Tagged (n := 3) counter).tracePrefix_refl _⟩
  commonPrefix := by
    intro l hl t ⟨p, c, h⟩
    obtain ⟨_, rfl, _⟩ := round1_output h
    exact hl PH ⟨2, rfl⟩
  weakAgreement := fun _ p t c h => (round1_output h).2.2

theorem silent_spec : silent.Specification where
  validity := by intro p t c h; cases h
  adoption := by intro p t h; cases h
  commitment := by intro ⟨s, p, h⟩; cases h
  convergence := ⟨(Tagged (n := 3) counter).emptyTrace, fun s ⟨p, c, h⟩ => by cases h⟩
  commonPrefix := by intro l _ t ⟨p, c, h⟩; cases h
  weakAgreement := by intro _ p t c h; cases h

/-- **All six properties of §4.2 hold of every round's whole-run history.** -/
theorem H_spec : ∀ r, (H (r + 1)).Specification := by
  intro r
  by_cases hr : r = 0
  · subst hr; exact round1_spec
  · have : H (r + 1) = silent := by simp [H, hr]
    rw [this]; exact silent_spec

/-- **Every input is a proposal of this very run**: the GCA history is the
run's own. -/
theorem run_covers : run.Covers counter := by
  intro r p s hs
  by_cases hr : r = 0
  · subst hr
    change round1.input p = some s at hs
    by_cases hp1 : p = 1
    · subst hp1
      have hs' : s = PR := by simp [round1] at hs; exact hs.symm
      subst hs'
      refine ⟨16, ?_⟩
      show _ ∈ (cfg 16).calls
      rw [show (cfg 16).calls = [⟨1, 1, PR⟩] from rfl]
      exact List.mem_singleton_self _
    · by_cases hp2 : p = 2
      · subst hp2
        have hs' : s = PH := by simp [round1] at hs; exact hs.symm
        subst hs'
        refine ⟨28, ?_⟩
        show _ ∈ (cfg 28).calls
        rw [show (cfg 28).calls = [⟨1, 2, PH⟩, ⟨1, 1, PR⟩] from rfl]
        exact List.mem_cons_self ..
      · simp [round1, hp1, hp2] at hs
  · have : H (r + 1) = silent := by simp [H, hr]
    rw [this] at hs
    cases hs

/-! ## What goes wrong -/

theorem cfg22_returns : (cfg 22).returns = [⟨ca, 1, PH⟩] := rfl
theorem cfg22_invocations : (cfg 22).invocations = [ca, cc] := rfl

/-- The operation of process `1` returns `1`. -/
theorem returns_one : (run.history counter).returned 22 ca 1 :=
  ⟨⟨ca, 1, PH⟩, by show _ ∈ (cfg 22).returns; rw [cfg22_returns]; exact List.mem_singleton_self _,
    rfl, rfl⟩

/-- **The GCA table is not causal**: process `1` receives the increment
before anyone has proposed it. -/
theorem not_causal : ¬ run.CausalGCA counter := by
  intro h
  have h16 : (cfg 16).localState 1 = .waiting ca 1 PR := rfl
  have h17 : (cfg 17).localState 1 = .publishing ca ⟨1, PH⟩ := rfl
  obtain ⟨call, hcall, _, hcount⟩ := h 16 1 ca 1 PR PH true h16
    (by show (cfg 17).localState 1 ≠ (cfg 16).localState 1; rw [h16, h17]; simp)
    rfl cb (by decide)
  change call ∈ (cfg 16).calls at hcall
  rw [show (cfg 16).calls = [⟨1, 1, PR⟩] from rfl, List.mem_singleton] at hcall
  subst hcall
  exact absurd hcount (by decide)

/-- **A returned trace contains an operation not yet invoked.** -/
theorem not_returnsInvokedBy : ¬ run.ReturnsInvokedBy counter := by
  intro h
  have hb := h 22 ⟨ca, 1, PH⟩
    (by show _ ∈ (cfg 22).returns; rw [cfg22_returns]; exact List.mem_singleton_self _)
    cb (by decide)
  change cb ∈ (cfg 22).invocations at hb
  rw [cfg22_invocations] at hb
  simp [cb, ca, cc] at hb

/-- A schedule of reads leaves the counter where it was. -/
theorem reads_finalState : ∀ (l : List (Cmd 3 CounterOp)), (∀ c ∈ l, c.operation = .read) →
    ∀ q, (Tagged (n := 3) counter).finalState l q = q
  | [], _, _ => rfl
  | c :: l, h, q => by
    have hc := h c (List.mem_cons_self ..)
    have hq : ((Tagged (n := 3) counter).step c q).2 = q := by
      show (counter.step c.operation q).2 = q
      rw [hc]; rfl
    show (Tagged (n := 3) counter).finalState l ((Tagged (n := 3) counter).step c q).2 = q
    rw [hq]
    exact reads_finalState l (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) q

/-- Every operation invoked by boundary `22` is a read. -/
theorem invoked_read {c : Cmd 3 CounterOp} (hc : c ∈ (cfg 22).invocations) :
    c.operation = .read := by
  rw [cfg22_invocations] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> rfl

/-- **Not linearizable**, in the boundary form the lower-level theorems conclude:
a legal sequential order of the operations invoked by boundary `22` reads `0`,
while the run read `1`. -/
theorem not_linearizable :
    ¬ ∃ x, (Tagged (n := 3) counter).Linearizes (run.history counter) 22 x := by
  rintro ⟨x, hx⟩
  obtain ⟨_, hv⟩ := hx.completed ca 1 returns_one
  have h0 : (Tagged (n := 3) counter).sequentialResponse x ca = 0 := by
    unfold Object.sequentialResponse
    rw [reads_finalState _ (fun c hc => invoked_read (hx.invoked c (List.mem_of_mem_take hc)))]
    rfl
  rw [h0] at hv
  exact absurd hv (by decide)

/-- **Not linearizable, in the manuscript's own definition**: no completion of
the run's first `22` events matches a legal sequential history process by
process.  Any response assignment agreeing with the run is meant. -/
theorem not_eventLinearizable (resp : Cmd 3 CounterOp → Nat)
    (hresp : ∀ k a v, (run.history counter).returned k a v → v = resp a) :
    ¬ (Tagged (n := 3) counter).EventLinearizable Command.process
      ((run.ledgerRun counter).history resp 22) := by
  have hca : resp ca = 1 := (hresp 22 ca 1 returns_one).symm
  have hmemret : ca ∈ ((run.ledgerRun counter).state 22).returned := by
    show ca ∈ ((cfg 22).returns.map Return.command)
    rw [cfg22_returns]; exact List.mem_singleton_self _
  have hev : Event.respond ca 1 ∈ (run.ledgerRun counter).history resp 22 :=
    ((run.ledgerRun counter).responded_iff resp 22 ca 1).mpr ⟨hmemret, hca.symm⟩
  rintro ⟨hbar, x, ⟨keep, ext, rfl, hdrop, _⟩, hproj, _⟩
  have hkeep : keep ca = true := by
    cases hk : keep ca with
    | true => rfl
    | false =>
      exfalso
      have hinv : History.Invoked ((run.ledgerRun counter).history resp 22) ca :=
        ((run.ledgerRun counter).invoked_iff resp 22 ca).mpr (by
          show ca ∈ (cfg 22).invocations
          rw [cfg22_invocations]; exact List.mem_cons_self ..)
      exact (hdrop ca hinv hk).2 ⟨1, hev⟩
  -- The completion keeps the response `1` of process 1 …
  have hmem : Event.respond ca 1 ∈ History.project Command.process 1
      (((run.ledgerRun counter).history resp 22).filter (fun e => keep e.op) ++
        ext.map (fun p => Event.respond p.1 p.2)) :=
    List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_filter.mpr ⟨hev, hkeep⟩), by decide⟩
  rw [hproj 1] at hmem
  have hseq : Event.respond ca 1 ∈ (Tagged (n := 3) counter).sequentialEvents x :=
    (List.mem_filter.mp hmem).1
  -- … while the sequential history executes only invoked reads …
  have hreads : ∀ c ∈ x, c.operation = .read := by
    intro c hc
    have hinv : Event.invoke c ∈ History.project Command.process c.process
        ((Tagged (n := 3) counter).sequentialEvents x) := by
      refine List.mem_filter.mpr ⟨?_, by simp⟩
      rw [← History.mem_invocations, Object.invocations_sequentialEvents]
      exact hc
    rw [← hproj c.process] at hinv
    rcases List.mem_append.mp (List.mem_filter.mp hinv).1 with h1 | h2
    · exact invoked_read (((run.ledgerRun counter).invoked_iff resp 22 c).mp
        (List.mem_filter.mp h1).1)
    · obtain ⟨_, _, hp⟩ := List.mem_map.mp h2
      cases hp
  -- … so every response it gives is `0`.
  have hzero : ∀ a v, Event.respond a v ∈ (Tagged (n := 3) counter).sequentialEvents x →
      v = 0 := by
    intro a v hav
    simp only [Object.sequentialEvents, History.alternating, List.append_nil,
      List.mem_flatMap] at hav
    obtain ⟨⟨a', v'⟩, hmem', hin⟩ := hav
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      Event.respond.injEq] at hin
    obtain ⟨rfl, rfl⟩ := hin
    obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hmem'
    have hlen : i < x.length := by simpa [Object.sequentialHistory] using hi
    have hv : v = ((Tagged (n := 3) counter).step x[i]
        ((Tagged (n := 3) counter).finalState (x.take i) 0)).1 := (congrArg Prod.snd he).symm
    rw [hv, reads_finalState _ (fun c hc => hreads c (List.mem_of_mem_take hc))]
    show (counter.step x[i].operation 0).1 = 0
    cases x[i].operation <;> rfl
  exact absurd (hzero ca 1 hseq) (by decide)

/-- **The table is not a GCA history in the manuscript's sense.**  The
manuscript requires the six properties of every execution.  In the prefix that
ends just after process `1`'s receive, its output holds the increment, and no
proposal made so far contains it: Validity fails. -/
theorem validity_fails_at_output : ¬ (run.prefixHistory counter 1 17).Validity := by
  intro hv
  have h16 : (cfg 16).localState 1 = .waiting ca 1 PR := rfl
  have h17 : (cfg 17).localState 1 = .publishing ca ⟨1, PH⟩ := rfl
  have hout : (run.prefixHistory counter 1 17).output 1 = some (PH, true) := by
    unfold HelpingUniversal.Execution.prefixHistory
    dsimp only
    rw [ite_eq_left ⟨16, by omega, ca, PR, h16,
      by show (cfg 17).localState 1 ≠ (cfg 16).localState 1; rw [h16, h17]; simp⟩]
    rfl
  obtain ⟨s', ⟨q, hq⟩, hocc⟩ := hv.occurs 1 PH true hout cb 0 (by unfold GCA.History.Occurs; decide)
  unfold HelpingUniversal.Execution.prefixHistory at hq
  dsimp only at hq
  by_cases hin : ∃ call ∈ (run.state 17).calls, call.round = 1 ∧ call.process = q
  · rw [ite_eq_left hin] at hq
    obtain ⟨call, hcall, _, hproc⟩ := hin
    change call ∈ (cfg 17).calls at hcall
    rw [show (cfg 17).calls = [⟨1, 1, PR⟩] from rfl, List.mem_singleton] at hcall
    subst hcall
    subst hproc
    change round1.input 1 = some s' at hq
    have hs' : s' = PR := by simp [round1] at hq; exact hq.symm
    subst hs'
    exact absurd hocc (by unfold GCA.History.Occurs; decide)
  · rw [ite_eq_right hin] at hq; cases hq

/-- **The whole-run reading of the six GCA properties does not make Algorithm 3
linearizable.**  Over a GCA table satisfying all six properties as a whole-run
history, whose inputs are all proposals of the run itself, a run of Algorithm 3
returns a value no linearization explains.  The manuscript's own specification
rules the table out — Validity fails on a prefix — and with the prefix instance
of Validity, `Execution.spec_finite_linearization` applies. -/
theorem whole_history_spec_not_enough :
    (∀ r, (H (r + 1)).Specification) ∧ run.Covers counter ∧
      ¬ (run.prefixHistory counter 1 17).Validity ∧ ¬ run.CausalGCA counter ∧
      ¬ (∃ x, (Tagged (n := 3) counter).Linearizes (run.history counter) 22 x) ∧
      ∀ resp : Cmd 3 CounterOp → Nat,
        (∀ k a v, (run.history counter).returned k a v → v = resp a) →
        ¬ (Tagged (n := 3) counter).EventLinearizable Command.process
          ((run.ledgerRun counter).history resp 22) :=
  ⟨H_spec, run_covers, validity_fails_at_output, not_causal, not_linearizable,
    not_eventLinearizable⟩

end ConflictFreedom.NonCausalWitness
