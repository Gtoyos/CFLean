import CFLeanProof.HelpingProgress
import CFLeanProof.WeakConflictFreedom

/-!
# Invariant (I) for Algorithm 3 (Lemma `UCV2isCF`)

This is the Algorithm 3 counterpart of `WeakConflictFreedom.lean`.  The paper's
invariant is the same sentence:

> (I) for any `r > r_0` only compatible traces are proposed to `GCA_r`.

and its proof is the same except for the shape of a proposal.  Algorithm 1
appends at most the caller's own command (lines 7–8); Algorithm 3 appends
`trace(M_j)`, the announced commands that are missing from the adopted trace
(lines 10–11).  So the residual of a proposal over the greatest common prefix
`t` of the traces retrieved from the previous round (`Retrieved`) is

* the part `u_j` of the adopted trace above the common prefix, and
* the helping list `m_j`,

and the paper argues that both consist of commands of pending operations:
`u_j` because a returned command lies in a committed trace, which by
`lemma:prefix-rounds` prefixes the common prefix; and `m_j` "according to
Line 10", that is, because the `M` collect skips commands that already occur in
the adopted trace.

`CallShape` is the inductive invariant that makes this precise.  The helping
list a process assembles

* contains only commands that are *absent* from its adopted trace,
* contains only commands that were *really invoked*, and
* is *duplicate-free*, because the `M` collect visits each register once and a
  register holds a command tagged with its own owner.

The third point is what makes occurrence uniqueness go through for Algorithm 3:
`output_count_le_one` is a theorem here, not a hypothesis, exactly as it is for
Algorithm 1.
-/

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best
  Supported Committed Stored CallInvariant)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op]

theorem count_le_one_of_nodup {α : Type} [DecidableEq α] :
    ∀ {l : List α}, l.Nodup → ∀ a : α, l.count a ≤ 1 := by
  intro l
  induction l with
  | nil => intro _ a; simp
  | cons b l ih =>
      intro h a
      rcases List.nodup_cons.mp h with ⟨hb, hl⟩
      by_cases he : a = b
      · subst he
        have hz : l.count a = 0 := List.count_eq_zero.mpr hb
        simp [hz]
      · have h1 := ih hl a
        simp only [List.count_cons]
        have hne : ¬ (b = a) := fun e => he e.symm
        simp [hne]
        omega

theorem observe_mem (base : Seed (n := n) obj) (x : Option (Cmd n Op))
    (commands : List (Cmd n Op)) (a : Cmd n Op)
    (h : a ∈ observe obj base x commands) :
    a ∈ commands ∨ (x = some a ∧ (Tagged obj).traceCount a base.trace = 0) := by
  cases x with
  | none => exact Or.inl h
  | some cmd =>
      by_cases hz : (Tagged obj).traceCount cmd base.trace = 0
      · simp only [observe, hz, ↓reduceIte] at h
        rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · have he : a = cmd := by simpa using h
          exact Or.inr ⟨by rw [he], by rw [he]; exact hz⟩
      · exact Or.inl (by simpa [observe, hz] using h)

theorem observe_nodup (base : Seed (n := n) obj) (x : Option (Cmd n Op))
    (commands : List (Cmd n Op)) (hnd : commands.Nodup)
    (hfresh : ∀ a, x = some a → a ∉ commands) :
    (observe obj base x commands).Nodup := by
  cases x with
  | none => exact hnd
  | some cmd =>
      by_cases hz : (Tagged obj).traceCount cmd base.trace = 0
      · have hn : cmd ∉ commands := hfresh cmd rfl
        simp only [observe, hz, ↓reduceIte]
        rw [List.nodup_append]
        refine ⟨hnd, by simp, ?_⟩
        intro y hy z hz2
        simp only [List.mem_singleton] at hz2
        subst hz2
        intro he
        subst he
        exact hn hy
      · simpa [observe, hz] using hnd

theorem observe_fresh (base : Seed (n := n) obj) (x : Option (Cmd n Op))
    (commands : List (Cmd n Op)) (q' : Fin n) (todo : List (Fin n))
    (hproc : ∀ a, x = some a → a.process = q')
    (hcmds : ∀ a ∈ commands, a.process ∉ q' :: todo)
    (hq' : q' ∉ todo) :
    ∀ a ∈ observe obj base x commands, a.process ∉ todo := by
  intro a ha
  rcases observe_mem obj base x commands a ha with hm | ⟨hann, -⟩
  · intro hbad; exact hcmds a hm (List.mem_cons_of_mem _ hbad)
  · rw [hproc a hann]; exact hq'

/-- The announcement array is tagged by its owner: `M[q]` only ever holds a
command of process `q`. -/
theorem announcement_process {H : Environment (n := n) obj}
    {c : Configuration (n := n) obj} (hc : Reachable obj H c) :
    ∀ q a, c.announcements q = some a → a.process = q := by
  induction hc with
  | initial => intro q a h; simp [initial] at h
  | step hprev hs ih =>
      cases hs with
      | announce p cmd seed h =>
          intro q a hq
          by_cases he : q = p
          · subst he
            have hown : cmd.process = q :=
              ((identity_invariant obj hprev).active_tag q cmd
                (by simp [ledger, h, Local.command])).1
            have hac : cmd = a := by simpa [update] using hq
            rw [← hac]; exact hown
          · exact ih q a (by simpa [update, he] using hq)
      | _ => exact ih

/-- The payload of the helping collect: only invoked commands absent from the
adopted trace, with no duplicates, and each register visited at most once. -/
def GatherOK (c : Configuration (n := n) obj) (seed : Seed (n := n) obj)
    (todo : List (Fin n)) (commands : List (Cmd n Op)) : Prop :=
  (∀ a ∈ commands, (Tagged obj).traceCount a seed.trace = 0 ∧ a ∈ c.invocations) ∧
    todo.Nodup ∧ commands.Nodup ∧ (∀ a ∈ commands, a.process ∉ todo)

/-- **The shape of an Algorithm 3 proposal.** -/
structure CallShape (H : Environment (n := n) obj)
    (c : Configuration (n := n) obj) : Prop where
  gathering : ∀ p own seed todo commands,
    c.localState p = .gathering own seed todo commands →
    GatherOK obj c seed todo commands
  calls : ∀ call ∈ c.calls, ∃ seed commands, Supported obj H seed ∧
    (∀ a ∈ commands, (Tagged obj).traceCount a seed.trace = 0 ∧ a ∈ c.invocations) ∧
    commands.Nodup ∧
    call.round = seed.round + 1 ∧ call.trace = proposal obj seed commands

theorem callShape {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : CallShape obj H c := by
  induction hc with
  | initial =>
      constructor
      · intro p own seed todo commands h; simp [initial] at h
      · intro call h; cases h
  | step hprev hs ih =>
    cases hs with
    | invoke p op seed h =>
        constructor
        · intro q own base todo commands hq
          by_cases he : q = p
          · subst he; simp [update] at hq
          · obtain ⟨h1, h2, h3, h4⟩ := ih.gathering q own base todo commands
              (by simpa [update, he] using hq)
            exact ⟨fun a ha => ⟨(h1 a ha).1, List.mem_cons_of_mem _ (h1 a ha).2⟩, h2, h3, h4⟩
        · intro call hcall
          obtain ⟨base, commands, hsup, hall, hnd, hr, ht⟩ := ih.calls call hcall
          exact ⟨base, commands, hsup,
            fun a ha => ⟨(hall a ha).1, List.mem_cons_of_mem _ (hall a ha).2⟩, hnd, hr, ht⟩
    | readAnnouncement p q' cmd seed todo commands h =>
        constructor
        · intro q own base todo' commands' hq
          by_cases he : q = p
          · subst he
            simp only [update, ↓reduceIte] at hq
            injection hq with e1 e2 e3 e4
            subst e1; subst e2; subst e3; subst e4
            obtain ⟨h1, h2, h3, h4⟩ := ih.gathering q cmd seed (q' :: todo) commands h
            have htodo : todo.Nodup := (List.nodup_cons.mp h2).2
            have hq'todo : q' ∉ todo := (List.nodup_cons.mp h2).1
            refine ⟨?_, htodo, ?_, ?_⟩
            · intro a ha
              rcases observe_mem obj seed _ commands a ha with hm | ⟨hann, hzero⟩
              · exact h1 a hm
              · exact ⟨hzero,
                  (proposal_provenance obj hprev).announcements q' a hann⟩
            · -- no duplicates: the freshly read register was never read before
              refine observe_nodup obj seed _ commands h3 ?_
              intro a hann hmem
              have hbp : a.process = q' := announcement_process obj hprev q' a hann
              exact h4 a hmem (hbp ▸ List.mem_cons_self ..)
            · exact observe_fresh obj seed _ commands q' todo
                (fun a hann => announcement_process obj hprev q' a hann) h4 hq'todo
          · exact ih.gathering q own base todo' commands' (by simpa [update, he] using hq)
        · exact ih.calls
    | propose p cmd seed commands h arranged harr hi =>
        constructor
        · intro q own base todo commands' hq
          by_cases he : q = p
          · subst he; simp [update] at hq
          · exact ih.gathering q own base todo commands' (by simpa [update, he] using hq)
        · intro call hcall
          obtain ⟨h1, -, h3, -⟩ := ih.gathering p cmd seed [] commands h
          rcases List.mem_cons.mp hcall with rfl | hm
          · refine ⟨seed, arranged, ?_, fun a ha => h1 a (harr.mem_iff.mp ha),
              harr.nodup_iff.mpr h3, rfl, rfl⟩
            have hl := (invariant obj hprev).localState p
            rw [h] at hl
            exact hl
          · exact ih.calls call hm
    | receive p cmd r prop s flag h ho =>
        constructor
        · intro q own base todo commands hq
          by_cases he : q = p
          · subst he
            simp only [update, ↓reduceIte] at hq
            split at hq <;> simp at hq
          · exact ih.gathering q own base todo commands (by simpa [update, he] using hq)
        · exact ih.calls
    | readStart p _ _ _ _ _ | readCheck p _ _ _ _ _ _ =>
        constructor
        · intro q own base todo' commands hq
          by_cases he : q = p
          · subst he; simp [update] at hq
          · exact ih.gathering q own base todo' commands (by simpa [update, he] using hq)
        · exact ih.calls
    | collectedStart p _ _ _ order horder | retry p _ _ _ _ _ order horder =>
        constructor
        · intro q own base todo commands hq
          by_cases he : q = p
          · subst he
            simp only [update, ↓reduceIte] at hq
            injection hq with e1 e2 e3 e4
            subst e3; subst e4
            exact ⟨by simp, horder.nodup_iff.mpr (List.nodup_finRange n), List.nodup_nil, by simp⟩
          · exact ih.gathering q own base todo commands (by simpa [update, he] using hq)
        · exact ih.calls
    | announce p _ _ _ | publish p _ _ _ | finish p _ _ _ _ _ =>
        constructor
        · intro q own base todo commands hq
          by_cases he : q = p
          · subst he; simp [update] at hq
          · exact ih.gathering q own base todo commands (by simpa [update, he] using hq)
        · exact ih.calls

/-- A step that records a new call leaves the caller waiting in that round. -/
theorem stepBy_new_call {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {call : Call (n := n) obj} (hin : call ∈ d.calls) (hout : call ∉ c.calls) :
    ∃ cmd, d.localState call.process = .waiting cmd call.round call.trace := by
  cases h.1 with
  | propose q cmd seed commands hq hi =>
      rcases List.mem_cons.mp hin with rfl | hm
      · exact ⟨cmd, by simp [update]⟩
      · exact absurd hm hout
  | _ => exact absurd hin hout

/-- A step that records a new call fires from a finished `M` collect, and the
recorded call is that collect's proposal, for some arrangement of `trace(M_i)`. -/
theorem stepBy_new_call_source {H : Environment (n := n) obj} {p : Fin n}
    {c d : Configuration (n := n) obj} (h : StepBy obj H p c d)
    {call : Call (n := n) obj} (hin : call ∈ d.calls) (hout : call ∉ c.calls) :
    ∃ cmd seed commands arranged, c.localState call.process = .gathering cmd seed [] commands ∧
      arranged.Perm commands ∧ call.round = seed.round + 1 ∧
      call.trace = proposal obj seed arranged := by
  cases h.1 with
  | propose q cmd seed commands hq arranged harr hi =>
      rcases List.mem_cons.mp hin with rfl | hm
      · exact ⟨cmd, seed, commands, arranged, hq, harr, rfl, rfl⟩
      · exact absurd hm hout
  | _ => exact absurd hin hout

/-- **Occurrence uniqueness for Algorithm 3.**  No GCA output reachable from
Algorithm 3 contains the same tagged command twice.  The `M` collect visits each
register once and skips commands already in the adopted trace, so an input never
duplicates an occurrence; GCA validity then pushes a hypothetical duplicate back
to a strictly earlier round. -/
theorem output_count_le_one {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H) (spec : ∀ r, (H (r + 1)).Specification) :
    ∀ r p t flag a, (H (r + 1)).output p = some (t, flag) →
      (Tagged obj).traceCount a t ≤ 1 := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro p t flag a hout
    apply Nat.le_of_not_lt
    intro hdup
    have hocc : GCA.History.Occurs (obj := Tagged (n := n) obj) a 1 t := by
      simpa only [GCA.History.Occurs, (Tagged obj).traceResponses_length] using hdup
    obtain ⟨s, ⟨q, hinput⟩, hsocc⟩ := (spec r).validity.occurs p t flag hout a 1 hocc
    have hsdup : 1 < (Tagged obj).traceCount a s := by
      simpa only [GCA.History.Occurs, (Tagged obj).traceResponses_length] using hsocc
    obtain ⟨c, hc, hcall⟩ := coverage r q s hinput
    obtain ⟨seed, commands, hseed, hall, hnd, hround, htrace⟩ := (callShape obj hc).calls _ hcall
    change s = proposal obj seed commands at htrace
    change r + 1 = seed.round + 1 at hround
    rw [htrace, proposal_count] at hsdup
    have hcnt : commands.count a ≤ 1 := count_le_one_of_nodup hnd a
    have hbase : 1 < (Tagged obj).traceCount a seed.trace := by
      by_cases hm : a ∈ commands
      · have := (hall a hm).1
        omega
      · have : commands.count a = 0 := List.count_eq_zero.mpr hm
        omega
    rcases hseed with ⟨_, hempty⟩ | ⟨hpositive, q', b, hprev⟩
    · rw [hempty] at hbase
      change 1 < ([] : List (Cmd n Op)).count a at hbase
      simp at hbase
    · have hseedr : seed.round = r := by omega
      have hrpos : 0 < r := by omega
      obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      have hprev' : (H (k + 1)).output q' = some (seed.trace, b) := by
        simpa only [hseedr, hk] using hprev
      have hle := ih k (by omega) q' seed.trace b a hprev'
      omega

/-- A command whose response has been recorded occupies every later committed
trace, hence the common prefix of any set of outputs of a later round. -/
theorem returned_below_glb {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H) (spec : ∀ r, (H (r + 1)).Specification)
    {ret : Return (n := n) obj}
    (hcom : Committed obj H ret.round ret.trace)
    {k : Nat} (hk : ret.round ≤ k + 1)
    {X : (Tagged (n := n) obj).Trace → Prop} (hX : ∀ x, X x → (H (k + 1)).Outputs x)
    {t : (Tagged (n := n) obj).Trace} (ht : (Tagged obj).IsGLB X t) :
    (Tagged obj).TracePrefix ret.trace t := by
  obtain ⟨hpos, q, hq⟩ := hcom
  obtain ⟨r, hr⟩ : ∃ r, ret.round = r + 1 := ⟨ret.round - 1, by omega⟩
  rw [hr] at hq hk
  refine ht.2 ret.trace ?_
  intro x hx
  obtain ⟨p', flag, hx⟩ := hX x hx
  exact committed_prefix obj coverage spec (by omega) hq hx

end ConflictFreedom.HelpingUniversal

namespace ConflictFreedom.GlobalSchedule
open Object UniversalProtocol

variable {State Op Response : Type} {n : Nat} {obj : Object State Op Response}
variable [DecidableEq Op] {H : WeakUniversal.Environment (n := n) obj}


namespace HelpingRun
variable (g : HelpingRun obj H)

/-- A command invoked by this particular scheduled run. -/
def Invoked (a : WeakUniversal.Cmd n Op) : Prop :=
  ∃ t, a ∈ (g.run.state t).invocations

/-- The paper's "operations that have already returned", relative to a round. -/
def ReturnedBy (k : Nat) (a : WeakUniversal.Cmd n Op) : Prop :=
  ∃ t, ∃ ret ∈ (g.run.state t).returns, ret.command = a ∧ ret.round ≤ k + 1

/-- The paper's "pending operations": invoked, and not returned by round
`k + 1`. -/
def Pending (k : Nat) (a : WeakUniversal.Cmd n Op) : Prop :=
  g.Invoked a ∧ ¬ g.ReturnedBy k a

/-- The step at which a call is recorded: at `u` its caller has finished the
`M` collect the proposal is built from (Lines 10–11), and the call appears at
`u + 1`. -/
theorem call_proposed {t' : Nat} {call : WeakUniversal.Call (n := n) obj}
    (h : call ∈ (g.run.state t').calls) :
    ∃ u cmd seed commands arranged, call ∉ (g.run.state u).calls ∧
      call ∈ (g.run.state (u + 1)).calls ∧
      (g.run.state u).localState call.process = .gathering cmd seed [] commands ∧
      arranged.Perm commands ∧ call.round = seed.round + 1 ∧
      call.trace = HelpingUniversal.proposal obj seed arranged := by
  classical
  induction t' with
  | zero => rw [g.run.initial_state] at h; simp [HelpingUniversal.initial] at h
  | succ t ih =>
      by_cases hprev : call ∈ (g.run.state t).calls
      · exact ih hprev
      · rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
        · rw [heq] at h; exact absurd h hprev
        · obtain ⟨cmd, seed, commands, arranged, hsrc, harr, hr, htr⟩ :=
            HelpingUniversal.stepBy_new_call_source obj hstep h hprev
          exact ⟨t, cmd, seed, commands, arranged, hprev, h, hsrc, harr, hr, htr⟩
        · rw [heq] at h; exact absurd h hprev

/-- The manuscript's `t_j` for round `k + 2`: `b` is the trace a process
retrieved from round `k + 1` — its local `(r, s) = (k + 1, b)` — at the step
`u` at which it proposes `b · trace(M_j)` to round `k + 2`. -/
def Retrieved (k : Nat) (b : (WeakUniversal.Tagged (n := n) obj).Trace) : Prop :=
  ∃ u cmd commands arranged, ∃ call : WeakUniversal.Call (n := n) obj,
    call ∉ (g.run.state u).calls ∧ call ∈ (g.run.state (u + 1)).calls ∧
    (g.run.state u).localState call.process = .gathering cmd ⟨k + 1, b⟩ [] commands ∧
    arranged.Perm commands ∧ call.round = k + 2 ∧
    call.trace = HelpingUniversal.proposal obj ⟨k + 1, b⟩ arranged

/-- A retrieved trace is an output of the previous round. -/
theorem retrieved_output {k : Nat} {b : (WeakUniversal.Tagged (n := n) obj).Trace}
    (h : g.Retrieved k b) : (H (k + 1)).Outputs b := by
  obtain ⟨u, cmd, commands, arranged, call, -, -, hL, -, -, -⟩ := h
  have hsup : WeakUniversal.Supported obj H ⟨k + 1, b⟩ := by
    simpa only [hL, HelpingUniversal.LocalInvariant] using
      (HelpingUniversal.invariant obj (g.run.reachable obj u)).localState call.process
  rcases hsup with ⟨h0, -⟩ | ⟨-, q, flag, hq⟩
  · exact absurd h0 (Nat.succ_ne_zero k)
  · exact ⟨q, flag, hq⟩

/-- Every proposal to round `k + 2` is built from a retrieved trace and a
finished `M` collect (Lines 10–11). -/
theorem input_retrieved {k : Nat} {p : Fin n} {s : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hs : (H (k + 2)).input p = some s) :
    ∃ b u cmd commands arranged, g.Retrieved k b ∧
      (g.run.state u).localState p = .gathering cmd ⟨k + 1, b⟩ [] commands ∧
      arranged.Perm commands ∧ s = HelpingUniversal.proposal obj ⟨k + 1, b⟩ arranged := by
  obtain ⟨t', hcall⟩ := (g.input_iff_call (k + 1) p s).mp hs
  obtain ⟨u, cmd, seed, commands, arranged, hno, hyes, hL, harr, hr, htr⟩ :=
    g.call_proposed hcall
  obtain ⟨sr, st⟩ := seed
  obtain rfl : sr = k + 1 := by simp only at hr; omega
  exact ⟨st, u, cmd, commands, arranged,
    ⟨u, cmd, commands, arranged, _, hno, hyes, hL, harr, rfl, htr⟩, hL, harr, htr⟩

/-- A round with a caller has a retrieved trace. -/
theorem retrieved_nonempty {k : Nat} (h : ∃ s, (H (k + 2)).Inputs s) :
    ∃ b, g.Retrieved k b := by
  obtain ⟨s, p, hp⟩ := h
  obtain ⟨b, -, -, -, -, hb, -⟩ := g.input_retrieved hp
  exact ⟨b, hb⟩

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- Every command in a protocol output originated in an invocation of this
run. -/
theorem output_occurrence_invoked :
    ∀ r p t flag a,
      (H (r + 1)).output p = some (t, flag) →
      0 < (WeakUniversal.Tagged obj).traceCount a t → g.Invoked a := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro p t flag a hout hpos
    have hocc : GCA.History.Occurs (obj := WeakUniversal.Tagged (n := n) obj) a 0 t := by
      simpa only [GCA.History.Occurs,
        (WeakUniversal.Tagged obj).traceResponses_length] using hpos
    obtain ⟨s, ⟨q, hinput⟩, hsocc⟩ :=
      (g.gca.spec r).validity.occurs p t flag hout a 0 hocc
    have hspos : 0 < (WeakUniversal.Tagged obj).traceCount a s := by
      simpa only [GCA.History.Occurs,
        (WeakUniversal.Tagged obj).traceResponses_length] using hsocc
    obtain ⟨u, hcall⟩ := (g.input_iff_call r q s).mp hinput
    obtain ⟨seed, commands, hsup, hall, -, hround, htrace⟩ :=
      (HelpingUniversal.callShape obj (g.run.reachable obj u)).calls _ hcall
    change s = HelpingUniversal.proposal obj seed commands at htrace
    change r + 1 = seed.round + 1 at hround
    rw [htrace, HelpingUniversal.proposal_count] at hspos
    by_cases hb : 0 < (WeakUniversal.Tagged obj).traceCount a seed.trace
    · rcases hsup with ⟨_, hempty⟩ | ⟨hpositive, q', b, hprev⟩
      · rw [hempty] at hb
        change 0 < ([] : List (WeakUniversal.Cmd n Op)).count a at hb
        simp at hb
      · have hseedr : seed.round = r := by omega
        obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        have hprev' : (H (k + 1)).output q' = some (seed.trace, b) := by
          simpa only [hseedr, hk] using hprev
        exact ih k (by omega) q' seed.trace b a hprev' hb
    · have hmem : a ∈ commands := List.count_pos_iff.mp (by omega)
      exact ⟨u, (hall a hmem).2⟩

/-- **Invariant (I), one proposal, for Algorithm 3.**  Let `t = ⊓ 𝒯` be the
greatest common prefix of the traces `t_j` retrieved from round `k + 1` by the
processes proposing to round `k + 2`, and `t_j = t · u_j`.  Every proposal
`s_j = t_j · m_j` is `t · u_j · m_j`, with only commands of operations that have
not returned in `u_j · m_j`: a returned command lies in a committed trace,
which prefixes every `t_j` (`lemma:prefix-rounds`), hence `t`, and `m_j` skips
the commands of `t_j` (Line 10). -/
theorem proposal_shape
    (coverage : HelpingUniversal.CallsCovered obj (H))
    {k : Nat} {t : (WeakUniversal.Tagged (n := n) obj).Trace}
    (ht : (WeakUniversal.Tagged obj).IsGLB (g.Retrieved k) t)
    {s : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hs : (H (k + 2)).Inputs s) :
    ∃ w : List (WeakUniversal.Cmd n Op),
      (∀ a ∈ w, g.Pending k a ∧ (WeakUniversal.Tagged obj).traceCount a t = 0) ∧
      s = (WeakUniversal.Tagged obj).traceAppend t (Quotient.mk _ w) := by
  classical
  obtain ⟨p, hp⟩ := hs
  -- the trace `t_p` that `p` retrieved, an output of round `k + 1`, and `m_p`
  obtain ⟨b, t', cmd, gathered, commands, hb, hL, harr, hshape⟩ := g.input_retrieved hp
  have hall : ∀ a ∈ commands, (WeakUniversal.Tagged obj).traceCount a b = 0 ∧
      a ∈ (g.run.state t').invocations := fun a ha =>
    ((HelpingUniversal.callShape obj (g.run.reachable obj t')).gathering p cmd
      ⟨k + 1, b⟩ [] gathered hL).1 a (harr.mem_iff.mp ha)
  obtain ⟨q, flag, hq⟩ := g.retrieved_output hb
  obtain ⟨v, hv⟩ := ((WeakUniversal.Tagged obj).tracePrefix_iff_append t b).mp (ht.1 b hb)
  obtain ⟨w0, hw0⟩ := Quotient.exists_rep v
  have hle1 : ∀ a, (WeakUniversal.Tagged obj).traceCount a b ≤ 1 :=
    fun a => HelpingUniversal.output_count_le_one obj coverage (g.gca.spec)
      k q b flag a hq
  -- a returned command already sits in the common prefix
  have hret_t : ∀ a, g.ReturnedBy k a → 0 < (WeakUniversal.Tagged obj).traceCount a t := by
    rintro a ⟨t₀, ret, hmem, rfl, hrk⟩
    obtain ⟨hcom, hcount⟩ :=
      (HelpingUniversal.invariant obj (g.run.reachable obj t₀)).returns ret hmem
    exact Nat.lt_of_lt_of_le hcount
      ((WeakUniversal.Tagged obj).traceCount_mono
        (HelpingUniversal.returned_below_glb obj coverage (g.gca.spec) hcom hrk
          (fun x hx => g.retrieved_output hx) ht) _)
  -- the residual of the adopted trace holds only pending commands
  have hres : ∀ a ∈ w0, g.Pending k a ∧
      (WeakUniversal.Tagged obj).traceCount a t = 0 := by
    intro a ha
    have h2 : 0 < w0.count a := List.count_pos_iff.mpr ha
    have h3 : (WeakUniversal.Tagged obj).traceCount a b
        = (WeakUniversal.Tagged obj).traceCount a t + w0.count a := by
      rw [hv, ← hw0]
      exact (WeakUniversal.Tagged obj).traceCount_append a t (Quotient.mk _ w0)
    have hle := hle1 a
    refine ⟨⟨g.output_occurrence_invoked k q b flag a hq (by omega), ?_⟩, by omega⟩
    intro hbad
    have h1 : 0 < (WeakUniversal.Tagged obj).traceCount a t := hret_t a hbad
    omega
  -- and so does the helping list, because it skips commands already adopted
  have hhelp : ∀ a ∈ commands, g.Pending k a ∧
      (WeakUniversal.Tagged obj).traceCount a t = 0 := by
    intro a ha
    obtain ⟨hzero, hinv⟩ := hall a ha
    have h2 : (WeakUniversal.Tagged obj).traceCount a t
        ≤ (WeakUniversal.Tagged obj).traceCount a b :=
      (WeakUniversal.Tagged obj).traceCount_mono (ht.1 b hb) _
    refine ⟨⟨⟨t', hinv⟩, ?_⟩, by omega⟩
    intro hbad
    have h1 : 0 < (WeakUniversal.Tagged obj).traceCount a t := hret_t a hbad
    omega
  refine ⟨w0 ++ commands, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hres a h
    · exact hhelp a h
  · have hshape' : s = HelpingUniversal.proposal obj ⟨k + 1, b⟩ commands := hshape
    have hexp : HelpingUniversal.proposal obj ⟨k + 1, b⟩ commands
        = (WeakUniversal.Tagged obj).traceAppend b
            (Quotient.mk _ commands) := rfl
    rw [hshape', hexp, hv, ← hw0]
    exact ((WeakUniversal.Tagged obj).traceAppend_assoc t (Quotient.mk _ w0)
      (Quotient.mk _ commands)).trans
      (by rw [(WeakUniversal.Tagged obj).traceAppend_mk])

end HelpingGCA

namespace HelpingRun
variable (g : HelpingRun obj H)

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- **Invariant (I) for Algorithm 3, for an arbitrary nonconflicting set.**  If
every command in the residual of a proposal to round `k + 2` over the common
prefix `t` of the traces retrieved from round `k + 1` lies in a set `C` of pairwise
nonconflicting commands, then only compatible traces are proposed to round
`k + 2`. -/
theorem inputs_compatible_res
    (coverage : HelpingUniversal.CallsCovered obj (H))
    {k : Nat} {t : (WeakUniversal.Tagged (n := n) obj).Trace}
    (ht : (WeakUniversal.Tagged obj).IsGLB (g.Retrieved k) t)
    {C : WeakUniversal.Cmd n Op → Prop}
    (hC : (WeakUniversal.Tagged obj).Nonconflicting C)
    (hsub : ∀ s, (H (k + 2)).Inputs s → ∀ a, g.Pending k a →
      (WeakUniversal.Tagged obj).traceCount a t = 0 →
      0 < (WeakUniversal.Tagged obj).traceCount a s → C a) :
    (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs := by
  classical
  refine (H (k + 2)).inputs_compatible_of_pending_proposals hC t
    ((List.finRange n).filterMap (fun p => (H (k + 2)).input p)) ?_ ?_
  · rintro s ⟨p, hp⟩
    exact List.mem_filterMap.mpr ⟨p, List.mem_finRange p, hp⟩
  · intro s hsm
    obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hsm
    obtain ⟨w, hw, he⟩ := g.proposal_shape coverage ht ⟨p, hp⟩
    refine ⟨w, fun a ha => hsub s ⟨p, hp⟩ a (hw a ha).1 (hw a ha).2 ?_, he⟩
    have hwc : 0 < w.count a := List.count_pos_iff.mpr ha
    have : (WeakUniversal.Tagged obj).traceCount a s
        = (WeakUniversal.Tagged obj).traceCount a t + w.count a := by
      rw [he]
      exact (WeakUniversal.Tagged obj).traceCount_append a t (Quotient.mk _ w)
    omega

/-- **Invariant (I) for Algorithm 3.**  If the commands of operations that have
not returned pairwise do not conflict, then only compatible traces are proposed
to round `k + 2`. -/
theorem inputs_compatible_at
    (coverage : HelpingUniversal.CallsCovered obj (H))
    {k : Nat} {t : (WeakUniversal.Tagged (n := n) obj).Trace}
    (ht : (WeakUniversal.Tagged obj).IsGLB (g.Retrieved k) t)
    (hC : (WeakUniversal.Tagged obj).Nonconflicting
      (fun a => g.Pending k a ∧ (WeakUniversal.Tagged obj).traceCount a t = 0)) :
    (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs :=
  g.inputs_compatible_res coverage ht hC (fun _ _ _ hp hz _ => ⟨hp, hz⟩)

theorem inputs_compatible
    (coverage : HelpingUniversal.CallsCovered obj (H))
    {k : Nat} (hne : ∃ x, g.Retrieved k x)
    (hC : (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k)) :
    (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs := by
  classical
  obtain ⟨t, ht⟩ := (WeakUniversal.Tagged obj).glb_exists _ hne
  exact g.inputs_compatible_at coverage ht (fun a b ha hb hab => hC a b ha.1 hb.1 hab)

/-- A caller that keeps taking steps gets an output from the round it called. -/
theorem caller_returns {p : Fin n} (hsched : ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p)
    {u : Nat} {cmd : WeakUniversal.Cmd n Op} {r : Nat}
    {prop : (WeakUniversal.Tagged (n := n) obj).Trace}
    (hL : (g.run.state u).localState p = .waiting cmd r prop) :
    ∃ y flag, (H r).output p = some (y, flag) := by
  obtain ⟨v, hv, hconst, hstep⟩ := g.next_step hsched u
  obtain ⟨y, flag, hout, -⟩ :=
    HelpingUniversal.stepBy_from_waiting obj hstep (hconst.trans hL)
  exact ⟨y, flag, hout⟩

end HelpingGCA

namespace HelpingRun
variable (g : HelpingRun obj H)

/-- Every recorded call was made from a `waiting` state of its caller. -/
theorem call_was_waiting {t' : Nat} {call : WeakUniversal.Call (n := n) obj}
    (h : call ∈ (g.run.state t').calls) :
    ∃ u cmd, (g.run.state u).localState call.process
      = .waiting cmd call.round call.trace := by
  classical
  induction t' with
  | zero => rw [g.run.initial_state] at h; simp [HelpingUniversal.initial] at h
  | succ t ih =>
      by_cases hprev : call ∈ (g.run.state t).calls
      · exact ih hprev
      · rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
        · rw [heq] at h; exact absurd h hprev
        · obtain ⟨cmd, hcmd⟩ := HelpingUniversal.stepBy_new_call obj hstep h hprev
          exact ⟨t + 1, cmd, hcmd⟩
        · rw [heq] at h; exact absurd h hprev

/-- A call not yet recorded at time `T` was made from a `waiting` state at or
after `T`. -/
theorem call_was_waiting_after {T t' : Nat} {call : WeakUniversal.Call (n := n) obj}
    (h : call ∈ (g.run.state t').calls) (hT : call ∉ (g.run.state T).calls) :
    ∃ u, T ≤ u ∧ ∃ cmd, (g.run.state u).localState call.process
      = .waiting cmd call.round call.trace := by
  classical
  induction t' with
  | zero => rw [g.run.initial_state] at h; simp [HelpingUniversal.initial] at h
  | succ t ih =>
      by_cases hprev : call ∈ (g.run.state t).calls
      · exact ih hprev
      · have hTt : T ≤ t + 1 := by
          refine Nat.le_of_not_lt (fun hlt => hT ?_)
          exact g.calls_mono (by omega) h
        rcases g.step_actor t with ⟨_, heq⟩ | ⟨q, _, hstep⟩ | ⟨q, r, _, _, heq⟩
        · rw [heq] at h; exact absurd h hprev
        · obtain ⟨cmd, hcmd⟩ := HelpingUniversal.stepBy_new_call obj hstep h hprev
          exact ⟨t + 1, hTt, cmd, hcmd⟩
        · rw [heq] at h; exact absurd h hprev

end HelpingRun

namespace HelpingGCA
variable (g : HelpingGCA obj H)

/-- Every caller of a round that keeps taking steps returns from it. -/
theorem allReturned {k : Nat}
    (hsched : ∀ p, (∃ s, (H (k + 2)).input p = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    (H (k + 2)).AllReturned := by
  intro p s hin
  obtain ⟨t', hcall⟩ := (g.input_iff_call (k + 1) p s).mp hin
  obtain ⟨u, cmd, hL⟩ := g.call_was_waiting hcall
  exact g.caller_returns (hsched p ⟨s, hin⟩) hL

/-- **Lemma `UCV2isCF`, Commitment step.**  Under invariant (I) the proposals to
round `k + 2` are compatible, so some caller's own proposal is a prefix of a
committed output. -/
theorem exists_commit_of_compatible {k : Nat}
    (hcompat : (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs)
    (hcaller : ∃ s, (H (k + 2)).Inputs s)
    (hcallers_sched : ∀ p, (∃ s, (H (k + 2)).input p = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    ∃ p s x, (H (k + 2)).input p = some s ∧
      (H (k + 2)).output p = some (x, true) ∧
      (WeakUniversal.Tagged obj).TracePrefix s x :=
  (g.gca.spec (k + 1)).commitment hcaller hcompat
    (g.allReturned hcallers_sched)

theorem exists_commit (coverage : HelpingUniversal.CallsCovered obj (H))
    {k : Nat} (hC : (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k))
    (hcaller : ∃ s, (H (k + 2)).Inputs s)
    (hcallers_sched : ∀ p, (∃ s, (H (k + 2)).input p = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    ∃ p s x, (H (k + 2)).input p = some s ∧
      (H (k + 2)).output p = some (x, true) ∧
      (WeakUniversal.Tagged obj).TracePrefix s x :=
  g.exists_commit_of_compatible
    (g.inputs_compatible coverage (g.retrieved_nonempty hcaller) hC)
    hcaller hcallers_sched

/-- Compatibility of the round's proposals with no nonemptiness side
condition. -/
theorem inputs_compatible_total
    (coverage : HelpingUniversal.CallsCovered obj (H)) {k : Nat}
    (hC : (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k)) :
    (WeakUniversal.Tagged obj).Compatible (H (k + 2)).Inputs := by
  classical
  by_cases hcaller : ∃ s, (H (k + 2)).Inputs s
  · exact g.inputs_compatible coverage (g.retrieved_nonempty hcaller) hC
  · exact ⟨(WeakUniversal.Tagged obj).emptyTrace, fun s hs => absurd ⟨s, hs⟩ hcaller⟩

/-- The committing caller's own command occurs in the committed trace. -/
theorem commit_contains_own (coverage : HelpingUniversal.CallsCovered obj (H))
    {k : Nat} (hC : (WeakUniversal.Tagged obj).Nonconflicting (g.Pending k))
    (hcaller : ∃ s, (H (k + 2)).Inputs s)
    (hcallers_sched : ∀ p, (∃ s, (H (k + 2)).input p = some s) →
      ∀ N, ∃ t, N ≤ t ∧ g.actor t = some p) :
    ∃ p s x cmd u, (H (k + 2)).input p = some s ∧
      (H (k + 2)).output p = some (x, true) ∧
      (g.run.state u).localState p = .waiting cmd (k + 2) s ∧
      0 < (WeakUniversal.Tagged obj).traceCount cmd x := by
  obtain ⟨p, s, x, hin, hout, hpre⟩ :=
    g.exists_commit coverage hC hcaller hcallers_sched
  obtain ⟨t', hcall⟩ := (g.input_iff_call (k + 1) p s).mp hin
  obtain ⟨u, cmd, hL⟩ := g.call_was_waiting hcall
  obtain ⟨-, hcount⟩ :=
    HelpingUniversal.waiting_call obj (g.run.reachable obj u) p cmd (k + 2) s hL
  exact ⟨p, s, x, cmd, u, hin, hout, hL,
    Nat.lt_of_lt_of_le hcount ((WeakUniversal.Tagged obj).traceCount_mono hpre cmd)⟩

end HelpingGCA
end ConflictFreedom.GlobalSchedule
