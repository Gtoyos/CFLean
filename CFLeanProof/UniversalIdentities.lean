import CFLeanProof.InvocationLedger
import CFLeanProof.HelpingUniversal

/-! Fresh invocation identities and at-most-once responses, derived from the
program transitions without assumptions about GCA results or progress. -/
namespace ConflictFreedom
namespace WeakUniversal
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-- The command a process is executing, if any. -/
def Local.command : Local (n := n) obj → Option (Cmd n Op)
  | .idle => none
  | .collecting cmd _ _ | .ready cmd _ | .waiting cmd _ _
  | .publishing cmd _ _ | .returning cmd _ _ => some cmd

/-- The invocation ledger a configuration of Algorithm 1 determines. -/
def ledger (c : Configuration (n := n) obj) : InvocationLedger.State (Fin n) Op :=
  ⟨c.sequence, fun p => (c.localState p).command obj, c.invocations, c.returns.map Return.command⟩

private theorem command_update (f : Fin n → Local (n := n) obj) (p : Fin n) (l : Local (n := n) obj) :
    (fun q => (update f p l q).command obj) =
      InvocationLedger.update (fun q => (f q).command obj) p (l.command obj) := by
  funext q
  by_cases h : q = p <;> simp [update, InvocationLedger.update, h]

private theorem update_same {α : Type} (f : Fin n → α) (p : Fin n) (a : α) (h : f p = a) :
    InvocationLedger.update f p a = f := by
  funext q
  by_cases he : q = p <;> simp_all [InvocationLedger.update]

variable [DecidableEq Op]

theorem ledger_step {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) :
    ledger obj d = ledger obj c ∨
      (∃ p op, (ledger obj c).active p = none ∧
        ledger obj d = InvocationLedger.invoke (ledger obj c) p op) ∨
      (∃ p cmd, (ledger obj c).active p = some cmd ∧
        ledger obj d = InvocationLedger.finish (ledger obj c) p cmd) := by
  cases hs with
  | invoke p op h =>
    right; left
    refine ⟨p, op, ?_, ?_⟩
    · simp [ledger, h, Local.command]
    · simp only [ledger]
      rw [command_update]
      rfl
  | receive p cmd r proposal s flag h ho =>
    left
    simp only [ledger]
    rw [command_update]
    split <;> simp only [Local.command] <;>
      rw [update_same _ p _ (by simp [h])]
  | read p _ _ _ _ h | collected p _ _ h | propose p _ _ h _ | publish p _ _ _ h =>
    left
    simp only [ledger]
    rw [command_update]
    simp only [Local.command]
    rw [update_same _ p _ (by simp [h])]
  | finish p cmd r s h =>
    right; right
    refine ⟨p, cmd, ?_, ?_⟩
    · simp [ledger, h, Local.command]
    · simp only [ledger]
      rw [command_update]
      rfl

theorem identity_invariant {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : InvocationLedger.Valid (ledger obj c) := by
  induction hc with
  | initial => exact InvocationLedger.initial_valid
  | step _ hs ih =>
    rcases ledger_step obj hs with he | ⟨p, op, hp, he⟩ | ⟨p, cmd, hp, he⟩
    · exact he ▸ ih
    · rw [he]; exact InvocationLedger.valid_invoke ih p op hp
    · rw [he]; exact InvocationLedger.valid_finish ih p cmd hp

theorem invocation_keys_unique {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : (c.invocations.map Command.key).Nodup :=
  (identity_invariant obj hc).invoked_unique

theorem response_keys_unique {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : (c.returns.map (fun r => r.command.key)).Nodup := by
  simpa only [ledger, List.map_map, Function.comp_def] using (identity_invariant obj hc).returned_unique

theorem response_was_invoked {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) {ret : Return (n := n) obj} (hr : ret ∈ c.returns) :
    ret.command ∈ c.invocations :=
  (identity_invariant obj hc).returned_invoked _ (List.mem_map.mpr ⟨ret, hr, rfl⟩)

/-- Every recorded call was made for an actual invocation. Its input is the
one-command extension of a seed collected by that process. -/
theorem call_origin {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) {call : Call (n := n) obj} (hcall : call ∈ c.calls) :
    ∃ cmd ∈ c.invocations, ∃ seed : Seed (n := n) obj,
      Supported obj H seed ∧ cmd.process = call.process ∧
      call.round = seed.round + 1 ∧
      call.trace = (Tagged obj).appendMissing seed.trace cmd := by
  induction hc generalizing call with
  | initial => cases hcall
  | step hprev hs ih =>
    cases hs with
    | invoke p op h =>
      obtain ⟨cmd, hcmd, seed, hseed, howner, hround, htrace⟩ := ih hcall
      exact ⟨cmd, List.mem_cons_of_mem _ hcmd, seed, hseed, howner, hround, htrace⟩
    | propose p cmd seed h hi =>
      rcases List.mem_cons.mp hcall with hnew | hold
      · subst call
        have htag := (identity_invariant obj hprev).active_tag p cmd
          (by simp [ledger, h, Local.command])
        have hcmd := htag.2.2
        have hseed : Supported obj H seed := by
          simpa only [h, LocalInvariant] using (invariant obj hprev).localState p
        exact ⟨cmd, hcmd, seed, hseed, htag.1, rfl, rfl⟩
      · exact ih hold
    | _ => exact ih hcall

private theorem appendMissing_source (s : (Tagged (n := n) obj).Trace)
    (a cmd : Cmd n Op) (h : 0 < (Tagged obj).traceCount a
      ((Tagged obj).appendMissing s cmd)) :
    a = cmd ∨ 0 < (Tagged obj).traceCount a s := by
  by_cases he : a = cmd
  · exact Or.inl he
  · right
    by_cases hz : (Tagged obj).traceCount cmd s = 0
    · simp only [Object.appendMissing, hz, ↓reduceIte] at h
      let one : (Tagged obj).Trace := Quotient.mk (Tagged obj).traceSetoid [cmd]
      change 0 < (Tagged obj).traceCount a ((Tagged obj).traceAppend s one) at h
      rw [(Tagged obj).traceCount_append a s one] at h
      have hsingle : (Tagged obj).traceCount a one = 0 := by
        change [cmd].count a = 0
        simp [Ne.symm he]
      rw [hsingle] at h
      omega
    · simpa [Object.appendMissing, hz] using h

private theorem appendMissing_count_other (s : (Tagged (n := n) obj).Trace)
    (a cmd : Cmd n Op) (hne : a ≠ cmd) :
    (Tagged obj).traceCount a ((Tagged obj).appendMissing s cmd) =
      (Tagged obj).traceCount a s := by
  unfold Object.appendMissing
  split
  · let one : (Tagged (n := n) obj).Trace :=
      Quotient.mk (Tagged obj).traceSetoid [cmd]
    change (Tagged obj).traceCount a ((Tagged obj).traceAppend s one) = _
    rw [(Tagged obj).traceCount_append a s one]
    have hsingle : (Tagged obj).traceCount a one = 0 := by
      change [cmd].count a = 0
      simp [Ne.symm hne]
    rw [hsingle]
    omega
  · rfl

/-- Every command occurrence in a GCA output of the weak construction comes
from an invocation recorded by some reachable configuration. This uses GCA
validity and faithful coverage of its inputs, while the call/seed provenance
itself follows from the program transitions. -/
theorem output_occurrence_invoked {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) :
    ∀ r p t flag a, (H (r + 1)).output p = some (t, flag) →
      0 < (Tagged obj).traceCount a t →
      ∃ c : Configuration (n := n) obj, Reachable obj H c ∧ a ∈ c.invocations := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro p t flag a hout hpos
    have hocc : GCA.History.Occurs (obj := Tagged (n := n) obj) a 0 t := by
      simpa only [GCA.History.Occurs, (Tagged obj).traceResponses_length] using hpos
    obtain ⟨s, ⟨q, hinput⟩, hsocc⟩ := (spec r).validity.occurs p t flag hout a 0 hocc
    have hspos : 0 < (Tagged obj).traceCount a s := by
      simpa only [GCA.History.Occurs, (Tagged obj).traceResponses_length] using hsocc
    obtain ⟨c, hc, hcall⟩ := coverage r q s hinput
    obtain ⟨cmd, hcmd, seed, hseed, _, hround, htrace⟩ := call_origin obj hc hcall
    change s = (Tagged obj).appendMissing seed.trace cmd at htrace
    change r + 1 = seed.round + 1 at hround
    rw [htrace] at hspos
    rcases appendMissing_source obj seed.trace a cmd hspos with he | hbase
    · exact ⟨c, hc, he ▸ hcmd⟩
    · rcases hseed with ⟨hz, hempty⟩ | ⟨hpositive, q', b, hprev⟩
      · rw [hempty] at hbase
        change 0 < ([] : List (Cmd n Op)).count a at hbase
        simp at hbase
      · have hseedr : seed.round = r := by omega
        have hrpos : 0 < r := by omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
        have hklt : k < r := by omega
        have hprev' : (H (k + 1)).output q' = some (seed.trace, b) := by
          have he : seed.round = k + 1 := hseedr.trans hk
          simpa only [he] using hprev
        exact ih k hklt q' seed.trace b a hprev' hbase

/-- No GCA output reachable from Algorithm 1 contains the same tagged command
twice. `appendMissing` caps the new command at one occurrence, and GCA validity
pushes any hypothetical duplicate back to a strictly earlier round. -/
theorem output_count_le_one {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) :
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
    obtain ⟨cmd, _, seed, hseed, _, hround, htrace⟩ := call_origin obj hc hcall
    change s = (Tagged obj).appendMissing seed.trace cmd at htrace
    change r + 1 = seed.round + 1 at hround
    rw [htrace] at hsdup
    have hbase : 1 < (Tagged obj).traceCount a seed.trace := by
      by_cases he : a = cmd
      · subst a
        rw [(Tagged obj).appendMissing_count] at hsdup
        omega
      · rw [appendMissing_count_other obj seed.trace a cmd he] at hsdup
        exact hsdup
    rcases hseed with ⟨_, hempty⟩ | ⟨hpositive, q', b, hprev⟩
    · rw [hempty] at hbase
      change 1 < ([] : List (Cmd n Op)).count a at hbase
      simp at hbase
    · have hseedr : seed.round = r := by omega
      have hrpos : 0 < r := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
      have hklt : k < r := by omega
      have hprev' : (H (k + 1)).output q' = some (seed.trace, b) := by
        have he : seed.round = k + 1 := hseedr.trans hk
        simpa only [he] using hprev
      have hle := ih k hklt q' seed.trace b a hprev'
      omega

end WeakUniversal

namespace HelpingUniversal
open WeakUniversal (Cmd Return Environment Seed Supported)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)

/-- The command a process is executing, if any. -/
def Local.command : Local (n := n) obj → Option (Cmd n Op)
  | .idle _ => none
  | .announcing cmd _ | .collecting cmd _ _ | .gathering cmd _ _ _
  | .waiting cmd _ _ | .publishing cmd _ | .checking cmd _ _ _ => some cmd

/-- The invocation ledger a configuration of Algorithm 3 determines. -/
def ledger (c : Configuration (n := n) obj) : InvocationLedger.State (Fin n) Op :=
  ⟨c.sequence, fun p => (c.localState p).command obj, c.invocations, c.returns.map Return.command⟩

private theorem command_update (f : Fin n → Local (n := n) obj) (p : Fin n) (l : Local (n := n) obj) :
    (fun q => (WeakUniversal.update f p l q).command obj) =
      InvocationLedger.update (fun q => (f q).command obj) p (l.command obj) := by
  funext q
  by_cases h : q = p <;> simp [WeakUniversal.update, InvocationLedger.update, h]

private theorem update_same {α : Type} (f : Fin n → α) (p : Fin n) (a : α) (h : f p = a) :
    InvocationLedger.update f p a = f := by
  funext q
  by_cases he : q = p <;> simp_all [InvocationLedger.update]

variable [DecidableEq Op]

theorem ledger_step {H : Environment (n := n) obj} {c d : Configuration (n := n) obj}
    (hs : Step obj H c d) :
    ledger obj d = ledger obj c ∨
      (∃ p op, (ledger obj c).active p = none ∧
        ledger obj d = InvocationLedger.invoke (ledger obj c) p op) ∨
      (∃ p cmd, (ledger obj c).active p = some cmd ∧
        ledger obj d = InvocationLedger.finish (ledger obj c) p cmd) := by
  cases hs with
  | invoke p op seed h =>
    right; left
    refine ⟨p, op, ?_, ?_⟩
    · simp [ledger, h, Local.command]
    · simp only [ledger]
      rw [command_update]
      rfl
  | receive p cmd r proposal s flag h ho =>
    left
    simp only [ledger]
    rw [command_update]
    split <;> simp only [Local.command] <;>
      rw [update_same _ p _ (by simp [h])]
  | announce p _ _ h | readStart p _ _ _ _ h | collectedStart p _ _ h
  | readAnnouncement p _ _ _ _ _ h | propose p _ _ _ h _ | publish p _ _ h
  | readCheck p _ _ _ _ _ h | retry p _ _ _ h _ =>
    left
    simp only [ledger]
    rw [command_update]
    simp only [Local.command]
    rw [update_same _ p _ (by simp [h])]
  | finish p cmd seed seen h hcontains =>
    right; right
    refine ⟨p, cmd, ?_, ?_⟩
    · simp [ledger, h, Local.command]
    · simp only [ledger]
      rw [command_update]
      rfl

theorem identity_invariant {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : InvocationLedger.Valid (ledger obj c) := by
  induction hc with
  | initial => exact InvocationLedger.initial_valid
  | step _ hs ih =>
    rcases ledger_step obj hs with he | ⟨p, op, hp, he⟩ | ⟨p, cmd, hp, he⟩
    · exact he ▸ ih
    · rw [he]; exact InvocationLedger.valid_invoke ih p op hp
    · rw [he]; exact InvocationLedger.valid_finish ih p cmd hp

theorem invocation_keys_unique {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : (c.invocations.map Command.key).Nodup :=
  (identity_invariant obj hc).invoked_unique

theorem response_keys_unique {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) : (c.returns.map (fun r => r.command.key)).Nodup := by
  simpa only [ledger, List.map_map, Function.comp_def] using (identity_invariant obj hc).returned_unique

theorem response_was_invoked {H : Environment (n := n) obj} {c : Configuration (n := n) obj}
    (hc : Reachable obj H c) {ret : Return (n := n) obj} (hr : ret ∈ c.returns) :
    ret.command ∈ c.invocations :=
  (identity_invariant obj hc).returned_invoked _ (List.mem_map.mpr ⟨ret, hr, rfl⟩)

/-- Bookkeeping needed to trace every helping proposal back either to a
previous-round output or to commands announced by actual invocations. -/
structure ProposalProvenance (H : Environment (n := n) obj)
    (c : Configuration (n := n) obj) : Prop where
  announcements : ∀ p cmd, c.announcements p = some cmd → cmd ∈ c.invocations
  gathering : ∀ p own seed todo commands,
    c.localState p = .gathering own seed todo commands →
      ∀ cmd ∈ commands, cmd ∈ c.invocations
  calls : ∀ call ∈ c.calls,
    ∃ seed commands, Supported obj H seed ∧
      (∀ cmd ∈ commands, cmd ∈ c.invocations) ∧
      call.round = seed.round + 1 ∧ call.trace = proposal obj seed commands

private theorem observe_source {base : Seed (n := n) obj}
    {seen : Option (Cmd n Op)} {commands : List (Cmd n Op)} {a : Cmd n Op}
    (h : a ∈ observe obj base seen commands) :
    a ∈ commands ∨ seen = some a := by
  cases seen with
  | none => exact Or.inl h
  | some cmd =>
    by_cases hz : (WeakUniversal.Tagged obj).traceCount cmd base.trace = 0
    · simp only [observe, hz, ↓reduceIte] at h
      rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · have he : a = cmd := by simpa using h
        exact Or.inr (congrArg some he.symm)
    · exact Or.inl (by simpa [observe, hz] using h)

theorem proposal_provenance {H : Environment (n := n) obj}
    {c : Configuration (n := n) obj} (hc : Reachable obj H c) :
    ProposalProvenance obj H c := by
  induction hc with
  | initial =>
      constructor
      · intro p cmd h; simp [initial] at h
      · intro p own seed todo commands h; simp [initial] at h
      · intro call h; cases h
  | step hprev hs ih =>
    rename_i prev next
    cases hs with
    | invoke p op seed h =>
      constructor
      · intro q cmd hq
        exact List.mem_cons_of_mem _ (ih.announcements q cmd hq)
      · intro q own base todo commands hq cmd hm
        by_cases he : q = p
        · subst q; simp [WeakUniversal.update] at hq
        · have hold : (prev.localState q) = .gathering own base todo commands := by
            simpa [WeakUniversal.update, he] using hq
          exact List.mem_cons_of_mem _ (ih.gathering q own base todo commands hold cmd hm)
      · intro call hcall
        obtain ⟨base, commands, hs, hall, hr, ht⟩ := ih.calls call hcall
        exact ⟨base, commands, hs,
          fun cmd hm => List.mem_cons_of_mem _ (hall cmd hm), hr, ht⟩
    | announce p cmd seed h =>
      constructor
      · intro q a hq
        by_cases he : q = p
        · subst q
          have ha : a = cmd := (Option.some.inj (by
            simpa [WeakUniversal.update] using hq)).symm
          subst a
          exact (identity_invariant obj hprev).active_tag p cmd
            (by simp [ledger, h, Local.command]) |>.2.2
        · exact ih.announcements q a (by
            simpa [WeakUniversal.update, he] using hq)
      · intro q own base todo commands hq a ha
        by_cases he : q = p
        · subst q; simp [WeakUniversal.update] at hq
        · exact ih.gathering q own base todo commands
            (by simpa [WeakUniversal.update, he] using hq) a ha
      · exact ih.calls
    | readAnnouncement p q own seed todo commands h =>
      constructor
      · exact ih.announcements
      · intro k cmd base rest gathered hk a ha
        by_cases he : k = p
        · subst k
          have holdprov := ih.gathering p own seed (q :: todo) commands h
          simp [WeakUniversal.update] at hk
          rcases hk with ⟨rfl, rfl, rfl, rfl⟩
          rcases observe_source obj ha with hold | hseen
          · exact holdprov a hold
          · exact ih.announcements q a hseen
        · exact ih.gathering k cmd base rest gathered
            (by simpa [WeakUniversal.update, he] using hk) a ha
      · exact ih.calls
    | propose p own seed commands h arranged harr hi =>
      constructor
      · exact ih.announcements
      · intro q cmd base todo gathered hq a ha
        by_cases he : q = p
        · subst q; simp [WeakUniversal.update] at hq
        · exact ih.gathering q cmd base todo gathered
            (by simpa [WeakUniversal.update, he] using hq) a ha
      · intro call hcall
        rcases List.mem_cons.mp hcall with rfl | hcall
        · have hs : Supported obj H seed := by
            simpa only [h, LocalInvariant] using (invariant obj hprev).localState p
          exact ⟨seed, arranged, hs,
            fun a ha => ih.gathering p own seed [] commands h a (harr.mem_iff.mp ha), rfl, rfl⟩
        · exact ih.calls call hcall
    | receive p own r input out flag h ho =>
      constructor
      · exact ih.announcements
      · intro q cmd base todo commands hq a ha
        by_cases he : q = p
        · subst q; split at hq <;> simp [WeakUniversal.update] at hq
        · exact ih.gathering q cmd base todo commands
            (by simpa [WeakUniversal.update, he] using hq) a ha
      · exact ih.calls
    | readStart p _ _ _ _ _ | readCheck p _ _ _ _ _ _ =>
      constructor
      · exact ih.announcements
      · intro k cmd base rest commands hk a ha
        by_cases he : k = p
        · subst k; simp [WeakUniversal.update] at hk
        · exact ih.gathering k cmd base rest commands
            (by simpa [WeakUniversal.update, he] using hk) a ha
      · exact ih.calls
    | collectedStart p _ _ _ | retry p _ _ _ _ _ =>
      constructor
      · exact ih.announcements
      · intro q cmd base todo commands hq a ha
        by_cases he : q = p
        · subst q
          simp [WeakUniversal.update] at hq
          rcases hq with ⟨rfl, rfl, rfl, rfl⟩
          cases ha
        · exact ih.gathering q cmd base todo commands
            (by simpa [WeakUniversal.update, he] using hq) a ha
      · exact ih.calls
    | publish p _ _ _ | finish p _ _ _ _ _ =>
      constructor
      · exact ih.announcements
      · intro q cmd base todo commands hq a ha
        by_cases he : q = p
        · subst q; simp [WeakUniversal.update] at hq
        · exact ih.gathering q cmd base todo commands
            (by simpa [WeakUniversal.update, he] using hq) a ha
      · exact ih.calls

private theorem proposal_source (base : Seed (n := n) obj)
    (commands : List (Cmd n Op)) (a : Cmd n Op)
    (h : 0 < (WeakUniversal.Tagged obj).traceCount a
      (proposal obj base commands)) :
    a ∈ commands ∨ 0 < (WeakUniversal.Tagged obj).traceCount a base.trace := by
  unfold proposal at h
  let suffix : (WeakUniversal.Tagged (n := n) obj).Trace :=
    Quotient.mk (WeakUniversal.Tagged obj).traceSetoid commands
  change 0 < (WeakUniversal.Tagged obj).traceCount a
    ((WeakUniversal.Tagged obj).traceAppend base.trace suffix) at h
  rw [(WeakUniversal.Tagged obj).traceCount_append a base.trace suffix] at h
  by_cases hb : 0 < (WeakUniversal.Tagged obj).traceCount a base.trace
  · exact Or.inr hb
  · left
    have hs : 0 < (WeakUniversal.Tagged obj).traceCount a suffix := by omega
    change 0 < commands.count a at hs
    exact List.count_pos_iff.mp hs

/-- Every command occurrence in an Algorithm 3 GCA output originates in an
actual invocation, including commands appended by another process's helping
collect. -/
theorem output_occurrence_invoked {H : Environment (n := n) obj}
    (coverage : CallsCovered obj H)
    (spec : ∀ r, (H (r + 1)).Specification) :
    ∀ r p t flag a, (H (r + 1)).output p = some (t, flag) →
      0 < (WeakUniversal.Tagged obj).traceCount a t →
      ∃ c : Configuration (n := n) obj, Reachable obj H c ∧ a ∈ c.invocations := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro p t flag a hout hpos
    have hocc : GCA.History.Occurs
        (obj := WeakUniversal.Tagged (n := n) obj) a 0 t := by
      simpa only [GCA.History.Occurs,
        (WeakUniversal.Tagged obj).traceResponses_length] using hpos
    obtain ⟨s, ⟨q, hinput⟩, hsocc⟩ :=
      (spec r).validity.occurs p t flag hout a 0 hocc
    have hspos : 0 < (WeakUniversal.Tagged obj).traceCount a s := by
      simpa only [GCA.History.Occurs,
        (WeakUniversal.Tagged obj).traceResponses_length] using hsocc
    obtain ⟨c, hc, hcall⟩ := coverage r q s hinput
    obtain ⟨seed, commands, hseed, hcommands, hround, htrace⟩ :=
      (proposal_provenance obj hc).calls _ hcall
    change s = proposal obj seed commands at htrace
    change r + 1 = seed.round + 1 at hround
    rw [htrace] at hspos
    rcases proposal_source obj seed commands a hspos with hcmd | hbase
    · exact ⟨c, hc, hcommands a hcmd⟩
    · rcases hseed with ⟨_, hempty⟩ | ⟨hpositive, q', b, hprev⟩
      · rw [hempty] at hbase
        change 0 < ([] : List (Cmd n Op)).count a at hbase
        simp at hbase
      · have hseedr : seed.round = r := by omega
        have hrpos : 0 < r := by omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hrpos)
        have hklt : k < r := by omega
        have hprev' : (H (k + 1)).output q' = some (seed.trace, b) := by
          have he : seed.round = k + 1 := hseedr.trans hk
          simpa only [he] using hprev
        exact ih k hklt q' seed.trace b a hprev' hbase

end HelpingUniversal
end ConflictFreedom
