import CFLeanProof.UniversalIdentities

/-! Invocation provenance of all program-held traces. The only external step
is receiving a GCA output; its causal provenance is supplied by the protocol
scheduler, rather than assumed for returned traces. -/
namespace ConflictFreedom
namespace Object
variable {State Op Response : Type} (obj : Object State Op Response) [DecidableEq Op]

/-- Every operation occurring in `s` satisfies `I`. -/
def TraceSupportedBy (I : Op → Prop) (s : obj.Trace) : Prop :=
  ∀ a, 0 < obj.traceCount a s → I a

theorem TraceSupportedBy.mono {I J : Op → Prop} {s : obj.Trace}
    (h : obj.TraceSupportedBy I s) (hm : ∀ a, I a → J a) : obj.TraceSupportedBy J s :=
  fun a ha => hm a (h a ha)

theorem traceSupportedBy_empty (I : Op → Prop) : obj.TraceSupportedBy I obj.emptyTrace := by
  intro a ha
  exact False.elim (Nat.not_lt_zero _ ha)

theorem traceSupportedBy_appendMissing {I : Op → Prop} {s : obj.Trace} {cmd : Op}
    (h : obj.TraceSupportedBy I s) (hc : I cmd) :
    obj.TraceSupportedBy I (obj.appendMissing s cmd) := by
  intro a ha
  unfold appendMissing at ha
  split at ha
  · rw [obj.traceCount_append a s (Quotient.mk obj.traceSetoid [cmd])] at ha
    by_cases he : a = cmd
    · exact he.symm ▸ hc
    · have hz : obj.traceCount a (Quotient.mk obj.traceSetoid [cmd]) = 0 := by
        change [cmd].count a = 0
        simp [Ne.symm he]
      rw [hz, Nat.add_zero] at ha
      exact h a ha
  · exact h a ha

end Object

namespace WeakUniversal
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response) [DecidableEq Op]

/-- All locally stored traces and the current command are supported by `I`. -/
def LocalProvenance (I : Cmd n Op → Prop) : Local (n := n) obj → Prop
  | .idle => True
  | .collecting cmd _ s | .ready cmd s => I cmd ∧ (Tagged obj).TraceSupportedBy I s.trace
  | .waiting cmd _ s | .publishing cmd _ s | .returning cmd _ s =>
      I cmd ∧ (Tagged obj).TraceSupportedBy I s

/-- Every trace a configuration of Algorithm 1 holds — locally, in `S`, in a
call or in a response — is supported by `I`. -/
structure Provenance (I : Cmd n Op → Prop) (c : Configuration (n := n) obj) : Prop where
  localState : ∀ p, LocalProvenance obj I (c.localState p)
  slots : ∀ p, (Tagged obj).TraceSupportedBy I (c.slots p).trace
  calls : ∀ call ∈ c.calls, (Tagged obj).TraceSupportedBy I call.trace
  returns : ∀ ret ∈ c.returns, (Tagged obj).TraceSupportedBy I ret.trace

theorem LocalProvenance.mono {I J : Cmd n Op → Prop} {l : Local (n := n) obj}
    (h : LocalProvenance obj I l) (hm : ∀ a, I a → J a) : LocalProvenance obj J l := by
  cases l with
  | idle => trivial
  | collecting | ready | waiting | publishing | returning =>
    exact ⟨hm _ h.1, h.2.mono _ hm⟩

theorem Provenance.mono {I J : Cmd n Op → Prop} {c : Configuration (n := n) obj}
    (h : Provenance obj I c) (hm : ∀ a, I a → J a) : Provenance obj J c :=
  ⟨fun p => (h.localState p).mono obj hm, fun p => (h.slots p).mono _ hm,
    fun call hc => (h.calls call hc).mono _ hm, fun ret hr => (h.returns ret hr).mono _ hm⟩

theorem provenance_initial (I : Cmd n Op → Prop) : Provenance obj I (initial obj) := by
  refine ⟨fun _ => trivial, fun _ => (Tagged obj).traceSupportedBy_empty I, ?_, ?_⟩
  · intro call h; cases h
  · intro ret h; cases h

theorem provenance_update_all {α : Type} (P : α → Prop) {f : Fin n → α}
    (hf : ∀ q, P (f q)) (p : Fin n) (a : α) (ha : P a) :
    ∀ q, P (update f p a q) := by
  intro q
  unfold update
  split
  · exact ha
  · exact hf q

theorem supported_best {I : Cmd n Op → Prop} {s t : Seed (n := n) obj}
    (hs : (Tagged obj).TraceSupportedBy I s.trace)
    (ht : (Tagged obj).TraceSupportedBy I t.trace) :
    (Tagged obj).TraceSupportedBy I (best obj s t).trace := by
  unfold best
  split <;> assumption

/-- A program step preserves provenance if any GCA answer actually consumed
in this step is supported. The scheduler will prove that premise causally. -/
theorem provenance_step {H : Environment (n := n) obj} {I : Cmd n Op → Prop}
    {c d : Configuration (n := n) obj} (hs : Step obj H c d)
    (hc : Provenance obj I c) (hinv : ∀ a ∈ d.invocations, I a)
    (hout : ∀ p cmd r proposal s flag,
      c.localState p = .waiting cmd r proposal → d.localState p ≠ c.localState p →
      (H r).output p = some (s, flag) → (Tagged obj).TraceSupportedBy I s) :
    Provenance obj I d := by
  cases hs with
  | invoke p op h =>
    refine ⟨?_, hc.slots, hc.calls, hc.returns⟩
    apply provenance_update_all _ hc.localState
    exact ⟨hinv _ (List.mem_cons_self ..), (Tagged obj).traceSupportedBy_empty I⟩
  | read p q cmd todo seed h =>
    have hl := hc.localState p
    rw [h] at hl
    refine ⟨?_, hc.slots, hc.calls, hc.returns⟩
    exact provenance_update_all _ hc.localState p _ ⟨hl.1, supported_best obj hl.2 (hc.slots q)⟩
  | collected p cmd seed h =>
    refine ⟨?_, hc.slots, hc.calls, hc.returns⟩
    exact provenance_update_all _ hc.localState p _ (by simpa only [h, LocalProvenance] using hc.localState p)
  | propose p cmd seed h hi =>
    have hl : I cmd ∧ (Tagged obj).TraceSupportedBy I seed.trace := by simpa only [h, LocalProvenance] using hc.localState p
    have hp := (Tagged obj).traceSupportedBy_appendMissing hl.2 hl.1
    refine ⟨provenance_update_all _ hc.localState p _ ⟨hl.1, hp⟩, hc.slots, ?_, hc.returns⟩
    intro call hcall
    rcases List.mem_cons.mp hcall with rfl | hcall
    · exact hp
    · exact hc.calls call hcall
  | receive p cmd r proposal s flag h ho =>
    have hl : I cmd ∧ (Tagged obj).TraceSupportedBy I proposal := by simpa only [h, LocalProvenance] using hc.localState p
    have hout := hout p cmd r proposal s flag h (by
      simp only [update, ite_true, h]
      split <;> simp) ho
    refine ⟨?_, hc.slots, hc.calls, hc.returns⟩
    apply provenance_update_all _ hc.localState
    split <;> exact ⟨hl.1, hout⟩
  | publish p cmd r s h =>
    have hl : I cmd ∧ (Tagged obj).TraceSupportedBy I s := by simpa only [h, LocalProvenance] using hc.localState p
    exact ⟨provenance_update_all _ hc.localState p _ hl,
      provenance_update_all (fun seed : Seed (n := n) obj => (Tagged obj).TraceSupportedBy I seed.trace) hc.slots p _ hl.2, hc.calls, hc.returns⟩
  | finish p cmd r s h =>
    have hl : I cmd ∧ (Tagged obj).TraceSupportedBy I s := by simpa only [h, LocalProvenance] using hc.localState p
    refine ⟨provenance_update_all _ hc.localState p _ trivial, hc.slots, hc.calls, ?_⟩
    intro ret hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hl.2
    · exact hc.returns ret hr

end WeakUniversal
namespace HelpingUniversal
open WeakUniversal (Cmd Tagged Seed Call Return Environment update zeroSeed best)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response) [DecidableEq Op]

/-- All locally stored traces, the current command and the gathered commands
are supported by `I`. -/
def LocalProvenance (I : Cmd n Op → Prop) : Local (n := n) obj → Prop
  | .idle s => (Tagged obj).TraceSupportedBy I s.trace
  | .announcing cmd s | .collecting cmd _ s | .publishing cmd s =>
      I cmd ∧ (Tagged obj).TraceSupportedBy I s.trace
  | .gathering cmd s _ commands =>
      I cmd ∧ (Tagged obj).TraceSupportedBy I s.trace ∧ ∀ a ∈ commands, I a
  | .waiting cmd _ s => I cmd ∧ (Tagged obj).TraceSupportedBy I s
  | .checking cmd s _ seen =>
      I cmd ∧ (Tagged obj).TraceSupportedBy I s.trace ∧ (Tagged obj).TraceSupportedBy I seen.trace

/-- Algorithm 3's `Provenance`, which also covers the announcements in `M`. -/
structure Provenance (I : Cmd n Op → Prop) (c : Configuration (n := n) obj) : Prop where
  localState : ∀ p, LocalProvenance obj I (c.localState p)
  slots : ∀ p, (Tagged obj).TraceSupportedBy I (c.slots p).trace
  announcements : ∀ p a, c.announcements p = some a → I a
  calls : ∀ call ∈ c.calls, (Tagged obj).TraceSupportedBy I call.trace
  returns : ∀ ret ∈ c.returns, (Tagged obj).TraceSupportedBy I ret.trace

theorem LocalProvenance.mono {I J : Cmd n Op → Prop} {l : Local (n := n) obj}
    (h : LocalProvenance obj I l) (hm : ∀ a, I a → J a) : LocalProvenance obj J l := by
  cases l with
  | idle => exact Object.TraceSupportedBy.mono (Tagged obj) h hm
  | announcing | collecting | publishing | waiting => exact ⟨hm _ h.1, h.2.mono _ hm⟩
  | gathering => exact ⟨hm _ h.1, h.2.1.mono _ hm, fun a ha => hm a (h.2.2 a ha)⟩
  | checking => exact ⟨hm _ h.1, h.2.1.mono _ hm, h.2.2.mono _ hm⟩

theorem Provenance.mono {I J : Cmd n Op → Prop} {c : Configuration (n := n) obj}
    (h : Provenance obj I c) (hm : ∀ a, I a → J a) : Provenance obj J c :=
  ⟨fun p => (h.localState p).mono obj hm, fun p => (h.slots p).mono _ hm,
    fun p a ha => hm a (h.announcements p a ha),
    fun call hc => (h.calls call hc).mono _ hm, fun ret hr => (h.returns ret hr).mono _ hm⟩

theorem provenance_initial (I : Cmd n Op → Prop) : Provenance obj I (initial obj) := by
  refine ⟨fun _ => (Tagged obj).traceSupportedBy_empty I,
    fun _ => (Tagged obj).traceSupportedBy_empty I, ?_, ?_, ?_⟩
  · intro p a h; cases h
  · intro call h; cases h
  · intro ret h; cases h

theorem supported_proposal {I : Cmd n Op → Prop} {s : Seed (n := n) obj} {commands : List (Cmd n Op)}
    (hs : (Tagged obj).TraceSupportedBy I s.trace) (hc : ∀ a ∈ commands, I a) :
    (Tagged obj).TraceSupportedBy I (proposal obj s commands) := by
  intro a ha
  rw [proposal, (Tagged obj).traceCount_append a s.trace (Quotient.mk (Tagged obj).traceSetoid commands)] at ha
  by_cases hbase : 0 < (Tagged obj).traceCount a s.trace
  · exact hs a hbase
  · have hlist : 0 < commands.count a := by
      change 0 < (Tagged obj).traceCount a s.trace + commands.count a at ha
      omega
    exact hc a (List.count_pos_iff.mp hlist)

theorem supported_observe {I : Cmd n Op → Prop} {s : Seed (n := n) obj}
    {seen : Option (Cmd n Op)} {commands : List (Cmd n Op)}
    (hs : ∀ a, seen = some a → I a) (hc : ∀ a ∈ commands, I a) :
    ∀ a ∈ observe obj s seen commands, I a := by
  intro a ha
  cases he : seen with
  | none => exact hc a (by simpa [observe, he] using ha)
  | some cmd =>
    simp only [observe, he] at ha
    split at ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact hc a ha
      · have : a = cmd := List.mem_singleton.mp ha
        exact this.symm ▸ hs cmd he
    · exact hc a ha

/-- Helping adds announcement registers and the collected command list to the
same causal provenance invariant. No progress or uniqueness premise is needed. -/
theorem provenance_step {H : Environment (n := n) obj} {I : Cmd n Op → Prop}
    {c d : Configuration (n := n) obj} (hs : Step obj H c d)
    (hc : Provenance obj I c) (hinv : ∀ a ∈ d.invocations, I a)
    (hout : ∀ p cmd r proposal s flag,
      c.localState p = .waiting cmd r proposal → d.localState p ≠ c.localState p →
      (H r).output p = some (s, flag) → (Tagged obj).TraceSupportedBy I s) :
    Provenance obj I d := by
  cases hs with
  | invoke p op seed h =>
    have hl := hc.localState p
    rw [h] at hl
    refine ⟨?_, hc.slots, hc.announcements, hc.calls, hc.returns⟩
    apply WeakUniversal.provenance_update_all _ hc.localState
    exact ⟨hinv _ (List.mem_cons_self ..), hl⟩
  | announce p cmd seed h =>
    have hl : I cmd ∧ (Tagged obj).TraceSupportedBy I seed.trace := by
      simpa only [h, LocalProvenance] using hc.localState p
    refine ⟨WeakUniversal.provenance_update_all _ hc.localState p _ hl,
      hc.slots, ?_, hc.calls, hc.returns⟩
    intro q a ha
    by_cases he : q = p
    · subst q
      have heq : cmd = a := Option.some.inj (by simpa only [update, ite_true] using ha)
      exact heq ▸ hl.1
    · exact hc.announcements q a (by simpa only [update, he, ite_false] using ha)
  | readStart p q cmd todo seed h =>
    have hl := hc.localState p
    rw [h] at hl
    refine ⟨?_, hc.slots, hc.announcements, hc.calls, hc.returns⟩
    exact WeakUniversal.provenance_update_all _ hc.localState p _
      ⟨hl.1, WeakUniversal.supported_best obj hl.2 (hc.slots q)⟩
  | collectedStart p cmd seed h =>
    have hl := hc.localState p
    rw [h] at hl
    refine ⟨?_, hc.slots, hc.announcements, hc.calls, hc.returns⟩
    exact WeakUniversal.provenance_update_all _ hc.localState p _ ⟨hl.1, hl.2, by simp⟩
  | readAnnouncement p q cmd seed todo commands h =>
    have hl := hc.localState p
    rw [h] at hl
    refine ⟨?_, hc.slots, hc.announcements, hc.calls, hc.returns⟩
    exact WeakUniversal.provenance_update_all _ hc.localState p _
      ⟨hl.1, hl.2.1, supported_observe obj (hc.announcements q) hl.2.2⟩
  | propose p cmd seed commands h arranged harr hi =>
    have hl := hc.localState p
    rw [h] at hl
    have hp := supported_proposal obj hl.2.1 (fun a ha => hl.2.2 a (harr.mem_iff.mp ha))
    refine ⟨WeakUniversal.provenance_update_all _ hc.localState p _ ⟨hl.1, hp⟩,
      hc.slots, hc.announcements, ?_, hc.returns⟩
    intro call hcall
    rcases List.mem_cons.mp hcall with rfl | hcall
    · exact hp
    · exact hc.calls call hcall
  | receive p cmd r proposal s flag h ho =>
    have hl := hc.localState p
    rw [h] at hl
    have hout := hout p cmd r proposal s flag h (by
      simp only [update, ite_true, h]
      split <;> simp) ho
    refine ⟨?_, hc.slots, hc.announcements, hc.calls, hc.returns⟩
    apply WeakUniversal.provenance_update_all _ hc.localState
    split
    · exact ⟨hl.1, hout⟩
    · exact ⟨hl.1, hout, (Tagged obj).traceSupportedBy_empty I⟩
  | publish p cmd seed h =>
    have hl := hc.localState p
    rw [h] at hl
    exact ⟨WeakUniversal.provenance_update_all _ hc.localState p _
        ⟨hl.1, hl.2, (Tagged obj).traceSupportedBy_empty I⟩,
      WeakUniversal.provenance_update_all
        (fun seed : Seed (n := n) obj => (Tagged obj).TraceSupportedBy I seed.trace)
        hc.slots p _ hl.2, hc.announcements, hc.calls, hc.returns⟩
  | readCheck p q cmd seed todo seen h =>
    have hl := hc.localState p
    rw [h] at hl
    refine ⟨?_, hc.slots, hc.announcements, hc.calls, hc.returns⟩
    exact WeakUniversal.provenance_update_all _ hc.localState p _
      ⟨hl.1, hl.2.1, WeakUniversal.supported_best obj hl.2.2 (hc.slots q)⟩
  | retry p cmd seed seen h hmissing =>
    have hl := hc.localState p
    rw [h] at hl
    refine ⟨?_, hc.slots, hc.announcements, hc.calls, hc.returns⟩
    exact WeakUniversal.provenance_update_all _ hc.localState p _ ⟨hl.1, hl.2.1, by simp⟩
  | finish p cmd seed seen h hcontains =>
    have hl := hc.localState p
    rw [h] at hl
    refine ⟨WeakUniversal.provenance_update_all _ hc.localState p _ hl.2.1,
      hc.slots, hc.announcements, hc.calls, ?_⟩
    intro ret hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hl.2.2
    · exact hc.returns ret hr

end HelpingUniversal
end ConflictFreedom
