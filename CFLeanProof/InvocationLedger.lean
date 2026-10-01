import CFLeanProof.Commands

/-! Shared invocation bookkeeping for both universal constructions. This small
transition system isolates fresh process/sequence tags and exactly-once response
recording from trace semantics and GCA correctness. -/
namespace ConflictFreedom

namespace Command
variable {P Op : Type}
/-- A command's identity, its process and sequence number. -/
def key (cmd : Command P Op) : P × Nat := (cmd.process, cmd.sequence)
end Command

namespace InvocationLedger
variable {P Op : Type} [DecidableEq P]

/-- Each process's sequence counter and active command, and the commands
invoked and returned so far, most recent first. -/
structure State (P Op : Type) where
  sequence : P → Nat
  active : P → Option (Command P Op)
  invoked : List (Command P Op)
  returned : List (Command P Op)

/-- Point update of a per-process array: `p` gets `v`. -/
def update {α : Type} (f : P → α) (p : P) (v : α) : P → α :=
  fun q => if q = p then v else f q

/-- No process active, nothing invoked or returned. -/
def initial : State P Op := ⟨fun _ => 0, fun _ => none, [], []⟩

/-- `p` invokes `op` as its next command, which becomes active. -/
def invoke (s : State P Op) (p : P) (op : Op) : State P Op :=
  let cmd : Command P Op := ⟨op, p, s.sequence p + 1⟩
  ⟨update s.sequence p (s.sequence p + 1), update s.active p (some cmd), cmd :: s.invoked, s.returned⟩

/-- `p`'s command `cmd` returns: it is recorded and `p` becomes idle. -/
def finish (s : State P Op) (p : P) (cmd : Command P Op) : State P Op :=
  ⟨s.sequence, update s.active p none, s.invoked, cmd :: s.returned⟩

/-- The ledger invariant: active commands are tagged by their process's current
sequence number and have not returned, and invoked identities are fresh. -/
structure Valid (s : State P Op) : Prop where
  active_tag : ∀ p cmd, s.active p = some cmd →
    cmd.process = p ∧ cmd.sequence = s.sequence p ∧ cmd ∈ s.invoked
  active_pending : ∀ p cmd, s.active p = some cmd →
    ∀ old ∈ s.returned, old.key ≠ cmd.key
  invoked_bound : ∀ cmd ∈ s.invoked, cmd.sequence ≤ s.sequence cmd.process
  invoked_unique : (s.invoked.map Command.key).Nodup
  returned_invoked : ∀ cmd ∈ s.returned, cmd ∈ s.invoked
  returned_unique : (s.returned.map Command.key).Nodup

omit [DecidableEq P] in
theorem initial_valid : Valid (initial : State P Op) := by
  constructor <;> simp [initial]

theorem valid_invoke {s : State P Op} (hs : Valid s) (p : P) (op : Op)
    (_hidle : s.active p = none) : Valid (invoke s p op) := by
  let cmd : Command P Op := ⟨op, p, s.sequence p + 1⟩
  have fresh : ∀ old ∈ s.invoked, old.key ≠ cmd.key := by
    intro old hold he
    have hp := congrArg Prod.fst he
    have hseq := congrArg Prod.snd he
    have hb := hs.invoked_bound old hold
    change old.process = p at hp
    change old.sequence = s.sequence p + 1 at hseq
    rw [hp] at hb
    omega
  have mono : ∀ q, s.sequence q ≤ update s.sequence p (s.sequence p + 1) q := by
    intro q
    unfold update
    split <;> simp_all
  constructor
  · intro q a ha
    change update s.active p (some cmd) q = some a at ha
    by_cases he : q = p
    · subst q
      have hac : cmd = a := Option.some.inj (by simpa [update] using ha)
      subst a
      exact ⟨rfl, by simp [invoke, update, cmd], by simp [invoke, cmd]⟩
    · have old : s.active q = some a := by simpa [update, he] using ha
      obtain ⟨hp, hseq, hin⟩ := hs.active_tag q a old
      exact ⟨hp, by simpa [invoke, update, he] using hseq, List.mem_cons_of_mem _ hin⟩
  · intro q a ha old hold
    change update s.active p (some cmd) q = some a at ha
    by_cases he : q = p
    · subst q
      have hac : cmd = a := Option.some.inj (by simpa [update] using ha)
      subst a
      exact fresh old (hs.returned_invoked old hold)
    · exact hs.active_pending q a (by simpa [update, he] using ha) old hold
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simp [invoke, update]
    · exact Nat.le_trans (hs.invoked_bound a ha) (mono a.process)
  · change (cmd.key :: s.invoked.map Command.key).Nodup
    apply List.nodup_cons.mpr
    refine ⟨?_, hs.invoked_unique⟩
    intro h
    obtain ⟨old, hold, he⟩ := List.mem_map.mp h
    exact fresh old hold he
  · intro a ha
    exact List.mem_cons_of_mem _ (hs.returned_invoked a ha)
  · exact hs.returned_unique

theorem valid_finish {s : State P Op} (hs : Valid s) (p : P) (cmd : Command P Op)
    (hactive : s.active p = some cmd) : Valid (finish s p cmd) := by
  obtain ⟨howner, hseq, hin⟩ := hs.active_tag p cmd hactive
  constructor
  · intro q a ha
    change update s.active p none q = some a at ha
    have hne : q ≠ p := by intro he; subst q; simp [update] at ha
    exact hs.active_tag q a (by simpa [update, hne] using ha)
  · intro q a ha old hold
    change update s.active p none q = some a at ha
    have hne : q ≠ p := by intro he; subst q; simp [update] at ha
    have hqa : s.active q = some a := by simpa [update, hne] using ha
    rcases List.mem_cons.mp hold with rfl | hold
    · intro he
      have heowner := congrArg Prod.fst he
      have hownerq := (hs.active_tag q a hqa).1
      simp only [Command.key] at heowner
      exact hne (hownerq.symm.trans (heowner.symm.trans howner))
    · exact hs.active_pending q a hqa old hold
  · exact hs.invoked_bound
  · exact hs.invoked_unique
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hin
    · exact hs.returned_invoked a ha
  · apply List.nodup_cons.mpr
    refine ⟨?_, hs.returned_unique⟩
    intro h
    obtain ⟨old, hold, he⟩ := List.mem_map.mp h
    exact hs.active_pending p cmd hactive old hold he

omit [DecidableEq P] in
/-- Keys identify a unique invocation, including its operation payload. -/
theorem key_injective {s : State P Op} (hs : Valid s) {a b : Command P Op}
    (ha : a ∈ s.invoked) (hb : b ∈ s.invoked) (he : a.key = b.key) : a = b := by
  have general : ∀ L : List (Command P Op), (L.map Command.key).Nodup →
      ∀ a ∈ L, ∀ b ∈ L, a.key = b.key → a = b := by
    intro L
    induction L with
    | nil => simp
    | cons c L ih =>
      intro hn a ha b hb he
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
      · rfl
      · exact False.elim (hnot (List.mem_map.mpr ⟨b, hbTail, he.symm⟩))
      · exact False.elim (hnot (List.mem_map.mpr ⟨a, haTail, he⟩))
      · exact ih htail a haTail b hbTail he
  exact general _ hs.invoked_unique a ha b hb he

end InvocationLedger
end ConflictFreedom
