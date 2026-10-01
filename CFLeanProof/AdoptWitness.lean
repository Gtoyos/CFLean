import CFLeanProof.MachineCompute

/-! # Runs that take the adopt branch

The other witness runs (`ProgressWitness`, `HelpingWitness`,
`ContentionWitness`, `WeakContentionWitness`, `SharedRoundWitness`) exercise
commits only: in every one of them a GCA call returns with its commit flag set.  Here are runs in which a caller
**adopts** — GCA hands it `(s, false)` — and the construction then does what its
pseudocode prescribes for that case: Algorithm 1 proposes again (Line 5's loop
does not exit), Algorithm 3 checks `S` and, not finding its command, collects
`M` again (`retry`).

The object is a counter each operation of which conflicts with every other
(`CounterWitness.ctr`), with two processes invoking one operation each.  Their
round-1 proposals are incompatible, so Algorithm 2 lets neither commit: each
caller's `A` scan sees both inputs, the flag `A_i = A_i^co` of line 4 is false,
and the output is the meet `ε` of the two, adopted.

The runs are those of the machines of §1.4 — Algorithm 1 or 3 over Algorithm 2
over atomic snapshots — so they are admitted executions (`forward_admitted`).
They are **computed**: independence is decidable for this object, so the
machines are programs (`MachineCompute`), and the kernel evaluates them step by
step (`decide`).

* Algorithm 1 (`Alg1`): process `0` runs up to its call, then process `1`, then
  they alternate.  Both propose a one-command trace to round 1, both adopt `ε`,
  and process `0`'s next step proposes to round 2.
* Algorithm 3 (`Alg3`): the same, except that the later process collects `M` in
  reverse index order, so it reads its own announcement first.  It proposes
  `c₁ · c₀` — helping the earlier process — against the earlier process's
  `c₀`: incompatible again.  Both adopt `ε`; process `0` then checks `S`, finds
  no trace containing its command, and retries.
-/
namespace ConflictFreedom.AdoptWitness
open Object

/-- The object: a counter, all of whose operations conflict. -/
abbrev obj : Object Nat Nat Nat := CounterWitness.ctr

instance : DecidableRel obj.Independent :=
  fun a b => isFalse (CounterWitness.ctr_totallyConflicting a b)

/-- The object GCA agrees on: traces of commands of two processes. -/
abbrev T := WeakUniversal.Tagged (n := 2) obj

/-- Process `p` invokes operation `p`, every time. -/
def client : Fin 2 → Nat → Nat := fun p _ => p.val

/-- The first commands of the two processes. -/
def c₀ : WeakUniversal.Cmd 2 Nat := ⟨0, 0, 1⟩
def c₁ : WeakUniversal.Cmd 2 Nat := ⟨1, 1, 1⟩

/-- The trace of a list of commands. -/
def tr (l : List (WeakUniversal.Cmd 2 Nat)) : T.Trace := T.ofList l

/-! ## Algorithm 1: adopt, and propose again -/

namespace Alg1
open WeakUniversal

/-- Process `0` for five steps — up to its call to round 1 — then process `1`
for five, then alternately. -/
def sched : Nat → Option (Fin 2) := fun t =>
  some (if t < 5 then 0 else if t < 10 then 1 else if t % 2 = 0 then 0 else 1)

/-- Collect `S` in index order. -/
abbrev ch : Forward.Choices (n := 2) obj := Forward.Choices.inOrder obj

/-- The run, as the computed machine produces it. -/
def run : Nat → Configuration (n := 2) obj × ForwardGCA.GState T 2 :=
  Over.mrun obj (ForwardGCA.machineC T 2) ch client sched

theorem frun_eq : Forward.frun obj ch client sched = run :=
  (Over.mrun_machineC obj ch client sched).symm

/-- `l` is `.waiting c r v`, decided. -/
def isWaiting (l : Local (n := 2) obj) (c : Cmd 2 Nat) (r : Nat) (v : T.Trace) : Bool :=
  match l with
  | .waiting c' r' v' => decide (c' = c) && decide (r' = r) && decide (v' = v)
  | _ => false

theorem eq_of_isWaiting {l : Local (n := 2) obj} {c : Cmd 2 Nat} {r : Nat} {v : T.Trace}
    (h : isWaiting l c r v = true) : l = .waiting c r v := by
  cases l with
  | waiting c' r' v' =>
      simp only [isWaiting, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      rfl
  | _ => simp [isWaiting] at h

/-- `l` is `.ready c ⟨r, s⟩`, decided. -/
def isReady (l : Local (n := 2) obj) (c : Cmd 2 Nat) (r : Nat) (s : T.Trace) : Bool :=
  match l with
  | .ready c' b => decide (c' = c) && decide (b.round = r) && decide (b.trace = s)
  | _ => false

theorem eq_of_isReady {l : Local (n := 2) obj} {c : Cmd 2 Nat} {r : Nat} {s : T.Trace}
    (h : isReady l c r s = true) : l = .ready c ⟨r, s⟩ := by
  cases l with
  | ready c' b =>
      simp only [isReady, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hr⟩, hs⟩ := h
      rw [← hr, ← hs]
  | _ => simp [isReady] at h

/-- **Algorithm 1 takes the adopt branch, and proposes again.**  At step 22
process `0` is inside its round-1 call with proposal `c₀`; round 1 of the GCA
family reconstructed from the run answers it `(ε, false)`; the receive keeps it
in the loop of Line 5, ready from `(1, ε)`; and its next step proposes `c₀` to
round 2. -/
theorem adopts :
    (Forward.frun obj ch client sched 22).1.localState 0 = .waiting c₀ 1 (tr [c₀]) ∧
    ((Forward.fam obj ch client sched).environment obj 1).output 0 = some (tr [], false) ∧
    (Forward.frun obj ch client sched 23).1.localState 0 = .ready c₀ ⟨1, tr []⟩ ∧
    (Forward.frun obj ch client sched 25).1.localState 0 = .waiting c₀ 2 (tr [c₀]) := by
  have h22 : (Forward.frun obj ch client sched 22).1.localState 0 = .waiting c₀ 1 (tr [c₀]) := by
    rw [frun_eq]
    exact eq_of_isWaiting (by decide)
  refine ⟨h22, ?_, ?_, ?_⟩
  · have hph : ¬ ((Forward.frun obj ch client sched 22).2.frame 0).phase < 6 := by
      rw [frun_eq]
      decide
    have hw : Forward.fwr obj ch client sched 22 0 = some 1 := by
      show GlobalSchedule.weakRound obj _ = _
      rw [h22]
      rfl
    have hv : Forward.fwv obj ch client sched 22 0 = tr [c₀] := by
      show Forward.waitProp obj _ = _
      rw [h22]
      rfl
    have hout := ForwardGCA.output_agrees (Forward.driven obj ch client sched) hw hph
    rw [hv, ForwardGCA.frameOutput_eq] at hout
    have hval : ForwardGCA.frameOutputC T 2 ((Forward.frun obj ch client sched 22).2.frame 0)
        (tr [c₀]) = (tr [], false) := by
      rw [frun_eq]
      decide
    rw [Forward.env_eq, hout, hval]
  · rw [frun_eq]
    exact eq_of_isReady (by decide)
  · rw [frun_eq]
    exact eq_of_isWaiting (by decide)

/-- The run never halts, so it is an admitted execution of Algorithm 1. -/
theorem live : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome := fun N => ⟨N, Nat.le_refl _, rfl⟩

theorem admitted :
    algorithm1 obj 2 ((Forward.fsched obj ch client sched).execution
      (Forward.fsched_opLive obj ch client sched live)) :=
  Forward.forward_admitted obj ch client sched live

end Alg1

/-! ## Algorithm 3: adopt, check `S`, and retry -/

namespace Alg3
open HelpingUniversal
open WeakUniversal (Cmd zeroSeed)

/-- Process `0` for eight steps — up to its call to round 1 — then process `1`
for eight, then alternately. -/
def sched : Nat → Option (Fin 2) := fun t =>
  some (if t < 8 then 0 else if t < 16 then 1 else if t % 2 = 0 then 0 else 1)

/-- Collect `S` in index order and `M` in reverse index order; arrange
`trace(M_i)` in the order read. -/
def ch : Forward.Choices (n := 2) obj where
  slotOrder := fun _ _ => List.finRange 2
  slotOrder_perm := fun _ _ => List.Perm.refl _
  announcementOrder := fun _ _ => (List.finRange 2).reverse
  announcementOrder_perm := fun _ _ => List.reverse_perm _
  arrange := fun _ _ l => l
  arrange_perm := fun _ _ _ => List.Perm.refl _

/-- The run, as the computed machine produces it. -/
def run : Nat → Configuration (n := 2) obj × ForwardGCA.GState T 2 :=
  Over.mrun obj (ForwardGCA.machineC T 2) ch client sched

theorem frun_eq : Forward.frun obj ch client sched = run :=
  (Over.mrun_machineC obj ch client sched).symm

/-- `l` is `.waiting c r v`, decided. -/
def isWaiting (l : Local (n := 2) obj) (c : Cmd 2 Nat) (r : Nat) (v : T.Trace) : Bool :=
  match l with
  | .waiting c' r' v' => decide (c' = c) && decide (r' = r) && decide (v' = v)
  | _ => false

theorem eq_of_isWaiting {l : Local (n := 2) obj} {c : Cmd 2 Nat} {r : Nat} {v : T.Trace}
    (h : isWaiting l c r v = true) : l = .waiting c r v := by
  cases l with
  | waiting c' r' v' =>
      simp only [isWaiting, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      rfl
  | _ => simp [isWaiting] at h

/-- `l` is `.checking c ⟨r, s⟩ todo seen`, decided. -/
def isChecking (l : Local (n := 2) obj) (c : Cmd 2 Nat) (r : Nat) (s : T.Trace)
    (todo : List (Fin 2)) (seen : WeakUniversal.Seed (n := 2) obj) : Bool :=
  match l with
  | .checking c' b todo' seen' =>
      decide (c' = c) && decide (b.round = r) && decide (b.trace = s) && decide (todo' = todo) &&
        decide (seen'.round = seen.round) && decide (seen'.trace = seen.trace)
  | _ => false

theorem eq_of_isChecking {l : Local (n := 2) obj} {c : Cmd 2 Nat} {r : Nat} {s : T.Trace}
    {todo : List (Fin 2)} {seen : WeakUniversal.Seed (n := 2) obj}
    (h : isChecking l c r s todo seen = true) : l = .checking c ⟨r, s⟩ todo seen := by
  cases l with
  | checking c' b todo' seen' =>
      simp only [isChecking, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨rfl, hr⟩, hs⟩, rfl⟩, hsr⟩, hst⟩ := h
      cases b
      cases seen
      cases seen'
      simp_all
  | _ => simp [isChecking] at h

/-- `l` is `.gathering c ⟨r, s⟩ todo commands`, decided. -/
def isGathering (l : Local (n := 2) obj) (c : Cmd 2 Nat) (r : Nat) (s : T.Trace)
    (todo : List (Fin 2)) (commands : List (Cmd 2 Nat)) : Bool :=
  match l with
  | .gathering c' b todo' commands' =>
      decide (c' = c) && decide (b.round = r) && decide (b.trace = s) && decide (todo' = todo) &&
        decide (commands' = commands)
  | _ => false

theorem eq_of_isGathering {l : Local (n := 2) obj} {c : Cmd 2 Nat} {r : Nat} {s : T.Trace}
    {todo : List (Fin 2)} {commands : List (Cmd 2 Nat)}
    (h : isGathering l c r s todo commands = true) : l = .gathering c ⟨r, s⟩ todo commands := by
  cases l with
  | gathering c' b todo' commands' =>
      simp only [isGathering, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨rfl, hr⟩, hs⟩, rfl⟩, rfl⟩ := h
      rw [← hr, ← hs]
  | _ => simp [isGathering] at h

/-- **Algorithm 3 takes the adopt branch, checks `S`, and retries.**  At step 28
both processes are inside their round-1 calls: process `0` proposed `c₀`, and
process `1`, having read both announcements, proposed `c₁ · c₀`.  Round 1 of the
reconstructed GCA family answers process `0` `(ε, false)`; the receive starts
the collect of `S` of Line 16 from `(1, ε)`; and after reading both registers,
none of which holds a trace with `c₀`, process `0` retries: at step 35 it is
collecting `M` again, in the rule's order, from `(1, ε)`. -/
theorem retries :
    (Forward.frun obj ch client sched 28).1.localState 0 = .waiting c₀ 1 (tr [c₀]) ∧
    (Forward.frun obj ch client sched 28).1.localState 1 = .waiting c₁ 1 (tr [c₁, c₀]) ∧
    ((Forward.fam obj ch client sched).environment obj 1).output 0 = some (tr [], false) ∧
    (Forward.frun obj ch client sched 29).1.localState 0 =
      .checking c₀ ⟨1, tr []⟩ (List.finRange 2) (zeroSeed obj) ∧
    (Forward.frun obj ch client sched 35).1.localState 0 =
      .gathering c₀ ⟨1, tr []⟩ (List.finRange 2).reverse [] := by
  have h28 : (Forward.frun obj ch client sched 28).1.localState 0 = .waiting c₀ 1 (tr [c₀]) := by
    rw [frun_eq]
    exact eq_of_isWaiting (by decide)
  refine ⟨h28, ?_, ?_, ?_, ?_⟩
  · rw [frun_eq]
    exact eq_of_isWaiting (by decide)
  · have hph : ¬ ((Forward.frun obj ch client sched 28).2.frame 0).phase < 6 := by
      rw [frun_eq]
      decide
    have hw : Forward.fwr obj ch client sched 28 0 = some 1 := by
      show GlobalSchedule.helpingRound obj _ = _
      rw [h28]
      rfl
    have hv : Forward.fwv obj ch client sched 28 0 = tr [c₀] := by
      show Forward.waitProp obj _ = _
      rw [h28]
      rfl
    have hout := ForwardGCA.output_agrees (Forward.driven obj ch client sched) hw hph
    rw [hv, ForwardGCA.frameOutput_eq] at hout
    have hval : ForwardGCA.frameOutputC T 2 ((Forward.frun obj ch client sched 28).2.frame 0)
        (tr [c₀]) = (tr [], false) := by
      rw [frun_eq]
      decide
    rw [Forward.env_eq, hout, hval]
  · rw [frun_eq]
    exact eq_of_isChecking (by decide)
  · rw [frun_eq]
    exact eq_of_isGathering (by decide)

/-- The run never halts, so it is an admitted execution of Algorithm 3. -/
theorem live : ∀ N, ∃ t, N ≤ t ∧ (sched t).isSome := fun N => ⟨N, Nat.le_refl _, rfl⟩

theorem admitted :
    algorithm3 obj 2 ((Forward.fsched obj ch client sched).execution
      (Forward.fsched_opLive obj ch client sched live)) :=
  Forward.forward_admitted obj ch client sched live

end Alg3
end ConflictFreedom.AdoptWitness
