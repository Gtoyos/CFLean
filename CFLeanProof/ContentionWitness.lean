import CFLeanProof.Algorithm3ConflictFree

/-! # A run of Algorithm 3 with two operations concurrently in flight

The witnesses in `ProgressWitness` and `HelpingWitness` run a single worker with
idle bystanders, so they never place two operations in flight and never put a
command into the announcement array that the worker did not invoke itself.  This
module supplies a run that does both, over two processes:

* process `1` invokes and announces once, and then takes no further step.  Its
  operation is pending for the whole run — the faulty-process case the helping
  mechanism exists for;
* process `0` cycles forever, and its `M` collect therefore gathers process
  `1`'s command as well as its own.  Round `1` commits *both*.

So the run has two operations simultaneously in flight, the announcement array
is non-trivial, and the conflict hypothesis of §3 has a real pair to range over.
-/

namespace ConflictFreedom.GlobalSchedule.WitnessC
open HelpingUniversal
open UniversalProtocol
open WeakUniversal (Cmd Tagged Seed Call Return update zeroSeed best)

variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op] (op : Op)

/-- The worker's `(k+1)`-st command. -/
def wcmd (k : Nat) : Cmd 2 Op := ⟨op, 0, k + 1⟩

/-- The second process's single command. -/
def ocmd : Cmd 2 Op := ⟨op, 1, 1⟩

omit [DecidableEq Op] in
theorem wcmd_ne_ocmd (k : Nat) : wcmd op k ≠ ocmd op := by
  intro h
  exact absurd (congrArg Command.process h) (by simp [wcmd, ocmd])

omit [DecidableEq Op] in
theorem ocmd_ne_wcmd (k : Nat) : ocmd op ≠ wcmd op k := (wcmd_ne_ocmd op k).symm

omit [DecidableEq Op] in
theorem wcmd_eq_iff (j k : Nat) : wcmd op j = wcmd op k ↔ j = k := by
  constructor
  · intro h
    have := congrArg Command.sequence h
    simp only [wcmd] at this
    omega
  · intro h; rw [h]

/-- The commands committed by round `k`.  Round `1` commits the worker's first
command together with the announced command of the stalled process. -/
def wlist : Nat → List (Cmd 2 Op)
  | 0 => []
  | 1 => [wcmd op 0, ocmd op]
  | (k + 2) => wlist (k + 1) ++ [wcmd op (k + 1)]

noncomputable def wtr (k : Nat) : (Tagged (n := 2) obj).Trace :=
  Quotient.mk _ (wlist op k)

theorem count_wcmd (j : Nat) : ∀ k, (wlist op k).count (wcmd op j)
    = if j < k then 1 else 0
  | 0 => by simp [wlist]
  | 1 => by
      by_cases hj : j = 0
      · subst hj
        simp [wlist, ocmd_ne_wcmd]
      · have hne : wcmd op j ≠ wcmd op 0 := by rw [Ne, wcmd_eq_iff]; exact hj
        have hlt : ¬ (j < 1) := by omega
        simp [wlist, Ne.symm hne, ocmd_ne_wcmd, hlt]
  | (k + 2) => by
      have ih := count_wcmd j (k + 1)
      by_cases hj : j = k + 1
      · subst hj
        simp [wlist, List.count_append, ih]
      · have hne : wcmd op j ≠ wcmd op (k + 1) := by rw [Ne, wcmd_eq_iff]; exact hj
        simp only [wlist, List.count_append, ih, List.count_cons, List.count_nil,
          Nat.zero_add]
        by_cases hlt : j < k + 1
        · have h2 : j < k + 2 := by omega
          simp [hlt, h2, Ne.symm hne]
        · have h2 : ¬ (j < k + 2) := by omega
          simp [hlt, h2, Ne.symm hne]

theorem count_ocmd : ∀ k, (wlist op k).count (ocmd op) = if 0 < k then 1 else 0
  | 0 => by simp [wlist]
  | 1 => by simp [wlist, wcmd_ne_ocmd]
  | (k + 2) => by
      have ih := count_ocmd (k + 1)
      simp only [wlist, List.count_append, ih, List.count_singleton]
      simp [wcmd_ne_ocmd]

theorem traceCount_wtr_wcmd (j k : Nat) :
    (Tagged (n := 2) obj).traceCount (wcmd op j) (wtr obj op k)
      = if j < k then 1 else 0 := count_wcmd op j k

theorem traceCount_wtr_ocmd (k : Nat) :
    (Tagged (n := 2) obj).traceCount (ocmd op) (wtr obj op k)
      = if 0 < k then 1 else 0 := count_ocmd op k

/-- The seed committed by round `k`. -/
noncomputable def wsd (k : Nat) : Seed (n := 2) obj := ⟨k, wtr obj op k⟩

/-! ### State components

Process `1` is parked in its start collect forever; only process `0` moves. -/

/-- The stalled process's parked local state. -/
noncomputable def park : Local (n := 2) obj :=
  .collecting (ocmd op) (List.finRange 2) (zeroSeed obj)

noncomputable def wloc (l : Local (n := 2) obj) : Fin 2 → Local (n := 2) obj :=
  fun q => if q = 0 then l else park obj op

def wseq (k : Nat) : Fin 2 → Nat := fun q => if q = 0 then k else 1

/-- What process `0` had announced before cycle `k`. -/
def wprev : Nat → Option (Cmd 2 Op)
  | 0 => none
  | (k + 1) => some (wcmd op k)

def wann (k : Nat) : Fin 2 → Option (Cmd 2 Op) :=
  fun q => if q = 0 then wprev op k else some (ocmd op)

noncomputable def wslots (k : Nat) : Fin 2 → Seed (n := 2) obj :=
  fun q => if q = 0 then wsd obj op k else zeroSeed obj

def winv : Nat → List (Cmd 2 Op)
  | 0 => [ocmd op]
  | (k + 1) => wcmd op k :: winv k

noncomputable def wcalls : Nat → List (Call (n := 2) obj)
  | 0 => []
  | (k + 1) => ⟨k + 1, 0, wtr obj op (k + 1)⟩ :: wcalls k

noncomputable def wrets : Nat → List (Return (n := 2) obj)
  | 0 => []
  | (k + 1) => ⟨wcmd op k, k + 1, wtr obj op (k + 1)⟩ :: wrets k

/-- The commands process `0` gathers in cycle `k`: its own, plus the stalled
process's on the first cycle, when that command is not yet committed. -/
def wcmds (k : Nat) : List (Cmd 2 Op) :=
  if k = 0 then [wcmd op 0, ocmd op] else [wcmd op k]

omit [DecidableEq Op] in
theorem wloc_zero (l : Local (n := 2) obj) : wloc obj op l 0 = l := by simp [wloc]

omit [DecidableEq Op] in
theorem wloc_one (l : Local (n := 2) obj) : wloc obj op l 1 = park obj op := by
  simp [wloc]

omit [DecidableEq Op] in
theorem update_wloc (l v : Local (n := 2) obj) :
    update (wloc obj op l) 0 v = wloc obj op v := by
  funext q
  by_cases h : q = 0 <;> simp [update, wloc, h]

omit [DecidableEq Op] in
theorem update_wseq (k : Nat) : update (wseq k) 0 (k + 1) = wseq (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [update, wseq, h]

omit [DecidableEq Op] in
theorem update_wann (k : Nat) :
    update (wann op k) 0 (some (wcmd op k)) = wann op (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [update, wann, wprev, h]

omit [DecidableEq Op] in
theorem update_wslots (k : Nat) :
    update (wslots obj op k) 0 (wsd obj op (k + 1)) = wslots obj op (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [update, wslots, h]

omit [DecidableEq Op] in
/-- The proposal process `0` builds in cycle `k` is exactly the trace committed
in round `k + 1`: on the first cycle it carries the stalled process's command
too. -/
theorem proposal_eq (k : Nat) :
    proposal obj (wsd obj op k) (wcmds op k) = wtr obj op (k + 1) := by
  show (Tagged (n := 2) obj).traceAppend (wtr obj op k)
    (Quotient.mk _ (wcmds op k)) = wtr obj op (k + 1)
  
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · show (Quotient.mk _ ((wlist op 0) ++ (wcmds op 0)) : (Tagged (n := 2) obj).Trace)
      = Quotient.mk _ (wlist op 1)
    simp [wlist, wcmds]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    show (Quotient.mk _ ((wlist op (j + 1)) ++ (wcmds op (j + 1))) :
      (Tagged (n := 2) obj).Trace) = Quotient.mk _ (wlist op (j + 2))
    simp [wlist, wcmds]

/-! ### The GCA family: one participant per positive round -/

noncomputable def wfam : Family (n := 2) obj where
  protocol := fun r =>
    { participants := if r = 0 then [] else [0]
      input := fun _ => wtr obj op r
      actor := fun _ => if r = 0 then none else some 0
      actor_valid := by
        intro t p h
        by_cases hr : r = 0
        · simp [hr] at h
        · simp [hr] at h ⊢
          exact h.symm
      acknowledged := fun _ => true }

omit [DecidableEq Op] in
theorem wfam_waitFree : (wfam obj op).SnapshotWaitFree obj :=
  fun _ => GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)

theorem wfam_input (r : Nat) (hr : r ≠ 0) :
    ((wfam obj op).environment obj r).input 0 = some (wtr obj op r) := by
  simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
    GCA.TimedExecution.views, GCA.SnapshotExecution.history, wfam, hr]

theorem wfam_input_none (r : Nat) {p : Fin 2} (hp : p ≠ 0) :
    ((wfam obj op).environment obj r).input p = none := by
  by_cases hr : r = 0 <;>
    simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
      GCA.TimedExecution.views, GCA.SnapshotExecution.history, wfam, hr, hp]

theorem wfam_output (r : Nat) (hr : r ≠ 0) :
    ((wfam obj op).environment obj r).output 0 = some (wtr obj op r, true) := by
  have hw : ((wfam obj op).protocol r).SnapshotWaitFree :=
    GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)
  have hinf : ((wfam obj op).protocol r).InfiniteSteps 0 :=
    fun N => ⟨N, Nat.le_refl _, by simp [wfam, hr]⟩
  obtain ⟨s, flag, ho⟩ := ((wfam obj op).protocol r).returned_of_infiniteSteps hw hinf
  have huniform : ∀ u, (((wfam obj op).environment obj r).Inputs u) → u = wtr obj op r := by
    intro u hu
    rw [Family.environment, GCA.Protocol.history, GCA.SnapshotExecution.inputs_iff] at hu
    obtain ⟨p, -, he⟩ := hu
    exact he.symm
  obtain ⟨rfl, rfl⟩ := (((wfam obj op).environment obj r).uniform_return
    ((wfam obj op).specification obj r) huniform ho)
  exact ho

/-! ### The collects and the gather -/

omit [DecidableEq Op] in
theorem finRange_two : List.finRange 2 = [(0 : Fin 2), 1] := by decide

omit [DecidableEq Op] in
theorem best_start_zero (k : Nat) :
    best obj (wsd obj op k) (wslots obj op k 0) = wsd obj op k := by
  simp [best, wslots, wsd]

omit [DecidableEq Op] in
theorem best_check_zero (k : Nat) :
    best obj (zeroSeed obj) (wslots obj op (k + 1) 0) = wsd obj op (k + 1) := by
  simp [best, wslots, zeroSeed, wsd]

omit [DecidableEq Op] in
theorem best_check_one (k : Nat) :
    best obj (wsd obj op (k + 1)) (wslots obj op (k + 1) 1) = wsd obj op (k + 1) := by
  simp [best, wslots, zeroSeed, wsd]

theorem observe_zero (k : Nat) :
    observe obj (wsd obj op k) (wann op (k + 1) 0) [] = [wcmd op k] := by
  have hc : (Tagged (n := 2) obj).traceCount (wcmd op k) (wtr obj op k) = 0 := by
    rw [traceCount_wtr_wcmd]; simp
  simp [observe, wann, wprev, hc, wsd]

theorem observe_one (k : Nat) :
    observe obj (wsd obj op k) (wann op (k + 1) 1) [wcmd op k] = wcmds op k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hc : (Tagged (n := 2) obj).traceCount (ocmd op) (wtr obj op 0) = 0 := by
      rw [traceCount_wtr_ocmd]; simp
    simp [observe, wann, hc, wcmds, wsd]
  · have hc : (Tagged (n := 2) obj).traceCount (ocmd op) (wtr obj op k) = 1 := by
      rw [traceCount_wtr_ocmd]; simp [hk]
    have hk' : k ≠ 0 := by omega
    simp [observe, wann, hc, wcmds, hk', wsd]

/-! ### The cycle's configurations -/

noncomputable def a0 (k : Nat) : Configuration (n := 2) obj where
  sequence := wseq k
  localState := wloc obj op (.idle (wsd obj op k))
  slots := wslots obj op k
  announcements := wann op k
  calls := wcalls obj op k
  returns := wrets obj op k
  invocations := winv op k

noncomputable def a1 (k : Nat) : Configuration (n := 2) obj :=
  { a0 obj op k with
    sequence := wseq (k + 1)
    localState := wloc obj op (.announcing (wcmd op k) (wsd obj op k))
    invocations := winv op (k + 1) }

noncomputable def a2 (k : Nat) : Configuration (n := 2) obj :=
  { a1 obj op k with
    announcements := wann op (k + 1)
    localState := wloc obj op (.collecting (wcmd op k) (List.finRange 2) (wsd obj op k)) }

noncomputable def a3 (k : Nat) : Configuration (n := 2) obj :=
  { a2 obj op k with
    localState := wloc obj op (.collecting (wcmd op k) [1] (wsd obj op k)) }

noncomputable def a4 (k : Nat) : Configuration (n := 2) obj :=
  { a2 obj op k with
    localState := wloc obj op (.collecting (wcmd op k) [] (wsd obj op k)) }

noncomputable def a5 (k : Nat) : Configuration (n := 2) obj :=
  { a2 obj op k with
    localState := wloc obj op (.gathering (wcmd op k) (wsd obj op k) (List.finRange 2) []) }

noncomputable def a6 (k : Nat) : Configuration (n := 2) obj :=
  { a2 obj op k with
    localState := wloc obj op
      (.gathering (wcmd op k) (wsd obj op k) [1] [wcmd op k]) }

noncomputable def a7 (k : Nat) : Configuration (n := 2) obj :=
  { a2 obj op k with
    localState := wloc obj op
      (.gathering (wcmd op k) (wsd obj op k) [] (wcmds op k)) }

noncomputable def a8 (k : Nat) : Configuration (n := 2) obj :=
  { a2 obj op k with
    localState := wloc obj op (.waiting (wcmd op k) (k + 1) (wtr obj op (k + 1)))
    calls := wcalls obj op (k + 1) }

noncomputable def a9 (k : Nat) : Configuration (n := 2) obj :=
  { a8 obj op k with
    localState := wloc obj op (.publishing (wcmd op k) (wsd obj op (k + 1))) }

noncomputable def a10 (k : Nat) : Configuration (n := 2) obj :=
  { a8 obj op k with
    slots := wslots obj op (k + 1)
    localState := wloc obj op
      (.checking (wcmd op k) (wsd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) }

noncomputable def a11 (k : Nat) : Configuration (n := 2) obj :=
  { a10 obj op k with
    localState := wloc obj op
      (.checking (wcmd op k) (wsd obj op (k + 1)) [1] (wsd obj op (k + 1))) }

noncomputable def a12 (k : Nat) : Configuration (n := 2) obj :=
  { a10 obj op k with
    localState := wloc obj op
      (.checking (wcmd op k) (wsd obj op (k + 1)) [] (wsd obj op (k + 1))) }

omit [DecidableEq Op] in

/-! ### Projections -/

omit [DecidableEq Op] in
theorem wseq_zero (k : Nat) : wseq k 0 = k := by simp [wseq]

section Proj
omit [DecidableEq Op]
variable (k : Nat)

theorem a0_seq : (a0 obj op k).sequence = wseq k := rfl
theorem a0_inv : (a0 obj op k).invocations = winv op k := rfl
theorem a0_slots : (a0 obj op k).slots = wslots obj op k := rfl
theorem a0_ann : (a0 obj op k).announcements = wann op k := rfl
theorem a0_localState : (a0 obj op k).localState = wloc obj op (.idle (wsd obj op k)) := rfl
theorem a0_local : (a0 obj op k).localState 0 = .idle (wsd obj op k) := wloc_zero obj op _
theorem a1_ann : (a1 obj op k).announcements = wann op k := rfl
theorem a1_localState : (a1 obj op k).localState
    = wloc obj op (.announcing (wcmd op k) (wsd obj op k)) := rfl
theorem a1_local : (a1 obj op k).localState 0
    = .announcing (wcmd op k) (wsd obj op k) := wloc_zero obj op _
theorem a2_slots : (a2 obj op k).slots = wslots obj op k := rfl
theorem a2_localState : (a2 obj op k).localState
    = wloc obj op (.collecting (wcmd op k) (List.finRange 2) (wsd obj op k)) := rfl
theorem a3_localState : (a3 obj op k).localState
    = wloc obj op (.collecting (wcmd op k) [1] (wsd obj op k)) := rfl
theorem a4_local : (a4 obj op k).localState 0
    = .collecting (wcmd op k) [] (wsd obj op k) := wloc_zero obj op _
theorem a4_localState : (a4 obj op k).localState
    = wloc obj op (.collecting (wcmd op k) [] (wsd obj op k)) := rfl
theorem a5_ann : (a5 obj op k).announcements = wann op (k + 1) := rfl
theorem a5_localState : (a5 obj op k).localState
    = wloc obj op (.gathering (wcmd op k) (wsd obj op k) (List.finRange 2) []) := rfl
theorem a6_ann : (a6 obj op k).announcements = wann op (k + 1) := rfl
theorem a6_localState : (a6 obj op k).localState
    = wloc obj op (.gathering (wcmd op k) (wsd obj op k) [1] [wcmd op k]) := rfl
theorem a7_local : (a7 obj op k).localState 0
    = .gathering (wcmd op k) (wsd obj op k) [] (wcmds op k) := wloc_zero obj op _
theorem a7_localState : (a7 obj op k).localState
    = wloc obj op (.gathering (wcmd op k) (wsd obj op k) [] (wcmds op k)) := rfl
theorem a8_local : (a8 obj op k).localState 0
    = .waiting (wcmd op k) (k + 1) (wtr obj op (k + 1)) := wloc_zero obj op _
theorem a8_localState : (a8 obj op k).localState
    = wloc obj op (.waiting (wcmd op k) (k + 1) (wtr obj op (k + 1))) := rfl
theorem a9_local : (a9 obj op k).localState 0
    = .publishing (wcmd op k) (wsd obj op (k + 1)) := wloc_zero obj op _
theorem a9_localState : (a9 obj op k).localState
    = wloc obj op (.publishing (wcmd op k) (wsd obj op (k + 1))) := rfl
theorem a9_slots : (a9 obj op k).slots = wslots obj op k := rfl
theorem a10_slots : (a10 obj op k).slots = wslots obj op (k + 1) := rfl
theorem a10_localState : (a10 obj op k).localState
    = wloc obj op (.checking (wcmd op k) (wsd obj op (k + 1)) (List.finRange 2)
        (zeroSeed obj)) := rfl
theorem a11_slots : (a11 obj op k).slots = wslots obj op (k + 1) := rfl
theorem a11_localState : (a11 obj op k).localState
    = wloc obj op (.checking (wcmd op k) (wsd obj op (k + 1)) [1] (wsd obj op (k + 1))) := rfl
theorem a12_local : (a12 obj op k).localState 0
    = .checking (wcmd op k) (wsd obj op (k + 1)) [] (wsd obj op (k + 1)) := wloc_zero obj op _
theorem a12_localState : (a12 obj op k).localState
    = wloc obj op (.checking (wcmd op k) (wsd obj op (k + 1)) [] (wsd obj op (k + 1))) := rfl

end Proj

/-! ### The thirteen steps of a cycle -/

variable {H : WeakUniversal.Environment (n := 2) obj}

theorem step_invoke (k : Nat) : Step obj H (a0 obj op k) (a1 obj op k) := by
  have h := Step.invoke (H := H) (a0 obj op k) 0 op (wsd obj op k) (a0_local obj op k)
  simp only [a0_seq, a0_inv, a0_localState, wseq_zero, update_wseq, update_wloc] at h
  exact h

theorem step_announce (k : Nat) : Step obj H (a1 obj op k) (a2 obj op k) := by
  have h := Step.announce (H := H) (a1 obj op k) 0 (wcmd op k) (wsd obj op k)
    (a1_local obj op k) (List.finRange 2) (List.Perm.refl _)
  simp only [a1_ann, a1_localState, update_wann, update_wloc] at h
  exact h

theorem step_read0 (k : Nat) : Step obj H (a2 obj op k) (a3 obj op k) := by
  have hloc : (a2 obj op k).localState 0
      = .collecting (wcmd op k) (0 :: [1]) (wsd obj op k) := by
    rw [a2_localState, wloc_zero, finRange_two]
  have h := Step.readStart (H := H) (a2 obj op k) 0 0 (wcmd op k) [1] (wsd obj op k) hloc
  simp only [a2_slots, best_start_zero, a2_localState, update_wloc] at h
  exact h

theorem step_read1 (k : Nat) : Step obj H (a3 obj op k) (a4 obj op k) := by
  have hloc : (a3 obj op k).localState 0
      = .collecting (wcmd op k) (1 :: []) (wsd obj op k) := by
    rw [a3_localState, wloc_zero]
  have h := Step.readStart (H := H) (a3 obj op k) 0 1 (wcmd op k) [] (wsd obj op k) hloc
  simp only [a3_localState, update_wloc] at h
  exact h

theorem step_collected (k : Nat) : Step obj H (a4 obj op k) (a5 obj op k) := by
  have h := Step.collectedStart (H := H) (a4 obj op k) 0 (wcmd op k) (wsd obj op k)
    (a4_local obj op k) (List.finRange 2) (List.Perm.refl _)
  simp only [a4_localState, update_wloc] at h
  exact h

theorem step_ann0 (k : Nat) : Step obj H (a5 obj op k) (a6 obj op k) := by
  have hloc : (a5 obj op k).localState 0
      = .gathering (wcmd op k) (wsd obj op k) (0 :: [1]) [] := by
    rw [a5_localState, wloc_zero, finRange_two]
  have h := Step.readAnnouncement (H := H) (a5 obj op k) 0 0 (wcmd op k) (wsd obj op k)
    [1] [] hloc
  simp only [a5_ann, observe_zero, a5_localState, update_wloc] at h
  exact h

theorem step_ann1 (k : Nat) : Step obj H (a6 obj op k) (a7 obj op k) := by
  have hloc : (a6 obj op k).localState 0
      = .gathering (wcmd op k) (wsd obj op k) (1 :: []) [wcmd op k] := by
    rw [a6_localState, wloc_zero]
  have h := Step.readAnnouncement (H := H) (a6 obj op k) 0 1 (wcmd op k) (wsd obj op k)
    [] [wcmd op k] hloc
  simp only [a6_ann, observe_one, a6_localState, update_wloc] at h
  exact h

theorem step_propose (k : Nat) :
    Step obj ((wfam obj op).environment obj) (a7 obj op k) (a8 obj op k) := by
  have hi : ((wfam obj op).environment obj ((wsd obj op k).round + 1)).input 0
      = some (proposal obj (wsd obj op k) (wcmds op k)) := by
    show ((wfam obj op).environment obj (k + 1)).input 0 = _
    rw [proposal_eq]
    exact wfam_input obj op (k + 1) (by omega)
  have h := Step.propose (a7 obj op k) 0 (wcmd op k) (wsd obj op k) (wcmds op k)
    (a7_local obj op k) (wcmds op k) (List.Perm.refl _) hi
  simp only [a7_localState, update_wloc, proposal_eq] at h
  exact h

theorem step_receive (k : Nat) :
    Step obj ((wfam obj op).environment obj) (a8 obj op k) (a9 obj op k) := by
  have h := Step.receive (a8 obj op k) 0 (wcmd op k) (k + 1) (wtr obj op (k + 1))
    (wtr obj op (k + 1)) true (a8_local obj op k) (wfam_output obj op (k + 1) (by omega))
    (List.finRange 2) (List.Perm.refl _)
  simp only [a8_localState, update_wloc] at h
  exact h

theorem step_publish (k : Nat) : Step obj H (a9 obj op k) (a10 obj op k) := by
  have h := Step.publish (H := H) (a9 obj op k) 0 (wcmd op k) (wsd obj op (k + 1))
    (a9_local obj op k) (List.finRange 2) (List.Perm.refl _)
  simp only [a9_slots, a9_localState, update_wslots, update_wloc] at h
  exact h

theorem step_check0 (k : Nat) : Step obj H (a10 obj op k) (a11 obj op k) := by
  have hloc : (a10 obj op k).localState 0
      = .checking (wcmd op k) (wsd obj op (k + 1)) (0 :: [1]) (zeroSeed obj) := by
    rw [a10_localState, wloc_zero, finRange_two]
  have h := Step.readCheck (H := H) (a10 obj op k) 0 0 (wcmd op k) (wsd obj op (k + 1))
    [1] (zeroSeed obj) hloc
  simp only [a10_slots, best_check_zero, a10_localState, update_wloc] at h
  exact h

theorem step_check1 (k : Nat) : Step obj H (a11 obj op k) (a12 obj op k) := by
  have hloc : (a11 obj op k).localState 0
      = .checking (wcmd op k) (wsd obj op (k + 1)) (1 :: []) (wsd obj op (k + 1)) := by
    rw [a11_localState, wloc_zero]
  have h := Step.readCheck (H := H) (a11 obj op k) 0 1 (wcmd op k) (wsd obj op (k + 1))
    [] (wsd obj op (k + 1)) hloc
  simp only [a11_slots, best_check_one, a11_localState, update_wloc] at h
  exact h

theorem step_finish (k : Nat) : Step obj H (a12 obj op k) (a0 obj op (k + 1)) := by
  have hcount : 0 < (Tagged (n := 2) obj).traceCount (wcmd op k)
      (wsd obj op (k + 1)).trace := by
    show 0 < (Tagged (n := 2) obj).traceCount (wcmd op k) (wtr obj op (k + 1))
    rw [traceCount_wtr_wcmd]; simp
  have h := Step.finish (H := H) (a12 obj op k) 0 (wcmd op k) (wsd obj op (k + 1))
    (wsd obj op (k + 1)) (a12_local obj op k) hcount
  simp only [a12_localState, update_wloc] at h
  exact h

/-! ### The prologue: the stalled process invokes and announces -/

omit [DecidableEq Op] in
theorem fin2 (q : Fin 2) : q = 0 ∨ q = 1 := by omega

omit [DecidableEq Op] in
theorem config_ext {c d : Configuration (n := 2) obj}
    (h1 : c.sequence = d.sequence) (h2 : c.localState = d.localState)
    (h3 : c.slots = d.slots) (h4 : c.announcements = d.announcements)
    (h5 : c.calls = d.calls) (h6 : c.returns = d.returns)
    (h7 : c.invocations = d.invocations) : c = d := by
  cases c; cases d; simp_all

/-- Process `0` is idle; process `1` has invoked and is about to announce. -/
noncomputable def q1 : Configuration (n := 2) obj :=
  { a0 obj op 0 with
    announcements := fun _ => none
    localState := fun q => if q = 0 then .idle (zeroSeed obj)
      else .announcing (ocmd op) (zeroSeed obj) }

theorem step_prologue_invoke :
    Step obj H (HelpingUniversal.initial obj) (q1 obj op) := by
  have h := Step.invoke (H := H) (HelpingUniversal.initial obj) 1 op (zeroSeed obj) rfl
  refine Eq.mp (congrArg (Step obj H (HelpingUniversal.initial obj)) ?_) h
  refine config_ext obj ?_ ?_ ?_ rfl rfl rfl rfl
  · funext q; rcases fin2 q with rfl | rfl <;>
      simp [update, q1, a0_seq, wseq, HelpingUniversal.initial]
  · funext q; rcases fin2 q with rfl | rfl <;>
      simp [update, q1, HelpingUniversal.initial, ocmd]
  · funext q; rcases fin2 q with rfl | rfl <;>
      simp [q1, a0_slots, wslots, wsd, HelpingUniversal.initial] <;> try rfl

theorem step_prologue_announce :
    Step obj H (q1 obj op) (a0 obj op 0) := by
  have h := Step.announce (H := H) (q1 obj op) 1 (ocmd op) (zeroSeed obj) (by simp [q1])
    (List.finRange 2) (List.Perm.refl _)
  refine Eq.mp (congrArg (Step obj H (q1 obj op)) ?_) h
  refine config_ext obj rfl ?_ rfl ?_ rfl rfl rfl
  · funext q; rcases fin2 q with rfl | rfl <;>
      simp [update, q1, a0_localState, wloc, park, wsd] <;> try rfl
  · funext q; rcases fin2 q with rfl | rfl <;> simp [update, q1, a0_ann, wann, wprev]

/-! ### The infinite run -/

noncomputable def wcyc (k : Nat) : Nat → Configuration (n := 2) obj
  | 0 => a0 obj op k
  | 1 => a1 obj op k
  | 2 => a2 obj op k
  | 3 => a3 obj op k
  | 4 => a4 obj op k
  | 5 => a5 obj op k
  | 6 => a6 obj op k
  | 7 => a7 obj op k
  | 8 => a8 obj op k
  | 9 => a8 obj op k
  | 10 => a8 obj op k
  | 11 => a8 obj op k
  | 12 => a8 obj op k
  | 13 => a8 obj op k
  | 14 => a8 obj op k
  | 15 => a9 obj op k
  | 16 => a10 obj op k
  | 17 => a11 obj op k
  | _ => a12 obj op k

noncomputable def wstate : Nat → Configuration (n := 2) obj
  | 0 => HelpingUniversal.initial obj
  | 1 => q1 obj op
  | (t + 2) => wcyc obj op (t / 19) (t % 19)

omit [DecidableEq Op] in
theorem wstate_at (k j : Nat) (hj : j < 19) :
    wstate obj op (j + 19 * k + 2) = wcyc obj op k j := by
  show wcyc obj op ((j + 19 * k) / 19) ((j + 19 * k) % 19) = _
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < 19), Nat.div_eq_of_lt hj,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj, Nat.zero_add]

omit [DecidableEq Op] in
theorem wstate_succ_wrap (k : Nat) :
    wstate obj op (18 + 19 * k + 2 + 1) = a0 obj op (k + 1) := by
  rw [show 18 + 19 * k + 2 + 1 = 0 + 19 * (k + 1) + 2 from by omega,
    wstate_at obj op (k + 1) 0 (by omega)]
  rfl

omit [DecidableEq Op] in
theorem wstate_succ (k j : Nat) (hj : j < 18) :
    wstate obj op (j + 19 * k + 2 + 1) = wcyc obj op k (j + 1) := by
  rw [show j + 19 * k + 2 + 1 = (j + 1) + 19 * k + 2 from by omega,
    wstate_at obj op k (j + 1) (by omega)]

omit [DecidableEq Op] in
/-- The six protocol events: the program stutters while the GCA call advances. -/
theorem wstutter_at (k j : Nat) (h8 : 8 ≤ j) (h13 : j ≤ 13) :
    wstate obj op (j + 19 * k + 2 + 1) = wstate obj op (j + 19 * k + 2) := by
  rw [wstate_succ obj op k j (by omega), wstate_at obj op k j (by omega)]
  match j, h8, h13 with
  | 8, _, _ => rfl
  | 9, _, _ => rfl
  | 10, _, _ => rfl
  | 11, _, _ => rfl
  | 12, _, _ => rfl
  | 13, _, _ => rfl

theorem wstep_at (k j : Nat) (hj : j < 19) (hst : ¬ (8 ≤ j ∧ j ≤ 13)) :
    Step obj ((wfam obj op).environment obj)
      (wstate obj op (j + 19 * k + 2)) (wstate obj op (j + 19 * k + 2 + 1)) := by
  rw [wstate_at obj op k j hj]
  match j, hj, hst with
  | 0, _, _ => rw [wstate_succ obj op k 0 (by omega)]; exact step_invoke obj op k
  | 1, _, _ => rw [wstate_succ obj op k 1 (by omega)]; exact step_announce obj op k
  | 2, _, _ => rw [wstate_succ obj op k 2 (by omega)]; exact step_read0 obj op k
  | 3, _, _ => rw [wstate_succ obj op k 3 (by omega)]; exact step_read1 obj op k
  | 4, _, _ => rw [wstate_succ obj op k 4 (by omega)]; exact step_collected obj op k
  | 5, _, _ => rw [wstate_succ obj op k 5 (by omega)]; exact step_ann0 obj op k
  | 6, _, _ => rw [wstate_succ obj op k 6 (by omega)]; exact step_ann1 obj op k
  | 7, _, _ => rw [wstate_succ obj op k 7 (by omega)]; exact step_propose obj op k
  | 8, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 9, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 10, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 11, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 12, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 13, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 14, _, _ => rw [wstate_succ obj op k 14 (by omega)]; exact step_receive obj op k
  | 15, _, _ => rw [wstate_succ obj op k 15 (by omega)]; exact step_publish obj op k
  | 16, _, _ => rw [wstate_succ obj op k 16 (by omega)]; exact step_check0 obj op k
  | 17, _, _ => rw [wstate_succ obj op k 17 (by omega)]; exact step_check1 obj op k
  | 18, _, _ => rw [wstate_succ_wrap obj op k]; exact step_finish obj op k
  | (n + 19), h, _ => exact absurd h (by omega)

/-- The run of Algorithm 3 the witness exhibits. -/
noncomputable def wrun :
    HelpingUniversal.Execution obj ((wfam obj op).environment obj) where
  state := wstate obj op
  initial_state := rfl
  next := by
    intro t
    match t with
    | 0 => exact Or.inr (step_prologue_invoke obj op)
    | 1 => exact Or.inr (step_prologue_announce obj op)
    | (t + 2) =>
        obtain ⟨k, j, hj, hje⟩ : ∃ k j, j < 19 ∧ t = j + 19 * k :=
          ⟨t / 19, t % 19, Nat.mod_lt _ (by omega), (Nat.mod_add_div t 19).symm⟩
        subst hje
        by_cases hst : 8 ≤ j ∧ j ≤ 13
        · exact Or.inl (wstutter_at obj op k j hst.1 hst.2)
        · exact Or.inr (wstep_at obj op k j hj hst)

theorem wrun_state : (wrun obj op).state = wstate obj op := rfl

/-! ### Two operations are in flight -/

omit [DecidableEq Op] in
theorem ocmd_mem_winv : ∀ k, ocmd op ∈ winv op k
  | 0 => by simp [winv]
  | (k + 1) => List.mem_cons_of_mem _ (ocmd_mem_winv k)

omit [DecidableEq Op] in
theorem wcmd_mem_winv (k : Nat) : wcmd op k ∈ winv op (k + 1) :=
  List.mem_cons_self ..

omit [DecidableEq Op] in
theorem wrets_command : ∀ k, ∀ ret ∈ wrets obj op k, ∃ j, j < k ∧ ret.command = wcmd op j
  | 0 => by intro ret h; simp [wrets] at h
  | (k + 1) => by
      intro ret h
      rcases List.mem_cons.mp h with rfl | hm
      · exact ⟨k, by omega, rfl⟩
      · obtain ⟨j, hj, he⟩ := wrets_command k ret hm
        exact ⟨j, by omega, he⟩

omit [DecidableEq Op] in
theorem a8_inv (k : Nat) : (a8 obj op k).invocations = winv op (k + 1) := rfl

omit [DecidableEq Op] in
theorem a8_returns (k : Nat) : (a8 obj op k).returns = wrets obj op k := rfl

/-- **The witness places two operations in flight.**  At the moment process `0`
is waiting on round `k + 1`, both its own command and the stalled process's have
been invoked and neither has a recorded response.  The stalled process's command
is in the announcement array throughout, so process `0`'s proposal carries a
command it did not invoke. -/
theorem two_in_flight (k : Nat) :
    (wcmd op k ∈ ((wrun obj op).state (8 + 19 * k + 2)).invocations ∧
      ocmd op ∈ ((wrun obj op).state (8 + 19 * k + 2)).invocations) ∧
    (∀ ret ∈ ((wrun obj op).state (8 + 19 * k + 2)).returns,
        ret.command ≠ wcmd op k ∧ ret.command ≠ ocmd op) ∧
    wcmd op k ≠ ocmd op ∧
    ((wrun obj op).state (8 + 19 * k + 2)).announcements 1 = some (ocmd op) := by
  have hst : (wrun obj op).state (8 + 19 * k + 2) = a8 obj op k := by
    show wstate obj op (8 + 19 * k + 2) = _
    rw [wstate_at obj op k 8 (by omega)]
    rfl
  rw [hst]
  refine ⟨⟨?_, ?_⟩, ?_, wcmd_ne_ocmd op k, ?_⟩
  · rw [a8_inv]; exact wcmd_mem_winv op k
  · rw [a8_inv]; exact ocmd_mem_winv op (k + 1)
  · intro ret hret
    rw [a8_returns] at hret
    obtain ⟨j, hj, he⟩ := wrets_command obj op k ret hret
    refine ⟨?_, ?_⟩
    · rw [he]; intro h; exact absurd ((wcmd_eq_iff op j k).mp h) (by omega)
    · rw [he]; exact wcmd_ne_ocmd op j
  · show (wann op (k + 1)) 1 = _
    simp [wann]

/-- Process `0`'s proposal in cycle `0` carries the stalled process's command:
round `1` commits both. -/
theorem round_one_commits_both :
    0 < (Tagged (n := 2) obj).traceCount (wcmd op 0) (wtr obj op 1) ∧
    0 < (Tagged (n := 2) obj).traceCount (ocmd op) (wtr obj op 1) := by
  refine ⟨?_, ?_⟩
  · rw [traceCount_wtr_wcmd]; simp
  · rw [traceCount_wtr_ocmd]; simp

/-! ### The schedule

Process `1` acts at the two prologue ticks; process `0` acts for ever after. -/

def wactor : Nat → Option (Fin 2) := fun t => if t < 2 then some 1 else some 0

omit [DecidableEq Op] in
theorem wactor_prologue {t : Nat} (h : t < 2) : wactor t = some 1 := by simp [wactor, h]

omit [DecidableEq Op] in
theorem wactor_main (t : Nat) : wactor (t + 2) = some 0 := by simp [wactor]

omit [DecidableEq Op] in
theorem wcyc_localState (k j : Nat) :
    ∃ l, (wcyc obj op k j).localState = wloc obj op l := by
  unfold wcyc
  split <;> exact ⟨_, rfl⟩

omit [DecidableEq Op] in
/-- Process `1` stays parked from the end of the prologue on. -/
theorem wstate_park (t : Nat) : (wstate obj op (t + 2)).localState 1 = park obj op := by
  obtain ⟨l, hl⟩ := wcyc_localState obj op (t / 19) (t % 19)
  show (wcyc obj op (t / 19) (t % 19)).localState 1 = _
  rw [hl, wloc_one]

omit [DecidableEq Op] in
theorem wround_mid (k j : Nat) (h8 : 8 ≤ j) (h14 : j ≤ 14) :
    helpingRound obj ((wstate obj op (j + 19 * k + 2)).localState 0) = some (k + 1) := by
  rw [wstate_at obj op k j (by omega)]
  match j, h8, h14 with
  | 8, _, _ => rfl
  | 9, _, _ => rfl
  | 10, _, _ => rfl
  | 11, _, _ => rfl
  | 12, _, _ => rfl
  | 13, _, _ => rfl
  | 14, _, _ => rfl

omit [DecidableEq Op] in
theorem wround_none (k j : Nat) (hj : j < 19) (h : ¬ (8 ≤ j ∧ j ≤ 14)) :
    helpingRound obj ((wstate obj op (j + 19 * k + 2)).localState 0) = none := by
  rw [wstate_at obj op k j hj]
  match j, hj, h with
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | 5, _, _ => rfl
  | 6, _, _ => rfl
  | 7, _, _ => rfl
  | 8, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 9, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 10, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 11, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 12, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 13, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 14, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 15, _, _ => rfl
  | 16, _, _ => rfl
  | 17, _, _ => rfl
  | 18, _, _ => rfl
  | (n + 19), hh, _ => exact absurd hh (by omega)

omit [DecidableEq Op] in
/-- Before the end of the prologue nobody is inside a GCA call. -/
theorem wround_prologue {t : Nat} (h : t < 2) {p : Fin 2} :
    helpingRound obj ((wstate obj op t).localState p) = none := by
  match t, h with
  | 0, _ => rcases fin2 p with rfl | rfl <;> rfl
  | 1, _ =>
      rcases fin2 p with rfl | rfl
      · show helpingRound obj ((q1 obj op).localState 0) = none
        simp [q1, helpingRound]
      · show helpingRound obj ((q1 obj op).localState 1) = none
        simp [q1, helpingRound]

/-! ### The projected protocol clock -/

omit [DecidableEq Op] in
private theorem clockH_succ_ne {st : Nat → Configuration (n := 2) obj}
    {act : Nat → Option (Fin 2)} {t r : Nat}
    (h : ∀ p, gcaEventH obj st act t ≠ some (r, p)) :
    gcaClockH obj st act (t + 1) r = gcaClockH obj st act t r := by
  rw [gcaClockH]
  cases hev : gcaEventH obj st act t with
  | none => rfl
  | some rp =>
    obtain ⟨r', p⟩ := rp
    have hne : ¬ r' = r := fun hr => h p (by rw [hev, hr])
    simp [hne]

omit [DecidableEq Op] in
private theorem clockH_succ_eq {st : Nat → Configuration (n := 2) obj}
    {act : Nat → Option (Fin 2)} {t r : Nat} {p : Fin 2}
    (h : gcaEventH obj st act t = some (r, p)) :
    gcaClockH obj st act (t + 1) r = gcaClockH obj st act t r + 1 := by
  rw [gcaClockH, h]; simp

omit [DecidableEq Op] in
theorem wevent_mid (k j : Nat) (h8 : 8 ≤ j) (h14 : j ≤ 14) :
    gcaEventH obj (wstate obj op) wactor (j + 19 * k + 2) = some (k + 1, 0) :=
  gcaEventH_spec obj (wactor_main (j + 19 * k)) (wround_mid obj op k j h8 h14)

omit [DecidableEq Op] in
theorem wevent_none (k j : Nat) (hj : j < 19) (h : ¬ (8 ≤ j ∧ j ≤ 14)) :
    gcaEventH obj (wstate obj op) wactor (j + 19 * k + 2) = none := by
  simp [gcaEventH, wactor_main (j + 19 * k), wround_none obj op k j hj h]

omit [DecidableEq Op] in
theorem wevent_prologue {t : Nat} (h : t < 2) :
    gcaEventH obj (wstate obj op) wactor t = none := by
  simp [gcaEventH, wactor_prologue h, wround_prologue obj op h]

omit [DecidableEq Op] in
theorem wevent_ne (k : Nat) : ∀ t, t < 8 + 19 * k + 2 →
    ∀ p, gcaEventH obj (wstate obj op) wactor t ≠ some (k + 1, p) := by
  intro t ht p hp
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · rw [wevent_prologue obj op h2] at hp; simp at hp
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
    obtain ⟨k', j, hj, rfl⟩ : ∃ k' j, j < 19 ∧ t' = j + 19 * k' :=
      ⟨t' / 19, t' % 19, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 19).symm⟩
    by_cases hmid : 8 ≤ j ∧ j ≤ 14
    · rw [wevent_mid obj op k' j hmid.1 hmid.2] at hp
      have hk : k' + 1 = k + 1 := congrArg Prod.fst (Option.some.inj hp)
      omega
    · rw [wevent_none obj op k' j hj hmid] at hp; simp at hp

omit [DecidableEq Op] in
theorem wclock_zero (k : Nat) : ∀ t, t ≤ 8 + 19 * k + 2 →
    gcaClockH obj (wstate obj op) wactor t (k + 1) = 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      rw [clockH_succ_ne obj (wevent_ne obj op k t (by omega))]
      exact ih (by omega)

omit [DecidableEq Op] in
theorem wclock_mid (k : Nat) : ∀ i, i ≤ 7 →
    gcaClockH obj (wstate obj op) wactor ((8 + i) + 19 * k + 2) (k + 1) = i := by
  intro i
  induction i with
  | zero => intro _; exact wclock_zero obj op k _ (by omega)
  | succ i ih =>
      intro hi
      rw [show (8 + (i + 1)) + 19 * k + 2 = ((8 + i) + 19 * k + 2) + 1 from by omega,
        clockH_succ_eq obj (wevent_mid obj op k (8 + i) (by omega) (by omega)),
        ih (by omega)]

omit [DecidableEq Op] in
theorem wclock_fourteen (k : Nat) :
    gcaClockH obj (wstate obj op) wactor (14 + 19 * k + 2) (k + 1) = 6 := by
  rw [show 14 + 19 * k + 2 = (8 + 6) + 19 * k + 2 from by omega]
  exact wclock_mid obj op k 6 (by omega)

/-! ### The protocol advances one stage per event -/

omit [DecidableEq Op] in
theorem wprotocol_actor (r : Nat) (hr : r ≠ 0) (t : Nat) :
    ((wfam obj op).protocol r).actor t = some 0 := by simp [wfam, hr]

omit [DecidableEq Op] in
theorem wprotocol_phase (r : Nat) (hr : r ≠ 0) : ∀ c, c ≤ 6 →
    ((wfam obj op).protocol r).phase c 0 = c := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
      intro hc
      have hstep : ((wfam obj op).protocol r).phase (c + 1) 0
          = GCA.Protocol.advance (((wfam obj op).protocol r).phase c 0) true := by
        rw [GCA.Protocol.phase, wprotocol_actor obj op r hr, ite_eq_left rfl]
        rfl
      rw [hstep, ih (by omega)]
      show GCA.Protocol.advance c true = c + 1
      simp [GCA.Protocol.advance]
      omega

/-! ### The schedule -/

noncomputable def wsched : Helping obj (wfam obj op) where
  run := wrun obj op
  actor := wactor
  step_actor := by
    intro t
    rcases Nat.lt_or_ge t 2 with h2 | h2
    · match t, h2 with
      | 0, _ =>
          refine Or.inr (Or.inl ⟨1, wactor_prologue (by omega),
            step_prologue_invoke obj op, ?_⟩)
          intro q hq
          rcases fin2 q with rfl | rfl
          · show (q1 obj op).localState 0 = (HelpingUniversal.initial obj).localState 0
            simp [q1, HelpingUniversal.initial] <;> try rfl
          · exact absurd rfl hq
      | 1, _ =>
          refine Or.inr (Or.inl ⟨1, wactor_prologue (by omega),
            step_prologue_announce obj op, ?_⟩)
          intro q hq
          rcases fin2 q with rfl | rfl
          · show (a0 obj op 0).localState 0 = (q1 obj op).localState 0
            simp [q1, a0_localState, wloc, wsd] <;> try rfl
          · exact absurd rfl hq
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 19 ∧ t' = j + 19 * k :=
        ⟨t' / 19, t' % 19, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 19).symm⟩
      by_cases hst : 8 ≤ j ∧ j ≤ 13
      · exact Or.inr (Or.inr ⟨0, k + 1, wactor_main _,
          wround_mid obj op k j hst.1 (by omega), wstutter_at obj op k j hst.1 hst.2⟩)
      · refine Or.inr (Or.inl ⟨0, wactor_main _, wstep_at obj op k j hj hst, ?_⟩)
        intro q hq
        rcases fin2 q with rfl | rfl
        · exact absurd rfl hq
        · show (wstate obj op (j + 19 * k + 2 + 1)).localState 1
            = (wstate obj op (j + 19 * k + 2)).localState 1
          rw [show j + 19 * k + 2 + 1 = (j + 19 * k + 1) + 2 from by omega,
            wstate_park, wstate_park]
  gca_actor := by
    intro t p r hact hr
    rw [wrun_state] at hr
    rcases Nat.lt_or_ge t 2 with h2 | h2
    · rw [wround_prologue obj op h2] at hr; exact absurd hr (by simp)
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
      have hp : p = 0 := (Option.some.inj ((wactor_main t').symm.trans hact)).symm
      subst hp
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 19 ∧ t' = j + 19 * k :=
        ⟨t' / 19, t' % 19, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 19).symm⟩
      by_cases hmid : 8 ≤ j ∧ j ≤ 14
      · have hrk : r = k + 1 :=
          (Option.some.inj ((wround_mid obj op k j hmid.1 hmid.2).symm.trans hr)).symm
        subst r
        exact wprotocol_actor obj op (k + 1) (by omega) _
      · rw [wround_none obj op k j hj hmid] at hr; exact absurd hr (by simp)
  no_ghost := by
    intro r p s hi
    by_cases hp : p = 0
    · subst p
      refine ⟨8 + 19 * r + 2, wtr obj op (r + 1), ?_⟩
      show (⟨r + 1, 0, wtr obj op (r + 1)⟩ : Call (n := 2) obj)
        ∈ (wstate obj op (8 + 19 * r + 2)).calls
      rw [wstate_at obj op r 8 (by omega)]
      show _ ∈ wcalls obj op (r + 1)
      exact List.mem_cons_self ..
    · rw [wfam_input_none obj op (r + 1) hp] at hi
      exact absurd hi (by simp)
  receive_ready := by
    intro t p r hr hchange
    rw [wrun_state] at hr hchange
    rcases Nat.lt_or_ge t 2 with h2 | h2
    · rw [wround_prologue obj op h2] at hr; exact absurd hr (by simp)
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 19 ∧ t' = j + 19 * k :=
        ⟨t' / 19, t' % 19, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 19).symm⟩
      rcases fin2 p with rfl | rfl
      · by_cases hmid : 8 ≤ j ∧ j ≤ 14
        · have hrk : r = k + 1 :=
            (Option.some.inj ((wround_mid obj op k j hmid.1 hmid.2).symm.trans hr)).symm
          subst r
          have hj14 : j = 14 := by
            apply Classical.byContradiction
            intro hne
            exact hchange (by
              rw [show j + 19 * k + 2 + 1 = (j + 19 * k + 1) + 2 from by omega,
                show j + 19 * k + 1 = (j + 1) + 19 * k from by omega]
              rw [show (j + 1) + 19 * k + 2 = (j + 1) + 19 * k + 2 from rfl]
              have := wstutter_at obj op k j hmid.1 (by omega)
              rw [show j + 19 * k + 2 + 1 = (j + 19 * k + 1) + 2 from by omega] at this
              rw [show j + 19 * k + 1 = (j + 1) + 19 * k from by omega] at this
              rw [this])
          subst j
          rw [wrun_state, wclock_fourteen obj op k]
          exact wprotocol_phase obj op (k + 1) (by omega) 6 (by omega)
        · rw [wround_none obj op k j hj hmid] at hr; exact absurd hr (by simp)
      · rw [show j + 19 * k + 2 = (j + 19 * k) + 2 from rfl, wstate_park] at hr
        exact absurd hr (by simp [park, helpingRound])

theorem wsched_state (t : Nat) : (wsched obj op).run.state t = wstate obj op t := rfl

theorem wsched_actor (t : Nat) : (wsched obj op).actor t = wactor t := rfl

theorem wsched_state_fun : (wsched obj op).run.state = wstate obj op := rfl

theorem wsched_actor_fun : (wsched obj op).actor = wactor := rfl

/-- **Fairness.**  The `receive` step is taken exactly when the projected
protocol clock shows the last stage, at offset `14` of the cycle. -/
theorem wsched_fair : (wsched obj op).Fair := by
  intro t p cmd r proposal hact hl hphase _
  rw [wsched_state] at hl
  rw [wsched_actor] at hact
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · exfalso
    have hnone := wround_prologue obj op h2 (p := p)
    rw [hl] at hnone
    exact absurd hnone (by simp [helpingRound])
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
    have hp : p = 0 := (Option.some.inj ((wactor_main t').symm.trans hact)).symm
    subst hp
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 19 ∧ t' = j + 19 * k :=
      ⟨t' / 19, t' % 19, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 19).symm⟩
    have hround : helpingRound obj
        ((wstate obj op (j + 19 * k + 2)).localState 0) = some r := by rw [hl]; rfl
    by_cases hmid : 8 ≤ j ∧ j ≤ 14
    · have hrk : r = k + 1 :=
        (Option.some.inj ((wround_mid obj op k j hmid.1 hmid.2).symm.trans hround)).symm
      subst r
      rw [wsched_state_fun, wsched_actor_fun] at hphase
      have hj14 : j = 14 := by
        apply Classical.byContradiction
        intro hne
        rw [show j + 19 * k + 2 = (8 + (j - 8)) + 19 * k + 2 from by omega,
          wclock_mid obj op k (j - 8) (by omega),
          wprotocol_phase obj op (k + 1) (by omega) (j - 8) (by omega)] at hphase
        omega
      subst j
      refine ⟨wstep_at obj op k 14 (by omega) (by omega), ?_⟩
      intro q hq
      rcases fin2 q with rfl | rfl
      · exact absurd rfl hq
      · show (wstate obj op (14 + 19 * k + 2 + 1)).localState 1
          = (wstate obj op (14 + 19 * k + 2)).localState 1
        rw [show 14 + 19 * k + 2 + 1 = (14 + 19 * k + 1) + 2 from by omega,
          wstate_park, wstate_park]
    · rw [wround_none obj op k j hj hmid] at hround
      exact absurd hround (by simp)

/-- **Operation liveness.**  Process `0` holds a command whenever it is waiting. -/
theorem wsched_opLive : (wsched obj op).OpLive := by
  intro N
  refine ⟨8 + 19 * N + 1, by omega, ?_⟩
  have h : (wsched obj op).opActor (8 + 19 * N + 1) = some (wcmd op N) := by
    show (match wactor (8 + 19 * N + 1 + 1) with
      | none => none
      | some p => (HelpingUniversal.ledger obj
          (wstate obj op (8 + 19 * N + 1 + 1))).active p) = _
    rw [show 8 + 19 * N + 1 + 1 = 8 + 19 * N + 2 from by omega, wactor_main (8 + 19 * N)]
    show ((wstate obj op (8 + 19 * N + 2)).localState 0).command obj = _
    rw [wstate_at obj op N 8 (by omega)]
    rfl
  rw [h]
  rfl

end ConflictFreedom.GlobalSchedule.WitnessC

namespace ConflictFreedom
variable {State Op Response : Type} [DecidableEq Op]

/-- **The admitted set of Algorithm 3 contains a contended run.**  Unlike
`algorithm3_nonempty`, whose witness runs a single worker with idle bystanders,
this one has two operations simultaneously in flight and a non-trivial
announcement array. -/
theorem algorithm3_nonempty_contended (obj : Object State Op Response) (op : Op) :
    ∃ e, algorithm3 obj 2 e :=
  ⟨_, GlobalSchedule.WitnessC.wfam obj op, GlobalSchedule.WitnessC.wsched obj op,
    GlobalSchedule.WitnessC.wsched_opLive obj op,
    GlobalSchedule.WitnessC.wsched_fair obj op,
    GlobalSchedule.WitnessC.wfam_waitFree obj op, rfl⟩

/-- **Algorithm 3's admitted set contains an execution with two operation
instances concurrently pending.**  This is what the single-worker witnesses
could not show: the §3 theorems are non-vacuous on a *contended* run. -/
theorem algorithm3_contended (obj : Object State Op Response) (op : Op) :
    ∃ e : Execution 2 Op, algorithm3 obj 2 e ∧
      ∃ (i j : e.Instance) (t : Nat), i ≠ j ∧ e.Pending i t ∧ e.Pending j t := by
  classical
  have hp := GlobalSchedule.WitnessC.wsched_opLive obj op
  obtain ⟨⟨hw, ho⟩, hret, hne, -⟩ := GlobalSchedule.WitnessC.two_in_flight obj op 0
  have hstate : ((GlobalSchedule.WitnessC.wsched obj op).run.state (0 + 1 + 9 + 1))
      = (GlobalSchedule.WitnessC.wrun obj op).state (8 + 19 * 0 + 2) := by
    show GlobalSchedule.WitnessC.wstate obj op 11
      = GlobalSchedule.WitnessC.wstate obj op 10
    rw [show (11 : Nat) = 9 + 19 * 0 + 2 from by omega,
      show (10 : Nat) = 8 + 19 * 0 + 2 from by omega,
      GlobalSchedule.WitnessC.wstate_at obj op 0 9 (by omega),
      GlobalSchedule.WitnessC.wstate_at obj op 0 8 (by omega)]
    rfl
  have hmem : ∀ a : WeakUniversal.Cmd 2 Op,
      a ∈ ((GlobalSchedule.WitnessC.wrun obj op).state (8 + 19 * 0 + 2)).invocations →
      a ∈ (InvocationLedger.obs
        ((GlobalSchedule.WitnessC.wsched obj op).run.ledgerRun obj) 9).invoked := by
    intro a ha
    show a ∈ ((GlobalSchedule.WitnessC.wsched obj op).run.state (9 + 1)).invocations
    rw [show (9 : Nat) + 1 = 10 from rfl]
    show a ∈ (GlobalSchedule.WitnessC.wstate obj op 10).invocations
    exact ha
  have hnotret : ∀ a : WeakUniversal.Cmd 2 Op,
      (∀ ret ∈ ((GlobalSchedule.WitnessC.wrun obj op).state (8 + 19 * 0 + 2)).returns,
        ret.command ≠ a) →
      a ∉ (InvocationLedger.obs
        ((GlobalSchedule.WitnessC.wsched obj op).run.ledgerRun obj) 9).returned := by
    intro a ha hm
    obtain ⟨ret, hret', he⟩ := List.mem_map.mp hm
    exact ha ret hret' he
  refine ⟨(GlobalSchedule.WitnessC.wsched obj op).execution hp,
    ⟨_, GlobalSchedule.WitnessC.wsched obj op, hp,
      GlobalSchedule.WitnessC.wsched_fair obj op,
      GlobalSchedule.WitnessC.wfam_waitFree obj op, rfl⟩, ?_⟩
  refine ⟨⟨GlobalSchedule.WitnessC.wcmd op 0, ⟨9, hmem _ hw⟩⟩,
    ⟨GlobalSchedule.WitnessC.ocmd op, ⟨9, hmem _ ho⟩⟩, 9,
    fun h => hne (congrArg Subtype.val h), ?_, ?_⟩
  · exact ((_ : InvocationLedger.Schedule _).execution_pending_iff _ 9).mpr
      ⟨hmem _ hw, hnotret _ (fun ret hr => (hret ret hr).1)⟩
  · exact ((_ : InvocationLedger.Schedule _).execution_pending_iff _ 9).mpr
      ⟨hmem _ ho, hnotret _ (fun ret hr => (hret ret hr).2)⟩

end ConflictFreedom
