import CFLeanProof.Algorithm1WeakConflictFree

/-! # A contended fair, operation-live run of Algorithm 1

`Witness.rsched` runs one worker with `m` permanently idle bystanders,
so `algorithm1_nonempty` exhibits an *uncontended* run: at every instant at
most one operation is in flight, and §3's conflict hypothesis — which speaks
about two simultaneously pending instances — is never tested on it.

This module builds the contended counterpart over two processes.  Process `1`
invokes and then takes no further step: its operation is pending for ever, as
in the manuscript's picture of a slow or faulty process.  Process `0` cycles
through the whole of Algorithm 1 for ever: invoke, the two register reads, the
collect, the proposal, six protocol events, the receive, the publication and
the response.  The cycle is `14` steps and the prologue is one.

Algorithm 1 has no announcement array, so process `0` never helps process `1`:
the stalled command is invoked, never proposed and never returned.  That is the
*point* of the contrast with `ContentionWitness`, where the same picture under
Algorithm 3 has the stalled command committed by round `1`.
-/
namespace ConflictFreedom.GlobalSchedule.WitnessW
open WeakUniversal
open UniversalProtocol
variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op] (op : Op)

/-! ### Commands -/

/-- The `(k+1)`-st command of the cycling process. -/
def vcmd (k : Nat) : Cmd 2 Op := ⟨op, 0, k + 1⟩

/-- The stalled process's single command. -/
def ocmd : Cmd 2 Op := ⟨op, 1, 1⟩

omit [DecidableEq Op] in
theorem vcmd_ne_ocmd (k : Nat) : vcmd op k ≠ ocmd op := by
  intro h
  exact absurd (congrArg Command.process h) (by simp [vcmd, ocmd])

omit [DecidableEq Op] in
theorem vcmd_eq_iff (j k : Nat) : vcmd op j = vcmd op k ↔ j = k := by
  constructor
  · intro h
    have := congrArg Command.sequence h
    simp only [vcmd] at this
    omega
  · intro h; rw [h]

/-! ### Traces and seeds -/

/-- The trace committed in round `k`; round zero is the empty trace. -/
noncomputable def vtr : Nat → (Tagged (n := 2) obj).Trace
  | 0 => (Tagged (n := 2) obj).emptyTrace
  | k + 1 => (Tagged (n := 2) obj).appendMissing (vtr k) (vcmd op k)

noncomputable def vsd (k : Nat) : Seed (n := 2) obj := ⟨k, vtr obj op k⟩

/-! ### State components

Process `1` is parked in its collect for ever; only process `0` moves. -/

/-- The stalled process's parked local state. -/
noncomputable def park : Local (n := 2) obj :=
  .collecting (ocmd op) (List.finRange 2) (zeroSeed obj)

noncomputable def vloc (l : Local (n := 2) obj) : Fin 2 → Local (n := 2) obj :=
  fun q => if q = 0 then l else park obj op

def vseq (k : Nat) : Fin 2 → Nat := fun q => if q = 0 then k else 1

noncomputable def vslots (k : Nat) : Fin 2 → Seed (n := 2) obj :=
  fun q => if q = 0 then vsd obj op k else zeroSeed obj

def vinv : Nat → List (Cmd 2 Op)
  | 0 => [ocmd op]
  | (k + 1) => vcmd op k :: vinv k

noncomputable def vcalls : Nat → List (Call (n := 2) obj)
  | 0 => []
  | (k + 1) => ⟨k + 1, 0, vtr obj op (k + 1)⟩ :: vcalls k

noncomputable def vrets : Nat → List (Return (n := 2) obj)
  | 0 => []
  | (k + 1) => ⟨vcmd op k, k + 1, vtr obj op (k + 1)⟩ :: vrets k

omit [DecidableEq Op] in
theorem vloc_zero (l : Local (n := 2) obj) : vloc obj op l 0 = l := by simp [vloc]

omit [DecidableEq Op] in
theorem vloc_one (l : Local (n := 2) obj) : vloc obj op l 1 = park obj op := by
  simp [vloc]

omit [DecidableEq Op] in
theorem update_vloc (l v : Local (n := 2) obj) :
    update (vloc obj op l) 0 v = vloc obj op v := by
  funext q
  by_cases h : q = 0 <;> simp [vloc, update, h]

theorem update_vseq (k : Nat) : update (vseq k) 0 (k + 1) = vseq (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [vseq, update, h]

theorem update_vslots (k : Nat) :
    update (vslots obj op k) 0 (⟨k + 1, vtr obj op (k + 1)⟩ : Seed (n := 2) obj)
      = vslots obj op (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [vslots, update, h, vsd]

theorem vseq_zero (k : Nat) : vseq k 0 = k := by simp [vseq]

/-! ### The GCA family: one participant per positive round -/

noncomputable def vfam : Family (n := 2) obj where
  protocol := fun r =>
    { participants := if r = 0 then [] else [0]
      input := fun _ => vtr obj op r
      actor := fun _ => if r = 0 then none else some 0
      actor_valid := by
        intro t p h
        by_cases hr : r = 0
        · simp [hr] at h
        · simp [hr] at h ⊢
          exact h.symm
      acknowledged := fun _ => true }

theorem vfam_waitFree : (vfam obj op).SnapshotWaitFree obj :=
  fun _ => GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)

theorem vfam_input (r : Nat) (hr : r ≠ 0) :
    ((vfam obj op).environment obj r).input 0 = some (vtr obj op r) := by
  simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
    GCA.TimedExecution.views, GCA.SnapshotExecution.history, vfam, hr]

theorem vfam_input_none (r : Nat) {p : Fin 2} (hp : p ≠ 0) :
    ((vfam obj op).environment obj r).input p = none := by
  by_cases hr : r = 0 <;>
    simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
      GCA.TimedExecution.views, GCA.SnapshotExecution.history, vfam, hr, hp]

/-- A lone always-acknowledged participant commits its own proposal. -/
theorem vfam_output (r : Nat) (hr : r ≠ 0) :
    ((vfam obj op).environment obj r).output 0 = some (vtr obj op r, true) := by
  have hw : ((vfam obj op).protocol r).SnapshotWaitFree :=
    GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)
  have hinf : ((vfam obj op).protocol r).InfiniteSteps 0 :=
    fun N => ⟨N, Nat.le_refl _, by simp [vfam, hr]⟩
  obtain ⟨s, flag, ho⟩ := ((vfam obj op).protocol r).returned_of_infiniteSteps hw hinf
  have huniform : ∀ u, (((vfam obj op).environment obj r).Inputs u) → u = vtr obj op r := by
    intro u hu
    rw [Family.environment, GCA.Protocol.history, GCA.SnapshotExecution.inputs_iff] at hu
    obtain ⟨p, -, he⟩ := hu
    exact he.symm
  obtain ⟨rfl, rfl⟩ := (((vfam obj op).environment obj r).uniform_return
    ((vfam obj op).specification obj r) huniform ho)
  exact ho

/-! ### The collect

Process `0` reads its own register first, so the collected seed is what it
published in the previous cycle; the stalled process's empty register never
improves on it. -/

theorem finRange_two : List.finRange 2 = [(0 : Fin 2), 1] := by decide

theorem vbest_zero (k : Nat) :
    best obj (zeroSeed obj) (vslots obj op k 0) = vsd obj op k := by
  show best obj (zeroSeed obj) (vsd obj op k) = vsd obj op k
  unfold best
  split
  · rfl
  · rename_i h
    have hk : k = 0 := by
      simp only [zeroSeed, vsd, Nat.not_lt, Nat.le_zero] at h
      exact h
    subst hk
    rfl

theorem vbest_one (k : Nat) :
    best obj (vsd obj op k) (vslots obj op k 1) = vsd obj op k := by
  show best obj (vsd obj op k) (zeroSeed obj) = vsd obj op k
  unfold best
  have hno : ¬ ((vsd obj op k).round < (zeroSeed (n := 2) obj).round) := by
    simp [vsd, zeroSeed]
  simp only [hno, reduceIte]

/-! ### The cycle's configurations -/

noncomputable def c0 (k : Nat) : Configuration (n := 2) obj where
  sequence := vseq k
  localState := vloc obj op .idle
  slots := vslots obj op k
  calls := vcalls obj op k
  returns := vrets obj op k
  invocations := vinv op k

noncomputable def c1 (k : Nat) : Configuration (n := 2) obj :=
  { c0 obj op k with
    sequence := vseq (k + 1)
    invocations := vinv op (k + 1)
    localState := vloc obj op (.collecting (vcmd op k) (List.finRange 2) (zeroSeed obj)) }

noncomputable def c2 (k : Nat) : Configuration (n := 2) obj :=
  { c1 obj op k with
    localState := vloc obj op (.collecting (vcmd op k) [1] (vsd obj op k)) }

noncomputable def c3 (k : Nat) : Configuration (n := 2) obj :=
  { c1 obj op k with
    localState := vloc obj op (.collecting (vcmd op k) [] (vsd obj op k)) }

noncomputable def c4 (k : Nat) : Configuration (n := 2) obj :=
  { c1 obj op k with
    localState := vloc obj op (.ready (vcmd op k) (vsd obj op k)) }

noncomputable def c5 (k : Nat) : Configuration (n := 2) obj :=
  { c1 obj op k with
    localState := vloc obj op (.waiting (vcmd op k) (k + 1) (vtr obj op (k + 1)))
    calls := vcalls obj op (k + 1) }

noncomputable def c6 (k : Nat) : Configuration (n := 2) obj :=
  { c5 obj op k with
    localState := vloc obj op (.publishing (vcmd op k) (k + 1) (vtr obj op (k + 1))) }

noncomputable def c7 (k : Nat) : Configuration (n := 2) obj :=
  { c5 obj op k with
    slots := vslots obj op (k + 1)
    localState := vloc obj op (.returning (vcmd op k) (k + 1) (vtr obj op (k + 1))) }

/-! ### Projections -/

section Proj
variable (k : Nat)

theorem c0_seq : (c0 obj op k).sequence = vseq k := rfl
theorem c0_inv : (c0 obj op k).invocations = vinv op k := rfl
theorem c0_localState : (c0 obj op k).localState = vloc obj op .idle := rfl
theorem c0_local : (c0 obj op k).localState 0 = .idle := vloc_zero obj op _
theorem c1_slots : (c1 obj op k).slots = vslots obj op k := rfl
theorem c1_localState : (c1 obj op k).localState
    = vloc obj op (.collecting (vcmd op k) (List.finRange 2) (zeroSeed obj)) := rfl
theorem c2_localState : (c2 obj op k).localState
    = vloc obj op (.collecting (vcmd op k) [1] (vsd obj op k)) := rfl
theorem c2_slots : (c2 obj op k).slots = vslots obj op k := rfl
theorem c3_localState : (c3 obj op k).localState
    = vloc obj op (.collecting (vcmd op k) [] (vsd obj op k)) := rfl
theorem c3_local : (c3 obj op k).localState 0
    = .collecting (vcmd op k) [] (vsd obj op k) := vloc_zero obj op _
theorem c4_localState : (c4 obj op k).localState
    = vloc obj op (.ready (vcmd op k) (vsd obj op k)) := rfl
theorem c4_local : (c4 obj op k).localState 0
    = .ready (vcmd op k) (vsd obj op k) := vloc_zero obj op _
theorem c5_localState : (c5 obj op k).localState
    = vloc obj op (.waiting (vcmd op k) (k + 1) (vtr obj op (k + 1))) := rfl
theorem c5_local : (c5 obj op k).localState 0
    = .waiting (vcmd op k) (k + 1) (vtr obj op (k + 1)) := vloc_zero obj op _
theorem c6_localState : (c6 obj op k).localState
    = vloc obj op (.publishing (vcmd op k) (k + 1) (vtr obj op (k + 1))) := rfl
theorem c6_local : (c6 obj op k).localState 0
    = .publishing (vcmd op k) (k + 1) (vtr obj op (k + 1)) := vloc_zero obj op _
theorem c6_slots : (c6 obj op k).slots = vslots obj op k := rfl
theorem c7_localState : (c7 obj op k).localState
    = vloc obj op (.returning (vcmd op k) (k + 1) (vtr obj op (k + 1))) := rfl
theorem c7_local : (c7 obj op k).localState 0
    = .returning (vcmd op k) (k + 1) (vtr obj op (k + 1)) := vloc_zero obj op _

end Proj

/-! ### The nine steps of a cycle -/

section Steps
variable {H : Environment (n := 2) obj}

theorem step_invoke (k : Nat) : Step obj H (c0 obj op k) (c1 obj op k) := by
  have h := Step.invoke (H := H) (c0 obj op k) 0 op (c0_local obj op k)
    (List.finRange 2) (List.Perm.refl _)
  simp only [c0_seq, c0_inv, c0_localState, vseq_zero, update_vseq, update_vloc] at h
  exact h

theorem step_read0 (k : Nat) : Step obj H (c1 obj op k) (c2 obj op k) := by
  have hloc : (c1 obj op k).localState 0
      = .collecting (vcmd op k) (0 :: [1]) (zeroSeed obj) := by
    rw [c1_localState, vloc_zero, finRange_two]
  have h := Step.read (H := H) (c1 obj op k) 0 0 (vcmd op k) [1] (zeroSeed obj) hloc
  simp only [c1_slots, vbest_zero, c1_localState, update_vloc] at h
  exact h

theorem step_read1 (k : Nat) : Step obj H (c2 obj op k) (c3 obj op k) := by
  have hloc : (c2 obj op k).localState 0
      = .collecting (vcmd op k) (1 :: []) (vsd obj op k) := by
    rw [c2_localState, vloc_zero]
  have h := Step.read (H := H) (c2 obj op k) 0 1 (vcmd op k) [] (vsd obj op k) hloc
  simp only [c2_slots, vbest_one, c2_localState, update_vloc] at h
  exact h

theorem step_collected (k : Nat) : Step obj H (c3 obj op k) (c4 obj op k) := by
  have h := Step.collected (H := H) (c3 obj op k) 0 (vcmd op k) (vsd obj op k)
    (c3_local obj op k)
  simp only [c3_localState, update_vloc] at h
  exact h

theorem step_propose (k : Nat) :
    Step obj ((vfam obj op).environment obj) (c4 obj op k) (c5 obj op k) := by
  have h := Step.propose (c4 obj op k) 0 (vcmd op k) (vsd obj op k)
    (c4_local obj op k) (vfam_input obj op (k + 1) (by omega))
  simp only [c4_localState, update_vloc] at h
  exact h

theorem step_receive (k : Nat) :
    Step obj ((vfam obj op).environment obj) (c5 obj op k) (c6 obj op k) := by
  have h := Step.receive (c5 obj op k) 0 (vcmd op k) (k + 1) (vtr obj op (k + 1))
    (vtr obj op (k + 1)) true (c5_local obj op k) (vfam_output obj op (k + 1) (by omega))
  have hc : 0 < (Tagged (n := 2) obj).traceCount (vcmd op k) (vtr obj op (k + 1)) :=
    (Tagged (n := 2) obj).appendMissing_contains _ _
  simp only [hc, and_self, ite_true, c5_localState, update_vloc] at h
  exact h

theorem step_publish (k : Nat) : Step obj H (c6 obj op k) (c7 obj op k) := by
  have h := Step.publish (H := H) (c6 obj op k) 0 (vcmd op k) (k + 1)
    (vtr obj op (k + 1)) (c6_local obj op k)
  simp only [c6_localState, c6_slots, update_vloc, update_vslots] at h
  exact h

theorem step_finish (k : Nat) : Step obj H (c7 obj op k) (c0 obj op (k + 1)) := by
  have h := Step.finish (H := H) (c7 obj op k) 0 (vcmd op k) (k + 1)
    (vtr obj op (k + 1)) (c7_local obj op k)
  simp only [c7_localState, update_vloc] at h
  exact h

end Steps

/-! ### The prologue: the stalled process invokes and stops -/

omit [DecidableEq Op] in
theorem fin2 (q : Fin 2) : q = 0 ∨ q = 1 := by omega

omit [DecidableEq Op] in
theorem config_ext {c d : Configuration (n := 2) obj}
    (h1 : c.sequence = d.sequence) (h2 : c.localState = d.localState)
    (h3 : c.slots = d.slots) (h4 : c.calls = d.calls) (h5 : c.returns = d.returns)
    (h6 : c.invocations = d.invocations) : c = d := by
  cases c; cases d; simp_all

section Prologue
variable {H : Environment (n := 2) obj}

/-- The single prologue step: process `1` invokes, and then never moves again. -/
theorem step_prologue_invoke :
    Step obj H (WeakUniversal.initial obj) (c0 obj op 0) := by
  have h := Step.invoke (H := H) (WeakUniversal.initial obj) 1 op rfl
    (List.finRange 2) (List.Perm.refl _)
  refine Eq.mp (congrArg (Step obj H (WeakUniversal.initial obj)) ?_) h
  refine config_ext obj ?_ ?_ ?_ rfl rfl ?_
  · funext q; rcases fin2 q with rfl | rfl <;>
      simp [update, c0, vseq, WeakUniversal.initial]
  · funext q; rcases fin2 q with rfl | rfl <;>
      simp [update, c0, vloc, park, WeakUniversal.initial, ocmd]
  · funext q; rcases fin2 q with rfl | rfl <;>
      simp [c0, vslots, vsd, WeakUniversal.initial] <;> try rfl
  · simp [c0, vinv, WeakUniversal.initial, ocmd]

end Prologue

/-! ### The infinite run

The cycle is `14` steps: the invocation, the two register reads, the collect,
the proposal, six protocol events at offsets `5 … 10`, the receive at `11`, the
publication and the response. -/

noncomputable def vcyc (k : Nat) : Nat → Configuration (n := 2) obj
  | 0 => c0 obj op k
  | 1 => c1 obj op k
  | 2 => c2 obj op k
  | 3 => c3 obj op k
  | 4 => c4 obj op k
  | 5 => c5 obj op k
  | 6 => c5 obj op k
  | 7 => c5 obj op k
  | 8 => c5 obj op k
  | 9 => c5 obj op k
  | 10 => c5 obj op k
  | 11 => c5 obj op k
  | 12 => c6 obj op k
  | _ => c7 obj op k

noncomputable def vstate : Nat → Configuration (n := 2) obj
  | 0 => WeakUniversal.initial obj
  | (t + 1) => vcyc obj op (t / 14) (t % 14)

theorem vstate_at (k j : Nat) (hj : j < 14) :
    vstate obj op (j + 14 * k + 1) = vcyc obj op k j := by
  show vcyc obj op ((j + 14 * k) / 14) ((j + 14 * k) % 14) = _
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < 14), Nat.div_eq_of_lt hj,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj, Nat.zero_add]

theorem vstate_succ_wrap (k : Nat) :
    vstate obj op (13 + 14 * k + 1 + 1) = c0 obj op (k + 1) := by
  rw [show 13 + 14 * k + 1 + 1 = 0 + 14 * (k + 1) + 1 from by omega,
    vstate_at obj op (k + 1) 0 (by omega)]
  rfl

theorem vstate_succ (k j : Nat) (hj : j < 13) :
    vstate obj op (j + 14 * k + 1 + 1) = vcyc obj op k (j + 1) := by
  rw [show j + 14 * k + 1 + 1 = (j + 1) + 14 * k + 1 from by omega,
    vstate_at obj op k (j + 1) (by omega)]

/-- The six protocol events: the program stutters while the GCA call advances. -/
theorem vstutter_at (k j : Nat) (h5 : 5 ≤ j) (h10 : j ≤ 10) :
    vstate obj op (j + 14 * k + 1 + 1) = vstate obj op (j + 14 * k + 1) := by
  rw [vstate_succ obj op k j (by omega), vstate_at obj op k j (by omega)]
  match j, h5, h10 with
  | 5, _, _ => rfl
  | 6, _, _ => rfl
  | 7, _, _ => rfl
  | 8, _, _ => rfl
  | 9, _, _ => rfl
  | 10, _, _ => rfl

theorem vstep_at (k j : Nat) (hj : j < 14) (hst : ¬ (5 ≤ j ∧ j ≤ 10)) :
    Step obj ((vfam obj op).environment obj)
      (vstate obj op (j + 14 * k + 1)) (vstate obj op (j + 14 * k + 1 + 1)) := by
  rw [vstate_at obj op k j hj]
  match j, hj, hst with
  | 0, _, _ => rw [vstate_succ obj op k 0 (by omega)]; exact step_invoke obj op k
  | 1, _, _ => rw [vstate_succ obj op k 1 (by omega)]; exact step_read0 obj op k
  | 2, _, _ => rw [vstate_succ obj op k 2 (by omega)]; exact step_read1 obj op k
  | 3, _, _ => rw [vstate_succ obj op k 3 (by omega)]; exact step_collected obj op k
  | 4, _, _ => rw [vstate_succ obj op k 4 (by omega)]; exact step_propose obj op k
  | 5, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 6, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 7, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 8, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 9, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 10, _, h => exact absurd ⟨by omega, by omega⟩ h
  | 11, _, _ => rw [vstate_succ obj op k 11 (by omega)]; exact step_receive obj op k
  | 12, _, _ => rw [vstate_succ obj op k 12 (by omega)]; exact step_publish obj op k
  | 13, _, _ => rw [vstate_succ_wrap obj op k]; exact step_finish obj op k
  | (n + 14), h, _ => exact absurd h (by omega)

/-- The run of Algorithm 1 the witness exhibits. -/
noncomputable def vrun :
    WeakUniversal.Execution obj ((vfam obj op).environment obj) where
  state := vstate obj op
  initial_state := rfl
  next := by
    intro t
    match t with
    | 0 => exact Or.inr (step_prologue_invoke obj op)
    | (t + 1) =>
        obtain ⟨k, j, hj, hje⟩ : ∃ k j, j < 14 ∧ t = j + 14 * k :=
          ⟨t / 14, t % 14, Nat.mod_lt _ (by omega), (Nat.mod_add_div t 14).symm⟩
        subst hje
        by_cases hst : 5 ≤ j ∧ j ≤ 10
        · exact Or.inl (vstutter_at obj op k j hst.1 hst.2)
        · exact Or.inr (vstep_at obj op k j hj hst)

theorem vrun_state : (vrun obj op).state = vstate obj op := rfl

/-! ### Two operations are in flight

Algorithm 1 has no announcement array: the stalled command is invoked and never
proposed, so it never appears in any response. -/

omit [DecidableEq Op] in
theorem ocmd_mem_vinv : ∀ k, ocmd op ∈ vinv op k
  | 0 => by simp [vinv]
  | (k + 1) => List.mem_cons_of_mem _ (ocmd_mem_vinv k)

omit [DecidableEq Op] in
theorem vcmd_mem_vinv (k : Nat) : vcmd op k ∈ vinv op (k + 1) :=
  List.mem_cons_self ..

theorem vrets_command : ∀ k, ∀ ret ∈ vrets obj op k, ∃ j, j < k ∧ ret.command = vcmd op j
  | 0 => by intro ret h; simp [vrets] at h
  | (k + 1) => by
      intro ret h
      rcases List.mem_cons.mp h with rfl | hm
      · exact ⟨k, by omega, rfl⟩
      · obtain ⟨j, hj, he⟩ := vrets_command k ret hm
        exact ⟨j, by omega, he⟩

theorem c5_inv (k : Nat) : (c5 obj op k).invocations = vinv op (k + 1) := rfl

theorem c5_returns (k : Nat) : (c5 obj op k).returns = vrets obj op k := rfl

/-- **The witness places two operations in flight.**  At the moment process `0`
is waiting on round `k + 1`, both its own command and the stalled process's have
been invoked and neither has a recorded response. -/
theorem two_in_flight (k : Nat) :
    (vcmd op k ∈ ((vrun obj op).state (5 + 14 * k + 1)).invocations ∧
      ocmd op ∈ ((vrun obj op).state (5 + 14 * k + 1)).invocations) ∧
    (∀ ret ∈ ((vrun obj op).state (5 + 14 * k + 1)).returns,
        ret.command ≠ vcmd op k ∧ ret.command ≠ ocmd op) ∧
    vcmd op k ≠ ocmd op := by
  have hst : (vrun obj op).state (5 + 14 * k + 1) = c5 obj op k := by
    show vstate obj op (5 + 14 * k + 1) = _
    rw [vstate_at obj op k 5 (by omega)]
    rfl
  rw [hst]
  refine ⟨⟨?_, ?_⟩, ?_, vcmd_ne_ocmd op k⟩
  · rw [c5_inv]; exact vcmd_mem_vinv op k
  · rw [c5_inv]; exact ocmd_mem_vinv op (k + 1)
  · intro ret hret
    rw [c5_returns] at hret
    obtain ⟨j, hj, he⟩ := vrets_command obj op k ret hret
    refine ⟨?_, ?_⟩
    · rw [he]; intro h; exact absurd ((vcmd_eq_iff op j k).mp h) (by omega)
    · rw [he]; exact vcmd_ne_ocmd op j

/-- **Without helping the stalled command is never answered.**  No state of the
run records a response for it, at any time. -/
theorem stalled_never_returns :
    ∀ t, ∀ ret ∈ ((vrun obj op).state t).returns, ret.command ≠ ocmd op := by
  intro t
  match t with
  | 0 =>
      intro ret h
      have hnil : ret ∈ ([] : List (Return (n := 2) obj)) := h
      cases hnil
  | (t + 1) =>
      obtain ⟨k, j, hj, hje⟩ : ∃ k j, j < 14 ∧ t = j + 14 * k :=
        ⟨t / 14, t % 14, Nat.mod_lt _ (by omega), (Nat.mod_add_div t 14).symm⟩
      subst hje
      have hret : ∀ l : Nat, ∀ ret ∈ (vrets obj op l), ret.command ≠ ocmd op := by
        intro l ret hmem
        obtain ⟨j', -, he⟩ := vrets_command obj op l ret hmem
        rw [he]; exact vcmd_ne_ocmd op j'
      show ∀ ret ∈ (vstate obj op (j + 14 * k + 1)).returns, _
      rw [vstate_at obj op k j hj]
      match j, hj with
      | 0, _ => exact hret k
      | 1, _ => exact hret k
      | 2, _ => exact hret k
      | 3, _ => exact hret k
      | 4, _ => exact hret k
      | 5, _ => exact hret k
      | 6, _ => exact hret k
      | 7, _ => exact hret k
      | 8, _ => exact hret k
      | 9, _ => exact hret k
      | 10, _ => exact hret k
      | 11, _ => exact hret k
      | 12, _ => exact hret k
      | 13, _ => exact hret k
      | (n + 14), h => exact absurd h (by omega)

/-! ### The schedule

Process `1` acts at the single prologue tick; process `0` acts for ever after. -/

def vactor : Nat → Option (Fin 2) := fun t => if t < 1 then some 1 else some 0

omit [DecidableEq Op] in
theorem vactor_prologue {t : Nat} (h : t < 1) : vactor t = some 1 := by simp [vactor, h]

omit [DecidableEq Op] in
theorem vactor_main (t : Nat) : vactor (t + 1) = some 0 := by simp [vactor]

theorem vcyc_localState (k j : Nat) :
    ∃ l, (vcyc obj op k j).localState = vloc obj op l := by
  unfold vcyc
  split <;> exact ⟨_, rfl⟩

/-- Process `1` stays parked from the end of the prologue on. -/
theorem vstate_park (t : Nat) : (vstate obj op (t + 1)).localState 1 = park obj op := by
  obtain ⟨l, hl⟩ := vcyc_localState obj op (t / 14) (t % 14)
  show (vcyc obj op (t / 14) (t % 14)).localState 1 = _
  rw [hl, vloc_one]

theorem vround_mid (k j : Nat) (h5 : 5 ≤ j) (h11 : j ≤ 11) :
    weakRound obj ((vstate obj op (j + 14 * k + 1)).localState 0) = some (k + 1) := by
  rw [vstate_at obj op k j (by omega)]
  match j, h5, h11 with
  | 5, _, _ => rfl
  | 6, _, _ => rfl
  | 7, _, _ => rfl
  | 8, _, _ => rfl
  | 9, _, _ => rfl
  | 10, _, _ => rfl
  | 11, _, _ => rfl

theorem vround_none (k j : Nat) (hj : j < 14) (h : ¬ (5 ≤ j ∧ j ≤ 11)) :
    weakRound obj ((vstate obj op (j + 14 * k + 1)).localState 0) = none := by
  rw [vstate_at obj op k j hj]
  match j, hj, h with
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | 5, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 6, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 7, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 8, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 9, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 10, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 11, _, hh => exact absurd ⟨by omega, by omega⟩ hh
  | 12, _, _ => rfl
  | 13, _, _ => rfl
  | (n + 14), hh, _ => exact absurd hh (by omega)

/-- Before the end of the prologue nobody is inside a GCA call. -/
theorem vround_prologue {t : Nat} (h : t < 1) {p : Fin 2} :
    weakRound obj ((vstate obj op t).localState p) = none := by
  match t, h with
  | 0, _ => rcases fin2 p with rfl | rfl <;> rfl

/-! ### The projected protocol clock -/

omit [DecidableEq Op] in
private theorem clock_succ_ne {st : Nat → Configuration (n := 2) obj}
    {act : Nat → Option (Fin 2)} {t r : Nat}
    (h : ∀ p, gcaEvent obj st act t ≠ some (r, p)) :
    gcaClock obj st act (t + 1) r = gcaClock obj st act t r := by
  rw [gcaClock]
  cases hev : gcaEvent obj st act t with
  | none => rfl
  | some rp =>
    obtain ⟨r', p⟩ := rp
    have hne : ¬ r' = r := fun hr => h p (by rw [hev, hr])
    simp [hne]

omit [DecidableEq Op] in
private theorem clock_succ_eq {st : Nat → Configuration (n := 2) obj}
    {act : Nat → Option (Fin 2)} {t r : Nat} {p : Fin 2}
    (h : gcaEvent obj st act t = some (r, p)) :
    gcaClock obj st act (t + 1) r = gcaClock obj st act t r + 1 := by
  rw [gcaClock, h]; simp

theorem vevent_mid (k j : Nat) (h5 : 5 ≤ j) (h11 : j ≤ 11) :
    gcaEvent obj (vstate obj op) vactor (j + 14 * k + 1) = some (k + 1, 0) :=
  gcaEvent_spec obj (vactor_main (j + 14 * k)) (vround_mid obj op k j h5 h11)

theorem vevent_none (k j : Nat) (hj : j < 14) (h : ¬ (5 ≤ j ∧ j ≤ 11)) :
    gcaEvent obj (vstate obj op) vactor (j + 14 * k + 1) = none := by
  simp [gcaEvent, vactor_main (j + 14 * k), vround_none obj op k j hj h]

theorem vevent_prologue {t : Nat} (h : t < 1) :
    gcaEvent obj (vstate obj op) vactor t = none := by
  simp [gcaEvent, vactor_prologue h, vround_prologue obj op h]

theorem vevent_ne (k : Nat) : ∀ t, t < 5 + 14 * k + 1 →
    ∀ p, gcaEvent obj (vstate obj op) vactor t ≠ some (k + 1, p) := by
  intro t ht p hp
  rcases Nat.lt_or_ge t 1 with h1 | h1
  · rw [vevent_prologue obj op h1] at hp; simp at hp
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨k', j, hj, rfl⟩ : ∃ k' j, j < 14 ∧ t' = j + 14 * k' :=
      ⟨t' / 14, t' % 14, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 14).symm⟩
    by_cases hmid : 5 ≤ j ∧ j ≤ 11
    · rw [vevent_mid obj op k' j hmid.1 hmid.2] at hp
      have hk : k' + 1 = k + 1 := congrArg Prod.fst (Option.some.inj hp)
      omega
    · rw [vevent_none obj op k' j hj hmid] at hp; simp at hp

theorem vclock_zero (k : Nat) : ∀ t, t ≤ 5 + 14 * k + 1 →
    gcaClock obj (vstate obj op) vactor t (k + 1) = 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      rw [clock_succ_ne obj (vevent_ne obj op k t (by omega))]
      exact ih (by omega)

theorem vclock_mid (k : Nat) : ∀ i, i ≤ 7 →
    gcaClock obj (vstate obj op) vactor ((5 + i) + 14 * k + 1) (k + 1) = i := by
  intro i
  induction i with
  | zero => intro _; exact vclock_zero obj op k _ (by omega)
  | succ i ih =>
      intro hi
      rw [show (5 + (i + 1)) + 14 * k + 1 = ((5 + i) + 14 * k + 1) + 1 from by omega,
        clock_succ_eq obj (vevent_mid obj op k (5 + i) (by omega) (by omega)),
        ih (by omega)]

theorem vclock_eleven (k : Nat) :
    gcaClock obj (vstate obj op) vactor (11 + 14 * k + 1) (k + 1) = 6 := by
  rw [show 11 + 14 * k + 1 = (5 + 6) + 14 * k + 1 from by omega]
  exact vclock_mid obj op k 6 (by omega)

/-! ### The protocol advances one stage per event -/

theorem vprotocol_actor (r : Nat) (hr : r ≠ 0) (t : Nat) :
    ((vfam obj op).protocol r).actor t = some 0 := by simp [vfam, hr]

theorem vprotocol_phase (r : Nat) (hr : r ≠ 0) : ∀ c, c ≤ 6 →
    ((vfam obj op).protocol r).phase c 0 = c := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
      intro hc
      have hstep : ((vfam obj op).protocol r).phase (c + 1) 0
          = GCA.Protocol.advance (((vfam obj op).protocol r).phase c 0) true := by
        rw [GCA.Protocol.phase, vprotocol_actor obj op r hr, ite_eq_left rfl]
        rfl
      rw [hstep, ih (by omega)]
      show GCA.Protocol.advance c true = c + 1
      simp [GCA.Protocol.advance]
      omega

/-! ### The global schedule -/

/-- **A contended infinite run of Algorithm 1 over two processes.**  Process `1`
invokes at the prologue tick and then never moves; process `0` completes one
operation per `14`-step cycle for ever.  Offsets `5 … 10` of each cycle are the
round's protocol events and the rest are program steps. -/
noncomputable def vsched : Weak obj (vfam obj op) where
  run := vrun obj op
  actor := vactor
  step_actor := by
    intro t
    match t with
    | 0 =>
        refine Or.inr (Or.inl ⟨1, vactor_prologue (by omega),
          step_prologue_invoke obj op, ?_⟩)
        intro q hq
        rcases fin2 q with rfl | rfl
        · show (c0 obj op 0).localState 0 = (WeakUniversal.initial obj).localState 0
          rw [c0_local]; rfl
        · exact absurd rfl hq
    | (t' + 1) =>
        obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 14 ∧ t' = j + 14 * k :=
          ⟨t' / 14, t' % 14, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 14).symm⟩
        by_cases hst : 5 ≤ j ∧ j ≤ 10
        · exact Or.inr (Or.inr ⟨0, k + 1, vactor_main _,
            vround_mid obj op k j hst.1 (by omega), vstutter_at obj op k j hst.1 hst.2⟩)
        · refine Or.inr (Or.inl ⟨0, vactor_main _, vstep_at obj op k j hj hst, ?_⟩)
          intro q hq
          rcases fin2 q with rfl | rfl
          · exact absurd rfl hq
          · show (vstate obj op (j + 14 * k + 1 + 1)).localState 1
              = (vstate obj op (j + 14 * k + 1)).localState 1
            rw [show j + 14 * k + 1 + 1 = (j + 14 * k + 1) + 1 from rfl,
              vstate_park, vstate_park]
  gca_actor := by
    intro t p r hact hr
    rw [vrun_state] at hr
    rcases Nat.lt_or_ge t 1 with h1 | h1
    · rw [vround_prologue obj op h1] at hr; exact absurd hr (by simp)
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have hp : p = 0 := (Option.some.inj ((vactor_main t').symm.trans hact)).symm
      subst hp
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 14 ∧ t' = j + 14 * k :=
        ⟨t' / 14, t' % 14, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 14).symm⟩
      by_cases hmid : 5 ≤ j ∧ j ≤ 11
      · have hrk : r = k + 1 :=
          (Option.some.inj ((vround_mid obj op k j hmid.1 hmid.2).symm.trans hr)).symm
        subst r
        exact vprotocol_actor obj op (k + 1) (by omega) _
      · rw [vround_none obj op k j hj hmid] at hr; exact absurd hr (by simp)
  no_ghost := by
    intro r p s hi
    by_cases hp : p = 0
    · subst p
      refine ⟨5 + 14 * r + 1, vtr obj op (r + 1), ?_⟩
      show (⟨r + 1, 0, vtr obj op (r + 1)⟩ : Call (n := 2) obj)
        ∈ (vstate obj op (5 + 14 * r + 1)).calls
      rw [vstate_at obj op r 5 (by omega)]
      show _ ∈ vcalls obj op (r + 1)
      exact List.mem_cons_self ..
    · rw [vfam_input_none obj op (r + 1) hp] at hi
      exact absurd hi (by simp)
  receive_ready := by
    intro t p r hr hchange
    rw [vrun_state] at hr hchange
    rcases Nat.lt_or_ge t 1 with h1 | h1
    · rw [vround_prologue obj op h1] at hr; exact absurd hr (by simp)
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 14 ∧ t' = j + 14 * k :=
        ⟨t' / 14, t' % 14, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 14).symm⟩
      rcases fin2 p with rfl | rfl
      · by_cases hmid : 5 ≤ j ∧ j ≤ 11
        · have hrk : r = k + 1 :=
            (Option.some.inj ((vround_mid obj op k j hmid.1 hmid.2).symm.trans hr)).symm
          subst r
          have hj11 : j = 11 := by
            apply Classical.byContradiction
            intro hne
            exact hchange (congrArg (fun c => c.localState 0)
              (vstutter_at obj op k j hmid.1 (by omega)))
          subst j
          rw [vrun_state, vclock_eleven obj op k]
          exact vprotocol_phase obj op (k + 1) (by omega) 6 (by omega)
        · rw [vround_none obj op k j hj hmid] at hr; exact absurd hr (by simp)
      · rw [vstate_park] at hr
        exact absurd hr (by simp [park, weakRound])

theorem vsched_state (t : Nat) : (vsched obj op).run.state t = vstate obj op t := rfl

theorem vsched_actor (t : Nat) : (vsched obj op).actor t = vactor t := rfl

theorem vsched_state_fun : (vsched obj op).run.state = vstate obj op := rfl

theorem vsched_actor_fun : (vsched obj op).actor = vactor := rfl

/-- **Fairness.**  The `receive` step is taken exactly when the projected
protocol clock shows the last stage, at offset `11` of the cycle. -/
theorem vsched_fair : (vsched obj op).Fair := by
  intro t p cmd r proposal hact hl hphase _
  rw [vsched_state] at hl
  rw [vsched_actor] at hact
  rcases Nat.lt_or_ge t 1 with h1 | h1
  · exfalso
    have hnone := vround_prologue obj op h1 (p := p)
    rw [hl] at hnone
    exact absurd hnone (by simp [weakRound])
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hp : p = 0 := (Option.some.inj ((vactor_main t').symm.trans hact)).symm
    subst hp
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 14 ∧ t' = j + 14 * k :=
      ⟨t' / 14, t' % 14, Nat.mod_lt _ (by omega), (Nat.mod_add_div t' 14).symm⟩
    have hround : weakRound obj
        ((vstate obj op (j + 14 * k + 1)).localState 0) = some r := by rw [hl]; rfl
    by_cases hmid : 5 ≤ j ∧ j ≤ 11
    · have hrk : r = k + 1 :=
        (Option.some.inj ((vround_mid obj op k j hmid.1 hmid.2).symm.trans hround)).symm
      subst r
      rw [vsched_state_fun, vsched_actor_fun] at hphase
      have hj11 : j = 11 := by
        apply Classical.byContradiction
        intro hne
        rw [show j + 14 * k + 1 = (5 + (j - 5)) + 14 * k + 1 from by omega,
          vclock_mid obj op k (j - 5) (by omega),
          vprotocol_phase obj op (k + 1) (by omega) (j - 5) (by omega)] at hphase
        omega
      subst j
      refine ⟨vstep_at obj op k 11 (by omega) (by omega), ?_⟩
      intro q hq
      rcases fin2 q with rfl | rfl
      · exact absurd rfl hq
      · show (vstate obj op (11 + 14 * k + 1 + 1)).localState 1
          = (vstate obj op (11 + 14 * k + 1)).localState 1
        rw [show 11 + 14 * k + 1 + 1 = (11 + 14 * k + 1) + 1 from rfl,
          vstate_park, vstate_park]
    · rw [vround_none obj op k j hj hmid] at hround
      exact absurd hround (by simp)

/-- **Operation liveness.**  Process `0` holds a command whenever it is waiting. -/
theorem vsched_opLive : (vsched obj op).OpLive := by
  intro N
  refine ⟨5 + 14 * N, by omega, ?_⟩
  have h : (vsched obj op).opActor (5 + 14 * N) = some (vcmd op N) := by
    show (match vactor (5 + 14 * N + 1) with
      | none => none
      | some p => (WeakUniversal.ledger obj
          (vstate obj op (5 + 14 * N + 1))).active p) = _
    rw [vactor_main (5 + 14 * N)]
    show ((vstate obj op (5 + 14 * N + 1)).localState 0).command obj = _
    rw [vstate_at obj op N 5 (by omega)]
    rfl
  rw [h]
  rfl

end ConflictFreedom.GlobalSchedule.WitnessW

namespace ConflictFreedom
variable {State Op Response : Type} [DecidableEq Op]

/-- **The admitted set of Algorithm 1 contains a contended run.**  Unlike
`algorithm1_nonempty`, whose witness runs a single worker with permanently idle
bystanders, this one has two operations simultaneously in flight. -/
theorem algorithm1_nonempty_contended (obj : Object State Op Response) (op : Op) :
    ∃ e, algorithm1 obj 2 e :=
  ⟨_, GlobalSchedule.WitnessW.vfam obj op, GlobalSchedule.WitnessW.vsched obj op,
    GlobalSchedule.WitnessW.vsched_opLive obj op,
    GlobalSchedule.WitnessW.vsched_fair obj op,
    GlobalSchedule.WitnessW.vfam_waitFree obj op, rfl⟩

/-- **Algorithm 1's admitted set contains an execution with two operation
instances concurrently pending.**  This is what `Witness.rsched` could
not show: `algorithm1_weakConflictFree` is non-vacuous on a *contended* run, so
§3's conflict hypothesis — which speaks about two pending instances — really
has instances to speak about. -/
theorem algorithm1_contended (obj : Object State Op Response) (op : Op) :
    ∃ e : Execution 2 Op, algorithm1 obj 2 e ∧
      ∃ (i j : e.Instance) (t : Nat), i ≠ j ∧ e.Pending i t ∧ e.Pending j t := by
  classical
  have hp := GlobalSchedule.WitnessW.vsched_opLive obj op
  obtain ⟨⟨hw, ho⟩, hret, hne⟩ := GlobalSchedule.WitnessW.two_in_flight obj op 0
  have hmem : ∀ a : WeakUniversal.Cmd 2 Op,
      a ∈ ((GlobalSchedule.WitnessW.vrun obj op).state (5 + 14 * 0 + 1)).invocations →
      a ∈ (InvocationLedger.obs
        ((GlobalSchedule.WitnessW.vsched obj op).run.ledgerRun obj) 5).invoked := by
    intro a ha
    show a ∈ ((GlobalSchedule.WitnessW.vsched obj op).run.state (5 + 1)).invocations
    exact ha
  have hnotret : ∀ a : WeakUniversal.Cmd 2 Op,
      (∀ ret ∈ ((GlobalSchedule.WitnessW.vrun obj op).state (5 + 14 * 0 + 1)).returns,
        ret.command ≠ a) →
      a ∉ (InvocationLedger.obs
        ((GlobalSchedule.WitnessW.vsched obj op).run.ledgerRun obj) 5).returned := by
    intro a ha hm
    obtain ⟨ret, hret', he⟩ := List.mem_map.mp hm
    exact ha ret hret' he
  refine ⟨(GlobalSchedule.WitnessW.vsched obj op).execution hp,
    ⟨_, GlobalSchedule.WitnessW.vsched obj op, hp,
      GlobalSchedule.WitnessW.vsched_fair obj op,
      GlobalSchedule.WitnessW.vfam_waitFree obj op, rfl⟩, ?_⟩
  refine ⟨⟨GlobalSchedule.WitnessW.vcmd op 0, ⟨5, hmem _ hw⟩⟩,
    ⟨GlobalSchedule.WitnessW.ocmd op, ⟨5, hmem _ ho⟩⟩, 5,
    fun h => hne (congrArg Subtype.val h), ?_, ?_⟩
  · exact ((_ : InvocationLedger.Schedule _).execution_pending_iff _ 5).mpr
      ⟨hmem _ hw, hnotret _ (fun ret hr => (hret ret hr).1)⟩
  · exact ((_ : InvocationLedger.Schedule _).execution_pending_iff _ 5).mpr
      ⟨hmem _ ho, hnotret _ (fun ret hr => (hret ret hr).2)⟩

end ConflictFreedom
