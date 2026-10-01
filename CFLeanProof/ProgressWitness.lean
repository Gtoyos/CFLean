import CFLeanProof.UniversalImplementation
import CFLeanProof.InfiniteEventLinearization
import CFLeanProof.Algorithm2Interface

/-! # An infinite fair, operation-live run of Algorithm 1

`Witness.completedSchedule` completes one operation and then
idles, so it is neither `Fair` (it idles inside a finished call) nor `OpLive`.
This module repeats its cycle forever, over `m + 1` processes of which only
the first ever takes a step: process `0` invokes, reads all `m + 1` registers,
collects, proposes, lets round `k+1` take its six protocol events, receives,
publishes and returns, and then starts again.  The cycle is `m + 13` steps.

The result is `Fair`, `OpLive`, solo, and above a wait-free snapshot
interface — the schedule the progress theorems and the `algorithm1` wrapper
need, at every process count `n = m + 1 ≥ 1`.
-/
namespace ConflictFreedom.GlobalSchedule.Witness
open WeakUniversal
open UniversalProtocol
variable {State Op Response : Type} (m : Nat) (obj : Object State Op Response)
variable [DecidableEq Op] (op : Op)

/-- The `(k+1)`-st command of the working process. -/
def rcmd (k : Nat) : Cmd (m + 1) Op := ⟨op, 0, k + 1⟩

/-- The trace committed in round `k`; round zero is the empty trace. -/
noncomputable def rtr : Nat → (Tagged (n := m + 1) obj).Trace
  | 0 => (Tagged (n := m + 1) obj).emptyTrace
  | k + 1 => (Tagged (n := m + 1) obj).appendMissing (rtr k) (rcmd m op k)

/-- The seed published after `k` completed operations. -/
noncomputable def rseed (k : Nat) : Seed (n := m + 1) obj := ⟨k, rtr m obj op k⟩

/-- Only the working process ever writes a register. -/
noncomputable def rslots (k : Nat) : Fin (m + 1) → Seed (n := m + 1) obj :=
  fun q => if q = 0 then rseed m obj op k else zeroSeed obj

/-- Only the working process ever invokes. -/
def rseq (k : Nat) : Fin (m + 1) → Nat := fun q => if q = 0 then k else 0

/-- Only the working process is ever non-idle. -/
def rlocal (l : Local (n := m + 1) obj) : Fin (m + 1) → Local (n := m + 1) obj :=
  WeakUniversal.update (fun _ => Local.idle) 0 l

/-- The best seed collected after `i` of the `m + 1` register reads.  The
working process reads its own register first, so one read already suffices. -/
noncomputable def racc (k i : Nat) : Seed (n := m + 1) obj :=
  if i = 0 then zeroSeed obj else rseed m obj op k

/-- Calls, responses and invocations accumulated after `k` cycles. -/
noncomputable def rcalls : Nat → List (Call (n := m + 1) obj)
  | 0 => []
  | k + 1 => (⟨k + 1, 0, rtr m obj op (k + 1)⟩ : Call (n := m + 1) obj) :: rcalls k

noncomputable def rreturns : Nat → List (Return (n := m + 1) obj)
  | 0 => []
  | k + 1 =>
      (⟨rcmd m op k, k + 1, rtr m obj op (k + 1)⟩ : Return (n := m + 1) obj) :: rreturns k

def rinv : Nat → List (Cmd (m + 1) Op)
  | 0 => []
  | k + 1 => rcmd m op k :: rinv k

/-! ### Pointwise behaviour of the three per-process fields -/

omit [DecidableEq Op] in
theorem rlocal_zero (l : Local (n := m + 1) obj) : rlocal m obj l 0 = l := by
  simp [rlocal, WeakUniversal.update]

omit [DecidableEq Op] in
theorem rlocal_ne (l : Local (n := m + 1) obj) {q : Fin (m + 1)} (hq : q ≠ 0) :
    rlocal m obj l q = .idle := by
  simp [rlocal, WeakUniversal.update, hq]

omit [DecidableEq Op] in
theorem update_rlocal (l v : Local (n := m + 1) obj) :
    WeakUniversal.update (rlocal m obj l) 0 v = rlocal m obj v := by
  funext q
  by_cases h : q = 0 <;> simp [rlocal, WeakUniversal.update, h]

theorem rslots_zero (k : Nat) : rslots m obj op k 0 = rseed m obj op k := by simp [rslots]

theorem rslots_ne (k : Nat) {q : Fin (m + 1)} (hq : q ≠ 0) :
    rslots m obj op k q = zeroSeed obj := by simp [rslots, hq]

theorem update_rslots (k : Nat) :
    WeakUniversal.update (rslots m obj op k) 0
        (⟨k + 1, rtr m obj op (k + 1)⟩ : Seed (n := m + 1) obj) = rslots m obj op (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [rslots, WeakUniversal.update, h, rseed]

omit [DecidableEq Op] in
theorem rseq_zero (k : Nat) : rseq m k 0 = k := by simp [rseq]

omit [DecidableEq Op] in
theorem update_rseq (k : Nat) :
    WeakUniversal.update (rseq m k) 0 (k + 1) = rseq m (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [rseq, WeakUniversal.update, h]

/-! ### The configurations of one cycle -/

noncomputable def r0 (k : Nat) : Configuration (n := m + 1) obj where
  sequence := rseq m k
  localState := rlocal m obj .idle
  slots := rslots m obj op k
  calls := rcalls m obj op k
  returns := rreturns m obj op k
  invocations := rinv m op k

/-- After the invocation and `i` register reads. -/
noncomputable def rcol (k i : Nat) : Configuration (n := m + 1) obj :=
  { r0 m obj op k with
    sequence := rseq m (k + 1)
    invocations := rinv m op (k + 1)
    localState := rlocal m obj
      (.collecting (rcmd m op k) ((List.finRange (m + 1)).drop i) (racc m obj op k i)) }

noncomputable def rready (k : Nat) : Configuration (n := m + 1) obj :=
  { rcol m obj op k (m + 1) with
    localState := rlocal m obj (.ready (rcmd m op k) (rseed m obj op k)) }

noncomputable def rwait (k : Nat) : Configuration (n := m + 1) obj :=
  { rready m obj op k with
    localState := rlocal m obj (.waiting (rcmd m op k) (k + 1) (rtr m obj op (k + 1)))
    calls := rcalls m obj op (k + 1) }

noncomputable def rpub (k : Nat) : Configuration (n := m + 1) obj :=
  { rwait m obj op k with
    localState := rlocal m obj (.publishing (rcmd m op k) (k + 1) (rtr m obj op (k + 1))) }

noncomputable def rret (k : Nat) : Configuration (n := m + 1) obj :=
  { rpub m obj op k with
    localState := rlocal m obj (.returning (rcmd m op k) (k + 1) (rtr m obj op (k + 1)))
    slots := rslots m obj op (k + 1) }

theorem r0_local (k : Nat) : (r0 m obj op k).localState 0 = .idle := rlocal_zero ..
theorem rcol_local (k i : Nat) : (rcol m obj op k i).localState 0 =
    .collecting (rcmd m op k) ((List.finRange (m + 1)).drop i) (racc m obj op k i) :=
  rlocal_zero ..
theorem rready_local (k : Nat) : (rready m obj op k).localState 0 =
    .ready (rcmd m op k) (rseed m obj op k) := rlocal_zero ..
theorem rwait_local (k : Nat) : (rwait m obj op k).localState 0 =
    .waiting (rcmd m op k) (k + 1) (rtr m obj op (k + 1)) := rlocal_zero ..
theorem rpub_local (k : Nat) : (rpub m obj op k).localState 0 =
    .publishing (rcmd m op k) (k + 1) (rtr m obj op (k + 1)) := rlocal_zero ..
theorem rret_local (k : Nat) : (rret m obj op k).localState 0 =
    .returning (rcmd m op k) (k + 1) (rtr m obj op (k + 1)) := rlocal_zero ..

/-! ### The GCA family: one always-acknowledging participant per positive round -/

noncomputable def rfam : Family (n := m + 1) obj where
  protocol := fun r =>
    { participants := if r = 0 then [] else [0]
      input := fun _ => rtr m obj op r
      actor := fun _ => if r = 0 then none else some 0
      actor_valid := by
        intro t p h
        by_cases hr : r = 0
        · simp [hr] at h
        · simp [hr] at h ⊢
          exact h.symm
      acknowledged := fun _ => true }

theorem rfam_waitFree : (rfam m obj op).SnapshotWaitFree obj :=
  fun _ => GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)

theorem rfam_input (r : Nat) (hr : r ≠ 0) :
    ((rfam m obj op).environment obj r).input 0 = some (rtr m obj op r) := by
  simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
    GCA.TimedExecution.views, GCA.SnapshotExecution.history, rfam, hr]

theorem rfam_input_none (r : Nat) {p : Fin (m + 1)} (hp : p ≠ 0) :
    ((rfam m obj op).environment obj r).input p = none := by
  by_cases hr : r = 0 <;>
    simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
      GCA.TimedExecution.views, GCA.SnapshotExecution.history, rfam, hr, hp]

/-- A lone always-acknowledged participant commits its own proposal. -/
theorem rfam_output (r : Nat) (hr : r ≠ 0) :
    ((rfam m obj op).environment obj r).output 0 = some (rtr m obj op r, true) := by
  have hw : ((rfam m obj op).protocol r).SnapshotWaitFree :=
    GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)
  have hinf : ((rfam m obj op).protocol r).InfiniteSteps 0 :=
    fun N => ⟨N, Nat.le_refl _, by simp [rfam, hr]⟩
  obtain ⟨s, flag, ho⟩ := ((rfam m obj op).protocol r).returned_of_infiniteSteps hw hinf
  have huniform : ∀ u, (((rfam m obj op).environment obj r).Inputs u) → u = rtr m obj op r := by
    intro u hu
    rw [Family.environment, GCA.Protocol.history, GCA.SnapshotExecution.inputs_iff] at hu
    obtain ⟨p, -, he⟩ := hu
    exact he.symm
  obtain ⟨rfl, rfl⟩ := (((rfam m obj op).environment obj r).uniform_return
    ((rfam m obj op).specification obj r) huniform ho)
  exact ho

/-! ### The steps of one cycle -/

theorem r0_seq (k : Nat) : (r0 m obj op k).sequence = rseq m k := rfl
theorem r0_inv (k : Nat) : (r0 m obj op k).invocations = rinv m op k := rfl
theorem r0_localState (k : Nat) : (r0 m obj op k).localState = rlocal m obj .idle := rfl
theorem rcol_slots (k i : Nat) : (rcol m obj op k i).slots = rslots m obj op k := rfl
theorem rcol_localState (k i : Nat) : (rcol m obj op k i).localState =
    rlocal m obj (.collecting (rcmd m op k) ((List.finRange (m + 1)).drop i)
      (racc m obj op k i)) := rfl
theorem rready_localState (k : Nat) : (rready m obj op k).localState =
    rlocal m obj (.ready (rcmd m op k) (rseed m obj op k)) := rfl
theorem rwait_localState (k : Nat) : (rwait m obj op k).localState =
    rlocal m obj (.waiting (rcmd m op k) (k + 1) (rtr m obj op (k + 1))) := rfl
theorem rpub_localState (k : Nat) : (rpub m obj op k).localState =
    rlocal m obj (.publishing (rcmd m op k) (k + 1) (rtr m obj op (k + 1))) := rfl
theorem rret_localState (k : Nat) : (rret m obj op k).localState =
    rlocal m obj (.returning (rcmd m op k) (k + 1) (rtr m obj op (k + 1))) := rfl
theorem rpub_slots (k : Nat) : (rpub m obj op k).slots = rslots m obj op k := rfl

/-- The working process reads its own register first, so the collected seed is
the one it published in the previous cycle; the bystanders' empty registers
never improve on it. -/
theorem rbest_step (k i : Nat) (hi : i < m + 1)
    (hlen : i < (List.finRange (m + 1)).length) :
    best obj (racc m obj op k i) (rslots m obj op k ((List.finRange (m + 1))[i]'hlen))
      = racc m obj op k (i + 1) := by
  have hget : ((List.finRange (m + 1))[i]'hlen).val = i := by simp [List.getElem_finRange]
  by_cases h0 : i = 0
  · subst i
    have hq : ((List.finRange (m + 1))[0]'hlen) = 0 := by
      apply Fin.ext
      simp
    rw [hq, rslots_zero]
    have hacc0 : racc m obj op k 0 = zeroSeed obj := by simp [racc]
    have hacc1 : racc m obj op k 1 = rseed m obj op k := by simp [racc]
    rw [hacc0, hacc1]
    unfold best
    by_cases hk : (zeroSeed (n := m + 1) obj).round < (rseed m obj op k).round
    · simp only [hk, reduceIte]
    · have hk0 : k = 0 := by
        simp only [zeroSeed, rseed, Nat.not_lt, Nat.le_zero] at hk
        exact hk
      subst k
      simp only [hk, reduceIte]
      rfl
  · have hq : ((List.finRange (m + 1))[i]'hlen) ≠ 0 := by
      intro he
      rw [he] at hget
      simp only [Fin.val_zero] at hget
      exact h0 hget.symm
    rw [rslots_ne m obj op k hq]
    have hacci : racc m obj op k i = rseed m obj op k := by simp [racc, h0]
    have hacc1 : racc m obj op k (i + 1) = rseed m obj op k := by simp [racc]
    rw [hacci, hacc1]
    unfold best
    have hno : ¬ ((rseed m obj op k).round < (zeroSeed (n := m + 1) obj).round) := by
      simp [rseed, zeroSeed]
    simp only [hno, reduceIte]

section Steps
variable {H : Environment (n := m + 1) obj}

theorem rstep_invoke (k : Nat) : Step obj H (r0 m obj op k) (rcol m obj op k 0) := by
  have h := Step.invoke (H := H) (r0 m obj op k) 0 op (r0_local m obj op k)
    (List.finRange (m + 1)) (List.Perm.refl _)
  simp only [r0_seq, r0_inv, r0_localState, rseq_zero, update_rseq, update_rlocal] at h
  exact h

theorem rstep_read (k i : Nat) (hi : i < m + 1) :
    Step obj H (rcol m obj op k i) (rcol m obj op k (i + 1)) := by
  have hlen : i < (List.finRange (m + 1)).length := by
    rw [List.length_finRange]; exact hi
  have hloc : (rcol m obj op k i).localState 0 =
      .collecting (rcmd m op k) (((List.finRange (m + 1))[i]'hlen) ::
        (List.finRange (m + 1)).drop (i + 1)) (racc m obj op k i) := by
    rw [rcol_local, List.drop_eq_getElem_cons hlen]
  have h := Step.read (H := H) (rcol m obj op k i) 0 ((List.finRange (m + 1))[i]'hlen)
    (rcmd m op k) ((List.finRange (m + 1)).drop (i + 1)) (racc m obj op k i) hloc
  simp only [rcol_slots, rbest_step m obj op k i hi hlen, rcol_localState, update_rlocal] at h
  exact h

theorem rstep_collected (k : Nat) :
    Step obj H (rcol m obj op k (m + 1)) (rready m obj op k) := by
  have hdrop : (List.finRange (m + 1)).drop (m + 1) = [] := by
    have hd := List.drop_length (l := List.finRange (m + 1))
    rwa [List.length_finRange] at hd
  have hacc : racc m obj op k (m + 1) = rseed m obj op k := by simp [racc]
  have hloc : (rcol m obj op k (m + 1)).localState 0 =
      .collecting (rcmd m op k) [] (rseed m obj op k) := by
    rw [rcol_local, hdrop, hacc]
  have h := Step.collected (H := H) (rcol m obj op k (m + 1)) 0 (rcmd m op k)
    (rseed m obj op k) hloc
  simp only [rcol_localState, update_rlocal] at h
  exact h

theorem rstep_propose (k : Nat) :
    Step obj ((rfam m obj op).environment obj) (rready m obj op k) (rwait m obj op k) := by
  have h := Step.propose (rready m obj op k) 0 (rcmd m op k) (rseed m obj op k)
    (rready_local m obj op k) (rfam_input m obj op (k + 1) (by omega))
  simp only [rready_localState, update_rlocal] at h
  exact h

theorem rstep_receive (k : Nat) :
    Step obj ((rfam m obj op).environment obj) (rwait m obj op k) (rpub m obj op k) := by
  have h := Step.receive (rwait m obj op k) 0 (rcmd m op k) (k + 1) (rtr m obj op (k + 1))
    (rtr m obj op (k + 1)) true (rwait_local m obj op k)
    (rfam_output m obj op (k + 1) (by omega))
  have hc : 0 < (Tagged (n := m + 1) obj).traceCount (rcmd m op k) (rtr m obj op (k + 1)) :=
    (Tagged (n := m + 1) obj).appendMissing_contains _ _
  simp only [hc, and_self, ite_true, rwait_localState, update_rlocal] at h
  exact h

theorem rstep_publish (k : Nat) : Step obj H (rpub m obj op k) (rret m obj op k) := by
  have h := Step.publish (H := H) (rpub m obj op k) 0 (rcmd m op k) (k + 1)
    (rtr m obj op (k + 1)) (rpub_local m obj op k)
  simp only [rpub_localState, rpub_slots, update_rlocal, update_rslots] at h
  exact h

theorem rstep_finish (k : Nat) : Step obj H (rret m obj op k) (r0 m obj op (k + 1)) := by
  have h := Step.finish (H := H) (rret m obj op k) 0 (rcmd m op k) (k + 1)
    (rtr m obj op (k + 1)) (rret_local m obj op k)
  simp only [rret_localState, update_rlocal] at h
  exact h

end Steps

/-! ### The infinite run

The cycle is `m + 13` steps: one invocation, `m + 1` register reads, the
collect, the proposal, six protocol events at offsets `m+4 … m+9`, the receive
at `m+10`, the publication and the response. -/

noncomputable def rcyc (k j : Nat) : Configuration (n := m + 1) obj :=
  if j = 0 then r0 m obj op k
  else if j ≤ m + 2 then rcol m obj op k (j - 1)
  else if j = m + 3 then rready m obj op k
  else if j ≤ m + 10 then rwait m obj op k
  else if j = m + 11 then rpub m obj op k
  else rret m obj op k

theorem rcyc_0 (k : Nat) : rcyc m obj op k 0 = r0 m obj op k := by simp [rcyc]

theorem rcyc_col (k i : Nat) (hi : i ≤ m + 1) :
    rcyc m obj op k (i + 1) = rcol m obj op k i := by
  have h1 : ¬ (i + 1 = 0) := by omega
  have h2 : i + 1 ≤ m + 2 := by omega
  simp [rcyc, h2]

theorem rcyc_ready (k : Nat) : rcyc m obj op k (m + 3) = rready m obj op k := by
  have h1 : ¬ (m + 3 = 0) := by omega
  have h2 : ¬ (m + 3 ≤ m + 2) := by omega
  simp [rcyc, h2]

theorem rcyc_wait (k j : Nat) (h4 : m + 4 ≤ j) (h10 : j ≤ m + 10) :
    rcyc m obj op k j = rwait m obj op k := by
  have h1 : ¬ (j = 0) := by omega
  have h2 : ¬ (j ≤ m + 2) := by omega
  have h3 : ¬ (j = m + 3) := by omega
  simp [rcyc, h1, h2, h3, h10]

theorem rcyc_pub (k : Nat) : rcyc m obj op k (m + 11) = rpub m obj op k := by
  have h1 : ¬ (m + 11 = 0) := by omega
  have h2 : ¬ (m + 11 ≤ m + 2) := by omega
  have h3 : ¬ (m + 11 = m + 3) := by omega
  have h4 : ¬ (m + 11 ≤ m + 10) := by omega
  simp [rcyc, h2, h4]

theorem rcyc_ret (k : Nat) : rcyc m obj op k (m + 12) = rret m obj op k := by
  have h2 : ¬ (m + 12 ≤ m + 2) := by omega
  have h4 : ¬ (m + 12 ≤ m + 10) := by omega
  simp [rcyc, h2, h4]

/-- Every configuration of the cycle leaves the bystanders idle. -/
theorem rcyc_localState (k j : Nat) :
    ∃ l, (rcyc m obj op k j).localState = rlocal m obj l := by
  unfold rcyc
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · split
          · exact ⟨_, rfl⟩
          · exact ⟨_, rfl⟩

noncomputable def rstate (t : Nat) : Configuration (n := m + 1) obj :=
  rcyc m obj op (t / (m + 13)) (t % (m + 13))

theorem rstate_at (k j : Nat) (hj : j < m + 13) :
    rstate m obj op (j + (m + 13) * k) = rcyc m obj op k j := by
  unfold rstate
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < m + 13), Nat.div_eq_of_lt hj,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj, Nat.zero_add]

/-- **The bystanders never move.** -/
theorem rstate_idle (t : Nat) {q : Fin (m + 1)} (hq : q ≠ 0) :
    (rstate m obj op t).localState q = .idle := by
  obtain ⟨l, hl⟩ := rcyc_localState m obj op (t / (m + 13)) (t % (m + 13))
  show (rcyc m obj op (t / (m + 13)) (t % (m + 13))).localState q = _
  rw [hl, rlocal_ne m obj l hq]

theorem rstutter_at (k j : Nat) (h4 : m + 4 ≤ j) (h9 : j ≤ m + 9) :
    rstate m obj op (j + (m + 13) * k + 1) = rstate m obj op (j + (m + 13) * k) := by
  rw [show j + (m + 13) * k + 1 = (j + 1) + (m + 13) * k from by omega,
    rstate_at m obj op k (j + 1) (by omega), rstate_at m obj op k j (by omega),
    rcyc_wait m obj op k (j + 1) (by omega) (by omega),
    rcyc_wait m obj op k j h4 (by omega)]

theorem rstep_at (k j : Nat) (hj : j < m + 13) (hm2 : ¬ (m + 4 ≤ j ∧ j ≤ m + 9)) :
    Step obj ((rfam m obj op).environment obj)
      (rstate m obj op (j + (m + 13) * k)) (rstate m obj op (j + (m + 13) * k + 1)) := by
  by_cases h0 : j = 0
  · subst j
    rw [show 0 + (m + 13) * k + 1 = 1 + (m + 13) * k from by omega,
      rstate_at m obj op k 0 (by omega), rstate_at m obj op k 1 (by omega),
      rcyc_0, rcyc_col m obj op k 0 (by omega)]
    exact rstep_invoke m obj op k
  · by_cases hc : j ≤ m + 1
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [show i + 1 + (m + 13) * k + 1 = (i + 1 + 1) + (m + 13) * k from by omega,
        rstate_at m obj op k (i + 1) (by omega), rstate_at m obj op k (i + 1 + 1) (by omega),
        rcyc_col m obj op k i (by omega), rcyc_col m obj op k (i + 1) (by omega)]
      exact rstep_read m obj op k i (by omega)
    · by_cases hcc : j = m + 2
      · subst j
        rw [show m + 2 + (m + 13) * k + 1 = (m + 3) + (m + 13) * k from by omega,
          rstate_at m obj op k (m + 2) (by omega), rstate_at m obj op k (m + 3) (by omega),
          rcyc_col m obj op k (m + 1) (by omega), rcyc_ready]
        exact rstep_collected m obj op k
      · have hcases : j = m + 3 ∨ j = m + 10 ∨ j = m + 11 ∨ j = m + 12 := by omega
        rcases hcases with rfl|rfl|rfl|rfl
        · rw [show m + 3 + (m + 13) * k + 1 = (m + 4) + (m + 13) * k from by omega,
            rstate_at m obj op k (m + 3) (by omega), rstate_at m obj op k (m + 4) (by omega),
            rcyc_ready, rcyc_wait m obj op k (m + 4) (by omega) (by omega)]
          exact rstep_propose m obj op k
        · rw [show m + 10 + (m + 13) * k + 1 = (m + 11) + (m + 13) * k from by omega,
            rstate_at m obj op k (m + 10) (by omega), rstate_at m obj op k (m + 11) (by omega),
            rcyc_wait m obj op k (m + 10) (by omega) (by omega), rcyc_pub]
          exact rstep_receive m obj op k
        · rw [show m + 11 + (m + 13) * k + 1 = (m + 12) + (m + 13) * k from by omega,
            rstate_at m obj op k (m + 11) (by omega), rstate_at m obj op k (m + 12) (by omega),
            rcyc_pub, rcyc_ret]
          exact rstep_publish m obj op k
        · rw [show m + 12 + (m + 13) * k + 1 = 0 + (m + 13) * (k + 1) from by
              rw [Nat.mul_succ]; omega,
            rstate_at m obj op k (m + 12) (by omega),
            rstate_at m obj op (k + 1) 0 (by omega), rcyc_ret, rcyc_0]
          exact rstep_finish m obj op k

theorem rnext (t : Nat) :
    rstate m obj op (t + 1) = rstate m obj op t ∨
    Step obj ((rfam m obj op).environment obj)
      (rstate m obj op t) (rstate m obj op (t + 1)) := by
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < m + 13 ∧ t = j + (m + 13) * k :=
    ⟨t / (m + 13), t % (m + 13), Nat.mod_lt _ (by omega),
      (Nat.mod_add_div t (m + 13)).symm⟩
  by_cases hm2 : m + 4 ≤ j ∧ j ≤ m + 9
  · exact Or.inl (rstutter_at m obj op k j hm2.1 hm2.2)
  · exact Or.inr (rstep_at m obj op k j hj hm2)

theorem r0_zero_eq_initial : r0 m obj op 0 = WeakUniversal.initial obj := by
  have hseq : rseq m 0 = (fun _ => 0 : Fin (m + 1) → Nat) := by
    funext q; simp [rseq]
  have hloc : rlocal m obj .idle = (fun _ => (Local.idle : Local (n := m + 1) obj)) := by
    funext q; by_cases h : q = 0 <;> simp [rlocal, WeakUniversal.update, h]
  have hsl : rslots m obj op 0 = (fun _ => zeroSeed (n := m + 1) obj) := by
    funext q
    by_cases h : q = 0
    · simp [rslots, h]; rfl
    · simp [rslots, h]
  show (⟨rseq m 0, rlocal m obj .idle, rslots m obj op 0, [], [], []⟩ :
      Configuration (n := m + 1) obj) = _
  rw [hseq, hloc, hsl]
  rfl

noncomputable def rrun : WeakUniversal.Execution obj ((rfam m obj op).environment obj) where
  state := rstate m obj op
  initial_state := by
    show rcyc m obj op (0 / (m + 13)) (0 % (m + 13)) = WeakUniversal.initial obj
    rw [Nat.zero_div, Nat.zero_mod, rcyc_0]
    exact r0_zero_eq_initial m obj op
  next := rnext m obj op

theorem rrun_state (t : Nat) : (rrun m obj op).state t = rstate m obj op t := rfl

theorem rrun_state_fun : (rrun m obj op).state = rstate m obj op := rfl

/-! ### The round-`k+1` clock reaches the last protocol stage at offset `m+10` -/

/-- The working process is scheduled at every instant; the bystanders never
take a step. -/
def ractor : Nat → Option (Fin (m + 1)) := fun _ => some 0

theorem rround_mid (k j : Nat) (h4 : m + 4 ≤ j) (h10 : j ≤ m + 10) :
    weakRound obj ((rstate m obj op (j + (m + 13) * k)).localState 0) = some (k + 1) := by
  rw [rstate_at m obj op k j (by omega), rcyc_wait m obj op k j h4 h10, rwait_local]
  rfl

theorem rround_none (k j : Nat) (hj : j < m + 13) (h : ¬ (m + 4 ≤ j ∧ j ≤ m + 10)) :
    weakRound obj ((rstate m obj op (j + (m + 13) * k)).localState 0) = none := by
  rw [rstate_at m obj op k j hj]
  by_cases h0 : j = 0
  · subst j; rw [rcyc_0, r0_local]; rfl
  · by_cases hc : j ≤ m + 2
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [rcyc_col m obj op k i (by omega), rcol_local]; rfl
    · by_cases hr : j = m + 3
      · subst j; rw [rcyc_ready, rready_local]; rfl
      · have hcases : j = m + 11 ∨ j = m + 12 := by omega
        rcases hcases with rfl|rfl
        · rw [rcyc_pub, rpub_local]; rfl
        · rw [rcyc_ret, rret_local]; rfl

theorem revent_mid (k j : Nat) (h4 : m + 4 ≤ j) (h10 : j ≤ m + 10) :
    gcaEvent obj (rstate m obj op) (ractor m) (j + (m + 13) * k) = some (k + 1, 0) :=
  gcaEvent_spec obj rfl (rround_mid m obj op k j h4 h10)

theorem revent_none (k j : Nat) (hj : j < m + 13) (h : ¬ (m + 4 ≤ j ∧ j ≤ m + 10)) :
    gcaEvent obj (rstate m obj op) (ractor m) (j + (m + 13) * k) = none := by
  simp [gcaEvent, ractor, rround_none m obj op k j hj h]

omit [DecidableEq Op] in
private theorem clock_succ_ne {st : Nat → Configuration (n := m + 1) obj}
    {act : Nat → Option (Fin (m + 1))} {t r : Nat}
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
private theorem clock_succ_eq {st : Nat → Configuration (n := m + 1) obj}
    {act : Nat → Option (Fin (m + 1))} {t r : Nat} {p : Fin (m + 1)}
    (h : gcaEvent obj st act t = some (r, p)) :
    gcaClock obj st act (t + 1) r = gcaClock obj st act t r + 1 := by
  rw [gcaClock, h]
  simp

theorem revent_ne (k : Nat) : ∀ t, t < (m + 4) + (m + 13) * k →
    ∀ p, gcaEvent obj (rstate m obj op) (ractor m) t ≠ some (k + 1, p) := by
  intro t ht p hp
  obtain ⟨k', j, hj, rfl⟩ : ∃ k' j, j < m + 13 ∧ t = j + (m + 13) * k' :=
    ⟨t / (m + 13), t % (m + 13), Nat.mod_lt _ (by omega),
      (Nat.mod_add_div t (m + 13)).symm⟩
  by_cases hmid : m + 4 ≤ j ∧ j ≤ m + 10
  · rw [revent_mid m obj op k' j hmid.1 hmid.2] at hp
    have hk : k' + 1 = k + 1 := congrArg Prod.fst (Option.some.inj hp)
    have hk' : k' = k := by omega
    subst k'
    omega
  · rw [revent_none m obj op k' j hj hmid] at hp
    simp at hp

theorem rclock_zero (k : Nat) : ∀ t, t ≤ (m + 4) + (m + 13) * k →
    gcaClock obj (rstate m obj op) (ractor m) t (k + 1) = 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [clock_succ_ne m obj (revent_ne m obj op k t (by omega))]
    exact ih (by omega)

theorem rclock_mid (k : Nat) : ∀ i, i ≤ 7 →
    gcaClock obj (rstate m obj op) (ractor m) ((m + 4 + i) + (m + 13) * k) (k + 1) = i := by
  intro i
  induction i with
  | zero => intro _; exact rclock_zero m obj op k _ (by omega)
  | succ i ih =>
    intro hi
    rw [show (m + 4 + (i + 1)) + (m + 13) * k = ((m + 4 + i) + (m + 13) * k) + 1 from by omega,
      clock_succ_eq m obj (revent_mid m obj op k (m + 4 + i) (by omega) (by omega)),
      ih (by omega)]

theorem rclock_ten (k : Nat) :
    gcaClock obj (rstate m obj op) (ractor m) ((m + 10) + (m + 13) * k) (k + 1) = 6 := by
  rw [show (m + 10) + (m + 13) * k = (m + 4 + 6) + (m + 13) * k from by omega]
  exact rclock_mid m obj op k 6 (by omega)

/-! ### The protocol advances one stage per event -/

theorem rprotocol_actor (r : Nat) (hr : r ≠ 0) (t : Nat) :
    ((rfam m obj op).protocol r).actor t = some 0 := by simp [rfam, hr]

theorem rprotocol_ack (r t : Nat) : ((rfam m obj op).protocol r).acknowledged t = true := rfl

theorem rprotocol_phase_succ (r : Nat) (hr : r ≠ 0) (t : Nat) :
    ((rfam m obj op).protocol r).phase (t + 1) 0 =
      GCA.Protocol.advance (((rfam m obj op).protocol r).phase t 0) true := by
  rw [GCA.Protocol.phase, rprotocol_actor m obj op r hr, ite_eq_left rfl, rprotocol_ack]

theorem rprotocol_phase (r : Nat) (hr : r ≠ 0) : ∀ c, c ≤ 6 →
    ((rfam m obj op).protocol r).phase c 0 = c := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
    intro hc
    rw [rprotocol_phase_succ m obj op r hr c, ih (by omega)]
    show GCA.Protocol.advance c true = c + 1
    unfold GCA.Protocol.advance
    rw [ite_eq_left ⟨by omega, Or.inr (Or.inr rfl)⟩]

/-! ### The schedule -/

/-- **An infinite run of Algorithm 1 over `m + 1` processes that completes one
operation per cycle.**  Only process `0` is ever scheduled; the bystanders
stay idle.  Offsets `m+4` to `m+9` of each cycle are the round's protocol
events and the rest are program steps. -/
noncomputable def rsched : Weak obj (rfam m obj op) where
  run := rrun m obj op
  actor := ractor m
  step_actor := by
    intro t
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < m + 13 ∧ t = j + (m + 13) * k :=
      ⟨t / (m + 13), t % (m + 13), Nat.mod_lt _ (by omega),
        (Nat.mod_add_div t (m + 13)).symm⟩
    by_cases hm2 : m + 4 ≤ j ∧ j ≤ m + 9
    · refine Or.inr (Or.inr ⟨0, k + 1, rfl, ?_, ?_⟩)
      · rw [rrun_state]
        exact rround_mid m obj op k j hm2.1 (by omega)
      · show rstate m obj op (j + (m + 13) * k + 1) = rstate m obj op (j + (m + 13) * k)
        exact rstutter_at m obj op k j hm2.1 hm2.2
    · refine Or.inr (Or.inl ⟨0, rfl, ?_, ?_⟩)
      · show Step obj ((rfam m obj op).environment obj)
          (rstate m obj op (j + (m + 13) * k)) (rstate m obj op (j + (m + 13) * k + 1))
        exact rstep_at m obj op k j hj hm2
      · intro q hq
        show (rstate m obj op (j + (m + 13) * k + 1)).localState q =
          (rstate m obj op (j + (m + 13) * k)).localState q
        rw [rstate_idle m obj op _ hq, rstate_idle m obj op _ hq]
  gca_actor := by
    intro t p r hact hr
    have hp : p = 0 := (Option.some.inj hact).symm
    subst p
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < m + 13 ∧ t = j + (m + 13) * k :=
      ⟨t / (m + 13), t % (m + 13), Nat.mod_lt _ (by omega),
        (Nat.mod_add_div t (m + 13)).symm⟩
    rw [rrun_state] at hr
    by_cases hmid : m + 4 ≤ j ∧ j ≤ m + 10
    · rw [rround_mid m obj op k j hmid.1 hmid.2] at hr
      have hrk : r = k + 1 := (Option.some.inj hr).symm
      subst r
      exact rprotocol_actor m obj op (k + 1) (by omega) _
    · rw [rround_none m obj op k j hj hmid] at hr
      simp at hr
  no_ghost := by
    intro r p s hi
    by_cases hp : p = 0
    · subst p
      refine ⟨(m + 4) + (m + 13) * r, rtr m obj op (r + 1), ?_⟩
      show (⟨r + 1, 0, rtr m obj op (r + 1)⟩ : Call (n := m + 1) obj) ∈
        (rstate m obj op ((m + 4) + (m + 13) * r)).calls
      rw [rstate_at m obj op r (m + 4) (by omega),
        rcyc_wait m obj op r (m + 4) (by omega) (by omega)]
      show _ ∈ rcalls m obj op (r + 1)
      exact List.mem_cons_self ..
    · rw [rfam_input_none m obj op (r + 1) hp] at hi
      exact absurd hi (by simp)
  receive_ready := by
    intro t p r hr hchange
    by_cases hp : p = 0
    · subst p
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < m + 13 ∧ t = j + (m + 13) * k :=
        ⟨t / (m + 13), t % (m + 13), Nat.mod_lt _ (by omega),
          (Nat.mod_add_div t (m + 13)).symm⟩
      rw [rrun_state] at hr
      by_cases hmid : m + 4 ≤ j ∧ j ≤ m + 10
      · rw [rround_mid m obj op k j hmid.1 hmid.2] at hr
        have hrk : r = k + 1 := (Option.some.inj hr).symm
        subst r
        have hj10 : j = m + 10 := by
          apply Classical.byContradiction
          intro hne
          exact hchange (by
            show ((rrun m obj op).state (j + (m + 13) * k + 1)).localState 0 =
              ((rrun m obj op).state (j + (m + 13) * k)).localState 0
            rw [rrun_state, rrun_state, rstutter_at m obj op k j hmid.1 (by omega)])
        subst j
        show ((rfam m obj op).protocol (k + 1)).phase
          (gcaClock obj (rrun m obj op).state (ractor m)
            ((m + 10) + (m + 13) * k) (k + 1)) 0 = 6
        rw [rrun_state_fun, rclock_ten m obj op k]
        exact rprotocol_phase m obj op (k + 1) (by omega) 6 (by omega)
      · rw [rround_none m obj op k j hj hmid] at hr
        simp at hr
    · rw [rrun_state, rstate_idle m obj op t hp] at hr
      simp [weakRound] at hr

theorem rsched_state_fun : (rsched m obj op).run.state = rstate m obj op := rfl

theorem rsched_actor_fun : (rsched m obj op).actor = ractor m := rfl

/-! ### Fairness, operation liveness and solo scheduling -/

/-- **Fairness.**  Whenever the caller is waiting and the projected protocol
clock already shows the last stage — which happens exactly at offset `m+10` —
the schedule takes the `receive` step. -/
theorem rsched_fair : (rsched m obj op).Fair := by
  intro t p cmd r proposal hact hl hphase _
  have hp : p = 0 := (Option.some.inj hact).symm
  subst p
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < m + 13 ∧ t = j + (m + 13) * k :=
    ⟨t / (m + 13), t % (m + 13), Nat.mod_lt _ (by omega),
      (Nat.mod_add_div t (m + 13)).symm⟩
  rw [rsched_state_fun] at hl
  have hround : weakRound obj ((rstate m obj op (j + (m + 13) * k)).localState 0) = some r := by
    rw [hl]; rfl
  by_cases hmid : m + 4 ≤ j ∧ j ≤ m + 10
  · have hrk : r = k + 1 := by
      rw [rround_mid m obj op k j hmid.1 hmid.2] at hround
      exact (Option.some.inj hround).symm
    subst r
    rw [rsched_state_fun, rsched_actor_fun] at hphase
    have hj10 : j = m + 10 := by
      apply Classical.byContradiction
      intro hne
      rw [show j + (m + 13) * k = (m + 4 + (j - (m + 4))) + (m + 13) * k from by omega,
        rclock_mid m obj op k (j - (m + 4)) (by omega),
        rprotocol_phase m obj op (k + 1) (by omega) (j - (m + 4)) (by omega)] at hphase
      omega
    subst j
    refine ⟨?_, ?_⟩
    · show Step obj ((rfam m obj op).environment obj)
        (rstate m obj op ((m + 10) + (m + 13) * k))
        (rstate m obj op ((m + 10) + (m + 13) * k + 1))
      exact rstep_at m obj op k (m + 10) (by omega) (by omega)
    · intro q hq
      show (rstate m obj op ((m + 10) + (m + 13) * k + 1)).localState q =
        (rstate m obj op ((m + 10) + (m + 13) * k)).localState q
      rw [rstate_idle m obj op _ hq, rstate_idle m obj op _ hq]
  · rw [rround_none m obj op k j hj hmid] at hround
    simp at hround

/-- **Operation liveness.**  An operation instance is running just after the
start of every cycle, hence at arbitrarily late instants. -/
theorem rsched_opLive : (rsched m obj op).OpLive := by
  intro N
  refine ⟨(m + 13) * (N + 1), ?_, ?_⟩
  · have h1 : (m + 13) * (N + 1) = m * (N + 1) + 13 * (N + 1) := by rw [Nat.add_mul]
    omega
  · have h : (rsched m obj op).opActor ((m + 13) * (N + 1)) = some (rcmd m op (N + 1)) := by
      show (WeakUniversal.ledger obj (rstate m obj op ((m + 13) * (N + 1) + 1))).active 0 =
        some (rcmd m op (N + 1))
      rw [show (m + 13) * (N + 1) + 1 = 1 + (m + 13) * (N + 1) from by omega,
        rstate_at m obj op (N + 1) 1 (by omega), rcyc_col m obj op (N + 1) 0 (by omega)]
      show WeakUniversal.Local.command obj ((rcol m obj op (N + 1) 0).localState 0) =
        some (rcmd m op (N + 1))
      rw [rcol_local]
      rfl
    rw [h]
    rfl

/-- The working process is scheduled at every instant, hence solo from time 0. -/
theorem rsched_soloFrom : (rsched m obj op).SoloFrom 0 0 :=
  FiniteScheduling.SoloFrom.of_continuous _ (fun _ _ => rfl)

/-- **The progress hypotheses are jointly satisfiable, and with content.**
`solo_completes` applied to this schedule really produces a completed
operation of the solo process. -/
theorem rsched_completes :
    ∃ u v cmd r s, u < v ∧ cmd.process = 0 ∧
      ((rsched m obj op).run.state u).localState 0 = .returning cmd r s ∧
      (⟨cmd, r, s⟩ : Return (n := m + 1) obj) ∈ ((rsched m obj op).run.state v).returns := by
  obtain ⟨u, v, cmd, r, s, -, huv, hproc, hL, hmem⟩ :=
    ((rsched m obj op).toGCA (rsched_fair m obj op) (rfam_waitFree m obj op)).solo_completes
      (rsched_soloFrom m obj op)
  exact ⟨u, v, cmd, r, s, huv, hproc, hL, hmem⟩

/-! ### The run's whole history is infinite

So `Weak.infinite_event_linearization` is exercised on a genuinely infinite
history: the working process invokes a fresh command in every cycle. -/

/-- The working process invokes its `(k+1)`-st command, for every `k`. -/
theorem rsched_invoked (resp : Cmd (m + 1) Op → Response) (k : Nat) :
    (((rsched m obj op).run.ledgerRun obj).events resp).Invoked (rcmd m op k) := by
  refine (((rsched m obj op).run.ledgerRun obj).events_invoked resp _).mpr
    ⟨0 + (m + 13) * (k + 1), ?_⟩
  show rcmd m op k ∈ (rstate m obj op (0 + (m + 13) * (k + 1))).invocations
  rw [rstate_at m obj op (k + 1) 0 (by omega), rcyc_0]
  exact List.mem_cons_self ..

/-- **The run's whole event history is not a finite history.** -/
theorem rsched_history_infinite (resp : Cmd (m + 1) Op → Response)
    (l : History (Cmd (m + 1) Op) Response) :
    ¬ (((rsched m obj op).run.ledgerRun obj).events resp).SameEvents
      (InfiniteHistory.ofHistory l) := by
  intro hs
  have hnd : ((List.range (l.length + 1)).map
      (fun k => (Event.invoke (rcmd m op k) : Event (Cmd (m + 1) Op) Response))).Nodup := by
    refine List.pairwise_map.mpr (List.nodup_range.imp (fun {k k'} hne heq => hne ?_))
    have := congrArg Command.sequence (Event.invoke.inj heq)
    simpa [rcmd] using this
  have hle := length_le_of_nodup_subset hnd (fun ev hev => by
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hev
    exact InfiniteHistory.invoked_ofHistory.mp (hs.invoked_iff.mp (rsched_invoked m obj op resp k)))
  simp only [List.length_map, List.length_range] at hle
  omega

end ConflictFreedom.GlobalSchedule.Witness
