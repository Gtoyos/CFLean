import CFLeanProof.HelpingProgress
import CFLeanProof.Algorithm2Interface

/-! # An infinite fair, operation-live run of Algorithm 3

The same construction as `ProgressWitness` for Algorithm 1, adapted to the
helping construction.  Over `m + 1` processes, only process `0` ever takes a
step; the others stay idle.  One cycle is `3 * m + 16` steps:

* invoke, announce;
* `m + 1` register reads (`readStart`), then `collectedStart`;
* `m + 1` announcement reads (`readAnnouncement`), then `propose`;
* six protocol events, then `receive`, then `publish`;
* `m + 1` register reads (`readCheck`), then `finish`.

Round `k+1` commits `htr (k+1)`, the trace of the first `k+1` commands, and
the worker's own announcement is the only one it ever gathers.
-/
namespace ConflictFreedom.GlobalSchedule.WitnessH
open HelpingUniversal
open UniversalProtocol
open WeakUniversal (Cmd Tagged Seed Call Return update zeroSeed best)
variable {State Op Response : Type} (m : Nat) (obj : Object State Op Response)
variable [DecidableEq Op] (op : Op)

/-- The `(k+1)`-st command of the working process. -/
def hcmd (k : Nat) : Cmd (m + 1) Op := ⟨op, 0, k + 1⟩

/-- The one-command trace. -/
noncomputable def hsingle (a : Cmd (m + 1) Op) : (Tagged (n := m + 1) obj).Trace :=
  Quotient.mk (Tagged (n := m + 1) obj).traceSetoid [a]

theorem hsingle_count (a b : Cmd (m + 1) Op) :
    (Tagged (n := m + 1) obj).traceCount a (hsingle m obj b) = List.count a [b] := rfl

/-- The trace committed in round `k`; round zero is the empty trace. -/
noncomputable def htr : Nat → (Tagged (n := m + 1) obj).Trace
  | 0 => (Tagged (n := m + 1) obj).emptyTrace
  | k + 1 => (Tagged (n := m + 1) obj).traceAppend (htr k) (hsingle m obj (hcmd m op k))

omit [DecidableEq Op] in
theorem htr_succ (k : Nat) : htr m obj op (k + 1) =
    (Tagged (n := m + 1) obj).traceAppend (htr m obj op k) (hsingle m obj (hcmd m op k)) := rfl

/-- The base seed at the start of cycle `k`. -/
noncomputable def hseed (k : Nat) : Seed (n := m + 1) obj := ⟨k, htr m obj op k⟩

/-- A command is missing from every trace committed before its own round. -/
theorem htr_count_zero (k : Nat) : ∀ j, j ≤ k →
    (Tagged (n := m + 1) obj).traceCount (hcmd m op k) (htr m obj op j) = 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hne : ¬ (hcmd m op k = hcmd m op j) := by
      intro he
      have hs := congrArg Command.sequence he
      simp only [hcmd] at hs
      omega
    rw [htr_succ, Object.traceCount_append, ih (by omega), hsingle_count]
    have hne2 : ¬ (hcmd m op j = hcmd m op k) := fun h => hne (Eq.symm h)
    simp [hne2]

/-- A command is present in the trace committed by its own round. -/
theorem htr_count_succ (k : Nat) :
    0 < (Tagged (n := m + 1) obj).traceCount (hcmd m op k) (htr m obj op (k + 1)) := by
  rw [htr_succ, Object.traceCount_append, htr_count_zero m obj op k k (Nat.le_refl k),
    hsingle_count]
  simp

/-! ### The per-process fields -/

noncomputable def hslots (k : Nat) : Fin (m + 1) → Seed (n := m + 1) obj :=
  fun q => if q = 0 then hseed m obj op k else zeroSeed obj

def hseq (k : Nat) : Fin (m + 1) → Nat := fun q => if q = 0 then k else 0

def hlocal (l : Local (n := m + 1) obj) : Fin (m + 1) → Local (n := m + 1) obj :=
  update (fun _ => Local.idle (zeroSeed obj)) 0 l

/-- The command the worker announced before cycle `k`. -/
def hprev : Nat → Option (Cmd (m + 1) Op)
  | 0 => none
  | k + 1 => some (hcmd m op k)

def hann (k : Nat) : Fin (m + 1) → Option (Cmd (m + 1) Op) :=
  fun q => if q = 0 then hprev m op k else none

/-- The commands gathered after `i` announcement reads. -/
def hcmds (k i : Nat) : List (Cmd (m + 1) Op) := if i = 0 then [] else [hcmd m op k]

/-- The best seed seen after `i` of the post-commit register reads. -/
noncomputable def hchkacc (k i : Nat) : Seed (n := m + 1) obj :=
  if i = 0 then zeroSeed obj else hseed m obj op (k + 1)

noncomputable def hcalls : Nat → List (Call (n := m + 1) obj)
  | 0 => []
  | k + 1 => (⟨k + 1, 0, htr m obj op (k + 1)⟩ : Call (n := m + 1) obj) :: hcalls k

noncomputable def hreturns : Nat → List (Return (n := m + 1) obj)
  | 0 => []
  | k + 1 =>
      (⟨hcmd m op k, k + 1, htr m obj op (k + 1)⟩ : Return (n := m + 1) obj) :: hreturns k

def hinvs : Nat → List (Cmd (m + 1) Op)
  | 0 => []
  | k + 1 => hcmd m op k :: hinvs k

omit [DecidableEq Op] in
theorem hlocal_zero (l : Local (n := m + 1) obj) : hlocal m obj l 0 = l := by
  simp [hlocal, update]

omit [DecidableEq Op] in
theorem hlocal_ne (l : Local (n := m + 1) obj) {q : Fin (m + 1)} (hq : q ≠ 0) :
    hlocal m obj l q = .idle (zeroSeed obj) := by
  simp [hlocal, update, hq]

omit [DecidableEq Op] in
theorem update_hlocal (l v : Local (n := m + 1) obj) :
    update (hlocal m obj l) 0 v = hlocal m obj v := by
  funext q
  by_cases h : q = 0 <;> simp [hlocal, update, h]

omit [DecidableEq Op] in
theorem hslots_zero (k : Nat) : hslots m obj op k 0 = hseed m obj op k := by simp [hslots]

omit [DecidableEq Op] in
theorem hslots_ne (k : Nat) {q : Fin (m + 1)} (hq : q ≠ 0) :
    hslots m obj op k q = zeroSeed obj := by simp [hslots, hq]

omit [DecidableEq Op] in
theorem update_hslots (k : Nat) :
    update (hslots m obj op k) 0 (hseed m obj op (k + 1)) = hslots m obj op (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [hslots, update, h]

omit [DecidableEq Op] in
theorem hseq_zero (k : Nat) : hseq m k 0 = k := by simp [hseq]

omit [DecidableEq Op] in
theorem update_hseq (k : Nat) : update (hseq m k) 0 (k + 1) = hseq m (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [hseq, update, h]

omit [DecidableEq Op] in
theorem hann_zero (k : Nat) : hann m op k 0 = hprev m op k := by simp [hann]

omit [DecidableEq Op] in
theorem hann_ne (k : Nat) {q : Fin (m + 1)} (hq : q ≠ 0) : hann m op k q = none := by
  simp [hann, hq]

omit [DecidableEq Op] in
theorem update_hann (k : Nat) :
    update (hann m op k) 0 (some (hcmd m op k)) = hann m op (k + 1) := by
  funext q
  by_cases h : q = 0 <;> simp [hann, update, h, hprev]

omit [DecidableEq Op] in
theorem hseed_trace (k : Nat) : (hseed m obj op k).trace = htr m obj op k := rfl

/-! ### The configurations of one cycle -/

noncomputable def hc0 (k : Nat) : Configuration (n := m + 1) obj where
  sequence := hseq m k
  localState := hlocal m obj (.idle (hseed m obj op k))
  slots := hslots m obj op k
  announcements := hann m op k
  calls := hcalls m obj op k
  returns := hreturns m obj op k
  invocations := hinvs m op k

noncomputable def hc1 (k : Nat) : Configuration (n := m + 1) obj :=
  { hc0 m obj op k with
    sequence := hseq m (k + 1)
    invocations := hinvs m op (k + 1)
    localState := hlocal m obj (.announcing (hcmd m op k) (hseed m obj op k)) }

/-- After the announcement and `i` register reads. -/
noncomputable def hcol (k i : Nat) : Configuration (n := m + 1) obj :=
  { hc1 m obj op k with
    announcements := hann m op (k + 1)
    localState := hlocal m obj
      (.collecting (hcmd m op k) ((List.finRange (m + 1)).drop i) (hseed m obj op k)) }

/-- After `i` announcement reads. -/
noncomputable def hgat (k i : Nat) : Configuration (n := m + 1) obj :=
  { hcol m obj op k (m + 1) with
    localState := hlocal m obj
      (.gathering (hcmd m op k) (hseed m obj op k) ((List.finRange (m + 1)).drop i)
        (hcmds m op k i)) }

noncomputable def hwait (k : Nat) : Configuration (n := m + 1) obj :=
  { hgat m obj op k (m + 1) with
    localState := hlocal m obj (.waiting (hcmd m op k) (k + 1) (htr m obj op (k + 1)))
    calls := hcalls m obj op (k + 1) }

noncomputable def hpub (k : Nat) : Configuration (n := m + 1) obj :=
  { hwait m obj op k with
    localState := hlocal m obj (.publishing (hcmd m op k) (hseed m obj op (k + 1))) }

/-- After the publication and `i` post-commit register reads. -/
noncomputable def hchk (k i : Nat) : Configuration (n := m + 1) obj :=
  { hpub m obj op k with
    slots := hslots m obj op (k + 1)
    localState := hlocal m obj
      (.checking (hcmd m op k) (hseed m obj op (k + 1)) ((List.finRange (m + 1)).drop i)
        (hchkacc m obj op k i)) }

omit [DecidableEq Op] in
theorem hc0_local (k : Nat) :
    (hc0 m obj op k).localState 0 = .idle (hseed m obj op k) := hlocal_zero ..
omit [DecidableEq Op] in
theorem hc1_local (k : Nat) :
    (hc1 m obj op k).localState 0 = .announcing (hcmd m op k) (hseed m obj op k) :=
  hlocal_zero ..
omit [DecidableEq Op] in
theorem hcol_local (k i : Nat) : (hcol m obj op k i).localState 0 =
    .collecting (hcmd m op k) ((List.finRange (m + 1)).drop i) (hseed m obj op k) :=
  hlocal_zero ..
omit [DecidableEq Op] in
theorem hgat_local (k i : Nat) : (hgat m obj op k i).localState 0 =
    .gathering (hcmd m op k) (hseed m obj op k) ((List.finRange (m + 1)).drop i)
      (hcmds m op k i) := hlocal_zero ..
omit [DecidableEq Op] in
theorem hwait_local (k : Nat) : (hwait m obj op k).localState 0 =
    .waiting (hcmd m op k) (k + 1) (htr m obj op (k + 1)) := hlocal_zero ..
omit [DecidableEq Op] in
theorem hpub_local (k : Nat) : (hpub m obj op k).localState 0 =
    .publishing (hcmd m op k) (hseed m obj op (k + 1)) := hlocal_zero ..
omit [DecidableEq Op] in
theorem hchk_local (k i : Nat) : (hchk m obj op k i).localState 0 =
    .checking (hcmd m op k) (hseed m obj op (k + 1)) ((List.finRange (m + 1)).drop i)
      (hchkacc m obj op k i) := hlocal_zero ..

omit [DecidableEq Op] in
theorem hc0_seq (k : Nat) : (hc0 m obj op k).sequence = hseq m k := rfl
omit [DecidableEq Op] in
theorem hc0_inv (k : Nat) : (hc0 m obj op k).invocations = hinvs m op k := rfl
omit [DecidableEq Op] in
theorem hc0_localState (k : Nat) :
    (hc0 m obj op k).localState = hlocal m obj (.idle (hseed m obj op k)) := rfl
omit [DecidableEq Op] in
theorem hc1_localState (k : Nat) :
    (hc1 m obj op k).localState = hlocal m obj (.announcing (hcmd m op k) (hseed m obj op k)) :=
  rfl
omit [DecidableEq Op] in
theorem hc1_ann (k : Nat) : (hc1 m obj op k).announcements = hann m op k := rfl
omit [DecidableEq Op] in
theorem hcol_localState (k i : Nat) : (hcol m obj op k i).localState =
    hlocal m obj (.collecting (hcmd m op k) ((List.finRange (m + 1)).drop i)
      (hseed m obj op k)) := rfl
omit [DecidableEq Op] in
theorem hcol_slots (k i : Nat) : (hcol m obj op k i).slots = hslots m obj op k := rfl
omit [DecidableEq Op] in
theorem hgat_localState (k i : Nat) : (hgat m obj op k i).localState =
    hlocal m obj (.gathering (hcmd m op k) (hseed m obj op k)
      ((List.finRange (m + 1)).drop i) (hcmds m op k i)) := rfl
omit [DecidableEq Op] in
theorem hgat_ann (k i : Nat) : (hgat m obj op k i).announcements = hann m op (k + 1) := rfl
omit [DecidableEq Op] in
theorem hwait_localState (k : Nat) : (hwait m obj op k).localState =
    hlocal m obj (.waiting (hcmd m op k) (k + 1) (htr m obj op (k + 1))) := rfl
omit [DecidableEq Op] in
theorem hpub_localState (k : Nat) : (hpub m obj op k).localState =
    hlocal m obj (.publishing (hcmd m op k) (hseed m obj op (k + 1))) := rfl
omit [DecidableEq Op] in
theorem hpub_slots (k : Nat) : (hpub m obj op k).slots = hslots m obj op k := rfl
omit [DecidableEq Op] in
theorem hchk_localState (k i : Nat) : (hchk m obj op k i).localState =
    hlocal m obj (.checking (hcmd m op k) (hseed m obj op (k + 1))
      ((List.finRange (m + 1)).drop i) (hchkacc m obj op k i)) := rfl
omit [DecidableEq Op] in
theorem hchk_slots (k i : Nat) : (hchk m obj op k i).slots = hslots m obj op (k + 1) := rfl

/-! ### The GCA family -/

noncomputable def hfam : Family (n := m + 1) obj where
  protocol := fun r =>
    { participants := if r = 0 then [] else [0]
      input := fun _ => htr m obj op r
      actor := fun _ => if r = 0 then none else some 0
      actor_valid := by
        intro t p h
        by_cases hr : r = 0
        · simp [hr] at h
        · simp [hr] at h ⊢
          exact h.symm
      acknowledged := fun _ => true }

omit [DecidableEq Op] in
theorem hfam_waitFree : (hfam m obj op).SnapshotWaitFree obj :=
  fun _ => GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)

theorem hfam_input (r : Nat) (hr : r ≠ 0) :
    ((hfam m obj op).environment obj r).input 0 = some (htr m obj op r) := by
  simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
    GCA.TimedExecution.views, GCA.SnapshotExecution.history, hfam, hr]

theorem hfam_input_none (r : Nat) {p : Fin (m + 1)} (hp : p ≠ 0) :
    ((hfam m obj op).environment obj r).input p = none := by
  by_cases hr : r = 0 <;>
    simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
      GCA.TimedExecution.views, GCA.SnapshotExecution.history, hfam, hr, hp]

theorem hfam_output (r : Nat) (hr : r ≠ 0) :
    ((hfam m obj op).environment obj r).output 0 = some (htr m obj op r, true) := by
  have hw : ((hfam m obj op).protocol r).SnapshotWaitFree :=
    GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)
  have hinf : ((hfam m obj op).protocol r).InfiniteSteps 0 :=
    fun N => ⟨N, Nat.le_refl _, by simp [hfam, hr]⟩
  obtain ⟨s, flag, ho⟩ := ((hfam m obj op).protocol r).returned_of_infiniteSteps hw hinf
  have huniform : ∀ u, (((hfam m obj op).environment obj r).Inputs u) → u = htr m obj op r := by
    intro u hu
    rw [Family.environment, GCA.Protocol.history, GCA.SnapshotExecution.inputs_iff] at hu
    obtain ⟨p, -, he⟩ := hu
    exact he.symm
  obtain ⟨rfl, rfl⟩ := (((hfam m obj op).environment obj r).uniform_return
    ((hfam m obj op).specification obj r) huniform ho)
  exact ho

/-! ### The accumulators -/

omit [DecidableEq Op] in
/-- The worker's own register already dominates; the bystanders' empty
registers never improve on it. -/
theorem hbest_start (k : Nat) (q : Fin (m + 1)) :
    best obj (hseed m obj op k) (hslots m obj op k q) = hseed m obj op k := by
  unfold WeakUniversal.best
  by_cases hq : q = 0
  · subst q
    rw [hslots_zero]
    simp
  · rw [hslots_ne m obj op k hq]
    have hno : ¬ ((hseed m obj op k).round < (zeroSeed (n := m + 1) obj).round) := by
      simp [hseed, zeroSeed]
    simp [hno]

/-- Only the worker has an announcement, and it is read first. -/
theorem hobserve_step (k i : Nat) (hlen : i < (List.finRange (m + 1)).length) :
    observe obj (hseed m obj op k) (hann m op (k + 1) ((List.finRange (m + 1))[i]'hlen))
      (hcmds m op k i) = hcmds m op k (i + 1) := by
  have hget : ((List.finRange (m + 1))[i]'hlen).val = i := by simp [List.getElem_finRange]
  by_cases h0 : i = 0
  · subst i
    have hq : ((List.finRange (m + 1))[0]'hlen) = 0 := by
      apply Fin.ext
      simp
    rw [hq, hann_zero]
    show (if (Tagged (n := m + 1) obj).traceCount (hcmd m op k) (hseed m obj op k).trace = 0
      then hcmds m op k 0 ++ [hcmd m op k] else hcmds m op k 0) = hcmds m op k 1
    rw [hseed_trace, htr_count_zero m obj op k k (Nat.le_refl k)]
    simp [hcmds]
  · have hq : ((List.finRange (m + 1))[i]'hlen) ≠ 0 := by
      intro he
      rw [he] at hget
      simp only [Fin.val_zero] at hget
      exact h0 hget.symm
    rw [hann_ne m op (k + 1) hq]
    show hcmds m op k i = hcmds m op k (i + 1)
    simp [hcmds, h0]

omit [DecidableEq Op] in
/-- The post-commit collect picks up the worker's freshly published seed. -/
theorem hbest_check (k i : Nat) (hlen : i < (List.finRange (m + 1)).length) :
    best obj (hchkacc m obj op k i)
        (hslots m obj op (k + 1) ((List.finRange (m + 1))[i]'hlen))
      = hchkacc m obj op k (i + 1) := by
  have hget : ((List.finRange (m + 1))[i]'hlen).val = i := by simp [List.getElem_finRange]
  by_cases h0 : i = 0
  · subst i
    have hq : ((List.finRange (m + 1))[0]'hlen) = 0 := by
      apply Fin.ext
      simp
    have h1 : hchkacc m obj op k 0 = zeroSeed obj := by simp [hchkacc]
    have h2 : hchkacc m obj op k 1 = hseed m obj op (k + 1) := by simp [hchkacc]
    rw [hq, hslots_zero, h1, h2]
    unfold WeakUniversal.best
    have hlt : (zeroSeed (n := m + 1) obj).round < (hseed m obj op (k + 1)).round := by
      simp [zeroSeed, hseed]
    simp [hlt]
  · have hq : ((List.finRange (m + 1))[i]'hlen) ≠ 0 := by
      intro he
      rw [he] at hget
      simp only [Fin.val_zero] at hget
      exact h0 hget.symm
    have h1 : hchkacc m obj op k i = hseed m obj op (k + 1) := by simp [hchkacc, h0]
    have h2 : hchkacc m obj op k (i + 1) = hseed m obj op (k + 1) := by simp [hchkacc]
    rw [hslots_ne m obj op (k + 1) hq, h1, h2]
    unfold WeakUniversal.best
    have hno : ¬ ((hseed m obj op (k + 1)).round < (zeroSeed (n := m + 1) obj).round) := by
      simp [hseed, zeroSeed]
    simp [hno]

/-! ### The steps of one cycle -/

omit [DecidableEq Op] in
theorem hdrop_full : (List.finRange (m + 1)).drop (m + 1) = [] := by
  have hd := List.drop_length (l := List.finRange (m + 1))
  rwa [List.length_finRange] at hd

section Steps
variable {H : WeakUniversal.Environment (n := m + 1) obj}

theorem hstep_invoke (k : Nat) : Step obj H (hc0 m obj op k) (hc1 m obj op k) := by
  have h := Step.invoke (H := H) (hc0 m obj op k) 0 op (hseed m obj op k) (hc0_local m obj op k)
  simp only [hc0_seq, hc0_inv, hc0_localState, hseq_zero, update_hseq, update_hlocal] at h
  exact h

theorem hstep_announce (k : Nat) : Step obj H (hc1 m obj op k) (hcol m obj op k 0) := by
  have h := Step.announce (H := H) (hc1 m obj op k) 0 (hcmd m op k) (hseed m obj op k)
    (hc1_local m obj op k) (List.finRange (m + 1)) (List.Perm.refl _)
  simp only [hc1_ann, hc1_localState, update_hann, update_hlocal] at h
  exact h

theorem hstep_readStart (k i : Nat) (hi : i < m + 1) :
    Step obj H (hcol m obj op k i) (hcol m obj op k (i + 1)) := by
  have hlen : i < (List.finRange (m + 1)).length := by rw [List.length_finRange]; exact hi
  have hloc : (hcol m obj op k i).localState 0 =
      .collecting (hcmd m op k) (((List.finRange (m + 1))[i]'hlen) ::
        (List.finRange (m + 1)).drop (i + 1)) (hseed m obj op k) := by
    rw [hcol_local, List.drop_eq_getElem_cons hlen]
  have h := Step.readStart (H := H) (hcol m obj op k i) 0 ((List.finRange (m + 1))[i]'hlen)
    (hcmd m op k) ((List.finRange (m + 1)).drop (i + 1)) (hseed m obj op k) hloc
  simp only [hcol_slots, hbest_start, hcol_localState, update_hlocal] at h
  exact h

theorem hstep_collectedStart (k : Nat) :
    Step obj H (hcol m obj op k (m + 1)) (hgat m obj op k 0) := by
  have hloc : (hcol m obj op k (m + 1)).localState 0 =
      .collecting (hcmd m op k) [] (hseed m obj op k) := by
    rw [hcol_local, hdrop_full]
  have h := Step.collectedStart (H := H) (hcol m obj op k (m + 1)) 0 (hcmd m op k)
    (hseed m obj op k) hloc (List.finRange (m + 1)) (List.Perm.refl _)
  simp only [hcol_localState, update_hlocal] at h
  exact h

theorem hstep_readAnnouncement (k i : Nat) (hi : i < m + 1) :
    Step obj H (hgat m obj op k i) (hgat m obj op k (i + 1)) := by
  have hlen : i < (List.finRange (m + 1)).length := by rw [List.length_finRange]; exact hi
  have hloc : (hgat m obj op k i).localState 0 =
      .gathering (hcmd m op k) (hseed m obj op k) (((List.finRange (m + 1))[i]'hlen) ::
        (List.finRange (m + 1)).drop (i + 1)) (hcmds m op k i) := by
    rw [hgat_local, List.drop_eq_getElem_cons hlen]
  have h := Step.readAnnouncement (H := H) (hgat m obj op k i) 0
    ((List.finRange (m + 1))[i]'hlen) (hcmd m op k) (hseed m obj op k)
    ((List.finRange (m + 1)).drop (i + 1)) (hcmds m op k i) hloc
  simp only [hgat_ann, hobserve_step, hgat_localState, update_hlocal] at h
  exact h

theorem hstep_propose (k : Nat) :
    Step obj ((hfam m obj op).environment obj) (hgat m obj op k (m + 1)) (hwait m obj op k) := by
  have hloc : (hgat m obj op k (m + 1)).localState 0 =
      .gathering (hcmd m op k) (hseed m obj op k) [] (hcmds m op k (m + 1)) := by
    rw [hgat_local, hdrop_full]
  have h := Step.propose (hgat m obj op k (m + 1)) 0 (hcmd m op k) (hseed m obj op k)
    (hcmds m op k (m + 1)) hloc (hcmds m op k (m + 1)) (List.Perm.refl _)
    (hfam_input m obj op (k + 1) (by omega))
  simp only [hgat_localState, update_hlocal] at h
  exact h

theorem hstep_receive (k : Nat) :
    Step obj ((hfam m obj op).environment obj) (hwait m obj op k) (hpub m obj op k) := by
  have h := Step.receive (hwait m obj op k) 0 (hcmd m op k) (k + 1) (htr m obj op (k + 1))
    (htr m obj op (k + 1)) true (hwait_local m obj op k)
    (hfam_output m obj op (k + 1) (by omega)) (List.finRange (m + 1)) (List.Perm.refl _)
  simp only [hwait_localState, update_hlocal] at h
  exact h

theorem hstep_publish (k : Nat) : Step obj H (hpub m obj op k) (hchk m obj op k 0) := by
  have h := Step.publish (H := H) (hpub m obj op k) 0 (hcmd m op k) (hseed m obj op (k + 1))
    (hpub_local m obj op k) (List.finRange (m + 1)) (List.Perm.refl _)
  simp only [hpub_slots, hpub_localState, update_hslots, update_hlocal] at h
  exact h

theorem hstep_readCheck (k i : Nat) (hi : i < m + 1) :
    Step obj H (hchk m obj op k i) (hchk m obj op k (i + 1)) := by
  have hlen : i < (List.finRange (m + 1)).length := by rw [List.length_finRange]; exact hi
  have hloc : (hchk m obj op k i).localState 0 =
      .checking (hcmd m op k) (hseed m obj op (k + 1)) (((List.finRange (m + 1))[i]'hlen) ::
        (List.finRange (m + 1)).drop (i + 1)) (hchkacc m obj op k i) := by
    rw [hchk_local, List.drop_eq_getElem_cons hlen]
  have h := Step.readCheck (H := H) (hchk m obj op k i) 0 ((List.finRange (m + 1))[i]'hlen)
    (hcmd m op k) (hseed m obj op (k + 1)) ((List.finRange (m + 1)).drop (i + 1))
    (hchkacc m obj op k i) hloc
  simp only [hchk_slots, hbest_check, hchk_localState, update_hlocal] at h
  exact h

theorem hstep_finish (k : Nat) :
    Step obj H (hchk m obj op k (m + 1)) (hc0 m obj op (k + 1)) := by
  have hacc : hchkacc m obj op k (m + 1) = hseed m obj op (k + 1) := by simp [hchkacc]
  have hloc : (hchk m obj op k (m + 1)).localState 0 =
      .checking (hcmd m op k) (hseed m obj op (k + 1)) [] (hseed m obj op (k + 1)) := by
    rw [hchk_local, hdrop_full, hacc]
  have hcontains : 0 < (Tagged (n := m + 1) obj).traceCount (hcmd m op k)
      (hseed m obj op (k + 1)).trace := by
    rw [hseed_trace]
    exact htr_count_succ m obj op k
  have h := Step.finish (H := H) (hchk m obj op k (m + 1)) 0 (hcmd m op k)
    (hseed m obj op (k + 1)) (hseed m obj op (k + 1)) hloc hcontains
  simp only [hchk_localState, update_hlocal] at h
  exact h

end Steps

/-! ### The infinite run: `3 * m + 16` steps per cycle -/

noncomputable def hcyc (k j : Nat) : Configuration (n := m + 1) obj :=
  if j = 0 then hc0 m obj op k
  else if j = 1 then hc1 m obj op k
  else if j ≤ m + 3 then hcol m obj op k (j - 2)
  else if j ≤ 2 * m + 5 then hgat m obj op k (j - (m + 4))
  else if j ≤ 2 * m + 12 then hwait m obj op k
  else if j = 2 * m + 13 then hpub m obj op k
  else hchk m obj op k (j - (2 * m + 14))

omit [DecidableEq Op] in
theorem hcyc_0 (k : Nat) : hcyc m obj op k 0 = hc0 m obj op k := by simp [hcyc]

omit [DecidableEq Op] in
theorem hcyc_1 (k : Nat) : hcyc m obj op k 1 = hc1 m obj op k := by simp [hcyc]

omit [DecidableEq Op] in
theorem hcyc_col (k j : Nat) (h2 : 2 ≤ j) (h3 : j ≤ m + 3) :
    hcyc m obj op k j = hcol m obj op k (j - 2) := by
  have e0 : ¬ (j = 0) := by omega
  have e1 : ¬ (j = 1) := by omega
  simp [hcyc, e0, e1, h3]

omit [DecidableEq Op] in
theorem hcyc_gat (k j : Nat) (h4 : m + 4 ≤ j) (h5 : j ≤ 2 * m + 5) :
    hcyc m obj op k j = hgat m obj op k (j - (m + 4)) := by
  have e0 : ¬ (j = 0) := by omega
  have e1 : ¬ (j = 1) := by omega
  have e3 : ¬ (j ≤ m + 3) := by omega
  simp [hcyc, e0, e1, e3, h5]

omit [DecidableEq Op] in
theorem hcyc_wait (k j : Nat) (h6 : 2 * m + 6 ≤ j) (h12 : j ≤ 2 * m + 12) :
    hcyc m obj op k j = hwait m obj op k := by
  have e0 : ¬ (j = 0) := by omega
  have e1 : ¬ (j = 1) := by omega
  have e3 : ¬ (j ≤ m + 3) := by omega
  have e5 : ¬ (j ≤ 2 * m + 5) := by omega
  simp [hcyc, e0, e1, e3, e5, h12]

omit [DecidableEq Op] in
theorem hcyc_pub (k : Nat) : hcyc m obj op k (2 * m + 13) = hpub m obj op k := by
  have e3 : ¬ (2 * m + 13 ≤ m + 3) := by omega
  have e5 : ¬ (2 * m + 13 ≤ 2 * m + 5) := by omega
  have e12 : ¬ (2 * m + 13 ≤ 2 * m + 12) := by omega
  simp [hcyc, e3, e5, e12]

omit [DecidableEq Op] in
theorem hcyc_chk (k j : Nat) (h14 : 2 * m + 14 ≤ j) (_h15 : j ≤ 3 * m + 15) :
    hcyc m obj op k j = hchk m obj op k (j - (2 * m + 14)) := by
  have e0 : ¬ (j = 0) := by omega
  have e1 : ¬ (j = 1) := by omega
  have e3 : ¬ (j ≤ m + 3) := by omega
  have e5 : ¬ (j ≤ 2 * m + 5) := by omega
  have e12 : ¬ (j ≤ 2 * m + 12) := by omega
  have e13 : ¬ (j = 2 * m + 13) := by omega
  simp [hcyc, e0, e1, e3, e5, e12, e13]

omit [DecidableEq Op] in
theorem hcyc_localState (k j : Nat) :
    ∃ l, (hcyc m obj op k j).localState = hlocal m obj l := by
  unfold hcyc
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
          · split
            · exact ⟨_, rfl⟩
            · exact ⟨_, rfl⟩

noncomputable def hstate (t : Nat) : Configuration (n := m + 1) obj :=
  hcyc m obj op (t / (3 * m + 16)) (t % (3 * m + 16))

omit [DecidableEq Op] in
theorem hstate_at (k j : Nat) (hj : j < 3 * m + 16) :
    hstate m obj op (j + (3 * m + 16) * k) = hcyc m obj op k j := by
  unfold hstate
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < 3 * m + 16), Nat.div_eq_of_lt hj,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj, Nat.zero_add]

omit [DecidableEq Op] in
theorem hstate_idle (t : Nat) {q : Fin (m + 1)} (hq : q ≠ 0) :
    (hstate m obj op t).localState q = .idle (zeroSeed obj) := by
  obtain ⟨l, hl⟩ := hcyc_localState m obj op (t / (3 * m + 16)) (t % (3 * m + 16))
  show (hcyc m obj op (t / (3 * m + 16)) (t % (3 * m + 16))).localState q = _
  rw [hl, hlocal_ne m obj l hq]

omit [DecidableEq Op] in
theorem hstutter_at (k j : Nat) (h6 : 2 * m + 6 ≤ j) (h11 : j ≤ 2 * m + 11) :
    hstate m obj op (j + (3 * m + 16) * k + 1) = hstate m obj op (j + (3 * m + 16) * k) := by
  rw [show j + (3 * m + 16) * k + 1 = (j + 1) + (3 * m + 16) * k from by omega,
    hstate_at m obj op k (j + 1) (by omega), hstate_at m obj op k j (by omega),
    hcyc_wait m obj op k (j + 1) (by omega) (by omega),
    hcyc_wait m obj op k j h6 (by omega)]

theorem hstep_at (k j : Nat) (hj : j < 3 * m + 16)
    (hm2 : ¬ (2 * m + 6 ≤ j ∧ j ≤ 2 * m + 11)) :
    Step obj ((hfam m obj op).environment obj)
      (hstate m obj op (j + (3 * m + 16) * k))
      (hstate m obj op (j + (3 * m + 16) * k + 1)) := by
  rw [show j + (3 * m + 16) * k + 1 = (j + 1) + (3 * m + 16) * k from by omega]
  -- one program step per segment of the cycle outside the protocol's waiting segment
  rcases (by omega : j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ m + 2) ∨ j = m + 3 ∨
      (m + 4 ≤ j ∧ j ≤ 2 * m + 4) ∨ j = 2 * m + 5 ∨ j = 2 * m + 12 ∨ j = 2 * m + 13 ∨
      (2 * m + 14 ≤ j ∧ j ≤ 3 * m + 14) ∨ j = 3 * m + 15) with
    rfl | rfl | ⟨ha, hb⟩ | rfl | ⟨ha, hb⟩ | rfl | rfl | rfl | ⟨ha, hb⟩ | rfl
  · rw [hstate_at m obj op k 0 (by omega), hstate_at m obj op k 1 (by omega), hcyc_0, hcyc_1]
    exact hstep_invoke m obj op k
  · rw [hstate_at m obj op k 1 (by omega), hstate_at m obj op k 2 (by omega), hcyc_1,
      hcyc_col m obj op k 2 (by omega) (by omega)]
    exact hstep_announce m obj op k
  · rw [hstate_at m obj op k j (by omega), hstate_at m obj op k (j + 1) (by omega),
      hcyc_col m obj op k j (by omega) (by omega),
      hcyc_col m obj op k (j + 1) (by omega) (by omega),
      show j + 1 - 2 = (j - 2) + 1 from by omega]
    exact hstep_readStart m obj op k (j - 2) (by omega)
  · rw [hstate_at m obj op k (m + 3) (by omega),
      hstate_at m obj op k (m + 4) (by omega),
      hcyc_col m obj op k (m + 3) (by omega) (by omega),
      hcyc_gat m obj op k (m + 4) (by omega) (by omega),
      show m + 3 - 2 = m + 1 from by omega, show m + 4 - (m + 4) = 0 from by omega]
    exact hstep_collectedStart m obj op k
  · rw [hstate_at m obj op k j (by omega), hstate_at m obj op k (j + 1) (by omega),
      hcyc_gat m obj op k j (by omega) (by omega),
      hcyc_gat m obj op k (j + 1) (by omega) (by omega),
      show j + 1 - (m + 4) = (j - (m + 4)) + 1 from by omega]
    exact hstep_readAnnouncement m obj op k (j - (m + 4)) (by omega)
  · rw [hstate_at m obj op k (2 * m + 5) (by omega),
      hstate_at m obj op k (2 * m + 6) (by omega),
      hcyc_gat m obj op k (2 * m + 5) (by omega) (by omega),
      hcyc_wait m obj op k (2 * m + 6) (by omega) (by omega),
      show 2 * m + 5 - (m + 4) = m + 1 from by omega]
    exact hstep_propose m obj op k
  · rw [hstate_at m obj op k (2 * m + 12) (by omega),
      hstate_at m obj op k (2 * m + 13) (by omega),
      hcyc_wait m obj op k (2 * m + 12) (by omega) (by omega), hcyc_pub]
    exact hstep_receive m obj op k
  · rw [hstate_at m obj op k (2 * m + 13) (by omega),
      hstate_at m obj op k (2 * m + 14) (by omega), hcyc_pub,
      hcyc_chk m obj op k (2 * m + 14) (by omega) (by omega),
      show 2 * m + 14 - (2 * m + 14) = 0 from by omega]
    exact hstep_publish m obj op k
  · rw [hstate_at m obj op k j (by omega),
      hstate_at m obj op k (j + 1) (by omega),
      hcyc_chk m obj op k j ha (by omega),
      hcyc_chk m obj op k (j + 1) (by omega) (by omega),
      show j + 1 - (2 * m + 14) = (j - (2 * m + 14)) + 1 from by omega]
    exact hstep_readCheck m obj op k (j - (2 * m + 14)) (by omega)
  · rw [show 3 * m + 15 + 1 + (3 * m + 16) * k = 0 + (3 * m + 16) * (k + 1) from by
        rw [Nat.mul_succ]; omega,
      hstate_at m obj op k (3 * m + 15) (by omega),
      hstate_at m obj op (k + 1) 0 (by omega),
      hcyc_chk m obj op k (3 * m + 15) (by omega) (by omega), hcyc_0,
      show 3 * m + 15 - (2 * m + 14) = m + 1 from by omega]
    exact hstep_finish m obj op k

theorem hnext (t : Nat) :
    hstate m obj op (t + 1) = hstate m obj op t ∨
    Step obj ((hfam m obj op).environment obj)
      (hstate m obj op t) (hstate m obj op (t + 1)) := by
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 * m + 16 ∧ t = j + (3 * m + 16) * k :=
    ⟨t / (3 * m + 16), t % (3 * m + 16), Nat.mod_lt _ (by omega),
      (Nat.mod_add_div t (3 * m + 16)).symm⟩
  by_cases hm2 : 2 * m + 6 ≤ j ∧ j ≤ 2 * m + 11
  · exact Or.inl (hstutter_at m obj op k j hm2.1 hm2.2)
  · exact Or.inr (hstep_at m obj op k j hj hm2)

omit [DecidableEq Op] in
theorem hc0_zero_eq_initial : hc0 m obj op 0 = initial obj := by
  have hseqz : hseq m 0 = (fun _ => 0 : Fin (m + 1) → Nat) := by
    funext q; simp [hseq]
  have hlocz : hlocal m obj (.idle (hseed m obj op 0))
      = (fun _ => (Local.idle (zeroSeed obj) : Local (n := m + 1) obj)) := by
    funext q
    by_cases h : q = 0
    · simp [hlocal, update, h]; rfl
    · simp [hlocal, update, h]
  have hslz : hslots m obj op 0 = (fun _ => zeroSeed (n := m + 1) obj) := by
    funext q
    by_cases h : q = 0
    · simp [hslots, h]; rfl
    · simp [hslots, h]
  have hannz : hann m op 0 = (fun _ => (none : Option (Cmd (m + 1) Op))) := by
    funext q
    by_cases h : q = 0 <;> simp [hann, h, hprev]
  show (⟨hseq m 0, hlocal m obj (.idle (hseed m obj op 0)), hslots m obj op 0,
      hann m op 0, [], [], []⟩ : Configuration (n := m + 1) obj) = _
  rw [hseqz, hlocz, hslz, hannz]
  rfl

noncomputable def hrun : HelpingUniversal.Execution obj ((hfam m obj op).environment obj) where
  state := hstate m obj op
  initial_state := by
    show hcyc m obj op (0 / (3 * m + 16)) (0 % (3 * m + 16)) = initial obj
    rw [Nat.zero_div, Nat.zero_mod, hcyc_0]
    exact hc0_zero_eq_initial m obj op
  next := hnext m obj op

theorem hrun_state (t : Nat) : (hrun m obj op).state t = hstate m obj op t := rfl

theorem hrun_state_fun : (hrun m obj op).state = hstate m obj op := rfl

/-! ### The round-`k+1` clock reaches the last stage at offset `2m+12` -/

/-- The worker is scheduled at every instant; the bystanders never step. -/
def hactor : Nat → Option (Fin (m + 1)) := fun _ => some 0

omit [DecidableEq Op] in
theorem hround_mid (k j : Nat) (h6 : 2 * m + 6 ≤ j) (h12 : j ≤ 2 * m + 12) :
    helpingRound obj ((hstate m obj op (j + (3 * m + 16) * k)).localState 0) =
      some (k + 1) := by
  rw [hstate_at m obj op k j (by omega), hcyc_wait m obj op k j h6 h12, hwait_local]
  rfl

omit [DecidableEq Op] in
theorem hround_none (k j : Nat) (hj : j < 3 * m + 16)
    (h : ¬ (2 * m + 6 ≤ j ∧ j ≤ 2 * m + 12)) :
    helpingRound obj ((hstate m obj op (j + (3 * m + 16) * k)).localState 0) = none := by
  rw [hstate_at m obj op k j hj]
  -- the segments of the cycle other than the waiting one
  rcases (by omega : j = 0 ∨ j = 1 ∨ (2 ≤ j ∧ j ≤ m + 3) ∨ (m + 4 ≤ j ∧ j ≤ 2 * m + 5) ∨
      j = 2 * m + 13 ∨ 2 * m + 14 ≤ j) with rfl | rfl | ⟨h2, h3⟩ | ⟨h4, h5⟩ | rfl | h14
  · rw [hcyc_0, hc0_local]; rfl
  · rw [hcyc_1, hc1_local]; rfl
  · rw [hcyc_col m obj op k j h2 h3, hcol_local]; rfl
  · rw [hcyc_gat m obj op k j h4 h5, hgat_local]; rfl
  · rw [hcyc_pub, hpub_local]; rfl
  · rw [hcyc_chk m obj op k j h14 (by omega), hchk_local]; rfl

omit [DecidableEq Op] in
theorem hevent_mid (k j : Nat) (h6 : 2 * m + 6 ≤ j) (h12 : j ≤ 2 * m + 12) :
    gcaEventH obj (hstate m obj op) (hactor m) (j + (3 * m + 16) * k) = some (k + 1, 0) :=
  gcaEventH_spec obj rfl (hround_mid m obj op k j h6 h12)

omit [DecidableEq Op] in
theorem hevent_none (k j : Nat) (hj : j < 3 * m + 16)
    (h : ¬ (2 * m + 6 ≤ j ∧ j ≤ 2 * m + 12)) :
    gcaEventH obj (hstate m obj op) (hactor m) (j + (3 * m + 16) * k) = none := by
  simp [gcaEventH, hactor, hround_none m obj op k j hj h]

omit [DecidableEq Op] in
private theorem clockH_succ_ne {st : Nat → Configuration (n := m + 1) obj}
    {act : Nat → Option (Fin (m + 1))} {t r : Nat}
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
private theorem clockH_succ_eq {st : Nat → Configuration (n := m + 1) obj}
    {act : Nat → Option (Fin (m + 1))} {t r : Nat} {p : Fin (m + 1)}
    (h : gcaEventH obj st act t = some (r, p)) :
    gcaClockH obj st act (t + 1) r = gcaClockH obj st act t r + 1 := by
  rw [gcaClockH, h]
  simp

omit [DecidableEq Op] in
theorem hevent_ne (k : Nat) : ∀ t, t < (2 * m + 6) + (3 * m + 16) * k →
    ∀ p, gcaEventH obj (hstate m obj op) (hactor m) t ≠ some (k + 1, p) := by
  intro t ht p hp
  obtain ⟨k', j, hj, rfl⟩ : ∃ k' j, j < 3 * m + 16 ∧ t = j + (3 * m + 16) * k' :=
    ⟨t / (3 * m + 16), t % (3 * m + 16), Nat.mod_lt _ (by omega),
      (Nat.mod_add_div t (3 * m + 16)).symm⟩
  by_cases hmid : 2 * m + 6 ≤ j ∧ j ≤ 2 * m + 12
  · rw [hevent_mid m obj op k' j hmid.1 hmid.2] at hp
    have hk : k' + 1 = k + 1 := congrArg Prod.fst (Option.some.inj hp)
    have hk' : k' = k := by omega
    subst k'
    omega
  · rw [hevent_none m obj op k' j hj hmid] at hp
    simp at hp

omit [DecidableEq Op] in
theorem hclock_zero (k : Nat) : ∀ t, t ≤ (2 * m + 6) + (3 * m + 16) * k →
    gcaClockH obj (hstate m obj op) (hactor m) t (k + 1) = 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [clockH_succ_ne m obj (hevent_ne m obj op k t (by omega))]
    exact ih (by omega)

omit [DecidableEq Op] in
theorem hclock_mid (k : Nat) : ∀ i, i ≤ 7 →
    gcaClockH obj (hstate m obj op) (hactor m)
      ((2 * m + 6 + i) + (3 * m + 16) * k) (k + 1) = i := by
  intro i
  induction i with
  | zero => intro _; exact hclock_zero m obj op k _ (by omega)
  | succ i ih =>
    intro hi
    rw [show (2 * m + 6 + (i + 1)) + (3 * m + 16) * k
        = ((2 * m + 6 + i) + (3 * m + 16) * k) + 1 from by omega,
      clockH_succ_eq m obj (hevent_mid m obj op k (2 * m + 6 + i) (by omega) (by omega)),
      ih (by omega)]

omit [DecidableEq Op] in
theorem hclock_twelve (k : Nat) :
    gcaClockH obj (hstate m obj op) (hactor m) ((2 * m + 12) + (3 * m + 16) * k) (k + 1) = 6 := by
  rw [show (2 * m + 12) + (3 * m + 16) * k = (2 * m + 6 + 6) + (3 * m + 16) * k from by omega]
  exact hclock_mid m obj op k 6 (by omega)

/-! ### The protocol advances one stage per event -/

omit [DecidableEq Op] in
theorem hprotocol_actor (r : Nat) (hr : r ≠ 0) (t : Nat) :
    ((hfam m obj op).protocol r).actor t = some 0 := by simp [hfam, hr]

omit [DecidableEq Op] in
theorem hprotocol_ack (r t : Nat) : ((hfam m obj op).protocol r).acknowledged t = true := rfl

omit [DecidableEq Op] in
theorem hprotocol_phase_succ (r : Nat) (hr : r ≠ 0) (t : Nat) :
    ((hfam m obj op).protocol r).phase (t + 1) 0 =
      GCA.Protocol.advance (((hfam m obj op).protocol r).phase t 0) true := by
  rw [GCA.Protocol.phase, hprotocol_actor m obj op r hr, ite_eq_left rfl, hprotocol_ack]

omit [DecidableEq Op] in
theorem hprotocol_phase (r : Nat) (hr : r ≠ 0) : ∀ c, c ≤ 6 →
    ((hfam m obj op).protocol r).phase c 0 = c := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
    intro hc
    rw [hprotocol_phase_succ m obj op r hr c, ih (by omega)]
    show GCA.Protocol.advance c true = c + 1
    unfold GCA.Protocol.advance
    rw [ite_eq_left ⟨by omega, Or.inr (Or.inr rfl)⟩]

/-! ### The schedule -/

/-- **An infinite run of Algorithm 3 over `m + 1` processes that completes one
operation per cycle.**  Only process `0` is ever scheduled; the bystanders stay
idle and never announce, so the worker gathers exactly its own command. -/
noncomputable def hsched : Helping obj (hfam m obj op) where
  run := hrun m obj op
  actor := hactor m
  step_actor := by
    intro t
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 * m + 16 ∧ t = j + (3 * m + 16) * k :=
      ⟨t / (3 * m + 16), t % (3 * m + 16), Nat.mod_lt _ (by omega),
        (Nat.mod_add_div t (3 * m + 16)).symm⟩
    by_cases hm2 : 2 * m + 6 ≤ j ∧ j ≤ 2 * m + 11
    · refine Or.inr (Or.inr ⟨0, k + 1, rfl, ?_, ?_⟩)
      · rw [hrun_state]
        exact hround_mid m obj op k j hm2.1 (by omega)
      · show hstate m obj op (j + (3 * m + 16) * k + 1) = hstate m obj op (j + (3 * m + 16) * k)
        exact hstutter_at m obj op k j hm2.1 hm2.2
    · refine Or.inr (Or.inl ⟨0, rfl, ?_, ?_⟩)
      · show Step obj ((hfam m obj op).environment obj)
          (hstate m obj op (j + (3 * m + 16) * k))
          (hstate m obj op (j + (3 * m + 16) * k + 1))
        exact hstep_at m obj op k j hj hm2
      · intro q hq
        show (hstate m obj op (j + (3 * m + 16) * k + 1)).localState q =
          (hstate m obj op (j + (3 * m + 16) * k)).localState q
        rw [hstate_idle m obj op _ hq, hstate_idle m obj op _ hq]
  gca_actor := by
    intro t p r hact hr
    have hp : p = 0 := (Option.some.inj hact).symm
    subst p
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 * m + 16 ∧ t = j + (3 * m + 16) * k :=
      ⟨t / (3 * m + 16), t % (3 * m + 16), Nat.mod_lt _ (by omega),
        (Nat.mod_add_div t (3 * m + 16)).symm⟩
    rw [hrun_state] at hr
    by_cases hmid : 2 * m + 6 ≤ j ∧ j ≤ 2 * m + 12
    · rw [hround_mid m obj op k j hmid.1 hmid.2] at hr
      have hrk : r = k + 1 := (Option.some.inj hr).symm
      subst r
      exact hprotocol_actor m obj op (k + 1) (by omega) _
    · rw [hround_none m obj op k j hj hmid] at hr
      simp at hr
  no_ghost := by
    intro r p s hi
    by_cases hp : p = 0
    · subst p
      refine ⟨(2 * m + 6) + (3 * m + 16) * r, htr m obj op (r + 1), ?_⟩
      show (⟨r + 1, 0, htr m obj op (r + 1)⟩ : Call (n := m + 1) obj) ∈
        (hstate m obj op ((2 * m + 6) + (3 * m + 16) * r)).calls
      rw [hstate_at m obj op r (2 * m + 6) (by omega),
        hcyc_wait m obj op r (2 * m + 6) (by omega) (by omega)]
      show _ ∈ hcalls m obj op (r + 1)
      exact List.mem_cons_self ..
    · rw [hfam_input_none m obj op (r + 1) hp] at hi
      exact absurd hi (by simp)
  receive_ready := by
    intro t p r hr hchange
    by_cases hp : p = 0
    · subst p
      obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 * m + 16 ∧ t = j + (3 * m + 16) * k :=
        ⟨t / (3 * m + 16), t % (3 * m + 16), Nat.mod_lt _ (by omega),
          (Nat.mod_add_div t (3 * m + 16)).symm⟩
      rw [hrun_state] at hr
      by_cases hmid : 2 * m + 6 ≤ j ∧ j ≤ 2 * m + 12
      · rw [hround_mid m obj op k j hmid.1 hmid.2] at hr
        have hrk : r = k + 1 := (Option.some.inj hr).symm
        subst r
        have hj12 : j = 2 * m + 12 := by
          apply Classical.byContradiction
          intro hne
          exact hchange (by
            show ((hrun m obj op).state (j + (3 * m + 16) * k + 1)).localState 0 =
              ((hrun m obj op).state (j + (3 * m + 16) * k)).localState 0
            rw [hrun_state, hrun_state, hstutter_at m obj op k j hmid.1 (by omega)])
        subst j
        show ((hfam m obj op).protocol (k + 1)).phase
          (gcaClockH obj (hrun m obj op).state (hactor m)
            ((2 * m + 12) + (3 * m + 16) * k) (k + 1)) 0 = 6
        rw [hrun_state_fun, hclock_twelve m obj op k]
        exact hprotocol_phase m obj op (k + 1) (by omega) 6 (by omega)
      · rw [hround_none m obj op k j hj hmid] at hr
        simp at hr
    · rw [hrun_state, hstate_idle m obj op t hp] at hr
      simp [helpingRound] at hr

theorem hsched_state_fun : (hsched m obj op).run.state = hstate m obj op := rfl

theorem hsched_actor_fun : (hsched m obj op).actor = hactor m := rfl

/-! ### Fairness, operation liveness and solo scheduling -/

/-- **Fairness.**  The schedule takes the `receive` step exactly when the
projected protocol clock shows the last stage, at offset `2m+12`. -/
theorem hsched_fair : (hsched m obj op).Fair := by
  intro t p cmd r proposal hact hl hphase _
  have hp : p = 0 := (Option.some.inj hact).symm
  subst p
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 * m + 16 ∧ t = j + (3 * m + 16) * k :=
    ⟨t / (3 * m + 16), t % (3 * m + 16), Nat.mod_lt _ (by omega),
      (Nat.mod_add_div t (3 * m + 16)).symm⟩
  rw [hsched_state_fun] at hl
  have hround : helpingRound obj
      ((hstate m obj op (j + (3 * m + 16) * k)).localState 0) = some r := by
    rw [hl]; rfl
  by_cases hmid : 2 * m + 6 ≤ j ∧ j ≤ 2 * m + 12
  · have hrk : r = k + 1 := by
      rw [hround_mid m obj op k j hmid.1 hmid.2] at hround
      exact (Option.some.inj hround).symm
    subst r
    rw [hsched_state_fun, hsched_actor_fun] at hphase
    have hj12 : j = 2 * m + 12 := by
      apply Classical.byContradiction
      intro hne
      rw [show j + (3 * m + 16) * k
            = (2 * m + 6 + (j - (2 * m + 6))) + (3 * m + 16) * k from by omega,
        hclock_mid m obj op k (j - (2 * m + 6)) (by omega),
        hprotocol_phase m obj op (k + 1) (by omega) (j - (2 * m + 6)) (by omega)] at hphase
      omega
    subst j
    refine ⟨?_, ?_⟩
    · show Step obj ((hfam m obj op).environment obj)
        (hstate m obj op ((2 * m + 12) + (3 * m + 16) * k))
        (hstate m obj op ((2 * m + 12) + (3 * m + 16) * k + 1))
      exact hstep_at m obj op k (2 * m + 12) (by omega) (by omega)
    · intro q hq
      show (hstate m obj op ((2 * m + 12) + (3 * m + 16) * k + 1)).localState q =
        (hstate m obj op ((2 * m + 12) + (3 * m + 16) * k)).localState q
      rw [hstate_idle m obj op _ hq, hstate_idle m obj op _ hq]
  · rw [hround_none m obj op k j hj hmid] at hround
    simp at hround

/-- **Operation liveness.** -/
theorem hsched_opLive : (hsched m obj op).OpLive := by
  intro N
  refine ⟨(3 * m + 16) * (N + 1), ?_, ?_⟩
  · have h1 : (3 * m + 16) * (N + 1) = (3 * m) * (N + 1) + 16 * (N + 1) := by rw [Nat.add_mul]
    omega
  · have h : (hsched m obj op).opActor ((3 * m + 16) * (N + 1)) = some (hcmd m op (N + 1)) := by
      show (HelpingUniversal.ledger obj
        (hstate m obj op ((3 * m + 16) * (N + 1) + 1))).active 0 = some (hcmd m op (N + 1))
      rw [show (3 * m + 16) * (N + 1) + 1 = 1 + (3 * m + 16) * (N + 1) from by omega,
        hstate_at m obj op (N + 1) 1 (by omega), hcyc_1]
      show HelpingUniversal.Local.command obj ((hc1 m obj op (N + 1)).localState 0) =
        some (hcmd m op (N + 1))
      rw [hc1_local]
      rfl
    rw [h]
    rfl

/-- The worker is scheduled at every instant, hence solo from time 0. -/
theorem hsched_soloFrom : (hsched m obj op).SoloFrom 0 0 :=
  FiniteScheduling.SoloFrom.of_continuous _ (fun _ _ => rfl)

/-- **Algorithm 3's progress hypotheses are jointly satisfiable, and with
content.**  `HelpingGCA.solo_completes` applied to this schedule really produces
a completed operation of the solo process. -/
theorem hsched_completes :
    ∃ u v cmd seed seen, u < v ∧ cmd.process = 0 ∧
      ((hsched m obj op).run.state u).localState 0 = .checking cmd seed [] seen ∧
      (⟨cmd, seen.round, seen.trace⟩ : Return (n := m + 1) obj) ∈
        ((hsched m obj op).run.state v).returns := by
  obtain ⟨u, v, cmd, seed, seen, -, huv, hproc, hL, hmem⟩ :=
    ((hsched m obj op).toGCA (hsched_fair m obj op) (hfam_waitFree m obj op)).solo_completes
      (hsched_soloFrom m obj op)
  exact ⟨u, v, cmd, seed, seen, huv, hproc, hL, hmem⟩

end ConflictFreedom.GlobalSchedule.WitnessH
