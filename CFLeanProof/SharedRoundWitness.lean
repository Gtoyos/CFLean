import CFLeanProof.ContentionWitness

/-! # A run of Algorithm 3 in which two processes share a GCA round

`WitnessC.wsched` has two operations in flight, but each GCA round
still has a single *participant*: process `1` stalls before proposing, so
process `0` proposes alone and the round's Commitment and Adoption properties
are never played off against another caller.

This module removes that restriction.  Two processes run Algorithm 3 in perfect
lockstep for ever.  In cycle `k` both announce, then both collect the *same*
announcement array, so `observe` builds the *same* command list for both and
they propose the *identical* trace to round `k + 1`.  Both are participants of
that round, both take their six protocol events on the shared projected clock,
and — inputs being equal — GCA Weak Agreement forces both to commit and Common
Prefix and Validity force the committed trace to be exactly the proposal.  Both
then publish, both find their own command in the committed trace, and both
respond.

The cycle is `38` steps and there is no prologue: the run starts in the initial
configuration.  Two operations are in flight at every proposal, and round
`k + 1` returns a commit to *both* callers.
-/
namespace ConflictFreedom.GlobalSchedule.WitnessS
open HelpingUniversal
open UniversalProtocol
open WeakUniversal (Cmd Tagged Seed Call Return update zeroSeed best)

variable {State Op Response : Type} (obj : Object State Op Response)
variable [DecidableEq Op] (op : Op)

/-! ### Commands -/

/-- Process `q`'s `(k+1)`-st command. -/
def scmd (q : Fin 2) (k : Nat) : Cmd 2 Op := ⟨op, q, k + 1⟩

omit [DecidableEq Op] in
theorem scmd_eq_iff (q q' : Fin 2) (j k : Nat) :
    scmd op q j = scmd op q' k ↔ q = q' ∧ j = k := by
  constructor
  · intro h
    refine ⟨congrArg Command.process h, ?_⟩
    have := congrArg Command.sequence h
    simp only [scmd] at this
    omega
  · rintro ⟨rfl, rfl⟩; rfl

omit [DecidableEq Op] in
theorem scmd_zero_ne_one (j k : Nat) : scmd op 0 j ≠ scmd op 1 k := by
  rw [Ne, scmd_eq_iff]
  intro h
  exact absurd h.1 (by decide)

/-! ### Traces and seeds -/

/-- The commands committed by round `k`: both processes' first `k` commands. -/
def slist : Nat → List (Cmd 2 Op)
  | 0 => []
  | (k + 1) => slist k ++ [scmd op 0 k, scmd op 1 k]

noncomputable def str (k : Nat) : (Tagged (n := 2) obj).Trace :=
  Quotient.mk _ (slist op k)

theorem count_scmd (q : Fin 2) (j : Nat) : ∀ k, List.count (scmd op q j) (slist op k)
    = if j < k then 1 else 0
  | 0 => by simp [slist]
  | (k + 1) => by
      have ih := count_scmd q j k
      have hsplit : List.count (scmd op q j) [scmd op 0 k, scmd op 1 k]
          = if j = k then 1 else 0 := by
        rcases Nat.decEq j k with hjk | hjk
        · have h0 : scmd op q j ≠ scmd op 0 k := by
            rw [Ne, scmd_eq_iff]; rintro ⟨-, rfl⟩; exact hjk rfl
          have h1 : scmd op q j ≠ scmd op 1 k := by
            rw [Ne, scmd_eq_iff]; rintro ⟨-, rfl⟩; exact hjk rfl
          simp [Ne.symm h0, Ne.symm h1, hjk]
        · subst hjk
          rcases WitnessC.fin2 q with rfl | rfl
          · have h1 : scmd op 0 j ≠ scmd op 1 j := scmd_zero_ne_one op j j
            simp [Ne.symm h1]
          · have h0 : scmd op 1 j ≠ scmd op 0 j := (scmd_zero_ne_one op j j).symm
            simp [Ne.symm h0]
      rw [slist, List.count_append, ih, hsplit]
      by_cases hlt : j < k
      · have h1 : j < k + 1 := by omega
        have h2 : ¬ (j = k) := by omega
        simp [hlt, h1, h2]
      · by_cases he : j = k
        · subst he
          have h1 : j < j + 1 := by omega
          simp [hlt, h1]
        · have h2 : ¬ (j < k + 1) := by omega
          simp [hlt, he, h2]

theorem traceCount_str (q : Fin 2) (j k : Nat) :
    (Tagged (n := 2) obj).traceCount (scmd op q j) (str obj op k)
      = if j < k then 1 else 0 := count_scmd op q j k

/-- The seed committed by round `k`. -/
noncomputable def ssd (k : Nat) : Seed (n := 2) obj := ⟨k, str obj op k⟩

/-! ### State components -/

noncomputable def sloc (l0 l1 : Local (n := 2) obj) : Fin 2 → Local (n := 2) obj :=
  fun q => if q = 0 then l0 else l1

/-- Both sequence counters, before and after process `0`'s invocation. -/
def sseqA (k : Nat) : Fin 2 → Nat := fun _ => k
def sseqB (k : Nat) : Fin 2 → Nat := fun q => if q = 0 then k + 1 else k

/-- Both registers hold the seed of round `k`; between the two publications of
a cycle process `0`'s register is one round ahead. -/
noncomputable def sslA (k : Nat) : Fin 2 → Seed (n := 2) obj := fun _ => ssd obj op k
noncomputable def sslB (k : Nat) : Fin 2 → Seed (n := 2) obj :=
  fun q => if q = 0 then ssd obj op (k + 1) else ssd obj op k

/-- The announcement array before cycle `k`, and after process `0`'s announce. -/
def sann (k : Nat) : Fin 2 → Option (Cmd 2 Op) :=
  fun q => if k = 0 then none else some ⟨op, q, k⟩
def sannM (k : Nat) : Fin 2 → Option (Cmd 2 Op) :=
  fun q => if q = 0 then some (scmd op 0 k) else sann op k 1

def sinv : Nat → List (Cmd 2 Op)
  | 0 => []
  | (k + 1) => scmd op 1 k :: scmd op 0 k :: sinv k

noncomputable def scalls : Nat → List (Call (n := 2) obj)
  | 0 => []
  | (k + 1) => ⟨k + 1, 1, str obj op (k + 1)⟩ :: ⟨k + 1, 0, str obj op (k + 1)⟩ :: scalls k

noncomputable def srets : Nat → List (Return (n := 2) obj)
  | 0 => []
  | (k + 1) => ⟨scmd op 1 k, k + 1, str obj op (k + 1)⟩ ::
      ⟨scmd op 0 k, k + 1, str obj op (k + 1)⟩ :: srets k

/-- Both processes gather the same two commands. -/
def scmds (k : Nat) : List (Cmd 2 Op) := [scmd op 0 k, scmd op 1 k]

/-! ### Component identities -/

omit [DecidableEq Op] in
theorem sloc_zero (l0 l1 : Local (n := 2) obj) : sloc obj l0 l1 0 = l0 := by simp [sloc]

omit [DecidableEq Op] in
theorem sloc_one (l0 l1 : Local (n := 2) obj) : sloc obj l0 l1 1 = l1 := by simp [sloc]

omit [DecidableEq Op] in
theorem update_sloc0 (l0 l1 v : Local (n := 2) obj) :
    update (sloc obj l0 l1) 0 v = sloc obj v l1 := by
  funext q; by_cases h : q = 0 <;> simp [update, sloc, h]

omit [DecidableEq Op] in
theorem fin2_eq_one {q : Fin 2} (h : q ≠ 0) : q = 1 := (WitnessC.fin2 q).resolve_left h

omit [DecidableEq Op] in
theorem fin2_eq_zero {q : Fin 2} (h : q ≠ 1) : q = 0 := (WitnessC.fin2 q).resolve_right h

omit [DecidableEq Op] in
theorem update_sloc1 (l0 l1 v : Local (n := 2) obj) :
    update (sloc obj l0 l1) 1 v = sloc obj l0 v := by
  funext q
  by_cases h : q = 1
  · subst h; simp [update, sloc]
  · have h0 := fin2_eq_zero h
    subst h0; simp [update, sloc]

omit [DecidableEq Op] in
theorem sseqA_zero (k : Nat) : sseqA k 0 = k := rfl

omit [DecidableEq Op] in
theorem sseqB_one (k : Nat) : sseqB k 1 = k := by simp [sseqB]

omit [DecidableEq Op] in
theorem update_sseqA (k : Nat) : update (sseqA k) 0 (k + 1) = sseqB k := by
  funext q; by_cases h : q = 0 <;> simp [update, sseqA, sseqB, h]

omit [DecidableEq Op] in
theorem update_sseqB (k : Nat) : update (sseqB k) 1 (k + 1) = sseqA (k + 1) := by
  funext q
  by_cases h : q = 1
  · subst h; simp [update, sseqA]
  · have h0 := fin2_eq_zero h
    subst h0; simp [update, sseqA, sseqB]

omit [DecidableEq Op] in
theorem update_sannA (k : Nat) :
    update (sann op k) 0 (some (scmd op 0 k)) = sannM op k := by
  funext q
  by_cases h : q = 0
  · subst h; simp [update, sannM]
  · have h1 := fin2_eq_one h
    subst h1; simp [update, sannM, sann]

omit [DecidableEq Op] in
theorem update_sannB (k : Nat) :
    update (sannM op k) 1 (some (scmd op 1 k)) = sann op (k + 1) := by
  funext q
  by_cases h : q = 1
  · subst h; simp [update, sann, scmd]
  · have h0 := fin2_eq_zero h
    subst h0; simp [update, sannM, sann, scmd]

omit [DecidableEq Op] in
theorem sann_succ (k : Nat) (q : Fin 2) : sann op (k + 1) q = some (scmd op q k) := by
  simp [sann, scmd]

omit [DecidableEq Op] in
theorem update_sslA (k : Nat) :
    update (sslA obj op k) 0 (ssd obj op (k + 1)) = sslB obj op k := by
  funext q; by_cases h : q = 0 <;> simp [update, sslA, sslB, h]

omit [DecidableEq Op] in
theorem update_sslB (k : Nat) :
    update (sslB obj op k) 1 (ssd obj op (k + 1)) = sslA obj op (k + 1) := by
  funext q
  by_cases h : q = 1
  · subst h; simp [update, sslA]
  · have h0 := fin2_eq_zero h
    subst h0; simp [update, sslA, sslB]

omit [DecidableEq Op] in
/-- **Both processes propose the trace committed by round `k + 1`.** -/
theorem proposal_eq (k : Nat) :
    proposal obj (ssd obj op k) (scmds op k) = str obj op (k + 1) := by
  show (Tagged (n := 2) obj).traceAppend (str obj op k)
    (Quotient.mk _ (scmds op k)) = str obj op (k + 1)
  show (Quotient.mk _ ((slist op k) ++ (scmds op k)) : (Tagged (n := 2) obj).Trace)
    = Quotient.mk _ (slist op (k + 1))
  simp [slist, scmds]

/-! ### The collects and the gathers -/

omit [DecidableEq Op] in
theorem sbest_start (k : Nat) (q : Fin 2) :
    best obj (ssd obj op k) (sslA obj op k q) = ssd obj op k := by
  simp [best, sslA]

omit [DecidableEq Op] in
theorem sbest_check0 (k : Nat) :
    best obj (zeroSeed obj) (sslA obj op (k + 1) 0) = ssd obj op (k + 1) := by
  simp [best, sslA, zeroSeed, ssd]

omit [DecidableEq Op] in
theorem sbest_check1 (k : Nat) :
    best obj (ssd obj op (k + 1)) (sslA obj op (k + 1) 1) = ssd obj op (k + 1) := by
  simp [best, sslA]

theorem observe_zero (k : Nat) :
    observe obj (ssd obj op k) (sann op (k + 1) 0) [] = [scmd op 0 k] := by
  have hc : (Tagged (n := 2) obj).traceCount (scmd op 0 k) (str obj op k) = 0 := by
    rw [traceCount_str]; simp
  rw [sann_succ]
  simp [observe, hc, ssd]

theorem observe_one (k : Nat) :
    observe obj (ssd obj op k) (sann op (k + 1) 1) [scmd op 0 k] = scmds op k := by
  have hc : (Tagged (n := 2) obj).traceCount (scmd op 1 k) (str obj op k) = 0 := by
    rw [traceCount_str]; simp
  rw [sann_succ]
  simp [observe, hc, scmds, ssd]

/-! ### The cycle's configurations

Offsets `16 … 22` are process `0`'s six protocol events and its receive; offsets
`24 … 30` are process `1`'s.  Configurations repeat inside those two ranges, so
the cycle has twenty-six distinct states. -/

noncomputable def scallsM (k : Nat) : List (Call (n := 2) obj) :=
  ⟨k + 1, 0, str obj op (k + 1)⟩ :: scalls obj op k

noncomputable def sretsM (k : Nat) : List (Return (n := 2) obj) :=
  ⟨scmd op 0 k, k + 1, str obj op (k + 1)⟩ :: srets obj op k

noncomputable def b0 (k : Nat) : Configuration (n := 2) obj where
  sequence := sseqA k
  localState := sloc obj (.idle (ssd obj op k)) (.idle (ssd obj op k))
  slots := sslA obj op k
  announcements := sann op k
  calls := scalls obj op k
  returns := srets obj op k
  invocations := sinv op k

noncomputable def b1 (k : Nat) : Configuration (n := 2) obj :=
  { b0 obj op k with
    sequence := sseqB k
    invocations := scmd op 0 k :: sinv op k
    localState := sloc obj (.announcing (scmd op 0 k) (ssd obj op k))
      (.idle (ssd obj op k)) }

noncomputable def b2 (k : Nat) : Configuration (n := 2) obj :=
  { b1 obj op k with
    announcements := sannM op k
    localState := sloc obj
      (.collecting (scmd op 0 k) (List.finRange 2) (ssd obj op k))
      (.idle (ssd obj op k)) }

noncomputable def b3 (k : Nat) : Configuration (n := 2) obj :=
  { b2 obj op k with
    sequence := sseqA (k + 1)
    invocations := sinv op (k + 1)
    localState := sloc obj
      (.collecting (scmd op 0 k) (List.finRange 2) (ssd obj op k))
      (.announcing (scmd op 1 k) (ssd obj op k)) }

noncomputable def b4 (k : Nat) : Configuration (n := 2) obj :=
  { b3 obj op k with
    announcements := sann op (k + 1)
    localState := sloc obj
      (.collecting (scmd op 0 k) (List.finRange 2) (ssd obj op k))
      (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) }

noncomputable def b5 (k : Nat) : Configuration (n := 2) obj :=
  { b4 obj op k with
    localState := sloc obj (.collecting (scmd op 0 k) [1] (ssd obj op k))
      (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) }

noncomputable def b6 (k : Nat) : Configuration (n := 2) obj :=
  { b4 obj op k with
    localState := sloc obj (.collecting (scmd op 0 k) [] (ssd obj op k))
      (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) }

noncomputable def b7 (k : Nat) : Configuration (n := 2) obj :=
  { b4 obj op k with
    localState := sloc obj
      (.gathering (scmd op 0 k) (ssd obj op k) (List.finRange 2) [])
      (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) }

noncomputable def b8 (k : Nat) : Configuration (n := 2) obj :=
  { b4 obj op k with
    localState := sloc obj
      (.gathering (scmd op 0 k) (ssd obj op k) [1] [scmd op 0 k])
      (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) }

noncomputable def b9 (k : Nat) : Configuration (n := 2) obj :=
  { b4 obj op k with
    localState := sloc obj
      (.gathering (scmd op 0 k) (ssd obj op k) [] (scmds op k))
      (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) }

noncomputable def b10 (k : Nat) : Configuration (n := 2) obj :=
  { b4 obj op k with
    calls := scallsM obj op k
    localState := sloc obj
      (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1)))
      (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) }

noncomputable def b11 (k : Nat) : Configuration (n := 2) obj :=
  { b10 obj op k with
    localState := sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1)))
      (.collecting (scmd op 1 k) [1] (ssd obj op k)) }

noncomputable def b12 (k : Nat) : Configuration (n := 2) obj :=
  { b10 obj op k with
    localState := sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1)))
      (.collecting (scmd op 1 k) [] (ssd obj op k)) }

noncomputable def b13 (k : Nat) : Configuration (n := 2) obj :=
  { b10 obj op k with
    localState := sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1)))
      (.gathering (scmd op 1 k) (ssd obj op k) (List.finRange 2) []) }

noncomputable def b14 (k : Nat) : Configuration (n := 2) obj :=
  { b10 obj op k with
    localState := sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1)))
      (.gathering (scmd op 1 k) (ssd obj op k) [1] [scmd op 0 k]) }

noncomputable def b15 (k : Nat) : Configuration (n := 2) obj :=
  { b10 obj op k with
    localState := sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1)))
      (.gathering (scmd op 1 k) (ssd obj op k) [] (scmds op k)) }

/-- Both callers are inside round `k + 1`. -/
noncomputable def b16 (k : Nat) : Configuration (n := 2) obj :=
  { b10 obj op k with
    calls := scalls obj op (k + 1)
    localState := sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1)))
      (.waiting (scmd op 1 k) (k + 1) (str obj op (k + 1))) }

noncomputable def b23 (k : Nat) : Configuration (n := 2) obj :=
  { b16 obj op k with
    localState := sloc obj (.publishing (scmd op 0 k) (ssd obj op (k + 1)))
      (.waiting (scmd op 1 k) (k + 1) (str obj op (k + 1))) }

noncomputable def b24 (k : Nat) : Configuration (n := 2) obj :=
  { b16 obj op k with
    slots := sslB obj op k
    localState := sloc obj
      (.checking (scmd op 0 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj))
      (.waiting (scmd op 1 k) (k + 1) (str obj op (k + 1))) }

noncomputable def b31 (k : Nat) : Configuration (n := 2) obj :=
  { b24 obj op k with
    localState := sloc obj
      (.checking (scmd op 0 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj))
      (.publishing (scmd op 1 k) (ssd obj op (k + 1))) }

noncomputable def b32 (k : Nat) : Configuration (n := 2) obj :=
  { b24 obj op k with
    slots := sslA obj op (k + 1)
    localState := sloc obj
      (.checking (scmd op 0 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj))
      (.checking (scmd op 1 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) }

noncomputable def b33 (k : Nat) : Configuration (n := 2) obj :=
  { b32 obj op k with
    localState := sloc obj
      (.checking (scmd op 0 k) (ssd obj op (k + 1)) [1] (ssd obj op (k + 1)))
      (.checking (scmd op 1 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) }

noncomputable def b34 (k : Nat) : Configuration (n := 2) obj :=
  { b32 obj op k with
    localState := sloc obj
      (.checking (scmd op 0 k) (ssd obj op (k + 1)) [] (ssd obj op (k + 1)))
      (.checking (scmd op 1 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) }

noncomputable def b35 (k : Nat) : Configuration (n := 2) obj :=
  { b32 obj op k with
    returns := sretsM obj op k
    localState := sloc obj (.idle (ssd obj op (k + 1)))
      (.checking (scmd op 1 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) }

noncomputable def b36 (k : Nat) : Configuration (n := 2) obj :=
  { b35 obj op k with
    localState := sloc obj (.idle (ssd obj op (k + 1)))
      (.checking (scmd op 1 k) (ssd obj op (k + 1)) [1] (ssd obj op (k + 1))) }

noncomputable def b37 (k : Nat) : Configuration (n := 2) obj :=
  { b35 obj op k with
    localState := sloc obj (.idle (ssd obj op (k + 1)))
      (.checking (scmd op 1 k) (ssd obj op (k + 1)) [] (ssd obj op (k + 1))) }

omit [DecidableEq Op] in

/-! ### The GCA family: **two** participants per positive round

Both callers hand the same trace to round `r`, so Weak Agreement forces both
returns to be commits and Common Prefix with Validity forces the returned trace
to be exactly that input.  The protocol's own actor gives process `0` the
clocks `0 … 6` and process `1` the clocks `7 … 13` — the order in which the
global schedule feeds the round — and alternates afterwards, so both
participants take infinitely many protocol steps and both calls return. -/

def sactorAt (r c : Nat) : Option (Fin 2) :=
  if r = 0 then none
  else if c < 7 then some 0
  else if c < 14 then some 1
  else if c % 2 = 0 then some 0 else some 1

noncomputable def sfam : Family (n := 2) obj where
  protocol := fun r =>
    { participants := if r = 0 then [] else [0, 1]
      input := fun _ => str obj op r
      actor := sactorAt r
      actor_valid := by
        intro c p h
        by_cases hr : r = 0
        · rw [sactorAt, ite_eq_left hr] at h; exact absurd h (by simp)
        · simp only [hr, ite_false]
          unfold sactorAt at h
          rw [ite_eq_right hr] at h
          split at h
          · rw [← Option.some.inj h]; simp
          · split at h
            · rw [← Option.some.inj h]; simp
            · split at h
              · rw [← Option.some.inj h]; simp
              · rw [← Option.some.inj h]; simp
      acknowledged := fun _ => true }

omit [DecidableEq Op] in
theorem sfam_waitFree : (sfam obj op).SnapshotWaitFree obj :=
  fun _ => GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)

omit [DecidableEq Op] in
theorem sactorAt_lo (r c : Nat) (hr : r ≠ 0) (hc : c < 7) : sactorAt r c = some 0 := by
  simp [sactorAt, hr, hc]

omit [DecidableEq Op] in
theorem sactorAt_hi (r c : Nat) (hr : r ≠ 0) (h7 : 7 ≤ c) (h14 : c < 14) :
    sactorAt r c = some 1 := by
  have h : ¬ (c < 7) := by omega
  simp [sactorAt, hr, h, h14]

theorem sfam_input (r : Nat) (hr : r ≠ 0) (p : Fin 2) :
    ((sfam obj op).environment obj r).input p = some (str obj op r) := by
  simp [Family.environment, GCA.Protocol.history, GCA.Protocol.timed,
    GCA.TimedExecution.views, GCA.SnapshotExecution.history, sfam]
  exact ⟨hr, fun h => fin2_eq_one h⟩

/-- Both participants take infinitely many protocol steps, so both calls
return; the inputs agree, so both returns are the same commit. -/
theorem sfam_output (r : Nat) (hr : r ≠ 0) (p : Fin 2) :
    ((sfam obj op).environment obj r).output p = some (str obj op r, true) := by
  have hw : ((sfam obj op).protocol r).SnapshotWaitFree :=
    GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)
  have hinf : ((sfam obj op).protocol r).InfiniteSteps p := by
    intro N
    rcases WitnessC.fin2 p with rfl | rfl
    · refine ⟨2 * (N + 7), by omega, ?_⟩
      show sactorAt r (2 * (N + 7)) = some 0
      have h1 : ¬ (2 * (N + 7) < 7) := by omega
      have h2 : ¬ (2 * (N + 7) < 14) := by omega
      have h3 : 2 * (N + 7) % 2 = 0 := by omega
      simp [sactorAt, hr, h1, h2, h3]
    · refine ⟨2 * (N + 7) + 1, by omega, ?_⟩
      show sactorAt r (2 * (N + 7) + 1) = some 1
      have h1 : ¬ (2 * (N + 7) + 1 < 7) := by omega
      have h2 : ¬ (2 * (N + 7) + 1 < 14) := by omega
      simp [sactorAt, hr, h1, h2]
  obtain ⟨s, flag, ho⟩ := ((sfam obj op).protocol r).returned_of_infiniteSteps hw hinf
  have huniform : ∀ u, (((sfam obj op).environment obj r).Inputs u) → u = str obj op r := by
    intro u hu
    rw [Family.environment, GCA.Protocol.history, GCA.SnapshotExecution.inputs_iff] at hu
    obtain ⟨q, -, he⟩ := hu
    exact he.symm
  obtain ⟨rfl, rfl⟩ := (((sfam obj op).environment obj r).uniform_return
    ((sfam obj op).specification obj r) huniform ho)
  exact ho

omit [DecidableEq Op] in
/-- **Round `r` really has two participants.** -/
theorem sfam_participants (r : Nat) (hr : r ≠ 0) :
    ((sfam obj op).protocol r).participants = [0, 1] := by simp [sfam, hr]

/-! ### Projections -/

section Proj
omit [DecidableEq Op]
variable (k : Nat)

theorem b0_seq : (b0 obj op k).sequence = sseqA k := rfl
theorem b0_inv : (b0 obj op k).invocations = sinv op k := rfl
theorem b0_localState : (b0 obj op k).localState = sloc obj (.idle (ssd obj op k)) (.idle (ssd obj op k)) := rfl
theorem b0_local0 : (b0 obj op k).localState 0 = (.idle (ssd obj op k)) := by
  rw [b0_localState]; exact sloc_zero ..
theorem b0_local1 : (b0 obj op k).localState 1 = (.idle (ssd obj op k)) := by
  rw [b0_localState]; exact sloc_one ..

theorem b1_ann : (b1 obj op k).announcements = sann op k := rfl
theorem b1_localState : (b1 obj op k).localState = sloc obj (.announcing (scmd op 0 k) (ssd obj op k)) (.idle (ssd obj op k)) := rfl
theorem b1_local0 : (b1 obj op k).localState 0 = (.announcing (scmd op 0 k) (ssd obj op k)) := by
  rw [b1_localState]; exact sloc_zero ..

theorem b2_seq : (b2 obj op k).sequence = sseqB k := rfl
theorem b2_inv : (b2 obj op k).invocations = (scmd op 0 k) :: sinv op k := rfl
theorem b2_localState : (b2 obj op k).localState = sloc obj (.collecting (scmd op 0 k) (List.finRange 2) (ssd obj op k)) (.idle (ssd obj op k)) := rfl
theorem b2_local1 : (b2 obj op k).localState 1 = (.idle (ssd obj op k)) := by
  rw [b2_localState]; exact sloc_one ..

theorem b3_ann : (b3 obj op k).announcements = sannM op k := rfl
theorem b3_localState : (b3 obj op k).localState = sloc obj (.collecting (scmd op 0 k) (List.finRange 2) (ssd obj op k)) (.announcing (scmd op 1 k) (ssd obj op k)) := rfl
theorem b3_local1 : (b3 obj op k).localState 1 = (.announcing (scmd op 1 k) (ssd obj op k)) := by
  rw [b3_localState]; exact sloc_one ..

theorem b4_slots : (b4 obj op k).slots = sslA obj op k := rfl
theorem b4_localState : (b4 obj op k).localState = sloc obj (.collecting (scmd op 0 k) (List.finRange 2) (ssd obj op k)) (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) := rfl
theorem b4_local0 : (b4 obj op k).localState 0 = (.collecting (scmd op 0 k) (List.finRange 2) (ssd obj op k)) := by
  rw [b4_localState]; exact sloc_zero ..

theorem b5_slots : (b5 obj op k).slots = sslA obj op k := rfl
theorem b5_localState : (b5 obj op k).localState = sloc obj (.collecting (scmd op 0 k) [1] (ssd obj op k)) (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) := rfl
theorem b5_local0 : (b5 obj op k).localState 0 = (.collecting (scmd op 0 k) [1] (ssd obj op k)) := by
  rw [b5_localState]; exact sloc_zero ..

theorem b6_localState : (b6 obj op k).localState = sloc obj (.collecting (scmd op 0 k) [] (ssd obj op k)) (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) := rfl
theorem b6_local0 : (b6 obj op k).localState 0 = (.collecting (scmd op 0 k) [] (ssd obj op k)) := by
  rw [b6_localState]; exact sloc_zero ..

theorem b7_ann : (b7 obj op k).announcements = sann op (k + 1) := rfl
theorem b7_localState : (b7 obj op k).localState = sloc obj (.gathering (scmd op 0 k) (ssd obj op k) (List.finRange 2) []) (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) := rfl
theorem b7_local0 : (b7 obj op k).localState 0 = (.gathering (scmd op 0 k) (ssd obj op k) (List.finRange 2) []) := by
  rw [b7_localState]; exact sloc_zero ..

theorem b8_ann : (b8 obj op k).announcements = sann op (k + 1) := rfl
theorem b8_localState : (b8 obj op k).localState = sloc obj (.gathering (scmd op 0 k) (ssd obj op k) [1] [(scmd op 0 k)]) (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) := rfl
theorem b8_local0 : (b8 obj op k).localState 0 = (.gathering (scmd op 0 k) (ssd obj op k) [1] [(scmd op 0 k)]) := by
  rw [b8_localState]; exact sloc_zero ..

theorem b9_localState : (b9 obj op k).localState = sloc obj (.gathering (scmd op 0 k) (ssd obj op k) [] (scmds op k)) (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) := rfl
theorem b9_local0 : (b9 obj op k).localState 0 = (.gathering (scmd op 0 k) (ssd obj op k) [] (scmds op k)) := by
  rw [b9_localState]; exact sloc_zero ..

theorem b10_slots : (b10 obj op k).slots = sslA obj op k := rfl
theorem b10_localState : (b10 obj op k).localState = sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1))) (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) := rfl
theorem b10_local1 : (b10 obj op k).localState 1 = (.collecting (scmd op 1 k) (List.finRange 2) (ssd obj op k)) := by
  rw [b10_localState]; exact sloc_one ..

theorem b11_slots : (b11 obj op k).slots = sslA obj op k := rfl
theorem b11_localState : (b11 obj op k).localState = sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1))) (.collecting (scmd op 1 k) [1] (ssd obj op k)) := rfl
theorem b11_local1 : (b11 obj op k).localState 1 = (.collecting (scmd op 1 k) [1] (ssd obj op k)) := by
  rw [b11_localState]; exact sloc_one ..

theorem b12_localState : (b12 obj op k).localState = sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1))) (.collecting (scmd op 1 k) [] (ssd obj op k)) := rfl
theorem b12_local1 : (b12 obj op k).localState 1 = (.collecting (scmd op 1 k) [] (ssd obj op k)) := by
  rw [b12_localState]; exact sloc_one ..

theorem b13_ann : (b13 obj op k).announcements = sann op (k + 1) := rfl
theorem b13_localState : (b13 obj op k).localState = sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1))) (.gathering (scmd op 1 k) (ssd obj op k) (List.finRange 2) []) := rfl
theorem b13_local1 : (b13 obj op k).localState 1 = (.gathering (scmd op 1 k) (ssd obj op k) (List.finRange 2) []) := by
  rw [b13_localState]; exact sloc_one ..

theorem b14_ann : (b14 obj op k).announcements = sann op (k + 1) := rfl
theorem b14_localState : (b14 obj op k).localState = sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1))) (.gathering (scmd op 1 k) (ssd obj op k) [1] [(scmd op 0 k)]) := rfl
theorem b14_local1 : (b14 obj op k).localState 1 = (.gathering (scmd op 1 k) (ssd obj op k) [1] [(scmd op 0 k)]) := by
  rw [b14_localState]; exact sloc_one ..

theorem b15_localState : (b15 obj op k).localState = sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1))) (.gathering (scmd op 1 k) (ssd obj op k) [] (scmds op k)) := rfl
theorem b15_local1 : (b15 obj op k).localState 1 = (.gathering (scmd op 1 k) (ssd obj op k) [] (scmds op k)) := by
  rw [b15_localState]; exact sloc_one ..

theorem b16_inv : (b16 obj op k).invocations = sinv op (k + 1) := rfl
theorem b16_localState : (b16 obj op k).localState = sloc obj (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1))) (.waiting (scmd op 1 k) (k + 1) (str obj op (k + 1))) := rfl
theorem b16_local0 : (b16 obj op k).localState 0 = (.waiting (scmd op 0 k) (k + 1) (str obj op (k + 1))) := by
  rw [b16_localState]; exact sloc_zero ..
theorem b16_local1 : (b16 obj op k).localState 1 = (.waiting (scmd op 1 k) (k + 1) (str obj op (k + 1))) := by
  rw [b16_localState]; exact sloc_one ..

theorem b23_slots : (b23 obj op k).slots = sslA obj op k := rfl
theorem b23_localState : (b23 obj op k).localState = sloc obj (.publishing (scmd op 0 k) (ssd obj op (k + 1))) (.waiting (scmd op 1 k) (k + 1) (str obj op (k + 1))) := rfl
theorem b23_local0 : (b23 obj op k).localState 0 = (.publishing (scmd op 0 k) (ssd obj op (k + 1))) := by
  rw [b23_localState]; exact sloc_zero ..

theorem b24_localState : (b24 obj op k).localState = sloc obj (.checking (scmd op 0 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) (.waiting (scmd op 1 k) (k + 1) (str obj op (k + 1))) := rfl
theorem b24_local1 : (b24 obj op k).localState 1 = (.waiting (scmd op 1 k) (k + 1) (str obj op (k + 1))) := by
  rw [b24_localState]; exact sloc_one ..

theorem b31_slots : (b31 obj op k).slots = sslB obj op k := rfl
theorem b31_localState : (b31 obj op k).localState = sloc obj (.checking (scmd op 0 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) (.publishing (scmd op 1 k) (ssd obj op (k + 1))) := rfl
theorem b31_local1 : (b31 obj op k).localState 1 = (.publishing (scmd op 1 k) (ssd obj op (k + 1))) := by
  rw [b31_localState]; exact sloc_one ..

theorem b32_slots : (b32 obj op k).slots = sslA obj op (k + 1) := rfl
theorem b32_localState : (b32 obj op k).localState = sloc obj (.checking (scmd op 0 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) (.checking (scmd op 1 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) := rfl
theorem b32_local0 : (b32 obj op k).localState 0 = (.checking (scmd op 0 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) := by
  rw [b32_localState]; exact sloc_zero ..

theorem b33_slots : (b33 obj op k).slots = sslA obj op (k + 1) := rfl
theorem b33_localState : (b33 obj op k).localState = sloc obj (.checking (scmd op 0 k) (ssd obj op (k + 1)) [1] (ssd obj op (k + 1))) (.checking (scmd op 1 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) := rfl
theorem b33_local0 : (b33 obj op k).localState 0 = (.checking (scmd op 0 k) (ssd obj op (k + 1)) [1] (ssd obj op (k + 1))) := by
  rw [b33_localState]; exact sloc_zero ..

theorem b34_localState : (b34 obj op k).localState = sloc obj (.checking (scmd op 0 k) (ssd obj op (k + 1)) [] (ssd obj op (k + 1))) (.checking (scmd op 1 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) := rfl
theorem b34_local0 : (b34 obj op k).localState 0 = (.checking (scmd op 0 k) (ssd obj op (k + 1)) [] (ssd obj op (k + 1))) := by
  rw [b34_localState]; exact sloc_zero ..

theorem b35_slots : (b35 obj op k).slots = sslA obj op (k + 1) := rfl
theorem b35_localState : (b35 obj op k).localState = sloc obj (.idle (ssd obj op (k + 1))) (.checking (scmd op 1 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) := rfl
theorem b35_local1 : (b35 obj op k).localState 1 = (.checking (scmd op 1 k) (ssd obj op (k + 1)) (List.finRange 2) (zeroSeed obj)) := by
  rw [b35_localState]; exact sloc_one ..

theorem b36_slots : (b36 obj op k).slots = sslA obj op (k + 1) := rfl
theorem b36_localState : (b36 obj op k).localState = sloc obj (.idle (ssd obj op (k + 1))) (.checking (scmd op 1 k) (ssd obj op (k + 1)) [1] (ssd obj op (k + 1))) := rfl
theorem b36_local1 : (b36 obj op k).localState 1 = (.checking (scmd op 1 k) (ssd obj op (k + 1)) [1] (ssd obj op (k + 1))) := by
  rw [b36_localState]; exact sloc_one ..

theorem b37_localState : (b37 obj op k).localState = sloc obj (.idle (ssd obj op (k + 1))) (.checking (scmd op 1 k) (ssd obj op (k + 1)) [] (ssd obj op (k + 1))) := rfl
theorem b37_local1 : (b37 obj op k).localState 1 = (.checking (scmd op 1 k) (ssd obj op (k + 1)) [] (ssd obj op (k + 1))) := by
  rw [b37_localState]; exact sloc_one ..

end Proj

/-! ### The twenty-six steps of a cycle -/

section Steps
variable {H : WeakUniversal.Environment (n := 2) obj}

theorem step_invoke0 (k : Nat) : Step obj H (b0 obj op k) (b1 obj op k) := by
  have h := Step.invoke (H := H) (b0 obj op k) 0 op (ssd obj op k) (b0_local0 obj op k)
  simp only [b0_seq, b0_inv, b0_localState, sseqA_zero, update_sseqA, update_sloc0] at h
  exact h

theorem step_announce0 (k : Nat) : Step obj H (b1 obj op k) (b2 obj op k) := by
  have h := Step.announce (H := H) (b1 obj op k) 0 (scmd op 0 k) (ssd obj op k)
    (b1_local0 obj op k) (List.finRange 2) (List.Perm.refl _)
  simp only [b1_ann, b1_localState, update_sannA, update_sloc0] at h
  exact h

theorem step_invoke1 (k : Nat) : Step obj H (b2 obj op k) (b3 obj op k) := by
  have h := Step.invoke (H := H) (b2 obj op k) 1 op (ssd obj op k) (b2_local1 obj op k)
  simp only [b2_seq, b2_inv, b2_localState, sseqB_one, update_sseqB, update_sloc1] at h
  exact h

theorem step_announce1 (k : Nat) : Step obj H (b3 obj op k) (b4 obj op k) := by
  have h := Step.announce (H := H) (b3 obj op k) 1 (scmd op 1 k) (ssd obj op k)
    (b3_local1 obj op k) (List.finRange 2) (List.Perm.refl _)
  simp only [b3_ann, b3_localState, update_sannB, update_sloc1] at h
  exact h

theorem step_read0_0 (k : Nat) : Step obj H (b4 obj op k) (b5 obj op k) := by
  have hloc : (b4 obj op k).localState 0
      = .collecting (scmd op 0 k) (0 :: [1]) (ssd obj op k) := by
    rw [b4_local0, WitnessC.finRange_two]
  have h := Step.readStart (H := H) (b4 obj op k) 0 0 (scmd op 0 k) [1] (ssd obj op k) hloc
  simp only [b4_slots, sbest_start, b4_localState, update_sloc0] at h
  exact h

theorem step_read0_1 (k : Nat) : Step obj H (b5 obj op k) (b6 obj op k) := by
  have hloc : (b5 obj op k).localState 0
      = .collecting (scmd op 0 k) (1 :: []) (ssd obj op k) := b5_local0 obj op k
  have h := Step.readStart (H := H) (b5 obj op k) 0 1 (scmd op 0 k) [] (ssd obj op k) hloc
  simp only [b5_slots, sbest_start, b5_localState, update_sloc0] at h
  exact h

theorem step_collected0 (k : Nat) : Step obj H (b6 obj op k) (b7 obj op k) := by
  have h := Step.collectedStart (H := H) (b6 obj op k) 0 (scmd op 0 k) (ssd obj op k)
    (b6_local0 obj op k) (List.finRange 2) (List.Perm.refl _)
  simp only [b6_localState, update_sloc0] at h
  exact h

theorem step_gather0_0 (k : Nat) : Step obj H (b7 obj op k) (b8 obj op k) := by
  have hloc : (b7 obj op k).localState 0
      = .gathering (scmd op 0 k) (ssd obj op k) (0 :: [1]) [] := by
    rw [b7_local0, WitnessC.finRange_two]
  have h := Step.readAnnouncement (H := H) (b7 obj op k) 0 0 (scmd op 0 k) (ssd obj op k)
    [1] [] hloc
  simp only [b7_ann, observe_zero, b7_localState, update_sloc0] at h
  exact h

theorem step_gather0_1 (k : Nat) : Step obj H (b8 obj op k) (b9 obj op k) := by
  have hloc : (b8 obj op k).localState 0
      = .gathering (scmd op 0 k) (ssd obj op k) (1 :: []) [scmd op 0 k] :=
    b8_local0 obj op k
  have h := Step.readAnnouncement (H := H) (b8 obj op k) 0 1 (scmd op 0 k) (ssd obj op k)
    [] [scmd op 0 k] hloc
  simp only [b8_ann, observe_one, b8_localState, update_sloc0] at h
  exact h

theorem step_propose0 (k : Nat) :
    Step obj ((sfam obj op).environment obj) (b9 obj op k) (b10 obj op k) := by
  have hi : ((sfam obj op).environment obj ((ssd obj op k).round + 1)).input 0
      = some (proposal obj (ssd obj op k) (scmds op k)) := by
    show ((sfam obj op).environment obj (k + 1)).input 0 = _
    rw [proposal_eq]
    exact sfam_input obj op (k + 1) (by omega) 0
  have h := Step.propose (b9 obj op k) 0 (scmd op 0 k) (ssd obj op k) (scmds op k)
    (b9_local0 obj op k) (scmds op k) (List.Perm.refl _) hi
  simp only [b9_localState, update_sloc0, proposal_eq] at h
  exact h

theorem step_read1_0 (k : Nat) : Step obj H (b10 obj op k) (b11 obj op k) := by
  have hloc : (b10 obj op k).localState 1
      = .collecting (scmd op 1 k) (0 :: [1]) (ssd obj op k) := by
    rw [b10_local1, WitnessC.finRange_two]
  have h := Step.readStart (H := H) (b10 obj op k) 1 0 (scmd op 1 k) [1] (ssd obj op k) hloc
  simp only [b10_slots, sbest_start, b10_localState, update_sloc1] at h
  exact h

theorem step_read1_1 (k : Nat) : Step obj H (b11 obj op k) (b12 obj op k) := by
  have hloc : (b11 obj op k).localState 1
      = .collecting (scmd op 1 k) (1 :: []) (ssd obj op k) := b11_local1 obj op k
  have h := Step.readStart (H := H) (b11 obj op k) 1 1 (scmd op 1 k) [] (ssd obj op k) hloc
  simp only [b11_slots, sbest_start, b11_localState, update_sloc1] at h
  exact h

theorem step_collected1 (k : Nat) : Step obj H (b12 obj op k) (b13 obj op k) := by
  have h := Step.collectedStart (H := H) (b12 obj op k) 1 (scmd op 1 k) (ssd obj op k)
    (b12_local1 obj op k) (List.finRange 2) (List.Perm.refl _)
  simp only [b12_localState, update_sloc1] at h
  exact h

theorem step_gather1_0 (k : Nat) : Step obj H (b13 obj op k) (b14 obj op k) := by
  have hloc : (b13 obj op k).localState 1
      = .gathering (scmd op 1 k) (ssd obj op k) (0 :: [1]) [] := by
    rw [b13_local1, WitnessC.finRange_two]
  have h := Step.readAnnouncement (H := H) (b13 obj op k) 1 0 (scmd op 1 k) (ssd obj op k)
    [1] [] hloc
  simp only [b13_ann, observe_zero, b13_localState, update_sloc1] at h
  exact h

theorem step_gather1_1 (k : Nat) : Step obj H (b14 obj op k) (b15 obj op k) := by
  have hloc : (b14 obj op k).localState 1
      = .gathering (scmd op 1 k) (ssd obj op k) (1 :: []) [scmd op 0 k] :=
    b14_local1 obj op k
  have h := Step.readAnnouncement (H := H) (b14 obj op k) 1 1 (scmd op 1 k) (ssd obj op k)
    [] [scmd op 0 k] hloc
  simp only [b14_ann, observe_one, b14_localState, update_sloc1] at h
  exact h

/-- **The second caller proposes the identical trace to the same round.** -/
theorem step_propose1 (k : Nat) :
    Step obj ((sfam obj op).environment obj) (b15 obj op k) (b16 obj op k) := by
  have hi : ((sfam obj op).environment obj ((ssd obj op k).round + 1)).input 1
      = some (proposal obj (ssd obj op k) (scmds op k)) := by
    show ((sfam obj op).environment obj (k + 1)).input 1 = _
    rw [proposal_eq]
    exact sfam_input obj op (k + 1) (by omega) 1
  have h := Step.propose (b15 obj op k) 1 (scmd op 1 k) (ssd obj op k) (scmds op k)
    (b15_local1 obj op k) (scmds op k) (List.Perm.refl _) hi
  simp only [b15_localState, update_sloc1, proposal_eq] at h
  exact h

theorem step_receive0 (k : Nat) :
    Step obj ((sfam obj op).environment obj) (b16 obj op k) (b23 obj op k) := by
  have h := Step.receive (b16 obj op k) 0 (scmd op 0 k) (k + 1) (str obj op (k + 1))
    (str obj op (k + 1)) true (b16_local0 obj op k)
    (sfam_output obj op (k + 1) (by omega) 0) (List.finRange 2) (List.Perm.refl _)
  simp only [b16_localState, update_sloc0] at h
  exact h

theorem step_publish0 (k : Nat) : Step obj H (b23 obj op k) (b24 obj op k) := by
  have h := Step.publish (H := H) (b23 obj op k) 0 (scmd op 0 k) (ssd obj op (k + 1))
    (b23_local0 obj op k) (List.finRange 2) (List.Perm.refl _)
  simp only [b23_slots, b23_localState, update_sslA, update_sloc0] at h
  exact h

theorem step_receive1 (k : Nat) :
    Step obj ((sfam obj op).environment obj) (b24 obj op k) (b31 obj op k) := by
  have h := Step.receive (b24 obj op k) 1 (scmd op 1 k) (k + 1) (str obj op (k + 1))
    (str obj op (k + 1)) true (b24_local1 obj op k)
    (sfam_output obj op (k + 1) (by omega) 1) (List.finRange 2) (List.Perm.refl _)
  simp only [b24_localState, update_sloc1] at h
  exact h

theorem step_publish1 (k : Nat) : Step obj H (b31 obj op k) (b32 obj op k) := by
  have h := Step.publish (H := H) (b31 obj op k) 1 (scmd op 1 k) (ssd obj op (k + 1))
    (b31_local1 obj op k) (List.finRange 2) (List.Perm.refl _)
  simp only [b31_slots, b31_localState, update_sslB, update_sloc1] at h
  exact h

theorem step_check0_0 (k : Nat) : Step obj H (b32 obj op k) (b33 obj op k) := by
  have hloc : (b32 obj op k).localState 0
      = .checking (scmd op 0 k) (ssd obj op (k + 1)) (0 :: [1]) (zeroSeed obj) := by
    rw [b32_local0, WitnessC.finRange_two]
  have h := Step.readCheck (H := H) (b32 obj op k) 0 0 (scmd op 0 k) (ssd obj op (k + 1))
    [1] (zeroSeed obj) hloc
  simp only [b32_slots, sbest_check0, b32_localState, update_sloc0] at h
  exact h

theorem step_check0_1 (k : Nat) : Step obj H (b33 obj op k) (b34 obj op k) := by
  have hloc : (b33 obj op k).localState 0
      = .checking (scmd op 0 k) (ssd obj op (k + 1)) (1 :: []) (ssd obj op (k + 1)) :=
    b33_local0 obj op k
  have h := Step.readCheck (H := H) (b33 obj op k) 0 1 (scmd op 0 k) (ssd obj op (k + 1))
    [] (ssd obj op (k + 1)) hloc
  simp only [b33_slots, sbest_check1, b33_localState, update_sloc0] at h
  exact h

theorem step_finish0 (k : Nat) : Step obj H (b34 obj op k) (b35 obj op k) := by
  have hcount : 0 < (Tagged (n := 2) obj).traceCount (scmd op 0 k)
      (ssd obj op (k + 1)).trace := by
    show 0 < (Tagged (n := 2) obj).traceCount (scmd op 0 k) (str obj op (k + 1))
    rw [traceCount_str]; simp
  have h := Step.finish (H := H) (b34 obj op k) 0 (scmd op 0 k) (ssd obj op (k + 1))
    (ssd obj op (k + 1)) (b34_local0 obj op k) hcount
  simp only [b34_localState, update_sloc0] at h
  exact h

theorem step_check1_0 (k : Nat) : Step obj H (b35 obj op k) (b36 obj op k) := by
  have hloc : (b35 obj op k).localState 1
      = .checking (scmd op 1 k) (ssd obj op (k + 1)) (0 :: [1]) (zeroSeed obj) := by
    rw [b35_local1, WitnessC.finRange_two]
  have h := Step.readCheck (H := H) (b35 obj op k) 1 0 (scmd op 1 k) (ssd obj op (k + 1))
    [1] (zeroSeed obj) hloc
  simp only [b35_slots, sbest_check0, b35_localState, update_sloc1] at h
  exact h

theorem step_check1_1 (k : Nat) : Step obj H (b36 obj op k) (b37 obj op k) := by
  have hloc : (b36 obj op k).localState 1
      = .checking (scmd op 1 k) (ssd obj op (k + 1)) (1 :: []) (ssd obj op (k + 1)) :=
    b36_local1 obj op k
  have h := Step.readCheck (H := H) (b36 obj op k) 1 1 (scmd op 1 k) (ssd obj op (k + 1))
    [] (ssd obj op (k + 1)) hloc
  simp only [b36_slots, sbest_check1, b36_localState, update_sloc1] at h
  exact h

theorem step_finish1 (k : Nat) : Step obj H (b37 obj op k) (b0 obj op (k + 1)) := by
  have hcount : 0 < (Tagged (n := 2) obj).traceCount (scmd op 1 k)
      (ssd obj op (k + 1)).trace := by
    show 0 < (Tagged (n := 2) obj).traceCount (scmd op 1 k) (str obj op (k + 1))
    rw [traceCount_str]; simp
  have h := Step.finish (H := H) (b37 obj op k) 1 (scmd op 1 k) (ssd obj op (k + 1))
    (ssd obj op (k + 1)) (b37_local1 obj op k) hcount
  simp only [b37_localState, update_sloc1] at h
  exact h

end Steps

/-! ### The infinite run

The cycle is `38` steps and there is no prologue.  Process `0` acts at the
offsets `0,1`, `4 … 9`, `16 … 23` and `32 … 34`; process `1` at the rest.
Offsets `16 … 21` and `24 … 29` are the two callers' protocol events. -/

noncomputable def scyc (k : Nat) : Nat → Configuration (n := 2) obj
  | 0 => b0 obj op k
  | 1 => b1 obj op k
  | 2 => b2 obj op k
  | 3 => b3 obj op k
  | 4 => b4 obj op k
  | 5 => b5 obj op k
  | 6 => b6 obj op k
  | 7 => b7 obj op k
  | 8 => b8 obj op k
  | 9 => b9 obj op k
  | 10 => b10 obj op k
  | 11 => b11 obj op k
  | 12 => b12 obj op k
  | 13 => b13 obj op k
  | 14 => b14 obj op k
  | 15 => b15 obj op k
  | 16 => b16 obj op k
  | 17 => b16 obj op k
  | 18 => b16 obj op k
  | 19 => b16 obj op k
  | 20 => b16 obj op k
  | 21 => b16 obj op k
  | 22 => b16 obj op k
  | 23 => b23 obj op k
  | 24 => b24 obj op k
  | 25 => b24 obj op k
  | 26 => b24 obj op k
  | 27 => b24 obj op k
  | 28 => b24 obj op k
  | 29 => b24 obj op k
  | 30 => b24 obj op k
  | 31 => b31 obj op k
  | 32 => b32 obj op k
  | 33 => b33 obj op k
  | 34 => b34 obj op k
  | 35 => b35 obj op k
  | 36 => b36 obj op k
  | _ => b37 obj op k

noncomputable def sstate (t : Nat) : Configuration (n := 2) obj :=
  scyc obj op (t / 38) (t % 38)

omit [DecidableEq Op] in
theorem sstate_at (k j : Nat) (hj : j < 38) :
    sstate obj op (j + 38 * k) = scyc obj op k j := by
  show scyc obj op ((j + 38 * k) / 38) ((j + 38 * k) % 38) = _
  rw [Nat.add_mul_div_left _ _ (by omega : 0 < 38), Nat.div_eq_of_lt hj,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj, Nat.zero_add]

omit [DecidableEq Op] in
theorem sstate_succ (k j : Nat) (hj : j < 37) :
    sstate obj op (j + 38 * k + 1) = scyc obj op k (j + 1) := by
  rw [show j + 38 * k + 1 = (j + 1) + 38 * k from by omega,
    sstate_at obj op k (j + 1) (by omega)]

omit [DecidableEq Op] in
theorem sstate_succ_wrap (k : Nat) :
    sstate obj op (37 + 38 * k + 1) = b0 obj op (k + 1) := by
  rw [show 37 + 38 * k + 1 = 0 + 38 * (k + 1) from by omega,
    sstate_at obj op (k + 1) 0 (by omega)]
  rfl

omit [DecidableEq Op] in
/-- The twelve protocol events: the program stutters while the calls advance. -/
theorem sstutter_at (k j : Nat) (hst : (16 ≤ j ∧ j ≤ 21) ∨ (24 ≤ j ∧ j ≤ 29)) :
    sstate obj op (j + 38 * k + 1) = sstate obj op (j + 38 * k) := by
  have hj : j < 37 := by omega
  rw [sstate_succ obj op k j hj, sstate_at obj op k j (by omega)]
  match j, hst with
  | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ =>
      rfl
  | (n + 30), h => exact absurd h (by omega)

theorem sstep_at (k j : Nat) (hj : j < 38)
    (hst : ¬ ((16 ≤ j ∧ j ≤ 21) ∨ (24 ≤ j ∧ j ≤ 29))) :
    Step obj ((sfam obj op).environment obj)
      (sstate obj op (j + 38 * k)) (sstate obj op (j + 38 * k + 1)) := by
  rw [sstate_at obj op k j hj]
  match j, hj, hst with
  | 0, _, _ => rw [sstate_succ obj op k 0 (by omega)]; exact step_invoke0 obj op k
  | 1, _, _ => rw [sstate_succ obj op k 1 (by omega)]; exact step_announce0 obj op k
  | 2, _, _ => rw [sstate_succ obj op k 2 (by omega)]; exact step_invoke1 obj op k
  | 3, _, _ => rw [sstate_succ obj op k 3 (by omega)]; exact step_announce1 obj op k
  | 4, _, _ => rw [sstate_succ obj op k 4 (by omega)]; exact step_read0_0 obj op k
  | 5, _, _ => rw [sstate_succ obj op k 5 (by omega)]; exact step_read0_1 obj op k
  | 6, _, _ => rw [sstate_succ obj op k 6 (by omega)]; exact step_collected0 obj op k
  | 7, _, _ => rw [sstate_succ obj op k 7 (by omega)]; exact step_gather0_0 obj op k
  | 8, _, _ => rw [sstate_succ obj op k 8 (by omega)]; exact step_gather0_1 obj op k
  | 9, _, _ => rw [sstate_succ obj op k 9 (by omega)]; exact step_propose0 obj op k
  | 10, _, _ => rw [sstate_succ obj op k 10 (by omega)]; exact step_read1_0 obj op k
  | 11, _, _ => rw [sstate_succ obj op k 11 (by omega)]; exact step_read1_1 obj op k
  | 12, _, _ => rw [sstate_succ obj op k 12 (by omega)]; exact step_collected1 obj op k
  | 13, _, _ => rw [sstate_succ obj op k 13 (by omega)]; exact step_gather1_0 obj op k
  | 14, _, _ => rw [sstate_succ obj op k 14 (by omega)]; exact step_gather1_1 obj op k
  | 15, _, _ => rw [sstate_succ obj op k 15 (by omega)]; exact step_propose1 obj op k
  | 16, _, h => exact absurd (by omega : (16 ≤ 16 ∧ 16 ≤ 21) ∨ (24 ≤ 16 ∧ 16 ≤ 29)) h
  | 17, _, h => exact absurd (by omega : (16 ≤ 17 ∧ 17 ≤ 21) ∨ (24 ≤ 17 ∧ 17 ≤ 29)) h
  | 18, _, h => exact absurd (by omega : (16 ≤ 18 ∧ 18 ≤ 21) ∨ (24 ≤ 18 ∧ 18 ≤ 29)) h
  | 19, _, h => exact absurd (by omega : (16 ≤ 19 ∧ 19 ≤ 21) ∨ (24 ≤ 19 ∧ 19 ≤ 29)) h
  | 20, _, h => exact absurd (by omega : (16 ≤ 20 ∧ 20 ≤ 21) ∨ (24 ≤ 20 ∧ 20 ≤ 29)) h
  | 21, _, h => exact absurd (by omega : (16 ≤ 21 ∧ 21 ≤ 21) ∨ (24 ≤ 21 ∧ 21 ≤ 29)) h
  | 22, _, _ => rw [sstate_succ obj op k 22 (by omega)]; exact step_receive0 obj op k
  | 23, _, _ => rw [sstate_succ obj op k 23 (by omega)]; exact step_publish0 obj op k
  | 24, _, h => exact absurd (by omega : (16 ≤ 24 ∧ 24 ≤ 21) ∨ (24 ≤ 24 ∧ 24 ≤ 29)) h
  | 25, _, h => exact absurd (by omega : (16 ≤ 25 ∧ 25 ≤ 21) ∨ (24 ≤ 25 ∧ 25 ≤ 29)) h
  | 26, _, h => exact absurd (by omega : (16 ≤ 26 ∧ 26 ≤ 21) ∨ (24 ≤ 26 ∧ 26 ≤ 29)) h
  | 27, _, h => exact absurd (by omega : (16 ≤ 27 ∧ 27 ≤ 21) ∨ (24 ≤ 27 ∧ 27 ≤ 29)) h
  | 28, _, h => exact absurd (by omega : (16 ≤ 28 ∧ 28 ≤ 21) ∨ (24 ≤ 28 ∧ 28 ≤ 29)) h
  | 29, _, h => exact absurd (by omega : (16 ≤ 29 ∧ 29 ≤ 21) ∨ (24 ≤ 29 ∧ 29 ≤ 29)) h
  | 30, _, _ => rw [sstate_succ obj op k 30 (by omega)]; exact step_receive1 obj op k
  | 31, _, _ => rw [sstate_succ obj op k 31 (by omega)]; exact step_publish1 obj op k
  | 32, _, _ => rw [sstate_succ obj op k 32 (by omega)]; exact step_check0_0 obj op k
  | 33, _, _ => rw [sstate_succ obj op k 33 (by omega)]; exact step_check0_1 obj op k
  | 34, _, _ => rw [sstate_succ obj op k 34 (by omega)]; exact step_finish0 obj op k
  | 35, _, _ => rw [sstate_succ obj op k 35 (by omega)]; exact step_check1_0 obj op k
  | 36, _, _ => rw [sstate_succ obj op k 36 (by omega)]; exact step_check1_1 obj op k
  | 37, _, _ => rw [sstate_succ_wrap obj op k]; exact step_finish1 obj op k
  | (n + 38), h, _ => exact absurd h (by omega)

omit [DecidableEq Op] in
theorem b0_zero_eq_initial : b0 obj op 0 = HelpingUniversal.initial obj := by
  refine WitnessC.config_ext obj rfl ?_ rfl ?_ rfl rfl rfl
  · funext q
    rcases WitnessC.fin2 q with rfl | rfl
    · rw [b0_local0]; rfl
    · rw [b0_local1]; rfl
  · funext q; simp [b0, sann, HelpingUniversal.initial]

/-- The run of Algorithm 3 the witness exhibits. -/
noncomputable def srun :
    HelpingUniversal.Execution obj ((sfam obj op).environment obj) where
  state := sstate obj op
  initial_state := by
    show scyc obj op (0 / 38) (0 % 38) = HelpingUniversal.initial obj
    rw [Nat.zero_div, Nat.zero_mod]
    exact b0_zero_eq_initial obj op
  next := by
    intro t
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 38 ∧ t = j + 38 * k :=
      ⟨t / 38, t % 38, Nat.mod_lt _ (by omega), (Nat.mod_add_div t 38).symm⟩
    by_cases hst : (16 ≤ j ∧ j ≤ 21) ∨ (24 ≤ j ∧ j ≤ 29)
    · exact Or.inl (sstutter_at obj op k j hst)
    · exact Or.inr (sstep_at obj op k j hj hst)

theorem srun_state : (srun obj op).state = sstate obj op := rfl

/-! ### The schedule's actor

Process `0` acts at the offsets `0,1`, `4 … 9`, `16 … 23` and `32 … 34`;
process `1` at the remaining ones. -/

def sact (j : Nat) : Fin 2 :=
  if j ≤ 1 then 0 else if j ≤ 3 then 1 else if j ≤ 9 then 0
  else if j ≤ 15 then 1 else if j ≤ 23 then 0 else if j ≤ 31 then 1
  else if j ≤ 34 then 0 else 1

def sactor : Nat → Option (Fin 2) := fun t => some (sact (t % 38))

omit [DecidableEq Op] in
theorem sactor_at (k j : Nat) (hj : j < 38) : sactor (j + 38 * k) = some (sact j) := by
  show some (sact ((j + 38 * k) % 38)) = _
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

omit [DecidableEq Op] in
theorem sact_zero (j : Nat) (h16 : 16 ≤ j) (h23 : j ≤ 23) : sact j = 0 := by
  unfold sact
  have h1 : ¬ (j ≤ 1) := by omega
  have h2 : ¬ (j ≤ 3) := by omega
  have h3 : ¬ (j ≤ 9) := by omega
  have h4 : ¬ (j ≤ 15) := by omega
  simp [h1, h2, h3, h4, h23]

omit [DecidableEq Op] in
theorem sact_one (j : Nat) (h24 : 24 ≤ j) (h31 : j ≤ 31) : sact j = 1 := by
  unfold sact
  have h1 : ¬ (j ≤ 1) := by omega
  have h2 : ¬ (j ≤ 3) := by omega
  have h3 : ¬ (j ≤ 9) := by omega
  have h4 : ¬ (j ≤ 15) := by omega
  have h5 : ¬ (j ≤ 23) := by omega
  simp [h1, h2, h3, h4, h5, h31]

/-! ### Which process is inside a call -/

omit [DecidableEq Op] in
/-- Process `0`'s own protocol events, offsets `16 … 22`. -/
theorem sround_mid0 (k j : Nat) (h16 : 16 ≤ j) (h22 : j ≤ 22) :
    helpingRound obj ((sstate obj op (j + 38 * k)).localState (sact j)) = some (k + 1) := by
  rw [sstate_at obj op k j (by omega)]
  match j, h16, h22 with
  | 16, _, _ => rfl
  | 17, _, _ => rfl
  | 18, _, _ => rfl
  | 19, _, _ => rfl
  | 20, _, _ => rfl
  | 21, _, _ => rfl
  | 22, _, _ => rfl
  | (n + 23), _, hh => exact absurd hh (by omega)

omit [DecidableEq Op] in
/-- Process `1`'s own protocol events, offsets `24 … 30`. -/
theorem sround_mid1 (k j : Nat) (h24 : 24 ≤ j) (h30 : j ≤ 30) :
    helpingRound obj ((sstate obj op (j + 38 * k)).localState (sact j)) = some (k + 1) := by
  rw [sstate_at obj op k j (by omega)]
  match j, h24, h30 with
  | 24, _, _ => rfl
  | 25, _, _ => rfl
  | 26, _, _ => rfl
  | 27, _, _ => rfl
  | 28, _, _ => rfl
  | 29, _, _ => rfl
  | 30, _, _ => rfl
  | (n + 31), _, hh => exact absurd hh (by omega)

omit [DecidableEq Op] in
theorem sround_none (k j : Nat) (hj : j < 38)
    (h : ¬ ((16 ≤ j ∧ j ≤ 22) ∨ (24 ≤ j ∧ j ≤ 30))) :
    helpingRound obj ((sstate obj op (j + 38 * k)).localState (sact j)) = none := by
  rw [sstate_at obj op k j hj]
  match j, hj, h with
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | 5, _, _ => rfl
  | 6, _, _ => rfl
  | 7, _, _ => rfl
  | 8, _, _ => rfl
  | 9, _, _ => rfl
  | 10, _, _ => rfl
  | 11, _, _ => rfl
  | 12, _, _ => rfl
  | 13, _, _ => rfl
  | 14, _, _ => rfl
  | 15, _, _ => rfl
  | 16, _, hh => exact absurd (by omega : (16 ≤ 16 ∧ 16 ≤ 22) ∨ (24 ≤ 16 ∧ 16 ≤ 30)) hh
  | 17, _, hh => exact absurd (by omega : (16 ≤ 17 ∧ 17 ≤ 22) ∨ (24 ≤ 17 ∧ 17 ≤ 30)) hh
  | 18, _, hh => exact absurd (by omega : (16 ≤ 18 ∧ 18 ≤ 22) ∨ (24 ≤ 18 ∧ 18 ≤ 30)) hh
  | 19, _, hh => exact absurd (by omega : (16 ≤ 19 ∧ 19 ≤ 22) ∨ (24 ≤ 19 ∧ 19 ≤ 30)) hh
  | 20, _, hh => exact absurd (by omega : (16 ≤ 20 ∧ 20 ≤ 22) ∨ (24 ≤ 20 ∧ 20 ≤ 30)) hh
  | 21, _, hh => exact absurd (by omega : (16 ≤ 21 ∧ 21 ≤ 22) ∨ (24 ≤ 21 ∧ 21 ≤ 30)) hh
  | 22, _, hh => exact absurd (by omega : (16 ≤ 22 ∧ 22 ≤ 22) ∨ (24 ≤ 22 ∧ 22 ≤ 30)) hh
  | 23, _, _ => rfl
  | 24, _, hh => exact absurd (by omega : (16 ≤ 24 ∧ 24 ≤ 22) ∨ (24 ≤ 24 ∧ 24 ≤ 30)) hh
  | 25, _, hh => exact absurd (by omega : (16 ≤ 25 ∧ 25 ≤ 22) ∨ (24 ≤ 25 ∧ 25 ≤ 30)) hh
  | 26, _, hh => exact absurd (by omega : (16 ≤ 26 ∧ 26 ≤ 22) ∨ (24 ≤ 26 ∧ 26 ≤ 30)) hh
  | 27, _, hh => exact absurd (by omega : (16 ≤ 27 ∧ 27 ≤ 22) ∨ (24 ≤ 27 ∧ 27 ≤ 30)) hh
  | 28, _, hh => exact absurd (by omega : (16 ≤ 28 ∧ 28 ≤ 22) ∨ (24 ≤ 28 ∧ 28 ≤ 30)) hh
  | 29, _, hh => exact absurd (by omega : (16 ≤ 29 ∧ 29 ≤ 22) ∨ (24 ≤ 29 ∧ 29 ≤ 30)) hh
  | 30, _, hh => exact absurd (by omega : (16 ≤ 30 ∧ 30 ≤ 22) ∨ (24 ≤ 30 ∧ 30 ≤ 30)) hh
  | 31, _, _ => rfl
  | 32, _, _ => rfl
  | 33, _, _ => rfl
  | 34, _, _ => rfl
  | 35, _, _ => rfl
  | 36, _, _ => rfl
  | 37, _, _ => rfl
  | (n + 38), hh, _ => exact absurd hh (by omega)

omit [DecidableEq Op] in
/-- **Only the scheduled process moves.** -/
theorem sother_at (k j : Nat) (hj : j < 38) :
    ∀ p : Fin 2, p ≠ sact j →
      (sstate obj op (j + 38 * k + 1)).localState p
        = (sstate obj op (j + 38 * k)).localState p := by
  -- at each position one of the two processes keeps its local state (`rfl`),
  -- and the other one is the scheduled process, excluded by `hp`
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _
  | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _
  | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ | 32, _ | 33, _ | 34, _
  | 35, _ | 36, _ =>
      rw [sstate_succ obj op k _ (by omega), sstate_at obj op k _ (by omega)]
      intro p hp
      rcases WitnessC.fin2 p with rfl | rfl <;> first | rfl | exact absurd rfl hp
  | 37, _ =>
      rw [sstate_succ_wrap obj op k, sstate_at obj op k 37 (by omega)]
      intro p hp
      rcases WitnessC.fin2 p with rfl | rfl <;> first | rfl | exact absurd rfl hp
  | (n + 38), hh => exact absurd hh (by omega)

/-! ### The projected protocol clock

Round `k + 1` receives process `0`'s seven events at the clocks `0 … 6` and
process `1`'s at the clocks `7 … 13`, with the gap at offset `23` where process
`0` publishes. -/

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
theorem sevent_mid0 (k j : Nat) (h16 : 16 ≤ j) (h22 : j ≤ 22) :
    gcaEventH obj (sstate obj op) sactor (j + 38 * k) = some (k + 1, sact j) :=
  gcaEventH_spec obj (sactor_at k j (by omega)) (sround_mid0 obj op k j h16 h22)

omit [DecidableEq Op] in
theorem sevent_mid1 (k j : Nat) (h24 : 24 ≤ j) (h30 : j ≤ 30) :
    gcaEventH obj (sstate obj op) sactor (j + 38 * k) = some (k + 1, sact j) :=
  gcaEventH_spec obj (sactor_at k j (by omega)) (sround_mid1 obj op k j h24 h30)

omit [DecidableEq Op] in
theorem sevent_none (k j : Nat) (hj : j < 38)
    (h : ¬ ((16 ≤ j ∧ j ≤ 22) ∨ (24 ≤ j ∧ j ≤ 30))) :
    gcaEventH obj (sstate obj op) sactor (j + 38 * k) = none := by
  simp [gcaEventH, sactor_at k j hj, sround_none obj op k j hj h]

omit [DecidableEq Op] in
theorem sevent_ne (k : Nat) : ∀ t, t < 16 + 38 * k →
    ∀ p, gcaEventH obj (sstate obj op) sactor t ≠ some (k + 1, p) := by
  intro t ht p hp
  obtain ⟨k', j, hj, rfl⟩ : ∃ k' j, j < 38 ∧ t = j + 38 * k' :=
    ⟨t / 38, t % 38, Nat.mod_lt _ (by omega), (Nat.mod_add_div t 38).symm⟩
  by_cases hmid : (16 ≤ j ∧ j ≤ 22) ∨ (24 ≤ j ∧ j ≤ 30)
  · have hev : gcaEventH obj (sstate obj op) sactor (j + 38 * k') = some (k' + 1, sact j) := by
      rcases hmid with hm | hm
      · exact sevent_mid0 obj op k' j hm.1 hm.2
      · exact sevent_mid1 obj op k' j hm.1 hm.2
    rw [hev] at hp
    have hk : k' + 1 = k + 1 := congrArg Prod.fst (Option.some.inj hp)
    omega
  · rw [sevent_none obj op k' j hj hmid] at hp; simp at hp

omit [DecidableEq Op] in
theorem sclock_zero (k : Nat) : ∀ t, t ≤ 16 + 38 * k →
    gcaClockH obj (sstate obj op) sactor t (k + 1) = 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      rw [clockH_succ_ne obj (sevent_ne obj op k t (by omega))]
      exact ih (by omega)

omit [DecidableEq Op] in
/-- Process `0`'s seven events take the round clock from `0` to `7`. -/
theorem sclock_a (k : Nat) : ∀ i, i ≤ 7 →
    gcaClockH obj (sstate obj op) sactor ((16 + i) + 38 * k) (k + 1) = i := by
  intro i
  induction i with
  | zero => intro _; exact sclock_zero obj op k _ (by omega)
  | succ i ih =>
      intro hi
      rw [show (16 + (i + 1)) + 38 * k = ((16 + i) + 38 * k) + 1 from by omega,
        clockH_succ_eq obj (sevent_mid0 obj op k (16 + i) (by omega) (by omega)),
        ih (by omega)]

omit [DecidableEq Op] in
/-- Offset `23` — process `0`'s publication — contributes no event. -/
theorem sclock_gap (k : Nat) :
    gcaClockH obj (sstate obj op) sactor (24 + 38 * k) (k + 1) = 7 := by
  rw [show 24 + 38 * k = (23 + 38 * k) + 1 from by omega,
    clockH_succ_ne obj (fun p => by
      rw [sevent_none obj op k 23 (by omega) (by omega)]; simp),
    show 23 + 38 * k = (16 + 7) + 38 * k from by omega]
  exact sclock_a obj op k 7 (by omega)

omit [DecidableEq Op] in
/-- Process `1`'s seven events take the round clock from `7` to `14`. -/
theorem sclock_b (k : Nat) : ∀ i, i ≤ 7 →
    gcaClockH obj (sstate obj op) sactor ((24 + i) + 38 * k) (k + 1) = 7 + i := by
  intro i
  induction i with
  | zero => intro _; exact sclock_gap obj op k
  | succ i ih =>
      intro hi
      rw [show (24 + (i + 1)) + 38 * k = ((24 + i) + 38 * k) + 1 from by omega,
        clockH_succ_eq obj (sevent_mid1 obj op k (24 + i) (by omega) (by omega)),
        ih (by omega)]
      omega

omit [DecidableEq Op] in
theorem sclock_recv0 (k : Nat) :
    gcaClockH obj (sstate obj op) sactor (22 + 38 * k) (k + 1) = 6 := by
  rw [show 22 + 38 * k = (16 + 6) + 38 * k from by omega]
  exact sclock_a obj op k 6 (by omega)

omit [DecidableEq Op] in
theorem sclock_recv1 (k : Nat) :
    gcaClockH obj (sstate obj op) sactor (30 + 38 * k) (k + 1) = 13 := by
  rw [show 30 + 38 * k = (24 + 6) + 38 * k from by omega]
  exact sclock_b obj op k 6 (by omega)

/-! ### The protocol advances one stage per event, for each caller in turn -/

omit [DecidableEq Op] in
theorem sprotocol_actor_lo (r c : Nat) (hr : r ≠ 0) (hc : c < 7) :
    ((sfam obj op).protocol r).actor c = some 0 := sactorAt_lo r c hr hc

omit [DecidableEq Op] in
theorem sprotocol_actor_hi (r c : Nat) (hr : r ≠ 0) (h7 : 7 ≤ c) (h14 : c < 14) :
    ((sfam obj op).protocol r).actor c = some 1 := sactorAt_hi r c hr h7 h14

omit [DecidableEq Op] in
theorem sprotocol_phase0 (r : Nat) (hr : r ≠ 0) : ∀ c, c ≤ 6 →
    ((sfam obj op).protocol r).phase c 0 = c := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
      intro hc
      have hstep : ((sfam obj op).protocol r).phase (c + 1) 0
          = GCA.Protocol.advance (((sfam obj op).protocol r).phase c 0) true := by
        rw [GCA.Protocol.phase, sprotocol_actor_lo obj op r c hr (by omega), ite_eq_left rfl]
        rfl
      rw [hstep, ih (by omega)]
      show GCA.Protocol.advance c true = c + 1
      simp [GCA.Protocol.advance]
      omega

omit [DecidableEq Op] in
theorem sprotocol_phase1_lo (r : Nat) (hr : r ≠ 0) : ∀ c, c ≤ 7 →
    ((sfam obj op).protocol r).phase c 1 = 0 := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ c ih =>
      intro hc
      have hne : ¬ (((sfam obj op).protocol r).actor c = some 1) := by
        rw [sprotocol_actor_lo obj op r c hr (by omega)]
        exact fun h => absurd (Option.some.inj h) (by decide)
      rw [GCA.Protocol.phase, ite_eq_right hne]
      exact ih (by omega)

omit [DecidableEq Op] in
theorem sprotocol_phase1 (r : Nat) (hr : r ≠ 0) : ∀ i, i ≤ 6 →
    ((sfam obj op).protocol r).phase (7 + i) 1 = i := by
  intro i
  induction i with
  | zero => intro _; exact sprotocol_phase1_lo obj op r hr 7 (by omega)
  | succ i ih =>
      intro hi
      have hstep : ((sfam obj op).protocol r).phase (7 + i + 1) 1
          = GCA.Protocol.advance (((sfam obj op).protocol r).phase (7 + i) 1) true := by
        rw [GCA.Protocol.phase, sprotocol_actor_hi obj op r (7 + i) hr (by omega) (by omega),
          ite_eq_left rfl]
        rfl
      rw [show 7 + (i + 1) = 7 + i + 1 from by omega, hstep, ih (by omega)]
      show GCA.Protocol.advance i true = i + 1
      simp [GCA.Protocol.advance]
      omega

/-! ### The global schedule -/

/-- **An infinite run of Algorithm 3 in which every round has two callers.**
The two processes run in lockstep; in cycle `k` both propose the same trace to
round `k + 1`, take their protocol events in turn on the round's shared clock,
and both receive the commit. -/
noncomputable def ssched : Helping obj (sfam obj op) where
  run := srun obj op
  actor := sactor
  step_actor := by
    intro t
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 38 ∧ t = j + 38 * k :=
      ⟨t / 38, t % 38, Nat.mod_lt _ (by omega), (Nat.mod_add_div t 38).symm⟩
    by_cases hst : (16 ≤ j ∧ j ≤ 21) ∨ (24 ≤ j ∧ j ≤ 29)
    · refine Or.inr (Or.inr ⟨sact j, k + 1, sactor_at k j hj, ?_,
        sstutter_at obj op k j hst⟩)
      rcases hst with hm | hm
      · exact sround_mid0 obj op k j hm.1 (by omega)
      · exact sround_mid1 obj op k j hm.1 (by omega)
    · exact Or.inr (Or.inl ⟨sact j, sactor_at k j hj, sstep_at obj op k j hj hst,
        sother_at obj op k j hj⟩)
  gca_actor := by
    intro t p r hact hr
    rw [srun_state] at hr
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 38 ∧ t = j + 38 * k :=
      ⟨t / 38, t % 38, Nat.mod_lt _ (by omega), (Nat.mod_add_div t 38).symm⟩
    have hp : p = sact j := (Option.some.inj ((sactor_at k j hj).symm.trans hact)).symm
    subst hp
    by_cases hmid : 16 ≤ j ∧ j ≤ 22
    · have hrk : r = k + 1 :=
        (Option.some.inj ((sround_mid0 obj op k j hmid.1 hmid.2).symm.trans hr)).symm
      subst r
      rw [srun_state, show j + 38 * k = (16 + (j - 16)) + 38 * k from by omega,
        sclock_a obj op k (j - 16) (by omega), sact_zero j hmid.1 (by omega)]
      exact sprotocol_actor_lo obj op (k + 1) (j - 16) (by omega) (by omega)
    · by_cases hmid' : 24 ≤ j ∧ j ≤ 30
      · have hrk : r = k + 1 :=
          (Option.some.inj ((sround_mid1 obj op k j hmid'.1 hmid'.2).symm.trans hr)).symm
        subst r
        rw [srun_state, show j + 38 * k = (24 + (j - 24)) + 38 * k from by omega,
          sclock_b obj op k (j - 24) (by omega), sact_one j hmid'.1 (by omega)]
        exact sprotocol_actor_hi obj op (k + 1) (7 + (j - 24)) (by omega) (by omega) (by omega)
      · rw [sround_none obj op k j hj (fun hh => hh.elim hmid hmid')] at hr
        exact absurd hr (by simp)
  no_ghost := by
    intro r p s hi
    rcases WitnessC.fin2 p with rfl | rfl
    · refine ⟨10 + 38 * r, str obj op (r + 1), ?_⟩
      show (⟨r + 1, 0, str obj op (r + 1)⟩ : Call (n := 2) obj)
        ∈ (sstate obj op (10 + 38 * r)).calls
      rw [sstate_at obj op r 10 (by omega)]
      show _ ∈ scallsM obj op (r + 1 - 1)
      exact List.mem_cons_self ..
    · refine ⟨16 + 38 * r, str obj op (r + 1), ?_⟩
      show (⟨r + 1, 1, str obj op (r + 1)⟩ : Call (n := 2) obj)
        ∈ (sstate obj op (16 + 38 * r)).calls
      rw [sstate_at obj op r 16 (by omega)]
      show _ ∈ scalls obj op (r + 1)
      exact List.mem_cons_self ..
  receive_ready := by
    intro t p r hr hchange
    rw [srun_state] at hr hchange
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 38 ∧ t = j + 38 * k :=
      ⟨t / 38, t % 38, Nat.mod_lt _ (by omega), (Nat.mod_add_div t 38).symm⟩
    by_cases hp : p = sact j
    · subst hp
      by_cases hmid : 16 ≤ j ∧ j ≤ 22
      · have hrk : r = k + 1 :=
          (Option.some.inj ((sround_mid0 obj op k j hmid.1 hmid.2).symm.trans hr)).symm
        subst r
        have hj22 : j = 22 := by
          apply Classical.byContradiction
          intro hne
          exact hchange (congrArg (fun c => c.localState (sact j))
            (sstutter_at obj op k j (Or.inl ⟨hmid.1, by omega⟩)))
        subst j
        rw [srun_state, sclock_recv0 obj op k, sact_zero 22 (by omega) (by omega)]
        exact sprotocol_phase0 obj op (k + 1) (by omega) 6 (by omega)
      · by_cases hmid' : 24 ≤ j ∧ j ≤ 30
        · have hrk : r = k + 1 :=
            (Option.some.inj ((sround_mid1 obj op k j hmid'.1 hmid'.2).symm.trans hr)).symm
          subst r
          have hj30 : j = 30 := by
            apply Classical.byContradiction
            intro hne
            exact hchange (congrArg (fun c => c.localState (sact j))
              (sstutter_at obj op k j (Or.inr ⟨hmid'.1, by omega⟩)))
          subst j
          rw [srun_state, sclock_recv1 obj op k, sact_one 30 (by omega) (by omega)]
          exact sprotocol_phase1 obj op (k + 1) (by omega) 6 (by omega)
        · rw [sround_none obj op k j hj (fun hh => hh.elim hmid hmid')] at hr
          exact absurd hr (by simp)
    · exact absurd (sother_at obj op k j hj p hp) hchange

theorem ssched_state (t : Nat) : (ssched obj op).run.state t = sstate obj op t := rfl

theorem ssched_actor (t : Nat) : (ssched obj op).actor t = sactor t := rfl

theorem ssched_state_fun : (ssched obj op).run.state = sstate obj op := rfl

theorem ssched_actor_fun : (ssched obj op).actor = sactor := rfl

/-- **Fairness.**  Each caller takes its `receive` exactly when its own share of
the round's projected clock shows the last stage: process `0` at offset `22`,
process `1` at offset `30`. -/
theorem ssched_fair : (ssched obj op).Fair := by
  intro t p cmd r proposal hact hl hphase _
  rw [ssched_state] at hl
  rw [ssched_actor] at hact
  obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 38 ∧ t = j + 38 * k :=
    ⟨t / 38, t % 38, Nat.mod_lt _ (by omega), (Nat.mod_add_div t 38).symm⟩
  have hp : p = sact j := (Option.some.inj ((sactor_at k j hj).symm.trans hact)).symm
  subst hp
  have hround : helpingRound obj
      ((sstate obj op (j + 38 * k)).localState (sact j)) = some r := by rw [hl]; rfl
  rw [ssched_state_fun, ssched_actor_fun] at hphase
  by_cases hmid : 16 ≤ j ∧ j ≤ 22
  · have hrk : r = k + 1 :=
      (Option.some.inj ((sround_mid0 obj op k j hmid.1 hmid.2).symm.trans hround)).symm
    subst r
    have hj22 : j = 22 := by
      apply Classical.byContradiction
      intro hne
      rw [show j + 38 * k = (16 + (j - 16)) + 38 * k from by omega,
        sclock_a obj op k (j - 16) (by omega), sact_zero j hmid.1 (by omega),
        sprotocol_phase0 obj op (k + 1) (by omega) (j - 16) (by omega)] at hphase
      omega
    subst j
    exact ⟨sstep_at obj op k 22 (by omega) (by omega), sother_at obj op k 22 (by omega)⟩
  · by_cases hmid' : 24 ≤ j ∧ j ≤ 30
    · have hrk : r = k + 1 :=
        (Option.some.inj ((sround_mid1 obj op k j hmid'.1 hmid'.2).symm.trans hround)).symm
      subst r
      have hj30 : j = 30 := by
        apply Classical.byContradiction
        intro hne
        rw [show j + 38 * k = (24 + (j - 24)) + 38 * k from by omega,
          sclock_b obj op k (j - 24) (by omega), sact_one j hmid'.1 (by omega),
          sprotocol_phase1 obj op (k + 1) (by omega) (j - 24) (by omega)] at hphase
        omega
      subst j
      exact ⟨sstep_at obj op k 30 (by omega) (by omega), sother_at obj op k 30 (by omega)⟩
    · rw [sround_none obj op k j hj (fun hh => hh.elim hmid hmid')] at hround
      exact absurd hround (by simp)

/-- **Operation liveness.**  Process `1` holds a command at offset `10` of every
cycle. -/
theorem ssched_opLive : (ssched obj op).OpLive := by
  intro N
  refine ⟨9 + 38 * N, by omega, ?_⟩
  have h : (ssched obj op).opActor (9 + 38 * N) = some (scmd op 1 N) := by
    show (match sactor (9 + 38 * N + 1) with
      | none => none
      | some p => (HelpingUniversal.ledger obj
          (sstate obj op (9 + 38 * N + 1))).active p) = _
    rw [show 9 + 38 * N + 1 = 10 + 38 * N from by omega, sactor_at N 10 (by omega)]
    show ((sstate obj op (10 + 38 * N)).localState (sact 10)).command obj = _
    rw [sstate_at obj op N 10 (by omega)]
    rfl
  rw [h]
  rfl

/-! ### What the witness exhibits -/

omit [DecidableEq Op] in
theorem scmd_mem_sinv (q : Fin 2) (k : Nat) : scmd op q k ∈ sinv op (k + 1) := by
  rcases WitnessC.fin2 q with rfl | rfl
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · exact List.mem_cons_self ..

omit [DecidableEq Op] in
theorem srets_command : ∀ k, ∀ ret ∈ srets obj op k,
    ∃ (q : Fin 2) (j : Nat), j < k ∧ ret.command = scmd op q j
  | 0 => by intro ret h; simp [srets] at h
  | (k + 1) => by
      intro ret h
      rcases List.mem_cons.mp h with rfl | hm
      · exact ⟨1, k, by omega, rfl⟩
      · rcases List.mem_cons.mp hm with rfl | hm'
        · exact ⟨0, k, by omega, rfl⟩
        · obtain ⟨q, j, hj, he⟩ := srets_command k ret hm'
          exact ⟨q, j, by omega, he⟩

theorem sstate_sixteen (k : Nat) :
    (srun obj op).state (16 + 38 * k) = b16 obj op k := by
  show sstate obj op (16 + 38 * k) = _
  rw [sstate_at obj op k 16 (by omega)]
  rfl

/-- **Both processes are inside the same GCA round, with the same proposal.**
At offset `16` of cycle `k` the two callers are blocked in round `k + 1` on the
identical trace, both commands are invoked and neither has a response. -/
theorem shared_round (k : Nat) :
    ((srun obj op).state (16 + 38 * k)).localState 0
        = .waiting (scmd op 0 k) (k + 1) (str obj op (k + 1)) ∧
    ((srun obj op).state (16 + 38 * k)).localState 1
        = .waiting (scmd op 1 k) (k + 1) (str obj op (k + 1)) ∧
    (scmd op 0 k ∈ ((srun obj op).state (16 + 38 * k)).invocations ∧
      scmd op 1 k ∈ ((srun obj op).state (16 + 38 * k)).invocations) ∧
    (∀ ret ∈ ((srun obj op).state (16 + 38 * k)).returns,
        ret.command ≠ scmd op 0 k ∧ ret.command ≠ scmd op 1 k) ∧
    scmd op 0 k ≠ scmd op 1 k := by
  rw [sstate_sixteen]
  refine ⟨b16_local0 obj op k, b16_local1 obj op k, ⟨?_, ?_⟩, ?_,
    scmd_zero_ne_one op k k⟩
  · rw [b16_inv]; exact scmd_mem_sinv op 0 k
  · rw [b16_inv]; exact scmd_mem_sinv op 1 k
  · intro ret hret
    rw [show (b16 obj op k).returns = srets obj op k from rfl] at hret
    obtain ⟨q, j, hj, he⟩ := srets_command obj op k ret hret
    constructor <;> rw [he] <;> rw [Ne, scmd_eq_iff] <;>
      exact fun hcon => absurd hcon.2 (by omega)

/-- **Round `k + 1` has two participants, both of which commit.**  Their inputs
agree, so GCA Weak Agreement forces both returns to be commits and Common
Prefix with Validity forces the returned trace to be the common input. -/
theorem round_commits_both (k : Nat) :
    ((sfam obj op).protocol (k + 1)).participants = [0, 1] ∧
    (((sfam obj op).environment obj (k + 1)).input 0 = some (str obj op (k + 1)) ∧
      ((sfam obj op).environment obj (k + 1)).input 1 = some (str obj op (k + 1))) ∧
    (((sfam obj op).environment obj (k + 1)).output 0 = some (str obj op (k + 1), true) ∧
      ((sfam obj op).environment obj (k + 1)).output 1 = some (str obj op (k + 1), true)) ∧
    (0 < (Tagged (n := 2) obj).traceCount (scmd op 0 k) (str obj op (k + 1)) ∧
      0 < (Tagged (n := 2) obj).traceCount (scmd op 1 k) (str obj op (k + 1))) := by
  refine ⟨sfam_participants obj op (k + 1) (by omega),
    ⟨sfam_input obj op (k + 1) (by omega) 0, sfam_input obj op (k + 1) (by omega) 1⟩,
    ⟨sfam_output obj op (k + 1) (by omega) 0, sfam_output obj op (k + 1) (by omega) 1⟩,
    ?_, ?_⟩
  · rw [traceCount_str]; simp
  · rw [traceCount_str]; simp

end ConflictFreedom.GlobalSchedule.WitnessS

namespace ConflictFreedom
variable {State Op Response : Type} [DecidableEq Op]

/-- **The admitted set of Algorithm 3 contains a run whose every GCA round has
two participants.**  `algorithm3_nonempty_contended` already exhibits two
operations in flight, but there the stalled process never calls the GCA; here
both processes call *the same round* with the same proposal, and both commit. -/
theorem algorithm3_nonempty_sharedRound (obj : Object State Op Response) (op : Op) :
    ∃ e, algorithm3 obj 2 e :=
  ⟨_, GlobalSchedule.WitnessS.sfam obj op, GlobalSchedule.WitnessS.ssched obj op,
    GlobalSchedule.WitnessS.ssched_opLive obj op,
    GlobalSchedule.WitnessS.ssched_fair obj op,
    GlobalSchedule.WitnessS.sfam_waitFree obj op, rfl⟩

/-- **Algorithm 3's admitted set contains an execution with two instances
concurrently pending *inside the same GCA round*.**  The two callers hand round
`k + 1` the identical proposal, so the round's Weak Agreement, Common Prefix and
Validity properties are exercised against a second real participant rather than
against a lone caller. -/
theorem algorithm3_sharedRound (obj : Object State Op Response) (op : Op) :
    ∃ e : Execution 2 Op, algorithm3 obj 2 e ∧
      ∃ (i j : e.Instance) (t : Nat), i ≠ j ∧ e.Pending i t ∧ e.Pending j t := by
  classical
  have hp := GlobalSchedule.WitnessS.ssched_opLive obj op
  obtain ⟨-, -, ⟨hw, ho⟩, hret, hne⟩ := GlobalSchedule.WitnessS.shared_round obj op 0
  have hmem : ∀ a : WeakUniversal.Cmd 2 Op,
      a ∈ ((GlobalSchedule.WitnessS.srun obj op).state (16 + 38 * 0)).invocations →
      a ∈ (InvocationLedger.obs
        ((GlobalSchedule.WitnessS.ssched obj op).run.ledgerRun obj) 15).invoked := by
    intro a ha
    show a ∈ ((GlobalSchedule.WitnessS.ssched obj op).run.state (15 + 1)).invocations
    exact ha
  have hnotret : ∀ a : WeakUniversal.Cmd 2 Op,
      (∀ ret ∈ ((GlobalSchedule.WitnessS.srun obj op).state (16 + 38 * 0)).returns,
        ret.command ≠ a) →
      a ∉ (InvocationLedger.obs
        ((GlobalSchedule.WitnessS.ssched obj op).run.ledgerRun obj) 15).returned := by
    intro a ha hm
    obtain ⟨ret, hret', he⟩ := List.mem_map.mp hm
    exact ha ret hret' he
  refine ⟨(GlobalSchedule.WitnessS.ssched obj op).execution hp,
    ⟨_, GlobalSchedule.WitnessS.ssched obj op, hp,
      GlobalSchedule.WitnessS.ssched_fair obj op,
      GlobalSchedule.WitnessS.sfam_waitFree obj op, rfl⟩, ?_⟩
  refine ⟨⟨GlobalSchedule.WitnessS.scmd op 0 0, ⟨15, hmem _ hw⟩⟩,
    ⟨GlobalSchedule.WitnessS.scmd op 1 0, ⟨15, hmem _ ho⟩⟩, 15,
    fun h => hne (congrArg Subtype.val h), ?_, ?_⟩
  · exact ((_ : InvocationLedger.Schedule _).execution_pending_iff _ 15).mpr
      ⟨hmem _ hw, hnotret _ (fun ret hr => (hret ret hr).1)⟩
  · exact ((_ : InvocationLedger.Schedule _).execution_pending_iff _ 15).mpr
      ⟨hmem _ ho, hnotret _ (fun ret hr => (hret ret hr).2)⟩

end ConflictFreedom
