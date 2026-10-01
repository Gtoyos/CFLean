import CFLeanProof.CausalLinearization
import CFLeanProof.UniversalEventLinearization

/-! A completed operation in the synchronized scheduler. Unlike an idle or
permanently waiting witness, this run exercises the receive-readiness rule,
publication, response recording, and the resulting linearization theorem. -/
namespace ConflictFreedom.GlobalSchedule.Witness
open WeakUniversal
open UniversalProtocol
variable {State Op Response : Type} (obj : Object State Op Response) [DecidableEq Op] (op : Op)

/-- The one-participant protocol really returns its input and commits. -/
theorem wfam_output :
    ((wfam obj op).environment obj 1).output 0 = some (wprop obj op, true) := by
  have hw : ((wfam obj op).protocol 1).SnapshotWaitFree :=
    GCA.Protocol.alwaysAcknowledged_waitFree _ (fun _ => rfl)
  have hinf : ((wfam obj op).protocol 1).InfiniteSteps 0 := fun N => ⟨N, Nat.le_refl _, rfl⟩
  obtain ⟨s, flag, ho⟩ := ((wfam obj op).protocol 1).returned_of_infiniteSteps hw hinf
  have huniform : ∀ u, (((wfam obj op).environment obj 1).Inputs u) → u = wprop obj op := by
    intro u ⟨p, hp⟩
    have he : p = 0 := Subsingleton.elim _ _
    subst p
    exact (Option.some.inj ((wfam_input obj op).symm.trans hp)).symm
  obtain ⟨rfl, rfl⟩ := (((wfam obj op).environment obj 1).uniform_return
    ((wfam obj op).specification obj 1) huniform ho)
  exact ho

noncomputable def w5 : Configuration (n := 1) obj :=
  { w4 obj op with
    localState :=
      update (w4 obj op).localState 0 (.publishing (wcmd op) 1 (wprop obj op)) }

noncomputable def w6 : Configuration (n := 1) obj :=
  { w5 obj op with
    localState :=
      update (w5 obj op).localState 0 (.returning (wcmd op) 1 (wprop obj op))
    slots := update (w5 obj op).slots 0 ⟨1, wprop obj op⟩ }

noncomputable def w7 : Configuration (n := 1) obj :=
  { w6 obj op with
    localState := update (w6 obj op).localState 0 .idle
    returns := (⟨wcmd op, 1, wprop obj op⟩ : Return obj) :: (w6 obj op).returns }

/-! ### Local states along the run -/

omit [DecidableEq Op] in
theorem w0_localState : (w0 obj).localState 0 = .idle := rfl

omit [DecidableEq Op] in
theorem w1_localState :
    (w1 obj op).localState 0 = .collecting (wcmd op) (List.finRange 1) (zeroSeed obj) := by
  rw [w1]; rfl

omit [DecidableEq Op] in
theorem w2_localState :
    (w2 obj op).localState 0 = .collecting (wcmd op) [] (wseed obj op) := by
  rw [w2]; rfl

omit [DecidableEq Op] in
theorem w3_localState : (w3 obj op).localState 0 = .ready (wcmd op) (wseed obj op) := by
  rw [w3]; rfl

theorem w4_localState :
    (w4 obj op).localState 0 = .waiting (wcmd op) 1 (wprop obj op) := by
  rw [w4, wseed_eq]; rfl

theorem w5_localState :
    (w5 obj op).localState 0 = .publishing (wcmd op) 1 (wprop obj op) := by
  rw [w5]; rfl

theorem w6_localState :
    (w6 obj op).localState 0 = .returning (wcmd op) 1 (wprop obj op) := by
  rw [w6]; rfl

theorem w7_localState : (w7 obj op).localState 0 = .idle := by
  rw [w7]; rfl

private theorem receive_step :
    Step obj ((wfam obj op).environment obj) (w4 obj op) (w5 obj op) := by
  have h := Step.receive (w4 obj op) 0 (wcmd op) 1 (wprop obj op) (wprop obj op) true
    (w4_localState obj op) (wfam_output obj op)
  have hc : 0 < (Tg obj).traceCount (wcmd op) (wprop obj op) :=
    (Tg obj).appendMissing_contains _ _
  simpa only [w5, hc, and_self, ite_true] using h

/-! ### The completed run

`wrun` stops at `w4`, blocked in the GCA call.  Here the call is given the six
protocol events it needs (global times 4 to 9), and the program then receives
the committed output, publishes it and returns. -/

/-- Six actual protocol events occur at global times 4 through 9. -/
noncomputable def completedState (t : Nat) : Configuration (n := 1) obj :=
  if t ≤ 10 then wstate obj op t else if t = 11 then w5 obj op
  else if t = 12 then w6 obj op else w7 obj op

theorem completedState_le (t : Nat) (ht : t ≤ 10) :
    completedState obj op t = wstate obj op t := by
  unfold completedState
  rw [ite_eq_left ht]

theorem completedState_eleven : completedState obj op 11 = w5 obj op := by
  unfold completedState
  rw [ite_eq_right (by omega), ite_eq_left rfl]

theorem completedState_twelve : completedState obj op 12 = w6 obj op := by
  unfold completedState
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

theorem completedState_ge (t : Nat) (ht : 13 ≤ t) :
    completedState obj op t = w7 obj op := by
  unfold completedState
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The program step taken at every global time that is not one of the six
protocol events. -/
private theorem step_at (t : Nat) (h12 : t ≤ 12) (hmid : ¬ (4 ≤ t ∧ t ≤ 9)) :
    Step obj ((wfam obj op).environment obj) (completedState obj op t)
      (completedState obj op (t + 1)) := by
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 10 ∨ t = 11 ∨ t = 12 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [completedState_le obj op 0 (by omega), completedState_le obj op 1 (by omega)]
    exact Step.invoke (w0 obj) 0 op rfl (List.finRange 1) (List.Perm.refl _)
  · rw [completedState_le obj op 1 (by omega), completedState_le obj op 2 (by omega)]
    exact Step.read (w1 obj op) 0 0 (wcmd op) [] (zeroSeed obj) rfl
  · rw [completedState_le obj op 2 (by omega), completedState_le obj op 3 (by omega)]
    exact Step.collected (w2 obj op) 0 (wcmd op) (wseed obj op) rfl
  · rw [completedState_le obj op 3 (by omega), completedState_le obj op 4 (by omega)]
    exact Step.propose (w3 obj op) 0 (wcmd op) (wseed obj op) rfl
      (by rw [wseed_eq]; exact wfam_input obj op)
  · rw [completedState_le obj op 10 (by omega), completedState_eleven obj op,
      wstate_ge obj op 10 (by omega)]
    exact receive_step obj op
  · rw [completedState_eleven obj op, completedState_twelve obj op]
    exact Step.publish (w5 obj op) 0 (wcmd op) 1 (wprop obj op) (w5_localState obj op)
  · rw [completedState_twelve obj op, completedState_ge obj op 13 (by omega)]
    exact Step.finish (w6 obj op) 0 (wcmd op) 1 (wprop obj op) (w6_localState obj op)

private theorem completedState_next (t : Nat) :
    completedState obj op (t + 1) = completedState obj op t ∨
    Step obj ((wfam obj op).environment obj) (completedState obj op t)
      (completedState obj op (t + 1)) := by
  by_cases h12 : t ≤ 12
  · by_cases hmid : 4 ≤ t ∧ t ≤ 9
    · refine Or.inl ?_
      rw [completedState_le obj op (t + 1) (by omega), completedState_le obj op t (by omega),
        wstate_ge obj op (t + 1) (by omega), wstate_ge obj op t hmid.1]
    · exact Or.inr (step_at obj op t h12 hmid)
  · refine Or.inl ?_
    rw [completedState_ge obj op (t + 1) (by omega), completedState_ge obj op t (by omega)]

noncomputable def completedRun :
    WeakUniversal.Execution obj ((wfam obj op).environment obj) where
  state := completedState obj op
  initial_state := rfl
  next := completedState_next obj op

/-- The lone process is scheduled until it returns. -/
def completedActor : Nat → Option (Fin 1) := fun t => if t ≤ 12 then some 0 else none

theorem completedActor_le {t : Nat} (h : t ≤ 12) : completedActor t = some 0 := by
  unfold completedActor
  rw [ite_eq_left h]

theorem completedActor_gt {t : Nat} (h : ¬ t ≤ 12) : completedActor t = none := by
  unfold completedActor
  rw [ite_eq_right h]

/-- The process is blocked in round 1 exactly from the proposal until the
receive step. -/
theorem completed_round {t : Nat} (h4 : 4 ≤ t) (h10 : t ≤ 10) :
    weakRound obj ((completedState obj op t).localState 0) = some 1 := by
  rw [completedState_le obj op t h10, wstate_ge obj op t h4, w4_localState]
  rfl

private theorem completed_waiting {t r : Nat} {p : Fin 1}
    (hr : weakRound obj ((completedState obj op t).localState p) = some r) :
    4 ≤ t ∧ t ≤ 10 ∧ r = 1 := by
  have hp : p = 0 := Subsingleton.elim _ _
  subst p
  by_cases ht : t ≤ 10
  · have ht4 : 4 ≤ t := by
      rcases Nat.lt_or_ge t 4 with hlt | hge
      · exfalso
        have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases hcases with rfl | rfl | rfl | rfl <;>
          rw [completedState_le obj op _ (by omega)] at hr
        · rw [show wstate obj op 0 = w0 obj from rfl, w0_localState] at hr; cases hr
        · rw [show wstate obj op 1 = w1 obj op from rfl, w1_localState] at hr; cases hr
        · rw [show wstate obj op 2 = w2 obj op from rfl, w2_localState] at hr; cases hr
        · rw [show wstate obj op 3 = w3 obj op from rfl, w3_localState] at hr; cases hr
      · exact hge
    rw [completed_round obj op ht4 ht] at hr
    exact ⟨ht4, ht, (Option.some.inj hr).symm⟩
  · exfalso
    rcases Nat.lt_or_ge t 12 with h11 | h12
    · rw [show t = 11 by omega, completedState_eleven obj op, w5_localState] at hr
      cases hr
    · rcases Nat.lt_or_ge t 13 with h12' | h13
      · rw [show t = 12 by omega, completedState_twelve obj op, w6_localState] at hr
        cases hr
      · rw [completedState_ge obj op t h13, w7_localState] at hr
        cases hr

/-! ### The round-1 clock reaches the last protocol stage -/

theorem completedEvent_none {t : Nat} (h : t ≤ 3) :
    gcaEvent obj (completedState obj op) completedActor t = none := by
  have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  have hact : completedActor t = some 0 := completedActor_le (by omega)
  have hround : weakRound obj ((completedState obj op t).localState 0) = none := by
    rcases hcases with rfl | rfl | rfl | rfl <;>
      rw [completedState_le obj op _ (by omega)]
    · rw [show wstate obj op 0 = w0 obj from rfl, w0_localState]; rfl
    · rw [show wstate obj op 1 = w1 obj op from rfl, w1_localState]; rfl
    · rw [show wstate obj op 2 = w2 obj op from rfl, w2_localState]; rfl
    · rw [show wstate obj op 3 = w3 obj op from rfl, w3_localState]; rfl
  cases hev : gcaEvent obj (completedState obj op) completedActor t with
  | none => rfl
  | some rp =>
      obtain ⟨r', p'⟩ := rp
      obtain ⟨h1, h2⟩ := gcaEvent_inv obj hev
      have hp : p' = 0 := Subsingleton.elim _ _
      subst p'
      rw [hround] at h2
      cases h2

theorem completedEvent_some {t : Nat} (h4 : 4 ≤ t) (h10 : t ≤ 10) :
    gcaEvent obj (completedState obj op) completedActor t = some (1, 0) :=
  gcaEvent_spec obj (completedActor_le (by omega)) (completed_round obj op h4 h10)

private theorem clock_succ_none {t : Nat}
    (h : gcaEvent obj (completedState obj op) completedActor t = none) :
    gcaClock obj (completedState obj op) completedActor (t + 1) 1 =
      gcaClock obj (completedState obj op) completedActor t 1 := by
  rw [gcaClock, h]

private theorem clock_succ_some {t : Nat}
    (h : gcaEvent obj (completedState obj op) completedActor t = some (1, 0)) :
    gcaClock obj (completedState obj op) completedActor (t + 1) 1 =
      gcaClock obj (completedState obj op) completedActor t 1 + 1 := by
  rw [gcaClock, h]
  rfl

theorem clock_four : gcaClock obj (completedState obj op) completedActor 4 1 = 0 := by
  rw [clock_succ_none obj op (completedEvent_none obj op (by omega : (3:Nat) ≤ 3)),
    clock_succ_none obj op (completedEvent_none obj op (by omega : (2:Nat) ≤ 3)),
    clock_succ_none obj op (completedEvent_none obj op (by omega : (1:Nat) ≤ 3)),
    clock_succ_none obj op (completedEvent_none obj op (by omega : (0:Nat) ≤ 3))]
  rfl

theorem clock_add (k : Nat) (hk : k ≤ 6) :
    gcaClock obj (completedState obj op) completedActor (4 + k) 1 = k := by
  induction k with
  | zero => exact clock_four obj op
  | succ k ih =>
      rw [show 4 + (k + 1) = (4 + k) + 1 from rfl,
        clock_succ_some obj op (completedEvent_some obj op (by omega) (by omega)),
        ih (by omega)]

theorem clock_ten : gcaClock obj (completedState obj op) completedActor 10 1 = 6 :=
  clock_add obj op 6 (by omega)

theorem protocol_actor (t : Nat) : ((wfam obj op).protocol 1).actor t = some 0 := rfl

theorem protocol_ack (t : Nat) : ((wfam obj op).protocol 1).acknowledged t = true := rfl

theorem protocol_phase_succ (t : Nat) :
    ((wfam obj op).protocol 1).phase (t + 1) 0 =
      GCA.Protocol.advance (((wfam obj op).protocol 1).phase t 0) true := by
  rw [GCA.Protocol.phase, protocol_actor, ite_eq_left rfl, protocol_ack]

/-- With an always-acknowledging snapshot interface and a single participant,
the protocol advances one stage per step, so six events reach the last stage. -/
theorem protocol_phase (k : Nat) (hk : k ≤ 6) :
    ((wfam obj op).protocol 1).phase k 0 = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [protocol_phase_succ obj op k, ih (by omega)]
      show GCA.Protocol.advance k true = k + 1
      unfold GCA.Protocol.advance
      rw [ite_eq_left ⟨by omega, Or.inr (Or.inr rfl)⟩]

theorem protocol_phase_six : ((wfam obj op).protocol 1).phase 6 0 = 6 :=
  protocol_phase obj op 6 (by omega)

/-! ### The synchronized schedule -/

/-- A synchronized run that actually completes an operation. -/
noncomputable def completedSchedule : Weak obj (wfam obj op) where
  run := completedRun obj op
  actor := completedActor
  step_actor := by
    intro t
    by_cases h12 : t ≤ 12
    · by_cases hmid : 4 ≤ t ∧ t ≤ 9
      · refine Or.inr (Or.inr ⟨0, 1, completedActor_le h12, ?_, ?_⟩)
        · exact completed_round obj op hmid.1 (by omega)
        · show completedState obj op (t + 1) = completedState obj op t
          rw [completedState_le obj op (t + 1) (by omega), completedState_le obj op t (by omega),
            wstate_ge obj op (t + 1) (by omega), wstate_ge obj op t hmid.1]
      · refine Or.inr (Or.inl ⟨0, completedActor_le h12, step_at obj op t h12 hmid, ?_⟩)
        intro q hq
        exact False.elim (hq (Subsingleton.elim _ _))
    · refine Or.inl ⟨completedActor_gt h12, ?_⟩
      show completedState obj op (t + 1) = completedState obj op t
      rw [completedState_ge obj op (t + 1) (by omega), completedState_ge obj op t (by omega)]
  gca_actor := by
    intro t p r _ hr
    obtain ⟨_, _, rfl⟩ := completed_waiting obj op hr
    have hp : p = 0 := Subsingleton.elim _ _
    subst p
    rfl
  no_ghost := by
    intro r p s hi
    have hp : p = 0 := Subsingleton.elim _ _
    subst p
    by_cases hr : r = 0
    · subst r
      refine ⟨4, wprop obj op, ?_⟩
      show (⟨0 + 1, 0, wprop obj op⟩ : Call obj) ∈ (completedState obj op 4).calls
      rw [completedState_le obj op 4 (by omega), wstate_ge obj op 4 (by omega)]
      have hcalls : (w4 obj op).calls =
          (⟨(wseed obj op).round + 1, 0,
            (Tg obj).appendMissing (wseed obj op).trace (wcmd op)⟩ : Call obj)
            :: (w3 obj op).calls := rfl
      rw [hcalls, wseed_eq]
      exact List.mem_cons_self ..
    · rw [wfam_input_none obj op r (by omega)] at hi
      cases hi
  receive_ready := by
    intro t p r hr hchange
    obtain ⟨hlow, hhigh, rfl⟩ := completed_waiting obj op hr
    have hp : p = 0 := Subsingleton.elim _ _
    subst p
    have ht : t = 10 := by
      rcases Nat.lt_or_ge t 10 with hlt | hge
      · exfalso
        apply hchange
        show (completedState obj op (t + 1)).localState 0 = (completedState obj op t).localState 0
        rw [completedState_le obj op (t + 1) (by omega), completedState_le obj op t (by omega),
          wstate_ge obj op (t + 1) (by omega), wstate_ge obj op t hlow]
      · omega
    subst t
    show ((wfam obj op).protocol 1).phase
      (gcaClock obj (completedState obj op) completedActor 10 1) 0 = 6
    rw [clock_ten obj op]
    exact protocol_phase_six obj op

/-- **The linearizability theorem has content.**  The synchronized scheduler
admits a run with a completed operation, and the finite history of that run has
a linearization containing that operation's command. -/
theorem completed_linearization :
    ∃ x, (Tg obj).Linearizes ((completedSchedule obj op).run.history obj) 13 x ∧
      wcmd op ∈ x := by
  obtain ⟨x, hx⟩ := (completedSchedule obj op).finite_linearization 13
  refine ⟨x, hx, ?_⟩
  have hret : (⟨wcmd op, 1, wprop obj op⟩ : Return obj) ∈
      ((completedSchedule obj op).run.state 13).returns := by
    show (⟨wcmd op, 1, wprop obj op⟩ : Return obj) ∈ (completedState obj op 13).returns
    rw [completedState_ge obj op 13 (by omega)]
    have hreturns : (w7 obj op).returns =
        (⟨wcmd op, 1, wprop obj op⟩ : Return obj) :: (w6 obj op).returns := rfl
    rw [hreturns]
    exact List.mem_cons_self ..
  obtain ⟨v, hv⟩ := response_defined obj
    ((completedSchedule obj op).run.reachable obj 13) hret
  exact (hx.completed (wcmd op) v ⟨_, hret, rfl, hv⟩).1

/-- **The event encoding has content.**  At boundary 13 the synchronized run's
literal event sequence really contains both the invocation and the response of
the completed operation, so the manuscript-form statement
`Weak.event_linearization` is not vacuously about an empty history. -/
theorem completed_event_history :
    ∃ resp : Cmd 1 Op → Response,
      History.Invoked
          ((completedSchedule obj op).run.ledgerRun obj |>.history resp 13) (wcmd op) ∧
      (∃ v, History.Responded
          ((completedSchedule obj op).run.ledgerRun obj |>.history resp 13) (wcmd op) v) ∧
      (Tg obj).EventLinearizable Command.process
          ((completedSchedule obj op).run.ledgerRun obj |>.history resp 13) := by
  obtain ⟨resp, hinv, hres, _, hlin⟩ := (completedSchedule obj op).event_linearization 13
  have hret : (⟨wcmd op, 1, wprop obj op⟩ : Return obj) ∈
      ((completedSchedule obj op).run.state 13).returns := by
    show (⟨wcmd op, 1, wprop obj op⟩ : Return obj) ∈ (completedState obj op 13).returns
    rw [completedState_ge obj op 13 (by omega)]
    have hreturns : (w7 obj op).returns =
        (⟨wcmd op, 1, wprop obj op⟩ : Return obj) :: (w6 obj op).returns := rfl
    rw [hreturns]
    exact List.mem_cons_self ..
  obtain ⟨v, hv⟩ := response_defined obj
    ((completedSchedule obj op).run.reachable obj 13) hret
  refine ⟨resp, ?_, ⟨v, (hres (wcmd op) v).mpr ⟨_, hret, rfl, hv⟩⟩, hlin⟩
  refine (hinv (wcmd op)).mpr ?_
  obtain ⟨u, hu, hi⟩ :=
    (completedSchedule obj op).run.invoked_strictly_before_return obj ⟨_, hret, rfl⟩
  exact ((completedSchedule obj op).run.ledgerRun obj).invoked_mono
    (by omega : u ≤ 13) hi

end ConflictFreedom.GlobalSchedule.Witness
