import CFLeanProof.Algorithm3OverGCA
import CFLeanProof.DecidableTraceCompute

/-! # The machines, as programs

`ForwardGCA.machine` runs Algorithm 2 with its two local calculations — the
pair `(⊔ A_i^co, A_i = A_i^co)` of lines 3–4 and the output of lines 6–8 — as
classical definitions, in the manuscript's convention that a local computation
is one step (`EffectiveInterface`).  For an object whose independence relation
is decidable, `machineC` computes both with `LocalCompute.ofDecidable`, and it
is the same machine (`machine_eq_machineC`).

So Algorithm 2 is a program, and so are Algorithms 1 and 3 over it: their runs
are the runs of the computed machine (`WeakUniversal.Over.mrun_machineC`,
`HelpingUniversal.Over.mrun_machineC`), which the kernel can evaluate.
`AdoptWitness` evaluates two of them.
-/
namespace ConflictFreedom.ForwardGCA
open Object GCA

variable {S Op R : Type} (O : Object S Op R) (n : Nat) [DecidableEq Op] [DecidableRel O.Independent]

/-- Algorithm 2's step, with the pair of lines 3–4 computed. -/
def gcaStepC (g : GState O n) (p : Fin n) (r : Nat) (v : O.Trace) : GState O n :=
  match (g.frame p).phase with
  | 0 => { g with
      A := fupdate g.A r (fupdate (g.A r) p (some v))
      frame := fupdate g.frame p { g.frame p with phase := 1 } }
  | 1 => { g with
      frame := fupdate g.frame p { g.frame p with phase := 2, aSnap := g.A r } }
  | 2 => { g with
      frame := fupdate g.frame p { g.frame p with
        phase := 3
        cand := ((LocalCompute.ofDecidable O).candidate (g.frame p).aTraces,
          (LocalCompute.ofDecidable O).compatible (g.frame p).aTraces) } }
  | 3 => { g with
      B := fupdate g.B r (fupdate (g.B r) p (some (g.frame p).cand))
      frame := fupdate g.frame p { g.frame p with phase := 4 } }
  | 4 => { g with
      frame := fupdate g.frame p { g.frame p with phase := 5, bSnap := g.B r } }
  | 5 => { g with frame := fupdate g.frame p { g.frame p with phase := 6 } }
  | _ => g

theorem gcaStep_eq (g : GState O n) (p : Fin n) (r : Nat) (v : O.Trace) :
    gcaStep O n g p r v = gcaStepC O n g p r v := by
  have hc : O.gcaCandidate (g.frame p).aTraces
      = (LocalCompute.ofDecidable O).candidate (g.frame p).aTraces :=
    ((LocalCompute.ofDecidable O).candidate_eq _).symm
  have hb : @decide (O.Compatible (fun s => s ∈ (g.frame p).aTraces)) (Classical.propDecidable _)
      = (LocalCompute.ofDecidable O).compatible (g.frame p).aTraces := by
    cases h : (LocalCompute.ofDecidable O).compatible (g.frame p).aTraces with
    | true =>
        exact @decide_eq_true _ (Classical.propDecidable _)
          (((LocalCompute.ofDecidable O).compatible_iff _).mp h)
    | false =>
        refine @decide_eq_false _ (Classical.propDecidable _) (fun hcomp => ?_)
        have hy := ((LocalCompute.ofDecidable O).compatible_iff _).mpr hcomp
        rw [h] at hy
        cases hy
  unfold gcaStep gcaStepC
  rw [hc, hb]
  rfl

/-- Line 6, computed: the meet of the flagged candidates, or the caller's own. -/
def frameResultC (fr : Frame O n) : O.Trace :=
  match fr.flagged with
  | [] => fr.cand.1
  | s :: rest => (LocalCompute.ofDecidable O).glb s rest

theorem frameResult_eq (fr : Frame O n) : frameResult O n fr = frameResultC O n fr := by
  unfold frameResult frameResultC
  cases fr.flagged with
  | nil =>
      have hne : ¬ ∃ s, s ∈ ([] : List O.Trace) := by
        rintro ⟨s, hs⟩
        cases hs
      rw [dite_eq_right hne]
  | cons s rest =>
      rw [dite_eq_left ⟨s, List.mem_cons_self ..⟩]
      exact O.glb_unique (O.traceGLB_spec _ _) ((LocalCompute.ofDecidable O).glb_spec s rest)

/-- Lines 7–8, decided. -/
def frameCommitsC (fr : Frame O n) (own : O.Trace) : Bool :=
  decide (((∀ q ∈ fr.aView, (fr.aSnap q).getD O.emptyTrace = own) ∧
      (∀ q ∈ fr.bView, (fr.bEntry q).1 = own)) ∨
    ((∀ q ∈ fr.aView,
        O.TracePrefix ((fr.aSnap q).getD O.emptyTrace) (frameResultC O n fr) → q ∈ fr.bView) ∧
      ∀ q ∈ fr.bView, (fr.bEntry q).2 = true))

/-- What the caller returns, computed. -/
def frameOutputC (fr : Frame O n) (own : O.Trace) : O.Trace × Bool :=
  (frameResultC O n fr, frameCommitsC O n fr own)

theorem frameOutput_eq (fr : Frame O n) (own : O.Trace) :
    frameOutput O n fr own = frameOutputC O n fr own := by
  unfold frameOutput frameOutputC frameCommitsC frameCommits
  rw [frameResult_eq]
  congr 1
  exact decide_eq_decide.mpr Iff.rfl

/-- **Algorithm 2 over atomic snapshots, as a program.** -/
def machineC : GCAMachine O n where
  State := GState O n
  init := GState.initial O n
  step := gcaStepC O n
  output g p _ v := if (g.frame p).phase < 6 then none else some (frameOutputC O n (g.frame p) v)
  leave := resetFrame O n

/-- **It is Algorithm 2**: the computed machine is `machine`. -/
theorem machine_eq_machineC : machine O n = machineC O n := by
  have hs : gcaStep O n = gcaStepC O n := by
    funext g p r v
    exact gcaStep_eq O n g p r v
  have ho : frameOutput O n = frameOutputC O n := by
    funext fr own
    exact frameOutput_eq O n fr own
  unfold machine machineC
  rw [hs, ho]

end ConflictFreedom.ForwardGCA

namespace ConflictFreedom.WeakUniversal.Over
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op] [DecidableRel obj.Independent]

/-- **Algorithm 1 over Algorithm 2 is a program**: the run of Algorithm 1 over
the computed Algorithm 2 is the machine's run, `Forward.frun`. -/
theorem mrun_machineC (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) :
    mrun obj (ForwardGCA.machineC (Tagged (n := n) obj) n) ch client sched =
      Forward.frun obj ch client sched := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [mrun_succ, Forward.frun_succ, ih]
      cases sched t with
      | none => rfl
      | some p =>
          cases hl : (Forward.frun obj ch client sched t).1.localState p with
          | waiting cmd r v =>
              by_cases hph : ((Forward.frun obj ch client sched t).2.frame p).phase < 6
              · rw [Forward.fstep_gca obj ch client _ hl hph, ForwardGCA.gcaStep_eq]
                exact mstep_step obj _ ch client _ hl (ite_eq_left hph)
              · rw [Forward.fstep_recv obj ch client _ hl hph, ForwardGCA.frameOutput_eq]
                exact mstep_ret obj _ ch client _ hl (ite_eq_right hph)
          | _ =>
              rw [Forward.fstep_prog obj ch client _ (by rw [hl]; rfl)]
              exact mstep_prog obj _ ch client _ (by rw [hl]; rfl)

end ConflictFreedom.WeakUniversal.Over

namespace ConflictFreedom.HelpingUniversal.Over
open WeakUniversal (Tagged)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op] [DecidableRel obj.Independent]

/-- **Algorithm 3 over Algorithm 2 is a program**: the run of Algorithm 3 over
the computed Algorithm 2 is the machine's run, `Forward.frun`. -/
theorem mrun_machineC (ch : Forward.Choices (n := n) obj) (client : Fin n → Nat → Op)
    (sched : Nat → Option (Fin n)) :
    mrun obj (ForwardGCA.machineC (Tagged (n := n) obj) n) ch client sched =
      Forward.frun obj ch client sched := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [mrun_succ, Forward.frun_succ, ih]
      cases sched t with
      | none => rfl
      | some p =>
          cases hl : (Forward.frun obj ch client sched t).1.localState p with
          | waiting cmd r v =>
              by_cases hph : ((Forward.frun obj ch client sched t).2.frame p).phase < 6
              · rw [Forward.fstep_gca obj ch client _ hl hph, ForwardGCA.gcaStep_eq]
                exact mstep_step obj _ ch client _ hl (ite_eq_left hph)
              · rw [Forward.fstep_recv obj ch client _ hl hph, ForwardGCA.frameOutput_eq]
                exact mstep_ret obj _ ch client _ hl (ite_eq_right hph)
          | _ =>
              rw [Forward.fstep_prog obj ch client _ (by rw [hl]; rfl)]
              exact mstep_prog obj _ ch client _ (by rw [hl]; rfl)

end ConflictFreedom.HelpingUniversal.Over
