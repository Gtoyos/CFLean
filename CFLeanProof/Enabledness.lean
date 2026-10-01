import CFLeanProof.GlobalSchedule

/-!
# The constructions never deadlock

§7 begins "take any process `i` and let it run after `α` in the absence of
step contention".  That presupposes that a process always *has* a step to take.
This module proves it: from any configuration, every process either has an
enabled transition **of its own** (`StepBy … p`, so the witness really is a step
by `p`, not by some other process) or is stopped at one of exactly two interface
points --

* it is inside a GCA call whose output the family has not produced yet
  (`waiting`), or
* it is about to propose and the family has not accepted that proposal as an
  input (`ready` for Algorithm 1; for Algorithm 3, a finished `M` collect, none
  of whose arrangements of `trace(M_i)` the family accepts).

Both exceptions are the *GCA object interface*, which this development assumes
as an external given (see the assumptions in `MODEL.md`): there is no
internal state in which the program is stuck.  The two schedule structures
already account for the first exception -- `step_actor`'s third case lets a
process inside a GCA call advance the subroutine while the program configuration
stutters -- so `enabled` says that a solo schedule can always be continued as
long as the family serves the proposals.

Nothing here needs reachability: enabledness is a property of the transition
relation itself.
-/

namespace ConflictFreedom.WeakUniversal
open Object
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op] [Nonempty Op]

/-- **Algorithm 1 never deadlocks.** -/
theorem enabled (H : Environment (n := n) obj) (c : Configuration (n := n) obj)
    (p : Fin n) :
    (∃ d, StepBy obj H p c d) ∨
    (∃ cmd r prop, c.localState p = .waiting cmd r prop ∧ (H r).output p = none) ∨
    (∃ cmd seed, c.localState p = .ready cmd seed ∧
      (H (seed.round + 1)).input p ≠ some ((Tagged obj).appendMissing seed.trace cmd)) := by
  classical
  cases h : c.localState p with
  | idle => exact Or.inl ⟨_, Step.invoke c p (Classical.ofNonempty) h (List.finRange n)
      (List.Perm.refl _), fun q hq => by simp [WeakUniversal.update, hq]⟩
  | collecting cmd todo seed =>
      cases todo with
      | nil => exact Or.inl ⟨_, Step.collected c p cmd seed h, fun q hq => by simp [WeakUniversal.update, hq]⟩
      | cons q todo => exact Or.inl ⟨_, Step.read c p q cmd todo seed h, fun q hq => by simp [WeakUniversal.update, hq]⟩
  | ready cmd seed =>
      by_cases hi : (H (seed.round + 1)).input p
          = some ((Tagged obj).appendMissing seed.trace cmd)
      · exact Or.inl ⟨_, Step.propose c p cmd seed h hi, fun q hq => by simp [WeakUniversal.update, hq]⟩
      · exact Or.inr (Or.inr ⟨cmd, seed, rfl, hi⟩)
  | waiting cmd r prop =>
      cases ho : (H r).output p with
      | none => exact Or.inr (Or.inl ⟨cmd, r, prop, rfl, ho⟩)
      | some sf => exact Or.inl ⟨_, Step.receive c p cmd r prop sf.1 sf.2 h (by simpa using ho), fun q hq => by simp [WeakUniversal.update, hq]⟩
  | publishing cmd r s => exact Or.inl ⟨_, Step.publish c p cmd r s h, fun q hq => by simp [WeakUniversal.update, hq]⟩
  | returning cmd r s => exact Or.inl ⟨_, Step.finish c p cmd r s h, fun q hq => by simp [WeakUniversal.update, hq]⟩

end ConflictFreedom.WeakUniversal

namespace ConflictFreedom.HelpingUniversal
open Object
open WeakUniversal (Cmd Tagged Seed Environment zeroSeed)
variable {State Op Response : Type} {n : Nat} (obj : Object State Op Response)
variable [DecidableEq Op] [Nonempty Op]

/-- **Algorithm 3 never deadlocks.** -/
theorem enabled (H : Environment (n := n) obj) (c : Configuration (n := n) obj)
    (p : Fin n) :
    (∃ d, StepBy obj H p c d) ∨
    (∃ cmd r prop, c.localState p = .waiting cmd r prop ∧ (H r).output p = none) ∨
    (∃ cmd seed commands, c.localState p = .gathering cmd seed [] commands ∧
      ∀ arranged, arranged.Perm commands →
        (H (seed.round + 1)).input p ≠ some (proposal obj seed arranged)) := by
  classical
  cases h : c.localState p with
  | idle seed => exact Or.inl ⟨_, Step.invoke c p (Classical.ofNonempty) seed h, fun q hq => by simp [WeakUniversal.update, hq]⟩
  | announcing cmd seed => exact Or.inl ⟨_, Step.announce c p cmd seed h (List.finRange n)
      (List.Perm.refl _), fun q hq => by simp [WeakUniversal.update, hq]⟩
  | collecting cmd todo seed =>
      cases todo with
      | nil => exact Or.inl ⟨_, Step.collectedStart c p cmd seed h (List.finRange n) (List.Perm.refl _),
          fun q hq => by simp [WeakUniversal.update, hq]⟩
      | cons q todo => exact Or.inl ⟨_, Step.readStart c p q cmd todo seed h, fun q hq => by simp [WeakUniversal.update, hq]⟩
  | gathering cmd seed todo commands =>
      cases todo with
      | nil =>
          by_cases hi : ∃ arranged, arranged.Perm commands ∧
              (H (seed.round + 1)).input p = some (proposal obj seed arranged)
          · obtain ⟨arranged, harr, hi⟩ := hi
            exact Or.inl ⟨_, Step.propose c p cmd seed commands h arranged harr hi,
              fun q hq => by simp [WeakUniversal.update, hq]⟩
          · exact Or.inr (Or.inr ⟨cmd, seed, commands, rfl,
              fun arranged harr hin => hi ⟨arranged, harr, hin⟩⟩)
      | cons q todo =>
          exact Or.inl ⟨_, Step.readAnnouncement c p q cmd seed todo commands h, fun q hq => by simp [WeakUniversal.update, hq]⟩
  | waiting cmd r prop =>
      cases ho : (H r).output p with
      | none => exact Or.inr (Or.inl ⟨cmd, r, prop, rfl, ho⟩)
      | some sf =>
          exact Or.inl ⟨_, Step.receive c p cmd r prop sf.1 sf.2 h (by simpa using ho)
            (List.finRange n) (List.Perm.refl _), fun q hq => by simp [WeakUniversal.update, hq]⟩
  | publishing cmd seed => exact Or.inl ⟨_, Step.publish c p cmd seed h (List.finRange n)
      (List.Perm.refl _), fun q hq => by simp [WeakUniversal.update, hq]⟩
  | checking cmd seed todo seen =>
      cases todo with
      | nil =>
          by_cases hc : 0 < (Tagged obj).traceCount cmd seen.trace
          · exact Or.inl ⟨_, Step.finish c p cmd seed seen h hc, fun q hq => by simp [WeakUniversal.update, hq]⟩
          · exact Or.inl ⟨_, Step.retry c p cmd seed seen h (by omega) (List.finRange n)
              (List.Perm.refl _), fun q hq => by simp [WeakUniversal.update, hq]⟩
      | cons q todo =>
          exact Or.inl ⟨_, Step.readCheck c p q cmd seed todo seen h, fun q hq => by simp [WeakUniversal.update, hq]⟩

end ConflictFreedom.HelpingUniversal
