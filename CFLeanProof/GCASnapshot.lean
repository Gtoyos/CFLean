import CFLeanProof.GCAOutput
import CFLeanProof.GCA

/-! Algorithm 2 at the atomic-snapshot abstraction boundary. Views retain process
identities (even when two inputs are equal). Partial publication and partial
return are explicit. The structural hypotheses below are snapshot containment,
self-inclusion and provenance, not GCA safety properties. -/
namespace ConflictFreedom.GCA
open Object
variable {State Op Response P : Type} (obj : Object State Op Response)

/-- One run of Algorithm 2, abstracted to what its two snapshots return:
`aView p` and `bView p` are the processes whose `A` and `B` entries `p`'s scans
saw. -/
structure SnapshotExecution (P : Type) where
  participants : List P
  published : List P
  returned : List P
  input : P → obj.Trace
  aView : P → List P
  bView : P → List P
  published_invoked : ∀ p ∈ published, p ∈ participants
  returned_published : ∀ p ∈ returned, p ∈ published
  a_self : ∀ p ∈ published, p ∈ aView p
  a_valid : ∀ p ∈ published, ∀ q ∈ aView p, q ∈ participants
  b_self : ∀ p ∈ returned, p ∈ bView p
  b_valid : ∀ p ∈ returned, ∀ q ∈ bView p, q ∈ published
  a_chain : ∀ p ∈ published, ∀ q ∈ published,
    (∀ k ∈ aView p, k ∈ aView q) ∨ (∀ k ∈ aView q, k ∈ aView p)
  b_chain : ∀ p ∈ returned, ∀ q ∈ returned,
    (∀ k ∈ bView p, k ∈ bView q) ∨ (∀ k ∈ bView q, k ∈ bView p)

namespace SnapshotExecution
variable {obj} [DecidableEq Op] (e : SnapshotExecution obj P)

/-- `A_p`: the inputs `p`'s scan of `A` saw (line 2). -/
def aTraces (p : P) : List obj.Trace := (e.aView p).map e.input

/-- For each `B` entry `p`'s scan saw (line 5), the view of `A` it was computed
from. -/
def bViews (p : P) : List (List obj.Trace) := (e.bView p).map e.aTraces

/-- The candidate `p` writes into `B` (lines 3–4). -/
noncomputable def candidate (p : P) : obj.Trace := obj.gcaCandidate (e.aTraces p)

/-- The flag `p` writes into `B`: its view of `A` is compatible. -/
def Flag (p : P) : Prop := obj.Compatible (fun s => s ∈ e.aTraces p)

/-- `β_p`, the trace `p` returns (line 6). -/
noncomputable def result (p : P) : obj.Trace := obj.gcaOutput (e.aTraces p) (e.bViews p)

/-- Line 7. -/
def EqualViews (p : P) : Prop :=
  (∀ q ∈ e.aView p, e.input q = e.input p) ∧
  (∀ q ∈ e.bView p, e.candidate q = e.input p)

/-- Line 8, with absent A slots excluded. -/
def Commits (p : P) : Prop := e.EqualViews p ∨
  ((∀ q ∈ e.aView p, obj.TracePrefix (e.input q) (e.result p) → q ∈ e.bView p) ∧
    ∀ q ∈ e.bView p, e.Flag q)

/-- The GCA history of the run: participants' inputs, and each returned
process's `β` with its commit decision (line 8). -/
noncomputable def history : History obj P := by
  classical
  exact {
    input := fun p => if p ∈ e.participants then some (e.input p) else none
    output := fun p => if p ∈ e.returned then some (e.result p, decide (e.Commits p)) else none
    returned_invoked := by
      intro p t c hp
      split at hp
      · exact ⟨e.input p, ite_eq_left (e.published_invoked p (e.returned_published p ‹_›))⟩
      · contradiction }

theorem inputs_iff (s : obj.Trace) : e.history.Inputs s ↔ ∃ p ∈ e.participants, e.input p = s := by
  classical
  simp only [History.Inputs, history]
  constructor
  · rintro ⟨p, hp⟩
    split at hp
    · exact ⟨p, ‹_›, Option.some.inj hp⟩
    · contradiction
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, ite_eq_left hp⟩

theorem output_iff (p : P) (t : obj.Trace) (c : Bool) :
    e.history.output p = some (t, c) ↔
      p ∈ e.returned ∧ t = e.result p ∧ c = @decide (e.Commits p) (Classical.propDecidable _) := by
  classical
  simp only [history]
  split <;> simp_all [eq_comm]

omit [DecidableEq Op] in
theorem a_nonempty {p : P} (hp : p ∈ e.published) : ∃ s, s ∈ e.aTraces p :=
  ⟨e.input p, List.mem_map.mpr ⟨p, e.a_self p hp, rfl⟩⟩

omit [DecidableEq Op] in
theorem a_subset {p q : P} (h : ∀ k ∈ e.aView p, k ∈ e.aView q) :
    ∀ s ∈ e.aTraces p, s ∈ e.aTraces q := by
  rintro s hs
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
  exact List.mem_map.mpr ⟨k, h k hk, rfl⟩

theorem candidate_extends {p : P} (hf : e.Flag p) {q : P} (hq : q ∈ e.aView p) :
    obj.TracePrefix (e.input q) (e.candidate p) :=
  (obj.gcaCandidate_of_compatible _ hf).1 _ (List.mem_map.mpr ⟨q, hq, rfl⟩)

theorem result_lower {p q : P} (hq : q ∈ e.bView p) (hf : e.Flag q) :
    obj.TracePrefix (e.result p) (e.candidate q) := by
  have hm : e.candidate q ∈ obj.gcaFlagged (e.bViews p) :=
    (obj.gcaFlagged_mem_iff _ _).mpr
      ⟨e.aTraces q, List.mem_map.mpr ⟨q, hq, rfl⟩, hf, rfl⟩
  unfold result Object.gcaOutput
  split
  · exact (obj.traceGLB_spec _ _).1 _ hm
  · rename_i hn
    exact False.elim (hn ⟨_, hm⟩)

theorem result_greatest {p : P} {l : obj.Trace}
    (hflag : ∃ q ∈ e.bView p, e.Flag q)
    (hl : ∀ q ∈ e.bView p, e.Flag q → obj.TracePrefix l (e.candidate q)) :
    obj.TracePrefix l (e.result p) := by
  unfold result Object.gcaOutput
  split
  · apply (obj.traceGLB_spec _ _).2
    intro t ht
    obtain ⟨S, hS, hf, rfl⟩ := (obj.gcaFlagged_mem_iff _ _).mp ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hS
    exact hl q hq hf
  · rename_i hn
    obtain ⟨q, hq, hf⟩ := hflag
    exact False.elim (hn ⟨e.candidate q, (obj.gcaFlagged_mem_iff _ _).mpr
      ⟨e.aTraces q, List.mem_map.mpr ⟨q, hq, rfl⟩, hf, rfl⟩⟩)

theorem validity : e.history.Validity := by
  apply History.Validity.of_occurs
  intro p t c hp a k hk
  obtain ⟨hret, rfl, _⟩ := (e.output_iff p t c).mp hp
  rw [History.Occurs, obj.traceResponses_length] at hk
  obtain ⟨S, hS, s, hs, hk⟩ := obj.gcaOutput_validity _ _ a k hk
  have provenance : ∃ q ∈ e.published, S = e.aTraces q := by
    rcases hS with rfl | hS
    · exact ⟨p, e.returned_published p hret, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hS
      exact ⟨q, e.b_valid p hret q hq, rfl⟩
  obtain ⟨q, hq, rfl⟩ := provenance
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
  refine ⟨e.input r, (e.inputs_iff _).mpr ⟨r, e.a_valid q hq r hr, rfl⟩, ?_⟩
  simpa only [History.Occurs, obj.traceResponses_length] using hk

theorem commonPrefix : e.history.CommonPrefix := by
  intro l hl t ht
  obtain ⟨p, c, hp⟩ := ht
  obtain ⟨hret, rfl, _⟩ := (e.output_iff p t c).mp hp
  have provenance : ∀ S, S = e.aTraces p ∨ S ∈ e.bViews p →
      ∃ q ∈ e.published, S = e.aTraces q := by
    intro S hS
    rcases hS with rfl | hS
    · exact ⟨p, e.returned_published p hret, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hS
      exact ⟨q, e.b_valid p hret q hq, rfl⟩
  apply obj.gcaOutput_commonPrefix
  · intro S hS
    obtain ⟨q, hq, rfl⟩ := provenance S hS
    exact e.a_nonempty hq
  · intro S hS s hs
    obtain ⟨q, hq, rfl⟩ := provenance S hS
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    exact hl _ ((e.inputs_iff _).mpr ⟨r, e.a_valid q hq r hr, rfl⟩)

theorem convergence : e.history.Convergence := by
  have chain : ∀ S ∈ e.published.map e.aTraces, ∀ T ∈ e.published.map e.aTraces,
      (∀ s ∈ S, s ∈ T) ∨ (∀ t ∈ T, t ∈ S) := by
    intro S hS T hT
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hS
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hT
    exact (e.a_chain p hp q hq).elim (fun h => Or.inl (e.a_subset h))
      (fun h => Or.inr (e.a_subset h))
  obtain ⟨u, hu⟩ := obj.gcaOutputs_convergence _ chain
  refine ⟨u, ?_⟩
  rintro t ⟨p, c, hp⟩
  obtain ⟨hret, rfl, _⟩ := (e.output_iff p t c).mp hp
  apply hu
  refine ⟨e.aTraces p, e.bViews p,
    List.mem_map.mpr ⟨p, e.returned_published p hret, rfl⟩, ?_, rfl⟩
  intro S hS
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hS
  exact List.mem_map.mpr ⟨q, e.b_valid p hret q hq, rfl⟩

/-- A uniform nonempty A view has exactly that trace as its candidate. -/
theorem candidate_eq_of_uniform {p : P} (hp : p ∈ e.published) (s : obj.Trace)
    (he : ∀ q ∈ e.aView p, e.input q = s) : e.candidate p = s := by
  have hc : e.Flag p := ⟨s, by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    rw [he q hq]
    exact obj.tracePrefix_refl s⟩
  apply obj.lub_unique (obj.gcaCandidate_of_compatible _ hc)
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
    rw [he q hq]
    exact obj.tracePrefix_refl s
  · intro u hu
    have h := hu (e.input p) (List.mem_map.mpr ⟨p, e.a_self p hp, rfl⟩)
    simpa only [he p (e.a_self p hp)] using h

theorem result_prefix {p : P} {l : obj.Trace}
    (hown : obj.TracePrefix l (e.candidate p))
    (hl : ∀ q ∈ e.bView p, e.Flag q → obj.TracePrefix l (e.candidate q)) :
    obj.TracePrefix l (e.result p) := by
  unfold result Object.gcaOutput
  split
  · apply (obj.traceGLB_spec _ _).2
    intro t ht
    obtain ⟨S, hS, hf, rfl⟩ := (obj.gcaFlagged_mem_iff _ _).mp ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hS
    exact hl q hq hf
  · exact hown

theorem weakAgreement : e.history.WeakAgreement := by
  classical
  intro he p t c hp
  obtain ⟨hret, _, hc⟩ := (e.output_iff p t c).mp hp
  have hpP := e.published_invoked p (e.returned_published p hret)
  have eq : ∀ q ∈ e.participants, e.input q = e.input p := by
    intro q hq
    exact he _ _ ((e.inputs_iff _).mpr ⟨q, hq, rfl⟩)
      ((e.inputs_iff _).mpr ⟨p, hpP, rfl⟩)
  have hw : e.EqualViews p := by
    refine ⟨fun q hq => eq q (e.a_valid p (e.returned_published p hret) q hq), ?_⟩
    intro q hq
    have hpub := e.b_valid p hret q hq
    exact e.candidate_eq_of_uniform hpub _ (fun r hr => eq r (e.a_valid q hpub r hr))
  rw [hc]
  exact decide_eq_true (Or.inl hw)

theorem candidates_comparable {p q : P} (hp : p ∈ e.published) (hq : q ∈ e.published)
    (hfp : e.Flag p) (hfq : e.Flag q) :
    obj.TracePrefix (e.candidate p) (e.candidate q) ∨
      obj.TracePrefix (e.candidate q) (e.candidate p) := by
  rcases e.a_chain p hp q hq with h | h
  · exact Or.inl (obj.gcaCandidate_mono_of_compatible (e.a_subset h) hfq)
  · exact Or.inr (obj.gcaCandidate_mono_of_compatible (e.a_subset h) hfp)

/-- Every compatible candidate extends a committed output. This is the key
adoption invariant, including the separate equal-view fast path. -/
theorem commit_below_flagged {p : P} (hp : p ∈ e.returned) (hc : e.Commits p)
    {r : P} (hr : r ∈ e.published) (hf : e.Flag r) :
    obj.TracePrefix (e.result p) (e.candidate r) := by
  classical
  have hpub := e.returned_published p hp
  rcases hc with hw | ⟨hcover, hflags⟩
  · have own : e.candidate p = e.input p := e.candidate_eq_of_uniform hpub _ hw.1
    have hfp : e.Flag p := ⟨e.input p, by
      intro s hs
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hs
      rw [hw.1 q hq]
      exact obj.tracePrefix_refl _⟩
    have hout : obj.TracePrefix (e.result p) (e.input p) :=
      own ▸ e.result_lower (e.b_self p hp) hfp
    apply obj.tracePrefix_trans hout
    rcases e.a_chain p hpub r hr with h | h
    · exact e.candidate_extends hf (h p (e.a_self p hpub))
    · have he := hw.1 r (h r (e.a_self r hr))
      rw [← he]
      exact e.candidate_extends hf (e.a_self r hr)
  · have hfp := hflags p (e.b_self p hp)
    by_cases hin : r ∈ e.bView p
    · exact e.result_lower hin hf
    · rcases e.a_chain p hpub r hr with h | h
      · exact obj.tracePrefix_trans (e.result_lower (e.b_self p hp) hfp)
          (obj.gcaCandidate_mono_of_compatible (e.a_subset h) hf)
      · apply Classical.byContradiction
        intro hn
        have hlow : obj.TracePrefix (e.candidate r) (e.result p) := by
          apply e.result_greatest ⟨p, e.b_self p hp, hfp⟩
          intro q hq hfq
          rcases e.candidates_comparable (e.b_valid p hp q hq) hr hfq hf with hqr | hrq
          · exact False.elim (hn (obj.tracePrefix_trans (e.result_lower hq hfq) hqr))
          · exact hrq
        exact hin (hcover r (h r (e.a_self r hr))
          (obj.tracePrefix_trans (e.candidate_extends hf (e.a_self r hr)) hlow))

theorem adoption : e.history.Adoption := by
  classical
  intro p t hp q u c hq
  obtain ⟨hpR, rfl, hcp⟩ := (e.output_iff p t true).mp hp
  obtain ⟨hqR, rfl, _⟩ := (e.output_iff q u c).mp hq
  have hc : e.Commits p := of_decide_eq_true hcp.symm
  have flagged := fun r hr hf => e.commit_below_flagged hpR hc (e.b_valid q hqR r hr) hf
  by_cases hex : ∃ r ∈ e.bView q, e.Flag r
  · exact e.result_greatest hex flagged
  · apply e.result_prefix _ flagged
    rcases hc with hw | ⟨_, hflags⟩
    · rcases e.b_chain p hpR q hqR with h | h
      · have hfp : e.Flag p := ⟨e.input p, by
          intro s hs
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
          rw [hw.1 r hr]
          exact obj.tracePrefix_refl _⟩
        exact False.elim (hex ⟨p, h p (e.b_self p hpR), hfp⟩)
      · have hqeq := hw.2 q (h q (e.b_self q hqR))
        have hfp : e.Flag p := ⟨e.input p, by
          intro s hs
          obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
          rw [hw.1 r hr]
          exact obj.tracePrefix_refl _⟩
        rw [hqeq]
        have he := e.candidate_eq_of_uniform (e.returned_published p hpR) _ hw.1
        exact he ▸ e.result_lower (e.b_self p hpR) hfp
    · rcases e.b_chain p hpR q hqR with h | h
      · exact False.elim (hex ⟨p, h p (e.b_self p hpR), hflags p (e.b_self p hpR)⟩)
      · exact False.elim (hex ⟨q, e.b_self q hqR, hflags q (h q (e.b_self q hqR))⟩)

/-- A finite nonempty family in a total preorder has a greatest member. -/
private theorem list_greatest {α : Type} (R : α → α → Prop)
    (refl : ∀ x, R x x) (trans : ∀ x y z, R x y → R y z → R x z)
    (L : List α) (hne : ∃ x, x ∈ L)
    (total : ∀ x ∈ L, ∀ y ∈ L, R x y ∨ R y x) :
    ∃ g ∈ L, ∀ x ∈ L, R x g := by
  induction L with
  | nil => obtain ⟨x, hx⟩ := hne; cases hx
  | cons a L ih =>
    cases L with
    | nil =>
      refine ⟨a, by simp, ?_⟩
      intro x hx
      have he : x = a := by simpa using hx
      exact he ▸ refl a
    | cons b L =>
      obtain ⟨g, hg, hgreat⟩ := ih ⟨b, by simp⟩
        (fun x hx y hy => total x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      rcases total a (by simp) g (List.mem_cons_of_mem _ hg) with hag | hga
      · refine ⟨g, List.mem_cons_of_mem _ hg, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hag
        · exact hgreat x hx
      · refine ⟨a, by simp, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact refl _
        · exact trans x g a (hgreat x hx) hga

/-- Commitment follows from a least candidate and a maximal B view among
processes whose input is below it. This also handles equal inputs and views. -/
theorem commitment : e.history.Commitment := by
  classical
  intro hne hcompatible hreturned
  have done : ∀ p ∈ e.participants, p ∈ e.returned := by
    intro p hp
    obtain ⟨t, c, hc⟩ := hreturned p (e.input p) (by simp [history, hp])
    exact ((e.output_iff p t c).mp hc).1
  have pub : ∀ p ∈ e.participants, p ∈ e.published :=
    fun p hp => e.returned_published p (done p hp)
  have flag : ∀ p ∈ e.published, e.Flag p := by
    intro p hp
    obtain ⟨u, hu⟩ := hcompatible
    refine ⟨u, ?_⟩
    intro s hs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    exact hu _ ((e.inputs_iff _).mpr ⟨r, e.a_valid p hp r hr, rfl⟩)
  have nonempty : ∃ p, p ∈ e.participants := by
    obtain ⟨s, hs⟩ := hne
    obtain ⟨p, hp, _⟩ := (e.inputs_iff s).mp hs
    exact ⟨p, hp⟩
  obtain ⟨m, hm, hmin⟩ := list_greatest
    (fun p q => obj.TracePrefix (e.candidate q) (e.candidate p))
    (fun p => obj.tracePrefix_refl _) (fun _ _ _ h₁ h₂ => obj.tracePrefix_trans h₂ h₁)
    e.participants nonempty (by
      intro p hp q hq
      exact (e.candidates_comparable (pub p hp) (pub q hq)
        (flag p (pub p hp)) (flag q (pub q hq))).symm)
  let eligible := e.participants.filter (fun p => decide (obj.TracePrefix (e.input p) (e.candidate m)))
  have eligible_iff : ∀ p, p ∈ eligible ↔
      p ∈ e.participants ∧ obj.TracePrefix (e.input p) (e.candidate m) := by
    intro p
    simp [eligible]
  have hmE : m ∈ eligible := (eligible_iff m).mpr
    ⟨hm, e.candidate_extends (flag m (pub m hm)) (e.a_self m (pub m hm))⟩
  obtain ⟨q, hqE, hmax⟩ := list_greatest
    (fun p q => ∀ k ∈ e.bView p, k ∈ e.bView q)
    (fun _ _ hk => hk) (fun _ _ _ h₁ h₂ k hk => h₂ k (h₁ k hk)) eligible
    ⟨m, hmE⟩ (by
      intro p hp q hq
      exact e.b_chain p (done p ((eligible_iff p).mp hp).1)
        q (done q ((eligible_iff q).mp hq).1))
  obtain ⟨hq, hinput⟩ := (eligible_iff q).mp hqE
  have hmB : m ∈ e.bView q := hmax m hmE m (e.b_self m (done m hm))
  have result_eq : e.result q = e.candidate m := by
    apply obj.tracePrefix_antisymm (e.result_lower hmB (flag m (pub m hm)))
    apply e.result_greatest ⟨m, hmB, flag m (pub m hm)⟩
    intro r hr _
    exact hmin r (e.published_invoked r (e.b_valid q (done q hq) r hr))
  have commits : e.Commits q := by
    right
    refine ⟨?_, fun r hr => flag r (e.b_valid q (done q hq) r hr)⟩
    intro r hr hle
    have hrP := e.a_valid q (pub q hq) r hr
    have hrE : r ∈ eligible := (eligible_iff r).mpr ⟨hrP, result_eq ▸ hle⟩
    exact hmax r hrE r (e.b_self r (done r hrP))
  refine ⟨q, e.input q, e.result q, ?_, ?_, ?_⟩
  · simp [history, hq]
  · exact (e.output_iff q _ true).mpr ⟨done q hq, rfl, (decide_eq_true commits).symm⟩
  · simpa only [result_eq] using hinput

/-- All six GCA requirements for Algorithm 2's snapshot view model. This theorem
is conditional only on the structural snapshot assumptions in the model; it
makes no claim yet about an atomic-register refinement or wait-freedom. -/
theorem specification : e.history.Specification :=
  ⟨e.validity, e.adoption, e.commitment, e.convergence, e.commonPrefix, e.weakAgreement⟩

end SnapshotExecution
end ConflictFreedom.GCA
