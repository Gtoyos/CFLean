import CFLeanProof.GCA
import CFLeanProof.TraceAlgebra

/-! Consequences of the six GCA requirements used by the constructions. -/
namespace ConflictFreedom.GCA.History
open Object
variable {State Op Response P : Type} {obj : Object State Op Response}
variable [DecidableEq Op] (h : History obj P)

/-- An output extending the common input of a round is that input: Validity
excludes new occurrences. -/
theorem output_eq_of_prefix {s : obj.Trace} (spec : h.Specification)
    (uniform : ∀ u, h.Inputs u → u = s)
    {p : P} {t : obj.Trace} {c : Bool} (hp : h.output p = some (t, c))
    (hpref : obj.TracePrefix s t) : t = s := by
  apply (obj.tracePrefix_eq_of_count_le hpref ?_).symm
  intro a
  by_cases hc : obj.traceCount a t ≤ obj.traceCount a s
  · exact hc
  · have hk : obj.traceCount a s < obj.traceCount a t := by omega
    obtain ⟨u, hu, hku⟩ := spec.validity.occurs p t c hp a (obj.traceCount a s)
      (by simpa only [Occurs, obj.traceResponses_length] using hk)
    rw [uniform u hu] at hku
    simp only [Occurs, obj.traceResponses_length] at hku
    omega

/-- Equal inputs force the exact input trace, not merely an extension: the
common-prefix property excludes deletion, and validity excludes new occurrences. -/
theorem uniform_output {s : obj.Trace} (spec : h.Specification)
    (uniform : ∀ u, h.Inputs u → u = s)
    {p : P} {t : obj.Trace} {c : Bool} (hp : h.output p = some (t, c)) : t = s :=
  h.output_eq_of_prefix spec uniform hp (spec.commonPrefix s
    (fun u hu => uniform u hu ▸ obj.tracePrefix_refl s) t ⟨p, c, hp⟩)

/-- When inputs agree, every return is precisely (input, commit). -/
theorem uniform_return {s : obj.Trace} (spec : h.Specification)
    (uniform : ∀ u, h.Inputs u → u = s)
    {p : P} {t : obj.Trace} {c : Bool} (hp : h.output p = some (t, c)) :
    t = s ∧ c = true :=
  ⟨h.uniform_output spec uniform hp,
    spec.weakAgreement (fun u v hu hv => (uniform u hu).trans (uniform v hv).symm) p t c hp⟩

/-- **A sole participant commits its own proposal.**  Its input alone is
compatible, and once it has returned every participant has, so by Commitment it
commits an extension of its input; by Validity that extension is the input. -/
theorem solo_commit {s : obj.Trace} (spec : h.Specification)
    {p : P} (hin : h.input p = some s) (hsole : ∀ q u, h.input q = some u → q = p)
    {t : obj.Trace} {c : Bool} (hp : h.output p = some (t, c)) :
    t = s ∧ c = true := by
  have hone : ∀ u, h.Inputs u → u = s := by
    rintro u ⟨q, hq⟩
    obtain rfl := hsole q u hq
    exact Option.some.inj (hq.symm.trans hin)
  obtain ⟨q, s', x, hq, hx, hpre⟩ := spec.commitment ⟨s, p, hin⟩
    ⟨s, fun u hu => hone u hu ▸ obj.tracePrefix_refl s⟩
    (fun q u hq => by obtain rfl := hsole q u hq; exact ⟨t, c, hp⟩)
  obtain rfl := hsole q s' hq
  obtain rfl : s' = s := Option.some.inj (hq.symm.trans hin)
  obtain ⟨rfl, rfl⟩ : x = t ∧ true = c := Prod.mk.inj (Option.some.inj (hx.symm.trans hp))
  exact ⟨h.output_eq_of_prefix spec hone hp hpre, rfl⟩

end ConflictFreedom.GCA.History
