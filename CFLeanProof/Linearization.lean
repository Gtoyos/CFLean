import CFLeanProof.TraceAlgebra

/-! # Trace-level content of the linearizability arguments

This module covers the purely trace-theoretic part of the proof of
Theorem `theorem:weakUCLin` in `main.tex` (the construction of the representative
schedule `\hat t` from the chain of committed traces `t_0 \le t_1 \le … \le t_{r^*}`),
together with the response-stability facts (`lemma:ret-trace-prefix`,
`lemma:ret-trace-eq`) that make the resulting sequential history legal.  The same
argument is reused verbatim by the Algorithm 3 linearizability lemma.

What is formalized here:

* `chain_representative` — a chain of committed traces starting at `ε` admits a
  block decomposition `blocks = s_0, …, s_{m-1}` of concrete schedules whose
  flattening represents `t m` and whose prefixes represent every `t k`.
* `blockStart` / `blockIndexOf` and `blocks_ordered` — the resulting representative
  lists the letters of block `k` strictly before those of block `k'` when `k < k'`.
* `traceReturn_stable_along_chain` — an occurrence response computed from an
  intermediate committed trace is the one computed from the final trace.
* `responses_occurrence` / `traceReturn_of_representative` — the response recorded
  for the `j`-th occurrence of an operation in a representative is exactly the one
  the sequential specification produces at that point, i.e. the sequential history
  read off a representative is legal.

This module supplies the trace-level lemmas. `FiniteLinearization` uses them to
construct finite command histories, completions, and real-time order.
`UniversalLinearization` connects that construction to both program runs, and
`CausalLinearization` discharges its last hypothesis (chronological occurrence
provenance) from causal GCA validity and the `receive_ready` scheduling rule, so
`GlobalSchedule.Weak.finite_linearization` and its `Helping` counterpart are
unconditional.

-/

namespace ConflictFreedom.Object
variable {State Op Response : Type} (obj : Object State Op Response)

/-! ### Chains of committed traces -/

/-- Concatenation of representatives represents the concatenation of traces. -/
theorem mk_append (x y : List Op) :
    Quotient.mk obj.traceSetoid (x ++ y) =
      obj.traceAppend (Quotient.mk obj.traceSetoid x) (Quotient.mk obj.traceSetoid y) := rfl

/-- A chain of committed traces (`t_{k} \le t_{k+1}` in the paper, obtained from
Adoption and Lemma `lemma:prefix-rounds`) is a prefix chain. -/
theorem tracePrefix_chain (t : Nat → obj.Trace) (m : Nat) :
    (∀ j, j < m → obj.TracePrefix (t j) (t (j + 1))) →
      ∀ k, k ≤ m → obj.TracePrefix (t k) (t m) := by
  induction m with
  | zero =>
      intro _ k hk
      rw [Nat.le_zero.mp hk]
      exact obj.tracePrefix_refl _
  | succ m ih =>
      intro hmono k hk
      rcases Nat.lt_or_ge k (m + 1) with h | h
      · exact obj.tracePrefix_trans
          (ih (fun j hj => hmono j (Nat.lt_succ_of_lt hj)) k (Nat.lt_succ_iff.mp h))
          (hmono m (Nat.lt_succ_self m))
      · rw [Nat.le_antisymm hk h]
        exact obj.tracePrefix_refl _

/-- **Chain representative with blocks** (main.tex, construction of `\hat t` in the
proof of `theorem:weakUCLin`).  From a chain `t_0 = ε`, `t_{k+1} = t_k \cdot s_k`
we extract *concrete* schedules `s_0, …, s_{m-1}`; their concatenation is a
representative of `t m`, and the concatenation of the first `k` of them is a
representative of `t k`.

Note the indexing: the blocks are `s_0, …, s_{m-1}`, not `s_1, …, s_m` as the
manuscript writes (see the reported off-by-one). -/
theorem chain_representative (t : Nat → obj.Trace) (m : Nat)
    (h0 : t 0 = obj.emptyTrace)
    (hmono : ∀ k, k < m → obj.TracePrefix (t k) (t (k + 1))) :
    ∃ blocks : List (List Op), blocks.length = m ∧
      Quotient.mk obj.traceSetoid blocks.flatten = t m ∧
      ∀ k, k ≤ m → Quotient.mk obj.traceSetoid ((blocks.take k).flatten) = t k := by
  revert hmono
  induction m with
  | zero =>
      intro _
      refine ⟨[], rfl, ?_, ?_⟩
      · rw [h0]; rfl
      · intro k hk
        rw [Nat.le_zero.mp hk, h0]
        rfl
  | succ m ih =>
      intro hmono
      obtain ⟨blocks, hlen, hflat, htake⟩ := ih (fun k hk => hmono k (Nat.lt_succ_of_lt hk))
      obtain ⟨u, hu⟩ :=
        (obj.tracePrefix_iff_append _ _).mp (hmono m (Nat.lt_succ_self m))
      obtain ⟨y, hy⟩ := Quotient.exists_rep u
      have hfull : Quotient.mk obj.traceSetoid (blocks ++ [y]).flatten = t (m + 1) := by
        rw [List.flatten_concat, obj.mk_append, hflat, hy]
        exact hu.symm
      refine ⟨blocks ++ [y], by simp [hlen], hfull, ?_⟩
      intro k hk
      rcases Nat.lt_or_ge k (m + 1) with h | h
      · have hk' : k ≤ m := Nat.lt_succ_iff.mp h
        have hcut : (blocks ++ [y]).take k = blocks.take k := by
          rw [List.take_append, Nat.sub_eq_zero_of_le (by omega : k ≤ blocks.length)]
          simp
        rw [hcut]
        exact htake k hk'
      · have hkeq : k = m + 1 := Nat.le_antisymm hk h
        subst hkeq
        rw [List.take_of_length_le (by simp [hlen])]
        exact hfull

/-! ### Where a block sits inside the representative -/

/-- Position at which block `k` starts inside the flattened representative. -/
def blockStart (blocks : List (List Op)) (k : Nat) : Nat :=
  ((blocks.take k).flatten).length

theorem flatten_take_append_drop (blocks : List (List Op)) (k : Nat) :
    blocks.flatten = (blocks.take k).flatten ++ (blocks.drop k).flatten := by
  rw [← List.flatten_append, List.take_append_drop]

/-- The first `k` blocks occupy exactly the prefix of length `blockStart blocks k`. -/
theorem take_blockStart (blocks : List (List Op)) (k : Nat) :
    blocks.flatten.take (blockStart blocks k) = (blocks.take k).flatten := by
  rw [flatten_take_append_drop blocks k]
  exact List.take_left

/-- The remaining blocks occupy exactly the corresponding suffix. -/
theorem drop_blockStart (blocks : List (List Op)) (k : Nat) :
    blocks.flatten.drop (blockStart blocks k) = (blocks.drop k).flatten := by
  rw [flatten_take_append_drop blocks k]
  exact List.drop_left

theorem blockStart_le_length (blocks : List (List Op)) (k : Nat) :
    blockStart blocks k ≤ blocks.flatten.length := by
  rw [flatten_take_append_drop blocks k, List.length_append]
  show ((blocks.take k).flatten).length ≤ _
  omega

theorem blockStart_mono (blocks : List (List Op)) {k k' : Nat} (h : k ≤ k') :
    blockStart blocks k ≤ blockStart blocks k' := by
  have h1 : (blocks.take k').take k = blocks.take k := by
    rw [List.take_take]
    congr 1
    omega
  have h2 : blocks.take k' = blocks.take k ++ (blocks.take k').drop k := by
    rw [← h1]
    exact (List.take_append_drop k (blocks.take k')).symm
  show ((blocks.take k).flatten).length ≤ ((blocks.take k').flatten).length
  rw [h2, List.flatten_append, List.length_append]
  omega

/-- Index of the block containing position `p` of the flattened representative:
the number of blocks that have already ended at or before `p`. -/
def blockIndexOf (blocks : List (List Op)) (p : Nat) : Nat :=
  (List.range blocks.length).countP (fun k => decide (blockStart blocks (k + 1) ≤ p))

private theorem countP_range_eq (P : Nat → Bool) (k : Nat)
    (hlt : ∀ j, j < k → P j = true) (hge : ∀ j, k ≤ j → P j = false) (n : Nat) :
    (List.range n).countP P = min k n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.countP_append, ih]
      by_cases h : n < k
      · rw [show List.countP P [n] = 1 by simp [hlt n h]]
        omega
      · rw [show List.countP P [n] = 0 by simp [hge n (Nat.le_of_not_lt h)]]
        omega

/-- Reading the representative left to right never decreases the block index.
This is a statement about positions in a `List (List Op)`; it becomes the
paper's `cmd(\Phi_1) \preceq_{\hat t} cmd(\Phi_2)` only once operations have
been assigned to blocks, which is supplied separately in `FiniteLinearization`. -/
theorem blocks_ordered (blocks : List (List Op)) {p q : Nat} (hpq : p ≤ q) :
    blockIndexOf blocks p ≤ blockIndexOf blocks q := by
  refine List.countP_mono_left (fun j _ hj => ?_)
  simp only [decide_eq_true_eq] at hj ⊢
  omega

/-- `blockIndexOf` really computes the block a position belongs to. -/
theorem blockIndexOf_eq (blocks : List (List Op)) {k p : Nat} (hk : k < blocks.length)
    (h1 : blockStart blocks k ≤ p) (h2 : p < blockStart blocks (k + 1)) :
    blockIndexOf blocks p = k := by
  have key := countP_range_eq (fun j => decide (blockStart blocks (j + 1) ≤ p)) k
    (fun j hj => by
      simp only [decide_eq_true_eq]
      have := blockStart_mono blocks (show j + 1 ≤ k by omega)
      omega)
    (fun j hj => by
      simp only [decide_eq_false_iff_not, Nat.not_le]
      have := blockStart_mono blocks (show k + 1 ≤ j + 1 by omega)
      omega)
    blocks.length
  rw [blockIndexOf, key]
  omega

/-- Every letter of block `k` occurs strictly before every letter of block `k'`
whenever `k < k'`.

This is the *positional* half of the paper's conclusion
"if `\Phi_1 \preceq_H \Phi_2` then `cmd(\Phi_1) \preceq_{\hat t} cmd(\Phi_2)`",
and nothing more: its statement mentions no object, trace, command or history.
The ordering of operations is proved separately by `roundChain_linearizes`:
the trace `t_k` associated with `\Phi_1` contains only commands invoked before
`\Phi_1` returned, so `cmd(\Phi_2)` lies outside the block prefix
`\hat s_1 ⋯ \hat s_k` that contains `cmd(\Phi_1)`. -/
theorem block_positions_ordered (blocks : List (List Op)) {k k' p p' : Nat}
    (hkk' : k < k') (hp : p < blockStart blocks (k + 1))
    (hp' : blockStart blocks k' ≤ p') : p < p' := by
  have := blockStart_mono blocks (show k + 1 ≤ k' from hkk')
  omega

/-- The letters of the first `k` blocks all occur in the prefix of the
representative of length `blockStart blocks k`. -/
theorem mem_take_blockStart {blocks : List (List Op)} {k : Nat} {a : Op}
    (h : a ∈ (blocks.take k).flatten) : a ∈ blocks.flatten.take (blockStart blocks k) := by
  rw [take_blockStart]
  exact h

/-- The letters of the remaining blocks all occur after that prefix. -/
theorem mem_drop_blockStart {blocks : List (List Op)} {k : Nat} {a : Op}
    (h : a ∈ (blocks.drop k).flatten) : a ∈ blocks.flatten.drop (blockStart blocks k) := by
  rw [drop_blockStart]
  exact h

/-! ### A canonical, monotone chain representative

`chain_representative` picks a block decomposition separately for each length
`m`, so the representatives it returns for different `m` need not agree.  For
the infinite-history closure the choice has to be made **once**: `chainBlock k`
is a representative of the residual of `t k` in `t (k + 1)`, chosen
independently of `m`, and `chainRep m` concatenates the first `m` blocks.  Then
`chainRep k` is literally a prefix of `chainRep m` for `k ≤ m`, so all the
finite linearizations agree on the order of the operations they share. -/

private theorem chainBlock_exists (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) (k : Nat) :
    ∃ b : List Op, t (k + 1) = obj.traceAppend (t k) (Quotient.mk obj.traceSetoid b) := by
  obtain ⟨u, hu⟩ := (obj.tracePrefix_iff_append _ _).mp (hmono k)
  obtain ⟨b, hb⟩ := Quotient.exists_rep u
  exact ⟨b, by rw [hb]; exact hu⟩

/-- A representative of the residual of `t k` in `t (k + 1)`. -/
noncomputable def chainBlock (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) (k : Nat) : List Op :=
  Classical.choose (obj.chainBlock_exists t hmono k)

theorem chainBlock_spec (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) (k : Nat) :
    t (k + 1) =
      obj.traceAppend (t k) (Quotient.mk obj.traceSetoid (obj.chainBlock t hmono k)) :=
  Classical.choose_spec (obj.chainBlock_exists t hmono k)

/-- The canonical representative of `t m`: the first `m` blocks, concatenated. -/
noncomputable def chainRep (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) : Nat → List Op
  | 0 => []
  | k + 1 => chainRep t hmono k ++ obj.chainBlock t hmono k

theorem chainRep_succ (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) (k : Nat) :
    obj.chainRep t hmono (k + 1) =
      obj.chainRep t hmono k ++ obj.chainBlock t hmono k := rfl

theorem chainRep_mk (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) (h0 : t 0 = obj.emptyTrace) (m : Nat) :
    Quotient.mk obj.traceSetoid (obj.chainRep t hmono m) = t m := by
  induction m with
  | zero => exact h0.symm
  | succ k ih =>
      rw [obj.chainRep_succ, obj.mk_append, ih]
      exact (obj.chainBlock_spec t hmono k).symm

/-- Earlier representatives are literal prefixes of later ones. -/
theorem chainRep_le (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) {k m : Nat} (h : k ≤ m) :
    ∃ z, obj.chainRep t hmono m = obj.chainRep t hmono k ++ z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
      obtain ⟨z, hz⟩ := ih (by omega)
      refine ⟨z ++ obj.chainBlock t hmono (k + d), ?_⟩
      rw [show k + (d + 1) = (k + d) + 1 from rfl, obj.chainRep_succ, hz, List.append_assoc]

theorem chainRep_length (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) (h0 : t 0 = obj.emptyTrace) (m : Nat) :
    (obj.chainRep t hmono m).length = obj.traceLength (t m) := by
  rw [← obj.chainRep_mk t hmono h0 m]; rfl

theorem chainRep_take (t : Nat → obj.Trace)
    (hmono : ∀ k, obj.TracePrefix (t k) (t (k + 1))) (h0 : t 0 = obj.emptyTrace)
    {k m : Nat} (h : k ≤ m) :
    (obj.chainRep t hmono m).take (obj.traceLength (t k)) = obj.chainRep t hmono k := by
  obtain ⟨z, hz⟩ := obj.chainRep_le t hmono h
  rw [hz, ← obj.chainRep_length t hmono h0 k]
  simp

/-- Packaged form of the construction of `\hat t`: a single concrete representative
of the final committed trace, each of whose prefixes (of the forced length
`obj.traceLength (t k)`) represents the `k`-th committed trace. -/
theorem chain_representative_prefixes (t : Nat → obj.Trace) (m : Nat)
    (h0 : t 0 = obj.emptyTrace)
    (hmono : ∀ k, k < m → obj.TracePrefix (t k) (t (k + 1))) :
    ∃ x : List Op, Quotient.mk obj.traceSetoid x = t m ∧
      ∀ k, k ≤ m → obj.traceLength (t k) ≤ x.length ∧
        Quotient.mk obj.traceSetoid (x.take (obj.traceLength (t k))) = t k := by
  obtain ⟨blocks, _, hflat, htake⟩ := obj.chain_representative t m h0 hmono
  refine ⟨blocks.flatten, hflat, fun k hk => ?_⟩
  have hlen : obj.traceLength (t k) = blockStart blocks k := by
    rw [← htake k hk]
    rfl
  rw [hlen]
  exact ⟨blockStart_le_length blocks k, by rw [take_blockStart]; exact htake k hk⟩

/-! ### Stability of responses along the chain -/

/-- **Response stability** (main.tex, `\ret^*(cmd(\Phi),s) = \ret^*(cmd(\Phi),t)` in
the proof of `theorem:weakUCLin`; Lemma `lemma:ret-trace-prefix` chained along the
prefix chain).  Once an occurrence exists in an intermediate committed trace, its
response never changes. -/
theorem traceReturn_stable_along_chain [DecidableEq Op] (t : Nat → obj.Trace) (m : Nat)
    (hmono : ∀ j, j < m → obj.TracePrefix (t j) (t (j + 1)))
    {k : Nat} (hkm : k ≤ m) (a : Op) (j : Nat)
    (hj : j < (obj.traceResponses a obj.initial (t k)).length) :
    obj.traceReturn a j (t k) = obj.traceReturn a j (t m) :=
  obj.traceReturn_prefix (obj.tracePrefix_chain t m hmono k hkm) a j hj

/-! ### Legality of the sequential history read off a representative -/

/-- The response recorded for the occurrence of `a` that sits between `y` and `z`
is exactly the response the sequential specification produces from the state
reached after `y`.  Its occurrence number is `y.count a`. -/
theorem responses_occurrence [DecidableEq Op] (a : Op) (y z : List Op) (q : State) :
    (obj.responses a (y ++ a :: z) q)[y.count a]? =
      some (obj.step a (obj.finalState y q)).1 := by
  rw [obj.responses_append,
    List.getElem?_append_right (Nat.le_of_eq (obj.responses_length a y q)),
    obj.responses_length]
  simp [responses]

/-- Positional form: if the letter at position `p` of a schedule `x` is `a`, then the
`(x.take p).count a`-th occurrence of `a` has as response the value produced by
`obj.step` from the state reached by the prefix `x.take p`.  This is the legality
of the sequential history `S_{\hat t}` of main.tex. -/
theorem responses_getElem_occurrence [DecidableEq Op] (a : Op) (x : List Op) (q : State)
    (p : Nat) (hp : p < x.length) (ha : x[p] = a) :
    (obj.responses a x q)[(x.take p).count a]? =
      some (obj.step a (obj.finalState (x.take p) q)).1 := by
  have hx : x = x.take p ++ a :: x.drop (p + 1) := by
    rw [← ha, ← List.drop_eq_getElem_cons hp, List.take_append_drop]
  have h := obj.responses_occurrence a (x.take p) (x.drop (p + 1)) q
  rwa [← hx] at h

/-- Occurrence responses of a trace are read off any of its representatives. -/
theorem traceReturn_representative [DecidableEq Op] {t : obj.Trace} {x : List Op}
    (hx : Quotient.mk obj.traceSetoid x = t) (a : Op) (j : Nat) :
    obj.traceReturn a j t = (obj.responses a x obj.initial)[j]? := by
  subst hx
  rfl

/-- The paper's `\ret^*(cmd(\Phi), \hat t)`: the `j`-th occurrence of `a` in a
representative `x` of `t`, located at position `p`, returns the value the
sequential specification produces at that point, and this value is
`obj.traceReturn a j t`. -/
theorem traceReturn_of_representative [DecidableEq Op] {t : obj.Trace} {x : List Op}
    (hx : Quotient.mk obj.traceSetoid x = t) (a : Op) (p : Nat)
    (hp : p < x.length) (hap : x[p] = a) :
    obj.traceReturn a ((x.take p).count a) t =
      some (obj.step a (obj.finalState (x.take p) obj.initial)).1 := by
  rw [obj.traceReturn_representative hx]
  exact obj.responses_getElem_occurrence a x obj.initial p hp hap

/-- The full chain of equalities used in the proof of `theorem:weakUCLin`:
`\ret^*(cmd(\Phi),s) = \ret^*(cmd(\Phi),t) = \ret^*(cmd(\Phi),\hat t)`, where `s` is
the trace read by the operation at some round `k`, `t` the final committed trace and
`\hat t` a representative of it. -/
theorem traceReturn_chain_representative [DecidableEq Op] (t : Nat → obj.Trace) (m : Nat)
    (hmono : ∀ j, j < m → obj.TracePrefix (t j) (t (j + 1)))
    {x : List Op} (hx : Quotient.mk obj.traceSetoid x = t m)
    (a : Op) (j k : Nat) (hkm : k ≤ m)
    (hj : j < (obj.traceResponses a obj.initial (t k)).length) :
    obj.traceReturn a j (t k) = (obj.responses a x obj.initial)[j]? := by
  rw [obj.traceReturn_stable_along_chain t m hmono hkm a j hj]
  exact obj.traceReturn_representative hx a j

end ConflictFreedom.Object
