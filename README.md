# Conflict-Freedom as a Progress Condition: a Lean Formalization

A Lean 4 formalization of *Conflict-Freedom as a Progress Condition* [1], in the
extended version included here as [`main.tex`](main.tex).

It formalizes the model of the paper and proves every numbered result:

- **Theorem 4.4.** Algorithm 1 is a weakly conflict-free universal construction.
- **Lemma 6.2.** Algorithm 3 is a conflict-free universal construction.
- **Theorem 4.3 and Lemma 6.1.** Both constructions are linearizable, for the
  whole, possibly infinite, history of every run.
- **Theorems 7.4 and 7.2** (conflict forgetting and conflict resolution). Every
  finite execution of Algorithm 1 (resp. 3) has a finite conflict-forgetting
  (resp. conflict-resolving) solo extension.
- **Theorem 5.1 and Lemmas A.2 to A.8.** Algorithm 2 meets the GCA
  specification, and Solo agreement.
- **Propositions 3.3 and 3.4, Lemmas 4.1, 4.2 and A.1** — the progress
  hierarchy, the degenerate conflict relations, and the trace facts the
  constructions rest on.

Algorithms 1 and 3 are proved correct over *any* GCA objects meeting the
specification of §4.2, used as a black box, as the paper does; Algorithm 2 is
proved to be one. The algorithms are also run as deterministic machines — for
every client, every scheduler, and every resolution of the choices the paper
leaves open — and every non-halting run is shown to be an execution the theorems
cover.

Every proof uses only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), with no `sorry`.
[`KernelAudit.lean`](CFLeanProof/KernelAudit.lean) checks this for every project
declaration and fails otherwise.

## Where to start

Read [`CFLeanProof/Paper.lean`](CFLeanProof/Paper.lean). It states each result
in the paper's terms, next to the paper's own wording, and proves it from the
rest of the development. [`MODEL.md`](MODEL.md) explains the formal model and
how it corresponds to the paper.

## Building

```sh
lake build
lake env lean CFLeanProof/KernelAudit.lean
lake env lean CFLeanProof/Audit.lean
```

`lake build` checks every module imported by
[`CFLeanProof.lean`](CFLeanProof.lean). `KernelAudit.lean` fails if any file
under `CFLeanProof/` is not imported, or if any project declaration uses an
axiom beyond the three above; `Audit.lean` prints the axioms of each result
stated in `Paper.lean`. CI runs all three. The development uses Lean 4.34.0 and its
standard library only, pinned by `lean-toolchain`.

## The results

The Lean statements are in [`CFLeanProof/Paper.lean`](CFLeanProof/Paper.lean),
named after the paper's numbering (`theorem4_4`, `lemmaA_1_alg1`, …). As in the
paper, the results about Algorithms 1 and 3 hold over any implementation of the
GCA objects that meets the specification of §4.2 and, for Theorem 7.4, Solo
Agreement. Algorithm 2 is proved to be one
([`CFLeanProof/GCAMachineAlgorithm2.lean`](CFLeanProof/GCAMachineAlgorithm2.lean)).

| Paper | Proof |
|---|---|
| Definitions 3.1 and 3.2 (conflict-freedom and weak conflict-freedom) | [`CFLeanProof/Progress.lean`](CFLeanProof/Progress.lean) |
| Proposition 3.3 (wait-freedom ⟹ conflict-freedom ⟹ weak conflict-freedom ⟹ obstruction-freedom) | [`CFLeanProof/Progress.lean`](CFLeanProof/Progress.lean) |
| Proposition 3.4 (if every pair of operations conflicts, both conditions are obstruction-freedom; if none does, they are wait-freedom and lock-freedom) | [`CFLeanProof/Progress.lean`](CFLeanProof/Progress.lean) |
| Lemma 4.1 (equivalent schedules give every operation the same response) | [`CFLeanProof/Sequential.lean`](CFLeanProof/Sequential.lean) |
| Lemma 4.2 (extending a trace does not change the responses of its operations) | [`CFLeanProof/TraceOrder.lean`](CFLeanProof/TraceOrder.lean) |
| §4.2: the GCA specification | [`CFLeanProof/GCA.lean`](CFLeanProof/GCA.lean) |
| Theorem 4.3 (Algorithm 1 is linearizable) | [`CFLeanProof/Algorithm1OverGCA.lean`](CFLeanProof/Algorithm1OverGCA.lean) |
| Theorem 4.4 (Algorithm 1 is weakly conflict-free) | [`CFLeanProof/Algorithm1OverGCA.lean`](CFLeanProof/Algorithm1OverGCA.lean) |
| Theorem 5.1 (Algorithm 2 implements GCA) | [`CFLeanProof/GCAProtocol.lean`](CFLeanProof/GCAProtocol.lean) |
| Lemma 6.1 (Algorithm 3 is linearizable) | [`CFLeanProof/Algorithm3OverGCA.lean`](CFLeanProof/Algorithm3OverGCA.lean) |
| Lemma 6.2 (Algorithm 3 is conflict-free) | [`CFLeanProof/Algorithm3OverGCA.lean`](CFLeanProof/Algorithm3OverGCA.lean) |
| Definition 7.1 and Theorem 7.2 (every finite execution of Algorithm 3 has a conflict-resolving solo extension) | [`CFLeanProof/Algorithm3OverGCA.lean`](CFLeanProof/Algorithm3OverGCA.lean) |
| Definition 7.3 and Theorem 7.4 (every finite execution of Algorithm 1 has a conflict-forgetting solo extension) | [`CFLeanProof/Algorithm1OverGCA.lean`](CFLeanProof/Algorithm1OverGCA.lean) |
| Lemma A.1 (a trace committed in some round is a prefix of every trace returned in that round or a later one) | [`CFLeanProof/PrefixRounds.lean`](CFLeanProof/PrefixRounds.lean) |
| Lemmas A.2 to A.7 (Algorithm 2 satisfies Adoption, Commitment, Convergence, Common Prefix, Weak Agreement and Validity) | [`CFLeanProof/GCASnapshot.lean`](CFLeanProof/GCASnapshot.lean) |
| Lemma A.8 (Algorithm 2 satisfies Solo Agreement) | [`CFLeanProof/GCASoloAgreement.lean`](CFLeanProof/GCASoloAgreement.lean) |

Theorem 4.4 and Lemma 6.2 also hold for the algorithms run over Algorithm 2 as
deterministic machines
([`CFLeanProof/ForwardUniversal.lean`](CFLeanProof/ForwardUniversal.lean),
[`CFLeanProof/ForwardHelping.lean`](CFLeanProof/ForwardHelping.lean)).

Concrete runs show that the hypotheses can be met: they exercise contention,
helping, two callers in one GCA round and the adopt branch of Algorithm 2, and
the hypotheses of the §7 definitions are satisfiable. The local trace
calculations (`⊓`, `⊔`, compatibility, the GCA outputs) are programs for every
object whose independence relation is decidable, and the kernel evaluates the
machines on them.

## Assumptions

Two, both from the paper's model ([`MODEL.md`](MODEL.md#assumptions)).

- **A local computation is one step.** The trace calculations are therefore
  classical functions in general, and programs whenever independence is
  decidable.
- **Snapshot objects.** Algorithm 2 runs on atomic snapshot objects. The one
  fact taken from the literature is that Algorithm 2 still meets the GCA
  specification and Solo Agreement when these are replaced by a wait-free
  linearizable implementation from read/write registers (Afek et al., 1993). No
  Lean theorem uses it: the theorems over any GCA take those two properties as
  hypotheses, so a proof of the fact would plug in unchanged.

## Layout

```text
CFLeanProof.lean            imports the development
CFLeanProof/
  Paper                     every result of the paper, in its terms
  Sequential, Trace*        objects, conflicts; the trace order, lattice and
                            compatibility (§4.1)
  Execution, Progress       executions and the progress conditions (§3)
  GCA*, ForwardGCA          the GCA specification and Algorithm 2 (§4.2, §5, App. A)
  WeakUniversal,            Algorithms 1 and 3 as transition systems
    HelpingUniversal
  GlobalSchedule,           runs of the constructions over any GCA
    Universal*, Helping*
  Algorithm1*, Algorithm3*  liveness, and every result over any GCA implementation
  Forward*                  the algorithms as deterministic machines
  WeakUCResolve, UCResolve  §7: conflict forgetting and conflict resolution
  *Linearization            safety, on finite and infinite event histories
  *Witness                  concrete runs showing the hypotheses have content
  Counterexamples           why the definitions read as they do
  Audit, KernelAudit        the axiom report and the module and axiom checks
main.tex                    the paper, extended version
MODEL.md                    the formal model, and how it corresponds to the paper
```

## License

[CC BY 4.0](LICENSE).

## References

- [1] Petr Kuznetsov, Pierre Sutra, Guillermo Toyos-Marfurt. Conflict-Freedom
  as a Progress Condition. In *Proceedings of the 2026 ACM Symposium on
  Principles of Distributed Computing (PODC '26)*, Egham, United Kingdom, 2026.
  [doi:10.1145/3796701.3815956](https://doi.org/10.1145/3796701.3815956).
