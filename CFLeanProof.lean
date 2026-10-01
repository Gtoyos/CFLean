import CFLeanProof.Sequential
import CFLeanProof.SharedMemory
import CFLeanProof.Execution
import CFLeanProof.Progress
import CFLeanProof.Counterexamples
import CFLeanProof.TraceOrder
import CFLeanProof.GCA
import CFLeanProof.TraceAlgebra
import CFLeanProof.TraceHeads
import CFLeanProof.TraceErase
import CFLeanProof.TraceLattice
import CFLeanProof.TracePresentation
import CFLeanProof.TraceOccurrences
import CFLeanProof.TraceCompatibility
import CFLeanProof.FiniteChain
import CFLeanProof.TraceRepresentatives
import CFLeanProof.GCACandidate
import CFLeanProof.GCAOutput
import CFLeanProof.EffectiveInterface
import CFLeanProof.FreeTraceCompute
import CFLeanProof.DecidableTraceCompute
import CFLeanProof.GCASnapshot
import CFLeanProof.GCATimed
import CFLeanProof.UniversalRounds
import CFLeanProof.GCAConsequences
import CFLeanProof.GCAProtocol
import CFLeanProof.GCASoloAgreement
import CFLeanProof.ForwardGCA
import CFLeanProof.Commands
import CFLeanProof.InvocationLedger
import CFLeanProof.WeakUniversal
import CFLeanProof.HelpingUniversal
import CFLeanProof.UniversalIdentities
import CFLeanProof.UniversalRoundTracking
import CFLeanProof.InvocationTiming
import CFLeanProof.UniversalProtocol
import CFLeanProof.ProtocolInterleaving
import CFLeanProof.UniversalFiniteHistory
import CFLeanProof.UniversalComposition
import CFLeanProof.ProgressCompatibility
import CFLeanProof.SharedScheduler
import CFLeanProof.SnapshotStutter
import CFLeanProof.GlobalSchedule
import CFLeanProof.PrefixRounds
import CFLeanProof.UniversalProgress
import CFLeanProof.WeakConflictFreedom
import CFLeanProof.UniversalLiveness
import CFLeanProof.UniversalImplementation
import CFLeanProof.HelpingProgress
import CFLeanProof.HelpingConflictFreedom
import CFLeanProof.HelpingConflictFree
import CFLeanProof.ConflictResolution
import CFLeanProof.WeakConflictForgetting
import CFLeanProof.Enabledness

/- Checked supplementary results; see the module for the proof boundary. -/

/- Linearizability of the two universal constructions: the finite-history
   argument, its instantiation for both programs, the derivation of
   chronological occurrence provenance from causal GCA validity, and a
   completing witness run. -/
import CFLeanProof.FiniteLinearization
import CFLeanProof.UniversalLinearization
import CFLeanProof.GCACausality
import CFLeanProof.UniversalProvenance
import CFLeanProof.CausalLinearization
import CFLeanProof.Algorithm2Interface
import CFLeanProof.LinearizationWitness

/- An infinite fair, operation-live run of Algorithm 1, and the resulting §3
   implementation wrapper with obstruction-freedom. -/
import CFLeanProof.FairnessClock
import CFLeanProof.ProgressWitness
import CFLeanProof.HelpingWitness
import CFLeanProof.HelpingImplementation
import CFLeanProof.Algorithm1
import CFLeanProof.Algorithm3
import CFLeanProof.HelpingInvariantTwo
import CFLeanProof.Algorithm3ConflictFree
import CFLeanProof.Algorithm1WeakConflictFree
import CFLeanProof.ContentionWitness
import CFLeanProof.WeakContentionWitness
import CFLeanProof.SharedRoundWitness
import CFLeanProof.ForwardUniversal
import CFLeanProof.ForwardHelping

/- §7 for Algorithm 1: GCA Solo agreement (property 7) and Algorithm 2's proof
   of it, and Theorem `th:WeakUCresolve` — every finite execution of the
   machine has a finite conflict-forgetting solo extension. -/
import CFLeanProof.WeakUCResolve

/- §7 for Algorithm 3: invocation points — where in an operation's code its
   invocation is placed, a free choice; `th:cr` places it at Line 5, the write of
   the command into `M` — and Theorem `th:cr`: every finite execution of the
   machine has a finite conflict-resolving solo extension (the argument inside
   one run is `ConflictResolution`). -/
import CFLeanProof.InvocationPoint
import CFLeanProof.UCResolve

/- GCA objects given by an implementation: an abstract GCA machine, the
   specification of §4.2 and Solo agreement for every run of it, Algorithm 2 as
   one such machine, and both constructions run over any machine meeting the
   specification — with Theorems `th:WeakUCresolve` and `th:cr` in the
   manuscript's form, "every finite execution has a finite solo extension that
   is conflict-forgetting (resp. conflict-resolving)". -/
import CFLeanProof.GCAMachine
import CFLeanProof.GCAMachineAlgorithm2
import CFLeanProof.Algorithm1OverGCA
import CFLeanProof.Algorithm3OverGCA
import CFLeanProof.MachineCompute
import CFLeanProof.AdoptWitness

/- Histories as literal invocation/response event sequences: the manuscript's
   own presentation, the event sequence of an actual run, and the paper's
   definition of linearizability discharged for both constructions — for every
   finite prefix, and for the whole, possibly infinite, history of a run. -/
import CFLeanProof.EventHistory
import CFLeanProof.LedgerEvents
import CFLeanProof.UniversalEventLinearization
import CFLeanProof.InfiniteHistory
import CFLeanProof.InfiniteEventLinearization

/- The GCA interface the constructions use: the six properties, coverage, and
   causal validity; Algorithm 2 meets it, Algorithm 3 needs causal validity
   (a counterexample without it), Algorithm 1 does not once the GCA history is
   the run's own. -/
import CFLeanProof.WeakCoveredLinearization
import CFLeanProof.NonCausalWitness
import CFLeanProof.GCAInterface

/- Every numbered result of the paper, stated in its terms next to its wording. -/
import CFLeanProof.Paper
