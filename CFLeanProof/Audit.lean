import CFLeanProof

/-! Axiom report for every result stated in `Paper.lean`, in its order. Each
depends on no axiom beyond `propext`, `Classical.choice` and `Quot.sound`;
`KernelAudit.lean` enforces this for every project declaration. -/

#print axioms ConflictFreedom.Paper.commuteAt_iff
#print axioms ConflictFreedom.Paper.conflict_iff
#print axioms ConflictFreedom.Paper.correct_iff
#print axioms ConflictFreedom.Paper.solo_iff
#print axioms ConflictFreedom.Paper.eventuallyConflictFree_iff
#print axioms ConflictFreedom.Paper.waitFree_iff
#print axioms ConflictFreedom.Paper.lockFree_iff
#print axioms ConflictFreedom.Paper.obstructionFree_iff
#print axioms ConflictFreedom.Paper.definition3_1
#print axioms ConflictFreedom.Paper.definition3_2
#print axioms ConflictFreedom.Paper.proposition3_3
#print axioms ConflictFreedom.Paper.proposition3_4_full
#print axioms ConflictFreedom.Paper.proposition3_4_empty
#print axioms ConflictFreedom.Paper.scheduleEquiv_iff
#print axioms ConflictFreedom.Paper.traceEq_iff_scheduleEquiv
#print axioms ConflictFreedom.Paper.lemma4_1
#print axioms ConflictFreedom.Paper.lemma4_2
#print axioms ConflictFreedom.Paper.gca_validity
#print axioms ConflictFreedom.Paper.gca_adoption
#print axioms ConflictFreedom.Paper.gca_commitment
#print axioms ConflictFreedom.Paper.gca_convergence
#print axioms ConflictFreedom.Paper.gca_commonPrefix
#print axioms ConflictFreedom.Paper.gca_weakAgreement
#print axioms ConflictFreedom.Paper.isGCA_iff
#print axioms ConflictFreedom.Paper.soloAgreement_iff
#print axioms ConflictFreedom.Paper.algorithm1Over_iff
#print axioms ConflictFreedom.Paper.theorem4_3
#print axioms ConflictFreedom.Paper.theorem4_4
#print axioms ConflictFreedom.Paper.theorem5_1
#print axioms ConflictFreedom.Paper.lemmaA_2
#print axioms ConflictFreedom.Paper.lemmaA_3
#print axioms ConflictFreedom.Paper.lemmaA_4
#print axioms ConflictFreedom.Paper.lemmaA_5
#print axioms ConflictFreedom.Paper.lemmaA_6
#print axioms ConflictFreedom.Paper.lemmaA_7
#print axioms ConflictFreedom.Paper.lemmaA_8
#print axioms ConflictFreedom.Paper.algorithm2_isGCA
#print axioms ConflictFreedom.Paper.algorithm2_soloAgreement
#print axioms ConflictFreedom.Paper.algorithm3Over_iff
#print axioms ConflictFreedom.Paper.lemma6_1
#print axioms ConflictFreedom.Paper.lemma6_2
#print axioms ConflictFreedom.Paper.eventuallyWeaklyConflictFree_iff
#print axioms ConflictFreedom.Paper.definition7_3
#print axioms ConflictFreedom.Paper.definition7_1
#print axioms ConflictFreedom.Paper.theorem7_2
#print axioms ConflictFreedom.Paper.theorem7_4
#print axioms ConflictFreedom.Paper.lemmaA_1_alg1
#print axioms ConflictFreedom.Paper.lemmaA_1_alg3
#print axioms ConflictFreedom.Paper.theorem4_4_machine
#print axioms ConflictFreedom.Paper.lemma6_2_machine
