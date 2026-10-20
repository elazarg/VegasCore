# Concurrent raw preservation: contract and usable code

The semantic target is
[`Vegas.ConcurrentRawSequentialPreservation`](../Vegas/Game/ConcurrentRawSequentialPreservation.lean).
It is a proposition, not a preservation theorem. It fixes the concurrent graph,
actual phase runtime, one unconditional exogenous tape prior for the whole
execution (correlated across owners/time), observation rule, resource
bounds, utility, exclusion settlement and authentic audit before quantifying over
intended source sequential equilibria. Its conclusion uses the actual raw game
and terminal audit settlement, preserving the **joint** law of the complete
initial source state, typed terminal state, public result and entire realized net
payoff vector. Exclusions and collected audit charges vanish on supported paths.

`ReservedConcurrentImplementation` names the fixed runtime, observation rule,
resource bounds, phase plan and unconditional tape prior. `ConcurrentPayoffs`
names the source utility, its bounds and exclusion floor; `ConcurrentCountAudit`
names the authentic evidence service and settlement funding. Implementation
`Valid` means exactly `Operational`, payoff `Bounded` and audit `Funded`
together. The top-level proposition therefore reads: every valid fixed
implementation preserves every intended source equilibrium. Its
`PreservesAssessment` conclusion names the raw equilibrium, one joint law of
`ConcurrentTerminalObservation`, and supportwise zero exclusions and charges.

The [hypothesis instance](../VegasTests/ConcurrentRawHypotheses.lean) checks
joint validity for two concurrently ready owners,
both supported activation orders, nonconstant utilities and a funded authentic
audit. It also supplies an intended source equilibrium witness. It proves
joint satisfiability of the assumptions, not the preservation conclusion.

The original setup law remains an arbitrary joint law with finite support, and
binding types are finite. The tape prior is not refreshed from block-entry
public data; Bayesian posterior updates condition the same original tape.
Public-prefix-adaptive block priors are outside this contract. There is
no independent-private-cell hypothesis. The
[likelihood derivation](se-concurrent-likelihood.md) retains its literal atom in
the replay and source weights; the [independent review](se-concurrent-likelihood-review.md)
accepts that mathematical argument. The Lean transport theorem is still open.

The initial-coordinate reader is fixed by the implementation, not supplied by a
caller. `phaseProposalUnflagged_initialized_terminal_coupling` in
[`PhaseProposalInitializedTerminal`](../Vegas/Game/PhaseProposalInitializedTerminal.lean)
identifies the recovered initial state with the literal original draw on every
supported pair. Its joint-readout theorem preserves that coordinate together
with exclusions, the complete typed state and whole base-payoff vector.

The mathematical reviews are independent agent reviews with a root-agent
model audit. They are not human review or a Lean proof.

## Existing checked owning APIs

These public components can be instantiated within their stated hypotheses;
none supplies the missing initialized conditional-belief comparison by itself.

| Component | Actual reusable conclusion |
| --- | --- |
| [`IntendedPreservation`](../Vegas/Game/IntendedPreservation.lean), [`ProposalRecoveryEquilibriumConstruction`](../Vegas/Game/ProposalRecoveryEquilibriumConstruction.lean) | Intended assessment extension and one enriched source equilibrium construction. |
| [`ReservedEpochResources`](../Vegas/Pending/ReservedEpochResources.lean), [`ReservedEpochCompletion`](../Vegas/Pending/ReservedEpochCompletion.lean) | Actual reserved-service completion and fresh-candidate reserves under explicit tape gap and deadline conditions. |
| [`PhaseProposalInitializedTerminal`](../Vegas/Game/PhaseProposalInitializedTerminal.lean), [`PhaseProposalInitializedLawError`](../Vegas/Game/PhaseProposalInitializedLawError.lean) | Original initialized joint readout and perturbation error for the specified native policies. |
| [`PhaseProposalCommonPerturbations`](../Vegas/Game/PhaseProposalCommonPerturbations.lean), [`PhaseProposalConsistentSequence`](../Vegas/Game/PhaseProposalConsistentSequence.lean) | Shared rate choices, actual Bayes assessments, source convergence and vanishing joint-law errors; native optimality remains separate. |
| [`ProposalRecoveryPublicClassFactorization`](../Vegas/Game/ProposalRecoveryPublicClassFactorization.lean), [`ProposalRecoveryPublicClassConstancy`](../Vegas/Game/ProposalRecoveryPublicClassConstancy.lean) | Actual source reach factors and a source-information-measurable class coefficient on the specified regular slice. Original initializer mass and focal own reach remain separate. |
| [`PhaseProposalNativeSourceInformation`](../Vegas/Game/PhaseProposalNativeSourceInformation.lean) | Full source information agrees for actual matched preimages with equal complete native information. This gives uniqueness, not all-preimage coverage or weights. |
| [`PhaseProposalPublicationGain`](../Vegas/Game/PhaseProposalPublicationGain.lean), [`PhaseProposalCurrentBindingGain`](../Vegas/Game/PhaseProposalCurrentBindingGain.lean) | Publication comparisons and binding comparisons on the stated failure/debt/reset branches. Clean binding comparisons remain open. |
| [`LocalSimulationLimit`](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean) | Native equilibrium and law limits once the required local comparisons are proved. |
| [`PhaseOnePacketExtension`](../Vegas/Game/PhaseOnePacketExtension.lean) | `PhaseCount.onePacket_raw_sequentialEquilibrium` extends a counted equilibrium to raw play, preserving both terminal history and realized-payoff joint laws, with zero charges. |

The convenience theorem in
[`PhaseRawReadoutLaw`](../Vegas/Game/PhaseRawReadoutLaw.lean) projects away the
history marginal. Final assembly should retain the inner extension theorem's
history and settlement laws until the fixed initialized joint readout is taken.

## Unadopted work and approaches to retire

Private conditional frontier/cursor laws, scalar callback identities and runtime
provenance adaptations require ordinary in-tree integration and checks before
use. A conditional law supplied with a cursor does not prove that every source
explanation of a native information set has an actual preimage or the required
weight. An authored but deliberately failing global file is not a checked
consumer of these pieces.

Custom provider selection, immutable compiler captures and repeated broad proof
prefix checks are not part of the intended build architecture. Use ordinary
imports and Lake. Archive the old machinery rather than extending it. Do not
promote unused global historical inverse/namespace traversals merely because
they were checked. Fixed-entry and parent-following completion constructions
must not both become permanent APIs without a demonstrated caller and an exact
projection relationship. No compatibility aliases are needed.

## Smallest justified remaining interfaces

The external contract needs local deviation comparisons, not independence from
every retained mechanical detail. The full product factorization over all
mechanical histories exceeds the required comparison. The narrower route needs,
at an actual ready, unsent binding input without saved or current own debt:

1. Weighting the native regular measure by the clean binding-admission gate
   gives a **common scalar** times the source conditional measure on source past
   and foreign future word, uniformly over proper typed current encodings.
   Neither an unweighted posterior identity nor a per-mechanical product law is
   required. A hidden-future-dependent gate cannot be replaced by its mean.
2. A literal current response inserts its typed value into the **actual** causal
   completion kernel, resampling only the remaining focal chain, with the
   supported terminal payoff correspondence required by the gain comparison.

These are internal proof interfaces, not additional capstone assumptions or
checked results. The [mathematical derivation](se-concurrent-likelihood.md) and
[review](se-concurrent-likelihood-review.md) specify their proof boundary.
Any derivation must retain arbitrary correlated initial inputs,
accepted and canceled focal failures, actual disclosure-cause classes, retained
archives, raw aliases, WAIT, and zero-mass cases. It must obtain support and
normalization from the initialized runtime rather than from counterpart
uniqueness. If the weaker interfaces cannot be derived, isolate the exact local
failure before introducing a stronger invariant.

After those comparisons, the existing shared-sequence/limit and raw-audit APIs
can perform the final assembly. Proving that assembly and the unresolved
likelihood/gain interfaces is outside this contract-and-inventory deliverable.

## Focused implementation boundary

Keep the unadopted 4,366-line initialized-fiber draft and its selected private
dependency set out of the active build. They are archived research, not a batch
of modules awaiting automatic promotion. In particular, the all-mechanical
factorization and its second annotated runner are not the chosen acceptance
criterion. Private helper proofs are reusable only after identifying an actual
caller under the simpler argument's hypotheses.

The replay construction uses existing boundaries directly: foreign aliases via
the reference-response projection; source queries via the typed-view/control/
address/archive reader; historical masks via complete source public signals;
and current/saved stores via the actual save/restore transitions. It needs no
global historical namespace inverse or equality of full canonical and latent
labeled histories. Preserve the entire focal catalogue and raw past separately.
The phase finishes all events before retry, so a surviving focal player cannot
have an unsubmitted historical commitment silently filled by a virtual choice.

These obligations belong to cohesive probability and operational components,
with the final gain consumer above both. They do not justify another parallel
hierarchy of per-field wrapper modules. Existing checked NE and serial-SE
implementations remain regressions until an explicit common-runtime replacement
is proved; deleting them would not establish that replacement.
