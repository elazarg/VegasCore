# Proof compression and common observation migration

The baseline is afda6834. Measurements include complete owning modules and all
added helpers, adapters and fixtures. A shorter caller alone is insufficient
evidence of compression. GameTheory remains unchanged. Existing theorem scopes,
joint observations, common assessment witnesses, service quantifiers and payoff
semantics are retained unless a separately approved semantic change is specified.

## Preservation assembly

| Complete module | Baseline lines | Accepted lines | Difference |
| --- | ---: | ---: | ---: |
| RecoveryOnePacketPreservation | 196 | 184 | -12 |
| SequentialPhasePreservation | 220 | 204 | -16 |
| Total | 416 | 388 | -28 |

Both callers already instantiate the same model-independent local-comparison
limit theorem. Their repeated comparison-result types are inferred from the
actual producer. Each proof binds the two combined-floor facts once and reuses
them throughout perturbation calibration. No helper, declaration or import is
added. The complete theorem prefixes remain identical to the baseline.

The zero-slot branch retains the empty-player case: its contradiction uses a
player introduced by the comparison quantifier and that player's existing
capacity hypothesis. No inhabited-player assumption is introduced. The common
completion, free-site optimality, original payoff bounds, supported exclusion
clearance and full joint law are unchanged. Both owners pass their strict
source checks and normal builds.

A separate generic assembly wrapper is rejected. The existing
[local-comparison limit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean)
already proves the substantive uniform-gain, common-limit and one-shot steps.
An additional wrapper would repeat its premises while leaving the concrete
observation, local-gain and clearance adapters in both callers. No shared
mathematical inference was identified for it to own. A public bundled-scale
wrapper is also unnecessary; binding the existing floor facts locally removes
the repetition without a new API. These decisions and the checked compression
are retained on experiment/consolidation-assembly.

## Posterior pilot

The full-law qualified-binding posterior declaration shrinks from 129 to 109
lines and its proof from 82 to 62. Its complete StoppedPayoff owner shrinks from
2,078 to 2,058 lines. The actual annotated-payoff consumer is checked in that
same owner. There are no additional helpers, adapters, fixtures or hypotheses.
Together the two pilots remove 48 lines.

The new power/tensor replacement is rejected for this consumer. It needs full
conditioned laws and atom identities after arbitrary continuation kernels,
under its original multirate sequence. The existing restricted-disintegration
API already provides that stronger result. A selected-expectation certificate
would need a separating observable family and a genuine callback/transcript
adapter; power completeness does not preserve the original stagewise rates.
The [dedicated experiment](experiments/posterior-consolidation.md) records this
boundary, cost and accepted fallback. No unimplemented certificate adapter is
counted as a saving.

## Common result observation and money

[TerminalObservation](../Vegas/Game/TerminalObservation.lean) replaces the
concurrent-specific carrier. The asynchronous client laws, concurrent raw
preservation and sequential monetary preservation use the same fixed reader:
original inputs, optional complete typed terminal state, public result and the
entire vector. Utility and cash interpretations remain explicit reader maps.

[TerminalObservationLaws](../Vegas/Game/TerminalObservationLaws.lean) proves
lossless recoding of the previous complete state/vector pair. Event
probabilities, expectations, integrability and total-variation comparisons
recover exactly through the projection. No right inverse is asserted for an
arbitrary incoherent four-field record. The arbitrary source profiles,
including source unilateral deviations represented by those profiles, and the
timing error and audit hypotheses of the client-law
guarantees remain unchanged. This interface migration adds 92 lines across its
new law owner and client module; it is measured separately from compression.

The existing quasi-linear settlement owner supplies one supportwise cash
inversion for the same actual correlated audit. Recovery uses it directly;
the mode-generic phase adapter adds the corresponding interpretation. The
concurrent target cash law drops its unnecessary zero-charge premise: actual
audit deductions commute with valuation addition and subtraction. Its
no-exclusion premise remains, and the original SE theorem still proves clean
equilibrium paths.

[SequentialPhasePaymentPreservation](../Vegas/Game/SequentialPhasePaymentPreservation.lean)
retains the original physical service, source equilibrium, conditional-input,
finiteness, funding and valuation-bound guards. It preserves the original joint
utility law and adds the joint cash law. Global failed-outcome valuation and
payment assumptions are unnecessary: the actual intended-history identity
handles the reference law, and actual no-exclusion support handles the target.
The two phase SE environments retain their different sufficient assumptions.

## Chosen source settlement and operational game

The owner selected permanent exit with observed commitment-phase retries and
program-declared exit transfers. Setup therefore requires an explicit integer
exit-transfer vector. All thirteen concrete constructors declare one; the
bounded-payment auction uses its negative penalty, the actual source-exit
regression declares minus one, and the remaining eleven use zero.
There is no default or compatibility wrapper.

[Source settlement](../Vegas/Source/Settlement.lean) pays the declared exit
amount on actual exclusion and evaluates the original ret instructions for
other players. Integer transfer aggregation has a lower mathematical owner,
so source settlement does not import audit analysis. The
[compiled reader](../Vegas/Compile/EventGraphCash.lean) independently evaluates
the actual native terminal payoff expressions. Its equality with source cash
holds for every structural configuration and execution mode, without history,
honesty or service premises. The actual physical excluded set is used, rather
than latent failed bindings. [PhaseCash](../Vegas/Game/PhaseCash.lean) connects
this integer reader to the existing real-valued correlated-audit settlement.
Real audit deposits and receipts retain their existing generality; this is not
an EVM balance or escrow-execution theorem.

[SourcePhaseGame](../Vegas/Game/SourcePhaseGame.lean) uses the existing source
exit/retry kernel and its proved horizon directly. It adds declared cash to
separate full-history valuation, without a second transition semantics or
automatic valuation clipping. An actual initialized withholding example proves
permanent exclusion, actual declared cash of minus one, unchanged valuation
of seven giving utility six, and only silence at the later information value.
Preservation for a chosen valuation still needs its
information-factorization hypotheses.

## Migration boundary and measurements

[FailureContinuationScope](../Vegas/Examples/FailureContinuationScope.lean)
compares actual interfaces: value-only source admission permits withholding
followed by a same-owner choice changing executable ret cash from zero to one.
An actual phase history retaining that failure cannot authorize the later
binding, including a packet prepared in advance. This obstructs the direct
failure/readiness/choice-preserving adapter. It is not a blanket Nash or
arbitrary terminal-law impossibility theorem. The continuing-source Nash
family remains available and is not relabelled as preservation for the chosen
operational game.

Across the six library directories, the measured additions are 1,117 production
lines and 49 fixture lines relative to afda6834, including the 48-line pilot
reduction. Two root-aggregator import lines are outside those directory counts.
The independent main-branch Paper cleanup is excluded from the compression
claim. These are useful semantic-interface and cash-law additions, not a net
tree-size reduction or evidence for a fourfold proof compression.

The [common semantic contract](common-semantics-contract.md) records the chosen
policy and remaining ports. The full source/phase strategy-information
correspondence and Nash port remain prerequisites for retiring parallel
contracts. A new shared observation or source-game definition does not discharge
those obligations, or strengthen intended-SE preservation to preservation of
every full-source equilibrium.

## Verification

The full warning-strict default build passes all 5,995 jobs, including Paper,
all library roots and all example/test aggregators. The module-boundary,
source-policy and documentation checks pass, as do all 111 Python tests.
Paper retains only manuscript-mentioned mathematical results; these library
additions do not add unrelated axiom pins. GameTheory remains at
8bb3fc270f716b07686f429ee0714e7ee4ea614e with a clean working tree.
