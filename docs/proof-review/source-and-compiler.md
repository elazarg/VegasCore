# Source, compiler, examples and proof engineering

This review covers the complete declaration surfaces of Foundation, Expr,
Source and Compile: 272 tracked files and 45,220 physical lines. Directory
aggregators are counted separately in the main report. Examples, regression tests,
the public Paper surface and repository checks were also screened. Deep reads
targeted the compiler's execution, backtranslation, observation codec and suffix
proofs; source purification, protocol policies, failed-binding and intended
invariants; the largest repair inductions; and the auction/payment/runtime
examples. Inventory is exhaustive; body review is selective.

The [main report](../proof-review.md) gives the coverage boundary, checked
experiments and overall priorities. None of the proposals below changes source
failure, exit, retry, observation or payment semantics.

## 1. Factor the legal action translation inside the two repair inductions

[Binding replay](../../Vegas/Source/CommitRecoveryBindingReplay.lean) and
[preparation repair](../../Vegas/Source/ProposalRecoveryPreparationRepairStep.lean)
contain 304 and 403 lexical proof-body lines respectively. The inventory finds
94 shared eight-line windows between these files. Windows overlap; that number
is neither a line saving nor a proof of full semantic equivalence.

The reveal branches construct the same translated joint action, prove it
unchanged at foreign players, prove legal availability and show its disclosure
readback. Their current differences concern how the repaired configuration and
its disclosure are produced. Extract these **action-level** facts with explicit
actor, excluded-set, disclosure and foreign-player premises. Keep each concrete
configuration relation, prepared-value calculation, history and final successor
proof in its caller. The scalar/legal-action kernel should not assume the whole
desired repaired execution law.

This is a medium-risk, high-confidence duplication finding. A plausible net
reduction is 60–130 source lines after the common lemma and both adapters; this
is an estimate, not a checked patch. First pilot the reveal action translation
alone. Do not assume guards invariant under arbitrary private-state changes.

## 2. One typed compiler metadata theorem can own two structural inductions

[Resolution fields](../../Vegas/Compile/EventGraphResolutionFields.lean), near
the resolution-name induction at line 119, and
[decoded revelations](../../Vegas/Game/DecodedRevelations.lean), near the typed
revealed-cell induction at line 69, recursively establish the same field-origin
correspondence. The latter retains both name and cell type; the former retains
only the name. The bodies share 28 exact eight-line windows.

Move the typed revealed-cell reader and its structural correspondence to a
source/compiler owner, then derive name-level facts by projection where the
field naming is compatible. The generic arbitrary field-label formulation may
still need a small general metadata lemma: do not silently replace its scope
by the default compiled graph. Compile must remain independent of Game.

Estimated net reduction: 20–50 lines after reader movement, general hypotheses
and both consumers. The engineering benefit is larger than the line saving:
the compiler would own the typed origin fact used by its game-level readers.

## 3. Share observation-codec traversal, retaining visibility and absence

[Observation decoding](../../Vegas/Compile/EventGraphObservation.lean) and
[observation encoding](../../Vegas/Compile/EventGraphObservationEncoding.lean)
repeat the public-data/publication and owner-visible commitment/private-input
cases. Encoding has 550 lexical body lines in an 840-line module; one decoder
inversion alone has 179 body lines. This is a substantial proof surface, but
many cases are semantically necessary.

The useful common unit is a typed visible-cell traversal with head-read,
tail-read and write/read lemmas. Instantiate it for both directions of the
partial codec. A successful decode and coverage of visible fields must remain
explicit; an unwritten or invisible field cannot be reconstructed from an
arbitrary default. Existing field getters, typed references and the encoder's
write/read lemmas already supply much of the operation-level API.

Estimated net reduction: 50–120 lines after all traversal adapters. This is
unproved and medium risk because dependent cell types and ownership equalities
are real obligations. Pilot a shared public-data/publication branch before
introducing a general environment framework.

## 4. Bundle the residual embedding already used by the compiler

[Policy suffix laws](../../Vegas/Compile/EventGraphPolicyLaw.lean) and
[graph suffix laws](../../Vegas/Compile/EventGraphSuffix.lean) repeatedly build
tail references, embeddings, strict-order evidence and rank equations. The
sample and commit cases in policy alignment each contain the same roughly
ten-line reference-order proof and repeated output-reference equality plumbing.

Give the existing residual embedding a small operation that returns its tail
references together with the derived ordering fact. Reuse the existing suffix
structures; do not introduce another compiler semantics or assume suffix
execution correspondence. Actor, action decoder and policy alignment remain
separate fields proved by the concrete lowering.

Expected saving is modest, perhaps 20–45 net lines across the initial consumers.
The main gain is that an elaboration repair to dependent embeddings has one
owner instead of being repeated in the 312-line execution-law and 273-line
backtranslation-alignment proof cones.

## 5. The private-parameter source-protocol payoff law is within immediate reach

[Source protocol Nash](../../Vegas/Game/SourceProtocolNash.lean) currently
specializes the exact typed terminal-readout law to utility of the public
outcome. [Initial-state preservation](../../Vegas/Source/InitialState.lean) and
the existing parameterized game form already provide the private-parameter
projection. Mapping the typed readout by that projection gives the entire
utility-vector law for utility of the correlated initial parameter and public
result, using the same policies and observations.

**Checked experiment:** this stronger payoff-vector law compiled under the
central Lean options. It needs no independent-input or finite-parameter
assumption. Reuse the same coordinate-update and expectation-existence transport
to obtain parameterized same-error Nash preservation/reflection. That Nash
extension itself was not proved in this review. The clean implementation should
generalize the observation reader once, then specialize public and parameter
views, rather than copy the full protocol-Nash module.

This is valuable new functionality and may grow the public API. It is not a
measured proof-compression result.

## 6. Purification needs finite explored action support, not finite payload types

[Purification](../../Vegas/Source/Purification.lean), especially the pure-mixture
construction starting at line 55, assumes finite binding types. Its induction
uses that premise to enumerate action support at the finitely many configurations
currently being explored. Chance tables and initial configuration lists are
already finite.

A useful stronger theorem would instead require finite support of the incumbent
and deviating action kernels at every explored binding view, with those premises
inherited by the syntactic suffix. The current theorem then follows because a
finite carrier makes every support finite. This would cover finite-support
strategies over integer payloads without changing source semantics.

This statement is **proposed, not checked**. The induction must prove its next
configuration frontier finite and maintain the support hypothesis there. It
does not remove the initial-support condition, reproduce arbitrary infinite
behavioral products by one discrete pure-policy PMF, or establish unrestricted
Nash compilation for infinite binding alphabets. Those are different claims.

## 7. Classify departure from the intended game before duplicating induction

[Intended play](../../Vegas/Source/IntendedPlay.lean), starting near line 740,
proves that a value-only unintended deviation creates indebtedness.
[Failed-binding deviations](../../Vegas/Source/FailedBindingDeviation.lean),
starting near line 37, repeats the source-constructor induction and permits
irrevocable failed bindings, producing the larger debt-or-failure conclusion.

The constructor-local classifier should distinguish withholding, a rejected
value and an admitted forfeiture, then supply the two existing global results.
The admission premise is essential: a failure admitted by the full interface is
not an ordinary successful value rejected by a guard. A helper merely assuming
the desired complete debt implication would not be an extraction.

Estimated net saving: 25–55 lines, with medium confidence. The import order
must be split below the two consumers to avoid making IntendedPlay depend on
its current downstream failed-binding module.

## 8. Erased-history continuation needs one step law and legality transport

[Erased continuation](../../Vegas/Source/CommitRecoveryErasedContinuation.lean)
and [support splicing](../../Vegas/Source/CommitRecoverySupportSplice.lean)
contain the same private mapped-step proof near lines 115 and 21 respectively.
The first six exact repeated eight-line windows corroborate this small duplicate.

Publish one owning erased-step law and reuse it for both continuation and
support extraction. Keep legality transport separate: equality of erased states
alone does not imply equality of menus; the current support-splice proof uses
erased **information histories** to establish menu agreement. Estimated net
saving is 10–25 lines. A general continuation law follows only after both the
step kernel and the legal observation-local choices commute.

## 9. Make the auction's executable transfers a separate concrete application

[The auction](../../Vegas/Examples/CommitRevealAuction.lean) proves conditional
withholding refutes dominant truthfulness for every real-valued forfeiture.
Its program returns an empty payment list; the economic payoff is supplied by
the analysis utility. This is an accurate existing counterexample, but it is
not yet an executable-payment auction application.

A nearby result is a bounded-bid auction whose return expressions compute its
ordinary transfers and whose valuation is separate. Preserve the current
withholding witness and prove the evaluated cash reader equals the economic
settlement. The finite bounded domain also meets the current ideal-graph Nash
theorem's commitment-alphabet premise.

Do not replace the existing universal real-forfeiture result by an integer-only
program theorem: executable payment expressions currently produce integers.
Keep the old theorem and add a concrete integer-transfer application with an
explicit adapter. This is feature growth, not proof shrinkage, and it does not
restore dominant truthfulness.

## 10. Reuse positive service fixtures without erasing adversarial timing

[The payment roster fixture](../../Vegas/Examples/ProgramPaymentsRuntimeService.lean)
shows that the existing roster-to-asynchronous constructor supplies all service
fields for a small concrete program. Future positive examples should reuse
that constructor and declared payoff bounds, rather than duplicate an ad hoc
clock/inclusion proof.

The [late-opening fixture](../../Vegas/Examples/LateOpeningRuntimeService.lean)
has a different purpose: it realizes a particular public lottery, leakage and
late-inclusion behavior. Replacing it by the roster would change the game and
lose its timing evidence. Its long proof is not removable merely because a
simpler scheduler can also satisfy an asynchronous contract.

## Engineering and validation findings

- Keep observational, transition and strategic correspondences separate. A
  terminal law does not supply off-path beliefs or continuation rationality.
- Prefer local lemmas for real dependent-carrier equalities over repeating
  unfolding lists in each caller. Do not change the central transparency option
  as part of a compression experiment.
- Module-level reachability is too coarse to establish declaration-level reuse.
  A module may be retained because one theorem is used while a nearby certificate
  has no constructor or downstream instance.
- Exact-window repetition is a review lead. Type signatures, type transports,
  semantic premises and new adapters must be included in any claimed net saving.
- The inventory tool has regression tests for blank lines, comments, term/tactic
  body separation, module naming and cross-file duplication. It is lexical,
  includes tactic-valued definitions, and is not a replacement for Lean's AST.

No new logical bug or weakening of a retained source/compiler theorem was found
in the inspected bodies. There is no claim that every source proof was read
line by line or that the proposed refactors have been integrated.
