# VegasCore proof and artifact guide

This artifact checks the active sequential-source, event-graph, and native
public-message results. It is not a verification of a Kotlin frontend,
blockchain ledger, deployed contract, or EVM.

## Reproduction

Use the pinned Lean toolchain and dependency revisions:

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

Do not run `lake update` when reproducing a pinned revision. The cache is only
a build optimization; the subsequent build checks the proof terms.

## Reading route

| Question | Main location |
| --- | --- |
| What is a checked source program? | `Vegas/Core/` |
| What is its written-order execution? | `Vegas/Core/SmallStep.lean`, `Vegas/Core/Strategy.lean` |
| How is the event graph built? | `Vegas/Compile/Compiler.lean`, `Vegas/EventGraph/` |
| How are source decisions and graph reads related? | `Vegas/Compile/Compiler.lean`, `SourceAdequacy.lean`, and the event-graph laws |
| What executes public messages? | `Interaction/`, `Vegas/Compile/SealedSource.lean` |
| Which active games use that runtime? | `Vegas/Game/SealedRounds.lean`, `SealedMessages.lean`, `SealedRelease.lean`, and `SealedTimeoutApplication.lean` |
| Where do source payout bounds imply native incentives? | `Vegas/Core/Settlement.lean`, `Vegas/Game/SourceCandidate.lean`, `Vegas/Game/SealedCandidate.lean`, and `VegasTests/SealedPayout.lean` |
| Which claims are paper-facing? | The single root audit, `Paper.lean` |

Read the owning theorem and definitions, not only its paper-facing restatement.
The audit pins theorem axioms; it does not prove that prose and formal
statements agree.

`paper-claims.json` records each manuscript claim either with active audit
theorems or an explicit explanation of what is unverified. These explanations
identify coverage gaps, not a list of theorem statements to implement.
`python scripts/check-paper-claims.py --allow-unverified` checks this inventory
against the direct Lean audit and the pinned manuscript snapshot. Strict mode
fails on any unverified claim or admitted audit declaration. Neither mode reads
reference code or derives obligations from it. `--allow-missing-paper` permits
a clone without the separate manuscript; prose coverage is then unchecked.
The concrete end-to-end target is specified in
[the active tower](docs/active-tower.md#end-to-end-candidate-theorem).

## Trust and scope

Proved audit entries use Lean's standard logical axioms reported by
`#print axioms`. The active `Paper.lean` file is intentionally a small
direct-delegation audit surface and currently contains no admissions. Open
strategic work is documented as an obligation in `docs/active-tower.md`; it is
not disguised as a proved paper theorem. Production libraries cannot import
the audit or contain admissions.

The repository does not treat generated code, test vectors, or an executable
compiler alone as a refinement proof.

Native support theorems say that supported sealed-message executions decode to
reachable graph prefixes, and terminal prefixes reconstruct written-order
source executions with matching payout evaluation. The same support guarantee
holds for arbitrary bounded policy executions, including pending messages,
recipient-local delivery, inclusion, replay, malformed traffic, and
withholding. The scheduler/environment sees the full pending pool; player
views currently expose only their own inbox, sent messages, and the public
ledger.
Ideal-service hiding is proved separately. These results are operational and
support-level; they do not identify an arbitrary runtime policy with a source
policy.

`Vegas.SealedCompilation.RoundModel.isεNash_iff_of_checkpointDominance` is a
concrete strategic edge to the actual pending-message round driver. It uses
timely service, normal source/native utility agreement, and conditional
comparisons at the player's actual timeout-checkpoint information. The legal
source completion retains that player's registered choices. The theorem covers
all unilateral native policies and derives its bound from the constructed
coupling. It preserves and reflects Nash and same-error epsilon-Nash at
compiled profiles; a positive margin charges the actual timeout probability.
`checkpointUtilitySimulation` packages profile-uniform comparisons for
composition. A uniform cap on own timeout utility below every source utility
supplies `utilitySimulation` as a sufficient case. These utility theorems do
not assert exact outcome-law simulation after selective withholding.

For the resolving sealed backend, `pending_honest_round_source_law` in
`Paper.lean` audits an exact coupling with the original written-source profile.
The native marginal is the actual early-stopping pending-message driver.
Roster coverage, periodic inclusion capacity, a sufficient relative timeout
window, and a whole-period termination budget imply normal completion and
exact decoding at every supported result. A multistage nullable-source test
instantiates the assumptions with delayed service and arbitrary unreserved
wire choices. `pending_round_approximate_nash_iff` and
`pending_round_deviation_margin` audit the uniform-cap strategic result.
The `pending_checkpoint_*` theorems audit the conditional result, actual local
information, and retained commitments. `pending_public_payout` verifies that
every supported completed native outcome has the public payout of a legal
source execution, including after defaults. `pending_timeout_source_choice`
additionally identifies the responsible player's designated source choice in
the same settlement witness. For utilities valuing the programmed payout,
`pending_source_payout_nash_iff` derives the incentive premise from
`VegasCore.QuitPayoutBound`: a lower bound on all legal source executions and
the same upper bound when the player quits. The separate conditional interface
allows finer comparisons; deriving commitment-dependent and conditional
continuation tests entirely from source semantics remains open.
The payout integration test pays `7` after a nonempty Boolean choice and `-3`
after `none`. It proves the quitting bound from legal source execution, proves
the always-`some true` source profile Nash, and derives Nash for its compiled
pending-message profile under arbitrary unreserved wire behavior. The native
utility evaluates the actual public payout; it is not an independent timeout
penalty supplied only to the test.

The candidate-service host admits competing and potentially unopenable
commitments. `pending_candidate_honest_payout_law` audits its original-source
payout law for generated profiles under the same deadline-service conditions,
with completion and no timeouts as conclusions. Both services instantiate the
shared `MessageApplication.RoundDriver`; the honest embedding retains histories,
receipts, and pending traffic. `VegasTests/SealedCandidates.lean` instantiates
this law for arbitrary source profiles and adaptive unreserved wire choices,
and separately tests selected and unopenable candidates.
`pending_candidate_timeout_owner` audits deadline protection under arbitrary
candidate-player deviations: roster coverage, periodic inclusion capacity, and
a sufficient window ensure that every timeout belongs to an unprotected player.
`VegasTests/SealedCandidateDeadline.lean` instantiates this result for a
two-player source with an arbitrary first-player policy and delayed service;
the second player meets both deadlines and completed supported runs exist.
`pending_candidate_source_payout_deviation_bound` and
`pending_candidate_source_payout_nash_iff` audit the candidate host's end-to-end
deviation bound and same-error equilibrium correspondence. Their source-only
condition compares legal quitting settlements with supported unilateral
continuations against fixed opponents, when the public source environments
strictly before the commitment agree. The graph/backend proof constructs this
pair relation; it is not supplied as a native incentive assumption. Equal global
quitting caps and fixed-opponent support floors imply the condition.
The uniform special case composes
`sourceGraphPayoutSimulation` with `CandidateRoundModel.utilitySimulation` through
`UtilitySimulation.trans`. The compiler derives graph information, disclosure,
and quitting certificates from the source; no native incentive inequality is a
premise. `VegasTests/SealedPayout.lean` also instantiates these candidate results
for the nonconstant payout above and arbitrary unreserved candidate wire policies.
`VegasTests/SealedProfilePayout.lean` separates the two incentive conditions with
a two-player source: it proves the fixed-opponent condition at a source Nash
profile, proves that no uniform source bound exists, and transports that profile
to the actual candidate game. Its native deviation bound covers an arbitrary
replacement policy and arbitrary unreserved wire behavior.
The same test also supplies a source Nash profile for which no equal cap/floor
certificate exists, and derives a candidate `1`-Nash guarantee from separate
source bounds. `pending_candidate_source_quit_gap` audits the sharper bound
weighted by the actual native timeout probability;
`pending_candidate_approximate_nash_with_gap` audits its unconditional error
corollary. `pending_candidate_approximate_nash_reflection` uses honest payout
agreement alone and does not assume any quitting incentive condition.

`VegasTests/SourceQuitPrefix.lean` proves the prefix condition strictly weaker
than equal global cap/floor bounds: an earlier public sample changes a baseline
payout. This is a source-only separation test, not a candidate-runtime instance;
sampling remains outside that backend fragment.
`VegasTests/SealedCandidatePrefix.lean` supplies an in-fragment integration test:
an earlier player's randomized commit/reveal sets the public baseline, the source
prefix condition is proved, and the native deviation bound is instantiated under
periodic service with arbitrary replacement policies and unreserved wire actions.

At the graph boundary, `Vegas.EventGraph.Strategic.deviation_law` proves the
sharper exact statement under declared-read locality and a single ready
commitment per player: every canonical unilateral replacement is one behavioral
graph deviation, and `isεNash_compileProfile_iff` follows for every observation
utility. `Paper.lean` delegates both graph claims directly. The theorem is not
yet a source-language or pending-message theorem; a graph with simultaneous
same-player commitments needs a correlated frontier strategy or an explicit
additional hypothesis.

The reusable mechanism-design step for a designated quit is proved in
`GameTheoryExtensions/Core/QuitTransfer.lean`. It transfers a strict source
improvement whenever the runtime supplies a support-level law identifying the
target quit with the source quit. This law is a field-level obligation of a
concrete runtime certificate, not an assumption hidden in the sealed compiler.
