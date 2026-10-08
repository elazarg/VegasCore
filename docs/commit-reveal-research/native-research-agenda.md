# Mathematical work on the actual asynchronous runtime

Analysis by Codex. This agenda directs mathematical research at the implemented
runtime. It does not adopt a new interface, change the source language or close
an owner-controlled proof box. Paper proofs and machine-checked declarations
remain separate evidence categories.

## Primary question and model reminder

The primary source is a finite intended commit-reveal game. Players choose
values their commitment guards accept, and its required openings publish those
immutable values. Initial secrets may be correlated and remain hidden across
several stages. The compiler adds declared forfeits for omitted required
actions; these target deviations are not silently made lawful source choices.
A source that permits withholding with its own continuation payoffs is a
different preservation question and must be identified separately.

The target uses the actual signed-packet runtime. A player can fix a private
candidate atomically while submitting its handle, respond when activated,
submit packets or remain silent, and retain its complete private observations
and action history. There is no separate private staging action. The builder
reads its public environment history, chooses activations, inclusion, clock advances and
completion operations. The asynchronous contract gives owner opportunities,
protects a sole owner-authored packet identifier within its inclusion window,
and requires all events to finish within the configured execution. It does not
make pending packets invisible or supply a generic lower probability of late
failure. Correct accepted late packets can be uncharged. Unaccepted packets,
including additional identifiers for an already settled event, can be charged
by the actual sampled audit.

Fix the program, utility bounds, forfeit, deposit and public service properties
before selecting the builder and the source equilibrium. Ask whether every
selected source SE has a target SE with the same joint law of initialized
parameters, public results and realized net payoffs, and no deductions on its
initialized paths. The target policy may depend on the service in a pointwise
existence theorem. A common policy using only public properties, and a Bayesian
model with a stated service prior, are separate stronger or different claims.

The eventual scope includes the compiler's permitted concurrency. Serial
execution is an intermediate case that isolates information and timing issues;
it cannot establish the concurrent claim without an additional argument.

## Allocation and reasons

Allocate **100% of the remaining mathematical attention to concrete runtime
questions and their independent review, with no standalone foundational
invention**. This is an estimate of useful effort, not a promised elapsed-time
budget. The protected restriction has a reviewed paper proof in
[native protected execution](native-protected-execution.md). The
[foundation map](native-foundation-obligations.md) identifies existing APIs for
its adaptive stopped-prefix construction. Prioritize full-menu late-action
accounting and the concrete properties a broader positive would need. The
[native two-late counterexample](native-late-action-analysis.md) has a reviewed
full-menu paper proof; the declared contract alone cannot supply that positive.

| Work | Share | Useful deliverable |
| --- | --- | --- |
| Actual late actions and settlement boundary | 60% | Test the reviewed weak-PBE and deposit arguments on guarded multi-phase programs, and concrete public service properties that could exclude the native SE counterexample. |
| Independent concrete review | 30% | Check the entire native action space, admissible builder on every legal history, actual observations and global belief consistency. |
| Protected proof integration and concrete cross-checks | 10% | Maintain the reviewed first-ready result and compare every claimed native premise with its declaration. |

The [same-fixture weak PBE](native-weak-pbe.md) has a reviewed full-menu paper
construction for every late inclusion probability in (0,1). The native
SE-negative [smaller-deposit corollary](native-late-action-analysis.md#smaller-sender-deposit)
requires only a sender charge above half its reward range. Concrete follow-up
should test these exact arguments on guarded multi-phase programs and test
public service properties against the two-late mechanism. These results do
not create a general PBE theorem or alter the SE target.

The general observation-transfer, consistent-completion and terminal-audit
machinery already supplies substantial foundations. The reviewed full-menu
negative shows that the contract and its accepted late actions do not suffice
for a general SE extension. The largest uncertainty is which concrete public
service or settlement property supports a useful positive without excluding
physically possible communication. Another family of alternative interfaces
would help only if its native relationship is proved.

## Protected execution handoff

Specify an actual native restriction: canonical commitment/opening at the first
ready owner response, one identifier per event, and forced silence elsewhere.
Prove that every legal source value can be realized within the existing finite
candidate and response bounds. Keep actual activation/response pairs, variable
waiting lengths, private packet samples, observed builder commands and own
recall in the history comparison.

Derive the remembered observation channel from primitive transition kernels.
At corresponding source decisions, compatible hidden source histories must
have equal likelihood for the whole additional runtime view. Recovering source
information from runtime information proves only one direction. Show that the
conditional logical transition and utility are also the original ones at every
legal restricted history, not only initialized equilibrium play.

Use a single fully mixed source sequence and actual runtime Bayesian beliefs.
Take limits at waiting and decision sites together. The output must distinguish
a complete native paper constructor, existing checked ingredients, and missing
formal or mathematical adapters. Guard-rejected intentions and private
preparation memory must not disappear in a state-only projection.

## Late-action handoff

Use the actual packet identifier, evidence, readiness, binding allocation,
deadline and final-verdict definitions. Analyze at least two late choices or a
fresh late binding where they are available; a one-callback abstraction can
miss private-type sorting and changes to later proof capabilities.

Accepted late packets cannot be placed among automatically penalized actions.
For each proposed retained action, establish either a source-equivalent
continuation or a direct rationality argument under real settlement. For each
excluded action, prove the needed additional collection bound under arbitrary
later raw policies. A terminal audit that is already charged is not fresh
deterrence for every later transmission.

A negative must fix a valid source assessment and an admissible native
configuration, then rule out every preserving target SE under its full menus.
Extra encodings, early submissions, withholding and later continuations might
rescue implementation. A bad subgame or one profitable comparator does not
settle the existential question. Source-secret-dependent failure rewards and
hidden service/source correlations may not be imported from alternative-model
counterexamples without a native realization.

## Foundation and review handoff

Start from the owning declaration surfaces and the
[module architecture](../module-architecture.md). Reuse the existing
[compositional criterion](universal-preservation-criterion.md),
[protected information argument](native-observation-criterion.md),
[public scheduling proof](../public-scheduling-se-preservation.md) and
checked terminal-audit completion before proposing new machinery.

For every gap, record which primitive runtime fact would discharge it and
whether that fact is true, false, or unestablished. Distinguish routine
representation work from a missing equilibrium argument. In particular,
collection bounds, audit soundness on every retained history, and a coherent
restriction of all raw menus are separate obligations.

Independent review checks the quantifier order, complete deviation menus,
conditioning at rare decisions, joint remembered observations, and one global
consistency sequence. It also checks whether every claimed native premise
really follows from a declaration rather than from informal blockchain
intuition.

## Reallocation rules

- If the concrete coupling needs only assembly of existing facts, devote the
  available effort to that assembly and late-action analysis; foundational
  invention can drop to zero.
- If both native arguments fail at the same precise mathematical bridge,
  concentrate effort on that bridge, with a smallest actual-runtime instance
  testing it. A temporary 100% foundation allocation is appropriate then.
- If a credible native negative emerges, prioritize its full-menu and service
  verification. A temporary 100% concrete allocation is appropriate until its
  quantifiers and every possible preserving equilibrium are settled.
- If a native premise is false, exhibit the violating execution or game.
  Describe any repaired runtime as a separate proposal; do not alter the
  theorem target or current implementation to fit the proof.

These rules govern research effort, not approval to change semantics.

## Scope and reporting

Ideal cryptography, bounded finite play and already funded participants are
the declared mathematical setting. Fees, capital timing, participation,
strategic producers, coalitions, outside communication or financial positions,
computation and chain resource/finality guarantees must be identified beside
each result as modeled, derived, bounded, or excluded. A proof for the symbolic
runtime does not by itself certify a deployed blockchain implementation.

Maintain mathematical status in the research notes. Only checked theorems with
the required statements can close the owner's preservation checklist. Compare
the actual target with alternatives explicitly: delivery-conditioned outcome
law, approximate rationality, uniform absorbing settlement and restricted
delivery menus are useful other claims, not substitutes for this question.
