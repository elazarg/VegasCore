# Preservation contracts and commitment failure

## Recommendation and status

Keep three things separate:

1. **The game:** program, legal actions, information, and public results.
2. **The translation:** a particular transformation and its playerwise strategy map.
3. **The requested claim:** what must be preserved, under which assumptions.

Use ordinary, named Lean propositions about a fixed translation as the proof
interface. Request selection belongs at the analysis/build boundary. A request
must not change source semantics. Keep the core's four instructions; introduce
neither an equilibrium-mode parameter on the AST nor a generic effect system.

Commitment forfeiture is a semantic choice. Represent its admission in a source
interface, with explicit site annotations when needed. Build the legal history
tree from that interface. The existing internal failure-aware core supplies the
full interface; its value-only abstraction needs a property-specific proof.

The source interface is implemented. Its canonical protocol restricts legal
histories, reuses source observations and execution, and has a playerwise
equivalence for admitted pure and behavioral policies. Private setup draws once before play;
the complete terminal-state law agrees with source execution at every prefix.
The pure and behavioral SPE characterizations and conditional preservation and
reflection theorems are checked. Native continuation correspondence and an
automatic checker remain open. The [SPE plan](subgame-preservation.md) states
those obligations separately from the source adapter.

## Requirements

### Semantic requirements

| Requirement | Consequence for the design |
| --- | --- |
| A program has stable semantics across requested guarantees | Asking for SPE cannot add legal actions, change observations, or select a different meaning of `commit` |
| Failure admission is part of the game | Restrict legal transitions and histories, not only prescribed strategies |
| Failure is irreversible at the corresponding phase | Later withholding cannot automatically substitute for early forfeiture in a continuation theorem |
| Private information stays private | An owner-known forfeiture does not create an immediate public abort signal |
| Binding is fixed at submission | Free private work cannot reinterpret transmitted candidates |
| Players retain in-flight reading and response opportunities | A new certificate must not hide packet observations or reset deadlines |
| One concrete translation serves all advertised claims | A Nash proof for one map and an SPE proof for another do not certify a combined artifact |
| Analysis scope is explicit | Utilities, joint type/public observation, service assumptions, profile restrictions, and error bounds cannot silently widen |
| SPE covers proper off-path subgames | On-path reachability and public checkpoint checks are insufficient |
| Preservation and reflection are distinct | Neither a name such as “SPE safe” nor an initial-law theorem establishes both directions |
| No utility oracle is implicit in compilation | A utility-specific completion is a separate scoped translation, not evidence for the uniform compiler |

Source utilities remain separate from core execution. A source return expression
is not an implicit license for the strategy compiler to inspect every analysis
utility. The uniform claim quantifies over utilities *after* fixing the map.

### Usability and engineering requirements

- Existing value-only programs keep their intended game when a request changes.
- A diagnostic names the site, missing continuation, and exact claim at issue.
- Failure to prove a sufficient condition is reported as unresolved, not as
  semantic impossibility. A failed candidate translation is not proof that all
  translations fail.
- Adding a property should add its definition, theorem adapter, and optional
  checker. It should not change source constructors or unrelated passes.
- Adding a transformation should identify its endpoints, maps, and relevant
  evidence. It should not require proving every property the system knows.
- Utility-specific and profile-specific evidence is useful, but visibly scoped.
- A finite checker may use enumeration; the core language does not acquire a
  finite-value restriction merely to make that checker complete.
- Evidence about one node or pass must compose without combining incompatible
  maps, observations, or assumptions.
- Retain the existing initial-play Nash/Bayesian theorem and its API until a
  concrete new adapter requires a coherent refactor. No duplicate compiler
  pipeline or compatibility layer is needed for this experiment.

## Candidate designs

| Design | Attractive feature | Failure mode or cost | Decision |
| --- | --- | --- | --- |
| Global mode such as `compile --equilibrium=spe` selects commitment semantics | Small apparent interface | Identical text denotes different games; a source equilibrium proof may refer to the other game | Reject semantic mode switching; a request flag may select obligations only |
| Hypothetical independent booleans such as “allow failure,” “preserve SPE,” and “check utilities” threaded through syntax and compiler | Direct local branching | Flags mix semantic choices, requested claims, and proof status; many combinations have unclear meaning | Reject |
| AST indexed by a generic effect/capability row | Rich static enforcement | Every interpreter and dependent continuation carries machinery unrelated to its execution; does not itself prove strategic preservation | Defer; one semantic distinction does not justify an effect system |
| Duplicate value-only and failure-aware ASTs or separate commit opcodes | Explicit syntax | Duplicates traversals, accounting, and compiler cases for a difference in legal actions | Reject for this distinction |
| Stable failure-aware core, explicit admission interface, and separate evidence for each transformation | Reuses the existing semantic split; supports independent properties | Requires honest source protocol adapters and concrete certificate scopes | Recommend |

The experiments test the semantic obligations of these choices; they do not
implement four competing production compilers. In particular, the AST-row and
duplicate-AST costs above are architectural assessments, not benchmark results.

### Where the semantic annotation belongs

The internal core already accepts value-or-failure commit actions:
[source syntax](../Vegas/Source/Basic.lean),
[value-binding abstraction](../Vegas/Source/ValueBinding.lean), and
[its strategic edge](../Vegas/Game/ValueBindingEdge.lean).
Adding an abstract forfeiture interpretation does not require exposing handles,
malformed bytes, preparation slots, or cryptographic witnesses in the language.

An elaborated source interface can assign each **actual commit site** one of two
admission policies: values only, or values plus forfeiture. Use structural site
identities from the program, not an unvalidated string-to-Boolean dictionary.
This admission map is semantic input to the protocol adapter, outside the core
AST. Site syntax can elaborate to it without adding an instruction. Keep the
map explicit in theorem endpoints; hiding it in typeclass search would make
the game hard to identify.

The value-only default is explicit in the source interface. A developer can
choose the full interface for a program, or mark a particular site as permitting
forfeiture. Do not introduce arbitrary action predicates, dynamic policies, or
generic effect rows until a real example needs them. Once there is a second
kind of semantic restriction, reassess this representation using that example.

The adapter must reject a forfeiture transition at a value-only site and hence
exclude every history extending it. A subtype of strategies does not accomplish
this: arbitrary prior actions still exist in the underlying history tree. This
is why the current value-binding strategic game alone is not the needed source
SPE presentation.

Forfeiture must have the same hidden/public timing as the accepted target
commitment. It does not automatically create a public event or activate a
public failure handler early. Publication failure remains observed at the
protocol's existing publication boundary.

## The proof interface

The smallest useful abstraction is ordinary predicate transport. For a fixed
map `C`, analysis context `k`, and admissible context family `K`, the shape is:

```text
PreservesOn C P Q K :=
  for every k in K and every source profile s,
    P(k, s) implies Q(k, C(s)).
```

This is a packaging experiment, not a replacement definition of Nash or SPE.
The claims instantiate the canonical game-theory predicates. A production
strategic map is obtained from per-player maps; a bare function on whole
profiles does not prove playerwise compilation or information locality.

The experiment proves the following without a property enumeration:

- Identity transports any claim.
- Composition transports a claim when the middle claim matches exactly; the
  resulting scope is the intersection of the two scopes.
- Two claims can be bundled when both refer to the same concrete map.
- Evidence for a broad scope can be restricted to a narrower scope.
- Evidence for one context cannot in general be widened to all contexts.
- Separate existential claims about different maps cannot be bundled.

Put outcome-law correspondence beside strategic evidence. Preservation of an
equilibrium predicate alone is too weak to mean compiler correctness: it can
be vacuous when the source has no equilibria or ignore the intended play. An
SPE request therefore includes both the established outcome contract and the
additional strategic contract. A behavioral continuation certificate remains
the intended sufficient condition, not an axiom inferred from a request name.

For the first implementation, use named theorem functions and explicit proof
arguments. The prototype's generic predicate need not become a production
framework. Existing mixture and utility simulation certificates remain useful
for their particular semantic obligations. Adapt them to a fixed map, rather
than pretending their proof strengths are interchangeable.

### Scope and error accounting

Make the following visible in theorem types and readable artifact summaries:

- Source and target program/interface and strategy translation.
- Observation/decode maps, including persistent private types when relevant.
- Utility family, or the exact utility when the claim is specialized.
- Whole-game versus particular-profile quantification.
- Pure or behavioral strategies, considered coalitions, and proper-root coverage.
- Runtime/service assumptions and any approximation bound.
- Preservation or reflection direction.

The prototype uses a common context type to expose intersection and prevent
widening. When observations or utility domains differ across passes, production
composition must supply the actual transport; it cannot equate context labels.
Approximation errors need a proved composition rule. Do not infer one by
intersecting a set of “capability” names.

Nash, SPE, dominant strategies, and coalition guarantees are not an integer
strength scale. In particular, the predicate implication SPE implies Nash does
not mean that an SPE-*preservation* theorem preserves every source Nash profile.
Requests may be bundled as convenient named presets, but each resulting claim
has its own evidence.

## Requests and diagnostics

Illustrative surface use (not implemented syntax):

```text
game: ordinary value-only commitment A
request: public outcomes + SPE preservation
```

The request elaborates to proof obligations about the unchanged game and chosen
translation. An automatic checker may return a certificate, a checked refutation
of the stated claim, or an unresolved obligation. The Lean prototype makes these
different constructors, and proves that its success branch supplies the claim.
Search heuristics may be untrusted; acceptance needs a kernel-checked proof or
an instance of a proved-sound validator. No unchecked `Bool` enables elision.

Example diagnostic:

```text
SPE preservation unresolved at commitment A.
The backend can make A unrevealable before decision B.
The value-only source has no corresponding continuation.
Needed: a continuation certificate for this translation and analysis scope.
```

An actual refutation should add the source profile, utility scope, target prefix,
and profitable continuation. A theorem excluding *all* utility-independent
translations should say so explicitly; failure of one proposed completion is a
weaker finding. Never print “unimplementable” from a failed sufficient check.

Available responses are explicit: provide a proof, select a backend whose
certified behavior meets the obligation, narrow the claim, or change the source
interface to admit forfeiture and re-establish its equilibrium. Adding a failure
handler is not itself a proof of optimal play after failure.

### Fallback has a semantic boundary

Failure elision is an abstraction of the *game*, not necessarily a code-size
optimization. A compiler cannot automatically “turn off elision” by adding
forfeiture to a value-only source and keep using the original equilibrium proof.

For an ordinary optional implementation optimization, falling back to a
certified identity pass may preserve the same source meaning and request. For
this source abstraction, the fallback is an unresolved obligation. Modeling
additional source choices requires an explicit semantic change. This distinction
belongs in diagnostics rather than another core-language flag.

## Experiment evidence

### E1: exhaustive failure-elision experiment

Run:

```text
python scripts/experiments/preservation_contracts.py
```

The model has one player, four atomic decisions, perfect own-action recall, no
chance, and integer utilities. Every history is a proper subgame root. The
script enumerates all pure strategies, computes all continuation optima, and
checks complete-continuation optimality. These restrictions are part of its
scope; it is not a finite test for multiplayer imperfect-information SPE.

| Measurement | Value-only source | Interface also admitting forfeiture at A |
| --- | ---: | ---: |
| Decision histories | 8 | 15 |
| Pure strategies | 128 | 32,768 |
| SPE for utility favoring false after failure | 2 | 8 |
| SPE for utility favoring true after failure | 2 | 8 |
| SPE shared by both utilities | 2 | 0 |

Both interfaces require a value at B's binding; withholding B later is allowed.
The same source profile can be optimal for both utilities while no expanded
profile is optimal for both. The canonical Lean proof in
[IrreversibleFailure.lean](../GameTheoryExtensionsTests/IrreversibleFailure.lean)
establishes the corresponding impossibility using the actual SPE definitions;
the script independently explores all finite pure policies.

| Candidate transformation / scope | Outcomes | Nash | SPE |
| --- | --- | --- | --- |
| Copy source behavior into the added failure histories; two utilities | Pass | Pass | Fail |
| Repair failure continuations using the selected utility; that utility only | Pass | Pass | Pass |
| Reuse the repair for the other utility | Pass | Pass | Fail |
| Copy completion; observe only whether A succeeds | Pass | Pass | Pass |
| Re-encode B by negating its stored bit and decoding it back; two utilities | Pass | Pass | Pass |
| Safe elision followed by B re-encoding; observe only A | Pass | Pass | Pass |

The first failing continuation is immediately after sealing an unopenable A:
the compiled continuation yields 1, while another continuation yields 2. This
history exists regardless of whether the compiled strategy reaches it.

For the A-only observation there are two terminal observations. The experiment
checks all three weak preference orders on them. Determinism makes this complete
for real-valued utilities of that observation in this finite pure game. It does
not establish an analogous behavioral, randomized, or Vegas theorem.
This restricts the analysis utility; it does not remove B from the players'
observations or claim preservation for utilities that depend on B.

B re-encoding is a second concrete transformation. It is intentionally simple:
it tests that the design accommodates another pass and outcome correspondence
without introducing another language mode or changing the property interface.
The script checks it on all 32,768 full-interface profiles, then checks composition
with the safe abstraction on all 128 source profiles.

### E2: Lean contract packaging

Run:

```text
lake build GameTheoryExtensionsTests.PreservationContracts
```

[PreservationContracts.lean](../GameTheoryExtensionsTests/PreservationContracts.lean)
checks identity, composition, conjunction, scope restriction, sound acceptance,
scope-widening failure, and incompatible-map bundling. Its SPE instance proves
that a uniform failure-elision certificate cannot exist for the checked pair of
protocols. Retaining the full interface has the identity certificate; this says
nothing by itself about the full-interface-to-runtime edge.

The experiment needs no AST change, core flag, property registry, or typeclass
hierarchy. Generic claim transport is a few elementary proofs. The difficult
work remains the concrete semantic certificate, as it should.

### E3: mixed site admission and visibility

The same Python experiment runs a small explicit admission record over the
program's two actual sites. All variants share the same four instruction stages.

| A admission | B admission | Decision histories |
| --- | --- | ---: |
| Values | Values | 8 |
| Values | Values or forfeiture | 11 |
| Values or forfeiture | Values | 15 |
| Values or forfeiture | Values or forfeiture | 21 |

For every legal history, the experiment checks that value-only sites exclude
forfeiture and all its extensions. Forfeiture at B makes its final publication
fail regardless of the later disclosure action. Before disclosure, the public
projection records only the two fixed commit events; it reveals neither the
values nor the forfeiture choices. Request selection is not an argument to the
arena or this projection.

These finite checks are complemented by the actual source adapter below.
The Python public projection alone does not establish multiplayer information
locality or proper-root closure.

### E4: actual source interface and private setup

**Question.** Can site admission restrict the legal history tree without a new
opcode, a utility argument, or additional player information?

**Implementation.** [CommitmentInterface.lean](../Vegas/Source/CommitmentInterface.lean)
uses structural sites of the given program. `CommitmentAdmission.values` admits
successful bindings; `CommitmentAdmission.forfeiture` also admits irreversible
forfeiture. Neither changes the timing of public observation. For the two-site
program in [SourceProtocol.lean](../VegasTests/SourceProtocol.lean), an interface is:

```lean
def interface (alice bob : CommitmentAdmission) : CommitmentInterface program
  | none => alice
  | some none => bob
  | some (some impossible) => nomatch impossible
```

The actual source adapter supports all four interfaces over the same program.
The mixed-site regression uses a Boolean payload at Alice's site and an integer
at Bob's; admission is independent of payload type. A forfeiture action is
illegal at a value-only site. Alice's choice leaves Bob's view and menu
unchanged. The prefix after Alice's hidden forfeiture is proved **not** to be a
proper subgame root, because Bob's decision information set crosses it.

[ProtocolPolicy.lean](../Vegas/Source/ProtocolPolicy.lean) proves a bijection
between admitted source pure policies and all canonical information-local
policies. [ProtocolEvaluation.lean](../Vegas/Source/ProtocolEvaluation.lean)
proves exact residual laws at arbitrary legal prefixes, including off-path
prefixes. Termination is checked from the number of remaining instructions.
No finite player universe or finite payload assumption is needed.

[SetupProtocolEvaluation.lean](../Vegas/Source/SetupProtocolEvaluation.lean)
adds the existing initial law as a chance step. One policy is used across all
draws. Continuation retains the draw; it never samples private types again.
[SetupProtocol.lean](../VegasTests/SetupProtocol.lean) checks that a hidden
private-input draw is not a proper root when the next player cannot distinguish
the two draws. The owner observes the input normally.

[SourceSubgame.lean](../Vegas/Game/SourceSubgame.lean) and
[SetupSubgame.lean](../Vegas/Game/SetupSubgame.lean) characterize canonical pure
SPE using source continuation expectations and admitted source replacements.
Utilities can read the complete terminal store, including persistent types;
restrictions to public results belong in the selected utility. These are
source semantic bridges, not native preservation theorems.

**Validation.** `lake build VegasTests.SourceProtocol VegasTests.SetupProtocol
Vegas.Game.SetupSubgame` passes. The bridges concern pure policies with
stochastic source chance. Behavioral policies are covered by E6 below.

### E5: proper-root continuation transfer

**Question.** Can named continuation-law hypotheses yield the existing SPE
predicate without an adequacy hierarchy or a second evaluator?

[Continuation.lean](../GameTheoryExtensions/Protocol/Continuation.lean)
constructs ordinary continuation game forms from the existing history runner.
With a certified horizon, canonical pure SPE is exactly Nash in every proper
continuation game. Preservation fixes one playerwise map, matches each proper
target root to a proper source root **before selecting a deviation**, and
requires the prescribed law and finite-mixture deviation laws at that root.
Reflection has its own source-root coverage and compiled-policy law premises.
These are direct theorem arguments; no property registry is introduced.

The checked boundary test in
[ContinuationTransfer.lean](../GameTheoryExtensionsTests/ContinuationTransfer.lean)
accepts identity and refutes uniform public continuation laws for **any**
playerwise map of the atomic irreversible-failure example. The refutation holds
already at the common source SPE for its two utilities. Thus the theorem cannot
turn the initial-law failure-elision argument into an SPE certificate.

**Validation.** `lake build GameTheoryExtensionsTests.ContinuationTransfer`
passes. The runtime-specific laws remain obligations. All implementation and
experiment code lives in VegasCore; the GameTheory submodule is unchanged.

### E6: behavioral deviations without finite player or payload domains

**Question.** Can the source interface cover arbitrary randomized deviations
without changing observations, weakening legality, or adding another runner?

[ProtocolBehavioralPolicy.lean](../Vegas/Source/ProtocolBehavioralPolicy.lean)
requires admission of every supported local binding choice. Its translation
preserves probabilities exactly; its inverse covers every canonical behavioral
policy. The same equivalence holds across private setup draws.
[SingleMover.lean](../GameTheoryExtensions/Protocol/SingleMover.lean) samples only
the active player's finite-support law. It gives each player's exact marginal
and agrees with the existing finite-player behavioral product where applicable.

[ProtocolBehavioralEvaluation.lean](../Vegas/Source/ProtocolBehavioralEvaluation.lean)
and [SetupProtocolBehavioral.lean](../Vegas/Source/SetupProtocolBehavioral.lean)
prove the full terminal-store law at every legal prefix. These laws use the
same source continuation evaluator as pure play and the existing randomized
protocol runner. A retained prefix never resamples its hidden bindings or types.

[BehavioralSubgame.lean](../Vegas/Game/BehavioralSubgame.lean) characterizes
behavioral SPE by source continuation inequalities. The generic preservation
and reflection theorems in
[BehavioralContinuation.lean](../GameTheoryExtensions/Protocol/BehavioralContinuation.lean)
use the existing proper-root predicate. Root matching precedes the deviation,
and the compiler is fixed. The proved horizon-independence theorem prevents
semantic dependence on evaluation fuel. Behavioral SPE of a point-mass profile
implies pure SPE; the converse still needs a separate deviation argument.

**Validation.** [BehavioralProtocol.lean](../VegasTests/BehavioralProtocol.lean)
uses natural numbers as players and a fair lottery over success and forfeiture.
It checks exact encoding, rejection of the whole lottery by value-only
admission, and retention of a binding under arbitrary randomized continuations.
[SetupProtocol.lean](../VegasTests/SetupProtocol.lean) also checks that randomized
policies cannot distinguish hidden setup draws and that continuations retain
the actual private type. These are source results and conditional transfer
results; native continuation coverage remains a proof obligation.

## Implementation order and stop conditions

1. Pure and behavioral source adapters, mixed-site admission, private setup,
   residual laws, and SPE characterizations are checked, without finite payload
   domains. Do not infer pure-to-behavioral SPE equivalence from value agreement.
2. Establish the full-interface continuation bridge to the actual runtime,
   including hostile prefixes, atomic responses, and all proper native roots.
   A generic contract wrapper is not evidence for this bridge.
3. Instantiate the SPE transfer theorem and use the canonical failure example
   as a negative case. Add a positive source elision theorem with an explicit
   structural premise, rather than promoting the finite Python result.
4. Attach these named certificates to the actual fixed strategy maps. Expose a
   small request/report interface only when it has real evidence to select.
5. Automate a useful sufficient condition. Preserve unresolved obligations as
   proof goals. Add a bounded exhaustive checker only for an explicitly finite
   fragment with a correctness bridge to the canonical semantics.

The mixed-site adapter validates the admission map without leaking private
failure information. Do not promote a generic certificate registry until a
second real property/pass needs shared orchestration.
Do not infer unimplementability from validator failure or advertise native SPE
before the full continuation bridge exists.

## Relation to standard compiler techniques

The separation of transformation from evidence follows
[translation validation](https://cs.nyu.edu/home/people/in_memoriam/pnueli/transval-icalp98.html):
correctness can be checked for a particular translation. A proved validator can
justify an unverified transformation, as demonstrated for
[Lazy Code Motion](https://xavierleroy.org/bibrefs/Tristan-Leroy-LCM.html).
Here the additional burden is strategic continuation correspondence, not only
ordinary execution behavior.

[Robust property preservation](https://arxiv.org/abs/1807.04603) distinguishes
different classes of properties and their associated compiler criteria. It
supports asking exactly which claim a translation preserves. It does not
establish our SPE criterion or license converting a property name into a proof.
These are methodological precedents; the protocol and equilibrium obligations
remain specific to Vegas.
