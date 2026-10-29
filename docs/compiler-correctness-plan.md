# Compiler correctness: completion plan

The source compiler already constructs a dependency graph, instantiates its
ledger application in Interaction, and translates source policies into actual
bounded-runtime clients. Exact source-to-ledger outcome preservation is checked.
The target here is to expose the ordinary correctness guarantees of that
existing tower as explicit capstones and align their presentation in the paper.
This does not require a new compiler for arbitrary independently authored graph
policies. Only paper-stated capstones receive pins in Paper.lean.

## The implemented tower and its checked guarantees

| Boundary | Construction and existing checked result |
| --- | --- |
| Intended game to source game | The intended game restricts the source action menus. Under the forfeit hypotheses, its assessments extend to source assessments; this is an equilibrium-extension result, not another AST lowering. See [intended preservation](../Vegas/Game/IntendedPreservation.lean). |
| Source to dependency graph | [Graph assembly](../Vegas/Compile/EventGraphAssembly.lean) lowers the program. [Policy translation](../Vegas/Compile/EventGraphPolicy.lean) supplies graph strategies, and [scheduled terminal-state preservation](../Vegas/Compile/EventGraphScheduling.lean) proves the exact source law. |
| Dependency graph to ledger model | [The runtime](../Vegas/Pending/EventApplication.lean) is parameterized by a graph. [Its reactive application](../Vegas/Pending/ReactiveRuntime.lean) instantiates Interaction's message operations. [Canonical clients](../Vegas/Game/SourceServiceCanonicalPolicy.lean) use the compiled graph policy to produce actual runtime responses. |
| Source to bounded ledger execution | [The exact client settlement law](../Vegas/Game/AsyncServiceRawNash.lean) quantifies over every admitted source profile without an equilibrium premise. [The monetary specialization](../Vegas/Game/ProgramPaymentAsyncNash.lean) preserves typed outcomes and executable transfers and already has a guarded pin in Paper.lean. |

The proofs of the last boundary use source syntax and source-compiled policies.
That is sufficient to establish correctness of the source compiler. A more
general intermediate-language API is a possible strengthening, not evidence
that this compilation or its end-to-end correctness is missing.

## Semantic contract

* The verified entry point is the typed source AST. The endpoint is the actual
  plain reactive application and its bounded raw response menu. Parsing,
  executable extraction, cryptographic refinement and machine execution are
  separate tasks.
* Ordinary preservation concerns the complete typed terminal store, including
  initial fields, and the program's executable payout readout. It covers every
  source profile, including failed bindings and withholding, without an
  equilibrium assumption. Traffic, clock values and chronological network
  traces are not identified with source outcomes.
* Runtime safety covers every legal raw history and arbitrary player responses.
  Outcome preservation concerns the prescribed clients of a supplied policy
  profile, under the existing all-history opportunity, protected-inclusion,
  completion and strict deadline-margin conditions. Finite execution fuel
  alone must not be presented as successful application completion.
* The second-pass outcome statement covers graphs and policy translations
  produced by the source compiler, in sequential and public-barrier modes.
  Source parameters or compiler-image hypotheses are legitimate in that
  statement. Do not require arbitrary graph policies to establish correctness
  of the supported compilation pipeline.
* Compare the actual ledger clients with the compiled graph's canonical law,
  and use the existing first-pass scheduler theorem where applicable. Do not
  assert scheduler independence for arbitrary graph policies that inspect
  chronological completion order.
* Retain arbitrary pending observation and correlated initial laws. Ordinary
  correctness must not acquire private-input independence, utility bounds,
  deposits or evidence-coverage assumptions from the SE proof chain.
* Permanent exclusion changes the controller and settlement semantics. Its
  graph-step safety can be a corollary, but ordinary outcome correctness for
  the plain application must not claim equivalence of recovery's off-path
  outcomes with the original source failure semantics.

Use finite players, finite graph action alphabets and finite initial support
where required by the actual policy realization and bounded-menu construction.
State the wire-value coverage and candidate-capacity premises explicitly.
Record which proof uses each premise before trying to weaken it.

## Existing proof material and missing adapters

| Obligation | Reuse | Work still required |
| --- | --- | --- |
| Source-to-graph outcome law | [Canonical laws](../Vegas/Compile/EventGraphCanonical.lean), [public scheduling law](../Vegas/Compile/EventGraphScheduling.lean), [typed readout](../Vegas/Compile/EventGraphReadout.lean) | Preserve the existing theorem's scope and use it as the first-pass capstone. |
| Interaction operations respect graph execution | [Native step relation](../Vegas/Pending/ExclusionNativeFailure.lean), [initialized invariant](../Vegas/Pending/ReactiveStateInvariant.lean), [completion origins](../Vegas/Pending/ReactiveCompletion.lean) | Expose initialized trace projection, stuttering, store agreement and conditional terminal completeness as one graph-level capstone. |
| Stable graph decision observations | [Barrier information](../Vegas/EventGraph/BarrierInformation.lean), [normalized policies](../Vegas/EventGraph/NormalizedPolicy.lean), [scheduler erasure](../Vegas/EventGraph/SchedulerErasure.lean) | Reuse the current compiler-policy observation arguments when exposing the second-pass capstone. |
| Ineffective disclosure and original own recall | [Source behavioral realization](../Vegas/Source/DisclosureBehavioral.lean), [observed-choice kernels](../GameTheoryExtensions/Math/Probability/ObservedChoice.lean) | Retain the existing checked normalization inside the actual client compiler. General graph-policy normalization is optional. |
| Packet realization and first opportunities | [Canonical decisions](../Vegas/Pending/ReactiveCanonicalDecision.lean), [opening provenance](../Vegas/Pending/ReactiveDisclosure.lean), [first-opportunity bound](../Vegas/Pending/ReactiveFirstOpportunity.lean), [service contract](../Vegas/Pending/ReactiveAsyncContract.lean) | Expose their established role in the bounded client construction and retain the existing service hypotheses. |
| Whole-run exact runtime law | [Source client law](../Vegas/Game/ServiceHonestLaw.lean), [bounded raw client settlement law](../Vegas/Game/AsyncServiceRawNash.lean) | Package the existing exact law as the end-to-end capstone; compare it with the first-pass graph law to expose the second-pass compiler-image result. |

Search the owning layers with rg and inspect declaration surfaces with
lean-defs.py before implementing an adapter. Extend the existing probability,
recall and execution APIs where possible. Do not introduce another runtime,
application transition system or commitment model.

Generic operational refinement belongs in Vegas.Pending. Source instantiation,
the supported second-pass law and composition belong in Vegas.Compile or
Vegas.Game according to their dependencies. Keep the underlying graph/runtime
operations shared. Factor a proof only where the exposed interface needs it;
a source-indexed correctness proof is not itself an architectural defect.

## Proof sequence and acceptance gates

### Fix the second-pass interface

- [ ] Display the actual composition of graph assembly, graph policy
  translation, runtime application, canonical decisions and bounded clients.
  Identify each existing definition rather than introducing a new interpreter.
- [ ] Specify the second-pass capstone on the compiler's supported graph/policy
  image, using the existing canonical graph semantics and actual source/ledger
  terminal decoders. No decoder may introduce a default payload.
- [ ] Reuse the checked public-barrier and information-discipline certificates
  for first-pass outputs and their sequential mode.
- [ ] Classify each desired capstone as an existing theorem, a direct
  consequence, or a genuine additional proof obligation. Do not list an
  established source-client law as an absent compiler edge.

Gate: every arrow of the paper's tower names an actual construction and the
correct kind of preservation result. The statements cover the supported
compiler image without importing a broader arbitrary-graph target.

### Complete operational refinement

- [ ] Construct an order-preserving projection of every initialized raw trace
  to a legal graph execution, erasing activation, submission, rejection,
  waiting, clock and bookkeeping steps that leave the graph unchanged.
- [ ] Reuse the native completion-step relation for accepted calls, chance
  commands and expiry. Retain original dependent actions and the actual
  initial draw, not merely an unrelated reachable-state witness.
- [ ] Relate every projected prefix to its actual typed graph store. Include
  authentication and expiry attribution where asserted by the capstone.
- [ ] Derive terminal graph completeness and successful decoding under the
  existing service completion premise. Keep safety independent of timeliness.
- [ ] If recovery safety is exposed, allow one runtime operation to project to
  several graph steps through the existing automatic drain trace.

Gate: arbitrary raw responses, malformed or competing packets, failed
openings and expiry remain in scope. No claim about probabilities follows
from this support-level refinement alone.

### Expose the supported second-pass outcome law

- [ ] Compare the existing exact ledger law and the existing canonical graph
  law through their common full typed source readout. This yields a
  graph-to-ledger equality for the compiled graph and the actual compiled
  clients without a new arbitrary-graph policy algorithm.
- [ ] Preserve the full terminal source store, including initial cells, and
  executable payouts. If the paper additionally states equality of complete
  graph stores, derive the graph-field reconstruction adapter explicitly.
- [ ] Expose the existing disclosure normalization in the compiler composition.
  Retain its checked treatment of remembered original actions and later
  decisions. Do not replace it with a simple true-to-false action rewrite.
- [ ] Retain bounded raw-menu coverage, candidate capacity, correlated initial
  laws, arbitrary pending observation, configured relative deadlines and the
  existing all-history service premises. The result is probability equality,
  not only graph reachability or equal expected utility.
- [ ] Check both sequential and public-barrier compiler outputs. Reuse the
  current service instances and exact client law rather than restricting the
  theorem to the fixed rank calendar or zero inclusion latency.

Gate: the paper can state the exact second-pass guarantee for its supported
compilation pipeline and point to a checked capstone. Source-indexed parameters
are permitted and stated honestly.

### Compose both passes and consolidate consumers

- [ ] Expose the existing source-to-Interaction exact law as the end-to-end
  capstone, showing its agreement with the two displayed pass laws through
  the actual terminal decoder. Preserve the joint initial data, complete
  typed source state, public result and executable payouts.
- [ ] Keep its quantification over every admitted source profile, including
  failed commitments, failed guards and withholding, in both compiled modes.
- [ ] Consolidate duplicated theorem presentations only where needed. Update
  callers and docs without compatibility aliases; do not replace established
  client algorithms to satisfy an unnecessary stronger interface.
- [ ] Any client refactor must establish the policy/response agreement needed
  by existing strategic consumers, including their off-path sites. Equal
  terminal laws alone do not justify replacing clients inside an SE proof.
- [ ] Retain the exact hypotheses and conclusions of the checked Nash,
  recovery SE and monetary capstones. A generic backtranslation of arbitrary
  Interaction deviations and concurrent raw-runtime SE are separate targets.

Gate: the two pass statements and end-to-end capstone describe the same actual
clients, and existing strategic and monetary consumers retain their scope.
Do not infer source-to-ledger SE preservation from a source-to-ledger Nash
theorem: the checked recovery SE result has its own controller and hypotheses.

## Capstones and manuscript changes

The ordinary-correctness presentation has four capstones. These are roles;
choose domain names for new Lean declarations after fixing their signatures.
Checklist labels and step numbers must not enter declaration names or docstrings.

| Capstone | Statement and paper placement |
| --- | --- |
| Source-to-graph semantics | Retain the existing scheduled terminal-state law, with its full source-profile and public graph-scheduler quantification. State it in the graph section. |
| Interaction-to-graph operational refinement | Every initialized raw trace projects to graph execution with typed-store agreement; service-complete terminal traces decode successfully. State it in the runtime section. |
| Graph-to-Interaction semantics | Exact terminal-outcome law for the graph and policies produced by the source compiler and the actual bounded clients, under explicit service and representation premises. Derive it from the checked graph and runtime laws and state it in the runtime section. |
| Composed compiler semantics | Expose the checked exact joint initialized source-state/result/payout law for the actual two-pass clients, without an equilibrium premise. State it beside the compiler tower and distinguish it from strategic preservation. |

- [ ] Add or retain only these ordinary-correctness capstones in Paper.lean.
  Each new paper-facing theorem must have its exact standard-axiom guard
  immediately after its statement. Existing paper-stated strategic, monetary,
  example and source-safety results retain their own justified pins.
- [ ] Keep normalization, observation, packet, freshness, local-kernel,
  commutation and induction helpers in their owning modules without new pins.
- [ ] Review existing compiler-specific direct pins. Remove a redundant helper
  pin only after rewriting every associated manuscript claim to the capstone.
  Do not remove a pin while its independent result remains stated in prose.
- [ ] State the four capstones in the maintained manuscript with exact
  hypotheses, outcome projections and `% Lean:` annotations. Proof sketches
  explain the construction without asserting additional unpinned invariants.
- [ ] Update the appendix's definitions and theorem-hypothesis mapping, the
  Overleaf theorem-correspondence table, module ownership and compilation
  documentation. Keep claims within the existing manuscript page limits.
- [ ] Add no theorem stub, admission or future-result pin. Update the
  manuscript's artifact revision only after the proof checkpoint is verified.

## Validation and checkpoints

Use checked Lean consumers that exercise the actual compiler boundaries:
remembered ineffective disclosure, withholding and expiry, both hidden-binding
completion orders, correlated initial inputs, partial pending observation and
positive inclusion latency with non-rank deadlines. Include empty and
chance-only programs where they expose boundary cases. Extend existing
examples when they already exercise a case. Runtime sampling experiments are
not a substitute for exact-law proofs.

Check the owning modules after each proof checkpoint. At consolidation, run
the ordinary full `lake build`, including Paper and all retained examples;
the module-boundary, Lean-option/source-policy and documentation checks; and
the repository checker unit tests. Check manuscript annotations against actual
capstone signatures and guards. Build the maintained paper, check references,
page limits and overflow, and render/inspect the changed pages.

Commit and push each stable, verified checkpoint: capstone interface and
operational refinement; supported second-pass and end-to-end statements;
consumer consolidation if needed; and final Paper/manuscript synchronization.
Keep the root artifact and separately managed manuscript revisions explicit.
Completion requires every gate above, checked capstones with only standard
axioms, matching paper statements and no pending proof obligations hidden by
an adapter assumption.

## Optional intermediate-language generalization

A source-independent policy compiler for all canonical policies on arbitrary
public-barrier graphs would be a stronger library API. Its proof would need
graph-level disclosure normalization preserving original private recall, exact
client realization and a generic bounded-menu outcome law. That work may
reuse the existing source normalization and service arguments, but it is not
required to establish the implemented source compiler's correctness or the
paper's tower. A graph constructed independently of source syntax is a useful
consumer for that extension, not an acceptance gate for this completion plan.
