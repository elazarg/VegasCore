# Compiler correctness: completion plan

The target is ordinary correctness of the two compiler passes, from the typed
source language through event graphs to the bounded Interaction message model.
Completion requires independently usable results for both passes and their
composition. The new results below are proof obligations, not checked claims.
Only their capstones will be added to Paper.lean and stated in the manuscript.

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
* The second-pass outcome theorem must not require a source program. Its graph
  domain includes sequential graphs and the public-barrier graphs emitted by
  the first pass, with concurrent bindings of different owners. General DAGs
  and concurrent public revelations are outside this completion target.
* The reference for a general graph policy is its canonical graph execution.
  Runtime clients normalize scheduling metadata. Equality with execution under
  other graph public schedulers needs the existing normalization and scheduling
  laws and their policy hypotheses; it is not asserted for arbitrary policies
  that inspect chronological completion order.
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
| Stable graph decision observations | [Barrier information](../Vegas/EventGraph/BarrierInformation.lean), [normalized policies](../Vegas/EventGraph/NormalizedPolicy.lean), [scheduler erasure](../Vegas/EventGraph/SchedulerErasure.lean) | Relate the observation at activation to the observation at eventual completion, without reading runtime-only information. |
| Ineffective disclosure and original own recall | [Source behavioral realization](../Vegas/Source/DisclosureBehavioral.lean), [observed-choice kernels](../GameTheoryExtensions/Math/Probability/ObservedChoice.lean) | Supply the graph-policy adapter: rank-indexed decisions and graph completion recall replace syntax-indexed source continuations. |
| Packet realization and first opportunities | [Canonical decisions](../Vegas/Pending/ReactiveCanonicalDecision.lean), [opening provenance](../Vegas/Pending/ReactiveDisclosure.lean), [first-opportunity bound](../Vegas/Pending/ReactiveFirstOpportunity.lean), [service contract](../Vegas/Pending/ReactiveAsyncContract.lean) | Lift local decisions to complete source-independent clients and prove exact conditional decision laws through inclusion or expiry. |
| Whole-run exact runtime law | [Source client law](../Vegas/Game/ServiceHonestLaw.lean), [bounded raw client settlement law](../Vegas/Game/AsyncServiceRawNash.lean) | Factor the graph-level execution argument, then recover the source results by instantiation and composition. |

Search the owning layers with rg and inspect declaration surfaces with
lean-defs.py before implementing an adapter. Extend the existing probability,
recall and execution APIs where possible. Do not introduce another runtime,
application transition system or commitment model.

Graph policy normalization belongs in Vegas.EventGraph; generic clients,
service realization and refinement belong in Vegas.Pending; source
instantiation and composition belong in Vegas.Compile or Vegas.Game according
to their dependencies. The generic graph and pending proof owners must not
import source-specific proofs. Extract shared probability operations to an
existing appropriate foundation owner only when both adapters actually need
them.

## Proof sequence and acceptance gates

### Fix the second-pass interface

- [ ] Specify graph inputs, graph policy semantics, Interaction initialization,
  compiled clients, bounded-menu restriction and a terminal decoder returning
  an explicit unfinished result. The decoder must have no default payload.
- [ ] Use the canonical reference law for graph policies. Make completion-order
  normalization an explicit compiler operation and prove its canonical-law
  preservation using the existing graph normalization API.
- [ ] Express structural requirements through the existing public-barrier and
  information-discipline interfaces. Prove that the first-pass outputs and
  their sequential mode satisfy them.
- [ ] Enumerate the new local hypotheses needed by the runtime proof. None may
  assume the desired whole-run outcome equality or its equivalent.

Gate: the second-pass signature is source-independent, identifies the actual
bounded target and covers both currently compiled dependency modes. A theorem
restricted to the image of the source compiler is an intermediate result, not
completion of this interface.

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

### Preserve policies when disclosure intentions are erased

- [ ] Implement graph-level effective-disclosure normalization and prove that
  it preserves the complete canonical terminal-store law.
- [ ] Preserve the influence of original private actions on later decisions.
  Adapt the existing posterior/disintegration construction to graph recall;
  simply replacing an ineffective true disclosure by false is insufficient.
- [ ] Prove that normalization uses only the player's graph observation and
  actual recall. Do not add a private memory command to runtime actions.
- [ ] Establish the joint initial-store/output law for arbitrary correlated
  finite initial laws. Keep any supported-observation qualifications explicit.
- [ ] Identify the effective graph-policy condition needed by the runtime
  realization proof and derive it from normalization, rather than requiring
  users to discard policies with ineffective disclosures.

Gate: an owner can make a later binding depend on an earlier reveal intention
whose publication failed, and the translated policy still preserves its
terminal law. This is the main semantic proof risk.

### Realize graph policies in the message model

- [ ] Factor source-independent clients from the existing canonical decisions,
  event-recording checks and first-opportunity policy. Clients read normalized
  graph observations and ignore extra clock and pending-message signals when
  choosing a graph action.
- [ ] Prove each decision is sampled once. A pending submission is not
  resampled, and a silent failed or withheld disclosure is not redrawn at a
  later activation.
- [ ] Prove binding candidate freshness and fixed meaning, authentic opening
  provenance, sole-identifier protection, and realization before the supplied
  relative deadline. Silence realizes failure through expiry.
- [ ] Prove that normalized decision observations remain stable while other
  owners' independent hidden bindings complete. Reuse the barrier observation
  and commutation results.
- [ ] Show compiled responses belong to the actual bounded raw menu using
  value coverage and a derived candidate budget. Do not stop at an unbounded
  or privileged client interface.

Gate: local conditional kernels are derived from the existing operations and
all-history service conditions, including histories of rejected traffic.

### Prove the independent second-pass outcome law

- [ ] Prove the exact law first on sequential graphs, then on public-barrier
  graphs with concurrent private bindings. This is an implementation order;
  both cases are required for completion.
- [ ] Compare the compiled Interaction run with the canonical graph run of
  the original profile, composing the disclosure-normalization realization.
  Prove probability equality, not only support inclusion or equal expectations.
- [ ] Preserve the whole typed graph outcome, including initial fields. The
  Interaction readout returns some outcome with probability one under the
  service premises. Obtain payout and other total store-derived observations
  by mapping that same law.
- [ ] Quantify over supplied relative deadlines, timely service schedulers and
  arbitrary pending observation. Do not specialize the capstone to the rank
  calendar, empty pending observation or zero inclusion latency.
- [ ] Instantiate the generic service on a checked concrete scheduler. Reuse
  and factor the existing roster producer as needed; do not treat an assumed
  completion contract as its own operational implementation.

Gate: the capstone quantifies over a graph and graph policies without source
syntax, source histories or source equilibrium hypotheses.

### Compose both passes and consolidate consumers

- [ ] Prove source-to-Interaction preservation by composing the two pass laws
  through the actual terminal decoder. Preserve the joint initial data,
  complete typed source state, public result and executable payouts.
- [ ] Instantiate the theorem for every source profile, including failed
  commitments, failed guards and withholding, in both compiled graph modes.
- [ ] Refactor source-specific client laws to consume the generic graph
  theorem. Update all callers and docs without compatibility aliases or a
  parallel source-only implementation of the same execution proof.
- [ ] Establish the policy/response agreement needed by existing strategic
  consumers, including the off-path sites they use. Equal terminal laws alone
  do not justify replacing clients inside an SE proof.
- [ ] Retain the exact hypotheses and conclusions of the checked Nash,
  recovery SE and monetary capstones. A generic backtranslation of arbitrary
  Interaction deviations and concurrent raw-runtime SE are separate targets.

Gate: the composed theorem is a consequence of the two pass capstones, and
the existing strategic and monetary consumers build against the consolidated
implementation.

## Capstones and manuscript changes

The ordinary-correctness presentation has four capstones. These are roles;
choose domain names for new Lean declarations after fixing their signatures.
Checklist labels and step numbers must not enter declaration names or docstrings.

| Capstone | Statement and paper placement |
| --- | --- |
| Source-to-graph semantics | Retain the existing scheduled terminal-state law, with its full source-profile and public graph-scheduler quantification. State it in the graph section. |
| Interaction-to-graph operational refinement | Every initialized raw trace projects to graph execution with typed-store agreement; service-complete terminal traces decode successfully. State it in the runtime section. |
| Graph-to-Interaction semantics | Source-independent exact terminal-outcome law for compiled graph policies on the supported graph class and the actual bounded target, under explicit service and representation premises. State it in the runtime section. |
| Composed compiler semantics | Exact joint initialized source-state/result/payout law for the actual two-pass clients, without an equilibrium premise. State it beside the compiler tower and distinguish it from strategic preservation. |

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

Use checked Lean consumers that exercise the semantic boundaries: a graph
constructed without a source program, remembered ineffective disclosure,
withholding and expiry, both hidden-binding completion orders, correlated
initial inputs, partial pending observation and positive inclusion latency with
non-rank deadlines. Include empty and chance-only graphs where they expose
boundary cases. Extend existing examples when they already exercise a case.
Runtime sampling experiments are not a substitute for exact-law proofs.

Check the owning modules after each proof checkpoint. At consolidation, run
the ordinary full `lake build`, including Paper and all retained examples;
the module-boundary, Lean-option/source-policy and documentation checks; and
the repository checker unit tests. Check manuscript annotations against actual
capstone signatures and guards. Build the maintained paper, check references,
page limits and overflow, and render/inspect the changed pages.

Commit and push each stable, verified checkpoint: operational refinement;
policy normalization; client realization and second-pass semantics; composition
and consumer consolidation; and final Paper/manuscript synchronization. Keep
the root artifact and separately managed manuscript revisions explicit.
Completion requires every gate above, checked capstones with only standard
axioms, matching paper statements and no pending proof obligations hidden by
an adapter assumption.
