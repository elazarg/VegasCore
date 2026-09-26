# Sequential-equilibrium compiler: theorem, inference and boundaries

This is the implementation plan and reading guide for SE compilation. The
[ideal-sanctions proof](research/se-ideal-sanctions.md) contains the generic
mathematics; the [native pilot](research/se-native-pilot.md) contains the checked
source-to-runtime instance. General source-to-native SE preservation is open.

## Compiler contract

Fix a source program, its declared utilities, initial distribution, backend
service and observation rules. Compile one native game, including any inferred
deposits, before choosing a source equilibrium. The primary theorem is:

> Every source SE has a native SE with the same joint initial-type,
> public-result and actual net-payoff law.

The structural proof additionally extends source behavior and beliefs at retained
information sets. Additional native equilibria are allowed. Equality of the two
sets of SE outcome laws is a stronger, separate property: even dominated added
actions can change off-path beliefs and create additional equilibria.

Compiling the game and translating player policies are distinct tasks. Generic
continuation completion can depend on the whole source assessment. It therefore
does not yet supply a fixed playerwise policy compiler, although the native
guessing pilot has one. Do not claim executable strategy synthesis from a
noncomputable equilibrium-existence proof.

The compiler may inspect declared utilities to select deposits. If a theorem
instead ranges over arbitrary external utilities, it must specify their bounds
or another common incentive certificate. A monetary deduction has the claimed
utility effect only under the stated preference model.

## One compilation tower

```text
SourceProgram + Setup + declared payoffs
                 |
                 v
              EventGraph
                 |
                 v
Pending-message application + specified native service
```

The native service specifies observations, inclusion, deadlines, bounded
responses, and any monitoring and collection mechanism. It is a backend
parameter, not a language in which the programmer rewrites the game.

The command-policy service used by the Nash/Bayesian theorem and the reactive
service used for SE are backend instances. A proof for one is not an
intermediate SE edge to the other. Concrete cryptographic or ledger execution
would require its own refinement beyond this idealized target.

These are analysis constructions, not emitted tower levels:

- The permitted part of the native game, used to identify source choices.
- Quotients by proved operational aliases of private response names.
- Information-agent normal forms used to construct consistent continuations.
- A finite tree/table extracted for checking incentives or exact SE formulas.

Ambient communication is an alternative source interpretation when a capability
must be retained. It is not automatically inserted to make an ordinary-source
preservation claim true. A compiler diagnosis must identify the capability and
the resulting change to the game's strategic meaning.

## Three proof obligations

### 1. Identify permitted native behavior with the source

Relate initialization, legal alternatives, information and chance laws at every
retained decision, including source withholding and admitted failure. Preserve
the joint terminal law. Forced service steps may be erased only with a proof
that their observations and timing do not change the decisions being compared.

Implement this as a relation between the existing protocols and their histories.
A narrower information menu alone is invalid: execution legality and the
resulting history space must agree. Source-to-graph correctness, completion of
the service, and the existing reactive policy translation are ingredients;
their initialized laws alone do not discharge continuation correspondence.

Every bounded raw native response must have an account: source behavior, a
proved alias, or an extra choice handled by an incentive argument. An alias
proof cannot erase different publicly visible packets merely because their
application effects match.

### 2. Establish conditional incentive bounds for extra choices

At every retained information set, show that an extra action is no better than
some legal source alternative after accounting for collectible loss. The bound
must respect the player's information and use additional future loss; an
already inevitable one-time charge supplies no fresh incentive.

The simple sufficient certificate is bounded base gain and a uniform positive
conditional collection probability. A sharper certificate compares actual
continuation gains and collection together, admitting harmless undetectable
actions. It need not catch every extra action or prevent every leak.

Soundness applies to all permitted source behavior, not just a selected profile.
Attribution, reporting, timely adjudication and remaining collateral must be
established separately. Ordinary passive sampling does not establish collection.
A mechanical reporting rule and an equilibrium of strategic reporters are
different implementations with different proofs.

### 3. Construct one consistent, rational completion

Pin a source consistency sequence, make forbidden trembles sufficiently rare
relative to compliant-history reach, and complete the other information sets
jointly. Preserve retained beliefs and apply the posterior one-shot principle
to whole continuation policies. After a departure, behavior is allowed to differ
from source behavior and must be rational with the information actually received.

The generic completion and local-to-whole-policy results are checked. The
remaining formal bridge derives their retained-strategy, belief and incentive
premises from obligation 1 and the certificate in obligation 2. It must not
assume a target SE, a rational completion, or the desired incentive inclusion.

## Inference rather than compiler flags

The intended compiler result consists of the ordinary compiled program, an
enforcement configuration, a preservation certificate and an explicit list of
backend assumptions. Game-specific analysis chooses the configuration; the core
language does not need a separate syntax option for each obstruction.

For finite rational comparison data, collect inequalities

`gain_k <= collection_k * deposit`.

Here the two coefficients describe the same conditional comparison. With
nonnegative collection coefficients, a zero coefficient requires a nonpositive
gain. Otherwise the least sufficient nonnegative deposit for this certificate is

`max(0, max_k gain_k / collection_k)`.

The inner maximum ranges over positive collection coefficients; when there are
none, zero suffices if every gain is nonpositive.

For several collectible charges, use a vector of deposits and linear
inequalities. Source-legal comparator lotteries can also be inferred, provided
one lottery works across every hidden history and continuation being compared.
The [sanctions note](research/se-ideal-sanctions.md) gives the finite certificate
and proof. Enumeration can be large; a solver may search for a candidate while
Lean checks its inequalities and the operational extraction theorem.

This is the least deposit for the chosen sufficient certificate, not necessarily
the least deposit preserving SE. A comparison against every continuation can
be stricter than a comparison against equilibrium continuations. The existing
range/detection bound is a conservative instance, not a weakest assumption.

A caught abort can be synthesized only when its actual continuation utility is
controlled. For compliance value `V`, missed value `U`, caught value `F` and
detection probability `p`, the exact comparison is `U - V <= p * (U - F)`.
Replacing future actions by failure does not by itself implement an arbitrary
negative `F`, revoke information, or guarantee payment.

The analyzer has three honest outcomes:

| Result | Evidence |
| --- | --- |
| Certified | A structural correspondence and incentive certificate, with inferred parameters and backend assumptions. |
| Obstructed | A source SE whose retained law no target SE can match, or an exact proof that the specified repair family has no solution. |
| Unresolved | A sufficient certificate failed, an operational premise is missing, or a complete search exceeded its budget. |

Failure of the linear certificate is not an impossibility proof. Repairs may
change the target enforcement configuration; changing source payoffs, source
observations, or admitted strategies changes the specification and must be
presented as such.

## Exact detection and synthesis on finite inputs

For explicitly finite games with rational or algebraic data, preservation is a
first-order formula over the reals. If `P(D)` means every source SE has a
matching SE in the fixed target with deposit `D`, the synthesis question is

```text
exists D >= 0, forall sourceAssessment,
  SE_source(sourceAssessment) -> exists targetAssessment,
  SE_target(D, targetAssessment) and Match(sourceAssessment, targetAssessment, D)
```

The deposit precedes the equilibrium quantifier. `Match` compares joint laws;
it can additionally require extension of retained strategies and beliefs. An
exact decision procedure can therefore classify every given finite pair and
determine all successful parameters within a specified repair template. This
is the semantic weakest condition for that template and guarantee, rather than
a single weakest collection assumption for all runtimes.

The [real-algebra reduction](runtime-abstraction-classification.md#an-exact-decision-procedure-in-principle)
gives the consistency encoding, probability laws, parameter quantifiers and
proof of the reduction. It is a written algorithmic argument, not an implemented
or Lean-verified solver. Its cost confines it to small reference examples and
diagnosis; it is not the first implementation dependency of the compiler.

Exact synthesis does not justify rounding a parameter, assuming a least
solution, or assuming larger deposits always work. Such properties hold for
the nonnegative linear sufficient certificate above and require separate proof
for a general repair template. A specified fixed playerwise strategy compiler
can be checked when its graph has an effective finite algebraic description;
synthesis of arbitrary unknown compiler functions is not this decision problem.

## Assumptions to keep visible

| Assumption | What it enables; what remains outside it |
| --- | --- |
| Finite value/response alphabets and bounded interaction | Standard finite SE and finite inference. Timeouts alone do not bound pre-deadline traffic. Cover all source output values; do not silently truncate the game. |
| Perfect recall | Consistent local optimality implies whole-policy rationality. The current generic Lean construction also assumes common-depth information sites and adequate evaluation fuel. |
| Faithful permitted histories and observations | Source behavior is genuinely implemented. Clock signals, rejected plaintext and visible encodings require proofs, not a declaration that they are administrative. |
| Correct utility model | Deposit deductions and abort payoffs have the intended incentive effect. Voluntary entry and available wealth are separate questions. |
| Sound, attributable, collectible consequences | A reporting opportunity becomes an expected utility loss. Strategic watcher behavior needs its own equilibrium argument. |
| Stated commitment/evidence capabilities | Ideal ownership restrictions do not establish cryptographic security after secrets or keys are shared. |

There is no globally weakest set across changes to utilities, available
communication, monitor powers and source observations. The exact finite check
compares such choices once their operational meaning is fixed.

## Implementation order and acceptance tests

1. **Close the generic restriction theorem in Lean.** Derive retained history
   laws and beliefs from a genuine action restriction; compose the checked
   completion and sequential-rationality results. Add the finite comparator
   certificate so positive detection is required only where incentives need it.
2. **Discharge the native correspondence on a game class.** Use the existing
   source, graph and reactive protocols. Include multiple dependent decisions
   and all bounded raw responses. Exercise the three cases below before claiming
   coverage of general programs.
3. **Infer and check enforcement parameters.** Extract finite comparisons from
   those operational proofs, synthesize deposits, and check exact certificates.
   Reproduce the native pilot and demonstrate a genuinely new multistage class.
4. **Add exact finite diagnosis.** Export the same games to the real-algebra
   encoding, verify the extraction/translation, and use small cases to measure
   conservatism and produce genuine failures. Keep general solver engineering
   separate from closing the first compiler theorem.

The decisive runtime cases are:

- **Early or rejected openings:** plaintext can matter before inclusion. A
  punishment rule needs evidence of when transmission was permitted; judging
  delayed traffic solely against the current stage can punish lawful behavior.
- **Opaque unopenable commitments:** valid and forfeited bindings can have the
  same public packet. Ordinary observation does not justify a positive detection
  premise. A game-specific irrelevance argument, admitted source forfeiture,
  or a stronger validity backend must account for the omitted choice.
- **Signals in permitted representations:** separate enforceable canonical
  encodings from choices that remain observable. An additional signaling SE
  alone does not refute forward preservation; prove harm to the chosen contract.

These tests and the existing checked obstructions are regressions, not extra
languages or mandatory compilation stages.

## Ownership and documentation

- `GameTheoryExtensions/`: restriction/completion theorem, finite incentive
  certificates, and SE formula correctness. Leave the GameTheory submodule alone.
- `Interaction/`: runtime observations, collection interfaces, operational alias
  laws and finite execution extraction, independent of Vegas syntax.
- `Vegas/`: source/graph/native correspondence, game-specific conformance,
  utility extraction and composed compiler theorem.
- Existing test roots: positive compiled instances and minimal obstructions.

The public result should consist of the ordinary Nash/Bayesian theorem, a
conditional SE compiler theorem with an inference algorithm, and precisely
scoped obstructions. SE existence and agent-form games support the proof.
The [artifact map](../ARTIFACT.md) records checked declarations. Detailed native
audits and research notes explain their premises; they do not extend the tower.

CE and coalition enforcement, strategic paid watchers, cryptographic refinement,
unbounded traffic, computational/approximate SE and channel-noise bounds remain
separate research. They should enter the compiler contract only through a proved
additional instance or a stated change of assumptions.
