# Authenticated disclosure defeats general sequential preservation

## Result

The checked theorem
[`native_no_utility_independent_sequential_translation`](../VegasTests/SequentialValidationImpossibility.lean)
rules out a utility-independent translator from one actual Vegas source game
to its bounded native message game that preserves sequential equilibrium for
all analysis utilities. The translator may inspect the entire source strategy
profile. Target beliefs may depend on the utility. Neither freedom avoids the
contradiction.

This establishes a limitation of the current information abstraction. It does
not establish nonexistence of native sequential equilibria, impossibility for
every runtime, or failure for every source program. A positive result must
restrict the games or services, change the source observations, or change the
preservation requirement.

## The game

Chance selects a uniform Boolean type `θ`, known to Alice. The initial setup
also contains Alice's commitment bound to `θ` and Bob's commitment bound to
`true`. The correlation between the private type and the initial commitment is
an explicit premise of this example.

The source program has four events:

1. Alice commits a dummy Boolean. Its guard depends on the later publication
   of her initial commitment and is contradictory: `x ∧ ¬x`.
2. Alice resolves the dummy commitment.
3. Alice resolves her initial commitment.
4. Bob resolves his commitment. Success represents guess `true`; failure
   represents guess `false`.

The dummy guard is deferred. On the particular prefix where the dummy was
successfully published, resolving Alice's initial commitment records **failure**
even if she supplies its correct opening. The source public observation exposes
that failure and omits the proposed value.

Alice's utility is zero. Bob's utility is zero when Alice's initial commitment
is successfully published. When that publication fails, consider two analysis
utilities:

| Utility | Bob receives one exactly when |
|---|---|
| Match | His guess equals `θ` |
| Mismatch | His guess differs from `θ` |

Both utilities read only the original private type and public publication
results. They do not reward packets, clocks, rejection receipts or hidden
implementation state.

## Why the source has the same equilibrium for both utilities

Use uniform behavioral choices at every source decision, independently of the
type: the dummy commitment ranges over failure and the two Boolean values,
and disclosure choices range over `false` and `true`. The source already has
the full forfeiture interface; the example does not elide malformed commitment
behavior at binding.

The profile is fully mixed. Its Bayes assessment is sequentially consistent.
At every Bob information set with failed publication, the posterior on `θ`
is uniform. Every replacement continuation has expected payoff `1/2` for
either utility. At successful-publication information sets both utilities are
zero. Alice is indifferent everywhere.

[`VegasTests.SequentialValidation.source_sequential_equilibrium`](../VegasTests/SequentialValidationEquilibrium.lean)
checks this for the actual source protocol, all legal source histories, and
whole continuation-policy deviations. This is a source sequential equilibrium,
including its beliefs and consistency proof.

## What the native execution exposes

Alice can transmit the correct opening of her initial commitment. The native
handler authenticates the opening, issues a successful receipt and applies the
deferred guard, which records publication failure. The public ledger retains
the packet containing `θ`.

| At Bob's decision | Source observation | Native observation |
|---|---|---|
| Alice's game publication | Failure | Failure |
| Her proposed opening | Absent | Present in the public ledger |
| Evidence tying that opening to the initial commitment | Absent | Successful authenticated receipt |

Rejecting a value as a game publication does not erase a transmitted opening.
Here authentication and game validation are separate operations: the packet
passes the former and its proposed publication fails the latter.

The native receipt invariant proves that **every** compatible history has the
disclosed original type. This includes histories outside prescribed play.
Consequently, every belief on this information set assigns probability one to
that type. The proof does not assume that the entire information set is a
singleton.

## The native service and response domain

The fixture uses the actual reactive application and finite response menu:

- Each activation is one optional transmission, with commitment meaning fixed
  at submission. There are no strategic private preparation steps or scratch
  memory fields.
- Each of the four events has a grant, an owner activation and an authorized
  uniform inclusion opportunity. These twelve service decisions precede clock
  advancement. The calendar is fixed independently of packet contents.
- Inclusion requires dependencies to have been complete at submission. Each
  envelope can be included at most once, including rejected calls. Selection
  uses the event and author, with equal weight for eligible envelope identities.
- The remaining forty-four service decisions provide ten clock ticks and an
  expiry for each event in order. Each event has deadline ten.
- The finite value alphabet contains both Booleans and integers `0` and `1`.
  All packet constructors, wrong addresses, foreign handles, malformed data,
  silence and known-envelope replays are available. There are fifty-six
  prepared handle identifiers per player.
- The observation rule samples no in-flight messages in this fixture. The
  disclosure is already public on the ledger. The general observation-rule
  interface and partial foreign leaks remain available in the runtime.

The bounds and service are ideal model assumptions. This is not an EVM
encoding or an incentive argument about miners. The public-history dependency
monitor is also an ideal service; constructing ledger-verifiable authorization
evidence is a separate implementation obligation.

[`native_runtime_completes`](../VegasTests/SequentialValidationCompletion.lean)
proves that the complete fifty-six-decision run finishes every graph event
under arbitrary raw player policies. The finite horizon does not truncate an
unfinished game. This completion result also covers responses outside the
finite alphabet used to define the equilibrium instance.

## The contradiction, including the whole native continuation

The legal disclosed prefix ends at Bob's only activation. Across its entire
information set, Bob has no previous response, there is no earlier Bob-authored
pending envelope, and exactly forty-five service decisions remain. Earlier
foreign traffic cannot compete in the final selection for Bob's event.

Bob can submit his correct opening or a withholding packet. Both responses
belong to the full finite menu. Their inclusion forces the two respective
public guesses; the timeout tail cannot change a stored result.

For arbitrary responses, not just these two packets, the proof establishes a
common final guessing law across all histories in Bob's information set. It
uses provenance, submission authorization, owner-local handler observations
and the actual clock/expiry continuation. Thus different beliefs about hidden
earlier histories cannot give the same prescribed strategy different guessing
probabilities.

Fix the observed type to `false`. Sequential rationality for Match requires
prescribed payoff at least one, because Bob can choose `false`. Rationality
for Mismatch requires prescribed payoff at least one, because Bob can choose
`true`. The two prescribed expected payoffs sum to one for any common native
strategy. They cannot both be at least one.

The source assessment is the same for both utilities. A utility-independent
translator would produce the same native strategy for both and contradict
[`native_no_common_rational_strategy`](../VegasTests/SequentialValidationImpossibility.lean).
The failure is already in continuation rationality, before imposing target
belief consistency. Consistent-completion existence therefore cannot repair it.

## Proof map

| Obligation | Checked artifact |
|---|---|
| Actual source sequential equilibrium for both utilities | [SequentialValidationEquilibrium](../VegasTests/SequentialValidationEquilibrium.lean) |
| Actual lowered guard and authenticated failed publication | [SequentialValidationNative](../VegasTests/SequentialValidationNative.lean) |
| Receipt evidence fixes the type at every compatible history | [SequentialValidationEvidence](../VegasTests/SequentialValidationEvidence.lean) |
| Fixed calendar, authorization, at-most-once inclusion, response bounds | [SequentialValidationService](../VegasTests/SequentialValidationService.lean) |
| Legal scheduled prefix and actual Bob information site | [SequentialValidationHistory](../VegasTests/SequentialValidationHistory.lean) |
| Information-set timing, recall, provenance and observed type | [SequentialValidationFibre](../VegasTests/SequentialValidationFibre.lean) |
| Arbitrary response and complete continuation laws | [SequentialValidationResponse](../VegasTests/SequentialValidationResponse.lean), [SequentialValidationNativeIncentives](../VegasTests/SequentialValidationNativeIncentives.lean) |
| Timeout completion under every raw player profile | [SequentialValidationCompletion](../VegasTests/SequentialValidationCompletion.lean) |
| Native rationality contradiction and translator impossibility | [SequentialValidationImpossibility](../VegasTests/SequentialValidationImpossibility.lean) |

## Consequences for language design

Keeping source forfeiture is insufficient for general sequential preservation.
The missing behavior here is authenticated disclosure even when the game
records failure. A future language/service design must account for that
observation before another player makes a consequential choice, or establish
a condition under which it cannot change incentives. The proof does not choose
surface syntax or a compiler flag.

The [communication interpretation](ambient-communication.md) implements that
distinction without changing `PublicationResult`. For this source game,
[`CommunicationDisclosure`](../VegasTests/CommunicationDisclosure.lean)
checks that the guard still records plain failure, while the opening supplies
a certificate that fixes the private type under every compatible belief. It
also constructs a legal private disclosure before the first source command.
These results address the information mismatch; they do not establish native
sequential-equilibrium preservation for the extended source game.

The [cryptographic future-work note](cryptographic-runtime-future-work.md)
separates commitment validity, forced recovery and controlled disclosure.
Validity proofs and timed recovery address different restrictions. Neither
by itself prevents an owner from transmitting a known, publicly verifiable
opening. No advanced cryptographic mechanism is implemented or assumed here.
