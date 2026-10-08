# What is known about SE preservation in the standard runtime

Analysis by Codex.

**We do not currently have a general SE-preservation theorem for the actual
asynchronous audited runtime. We also do not have a checked impossibility
theorem for that full target.** The calendar theorem is a positive result for
a stronger scheduling interface; the late-leak theorem is a negative result
for a particular observation game. Neither settles the general question.
Here "standard" means this repository's `AsyncContract` runtime model; its
sure protected-service assumption is not a claim about an unconditional
liveness guarantee on a deployed blockchain.

## Checked positive results

- **Audited calendar compiler:** every source SE has a native raw-runtime SE
  preserving the required outcome and settlement law, under the theorem's
  service, audit, coverage and deposit hypotheses. Pending traffic can be
  observed; the calendar supplies reliable settlement and the scheduling
  structure used by the information and consistency proof. See
  `Vegas.Paper.source_audited_raw_sequential_equilibrium` and
  `Vegas.Paper.intended_sequential_equilibrium` in
  [Paper.lean](../Paper.lean).
- **Asynchronous Nash correspondence:** the checked client theorem applies
  to arbitrary contract builders with a barrier-ordered graph, including the
  sequential and concurrent-binding modes. Its approximate form has Nash
  error at most the source error plus twice the total deferral weight times
  the runtime payoff range; zero deferral gives exact Nash preservation.
  The intended-game version also bounds outcome-law error by the deferral
  weight. This does not assert SE or cover arbitrary concurrent reveals.
  See `Vegas.Paper.async_client_nash_correspondence` and
  `Vegas.Paper.intended_async_client_nash` in [Paper.lean](../Paper.lean).
- **Intended opening clients, including concurrent reveals:** a specialized
  asynchronous Nash theorem goes beyond that barrier-ordered correspondence.
  Under its well-formedness, effective opening, forfeit, audit and menu
  admissibility hypotheses, it gives the same deferral-dependent Nash and
  law-error bounds for reveal-relaxed scheduling. See
  `Vegas.AsyncServiceSpec.intended_openingClientProfile_isεNash` and
  `Vegas.AsyncServiceSpec.intended_openingExtension_isεNash` in
  [IntendedOpeningNash.lean](../Vegas/Game/IntendedOpeningNash.lean).
- **Fully observed late-opening comparison:** for every inclusion probability
  between zero and one, a checked comparison family with intrinsic forfeit
  twice its reward preserves every intended source SE by a target SE. This
  is a finite comparison game, not a general source-language compiler
  adapter. See [the actual-runtime analysis](actual-runtime-late-opening-analysis.md).

The last result is useful because it prevents attributing the old negative
example merely to public pending messages and high late inclusion probability.
Both properties coexist with preservation in that comparison family.

## Checked negative results and their limits

The selective late-leak game has no preserving target SE in its stated
parameter regime. Its distinguishing information pattern is essential:
different late emissions need not reveal the value before the receiver's
irreversible choice. A public network with propagation delay can have such
a distinction. A full actual-RAW embedding satisfying every service and audit
hypothesis is still needed before this becomes a compiler impossibility.
The broad impossibility wording in the
[async checklist](se-async-checklist.md) should therefore not be read as an
established impossibility for every fully public actual-runtime configuration.
This analysis does not change its owner-controlled target or boxes.

There is also a checked negative theorem for a nearby probabilistic backend.
Mix the actual public controller with a positive probability of waiting on
each runtime round. For a nonempty program and a finite runtime horizon,
there is positive probability that its source readout remains unfinished.
Every source terminal law is complete, so **no native behavioral profile**
can realize that exact law; this excludes Nash, PBE and SE profiles equally.
The primitive all-wait event gives the quantitative total-variation lower
bound. This backend keeps the real application, initialization, observation
interface and raw menus, but weakens sure protected service. It is not a
counterexample under the unchanged asynchronous contract. See
[the probabilistic-runtime analysis](probabilistic-runtime-preservation.md).

## Stronger positive mathematics, not yet checked compiler theorems

The [public disclosure-phase proof](full-public-disclosure-phase-preservation.md)
implements every source Nash outcome, hence every source PBE and SE outcome,
by a target SE. It allows lawful withholding, correlated private types with
full joint support, and arbitrary finite value-dependent late inclusion
probabilities. It needs a surely successful protected opening and an intrinsic
failure forfeit above the sender's base payoff range. Its restrictions include
an immutable disclosed value, one emitted opening and no intervening strategic
choices. The [public-reset composition](public-reset-phase-se-preservation.md)
extends it to phases separated by genuine public subgames already in the
source. Retained hidden state and general raw packet behavior remain outside
these proofs.

The [vanishing-noise proof](noisy-runtime-approximate-se-preservation.md)
gives another positive target: exactly consistent assessments with vanishing
whole-continuation sequential regret and convergent outcome laws for every
selected source SE. It needs a fixed finite game and information structure,
bounded fixed payoffs, and uniformly small primitive chance errors at every
source-compatible history, including deviations. It does not promise nearby
exact SEs, and its actual-runtime tree adapter remains unformalized.

## The remaining question

For the unchanged standard asynchronous contract, can a finite audit deposit
support a consistent, sequentially rational completion of every intended
source equilibrium, across all raw histories and concurrent dependencies?
Sure protected service removes the finite-horizon outage obstruction, but
does not itself answer this question. Accepted late openings can be audit
clean, and an owner's single escrow charge can already be sunk at later
histories. The proof must derive conditional incentives and compatible
beliefs from those actual rules.

A weaker intrinsic-forfeit-only concurrent comparison already exhibits timing
incentives despite complete public observation; a sufficiently large audit
charge repairs that example. See
[the concurrent-disclosure analysis](concurrent-disclosure-se-boundary.md).
It therefore does not refute the intended audited target. At present, the
general audited asynchronous result remains open, rather than either proved
or disproved.

We likewise lack a general actual-runtime PBE-preservation theorem. The
disclosure-phase paper result covers PBE outcomes by constructing a target SE;
it does not establish that weakening SE consistency to PBE solves every raw
asynchronous case.
