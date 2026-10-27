# Silence and collateral after exclusion

A failed player can retain a refundable communication bond. Failure need not
consume all of its collateral, and new provable misconduct can incur a further
loss. This is a contract choice, compatible with asynchronous submission and
private reception. It is useful even though it does not make every disclosure
detectable or erase a message sent before failure.

The mathematical claims below distinguish selecting silence in an SE from
making every later message strictly unprofitable. They are hand derivations,
not a checked asynchronous preservation theorem.

## Silence need not be a restriction on the network

Suppose a finite perfect-recall game has a public permanent exit marker.
After player i exits, suppose its **total** utility is F_i under every
continuation, and silence is legal at every remaining site. Then every
continuation policy of i is optimal, including
silence at every information set. Other players can still be affected by
its messages; their payoffs need not be constant.

There is a common consistency construction. At each excluded-player site,
mix silence with a full-support law of total mass epsilon_n>0 tending to
zero. Fix those policies. Complete the remaining handler information agents
jointly by a constrained equilibrium with positive action floors tending to
zero. Excluded players' gains are exactly zero. At each other handler site,
constrained optimality bounds conditional regret by the floor mass times
the terminal payoff range, with no inverse-reach loss.
A common subsequence of the fully mixed Bayesian assessments supplies
consistent beliefs and rational play at all handler information sets.
The limit prescribes silence for every excluded player, including off path.

Together with the hypotheses of the
[first-quitter extension](se-quit-handler-preservation.md), this preserves
the intended no-failure SE. The native pre-exit adapter is still required.
In particular, this does not establish that a late attempted transmission
is equivalent to a source Quit.

Assuming failed players cannot send would instead delete legal target actions.
That can define an intermediate restricted game, but an actual implementation
theorem must reintroduce those actions and prove the incentive comparison.
The construction above explains when deleting them is unnecessary.

### Fixed base payoff is not fixed net payoff

The existing theorem `Vegas.phase_excluded_terminal_payoff` in
[PhaseExclusionPayoff](../Vegas/Game/PhaseExclusionPayoff.lean) fixes the
excluded player's **base** utility under every raw continuation. If actual
utility is F_i minus audit charges, incoming rewards or collection effects
must still be accounted for. For example, a message that suppresses reporting
of an earlier offense could improve net utility even though base utility is
unchanged.

There is a weaker existing comparison useful for extending a clean restricted
equilibrium: every raw continuation with nonnegative penalties has utility at
most F_i, while a clean retained source continuation pays F_i. The direct
branch of
`GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends_of_local_collection`
in [LocalizedEnforcement](../GameTheoryExtensions/Analysis/Protocol/LocalizedEnforcement.lean)
can use that inequality. It supplies rational completion at new information
sets; it does not assert that silence is optimal at every already-charged
target history.

## An additional bond and the exact deterrence inequality

Separate two liabilities:

* the failure penalty needed to keep the excluded payoff at its specified
  floor;
* a refundable reserve available for additional communication violations.

Keeping part of an existing failure forfeiture refundable may raise the
failure payoff and invalidate the floor argument. A separate additional
reserve avoids that change. Normalize net utility relative to the initial
stake so full return of the reserve adds no gain to the intended payoff.
With no new violation, the excluded player still receives F_i.

At an actual information set I, compare one legal quiet continuation Q with
a continuation A that sends. All expectations below use the same conditional
belief and the same prescribed strategies of other players. Let W be all
utility except the new reserve charge, R>=0 the amount at stake, and C the
charge indicator. Then exactly

    V(A)-V(Q)
      = E[W_A-W_Q | I]
        - R (E[C_A|I]-E[C_Q|I]).

Consequently, if the non-reserve gain is at most G and the **incremental**
collection probability is at least q, then

    V(A)-V(Q) <= G-Rq.

If G=0 and q>0, any R>0 makes sending strictly worse. The inequality Rq>G
suffices for a uniform strict bound on messages with possible gain G.
The comparison must use one
legal quiet policy across all hidden histories in I, not an oracle choosing
a different policy in each hidden history.

A positive chance of some penalty is insufficient. If C_A=C_Q=1 because a
single binary slash is already inevitable, its incremental probability is
zero. Keeping that doomed deposit locked changes collectibility, not incentives.
Likewise, a new message can affect old evidence collection; monotonicity of the
verifier alone does not show that old expected liabilities cannot decrease.
Already-public irreversible charges or a proved reporting noninterference
property can establish that fact.

### Repeated offenses

The simplest useful reserve pays for the first detectable post-exit offense
and is independent of earlier active-phase penalties. It can deter that
first offense even when the ordinary failure forfeiture is already lost.
Once the new reserve is itself inevitably lost, another offense has no
additional penalty under that binary rule. This need not prevent selecting
silence in an SE, but it prevents a claim of strict deterrence at every site.

For a bounded game, let N bound the number of distinct provable additional
offenses along any legal raw execution. This is a bound on the actual raw
action/evidence domain, not merely the number of source events. Reserving
N tranches of size R can fund an additional charge for each such offense.
If old liabilities cannot decrease and a new unpaid tranche is collected with
conditional probability at least q, the same G-Rq comparison applies even
after earlier tranches have been lost. All outstanding liabilities, including
unreported offenses, must fit the reserve.

This does not make every physical retransmission a new provable offense.
An old signed body does not identify its latest broadcaster or date its latest
private delivery. Repeating an already-penalized body may produce no additional
chargeable witness. Fresh attributable occurrence evidence is needed to charge
each occurrence separately. With genuinely fixed net utility, silence can
still be selected when further messages are only weakly deterred.

Keep the reserve locked through the survivors' remaining game and the full
evidence-collection window. Releasing it shortly after its owner's exit would
permit a later disclosure while surviving players still have choices. A finite
game/evidence horizon supplies a finite release time; indefinite observability
cannot be inferred from a finite escrow.

### Existing implementation boundary

`GameTheory.Enforcement.TerminalAudit.settlement` in
[TerminalAudit](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean)
currently subtracts one deposit according to one Boolean verdict per player.
That is a single-charge adapter. The underlying localized-enforcement theorem
already accepts a real-valued charge function, so finite additive charges do
not require a different equilibrium-extension principle.

For a realized verdict vector v, the additional settlement would be
sum_k R_k*v_k. Its expectation is sum_k R_k*Pr(v_k=1), whether or not the
verdicts are independent. An implementation still needs the corresponding
multi-charge settlement-law adapter, collectible escrow, and retained-history
payoff matching. An expected-charge calculation alone does not specify the
joint realized settlement law.

## What an actual ledger can establish about lateness

There are three different cases:

| Event | Consequence |
| --- | --- |
| A new attributable violation after exclusion | An unpaid reserve can deter it under the incremental collection bound. |
| A message sent before exclusion but received later | Silence after exclusion does not remove it; later receipt alone does not prove later sending. |
| A new receipt of an old signed body | The body proves its author and content, not who retransmitted it or when. |

An ordinary signature does not provide a trustworthy sending time. A stored
old phase authorization can also be reused after exit. More collateral cannot
make two evidentially identical histories distinguishable.

A receipt-based rule can avoid asserting a private sending time. Let e be
the public exit time, and suppose every retained qualifying pre-exit opening
admitted at s<=e is finalized on the ledger by s+Delta. Let r(m) be the first
ledger record of the canonical signed opening body, including an admissible
evidence report. Consider a charge when

    r(m) > e+Delta.

Every retained pre-exit opening is clean because

    r(m) <= s+Delta <= e+Delta.

This assumes every relevant retained disclosure really enters that qualifying
admitted class. Private receipt of bytes that never enter it supplies no such
bound.

An opening first recorded within that grace interval may have been sent after
exit, so this rule does not punish every post-exit send. If the contract delays
the next semantic binding until strictly after the finalized cutoff e+Delta,
however, those recorded openings are already public before that choice.
An as-yet unrecorded old opening disclosed privately at a later binding has a
late first record whenever the audit eventually collects its signed body.
A reserve can make that disclosure costly when collection has the required
incremental probability and the body has not already consumed that charge.

Prior ledger publication establishes that the opening payload is public.
Choosing to replay that body to a particular recipient at a particular time
can still convey a new signal; the payload argument does not erase such
operational observations.

This uses an individual inclusion bound for retained qualifying messages, not
a full queue flush or public sender order. It still needs that bound. Without
it, an honestly sent pre-exit opening can have the same late receipt as a new
post-exit disclosure, so the rule need not preserve retained payoffs.
Messages never collected, unauthenticated hints and repeated disclosures after
an already-inevitable charge remain outside strict deterrence by this rule.
The [audit analysis](se-asynchronous-audit-feasibility.md) gives the reporting
and evidence hypotheses separately.

## What this resolves for preservation

Post-exit silence is a reasonable equilibrium prescription, and residual
collateral can support it without assuming that failed players lose their
ability to communicate. Neither public sender turns nor complete mempool
visibility is needed for these incentive arguments.

Legal messages nevertheless remain in every fully mixed consistency sequence.
Survivors therefore still need consistent beliefs and rational continuations
at information sets reached after a disclosure. The
[private handler extension](se-quit-handler-preservation.md) handles that
source-level completion under its hypotheses.

The remaining native issue is a message sent or observed **before** its author's
public exclusion, possibly followed by success, failure or another player's
exit. No post-exit silence rule undoes that information. Residual collateral
addresses additional misconduct; the
[asynchronous preservation analysis](se-asynchronous-preservation.md) still
requires the pre-exit timing, information and attribution comparison.
