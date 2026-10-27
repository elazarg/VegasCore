# Lossless summaries for a Boolean evidence audit

The terminal reporting stage need not publish every body a reporter knows.
For the singleton/pair verifier below, each reporter can send an authorwise
summary whose size depends on authorized protocol slots. The union of these
summaries proves exactly the same Boolean violations as the union of the full
bundles, including violations completed by bodies supplied publicly later.

This is an optional replacement for the full terminal evidence bundles in the
[authenticated construction](se-asynchronous-authenticated-construction.md).
It does not change application publication, capture, exposure, or the delivery
guarantees needed for reporting. It does not introduce a trusted monitor.

## The verifier and its fixed inputs

Fix the public certificate and controller data C at the frozen end of base
game play. Later archive publication adds bodies but does not change this
controller state or retroactively validate an invalid capability. Let M_i be
the finite set of complete canonical application bodies authenticating author
i for this session. Exact copies denote the same body. Unauthenticated data,
data from a different author, and signatures for unrelated sessions are not
evidence against i. An invalid inner tag is distinguished from failure of
this outer session-authentication check.

Use the typed, nonnested authenticated-body grammar of the construction. A
body does not contain an unaccounted nested application signature from another
author. Initial-binding and phase certificates are separate public-proof
sorts, rather than another player's private application entry.

Let S_i be the finite set of authorized physical slots for author i over the
whole bounded session, including retries, and write H_i = |S_i|. The verifier
uses these positive predicates:

* An intrinsically invalid body has a format, ownership, type, component,
  handle, or authorization defect verifiable from that body and C. In
  particular, a body without an authorized slot in S_i is intrinsically
  invalid. Reusing a handle for two components of one body is also a
  singleton defect.
* Two distinct bodies naming the same slot constitute a conflict.
* Two binding/component occurrences in distinct bodies using the same handle
  for distinct bindings constitute a handle-reuse conflict.

For E contained in M_i, define Bad_i(E; C) to hold when E contains an
intrinsically invalid body or one of these conflicting pairs. Every accepted
witness therefore uses at most two complete bodies, together with C and
bounded component indices. The predicate is monotone in E.

Public initial-binding data may instead be represented by fixed public bodies.
They are then included in the public set P below, not charged to a reporter's
private summary. The theorem is unchanged. The local summary need not know
which further bodies will have appeared publicly by final settlement.

The singleton/pair grammar is essential. The proof does not apply to a
predicate based on absence of a message, a hidden sending order, an accumulated
number of offenses, or a time-dependent reclassification of previously valid
bodies. A private guard failure invisible in a commitment handle is not made
auditable by this summary.

## The summary

At the reporting freeze, reporter j holds a finite set K_j of complete
authenticated application bodies. For a foreign author i, let

    K_j^i = { b in K_j : b authenticates author i }.

Define the summary S_j^i as follows.

1. If Bad_i(K_j^i; C) holds, choose one witnessing singleton or pair using a
   fixed canonical order, and send those complete bodies.
2. Otherwise send K_j^i, deduplicated by canonical body identity.

In the second case every body has a slot in S_i, and distinct bodies cannot
share a slot. Consequently there is at most one body per slot and

    |S_j^i| = |K_j^i| <= H_i.

This case can equivalently be implemented as retaining the unique
representative of each occupied slot. No arbitrary choice between conflicting
bodies is made: finding such a pair takes the first branch instead.
In either case

    S_j^i is a subset of K_j^i,
    |S_j^i| <= max(H_i, 2).

The reporter sends the union of S_j^i over foreign authors i only. The test,
canonical witness choice, and representative selection for i use only the
i-authored stream and the fixed public data C. They do not depend on another
author's stream. An unauthenticated claimed author is never enough to enter
one of these sets.

## Union-preservation theorem

Let P_i be any finite public set of i-authored bodies available to the final
audit. It may include retained-prefix bodies which were still in flight when
reporting knowledge froze. Let J_i be any set of reporters eligible to report
against i. Then

    Bad_i(P_i union union_(j in J_i) K_j^i; C)
      iff
    Bad_i(P_i union union_(j in J_i) S_j^i; C).               (1)

**Proof.** Each summary is a subset of its full local set, so the right-hand
side implies the left-hand side by monotonicity.

For the converse, first suppose some reporter j has a local violation
Bad_i(K_j^i; C). Its summary contains a complete witness, so the right-hand
side holds independently of what the other reporters or public archive
supply. Otherwise no reporter has a local violation. By the definition of the
second branch, S_j^i = K_j^i for every reporter j. The two unions in (1) are
then identical. This includes a violation lying wholly in P_i, a pair split
between two reporters, and a pair split between a reporter and P_i. ∎

Thus no reporter has to know whether its body completes a witness held
elsewhere. For example, if one reporter knows only p and another knows only q
for the same slot, each sends its representative and the final union retains
both. If a reporter knows both, it can send that pair and discard its other
bodies from the same author. Cross-slot handle reuse is preserved for the
same reason: absent a local violation, no local body is discarded.

The statement holds for every possible P_i. In particular, it does not require
reporters to predict the final public archive. It does require the original
irrevocable publication guarantee if that archive is supposed to supply an
earlier conflicting body. If neither a reporter nor the final archive holds
that counterpart, compression cannot manufacture it.

## Encoding and delivery bounds

Let a_i bound the encoded length of one complete i-authored body, including
the required fixed-size framing, authentication and certificate references.
Let h_j bound reporter j's bundle header and framing. A prescribed summary
bundle has encoded length at most

    h_j + sum_(i != j) a_i * max(H_i, 2).                   (2)

Bounded witness indices can be included in a_i or added as a separate fixed
per-author overhead. The public verifier can also locate the offending
components from the complete bodies. Verification and ledger execution costs
need their own bound; an encoding-length bound alone does not prove a gas
bound or timely inclusion.

For a fixed reporter set, sum (2) over reporters to obtain the total prescribed
report workload. This removes enumeration of all possible values or handle
names from the body-count bound. Their representation lengths still contribute
to a_i, as they must. The number of reporters, authorized slots, retries and
components remains relevant.

The bound is for these prescribed summaries. It does not prove that all raw
reporting traffic has this size or that a larger raw report cannot congest a
shared queue. The reporting backend must still protect admission and delivery
of the prescribed bundle against every bounded raw continuation in scope.
Earlier application traffic or partial reports must not consume its reserved
final reporting entitlement. If there are several reserved reporting slots per
reporter, their number belongs in the capacity and fee bound.

There is no claim of one global witness per offending author. The distributed
reporters may each need their slot representatives before anybody can assemble
a pair. Reducing that further needs an additional exchange, aggregator or
availability argument.

## Reporting incentives and the equilibrium composition

Reporter j's prescribed summary excludes every j-authored application body.
The full raw report menu may still contain self-reports, malformed wrappers and
newly learned bodies, as in the
[strategic reporting construction](se-strategic-reporting-mathematics.md).
In the typed grammar, a reported foreign body also contains no hidden
j-authored application entry. Base game payoffs are frozen, canonical reporting has zero
net player cost and no positive player reward, and each proper report's final
delivery is guaranteed independently of the others' report choices.

Under these conditions the same terminal reporting argument applies with
summary-all in place of full report-all. Other reporters' frozen summaries of
j-authored data do not change when j changes its own foreign-evidence report.
The final old public j-authored archive is fixed by the earlier publication
promises. Therefore changing j's foreign-only report cannot change its own
Boolean audit liability. A raw alternative which additionally exposes
j-authored bodies can increase that liability but cannot decrease it, by
monotonicity. Malformed wrappers cannot erase evidence or execute application
instructions. The prescribed summary is consequently sequentially optimal
under every belief, including after earlier reporting mistakes.
This is an equilibrium-specific reporting prescription; it is not a claim
that every raw reporter will provide the summary.

Equation (1), applied for every author, identifies the entire Boolean charge
vector with the full-bundle reduced game at every pre-report history. Hence
the reduced continuation payoff vector is unchanged, not just its value on
the selected equilibrium path. A pre-report equilibrium and its consistency
witness can consequently be reused for this reduced game.

To restore strategic reporting, give each reporting action positive
probability while placing total mass at most rho_n on departure from the
prescribed summary. If H_R bounds the number of future reporting choices,
the conditional probability of any future perturbation is at most H_R*rho_n
at every reporting history. With net payoff range B_R, the corresponding
continuation-value error is at most B_R*H_R*rho_n, and a two-action gain error
is at most twice this quantity. Include the current mixed reporting choice
in H_R when comparing it with a pure alternative. Future reports do not change
pre-report reach or Bayes beliefs. The common finite subsequential-limit
argument therefore lifts the same reduced equilibrium to the strategic
summary-reporting game.

This preserves Boolean penalties and the intended initialized game law.
It need not preserve the terminal evidence transcript or the number of
provable offenses. A per-offense charge or residual-reserve audit requires a
different summary invariant. Finally, the theorem leaves the main exposure
obligation untouched: a payoff-relevant bad body must actually reach a
nonculprit reporter or the final public archive. Neither this summary nor
reporting incentives turn passive retention by an unrelated ingress into
evidence delivery.
