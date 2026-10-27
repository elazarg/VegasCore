# End-to-end preservation with direct ledger audit

This is the assembly of the finite mathematical construction. Every bounded
current-session authenticated message is recordable. Its audit evidence comes
from the public ledger, without an honest evidence collector or strategic
reporting. The source game, initial law and utilities remain those of the
intended source program.

The implementation adds fixed windows, publication barriers, forced exclusion,
commitment rollback and funded authenticated submissions. Players can wait,
send late, send malformed or conflicting bodies, replay messages and act after
exclusion. Their network observations may differ. Only actual ledger
publication creates the public archive.

This is a hand derivation for the specified runtime. It is not a checked Lean
result or a theorem about every bounded-delay builder. Nonrevocable submission,
fresh independent body service and the observation/reset laws are substantive
runtime conditions.

## 1. Statement and order of quantifiers

Fix a finite, well-formed linear source program, a finite-support initial law,
finite strategic value domains and its intended perfect-recall game S. Require
finitely many histories, including finite support for every reachable source
sample. Initial private inputs may be arbitrarily correlated. Fix the bounded
implementation, clock, raw message menus, service and observation kernels,
funding and verifier before choosing a source equilibrium.

Every bounded authenticated current-session body uses one broadcast/submission
primitive which creates its immutable recording job. Outer recording accepts
malformed, conflicting and stale inner game calls. There is no nonrecordable
authenticated body class in the primary model, and no separate operation for
announcing those same bytes without submission.

The observation and service hypotheses are:

* Semantic opacity: operational observations cannot inspect unrevealed candidate
  meanings or hidden source values. At binding sites their path weights factor
  from the source law conditional on the actual source information. Authorized
  reveal payloads may be observed through a mechanically selected visibility
  mask, independent of their values.
* Own-service freshness: observations before a body's first submission reveal
  no information about its fresh service coins. Its success probability p_e(a)
  depends only on its structural class, submission time a and public parameters
  fixed at window entry, not on evolving within-window semantic publications.
* Independent service: body jobs are independent and cannot be cancelled,
  delayed or accelerated by later messages, replays or observation choices.
  Exact copies do not create fresh jobs.
* Reset compatibility: new-namespace service and observations are independent
  of discarded old traffic, including changes to old replay policies. The
  old record is a causal auxiliary observation of the retained coarse history;
  current actions and inert old replay coordinates have the stated product
  menu. The concrete fresh-namespace/reset construction proves this quotient.

Complete-body receipt is unnecessary for audit collection. Partial bodies,
opaque metadata and counts are allowed when these conditions hold. Counts
indexed by current namespace can satisfy them. An unlabeled total count mixing
old replay noise with new traffic need not: old private memories may reveal
which new event caused it. The theorem does not admit every value-blind
observation rule merely because it cannot read a hidden payload.

For each player i choose a permanent exclusion payoff F_i below every active
base payoff, including failure continuations. Let U_i bound all base payoffs
from above. Fix refundable audit collateral

    D_i >= U_i-F_i.                                           (1)

The audit subtracts D_i once when a positive violation by i is proved.
Penalties are not redistributed to game players. Publication fees use a
separate fixed reserve; they are not deducted from the preserved game payoff.

**Preservation statement.** Every sequential equilibrium sigma of S has a
sequential equilibrium of the full finite implementation with the same joint
law of initial source data, typed terminal source results, projected source
public results and realized net game payoffs. On that implementing law no
player is excluded or charged. This selects an implementing equilibrium; it
does not assert that every implementation equilibrium reproduces sigma.

The [runtime specification](se-broadcast-runtime-mathematics.md) instantiates
these hypotheses. Correlated builder outages and the current Lean reserved
tape are not automatically included. Unbounded message domains and an arbitrary
additional communication channel are outside the statement.

## 2. Components of the proof

| Component | Mathematical result | Concrete producer |
| --- | --- | --- |
| Source-to-block correspondence | Batching transports the source consistency witness and initialized law. | Own-information guard structure; componentwise openings preserve reveal and sample order. |
| Publication | Every submitted authenticated body is public by its individual deadline. | Body-keyed immutable validation, per-author per-run funding and independent bounded inclusion. |
| Retained equilibrium | One fully mixed family has vanishing local regret on actual information sets. | Fresh-body timing optimizer and the explicit reset/menu quotient. |
| Raw extension | One causal retained continuation dominates each additional raw choice. | Saved semantic debt, permanent exclusion, or inevitable audit after a forbidden submission. |
| Ledger collection | Every required positive witness belongs to the final public archive. | All authenticated bodies are recordable; retained counterparts cannot be cancelled. |
| Selected joint law | The implementing limit has no failure or charge. | Protected submissions, source transition correspondence and the restriction-extension law. |

The supporting derivations are the
[source adapter](se-asynchronous-pre-exit-construction.md#8-the-source-adapter-for-finite-linear-vegas-programs),
[fresh-service proof](se-asynchronous-support-weakening.md),
[semantic raw comparison](se-asynchronous-authenticated-construction.md) and
[runtime specification](se-broadcast-runtime-mathematics.md).
The direct-ledger specialization below replaces the latter comparison's need
to wait for a receipt with the earlier stopping event of actual submission.

## 3. Publication, funding and final audit

A body has a canonical key. A key can be consumed only by recording that exact
body. Replacement, cancellation, shared nonces, validator changes and fee
withdrawals cannot invalidate an admitted recording obligation. Inner game
rejection cannot revert its outer record. Induction on runtime transitions
therefore proves persistent validity and funding after submission.

The service's nonrevocable timely-inclusion contract applies to those submitted
jobs. Hence a body submitted at a is public by a+Delta under every later raw
profile. Merely remaining eligible is not a delivery proof; creating the job
at broadcast and its bounded service are explicit assumptions. Ordinary
account-nonce replacement does not supply them.

For author i, let H_i bound its action opportunities, b_i its fresh-body batch
size and c_i the maximum recording fee. Put

    N_i = H_i*b_i,       reserve_i = N_i*c_i.                  (2)

At any prefix after k opportunities, at most k*b_i new keys have received
irrevocable earmarks. The remaining reserve covers every possible later fresh
batch. Different authors' reserves and audit collateral are segregated.
Private preparation does not consume them. This is a bound on bodies submitted
in one execution, not a reserve for every body in the finite payload alphabet.

Copies need no new job. Their bounded intake still costs resources. With G
fixed genesis bodies and replay multiplicity L per known body, the number of
known bodies is at most G+sum_i N_i, so a per-step occurrence bound is
b_i+L*(G+sum_i N_i). Current fresh choices and old replay coordinates remain
a product; there is no smaller shared cap that makes a current action
unavailable after choosing old replays.

In this count, a replayable known body has already been broadcast or is a
genesis record. The first network use of a privately prepared signed body
consumes the fresh-body cap, even though its author already knows its bytes.

If w_i bounds one recording's work, per-block application capacity at least
sum_i N_i*w_i is a simple sufficient bound for every possible set of due jobs.
Independent inclusion coins may still defer other pending jobs; this does not
require flushing every queue in every block. Audit and intake work use their
own finite per-run bounds. A smaller backend must prove the same publication
and noninterference properties under all raw continuations.

Let T0 be the base-payoff freeze and last strategic submission point. Pending
jobs continue after it. Choose final audit time

    TA >= T0+Delta.                                          (3)

Every submitted authenticated body is then in the actual final public archive.
There is no report tail or C_report term in the primary construction.

## 4. Construct the retained equilibrium

Call R the intermediate game. Before public failure it permits source-admitted
semantic choices and all specified operational choices, including late sends
and exact replays. After failure it uses the structurally audit-clean handler
of the fresh-service proof. Removed raw choices are restored in section 6.

Batch each player's component choices within a private-choice block using the
product of its original behavioral probabilities. Its intermediate observations
contain its earlier own choices and no newly available foreign semantic data.
Use distinct canonical component handles and reveal only components in their
original reveal block. Samples and public observations retain their order.
A vector deviation is a legal source continuation. Finite perfect recall
therefore transports source local bounds to the batched game. Let r_n tend
to zero bound these comparisons along one source consistency witness.

A window has fixed public readiness, last protected submission time A and
settlement D=A+Delta. The next binding window waits until D+Delta. Every proper
opening submitted by D is public before that next binding, even when its inner
call was rejected as late. At D, the ledger determines success or exclusion
before another strategic decision. No optional timeout call is needed.

At an unsent body class e and time t define

    q*_e(t) = max_(a >= t) p_e(a),                            (4)

where a ranges over remaining admissible current-window times, including
never-send with probability zero if necessary. The earliest maximizing
clock policy attains (4), conditional on every relevant foreign completion
scenario C. An adaptive policy only averages p_e(a)'s, all bounded by (4).
Own-service freshness is essential to this conditional calculation. At protected
times the maximum is one.

A failed commitment window rolls back the whole unsaved current block. Saved
obligations, private inputs, exclusions and actually public values remain.
Fresh namespaces and service isolate later attempts from old jobs. The chosen
handler filters old-namespace replay noise while players retain their actual
observations. The reset/menu quotient, including its conditional own-history
factor, justifies this prescription.

At an opening site, conditioning on foreign scenario C gives

    F_i + Pr(own success | I,C) * (W_i(C)-F_i),

where W_i(C)>=F_i and is invariant under successful focal timing. At a binding
site with source information J and vector a, the a-dependent term is

    q*_e(t) * Pr(foreign completion | I) * v_source(J,a).      (5)

Foreign failure rolls back a, so the remaining term is independent of a. The
coefficient in (5) is independent of remaining hidden source state at J by
the source/operational factorization. This is an all-index likelihood claim,
not a claim about the limiting strategies alone.

Use canonical current names and proof representations. Lift old-public-body
replays with a fixed positive product law. Their effective gain is zero, and
they supply positive probability to every retained literal replay coordinate.
No additional representation-floor error is needed.
Here canonicality is enforced by the valid grammar or a unique ideal primitive;
it is not just the reference policy's choice among additional valid aliases.

Perturb current operational prescriptions by total mass epsilon_n and solve
the coarse handler agents jointly with local regret delta_n. For H remaining
operational decisions and payoff-difference bound B, actual retained local
gain is at most

    max(r_n + 2 B H epsilon_n, delta_n).                       (6)

This is a conditional future bound from the actual information set. It has
no inverse reach-probability term. The handler uses the same index's actual
entry law. A common subsequential limit of the fully mixed profiles and their
Bayes beliefs is a sequential equilibrium of R.

## 5. Positive audit evidence at submission

Use the total, monotone, authorwise positive verifier. Malformed inner syntax
or an invalid actual phase/accepted-binding certificate gives a singleton
witness. Two distinct bodies for one physical slot, or improper handle reuse,
give a pair. Exact repeats are not offenses. Genuine signatures from unrelated
sessions are not chargeable current-session evidence. Hidden semantic guard
failures are handled by debt, not an invented visible witness.

Let A_bad be the first submission of an auditable forbidden body before the
base freeze, unless own exclusion or saved semantic debt stops first. Every
body in that submission batch is immediately committed to eventual recording.
All retained-prefix counterparts have immutable recording promises. Thus

    W subseteq P_final                                      (7)

for the complete positive witness W at final audit. A pair can consist of two
bodies in the same new batch. The verifier needs neither a global emission-order
oracle nor a participant who privately received or recognized the violation.

The stopping event is submission, not receipt. Arbitrary subsequent observation
effects of the forbidden body are already covered by its inevitable charge.
Complete-body receipt and suppression-until-exposure noninterference are not
needed for this raw comparison. The retained timing and reset proof still
requires the observation conditions in section 1.

## 6. Restore all raw actions directly

Let G be the full finite application game with final deterministic ledger audit.
At a retained information set, fix every extending opponents' profile, every
belief on the retained fiber and an additional raw choice by player i.
Construct one legal retained continuation using i's actual information and
private virtual memory. It copies structurally compatible packets and repairs
pre-exit semantic choices behind the same opaque canonical names. Matching
physical broadcasts preserve all other observations until a stopping boundary.
The comparator is one causal policy over the fiber, not a hidden-state-selected
family of policies.

Before public exit, the retained source menu provides an admitted semantic
choice. After exit R already permits current structurally clean raw values,
including unusable and guard-invalid ones; these are copied literally. No
post-failure admitted-value selector is assumed. A first historically valid
old disclosure of an already excluded owner uses the permanent own-payoff
comparison rather than a fabricated audit offense.

There are three stopping cases.

1. If the earliest bad semantic obligation is irreversibly saved, truthful
   completion eventually checks its guard at the last required publication;
   withholding or unusability also excludes its owner. Its eventual raw base
   payoff is F_i. Before save, a rollback can erase the entire unsaved block.
2. If the owner exits, its base payoff is permanently F_i and later audit
   charges are nonnegative.
3. At A_bad, equation (7) guarantees charge D_i for every subsequent raw
   profile, so terminal raw net payoff is at most U_i-D_i<=F_i.

A clean retained comparator can remain quiet and obtain at least F_i at any
stop. If no stop occurs before base freeze, the coupled base utilities agree;
nonnegative raw charges cannot improve the result. Consequently

    E[raw net payoff - retained comparator payoff]
      <= (U_i-F_i-D_i) Pr(A_bad) <= 0.                        (8)

This proves the direct continuation-extension premise over the whole information
fiber and for every required extending profile. There is no fixed report
strategy and no assumption that strategic witnesses cooperate.

Apply
`GameTheory.Protocol.InformationModel.ActionRestriction.sequentialEquilibrium_extends_of_continuation_unclocked`.
It gives an SE of G, supplies consistent rational completion at newly available
raw information sets, and preserves the selected retained initialized law.
The exact Lean interface and current runtime scope are recorded in the
[mechanization inventory](se-asynchronous-mechanization-inventory.md).

## 7. Initialized law and optional reporting extensions

On the retained limiting path, protected submissions arrive by their deadlines
and no window fails. Source transition correspondence preserves typed results,
projected public source trace and their joint law with initial private data.
All retained bodies are audit clean, so net payoff equals source payoff. The
raw restriction extension preserves this initialized law. This proves the
hand statement in section 1 for the specified finite target.

Strategic reporting remains a separate [extension tool](se-strategic-reporting-mathematics.md)
for a model with some nonrecordable authenticated messages. For that variant,
choose evidence snapshot TK=T0, reporting cutoff TS, and
TA>=max(TS+Delta,TS+Delta_R). Its fixed simultaneous rounds, segregated funding,
monotone authorwise verifier and zero-cost own-free reports yield a selected
report-all equilibrium via one common fully mixed sequence. None is used by
the primary theorem. The [evidence-summary result](se-evidence-summary-mathematics.md)
can reduce such reports without creating missing evidence.

This does not establish preservation for a separate announcement-only operation
on proper protocol bodies. Terminal reporting can collect evidence while still
leaving a failed owner's announced value private at the next binding decision.
That enlargement needs a retained timing/information proof, not merely a final
audit mechanism.

A concrete EVM carrier or a different network must prove the stated message,
funding, publication and observation interfaces. Neither an honest audit party,
a generic deadline nor an ordinary sender-nonce transaction is substituted for
that refinement.
