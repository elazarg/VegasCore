# Concurrent commitment preservation

This is the proof design for intended Nash preservation. The dependency and
prescribed-policy scheduling lemmas are checked in
[BindingConcurrency](../Vegas/EventGraph/BindingConcurrency.lean) and
[PrefixPolicy](../Vegas/EventGraph/PrefixPolicy.lean). The equilibrium and native
runtime statements below remain proof obligations; they are not paper claims.

## Target

Retain the source program, information model, initial distribution, payoff and
native application. Permit independent bindings of different owners and
independent reveals to complete in either order. Retain public barriers, causal
reads and the order of each owner's bindings. No independence assumption on
private inputs is needed.

For every intended approximate Nash equilibrium, construct prescribed clients
with the same approximation error and the same joint law of the full terminal
source configuration and payoff vector. Their supported outcomes have no
defaults or failed reveals. Deviations retain the full chronological observation
and all available actions. Use the existing fixed-exit utility, or the existing
forfeit at least as large as the utility spread. Native transport should use
the existing service and timeliness contracts.

The target concerns intended equilibrium preservation. Arbitrary source profiles
can condition on an earlier commitment's public omission, which an early
concurrent decision has not yet observed. Preserving all such contingent choices
is a separate, stronger problem.

## Prescribed observations

Sorting completed events alone does not reconstruct a source decision. The
default log has one slot per completed instruction, including successful
instructions. An intended policy can count those slots. A commitment completed
early would otherwise see a different information value even on successful play.

At event rank `e`, prescribed clients receive the source-ranked prefix before
`e`, with one default slot per source instruction and their own earlier actions
in rank order. Public-event default markers are retained. Private-binding slots
carry `none`, including bindings not yet completed. Visible values stay in the
existing projected store. Publications always open. These are restrictions on
the prescribed policies, not changes to players' actual observations.

Under the existing reveal-relaxed barrier discipline, foreign binding
completions leave this decision interface unchanged. Concurrent publications
leave the prescribed opening action unchanged. The existing ready-independence
theorem therefore gives exact public-scheduler independence of the final store
and per-event completion records.

## Deviations and failure

First compare payoffs with a fixed-exit surrogate whose exit payoff is no greater
than any ordinary utility. Repair an active binding omission by submitting an
opaque unopenable binding. The omitted branch immediately defaults the player
and pays the exit value; the repaired continuation is bounded below by that
value. Non-omitting actions are unchanged. The existing analogous argument
replaces withholding by opening. This is a fixed-exit comparison, not a claim
that repairing omissions increases the actual forfeited utility pointwise.

Prescribed policies also submit at every active binding. Thus, after repair,
private-binding completions create no new default markers. Automatic
completions of an already defaulted owner create no new decisions. The prefix
interface agrees with the ordinary source prefix on these executions.

Fix a deterministic public scheduling tape. At a selected binding decision,
the tape, source-visible public values and public default markers determine
the actual chronological completion transcript up to that decision. The replay
witness must be selected at the same binding event: equality of padded prefix
observations alone does not identify the current cut. Public barriers and
same-owner order then recover the player's actual visible values and own-action
history. Predrawing public scheduler randomness yields a mixture of source
deviations. Source equilibrium bounds each member of the mixture.

Finally, every reachable default entails a failed reveal under the existing
binding-revelation invariant. The actual forfeited payoff is bounded above by
the fixed-exit surrogate and agrees with ordinary utility on intended play.
This transfers the deviation bound without an additional economic assumption.

## Native transport

The native application already has hidden-binding inclusion and prepared-handle
opacity lemmas. Canonical commitment packets do not expose the chosen value;
same-owner order fixes the prepared serial at each binding. The required new
operational proof is a coupling for a whole private-binding block under the
existing service contract. Treating each binding as the sole ready event would
restore serialization and would not establish the target.

Exact sequential assessment replay and concurrent sequential equilibrium are
separate obligations. A native prefix can contain a later binding before an
earlier source binding has been chosen, so the current deterministic linear
prefix replay cannot simply be reused as a correspondence at every native site.
