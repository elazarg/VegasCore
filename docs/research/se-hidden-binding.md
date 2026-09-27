# Hidden unusability: audit limitation, conditional simulation, SE obligation

## Decisive checked facts

An unusable binding is not publicly identifiable in general.
`VegasTests.UnusableBindingAudit.auditTrace_eq` compares actual reactive binding,
inclusion, granted revelation and withholding steps. Valid binding followed by
legal withholding and unusable binding followed by withholding have identical
public snapshots, including phase, input authors, pending packets and receipts.
Their private meanings remain different and fixed. `no_sound_detection` rules
out charging the latter while an audit is silent on the former.

That fact is **not** an SE impossibility. There is now a stronger positive result
than initial Nash simulation, in `Vegas/Source/ValueBindingContinuation.lean`:

- `bindValues_runFrom_publicOutcome_eq` repairs a pure continuation from any
  residual source configuration, preserving its registry, revelations and own
  action histories rather than resetting them.
- `exists_valueBinding_continuation_mixture` repairs every behavioral
  continuation, using one mixture for every configuration in a finite list.
- `exists_valueBinding_belief_mixture` preserves the joint law of any parameter
  of the starting configuration and the public result, for an arbitrary finite
  belief over configurations. The mixture is chosen before the hidden state.
- `exists_valueBinding_continuation_ge` gives a value-only continuation with
  conditional utility at least as high as the original continuation.
- `ValueBinding.admitted` makes every repaired policy legal under every existing
  commitment interface, including value-only admission.

These results cover the full existing source syntax: public chance, subsequent
bindings, deferred guards, disclosure, and withholding. They impose no equilibrium
or reachability premise on the starting belief. Opponents keep the same source
policies and observations. Utility may depend on persistent private parameters
and public results; it may not reward the hidden representation of a future
commitment that the repair deliberately changes.

The native prefix facts are checked in
`Vegas/Pending/ReactiveBindingObservation.lean`:
`reactiveBinding_network` equates the complete network after either private
meaning is fixed; `reactiveBinding_include_other_input` also preserves receipts
and every foreign player's actual recall/current input through inclusion;
`reactiveBinding_activation_other_input` preserves the law of passive reads
under the original observation rule. Initial correlations and previously known
foreign evidence are unrestricted. The owner's own observations need not agree.

## Finite admission and clean-prefix contract

A nonvacuous finite SE theorem for fresh commitments needs finite legal source
payload domains, not merely finite target packet bounds. In particular, a full
integer commitment menu has no fully mixed finite-support behavioral law under
the current `FinDist` assessment definition. A theorem quantified over source
SEs must not conceal that absence. The finite admission must retain every legal
source value and every legal withholding action; it is fixed before the source
equilibrium is chosen. The target capacity includes these values, one repair
default in each nonempty admitted domain, and fresh canonical handles for every
remaining source binding site. The program's finite event count bounds those
handles. No default depends on the unobserved state of an opponent.

At the starting retained prefix, runtime/source stores agree except for the
owner-private bindings explicitly tracked by `Patched`. Public data, other
players' private cells, accepted handles, completion order, network state,
receipts, and other players' response recall agree. Candidate meanings are fixed
at transmission. Earlier pending and known packets must already be accounted
for by the retained transcript. A preexisting raw opening of the repaired handle
is not harmless: it may reject on the unusable side and succeed on the valid
side. Such a packet belongs to the observable-departure branch below.

The service assumptions must be proved for each compiled construct. The checked
revelation service does not already supply a full-language binding/chance
calendar or an arbitrary ambient-communication schedule. The ordinary target
message space remains available; admission bounds and protected opportunities
are explicit backend assumptions, not exclusions justified by an equilibrium.

## Why the repair is local enough, and why the current comparator is too strong

At the start of a continuation, replace any future failed binding with a
canonical valid value. At that binding's later disclosure, withhold instead.
The existing `Patched` invariant reconstructs the deviator's original view and
own actions; every other player's view and own history stays unchanged.
`bindValues_publicOutcome_eq` already proves this for arbitrary related residual
configurations, not only for initial execution.

The transformation edits a whole future policy. It is local to a continuation
and uniform across its hidden states, but it is not a replacement of only the
current action followed by unchanged play. In particular, replacing a failed
binding with a valid value and then leaving a later opening unchanged can alter
the public result. Failure of that one-action comparator is not strategic gain.

Sequential rationality already compares every whole continuation policy. The
required generic relaxation therefore allows an extra target action's future
behavior to be simulated by a mixture of whole source continuation policies,
instead of requiring one legal source action with the old continuation unchanged.
Every mixture component is bounded by source sequential rationality.

## Exact remaining native obligations

The conditional source result does not yet prove native SE preservation. The
native adapter must establish the following facts, rather than assume them:

1. From a retained native prefix, a privately unusable binding and the repaired
   source continuation give every **other** player corresponding future views.
   This includes accepted handles, response recall, pending observations and
   deferred-guard effects. The sender's own extra private information is mapped,
   not incorrectly identified with the source information state.
2. Opponents' prescribed policies must continue to agree at those corresponding
   views after the hidden departure. Agreement merely on the originally
   embedded execution histories is insufficient by itself.
3. A later observable departure is handled by the audit/collection argument.
   The conditional source simulation does not cover arbitrary leaked certificates,
   new public signaling, or arbitrary native opponents after such traffic.
4. New private information sites need rational continuations in one common
   consistency construction. Existing action-restriction completion supplies
   that mechanism only after its structural embedding and retained-belief
   hypotheses are actually instantiated.

The existing generic restriction proof can retain its consistency-completion and
one-shot-to-whole-policy machinery. Its retained-site comparison should accept
whole continuation mixtures. That change alone does not discharge obligations
1–3, and this note does not claim a completed full-language SE theorem.

## Stopped-path proof design

The target comparison is universal over paired source/target continuation
profiles; it must not assume target sequential rationality.

1. Draw a repair-policy seed independently of the hidden starting configuration,
   using `exists_valueBinding_belief_mixture`. Retain that one seed for the whole
   continuation. Replacing the mixture separately at each hidden history would
   change correlations and is not a valid comparison.
2. Couple the actual source/native execution until the first publicly
   nonconforming transmission. A privately unusable binding does not stop this
   coupling. Its repaired value uses the same opaque handle, and the repaired
   owner withholds when the original binding could not publish. Common public
   chance draws, passive samples, inclusion decisions and protected deadlines
   must preserve the coupled prefix invariant by actual runtime transition laws.
3. At each nondeviating player's decision, prove its complete native input is a
   retained input with the corresponding source view. Then `ExtendsProfile`
   supplies its law. Equality of current ledger states alone is insufficient:
   private response recall, prior leaks and timing are part of that input.
4. If no visible departure occurs, the terminal private-parameter/public-result
   law is exactly the source repair law. Hidden owner representations are not
   required to match.
5. At a first visible departure, condition on the coupled prefix. A fresh
   collectible loss must cover the full remaining payoff range, uniformly over
   later policies and later authentic audit transcripts. This permits arbitrary
   post-departure target play. A penalty already sunk on that branch provides no
   further deterrence; charges are not silently counted twice.
6. Average over the starting posterior and the single seed. Source whole-policy
   sequential rationality bounds every legal repair continuation. Only then use
   the common-consistency completion theorem for the native extra private sites.

Steps 2–3 are the missing native induction. The checked prefix lemmas and source
repair establish ingredients, not this induction or the final comparison.

## Guards and copying

Deferred guard rejection is not an unavoidable honest disclosure in the current
compiler: `reactiveResolutionPacket` emits withholding when the proposed opening
does not publish successfully. A raw opening that still carries a rejected
secret is extra traffic and may be audited. The source repair preserves guard
results because guard reads use public data and revelation results; its existing
proof covers the whole obligation registry.

In the current ideal runtime, binding acceptance requires ownership of the
candidate handle; a third party cannot bind another player's opaque handle as
its own source commitment. Certificates may be forwarded once known. Copying a
publicly disclosed value is source-representable; additional private certificate
disclosure is an information-flow obligation for the audit adapter.

A cryptographic backend that permits copying an opaque commitment without
knowing its value requires a separate analysis or a knowledge/nonmalleability
assumption. The checked conditional repair concerns unusable binding in the
existing ideal semantics and does not establish preservation for that larger
cryptographic action space.

**Conclusion:** no forward-SE counterexample from hidden unusability has been
established. We have proved its lack of conditional source best-response gain.
The remaining issue is a native information/continuation simulation and its
consistent extension, not a demonstrated need to expose malformed commitment
values in the source language.
