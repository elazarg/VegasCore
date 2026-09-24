# Selective association: proof contract

This compares **accepted named-binding evidence** and **candidate evidence later
associated with a binding**. No sequential-equilibrium impossibility for the
full named-evidence source service has been proved yet.

## Source evidence capability

Use the full existing `Vegas.Source.CommitmentEvidence` interface. A fact is
true only when its source name already occurs in the current context with the
stated successful binding. The owner may transmit any such fact; recipients
may forward facts they possess. False claims remain freely available.

The initial setup has no commitment bindings. Thus no certificate naming the
first future binding can be issued initially. Certifying an unaccepted proposal
would be a further evidence capability: the current `Holds` predicate does not
assert facts about proposals or future source names.

## Matching service timeline

The following is the proposed witness schedule, with its proof obligations
still to be discharged for a complete native game.

1. Alice has an ambient response. Its envelope remains pending.
2. Bob activates, with a passive leak rule selecting only Alice's first envelope.
   Bob then has an arbitrary response. It is neither recorded nor leaked to
   Alice or Carol before their next decisions.
3. Alice has another response for her binding event. The reserved selector
   includes her latest envelope addressed to that event.
4. Carol chooses her hidden guess and its binding is included.
5. Bob has his final guess response and reserved inclusion.
6. Ordinary opening events occur. There is no automatic opening primitive.

Carol's and Bob's guess bindings both depend on Alice's binding; neither
depends on the other guess. The service processes Carol's guess first. The
candidate leak rule is stateless: it selects Alice's first envelope only for
Bob, and selects no envelopes for Alice or Carol. It inspects no private
delivery history. A second Bob activation may revisit the old envelope;
[`MessageNetwork.learn`](../Interaction/MessageNetwork.lean) excludes each
identifier for which `network.known who` already contains a message.

Every source response retains all possessed named certificates, arbitrary
claims, and forwarding. Envelopes are immutable. Any new named certificate
emitted after association has a new envelope identity and is not privately
delivered before the guesses under this rule. Recording it makes it public;
public disclosure remains available and must be covered by the source
equilibrium proof. An already pending certificate is not silently excluded:
the argument must show that no certificate of this previously absent binding
could have been valid when the earlier envelope was emitted.

## Actual native capability and admission risk

Alice's first native envelope can register a candidate `h` with value `x` and
carry its opening certificate. Her later envelope can bind that same `h`
without carrying a certificate. The checked association theorem states that
Bob's earlier candidate certificate and the public accepted association imply
the named binding at every compatible native history.

Candidate registration currently requires a commitment call. It is not a
standalone seal operation. The first packet may itself bind the game event if
included. The witness must therefore prove that the stated schedule leaves it
pending and selects Alice's later envelope, including after arbitrary replay
and competing traffic from Bob. This coupling may not be erased in the source
service contract.

The native prefix is checked in
[`ReactiveAssociationEvidence.lean`](../VegasTests/ReactiveAssociationEvidence.lean).
`later_envelope_selected` proves the latest-envelope selection for every Bob
response, including replay. `association_after_arbitrary_response` proves
Bob retains the earlier certificate and recognizes the accepted binding.
`carol_input_after_arbitrary_responses` proves equality of Carol's full recall
and current view even with different Bob responses in the two worlds;
`carol_activation_after_arbitrary_responses` extends it through the actual
passive-observation activation. This fixture has only Alice's binding event.
The subsequent guesses, opening choices, and strategic conclusions remain
unproved.

## Remaining strategic obligations

- Extend the checked Carol input equality through the complete service and
  guessing game, retaining arbitrary earlier responses.
- Prove Bob retains a fresh corrective guess opportunity: no earlier response
  has irrevocably completed his binding, and the final response is selected.
- Declare a finite candidate bound sufficient after every allowed earlier
  response. Do not infer such a bound merely from game deadlines.
- Specify utilities solely on the original types and public game results.
  If opening failures carry penalties, prove optimal opening at every relevant
  information set, including after earlier deviations. Do not replace these
  choices by forced publication.
- Construct a source assessment using the full named-evidence menus and one
  common fully mixed consistency sequence, then prove the native deviation
  bound against arbitrary sequentially rational continuations.

The operational association result alone does not rule out a one-way SE
compiler. A source service that already grants prospective evidence or a
matching retrospective disclosure rule needs a different analysis. No claim
that every implementation requires an ambient seal registry follows here.
