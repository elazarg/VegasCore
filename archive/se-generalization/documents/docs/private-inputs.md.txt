# Persistent private inputs

Private inputs model information present before protocol play, such as a
bidder's valuation. They are immutable ordinary values observed by their owner.
The initial prior may correlate inputs with one another and with protocol state.
A player's policy is one function of its observations across this entire prior.

## Representation and access

The typed environment distinguishes `privateInput owner payload` from
`commitment owner payload`. An input contains a value of the payload type; a
commitment contains a possibly unsuccessful binding. Only the initial setup can
introduce private inputs. The syntax has no input-writing operation.

The shared environment representation preserves the existing dependent context
and lookup infrastructure. Separate cell kinds enforce the semantic boundary:

- A player's observation includes its own inputs and commitments.
- Public expressions and settlement cannot read private inputs.
- Guard operands cannot read private inputs, including the guard author's.
- Reveal accepts only a commitment reference.
- Publication accounting tracks commitments alone.

An owner can report any function of its input through ordinary choices. The
input itself remains unchanged, so utilities can compare reports with true
types. This is an access restriction, not a promise that actions disclose no
information about types.

## Compilation

An input lowers to an owner-visible immutable graph input with the same ordinary
value. No graph event can produce this field kind. Public node expressions and
validation cannot read it. The native semantic state retains it for the owner's
observation and for joint-law analysis. It creates no accepted commitment handle,
candidate meaning, packet, reveal event, deadline, or public storage value.

This input is part of the player's initial information. Compilation assumes the
same information at both ends; it does not implement a protocol for generating
or verifying an economic valuation. Protocol-generated private randomness is a
separate language feature.

## Proof contract

The source and native observation correspondence includes the new input kind.
The deviation extraction must use one policy mixture across the entire initial
prior, rather than selecting a policy after inspecting hidden opponent inputs.
The full-store law then projects to the joint law of initial parameters and
public results. The value-binding abstraction leaves private inputs unchanged.
Consequently the same-error ex ante Bayesian equilibrium theorem applies to
utilities of private types and public results without publication obligations
for the types.

Required regressions cover owner and foreign observations, exclusion from public
reads and guards, immutability, empty commitment accounting for input-only
contexts, absence of native handles and candidates, and an auction whose
valuations have no reveal sites.
