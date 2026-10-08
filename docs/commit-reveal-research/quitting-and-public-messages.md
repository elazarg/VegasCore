# Quitting, publication failure and public messages

Analysis by Codex. This note separates two proposed responses to the
[runtime counterexample](native-late-action-analysis.md): stopping after a
missed publication, and giving source players explicit communication choices.
Neither proposal changes the adopted source, runtime or preservation target.
The positive results cited here are paper theorems for specified interfaces;
there is no full native SE-preservation theorem for either proposal.

## What quitting would have to mean

The counterexample has an immutable Alice bit commitment and an independent
private label A, B or C. Alice opens the bit, then Bob binds and opens an answer.
Successful publication makes Safe Bob's best answer when the labels remain
uniform. If publication fails, Bob instead tries to guess the bit. Different
Alice labels benefit from different failure guesses.

Alice can send the same proper opening at either of two late opportunities.
The earlier send gives Bob more opportunities to learn its contents while
pending, including when it is never accepted. Thus the failure continuation
gives different labels different timing preferences. Consistent inference from
those preferences changes Bob's label beliefs even after successful delivery.
The resulting successful-delivery gain can outweigh the small probability of
losing any fixed finite deposit.

Making a failed player stop submitting packets does not remove that argument
if later answers can still change that player's payoff. A fixed deduction from
the continuing game's payoff also leaves the relative timing incentives intact.
The useful candidate is instead an absorbing settlement: failure fixes the
relevant payoffs, so later knowledge, messages and choices cannot change them.
Players can remember packets and keep physically communicating.

The [several-delivery-decision theorem](delivery-control-preservation.md)
uses the following concrete version. Each immutable opening has a protected
surely successful opportunity. If its owner defers, it can make several send,
wait or retry decisions. Success resumes the source game without additional
transport deductions. Failure ends payoff-relevant play and gives the owner
the same fixed utility -D after every delivery route. Source continuation
utilities are nonnegative. For a fixed operational policy, the owner's value is

\[
qV-(1-q)D=q(V+D)-D.
\]

Here q is its delivery probability and V its expected successful continuation
value. Every retained private type wants to maximize q. When service dynamics
for the same public history and opening do not depend on unrelated private
game data, the owner can use one delivery policy across those types. Its
timing then need not signal those retained secrets.

This theorem includes private learning about service conditions and readable
pending packets. Its source requires successful bindings and mandatory
openings; other players have no strategic choice during the delivery process.
It does not include arbitrary raw extra packets, rejected source bindings or
lawful withholding with arbitrary recovery rewards. The native audit can
charge an unaccepted duplicate even when another copy succeeds, which differs
from the theorem's accounting. The note gives a separate cost variant with
explicit common-policy inequalities. Quitting alone does not supply them.

Sure protected delivery also matters to the exact outcome claim. If even the
prescribed delivery can fail, exact unconditional equality with an always
completing source needs a different argument or a different outcome target.
The [whole-game delivery theorem](whole-game-delivery-preservation.md) studies
genuine outages under stronger service and common abort-settlement conditions.
Its counterexamples show that aborting with low payoffs alone is insufficient:
different actions can have different survival probabilities, or a player can
prefer shifting failure to another player's stage.

## Why failure is local to a publication

The [source semantics](../source-semantics.md) gives each publication an explicit
success or failure result and continues through the fixed program. The
[source design rationale](../../archive/se-generalization/documents/docs/source-design-rationale.md.txt)
explains the relevant design commitments:

- Failure is outside the ordinary payload domain. A program must supply its
  own failure branch instead of receiving an invented ordinary default.
- Failure changes the public publication result and preserves the immutable
  private binding and earlier public effects.
- Rejecting guards and deliberately withheld publications are admitted source
  behaviors. Programs can penalize, reward or recover from them.

For the immutability issue, suppose nullable bindings x and y both contain
some true, with a relation requiring y to be none or equal to x. If y has
already been published, replacing x by none on timeout leaves the ordinary
pair (none, some true), violating the relation. Recording x's publication as
failed leaves both private bindings intact and lets the failure-aware public
rule handle the missing publication.

A constant-false guard is another example: the program has defined execution
and settlement despite having no successful ordinary publication for that
guard. Automatic global termination would select its consequences on the
programmer's behalf.

Consequently, a publication failure and permanent withdrawal are distinct
rules. An absorbing settlement can be a useful supported application class,
but implementing it in a compiler for a program whose failure branch continues
would change the game. A distinction between physical delivery failure and a
lawful source decline could be useful; establishing that distinction and its
observations is a separate proposed interface, not the present semantics.

## What a message attached to binding would add

A source binding could choose a pair consisting of a sealed value and an
ordinary message. Other players would see the message at a specified time,
while the value remains sealed. This adds a real communication choice to the
source game. Equilibria of that enlarged game can account for announcements,
coordination and strategic silence.

It does not by itself establish preservation. Three questions remain:

1. **When can the sender speak?** The counterexample's timing choice is made
   during opening, after the commitment already exists. A message only at
   binding does not represent that later choice. More generally, communication
   before a player learns something cannot represent a later disclosure of it.
2. **Who sees which message, and when?** A message commonly observed by all
   players differs from plaintext that some players have received while others
   have not. Absence, early receipt and remembered receipt can all carry
   information. Readability alone does not define a delivery service.
3. **What does the message establish?** A statement about a private value can
   be false. An authentic opening can establish the committed value even if
   the application rejects it. The communication semantics must distinguish
   ordinary claims from verifiable disclosure when that distinction matters.

There is a useful separation in the existing
[calendar communication study](../abstraction-and-cheap-talk.md). Alice can
signal a private bit through submission timing to Bob, whose pending
observation succeeds with probability p, while Carol sees only the later
ledger record. Bob can guess correctly with probability (1+p)/2; Carol gets
only 1/2. When communication is solely commonly observed public talk, Carol
can use at least the public information Bob used, so the same guessing
advantage cannot occur in equilibrium. This is a paper separation about the
communication channel, not a new full-runtime preservation counterexample.

Adding commonly observed public messages therefore need not represent the
runtime's partially observed traffic. Giving the source more communication
also changes its equilibrium set; it is not automatically conservative for
preservation of every selected source equilibrium. Choosing an uninformative
prescribed message does not dispose of rational behavior after unexpected
delays or messages.

## Candidate research directions

Two separate candidates are worth studying:

- **Settlement discipline:** keep the abstract commit-reveal language and
  identify application classes whose physical failures have absorbing,
  route-independent settlements and compatible delivery costs. Extend the
  paper positive to actual raw packets and audit accounting.
- **Communication-aware interpretation:** interpret programs in a small,
  independently specified communication service, allowing ordinary claims and
  possessed opening evidence at relevant program boundaries. State delivery,
  remembered observations and costs through that service; prove preservation
  for the enlarged source game rather than silently reusing the old analysis.

A message attached to binding is a useful first instance of the second
candidate. General coverage requires a proof that every additional relevant
runtime signal is represented or controlled by incentives. Neither candidate
requires messages already received to become invisible, and neither has yet
been adopted as the project's runtime model.
