# Absorbing failure as the source language semantics

Absorbing failure changes the source games. A player cannot withhold once and
later resume successful play. The replacement belongs to the ordinary intended
game -> source -> dependency graph -> ledger tower: the intended game restricts
source menus, and each remaining level has one authoritative executor.

This research branch implements the absorbing source kernel and ports its
protocol presentation. Graph execution, ledger unification and the compiler's
ordinary and equilibrium theorems still require ports. A checked source module
does not establish source-to-ledger preservation, and the full branch is not a
verified replacement for the maintained tower. The paper and its pins are
unchanged.

## Authoritative source execution

[Semantics](../Vegas/Source/Semantics.lean) has one recursive evaluator,
`SourceProgram.runFrom`, over `Config`. The protocol uses the same sample,
binding and revelation successors. Execution returns the complete terminal
configuration; public projection retains public typed cells and default history.

A binding decision is `Option (PublicationResult payload)`:

* `none` omits the binding and publicly defaults the owner immediately;
* `some (.success value)` accepts an ordinary opaque binding;
* `some .failure` accepts an opaque but unopenable binding. Its owner remains
  active until a public failed opening, unless another public default occurs.

The binding cell stores a `PublicationResult`. Equal hidden cell contents do
not imply equal public default events. In particular, the source cannot infer
public default from hidden failed binding values. The runtime's corresponding
distinction is receipt-based: see
[ExclusionApplication](../Vegas/Pending/ExclusionApplication.lean) and
[PublicFailureEvidence](../Vegas/Pending/PublicFailureEvidence.lean).

An active owner's attempted reveal runs the retained guard checks. Withholding,
an unopenable binding or a rejected publication produces public failure and
defaults that owner. Every later owned instruction completes automatically with
failure. It queries no policy callback and appends no invented own action.
Automatic openings still resolve their binding and retain guard bookkeeping.
Public samples follow their declared laws and execution continues.

Policy callbacks accept proof that their owner is active. This removes unused
inactive responses from the strategy type and permits exact strategy
equivalence with legal protocol policies. It imposes no restriction on an
active player's action law. The source kernel proves persistence of default,
automatic failure and absence of automatic own-action recall.

[AbsorbingFailure](../VegasTests/AbsorbingFailure.lean) checks complete runs with
withholding, binding omission and accepted unopenable bindings. The last case
permits an intervening successful binding before the bad opening becomes public.

## Public information and recall

[DefaultHistory](../Vegas/Foundation/DefaultHistory.lean) is the single
authoritative public default record. Each completed source instruction adds one
entry, newest first: a newly defaulted player, or no new default. `Config.defaulted`
is derived from this record. The initial record is empty, regardless of hidden
input binding values.

Every player's view retains this public record and its actual own actions.
Retaining only the current default set would lose information. Suppose Alice
omits a binding before Bob acts in one history, but accepts an unopenable binding
and fails its opening after Bob acts in another. Alice's final failed cells and
default set can agree, while Bob previously observed different public status.
The public record keeps these histories distinguishable. It adds no observation
that a player did not already receive.

Earlier views are reconstructed by dropping the newest typed cell and public
record entry, and dropping the newest own action only when the player was active
at that instruction. No private configuration or remembered policy is needed.
The protocol recall proofs must use these projections, including automatic steps.

[ProtocolBehavioralPolicy](../Vegas/Source/ProtocolBehavioralPolicy.lean) and
[SetupProtocolBehavioral](../Vegas/Source/SetupProtocolBehavioral.lean) check exact
policy equivalence and behavioral continuation laws at every legal history.
[ObservationRecall](../Vegas/Source/ObservationRecall.lean) reconstructs earlier
views; [SetupProtocolRecall](../Vegas/Source/SetupProtocolRecall.lean) proves
perfect recall and decision recall under every commitment interface.
[InitialState](../Vegas/Source/InitialState.lean) retains the initial environment
and its joint parameter/public-result law through the full configuration readout.

## Utility and transfers

[Utility](../Vegas/Source/Utility.lean) defines the canonical `exclusionUtility`
from public default membership, including binding omission. Its public-outcome
rule agrees definitionally with `Config.utility`. For an active player, the
ordinary valuation can read all typed cells
and the complete public default history. A defaulted player receives its
declared exit utility under every continuation. The source proof gives fixed
expected utility and integrability for an already defaulted player without a
finiteness or bounded-valuation hypothesis.

Failed-reveal counts remain a diagnostic of publication cells. They are not the
control state for source utility. Count-only utility laws for arbitrary public
outcomes do not apply to the canonical rule; consumers must use public membership
or prove a reachable-outcome correspondence.

Exit utility and exit transfer remain distinct. The monetary readout must return
the declared exit transfer after default; external valuation must be included
when defining the fixed total exit utility. The ledger's count audit can still
deduct for forbidden traffic after default. These definitions and their
settlement projection require an explicit port in the strategic consumers.

No independence, service, coverage, finiteness or funding premise is added.
The preservation theorem's premises, including the exit floor, remain proof
obligations for its port. Restricting surviving players' valuations to ignore
public default history would be an additional assumption and is not part of
this design.

The ambient public-record type admits impossible histories. Utility-range ports
must use their actual execution domain or a bounded extension outside it;
boundedness on extra impossible records must not become a hidden new premise.

## Graph and ledger port

Binding decisions in the graph need the same accepted/omitted distinction;
stored binding values remain publication results. The existing `Config.step`
must normalize actions of defaulted owners and update public failure control.
Graph completion history retains every completed event, while its optional
decision distinguishes actual player choices from automatic or chance steps.
Player recall includes actual choices only.

Public omissions introduce information dependencies. If Alice's source binding
precedes Bob's, Bob may condition on Alice's default. Scheduling Bob first can
change their joint outcome law. The compiler must generate the required order;
the existing sequential dependency machinery supplies it without a scheduler
assumption. More concurrency requires a separate information-preservation proof.
Unconditional commutation of same-owner events and unconditional independence
of different owners' binding decisions are false for this semantics.

At ledger level, accepted handles implement accepted bindings, owned expiry
implements omission, and accepted failed openings implement failed resolution.
Automatic draining must use the graph's one failure step. The permanent-exclusion
controller must be consolidated into the compiled application; no second graph
evaluator or failure-mode parameter is introduced. Raw packets after default
remain network actions, with semantic rejection and count-audit treatment.

## Remaining acceptance obligations

Only checked theorems close these obligations:

1. The source protocol, whole-continuation and perfect-recall correspondence is
   checked under every commitment interface, including automatic instructions.
2. Prove source-to-graph typed-store, public-history and own-action correspondence
   for arbitrary source profiles and the compiler-generated dependencies.
3. Prove ledger inclusion, expiry and automatic draining refine finite sequences
   of those graph steps, retaining public failure provenance.
4. Reprove the bounded-client law with complete readout and the service contract.
5. Port Nash deviation translation and sequential consistency/rationality;
   equilibrium-path outcome agreement alone is insufficient.
6. Recheck intended-SE preservation only after the source and target utilities
   and transfers agree. This does not assert preservation of every full-source
   sequential equilibrium.

The ordinary full build, examples and paper guards remain acceptance gates for
replacing the maintained tower. Targeted source checks do not close them.
