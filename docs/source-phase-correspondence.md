# Source phase correspondence and Nash transport

The source game is `Vegas.SourceProgram.Setup.sourcePhaseGame`: the existing
source exit/retry protocol, with declared integer cash and a separate history
valuation. The physical target uses `phaseApplication` with the same maximal
commitment blocks. Singleton sequential phases are a distinct partition; their
after-failure behavior cannot be identified with that source kernel.

The target Nash port must compile each player's policy independently, preserve
the initialized joint observation/cash law for every source profile, and cover
every native unilateral deviation against the compiled opponents. Reflection
must retain every source unilateral deviation. Neither a legal source endpoint
nor an intended-only equilibrium theorem supplies these policy-law obligations.

## Checked endpoint correspondence

[SourcePhaseOperational](../Vegas/Game/SourcePhaseOperational.lean) derives the
source counterpart from the actual initialized physical trace. For every
execution mode, maximal phase plan, scheduler and pending-observation rule, an
actual completed raw prefix yields a legal terminal source history with:

- the same actual excluded set;
- the same complete typed terminal readout;
- the same entire declared integer cash vector;
- retained source recall, public chronology and archived source origins.

The counted variant retains the full consumed proposal archive and uses the
physical completion contract to derive native completion at protocol-terminal
prefixes. The caller supplies no source history or simulation witness.
These are pointwise results; the extracted history is not asserted to follow
one source policy or to have the source evaluator's probability law.

## Source payoff recoding

[SourcePhaseObservation](../Vegas/Game/SourcePhaseObservation.lean) reads the
same `TerminalObservation` from the full source game. Its Nash equivalence
retains every source policy, every source unilateral deviation and the exact
same error. Valuation must factor through that observation on completed source
paths. No finite prior, finite menus or new integrability premise is needed;
the original expectation guards are retained. This is a source outcome
recoding, not the native strategy port.

The factorization is substantive.
[SourcePhaseValuation](../Vegas/Examples/SourcePhaseValuation.lean) constructs
two legal initialized terminal histories with an initially unusable binding.
Withholding and attempting its publication give identical terminal state,
exclusions and cash, but retain different original own actions. A valuation
of that action gives different utilities, so no reader of the common terminal
observation can represent every full-history valuation.

## Checked interface distinctions

[SourcePhasePartition](../Vegas/Examples/SourcePhasePartition.lean) uses a real
two-owner program and initialized source and physical traces. Source omission
inside its maximal block retains that block's checkpoint and later retries a
surviving owner, retaining its voided action. The singleton runtime advances
the failed slot without that retry. Phase addresses, retry generations and own
recall differ. Both displayed readouts are unfinished; the result does not
assert terminal-law or Nash impossibility.

[SourcePhaseInformation](../Vegas/Examples/SourcePhaseInformation.lean) checks
an immediate-callback decoder failure on the concurrent maximal graph. A later
source owner sees an earlier owner's omission, whereas a native scheduler can
activate that later owner before the earlier owner acts. The paired source
information values differ and the paired native callback inputs agree. No
decoder maps those particular families as proposed. The witness scheduler is
not claimed to satisfy a complete physical service contract, and the theorem
does not rule out clients that wait or a unilateral-deviation simulation.

## Remaining strategy obligations

The first positive policy target uses the sequential graph with maximal phase
blocks: sequential readiness orders source decisions while maximal blocks keep
the same rollback and retry rule. The existing singleton SE theorems retain
their own partitions and statements.

The required construction is an actual source cursor at ready callbacks,
followed by reconstruction of complete surviving-player source information
from physical own recall and current observation. First-opportunity clients
must record silence as well as submissions at each attempt/event, so an
omission is sampled once. After a player exits, future source instructions are
automatic; erased failed-disclosure intentions still require the explicit
payoff factorization above.

Initialized law transport and arbitrary native deviation simulation remain
unproved. Existing `GameForm.UtilitySimulation` and
`GameForm.isεNash_of_deviation_bounds` own the Nash algebra; introducing a
certificate that merely assumes these missing facts would not prove the port.
The retained plain-contract Nash results therefore remain available.
