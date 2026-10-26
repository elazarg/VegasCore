# Payoff-aligned source completion

[SourceTerminalReadout](../Vegas/Game/SourceTerminalReadout.lean) proves that the
actual source Config and typed readout freeze after source completion, under
every legal continuation profile. Consequently the complete terminal readout
law equals its law stopped at that actual completion time.

[SourceTerminalComparison](../Vegas/Game/SourceTerminalComparison.lean) applies
the existing stopped honest-response comparison at this cutoff. The error
budget counts honest responses only until source completion. The result keeps
the joint typed readout and the original exclusion-payoff vector, with bounded
readout-payoff corollaries. The initialized one-packet theorem follows with
its exact statement, original service premises and zero-player case retained.
It uses the original assessment sequence and selected law.

[SourceTerminalIndifference](../Vegas/Game/SourceTerminalIndifference.lean)
derives completion throughout the actual information fiber from the current
public completion view. For every hidden history all continuation profiles
have the same original readout payoff. The signed residual is therefore zero for every continuation profile.
With finite actual histories, the conditional whole-policy gain is zero for
every belief and every deviation.
This uses exact cancellation before taking absolute values.

[SourceTerminalCallbacks](../VegasTests/SourceTerminalCallbacks.lean) constructs
a genuine initialized bounded-raw commit/reveal prefix and an additional
callback after source completion. At that history the completion-stopped
response budget is zero while the full-horizon budget is at least one for
every continuation profile. Its scheduler mixture exhibits the prefix only;
no physical-service or equilibrium certificate is claimed for that scheduler.

The [native prefix owner](../Vegas/Examples/ProgramPaymentsNativeRepresentation.lean)
also proves a useful obstruction to a literal Config-only runtime projection:
reachable second callbacks can share Config and differ in public accepted
handles and actual player observations, and the same admitted opening succeeds in one and fails in the other.
This does not rule out richer finite encodings or coherent handle renamings.
The compiled observable-space prototype is retained separately on
[its experiment branch](https://github.com/elazarg/VegasCore/blob/research/vegas-observable-representation/docs/experiments/program-payments-observable-representation.md).

Generic opposite-sign cancellation across live residuals is rejected as a
production refinement. Arbitrary payoffs and foreign failures provide no sign
relation. Source completion also need not freeze audited charges, receipts or
full histories. The accepted equality concerns the same original readout
payoff; it does not replace the phase preservation error by zero or strengthen
an SE theorem without its existing assumptions.

Normal owner builds and the actual strict-budget regression pass. The paper
audit pins the readout law, original joint-payoff bound, bounded-payoff bound,
signed residual, whole-policy gain, two native obstructions and budget witness.
