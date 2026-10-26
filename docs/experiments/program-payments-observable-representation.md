# Payment-program finite observable representation

Decision: retain this checked experiment on research/vegas-observable-representation;
reject adoption of its compiled representation as a production native-runtime
compression layer.

[FiniteRuntime](../../Vegas/Examples/ProgramPaymentsFiniteRuntime.lean) checks the
actual two-decision compiled payment program against a ten-state carrier,
including every failed binding and withheld disclosure. It proves exact
transition rows, reachability, actual private observations, both directions of
legal state-local policy representation, arbitrary-scheduler execution laws,
and the joint publication, executable payment and original utility readout.
This is 352 lines of Lean; it fixes the bonus at two, with arbitrary PMF action
coefficients. It is not the network-runtime semantics.

[ObservableCertificate](../../Vegas/Examples/ProgramPaymentsObservableCertificate.lean)
adds 216 lines. Terminal operator rows are zero: the stopped system generates
no observations after halt. The exact orbit span has dimension seven over ten
states. Its independent columns and closure under every actual observation/action
label are checked in Lean, and the existing word consumer is instantiated.
The [exact search](../../scripts/experiments/program_payment_observables.py) is
untrusted; run it from the repository root. Its result is independently checked
by the Lean certificate.

All four live callback states remain distinct. The three saved dimensions merge
only terminal failure histories. Thus 568 lines buy no live decision compression,
and do not discharge native private-recall, accepted-handle or raw-action
transport. A separate actual reachable-prefix test demonstrates why the literal
Config-only native lift fails: the same Config can have different owner handle
observations, and the same raw opening can succeed in one and be rejected in
the other. This rules out that proposed decoder/action factorization, without
ruling out richer finite encodings or handle renamings.

The rejection concerns integration cost and absence of a useful native consumer,
not correctness of the finite certificate or the weighted-automata method.
A subsequent pilot should identify a nonterminal payoff-preserving symmetry,
or an encoding already required by the executor, before building another
private-recall and identity adapter. No native matrix or native dimension is
claimed; no preservation premise or payoff semantics is weakened.

Verification: both owners passed an exact-source strict check with the central
Lean options. Normal build passed for both owners (4053 jobs in the combined owner check).
All five audited roots use only propext, Classical.choice and Quot.sound.
The exact search returns 10 states, 60 labels, 24 nonzero labels and dimension 7.
The independently useful native obstruction/prefix is included on this branch
and is eligible for separate integration with its production regression.
