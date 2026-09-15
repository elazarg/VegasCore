# Cross-site logical commitment experiment

This bounded experiment asks whether the useful part of a native candidate
execution can retain authenticated information from another binding while
forgetting lower-level execution detail. It is an independent test of a
possible intermediate boundary, not a compiler theorem.

## Native fixture

The candidate program contains two commitment/reveal pairs. The focal owner
prepares a Boolean value, submits its commitment, and later chooses an opening
or withholds. A fixed second-binding policy independently prepares its own
Boolean value, submits its commitment for inclusion by the environment, and submits an
authenticated opening for its selected handle. The fixed environment delivers
that opening to the focal owner and may include it before the focal decision.

The experiment uses the existing `MessageApplication.runPolicies` runner. The
other-binding policy, environment and invocation schedule are fixed before the
two focal decision kernels are quantified. Both binding wrappers reconstruct
their later payloads from their own actual private-command histories; neither
receives the private candidate catalog.

The checked direct factorization has the following order:

```text
focal first choice
  -> fixed other-binding choice and authenticated disclosure
  -> focal second choice from actual owner view and recalled first choice
  -> fixed inclusion and clock continuation
```

The retained result consists of the public event prefix strictly before focal
settlement, the focal published value, and focal-site timeout attribution. In
this fixture the prefix can be recovered from the terminal append-only event
log because the first focal reveal event is produced by the focal opening or
its timeout, with no public event inserted between the opening decision and
that first focal settlement event. Later events are outside the recovered
prefix. That recovery is a property of this fixed suffix, not
a general equivalence between terminal and decision-time prefixes.

## Checked boundary

`runPolicies_crossSite_stoppedOutcome` establishes the exact result law from
the actual runner for arbitrary focal first and second kernels. The other
value law, other-binding policy, environment and schedule are parameters fixed
independently of both focal kernels. Thus the theorem establishes an
action-total factorization for this finite interface under unchanged
surrounding policies. In particular, it tests facts not covered by the
single-binding experiment:

- the cross-site claim is an authenticated opening generated from another
  actual selected candidate;
- the focal policy sees the site-tagged claim through the actual shared native
  message view;
- pending versus publicly included disclosure remains distinguishable; and
- the result retains joint public history rather than only terminal
  publication.

`runPolicies_crossSite_logical_law` then applies the generic two-decision
conditioning theorem. Its logical observation consists of public application
events and delivered payloads with envelope identifiers removed. The second
logical policy also recalls the focal first choice. It receives neither the
full native view nor the auxiliary metadata used to randomize focal policies.
An authenticated inclusion appends the other site's opening to public events;
an opening still pending appears only in the inbox. The quotient therefore
retains the distinction between these cases.

The logical transition to that observation is independent of the focal
prepared value; the checked hiding lemma supplies this equality for every
first action. The final continuation uses only the retained public prefix and
whether the response matches the recalled preparation. The other-binding law,
environment and logical continuation kernels remain fixed across both
arbitrary focal kernels. The resulting equality preserves the joint prefix and
settlement law, not just its terminal marginal.

## Limits

The second-binding wrapper is a fixed honest-protocol-shaped policy, but it is
not proved to be the compilation of a source policy. The environment is a
bounded scripted service whose inclusion mode is a fixed parameter. The
fixture does not cover an arbitrary wire policy that can inspect packet
identifiers, receipts, multiplicities, or deadline phase. Success therefore
shows sufficiency only for this common kernel, not for every candidate-runtime
environment.

The independent `InteractionTests/LogicalCommitmentAdaptive.lean` test makes
one limit concrete: an unchanged wire can use rejected cleartext traffic to
choose between delivery and immediate inclusion of an honest opening. Erasing
that traffic from the command prefix prevents one common next-publication
kernel from covering both tag policies, although both runs complete. This
constrains that trace erasure; it does not exclude a richer logical history
or an outcome-only strategic simulation.

The theorem does not assume or prove deadline-relative service. Withholding
or a mismatched focal opening resolves by the actual clock; the other opening
can also remain pending until timeout. These cases test the logical law, not
protection of honest progress.

The recorded prefix is the public state at the focal owner's later opening
decision. It is not automatically the source incentive comparison prefix.
`candidateGraphCoupling_timeout_public_prefix` concerns the commitment
producer's earlier public declared reads, including their graph-indexed
projection, even when settlement later occurs at a reveal. The fixture's
commitment rules have no nontrivial read dependencies, so it does not test
reconstruction of that producer prefix. The two prefixes must not be
identified without a separate theorem.

The experiment also does not prove a graph-wide state relation, adaptive
service simulation, arbitrary `PlayerPolicy` replacement, or composition of
shared candidate catalogs across an unbounded collection of sites. Failure of
a per-binding quotient would identify missing retained information; it would
not prove a strategic impossibility for the native runtime.

## Adoption criterion

Adoption requires a graph-wide stopped-prefix factorization under one fixed
admitted environment and unchanged opponents. The relation must retain all
cross-site facts jointly visible to the focal player, derive its action-total
continuation kernels from native execution, and reconstruct the producer's
graph-indexed declared-read prefix used by
`candidateGraphCoupling_timeout_public_prefix`.

The intermediate layer is worthwhile only if that theorem replaces a named
part of `candidateGraphRun_native_prefix_law` and simplifies the existing
timeout-prefix proof without reintroducing the full native history as an
unconstrained logical signal. This bounded fixture alone does not justify
connecting the logical protocol to the active compiler.
