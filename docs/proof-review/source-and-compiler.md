# Source, compiler and review tooling

The source/compiler declaration surfaces cover 274 modules and 45,304 physical
lines using the common inventory grouping. Examples, VegasTests and Paper surfaces were
also screened. Deep reads focused on compiled suffix laws and backtranslation,
source recovery step support, control/potential proofs, clear projection, owned
history, commitment observation congruence, and the reveal branches of the two
repair inductions. Selected observation-codec and executable-auction bodies were
read. This is not a claim of reading every tactic in these modules.

The production Lean baseline is `ec4de15c`. The review changes no source,
compiler or runtime semantics, theorem, dependency or SE checklist. The one
implemented change is a tested correction to the Python review scanner.

## 1. Six compiler proofs can use the existing tail-order lemma

`ContextRefsBefore.tail_cons` in
[EventGraphCompiler](../../Vegas/Compile/EventGraphCompiler.lean#L511) already
proves that a newly produced head reference and all prior references precede
all outputs of the residual embedding. Its full hypotheses include the actual
source tail, event-count equality, output-layout correspondence, and equality
of the head field to the original head event.

Six current consumers still reproduce this proof by splitting HasVar, proving
head-before-tail from strictMono, and forwarding old references:

- [EventGraphLaw](../../Vegas/Compile/EventGraphLaw.lean#L147): sample, commitment
  and reveal branches at lines 147, 250 and 368.
- [EventGraphPolicyAlignment](../../Vegas/Compile/EventGraphPolicyAlignment.lean#L108):
  sample, commitment and reveal tailRefsBefore at lines 108, 209 and 317.

All six have exactly the existing lemma's premises. The head-field equality is
reflexive for the actual reference, including the dependent publication cast.
Each replacement uses `refsBefore.tail_cons next ... _ rfl`; no new generic
API, simulation certificate, source assumption or compatibility wrapper is
needed. The legal policy normalization, decoded history and partial readout
proofs stay in their existing consumers.

**Checked evidence:** complete copies of both actual consumer proof modules
compile with the six replacements and the central strict options. They retain
all original declaration statements. EventGraphLaw goes from 386 to 362 lines;
EventGraphPolicyAlignment goes from 391 to 373. This is **42 fewer physical
lines across the full two-module family**, with no added common API or imports.
The candidates are not applied to production.

Reproduce the complete checks after the ordinary build:

```powershell
python scripts/experiments/compiler_tail_order_probe.py
```

The experiment reads the real two source files, checks all three sites in each,
and compiles the transformed full modules in a temporary directory. It does not
edit project source or create a different game model. Confidence is high; the
remaining implementation work is six substitutions and the normal owning/full
builds.

## 2. Move the actual recovery-step eliminator to its lower owning layer

The useful exact eliminator already exists:
[CommitRecoveryState.step_raw_result](../../Vegas/Source/CommitRecoveryAttemptReset.lean#L196).
It returns the actual raw result in the recoveryStep support, its real exclusion
monotonicity witness, and the exact target `(state.install ...).close`.
It is stronger and more useful than unpacking the outer PMF map and separately
recovering raw support via map_val_pmfToSubtype.

Its current owner is too high. AttemptReset imports control/frontier/history
results that already need the same primitive. The declaration itself depends
only on [CommitRecoveryState](../../Vegas/Source/CommitRecoveryState.lean#L140),
so it belongs directly after step, before the potential proof. Moving this
existing declaration preserves its name and mathematics; no forwarding module,
new record or general invariant framework is needed.

Four complete actual consumer proofs are checked with the existing eliminator:

| Actual declaration | Owner | Physical proof lines |
| --- | --- | ---: |
| step_control_lt | [CommitRecoveryControl](../../Vegas/Source/CommitRecoveryControl.lean#L25) | 42 to 35 |
| step_potential_lt | [CommitRecoveryState](../../Vegas/Source/CommitRecoveryState.lean#L186) | 45 to 38 |
| clear_step_source | [CommitRecoveryProjection](../../Vegas/Source/CommitRecoveryProjection.lean#L43) | 26 to 19 |
| step_own_history | [CommitRecoveryOwnHistory](../../Vegas/Source/CommitRecoveryOwnHistory.lean#L166) | 21 to 14 |

**Checked evidence:** the exact helper elaborates with only the proposed lower
imports. The four proofs elaborate against the actual current source-state
model; no new state, desired successor law, rank hypothesis or Fintype premise
is introduced. The potential proof retains Fintype Player, while the control
and projection statements retain their existing broader scope. Every retry,
exhausted block, preserved original history and actual closure result remains.

These four ports remove **28 physical lines**. Moving the existing 13-line
helper has zero mathematical API growth. Further raw-support reconstruction
occurs in CommitBlockRecovery, CommitRecoveryCommitUnique, Cursor, Debt,
FailureCoverage, Frontier, PublicRanks, SavedObservation and
ProposalRecoverySuccessfulTrace. Those additional ports need individual checks;
their line savings are not included in 28. Some map/subtype uses serve different
purposes, such as finite-support images or reverse construction, and should not
be replaced mechanically.

The checked lower helper and four consumer proofs are retained in the
[probe appendix](checked-probes.md). Production relocation and all caller ports
remain proposed. Confidence is high for the four checked consumers.

## 3. Correct the scanner before interpreting proof-size leads

The review found a concrete measurement bug. A theorem can have a result type
containing `let common := ...`, `let certificate := ...` and `let payoff := ...`
before its actual proof assignment. The scanner treated the first such binding
as the proof start. The prominent eight-file Recovery comparison match was
mostly shared result-type scaffolding, not eight repeated proof bodies.

The shared scanner in [lean-defs.py](../../lean-defs.py#L173) now skips value
assignments belonging to result-type let/have bindings, including nested
bindings, named arguments, comments, strings and quoted identifiers. Four
regression tests exercise both inventory bodies and preserved declaration
surfaces. All 98 Python tests pass. This changes tooling only.

The corrected scan finds 3,705 cross-file eight-line candidate windows at this
production baseline. It remains lexical: equation-style declarations do not
have complete body coverage, and some previously counted equation fragments
are no longer reported. These counts are not an AST proof census and must not
be compared with the old scanner's body totals as evidence of compression.
Physical module sizes and the manually delimited complete consumer proofs
above are the exact size measurements used here.

## Leads excluded from the savings claims

The large binding-replay/preparation-repair pair still shares reveal plumbing.
Its current legal action update already uses the extracted IsLegalJoint.update
kernel. The remaining branches build different repaired configurations and
source relations, retain foreign actions and omission markers, and prove
concrete disclosure/history identities. The previous broad menu helper had
no measured advantage. This review does not relist the same large window count
as a new compression result without a new complete adapter pilot.

A common compiler simulation record would need actual probability, visibility,
readout and policy-normalization adapters. Their cost is unmeasured. The six
checked factual tail-order substitutions provide a smaller verified route.

The executable auction still evaluates the real transfer expressions and keeps
valuation separate from cash. Its withholding counterexample and complete
compiled-deviation scope are retained; no new truthfulness claim follows from
these proof-engineering opportunities.
