# Primary sources and what they do not establish

These references help formulate the research questions. None proves that a
particular deployed ledger implements the interfaces in this directory.

## Cryptographic representations of abstract games

Halpern, Pass and Seeman formulate representation of a finite extensive-form
game by computational games. Their conditions include history structure,
payoffs and simulation of efficient unilateral deviations. They prove
preservation into their computational Nash and sequential-equilibrium notions.
This separates cryptographic implementation from abstract strategic analysis;
our extra transport decisions and their observations still need adapters.
[Computational Extensive-Form Games](https://arxiv.org/abs/1506.03030).

The [preservation track](preservation-and-robustness.md) distinguishes their
computational definition from ordinary finite-game sequential equilibrium
under ideal primitives. The theorem should not be cited as if encryption alone
established our physical runtime's rationality preservation.

## Network timing and consensus

Dwork, Lynch and Stockmeyer distinguish known synchronous message bounds from
partial synchrony, including known bounds that hold only after an unknown
stabilization time. This matters when a source decision has a physical deadline:
eventual communication bounds do not themselves give a predetermined completion
deadline for a particular transaction.
[Consensus in the Presence of Partial Synchrony](https://groups.csail.mit.edu/tds/papers/Lynch/MIT-LCS-TM-270.pdf).

The inference about a transaction deadline is ours; the cited paper supplies
the network and consensus definitions. Transaction selection, fee competition,
admission capacity and decryption availability are further assumptions.

## Sequential rationality

Kreps and Wilson introduce sequential equilibrium for extensive-form games,
including optimal continuation decisions and consistent beliefs at off-path
information sets. This motivates keeping conditional incentives and a common
belief-consistency construction separate from initialized outcome matching.
[Sequential Equilibria](https://www.jstor.org/stable/1912767).

## How to add further sources

Use papers, official protocol specifications or implementation documentation.
Record the precise property supported: cryptographic confidentiality, finality,
admission, release, observation or availability. Distinguish transaction
proposal from final admission, and disclosure authorization from receipt of
plaintext. An implementation example is evidence for a component, not a proof
of the combined game interface.

Hardware confidentiality, committee honesty and availability, and computational
cryptographic security must be named separately. Idealizing one assumption
does not idealize the rest. The present round makes no new deployment claim.
