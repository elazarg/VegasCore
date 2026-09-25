# Sequential enforcement: extension and reflection

The implementation objective is forward preservation: extend each source
sequential equilibrium to a target sequential equilibrium with the same
retained outcome law. This is different from requiring every target sequential
equilibrium to reflect to the source.

## A reflection obstruction

The following finite example has been checked mathematically but has **not
been formalized in Lean**.

In the source, Alice chooses `Out` or `In`. `Out` ends the game with payoff
`(1, 0)`. After `In`, Bob chooses `L`, giving `(2, 1)`, or `R`, giving `(0, 0)`.
The source's sequential equilibrium chooses `In` and `L`.

The target adds Alice's forbidden action `Bad`. Bob cannot distinguish `Bad`
from `In`. After `Bad`, Bob's payoffs from `L` and `R` are respectively zero and
one; Alice receives minus 100 either way. Thus `Bad` is strictly dominated by
`Out`, regardless of Bob's continuation.

Nevertheless, `Out/R` is a target sequential equilibrium. In a common fully
mixed sequence, assign Alice probability `epsilon` to `Bad`, probability
`epsilon^2` to `In`, and the remainder to `Out`; let Bob's probability of `R`
approach one. At Bob's information set the posterior probability of `Bad` is
`1/(1+epsilon)`, approaching one. Bob therefore prefers `R` in the limit, and
Alice prefers `Out` to both alternatives. Its retained source behavior
`Out/R` is not sequentially rational in the source.

The example concerns off-path beliefs, not inadequate penalty size. A public
signal distinguishing the punished branch before Bob acts removes this
particular merged information set. A delayed or hidden sanction need not do so.
It does not refute forward preservation: the source equilibrium `In/L` has a
target extension supported by making `Bad` trembles sufficiently rarer than
`In` trembles.

## General forward proof route

A finite game obtained by adding forbidden actions to a genuine source action
restriction should admit a forward extension theorem under perfect recall and
uniform domination of the gain from a first violation. This general theorem is
**not yet checked**. Its intended proof pins a source consistency sequence at
old information sets, makes forbidden actions asymptotically rarer than every
positive source-history reach probability, and completes behavior at new-only
information sets by finite perturbed-game equilibria. Compactness then preserves
the original beliefs at old sites while permitting optimal continuations after
a disclosure. Perfect recall is needed for the passage from local optimality
to whole continuation-policy optimality.

The [checked implementation](../GameTheoryExtensions/Analysis/Protocol/DisclosureEnforcementEquilibrium.lean)
is the finite sender/receiver decision class,
where the completion is explicit: retain the receiver's source decision law
after silence and select a receiver best response after authenticated
disclosure. A common type-independent disclosure tremble retains the original
prior on silence. State-dependent charges can deter the sender whenever they
cover its conditional gain from disclosure. This class does not establish the
full native compiler theorem or implement detection by a watchdog.

Dilmé's [Sequentially Stable Outcomes](https://doi.org/10.3982/ECTA21402),
Sections 2.4 and 4.1, gives a useful primary reference for perturbation-based
reasoning and the distinction between ordinary sequential outcomes and
refinements that survive dominated-action elimination. Its sequential stability
results should not be cited as an ordinary sequential-equilibrium extension
theorem.
