import Vegas.Examples.NullableCommit

/-!
# Nullable Compilation Theorem Targets

This file records the nullable-compilation theorem targets as comments only.
They should become declarations once the compiler from
non-nullable source programs to nullable backend-safe programs is defined.
-/

namespace Vegas

/- TODO:
theorem nullableCompile_preserves_honest_subgame ...

Replacing source actions by nullable backend actions preserves the original
game on all-honest profiles.
-/

/- TODO:
theorem nullableCompile_none_strictly_dominated ...

Synthesized nullable abort moves are strictly dominated under the compiler's
penalty scheme.
-/

/- TODO:
theorem nullableCompile_equilibria_are_honest ...

Equilibrium/rationalizable behavior in the nullable game is honest: abort
moves have no strategic role after compilation.
-/

/- TODO:
theorem nullableCompile_no_honest_disadvantage ...

Backend abortability introduced by nullable compilation does not make honest
source players worse off.
-/

end Vegas
