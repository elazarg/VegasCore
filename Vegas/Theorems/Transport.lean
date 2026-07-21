import Vegas.Frontier.Transport

/-!
# Frontier game transport facts

The canonical pure-to-behavioral embedding preserves expected utility on the
completed checked-program frontier games.
-/

namespace Vegas

open GameTheory

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- The canonical pure-to-behavioral frontier embedding preserves expected
utility for every profile and player. -/
theorem pureToBehavioralFrontierMorphism_eu
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) (player : P) :
    program.behavioralFrontierGame.eu
        (fun who =>
          program.pureFrontierStrategyToBehavioral who (profile who))
        player =
      program.pureFrontierGame.eu profile player :=
  program.pureToBehavioralFrontierMorphism.eu_preserved profile player

end WFProgram

end Vegas
