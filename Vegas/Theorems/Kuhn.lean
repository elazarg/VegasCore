import Vegas.Frontier.Games

/-!
# Kuhn realization for compiled frontier games

The public statements here are phrased over checked Vegas programs and their
canonical completed frontier games.  The proof route goes through the
round-view/observation-model infrastructure, but users do not need to mention
that machinery to apply these theorems.
-/

namespace Vegas

namespace WFProgram

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Behavioral frontier profiles induce product mixed pure frontier profiles
with the same completed outcome kernel. -/
theorem behavioralFrontier_to_mixedPure_kernel
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    program.mixedPureFrontierGame.outcomeKernel
        (program.behavioralFrontierToMixedPure behavioral) =
      program.behavioralFrontierGame.outcomeKernel behavioral :=
  (program.behavioralFrontier_to_mixedPure_outcomeKernel behavioral).symm

/-- Behavioral frontier profiles induce correlated distributions over pure
frontier profiles with the same completed outcome kernel. This is the
correlated-pure Kuhn direction; the product mixed-pure direction is exposed by
`behavioralFrontier_to_mixedPure_kernel`. -/
theorem behavioralFrontier_to_correlatedPure_kernel
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    ∃ correlated : PMF program.PureFrontierProfile,
      program.behavioralFrontierGame.outcomeKernel behavioral =
        correlated.bind fun pureProfile =>
          program.pureFrontierGame.outcomeKernel pureProfile :=
  program.behavioralFrontier_to_correlatedPure behavioral

/-- Behavioral frontier profiles induce product mixed pure frontier profiles
with the same completed joint utility distribution. -/
theorem mixedPureFrontier_udist_of_behavioral
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile) :
    program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure behavioral) =
      program.behavioralFrontierGame.udist behavioral :=
  (program.behavioralFrontier_to_mixedPure_udist behavioral).symm

/-- The canonical mixed-pure-to-behavioral realization preserves completed
frontier outcome kernels. -/
theorem mixedPureFrontier_to_behavioral_kernel
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile) :
    program.behavioralFrontierGame.outcomeKernel
        (program.mixedPureToBehavioralFrontierProfile mixed) =
      program.mixedPureFrontierGame.outcomeKernel mixed :=
  program.mixedPureToBehavioralFrontierProfile_outcomeKernel mixed

/-- Strategy/deviation-level Kuhn equivalence for the canonical completed
frontier games of a checked program. This is the non-equilibrium package:
profile translations preserve completed outcome kernels, and unilateral
deviations can be matched across the mixed-pure and behavioral presentations. -/
noncomputable def frontierKuhnStrategicEquivalence_schema
    (program : WFProgram P L) [FiniteDomains program] :
    program.FrontierKuhnStrategicEquivalence :=
  program.frontierKuhnStrategicEquivalence

/-- Every unilateral behavioral deviation from the canonical behavioral
realization of a mixed-pure profile has a matching unilateral mixed-pure
deviation with the same completed outcome kernel. -/
theorem mixedPureFrontier_behavioralDeviation_to_mixedPure_kernel
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile)
    (who : P)
    (behavioralDeviation : program.BehavioralFrontierStrategy who) :
    ∃ mixedDeviation : program.MixedPureFrontierStrategy who,
      program.behavioralFrontierGame.outcomeKernel
          (Function.update
            (program.mixedPureToBehavioralFrontierProfile mixed)
            who behavioralDeviation) =
        program.mixedPureFrontierGame.outcomeKernel
          (Function.update mixed who mixedDeviation) :=
  program.mixedPureFrontier_behavioralDeviation_to_mixedPure
    mixed who behavioralDeviation

/-- Every unilateral mixed-pure deviation has a matching unilateral behavioral
deviation from the canonical behavioral realization, with the same completed
outcome kernel. -/
theorem mixedPureFrontier_mixedDeviation_to_behavioral_kernel
    (program : WFProgram P L) [FiniteDomains program]
    (mixed : program.MixedPureFrontierProfile)
    (who : P)
    (mixedDeviation : program.MixedPureFrontierStrategy who) :
    ∃ behavioralDeviation : program.BehavioralFrontierStrategy who,
      program.mixedPureFrontierGame.outcomeKernel
          (Function.update mixed who mixedDeviation) =
        program.behavioralFrontierGame.outcomeKernel
          (Function.update
            (program.mixedPureToBehavioralFrontierProfile mixed)
            who behavioralDeviation) :=
  program.mixedPureFrontier_mixedDeviation_to_behavioral
    mixed who mixedDeviation

/-- Every unilateral behavioral deviation from an arbitrary behavioral profile
has a matching unilateral mixed-pure deviation from the induced mixed-pure
profile, with the same completed outcome kernel. -/
theorem behavioralFrontier_deviation_to_mixedPure_kernel
    (program : WFProgram P L) [FiniteDomains program]
    (behavioral : program.BehavioralFrontierProfile)
    (who : P)
    (behavioralDeviation : program.BehavioralFrontierStrategy who) :
    ∃ mixedDeviation : program.MixedPureFrontierStrategy who,
      program.behavioralFrontierGame.outcomeKernel
          (Function.update behavioral who behavioralDeviation) =
        program.mixedPureFrontierGame.outcomeKernel
          (Function.update
            (program.behavioralFrontierToMixedPure behavioral)
            who mixedDeviation) :=
  program.behavioralFrontier_deviation_to_mixedPure
    behavioral who behavioralDeviation

/-- The behavioral-to-product-mixed Kuhn relation as a one-way Nash deviation
simulation. A behavioral deviation is simulated by updating the same player's
induced product mixed pure strategy. -/
noncomputable def behavioralToMixedPureFrontier_deviationSimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationSimulation
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.behavioralToMixedPureFrontierNashDeviationSimulation

/-- The canonical mixed-pure-to-behavioral Kuhn realization as a one-way Nash
deviation simulation. -/
noncomputable def mixedPureToBehavioralFrontier_deviationSimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationSimulation
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.mixedPureToBehavioralFrontierNashDeviationSimulation

/-- The canonical mixed-pure/behavioral Kuhn equivalence as a standard
two-way Nash deviation bisimulation. -/
noncomputable def mixedPureBehavioralFrontier_deviationBisimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationBisimulation
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.mixedPureBehavioralFrontierNashDeviationBisimulation

/-- If the product mixed pure frontier profile induced by a behavioral profile
is Nash, then the original behavioral frontier profile is Nash. -/
theorem behavioralFrontier_nash_of_inducedMixedPure_nash
    (program : WFProgram P L) [FiniteDomains program]
    {behavioral : program.BehavioralFrontierProfile}
    (hNash :
      program.MixedPureFrontierNash
        (program.behavioralFrontierToMixedPure behavioral)) :
    program.BehavioralFrontierNash behavioral :=
  program.behavioralFrontier_nash_of_induced_mixedPure_nash hNash

/-- The canonical mixed-pure-to-behavioral realization transports mixed-pure
Nash equilibria to behavioral Nash equilibria. -/
theorem mixedPureFrontier_nash_to_behavioral
    (program : WFProgram P L) [FiniteDomains program]
    {mixed : program.MixedPureFrontierProfile}
    (hNash : program.MixedPureFrontierNash mixed) :
    program.BehavioralFrontierNash
      (program.mixedPureToBehavioralFrontierProfile mixed) :=
  program.behavioralFrontier_nash_of_mixedPure_nash
    program.canonicalMixedPureToBehavioralFrontierDeviationSimulation hNash

/-- Complete outcome-equivalence schema for the canonical completed frontier
games. -/
theorem frontierCompleteOutcomeKuhn_schema
    (program : WFProgram P L) [FiniteDomains program] :
    GameTheory.Theorems.KuhnCompleteViaOutcome
      program.BehavioralFrontierProfile
      (∀ player, PMF (program.PureFrontierStrategy player))
      program.PureFrontierProfile
      program.pureFrontierGame.Outcome
      (fun behavioral =>
        Math.PMFProduct.pmfPi
          (program.behavioralFrontierToMixedPure behavioral))
      Math.PMFProduct.pmfPi
      program.behavioralFrontierGame.outcomeKernel
      program.pureFrontierGame.outcomeKernel :=
  program.frontierCompleteOutcomeKuhn

end WFProgram

end Vegas
