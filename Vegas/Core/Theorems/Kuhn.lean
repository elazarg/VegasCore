import Vegas.Core.ToEventGraph.Games

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

/-- The behavioral-to-product-mixed Kuhn relation as a one-way Nash deviation
simulation. A behavioral deviation is simulated by updating the same player's
induced product mixed pure strategy. -/
noncomputable def behavioralToMixedPureFrontier_deviationSimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationSimulation
      program.mixedPureFrontierGame program.behavioralFrontierGame
      program.mixedPureFrontierGame.Outcome :=
  program.behavioralToMixedPureFrontierNashDeviationSimulation

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
