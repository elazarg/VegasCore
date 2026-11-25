module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensFairValue
public import Vegas.Game.OnePacketDistributionApproximation
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

open GameTheory.Math.Probability

/-! # The exact fair configuration and payoff law of Odds–Evens -/

noncomputable section

namespace Vegas.Examples.OddsEvens

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement

/-- The complete fair configuration and payoff law, retaining both private bits and defaults. -/
def uniformJointDistribution :
    PMF (Option (Config Player simpleExpr program.terminalCtx) × (Player → ℝ)) :=
  ((uniformLaw Bool).bind fun e =>
    (uniformLaw Bool).map (fun o => (e, o))).map fun bits =>
      (some (bitConfig bits.1 bits.2), fun who =>
        (cash (.success bits.1) (.success bits.2) who : ℝ))

theorem bitConfig_exclusion_value (e o : Bool) (who : Player) :
    exclusionReadoutUtility setup (fun _ => ()) sourceUtility (fun _ => 0)
      (some (bitConfig e o)) who = (cash (.success e) (.success o) who : ℝ) := by
  cases who <;> rfl

theorem uniform_source_joint_distribution :
    (setup.intendedModel.runBehavioral uniformProfile (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup (fun _ => ()) sourceUtility (fun _ => 0)) =
        uniformJointDistribution := by
  let joint := fun readout : Option (Config Player simpleExpr program.terminalCtx) =>
    (readout, exclusionReadoutUtility setup (fun _ => ()) sourceUtility (fun _ => 0) readout)
  have law := congrArg (PMF.map joint) (sourceDecoded_run uniformProfile)
  rw [PMF.map_comp] at law
  change (setup.intendedModel.runBehavioral uniformProfile _).map
    (joint ∘ fun final => setup.protocolReadout final.state) = _
  rw [law, PMF.map_comp, sourceDecoded_bitRun, firstBitDistribution_uniform,
    secondBitDistribution_uniform]
  simp only [uniformJointDistribution, PMF.map_bind, PMF.map_comp]
  rfl

theorem uniformJointDistribution_expected_payoff (who : Player) :
    expect uniformJointDistribution (fun realized => realized.2 who) = 100 := by
  have law : uniformJointDistribution =
      (setup.run (sourceBitProfile (uniformLaw Bool) (uniformLaw Bool))).map
        (fun terminal => (some terminal, fun actor =>
          sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) actor)) := by
    rw [sourceBitProfile_run]
    simp only [uniformJointDistribution, PMF.map_bind, PMF.map_comp]
    rfl
  rw [law, expect_map]
  exact sourceBitProfile_uniform_value (uniformLaw Bool) who

end Vegas.Examples.OddsEvens
