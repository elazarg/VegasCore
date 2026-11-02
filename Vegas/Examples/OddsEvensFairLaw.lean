/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensFairValue
import Vegas.Game.OnePacketLawApproximation

/-! # The exact fair configuration and payoff law of Odds–Evens -/

noncomputable section

namespace Vegas.Examples.OddsEvens

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement

/-- The complete fair configuration and payoff law, retaining both private bits and defaults. -/
def uniformJointLaw : PMF (Option (Config Player simpleExpr program.terminalCtx) × (Player → ℝ)) :=
  ((PMF.uniformOfFintype Bool).bind fun e =>
    (PMF.uniformOfFintype Bool).map (fun o => (e, o))).map fun bits =>
      (some (bitConfig bits.1 bits.2), fun who =>
        (cash (.success bits.1) (.success bits.2) who : ℝ))

theorem bitConfig_exclusion_value (e o : Bool) (who : Player) :
    exclusionReadoutUtility setup (fun _ => ()) sourceUtility (fun _ => 0)
      (some (bitConfig e o)) who = (cash (.success e) (.success o) who : ℝ) := by
  cases who <;> rfl

theorem uniform_source_joint_law :
    (setup.intendedModel.runBehavioral uniformProfile (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup (fun _ => ()) sourceUtility (fun _ => 0)) =
        uniformJointLaw := by
  let joint := fun readout : Option (Config Player simpleExpr program.terminalCtx) =>
    (readout, exclusionReadoutUtility setup (fun _ => ()) sourceUtility (fun _ => 0) readout)
  have law := congrArg (PMF.map joint) (sourceDecoded_run uniformProfile)
  rw [PMF.map_comp] at law
  change (setup.intendedModel.runBehavioral uniformProfile _).map
    (joint ∘ fun final => setup.protocolReadout final.state) = _
  rw [law, PMF.map_comp, sourceDecoded_bitRun, firstBitLaw_uniform, secondBitLaw_uniform]
  simp only [uniformJointLaw, PMF.map_bind, PMF.map_comp]
  rfl

theorem uniformJointLaw_expected (who : Player) :
    expect uniformJointLaw (fun realized => realized.2 who) = 100 := by
  have law : uniformJointLaw =
      (setup.run (sourceBitProfile (PMF.uniformOfFintype Bool) (PMF.uniformOfFintype Bool))).map
        (fun terminal => (some terminal, fun actor =>
          sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) actor)) := by
    rw [sourceBitProfile_run]
    simp only [uniformJointLaw, PMF.map_bind, PMF.map_comp]
    rfl
  rw [law, expect_map]
  exact sourceBitProfile_uniform_value (PMF.uniformOfFintype Bool) who

end Vegas.Examples.OddsEvens
