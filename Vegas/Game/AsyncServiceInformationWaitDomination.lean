/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceInformationWait
import Vegas.Game.AsyncServiceInitializedDomination

/-! # Initialized loss for information-dependent native waiting

The actual supported first-turn choice law supplies the uniform lower factor.
The existing initialized finite-step kernel then bounds the complete history
law, independently of all free continuation behavior. This is an unconditional
bound; conditioning on rare information requires further likelihood estimates.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound)
  (initialLaw service.setup) service.horizon service.scheduler

/-- The same initialized first-turn history law is within the finite loss
bound for every information-dependent waiting family with this maximum rate.
Neither source posterior transport nor conditional rationality follows. -/
theorem completedInformationWaitProfile_initialized_close
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ who info, 0 ≤ weight who info)
    (small : ∀ who info, weight who info ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (boundSmall : bound ≤ 1)
    (bounded : ∀ who info, service.sourceCompatibleInfo who info → weight who info ≤ bound)
    (fuel : Nat) :
    PMF.WithinTV (1 - ((1 - delta) * (1 - bound)) ^ (Fintype.card Player * fuel))
      ((model).runBehavioral (service.firstTurnProfile service.horizon profile) fuel)
      ((model).runBehavioral (service.completedInformationWaitProfile profile weight nonnegative
        small delta deltaNonnegative deltaSmall continuation) fuel) := by
  apply service.firstTurnProfile_initialized_close_of_choice profile
    (service.completedInformationWaitProfile profile weight nonnegative small delta
      deltaNonnegative deltaSmall continuation) ((1 - delta) * (1 - bound))
  · exact mul_nonneg (sub_nonneg.mpr deltaSmall) (sub_nonneg.mpr boundSmall)
  · calc
      _ ≤ 1 * (1 - bound) :=
        mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr boundSmall)
      _ ≤ 1 := by linarith
  · intro elapsed history reached who choice
    exact service.completedInformationWaitProfile_firstTurn_choice_lower profile permitted
      effective weight nonnegative small delta deltaNonnegative deltaSmall continuation bound
        boundNonnegative boundSmall bounded elapsed history reached who choice

end Vegas.AsyncServiceSpec
