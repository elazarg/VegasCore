/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingReach
import Vegas.Pending.PhaseBindingEnvironmentMass

/-! # Counterfactual reach extensions along actual repaired native histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}

local notation "app" => phaseApplication runtime leaks

variable (menu : ReactiveApplication.ResponseMenu (phaseApplication runtime leaks))
  (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
  (scheduler : ReactiveApplication.Scheduler (phaseApplication runtime leaks))

local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

/-- Actual scheduler boundaries have no behavioral multiplier. Their full
counterfactual step masses follow from the derived command atom equality. -/
theorem counterfactual_environment_step {original repaired after image : (app).Execution}
    (frame : Frame runtime leaks memory owner original repaired)
    (afterFrame : Frame runtime leaks memory owner after image)
    (remaining : Nat) (chosen : (app).Command)
    (leftTrace : (E).Trace (some ⟨remaining + 1, none, original⟩))
    (rightTrace : (E).Trace (some ⟨remaining + 1, none, repaired⟩))
    (firstJoint secondJoint : Player → Option (app).Action)
    (firstLegal : (E).Legal (some ⟨remaining + 1, none, original⟩) firstJoint)
    (secondLegal : (E).Legal (some ⟨remaining + 1, none, repaired⟩) secondJoint)
    (leftMoved : after ∈ (original.environmentStep (app) chosen).support)
    (rightMoved : image ∈ (repaired.environmentStep (app) chosen).support)
    (strategy : ∀ player, (N).BehavioralPolicy player) :
    (N).counterfactualStepProb strategy owner leftTrace ⟨firstJoint, firstLegal⟩
        (some ⟨remaining, chosen.actor? (app), after⟩) =
      (N).counterfactualStepProb strategy owner rightTrace ⟨secondJoint, secondLegal⟩
        (some ⟨remaining, chosen.actor? (app), image⟩) := by
  rw [environment_counterfactualStepProb runtime leaks menu initial horizon scheduler,
    environment_counterfactualStepProb runtime leaks menu initial horizon scheduler,
    frame.environment_transition_apply afterFrame initial horizon scheduler remaining chosen
      leftMoved rightMoved firstJoint secondJoint]

/-- The induction invariant extends at a genuine scheduler step using the
same actual command and its two real supported outcomes. -/
theorem counterfactual_environment_extend {original repaired after image : (app).Execution}
    (frame : Frame runtime leaks memory owner original repaired)
    (afterFrame : Frame runtime leaks memory owner after image)
    (remaining : Nat) (chosen : (app).Command)
    (leftTrace : (E).Trace (some ⟨remaining + 1, none, original⟩))
    (rightTrace : (E).Trace (some ⟨remaining + 1, none, repaired⟩))
    (firstJoint secondJoint : Player → Option (app).Action)
    (firstLegal : (E).Legal (some ⟨remaining + 1, none, original⟩) firstJoint)
    (secondLegal : (E).Legal (some ⟨remaining + 1, none, repaired⟩) secondJoint)
    (leftMoved : after ∈ (original.environmentStep (app) chosen).support)
    (rightMoved : image ∈ (repaired.environmentStep (app) chosen).support)
    (firstRealized : some ⟨remaining, chosen.actor? (app), after⟩ ∈
      ((E).step _ ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : some ⟨remaining, chosen.actor? (app), image⟩ ∈
      ((E).step _ ⟨secondJoint, secondLegal⟩).support)
    (strategy : ∀ player, (N).BehavioralPolicy player)
    (prior : (N).counterfactualReachProbability strategy owner leftTrace =
      (N).counterfactualReachProbability strategy owner rightTrace) :
    (N).counterfactualReachProbability strategy owner
        (leftTrace.extend firstJoint firstLegal firstRealized) =
      (N).counterfactualReachProbability strategy owner
        (rightTrace.extend secondJoint secondLegal secondRealized) := by
  rw [InformationModel.counterfactualReachProbability,
    InformationModel.counterfactualReachProbability, prior,
    frame.counterfactual_environment_step runtime leaks menu initial horizon scheduler afterFrame
      remaining chosen leftTrace rightTrace firstJoint secondJoint firstLegal secondLegal leftMoved
        rightMoved strategy]

/-- Actual paired response steps extend the accumulated counterfactual equality.
The raw off-owner actions are structural response witnesses, not likelihood
premises; the transition itself is the real deterministic native response. -/
theorem counterfactual_response_extend {original repaired : (app).Execution}
    (frame : Frame runtime leaks memory owner original repaired) (remaining : Nat) (active : Player)
    (leftTrace : (E).Trace (some ⟨remaining, some active, original⟩))
    (rightTrace : (E).Trace (some ⟨remaining, some active, repaired⟩))
    (firstJoint secondJoint : Player → Option (app).Action)
    (firstLegal : (E).Legal (some ⟨remaining, some active, original⟩) firstJoint)
    (secondLegal : (E).Legal (some ⟨remaining, some active, repaired⟩) secondJoint)
    (sameActions : ∀ who, who ≠ owner → firstJoint who = secondJoint who)
    (firstRealized : some ⟨remaining, none,
        original.respond (app) active ((firstJoint active).getD ⟨none⟩)⟩ ∈
      ((E).step _ ⟨firstJoint, firstLegal⟩).support)
    (secondRealized : some ⟨remaining, none,
        repaired.respond (app) active ((secondJoint active).getD ⟨none⟩)⟩ ∈
      ((E).step _ ⟨secondJoint, secondLegal⟩).support)
    (strategy : ∀ player, (N).BehavioralPolicy player)
    (prior : (N).counterfactualReachProbability strategy owner leftTrace =
      (N).counterfactualReachProbability strategy owner rightTrace) :
    (N).counterfactualReachProbability strategy owner
        (leftTrace.extend firstJoint firstLegal firstRealized) =
      (N).counterfactualReachProbability strategy owner
        (rightTrace.extend secondJoint secondLegal secondRealized) := by
  rw [InformationModel.counterfactualReachProbability,
    InformationModel.counterfactualReachProbability, prior,
    frame.response_counterfactualStepProb runtime leaks menu initial horizon scheduler remaining
      active leftTrace rightTrace firstJoint secondJoint firstLegal secondLegal sameActions
        strategy]

/-- The shared initial physical draw has the same counterfactual step atom
under every legal inactive joint, without dropping any source failure mass. -/
theorem counterfactual_initial_step (who : Player)
    (firstJoint secondJoint : Player → Option (app).Action)
    (firstLegal : (E).Legal none firstJoint) (secondLegal : (E).Legal none secondJoint)
    (strategy : ∀ player, (N).BehavioralPolicy player) (target : (E).State) :
    (N).counterfactualStepProb strategy who .start ⟨firstJoint, firstLegal⟩ target =
      (N).counterfactualStepProb strategy who .start ⟨secondJoint, secondLegal⟩ target := by
  have firstNothing (player : Player) : firstJoint player = none :=
    LegalOption.eq_none_of_inactive _ ((E).legalOption_of_legal firstLegal player)
      (by simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor])
  have secondNothing (player : Player) : secondJoint player = none :=
    LegalOption.eq_none_of_inactive _ ((E).legalOption_of_legal secondLegal player)
      (by simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor])
  rw [InformationModel.counterfactualStepProb, InformationModel.counterfactualStepProb,
    (N).opponentsStepProb_eq_one_of_none strategy who .start ⟨firstJoint, firstLegal⟩ firstNothing,
    (N).opponentsStepProb_eq_one_of_none strategy who .start ⟨secondJoint, secondLegal⟩
      secondNothing]
  rfl

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
