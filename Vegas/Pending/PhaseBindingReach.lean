/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairFrame
import Interaction.ReactiveOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach
import GameTheoryExtensions.Analysis.Protocol.SingleMoverReach

/-! # Actual foreign-player reach and response factors under directed repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
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

omit [Fintype Player] in
/-- Physical foreign recall determines the exact recorded own-play list even
when the current protocol input is inactive. -/
theorem foreign_ownPlay {first second : (app).Control}
    (frame : Frame runtime leaks memory owner first.execution second.execution)
    (leftTrace : (E).Trace (some first)) (rightTrace : (E).Trace (some second))
    (who : Player) (different : who ≠ owner) :
    (N).ownPlay who leftTrace = (N).ownPlay who rightTrace := by
  have word (control : (app).Control) (trace : (E).Trace (some control)) :
      (N).ownPlay who trace = (app).recallOwnPlay (control.execution.recall who) := by
    change (menu.signals initial horizon scheduler).ownPlay who trace = _
    rw [← menu.ownPlay_toRawTrace initial horizon scheduler who trace,
      (app).trace_ownPlay]
    rfl
  rw [word first leftTrace, word second rightTrace, frame.foreignRecall who different]

omit [Fintype Player] in
/-- Every other player's full history reach factor agrees under the SAME
profile, without any likelihood premise or recall truncation. -/
theorem foreign_playerReach {first second : (app).Control}
    (frame : Frame runtime leaks memory owner first.execution second.execution)
    (leftTrace : (E).Trace (some first)) (rightTrace : (E).Trace (some second))
    (strategy : ∀ player, (N).BehavioralPolicy player) (who : Player) (different : who ≠ owner) :
    (N).playerReachProbability strategy who leftTrace =
      (N).playerReachProbability strategy who rightTrace := by
  rw [(N).playerReachProbability_eq_ownPlayReachProbability,
    (N).playerReachProbability_eq_ownPlayReachProbability,
    frame.foreign_ownPlay runtime leaks menu initial horizon scheduler leftTrace rightTrace who
      different]

/-- At paired response callbacks, exact off-owner raw actions and the actual
foreign input equality derive all opponent behavioral factors. -/
theorem response_opponentsStepProb {original repaired : (app).Execution}
    (frame : Frame runtime leaks memory owner original repaired) (remaining : Nat) (active : Player)
    (leftTrace : (E).Trace (some ⟨remaining, some active, original⟩))
    (rightTrace : (E).Trace (some ⟨remaining, some active, repaired⟩))
    (firstJoint secondJoint : Player → Option (app).Action)
    (firstLegal : (E).Legal (some ⟨remaining, some active, original⟩) firstJoint)
    (secondLegal : (E).Legal (some ⟨remaining, some active, repaired⟩) secondJoint)
    (sameActions : ∀ who, who ≠ owner → firstJoint who = secondJoint who)
    (strategy : ∀ player, (N).BehavioralPolicy player) :
    (N).opponentsStepProb strategy owner leftTrace ⟨firstJoint, firstLegal⟩ =
      (N).opponentsStepProb strategy owner rightTrace ⟨secondJoint, secondLegal⟩ := by
  classical
  unfold InformationModel.opponentsStepProb
  apply Finset.prod_congr rfl
  intro who member
  have different : who ≠ owner := (Finset.mem_erase.mp member).1
  have observations : (N).infoOf who leftTrace = (N).infoOf who rightTrace := by
    change (menu.signals initial horizon scheduler).infoOf who leftTrace =
      (menu.signals initial horizon scheduler).infoOf who rightTrace
    rw [menu.info, menu.info]
    by_cases acting : some active = some who
    · simp only [ReactiveApplication.observe, acting, ↓reduceIte]
      exact congrArg some (frame.foreign_input who different)
    · simp only [ReactiveApplication.observe, acting, ↓reduceIte]
  have leftAtom := pmf_map_apply_of_injective (strategy who ((N).infoOf who leftTrace))
    Subtype.val_injective ((N).choicesOfLegal leftTrace ⟨firstJoint, firstLegal⟩ who)
  have rightAtom := pmf_map_apply_of_injective (strategy who ((N).infoOf who rightTrace))
    Subtype.val_injective ((N).choicesOfLegal rightTrace ⟨secondJoint, secondLegal⟩ who)
  apply congrArg ENNReal.toReal
  rw [← leftAtom, ← rightAtom]
  change ((strategy who ((N).infoOf who leftTrace)).map Subtype.val) (firstJoint who) =
    ((strategy who ((N).infoOf who rightTrace)).map Subtype.val) (secondJoint who)
  rw [observations, sameActions who different]

/-- Deterministic response transitions introduce no additional counterfactual
factor beyond the concrete opponent behavioral probabilities above. -/
theorem response_counterfactualStepProb {original repaired : (app).Execution}
    (frame : Frame runtime leaks memory owner original repaired) (remaining : Nat) (active : Player)
    (leftTrace : (E).Trace (some ⟨remaining, some active, original⟩))
    (rightTrace : (E).Trace (some ⟨remaining, some active, repaired⟩))
    (firstJoint secondJoint : Player → Option (app).Action)
    (firstLegal : (E).Legal (some ⟨remaining, some active, original⟩) firstJoint)
    (secondLegal : (E).Legal (some ⟨remaining, some active, repaired⟩) secondJoint)
    (sameActions : ∀ who, who ≠ owner → firstJoint who = secondJoint who)
    (strategy : ∀ player, (N).BehavioralPolicy player) :
    (N).counterfactualStepProb strategy owner leftTrace ⟨firstJoint, firstLegal⟩
        (some ⟨remaining, none,
          original.respond (app) active ((firstJoint active).getD ⟨none⟩)⟩) =
      (N).counterfactualStepProb strategy owner rightTrace ⟨secondJoint, secondLegal⟩
        (some ⟨remaining, none,
          repaired.respond (app) active ((secondJoint active).getD ⟨none⟩)⟩) := by
  classical
  rw [InformationModel.counterfactualStepProb, InformationModel.counterfactualStepProb,
    frame.response_opponentsStepProb runtime leaks menu initial horizon scheduler remaining active
      leftTrace
      rightTrace firstJoint secondJoint firstLegal secondLegal sameActions strategy]
  simp only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.transition,
    PMF.pure_apply_self]

/-- Nobody acts at an actual scheduler boundary. Its counterfactual factor is
therefore exactly the real transition atom, without any behavioral multiplier. -/
theorem environment_counterfactualStepProb (remaining : Nat) (execution : (app).Execution)
    (trace : (E).Trace (some ⟨remaining, none, execution⟩))
    (joint : Player → Option (app).Action)
    (legal : (E).Legal (some ⟨remaining, none, execution⟩) joint)
    (strategy : ∀ player, (N).BehavioralPolicy player) (who : Player) (target : (E).State) :
    (N).counterfactualStepProb strategy who trace ⟨joint, legal⟩ target =
      ((app).transition initial horizon scheduler (some ⟨remaining, none, execution⟩) joint
        target).toReal := by
  have nothing (player : Player) : joint player = none := by
    exact LegalOption.eq_none_of_inactive _ ((E).legalOption_of_legal legal player)
      (by simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor])
  rw [InformationModel.counterfactualStepProb,
    (N).opponentsStepProb_eq_one_of_none strategy who trace ⟨joint, legal⟩ nothing, one_mul]
  rfl

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
