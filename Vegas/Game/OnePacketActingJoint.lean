/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketIntendedProjection
import Vegas.Source.IntendedPrefixSwap

/-! # The acting joint of a realized intended step

A realized step of the intended game whose target is also reached by the acting
joint of a choice (`Vegas.actingJoint`) is the step of that acting joint,
provided the choice is addressed to the acting site
(`Vegas.intended_joint_eq_actingJoint`). Without that proviso the claim fails
at a reveal: every opening reveal, whatever owner and name it carries, reaches
the same target as the owner's own opening.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **A realized intended step is the acting joint of its choice.** If a realized
step of the intended game and the acting joint of a choice addressed to the
acting site under some commitment interface reach the same target, the joint
action of the step is that acting joint. -/
theorem intended_joint_eq_actingJoint (setup : Setup (Player := Player) (L := L))
    {state target : setup.ProtocolState} {joint : Player → Option (OwnAction Player L)}
    (legal : setup.intendedProtocol.Legal state joint)
    (realized : target ∈ (setup.intendedProtocol.step state ⟨joint, legal⟩).support)
    {admission : CommitmentInterface setup.program} (choice : Option (OwnAction Player L))
    (addressed : ∀ who action, choice = some action →
      (setup.executionProtocol admission).active state who →
        action ∈ (setup.executionProtocol admission).available state who)
    (actingRealized :
      target ∈ (setup.protocolStep state (actingJoint setup state choice)).support) :
    joint = actingJoint setup state choice := by
  funext who
  have member := legal.2 who
  cases state with
  | none =>
      revert member
      cases joint who with
      | none => exact fun _ => rfl
      | some _ => exact fun chosen => chosen.1.elim
  | some point =>
      rw [protocolStep_actingJoint] at actingRealized
      by_cases acting : ProtocolView.actor who setup.program
          (ProtocolState.observe who setup.program point) = some who
      · simp only [actingJoint, acting, ↓reduceIte]
        exact setup.intended_joint_eq_of_choice legal realized addressed actingRealized who
          acting
      · simp only [actingJoint, acting, ↓reduceIte]
        revert member
        cases joint who with
        | none => exact fun _ => rfl
        | some _ => exact fun chosen => (acting chosen.1).elim

end Vegas
