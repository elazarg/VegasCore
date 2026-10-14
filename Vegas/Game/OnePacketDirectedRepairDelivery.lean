/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketDirectedRepairResponse

/-! # Delivery values of repaired successful bindings

A binding-repair frame preserves every successful original binding. At an
ordinary reveal this is sufficient for equality of the delivered value, even
when the private repair memory records that unchanged binding explicitly.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

namespace DirectedBindingFrame

variable {memory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired : (application setup leaks).Execution}

/-- Successful original bindings deliver the same value after directed repair.
This permits explicitly remembered usable bindings; no empty-shadow premise is
needed. At non-reveal turns there is no delivered value on either side. -/
theorem deliveredValue_of_successful
    (frame : DirectedBindingFrame memory owner original repaired)
    (unfailed : ∀ event payload
      (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
      (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
      (outputEq : (graph setup).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve owner payload binding checks),
      original.application.publicView.ownTurn? owner = some event →
      nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
      ∃ value, binding.get? original.application.config.store = some (.success value)) :
    deliveredValue setup leaks owner (original.observe (application setup leaks) owner) =
      deliveredValue setup leaks owner (repaired.observe (application setup leaks) owner) := by
  have sameTurn : repaired.application.publicView.ownTurn? owner =
      original.application.publicView.ownTurn? owner :=
    congrArg (fun pub => pub.ownTurn? owner) frame.toFrame.publicView.symm
  unfold deliveredValue
  change (match original.application.publicView.ownTurn? owner with
    | none => none
    | some event => _) = (match repaired.application.publicView.ownTurn? owner with
    | none => none
    | some event => _)
  rw [sameTurn]
  cases turn : original.application.publicView.ownTurn? owner with
  | none => rfl
  | some event =>
      cases node : nodeView (graph setup) event with
      | bind | sample => simp only [node]
      | resolve actor payload binding checks outputEq codeEq =>
          have owned := (original.application.publicView.ownTurn?_spec owner event turn).2
          have actorEq : actor = owner :=
            Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
          subst actor
          obtain ⟨value, stored⟩ := unfailed event payload binding checks outputEq codeEq turn node
          have repairedStored := EventGraph.Store.BindingRefines.success frame.successful
            binding value stored
          simp only [node]
          congr 2
          change binding.get? ((graph setup).playerStore owner original.application.config.store) =
            binding.get? ((graph setup).playerStore owner repaired.application.config.store)
          rw [binding.get?_playerStore owner _ rfl, binding.get?_playerStore owner _ rfl,
            stored, repairedStored]

end DirectedBindingFrame

end Vegas
