/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCanonicalPermits

/-! # Committed values and emitted transmissions

A source action binds a successful value whenever it is a commitment
(`Vegas.SourceProgram.OwnAction.CommitsValue`); such an action encodes, at a
binding event, to a successful binding value
(`Vegas.encodeEventAction?_commitsValue`). Every transmitting recall entry
emitted the packet of its submission, at every history under arbitrary
responses and scheduler choices (`Vegas.transmissionsEmitted_serviceInvariant`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Effective

/-- A source action binds a successful value whenever it is a commitment. -/
def SourceProgram.OwnAction.CommitsValue : OwnAction Player L → Prop
  | .commit _ _ _ choice => ∃ value, choice = .success value
  | .reveal .. => True

/-- A source action binding a successful value encodes, at a binding event, to a
successful binding value. -/
theorem encodeEventAction?_commitsValue :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (event : Fin (eventCount program)) →
    (action : OwnAction Player L) → action.CommitsValue →
    ∀ encoded, encodeEventAction? program event action = some encoded →
    ∀ owner payload (binding : outputLayout program event = .binding owner payload),
      ∃ value : L.Val payload,
        encoded = cast (congrArg EventGraph.EventField.Action binding.symm)
          (PublicationResult.success value)
  | _, _, .ret _, event, _, _, _, _ => nomatch event
  | _, _, .sample name fresh law next, event, action, commits, encoded, encodes => by
      cases event using Fin.cases with
      | zero => cases encodes
      | succ tail =>
          exact encodeEventAction?_commitsValue next tail action commits encoded encodes
  | _, _, .commit name owner fresh guard next, event, action, commits, encoded, encodes => by
      cases event using Fin.cases with
      | zero =>
          intro bindingOwner bindingPayload binding
          cases binding
          cases action with
          | reveal => cases encodes
          | commit actionOwner actionName actionPayload choice =>
              obtain ⟨value, rfl⟩ := commits
              simp only [encodeEventAction?, Fin.cases_zero] at encodes
              split_ifs at encodes with ownerEq nameEq payloadEq
              subst payloadEq
              exact ⟨value, (Option.some.inj encodes).symm⟩
      | succ tail =>
          exact encodeEventAction?_commitsValue next tail action commits encoded encodes
  | _, _, .reveal published owner name fresh selected unresolved next, event, action, commits,
      encoded, encodes => by
      cases event using Fin.cases with
      | zero =>
          intro _ _ binding
          cases binding
      | succ tail =>
          exact encodeEventAction?_commitsValue next tail action commits encoded encodes

end Effective

section Repeated

/-- Every transmitting recall entry emitted the packet of its submission. -/
def TransmissionsEmitted (execution : (application setup leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who, ∀ material, entry.action.transmission = some material →
    ∃ message, entry.emitted = some message ∧ message.payload.call = material.call.packet

/-- Transmissions are emitted at every history, under arbitrary responses and
scheduler choices. -/
theorem transmissionsEmitted_serviceInvariant (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler (TransmissionsEmitted (leaks := leaks))
    where
  respond execution responder action valid := by
    intro who entry member material transmits
    rw [(runtime setup).respond_recall leaks execution responder who action] at member
    split at member
    · rename_i same
      subst same
      rcases List.mem_append.mp member with old | new
      · exact valid who entry old material transmits
      · cases List.mem_singleton.mp new
        change action.transmission = some material at transmits
        refine ⟨_, by rw [transmits]; rfl, rfl⟩
    · exact valid who entry member material transmits
  environment execution next command valid _ moved := by
    intro who entry member
    rw [(application setup leaks).environmentStep_recall execution next command moved] at member
    exact valid who entry member

end Repeated

end Vegas
