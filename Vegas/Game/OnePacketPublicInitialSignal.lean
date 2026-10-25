/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerPriorSite

/-! # The actual late key retains every public initial input -/

noncomputable section

namespace Vegas

open Vegas Vegas.SourceProgram Interaction GameTheory GameTheory.Protocol EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {bounds : MessageBounds (graph setup)} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}

/-- Public initial fields are read directly from the actual input configuration. -/
theorem execution_public_initial_input
    (execution : (application setup leaks).Execution) (who : Player)
    {draw : State L setup.context}
    (inputsEq : execution.application.config.inputs = setup.eventInputs draw)
    (input : (graph setup).InputId) (publicField : (graph setup).fieldPublic (.inl input)) :
    (execution.observe (application setup leaks) who).application.publicView.observation.store
      (.inl input) = some (setup.eventInputs draw input) := by
  change (graph setup).publicStore execution.application.config.store (.inl input) = _
  rw [EventGraph.publicStore_of_public _ _ _ publicField]
  change some (execution.application.config.inputs input) = _
  rw [inputsEq]

variable [Fintype Player]

/-- Every draw actually represented by a site history is read at each public
initial field by that site's fixed public view, not only one chosen anchor. -/
theorem site_public_initial_inputs {who : Player}
    {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (decision : site.1 = some (past, view))
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who site.1) {control : (application setup leaks).Control}
    {draw : State L setup.context} (stateEq : history.1.state = some control)
    (inputsEq : control.execution.application.config.inputs = setup.eventInputs draw)
    (input : (graph setup).InputId) (publicField : (graph setup).fieldPublic (.inl input)) :
    view.application.publicView.observation.store (.inl input) =
      some (setup.eventInputs draw input) := by
  obtain ⟨seen, seenEq, viewEq⟩ := state_of_decision history decision
  have same : control = seen := Option.some.inj (stateEq.symm.trans seenEq)
  subst seen
  rw [← viewEq]
  exact execution_public_initial_input control.execution who inputsEq input publicField

/-- Same-key sites share the actual public view, including the initial store. -/
theorem same_key_publicView {who : Player}
    {site₁ site₂ : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past₁ past₂ : List (application setup leaks).PlayerEntry}
    {view₁ view₂ : (application setup leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup leaks who site₁.1 = lateKey setup leaks who site₂.1) :
    view₁.application.publicView = view₂.application.publicView := by
  rw [firstSite, secondSite] at sameKey
  simp only [lateKey, Option.some.injEq, LateKey.mk.injEq] at sameKey
  obtain ⟨_, currentEq, _, _⟩ := sameKey
  exact congrArg Prod.fst currentEq

/-- Any two actual history draws at same-key sites have equal public initial
inputs. No unconditional prior independence or global hidden-fiber premise is used. -/
theorem same_key_public_initial_inputs {who : Player}
    {site₁ site₂ : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past₁ past₂ : List (application setup leaks).PlayerEntry}
    {view₁ view₂ : (application setup leaks).PlayerView}
    (firstSite : site₁.1 = some (past₁, view₁)) (secondSite : site₂.1 = some (past₂, view₂))
    (sameKey : lateKey setup leaks who site₁.1 = lateKey setup leaks who site₂.1)
    (first : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who site₁.1)
    (second : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who site₂.1)
    {firstControl secondControl : (application setup leaks).Control}
    {firstDraw secondDraw : State L setup.context}
    (firstState : first.1.state = some firstControl)
    (secondState : second.1.state = some secondControl)
    (firstInputs : firstControl.execution.application.config.inputs = setup.eventInputs firstDraw)
    (secondInputs : secondControl.execution.application.config.inputs =
      setup.eventInputs secondDraw)
    (input : (graph setup).InputId) (publicField : (graph setup).fieldPublic (.inl input)) :
    setup.eventInputs firstDraw input = setup.eventInputs secondDraw input := by
  have firstRead := site_public_initial_inputs firstSite first firstState firstInputs input
    publicField
  have secondRead := site_public_initial_inputs secondSite second secondState secondInputs input
    publicField
  have views := same_key_publicView firstSite secondSite sameKey
  have observed := congrArg (fun view : PublicView (graph setup) =>
    view.observation.store (.inl input)) views
  exact Option.some.inj (firstRead.symm.trans (observed.trans secondRead))

end Vegas
