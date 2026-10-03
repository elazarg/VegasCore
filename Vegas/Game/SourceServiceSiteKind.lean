/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceContinuationBridge

/-! # Kinds of native decision sites

Every native information site of the permitted service model is a decision
during the phase of the one ready event. What the acting player faces there is
decided by that event, the player's own recall, and its view: a public sample,
another player's binding or disclosure, or the player's own binding or
disclosure, before or after its submission. Each kind carries the
facts its local comparison uses. Since the kind is a function of the site's
information state, every history of a site has the same kind.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- What a player's decision is, given its own recall `past`, its view, and the
event its view shows ready. -/
inductive DecisionSiteKind (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId) : Prop
  /-- A public sample: the event has no actor. -/
  | chance (actorless : (graph setup).actor? event = none)
  /-- Another player's binding. -/
  | foreignBinding (owner : Player) (payload : L.Ty) (foreign : who ≠ owner)
      (outputEq : (graph setup).outputLayout event = .binding owner payload)
  /-- Another player's disclosure. -/
  | foreignDisclosure (owner : Player) (payload : L.Ty) (foreign : who ≠ owner)
      (owned : (graph setup).actor? event = some owner)
      (outputEq : (graph setup).outputLayout event = .publication payload)
  /-- The player's own binding, already submitted. -/
  | recordedBinding (payload : L.Ty)
      (outputEq : (graph setup).outputLayout event = .binding who payload)
      (recorded : (runtime setup).eventRecorded leaks past event = true)
  /-- The player's own binding, not yet submitted. -/
  | unsentBinding (payload : L.Ty)
      (outputEq : (graph setup).outputLayout event = .binding who payload)
      (unsent : (runtime setup).eventRecorded leaks past event = false)
  /-- The player's own disclosure, already submitted. -/
  | recordedDisclosure (payload : L.Ty)
      (owned : (graph setup).actor? event = some who)
      (outputEq : (graph setup).outputLayout event = .publication payload)
      (recorded : (runtime setup).eventRecorded leaks past event = true)
  /-- The player's own disclosure, not yet submitted. Both effective Boolean
  source choices produce an actual decision packet. -/
  | unsentDisclosure (payload : L.Ty)
      (owned : (graph setup).actor? event = some who)
      (outputEq : (graph setup).outputLayout event = .publication payload)
      (unsent : (runtime setup).eventRecorded leaks past event = false)

/-- Every decision has a kind. -/
theorem DecisionSiteKind.classify (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId) :
    DecisionSiteKind setup leaks who past view event := by
  have actorOf {field : EventGraph.EventField Player L}
      (outputEq : (graph setup).outputLayout event = field)
      {code : EventGraph.EventCode (graph setup).layout field}
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = code) :
      (graph setup).actor? event = code.actor := by
    rw [← codeEq]
    exact (EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event)).symm
  cases nodeView (graph setup) event with
  | sample payload law outputEq codeEq => exact .chance (actorOf outputEq codeEq)
  | bind owner payload outputEq codeEq =>
      by_cases same : who = owner
      · subst same
        cases recorded : (runtime setup).eventRecorded leaks past event with
        | false => exact .unsentBinding payload outputEq recorded
        | true => exact .recordedBinding payload outputEq recorded
      · exact .foreignBinding owner payload same outputEq
  | resolve owner payload binding checks outputEq codeEq =>
      have owned := actorOf outputEq codeEq
      by_cases same : who = owner
      · subst same
        cases recorded : (runtime setup).eventRecorded leaks past event with
        | true => exact .recordedDisclosure payload owned outputEq recorded
        | false => exact .unsentDisclosure payload owned outputEq recorded
      · exact .foreignDisclosure owner payload same owned outputEq

variable [Fintype Player]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- Every native information site is a decision during the phase of an event
its view shows ready, and has a kind. -/
theorem exists_siteKind (who : Player) (site : service.model.InformationSite who) :
    ∃ past view event, site.1 = some (past, view) ∧
      view.application.publicView.EventReady event ∧
      DecisionSiteKind service.setup service.leaks who past view event := by
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active service.model site history
  obtain ⟨control, current⟩ : ∃ control, history.1.state = some control := by
    cases state : history.1.state with
    | none => rw [state] at active; cases active
    | some control => exact ⟨control, rfl⟩
  have actor : control.actor = some who := by rw [current] at active; exact active
  obtain ⟨remaining, actorValue, execution⟩ := control
  change actorValue = some who at actor
  subst actorValue
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    current ▸ history.1.trace
  obtain ⟨phase⟩ := service.exists_decisionPhase who remaining execution trace
  exact ⟨_, _, phase.event, history.2.symm.trans (service.infoOf_decision history.1 current),
    (execution.application.publicView_eventReady _).mpr phase.ready,
    DecisionSiteKind.classify service.setup service.leaks who _ _ phase.event⟩

end SourceServiceSpec

end Vegas
