/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceContinuationBridge

/-! # Kinds of native decision sites

Every actual native information site has a full local input and either a
completed cut or a ready event. Arbitrary builders may activate players after
graph completion. At a ready event, its constructor and the player's recall
classify the decision as a public sample, a foreign binding or disclosure, or
an own binding or disclosure before or after submission. These public and
recalled facts agree throughout the site's hidden history fiber.

The fixed calendar additionally supplies a current ready-event phase at every
decision. Its specialized consumer excludes the completed-cut alternative.
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

/-- Every actual native decision has a full local input and either a completed
cut or a ready source constructor. An arbitrary builder may activate a player
after graph completion, so no fixed-calendar phase premise is used. -/
theorem sourceServiceInformationSite_cases
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (EventGraphRuntime.State (graph setup))) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (who : Player)
    (site : (menu.information initial horizon scheduler).InformationSite who) :
    ∃ past view, site.1 = some (past, view) ∧
      ((∀ event, event ∈ view.application.publicView.observation.completionOrder) ∨
        ∃ event, view.application.publicView.EventReady event ∧
          DecisionSiteKind setup leaks who past view event) := by
  let app := application setup leaks
  let model := menu.information initial horizon scheduler
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active model site history
  obtain ⟨control, current⟩ : ∃ control, history.1.state = some control := by
    cases state : history.1.state with
    | none => rw [state] at active; cases active
    | some control => exact ⟨control, rfl⟩
  have acting : control.actor = some who := by rw [current] at active; exact active
  have observed : site.1 = some (control.execution.recall who,
      control.execution.observe app who) := by
    have input := history.2.symm.trans (menu.info initial horizon scheduler who history.1.trace)
    simpa only [current, ReactiveApplication.observe, acting, ↓reduceIte] using input
  refine ⟨control.execution.recall who, control.execution.observe app who, observed, ?_⟩
  by_cases complete : control.execution.application.config.cut.Terminal
  · left
    intro event
    exact (control.execution.application.config.history_exact event).mpr
      (complete.symm ▸ Finset.mem_univ event)
  · obtain ⟨event, ready⟩ :=
      control.execution.application.config.cut.exists_ready_of_not_terminal complete
    exact Or.inr ⟨event, (control.execution.application.publicView_eventReady event).mpr ready,
      DecisionSiteKind.classify setup leaks who _ _ event⟩

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
