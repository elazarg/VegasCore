/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketOwnerLaws
import Vegas.Game.OnePacketRevealMasses
import Vegas.Game.OnePacketOpeningUnique
import Vegas.Game.OnePacketOperationalReads

/-! # The owner's opening law for slot-trembled late components

At a pending reveal of the owner's turn, the owner's resolution packet reads its
binding and public data only (`Vegas.reactiveResolutionPacket_congr`), so whether
the canonical disclosure transmits is read off the operational state. Along a
one-packet history the one-packet menu offers a transmitting disclosure exactly
when no own envelope names the reveal (`Vegas.disclosure_mem_iff`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A public field is visible to every player. -/
theorem publicStore_playerStore (who : Player) (store : EventGraph.Store (graph setup).layout) :
    (graph setup).publicStore ((graph setup).playerStore who store) =
      (graph setup).publicStore store := by
  funext field
  unfold EventGraph.publicStore EventGraph.playerStore
  by_cases isPublic : (graph setup).fieldPublic field
  · have visible : (graph setup).fieldVisibleTo who field := by
      unfold EventGraph.fieldPublic at isPublic
      unfold EventGraph.fieldVisibleTo
      generalize (graph setup).layout field = kind at isPublic ⊢
      cases kind <;> simp_all [EventGraph.EventField.IsPublic, EventGraph.EventField.VisibleTo]
    simp only [isPublic, visible, ↓reduceIte]
  · simp only [isPublic, ↓reduceIte]

/-- **The resolution packet reads the binding and public data.** At states with
the same operational state, with a publication event of the owner ready, the
owner's resolution packet of every action is the same. -/
theorem reactiveResolutionPacket_congr {first second : (application setup leaks).Control}
    (same : operationalState setup leaks (some first) = operationalState setup leaks (some second))
    {event : (graph setup).EventId} (ready : first.execution.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (action : (graph setup).Action event) :
    reactiveResolutionPacket owner event payload binding checks outputEq action
        (first.execution.observe (application setup leaks) owner).application =
      reactiveResolutionPacket owner event payload binding checks outputEq action
        (second.execution.observe (application setup leaks) owner).application := by
  have bindings := SameOperational.binding same ready view
  have publics := SameOperational.publicView same
  have stores : (graph setup).publicStore first.execution.application.config.store =
      (graph setup).publicStore second.execution.application.config.store :=
    congrArg (fun view : PublicView (graph setup) => view.observation.store) publics
  have own : ∀ store : EventGraph.Store (graph setup).layout,
      binding.get? ((graph setup).playerStore owner store) = binding.get? store := by
    intro store
    rcases binding with ⟨field, layoutEq⟩
    apply EventGraph.FieldRef.get?_congr
    apply EventGraph.playerStore_of_visible
    change ((graph setup).layout field).VisibleTo owner
    rw [layoutEq]
    rfl
  have resolved : EventGraph.EventCode.resolveOutput? binding checks true
      ((graph setup).playerStore owner first.execution.application.config.store) =
      EventGraph.EventCode.resolveOutput? binding checks true
        ((graph setup).playerStore owner second.execution.application.config.store) := by
    unfold EventGraph.EventCode.resolveOutput?
    rw [own, own, bindings]
    simp only [Option.bind_eq_bind]
    congr 1
    funext bound
    rw [← EventGraph.GuardCheck.allAccepted?_publicStore checks
        ((graph setup).playerStore owner first.execution.application.config.store),
      ← EventGraph.GuardCheck.allAccepted?_publicStore checks
        ((graph setup).playerStore owner second.execution.application.config.store),
      publicStore_playerStore, publicStore_playerStore, stores]
  have firstStore : (first.execution.observe (application setup leaks)
      owner).application.observation.store =
      (graph setup).playerStore owner first.execution.application.config.store := rfl
  have secondStore : (second.execution.observe (application setup leaks)
      owner).application.observation.store =
      (graph setup).playerStore owner second.execution.application.config.store := rfl
  have firstPublic : (first.execution.observe (application setup leaks)
      owner).application.publicView = first.execution.application.publicView := rfl
  have secondPublic : (second.execution.observe (application setup leaks)
      owner).application.publicView = second.execution.application.publicView := rfl
  unfold reactiveResolutionPacket
  rw [firstStore, secondStore, firstPublic, secondPublic]
  rw [resolved, publics]

/-- The canonical disclosure transmits exactly when the resolution packet
exists. -/
theorem disclosure_transmission_isSome (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) {event : (graph setup).EventId}
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (action : (graph setup).Action event) :
    ((runtime setup).canonicalServiceDecision leaks who past view event
        action).transmission.isSome =
      (reactiveResolutionPacket who event payload binding checks outputEq action
        view.application).isSome := by
  unfold EventGraphRuntime.canonicalServiceDecision
  cases packet : reactiveResolutionPacket who event payload binding checks outputEq action
      view.application with
  | none =>
      simp only [EventGraphRuntime.canonicalReactiveDecision, node, packet, Option.map_none,
        ReactiveApplication.SubmissionNormalization.action, Option.isSome_none]
  | some sent =>
      simp only [EventGraphRuntime.canonicalReactiveDecision, node, packet, Option.map_some,
        ReactiveApplication.SubmissionNormalization.action, Option.isSome_some]

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **When the disclosure is silent.** Along every history of the one-packet
game, at a reveal of the player's turn, when every publication value is a
bounded value, the chosen canonical disclosure keeps silence exactly when its
resolution packet is missing or an own envelope already names the reveal. -/
theorem disclosure_silent_iff (covers : bounds.CoversOutputValues)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    ((responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))).1.getD
          ⟨none⟩).transmission = none ↔
      ¬ ((reactiveResolutionPacket who event payload binding checks outputEq
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (control.execution.observe (application setup leaks) who).application).isSome ∧
        ¬ ∃ message ∈ (application setup leaks).outputs (control.execution.recall who),
          message.payload.call.event? (graph setup) = some event) := by
  set disclosure := (runtime setup).canonicalServiceDecision leaks who
    (control.execution.recall who) (control.execution.observe (application setup leaks) who) event
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) with disclosureEq
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have transmits := disclosure_transmission_isSome (leaks := leaks) who
    (control.execution.recall who) (control.execution.observe (application setup leaks) who) node
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
  rw [← disclosureEq] at transmits
  have decodedMember : ∀ response : (application setup leaks).Action,
      response ∈ bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) →
      (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) response).1.getD ⟨none⟩ =
        response := by
    intro response member
    simp only [responseChoice, member, ↓reduceDIte, Option.getD_some]
  have decodedSilent : ∀ response : (application setup leaks).Action,
      response ∉ bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) →
      (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) response).1.getD ⟨none⟩ =
        ⟨none⟩ := by
    intro response notMember
    simp only [responseChoice, notMember, ↓reduceDIte, Option.getD_some]
  cases sends : disclosure.transmission with
  | none =>
      rw [sends, Option.isSome_none] at transmits
      constructor
      · intro _ both
        rw [← transmits] at both
        cases both.1
      · intro _
        by_cases member : disclosure ∈ bounds.onePacketActions (runtime setup) leaks who
            (control.execution.recall who)
            (control.execution.observe (application setup leaks) who)
        · rw [decodedMember _ member]
          exact sends
        · rw [decodedSilent _ member]
  | some material =>
      rw [sends, Option.isSome_some] at transmits
      by_cases unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event =
          false
      · have member := onePacket_disclosure_offered covers trace who event turn unsent node
          material sends
        rw [decodedMember _ member, sends]
        have noOutput : ¬ ∃ message ∈ (application setup leaks).outputs
            (control.execution.recall who), message.payload.call.event? (graph setup) =
              some event := by
          intro named
          have recorded := (history_eventRecorded_iff rawTrace who event).mpr named
          rw [unsent] at recorded
          cases recorded
        constructor
        · intro silent
          cases silent
        · intro claim
          exact (claim ⟨transmits.symm, noOutput⟩).elim
      · have recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event =
            true := by
          cases value : (runtime setup).eventRecorded leaks (control.execution.recall who) event
          · exact (unsent value).elim
          · rfl
        obtain ⟨message, output, named⟩ := (history_eventRecorded_iff rawTrace who event).mp
          recorded
        have notMember : disclosure ∉ bounds.onePacketActions (runtime setup) leaks who
            (control.execution.recall who)
            (control.execution.observe (application setup leaks) who) := by
          intro member
          rcases ((bounds.mem_onePacketActions (runtime setup) leaks who _ _ disclosure).mp
              member).2 with silent | ⟨other, otherSends, permitted⟩
          · rw [sends] at silent
            cases silent
          rw [sends] at otherSends
          cases Option.some.inj otherSends
          have recalled := (runtime setup).countRecall_history leaks rawTrace
          have first := ((countPermits_eq_true_iff _ _).mp permitted).2.2
          rw [(runtime setup).localEnvelope_eq_of_recall leaks control.execution recalled.1
            recalled.2.1 who material] at first
          have earlier := earlierOwnPacket_of_output rawTrace who
            ((application setup leaks).packet ((application setup leaks).submit
              control.execution.application who material) who
              (control.execution.network.known who) material) message output
          apply first message earlier
          rw [named]
          rcases (runtime setup).canonicalServiceDecision_cases leaks who
              (control.execution.recall who)
              (control.execution.observe (application setup leaks) who) event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) with
            silent | submitted
          · have silent' : disclosure = ⟨none⟩ := silent
            rw [silent'] at sends
            cases sends
          · have submitted' : (runtime setup).submittedEvent? leaks disclosure = some event :=
              submitted
            unfold EventGraphRuntime.submittedEvent? at submitted'
            rw [sends] at submitted'
            exact submitted'.symm
        rw [decodedSilent _ notMember]
        constructor
        · intro _ both
          exact both.2 ⟨message, output, named⟩
        · intro _
          rfl

end Vegas
