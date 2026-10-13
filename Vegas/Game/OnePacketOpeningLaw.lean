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

end Vegas
