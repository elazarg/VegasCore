/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceOwnerSupport
import Vegas.Game.RevealServiceFocalRecall

/-! # The actual selected owner information fiber

The source view and a recorded native alias recall determine the complete
owner information value. All reachability and observation facts below are
derived from actual restricted-game histories and actual service execution.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Native owner information determines the actual source observation;
no selector premise is needed for this direction. -/
theorem owner_information_projects
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (left right : Profile (information setup leaks bounds watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (leftHistory rightHistory : (protocol setup leaks bounds watcher).History)
    (leftSupport : leftHistory ∈ ((information setup leaks bounds watcher).runBehavioral left
      (blockOffset event.val + 2 * event.val + 3)).support)
    (rightSupport : rightHistory ∈ ((information setup leaks bounds watcher).runBehavioral right
      (blockOffset event.val + 2 * event.val + 3)).support)
    (same : (information setup leaks bounds watcher).infoOf who leftHistory.trace =
      (information setup leaks bounds watcher).infoOf who rightHistory.trace) :
    setup.protocolObserve who (prefixReadout setup leaks event.val leftHistory.state) =
      setup.protocolObserve who (prefixReadout setup leaks event.val rightHistory.state) := by
  let responses := menu setup leaks bounds watcher
  obtain ⟨leftBoundary, _leftSupport, leftState, leftInitial, _leftInitialSupport,
      leftSource, _leftCheckpoint, leftOpportunity, leftDecoded⟩ :=
    owner_supported setup leaks bounds watcher who reveals observer openable left event owned
      leftHistory leftSupport
  obtain ⟨rightBoundary, _rightSupport, rightState, rightInitial, _rightInitialSupport,
      rightSource, _rightCheckpoint, rightOpportunity, rightDecoded⟩ :=
    owner_supported setup leaks bounds watcher who reveals observer openable right event owned
      rightHistory rightSupport
  change (responses.signals _ _ _).infoOf who leftHistory.trace =
    (responses.signals _ _ _).infoOf who rightHistory.trace at same
  rw [responses.info, responses.info, leftState, rightState] at same
  simp only [ReactiveApplication.observe, ↓reduceIte] at same
  have beforeView := congrArg Prod.snd (Option.some.inj same)
  have leftLeaks := PrefixCheckpoint.runtime_fact
    (fun execution => execution.network.leaked = fun _ => [])
    (fun _ _ _ _ checkpoint => checkpoint.leaked) _ _ _ _ _ _ _ _ leftOpportunity
  have rightLeaks := PrefixCheckpoint.runtime_fact
    (fun execution => execution.network.leaked = fun _ => [])
    (fun _ _ _ _ checkpoint => checkpoint.leaked) _ _ _ _ _ _ _ _ rightOpportunity
  have sourceView := (PublicPrefixCheckpoint.observe_eq_iff who setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val
    leftSource rightSource _ _
    (PrefixCheckpoint.toPublic _ _ _ _ _ _ _ _ leftOpportunity)
    (PrefixCheckpoint.toPublic _ _ _ _ _ _ _ _ rightOpportunity) rfl
    (by rw [leftLeaks, rightLeaks])).mpr beforeView
  simpa only [leftState, rightState, prefixReadout, ownerOpportunity,
    leftDecoded, rightDecoded, Setup.protocolObserve, Option.map_some] using
      congrArg some sourceView

/-- Equality of the decoded source view reconstructs a selected focal
player's entire native information, including private replay recall. -/
theorem owner_focal_information
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (source : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (reference : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (left right : Profile (information setup leaks bounds watcher).behavioralSignature)
    (selected : (menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) left who =
        focalPolicy setup leaks bounds source weight nonnegative atMostOne who reference)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (leftHistory rightHistory : (protocol setup leaks bounds watcher).History)
    (leftSupport : leftHistory ∈ ((information setup leaks bounds watcher).runBehavioral left
      (blockOffset event.val + 2 * event.val + 3)).support)
    (rightSupport : rightHistory ∈ ((information setup leaks bounds watcher).runBehavioral right
      (blockOffset event.val + 2 * event.val + 3)).support)
    (referenceInfo : (information setup leaks bounds watcher).infoOf who rightHistory.trace =
      some (reference, view))
    (same : setup.protocolObserve who
      (prefixReadout setup leaks event.val leftHistory.state) =
        setup.protocolObserve who (prefixReadout setup leaks event.val rightHistory.state)) :
    (information setup leaks bounds watcher).infoOf who leftHistory.trace =
      (information setup leaks bounds watcher).infoOf who rightHistory.trace := by
  let responses := menu setup leaks bounds watcher
  let leftPlayers := responses.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) left
  let rightPlayers := responses.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) right
  have different : who ≠ watcher := by
    intro equal
    exact observer event (equal ▸ owned)
  obtain ⟨leftBoundary, leftBoundarySupport, leftState, leftInitial, _leftInitialSupport,
      leftSource, _leftCheckpoint, leftOpportunity, leftDecoded⟩ :=
    owner_supported setup leaks bounds watcher who reveals observer openable left event owned
      leftHistory leftSupport
  obtain ⟨rightBoundary, rightBoundarySupport, rightState, rightInitial, _rightInitialSupport,
      rightSource, _rightCheckpoint, rightOpportunity, rightDecoded⟩ :=
    owner_supported setup leaks bounds watcher who reveals observer openable right event owned
      rightHistory rightSupport
  have leftInfo : (information setup leaks bounds watcher).infoOf who leftHistory.trace =
      some (leftBoundary.recall who,
        (ownerOpportunity setup leaks event who leftBoundary).observe
          (application setup leaks) who) := by
    change (responses.signals _ _ _).infoOf who leftHistory.trace = _
    rw [responses.info, leftState]
    simp only [ReactiveApplication.observe, ↓reduceIte, ownerOpportunity]
  have rightInfo : (information setup leaks bounds watcher).infoOf who rightHistory.trace =
      some (rightBoundary.recall who,
        (ownerOpportunity setup leaks event who rightBoundary).observe
          (application setup leaks) who) := by
    change (responses.signals _ _ _).infoOf who rightHistory.trace = _
    rw [responses.info, rightState]
    simp only [ReactiveApplication.observe, ↓reduceIte, ownerOpportunity]
  have boundarySame : setup.protocolObserve who
      (sourcePrefix? setup event.val leftBoundary.application.config) =
        setup.protocolObserve who
          (sourcePrefix? setup event.val rightBoundary.application.config) := by
    simpa only [leftState, rightState, prefixReadout, ownerOpportunity] using same
  have past : leftBoundary.recall who = rightBoundary.recall who :=
    initialized_focal_recall setup leaks bounds watcher reveals observer openable source
      weight nonnegative atMostOne who different reference leftPlayers rightPlayers selected
      (menu_decode_reports setup leaks bounds watcher left)
      (menu_decode_reports setup leaks bounds watcher right)
      (menu_decode_ordinary setup leaks bounds watcher left)
      (menu_decode_ordinary setup leaks bounds watcher right)
      event.val event.isLt.le leftBoundary rightBoundary leftBoundarySupport rightBoundarySupport
      (congrArg Prod.fst (Option.some.inj (rightInfo.symm.trans referenceInfo))) boundarySame
  have sourceView : ProtocolState.observe who setup.program leftSource =
      ProtocolState.observe who setup.program rightSource := by
    rw [leftDecoded, rightDecoded] at boundarySame
    exact Option.some.inj boundarySame
  have leftLeaks := PrefixCheckpoint.runtime_fact
    (fun execution => execution.network.leaked = fun _ => [])
    (fun _ _ _ _ checkpoint => checkpoint.leaked) _ _ _ _ _ _ _ _ leftOpportunity
  have rightLeaks := PrefixCheckpoint.runtime_fact
    (fun execution => execution.network.leaked = fun _ => [])
    (fun _ _ _ _ checkpoint => checkpoint.leaked) _ _ _ _ _ _ _ _ rightOpportunity
  have beforeView := (PublicPrefixCheckpoint.observe_eq_iff who setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val
    leftSource rightSource _ _
    (PrefixCheckpoint.toPublic _ _ _ _ _ _ _ _ leftOpportunity)
    (PrefixCheckpoint.toPublic _ _ _ _ _ _ _ _ rightOpportunity) rfl
    (by rw [leftLeaks, rightLeaks])).mp sourceView
  rw [leftInfo, rightInfo, past, beforeView]

end Vegas
