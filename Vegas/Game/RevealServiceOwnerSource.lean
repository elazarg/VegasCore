/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceOwnerSupport
import Vegas.Game.SourcePrefixKernel

/-! # Source sites reached by actual restricted owner histories

Every legal restricted prefix supplies a source history through a uniform
source reference. Native full mixing is not used to construct that witness.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The native source-state readout is the state of an actual source
decision history at the corresponding rank, including off-path C histories. -/
theorem owner_source_history
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : Profile (information setup leaks bounds watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (history : (protocol setup leaks bounds watcher).History)
    (supported : history ∈ ((information setup leaks bounds watcher).runBehavioral profile
      (blockOffset event.val + 2 * event.val + 2)).support) :
    ∃ source : (setup.executionProtocol admission).History,
      source ∈ ((setup.informationModel admission).runBehavioral
        (setup.revealReference reveals admission).strategy (event.val + 1)).support ∧
      source.state = prefixReadout setup leaks event.val history.state ∧
      (setup.executionProtocol admission).active source.state who ∧
      ¬ (setup.executionProtocol admission).terminal source.state := by
  let players := (menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher) profile
  obtain ⟨boundary, boundarySupport, nativeState, _initial, _initialSupport,
      _source, _boundaryCheckpoint, _opportunityCheckpoint, _decoded⟩ :=
    owner_supported setup leaks bounds watcher who reveals observer openable profile event owned
      history supported
  obtain ⟨initial, initialSupport, state, related, decoded, _priorView, sourceReach⟩ :=
    initialized_prefix_support setup leaks bounds watcher reveals observer openable players
      (menu_decode_reports setup leaks bounds watcher profile)
      (menu_decode_ordinary setup leaks bounds watcher profile)
      event.val event.isLt.le boundary boundarySupport
  obtain ⟨source, sourceSupport, sourceState⟩ := setup.exists_history_of_prefix_support admission
    (fun player => RevealOnly.uniformPolicy player setup.program reveals)
    (fun player => RevealOnly.uniformPolicy_admitted player setup.program reveals admission)
    initial initialSupport event.val state sourceReach
  have acting := PublicPrefixCheckpoint.actor who setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state boundary
    (related.toPublic _ _ _ _ _ _ _ _) event.isLt
  rw [eventOwner?_eq_actor] at acting
  change ProtocolView.actor who setup.program (ProtocolState.observe who setup.program state) =
    (graph setup).actor? event at acting
  rw [owned] at acting
  refine ⟨source, sourceSupport, ?_, ?_, ?_⟩
  · simpa only [nativeState, prefixReadout, ownerOpportunity, decoded] using sourceState
  · rw [sourceState]
    exact acting
  · rw [sourceState]
    intro stopped
    have absent := ProtocolState.terminal_actor_none who setup.program state stopped
    rw [acting] at absent
    cases absent

/-- The decoded observation is an actual source information site, so source
full mixing applies to its Boolean choices without a native-mixing premise. -/
theorem owner_source_site
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : Profile (information setup leaks bounds watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (history : (protocol setup leaks bounds watcher).History)
    (supported : history ∈ ((information setup leaks bounds watcher).runBehavioral profile
      (blockOffset event.val + 2 * event.val + 2)).support) :
    ∃ site : (setup.informationModel admission).InformationSite who,
      site.1 = setup.protocolObserve who (prefixReadout setup leaks event.val history.state) := by
  obtain ⟨source, _sourceSupport, same, active, running⟩ :=
    owner_source_history setup leaks bounds watcher who reveals observer openable admission
      profile event owned history supported
  obtain ⟨joint, legal⟩ := source.exists_legal_of_not_terminal running
  obtain ⟨action, chosen⟩ :=
    ((setup.executionProtocol admission).legalOption_of_legal legal who).exists_eq_some_of_active
      (joint who) active
  have allowed : some action ∈ (setup.informationModel admission).menu who
      ((setup.informationModel admission).infoOf who source.trace) := by
    apply ((setup.informationModel admission).menu_adequate who source.trace (some action)).mpr
    have admittedChoice := (setup.executionProtocol admission).legalOption_of_legal legal who
    rw [chosen] at admittedChoice
    exact admittedChoice
  refine ⟨(setup.informationModel admission).informationSite who source action running allowed, ?_⟩
  change (setup.informationModel admission).infoOf who source.trace = _
  exact (setup.protocol_info admission who source.trace).trans
    (congrArg (setup.protocolObserve who) same)

end Vegas
