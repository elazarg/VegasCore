/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefixEnforcement
import Vegas.Game.RevealServiceOwnerSupport

/-! # Conditional collection at every retained owner history

The actual C support theorem supplies a clean source checkpoint at each owner
decision. Compiler node alignment and packet classification then establish the
existing collection bound against every watched continuation. The observation
assumption below is deliberately stronger than a bound only on reachable
bounded pools: every foreign pending envelope is sampled with the stated rate.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

open Classical in
theorem owner_extra_collection
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : Profile (watchedInformation setup leaks bounds watcher).behavioralSignature)
    (who : Player) (different : who ≠ watcher)
    (site : (information setup leaks bounds watcher).InformationSite who)
    (action : (watchedInformation setup leaks bounds watcher).Choice who
      ((ordinaryRestriction setup leaks bounds watcher).site who site).1)
    (extra : action ∉ Set.range ((ordinaryRestriction setup leaks bounds watcher).choice
      who site.1))
    (history : (information setup leaks bounds watcher).InformationHistory who site.1)
    (probability : Player → ℝ)
    (sampling : ∀ owner, owner ≠ watcher →
      ∀ (pending : List (Message Player (WitnessedPacket (graph setup)))) message,
        message ∈ pending → message.id.1 = owner →
        probability owner ≤ (leaks watcher pending).probOf {selected | message.id ∈ selected})
    (fuel : Nat) (enough : 2 * horizon setup watcher + 1 - history.1.trace.length ≤ fuel) :
    probability who ≤ ((watchedInformation setup leaks bounds watcher).runBehavioralFrom
      (Profile.update (sig := (watchedInformation setup leaks bounds watcher).behavioralSignature)
        profile who ((profile who).commit
          ((ordinaryRestriction setup leaks bounds watcher).site who site).1 action))
      fuel ((ordinaryRestriction setup leaks bounds watcher).history history.1)).probOf
        {final | departureAtState setup leaks who final.state} := by
  let responses := menu setup leaks bounds watcher
  let restriction := ordinaryRestriction setup leaks bounds watcher
  let reference := responses.uniformPolicy (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)
  have active := InformationModel.InformationSite.active
    (information setup leaks bounds watcher) site history
  obtain ⟨event, owned, _length, supported⟩ := owner_history_supported setup leaks bounds
    watcher who reveals different history.1 active
  obtain ⟨boundary, _boundarySupport, nativeState, initial, _initialSupport, source,
      _boundaryCheckpoint, related, _decoded⟩ :=
    owner_supported setup leaks bounds watcher who reveals observer openable reference
      event owned history.1 supported
  let execution := ownerOpportunity setup leaks event who boundary
  let control : (application setup leaks).Control :=
    ⟨horizon setup watcher - blockOffset event.val - 2, some who, execution⟩
  have current : history.1.state = some control := nativeState
  have observed : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who) := by
    calc
      site.1 = (information setup leaks bounds watcher).infoOf who history.1.trace := history.2.symm
      _ = (application setup leaks).observe who history.1.state :=
        responses.info (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher) who history.1.trace
      _ = _ := by rw [current]; simp only [ReactiveApplication.observe, control, ↓reduceIte]
  obtain ⟨response, chosen, effective, excluded⟩ := extra_choice_response setup leaks bounds
    watcher who different site _ _ observed action extra
  obtain ⟨submission, same, departure⟩ := prefix_extra_submission setup leaks bounds who reveals
    initial event owned source execution related rfl response effective excluded
  have chosenSubmission : action.1 = some ⟨some (.submit submission)⟩ := by rw [chosen, same]
  have serials : execution.network.SerialsBeforeNext :=
    PrefixCheckpoint.runtime_fact (fun current => current.network.SerialsBeforeNext)
      (fun _ _ _ _ checkpoint => checkpoint.serials) _ _ _ _ _ _ _ _ related
  have pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id :=
    PrefixCheckpoint.runtime_fact (fun current => ∀ message ∈ current.network.pending,
      message.id ∈ current.network.ledger.map Message.id)
      (fun _ _ _ _ checkpoint => checkpoint.pending) _ _ _ _ _ _ _ _ related
  have known : ∀ message ∈ execution.network.known watcher,
      message.id ∈ execution.network.ledger.map Message.id :=
    PrefixCheckpoint.runtime_fact (fun current => ∀ message ∈ current.network.known watcher,
      message.id ∈ current.network.ledger.map Message.id)
      (fun _ _ _ _ checkpoint => checkpoint.known_published watcher) _ _ _ _ _ _ _ _ related
  have collected := watched_commit_collection setup leaks bounds watcher who different reveals
    profile (restriction.site who site) (restriction.informationHistory who site history)
    control current event rfl submission action chosenSubmission serials pending known departure
    fuel (by
      change 2 * horizon setup watcher + 1 -
        (restriction.history history.1).trace.length ≤ fuel
      rw [restriction.length]
      exact enough)
  let state := (application setup leaks).submit execution.application who submission
  let packet := submission.emit state who (execution.network.known who)
  let message : Message Player (application setup leaks).Payload :=
    ⟨(who, execution.network.nextSerial who), packet⟩
  let submitted := execution.respond (application setup leaks) who ⟨some (.submit submission)⟩
  have present : message ∈ submitted.network.pending := by
    change message ∈ execution.network.pending ++ [message]
    simp only [List.mem_append, List.mem_singleton, or_true]
  exact (sampling who different submitted.network.pending message present rfl).trans collected

end Vegas
