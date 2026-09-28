/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceOwnerResponse
import Interaction.ReactiveLocalContinuation

/-! # Local owner laws in the original source continuation

An arbitrary law at one native information site first chooses a physical
response. Its Boolean interpretation then takes one existing source step,
followed by the unchanged source continuation. Replay aliases retain their
native histories; only the resulting terminal-state law is projected.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem owner_choice_ordinary
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (different : who ≠ watcher)
    (history : (protocol setup leaks bounds watcher).History)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (choice : (information setup leaks bounds watcher).Choice who
      ((information setup leaks bounds watcher).infoOf who history.trace)) :
    choice.1.getD ⟨none⟩ ∈ ordinaryActions setup leaks bounds who
      (execution.recall who) (execution.observe (application setup leaks) who) := by
  have observed : (information setup leaks bounds watcher).infoOf who history.trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    change ((menu setup leaks bounds watcher).signals (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).infoOf who history.trace = _
    rw [(menu setup leaks bounds watcher).info, current]
    simp [ReactiveApplication.observe]
  obtain ⟨choice, legal⟩ := choice
  rw [observed] at legal
  obtain ⟨response, allowed, same⟩ := legal
  change choice.getD ⟨none⟩ ∈ _
  rw [same, Option.getD_some]
  simpa only [menu, different, ↓reduceIte] using allowed

open Classical in
theorem owner_local_law_readout
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (source : ProtocolState setup.program) (execution : (application setup leaks).Execution)
    (related : PrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val source execution)
    (granted : execution.application.serviceGrant = some event)
    (position : execution.environmentRecall.length = blockOffset event.val + 2)
    (history : (protocol setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).History)
    (current : history.state =
      some ⟨horizon setup watcher - blockOffset event.val - 2, some who, execution⟩)
    (law : FinDist ((information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).Choice who ((information setup leaks (bounds.withInitialValues (initialLaw setup))
        watcher).infoOf who history.trace)))
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose who) = disclose) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let model := information setup leaks extended watcher
    let compiled := compiledProfile setup leaks extended watcher profile 0 le_rfl (by norm_num)
    (model.runBehavioralFrom
      (Profile.update compiled who ((compiled who).withLaw (model.infoOf who history.trace) law))
      (2 * horizon setup watcher + 1 - history.trace.length) history).map
        (fun final => sourceReadout setup leaks final.state) =
      (law.bind (fun choice =>
        ((ProtocolState.step setup.program source
          (joint (sourceChoice setup leaks (choice.1.getD ⟨none⟩))))).bind
            (ProtocolState.continuationLaw setup.program profile))).map some := by
  intro extended model compiled
  let responses := menu setup leaks extended watcher
  let players := policy setup leaks extended watcher profile 0 le_rfl (by norm_num)
  have different : who ≠ watcher := fun same => observer event (same ▸ owned)
  have reports : players watcher = (application setup leaks).reportFirstUnpublished := by
    simp only [players, policy, ↓reduceIte]
  have ordinary : ∀ player, player ≠ watcher → ∀ past view response,
      response ∈ (players player past view).support → response ∈
        ordinaryActions setup leaks extended player past view := by
    intro player other past view response supported
    simp only [players, policy, other, ↓reduceIte] at supported
    exact ordinaryPolicy_covered setup leaks extended profile 0 le_rfl (by norm_num)
      player past view response supported
  have projects : ∀ player, player ≠ watcher → ∀ past view opening,
      opening? setup leaks player past view = some opening →
      opening ∈ (extended.menu (runtime setup) leaks).actions player past view →
      (players player past view).map (sourceChoice setup leaks) =
        sourceChoiceLaw setup leaks profile player view := by
    intro player other past view opening selected covered
    simp only [players, policy, other, ↓reduceIte]
    exact ordinaryPolicy_projects setup leaks extended profile 0 le_rfl (by norm_num)
      player past view opening selected covered
  let updated := Profile.update (sig := model.behavioralSignature) compiled who
    ((compiled who).withLaw (model.infoOf who history.trace) law)
  let decode (state : (application setup leaks).ProtocolState) :=
    state.bind fun control => decodeState? (terminalRefs setup.program)
      control.execution.application.config.store
  have first := responses.run_local_law_remaining (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) compiled history who
    (horizon setup watcher - blockOffset event.val - 2) execution current law
  rw [decoded_compiledProfile] at first
  change (model.runBehavioralFrom updated
      (2 * horizon setup watcher + 1 - history.trace.length) history).map History.state =
    (law.map (fun choice => choice.1.getD ⟨none⟩)).bind (fun response =>
      (application setup leaks).finish (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) players
          (some ⟨horizon setup watcher - blockOffset event.val - 2, none,
            execution.respond (application setup leaks) who response⟩)) at first
  calc
    _ = (model.runBehavioralFrom updated
        (2 * horizon setup watcher + 1 - history.trace.length) history).map
          (fun final => decode final.state) :=
      remaining_readout_eq_decode setup leaks responses watcher reveals updated history
    _ = ((law.map (fun choice => choice.1.getD ⟨none⟩)).bind (fun response =>
        (application setup leaks).finish (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher) players
            (some ⟨horizon setup watcher - blockOffset event.val - 2, none,
              execution.respond (application setup leaks) who response⟩))).map decode := by
      simpa only [FinDist.map_comp, Function.comp_def] using
        congrArg (fun distribution => distribution.map decode) first
    _ = _ := by
      rw [FinDist.map_bind, FinDist.bind_map, FinDist.map_bind]
      apply FinDist.bind_congr
      intro choice _supported
      exact owner_response_finish_decode_law setup leaks bounds watcher who reveals observer
        profile players reports ordinary projects initial initialSupport event owned source
        execution related granted position (choice.1.getD ⟨none⟩)
        (owner_choice_ordinary setup leaks extended watcher who different history _ execution
          current choice) _ (chosen _)

end Vegas
