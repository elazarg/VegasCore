/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceMenu
import Vegas.Game.ServiceRoster
import Vegas.Pending.ReactiveRepeatedSubmissionWindow

/-! # Stopped repair in the actual post-submission service roster

The player's turn and existing own recall make the required-binding branch
inactive after the first submission. The fixed roster scheduler supplies the
activation-only window; arbitrary raw opponents remain in the exact law.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem recorded_compiled_sourceService
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (serving : view.application.publicView.ownTurn? who = some event)
    (recorded : (runtime setup).eventRecorded leaks past event = true) :
    bounds.compiledActions (runtime setup) leaks who past view ⊆
      (sourceServiceMenu setup leaks bounds rosters).actions who past view := by
  classical
  have optional : ¬ decisionRequired setup leaks rosters who past view := by
    rintro ⟨selected, sameTurn, _, _, unsent, _⟩
    cases Option.some.inj (sameTurn.symm.trans serving)
    rw [recorded] at unsent
    cases unsent
  change _ ⊆ sourceServiceActions setup leaks bounds rosters who past view
  rw [sourceServiceActions, ite_eq_right optional]

omit [Fintype Player] in
theorem roster_activation_segment
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (before after : List (ServiceInstruction (graph setup))) (visits : List Player)
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++ after)
    (execution : (application setup leaks).Execution)
    (lower : before.length ≤ execution.environmentRecall.length)
    (upper : execution.environmentRecall.length < before.length + visits.length)
    (command : (application setup leaks).Command)
    (supported : command ∈ (rosterScheduler setup leaks rosters network execution.environmentRecall
      (execution.observeEnvironment (application setup leaks))).support) :
    ∃ actor, command = .activate actor := by
  have index : execution.environmentRecall.length - before.length < visits.length := by omega
  let actor := visits[execution.environmentRecall.length - before.length]
  have selected : (rosterPlan setup rosters)[execution.environmentRecall.length]? =
      some (.player actor) := by
    rw [split, List.append_assoc, List.getElem?_append_right lower,
      List.getElem?_append_left (by simpa only [List.length_map] using index),
      List.getElem?_map, List.getElem?_eq_getElem index]
    rfl
  simp only [rosterScheduler, selected, interactionInstruction] at supported
  exact ⟨actor, (PMF.mem_support_pure_iff _ _).mp supported⟩

/-- This instantiates the complete stopped window on the existing source
service calendar and retained menu. No menu-coverage or timing certificate is
left to supply: only the actual post-first prefix resources remain. -/
theorem repeated_roster_stopped_coupling
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (owner : Player) (event : (graph setup).EventId)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (application setup leaks))
    (rightRecall : repaired.InputRecall (application setup leaks))
    (serials : original.network.SerialsBeforeNext)
    (repeated : original.network.nextSerial owner ≠
      Message.distinctAuthoredCount original.network.ledger owner)
    (serving : original.application.publicView.ownTurn? owner = some event)
    (recorded : (runtime setup).eventRecorded leaks (repaired.recall owner) event = true)
    (available : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ (bounds.menu (runtime setup) leaks).actions owner past view)
    (before after : List (ServiceInstruction (graph setup))) (visits : List Player)
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++ after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = (runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) original ∧
      coupling.map Prod.snd = strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network) visits.length repaired memory ∧
      ∀ next ∈ coupling.support,
        (∃ record ∈ app.executionTraffic next.1, record.envelope.sender = owner ∧
          (runtime setup).permittedServiceEnvelope record.observation record.ledger
            record.envelope = false) ∨
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow = memory.shadow ∧
          next.2.1.application.playerView owner = repaired.application.playerView owner := by
  obtain ⟨coupling, first, second, related⟩ := frame.run_repeated_stopped_coupling bounds
    (sourceServiceMenu setup leaks bounds rosters) players
    (rosterScheduler setup leaks rosters network) reference started leftRecall rightRecall
    serials repeated event serving recorded
    (recorded_compiled_sourceService setup leaks bounds rosters owner event) available
    before.length visits.length position
    (fun execution lower upper command supported => roster_activation_segment setup leaks
      rosters network before after visits split execution lower upper command supported)
  refine ⟨coupling, ?_, second, related⟩
  rw [first]
  have law := roster_segment_rounds setup leaks rosters network players before
    (visits.map ServiceInstruction.player) after split original position
  simpa only [List.length_map] using law

end Vegas
