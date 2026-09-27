/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceOwnerLocalLaw

/-! # Owner continuation values at every restricted native site

The operational checkpoint and the typed source state are recovered from an
actual native history. Averaging the local response law therefore uses the
actual source-state posterior; no correspondence of information fibers is an
assumption of the value equation.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

open Classical in
theorem owner_history_local_readout
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : BehavioralProfile setup.program)
    (reference : Profile (information setup leaks
      (bounds.withInitialValues (initialLaw setup)) watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (history : (protocol setup leaks (bounds.withInitialValues (initialLaw setup)) watcher).History)
    (supported : history ∈ ((information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).runBehavioral reference (blockOffset event.val + 2 * event.val + 3)).support)
    {info : (application setup leaks).Info}
    (observed : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).infoOf who history.trace = info)
    (law : FinDist ((information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).Choice who info))
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose who) = disclose) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let model := information setup leaks extended watcher
    let compiled := compiledProfile setup leaks extended watcher profile 0 le_rfl (by norm_num)
    (model.runBehavioralFrom
      (Profile.update compiled who ((compiled who).withLaw info law))
      (2 * horizon setup watcher + 1 - history.trace.length) history).map
        (fun final => sourceReadout setup leaks final.state) =
      law.bind (fun choice =>
        ((setup.protocolStep (prefixReadout setup leaks event.val history.state)
          (joint (sourceChoice setup leaks (choice.1.getD ⟨none⟩)))).bind
            (setup.continuationLaw profile)).map some) := by
  cases observed
  intro extended model compiled
  obtain ⟨boundary, boundarySupport, nativeState, initial, initialSupport, source,
      _beforeCheckpoint, related, decoded⟩ :=
    owner_supported setup leaks extended watcher who reveals observer openable reference
      event owned history supported
  have position : boundary.environmentRecall.length = blockOffset event.val := by
    rw [FinDist.support_bind] at boundarySupport
    obtain ⟨nativeInitial, _initialSupport, reached⟩ := Set.mem_iUnion₂.mp boundarySupport
    have count := (runtime setup).runInteractionPlan_recall leaks
      ((menu setup leaks extended watcher).decodeProfile (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) reference)
      ((runtime setup).reportNetwork leaks watcher) (planPrefix setup watcher event.val)
      (ReactiveApplication.Execution.initial (application setup leaks) nativeInitial)
      boundary reached
    simpa only [ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add,
      planPrefix_length setup watcher reveals event.val event.isLt.le] using count
  have opportunityPosition :
      (ownerOpportunity setup leaks event who boundary).environmentRecall.length =
        blockOffset event.val + 2 := by
    simp only [ownerOpportunity, List.length_append, List.length_cons, List.length_nil, position]
  have value := owner_local_law_readout setup leaks bounds watcher who reveals observer profile
    initial initialSupport event owned source (ownerOpportunity setup leaks event who boundary)
    related rfl opportunityPosition history nativeState law joint chosen
  have read : prefixReadout setup leaks event.val history.state = some source := by
    simpa only [nativeState, prefixReadout, ownerOpportunity] using decoded
  rw [read]
  simpa only [Setup.protocolStep, FinDist.bind_map, Setup.continuationLaw,
    FinDist.map_bind] using value

open Classical in
theorem owner_context_local_value
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : BehavioralProfile setup.program)
    (assessment : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).BehavioralAssessment)
    (strategy : assessment.strategy = compiledProfile setup leaks
      (bounds.withInitialValues (initialLaw setup)) watcher profile 0 le_rfl (by norm_num))
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (site : (information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).InformationSite who)
    (clock : InformationModel.InformationSite.CommonDepth
      (information setup leaks (bounds.withInitialValues (initialLaw setup)) watcher) site
        (blockOffset event.val + 2 * event.val + 3))
    (law : FinDist ((information setup leaks (bounds.withInitialValues (initialLaw setup))
      watcher).Choice who site.1))
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose who) = disclose)
    (utility : State L setup.program.terminalCtx → ℝ) :
    (assessment.continuationContext site
      (fun final => (sourceReadout setup leaks final.state).elim 0 utility)
      (2 * horizon setup watcher + 1 - (blockOffset event.val + 2 * event.val + 3))).value
        ((assessment.strategy who).withLaw site.1 law) =
      ((assessment.belief who site).map
        (fun current => prefixReadout setup leaks event.val current.1.state)).expect
          (fun state => law.expect fun choice =>
            ((setup.protocolStep state
              (joint (sourceChoice setup leaks (choice.1.getD ⟨none⟩)))).bind
                (setup.continuationLaw profile)).expect utility) := by
  let extended := bounds.withInitialValues (initialLaw setup)
  let responses := menu setup leaks extended watcher
  let model := information setup leaks extended watcher
  let reference := responses.uniformPolicy (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.expect_bind, FinDist.expect_map]
  apply FinDist.expect_congr
  intro history _supported
  have reached : history.1 ∈ (model.runBehavioral reference
      (blockOffset event.val + 2 * event.val + 3)).support := by
    have result := (responses.uniform_fullyMixed (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).history_supported history.1.trace
    simpa only [clock history, ReactiveApplication.ResponseMenu.uniformAssessment,
      InformationModel.BehavioralAssessment.ofStrategy] using result
  have equality := owner_history_local_readout setup leaks bounds watcher who reveals observer
    openable profile reference event owned history.1 reached history.2 law joint chosen
  have value := congrArg (fun distribution => distribution.expect
    (fun result => result.elim 0 utility)) equality
  rw [strategy]
  simpa only [FinDist.expect_map, FinDist.expect_bind, Option.elim_some, clock history] using value

end Vegas.SourceProgram.RevealService
