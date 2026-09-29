/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceCheckpoint
import Vegas.Game.RevealServicePayoffs

/-! # Enforcement at retained ordinary information histories

The existing checkpoint relation supplies the actual clean network, initial
binding meanings, and ready current reveal. Every additional watched response
therefore incurs the checked collection risk in its behavioral continuation.
Compiler node alignment and the checkpoint premise are explicit; the global
source-history induction supplies them independently of equilibrium choices.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

theorem extra_choice_response (watcher owner : Player) (different : owner ≠ watcher)
    (site : (information setup leaks bounds watcher).InformationSite owner)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (observed : site.1 = some (past, view))
    (action : (watchedInformation setup leaks bounds watcher).Choice owner
      ((ordinaryRestriction setup leaks bounds watcher).site owner site).1)
    (extra : action ∉ Set.range ((ordinaryRestriction setup leaks bounds watcher).choice
      owner site.1)) :
    ∃ response, action.1 = some response ∧
      response ∈ (bounds.menu (runtime setup) leaks).actions owner past view ∧
      response ∉ ordinaryActions setup leaks bounds owner past view := by
  rcases site with ⟨info, occurs⟩
  dsimp only at observed
  subst info
  obtain ⟨response, allowed, same⟩ := action.2
  have effective : response ∈ (bounds.menu (runtime setup) leaks).actions owner past view := by
    simpa only [watchedMenu, different, ↓reduceIte] using allowed
  refine ⟨response, same, effective, ?_⟩
  intro ordinary
  let source : (information setup leaks bounds watcher).Choice owner (some (past, view)) :=
    ⟨some response, response, by simpa only [menu, different, ↓reduceIte] using ordinary, rfl⟩
  exact extra ⟨source, Subtype.ext same.symm⟩

/-- A retained checkpoint discharges every operational packet-classification
premise. All extra effective responses allocate attributable fresh envelopes. -/
theorem checkpoint_extra_submission
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (execution : (application setup leaks).Execution)
    (checkpoint : Checkpoint setup leaks initial source refs rank execution)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (ownedEvent : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (granted : execution.application.serviceGrant = some event)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions owner
      (execution.recall owner) (execution.observe (application setup leaks) owner))
    (extra : response ∉ ordinaryActions setup leaks bounds owner (execution.recall owner)
      (execution.observe (application setup leaks) owner)) :
    ∃ submission, response = ⟨some (.submit submission)⟩ ∧
      let state := (application setup leaks).submit execution.application owner submission
      let packet := submission.emit state owner (execution.network.known owner)
      (application setup leaks).handle state
          ⟨(owner, execution.network.nextSerial owner), packet⟩ = none ∨
        certifiedOpening packet = false := by
  obtain ⟨value, bound⟩ := checkpoint.openable selected
  obtain ⟨candidate, associated, owned, fixed, opening⟩ := opening_at_checkpoint setup leaks
    selected source.state refs execution checkpoint.agrees checkpoint.binding event ownedEvent
      outputEq codeEq node granted value bound
  have ready : execution.application.config.cut.Ready event := by
    have inside : rank < (graph setup).order.eventCount := eventRank ▸ event.isLt
    have same : (⟨rank, inside⟩ : (graph setup).EventId) = event := Fin.ext eventRank.symm
    rw [← same]
    exact checkpoint.ordered.ready inside
  exact extra_response_packet_cases setup leaks bounds execution owner checkpoint.recall
    (checkpoint.known_published owner) event payload (refs.get selected) [] outputEq codeEq node
    ready candidate ⟨payload, value⟩ associated owned fixed opening response effective extra

open Classical in
/-- Collection at every hidden retained information history, for every extra
watched action and arbitrary later watched play. The single checkpoint premise
is operational and independent of any strategy or belief. -/
theorem ordinary_extra_collection (watcher owner : Player) (different : owner ≠ watcher)
    (reveals : setup.program.RevealOnly)
    (profile : Profile (watchedInformation setup leaks bounds watcher).behavioralSignature)
    (site : (information setup leaks bounds watcher).InformationSite owner)
    (history : (information setup leaks bounds watcher).InformationHistory owner site.1)
    (control : (application setup leaks).Control) (state : history.1.state = some control)
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (checkpoint : Checkpoint setup leaks initial source refs rank control.execution)
    {name : VarId} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (ownedEvent : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (granted : control.execution.application.serviceGrant = some event)
    (action : (watchedInformation setup leaks bounds watcher).Choice owner
      ((ordinaryRestriction setup leaks bounds watcher).site owner site).1)
    (extra : action ∉ Set.range ((ordinaryRestriction setup leaks bounds watcher).choice
      owner site.1))
    (probability : ℝ)
    (sampling : ∀ submission : WitnessedSubmission (graph setup),
      (⟨some (.submit submission)⟩ : (application setup leaks).Action) ∈
        (bounds.menu (runtime setup) leaks).actions owner (control.execution.recall owner)
          (control.execution.observe (application setup leaks) owner) →
      (⟨some (.submit submission)⟩ : (application setup leaks).Action) ∉
        ordinaryActions setup leaks bounds owner (control.execution.recall owner)
          (control.execution.observe (application setup leaks) owner) →
      probability ≤ ((leaks watcher
        (control.execution.respond (application setup leaks) owner
          ⟨some (.submit submission)⟩).network.pending).toOuterMeasure {selected | (owner, control.execution.network.nextSerial owner) ∈ selected}).toReal)
    (fuel : Nat) (enough : 2 * horizon setup watcher + 1 - history.1.trace.length ≤ fuel) :
    probability ≤ (((watchedInformation setup leaks bounds watcher).runBehavioralFrom
      (Profile.update (sig := (watchedInformation setup leaks bounds watcher).behavioralSignature)
        profile owner ((profile owner).commit
          ((ordinaryRestriction setup leaks bounds watcher).site owner site).1 action))
      fuel ((ordinaryRestriction setup leaks bounds watcher).history history.1)).toOuterMeasure {final | departureAtState setup leaks owner final.state}).toReal := by
  classical
  let restriction := ordinaryRestriction setup leaks bounds watcher
  have active := InformationModel.InformationSite.active
    (information setup leaks bounds watcher) site history
  change (application setup leaks).actor history.1.state = some owner at active
  rw [state] at active
  change control.actor = some owner at active
  have observed : site.1 = some (control.execution.recall owner,
      control.execution.observe (application setup leaks) owner) := by
    calc
      site.1 = (information setup leaks bounds watcher).infoOf owner history.1.trace :=
        history.2.symm
      _ = (application setup leaks).observe owner history.1.state :=
        (menu setup leaks bounds watcher).info (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher) owner history.1.trace
      _ = _ := by rw [state]; simp only [ReactiveApplication.observe, active, ↓reduceIte]
  obtain ⟨response, chosen, effective, excluded⟩ := extra_choice_response setup leaks bounds
    watcher owner different site _ _ observed action extra
  obtain ⟨submission, same, departure⟩ := checkpoint_extra_submission setup leaks bounds
    source refs rank control.execution checkpoint selected event eventRank ownedEvent outputEq
    codeEq node granted response effective excluded
  have chosenSubmission : action.1 = some ⟨some (.submit submission)⟩ := by rw [chosen, same]
  have collected := watched_commit_collection setup leaks bounds watcher owner different reveals
    profile (restriction.site owner site) (restriction.informationHistory owner site history)
    control state event granted submission action chosenSubmission checkpoint.serials
    checkpoint.pending (checkpoint.known_published watcher) departure fuel (by
      change 2 * horizon setup watcher + 1 -
        (restriction.history history.1).trace.length ≤ fuel
      rw [restriction.length]
      exact enough)
  exact (sampling submission (same ▸ effective) (same ▸ excluded)).trans collected

open Classical in
/-- The pointwise inequality required by the restriction theorem. The target
continuation is arbitrary and the legal continuation may use any C profile,
including future withholding. The source transcript induction supplies its
cleanliness; the finite payoff carrier supplies the two payoff bounds. -/
theorem ordinary_extra_comparison (watcher owner : Player) (different : owner ≠ watcher)
    (reveals : setup.program.RevealOnly)
    (legalProfile : Profile (information setup leaks bounds watcher).behavioralSignature)
    (targetProfile : Profile (watchedInformation setup leaks bounds watcher).behavioralSignature)
    (site : (information setup leaks bounds watcher).InformationSite owner)
    (history : (information setup leaks bounds watcher).InformationHistory owner site.1)
    (control : (application setup leaks).Control) (state : history.1.state = some control)
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (checkpoint : Checkpoint setup leaks initial source refs rank control.execution)
    {name : VarId} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (ownedEvent : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq)
    (granted : control.execution.application.serviceGrant = some event)
    (action : (watchedInformation setup leaks bounds watcher).Choice owner
      ((ordinaryRestriction setup leaks bounds watcher).site owner site).1)
    (extra : action ∉ Set.range ((ordinaryRestriction setup leaks bounds watcher).choice
      owner site.1))
    (probability : ℝ)
    (sampling : ∀ submission : WitnessedSubmission (graph setup),
      (⟨some (.submit submission)⟩ : (application setup leaks).Action) ∈
        (bounds.menu (runtime setup) leaks).actions owner (control.execution.recall owner)
          (control.execution.observe (application setup leaks) owner) →
      (⟨some (.submit submission)⟩ : (application setup leaks).Action) ∉
        ordinaryActions setup leaks bounds owner (control.execution.recall owner)
          (control.execution.observe (application setup leaks) owner) →
      probability ≤ ((leaks watcher
        (control.execution.respond (application setup leaks) owner
          ⟨some (.submit submission)⟩).network.pending).toOuterMeasure {selected | (owner, control.execution.network.nextSerial owner) ∈ selected}).toReal)
    (base : (application setup leaks).ProtocolState → Player → ℝ) (deposit : Player → ℝ)
    (nonnegative : 0 ≤ deposit owner) (lower upper : ℝ)
    (above : ∀ final : ((watchedMenu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History,
        base final.state owner ≤ upper)
    (below : ∀ final : ((menu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History,
        lower ≤ base final.state owner)
    (sufficient : upper - lower ≤ probability * deposit owner)
    (fuel : Nat) (enough : 2 * horizon setup watcher + 1 - history.1.trace.length ≤ fuel)
    (clean : ∀ final ∈ ((information setup leaks bounds watcher).runBehavioralFrom
      legalProfile fuel history.1).support, ¬ departureAtState setup leaks owner final.state) :
    expect ((watchedInformation setup leaks bounds watcher).runBehavioralFrom
      (Profile.update (sig := (watchedInformation setup leaks bounds watcher).behavioralSignature)
        targetProfile owner ((targetProfile owner).commit
          ((ordinaryRestriction setup leaks bounds watcher).site owner site).1 action))
      fuel ((ordinaryRestriction setup leaks bounds watcher).history history.1))
        (fun final => netUtility setup leaks watcher base deposit final.state owner) ≤
      expect ((information setup leaks bounds watcher).runBehavioralFrom
        legalProfile fuel history.1)
        (fun final => netUtility setup leaks watcher base deposit final.state owner) := by
  let targetLaw := (watchedInformation setup leaks bounds watcher).runBehavioralFrom
    (Profile.update (sig := (watchedInformation setup leaks bounds watcher).behavioralSignature)
      targetProfile owner ((targetProfile owner).commit
        ((ordinaryRestriction setup leaks bounds watcher).site owner site).1 action))
    fuel ((ordinaryRestriction setup leaks bounds watcher).history history.1)
  let legalLaw := (information setup leaks bounds watcher).runBehavioralFrom legalProfile fuel
    history.1
  have collected := ordinary_extra_collection setup leaks bounds watcher owner different reveals
    targetProfile site history control state source refs rank checkpoint selected event eventRank
    ownedEvent outputEq codeEq node granted action extra probability sampling fuel enough
  have compared := netUtility_comparison setup leaks watcher owner different base deposit
    nonnegative (targetLaw.map History.state) (legalLaw.map History.state) lower upper probability
    (by
      intro final supported
      obtain ⟨reached, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact above reached)
    (by
      intro final supported
      obtain ⟨reached, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact below reached)
    (by
      intro final supported
      obtain ⟨reached, member, rfl⟩ := PMF.support_map .. ▸ supported
      exact clean reached member)
    (by rw [FinDist.probOf_map]; exact collected) sufficient
  simpa only [expect_map] using compared

end Vegas
