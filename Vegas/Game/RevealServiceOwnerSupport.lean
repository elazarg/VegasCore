/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceOwnerPrefix
import Vegas.Game.RevealServicePrefixInformation
import Interaction.ReactiveFiniteAssessment

/-! # Actual restricted owner histories

An owner opportunity is the existing activation update. Every
supported owner history comes from a supported source-boundary execution;
the update preserves the decoded source state and the entire private recall.
No compiled-profile or positive-probability assumption on source play is used.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The literal endpoint of the passive owner activation command, when all
pending envelopes are already published. -/
def ownerOpportunity (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player)
    (execution : (application setup leaks).Execution) : (application setup leaks).Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
    [⟨execution.observeEnvironment (application setup leaks), .activate owner⟩] }

omit [Fintype Player] in
theorem PrefixCheckpoint.ownerOpportunity
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    {refs : ContextRefs (graph setup).layout Γ} {revelations : Revelations Γ}
    {outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event)}
    {offset count : Nat} {state : ProtocolState program}
    {execution : (application setup leaks).Execution}
    (related : PrefixCheckpoint setup leaks initial program refs revelations outputs
      offset count state execution) (owner : Player) :
    PrefixCheckpoint setup leaks initial program refs revelations outputs offset count state
      (ownerOpportunity setup leaks owner execution) := by
  apply PrefixCheckpoint.map_execution execution _ _ program refs revelations outputs
    offset count state related
  intro Γ source refs rank checkpoint
  exact { checkpoint with
    invariant := checkpoint.invariant.copy rfl rfl rfl
    binding := checkpoint.binding.copy rfl rfl rfl }

theorem menu_decode_silent (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (profile : Profile (information setup leaks bounds watcher).behavioralSignature) :
    (menu setup leaks bounds watcher).decodeProfile (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) profile watcher =
        (application setup leaks).silentPolicy := by
  funext past view
  apply pmf_eq_pure_of_support_subset_singleton
  intro response supported
  have allowed := (menu setup leaks bounds watcher).decode_embedPolicy_covered
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
    watcher (profile watcher) past view response supported
  simpa only [menu, ↓reduceIte, Finset.mem_singleton, Set.mem_singleton_iff] using allowed

theorem menu_decode_ordinary (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (profile : Profile (information setup leaks bounds watcher).behavioralSignature)
    (who : Player) (different : who ≠ watcher)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (response : (application setup leaks).Action)
    (supported : response ∈ ((menu setup leaks bounds watcher).decodeProfile
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
      profile who past view).support) :
    response ∈ ordinaryActions setup leaks bounds who past view := by
  have allowed := (menu setup leaks bounds watcher).decode_embedPolicy_covered
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
    who (profile who) past view response supported
  simpa only [menu, different, ↓reduceIte] using allowed

omit [Fintype Player] in
private theorem activate_state
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (watcher owner : Player) (players : Player → (application setup leaks).Policy)
    (remaining cursor : Nat)
    (execution : (application setup leaks).Execution)
    (pending : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
    (position : execution.environmentRecall.length = cursor)
    (ownerAt : (plan setup watcher)[cursor]? = some (.player owner)) :
    (fun law => law.bind ((application setup leaks).controlStep (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) players))^[1]
        (PMF.pure (some ⟨remaining + 1, none, execution⟩)) =
      PMF.pure (some ⟨remaining, some owner,
        ownerOpportunity setup leaks owner execution⟩) := by
  let app := application setup leaks
  have scheduled : (scheduler setup leaks watcher) execution.environmentRecall
      (execution.observeEnvironment app) = PMF.pure (.activate owner) := by
    simp only [scheduler, position, ownerAt, interactionInstruction]
  have one : app.controlStep (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) players (some ⟨remaining + 1, none, execution⟩) =
      PMF.pure (some ⟨remaining, some owner,
        ownerOpportunity setup leaks owner execution⟩) := by
    change ((scheduler setup leaks watcher) execution.environmentRecall
      (execution.observeEnvironment app)).bind _ = _
    rw [scheduled, PMF.pure_bind,
      execution.activate_of_pending_published app owner pending, PMF.pure_map]
    rfl
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, PMF.pure_bind]
  rw [one]

/-- Every supported C owner history retains a concrete boundary execution
and its source checkpoint. This quantifies over arbitrary C policies. -/
theorem owner_supported
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher owner : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (profile : Profile (information setup leaks bounds watcher).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (history : (protocol setup leaks bounds watcher).History)
    (supported : history ∈ ((information setup leaks bounds watcher).runBehavioral profile
      (blockOffset event.val + 2 * event.val + 2)).support) :
    let players := (menu setup leaks bounds watcher).decodeProfile (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) profile
    ∃ boundary : (application setup leaks).Execution,
      boundary ∈ ((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks players
          ((runtime setup).idleNetwork leaks) (planPrefix setup watcher event.val)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).support ∧
      history.state = some ⟨horizon setup watcher - blockOffset event.val - 1, some owner,
        ownerOpportunity setup leaks owner boundary⟩ ∧
      ∃ initial ∈ setup.initialLaw.support, ∃ source,
        PrefixCheckpoint setup leaks initial setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (Revelations.initial setup.context) (outputRef setup.program) 0 event.val
          source boundary ∧
        PrefixCheckpoint setup leaks initial setup.program
          (ContextRefs.initial setup.context (outputLayout setup.program))
          (Revelations.initial setup.context) (outputRef setup.program) 0 event.val
          source (ownerOpportunity setup leaks owner boundary) ∧
        sourcePrefix? setup event.val boundary.application.config = some source := by
  let responses := menu setup leaks bounds watcher
  let model := information setup leaks bounds watcher
  let players := responses.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) profile
  let depth := blockOffset event.val + 2 * event.val + 1
  change history ∈ (model.runBehavioral profile (depth + 1)).support at supported
  rw [InformationModel.runBehavioral, InformationModel.runBehavioralFrom_add,
    PMF.support_bind] at supported
  obtain ⟨before, beforeSupport, continued⟩ := Set.mem_iUnion₂.mp supported
  have prefixes := menu_prefix_state setup leaks responses watcher reveals profile event.val
    event.isLt.le
  have seen : before.state ∈
      ((model.runBehavioral profile depth).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨before, beforeSupport, rfl⟩
  rw [prefixes, PMF.support_bind] at seen
  obtain ⟨initialNative, nativeSupport, reached⟩ := Set.mem_iUnion₂.mp seen
  obtain ⟨boundary, executed, stateEq⟩ := PMF.support_map .. ▸ reached
  have boundarySupport : boundary ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players ((runtime setup).idleNetwork leaks)
        (planPrefix setup watcher event.val)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support := by
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initialNative, nativeSupport, executed⟩
  obtain ⟨initial, initialSupport, source, checkpoint, decoded, _priorView⟩ :=
    initialized_prefix_support setup leaks bounds watcher reveals observer openable players
      (menu_decode_silent setup leaks bounds watcher profile)
      (menu_decode_ordinary setup leaks bounds watcher profile)
      event.val event.isLt.le boundary boundarySupport
  have pending : ∀ message ∈ boundary.network.pending,
      message.id ∈ boundary.network.ledger.map Message.id :=
    PrefixCheckpoint.runtime_fact (fun execution => ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id)
      (fun _ _ _ _ checked => checked.pending) _ _ _ _ _ _ _ _ checkpoint
  obtain ⟨rest, planEq⟩ := plan_split_at setup watcher event
  have prefixLength := planPrefix_length setup watcher reveals event.val event.isLt.le
  have ownerAt : (plan setup watcher)[blockOffset event.val]? = some (.player owner) := by
    rw [planEq, List.append_assoc, List.getElem?_append_right (by omega), prefixLength,
      Nat.sub_self, block_of_owner setup watcher owner event owned]
    rfl
  have room : 1 ≤ horizon setup watcher - blockOffset event.val := by
    have lengths := congrArg List.length planEq
    rw [List.length_append, List.length_append, prefixLength,
      block_length setup watcher reveals] at lengths
    change (plan setup watcher).length - blockOffset event.val ≥ 1
    omega
  have position : boundary.environmentRecall.length = blockOffset event.val := by
    have counted := (runtime setup).runInteractionPlan_recall leaks players
      ((runtime setup).idleNetwork leaks) (planPrefix setup watcher event.val)
      (ReactiveApplication.Execution.initial (application setup leaks) initialNative)
      boundary executed
    simpa only [ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add,
      prefixLength] using counted
  have stateSupport : history.state ∈
      ((model.runBehavioralFrom profile 1 before).map History.state).support := by
    rw [PMF.support_map]
    exact ⟨history, continued, rfl⟩
  rw [menu_run_control_steps, ← stateEq] at stateSupport
  have remaining : horizon setup watcher - blockOffset event.val =
      (horizon setup watcher - blockOffset event.val - 1) + 1 := by omega
  rw [remaining] at stateSupport
  have law := activate_state setup leaks watcher owner players
    (horizon setup watcher - blockOffset event.val - 1) (blockOffset event.val)
    boundary pending position ownerAt
  change history.state ∈ ((fun law => law.bind ((application setup leaks).controlStep
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher) players))^[1]
      (PMF.pure (some ⟨(horizon setup watcher - blockOffset event.val - 1) + 1,
        none, boundary⟩))).support at stateSupport
  rw [law, PMF.mem_support_pure_iff _ _] at stateSupport
  exact ⟨boundary, boundarySupport, stateSupport, initial, initialSupport, source,
    checkpoint, checkpoint.ownerOpportunity owner, decoded⟩

/-- Every actual ordinary decision has a declared source rank and occurs
with positive probability under the finite menu's uniform reference. This
reference exists independently of any source-to-C preservation argument. -/
theorem owner_history_supported
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher owner : Player)
    (reveals : setup.program.RevealOnly) (ordinary : owner ≠ watcher)
    (history : (protocol setup leaks bounds watcher).History)
    (active : (protocol setup leaks bounds watcher).active history.state owner) :
    ∃ event : (graph setup).EventId, (graph setup).actor? event = some owner ∧
      history.trace.length = blockOffset event.val + 2 * event.val + 2 ∧
      history ∈ ((information setup leaks bounds watcher).runBehavioral
        ((menu setup leaks bounds watcher).uniformPolicy (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher))
        (blockOffset event.val + 2 * event.val + 2)).support := by
  let responses := menu setup leaks bounds watcher
  have supported := (responses.uniform_fullyMixed (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)).history_supported history.trace
  rcases history with ⟨state, trace⟩
  cases state with
  | none => cases active
  | some control =>
      change control.actor = some owner at active
      let rawTrace := responses.toRawTrace (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) trace
      obtain ⟨event, located⟩ := raw_decision_calendar setup leaks watcher owner
        reveals control rawTrace active
      rcases located with ⟨position, owned⟩ | ⟨_position, same⟩
      · have depth := raw_owner_decision_depth setup leaks watcher owner reveals event owned
          control rawTrace active position
        rw [responses.toRawTrace_length] at depth
        refine ⟨event, owned, depth, ?_⟩
        simpa only [depth, ReactiveApplication.ResponseMenu.uniformAssessment,
          InformationModel.BehavioralAssessment.ofStrategy] using supported
      · exact (ordinary same).elim

end Vegas
