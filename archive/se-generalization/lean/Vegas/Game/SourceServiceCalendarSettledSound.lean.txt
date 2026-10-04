/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSettledSound
import Vegas.Game.SourceServiceTrafficSound

/-! # Settled packet soundness of the retained source calendar

The concrete roster calendar emits conforming sole calls from its retained
menu. Protected inclusion then makes each actual emitted packet permitted by
the contract's settled record at every legal calendar history.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- In the retained source service a fresh submission conforms on the public
view its author sees. -/
theorem sourceService_fresh_response [Fintype Player] (bounds : MessageBounds (graph setup))
    (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {rosters : (graph setup).EventId → List Player}
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks) {remaining : Nat} {who : Player}
    {execution : (application setup leaks).Execution}
    (prior : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (submitted : response.transmission = some material) :
    (runtime setup).freshServiceEnvelope execution.application.publicView
      ⟨(who, execution.network.nextSerial who),
        (application setup leaks).packet ((application setup leaks).submit
          execution.application who material) who (execution.network.known who) material⟩ := by
  classical
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  let joint : ∀ i, Option ((menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Action i) :=
    fun i => if i = who then some response else none
  have legal : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Legal
        (some ⟨remaining, some who, execution⟩) joint := by
    refine ⟨fun stopped => ?_, fun player => ?_⟩
    · change remaining = 0 ∧ some who = none at stopped
      cases stopped.2
    · by_cases same : player = who
      · subst player
        simp only [joint, ↓reduceIte]
        exact ⟨rfl, member⟩
      · simp only [joint, same, ↓reduceIte]
        intro active
        exact same (Option.some.inj active.symm)
  have reached : some ⟨remaining, none, execution.respond app who response⟩ ∈
      ((menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).step
          (some ⟨remaining, some who, execution⟩) ⟨joint, legal⟩).support := by
    change _ ∈ (app.transition (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) (some ⟨remaining, some who, execution⟩)
        joint).support
    simp only [ReactiveApplication.transition, joint, ↓reduceIte, Option.getD_some]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have trafficOk := sourceService_history_traffic bounds values capacity opportunities network
    ⟨_, .extend prior joint legal reached⟩
  have traffic := app.stateTraffic_transition (initialLaw setup) _ _
    ⟨_, menu.toRawTrace (initialLaw setup) _ _ prior⟩ joint _ reached
  have facts := settledFacts_history (initialLaw setup) _ _
    (menu.toRawTrace (initialLaw setup) _ _ prior)
  rcases response with ⟨transmission⟩
  cases submitted
  have recorded : (⟨execution.application.publicView, execution.network.ledger,
      ⟨(who, execution.network.nextSerial who),
        app.packet (app.submit execution.application who material) who
          (execution.network.known who) material⟩⟩ : app.TrafficRecord) ∈
      app.stateTraffic (some ⟨remaining, none,
        execution.respond app who ⟨some material⟩⟩) := by
    rw [traffic]
    refine List.mem_append_right _ ?_
    simp only [ReactiveApplication.trafficStep, ReactiveApplication.Execution.respond,
      MessageNetwork.submit, List.drop_left', List.map_cons, List.map_nil,
      List.mem_singleton]
    rfl
  have permitted := trafficOk _ recorded
  have unpublished : (who, execution.network.nextSerial who) ∉
      execution.network.ledger.map Message.id := by
    intro published
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp published
    have bound := facts.serials.ledger other otherMember
    rw [same] at bound
    exact Nat.lt_irrefl _ bound
  exact (((runtime setup).permittedServiceEnvelope_unpublished_iff _ _ _ unpublished).mp
    permitted).2

/-- **The settled record permits every retained packet.** At every history of
the retained source service, including off-path and intermediate histories,
every transmitted packet is permitted by the contract's current record. -/
theorem sourceService_history_settled [Fintype Player] (bounds : MessageBounds (graph setup))
    (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {rosters : (graph setup).EventId → List Player}
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks) {control : (application setup leaks).Control}
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) :
    ∀ record ∈ (application setup leaks).executionTraffic control.execution,
      ((runtime setup).settledRecord leaks control.execution).permits record.envelope =
        true := by
  have retained : RetainedFacts setup leaks control.execution :=
    retainedFacts_history (rosterScheduler_protectedInclusion setup leaks rosters network)
      (sourceServiceMenu setup leaks bounds rosters)
      (fun prior response member material submitted =>
        sourceService_fresh_response bounds values capacity opportunities network prior response
          member material submitted)
      (fun who _ _ response member => bounds.compiledActions_firstSubmission (runtime setup) leaks
        who _ _ response (sourceServiceMenu_in_compiled setup leaks bounds rosters who _ _ member))
      trace
  have inputs := (application setup leaks).stateTraffic_inputs (initialLaw setup) _ _
    ((sourceServiceMenu setup leaks bounds rosters).toRawTrace (initialLaw setup) _ _ trace)
  change ((application setup leaks).executionTraffic control.execution).map
    ReactiveApplication.TrafficRecord.envelope = control.execution.network.inputs at inputs
  intro record member
  have emitted : Emitted setup leaks control.execution record.envelope := by
    unfold Emitted
    rw [← inputs]
    exact List.mem_map.mpr ⟨record, member, rfl⟩
  exact (retained.good _ emitted).permits


end Vegas
