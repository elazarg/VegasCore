module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketEnvironmentSteps
public import Vegas.Pending.EventSampleObservation
public import Vegas.EventGraph.BarrierInformation

@[expose] public section

/-! # Chance mass depends only on paired public endpoints -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Public sample laws and their realized public values determine the exact
completion mass, even when private binding stores differ. -/
theorem sample_step_mass_of_public {left right afterLeft afterRight : graph.Config}
    (event : graph.EventId) (leftReady : left.cut.Ready event)
    (rightReady : right.cut.Ready event) (leftAction rightAction : graph.Action event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .sample payload law)
    (beforePublic : graph.publicStore left.store = graph.publicStore right.store)
    (afterPublic : graph.publicStore afterLeft.store = graph.publicStore afterRight.store)
    (leftMember : afterLeft ∈ (left.step event leftReady leftAction).support)
    (rightMember : afterRight ∈ (right.step event rightReady rightAction).support) :
    left.step event leftReady leftAction afterLeft =
      right.step event rightReady rightAction afterRight := by
  classical
  obtain ⟨leftUnit, rfl⟩ : ∃ marker : PUnit,
      leftAction = cast (congrArg EventField.Action outputEq.symm) marker :=
    ⟨cast (congrArg EventField.Action outputEq) leftAction, by simp⟩
  obtain ⟨rightUnit, rfl⟩ : ∃ marker : PUnit,
      rightAction = cast (congrArg EventField.Action outputEq.symm) marker :=
    ⟨cast (congrArg EventField.Action outputEq) rightAction, by simp⟩
  cases leftUnit
  cases rightUnit
  have available : (law.eval? left.store).isSome := by
    apply law.eval?_isSome
    intro field member
    apply left.read_available leftReady
    rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
    exact member
  let draw := (law.eval? left.store).get available
  have leftLaw : law.eval? left.store = some draw := (Option.some_get _).symm
  have rightLaw : law.eval? right.store = some draw := by
    rw [← law.eval?_publicStore right.store, ← beforePublic, law.eval?_publicStore left.store]
    exact leftLaw
  have leftStep := left.step_eq_map_of_code event leftReady outputEq (.sample payload law)
    codeEq PUnit.unit draw leftLaw
  have rightStep := right.step_eq_map_of_code event rightReady outputEq (.sample payload law)
    codeEq PUnit.unit draw rightLaw
  rw [leftStep, PMF.support_map] at leftMember
  obtain ⟨leftValue, _, rfl⟩ := leftMember
  rw [rightStep, PMF.support_map] at rightMember
  obtain ⟨rightValue, _, rfl⟩ := rightMember
  have values : leftValue = rightValue := by
    have stored := congrFun afterPublic (.inr event)
    have visible : graph.fieldPublic (.inr event) := by
      change (graph.outputLayout event).IsPublic
      rw [outputEq]
      trivial
    rw [publicStore_of_public _ _ _ visible, publicStore_of_public _ _ _ visible] at stored
    simp only [Config.store_output, Config.complete_output_same, Option.some.injEq] at stored
    exact (cast_inj _).mp stored
  subst rightValue
  have injective (config : graph.Config) (ready : config.cut.Ready event) :
      Function.Injective (fun value : L.Val payload => config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventField.Value outputEq.symm) value)) := by
    intro first second equal
    have stored := congrArg (fun next : graph.Config => next.outputs event) equal
    simp only [Config.complete_output_same, Option.some.injEq] at stored
    exact (cast_inj _).mp stored
  rw [leftStep, rightStep, pmf_map_apply_of_injective _ (injective left leftReady),
    pmf_map_apply_of_injective _ (injective right rightReady)]

end Vegas.EventGraph

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}

/-- Public completion order, sampled outputs and sample distributions determine
completion mass, without a reachability or one-step premise. -/
theorem completionMass_eq_of_public
    {before after imageBefore imageAfter : EventGraphRuntime.State (graph setup)}
    (beforePublic : (graph setup).publicObserve before.config =
      (graph setup).publicObserve imageBefore.config)
    (afterPublic : (graph setup).publicObserve after.config =
      (graph setup).publicObserve imageAfter.config) :
    completionMass setup before after = completionMass setup imageBefore imageAfter := by
  have beforeOrder := congrArg EventPublicObservation.completionOrder beforePublic
  have afterOrder := congrArg EventPublicObservation.completionOrder afterPublic
  change before.config.history.map EventCompletion.event =
    imageBefore.config.history.map EventCompletion.event at beforeOrder
  change after.config.history.map EventCompletion.event =
    imageAfter.config.history.map EventCompletion.event at afterOrder
  have beforeLength := congrArg List.length beforeOrder
  simp only [List.length_map] at beforeLength
  have suffix : (after.config.history.drop before.config.history.length).map
        EventCompletion.event =
      (imageAfter.config.history.drop imageBefore.config.history.length).map
        EventCompletion.event := by
    rw [List.map_drop, List.map_drop, afterOrder, beforeLength]
  cases left : after.config.history.drop before.config.history.length with
  | nil =>
      cases right : imageAfter.config.history.drop imageBefore.config.history.length with
      | nil =>
          unfold completionMass
          rw [left, right]
      | cons record rest =>
          simp only [left, right, List.map_nil, List.map_cons] at suffix
          cases suffix
  | cons record rest =>
      cases right : imageAfter.config.history.drop imageBefore.config.history.length with
      | nil =>
          simp only [left, right, List.map_nil, List.map_cons] at suffix
          cases suffix
      | cons imageRecord imageRest =>
          have eventEq : record.event = imageRecord.event := by
            simp only [left, right, List.map_cons, List.cons.injEq] at suffix
            exact suffix.1
          rcases record with ⟨event, decision, defaultEvent⟩
          rcases imageRecord with ⟨imageEvent, imageDecision, imageDefault⟩
          change event = imageEvent at eventEq
          subst imageEvent
          unfold completionMass
          rw [left, right]
          dsimp only
          by_cases chance : (graph setup).actor? event = none
          · simp only [chance, ↓reduceDIte]
            have publicField : (graph setup).fieldPublic (.inr event) :=
              EventGraph.EventCode.output_public_of_actor_none
                ((graph setup).nodes event) chance
            have outputs := congrFun (congrArg EventPublicObservation.store afterPublic)
              (.inr event)
            change (graph setup).publicStore after.config.store (.inr event) =
              (graph setup).publicStore imageAfter.config.store (.inr event) at outputs
            rw [(graph setup).publicStore_of_public _ _ publicField,
              (graph setup).publicStore_of_public _ _ publicField] at outputs
            change after.config.outputs event = imageAfter.config.outputs event
              at outputs
            have stores := congrArg EventPublicObservation.store beforePublic
            change (graph setup).publicStore before.config.store =
              (graph setup).publicStore imageBefore.config.store at stores
            have evalPublic {output : EventGraph.EventField Player L}
                (code : EventGraph.EventCode (graph setup).layout output)
                (nobody : code.actor = none) :
                code.eval? (EventGraph.EventCode.actionOfActorNone code nobody)
                    before.config.store =
                  code.eval? (EventGraph.EventCode.actionOfActorNone code nobody)
                    imageBefore.config.store := by
              cases code with
              | bind owner payload => cases nobody
              | resolve owner payload binding checks => cases nobody
              | sample payload law =>
                  change law.eval? before.config.store = law.eval? imageBefore.config.store
                  rw [← law.eval?_publicStore before.config.store, stores,
                    law.eval?_publicStore imageBefore.config.store]
            rw [outputs, evalPublic ((graph setup).nodes event) chance]
            cases imageAfter.config.outputs event with
            | none => rfl
            | some value =>
                cases ((graph setup).nodes event).eval?
                    (EventGraph.EventCode.actionOfActorNone _ chance) imageBefore.config.store <;>
                  rfl
          · simp only [chance, ↓reduceDIte]

variable {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}

/-- Complete operational endpoint equality determines the completion factor of
any two realized native transitions, including scheduler and response rounds. -/
theorem completionMass_eq_of_operational_transitions
    {before after imageBefore imageAfter : (application setup timeouts leaks).Control}
    (joint imageJoint : Player → Option (application setup timeouts leaks).Action)
    (_realized : some after ∈ ((application setup timeouts leaks).transition (initialLaw setup)
      horizon
      scheduler (some before) joint).support)
    (_imageRealized : some imageAfter ∈ ((application setup timeouts leaks).transition (initialLaw
      setup)
      horizon scheduler (some imageBefore) imageJoint).support)
    (beforeOperational : operationalState setup timeouts leaks (some before) =
      operationalState setup timeouts leaks (some imageBefore))
    (afterOperational : operationalState setup timeouts leaks (some after) =
      operationalState setup timeouts leaks (some imageAfter)) :
    completionMass setup before.execution.application after.execution.application =
      completionMass setup imageBefore.execution.application imageAfter.execution.application := by
  apply completionMass_eq_of_public
  · exact congrArg (fun state : OperationalState setup timeouts leaks =>
      state.environment.application.observation) (Option.some.inj
        beforeOperational)
  · exact congrArg (fun state : OperationalState setup timeouts leaks =>
      state.environment.application.observation) (Option.some.inj
        afterOperational)

end Vegas
