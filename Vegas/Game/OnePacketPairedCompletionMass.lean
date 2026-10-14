/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketEnvironmentSteps

/-! # Chance mass depends only on paired public endpoints -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
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

/-- Matching public endpoints of actual configuration steps have equal chance
completion factors. Binding changes may be directed and need not be invertible. -/
theorem completionMass_eq_of_public_steps
    {before after imageBefore imageAfter : EventGraphRuntime.State (graph setup)}
    (leftStep : ConfigStep setup before.config after.config)
    (rightStep : ConfigStep setup imageBefore.config imageAfter.config)
    (beforePublic : (graph setup).publicObserve before.config =
      (graph setup).publicObserve imageBefore.config)
    (afterPublic : (graph setup).publicObserve after.config =
      (graph setup).publicObserve imageAfter.config) :
    completionMass setup before after = completionMass setup imageBefore imageAfter := by
  have beforeOrder := congrArg EventGraph.PublicObservation.completionOrder beforePublic
  have afterOrder := congrArg EventGraph.PublicObservation.completionOrder afterPublic
  have beforeLength := congrArg List.length beforeOrder
  have afterLength := congrArg List.length afterOrder
  change before.config.history.map EventGraph.Completion.event =
    imageBefore.config.history.map EventGraph.Completion.event at beforeOrder
  change after.config.history.map EventGraph.Completion.event =
    imageAfter.config.history.map EventGraph.Completion.event at afterOrder
  simp only [EventGraph.publicObserve, List.length_map] at beforeLength afterLength
  rcases leftStep with leftSame | ⟨event, ready, action, member⟩
  · rcases rightStep with rightSame | ⟨other, otherReady, otherAction, otherMember⟩
    · rw [completionMass_of_config_eq leftSame, completionMass_of_config_eq rightSame]
    · have extended := imageBefore.config.step_history other otherReady otherAction _ otherMember
      rw [leftSame, extended] at afterLength
      simp only [List.length_append, List.length_cons, List.length_nil] at afterLength
      omega
  · rcases rightStep with rightSame | ⟨other, otherReady, otherAction, otherMember⟩
    · have extended := before.config.step_history event ready action _ member
      rw [rightSame, extended] at afterLength
      simp only [List.length_append, List.length_cons, List.length_nil] at afterLength
      omega
    · rw [before.config.step_history event ready action _ member,
        imageBefore.config.step_history other otherReady otherAction _ otherMember,
        List.map_append, List.map_append] at afterOrder
      change before.config.history.map EventGraph.Completion.event ++ [event] =
        imageBefore.config.history.map EventGraph.Completion.event ++ [other] at afterOrder
      rw [beforeOrder] at afterOrder
      have eventEq := List.singleton_inj.mp (List.append_cancel_left afterOrder)
      subst other
      rw [completionMass_of_step member, completionMass_of_step otherMember]
      cases chance : (graph setup).actor? event with
      | some owner => rfl
      | none =>
          cases node : nodeView (graph setup) event with
          | bind owner payload outputEq codeEq =>
              rw [nodeView_bind_actor outputEq codeEq] at chance
              cases chance
          | resolve owner payload binding checks outputEq codeEq =>
              rw [nodeView_resolve_actor outputEq codeEq] at chance
              cases chance
          | sample payload law outputEq codeEq =>
              apply congrArg ENNReal.toReal
              exact EventGraph.sample_step_mass_of_public event ready otherReady action
                otherAction payload law outputEq codeEq
                (congrArg EventGraph.PublicObservation.store beforePublic)
                (congrArg EventGraph.PublicObservation.store afterPublic) member otherMember

variable {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {horizon : Nat} {scheduler : (application setup leaks).Scheduler}

/-- Complete operational endpoint equality determines the completion factor of
any two realized native transitions, including scheduler and response rounds. -/
theorem completionMass_eq_of_operational_transitions
    {before after imageBefore imageAfter : (application setup leaks).Control}
    (joint imageJoint : Player → Option (application setup leaks).Action)
    (realized : some after ∈ ((application setup leaks).transition (initialLaw setup) horizon
      scheduler (some before) joint).support)
    (imageRealized : some imageAfter ∈ ((application setup leaks).transition (initialLaw setup)
      horizon scheduler (some imageBefore) imageJoint).support)
    (beforeOperational : operationalState setup leaks (some before) =
      operationalState setup leaks (some imageBefore))
    (afterOperational : operationalState setup leaks (some after) =
      operationalState setup leaks (some imageAfter)) :
    completionMass setup before.execution.application after.execution.application =
      completionMass setup imageBefore.execution.application imageAfter.execution.application := by
  apply completionMass_eq_of_public_steps
    (transition_configStep (initialLaw setup) horizon scheduler before after joint realized)
    (transition_configStep (initialLaw setup) horizon scheduler imageBefore imageAfter imageJoint
      imageRealized)
  · exact congrArg (fun state : OperationalState setup leaks =>
      state.environment.application.observation) (Option.some.inj beforeOperational)
  · exact congrArg (fun state : OperationalState setup leaks =>
      state.environment.application.observation) (Option.some.inj afterOperational)

end Vegas
