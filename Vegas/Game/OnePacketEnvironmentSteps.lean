/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFactorization
import Vegas.Game.OnePacketPendingPool
import Vegas.Game.ServiceSettledEvidence
import Interaction.ReactiveResponseAccounting

/-! # Scheduler rounds factor through the operational record

The mass of a scheduler round of the one-packet game is the chance mass of the
event it completes, times a function of the operational states before and after
the round (`Vegas.environment_stepProb`). That function reads the command from
the scheduler's recall after the round, takes its mass under the scheduler at
the recall and view before it, and at an activation multiplies by the mass the
observation rule gives the leaked packets (`Vegas.environmentMass`). The network
is recorded whole in the operational state (`Vegas.OperationalState.network`),
so no hypothesis on the scheduler or the observation rule is needed for this.

So the operational steps of the factorization reduce to their component part:
any response mass satisfying the component bound at regular responses of other
players gives operational steps, with the round mass at scheduler rounds
(`Vegas.OperationalSteps.ofComponents`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The network an operational state records. -/
def OperationalState.network (state : OperationalState setup runtime leaks) :
    MessageNetwork Player (application setup runtime leaks).Payload :=
  ⟨state.environment.network.pending, state.environment.network.ledger, state.leaked,
    state.environment.network.inputs, state.environment.network.nextSerial⟩

/-- The mass of the network effect of a command: at an activation, the mass the
observation rule gives the packets the activated player learns; one
otherwise. -/
def commandMass (before after : OperationalState setup runtime leaks) :
    (application setup runtime leaks).Command → ℝ
  | .activate who =>
      ((leaks who before.network.pending).toOuterMeasure
        {selected | before.network.learn who selected = after.network
          (runtime := runtime)}).toReal
  | _ => 1

variable (scheduler : (application setup runtime leaks).Scheduler)

/-- **The operational mass of a scheduler round.** The scheduler's mass for the
command recorded by the round, at the recall and view before it, times the
mass of the command's network effect. -/
def environmentMass :
    Option (OperationalState setup runtime leaks) → Option (OperationalState setup runtime leaks)
      → ℝ
  | some before, some after =>
      match after.environmentRecall.drop before.environmentRecall.length with
      | [entry] => (scheduler before.environmentRecall before.environment entry.command).toReal *
          commandMass setup runtime leaks before after entry.command
      | _ => 1
  | _, _ => 1

variable {setup runtime leaks scheduler}

theorem completionMass_of_config_eq {before after : EventGraphRuntime.State (graph setup)}
    (same : after.config = before.config) : completionMass setup before after = 1 := by
  unfold completionMass
  rw [same, List.drop_length]

theorem completionMass_of_step {before after : EventGraphRuntime.State (graph setup)}
    {event : (graph setup).EventId} {ready : before.config.cut.Ready event}
    {action : (graph setup).Action event}
    (member : after.config ∈ (before.config.step event ready action).support) :
    completionMass setup before after =
      match (graph setup).actor? event with
      | none => (before.config.step event ready action after.config).toReal
      | some _ => 1 := by
  unfold completionMass
  rw [before.config.step_history event ready action _ member, List.drop_left]
  rcases acting : (graph setup).actor? event with _ | actor <;>
    simp only [acting, dite_eq_left ready]

/-- A point mass at a reached point has mass one there. -/
private theorem pure_apply_of_mem {α : Type*} {point reached : α}
    (member : reached ∈ (PMF.pure point).support) : (PMF.pure point reached).toReal = 1 := by
  rw [(PMF.mem_support_pure_iff _ _).mp member, PMF.pure_apply_self, ENNReal.toReal_one]

/-- An included packet that completes an event completes one with an actor. -/
theorem include_completion_actor (execution : (application setup runtime leaks).Execution)
    (id : MessageId Player) {event : (graph setup).EventId}
    {ready : execution.application.config.cut.Ready event} {action : (graph setup).Action event}
    (member : (execution.includePending (application setup runtime leaks) id).application.config ∈
      (execution.application.config.step event ready action).support) :
    ∃ actor, (graph setup).actor? event = some actor := by
  cases found : execution.network.lookup id with
  | none =>
      exact (config_ne_of_step member (by
        simp only [ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found])).elim
  | some message =>
      cases accepted : (application setup runtime leaks).handle execution.application message with
      | none =>
          exact (config_ne_of_step member (by
            simp only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found, accepted, Option.getD_none])).elim
      | some after =>
          have applicationEq :
              (execution.includePending (application setup runtime leaks) id).application = after
                := by
            simp only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found, accepted, Option.getD_some]
          obtain ⟨_, namedEvent, named, _, _, actor⟩ :=
            accepted_inclusion execution.application after message accepted
          obtain ⟨other, otherNamed, _, _, otherMember⟩ :=
            handle_config_mem_step runtime execution.application after _
              (reactiveHandle_call accepted)
          have sameNamed : other = namedEvent := Option.some.inj (otherNamed.symm.trans named)
          subst sameNamed
          rw [applicationEq] at member
          cases step_completion_unique otherMember member
          exact ⟨_, actor⟩

/-- An expiry that completes an event completes one with an actor. -/
theorem expire_completion_actor (state next : EventGraphRuntime.State (graph setup))
    (expired : (graph setup).EventId)
    (changed : next ∈ (EventGraphRuntime.environmentStep runtime state
      (.expire expired)).support)
    {event : (graph setup).EventId} {ready : state.config.cut.Ready event}
    {action : (graph setup).Action event}
    (member : next.config ∈ (state.config.step event ready action).support) :
    ∃ actor, (graph setup).actor? event = some actor := by
  have stutter : next = state → False := fun same => config_ne_of_step member (by rw [same])
  obtain ⟨_, effect⟩ := environmentStep_expire_config_activated runtime state next
    expired changed
  rcases effect with ⟨configEq, _⟩ | ⟨expiredReady, expiredAction, expiredMember, _⟩
  · exact (config_ne_of_step member configEq).elim
  · cases step_completion_unique expiredMember member
    cases view : nodeView (graph setup) expired with
    | bind owner _ outputEq codeEq => exact ⟨owner, nodeView_bind_actor outputEq codeEq⟩
    | resolve owner _ _ _ outputEq codeEq => exact ⟨owner, nodeView_resolve_actor outputEq codeEq⟩
    | sample payload law outputEq codeEq =>
        exfalso
        apply stutter
        cases activated : state.activatedAt expired with
        | none =>
            rw [environmentStep_expire_of_not_activated runtime _ expired ready activated,
              PMF.mem_support_pure_iff] at changed
            exact changed
        | some entered =>
            by_cases due : runtime.deadline expired ≤ state.clock - entered
            · rw [environmentStep_expire_sample_eq runtime _ expired ready entered activated
                due payload law outputEq codeEq view, PMF.mem_support_pure_iff] at changed
              exact changed
            · rw [environmentStep_expire_of_not_due runtime _ expired ready entered
                activated due, PMF.mem_support_pure_iff] at changed
              exact changed

/-- The contract part of a scheduler command: its mass at a reached state is the
chance mass of the completed event. -/
theorem applicationStep_mass (state next : EventGraphRuntime.State (graph setup))
    (command : EnvironmentCommand (graph setup))
    (changed : next ∈ (EventGraphRuntime.environmentStep runtime state command).support) :
    (EventGraphRuntime.environmentStep runtime state command next).toReal =
      completionMass setup state next := by
  cases command with
  | advanceClock =>
      have reached := changed
      simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at reached
      rw [show EventGraphRuntime.environmentStep runtime state .advanceClock =
        PMF.pure { state with clock := state.clock + 1 } from rfl, pure_apply_of_mem changed,
        completionMass_of_config_eq (by rw [reached])]
  | expire expired =>
      rw [show EventGraphRuntime.environmentStep runtime state (.expire expired) =
        PMF.pure _ from rfl] at changed ⊢
      rw [pure_apply_of_mem changed]
      obtain ⟨_, effect⟩ := environmentStep_expire_config_activated runtime state next
        expired changed
      rcases effect with ⟨configEq, _⟩ | ⟨ready, action, member, _⟩
      · rw [completionMass_of_config_eq configEq]
      · obtain ⟨actor, acts⟩ := expire_completion_actor state next expired
          changed member
        rw [completionMass_of_step member, acts]
  | executeSample sampled =>
      by_cases ready : state.config.cut.Ready sampled
      · cases view : nodeView (graph setup) sampled with
        | sample payload law outputEq codeEq =>
            have lawEq := environmentStep_executeSample_eq runtime state sampled ready
              payload law outputEq codeEq view
            rw [lawEq, PMF.support_map] at changed
            obtain ⟨config, configMember, rfl⟩ := changed
            rw [lawEq, pmf_map_apply_of_injective _ (fun first second same => by
              have := congrArg EventGraphRuntime.State.config same
              exact this) config,
              completionMass_of_step configMember, nodeView_sample_actor outputEq codeEq]
        | bind owner payload outputEq codeEq =>
            have lawEq := environmentStep_executeSample_of_nonsample runtime state sampled
              ready (fun _ _ _ _ sampled => by rw [view] at sampled; cases sampled)
            rw [lawEq] at changed ⊢
            rw [pure_apply_of_mem changed, completionMass_of_config_eq (by
              rw [(PMF.mem_support_pure_iff _ _).mp changed])]
        | resolve owner payload binding checks outputEq codeEq =>
            have lawEq := environmentStep_executeSample_of_nonsample runtime state sampled
              ready (fun _ _ _ _ sampled => by rw [view] at sampled; cases sampled)
            rw [lawEq] at changed ⊢
            rw [pure_apply_of_mem changed, completionMass_of_config_eq (by
              rw [(PMF.mem_support_pure_iff _ _).mp changed])]
      · have lawEq := environmentStep_executeSample_of_not_ready runtime state sampled ready
        rw [lawEq] at changed ⊢
        rw [pure_apply_of_mem changed, completionMass_of_config_eq (by
          rw [(PMF.mem_support_pure_iff _ _).mp changed])]

/-- **The mass of one command.** The environment step of a command gives a
reached execution the chance mass of its completed event times the mass of the
command's network effect. -/
theorem environmentStep_mass (execution reached : (application setup runtime leaks).Execution)
    (command : (application setup runtime leaks).Command)
    (member : reached ∈ (execution.environmentStep (application setup runtime leaks)
      command).support)
    (before after : OperationalState setup runtime leaks) (beforeNetwork : before.network (runtime
      := runtime) =
      execution.network) (afterNetwork : after.network = reached.network) :
    (execution.environmentStep (application setup runtime leaks) command reached).toReal =
      completionMass setup execution.application reached.application *
        commandMass setup runtime leaks before after command := by
  let app := application setup runtime leaks
  let record := execution.environmentRecall ++ [⟨execution.observeEnvironment app, command⟩]
  cases command with
  | activate who =>
      let place : MessageNetwork Player app.Payload → app.Execution := fun network =>
        { execution with network := network, environmentRecall := record }
      have lawEq : execution.environmentStep app (.activate who) =
          (leaks who execution.network.pending).map
            (fun selected => place (execution.network.learn who selected)) := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.map_comp]
        rfl
      rw [lawEq] at member ⊢
      obtain ⟨chosen, _, rfl⟩ := PMF.support_map .. ▸ member
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
        completionMass_of_config_eq rfl, one_mul]
      unfold commandMass
      rw [beforeNetwork, afterNetwork]
      congr 2
      ext selected
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro same
        exact congrArg ReactiveApplication.Execution.network same
      · intro same
        change place _ = place _
        rw [show (place (execution.network.learn who chosen)).network =
          execution.network.learn who chosen from rfl] at same
        rw [same]
  | wait =>
      have lawEq : execution.environmentStep app .wait =
          PMF.pure { execution with environmentRecall := record } := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.pure_map]
      rw [lawEq] at member ⊢
      rw [pure_apply_of_mem member, (PMF.mem_support_pure_iff _ _).mp member,
        completionMass_of_config_eq rfl]
      simp [commandMass]
  | «include» id =>
      have lawEq : execution.environmentStep app (.include id) =
          PMF.pure { execution.includePending app id with environmentRecall := record } := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.pure_map]
      have step := environmentStep_configStep setup leaks execution reached _ member
      rw [lawEq] at member ⊢
      rw [pure_apply_of_mem member]
      have applicationEq : reached.application = (execution.includePending app id).application := by
        rw [(PMF.mem_support_pure_iff _ _).mp member]
      rcases step with same | ⟨event, ready, action, configMember⟩
      · rw [completionMass_of_config_eq same]
        simp [commandMass]
      · rw [completionMass_of_step configMember]
        rw [applicationEq] at configMember
        obtain ⟨actor, acts⟩ := include_completion_actor execution id
          configMember
        rw [acts]
        simp [commandMass]
  | application command =>
      let place : EventGraphRuntime.State (graph setup) → app.Execution := fun state =>
        { execution with application := state, environmentRecall := record }
      have lawEq : execution.environmentStep app (.application command) =
          (EventGraphRuntime.environmentStep runtime execution.application command).map
            place := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.map_comp]
        rfl
      rw [lawEq] at member ⊢
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ member
      rw [pmf_map_apply_of_injective _ (fun first second same =>
        congrArg ReactiveApplication.Execution.application same) state,
        applicationStep_mass (runtime := runtime) execution.application state command changed]
      exact (mul_one _).symm

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}

/-- **Scheduler rounds factor through the operational record.** The mass of a
scheduler round of the one-packet game, under any profile, is the chance mass
of the event it completes times the operational mass of the round. -/
theorem environment_stepProb
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    {before after : (application setup runtime leaks).ProtocolState}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      before
      ⟨joint, legal⟩).support) (control : (application setup runtime leaks).Control)
    (initialized : before = some control) (idle : control.actor = none)
    (next : (application setup runtime leaks).Control) (reachedNext : after = some next) :
    InformationModel.stepProb (onePacketInformation setup runtime leaks bounds horizon scheduler)
        profile prior ⟨joint, legal⟩ after =
      completionMass setup control.execution.application next.execution.application *
        environmentMass setup runtime leaks scheduler (operationalState setup runtime leaks before)
          (operationalState setup runtime leaks after) := by
  let app := application setup runtime leaks
  subst initialized reachedNext
  rw [stepProb_of_idle (runtime := runtime) profile prior joint legal idle]
  change some next ∈ (app.transition (initialLaw setup) horizon scheduler (some control)
    joint).support at realized
  rcases control with ⟨remaining, current, execution⟩
  change current = none at idle
  subst idle
  cases remaining with
  | zero =>
      have lawEq : app.transition (initialLaw setup) horizon scheduler (some ⟨0, none, execution⟩)
          joint = PMF.pure (some ⟨0, none, execution⟩) := rfl
      rw [lawEq] at realized ⊢
      rw [pure_apply_of_mem realized]
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp realized)
      rw [completionMass_of_config_eq rfl]
      simp [environmentMass, operationalState]
  | succ remaining =>
      let shift : app.Command → app.Execution → app.ProtocolState := fun command reached =>
        some ⟨remaining, command.actor? app, reached⟩
      have lawEq : app.transition (initialLaw setup) horizon scheduler
          (some ⟨remaining + 1, none, execution⟩) joint =
          (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
            fun command => (execution.environmentStep app command).map (shift command) := rfl
      rw [lawEq] at realized ⊢
      obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
      obtain ⟨reached, member, same⟩ := PMF.support_map .. ▸ moved
      cases same
      have recallEq := app.environmentStep_environmentRecall execution reached command member
      rw [PMF.bind_apply, tsum_eq_single command]
      · rw [pmf_map_apply_of_injective _ (fun first second equal => by
            have inner := Option.some.inj equal
            exact congrArg ReactiveApplication.Control.execution inner) reached,
          ENNReal.toReal_mul]
        obtain ⟨first, firstEq⟩ : ∃ first, operationalState setup runtime leaks
            (some ⟨remaining + 1, none, execution⟩) = some first := ⟨_, rfl⟩
        obtain ⟨second, secondEq⟩ : ∃ second, operationalState setup runtime leaks
            (some ⟨remaining, command.actor? app, reached⟩) = some second := ⟨_, rfl⟩
        have firstRecall : first.environmentRecall =
          execution.environmentRecall := by
          rw [← Option.some.inj firstEq]
        have firstView : first.environment = execution.observeEnvironment app
          := by
          rw [← Option.some.inj firstEq]
        have firstNetwork : first.network = execution.network := by
          rw [← Option.some.inj firstEq]
          rfl
        have secondRecall : second.environmentRecall =
          reached.environmentRecall := by
          rw [← Option.some.inj secondEq]
        have secondNetwork : second.network = reached.network := by
          rw [← Option.some.inj secondEq]
          rfl
        rw [firstEq, secondEq, environmentStep_mass (runtime := runtime) execution reached command
          member first second
          firstNetwork secondNetwork]
        simp only [environmentMass, firstRecall, secondRecall, recallEq, List.drop_left, firstView]
        ring
      · intro other different
        rw [mul_eq_zero]
        right
        rw [PMF.apply_eq_zero_iff]
        intro present
        obtain ⟨otherReached, otherMember, otherSame⟩ := PMF.support_map .. ▸ present
        have inner := congrArg ReactiveApplication.Control.execution (Option.some.inj otherSame)
        change otherReached = reached at inner
        subst inner
        have otherRecall := app.environmentStep_environmentRecall execution otherReached other
          otherMember
        rw [recallEq] at otherRecall
        have entries := List.append_cancel_left otherRecall
        exact different (congrArg ReactiveApplication.EnvironmentEntry.command
          (List.singleton_injective entries)).symm

omit [Fintype Player] in
theorem environmentMass_nonneg (before after : Option (OperationalState setup runtime leaks)) :
    0 ≤ environmentMass setup runtime leaks scheduler before after := by
  unfold environmentMass
  split
  · split
    · rename_i entry _
      refine mul_nonneg ENNReal.toReal_nonneg ?_
      unfold commandMass
      split
      · exact ENNReal.toReal_nonneg
      · exact zero_le_one
    · exact zero_le_one
  · exact zero_le_one

/-- The operational mass of a transition: the round's mass at a scheduler round
and a given response mass at a response. -/
def roundOrResponseMass
    (response : Option (OperationalState setup runtime leaks) → Option (OperationalState setup
      runtime leaks) → ℝ)
    (before after : Option (OperationalState setup runtime leaks)) : ℝ :=
  match before with
  | some state =>
      if state.actor = none then environmentMass setup runtime leaks
        scheduler before after
      else response before after
  | none => 1

/-- **Operational steps from component steps.** Scheduler rounds need no
hypothesis: given a response mass for which every regular response of another
player satisfies the component bound, the operational steps hold with the round
mass at scheduler rounds. -/
def OperationalSteps.ofComponents {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player}
    (response : ℕ → Option (OperationalState setup runtime leaks) →
      Option (OperationalState setup runtime leaks) → ℝ)
    (error : ℕ → ℝ) (response_nonneg : ∀ n before after, 0 ≤ response n before after)
    (error_nonneg : ∀ n, 0 ≤ error n) (error_tendsto : Filter.Tendsto error Filter.atTop (nhds 0))
    (component : ∀ n {before after}
      (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before)
        joint legal
      (_ : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (control next : (application setup runtime leaks).Control)
      (actor : Player), before = some control → after = some next →
      control.actor = some actor → actor ≠ who →
      forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw setup)
        horizon
        scheduler actor ((application setup runtime leaks).observe actor (some control)) →
      ForcedState setup runtime leaks who (some control) →
      0 < contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
        ((joint actor).getD ⟨none⟩) →
      |InformationModel.stepProb (onePacketInformation setup runtime leaks bounds horizon scheduler)
          (profiles n) prior ⟨joint, legal⟩ after -
        contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
            ((joint actor).getD ⟨none⟩) *
          response n (operationalState setup runtime leaks before) (operationalState setup runtime
            leaks after)| ≤
        error n * (contentFactor setup runtime leaks (sequence n) actor control.execution
          next.execution
            ((joint actor).getD ⟨none⟩) *
          response n (operationalState setup runtime leaks before) (operationalState setup runtime
            leaks after))) :
    OperationalSteps setup runtime leaks bounds horizon scheduler sequence profiles who where
  mass n := roundOrResponseMass (runtime := runtime) (scheduler := scheduler)
    (response n)
  error := error
  mass_nonneg n before after := by
    unfold roundOrResponseMass
    split
    · split
      · exact environmentMass_nonneg (runtime := runtime) _ _
      · exact response_nonneg _ _ _
    · exact zero_le_one
  error_nonneg := error_nonneg
  error_tendsto := error_tendsto
  environment n before after prior joint legal realized control initialized
    idle next reached := by
    rw [environment_stepProb (runtime := runtime) (profiles n) prior joint legal realized control
      initialized idle next
      reached]
    subst initialized
    congr 1
    change _ = if control.actor = none then _ else _
    simp only [idle, ↓reduceIte]
  component n before after prior joint legal realized control next actor
    initialized reached
      acting other forced observerForced positive := by
    have bound := component n prior joint legal realized control next actor initialized reached
      acting other forced observerForced positive
    subst initialized
    have active : ¬ control.actor = none := by rw [acting]; exact Option.some_ne_none _
    have massEq : roundOrResponseMass (runtime := runtime) (scheduler := scheduler) (response n)
        (operationalState setup runtime leaks (some control)) (operationalState setup runtime
          leaks after) =
        response n (operationalState setup runtime leaks (some control))
          (operationalState setup runtime leaks after) := by
      change (if control.actor = none then _ else _) = _
      simp only [active, ↓reduceIte]
    rw [massEq]
    exact bound

end Vegas
