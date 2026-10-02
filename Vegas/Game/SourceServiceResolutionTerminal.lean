/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionSilenceRates
import Vegas.Game.SourceServiceAudit
import Vegas.Pending.ReactiveOpeningExpiry
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Pending.ReactiveResolutionEvidence
import Interaction.ReactiveTrafficContinuation

/-! # Actual terminal settlement of a protected resolution opportunity

A supplied actual activation offers silence or an authentic opening. The
service includes the opening, advances the clock, and expires the remaining
resolution. This leaf relates the response reward to the resulting public
output and actual audit settlement. Deadline protection, activation, pending
publication, and the absence of earlier traffic are operational premises.
It does not construct an initialized information set or assert equilibrium.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability GameTheory.Enforcement
open Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A reward read from the actual public resolution output. -/
def resolutionPublicationReward (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (execution : (application setup leaks).Execution) : ℝ :=
  match (execution.application.config.outputs event).map
      (cast (congrArg EventField.Value outputEq)) with
  | some (.success _) => 1
  | _ => 0

/-- Only the resolution's owner is rewarded for a successful publication. -/
def resolutionTerminalPayoff (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload) :
    (application setup leaks).ProtocolState → Player → ℝ
  | none, _ => 0
  | some control, who => if who = owner then
      resolutionPublicationReward event payload outputEq control.execution else 0

/-- Execute an actual response, include its opening, expire any unresolved
resolution, and collect the terminal audit's realized payoff vector. -/
def resolutionAuditedSuffix (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat)
    (initial : (application setup leaks).Execution)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : Player → ℝ) (law : PMF (application setup leaks).Action) : PMF (Player → ℝ) :=
  law.bind fun response =>
    (((runtime setup).runInteractionPlan leaks players network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
        (initial.respond (application setup leaks) owner response)).bind fun final =>
      TerminalAudit.settlement (resolutionTerminalPayoff owner event payload outputEq)
        ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
        deposit (some ⟨0, none, final⟩))

private def passiveInstruction : ServiceInstruction (graph setup) → Prop
  | .player _ | .wire => False
  | _ => True

private theorem passive_plan_traffic
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (plan : List (ServiceInstruction (graph setup)))
    (quiet : ∀ instruction ∈ plan, passiveInstruction instruction)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network plan
      initial).support) :
    (application setup leaks).executionTraffic final =
      (application setup leaks).executionTraffic initial := by
  induction plan generalizing initial with
  | nil => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | cons instruction plan ih =>
      obtain ⟨middle, stepped, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, chosen, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ stepped)
      have inactive : command.actor? (application setup leaks) = none := by
        have allowed := quiet instruction (by simp)
        cases instruction with
        | player who | wire => exact allowed.elim
        | includeLatest event who =>
            cases (PMF.mem_support_pure_iff _ _).mp chosen
            unfold reactiveLatest
            split <;> rfl
        | sample event | tick | expire event =>
            cases (PMF.mem_support_pure_iff _ _).mp chosen
            rfl
      obtain ⟨observed, moved, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      change middle ∈ ((application setup leaks).resume players
        (command.actor? (application setup leaks)) observed).support at resumed
      rw [inactive] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact (ih (fun next member => quiet next (by simp [member])) middle rest).trans
        ((application setup leaks).executionTraffic_environment initial middle command moved)

private theorem resolution_tail_traffic
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player) (ticks : Nat)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
      initial).support) :
    (application setup leaks).executionTraffic final =
      (application setup leaks).executionTraffic initial := by
  apply passive_plan_traffic players network _ _ initial final reached
  intro instruction member
  simp only [List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil, or_false]
    at member
  rcases member with (rfl | ⟨_, rfl⟩) | rfl <;> trivial

private theorem resolution_response_traffic
    (before activated : (application setup leaks).Execution) (owner : Player)
    (activation : activated ∈ (before.environmentStep (application setup leaks)
      (.activate owner)).support)
    (emptyTraffic : (application setup leaks).executionTraffic before = [])
    (event : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    (owned : candidate.1 = owner)
    (valid : activated.application.candidates.lookup candidate = .openable raw) :
    (application setup leaks).executionTraffic
      (activated.respond (application setup leaks) owner ⟨none⟩) = [] ∧
    ((application setup leaks).executionTraffic
      (activated.respond (application setup leaks) owner
        ((runtime setup).windowOpening leaks event candidate raw))).map
          ReactiveApplication.TrafficRecord.envelope =
      [(runtime setup).windowEnvelope leaks owner event candidate raw activated] := by
  have inputs := (application setup leaks).environmentStep_inputs before activated
    (.activate owner) activation
  constructor
  · rw [(application setup leaks).executionTraffic_activated_response before activated owner
      ⟨none⟩ 0 activation, emptyTraffic]
    simp [ReactiveApplication.trafficStep, ReactiveApplication.Execution.respond, inputs]
  · rw [(application setup leaks).executionTraffic_activated_response before activated owner
      _ 0 activation, emptyTraffic]
    have packet := (runtime setup).windowOpening_packet leaks owner event candidate raw
      activated.application (activated.network.known owner) owned valid
    simp only [List.nil_append, ReactiveApplication.trafficStep,
      ReactiveApplication.Execution.respond, windowOpening, MessageNetwork.submit,
      inputs, List.drop_append_of_le_length (le_refl _), List.drop_length,
      List.nil_append, List.map_cons, List.map_nil, windowEnvelope]
    congr 2

private theorem complete_single_terminal
    (event : (graph setup).EventId) (unique : ∀ other : (graph setup).EventId, other = event)
    (config : (graph setup).Config) (ready : config.cut.Ready event)
    (action : (graph setup).Action event) (value : ((graph setup).outputLayout event).Value) :
    (config.complete event ready action value).cut.Terminal := by
  apply Finset.ext
  intro other
  simp [Config.complete, EventOrder.Cut.complete, unique other]

/-- The canonical authentic opening is accepted by the actual token-checking
handler at this protected resolution opportunity. -/
theorem resolutionOpening_accepted
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle (graph setup)) (value : L.Val payload)
    (initial : (application setup leaks).Execution)
    (ready : initial.application.config.cut.Ready event)
    (timely : initial.application.WithinDeadline (runtime setup) event)
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (associated : initial.application.accepted binding.field = some candidate)
    (resolved : EventCode.resolveOutput? binding checks true initial.application.config.store =
      some (.success value)) :
    (application setup leaks).handle initial.application
      ((runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ initial) =
      some (initial.application.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) true)
        (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success value))) := by
  rw [(runtime setup).reactiveApplication_handle_of_tokenValid leaks _ _
    ((runtime setup).windowEnvelope_tokenValid leaks owner event candidate _ initial ready)]
  exact handle_opening_eq (runtime setup) initial.application _ event candidate owner payload
    binding checks outputEq codeEq node ready timely rfl owned associated value valid
    (EventCode.binding_success_of_resolve_success binding checks true _ value resolved)
    _ resolved

section Resolution

variable (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
  (binding : FieldRef (graph setup).layout (.binding owner payload))
  (checks : List (GuardCheck (graph setup).layout payload))
  (outputEq : (graph setup).outputLayout event = .publication payload)
  (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
    ((graph setup).nodes event) = .resolve owner payload binding checks)
  (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
  (candidate : Handle (graph setup)) (value : L.Val payload)
  (unique : ∀ other : (graph setup).EventId, other = event)
  (before initial : (application setup leaks).Execution)
  (activation : initial ∈ (before.environmentStep (application setup leaks)
    (.activate owner)).support)
  (emptyTraffic : (application setup leaks).executionTraffic before = [])
  (ready : initial.application.config.cut.Ready event)
  (timely : initial.application.WithinDeadline (runtime setup) event)
  (serials : initial.network.SerialsBeforeNext)
  (published : initial.network.Satisfies fun message =>
    message.id ∈ initial.network.ledger.map Message.id)
  (owned : candidate.1 = owner)
  (valid : initial.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
  (associated : initial.application.accepted binding.field = some candidate)
  (resolved : EventCode.resolveOutput? binding checks true initial.application.config.store =
    some (.success value))
  (entered ticks : Nat) (activated : initial.application.activatedAt event = some entered)
  (due : (runtime setup).deadline event ≤ initial.application.clock + ticks - entered)
  (players : Player → (application setup leaks).Policy)
  (network : (runtime setup).NetworkPolicy leaks)

include binding checks codeEq node unique ready timely serials owned valid associated resolved
  entered activated due

private theorem resolution_frame_terminal
    (selected : Option (Fin 1)) (current final : (application setup leaks).Execution)
    (frame : (runtime setup).OpeningWindowFrame leaks owner event candidate ⟨payload, value⟩
      (initial.recall owner).length selected 1 initial current)
    (empty : selected = none → (application setup leaks).executionTraffic current = [])
    (packets : ∀ record ∈ (application setup leaks).executionTraffic current,
      record.envelope = (runtime setup).windowEnvelope leaks owner event candidate
        ⟨payload, value⟩ initial)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
      current).support) :
    final.application.config.cut.Terminal ∧
    resolutionPublicationReward event payload outputEq final =
      (if selected.isSome then 1 else 0) ∧
    ∀ record ∈ (application setup leaks).executionTraffic final,
      ((runtime setup).settledRecord leaks final).permits record.envelope = true := by
  have accepted := resolutionOpening_accepted owner event payload binding checks outputEq codeEq
    node candidate value initial ready timely owned valid associated resolved
  obtain ⟨state, _, _, receipts, _⟩ := frame.expiry (runtime setup) leaks owner event payload
    binding checks outputEq codeEq node candidate value initial current
      (initial.recall owner).length selected ready serials accepted entered ticks activated due
      players network final reached
  have traffic := resolution_tail_traffic players network event owner ticks current final reached
  cases selected with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at state receipts ⊢
      refine ⟨?_, ?_, ?_⟩
      · rw [state]
        exact complete_single_terminal event unique _ ready _ _
      · simp [resolutionPublicationReward, state, State.complete, cast_cast, cast_eq]
      · intro record member
        rw [traffic, empty rfl] at member
        exact (List.not_mem_nil member).elim
  | some slot =>
      simp only [Option.isSome_some, ↓reduceIte] at state receipts ⊢
      refine ⟨?_, ?_, ?_⟩
      · rw [state]
        exact complete_single_terminal event unique _ ready _ _
      · simp [resolutionPublicationReward, state, State.complete, cast_cast, cast_eq]
      · intro record member
        rw [traffic] at member
        rw [packets record member]
        let message := (runtime setup).windowEnvelope leaks owner event candidate
          ⟨payload, value⟩ initial
        apply SettledRecord.permits_of_accepted _ message event rfl
        · change (message.id, true) ∈ final.receipts
          rw [receipts]
          exact List.mem_append_right _ (by simp [message, windowEnvelope])
        · have call := reactiveHandle_call accepted
          obtain ⟨actual, _, previousReady, action, member⟩ := handle_config_mem_step
            (runtime setup) initial.application _ _ call
          have same := unique actual
          subst actual
          apply settledContent_of_pending initial.application final.application final.receipts
            message event rfl previousReady action
          · simpa only [state, State.complete] using member
          · change certifiedOpening message.payload = true ∧
              initial.application.publicView.openingGuardsAccepted message.payload = true
            refine ⟨by simp [message, windowEnvelope, certifiedOpening], ?_⟩
            apply (initial.application.publicView.openingGuardsAccepted_iff owner event payload
              binding checks outputEq codeEq node candidate ⟨payload, value⟩ _).mpr
            refine ⟨value, rfl, ?_⟩
            change GuardCheck.allAccepted? checks
              ((graph setup).publicStore initial.application.config.store) (.success value) = _
            rw [GuardCheck.allAccepted?_publicStore]
            exact EventCode.guards_pass_of_resolve_success binding checks true _ value resolved

include before activation emptyTraffic published

/-- Silence reaches the public failure output; an authentic protected opening
reaches success. Every actual packet is permitted by the final settled record.
The single-event hypothesis makes both branches terminal. -/
theorem resolutionTerminal_response
    (response : (application setup leaks).Action)
    (supported : response = ⟨none⟩ ∨ response =
      (runtime setup).windowOpening leaks event candidate ⟨payload, value⟩)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
      (initial.respond (application setup leaks) owner response)).support) :
    final.application.config.cut.Terminal ∧
    resolutionPublicationReward event payload outputEq final =
      resolutionTransmissionReward response ∧
    ∀ record ∈ (application setup leaks).executionTraffic final,
      ((runtime setup).settledRecord leaks final).permits record.envelope = true := by
  have traffic := resolution_response_traffic before initial owner activation emptyTraffic event
    candidate ⟨payload, value⟩ owned valid
  rcases supported with rfl | rfl
  · have frame := (OpeningWindowFrame.initial (runtime setup) leaks owner event candidate
        ⟨payload, value⟩ (none : Option (Fin 1)) initial serials published).waiting_response
        (runtime setup) leaks owner event candidate ⟨payload, value⟩
          (initial.recall owner).length none 0 initial initial owner ⟨none⟩ rfl (by rfl)
    have result := resolution_frame_terminal owner event payload binding checks outputEq codeEq
      node candidate value unique initial ready timely serials owned valid associated resolved
      entered ticks activated due
      players network none _ final (by simpa only [ite_true, Nat.zero_add] using frame)
      (fun _ => traffic.1) (by
        intro record member
        rw [traffic.1] at member
        exact (List.not_mem_nil member).elim)
      reached
    simpa only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      resolutionTransmissionReward] using result
  · have frame := (OpeningWindowFrame.initial (runtime setup) leaks owner event candidate
        ⟨payload, value⟩ (some (0 : Fin 1)) initial serials published).opening_response
        (runtime setup) leaks owner event candidate ⟨payload, value⟩
          (initial.recall owner).length 0 initial initial owned valid
    have result := resolution_frame_terminal owner event payload binding checks outputEq codeEq
      node candidate value unique initial ready timely serials owned valid associated resolved
      entered ticks activated due
      players network (some 0) _ final frame (by simp)
      (fun record member => by
        have inside := List.mem_map_of_mem (f := ReactiveApplication.TrafficRecord.envelope)
          member
        rw [traffic.2] at inside
        exact List.mem_singleton.mp inside) reached
    simpa only [Option.isSome_some, ↓reduceIte, resolutionTransmissionReward, windowOpening,
      reduceCtorEq] using result

/-- The same terminal audit draw leaves the entire realized payoff vector
equal to the response reward. Authentic partial observation suffices: no
positive detection or report-delivery rate is assumed for clean play. -/
theorem resolutionTerminal_settlement
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (response : (application setup leaks).Action)
    (supported : response = ⟨none⟩ ∨ response =
      (runtime setup).windowOpening leaks event candidate ⟨payload, value⟩)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
      (initial.respond (application setup leaks) owner response)).support) :
    TerminalAudit.settlement (resolutionTerminalPayoff owner event payload outputEq)
      ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
      deposit (some ⟨0, none, final⟩) =
        PMF.pure (fun who => if who = owner then resolutionTransmissionReward response else 0) := by
  have result := resolutionTerminal_response owner event payload binding checks outputEq codeEq
    node candidate value unique before initial activation emptyTraffic ready timely serials
    published owned valid associated resolved entered ticks activated due players network
    response supported final reached
  have clean : ∀ who, TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) (some ⟨0, none, final⟩) who = 0 := by
    intro who
    have noMiss := final.application.publicView.missedBindingBy_of_publications
      (fun other _ _ => by rw [unique other, outputEq]; simp) who
    unfold sourceServiceAudit
    rw [(runtime setup).serviceAudit_charge, noMiss]
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply (application setup leaks).sampledTrafficAudit_sound
    · exact authentic _
    · intro record member _
      exact result.2.2 record member
  rw [TerminalAudit.settlement_clean _ _ _ deposit _ clean]
  congr 1
  funext who
  simp only [resolutionTerminalPayoff, result.2.1]

/-- The actual supplied suffix law, including the terminal audit's joint
randomness, realizes the response-reward law for every response distribution
supported on the authentic opening and silence. -/
theorem resolutionTerminal_joint_law
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (law : PMF (application setup leaks).Action)
    (supported : ∀ response ∈ law.support, response = ⟨none⟩ ∨ response =
      (runtime setup).windowOpening leaks event candidate ⟨payload, value⟩) :
    resolutionAuditedSuffix owner event payload outputEq players network ticks initial sample
      deposit law =
      law.map (fun response who =>
        if who = owner then resolutionTransmissionReward response else 0) := by
  unfold resolutionAuditedSuffix
  rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro response member
  calc
    _ = ((runtime setup).runInteractionPlan leaks players network
        (.includeLatest event owner :: List.replicate ticks .tick ++ [.expire event])
          (initial.respond (application setup leaks) owner response)).bind
        (fun _ => PMF.pure (fun who =>
          if who = owner then resolutionTransmissionReward response else 0)) := by
      apply bind_congr_on_support _
      intro final reached
      exact resolutionTerminal_settlement owner event payload binding checks outputEq codeEq node
        candidate value unique before initial activation emptyTraffic ready timely serials
        published owned valid associated resolved entered ticks activated due players network
        sample authentic deposit response (supported response member) final reached
    _ = _ := PMF.bind_const _ _

/-- Choosing the authentic opening now has actual terminal audited payoff
one, independently of deposit size and authentic audit sampling. -/
theorem resolutionTerminal_opening_reward
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) :
    expect ((resolutionAuditedSuffix owner event payload outputEq players network ticks initial
      sample deposit (PMF.pure ((runtime setup).windowOpening leaks event candidate
        ⟨payload, value⟩))).map (fun payoffs => payoffs owner)) id = 1 := by
  rw [resolutionTerminal_joint_law owner event payload binding checks outputEq codeEq node
    candidate value unique before initial activation emptyTraffic ready timely serials
    published owned valid associated resolved entered ticks activated due players network
    sample authentic deposit _ (fun response member =>
      Or.inr ((PMF.mem_support_pure_iff _ _).mp member))]
  simp only [PMF.pure_map, expect_pure, id_eq, resolutionTransmissionReward,
    windowOpening, reduceCtorEq, ↓reduceIte]

end Resolution

section ResolutionPolicy

variable (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
  (binding : FieldRef (graph setup).layout (.binding owner payload))
  (checks : List (GuardCheck (graph setup).layout payload))
  (outputEq : (graph setup).outputLayout event = .publication payload)
  (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
    ((graph setup).nodes event) = .resolve owner payload binding checks)
  (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
  (candidate : Handle (graph setup)) (value : L.Val payload)
  (initial : (application setup leaks).Execution)
  (validState : initial.application.BindingInvariant)
  (recalled : initial.InputRecall (application setup leaks))
  (origins : (runtime setup).ResolutionEvidenceOrigins leaks initial)
  (ready : initial.application.config.cut.Ready event)
  (owned : candidate.1 = owner)
  (valid : initial.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
  (associated : initial.application.accepted binding.field = some candidate)
  (resolved : EventCode.resolveOutput? binding checks true initial.application.config.store =
    some (.success value))
  (unsent : (runtime setup).eventRecorded leaks (initial.recall owner) event = false)

include binding checks codeEq node validState recalled origins owned valid associated resolved
  unsent

private theorem resolution_canonical_true :
    (runtime setup).canonicalServiceDecision leaks owner (initial.recall owner)
      (initial.observe (application setup leaks) owner) event
        (cast (congrArg EventField.Action outputEq.symm) true) =
      (runtime setup).windowOpening leaks event candidate ⟨payload, value⟩ := by
  rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _
    (fun _ _ _ _ => by rw [node]; simp)]
  have resolves : ((graph setup).nodes event).resolutionField? = some binding.field := by
    have field := congrArg EventCode.resolutionField? codeEq
    rw [EventCode.resolutionField?_cast outputEq] at field
    exact field
  have normal := origins.opening_normal (runtime setup) leaks
    (resolution_field_injective setup.program) initial validState recalled owner event
      binding.field resolves candidate ⟨payload, value⟩ associated owned valid unsent
  have decision := (runtime setup).serviceDecision_successful_opening leaks initial recalled
    owner event payload binding checks outputEq codeEq node candidate value associated owned valid
      resolved
  have known : ReactiveApplication.ResponseMenu.knownPackets (initial.recall owner)
      (initial.observe (application setup leaks) owner) = initial.network.known owner :=
    ((application setup leaks).known_from_recall initial owner recalled).symm
  calc
    _ = ((runtime setup).reactiveNormalization leaks).action owner (initial.recall owner)
        (initial.observe (application setup leaks) owner)
          ((runtime setup).windowOpening leaks event candidate ⟨payload, value⟩) := by
      rw [decision]
      change (⟨some ((disclosureSubmission (.opening event candidate
        ⟨payload, value⟩)).normalizeReactive owner _ (initial.network.known owner))⟩ :
          (application setup leaks).Action) = _
      rw [← known]
      rfl
    _ = _ := normal

include ready in
/-- At a protected unrecorded actual resolution, source choices produce only
silence and the authentic opening. Recall and evidence provenance derive the
raw response's normal form; endpoint support is not assumed. -/
theorem sourceServiceResolution_opportunity_support
    (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
    (fits : initial.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceCanonicalOpportunity setup leaks bound profile owner event
      (initial.recall owner) (initial.observe (application setup leaks) owner)).support) :
    response = ⟨none⟩ ∨ response =
      (runtime setup).windowOpening leaks event candidate ⟨payload, value⟩ := by
  have opportunity : sourceServiceCanonicalOpportunity setup leaks bound profile owner event
      (initial.recall owner) (initial.observe (application setup leaks) owner) =
      sourceServiceCanonicalPolicy setup leaks profile owner (initial.recall owner)
        (initial.observe (application setup leaks) owner) := by
    unfold sourceServiceCanonicalOpportunity
    simp only [unsent, Bool.false_eq_true, ↓reduceIte]
    have fitView : PublicView.InclusionFitsDeadline (runtime setup) bound
        (initial.observe (application setup leaks) owner).application.publicView event := fits
    rw [ite_eq_left fitView]
    have kernel : (fun action : (application setup leaks).Action =>
        if action.transmission = none then (application setup leaks).silentPolicy
          (initial.recall owner) (initial.observe (application setup leaks) owner)
        else PMF.pure action) = PMF.pure := by
      funext action
      rcases action with ⟨transmission⟩
      cases transmission <;> rfl
    rw [kernel, PMF.bind_pure]
  rw [opportunity, sourceServiceCanonicalPolicy_at_event setup leaks profile owner initial event
    (ownTurn?_of_ready setup initial.application ready (nodeView_resolve_actor outputEq codeEq))
    (nodeView_resolve_actor outputEq codeEq)] at member
  obtain ⟨choice, _, rfl⟩ := PMF.support_map .. ▸ member
  let disclose : Bool := cast (congrArg EventField.Action outputEq) choice
  have choiceEq : choice = cast (congrArg EventField.Action outputEq.symm) disclose := by
    simp only [disclose, cast_cast, cast_eq]
  rw [choiceEq]
  cases disclose with
  | false =>
      left
      simp only [canonicalServiceDecision, canonicalReactiveDecision, node,
        reactiveResolutionPacket, cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
        disclosureSubmission_normalize_withhold]
      rfl
  | true =>
      exact Or.inr (resolution_canonical_true owner event payload binding checks outputEq codeEq
        node candidate value initial validState recalled origins owned valid associated resolved
          unsent)

include ready in
/-- The actual turn-counted behavioral mixture has the same two physical
response endpoints, for every timing law and every actual own transcript. -/
theorem sourceServiceResolution_turnPolicy_support
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (fits : initial.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceTurnPolicy setup leaks bound turns timing profile owner
      (initial.recall owner) (initial.observe (application setup leaks) owner)).support) :
    response = ⟨none⟩ ∨ response =
      (runtime setup).windowOpening leaks event candidate ⟨payload, value⟩ := by
  rw [sourceServiceTurnPolicy_turn setup leaks bound turns timing profile owner _ _ event
    (nodeView_resolve_actor outputEq codeEq)
    (ownTurn?_of_ready setup initial.application ready (nodeView_resolve_actor outputEq codeEq)),
    (application setup leaks).policyMixture_policy] at member
  obtain ⟨slot, _, chosen⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
  dsimp only [sourceServiceTurnFamily, ReactiveApplication.turnScheduledPolicy] at chosen
  split at chosen
  · exact sourceServiceResolution_opportunity_support owner event payload binding checks outputEq
      codeEq node candidate value initial validState recalled origins ready owned valid associated
      resolved unsent bound profile fits response chosen
  · exact Or.inl ((application setup leaks).silentPolicy_cases _ _ response chosen)

end ResolutionPolicy

section TwoSlot

variable (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
  (binding : FieldRef (graph setup).layout (.binding owner payload))
  (checks : List (GuardCheck (graph setup).layout payload))
  (outputEq : (graph setup).outputLayout event = .publication payload)
  (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
    ((graph setup).nodes event) = .resolve owner payload binding checks)
  (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
  (candidate : Handle (graph setup)) (value : L.Val payload)
  (unique : ∀ other : (graph setup).EventId, other = event)
  (before initial : (application setup leaks).Execution)
  (activation : initial ∈ (before.environmentStep (application setup leaks)
    (.activate owner)).support)
  (emptyTraffic : (application setup leaks).executionTraffic before = [])
  (validState : initial.application.BindingInvariant)
  (recalled : initial.InputRecall (application setup leaks))
  (origins : (runtime setup).ResolutionEvidenceOrigins leaks initial)
  (ready : initial.application.config.cut.Ready event)
  (timely : initial.application.WithinDeadline (runtime setup) event)
  (serials : initial.network.SerialsBeforeNext)
  (published : initial.network.Satisfies fun message =>
    message.id ∈ initial.network.ledger.map Message.id)
  (owned : candidate.1 = owner)
  (valid : initial.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
  (associated : initial.application.accepted binding.field = some candidate)
  (resolved : EventCode.resolveOutput? binding checks true initial.application.config.store =
    some (.success value))
  (unsent : (runtime setup).eventRecorded leaks (initial.recall owner) event = false)
  (entered ticks : Nat) (activated : initial.application.activatedAt event = some entered)
  (due : (runtime setup).deadline event ≤ initial.application.clock + ticks - entered)
  (players : Player → (application setup leaks).Policy)
  (network : (runtime setup).NetworkPolicy leaks)
  (bound : (graph setup).EventId → Nat) (profile : BehavioralProfile setup.program)
  (fits : initial.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
  (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
  (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
  (deposit : Player → ℝ)

include binding checks codeEq node candidate value unique before activation emptyTraffic
  validState recalled origins ready timely serials published owned valid associated resolved
  unsent entered activated due fits authentic

/-- The actual next-turn terminal audited payoff realizes the two-slot
posterior reward. The next activation occurs after the actual first silent
response; current inclusion protection is supplied explicitly. No equality
of the two source silent likelihoods is assumed. -/
theorem resolutionTerminal_twoSlot_reward
    (middle : (application setup leaks).Execution)
    (first : sourceServiceTurn setup leaks owner event (middle.recall owner)
      (middle.observe (application setup leaks) owner) = some 0)
    (positive : 0 < ((sourceServiceCanonicalOpportunity setup leaks bound profile owner event
      (middle.recall owner) (middle.observe (application setup leaks) owner)) ⟨none⟩).toReal)
    (beforeEq : before = middle.respond (application setup leaks) owner ⟨none⟩)
    (next : sourceServiceTurn setup leaks owner event (initial.recall owner)
      (initial.observe (application setup leaks) owner) = some 1)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1) :
    let app := application setup leaks
    let silent := ((sourceServiceCanonicalOpportunity setup leaks bound profile owner event
      (middle.recall owner) (middle.observe app owner)) ⟨none⟩).toReal
    let law := sourceServiceTurnPolicy setup leaks bound 1
      (geometricTiming setup 1 weight nonnegative bounded) profile owner (initial.recall owner)
        (initial.observe app owner)
    expect ((resolutionAuditedSuffix owner event payload outputEq players network ticks initial
      sample deposit law).map (fun payoffs => payoffs owner)) id =
      (weight / (silent * (1 - weight) + weight)) *
        (1 - ((sourceServiceCanonicalOpportunity setup leaks bound profile owner event
          (initial.recall owner) (initial.observe app owner)) ⟨none⟩).toReal) := by
  dsimp only
  have recallEq := congrFun ((application setup leaks).environmentStep_recall before initial
    (.activate owner) activation) owner
  rw [beforeEq] at recallEq
  let law := sourceServiceTurnPolicy setup leaks bound 1
    (geometricTiming setup 1 weight nonnegative bounded) profile owner (initial.recall owner)
      (initial.observe (application setup leaks) owner)
  have joint := resolutionTerminal_joint_law owner event payload binding checks outputEq codeEq
    node candidate value unique before initial activation emptyTraffic ready timely serials
    published owned valid associated resolved entered ticks activated due players network sample
    authentic deposit law (fun response supported =>
      sourceServiceResolution_turnPolicy_support owner event payload binding checks outputEq codeEq
        node candidate value initial validState recalled origins ready owned valid associated
        resolved unsent bound 1 _ profile fits response supported)
  have nextOriginal : sourceServiceTurn setup leaks owner event
      ((middle.respond (application setup leaks) owner ⟨none⟩).recall owner)
      (initial.observe (application setup leaks) owner) = some 1 := by
    rw [← recallEq]
    exact next
  calc
    _ = expect law resolutionTransmissionReward := by
      rw [joint, PMF.map_comp, expect_map]
      simp only [Function.comp_def, id_eq, ite_true]
    _ = _ := by
      have rate := sourceServiceTurnPolicy_first_silence_two_slots_reward middle first positive
        (nodeView_resolve_actor outputEq codeEq) weight nonnegative bounded
        (initial.observe (application setup leaks) owner) nextOriginal
      simpa only [← recallEq] using rate

/-- The gain from opening now is measured in the actual terminal audited
payoff, rather than an action reward. Initialization and legality of the
earlier information set remain separate obligations. -/
theorem resolutionTerminal_twoSlot_regret
    (middle : (application setup leaks).Execution)
    (first : sourceServiceTurn setup leaks owner event (middle.recall owner)
      (middle.observe (application setup leaks) owner) = some 0)
    (positive : 0 < ((sourceServiceCanonicalOpportunity setup leaks bound profile owner event
      (middle.recall owner) (middle.observe (application setup leaks) owner)) ⟨none⟩).toReal)
    (beforeEq : before = middle.respond (application setup leaks) owner ⟨none⟩)
    (next : sourceServiceTurn setup leaks owner event (initial.recall owner)
      (initial.observe (application setup leaks) owner) = some 1)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1) :
    let app := application setup leaks
    let silent := ((sourceServiceCanonicalOpportunity setup leaks bound profile owner event
      (middle.recall owner) (middle.observe app owner)) ⟨none⟩).toReal
    let law := sourceServiceTurnPolicy setup leaks bound 1
      (geometricTiming setup 1 weight nonnegative bounded) profile owner (initial.recall owner)
        (initial.observe app owner)
    expect ((resolutionAuditedSuffix owner event payload outputEq players network ticks initial
      sample deposit (PMF.pure ((runtime setup).windowOpening leaks event candidate
        ⟨payload, value⟩))).map (fun payoffs => payoffs owner)) id -
      expect ((resolutionAuditedSuffix owner event payload outputEq players network ticks initial
        sample deposit law).map (fun payoffs => payoffs owner)) id =
      1 - (weight / (silent * (1 - weight) + weight)) *
        (1 - ((sourceServiceCanonicalOpportunity setup leaks bound profile owner event
          (initial.recall owner) (initial.observe app owner)) ⟨none⟩).toReal) := by
  dsimp only
  rw [resolutionTerminal_opening_reward owner event payload binding checks outputEq codeEq node
    candidate value unique before initial activation emptyTraffic ready timely serials
    published owned valid associated resolved entered ticks activated due players network sample
    authentic deposit,
    resolutionTerminal_twoSlot_reward owner event payload binding checks outputEq codeEq node
      candidate value unique before initial activation emptyTraffic validState recalled origins
      ready timely serials published owned valid associated resolved unsent entered ticks activated
      due players network bound profile fits sample authentic deposit middle first positive beforeEq
      next weight nonnegative bounded]

end TwoSlot

end Vegas
