/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCompiledResolution
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Pending.ReactiveOpeningWindow
import Vegas.Pending.ReactiveAssociationPersistence
import Vegas.Pending.ReactiveServiceRecall
import Vegas.EventGraph.ResolutionProvenance
import Vegas.EventGraph.ResolutionFields
import Interaction.ReactiveMenuInvariant
import Interaction.ReactiveMenuRestriction

/-! # Opening certificates originate in an owner's resolution response

The retained menu issues certificates only with successful guarded openings.
Every network copy therefore identifies an accepted binding and a resolution
already recorded in that binding owner's response recall. This uses the
runtime's ideal certificate issuance and handle ownership rules; it does not
assert cryptographic key secrecy or identify a physical broadcaster.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A certificate's binding association and original resolution survive all
later network copies. The event is remembered by the certificate owner. -/
def ResolutionEvidence (execution : (runtime.reactiveApplication leaks).Execution)
    (fact : OpeningFact graph) : Prop :=
  ∃ event field, (graph.nodes event).resolutionField? = some field ∧
    execution.application.accepted field = some fact.handle ∧
    runtime.eventRecorded leaks (execution.recall fact.handle.1) event = true

def ResolutionEvidenceOrigins (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  execution.network.Satisfies fun message => ∀ fact,
    message.payload.evidence = some fact → runtime.ResolutionEvidence leaks execution fact

theorem ResolutionEvidence.respond
    {execution : (runtime.reactiveApplication leaks).Execution} {fact : OpeningFact graph}
    (origin : runtime.ResolutionEvidence leaks execution fact)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action) :
    runtime.ResolutionEvidence leaks
      (execution.respond (runtime.reactiveApplication leaks) who response) fact := by
  obtain ⟨event, field, node, accepted, recorded⟩ := origin
  refine ⟨event, field, node, ?_, runtime.eventRecorded_respond_of_recorded leaks
    execution who fact.handle.1 response event recorded⟩
  exact (congrFun (congrArg PublicView.accepted
    (runtime.reactive_respond_application leaks execution who response).2) field).trans accepted

theorem ResolutionEvidence.environment
    {execution next : (runtime.reactiveApplication leaks).Execution} {fact : OpeningFact graph}
    (origin : runtime.ResolutionEvidence leaks execution fact)
    (valid : execution.application.BindingInvariant)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep
      (runtime.reactiveApplication leaks) command).support) :
    runtime.ResolutionEvidence leaks next fact := by
  obtain ⟨event, field, node, accepted, recorded⟩ := origin
  refine ⟨event, field, node, ((runtime.reactiveAssociationInvariant leaks field
    fact.handle).environmentStep execution next command ⟨valid, accepted⟩ reached).2, ?_⟩
  rw [(runtime.reactiveApplication leaks).environmentStep_recall execution next command reached]
  exact recorded

/-- A fresh certificate emitted by a semantic decision comes from its actual
successful resolution and is recorded by that certificate's owner. -/
theorem serviceDecision_resolutionEvidence
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (valid : execution.application.BindingInvariant)
    (who : Player) (event : graph.EventId) (owned : graph.actor? event = some who)
    (choice : graph.Action event) (material : WitnessedSubmission graph)
    (submitted : runtime.serviceDecision leaks who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who) event choice =
        ⟨some (.submit material)⟩)
    (fact : OpeningFact graph)
    (issued : (material.emit
      ((runtime.reactiveApplication leaks).submit execution.application who material)
        who (execution.network.known who)).evidence = some fact) :
    runtime.ResolutionEvidence leaks
      (execution.respond (runtime.reactiveApplication leaks) who ⟨some (.submit material)⟩)
      fact := by
  let app := runtime.reactiveApplication leaks
  cases node : nodeView graph event with
  | sample payload outputEq codeEq =>
      simp only [serviceDecision, reactiveDecision, node,
        ReactiveApplication.SubmissionNormalization.action] at submitted
      cases submitted
  | bind actor payload outputEq codeEq =>
      cases fresh : reactiveFreshSlot (execution.observe app who).application with
      | none =>
          dsimp only [app] at fresh
          simp only [serviceDecision, reactiveDecision, node, fresh, Option.map_none,
            ReactiveApplication.SubmissionNormalization.action] at submitted
          cases submitted
      | some serial =>
          dsimp only [app] at fresh
          simp only [serviceDecision, reactiveDecision, node, fresh, Option.map_some,
            ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
            WitnessedSubmission.normalizeReactive, EvidenceRequest.normalize_none] at submitted
          cases submitted
          simp only [WitnessedSubmission.emit_eq_resolve, EvidenceRequest.resolve] at issued
          cases issued
  | resolve actor payload binding checks outputEq codeEq =>
      have actorEq : actor = who := by
        have codeActor := congrArg EventCode.actor codeEq
        rw [EventCode.actor_cast outputEq (graph.nodes event)] at codeActor
        exact Option.some.inj (codeActor.symm.trans owned)
      subst actor
      obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
          choice = cast (congrArg EventField.Action outputEq.symm) disclose :=
        ⟨cast (congrArg EventField.Action outputEq) choice, by
          simp only [cast_cast, cast_eq]⟩
      rcases runtime.serviceDecision_resolution_cases leaks who _ _ event who payload binding
        checks outputEq codeEq node disclose with quiet |
          ⟨candidate, value, evidence, resolved, associated, candidateOwner, shape⟩
      · rw [quiet] at submitted
        cases submitted
      · change EventCode.resolveOutput? binding checks true
          (graph.playerStore who execution.application.config.store) = _ at resolved
        rw [EventCode.resolveOutput?_playerStore] at resolved
        have stored := EventCode.binding_success_of_resolve_success binding checks true
          execution.application.config.store value resolved
        obtain ⟨actual, accepted, _, fixed⟩ := valid.success_provenance binding value stored
        change execution.application.accepted binding.field = some candidate at associated
        cases Option.some.inj (accepted.symm.trans associated)
        have positive : disclose = true := by
          cases disclose with
          | true => rfl
          | false =>
              simp only [serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
                cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
                disclosureSubmission_normalize_withhold] at submitted
              cases submitted
        subst disclose
        have canonical := runtime.serviceDecision_successful_opening leaks execution recalled
          who event payload binding checks outputEq codeEq node candidate value associated
            candidateOwner fixed resolved
        rw [canonical] at submitted
        cases submitted
        have packet := (WitnessedSubmission.normalizeReactive_emit runtime leaks
          execution.application who (execution.network.known who)
            (disclosureSubmission (.opening event candidate ⟨payload, value⟩))).trans
          (runtime.windowOpening_packet leaks who event candidate ⟨payload, value⟩
            execution.application (execution.network.known who) candidateOwner fixed)
        change (app.packet (app.submit execution.application who _) who
          (execution.network.known who) _).evidence = some fact at issued
        change app.packet (app.submit execution.application who _) who
          (execution.network.known who) _ = _ at packet
        have sameSubmit := (runtime.reactiveNormalization leaks).submit execution.application
          who (execution.network.known who)
            (disclosureSubmission (.opening event candidate ⟨payload, value⟩))
        change app.submit execution.application who _ = app.submit execution.application who _
          at sameSubmit
        dsimp only [reactiveNormalization] at sameSubmit
        rw [sameSubmit] at issued
        rw [packet] at issued
        cases Option.some.inj issued
        refine ⟨event, binding.field, ?_, ?_, ?_⟩
        · have field := congrArg EventCode.resolutionField? codeEq
          rw [EventCode.resolutionField?_cast outputEq] at field
          exact field
        · have same := (runtime.reactive_respond_application leaks execution who
            ⟨some (.submit ((disclosureSubmission (.opening event candidate ⟨payload, value⟩))
              |>.normalizeReactive who (app.observePlayer execution.application who)
                (execution.network.known who)))⟩).2
          exact (congrFun (congrArg PublicView.accepted same) binding.field).trans associated
        · rw [candidateOwner]
          exact runtime.eventRecorded_respond leaks execution who _ event rfl

/-- If each binding has one resolution, its certificate cannot precede the
owner's first response at that resolution. Network copies preserve this fact. -/
theorem ResolutionEvidenceOrigins.no_forward
    (unique : ∀ left right field,
      (graph.nodes left).resolutionField? = some field →
      (graph.nodes right).resolutionField? = some field → left = right)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (origins : runtime.ResolutionEvidenceOrigins leaks execution)
    (event : graph.EventId) (field : graph.Field)
    (resolves : (graph.nodes event).resolutionField? = some field)
    (candidate : Handle graph) (raw : Raw L)
    (associated : execution.application.accepted field = some candidate)
    (unsent : runtime.eventRecorded leaks (execution.recall candidate.1) event = false)
    (observer : Player) :
    EvidenceRequest.forwardingPacket (execution.network.known observer)
      (⟨candidate, raw⟩ : OpeningFact graph) = none := by
  apply EvidenceRequest.forwardingPacket_eq_none
  intro message known carried
  obtain ⟨prior, priorField, node, accepted, recorded⟩ :=
    origins.known observer message known ⟨candidate, raw⟩ carried
  have fieldEq := valid.accepted_injective priorField field candidate accepted associated
  subst priorField
  have eventEq := unique prior event field node resolves
  subst prior
  rw [unsent] at recorded
  cases recorded

/-- At its first resolution response the owned certificate request is already
the semantic normal form. This proves equality of raw response recall too. -/
theorem ResolutionEvidenceOrigins.opening_normal
    (unique : ∀ left right field,
      (graph.nodes left).resolutionField? = some field →
      (graph.nodes right).resolutionField? = some field → left = right)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (origins : runtime.ResolutionEvidenceOrigins leaks execution)
    (who : Player) (event : graph.EventId) (field : graph.Field)
    (resolves : (graph.nodes event).resolutionField? = some field)
    (candidate : Handle graph) (raw : Raw L)
    (associated : execution.application.accepted field = some candidate)
    (owned : candidate.1 = who)
    (fixed : execution.application.candidates.lookup candidate = .openable raw)
    (unsent : runtime.eventRecorded leaks (execution.recall who) event = false) :
    (runtime.reactiveNormalization leaks).action who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who)
        (runtime.windowOpening leaks event candidate raw) =
      runtime.windowOpening leaks event candidate raw := by
  let app := runtime.reactiveApplication leaks
  have unavailable := origins.no_forward runtime leaks unique execution valid event field
    resolves candidate raw associated (by simpa only [owned] using unsent) who
  have known : ReactiveApplication.ResponseMenu.knownPackets (execution.recall who)
      (execution.observe app who) = execution.network.known who :=
    (app.known_from_recall execution who recalled).symm
  have localFixed : execution.application.candidates.lookup (who, candidate.2) =
      .openable raw := by simpa only [← owned, Prod.mk.eta] using fixed
  simp only [ReactiveApplication.SubmissionNormalization.action, windowOpening,
    reactiveNormalization, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive_none, disclosureSubmission, Submission.candidateAfter_opening]
  rw [known]
  exact congrArg (fun evidence => (⟨some (.submit ⟨⟨.opening event candidate raw, none⟩,
    evidence⟩)⟩ : app.Action)) (EvidenceRequest.normalize_owned_of_no_forward who
      (fun slot => execution.application.candidates.lookup (who, slot))
      (execution.network.known who) ⟨candidate, raw⟩ owned localFixed unavailable)

variable [Fintype Player]

theorem MessageBounds.compiled_resolutionEvidence (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (valid : execution.application.BindingInvariant)
    (who : Player) (material : WitnessedSubmission graph)
    (member : (⟨some (.submit material)⟩ : (runtime.reactiveApplication leaks).Action) ∈
      bounds.compiledActions runtime leaks who (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who))
    (fact : OpeningFact graph)
    (issued : (material.emit
      ((runtime.reactiveApplication leaks).submit execution.application who material)
        who (execution.network.known who)).evidence = some fact) :
    runtime.ResolutionEvidence leaks
      (execution.respond (runtime.reactiveApplication leaks) who ⟨some (.submit material)⟩)
      fact := by
  classical
  have permitted := (Finset.mem_inter.mp member).1
  rcases Finset.mem_union.mp permitted with decision | replay
  · obtain ⟨chosen, _⟩ := Finset.mem_filter.mp decision
    simp only [MessageBounds.decisionActions] at chosen
    split at chosen
    · simp only [Finset.mem_singleton] at chosen
      cases chosen
    · rename_i event turn
      split at chosen
      · rename_i allowed
        split at chosen
        · simp only [Finset.mem_singleton] at chosen
          cases chosen
        all_goals
          obtain ⟨choice, _, equal⟩ := Finset.mem_image.mp chosen
          exact runtime.serviceDecision_resolutionEvidence leaks execution recalled valid who
            event allowed.1 _ material equal fact issued
      · simp only [Finset.mem_singleton] at chosen
        cases chosen
  · have transport := (runtime.reactiveApplication leaks).replayPolicy_cases _ _ _
      (((runtime.reactiveApplication leaks).mem_replayActions_iff _ _ _).mp replay)
    rcases transport with impossible | ⟨_, impossible⟩ <;> cases impossible

theorem resolutionEvidenceOrigins_respond (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (valid : execution.application.BindingInvariant)
    (origin : runtime.ResolutionEvidenceOrigins leaks execution)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who)) :
    runtime.ResolutionEvidenceOrigins leaks
      (execution.respond (runtime.reactiveApplication leaks) who response) := by
  have prior := origin.mono fun _ carried fact issued =>
    (carried fact issued).respond runtime leaks who response
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact prior
  | some transmission =>
      cases transmission with
      | replay id => exact prior.replay who id
      | submit material =>
          apply prior.submit who
            ((runtime.reactiveApplication leaks).packet
              ((runtime.reactiveApplication leaks).submit execution.application who material)
                who (execution.network.known who) material)
          exact fun fact issued => bounds.compiled_resolutionEvidence runtime leaks execution
            recalled valid who material member fact issued

omit [Fintype Player] in
theorem resolutionEvidenceOrigins_environment
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (origin : runtime.ResolutionEvidenceOrigins leaks execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep
      (runtime.reactiveApplication leaks) command).support) :
    runtime.ResolutionEvidenceOrigins leaks next := by
  have prior := origin.mono fun _ carried fact issued =>
    (carried fact issued).environment runtime leaks valid command reached
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact prior
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact prior.learn who selected
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      have kept := prior.includePending id
      cases found : execution.network.lookup id <;>
        simpa only [ResolutionEvidenceOrigins, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found] using kept
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact prior

/-- Every lawful execution of a service plan keeps the binding invariant, input
recall and authentic resolution origins. -/
theorem resolutionEvidenceOrigins_run (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (valid : initial.application.BindingInvariant)
    (recalled : initial.InputRecall (runtime.reactiveApplication leaks))
    (origin : runtime.ResolutionEvidenceOrigins leaks initial)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network plan initial).support) :
    final.application.BindingInvariant ∧ final.InputRecall (runtime.reactiveApplication leaks) ∧
      runtime.ResolutionEvidenceOrigins leaks final := by
  let app := runtime.reactiveApplication leaks
  have invariant : app.PolicyInvariant players (fun execution =>
      execution.application.BindingInvariant ∧ execution.InputRecall app ∧
        runtime.ResolutionEvidenceOrigins leaks execution) := {
    respond := fun execution who action valid member =>
      ⟨(runtime.reactiveBindingInvariant leaks).respond execution who action valid.1,
        app.respond_inputRecall execution who action valid.2.1,
        runtime.resolutionEvidenceOrigins_respond leaks bounds execution valid.2.1 valid.1
          valid.2.2 who action (lawful who _ _ action member)⟩
    environment := fun execution next command valid reached =>
      ⟨(runtime.reactiveBindingInvariant leaks).environmentStep execution next command
        valid.1 reached, app.environment_inputRecall execution next command valid.2.1 reached,
        runtime.resolutionEvidenceOrigins_environment leaks execution next valid.1 valid.2.2
          command reached⟩ }
  exact runtime.runInteractionPlan_preserves leaks players network _ invariant plan initial final
    ⟨valid, recalled, origin⟩ reached

/-- Every legal prefix of any sub-menu of the compiled responses has authentic
resolution origins. This ranges over all policies and scheduler behavior. -/
theorem resolutionEvidenceOrigins_history (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (included : menu.IncludedIn (bounds.compiledMenu runtime leaks))
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (setup : ∀ state ∈ initial.support, state.BindingInvariant)
    {state} (trace : (menu.protocol initial horizon scheduler).Trace state) :
    ReactiveApplication.serviceInvariant (runtime.ResolutionEvidenceOrigins leaks) state := by
  let app := runtime.reactiveApplication leaks
  have invariant : menu.ServiceInvariant scheduler (fun execution =>
      execution.application.BindingInvariant ∧ execution.InputRecall app ∧
        runtime.ResolutionEvidenceOrigins leaks execution) := {
    respond := fun execution who response valid member =>
      ⟨(runtime.reactiveBindingInvariant leaks).respond execution who response valid.1,
        app.respond_inputRecall execution who response valid.2.1,
        runtime.resolutionEvidenceOrigins_respond leaks bounds execution valid.2.1 valid.1
          valid.2.2 who response (included who _ _ member)⟩
    environment := fun execution next command valid _ reached =>
      ⟨(runtime.reactiveBindingInvariant leaks).environmentStep execution next command
        valid.1 reached, app.environment_inputRecall execution next command valid.2.1 reached,
        runtime.resolutionEvidenceOrigins_environment leaks execution next valid.1 valid.2.2
          command reached⟩ }
  have result := invariant.history initial horizon (fun state supported =>
    ⟨setup state supported, app.initial_inputRecall state, MessageNetwork.Satisfies.empty⟩) trace
  cases state with
  | none => trivial
  | some control => exact result.2.2

end Vegas.EventGraphRuntime
