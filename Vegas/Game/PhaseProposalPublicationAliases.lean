/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalUnflagged
import Vegas.Game.PhaseExclusionPayoff
import Interaction.ReactiveResponseEvaluation
import Interaction.ReactiveAliasLaw
import Vegas.Pending.PhaseResponseAliases

/-! # Literal opening aliases and their actual physical continuations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

/-- Choosing the canonical representative uses the same finite response
classes whenever the original traffic and submission count agree. -/
theorem phaseProposalUnflaggedPolicy_congr_input
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (first second : List (app).PlayerEntry) (view : (app).PlayerView)
    (outputs : (app).outputs first = (app).outputs second)
    (serial : (app).submissionCount first = (app).submissionCount second) :
    phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who first view =
      phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who second view := by
  classical
  have menus := PhaseCount.onePacketActions_congr_input runtime leaks bounds who first second view
    outputs serial
  have packets (material : WitnessedSubmission (serviceGraph setup mode)) :
      PhaseCount.localEnvelope runtime leaks who first view material =
        PhaseCount.localEnvelope runtime leaks who second view material := by
    unfold PhaseCount.localEnvelope ReactiveApplication.ResponseMenu.knownPackets
    rw [outputs, serial]
  have base := phaseProposalBasePolicy_congr_input setup mode runtime leaks bounds plan values
    PhaseProposalRates.zero who first second view outputs serial
  let compute (allowed : Finset (app).Action)
      (wire : WitnessedSubmission (serviceGraph setup mode) →
        CommitAttemptPacket (serviceGraph setup mode))
      (law : PMF (app).Action) (covered : ∀ response ∈ law.support, response ∈ allowed) :
      PMF (app).Action :=
    let classify (response : {response : (app).Action // response ∈ allowed}) :=
      (response.val.transmission.bind PhaseProposal.bindingPreparation,
        response.val.transmission.map wire)
    let project := fun response =>
      (⟨classify response, response, rfl⟩ : Set.range classify)
    let canonical := fun chosen : Set.range classify => Classical.choose chosen.property
    let selected := law.bindOnSupport fun response supported =>
      PMF.pure (⟨response, covered response supported⟩ :
        {response : (app).Action // response ∈ allowed})
    ((selected.map project).map canonical).map Subtype.val
  change compute (PhaseCount.onePacketActions runtime leaks bounds who first view)
      (fun material => (PhaseCount.localEnvelope runtime leaks who first view material).payload)
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values PhaseProposalRates.zero
        who first view)
      (phaseProposalBasePolicy_covered setup mode runtime leaks bounds plan values
        PhaseProposalRates.zero who first view) =
    compute (PhaseCount.onePacketActions runtime leaks bounds who second view)
      (fun material => (PhaseCount.localEnvelope runtime leaks who second view material).payload)
      (phaseProposalBasePolicy setup mode runtime leaks bounds plan values PhaseProposalRates.zero
        who second view)
      (phaseProposalBasePolicy_covered setup mode runtime leaks bounds plan values
        PhaseProposalRates.zero who second view)
  congr 1
  funext material
  exact congrArg (fun packet => packet.payload) (packets material)

/-- The original full-history runner projects under operational normalization.
Every current raw response is still integrated with its literal probability. -/
theorem phaseProposalUnflagged_normalized_continuation
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (fuel : Nat) (current : ((menu).protocol initial horizon scheduler).History) :
    let normal := PhaseCount.normalization runtime leaks
    let stable := fun who past view => PhaseCount.onePacketActions_recall runtime leaks bounds
      normal who who past view
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let native := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let projected := fun who => (normal.menu menu).restrictPolicy initial horizon scheduler who
      (fun past view => (players who past view).map (normal.action who past view))
    (((menu).information initial horizon scheduler).runBehavioralFrom native fuel current).map
        (normal.history menu stable initial horizon scheduler) =
      ((normal.menu menu).information initial horizon scheduler).runBehavioralFrom projected fuel
        (normal.history menu stable initial horizon scheduler current) := by
  classical
  intro normal stable players native projected
  have admitted := phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values
  have projectedCovered (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
      (response : (app).Action)
      (supported : response ∈ ((players who past view).map
        (normal.action who past view)).support) :
      response ∈ (normal.menu menu).actions who past view := by
    obtain ⟨raw, selected, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact (normal.menu_mem menu who past view _).mpr ⟨raw, admitted who past view raw selected, rfl⟩
  have projects (who : Player) (observed : (app).Info) :
      (native who observed).map (normal.choice menu stable initial horizon scheduler who observed) =
        projected who (normal.info who observed) := by
    apply pmf_map_injective Subtype.val_injective
    rw [PMF.map_comp]
    cases observed with
    | none => rfl
    | some pair =>
        rcases pair with ⟨past, view⟩
        change (((menu).restrictPolicy initial horizon scheduler who (players who)
          (some (past, view))).map (fun choice =>
            normal.optionChoice who (some (past, view)) choice.val)) =
          ((normal.menu menu).restrictPolicy initial horizon scheduler who
            (fun past view => (players who past view).map (normal.action who past view))
              (some (normal.recall who past, view))).map Subtype.val
        rw [show (fun choice => normal.optionChoice who (some (past, view)) choice.val) =
          (normal.optionChoice who (some (past, view))) ∘ Subtype.val from rfl, ← PMF.map_comp]
        rw [(menu).restrictPolicy_map_val initial horizon scheduler who (players who) past view
          (admitted who past view)]
        rw [(normal.menu menu).restrictPolicy_map_val initial horizon scheduler who _
          (normal.recall who past) view (projectedCovered who (normal.recall who past) view)]
        have unchanged : players who (normal.recall who past) view = players who past view :=
          phaseProposalUnflaggedPolicy_congr_input setup mode runtime leaks bounds plan values
            who _ _ view (normal.recall_outputs who past)
              (normal.recall_submissionCount who past)
        rw [unchanged]
        simp only [PMF.map_comp, Function.comp_def,
          ReactiveApplication.SubmissionNormalization.optionChoice,
          Option.map_some, normal.action_recall]
  exact normal.runBehavioral_projection menu stable initial horizon scheduler native projected
    projects fuel current

/-- Every nonsilent counted opening has the same operational normal form.
The actual ready request fixes its handle, value and disclosed certificate. -/
theorem phaseProposal_opening_alias_normalized_eq
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (output : (serviceGraph setup mode).outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode (serviceGraph setup mode).layout) output)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve who payload binding checks output code)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (first second : WitnessedSubmission (serviceGraph setup mode))
    (firstMember : (⟨some first⟩ : (app).Action) ∈ (menu).actions who
      (execution.recall who) (execution.observe app who))
    (secondMember : (⟨some second⟩ : (app).Action) ∈ (menu).actions who
      (execution.recall who) (execution.observe app who)) :
    let normal := PhaseCount.normalization runtime leaks
    normal.action who (execution.recall who) (execution.observe app who) ⟨some first⟩ =
      normal.action who (execution.recall who) (execution.observe app who) ⟨some second⟩ := by
  classical
  intro normal
  obtain ⟨candidate, value, call, stored, accepted, _lookup⟩ :=
    PhaseCount.onePacket_opening_shape runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who
        execution trace event payload binding checks output code node request first firstMember
  obtain ⟨other, otherValue, otherCall, otherStored, otherAccepted, _otherLookup⟩ :=
    PhaseCount.onePacket_opening_shape runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who
        execution trace event payload binding checks output code node request second secondMember
  have sameHandle : other = candidate := Option.some.inj (otherAccepted.symm.trans accepted)
  have sameValue : otherValue = value := by
    have same := Option.some.inj (otherStored.symm.trans stored)
    injection same
  subst other
  subst otherValue
  let past := execution.recall who
  let view := execution.observe app who
  let known := (ReactiveApplication.ResponseMenu.knownPackets past view).map
    PhaseCount.nativeMessage
  have canonical (material : WitnessedSubmission (serviceGraph setup mode))
      (member : (⟨some material⟩ : (app).Action) ∈ (menu).actions who past view)
      (named : material.call.packet = .opening event candidate ⟨payload, value⟩) :
      normal.normalize who view.application
        (ReactiveApplication.ResponseMenu.knownPackets past view) material =
      ⟨⟨.opening event candidate ⟨payload, value⟩, none⟩,
        EvidenceRequest.canonical known (some ⟨candidate, ⟨payload, value⟩⟩)⟩ := by
    have allowed : PhaseCount.permits ((app).outputs past)
        (PhaseCount.localEnvelope runtime leaks who past view material) = true := by
      rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds who past view _).mp member).2
        with impossible | ⟨other, sent, permitted⟩
      · cases impossible
      · cases Option.some.inj sent
        exact permitted
    let message := PhaseCount.localEnvelope runtime leaks who past view material
    have correct := ((PhaseCount.permits_eq_true_iff _ _).mp allowed).2.1
    have exactCall : message.payload.packet.call = .opening event candidate ⟨payload, value⟩ :=
      (PhaseCount.maskPacket_call _ _).trans named
    unfold CountCallCorrect at correct
    dsimp only [PhaseCount.nativeMessage] at correct
    rw [exactCall] at correct
    obtain ⟨certified, _resolves⟩ := correct
    have physical : message.payload.packet.evidence = some ⟨candidate, ⟨payload, value⟩⟩ := by
      obtain ⟨otherEvent, otherHandle, otherRaw, token, packetEq⟩ :=
        (certifiedOpening_iff _).mp certified
      have calls := Payload.opening.inj
        (exactCall.symm.trans (congrArg WitnessedPacket.call packetEq))
      simpa only [← calls.2.1, ← calls.2.2] using
        congrArg WitnessedPacket.evidence packetEq
    have evidence : material.evidence.resolve who
        (material.call.candidateAfter who view.application.1.candidates) known =
          some ⟨candidate, ⟨payload, value⟩⟩ := by
      have unmask : message.payload.packet.evidence = material.evidence.resolve who
          (material.call.candidateAfter who view.application.1.candidates) known := by
        dsimp only [message, PhaseCount.localEnvelope, PhaseCount.maskPacket]
        split <;> split <;> rfl
      exact unmask.symm.trans physical
    change (⟨material.call.normalizeReactive who view.application.1,
      material.evidence.normalize who
        (material.call.candidateAfter who view.application.1.candidates) known⟩ :
          WitnessedSubmission (serviceGraph setup mode)) = _
    rw [EvidenceRequest.normalize, evidence]
    rcases material with ⟨⟨packet, preparation⟩, request⟩
    dsimp only at named ⊢
    subst packet
    simp only [Submission.normalizeReactive, openingEffective, ↓reduceIte]
  have firstNormalized := canonical first firstMember call
  have secondNormalized := canonical second secondMember otherCall
  change (⟨some (normal.normalize who view.application
    (ReactiveApplication.ResponseMenu.knownPackets past view) first)⟩ : (app).Action) =
      ⟨some (normal.normalize who view.application
        (ReactiveApplication.ResponseMenu.knownPackets past view) second)⟩
  rw [firstNormalized, secondNormalized]

/-- The existing history projection identifies the normalized physical
finish law from the supplied original counted history. -/
theorem phaseProposalUnflagged_normalized_finish
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (current : ((menu).protocol initial horizon scheduler).History) :
    let normal := PhaseCount.normalization runtime leaks
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    ((app).finish initial horizon scheduler players current.state).map normal.state =
      (app).finish initial horizon scheduler
        (fun who past view => (players who past view).map (normal.action who past view))
          (normal.state current.state) := by
  intro normal players
  let stable := fun who past view => PhaseCount.onePacketActions_recall runtime leaks bounds
    normal who who past view
  let native := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
  let projected := fun who => (normal.menu menu).restrictPolicy initial horizon scheduler who
    (fun past view => (players who past view).map (normal.action who past view))
  have covered := phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values
  have projectedCovered (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
      (response : (app).Action) (supported : response ∈ ((players who past view).map
        (normal.action who past view)).support) :
      response ∈ (normal.menu menu).actions who past view := by
    obtain ⟨raw, selected, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact (normal.menu_mem menu who past view _).mpr ⟨raw, covered who past view raw selected, rfl⟩
  have decoded : (menu).decodeProfile initial horizon scheduler native = players := by
    funext who
    exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler who _ (covered who)
  have projectedDecoded : (normal.menu menu).decodeProfile initial horizon scheduler projected =
      fun who past view => (players who past view).map (normal.action who past view) := by
    funext who
    exact (normal.menu menu).decode_restrictPolicy_of_covered initial horizon scheduler who _
      (projectedCovered who)
  have depth := (app).trace_bound initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler current.trace)
  have sufficient : (app).rank horizon current.state ≤ 2 * horizon + 1 := by
    omega
  have normalSufficient : (app).rank horizon (normal.state current.state) ≤ 2 * horizon + 1 := by
    cases stateEq : current.state <;>
      simp only [stateEq, ReactiveApplication.SubmissionNormalization.state,
        Option.map_none, Option.map_some, ReactiveApplication.rank] at sufficient ⊢ <;>
      exact sufficient
  have law := phaseProposalUnflagged_normalized_continuation setup mode runtime leaks bounds plan
    values initial horizon scheduler (2 * horizon + 1) current
  have mapped := congrArg (PMF.map History.state) law
  rw [PMF.map_comp] at mapped
  have presentation := (menu).run_eq_finish initial horizon scheduler native
    (2 * horizon + 1) current sufficient
  have normalizedPresentation := (normal.menu menu).run_eq_finish initial horizon scheduler
    projected (2 * horizon + 1) (normal.history menu stable initial horizon scheduler current)
      normalSufficient
  rw [decoded] at presentation
  rw [projectedDecoded] at normalizedPresentation
  calc
    _ = (((menu).information initial horizon scheduler).runBehavioralFrom native
        (2 * horizon + 1) current).map (normal.state ∘ History.state) := by
      rw [← presentation, PMF.map_comp]
    _ = _ := mapped.trans normalizedPresentation

/-- Two legal nonsilent openings at the same actual request have identical
payoff laws under the literal future baseline. Raw current recalls may differ. -/
theorem phaseProposal_opening_alias_finish_payoff_eq
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (output : (serviceGraph setup mode).outputLayout event = .publication payload)
    (code : cast (congrArg (EventCode (serviceGraph setup mode).layout) output)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve who payload binding checks output code)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (first second : WitnessedSubmission (serviceGraph setup mode))
    (firstMember : (⟨some first⟩ : (app).Action) ∈ (menu).actions who
      (execution.recall who) (execution.observe app who))
    (secondMember : (⟨some second⟩ : (app).Action) ∈ (menu).actions who
      (execution.recall who) (execution.observe app who))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    let payoff := fun state => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
      state who
    ((app).finish (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler players
      (some ⟨remaining, none, execution.respond app who ⟨some first⟩⟩)).map payoff =
    ((app).finish (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler players
      (some ⟨remaining, none, execution.respond app who ⟨some second⟩⟩)).map payoff := by
  classical
  intro players payoff
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let normal := PhaseCount.normalization runtime leaks
  let joint := fun material owner => if owner = who then some (⟨some material⟩ : (app).Action)
    else none
  have legal (material : WitnessedSubmission (serviceGraph setup mode))
      (offered : (⟨some material⟩ : (app).Action) ∈ (menu).actions who
        (execution.recall who) (execution.observe app who)) :
      ((menu).protocol initial horizon scheduler).Legal
        (some ⟨remaining, some who, execution⟩) (joint material) := by
    constructor
    · simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
    · intro owner
      by_cases same : owner = who
      · subst owner
        simpa [joint, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor, ReactiveApplication.ResponseMenu.available] using offered
      · simp [joint, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
          same, Ne.symm same]
  have realized (material : WitnessedSubmission (serviceGraph setup mode)) :
      some (⟨remaining, none, execution.respond app who ⟨some material⟩⟩ : (app).Control) ∈
      ((app).transition initial horizon scheduler (some ⟨remaining, some who, execution⟩)
        (joint material)).support := by
    change _ ∈ (PMF.pure _).support
    simp only [joint, ↓reduceIte, Option.getD_some, PMF.mem_support_pure_iff _ _]
  let firstTrace := trace.extend (joint first) (legal first firstMember) (realized first)
  let secondTrace := trace.extend (joint second) (legal second secondMember) (realized second)
  have normalized := phaseProposal_opening_alias_normalized_eq setup mode runtime leaks bounds
    plan inputs horizon scheduler remaining who execution trace event payload binding checks
      output code node request first second firstMember secondMember
  have valid := (app).history_inputRecall initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler trace)
  have executions : normal.execution (execution.respond app who ⟨some first⟩) =
      normal.execution (execution.respond app who ⟨some second⟩) := by
    rw [normal.execution_respond execution who ⟨some first⟩ valid,
      normal.execution_respond execution who ⟨some second⟩ valid, normalized]
  have states : normal.state (some ⟨remaining, none, execution.respond app who ⟨some first⟩⟩) =
      normal.state (some ⟨remaining, none, execution.respond app who ⟨some second⟩⟩) :=
    congrArg (fun next => some (⟨remaining, none, next⟩ : (app).Control)) executions
  have firstLaw := phaseProposalUnflagged_normalized_finish setup mode runtime leaks bounds plan
    values initial horizon scheduler ⟨_, firstTrace⟩
  have secondLaw := phaseProposalUnflagged_normalized_finish setup mode runtime leaks bounds plan
    values initial horizon scheduler ⟨_, secondTrace⟩
  have ignores : payoff ∘ normal.state = payoff := by
    funext state
    cases state <;> rfl
  calc
    _ = (((app).finish initial horizon scheduler players
        (some ⟨remaining, none, execution.respond app who ⟨some first⟩⟩)).map
          normal.state).map payoff := by
      rw [PMF.map_comp, ignores]
    _ = _ := by rw [firstLaw, states, ← secondLaw, PMF.map_comp, ignores]

end Vegas
