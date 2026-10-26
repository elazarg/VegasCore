/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseClientLaw
import Vegas.Source.CommitRecoveryDisclosureAliases
import Vegas.Source.RegistryFailureExtension
import Vegas.Compile.EventGraphEvaluation

/-! # Exact first opening encoders for arbitrary source clients -/

noncomputable section

namespace Vegas.SourcePhaseClient

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (serviceGraph setup .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket (serviceGraph setup .sequential)))
  (bounds : MessageBounds (serviceGraph setup .sequential))

local notation "G" => serviceGraph setup EventGraph.ExecutionMode.sequential
local notation "app" => phaseApplication runtime leaks
local notation "counted" => PhaseCount.onePacketMenu runtime leaks bounds

omit [Fintype Player] in
/-- The privacy guard is evaluated from the actual own observation, with
exactly the output of the complete physical store, including deferred checks. -/
theorem effectiveOpening_read (execution : (app).Execution)
    {who : Player} {payload : L.Ty}
    (binding : FieldRef (G).layout (.binding who payload))
    (checks : List (GuardCheck (G).layout payload)) (disclose : Bool) :
    effectiveOpening setup runtime leaks binding checks (execution.observe app who) disclose =
      match EventCode.resolveOutput? binding checks disclose
        execution.application.current.native.config.store with
      | some (.success _) => true
      | _ => false := by
  unfold effectiveOpening
  change (match EventCode.resolveOutput? binding checks disclose
    ((G).playerStore who execution.application.current.native.config.store) with
    | some (.success _) => true | _ => false) = _
  rw [EventCode.resolveOutput?_playerStore]

omit [Fintype Player] in
/-- Compilation and the actual registry failure extension identify local
prevalidation with the original source effective disclosure. No source history
or hidden store is selected by the physical policy. -/
theorem effectiveOpening_eq_source (execution : (app).Execution)
    {Γ : SourceCtx Player L} {published name : VarId} {who : Player} {payload : L.Ty}
    (refs : ContextRefs (G).layout Γ) (source : SourceProgram.Config Player L Γ)
    (registry : Registry Γ) (selected : HasVar Γ name (.commitment who payload))
    (agree : refs.Agrees source.state execution.application.current.native.config.store)
    (guards : Registry.FailureExtension source.registry registry source.state)
    (failures : Revelations.PreservesFailures source.revelations source.state)
    (unique : (Γ.map Prod.fst).Nodup) (disclose : Bool) :
    effectiveOpening setup runtime leaks (refs.get selected)
        (compileChecks (published := published) refs registry source.revelations selected)
          (execution.observe app who) disclose =
      effectiveDisclosure published selected source disclose := by
  let store := execution.application.current.native.config.store
  let checks := compileChecks (published := published) refs registry source.revelations selected
  have evaluated : (EventCode.resolve who payload (refs.get selected) checks).eval? disclose store =
      some (PMF.pure (disclosureResult published selected source disclose)) := by
    rw [compileResolve_eval? refs registry source.revelations source.state store agree selected
      disclose]
    have exactChecks := guards.completedBy_all_eq source.revelations failures unique selected
      (published := published) disclose
    dsimp only at exactChecks
    dsimp only [disclosureResult, revealSuccessor, Env.cons_get_here]
    rw [exactChecks]
  have resolved : EventCode.resolveOutput? (refs.get selected) checks disclose store =
      some (disclosureResult published selected source disclose) := by
    change (EventCode.resolveOutput? (refs.get selected) checks disclose store).map PMF.pure = _
      at evaluated
    cases found : EventCode.resolveOutput? (refs.get selected) checks disclose store with
    | none => simp only [found, Option.map_none, reduceCtorEq] at evaluated
    | some result =>
        have same : PMF.pure result =
            PMF.pure (disclosureResult published selected source disclose) :=
          Option.some.inj (by simpa only [found, Option.map_some] using evaluated)
        have reached : result ∈ (PMF.pure
            (disclosureResult published selected source disclose)).support := by
          rw [← same]
          exact (PMF.mem_support_pure_iff _ _).mpr rfl
        exact congrArg some ((PMF.mem_support_pure_iff _ _).mp reached)
  rw [effectiveOpening_read]
  change (match EventCode.resolveOutput? (refs.get selected) checks disclose store with
    | some (.success _) => true | _ => false) = _
  rw [resolved]
  unfold effectiveDisclosure
  cases disclosureResult published selected source disclose <;> rfl

private theorem moveResponse_opening (who : Player) (event : (G).EventId) (payload : L.Ty)
    (binding : FieldRef (G).layout (.binding who payload))
    (checks : List (GuardCheck (G).layout payload))
    (outputEq : (G).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (G).layout) outputEq) ((G).nodes event) =
      .resolve who payload binding checks)
    (node : nodeView G event = .resolve who payload binding checks outputEq codeEq)
    (move : Option (CommitRecoveryMove Player L)) :
    moveResponse setup runtime leaks bounds who event move =
      PhaseCount.phaseOpeningPolicy runtime leaks bounds who event payload binding
        (fun _ view => PMF.pure (effectiveOpening setup runtime leaks binding checks view
          (OwnAction.disclosure (move.map (·.action))))) := by
  classical
  funext past view
  simp only [moveResponse, node, ↓reduceDIte]

/-- A genuine successful binding uses its actual accepted catalogue handle for
every effective source disclosure choice. Deferred guard rejection is
prevalidated on the actual local store before any opening is emitted. The
physical menu guard is inactive on this same counted first callback. -/
theorem opening_encoders_of_history (horizon : Nat) (scheduler : (app).Scheduler)
    {control : (app).Control}
    (trace : ((counted).protocol (initial setup runtime leaks) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (G).EventId) (payload : L.Ty)
    (binding : FieldRef (G).layout (.binding who payload))
    (checks : List (GuardCheck (G).layout payload))
    (outputEq : (G).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (G).layout) outputEq) ((G).nodes event) =
      .resolve who payload binding checks)
    (node : nodeView G event = .resolve who payload binding checks outputEq codeEq)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? control.execution.application.current.native.config.store =
      some (.success value))
    (values : (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ candidate,
      control.execution.application.current.native.accepted binding.field = some candidate ∧
      candidate.1 = who ∧
      control.execution.application.current.native.candidates.lookup candidate =
        .openable ⟨payload, value⟩ ∧
      ∀ move, moveResponse setup runtime leaks bounds who event move
          (control.execution.recall who) (control.execution.observe app who) =
        PMF.pure (if effectiveOpening setup runtime leaks binding checks
          (control.execution.observe app who) (OwnAction.disclosure (move.map (·.action))) then
          PhaseCount.phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩
            else ⟨none⟩) := by
  classical
  let inputs := setup.initialLaw.map encodeInputs
  have countedTrace : ((counted).protocol
      (inputs.map (PhaseRuntimeState.initial (plan setup))) horizon scheduler).Trace
        (some control) := by
    rw [PMF.map_comp]
    exact trace
  obtain ⟨candidate, accepted, owner, openable, available⟩ :=
    PhaseCount.phaseOpeningResponse_of_history runtime leaks bounds (plan setup) inputs horizon
      scheduler countedTrace who event payload binding checks outputEq codeEq node request unsent
        value stored values
  have localStored : binding.get?
      (control.execution.observe app who).application.1.observation.store =
        some (.success value) := by
    change binding.get? ((G).playerStore who
      control.execution.application.current.native.config.store) = _
    rw [binding.get?_playerStore who _ (by simp only [EventField.VisibleTo]), stored]
  have localAccepted : (control.execution.observe app who).application.1.publicView.accepted
      binding.field = some candidate := accepted
  refine ⟨candidate, accepted, owner, openable, ?_⟩
  intro move
  rw [moveResponse_opening setup runtime leaks bounds who event payload binding checks outputEq
    codeEq node]
  unfold PhaseCount.phaseOpeningPolicy
  simp only [localStored, localAccepted, ite_eq_left available, PMF.pure_map]

/-- If the actual binding is failed, every encoded source disclosure is silence.
This is only the physical encoder law; it does not identify the exited owner's
literal source action history. -/
theorem failed_opening_encoder (execution : (app).Execution)
    (who : Player) (event : (G).EventId) (payload : L.Ty)
    (binding : FieldRef (G).layout (.binding who payload))
    (checks : List (GuardCheck (G).layout payload))
    (outputEq : (G).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (G).layout) outputEq) ((G).nodes event) =
      .resolve who payload binding checks)
    (node : nodeView G event = .resolve who payload binding checks outputEq codeEq)
    (stored : binding.get? execution.application.current.native.config.store = some .failure)
    (move : Option (CommitRecoveryMove Player L)) :
    moveResponse setup runtime leaks bounds who event move (execution.recall who)
      (execution.observe app who) = PMF.pure ⟨none⟩ := by
  have localStored : binding.get? (execution.observe app who).application.1.observation.store =
      some .failure := by
    change binding.get? ((G).playerStore who
      execution.application.current.native.config.store) = _
    rw [binding.get?_playerStore who _ (by simp only [EventField.VisibleTo]), stored]
  rw [moveResponse_opening setup runtime leaks bounds who event payload binding checks outputEq
    codeEq node]
  simp only [PhaseCount.phaseOpeningPolicy, localStored]

/-- A guard-rejected requested opening emits no packet, even if the stored
binding is successful. Its private payload is therefore never exposed by
this encoder to pending traffic or a raw foreign player. -/
theorem rejected_opening_encoder (execution : (app).Execution)
    (who : Player) (event : (G).EventId) (payload : L.Ty)
    (binding : FieldRef (G).layout (.binding who payload))
    (checks : List (GuardCheck (G).layout payload))
    (outputEq : (G).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (G).layout) outputEq) ((G).nodes event) =
      .resolve who payload binding checks)
    (node : nodeView G event = .resolve who payload binding checks outputEq codeEq)
    (move : Option (CommitRecoveryMove Player L))
    (rejected : EventCode.resolveOutput? binding checks
      (OwnAction.disclosure (move.map (·.action)))
      execution.application.current.native.config.store = some .failure) :
    moveResponse setup runtime leaks bounds who event move (execution.recall who)
      (execution.observe app who) = PMF.pure ⟨none⟩ := by
  have suppressed : effectiveOpening setup runtime leaks binding checks (execution.observe app who)
      (OwnAction.disclosure (move.map (·.action))) = false := by
    rw [effectiveOpening_read, rejected]
  rw [moveResponse_opening setup runtime leaks bounds who event payload binding checks outputEq
    codeEq node]
  unfold PhaseCount.phaseOpeningPolicy
  split
  · dsimp only
    split
    · simp only [suppressed, PMF.pure_map]
      rfl
    · rfl
  · rfl

/-- Every supported first successful opening realizes the actual arbitrary
source effective-disclosure marginal through the same accepted physical handle.
The prior, source profile and all earlier attempts are unchanged. -/
theorem supported_first_opening_law (horizon : Nat) (scheduler : (app).Scheduler)
    (source : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat)
    (history : ((PhaseCount.rawMenu runtime leaks bounds).protocol
      (initial setup runtime leaks) horizon scheduler).History)
    (supported : history ∈ (((PhaseCount.rawMenu runtime leaks bounds).information
      (initial setup runtime leaks) horizon scheduler).runBehavioral
        (compileProfile setup runtime leaks bounds horizon scheduler source) fuel).support)
    (control : (app).Control) (atState : history.state = some control)
    (who : Player) (event : (G).EventId) (payload : L.Ty)
    (binding : FieldRef (G).layout (.binding who payload))
    (checks : List (GuardCheck (G).layout payload))
    (outputEq : (G).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (G).layout) outputEq) ((G).nodes event) =
      .resolve who payload binding checks)
    (node : nodeView G event = .resolve who payload binding checks outputEq codeEq)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks who
      ⟨control.execution.application.attempt, event⟩ (control.execution.recall who))
    (value : L.Val payload)
    (stored : binding.get? control.execution.application.current.native.config.store =
      some (.success value))
    (values : (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ candidate,
      control.execution.application.current.native.accepted binding.field = some candidate ∧
      candidate.1 = who ∧
      control.execution.application.current.native.candidates.lookup candidate =
        .openable ⟨payload, value⟩ ∧
      ∃ (current : CommitRecoveryState setup.program)
        (sourceTrace : setup.commitRecoveryProtocol.Trace (some current)),
        current.excluded = control.execution.application.current.excluded ∧
        ProtocolState.actor setup.program current.point = some who ∧
        policy setup runtime leaks bounds who (source who) (control.execution.recall who)
            (control.execution.observe app who) =
          ((source who (setup.commitRecoveryModel.infoOf who sourceTrace)).map
            (fun choice => effectiveOpening setup runtime leaks binding checks
              (control.execution.observe app who)
              (OwnAction.disclosure (choice.val.map (·.action))))).map
              (fun disclose => if disclose then
                PhaseCount.phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩
                  else ⟨none⟩) := by
  obtain ⟨countedTrace⟩ := supported_counted_trace setup runtime leaks bounds horizon scheduler
    source fuel history supported control atState
  have unsent := supported_first_unsent setup runtime leaks bounds horizon scheduler source fuel
    history supported control atState who ⟨control.execution.application.attempt, event⟩ first
  obtain ⟨candidate, accepted, owner, openable, encoded⟩ := opening_encoders_of_history setup
    runtime leaks bounds horizon scheduler countedTrace who event payload binding checks outputEq
      codeEq node request unsent value stored values
  have directTrace := (counted).toRawTrace _ horizon scheduler countedTrace
  obtain ⟨current, sourceTrace, exclusions, actor, law⟩ := policy_first_of_history setup runtime
    leaks bounds horizon scheduler directTrace who (source who) event request first
  refine ⟨candidate, accepted, owner, openable, current, sourceTrace, exclusions, actor, ?_⟩
  rw [law, PMF.map_comp, ← PMF.bind_pure_comp]
  apply congrArg (fun continuation =>
    (source who (setup.commitRecoveryModel.infoOf who sourceTrace)).bind continuation)
  funext choice
  exact encoded choice.val

/-- At a genuine first request with a failed stored binding, even an arbitrary
source disclosure law produces physical silence. This does not equate the
owner's two literal source intentions. -/
theorem policy_failed_opening_of_history (horizon : Nat) (scheduler : (app).Scheduler)
    {control : (app).Control}
    (trace : ((app).protocol (initial setup runtime leaks) horizon scheduler).Trace (some control))
    (who : Player) (source : setup.commitRecoveryModel.BehavioralPolicy who)
    (event : (G).EventId) (payload : L.Ty)
    (binding : FieldRef (G).layout (.binding who payload))
    (checks : List (GuardCheck (G).layout payload))
    (outputEq : (G).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (G).layout) outputEq) ((G).nodes event) =
      .resolve who payload binding checks)
    (node : nodeView G event = .resolve who payload binding checks outputEq codeEq)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks who
      ⟨control.execution.application.attempt, event⟩ (control.execution.recall who))
    (stored : binding.get? control.execution.application.current.native.config.store =
      some .failure) :
    policy setup runtime leaks bounds who source (control.execution.recall who)
      (control.execution.observe app who) = PMF.pure ⟨none⟩ := by
  obtain ⟨current, sourceTrace, _exclusions, _actor, law⟩ := policy_first_of_history setup runtime
    leaks bounds horizon scheduler trace who source event request first
  rw [law]
  calc
    _ = (source (setup.commitRecoveryModel.infoOf who sourceTrace)).bind
        (fun _ => PMF.pure (⟨none⟩ : (app).Action)) := by
      apply congrArg (fun continuation =>
        (source (setup.commitRecoveryModel.infoOf who sourceTrace)).bind continuation)
      funext choice
      exact failed_opening_encoder setup runtime leaks bounds control.execution who event payload
        binding checks outputEq codeEq node stored choice.val
    _ = _ := PMF.bind_const ..

end Vegas.SourcePhaseClient
