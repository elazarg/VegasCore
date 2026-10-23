/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalStoppedSample
import GameTheory.Math.Probability.Conditioning

/-! # Full source histories at actual singleton Nature stops -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual stopped native history and the full ordinary enriched source
history retain the SAME original sample value, for every reserved tape. -/
theorem phaseProposal_ordinary_sample_stopped_coupling
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs)
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (frontier : anchor.execution.application.Frontier)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : anchor.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .sample)
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (suffix : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (lift : ProtocolState (.sample name fresh law suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.sample name fresh law suffix) lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift (.inl source))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (agrees : refs.Agrees source.state anchor.execution.application.current.native.config.store)
    (event : (serviceGraph setup mode).EventId) (rank : event.val = phase.low)
    (ready : anchor.execution.application.current.native.config.cut.Ready event)
    (output : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode (graphLayout setup.program)) output)
      ((serviceGraph setup mode).nodes event) = .sample payload (compilePublicDist refs law))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (profile : ∀ who, ((PhaseCount.onePacketMenu runtime leaks bounds).information
      (inputs.map (PhaseRuntimeState.initial plan)) (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks
        (ReservedEpoch.packetCapacity runtime) tape)).BehavioralPolicy who) :
    let initial := inputs.map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let menu := PhaseCount.onePacketMenu runtime leaks bounds
    let model := menu.information initial horizon scheduler
    let certificate := (menu.bounded initial horizon scheduler).wellFoundedHistories
    let stopped := fun history : (menu.protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ anchor.execution.application.attempt
    let field : FieldRef (graphLayout setup.program) (.publicData payload) := ⟨.inr event, output⟩
    ∃ joint : PMF ((menu.protocol initial horizon scheduler).History ×
        setup.proposalRecoveryProtocol.History),
      joint.map Prod.fst =
        model.runBehavioralUntil certificate profile stopped ⟨some anchor, anchorTrace⟩ ∧
      joint.map Prod.snd = setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        1 ⟨some current, trace⟩ ∧
      ∀ pair ∈ joint.support,
        ∃ value ∈ (L.evalDist law (sourcePublicEnv source.state)).support,
          pair.2.state = some (CommitRecoveryState.atPoint
            (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
            current.excluded current.generation) ∧
          TracePrefix trace pair.2.trace ∧
          pair.1.state.bind (fun control =>
            field.get? control.execution.application.current.native.config.store) = some value := by
  classical
  intro initial horizon scheduler menu model certificate stopped field
  let draw := L.evalDist law (sourcePublicEnv source.state)
  have evaluates : (compilePublicDist refs law).eval?
      anchor.execution.application.current.native.config.store = some draw := by
    rw [PublicDist.eval?, compilePublicDist_evalLaw? refs source.state _ agrees law]
    rfl
  have inside : event ∈ phase.events := (phase.mem_events event).mpr
    ⟨rank.ge, by have positive := phase.nonempty; omega⟩
  have head : anchor.execution.application.phases.head? = some phase := by
    simp only [installed, List.head?_cons]
  have allowed : anchor.execution.application.commandAllowed (.executeSample event) = true := by
    simp only [PhaseRuntimeState.commandAllowed, head, Option.any_some, inside, decide_true]
  obtain ⟨commandJoint, sourceLaw, nativeLaw, supported⟩ :=
    phaseProposal_ordinary_sample_application_coupling setup mode runtime leaks fresh law suffix
      lift origin source current trace point refs anchor.execution agrees event ready output code
        allowed values
  let observe := fun pair : setup.proposalRecoveryProtocol.History ×
      (phaseApplication runtime leaks).Execution =>
    field.get? pair.2.application.current.native.config.store
  let read := fun history : (menu.protocol initial horizon scheduler).History =>
    history.state.bind fun control =>
      field.get? control.execution.application.current.native.config.store
  let native := model.runBehavioralUntil certificate profile stopped ⟨some anchor, anchorTrace⟩
  have observedCommand : commandJoint.map observe = draw.map some := by
    have actual := (phaseProposal_sample_application_laws runtime leaks anchor.execution frontier
      phase remaining installed kind event rank ready payload (compilePublicDist refs law) output
        code draw evaluates).1
    have mapped := congrArg (PMF.map (fun next : (phaseApplication runtime leaks).Execution =>
      field.get? next.application.current.native.config.store)) nativeLaw
    simpa only [PMF.map_comp, Function.comp_def, observe] using mapped.trans actual
  have observedStopped : native.map read = draw.map some := by
    convert phaseProposal_sample_stopped_draw_law runtime leaks bounds plan inputs ordered maximal
      tape anchor anchorTrace phase remaining installed kind event rank ready payload
        (compilePublicDist refs law) output code draw evaluates profile using 1
    congr 2
    dsimp only [native, stopped]
    congr 1
    funext history
    cases history.state <;> rfl
  let joint := native.bind fun history =>
    (fiberPosterior commandJoint observe (read history)).map fun pair => (history, pair.1)
  refine ⟨joint, ?_, ?_, ?_⟩
  · change (native.bind _).map Prod.fst = native
    rw [PMF.map_bind]
    calc
      _ = native.bind (fun history => PMF.pure history) := by
        apply bind_congr_on_support
        intro history _supported
        rw [PMF.map_comp]
        exact PMF.map_const _ _
      _ = native := PMF.bind_pure native
  · change (native.bind _).map Prod.snd = _
    calc
      _ = (native.bind fun history =>
          fiberPosterior commandJoint observe (read history)).map Prod.fst := by
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      _ = ((native.map read).bind (fiberPosterior commandJoint observe)).map Prod.fst := by
        rw [PMF.bind_map]
        rfl
      _ = ((commandJoint.map observe).bind
          (fiberPosterior commandJoint observe)).map Prod.fst := by
        rw [observedStopped, observedCommand]
      _ = _ := by rw [fiberPosterior_reconstruct, sourceLaw]
  · intro pair member
    obtain ⟨history, nativeSupport, conditionalSupport⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp member
    obtain ⟨sampled, sampledSupport, equal⟩ :=
      (PMF.mem_support_map_iff _ _ _).mp conditionalSupport
    subst pair
    have signal : read history ∈ (commandJoint.map observe).support := by
      rw [observedCommand, ← observedStopped]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨history, nativeSupport, rfl⟩
    obtain ⟨same, actualSupport⟩ := mem_support_fiberPosterior signal sampledSupport
    obtain ⟨value, valueSupport, sourceState, kept, actual⟩ := supported sampled actualSupport
    refine ⟨value, valueSupport, sourceState, kept, ?_⟩
    change read history = some value
    rw [← same]
    change field.get? sampled.2.application.current.native.config.store = some value
    rw [actual]
    exact (phaseProposal_sample_application_laws runtime leaks anchor.execution frontier phase
      remaining installed kind event rank ready payload (compilePublicDist refs law) output code
        draw evaluates).2.2 value valueSupport

end Vegas
