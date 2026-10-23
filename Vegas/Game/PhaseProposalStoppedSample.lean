/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalFreshTerminal
import Interaction.ReactiveLocalContinuation

/-! # Original source draws through actual physical sample normalization -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
theorem EventGraphRuntime.RuntimePhase.sample_drain_eq {graph : Vegas.EventGraph Player L}
    (phase : RuntimePhase graph) (kind : phase.kind = .sample)
    (event : graph.EventId) (rank : event.val = phase.low)
    (actorless : graph.actor? event = none) (state : RecoveryState graph) :
    phase.drain state = state := by
  apply phase.drain_eq_of_clear state
  intro other eligible
  have bounds := (phase.mem_events other).mp eligible.1
  have singleton := phase.sample_singleton kind
  have same : other = event := Fin.ext (by omega)
  subst other
  obtain ⟨owner, acting, _excluded⟩ := eligible.2.owned
  rw [actorless] at acting
  cases acting

omit [Fintype Player] in
theorem EventGraphRuntime.PhaseRuntimeState.normalize_pending_sample
    {graph : Vegas.EventGraph Player L} (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .sample)
    (event : graph.EventId) (rank : event.val = phase.low)
    (actorless : graph.actor? event = none) (pending : ¬ phase.Finished state.current) :
    state.normalize = state := by
  have drain := phase.sample_drain_eq kind event rank actorless state.current
  cases state with
  | mk phases generation entry current retired =>
      change phases = phase :: remaining at installed
      subst phases
      simp only [PhaseRuntimeState.normalize, PhaseRuntimeState.settle, drain, pending,
        ↓reduceIte]

omit [Fintype Player] in
theorem EventGraphRuntime.PhaseRuntimeState.sample_normalization_keepsStore
    {graph : Vegas.EventGraph Player L} (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .sample)
    (event : graph.EventId) (rank : event.val = phase.low)
    (actorless : graph.actor? event = none) (raw : RecoveryState graph)
    (completed : event ∈ raw.native.config.cut.completed) :
    KeepsStore raw.native
      ({ state with current := raw } : PhaseRuntimeState graph).normalize.current.native := by
  have drain := phase.sample_drain_eq kind event rank actorless raw
  have finished : phase.Finished (phase.drain raw) := by
    rw [drain]
    intro other member
    have bounds := (phase.mem_events other).mp member
    have singleton := phase.sample_singleton kind
    have same : other = event := Fin.ext (by omega)
    subst other
    exact completed
  have noRetry : ¬ (phase.kind = .commitment ∧
      (((phase.drain raw).excluded \ state.entry.excluded) ∩ phase.owners).Nonempty) := by
    rintro ⟨impossible, _⟩
    cases kind.symm.trans impossible
  change KeepsStore raw.native (PhaseRuntimeState.settle state.phases state.generation
    state.entry raw state.retired).current.native
  rw [installed, PhaseRuntimeState.settle_clean phase remaining state.generation state.entry raw
    state.retired finished noRetry, drain]
  exact (phaseProposal_fresh_settle_completion_origin remaining state.generation raw
    state.retired).2.2.2.1

/-- The complete physical sample command and full enriched source instruction
share one original draw, with the actual normalization and scheduler recall. -/
theorem phaseProposal_ordinary_sample_application_coupling
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
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
    (physical : (phaseApplication runtime leaks).Execution)
    (agrees : refs.Agrees source.state physical.application.current.native.config.store)
    (event : (serviceGraph setup mode).EventId)
    (ready : physical.application.current.native.config.cut.Ready event)
    (output : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode (graphLayout setup.program)) output)
      ((serviceGraph setup mode).nodes event) = .sample payload (compilePublicDist refs law))
    (allowed : physical.application.commandAllowed (.executeSample event) = true)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1)) :
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History ×
        (phaseApplication runtime leaks).Execution),
      joint.map Prod.fst = setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        1 ⟨some current, trace⟩ ∧
      joint.map Prod.snd = physical.environmentStep (phaseApplication runtime leaks)
        (.application (.executeSample event)) ∧
      ∀ pair ∈ joint.support, ∃ value ∈ (L.evalDist law (sourcePublicEnv source.state)).support,
        pair.1.state = some (CommitRecoveryState.atPoint
          (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
          current.excluded current.generation) ∧
        TracePrefix trace pair.1.trace ∧
        pair.2 = PhaseRuntimeState.normalizeExecution runtime leaks
          (PhaseBindingRepair.rawSample runtime leaks physical event payload output ready
            value) := by
  obtain ⟨localJoint, sourceLaw, nativeLaw, supported⟩ :=
    phaseProposal_ordinary_sample_coupling setup mode runtime fresh law suffix lift origin source
      current trace point refs physical.application.current.native agrees event ready output code
        values
  let install := fun native : EventGraphRuntime.State (serviceGraph setup mode) =>
    PhaseRuntimeState.normalizeExecution runtime leaks {
      physical with
      application := { physical.application with
        current := physical.application.current.environmentResult (.executeSample event) native }
      environmentRecall := physical.environmentRecall ++
        [⟨physical.observeEnvironment (phaseApplication runtime leaks),
          .application (.executeSample event)⟩] }
  have actual : (environmentStep runtime physical.application.current.native
      (.executeSample event)).map install =
        physical.environmentStep (phaseApplication runtime leaks)
        (.application (.executeSample event)) := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change _ = (physical.application.environment runtime (.executeSample event)).map _
    rw [PhaseRuntimeState.environment, ite_eq_left allowed, PMF.map_comp]
    rfl
  let joint := localJoint.map fun pair => (pair.1, install pair.2)
  refine ⟨joint, ?_, ?_, ?_⟩
  · simpa only [joint, PMF.map_comp, Function.comp_def] using sourceLaw
  · simpa only [joint, PMF.map_comp, Function.comp_def] using
      (congrArg (PMF.map install) nativeLaw).trans actual
  · intro pair member
    obtain ⟨original, originalSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    subst pair
    obtain ⟨value, valueSupport, state, kept, native⟩ := supported original originalSupport
    refine ⟨value, valueSupport, state, kept, ?_⟩
    rw [native]
    rfl

omit [Fintype Player] in
/-- Before the actual singleton Nature operation every other physical command
stutters on the semantic configuration, despite arbitrary network traffic. -/
theorem phaseProposal_sample_environment_configuration
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (physical : (phaseApplication runtime leaks).Execution)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : physical.application.phases = phase :: remaining)
    (kind : phase.kind = .sample) (event : graph.EventId) (rank : event.val = phase.low)
    (ready : physical.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (output : graph.outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode graph.layout) output) (graph.nodes event) =
      .sample payload law)
    (command : (phaseApplication runtime leaks).Command) :
    command = .application (.executeSample event) ∨
      (physical.environmentStep (phaseApplication runtime leaks) command).map
        (fun next => (next.application.current.native.config, next.application.attempt)) =
          PMF.pure (physical.application.current.native.config, physical.application.attempt) := by
  classical
  let app := phaseApplication runtime leaks
  have actorless : graph.actor? event = none :=
    (EventCode.actor_cast output (graph.nodes event)).symm.trans (congrArg EventCode.actor code)
  have node := nodeView_eq_sample output code
  have inside : event ∈ phase.events := (phase.mem_events event).mpr
    ⟨rank.ge, by have positive := phase.nonempty; omega⟩
  have only (other : graph.EventId) (member : other ∈ phase.events) : other = event := by
    have bounds := (phase.mem_events other).mp member
    have singleton := phase.sample_singleton kind
    exact Fin.ext (by omega)
  have noHandle : ∀ message : Message Player (CommitAttemptPacket graph),
      physical.application.handle runtime message = none := by
    intro message
    unfold PhaseRuntimeState.handle
    split
    · rename_i permitted
      have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp permitted).1).2
      obtain ⟨selectedPhase, member, selected, named, selectedInside⟩ :=
        physical.application.allows_event message.payload.packet.call allowed
      have phaseEq : selectedPhase = phase := by
        have reverse : phase = selectedPhase := by
          simpa only [installed, List.head?_cons, Option.mem_some_iff] using member
        exact reverse.symm
      subst selectedPhase
      have eventEq := only selected selectedInside
      subst selected
      have nativeNone : EventGraphRuntime.handle runtime physical.application.current.native
          ⟨message.id, message.payload.packet.call⟩ = none := by
        cases call : message.payload.packet.call with
        | malformed raw =>
            have impossible : (none : Option graph.EventId) = some event := by
              simpa only [call, Payload.event?] using named
            cases impossible
        | commitment actual candidate =>
            have actualEq : actual = event := Option.some.inj (by
              simpa only [call, Payload.event?] using named)
            subst actual
            simp only [EventGraphRuntime.handle, dite_eq_left ready, node]
            split <;> rfl
        | opening actual candidate raw =>
            have actualEq : actual = event := Option.some.inj (by
              simpa only [call, Payload.event?] using named)
            subst actual
            simp only [EventGraphRuntime.handle, dite_eq_left ready, node]
            split <;> rfl
      rw [nativeNone]
      rfl
    · rfl
  have stays (all : ∀ next ∈ (physical.environmentStep app command).support,
      (next.application.current.native.config, next.application.attempt) =
        (physical.application.current.native.config, physical.application.attempt)) :
      (physical.environmentStep app command).map
        (fun next => (next.application.current.native.config, next.application.attempt)) =
          PMF.pure (physical.application.current.native.config, physical.application.attempt) := by
    rw [map_congr_on_support _ (g := fun _ =>
          (physical.application.current.native.config, physical.application.attempt)) all]
    exact PMF.map_const _ _
  have applicationStays (chosen : EnvironmentCommand graph)
      (nativeStays : ∀ native ∈
        (environmentStep runtime physical.application.current.native chosen).support,
          native.config = physical.application.current.native.config) :
      (physical.environmentStep app (.application chosen)).map
        (fun next => (next.application.current.native.config, next.application.attempt)) =
          PMF.pure (physical.application.current.native.config, physical.application.attempt) := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change (physical.application.environment runtime chosen).map
      (fun state => (state.current.native.config, state.attempt)) = _
    unfold PhaseRuntimeState.environment
    split
    · rename_i allowed
      rw [PMF.map_comp]
      rw [map_congr_on_support _
        (g := fun _ =>
          (physical.application.current.native.config, physical.application.attempt))
        (fun native supported => by
          have same := nativeStays native supported
          let raw : PhaseRuntimeState graph := { physical.application with
            current := physical.application.current.environmentResult chosen native }
          have rawPending : ¬ phase.Finished raw.current := by
            intro finished
            apply ready.1
            have completed := finished inside
            change event ∈ native.config.cut.completed at completed
            rwa [same] at completed
          have normalized := raw.normalize_pending_sample phase remaining installed kind event
            rank actorless rawPending
          change (raw.normalize.current.native.config, raw.normalize.attempt) = _
          rw [normalized]
          exact Prod.ext same rfl)]
      exact PMF.map_const _ _
    · exact PMF.pure_map _ _
  cases command with
  | activate owner =>
      right
      apply stays
      intro next supported
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp,
        PMF.mem_support_map_iff] at supported
      obtain ⟨observed, _member, rfl⟩ := supported
      rfl
  | wait =>
      right
      apply stays
      intro next supported
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at supported
      cases supported
      rfl
  | «include» id =>
      right
      apply stays
      intro next supported
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at supported
      cases supported
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : physical.network.lookup id with
      | none => rfl
      | some message =>
          change (((physical.application.handle runtime message).getD
            physical.application).current.native.config,
              ((physical.application.handle runtime message).getD physical.application).attempt) = _
          rw [noHandle]
          rfl
  | application chosen =>
      cases chosen with
      | advanceClock =>
          right
          apply applicationStays
          intro native supported
          simp only [environmentStep, PMF.mem_support_pure_iff] at supported
          cases supported
          rfl
      | executeSample other =>
          by_cases equal : other = event
          · subst other
            exact Or.inl rfl
          · right
            by_cases allowed : physical.application.commandAllowed (.executeSample other) = true
            · have member : other ∈ phase.events := by
                simpa only [PhaseRuntimeState.commandAllowed, installed, List.head?_cons,
                  Option.any_some, decide_eq_true_eq] using allowed
              exact (equal (only other member)).elim
            · simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
              change (physical.application.environment runtime (.executeSample other)).map _ = _
              rw [PhaseRuntimeState.environment, ite_eq_right allowed, PMF.pure_map]
              rfl
      | expire other =>
          right
          by_cases allowed : physical.application.commandAllowed (.expire other) = true
          · have member : other ∈ phase.events := by
              simpa only [PhaseRuntimeState.commandAllowed, installed, List.head?_cons,
                Option.any_some, decide_eq_true_eq] using allowed
            have equal := only other member
            subst other
            apply applicationStays
            have inert : environmentStep runtime physical.application.current.native
                (.expire event) = PMF.pure physical.application.current.native := by
              cases activated : physical.application.current.native.activatedAt event with
              | none =>
                  exact environmentStep_expire_of_not_activated runtime _ event ready activated
              | some entered =>
                  by_cases due : runtime.deadline event ≤
                      physical.application.current.native.clock - entered
                  · exact environmentStep_expire_sample_eq runtime _ event ready entered activated
                      due payload law output code node
                  · exact environmentStep_expire_of_not_due runtime _ event ready entered activated
                      due
            intro native supported
            rw [inert, PMF.mem_support_pure_iff] at supported
            cases supported
            rfl
          · simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
            change (physical.application.environment runtime (.expire other)).map _ = _
            rw [PhaseRuntimeState.environment, ite_eq_right allowed, PMF.pure_map]
            rfl

omit [Fintype Player] in
/-- The actual Nature command is harmonic for its original value law before
completion and the literal immutable sample read after phase advancement. -/
theorem phaseProposal_sample_application_laws
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (physical : (phaseApplication runtime leaks).Execution)
    (frontier : physical.application.Frontier)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : physical.application.phases = phase :: remaining)
    (kind : phase.kind = .sample) (event : graph.EventId) (rank : event.val = phase.low)
    (ready : physical.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (output : graph.outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode graph.layout) output) (graph.nodes event) =
      .sample payload law)
    (draw : PMF (L.Val payload))
    (evaluates : law.eval? physical.application.current.native.config.store = some draw) :
    let field : FieldRef graph.layout (.publicData payload) := ⟨.inr event, output⟩
    (physical.environmentStep (phaseApplication runtime leaks)
      (.application (.executeSample event))).map (fun after =>
        field.get? after.application.current.native.config.store) = draw.map some ∧
    (physical.environmentStep (phaseApplication runtime leaks)
      (.application (.executeSample event))).bind (fun after =>
        if after.application.attempt = physical.application.attempt then draw.map some
        else PMF.pure (field.get? after.application.current.native.config.store)) =
      draw.map some ∧
    ∀ value ∈ draw.support,
      let after := PhaseRuntimeState.normalizeExecution runtime leaks
        (PhaseBindingRepair.rawSample runtime leaks physical event payload output ready value)
      field.get? after.application.current.native.config.store = some value := by
  classical
  intro field
  have inside : event ∈ phase.events := (phase.mem_events event).mpr
    ⟨rank.ge, by have positive := phase.nonempty; omega⟩
  have head : physical.application.phases.head? = some phase := by
    simp only [installed, List.head?_cons]
  have allowed : physical.application.commandAllowed (.executeSample event) = true := by
    simp only [PhaseRuntimeState.commandAllowed, head, Option.any_some, inside, decide_true]
  have actorless : graph.actor? event = none :=
    (EventCode.actor_cast output (graph.nodes event)).symm.trans (congrArg EventCode.actor code)
  have nativeLaw : environmentStep runtime physical.application.current.native
      (.executeSample event) = draw.map (fun value =>
        physical.application.current.native.complete event ready
          (cast (congrArg EventField.Action output.symm) PUnit.unit)
          (cast (congrArg EventField.Value output.symm) value)) := by
    rw [environmentStep_executeSample_eq runtime _ event ready payload law output code
      (nodeView_eq_sample output code),
      physical.application.current.native.config.step_eq_map_of_code event ready output
        (.sample payload law) code PUnit.unit draw evaluates, PMF.map_comp]
    rfl
  have pointwise (value : L.Val payload) (supported : value ∈ draw.support) :
      let after := PhaseRuntimeState.normalizeExecution runtime leaks
        (PhaseBindingRepair.rawSample runtime leaks physical event payload output ready value)
      after.application.attempt ≠ physical.application.attempt ∧
        field.get? after.application.current.native.config.store = some value := by
    let native := physical.application.current.native.complete event ready
      (cast (congrArg EventField.Action output.symm) PUnit.unit)
      (cast (congrArg EventField.Value output.symm) value)
    let raw : RecoveryState graph := { physical.application.current with native := native }
    let after := PhaseRuntimeState.normalizeExecution runtime leaks
      (PhaseBindingRepair.rawSample runtime leaks physical event payload output ready value)
    have moved : native ∈ (environmentStep runtime physical.application.current.native
        (.executeSample event)).support := by
      rw [nativeLaw]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, supported, rfl⟩
    have applicationMoved : after.application ∈
        (physical.application.environment runtime (.executeSample event)).support := by
      rw [PhaseRuntimeState.environment, ite_eq_left allowed, PMF.mem_support_map_iff]
      exact ⟨native, moved, rfl⟩
    have advanced := physical.application.sample_advances_phase runtime after.application
      frontier phase head kind event rank ready actorless applicationMoved
    have different : after.application.attempt ≠ physical.application.attempt := by
      intro equal
      have equalPhase := congrArg CommitAttemptId.phase equal
      omega
    have completed : event ∈ raw.native.config.cut.completed := by
      change event ∈
        (physical.application.current.native.config.complete event ready _ _).cut.completed
      simp only [Config.complete_cut, EventOrder.Cut.mem_complete, true_or]
    have retained := physical.application.sample_normalization_keepsStore phase remaining
      installed kind event rank actorless raw completed
    have stored : field.get? raw.native.config.store = some value := by
      change cast (congrArg (fun kind => Option kind.Value) output)
        ((physical.application.current.native.config.complete event ready _
          (cast (congrArg EventField.Value output.symm) value)).outputs event) = some value
      rw [Config.complete_output_same]
      have inverse {A B : Type} (equal : A = B) (item : B) :
          cast (congrArg Option equal) (some (cast equal.symm item)) = some item := by
        cases equal
        rfl
      exact inverse (congrArg EventField.Value output) value
    have read : field.get? after.application.current.native.config.store = some value :=
      field.get?_preserved raw.native.config.store _ retained value stored
    exact ⟨different, read⟩
  have actual := PhaseBindingRepair.sample_environment_law runtime leaks physical event ready
    payload law output code (nodeView_eq_sample output code) allowed draw evaluates
  refine ⟨?_, ?_, fun value member => (pointwise value member).2⟩
  · rw [actual, PMF.map_comp]
    apply map_congr_on_support
    intro value supported
    exact (pointwise value supported).2
  · rw [actual, PMF.bind_map]
    calc
      _ = draw.bind (fun value => PMF.pure (some value)) := by
        apply bind_congr_on_support
        intro value supported
        obtain ⟨different, read⟩ := pointwise value supported
        simp only [Function.comp_apply]
        rw [ite_eq_right different, read]
      _ = _ := PMF.bind_pure_comp _ _

/-- Every actual protocol row before its singleton Nature phase closes is
harmonic for the fixed original draw and the eventual typed sample read. -/
theorem phaseProposal_sample_control_harmonic
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (profile : ∀ who, ((PhaseCount.onePacketMenu runtime leaks bounds).information initial
      horizon scheduler).BehavioralPolicy who)
    (history : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
      scheduler).History)
    (current : (phaseApplication runtime leaks).Control) (state : history.state = some current)
    (frontier : current.execution.application.Frontier)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : current.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .sample) (event : graph.EventId) (rank : event.val = phase.low)
    (ready : current.execution.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (output : graph.outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode graph.layout) output) (graph.nodes event) =
      .sample payload law)
    (draw : PMF (L.Val payload))
    (evaluates : law.eval? current.execution.application.current.native.config.store = some draw) :
    let field : FieldRef graph.layout (.publicData payload) := ⟨.inr event, output⟩
    let potential : (phaseApplication runtime leaks).ProtocolState → PMF (Option (L.Val payload)) :=
      fun state => match state with
      | none => PMF.pure none
      | some control =>
          if control.execution.application.attempt = current.execution.application.attempt then
            draw.map some
          else PMF.pure (field.get? control.execution.application.current.native.config.store)
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      initial horizon scheduler).runBehavioralFrom profile 1 history).bind
        (fun after => potential after.state) =
        draw.map some := by
  classical
  intro field potential
  let app := phaseApplication runtime leaks
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let model := menu.information initial horizon scheduler
  let policies := menu.decodeProfile initial horizon scheduler profile
  have environment (count : Nat) (command : app.Command) :
      (current.execution.environmentStep app command).bind (fun next =>
        potential (some ⟨count, command.actor? app, next⟩)) = draw.map some := by
    rcases phaseProposal_sample_environment_configuration runtime leaks current.execution phase
      remaining installed kind event rank ready payload law output code command with sample | stays
    · subst command
      exact (phaseProposal_sample_application_laws runtime leaks current.execution frontier
        phase remaining installed kind event rank ready payload law output code draw evaluates).2.1
    · calc
        _ = (current.execution.environmentStep app command).bind
            (fun _ => draw.map some) := by
          apply bind_congr_on_support
          intro next supported
          have observed : (next.application.current.native.config, next.application.attempt) ∈
              ((current.execution.environmentStep app command).map (fun after =>
                (after.application.current.native.config, after.application.attempt))).support :=
            (PMF.mem_support_map_iff _ _ _).mpr ⟨next, supported, rfl⟩
          rw [stays, PMF.mem_support_pure_iff] at observed
          have sameAttempt : next.application.attempt =
              current.execution.application.attempt := congrArg Prod.snd observed
          simp only [potential, sameAttempt, ite_true]
        _ = _ := PMF.bind_const _ _
  have response (count : Nat) (owner : Player) (action : app.Action) :
      potential (some ⟨count, none, current.execution.respond app owner action⟩) =
        draw.map some := by
    have sameAttempt : (current.execution.respond app owner action).application.attempt =
        current.execution.application.attempt := by
      rcases action with ⟨transmission⟩
      cases transmission <;> rfl
    simp only [potential, sameAttempt, ite_true]
  have evaluated := congrArg (fun distribution : PMF app.ProtocolState =>
      distribution.bind potential)
    (menu.run_map_controlSteps initial horizon scheduler profile 1 history)
  simp only [Function.iterate_one, PMF.pure_bind, PMF.bind_map] at evaluated
  change (model.runBehavioralFrom profile 1 history).bind (fun after => potential after.state) = _
  refine evaluated.trans ?_
  rw [state]
  rcases current with ⟨count, actor, execution⟩
  cases actor with
  | none =>
      cases count with
      | zero =>
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
            Option.bind_some, ReactiveApplication.transition, PMF.pure_bind, potential, ite_true]
      | succ count =>
          simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
            Option.bind_some, ReactiveApplication.transition, PMF.bind_bind, PMF.bind_map]
          exact (bind_congr_on_support _ (fun command _ => environment count command)).trans
            (PMF.bind_const _ _)
  | some owner =>
      simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
        ReactiveApplication.transition, ↓reduceIte, Option.getD_some, PMF.bind_bind,
        PMF.pure_bind]
      calc
        _ = (policies owner (execution.recall owner) (execution.observe app owner)).bind
          (fun _ => draw.map some) := by
          apply bind_congr_on_support
          intro action _supported
          exact response count owner action
        _ = _ := PMF.bind_const _ _

/-- The existing stopped native evaluator retains the ORIGINAL public sample
law at every supported reserved tape, including full automatic phase closure. -/
theorem phaseProposal_sample_stopped_draw_law
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (anchor : (phaseApplication runtime leaks).Control)
    (anchorTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some anchor))
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : anchor.execution.application.phases = phase :: remaining)
    (kind : phase.kind = .sample) (event : graph.EventId) (rank : event.val = phase.low)
    (ready : anchor.execution.application.current.native.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (output : graph.outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode graph.layout) output) (graph.nodes event) =
      .sample payload law)
    (draw : PMF (L.Val payload))
    (evaluates : law.eval? anchor.execution.application.current.native.config.store = some draw)
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
    let field : FieldRef graph.layout (.publicData payload) := ⟨.inr event, output⟩
    let read : (menu.protocol initial horizon scheduler).History → Option (L.Val payload) :=
      fun history => history.state.bind fun control =>
        field.get? control.execution.application.current.native.config.store
    let stopped := fun history : (menu.protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ anchor.execution.application.attempt
    (model.runBehavioralUntil certificate profile stopped ⟨some anchor, anchorTrace⟩).map read =
      draw.map some := by
  classical
  intro initial horizon scheduler menu model certificate field read stopped
  let app := phaseApplication runtime leaks
  let potential : app.ProtocolState → PMF (Option (L.Val payload)) := fun state =>
    match state with
    | none => PMF.pure none
    | some control =>
        if control.execution.application.attempt = anchor.execution.application.attempt then
          draw.map some
        else PMF.pure (field.get? control.execution.application.current.native.config.store)
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan input
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized (menu.toRawTrace initial horizon scheduler anchorTrace)
  have stoppedLaw : ∀ history : (menu.protocol initial horizon scheduler).History,
      TracePrefix anchorTrace history.trace →
      (∃ current : app.Control, history.state = some current ∧
        (current.execution.application.attempt = anchor.execution.application.attempt →
          current.execution.application.phases = anchor.execution.application.phases)) →
      (model.runBehavioralUntil certificate profile stopped history).map read =
        potential history.state := by
    intro history
    induction history using certificate.induction with
    | _ history ih =>
      rintro kept ⟨current, state, phasesKept⟩
      by_cases halt : stopped history
      · rw [model.runBehavioralUntil_of_stopped certificate profile halt, PMF.pure_map]
        have changed : current.execution.application.attempt ≠
            anchor.execution.application.attempt :=
          by simpa only [stopped, state] using halt
        simp only [read, state, Option.bind_some, potential, ite_eq_right changed]
      have same : current.execution.application.attempt = anchor.execution.application.attempt :=
        by simpa only [stopped, state, not_not] using halt
      have phases : current.execution.application.phases = phase :: remaining :=
        (phasesKept same).trans installed
      let raw := menu.toRawTrace initial horizon scheduler (state ▸ history.trace)
      have currentOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
        scheduler initialized raw
      by_cases ended : (menu.protocol initial horizon scheduler).terminal history.state
      · have terminal : app.terminal (some current) := by
          change app.terminal history.state at ended
          rwa [state] at ended
        have complete := ReservedEpoch.terminal_history_complete runtime leaks tape plan ordered
          maximal inputs current raw terminal
        rw [phases] at complete
        cases complete.1
      have geometry := (phaseApplication_quiescent runtime leaks ordered).history initial horizon
        scheduler (fun state supported => by
          obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
          exact phaseApplication_initial_quiescent plan ordered maximal input) raw
      have living := (phaseApplication_live runtime leaks).history initial horizon scheduler
        (fun state supported => by
          obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨PhaseRuntimeState.initial_frontier plan input,
            PhaseRuntimeState.initial_live plan input⟩) raw
      have head : current.execution.application.phases.head? = some phase := by
        simp only [phases, List.head?_cons]
      obtain ⟨selected, selectedRank, selectedReady, _actorless⟩ :=
        current.execution.application.sample_ready_of_live geometry.1 living.2 geometry.2.2 phase
          head kind
      have selectedEq : selected = event := Fin.ext (selectedRank.trans rank.symm)
      subst selected
      have keptState : TracePrefix anchorTrace (state ▸ history.trace) := by
        have transport : ∀ target (equal : history.state = target),
            TracePrefix anchorTrace (equal ▸ history.trace) := by
          intro target equal
          cases equal
          exact kept
        exact transport _ state
      have preserved := (phase_prefix_semantic_extension runtime leaks menu initial horizon
        scheduler anchor current anchorTrace (state ▸ history.trace) keptState anchorOrdered
          same.symm).1
      have agrees : Store.AgreeOn anchor.execution.application.current.native.config.store
          current.execution.application.current.native.config.store law.readFields := by
        intro selected selectedRead
        have available := anchor.execution.application.current.native.config.read_available ready
          (show selected ∈ (graph.nodes event).readFields from by
            rw [← EventCode.readFields_cast output (graph.nodes event), code]
            exact selectedRead)
        obtain ⟨value, present⟩ := Option.isSome_iff_exists.mp available
        exact present.trans (preserved selected value present).symm
      have actualEval : law.eval? current.execution.application.current.native.config.store =
          some draw := (law.eval?_congr _ _ agrees).symm.trans evaluates
      have row := phaseProposal_sample_control_harmonic runtime leaks bounds initial horizon
        scheduler profile history current state geometry.1 phase remaining phases kind event rank
          selectedReady payload law output code draw actualEval
      have actualRow : (model.runBehavioralFrom profile 1 history).bind
          (fun after => potential after.state) = potential history.state := by
        have right : potential history.state = draw.map some := by
          simp only [potential, state, same, ite_true]
        rw [right]
        convert row using 1
        congr 1
        funext after
        cases after.state with
        | none => rfl
        | some control =>
            change (if control.execution.application.attempt =
                anchor.execution.application.attempt then _ else _) =
              (if control.execution.application.attempt =
                current.execution.application.attempt then _ else _)
            rw [same]
      rw [model.runBehavioralUntil_of_running certificate profile halt ended, PMF.map_bind]
      calc
        _ = (model.runBehavioralFrom profile 1 history).bind
            (fun after => potential after.state) := by
          apply bind_congr_on_support
          intro after supported
          obtain ⟨⟨joint, legal, realized⟩, _future⟩ :=
            model.mem_support_runBehavioralFrom_one profile ended supported
          have moved : after.state ∈
              (app.transition initial horizon scheduler (some current) joint).support := by
            change after.state ∈
              (app.transition initial horizon scheduler history.state joint).support at realized
            simpa only [state] using realized
          obtain ⟨next, nextState, _recall⟩ := app.transition_recall_prefix initial horizon
            scheduler current after.state joint moved
          have retained := (model.runBehavioralFrom_reachesWithin profile 1 history after
            supported).tracePrefix
          apply ih after ⟨joint, legal, realized⟩ (kept.trans retained)
          refine ⟨next, nextState, ?_⟩
          intro nextSame
          have actual : some next ∈
              (app.transition initial horizon scheduler (some current) joint).support := by
            rwa [nextState] at moved
          exact (((phaseApplication_sameAttempt_controls runtime leaks).transition initial horizon
            scheduler current next joint actual currentOrdered (same.trans nextSame.symm)).1).trans
              (phasesKept same)
        _ = _ := actualRow
  have result := stoppedLaw ⟨some anchor, anchorTrace⟩ .refl ⟨anchor, rfl, fun _ => rfl⟩
  simpa only [potential, ite_true] using result

end Vegas
