/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationPredrawSupport
import Vegas.Pending.Service

/-! # Service-command support under setup-wide predrawing -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Δ : VCtx Player L}

/-- Forget application-trigger authority when interpreting a predrawn full
environment response as a wire response. -/
def environmentCommandToWire
    (runtime : GraphRuntime Player L Δ) :
    runtime.application.EnvironmentPolicyCommand → WireCommand Player
  | .deliver observer id => .deliver observer id
  | .include id => .include id
  | .application _ => .wait
  | .wait => .wait

/-- Reinstall a predrawn full response only at ordinary wire slots; reserved
service slots continue to be computed from the live history and view. -/
def predrawnServiceEnvironment (runtime : GraphRuntime Player L Δ)
    (plan : List (ServiceInstruction Player))
    (response : runtime.application.InvocationSite (.environment) →
      runtime.application.InvocationCommand (.environment)) :
    runtime.application.EnvironmentPolicy :=
  runtime.serviceEnvironment plan fun history view =>
    FinDist.pure (runtime.environmentCommandToWire (response (history, view)))

@[simp] theorem environmentCommandToWire_toEnvironmentCommand
    (runtime : GraphRuntime Player L Δ) (command : WireCommand Player) :
    runtime.environmentCommandToWire
      (WireCommand.toEnvironmentCommand runtime.application command) = command := by
  cases command <;> rfl

/-- A deterministic service command at a selected setup-wide environment site
is retained by every supported pure response. In particular this applies to
reserved inclusion and expiry slots, so predrawing cannot replace them by an
arbitrary off-support fallback along a reachable pure execution. -/
theorem setupResponseMixture_service_command
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (initials : FinDist runtime.application.PolicyExecution)
    (response : runtime.application.InvocationSite (.environment) →
      runtime.application.InvocationCommand (.environment))
    (supported : response ∈
      (runtime.application.setupResponseMixture players
        (runtime.serviceEnvironment plan wire) .environment schedule initials
        (fun site => runtime.serviceEnvironment plan wire site.1 site.2)).support)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (command : runtime.application.EnvironmentPolicyCommand)
    (selected : some (history, view) ∈ runtime.application.setupFocalSites players
      (runtime.serviceEnvironment plan wire) .environment schedule initials
      (fun site => runtime.serviceEnvironment plan wire site.1 site.2))
    (mandatory : runtime.serviceEnvironment plan wire history view = FinDist.pure command) :
    response (history, view) = command := by
  have member := runtime.application.setupResponseMixture_apply_mem_support players
    (runtime.serviceEnvironment plan wire) .environment schedule initials
    (fun site => runtime.serviceEnvironment plan wire site.1 site.2)
    response supported (history, view) selected
  rw [mandatory] at member
  simpa using member

/-- At a selected ordinary wire slot, decoding a supported full predrawn
environment response and re-embedding it as a wire command recovers the
original response exactly. Application commands are excluded by support of the
real wire kernel. -/
theorem setupResponseMixture_wire_command
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (initials : FinDist runtime.application.PolicyExecution)
    (response : runtime.application.InvocationSite (.environment) →
      runtime.application.InvocationCommand (.environment))
    (supported : response ∈
      (runtime.application.setupResponseMixture players
        (runtime.serviceEnvironment plan wire) .environment schedule initials
        (fun site => runtime.serviceEnvironment plan wire site.1 site.2)).support)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (selected : some (history, view) ∈ runtime.application.setupFocalSites players
      (runtime.serviceEnvironment plan wire) .environment schedule initials
      (fun site => runtime.serviceEnvironment plan wire site.1 site.2))
    (slot : (plan.filterMap
      ServiceInstruction.environmentSlot)[history.length]? = some .wire) :
    WireCommand.toEnvironmentCommand runtime.application
        (runtime.environmentCommandToWire (response (history, view))) =
      response (history, view) := by
  have member := runtime.application.setupResponseMixture_apply_mem_support players
    (runtime.serviceEnvironment plan wire) .environment schedule initials
    (fun site => runtime.serviceEnvironment plan wire site.1 site.2)
    response supported (history, view) selected
  rw [runtime.serviceEnvironment_wire plan wire history view slot] at member
  unfold MessageApplication.wireEnvironment at member
  rw [FinDist.support_map] at member
  obtain ⟨command, _, commandEq⟩ := member
  rw [← commandEq, runtime.environmentCommandToWire_toEnvironmentCommand]

/-- On every selected setup-wide environment site, the service wrapper around
the decoded pure wire response is exactly the original pure full response. -/
theorem predrawnServiceEnvironment_eq_response
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (initials : FinDist runtime.application.PolicyExecution)
    (response : runtime.application.InvocationSite (.environment) →
      runtime.application.InvocationCommand (.environment))
    (supported : response ∈
      (runtime.application.setupResponseMixture players
        (runtime.serviceEnvironment plan wire) .environment schedule initials
        (fun site => runtime.serviceEnvironment plan wire site.1 site.2)).support)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (selected : some (history, view) ∈ runtime.application.setupFocalSites players
      (runtime.serviceEnvironment plan wire) .environment schedule initials
      (fun site => runtime.serviceEnvironment plan wire site.1 site.2)) :
    runtime.predrawnServiceEnvironment plan response history view =
      FinDist.pure (response (history, view)) := by
  cases slotEq : (plan.filterMap
      ServiceInstruction.environmentSlot)[history.length]? with
  | none =>
      have fixed := runtime.setupResponseMixture_service_command players plan wire schedule initials
        response supported history view .wait selected (by simp [serviceEnvironment, slotEq])
      simp [predrawnServiceEnvironment, serviceEnvironment, slotEq, fixed]
  | some instruction =>
      cases instruction with
      | player who =>
          have fixed := runtime.setupResponseMixture_service_command players plan wire schedule
            initials response supported history view .wait selected
              (by simp [serviceEnvironment, slotEq])
          simp [predrawnServiceEnvironment, serviceEnvironment, slotEq, fixed]
      | wire =>
          have fixed := runtime.setupResponseMixture_wire_command players plan wire schedule
            initials response supported history view selected slotEq
          simpa [predrawnServiceEnvironment, serviceEnvironment, slotEq,
            MessageApplication.wireEnvironment] using congrArg FinDist.pure fixed
      | includeLatest who =>
          have fixed := runtime.setupResponseMixture_service_command players plan wire schedule
            initials response supported history view
              (runtime.application.latestSubmissionCommand who view) selected
              (by simp [serviceEnvironment, slotEq])
          simp [predrawnServiceEnvironment, serviceEnvironment, slotEq, fixed]
      | expire phase =>
          let command : runtime.application.EnvironmentPolicyCommand :=
            if view.application.pc = phase then .application .tick else .wait
          have fixed := runtime.setupResponseMixture_service_command players plan wire schedule
            initials response supported history view command selected
              (by simp [serviceEnvironment, slotEq, command])
          simp [predrawnServiceEnvironment, serviceEnvironment, slotEq, command, fixed]

/-- For each supported setup response and supported initial execution, replacing
the full pure environment response by its service-preserving wire wrapper does
not change the complete trace law. -/
theorem predrawnServiceEnvironment_tracePolicies
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (initials : FinDist runtime.application.PolicyExecution)
    (response : runtime.application.InvocationSite (.environment) →
      runtime.application.InvocationCommand (.environment))
    (supported : response ∈
      (runtime.application.setupResponseMixture players
        (runtime.serviceEnvironment plan wire) .environment schedule initials
        (fun site => runtime.serviceEnvironment plan wire site.1 site.2)).support)
    (initial : runtime.application.PolicyExecution) (hinitial : initial ∈ initials.support) :
    runtime.application.tracePolicies players
        (fun history view => FinDist.pure (response (history, view))) schedule initial =
      runtime.application.tracePolicies players
        (runtime.predrawnServiceEnvironment plan response) schedule initial := by
  let app := runtime.application
  let environment := runtime.serviceEnvironment plan wire
  let M := app.focalInformation players environment .environment schedule initial
  let start := (app.focalProtocol players environment .environment schedule initial).initHistory
  let purePolicy : (i : Unit) → M.BehavioralPolicy i := fun _ =>
    app.focalBehavioral players environment .environment schedule initial
      (fun site => FinDist.pure (response site))
  let wrappedPolicy : (i : Unit) → M.BehavioralPolicy i := fun _ =>
    app.focalBehavioral players environment .environment schedule initial
      (fun site => runtime.predrawnServiceEnvironment plan response site.1 site.2)
  have modelEq : M.runBehavioralFrom purePolicy schedule.length start =
      M.runBehavioralFrom wrappedPolicy schedule.length start := by
    apply M.runBehavioralFrom_congr_on_support
    intro elapsed helapsed later laterSupported _ i
    cases i
    cases infoEq : M.infoOf () later.trace with
    | none => simp [purePolicy, wrappedPolicy, MessageApplication.focalBehavioral]
    | some site =>
        have selected := app.focal_pureResponse_info_mem_setupFocalSites players environment
          .environment schedule initials (fun site => environment site.1 site.2) response supported
          initial hinitial elapsed helapsed later laterSupported
        rw [infoEq] at selected
        have localEq := runtime.predrawnServiceEnvironment_eq_response players plan wire schedule
          initials response supported site.1 site.2 selected
        simp [purePolicy, wrappedPolicy, MessageApplication.focalBehavioral, localEq]
  have left := app.focal_runBehavioralFrom players environment .environment schedule initial
    (fun site => FinDist.pure (response site)) start
  have right := app.focal_runBehavioralFrom players environment .environment schedule initial
    (fun site => runtime.predrawnServiceEnvironment plan response site.1 site.2) start
  have hprefix : app.focalRecordedTrace players environment .environment schedule initial start =
      id := rfl
  simpa [hprefix, start, ExecutionProtocol.initHistory_state,
    MessageApplication.playersReplacing, MessageApplication.environmentReplacing] using
    left.symm.trans ((congrArg (FinDist.map fun result =>
      app.focalRecordedTrace players environment .environment schedule initial result
        (.finish result.state.execution)) modelEq).trans right)

/-- A single setup-wide draw of a pure wire policy preserves the complete
execution law while reserved service slots remain live in `serviceEnvironment`.
The draw precedes the finite initial execution law. -/
theorem exists_service_wire_response_mixture_runPolicies_setup
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (initials : FinDist runtime.application.PolicyExecution) :
    ∃ mixture : FinDist (runtime.application.InvocationSite (.environment) →
        WireCommand Player),
      mixture.bind (fun response => initials.bind fun initial =>
        runtime.application.runPolicies players
          (runtime.serviceEnvironment plan
            (fun history view => FinDist.pure (response (history, view))))
          schedule initial) =
      initials.bind fun initial => runtime.application.runPolicies players
        (runtime.serviceEnvironment plan wire) schedule initial := by
  let environment := runtime.serviceEnvironment plan wire
  let responses := runtime.application.setupResponseMixture players environment .environment
    schedule initials (fun site => environment site.1 site.2)
  refine ⟨responses.map (fun response site =>
    runtime.environmentCommandToWire (response site)), ?_⟩
  rw [FinDist.bind_map]
  calc
    _ = responses.bind (fun response => initials.bind fun initial =>
          runtime.application.runPolicies players
            (fun history view => FinDist.pure (response (history, view))) schedule initial) := by
      apply FinDist.bind_congr
      intro response responseSupported
      apply FinDist.bind_congr
      intro initial initialSupported
      have traced := runtime.predrawnServiceEnvironment_tracePolicies players plan wire schedule
        initials response responseSupported initial initialSupported
      have last := congrArg (FinDist.map MessageApplication.PolicyTrace.last) traced
      simpa only [runtime.application.tracePolicies_last, predrawnServiceEnvironment] using
        last.symm
    _ = _ := by
      exact runtime.application.setupResponseMixture_runPolicies_setup players environment
        .environment schedule initials (fun site => environment site.1 site.2)

/-- Jointly predraw one focal native player and the adaptive wire policy while
keeping every reserved service command live. The same response pair is used
across the complete finite initial execution law. -/
theorem exists_joint_service_response_mixture_runPolicies_setup
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy)
    (who : Player) (schedule : List (@MessageApplication.Invocation Player))
    (initials : FinDist runtime.application.PolicyExecution)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ mixture : FinDist
        ((List runtime.application.PlayerEntry → runtime.application.View →
            runtime.application.PlayerCommand) ×
          (runtime.application.InvocationSite (.environment) → WireCommand Player)),
      mixture.bind (fun responses => initials.bind fun initial =>
        runtime.application.runPolicies
          (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
            players who (fun history view => FinDist.pure (responses.1 history view)))
          (runtime.serviceEnvironment plan
            (fun history view => FinDist.pure (responses.2 (history, view))))
          schedule initial) =
      initials.bind fun initial => runtime.application.runPolicies
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          players who replacement)
        (runtime.serviceEnvironment plan wire) schedule initial := by
  obtain ⟨playerResponses, playerTraceLaw⟩ :=
    runtime.application.exists_native_response_mixture_tracePolicies_setup players
      (runtime.serviceEnvironment plan wire) who schedule initials replacement
  have playerLaw := congrArg (FinDist.map MessageApplication.PolicyTrace.last) playerTraceLaw
  simp only [FinDist.map_bind, runtime.application.tracePolicies_last] at playerLaw
  let PlayerResponse := List runtime.application.PlayerEntry → runtime.application.View →
    runtime.application.PlayerCommand
  let WireResponse := runtime.application.InvocationSite (.environment) → WireCommand Player
  have wireExists (response : PlayerResponse) : ∃ mixture : FinDist WireResponse,
      mixture.bind (fun wireResponse => initials.bind fun initial =>
        runtime.application.runPolicies
          (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
            players who (fun history view => FinDist.pure (response history view)))
          (runtime.serviceEnvironment plan
            (fun history view => FinDist.pure (wireResponse (history, view)))) schedule initial) =
      initials.bind fun initial => runtime.application.runPolicies
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          players who (fun history view => FinDist.pure (response history view)))
        (runtime.serviceEnvironment plan wire) schedule initial :=
    runtime.exists_service_wire_response_mixture_runPolicies_setup
      (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
        players who (fun history view => FinDist.pure (response history view)))
      plan wire schedule initials
  let wireResponses (response : PlayerResponse) := Classical.choose (wireExists response)
  refine ⟨playerResponses.bind (fun response =>
    (wireResponses response).map fun wireResponse => (response, wireResponse)), ?_⟩
  rw [FinDist.bind_bind]
  calc
    _ = playerResponses.bind (fun response => initials.bind fun initial =>
          runtime.application.runPolicies
            (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
              players who (fun history view => FinDist.pure (response history view)))
            (runtime.serviceEnvironment plan wire) schedule initial) := by
      apply FinDist.bind_congr
      intro response _
      rw [FinDist.bind_map]
      exact Classical.choose_spec (wireExists response)
    _ = _ := playerLaw

end Vegas.GraphRuntime
