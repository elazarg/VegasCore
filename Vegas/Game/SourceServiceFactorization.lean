/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRoster
import Vegas.Game.SourceServiceDisclosure
import Vegas.Pending.ReactiveOpeningLikelihood
import GameTheory.Math.Probability.ConditionalObservation
import Vegas.Source.ObservationRecall
import Vegas.Game.SourceServiceCheckpoint
import Vegas.Game.ServiceObservation
import Vegas.Pending.ReactiveBindingTranscript
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Source memory and actual service-channel factorization

The proof law retains both the effective source configuration and its original
private intentions. Only the former is decoded from the native execution.
Binding timing, passive sampling, silence, and inclusion use the existing
runtime evaluator. Their conditional likelihood is derived from those actual
operations, rather than supplied as an independent channel hypothesis.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Correlated initial draws with the same source view have identical native
traffic projections, including the genuine owned initial candidate catalogue. -/
theorem source_initial_traffic_eq
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) (left right : State L setup.context)
    (same : (setup.initialConfig left).view focal = (setup.initialConfig right).view focal) :
    (serviceRuntime setup mode deadline).bindingTraffic leaks focal
        (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
          (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
              (setup.eventInputs left))) =
      (serviceRuntime setup mode deadline).bindingTraffic leaks focal
        (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
          (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
              (setup.eventInputs right))) := by
  have first := SourceCheckpoint.initial (mode := mode) setup left
  have second := SourceCheckpoint.initial (mode := mode) setup right
  have observed := checkpoint_playerObservation_eq_of_order setup _ 0
    (ContextRefs.initial_coversPrefix setup.program) focal _ _ _ _ (by rfl) first.ordered
    second.ordered first.agrees second.agrees first.history second.history same
  have publics : (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs left)).publicView =
      (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs right)).publicView :=
    EventGraphRuntime.State.initial_publicView_eq_of_observation (graph := serviceGraph setup mode)
        focal (setup.eventInputs left) (setup.eventInputs right) observed
  have candidates := EventGraphRuntime.State.initial_candidates_eq_of_observation
    (graph := serviceGraph setup mode) focal (setup.eventInputs left)
    (setup.eventInputs right) observed
  have views : (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs left)).playerView focal =
      (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs right)).playerView focal := by
    unfold EventGraphRuntime.State.playerView
    rw [publics, observed, candidates]
  unfold EventGraphRuntime.bindingTraffic
  dsimp only [ReactiveApplication.Execution.initial]
  rw [views, publics]

/-- The induction starts from the actual supplied initial law. There is no
independence assumption on private types, and original and effective histories
are paired only at initialization, before any intention can be erased. -/
theorem source_initial_memory_factorization
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) :
    ∃ noise : DecisionView focal setup.context → PMF _,
      setup.initialLaw.map (fun initial =>
        ((setup.initialConfig initial, setup.initialConfig initial),
          (serviceRuntime setup mode deadline).bindingTraffic leaks focal
            (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
              (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
                (setup.eventInputs initial))))) =
      (setup.initialLaw.map fun initial =>
        (setup.initialConfig initial, setup.initialConfig initial)).bind fun pair =>
          (noise (pair.1.view focal)).map fun extra => (pair, extra) := by
  classical
  let read := fun initial : State L setup.context =>
    (serviceRuntime setup mode deadline).bindingTraffic leaks focal
      (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
        (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
            (setup.eventInputs initial)))
  let noise := fun view : DecisionView focal setup.context =>
    if present : ∃ initial ∈ setup.initialLaw.support,
        (setup.initialConfig initial).view focal = view then
      PMF.pure (read present.choose)
    else PMF.pure (read setup.initialLaw.support_nonempty.choose)
  refine ⟨noise, ?_⟩
  rw [PMF.bind_map]
  change setup.initialLaw.bind (fun initial => PMF.pure
      ((setup.initialConfig initial, setup.initialConfig initial), read initial)) = _
  apply bind_congr_on_support _
  intro initial supported
  have present : ∃ other ∈ setup.initialLaw.support,
      (setup.initialConfig other).view focal = (setup.initialConfig initial).view focal :=
    ⟨initial, supported, rfl⟩
  simp only [noise, Function.comp_apply, dite_eq_left present, PMF.pure_map]
  rw [show read initial = read present.choose from
    source_initial_traffic_eq setup leaks focal initial present.choose present.choose_spec.2.symm]

/-- A real clock step or expiry preserves the traffic factorization.
The carried source configuration is proof data; the native application still
performs the specified command, including its public effects and service recall. -/
theorem source_maintenance_factorization
    {Seed Source View : Type}
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) (prior : PMF Seed) (source : Seed → Source)
    (observe : Source → View)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (noise : View → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (serviceRuntime setup mode deadline).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (observe config)).map fun extra => (config, extra))
    (command : EnvironmentCommand (serviceGraph setup mode))
    (maintenance : ∀ event, command ≠ .executeSample event) :
    ∃ nextNoise : View → PMF _,
      (prior.bind fun seed =>
        ((execution seed).environmentStep (serviceApplication setup mode deadline leaks)
            (.application command)).map fun final =>
        (source seed, (serviceRuntime setup mode deadline).bindingTraffic leaks focal final)) =
      (prior.map source).bind fun config =>
        (nextNoise (observe config)).map fun extra => (config, extra) := by
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (serviceRuntime setup mode deadline).bindingTraffic leaks focal (execution seed))
    observe noise factor (fun _ => PMF.pure Unit.unit)
    (fun config _ => config) observe
    (fun seed _ => ((execution seed).environmentStep (serviceApplication setup mode deadline leaks)
      (.application command)).map ((serviceRuntime setup mode deadline).bindingTraffic leaks focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left _ _ _ right _ _ _ _ same =>
      (serviceRuntime setup mode deadline).bindingTraffic_maintenance leaks (execution left)
      (execution right) focal same command maintenance)
  exact ⟨nextNoise, by simpa only [PMF.pure_bind, PMF.pure_map,
    PMF.bind_pure, PMF.map_id, PMF.map_comp, Function.comp_def] using law⟩

/-- Passive activation turns the complete traffic factorization into a law
for the player's actual input: its response history and current observation.
The same network sample is used on each coupled branch; no observer receives
another player's sample or any of the auxiliary proof projection. -/
theorem source_activation_input_factorization
    {Seed Source View : Type}
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (focal : Player) (prior : PMF Seed) (source : Seed → Source)
    (observe : Source → View)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (noise : View → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (serviceRuntime setup mode deadline).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (observe config)).map fun extra => (config, extra)) :
    ∃ channel : View → PMF
        (List (serviceApplication setup mode deadline leaks).PlayerEntry ×
            (serviceApplication setup mode deadline leaks).PlayerView),
      (prior.bind fun seed =>
        ((execution seed).environmentStep (serviceApplication setup mode deadline leaks)
            (.activate focal)).map fun final =>
        (source seed,
            (final.recall focal, final.observe (serviceApplication setup mode deadline leaks)
            focal))) =
      (prior.map source).bind fun config =>
        (channel (observe config)).map fun input => (config, input) := by
  let app := serviceApplication setup mode deadline leaks
  have coupled (left right : app.Execution)
      (same : (serviceRuntime setup mode deadline).bindingTraffic leaks focal left =
        (serviceRuntime setup mode deadline).bindingTraffic leaks focal right) :
      (left.environmentStep app (.activate focal)).map
          (fun final => (final.recall focal, final.observe app focal)) =
        (right.environmentStep app (.activate focal)).map
          (fun final => (final.recall focal, final.observe app focal)) := by
    have networks : left.network = right.network := congrArg Prod.fst same
    simp only [ReactiveApplication.Execution.activation_samples, PMF.map_comp]
    rw [networks]
    apply map_congr_on_support _
    intro sample _supported
    let first := left.sampledActivation app focal sample
    let second := right.sampledActivation app focal sample
    have equal := (serviceRuntime setup mode deadline).bindingTraffic_activation leaks left right
        focal focal same sample
    have sampledNetworks : first.network = second.network := congrArg Prod.fst equal
    have receipts : first.receipts = second.receipts :=
      congrArg (fun traffic => traffic.2.1) equal
    have recalled : first.recall focal = second.recall focal :=
      congrArg (fun traffic => traffic.2.2.2.1) equal
    have views : first.application.playerView focal = second.application.playerView focal :=
      congrArg (fun traffic => traffic.2.2.2.2.1) equal
    change (first.recall focal, first.observe app focal) =
      (second.recall focal, second.observe app focal)
    apply Prod.ext recalled
    change ReactiveApplication.PlayerView.mk _ _ _ = _
    rw [sampledNetworks]
    exact congrArg₂ (fun view evidence =>
      (⟨second.network.observe focal, view, evidence⟩ : app.PlayerView)) views receipts
  obtain ⟨channel, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (serviceRuntime setup mode deadline).bindingTraffic leaks focal (execution seed))
    observe noise factor (fun _ => PMF.pure Unit.unit)
    (fun config _ => config) observe
    (fun seed _ => ((execution seed).environmentStep app (.activate focal)).map
      fun final => (final.recall focal, final.observe app focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left _ _ _ right _ _ _ _ same => coupled (execution left) (execution right) same)
  exact ⟨channel, by simpa only [PMF.pure_bind, PMF.pure_map,
    PMF.bind_pure, PMF.map_id, PMF.map_comp, Function.comp_def] using law⟩

omit [IExpr.ResultTypes L] in
private theorem commit_view_reflects {Γ : SourceCtx Player L} {owner : Player}
    {payload : L.Ty} (focal : Player) (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (left right : Config Player L Γ)
    (first second : PublicationResult (L.Val payload))
    (same : (commitSuccessor name guard left first).view focal =
      (commitSuccessor name guard right second).view focal) :
    left.view focal = right.view focal := by
  have earlier := congrArg (DecisionView.back (decide (owner = focal))) same
  simpa only [back_commit_view] using earlier

omit [IExpr.ResultTypes L] in
private theorem commit_choice_of_owner_view {Γ : SourceCtx Player L} {owner : Player}
    {payload : L.Ty} (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (left right : Config Player L Γ) (first second : PublicationResult (L.Val payload))
    (same : (commitSuccessor name guard left first).view owner =
      (commitSuccessor name guard right second).view owner) : first = second := by
  have cell := congrArg (fun view : DecisionView owner ((name, .commitment owner payload) :: Γ) =>
    view.1.cells.get .here) same
  simp only [Config.view, commitSuccessor, sourceObserve, Env.get, Env.cons, ite_true] at cell
  exact Option.some.inj cell

/-- Equal successful guarded publications supply the handler agreement needed
by the actual focal window coupling. Both candidates are recovered from their
current dynamic binding invariants; no initial-catalogue equality is assumed. -/
theorem guarded_opening_handler_focal
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (leftSource rightSource : Config Player L Γ)
    (left right : (application setup leaks).Execution)
    (leftAgrees : refs.Agrees leftSource.state left.application.config.store)
    (rightAgrees : refs.Agrees rightSource.state right.application.config.store)
    (leftBinding : left.application.BindingInvariant)
    (rightBinding : right.application.BindingInvariant)
    (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (leftCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs leftSource.registry
          leftSource.revelations binding))
    (rightCode : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs rightSource.registry
          rightSource.revelations binding))
    (leftNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs leftSource.registry leftSource.revelations
        binding) outputEq leftCode)
    (rightNode : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs rightSource.registry rightSource.revelations
        binding) outputEq rightCode)
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (leftTimely : left.application.WithinDeadline (runtime setup) event)
    (rightTimely : right.application.WithinDeadline (runtime setup) event)
    (value : L.Val payload)
    (leftSuccess : disclosureResult published binding leftSource true = .success value)
    (rightSuccess : disclosureResult published binding rightSource true = .success value)
    (focal : Player)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    ∃ candidate, candidate.1 = owner ∧
      left.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      right.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      rosterOpening? setup leaks owner event (left.observe (application setup leaks) owner) =
        some (candidate, ⟨payload, value⟩) ∧
      rosterOpening? setup leaks owner event (right.observe (application setup leaks) owner) =
        some (candidate, ⟨payload, value⟩) ∧
      ((application setup leaks).handle left.application
        ((runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ left)).map
          (fun state => state.playerView focal) =
      ((application setup leaks).handle right.application
        ((runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ left)).map
          (fun state => state.playerView focal) := by
  obtain ⟨candidate, leftAssociated, owned, leftValid, leftOpening⟩ :=
    guarded_rosterOpening_success setup leaks published binding leftSource refs left leftAgrees
      leftBinding event outputEq leftCode leftNode value leftSuccess
  obtain ⟨other, rightAssociated, _, rightValid, rightOpening⟩ :=
    guarded_rosterOpening_success setup leaks published binding rightSource refs right rightAgrees
      rightBinding event outputEq rightCode rightNode value rightSuccess
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun read => read.2.2.2.2.2) same
  have accepted : left.application.accepted = right.application.accepted :=
    congrArg EventGraphRuntime.PublicView.accepted publics
  have candidateEq : candidate = other := Option.some.inj
    (leftAssociated.symm.trans ((congrFun accepted (refs.get binding).field).trans rightAssociated))
  subst other
  refine ⟨candidate, owned, leftValid, rightValid, leftOpening, rightOpening, ?_⟩
  have stored (source : Config Player L Γ) (native : EventGraphRuntime.State (graph setup))
      (agrees : refs.Agrees source.state native.config.store)
      (success : disclosureResult published binding source true = .success value) :
      (refs.get binding).get? native.config.store = some (.success value) := by
    have original : source.state.get binding = .success value := by
      simp only [disclosureResult, revealSuccessor, ite_true, Env.cons_get_here] at success
      split at success
      · exact success
      · cases success
    simpa only [original, cellValue] using agrees binding
  have leftResolved := compiled_disclosure_result published binding leftSource refs
    left.application.config.store leftAgrees true
  have rightResolved := compiled_disclosure_result published binding rightSource refs
    right.application.config.store rightAgrees true
  rw [leftSuccess, EventGraph.EventCode.resolveOutput?_playerStore] at leftResolved
  rw [rightSuccess, EventGraph.EventCode.resolveOutput?_playerStore] at rightResolved
  have first := handle_opening_eq (runtime setup) left.application
    (owner, left.network.nextSerial owner) event candidate owner payload (refs.get binding)
      _ outputEq leftCode leftNode leftReady leftTimely rfl owned leftAssociated value leftValid
        (stored leftSource left.application leftAgrees leftSuccess) (.success value) leftResolved
  have second := handle_opening_eq (runtime setup) right.application
    (owner, left.network.nextSerial owner) event candidate owner payload (refs.get binding)
      _ outputEq rightCode rightNode rightReady rightTimely rfl owned rightAssociated value
        rightValid (stored rightSource right.application rightAgrees rightSuccess)
          (.success value) rightResolved
  have valid := (runtime setup).windowEnvelope_tokenValid leaks owner event candidate
    ⟨payload, value⟩ left leftReady
  rw [reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _ valid,
    reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _ valid]
  change (handle (runtime setup) left.application
      ⟨(owner, left.network.nextSerial owner), .opening event candidate ⟨payload, value⟩⟩).map _ =
    (handle (runtime setup) right.application
      ⟨(owner, left.network.nextSerial owner), .opening event candidate ⟨payload, value⟩⟩).map _
  rw [first, second, Option.map_some, Option.map_some]
  apply congrArg some
  have views : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun read => read.2.2.2.2.1) same
  exact EventGraphRuntime.State.complete_playerView_congr left.application right.application focal
    publics (left.application.playerView_observation_eq right.application focal views)
      (congrArg EventGraphRuntime.PlayerView.candidates views) event leftReady rightReady
        _ _ _ _ (fun _ => rfl) (fun _ => rfl)

end Vegas
