/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOffTurnRepair
import Vegas.Pending.ReactiveBindingForeignWindow
import Interaction.ReactiveTrafficContinuation
import Interaction.ReactiveAllocation

/-! # Stopped repair through an off-turn response window

Every player keeps the complete raw response interface. At a phase owned by
another player, or a public chance phase, the focal player's known replays and
silence preserve the paired executions. Fresh focal submissions create an
attributed forbidden record. The unchanged physical law and the single fixed
private implementation continue after that stopping event.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private def departed (owner : Player)
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∃ record ∈ (runtime.reactiveApplication leaks).executionTraffic execution,
    record.input.envelope.sender = owner ∧
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = false

omit [Fintype Player] in
private theorem activation_resources
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution) (actor : Player)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players (.activate actor)
      execution).support) :
    next.InputRecall (runtime.reactiveApplication leaks) ∧ next.network.SerialsBeforeNext ∧
      next.application.serviceGrant = execution.application.serviceGrant := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
  have middleRecall := app.environment_inputRecall execution middle (.activate actor) recalled moved
  have middleSerials := (app.serialsBeforeNextInvariant
    (fun _ _ => PMF.pure (.activate actor))).environment execution middle (.activate actor)
      serials ((PMF.mem_support_pure_iff _ _).mpr rfl) moved
  refine ⟨app.respond_inputRecall middle actor response middleRecall,
    (app.serialsBeforeNextInvariant (fun _ _ => PMF.pure .wait)).respond
      middle actor response middleSerials, ?_⟩
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸
    ((congrArg (fun law : PMF app.Execution => middle ∈ law.support)
      (ReactiveApplication.Execution.activation_samples app execution actor)).mp moved)
  exact congrArg PublicView.serviceGrant
    (reactive_respond_application runtime leaks _ actor response).2

omit [Fintype Player] in
private theorem activation_step_evidence
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution) (actor : Player)
    (reached : next ∈ ((runtime.reactiveApplication leaks).dispatch players (.activate actor)
      execution).support) (remaining : Nat)
    (record : (runtime.reactiveApplication leaks).TrafficRecord)
    (step : (runtime.reactiveApplication leaks).trafficStep
      (some ⟨remaining + 1, none, execution⟩) (some ⟨remaining, none, next⟩) = [record]) :
    record ∈ (runtime.reactiveApplication leaks).executionTraffic next := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
  rw [app.executionTraffic_activated_response execution middle actor response remaining moved,
    step]
  exact List.mem_append_right _ (List.mem_singleton_self _)

omit [Fintype Player] in
private theorem private_activation_recall {Memory : Type}
    (strategy : (runtime.reactiveApplication leaks).Implementation Memory)
    (players : Player → (runtime.reactiveApplication leaks).Policy) (owner actor : Player)
    (execution : (runtime.reactiveApplication leaks).Execution) (memory : Memory)
    (next : (runtime.reactiveApplication leaks).Execution × Memory)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (supported : next ∈ ((execution.environmentStep (runtime.reactiveApplication leaks)
      (.activate actor)).bind (fun current => strategy.resume owner players (some actor)
        current memory)).support) :
    next.1.InputRecall (runtime.reactiveApplication leaks) := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  have valid := app.environment_inputRecall execution middle (.activate actor) recalled moved
  by_cases same : actor = owner
  · subst actor
    simp only [ReactiveApplication.Implementation.resume, ↓reduceIte] at resumed
    obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
    exact app.respond_inputRecall middle owner response.1 valid
  · simp only [ReactiveApplication.Implementation.resume, same, ↓reduceIte] at resumed
    obtain ⟨final, reached, rfl⟩ := PMF.support_map .. ▸ resumed
    obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ reached
    exact app.respond_inputRecall middle actor response valid

omit [Fintype Player] in
private theorem foreign_activation_view
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (execution next : (runtime.reactiveApplication leaks).Execution) (actor owner : Player)
    (different : actor ≠ owner)
    (supported : next ∈ ((runtime.reactiveApplication leaks).dispatch players (.activate actor)
      execution).support) :
    next.application.playerView owner = execution.application.playerView owner := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
  rw [ReactiveApplication.Execution.activation_samples] at moved
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ moved
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id => rfl
      | submit material =>
          exact (submitStep_playerView_other (material.call.register execution.application actor)
            actor owner different.symm material.call.packet).trans
              (material.call.register_other execution.application actor owner different.symm)

namespace BindingMemory.Frame

variable {runtime leaks} {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

private theorem off_turn_owner_activation_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (serials : original.network.SerialsBeforeNext)
    (offTurn : ∀ event, original.application.serviceGrant = some event →
      graph.actor? event ≠ some owner)
    (coverage : ∀ past view,
      (∀ event, view.application.publicView.serviceGrant = some event →
        graph.actor? event ≠ some owner) →
      ∀ response ∈ ((runtime.reactiveApplication leaks).replayPolicy past view).support,
        response ∈ menu.actions owner past view)
    (available : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ (bounds.menu runtime leaks).actions owner past view) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.dispatch players (.activate owner) original ∧
      coupling.map Prod.snd = (repaired.environmentStep app (.activate owner)).bind
        (fun execution => strategy.resume owner players (some owner) execution memory) ∧
      ∀ next ∈ coupling.support,
        (∃ record, app.trafficStep (some ⟨1, none, original⟩)
            (some ⟨0, none, next.1⟩) = [record] ∧
          record.input.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.2.2.shadow = memory.shadow ∧
          next.2.1.application.playerView owner = repaired.application.playerView owner) := by
  classical
  intro app strategy
  let sample := leaks owner original.network.pending
  have rightOffTurn : ∀ event, repaired.application.serviceGrant = some event →
      graph.actor? event ≠ some owner := by
    intro event granted
    exact offTurn event ((congrArg PublicView.serviceGrant frame.publicView).trans granted)
  have existsStep (selected) (_supported : selected ∈ sample.support) :=
    (frame.activate owner selected).off_turn_stopped_response_coupling
      bounds menu players reference started leftRecall rightRecall (serials.learn owner selected)
        0 offTurn (coverage _ _ rightOffTurn) (available _ _)
  let step := fun selected supported => (existsStep selected supported).choose
  refine ⟨sample.bindOnSupport step, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    change _ = (original.environmentStep app (.activate owner)).bind _
    rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected supported
    exact (existsStep selected supported).choose_spec.1
  · rw [map_bindOnSupport, ReactiveApplication.Execution.activation_samples,
      PMF.bind_map]
    have same : leaks owner repaired.network.pending = sample := by rw [← frame.network]
    change _ = (leaks owner repaired.network.pending).bind _
    rw [same]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected supported
    exact (existsStep selected supported).choose_spec.2.1
  · intro next supported
    obtain ⟨selected, member, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
    exact (existsStep selected member).choose_spec.2.2 next reached

private theorem off_turn_activation_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (serials : original.network.SerialsBeforeNext)
    (offTurn : ∀ event, original.application.serviceGrant = some event →
      graph.actor? event ≠ some owner)
    (coverage : ∀ past view,
      (∀ event, view.application.publicView.serviceGrant = some event →
        graph.actor? event ≠ some owner) →
      ∀ response ∈ ((runtime.reactiveApplication leaks).replayPolicy past view).support,
        response ∈ menu.actions owner past view)
    (available : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ (bounds.menu runtime leaks).actions owner past view)
    (actor : Player) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.dispatch players (.activate actor) original ∧
      coupling.map Prod.snd = (repaired.environmentStep app (.activate actor)).bind
        (fun execution => strategy.resume owner players (some actor) execution memory) ∧
      ∀ next ∈ coupling.support,
        departed runtime leaks owner next.1 ∨
          (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
            reference.length ≤ (next.2.1.recall owner).length ∧
            next.2.2.shadow = memory.shadow ∧
            next.2.1.application.playerView owner = repaired.application.playerView owner) := by
  classical
  let app := runtime.reactiveApplication leaks
  by_cases same : actor = owner
  · subst actor
    obtain ⟨coupling, first, second, related⟩ :=
      frame.off_turn_owner_activation_coupling bounds menu players reference started
        leftRecall rightRecall serials offTurn coverage available
    refine ⟨coupling, first, second, ?_⟩
    intro next supported
    rcases related next supported with ⟨record, step, authored, rejected⟩ | good
    · left
      refine ⟨record, ?_, authored, rejected⟩
      apply runtime.activation_step_evidence leaks players original next.1 owner
        _ 0 record step
      rw [← first, PMF.support_map]
      exact ⟨next, supported, rfl⟩
    · exact Or.inr good
  · obtain ⟨coupling, first, second, related⟩ :=
      frame.foreign_activation_coupling players actor same
    let lifted := coupling.map fun next => (next.1, next.2, memory)
    refine ⟨lifted, ?_, ?_, ?_⟩
    · simpa only [lifted, PMF.map_comp, Function.comp_def] using first
    · change (coupling.map fun next => (next.1, next.2, memory)).map Prod.snd = _
      rw [PMF.map_comp]
      calc
        _ = (coupling.map Prod.snd).map (fun execution => (execution, memory)) := by
          rw [PMF.map_comp]; rfl
        _ = _ := by
          rw [second, ReactiveApplication.dispatch, PMF.map_bind]
          apply bind_congr_on_support _
          intro execution _
          simp only [ReactiveApplication.resume, ReactiveApplication.Command.actor?,
            ReactiveApplication.Implementation.resume, same, ↓reduceIte]
    · intro next supported
      obtain ⟨pair, chosen, rfl⟩ := PMF.support_map .. ▸ supported
      right
      refine ⟨related pair chosen, ?_, rfl, ?_⟩
      · have reached : pair.2 ∈ (app.dispatch players (.activate actor) repaired).support := by
          rw [← second, PMF.support_map]
          exact ⟨pair, chosen, rfl⟩
        rw [app.dispatch_recall_length players (.activate actor) repaired pair.2 reached owner]
        omega
      have reached : pair.2 ∈ (app.dispatch players (.activate actor) repaired).support := by
        rw [← second, PMF.support_map]
        exact ⟨pair, chosen, rfl⟩
      exact runtime.foreign_activation_view leaks players repaired pair.2 actor owner same reached

/-- A whole fixed response window is coupled without restricting the focal
player's raw actions or any opponent policy. Passive samples remain joint;
audited departures retain both complete continuation marginals. -/
theorem run_off_turn_stopped_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (serials : original.network.SerialsBeforeNext)
    (offTurn : ∀ event, original.application.serviceGrant = some event →
      graph.actor? event ≠ some owner)
    (coverage : ∀ past view,
      (∀ event, view.application.publicView.serviceGrant = some event →
        graph.actor? event ≠ some owner) →
      ∀ response ∈ ((runtime.reactiveApplication leaks).replayPolicy past view).support,
        response ∈ menu.actions owner past view)
    (available : ∀ past view response, response ∈ (players owner past view).support →
      response ∈ (bounds.menu runtime leaks).actions owner past view)
    (offset count : Nat) (position : original.environmentRecall.length = offset)
    (commands : ∀ execution : (runtime.reactiveApplication leaks).Execution,
      offset ≤ execution.environmentRecall.length →
      execution.environmentRecall.length < offset + count →
      ∀ command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment (runtime.reactiveApplication leaks))).support,
        ∃ actor, command = .activate actor) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.runRounds scheduler players count original ∧
      coupling.map Prod.snd = strategy.runJoint owner players scheduler count repaired memory ∧
      ∀ next ∈ coupling.support,
        (∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow = memory.shadow ∧
          next.2.1.application.playerView owner = repaired.application.playerView owner := by
  classical
  let app := runtime.reactiveApplication leaks
  let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
  induction count generalizing original repaired memory offset with
  | zero =>
      exact ⟨PMF.pure (original, repaired, memory), PMF.pure_map .., PMF.pure_map ..,
        fun next member => by
          cases (PMF.mem_support_pure_iff _ _).mp member
          exact Or.inr ⟨frame, rfl, rfl⟩⟩
  | succ count ih =>
      let selected := scheduler original.environmentRecall (original.observeEnvironment app)
      have commandStep (command : app.Command) (chosen : command ∈ selected.support) :
          ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
            coupling.map Prod.fst = (app.dispatch players command original).bind
              (app.runRounds scheduler players count) ∧
            coupling.map Prod.snd = ((repaired.environmentStep app command).bind
              (fun execution => strategy.resume owner players (command.actor? app)
                execution memory)).bind
                  (fun next => strategy.runJoint owner players scheduler count next.1 next.2) ∧
            ∀ next ∈ coupling.support, departed runtime leaks owner next.1 ∨
              Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
                next.2.2.shadow = memory.shadow ∧
                next.2.1.application.playerView owner = repaired.application.playerView owner := by
        obtain ⟨actor, rfl⟩ := commands original (by omega) (by omega) command chosen
        obtain ⟨step, first, second, related⟩ := frame.off_turn_activation_coupling
          bounds menu players reference started leftRecall rightRecall serials offTurn
            coverage available actor
        have existsTail (next) (member : next ∈ step.support) :
            ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
              coupling.map Prod.fst = app.runRounds scheduler players count next.1 ∧
              coupling.map Prod.snd =
                strategy.runJoint owner players scheduler count next.2.1 next.2.2 ∧
              ∀ final ∈ coupling.support, departed runtime leaks owner final.1 ∨
                Frame runtime leaks final.2.2 owner final.1 final.2.1 ∧
                  final.2.2.shadow = memory.shadow ∧
                  final.2.1.application.playerView owner =
                    repaired.application.playerView owner := by
          by_cases bad : departed runtime leaks owner next.1
          · let coupling := bindPairLaw (app.runRounds scheduler players count next.1)
              (fun _ => (strategy.runJoint owner players scheduler count next.2.1 next.2.2))
            refine ⟨coupling, bindPairLaw_map_fst .., bindPairLaw_const_map_snd .., ?_⟩
            intro final supported
            left
            obtain ⟨record, present, authored, rejected⟩ := bad
            refine ⟨record, ?_, authored, rejected⟩
            have reached : final.1 ∈ (app.runRounds scheduler players count next.1).support := by
              rw [← bindPairLaw_map_fst (app.runRounds scheduler players count next.1)
                (fun _ => strategy.runJoint owner players scheduler count next.2.1 next.2.2),
                PMF.support_map]
              exact ⟨final, supported, rfl⟩
            exact (app.executionTraffic_runRounds scheduler players count next.1 final.1
              reached).subset present
          · have good := (related next member).resolve_left bad
            have reached : next.1 ∈ (app.dispatch players (.activate actor) original).support := by
              rw [← first, PMF.support_map]
              exact ⟨next, member, rfl⟩
            have privateReached : next.2 ∈ ((repaired.environmentStep app (.activate actor)).bind
                (fun execution => strategy.resume owner players (some actor) execution
                  memory)).support := by
              rw [← second, PMF.support_map]
              exact ⟨next, member, rfl⟩
            obtain ⟨valid, fresh, grant⟩ := runtime.activation_resources leaks players
              original next.1 actor leftRecall serials reached
            have nextPosition : next.1.environmentRecall.length = offset + 1 := by
              rw [app.dispatch_environmentRecall players (.activate actor) original next.1 reached,
                List.length_append, List.length_singleton, position]
            obtain ⟨coupling, leftLaw, rightLaw, connected⟩ := ih good.1 good.2.1 valid
              (runtime.private_activation_recall leaks strategy players owner actor repaired memory
                next.2 rightRecall privateReached) fresh
              (fun event granted => offTurn event (grant.symm.trans granted))
              (offset + 1) nextPosition
              (fun execution lower upper => commands execution (by omega) (by omega))
            refine ⟨coupling, leftLaw, rightLaw, ?_⟩
            intro final supported
            rcases connected final supported with bad | ⟨paired, shadow, view⟩
            · exact Or.inl bad
            · exact Or.inr ⟨paired, shadow.trans good.2.2.1,
                view.trans good.2.2.2⟩
        let tail := fun next member => (existsTail next member).choose
        refine ⟨step.bindOnSupport tail, ?_, ?_, ?_⟩
        · rw [map_bindOnSupport]
          calc
            _ = step.bind (fun next => app.runRounds scheduler players count next.1) := by
              apply bindOnSupport_eq_bind_of_eq_on_support _
              intro next member
              exact (existsTail next member).choose_spec.1
            _ = _ := by rw [← first, PMF.bind_map]; rfl
        · rw [map_bindOnSupport]
          calc
            _ = step.bind (fun next =>
                strategy.runJoint owner players scheduler count next.2.1 next.2.2) := by
              apply bindOnSupport_eq_bind_of_eq_on_support _
              intro next member
              exact (existsTail next member).choose_spec.2.1
            _ = (step.map Prod.snd).bind (fun next =>
                strategy.runJoint owner players scheduler count next.1 next.2) := by
              rw [PMF.bind_map]; rfl
            _ = _ := by rw [second]; rfl
        · intro final supported
          obtain ⟨next, member, reached⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
          exact (existsTail next member).choose_spec.2.2 final reached
      let step := fun command chosen => (commandStep command chosen).choose
      refine ⟨selected.bindOnSupport step, ?_, ?_, ?_⟩
      · rw [map_bindOnSupport]
        change _ = (app.round scheduler players original).bind _
        rw [ReactiveApplication.round, PMF.bind_bind]
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro command chosen
        exact (commandStep command chosen).choose_spec.1
      · rw [map_bindOnSupport]
        change _ = (strategy.round owner players scheduler repaired memory).bind _
        rw [ReactiveApplication.Implementation.round, PMF.bind_bind]
        have same : scheduler repaired.environmentRecall (repaired.observeEnvironment app) =
            selected := by rw [← frame.service, ← frame.environment]
        rw [same]
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro command chosen
        simpa only [step, strategy, app, PMF.bind_bind] using
          (commandStep command chosen).choose_spec.2.1
      · intro final supported
        obtain ⟨command, chosen, reached⟩ :=
          Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
        exact (commandStep command chosen).choose_spec.2.2 final reached

end BindingMemory.Frame

end Vegas.EventGraphRuntime
