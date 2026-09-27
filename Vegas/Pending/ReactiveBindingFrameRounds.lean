/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameLaw

/-! # Response windows in the actual repaired implementation

Finite activation windows use the existing scheduler and passive observation
rule. Original own responses are silence or replay in this segment; foreign
responses remain arbitrary. Complete private recall is retained on both sides.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

theorem foreign_observed (frame : Frame runtime leaks memory owner original repaired)
    (actor : Player) (different : actor ≠ owner) :
    original.observe (runtime.reactiveApplication leaks) actor =
      repaired.observe (runtime.reactiveApplication leaks) actor := by
  let app := runtime.reactiveApplication leaks
  have view := congrArg (fun view : PlayerView graph =>
    (⟨view.who, view.publicView, view.observation, view.candidates⟩ : ReactivePlayerView graph))
      (frame.views actor different)
  change (⟨original.network.observe actor, app.observePlayer original.application actor,
    original.receipts⟩ : app.PlayerView) =
      ⟨repaired.network.observe actor, app.observePlayer repaired.application actor,
        repaired.receipts⟩
  rw [frame.network, frame.receipts]
  exact congrArg (fun current => (⟨repaired.network.observe actor, current,
    repaired.receipts⟩ : app.PlayerView)) view

private theorem repairResponse_transport
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (transport : ∀ submission, response.transmission ≠ some (.submit submission)) :
    memory.repairResponse runtime leaks owner view response = (response, memory.shadow) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id => rfl
      | submit material => exact (transport material rfl).elim

/-- One real player response has a joint coupling with the private repair.
This statement concerns the response window, not later inclusion. -/
theorem resume_transport_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (transport : ∀ past view response, response ∈ (players owner past view).support →
      ∀ material, response.transmission ≠ some (.submit material))
    (actor : Option Player) :
    let app := runtime.reactiveApplication leaks
    let strategy := implementation runtime leaks owner reference (players owner)
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.resume players actor original ∧
      coupling.map Prod.snd = strategy.resume owner players actor repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length := by
  let app := runtime.reactiveApplication leaks
  let strategy := implementation runtime leaks owner reference (players owner)
  cases actor with
  | none =>
      exact ⟨FinDist.pure (original, repaired, memory), FinDist.map_pure ..,
        FinDist.map_pure .., fun next member => by
          cases FinDist.mem_support_pure.mp member
          exact ⟨frame, started⟩⟩
  | some actor =>
      by_cases own : actor = owner
      · subst actor
        let law := players owner (original.recall owner) (original.observe app owner)
        let updated (response : app.Action) := memory.record runtime leaks
          (memory.shadow.inputView runtime leaks (repaired.observe app owner)) response
        let coupling := law.map fun response =>
          (original.respond app owner response, repaired.respond app owner response,
            updated response)
        have responseLaw : strategy.respond memory (repaired.recall owner,
            repaired.observe app owner) = law.map fun response => (response, updated response) := by
          rw [implementation_respond runtime leaks owner reference (players owner) memory
            (repaired.recall owner) (repaired.observe app owner) started,
              frame.past, frame.observed]
          apply FinDist.map_congr_of_eq_on_support
          intro response member
          rw [repairResponse_transport (repaired.observe app owner) response
            (transport _ _ response member)]
          simp only [updated, record, app, frame.observed]
        refine ⟨coupling, ?_, ?_, ?_⟩
        · simp only [coupling, FinDist.map_comp]
          rfl
        · simp only [coupling, FinDist.map_comp, ReactiveApplication.Implementation.resume,
            ↓reduceIte]
          change law.map _ = (strategy.respond memory
            (repaired.recall owner, repaired.observe app owner)).map _
          rw [responseLaw, FinDist.map_comp]
          rfl
        · intro next member
          obtain ⟨response, supported, rfl⟩ := FinDist.support_map .. ▸ member
          refine ⟨frame.transport_response response (transport _ _ response supported), ?_⟩
          rw [app.respond_recall_length]
          omega
      · let law := players actor (original.recall actor) (original.observe app actor)
        let coupling := law.map fun response =>
          (original.respond app actor response, repaired.respond app actor response, memory)
        have lawEq : players actor (repaired.recall actor) (repaired.observe app actor) = law := by
          rw [← frame.recall actor own, ← frame.foreign_observed actor own]
        refine ⟨coupling, ?_, ?_, ?_⟩
        · simp only [coupling, FinDist.map_comp]
          rfl
        · simp only [coupling, FinDist.map_comp, ReactiveApplication.Implementation.resume,
            own, ↓reduceIte, ReactiveApplication.invoke, FinDist.map_comp]
          change law.map _ =
            (players actor (repaired.recall actor) (repaired.observe app actor)).map _
          rw [lawEq]
          rfl
        · intro next member
          obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ member
          refine ⟨frame.foreign_response actor own response, ?_⟩
          rw [app.respond_recall_other repaired actor owner (Ne.symm own) response]
          exact started

/-- One real activation (including the original partial leak sample) or wait
couples the two executions without suppressing pending observations. -/
theorem dispatch_transport_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (transport : ∀ past view response, response ∈ (players owner past view).support →
      ∀ material, response.transmission ≠ some (.submit material))
    (command : (runtime.reactiveApplication leaks).Command)
    (allowed : command = .wait ∨ ∃ actor, command = .activate actor) :
    let app := runtime.reactiveApplication leaks
    let strategy := implementation runtime leaks owner reference (players owner)
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.dispatch players command original ∧
      coupling.map Prod.snd = (repaired.environmentStep app command).bind
        (fun next => strategy.resume owner players (command.actor? app) next memory) ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length := by
  classical
  let app := runtime.reactiveApplication leaks
  rcases allowed with rfl | ⟨actor, rfl⟩
  · let waited (execution : app.Execution) : app.Execution :=
      { execution with environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .wait⟩] }
    have paired : Frame runtime leaks memory owner (waited original) (waited repaired) :=
      { frame with
        service := by
          change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
          rw [frame.service, frame.environment] }
    refine ⟨FinDist.pure (waited original, waited repaired, memory), ?_, ?_, ?_⟩
    · simp only [FinDist.map_pure, ReactiveApplication.dispatch,
        ReactiveApplication.Execution.environmentStep, FinDist.map_pure, FinDist.pure_bind,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume]
      rfl
    · simp only [FinDist.map_pure, ReactiveApplication.Execution.environmentStep,
        FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
        ReactiveApplication.Implementation.resume]
      rfl
    · intro next member
      cases FinDist.mem_support_pure.mp member
      exact ⟨paired, started⟩
  · let activated (execution : app.Execution) (selected : Finset (MessageId Player)) :
        app.Execution :=
      { execution with
        network := execution.network.learn actor selected
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .activate actor⟩] }
    let sample := leaks actor original.network.pending
    have existsStep (selected : Finset (MessageId Player)) :=
      (frame.activate actor selected).resume_transport_coupling players reference started
        transport (some actor)
    let step := fun selected => (existsStep selected).choose
    have left (selected : Finset (MessageId Player)) :
        (step selected).map Prod.fst = app.resume players (some actor)
          (activated original selected) := (existsStep selected).choose_spec.1
    have right (selected : Finset (MessageId Player)) :
        (step selected).map Prod.snd =
          (implementation runtime leaks owner reference (players owner)).resume owner players
            (some actor) (activated repaired selected) memory :=
      (existsStep selected).choose_spec.2.1
    refine ⟨sample.bind step, ?_, ?_, ?_⟩
    · rw [FinDist.map_bind]
      simp only [left]
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        FinDist.map_comp, FinDist.bind_map, ReactiveApplication.Command.actor?]
      rfl
    · rw [FinDist.map_bind]
      simp only [right]
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_comp,
        FinDist.bind_map, ReactiveApplication.Command.actor?]
      change sample.bind _ = (leaks actor repaired.network.pending).bind _
      rw [show leaks actor repaired.network.pending = sample from
        congrArg (fun network => leaks actor network.pending) frame.network.symm]
      rfl
    · intro next member
      obtain ⟨selected, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ member)
      exact (existsStep selected).choose_spec.2.2 next reached

/-- A scheduler that selects activations and waits may use its complete
existing public view and recall. The repair does not alter its input law. -/
theorem round_transport_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (transport : ∀ past view response, response ∈ (players owner past view).support →
      ∀ material, response.transmission ≠ some (.submit material))
    (commands : ∀ past view command, command ∈ (scheduler past view).support →
      command = .wait ∨ ∃ actor, command = .activate actor) :
    let app := runtime.reactiveApplication leaks
    let strategy := implementation runtime leaks owner reference (players owner)
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.round scheduler players original ∧
      coupling.map Prod.snd = strategy.round owner players scheduler repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length := by
  classical
  let app := runtime.reactiveApplication leaks
  let law := scheduler original.environmentRecall (original.observeEnvironment app)
  have existsStep (command) (member : command ∈ law.support) :=
    frame.dispatch_transport_coupling players reference started transport command
      (commands _ _ command member)
  let step := fun command member => (existsStep command member).choose
  refine ⟨law.bindOnSupport step, ?_, ?_, ?_⟩
  · rw [FinDist.map_bindOnSupport]
    apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
    intro command member
    exact (existsStep command member).choose_spec.1
  · rw [FinDist.map_bindOnSupport]
    have same : scheduler repaired.environmentRecall (repaired.observeEnvironment app) = law := by
      rw [← frame.service, ← frame.environment]
    change _ = (scheduler repaired.environmentRecall (repaired.observeEnvironment app)).bind _
    rw [same]
    apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
    intro command member
    exact (existsStep command member).choose_spec.2.1
  · intro next member
    obtain ⟨command, chosen, reached⟩ :=
      Set.mem_iUnion₂.mp (FinDist.support_bindOnSupport .. ▸ member)
    exact (existsStep command chosen).choose_spec.2.2 next reached

/-- The complete finite response window is coupled in the existing round
evaluator and private implementation evaluator. All actual network data and
private action recalls are retained; no new interpreter or observation quotient
is used. The own transport premise is local to this window. -/
theorem run_transport_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (transport : ∀ past view response, response ∈ (players owner past view).support →
      ∀ material, response.transmission ≠ some (.submit material))
    (commands : ∀ past view command, command ∈ (scheduler past view).support →
      command = .wait ∨ ∃ actor, command = .activate actor)
    (count : Nat) :
    let app := runtime.reactiveApplication leaks
    let strategy := implementation runtime leaks owner reference (players owner)
    ∃ coupling : FinDist (app.Execution × app.Execution),
      coupling.map Prod.fst = app.runRounds scheduler players count original ∧
      coupling.map Prod.snd = strategy.run owner players scheduler count repaired memory ∧
      ∀ next ∈ coupling.support, ∃ afterMemory,
        Frame runtime leaks afterMemory owner next.1 next.2 := by
  classical
  let app := runtime.reactiveApplication leaks
  let strategy := implementation runtime leaks owner reference (players owner)
  induction count generalizing original repaired memory with
  | zero =>
      exact ⟨FinDist.pure (original, repaired), FinDist.map_pure .., FinDist.map_pure ..,
        fun next member => by cases FinDist.mem_support_pure.mp member; exact ⟨memory, frame⟩⟩
  | succ count ih =>
      obtain ⟨step, first, second, related⟩ := frame.round_transport_coupling
        players scheduler reference started transport commands
      have existsTail (next) (member : next ∈ step.support) :=
        ih (related next member).1 (related next member).2
      let tail := fun next member => (existsTail next member).choose
      refine ⟨step.bindOnSupport tail, ?_, ?_, ?_⟩
      · rw [FinDist.map_bindOnSupport]
        calc
          _ = step.bind (fun next => app.runRounds scheduler players count next.1) := by
            apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
            intro next member
            exact (existsTail next member).choose_spec.1
          _ = (step.map Prod.fst).bind (app.runRounds scheduler players count) :=
            (FinDist.bind_map ..).symm
          _ = _ := by rw [first]; rfl
      · rw [FinDist.map_bindOnSupport]
        calc
          _ = step.bind (fun next => strategy.run owner players scheduler
              count next.2.1 next.2.2) := by
            apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
            intro next member
            exact (existsTail next member).choose_spec.2.1
          _ = (step.map Prod.snd).bind (fun next =>
              strategy.run owner players scheduler count next.1 next.2) := by
            rw [FinDist.bind_map]
          _ = _ := by rw [second]; rfl
      · intro final member
        obtain ⟨next, chosen, reached⟩ :=
          Set.mem_iUnion₂.mp (FinDist.support_bindOnSupport .. ▸ member)
        exact (existsTail next chosen).choose_spec.2.2 final reached

end Vegas.EventGraphRuntime.BindingMemory.Frame
