/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceUnclassifiedPending
import Vegas.Game.SourceServiceUnclassifiedPendingCommands
import Vegas.Game.SourceServicePendingPacketOrigin
import Vegas.Pending.ReactiveBindingPendingInclusion
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveImplementationCoupling

/-! # Actual pending repair transitions and their settlement boundary

The pending phase keeps the real recorded response and its silent later recall.
Actual packet provenance determines which identifier can settle its event.
Every other identifier is rejected on both executions. Completion restores the
ordinary completed-memory invariant; a focal classified draw is a real exit.
Neither branch asserts a common continuation after that boundary.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Every actual scheduler command retains the pending frame. The real anchor
envelope is reconstructed from authenticated recall and allocated identifiers,
not supplied as a sole-packet condition. Inclusion may accept or reject it. -/
theorem sourceService_pending_environment_coupling
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, original⟩))
    (onlyBindings : memory.shadow.OwnBindings who)
    (pending : (graph setup).EventId)
    (past : memory.shadow.CompletedExcept original.application.config pending)
    (payload : L.Ty)
    (outputEq : (graph setup).outputLayout pending = .binding who payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes pending) = .bind who payload)
    (node : nodeView (graph setup) pending = .bind who payload outputEq codeEq)
    (ready : original.application.config.cut.Ready pending)
    (id : MessageId Player) (candidate : Handle (graph setup))
    (leftFixed : original.application.candidates.lookup candidate ≠ .fresh)
    (rightFixed : repaired.application.candidates.lookup candidate ≠ .fresh)
    (failed : original.application.bindingResult candidate payload = .failure)
    (rememberedAction : memory.shadow.actions pending = some
      (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure))
    (rememberedValue : memory.shadow.values (.inr pending) = some
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure))
    (anchor : (application setup leaks).PlayerEntry)
    (earlier later : List (application setup leaks).PlayerEntry)
    (split : original.recall who = earlier ++ anchor :: later)
    (unrecorded : (runtime setup).eventRecorded leaks earlier pending = false)
    (silent : ∀ entry ∈ later, entry.action.transmission = none)
    (emitted : anchor.emitted = some ⟨id, ⟨.commitment pending candidate, none, some ⟨pending⟩⟩⟩)
    (command : (application setup leaks).Command) :
    let app := application setup leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = original.environmentStep app command ∧
      coupling.map Prod.snd = repaired.environmentStep app command ∧
      ∀ pair ∈ coupling.support,
        memory.Frame (runtime setup) leaks who pair.1 pair.2 ∧
          memory.shadow.CompletedExcept pair.1.application.config pending ∧
          (pending ∈ pair.1.application.config.cut.completed →
            memory.shadow.CompletedAt pair.1.application.config) := by
  classical
  let app := application setup leaks
  have existsFrame : ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = original.environmentStep app command ∧
      coupling.map Prod.snd = repaired.environmentStep app command ∧
      ∀ pair ∈ coupling.support, memory.Frame (runtime setup) leaks who pair.1 pair.2 := by
    cases command with
    | wait =>
        let record (execution : app.Execution) : app.Execution :=
          { execution with environmentRecall := execution.environmentRecall ++
            [⟨execution.observeEnvironment app, .wait⟩] }
        refine ⟨PMF.pure (record original, record repaired), ?_, ?_, ?_⟩
        · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]; rfl
        · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]; rfl
        intro pair supported
        cases (PMF.mem_support_pure_iff _ _).mp supported
        exact { frame with
          service := by
            change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
            rw [frame.service, frame.environment] }
    | activate actor =>
        let law := app.observePending actor original.network.pending
        let updated (execution : app.Execution) (selected : Finset (MessageId Player)) :
            app.Execution :=
          { execution with
            network := execution.network.learn actor selected
            environmentRecall := execution.environmentRecall ++
              [⟨execution.observeEnvironment app, .activate actor⟩] }
        refine ⟨law.map (fun selected => (updated original selected, updated repaired selected)),
          ?_, ?_, ?_⟩
        · simp only [law, updated, ReactiveApplication.Execution.environmentStep, PMF.map_comp,
            Function.comp_def]
        · simp only [law, updated, ReactiveApplication.Execution.environmentStep, PMF.map_comp,
            Function.comp_def]
          rw [← frame.network]
        · intro pair supported
          obtain ⟨selected, _chosen, rfl⟩ := PMF.support_map .. ▸ supported
          exact frame.activate actor selected
    | application actual =>
        obtain ⟨coupling, first, second, related⟩ := sourceService_pending_application_coupling
          original repaired who memory frame onlyBindings pending past payload outputEq codeEq
            node ready rememberedAction rememberedValue actual
        exact ⟨coupling, first, second, fun pair member => (related pair member).1⟩
    | «include» selected =>
        let included (execution : app.Execution) : app.Execution :=
          { execution.includePending app selected with
            environmentRecall := execution.environmentRecall ++
              [⟨execution.observeEnvironment app, .include selected⟩] }
        cases found : original.network.lookup selected with
        | none =>
            have rightFound : repaired.network.lookup selected = none := by
              rw [← frame.network, found]
            refine ⟨PMF.pure (included original, included repaired), ?_, ?_, ?_⟩
            · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]; rfl
            · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]; rfl
            intro pair supported
            cases (PMF.mem_support_pure_iff _ _).mp supported
            have leftSame : original.includePending app selected = original := by
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found]
              rfl
            have rightSame : repaired.includePending app selected = repaired := by
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, rightFound]
              rfl
            change memory.Frame (runtime setup) leaks who (included original) (included repaired)
            simp only [included, leftSame, rightSame]
            exact { frame with
              service := by
                change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
                rw [frame.service, frame.environment] }
        | some message =>
            have allocated : message.id = selected := by
              simpa only [decide_eq_true_eq] using List.find?_some found
            have located : original.network.lookup selected = some ⟨selected, message.payload⟩ :=
              by
              cases message with
              | mk actual packet =>
                  change actual = selected at allocated
                  cases allocated
                  exact found
            by_cases same : selected = id
            · have facts := legalFacts setup leaks horizon scheduler _ trace
              let anchorMessage : Message Player (WitnessedPacket (graph setup)) :=
                ⟨id, ⟨.commitment pending candidate, none, some ⟨pending⟩⟩⟩
              have anchorMember : anchor ∈ original.recall who := by
                rw [split]
                exact List.mem_append_right _ List.mem_cons_self
              have outputMember : anchorMessage ∈ app.outputs (original.recall who) :=
                List.mem_filterMap.mpr ⟨anchor, anchorMember, emitted⟩
              have inputMember : anchorMessage ∈ original.network.inputs := by
                have filtered : anchorMessage ∈ original.network.inputs.filter
                    (fun message => message.sender = who) := by
                  rw [facts.inputs who]
                  exact outputMember
                exact (List.mem_filter.mp filtered).1
              have exactMessage : message = anchorMessage :=
                (facts.unique.inputs anchorMessage inputMember).lookup selected message found
                  (allocated.trans same)
              have exactFound : original.network.lookup id = some anchorMessage := by
                rw [← same, ← exactMessage]
                exact found
              obtain ⟨coupling, first, second, related⟩ :=
                frame.pending_failed_binding_include_coupling pending past payload outputEq codeEq
                  node id candidate exactFound leftFixed rightFixed failed rememberedAction
                    rememberedValue
              exact ⟨coupling, by simpa only [same] using first,
                by simpa only [same] using second, fun pair member => (related pair member).1⟩
            · have owned : (graph setup).actor? pending = some who := by
                exact binding_actor setup pending who payload outputEq
              refine ⟨PMF.pure (included original, included repaired), ?_, ?_, ?_⟩
              · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]; rfl
              · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]; rfl
              intro pair supported
              cases (PMF.mem_support_pure_iff _ _).mp supported
              exact sourceService_pending_other_packet_frame original repaired who memory frame
                trace pending ready owned anchor earlier later split unrecorded silent _ emitted
                  selected message.payload located same
  obtain ⟨coupling, first, second, related⟩ := existsFrame
  refine ⟨coupling, first, second, ?_⟩
  intro pair member
  have supported : pair.1 ∈ (original.environmentStep app command).support := by
    rw [← first, PMF.support_map]
    exact ⟨pair, member, rfl⟩
  have retained := ((runtime setup).reactiveCompletedInvariant leaks
    original.application.config.cut.completed).environmentStep original pair.1 command
      (Finset.Subset.refl _) supported
  have after := past.mono retained
  exact ⟨related pair member, after, after.completedAt⟩

private theorem resume_candidate_fixed
    (players : Player → (application setup leaks).Policy) (actor : Option Player)
    (original next : (application setup leaks).Execution) (candidate : Handle (graph setup))
    (fixed : original.application.candidates.lookup candidate ≠ .fresh)
    (reached : next ∈ ((application setup leaks).resume players actor original).support) :
    next.application.candidates.lookup candidate = original.application.candidates.lookup
      candidate := by
  cases actor with
  | none => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | some actor =>
      obtain ⟨response, _chosen, rfl⟩ := PMF.support_map .. ▸ reached
      exact (runtime setup).reactive_respond_candidate_fixed leaks original actor response
        candidate fixed

private theorem implementation_resume_resources
    (strategy : (application setup leaks).Implementation (BindingMemory (runtime setup) leaks))
    (players : Player → (application setup leaks).Policy) (who : Player) (actor : Option Player)
    (original : (application setup leaks).Execution) (memory : BindingMemory (runtime setup) leaks)
    (next : (application setup leaks).Execution × BindingMemory (runtime setup) leaks)
    (candidate : Handle (graph setup))
    (fixed : original.application.candidates.lookup candidate ≠ .fresh)
    (reached : next ∈ (strategy.resume who players actor original memory).support) :
    next.1.application.candidates.lookup candidate = original.application.candidates.lookup
      candidate ∧ (original.recall who).length ≤ (next.1.recall who).length := by
  cases actor with
  | none => cases (PMF.mem_support_pure_iff _ _).mp reached; exact ⟨rfl, Nat.le_refl _⟩
  | some actor =>
      by_cases own : actor = who
      · subst actor
        simp only [ReactiveApplication.Implementation.resume, ↓reduceIte] at reached
        obtain ⟨response, _chosen, rfl⟩ := PMF.support_map .. ▸ reached
        exact ⟨(runtime setup).reactive_respond_candidate_fixed leaks original who response.1
          candidate fixed, by
              rw [(application setup leaks).respond_recall_length]
              exact Nat.le_add_right _ _⟩
      · simp only [ReactiveApplication.Implementation.resume, own, ↓reduceIte] at reached
        obtain ⟨updated, moved, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨response, _chosen, rfl⟩ := PMF.support_map .. ▸ moved
        exact ⟨(runtime setup).reactive_respond_candidate_fixed leaks original actor response
          candidate fixed, by
              rw [(application setup leaks).respond_recall_length]
              exact Nat.le_add_right _ _⟩

private def pendingPhase
    (who : Player) (pending : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout pending = .binding who payload)
    (candidate : Handle (graph setup)) (anchor : (application setup leaks).PlayerEntry)
    (earlier reference : List (application setup leaks).PlayerEntry)
    (next : (application setup leaks).Execution × (application setup leaks).Execution ×
      BindingMemory (runtime setup) leaks) : Prop :=
  next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
    next.2.2.shadow.OwnBindings who ∧
    next.2.2.shadow.CompletedExcept next.1.application.config pending ∧
    next.1.application.config.cut.Ready pending ∧
    next.1.application.candidates.lookup candidate ≠ .fresh ∧
    next.2.1.application.candidates.lookup candidate ≠ .fresh ∧
    next.1.application.bindingResult candidate payload = .failure ∧
    next.2.2.shadow.actions pending = some
      (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure) ∧
    next.2.2.shadow.values (.inr pending) = some
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure) ∧
    reference.length ≤ (next.2.1.recall who).length ∧
    ∃ later, next.1.recall who = earlier ++ anchor :: later ∧
      ∀ entry ∈ later, entry.action.transmission = none

private def pendingExit
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (pending : (graph setup).EventId)
    (next : (application setup leaks).Execution × (application setup leaks).Execution ×
      BindingMemory (runtime setup) leaks) : Prop :=
  (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
    next.2.2.shadow.OwnBindings who ∧ next.2.2.shadow.CompletedAt next.1.application.config ∧
      pending ∈ next.1.application.config.cut.completed) ∨
    ∃ remaining original response,
      Nonempty (((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, some who, original⟩)) ∧
      response ∈ (players who (original.recall who)
        (original.observe (application setup leaks) who)).support ∧
      next.1 = original.respond (application setup leaks) who response ∧
      (auditableServiceResponse setup leaks who (original.recall who)
        (original.observe (application setup leaks) who) response ∨
          recordedServiceResponse setup leaks (original.recall who) response)

variable [Fintype Player]

private theorem pending_dispatch_coupling
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (who : Player) (pending : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout pending = .binding who payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes pending) = .bind who payload)
    (node : nodeView (graph setup) pending = .bind who payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle (graph setup))
    (anchor : (application setup leaks).PlayerEntry)
    (earlier reference : List (application setup leaks).PlayerEntry)
    (named : (runtime setup).submittedEvent? leaks anchor.action = some pending)
    (unrecorded : (runtime setup).eventRecorded leaks earlier pending = false)
    (emitted : anchor.emitted = some ⟨id, ⟨.commitment pending candidate, none, some ⟨pending⟩⟩⟩)
    (players : Player → (application setup leaks).Policy)
    (original repaired : (application setup leaks).Execution)
    (memory : BindingMemory (runtime setup) leaks)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, original⟩))
    (phase : pendingPhase who pending payload outputEq candidate anchor earlier reference
      (original, repaired, memory))
    (command : (application setup leaks).Command)
    (selected : command ∈ (scheduler original.environmentRecall
      (original.observeEnvironment (application setup leaks))).support) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.dispatch players command original ∧
      coupling.map Prod.snd = (repaired.environmentStep app command).bind
        (fun next => strategy.resume who players (command.actor? app) next memory) ∧
      ∀ next ∈ coupling.support,
        pendingPhase who pending payload outputEq candidate anchor earlier reference next ∨
          pendingExit horizon scheduler players who pending next := by
  classical
  let app := application setup leaks
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
    (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)
  obtain ⟨frame, onlyBindings, past, ready, leftFixed, rightFixed, failed,
    rememberedAction, rememberedValue, started, later, split, silent⟩ := phase
  obtain ⟨environment, left, right, related⟩ := sourceService_pending_environment_coupling
    original repaired who memory frame trace onlyBindings pending past payload outputEq codeEq
      node ready id candidate leftFixed rightFixed failed rememberedAction rememberedValue
        anchor earlier later split unrecorded silent emitted command
  have leftSupport (pair) (member : pair ∈ environment.support) :
      pair.1 ∈ (original.environmentStep app command).support := by
    rw [← left, PMF.support_map]
    exact ⟨pair, member, rfl⟩
  have rightSupport (pair) (member : pair ∈ environment.support) :
      pair.2 ∈ (repaired.environmentStep app command).support := by
    rw [← right, PMF.support_map]
    exact ⟨pair, member, rfl⟩
  have existsResume (pair) (member : pair ∈ environment.support) :
      ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = app.resume players (command.actor? app) pair.1 ∧
        coupling.map Prod.snd = strategy.resume who players (command.actor? app) pair.2 memory ∧
        ∀ next ∈ coupling.support,
          pendingPhase who pending payload outputEq candidate anchor earlier reference next ∨
            pendingExit horizon scheduler players who pending next := by
    obtain ⟨currentFrame, currentPast, completeMemory⟩ := related pair member
    by_cases completed : pending ∈ pair.1.application.config.cut.completed
    · have inactive : command.actor? app = none := by
        cases command with
        | activate actor =>
            obtain ⟨updated, moved, actual⟩ := PMF.support_map .. ▸ leftSupport pair member
            obtain ⟨sample, _chosen, actualUpdated⟩ := PMF.support_map .. ▸ moved
            have sameConfig : pair.1.application.config = original.application.config := by
              rw [← actual, ← actualUpdated]
            exact False.elim (ready.1 (sameConfig ▸ completed))
        | wait | application | «include» => rfl
      refine ⟨PMF.pure (pair.1, pair.2, memory), ?_, ?_, ?_⟩
      · simp only [PMF.pure_map, inactive, ReactiveApplication.resume]
      · simp only [PMF.pure_map, inactive, ReactiveApplication.Implementation.resume]
      · intro next chosen
        cases (PMF.mem_support_pure_iff _ _).mp chosen
        exact Or.inr (Or.inl ⟨currentFrame, onlyBindings, completeMemory completed, completed⟩)
    · have retained := ((runtime setup).reactiveCompletedInvariant leaks
        original.application.config.cut.completed).environmentStep original pair.1 command
          (Finset.Subset.refl _) (leftSupport pair member)
      have currentReady : pair.1.application.config.cut.Ready pending :=
        ⟨completed, ready.2.trans retained⟩
      have currentSplit : pair.1.recall who = earlier ++ anchor :: later := by
        rw [app.environmentStep_recall original pair.1 command (leftSupport pair member)]
        exact split
      have currentStarted : reference.length ≤ (pair.2.recall who).length := by
        rw [app.environmentStep_recall repaired pair.2 command (rightSupport pair member)]
        exact started
      obtain ⟨currentTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
        remaining original pair.1 command trace selected (leftSupport pair member)
      obtain ⟨resume, first, second, supported⟩ :=
        sourceServiceRecorded_ready_resume_coupling bounds bound pair.1 pair.2 who memory
          currentFrame (command.actor? app) currentTrace pending currentReady anchor earlier later
            currentSplit named silent players reference currentStarted
      refine ⟨resume, first, second, ?_⟩
      intro next chosen
      rcases supported next chosen with charged | good
      · obtain ⟨actor, response, picked, actual, classified⟩ := charged
        right
        right
        refine ⟨remaining, pair.1, response, ?_, picked, actual, classified⟩
        exact ⟨by simpa only [actor] using currentTrace⟩
      · obtain ⟨unchanged, afterFrame, configEq, laterNext, afterSplit, afterSilent⟩ := good
        have leftResumed : next.1 ∈ (app.resume players (command.actor? app) pair.1).support := by
          rw [← first, PMF.support_map]
          exact ⟨next, chosen, rfl⟩
        have rightResumed : next.2 ∈
            (strategy.resume who players (command.actor? app) pair.2 memory).support := by
          rw [← second, PMF.support_map]
          exact ⟨next, chosen, rfl⟩
        have leftLookup := (runtime setup).reactive_environment_candidate_fixed leaks original
          pair.1 command candidate leftFixed (leftSupport pair member)
        have rightLookup := (runtime setup).reactive_environment_candidate_fixed leaks repaired
          pair.2 command candidate rightFixed (rightSupport pair member)
        have afterLeftLookup := resume_candidate_fixed players (command.actor? app) pair.1 next.1
          candidate (by rwa [leftLookup]) leftResumed
        have afterRight := implementation_resume_resources strategy players who (command.actor? app)
          pair.2 memory next.2 candidate (by rwa [rightLookup]) rightResumed
        have fullLeftLookup := afterLeftLookup.trans leftLookup
        have fullRightLookup := afterRight.1.trans rightLookup
        left
        refine ⟨afterFrame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, laterNext, afterSplit,
          afterSilent⟩
        · rw [unchanged]; exact onlyBindings
        · rw [unchanged, configEq]; exact currentPast
        · rwa [configEq]
        · rwa [fullLeftLookup]
        · rwa [fullRightLookup]
        · unfold EventGraphRuntime.State.bindingResult
          rw [fullLeftLookup]
          exact failed
        · rw [unchanged]; exact rememberedAction
        · rw [unchanged]; exact rememberedValue
        · exact currentStarted.trans afterRight.2
  let resume := fun pair member => (existsResume pair member).choose
  refine ⟨environment.bindOnSupport resume, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    calc
      _ = environment.bind (fun pair => app.resume players (command.actor? app) pair.1) := by
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro pair member
        exact (existsResume pair member).choose_spec.1
      _ = (environment.map Prod.fst).bind (app.resume players (command.actor? app)) :=
        by rw [PMF.bind_map]; rfl
      _ = _ := by rw [left]; rfl
  · rw [map_bindOnSupport]
    calc
      _ = environment.bind (fun pair => strategy.resume who players (command.actor? app)
          pair.2 memory) := by
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro pair member
        exact (existsResume pair member).choose_spec.2.1
      _ = (environment.map Prod.snd).bind (fun next => strategy.resume who players
          (command.actor? app) next memory) := by rw [PMF.bind_map]; rfl
      _ = _ := by rw [right]
  · intro next supported
    obtain ⟨pair, moved, resumed⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
    exact (existsResume pair moved).choose_spec.2.2 next resumed

private theorem pending_round_coupling
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (who : Player) (pending : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout pending = .binding who payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes pending) = .bind who payload)
    (node : nodeView (graph setup) pending = .bind who payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle (graph setup))
    (anchor : (application setup leaks).PlayerEntry)
    (earlier reference : List (application setup leaks).PlayerEntry)
    (named : (runtime setup).submittedEvent? leaks anchor.action = some pending)
    (unrecorded : (runtime setup).eventRecorded leaks earlier pending = false)
    (emitted : anchor.emitted = some ⟨id, ⟨.commitment pending candidate, none, some ⟨pending⟩⟩⟩)
    (players : Player → (application setup leaks).Policy)
    (original repaired : (application setup leaks).Execution)
    (memory : BindingMemory (runtime setup) leaks)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining + 1, none, original⟩))
    (phase : pendingPhase who pending payload outputEq candidate anchor earlier reference
      (original, repaired, memory)) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.round scheduler players original ∧
      coupling.map Prod.snd = strategy.round who players scheduler repaired memory ∧
      ∀ next ∈ coupling.support,
        pendingPhase who pending payload outputEq candidate anchor earlier reference next ∨
          pendingExit horizon scheduler players who pending next := by
  classical
  let app := application setup leaks
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
    (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)
  let law := scheduler original.environmentRecall (original.observeEnvironment app)
  have existsDispatch command (selected : command ∈ law.support) :=
    pending_dispatch_coupling bounds bound who pending payload outputEq codeEq node id candidate
      anchor earlier reference named unrecorded emitted players original repaired memory trace
        phase command selected
  let dispatch := fun command selected => (existsDispatch command selected).choose
  refine ⟨law.bindOnSupport dispatch, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro command selected
    exact (existsDispatch command selected).choose_spec.1
  · rw [map_bindOnSupport]
    have same : scheduler repaired.environmentRecall (repaired.observeEnvironment app) = law := by
      rw [← phase.1.service, ← phase.1.environment]
    change _ = (scheduler repaired.environmentRecall (repaired.observeEnvironment app)).bind _
    rw [same]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro command selected
    exact (existsDispatch command selected).choose_spec.2.1
  · intro next supported
    obtain ⟨command, selected, dispatched⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
    exact (existsDispatch command selected).choose_spec.2.2 next dispatched

/-- The actual pending segment ends at settlement or an actual classified
owner draw. Independent actual tails then retain both complete evaluator
marginals and the checkpoint witnesses. Until that boundary the full frame
and the one pending exception remain valid. The count is bounded by the real
RAW control budget; no promise about future original policy support is used. -/
theorem sourceService_pending_stopped_coupling
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, original⟩))
    (onlyBindings : memory.shadow.OwnBindings who)
    (pending : (graph setup).EventId)
    (past : memory.shadow.CompletedExcept original.application.config pending)
    (payload : L.Ty)
    (outputEq : (graph setup).outputLayout pending = .binding who payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes pending) = .bind who payload)
    (node : nodeView (graph setup) pending = .bind who payload outputEq codeEq)
    (ready : original.application.config.cut.Ready pending)
    (id : MessageId Player) (candidate : Handle (graph setup))
    (leftFixed : original.application.candidates.lookup candidate ≠ .fresh)
    (rightFixed : repaired.application.candidates.lookup candidate ≠ .fresh)
    (failed : original.application.bindingResult candidate payload = .failure)
    (rememberedAction : memory.shadow.actions pending = some
      (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure))
    (rememberedValue : memory.shadow.values (.inr pending) = some
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure))
    (anchor : (application setup leaks).PlayerEntry)
    (earlier later : List (application setup leaks).PlayerEntry)
    (split : original.recall who = earlier ++ anchor :: later)
    (named : (runtime setup).submittedEvent? leaks anchor.action = some pending)
    (unrecorded : (runtime setup).eventRecorded leaks earlier pending = false)
    (silent : ∀ entry ∈ later, entry.action.transmission = none)
    (emitted : anchor.emitted = some ⟨id, ⟨.commitment pending candidate, none, some ⟨pending⟩⟩⟩)
    (players : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall who).length)
    (count : Nat) (bounded : count ≤ remaining) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)
    let boundary := fun next : app.Execution × app.Execution ×
        BindingMemory (runtime setup) leaks =>
      (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
        next.2.2.shadow.OwnBindings who ∧ next.2.2.shadow.CompletedAt next.1.application.config ∧
          pending ∈ next.1.application.config.cut.completed) ∨
        ∃ budget before response,
          Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
            (some ⟨budget, some who, before⟩)) ∧
          response ∈ (players who (before.recall who) (before.observe app who)).support ∧
          next.1 = before.respond app who response ∧
          (auditableServiceResponse setup leaks who (before.recall who)
            (before.observe app who) response ∨
              recordedServiceResponse setup leaks (before.recall who) response)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.runRounds scheduler players count original ∧
      coupling.map Prod.snd = strategy.runJoint who players scheduler count repaired memory ∧
      ∀ next ∈ coupling.support,
        (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings who ∧
          next.2.2.shadow.CompletedExcept next.1.application.config pending ∧
          next.1.application.config.cut.Ready pending ∧
          ∃ laterNext, next.1.recall who = earlier ++ anchor :: laterNext ∧
            ∀ entry ∈ laterNext, entry.action.transmission = none) ∨
        ∃ stopped ≤ count,
          ∃ checkpoint : app.Execution × app.Execution × BindingMemory (runtime setup) leaks,
            checkpoint.1 ∈ (app.runRounds scheduler players stopped original).support ∧
            checkpoint.2 ∈
              (strategy.runJoint who players scheduler stopped repaired memory).support ∧
            boundary checkpoint ∧
            next.1 ∈ (app.runRounds scheduler players (count - stopped) checkpoint.1).support ∧
            next.2 ∈ (strategy.runJoint who players scheduler (count - stopped)
              checkpoint.2.1 checkpoint.2.2).support := by
  classical
  let app := application setup leaks
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
    (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)
  let good := pendingPhase who pending payload outputEq candidate anchor earlier reference
  let exited := pendingExit horizon scheduler players who pending
  let closed (index : Nat) (next : app.Execution × app.Execution × BindingMemory
      (runtime setup) leaks) :=
    ∃ stopped ≤ index,
      ∃ checkpoint : app.Execution × app.Execution × BindingMemory (runtime setup) leaks,
        checkpoint.1 ∈ (app.runRounds scheduler players stopped original).support ∧
        checkpoint.2 ∈ (strategy.runJoint who players scheduler stopped repaired memory).support ∧
        exited checkpoint ∧
        next.1 ∈ (app.runRounds scheduler players (index - stopped) checkpoint.1).support ∧
        next.2 ∈ (strategy.runJoint who players scheduler (index - stopped)
          checkpoint.2.1 checkpoint.2.2).support
  have seed : good (original, repaired, memory) ∨ closed 0 (original, repaired, memory) :=
    Or.inl ⟨frame, onlyBindings, past, ready, leftFixed, rightFixed, failed,
      rememberedAction, rememberedValue, started, later, split, silent⟩
  obtain ⟨coupling, left, right, related⟩ := strategy.runJoint_coupling who players scheduler
    original repaired memory (fun index next => good next ∨ closed index next) seed count (by
      intro index within next leftReached _rightReached relation
      rcases relation with phase | ended
      · have budget : index + 1 ≤ remaining := (Nat.succ_le_iff.mpr within).trans bounded
        have startTrace : (app.protocol (initialLaw setup) horizon scheduler).Trace
            (some ⟨remaining - index + index, none, original⟩) := by
          simpa only [Nat.sub_add_cancel (by omega : index ≤ remaining)] using trace
        obtain ⟨currentTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler
          players (remaining - index) index original next.1 startTrace leftReached
        have roundTrace : (app.protocol (initialLaw setup) horizon scheduler).Trace
            (some ⟨remaining - (index + 1) + 1, none, next.1⟩) := by
          simpa only [show remaining - (index + 1) + 1 = remaining - index by omega]
            using currentTrace
        obtain ⟨step, first, second, supported⟩ := pending_round_coupling bounds bound who pending
          payload outputEq codeEq node id candidate anchor earlier reference named unrecorded
            emitted players next.1 next.2.1 next.2.2 roundTrace phase
        refine ⟨step, first, second, ?_⟩
        intro after member
        rcases supported after member with ongoing | boundary
        · exact Or.inl ongoing
        · right
          refine ⟨index + 1, Nat.le_refl _, after, ?_, ?_, boundary, ?_, ?_⟩
          · rw [app.runRounds_add scheduler players index 1 original, PMF.support_bind]
            refine Set.mem_iUnion₂.mpr ⟨next.1, leftReached, ?_⟩
            simp only [ReactiveApplication.runRounds, PMF.bind_pure]
            rw [← first, PMF.support_map]
            exact ⟨after, member, rfl⟩
          · rw [ReactiveApplication.Implementation.runJoint_add strategy who players scheduler
              index 1 repaired memory, PMF.support_bind]
            refine Set.mem_iUnion₂.mpr ⟨next.2, _rightReached, ?_⟩
            simp only [ReactiveApplication.Implementation.runJoint, Prod.mk.eta, PMF.bind_pure]
            rw [← second, PMF.support_map]
            exact ⟨after, member, rfl⟩
          · simp only [Nat.sub_self, ReactiveApplication.runRounds, PMF.mem_support_pure_iff]
          · simp only [Nat.sub_self, ReactiveApplication.Implementation.runJoint,
              PMF.mem_support_pure_iff]
      · obtain ⟨stopped, before, checkpoint, checkpointLeft, checkpointRight, boundary,
          leftTail, rightTail⟩ := ended
        let leftLaw := app.round scheduler players next.1
        let rightLaw := strategy.round who players scheduler next.2.1 next.2.2
        let step := leftLaw.bind fun l => rightLaw.map fun r => (l, r)
        refine ⟨step, ?_, ?_, ?_⟩
        · simp only [step, PMF.map_bind, PMF.map_comp, Function.comp_def]
          rw [show (fun l => rightLaw.map (fun _ => l)) = (fun l => PMF.pure l) from
            funext fun _ => PMF.map_const _ _]
          exact PMF.bind_pure _
        · simp only [step, PMF.map_bind, PMF.map_comp, Function.comp_def]
          change (leftLaw.bind fun _ => rightLaw.map _root_.id) = rightLaw
          rw [PMF.map_id]
          exact PMF.bind_const _ _
        · intro after member
          obtain ⟨l, lMember, paired⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
          obtain ⟨r, rMember, actual⟩ := PMF.support_map .. ▸ paired
          subst after
          right
          refine ⟨stopped, Nat.le_trans before (Nat.le_succ _), checkpoint,
            checkpointLeft, checkpointRight, boundary, ?_, ?_⟩
          · rw [show index + 1 - stopped = (index - stopped) + 1 by omega,
              app.runRounds_add, PMF.support_bind]
            refine Set.mem_iUnion₂.mpr ⟨next.1, leftTail, ?_⟩
            simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using lMember
          · rw [show index + 1 - stopped = (index - stopped) + 1 by omega,
              ReactiveApplication.Implementation.runJoint_add, PMF.support_bind]
            refine Set.mem_iUnion₂.mpr ⟨next.2, rightTail, ?_⟩
            simpa only [ReactiveApplication.Implementation.runJoint, Prod.mk.eta,
              PMF.bind_pure] using rMember)
  refine ⟨coupling, left, right, ?_⟩
  intro next member
  rcases related next member with ongoing | closed
  · obtain ⟨afterFrame, afterOwn, afterPast, afterReady, _leftFixed, _rightFixed, _failed,
      _action, _value, _started, laterNext, afterSplit, afterSilent⟩ := ongoing
    exact Or.inl ⟨afterFrame, afterOwn, afterPast, afterReady, laterNext, afterSplit, afterSilent⟩
  · exact Or.inr closed

end Vegas
