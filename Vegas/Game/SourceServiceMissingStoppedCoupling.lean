/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePastCommitmentTraffic
import Vegas.Pending.ReactiveBindingPacketStep
import Vegas.Pending.ReactiveBindingInertClosure
import Vegas.Pending.ReactiveBindingUsableResume
import Vegas.Pending.ReactiveBindingRiskRecall
import Interaction.ReactiveImplementationInvariant

/-! # Actual missing-binding continuation up to an owner's signed breach

The owner uses one retained private implementation at every hidden history.
Its later operational slice permits effective noncommitment responses and
fresh usable registrations. Foreign raw responses and scheduler commands remain
arbitrary. The evaluator stops sharing
draws once the original actual traffic contains an owner signed-content breach.
The same envelope persists on both sides of subsequent independent tails.
This is a finite continuation coupling, not terminal utility domination or
admission of unusable or reused future owner binding responses.
The owner's actual public response-risk records agree on clean support;
their equality is seeded from the two legal raw traces and preserved by real
response and environment steps. The implementation still uses the complete
effective menu: equal risk records do not assert canonical-menu admission.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private def continuationFacts (execution : (application setup leaks).Execution) : Prop :=
  SettledFacts setup leaks execution ∧ execution.application.BindingInvariant ∧
    ((runtime setup).packetEvidence leaks).Sound execution ∧
      (runtime setup).ReactiveCommitmentsFixed leaks execution ∧
        execution.application.remembered = (fun _ => none) ∧
          execution.InputRecall (application setup leaks)

private theorem continuationFacts_respond
    (execution : (application setup leaks).Execution) (actor : Player)
    (response : (application setup leaks).Action)
    (facts : continuationFacts execution) :
    continuationFacts (execution.respond (application setup leaks) actor response) := by
  exact ⟨settledFacts_respond execution facts.1 actor response,
    ((runtime setup).reactiveBindingInvariant leaks).respond execution actor response facts.2.1,
    ((runtime setup).packetEvidence leaks).sound_respond execution actor response facts.2.2.1,
    (runtime setup).reactiveCommitmentsFixed_respond leaks execution actor response facts.2.2.2.1,
    ((runtime setup).reactiveRememberedInvariant leaks (fun table => table = fun _ => none)).respond
      execution actor response facts.2.2.2.2.1,
    (application setup leaks).respond_inputRecall execution actor response facts.2.2.2.2.2⟩

private theorem continuationFacts_environment
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (facts : continuationFacts execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    continuationFacts next := by
  let cache := (runtime setup).reactiveRememberedInvariant leaks
    (fun table => table = fun _ => none)
  exact ⟨settledFacts_environment execution next command facts.1 reached,
    ((runtime setup).reactiveBindingInvariant leaks).environmentStep execution next command
      facts.2.1 reached,
    ((runtime setup).packetEvidence leaks).sound_environment execution next command facts.2.2.1
      reached,
    (runtime setup).reactiveCommitmentsFixed_environment leaks execution next command
      facts.2.2.2.1 reached,
    cache.environmentStep execution next command facts.2.2.2.2.1 reached,
    (application setup leaks).environment_inputRecall execution next command facts.2.2.2.2.2
      reached⟩

private theorem continuationFacts_policy
    (players : Player → (application setup leaks).Policy) :
    (application setup leaks).PolicyInvariant players continuationFacts where
  respond execution actor response facts _ :=
    continuationFacts_respond execution actor response facts
  environment := continuationFacts_environment

private theorem continuationFacts_service (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler continuationFacts where
  respond := continuationFacts_respond
  environment execution next command facts _ reached :=
    continuationFacts_environment execution next command facts reached

private theorem continuationFacts_history
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) : continuationFacts control.execution := by
  let facts := legalFacts setup leaks horizon scheduler control trace
  exact ⟨settledFacts_history (initialLaw setup) horizon scheduler trace, facts.binding,
    facts.evidence, (runtime setup).reactiveCommitmentsFixed_history leaks (initialLaw setup)
      horizon scheduler trace, facts.remembered, facts.inputs⟩

private def ownerBreachInInputs (who : Player)
    (execution : (application setup leaks).Execution) : Prop :=
  ∃ message ∈ execution.network.inputs, message.sender = who ∧ SignedContentBreach message

private theorem input_policy
    (players : Player → (application setup leaks).Policy)
    (message : Message Player (WitnessedPacket (graph setup))) :
    (application setup leaks).PolicyInvariant players
      (fun execution => message ∈ execution.network.inputs) where
  respond execution actor response member _ := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact member
    | some material => exact List.mem_append_left _ member
  environment execution next command member reached := by
    rw [(application setup leaks).environmentStep_inputs execution next command reached]
    exact member

private theorem input_service
    (scheduler : (application setup leaks).Scheduler)
    (message : Message Player (WitnessedPacket (graph setup))) :
    (application setup leaks).ServiceInvariant scheduler
      (fun execution => message ∈ execution.network.inputs) where
  respond execution actor response member := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => exact member
    | some material => exact List.mem_append_left _ member
  environment execution next command member _ reached := by
    rw [(application setup leaks).environmentStep_inputs execution next command reached]
    exact member

variable [Fintype Player]

omit [Fintype Player] in
private theorem resume_submissionRiskRecords
    {memory nextMemory : BindingMemory (runtime setup) leaks} {owner : Player}
    {original repaired left right : (application setup leaks).Execution}
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (same : (original.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
      (repaired.recall owner).map ((runtime setup).submissionRiskRecord leaks))
    (players : Player → (application setup leaks).Policy)
    (strategy : (application setup leaks).Implementation
      (BindingMemory (runtime setup) leaks))
    (actor : Option Player)
    (leftReached : left ∈ ((application setup leaks).resume players actor original).support)
    (rightReached : (right, nextMemory) ∈
      (strategy.resume owner players actor repaired memory).support)
    (afterFrame : BindingMemory.Frame (runtime setup) leaks nextMemory owner left right) :
    (left.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
      (right.recall owner).map ((runtime setup).submissionRiskRecord leaks) := by
  let app := application setup leaks
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp leftReached
      cases (PMF.mem_support_pure_iff _ _).mp rightReached
      exact same
  | some actor =>
      change left ∈ (app.invoke players actor original).support at leftReached
      obtain ⟨leftResponse, _, rfl⟩ := PMF.support_map .. ▸ leftReached
      by_cases own : actor = owner
      · subst actor
        simp only [ReactiveApplication.Implementation.resume, ↓reduceIte] at rightReached
        change (right, nextMemory) ∈
          ((strategy.respond memory (repaired.recall owner, repaired.observe app owner)).map
            (fun response => (repaired.respond app owner response.1, response.2))).support
          at rightReached
        obtain ⟨result, _, equality⟩ := PMF.support_map .. ▸ rightReached
        rcases result with ⟨rightResponse, updated⟩
        cases equality
        have named := afterFrame.submissions
        rw [(runtime setup).submissionRecall_respond, (runtime setup).submissionRecall_respond,
          ← frame.submissions] at named
        have eventEq := List.append_cancel_left named
        have actual : (runtime setup).submittedEvent? leaks leftResponse =
            (runtime setup).submittedEvent? leaks rightResponse := by
          simpa only [List.cons.injEq, and_true] using eventEq
        exact frame.submissionRiskRecords_respond (runtime setup) leaks same _ _ actual
      · simp only [ReactiveApplication.Implementation.resume, own, ↓reduceIte] at rightReached
        change (right, nextMemory) ∈
          ((app.invoke players actor repaired).map (fun next => (next, memory))).support
          at rightReached
        obtain ⟨after, supported, equality⟩ := PMF.support_map .. ▸ rightReached
        cases equality
        obtain ⟨rightResponse, _, rfl⟩ := PMF.support_map .. ▸ supported
        rw [app.respond_recall_other original actor owner (Ne.symm own),
          app.respond_recall_other repaired actor owner (Ne.symm own)]
        exact same

private theorem clean_dispatch_coupling
    {memory : BindingMemory (runtime setup) leaks} {owner : Player}
    {original repaired : (application setup leaks).Execution}
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (provenance : OwnerCommitmentsSettledOrMatching owner original repaired)
    (riskRecords : (original.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
      (repaired.recall owner).map ((runtime setup).submissionRiskRecord leaks))
    (leftFacts : continuationFacts original) (rightFacts : continuationFacts repaired)
    (clean : ¬ ownerBreachInInputs owner original)
    (bounds : MessageBounds (graph setup))
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (players : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (effective : ∀ earlier view response, response ∈ (players owner earlier view).support →
      response ∈ (bounds.menu (runtime setup) leaks).actions owner earlier view)
    (usable : ∀ earlier view response, response ∈ (players owner earlier view).support →
      (∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
        FreshUsableBindingResponse (runtime setup) leaks owner view.application response)
    (command : (application setup leaks).Command) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.menu (runtime setup) leaks) owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.dispatch players command original ∧
      coupling.map Prod.snd = (repaired.environmentStep app command).bind
        (fun next => strategy.resume owner players (command.actor? app) next memory) ∧
      ∀ next ∈ coupling.support,
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings owner ∧
          next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsSettledOrMatching owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          (next.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
            (next.2.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) ∧
          next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
          ∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
            next.2.1.application.candidates.lookup (owner, slot) = .openable raw := by
  classical
  let app := application setup leaks
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
    (bounds.menu (runtime setup) leaks) owner reference (players owner)
  have ownerCommitment (id event candidate evidence token)
      (found : original.network.lookup id =
        some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩)
      (authored : id.1 = owner) (valid) :=
    provenance _ (leftFacts.1.carried.lookup id _ found) authored event candidate rfl valid
  obtain ⟨environment, left, right, related⟩ := frame.environment_coupling_or_owner_breach
    onlyBindings past leftFacts.2.2.1 leftFacts.2.1 rightFacts.2.1 leftFacts.2.2.2.1
      leftFacts.2.2.2.2.1 rightFacts.2.2.2.2.1
        ownerCommitment command
  have leftSupport (pair) (member : pair ∈ environment.support) :
      pair.1 ∈ (original.environmentStep app command).support := by
    rw [← left]
    rw [PMF.support_map]
    exact ⟨pair, member, rfl⟩
  have rightSupport (pair) (member : pair ∈ environment.support) :
      pair.2 ∈ (repaired.environmentStep app command).support := by
    rw [← right]
    rw [PMF.support_map]
    exact ⟨pair, member, rfl⟩
  have paired (pair) (member : pair ∈ environment.support) :
      BindingMemory.Frame (runtime setup) leaks memory owner pair.1 pair.2 := by
    rcases related pair member with good | ⟨id, packet, _, found, authored, breach⟩
    · exact good
    · exact (clean ⟨_, leftFacts.1.carried.lookup id _ found, authored, breach⟩).elim
  have capability (pair) (member : pair ∈ environment.support) (slot raw)
      (opened : pair.1.application.candidates.lookup (owner, slot) = .openable raw) :
      pair.2.application.candidates.lookup (owner, slot) = .openable raw :=
    ((runtime setup).reactive_environment_openable_iff repaired pair.2 command
      (rightSupport pair member) (owner, slot) raw).mpr
        (preserved slot raw (((runtime setup).reactive_environment_openable_iff original pair.1
          command (leftSupport pair member) (owner, slot) raw).mp opened))
  have startedAfter (pair) (member : pair ∈ environment.support) :
      reference.length ≤ (pair.2.recall owner).length := by
    rw [app.environmentStep_recall repaired pair.2 command (rightSupport pair member)]
    exact started
  have pastAfter (pair) (member : pair ∈ environment.support) :
      memory.shadow.CompletedAt pair.1.application.config :=
    past.mono (((runtime setup).reactiveCompletedInvariant leaks
      original.application.config.cut.completed).environmentStep original pair.1 command
        (Finset.Subset.refl _) (leftSupport pair member))
  have provenanceAfter (pair) (member : pair ∈ environment.support) :
      OwnerCommitmentsSettledOrMatching owner pair.1 pair.2 :=
    provenance.environment pair.1 pair.2 command
      (leftSupport pair member) (rightSupport pair member)
  have recordsAfter (pair) (member : pair ∈ environment.support) :
      (pair.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
        (pair.2.recall owner).map ((runtime setup).submissionRiskRecord leaks) := by
    rw [app.environmentStep_recall original pair.1 command (leftSupport pair member),
      app.environmentStep_recall repaired pair.2 command (rightSupport pair member)]
    exact riskRecords
  have existsResume (pair) (member : pair ∈ environment.support) :=
    (paired pair member).usable_effective_resume_coupling onlyBindings (pastAfter pair member)
      (provenanceAfter pair member) bounds
      (app.environment_inputRecall original pair.1 command leftFacts.2.2.2.2.2
        (leftSupport pair member))
      (app.environment_inputRecall repaired pair.2 command rightFacts.2.2.2.2.2
        (rightSupport pair member))
      (capability pair member) players reference (startedAfter pair member) effective usable
        (command.actor? app)
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
      _ = environment.bind (fun pair => strategy.resume owner players (command.actor? app)
          pair.2 memory) := by
        apply bindOnSupport_eq_bind_of_eq_on_support _
        intro pair member
        exact (existsResume pair member).choose_spec.2.1
      _ = (environment.map Prod.snd).bind (fun next =>
          strategy.resume owner players (command.actor? app) next memory) :=
        by rw [PMF.bind_map]; rfl
      _ = _ := by rw [right]
  · intro next member
    obtain ⟨pair, chosen, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ member)
    have step := (existsResume pair chosen).choose_spec
    have leftReached : next.1 ∈ (app.resume players (command.actor? app) pair.1).support := by
      rw [← step.1, PMF.support_map]
      exact ⟨next, reached, rfl⟩
    have rightReached : next.2 ∈
        (strategy.resume owner players (command.actor? app) pair.2 memory).support := by
      rw [← step.2.1, PMF.support_map]
      exact ⟨next, reached, rfl⟩
    obtain ⟨afterFrame, afterOwn, afterPast, afterLedger, afterStarted, leftRecall,
      rightRecall, afterCapability⟩ := step.2.2 next reached
    exact ⟨afterFrame, afterOwn, afterPast, afterLedger, afterStarted,
      resume_submissionRiskRecords (paired pair chosen) (recordsAfter pair chosen) players
        strategy (command.actor? app) leftReached rightReached afterFrame,
      leftRecall, rightRecall, afterCapability⟩

private theorem clean_round_coupling
    {memory : BindingMemory (runtime setup) leaks} {owner : Player}
    {original repaired : (application setup leaks).Execution}
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (provenance : OwnerCommitmentsSettledOrMatching owner original repaired)
    (riskRecords : (original.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
      (repaired.recall owner).map ((runtime setup).submissionRiskRecord leaks))
    (leftFacts : continuationFacts original) (rightFacts : continuationFacts repaired)
    (clean : ¬ ownerBreachInInputs owner original)
    (bounds : MessageBounds (graph setup))
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (players : Player → (application setup leaks).Policy)
    (scheduler : (application setup leaks).Scheduler)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (effective : ∀ earlier view response, response ∈ (players owner earlier view).support →
      response ∈ (bounds.menu (runtime setup) leaks).actions owner earlier view)
    (usable : ∀ earlier view response, response ∈ (players owner earlier view).support →
      (∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
        FreshUsableBindingResponse (runtime setup) leaks owner view.application response) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.menu (runtime setup) leaks) owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.round scheduler players original ∧
      coupling.map Prod.snd = strategy.round owner players scheduler repaired memory ∧
      ∀ next ∈ coupling.support,
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings owner ∧
          next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsSettledOrMatching owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          (next.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
            (next.2.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) ∧
          next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
          ∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
            next.2.1.application.candidates.lookup (owner, slot) = .openable raw := by
  classical
  let app := application setup leaks
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
    (bounds.menu (runtime setup) leaks) owner reference (players owner)
  let law := scheduler original.environmentRecall (original.observeEnvironment app)
  have existsDispatch (command) (member : command ∈ law.support) :=
    clean_dispatch_coupling frame onlyBindings past provenance riskRecords leftFacts rightFacts
      clean bounds
      preserved players reference started effective usable command
  let dispatch := fun command member => (existsDispatch command member).choose
  refine ⟨law.bindOnSupport dispatch, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro command member
    exact (existsDispatch command member).choose_spec.1
  · rw [map_bindOnSupport]
    have same : scheduler repaired.environmentRecall (repaired.observeEnvironment app) = law := by
      rw [← frame.service, ← frame.environment]
    change _ = (scheduler repaired.environmentRecall (repaired.observeEnvironment app)).bind _
    rw [same]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro command member
    exact (existsDispatch command member).choose_spec.2.1
  · intro next member
    obtain ⟨command, chosen, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ member)
    exact (existsDispatch command chosen).choose_spec.2.2 next reached

/-- From actual initialized prefixes and a completed private repair, one
fixed owner implementation couples the full finite evaluator. Before the
prepared event completes, the actual prefix policy sends no further owner
commitments. Thereafter the owner may also register fresh typed values. The
current memory and traffic resources evolve through those registrations.
Foreign responses and all scheduler commands are arbitrary. The exceptional
branch carries the SAME actual owner breach, without a renewed fine claim. -/
theorem sourceService_missing_usable_stopped_coupling
    (bounds : MessageBounds (graph setup)) (owner : Player)
    (players : Player → (application setup leaks).Policy)
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (effective : ∀ earlier view response, response ∈ (players owner earlier view).support →
      response ∈ (bounds.menu (runtime setup) leaks).actions owner earlier view)
    (usable : ∀ earlier view response, response ∈ (players owner earlier view).support →
      (∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
        FreshUsableBindingResponse (runtime setup) leaks owner view.application response)
    (prefixPlayers : Player → (application setup leaks).Policy)
    (prefixNoncommitment : ∀ earlier view response,
      response ∈ (prefixPlayers owner earlier view).support →
        ∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate)
    (before original repaired : (application setup leaks).Control)
    (beforeTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some before))
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some original))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some repaired))
    (current : (graph setup).EventId)
    (ready : before.execution.application.config.cut.Ready current)
    (response : (application setup leaks).Action) (preparation : Nat)
    (arrival : original.execution ∈ ((application setup leaks).runRounds scheduler prefixPlayers
      preparation (before.execution.respond (application setup leaks) owner response)).support)
    (completed : current ∈ original.execution.application.config.cut.completed)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original.execution
      repaired.execution)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.execution.application.config)
    (preserved : ∀ slot raw,
      original.execution.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.execution.application.candidates.lookup (owner, slot) = .openable raw)
    (reference : List (application setup leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.execution.recall owner).length)
    (count : Nat) :
    let app := application setup leaks
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.menu (runtime setup) leaks) owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.runRounds scheduler players count original.execution ∧
      coupling.map Prod.snd = strategy.runJoint owner players scheduler count repaired.execution
        memory ∧
      ∀ next ∈ coupling.support,
        (BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings owner ∧
          next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsSettledOrMatching owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          (next.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
            (next.2.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) ∧
          next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
          (∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
            next.2.1.application.candidates.lookup (owner, slot) = .openable raw) ∧
          ∀ bound, (runtime setup).serviceRisk leaks bound owner (next.1.recall owner)
              (next.1.observe app owner) =
            (runtime setup).serviceRisk leaks bound owner (next.2.1.recall owner)
              (next.2.1.observe app owner)) ∨
          ∃ message, message.sender = owner ∧ SignedContentBreach message ∧
            message ∈ next.1.network.inputs ∧ message ∈ next.2.1.network.inputs := by
  classical
  let app := application setup leaks
  let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
    (bounds.menu (runtime setup) leaks) owner reference (players owner)
  let good (next : app.Execution × app.Execution × BindingMemory (runtime setup) leaks) :=
    BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
      next.2.2.shadow.OwnBindings owner ∧
      next.2.2.shadow.CompletedAt next.1.application.config ∧
      OwnerCommitmentsSettledOrMatching owner next.1 next.2.1 ∧
      reference.length ≤ (next.2.1.recall owner).length ∧
      (next.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) =
        (next.2.1.recall owner).map ((runtime setup).submissionRiskRecord leaks) ∧
      next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
      ∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
        next.2.1.application.candidates.lookup (owner, slot) = .openable raw
  let bad (next : app.Execution × app.Execution × BindingMemory (runtime setup) leaks) :=
    ∃ message, message.sender = owner ∧ SignedContentBreach message ∧
      message ∈ next.1.network.inputs ∧ message ∈ next.2.1.network.inputs
  have originalFacts := continuationFacts_history horizon scheduler original leftTrace
  have repairedFacts := continuationFacts_history horizon scheduler repaired rightTrace
  have startFacts := settledFacts_respond before.execution
    (settledFacts_history (initialLaw setup) horizon scheduler beforeTrace) owner response
  have readyAfter : (before.execution.respond app owner response).application.config.cut.Ready
      current := by
    rw [((runtime setup).reactive_respond_application leaks before.execution owner response).1]
    exact ready
  have initialBound := (ownerCommitmentRanksBelow_policyInvariant setup leaks prefixPlayers owner
    current.val prefixNoncommitment).runRounds scheduler preparation _ original.execution
      (ownerCommitmentRanksBelow_of_ready setup leaks _ startFacts owner current readyAfter) arrival
  have initialProvenance : OwnerCommitmentsSettledOrMatching owner original.execution
      repaired.execution := by
    intro message member authored event candidate committed valid
    exact Or.inl (ownerCommitmentRanksBelow_completed setup leaks original.execution owner
      current initialBound completed message member authored event candidate committed valid)
  have initialRecords := frame.submissionRiskRecords (runtime setup) leaks leftTrace rightTrace
  have coupled : ∀ count, ∃ coupling :
      PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = app.runRounds scheduler players count original.execution ∧
      coupling.map Prod.snd = strategy.runJoint owner players scheduler count repaired.execution
        memory ∧ ∀ next ∈ coupling.support, good next ∨ bad next := by
    intro count
    induction count with
    | zero =>
        refine ⟨PMF.pure (original.execution, repaired.execution, memory), PMF.pure_map ..,
          PMF.pure_map .., ?_⟩
        intro next member
        cases (PMF.mem_support_pure_iff _ _).mp member
        exact Or.inl ⟨frame, onlyBindings, past, initialProvenance, started, initialRecords,
          originalFacts.2.2.2.2.2, repairedFacts.2.2.2.2.2, preserved⟩
    | succ count ih =>
        obtain ⟨joint, first, second, related⟩ := ih
        have leftSupport (next) (member : next ∈ joint.support) :
            next.1 ∈ (app.runRounds scheduler players count original.execution).support := by
          rw [← first, PMF.support_map]
          exact ⟨next, member, rfl⟩
        have rightSupport (next) (member : next ∈ joint.support) :
            next.2 ∈ (strategy.runJoint owner players scheduler count repaired.execution
              memory).support := by
          rw [← second, PMF.support_map]
          exact ⟨next, member, rfl⟩
        have independent
            (next : app.Execution × app.Execution × BindingMemory (runtime setup) leaks)
            (breach : bad next) :
            ∃ step : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
              step.map Prod.fst = app.round scheduler players next.1 ∧
              step.map Prod.snd = strategy.round owner players scheduler next.2.1 next.2.2 ∧
              ∀ after ∈ step.support, good after ∨ bad after := by
          obtain ⟨message, authored, forbidden, leftEmitted, rightEmitted⟩ := breach
          let left := app.round scheduler players next.1
          let right := strategy.round owner players scheduler next.2.1 next.2.2
          let step := left.bind fun l => right.map fun r => (l, r)
          refine ⟨step, ?_, ?_, ?_⟩
          · simp only [step, PMF.map_bind, PMF.map_comp, Function.comp_def]
            rw [show (fun l => right.map (fun _ => l)) =
                (fun l => PMF.pure l) from funext fun _ => PMF.map_const _ _]
            exact PMF.bind_pure _
          · simp only [step, PMF.map_bind, PMF.map_comp, Function.comp_def]
            change (left.bind fun _ => right.map id) = right
            rw [PMF.map_id]
            exact PMF.bind_const _ _
          · intro after member
            obtain ⟨l, lMember, pairedMember⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
            obtain ⟨r, rMember, rfl⟩ := PMF.support_map .. ▸ pairedMember
            obtain ⟨command, _, dispatched⟩ :=
              Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ lMember)
            exact Or.inr ⟨message, authored, forbidden,
              (input_policy players message).dispatch command next.1 l leftEmitted dispatched,
              (input_service scheduler message).implementation_round strategy owner players
                next.2.1 next.2.2 r rightEmitted rMember⟩
        have existsStep (next) (member : next ∈ joint.support) :
            ∃ step : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
              step.map Prod.fst = app.round scheduler players next.1 ∧
              step.map Prod.snd = strategy.round owner players scheduler next.2.1 next.2.2 ∧
              ∀ after ∈ step.support, good after ∨ bad after := by
          rcases related next member with matched | breach
          swap
          · exact independent next breach
          by_cases breached : ownerBreachInInputs owner next.1
          · obtain ⟨message, emitted, authored, forbidden⟩ := breached
            exact independent next
              ⟨message, authored, forbidden, emitted, matched.1.network ▸ emitted⟩
          have leftCurrentFacts := (continuationFacts_policy players).runRounds scheduler count
            original.execution next.1 originalFacts (leftSupport next member)
          have rightCurrentFacts := (continuationFacts_service scheduler).implementation_runJoint
            strategy owner players count repaired.execution memory next.2 repairedFacts
              (rightSupport next member)
          obtain ⟨currentFrame, currentOwn, currentPast, currentLedger, currentStarted,
            currentRecords, _currentLeftRecall, _currentRightRecall, currentCapability⟩ := matched
          obtain ⟨step, left, right, continued⟩ := clean_round_coupling currentFrame currentOwn
            currentPast currentLedger currentRecords leftCurrentFacts rightCurrentFacts
              breached bounds
              currentCapability players scheduler reference currentStarted effective usable
          refine ⟨step, left, right, fun after afterMember => ?_⟩
          exact Or.inl (continued after afterMember)
        let step := fun next member => (existsStep next member).choose
        refine ⟨joint.bindOnSupport step, ?_, ?_, ?_⟩
        · rw [map_bindOnSupport]
          calc
            _ = joint.bind (fun next => app.round scheduler players next.1) := by
              apply bindOnSupport_eq_bind_of_eq_on_support _
              intro next member
              exact (existsStep next member).choose_spec.1
            _ = (joint.map Prod.fst).bind (app.round scheduler players) := by
              rw [PMF.bind_map]; rfl
            _ = _ := by
              rw [first, app.runRounds_add]
              simp only [ReactiveApplication.runRounds, PMF.bind_pure]
        · rw [map_bindOnSupport]
          calc
            _ = joint.bind (fun next => strategy.round owner players scheduler next.2.1
                next.2.2) := by
              apply bindOnSupport_eq_bind_of_eq_on_support _
              intro next member
              exact (existsStep next member).choose_spec.2.1
            _ = (joint.map Prod.snd).bind (fun next => strategy.round owner players scheduler
                next.1 next.2) := by rw [PMF.bind_map]; rfl
            _ = _ := by
              rw [second, ReactiveApplication.Implementation.runJoint_add]
              simp only [ReactiveApplication.Implementation.runJoint, Prod.mk.eta, PMF.bind_pure]
              rfl
        · intro final member
          obtain ⟨next, chosen, reached⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ member)
          exact (existsStep next chosen).choose_spec.2.2 final reached
  obtain ⟨coupling, left, right, related⟩ := coupled count
  refine ⟨coupling, left, right, fun next member => ?_⟩
  rcases related next member with matched | breach
  · obtain ⟨currentFrame, currentOwn, currentPast, currentLedger, currentStarted,
      currentRecords, leftRecall, rightRecall, currentCapability⟩ := matched
    refine Or.inl ⟨currentFrame, currentOwn, currentPast, currentLedger, currentStarted,
      currentRecords, leftRecall, rightRecall, currentCapability, ?_⟩
    intro bound
    exact (runtime setup).serviceRisk_congr leaks bound owner _ _ _ _ rfl
      currentFrame.publicView currentRecords
  · exact Or.inr breach

end Vegas
