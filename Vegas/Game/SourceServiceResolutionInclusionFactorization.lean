/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDisclosure
import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Pending.ReactiveBindingLikelihood
import Vegas.Pending.ReactiveCanonicalDecision
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.Source.ObservationRecall
import GameTheory.Math.Probability.ConditionalObservation

/-! # Actual canonical resolution inclusion

An effective source decision emits a real pending withholding or opening packet.
Inclusion of its fresh identity completes with the exact source disclosure result.
Initialized trace invariants supply opening provenance, serial freshness, input
recall and the empty intention table. No roster or handler-equivalence premise
is used. These are local inclusion laws, not a stopped continuation theorem.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Inclusion of the actually issued canonical decision preserves all recall
and network fields and completes with the source's typed publication result. -/
theorem source_resolution_decision_include
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (source : Config Player L Γ)
    (execution : (application setup leaks).Execution)
    (horizon remaining : Nat) (scheduler : (application setup leaks).Scheduler)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (agree : refs.Agrees source.state execution.application.config.store)
    (event : (graph setup).EventId)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (disclose : Bool)
    (effective : disclose = false ∨ ∃ value : L.Val payload,
      disclose = true ∧ disclosureResult published binding source true = .success value) :
    let app := application setup leaks
    let response := (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
      (execution.observe app owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    let submitted := execution.respond app owner response
    let id := (owner, execution.network.nextSerial owner)
    submitted.application = execution.application ∧
      submitted.includePending app id =
        { submitted with
          network := (submitted.network.includePending id).2
          application := execution.application.complete event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm)
              (disclosureResult published binding source disclose))
          receipts := submitted.receipts ++ [(id, true)] } := by
  intro app response submitted id
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have token (packet : Payload (graph setup))
      (named : packet.event? (graph setup) = some event) :
      execution.application.publicView.tokenFor packet = some ⟨event⟩ :=
    execution.application.publicView_tokenFor_of_ready packet event named ready
  have finish (material : WitnessedSubmission (graph setup))
      (chosen : response = ⟨some material⟩)
      (inert : app.submit execution.application owner material = execution.application)
      (message : WitnessedPacket (graph setup))
      (emitted : app.packet execution.application owner (execution.network.known owner) material =
        message)
      (handled : app.handle execution.application ⟨id, message⟩ =
        some (execution.application.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding source disclose)))) :
      submitted.application = execution.application ∧
        submitted.includePending app id =
          { submitted with
            network := (submitted.network.includePending id).2
            application := execution.application.complete event ready
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                (disclosureResult published binding source disclose))
            receipts := submitted.receipts ++ [(id, true)] } := by
    have applicationEq : submitted.application = execution.application := by
      simp only [submitted, ReactiveApplication.Execution.respond, chosen, inert]
    have networkEq : submitted.network = (execution.network.submit owner message).2 := by
      simp only [submitted, ReactiveApplication.Execution.respond, chosen, inert, emitted]
    have found : submitted.network.lookup id = some ⟨id, message⟩ := by
      rw [networkEq]
      exact facts.serials.lookup_submit owner message
    refine ⟨applicationEq, ?_⟩
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, applicationEq, handled, Option.getD_some, Option.isSome_some]
  rcases effective with rfl | ⟨value, rfl, success⟩
  · have chosen : response = ⟨some (disclosureSubmission (.withhold event))⟩ :=
      (runtime setup).canonicalServiceDecision_resolution_false leaks owner _ _ event owner
        payload (refs.get binding) _ outputEq codeEq node
    apply finish (disclosureSubmission (.withhold event)) chosen rfl
      ⟨.withhold event, none, some ⟨event⟩⟩
    · change (disclosureSubmission (.withhold event)).emit execution.application owner
        (execution.network.known owner) = _
      simp only [disclosureSubmission, WitnessedSubmission.emit,
        token (.withhold event) rfl]
    · rw [reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _
        (WitnessedPacket.tokenValid_withhold _ _)]
      have unremembered : execution.application.remembered event = none :=
        congrFun facts.remembered event
      simpa only [disclosureResult_false] using
        (runtime setup).handle_withhold_unremembered_eq execution.application id event owner
          payload (refs.get binding) _ outputEq codeEq node ready timely rfl unremembered
  · obtain ⟨candidate, associated, owned, verified, _⟩ :=
      guarded_rosterOpening_success setup leaks published binding source refs execution agree
        facts.binding event outputEq codeEq node value success
    have resolved := compiled_disclosure_result published binding source refs
      execution.application.config.store agree true
    rw [success, EventGraph.EventCode.resolveOutput?_playerStore] at resolved
    have stored : (refs.get binding).get? execution.application.config.store =
        some (.success value) := facts.binding.opening_stored _ _ _ associated verified
    let call : WitnessedSubmission (graph setup) :=
      disclosureSubmission (.opening event candidate ⟨payload, value⟩)
    let material := call.normalizeReactive owner (app.observePlayer execution.application owner)
      (execution.network.known owner)
    have chosen : response = ⟨some material⟩ := by
      have notBind who ty output code
          (impossible : nodeView (graph setup) event = .bind who ty output code) : False := by
        rw [node] at impossible
        cases impossible
      dsimp only [response]
      rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks owner _ _ event _ notBind]
      exact (runtime setup).serviceDecision_successful_opening leaks execution facts.inputs owner
        event payload (refs.get binding) _ outputEq codeEq node candidate value associated owned
        verified resolved
    have callEq : material.call = ⟨.opening event candidate ⟨payload, value⟩, none⟩ := by
      simp only [material, call, disclosureSubmission, WitnessedSubmission.normalizeReactive,
        Submission.normalizeReactive_none]
    have inert : app.submit execution.application owner material = execution.application := by
      change submitStep (material.call.register execution.application owner)
        owner material.call.packet = _
      rw [callEq]
      rfl
    apply finish material chosen inert
      ⟨.opening event candidate ⟨payload, value⟩,
        some ⟨candidate, ⟨payload, value⟩⟩, some ⟨event⟩⟩
    · have normalized := WitnessedSubmission.normalizeReactive_emit (runtime setup) leaks
        execution.application owner (execution.network.known owner) call
      change material.emit execution.application owner (execution.network.known owner) = _
      change material.emit execution.application owner (execution.network.known owner) =
        call.emit execution.application owner (execution.network.known owner) at normalized
      rw [normalized]
      have authentic : execution.application.candidates.verify candidate ⟨payload, value⟩ = true :=
        (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr verified
      simp only [call, disclosureSubmission, WitnessedSubmission.emit, owned, authentic,
        and_self, ↓reduceIte, token (.opening event candidate ⟨payload, value⟩) rfl]
    · rw [reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _
        (WitnessedPacket.tokenValid_opening _ _ _ _), success]
      exact (runtime setup).handle_opening_eq execution.application id event candidate owner
        payload (refs.get binding) _ outputEq codeEq node ready timely rfl owned associated value
        verified stored (.success value) resolved

/-- The real included decision extends the complete typed source store,
including earlier private bindings and deferred guard inputs. -/
theorem source_resolution_inclusion_agrees
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (source : Config Player L Γ)
    (execution : (application setup leaks).Execution)
    (horizon remaining : Nat) (scheduler : (application setup leaks).Scheduler)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some owner, execution⟩))
    (agree : refs.Agrees source.state execution.application.config.store)
    (event : (graph setup).EventId)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs source.registry source.revelations binding))
    (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (disclose : Bool)
    (effective : disclose = false ∨ ∃ value : L.Val payload,
      disclose = true ∧ disclosureResult published binding source true = .success value) :
    let app := application setup leaks
    let response := (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
      (execution.observe app owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
      (revealSuccessor published binding source disclose).state
      (((execution.respond app owner response).includePending app
        (owner, execution.network.nextSerial owner)).application.config.store) := by
  intro app response
  have actual := (source_resolution_decision_include setup leaks published binding refs source
    execution horizon remaining scheduler trace agree event ready timely outputEq codeEq node
      disclose effective).2
  rw [actual]
  change (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
    (revealSuccessor published binding source disclose).state
    (execution.application.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (disclosureResult published binding source disclose))).config.store
  exact complete_guarded_reveal_agrees (graph := graph setup) published binding source refs
    execution.application agree event ready outputEq before disclose

/-- Once the actual response law factors through the source successor, its
protected inclusion preserves that channel. The command records the real
pre-inclusion scheduler observation and retains the complete focal recall. -/
theorem source_async_resolution_inclusion_factorization
    {Seed : Type} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (focal : Player)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (horizon : Nat) (remaining : Seed → Nat)
    (scheduler : (application setup leaks).Scheduler)
    (trace : ∀ seed ∈ prior.support,
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining seed, some owner, execution seed⟩))
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (event : (graph setup).EventId)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (timely : ∀ seed ∈ prior.support,
      (execution seed).application.WithinDeadline (runtime setup) event)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : ∀ seed, cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding))
    (node : ∀ seed, nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs (source seed).registry
        (source seed).revelations binding) outputEq (codeEq seed))
    (disclose : Seed → Bool)
    (effective : ∀ seed ∈ prior.support, disclose seed = false ∨ ∃ value : L.Val payload,
      disclose seed = true ∧
        disclosureResult published binding (source seed) true = .success value)
    (noise : DecisionView focal ((published, .publication payload) :: Γ) → PMF _)
    (factor : prior.map (fun seed =>
        (revealSuccessor published binding (source seed) (disclose seed),
          (runtime setup).bindingTraffic leaks focal
            ((execution seed).respond (application setup leaks) owner
              ((runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
                ((execution seed).observe (application setup leaks) owner) event
                (cast (congrArg EventGraph.EventField.Action outputEq.symm) (disclose seed)))))) =
      (prior.map fun seed => revealSuccessor published binding (source seed) (disclose seed)).bind
        fun successor => (noise (successor.view focal)).map fun extra => (successor, extra)) :
    ∃ nextNoise : DecisionView focal ((published, .publication payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        (ReactiveApplication.Execution.environmentStep (application setup leaks)
          ((execution seed).respond (application setup leaks) owner
            ((runtime setup).canonicalServiceDecision leaks owner ((execution seed).recall owner)
              ((execution seed).observe (application setup leaks) owner) event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) (disclose seed))))
          (.include (owner, (execution seed).network.nextSerial owner))).map fun final =>
          (revealSuccessor published binding (source seed) (disclose seed),
            (runtime setup).bindingTraffic leaks focal final)) =
      (prior.map fun seed => revealSuccessor published binding (source seed) (disclose seed)).bind
        fun successor =>
          (nextNoise (successor.view focal)).map fun extra => (successor, extra) := by
  let app := application setup leaks
  let response := fun seed => (runtime setup).canonicalServiceDecision leaks owner
    ((execution seed).recall owner) ((execution seed).observe app owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) (disclose seed))
  let submitted := fun seed => (execution seed).respond app owner (response seed)
  let successor := fun seed => revealSuccessor published binding (source seed) (disclose seed)
  let id := fun seed => (owner, (execution seed).network.nextSerial owner)
  have included seed (supported : seed ∈ prior.support) :=
    source_resolution_decision_include setup leaks published binding refs (source seed)
      (execution seed) horizon (remaining seed) scheduler (trace seed supported)
      (agree seed supported) event (ready seed supported) (timely seed supported) outputEq
      (codeEq seed) (node seed) (disclose seed) (effective seed supported)
  have serial seed : (submitted seed).network.nextSerial owner =
      (execution seed).network.nextSerial owner + 1 := by
    have issues : (response seed).isSubmission app = true := by
      simp only [response, canonicalServiceDecision, canonicalReactiveDecision, node seed,
        ReactiveApplication.SubmissionNormalization.action, ReactiveApplication.Action.isSubmission]
    rw [show (submitted seed).network.nextSerial owner =
      ((execution seed).respond app owner (response seed)).network.nextSerial owner from rfl,
      app.respond_nextSerial, issues]
    simp only [and_self, ite_true]
  have coupled left (leftSupport : left ∈ prior.support)
      right (rightSupport : right ∈ prior.support)
      (seen : (successor left).view focal = (successor right).view focal)
      (same : (runtime setup).bindingTraffic leaks focal (submitted left) =
        (runtime setup).bindingTraffic leaks focal (submitted right)) :
      ((submitted left).environmentStep app (.include (id left))).map
          ((runtime setup).bindingTraffic leaks focal) =
        ((submitted right).environmentStep app (.include (id right))).map
          ((runtime setup).bindingTraffic leaks focal) := by
    have result := congrArg
      (fun view : DecisionView focal ((published, .publication payload) :: Γ) =>
        view.1.cells.get .here) seen
    change disclosureResult published binding (source left) (disclose left) =
      disclosureResult published binding (source right) (disclose right) at result
    have choices : disclose left = disclose right := by
      rcases effective left leftSupport with first | ⟨value, first, firstSuccess⟩
      · rcases effective right rightSupport with second | ⟨value, second, secondSuccess⟩
        · exact first.trans second.symm
        · rw [first, second, disclosureResult_false, secondSuccess] at result
          cases result
      · rcases effective right rightSupport with second | ⟨value, second, secondSuccess⟩
        · rw [first, second, firstSuccess, disclosureResult_false] at result
          cases result
        · exact first.trans second.symm
    have networks := congrArg Prod.fst same
    have receipts := congrArg (fun read => read.2.1) same
    have environments := congrArg (fun read => read.2.2.1) same
    have recalled := congrArg (fun read => read.2.2.2.1) same
    have views := congrArg (fun read => read.2.2.2.2.1) same
    have publics := congrArg (fun read => read.2.2.2.2.2) same
    dsimp only [bindingTraffic] at networks receipts environments recalled views publics
    have ids : id left = id right := by
      have counters := congrArg (fun network => network.nextSerial owner) networks
      rw [serial left, serial right] at counters
      exact congrArg (Prod.mk owner) (Nat.add_right_cancel counters)
    have observations : (submitted left).observeEnvironment app =
        (submitted right).observeEnvironment app := by
      change ReactiveApplication.EnvironmentView.mk (submitted left).network.publicView
        (submitted left).application.publicView (submitted left).receipts =
          ReactiveApplication.EnvironmentView.mk (submitted right).network.publicView
            (submitted right).application.publicView (submitted right).receipts
      rw [networks, publics, receipts]
    have leftInert : (submitted left).application = (execution left).application :=
      (included left leftSupport).1
    have rightInert : (submitted right).application = (execution right).application :=
      (included right rightSupport).1
    rw [leftInert, rightInert] at views publics
    have completed := State.complete_playerView_congr (execution left).application
      (execution right).application focal publics
      ((execution left).application.playerView_observation_eq _ focal views)
      (congrArg PlayerView.remembered views) (congrArg PlayerView.candidates views)
      event (ready left leftSupport) (ready right rightSupport)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) (disclose left))
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) (disclose right))
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (disclosureResult published binding (source left) (disclose left)))
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (disclosureResult published binding (source right) (disclose right)))
      (fun _ => congrArg _ result) (fun _ => congrArg _ choices)
    have completedPublic := congrArg PlayerView.publicView completed
    dsimp only [State.playerView] at completedPublic
    have leftInclude := (included left leftSupport).2
    have rightInclude := (included right rightSupport).2
    change (submitted left).includePending app (id left) =
      { submitted left with
        network := ((submitted left).network.includePending (id left)).2
        application := (execution left).application.complete event (ready left leftSupport)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) (disclose left))
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding (source left) (disclose left)))
        receipts := (submitted left).receipts ++ [(id left, true)] } at leftInclude
    change (submitted right).includePending app (id right) =
      { submitted right with
        network := ((submitted right).network.includePending (id right)).2
        application := (execution right).application.complete event (ready right rightSupport)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) (disclose right))
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (disclosureResult published binding (source right) (disclose right)))
        receipts := (submitted right).receipts ++ [(id right, true)] } at rightInclude
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    apply congrArg PMF.pure
    simp only [leftInclude, rightInclude, bindingTraffic]
    rw [networks, ids, receipts, environments, observations, recalled,
      completed, completedPublic]
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior successor
    (fun seed => (runtime setup).bindingTraffic leaks focal (submitted seed))
    (fun config => config.view focal) noise factor (fun _ => PMF.pure Unit.unit)
    (fun config _ => config) (fun config => config.view focal)
    (fun seed _ => ((submitted seed).environmentStep app (.include (id seed))).map
      ((runtime setup).bindingTraffic leaks focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ seen same =>
      coupled left leftSupport right rightSupport seen same)
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure, PMF.map_id,
    PMF.map_comp, Function.comp_def] using law

end Vegas
