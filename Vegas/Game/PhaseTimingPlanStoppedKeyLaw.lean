/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPlanStoppedLaw
import Vegas.Game.PhaseTimingBindingKey

/-! # Original operational-key hitting laws under complete owner words -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
      scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
        scheduler).InfoState who)]

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

include maximal

open Classical in
/-- Original history laws have the SAME operational channel at the first
specified own binding key. Typed past actions remain private and are filtered
separately; no equality of the owner's raw candidate values is asserted. -/
theorem phase_timing_plan_stopped_key_law
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (fallback : (who : Player) → (N).Policy who)
    (parts : (p : Pool) → Parts p)
    (opponents : (who : Player) → (N).BehavioralPolicy who) (owner : Player)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (firstWord secondWord : DecisionView owner Δ)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (left right : (app).Control)
    (firstHistory secondHistory : (E).History)
    (firstCurrent : firstHistory.state = some left)
    (secondCurrent : secondHistory.state = some right)
    (sameRemaining : left.remaining = right.remaining) (sameActor : left.actor = right.actor)
    (memory : BindingShadow (graph)) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (application : left.execution.application = memory.phased owner right.execution.application)
    (network : left.execution.network = right.execution.network)
    (receipts : left.execution.receipts = right.execution.receipts)
    (service : left.execution.environmentRecall = right.execution.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.execution.recall who = right.execution.recall who)
    (past : (left.execution.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (right.execution.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (clear : right.execution.application.current.excluded = ∅)
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (committing : phase.kind = .commitment)
    (lower : phase.low = low) (upper : phase.high = low + block.length)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (capacity : horizon ≤ bounds.candidateCount)
    (address : right.execution.application.attempt = ⟨low, generation⟩)
    (certificate : (E).WellFoundedHistories) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (wanted : Option (PhaseTimingKey graph)) :
    let firstProfile := GameTheory.Profile.update (sig := (N).behavioralSignature) opponents owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low generation slotWeight
            slotNonnegative slotBounded parts owner firstWord))
    let secondProfile := GameTheory.Profile.update (sig := (N).behavioralSignature) opponents owner
      ((menu).restrictPolicy initial horizon scheduler owner
        (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed (approximation.sequence n) block low generation slotWeight
            slotNonnegative slotBounded parts owner secondWord))
    let exits : (E).History → Prop := fun history => match history.state with
      | none => True
      | some control => control.execution.application.current.excluded ≠ ∅ ∨
          control.execution.application.phases ≠ phase :: remaining
    let hits : (E).History → Prop := fun history => match history.state with
      | none => False
      | some control => control.actor = some owner ∧
          control.execution.application.SeedRequest owner
            ⟨control.execution.application.attempt, event⟩ ∧
          phaseTimingKey runtime leaks owner ((N).infoOf owner history.trace) = wanted
    let stopped : (E).History → Prop := fun history => exits history ∨ hits history
    let readout := fun history : (E).History =>
      @ite _ (exits history) (Classical.propDecidable (exits history)) none
        (@ite _ (hits history) (Classical.propDecidable (hits history))
          (history.state.map fun control =>
            (control.remaining, control.actor,
              phaseExternalObservation runtime leaks owner control.execution,
              phaseOperationalView runtime leaks (control.execution.observe app owner),
              (control.execution.recall owner).map (fun entry =>
                (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))) none)
    ((N).runBehavioralUntil certificate firstProfile stopped firstHistory).map readout =
      ((N).runBehavioralUntil certificate secondProfile stopped secondHistory).map readout := by
  classical
  intro firstProfile secondProfile exits hits stopped readout
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have zeroGeneration (history : (E).History) (control : (app).Control)
      (current : history.state = some control)
      (isClear : control.execution.application.current.excluded = ∅) :
      control.execution.application.generation = 0 := by
    have counted : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some control) := by
      dsimp only [inputs]
      rw [PMF.map_comp]
      exact current ▸ history.trace
    exact (phase_clear_history runtime leaks plan inputs horizon scheduler control
      ((menu).toRawTrace _ horizon scheduler counted) isClear).1
  have generationZero : generation = 0 := by
    have actual := zeroGeneration secondHistory right secondCurrent clear
    have named := congrArg CommitAttemptId.generation address
    exact named.symm.trans actual
  let related := fun first second : (E).History =>
    ∃ count actor original repaired,
      first.state = some (⟨count, actor, original⟩ : (app).Control) ∧
      second.state = some (⟨count, actor, repaired⟩ : (app).Control) ∧
      ((exits first ∧ exits second) ∨ ∃ memory : BindingShadow graph,
        memory.OwnBindings owner ∧ (∀ slot, memory.candidates slot ≠ some .fresh) ∧
        original.application = memory.phased owner repaired.application ∧
        original.network = repaired.network ∧ original.receipts = repaired.receipts ∧
        original.environmentRecall = repaired.environmentRecall ∧
        (∀ who, who ≠ owner → original.recall who = repaired.recall who) ∧
        (original.recall owner).map (fun entry =>
            (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
          (repaired.recall owner).map (fun entry =>
            (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
  have sameHit (first second : (E).History) (count : Nat) (actor : Option Player)
      (original repaired : (app).Execution)
      (firstAt : first.state = some ⟨count, actor, original⟩)
      (secondAt : second.state = some ⟨count, actor, repaired⟩)
      (memory : BindingShadow graph) (owned : memory.OwnBindings owner)
      (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
      (state : original.application = memory.phased owner repaired.application)
      (net : original.network = repaired.network) (receipt : original.receipts = repaired.receipts)
      (word : (original.recall owner).map (fun entry =>
          (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
        (repaired.recall owner).map (fun entry =>
          (phaseOperationalView runtime leaks entry.beforeView, entry.emitted))) :
      hits first ↔ hits second := by
    have requests : original.application.SeedRequest owner
          ⟨original.application.attempt, event⟩ ↔ repaired.application.SeedRequest owner
          ⟨repaired.application.attempt, event⟩ := by rw [state]; rfl
    have keyEq (acting : actor = some owner)
        (request : repaired.application.SeedRequest owner
          ⟨repaired.application.attempt, event⟩) :
        phaseTimingKey runtime leaks owner ((N).infoOf owner first.trace) =
          phaseTimingKey runtime leaks owner ((N).infoOf owner second.trace) := by
      change phaseTimingKey runtime leaks owner
          (((menu).signals initial horizon scheduler).infoOf owner first.trace) =
        phaseTimingKey runtime leaks owner
          (((menu).signals initial horizon scheduler).infoOf owner second.trace)
      rw [(menu).info, (menu).info, firstAt, secondAt]
      simp only [ReactiveApplication.observe, acting, ite_true]
      exact phaseTimingKey_binding_memory runtime leaks
        (serviceGraph_revealRelaxedOrdered setup mode) memory owner owned valid original repaired
          state net receipt word event payload binding request
    simp only [hits, firstAt, secondAt]
    constructor
    · rintro ⟨acting, request, key⟩
      have afterRequest := requests.mp request
      exact ⟨acting, afterRequest, (keyEq acting afterRequest).symm.trans key⟩
    · rintro ⟨acting, request, key⟩
      exact ⟨acting, requests.mpr request, (keyEq acting request).trans key⟩
  have sameExit (first second : (E).History) (count : Nat) (actor : Option Player)
      (original repaired : (app).Execution)
      (firstAt : first.state = some ⟨count, actor, original⟩)
      (secondAt : second.state = some ⟨count, actor, repaired⟩)
      (memory : BindingShadow graph)
      (state : original.application = memory.phased owner repaired.application) :
      exits first ↔ exits second := by
    simp only [exits, firstAt, secondAt, state]
    rfl
  have halting : ∀ first second, related first second →
      (stopped first ∨ (E).terminal first.state ↔ stopped second ∨ (E).terminal second.state) := by
    rintro first second ⟨count, actor, original, repaired, firstAt, secondAt, linked⟩
    rcases linked with ⟨firstExit, secondExit⟩ |
      ⟨memory, owned, valid, state, net, receipt, _, _, word⟩
    · exact ⟨fun _ => Or.inl (Or.inl secondExit), fun _ => Or.inl (Or.inl firstExit)⟩
    · have hitEq := sameHit first second count actor original repaired firstAt secondAt memory
        owned valid state net receipt word
      have exitEq := sameExit first second count actor original repaired firstAt secondAt memory
        state
      have terminalEq : (E).terminal first.state ↔ (E).terminal second.state := by
        rw [firstAt, secondAt]
        rfl
      simp only [stopped, exitEq, hitEq, terminalEq]
  have classified : ∀ first second, related first second →
      stopped first ∨ (E).terminal first.state → readout first = readout second := by
    rintro first second ⟨count, actor, original, repaired, firstAt, secondAt, linked⟩ _
    rcases linked with ⟨firstExit, secondExit⟩ |
        ⟨memory, owned, valid, state, net, receipt, log, foreign, word⟩
    · simp only [readout, firstExit, secondExit, ite_true]
    · have exitEq := sameExit first second count actor original repaired firstAt secondAt memory
        state
      by_cases firstExit : exits first
      · have secondExit := exitEq.mp firstExit
        simp only [readout, firstExit, secondExit, ite_true]
      · have secondExit : ¬ exits second := fun yes => firstExit (exitEq.mpr yes)
        have hitEq := sameHit first second count actor original repaired firstAt secondAt memory
          owned valid state net receipt word
        have op := phaseOperationalView_memory runtime leaks memory owner owned valid original
          repaired state net receipt
        have external : phaseExternalObservation runtime leaks owner original =
            phaseExternalObservation runtime leaks owner repaired := by
          unfold phaseExternalObservation
          refine Prod.ext net (Prod.ext receipt (Prod.ext log (Prod.ext ?_ ?_)))
          · change (⟨original.network.publicView, original.application.publicView,
              original.receipts⟩ : (app).EnvironmentView) = ⟨_, _, _⟩
            rw [net, receipt, state, BindingShadow.phased_publicView owned]
            rfl
          · funext who
            by_cases same : who = owner
            · simp only [same, ite_true]
            · simp only [same, ite_false]
              apply congrArg some
              apply Prod.ext (foreign who same)
              change (⟨original.network.observe who, original.application.playerView who,
                original.receipts⟩ : (app).PlayerView) = ⟨_, _, _⟩
              rw [net, receipt, state, BindingShadow.phased_playerView_other owned _ who same]
              rfl
        simp only [readout, firstExit, secondExit, ite_false]
        by_cases firstHit : hits first
        · have secondHit := hitEq.mp firstHit
          simp only [firstHit, secondHit, ite_true, firstAt, secondAt, Option.map_some,
            external, op, word]
        · have secondHit : ¬ hits second := fun yes => firstHit (hitEq.mpr yes)
          simp only [firstHit, secondHit, ite_false]
  have step : ∀ first second, related first second → ¬ stopped first →
      ¬ (E).terminal first.state →
      ∃ joint : PMF ((E).History × (E).History),
        joint.map Prod.fst = (N).runBehavioralFrom firstProfile 1 first ∧
        joint.map Prod.snd = (N).runBehavioralFrom secondProfile 1 second ∧
        ∀ next ∈ joint.support, related next.1 next.2 := by
    rintro first second ⟨count, actor, original, repaired, firstAt, secondAt, linked⟩
      notStopped notTerminal
    have notExit : ¬ exits first := fun yes => notStopped (Or.inl yes)
    rcases linked with ⟨firstExit, _⟩ |
      ⟨memory, owned, valid, state, net, receipt, log, foreign, word⟩
    · exact (notExit firstExit).elim
    · have originalClear : original.application.current.excluded = ∅ := by
        by_contra nonempty
        apply notExit
        simp only [exits, firstAt]
        exact Or.inl nonempty
      have repairedClear : repaired.application.current.excluded = ∅ := by
        change (memory.phased owner repaired.application).current.excluded = ∅
        rw [← state]
        exact originalClear
      have originalInstalled : original.application.phases = phase :: remaining := by
        by_contra other
        apply notExit
        simp only [exits, firstAt]
        exact Or.inr other
      have repairedInstalled : repaired.application.phases = phase :: remaining := by
        rw [state] at originalInstalled
        exact originalInstalled
      have currentGeneration : repaired.application.generation = 0 :=
        zeroGeneration second ⟨count, actor, repaired⟩ secondAt repairedClear
      have currentAddress : repaired.application.attempt = ⟨low, generation⟩ := by
        simp only [PhaseRuntimeState.attempt, repairedInstalled, List.head?_cons, Option.map_some,
          Option.getD_some, lower, currentGeneration, generationZero]
      have running : ¬((⟨count, actor, original⟩ : (app).Control).remaining = 0 ∧
          (⟨count, actor, original⟩ : (app).Control).actor = none) := by
        intro terminal
        apply notTerminal
        rw [firstAt]
        exact terminal
      obtain ⟨joint, firstLaw, secondLaw, preserved⟩ := phase_timing_plan_history_word_coupling
        setup mode runtime leaks bounds plan maximal horizon scheduler bound finite wellFormed
          target approximation n fallback parts opponents owner block low generation firstWord
            secondWord slotWeight slotNonnegative slotBounded ⟨count, actor, original⟩
              ⟨count, actor, repaired⟩ first second firstAt secondAt rfl rfl running memory owned
                valid state net receipt log foreign word repairedClear phase remaining
                  repairedInstalled committing lower upper values capacity currentAddress
      refine ⟨joint, firstLaw, secondLaw, ?_⟩
      intro next supported
      obtain ⟨nextCount, nextActor, firstNext, secondNext, firstNextAt, secondNextAt, nextLinked⟩ :=
        preserved next supported
      refine ⟨nextCount, nextActor, firstNext, secondNext, firstNextAt, secondNextAt, ?_⟩
      rcases nextLinked with ⟨firstExcluded, secondExcluded⟩ | nextMemory
      · left
        constructor
        · simp only [exits, firstNextAt]
          exact Or.inl firstExcluded
        · simp only [exits, secondNextAt]
          exact Or.inl secondExcluded
      · exact Or.inr nextMemory
  apply (N).runBehavioralUntil_map_eq_of_paired_steps (N) certificate certificate firstProfile
    secondProfile stopped stopped readout readout related halting classified step
  refine ⟨left.remaining, left.actor, left.execution, right.execution, firstCurrent, ?_, ?_⟩
  · rw [secondCurrent, sameRemaining, sameActor]
  · exact Or.inr ⟨memory, owned, valid, application, network, receipts, service, recalled, past⟩

end Vegas
