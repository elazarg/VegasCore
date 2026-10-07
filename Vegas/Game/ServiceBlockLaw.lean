/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceBlockDecode
import Vegas.Game.ServiceTimingCoupling

/-! # One deviating player through a block of commitments

Against the first-turn clients of a source profile, one player follows an
arbitrary native policy while the scheduler satisfies the asynchronous
contract. On a reveal-relaxed graph, a maximal run of commitments between two
public events forms a block of bindings. Through such a block, the decoded
source state and the deviator's traffic have the joint law of the source
protocol in which the deviator follows behavioral kernels at its commitments of
the block, and the deviator's traffic factors through its new source view
(`Vegas.asyncDeviation_block_factorization`).

The proof draws the other owners' commitments in advance
(`Vegas.blockPlayers_runUntil_predraw`); whatever they draw, the deviator's
traffic at the end of the block has one law, which depends on the execution
only through the deviator's traffic at the block's start
(`Vegas.decidedBlock_readout_congr`); and the drawn commitments together with
the deviator's choices decode to the source configuration of the block
(`Vegas.blockDecode`), whose law is the source law of the block with the
deviator's choices supplied (`Vegas.assignChain_assemble`). The behavioral
kernels are then the deviator's conditional choices given its view
(`Vegas.listChain_factorization`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- Leading commitments are events of the program. -/
theorem CommitPrefix.le_eventCount :
    ∀ {count : Nat} {Γ : SourceCtx Player L} {names : Finset VarId}
      {program : SourceProgram Player L Γ names}, CommitPrefix program count →
      count ≤ eventCount program
  | 0, _, _, _, _ => Nat.zero_le _
  | _ + 1, _, _, .commit _ _ _ _ next, prefixed => by
      have := CommitPrefix.le_eventCount (program := next) prefixed
      simp only [eventCount]
      omega
  | _ + 1, _, _, .ret _, prefixed => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed => prefixed.elim

/-- The deviated first-turn clients are the block's players with nothing
drawn. -/
theorem deviatedTurnProfile_firstTurn_eq_blockPlayers
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy) :
    deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) profile who deviation =
      blockPlayers bound turns profile who deviation (fun _ => none) := by
  funext player
  by_cases same : player = who
  · subst same
    simp only [deviatedTurnProfile, blockPlayers, Function.update_self]
  · simp only [deviatedTurnProfile, blockPlayers, Function.update_of_ne same]
    exact (assignedTurnPolicy_empty bound turns profile player).symm

/-- At a block's start, no other player has had a turn at, or submitted for, a
block event. -/
theorem blockMarks_start (who : Player) {low high : Nat}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (untouched : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      Untouched setup leaks event execution)
    (own : ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks execution owner) :
    blockMarks who low high execution = fun _ _ => (0, false) := by
  funext owner event
  unfold blockMarks
  split_ifs with inside
  · obtain ⟨honest, lower, _⟩ := inside
    have turns : ownerTurns owner event execution = 0 := by
      unfold ownerTurns
      rw [List.countP_eq_zero]
      intro entry member turn
      exact untouched event lower owner entry member
        (PublicView.ownTurn?_spec _ owner event (of_decide_eq_true turn)).1
    have recorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (execution.recall owner) event = false := by
      apply Bool.eq_false_of_not_eq_true
      intro recorded
      obtain ⟨entry, member, submitted⟩ := List.any_eq_true.mp recorded
      exact untouched event lower owner entry member
        (PublicView.ownTurn?_spec _ owner event
          (own owner honest entry member event (of_decide_eq_true submitted))).1
    rw [turns, recorded]
  · rfl

/-- **One deviating player through a block of commitments.** On a
reveal-relaxed graph, under the asynchronous contract with
`delay + bound < deadline`, against the first-turn clients of a source profile
one player follows an arbitrary native policy. From completion boundaries at
the start `low` of a block of bindings ending at a public event or at the end
of the graph, the run until the block is done has, jointly with the deviator's
traffic, the decoded law of the block's commitments in which every other owner
follows its source kernel and the deviator follows behavioral kernels; the
deviator's traffic again factors through its new source view. -/
theorem asyncDeviation_block_factorization
    (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {low high : Nat} (wall : BlockEnd setup mode high) {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (bindings : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < high →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    {Γ : SourceCtx Player L} {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (count : Nat) (prefixed : CommitPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (highEq : low + count = high)
    {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile program profile refs
      (source seed).revelations (source seed).registry embedding refsBefore low)
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs low
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile who
        deviation) low (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : DecisionView who Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view who)).map fun extra => (config, extra)) :
    ∃ policy : BehavioralPolicy who program,
      ∃ nextNoise : DecisionView who (commitTail count program prefixed).context → PMF _,
        (prior.bind fun seed =>
          ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
            (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile who
              deviation) (BlockDone high) horizon (execution seed)).map fun final =>
            (decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
              embedding.ref count final.application.config.store
              (decodeHistory setup.program (final.application.config.history.map
                (setup.eventGraph.fromModeCompletion mode))),
              (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
        ((prior.map source).bind (kernelChain who count program profile policy
          prefixed)).bind fun config =>
          (nextNoise (config.view who)).map fun extra =>
            (some ((commitTail count program prefixed).lift
              (ProtocolState.entry _ config)), extra) := by
  let app := serviceApplication setup mode deadline leaks
  have lowHigh : low ≤ high := by omega
  let traffic := (serviceRuntime setup mode deadline).bindingTraffic leaks who
  let choicesOf := fun view : PlayerView (serviceGraph setup mode) =>
    deviatorChoices setup mode (· ≠ who) who count program prefixed embedding view.observation.store
  let decided := fun (seed : Seed) (drawn : Assignment setup mode) =>
    app.runUntilHorizon scheduler (blockPlayers bound turns wholeProfile who deviation drawn)
      (BlockDone high) horizon (execution seed)
  -- Facts at the block's start.
  have startFacts (seed : Seed) (supported : seed ∈ prior.support) :
      Nonempty ((app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨horizon - (execution seed).environmentRecall.length, none, execution seed⟩)) ∧
      (∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks (execution seed) owner ∧
        CanonicalSlotsUsed setup leaks (execution seed) owner) ∧
      ActivationsAnswered setup leaks (execution seed) := by
    refine ⟨app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler _ _
      (bounded seed supported) _ (boundary seed supported).supported, fun owner honest => ?_,
      roundsFrom_activationsAnswered _ _ (boundary seed supported).supported⟩
    exact canonicalSlots_roundsFrom scheduler _ owner (bound := bound)
      (firstTurnTiming setup turns mode) wholeProfile
      (by simp only [deviatedTurnProfile, Function.update_of_ne honest]) _ _
      (boundary seed supported).supported
  -- Block events are the embedded leading commitments.
  have embedded (event : (serviceGraph setup mode).EventId) (lower : low ≤ event.val)
      (upper : event.val < high) (seed : Seed) :
      ∃ index : Fin (eventCount program), index.val < count ∧ embedding.event index = event := by
    have within := prefixed.le_eventCount
    have below : event.val - low < count := by omega
    refine ⟨⟨event.val - low, Nat.lt_of_lt_of_le below within⟩, below, ?_⟩
    apply Fin.ext
    rw [(aligned seed).graphSuffix.rankEq]
    simp only
    omega
  -- Every drawn assignment assigns every block event of every other owner.
  have drawnAssigns (seed : Seed) (drawn : Assignment setup mode)
      (member : drawn ∈ (assignChain setup mode (· ≠ who) count program profile prefixed embedding
        (source seed) (fun _ => none)).support) :
      ∀ event owner, low ≤ event.val → event.val < high →
        (serviceGraph setup mode).actor? event = some owner → owner ≠ who →
          ∃ action, drawn event = some action := by
    intro event owner lower upper owned honest
    obtain ⟨index, below, rfl⟩ := embedded event lower upper seed
    exact assignChain_support_assigns (· ≠ who) count program profile prefixed embedding _ _ drawn
      member index owner below owned honest
  -- The decided runs: their outcomes and their deviator readouts.
  have decidedFacts (seed : Seed) (supported : seed ∈ prior.support)
      (drawn : Assignment setup mode)
      (member : drawn ∈ (assignChain setup mode (· ≠ who) count program profile prefixed embedding
        (source seed) (fun _ => none)).support)
      (final : app.Execution) (reached : final ∈ (decided seed drawn).support) :
      decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
          embedding.ref count final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode))) =
        some ((commitTail count program prefixed).lift (ProtocolState.entry _
          (assembleChain setup mode (· ≠ who) count program prefixed embedding (source seed) drawn
            (choicesOf (traffic final).2.2.2.2.1)))) := by
    obtain ⟨⟨trace⟩, ownSlots, answered⟩ := startFacts seed supported
    have start := boundary seed supported
    have done := runUntil_blockDone_of_trace _ contract.completes high _ _ final trace reached
    have reach := runUntil_configReaches scheduler _ _ _ _ final reached
    have inside := runUntil_within (BlockEnd.sealed_relaxed relaxed wall
        (plain_of_bindings bindings))
      scheduler _ _ _ final
      (start.withinBlock lowHigh)
      reached
    have finalPrefix : final.application.config.cut.IsPrefix high :=
      inside.within.isPrefix wall.1 done
    refine blockDecode relaxed (· ≠ who) who (fun _ undrawn => not_not.mp undrawn)
      wholeProfile (execution seed).application.config
      final.application.config reach start.ordered finalPrefix bindings drawn ?_ count program
      profile prefixed refs embedding refsBefore low (source seed) (aligned seed)
      (execution seed).application.config (checkpoint seed) Relation.ReflTransGen.refl
      (fun completion member notStart =>
          (notStart ((execution seed).application.config.history_exact
        _ |>.mp (List.mem_map_of_mem member))).elim) le_rfl (by omega)
    intro event owner lower upper owned honest
    obtain ⟨action, assigned⟩ := drawnAssigns seed drawn member event owner lower upper owned
      honest
    obtain ⟨nodeOwner, nodePayload, nodeEq, nodeCode, _⟩ := bindings event lower upper
    have ownerIs : nodeOwner = owner := Option.some.inj
      ((nodeView_bind_actor nodeEq nodeCode).symm.trans owned)
    subst ownerIs
    have facts := binding_decision_facts nodeEq action
    have phase := DecidedEventPhase.runUntil contract timely facts.1 facts.2.1 facts.2.2.1
      (start.untouched event lower)
      (players := blockPlayers bound turns wholeProfile who deviation drawn)
      (by
        simp only [blockPlayers, Function.update_of_ne honest]
        exact assignedTurnPolicy_decidesAt bound turns wholeProfile nodeOwner drawn event action
          assigned)
      (by
        simp only [blockPlayers, Function.update_of_ne honest]
        exact assignedTurnPolicy_submitsAtTurn bound turns wholeProfile nodeOwner drawn)
      (BlockDone high) _ 0 _ (by simpa only [Nat.zero_add] using trace)
      (DecidedEventPhase.initial bound action (start.untouched event lower)
        (ownSlots nodeOwner honest).1
        (fun completed => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le
          ((start.ordered.2 event).mp completed) lower)))
      (ownSlots nodeOwner honest).1 answered final reached
    exact ⟨action, assigned, phase.binding_completed nodeEq (done event upper)⟩
  -- The law of the deviator's choices and traffic is the same for every draw.
  have congruent (left : Seed) (leftSupported : left ∈ prior.support)
      (right : Seed) (rightSupported : right ∈ prior.support)
      (same : traffic (execution left) = traffic (execution right))
      (leftDrawn : Assignment setup mode)
      (leftMember : leftDrawn ∈ (assignChain setup mode (· ≠ who) count program profile prefixed
        embedding (source left) (fun _ => none)).support)
      (rightDrawn : Assignment setup mode)
      (rightMember : rightDrawn ∈ (assignChain setup mode (· ≠ who) count program profile prefixed
        embedding (source right) (fun _ => none)).support) :
      (decided left leftDrawn).map (blockReadout who low high) =
        (decided right rightDrawn).map (blockReadout who low high) := by
    obtain ⟨⟨leftTrace⟩, leftOwn, _⟩ := startFacts left leftSupported
    obtain ⟨⟨rightTrace⟩, rightOwn, _⟩ := startFacts right rightSupported
    have counts : horizon - (execution left).environmentRecall.length =
        horizon - (execution right).environmentRecall.length := by
      rw [show (execution left).environmentRecall = (execution right).environmentRecall from
        congrArg (fun value => value.2.2.1) same]
    unfold decided ReactiveApplication.runUntilHorizon
    rw [counts]
    apply decidedBlock_readout_congr
      (BlockEnd.sealed_relaxed relaxed wall
          (plain_of_bindings bindings)) scheduler bound turns wholeProfile who deviation
      bindings leftDrawn rightDrawn (drawnAssigns left leftDrawn leftMember)
      (drawnAssigns right rightDrawn rightMember)
    · exact ⟨⟨0, ⟨by rw [Nat.zero_add, ← counts]; exact leftTrace⟩⟩,
        (boundary left leftSupported).withinBlock lowHigh,
        fun owner honest => (leftOwn owner honest).1, fun owner honest => (leftOwn owner honest).2⟩
    · exact ⟨⟨0, ⟨by rw [Nat.zero_add]; exact rightTrace⟩⟩,
        (boundary right rightSupported).withinBlock lowHigh,
        fun owner honest => (rightOwn owner honest).1,
        fun owner honest => (rightOwn owner honest).2⟩
    · refine Prod.ext same ?_
      change blockMarks who low high (execution left) = blockMarks who low high (execution right)
      rw [blockMarks_start who (boundary left leftSupported).untouched
          (fun owner honest => (leftOwn owner honest).1),
        blockMarks_start who (boundary right rightSupported).untouched
          (fun owner honest => (rightOwn owner honest).1)]
  -- A reference draw for each seed.
  have drawExists (seed : Seed) : ∃ drawn, drawn ∈ (assignChain setup mode (· ≠ who) count program
      profile prefixed embedding (source seed) (fun _ => none)).support :=
    (assignChain setup mode (· ≠ who) count program profile prefixed embedding (source seed)
      (fun _ => none)).support_nonempty
  let reference := fun seed : Seed => (drawExists seed).choose
  let outcome := fun seed : Seed => (decided seed (reference seed)).map fun final =>
    (choicesOf (traffic final).2.2.2.2.1, traffic final)
  have outcomeEq (seed : Seed) (supported : seed ∈ prior.support) (drawn : Assignment setup mode)
      (member : drawn ∈ (assignChain setup mode (· ≠ who) count program profile prefixed embedding
        (source seed) (fun _ => none)).support) :
      (decided seed drawn).map (fun final => (choicesOf (traffic final).2.2.2.2.1, traffic final)) =
        outcome seed := by
    have readoutEq := congruent seed supported seed supported rfl drawn member (reference seed)
      (drawExists seed).choose_spec
    have projected := congrArg (PMF.map fun read => (choicesOf read.1.2.2.2.2.1, read.1)) readoutEq
    simp only [PMF.map_comp] at projected
    exact projected
  -- The native law of one seed.
  have native (seed : Seed) (supported : seed ∈ prior.support) :
      (app.runUntilHorizon scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) wholeProfile who
          deviation) (BlockDone high) horizon (execution seed)).map (fun final =>
            (decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
              embedding.ref count final.application.config.store
              (decodeHistory setup.program (final.application.config.history.map
                (setup.eventGraph.fromModeCompletion mode))), traffic final)) =
        (outcome seed).bind fun pair =>
          (listChain (· ≠ who) count program profile prefixed
              (source seed) pair.1).map fun config =>
            (some ((commitTail count program prefixed).lift (ProtocolState.entry _ config)),
              pair.2) := by
    obtain ⟨⟨trace⟩, ownSlots, answered⟩ := startFacts seed supported
    have start := boundary seed supported
    have predraw := blockPlayers_runUntil_predraw relaxed wall contract timely turns wholeProfile
      who deviation (execution seed) start.ordered start.untouched
      (fun owner honest => (ownSlots owner honest).1) answered bindings count program profile
      prefixed refs embedding refsBefore low (source seed) (aligned seed)
      (execution seed).application.config (checkpoint seed) Relation.ReflTransGen.refl le_rfl
      (by omega) (fun _ => none) (fun _ _ none => by cases none)
      (fun event _ lower upper => by omega) _ 0 (by simpa only [Nat.zero_add] using trace)
    unfold ReactiveApplication.runUntilHorizon
    rw [deviatedTurnProfile_firstTurn_eq_blockPlayers, predraw, PMF.map_bind]
    calc
      _ = (assignChain setup mode (· ≠ who) count program profile prefixed embedding (source seed)
            (fun _ => none)).bind fun drawn =>
            (outcome seed).map fun pair =>
              (some ((commitTail count program prefixed).lift (ProtocolState.entry _
                (assembleChain setup mode (· ≠ who) count program prefixed embedding (source seed)
                  drawn pair.1))), pair.2) := by
        apply bind_congr_on_support _
        intro drawn member
        rw [← outcomeEq seed supported drawn member, PMF.map_comp]
        apply map_congr_on_support _
        intro final reached
        exact Prod.ext (decidedFacts seed supported drawn member final reached) rfl
      _ = (outcome seed).bind fun pair =>
            ((assignChain setup mode (· ≠ who) count program profile prefixed embedding
                (source seed)
              (fun _ => none)).map fun drawn => assembleChain setup mode (· ≠ who) count program
                prefixed embedding (source seed) drawn pair.1).map fun config =>
              (some ((commitTail count program prefixed).lift (ProtocolState.entry _ config)),
                pair.2) := by
        simp only [← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
        exact PMF.bind_comm _ _ _
      _ = _ := by
        apply bind_congr_on_support _
        intro pair _
        rw [assignChain_assemble (· ≠ who) count program profile prefixed embedding (source seed)
          (source seed) (fun _ => none) pair.1 (fun _ _ => rfl)]
  -- The deviator's behavioral kernels.
  obtain ⟨policy, nextNoise, law⟩ := listChain_factorization who count program profile prefixed
    prior source (fun seed => traffic (execution seed)) noise factor outcome
    (fun left leftSupported right rightSupported same => by
      have readoutEq := congruent left leftSupported right rightSupported same (reference left)
        (drawExists left).choose_spec (reference right) (drawExists right).choose_spec
      have projected := congrArg (PMF.map fun read => (choicesOf read.1.2.2.2.2.1, read.1))
          readoutEq
      simp only [PMF.map_comp] at projected
      exact projected)
  refine ⟨policy, nextNoise, ?_⟩
  have mapped := congrArg (PMF.map fun pair : Config Player L _ × _ =>
    ((some ((commitTail count program prefixed).lift (ProtocolState.entry _ pair.1)) :
      Option (ProtocolState program)), pair.2)) law
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
  calc
    _ = prior.bind fun seed => (outcome seed).bind fun pair =>
          (listChain (· ≠ who) count program profile prefixed
              (source seed) pair.1).map fun config =>
            (some ((commitTail count program prefixed).lift (ProtocolState.entry _ config)),
              pair.2) := bind_congr_on_support _ native
    _ = _ := mapped

end Vegas
