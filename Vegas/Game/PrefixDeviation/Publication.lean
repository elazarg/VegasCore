module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheory.Math.Probability.ExpectationConditioning
public import Vegas.Game.IntendedPrefixContinuation
public import Vegas.Game.NativeForfeitContinuation
public import Vegas.Game.PrefixDeviation.Boundary
public import Vegas.Game.PublicationSurvival
public import Vegas.Game.ServiceObservation
public import Vegas.Game.SourceStateKernel

@[expose] public section

/-! # Continuation bounds across a publication interval -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private def representativeRevealTail
    {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}
    {rank : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup profile rank origin)
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ frame.Γ.map Prod.fst)
    (selected : HasVar frame.Γ name (.commitment owner payload)) (unresolved : name ∈ frame.names)
    (next : SourceProgram Player L ((published, .publication payload) :: frame.Γ)
      (frame.names.erase name))
    (programEq : frame.program = .reveal published owner name fresh selected unresolved next) :
    let embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (.reveal published owner name fresh selected unresolved next) := programEq ▸ frame.embedding
    let index : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : setup.informationGraph.outputLayout (embedding.event index) =
        .publication payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    let atRank : (embedding.event index).val = rank := by
      rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
        aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
        transport, checkpoint⟩
      dsimp only at fresh selected unresolved next programEq ⊢
      cases programEq
      simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
    let ready : origin.cut.Ready (embedding.event index) := by
      have ordered := frame.checkpoint.ordered
      rw [← atRank] at ordered
      exact ordered.ready (embedding.event index).isLt
    SourceResidual setup profile (rank + 1)
      (origin.complete (embedding.event index) ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (disclosureResult published selected frame.source true))) := by
  rcases frame with ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore,
    aligned, admitted, authentic, supports, disclosing, lift, commutes, steps, injective,
    transport, checkpoint⟩
  dsimp only at fresh selected unresolved next programEq ⊢
  cases programEq
  let index : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
    ⟨0, by simp [eventCount]⟩
  have outputEq : setup.informationGraph.outputLayout (embedding.event index) =
      .publication payload := by
    change outputLayout setup.program (embedding.event index) = _
    simpa [index, outputLayout, eventCount] using embedding.layout_eq index
  have atRank : (embedding.event index).val = rank := by
    simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have ready : origin.cut.Ready (embedding.event index) := by
    have ordered := checkpoint.ordered
    rw [← atRank] at ordered
    exact ordered.ready (embedding.event index).isLt
  have decoded : decodeEventAction setup.program (embedding.event index)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) =
        some (.reveal owner name true) := by
    have lookup := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
    simpa [index, outputEq, decodeEventAction] using lookup
  let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
  let tailRefs : ContextRefs (graphLayout setup.program)
      ((published, .publication payload) :: Γ) :=
    refs.cons ⟨.inr (embedding.event index), outputEq⟩
  have tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
    refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl
  have tailAligned : CompiledPolicySuffix setup.program profile next
      (afterReveal residualProfile) tailRefs
      (revealSuccessor published selected source true).revelations
      (revealSuccessor published selected source true).registry
      tailEmbedding tailBefore (rank + 1) := by
    simpa only [revealSuccessor, tailRefs, tailEmbedding, OutputEmbedding.ref] using
      aligned.revealTail setup.program profile fresh selected unresolved next
        residualProfile refs source.revelations source.registry embedding refsBefore rank
  refine {
    Γ := _, names := _, program := next, residualProfile := afterReveal residualProfile,
    source := revealSuccessor published selected source true, refs := tailRefs,
    embedding := tailEmbedding, refsBefore := tailBefore, aligned := tailAligned,
    admitted := fun whole who => admitted whole who,
    authentic := fun whole who => (authentic whole who).2,
    supports := fun whole who => (supports whole who).2,
    disclosing := fun whole who => (disclosing whole who).2,
    lift := lift ∘ Sum.inr,
    commutes := fun state => ?_, steps := fun state joint => ?_,
    injective := injective.comp Sum.inr_injective,
    transport := fun more store history defaults => ?_,
    checkpoint := checkpoint.reveal (native := origin) published selected
      (embedding.event index) atRank ready outputEq (fun ref => refsBefore ref index) true decoded }
  · rw [Function.comp_apply, commutes, ProtocolState.behavioralStateStep_reveal_tail,
      PMF.map_comp]
  · rw [Function.comp_apply, steps]
    change PMF.map lift ((ProtocolState.step next state joint).map Sum.inr) = _
    rw [PMF.map_comp]
  · rw [show rank + 1 + more = rank + (more + 1) by omega, transport,
      decodeSourcePrefix?_reveal, Option.map_map]
    rfl

end Vegas

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem exists_reveal_prefix_source_frame
    {setup : Setup (Player := Player) (L := L)} [Finite Player]
    (wellFormed : setup.WellFormed)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who)) :
    ∀ (count rank : Nat) (origin : setup.informationGraph.Config)
      (frame : SourceResidual setup (setup.decodeBehavioralProfile
        (CommitmentInterface.forfeiture setup.program) target) rank origin),
      frame.refs.CoversPrefix setup.program rank →
      rank + count ≤ setup.informationGraph.order.eventCount →
      (∀ event : setup.informationGraph.EventId, rank ≤ event.val →
        event.val < rank + count → (setup.informationGraph.outputLayout event).IsPublication) →
    ∃ (endOrigin : setup.informationGraph.Config)
      (tail : SourceResidual setup (setup.decodeBehavioralProfile
        (CommitmentInterface.forfeiture setup.program) target) (rank + count) endOrigin),
      tail.refs.CoversPrefix setup.program (rank + count) ∧
      eventCount frame.program = count + eventCount tail.program ∧
      ∀ (source : Config Player L frame.Γ),
        @source.revelations = @frame.source.revelations →
        source.registry = frame.source.registry →
      ∀ (ghost : setup.informationGraph.Config),
        SourceCheckpoint setup source frame.refs rank ghost →
      ∀ (inputs : setup.informationGraph.Inputs), ghost.Reachable inputs →
      ∀ (history : setup.intendedProtocol.History),
        history.state = some (frame.lift (ProtocolState.entry frame.program source)) →
      ∃ (nextSource : Config Player L tail.Γ) (nextGhost : setup.informationGraph.Config),
        @nextSource.revelations = @tail.source.revelations ∧
        nextSource.registry = tail.source.registry ∧
        SourceCheckpoint setup nextSource tail.refs (rank + count) nextGhost ∧
        nextGhost.Reachable inputs ∧
        (∃ nextHistory : setup.intendedProtocol.History,
          nextHistory.state = some (tail.lift (ProtocolState.entry tail.program nextSource))) ∧
        setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan
            (compilePrescribedProfile setup.program setup.informationDependencies
              (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target))
            setup.informationGraph.canonicalScheduler) count ghost = PMF.pure nextGhost := by
  classical
  let _ := Fintype.ofFinite Player
  intro count
  induction count with
  | zero =>
      intro rank origin frame covered bounded publications
      refine ⟨origin, by simpa using frame, ?_⟩
      simp only [Nat.add_zero, Nat.zero_add]
      refine ⟨covered, rfl, ?_⟩
      intro source revelations registry ghost checkpoint inputs reachable history historyAt
      exact ⟨source, ghost, revelations, registry, checkpoint, reachable,
        ⟨history, historyAt⟩, rfl⟩
  | succ count ih =>
      intro rank origin frame covered bounded publications
      rcases frame with ⟨Γ, names, program, residualProfile, original, refs, embedding,
        refsBefore, aligned, admitted, authentic, supports, opens, lift, commutes, steps,
        injective, transport, originalCheckpoint⟩
      have counted := aligned.graphSuffix.countEq
      change rank + eventCount program = setup.informationGraph.order.eventCount at counted
      cases program with
      | ret payoffs =>
          simp only [eventCount] at counted
          omega
      | @sample Γ names name payload fresh law next =>
          let index : Fin (eventCount (.sample name fresh law next)) := ⟨0, by simp [eventCount]⟩
          have atRank : (embedding.event index).val = rank := by
            simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have publication := publications (embedding.event index) atRank.symm.le (by omega)
          have layout : setup.informationGraph.outputLayout (embedding.event index) =
              .publicData payload := (embedding.layout_eq index).trans rfl
          rw [layout] at publication
          exact publication.elim
      | @commit Γ names name owner payload fresh guard next =>
          let index : Fin (eventCount (.commit name owner fresh guard next)) :=
            ⟨0, by simp [eventCount]⟩
          have atRank : (embedding.event index).val = rank := by
            simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have publication := publications (embedding.event index) atRank.symm.le (by omega)
          have layout : setup.informationGraph.outputLayout (embedding.event index) =
              .binding owner payload := (embedding.layout_eq index).trans rfl
          rw [layout] at publication
          exact publication.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          let frame : SourceResidual setup (setup.decodeBehavioralProfile
              (CommitmentInterface.forfeiture setup.program) target) rank origin :=
            ⟨Γ, names, .reveal published owner name fresh selected unresolved next, residualProfile,
              original, refs, embedding, refsBefore, aligned, admitted, authentic, supports,
              opens,
              lift, commutes, steps, injective, transport, originalCheckpoint⟩
          let index : Fin (eventCount
              (.reveal published owner name fresh selected unresolved next)) :=
            ⟨0, by simp [eventCount]⟩
          let event := embedding.event index
          have atRank : event.val = rank := by
            simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have outputEq : setup.informationGraph.outputLayout event = .publication payload :=
            (embedding.layout_eq index).trans rfl
          have decoded : decodeEventAction setup.program event
              (cast (congrArg EventField.Action outputEq.symm) true) =
                some (.reveal owner name true) := by
            simpa [index, event, outputEq, decodeEventAction] using aligned.actionEq index
              (cast (congrArg EventField.Action outputEq.symm) true)
          let head := representativeRevealTail frame fresh selected unresolved next rfl
          have headCovered : head.refs.CoversPrefix setup.program (rank + 1) :=
            covered.cons setup.program (name := published) (cell := .publication payload)
              ⟨.inr event, outputEq⟩ event rfl atRank
          obtain ⟨endOrigin, tail, tailCovered, tailCount, advance⟩ := ih (rank + 1) _ head
            headCovered (by omega) (fun node lower upper => publications node (by omega) (by omega))
          have rankEq : rank + 1 + count = rank + (count + 1) := by omega
          rw [← rankEq]
          refine ⟨endOrigin, tail, tailCovered, ?_, ?_⟩
          · change eventCount (.reveal published owner name fresh selected unresolved next) = _
            change eventCount next = count + eventCount tail.program at tailCount
            simp only [eventCount]
            omega
          · intro source revelations registry ghost checkpoint inputs reachable history historyAt
            have ready : ghost.cut.Ready event := by
              have ordered := checkpoint.ordered
              rw [← atRank] at ordered
              exact ordered.ready event.isLt
            let actual := residualAt frame source revelations registry ghost checkpoint
            have atGhost : history.state = sourceServicePrefix? setup rank ghost :=
              historyAt.trans actual.decode.symm
            have clear := actual.clear_of_intended_history wellFormed history atGhost
            have active : owner ∉ ghost.defaulted := by rw [clear]; simp
            have sourceActive : owner ∉ source.defaulted := by
              have status := congrArg DefaultHistory.defaulted checkpoint.defaults
              change ghost.defaulted = source.defaulted at status
              rw [← status]
              exact active
            let sourceAfter := revealSuccessor published selected source true
            let ghostAfter := ghost.complete event ready
              (cast (congrArg EventField.Action outputEq.symm) true)
              (cast (congrArg EventField.Value outputEq.symm)
                (disclosureResult published selected source true))
            have nextCheckpoint : SourceCheckpoint setup sourceAfter head.refs (rank + 1)
                ghostAfter := checkpoint.reveal (native := ghost) published selected
              event atRank ready outputEq (fun ref => refsBefore ref index) true decoded
            have codeEq : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
                (setup.informationGraph.nodes event) = .resolve owner payload (refs.get selected)
                  (compileChecks (published := published) refs source.registry source.revelations
                    selected) := by
              rw [revelations, registry]
              simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
            have status : ghost.defaulted = source.defaulted :=
              congrArg DefaultHistory.defaulted checkpoint.defaults
            have stepLaw : ghost.step event ready
                (cast (congrArg EventField.Action outputEq.symm) true) = PMF.pure ghostAfter := by
              simpa only [ghostAfter, status, disclosureResult, revealSuccessor, Env.get,
                Env.cons] using
                reveal_step ghost event ready outputEq refs source.revelations source.registry
                  selected codeEq source.state checkpoint.agrees true
            have graphStep : ghostAfter ∈ (ghost.step event ready
                (cast (congrArg EventField.Action outputEq.symm) true)).support := by
              rw [stepLaw]
              exact (PMF.mem_support_pure_iff _ _).mpr rfl
            have afterReach : ghostAfter.Reachable inputs :=
              Config.Step.path_reachable (.single ⟨event, ready, _, graphStep⟩) reachable
            have residualOpens := actual.disclosing disclosing owner
            have kernel : revealKernel residualProfile (source.view owner) sourceActive =
                PMF.pure true := eq_pure_true_of_false_not_mem
                  (residualOpens.1 rfl (source.view owner) sourceActive)
            have sourceStep : Sum.inr (ProtocolState.entry next sourceAfter) ∈
                (ProtocolState.behavioralStateStep
                  (.reveal published owner name fresh selected unresolved next) residualProfile
                  (.inl source)).support := by
              have activeView : owner ∉ (source.view owner).defaulted := sourceActive
              rw [ProtocolState.behavioralStateStep_reveal_entry, dite_eq_right activeView,
                kernel, PMF.pure_map]
              exact (PMF.mem_support_pure_iff _ _).mpr rfl
            obtain ⟨nextHistory, nextHistoryAt⟩ := actual.intendedHistory_of_step intended target
              agrees history atGhost _ sourceStep
            have afterRevelations : @sourceAfter.revelations = @head.source.revelations := by
              change @(revealSuccessor published selected source true).revelations =
                @(revealSuccessor published selected original true).revelations
              simp only [revealSuccessor_revelations, revelations]
            have afterRegistry : sourceAfter.registry = head.source.registry := by
              change source.registry.weaken = original.registry.weaken
              rw [registry]
            obtain ⟨finalSource, finalGhost, finalRevelations, finalRegistry, finalCheckpoint,
              finalReach, finalHistory, finalLaw⟩ := advance sourceAfter afterRevelations
                afterRegistry ghostAfter nextCheckpoint inputs afterReach nextHistory nextHistoryAt
            refine ⟨finalSource, finalGhost, finalRevelations, finalRegistry,
              finalCheckpoint, finalReach, finalHistory, ?_⟩
            have actor : setup.informationGraph.actor? event = some owner := by
              have law := (decodeEventAction_owner setup.program event
                (cast (congrArg EventField.Action outputEq.symm) true)).symm
              rw [eventOwner?_eq_actor] at law
              simpa [decoded, sourceActionOwner] using law
            have least : ∀ other, other ∉ ghost.cut.completed → event.val ≤ other.val := by
              intro other missing
              rw [atRank]
              exact Nat.le_of_not_gt fun lower =>
                missing ((checkpoint.ordered.2 other).mpr lower)
            rw [runPlan_canonical_actor _ count ghost event ready least owner actor active,
              compilePrescribedProfile_publication setup.program setup.informationDependencies _
                disclosing owner event actor (by rw [outputEq]; trivial),
              EventGraphRuntime.openAction_eq_cast_true outputEq, PMF.pure_bind, stepLaw,
              PMF.pure_bind]
            exact finalLaw

end Vegas

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

private theorem publication_surviving_endpoint_boundary
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile reference : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} (run : RevealRun (serviceGraph setup deps) start finish)
    (origin : (serviceApplication setup deps duration leaks).Execution)
    (boundary : PhaseBoundary scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      horizon start origin)
    (donor : (serviceGraph setup deps).Config) (ordered : donor.cut.IsPrefix finish)
    (law : outcomeDistribution profile Config.defaulted donor = PMF.pure ∅)
    (potential : canonicalDistribution profile origin.application.config = canonicalDistribution
      profile donor)
    (final : (serviceApplication setup deps duration leaks).Execution)
    (reached : final ∈ ((serviceApplication setup deps duration leaks).runUntilHorizon scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      (fun current => BlockDone finish current.application.config) horizon origin).support)
    (survived : focal ∉ final.application.config.defaulted) :
    CompletionBoundary setup leaks scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation)
      finish final ∧ final.environmentRecall.length ≤ horizon ∧
      runKey final.application.config = runKey donor := by
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
    (firstTurnTiming setup turns deps) (effectiveOpening reference)) focal deviation
  obtain ⟨_finalClear, key⟩ := publication_surviving_endpoint_key scheduler bound relaxed contract
    timely profile reference independent opens focal deviation run origin boundary donor ordered
    law potential final reached survived
  have finalOrdered : final.application.config.cut.IsPrefix finish := by
    have cuts : final.application.config.cut = donor.cut := congrArg Prod.fst key
    rw [cuts]
    exact ordered
  obtain ⟨finalSupport, finalBound⟩ := runUntilHorizon_bounded boundary.supported boundary.bounded
    reached
  have originLaw : outcomeDistribution profile Config.defaulted origin.application.config =
    PMF.pure ∅ :=
    (outcomeDistribution_eq_of_canonicalDistribution_eq Config.defaulted
      (fun _ _ equal => defaulted_eq_of_completionOf_eq (congrArg (fun key => key.2.2) equal))
      potential).trans law
  have originClear := defaulted_eq_empty_of_outcomeDistribution profile _ originLaw
  have originInside : InBlock start finish origin.application.config := by
    refine ⟨boundary.earlier, ?_⟩
    intro event later completed
    obtain ⟨_record, _value, owner, _owned, inactive⟩ :=
      boundary.later event (by have := run.nonempty; omega) completed
    rw [originClear] at inactive
    simp at inactive
  have untouched := blockRun_untouched (run.shaped relaxed) scheduler players
    (fun current => BlockDone finish current.application.config) (fun _ done => done)
    (horizon - origin.environmentRecall.length) origin final originInside
    (fun event later => boundary.seen.untouched
      (show ¬ event.val < start by have := run.nonempty; omega)) reached
  exact ⟨⟨finalSupport, finalOrdered, untouched⟩, finalBound, key⟩

private theorem publication_surviving_phase_posterior
    {Seed Source View Next NextView : Type} {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (reference : Seed → (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} (run : RevealRun (serviceGraph setup deps) start finish)
    (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (advance : Source → Next) (nextView : Next → NextView)
    (donor : Next → (serviceGraph setup deps).Config)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (noise : View → PMF (MessageNetwork Player
        (serviceApplication setup deps duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup deps duration leaks).EnvironmentEntry ×
      List (serviceApplication setup deps duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps)))
    (factor : prior.map (fun seed => (source seed,
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map source).bind fun current =>
        (noise (observe current)).map fun extra => (current, extra))
    (boundary : ∀ seed ∈ prior.support, PhaseBoundary scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening (reference seed))) focal deviation)
      horizon start (execution seed))
    (reachable : ∀ seed ∈ prior.support,
      ∃ inputs, (donor (advance (source seed))).Reachable inputs)
    (ordered : ∀ seed ∈ prior.support, (donor (advance (source seed))).cut.IsPrefix finish)
    (defaultLaw : ∀ seed ∈ prior.support,
      outcomeDistribution profile Config.defaulted (donor (advance (source seed))) = PMF.pure ∅)
    (potential : ∀ seed ∈ prior.support,
      canonicalDistribution profile (execution seed).application.config =
        canonicalDistribution profile (donor (advance (source seed))))
    (reflects : ∀ left ∈ (prior.map source).support, ∀ right ∈ (prior.map source).support,
      nextView (advance left) = nextView (advance right) → observe left = observe right)
    (visible : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      nextView (advance (source left)) = nextView (advance (source right)) →
      keyView focal (runKey (donor (advance (source left)))) =
        keyView focal (runKey (donor (advance (source right))))) :
    let app := serviceApplication setup deps duration leaks
    let players := fun seed => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening (reference seed))) focal deviation
    let phase := fun seed => app.runUntilHorizon scheduler (players seed)
      (fun current => BlockDone finish current.application.config) horizon (execution seed)
    let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
    let good := fun entry : Seed × app.Execution => decide (focal ∉
      entry.2.application.config.defaulted)
    ∀ _present : true ∈ (staged.map good).support,
    let accepted := fiberPosterior staged good true
    ∃ nextNoise : NextView → PMF (MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps)),
      (accepted.map (fun entry => (advance (source entry.1),
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal entry.2))) =
        ((accepted.map (fun entry => advance (source entry.1))).bind fun current =>
          (nextNoise (nextView current)).map fun observed => (current, observed)) ∧
      ∀ entry ∈ accepted.support,
        CompletionBoundary setup leaks scheduler (players entry.1) finish entry.2 ∧
          entry.2.environmentRecall.length ≤ horizon ∧
          runKey entry.2.application.config = runKey (donor (advance (source entry.1))) := by
  classical
  intro app players phase staged good present accepted
  let traffic := (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
  obtain ⟨optionalNoise, optionalLaw⟩ := publication_surviving_joint
    (setup := setup) (deps := deps) (duration := duration) (leaks := leaks)
    (Seed := Seed) (Source := Source) (View := View) (Next := Next) (NextView := NextView)
    scheduler bound relaxed
    contract timely profile reference independent opens focal deviation run prior source observe
    advance nextView donor execution noise factor boundary reachable ordered defaultLaw potential
    reflects visible
  have joint : (staged.map (fun entry => (advance (source entry.1),
      if good entry then some (traffic entry.2) else none))) =
      ((prior.map source).map advance).bind fun current =>
        (optionalNoise (nextView current)).map fun extra => (current, extra) := by
    rw [PMF.map_bind]
    have same : ∀ seed ∈ prior.support,
        (phase seed).map (fun final => (advance (source seed),
          if good (seed, final) then some (traffic final) else none)) =
        (phase seed).map (fun final => (advance (source seed),
          if focal ∈ final.application.config.defaulted then none else some (traffic final))) := by
      intro seed _
      apply map_congr_on_support _
      intro final _
      by_cases failed : focal ∈ final.application.config.defaulted <;>
        simp only [good, failed, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
          not_false_eq_true, decide_true]
    have converted := bind_congr_on_support prior same
    simpa only [staged, phase, players, traffic, PMF.map_bind, PMF.map_comp,
      Function.comp_def] using converted.trans optionalLaw
  have conditional := surviving_channel_posterior staged ((prior.map source).map advance)
    (fun entry => advance (source entry.1)) (fun entry => traffic entry.2) good nextView
      optionalNoise
    (traffic (execution prior.support_nonempty.choose)) joint present
  let goodNoise := fun view : NextView =>
    (fiberPosterior (optionalNoise view) Option.isSome true).map
      (fun extra => extra.getD (traffic (execution prior.support_nonempty.choose)))
  refine ⟨goodNoise, ?_, ?_⟩
  · exact conditional
  intro entry supported
  obtain ⟨selectedGood, stagedSupported⟩ := mem_support_fiberPosterior present supported
  obtain ⟨seed, seedSupported, finalSupported⟩ := (PMF.mem_support_bind_iff _ _ _).mp
    stagedSupported
  obtain ⟨final, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp finalSupported
  cases same
  have survived : focal ∉ final.application.config.defaulted := of_decide_eq_true selectedGood
  exact publication_surviving_endpoint_boundary
    (setup := setup) (deps := deps) (duration := duration) (leaks := leaks)
    scheduler bound relaxed contract timely
    profile (reference seed) independent opens focal deviation run (execution seed)
    (boundary seed seedSupported) (donor (advance (source seed))) (ordered seed seedSupported)
    (defaultLaw seed seedSupported) (potential seed seedSupported) final reached survived

private theorem native_block_expected_comparison
    {Seed Parameter : Type} {horizon turns start finish tailCount : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (reference : setup.informationGraph.BehavioralProfile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (prior : PMF Seed) (members : Seed → (serviceGraph setup deps).BehavioralProfile)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (before after : Seed → setup.informationGraph.Config)
    (lower : start ≤ finish) (bounded : finish ≤ setup.informationGraph.order.eventCount)
    (prefixAt : ∀ seed ∈ prior.support, (before seed).cut.IsPrefix start)
    (headLaw : ∀ seed ∈ prior.support,
      setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
          setup.informationGraph.canonicalScheduler) (finish - start) (before seed) =
        PMF.pure (after seed)) :
    let app := serviceApplication setup deps duration leaks
    let players := fun seed => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps)
          (effectiveOpening ((serviceGraph setup deps).prefixProfile (members seed))))
            focal deviation
    let nativePayoff := fun final : app.Execution => setup.graphForfeitConfigPayoff deps parameter
      utility forfeit final.application.config focal
    let sourcePayoff := setup.graphPayoff setup.informationDependencies parameter utility
      (leastUtility utility) focal
    let phase := fun seed => app.runUntilHorizon scheduler (players seed)
      (fun current => BlockDone finish current.application.config) horizon (execution seed)
    let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
    let good := fun entry : Seed × app.Execution =>
      decide (focal ∉ entry.2.application.config.defaulted)
    (∀ seed ∈ prior.support, PhaseBoundary scheduler (players seed) horizon start
      (execution seed)) →
    (∀ _present : true ∈ (staged.map good).support,
      ∃ policy : setup.informationGraph.BehavioralPolicy focal,
        let accepted := fiberPosterior staged good true
        expect (accepted.bind fun entry => app.runToHorizon scheduler (players entry.1) horizon
          entry.2) nativePayoff ≤
          expect (accepted.bind fun entry => setup.informationGraph.runPlan
            (setup.informationGraph.policyPlan (Function.update
              (setup.informationGraph.prefixProfile reference) focal policy)
              setup.informationGraph.canonicalScheduler) tailCount (after entry.1)) sourcePayoff) →
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (prior.bind fun seed => app.runToHorizon scheduler (players seed) horizon
        (execution seed)) nativePayoff ≤
        expect (prior.bind fun seed => setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan (Function.update
            (setup.informationGraph.prefixProfile reference) focal policy)
            setup.informationGraph.canonicalScheduler) (finish - start + tailCount)
              (before seed)) sourcePayoff := by
  classical
  intro app players nativePayoff sourcePayoff phase staged good boundary continues
  let nativeValue := fun entry : Seed × app.Execution =>
    expect (app.runToHorizon scheduler (players entry.1) horizon entry.2) nativePayoff
  let sourceValue := fun (policy : setup.informationGraph.BehavioralPolicy focal)
      (entry : Seed × app.Execution) => expect (setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) tailCount (after entry.1)) sourcePayoff
  obtain ⟨nativeBound, nativeNonnegative, nativeBounded⟩ :=
    setup.graphForfeitConfigPayoff_abs_bound deps parameter utility range focal
  obtain ⟨sourceBound, sourceNonnegative, sourceBounded⟩ :=
    setup.graphPayoff_abs_bound setup.informationDependencies parameter utility range focal
  have nativePayoffBound : ∀ final : app.Execution, |nativePayoff final| ≤ nativeBound :=
    fun final => nativeBounded final.application.config
  have nativeValueBound : ∀ entry, |nativeValue entry| ≤ nativeBound := by
    intro entry
    exact expect_abs_le_of_bounded nativeNonnegative nativePayoffBound
  have sourceValueBound : ∀ policy entry, |sourceValue policy entry| ≤ sourceBound := by
    intro policy entry
    exact expect_abs_le_of_bounded sourceNonnegative sourceBounded
  have nativeIntegral (law : PMF app.Execution) : PayoffIntegrable law nativePayoff :=
    payoffIntegrable_of_bounded law nativePayoff nativePayoffBound
  have sourceIntegral (law : PMF setup.informationGraph.Config) :
      PayoffIntegrable law sourcePayoff :=
    payoffIntegrable_of_bounded law sourcePayoff sourceBounded
  have nativeTower (law : PMF (Seed × app.Execution)) :
      expect (law.bind fun entry => app.runToHorizon scheduler (players entry.1) horizon entry.2)
        nativePayoff = expect law nativeValue :=
    expect_bind_tower law _ nativePayoff (nativeIntegral _)
  have sourceTower (law : PMF (Seed × app.Execution)) (policy) :
      expect (law.bind fun entry => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler) tailCount (after entry.1)) sourcePayoff =
        expect law (sourceValue policy) := expect_bind_tower law _ sourcePayoff (sourceIntegral _)
  obtain ⟨tailPolicy, tailCompare⟩ : ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      ∀ _present : true ∈ (staged.map good).support,
        expect (fiberPosterior staged good true) nativeValue ≤
          expect (fiberPosterior staged good true) (sourceValue policy) := by
    by_cases present : true ∈ (staged.map good).support
    · obtain ⟨policy, compare⟩ := continues present
      refine ⟨policy, fun _ => ?_⟩
      dsimp only at compare
      rw [nativeTower, sourceTower] at compare
      exact compare
    · exact ⟨(setup.informationGraph.prefixProfile reference) focal,
        fun impossible => (present impossible).elim⟩
  have sourceFloor (entry : Seed × app.Execution) :
      leastUtility utility focal ≤ sourceValue tailPolicy entry := by
    have compare := expect_mono
      (μ := setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal tailPolicy)
          setup.informationGraph.canonicalScheduler) tailCount (after entry.1))
      (f := fun _ => leastUtility utility focal) (g := sourcePayoff)
      (fun config _ => setup.leastUtility_le_graphPayoff setup.informationDependencies parameter
        utility range focal config) (payoffIntegrable_constant _ _) (sourceIntegral _)
    simpa only [expect_constant] using compare
  have stagedSupport (entry : Seed × app.Execution) (member : entry ∈ staged.support) :
      entry.1 ∈ prior.support ∧ entry.2 ∈ (phase entry.1).support := by
    obtain ⟨seed, selected, present⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    obtain ⟨final, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp present
    cases same
    exact ⟨selected, reached⟩
  have compare : expect staged nativeValue ≤ expect staged (sourceValue tailPolicy) := by
    apply expect_fiberwise_le staged good nativeValue (sourceValue tailPolicy)
      (payoffIntegrable_of_bounded staged _ nativeValueBound)
      (payoffIntegrable_of_bounded staged _ (sourceValueBound tailPolicy))
    intro selected possible
    cases selected with
    | true => exact tailCompare possible
    | false =>
        refine expect_mono (fun entry supported => ?_)
          (payoffIntegrable_of_bounded _ _ nativeValueBound)
          (payoffIntegrable_of_bounded _ _ (sourceValueBound tailPolicy))
        obtain ⟨failed, stagedMember⟩ := mem_support_fiberPosterior possible supported
        have defaulted : focal ∈ entry.2.application.config.defaulted := by
          by_contra active
          simp only [good, active] at failed
          cases failed
        obtain ⟨seedSupported, reached⟩ := stagedSupport entry stagedMember
        obtain ⟨currentSupported, currentBound⟩ := runUntilHorizon_bounded
          (boundary entry.1 seedSupported).supported (boundary entry.1 seedSupported).bounded
          reached
        exact (expect_runToHorizon_forfeit_le_of_defaulted scheduler contract (players entry.1)
          parameter utility range focal entry.2 currentSupported currentBound defaulted).trans
          (sourceFloor entry)
  obtain ⟨policy, splice⟩ := exists_canonical_policy_splice
    (setup.informationGraph.prefixProfile reference) focal
    ((setup.informationGraph.prefixProfile reference) focal) tailPolicy start (finish - start)
    tailCount (by omega)
  refine ⟨policy, ?_⟩
  have nativeDistribution : (staged.bind fun entry => app.runToHorizon scheduler
    (players entry.1) horizon
      entry.2) = prior.bind fun seed => app.runToHorizon scheduler (players seed) horizon
        (execution seed) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    apply bind_congr_on_support _
    intro seed _
    exact (app.runToHorizon_eq_runUntilHorizon_bind scheduler (players seed)
      (fun current => BlockDone finish current.application.config) horizon (execution seed)).symm
  have sourceDistribution : (prior.bind fun seed => setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (Function.update
        (setup.informationGraph.prefixProfile reference) focal policy)
        setup.informationGraph.canonicalScheduler) (finish - start + tailCount) (before seed)) =
      staged.bind (fun entry => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal tailPolicy)
          setup.informationGraph.canonicalScheduler) tailCount (after entry.1)) := by
    simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_const]
    apply bind_congr_on_support _
    intro seed supported
    rw [splice (before seed) (prefixAt seed supported), Function.update_eq_self,
      headLaw seed supported, PMF.pure_bind]
  rw [← nativeTower, nativeDistribution, ← sourceTower, ← sourceDistribution] at compare
  exact compare

private theorem native_publication_expected_continuation
    {Seed Source View Parameter : Type} {horizon turns start finish : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (wholeProfile : BehavioralProfile setup.program)
    (reference : setup.informationGraph.BehavioralProfile)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {tailPoint : setup.informationGraph.Config}
    (tailFrame : SourceResidual setup wholeProfile finish tailPoint)
    (tailCovered : tailFrame.refs.CoversPrefix setup.program finish)
    (outer : nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      wholeProfile reference focal deviation
      (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
        final.application.config focal)
      (setup.graphPayoff setup.informationDependencies parameter utility
        (leastUtility utility) focal) tailFrame)
    (profile : (serviceGraph setup deps).BehavioralProfile)
    (independent : ReadyIndependent profile) (opens : OpensPublications profile)
    (run : RevealRun (serviceGraph setup deps) start finish)
    (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (advance : Source → Config Player L tailFrame.Γ × setup.informationGraph.Config)
    (members : Seed → (serviceGraph setup deps).BehavioralProfile)
    (execution : Seed → (serviceApplication setup deps duration leaks).Execution)
    (before : Seed → setup.informationGraph.Config)
    (noise : View → PMF (MessageNetwork Player
        (serviceApplication setup deps duration leaks).Payload ×
      List (MessageId Player × Bool) ×
      List (serviceApplication setup deps duration leaks).EnvironmentEntry ×
      List (serviceApplication setup deps duration leaks).PlayerEntry ×
      PlayerView (serviceGraph setup deps) × PublicView (serviceGraph setup deps)))
    (factor : prior.map (fun seed => (source seed,
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal (execution seed))) =
      (prior.map source).bind fun current =>
        (noise (observe current)).map fun extra => (current, extra))
    (submitted : ∀ seed ∈ prior.support,
      (serviceGraph setup deps).SubmitsBindings (members seed))
    (future : ∀ seed ∈ prior.support, ∀ owner node actor observation active,
      finish ≤ node.val → members seed owner node actor observation active =
        reference owner node actor observation active)
    (boundary : ∀ seed ∈ prior.support, PhaseBoundary scheduler
      (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) (effectiveOpening
          ((serviceGraph setup deps).prefixProfile (members seed)))) focal deviation)
      horizon start (execution seed))
    (metadata : ∀ seed ∈ prior.support,
      @(advance (source seed)).1.revelations = @tailFrame.source.revelations)
    (registry : ∀ seed ∈ prior.support,
      (advance (source seed)).1.registry = tailFrame.source.registry)
    (checkpoint : ∀ seed ∈ prior.support, SourceCheckpoint setup (advance (source seed)).1
      tailFrame.refs finish (advance (source seed)).2)
    (reachable : ∀ seed ∈ prior.support,
      ∃ inputs, (advance (source seed)).2.Reachable inputs)
    (history : ∀ seed ∈ prior.support, ∃ intended : setup.intendedProtocol.History,
      intended.state = some (tailFrame.lift
        (ProtocolState.entry tailFrame.program (advance (source seed)).1)))
    (defaultLaw : ∀ seed ∈ prior.support, outcomeDistribution profile Config.defaulted
      ((serviceGraph setup deps).fromSequentialConfig (advance (source seed)).2) = PMF.pure ∅)
    (potential : ∀ seed ∈ prior.support,
      canonicalDistribution profile (execution seed).application.config = canonicalDistribution
        profile
        ((serviceGraph setup deps).fromSequentialConfig (advance (source seed)).2))
    (reflects : ∀ left ∈ (prior.map source).support, ∀ right ∈ (prior.map source).support,
      (advance left).1.view focal = (advance right).1.view focal → observe left = observe right)
    (visible : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      (advance (source left)).1.view focal = (advance (source right)).1.view focal →
      keyView focal (runKey
        ((serviceGraph setup deps).fromSequentialConfig (advance (source left)).2)) =
      keyView focal (runKey
        ((serviceGraph setup deps).fromSequentialConfig (advance (source right)).2)))
    (prefixAt : ∀ seed ∈ prior.support, (before seed).cut.IsPrefix start)
    (headLaw : ∀ seed ∈ prior.support, setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
        setup.informationGraph.canonicalScheduler) (finish - start) (before seed) =
      PMF.pure (advance (source seed)).2) :
    ∃ policy : setup.informationGraph.BehavioralPolicy focal,
      expect (prior.bind fun seed =>
        (serviceApplication setup deps duration leaks).runToHorizon scheduler
          (Function.update (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
            (firstTurnTiming setup turns deps) (effectiveOpening
              ((serviceGraph setup deps).prefixProfile (members seed)))) focal deviation)
          horizon (execution seed))
        (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
          final.application.config focal) ≤
      expect (prior.bind fun seed => setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (Function.update
          (setup.informationGraph.prefixProfile reference) focal policy)
          setup.informationGraph.canonicalScheduler)
        (finish - start + eventCount tailFrame.program) (before seed))
        (setup.graphPayoff setup.informationDependencies parameter utility
          (leastUtility utility) focal) := by
  classical
  let app := serviceApplication setup deps duration leaks
  let players := fun seed => Function.update
    (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
      (firstTurnTiming setup turns deps) (effectiveOpening
        ((serviceGraph setup deps).prefixProfile (members seed)))) focal deviation
  let phase := fun seed => app.runUntilHorizon scheduler (players seed)
    (fun current => BlockDone finish current.application.config) horizon (execution seed)
  let staged := prior.bind fun seed => (phase seed).map fun final => (seed, final)
  let good := fun entry : Seed × app.Execution => decide
    (focal ∉ entry.2.application.config.defaulted)
  have donorReach : ∀ seed ∈ prior.support, ∃ inputs,
      ((serviceGraph setup deps).fromSequentialConfig (advance (source seed)).2).Reachable
        inputs := by
    intro seed supported
    obtain ⟨inputs, reached⟩ := reachable seed supported
    exact ⟨inputs, Config.Reachable.fromSequentialConfig (serviceGraph setup deps) reached⟩
  have donorOrdered : ∀ seed ∈ prior.support,
      ((serviceGraph setup deps).fromSequentialConfig (advance (source seed)).2).cut.IsPrefix
        finish := by
    intro seed supported
    exact (checkpoint seed supported).ordered
  have survivors := publication_surviving_phase_posterior
    (setup := setup) (deps := deps) (duration := duration) (leaks := leaks)
    scheduler bound relaxed contract timely profile
    (fun seed => (serviceGraph setup deps).prefixProfile (members seed)) independent opens
    focal deviation run prior source observe advance (fun next => next.1.view focal)
    (fun next => (serviceGraph setup deps).fromSequentialConfig next.2) execution noise factor
    boundary donorReach donorOrdered defaultLaw potential reflects visible
  apply native_block_expected_comparison (tailCount := eventCount tailFrame.program)
    scheduler bound contract parameter utility range
    reference focal deviation prior members execution before (fun seed => (advance (source seed)).2)
    (Nat.le_of_lt run.nonempty) run.bounded prefixAt headLaw boundary
  intro present
  obtain ⟨nextNoise, nextFactor, nextBoundary⟩ := survivors present
  let accepted := fiberPosterior staged good true
  have acceptedSeed (entry : Seed × app.Execution) (supported : entry ∈ accepted.support) :
      entry.1 ∈ prior.support := by
    obtain ⟨_survived, stagedSupport⟩ := mem_support_fiberPosterior present supported
    obtain ⟨seed, seedSupport, finalSupport⟩ := (PMF.mem_support_bind_iff _ _ _).mp stagedSupport
    obtain ⟨final, _reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp finalSupport
    cases same
    exact seedSupport
  exact outer tailCovered accepted
    (fun entry => (advance (source entry.1)).1) (fun entry => (advance (source entry.1)).2)
    (fun entry supported => metadata entry.1 (acceptedSeed entry supported))
    (fun entry supported => registry entry.1 (acceptedSeed entry supported))
    (fun entry supported => checkpoint entry.1 (acceptedSeed entry supported))
    (fun entry supported => reachable entry.1 (acceptedSeed entry supported))
    (fun entry supported => history entry.1 (acceptedSeed entry supported))
    (fun entry => members entry.1)
    (fun entry supported => submitted entry.1 (acceptedSeed entry supported))
    (fun entry supported => future entry.1 (acceptedSeed entry supported)) Prod.snd
    (fun entry supported => (nextBoundary entry supported).1)
    (fun entry supported => (nextBoundary entry supported).2.1)
    (fun entry supported => (nextBoundary entry supported).2.2) nextNoise nextFactor

private theorem phaseBoundary_of_completionBoundary
    {horizon rank : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players rank execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (clear : execution.application.config.defaulted = ∅) :
    PhaseBoundary scheduler players horizon rank execution := by
  refine ⟨boundary.supported, bounded,
    (fun event lower => (boundary.ordered.2 event).mpr lower), ?_, ?_, ?_⟩
  · intro event later completed
    exact ((Nat.not_lt.mpr later) ((boundary.ordered.2 event).mp completed)).elim
  · intro owner entry member event ready
    by_contra later
    exact boundary.untouched event (Nat.le_of_not_gt later) owner entry member ready
  · intro completion member owner recorded
    have defaulted : owner ∈ execution.application.config.defaulted :=
      (mem_defaulted_iff_completionOf _ _).mpr ⟨completion.event, by
        rw [(completionOf_eq_some_iff _ _ _).mpr ⟨member, rfl⟩]
        exact recorded⟩
    rw [clear] at defaulted
    simp at defaulted

private theorem canonicalDistribution_eq_of_pure_prefix {graph : EventGraph Player L}
    (profile : graph.BehavioralProfile) (before after : graph.Config) (start finish : Nat)
    (lower : start ≤ finish) (beforeOrdered : before.cut.IsPrefix start)
    (afterOrdered : after.cut.IsPrefix finish)
    (head : graph.runPlan (graph.policyPlan profile graph.canonicalScheduler)
      (finish - start) before = PMF.pure after) :
    canonicalDistribution profile before = canonicalDistribution profile after := by
  have remaining : before.remaining = finish - start + after.remaining := by
    have finishBound := afterOrdered.1
    simp only [Config.remaining, beforeOrdered.card, afterOrdered.card]
    omega
  unfold canonicalDistribution
  rw [remaining, graph.runPlan_add, head, PMF.pure_bind]

theorem nativeSourceContinuation_public [Finite Player]
    {horizon turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {delay : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    (wellFormed : setup.WellFormed)
    (intended : GameTheory.Profile setup.intendedModel.behavioralSignature)
    (target : GameTheory.Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended target)
    (submits : ∀ who, SourceProgram.SubmitsBindings setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    (disclosing : ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target who))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) {forfeit : ℝ}
    (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    {start finish : Nat} {origin : setup.informationGraph.Config}
    (frame : SourceResidual setup (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) target) start origin)
    (run : RevealRun (serviceGraph setup deps) start finish)
    (outer : ∀ {tailPoint : setup.informationGraph.Config}
      (tail : SourceResidual setup (setup.decodeBehavioralProfile
        (CommitmentInterface.forfeiture setup.program) target) finish tailPoint),
      nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
        (setup.informationGraph.submitProfile (compileEventProfile setup.program
          (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)))
        focal deviation
        (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
          final.application.config focal)
        (setup.graphPayoff setup.informationDependencies parameter utility
          (leastUtility utility) focal) tail) :
    nativeSourceContinuation setup deps duration leaks horizon scheduler bound turns
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)
      (setup.informationGraph.submitProfile (compileEventProfile setup.program
        (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) target)))
      focal deviation
      (fun final => setup.graphForfeitConfigPayoff deps parameter utility forfeit
        final.application.config focal)
      (setup.graphPayoff setup.informationDependencies parameter utility
        (leastUtility utility) focal) frame := by
  classical
  let G := serviceGraph setup deps
  let wholeProfile := setup.decodeBehavioralProfile
    (CommitmentInterface.forfeiture setup.program) target
  let reference := setup.informationGraph.submitProfile
    (compileEventProfile setup.program wholeProfile)
  let profile : G.BehavioralProfile := compilePrescribedProfile setup.program deps wholeProfile
  have rawOpens (owner : Player) (event : G.EventId) (actor : G.actor? event = some owner)
      (publication : (G.outputLayout event).IsPublication) (observation : G.PlayerObservation owner)
      (active : owner ∉ observation.defaulted) :
      G.submitProfile (compileEventProfile setup.program wholeProfile) owner event actor
        observation active = PMF.pure (EventField.openAction _ publication) := by
    change (compileEventPolicy setup.program owner (wholeProfile owner) event actor observation
      active).map (EventField.submitAction _) = _
    rw [compileEventPolicy_publication setup.program owner (wholeProfile owner)
      (disclosing owner) event actor publication, PMF.pure_map]
    congr 1
    exact EventField.submitAction_eq_self _ _
      (EventField.submitted_of_publication _ publication _)
  have independent : ReadyIndependent profile :=
    relaxed.readyIndependent_prefixProfile
      (G.submitProfile (compileEventProfile setup.program wholeProfile))
      (fun owner event actor publication left right leftActive rightActive =>
        (rawOpens owner event actor publication left leftActive).trans
          (rawOpens owner event actor publication right rightActive).symm)
  have opens : OpensPublications profile := by
    intro config event owner actor publication active
    exact compilePrescribedProfile_publication setup.program deps wholeProfile disclosing
      owner event actor publication _ _
  intro covered Seed prior source ghost metadata registry checkpoint reachable history members
    submitted future execution players boundary budget keys noise factor
  have typed := exists_reveal_prefix_source_frame wellFormed intended target agrees disclosing
    (finish - start) start origin frame covered (by
      rw [Nat.add_sub_of_le (Nat.le_of_lt run.nonempty)]
      exact run.bounded)
      (fun event lower upper => run.publications event lower (by have := run.nonempty; omega))
  rw [show start + (finish - start) = finish by have := run.nonempty; omega] at typed
  obtain ⟨endOrigin, tail, tailCovered, countEq, advanceExists⟩ := typed
  let valid := fun hidden : Config Player L frame.Γ × setup.informationGraph.Config =>
    @hidden.1.revelations = @frame.source.revelations ∧
      hidden.1.registry = frame.source.registry ∧
      SourceCheckpoint setup hidden.1 frame.refs start hidden.2 ∧
      (∃ inputs, hidden.2.Reachable inputs) ∧
      ∃ intendedHistory : setup.intendedProtocol.History,
        intendedHistory.state = some (frame.lift (ProtocolState.entry frame.program hidden.1))
  let nextValid := fun (hidden : Config Player L frame.Γ × setup.informationGraph.Config)
      (next : Config Player L tail.Γ × setup.informationGraph.Config) =>
    @next.1.revelations = @tail.source.revelations ∧
      next.1.registry = tail.source.registry ∧
      SourceCheckpoint setup next.1 tail.refs finish next.2 ∧
      (∃ inputs, next.2.Reachable inputs) ∧
      (∃ intendedHistory : setup.intendedProtocol.History,
        intendedHistory.state = some (tail.lift (ProtocolState.entry tail.program next.1))) ∧
      setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
          setup.informationGraph.canonicalScheduler) (finish - start) hidden.2 = PMF.pure next.2
  have nextExists (hidden : Config Player L frame.Γ × setup.informationGraph.Config)
      (supported : valid hidden) : ∃ next, nextValid hidden next := by
    obtain ⟨reveals, names, check, ⟨inputs, reach⟩, intendedHistory, atHistory⟩ := supported
    obtain ⟨nextSource, nextGhost, nextMetadata, nextRegistry, nextCheckpoint, nextReach,
      nextHistory, law⟩ := advanceExists hidden.1 reveals names hidden.2 check inputs reach
        intendedHistory atHistory
    exact ⟨(nextSource, nextGhost), nextMetadata, nextRegistry, nextCheckpoint,
      ⟨inputs, nextReach⟩, nextHistory, law⟩
  let advance := fun hidden => if supported : valid hidden then
    (nextExists hidden supported).choose else (tail.source, endOrigin)
  have nextFacts (hidden : Config Player L frame.Γ × setup.informationGraph.Config)
      (supported : valid hidden) : nextValid hidden (advance hidden) := by
    dsimp only [advance]
    rw [dite_eq_left supported]
    exact (nextExists hidden supported).choose_spec
  have currentValid (seed : Seed) (supported : seed ∈ prior.support) :
      valid (source seed, ghost seed) :=
    ⟨metadata seed supported, registry seed supported, checkpoint seed supported,
      reachable seed supported, history seed supported⟩
  have endFacts (seed : Seed) (supported : seed ∈ prior.support) :
      nextValid (source seed, ghost seed) (advance (source seed, ghost seed)) :=
    nextFacts _ (currentValid seed supported)
  have endPath (seed : Seed) (supported : seed ∈ prior.support) :
      Relation.ReflTransGen Config.Step (ghost seed) (advance (source seed, ghost seed)).2 := by
    apply runPlan_graph_steps
      (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
        setup.informationGraph.canonicalScheduler) (finish - start)
    rw [(endFacts seed supported).2.2.2.2.2]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have endClear (seed : Seed) (supported : seed ∈ prior.support) :
      (advance (source seed, ghost seed)).2.defaulted = ∅ := by
    obtain ⟨reveals, names, check, _reach, ⟨intendedHistory, atHistory⟩, _law⟩ :=
      endFacts seed supported
    let actual := residualAt tail (advance (source seed, ghost seed)).1 reveals names
      (advance (source seed, ghost seed)).2 check
    exact actual.clear_of_intended_history wellFormed intendedHistory
      (atHistory.trans actual.decode.symm)
  have endLaw (seed : Seed) (supported : seed ∈ prior.support) :
      outcomeDistribution profile Config.defaulted
        (G.fromSequentialConfig (advance (source seed, ghost seed)).2) = PMF.pure ∅ := by
    obtain ⟨reveals, names, check, ⟨inputs, reach⟩, ⟨intendedHistory, atHistory⟩, _law⟩ :=
      endFacts seed supported
    let actual := residualAt tail (advance (source seed, ghost seed)).1 reveals names
      (advance (source seed, ghost seed)).2 check
    exact actual.prescribed_defaultDistribution_fromSequential deps wellFormed
      (CommitmentInterface.forfeiture setup.program) intended target agrees submits reach
      intendedHistory (atHistory.trans actual.decode.symm)
  have phaseBoundary (seed : Seed) (supported : seed ∈ prior.support) :
      PhaseBoundary scheduler (players seed) horizon start (execution seed) := by
    obtain ⟨intendedHistory, atHistory⟩ := history seed supported
    let actual := residualAt frame (source seed) (metadata seed supported) (registry seed supported)
      (ghost seed) (checkpoint seed supported)
    have ghostClear := actual.clear_of_intended_history wellFormed intendedHistory
      (atHistory.trans actual.decode.symm)
    have clear := defaulted_eq_of_completionOf_eq
      (congrArg (fun key => key.2.2) (keys seed supported))
    rw [G.fromSequentialConfig_defaulted, ghostClear] at clear
    exact phaseBoundary_of_completionBoundary scheduler (players seed) (execution seed)
      (boundary seed supported) (budget seed supported) clear
  have potential (seed : Seed) (supported : seed ∈ prior.support) :
      canonicalDistribution profile (execution seed).application.config =
        canonicalDistribution profile (G.fromSequentialConfig (advance
          (source seed, ghost seed)).2) := by
    have headLaw := G.runPlan_canonical_fromSequential
      (setup.informationGraph.prefixProfile reference) (finish - start) (ghost seed)
    change (setup.informationGraph.runPlan
      (setup.informationGraph.policyPlan (setup.informationGraph.prefixProfile reference)
        setup.informationGraph.canonicalScheduler) (finish - start) (ghost seed)).map
          G.fromSequentialConfig =
        G.runPlan (G.policyPlan profile G.canonicalScheduler) (finish - start)
          (G.fromSequentialConfig (ghost seed)) at headLaw
    rw [(endFacts seed supported).2.2.2.2.2, PMF.pure_map] at headLaw
    exact (independent.canonicalDistribution_congr _ _ _ rfl (keys seed supported)).trans
      (canonicalDistribution_eq_of_pure_prefix profile _ _ start finish (Nat.le_of_lt run.nonempty)
        (checkpoint seed supported).ordered (endFacts seed supported).2.2.1.ordered
        headLaw.symm)
  have reflects : ∀ left ∈ (prior.map (fun seed => (source seed, ghost seed))).support,
    ∀ right ∈ (prior.map (fun seed => (source seed, ghost seed))).support,
    (advance left).1.view focal = (advance right).1.view focal →
      left.1.view focal = right.1.view focal := by
    intro left leftSupported right rightSupported same
    obtain ⟨leftSeed, leftMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp leftSupported
    obtain ⟨rightSeed, rightMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rightSupported
    obtain ⟨_leftInputs, leftReach⟩ := reachable leftSeed leftMember
    obtain ⟨_rightInputs, rightReach⟩ := reachable rightSeed rightMember
    exact SourceCheckpoint.sourceView_reflects_at_path_end frame.refs tail.refs start finish
      tailCovered focal (source leftSeed) (source rightSeed)
      (advance (source leftSeed, ghost leftSeed)).1
      (advance (source rightSeed, ghost rightSeed)).1 (ghost leftSeed) (ghost rightSeed)
      (advance (source leftSeed, ghost leftSeed)).2
      (advance (source rightSeed, ghost rightSeed)).2 leftReach rightReach
      (endPath leftSeed leftMember) (endPath rightSeed rightMember)
      (by rw [endClear leftSeed leftMember]; simp)
      (by rw [endClear rightSeed rightMember]; simp)
      (checkpoint leftSeed leftMember) (checkpoint rightSeed rightMember)
      (endFacts leftSeed leftMember).2.2.1 (endFacts rightSeed rightMember).2.2.1 same
  have visible : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
    (advance (source left, ghost left)).1.view focal =
      (advance (source right, ghost right)).1.view focal →
    keyView focal (runKey (G.fromSequentialConfig (advance (source left, ghost left)).2)) =
      keyView focal (runKey (G.fromSequentialConfig (advance (source right, ghost right)).2)) := by
    intro left leftSupported right rightSupported same
    obtain ⟨_leftInputs, leftReach⟩ := (endFacts left leftSupported).2.2.2.1
    obtain ⟨_rightInputs, rightReach⟩ := (endFacts right rightSupported).2.2.2.1
    exact SourceCheckpoint.keyView_eq_of_sourceView tail.refs finish tailCovered focal
      (advance (source left, ghost left)).1 (advance (source right, ghost right)).1
      (advance (source left, ghost left)).2 (advance (source right, ghost right)).2
      leftReach rightReach (by rw [endClear left leftSupported]; simp)
      (by rw [endClear right rightSupported]; simp)
      (endFacts left leftSupported).2.2.1 (endFacts right rightSupported).2.2.1 same
  obtain ⟨policy, compare⟩ := native_publication_expected_continuation scheduler bound relaxed
    contract timely parameter utility range wholeProfile reference focal deviation tail tailCovered
    (outer tail) profile independent opens run prior (fun seed => (source seed, ghost seed))
    (fun hidden => hidden.1.view focal) advance members execution ghost noise factor submitted
    (fun seed supported owner node actor observation active lower => future seed supported owner
      node actor observation active (by have := run.nonempty; omega)) phaseBoundary
    (fun seed supported => (endFacts seed supported).1)
    (fun seed supported => (endFacts seed supported).2.1)
    (fun seed supported => (endFacts seed supported).2.2.1)
    (fun seed supported => (endFacts seed supported).2.2.2.1)
    (fun seed supported => (endFacts seed supported).2.2.2.2.1)
    endLaw potential reflects visible (fun seed supported => (checkpoint seed supported).ordered)
    (fun seed supported => (endFacts seed supported).2.2.2.2.2)
  refine ⟨policy, ?_⟩
  rw [countEq]
  exact compare

end Vegas
