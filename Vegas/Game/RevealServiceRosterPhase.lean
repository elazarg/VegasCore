/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterContinuation
import Vegas.Pending.ReactiveOpeningContinuationExpiry

/-! # Source continuations from an unfinished revelation phase

The current physical response memory conditions the timing mixture. Completing
the actual phase, followed by the remaining source service, has the corresponding
source disclosure continuation. Neither the private response history nor pending
traffic is reset at the phase boundary.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem PublicCheckpoint.reveal_endpoint_agrees
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : PublicCheckpoint setup leaks initial source refs rank execution)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get binding) [] outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : ∀ disclose, decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
        some (.reveal owner name disclose))
    (ready : execution.application.config.cut.Ready event)
    (value : L.Val payload) (bound : source.state.get binding = .success value)
    (candidate : Handle (graph setup))
    (associated : execution.application.accepted (refs.get binding).field = some candidate)
    (disclose : Bool) (next : (application setup leaks).Execution)
    (nextInvariant : EventGraphRuntime.State.Invariant (graph := graph setup)
      (setup.eventInputs initial) next.application)
    (applicationEq : next.application = (if disclose then
      { execution.application.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.success value)) with
          clock := execution.application.clock + (event.val + 1) }
      else ({ execution.application with clock := execution.application.clock + (event.val + 1) } :
        EventGraphRuntime.State (graph setup)).complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) PublicationResult.failure)))
    (ledger : next.network.ledger = (if disclose then List.append execution.network.ledger
      [(runtime setup).windowEnvelope leaks owner event candidate ⟨payload, value⟩ execution]
      else execution.network.ledger))
    (receipts : next.receipts = (if disclose then execution.receipts ++
      [((owner, execution.network.nextSerial owner), true)] else execution.receipts))
    (counters : next.network.nextSerial = fun who => execution.network.nextSerial who +
      if who = owner ∧ disclose then 1 else 0) :
    PublicCheckpoint setup leaks initial (revealSuccessor published binding source disclose)
      (refs.cons (name := published) ⟨.inr event, outputEq⟩) (rank + 1) next := by
  have store : (refs.cons (name := published) ⟨.inr event, outputEq⟩).Agrees
      (revealSuccessor published binding source disclose).state
      (execution.application.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (if disclose then source.state.get binding
            else PublicationResult.failure))).config.store :=
    complete_reveal_agrees published binding source checkpoint.emptyRegistry refs
      execution.application checkpoint.agrees event ready outputEq before disclose
  simp only [bound] at store
  have history := complete_reveal_history setup published binding source execution.application
    checkpoint.history event ready
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    (cast (congrArg EventGraph.EventField.Value outputEq.symm)
      (if disclose then PublicationResult.success value else .failure)) disclose (decoded disclose)
  apply checkpoint.reveal_endpoint published binding event eventRank outputEq codeEq node ready
    value candidate associated disclose next nextInvariant _ _ applicationEq ledger receipts
      counters
  · rw [applicationEq]
    cases disclose <;> exact @store
  · rw [applicationEq]
    cases disclose <;> exact history

omit [Fintype Player] in
/-- Typed head case: the actual remaining window and future roster blocks
implement the source continuation under the current timing posterior. -/
theorem roster_reveal_continuation_law [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program) (initial : State L setup.context)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (binding : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name)) (reveals : next.RevealOnly)
    (profile : BehavioralProfile (.reveal published owner name fresh binding unresolved next))
    (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh binding unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh binding unresolved next) profile
      refs source.revelations [] embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (checkpoint : PublicCheckpoint setup leaks initial source refs offset execution)
    (candidate : Handle (graph setup)) (value : L.Val payload)
    (bound : source.state.get binding = .success value)
    (associated : execution.application.accepted (refs.get binding).field = some candidate)
    (owned : candidate.1 = owner)
    (valid : execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (responseOffset : Nat) {slots : Nat} (choices : PMF (Option (Fin slots))) (visits : Nat)
    (current : (application setup leaks).Execution)
    (serials : execution.network.SerialsBeforeNext)
    (remaining : List Player) (complete : visits + remaining.count owner = slots)
    (counts : ∀ who, (current.recall who).length + remaining.count who =
      (((List.finRange (graph setup).order.eventCount).take (offset + 1)).flatMap
        rosters).count who) :
    let event := embedding.event ⟨0, by simp [eventCount]⟩
    let app := application setup leaks
    let family := fun mode => app.scheduledPolicy responseOffset mode
      (fun _ _ => PMF.pure
        ((runtime setup).windowOpening leaks event candidate ⟨payload, value⟩)) app.silentPolicy
    let posterior := (app.policyMixture choices family).posterior (current.recall owner)
    (∀ mode ∈ posterior.support,
      (runtime setup).OpeningWindowFrame leaks owner event candidate ⟨payload, value⟩
        responseOffset mode visits execution current) →
    (((runtime setup).runInteractionPlan leaks
      ((runtime setup).openingWindowMixturePlayers leaks owner event candidate ⟨payload, value⟩
        responseOffset choices) network
      (remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]))
      current).bind fun settled => (runtime setup).runInteractionPlan leaks
        (rosterPolicy setup leaks rosters timing wholeProfile) network
        ((List.finRange (eventCount next)).flatMap fun index =>
          rosterBlock setup rosters (embedding.event index.succ)) settled).map
      (fun final => decodeState? (terminalRefsWith
        (.reveal published owner name fresh binding unresolved next) refs embedding.ref)
          final.application.config.store) =
      (posterior.bind fun mode => runFrom next (afterReveal profile)
        (revealSuccessor published binding source mode.isSome)).map some := by
  intro event app family posterior frames
  let := Fintype.ofFinite Player
  let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
    ⟨0, by simp [eventCount]⟩
  have eventRank : event.val = offset := by
    simpa only [event, index, Fin.val_zero, Nat.add_zero] using aligned.graphSuffix.rankEq index
  have actor : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  have outputEq : (graph setup).outputLayout event = .publication payload :=
    embedding.layout_eq index
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding) [] :=
    reveal_head_code setup fresh binding unresolved next refs source.revelations embedding
      refsBefore offset aligned.graphSuffix
  have node : nodeView (graph setup) event =
      .resolve owner payload (refs.get binding) [] outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  have ready : execution.application.config.cut.Ready event := by
    have within : offset < (graph setup).order.eventCount := eventRank ▸ event.isLt
    have same : (⟨offset, within⟩ : (graph setup).EventId) = event := Fin.ext eventRank.symm
    rw [← same]
    exact checkpoint.ordered.ready within
  have strategic : ((graph setup).actor? event).isSome = true := by rw [actor]; rfl
  have stored : (refs.get binding).get? execution.application.config.store =
      some (.success value) := by
    simpa only [bound, cellValue] using checkpoint.agrees binding
  have resolved : EventGraph.EventCode.resolveOutput? (refs.get binding) [] true
      execution.application.config.store = some (.success value) := by
    simp only [EventGraph.EventCode.resolveOutput?, stored,
      EventGraph.GuardCheck.allAccepted?, ↓reduceIte]
    rfl
  have accepted := handle_opening_eq (runtime setup) execution.application
    (owner, execution.network.nextSerial owner)
    event candidate owner payload (refs.get binding) [] outputEq codeEq node ready
    (checkpoint.timely event eventRank strategic) rfl owned associated value valid stored
      (.success value) resolved
  obtain ⟨entered, activated⟩ := checkpoint.invariant.activatedAt_eq_some_of_ready_actor
    event ready strategic
  have due := checkpoint.invariant.due_after_deadline (runtime setup) event entered activated
  obtain ⟨coupling, first, second, endpoint⟩ :=
    (runtime setup).openingWindowMixture_continuation_expiry leaks owner event payload
      (refs.get binding) [] outputEq codeEq node candidate value responseOffset choices visits
      execution current ready serials owned valid
      ((reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _
        ((runtime setup).windowEnvelope_tokenValid leaks owner event candidate _ execution
          ready)).trans accepted) entered (event.val + 1) activated due
      remaining complete network frames
  change coupling.map Prod.fst = posterior at first
  let phasePlayers := (runtime setup).openingWindowMixturePlayers leaks owner event candidate
    ⟨payload, value⟩ responseOffset choices
  let phase : List (ServiceInstruction (graph setup)) := remaining.map ServiceInstruction.player ++
    (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event])
  obtain ⟨mode, modePresent⟩ := posterior.support_nonempty
  have invariant : EventGraphRuntime.State.Invariant (graph := graph setup)
      (setup.eventInputs initial) current.application := by
    rw [(frames mode modePresent).application]
    exact checkpoint.invariant
  let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
  let tailRefs := refs.cons (name := published) (cell := .publication payload)
    (embedding.ref index)
  have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
    intro readName cell ref remaining
    cases ref with
    | here =>
        change (embedding.event index).val < (embedding.event (Fin.succ remaining)).val
        apply embedding.strictMono
        exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
    | there ref => exact refsBefore ref (Fin.succ remaining)
  rw [← second, PMF.bind_map, PMF.map_bind, ← first, PMF.bind_map,
    PMF.map_bind]
  apply bind_congr_on_support _
  intro pair present
  have supported : pair.2 ∈ ((runtime setup).runInteractionPlan leaks phasePlayers network
      phase current).support := by
    rw [← second]
    rw [PMF.support_map]
    exact ⟨pair, present, rfl⟩
  obtain ⟨applicationEq, clean, ledger, receipts, counters⟩ := endpoint pair present
  have progressed := (runtime setup).runInteractionPlan_facts leaks (setup.eventInputs initial)
    phasePlayers network phase current pair.2 invariant supported
  have decoded (disclose : Bool) : decodeEventAction setup.program event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
      some (.reveal owner name disclose) := by
    have law := aligned.actionEq index
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
    simpa [event, index, outputEq, decodeEventAction] using law
  have after := checkpoint.reveal_endpoint_agrees published binding event eventRank
    outputEq codeEq node (fun ref => refsBefore ref index) decoded ready value bound candidate
      associated pair.1.isSome pair.2 progressed.invariant applicationEq ledger receipts counters
  have afterCounts (who : Player) : (pair.2.recall who).length =
      (((List.finRange (graph setup).order.eventCount).take (offset + 1)).flatMap
        rosters).count who :=
    by
    have advanced := fixed_plan_response_counts setup leaks network phasePlayers phase
      (by simp [phase]) current pair.2 supported who
    have countLaw : (pair.2.recall who).length =
        (current.recall who).length + remaining.count who := by
      simpa only [phase, List.filterMap_append, List.filterMap_map, instructionActor,
      Function.comp_def, List.filterMap_some, List.filterMap_cons, List.filterMap_replicate,
      List.filterMap_nil, List.nil_append, List.append_nil, List.count_nil, Nat.add_zero]
        using advanced
    exact countLaw.trans (counts who)
  have afterSerials := (runtime setup).runInteractionPlan_serials leaks phasePlayers network
    phase current pair.2 (frames mode modePresent).serials supported
  have tailAligned : CompiledPolicySuffix setup.program wholeProfile next (afterReveal profile)
      tailRefs (revealSuccessor published binding source pair.1.isSome).revelations
      [] tailEmbedding tailBefore (offset + 1) := by
    simpa only [Registry.weaken, List.map_nil, revealSuccessor, tailRefs, tailEmbedding,
      OutputEmbedding.ref] using aligned.revealTail (whole := setup.program)
        (wholeProfile := wholeProfile) fresh binding unresolved next profile refs
        source.revelations [] embedding refsBefore offset
  exact run_roster_source_suffix_option_law setup leaks rosters timing network wholeProfile initial
    next reveals (afterReveal profile) (revealSuccessor published binding source pair.1.isSome)
    tailRefs tailEmbedding tailBefore (offset + 1) tailAligned pair.2 after afterCounts clean
      afterSerials

omit [Fintype Player] in
/-- The existing source protocol position aligns an unfinished native window
with its actual source step. This includes positions after arbitrarily many
earlier reveals, without introducing another source interpreter. -/
theorem prefix_roster_window_continuation_law [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program) (initial : State L setup.context) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (_reveals : program.RevealOnly)
      (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations []
        embedding refsBefore offset →
      ∀ (count : Nat) (inside : count < eventCount program) (state : ProtocolState program)
        (execution : (application setup leaks).Execution),
      PublicPrefixCheckpoint setup leaks initial program refs revelations embedding.ref
        offset count state execution →
      ∀ (owner : Player), (graph setup).actor? (embedding.event ⟨count, inside⟩) = some owner →
      ∀ (candidate : Handle (graph setup)) (raw : Raw L),
      rosterOpening? setup leaks owner (embedding.event ⟨count, inside⟩)
        (execution.observe (application setup leaks) owner) = some (candidate, raw) →
      ∀ (responseOffset slots : Nat) (choices : PMF (Option (Fin slots))) (visits : Nat)
        (current : (application setup leaks).Execution),
      execution.network.SerialsBeforeNext →
      ∀ (remaining : List Player), visits + remaining.count owner = slots →
      (∀ who, (current.recall who).length + remaining.count who =
        (((List.finRange (graph setup).order.eventCount).take (offset + count + 1)).flatMap
          rosters).count who) →
      ∀ (joint : Bool → Player → Option (OwnAction Player L)),
      (∀ disclose, OwnAction.disclosure (joint disclose owner) = disclose) →
      let event := embedding.event ⟨count, inside⟩
      let app := application setup leaks
      let family := fun mode => app.scheduledPolicy responseOffset mode
        (fun _ _ => PMF.pure ((runtime setup).windowOpening leaks event candidate raw))
          app.silentPolicy
      let posterior := (app.policyMixture choices family).posterior (current.recall owner)
      (∀ mode ∈ posterior.support,
        (runtime setup).OpeningWindowFrame leaks owner event candidate raw
          responseOffset mode visits execution current) →
      (((runtime setup).runInteractionPlan leaks
        ((runtime setup).openingWindowMixturePlayers leaks owner event candidate raw
          responseOffset choices) network
        (remaining.map ServiceInstruction.player ++
          (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]))
        current).bind fun settled => (runtime setup).runInteractionPlan leaks
          (rosterPolicy setup leaks rosters timing wholeProfile) network
          (((List.finRange (eventCount program)).drop (count + 1)).flatMap fun index =>
            rosterBlock setup rosters (embedding.event index)) settled).map
        (fun final => decodeState? (terminalRefsWith program refs embedding.ref)
          final.application.config.store) =
        (posterior.bind fun mode => (ProtocolState.step program state (joint mode.isSome)).bind
          (ProtocolState.continuationLaw program profile)).map some := by
  let := Fintype.ofFinite Player
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro reveals profile refs revelations embedding refsBefore offset aligned count inside
      simp only [eventCount] at inside
      omega
  | sample name fresh law next ih => intro impossible; exact impossible.elim
  | commit name owner fresh guard next ih => intro impossible; exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh binding unresolved next ih =>
      intro reveals profile refs revelations embedding refsBefore offset aligned count inside state
        execution related who owned candidate raw opening responseOffset slots choices visits
        current serials remaining complete counts joint chosen event app family posterior frames
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [← revelationsEq] at aligned
          let index : Fin (eventCount
            (.reveal published owner name fresh binding unresolved next)) :=
              ⟨0, by simp [eventCount]⟩
          have actor : (graph setup).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
          have sameOwner : who = owner := Option.some.inj (owned.symm.trans actor)
          subst who
          have outputEq : (graph setup).outputLayout event = .publication payload :=
            embedding.layout_eq index
          have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
              ((graph setup).nodes event) = .resolve owner payload (refs.get binding) [] :=
            reveal_head_code setup fresh binding unresolved next refs source.revelations
              embedding refsBefore offset aligned.graphSuffix
          have node : nodeView (graph setup) event =
              .resolve owner payload (refs.get binding) [] outputEq codeEq :=
            EventGraphRuntime.nodeView_eq_resolve _ _
          obtain ⟨value, bound⟩ := checkpoint.openable binding
          obtain ⟨canonical, associated, candidateOwned, valid, canonicalOpening⟩ :=
            roster_opening_at_checkpoint setup leaks binding source.state refs execution
              checkpoint.agrees checkpoint.binding event outputEq codeEq node value bound
          have pairEq := Option.some.inj (opening.symm.trans canonicalOpening)
          have candidateEq : candidate = canonical := congrArg Prod.fst pairEq
          have rawEq : raw = ⟨payload, value⟩ := congrArg Prod.snd pairEq
          subst canonical
          subst raw
          have law := roster_reveal_continuation_law setup leaks rosters timing network
            wholeProfile initial fresh binding unresolved next reveals profile source refs
            embedding refsBefore offset aligned execution checkpoint candidate value bound
            associated candidateOwned valid responseOffset choices visits current serials
            remaining complete (by simpa only [Nat.add_zero] using counts) frames
          have sourceStep (disclose : Bool) :
              ((ProtocolState.step (.reveal published owner name fresh binding unresolved next)
                (ProtocolState.entry _ source) (joint disclose)).bind
                  (ProtocolState.continuationLaw _ profile)) =
                runFrom next (afterReveal profile)
                  (revealSuccessor published binding source disclose) := by
            change (PMF.pure (Sum.inr (α := Config Player L Γ)
              (ProtocolState.entry next (revealSuccessor published binding source
                (OwnAction.disclosure (joint disclose owner)))))).bind _ = _
            rw [PMF.pure_bind, chosen]
            exact ProtocolState.continuationLaw_entry next (afterReveal profile) _
          simp_rw [sourceStep]
          simpa only [eventCount, List.finRange_succ, List.drop_succ_cons, List.drop_zero,
            List.flatMap_map] using law
      | succ count =>
          cases state with
          | inl source => exact related.elim
          | inr state =>
              let index : Fin (eventCount
                (.reveal published owner name fresh binding unresolved next)) :=
                  ⟨0, by simp [eventCount]⟩
              let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
              let tailRefs := refs.cons (name := published) (cell := .publication payload)
                (embedding.ref index)
              have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
                intro readName cell ref future
                cases ref with
                | here =>
                    change (embedding.event index).val <
                      (embedding.event (Fin.succ future)).val
                    apply embedding.strictMono
                    exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
                | there ref => exact refsBefore ref (Fin.succ future)
              have tailAligned : CompiledPolicySuffix setup.program wholeProfile next
                  (afterReveal profile) tailRefs (revelations.reveal binding)
                  [] tailEmbedding tailBefore (offset + 1) := by
                simpa only [Registry.weaken, List.map_nil, tailRefs, tailEmbedding] using
                  aligned.revealTail (whole := setup.program) (wholeProfile := wholeProfile)
                    fresh binding unresolved next profile refs revelations [] embedding
                    refsBefore offset
              have within : count < eventCount next := by simp only [eventCount] at inside; omega
              have tailCounts : ∀ who, (current.recall who).length + remaining.count who =
                  (((List.finRange (graph setup).order.eventCount).take
                    (offset + 1 + count + 1)).flatMap rosters).count who := by
                simpa only [Nat.add_assoc, Nat.add_comm 1 count] using counts
              have law := ih reveals (afterReveal profile) tailRefs (revelations.reveal binding)
                tailEmbedding tailBefore (offset + 1) tailAligned count within state execution
                related who owned candidate raw opening responseOffset slots choices visits
                current serials remaining complete tailCounts joint chosen frames
              simp only [eventCount, List.finRange_succ, List.drop_succ_cons, ← List.map_drop,
                List.flatMap_map, terminalRefsWith, ProtocolState.step, Sum.elim_inr,
                PMF.bind_map, ProtocolState.continuationLaw]
              convert law using 1 <;> rfl

omit [Fintype Player] in
/-- Whole-program instance with the actual terminal source readout. The
Boolean joint-action section may be chosen from an original source menu. -/
theorem roster_window_source_step_law [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly) (profile : BehavioralProfile setup.program)
    (initial : State L setup.context) (event : (graph setup).EventId)
    (source : ProtocolState setup.program) (execution : (application setup leaks).Execution)
    (related : PublicPrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val source execution)
    (owner : Player) (owned : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (execution.observe (application setup leaks) owner) = some (candidate, raw))
    (responseOffset slots : Nat) (choices : PMF (Option (Fin slots))) (visits : Nat)
    (current : (application setup leaks).Execution)
    (serials : execution.network.SerialsBeforeNext)
    (remaining : List Player) (complete : visits + remaining.count owner = slots)
    (counts : ∀ who, (current.recall who).length + remaining.count who =
      (((List.finRange (graph setup).order.eventCount).take (event.val + 1)).flatMap
        rosters).count who)
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose owner) = disclose) :
    let app := application setup leaks
    let family := fun mode => app.scheduledPolicy responseOffset mode
      (fun _ _ => PMF.pure ((runtime setup).windowOpening leaks event candidate raw))
        app.silentPolicy
    let posterior := (app.policyMixture choices family).posterior (current.recall owner)
    (∀ mode ∈ posterior.support,
      (runtime setup).OpeningWindowFrame leaks owner event candidate raw
        responseOffset mode visits execution current) →
    (((runtime setup).runInteractionPlan leaks
      ((runtime setup).openingWindowMixturePlayers leaks owner event candidate raw
        responseOffset choices) network
      (remaining.map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]))
      current).bind fun settled => (runtime setup).runInteractionPlan leaks
        (rosterPolicy setup leaks rosters timing profile) network
        (((List.finRange (eventCount setup.program)).drop (event.val + 1)).flatMap
          (rosterBlock setup rosters)) settled).map
      (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
      (posterior.bind fun mode => (ProtocolState.step setup.program source (joint mode.isSome)).bind
        (ProtocolState.continuationLaw setup.program profile)).map some := by
  intro app family posterior frames
  simp_rw [sourceReadout_eq_decode]
  exact prefix_roster_window_continuation_law setup leaks rosters timing network profile initial
    setup.program reveals profile (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program profile)
    event.val event.isLt source execution related owner owned candidate raw opening responseOffset
    slots choices visits current serials remaining complete
    (by simpa only [Nat.zero_add] using counts) joint chosen frames

end Vegas
