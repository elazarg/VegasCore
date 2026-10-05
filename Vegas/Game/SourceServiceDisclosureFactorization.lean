/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFactorization
import GameTheoryExtensions.Math.Probability.Support

/-! # Conditional traffic laws for guarded disclosure

The conditional branch below runs the actual opening window, protected
inclusion and deadline settlement. The evidence comes from the current
candidate catalogue, including bindings created during this execution.
Only effective source choices are used; their original private intentions
are handled by the source assessment's disclosure normalization.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The traffic of an actual service window, conditional on a source choice.
This is a proof kernel over the existing interpreter, not a separate game. -/
def guardedDisclosureTranscript
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player)
    (owner focal : Player) (event : (graph setup).EventId) (ticks : Nat)
    (timing : PMF (Fin (roster.count owner)))
    (execution : (application setup leaks).Execution) (disclose : Bool) :=
  let app := application setup leaks
  let phase := (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
    (List.replicate ticks .tick ++ [.expire event])
  let withheld := ((runtime setup).runInteractionPlan leaks (fun _ => app.silentPolicy)
    network phase execution).map ((runtime setup).bindingTraffic leaks focal)
  if disclose then
    match rosterOpening? setup leaks owner event (execution.observe app owner) with
    | none => withheld
    | some (candidate, raw) => timing.bind fun slot =>
        ((runtime setup).runInteractionPlan leaks
          ((runtime setup).openingWindowPlayers leaks owner event candidate raw
            (execution.recall owner).length (some slot)) network phase execution).map
              ((runtime setup).bindingTraffic leaks focal)
  else withheld

/-- Equal effective source successor views induce equal actual traffic laws.
The guard may inspect private bindings: success is checked in each state,
and withholding needs neither a successful guard nor an openable candidate. -/
theorem guarded_disclosure_transcript_congr
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
    (leftRecall : left.InputRecall (application setup leaks))
    (rightRecall : right.InputRecall (application setup leaks))
    (leftSerials : left.network.SerialsBeforeNext)
    (rightSerials : right.network.SerialsBeforeNext)
    (leftPublished : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id)
    (rightPublished : right.network.Satisfies fun message =>
      message.id ∈ right.network.ledger.map Message.id)
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player)
    (focal : Player) (ticks : Nat) (timing : PMF (Fin (roster.count owner)))
    (leftChoice rightChoice : Bool)
    (leftEffective : leftChoice = false ∨ ∃ value : L.Val payload,
      leftChoice = true ∧ disclosureResult published binding leftSource true = .success value)
    (rightEffective : rightChoice = false ∨ ∃ value : L.Val payload,
      rightChoice = true ∧ disclosureResult published binding rightSource true = .success value)
    (same : (revealSuccessor published binding leftSource leftChoice).view focal =
      (revealSuccessor published binding rightSource rightChoice).view focal)
    (traffic : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right)
    (counts : (left.recall owner).length = (right.recall owner).length) :
    guardedDisclosureTranscript setup leaks network roster owner focal event ticks timing
        left leftChoice =
      guardedDisclosureTranscript setup leaks network roster owner focal event ticks timing
        right rightChoice := by
  have result := congrArg
    (fun view : DecisionView focal ((published, .publication payload) :: Γ) =>
      view.1.cells.get .here) same
  change disclosureResult published binding leftSource leftChoice =
    disclosureResult published binding rightSource rightChoice at result
  rcases leftEffective with rfl | ⟨value, rfl, leftSuccess⟩
  · rcases rightEffective with rfl | ⟨other, rfl, rightSuccess⟩
    · simpa only [guardedDisclosureTranscript, Bool.false_eq_true, ↓reduceIte,
        List.append_assoc, List.singleton_append] using
        (runtime setup).withholdingWindow_focal_coupling leaks network roster left right
          leftRecall rightRecall leftPublished rightPublished owner focal event ticks traffic
    · simp only [disclosureResult_false, rightSuccess] at result
      cases result
  · rcases rightEffective with rfl | ⟨other, rfl, rightSuccess⟩
    · simp only [disclosureResult_false, leftSuccess] at result
      cases result
    · have values : value = other := PublicationResult.success.inj
        (leftSuccess.symm.trans (result.trans rightSuccess))
      subst other
      obtain ⟨candidate, owned, leftValid, rightValid, leftOpening, rightOpening, handled⟩ :=
        guarded_opening_handler_focal setup leaks published binding refs leftSource rightSource
          left right leftAgrees rightAgrees leftBinding rightBinding event outputEq leftCode
          rightCode leftNode rightNode leftReady rightReady leftTimely rightTimely value
          leftSuccess rightSuccess focal traffic
      simp only [guardedDisclosureTranscript, ↓reduceIte,
        leftOpening, rightOpening]
      rw [← counts]
      apply bind_congr_on_support _
      intro slot _supported
      have included := (runtime setup).openingWindow_inclusion_focal_coupling leaks network
        roster left right leftRecall rightRecall leftSerials rightSerials leftPublished
        rightPublished owner focal event candidate ⟨payload, value⟩ owned (some slot)
          (fun _ => leftValid) (fun _ => rightValid) traffic counts (fun _ => handled)
      conv_lhs => rw [runInteractionPlan_append, PMF.map_bind]
      conv_rhs => rw [runInteractionPlan_append, PMF.map_bind]
      apply bind_eq_of_map_eq _ _ _ _ included
      intro before _ after _ equal
      exact (runtime setup).settlement_focal_law leaks _ network event ticks before after
        focal equal

/-- Guarded disclosure preserves the source-view factorization of the
actual traffic. Correlated source inputs and all previous native records are
retained. The effective-choice premise is supplied by source normalization. -/
theorem guarded_disclosure_successor_factorization
    {Seed : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (valid : ∀ seed ∈ prior.support, (execution seed).application.BindingInvariant)
    (codeEq : ∀ seed, cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
        (compileChecks (published := published) refs (source seed).registry
          (source seed).revelations binding))
    (node : ∀ seed, nodeView (graph setup) event = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs (source seed).registry
        (source seed).revelations binding) outputEq (codeEq seed))
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (timely : ∀ seed ∈ prior.support,
      (execution seed).application.WithinDeadline (runtime setup) event)
    (recalled : ∀ seed ∈ prior.support, (execution seed).InputRecall (application setup leaks))
    (serials : ∀ seed ∈ prior.support, (execution seed).network.SerialsBeforeNext)
    (publishedTraffic : ∀ seed ∈ prior.support, (execution seed).network.Satisfies fun message =>
      message.id ∈ (execution seed).network.ledger.map Message.id)
    (offset : Nat) (counts : ∀ seed ∈ prior.support,
      ((execution seed).recall owner).length = offset)
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player)
    (focal : Player) (ticks : Nat) (timing : PMF (Fin (roster.count owner)))
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (config.view focal)).map fun extra => (config, extra))
    (choice : Config Player L Γ → PMF Bool)
    (effective : ∀ seed ∈ prior.support, ∀ disclose ∈ (choice (source seed)).support,
      disclose = false ∨ ∃ value : L.Val payload,
        disclose = true ∧ disclosureResult published binding (source seed) true = .success value) :
    ∃ nextNoise : DecisionView focal ((published, .publication payload) :: Γ) → PMF _,
      (prior.bind fun seed => (choice (source seed)).bind fun disclose =>
        (guardedDisclosureTranscript setup leaks network roster owner focal event ticks timing
          (execution seed) disclose).map fun extra =>
            (revealSuccessor published binding (source seed) disclose, extra)) =
      ((prior.map source).bind fun config =>
        (choice config).map (revealSuccessor published binding config)).bind fun config =>
          (nextNoise (config.view focal)).map fun extra => (config, extra) := by
  apply exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun config => config.view focal) noise factor choice
    (revealSuccessor published binding) (fun config => config.view focal)
  · intro left _ first _ right _ second _ same
    exact reveal_view_reflects focal published binding left right first second same
  · intro left leftSupport first firstSupport right rightSupport second secondSupport same traffic
    exact guarded_disclosure_transcript_congr setup leaks published binding refs
      (source left) (source right) (execution left) (execution right)
      (agree left leftSupport) (agree right rightSupport) (valid left leftSupport)
      (valid right rightSupport) event outputEq (codeEq left) (codeEq right) (node left)
      (node right) (ready left leftSupport) (ready right rightSupport) (timely left leftSupport)
      (timely right rightSupport) (recalled left leftSupport) (recalled right rightSupport)
      (serials left leftSupport) (serials right rightSupport) (publishedTraffic left leftSupport)
      (publishedTraffic right rightSupport) network roster focal ticks timing first second
      (effective left leftSupport first firstSupport)
      (effective right rightSupport second secondSupport) same traffic
      ((counts left leftSupport).trans (counts right rightSupport).symm)

end Vegas
