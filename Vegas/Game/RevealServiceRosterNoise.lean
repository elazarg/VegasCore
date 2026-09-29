/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterCoupling
import GameTheoryExtensions.Math.Probability.ConditionalNoise

/-! # Conditional independence through one actual roster phase

The initial finite law may correlate every private source input. Its auxiliary
traffic may already be random. The conclusion preserves the conditional-noise
invariant through the actual native phase, with source choices depending on
hidden source state and all native records retained in the auxiliary readout.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A conditional branch of the actual phase interpreter. This is a proof
kernel; the implemented policy is `Vegas.rosterPolicy`. -/
def rosterDisclosureTranscript
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (roster : List Player) (timing : PMF (Fin (roster.count owner)))
    (network : (runtime setup).NetworkPolicy leaks) (focal : Player)
    (execution : (application setup leaks).Execution) (disclose : Bool) :=
  let app := application setup leaks
  let phase := (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
    (List.replicate (event.val + 1) .tick ++ [.expire event])
  let branch := fun slot : Option (Fin (roster.count owner)) =>
    ((runtime setup).runInteractionPlan leaks
      ((runtime setup).openingWindowPlayers leaks owner event candidate raw
        (execution.recall owner).length slot) network phase execution).map
          (fun final => (app.messageView final, final.recall focal))
  if disclose then timing.bind (fun slot => branch (some slot)) else branch none

/-- The inductive source/traffic factorization is preserved by one real
revelation phase. The coupled starts may have different secret values and
arbitrary correlated noise; only equal auxiliary readouts are paired. -/
theorem roster_successor_observation_kernel
    {Seed : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
    (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (event : (graph setup).EventId) (eventRank : event.val = rank)
    (actor : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get binding) [])
    (node : nodeView (graph setup) event =
      .resolve owner payload (refs.get binding) [] outputEq codeEq)
    (prior : PMF Seed) (initial : Seed → State L setup.context)
    (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (checkpoint : ∀ seed ∈ prior.support,
      PublicCheckpoint setup leaks (initial seed) (source seed) refs rank (execution seed))
    (value : Seed → L.Val payload)
    (openable : ∀ seed ∈ prior.support, (source seed).state.get binding = .success (value seed))
    (candidate : Seed → Handle (graph setup))
    (owned : ∀ seed ∈ prior.support, (candidate seed).1 = owner)
    (associated : ∀ seed ∈ prior.support,
      (execution seed).application.accepted (refs.get binding).field = some (candidate seed))
    (valid : ∀ seed ∈ prior.support,
      (execution seed).application.candidates.lookup (candidate seed) =
        .openable ⟨payload, value seed⟩)
    (recalls : ∀ seed ∈ prior.support, (execution seed).InputRecall (application setup leaks))
    (serials : ∀ seed ∈ prior.support, (execution seed).network.SerialsBeforeNext)
    (clean : ∀ seed ∈ prior.support, (execution seed).network.Satisfies fun message =>
      message.id ∈ (execution seed).network.ledger.map Message.id)
    (granted : ∀ seed ∈ prior.support, (execution seed).application.serviceGrant = some event)
    (roster : List Player) (timing : PMF (Fin (roster.count owner)))
    (network : (runtime setup).NetworkPolicy leaks) (focal : Player)
    (noise : DecisionView focal Γ → PMF ((application setup leaks).MessageReadout ×
      List (application setup leaks).PlayerEntry))
    (factor : prior.map (fun seed => (source seed,
        ((application setup leaks).messageView (execution seed), (execution seed).recall focal))) =
      (prior.map source).bind fun config => (noise (config.view focal)).map fun extra =>
        (config, extra))
    (choice : Config Player L Γ → PMF Bool) :
    ∃ nextNoise : DecisionView focal ((published, .publication payload) :: Γ) →
        PMF ((application setup leaks).MessageReadout ×
          List (application setup leaks).PlayerEntry),
      (prior.bind fun seed => (choice (source seed)).bind fun disclose =>
        (rosterDisclosureTranscript setup leaks owner event (candidate seed)
          ⟨payload, value seed⟩ roster timing network focal (execution seed) disclose).map
            fun extra => (revealSuccessor published binding (source seed) disclose, extra)) =
      ((prior.map source).bind fun config =>
        (choice config).map (revealSuccessor published binding config)).bind fun config =>
          (nextNoise (config.view focal)).map fun extra => (config, extra) := by
  apply PMF.exists_updated_observation_kernel_of_readout prior source
    (fun seed => ((application setup leaks).messageView (execution seed),
      (execution seed).recall focal)) (fun config => config.view focal) noise factor choice
        (revealSuccessor published binding) (fun config => config.view focal)
  · intro left _ leftAction _ right _ rightAction _ same
    exact reveal_view_reflects focal published binding left right leftAction rightAction same
  · intro left leftSupport leftAction _ right rightSupport rightAction _ same equalNoise
    have leftCheckpoint := checkpoint left leftSupport
    have rightCheckpoint := checkpoint right rightSupport
    have sameChoice := reveal_choice_eq_of_view_eq focal published binding
      (source left) (source right) leftAction rightAction leftCheckpoint.emptyRegistry
        rightCheckpoint.emptyRegistry (value left) (value right) (openable left leftSupport)
          (openable right rightSupport) same
    subst rightAction
    have accepted : (execution left).application.accepted =
        (execution right).application.accepted :=
      leftCheckpoint.accepted.trans rightCheckpoint.accepted.symm
    have candidateEq : candidate left = candidate right := by
      apply Option.some.inj
      exact (associated left leftSupport).symm.trans
        ((congrFun accepted (refs.get binding).field).trans (associated right rightSupport))
    have messages := congrArg Prod.fst equalNoise
    have recall := congrArg Prod.snd equalNoise
    have fixed (slot : Option (Fin (roster.count owner)))
        (sameDisclosure : slot.isSome = leftAction) :
        (((runtime setup).runInteractionPlan leaks
          ((runtime setup).openingWindowPlayers leaks owner event (candidate left)
            ⟨payload, value left⟩ ((execution left).recall owner).length slot) network
          ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
            (List.replicate (event.val + 1) .tick ++ [.expire event])) (execution left)).map
              (fun final =>
                ((application setup leaks).messageView final, final.recall focal))) =
        (((runtime setup).runInteractionPlan leaks
          ((runtime setup).openingWindowPlayers leaks owner event (candidate right)
            ⟨payload, value right⟩ ((execution right).recall owner).length slot) network
          ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
            (List.replicate (event.val + 1) .tick ++ [.expire event])) (execution right)).map
              (fun final =>
                ((application setup leaks).messageView final, final.recall focal))) := by
      have coupled := leftCheckpoint.reveal_scheduled_coupling rightCheckpoint published binding
        event eventRank actor outputEq codeEq node (value left) (value right)
          (openable left leftSupport) (openable right rightSupport) (candidate left)
          (owned left leftSupport) (associated left leftSupport)
          (by rw [candidateEq]; exact associated right rightSupport)
          (valid left leftSupport) (by rw [candidateEq]; exact valid right rightSupport)
          roster slot network focal (recalls left leftSupport) (recalls right rightSupport)
          (serials left leftSupport) (serials right rightSupport) (clean left leftSupport)
          (clean right rightSupport)
          ((granted left leftSupport).trans (granted right rightSupport).symm)
          messages recall (by rwa [sameDisclosure])
      simpa only [candidateEq] using coupled
    cases leftAction with
    | false => exact fixed none rfl
    | true =>
        change timing.bind _ = timing.bind _
        exact bind_congr_on_support _ fun slot _ => fixed (some slot) rfl

end Vegas
