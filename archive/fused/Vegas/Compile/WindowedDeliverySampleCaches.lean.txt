/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSampleCaches
import Vegas.Compile.WindowedDeliveryAlignment
import Vegas.Compile.WindowedService

/-! # Cache freshness through delivery-enabled sample blocks -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every delivery player coordinate waits at a sample instruction. -/
theorem deliveryBlockPlayer_sample_wait (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (code : SampleCode L)
    (hindex : runtime.image.instructions[history.length / 4]? = some (.sample code))
    (hlookup : runtime.image.lookup code.node = some (.sample code)) :
    runtime.deliveryBlockPlayer who base history view = FinDist.pure .wait := by
  simp only [deliveryBlockPlayer, hindex]
  split
  · rename_i hactiveAddress
    have hdue : runtime.dueExpiry? view.application = none := by
      unfold dueExpiry?
      cases hactivation : view.application.2 with
      | none => simp
      | some activation =>
          simp only [Option.bind_eq_bind, Option.bind_some]
          split
          · rename_i hactive
            have hkey : activation.key = code.node :=
              Option.some.inj (hactive.1.symm.trans hactiveAddress)
            simp [hkey, hlookup, ApplicationInstruction.expiryPayload?]
          · rfl
    have hmod : history.length % 4 = 0 ∨ history.length % 4 = 1 ∨
        history.length % 4 = 2 ∨ history.length % 4 = 3 := by omega
    rcases hmod with hmod | hmod | hmod | hmod <;>
      simp [hmod, ApplicationInstruction.submitter, hdue, relayCommand]
  · rfl

end Vegas.WindowedApplication

namespace Vegas.ApplicationPlan

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability WindowedApplication

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {state : Vegas.ToEventGraph.BuildState P L Γ}

/-- One complete delivery-enabled sample block preserves unchanged-owner cache
freshness while leaving the focal policy unrestricted. -/
theorem runPolicies_full_delivery_sample_block_preserves_unchangedCaches
    (runtime : WindowedApplication P L) (cacheImage : ApplicationImage P L)
    (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state) (roster recipients : List P)
    (hroster : roster.Nodup) (focal : P)
    (bases players : P → runtime.application.PlayerPolicy)
    (hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.deliveryBlockPlayer actor (bases actor))
    (block : Nat) (code : SampleCode L)
    (execution next : runtime.application.PolicyExecution)
    (hlookup : runtime.image.lookup code.node = some (.sample code))
    (hindex : runtime.image.instructions[block]? = some (.sample code))
    (hplayers : ∀ actor ∈ roster,
      (execution.principalHistory actor).length = 4 * block)
    (hfresh : RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution execution))
    (hnext : next ∈ (runtime.application.runPolicies players
      (runtime.deliveryBlockEnvironment roster recipients)
      (deliveryBlockInvocations roster recipients) execution).support) :
    RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution next) := by
  apply runPolicies_waiting_others_preserves_unchangedCaches runtime cacheImage
    deadlineOf plan focal players (runtime.deliveryBlockEnvironment roster recipients)
    (deliveryBlockInvocations roster recipients) execution next
  · intro actor hactor index hlo hhi history view hlength
    have hcount : (deliveryBlockInvocations roster recipients).countP
        (fun call : @Invocation P => match call with
          | .player who => decide (who = actor)
          | .environment => false) = if actor ∈ roster then 4 else 0 :=
      deliveryBlockInvocations_player_count roster recipients hroster actor
    have hhi' : index < (execution.principalHistory actor).length +
        (if actor ∈ roster then 4 else 0) := by
      convert hhi using 1
      congr 1
      exact hcount.symm
    by_cases hmem : actor ∈ roster
    · simp only [hmem, ↓reduceIte] at hhi'
      have hbaseLength := hplayers actor hmem
      have hquotient : index / 4 = block := by omega
      rw [hothers actor hactor]
      exact runtime.deliveryBlockPlayer_sample_wait actor (bases actor) history view code
        (by rw [hlength, hquotient]; exact hindex) hlookup
    · simp only [hmem, ↓reduceIte, Nat.add_zero] at hhi'
      omega
  · exact hfresh
  · exact hnext

end Vegas.ApplicationPlan
