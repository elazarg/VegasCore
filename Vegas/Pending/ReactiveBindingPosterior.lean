/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingLikelihood
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Conditional laws for actual opaque binding phases

The actual replay roster and protected inclusion generate no additional
information about the submitted private value for a foreign player. The joint
readout retains that player's full recall and the real network, including
pending copies and sampled leaks. Correlated initial executions are allowed;
the conditional statement compares their actual initial auxiliary readout.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A lottery over private binding results is independent of the actual
foreign traffic readout after replay visits and protected inclusion. -/
theorem binding_silent_joint_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (different : focal ≠ owner) (event : graph.EventId)
    (payload : L.Ty) (prior : PMF (PublicationResult (L.Val payload))) (serial : Nat)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext) :
    let app := runtime.reactiveApplication leaks
    let phase := roster.map ServiceInstruction.player ++ [.includeLatest event owner]
    let run := fun result => runtime.runInteractionPlan leaks
      (fun _ => app.silentPolicy) network phase
        (execution.respond app owner (runtime.reactiveBinding leaks owner event payload
          result serial))
    prior.bind (fun result => (run result).map fun final =>
      (runtime.bindingTraffic leaks focal final, result)) =
      bindPairLaw ((run .failure).map (runtime.bindingTraffic leaks focal)) (fun _ => prior) := by
  intro app phase run
  have same (result : PublicationResult (L.Val payload)) :
      (run result).map (runtime.bindingTraffic leaks focal) =
        (run .failure).map (runtime.bindingTraffic leaks focal) :=
    runtime.binding_silent_inclusion_coupling leaks network roster execution execution
      recalled recalled owner focal event payload result .failure
        (fun equal => False.elim (different equal)) serial rfl published serials
  calc
    _ = prior.bind (fun result =>
        ((run .failure).map (runtime.bindingTraffic leaks focal)).map fun traffic =>
          (traffic, result)) := by
      apply bind_congr_on_support _
      intro result _supported
      simpa only [PMF.map_comp, Function.comp_def] using
        congrArg (PMF.map (fun traffic => (traffic, result))) (same result)
    _ = _ := by
      exact PMF.bind_comm prior
        ((run .failure).map (runtime.bindingTraffic leaks focal))
          (fun result traffic => PMF.pure (traffic, result))

/-- Conditioning the actual joint phase law on any foreign readout preserves
the private-result lottery. The finite-law fallback also covers absent inputs. -/
theorem binding_silent_posterior (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (different : focal ≠ owner) (event : graph.EventId)
    (payload : L.Ty) (prior : PMF (PublicationResult (L.Val payload))) (serial : Nat)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (observed : (runtime.reactiveApplication leaks).Execution) :
    let app := runtime.reactiveApplication leaks
    let phase := roster.map ServiceInstruction.player ++ [.includeLatest event owner]
    let joint := prior.bind fun result =>
      (runtime.runInteractionPlan leaks (fun _ => app.silentPolicy) network phase
        (execution.respond app owner
          (runtime.reactiveBinding leaks owner event payload result serial))).map fun final =>
            (runtime.bindingTraffic leaks focal final, result)
    (fiberPosterior joint Prod.fst (runtime.bindingTraffic leaks focal observed)).map Prod.snd =
      prior := by
  intro app phase joint
  have product := runtime.binding_silent_joint_law leaks network roster execution recalled
    owner focal different event payload prior serial published serials
  dsimp only at product
  change (fiberPosterior joint _ _).map _ = _
  rw [show joint = _ from product]
  exact fiberPosterior_snd_bindPairLaw_const _ _ _

/-- For arbitrarily correlated hidden seeds and initial executions, the actual
phase preserves the seed posterior conditional on the initial traffic readout.
The likelihood equality is proved from the runtime, not supplied as a premise. -/
theorem binding_silent_conditional_seed {Seed : Type*}
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (prior : PMF Seed)
    (execution : Seed → (runtime.reactiveApplication leaks).Execution)
    (owner focal : Player) (different : focal ≠ owner) (event : graph.EventId)
    (payload : L.Ty) (result : Seed → PublicationResult (L.Val payload)) (serial : Nat)
    (recalled : ∀ seed ∈ prior.support,
      (execution seed).InputRecall (runtime.reactiveApplication leaks))
    (published : ∀ seed ∈ prior.support, (execution seed).network.Satisfies fun message =>
      message.id ∈ (execution seed).network.ledger.map Message.id)
    (serials : ∀ seed ∈ prior.support, (execution seed).network.SerialsBeforeNext)
    (before after : (runtime.reactiveApplication leaks).Execution) :
    let app := runtime.reactiveApplication leaks
    let observe := fun seed => runtime.bindingTraffic leaks focal (execution seed)
    let phase := roster.map ServiceInstruction.player ++ [.includeLatest event owner]
    let kernel := fun seed => (runtime.runInteractionPlan leaks
      (fun _ => app.silentPolicy) network phase ((execution seed).respond app owner
        (runtime.reactiveBinding leaks owner event payload (result seed) serial))).map
          (runtime.bindingTraffic leaks focal)
    let joint := prior.bind fun seed => (kernel seed).map fun traffic => (seed, traffic)
    (∃ seed ∈ prior.support, observe seed = runtime.bindingTraffic leaks focal before ∧
      runtime.bindingTraffic leaks focal after ∈ (kernel seed).support) →
    (fiberPosterior joint (fun pair => (observe pair.1, pair.2))
      (runtime.bindingTraffic leaks focal before, runtime.bindingTraffic leaks focal after)).map
        Prod.fst = fiberPosterior prior observe (runtime.bindingTraffic leaks focal before) := by
  intro app observe phase kernel joint present
  apply conditional_kernel_of_fiber prior observe kernel
    (fun left leftSupport right rightSupport same => ?_) _ _ present
  exact runtime.binding_silent_inclusion_coupling leaks network roster
    (execution left) (execution right) (recalled left leftSupport) (recalled right rightSupport)
      owner focal event payload (result left) (result right)
        (fun equal => False.elim (different equal)) serial same
          (published left leftSupport) (serials left leftSupport)

end Vegas.EventGraphRuntime
