/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOriginalConfig
import Vegas.Pending.ReactiveResponseSampling
import Vegas.EventGraph.ConfigRestriction

/-! # Original-action reconstruction for disclosing graph policies -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem prescribedResponse_publication_true (who : Player)
    (policy : graph.BehavioralPolicy who)
    (discloses : ∀ event actor observation action,
      action ∈ (graph.normalizePolicy who policy event actor observation).support →
        ∀ payload (outputEq : graph.outputLayout event = .publication payload),
          cast (congrArg EventField.Action outputEq) action = true)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supported : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support)
    (payload : L.Ty) (outputEq : graph.outputLayout remembered.event = .publication payload) :
    cast (congrArg EventField.Action outputEq) remembered.action = true := by
  unfold prescribedReactiveResponse at supported
  split at supported
  · simp at supported
  · split at supported
    · simp at supported
    · split at supported
      · split at supported
        · split at supported
          · obtain ⟨choice, positive, image⟩ := PMF.support_map .. ▸ supported
            have same := Option.some.inj (congrArg Prod.snd image)
            cases same
            exact discloses _ _ _ choice positive payload outputEq
          · simp at supported
        · simp at supported
      · simp at supported

/-- Every retained sampled publication choice is true when its generating
normalized graph policy discloses at all publication inputs. -/
theorem prescribedReactivePosterior_publication_true (who : Player)
    (policy : graph.BehavioralPolicy who)
    (discloses : ∀ event actor observation action,
      action ∈ (graph.normalizePolicy who policy event actor observation).support →
        ∀ payload (outputEq : graph.outputLayout event = .publication payload),
          cast (congrArg EventField.Action outputEq) action = true)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    ∀ remembered, some remembered ∈ intentions →
      ∀ payload (outputEq : graph.outputLayout remembered.event = .publication payload),
        cast (congrArg EventField.Action outputEq) remembered.action = true := by
  induction consistent generalizing intentions with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      simp
  | @snoc history latest consistent positive ih =>
      obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy history latest
          positive intentions supported
      intro remembered member payload outputEq
      rw [memoryEq] at member
      rcases List.mem_append.mp member with earlier | latestMem
      · exact ih previous prior remembered earlier payload outputEq
      · have same : saved = some remembered := (List.mem_singleton.mp latestMem).symm
        subst saved
        exact prescribedResponse_publication_true runtime leaks who policy discloses history
          previous latest.beforeView latest.action remembered produced payload outputEq

/-- Reconstruction fixes a physical completion when all recorded and retained
publication actions at that event disclose. Binding and chance actions are kept
by definition. -/
theorem reactiveOriginal_eq_of_publication_true (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion)) (receipts : List (MessageId Player × Bool))
    (completion : graph.Completion)
    (physical : ∀ payload (outputEq : graph.outputLayout completion.event = .publication payload),
      cast (congrArg EventField.Action outputEq) completion.action = true)
    (retained : ∀ remembered, some remembered ∈ intentions →
      ∀ payload (outputEq : graph.outputLayout remembered.event = .publication payload),
        cast (congrArg EventField.Action outputEq) remembered.action = true) :
    runtime.reactiveOriginal leaks who history intentions receipts completion = completion := by
  cases node : nodeView graph completion.event with
  | sample => simp only [reactiveOriginal, node]
  | bind => simp only [reactiveOriginal, node]
  | resolve owner payload binding checks outputEq codeEq =>
      rcases runtime.reactiveOriginal_eq_or_retained leaks who history intentions receipts
          completion with same | ⟨remembered, member, named, same⟩
      · exact same
      · rw [same]
        rcases completion with ⟨event, action⟩
        rcases remembered with ⟨other, choice⟩
        dsimp only at named
        subst other
        have sameAction := (retained ⟨event, choice⟩ member payload outputEq).trans
          (physical payload outputEq).symm
        have actual := congrArg (cast (congrArg EventField.Action outputEq.symm)) sameAction
        have equal : choice = action := by simpa only [cast_cast, cast_eq] using actual
        cases equal
        rfl

/-- Disclosing sampled memories do not change any physical graph configuration
whose completed publication records all disclose. -/
theorem originalConfig_eq_of_publication_true (profile : graph.BehavioralProfile)
    (discloses : ∀ who event actor observation action,
      action ∈ (graph.normalizePolicy who (profile who) event actor observation).support →
        ∀ payload (outputEq : graph.outputLayout event = .publication payload),
          cast (congrArg EventField.Action outputEq) action = true)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (consistent : ∀ who, (runtime.prescribedReactivePolicy leaks who (profile who)).Consistent
      (execution.recall who)) (memories : Player → List (Option graph.Completion))
    (supported : ∀ who, memories who ∈
      ((runtime.prescribedReactiveImplementation leaks who (profile who)).posterior
        (execution.recall who)).support)
    (physical : ∀ completion ∈ execution.application.config.history,
      ∀ payload (outputEq : graph.outputLayout completion.event = .publication payload),
        cast (congrArg EventField.Action outputEq) completion.action = true) :
    runtime.originalConfig leaks execution memories = execution.application.config := by
  apply Config.eq_of_fields
  · rfl
  · rfl
  · rfl
  · change execution.application.config.history.map
      (runtime.originalCompletion leaks execution memories) = execution.application.config.history
    calc
      _ = execution.application.config.history.map id := by
        apply List.map_congr_left
        intro completion member
        unfold originalCompletion
        split
        · rfl
        · rename_i who _acting
          exact runtime.reactiveOriginal_eq_of_publication_true leaks who
            (execution.recall who) (memories who) execution.receipts completion
            (physical completion member)
            (runtime.prescribedReactivePosterior_publication_true leaks who (profile who)
              (discloses who) (consistent who) (memories who) (supported who))
      _ = _ := List.map_id _

end Vegas.EventGraphRuntime
