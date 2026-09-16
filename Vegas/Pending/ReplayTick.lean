/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReplayApplication

/-! # Deterministic tick replay away from chance nodes -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- At a non-sample cursor the native tick kernel is deterministic. Two states
at a focal replay checkpoint therefore retain the same focal player view,
complete focal candidate catalogue, and public view after every supported
tick. -/
theorem FocalReplayCheckpoint.tick_application_congr
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    {left right : runtime.application.PolicyExecution}
    {suffix : Graph Player L Γ Δ}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (notSample : ¬ ∃ (name : VarId) (payload : L.Ty)
        (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
        (tail : Graph Player L ((name, .pub payload) :: Γ) Δ),
      suffix = .sample name fresh law tail)
    {leftAfter rightAfter : State Player L Δ}
    (leftSupported : leftAfter ∈ (runtime.tick (.running suffix checkpoint.leftIdeal
      checkpoint.publicValues checkpoint.bindings checkpoint.leftCandidates checkpoint.pc
      checkpoint.clock checkpoint.enteredAt)).support)
    (rightSupported : rightAfter ∈ (runtime.tick (.running suffix checkpoint.rightIdeal
      checkpoint.publicValues checkpoint.bindings checkpoint.rightCandidates checkpoint.pc
      checkpoint.clock checkpoint.enteredAt)).support) :
    leftAfter.playerView focal = rightAfter.playerView focal ∧
      (fun slot => leftAfter.candidates.lookup (focal, slot)) =
        (fun slot => rightAfter.candidates.lookup (focal, slot)) ∧
      leftAfter.publicView = rightAfter.publicView := by
  have candidates :
      (fun slot => checkpoint.leftCandidates.lookup (focal, slot)) =
        fun slot => checkpoint.rightCandidates.lookup (focal, slot) := by
    funext slot
    exact checkpoint.focalCandidates slot
  cases suffix with
  | sample name fresh law tail => exact (notSample ⟨name, _, fresh, law, tail, rfl⟩).elim
  | ret payoffs =>
      simp only [GraphRuntime.tick, FinDist.mem_support_pure] at leftSupported rightSupported
      subst leftAfter
      subst rightAfter
      simp only [State.playerView, State.publicView]
      refine ⟨?_, candidates, trivial⟩
      congr 1
      · exact checkpoint.focalObservation
      · funext serial
        exact congrFun candidates (.prepared serial)
  | bind name owner fresh tail =>
      by_cases expired : runtime.deadline checkpoint.pc ≤
          checkpoint.clock + 1 - checkpoint.enteredAt
      · simp only [GraphRuntime.tick, expired, ↓reduceIte, FinDist.mem_support_pure]
          at leftSupported rightSupported
        subst leftAfter
        subst rightAfter
        simp only [advanceBindFailure, State.playerView, State.publicView]
        refine ⟨?_, candidates, trivial⟩
        congr 1
        · exact observe_cons_same focal name (.sealed owner (R.result _)) _ _ _
            checkpoint.focalObservation
        · funext serial
          exact congrFun candidates (.prepared serial)
      · simp only [GraphRuntime.tick, expired, ↓reduceIte, FinDist.mem_support_pure]
          at leftSupported rightSupported
        subst leftAfter
        subst rightAfter
        simp only [State.playerView, State.publicView]
        refine ⟨?_, candidates, trivial⟩
        congr 1
        · exact checkpoint.focalObservation
        · funext serial
          exact congrFun candidates (.prepared serial)
  | resolve outputName owner bindingName fresh source checks tail =>
      by_cases expired : runtime.deadline checkpoint.pc ≤
          checkpoint.clock + 1 - checkpoint.enteredAt
      · simp only [GraphRuntime.tick, expired, ↓reduceIte, FinDist.mem_support_pure]
          at leftSupported rightSupported
        subst leftAfter
        subst rightAfter
        simp only [advanceResolve, State.playerView, State.publicView]
        refine ⟨?_, candidates, trivial⟩
        congr 1
        · exact observe_cons_same focal outputName (.pub (R.result _)) _ _ _
            checkpoint.focalObservation
        · funext serial
          exact congrFun candidates (.prepared serial)
      · simp only [GraphRuntime.tick, expired, ↓reduceIte, FinDist.mem_support_pure]
          at leftSupported rightSupported
        subst leftAfter
        subst rightAfter
        simp only [State.playerView, State.publicView]
        refine ⟨?_, candidates, trivial⟩
        congr 1
        · exact checkpoint.focalObservation
        · funext serial
          exact congrFun candidates (.prepared serial)

/-- info: 'Vegas.GraphRuntime.FocalReplayCheckpoint.tick_application_congr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.FocalReplayCheckpoint.tick_application_congr

end Vegas.GraphRuntime
