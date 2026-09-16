/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ServicePredraw
import Vegas.Pending.DeviationLaw
import Vegas.Pending.DeviationActionLocality

/-! # Reducing serviced deviations to deterministic response pairs -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- If every deterministic focal-response/pure-wire pair has an exact graph
behavioral backtranslation over the entire finite input law, then an arbitrary
native focal deviation has an exact finite mixture of graph backtranslations. -/
theorem servicedGame_deviation_law_of_pure
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ Δ)
    (profile : BehavioralProfile whole) (inputs : FinDist (VEnv L Γ))
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (who : Player) (replacement : runtime.application.PlayerPolicy)
    (hPure : ∀
      (playerResponse : List runtime.application.PlayerEntry → runtime.application.View →
        runtime.application.PlayerCommand)
      (wireResponse : runtime.application.InvocationSite (.environment) → WireCommand Player),
      ∃ alternative : BehavioralPolicy who whole,
        ((runtime.servicedGame whole inputs roster reactionRounds
          (fun history view => FinDist.pure (wireResponse (history, view)))).play
          (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
            (runtime.compileProfile whole profile) who
            (fun history view => FinDist.pure (playerResponse history view)))).map
              (fun execution => execution.native.application.outcome?) =
        (inputs.bind fun input => Graph.run whole
          (Profile.update (sig := Graph.gameSignature whole) profile who alternative)
          input).map some) :
    ∃ mixture : FinDist (BehavioralPolicy who whole),
      ((runtime.servicedGame whole inputs roster reactionRounds wire).play
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile whole profile) who replacement)).map
            (fun execution => execution.native.application.outcome?) =
      mixture.bind (fun alternative =>
        (inputs.bind fun input => Graph.run whole
          (Profile.update (sig := Graph.gameSignature whole) profile who alternative)
          input).map some) := by
  let plan := runtime.servicePlan roster reactionRounds whole 0
  let schedule := plan.map ServiceInstruction.invocation
  let initials := inputs.map fun input => MessageApplication.PolicyExecution.initial
    runtime.application (MessageApplication.State.initial runtime.application
      (State.initial whole input))
  obtain ⟨responses, responseLaw⟩ :=
    runtime.exists_joint_service_response_mixture_runPolicies_setup
      (runtime.compileProfile whole profile) plan wire who schedule initials replacement
  dsimp only [initials] at responseLaw
  rw [FinDist.bind_map] at responseLaw
  let alternative (response :
      (List runtime.application.PlayerEntry → runtime.application.View →
        runtime.application.PlayerCommand) ×
      (runtime.application.InvocationSite (.environment) → WireCommand Player)) :=
    Classical.choose (hPure response.1 response.2)
  refine ⟨responses.map alternative, ?_⟩
  have mapped := congrArg
    (FinDist.map fun execution => execution.native.application.outcome?) responseLaw
  simp only [FinDist.map_bind, FinDist.bind_map] at mapped
  dsimp only [plan, schedule] at mapped
  rw [FinDist.bind_map]
  simp only [servicedGame]
  rw [FinDist.map_bind]
  refine mapped.symm.trans ?_
  apply FinDist.bind_congr
  intro response _
  rw [← Classical.choose_spec (hPure response.1 response.2)]
  simp only [servicedGame, FinDist.map_bind]
  rfl

/-- Every native unilateral deviation in the concrete serviced game has an
exact finite mixture of graph-policy backtranslations. The mixture is chosen
before the private initial state is sampled; opponents and chance retain
their original kernels. -/
theorem servicedGame_deviation_law
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ Δ)
    (profile : BehavioralProfile whole) (inputs : FinDist (VEnv L Γ))
    (unique : (Γ.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy)
    (who : Player) (replacement : runtime.application.PlayerPolicy) :
    ∃ mixture : FinDist (BehavioralPolicy who whole),
      ((runtime.servicedGame whole inputs roster reactionRounds wire).play
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile whole profile) who replacement)).map
            (fun execution => execution.native.application.outcome?) =
      mixture.bind (fun alternative =>
        (inputs.bind fun input => Graph.run whole
          (Profile.update (sig := Graph.gameSignature whole) profile who alternative)
          input).map some) := by
  apply runtime.servicedGame_deviation_law_of_pure whole profile inputs roster
    reactionRounds wire who replacement
  intro playerResponse wireResponse
  apply runtime.servicedGame_pure_deviation_law_of_locality whole profile inputs unique
    discipline who (fun history view => FinDist.pure (playerResponse history view))
    roster reactionRounds (fun history view => FinDist.pure (wireResponse (history, view)))
  exact runtime.servicePlan_reachedOwnAction_locality_pure whole profile inputs unique
    discipline who playerResponse roster reactionRounds wireResponse

end Vegas.GraphRuntime
