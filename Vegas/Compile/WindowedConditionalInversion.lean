/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationSampleOnce
import Vegas.Compile.WindowedConditionalReadiness

/-! # Support inversion for ordinary conditional-disclosure polls -/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal owner : P}
variable {replacement :
  (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name publicName : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {spec : ConditionalOpening guard}
variable {accounted : CommitmentAccounting pending
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ} {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile
  (.commit name owner guard (.reveal publicName owner name .here tail))}

/-- A supported complete ordinary conditional poll determines a supported
encoded source result and its concrete conditional submit/wait branch. -/
theorem conditional_ordinary_support_result
    (head : ConditionalHead spec plan)
    (current : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state)
    (execution polled :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster) (hother : owner ≠ focal)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (hpolled : polled ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [.player actor, .player actor]) execution).support) :
    ∃ result,
      result ∈ ((profile owner (.here guard (.reveal publicName owner name .here tail))
        ((current.current.source.toView owner).eraseEnv)).map
          (fun chosen => spec.encoding chosen.1)).support ∧
      polled ∈ (let runtime := root.windowed deadlineOf binding choice windowOf
        let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
          replacement
        let environment := runtime.blockEnvironment roster
        let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
        let payload := ApplicationImage.Payload.conditional
          (site.choice.publicationNode fresh state)
          (site.sourceRequestPayload fresh state (site.sourceField fresh state)
            (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
        (runtime.application.runPolicies players environment
          (beforeRoster.flatMap fun actor => [.player actor, .player actor]) execution).bind
            fun middle =>
              (runtime.application.playerStep owner middle (.submit payload)).bind fun submitted =>
                (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                  runtime.application.runPolicies players environment
                    (afterRoster.flatMap fun actor => [.player actor, .player actor])
                      waited).support := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  let environment := runtime.blockEnvironment roster
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let code := site.code fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state))
  let payload := fun result => ApplicationImage.Payload.conditional
    (P := P) (L := L) (site.choice.publicationNode fresh state)
    (site.sourceRequestPayload fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition result)
  let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
    (deadlineOf (site.choice.publicationNode fresh state)) disposition
    (ApplicationImage.conditionalTransport spec.secretTy)
  let kernel : FinDist (Option (L.Val spec.secretTy)) :=
    (profile owner site.choice.decision
      ((current.current.source.toView owner).eraseEnv)).map
        (fun chosen => spec.encoding chosen.1)
  have hbeforeOwner : Invocation.player owner ∉ before := by
    have hnot : owner ∉ beforeRoster := by
      intro hmem
      exact (List.nodup_append.mp (hsplit ▸ hroster)).2.2 owner hmem owner (by simp) rfl
    simp [before, hnot]
  have hencode (chosen : L.Val ty) : encoding.encode chosen = payload (spec.encoding chosen) :=
    site.choiceEncodingFor_encode fresh state (site.sourceField fresh state)
      (deadlineOf (site.choice.publicationNode fresh state)) disposition chosen
  apply runtime.application.ordinary_submit_wait_support_value
    (Choice := Option (L.Val spec.secretTy)) owner payload players environment roster
    beforeRoster afterRoster hsplit execution polled kernel
  · intro middle hmiddle
    have hinput := runtime.application.runPolicies_other_input owner
      (fun state actor command _ => by cases command; rfl)
      players environment before (by simp [before]) hbeforeOwner execution middle hmiddle
    have hrefines := runtime.runPolicies_players_refines players environment before
      (by simp [before]) execution middle checkpoint.refines hmiddle
    have hlaw := checkpoint.conditional_polls_source_law_of_input_eq head hinitial horigins
      hroster howner hother disposition hbinding environment middle hrefines hinput
    change runtime.application.runPolicies players environment [.player owner, .player owner]
      middle = (profile owner site.choice.decision
        ((current.current.source.toView owner).eraseEnv)).bind
          (fun chosen => (runtime.application.playerStep owner middle
            (.submit (encoding.encode chosen.1))).bind
              (fun submitted => runtime.application.playerStep owner submitted .wait)) at hlaw
    rw [FinDist.bind_map, hlaw]
    apply FinDist.bind_congr
    intro chosen _
    rw [hencode]
  · exact hpolled

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_support_result'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.conditional_ordinary_support_result
