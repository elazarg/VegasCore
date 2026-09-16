/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DisclosureAcceptance
import Vegas.Pending.Invariant

/-! # Verification of retained compiled openings -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Every pending opening emitted by a compiled sender in an initialized run
still verifies in the current candidate store. Other players and the
environment are unrestricted. -/
theorem pending_opening_verified
    (runtime : GraphRuntime Player L Δ) {origin : VCtx Player L}
    (whole : Graph Player L origin Δ) (input : VEnv L origin)
    (unique : (origin.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (owner : Player) (policy : BehavioralPolicy owner whole)
    (players : Player → runtime.application.PlayerPolicy)
    (compiledOwner : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (current : runtime.application.PolicyExecution)
    (site serial : Nat) (handle : Handle Player) (raw : Raw L)
    (supported : current ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (pending : ({ id := (owner, serial), payload := .opening site handle raw } :
      Message Player (Payload Player L)) ∈ current.native.pool.pending) :
    current.native.application.candidates.verify handle raw = true := by
  obtain ⟨front, suffix, before, submitted, splitSchedule, beforeMem, commandMem,
      stepMem, _, residual⟩ :=
    runtime.application.runPolicies_initial_pending_submission_origin players environment schedule
      (State.initial whole input) current supported _ pending
  change (.submit (.opening site handle raw) : Command runtime) ∈
    (players owner (before.principalHistory owner)
      (MessageApplication.State.observe runtime.application before.native owner)).support
    at commandMem
  have beforeFollows := runtime.runPolicies_follows whole 0 players environment front _ before
    (State.initial_follows whole input) beforeMem
  obtain ⟨target, graph, pc, ideal, values, bindings, candidates, clock, enteredAt,
      walk, beforeState⟩ := beforeFollows
  simp only [Nat.zero_add] at beforeState
  have atPhase := runtime.compilePlayerPolicy_command_atPhase whole owner policy
    (before.principalHistory owner)
    (MessageApplication.State.observe runtime.application before.native owner)
    (.submit (.opening site handle raw)) (by simpa [compiledOwner] using commandMem)
  have pcEq : pc = site := by
    change site = before.native.application.phase at atPhase
    rw [beforeState] at atPhase
    exact atPhase.symm
  subst pc
  have agreement := runtime.runPolicies_preserves_publicAgreement players environment front _ before
    (State.initial_publicAgreement whole input) beforeMem
  rw [beforeState] at agreement
  change (values : PublicValues target) =
    (PublicValues.ofVEnv ideal : PublicValues target) at agreement
  rw [agreement] at beforeState
  have provenance := runtime.runPolicies_initial_disciplinedBindingProvenance whole input unique
    discipline players environment front before beforeMem
  have localCommand : (.submit (.opening site handle raw) : Command runtime) ∈
      (compileAt runtime owner whole graph (walk.policyTail owner policy) site
        (before.principalHistory owner)
        (MessageApplication.State.observe runtime.application before.native owner)).support := by
    rw [← walk.compilePlayerPolicy_eq_suffix owner policy]
    · simpa [compiledOwner] using commandMem
    · change before.native.application.phase = site
      simp [beforeState]
  cases graph with
  | ret output =>
      simp [compileAt] at localCommand
  | sample name fresh law tail =>
      have viewPhase : (MessageApplication.State.observe runtime.application before.native
          owner).application.publicState.pc = site := by
        change before.native.application.publicView.pc = site
        simp [beforeState]
      simp [compileAt, viewPhase] at localCommand
  | bind name phaseOwner fresh tail =>
      have viewPhase : (MessageApplication.State.observe runtime.application before.native
          owner).application.publicState.pc = site := by
        change before.native.application.publicView.pc = site
        simp [beforeState]
      by_cases same : phaseOwner = owner
      · by_cases submittedAlready : submittedAt (before.principalHistory owner) site = true
        · simp [compileAt, viewPhase, same, submittedAlready] at localCommand
        · cases prepared : preparedRaw (before.principalHistory owner) site with
          | some value =>
              simp [compileAt, viewPhase, same, submittedAlready, prepared] at localCommand
          | none =>
              by_cases whoEq : (MessageApplication.State.observe runtime.application
                before.native owner).application.who = owner
              · by_cases contextEq : (MessageApplication.State.observe runtime.application
                    before.native owner).application.publicState.Γ = target
                · simp [compileAt, viewPhase, same, submittedAlready, prepared, whoEq,
                    contextEq, FinDist.support_map, Set.mem_image] at localCommand
                · simp [compileAt, viewPhase, same, submittedAlready, prepared, whoEq,
                    contextEq] at localCommand
              · simp [compileAt, viewPhase, same, submittedAlready, prepared, whoEq]
                  at localCommand
      · simp [compileAt, viewPhase, same] at localCommand
  | resolve outputName phaseOwner bindingName fresh source checks tail =>
      have viewPhase : (MessageApplication.State.observe runtime.application before.native
          owner).application.publicState.pc = site := by
        change before.native.application.publicView.pc = site
        simp [beforeState]
      have ownerEq : phaseOwner = owner := by
        by_contra different
        simp [compileAt, viewPhase, different] at localCommand
      subst phaseOwner
      obtain ⟨disclose, remembered, unsubmitted⟩ :=
        compileAt_resolve_submit_cached runtime whole outputName bindingName owner fresh
          source checks tail (walk.policyTail owner policy) (before.principalHistory owner)
          before.native ideal bindings candidates site clock enteredAt
          (.opening site handle raw) beforeState localCommand
      have compiledLaw := compileAt_resolve_result runtime whole outputName bindingName owner
        fresh source checks tail (walk.policyTail owner policy) (before.principalHistory owner)
        before.native ideal bindings candidates site clock enteredAt disclose beforeState
        remembered unsubmitted
      rw [compiledLaw] at localCommand
      simp only [FinDist.mem_support_pure] at localCommand
      cases result : acceptedResult source checks ideal disclose with
      | failure =>
          simp [result, disclosureCommand] at localCommand
      | success value =>
          simp only [result, disclosureCommand] at localCommand
          cases binding : lookupBinding bindings bindingName with
          | none => simp [binding] at localCommand
          | some sourceHandle =>
              rw [binding] at localCommand
              injection localCommand with packetEq
              simp only [Payload.opening.injEq] at packetEq
              obtain ⟨siteEq, handleEq, rawEq⟩ := packetEq
              subst handle
              subst raw
              obtain ⟨discloseEq, encoded⟩ :=
                acceptedResult_success source checks ideal disclose value result
              subst disclose
              have decoded : R.valueEquiv _ (ideal.get source) = .success value := by
                rw [encoded, Equiv.apply_symm_apply]
              obtain ⟨verifiedHandle, sourceBinding, _, verified⟩ :=
                State.resolveSource_verified fresh source checks tail ideal
                  (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt decoded
                  (beforeState ▸ provenance)
              have handleEq : verifiedHandle = sourceHandle := by
                rw [binding] at sourceBinding
                exact (Option.some.inj sourceBinding).symm
              subst verifiedHandle
              have fromBefore : current ∈ (runtime.application.runPolicies players environment
                  (.player owner :: suffix) before).support := by
                simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion]
                refine ⟨submitted, ?_, residual⟩
                simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
                exact ⟨.submit (.opening site sourceHandle
                  ⟨_, (R.valueEquiv _).symm (.success value)⟩), by simpa using commandMem,
                  stepMem⟩
              have verifiedBefore : before.native.application.candidates.verify sourceHandle
                  ⟨_, (R.valueEquiv _).symm (.success value)⟩ = true := by
                rw [beforeState]
                change candidates.verify sourceHandle
                  ⟨_, (R.valueEquiv _).symm (.success value)⟩ = true
                rw [← encoded]
                exact verified
              exact runtime.runPolicies_preserves_verification sourceHandle
                ⟨_, (R.valueEquiv _).symm (.success value)⟩ players environment
                (.player owner :: suffix) before current verifiedBefore fromBefore

end Vegas.GraphRuntime
