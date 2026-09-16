/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PolicyLaws
import Vegas.Pending.StepLaw
import Vegas.Pending.BindingProvenance
import Interaction.MessageApplicationImmediateService

/-! # Prescribed disclosure through the actual message runner

A remembered graph disclosure is implemented by a verified opening when the
public guard precheck succeeds, and by the uniform withhold packet otherwise.
Both cases install exactly the graph's accepted result. Successful opening
material is derived from the origin-indexed execution invariant; explicit
failures need no opening.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- Once its private disclosure choice is recorded, the compiled policy's
entire next command is a function of the accepted graph result and public
addressing. In particular two private causes of failure have the same command,
and a successful opening contains exactly the published value. -/
theorem compileAt_resolve_result
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner
      (.resolve outputName owner bindingName fresh source checks tail))
    (history : List (Entry runtime)) (native : runtime.application.State)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt : Nat) (disclose : Bool)
    (application : native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (remembered : rememberedDisclosure history site = some disclose)
    (unsubmitted : submittedAt history site = false) :
    compileAt runtime owner whole
      (.resolve outputName owner bindingName fresh source checks tail)
      policy site history (MessageApplication.State.observe runtime.application native owner) =
        FinDist.pure (runtime.disclosureCommand site bindingName bindings
          (acceptedResult source checks ideal disclose)) := by
  obtain ⟨state, pool, receipts⟩ := native
  dsimp only at application
  subst state
  have observed : (observe owner ideal).cells.get source = some (ideal.get source) := by
    simp [observe, Env.get]
  cases disclose with
  | false =>
      simp [compileAt, MessageApplication.State.observe, GraphRuntime.application,
        State.playerView, remembered, unsubmitted, acceptedResult, proposedResult,
        disclosureCommand]
  | true =>
      have precheck := acceptedProposal_eq_acceptedResult source checks ideal true
      simp only [proposedResult, if_true] at precheck
      simp [compileAt, MessageApplication.State.observe, GraphRuntime.application,
        State.playerView, remembered, unsubmitted, observed, precheck]

/-- The prescribed second disclosure invocation emits an accepted packet with
the graph result. Rejected values need no opening and are not put on the wire. -/
theorem exists_compiled_resolve_submission
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner
      (.resolve outputName owner bindingName fresh source checks tail))
    (history : List (Entry runtime)) (native : runtime.application.State)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt serial : Nat) (disclose : Bool)
    (application : native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (remembered : rememberedDisclosure history site = some disclose)
    (unsubmitted : submittedAt history site = false)
    (provenance : native.application.DisciplinedBindingProvenance) :
    ∃ packet : Payload Player L,
      compileAt runtime owner whole
        (.resolve outputName owner bindingName fresh source checks tail)
        policy site history (MessageApplication.State.observe runtime.application native owner) =
          FinDist.pure (.submit packet) ∧
      runtime.handle native.application ⟨(owner, serial), packet⟩ =
        some (advanceResolve tail ideal (PublicValues.ofVEnv ideal) bindings candidates
          site clock (acceptedResult source checks ideal disclose)) := by
  have compiled := compileAt_resolve_result runtime whole outputName bindingName owner
    fresh source checks tail policy history native ideal bindings candidates site clock
    enteredAt disclose application remembered unsubmitted
  cases result : acceptedResult source checks ideal disclose with
  | failure =>
      refine ⟨.withhold site, ?_, ?_⟩
      · simpa only [result, disclosureCommand] using compiled
      · rw [application]
        exact runtime.handle_resolve_withhold fresh source checks tail ideal
          (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt serial
  | success value =>
      obtain ⟨discloseEq, encoded⟩ :=
        acceptedResult_success source checks ideal disclose value result
      subst disclose
      have decoded : R.valueEquiv payload (ideal.get source) = .success value := by
        rw [encoded, Equiv.apply_symm_apply]
      obtain ⟨handle, binding, ownerEq, verified⟩ := State.resolveSource_verified
        fresh source checks tail ideal (PublicValues.ofVEnv ideal) bindings candidates
        site clock enteredAt decoded (application ▸ provenance)
      refine ⟨.opening site handle ⟨R.result payload, ideal.get source⟩, ?_, ?_⟩
      · simpa only [result, disclosureCommand, binding, encoded] using compiled
      · rw [application]
        simpa only [advanceResolve, result] using
          runtime.handle_resolve_verified fresh source checks tail ideal bindings
          candidates site clock enteredAt serial handle (ideal.get source)
          binding ownerEq verified rfl

/-- Submission and reserved inclusion implement a remembered graph disclosure
through the shared policy runner, including explicit and guard-induced failure. -/
theorem compiled_resolve_submit_include
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (policy : BehavioralPolicy owner
      (.resolve outputName owner bindingName fresh source checks tail))
    (players : Player → runtime.application.PlayerPolicy)
    (execution : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (site clock enteredAt : Nat) (disclose : Bool)
    (application : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (hplayer : players owner (execution.principalHistory owner)
      (MessageApplication.State.observe runtime.application execution.native owner) =
        compileAt runtime owner whole
          (.resolve outputName owner bindingName fresh source checks tail) policy site
          (execution.principalHistory owner)
          (MessageApplication.State.observe runtime.application execution.native owner))
    (remembered : rememberedDisclosure (execution.principalHistory owner) site = some disclose)
    (unsubmitted : submittedAt (execution.principalHistory owner) site = false)
    (provenance : execution.native.application.DisciplinedBindingProvenance)
    (serialFresh : execution.native.pool.lookup
      (owner, execution.native.pool.nextSerial owner) = none) :
    (runtime.application.runPolicies players (runtime.application.includeLatestFrom owner)
      [.player owner, .environment] execution).map (fun out => out.native.application) =
      FinDist.pure (advanceResolve tail ideal (PublicValues.ofVEnv ideal) bindings candidates
        site clock (acceptedResult source checks ideal disclose)) := by
  obtain ⟨packet, compiled, accepted⟩ := exists_compiled_resolve_submission runtime whole
    outputName bindingName owner fresh source checks tail policy
    (execution.principalHistory owner) execution.native ideal bindings candidates
    site clock enteredAt (execution.native.pool.nextSerial owner) disclose
    application remembered unsubmitted provenance
  have law := runtime.application.submit_include_accepts players owner packet execution _
    (hplayer.trans compiled) serialFresh accepted
  have projected := congrArg (fun law => law.map Prod.fst) law
  simpa only [FinDist.map_comp, FinDist.map_pure, Function.comp_def] using projected

end Vegas.GraphRuntime
