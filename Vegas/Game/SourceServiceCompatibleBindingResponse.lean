/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceInformationWait
import Vegas.Game.SourceServiceBindingResponseFactorization

/-! # Actual binding draws under native information-dependent pins

The actual compatible full-menu prefix supplies focal slot freshness and local
coverage. A compiler-aligned binding checkpoint then identifies the native
immediate branch with its residual typed source draw. The same response draw
retains a WAIT or commitment tag beside its entire post-response execution.
Uniform trembles keep their actual full-menu response law. No source posterior
or source-support equation is assumed.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "runtime" => runtime service.setup
local notation "menu" => service.bounds.menu (runtime) service.leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.menu (Vegas.runtime service.setup) service.leaks)
  (initialLaw service.setup) service.horizon service.scheduler

private theorem immediate_decoded_response
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (remaining : Nat) (execution : (app).Execution)
    (trace : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (event : (graph service.setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime).eventRecorded service.leaks (execution.recall who) event = false) :
    ((service.effectiveImmediateComparator profile who
      (some (execution.recall who, execution.observe (app) who))).map
        (fun choice => choice.1.getD (⟨none⟩ : (app).Action))) =
      sourceServiceCanonicalPolicy service.setup service.leaks profile who
        (execution.recall who) (execution.observe (app) who) := by
  have rawTrace := (menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler
    trace
  obtain ⟨clear, atTurn, slots, _⟩ := service.sourceCompatibleInfo_raw_prefixFacts
    ⟨remaining, some who, execution⟩ rawTrace who compatible
  have covered : ∀ response ∈ (sourceServiceImmediatePolicy service.setup service.leaks
      service.bound profile who (execution.recall who) (execution.observe (app) who)).support,
      response ∈ (menu).actions who (execution.recall who) (execution.observe (app) who) := by
    intro response supported
    exact service.immediatePolicy_effective_of_slots profile who permitted
      ⟨remaining, some who, execution⟩ trace atTurn slots response supported
  have represented := congrArg (PMF.map (fun response : Option (app).Action =>
    response.getD ⟨none⟩)) ((menu).restrictPolicy_map_val (initialLaw service.setup)
      service.horizon service.scheduler who _ _ _ covered)
  simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at represented
  change _ = (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who
    (execution.recall who) (execution.observe (app) who)).map id at represented
  rw [PMF.map_id] at represented
  unfold effectiveImmediateComparator
  rw [represented, sourceServiceImmediatePolicy_at_event clear turn]
  exact sourceServiceCanonicalOpportunity_protected service.bound profile who event _ _
    unrecorded (service.sourceCompatibleInfo_protected_opportunity who _ _ compatible event
      turn unrecorded)

open Classical in
/-- The real native pin samples its typed source commitment and post-response
execution jointly. The binding checkpoint is the actual phase induction
resource; protection, freshness and finite-menu coverage come from this same
initialized compatible history, even with privately risky foreign prefixes. -/
theorem completedInformationWaitProfile_binding_joint_response
    (profile : BehavioralProfile service.setup.program)
    (event : (graph service.setup).EventId) (execution : (app).Execution)
    (site : BindingSource service.setup profile event execution.application.config)
    (permitted : (profile site.owner).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (remaining : Nat)
    (trace : ((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some site.owner, execution⟩))
    (compatible : service.sourceCompatibleInfo site.owner
      (some (execution.recall site.owner, execution.observe (app) site.owner)))
    (turn : execution.application.publicView.ownTurn? site.owner = some event)
    (unrecorded : (runtime).eventRecorded service.leaks (execution.recall site.owner) event = false)
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ who info, 0 ≤ weight who info) (small : ∀ who info, weight who info ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who) :
    let info := some (execution.recall site.owner, execution.observe (app) site.owner)
    let read := fun choice : (model).Choice site.owner info =>
      let response := choice.1.getD (⟨none⟩ : (app).Action)
      (bindingResponseResult? site.owner site.payload execution response,
        execution.respond (app) site.owner response)
    ((service.completedInformationWaitProfile profile weight nonnegative small delta
      deltaNonnegative deltaSmall continuation site.owner info).map read) =
      mix delta deltaNonnegative deltaSmall
        (((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler
          site.owner info).map read)
        (mix (weight site.owner info) (nonnegative site.owner info) (small site.owner info)
          (PMF.pure (none, execution.respond (app) site.owner ⟨none⟩))
          ((commitKernel site.residual (site.source.view site.owner)).map fun value =>
            (some value, execution.respond (app) site.owner
              ((runtime).reactiveBinding service.leaks site.owner event site.payload value
                (execution.application.publicView.bindingCount site.owner))))) := by
  intro info read
  have rawTrace := (menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler
    trace
  obtain ⟨_, atTurn, slots, _⟩ := service.sourceCompatibleInfo_raw_prefixFacts
    ⟨remaining, some site.owner, execution⟩ rawTrace site.owner compatible
  have fresh := canonicalSlot_fresh_of_used rawTrace site.owner atTurn slots event turn unrecorded
  have canonical := service.immediate_decoded_response profile site.owner permitted remaining
    execution trace compatible event turn unrecorded
  rw [sourceServiceCanonicalPolicy_at_event service.setup service.leaks profile site.owner
    execution event turn site.owned, BindingSource.compiled_choice execution site,
    PMF.map_comp] at canonical
  have responseEq (value : PublicationResult (L.Val site.payload)) :
      (runtime).canonicalServiceDecision service.leaks site.owner (execution.recall site.owner)
        (execution.observe (app) site.owner) event
        (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value) =
      (runtime).reactiveBinding service.leaks site.owner event site.payload value
        (execution.application.publicView.bindingCount site.owner) :=
    (runtime).canonicalServiceDecision_binding service.leaks site.owner _ _ event site.payload
      site.outputEq site.code (nodeView_eq_bind site.outputEq site.code) _
      (canonicalFreshSlot_canonical site.owner _ fresh) value
  have silentCovered : ∀ response ∈ ((app).silentPolicy (execution.recall site.owner)
      (execution.observe (app) site.owner)).support,
      response ∈ (menu).actions site.owner (execution.recall site.owner)
        (execution.observe (app) site.owner) := by
    intro response supported
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact service.bounds.canonicalActions_effective (runtime) service.leaks site.owner _ _
      (service.bounds.silence_canonical (runtime) service.leaks site.owner _ _)
  have silent := (menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon
    service.scheduler site.owner (app).silentPolicy _ _ silentCovered
  unfold completedInformationWaitProfile
  rw [ite_eq_left compatible, mix_map, mix_map]
  congr 1
  congr 1
  · have represented := congrArg (PMF.map (fun response : Option (app).Action =>
      (bindingResponseResult? site.owner site.payload execution (response.getD ⟨none⟩),
        execution.respond (app) site.owner (response.getD ⟨none⟩)))) silent
    simpa only [PMF.map_comp, Function.comp_def, ReactiveApplication.silentPolicy,
      PMF.pure_map, Option.getD_some, read, info, bindingResponseResult?,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using represented
  · change (service.effectiveImmediateComparator profile site.owner info).map
      ((fun response => (bindingResponseResult? site.owner site.payload execution response,
        execution.respond (app) site.owner response)) ∘
          (fun choice => choice.1.getD (⟨none⟩ : (app).Action))) = _
    rw [← PMF.map_comp, canonical, PMF.map_comp]
    apply map_congr_on_support
    intro value _supported
    dsimp only [Function.comp_def]
    rw [responseEq]
    apply Prod.ext
    · unfold bindingResponseResult?
      have submits : ((runtime).reactiveBinding service.leaks site.owner event site.payload
          value (execution.application.publicView.bindingCount site.owner)).transmission.isSome =
          true := by
        cases value <;> rfl
      rw [submits, ite_eq_left rfl]
      exact congrArg some ((runtime).reactiveBinding_result service.leaks site.owner event
        site.payload value _ execution fresh)
    · rfl

end Vegas.AsyncServiceSpec
