/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServicePrescribedCompletion

/-! # Native waiting rates indexed by actual information

At a source-compatible input this finite-menu policy mixes WAIT with the
current admitted source decision, then adds a full-support native tremble.
The waiting rate may depend on the owner's complete actual input. No latent
event-only timing lottery is asserted for this family.

A uniform upper bound on these local waiting rates retains a common fraction
of the immediate policy's choices. Vanishing rates preserve its prescribed
pointwise limits. These facts allow native completion with different waiting
likelihoods at distinct private inputs; they do not select rates that make
prescribed decisions rational.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "menu" => service.bounds.riskMenu (runtime service.setup) service.leaks
  service.bound
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound)
  (initialLaw service.setup) service.horizon service.scheduler

open Classical in
/-- A native prescribed law with information-dependent waiting and uniform
trembles. The continuation is left free outside source-compatible inputs. -/
def completedInformationWaitProfile (profile : BehavioralProfile service.setup.program)
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ who info, 0 ≤ weight who info)
    (small : ∀ who info, weight who info ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who) :
    ∀ who, (model).BehavioralPolicy who := fun who info =>
  if service.sourceCompatibleInfo who info then
    mix delta deltaNonnegative deltaSmall
      ((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler who info)
      (mix (weight who info) (nonnegative who info) (small who info)
        (((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
          (app).silentPolicy) info)
        (service.immediateProfile profile who info))
  else continuation who info

/-- Uniform native trembles give every retained choice positive likelihood
at prescribed sites, regardless of its waiting rate or source support. -/
theorem completedInformationWaitProfile_full_at_compatible
    (profile : BehavioralProfile service.setup.program)
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ who info, 0 ≤ weight who info)
    (small : ∀ who info, weight who info ≤ 1)
    (delta : ℝ) (deltaPositive : 0 < delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who)
    (who : Player) (info : (app).Info)
    (compatible : service.sourceCompatibleInfo who info) :
    FullSupport (service.completedInformationWaitProfile profile weight nonnegative small
      delta deltaPositive.le deltaSmall continuation who info) := by
  classical
  rw [completedInformationWaitProfile, ite_eq_left compatible]
  intro choice
  apply mem_support_mix_left _ _ _ deltaPositive
  let := Fintype.ofFinite ((model).Choice who info)
  exact PMF.mem_support_uniformOfFintype (α := (model).Choice who info) choice

/-- One uniform bound on information-dependent waiting supplies a common
choice factor at every prescribed input. The factor is independent of the
hidden history realizing that same information value. -/
theorem completedInformationWaitProfile_choice_lower
    (profile : BehavioralProfile service.setup.program)
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ who info, 0 ≤ weight who info)
    (small : ∀ who info, weight who info ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who)
    (bound : ℝ) (who : Player) (info : (app).Info)
    (compatible : service.sourceCompatibleInfo who info)
    (bounded : weight who info ≤ bound) (choice : (model).Choice who info) :
    ((1 - delta) * (1 - bound)) * (service.immediateProfile profile who info choice).toReal ≤
      (service.completedInformationWaitProfile profile weight nonnegative small delta
        deltaNonnegative deltaSmall continuation who info choice).toReal := by
  classical
  rw [completedInformationWaitProfile, ite_eq_left compatible, mix_apply_toReal,
    mix_apply_toReal]
  let current := (service.immediateProfile profile who info choice).toReal
  have lower : (1 - bound) * current ≤ (1 - weight who info) * current :=
    mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
  calc
    _ = (1 - delta) * ((1 - bound) * current) := by ring
    _ ≤ (1 - delta) * ((1 - weight who info) * current) :=
      mul_le_mul_of_nonneg_left lower (sub_nonneg.mpr deltaSmall)
    _ ≤ (1 - delta) *
        (weight who info * ((((menu).restrictPolicy (initialLaw service.setup) service.horizon
          service.scheduler who (app).silentPolicy) info) choice).toReal +
            (1 - weight who info) * current) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left
        (mul_nonneg (nonnegative who info) ENNReal.toReal_nonneg))
          (sub_nonneg.mpr deltaSmall)
    _ ≤ _ := le_add_of_nonneg_left (mul_nonneg deltaNonnegative ENNReal.toReal_nonneg)

/-- Arbitrary local waiting rates tending to zero retain the immediate
prescribed limit. Free continuation laws may vary without converging. -/
theorem completedInformationWaitProfile_limit_at_compatible
    (profile : BehavioralProfile service.setup.program)
    (weight : ℕ → Player → (app).Info → ℝ)
    (nonnegative : ∀ n who info, 0 ≤ weight n who info)
    (small : ∀ n who info, weight n who info ≤ 1)
    (delta : ℕ → ℝ) (deltaNonnegative : ∀ n, 0 ≤ delta n)
    (deltaSmall : ∀ n, delta n ≤ 1)
    (deltaVanishes : Tendsto delta atTop (nhds 0))
    (continuation : ℕ → ∀ who, (model).BehavioralPolicy who)
    (who : Player) (info : (app).Info)
    (compatible : service.sourceCompatibleInfo who info)
    (vanishes : Tendsto (fun n => weight n who info) atTop (nhds 0)) :
    PMFConvergesPointwise (fun n => service.completedInformationWaitProfile profile (weight n)
      (nonnegative n) (small n) (delta n) (deltaNonnegative n) (deltaSmall n)
        (continuation n) who info) (service.immediateProfile profile who info) := by
  classical
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro choice
  simp only [completedInformationWaitProfile, ite_eq_left compatible, mix_apply_toReal]
  have one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have reference := deltaVanishes.mul_const
    (((menu).uniformPolicy (initialLaw service.setup) service.horizon service.scheduler who
      info) choice).toReal
  have wait := vanishes.mul_const
    (((menu).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
      (app).silentPolicy) info choice).toReal
  have current := (one.sub vanishes).mul_const
    (service.immediateProfile profile who info choice).toReal
  have decided := (one.sub deltaVanishes).mul (wait.add current)
  convert reference.add decided using 1
  simp only [zero_mul, sub_zero, one_mul, zero_add]

private theorem immediateProfile_firstTurn_at_supported_history
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (fuel : Nat) (history : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History)
    (reached : history ∈ ((model).runBehavioral
      (service.firstTurnProfile service.horizon profile) fuel).support)
    (who : Player)
    (active : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).active history.state who) :
    service.immediateProfile profile who ((model).infoOf who history.trace) =
      service.firstTurnProfile service.horizon profile who ((model).infoOf who history.trace) := by
  have actual := service.firstTurnProfile_initialized_roundSupported service.horizon profile
    permitted fuel history reached
  have atState : (model).infoOf who history.trace = (app).observe who history.state :=
    (menu).info (initialLaw service.setup) service.horizon service.scheduler who history.trace
  obtain ⟨state, trace⟩ := history
  cases state with
  | none => cases active
  | some control =>
      have acting : control.actor = some who := active
      have supported : (app).RoundSupported (initialLaw service.setup) service.horizon
          service.scheduler (sourceServiceTurnPolicy service.setup service.leaks service.bound
            service.horizon (firstTurnTiming service.setup service.horizon) profile)
              (some control) := actual
      have input : (model).infoOf who trace =
          some (control.execution.recall who, control.execution.observe (app) who) := by
        rw [atState]
        simp only [ReactiveApplication.observe, acting, ↓reduceIte]
      rw [input]
      have physical := sourceServiceImmediatePolicy_firstTurn_roundSupported service
        service.horizon profile control who supported
      have baselineCovered : ∀ response ∈ (sourceServiceTurnPolicy service.setup service.leaks
          service.bound service.horizon (firstTurnTiming service.setup service.horizon) profile
            who (control.execution.recall who) (control.execution.observe (app) who)).support,
          response ∈ (menu).actions who (control.execution.recall who)
            (control.execution.observe (app) who) :=
        service.firstTurnProfile_response_covered service.horizon profile permitted who control
          trace supported
      have immediateCovered : ∀ response ∈ (sourceServiceImmediatePolicy service.setup
          service.leaks service.bound profile who (control.execution.recall who)
            (control.execution.observe (app) who)).support,
          response ∈ (menu).actions who (control.execution.recall who)
            (control.execution.observe (app) who) := by
        rw [physical]
        exact baselineCovered
      unfold immediateProfile firstTurnProfile
      apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
      rw [(menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon
        service.scheduler who _ _ _ immediateCovered,
        (menu).restrictPolicy_map_val (initialLaw service.setup) service.horizon
          service.scheduler who _ _ _ baselineCovered]
      exact congrArg (PMF.map some) physical

/-- The uniform local WAIT bound dominates actual initialized first-turn
choices. Its current source law and compatible classification are derived
from that same initialized support, including inactive unique choices. -/
theorem completedInformationWaitProfile_firstTurn_choice_lower
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (weight : Player → (app).Info → ℝ)
    (nonnegative : ∀ who info, 0 ≤ weight who info)
    (small : ∀ who info, weight who info ≤ 1)
    (delta : ℝ) (deltaNonnegative : 0 ≤ delta) (deltaSmall : delta ≤ 1)
    (continuation : ∀ who, (model).BehavioralPolicy who)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (boundSmall : bound ≤ 1)
    (bounded : ∀ who info, service.sourceCompatibleInfo who info → weight who info ≤ bound)
    (fuel : Nat) (history : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History)
    (reached : history ∈ ((model).runBehavioral
      (service.firstTurnProfile service.horizon profile) fuel).support)
    (who : Player) (choice : (model).Choice who ((model).infoOf who history.trace)) :
    ((1 - delta) * (1 - bound)) * ((service.firstTurnProfile service.horizon profile who
      ((model).infoOf who history.trace)) choice).toReal ≤
      (service.completedInformationWaitProfile profile weight nonnegative small delta
        deltaNonnegative deltaSmall continuation who ((model).infoOf who history.trace)
          choice).toReal := by
  classical
  by_cases active : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).active history.state who
  · have compatible := service.firstTurnProfile_sourceCompatibleInfo service.horizon profile
      permitted effective fuel history reached who active
    rw [← immediateProfile_firstTurn_at_supported_history service profile permitted fuel history
      reached who active]
    exact service.completedInformationWaitProfile_choice_lower profile weight nonnegative small
      delta deltaNonnegative deltaSmall continuation bound who _ compatible
        (bounded who _ compatible) choice
  · rw [(model).behavioral_eq_of_not_active
      (service.firstTurnProfile service.horizon profile who)
      (service.completedInformationWaitProfile profile weight nonnegative small delta
        deltaNonnegative deltaSmall continuation who) history.trace active]
    have factor : (1 - delta) * (1 - bound) ≤ 1 := by
      calc
        _ ≤ 1 * (1 - bound) :=
          mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr boundSmall)
        _ ≤ 1 := by linarith
    exact mul_le_of_le_one_left ENNReal.toReal_nonneg factor

end Vegas.AsyncServiceSpec
