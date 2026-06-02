/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Kuhn.StrategyTranslation

/-!
# Kuhn adapter: distribution and mixed/behavioral profiles

Joint-action and step distribution identities, the mixed-pure to behavioral
profile constructions, unilateral-deviation run distributions, and the
mixed/behavioral core equivalences.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type} {M : Machine Player}

namespace RoundView

theorem kuhnJointActionDist_bind_eq_native
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player]
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (behavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile)
    (trace : List (view.BoundedHistory horizon))
    {β : Type} (K : JointAction view.Act → PMF β) :
    ((view.kuhnModel horizon hMenus).jointActionDist behavioral trace).bind
        (fun action => K (fun player => (action player).1)) =
      (view.jointActionDist horizon
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)
        ((view.kuhnModel horizon hMenus).lastState trace)).bind K := by
  classical
  let O := view.kuhnModel horizon hMenus
  have hnative :
      view.jointActionDist horizon
          (view.behavioralProfileOfKuhn horizon hMenus behavioral)
          (O.lastState trace) =
        Math.PMFProduct.pmfPi
          (fun player =>
            PMF.map Subtype.val
              (behavioral player (O.projectStates player trace))) := by
    change
      Math.PMFProduct.pmfPi
          (fun player =>
            PMF.map Subtype.val
              (behavioral player
                (view.reachableInfoStateOfHistory horizon player
                  (O.lastState trace)))) =
        Math.PMFProduct.pmfPi
          (fun player =>
            PMF.map Subtype.val
              (behavioral player (O.projectStates player trace)))
    congr
    funext player
    rw [kuhnModel_projectStates]
  rw [hnative]
  change
    (Math.PMFProduct.pmfPi
        (fun player => behavioral player (O.projectStates player trace))).bind
        (fun action => K (fun player => (action player).1)) =
      (Math.PMFProduct.pmfPi
        (fun player =>
          PMF.map Subtype.val
            (behavioral player (O.projectStates player trace)))).bind K
  rw [Math.PMFProduct.pmfPi_map_bind]
  rfl

theorem kuhnStepDist_eq_runDistFrom_one
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (behavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile)
    (trace : List (view.BoundedHistory horizon)) :
    (view.kuhnModel horizon hMenus).stepDist behavioral trace =
      BoundedHistory.runDistFrom view horizon
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)
        1 ((view.kuhnModel horizon hMenus).lastState trace) := by
  classical
  let O := view.kuhnModel horizon hMenus
  let h := O.lastState trace
  by_cases hterm : view.boundedTerminal horizon h.lastState
  · change
      (O.jointActionDist behavioral trace).bind
          (fun action =>
            view.kuhnStep horizon h (O.castJointAction trace action)) =
        BoundedHistory.runDistFrom view horizon
          (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1 h
    rw [BoundedHistory.runDistFrom_succ_terminal view horizon
      (view.behavioralProfileOfKuhn horizon hMenus behavioral) 0 h hterm]
    apply PMF.ext
    intro dst
    rw [PMF.bind_apply]
    by_cases hdst : dst = h
    · simp [kuhnStep_terminal, hterm, hdst]
      have hmass := PMF.tsum_coe (O.jointActionDist behavioral trace)
      rwa [tsum_fintype] at hmass
    · simp [kuhnStep_terminal, hterm, hdst]
  · change
      (O.jointActionDist behavioral trace).bind
          (fun action =>
            view.kuhnStep horizon h (O.castJointAction trace action)) =
        BoundedHistory.runDistFrom view horizon
          (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1 h
    rw [BoundedHistory.runDistFrom_succ_nonterminal view horizon
      (view.behavioralProfileOfKuhn horizon hMenus behavioral) 0 h hterm]
    rw [view.legalActionLaw_bind_eq_jointActionDist_bind horizon
      (view.behavioralProfileOfKuhn horizon hMenus behavioral) h hterm h
      (fun action =>
        (view.boundedTransition horizon h.lastState action).bind fun dst =>
          BoundedHistory.runDistFrom view horizon
            (view.behavioralProfileOfKuhn horizon hMenus behavioral) 0
            (h.extendByOutcome action dst))]
    rw [← view.kuhnJointActionDist_bind_eq_native horizon hMenus behavioral
      trace]
    apply congrArg
      (fun f =>
        (O.jointActionDist behavioral trace).bind f)
    funext action
    let joint : JointAction view.Act := fun player => (action player).1
    have hlegal :
        JointActionLegal view.Act (view.boundedActive horizon)
          (view.boundedTerminal horizon)
          (view.boundedAvailableActions horizon) h.lastState joint := by
      have hlegalCast :=
        view.kuhnJointAction_legal horizon h hterm
          (O.castJointAction trace action)
      rw [view.kuhnJointAction_castJointAction horizon hMenus trace action]
        at hlegalCast
      exact hlegalCast
    have hlegalAction :
        view.kuhnLegalAction horizon h hterm
            (O.castJointAction trace action) =
          (⟨joint, hlegal⟩ :
            view.BoundedLegalAction horizon h.lastState) := by
      apply Subtype.ext
      simpa [joint] using
        view.kuhnJointAction_castJointAction horizon hMenus trace action
    rw [dif_pos hlegal]
    rw [view.kuhnStep_nonterminal horizon h (O.castJointAction trace action)
      hterm, hlegalAction]
    rfl

/-- Default behavioral profile used only on Kuhn-adapter information states
that are unreachable under every pure profile. Reachable behavior in the
mixed-to-behavioral construction is determined by the mixed profile itself. -/
noncomputable def defaultKuhnBehavioralProfile
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon) :
    (view.kuhnModel horizon hMenus).BehavioralProfile :=
  fun player info =>
    PMF.pure (view.defaultKuhnActionAtInfo horizon hMenus player info)

/-- Push a native product-mixed pure profile into the Kuhn adapter's pure
strategy carrier. -/
noncomputable def mixedPureProfileToKuhn
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    ∀ player, PMF ((view.kuhnModel horizon hMenus).LocalStrategy player) :=
  fun player =>
    PMF.map
      (view.pureStrategyToKuhn horizon hMenus player)
      (mixed player)

/-- Canonical mixed-to-behavioral realization used by the native Kuhn bridge.

This is the explicit `ObsModelCore.mixedToBehavioralProfileWithFallback`
witness. The fallback is irrelevant on reachable adapter information states
but makes the profile total. -/
noncomputable def mixedPureToKuhnBehavioralProfile
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    (view.kuhnModel horizon hMenus).BehavioralProfile := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI :
      ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  letI :
      ∀ player info,
        Nonempty (view.KuhnActionAtInfo horizon player info) :=
    view.instNonemptyKuhnActionAtInfo horizon hMenus
  exact
    ObsModelCore.mixedToBehavioralProfileWithFallback
      (O := O)
      (view.mixedPureProfileToKuhn horizon hMenus mixed)
      (view.defaultKuhnBehavioralProfile horizon hMenus)

/-- Canonical mixed-to-behavioral realization used by the native Kuhn bridge,
erased from the proof adapter back to the native bounded behavioral-strategy
carrier. -/
noncomputable def mixedPureToBehavioralProfile
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    view.BoundedBehavioralProfile horizon :=
  view.behavioralProfileOfKuhn horizon hMenus
    (view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed)

/-- Updating one player's mixed-pure marginal leaves every other player's
Kuhn-adapter behavioral realization unchanged. -/
theorem mixedPureToKuhnBehavioralProfile_update_ne
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player))
    {who player : Player} (hne : player ≠ who)
    (τ : PMF (view.BoundedPureStrategy horizon who)) :
    view.mixedPureToKuhnBehavioralProfile horizon hMenus
        (Function.update mixed who τ) player =
      view.mixedPureToKuhnBehavioralProfile horizon hMenus
        mixed player := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI :
      ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  funext info
  let μ := view.mixedPureProfileToKuhn horizon hMenus mixed
  let τK : PMF (O.LocalStrategy who) :=
    PMF.map (view.pureStrategyToKuhn horizon hMenus who) τ
  have hμ :
      view.mixedPureProfileToKuhn horizon hMenus
          (Function.update mixed who τ) =
        Function.update μ who τK := by
    funext other
    by_cases hother : other = who
    · subst other
      simp [mixedPureProfileToKuhn, μ, τK]
    · simp [mixedPureProfileToKuhn, μ, τK, Function.update_of_ne hother]
  calc
    view.mixedPureToKuhnBehavioralProfile horizon hMenus
        (Function.update mixed who τ) player info
        =
      ObsModelCore.mixedToBehavioralProfileWithFallback (O := O)
        (Function.update μ who τK)
        (view.defaultKuhnBehavioralProfile horizon hMenus) player info := by
          simp [mixedPureToKuhnBehavioralProfile, hμ, μ, τK, O]
    _ =
      ObsModelCore.mixedToBehavioralProfileWithFallback (O := O)
        μ (view.defaultKuhnBehavioralProfile horizon hMenus) player info :=
          ObsModelCore.mixedToBehavioralProfileWithFallback_update_ne
            (O := O) μ (view.defaultKuhnBehavioralProfile horizon hMenus)
            hne τK info
    _ =
      view.mixedPureToKuhnBehavioralProfile horizon hMenus
        mixed player info := by
          simp [mixedPureToKuhnBehavioralProfile, μ, O]

/-- Updating one player's mixed-pure marginal leaves every other player's
native behavioral realization unchanged. -/
theorem mixedPureToBehavioralProfile_update_ne
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player))
    {who player : Player} (hne : player ≠ who)
    (τ : PMF (view.BoundedPureStrategy horizon who)) :
    view.mixedPureToBehavioralProfile horizon hMenus
        (Function.update mixed who τ) player =
      view.mixedPureToBehavioralProfile horizon hMenus
        mixed player := by
  apply Subtype.ext
  funext info
  have hprofile :=
    view.mixedPureToKuhnBehavioralProfile_update_ne
      horizon hMenus mixed hne τ
  exact congrArg (fun strategy => PMF.map Subtype.val (strategy info))
    hprofile

/-- The canonical mixed-to-behavioral witness has the adapter trace law
specified by Kuhn's theorem. -/
theorem mixedPureToBehavioralProfile_runDist
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    let O := view.kuhnModel horizon hMenus
    O.runDist steps
        (view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed) =
      (Math.PMFProduct.pmfPi
        (view.mixedPureProfileToKuhn horizon hMenus mixed)).bind
        (O.runDistPure steps) := by
  classical
  let O := view.kuhnModel horizon hMenus
  have hDet :
      ObsModelCore.StepActionDeterminism O :=
    view.kuhnModel_stepActionDeterminism horizon hMenus
  letI :
      ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  letI :
      ∀ player info,
        Nonempty (view.KuhnActionAtInfo horizon player info) :=
    view.instNonemptyKuhnActionAtInfo horizon hMenus
  have hLocalO :
      ∀ player, ObsModelCore.ObsLocalFeasibilityFull O player := by
    simpa [KuhnLocality, O] using
      view.kuhnLocality horizon hMenus
  have hAPL :
      ∀ player, ObsModelCore.ActionPosteriorLocal O player :=
    fun player =>
      ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
        hDet.toMassInvariant player
        (by
          intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _hsub πᵢ
          exact hLocalO player n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ πᵢ)
  simpa [O, mixedPureProfileToKuhn, mixedPureToKuhnBehavioralProfile] using
    (ObsModelCore.mixedToBehavioralProfileWithFallback_runDist
      (O := O)
      hDet.toMassInvariant
      hDet.toSupportFactorization
      hAPL
      (view.mixedPureProfileToKuhn horizon hMenus mixed)
      (view.defaultKuhnBehavioralProfile horizon hMenus)
      steps)

open Classical in
/-- Unilateral-deviation law for the canonical mixed-to-behavioral Kuhn
realizer at the adapter trace level.

Replacing one player's mixed pure component by the product mixed strategy
induced from a behavioral deviation has the same trace law as keeping the
canonical behavioral realization for the opponents and plugging in that
behavioral deviation for the deviating player. -/
theorem mixedPureToKuhnBehavioralProfile_unilateral_deviation_runDist
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player))
    (who : Player)
    (deviation : view.BoundedBehavioralStrategy horizon who) :
    let mixedDeviation :=
      view.behavioralStrategyToMixedPure horizon hMenus who deviation
    let mixed' := Function.update mixed who mixedDeviation
    let behavioralTarget :
        (view.kuhnModel horizon hMenus).BehavioralProfile :=
      Function.update
        (view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed)
        who
        (view.behavioralStrategyToKuhn horizon who deviation)
    (view.kuhnModel horizon hMenus).runDist steps
        (view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed') =
      (view.kuhnModel horizon hMenus).runDist steps behavioralTarget := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI : ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  let mixedDeviation :=
    view.behavioralStrategyToMixedPure horizon hMenus who deviation
  let mixed' := Function.update mixed who mixedDeviation
  let μ := view.mixedPureProfileToKuhn horizon hMenus mixed
  let μ' := view.mixedPureProfileToKuhn horizon hMenus mixed'
  let fallback := view.defaultKuhnBehavioralProfile horizon hMenus
  let βsrc := view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed'
  let βorig := view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed
  let βtgt : O.BehavioralProfile :=
    Function.update βorig who
      (view.behavioralStrategyToKuhn horizon who deviation)
  have hDet : ObsModelCore.StepActionDeterminism O :=
    view.kuhnModel_stepActionDeterminism horizon hMenus
  have hLocalO :
      ∀ player, ObsModelCore.ObsLocalFeasibilityFull O player := by
    simpa [KuhnLocality, O] using
      view.kuhnLocality horizon hMenus
  have hAPL :
      ∀ player, ObsModelCore.ActionPosteriorLocal O player :=
    fun player =>
      ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
        hDet.toMassInvariant player
        (by
          intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _hsub πᵢ
          exact hLocalO player n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ πᵢ)
  have hμWho :
      μ' who =
        view.behavioralStrategyToKuhnMixed horizon hMenus who deviation := by
    simp [μ', mixedPureProfileToKuhn, mixed', mixedDeviation]
  have hμOther :
      ∀ player, player ≠ who → μ' player = μ player := by
    intro player hne
    simp [μ', μ, mixedPureProfileToKuhn, mixed', Function.update_of_ne hne]
  have hrunSrc :
      ∀ m,
        O.runDist m βsrc =
          (Math.PMFProduct.pmfPi μ').bind (O.runDistPure m) := by
    intro m
    simpa [O, βsrc, μ'] using
      view.mixedPureToBehavioralProfile_runDist
        horizon m hMenus mixed'
  apply ObsModelCore.runDist_congr
    (O := O) (β₁ := βsrc) (β₂ := βtgt)
  intro m player trace htrace
  have hmix :
      ((Math.PMFProduct.pmfPi μ').bind (O.runDistPure m)) trace ≠ 0 := by
    rw [← hrunSrc m]
    exact htrace
  have hmixSum :
      ∑ pure : O.PureProfile,
        Math.PMFProduct.pmfPi μ' pure * O.runDistPure m pure trace ≠ 0 := by
    simpa only [PMF.bind_apply, tsum_fintype] using hmix
  obtain ⟨witness, _hwitnessMem, hwitnessProd⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hmixSum
  have hwitnessRun :
      O.runDistPure m witness trace ≠ 0 :=
    right_ne_zero_of_mul hwitnessProd
  have hwitnessPureRun :
      Math.ParameterizedChain.pureRun O.pureStep O.init m
          witness trace ≠ 0 := by
    simpa [O.runDistPure_eq_pureRun] using hwitnessRun
  have hsrcFactor :
      βsrc player (O.projectStates player trace) =
        ObsModelCore.mixedToBehavioralFactorAt
          (O := O) μ' player m trace witness := by
    have h :=
      ObsModelCore.mixedToBehavioralProfileWithFallback_eq_factorAt
        (O := O) hAPL μ' fallback player m trace witness
        hwitnessPureRun
    simpa [βsrc, mixedPureToKuhnBehavioralProfile, μ',
      fallback, O] using h
  by_cases hplayer : player = who
  · subst player
    have hwhoFactor :
        ObsModelCore.mixedToBehavioralFactorAt
            (O := O) μ' who m trace witness =
          view.behavioralStrategyToKuhn horizon who deviation
            (O.projectStates who trace) := by
      simpa [ObsModelCore.mixedToBehavioralFactorAt, hμWho, O] using
        view.behavioralStrategyToKuhnMixed_factorAt
          horizon hMenus who deviation m trace witness
          hwitnessPureRun
    have htgt :
        βtgt who (O.projectStates who trace) =
          view.behavioralStrategyToKuhn horizon who deviation
            (O.projectStates who trace) := by
      simp [βtgt]
    exact hsrcFactor.trans (hwhoFactor.trans htgt.symm)
  · have horigFactor :
        βorig player (O.projectStates player trace) =
          ObsModelCore.mixedToBehavioralFactorAt
            (O := O) μ player m trace witness := by
      have h :=
        ObsModelCore.mixedToBehavioralProfileWithFallback_eq_factorAt
          (O := O) hAPL μ fallback player m trace witness
          hwitnessPureRun
      simpa [βorig, mixedPureToKuhnBehavioralProfile, μ,
        fallback, O] using h
    have hfactorEq :
        ObsModelCore.mixedToBehavioralFactorAt
            (O := O) μ' player m trace witness =
          ObsModelCore.mixedToBehavioralFactorAt
            (O := O) μ player m trace witness := by
      simp [ObsModelCore.mixedToBehavioralFactorAt, hμOther player hplayer]
    calc
      βsrc player (O.projectStates player trace)
          =
        ObsModelCore.mixedToBehavioralFactorAt
          (O := O) μ' player m trace witness := hsrcFactor
      _ =
        ObsModelCore.mixedToBehavioralFactorAt
          (O := O) μ player m trace witness := hfactorEq
      _ =
        βorig player (O.projectStates player trace) := horigFactor.symm
      _ =
        βtgt player (O.projectStates player trace) := by
          simp [βtgt, hplayer]

/-- Core mixed-to-behavioral Kuhn realization for a native round view, stated
at the proof-adapter trace level.

The public game-facing theorem should compose this result with a run/outcome
adequacy theorem for the concrete `RoundView`.  The hypotheses are exactly the
generic Kuhn semantic hypotheses on the adapter model; the adapter itself does
not add another public game IR. -/
theorem kuhn_mixed_to_behavioral_core
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    ∃ behavioral : view.BoundedBehavioralProfile horizon,
      ∃ adapterBehavioral :
        (view.kuhnModel horizon hMenus).BehavioralProfile,
        behavioral = view.behavioralProfileOfKuhn horizon hMenus
          adapterBehavioral ∧
        (view.kuhnModel horizon hMenus).runDist steps
          adapterBehavioral =
          (Math.PMFProduct.pmfPi
            (fun player =>
              PMF.map
                (view.pureStrategyToKuhn horizon hMenus player)
                (mixed player))).bind
            ((view.kuhnModel horizon hMenus).runDistPure steps) := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI :
      ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  let adapterBehavioral :=
    view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed
  exact
    ⟨view.mixedPureToBehavioralProfile horizon hMenus mixed,
      adapterBehavioral, by
        simp [mixedPureToBehavioralProfile, adapterBehavioral],
      by
        simpa [mixedPureProfileToKuhn, O, adapterBehavioral] using
          view.mixedPureToBehavioralProfile_runDist
            horizon steps hMenus mixed⟩

/-- Core behavioral-to-correlated-pure Kuhn theorem for the native round-view
adapter. This is useful when analyzing behavioral strategies directly at the
adapter trace level. The produced distribution is over pure profiles jointly,
not a product mixed strategy profile. -/
theorem kuhn_behavioral_to_correlated_pure_core
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    [∀ player info,
      Fintype (view.KuhnActionAtInfo horizon player info)]
    (behavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile) :
    (view.kuhnModel horizon hMenus).runDist steps behavioral =
      ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
        behavioral).bind
        ((view.kuhnModel horizon hMenus).runDistPure steps) :=
  ObsModelCore.kuhn_behavioral_to_mixed
    (view.kuhnModel_noNontrivialInfoStateRepeat horizon hMenus)
    behavioral steps


end RoundView

end Machine

end Vegas
