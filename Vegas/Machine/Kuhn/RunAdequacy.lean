/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Kuhn.Distribution

/-!
# Kuhn adapter: run adequacy and outcome preservation

The run-adequacy predicates moving Kuhn results from the proof adapter onto
native bounded histories, and the bounded-outcome preservation theorems.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type} {M : Machine Player}

namespace RoundView

/-- Run adequacy needed to move Kuhn results from the proof adapter back to
native bounded histories.  The adapter is proof-facing; this predicate is the
claim that its final-history marginal is exactly the native `RoundView` run for
the corresponding legal behavioral or pure strategy. -/
def KuhnRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) : Prop :=
  let O := view.kuhnModel horizon hMenus
  (∀ behavioral : O.BehavioralProfile,
    PMF.map O.lastState (O.runDist steps behavioral) =
      view.runDist horizon steps
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)) ∧
  (∀ pure : view.BoundedPureProfile horizon,
    PMF.map O.lastState
        (O.runDistPure steps
        (view.pureProfileToKuhn horizon hMenus pure)) =
      view.runDist horizon steps
        (view.legalPureToBehavioral horizon pure))

/-- The single semantic bridge behind `KuhnRunAdequacy`: projecting the
adapter trace run to its final native history agrees with the native
history-run semantics for every adapter behavioral profile. -/
def KuhnBehavioralRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) : Prop :=
  let O := view.kuhnModel horizon hMenus
  ∀ behavioral : O.BehavioralProfile,
    PMF.map O.lastState (O.runDist steps behavioral) =
      view.runDist horizon steps
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)

theorem kuhnBehavioralRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) :
    view.KuhnBehavioralRunAdequacy horizon hMenus steps := by
  classical
  intro behavioral
  let O := view.kuhnModel horizon hMenus
  induction steps with
  | zero =>
      change PMF.map O.lastState (PMF.pure [O.init]) =
        PMF.pure (BoundedHistory.nil view horizon)
      rw [PMF.pure_map]
      change PMF.pure O.init = PMF.pure (BoundedHistory.nil view horizon)
      simp [O, kuhnModel]
  | succ steps ih =>
      change
        PMF.map O.lastState
            (Math.TraceRun.traceRun (O.stepDist behavioral) O.init
              (steps + 1)) =
          Machine.RoundView.runDist view horizon (steps + 1)
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
      rw [Math.TraceRun.traceRun_succ]
      rw [PMF.map_bind]
      conv_lhs =>
        arg 2
        ext trace
        rw [PMF.map_bind]
        arg 2
        ext next
        rw [PMF.pure_map]
        rw [ObsModelCore.lastState_append_singleton]
      conv_lhs =>
        arg 2
        ext trace
        rw [view.kuhnStepDist_eq_runDistFrom_one horizon hMenus behavioral
          trace]
        rw [PMF.bind_pure]
      change
        (Math.TraceRun.traceRun (O.stepDist behavioral) O.init steps).bind
            ((fun history =>
              BoundedHistory.runDistFrom view horizon
                (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1
                history) ∘ O.lastState) =
          Machine.RoundView.runDist view horizon (steps + 1)
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
      rw [← PMF.bind_map]
      change
        (PMF.map O.lastState (O.runDist steps behavioral)).bind
            (fun history =>
              BoundedHistory.runDistFrom view horizon
                (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1
                history) =
          Machine.RoundView.runDist view horizon (steps + 1)
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
      rw [ih]
      change
        (BoundedHistory.runDistFrom view horizon
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
            steps (BoundedHistory.nil view horizon)).bind
            (fun history =>
              BoundedHistory.runDistFrom view horizon
                (view.behavioralProfileOfKuhn horizon hMenus behavioral) 1
                history) =
          BoundedHistory.runDistFrom view horizon
            (view.behavioralProfileOfKuhn horizon hMenus behavioral)
            (steps + 1) (BoundedHistory.nil view horizon)
      rw [← BoundedHistory.runDistFrom_bind_runDistFrom
        view horizon
        (view.behavioralProfileOfKuhn horizon hMenus behavioral)
        steps 1 (BoundedHistory.nil view horizon)]

/-- Pure-profile run adequacy for arbitrary adapter pure profiles.  This is
the behavioral-to-correlated-pure counterpart of the native-pure clause in
`KuhnRunAdequacy`: an adapter pure profile may be produced by the generic Kuhn
behavioral-to-correlated-pure theorem, so it must be compared with its native
erased pure profile. -/
def KuhnAdapterPureRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) : Prop :=
  let O := view.kuhnModel horizon hMenus
  ∀ pure : O.PureProfile,
    PMF.map O.lastState (O.runDistPure steps pure) =
      view.runDist horizon steps
        (view.legalPureToBehavioral horizon
          (view.pureProfileOfKuhn horizon hMenus pure))

theorem KuhnRunAdequacy.of_behavioral
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat)
    (hAdequacy :
      view.KuhnBehavioralRunAdequacy horizon hMenus steps) :
    view.KuhnRunAdequacy horizon hMenus steps := by
  constructor
  · exact hAdequacy
  · intro pure
    let O := view.kuhnModel horizon hMenus
    have hrun := hAdequacy (O.pureToBehavioral
      (view.pureProfileToKuhn horizon hMenus pure))
    simpa [KuhnBehavioralRunAdequacy, O, ObsModelCore.runDistPure] using hrun

theorem kuhnRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) :
    view.KuhnRunAdequacy horizon hMenus steps :=
  KuhnRunAdequacy.of_behavioral view horizon hMenus steps
    (view.kuhnBehavioralRunAdequacy horizon hMenus steps)

theorem KuhnAdapterPureRunAdequacy.of_behavioral
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat)
    (hAdequacy :
      view.KuhnBehavioralRunAdequacy horizon hMenus steps) :
    view.KuhnAdapterPureRunAdequacy horizon hMenus steps := by
  intro pure
  let O := view.kuhnModel horizon hMenus
  have hrun := hAdequacy (O.pureToBehavioral pure)
  simpa [KuhnBehavioralRunAdequacy, O, ObsModelCore.runDistPure] using hrun

theorem kuhnAdapterPureRunAdequacy
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (steps : Nat) :
    view.KuhnAdapterPureRunAdequacy horizon hMenus steps :=
  KuhnAdapterPureRunAdequacy.of_behavioral view horizon hMenus steps
    (view.kuhnBehavioralRunAdequacy horizon hMenus steps)

theorem pureProfileToKuhn_pmfPi
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    Math.PMFProduct.pmfPi
        (fun player =>
          PMF.map
            (view.pureStrategyToKuhn horizon hMenus player)
            (mixed player)) =
      PMF.map
        (view.pureProfileToKuhn horizon hMenus)
        (Math.PMFProduct.pmfPi mixed) := by
  exact
    (Math.PMFProduct.pmfPi_push_coordwise
      (A := fun player => view.BoundedPureStrategy horizon player)
      (B := fun player =>
        (view.kuhnModel horizon hMenus).LocalStrategy player)
      mixed
      (fun player =>
        view.pureStrategyToKuhn horizon hMenus player)).symm

theorem boundedOutcomeFromBehavioral_eq_map_history
    (view : M.RoundView) (horizon steps : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    view.boundedOutcomeFromBehavioral horizon behavioral steps =
      PMF.map (fun history : view.BoundedHistory horizon =>
        M.outcome history.lastState.state)
        (view.runDist horizon steps behavioral) := by
  rw [boundedOutcomeFromBehavioral, boundedEventBatchTraceFromBehavioral]
  rw [PMF.map_comp]
  rfl

theorem boundedOutcomeFromPure_eq_map_history
    (view : M.RoundView) (horizon steps : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    (pure : view.BoundedPureProfile horizon) :
    view.boundedOutcomeFromPure horizon pure steps =
      PMF.map (fun history : view.BoundedHistory horizon =>
        M.outcome history.lastState.state)
        (view.runDist horizon steps
          (view.legalPureToBehavioral horizon pure)) := by
  rw [boundedOutcomeFromPure, boundedEventBatchTraceFromPure,
    boundedEventBatchTraceFromBehavioral]
  rw [PMF.map_comp]
  rfl

/-- Native option-outcome law for the canonical mixed-to-behavioral Kuhn
realizer. -/
theorem mixedPureToBehavioralProfile_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    view.boundedOutcomeFromBehavioral horizon
        (view.mixedPureToBehavioralProfile horizon hMenus mixed) steps =
      (Math.PMFProduct.pmfPi mixed).bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
  classical
  let O := view.kuhnModel horizon hMenus
  let historyOutcome : view.BoundedHistory horizon → Option M.Outcome :=
    fun history => M.outcome history.lastState.state
  let traceOutcome : List (view.BoundedHistory horizon) → Option M.Outcome :=
    fun trace => historyOutcome (O.lastState trace)
  let adapterBehavioral :=
    view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed
  have hrun :
      O.runDist steps adapterBehavioral =
        (Math.PMFProduct.pmfPi
          (view.mixedPureProfileToKuhn horizon hMenus mixed)).bind
          (O.runDistPure steps) := by
    simpa [O, adapterBehavioral] using
      view.mixedPureToBehavioralProfile_runDist
        horizon steps hMenus mixed
  have hAdequacy := view.kuhnRunAdequacy horizon hMenus steps
  have hAdeqBehavioral := hAdequacy.1 adapterBehavioral
  have hAdeqPure := hAdequacy.2
  calc
    view.boundedOutcomeFromBehavioral horizon
        (view.mixedPureToBehavioralProfile horizon hMenus mixed) steps
        =
      PMF.map historyOutcome
        (view.runDist horizon steps
          (view.mixedPureToBehavioralProfile horizon hMenus mixed)) := by
          simp [historyOutcome,
            boundedOutcomeFromBehavioral_eq_map_history]
    _ =
      PMF.map historyOutcome
        (view.runDist horizon steps
          (view.behavioralProfileOfKuhn horizon hMenus
            adapterBehavioral)) := by
          rfl
    _ =
      PMF.map historyOutcome
        (PMF.map O.lastState
          (O.runDist steps adapterBehavioral)) := by
          rw [hAdeqBehavioral]
    _ =
      PMF.map traceOutcome
        (O.runDist steps adapterBehavioral) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map traceOutcome
        ((Math.PMFProduct.pmfPi
          (view.mixedPureProfileToKuhn horizon hMenus mixed)).bind
          (O.runDistPure steps)) := by
          rw [hrun]
    _ =
      (Math.PMFProduct.pmfPi
        (view.mixedPureProfileToKuhn horizon hMenus mixed)).bind
        (fun pure =>
          PMF.map traceOutcome (O.runDistPure steps pure)) := by
          rw [PMF.map_bind]
    _ =
      (PMF.map
        (view.pureProfileToKuhn horizon hMenus)
        (Math.PMFProduct.pmfPi mixed)).bind
        (fun pure =>
          PMF.map traceOutcome (O.runDistPure steps pure)) := by
          rw [show
            Math.PMFProduct.pmfPi
                (view.mixedPureProfileToKuhn horizon hMenus mixed) =
              PMF.map
                (view.pureProfileToKuhn horizon hMenus)
                (Math.PMFProduct.pmfPi mixed) from by
                  exact
                    view.pureProfileToKuhn_pmfPi horizon hMenus mixed]
    _ =
      (Math.PMFProduct.pmfPi mixed).bind
        (fun pure =>
          PMF.map traceOutcome
            (O.runDistPure steps
              (view.pureProfileToKuhn horizon hMenus pure))) := by
          rw [PMF.bind_map]
          rfl
    _ =
      (Math.PMFProduct.pmfPi mixed).bind
        (fun pure =>
          PMF.map historyOutcome
            (view.runDist horizon steps
              (view.legalPureToBehavioral horizon pure))) := by
          apply congrArg
            (fun f =>
              (Math.PMFProduct.pmfPi mixed).bind f)
          funext pure
          rw [← hAdeqPure pure]
          rw [PMF.map_comp]
          rfl
    _ =
      (Math.PMFProduct.pmfPi mixed).bind
      (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
          apply congrArg
            (fun f =>
              (Math.PMFProduct.pmfPi mixed).bind f)
          funext pure
          rw [boundedOutcomeFromPure_eq_map_history]

open Classical in
/-- Native option-outcome unilateral-deviation law for the canonical
mixed-to-behavioral Kuhn realizer. -/
theorem mixedPureToBehavioralProfile_unilateral_deviation_optionOutcome
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
    view.boundedOutcomeFromBehavioral horizon
        (Function.update
          (view.mixedPureToBehavioralProfile horizon hMenus mixed)
          who deviation) steps =
      (Math.PMFProduct.pmfPi
        (Function.update mixed who mixedDeviation)).bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
  classical
  let O := view.kuhnModel horizon hMenus
  letI : ∀ player, Fintype (O.InfoState player) :=
    fun player => Fintype.ofFinite _
  let mixedDeviation :=
    view.behavioralStrategyToMixedPure horizon hMenus who deviation
  let mixed' := Function.update mixed who mixedDeviation
  let βsrc := view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed'
  let βorig := view.mixedPureToKuhnBehavioralProfile horizon hMenus mixed
  let βtgtCore : O.BehavioralProfile :=
    Function.update βorig who
      (view.behavioralStrategyToKuhn horizon who deviation)
  let nativeTarget : view.BoundedBehavioralProfile horizon :=
    Function.update
      (view.mixedPureToBehavioralProfile horizon hMenus mixed)
      who deviation
  have hnative :
      view.behavioralProfileOfKuhn horizon hMenus βtgtCore =
        nativeTarget := by
    funext player
    apply Subtype.ext
    funext info
    by_cases hplayer : player = who
    · subst player
      have hnativeWho : nativeTarget who = deviation := by
        simp [nativeTarget]
      rw [hnativeWho]
      change
        PMF.map Subtype.val (βtgtCore who info) =
          deviation.1 info
      have hcoreWho :
          βtgtCore who =
            view.behavioralStrategyToKuhn horizon who deviation := by
        simp [βtgtCore]
      rw [hcoreWho]
      exact view.behavioralStrategyToKuhn_map_val
        horizon who deviation info
    · have hcore :
          βtgtCore player info = βorig player info := by
        simp [βtgtCore, Function.update_of_ne hplayer]
      have hnativePlayer :
          nativeTarget player =
            view.mixedPureToBehavioralProfile horizon hMenus mixed player := by
        simp [nativeTarget, Function.update_of_ne hplayer]
      rw [hnativePlayer]
      change PMF.map Subtype.val (βtgtCore player info) =
        PMF.map Subtype.val (βorig player info)
      rw [hcore]
  have hcoreTrace :
      O.runDist steps βsrc = O.runDist steps βtgtCore := by
    simpa [O, mixedDeviation, mixed', βsrc, βorig, βtgtCore] using
      view.mixedPureToKuhnBehavioralProfile_unilateral_deviation_runDist
        horizon steps hMenus mixed who deviation
  have hAdequacy := view.kuhnRunAdequacy horizon hMenus steps
  have hsrcNative :
      view.boundedOutcomeFromBehavioral horizon
          (view.mixedPureToBehavioralProfile horizon hMenus mixed') steps =
        view.boundedOutcomeFromBehavioral horizon nativeTarget steps := by
    let historyOutcome : view.BoundedHistory horizon → Option M.Outcome :=
      fun history => M.outcome history.lastState.state
    let traceOutcome : List (view.BoundedHistory horizon) → Option M.Outcome :=
      fun trace => historyOutcome (O.lastState trace)
    have hsrcAdeq := hAdequacy.1 βsrc
    have htgtAdeq := hAdequacy.1 βtgtCore
    calc
      view.boundedOutcomeFromBehavioral horizon
          (view.mixedPureToBehavioralProfile horizon hMenus mixed') steps
          =
        PMF.map historyOutcome
          (view.runDist horizon steps
            (view.behavioralProfileOfKuhn horizon hMenus βsrc)) := by
            simp [historyOutcome,
              boundedOutcomeFromBehavioral_eq_map_history,
              mixedPureToBehavioralProfile, βsrc]
      _ =
        PMF.map historyOutcome
          (PMF.map O.lastState (O.runDist steps βsrc)) := by
            rw [hsrcAdeq]
      _ =
        PMF.map traceOutcome (O.runDist steps βsrc) := by
            rw [PMF.map_comp]
            rfl
      _ =
        PMF.map traceOutcome (O.runDist steps βtgtCore) := by
            rw [hcoreTrace]
      _ =
        PMF.map historyOutcome
          (PMF.map O.lastState (O.runDist steps βtgtCore)) := by
            rw [PMF.map_comp]
            rfl
      _ =
        PMF.map historyOutcome
          (view.runDist horizon steps nativeTarget) := by
            rw [htgtAdeq]
            rw [hnative]
      _ =
        view.boundedOutcomeFromBehavioral horizon nativeTarget steps := by
            simp [historyOutcome,
              boundedOutcomeFromBehavioral_eq_map_history]
  calc
    view.boundedOutcomeFromBehavioral horizon nativeTarget steps
        =
      view.boundedOutcomeFromBehavioral horizon
          (view.mixedPureToBehavioralProfile horizon hMenus mixed') steps :=
        hsrcNative.symm
    _ =
      (Math.PMFProduct.pmfPi mixed').bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
        exact
          view.mixedPureToBehavioralProfile_optionOutcome
            horizon steps hMenus mixed'
    _ =
      (Math.PMFProduct.pmfPi
          (Function.update mixed who mixedDeviation)).bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
        rfl

/-- Native option-outcome mixed-to-behavioral Kuhn realization. -/
theorem kuhn_mixed_to_behavioral_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player, Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (mixed :
      ∀ player, PMF (view.BoundedPureStrategy horizon player)) :
    ∃ behavioral : view.BoundedBehavioralProfile horizon,
      view.boundedOutcomeFromBehavioral horizon behavioral steps =
        (Math.PMFProduct.pmfPi mixed).bind
          (fun pure =>
            view.boundedOutcomeFromPure horizon pure steps) := by
  classical
  refine ⟨view.mixedPureToBehavioralProfile horizon hMenus mixed, ?_⟩
  exact
    view.mixedPureToBehavioralProfile_optionOutcome
      horizon steps hMenus mixed

open Classical in
/-- Convert a native legal behavioral profile to the product mixed profile over
native legal pure strategies obtained by independently sampling each player's
Kuhn-adapter localStrategy strategy. -/
noncomputable def behavioralToMixedPure
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    ∀ player, PMF (view.BoundedPureStrategy horizon player) :=
  let adapterBehavioral :=
    view.behavioralProfileToKuhn horizon hMenus behavioral
  fun player =>
    PMF.map
      (view.pureStrategyOfKuhn horizon hMenus player)
      ((view.kuhnModel horizon hMenus).behavioralToMixed
        adapterBehavioral player)

open Classical in
theorem behavioralToMixedPure_pmfPi
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    PMF.map
        (view.pureProfileOfKuhn horizon hMenus)
        ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
          (view.behavioralProfileToKuhn horizon hMenus behavioral)) =
      Math.PMFProduct.pmfPi
        (view.behavioralToMixedPure horizon hMenus behavioral) := by
  classical
  let O := view.kuhnModel horizon hMenus
  let adapterBehavioral :=
    view.behavioralProfileToKuhn horizon hMenus behavioral
  change
    PMF.map
        (fun profile : O.PureProfile =>
          fun player =>
            view.pureStrategyOfKuhn horizon hMenus player
              (profile player))
        (O.behavioralToMixedJoint adapterBehavioral) =
      Math.PMFProduct.pmfPi
        (fun player =>
          PMF.map
            (view.pureStrategyOfKuhn horizon hMenus player)
            (O.behavioralToMixed adapterBehavioral player))
  exact
    Math.PMFProduct.pmfPi_push_coordwise
      (A := fun player => O.LocalStrategy player)
      (B := fun player => view.BoundedPureStrategy horizon player)
      (O.behavioralToMixed adapterBehavioral)
      (fun player => view.pureStrategyOfKuhn horizon hMenus player)

theorem behavioralToMixedPure_update
    (view : M.RoundView) (horizon : Nat)
    (hMenus : view.MenusObservable horizon)
    [DecidableEq Player] [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon)
    (who : Player)
    (deviation : view.BoundedBehavioralStrategy horizon who) :
    view.behavioralToMixedPure horizon hMenus
        (Function.update behavioral who deviation) =
      Function.update
        (view.behavioralToMixedPure horizon hMenus behavioral)
        who
        ((view.behavioralToMixedPure horizon hMenus
          (Function.update behavioral who deviation)) who) := by
  classical
  funext player
  by_cases h : player = who
  · subst player
    rw [Function.update_self]
  · rw [Function.update_of_ne h]
    have hprofile :
        view.behavioralProfileToKuhn horizon hMenus
            (Function.update behavioral who deviation) player =
          view.behavioralProfileToKuhn horizon hMenus behavioral player := by
      funext info
      simp [behavioralProfileToKuhn, Function.update, h]
    exact congrArg
      (fun localProfile =>
        PMF.map (view.pureStrategyOfKuhn horizon hMenus player)
          (Math.PMFProduct.pmfPi localProfile))
      hprofile

open Classical in
/-- Native option-outcome behavioral-to-correlated-pure Kuhn realization for
behavioral profiles represented in the Kuhn adapter, with the exact erased
adapter distribution exposed. -/
theorem kuhn_adapterBehavioral_to_erased_correlated_pure_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (adapterBehavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile) :
    view.boundedOutcomeFromBehavioral horizon
        (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
        steps =
      (PMF.map
        (view.pureProfileOfKuhn horizon hMenus)
        ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
          adapterBehavioral)).bind fun pure =>
        view.boundedOutcomeFromPure horizon pure steps := by
  classical
  let O := view.kuhnModel horizon hMenus
  let historyOutcome : view.BoundedHistory horizon → Option M.Outcome :=
    fun history => M.outcome history.lastState.state
  let traceOutcome : List (view.BoundedHistory horizon) → Option M.Outcome :=
    fun trace => historyOutcome (O.lastState trace)
  letI :
      ∀ player info,
        Fintype (view.KuhnActionAtInfo horizon player info) :=
    fun player info => inferInstance
  let correlatedPureAdapter := O.behavioralToMixedJoint adapterBehavioral
  let erasePure : O.PureProfile → view.BoundedPureProfile horizon :=
    view.pureProfileOfKuhn horizon hMenus
  have hrun :=
    view.kuhn_behavioral_to_correlated_pure_core
      horizon steps hMenus adapterBehavioral
  have hAdequacy := view.kuhnRunAdequacy horizon hMenus steps
  have hPureAdequacy := view.kuhnAdapterPureRunAdequacy horizon hMenus steps
  have hAdeqBehavioral := hAdequacy.1 adapterBehavioral
  calc
    view.boundedOutcomeFromBehavioral horizon
        (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
        steps
        =
      PMF.map historyOutcome
        (view.runDist horizon steps
          (view.behavioralProfileOfKuhn horizon hMenus
            adapterBehavioral)) := by
          simp [historyOutcome,
            boundedOutcomeFromBehavioral_eq_map_history]
    _ =
      PMF.map historyOutcome
        (PMF.map O.lastState
          (O.runDist steps adapterBehavioral)) := by
          rw [← hAdeqBehavioral]
    _ =
      PMF.map traceOutcome
        (O.runDist steps adapterBehavioral) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map traceOutcome
        (correlatedPureAdapter.bind (O.runDistPure steps)) := by
          exact
            congrArg (PMF.map traceOutcome) hrun
    _ =
      correlatedPureAdapter.bind
        (fun pure =>
          PMF.map traceOutcome (O.runDistPure steps pure)) := by
          rw [PMF.map_bind]
    _ =
      correlatedPureAdapter.bind
        (fun pure =>
          PMF.map historyOutcome
            (view.runDist horizon steps
              (view.legalPureToBehavioral horizon
                (erasePure pure)))) := by
          apply congrArg
            (fun f => correlatedPureAdapter.bind f)
          funext pure
          rw [← hPureAdequacy pure]
          rw [PMF.map_comp]
          rfl
    _ =
      correlatedPureAdapter.bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon
            (erasePure pure) steps) := by
          apply congrArg
            (fun f => correlatedPureAdapter.bind f)
          funext pure
          rw [boundedOutcomeFromPure_eq_map_history]
    _ =
      (PMF.map erasePure correlatedPureAdapter).bind
        (fun pure =>
          view.boundedOutcomeFromPure horizon pure steps) := by
          rw [PMF.bind_map]
          rfl

/-- Native option-outcome behavioral-to-correlated-pure Kuhn realization for
behavioral profiles represented in the Kuhn adapter. The resulting distribution
is over native legal pure profiles obtained by erasing adapter pure
strategies. -/
theorem kuhn_adapterBehavioral_to_correlated_pure_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (adapterBehavioral :
      (view.kuhnModel horizon hMenus).BehavioralProfile) :
    ∃ correlated : PMF (view.BoundedPureProfile horizon),
      view.boundedOutcomeFromBehavioral horizon
          (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
          steps =
        correlated.bind fun pure =>
          view.boundedOutcomeFromPure horizon pure steps := by
  classical
  letI :
      ∀ player,
        Fintype ((view.kuhnModel horizon hMenus).InfoState player) :=
    fun player => Fintype.ofFinite _
  refine
    ⟨PMF.map
      (view.pureProfileOfKuhn horizon hMenus)
      ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
        adapterBehavioral), ?_⟩
  exact
    view.kuhn_adapterBehavioral_to_erased_correlated_pure_optionOutcome
      horizon steps hMenus adapterBehavioral

open Classical in
/-- Native option-outcome behavioral-to-product-mixed Kuhn realization for an
arbitrary native legal behavioral profile. -/
theorem kuhn_behavioral_to_mixedPure_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Fintype ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    view.boundedOutcomeFromBehavioral horizon behavioral steps =
      (Math.PMFProduct.pmfPi
        (view.behavioralToMixedPure horizon hMenus behavioral)).bind
        fun pure =>
          view.boundedOutcomeFromPure horizon pure steps := by
  classical
  let adapterBehavioral :=
    view.behavioralProfileToKuhn horizon hMenus behavioral
  calc
    view.boundedOutcomeFromBehavioral horizon behavioral steps
        =
      view.boundedOutcomeFromBehavioral horizon
        (view.behavioralProfileOfKuhn horizon hMenus adapterBehavioral)
        steps := by
          simp [adapterBehavioral]
    _ =
      (PMF.map
        (view.pureProfileOfKuhn horizon hMenus)
        ((view.kuhnModel horizon hMenus).behavioralToMixedJoint
          adapterBehavioral)).bind fun pure =>
        view.boundedOutcomeFromPure horizon pure steps := by
          exact
            view.kuhn_adapterBehavioral_to_erased_correlated_pure_optionOutcome
              horizon steps hMenus adapterBehavioral
    _ =
      (Math.PMFProduct.pmfPi
        (view.behavioralToMixedPure horizon hMenus behavioral)).bind
        fun pure =>
          view.boundedOutcomeFromPure horizon pure steps := by
          rw [view.behavioralToMixedPure_pmfPi horizon hMenus behavioral]

/-- Native option-outcome behavioral-to-correlated-pure Kuhn realization for
an arbitrary native legal behavioral profile. -/
theorem kuhn_behavioral_to_correlated_pure_optionOutcome
    (view : M.RoundView) (horizon steps : Nat)
    (hMenus : view.MenusObservable horizon)
    [Fintype Player]
    [∀ player, Fintype (Option (view.Act player))]
    [∀ player,
      Finite ((view.kuhnModel horizon hMenus).InfoState player)]
    (behavioral : view.BoundedBehavioralProfile horizon) :
    ∃ correlated : PMF (view.BoundedPureProfile horizon),
      view.boundedOutcomeFromBehavioral horizon behavioral steps =
        correlated.bind fun pure =>
          view.boundedOutcomeFromPure horizon pure steps := by
  classical
  rcases
      view.kuhn_adapterBehavioral_to_correlated_pure_optionOutcome
        horizon steps hMenus
        (view.behavioralProfileToKuhn horizon hMenus behavioral) with
    ⟨correlated, hcorrelated⟩
  refine ⟨correlated, ?_⟩
  simpa using hcorrelated


end RoundView

end Machine

end Vegas
