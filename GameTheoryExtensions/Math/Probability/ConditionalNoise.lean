/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.FinDist

/-! # Auxiliary observations conditional on an existing observation

An extra finite channel whose law depends only on an existing observation does
not change the posterior of the underlying state. Positive joint observations
are explicit; this is the finite Bayes calculation used at perturbations, not
an assertion about arbitrary off-path beliefs.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {State Observation Noise : Type*}

theorem conditional_observation_kernel (prior : FinDist State)
    (observe : State → Observation) (noise : Observation → FinDist Noise)
    (observed : Observation) (extra : Noise)
    (present : observed ∈ (prior.map observe).support)
    (possible : extra ∈ (noise observed).support) :
    let joint := prior.bind fun state =>
      (noise (observe state)).map fun signal => (state, signal)
    (joint.condOnFibre (fun pair => (observe pair.1, pair.2)) (observed, extra)).map
      Prod.fst = prior.condOnFibre observe observed := by
  classical
  dsimp only
  let joint := prior.bind fun state =>
    (noise (observe state)).map fun signal => (state, signal)
  let information := fun pair : State × Noise => (observe pair.1, pair.2)
  obtain ⟨witness, supported, equal⟩ := support_map .. ▸ present
  have oldMeets : ∃ state ∈ observe ⁻¹' {observed}, state ∈ prior.support :=
    ⟨witness, equal, supported⟩
  have meets : ∃ pair ∈ information ⁻¹' {(observed, extra)}, pair ∈ joint.support := by
    refine ⟨(witness, extra), ?_, ?_⟩
    · exact Prod.ext equal rfl
    · simp only [joint, support_bind, Set.mem_iUnion]
      refine ⟨witness, supported, ?_⟩
      rw [support_map]
      exact ⟨extra, by simpa only [equal] using possible, rfl⟩
  have mapped : joint.map information =
      (prior.map observe).bind fun observation =>
        (noise observation).map fun signal => (observation, signal) := by
    simp only [joint, information, map_bind, map_comp, bind_map, Function.comp_def]
  have mass : joint.probOf (information ⁻¹' {(observed, extra)}) =
      (prior.map observe).prob observed * (noise observed).prob extra := by
    rw [← prob_map_eq_probOf_preimage_singleton, mapped, prob_bind_map_prod]
  have noisePositive : 0 < (noise observed).prob extra := prob_pos_iff.mpr possible
  have conditional : joint.condOnFibre information (observed, extra) =
      (prior.condOnFibre observe observed).map (fun state => (state, extra)) := by
    rw [condOnFibre, dite_eq_left meets, condOnFibre, dite_eq_left oldMeets]
    apply ext_of_prob
    rintro ⟨state, signal⟩
    rw [prob_condOn, mass]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, information, Prod.mk.injEq]
    by_cases signalEq : signal = extra
    · subst signal
      rw [prob_map_of_injective (fun state => (state, extra))
        (fun _ _ same => (Prod.mk.inj same).1), prob_condOn]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases same : observe state = observed
      · rw [ite_eq_left ⟨same, True.intro⟩, ite_eq_left same]
        rw [show joint.prob (state, extra) =
          prior.prob state * (noise (observe state)).prob extra from
            prob_bind_map_prod prior (fun state => noise (observe state)) state extra]
        rw [same, ← prob_map_eq_probOf_preimage_singleton]
        exact mul_div_mul_right _ _ (ne_of_gt noisePositive)
      · rw [ite_eq_right (fun h => same h.1), ite_eq_right same]
    · rw [ite_eq_right (fun h => signalEq h.2)]
      symm
      apply prob_eq_zero_iff.mpr
      intro member
      obtain ⟨old, _, same⟩ := support_map .. ▸ member
      exact signalEq (congrArg Prod.snd same).symm
  change (joint.condOnFibre information (observed, extra)).map Prod.fst = _
  rw [conditional, map_comp]
  exact map_id _

/-- The same calculation needs channel equality only on supported states in
each original information fiber. No global factorization is supplied as a
premise: it is constructed from those finite supported fibers. -/
theorem conditional_kernel_of_fiber (prior : FinDist State)
    (observe : State → Observation) (kernel : State → FinDist Noise)
    (same : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      observe left = observe right → kernel left = kernel right)
    (observed : Observation) (extra : Noise)
    (present : ∃ state ∈ prior.support,
      observe state = observed ∧ extra ∈ (kernel state).support) :
    let joint := prior.bind fun state =>
      (kernel state).map fun signal => (state, signal)
    (joint.condOnFibre (fun pair => (observe pair.1, pair.2)) (observed, extra)).map
      Prod.fst = prior.condOnFibre observe observed := by
  classical
  let noise := fun observed =>
    if existsState : ∃ state ∈ prior.support, observe state = observed then
      kernel existsState.choose
    else kernel prior.support_nonempty.choose
  have factors (state : State) (supported : state ∈ prior.support) :
      kernel state = noise (observe state) := by
    have existsState : ∃ other ∈ prior.support, observe other = observe state :=
      ⟨state, supported, rfl⟩
    simp only [noise, dite_eq_left existsState]
    exact same state supported existsState.choose existsState.choose_spec.1
      existsState.choose_spec.2.symm
  have joint : (prior.bind fun state => (kernel state).map fun signal => (state, signal)) =
      prior.bind fun state => (noise (observe state)).map fun signal => (state, signal) := by
    apply bind_congr
    intro state supported
    rw [factors state supported]
  obtain ⟨state, supported, equal, possible⟩ := present
  have oldPresent : observed ∈ (prior.map observe).support := by
    rw [support_map]
    exact ⟨state, supported, equal⟩
  have noisePresent : extra ∈ (noise observed).support := by
    rw [← equal, ← factors state supported]
    exact possible
  dsimp only
  rw [joint]
  exact conditional_observation_kernel prior observe noise observed extra oldPresent noisePresent

/-- Conditional auxiliary noise remains ancillary after one hidden-state
transition. The new observation must determine the old observation, and the
conditional noise transition may depend on the hidden state/action only
through that new observation. Source action probabilities may depend on the
entire hidden state; no independence of source choices is assumed. -/
theorem exists_updated_observation_kernel
    {Action NextState NextObservation NextNoise : Type*}
    (prior : FinDist State) (observe : State → Observation)
    (noise : Observation → FinDist Noise) (choice : State → FinDist Action)
    (advance : State → Action → NextState) (nextObserve : NextState → NextObservation)
    (channel : State → Action → Noise → FinDist NextNoise)
    (reflects : ∀ left ∈ prior.support, ∀ leftAction ∈ (choice left).support,
      ∀ right ∈ prior.support, ∀ rightAction ∈ (choice right).support,
      nextObserve (advance left leftAction) = nextObserve (advance right rightAction) →
        observe left = observe right)
    (coupled : ∀ left ∈ prior.support, ∀ leftAction ∈ (choice left).support,
      ∀ right ∈ prior.support, ∀ rightAction ∈ (choice right).support,
      nextObserve (advance left leftAction) = nextObserve (advance right rightAction) →
      ∀ extra ∈ (noise (observe left)).support,
        channel left leftAction extra = channel right rightAction extra) :
    ∃ nextNoise : NextObservation → FinDist NextNoise,
      (prior.bind fun state => (noise (observe state)).bind fun extra =>
        (choice state).bind fun action => (channel state action extra).map fun next =>
          (advance state action, next)) =
      (prior.bind fun state => (choice state).map (advance state)).bind fun state =>
        (nextNoise (nextObserve state)).map fun extra => (state, extra) := by
  classical
  let pairs := prior.bind fun state => (choice state).map fun action => (state, action)
  let observation := fun pair : State × Action => nextObserve (advance pair.1 pair.2)
  let branch := fun pair : State × Action =>
    (noise (observe pair.1)).bind (channel pair.1 pair.2)
  have supported (pair : State × Action) (member : pair ∈ pairs.support) :
      pair.1 ∈ prior.support ∧ pair.2 ∈ (choice pair.1).support := by
    obtain ⟨state, stateSupport, member⟩ := Set.mem_iUnion₂.mp (support_bind .. ▸ member)
    obtain ⟨action, actionSupport, same⟩ := support_map .. ▸ member
    cases same
    exact ⟨stateSupport, actionSupport⟩
  have same (left : State × Action) (leftSupport : left ∈ pairs.support)
      (right : State × Action) (rightSupport : right ∈ pairs.support)
      (equal : observation left = observation right) : branch left = branch right := by
    obtain ⟨leftPrior, leftAction⟩ := supported left leftSupport
    obtain ⟨rightPrior, rightAction⟩ := supported right rightSupport
    have priorView := reflects left.1 leftPrior left.2 leftAction right.1 rightPrior right.2
      rightAction equal
    change (noise (observe left.1)).bind _ = (noise (observe right.1)).bind _
    rw [← priorView]
    exact bind_congr fun extra member => coupled left.1 leftPrior left.2 leftAction right.1
      rightPrior right.2 rightAction equal extra member
  let nextNoise := fun view =>
    if present : ∃ pair ∈ pairs.support, observation pair = view then branch present.choose
    else branch pairs.support_nonempty.choose
  have factors (pair : State × Action) (member : pair ∈ pairs.support) :
      branch pair = nextNoise (observation pair) := by
    have present : ∃ other ∈ pairs.support, observation other = observation pair :=
      ⟨pair, member, rfl⟩
    simp only [nextNoise, dite_eq_left present]
    exact same pair member present.choose present.choose_spec.1 present.choose_spec.2.symm
  refine ⟨nextNoise, ?_⟩
  calc
    _ = pairs.bind (fun pair => (branch pair).map fun extra =>
        (advance pair.1 pair.2, extra)) := by
      simp only [pairs, branch, bind_bind, bind_map, map_bind]
      apply bind_congr
      intro state _
      exact bind_comm _ _ _
    _ = pairs.bind (fun pair => (nextNoise (observation pair)).map fun extra =>
        (advance pair.1 pair.2, extra)) := by
      apply bind_congr
      intro pair member
      rw [factors pair member]
    _ = _ := by simp only [pairs, observation, bind_bind, bind_map]

/-- Readout form of the conditional-noise induction. A native state may contain
more information than its source state and auxiliary readout; that remainder
is eliminated by actual transition coupling on supported inputs. -/
theorem exists_updated_observation_kernel_of_readout
    {Native Action NextState NextObservation NextNoise : Type*}
    (law : FinDist Native) (state : Native → State) (read : Native → Noise)
    (observe : State → Observation) (noise : Observation → FinDist Noise)
    (factor : law.map (fun point => (state point, read point)) =
      (law.map state).bind fun source => (noise (observe source)).map fun extra => (source, extra))
    (choice : State → FinDist Action) (advance : State → Action → NextState)
    (nextObserve : NextState → NextObservation) (step : Native → Action → FinDist NextNoise)
    (reflects : ∀ left ∈ (law.map state).support, ∀ leftAction ∈ (choice left).support,
      ∀ right ∈ (law.map state).support, ∀ rightAction ∈ (choice right).support,
      nextObserve (advance left leftAction) = nextObserve (advance right rightAction) →
        observe left = observe right)
    (coupled : ∀ left ∈ law.support, ∀ leftAction ∈ (choice (state left)).support,
      ∀ right ∈ law.support, ∀ rightAction ∈ (choice (state right)).support,
      nextObserve (advance (state left) leftAction) =
        nextObserve (advance (state right) rightAction) →
      read left = read right → step left leftAction = step right rightAction) :
    ∃ nextNoise : NextObservation → FinDist NextNoise,
      (law.bind fun point => (choice (state point)).bind fun action =>
        (step point action).map fun extra => (advance (state point) action, extra)) =
      ((law.map state).bind fun source => (choice source).map (advance source)).bind fun source =>
        (nextNoise (nextObserve source)).map fun extra => (source, extra) := by
  classical
  let joint := (law.map state).bind fun source =>
    (noise (observe source)).map fun extra => (source, extra)
  let representative := fun source extra =>
    if present : ∃ point ∈ law.support, (state point, read point) = (source, extra) then
      present.choose else law.support_nonempty.choose
  have realizes (source : State) (sourceSupport : source ∈ (law.map state).support)
      (extra : Noise) (extraSupport : extra ∈ (noise (observe source)).support) :
      representative source extra ∈ law.support ∧
      state (representative source extra) = source ∧
      read (representative source extra) = extra := by
    have jointSupport : (source, extra) ∈ joint.support := by
      rw [show joint = _ from rfl, support_bind]
      apply Set.mem_iUnion₂.mpr
      refine ⟨source, sourceSupport, ?_⟩
      rw [support_map]
      exact ⟨extra, extraSupport, rfl⟩
    change (source, extra) ∈ ((law.map state).bind fun source =>
      (noise (observe source)).map fun extra => (source, extra)).support at jointSupport
    rw [← factor, support_map] at jointSupport
    obtain ⟨point, pointSupport, same⟩ := jointSupport
    have present : ∃ point ∈ law.support, (state point, read point) = (source, extra) :=
      ⟨point, pointSupport, same⟩
    simp only [representative, dite_eq_left present]
    exact ⟨present.choose_spec.1, (Prod.mk.inj present.choose_spec.2).1,
      (Prod.mk.inj present.choose_spec.2).2⟩
  let channel := fun source action extra => step (representative source extra) action
  have channels : ∀ left ∈ (law.map state).support,
      ∀ leftAction ∈ (choice left).support, ∀ right ∈ (law.map state).support,
      ∀ rightAction ∈ (choice right).support,
      nextObserve (advance left leftAction) = nextObserve (advance right rightAction) →
      ∀ extra ∈ (noise (observe left)).support,
        channel left leftAction extra = channel right rightAction extra := by
    intro left leftSupport leftAction leftChoice right rightSupport rightAction rightChoice
      same extra extraSupport
    obtain ⟨leftPresent, leftState, leftRead⟩ := realizes left leftSupport extra extraSupport
    have priorView := reflects left leftSupport leftAction leftChoice right rightSupport
      rightAction rightChoice same
    obtain ⟨rightPresent, rightState, rightRead⟩ := realizes right rightSupport extra
      (by rwa [← priorView])
    apply coupled _ leftPresent leftAction (by rwa [leftState]) _ rightPresent rightAction
      (by rwa [rightState])
    · simpa only [leftState, rightState] using same
    · exact leftRead.trans rightRead.symm
  obtain ⟨nextNoise, nextLaw⟩ := exists_updated_observation_kernel (law.map state) observe noise
    choice advance nextObserve channel reflects channels
  refine ⟨nextNoise, ?_⟩
  calc
    _ = joint.bind (fun pair => (choice pair.1).bind fun action =>
        (channel pair.1 action pair.2).map fun extra => (advance pair.1 action, extra)) := by
      apply bind_eq_of_map_eq law joint (fun point => (state point, read point)) id
        (factor.trans (map_id joint).symm)
      intro point pointSupport pair pairSupport equal
      obtain ⟨source, sourceSupport, member⟩ :=
        Set.mem_iUnion₂.mp (support_bind .. ▸ pairSupport)
      obtain ⟨extra, extraSupport, pairEq⟩ := support_map .. ▸ member
      cases pairEq
      have sourceEq : state point = source := (Prod.mk.inj equal).1
      have extraEq : read point = extra := (Prod.mk.inj equal).2
      obtain ⟨present, represented, readEq⟩ := realizes source sourceSupport extra extraSupport
      rw [sourceEq]
      apply bind_congr
      intro action chosen
      have steps := coupled point pointSupport action (by rwa [sourceEq])
        (representative source extra) present action (by rwa [represented])
          (by rw [sourceEq, represented]) (extraEq.trans readEq.symm)
      exact congrArg (fun selected => selected.map fun next => (advance source action, next)) steps
    _ = _ := by
      simpa only [joint, bind_bind, bind_map, channel] using nextLaw

end GameTheory.Math.Probability.FinDist
