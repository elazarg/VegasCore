/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OwnedPhaseJoint
import Vegas.Game.RevealBlockRun

/-! # The joint law of a block of concurrent reveals

A block of concurrent reveals, run from a coupled prior whose deviator traffic
is noise read from the deviator's view of the order-free key, has a final
traffic that is a channel read from the deviator's view and the hidden accepted
outputs of the honest reveals, and a successor key and final traffic again of
the factored form.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A successful resolution publishes its stored binding. -/
theorem binding_get_of_resolveOutput_success {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {owner : Player} {payload : L.Ty}
    {binding : FieldRef layout (.binding owner payload)} {checks : List (GuardCheck layout payload)}
    {store : EventGraph.Store layout} {value : L.Val payload}
    (resolved : EventCode.resolveOutput? binding checks true store = some (.success value)) :
    binding.get? store = some (.success value) := by
  unfold EventCode.resolveOutput? at resolved
  cases bound : binding.get? store with
  | none => simp [bound] at resolved
  | some proposal =>
      rw [bound] at resolved
      cases accepted : GuardCheck.allAccepted? checks store proposal with
      | none => simp [accepted] at resolved
      | some flag => cases flag <;> simp_all

/-- An honest owner has neither a turn nor a submission at an untouched event. -/
theorem blockCounters_of_untouched {owner : Player} {event : (serviceGraph setup mode).EventId}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (untouched : Untouched setup leaks event execution)
    (own : OwnSubmissionsAtTurn setup leaks execution owner) :
    blockCounters execution owner event = (0, false) := by
  have never : ∀ entry ∈ execution.logs owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
    intro entry member turn
    exact untouched owner entry member
      (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1
  unfold blockCounters
  refine Prod.ext ?_ ?_
  · apply List.countP_eq_zero.mpr
    intro entry member
    exact fun equal => never entry member (of_decide_eq_true equal)
  · apply Bool.eq_false_iff.mpr
    intro recorded
    obtain ⟨entry, member, submitted⟩ :=
      ((serviceRuntime setup mode deadline).eventRecorded_iff leaks _ event).mp recorded
    exact never entry member (own entry member event submitted)

/-- Equal normalized views agree on which events completed. -/
theorem completed_iff_of_normalize {graph : Vegas.EventGraph Player L} (who : Player)
    {left right : graph.Config}
    (same : graph.normalizeObservation who (graph.playerObserve who left) =
      graph.normalizeObservation who (graph.playerObserve who right))
    (event : graph.EventId) :
    event ∈ left.cut.completed ↔ event ∈ right.cut.completed := by
  rw [← completionOf_isSome_iff, ← completionOf_isSome_iff, normalize_present_congr who same event]

/-- **The joint law of a block.** From a coupled prior of block starts whose
deviator traffic is noise read from its normalized view of the order-free key,
a run of the block of concurrent reveals to its end has a final traffic that is
a channel read from the view and the hidden accepted outputs of the honest
reveals, and a successor key and final traffic again of the factored form, when
honest clients open a reveal exactly when its opening is accepted. -/
theorem ledgerBlock_joint {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    (flat : BlockFlat (graph := serviceGraph setup mode) start finish)
    {Seed : Type} (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (supported : ∀ seed ∈ prior.support, execution seed ∈
      ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
          turns (firstTurnTiming setup turns mode) reference) who deviation)
        (execution seed).environmentRecall.length).support)
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (begin : ∀ seed ∈ prior.support, BlockStart start finish (execution seed).application.config)
    (owners : ∀ seed ∈ prior.support, DefaultOwners (execution seed).application.config)
    (untouched : ∀ seed ∈ prior.support, ∀ event : (serviceGraph setup mode).EventId,
      start ≤ event.val → event.val < finish → Untouched setup leaks event (execution seed))
    (completes : ∀ seed ∈ prior.support, ∀ final ∈
      ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) reference) who deviation)
        (fun current => BlockDone finish current.application.config) horizon
        (execution seed)).support,
      BlockDone finish final.application.config)
    (noise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _)
    (factor : prior.map (fun seed => (runKey (execution seed).application.config,
        (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map fun seed => runKey (execution seed).application.config).bind fun current =>
        (noise (keyView who current)).map fun extra => (current, extra)) :
    ∃ (channel : Option ((serviceGraph setup mode).PlayerObservation who) ×
        ((event : (serviceGraph setup mode).EventId) →
          Option ((serviceGraph setup mode).outputLayout event).Value) → PMF _)
      (nextNoise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _)
      (endKey : RunKey (serviceGraph setup mode) → _ → RunKey (serviceGraph setup mode)),
      (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) reference) who deviation)
          (fun current => BlockDone finish current.application.config) horizon
          (execution seed)).map fun final => (runKey (execution seed).application.config,
            (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
        (prior.map fun seed => runKey (execution seed).application.config).bind
          (fun current => (channel (keyView who current, blockHidden who start finish current)).map
            fun extra => (current, extra)) ∧
      (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) reference) who deviation)
          (fun current => BlockDone finish current.application.config) horizon
          (execution seed)).map fun final => (runKey final.application.config,
            (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
        (prior.bind fun seed =>
          ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
            (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
              (firstTurnTiming setup turns mode) reference) who deviation)
            (fun current => BlockDone finish current.application.config) horizon
            (execution seed)).map fun final => runKey final.application.config).bind
          (fun current => (nextNoise (keyView who current)).map fun extra => (current, extra)) ∧
      ∀ seed ∈ prior.support, ∀ final ∈
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) reference) who deviation)
          (fun current => BlockDone finish current.application.config) horizon
          (execution seed)).support,
        runKey final.application.config = endKey (runKey (execution seed).application.config)
          ((serviceRuntime setup mode deadline).bindingTraffic leaks who final) := by
  classical
  let G := serviceGraph setup mode
  let app := serviceApplication setup mode deadline leaks
  let runtime := serviceRuntime setup mode deadline
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) reference) who deviation
  let run := fun seed => app.runUntilHorizon scheduler players
    (fun current => BlockDone finish current.application.config) horizon (execution seed)
  let traffic := runtime.bindingTraffic leaks who
  let key := fun seed => runKey (execution seed).application.config
  let view := fun current : RunKey G => (keyView who current, blockHidden who start finish current)
  let Traffic := MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView G × PublicView G
  let pick := fun extra : Traffic =>
    (⟨extra.2.2.2.2.1.who, G.normalizeObservation extra.2.2.2.2.1.who
      extra.2.2.2.2.1.observation⟩ : Σ player, G.PlayerObservation player)
  have pickFinal (final : app.Execution) : pick (traffic final) =
      ⟨who, G.normalizeObservation who (G.playerObserve who final.application.config)⟩ := rfl
  change ∃ (channel : Option (G.PlayerObservation who) ×
      ((event : G.EventId) → Option (G.outputLayout event).Value) → PMF Traffic)
    (nextNoise : Option (G.PlayerObservation who) → PMF Traffic)
    (endKey : RunKey G → Traffic → RunKey G),
    (prior.bind fun seed => (run seed).map fun final => (key seed, traffic final)) =
      (prior.map key).bind (fun current => (channel (view current)).map
        fun extra => (current, extra)) ∧
    (prior.bind fun seed => (run seed).map fun final =>
        (runKey final.application.config, traffic final)) =
      (prior.bind fun seed => (run seed).map fun final => runKey final.application.config).bind
        (fun current => (nextNoise (keyView who current)).map fun extra => (current, extra)) ∧
      ∀ seed ∈ prior.support, ∀ final ∈ (run seed).support,
        runKey final.application.config = endKey (key seed) (traffic final)
  have facts (seed : Seed) (member : seed ∈ prior.support) (final : app.Execution)
      (reached : final ∈ (run seed).support) :=
    blockRun_facts bound turns contract timely reference decides who deviation start finish
      shaped publications (execution seed) (supported seed member) (bounded seed member)
      (begin seed member).inside (untouched seed member) final reached
  let advance := fun (current : RunKey G) (choice : Σ player, G.PlayerObservation player) =>
    if found : ∃ seed ∈ prior.support, key seed = current ∧
        ∃ final ∈ (run seed).support, pick (traffic final) = choice then
      runKey found.choose_spec.2.2.choose.application.config
    else current
  have advanceSpec (seed : Seed) (member : seed ∈ prior.support) (final : app.Execution)
      (reached : final ∈ (run seed).support) :
      advance (key seed) (pick (traffic final)) = runKey final.application.config := by
    have found : ∃ other ∈ prior.support, key other = key seed ∧
        ∃ last ∈ (run other).support, pick (traffic last) = pick (traffic final) :=
      ⟨seed, member, rfl, final, reached, rfl⟩
    change (if found : ∃ other ∈ prior.support, key other = key seed ∧
        ∃ last ∈ (run other).support, pick (traffic last) = pick (traffic final) then
      runKey found.choose_spec.2.2.choose.application.config else key seed) = _
    rw [dite_eq_left found]
    obtain ⟨otherMember, keys, lastSpec⟩ := found.choose_spec
    obtain ⟨lastReached, picks⟩ := lastSpec.choose_spec
    obtain ⟨otherPath, otherSound⟩ := facts _ otherMember _ lastReached
    obtain ⟨path, sound⟩ := facts seed member final reached
    have picked : (⟨who, G.normalizeObservation who
        (G.playerObserve who lastSpec.choose.application.config)⟩ :
          Σ player, G.PlayerObservation player) =
        ⟨who, G.normalizeObservation who (G.playerObserve who final.application.config)⟩ :=
      picks
    exact blockEnd_runKey_congr publications keys otherPath path otherSound sound
      (eq_of_heq (Sigma.mk.inj picked).2)
  have atTurnOf (seed : Seed) (member : seed ∈ prior.support) :
      ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks (execution seed) owner :=
    fun owner different => (canonicalSlots_roundsFrom_reference scheduler players owner
      (firstTurnTiming setup turns mode) reference (Function.update_of_ne different _ _)
      _ (execution seed) (supported seed member)).1
  have coupled : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      view (key left) = view (key right) → traffic (execution left) = traffic (execution right) →
      (run left).map traffic = (run right).map traffic := by
    intro left leftMember right rightMember views same
    obtain ⟨viewEq, hiddenEq⟩ := Prod.mk.inj views
    change keyView who (runKey (execution left).application.config) =
      keyView who (runKey (execution right).application.config) at viewEq
    rw [keyView_runKey, keyView_runKey] at viewEq
    have normals := Option.some.inj viewEq
    have lengths : (execution left).environmentRecall.length =
        (execution right).environmentRecall.length :=
      congrArg (fun value => value.2.2.1.length) same
    obtain ⟨leftTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon
      scheduler players _ (bounded left leftMember) _ (supported left leftMember)
    obtain ⟨rightTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon
      scheduler players _ (bounded right rightMember) _ (supported right rightMember)
    have agree : AcceptedAgree who start finish (execution left).application.config
        (execution right).application.config := by
      intro event owner payload binding checks outputEq codeEq node early late pending
      have pendingRight : event ∉ (execution right).application.config.cut.completed :=
        fun done => pending ((completed_iff_of_normalize who normals event).mpr done)
      have leftReady := flat.ready (begin left leftMember).inside early late pending
      have rightReady := flat.ready (begin right rightMember).inside early late pendingRight
      have owned := nodeView_resolve_actor outputEq codeEq
      have resolvedEq (honest : owner ≠ who) :
          EventCode.resolveOutput? binding checks true (execution left).application.config.store =
            EventCode.resolveOutput? binding checks true
              (execution right).application.config.store := by
        have atEvent := congrFun hiddenEq event
        have notWho : (serviceGraph setup mode).actor? event ≠ some who :=
          fun equal => honest (Option.some.inj (owned.symm.trans equal))
        change (if start ≤ event.val ∧ event.val < finish ∧
            event ∉ (execution left).application.config.cut.completed ∧
            (serviceGraph setup mode).actor? event ≠ some who then
            acceptedOutput event (execution left).application.config.store else none) =
          (if start ≤ event.val ∧ event.val < finish ∧
            event ∉ (execution right).application.config.cut.completed ∧
            (serviceGraph setup mode).actor? event ≠ some who then
            acceptedOutput event (execution right).application.config.store else none) at atEvent
        rw [ite_eq_left ⟨early, late, pending, notWho⟩,
          ite_eq_left ⟨early, late, pendingRight, notWho⟩] at atEvent
        simp only [acceptedOutput, node] at atEvent
        exact Option.map_injective (fun first second equal => (cast_inj _).mp equal) atEvent
      refine ⟨fun field read => (execution left).application.config.read_available leftReady read,
        fun field read => (execution right).application.config.read_available rightReady read,
        fun honest => ?_, fun opened => ?_⟩
      · unfold openingAccepted
        rw [node]
        dsimp only
        rw [resolvedEq honest]
      · by_cases isWho : owner = who
        · subst isWho
          have stores := congrArg (fun observation : G.PlayerObservation owner =>
            observation.store) normals
          rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at stores
          simp only at stores
          have visibleField : G.fieldVisibleTo owner binding.field := by
            unfold EventGraph.fieldVisibleTo
            rw [binding.layout_eq]
            exact (rfl : owner = owner)
          have visible := congrFun stores binding.field
          rw [playerStore_of_visible (visible := visibleField),
            playerStore_of_visible (visible := visibleField)] at visible
          exact FieldRef.get?_congr binding _ _ visible
        · have accepted := opened.resolve_right isWho
          obtain ⟨value, resolved⟩ := resolveOutput_of_accepted node accepted
          rw [binding_get_of_resolveOutput_success resolved,
            binding_get_of_resolveOutput_success ((resolvedEq isWho) ▸ resolved)]
    have countersEq : blockCountersOn (blockWindow start finish) (execution left) =
        blockCountersOn (blockWindow start finish) (execution right) := by
      funext owner event
      unfold blockCountersOn
      by_cases inside : blockWindow (setup := setup) (mode := mode) start finish event = true
      · rw [ite_eq_left inside, ite_eq_left inside]
        have bounds : start ≤ event.val ∧ event.val < finish := by
          simpa only [blockWindow, decide_eq_true_eq] using inside
        by_cases isWho : owner = who
        · subst isWho
          have logs : (execution left).logs owner = (execution right).logs owner :=
            congrArg (fun value => value.2.2.2.1) same
          unfold blockCounters ownerTurns
          rw [logs]
        · rw [blockCounters_of_untouched (untouched left leftMember event bounds.1 bounds.2)
              (atTurnOf left leftMember owner isWho),
            blockCounters_of_untouched (untouched right rightMember event bounds.1 bounds.2)
              (atTurnOf right rightMember owner isWho)]
      · rw [ite_eq_right inside, ite_eq_right inside]
    have readouts : blockReadoutOn who (blockWindow start finish) (execution left) =
        blockReadoutOn who (blockWindow start finish) (execution right) := by
      unfold blockReadoutOn
      rw [countersEq]
      exact congrArg (fun value => (value, _)) same
    have coupledReadout := block_stopped_readoutOn_congr scheduler bound turns reference decides
      who deviation start finish shaped publications
      (horizon - (execution left).environmentRecall.length) 0 0 (execution left)
      (execution right) (by simpa only [Nat.zero_add] using leftTrace)
      (by rw [lengths]; simpa only [Nat.zero_add] using rightTrace)
      (fun _ => (begin left leftMember).inside) (fun _ => (begin right rightMember).inside)
      (honestBlockSubmissions_start who start finish _ (atTurnOf left leftMember)
        (untouched left leftMember))
      (honestBlockSubmissions_start who start finish _ (atTurnOf right rightMember)
        (untouched right rightMember)) agree readouts
    have projected := congrArg (PMF.map Prod.fst) coupledReadout
    simp only [PMF.map_comp, Function.comp_def, blockReadoutOn] at projected
    change (app.runUntil scheduler players
        (fun current => BlockDone finish current.application.config)
        (horizon - (execution left).environmentRecall.length) (execution left)).map traffic =
      (app.runUntil scheduler players
        (fun current => BlockDone finish current.application.config)
        (horizon - (execution right).environmentRecall.length) (execution right)).map traffic
    rw [← lengths]
    exact projected
  have realizedFinal (current : RunKey G) (choice : Σ player, G.PlayerObservation player)
      (realized : ∃ seed ∈ prior.support, key seed = current ∧
        ∃ extra ∈ ((run seed).map traffic).support, pick extra = choice) :
      ∃ seed ∈ prior.support, key seed = current ∧ ∃ final ∈ (run seed).support,
        pick (traffic final) = choice ∧
          advance current choice = runKey final.application.config := by
    obtain ⟨seed, member, keyEq, extra, extraMember, picked⟩ := realized
    obtain ⟨final, reached, finalEq⟩ := (PMF.mem_support_map_iff _ _ _).mp extraMember
    subst finalEq
    refine ⟨seed, member, keyEq, final, reached, picked, ?_⟩
    rw [← keyEq, ← picked]
    exact advanceSpec seed member final reached
  have reflects : ∀ left ∈ (prior.map key).support, ∀ right ∈ (prior.map key).support,
      ∀ leftChoice, (∃ seed ∈ prior.support, key seed = left ∧
        ∃ extra ∈ ((run seed).map traffic).support, pick extra = leftChoice) →
      ∀ rightChoice, (∃ seed ∈ prior.support, key seed = right ∧
        ∃ extra ∈ ((run seed).map traffic).support, pick extra = rightChoice) →
      keyView who (advance left leftChoice) = keyView who (advance right rightChoice) →
        view left = view right := by
    intro left _ right _ leftChoice leftRealized rightChoice rightRealized same
    obtain ⟨leftSeed, leftMember, leftKey, leftFinal, leftReached, _, leftAdvance⟩ :=
      realizedFinal left leftChoice leftRealized
    obtain ⟨rightSeed, rightMember, rightKey, rightFinal, rightReached, _, rightAdvance⟩ :=
      realizedFinal right rightChoice rightRealized
    rw [leftAdvance, rightAdvance, keyView_runKey, keyView_runKey] at same
    have ends := Option.some.inj same
    obtain ⟨leftPath, leftSound⟩ := facts leftSeed leftMember leftFinal leftReached
    obtain ⟨rightPath, rightSound⟩ := facts rightSeed rightMember rightFinal rightReached
    obtain ⟨startViews, hiddens⟩ := blockStart_reflect concurrent flat publications
      (begin leftSeed leftMember) (begin rightSeed rightMember) leftPath rightPath leftSound
      rightSound (DefaultOwners.path leftPath (owners leftSeed leftMember))
      (DefaultOwners.path rightPath (owners rightSeed rightMember))
      (completes leftSeed leftMember leftFinal leftReached)
      (completes rightSeed rightMember rightFinal rightReached) ends
    rw [← leftKey, ← rightKey]
    change (keyView who (runKey (execution leftSeed).application.config),
        blockHidden who start finish (runKey (execution leftSeed).application.config)) =
      (keyView who (runKey (execution rightSeed).application.config),
        blockHidden who start finish (runKey (execution rightSeed).application.config))
    rw [keyView_runKey, keyView_runKey, startViews, hiddens]
  have remembered : ∀ left ∈ (prior.map key).support, ∀ right ∈ (prior.map key).support,
      ∀ leftChoice, (∃ seed ∈ prior.support, key seed = left ∧
        ∃ extra ∈ ((run seed).map traffic).support, pick extra = leftChoice) →
      ∀ rightChoice, (∃ seed ∈ prior.support, key seed = right ∧
        ∃ extra ∈ ((run seed).map traffic).support, pick extra = rightChoice) →
      True → keyView who (advance left leftChoice) = keyView who (advance right rightChoice) →
        leftChoice = rightChoice := by
    intro left _ right _ leftChoice leftRealized rightChoice rightRealized _ same
    obtain ⟨_, _, _, leftFinal, _, leftPick, leftAdvance⟩ :=
      realizedFinal left leftChoice leftRealized
    obtain ⟨_, _, _, rightFinal, _, rightPick, rightAdvance⟩ :=
      realizedFinal right rightChoice rightRealized
    rw [leftAdvance, rightAdvance, keyView_runKey, keyView_runKey] at same
    rw [← leftPick, ← rightPick, pickFinal, pickFinal, Option.some.inj same]
  obtain ⟨channel, nextNoise, joint, factored⟩ := exists_owned_phase_joint_of_realized prior key
    (fun seed => traffic (execution seed)) view (fun pair => noise pair.1) factor
    (fun seed => (run seed).map traffic) coupled pick advance (keyView who) (fun _ => True)
    reflects remembered (fun _ _ idle => (idle trivial).elim)
  have keyed : ∀ seed ∈ prior.support,
      (run seed).map (fun final => (runKey final.application.config, traffic final)) =
        ((run seed).map traffic).map (fun extra => (advance (key seed) (pick extra), extra)) := by
    intro seed member
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final reached
    simp only [Function.comp_apply, advanceSpec seed member final reached]
  have keyedEnds : ∀ seed ∈ prior.support,
      (run seed).map (fun final => runKey final.application.config) =
        (run seed).map (fun final => advance (key seed) (pick (traffic final))) := by
    intro seed member
    apply map_congr_on_support _
    intro final reached
    rw [advanceSpec seed member final reached]
  have nextLaw : (prior.bind fun seed => (run seed).map fun final =>
      runKey final.application.config) =
      (prior.map key).bind (fun current => (channel (view current)).map
        fun extra => advance current (pick extra)) := by
    have projected := congrArg (PMF.map Prod.fst) factored
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
      PMF.bind_pure] at projected
    exact (bind_congr_on_support _ keyedEnds).trans projected
  refine ⟨channel, nextNoise, fun current extra => advance current (pick extra), ?_, ?_,
    fun seed member final reached => (advanceSpec seed member final reached).symm⟩
  · refine Eq.trans (bind_congr_on_support _ fun seed _ => ?_) joint
    rw [PMF.map_comp]
    rfl
  · rw [nextLaw]
    exact (bind_congr_on_support _ keyed).trans factored

end Vegas
