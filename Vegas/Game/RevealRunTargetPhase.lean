/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunTarget
import Vegas.Game.RevealBlockPhase
import Vegas.Game.RevealRunCoupling

/-! # A step to the deviator's next reveal as a phase

A step of a run of concurrent reveals runs from a point of the run until the
deviator's earliest pending reveal of the run, `target`, completes. Its points
are the keys of the closure: the honest reveals that do not wait for `target`
are taken as already completed. From a coupled prior whose deviator traffic is
noise read from the deviator's view of the closure, the step's final traffic is
a channel read from that view, and the closure key at the end is the closure
advance by the deviator's observed action at `target`.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The starting conditions of a step to the deviator's next reveal `target`:
earlier events have completed, the configuration lies inside the run, the
deviator's reveals of the run before `target` have completed, `target` is
pending while the deviator is active, and any record of `target` is silent. -/
structure TargetStart (who : Player) (start finish : Nat)
    (target : (serviceGraph setup mode).EventId) (config : (serviceGraph setup mode).Config) :
    Prop where
  earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
    event ∈ config.cut.completed
  inside : ¬ BlockDone finish config → InBlock start finish config
  before : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
    event.val < target.val → (serviceGraph setup mode).actor? event = some who →
      event ∈ config.cut.completed
  pending : who ∉ config.defaulted → target ∉ config.cut.completed
  silent : ∀ record, completionOf config target = some record → record.decision = none

/-- The deviator's action at `target` read from a player's normalized
observation. -/
def targetChoice (who : Player) (target : (serviceGraph setup mode).EventId) :
    (Σ player, (serviceGraph setup mode).PlayerObservation player) →
      Option ((serviceGraph setup mode).Action target)
  | ⟨player, observation⟩ =>
      if same : player = who then observedAction target (same ▸ observation) else none

/-- The deviator's action at `target` read from its own normalized observation. -/
theorem targetChoice_self (who : Player) (target : (serviceGraph setup mode).EventId)
    (observation : (serviceGraph setup mode).PlayerObservation who) :
    targetChoice who target ⟨who, observation⟩ = observedAction target observation := by
  simp [targetChoice]

/-- **The joint law of a step to the deviator's next reveal.** From a coupled
prior of step starts whose deviator traffic is noise read from the deviator's
view of the closure key, the step's final traffic is a channel read from that
view, the closure key at the end is the closure advance by the deviator's
observed action at `target`, and the end key and final traffic again have the
factored form, when honest clients open a reveal exactly when its opening is
accepted. -/
theorem targetStep_joint {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay : (serviceGraph setup mode).EventId → Nat}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (base : (serviceGraph setup mode).BehavioralProfile)
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
        (serviceGraph setup mode).normalizeProfile base owner event actor
          ((serviceGraph setup mode).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (referenceIndependent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (relaxed : RelaxedOrder (serviceGraph setup mode)) {start finish : Nat}
    (run : RevealRun (serviceGraph setup mode) start finish)
    (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (targetLate : target.val < finish)
    {Seed : Type} (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (supported : ∀ seed ∈ prior.support, execution seed ∈
      ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
          turns (firstTurnTiming setup turns mode)
          ((serviceGraph setup mode).normalizeProfile base)) who deviation)
        (execution seed).environmentRecall.length).support)
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (begin : ∀ seed ∈ prior.support,
      TargetStart who start finish target (execution seed).application.config)
    (submissions : ∀ seed ∈ prior.support, HonestBlockSubmissions who start finish (execution seed))
    (noise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _)
    (factor : prior.map (fun seed => (runKey (closure ((serviceGraph setup mode).normalizeProfile
        base) who (execution seed).application.config),
        (serviceRuntime setup mode deadline).bindingTraffic leaks who (execution seed))) =
      (prior.map fun seed => runKey (closure ((serviceGraph setup mode).normalizeProfile base)
        who (execution seed).application.config)).bind fun current =>
        (noise (keyView who current)).map fun extra => (current, extra)) :
    ∃ (channel : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _)
      (nextNoise : Option ((serviceGraph setup mode).PlayerObservation who) → PMF _),
      (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
            who deviation)
          (fun current => target ∈ current.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
              (execution seed).application.config),
            (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
        (prior.map fun seed => runKey (closure ((serviceGraph setup mode).normalizeProfile base)
          who (execution seed).application.config)).bind
          (fun current => (channel (keyView who current)).map fun extra => (current, extra)) ∧
      (prior.bind fun seed =>
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
            who deviation)
          (fun current => target ∈ current.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
              final.application.config),
            (serviceRuntime setup mode deadline).bindingTraffic leaks who final)) =
        (prior.bind fun seed =>
          ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
            (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
              (firstTurnTiming setup turns mode)
              ((serviceGraph setup mode).normalizeProfile base)) who deviation)
            (fun current => target ∈ current.application.config.cut.completed) horizon
            (execution seed)).map fun final => runKey (closure
              ((serviceGraph setup mode).normalizeProfile base) who final.application.config)).bind
          (fun current => (nextNoise (keyView who current)).map fun extra => (current, extra)) ∧
      ∀ seed ∈ prior.support, ∀ final ∈
        ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
          (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
            (firstTurnTiming setup turns mode) ((serviceGraph setup mode).normalizeProfile base))
            who deviation)
          (fun current => target ∈ current.application.config.cut.completed) horizon
          (execution seed)).support,
        runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
            final.application.config) =
          closureAdvance ((serviceGraph setup mode).normalizeProfile base) who target targetOwned
            (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
              (execution seed).application.config))
            (targetChoice who target
              ⟨((serviceRuntime setup mode deadline).bindingTraffic leaks who final).2.2.2.2.1.who,
                (serviceGraph setup mode).normalizeObservation _
                  ((serviceRuntime setup mode deadline).bindingTraffic leaks who
                    final).2.2.2.2.1.observation⟩) := by
  classical
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  let app := serviceApplication setup mode deadline leaks
  let runtime := serviceRuntime setup mode deadline
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) R) who deviation
  let stop : G.order.Cut → Prop := fun cut => target ∈ cut.completed
  have stopDone : ∀ cut : G.order.Cut, (∀ event : G.EventId, event.val < finish →
      event ∈ cut.completed) → stop cut := fun cut done => done target targetLate
  let stepRun := fun seed => app.runUntilHorizon scheduler players
    (fun current => stop current.application.config.cut) horizon (execution seed)
  let traffic := runtime.bindingTraffic leaks who
  let point := fun current : app.Execution => runKey (closure R who current.application.config)
  let key := fun seed => point (execution seed)
  let Traffic := MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView G × PublicView G
  let pick := fun extra : Traffic => targetChoice who target
    ⟨extra.2.2.2.2.1.who, G.normalizeObservation extra.2.2.2.2.1.who extra.2.2.2.2.1.observation⟩
  have pickFinal (final : app.Execution) : pick (traffic final) =
      observedAction target (G.normalizeObservation who (G.playerObserve who
        final.application.config)) :=
    targetChoice_self who target _
  let advance := closureAdvance R who target targetOwned
  have readyAllowed (seed : Seed) (member : seed ∈ prior.support) :
      ∀ config : G.Config, Relation.ReflTransGen Config.Step
        (execution seed).application.config config → ¬ stop config.cut →
        ∀ event, config.cut.Ready event → G.actor? event = some who → event = target :=
    fun config path running event ready owned => ready_owned_eq_target who relaxed run
      (begin seed member).earlier target targetOwned targetLate (begin seed member).before path
      running ready owned
  have facts (seed : Seed) (member : seed ∈ prior.support) (final : app.Execution)
      (reached : final ∈ (stepRun seed).support) :=
    runStep_facts bound turns contract timely R decides who deviation start finish
      (run.shaped relaxed) run.publications stop stopDone (execution seed) (· = target)
      (readyAllowed seed member) (supported seed member) (bounded seed member)
      (begin seed member).inside (submissions seed member) final reached
  have doneOf (seed : Seed) (member : seed ∈ prior.support) (final : app.Execution)
      (reached : final ∈ (stepRun seed).support) :
      target ∈ final.application.config.cut.completed :=
    runUntilHorizon_stop contract players (fun current => stop current.application.config.cut)
      (fun current terminal => by
        change target ∈ current.application.config.cut.completed
        rw [terminal]
        exact Finset.mem_univ _)
      (execution seed) (supported seed member) (bounded seed member) final reached
  have endsOf (seed : Seed) (member : seed ∈ prior.support) (final : app.Execution)
      (reached : final ∈ (stepRun seed).support) :
      point final = advance (key seed) (pick (traffic final)) := by
    obtain ⟨path, sound, decided, _, _⟩ := facts seed member final reached
    rw [pickFinal]
    exact targetStep_end base decides referenceIndependent who run path sound target targetOwned
      decided (begin seed member).earlier targetLate (begin seed member).before
      (begin seed member).pending (doneOf seed member final reached)
  let good := fun (seed : Seed) => RunStepHolds scheduler bound turns R who deviation horizon
    start finish (· = target) (execution seed).application.config
  have goodRound (seed : Seed) (member : seed ∈ prior.support) :
      ∀ n current, good seed (n + 1) current → ¬ stop current.application.config.cut →
        ∀ next ∈ (app.round scheduler players current).support, good seed n next :=
    runStep_round bound turns contract timely R decides who deviation start finish
      (run.shaped relaxed) run.publications stop stopDone (execution seed).application.config
      (· = target) (readyAllowed seed member)
  have goodStart (seed : Seed) (member : seed ∈ prior.support) :
      good seed (horizon - (execution seed).environmentRecall.length) (execution seed) :=
    ⟨supported seed member, by have := bounded seed member; omega, (begin seed member).inside,
      submissions seed member, .refl, fun event fresh done => (fresh done).elim,
      fun event _ fresh _ record found => (fresh ((completionOf_isSome_iff _ event).mp
        (by rw [found]; rfl))).elim⟩
  have coupled : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      keyView who (key left) = keyView who (key right) →
      traffic (execution left) = traffic (execution right) →
      (stepRun left).map traffic = (stepRun right).map traffic := by
    intro left leftMember right rightMember views same
    have lengths : (execution left).environmentRecall.length =
        (execution right).environmentRecall.length :=
      congrArg (fun value => value.2.2.1.length) same
    obtain ⟨leftTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon
      scheduler players _ (bounded left leftMember) _ (supported left leftMember)
    obtain ⟨rightTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon
      scheduler players _ (bounded right rightMember) _ (supported right rightMember)
    have agreeAt : ∀ (n : Nat) (currentRun otherRun : app.Execution),
        good left (n + 1) currentRun → good right (n + 1) otherRun →
        currentRun.application.config.cut = otherRun.application.config.cut →
        ¬ stop currentRun.application.config.cut →
        ∀ (event : G.EventId) (owner : Player) (payload : L.Ty)
          (binding : FieldRef G.layout (.binding owner payload))
          (checks : List (GuardCheck G.layout payload))
          (outputEq : G.outputLayout event = .publication payload)
          (codeEq : cast (congrArg (EventCode G.layout) outputEq) (G.nodes event) =
            .resolve owner payload binding checks),
          nodeView G event = .resolve owner payload binding checks outputEq codeEq →
          currentRun.application.config.cut.Ready event →
          owner ∉ currentRun.application.config.defaulted →
          owner ∉ otherRun.application.config.defaulted →
          (owner ≠ who → openingAccepted event currentRun.application.config.store =
            openingAccepted event otherRun.application.config.store) ∧
          (openingAccepted event currentRun.application.config.store = true ∨ owner = who →
            binding.get? currentRun.application.config.store =
              binding.get? otherRun.application.config.store) := by
      intro n currentRun otherRun currentGood otherGood cuts running
      obtain ⟨_, _, _, _, currentPath, currentSound, currentDecided⟩ := currentGood
      obtain ⟨_, _, _, _, otherPath, otherSound, otherDecided⟩ := otherGood
      have otherRunning : ¬ stop otherRun.application.config.cut := by
        change target ∉ _
        rw [← cuts]
        exact running
      have quietOf {origin config : G.Config} (decided : DecidesOnly who origin (· = target) config)
          (pending : target ∉ config.cut.completed) :
          ∀ event : G.EventId, event ∉ origin.cut.completed → G.actor? event = some who →
            ∀ record, completionOf config event = some record → record.decision = none := by
        intro event fresh mine record found
        by_cases same : event = target
        · subst same
          exact (pending ((completionOf_isSome_iff config event).mp (by rw [found]; rfl))).elim
        · exact decided event same fresh mine record found
      exact run_agree_of_closure base decides referenceIndependent who views currentPath
        otherPath currentSound otherSound (quietOf currentDecided running)
        (quietOf otherDecided otherRunning) cuts
    have coupledRun := run_stopped_traffic_congr scheduler bound turns R decides who deviation
      start finish (run.shaped relaxed) run.publications stop stopDone (good left) (good right)
      (goodRound left leftMember) (goodRound right rightMember)
      (horizon - (execution left).environmentRecall.length) 0 0 (execution left)
      (execution right) (by simpa only [Nat.zero_add] using leftTrace)
      (by rw [lengths]; simpa only [Nat.zero_add] using rightTrace)
      (begin left leftMember).inside (begin right rightMember).inside
      (submissions left leftMember) (submissions right rightMember)
      (runTurnFacts_roundsFrom scheduler bound turns R who deviation _ _
        (supported left leftMember))
      (runTurnFacts_roundsFrom scheduler bound turns R who deviation _ _
        (supported right rightMember))
      (goodStart left leftMember) (by rw [lengths]; exact goodStart right rightMember) agreeAt
      same
    change (app.runUntil scheduler players (fun current => stop current.application.config.cut)
        (horizon - (execution left).environmentRecall.length) (execution left)).map traffic =
      (app.runUntil scheduler players (fun current => stop current.application.config.cut)
        (horizon - (execution right).environmentRecall.length) (execution right)).map traffic
    rw [← lengths]
    exact coupledRun
  have realizedFinal (current : RunKey G) (choice : Option (G.Action target))
      (realized : ∃ seed ∈ prior.support, key seed = current ∧
        ∃ extra ∈ ((stepRun seed).map traffic).support, pick extra = choice) :
      ∃ seed ∈ prior.support, key seed = current ∧ ∃ final ∈ (stepRun seed).support,
        pick (traffic final) = choice ∧ advance current choice = point final := by
    obtain ⟨seed, member, keyEq, extra, extraMember, picked⟩ := realized
    obtain ⟨final, reached, finalEq⟩ := (PMF.mem_support_map_iff _ _ _).mp extraMember
    subst finalEq
    refine ⟨seed, member, keyEq, final, reached, picked, ?_⟩
    rw [← keyEq, ← picked]
    exact (endsOf seed member final reached).symm
  have choiceOfView (seed : Seed) (member : seed ∈ prior.support) (final : app.Execution)
      (reached : final ∈ (stepRun seed).support) :
      pick (traffic final) = observedAction target (G.normalizeObservation who
        (G.playerObserve who (closure R who final.application.config))) := by
    rw [pickFinal, observedAction_closure R who (doneOf seed member final reached)]
  have reflects : ∀ left ∈ (prior.map key).support, ∀ right ∈ (prior.map key).support,
      ∀ leftChoice, (∃ seed ∈ prior.support, key seed = left ∧
        ∃ extra ∈ ((stepRun seed).map traffic).support, pick extra = leftChoice) →
      ∀ rightChoice, (∃ seed ∈ prior.support, key seed = right ∧
        ∃ extra ∈ ((stepRun seed).map traffic).support, pick extra = rightChoice) →
      keyView who (advance left leftChoice) = keyView who (advance right rightChoice) →
        keyView who left = keyView who right := by
    intro left _ right _ leftChoice leftRealized rightChoice rightRealized same
    obtain ⟨leftSeed, leftMember, leftKey, leftFinal, leftReached, _, leftAdvance⟩ :=
      realizedFinal left leftChoice leftRealized
    obtain ⟨rightSeed, rightMember, rightKey, rightFinal, rightReached, _, rightAdvance⟩ :=
      realizedFinal right rightChoice rightRealized
    rw [leftAdvance, rightAdvance] at same
    obtain ⟨leftPath, leftSound, leftDecided, _, _⟩ := facts leftSeed leftMember leftFinal
      leftReached
    obtain ⟨rightPath, rightSound, rightDecided, _, _⟩ := facts rightSeed rightMember rightFinal
      rightReached
    rw [← leftKey, ← rightKey]
    exact targetStep_reflect base decides referenceIndependent who relaxed run target targetOwned
      targetLate leftPath rightPath leftSound rightSound leftDecided rightDecided
      (begin leftSeed leftMember).earlier (begin rightSeed rightMember).earlier
      (begin leftSeed leftMember).before (begin rightSeed rightMember).before
      (begin leftSeed leftMember).pending (begin rightSeed rightMember).pending
      (begin leftSeed leftMember).silent (begin rightSeed rightMember).silent
      (doneOf leftSeed leftMember leftFinal leftReached)
      (doneOf rightSeed rightMember rightFinal rightReached) same
  have remembered : ∀ left ∈ (prior.map key).support, ∀ right ∈ (prior.map key).support,
      ∀ leftChoice, (∃ seed ∈ prior.support, key seed = left ∧
        ∃ extra ∈ ((stepRun seed).map traffic).support, pick extra = leftChoice) →
      ∀ rightChoice, (∃ seed ∈ prior.support, key seed = right ∧
        ∃ extra ∈ ((stepRun seed).map traffic).support, pick extra = rightChoice) →
      True → keyView who (advance left leftChoice) = keyView who (advance right rightChoice) →
        leftChoice = rightChoice := by
    intro left _ right _ leftChoice leftRealized rightChoice rightRealized _ same
    obtain ⟨leftSeed, leftMember, _, leftFinal, leftReached, leftPick, leftAdvance⟩ :=
      realizedFinal left leftChoice leftRealized
    obtain ⟨rightSeed, rightMember, _, rightFinal, rightReached, rightPick, rightAdvance⟩ :=
      realizedFinal right rightChoice rightRealized
    rw [leftAdvance, rightAdvance] at same
    rw [← leftPick, ← rightPick, choiceOfView leftSeed leftMember leftFinal leftReached,
      choiceOfView rightSeed rightMember rightFinal rightReached]
    exact observedAction_of_keyView who same target
  obtain ⟨channel, nextNoise, joint, factored⟩ := exists_owned_phase_joint_of_realized prior key
    (fun seed => traffic (execution seed)) (keyView who) noise factor
    (fun seed => (stepRun seed).map traffic) coupled pick advance (keyView who) (fun _ => True)
    reflects remembered (fun _ _ idle => (idle trivial).elim)
  have keyed : ∀ seed ∈ prior.support,
      (stepRun seed).map (fun final => (point final, traffic final)) =
        ((stepRun seed).map traffic).map
          (fun extra => (advance (key seed) (pick extra), extra)) := by
    intro seed member
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final reached
    simp only [Function.comp_apply, endsOf seed member final reached]
  have keyedEnds : ∀ seed ∈ prior.support,
      (stepRun seed).map point =
        (stepRun seed).map (fun final => advance (key seed) (pick (traffic final))) := by
    intro seed member
    apply map_congr_on_support _
    intro final reached
    rw [endsOf seed member final reached]
  have nextLaw : (prior.bind fun seed => (stepRun seed).map point) =
      (prior.map key).bind (fun current => (channel (keyView who current)).map
        fun extra => advance current (pick extra)) := by
    have projected := congrArg (PMF.map Prod.fst) factored
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
      PMF.bind_pure] at projected
    exact (bind_congr_on_support _ keyedEnds).trans projected
  refine ⟨channel, nextNoise, ?_, ?_, fun seed member final reached =>
    endsOf seed member final reached⟩
  · refine Eq.trans (bind_congr_on_support _ fun seed _ => ?_) joint
    rw [PMF.map_comp]
    rfl
  · change (prior.bind fun seed => (stepRun seed).map fun final => (point final, traffic final)) =
      (prior.bind fun seed => (stepRun seed).map point).bind _
    rw [nextLaw]
    exact (bind_congr_on_support _ keyed).trans factored

end Vegas
