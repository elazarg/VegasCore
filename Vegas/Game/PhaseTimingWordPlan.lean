/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPoolPlan
import Vegas.Game.PhaseCommitTimingWordPolicy

/-! # Original owner words under actual finite timing plans -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound


open Classical in
/-- The NON-RAW finite component keeps free choices unchanged and replaces
only one owner's addressed source draws by one immutable original word.
Prescribed and keyed parts retain their respective physical dispatchers. -/
def phaseTimingWordComponent {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (word : DecisionView who Δ) (agent : Agent) :
    Parts (pool agent) → PMF ((N).Choice agent.1 agent.2.1) :=
  freeKeyedComponent
    (fun _ choice => PMF.pure choice)
    (fun agent => if same : agent.1 = who then
      (menu).restrictPolicy initial horizon scheduler agent.1
        (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation
          slotWeight slotNonnegative slotBounded agent.1
          (cast (congrArg (fun owner => DecisionView owner Δ) same.symm) word)) agent.2.1
      else phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed source 0 le_rfl (by norm_num) slotWeight slotNonnegative slotBounded
        agent.1 agent.2.1)
    (fun agent option => if same : agent.1 = who then
      phaseCommitTimingWordStrategy setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded initial horizon scheduler option agent.1
        (cast (congrArg (fun owner => DecisionView owner Δ) same.symm) word) agent.2.1
      else phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        wellFormed source 0 le_rfl (by norm_num) slotWeight slotNonnegative slotBounded
        agent.1 agent.2.1 option)
    agent

open Classical in
/-- The same actual played-pool assignment selects every callback component.
Its selected option may vary with the complete operational key, while the
owner's single original source word remains unchanged across callbacks. -/
def phaseTimingWordPlanPolicy {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player) (word : DecisionView who Δ) : (app).Policy :=
  (menu).decodeProfile initial horizon scheduler
    ((N).agentBehavior (N).playedInformation fallback
      (fun agent => phaseTimingWordComponent setup mode runtime leaks bounds initial horizon
        scheduler bound wellFormed source block low generation slotWeight slotNonnegative
          slotBounded who word agent (plan (pool agent)))) who

open Classical in
/-- At a nonfree keyed played agent, the original and word-valued components
read the SAME structural option from its actual finite pool part. -/
theorem phaseTimingWordComponent_of_ownedKeyed
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (info : (N).InfoState who) (played : info ∈ (N).playedInformation who)
    (word : DecisionView who Δ)
    (owned : ownedKeyed isFree isKeyed (⟨who, ⟨info, played⟩⟩ : Agent))
    (part : Parts (pool (⟨who, ⟨info, played⟩⟩ : Agent))) :
    phaseTimingWordComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed source block low generation slotWeight slotNonnegative slotBounded who word
          ⟨who, ⟨info, played⟩⟩ part =
      phaseCommitTimingWordStrategy setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded initial horizon scheduler
        (ownedKeyedIdentify (key := poolKey) owned part) who word info := by
  rw [phaseTimingWordComponent, freeKeyedComponent_of_ownedKeyed _ _ _ owned]
  simp only [dite_true, cast_eq]

open Classical in
/-- At each played owner input, the total NON-RAW word component is either
independent of the word, the canonical word member, or the timing member of
one actual original pool option. The option does not depend on the word. -/
theorem phaseTimingWordComponent_cases {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (info : (N).InfoState who) (played : info ∈ (N).playedInformation who)
    (part : Parts (pool (⟨who, ⟨info, played⟩⟩ : Agent))) :
    (∃ law, ∀ word, phaseTimingWordComponent setup mode runtime leaks bounds initial horizon
      scheduler
      bound wellFormed source block low generation slotWeight slotNonnegative slotBounded who word
        ⟨who, ⟨info, played⟩⟩ part = law) ∨
    (∀ word, phaseTimingWordComponent setup mode runtime leaks bounds initial horizon scheduler
      bound
      wellFormed source block low generation slotWeight slotNonnegative slotBounded who word
        ⟨who, ⟨info, played⟩⟩ part =
      (menu).restrictPolicy initial horizon scheduler who
        (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low
          generation
          slotWeight slotNonnegative slotBounded who word) info) ∨
    ∃ option, ∀ word, phaseTimingWordComponent setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed source block low generation slotWeight slotNonnegative slotBounded
        who word ⟨who, ⟨info, played⟩⟩ part =
      phaseCommitTimingWordStrategy setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded initial horizon scheduler option who word
          info := by
  let current : Agent := ⟨who, ⟨info, played⟩⟩
  by_cases excluded : isFree current
  · refine Or.inl ⟨PMF.pure (freeIdentify (key := poolKey) excluded part), ?_⟩
    intro word
    rw [phaseTimingWordComponent, freeKeyedComponent_of_free _ _ _ excluded]
  · by_cases keyed : isKeyed current
    · refine Or.inr (Or.inr ⟨ownedKeyedIdentify (key := poolKey) ⟨keyed, excluded⟩ part, ?_⟩)
      intro word
      exact phaseTimingWordComponent_of_ownedKeyed setup mode runtime leaks bounds initial horizon
        scheduler bound wellFormed source block low generation slotWeight slotNonnegative
          slotBounded
          who info played word ⟨keyed, excluded⟩ part
    · refine Or.inr (Or.inl ?_)
      intro word
      unfold phaseTimingWordComponent
      obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free (free := isFree)
        (keyed := isKeyed) (key := poolKey) _ _ _ (agent := current) excluded
      rw [same part, keyedComponent_of_not_keyed _ _ (fun owned => keyed owned.1)]
      simp only [current, dite_true, cast_eq]

open Classical in
/-- Decode the actual finite played-pool member at its complete physical input,
retaining the original dependent plan coordinate and fallback branch. -/
theorem word_member_apply {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player) (word : DecisionView who Δ)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded plan
          who word past view =
      (if present : some (past, view) ∈ (N).playedInformation who then
        phaseTimingWordComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed source block low generation slotWeight slotNonnegative slotBounded who word
            ⟨who, ⟨some (past, view), present⟩⟩
            (plan (pool ⟨who, ⟨some (past, view), present⟩⟩))
      else PMF.pure (fallback who (some (past, view)))).map
        (fun choice => choice.1.getD ⟨none⟩) := by
  simp only [phaseTimingWordPlanPolicy, ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    PMF.map_comp, Function.comp_def, InformationModel.agentBehavior]
  by_cases present : some (past, view) ∈ (N).playedInformation who
  · simp only [dite_eq_left present]
    rfl
  · simp only [dite_eq_right present]
    rfl

omit [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
  scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
    scheduler).InfoState who)] in
private theorem restrict_readout (who : Player) (policy : (app).Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (((menu).restrictPolicy initial horizon scheduler who policy) (some (past, view))).map
        (fun choice => choice.1.getD ⟨none⟩) = policy past view := by
  have mapped := congrArg (PMF.map (fun response : Option (app).Action => response.getD ⟨none⟩))
    ((menu).restrictPolicy_map_val initial horizon scheduler who policy past view
      (covered past view))
  simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at mapped
  change _ = (policy past view).map id at mapped
  rw [PMF.map_id] at mapped
  exact mapped

open Classical in
/-- The actual private-plan member at any complete physical input is either
word-independent, the canonical member, or the timing member of the part
chosen at THIS input's actual played pool. That option is fixed independently
of the hidden word, and may differ at subsequent operational keys. -/
theorem phaseTimingWordPlanPolicy_cases {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (∃ law, ∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
        slotBounded plan who word past view = law) ∨
    (∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded
        plan who word past view =
      phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low generation
        slotWeight slotNonnegative slotBounded who word past view) ∨
    ∃ option, ∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
        slotBounded plan who word past view =
      phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded option who word past view := by
  by_cases present : some (past, view) ∈ (N).playedInformation who
  · let current : Agent := ⟨who, ⟨some (past, view), present⟩⟩
    obtain ⟨law, constant⟩ | prescribed | ⟨option, timed⟩ := phaseTimingWordComponent_cases setup
      mode
      runtime leaks bounds initial horizon scheduler bound wellFormed source block low generation
      slotWeight slotNonnegative slotBounded who (some (past, view)) present (plan (pool current))
    · refine Or.inl ⟨law.map (fun choice => choice.1.getD ⟨none⟩), ?_⟩
      intro word
      rw [word_member_apply, dite_eq_left present, constant word]
    · refine Or.inr (Or.inl ?_)
      intro word
      rw [word_member_apply, dite_eq_left present, prescribed word]
      exact restrict_readout setup mode runtime leaks bounds initial horizon scheduler who _
        (phaseCommitWordPolicy_covered setup mode runtime leaks bounds wellFormed source block low
          generation slotWeight slotNonnegative slotBounded who word) past view
    · refine Or.inr (Or.inr ⟨option, ?_⟩)
      intro word
      rw [word_member_apply, dite_eq_left present, timed word]
      exact restrict_readout setup mode runtime leaks bounds initial horizon scheduler who _
        (phaseCommitTimingWordPolicy_covered setup mode runtime leaks bounds wellFormed source block
          low generation slotWeight slotNonnegative slotBounded option who word) past view
  · refine Or.inl ⟨(PMF.pure (fallback who (some (past, view)))).map
        (fun choice => choice.1.getD ⟨none⟩), ?_⟩
    intro word
    rw [word_member_apply, dite_eq_right present]

/-- The complete varying-plan family has identical response masses on common
word support. RAW perturbations are retained outside this exact member law. -/
theorem phaseTimingWordPlanPolicy_apply_eq_of_support
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player) (first second : DecisionView who Δ)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (left : response ∈ (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
        slotBounded plan who first past view).support)
    (right : response ∈ (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
        slotBounded plan who second past view).support) :
    phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded plan
          who first past view response =
      phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded plan
          who second past view response := by
  obtain ⟨law, constant⟩ | canonical | ⟨option, timed⟩ := phaseTimingWordPlanPolicy_cases setup mode
    runtime leaks bounds initial horizon scheduler bound fallback wellFormed source block low
      generation slotWeight slotNonnegative slotBounded plan who past view
  · rw [constant first, constant second]
  · rw [canonical first] at left ⊢
    rw [canonical second] at right ⊢
    exact phaseCommitWordPolicy_apply_eq_of_support setup mode runtime leaks bounds wellFormed
      source block low generation slotWeight slotNonnegative slotBounded who first second past view
        response left right
  · rw [timed first] at left ⊢
    rw [timed second] at right ⊢
    exact phaseCommitTimingWordPolicy_apply_eq_of_support setup mode runtime leaks bounds wellFormed
      source block low generation slotWeight slotNonnegative slotBounded option who first second
        past
        view response left right

open Classical in
/-- Under a fixed original timing plan, full actual recall filters the ONE
original owner-word prior by the member-consistency fiber. Earlier WAITs are
retained and do not silently select a source omission or a current result. -/
theorem phaseTimingWordPlanPolicy_posterior_consistency_fiber
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player) (prior : PMF (DecisionView who Δ))
    (past : List (app).PlayerEntry)
    (consistent : ((app).policyMixture prior
      (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded plan
          who)).policy.Consistent past) :
    ((app).policyMixture prior
      (phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded plan
          who)).posterior past =
      fiberPosterior prior (fun word => decide ((phaseTimingWordPlanPolicy setup mode runtime leaks
        bounds initial horizon scheduler bound fallback wellFormed source block low generation
          slotWeight slotNonnegative slotBounded plan who word).Consistent past)) true := by
  apply (app).policyMixture_posterior_consistency_fiber prior _ ?_ past consistent
  intro earlier view response first second left right
  exact phaseTimingWordPlanPolicy_apply_eq_of_support setup mode runtime leaks bounds initial
    horizon
    scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
      slotBounded plan who first second earlier view response left right

open Classical in
/-- A genuinely played nonexcluded input cannot select a free arbitrary
choice or the dormant fallback. Its complete word law is the canonical
member or the SAME selected operational option of the actual finite plan. -/
theorem phaseTimingWordPlanPolicy_of_not_free
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (present : some (past, view) ∈ (N).playedInformation who)
    (unflagged : ¬ PhasePublicExclusion setup mode runtime leaks (some (past, view))) :
    (∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded
        plan who word past view =
      phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low generation
        slotWeight slotNonnegative slotBounded who word past view) ∨
    ∃ option, ∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
        slotBounded plan who word past view =
      phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded option who word past view := by
  let current : Agent := ⟨who, ⟨some (past, view), present⟩⟩
  have excluded : ¬ isFree current := unflagged
  by_cases keyed : isKeyed current
  · refine Or.inr ⟨ownedKeyedIdentify (key := poolKey) ⟨keyed, excluded⟩ (plan (pool current)), ?_⟩
    intro word
    rw [word_member_apply, dite_eq_left present,
      phaseTimingWordComponent_of_ownedKeyed setup mode runtime leaks bounds initial horizon
        scheduler bound wellFormed source block low generation slotWeight slotNonnegative
          slotBounded
          who (some (past, view)) present word ⟨keyed, excluded⟩]
    exact restrict_readout setup mode runtime leaks bounds initial horizon scheduler who _
      (phaseCommitTimingWordPolicy_covered setup mode runtime leaks bounds wellFormed source block
        low
        generation slotWeight slotNonnegative slotBounded _ who word) past view
  · refine Or.inl ?_
    intro word
    rw [word_member_apply, dite_eq_left present]
    have atCurrent : phaseTimingWordComponent setup mode runtime leaks bounds initial horizon
        scheduler bound wellFormed source block low generation slotWeight slotNonnegative
          slotBounded
          who word current (plan (pool current)) =
        (menu).restrictPolicy initial horizon scheduler who
          (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low
            generation
            slotWeight slotNonnegative slotBounded who word) (some (past, view)) := by
      unfold phaseTimingWordComponent
      obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free (free := isFree)
        (keyed := isKeyed) (key := poolKey) _ _ _ (agent := current) excluded
      rw [same, keyedComponent_of_not_keyed _ _ (fun owned => keyed owned.1)]
      simp only [current, dite_true, cast_eq]
    rw [atCurrent]
    exact restrict_readout setup mode runtime leaks bounds initial horizon scheduler who _
      (phaseCommitWordPolicy_covered setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded who word) past view

/-- At an authentic clear active callback the actual plan chooses only its
prescribed or keyed source-word channel. Playedness and nonexclusion are
derived from the actual trace and full physical input, not supplied as
counterpart or menu assumptions. -/
theorem phaseTimingWordPlanPolicy_of_clear_actor
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (fallback : (who : Player) → (N).Policy who)
    (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (acting : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅) :
    (∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded
        plan who word (control.execution.recall who) (control.execution.observe (app) who) =
      phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed source block low generation
        slotWeight slotNonnegative slotBounded who word (control.execution.recall who)
          (control.execution.observe (app) who)) ∨
    ∃ option, ∀ word, phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
        slotBounded plan who word (control.execution.recall who) (control.execution.observe (app)
          who) =
      phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed source block low
        generation slotWeight slotNonnegative slotBounded option who word
        (control.execution.recall who) (control.execution.observe (app) who) := by
  have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some control) := by
    change ¬ (control.remaining = 0 ∧ control.actor = none)
    rintro ⟨_, actorNone⟩
    rw [acting] at actorNone
    cases actorNone
  have observed : (N).infoOf who trace =
      some (control.execution.recall who, control.execution.observe (app) who) :=
    ((menu).info initial horizon scheduler who trace).trans (by
      simp only [ReactiveApplication.observe, acting, ite_true])
  have played := (N).mem_playedInformation (who := who)
    (history := ⟨some control, trace⟩) running
  rw [observed] at played
  have unflagged : ¬ PhasePublicExclusion setup mode runtime leaks
      (some (control.execution.recall who, control.execution.observe (app) who)) := by
    rintro ⟨before, view, same, excluded⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
    change control.execution.application.current.excluded ≠ ∅ at excluded
    exact excluded clear
  exact phaseTimingWordPlanPolicy_of_not_free setup mode runtime leaks bounds initial horizon
    scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
      slotBounded plan who (control.execution.recall who) (control.execution.observe (app) who)
      played unflagged

end Vegas
