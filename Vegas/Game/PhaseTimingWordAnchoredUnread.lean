/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordUnread
import Vegas.Pending.PhaseAnchoredRecall

/-! # Unread timing-pool parts after authentic-entry raw replay

The original entry and full timing plans remain tagged through the existing
physical runner. Owned word kernels use only owned entry views; entry mixing
is retained rather than replaced by independence across hidden entries.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information initial
    horizon scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
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
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
  (fallback : (who : Player) →
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).Policy
      who)
  (wellFormed : setup.WellFormed) (source : setup.commitRecoveryModel.BehavioralAssessment)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)

local notation "baseFamily" => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
  horizon scheduler bound fallback wellFormed source block low generation slotWeight
    slotNonnegative slotBounded

variable (anchor : (phaseApplication runtime leaks).Execution)

local notation "family" => fun plan who word =>
  ReactiveApplication.anchoredPolicy anchor (fun _ => baseFamily plan who word) who

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

local instance timingWordAnchoredUnreadPoolFintype :
    Fintype (FreeKeyedPool isFree isKeyed poolKey) := Fintype.ofFinite _

open Classical in
/-- The actual current pool coordinate has not been used in any earlier
recalled response, even though those responses may read the original word. -/
theorem phaseTimingWordAnchoredPolicy_unread
    (who : Player) (word : DecisionView who Δ)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (present : some (past, view) ∈ (N).playedInformation who) :
    let current : Agent := ⟨who, ⟨some (past, view), present⟩⟩
    ∀ (before : List (app).PlayerEntry) (entry : (app).PlayerEntry),
      before ++ [entry] <+: past → ∀ (plan : (p : Pool) → Parts p)
      (part : Parts (pool current)),
        family (Function.update plan (pool current) part) who word before entry.beforeView =
          family plan who word before entry.beforeView := by
  intro current before entry recorded plan part
  have original := phaseTimingWordPlanPolicy_unread setup mode runtime leaks bounds initial
    horizon scheduler bound fallback wellFormed source block low generation slotWeight
      slotNonnegative slotBounded who word past view present before entry recorded plan part
  change ReactiveApplication.anchoredPolicy anchor
    (fun _ => baseFamily (Function.update plan (pool current) part) who word) who before
      entry.beforeView =
    ReactiveApplication.anchoredPolicy anchor (fun _ => baseFamily plan who word) who before
      entry.beforeView
  unfold ReactiveApplication.anchoredPolicy
  cases found : (anchor.recall who)[before.length]? with
  | none => simpa only [found] using original
  | some saved =>
    by_cases replayed : before ++ [saved] <+: anchor.recall who ∧
      saved.beforeView = entry.beforeView
    · simp only [replayed, and_self, ite_true]
    · simpa only [found, replayed, ite_false] using original

open Classical in
/-- In the actual ORIGINAL plan-weight product times the original word prior,
the current unread part keeps its original weights independently of all other
parts AND the complete updated word. No source-word posterior is assumed. -/
theorem phaseTimingWordAnchoredPolicy_posterior_current_part
    (weights : (p : Pool) → PMF (Parts p)) (who : Player)
    (prior : PMF (DecisionView who Δ)) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (present : some (past, view) ∈ (N).playedInformation who) :
    let current : Agent := ⟨who, ⟨some (past, view), present⟩⟩
    let original := (independentProduct weights).bind fun plan => prior.map (Prod.mk plan)
    let members := fun memory : ((p : Pool) → Parts p) × DecisionView who Δ =>
      family memory.1 who memory.2
    ∃ remainder : PMF (((p : {p // p ≠ pool current}) → Parts p.val) × DecisionView who Δ),
      (((app).policyMixture original members).posterior past).map
          (fun memory => (memory.1 (pool current),
            ((fun p : {p // p ≠ pool current} => memory.1 p.val), memory.2))) =
        (weights (pool current)).bind (fun part => remainder.map (Prod.mk part)) := by
  intro current original members
  let selected := pool current
  let split := (Equiv.prodCongr (Equiv.piSplitAt selected Parts)
    (Equiv.refl (DecisionView who Δ))).trans (Equiv.prodAssoc (Parts selected)
      ((p : {p // p ≠ selected}) → Parts p.val) (DecisionView who Δ))
  let restLaw := (independentProduct (fun p : {p // p ≠ selected} => weights p.val)).bind
    fun rest => prior.map (Prod.mk rest)
  let pairMembers := fun pair => members (split.symm pair)
  let reference := (weights selected).support_nonempty.choose
  let restMembers := fun rest => pairMembers (reference, rest)
  have splitLaw : original.map split =
      (weights selected).bind (fun part => restLaw.map (Prod.mk part)) := by
    dsimp only [original]
    rw [independentProduct_splitAt weights selected]
    simp only [restLaw, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def]
    apply bind_congr_on_support _
    intro part _
    apply bind_congr_on_support _
    intro rest _
    apply congrArg (PMF.map · prior)
    funext word
    simp [split]
  have transported := (app).policyMixture_posterior_map original split pairMembers past
  have same : (fun memory => pairMembers (split memory)) = members := by
    funext memory
    simp only [pairMembers, Equiv.symm_apply_apply]
  rw [same, splitLaw] at transported
  have product := (app).policyMixture_posterior_independent_left (weights selected) restLaw
    pairMembers restMembers past (fun before entry recorded part rest => by
      have updated : (Equiv.piSplitAt selected Parts).symm (part, rest.1) =
          Function.update ((Equiv.piSplitAt selected Parts).symm (reference, rest.1))
            selected part := by
        funext p
        by_cases equal : p = selected
        · subst p
          simp [Equiv.piSplitAt]
        · simp [Equiv.piSplitAt, equal]
      change family ((Equiv.piSplitAt selected Parts).symm (part, rest.1)) who rest.2 before
          entry.beforeView =
        family ((Equiv.piSplitAt selected Parts).symm (reference, rest.1)) who rest.2 before
          entry.beforeView
      rw [updated]
      exact phaseTimingWordAnchoredPolicy_unread setup mode runtime leaks bounds initial horizon
        scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
          slotBounded anchor who rest.2 past view present before entry recorded _ part)
  refine ⟨((app).policyMixture restLaw restMembers).posterior past, ?_⟩
  exact transported.trans product

end Vegas
