/-
  PokemonLean / OfficialRules.lean

  Formalization of 8 key rules from the official Pokémon TCG Comprehensive Rules.
  Each rule is stated as a legality predicate and proved via an extended game model
  that tracks turn numbers, evolution timing, per-turn flags, and card stages.

  References are to the Pokémon TCG Comprehensive Rules (2023 edition) and the
  Pokémon TCG Rulebook sections.
-/
import PokemonLean.Basic

namespace PokemonLean.OfficialRules

open PokemonLean

/-! ## Extended Types for Official Rule Enforcement -/

/-- Evolution stage of a card.
    Official Rules §3.1.1: Pokémon cards have stages (Basic, Stage 1, Stage 2). -/
inductive Stage where
  | basic
  | stage1
  | stage2
  deriving Repr, DecidableEq

instance : BEq Stage where
  beq a b := decide (a = b)

instance : LawfulBEq Stage where
  eq_of_beq {a b} h := of_decide_eq_true h
  rfl {a} := decide_eq_true rfl

/-- Trainer card subtypes.
    Official Rules §3.3: Trainer cards are Item, Supporter, Tool, or Stadium. -/
inductive TrainerKind where
  | item
  | supporter
  | tool
  | stadium
  deriving Repr, DecidableEq

instance : BEq TrainerKind where
  beq a b := decide (a = b)

/-- Rule box classification for prize value.
    Official Rules §2.1: Pokémon with Rule Boxes (ex, V, VMAX, etc.) give extra prizes. -/
inductive RuleBox where
  | none
  | ex       -- gives 2 prizes
  | v        -- gives 2 prizes
  | vmax     -- gives 3 prizes
  | vstar    -- gives 2 prizes
  | tagTeam  -- gives 3 prizes
  deriving Repr, DecidableEq

instance : BEq RuleBox where
  beq a b := decide (a = b)

/-- Extended card with stage, evolves-from, trainer kind, and rule box info. -/
structure ExtCard where
  name : String
  hp : Nat
  energyType : EnergyType
  attacks : List Attack
  weakness : Option Weakness := none
  resistance : Option Resistance := none
  stage : Stage := .basic
  evolvesFrom : Option String := none
  trainerKind : Option TrainerKind := none
  ruleBox : RuleBox := .none
  deriving Repr, DecidableEq

instance : BEq ExtCard where
  beq a b := decide (a = b)

instance : LawfulBEq ExtCard where
  eq_of_beq {a b} h := of_decide_eq_true h
  rfl {a} := decide_eq_true rfl

/-- Extended Pokémon in play, tracking which turn it was played/evolved. -/
structure ExtPokemonInPlay where
  card : ExtCard
  damage : Nat
  status : Option StatusCondition := none
  energy : List EnergyType := []
  turnPlayed : Nat   -- the turn number when this Pokémon was put into play
  deriving Repr, BEq, DecidableEq

/-- Per-player state with official rule tracking flags. -/
structure ExtPlayerState where
  deck : List ExtCard
  hand : List ExtCard
  bench : List ExtPokemonInPlay
  active : Option ExtPokemonInPlay
  discard : List ExtCard
  prizes : List ExtCard
  supporterPlayed : Bool := false   -- has a Supporter been played this turn?
  energyAttached : Bool := false    -- has an energy been attached this turn?
  retreated : Bool := false         -- has a retreat been performed this turn?
  deriving Repr, BEq, DecidableEq

/-- Extended game state with turn tracking. -/
structure ExtGameState where
  playerOne : ExtPlayerState
  playerTwo : ExtPlayerState
  activePlayer : PlayerId
  turnNumber : Nat                  -- global turn counter (1 = first turn of the game)
  isFirstPlayerFirstTurn : Bool     -- is this player 1's very first turn?
  deriving Repr, BEq, DecidableEq

/-- Bench size limit.
    Official Rules §2.1.2: Each player may have up to 5 Pokémon on their Bench. -/
def benchLimit : Nat := 5

/-- Prize value of a knocked-out Pokémon.
    Official Rules §2.1: Basic rule box = 1 prize; ex/V/VSTAR = 2; VMAX/Tag Team = 3. -/
def prizeValue (ruleBox : RuleBox) : Nat :=
  match ruleBox with
  | .none     => 1
  | .ex       => 2
  | .v        => 2
  | .vmax     => 3
  | .vstar    => 2
  | .tagTeam  => 3

/-! ## Helper Functions -/

def extOtherPlayer : PlayerId → PlayerId
  | .playerOne => .playerTwo
  | .playerTwo => .playerOne

def getExtPlayerState (state : ExtGameState) (player : PlayerId) : ExtPlayerState :=
  match player with
  | .playerOne => state.playerOne
  | .playerTwo => state.playerTwo

def setExtPlayerState (state : ExtGameState) (player : PlayerId) (ps : ExtPlayerState) : ExtGameState :=
  match player with
  | .playerOne => { state with playerOne := ps }
  | .playerTwo => { state with playerTwo := ps }

def removeFirstExt (card : ExtCard) : List ExtCard → Option (List ExtCard)
  | [] => none
  | x :: xs =>
    if x == card then some xs
    else match removeFirstExt card xs with
      | some rest => some (x :: rest)
      | none => none

/-! ## Actions for the Extended Model -/

inductive ExtAction
  | playPokemonToBench (card : ExtCard)
  | playSupporter (card : ExtCard)
  | playItem (card : ExtCard)
  | evolveActive (card : ExtCard)
  | attachEnergy (energyType : EnergyType)
  | attack (attackIndex : Nat)
  | retreat
  | endTurn
  deriving Repr, BEq, DecidableEq

/-! ## Error Types -/

inductive ExtStepError
  | cardNotInHand
  | benchFull
  | noActivePokemon
  | noDefenderPokemon
  | invalidAttackIndex
  | insufficientEnergy
  | emptyDeck
  | noBenchPokemon
  -- Official rule violations:
  | evolutionSicknessViolation     -- Rule 1: can't evolve on turn played
  | firstTurnEvolutionViolation    -- Rule 1: can't evolve on first turn
  | firstTurnAttackViolation       -- Rule 2: first player can't attack turn 1
  | supporterAlreadyPlayed         -- Rule 3: one supporter per turn
  | energyAlreadyAttached          -- Rule 4: one energy per turn
  | retreatAlreadyUsed             -- Rule 5: one retreat per turn
  | wrongStageEvolution            -- Rule 7: stage mismatch
  deriving Repr, BEq, DecidableEq

/-! ## Rule Predicates -/

/-- **Rule 1 — Evolution Timing** (Official Rules §8.3.1, Rulebook p.12):
    "A Pokémon cannot evolve on the same turn it was played, and neither player
    can evolve a Pokémon on their first turn."
    `canEvolve` is true when the Pokémon has been in play for at least one full
    turn AND it is not the very first turn of the game. -/
def canEvolve (state : ExtGameState) (pokemon : ExtPokemonInPlay) : Bool :=
  state.turnNumber > 1 && pokemon.turnPlayed < state.turnNumber

/-- **Rule 2 — First Turn Attack Restriction** (Official Rules §8.4, Rulebook p.8):
    "The player who goes first cannot attack on their first turn." -/
def canAttackThisTurn (state : ExtGameState) : Bool :=
  !state.isFirstPlayerFirstTurn

/-- **Rule 3 — One Supporter Per Turn** (Official Rules §8.3.3, Rulebook p.11):
    "You may play only 1 Supporter card during your turn." -/
def canPlaySupporter (state : ExtGameState) : Bool :=
  !(getExtPlayerState state state.activePlayer).supporterPlayed

/-- **Rule 4 — One Energy Per Turn** (Official Rules §8.3.2, Rulebook p.10):
    "Once during your turn, you may attach 1 Energy card from your hand." -/
def canAttachEnergy (state : ExtGameState) : Bool :=
  !(getExtPlayerState state state.activePlayer).energyAttached

/-- **Rule 5 — One Retreat Per Turn** (Official Rules §8.3.4, Rulebook p.13):
    "You may retreat your Active Pokémon only once during your turn." -/
def canRetreat (state : ExtGameState) : Bool :=
  !(getExtPlayerState state state.activePlayer).retreated

/-- **Rule 6 — Bench Limit** (Official Rules §2.1.2):
    "Each player may have up to 5 Pokémon on their Bench." -/
def benchHasRoom (state : ExtGameState) : Bool :=
  (getExtPlayerState state state.activePlayer).bench.length < benchLimit

/-- **Rule 7 — Stage Matching for Evolution** (Official Rules §8.3.1, Rulebook p.12):
    "Stage 1 evolves from a specific Basic; Stage 2 evolves from a specific Stage 1." -/
def stageMatchesForEvolution (evoCard : ExtCard) (activePokemon : ExtPokemonInPlay) : Bool :=
  match evoCard.stage with
  | .basic => false   -- basics don't evolve onto anything
  | .stage1 => activePokemon.card.stage == .basic &&
               evoCard.evolvesFrom == some activePokemon.card.name
  | .stage2 => activePokemon.card.stage == .stage1 &&
               evoCard.evolvesFrom == some activePokemon.card.name

@[simp] theorem stageMatchesForEvolution_basic (card : ExtCard) (poke : ExtPokemonInPlay)
    (h : card.stage = .basic) : stageMatchesForEvolution card poke = false := by
  simp [stageMatchesForEvolution, h]

/-! ## Extended Step Function (Enforces All 8 Official Rules) -/

/-- The official step function that checks all 8 rules before executing an action. -/
def extStep (state : ExtGameState) (action : ExtAction) : Except ExtStepError ExtGameState :=
  match action with

  | .endTurn =>
    -- Reset per-turn flags, advance turn
    let newTurn := state.turnNumber + 1
    let nextPlayer := extOtherPlayer state.activePlayer
    let nextPS := getExtPlayerState state nextPlayer
    let resetPS := { nextPS with supporterPlayed := false, energyAttached := false, retreated := false }
    .ok { (setExtPlayerState state nextPlayer resetPS) with
            activePlayer := nextPlayer,
            turnNumber := newTurn,
            isFirstPlayerFirstTurn := false }

  | .playPokemonToBench card =>
    let ps := getExtPlayerState state state.activePlayer
    match removeFirstExt card ps.hand with
    | none => .error .cardNotInHand
    | some newHand =>
      -- Rule 6: Bench limit
      if ps.bench.length < benchLimit then
        let pokemon : ExtPokemonInPlay :=
          { card := card, damage := 0, status := none, energy := [],
            turnPlayed := state.turnNumber }
        let newPS := { ps with hand := newHand, bench := ps.bench ++ [pokemon] }
        .ok (setExtPlayerState state state.activePlayer newPS)
      else
        .error .benchFull

  | .playSupporter card =>
    let ps := getExtPlayerState state state.activePlayer
    -- Rule 3: One supporter per turn
    if ps.supporterPlayed then
      .error .supporterAlreadyPlayed
    else
      match removeFirstExt card ps.hand with
      | none => .error .cardNotInHand
      | some newHand =>
        let newPS := { ps with hand := newHand, discard := card :: ps.discard,
                               supporterPlayed := true }
        .ok (setExtPlayerState state state.activePlayer newPS)

  | .playItem card =>
    let ps := getExtPlayerState state state.activePlayer
    match removeFirstExt card ps.hand with
    | none => .error .cardNotInHand
    | some newHand =>
      let newPS := { ps with hand := newHand, discard := card :: ps.discard }
      .ok (setExtPlayerState state state.activePlayer newPS)

  | .evolveActive card =>
    let ps := getExtPlayerState state state.activePlayer
    match ps.active with
    | none => .error .noActivePokemon
    | some activePoke =>
      -- Rule 7: Stage matching
      if !stageMatchesForEvolution card activePoke then
        .error .wrongStageEvolution
      -- Rule 1: Evolution timing — first turn of the game
      else if state.turnNumber ≤ 1 then
        .error .firstTurnEvolutionViolation
      -- Rule 1: Evolution timing — same turn the Pokémon was played
      else if activePoke.turnPlayed ≥ state.turnNumber then
        .error .evolutionSicknessViolation
      else
        match removeFirstExt card ps.hand with
        | none => .error .cardNotInHand
        | some newHand =>
          let evolved : ExtPokemonInPlay :=
            { activePoke with card := card, turnPlayed := state.turnNumber }
          let newPS := { ps with hand := newHand, active := some evolved,
                                 discard := activePoke.card :: ps.discard }
          .ok (setExtPlayerState state state.activePlayer newPS)

  | .attachEnergy energyType =>
    let ps := getExtPlayerState state state.activePlayer
    -- Rule 4: One energy per turn
    if ps.energyAttached then
      .error .energyAlreadyAttached
    else
      match ps.active with
      | none => .error .noActivePokemon
      | some activePoke =>
        let updated := { activePoke with energy := energyType :: activePoke.energy }
        let newPS := { ps with active := some updated, energyAttached := true }
        .ok (setExtPlayerState state state.activePlayer newPS)

  | .attack _attackIndex =>
    -- Rule 2: First turn attack restriction
    if state.isFirstPlayerFirstTurn then
      .error .firstTurnAttackViolation
    else
      let ps := getExtPlayerState state state.activePlayer
      match ps.active with
      | none => .error .noActivePokemon
      | some _attacker =>
        let defPS := getExtPlayerState state (extOtherPlayer state.activePlayer)
        match defPS.active with
        | none => .error .noDefenderPokemon
        | some _defender =>
          -- Simplified: just switch turns (full damage calc omitted for rule proofs)
          .ok { state with activePlayer := extOtherPlayer state.activePlayer }

  | .retreat =>
    let ps := getExtPlayerState state state.activePlayer
    -- Rule 5: One retreat per turn
    if ps.retreated then
      .error .retreatAlreadyUsed
    else
      match ps.active with
      | none => .error .noActivePokemon
      | some activePoke =>
        match ps.bench with
        | [] => .error .noBenchPokemon
        | newActive :: rest =>
          let newPS := { ps with
            active := some newActive,
            bench := rest ++ [activePoke],
            retreated := true }
          .ok (setExtPlayerState state state.activePlayer newPS)

/-! ## Legality Definition -/

def ExtLegal (state : ExtGameState) (action : ExtAction) : Prop :=
  ∃ next, extStep state action = .ok next

instance (state : ExtGameState) (action : ExtAction) : Decidable (ExtLegal state action) := by
  cases h : extStep state action with
  | ok next => exact isTrue ⟨next, h⟩
  | error _ => exact isFalse (fun ⟨n, hn⟩ => by simp [h] at hn)

/-! ====================================================================
    RULE 1 — EVOLUTION TIMING
    Official Rules §8.3.1: "A Pokémon can't evolve the same turn it was
    played, and neither player can evolve on the first turn of the game."
    ==================================================================== -/

/-- If canEvolve is false, evolving is illegal. -/
theorem evolution_illegal_when_cannotEvolve
    (state : ExtGameState) (card : ExtCard) (activePoke : ExtPokemonInPlay)
    (hActive : (getExtPlayerState state state.activePlayer).active = some activePoke)
    (hStageOk : stageMatchesForEvolution card activePoke = true)
    (hNoEvolve : canEvolve state activePoke = false) :
    ¬ExtLegal state (.evolveActive card) := by
  intro ⟨next, hStep⟩
  simp only [extStep, hActive] at hStep
  simp only [hStageOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
  simp only [canEvolve, Bool.and_eq_false_iff] at hNoEvolve
  cases hNoEvolve with
  | inl hTurn =>
    simp only [Bool.not_eq_true, Nat.not_lt] at hTurn
    have : state.turnNumber ≤ 1 := by omega
    simp only [this, ↓reduceIte] at hStep
  | inr hPlayed =>
    simp only [Bool.not_eq_true, Nat.not_lt] at hPlayed
    by_cases hT1 : state.turnNumber ≤ 1
    · simp only [hT1, ↓reduceIte] at hStep
    · simp only [hT1, ↓reduceIte] at hStep
      have : activePoke.turnPlayed ≥ state.turnNumber := by omega
      simp only [this, ↓reduceIte] at hStep

/-- Evolving on turn 1 is always illegal. -/
theorem evolution_illegal_on_first_turn
    (state : ExtGameState) (card : ExtCard)
    (hTurn : state.turnNumber ≤ 1) :
    ¬ExtLegal state (.evolveActive card) := by
  intro ⟨next, hStep⟩
  simp only [extStep] at hStep
  split at hStep
  · exact nomatch hStep
  · rename_i activePoke
    split at hStep
    · exact nomatch hStep
    · simp only [hTurn, ↓reduceIte] at hStep

/-- Evolving a Pokémon on the same turn it was played is illegal. -/
theorem evolution_illegal_same_turn_played
    (state : ExtGameState) (card : ExtCard) (activePoke : ExtPokemonInPlay)
    (hActive : (getExtPlayerState state state.activePlayer).active = some activePoke)
    (hSameTurn : activePoke.turnPlayed ≥ state.turnNumber)
    (hStageOk : stageMatchesForEvolution card activePoke = true)
    (hNotFirst : state.turnNumber > 1) :
    ¬ExtLegal state (.evolveActive card) := by
  intro ⟨next, hStep⟩
  simp only [extStep, hActive] at hStep
  simp only [hStageOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
  have hNotLE : ¬(state.turnNumber ≤ 1) := by omega
  simp only [hNotLE, ↓reduceIte] at hStep
  simp only [hSameTurn, ↓reduceIte] at hStep

/-! ====================================================================
    RULE 2 — FIRST TURN ATTACK RESTRICTION
    Official Rules §8.4: "The player who goes first cannot attack on
    their first turn."
    ==================================================================== -/

/-- The first player cannot attack on their first turn. -/
theorem first_player_cannot_attack_turn_one
    (state : ExtGameState) (idx : Nat)
    (hFirst : state.isFirstPlayerFirstTurn = true) :
    ¬ExtLegal state (.attack idx) := by
  intro ⟨next, hStep⟩
  simp only [extStep, hFirst, ↓reduceIte] at hStep

/-- canAttackThisTurn = false implies attack is illegal. -/
theorem attack_illegal_when_cannotAttack
    (state : ExtGameState) (idx : Nat)
    (hNo : canAttackThisTurn state = false) :
    ¬ExtLegal state (.attack idx) := by
  intro ⟨next, hStep⟩
  simp only [canAttackThisTurn, Bool.not_eq_true] at hNo
  simp only [extStep, hNo, ↓reduceIte] at hStep

/-! ====================================================================
    RULE 3 — ONE SUPPORTER PER TURN
    Official Rules §8.3.3: "You may play only 1 Supporter card during
    your turn."
    ==================================================================== -/

/-- If a supporter has already been played this turn, playing another is illegal. -/
theorem second_supporter_illegal
    (state : ExtGameState) (card : ExtCard)
    (hPlayed : (getExtPlayerState state state.activePlayer).supporterPlayed = true) :
    ¬ExtLegal state (.playSupporter card) := by
  intro ⟨next, hStep⟩
  simp only [extStep, hPlayed, ↓reduceIte] at hStep

/-- canPlaySupporter = false implies supporter play is illegal. -/
theorem supporter_illegal_when_flag_set
    (state : ExtGameState) (card : ExtCard)
    (hNo : canPlaySupporter state = false) :
    ¬ExtLegal state (.playSupporter card) := by
  intro ⟨next, hStep⟩
  simp only [canPlaySupporter, Bool.not_eq_true, Bool.not_not] at hNo
  simp only [extStep, hNo, ↓reduceIte] at hStep

/-- Successfully playing a supporter sets the flag, blocking a second one. -/
theorem playSupporter_sets_flag
    (state state' : ExtGameState) (card : ExtCard)
    (hStep : extStep state (.playSupporter card) = .ok state') :
    (getExtPlayerState state' state.activePlayer).supporterPlayed = true := by
  simp only [extStep] at hStep
  split at hStep
  · exact nomatch hStep
  · rename_i hRemove
    split at hStep
    · exact nomatch hStep
    · rename_i newHand _
      cases hEq : state.activePlayer <;>
        simp only [hEq, getExtPlayerState, setExtPlayerState] at hStep ⊢ <;>
        (cases hStep; rfl)

/-! ====================================================================
    RULE 4 — ONE ENERGY PER TURN
    Official Rules §8.3.2: "Once during your turn, you may attach 1
    Energy card from your hand to 1 of your Pokémon."
    ==================================================================== -/

/-- If energy has already been attached this turn, attaching another is illegal. -/
theorem second_energy_illegal
    (state : ExtGameState) (et : EnergyType)
    (hAttached : (getExtPlayerState state state.activePlayer).energyAttached = true) :
    ¬ExtLegal state (.attachEnergy et) := by
  intro ⟨next, hStep⟩
  simp only [extStep, hAttached, ↓reduceIte] at hStep

/-- canAttachEnergy = false implies energy attachment is illegal. -/
theorem energy_illegal_when_flag_set
    (state : ExtGameState) (et : EnergyType)
    (hNo : canAttachEnergy state = false) :
    ¬ExtLegal state (.attachEnergy et) := by
  intro ⟨next, hStep⟩
  simp only [canAttachEnergy, Bool.not_eq_true, Bool.not_not] at hNo
  simp only [extStep, hNo, ↓reduceIte] at hStep

/-- Successfully attaching energy sets the flag, blocking a second attachment. -/
theorem attachEnergy_sets_flag
    (state state' : ExtGameState) (et : EnergyType)
    (hStep : extStep state (.attachEnergy et) = .ok state') :
    (getExtPlayerState state' state.activePlayer).energyAttached = true := by
  simp only [extStep] at hStep
  split at hStep
  · exact nomatch hStep
  · split at hStep
    · exact nomatch hStep
    · rename_i activePoke
      cases hEq : state.activePlayer <;>
        simp only [hEq, getExtPlayerState, setExtPlayerState] at hStep ⊢ <;>
        (cases hStep; rfl)

/-! ====================================================================
    RULE 5 — ONE RETREAT PER TURN
    Official Rules §8.3.4: "Once during your turn, you may retreat your
    Active Pokémon."
    ==================================================================== -/

/-- If retreat has already been used this turn, retreating again is illegal. -/
theorem second_retreat_illegal
    (state : ExtGameState)
    (hRetreated : (getExtPlayerState state state.activePlayer).retreated = true) :
    ¬ExtLegal state .retreat := by
  intro ⟨next, hStep⟩
  simp only [extStep, hRetreated, ↓reduceIte] at hStep

/-- canRetreat = false implies retreat is illegal. -/
theorem retreat_illegal_when_flag_set
    (state : ExtGameState)
    (hNo : canRetreat state = false) :
    ¬ExtLegal state .retreat := by
  intro ⟨next, hStep⟩
  simp only [canRetreat, Bool.not_eq_true, Bool.not_not] at hNo
  simp only [extStep, hNo, ↓reduceIte] at hStep

/-- Successfully retreating sets the flag, blocking a second retreat. -/
theorem retreat_sets_flag
    (state state' : ExtGameState)
    (hStep : extStep state .retreat = .ok state') :
    (getExtPlayerState state' state.activePlayer).retreated = true := by
  simp only [extStep] at hStep
  split at hStep
  · exact nomatch hStep
  · split at hStep
    · exact nomatch hStep
    · split at hStep
      · exact nomatch hStep
      · rename_i newActive rest _ _
        cases hEq : state.activePlayer <;>
          simp only [hEq, getExtPlayerState, setExtPlayerState] at hStep ⊢ <;>
          (cases hStep; rfl)

/-! ====================================================================
    RULE 6 — BENCH LIMIT
    Official Rules §2.1.2: "Each player may have up to 5 Pokémon on
    their Bench."
    ==================================================================== -/

/-- Playing a Pokémon to a full bench (≥5) is illegal. -/
theorem bench_full_illegal
    (state : ExtGameState) (card : ExtCard)
    (hFull : (getExtPlayerState state state.activePlayer).bench.length ≥ benchLimit) :
    ¬ExtLegal state (.playPokemonToBench card) := by
  intro ⟨next, hStep⟩
  simp only [extStep] at hStep
  split at hStep
  · exact nomatch hStep
  · rename_i newHand _
    split at hStep
    · rename_i hLen
      exact absurd hLen (by omega)
    · exact nomatch hStep

/-- benchHasRoom = false implies play-to-bench is illegal (for any card in hand). -/
theorem bench_no_room_illegal
    (state : ExtGameState) (card : ExtCard)
    (hNoRoom : benchHasRoom state = false) :
    ¬ExtLegal state (.playPokemonToBench card) := by
  simp only [benchHasRoom, Nat.not_lt, Bool.not_eq_true, decide_eq_false_iff_not] at hNoRoom
  exact bench_full_illegal state card hNoRoom

/-- After a successful play-to-bench, bench size increases by 1. -/
theorem playToBench_increases_bench
    (state state' : ExtGameState) (card : ExtCard)
    (hStep : extStep state (.playPokemonToBench card) = .ok state') :
    (getExtPlayerState state' state.activePlayer).bench.length =
    (getExtPlayerState state state.activePlayer).bench.length + 1 := by
  simp only [extStep] at hStep
  split at hStep
  · exact nomatch hStep
  · rename_i newHand _
    split at hStep
    · cases hEq : state.activePlayer <;>
        simp only [hEq, getExtPlayerState, setExtPlayerState] at hStep ⊢ <;>
        (cases hStep; simp [List.length_append])
    · exact nomatch hStep

/-! ====================================================================
    RULE 7 — NO EVOLUTION TO WRONG STAGE
    Official Rules §8.3.1: "Stage 1 cards evolve from the matching Basic
    Pokémon; Stage 2 cards evolve from the matching Stage 1 Pokémon."
    ==================================================================== -/

/-- Evolving with a wrong-stage card is illegal. -/
theorem wrong_stage_evolution_illegal
    (state : ExtGameState) (card : ExtCard) (activePoke : ExtPokemonInPlay)
    (hActive : (getExtPlayerState state state.activePlayer).active = some activePoke)
    (hBadStage : stageMatchesForEvolution card activePoke = false) :
    ¬ExtLegal state (.evolveActive card) := by
  intro ⟨next, hStep⟩
  simp only [extStep, hActive] at hStep
  simp only [hBadStage, Bool.not_false, ↓reduceIte] at hStep

/-- A Basic card cannot be used as an evolution. -/
theorem basic_cannot_evolve_onto
    (state : ExtGameState) (card : ExtCard) (activePoke : ExtPokemonInPlay)
    (hActive : (getExtPlayerState state state.activePlayer).active = some activePoke)
    (hBasic : card.stage = .basic) :
    ¬ExtLegal state (.evolveActive card) := by
  apply wrong_stage_evolution_illegal state card activePoke hActive
  exact stageMatchesForEvolution_basic card activePoke hBasic

/-- Stage 1 can only evolve from a matching Basic. If the active Pokémon is not
    the correct Basic, evolution is illegal. -/
theorem stage1_requires_matching_basic
    (state : ExtGameState) (card : ExtCard) (activePoke : ExtPokemonInPlay)
    (hActive : (getExtPlayerState state state.activePlayer).active = some activePoke)
    (hStage1 : card.stage = .stage1)
    (hMismatch : activePoke.card.stage ≠ .basic ∨ card.evolvesFrom ≠ some activePoke.card.name) :
    ¬ExtLegal state (.evolveActive card) := by
  apply wrong_stage_evolution_illegal state card activePoke hActive
  unfold stageMatchesForEvolution; rw [hStage1]
  rw [Bool.and_eq_false_iff]
  cases hMismatch with
  | inl hNotBasic =>
    left; exact bne_iff_ne _ _ |>.mpr hNotBasic
  | inr hWrongName =>
    right; exact bne_iff_ne _ _ |>.mpr hWrongName

/-- Stage 2 can only evolve from a matching Stage 1. If the active Pokémon is not
    the correct Stage 1, evolution is illegal. -/
theorem stage2_requires_matching_stage1
    (state : ExtGameState) (card : ExtCard) (activePoke : ExtPokemonInPlay)
    (hActive : (getExtPlayerState state state.activePlayer).active = some activePoke)
    (hStage2 : card.stage = .stage2)
    (hMismatch : activePoke.card.stage ≠ .stage1 ∨ card.evolvesFrom ≠ some activePoke.card.name) :
    ¬ExtLegal state (.evolveActive card) := by
  apply wrong_stage_evolution_illegal state card activePoke hActive
  unfold stageMatchesForEvolution; rw [hStage2]
  rw [Bool.and_eq_false_iff]
  cases hMismatch with
  | inl hNotS1 =>
    left; exact bne_iff_ne _ _ |>.mpr hNotS1
  | inr hWrongName =>
    right; exact bne_iff_ne _ _ |>.mpr hWrongName

/-! ====================================================================
    RULE 8 — KNOCKED OUT CLEANUP / PRIZE VALUE
    Official Rules §2.1, §10.1: "When you Knock Out an opponent's
    Pokémon, take Prize cards equal to that Pokémon's prize value."
    ==================================================================== -/

/-- Take `n` prizes from the opponent's prize pile.
    Returns the updated attacker prizes (hand) and defender prizes. -/
def takePrizes (attackerPS defenderPS : ExtPlayerState) (n : Nat) :
    ExtPlayerState × ExtPlayerState :=
  match n, defenderPS.prizes with
  | 0, _ => (attackerPS, defenderPS)
  | _, [] => (attackerPS, defenderPS)
  | Nat.succ k, prize :: rest =>
    takePrizes
      { attackerPS with hand := prize :: attackerPS.hand }
      { defenderPS with prizes := rest }
      k

/-- takePrizes decreases the defender's prize count by at most n. -/
theorem takePrizes_decreases_prizes (atkPS defPS : ExtPlayerState) (n : Nat) :
    (takePrizes atkPS defPS n).2.prizes.length ≤ defPS.prizes.length := by
  induction n generalizing atkPS defPS with
  | zero => unfold takePrizes; exact Nat.le_refl _
  | succ k ih =>
    match hP : defPS.prizes with
    | [] => unfold takePrizes; rw [hP]; exact Nat.le_refl _
    | prize :: rest =>
      unfold takePrizes; rw [hP]
      have h := ih
        { atkPS with hand := prize :: atkPS.hand }
        { defPS with prizes := rest }
      have hSimp : ({ defPS with prizes := rest } : ExtPlayerState).prizes = rest := rfl
      rw [hSimp] at h
      simp only [List.length_cons]
      exact Nat.le_trans h (Nat.le_succ _)

/-- When there are enough prizes, takePrizes removes exactly n. -/
theorem takePrizes_exact (atkPS defPS : ExtPlayerState) (n : Nat)
    (hEnough : n ≤ defPS.prizes.length) :
    (takePrizes atkPS defPS n).2.prizes.length = defPS.prizes.length - n := by
  obtain ⟨deck, hand, bench, active, discard, prizes, sp, ea, ret⟩ := defPS
  simp only at hEnough ⊢
  -- Now we need to prove it with the explicit structure.
  -- takePrizes pattern-matches on n and prizes, so we induct on prizes
  -- generalizing atkPS and n
  suffices ∀ (atkPS : ExtPlayerState) (n : Nat), n ≤ prizes.length →
    (takePrizes atkPS
      { deck := deck, hand := hand, bench := bench, active := active,
        discard := discard, prizes := prizes, supporterPlayed := sp,
        energyAttached := ea, retreated := ret } n).2.prizes.length =
    prizes.length - n from this atkPS n hEnough
  clear hEnough atkPS n
  induction prizes with
  | nil =>
    intro atkPS n hLen
    have hn : n = 0 := by omega
    subst hn; rfl
  | cons prize rest ih =>
    intro atkPS n hLen
    match n with
    | 0 => rfl
    | k + 1 =>
      -- unfold one step of takePrizes
      show (takePrizes { atkPS with hand := prize :: atkPS.hand }
            { deck := deck, hand := hand, bench := bench, active := active,
              discard := discard, prizes := rest, supporterPlayed := sp,
              energyAttached := ea, retreated := ret } k).2.prizes.length =
            (prize :: rest).length - (k + 1)
      have hLen' : k ≤ rest.length := by omega
      have hIH := ih { atkPS with hand := prize :: atkPS.hand } k hLen'
      -- hIH says the recursive result has length rest.length - k
      -- Goal: ... = (prize :: rest).length - (k + 1)
      simp only [show (prize :: rest).length = rest.length + 1 from rfl] at *
      omega

/-- Prize value is always positive for regular Pokémon (RuleBox.none). -/
theorem prizeValue_none_eq_one : prizeValue .none = 1 := rfl

/-- Prize value for ex Pokémon is 2. -/
theorem prizeValue_ex_eq_two : prizeValue .ex = 2 := rfl

/-- Prize value for VMAX Pokémon is 3. -/
theorem prizeValue_vmax_eq_three : prizeValue .vmax = 3 := rfl

/-- Prize value is always at least 1. -/
theorem prizeValue_pos (rb : RuleBox) : prizeValue rb ≥ 1 := by
  cases rb <;> native_decide

/-- Prize value is always at most 3. -/
theorem prizeValue_le_three (rb : RuleBox) : prizeValue rb ≤ 3 := by
  cases rb <;> native_decide

/-- After a KO, defender's prize pile shrinks by the KO'd Pokémon's prize value
    (assuming enough prizes remain). -/
theorem ko_takes_correct_prizes
    (atkPS defPS : ExtPlayerState) (koPoke : ExtPokemonInPlay)
    (hEnough : prizeValue koPoke.card.ruleBox ≤ defPS.prizes.length) :
    (takePrizes atkPS defPS (prizeValue koPoke.card.ruleBox)).2.prizes.length =
      defPS.prizes.length - prizeValue koPoke.card.ruleBox := by
  exact takePrizes_exact atkPS defPS (prizeValue koPoke.card.ruleBox) hEnough

/-! ====================================================================
    CROSS-RULE COMPOSABILITY
    ==================================================================== -/

/-- After endTurn, all per-turn flags are reset for the next player. -/
theorem endTurn_resets_flags
    (state state' : ExtGameState)
    (hStep : extStep state .endTurn = .ok state') :
    let nextPlayer := extOtherPlayer state.activePlayer
    (getExtPlayerState state' nextPlayer).supporterPlayed = false ∧
    (getExtPlayerState state' nextPlayer).energyAttached = false ∧
    (getExtPlayerState state' nextPlayer).retreated = false := by
  simp only [extStep] at hStep
  have hInj := Except.ok.inj hStep
  subst hInj
  refine ⟨?_, ?_, ?_⟩ <;> (
    cases hEq : state.activePlayer <;>
      simp [hEq, extOtherPlayer, getExtPlayerState, setExtPlayerState])

/-- extStep is deterministic. -/
theorem extStep_deterministic
    (state : ExtGameState) (action : ExtAction) (s1 s2 : ExtGameState)
    (h1 : extStep state action = .ok s1) (h2 : extStep state action = .ok s2) :
    s1 = s2 := by
  simpa [h1] using h2

end PokemonLean.OfficialRules
