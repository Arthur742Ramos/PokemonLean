import PokemonLean.Core.Types

inductive EnergyType
  | fire
  | water
  | grass
  | lightning
  | psychic
  | fighting
  | dark
  | metal
  | fairy
  | dragon
  | colorless
  deriving Repr, DecidableEq

instance : BEq EnergyType where
  beq a b := decide (a = b)

instance : LawfulBEq EnergyType where
  eq_of_beq {a b} h := of_decide_eq_true h
  rfl {a} := decide_eq_true rfl

inductive StatusCondition
  | asleep
  | burned
  | confused
  | paralyzed
  | poisoned
  deriving Repr, BEq, DecidableEq

inductive Weather
  | clear
  | sunny
  | rain
  | sandstorm
  | hail
  deriving Repr, BEq, DecidableEq

inductive AttackEffect
  | applyStatus (condition : StatusCondition)
  | heal (amount : Nat)
  | drawCards (count : Nat)
  | addDamage (amount : Nat)
  deriving Repr, BEq, DecidableEq

structure Attack where
  name : String
  baseDamage : Nat
  effects : List AttackEffect
  energyCost : List EnergyType := []
  deriving Repr, BEq, DecidableEq

structure Weakness where
  energyType : EnergyType
  multiplier : Nat := 2
  deriving Repr, BEq, DecidableEq

structure Resistance where
  energyType : EnergyType
  amount : Nat := 30
  deriving Repr, BEq, DecidableEq

structure Card where
  name : String
  hp : Nat
  energyType : EnergyType
  attacks : List Attack
  weakness : Option Weakness := none
  resistance : Option Resistance := none
  deriving Repr, DecidableEq

instance : BEq Card where
  beq a b := decide (a = b)

instance : LawfulBEq Card where
  eq_of_beq {a b} h := of_decide_eq_true h
  rfl {a} := decide_eq_true rfl

def isTrainer (card : Card) : Bool :=
  card.attacks.isEmpty

structure PokemonInPlay where
  card : Card
  damage : Nat
  status : Option StatusCondition
  energy : List EnergyType := []
  deriving Repr, BEq, DecidableEq

structure PlayerState where
  deck : List Card
  hand : List Card
  bench : List PokemonInPlay
  active : Option PokemonInPlay
  discard : List Card
  prizes : List Card
  deriving Repr, BEq, DecidableEq

inductive PlayerId
  | playerOne
  | playerTwo
  deriving Repr, BEq, DecidableEq

structure GameState where
  playerOne : PlayerState
  playerTwo : PlayerState
  activePlayer : PlayerId
  deriving Repr, BEq, DecidableEq

inductive Effect
  | applyStatus (condition : StatusCondition)
  | heal (amount : Nat)
  | addDamage (amount : Nat)
  deriving Repr, BEq, DecidableEq

abbrev EffectStack := List Effect

inductive Action
  | endTurn
  | playCard (card : Card)
  | attachEnergy (energyType : EnergyType)
  | attack (attackIndex : Nat)
  deriving Repr, BEq, DecidableEq

-- Actions allowed during a single Turn 1 for player one.
inductive TurnOneActions : List Action -> Prop
  | nil : TurnOneActions []
  | play {card : Card} {actions : List Action} (h : TurnOneActions actions) :
      TurnOneActions (Action.playCard card :: actions)
  | attach {energyType : EnergyType} {actions : List Action} (h : TurnOneActions actions) :
      TurnOneActions (Action.attachEnergy energyType :: actions)
  | endTurn : TurnOneActions [Action.endTurn]

def otherPlayer : PlayerId -> PlayerId
  | .playerOne => .playerTwo
  | .playerTwo => .playerOne

def getPlayerState (state : GameState) (player : PlayerId) : PlayerState :=
  match player with
  | .playerOne => state.playerOne
  | .playerTwo => state.playerTwo

def setPlayerState (state : GameState) (player : PlayerId) (playerState : PlayerState) : GameState :=
  match player with
  | .playerOne => { state with playerOne := playerState }
  | .playerTwo => { state with playerTwo := playerState }

def removeFirst (card : Card) : List Card -> Option (List Card)
  | [] => none
  | x :: xs =>
    if x == card then
      some xs
    else
      match removeFirst card xs with
      | some rest => some (x :: rest)
      | none => none

def removeFirstEnergy (energyType : EnergyType) : List EnergyType -> Option (List EnergyType)
  | [] => none
  | x :: xs =>
    if energyType == .colorless then
      some xs
    else if x == energyType then
      some xs
    else
      match removeFirstEnergy energyType xs with
      | some rest => some (x :: rest)
      | none => none

theorem removeFirstEnergy_length (energyType : EnergyType) (xs : List EnergyType) (ys : List EnergyType)
    (h : removeFirstEnergy energyType xs = some ys) : ys.length + 1 = xs.length := by
  induction xs generalizing ys with
  | nil =>
    simp [removeFirstEnergy] at h
  | cons x xs ih =>
    by_cases hColorless : energyType == .colorless
    · simp [removeFirstEnergy, hColorless] at h
      cases h
      simp
    · by_cases hEq : x == energyType
      · simp [removeFirstEnergy, hColorless, hEq] at h
        cases h
        simp
      · cases hRec : removeFirstEnergy energyType xs with
        | none =>
          simp [removeFirstEnergy, hColorless, hEq, hRec] at h
        | some rest =>
          simp [removeFirstEnergy, hColorless, hEq, hRec] at h
          cases h
          simp [ih rest hRec]

def energyCostSatisfied : List EnergyType -> List EnergyType -> Bool
  | [], _ => true
  | required :: rest, energy =>
    match removeFirstEnergy required energy with
    | some remaining => energyCostSatisfied rest remaining
    | none => false

def consumeEnergyCost : List EnergyType -> List EnergyType -> Option (List EnergyType)
  | [], energy => some energy
  | required :: rest, energy =>
    match removeFirstEnergy required energy with
    | some remaining => consumeEnergyCost rest remaining
    | none => none

theorem consumeEnergyCost_sound :
    ∀ required energy remaining,
      consumeEnergyCost required energy = some remaining →
      energyCostSatisfied required energy = true := by
  intro required
  induction required with
  | nil =>
    intro energy remaining h
    simp [consumeEnergyCost] at h
    simp [energyCostSatisfied]
  | cons req rest ih =>
    intro energy remaining h
    cases hRemove : removeFirstEnergy req energy with
    | none =>
      simp [consumeEnergyCost, hRemove] at h
    | some remaining' =>
      simp [consumeEnergyCost, hRemove] at h
      have hRest := ih remaining' remaining h
      simp [energyCostSatisfied, hRemove, hRest]

theorem energyCostSatisfied_complete :
    ∀ required energy,
      energyCostSatisfied required energy = true →
      ∃ remaining, consumeEnergyCost required energy = some remaining := by
  intro required
  induction required with
  | nil =>
    intro energy h
    exact ⟨energy, by simp [consumeEnergyCost]⟩
  | cons req rest ih =>
    intro energy h
    cases hRemove : removeFirstEnergy req energy with
    | none =>
      simp [energyCostSatisfied, hRemove] at h
    | some remaining' =>
      have hRest : energyCostSatisfied rest remaining' = true := by
        simpa [energyCostSatisfied, hRemove] using h
      rcases ih remaining' hRest with ⟨remaining, hConsume⟩
      exact ⟨remaining, by simp [consumeEnergyCost, hRemove, hConsume]⟩

theorem energyCostSatisfied_iff_consume (required : List EnergyType) (energy : List EnergyType) :
    energyCostSatisfied required energy = true ↔
      ∃ remaining, consumeEnergyCost required energy = some remaining := by
  constructor
  · exact energyCostSatisfied_complete required energy
  · intro h
    rcases h with ⟨remaining, hConsume⟩
    exact consumeEnergyCost_sound required energy remaining hConsume

def retreatCost : List EnergyType :=
  [.colorless]

def payRetreatCost (pokemon : PokemonInPlay) : Option PokemonInPlay :=
  match consumeEnergyCost retreatCost pokemon.energy with
  | none => none
  | some remaining => some { pokemon with energy := remaining }

theorem payRetreatCost_sound (pokemon : PokemonInPlay) (paid : PokemonInPlay)
    (h : payRetreatCost pokemon = some paid) :
    energyCostSatisfied retreatCost pokemon.energy = true := by
  cases hConsume : consumeEnergyCost retreatCost pokemon.energy with
  | none =>
    simp [payRetreatCost, hConsume] at h
  | some remaining =>
    simp [payRetreatCost, hConsume] at h
    cases h
    exact (energyCostSatisfied_iff_consume retreatCost pokemon.energy).2 ⟨remaining, hConsume⟩

theorem payRetreatCost_length (pokemon : PokemonInPlay) (paid : PokemonInPlay)
    (h : payRetreatCost pokemon = some paid) :
    paid.energy.length + 1 = pokemon.energy.length := by
  simp [payRetreatCost, retreatCost] at h
  cases hConsume : removeFirstEnergy .colorless pokemon.energy with
  | none =>
    simp [consumeEnergyCost, hConsume] at h
  | some remaining =>
    simp [consumeEnergyCost, hConsume] at h
    cases h
    simpa using removeFirstEnergy_length .colorless pokemon.energy remaining hConsume

theorem payRetreatCost_iff (pokemon : PokemonInPlay) :
    (∃ paid, payRetreatCost pokemon = some paid) ↔
      energyCostSatisfied retreatCost pokemon.energy = true := by
  constructor
  · intro h
    rcases h with ⟨paid, hPaid⟩
    exact payRetreatCost_sound pokemon paid hPaid
  · intro h
    have hConsume : ∃ remaining, consumeEnergyCost retreatCost pokemon.energy = some remaining :=
      (energyCostSatisfied_iff_consume retreatCost pokemon.energy).1 h
    rcases hConsume with ⟨remaining, hConsume⟩
    refine ⟨{ pokemon with energy := remaining }, ?_⟩
    simp [payRetreatCost, hConsume]

def statusDamage : StatusCondition -> Nat
  | .poisoned => 10
  | .burned => 20
  | .asleep => 0
  | .confused => 0
  | .paralyzed => 0

@[simp] theorem statusDamage_poisoned : statusDamage .poisoned = 10 := rfl
@[simp] theorem statusDamage_burned : statusDamage .burned = 20 := rfl
@[simp] theorem statusDamage_asleep : statusDamage .asleep = 0 := rfl
@[simp] theorem statusDamage_confused : statusDamage .confused = 0 := rfl
@[simp] theorem statusDamage_paralyzed : statusDamage .paralyzed = 0 := rfl

theorem statusDamage_le_twenty (condition : StatusCondition) : statusDamage condition ≤ 20 := by
  cases condition <;> simp [statusDamage]

theorem statusDamage_ge_zero (condition : StatusCondition) : 0 ≤ statusDamage condition := by
  cases condition <;> simp [statusDamage]

theorem statusDamage_eq_zero_iff (condition : StatusCondition) :
    statusDamage condition = 0 ↔
      condition = .asleep ∨ condition = .confused ∨ condition = .paralyzed := by
  cases condition <;> simp [statusDamage]

theorem statusDamage_pos_iff (condition : StatusCondition) :
    0 < statusDamage condition ↔ condition = .poisoned ∨ condition = .burned := by
  cases condition <;> simp [statusDamage]

def applyStatusEndTurn (pokemon : PokemonInPlay) : PokemonInPlay :=
  match pokemon.status with
  | none => pokemon
  | some condition =>
    let newDamage := Nat.min (pokemon.damage + statusDamage condition) pokemon.card.hp
    { pokemon with damage := newDamage }

theorem applyStatusEndTurn_damage_le_hp (pokemon : PokemonInPlay) (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (applyStatusEndTurn pokemon).damage ≤ pokemon.card.hp := by
  cases hStatus : pokemon.status with
  | none =>
    simpa [applyStatusEndTurn, hStatus] using hBound
  | some condition =>
    simp [applyStatusEndTurn, hStatus, Nat.min_le_right]

theorem applyStatusEndTurn_status (pokemon : PokemonInPlay) :
    (applyStatusEndTurn pokemon).status = pokemon.status := by
  cases hStatus : pokemon.status with
  | none =>
    simp [applyStatusEndTurn, hStatus]
  | some condition =>
    simp [applyStatusEndTurn, hStatus]

theorem applyStatusEndTurn_none_damage (pokemon : PokemonInPlay) (hStatus : pokemon.status = none) :
    (applyStatusEndTurn pokemon).damage = pokemon.damage := by
  simp [applyStatusEndTurn, hStatus]

theorem applyStatusEndTurn_none (pokemon : PokemonInPlay) (hStatus : pokemon.status = none) :
    applyStatusEndTurn pokemon = pokemon := by
  simp [applyStatusEndTurn, hStatus]

theorem applyStatusEndTurn_damage_ge (pokemon : PokemonInPlay) (hBound : pokemon.damage ≤ pokemon.card.hp) :
    pokemon.damage ≤ (applyStatusEndTurn pokemon).damage := by
  cases hStatus : pokemon.status with
  | none =>
    simp [applyStatusEndTurn, hStatus]
  | some condition =>
    simp [applyStatusEndTurn, hStatus]
    have h1 : pokemon.damage ≤ pokemon.damage + statusDamage condition := Nat.le_add_right _ _
    exact (Nat.le_min).2 ⟨h1, hBound⟩

theorem applyStatusEndTurn_zero_damage (pokemon : PokemonInPlay) (condition : StatusCondition)
    (hStatus : pokemon.status = some condition) (hZero : statusDamage condition = 0)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (applyStatusEndTurn pokemon).damage = pokemon.damage := by
  simp [applyStatusEndTurn, hStatus, hZero, Nat.min_eq_left hBound]

theorem applyStatusEndTurn_asleep_damage (pokemon : PokemonInPlay)
    (hStatus : pokemon.status = some .asleep) (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (applyStatusEndTurn pokemon).damage = pokemon.damage := by
  exact applyStatusEndTurn_zero_damage pokemon .asleep hStatus (by simp) hBound

theorem applyStatusEndTurn_confused_damage (pokemon : PokemonInPlay)
    (hStatus : pokemon.status = some .confused) (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (applyStatusEndTurn pokemon).damage = pokemon.damage := by
  exact applyStatusEndTurn_zero_damage pokemon .confused hStatus (by simp) hBound

theorem applyStatusEndTurn_paralyzed_damage (pokemon : PokemonInPlay)
    (hStatus : pokemon.status = some .paralyzed) (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (applyStatusEndTurn pokemon).damage = pokemon.damage := by
  exact applyStatusEndTurn_zero_damage pokemon .paralyzed hStatus (by simp) hBound

theorem applyStatusEndTurn_poisoned_damage (pokemon : PokemonInPlay)
    (hStatus : pokemon.status = some .poisoned) :
    (applyStatusEndTurn pokemon).damage = Nat.min (pokemon.damage + 10) pokemon.card.hp := by
  simp [applyStatusEndTurn, hStatus]

theorem applyStatusEndTurn_burned_damage (pokemon : PokemonInPlay)
    (hStatus : pokemon.status = some .burned) :
    (applyStatusEndTurn pokemon).damage = Nat.min (pokemon.damage + 20) pokemon.card.hp := by
  simp [applyStatusEndTurn, hStatus]


theorem applyStatusEndTurn_damage_eq (pokemon : PokemonInPlay) :
    (applyStatusEndTurn pokemon).damage =
      match pokemon.status with
      | none => pokemon.damage
      | some condition => Nat.min (pokemon.damage + statusDamage condition) pokemon.card.hp := by
  cases hStatus : pokemon.status with
  | none =>
    simp [applyStatusEndTurn, hStatus]
  | some condition =>
    simp [applyStatusEndTurn, hStatus]

theorem applyStatusEndTurn_damage_le_add (pokemon : PokemonInPlay) :
    (applyStatusEndTurn pokemon).damage ≤
      match pokemon.status with
      | none => pokemon.damage
      | some condition => pokemon.damage + statusDamage condition := by
  cases hStatus : pokemon.status with
  | none =>
    simp [applyStatusEndTurn, hStatus]
  | some condition =>
    simp [applyStatusEndTurn, hStatus, Nat.min_le_left]

theorem applyStatusEndTurn_damage_eq_of_some (pokemon : PokemonInPlay) (condition : StatusCondition)
    (hStatus : pokemon.status = some condition) :
    (applyStatusEndTurn pokemon).damage = Nat.min (pokemon.damage + statusDamage condition) pokemon.card.hp := by
  simp [applyStatusEndTurn, hStatus]

theorem applyStatusEndTurn_damage_eq_damage_or_add_or_hp (pokemon : PokemonInPlay)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (applyStatusEndTurn pokemon).damage = pokemon.damage ∨
      (applyStatusEndTurn pokemon).damage = pokemon.damage + 10 ∨
      (applyStatusEndTurn pokemon).damage = pokemon.damage + 20 ∨
      (applyStatusEndTurn pokemon).damage = pokemon.card.hp := by
  cases hStatus : pokemon.status with
  | none =>
    left
    simp [applyStatusEndTurn, hStatus]
  | some condition =>
    cases condition with
    | asleep =>
      left
      simp [applyStatusEndTurn, hStatus, statusDamage, Nat.min_eq_left hBound]
    | confused =>
      left
      simp [applyStatusEndTurn, hStatus, statusDamage, Nat.min_eq_left hBound]
    | paralyzed =>
      left
      simp [applyStatusEndTurn, hStatus, statusDamage, Nat.min_eq_left hBound]
    | poisoned =>
      by_cases h : pokemon.damage + 10 ≤ pokemon.card.hp
      · right
        left
        simp [applyStatusEndTurn, hStatus, statusDamage, Nat.min_eq_left h]
      · right
        right
        right
        have h' : pokemon.card.hp ≤ pokemon.damage + 10 := by
          exact Nat.le_of_lt (Nat.not_le.mp h)
        simp [applyStatusEndTurn, hStatus, statusDamage, Nat.min_eq_right h']
    | burned =>
      by_cases h : pokemon.damage + 20 ≤ pokemon.card.hp
      · right
        right
        left
        simp [applyStatusEndTurn, hStatus, statusDamage, Nat.min_eq_left h]
      · right
        right
        right
        have h' : pokemon.card.hp ≤ pokemon.damage + 20 := by
          exact Nat.le_of_lt (Nat.not_le.mp h)
        simp [applyStatusEndTurn, hStatus, statusDamage, Nat.min_eq_right h']
theorem applyStatusEndTurn_energy (pokemon : PokemonInPlay) :
    (applyStatusEndTurn pokemon).energy = pokemon.energy := by
  cases hStatus : pokemon.status with
  | none =>
    simp [applyStatusEndTurn, hStatus]
  | some condition =>
    simp [applyStatusEndTurn, hStatus]

def canAttack (pokemon : PokemonInPlay) : Bool :=
  match pokemon.status with
  | some .paralyzed => false
  | some .asleep => false
  | _ => true

theorem canAttack_none (pokemon : PokemonInPlay) (hStatus : pokemon.status = none) :
    canAttack pokemon = true := by
  simp [canAttack, hStatus]

theorem canAttack_paralyzed (pokemon : PokemonInPlay) (hStatus : pokemon.status = some .paralyzed) :
    canAttack pokemon = false := by
  simp [canAttack, hStatus]

theorem canAttack_asleep (pokemon : PokemonInPlay) (hStatus : pokemon.status = some .asleep) :
    canAttack pokemon = false := by
  simp [canAttack, hStatus]

theorem canAttack_confused (pokemon : PokemonInPlay) (hStatus : pokemon.status = some .confused) :
    canAttack pokemon = true := by
  simp [canAttack, hStatus]

theorem canAttack_burned (pokemon : PokemonInPlay) (hStatus : pokemon.status = some .burned) :
    canAttack pokemon = true := by
  simp [canAttack, hStatus]

theorem canAttack_poisoned (pokemon : PokemonInPlay) (hStatus : pokemon.status = some .poisoned) :
    canAttack pokemon = true := by
  simp [canAttack, hStatus]

theorem canAttack_applyStatusEndTurn (pokemon : PokemonInPlay) :
    canAttack (applyStatusEndTurn pokemon) = canAttack pokemon := by
  cases hStatus : pokemon.status with
  | none =>
    simp [applyStatusEndTurn, canAttack, hStatus]
  | some condition =>
    simp [applyStatusEndTurn, canAttack, hStatus]

theorem canAttack_false_iff (pokemon : PokemonInPlay) :
    canAttack pokemon = false ↔
      pokemon.status = some .paralyzed ∨ pokemon.status = some .asleep := by
  cases hStatus : pokemon.status with
  | none =>
    simp [canAttack, hStatus]
  | some condition =>
    cases condition <;> simp [canAttack, hStatus]

theorem canAttack_true_iff (pokemon : PokemonInPlay) :
    canAttack pokemon = true ↔
      pokemon.status = none ∨ pokemon.status = some .confused ∨
        pokemon.status = some .burned ∨ pokemon.status = some .poisoned := by
  cases hStatus : pokemon.status with
  | none =>
    simp [canAttack, hStatus]
  | some condition =>
    cases condition <;> simp [canAttack, hStatus]

-- ============================================================================
-- ENTRY HAZARDS (SIMPLIFIED)
-- ============================================================================

def applyStealthRock (pokemon : PokemonInPlay) : PokemonInPlay :=
  { pokemon with damage := Nat.min (pokemon.damage + pokemon.card.hp / 8) pokemon.card.hp }

theorem applyStealthRock_status (pokemon : PokemonInPlay) :
    (applyStealthRock pokemon).status = pokemon.status := by
  simp [applyStealthRock]

theorem applyStealthRock_energy (pokemon : PokemonInPlay) :
    (applyStealthRock pokemon).energy = pokemon.energy := by
  simp [applyStealthRock]

theorem applyStealthRock_card (pokemon : PokemonInPlay) :
    (applyStealthRock pokemon).card = pokemon.card := by
  simp [applyStealthRock]

theorem applyStealthRock_damage_le_hp (pokemon : PokemonInPlay) :
    (applyStealthRock pokemon).damage ≤ pokemon.card.hp := by
  simp [applyStealthRock, Nat.min_le_right]

theorem applyStealthRock_damage_ge (pokemon : PokemonInPlay)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    pokemon.damage ≤ (applyStealthRock pokemon).damage := by
  simp [applyStealthRock]
  exact (Nat.le_min).2 ⟨Nat.le_add_right _ _, hBound⟩


theorem applyStealthRock_damage_eq (pokemon : PokemonInPlay) :
    (applyStealthRock pokemon).damage =
      Nat.min (pokemon.damage + pokemon.card.hp / 8) pokemon.card.hp := by
  simp [applyStealthRock]

theorem applyStealthRock_damage_eq_add (pokemon : PokemonInPlay)
    (hBound : pokemon.damage + pokemon.card.hp / 8 ≤ pokemon.card.hp) :
    (applyStealthRock pokemon).damage = pokemon.damage + pokemon.card.hp / 8 := by
  simp [applyStealthRock, Nat.min_eq_left hBound]

theorem applyStealthRock_damage_eq_hp (pokemon : PokemonInPlay)
    (hBound : pokemon.card.hp ≤ pokemon.damage + pokemon.card.hp / 8) :
    (applyStealthRock pokemon).damage = pokemon.card.hp := by
  simp [applyStealthRock, Nat.min_eq_right hBound]

theorem applyStealthRock_no_damage_of_zero_hp (pokemon : PokemonInPlay)
    (hZero : pokemon.card.hp = 0) (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (applyStealthRock pokemon).damage = pokemon.damage := by
  have hDiv : pokemon.card.hp / 8 = 0 := by simp [hZero]
  simp [applyStealthRock, hDiv, Nat.min_eq_left hBound]
theorem applyStealthRock_zero (pokemon : PokemonInPlay)
    (hZero : pokemon.card.hp < 8) (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (applyStealthRock pokemon).damage = pokemon.damage := by
  have hDiv : pokemon.card.hp / 8 = 0 := Nat.div_eq_of_lt hZero
  simp [applyStealthRock, hDiv, Nat.min_eq_left hBound]

def listGet? {α : Type} (xs : List α) (index : Nat) : Option α :=
  match xs, index with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ index => listGet? xs index

def toPokemonInPlay (card : Card) : PokemonInPlay :=
  { card := card, damage := 0, status := none, energy := [] }

def applyDamage (pokemon : PokemonInPlay) (amount : Nat) : PokemonInPlay :=
  { pokemon with damage := Nat.min (pokemon.damage + amount) pokemon.card.hp }

theorem applyDamage_status (pokemon : PokemonInPlay) (amount : Nat) :
    (applyDamage pokemon amount).status = pokemon.status := by
  simp [applyDamage]

theorem applyDamage_energy (pokemon : PokemonInPlay) (amount : Nat) :
    (applyDamage pokemon amount).energy = pokemon.energy := by
  simp [applyDamage]

theorem applyDamage_card (pokemon : PokemonInPlay) (amount : Nat) :
    (applyDamage pokemon amount).card = pokemon.card := by
  simp [applyDamage]

theorem applyDamage_damage_le_hp (pokemon : PokemonInPlay) (amount : Nat) :
    (applyDamage pokemon amount).damage ≤ pokemon.card.hp := by
  simp [applyDamage, Nat.min_le_right]

theorem applyDamage_damage_ge (pokemon : PokemonInPlay) (amount : Nat)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    pokemon.damage ≤ (applyDamage pokemon amount).damage := by
  simp [applyDamage]
  exact (Nat.le_min).2 ⟨Nat.le_add_right _ _, hBound⟩

theorem applyDamage_damage_eq_add (pokemon : PokemonInPlay) (amount : Nat)
    (hBound : pokemon.damage + amount ≤ pokemon.card.hp) :
    (applyDamage pokemon amount).damage = pokemon.damage + amount := by
  simp [applyDamage, Nat.min_eq_left hBound]

theorem applyDamage_damage_eq_hp (pokemon : PokemonInPlay) (amount : Nat)
    (hBound : pokemon.card.hp ≤ pokemon.damage + amount) :
    (applyDamage pokemon amount).damage = pokemon.card.hp := by
  simp [applyDamage, Nat.min_eq_right hBound]

theorem applyDamage_damage_eq_add_or_hp (pokemon : PokemonInPlay) (amount : Nat) :
    (applyDamage pokemon amount).damage = pokemon.damage + amount ∨
      (applyDamage pokemon amount).damage = pokemon.card.hp := by
  by_cases h : pokemon.damage + amount ≤ pokemon.card.hp
  · left
    simp [applyDamage, Nat.min_eq_left h]
  · right
    have h' : pokemon.card.hp ≤ pokemon.damage + amount := by
      exact Nat.le_of_lt (Nat.not_le.mp h)
    simp [applyDamage, Nat.min_eq_right h']

theorem applyDamage_zero (pokemon : PokemonInPlay) (hBound : pokemon.damage ≤ pokemon.card.hp) :
    applyDamage pokemon 0 = pokemon := by
  cases pokemon
  simp [applyDamage, Nat.min_eq_left hBound]

def attackEffectBonus : AttackEffect → Nat
  | .addDamage amount => amount
  | _ => 0

def attackBonus (effects : List AttackEffect) : Nat :=
  effects.foldl (fun acc effect => acc + attackEffectBonus effect) 0

theorem attackBonus_foldl_acc (effects : List AttackEffect) (acc : Nat) :
    effects.foldl (fun acc effect => acc + attackEffectBonus effect) acc =
      acc + attackBonus effects := by
  induction effects generalizing acc with
  | nil =>
    simp [attackBonus]
  | cons effect rest ih =>
    have h1 := ih (acc := acc + attackEffectBonus effect)
    have h2 := ih (acc := attackEffectBonus effect)
    have hcons :
        attackBonus (effect :: rest) = attackEffectBonus effect + attackBonus rest := by
      calc
        attackBonus (effect :: rest) =
            List.foldl (fun acc effect => acc + attackEffectBonus effect)
              (attackEffectBonus effect) rest := by
                simp [attackBonus, List.foldl]
        _ = attackEffectBonus effect + attackBonus rest := h2
    calc
      List.foldl (fun acc effect => acc + attackEffectBonus effect) acc (effect :: rest) =
          List.foldl (fun acc effect => acc + attackEffectBonus effect)
            (acc + attackEffectBonus effect) rest := by
              simp [List.foldl]
      _ = (acc + attackEffectBonus effect) + attackBonus rest := h1
      _ = acc + (attackEffectBonus effect + attackBonus rest) := by
              simp [Nat.add_assoc]
      _ = acc + attackBonus (effect :: rest) := by
              simp [hcons]

theorem attackBonus_cons (effect : AttackEffect) (effects : List AttackEffect) :
    attackBonus (effect :: effects) = attackEffectBonus effect + attackBonus effects := by
  simpa [attackBonus, List.foldl] using (attackBonus_foldl_acc (effects := effects)
    (acc := attackEffectBonus effect))

theorem attackBonus_nil : attackBonus [] = 0 := by
  rfl

theorem attackBonus_cons_add (effects : List AttackEffect) (amount : Nat) :
    attackBonus (.addDamage amount :: effects) = amount + attackBonus effects := by
  simpa [attackEffectBonus] using (attackBonus_cons (.addDamage amount) effects)

theorem attackBonus_cons_other (effect : AttackEffect) (effects : List AttackEffect)
    (h : (match effect with | .addDamage _ => False | _ => True)) :
    attackBonus (effect :: effects) = attackBonus effects := by
  cases effect with
  | addDamage amount =>
    cases h
  | applyStatus condition =>
    simp [attackBonus_cons, attackEffectBonus]
  | heal amount =>
    simp [attackBonus_cons, attackEffectBonus]
  | drawCards count =>
    simp [attackBonus_cons, attackEffectBonus]

theorem attackBonus_ge (effects : List AttackEffect) :
    0 ≤ attackBonus effects := by
  simp [attackBonus]

theorem attackBonus_append (effects1 effects2 : List AttackEffect) :
    attackBonus (effects1 ++ effects2) = attackBonus effects1 + attackBonus effects2 := by
  induction effects1 with
  | nil =>
    simp [attackBonus]
  | cons effect rest ih =>
    calc
      attackBonus ((effect :: rest) ++ effects2) =
          attackBonus (effect :: (rest ++ effects2)) := by simp
      _ = attackEffectBonus effect + attackBonus (rest ++ effects2) := by
          simpa using (attackBonus_cons effect (rest ++ effects2))
      _ = attackEffectBonus effect + (attackBonus rest + attackBonus effects2) := by
          simp [ih]
      _ = (attackEffectBonus effect + attackBonus rest) + attackBonus effects2 := by
          simp [Nat.add_assoc]
      _ = attackBonus (effect :: rest) + attackBonus effects2 := by
          simp [attackBonus_cons]

def applyAttackEffects (pokemon : PokemonInPlay) (effects : List AttackEffect) : PokemonInPlay :=
  effects.foldl
    (fun acc effect =>
      match effect with
      | .applyStatus condition => { acc with status := some condition }
      | .heal amount => { acc with damage := Nat.sub acc.damage amount }
      | .drawCards _ => acc
      | .addDamage _ => acc)
    pokemon

theorem applyAttackEffects_nil (pokemon : PokemonInPlay) :
    applyAttackEffects pokemon [] = pokemon := by
  simp [applyAttackEffects]

theorem applyAttackEffects_energy (pokemon : PokemonInPlay) (effects : List AttackEffect) :
    (applyAttackEffects pokemon effects).energy = pokemon.energy := by
  induction effects generalizing pokemon with
  | nil =>
    simp [applyAttackEffects]
  | cons effect rest ih =>
    cases effect with
    | applyStatus condition =>
      simpa [applyAttackEffects] using (ih (pokemon := { pokemon with status := some condition }))
    | heal amount =>
      simpa [applyAttackEffects] using (ih (pokemon := { pokemon with damage := Nat.sub pokemon.damage amount }))
    | drawCards count =>
      simpa [applyAttackEffects] using (ih (pokemon := pokemon))
    | addDamage amount =>
      simpa [applyAttackEffects] using (ih (pokemon := pokemon))

theorem applyAttackEffects_card (pokemon : PokemonInPlay) (effects : List AttackEffect) :
    (applyAttackEffects pokemon effects).card = pokemon.card := by
  induction effects generalizing pokemon with
  | nil =>
    simp [applyAttackEffects]
  | cons effect rest ih =>
    cases effect with
    | applyStatus condition =>
      simpa [applyAttackEffects] using (ih (pokemon := { pokemon with status := some condition }))
    | heal amount =>
      simpa [applyAttackEffects] using (ih (pokemon := { pokemon with damage := Nat.sub pokemon.damage amount }))
    | drawCards count =>
      simpa [applyAttackEffects] using (ih (pokemon := pokemon))
    | addDamage amount =>
      simpa [applyAttackEffects] using (ih (pokemon := pokemon))

theorem applyAttackEffects_single_status (pokemon : PokemonInPlay) (condition : StatusCondition) :
    (applyAttackEffects pokemon [.applyStatus condition]).status = some condition := by
  simp [applyAttackEffects]

theorem applyAttackEffects_single_heal (pokemon : PokemonInPlay) (amount : Nat) :
    (applyAttackEffects pokemon [.heal amount]).damage = Nat.sub pokemon.damage amount := by
  simp [applyAttackEffects]

theorem applyAttackEffects_single_heal_status (pokemon : PokemonInPlay) (amount : Nat) :
    (applyAttackEffects pokemon [.heal amount]).status = pokemon.status := by
  simp [applyAttackEffects]

theorem applyAttackEffects_single_draw (pokemon : PokemonInPlay) (count : Nat) :
    applyAttackEffects pokemon [.drawCards count] = pokemon := by
  simp [applyAttackEffects]

theorem applyAttackEffects_single_draw_status (pokemon : PokemonInPlay) (count : Nat) :
    (applyAttackEffects pokemon [.drawCards count]).status = pokemon.status := by
  simp [applyAttackEffects]

theorem applyAttackEffects_single_addDamage (pokemon : PokemonInPlay) (amount : Nat) :
    applyAttackEffects pokemon [.addDamage amount] = pokemon := by
  simp [applyAttackEffects]

theorem applyAttackEffects_single_addDamage_status (pokemon : PokemonInPlay) (amount : Nat) :
    (applyAttackEffects pokemon [.addDamage amount]).status = pokemon.status := by
  simp [applyAttackEffects]

theorem applyAttackEffects_damage_le (pokemon : PokemonInPlay) (effects : List AttackEffect) :
    (applyAttackEffects pokemon effects).damage ≤ pokemon.damage := by
  induction effects generalizing pokemon with
  | nil =>
    simp [applyAttackEffects]
  | cons effect rest ih =>
    cases effect with
    | applyStatus condition =>
      simpa [applyAttackEffects] using (ih (pokemon := { pokemon with status := some condition }))
    | heal amount =>
      have h := ih (pokemon := { pokemon with damage := Nat.sub pokemon.damage amount })
      exact Nat.le_trans h (Nat.sub_le _ _)
    | drawCards count =>
      simpa [applyAttackEffects] using (ih (pokemon := pokemon))
    | addDamage amount =>
      simpa [applyAttackEffects] using (ih (pokemon := pokemon))

theorem applyAttackEffects_append (pokemon : PokemonInPlay) (effects1 effects2 : List AttackEffect) :
    applyAttackEffects pokemon (effects1 ++ effects2) =
      applyAttackEffects (applyAttackEffects pokemon effects1) effects2 := by
  simp [applyAttackEffects, List.foldl_append]

theorem applyAttackEffects_damage_le_hp (pokemon : PokemonInPlay) (effects : List AttackEffect)
    (hBound : pokemon.damage ≤ pokemon.card.hp) :
    (applyAttackEffects pokemon effects).damage ≤ pokemon.card.hp := by
  exact Nat.le_trans (applyAttackEffects_damage_le pokemon effects) hBound

def takePrize (attacker defender : PlayerState) : PlayerState × PlayerState :=
  match defender.prizes with
  | [] => (attacker, defender)
  | prize :: rest =>
    ({ attacker with hand := prize :: attacker.hand }, { defender with prizes := rest })

theorem takePrize_prizes_length_le (attacker defender : PlayerState) :
    defender.prizes.length ≤ (takePrize attacker defender).2.prizes.length + 1 := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

theorem takePrize_prizes_length_eq (attacker defender : PlayerState) :
    defender.prizes.length = (takePrize attacker defender).2.prizes.length +
      (if defender.prizes.isEmpty then 0 else 1) := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

theorem takePrize_prizes_length_succ (attacker defender : PlayerState)
    (hNonempty : defender.prizes ≠ []) :
    (takePrize attacker defender).2.prizes.length + 1 = defender.prizes.length := by
  cases h : defender.prizes with
  | nil =>
    cases hNonempty h
  | cons prize rest =>
    simp [takePrize, h]

theorem takePrize_hand_length_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).1.hand.length = attacker.hand.length +
      (if defender.prizes.isEmpty then 0 else 1) := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

theorem takePrize_hand_length_succ (attacker defender : PlayerState)
    (hNonempty : defender.prizes ≠ []) :
    (takePrize attacker defender).1.hand.length = attacker.hand.length + 1 := by
  cases h : defender.prizes with
  | nil =>
    cases hNonempty h
  | cons prize rest =>
    simp [takePrize, h]

theorem takePrize_attacker_prizes_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).1.prizes = attacker.prizes := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

theorem takePrize_attacker_prizes_length_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).1.prizes.length = attacker.prizes.length := by
  simp [takePrize_attacker_prizes_eq]

@[simp] theorem takePrize_attacker_bench_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).1.bench = attacker.bench := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

@[simp] theorem takePrize_defender_bench_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).2.bench = defender.bench := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

@[simp] theorem takePrize_attacker_deck_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).1.deck = attacker.deck := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

@[simp] theorem takePrize_defender_deck_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).2.deck = defender.deck := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

@[simp] theorem takePrize_attacker_active_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).1.active = attacker.active := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

@[simp] theorem takePrize_defender_active_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).2.active = defender.active := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

@[simp] theorem takePrize_attacker_discard_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).1.discard = attacker.discard := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

@[simp] theorem takePrize_defender_discard_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).2.discard = defender.discard := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

@[simp] theorem takePrize_defender_hand_eq (attacker defender : PlayerState) :
    (takePrize attacker defender).2.hand = defender.hand := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h]
  | cons prize rest => simp [takePrize, h]

def applyWeakness (damage : Nat) (attackerType : EnergyType) (weakness : Option Weakness) : Nat :=
  match weakness with
  | some w => if w.energyType == attackerType then damage * w.multiplier else damage
  | none => damage

def applyResistance (damage : Nat) (attackerType : EnergyType) (resistance : Option Resistance) : Nat :=
  match resistance with
  | some r => if r.energyType == attackerType then Nat.sub damage r.amount else damage
  | none => damage

@[simp] theorem applyWeakness_none (damage : Nat) (attackerType : EnergyType) :
    applyWeakness damage attackerType none = damage := by
  simp [applyWeakness]

theorem applyWeakness_beq_true (damage : Nat) (attackerType : EnergyType) (w : Weakness)
    (h : (w.energyType == attackerType) = true) :
    applyWeakness damage attackerType (some w) = damage * w.multiplier := by
  simp [applyWeakness, h]

theorem applyWeakness_beq_false (damage : Nat) (attackerType : EnergyType) (w : Weakness)
    (h : (w.energyType == attackerType) = false) :
    applyWeakness damage attackerType (some w) = damage := by
  simp [applyWeakness, h]

@[simp] theorem applyResistance_none (damage : Nat) (attackerType : EnergyType) :
    applyResistance damage attackerType none = damage := by
  simp [applyResistance]

theorem applyResistance_beq_true (damage : Nat) (attackerType : EnergyType) (r : Resistance)
    (h : (r.energyType == attackerType) = true) :
    applyResistance damage attackerType (some r) = Nat.sub damage r.amount := by
  simp [applyResistance, h]

theorem applyResistance_beq_false (damage : Nat) (attackerType : EnergyType) (r : Resistance)
    (h : (r.energyType == attackerType) = false) :
    applyResistance damage attackerType (some r) = damage := by
  simp [applyResistance, h]

@[simp] theorem applyWeakness_zero (attackerType : EnergyType) (weakness : Option Weakness) :
    applyWeakness 0 attackerType weakness = 0 := by
  cases weakness <;> simp [applyWeakness]

@[simp] theorem applyResistance_zero (attackerType : EnergyType) (resistance : Option Resistance) :
    applyResistance 0 attackerType resistance = 0 := by
  cases resistance <;> simp [applyResistance]

theorem applyWeakness_mono (damage damage' : Nat) (attackerType : EnergyType) (weakness : Option Weakness)
    (h : damage ≤ damage') :
    applyWeakness damage attackerType weakness ≤ applyWeakness damage' attackerType weakness := by
  cases weakness with
  | none =>
    simpa [applyWeakness] using h
  | some w =>
    by_cases hEq : w.energyType == attackerType
    · simp [applyWeakness, hEq]
      exact Nat.mul_le_mul_right w.multiplier h
    · simp [applyWeakness, hEq, h]

theorem applyResistance_mono (damage damage' : Nat) (attackerType : EnergyType) (resistance : Option Resistance)
    (h : damage ≤ damage') :
    applyResistance damage attackerType resistance ≤ applyResistance damage' attackerType resistance := by
  cases resistance with
  | none =>
    simpa [applyResistance] using h
  | some r =>
    by_cases hEq : r.energyType == attackerType
    · have h' : damage - r.amount ≤ damage' - r.amount := Nat.sub_le_sub_right h r.amount
      simpa [applyResistance, hEq] using h'
    · simpa [applyResistance, hEq] using h

def calculateDamage (attack : Attack) (attackerType : EnergyType) (defender : Card) : Nat :=
  let base := attack.baseDamage + attackBonus attack.effects
  let afterWeakness := applyWeakness base attackerType defender.weakness
  let afterResistance := applyResistance afterWeakness attackerType defender.resistance
  afterResistance

theorem calculateDamage_weakness_none (attack : Attack) (attackerType : EnergyType) (defender : Card)
    (hWeak : defender.weakness = none) :
    calculateDamage attack attackerType defender =
      applyResistance (attack.baseDamage + attackBonus attack.effects) attackerType defender.resistance := by
  simp [calculateDamage, hWeak]

theorem calculateDamage_resistance_none (attack : Attack) (attackerType : EnergyType) (defender : Card)
    (hRes : defender.resistance = none) :
    calculateDamage attack attackerType defender =
      applyWeakness (attack.baseDamage + attackBonus attack.effects) attackerType defender.weakness := by
  simp [calculateDamage, hRes]

theorem calculateDamage_no_mods (attack : Attack) (attackerType : EnergyType) (defender : Card)
    (hWeak : defender.weakness = none) (hRes : defender.resistance = none) :
    calculateDamage attack attackerType defender = attack.baseDamage + attackBonus attack.effects := by
  simp [calculateDamage, hWeak, hRes]

theorem calculateDamage_base_no_effects (attack : Attack) (attackerType : EnergyType) (defender : Card)
    (hEff : attack.effects = []) (hWeak : defender.weakness = none) (hRes : defender.resistance = none) :
    calculateDamage attack attackerType defender = attack.baseDamage := by
  simp [calculateDamage, hEff, hWeak, hRes, attackBonus_nil]

theorem calculateDamage_weakness_match (attack : Attack) (attackerType : EnergyType) (defender : Card)
    (w : Weakness) (hWeak : defender.weakness = some w)
    (hType : (w.energyType == attackerType) = true)
    (hRes : defender.resistance = none) :
    calculateDamage attack attackerType defender =
      (attack.baseDamage + attackBonus attack.effects) * w.multiplier := by
  simp [calculateDamage, hWeak, hRes, applyWeakness, hType]

theorem calculateDamage_resistance_match (attack : Attack) (attackerType : EnergyType) (defender : Card)
    (r : Resistance) (hRes : defender.resistance = some r)
    (hType : (r.energyType == attackerType) = true)
    (hWeak : defender.weakness = none) :
    calculateDamage attack attackerType defender =
      Nat.sub (attack.baseDamage + attackBonus attack.effects) r.amount := by
  simp [calculateDamage, hWeak, hRes, applyResistance, hType]

theorem calculateDamage_weakness_resistance_match (attack : Attack) (attackerType : EnergyType)
    (defender : Card) (w : Weakness) (r : Resistance)
    (hWeak : defender.weakness = some w) (hRes : defender.resistance = some r)
    (hWeakType : (w.energyType == attackerType) = true)
    (hResType : (r.energyType == attackerType) = true) :
    calculateDamage attack attackerType defender =
      Nat.sub ((attack.baseDamage + attackBonus attack.effects) * w.multiplier) r.amount := by
  simp [calculateDamage, hWeak, hRes, applyWeakness, applyResistance, hWeakType, hResType]

def hasEnergyCost (attack : Attack) (energy : List EnergyType) : Bool :=
  energyCostSatisfied attack.energyCost energy

theorem hasEnergyCost_iff_consume (attack : Attack) (energy : List EnergyType) :
    hasEnergyCost attack energy = true ↔
      ∃ remaining, consumeEnergyCost attack.energyCost energy = some remaining := by
  simpa [hasEnergyCost] using energyCostSatisfied_iff_consume attack.energyCost energy

def applyAction (state : GameState) (action : Action) : Option GameState :=
  match action with
  | .endTurn =>
    some { state with activePlayer := otherPlayer state.activePlayer }
  | .playCard card =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match removeFirst card playerState.hand with
    | none => none
    | some newHand =>
      let pokemon := toPokemonInPlay card
      let updatedPlayerState :=
        match playerState.active with
        | none => { playerState with hand := newHand, active := some pokemon }
        | some _ => { playerState with hand := newHand, bench := playerState.bench ++ [pokemon] }
      some (setPlayerState state player updatedPlayerState)
  | .attachEnergy energyType =>
    let player := state.activePlayer
    let playerState := getPlayerState state player
    match playerState.active with
    | none => none
    | some active =>
      let updatedActive := { active with energy := energyType :: active.energy }
      let updatedPlayerState := { playerState with active := some updatedActive }
      some (setPlayerState state player updatedPlayerState)
  | .attack attackIndex =>
    let attackerPlayer := state.activePlayer
    let defenderPlayer := otherPlayer attackerPlayer
    let attackerState := getPlayerState state attackerPlayer
    let defenderState := getPlayerState state defenderPlayer
    match attackerState.active, defenderState.active with
    | some attacker, some defender =>
      match listGet? attacker.card.attacks attackIndex with
      | none => none
      | some attack =>
        if hasEnergyCost attack attacker.energy then
          let damage := calculateDamage attack attacker.card.energyType defender.card
          let damagedDefender := applyDamage defender damage
          let effectedDefender := applyAttackEffects damagedDefender attack.effects
          if effectedDefender.damage >= effectedDefender.card.hp then
            let (updatedAttacker, updatedDefender) := takePrize attackerState defenderState
            let newDefenderState :=
              { updatedDefender with active := none, discard := defender.card :: updatedDefender.discard }
            let newState := setPlayerState state attackerPlayer updatedAttacker
            let finalState := setPlayerState newState defenderPlayer newDefenderState
            some { finalState with activePlayer := otherPlayer state.activePlayer }
          else
            let newDefenderState := { defenderState with active := some effectedDefender }
            let newState := setPlayerState state defenderPlayer newDefenderState
            some { newState with activePlayer := otherPlayer state.activePlayer }
        else
          none
    | _, _ => none

-- ============================================================================
-- PHASE 3: FORMAL VERIFICATION & META-SAFETY
-- ============================================================================

-- Count cards in a PokemonInPlay (always 1 card per Pokemon)
def pokemonInPlayCardCount (_pokemon : PokemonInPlay) : Nat := 1

-- Count all cards in a player's zones
def playerCardCount (player : PlayerState) : Nat :=
  player.deck.length +
  player.hand.length +
  (player.bench.map pokemonInPlayCardCount).foldl (· + ·) 0 +
  (match player.active with | some _ => 1 | none => 0) +
  player.discard.length +
  player.prizes.length

@[simp] theorem active_card_count_some (x : PokemonInPlay) :
    (match (some x) with | some _ => 1 | none => 0) = 1 := rfl

@[simp] theorem active_card_count_none :
    (match (none : Option PokemonInPlay) with | some _ => 1 | none => 0) = 0 := rfl

theorem active_card_count_eq_one (opt : Option PokemonInPlay) (x : PokemonInPlay) (h : opt = some x) :
    (match opt with | some _ => 1 | none => 0) = 1 := by
  rw [h]

-- Total cards in game (both players)
def totalCardCount (state : GameState) : Nat :=
  playerCardCount state.playerOne + playerCardCount state.playerTwo

-- Standard deck size constant
def standardDeckSize : Nat := 60

-- A game state is valid if total cards equals 120 (60 per player)
def validCardCount (state : GameState) : Prop :=
  totalCardCount state = 2 * standardDeckSize

theorem takePrize_preserves_total_cards (attacker defender : PlayerState) :
    playerCardCount (takePrize attacker defender).1 +
      playerCardCount (takePrize attacker defender).2 =
      playerCardCount attacker + playerCardCount defender := by
  cases h : defender.prizes with
  | nil => simp [takePrize, h, playerCardCount]
  | cons prize rest =>
    simp [takePrize, h, playerCardCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

-- Win condition: opponent has no prizes left (took all 6)
def hasWon (state : GameState) (player : PlayerId) : Prop :=
  let opponent := otherPlayer player
  let opponentState := getPlayerState state opponent
  opponentState.prizes.length = 0

-- A standard starting state for a player
def standardStartingPlayer (deck : List Card) (hand : List Card) (prizes : List Card) : PlayerState :=
  { deck := deck
  , hand := hand
  , bench := []
  , active := none
  , discard := []
  , prizes := prizes }

-- ============================================================================
-- CONSERVATION OF CARDS THEOREM
-- ============================================================================

-- Helper: endTurn preserves card count
theorem endTurn_preserves_cards (state : GameState) :
    totalCardCount { state with activePlayer := otherPlayer state.activePlayer } = totalCardCount state := by
  rfl

-- Lemma: removeFirst reduces list length by 1
theorem removeFirst_length (card : Card) (xs : List Card) (ys : List Card)
    (h : removeFirst card xs = some ys) : ys.length + 1 = xs.length := by
  induction xs generalizing ys with
  | nil => simp [removeFirst] at h
  | cons x xs ih =>
    simp only [removeFirst] at h
    split at h
    · -- card == x, so ys = xs
      simp at h
      simp [← h]
    · -- card ≠ x, recursive case
      cases hRec : removeFirst card xs with
      | none => simp [hRec] at h
      | some rest =>
        simp [hRec] at h
        subst h
        simp [ih rest hRec]

-- Helper: foldl addition with init n equals n + foldl with init 0
theorem foldl_add_shift (xs : List Nat) (n : Nat) :
    xs.foldl (· + ·) n = n + xs.foldl (· + ·) 0 := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl, Nat.zero_add]
    rw [ih (n + x), ih x]
    exact Nat.add_assoc n x _

-- Helper: bench card count is just the length (since each pokemon counts as 1)
theorem bench_card_count (bench : List PokemonInPlay) :
    (bench.map pokemonInPlayCardCount).foldl (· + ·) 0 = bench.length := by
  induction bench with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map, pokemonInPlayCardCount, List.foldl, List.length_cons]
    rw [foldl_add_shift]
    omega

-- Helper: playing a card preserves total card count (card moves from hand to board)
theorem playCard_preserves_player_cards (playerState : PlayerState) (card : Card) (newHand : List Card)
    (h : removeFirst card playerState.hand = some newHand) :
    let pokemon := toPokemonInPlay card
    let newState := match playerState.active with
      | none => { playerState with hand := newHand, active := some pokemon }
      | some _ => { playerState with hand := newHand, bench := playerState.bench ++ [pokemon] }
    playerCardCount newState = playerCardCount playerState := by
  have hLen : newHand.length + 1 = playerState.hand.length := removeFirst_length card playerState.hand newHand h
  cases hActive : playerState.active with
  | none =>
    simp only [playerCardCount, hActive]
    rw [bench_card_count]
    omega
  | some _ =>
    simp only [playerCardCount, hActive]
    rw [bench_card_count, bench_card_count]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem applyAction_endTurn_preserves_total_cards (state : GameState) (finalState : GameState)
    (h : applyAction state .endTurn = some finalState) :
    totalCardCount finalState = totalCardCount state := by
  simp [applyAction] at h
  cases h
  simpa using (endTurn_preserves_cards state)

theorem applyAction_playCard_preserves_total_cards (state : GameState) (card : Card) (finalState : GameState)
    (h : applyAction state (.playCard card) = some finalState) :
    totalCardCount finalState = totalCardCount state := by
  cases hPlayer : state.activePlayer with
  | playerOne =>
    simp [applyAction, hPlayer, getPlayerState, setPlayerState] at h
    cases hRemove : removeFirst card state.playerOne.hand with
    | none =>
      simp [hRemove] at h
    | some newHand =>
      simp [hRemove] at h
      cases h
      have hCards :
          playerCardCount
              (match state.playerOne.active with
              | none => { state.playerOne with hand := newHand, active := some (toPokemonInPlay card) }
              | some _ => { state.playerOne with hand := newHand, bench := state.playerOne.bench ++ [toPokemonInPlay card] }) =
            playerCardCount state.playerOne := by
        simpa using (playCard_preserves_player_cards state.playerOne card newHand hRemove)
      simp [totalCardCount, hCards]
  | playerTwo =>
    simp [applyAction, hPlayer, getPlayerState, setPlayerState] at h
    cases hRemove : removeFirst card state.playerTwo.hand with
    | none =>
      simp [hRemove] at h
    | some newHand =>
      simp [hRemove] at h
      cases h
      have hCards :
          playerCardCount
              (match state.playerTwo.active with
              | none => { state.playerTwo with hand := newHand, active := some (toPokemonInPlay card) }
              | some _ => { state.playerTwo with hand := newHand, bench := state.playerTwo.bench ++ [toPokemonInPlay card] }) =
            playerCardCount state.playerTwo := by
        simpa using (playCard_preserves_player_cards state.playerTwo card newHand hRemove)
      simp [totalCardCount, hCards]

theorem turn_one_cards_preserved (state : GameState) (actions : List Action)
    (hActions : TurnOneActions actions) :
    ∀ finalState : GameState,
      (actions.foldlM applyAction state = some finalState) →
      totalCardCount finalState = totalCardCount state := by
  induction hActions generalizing state with
  | nil =>
    intro finalState hFold
    simp [List.foldlM] at hFold
    cases hFold
    rfl
  | play hRest ih =>
    rename_i card rest
    intro finalState hFold
    cases hAct : applyAction state (.playCard card) with
    | none =>
      simp [List.foldlM, hAct] at hFold
    | some state' =>
      have hFold' : rest.foldlM applyAction state' = some finalState := by
        simpa [List.foldlM, hAct] using hFold
      have hCardsRest := ih (state := state') (finalState := finalState) hFold'
      have hCardsPlay := applyAction_playCard_preserves_total_cards state card state' hAct
      exact hCardsRest.trans hCardsPlay
  | attach hRest ih =>
    rename_i energyType rest
    intro finalState hFold
    cases hAct : applyAction state (.attachEnergy energyType) with
    | none =>
      simp [List.foldlM, hAct] at hFold
    | some state' =>
      have hFold' : rest.foldlM applyAction state' = some finalState := by
        simpa [List.foldlM, hAct] using hFold
      have hCardsRest := ih (state := state') (finalState := finalState) hFold'
      cases hPlayer : state.activePlayer with
      | playerOne =>
        simp [applyAction, getPlayerState, setPlayerState, hPlayer] at hAct
        cases hActive : state.playerOne.active with
        | none =>
          simp [hActive] at hAct
        | some active =>
          simp [hActive] at hAct
          cases hAct
          simpa [totalCardCount, playerCardCount, getPlayerState, setPlayerState, hPlayer, hActive,
            bench_card_count] using hCardsRest
      | playerTwo =>
        simp [applyAction, getPlayerState, setPlayerState, hPlayer] at hAct
        cases hActive : state.playerTwo.active with
        | none =>
          simp [hActive] at hAct
        | some active =>
          simp [hActive] at hAct
          cases hAct
          simpa [totalCardCount, playerCardCount, getPlayerState, setPlayerState, hPlayer, hActive,
            bench_card_count] using hCardsRest
  | endTurn =>
    intro finalState hFold
    simp [List.foldlM] at hFold
    exact applyAction_endTurn_preserves_total_cards state finalState hFold

-- ============================================================================
-- T1 (TURN ONE) THEOREM SETUP
-- ============================================================================

-- Standard prize count
def standardPrizeCount : Nat := 6

-- A valid starting game state
structure ValidStartingState (state : GameState) : Prop where
  playerOnePrizes : state.playerOne.prizes.length = standardPrizeCount
  playerTwoPrizes : state.playerTwo.prizes.length = standardPrizeCount
  cardConservation : validCardCount state

theorem turn_one_prizes_preserved (state : GameState) (actions : List Action)
    (hActions : TurnOneActions actions) :
    ∀ finalState : GameState,
      (actions.foldlM applyAction state = some finalState) →
      (getPlayerState finalState .playerTwo).prizes.length =
        (getPlayerState state .playerTwo).prizes.length := by
  -- Turn 1 actions exclude attacks, so player two prizes are unchanged.
  induction hActions generalizing state with
  | nil =>
    intro finalState hFold
    simp [List.foldlM] at hFold
    cases hFold
    rfl
  | play hRest ih =>
    rename_i card rest
    intro finalState hFold
    cases hAct : applyAction state (.playCard card) with
    | none =>
      simp [List.foldlM, hAct] at hFold
    | some state' =>
      have hFold' : rest.foldlM applyAction state' = some finalState := by
        simpa [List.foldlM, hAct] using hFold
      have hEqRest :=
        ih (state := state') (finalState := finalState) hFold'
      have hEqPlay :
          (getPlayerState state' .playerTwo).prizes.length =
            (getPlayerState state .playerTwo).prizes.length := by
        cases hPlayer : state.activePlayer with
        | playerOne =>
          simp [applyAction, getPlayerState, setPlayerState, hPlayer] at hAct
          cases hRemove : removeFirst card state.playerOne.hand with
          | none =>
            simp [hRemove] at hAct
            | some newHand =>
              simp [hRemove] at hAct
              cases hAct
              simp [getPlayerState]
        | playerTwo =>
          simp [applyAction, getPlayerState, setPlayerState, hPlayer] at hAct
          cases hRemove : removeFirst card state.playerTwo.hand with
          | none =>
            simp [hRemove] at hAct
            | some newHand =>
              simp [hRemove] at hAct
              cases hAct
              cases hActive : state.playerTwo.active <;> simp [getPlayerState]
      exact hEqRest.trans hEqPlay
  | attach hRest ih =>
    rename_i energyType rest
    intro finalState hFold
    cases hAct : applyAction state (.attachEnergy energyType) with
    | none =>
      simp [List.foldlM, hAct] at hFold
    | some state' =>
      have hFold' : rest.foldlM applyAction state' = some finalState := by
        simpa [List.foldlM, hAct] using hFold
      have hEqRest := ih (state := state') (finalState := finalState) hFold'
      have hEqAttach :
          (getPlayerState state' .playerTwo).prizes.length =
            (getPlayerState state .playerTwo).prizes.length := by
        cases hPlayer : state.activePlayer with
        | playerOne =>
          simp [applyAction, getPlayerState, setPlayerState, hPlayer] at hAct
          cases hActive : state.playerOne.active with
          | none =>
            simp [hActive] at hAct
            | some active =>
              simp [hActive] at hAct
              cases hAct
              simp [getPlayerState]
        | playerTwo =>
          simp [applyAction, getPlayerState, setPlayerState, hPlayer] at hAct
          cases hActive : state.playerTwo.active with
          | none =>
            simp [hActive] at hAct
            | some active =>
              simp [hActive] at hAct
              cases hAct
              simp [getPlayerState]
      exact hEqRest.trans hEqAttach
  | endTurn =>
    intro finalState hFold
    simp [List.foldlM, applyAction] at hFold
    cases hFold
    rfl
theorem applyAction_attack_prizes_le (state : GameState) (attackIndex : Nat) (finalState : GameState)
    (hFirst : state.activePlayer = .playerOne)
    (h : applyAction state (.attack attackIndex) = some finalState) :
    state.playerTwo.prizes.length ≤ finalState.playerTwo.prizes.length + 1 := by
  cases hAtt : state.playerOne.active with
  | none =>
    simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt] at h
  | some attacker =>
    cases hDef : state.playerTwo.active with
    | none =>
      simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt, hDef] at h
    | some defender =>
      cases hAttack : listGet? attacker.card.attacks attackIndex with
      | none =>
        simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt, hDef, hAttack] at h
      | some attack =>
        by_cases hCost : hasEnergyCost attack attacker.energy
        · let damage := calculateDamage attack attacker.card.energyType defender.card
          let damagedDefender := applyDamage defender damage
          let effectedDefender := applyAttackEffects damagedDefender attack.effects
          by_cases hKo : effectedDefender.damage >= effectedDefender.card.hp
          · simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt, hDef, hAttack, hCost, hKo,
              damage, damagedDefender, effectedDefender] at h
            cases h
            simp [setPlayerState]
            exact takePrize_prizes_length_le state.playerOne state.playerTwo
          · simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt, hDef, hAttack, hCost, hKo,
              damage, damagedDefender, effectedDefender] at h
            cases h
            simp [setPlayerState]
        · simp [applyAction, hFirst, otherPlayer, getPlayerState, hAtt, hDef, hAttack, hCost] at h

theorem turn_one_prizes_at_most_one (state : GameState) (actions : List Action)
    (hActions : TurnOneActions actions) :
    ∀ finalState : GameState,
      (actions.foldlM applyAction state = some finalState) →
      (getPlayerState state .playerTwo).prizes.length ≤
        (getPlayerState finalState .playerTwo).prizes.length + 1 := by
  intro finalState hFold
  have hEq := turn_one_prizes_preserved state actions hActions finalState hFold
  simp [hEq, Nat.le_succ]

-- The Turn 1 Theorem: No sequence of legal actions on Turn 1 can result in a win
-- This states that from any valid starting state, after one turn, no player has won
theorem no_turn_one_win (state : GameState) (actions : List Action)
    (hStart : ValidStartingState state)
    (hActions : TurnOneActions actions) :
    ∀ finalState : GameState,
      (actions.foldlM applyAction state = some finalState) →
      ¬ hasWon finalState .playerOne := by
  intro finalState hFold hWon
  have hEq := turn_one_prizes_preserved state actions hActions finalState hFold
  have hWon' : (getPlayerState finalState .playerTwo).prizes.length = 0 := by
    simpa [hasWon, otherPlayer, getPlayerState] using hWon
  have hStartPrizes : (getPlayerState state .playerTwo).prizes.length = standardPrizeCount := by
    simpa [getPlayerState] using hStart.playerTwoPrizes
  have hStateZero : (getPlayerState state .playerTwo).prizes.length = 0 := by
    rw [hEq] at hWon'
    exact hWon'
  have hStandardZero : standardPrizeCount = 0 := by
    rw [hStartPrizes] at hStateZero
    exact hStateZero
  simp [standardPrizeCount] at hStandardZero

-- ============================================================================
-- DAMAGE CALCULATION VERIFICATION
-- ============================================================================

-- Damage is always non-negative (trivially true for Nat)
theorem damage_nonneg (attack : Attack) (attackerType : EnergyType) (defender : Card) :
    0 ≤ calculateDamage attack attackerType defender := by
  exact Nat.zero_le _

-- Weakness at most doubles damage (with default multiplier of 2)
theorem weakness_bounded (damage : Nat) (attackerType : EnergyType) (w : Weakness)
    (hMult : w.multiplier ≥ 1) :
    applyWeakness damage attackerType (some w) ≤ damage * w.multiplier := by
  simp only [applyWeakness]
  split
  · -- Weakness applies
    exact Nat.le_refl _
  · -- Weakness doesn't apply (wrong type), damage ≤ damage * multiplier when multiplier ≥ 1
    exact Nat.le_mul_of_pos_right damage hMult

-- Resistance reduces damage (cannot go negative due to Nat.sub)
theorem resistance_reduces (damage : Nat) (attackerType : EnergyType) (r : Resistance) :
    applyResistance damage attackerType (some r) ≤ damage := by
  simp only [applyResistance]
  split
  · -- Resistance applies
    exact Nat.sub_le damage r.amount
  · -- Resistance doesn't apply
    exact Nat.le_refl _

-- ============================================================================
-- SAMPLE CARDS FOR TESTING
-- ============================================================================

def samplePikachu : Card :=
  { name := "Pikachu"
  , hp := 60
  , energyType := .lightning
  , attacks :=
      [{ name := "Thunder Shock", baseDamage := 20, effects := [.applyStatus .paralyzed], energyCost := [.lightning] }]
  , weakness := some { energyType := .fighting }
  , resistance := some { energyType := .metal } }

def sampleCharmander : Card :=
  { name := "Charmander"
  , hp := 70
  , energyType := .fire
  , attacks := [{ name := "Ember", baseDamage := 30, effects := [], energyCost := [.fire] }]
  , weakness := some { energyType := .water }
  , resistance := none }

-- Helper to safely get first attack
def getFirstAttack (card : Card) : Option Attack :=
  match card.attacks with
  | [] => none
  | a :: _ => some a

-- Example evaluation: Pikachu attacking Charmander
#eval match getFirstAttack samplePikachu with
  | some atk => calculateDamage atk samplePikachu.energyType sampleCharmander
  | none => 0
-- Expected: 20 (no weakness/resistance interaction)

-- Example: Damage with weakness
def sampleSquirtle : Card :=
  { name := "Squirtle"
  , hp := 60
  , energyType := .water
  , attacks := [{ name := "Water Gun", baseDamage := 20, effects := [], energyCost := [.water] }]
  , weakness := some { energyType := .lightning }
  , resistance := none }

#eval match getFirstAttack sampleSquirtle with
  | some atk => calculateDamage atk sampleSquirtle.energyType sampleCharmander
  | none => 0
-- Expected: 40 (water vs fire weakness, 20 * 2)
