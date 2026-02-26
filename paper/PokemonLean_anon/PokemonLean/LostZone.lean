import PokemonLean.Basic
import PokemonLean.Switching

namespace PokemonLean.LostZone

open PokemonLean
open PokemonLean.Switching

-- ============================================================================
-- LOST ZONE AS A PERMANENT GAME ZONE
-- ============================================================================

inductive GameZone
  | deck
  | hand
  | bench
  | active
  | discard
  | prizes
  | lostZone
  deriving Repr, BEq, DecidableEq

def isRecoverableZone : GameZone → Bool
  | .lostZone => false
  | _ => true

@[simp] theorem isRecoverableZone_deck : isRecoverableZone .deck = true := rfl
@[simp] theorem isRecoverableZone_hand : isRecoverableZone .hand = true := rfl
@[simp] theorem isRecoverableZone_bench : isRecoverableZone .bench = true := rfl
@[simp] theorem isRecoverableZone_active : isRecoverableZone .active = true := rfl
@[simp] theorem isRecoverableZone_discard : isRecoverableZone .discard = true := rfl
@[simp] theorem isRecoverableZone_prizes : isRecoverableZone .prizes = true := rfl
@[simp] theorem isRecoverableZone_lostZone : isRecoverableZone .lostZone = false := rfl

theorem isRecoverableZone_false_iff (zone : GameZone) :
    isRecoverableZone zone = false ↔ zone = .lostZone := by
  cases zone <;> simp [isRecoverableZone]

theorem isRecoverableZone_true_iff (zone : GameZone) :
    isRecoverableZone zone = true ↔ zone ≠ .lostZone := by
  cases zone <;> simp [isRecoverableZone]

-- ============================================================================
-- LOST ZONE STATE
-- ============================================================================

inductive LostZoneItem
  | card (card : Card)
  | energy (energyType : EnergyType)
  deriving Repr, BEq, DecidableEq

structure LostZonePlayerState where
  deck : List Card
  hand : List Card
  bench : List PokemonInPlay
  active : Option PokemonInPlay
  discard : List Card
  prizes : List Card
  lostZone : List LostZoneItem := []
  energyDeck : List EnergyType := []
  deriving Repr, BEq, DecidableEq

def ofPlayerState (player : PlayerState) : LostZonePlayerState :=
  { deck := player.deck
  , hand := player.hand
  , bench := player.bench
  , active := player.active
  , discard := player.discard
  , prizes := player.prizes
  , lostZone := []
  , energyDeck := [] }

def toPlayerState (player : LostZonePlayerState) : PlayerState :=
  { deck := player.deck
  , hand := player.hand
  , bench := player.bench
  , active := player.active
  , discard := player.discard
  , prizes := player.prizes }

def withPlayerState (player : LostZonePlayerState) (core : PlayerState) : LostZonePlayerState :=
  { deck := core.deck
  , hand := core.hand
  , bench := core.bench
  , active := core.active
  , discard := core.discard
  , prizes := core.prizes
  , lostZone := player.lostZone
  , energyDeck := player.energyDeck }

@[simp] theorem toPlayerState_ofPlayerState (player : PlayerState) :
    toPlayerState (ofPlayerState player) = player := by
  rfl

@[simp] theorem withPlayerState_toPlayerState (player : LostZonePlayerState) :
    withPlayerState player (toPlayerState player) = player := by
  cases player
  rfl

@[simp] theorem withPlayerState_lostZone (player : LostZonePlayerState) (core : PlayerState) :
    (withPlayerState player core).lostZone = player.lostZone := by
  rfl

@[simp] theorem withPlayerState_energyDeck (player : LostZonePlayerState) (core : PlayerState) :
    (withPlayerState player core).energyDeck = player.energyDeck := by
  rfl


def lostZoneCount (player : LostZonePlayerState) : Nat :=
  player.lostZone.length

def lostZoneAtLeast (player : LostZonePlayerState) (n : Nat) : Prop :=
  n ≤ lostZoneCount player

def hasLostZoneAtLeast (player : LostZonePlayerState) (n : Nat) : Bool :=
  decide (n ≤ lostZoneCount player)

@[simp] theorem lostZoneCount_eq_length (player : LostZonePlayerState) :
    lostZoneCount player = player.lostZone.length := by
  rfl

@[simp] theorem lostZoneCount_ofPlayerState (player : PlayerState) :
    lostZoneCount (ofPlayerState player) = 0 := by
  rfl

theorem lostZoneAtLeast_zero (player : LostZonePlayerState) :
    lostZoneAtLeast player 0 := by
  simp [lostZoneAtLeast, lostZoneCount]

theorem lostZoneAtLeast_self (player : LostZonePlayerState) :
    lostZoneAtLeast player (lostZoneCount player) := by
  simp [lostZoneAtLeast]

theorem hasLostZoneAtLeast_true_iff (player : LostZonePlayerState) (n : Nat) :
    hasLostZoneAtLeast player n = true ↔ n ≤ lostZoneCount player := by
  simp [hasLostZoneAtLeast]

theorem hasLostZoneAtLeast_false_iff (player : LostZonePlayerState) (n : Nat) :
    hasLostZoneAtLeast player n = false ↔ lostZoneCount player < n := by
  simp [hasLostZoneAtLeast]

-- ============================================================================
-- CARD MOVEMENT: LOST ZONE VS DISCARD
-- ============================================================================

def sendCardToLostZone (player : LostZonePlayerState) (card : Card) : LostZonePlayerState :=
  { player with lostZone := .card card :: player.lostZone }

def sendEnergyToLostZone (player : LostZonePlayerState) (energyType : EnergyType) : LostZonePlayerState :=
  { player with lostZone := .energy energyType :: player.lostZone }

def sendCardToDiscard (player : LostZonePlayerState) (card : Card) : LostZonePlayerState :=
  { player with discard := card :: player.discard }

@[simp] theorem sendCardToLostZone_lostZoneCount (player : LostZonePlayerState) (card : Card) :
    lostZoneCount (sendCardToLostZone player card) = lostZoneCount player + 1 := by
  simp [sendCardToLostZone, lostZoneCount]

@[simp] theorem sendCardToLostZone_discard (player : LostZonePlayerState) (card : Card) :
    (sendCardToLostZone player card).discard = player.discard := by
  rfl

@[simp] theorem sendCardToLostZone_hand (player : LostZonePlayerState) (card : Card) :
    (sendCardToLostZone player card).hand = player.hand := by
  rfl

@[simp] theorem sendCardToDiscard_lostZone (player : LostZonePlayerState) (card : Card) :
    (sendCardToDiscard player card).lostZone = player.lostZone := by
  rfl

@[simp] theorem sendCardToDiscard_discard (player : LostZonePlayerState) (card : Card) :
    (sendCardToDiscard player card).discard = card :: player.discard := by
  rfl

@[simp] theorem sendEnergyToLostZone_lostZoneCount (player : LostZonePlayerState) (energyType : EnergyType) :
    lostZoneCount (sendEnergyToLostZone player energyType) = lostZoneCount player + 1 := by
  simp [sendEnergyToLostZone, lostZoneCount]

@[simp] theorem sendEnergyToLostZone_discard (player : LostZonePlayerState) (energyType : EnergyType) :
    (sendEnergyToLostZone player energyType).discard = player.discard := by
  rfl


def sendFromHandToLostZone (player : LostZonePlayerState) (card : Card) : Option LostZonePlayerState :=
  match removeFirst card player.hand with
  | none => none
  | some newHand =>
      some { player with hand := newHand, lostZone := .card card :: player.lostZone }

def sendFromHandToDiscard (player : LostZonePlayerState) (card : Card) : Option LostZonePlayerState :=
  match removeFirst card player.hand with
  | none => none
  | some newHand =>
      some { player with hand := newHand, discard := card :: player.discard }

theorem sendFromHandToLostZone_none_iff (player : LostZonePlayerState) (card : Card) :
    sendFromHandToLostZone player card = none ↔ removeFirst card player.hand = none := by
  unfold sendFromHandToLostZone
  cases h : removeFirst card player.hand <;> simp [h]

theorem sendFromHandToDiscard_none_iff (player : LostZonePlayerState) (card : Card) :
    sendFromHandToDiscard player card = none ↔ removeFirst card player.hand = none := by
  unfold sendFromHandToDiscard
  cases h : removeFirst card player.hand <;> simp [h]

theorem sendFromHandToLostZone_lostZoneCount (player next : LostZonePlayerState) (card : Card)
    (h : sendFromHandToLostZone player card = some next) :
    lostZoneCount next = lostZoneCount player + 1 := by
  unfold sendFromHandToLostZone at h
  cases hRemove : removeFirst card player.hand with
  | none =>
      simp [hRemove] at h
  | some newHand =>
      simp [hRemove] at h
      cases h
      simp [lostZoneCount]

theorem sendFromHandToLostZone_hand_length (player next : LostZonePlayerState) (card : Card)
    (h : sendFromHandToLostZone player card = some next) :
    next.hand.length + 1 = player.hand.length := by
  unfold sendFromHandToLostZone at h
  cases hRemove : removeFirst card player.hand with
  | none =>
      simp [hRemove] at h
  | some newHand =>
      simp [hRemove] at h
      cases h
      simpa using removeFirst_length card player.hand newHand hRemove

theorem sendFromHandToLostZone_discard (player next : LostZonePlayerState) (card : Card)
    (h : sendFromHandToLostZone player card = some next) :
    next.discard = player.discard := by
  unfold sendFromHandToLostZone at h
  cases hRemove : removeFirst card player.hand with
  | none =>
      simp [hRemove] at h
  | some newHand =>
      simp [hRemove] at h
      cases h
      rfl

theorem sendFromHandToDiscard_hand_length (player next : LostZonePlayerState) (card : Card)
    (h : sendFromHandToDiscard player card = some next) :
    next.hand.length + 1 = player.hand.length := by
  unfold sendFromHandToDiscard at h
  cases hRemove : removeFirst card player.hand with
  | none =>
      simp [hRemove] at h
  | some newHand =>
      simp [hRemove] at h
      cases h
      simpa using removeFirst_length card player.hand newHand hRemove

theorem sendFromHandToDiscard_lostZone (player next : LostZonePlayerState) (card : Card)
    (h : sendFromHandToDiscard player card = some next) :
    next.lostZone = player.lostZone := by
  unfold sendFromHandToDiscard at h
  cases hRemove : removeFirst card player.hand with
  | none =>
      simp [hRemove] at h
  | some newHand =>
      simp [hRemove] at h
      cases h
      rfl

theorem sendFromHandToDiscard_discard (player next : LostZonePlayerState) (card : Card)
    (h : sendFromHandToDiscard player card = some next) :
    next.discard = card :: player.discard := by
  unfold sendFromHandToDiscard at h
  cases hRemove : removeFirst card player.hand with
  | none =>
      simp [hRemove] at h
  | some newHand =>
      simp [hRemove] at h
      cases h
      rfl

-- ============================================================================
-- GIRATINA VSTAR: LOST IMPACT (PUT 2 ENERGY IN LOST ZONE)
-- ============================================================================

def lostImpact (player : LostZonePlayerState) : Option LostZonePlayerState :=
  match player.active with
  | none => none
  | some active =>
      match active.energy with
      | e1 :: e2 :: rest =>
          let updatedActive := { active with energy := rest }
          some { player with
            active := some updatedActive
            lostZone := .energy e1 :: .energy e2 :: player.lostZone }
      | _ => none

@[simp] theorem lostImpact_none_no_active (player : LostZonePlayerState) :
    lostImpact { player with active := none } = none := by
  simp [lostImpact]

@[simp] theorem lostImpact_none_zero_energy (player : LostZonePlayerState) (active : PokemonInPlay) :
    lostImpact { player with active := some { active with energy := [] } } = none := by
  simp [lostImpact]

@[simp] theorem lostImpact_none_one_energy (player : LostZonePlayerState) (active : PokemonInPlay) (e : EnergyType) :
    lostImpact { player with active := some { active with energy := [e] } } = none := by
  simp [lostImpact]

theorem lostImpact_some_two_energy (player : LostZonePlayerState) (active : PokemonInPlay)
    (e1 e2 : EnergyType) (rest : List EnergyType) :
    lostImpact { player with active := some { active with energy := e1 :: e2 :: rest } } =
      some { player with
        active := some { active with energy := rest }
        lostZone := .energy e1 :: .energy e2 :: player.lostZone } := by
  simp [lostImpact]

theorem lostImpact_lostZoneCount (player next : LostZonePlayerState)
    (h : lostImpact player = some next) :
    lostZoneCount next = lostZoneCount player + 2 := by
  cases hActive : player.active with
  | none =>
      simp [lostImpact, hActive] at h
  | some active =>
      cases hEnergy : active.energy with
      | nil =>
          simp [lostImpact, hActive, hEnergy] at h
      | cons e1 tail =>
          cases tail with
          | nil =>
              simp [lostImpact, hActive, hEnergy] at h
          | cons e2 rest =>
              simp [lostImpact, hActive, hEnergy] at h
              cases h
              simp [lostZoneCount, Nat.add_assoc]

theorem lostImpact_discard (player next : LostZonePlayerState)
    (h : lostImpact player = some next) :
    next.discard = player.discard := by
  cases hActive : player.active with
  | none =>
      simp [lostImpact, hActive] at h
  | some active =>
      cases hEnergy : active.energy with
      | nil =>
          simp [lostImpact, hActive, hEnergy] at h
      | cons e1 tail =>
          cases tail with
          | nil =>
              simp [lostImpact, hActive, hEnergy] at h
          | cons e2 rest =>
              simp [lostImpact, hActive, hEnergy] at h
              cases h
              rfl

theorem lostImpact_energyDeck (player next : LostZonePlayerState)
    (h : lostImpact player = some next) :
    next.energyDeck = player.energyDeck := by
  cases hActive : player.active with
  | none =>
      simp [lostImpact, hActive] at h
  | some active =>
      cases hEnergy : active.energy with
      | nil =>
          simp [lostImpact, hActive, hEnergy] at h
      | cons e1 tail =>
          cases tail with
          | nil =>
              simp [lostImpact, hActive, hEnergy] at h
          | cons e2 rest =>
              simp [lostImpact, hActive, hEnergy] at h
              cases h
              rfl

-- ============================================================================
-- COMFEY: FLOWER SELECTING (LOOK TOP 2, LOST ZONE 1)
-- ============================================================================

def flowerSelecting (player : LostZonePlayerState) (chooseFirst : Bool) : Option LostZonePlayerState :=
  match player.deck with
  | c1 :: c2 :: rest =>
      if chooseFirst then
        some { player with
          deck := rest
          hand := c2 :: player.hand
          lostZone := .card c1 :: player.lostZone }
      else
        some { player with
          deck := rest
          hand := c1 :: player.hand
          lostZone := .card c2 :: player.lostZone }
  | _ => none

@[simp] theorem flowerSelecting_none_nil (player : LostZonePlayerState) (chooseFirst : Bool) :
    flowerSelecting { player with deck := [] } chooseFirst = none := by
  simp [flowerSelecting]

@[simp] theorem flowerSelecting_none_single (player : LostZonePlayerState) (chooseFirst : Bool) (c : Card) :
    flowerSelecting { player with deck := [c] } chooseFirst = none := by
  simp [flowerSelecting]

theorem flowerSelecting_chooseFirst (player : LostZonePlayerState) (c1 c2 : Card) (rest : List Card) :
    flowerSelecting { player with deck := c1 :: c2 :: rest } true =
      some { player with
        deck := rest
        hand := c2 :: player.hand
        lostZone := .card c1 :: player.lostZone } := by
  simp [flowerSelecting]

theorem flowerSelecting_chooseSecond (player : LostZonePlayerState) (c1 c2 : Card) (rest : List Card) :
    flowerSelecting { player with deck := c1 :: c2 :: rest } false =
      some { player with
        deck := rest
        hand := c1 :: player.hand
        lostZone := .card c2 :: player.lostZone } := by
  simp [flowerSelecting]

theorem flowerSelecting_lostZoneCount (player next : LostZonePlayerState) (chooseFirst : Bool)
    (h : flowerSelecting player chooseFirst = some next) :
    lostZoneCount next = lostZoneCount player + 1 := by
  cases hDeck : player.deck with
  | nil =>
      simp [flowerSelecting, hDeck] at h
  | cons c1 tail =>
      cases tail with
      | nil =>
          simp [flowerSelecting, hDeck] at h
      | cons c2 rest =>
          cases chooseFirst <;> simp [flowerSelecting, hDeck] at h
          · cases h
            simp [lostZoneCount]
          · cases h
            simp [lostZoneCount]

theorem flowerSelecting_hand_length (player next : LostZonePlayerState) (chooseFirst : Bool)
    (h : flowerSelecting player chooseFirst = some next) :
    next.hand.length = player.hand.length + 1 := by
  cases hDeck : player.deck with
  | nil =>
      simp [flowerSelecting, hDeck] at h
  | cons c1 tail =>
      cases tail with
      | nil =>
          simp [flowerSelecting, hDeck] at h
      | cons c2 rest =>
          cases chooseFirst <;> simp [flowerSelecting, hDeck] at h
          · cases h
            simp
          · cases h
            simp

theorem flowerSelecting_deck_length (player next : LostZonePlayerState) (chooseFirst : Bool)
    (h : flowerSelecting player chooseFirst = some next) :
    next.deck.length + 2 = player.deck.length := by
  cases hDeck : player.deck with
  | nil =>
      simp [flowerSelecting, hDeck] at h
  | cons c1 tail =>
      cases tail with
      | nil =>
          simp [flowerSelecting, hDeck] at h
      | cons c2 rest =>
          cases chooseFirst <;> simp [flowerSelecting, hDeck] at h
          · cases h
            simp
          · cases h
            simp

-- ============================================================================
-- MIRAGE GATE (REQUIRES 7+ IN LOST ZONE, ATTACH 2 FROM ENERGY DECK)
-- ============================================================================

def canUseMirageGate (player : LostZonePlayerState) : Bool :=
  decide (7 ≤ lostZoneCount player)

def mirageGate (player : LostZonePlayerState) : Option LostZonePlayerState :=
  if 7 ≤ lostZoneCount player then
    match player.active, player.energyDeck with
    | some active, e1 :: e2 :: rest =>
        let updatedActive := { active with energy := e1 :: e2 :: active.energy }
        some { player with active := some updatedActive, energyDeck := rest }
    | _, _ => none
  else
    none

theorem canUseMirageGate_true_iff (player : LostZonePlayerState) :
    canUseMirageGate player = true ↔ 7 ≤ lostZoneCount player := by
  simp [canUseMirageGate]

theorem canUseMirageGate_false_iff (player : LostZonePlayerState) :
    canUseMirageGate player = false ↔ lostZoneCount player < 7 := by
  simp [canUseMirageGate]

theorem mirageGate_none_of_lt_seven (player : LostZonePlayerState)
    (h : lostZoneCount player < 7) :
    mirageGate player = none := by
  have hNot : ¬ 7 ≤ player.lostZone.length := by
    simpa [lostZoneCount] using (Nat.not_le_of_gt h)
  simp [mirageGate, lostZoneCount, hNot]

theorem mirageGate_none_no_active (player : LostZonePlayerState)
    (hCount : 7 ≤ lostZoneCount player) :
    mirageGate { player with active := none } = none := by
  have hCount' : 7 ≤ player.lostZone.length := by
    simpa [lostZoneCount] using hCount
  simp [mirageGate, lostZoneCount, hCount']

theorem mirageGate_none_insufficient_energyDeck
    (player : LostZonePlayerState) (active : PokemonInPlay) (e : EnergyType)
    (hCount : 7 ≤ lostZoneCount player) :
    mirageGate { player with active := some active, energyDeck := [e] } = none := by
  have hCount' : 7 ≤ player.lostZone.length := by
    simpa [lostZoneCount] using hCount
  simp [mirageGate, lostZoneCount, hCount']

theorem mirageGate_some_of_ready
    (player : LostZonePlayerState) (active : PokemonInPlay)
    (e1 e2 : EnergyType) (rest : List EnergyType)
    (hCount : 7 ≤ lostZoneCount player) :
    mirageGate { player with active := some active, energyDeck := e1 :: e2 :: rest } =
      some { player with
        active := some { active with energy := e1 :: e2 :: active.energy }
        energyDeck := rest } := by
  have hCount' : 7 ≤ player.lostZone.length := by
    simpa [lostZoneCount] using hCount
  simp [mirageGate, lostZoneCount, hCount']

theorem mirageGate_some_implies_threshold (player next : LostZonePlayerState)
    (h : mirageGate player = some next) :
    7 ≤ lostZoneCount player := by
  unfold mirageGate at h
  split at h
  · assumption
  · simp at h

theorem mirageGate_energyDeck_length (player next : LostZonePlayerState)
    (h : mirageGate player = some next) :
    next.energyDeck.length + 2 = player.energyDeck.length := by
  unfold mirageGate at h
  split at h
  · cases hActive : player.active with
    | none =>
        simp [hActive] at h
    | some active =>
        cases hDeck : player.energyDeck with
        | nil =>
            simp [hActive, hDeck] at h
        | cons e1 tail =>
            cases tail with
            | nil =>
                simp [hActive, hDeck] at h
            | cons e2 rest =>
                simp [hActive, hDeck] at h
                cases h
                simp
  · simp at h

theorem mirageGate_lostZone (player next : LostZonePlayerState)
    (h : mirageGate player = some next) :
    next.lostZone = player.lostZone := by
  unfold mirageGate at h
  split at h
  · cases hActive : player.active with
    | none =>
        simp [hActive] at h
    | some active =>
        cases hDeck : player.energyDeck with
        | nil =>
            simp [hActive, hDeck] at h
        | cons e1 tail =>
            cases tail with
            | nil =>
                simp [hActive, hDeck] at h
            | cons e2 rest =>
                simp [hActive, hDeck] at h
                cases h
                rfl
  · simp at h

-- ============================================================================
-- LOST CITY STADIUM (KO'D POKEMON GO TO LOST ZONE)
-- ============================================================================

def knockOutActiveToDiscard (player : LostZonePlayerState) : LostZonePlayerState :=
  match player.active with
  | none => player
  | some active => { player with active := none, discard := active.card :: player.discard }

def knockOutActiveToLostZone (player : LostZonePlayerState) : LostZonePlayerState :=
  match player.active with
  | none => player
  | some active => { player with active := none, lostZone := .card active.card :: player.lostZone }

def lostCityKO (lostCityInPlay : Bool) (player : LostZonePlayerState) : LostZonePlayerState :=
  if lostCityInPlay then knockOutActiveToLostZone player else knockOutActiveToDiscard player

@[simp] theorem knockOutActiveToDiscard_none (player : LostZonePlayerState)
    (h : player.active = none) :
    knockOutActiveToDiscard player = player := by
  simp [knockOutActiveToDiscard, h]

@[simp] theorem knockOutActiveToLostZone_none (player : LostZonePlayerState)
    (h : player.active = none) :
    knockOutActiveToLostZone player = player := by
  simp [knockOutActiveToLostZone, h]

theorem knockOutActiveToDiscard_some (player : LostZonePlayerState) (active : PokemonInPlay)
    (h : player.active = some active) :
    knockOutActiveToDiscard player =
      { player with active := none, discard := active.card :: player.discard } := by
  simp [knockOutActiveToDiscard, h]

theorem knockOutActiveToLostZone_some (player : LostZonePlayerState) (active : PokemonInPlay)
    (h : player.active = some active) :
    knockOutActiveToLostZone player =
      { player with active := none, lostZone := .card active.card :: player.lostZone } := by
  simp [knockOutActiveToLostZone, h]

@[simp] theorem lostCityKO_true (player : LostZonePlayerState) :
    lostCityKO true player = knockOutActiveToLostZone player := by
  simp [lostCityKO]

@[simp] theorem lostCityKO_false (player : LostZonePlayerState) :
    lostCityKO false player = knockOutActiveToDiscard player := by
  simp [lostCityKO]

theorem lostCityKO_true_lostZoneCount (player : LostZonePlayerState) (active : PokemonInPlay)
    (h : player.active = some active) :
    lostZoneCount (lostCityKO true player) = lostZoneCount player + 1 := by
  simp [lostCityKO, knockOutActiveToLostZone, h, lostZoneCount]

theorem lostCityKO_false_discard_length (player : LostZonePlayerState) (active : PokemonInPlay)
    (h : player.active = some active) :
    (lostCityKO false player).discard.length = player.discard.length + 1 := by
  simp [lostCityKO, knockOutActiveToDiscard, h]

-- ============================================================================
-- LOST VACUUM (PAY COST TO LOST ZONE FOR SWITCH / GUST)
-- ============================================================================

def payLostVacuumCost (player : LostZonePlayerState) (card : Card) : Option LostZonePlayerState :=
  sendFromHandToLostZone player card

def lostVacuumSwitch (player : LostZonePlayerState) (costCard : Card) : Option LostZonePlayerState :=
  match payLostVacuumCost player costCard with
  | none => none
  | some paid =>
      match switchHead (toPlayerState paid) with
      | none => none
      | some switched => some (withPlayerState paid switched)

def lostVacuumGust
    (user opponent : LostZonePlayerState)
    (costCard : Card)
    (benchIndex : Nat) :
    Option (LostZonePlayerState × LostZonePlayerState) :=
  match payLostVacuumCost user costCard with
  | none => none
  | some paidUser =>
      match switchWithBenchIndex (toPlayerState opponent) benchIndex with
      | none => none
      | some switchedOpponent => some (paidUser, withPlayerState opponent switchedOpponent)

@[simp] theorem payLostVacuumCost_eq_sendFromHandToLostZone
    (player : LostZonePlayerState) (card : Card) :
    payLostVacuumCost player card = sendFromHandToLostZone player card := by
  rfl

theorem payLostVacuumCost_lostZoneCount (player next : LostZonePlayerState) (card : Card)
    (h : payLostVacuumCost player card = some next) :
    lostZoneCount next = lostZoneCount player + 1 := by
  exact sendFromHandToLostZone_lostZoneCount player next card h

theorem payLostVacuumCost_hand_length (player next : LostZonePlayerState) (card : Card)
    (h : payLostVacuumCost player card = some next) :
    next.hand.length + 1 = player.hand.length := by
  exact sendFromHandToLostZone_hand_length player next card h

theorem payLostVacuumCost_energyDeck (player next : LostZonePlayerState) (card : Card)
    (h : payLostVacuumCost player card = some next) :
    next.energyDeck = player.energyDeck := by
  unfold payLostVacuumCost sendFromHandToLostZone at h
  cases hRemove : removeFirst card player.hand with
  | none =>
      simp [hRemove] at h
  | some newHand =>
      simp [hRemove] at h
      cases h
      rfl

theorem lostVacuumSwitch_none_of_cost_fail (player : LostZonePlayerState) (costCard : Card)
    (hCost : payLostVacuumCost player costCard = none) :
    lostVacuumSwitch player costCard = none := by
  have hCost' : sendFromHandToLostZone player costCard = none := by
    simpa [payLostVacuumCost] using hCost
  simp [lostVacuumSwitch, hCost']

theorem lostVacuumSwitch_some_of_switch
    (player paid : LostZonePlayerState) (costCard : Card) (switched : PlayerState)
    (hCost : payLostVacuumCost player costCard = some paid)
    (hSwitch : switchHead (toPlayerState paid) = some switched) :
    lostVacuumSwitch player costCard = some (withPlayerState paid switched) := by
  have hCost' : sendFromHandToLostZone player costCard = some paid := by
    simpa [payLostVacuumCost] using hCost
  simp [lostVacuumSwitch, hCost', hSwitch]

theorem lostVacuumSwitch_lostZoneCount (player next : LostZonePlayerState) (costCard : Card)
    (h : lostVacuumSwitch player costCard = some next) :
    lostZoneCount next = lostZoneCount player + 1 := by
  unfold lostVacuumSwitch at h
  cases hCost : sendFromHandToLostZone player costCard with
  | none =>
      simp [hCost] at h
  | some paid =>
      cases hSwitch : switchHead (toPlayerState paid) with
      | none =>
          simp [hCost, hSwitch] at h
      | some switched =>
          simp [hCost, hSwitch] at h
          cases h
          have hCount := sendFromHandToLostZone_lostZoneCount player paid costCard hCost
          simpa [withPlayerState] using hCount

theorem lostVacuumSwitch_energyDeck (player next : LostZonePlayerState) (costCard : Card)
    (h : lostVacuumSwitch player costCard = some next) :
    next.energyDeck = player.energyDeck := by
  unfold lostVacuumSwitch at h
  cases hCost : sendFromHandToLostZone player costCard with
  | none =>
      simp [hCost] at h
  | some paid =>
      cases hSwitch : switchHead (toPlayerState paid) with
      | none =>
          simp [hCost, hSwitch] at h
      | some switched =>
          simp [hCost, hSwitch] at h
          cases h
          have hDeck : paid.energyDeck = player.energyDeck := by
            unfold sendFromHandToLostZone at hCost
            cases hRemove : removeFirst costCard player.hand with
            | none =>
                simp [hRemove] at hCost
            | some newHand =>
                simp [hRemove] at hCost
                cases hCost
                rfl
          simpa [withPlayerState, hDeck] using hDeck

theorem lostVacuumGust_none_of_cost_fail
    (user opponent : LostZonePlayerState) (costCard : Card) (benchIndex : Nat)
    (hCost : payLostVacuumCost user costCard = none) :
    lostVacuumGust user opponent costCard benchIndex = none := by
  have hCost' : sendFromHandToLostZone user costCard = none := by
    simpa [payLostVacuumCost] using hCost
  simp [lostVacuumGust, hCost']

theorem lostVacuumGust_some_of_switch
    (user opponent paidUser : LostZonePlayerState)
    (costCard : Card)
    (benchIndex : Nat)
    (switchedOpponent : PlayerState)
    (hCost : payLostVacuumCost user costCard = some paidUser)
    (hSwitch : switchWithBenchIndex (toPlayerState opponent) benchIndex = some switchedOpponent) :
    lostVacuumGust user opponent costCard benchIndex =
      some (paidUser, withPlayerState opponent switchedOpponent) := by
  have hCost' : sendFromHandToLostZone user costCard = some paidUser := by
    simpa [payLostVacuumCost] using hCost
  simp [lostVacuumGust, hCost', hSwitch]

theorem lostVacuumGust_user_lostZoneCount
    (user opponent nextUser nextOpponent : LostZonePlayerState)
    (costCard : Card)
    (benchIndex : Nat)
    (h : lostVacuumGust user opponent costCard benchIndex = some (nextUser, nextOpponent)) :
    lostZoneCount nextUser = lostZoneCount user + 1 := by
  unfold lostVacuumGust at h
  cases hCost : sendFromHandToLostZone user costCard with
  | none =>
      simp [hCost] at h
  | some paidUser =>
      cases hSwitch : switchWithBenchIndex (toPlayerState opponent) benchIndex with
      | none =>
          simp [hCost, hSwitch] at h
      | some switchedOpponent =>
          simp [hCost, hSwitch] at h
          rcases h with ⟨hUser, hOpponent⟩
          subst hUser
          exact sendFromHandToLostZone_lostZoneCount user paidUser costCard hCost

theorem lostVacuumGust_opponent_lostZone
    (user opponent nextUser nextOpponent : LostZonePlayerState)
    (costCard : Card)
    (benchIndex : Nat)
    (h : lostVacuumGust user opponent costCard benchIndex = some (nextUser, nextOpponent)) :
    nextOpponent.lostZone = opponent.lostZone := by
  unfold lostVacuumGust at h
  cases hCost : sendFromHandToLostZone user costCard with
  | none =>
      simp [hCost] at h
  | some paidUser =>
      cases hSwitch : switchWithBenchIndex (toPlayerState opponent) benchIndex with
      | none =>
          simp [hCost, hSwitch] at h
      | some switchedOpponent =>
          simp [hCost, hSwitch] at h
          rcases h with ⟨hUser, hOpponent⟩
          subst hOpponent
          simp [withPlayerState]

theorem lostVacuumGust_opponent_energyDeck
    (user opponent nextUser nextOpponent : LostZonePlayerState)
    (costCard : Card)
    (benchIndex : Nat)
    (h : lostVacuumGust user opponent costCard benchIndex = some (nextUser, nextOpponent)) :
    nextOpponent.energyDeck = opponent.energyDeck := by
  unfold lostVacuumGust at h
  cases hCost : sendFromHandToLostZone user costCard with
  | none =>
      simp [hCost] at h
  | some paidUser =>
      cases hSwitch : switchWithBenchIndex (toPlayerState opponent) benchIndex with
      | none =>
          simp [hCost, hSwitch] at h
      | some switchedOpponent =>
          simp [hCost, hSwitch] at h
          rcases h with ⟨hUser, hOpponent⟩
          subst hOpponent
          simp [withPlayerState]

-- ============================================================================
-- SABLEYE: LOST MINE (12 DAMAGE COUNTERS IF 10+ IN LOST ZONE)
-- ============================================================================

def lostMineDamageCounters : Nat := 12

def lostMineDamage : Nat :=
  lostMineDamageCounters * 10

def canUseLostMine (player : LostZonePlayerState) : Bool :=
  decide (10 ≤ lostZoneCount player)

def sableyeLostMine (attacker : LostZonePlayerState) (target : PokemonInPlay) : Option PokemonInPlay :=
  if 10 ≤ lostZoneCount attacker then
    some (applyDamage target lostMineDamage)
  else
    none

def sableyeLostMineActive
    (attacker defender : LostZonePlayerState) :
    Option LostZonePlayerState :=
  if 10 ≤ lostZoneCount attacker then
    match defender.active with
    | none => none
    | some active =>
        some { defender with active := some (applyDamage active lostMineDamage) }
  else
    none

@[simp] theorem lostMineDamageCounters_value : lostMineDamageCounters = 12 := rfl

@[simp] theorem lostMineDamage_value : lostMineDamage = 120 := by
  simp [lostMineDamage, lostMineDamageCounters]

theorem canUseLostMine_true_iff (player : LostZonePlayerState) :
    canUseLostMine player = true ↔ 10 ≤ lostZoneCount player := by
  simp [canUseLostMine]

theorem canUseLostMine_false_iff (player : LostZonePlayerState) :
    canUseLostMine player = false ↔ lostZoneCount player < 10 := by
  simp [canUseLostMine]

theorem sableyeLostMine_none_of_lt_ten (attacker : LostZonePlayerState) (target : PokemonInPlay)
    (h : lostZoneCount attacker < 10) :
    sableyeLostMine attacker target = none := by
  have hNot : ¬ 10 ≤ attacker.lostZone.length := by
    simpa [lostZoneCount] using (Nat.not_le_of_gt h)
  simp [sableyeLostMine, lostZoneCount, hNot]

theorem sableyeLostMine_some_of_ten (attacker : LostZonePlayerState) (target : PokemonInPlay)
    (h : 10 ≤ lostZoneCount attacker) :
    sableyeLostMine attacker target = some (applyDamage target lostMineDamage) := by
  have hCount : 10 ≤ attacker.lostZone.length := by
    simpa [lostZoneCount] using h
  simp [sableyeLostMine, lostZoneCount, hCount]

theorem sableyeLostMine_damage_le_hp (attacker : LostZonePlayerState)
    (target damaged : PokemonInPlay)
    (h : sableyeLostMine attacker target = some damaged) :
    damaged.damage ≤ target.card.hp := by
  unfold sableyeLostMine at h
  split at h
  · simp at h
    cases h
    simpa [lostMineDamage] using applyDamage_damage_le_hp target lostMineDamage
  · simp at h

@[simp] theorem sableyeLostMineActive_none_no_active
    (attacker defender : LostZonePlayerState)
    (hCount : 10 ≤ lostZoneCount attacker)
    (hActive : defender.active = none) :
    sableyeLostMineActive attacker defender = none := by
  have hCount' : 10 ≤ attacker.lostZone.length := by
    simpa [lostZoneCount] using hCount
  simp [sableyeLostMineActive, lostZoneCount, hCount', hActive]

theorem sableyeLostMineActive_none_of_lt_ten
    (attacker defender : LostZonePlayerState)
    (h : lostZoneCount attacker < 10) :
    sableyeLostMineActive attacker defender = none := by
  have hNot : ¬ 10 ≤ attacker.lostZone.length := by
    simpa [lostZoneCount] using (Nat.not_le_of_gt h)
  simp [sableyeLostMineActive, lostZoneCount, hNot]

theorem sableyeLostMineActive_some_of_ten
    (attacker defender : LostZonePlayerState)
    (active : PokemonInPlay)
    (hCount : 10 ≤ lostZoneCount attacker)
    (hActive : defender.active = some active) :
    sableyeLostMineActive attacker defender =
      some { defender with active := some (applyDamage active lostMineDamage) } := by
  have hCount' : 10 ≤ attacker.lostZone.length := by
    simpa [lostZoneCount] using hCount
  simp [sableyeLostMineActive, lostZoneCount, hCount', hActive]

theorem sableyeLostMineActive_lostZone
    (attacker defender next : LostZonePlayerState)
    (h : sableyeLostMineActive attacker defender = some next) :
    next.lostZone = defender.lostZone := by
  unfold sableyeLostMineActive at h
  split at h
  · cases hActive : defender.active with
    | none =>
        simp [hActive] at h
    | some active =>
        simp [hActive] at h
        cases h
        rfl
  · simp at h

end PokemonLean.LostZone
