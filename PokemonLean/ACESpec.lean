import PokemonLean.DeckBuilding

namespace PokemonLean.ACESpec

open PokemonLean.DeckBuilding

/-- Named ACE SPEC trainer cards. -/
inductive AceSpecName
  | computerSearch
  | dowsingMachine
  | scrambleSwitch
  | lifeDew
  | masterBall
  | rockGuard
  | goldPotion
  | crystalWall
  | crystalEdge
  | gBooster
  | gScope
  deriving Repr, BEq, DecidableEq

/-- Canonical display name for each ACE SPEC card. -/
def aceSpecName : AceSpecName → String
  | .computerSearch => "Computer Search"
  | .dowsingMachine => "Dowsing Machine"
  | .scrambleSwitch => "Scramble Switch"
  | .lifeDew => "Life Dew"
  | .masterBall => "Master Ball"
  | .rockGuard => "Rock Guard"
  | .goldPotion => "Gold Potion"
  | .crystalWall => "Crystal Wall"
  | .crystalEdge => "Crystal Edge"
  | .gBooster => "G Booster"
  | .gScope => "G Scope"

@[simp] theorem aceSpecName_computerSearch :
    aceSpecName .computerSearch = "Computer Search" := rfl

@[simp] theorem aceSpecName_dowsingMachine :
    aceSpecName .dowsingMachine = "Dowsing Machine" := rfl

@[simp] theorem aceSpecName_scrambleSwitch :
    aceSpecName .scrambleSwitch = "Scramble Switch" := rfl

@[simp] theorem aceSpecName_lifeDew :
    aceSpecName .lifeDew = "Life Dew" := rfl

@[simp] theorem aceSpecName_masterBall :
    aceSpecName .masterBall = "Master Ball" := rfl

@[simp] theorem aceSpecName_rockGuard :
    aceSpecName .rockGuard = "Rock Guard" := rfl

@[simp] theorem aceSpecName_goldPotion :
    aceSpecName .goldPotion = "Gold Potion" := rfl

@[simp] theorem aceSpecName_crystalWall :
    aceSpecName .crystalWall = "Crystal Wall" := rfl

@[simp] theorem aceSpecName_crystalEdge :
    aceSpecName .crystalEdge = "Crystal Edge" := rfl

@[simp] theorem aceSpecName_gBooster :
    aceSpecName .gBooster = "G Booster" := rfl

@[simp] theorem aceSpecName_gScope :
    aceSpecName .gScope = "G Scope" := rfl

/-- The complete ACE SPEC pool represented in this module. -/
def allAceSpecNames : List AceSpecName :=
  [ .computerSearch
  , .dowsingMachine
  , .scrambleSwitch
  , .lifeDew
  , .masterBall
  , .rockGuard
  , .goldPotion
  , .crystalWall
  , .crystalEdge
  , .gBooster
  , .gScope
  ]

@[simp] theorem allAceSpecNames_length : allAceSpecNames.length = 11 := by
  simp [allAceSpecNames]

theorem allAceSpecNames_nodup : allAceSpecNames.Nodup := by
  decide

@[simp] theorem mem_allAceSpecNames_computerSearch :
    .computerSearch ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_dowsingMachine :
    .dowsingMachine ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_scrambleSwitch :
    .scrambleSwitch ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_lifeDew :
    .lifeDew ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_masterBall :
    .masterBall ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_rockGuard :
    .rockGuard ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_goldPotion :
    .goldPotion ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_crystalWall :
    .crystalWall ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_crystalEdge :
    .crystalEdge ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_gBooster :
    .gBooster ∈ allAceSpecNames := by
  simp [allAceSpecNames]

@[simp] theorem mem_allAceSpecNames_gScope :
    .gScope ∈ allAceSpecNames := by
  simp [allAceSpecNames]

/-- Abstracted ACE SPEC effects. -/
inductive AceSpecEffect
  | searchAnyCard
  | recoverItem
  | switchAndMoveEnergy
  | preventPrize
  | guaranteedCatch
  | damageOnContact (amount : Nat)
  | fullHeal
  | setHP (hp : Nat)
  | setDamage (amount : Nat)
  | damageIgnoreEffects (amount : Nat)
  | damageIgnoreBenchProtection (amount : Nat)
  deriving Repr, BEq, DecidableEq

/-- Effect associated with each named ACE SPEC card. -/
def effectOf : AceSpecName → AceSpecEffect
  | .computerSearch => .searchAnyCard
  | .dowsingMachine => .recoverItem
  | .scrambleSwitch => .switchAndMoveEnergy
  | .lifeDew => .preventPrize
  | .masterBall => .guaranteedCatch
  | .rockGuard => .damageOnContact 60
  | .goldPotion => .fullHeal
  | .crystalWall => .setHP 300
  | .crystalEdge => .setDamage 100
  | .gBooster => .damageIgnoreEffects 200
  | .gScope => .damageIgnoreBenchProtection 100

@[simp] theorem effectOf_computerSearch :
    effectOf .computerSearch = .searchAnyCard := rfl

@[simp] theorem effectOf_dowsingMachine :
    effectOf .dowsingMachine = .recoverItem := rfl

@[simp] theorem effectOf_scrambleSwitch :
    effectOf .scrambleSwitch = .switchAndMoveEnergy := rfl

@[simp] theorem effectOf_lifeDew :
    effectOf .lifeDew = .preventPrize := rfl

@[simp] theorem effectOf_masterBall :
    effectOf .masterBall = .guaranteedCatch := rfl

@[simp] theorem effectOf_rockGuard :
    effectOf .rockGuard = .damageOnContact 60 := rfl

@[simp] theorem effectOf_goldPotion :
    effectOf .goldPotion = .fullHeal := rfl

@[simp] theorem effectOf_crystalWall :
    effectOf .crystalWall = .setHP 300 := rfl

@[simp] theorem effectOf_crystalEdge :
    effectOf .crystalEdge = .setDamage 100 := rfl

@[simp] theorem effectOf_gBooster :
    effectOf .gBooster = .damageIgnoreEffects 200 := rfl

@[simp] theorem effectOf_gScope :
    effectOf .gScope = .damageIgnoreBenchProtection 100 := rfl

/-- Simplified state tracked for ACE SPEC effect resolution. -/
structure AceSpecState where
  searchedAnyCard : Bool := false
  recoveredItem : Bool := false
  switchedActive : Bool := false
  movedEnergy : Bool := false
  preventedPrize : Bool := false
  guaranteedCatch : Bool := false
  contactDamage : Nat := 0
  activeHP : Nat := 0
  activeDamage : Nat := 0
  outgoingDamage : Nat := 0
  benchDamage : Nat := 0
  ignoresDefendingEffects : Bool := false
  ignoresBenchProtection : Bool := false
  deriving Repr, BEq, DecidableEq

/-- Deterministic resolution of an ACE SPEC effect into state updates. -/
def applyEffect (state : AceSpecState) : AceSpecEffect → AceSpecState
  | .searchAnyCard => { state with searchedAnyCard := true }
  | .recoverItem => { state with recoveredItem := true }
  | .switchAndMoveEnergy => { state with switchedActive := true, movedEnergy := true }
  | .preventPrize => { state with preventedPrize := true }
  | .guaranteedCatch => { state with guaranteedCatch := true }
  | .damageOnContact amount => { state with contactDamage := amount }
  | .fullHeal => { state with activeDamage := 0 }
  | .setHP hp => { state with activeHP := hp }
  | .setDamage amount => { state with outgoingDamage := amount }
  | .damageIgnoreEffects amount =>
      { state with outgoingDamage := amount, ignoresDefendingEffects := true }
  | .damageIgnoreBenchProtection amount =>
      { state with benchDamage := amount, ignoresBenchProtection := true }

@[simp] theorem applyEffect_searchAnyCard (state : AceSpecState) :
    (applyEffect state .searchAnyCard).searchedAnyCard = true := by
  simp [applyEffect]

@[simp] theorem applyEffect_recoverItem (state : AceSpecState) :
    (applyEffect state .recoverItem).recoveredItem = true := by
  simp [applyEffect]

@[simp] theorem applyEffect_switchAndMoveEnergy_switched (state : AceSpecState) :
    (applyEffect state .switchAndMoveEnergy).switchedActive = true := by
  simp [applyEffect]

@[simp] theorem applyEffect_switchAndMoveEnergy_moved (state : AceSpecState) :
    (applyEffect state .switchAndMoveEnergy).movedEnergy = true := by
  simp [applyEffect]

@[simp] theorem applyEffect_preventPrize (state : AceSpecState) :
    (applyEffect state .preventPrize).preventedPrize = true := by
  simp [applyEffect]

@[simp] theorem applyEffect_guaranteedCatch (state : AceSpecState) :
    (applyEffect state .guaranteedCatch).guaranteedCatch = true := by
  simp [applyEffect]

@[simp] theorem applyEffect_damageOnContact (state : AceSpecState) (amount : Nat) :
    (applyEffect state (.damageOnContact amount)).contactDamage = amount := by
  simp [applyEffect]

@[simp] theorem applyEffect_fullHeal (state : AceSpecState) :
    (applyEffect state .fullHeal).activeDamage = 0 := by
  simp [applyEffect]

@[simp] theorem applyEffect_setHP (state : AceSpecState) (hp : Nat) :
    (applyEffect state (.setHP hp)).activeHP = hp := by
  simp [applyEffect]

@[simp] theorem applyEffect_setDamage (state : AceSpecState) (amount : Nat) :
    (applyEffect state (.setDamage amount)).outgoingDamage = amount := by
  simp [applyEffect]

@[simp] theorem applyEffect_damageIgnoreEffects_damage (state : AceSpecState) (amount : Nat) :
    (applyEffect state (.damageIgnoreEffects amount)).outgoingDamage = amount := by
  simp [applyEffect]

@[simp] theorem applyEffect_damageIgnoreEffects_flag (state : AceSpecState) (amount : Nat) :
    (applyEffect state (.damageIgnoreEffects amount)).ignoresDefendingEffects = true := by
  simp [applyEffect]

@[simp] theorem applyEffect_damageIgnoreBenchProtection_damage (state : AceSpecState) (amount : Nat) :
    (applyEffect state (.damageIgnoreBenchProtection amount)).benchDamage = amount := by
  simp [applyEffect]

@[simp] theorem applyEffect_damageIgnoreBenchProtection_flag (state : AceSpecState) (amount : Nat) :
    (applyEffect state (.damageIgnoreBenchProtection amount)).ignoresBenchProtection = true := by
  simp [applyEffect]

/-- Apply a named ACE SPEC card. -/
def playAceSpec (state : AceSpecState) (card : AceSpecName) : AceSpecState :=
  applyEffect state (effectOf card)

@[simp] theorem playAceSpec_computerSearch_search (state : AceSpecState) :
    (playAceSpec state .computerSearch).searchedAnyCard = true := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_dowsingMachine_recover (state : AceSpecState) :
    (playAceSpec state .dowsingMachine).recoveredItem = true := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_scrambleSwitch_switched (state : AceSpecState) :
    (playAceSpec state .scrambleSwitch).switchedActive = true := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_scrambleSwitch_moved (state : AceSpecState) :
    (playAceSpec state .scrambleSwitch).movedEnergy = true := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_lifeDew_preventedPrize (state : AceSpecState) :
    (playAceSpec state .lifeDew).preventedPrize = true := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_masterBall_guaranteedCatch (state : AceSpecState) :
    (playAceSpec state .masterBall).guaranteedCatch = true := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_rockGuard_contactDamage (state : AceSpecState) :
    (playAceSpec state .rockGuard).contactDamage = 60 := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_goldPotion_fullHeal (state : AceSpecState) :
    (playAceSpec state .goldPotion).activeDamage = 0 := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_crystalWall_setHP (state : AceSpecState) :
    (playAceSpec state .crystalWall).activeHP = 300 := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_crystalEdge_setDamage (state : AceSpecState) :
    (playAceSpec state .crystalEdge).outgoingDamage = 100 := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_gBooster_setDamage (state : AceSpecState) :
    (playAceSpec state .gBooster).outgoingDamage = 200 := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_gBooster_ignoreEffects (state : AceSpecState) :
    (playAceSpec state .gBooster).ignoresDefendingEffects = true := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_gScope_setBenchDamage (state : AceSpecState) :
    (playAceSpec state .gScope).benchDamage = 100 := by
  simp [playAceSpec]

@[simp] theorem playAceSpec_gScope_ignoreBenchProtection (state : AceSpecState) :
    (playAceSpec state .gScope).ignoresBenchProtection = true := by
  simp [playAceSpec]

/-- ACE SPEC deck-building rule: at most one ACE SPEC card per deck. -/
def aceSpecDeckConstraint (deck : List DeckCard) : Prop :=
  aceSpecCount deck ≤ 1

theorem aceSpecDeckConstraint_iff (deck : List DeckCard) :
    aceSpecDeckConstraint deck ↔ aceSpecCount deck ≤ 1 := Iff.rfl

theorem aceSpecDeckConstraint_eq_aceSpecLegal (deck : List DeckCard) :
    aceSpecDeckConstraint deck ↔ aceSpecLegal deck := by
  simp [aceSpecDeckConstraint, aceSpecLegal]

theorem aceSpecDeckConstraint_nil : aceSpecDeckConstraint [] := by
  simp [aceSpecDeckConstraint]

theorem aceSpecDeckConstraint_singleton (c : DeckCard) :
    aceSpecDeckConstraint [c] := by
  cases hAce : c.isAceSpec <;> simp [aceSpecDeckConstraint, aceSpecCount, hAce]

/-- Deck validity with explicit ACE SPEC constraint. -/
def deckValidWithAceSpec (deck : List DeckCard) : Prop :=
  hasSixtyCards deck ∧
  legalCopies deck ∧
  hasBasicPokemon deck ∧
  aceSpecDeckConstraint deck

theorem deckValidWithAceSpec_hasSixtyCards (deck : List DeckCard) :
    deckValidWithAceSpec deck → hasSixtyCards deck := by
  intro h
  exact h.1

theorem deckValidWithAceSpec_legalCopies (deck : List DeckCard) :
    deckValidWithAceSpec deck → legalCopies deck := by
  intro h
  exact h.2.1

theorem deckValidWithAceSpec_hasBasicPokemon (deck : List DeckCard) :
    deckValidWithAceSpec deck → hasBasicPokemon deck := by
  intro h
  exact h.2.2.1

theorem deckValidWithAceSpec_aceSpecDeckConstraint (deck : List DeckCard) :
    deckValidWithAceSpec deck → aceSpecDeckConstraint deck := by
  intro h
  exact h.2.2.2

theorem deckValidWithAceSpec_of_legalDeck (deck : List DeckCard) :
    legalDeck deck → deckValidWithAceSpec deck := by
  intro h
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  simpa [aceSpecDeckConstraint, aceSpecLegal] using h.2.2.2.1

theorem aceSpecDeckConstraint_of_legalDeck (deck : List DeckCard) :
    legalDeck deck → aceSpecDeckConstraint deck := by
  intro h
  exact (deckValidWithAceSpec_of_legalDeck deck h).2.2.2

end PokemonLean.ACESpec
