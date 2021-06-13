module VVXtAdventure.Base where
-- | GameData contains game data, e.g., the player's name, the contents
-- of the player's inventory, whether or not a question is currently
-- asked, and whether or not the player is become a corpse.
data GameData = GameData {
  -- | For all 'GameData' k, playerName k equals the name of the player
  -- character, NOT the name of the player, of k.
  playerName :: CharName,
  -- | For all 'GameData' k, playerName k equals the contents of the
  -- inventory of the player character of k.
  -- The order of inventory is arbitrary.
  inventory :: [Item],
  -- | For all 'GameData' k, questionYNExists k iff a question is
  -- currently asked such that the player responds.
  questionYNExists :: Bool,
  -- | For all 'GameData' k, secretWordNums k denotes the number of
  -- occurrences of the secret word, which is generally actually a
  -- secret phrase, but whatever.
  secretWordNums :: Integer,
  -- | For all 'GameData' k, status k equals the status of the player
  -- character of k.  @status k == Alive@ iff the player character of
  -- k is alive.  @status k == Dead@ iff the player character of k is
  -- dead.
  status :: State,
  -- | To what extent is the living room table smashed up?
  lrTableSmashedness :: Integer,
  -- | Is the table in the living room flipped upside-down?
  lrTableFlipped :: Bool,
  -- | Is any debris of the living room table on the floor of the
  -- living room?
  lrTableDebrisPresent :: Bool,
  -- | What is the player character's current location?
  currentRoom :: Room
} deriving (Eq, Read, Show);

-- | For all Item k, k is an inventory item of some sort.
data Item = Item {
  -- | For all 'Item' k, itemName k equals the human-readable name of
  -- k, e.g., "a broken toilet".
  itemName :: String
} deriving (Eq, Read, Show);

-- | For all CharName k, k is the name of a character.
data CharName = CharName {
  -- | For all 'CharName' k, forename k is the forename of a character,
  -- e.g., "SPINACH".
  forename :: String,
  -- | For all 'CharName' k, surname k is the surname of a character,
  -- e.g., "GRAVYBOAT".
  surname :: String,
  -- | For all 'CharName' k, nickname k is the nickname of a character,
  -- e.g., "WARREN WESLEY JUNIOR VIII".
  nickname :: String
} deriving (Eq, Read, Show);

-- | State is used to indicate whether a particular character is dead or
-- alive.
data State = Dead | Alive | Win deriving (Eq, Read, Show);

-- | Room is a room.  No shit.
data Room = LivingRoom deriving (Eq, Read, Show);
