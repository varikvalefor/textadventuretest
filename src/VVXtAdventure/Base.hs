module VVXtAdventure.Base where
-- | 'GameData' contains game data, e.g., the player's name, the
-- contents of the player's inventory, whether or not a question
-- is currently asked, and whether or not the player is become a corpse.
data GameData = GameData {
  -- | @playerName k@ equals the name of the player character, NOT the
  -- name of the player, of @k@.
  playerName :: CharName,
  -- | @playerName k@ equals the contents of the inventory of the player
  -- character of @k@.
  --
  -- The order of @inventory@ is arbitrary.
  inventory :: [Item],
  -- | @questionYNExists k@ iff a question is currently asked such that
  -- the player responds.
  questionYNExists :: Bool,
  -- | @secretWordNums k@ denotes the number of occurrences of the
  -- secret word, which is generally actually a secret phrase, but
  --- whatever.
  secretWordNums :: Integer,
  -- | @status k@ equals the status of the player character of @k@.
  -- @status k == Alive@ iff the player character of k is alive.
  -- @status k == Dead@ iff the player character of k is
  -- dead.
  status :: State,
  -- | To what extent is the living room table smashed up?
  --
  -- This value is incremented by one (1) whenever the living room
  -- table is smashed.
  lrTableSmashedness :: Integer,
  -- | Is the table in the living room flipped upside-down?
  lrTableFlipped :: Bool,
  -- | Is any debris of the living room table on the floor of the
  -- living room?
  lrTableDebrisPresent :: Bool,
  -- | What is the player character's current location?
  currentRoom :: Room,
  -- | How smashed is the mop?
  --
  -- This value equals the number of smashings which the mop has
  -- received.
  mopSmashedness :: Integer,
  -- | How smashed is the broom?
  --
  -- This value equals the number of smashings which the broom has
  -- received.
  broomSmashedness :: Integer,
  -- | What, if anything, is the player holding?
  wieldedWeapon :: Maybe Item
} deriving (Eq, Read, Show);

-- | For all Item k, k is an inventory item of some sort.
data Item = Item {
  -- | For all 'Item' k, itemName k equals the human-readable name of
  -- k, e.g., "a broken toilet".
  itemName :: String,
  -- | For all 'Item' k, @isWeapon k@ iff k is a weapon.
  isWeapon :: Bool
} deriving (Eq, Read, Show);

-- | For all 'CharName' @k@, @k@ is the name of a character.
data CharName = CharName {
  -- | @forename k@ is the forename of a character, e.g., "SPINACH".
  forename :: String,
  -- | @surname k@ is the surname of a character, e.g., "GRAVYBOAT".
  surname :: String,
  -- | @nickname k@ is the nickname of a character, e.g., "WARREN WESLEY
  -- JUNIOR VIII".
  nickname :: String
} deriving (Eq, Read, Show);

-- | 'State' is used to indicate whether a particular character is dead
-- or alive.
data State = Dead | Alive | Win deriving (Eq, Read, Show);

-- | 'Room' represents a room.  No shit.
data Room = LivingRoom
          -- ^ This thing represents the living room in which the game
          -- begins.
          | BroomCloset
          -- ^ This thing represents the broom closet which is
          -- accessible from the living room in wich the game begins.
          deriving (Eq, Read, Show);
