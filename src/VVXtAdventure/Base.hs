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
  status :: State
} deriving (Eq, Read, Show);

data Item = Item {
  itemName :: String
} deriving (Eq, Read, Show);

data CharName = CharName {
  forename :: String,
  surname :: String,
  nickname :: String
} deriving (Eq, Read, Show);

data State = Dead | Alive deriving (Eq, Read, Show);
