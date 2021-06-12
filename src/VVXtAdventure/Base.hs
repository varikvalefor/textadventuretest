module VVXtAdventure.Base where
data GameData = GameData {
  playerName :: CharName,
  inventory :: [Item],
  questionYNExists :: Bool,
  secretWordNums :: Integer,
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
