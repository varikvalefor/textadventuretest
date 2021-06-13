module TestAdventure.Functions.Action where
import VVXtAdventure.Base;
import TestAdventure.ConditionChecks;
import qualified TestAdventure.Messages.Death as MD;
import qualified TestAdventure.Messages.Status as MS;
import qualified TestAdventure.Messages.Error as ME;
import Data.Maybe;
import Text.Read;
import Data.Char (toUpper);

-- | crush is used to smash stuff, e.g., the flimsy-looking table.
-- crush's output is modified such that the destruction is documented.
crush :: GameData
      -> String -- ^ The "SMASH SO-AND-SO" command
      -> IO GameData;
crush y x
  | (k, theRoom) == ("FLIMSY-LOOKING TABLE", LivingRoom) = crushTable
  | otherwise = putStrLn "Eh?" >> return y
  where
  k = unwords $ drop 1 $ words x
  crushTable :: IO GameData
  crushTable
    | lrTableSmashed y = putStrLn MS.lrTableCrushed >> return y
    | otherwise = putStrLn MS.lrTableCrush >>
      return y {lrTableSmashed = True}
  theRoom :: Room
  theRoom = currentRoom y;

-- | travel transports the player character to the specified room
-- or complains about the player's having entered some useless
-- information, where appropriate.
travel :: String -> GameData -> IO GameData;
travel com gd
  | dest' == Nothing = putStrLn ME.invalidRoom >> return gd
  | dest == currentRoom gd = putStrLn ME.travelCurRoom >> return gd
  | otherwise = putStrLn MS.travelSuccess >> return gd {currentRoom = dest}
  where
  dest :: Room
  dest = fromJust dest'
  --
  dest' :: Maybe Room
  dest'
    | inputDest `elem` ["LIVING ROOM", "LIVINGROOM"] = Just LivingRoom
    | otherwise = Nothing
    where inputDest = unwords $ drop 1 $ words $ map toUpper com;

flipObj :: GameData -> String -> IO GameData;
flipObj gd com
  | target == "FLIMSY-LOOKING TABLE" = flipTable gd
  | otherwise = putStrLn ME.invalidFlipObject >> return gd
  where
  target = unwords $ drop 1 $ words com;

flipTable :: GameData -> IO GameData;
flipTable gd
  | lrTableFlipped gd = putStrLn MS.tableFlippedUU >> return flipped
  | otherwise = putStrLn MS.tableFlippedUD >> return flipped
  where
  flipped :: GameData
  flipped = gd {lrTableFlipped = True};
