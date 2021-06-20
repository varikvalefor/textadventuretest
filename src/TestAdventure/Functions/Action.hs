module TestAdventure.Functions.Action where
import VVXtAdventure.Base;
import VVXtAdventure.RenegadesOfFunc (daArgz);
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
  | (k, theRoom) == ("FLIMSY-LOOKING TABLE", LivingRoom) = crushTable y
  | otherwise = putStrLn "Eh?" >> return y
  where
  k = daArgz x
  --
  theRoom :: Room
  theRoom = currentRoom y

-- | crushTable crushes the table of the living room.
crushTable :: GameData -> IO GameData
crushTable y
  | lrTableSmashedness y > 5 = putStrLn MS.lrTableTotesDestroyed >> return incr
  | lrTableSmashedness y > 0 = putStrLn MS.lrTableCrushed >> return incr
  | otherwise = putStrLn MS.lrTableCrush >> return incr {lrTableDebrisPresent = True}
  where
  incr :: GameData
  incr = y {lrTableSmashedness = lrTableSmashedness y + 1};

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
    where inputDest = daArgz com;

-- | flipObj is used to flip over miscellaneous objects.
flipObj :: GameData -> String -> IO GameData;
flipObj gd com
  | target == "FLIMSY-LOOKING TABLE" = flipTable gd
  | otherwise = putStrLn ME.invalidFlipObject >> return gd
  where
  target = daArgz com;

-- | flipTable flips over the living room table if doing such a thing
-- is actually feasible.
flipTable :: GameData -> IO GameData;
flipTable gd
  | lrTableFlipped gd = putStrLn MS.tableFlippedUU >> return flipped
  | otherwise = putStrLn MS.tableFlippedUD >> return flipped
  where
  flipped :: GameData
  flipped = gd {lrTableFlipped = not $ lrTableFlipped gd};

-- | cleanUp cleans up messes, e.g., the remains of the janky living
-- room table.
cleanUp :: GameData -> String -> IO GameData;
cleanUp gd com
  | target == "DEBRIS" = cleanUpLRTableDebris gd
  | otherwise = putStrLn "The specified thing cannot be cleaned up!" >>
    return gd
  where
  target = daArgz com;

-- | cleanUpLRTableDebris cleans up the remains of the living room table
-- if such a thing is possible.
cleanUpLRTableDebris :: GameData -> IO GameData;
cleanUpLRTableDebris gd
  | tableIsBroken && tableDebrisPresent =
    putStrLn MS.junkLRTableDebris >>
    return gd {lrTableDebrisPresent = False}
  | tableIsBroken =
    putStrLn ME.lrTableDebrisAlreadyJunked >>
    return gd
  | tableDebrisPresent =
    putStrLn ME.lrDebrisNotBroken >>
    return gd
  | otherwise =
    putStrLn ME.lrTableNotJunk >>
    return gd
  where
  tableIsBroken :: Bool
  tableIsBroken = lrTableSmashedness gd /= 0
  --
  tableDebrisPresent :: Bool
  tableDebrisPresent = lrTableDebrisPresent gd;

-- | killSelf is called iff the player character suicides.
killSelf :: GameData
         -> String -- ^ Command used to kill, kill self
         -> IO GameData;
killSelf godDamn strcat =
  putStrLn MD.spontComb >>
  return godDamn {status = Dead};
