module TestAdventure.Functions.Action.Crush where
import VVXtAdventure.Base;
import VVXtAdventure.RenegadesOfFunc (daArgz);
import TestAdventure.ConditionChecks;
import qualified TestAdventure.Messages.Death as MD;
import qualified TestAdventure.Messages.Status as MS;
import qualified TestAdventure.Messages.Error as ME;
import Data.Maybe;
import Text.Read;
import Data.Char (toUpper);

-- | @table@ crushes the table of the living room.
table :: GameData -> IO GameData
table y
  | lrTableSmashedness y > 5 = putStrLn MS.lrTableTotesDestroyed >> return incr
  | lrTableSmashedness y > 0 = putStrLn MS.lrTableCrushed >> return incr
  | otherwise = putStrLn MS.lrTableCrush >> return incr {lrTableDebrisPresent = True}
  where
  incr :: GameData
  incr = y {lrTableSmashedness = lrTableSmashedness y + 1};

-- | @broom@ is used to BREAK THE BROOM!!!
broom :: GameData -> IO GameData;
broom gd
  | broomSmashedness gd > 0 = putStrLn MS.broomAlreadySmashed >> return gd
  | otherwise = putStrLn MS.broomSmashed >> return gd {broomSmashedness = 1};

-- | @mop@ is used to MUTILATE THE MOP!!!
mop :: GameData -> IO GameData;
mop gd
  | mopSmashedness gd > 0 = putStrLn MS.mopAlreadySmashed >> return gd
  | otherwise = putStrLn MS.mopSmashed >> return gd {mopSmashedness = 1};
