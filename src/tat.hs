import Data.Char (toUpper);
import VVXtAdventure.Base;
import TestAdventure.ConditionChecks;
import Data.List (intersperse);
import qualified TestAdventure.Messages.Death as MD;
import qualified TestAdventure.Messages.Status as MS;
import qualified TestAdventure.Messages.Error as ME;
import TestAdventure.Functions.Interface;
import TestAdventure.Functions.Action;

-- | defChar is the default game data.
defChar :: GameData;
defChar = GameData {
  playerName = CharName {
    forename = "HARRIETT",
    surname  = "TUBMAN",
    nickname = "THE O.G. MEATBALL"
  },
  inventory = [Item {itemName = "shitty-ass stick"}],
  questionYNExists = False,
  secretWordNums = 0,
  status = Alive,
  currentRoom = LivingRoom,
  lrTableSmashed = False,
  lrTableFlipped = False
};

main :: IO ();
main = introducePlayer defChar >>= getAndParseCommand >>= chooseCont;

-- | For all 'GameData' k, introducePlayer k prints a short description
-- of k to the terminal.
introducePlayer :: GameData -> IO GameData;
introducePlayer k =
  putStrLn ("You are " ++ (forename . playerName) k ++ " " ++ (surname . playerName) k ++ ", a.k.a. " ++ (nickname . playerName) k ++ ".") >>
  return k;

-- | chooseCont determines whether or not the game should continue,
-- based upon the status of the player character.
chooseCont :: GameData -> IO ();
chooseCont k
  | status k == Dead = putStrLn "Aw, you dead."
  | status k == Win = putStrLn MD.winMsg
  | otherwise = getAndParseCommand k >>= chooseCont;

-- | getAndParseCommand retrieves a command from the user and executes
-- or rejects this command, depending upon whether or not the command is
-- recognised as being an acceptable command.
getAndParseCommand :: GameData -> IO GameData;
getAndParseCommand godDamn =
  putStrLn "What do you do?" >> getLine >>= parseCommand
  where
  parseCommand :: String -> IO GameData
  parseCommand l
    | isGo k = travel k godDamn
    | isSuicide k = putStrLn MD.spontComb >> return godDamn {status = Dead}
    | isAffirmative k && (not . questionYNExists) godDamn =
      putStrLn MD.answerAff >> return godDamn {status = Win}
    | isSecretWord k = secretWordProcedure godDamn
    | isCheckBag k = listInventory godDamn
    | isObsSurround k = listSurroundings godDamn
    | isDemolish k = crush godDamn k
    | isFlip k = flipObj godDamn k
    | otherwise = putStrLn "Eh?" >> return godDamn
    where
    k = foldr (++) [] $ intersperse " " $ filter (not . (`elem` ["TO", "THE", "A", "AN"])) $ words l

-- | secretWordProcedure contains the stuff which should be done iff the
-- secret word is entered.
secretWordProcedure :: GameData -> IO GameData;
secretWordProcedure gd
  | time 0 = putStrLn "Eh?" >> increment
  | time 1 = putStrLn "Do it again, and it's harassment." >> increment
  | time 2 = putStrLn "I'm warning you, motherfucker." >> increment
  | time 3 = putStrLn "Run with the money, I pull the trigger and damage you.  Kaboom." >> return (killPlayer gd)
  | otherwise = error "Aw, shit.  An error occurs.  secretWordNums is of some invalid value!"
  where
  increment :: IO GameData
  increment = return $ gd {secretWordNums = secretWordNums gd + 1}
  --
  time :: Integer -> Bool
  time = (secretWordNums gd ==);

-- | For all 'GameData' k, killPlayer k equals a version of k which is
-- modified such that the player of k is dead.
killPlayer :: GameData -> GameData;
killPlayer k = k {status = Dead};
