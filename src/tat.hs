import Data.Char (toUpper);
import VVXtAdventure.Base;
import TestAdventure.ConditionChecks;
import Data.List.Split (splitOn);
import Data.List (intersperse);
import qualified TestAdventure.Messages.Death as MD;
import qualified TestAdventure.Messages.Status as MS;

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
  lrTableSmashed = False
};

main :: IO ();
main = introducePlayer defChar >>= getAndParseCommand >> return ();

-- | For all 'GameData' k, introducePlayer k prints a short description
-- of k to the terminal.
introducePlayer :: GameData -> IO GameData;
introducePlayer k =
  putStrLn ("You are " ++ (forename . playerName) k ++ " " ++ (surname . playerName) k ++ ", a.k.a. " ++ (nickname . playerName) k ++ ".") >>
  return k;

-- | getAndParseCommand retrieves a command from the user and executes
-- or rejects this command, depending upon whether or not the command is
-- recognised as being an acceptable command.
getAndParseCommand :: GameData -> IO GameData;
getAndParseCommand godDamn
  | status godDamn == Dead = putStrLn "Aw, you dead." >> return godDamn
  | True = putStrLn "What do you do?" >> getLine >>= parseCommand
  where
  parseCommand :: String -> IO GameData
  parseCommand k
    | isSuicide k = putStrLn MD.spontComb >> return godDamn
    | isAffirmative k && (not . questionYNExists) godDamn =
      putStrLn MD.answerAff >> return godDamn
    | isSecretWord k = secretWordProcedure godDamn >>= getAndParseCommand
    | isCheckBag k = listInventory godDamn >>= getAndParseCommand
    | isObsSurround k = listSurroundings godDamn >>= getAndParseCommand
    | isDemolish k = crush godDamn k >>= getAndParseCommand
    | otherwise = putStrLn "Eh?" >> getAndParseCommand godDamn;

-- | secretWordProcedure contains the stuff which should be done iff the
-- secret word is entered.
secretWordProcedure :: GameData -> IO GameData;
secretWordProcedure gd
  | secretWordNums gd == 0 = putStrLn "Eh?" >> increment
  | secretWordNums gd == 1 = putStrLn "Do it again, and it's harassment." >> increment
  | secretWordNums gd == 2 = putStrLn "I'm warning you, motherfucker." >> increment
  | secretWordNums gd == 3 = putStrLn "Run with the money, I pull the trigger and damage you.  Kaboom." >> return (killPlayer gd)
  | otherwise = error "Aw, shit.  An error occurs.  secretWordNums is of some invalid value!"
  where
  increment :: IO GameData
  increment = return $ gd {secretWordNums = secretWordNums gd + 1};

-- | For all 'GameData' k, killPlayer k equals a version of k which is
-- modified such that the player of k is dead.
killPlayer :: GameData -> GameData;
killPlayer k = k {status = Dead};

-- | listInventory lists the contents of the player character's
-- inventory.
listInventory :: GameData -> IO GameData;
listInventory gd =
  putStrLn "You have..." >>
  mapM_ (putStrLn . (\(x:xs) -> (toUpper x):xs) . itemName) (inventory gd) >>
  return gd;

listSurroundings :: GameData -> IO GameData;
listSurroundings k =
  putStrLn "You stand in the middle of a dingy living room." >>
  putStrLn "In front of you is a flimsy-looking card table." >>
  return k;

-- | crush is used to smash stuff, e.g., the flimsy-looking table.
-- crush's output is modified such that the destruction is documented.
crush :: GameData
      -> String -- ^ The "SMASH SO-AND-SO" command
      -> IO GameData;
crush y x
  | (k, theRoom) == ("FLIMSY-LOOKING TABLE", LivingRoom) = crushTable
  | otherwise = putStrLn "Eh?" >> return y
  where
  k = foldr (++) [] $ intersperse " " $ drop 1 $ splitOn " " x
  crushTable :: IO GameData
  crushTable
    | lrTableSmashed y = putStrLn MS.lrTableCrushed >> return y
    | otherwise = putStrLn MS.lrTableCrush >>
      return y {lrTableSmashed = True}
  theRoom :: Room
  theRoom = currentRoom y;
