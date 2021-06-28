import Data.Char (toUpper);
import VVXtAdventure.Base;
import TestAdventure.ConditionChecks;
import qualified TestAdventure.Messages.Death as MD;
import qualified TestAdventure.Messages.Status as MS;
import qualified TestAdventure.Messages.Error as ME;
import TestAdventure.Functions.Interface;
import TestAdventure.Functions.Action;
import TestAdventure.Functions.Miscellaneous;

-- | defChar is the default game data.
defChar :: GameData;
defChar = GameData {
  playerName = CharName {
    forename = "HARRIETT",
    surname  = "TUBMAN",
    nickname = "THE O.G. MEATBALL"
  },
  inventory =
    [
      Item {
        itemName = "shitty-ass stick",
        isWeapon = True
      }
    ],
  questionYNExists = False,
  secretWordNums = 0,
  status = Alive,
  currentRoom = LivingRoom,
  lrTableSmashedness = 0,
  lrTableDebrisPresent = False,
  lrTableFlipped = False,
  broomSmashedness = 0,
  mopSmashedness = 0,
  wieldedWeapon = Nothing
};

main :: IO ();
main = introducePlayer defChar >>= getAndParseCommand >>= chooseCont;

-- | For all 'GameData' k, introducePlayer k prints a short description
-- of k to the terminal.
introducePlayer :: GameData -> IO GameData;
introducePlayer k =
  putStrLn ("You are " ++ name ++ ", a.k.a. " ++ alias ++ ".") >>
  return k
  where
  name :: String
  name = (forename $ playerName k) ++ " " ++ (surname $ playerName k)
  alias :: String
  alias = nickname $ playerName k

-- | chooseCont determines whether or not the game should continue,
-- based upon the status of the player character.
chooseCont :: GameData -> IO ();
chooseCont k
  | status k == Dead = putStrLn MD.standard
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
    | l == [] = putStrLn "The silent treatment won't work here." >>
      return godDamn
      -- ACTIONS FOR PLAYER
    | isClean k = cleanUp godDamn k
    | isDemolish k = crush godDamn k
    | isFlip k = flipObj godDamn k
    | isGo k = travel godDamn k
    | isSuicide k = killSelf godDamn k
    | isWieldWeapon k = wieldWeapon godDamn k
    -- MISCELLANEOUS
    | isAffirmative k && (not . questionYNExists) godDamn =
      putStrLn MD.answerAff >> return godDamn {status = Win}
    | isSecretWord k = secretWordProcedure godDamn
    -- INTERFACE
    | isCheckBag k = listInventory godDamn
    | isObsSurround k = listSurroundings godDamn
    -- CATCH-ALL
    | otherwise = putStrLn "Eh?" >> return godDamn
    where
    k = unwords $ filter (not . (`elem` ["TO", "THE", "A", "AN"])) $ words l
