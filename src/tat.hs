import Data.Char (toUpper);
import VVXtAdventure.Base;
import Data.Char (toUpper);
import TestAdventure.ConditionChecks;
import qualified TestAdventure.Messages.Death as MD;
import qualified TestAdventure.Messages.Status as MS;
import qualified TestAdventure.Messages.Error as ME;
import TestAdventure.Functions.Interface;
import TestAdventure.Functions.Action;
import TestAdventure.Functions.Miscellaneous;

-- | @defChar@ is the default game data.
defChar :: GameData;
defChar = GameData {
  playerName = CharName {
    forename = "HARRIET",
    surname  = "TUBMAN",
    nickname = "THE O.G. MEATBALL"
  },
  inventory = [Item {itemName = "shitty-ass stick",
                     isWeapon = True},
               Item {itemName = "repair kit",
                     -- \| Is using a repair kit as a weapon infeasible?
                     -- The contents of this repair kit are not made
                     -- terribly obvious to the player; as such, this
                     -- repair kit may contain a screwdriver... or
                     -- something else which can be used to efficiently
                     -- stab some bitches.
                     isWeapon = False}
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

-- | For all 'GameData' @k@, @introducePlayer k@ prints a short
-- description of @k@ to the standard output.
introducePlayer :: GameData -> IO GameData;
introducePlayer k = putStrLn nameMessage >> return k 
  where
  name :: String
  name = unwords $ map ($ playerName k) [forename, surname]
  alias :: String
  alias = nickname $ playerName k
  nameMessage :: String
  nameMessage = "You are " ++ name ++ ", a.k.a. " ++ alias ++ ".";

-- | @chooseCont@ determines whether or not the game should continue,
-- based upon the status of the player character.
--
-- @chooseCont@ is the main game loop.
chooseCont :: GameData -> IO ();
chooseCont k = maybe readAnotherCommand putStrLn checkForEndMessage
  where
  readAnotherCommand = getAndParseCommand k >>= chooseCont
  checkForEndMessage = case status k of
    Dead -> Just MD.standard
    Win  -> Just MD.winMsg
    _    -> Nothing;

-- | @getAndParseCommand@ retrieves a command from the user and executes
-- or rejects this command, depending upon whether or not the command is
-- recognised as being an acceptable command.
getAndParseCommand :: GameData -> IO GameData;
getAndParseCommand godDamn = prompt >> getLine >>= parseCommand
  where
  prompt :: IO ()
  prompt = putStrLn "What do you do?" >> putStr "$ "
  --
  parseCommand :: String -> IO GameData
  parseCommand l
    | l == [] = putStrLn "The silent treatment won't work here." >>
      return godDamn
    -- \| ACTIONS FOR PLAYER
    | isClean k = cleanUp godDamn k
    | isDemolish k = crush godDamn k
    | isFlip k = flipObj godDamn k
    | isGo k = travel godDamn k
    | isSuicide k = killSelf godDamn k
    | isWieldWeapon k = wieldWeapon godDamn k
    -- \| MISCELLANEOUS
    | isAffirmative k && (not . questionYNExists) godDamn =
      putStrLn MD.answerAff >> return godDamn {status = Win}
    | isSecretWord k = secretWordProcedure godDamn
    -- \| INTERFACE
    | isCheckBag k = listInventory godDamn
    | isObsSurround k = listSurroundings godDamn
    -- \| CATCH-ALL
    | otherwise = putStrLn "Eh?" >> return godDamn
    where
    -- \| @k@ is a version of the player's command which lacks some
    -- @junkwords@.
    k = unwords $ filter (not . (`elem` junkwords)) $ words $ map toUpper l 
    -- \| @junkwords@ is a list of words which can be safely discarded.
    junkwords = ["TO", "THE", "A", "AN"];
