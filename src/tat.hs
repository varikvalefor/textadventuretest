import Data.Char (toUpper);
import VVXtAdventure.Base;

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
  status = Alive
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
    | isSuicide k = putStrLn ("You spontaneously combust, " ++
      "thereby losing the game and making yourself look like a bit " ++
      "of a jack-ass in the process.") >> return godDamn
    | isAffirmative k && (not . questionYNExists) godDamn =
      putStrLn ("You answer no one in the affirmative.\nNo one " ++
      "responds with a swift punch to the sternum.\n\"Gah!\"\nYou " ++
      "collapse to the ground, slowly melting into cheese.\nJust " ++
      "before dying, you awaken from your wack-ass dream and " ++
      "remember that you are actually the great BRIAN W. " ++
      "KERNIGHAN.") >> return godDamn
    | isSecretWord k = secretWordProcedure godDamn >>= getAndParseCommand
    | otherwise = putStrLn "Eh?" >> getAndParseCommand godDamn;

-- | For all 'String' k, isSuicide k iff k demands that the player
-- character commits suicide.
isSuicide :: String -> Bool;
isSuicide = (`elem` ["KILL SELF", "SUICIDE", "EXPLODE", "KABOOM", "DIVIDE BY ZERO"]) . map toUpper;

-- | For all 'String' k, isAffirmative k iff k is an affirmative
-- response.
isAffirmative :: String -> Bool;
isAffirmative k = or [k == "YES"];

-- | For all 'String' k, isSecretWord k iff k equals the secret word...
-- technically, the secret phrase.
isSecretWord :: String -> Bool;
isSecretWord = (== "HAM AND SWISS ON RYE");

-- | secretWordProcedure contains the stuff which should be done iff the
-- secret word is entered.
secretWordProcedure :: GameData -> IO GameData;
secretWordProcedure gd
  | secretWordNums gd == 0 = putStrLn "Eh?" >> increment
  | secretWordNums gd == 1 = putStrLn "Do it again, and it's harassment." >> increment
  | secretWordNums gd == 2 = putStrLn "I'm warning you, motherfucker." >> increment
  | secretWordNums gd == 3 = putStrLn "Run with the money, I pull the trigger and damage you.  Kaboom." >> return (killPlayer gd)
  where
  increment :: IO GameData
  increment = return $ gd {secretWordNums = secretWordNums gd + 1};

-- | For all 'GameData' k, killPlayer k equals a version of k which is
-- modified such that the player of k is dead.
killPlayer :: GameData -> GameData;
killPlayer k = k {status = Dead};
