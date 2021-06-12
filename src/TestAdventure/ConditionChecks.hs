module TestAdventure.ConditionChecks where
import Data.Char (toUpper);

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

-- | For all 'String' k, isCheckBag k iff k demands that the contents
-- of the player character's inventory are listed.
isCheckBag :: String -> Bool;
isCheckBag k = map toUpper k `elem` ["LIST INVENTORY", "INVENTORY"];

isObsSurround :: String -> Bool;
isObsSurround = (`elem` ["LOOK AROUND YOU"]) . map toUpper;
