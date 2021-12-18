module TestAdventure.ConditionChecks where
import Data.List.Split (splitOn);

-- | For all commands @k@, @isSuicide k@ iff @k@ demands that the player
-- character commits suicide.
isSuicide :: String -> Bool;
isSuicide = (`elem` ["KILL SELF", "SUICIDE", "EXPLODE", "KABOOM", "DIVIDE BY ZERO"]);

-- | For all commands @k@, @isAffirmative k@ iff @k@ is an affirmative
-- response.
isAffirmative :: String -> Bool;
isAffirmative k = or [k == "YES"];

-- | For all commands @k@, @isSecretWord k@ iff @k@ equals the secret
-- word... technically, the secret phrase.
isSecretWord :: String -> Bool;
isSecretWord = (== "HAM AND SWISS ON RYE");

-- | For all commands @k@, @isCheckBag k@ iff @k@ demands that the
-- contents of the player character's inventory are listed.
isCheckBag :: String -> Bool;
isCheckBag = (`elem` ["LIST INVENTORY", "INVENTORY"]);

-- | For all commands @k@, @isObsSurround k@ iff @k@ demands that the
-- player character's surroundings are listed.
isObsSurround :: String -> Bool;
isObsSurround = (`elem` ["LOOK AROUND YOU"]);

-- | For all commands @k@, @isDemolish k@ iff @k@ demands that the
-- player character smashes up something.
isDemolish :: String -> Bool;
isDemolish = (`elem` ["SMASH"]) . (!! 0) . splitOn " ";

-- For all commands @k@, @isGo k@ iff @k@ demands that the player moves
-- somewhere.  @k@ need not actually be a followable instruction.
isGo :: String -> Bool;
isGo = (== "GO") . (!! 0) . words;

-- | For all commands @k@, @isFlip k@ iff @k@ demands that the player
- character flips something, e.g., the crappy living room table.
isFlip :: String -> Bool;
isFlip = (== "FLIP") . (!!0) . words;

-- | For all commands @k@, @isClean k@ iff @k@ demands that the player
-- character cleans up some mess, e.g., the debris of the living room
-- table.
isClean :: String -> Bool;
isClean = (== "CLEANUP") . (!! 0) . words;

-- | For all commands @k@, @isWieldWeapon k@ iff @k@ demands that the
-- player character wields some weapon.
isWieldWeapon :: String -> Bool;
isWieldWeapon = (== "WIELD") . head . words;
