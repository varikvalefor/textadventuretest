module TestAdventure.Functions.Interface where
import Data.Char (toUpper);
import VVXtAdventure.Base;

-- | listInventory lists the contents of the player character's
-- inventory.
listInventory :: GameData -> IO GameData;
listInventory gd =
  putStrLn "You have..." >>
  mapM_ (putStrLn . (\(x:xs) -> (toUpper x):xs) . itemName) (inventory gd) >>
  return gd;

-- | listSurroundings describes the player's environment.
listSurroundings :: GameData -> IO GameData;
listSurroundings k
  | currentRoom k == LivingRoom = listSurroundingsOfLivingRoom k
  | currentRoom k == BroomCloset = listSurroundingsOfBroomCloset k
  | otherwise = putStrLn ("Cleverly done, Mr. FREEMAN, but you're " ++
    "not supposed to be here -- as a matter of fact, you're not.  " ++
    "Get back where you belong and forget about all this until we " ++
    "meet again.") >> return k;

listSurroundingsOfLivingRoom :: GameData -> IO GameData;
listSurroundingsOfLivingRoom gd =
  putStrLn "You stand in the middle of a dingy living room." >>
  putStrLn tableDescription >>
  putStrLn "North of this dingy living room is a broom closet." >>
  return gd
  where
  tableDescription :: String
  tableDescription
    | lrTableSmashedness gd > 1 = "In the centre of the room is a " ++
      "smashed-up card table."
    | lrTableDebrisPresent gd = "In the centre of the room are the " ++
      "remains of what probably could have been a table... or a " ++
      "chair... or a fairly shitty cupboard."
    | lrTableFlipped gd = "In the centre of the room is a table " ++
      "which is flipped upside-down."
    | otherwise = "In the centre of the room is a flimsy-looking " ++
      "table."

listSurroundingsOfBroomCloset :: GameData -> IO GameData;
listSurroundingsOfBroomCloset gd =
  putStrLn "You stand inside of a tiny broom closet." >>
  putStr broomStat >>
  putStr mopStat >>
  return gd
  where
  broomStat :: String
  broomStat
    | broomSmashedness gd == 0 = "To your left is a wooden broom.\n"
    | otherwise = "On the floor are the remains of a wooden broom.\n"
  mopStat :: String
  mopStat
    | mopSmashedness gd == 0 = "To your right is a mop.\n"
    | otherwise = "Strangely, no mop is here.\n";
