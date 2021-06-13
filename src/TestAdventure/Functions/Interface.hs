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
listSurroundings k =
  putStrLn "You stand in the middle of a dingy living room." >>
  putStrLn "In front of you is a flimsy-looking card table." >>
  return k;
