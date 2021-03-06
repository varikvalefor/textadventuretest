module VVXtAdventure.RenegadesOfFunc where
import VVXtAdventure.Base;
import Data.Char (toUpper);

-- | listInventory is used to list the contents of the player's
-- inventory.
listInventory :: GameData -> IO ();
listInventory = mapM_ (putStrLn . itemName) . inventory;

-- | For all input commands @k@, @daArgz k@ equals the target of @k@.
daArgz :: String -> String;
daArgz = unwords . tail . filter (not . isJunk) . words . map toUpper
  where
  isJunk :: String -> Bool
  isJunk = flip elem ["TO", "THE", "A", "AN"];

-- | For all input commands @k@, @daComd k@ equals the command-based
-- part of @k@.
daComd :: String -> String;
daComd = head . words . map toUpper;
