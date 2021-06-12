module RenegadesOfFunc where
import VVXtAdventure.Base;

-- | listInventory is used to list the contents of the player's
-- inventory.
listInventory :: GameData -> IO ();
listInventory = mapM_ (putStrLn . itemName) . inventory;
