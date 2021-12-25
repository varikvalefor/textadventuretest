module TestAdventure.Functions.Interface where
import Data.Char (toUpper);
import VVXtAdventure.Base;

-- | listInventory @g@ lists the contents of the player character's
-- inventory, according to @g@.
listInventory :: GameData -> IO GameData;
listInventory gd = putStrLn "You have..." >> listTrinkets >> return gd
  where
  printName = putStrLn . (\(x:xs) -> toUpper x:xs) . itemName
  listTrinkets = mapM_ printName $ inventory gd;

-- | listSurroundings describes the player's environment.
listSurroundings :: GameData -> IO GameData;
listSurroundings k = case currentRoom k of
  LivingRoom  -> listSurroundingsOfLivingRoom k
  BroomCloset -> listSurroundingsOfBroomCloset k
  _           -> putStrLn weirdAssRoom >> return k
  where weirdAssRoom = "Cleverly done, Mr. FREEMAN, but you're  not \
                      \not supposed to be here -- as a matter of \
                      \fact, you're not.  Get back where you belong \
                      \and forget about all this until we meet again."

-- | For all 'GameData' @k@, @listSurroundingsOfLivingRoom k@ prints a
-- description of the living room to the terminal, then outputs @k@.
listSurroundingsOfLivingRoom :: GameData -> IO GameData;
listSurroundingsOfLivingRoom gd = displayCrap >> return gd
  where
  displayCrap :: IO ()
  displayCrap = mapM_ putStrLn ["You stand in the middle of a dingy \
                                \living room.",
                                tableDescription,
                                "North of this dingy living room is \
                                \a broom closet."]
  tableDescription :: String
  tableDescription
    | lrTableSmashedness gd > 1 = "You have smashed up the table such \
                                  \that the table is now all but \
                                  \entirely unrecognisable."
    | lrTableDebrisPresent gd = "In the centre of the room are the \
                                \remains of what probably could have \
                                \been a table... or a chair... or a \
                                \fairly shitty cupboard."
    | lrTableFlipped gd = "In the centre of the room is a table which \
                          \which is flipped upside-down."
    | otherwise = "In the centre of the room is a flimsy-looking table."

-- | @listSurroundingsOfBroomCloset k@ prints a description of the broom
-- closet of @k@ to the terminal, then outputs @k@.
listSurroundingsOfBroomCloset :: GameData -> IO GameData;
listSurroundingsOfBroomCloset gd = describeStuff >> return gd
  where
  describeStuff :: IO ()
  describeStuff = mapM_ putStrLn ["You stand inside of a tiny broom \
                                  \closet.", broomStat, mopStat]
  broomStat :: String
  broomStat
    | broomSmashedness gd == 0 = "To your left is a wooden broom."
    | otherwise = "On the floor are the remains of a wooden broom."
  mopStat :: String
  mopStat
    | mopSmashedness gd == 0 = "To your right is a mop."
    | otherwise = "Strangely, no mop is here.";
