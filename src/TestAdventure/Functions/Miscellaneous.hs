module TestAdventure.Functions.Miscellaneous where
import VVXtAdventure.Base;

-- | secretWordProcedure contains the stuff which should be done iff the
-- secret word is entered.
secretWordProcedure :: GameData -> IO GameData;
secretWordProcedure gd = case secretWordNums gd of
  0 -> putStrLn "Eh?" >> increment
  1 -> putStrLn "Do it again, and it's harassment." >> increment
  2 -> putStrLn "I'm warning you, motherfucker." >> increment
  3 -> putStrLn "Run with the money, I pull the trigger and damage you.  Kaboom." >> return gd {status = Dead}
  _ -> error "Aw, shit.  An error occurs.  secretWordNums is of some invalid value!"
  where
  increment :: IO GameData
  increment = return $ gd {secretWordNums = secretWordNums gd + 1};
