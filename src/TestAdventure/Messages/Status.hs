module TestAdventure.Messages.Status where

-- | lrTableCrush is output to the terminal if the flimsy-looking living
-- room table is demolished.
lrTableCrush :: String;
lrTableCrush = "Shouting loudly, you smash the flimsy-looking table a la WWE.\nFragments of the table now litter the room which was once somewhat clean.";

-- | lrTableCrushed is output to the terminal if the player attempts to
-- smash the flimsy-looking living room table... after having already
-- smashed the living room table.
lrTableCrushed :: String;
lrTableCrushed = "You already smashed the table some time ago.  Hell, the thing is still smoking.\nRegardless of this fact, you shout and attempt to smash the deris.  Determijning whether or not this attempt is successful is left as an exercise for the reader.";

-- | travelSuccess is output if the player character successfully
-- travels to a player-specified destination.
travelSuccess :: String;
travelSuccess = "You travel successfully.";
