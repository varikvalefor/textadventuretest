module TestAdventure.Messages.Status where

-- | lrTableCrush is output to the terminal if the flimsy-looking living
-- room table is demolished.
lrTableCrush :: String;
lrTableCrush = "Shouting loudly, you smash the flimsy-looking table a la WWE.\nFragments of the table now litter the living room, which was once somewhat clean.";

-- | lrTableCrushed is output to the terminal if the player attempts to
-- smash the flimsy-looking living room table... after having already
-- smashed the living room table.
lrTableCrushed :: String;
lrTableCrushed = "You already smashed the table some time ago.  Hell, the thing is still smoking.\nRegardless of this fact, you shout and attempt to smash the deris.  Determining whether or not this attempt is successful is left as an exercise for the reader.";

-- | travelSuccess is output if the player character successfully
-- travels to a player-specified destination.
travelSuccess :: String;
travelSuccess = "You travel successfully.";

-- | tableFlippedUD is printed to the terminal if the player character
-- flips the living room table upside-down.
tableFlippedUD :: String;
tableFlippedUD = "You grab the card table and throw the thing into the air.  By sheer coincidence, the table manages to land exactly as the table was a few moments ago, with the exception of being upside-down.";

-- | tableFlippedUU is printed to the terminal if the player character
-- restores the table to the table's original position, i.e., "de-flips"
-- the table.
tableFlippedUU :: String;
tableFlippedUU = "You restore the table to the table's original position, i.e., you \"de-flip\" the table.";

junkLRTableDebris :: String;
junkLRTableDebris = "You successfully place the rubble into the bin.\nBecause the table is shattered into sharp shards, the bin bag tears a bit.";
