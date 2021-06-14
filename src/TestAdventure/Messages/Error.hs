module TestAdventure.Messages.Error where

-- | invalidRoom is output if the player attempts to enter a nonexistent
-- room.
invalidRoom :: String;
invalidRoom = "You attempt to enter the specified room but quickly realise that the room in question does not actually exist.\nAfter sitting down and pondering potential other lies for a few moments, you regain what little sense you have and are again ready to do stuff.";

-- | travelCurRoom is output to the terminal if the player attempts to
-- enter the room which the player character currently occupies.
travelCurRoom :: String;
travelCurRoom = "Damn, that's some fast travel.  You're already there!";

-- | invalidFlipObject is output if the player attempts to flip an
-- object which is not recognised as being flippable.
invalidFlipObject :: String;
invalidFlipObject = "You cannot flip objects which do not exist.";

-- | lrTableDebrisAlreadyJunked is output if the player attempts to junk
-- the debris of the table whilst such debris is stored in the bin.
lrTableDebrisAlreadyJunked :: String;
lrTableDebrisAlreadyJunked = "You already junked the remains of the table.\nYou CAN retrieve the table's remains if you so desire.";

-- | lrDebrisNotBroken is output if the table is reduced to debris
-- without actually being broken.  lrDebrisNotBroken is a "true" error
-- message.
lrDebrisNotBroken :: String;
lrDebrisNotBroken = "The table is somehow reduced to a pile of garbage without actually being broken.  Determining the process which is used to modify the table as described is left as an exercise for the reader.";

-- | lrTableNotJunk is output if the player attempts to junk the
-- non-broken living room table.
lrTableNotJunk :: String;
lrTableNotJunk = "Why in God's name would you junk a perfectly good -- actually a bit cheesy -- actually very cheesy, but still functional -- table?!  The thing still at least somewhat works, although slightly nudging the table can lead to spilled coffee.";
