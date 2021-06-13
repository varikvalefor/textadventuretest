module TestAdventure.Messages.Error where

-- | invalidRoom is output if the player attempts to enter a nonexistent
-- room.
invalidRoom :: String;
invalidRoom = "You attempt to enter the specified room but quickly realise that the room in question does not actually exist.\nAfter sitting down and pondering potential other lies for a few moments, you regain what little sense you have and are again ready to do stuff.";

travelCurRoom :: String;
travelCurRoom = "Damn, that's some fast travel.  You're already there!";

invalidFlipObject :: String;
invalidFlipObject = "You cannot flip objects which do not exist.";

lrTableDebrisAlreadyJunked :: String;
lrTableDebrisAlreadyJunked = "You already junked the remains of the table.\nYou CAN retrieve the table's remains if you so desire.";

lrDebrisNotBroken :: String;
lrDebrisNotBroken = "The table is somehow reduced to a pile of garbage without actually being broken.  Determining the process which is used to modify the table as described is left as an exercise for the reader.";

lrTableNotJunk :: String;
lrTableNotJunk = "Why in God's name would you junk a perfectly good -- actually a bit cheesy -- actually very cheesy, but still functional -- table?!  The thing still at least somewhat works, although slightly nudging the table can lead to spilled coffee.";
