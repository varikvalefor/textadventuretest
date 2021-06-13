module TestAdventure.Messages.Error where

-- | invalidRoom is output if the player attempts to enter a nonexistent
-- room.
invalidRoom :: String;
invalidRoom = "You attempt to enter the specified room but quickly realise that the room in question does not actually exist.\nAfter sitting down and pondering potential other lies for a few moments, you regain what little sense you have and are again ready to do stuff.";

travelCurRoom :: String;
travelCurRoom = "Damn, that's some fast travel.  You're already there!";

invalidFlipObject :: String;
invalidFlipObject = "You cannot flip objects which do not exist.";
