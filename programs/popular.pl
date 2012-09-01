likedByMajority(nick).
hasDieHardFriends(nick).
isGoodLooking(nick).


isWellLiked(X) :- likedByMajority(X) ; hasDieHardFriends(X).
isPopular(X) :- isWellLiked(X) ; isGoodLooking(X).