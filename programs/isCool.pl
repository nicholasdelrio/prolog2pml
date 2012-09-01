%--- Asserted Facts by someone other than Nick ;-)
isWellKnown(nick).
isWellLiked(nick).
isComputerScientist(nick).

%--- Popularity Rules
isPopular(X) :- isWellKnown(X), isWellLiked(X).
isCool(X) :- isPopular(X); isComputerScientist(X).