operatesOn(s1,format-a).
operatesOn(s2,format-b).
operatesOn(s3,format-c).
operatesOn(s4,format-d).

transformsTo(s1,format-b).
transformsTo(s2,format-c).
transformsTo(s3,format-d).
transformsTo(s4,format-e).

mapsTo(s3,contour-lines).

canBeTransformedToDirectly(A,B) :- operatesOn(S,A), transformsTo(S,B).

canBeTransformedTo(A,B) :- canBeTransformedToDirectly(A,B), !.
canBeTransformedTo(A,B) :- canBeTransformedToDirectly(A, I), canBeTransformedTo(I,B).