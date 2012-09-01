hasTimeViolation(truck1).
hasRouteViolation(truck1).

hasViolation(Truck) :- hasTimeViolation(Truck); hasRouteViolation(Truck).
