encounteredBadWeather(truck1).
encounteredBadTraffic(truck1).

hasViolationJustification(Truck) :- encounteredBadWeather(Truck); encounteredBadTraffic(Truck).

hasExpectedRoute(truck1, r1).
hasActualRoute(truck1, r2).

hasExpectedArrivalTime(truck1, t1).
hasActualArrivalTime(truck1, t2).

hasRouteViolation(Truck) :- hasExpectedRoute(Truck, ERoute), hasActualRoute(Truck, ARoute), not(ERoute = ARoute).
hasTimeViolation(Truck) :- hasExpectedArrivalTime(Truck, ETime), hasActualArrivalTime(Truck, ATime), not(ETime = ATime).

hasViolation(Truck) :- hasTimeViolation(Truck); hasRouteViolation(Truck).

isSafe(Truck) :- hasViolation(Truck), hasViolationJustification(Truck).
