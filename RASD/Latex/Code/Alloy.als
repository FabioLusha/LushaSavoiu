open util/ordering[DateTime]

sig DateTime{}

// some actors in the system
abstract sig User {}
sig UnRegEVD extends User {}

sig Email{}
sig Password{}
sig Location{}
sig History{}

sig RegEVD {
	evs: some EV,
    email: one Email, 
	password: one Password,
	chargingHistory: one History
}

sig DSO {}

abstract sig Socket {}
one sig Type1, Type2, Chademo extends Socket{}

sig EV {
	socket: one Socket,
}

//Even he books a socket I think is correct to consider that there are many for each CP, but only one used at the time
sig ChargingPoint {
	//socket: one Socket,
 	socket: some Socket,
	connectedEV: lone EV
}{
	//socket = connectedEV.socket
	EV.socket in socket
	// No dangling ChargingPoint
	// each EV must be in relation with a ChargingStation
	this in ChargingStation.chargingPoints
}

sig ChargingStation {
	chargingPoints: some ChargingPoint,
	location: one Location
}
//this in CPO.chargingStations

sig CPO extends User{
	chargingStations: some ChargingStation
}

sig Booking {
	ev: EV,
	cs: ChargingStation,
	cp: ChargingPoint,
	start: DateTime,
	end: DateTime
}{
	// Only Registerd User can book
	ev in RegEVD.evs &&
	cp in cs.chargingPoints
	lt[start, end]
}

/*********** FACTS  *************/

fact eachChargingToOnlyOneChargingStation{
	all disj x, y : ChargingStation | #(x.chargingPoints & y.chargingPoints) = 0
}

fact eachCStoOnlyOneCPO{
	all disj x, y : CPO | #(x.chargingStations & y.chargingStations) = 0
}

fact eachEVtoOnlyOneEVD {
	all disj x, y : RegEVD | #(x.evs & y.evs) = 0
}

fact eachEVConnectedToOneChargingPoint{
    all disj x, y: ChargingPoint | #(x.connectedEV & y.connectedEV) = 0
}

// impose that there must not exist multiple bookings for the same vehicles at the same time
fact noEVOverBooking{
	no disj b1, b2: Booking
	| b1.ev = b2.ev && 
 		(gte[b1.start, b2.start] && lte[b1.start, b2.end] ||
 		 gte[b1.end, b2.start] && lte[b1.end, b2.end])
}

// impose that there must not exist multiple bookings for the same charging point at the same time
fact noOverBooking{
	no disj b1, b2: Booking
	| b1.cp = b2.cp && 
		(gte[b1.start, b2.start] && lte[b1.start, b2.end] ||
		 gte[b1.end, b2.start] && lte[b1.end, b2.end])
}

//Only an EV can be in charge for EVD
fact onlyAnEVisChargingForEVD{
	all evd: RegEVD, disj ev1, ev2 :EV |
	ev1 in evd.evs and ev2 in evd.evs and ev1 in ChargingPoint.connectedEV
	implies ev2 not in ChargingPoint.connectedEV
}

//Connected email to EVD
fact allEmailConnectedToAnEVD{
 all e: Email | one driver: RegEVD | e = driver.email
}

//Connected EV to EVD
fact allEVConnectedToAnEVD{
 all ev: EV | one evd: RegEVD | ev in evd.evs
}

//Connected password to EVD
fact allPasswordConnectedToAnEVD{
 all p: Password | one driver: RegEVD | p = driver.password
}

//Connected chargingHistory to EVD
fact allChargingHistoryConnectedToAnEVD{
 all h: History | one evd: RegEVD | h = evd.chargingHistory
}

//Connected ChargingStation to CPO
fact allChargingStationToCPO{
 all cs: ChargingStation | one cpo: CPO | cs in cpo.chargingStations
}

//Connected Location to ChargingStation
fact allLocationsConnectedToStations{
 all l: Location | one cs : ChargingStation | l = cs.location
}

//Connected chargingPoint to ChargingStation
fact allChargingPointToAStation{
 all cp: ChargingPoint | one cs: ChargingStation | cp in cs.chargingPoints
}

//Unique email to EVD
fact uniqueEmail{
 no disj driver1, driver2: RegEVD | driver1.email = driver2.email 
}

//Unique history to EVD
fact uniqueHistory{
 no disj driver1, driver2: RegEVD | driver1.chargingHistory = driver2.chargingHistory
}

/**** ASSERTIONS ****/
// The same charging point can't be in two different charging stations
assert noCPinTwoChargingStations{
	no cp: ChargingPoint, disj cs1, cs2: ChargingStation | 
		cp in cs1.chargingPoints && cp in cs2.chargingPoints
}

assert NoCSInTwoCPO{
 no cs: ChargingStation, disj CPO1, CPO2: CPO |
	cs in CPO1.chargingStations && cs in CPO2.chargingStations
}

assert notExsistCPnotInCS{
	no cp: ChargingPoint
	| cp not in ChargingStation.chargingPoints
}

assert exsistEVnotInRegEVD{
	some ev: EV
	| ev not in RegEVD.evs
}

assert noBookingForUnregEVD{
	Booking.ev in RegEVD.evs
}

assert noEVOverBooking{
	no disj b1, b2: Booking |
	b1.ev = b2.ev && gte[b1.start, b2.start] && lte[b1.start, b2.end]
}

assert bookingStartLessThanBookingEnd{
	all b: Booking | lt[b.start, b.end]
}


pred vehiclesCharging {
	some ev: EV, cp: ChargingPoint
	| cp.connectedEV in ev and #(ev.socket) > 2
}

pred bookingForUnregEVD{
	some b: Booking
	| b.ev not in RegEVD.evs
}

pred orederedDates{
	some d1, d2: DateTime | d1 in d2.prev
}

pred findBookings{
	some disj b1, b2: Booking | lt[b2.end, b1.start]
}


// check noCPinTwoChargingStations
// check NoCSInTwoCPO


/*********PREDICATES*********/
pred addEVToEVD[evd', evd: RegEVD, NewEv: EV]{
	evd'.evs = evd.evs + NewEv
}

pred addEVToCS[evd', evd: RegEVD, NewEv: EV]{
	evd'.evs = evd.evs + NewEv
}

pred addCSToCPO[cpo', cpo: CPO, NewCS: ChargingStation]{
    cpo'.chargingStations = cpo.chargingStations + NewCS
}

pred deleteCSFromCPO[cpo', cpo: CPO, cs: ChargingStation]{
    cpo'.chargingStations = cpo.chargingStations - cs
}

pred show {
    #CPO = 3
    #EV = 5
}

// assert a {
// 	not bookingForUnregEVD
// }
// check a

// check noBookingForUnregEVD
//check bookingStartLessThanBookingEnd
// check noEVOverBooking

//  run {} for 10 but exactly 2 Booking
run findBookings for 10

//To show the CPO interaction with the system
pred world1{
	#CPO >= 2
	#ChargingStation >= 3
	#ChargingPoint >= 5
}

run world1 for 20

//To show the RegEVD interaction with the system
pred world2{

}

//To show the UnRegEVD interaction with the system
pred world3{

}

run show for 20
run addEVToEVD

run deleteCSFromCPO

run addCSToCPO