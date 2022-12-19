//Model eMall

/*
open util/integer
open util/ordering [DateTime] 

sig DateTime {}
*/

abstract sig User{}

sig ChargingPointOperator extends User{
	managedStations: some ChargingStation
}

sig ElectricVehicleDriver extends User{
 	ownEV: some ElectricVehicle
}

sig ElectricVehicle{
	plug: one Plug, 
	evd: one ElectricVehicleDriver
	//cp: lone ChargingPoint
}

sig ChargingStation {
	chargingPoints: some ChargingPoint
}

sig ChargingPoint {
	plug: some Plug, 
	chargingStation: one ChargingStation
	//ev: lone ElectricVehicle
}

abstract sig Plug{}
one sig Type1 extends Plug{}
one sig Type2 extends Plug{}
one sig Chademo extends Plug{}


/*
fact allChargingPointHavePlugs {
 all cp: ChargingPoint | some p: Plug | p in cp.plugSet
}

fact chargingPointsAreAssociatedWithChargingStations {
 all cs: ChargingStation, cp: ChargingPoint | cp in cs.chargingPointSet iff cs = cp.chargingStation
}

fact evDriverAreAssociatedWithEvs {
 all ev: ElectricVehicle, evd: ElectricVehicleDriver | ev.electricVehicleDriver = evd iff evd.electricVehicle = ev
}

fact evIsConnectedToOnlyOneCharginPoint {
 all ev: ElectricVehicle, cp: ChargingPoint | cp.electricVehicle = ev iff ev.chargingPoint = cp
}

fact evIsConnectedToTheRightPlug {
 all cp: ChargingPoint | some ev: ElectricVehicle | ev in cp.electricVehicle implies ev.plug in cp.plugSet
}
*/

pred show {
}

run show for 3
