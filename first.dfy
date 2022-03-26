class CarPark {
    // a constructor for the class, setting the car-park up for a new day
    constructor(newDay: string) 
    {

    }

    // to allow any car without a reservation to enter the car park.
    method enterCarPark(hasReservation: bool, IsFull: bool, car: int, countCar: int) 
    {

    }

    // to allow any car from any area to leave the car park
    method leaveCarPark(car: int, countCar: int)
    {

    }

    // to report on the number of non-reserved free spaces currently available.
    method checkAvailability(countCar: int) returns (numberOfNonReservedFreeSpaces: int)
    {

    }

    // to allow a car with a subscription to enter the car park’s reserved area on a
    // weekday, or to enter the car park generally on a weekend day
    method enterReservedCarPark(hasReservation: bool, week: int) 
    {

    }

    // to allow a car to be registered as having a reserved space when the owner
    // pays the subscription – as long as subscriptions are available.
    method makeSubscription(car: int) 
    {

    }

    // to remove parking restrictions on the reserved spaces (at the weekend)
    method openReservedArea(week: int, hasReservation: bool) 
    {

    }

    // to remove and crush remaining parked cars at closing time.
    method closeCarPark(time: int, car: int, countCar: int) 
    {

    }

    // to display the car park in rows, indicating the state of each space.
    method printParkingPlan()
    {

    }

    // Your tests (main program) will tell me to what extent the specification has been met
    method Main() {

    }
}





