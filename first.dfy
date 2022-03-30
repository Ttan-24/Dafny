class CarPark {

    var spacesArr: array<string>;
    var reservedSpacesArr: array<string>;
    var subscriptions: array<string>;

    var spaces: int;
    var spacesUsed: int;
    var reservedSpaces: int;
    var reservedSpacesUsed: int;
    var isWeekday: bool;
    var spaceIndentCount: int;
    var subscriptionsCount: int; 

    // a constructor for the class, setting the car-park up for a new day
    constructor(aSpaces: int, aReservedSpaces: int, aDay: int) 
    requires aReservedSpaces >= 0
    requires aSpaces >= 0
    ensures fresh(subscriptions)
    ensures fresh(spacesArr)
    ensures fresh(reservedSpacesArr)
    {
        /*
        Preconditions:
        - newday is not negative
        - newday is less than 7
        */
        spaceIndentCount := 8; 
        subscriptionsCount := 0;
        
        // Regular spaces
		spaces := aSpaces;
		spacesUsed := 0;

        // Reserves spaces
        reservedSpaces := aReservedSpaces;
        reservedSpacesUsed := 0;

        assert  aReservedSpaces >= 0;
        // Subscriptions
        subscriptions := new string[aReservedSpaces];

        
        assert  aSpaces >= 0;
        // Array
		spacesArr := new string[aSpaces];
        reservedSpacesArr := new string[aSpaces];

        //Weekday
        
        new ; 
        isWeekday := setIsWeekday(aDay);
    }


    method setIsWeekday(day: int) returns (result: bool)
	{
		if (day <= 4)
		{
			result := true;
		}
		else
		{
			result := false;
		}
	}

    method checkAvailability() returns (result: int)
	{
	    if (isWeekday)
        {
            result := (spaces - reservedSpaces);
        }
        else
        {
            result := ((spaces + reservedSpaces) - (spacesUsed + reservedSpacesUsed));
        }
	}

    method AddCar(aCar: string)  
    requires spacesArr.Length > 0
    modifies spacesArr
	{
        var i: int := 0;
        while (i < spacesArr.Length)
        invariant 0 <= i <= spacesArr.Length 
    
        decreases spacesArr.Length - i
        {
            if (spacesArr[i] == "") {
                print("Adding " + aCar + "\n");
                spacesArr[i] := aCar;
                break;
            }
            i := i + 1;
        }
	}

    method RemoveCar(aCar: string)  
    requires spacesArr.Length > 0
    modifies spacesArr
	{
        var i: int := 0;
        while (i < spacesArr.Length)
        invariant 0 <= i <= spacesArr.Length 
    
        decreases spacesArr.Length - i
        {
            if (spacesArr[i] == aCar) {
                print("Removing " + aCar + "\n");
                spacesArr[i] := "";
                break;
            }
            i := i + 1;
        }
	}

    method AddCarReserved(aCar: string)
    modifies subscriptions
    modifies reservedSpacesArr
    {
        // Stop if not reserved
        var i: int := 0;
        var subscriptionFound: bool := false;
        while (i < subscriptions.Length)
        decreases subscriptions.Length - i
        {
            if (subscriptions[i] == aCar)
            {
                subscriptionFound := true;
            }
            i := i + 1;
        }

        if (subscriptionFound == false)
        {
            print("Could not add " + aCar + " to reserved carpark because it did not have a subscription \n");
        }
        else
        {
            // Otherwise search for space
            var i: int := 0;
            while (i < reservedSpacesArr.Length) 
            decreases reservedSpacesArr.Length - i
            {
                if (reservedSpacesArr[i] == "")
                {
                    print("Adding " + aCar + " to reserved carpark \n");
                    reservedSpacesArr[i] := aCar;
                    //reservedSpacesUsed := reservedSpacesUsed + 1;
                    break;
                }
                i := i + 1;
            }
        }
    }

    method CreateSubscription(aCar: string)
    modifies subscriptions 
	{
        var i: int := 0;
        while (i < subscriptions.Length) 
        decreases subscriptions.Length - i
        {
            if (subscriptions[i] == "") {
                print("Create subscription \n");
                subscriptions[i] := aCar;
                break;
            }
            i := i + 1;
        }
        // subscriptions[subscriptionsCount] := aCar;
        // subscriptionsCount := subscriptionsCount + 1;
	}

    // to allow any car without a reservation to enter the car park.
    method enterCarPark(hasReservation: bool, IsFull: bool, car: int, carCount: int) 
    //requires IsFull(CarParkSpaces)
    //ensures day > 0 || day <= 0
    {
        /*
        Preconditions:
        - hasreservation should be false
        - is not full
        - carCount should not be negative
        - carCount should not be bigger than spaces available
        - car int should not be negative
        */

    }

    // to allow any car from any area to leave the car park
    method leaveCarPark(car: int, carCount: int)
    {
        /*
        Preconditions:
        - car should not be negative
        - carCount should not be negative
        */
    }

    // to report on the number of non-reserved free spaces currently available.
    //method checkAvailability(carCount: int, isWeekend: bool) returns (numberOfNonReservedFreeSpaces: int)
    //{
        /*
        Preconditions:
        - carCount should not be negative

        Postconditions:
        - numberOfNonReservedFreeSpaces should not be greater than total spaces
        */
    //}

    // to allow a car with a subscription to enter the car park’s reserved area on a
    // weekday, or to enter the car park generally on a weekend day
    method enterReservedCarPark(hasReservation: bool, isWeekend: bool, isFull: bool) 
    {
        /*
        Preconditions:
        - is a weekday ==> hasreservation should be true
        - should not be full

        Postconditions:
        - 
        */
    }

    // to allow a car to be registered as having a reserved space when the owner
    // pays the subscription – as long as subscriptions are available.
    method makeSubscription(car: int, IsSubscriptionAvailable: bool) 
    {
        /*
        Preconditions:
        - Car should not be negative
        - IsSubscriptionAvailable true then only hasReservation true

        Postconditions:
        - 
        */
    }

    // to remove parking restrictions on the reserved spaces (at the weekend)
    method openReservedArea(week: int, hasReservation: bool) 
    {
        /*
        Preconditions:
        - week should not be negative
        - hasReservation is false if week is a weekend

        Postconditions:
        - 
        */
    }

    // to remove and crush remaining parked cars at closing time.
    method closeCarPark(time: int, car: int, carCount: int) 
    {
        /*
        Preconditions:
        - time should not be negative
        - time >= 11 then car remove and carCount is subtracted 

        Postconditions:
        - 
        */
    }

    // to display the car park in rows, indicating the state of each space.
    method printParkingPlan()
    {
        /*
        Preconditions:
        - 

        Postconditions:
        - 
        */
    }

    method isFull() returns (result: bool)
    {
        /*
        Preconditions:
        - 

        Postconditions:
        - 
        */
    }

    predicate Even( x : int ) { x % 2 == 0 }

    // predicate IsFull(Array: array<bool>) 
    // { forall element :: 0 < element < Array.Length ==> Array[element] != false }

    method Display()
	{
        //checkAvailability();

        // Spacing
        print("\n");

        // Regular spaces
        print("Regular spaces: " + "\n"); 
		var i := 0;
		while (i < spacesArr.Length)
        //invariant 0 <= i < spaces 
        //invariant forall k :: 0 <= k < i && k < spaces ==> spacesArr[k] != ""
        decreases spacesArr.Length - i
		{
            // Found car
		    if (spacesArr[i] != "") 
            { 
                print(spacesArr[i]); 
            }
          
            // Could not find car
			else 
            { 
                print("........"); 
            }

            // Spacing
            print(" ");
            
            
            if ((i+1) % 8 == 0) 
            {          
                print("\n");
            }
		    i := i + 1;
		}
        print("\n");
        // Reserved spaces
        print("Reserved spaces: " + "\n"); 
		var j := 0;
        while(j < reservedSpacesArr.Length)
		{
            // Found car
			if (reservedSpacesArr[j] != "") 
            {
                print(reservedSpacesArr[j]); 
            }
          
            // Could not find car
			else 
            { 
                print("........"); 
            }

            // Spacing
            print(" ");
            if ((j+1) % 8 == 0) 
            { 
                print("\n"); 
            }
			j := j + 1;
		}

        // Spacing
		print("\n");
        print("\n");
	}
    
}

// Your tests (main program) will tell me to what extent the specification has been met
method Main() {
    /*
    Preconditions:
    - 

    Postconditions:
    - 
    */
     
    var carPark : CarPark;
    carPark :=  new CarPark(10, 10, 3);

    //carPark := new CarPark(10, 10, 3);

    // Display start
	carPark.Display();
    // Display adding cars
    if (carPark.spacesArr.Length > 0) {
        // adding cars in the area
	    carPark.AddCar("S8F2HD8Q");
	    carPark.AddCar("BBBBBBBB");
	    carPark.AddCar("CCCCCCCC");
        carPark.Display();

        // removing a car from the area
        carPark.RemoveCar("BBBBBBBB");
        carPark.Display();
        
        // added car and created a subscription for it. This car should be in the reserved area
        carPark.CreateSubscription("AJSKFKDK");
        carPark.AddCarReserved("AJSKFKDK");
        
        // added a reserved car
        carPark.AddCarReserved("SSSSSSCCC");
        carPark.Display();
    }
}





