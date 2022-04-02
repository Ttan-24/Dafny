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
    var extraSpaces: int;

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

        // Extra spaces
        extraSpaces := 5;

        assert  aReservedSpaces >= 0;
        // Subscriptions
        subscriptions := new string[aReservedSpaces];

        
        assert  aSpaces >= 0;
        // Array
		spacesArr := new string[aSpaces];
        reservedSpacesArr := new string[aSpaces];

        //Weekday
        new ; 
        setWeekday(aDay);
    }

    method setWeekday(day: int)
    modifies this
    ensures subscriptions == old(subscriptions)
    ensures spacesArr == old(spacesArr)
    ensures reservedSpacesArr == old(reservedSpacesArr)
	{
		if (day > 4)
		{
			openReservedArea();
		}
	}

    method checkAvailability() returns (result: int)
	{
	    if (isWeekday)
        {
            result := (((spaces) - spacesUsed) - extraSpaces);
        }
        else
        {
            result := (((spaces + reservedSpaces) - (spacesUsed + reservedSpacesUsed)) - extraSpaces);
        }
	}

    method isFull() returns (result: bool)
    {
        var availableSpaces: int;
        availableSpaces := checkAvailability();
        if (availableSpaces <= 0) { result := true; }
        else{ result := false; }
    }

    

    method AddCar(aCar: string)  
    requires spacesArr.Length > 0
    modifies spacesArr
    modifies reservedSpacesArr
    modifies this
    ensures spacesArr.Length > 0
    ensures spacesArr == old(spacesArr)
    ensures reservedSpacesArr == old(reservedSpacesArr)
    ensures subscriptions == old(subscriptions)
	{
        var carparkIsFull:bool;
        carparkIsFull := isFull();
        if (!carparkIsFull)
        {
            // Add in reserved if weekend and regular is full
            if (!isWeekday && spaces == spacesUsed)
            {
                var i: int := 0;
                while (i < reservedSpacesArr.Length)
                invariant 0 <= i <= reservedSpacesArr.Length 
                decreases reservedSpacesArr.Length - i
                {
                    if (reservedSpacesArr[i] == "") {
                        print("Adding " + aCar + " to carpark \n");
                        reservedSpacesArr[i] := aCar;
                        reservedSpacesUsed := reservedSpacesUsed + 1;
                        break;
                    }
                    i := i + 1;
                }
            }
            else // Otherwise add in regular carpark
            {
                var i: int := 0;
                while (i < spacesArr.Length)
                invariant 0 <= i <= spacesArr.Length 
                decreases spacesArr.Length - i
                {
                    if (spacesArr[i] == "") {
                        print("Adding " + aCar + " to carpark \n");
                        spacesArr[i] := aCar;
                        spacesUsed := spacesUsed + 1;
                        break;
                    }
                    i := i + 1;
                }
            }
        }
        else
        {
            print("Carpark is full. Cannot add car with registration number " + aCar + "\n");
        }
	}

    method RemoveCar(aCar: string)  
    requires spacesArr.Length > 0 || reservedSpacesArr.Length > 0
    //requires reservedSpacesArr.Length > 0
    modifies spacesArr
    modifies reservedSpacesArr
    modifies this
    ensures subscriptions == old(subscriptions)
    ensures spacesArr == old(spacesArr)
    ensures reservedSpacesArr == old(reservedSpacesArr)
	{
        // Index
        var i: int := 0;

        // Search in regular spaces
        while (i < spacesArr.Length)
        invariant 0 <= i <= spacesArr.Length 
        decreases spacesArr.Length - i
        {
            if (spacesArr[i] == aCar) {
                print("Removing " + aCar + " from regular carpark \n");
                spacesArr[i] := "";
                spacesUsed := spacesUsed - 1;
                break;
            }
            i := i + 1;
        }

        // Search in reserved spaces
        var j: int := 0;
        while (j < reservedSpacesArr.Length)
        invariant 0 <= j <= reservedSpacesArr.Length 
        decreases reservedSpacesArr.Length - j
        {
            if (reservedSpacesArr[j] == aCar) {
                print("Removing " + aCar + " from reserved carpark \n");
                reservedSpacesArr[j] := "";
                //reservedSpacesUsed := reservedSpacesUsed - 1;
                break;
            }
            j := j + 1;
        }
	}

    method AddCarReserved(aCar: string)
    modifies subscriptions
    modifies reservedSpacesArr
    modifies this
    ensures subscriptions == old(subscriptions)
    ensures spacesArr == old(spacesArr)
    ensures reservedSpacesArr == old(reservedSpacesArr)
    {
        // Stop if full
        var availableSpaces : int;
        availableSpaces := checkAvailability();
        if (availableSpaces <= 0)
        {
            return;
        }

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

        if (subscriptionFound == false && !isWeekday)
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
                    reservedSpacesUsed := reservedSpacesUsed + 1;
                    break;
                }
                i := i + 1;
            }
        }
    }

    method CreateSubscription(aCar: string)
    modifies subscriptions 
    ensures this == old(this)
    ensures subscriptions == old(subscriptions)
	{
        var i: int := 0;
        while (i < subscriptions.Length) 
        decreases subscriptions.Length - i
        {
            if (subscriptions[i] == "") {
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
    method openReservedArea()
    modifies this 
    ensures subscriptions == old(subscriptions)
    ensures spacesArr == old(spacesArr)
    ensures reservedSpacesArr == old(reservedSpacesArr)
    {
        /*
        Preconditions:
        - week should not be negative
        - hasReservation is false if week is a weekend

        Postconditions:
        - 
        */

        isWeekday := false;
    }

    // to remove and crush remaining parked cars at closing time.
    method closeCarPark() 
    modifies spacesArr
    modifies reservedSpacesArr
    {
        /*
        Preconditions:
        - time should not be negative
        - time >= 11 then car remove and carCount is subtracted 

        Postconditions:
        - 
        */

        // Reset all spaces
        var i: int := 0;
        while (i < reservedSpacesArr.Length) 
        decreases reservedSpacesArr.Length - i
        {
            reservedSpacesArr[i] := "";
            i := i + 1;
        }
        i := 0;
        while (i < spacesArr.Length) 
        decreases spacesArr.Length - i
        {
            spacesArr[i] := "";
            i := i + 1;
        }
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

    // predicate IsFull(Array: array<bool>) 
    // { forall element :: 0 < element < Array.Length ==> Array[element] != false }
    predicate Even( x : int ) { x % 2 == 0 }

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
        if (isWeekday)
        {
            print("Reserved spaces: " + "\n"); 
        }
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
    print("--------------------------------------------------- \n");
    print("Program start \n");
    print("--------------------------------------------------- \n");
     
    var carPark : CarPark;
    carPark :=  new CarPark(10, 10, 5);

    //carPark := new CarPark(10, 10, 3);

    // Display start
	carPark.Display();
    // Display adding cars
    if (carPark.spacesArr.Length > 0) {

        // Make subscriptions
        carPark.CreateSubscription("11111111");
        carPark.CreateSubscription("22222222");
        carPark.CreateSubscription("33333333");
        carPark.CreateSubscription("44444444");
        carPark.CreateSubscription("55555555");
        carPark.CreateSubscription("77777777");
        carPark.CreateSubscription("88888888");

        
        //adding cars in the area
	    carPark.AddCar("AAAAAAAA");
	    carPark.AddCar("BBBBBBBB");
	    carPark.AddCar("CCCCCCCC");
        carPark.AddCar("DDDDDDDD");
        carPark.AddCar("EEEEEEEE");
        carPark.AddCar("FFFFFFFF");
        carPark.AddCar("GGGGGGGG");
        carPark.AddCar("HHHHHHHH");
        carPark.AddCar("IIIIIIII");
        carPark.AddCar("JJJJJJJJ");
        carPark.AddCar("KKKKKKKK");
        carPark.AddCar("LLLLLLLL");
        carPark.Display();

        // removing a car from the area
        carPark.RemoveCar("BBBBBBBB");
        carPark.Display();

        // Add subscribed cars
        carPark.AddCarReserved("11111111");
        carPark.AddCarReserved("22222222");
        carPark.AddCarReserved("33333333");
        carPark.AddCarReserved("44444444");
        carPark.AddCarReserved("55555555");
        carPark.AddCarReserved("66666666");
        carPark.AddCarReserved("77777777");
        carPark.AddCarReserved("88888888");
        carPark.Display();
        
        // remove car from the reserved area
        carPark.RemoveCar("11111111");
        carPark.Display();

        // Close carpark
        print("Closing carpark");
        carPark.closeCarPark();
        carPark.Display();
    }
}





