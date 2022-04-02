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
    var subscriptionsCountMax: int; 
    var extraSpaces: int;

    // a constructor for the class, setting the car-park up for a new day
    constructor(aSpaces: int, aReservedSpaces: int, aDay: int) 
    requires aReservedSpaces >= 0
    requires aSpaces >= 0
    requires aDay >= 0 && aDay <= 6
    ensures fresh(subscriptions)
    ensures fresh(spacesArr)
    ensures fresh(reservedSpacesArr)
    //ensures subscriptionsCount <= subscriptionsCountMax
    {
        /*
        Preconditions:
        - newday is not negative
        - newday is less than 7
        */
        spaceIndentCount := 8; 
        subscriptionsCount := 0;
        subscriptionsCountMax := aReservedSpaces;
        
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

    // predicate Valid()
    // reads this;
    // {
    //     // Ensures subscriptions do not exceed their maximum from the constructor argument
    //     //subscriptionsCount <= subscriptionsCountMax

    //     // Ensures the spaces used to not exceed the max spaces
    //     //spacesUsed < spaces
    //     //reservedSpacesUsed < reservedSpaces

    //     // Ensure the size of each license plate is 0 or 8
    //     //(forall i: int :: 0 <= i < spacesArr.Length ==> |spacesArr[i]| == 8 || |spacesArr[i]| == 0) &&
    //     //(forall k: int :: 0 <= k < reservedSpacesArr.Length ==> |reservedSpacesArr[k]| == 8 || |reservedSpacesArr[k]| == 0)
    // }

    method setWeekday(day: int)
    modifies this
    requires day >= 0 && day <= 6
    ensures subscriptions == old(subscriptions)
    ensures spacesArr == old(spacesArr)
    ensures reservedSpacesArr == old(reservedSpacesArr)
    //ensures subscriptionsCount <= subscriptionsCountMax
	{
        isWeekday := true;
		if (day > 4)
		{
			openReservedArea();
		}
	}

    // to report on the number of non-reserved free spaces currently available.
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

    
    //to allow any car without a reservation to enter the car park
    method enterCarPark(aCar: string)  
    requires spacesArr.Length >= 0
    modifies spacesArr
    modifies reservedSpacesArr
    modifies this
    ensures spacesArr.Length >= 0
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

    //to allow any car from any area to leave the car park
    method leaveCarPark(aCar: string)  
    requires spacesArr.Length >= 0 || reservedSpacesArr.Length >= 0
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

    // to allow a car with a subscription to enter the car park’s reserved area on a
    // weekday, or to enter the car park generally on a weekend day
    method enterReservedCarPark(aCar: string)
    modifies subscriptions
    modifies reservedSpacesArr
    modifies this
    ensures subscriptions == old(subscriptions)
    ensures spacesArr == old(spacesArr)
    ensures reservedSpacesArr == old(reservedSpacesArr)
    {
        // Check for subscription
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

        // return if subscription not found and is weekday
        if (subscriptionFound == false && isWeekday)
        {
            print("Could not add " + aCar + " to reserved carpark because it did not have a subscription \n");
            return;
        }
        
        // Stop if full
        var availableSpaces : int;
        availableSpaces := checkAvailability();
        if (availableSpaces <= 0)
        {
            print("Carpark is full");
            return;
        }
        else // Otherwise search for space
        {
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

    // to allow a car to be registered as having a reserved space when the owner
    // pays the subscription – as long as subscriptions are available.
    method makeSubscription(aCar: string)
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

    // to remove parking restrictions on the reserved spaces (at the weekend)
    method openReservedArea()
    modifies this 
    ensures subscriptions == old(subscriptions)
    ensures spacesArr == old(spacesArr)
    ensures reservedSpacesArr == old(reservedSpacesArr)
    //ensures subscriptionsCount <= subscriptionsCountMax
    {
         isWeekday := false;
    }

    // to remove and crush remaining parked cars at closing time.
    method closeCarPark() 
    modifies spacesArr
    modifies reservedSpacesArr
    {
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
    
    print("--------------------------------------------------- \n");
    print("Program start \n");
    print("--------------------------------------------------- \n");
     

    print("--------------------------------------------------- \n");
    print("WEEKENDS \n");
    print("--------------------------------------------------- \n");
    var carPark : CarPark;

    // setting it to weekend
    carPark :=  new CarPark(10, 10, 5);

    // Display start
	carPark.printParkingPlan();
    // Display adding cars
    if (carPark.spacesArr.Length > 0) {

        // Make subscriptions
        carPark.makeSubscription("11111111");
        carPark.makeSubscription("22222222");
        carPark.makeSubscription("33333333");
        carPark.makeSubscription("44444444");
        carPark.makeSubscription("55555555");
        carPark.makeSubscription("77777777");
        carPark.makeSubscription("88888888");

        
        //adding cars in the area
        print ("Demo: Adding cars in the area");
	    carPark.enterCarPark("AAAAAAAA");
	    carPark.enterCarPark("BBBBBBBB");
	    carPark.enterCarPark("CCCCCCCC");
        carPark.enterCarPark("DDDDDDDD");
        carPark.enterCarPark("EEEEEEEE");
        carPark.enterCarPark("FFFFFFFF");
        carPark.enterCarPark("GGGGGGGG");
        carPark.enterCarPark("HHHHHHHH");
        carPark.enterCarPark("IIIIIIII");
        carPark.enterCarPark("JJJJJJJJ");
        carPark.enterCarPark("KKKKKKKK");
        carPark.enterCarPark("LLLLLLLL");
        carPark.printParkingPlan();

        // removing a car from the area
        print ("Demo: Removing cars from the area");
        carPark.leaveCarPark("BBBBBBBB");
        carPark.printParkingPlan();

        // Add subscribed cars
        print ("Demo: Added reserved cars in the reserved area");
        carPark.enterReservedCarPark("11111111");
        carPark.enterReservedCarPark("22222222");
        carPark.printParkingPlan();
        
        // remove car from the reserved area
        print ("Demo: Remove reserved cars in the reserved area");
        carPark.leaveCarPark("11111111");
        carPark.printParkingPlan();

        // attempting to add a non reserved car in a reserved space in a weekend
        print ("Demo: Attempting to add a non reserved car in a reserved space in a weekend");
        carPark.enterReservedCarPark("NNNNNNNN");
        carPark.printParkingPlan();

        // should leave 5 remaining space 
        print ("Demo: Checking if it leaves 5 remaining spaces");
        carPark.enterReservedCarPark("33333333");
        carPark.enterReservedCarPark("44444444");
        carPark.enterReservedCarPark("55555555");
        carPark.enterReservedCarPark("66666666");
        carPark.enterReservedCarPark("77777777");
        carPark.enterReservedCarPark("88888888");
        carPark.printParkingPlan();

        // Close carpark
        print ("Demo: Checking if it removes all cars when it closes the carpark");
        print("Closing carpark");
        carPark.closeCarPark();
        carPark.printParkingPlan();
    }


    print("--------------------------------------------------- \n");
    print("WEEK DAYS \n");
    print("--------------------------------------------------- \n");
    
    // setting it to weekday
    carPark.setWeekday(3);

    carPark :=  new CarPark(10, 10, 3);

    // Display start
	carPark.printParkingPlan();
    // Display adding cars
    if (carPark.spacesArr.Length > 0) {

        // Make subscriptions
        carPark.makeSubscription("11111111");
        carPark.makeSubscription("22222222");
        carPark.makeSubscription("33333333");
        carPark.makeSubscription("44444444");
        carPark.makeSubscription("55555555");
        carPark.makeSubscription("77777777");
        carPark.makeSubscription("88888888");

        
        //adding cars in the area
        print ("Demo: Adding cars in non reserved area and checking if it leaves 5 remaining spaces in a weekday");
	    carPark.enterCarPark("AAAAAAAA");
	    carPark.enterCarPark("BBBBBBBB");
	    carPark.enterCarPark("CCCCCCCC");
        carPark.enterCarPark("DDDDDDDD");
        carPark.enterCarPark("EEEEEEEE");
        carPark.enterCarPark("FFFFFFFF");
        carPark.enterCarPark("GGGGGGGG");
        carPark.enterCarPark("HHHHHHHH");
        carPark.enterCarPark("IIIIIIII");
        carPark.enterCarPark("JJJJJJJJ");
        carPark.enterCarPark("KKKKKKKK");
        carPark.enterCarPark("LLLLLLLL");
        carPark.printParkingPlan();

        // removing a car from the area
        print ("Demo: Removing cars in an area");
        carPark.leaveCarPark("BBBBBBBB");
        carPark.printParkingPlan();

        // Add subscribed cars
        print ("Demo: Adding reserved cars in a reserved area");
        carPark.enterReservedCarPark("11111111");
        carPark.enterReservedCarPark("22222222");
        carPark.enterReservedCarPark("33333333");
        carPark.enterReservedCarPark("44444444");
        carPark.enterReservedCarPark("55555555");
        carPark.enterReservedCarPark("66666666");
        carPark.enterReservedCarPark("77777777");
        carPark.enterReservedCarPark("88888888");
        carPark.printParkingPlan();
        
        // remove car from the reserved area
        print ("Demo: Remove reserved car in a reserved area");
        carPark.leaveCarPark("11111111");
        carPark.printParkingPlan();

        // attempting to add a non reserved car in a reserved space in a week day
        print ("Demo: Attempting to add a non reserved car in a reserved space in a week day");
        carPark.enterReservedCarPark("NNNNNNNN");
        carPark.printParkingPlan();

        // Close carpark
        print ("Demo: Checking if it removes all cars when it closes the carpark");
        print("Closing carpark");
        carPark.closeCarPark();
        carPark.printParkingPlan();
    }
}





