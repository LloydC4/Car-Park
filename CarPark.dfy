class {:autocontracts} CarPark
{
    const nonReservedSpaces : int := 20; // total number of non-reserved spaces
    const margin : int := 5; // spaces removed from non-reserved spaces due to bad parking
    const reservedSpaces : int := 10; // total number of reserved

    var nonReservedSet : set<int>; // set for non-reserved parking
    var reservedSet : set<int>; // set for reserved parking
    var reservationIDs: set<int>; // set for reservationIDs

    var isWeekend : bool; // true if weekend, false if weekday

    constructor()
        //requires
        //ensures
        ensures nonReservedSpaces > 5; // ensures at least 1 space in non reserved car park(because of -5 margin)
        ensures reservedSpaces > 0; // ensures at least 1 space in reserved car park
        ensures reservationIDs == {} // ensures that no susbcriptions exist
        ensures nonReservedSet == {}  // ensures that non-reserevd car park is empty
        ensures reservedSet == {} // ensures that reserved car park is empty
        ensures !isWeekend // ensures car park begins on a weekday
        //modifies
    {
        nonReservedSet := {};
        reservedSet := {};
        reservationIDs := {};
        isWeekend := false;
    }
    
    // using {:autocontracts} so this predicate must hold true for all pre/post conditions
    // ensures that the number of spaces taken is always correct
    predicate Valid() 
        reads this;
    {
        nonReservedSpaces - (nonReservedSpaces - |nonReservedSet|) == |nonReservedSet| &&
        reservedSpaces - (reservedSpaces - |reservedSet|) == |reservedSet|
    }


    method enterCarPark(carID:int)
        //requires
        // check to see if car is already in car park
        requires carID !in nonReservedSet && carID !in reservedSet
        // checks to see if there's room available in the car park, cars with reservations can enter even if non-reserved is full
        requires !isWeekend ==> (|nonReservedSet| < (nonReservedSpaces - margin) || carID in reservationIDs)
        // checks to see if there is space in both car parks on weekend
        requires isWeekend ==> |nonReservedSet| + |reservedSet| < ((nonReservedSpaces + reservedSpaces) - margin)
        //ensures
        // ensures car park is not empty after method is run
        ensures |nonReservedSet| > 0
        // ensures car park contains 1 more car after method is run
        ensures |nonReservedSet| - 1 == old(|nonReservedSet|) 
        // ensures car has been added to car park
        ensures nonReservedSet == old(nonReservedSet) + {carID}
        //modifies
        modifies `nonReservedSet
    {
        nonReservedSet := nonReservedSet + {carID};     
    }

    method leaveCarPark(carID:int)
        //requires
        // check to see car is in the car park, this covers checking if the car park is empty to make sure no underflow 
        requires carID in nonReservedSet || carID in reservedSet 
        //ensures
        // ensures car park contains 1 less car after method is run
        ensures carID in nonReservedSet ==> |nonReservedSet| == old(|nonReservedSet|) - 1  || carID in reservedSet ==> |reservedSet| == old(|reservedSet|) - 1
        // ensures specified car has been removed from car park
        ensures carID in nonReservedSet ==> nonReservedSet == old(nonReservedSet) - {carID}  || carID in reservedSet ==> reservedSet == old(reservedSet) - {carID}
        // ensures car has been removed from either car park
        ensures (nonReservedSet == old(nonReservedSet) - {carID}  && reservedSet == old(reservedSet)) || (reservedSet == old(reservedSet) - {carID} && nonReservedSet == old(nonReservedSet)) 
        //modifies
        modifies `nonReservedSet, `reservedSet
    {
        if (carID in reservedSet) 
        {
            reservedSet := reservedSet - {carID};
        }
        else
        {
            nonReservedSet := nonReservedSet - {carID};
        }
    }

   method checkAvailability()
        //requires
        //ensures
        // ensures nothing is modified in this method
        // needed because with no modifies clause, things can be changed for some reason
        ensures nonReservedSet == old(nonReservedSet)
        ensures reservedSet == old(reservedSet) 
        ensures reservationIDs == old(reservationIDs) 
        ensures isWeekend == old(isWeekend) 
        //modifies
    {   
        print "\n";
        print("Non-reserved spaces available: ");
        if (!isWeekend)
        {
            print(nonReservedSpaces - |nonReservedSet| - margin);
            print "\n";
        }
        else
        {
            print(nonReservedSpaces + reservedSpaces - |nonReservedSet| - margin);
            print "\n";
        }
    }

    method enterReservedCarPark(carID:int)
        //requires
        // cars parked should be less than or equal to no of subscriptions on weekdays
        requires !isWeekend ==> |reservedSet| < |reservationIDs| || isWeekend ==> |reservedSet| < reservedSpaces 
        // only cars with reservations can park in reserved space unless it's weekend
        requires isWeekend || carID in reservationIDs 
        // car must not already be in reserved car park
        requires carID !in reservedSet 
        // car must be in non-reserved car park to enter reserved car park
        requires carID in nonReservedSet
        // must be at least 1 space available for car to park in
        requires |reservedSet| < reservedSpaces 
        //ensures
        // ensures that car park isn't empty
        ensures |reservedSet| > 0
        // ensures reserved car park contains 1 more car after method is run
        ensures |reservedSet| - 1 == old(|reservedSet|) 
        // ensures non reserved car park contains 1 less car after method is run
        ensures |nonReservedSet| == old(|nonReservedSet|- 1) 
        // ensures car has been removed from non reserved car park
        ensures nonReservedSet == old(nonReservedSet) - {carID} 
        // ensures car has been added to reserved car park
        ensures reservedSet == old(reservedSet) + {carID} 
        // ensures car is in reserved car park
        ensures carID in reservedSet
        // ensures car is not in non-reserved car park
        ensures carID !in nonReservedSet
        //modifies
        modifies `reservedSet, `nonReservedSet
    {
        nonReservedSet := nonReservedSet - {carID};
        reservedSet := reservedSet + {carID};
    }

    method makeSubscription(carID:int)
        //requires
        // must be less reservations than total spaces available
        requires |reservationIDs| < reservedSpaces 
        // car cannot already have a reservation
        requires carID !in reservationIDs 
        //ensures
        // ensures at least 1 reservation has been created
        ensures |reservationIDs| == old(|reservationIDs| + 1) 
        // ensures carID is in reservationIDs set
        ensures reservationIDs == old(reservationIDs) + {carID} 
        //modifies
        modifies `reservationIDs
    {
        reservationIDs := reservationIDs + {carID};
    }

    method openReservedArea() 
        //requires
        // isWeekend must be false
        requires !isWeekend
        //ensures
        // ensures is weekend is set to true
        ensures isWeekend
        //modifies
        modifies `isWeekend
    {
        isWeekend := true;
    }

    method closeCarPark()
        //requires
        //ensures
        // ensures both car parks are emptied and cars are crushed
        ensures nonReservedSet == {} 
        ensures |nonReservedSet| == 0
        ensures reservedSet == {}
        ensures |reservedSet| == 0
        //modifies 
        modifies `nonReservedSet, `reservedSet
    {
        nonReservedSet := {};
        reservedSet := {};
    }

    method printParkingPlan()
        //requires
        //ensures
        // ensures nothing is modified in this method
        // needed because with no modifies clause, things can be changed for some reason
        ensures nonReservedSet == old(nonReservedSet)
        ensures reservedSet == old(reservedSet) 
        ensures reservationIDs == old(reservationIDs) 
        ensures isWeekend == old(isWeekend) 
        //modifies
    {   
        print "\n";
        print("Parking Details: ");
        print "\n";
        print("Number of Subscriptions: ");
        print(|reservationIDs|);
        print(" - ");
        print(reservationIDs);
        print "\n";

        if (!isWeekend)
        {
            print("WEEKDAY: Non-reserved Spaces available: ");
            print(nonReservedSpaces - |nonReservedSet| - margin);
            print(" - ");
            print(nonReservedSet);
            print "\n";
            print("WEEKDAY: Reserved Spaces available: ");
            print(reservedSpaces - |reservedSet|);
            print(" - ");
            print(reservedSet);
            print "\n";
        }
        else
        {
            print("WEEKEND: Non-reserved Spaces: ");
            print(nonReservedSpaces - |nonReservedSet| - margin);
            print(" - ");
            print(nonReservedSet);
            print "\n";
            print("WEEKEND: Reserved Spaces available: ");
            print(reservedSpaces - |reservedSet|);
            print(" - ");
            print(reservedSet);
            print "\n";
        }
    }
}


method Main()
{
    //creating the car park
    var carPark := new CarPark();
    // SIMULATION -------------------------------------------------------------------------------------------------------------
    // Week day
    print("Employee with reservation shows up in car 1");
    print "\n";
    carPark.makeSubscription(1);
    carPark.enterCarPark(1);
    carPark.printParkingPlan();

    print "\n";
    print("Employee in car 1 enters the reserved car park");
    print "\n";
    carPark.enterReservedCarPark(1);
    carPark.printParkingPlan();

    print "\n";
    print("non-employees show up in cars 2 and 3");
    print "\n";
    carPark.enterCarPark(2);
    carPark.enterCarPark(3);
    carPark.printParkingPlan();

    print "\n";
    print("Car 1 and 3 leave");
    print "\n";
    carPark.leaveCarPark(1);
    carPark.leaveCarPark(3);
    carPark.printParkingPlan();

    print "\n";
    print("Car 2s owner forgets his car and it gets crushed");
    print "\n";
    carPark.closeCarPark();
    carPark.printParkingPlan();

    // Weekend
    carPark.openReservedArea();

    print "\n";
    print("Employee with reservation shows up in car 1");
    print "\n";
    carPark.enterCarPark(1);
    carPark.printParkingPlan();

    print "\n";
    print("Employee in car 1 enters the reserved car park");
    print "\n";
    carPark.enterReservedCarPark(1);
    carPark.printParkingPlan();

    print "\n";
    print("non-employees fill up non-reserved car park");
    print "\n";
    carPark.enterCarPark(2);
    carPark.enterCarPark(3);
    carPark.enterCarPark(4);
    carPark.enterCarPark(5);
    carPark.enterCarPark(6);
    carPark.enterCarPark(7);
    carPark.enterCarPark(8);
    carPark.enterCarPark(9);
    carPark.enterCarPark(10);
    carPark.enterCarPark(11);
    carPark.enterCarPark(12);
    carPark.enterCarPark(13);
    carPark.enterCarPark(14);
    carPark.enterCarPark(15);
    carPark.enterCarPark(16);
    carPark.printParkingPlan();

    print "\n";
    print("but since it's the weekend, car 17 shows up with no reservation, but can park in the reserved area anyway");
    print "\n";
    carPark.enterCarPark(17);
    carPark.enterReservedCarPark(17);
    carPark.printParkingPlan();

    print "\n";
    print("Cars 1, 16 and 17 leave from the reserved and non-reserved areas respectively");
    print "\n";
    carPark.leaveCarPark(1);
    carPark.leaveCarPark(16);
    carPark.leaveCarPark(17);
    carPark.printParkingPlan();

    print "\n";
    print("All other car owners forget their cars on the weekend due to drinking too much and they get crushed");
    print "\n";
    carPark.closeCarPark();
    carPark.printParkingPlan();

    // TEST CASES -------------------------------------------------------------------------------------------------------------
    // Test Case 1.1: Entering Car Park
    // Test Case 1.1.1: Entering Car Park when not already in - Expected Result/Actual Result: Pass/Pass
    //carPark.enterCarPark(1);
    //carPark.printParkingPlan();

    // Test Case 1.1.2: Entering Car Park when already in non-reserved car park - Expected Result/Actual Result: Fail/Fail
    //carPark.enterCarPark(1);

    // Test Case 1.1.3: Entering Car Park when already in reserved car park - Expected Result/Actual Result: Fail/Fail
    //carPark.makeSubscription(1);
    //carPark.enterReservedCarPark(1);
    //carPark.enterCarPark(1);

    // Test Case 1.1.4: Entering Car Park when full - Expected Result/Actual Result: Fail/Fail
    /*carPark.enterCarPark(1);
    carPark.enterCarPark(2);
    carPark.enterCarPark(3);
    carPark.enterCarPark(4);
    carPark.enterCarPark(5);
    carPark.enterCarPark(6);
    carPark.enterCarPark(7);
    carPark.enterCarPark(8);
    carPark.enterCarPark(9);
    carPark.enterCarPark(10);
    carPark.enterCarPark(11);
    carPark.enterCarPark(12);
    carPark.enterCarPark(13);
    carPark.enterCarPark(14);
    carPark.enterCarPark(15);
    carPark.enterCarPark(16);
    */
    
    // Test Case 1.1.5: Entering Car Park when full on weekend - Expected Result/Actual Result: Fail/Fail
    /*carPark.openReservedArea();
    carPark.enterCarPark(1);
    carPark.enterReservedCarPark(1);
    carPark.enterCarPark(2);
    carPark.enterReservedCarPark(2);
    carPark.enterCarPark(3);
    carPark.enterReservedCarPark(3);
    carPark.enterCarPark(4);
    carPark.enterReservedCarPark(4);
    carPark.enterCarPark(5);
    carPark.enterReservedCarPark(5);
    carPark.enterCarPark(6);
    carPark.enterReservedCarPark(6);
    carPark.enterCarPark(7);
    carPark.enterReservedCarPark(7);
    carPark.enterCarPark(8);
    carPark.enterReservedCarPark(8);
    carPark.enterCarPark(9);
    carPark.enterReservedCarPark(9);
    carPark.enterCarPark(10);
    carPark.enterReservedCarPark(10);
    carPark.enterCarPark(11);
    carPark.enterCarPark(12);
    carPark.enterCarPark(13);
    carPark.enterCarPark(14);
    carPark.enterCarPark(15);
    carPark.enterCarPark(16);
    carPark.enterCarPark(17);
    carPark.enterCarPark(18);
    carPark.enterCarPark(19);
    carPark.enterCarPark(20);
    carPark.enterCarPark(21);
    carPark.enterCarPark(22);
    carPark.enterCarPark(23);
    carPark.enterCarPark(24);
    carPark.enterCarPark(25);
    carPark.enterCarPark(26);
    */

    // Test Case 1.2: Susbcriptions
    // Test Case 1.2.1: Creating subscription when not having one - Expected Result/Actual Result: Pass/Pass
    //carPark.makeSubscription(1);
    //carPark.printParkingPlan();

    // Test Case 1.2.2: Creating subscription when already having one - Expected Result/Actual Result: Fail/Fail
    //carPark.makeSubscription(1);
    //carPark.makeSubscription(1);

    // Test Case 1.2.3: Creating subscription when every space is already reserved - Expected Result/Actual Result: Fail/Fail
    /*carPark.makeSubscription(1);
    carPark.makeSubscription(2);
    carPark.makeSubscription(3);
    carPark.makeSubscription(4);
    carPark.makeSubscription(5);
    carPark.makeSubscription(6);
    carPark.makeSubscription(7);
    carPark.makeSubscription(8);
    carPark.makeSubscription(9);
    carPark.makeSubscription(10);
    carPark.makeSubscription(11);
    */

    // Test Case 1.3: Entering Reserved Car Park
    // Test Case 1.3.1: Entering Reserved Car Park with subscription - Expected Result/Actual Result: Pass/Pass
    //carPark.makeSubscription(1);
    //carPark.enterCarPark(1);
    //carPark.enterReservedCarPark(1);
    //carPark.printParkingPlan();

    // Test Case 1.3.2: Entering Reserved Car Park without subscription - Expected Result/Actual Result: Fail/Fail
    //carPark.enterCarPark(1);
    //carPark.enterReservedCarPark(1);

    // Test Case 1.3.3: Entering Reserved Car Park from outside non-reserved car park with subscription - Expected Result/Actual Result: Fail/Fail
    //carPark.makeSubscription(1);
    //carPark.enterReservedCarPark(1);

    // Test Case 1.3.4: Entering Reserved Car Park from outside non-reserved car park without subscription - Expected Result/Actual Result: Fail/Fail
    //carPark.enterReservedCarPark(1);

    // Test Case 1.3.5: Entering Reserved Car Park on weekend with subscription - Expected Result/Actual Result: Pass/Pass
    //carPark.makeSubscription(1);
    //carPark.enterCarPark(1);
    //carPark.openReservedArea();
    //carPark.enterReservedCarPark(1);
    //carPark.printParkingPlan();

    // Test Case 1.3.6: Entering Reserved Car Park on weekend without subscription - Expected Result/Actual Result: Pass/Pass
    //carPark.enterCarPark(1);
    //carPark.openReservedArea();
    //carPark.enterReservedCarPark(1);
    //carPark.printParkingPlan();

    // Test Case 1.3.7: Entering Reserved Car Park on weekend when full - Expected Result/Actual Result: Fail/Fail
    /*carPark.openReservedArea();
    carPark.enterCarPark(1);
    carPark.enterReservedCarPark(1);
    carPark.enterCarPark(2);
    carPark.enterReservedCarPark(2);
    carPark.enterCarPark(3);
    carPark.enterReservedCarPark(3);
    carPark.enterCarPark(4);
    carPark.enterReservedCarPark(4);
    carPark.enterCarPark(5);
    carPark.enterReservedCarPark(5);
    carPark.enterCarPark(6);
    carPark.enterReservedCarPark(6);
    carPark.enterCarPark(7);
    carPark.enterReservedCarPark(7);
    carPark.enterCarPark(8);
    carPark.enterReservedCarPark(8);
    carPark.enterCarPark(9);
    carPark.enterReservedCarPark(9);
    carPark.enterCarPark(10);
    carPark.enterReservedCarPark(10);
    carPark.enterCarPark(11);
    carPark.enterReservedCarPark(11);
    */

    // Test Case 1.4: Leaving Car Park
    // Test Case 1.4.1: Leaving Car Park when in non-reserved car park - Expected Result/Actual Result: Pass/Pass
    //carPark.enterCarPark(1);
    //carPark.leaveCarPark(1);
    //carPark.printParkingPlan();

    // Test Case 1.4.2: Leaving Car Park when in reserved car park - Expected Result/Actual Result: Pass/Pass
    //carPark.makeSubscription(1);
    //carPark.enterCarPark(1);
    //carPark.enterReservedCarPark(1);
    //carPark.leaveCarPark(1)
    //carPark.printParkingPlan();

    // Test Case 1.4.3: Leaving Car Park when in not in car park - Expected Result/Actual Result: Fail/Fail
    //carPark.leaveCarPark(1);

    // Test Case 1.4.4: Leaving Car Park when in non-reserved car park on weekend - Expected Result/Actual Result: Pass/Pass
    //carPark.openReservedArea();
    //carPark.enterCarPark(1);
    //carPark.leaveCarPark(1);
    //carPark.printParkingPlan();

    // Test Case 1.4.5: Leaving Car Park when in reserved car park on weekend - Expected Result/Actual Result: Pass/Pass
    //carPark.openReservedArea();
    //carPark.enterCarPark(1);
    //carPark.enterReservedCarPark(1);
    //carPark.leaveCarPark(1);
    //carPark.printParkingPlan();

    // Test Case 1.4.6: Leaving Car Park when in not in car park on weekend - Expected Result/Actual Result: Fail/Fail
    //carPark.openReservedArea();
    //carPark.leaveCarPark(1);

    // Test Case 1.5: Closing Car Park
    // Test Case 1.5.1: Closing Car Park when empty - Expected Result/Actual Result: Pass/Pass
    //carPark.closeCarPark();
    //carPark.printParkingPlan();

    // Test Case 1.5.2: Closing Car Park when half full - Expected Result/Actual Result: Pass/Pass
    /*carPark.enterCarPark(1);
    carPark.enterCarPark(2);
    carPark.enterCarPark(3);
    carPark.enterCarPark(4);
    carPark.enterCarPark(5);
    carPark.enterCarPark(6);
    carPark.enterCarPark(7);
    carPark.closeCarPark();
    carPark.printParkingPlan();
    */

    // Test Case 1.5.3: Closing Car Park when full - Expected Result/Actual Result: Pass/Pass
    /*carPark.enterCarPark(1);
    carPark.enterCarPark(2);
    carPark.enterCarPark(3);
    carPark.enterCarPark(4);
    carPark.enterCarPark(5);
    carPark.enterCarPark(6);
    carPark.enterCarPark(7);
    carPark.enterCarPark(8);
    carPark.enterCarPark(9);
    carPark.enterCarPark(10);
    carPark.enterCarPark(11);
    carPark.enterCarPark(12);
    carPark.enterCarPark(13);
    carPark.enterCarPark(14);
    carPark.enterCarPark(15);
    carPark.closeCarPark();
    carPark.printParkingPlan();
    */

    // Test Case 1.5.4: Closing Car Park with cars in reserved car park - Expected Result/Actual Result: Pass/Pass
    /*carPark.makeSubscription(1);
    carPark.enterCarPark(1);
    carPark.enterReservedCarPark(1);
    carPark.closeCarPark();
    carPark.printParkingPlan();
    */

    // Test Case 1.5.5: Closing Car Park on weekend - Expected Result/Actual Result: Pass/Pass
    /*carPark.openReservedArea();
    carPark.enterCarPark(1);
    carPark.enterCarPark(2);
    carPark.enterCarPark(3);
    carPark.enterCarPark(4);
    carPark.enterCarPark(5);
    carPark.enterCarPark(6);
    carPark.enterCarPark(7);
    carPark.closeCarPark();
    carPark.printParkingPlan();
    */
}