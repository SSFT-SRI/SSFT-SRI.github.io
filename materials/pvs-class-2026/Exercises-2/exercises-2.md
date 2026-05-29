**Exercises: Developing and Proving Algorithms with PVS (Part II)**

Consider the theories [`UTM0`](UTM0.pvs), [`UTM`](UTM.pvs), and the lecture ["*Developing and Proving Algorithms with PVS (Part II)*"](../lecture-2.pdf).

6. Write a strategy called [`uss-tcc`](pvs-strategies#L6) and use it to discharge the proofs of [`subscribe_j`](UTM0.pvs#L57), [`test_0`](UTM0.pvs#L104), [`test_1`](UTM0.pvs#L109), [`Dos`](UTM0.pvs#L122), and
[`test_update`](UTM0.pvs#L137). **Hint**: The strategy does the following: first apply `grind`,
then to each generated subgoal, expand `exists_op` as many times as needed.

7. Define the function [`in_operational_volume?(uss:USS)(p:Vect3) : bool`](UTM.pvs#34) that
   returns `TRUE` if the point `p` is inside the
   operational volume of `uss`. **Hint**: Check that
   - The vertical component of `p`, i.e., `p`\``z`,
       is below `uss`\``op_alt`.
   - The horizontal component of `p`, i.e.,
       `vect2(p)`, is inside `uss`op\_area}.
    Look for the names of the functions in `NASALib/shapes`
     that check if a point is inside a circle, rectangle, and triangle.

8. Define the function [`check_flight_plan(uss:USS,ac_op:AircraftOP)`](UTM.pvs#L47) that
   returns
     - `OK`, if every waypoint in the flight plan of ac_op lies inside the USS
   operational volume, or
   - `Failure(wps)` otherwise, where `wps` is
   the list of waypoints in its flight plan that lie outside the USS
   operational volume.

9. Modify the function `subscribe` in [`UTM.pvs`](UTM.pvs) so that
   only aircraft operations `ac_op` that satisfy
   `check_flight_plan(uss,ac_op) = OK` are subscribed.
   Throw an exception if `check_flight_plan(uss)` returns a Failure.
