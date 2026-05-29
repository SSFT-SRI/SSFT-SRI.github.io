**Exercises: Developing and Proving Algorithms with PVS (Part I)**

Consider the theory [`UTM0`](UTM0.pvs) and the lecture ["*Developing and Proving Algorithms with PVS (Part I)*"](../lecture-1.pdf).

1. Using `remove_op`, define the function [`unsubscribe`](UTM0.pvs#L55) that unsubscribes any operation of aircraft `ac_id` from `ops`.
2. Define a type judgement [`unsubscribe_j`](UTM0.pvs#L67) for the function `unsubscribe` stating that `result`, the output of the function, doesn't have an operation for aircraft `ac_id`,
the input parameter of the function. Prove the type judgement using `remove_op_j` as a lemma.
3. Fix [`test_1`](UTM0.pvs#L110) so that it holds. **Hint**: What is known about `Ac0`, `Ac1`, and `Ac2`? What should be assumed?
4. Fix [`subscribe`](UTM0.pvs#L32) so that only one operation per aircraft can be subscribed. After the change, make sure all TCCs and LEMMAS are still valid.
5. Define the function [`update`](UTM0.pvs#L129) that modifies the operation for a given aircraft. The function does nothing if the aircraft is not subscribed. Write a lemma to test the functionality. **Hint**: First, define a recursive function on `Operations` that change an element in the list. Then, use this function to define `update`.
