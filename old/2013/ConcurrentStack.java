package benchmarks.testcases;

import java.util.concurrent.atomic.*;
import java.util.*;

// import net.jcip.annotations.*;

/**
 * ConcurrentStack
 *
 * Nonblocking stack using Treiber's algorithm
 *
 * @author Brian Goetz and Tim Peierls
 */

public class ConcurrentStack <E> {
    AtomicReference<Node<E>> top = new AtomicReference<Node<E>>();

    public void push(E item) {
        Node<E> newHead = new Node<E>(item);
        Node<E> oldHead;
        do {
            oldHead = top.get();
            newHead.next = oldHead;
        } while (!top.compareAndSet(oldHead, newHead));
    }

    public E pop() {
        Node<E> oldHead;
        Node<E> newHead;
        do {
            oldHead = top.get();
            if (oldHead == null)
                return null;
            newHead = oldHead.next;
        } while (!top.compareAndSet(oldHead, newHead));
        return oldHead.item;
    }

    private static class Node <E> {
        public final E item;
        public Node<E> next;

        public Node(E item) {
            this.item = item;
        }
    }

/**
 * Test routine (used for CalFuzzer http://srl.cs.berkeley.edu/~ksen/calfuzzer/)
 *
 * @author Gidon Ernst <ernst@informatik.uni-augsburg.de>
 *
 * Instructions:
 *
 * $ cd calfuzzer
 *
 * save this file in test/benchmarks/testcases/ConcurrentStack.java
 *
 * add to run.xml
 *
 * <target name="concurrentstack">
 *     <echo message="unknown?"/>
 *     <property name="javato.work.dir" value="${benchdir}"/>
 *     <property name="javato.app.main.class" value="benchmarks.testcases.ConcurrentStack"/>
 *     <antcall target="deadlock-analysis"/>
 *     <antcall target="race-analysis"/>
 * </target>
 *
 * $ javac test/benchmarks/testcases/ConcurrentStack.java -d classes
 *
 * $ ant -f run.xml concurrentstack
 *
 * it should report two data races
 * (which are in fact benign, Treiber's stack has been proved linearizable)
 */
    public static void main(String[] args) {
        final ConcurrentStack<Integer> stack = new ConcurrentStack<>();

        /* producer thread */
        new Thread() {
            public void run() {
                Random random = new Random();
                /* bounded loops, since the analyzer actually runs this code */
                for(int i=0; i<10; i++) {
                    stack.push(random.nextInt());
                }
            }
        }.start();

        /* consumer thread */
        new Thread() {
            public void run() {
                for(int i=0; i<10; i++) {
                    stack.pop();
                }
            }
        }.start();
    }
}
