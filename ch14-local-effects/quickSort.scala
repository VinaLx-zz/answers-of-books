package local_effects

object QuickSort {
    def quickSort(xs: List[Int]): List[Int] = {
        if (xs.isEmpty) xs else ST.runST(new RunnableST[List[Int]] {
            def apply[S] = for {
                arr ← STArray.fromList(xs)
                size ← arr.size
                _ ← quickSortImpl(arr, 0, size - 1)
                sorted ← arr.freeze
            } yield sorted
        })
    }

    def main(args: Array[String]) = {
        def printList(l: List[Int]): Unit = println(l.mkString(" "))
        val l1 = List(1)
        val l2 = List(2, 1, 3, 7, 0, 5, 4, 6)
        import scala.util.Random._
        List.fill(20)(1 to 20).
            map(l ⇒ shuffle(l).toList).
            map(l ⇒ quickSort(l)).foreach(l ⇒ printList(l))

        printList(quickSort(l1))
        printList(quickSort(l2))
    }

    /** ex14.2 */
    def partition[S](
        arr: STArray[S, Int], n: Int, r: Int, pivot: Int): ST[S, Int] = {
        for {
            _ ← arr.swap(n, pivot)
            p ← arr.read(n)
            boundref ← STRef(n)
            _ ← (n + 1 to r).foldLeft(ST[S, Unit](())) { (cur, idx) ⇒
                cur flatMap { _ ⇒
                    for {
                        value ← arr.read(idx)
                        _ ← if (value <= p) {
                            for {
                                bound ← boundref.read
                                _ ← arr.swap(idx, bound + 1)
                                _ ← boundref.write(bound + 1)
                            } yield ()
                        } else ST[S, Unit](())
                    } yield ()
                }
            }
            b ← boundref.read
            _ ← arr.swap(n, b)
        } yield b
    }
    def quickSortImpl[S](a: STArray[S, Int], n: Int, r: Int): ST[S, Unit] = {
        if (n >= r) ST(())
        else for {
            p ← partition(a, n, r, n)
            _ ← quickSortImpl(a, n, p - 1)
            _ ← quickSortImpl(a, p + 1, r)
        } yield ()
    }

}