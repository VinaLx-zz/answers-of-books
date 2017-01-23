object IsSorted {
    def isSorted[A](a: Array[A], order: (A, A) ⇒ Boolean): Boolean = {
        @annotation.tailrec
        def isSortedImpl(n: Int): Boolean = {
            if (n >= a.length - 1) true
            else if (!order(a(n), a(n + 1))) false
            else isSortedImpl(n + 1)
        }

        isSortedImpl(0)
    }

    def main(argv: Array[String]) = {
        val le = (a: Int, b: Int) ⇒ a <= b
        val empty = Array[Int]()
        val is_sorted = Array(1, 2, 3, 4, 5)
        val is_not_sorted = Array(1, 3, 2, 4, 5)
        for (a ← Seq(empty, is_sorted, is_not_sorted)) println(isSorted(a, le))
    }
}