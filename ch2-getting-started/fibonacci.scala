object Fibonacci {
    def fib(n: Int): Int = {
        @annotation.tailrec
        def fib_impl(cur: Int, next: Int, count: Int): Int = {
            if (count <= 0) cur
            else fib_impl(next, cur + next, count - 1)
        }
        fib_impl(0, 1, n)
    }

    def main(argv: Array[String]) = {
        for (n ← 0 to 20) println(s"fib $n = ${fib(n)}")
    }
}