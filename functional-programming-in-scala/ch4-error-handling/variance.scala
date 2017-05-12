package error_handling

object Variance {
    /** ex4.2 */
    def variance(xs: Seq[Double]): Option[Double] = {
        def map_helper(xs: Seq[Double]): Option[Double] = {
            if (xs.isEmpty) None
            else {
                val mean = xs.sum / xs.size
                val sxx = xs.map(n ⇒ math.pow(n - mean, 2)).sum
                Some(sxx / xs.size)
            }
        }
        Some(xs) flatMap map_helper
    }

    /** answer in the answerkey, a lot more elegant */
    def variance2(xs: Seq[Double]): Option[Double] = {
        def mean(xs: Seq[Double]): Option[Double] = {
            if (xs.isEmpty) None
            else Some(xs.sum / xs.size)
        }
        mean(xs) flatMap (a ⇒ mean(xs.map(n ⇒ math.pow(n - a, 2))))
    }

    def main(argv: Array[String]) = {
        val xs1 = Seq.empty[Double]
        val xs2 = Seq(1.0 to 5.0 by 1.0: _*)
        for (xs ← Seq(xs1, xs2))
            println(s"variance of $xs is: ${variance(xs)}")
    }
}
