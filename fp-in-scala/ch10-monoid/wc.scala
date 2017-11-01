package monoid

sealed trait WC {
    private def helper(s: String): Int = if (s.isEmpty) 0 else 1
    def count = this match {
        case Stub(s) ⇒ helper(s)
        case Part(l, c, r) ⇒ c + helper(l) + helper(r)
    }
}
final case class Stub(chars: String) extends WC
final case class Part(lStub: String, words: Int, rStub: String) extends WC

/** ex10.10 */
object WcMonoid extends Monoid[WC] {
    def zero: WC = Stub("")
    def op(lhs: WC, rhs: WC): WC = (lhs, rhs) match {
        case (Stub(sl), Stub(sr)) ⇒ Stub(sl + sr)
        case (Stub(s), Part(spl, c, spr)) ⇒ Part(s + spl, c, spr)
        case (Part(spl, c, spr), Stub(s)) ⇒ Part(spl, c, spr + s)
        case (Part(l1, c1, r1), Part(l2, c2, r2)) ⇒
            val add = if (r1.isEmpty && l2.isEmpty) 0 else 1
            Part(l1, c1 + c2 + add, r2)
    }
}

import Monoid._

object WC {
    def count(s: String): Int = {
        foldMapV(s.toIndexedSeq, WcMonoid) { c ⇒
            if (c.isWhitespace) Part("", 0, "")
            else Stub(c.toString)
        }.count
    }

    def main(args: Array[String]) = {
        println(count(" lets count how many words this string contains lol"))
    }
}
