package parsing

import scala.language.implicitConversions
import scala.util.matching._

trait Parsers[Parser[+_]] { self ⇒

    import Parsers._

    def run[A](p: Parser[A])(input: String): Either[ParseError, A]

    def or[A](s1: Parser[A], s2: ⇒ Parser[A]): Parser[A]

    implicit def string(s: String): Parser[String]

    implicit def operators[A](p: Parser[A]) = ParserOps[A](p)

    implicit def regex(r: Regex): Parser[String]

    case class ParserOps[A](p: Parser[A]) {
        def |[B >: A](p2: ⇒ Parser[B]): Parser[B] = self.or(p, p2)
        def or[B >: A](p2: ⇒ Parser[B]): Parser[B] = self.or(p, p2)
        def map[B](f: A ⇒ B): Parser[B] = self.map(p)(f)
        def **[B](pb: ⇒ Parser[B]) = self.product(p, pb)
        def product[B](pb: Parser[B]) = self.product(p, pb)
        def flatMap[B](f: A ⇒ Parser[B]) = self.flatMap(p)(f)
    }

    def char(c: Char): Parser[Char] = string(c.toString) map (_.charAt(0))

    def succeed[A](a: A): Parser[A] = string("") map (_ ⇒ a)

    def slice[A](p: Parser[A]): Parser[String]

    def flatMap[A, B](p: Parser[A])(f: A ⇒ Parser[B]): Parser[B]

    def errorLocation(e: ParseError): Location
    def errorMessage(e: ParseError): String
    def label[A](message: String)(p: Parser[A]): Parser[A]
    def scope[A](message: String)(p: Parser[A]): Parser[A]
    def attempt[A](p: Parser[A]): Parser[A]

    def option[A](p: Parser[A]): Parser[Option[A]] = {
        (p map (a ⇒ Some(a))) | succeed(None)
    }

    /** ex9.1 */
    def map2[A, B, C](pa: Parser[A], pb: ⇒ Parser[B])(f: (A, B) ⇒ C) = {
        pa ** pb map { case (a, b) ⇒ f(a, b) }
    }

    def many1[A](p: Parser[A]): Parser[List[A]] = {
        map2(p, many(p))(_ :: _)
    }

    /** ex9.3 Requirement: use `or`, `map2`, `succeed` */
    def many[A](p: Parser[A]): Parser[List[A]] = {
        map2(p, many(p))(_ :: _) or succeed(Nil)
    }

    /** ex9.4 Requirement: use `map2`, `succeed` */
    def listOfN[A](n: Int, p: Parser[A]): Parser[List[A]] = {
        @annotation.tailrec
        def listOfNImpl(
            n: Int, p: Parser[A], pl: Parser[List[A]]): Parser[List[A]] = {
            if (n == 0) pl
            else listOfNImpl(n - 1, p, map2(p, pl)(_ :: _))
        }
        listOfNImpl(n, p, succeed[List[A]](Nil))
    }

    /** ex9.6 open questing */
    def ex9_6(): Parser[String] = {
        flatMap(slice(many(char('c')))) { s ⇒
            string(s) ** listOfN(s.size, char('a')) map {
                case (s, l) ⇒ s + l.mkString("")
            }
        }
    }

    /** ex9.7 Requirement: use flatMap */
    def product[A, B](pa: Parser[A], pb: ⇒ Parser[B]): Parser[(A, B)] = {
        pa flatMap { a ⇒ flatMap(pb)(b ⇒ succeed((a, b))) }
    }

    def map2ByFlatMap[A, B, C](
        pa: Parser[A], pb: ⇒ Parser[B])(f: (A, B) ⇒ C) = {
        pa flatMap { a ⇒ pb flatMap (b ⇒ succeed(f(a, b))) }
    }

    /** ex9.8 Requirement: use flatMap */
    def map[A, B](a: Parser[A])(f: A ⇒ B): Parser[B] = {
        flatMap(a)(a ⇒ succeed(f(a)))
    }
}

object Parsers {
    case class Location(input: String, offset: Int = 0) {
        lazy val line = input.slice(0, offset + 1).count(_ == '\n') + 1
        lazy val col = input.slice(0, offset + 1).lastIndexOf('\n') match {
            case -1 ⇒ offset + 1
            case lineStart ⇒ offset - lineStart
        }

        def advanceBy(n: Int): Location = copy(offset = offset + n)
    }

    case class ParseError(stack: List[(Location, String)]) {
        def push(loc: Location, message: String): ParseError = {
            copy(stack = (loc, message) :: stack)
        }
        def label[A](s: String): ParseError = {
            ParseError(latestLoc.map((_, s)).toList)
        }
        def latestLoc: Option[Location] = {
            latest map (_._1)
        }
        def latest: Option[(Location, String)] = {
            stack.lastOption
        }
    }
}