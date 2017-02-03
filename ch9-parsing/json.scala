/**
 * custom json objects of the book
 */

package parsing

import scala.language.implicitConversions

trait Json
object Json {
    case object JNull extends Json
    case class JNumber(get: Double) extends Json
    case class JString(get: String) extends Json
    case class JBool(get: Boolean) extends Json
    case class JArray(get: IndexedSeq[Json]) extends Json
    case class JObject(get: Map[String, Json]) extends Json
}

object JsonParser {
    import Json._
    import Parsers._
    import MyParser._

    def parse[Parser[+_]](P: Parsers[Parser]): Parser[Json] = {
        import P._
        val jnum: Parser[JNumber] = regex(
            """(\d*\.\d+|(\d+(\.\d*)?))([eE]\d+)?""".r) map {
                s ⇒ JNumber(s.toDouble)
            }
        val quoted_string: Parser[String] =
            regex("""".*?"""".r) map (s ⇒ s.substring(1, s.size - 1))
        val jstring: Parser[JString] = quoted_string map (JString(_))
        val jnull: Parser[JNull.type] = string("null") map (_ ⇒ JNull)
        val jbool: Parser[JBool] = string("true") | string("false") map {
            case "true" ⇒ JBool(true)
            case "false" ⇒ JBool(false)
        }
        val space = char(' ') | char('\n') | char('\t')
        val spaces = slice(many(space))
        val (comma, colon) = (char(','), char(':'))
        val (left_bracket, right_bracket) = (char('['), char(']'))
        val (left_brace, right_brace) = (char('{'), char('}'))

        def spaceAround[A](p: Parser[A]): Parser[A] = {
            spaces ** p ** spaces map { case ((s, a), s2) ⇒ a }
        }
        def connect[A](
            p: Parser[A], conn: String, allow_last_seq: Boolean) = {
            val item = string(conn) ** spaceAround(p) map { case (_, a) ⇒ a }
            val items = spaceAround(p) ** many(item) map {
                case (a, la) ⇒ a +: la.toIndexedSeq
            }
            val res_items =
                if (allow_last_seq)
                    items ** option(spaceAround(conn)) map { case (l, _) ⇒ l }
                else items

            val empty = spaces map (_ ⇒ IndexedSeq[A]())
            attempt(res_items) or empty
        }

        val jbasic: Parser[Json] = jnum | jstring | jnull | jbool
        val spc_string: Parser[String] = spaceAround(quoted_string)

        def jall: Parser[Json] = jbasic | jarray | jObject

        def jarray: Parser[JArray] = {
            val item_seq = connect(jall, ",", true)
            left_bracket ** item_seq ** right_bracket map {
                case ((_, seq), _) ⇒ JArray(seq)
            }
        }
        def jObject: Parser[JObject] = {
            val kvpair = spc_string ** spaceAround(colon) ** jall map {
                case ((s, _), a) ⇒ s -> a
            }
            left_brace ** connect(kvpair, ",", true) ** right_brace map {
                case ((_, lkv), _) ⇒ JObject(Map(lkv: _*))
            }
        }

        spaceAround(jall)
    }

    def testNumber() = {
        val integer = "   12345   "
        val floating = "   123.56"
        val exponential = "1.5e10    "
        val parser = parse(MyParsers)
        val result = for (num ← Seq(integer, floating, exponential))
            yield MyParsers.run(parser)(num)
        println(result.mkString("\n"))
    }

    def testString() = {
        println("")
        val s1 = """"""""
        val s2 = """"something" """
        val s3 = """ "what is this"  """
        val result = for (s ← Seq(s1, s2, s3))
            yield MyParsers.run(parse(MyParsers))(s)
        println(result.mkString("\n"))
    }

    def testBoolNull() = {
        println("")
        val t = " true  "
        val f = " false"
        val n = " null   "
        val result = for (v ← Seq(t, f, n))
            yield MyParsers.run(parse(MyParsers))(v)
        println(result.mkString("\n"))
    }

    def testArray() = {
        println("")
        val arr1 = "[1,2,3,]"
        var arr2 = " [ ] "
        val arr3 = " [ 1, \"what\", true]"
        val arr4 = " [ [1, 2, false,], [\"what\", null]]"
        val result = for (arr ← Seq(arr1, arr2, arr3, arr4))
            yield MyParsers.run(parse(MyParsers))(arr)
        println(result.mkString("\n"))
    }

    def testObject() = {
        println("")
        val obj1 = "{ }"
        val obj2 = """ { "one": 1, "two": 2, "three": 3}"""
        val obj3 = """ { "one": [1, 2, 3], "two": true, "three": "what"}"""
        val obj4 = s"""
            |{
            |   "one": {
            |       "two": 2,
            |       "three": {
            |            "four": [4, 5, 6, 7],
            |       },
            |       "five": [ { "six": 6 } ],
            |   }
            |}""".stripMargin
        val result = for (obj ← Seq(obj1, obj2, obj3, obj4))
            yield MyParsers.run(parse(MyParsers))(obj)
        println(result.mkString("\n"))
    }

    def main(args: Array[String]) = {
        testNumber()
        testString()
        testBoolNull()
        testArray()
        testObject()
    }
}
