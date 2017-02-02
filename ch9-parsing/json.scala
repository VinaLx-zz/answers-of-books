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

    def jsonParser[Err, Parser[+_]](P: Parsers[Err, Parser]): Parser[Json] = {
        import P._
        val jnum: Parser[JNumber] = regex(
            """(\d*\.\d+|\d+\.\d*)([eE]\d+)?""".r) map (s ⇒ JNumber(s.toDouble))
        val quoted_string: Parser[String] =
            regex(".*?".r) map (s ⇒ s.substring(1, s.size - 1))
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

        val jbasic: Parser[Json] = jnum | jstring | jnull | jbool
        val spc_string: Parser[String] = spaceAround(quoted_string)

        def jall: Parser[Json] = {
            spaceAround(jbasic | jarray | jObject)
        }

        def jarray: Parser[JArray] = {
            val item = jall ** comma map { case (j, _) ⇒ j }
            val last_item = jall ** option(comma) map { case (j, _) ⇒ j }
            val item_seq = many(item) ** last_item map {
                case (l, j) ⇒ l.toIndexedSeq :+ j
            }
            val empty = spaces map (_ ⇒ IndexedSeq[Json]())
            left_bracket ** (item_seq | empty) ** right_bracket map {
                case ((_, seq), _) ⇒ JArray(seq)
            }
        }
        def jObject: Parser[JObject] = {
            val kvpair = spaceAround(spc_string ** colon ** jall map {
                case ((s, _), a) ⇒ s -> a
            })
            left_brace ** many(kvpair) ** right_brace map {
                case ((_, lkv), _) ⇒ JObject(Map(lkv: _*))
            }
        }

        jall
    }
}
