package functional_state

sealed trait Input
case object Coin extends Input
case object Turn extends Input

import State._

case class Machine(locked: Boolean, candies: Int, coins: Int) {
    override def toString(): String = s"Locked: $locked, Candies: $candies, Coins: $coins"
}

object Machine {
    val coin_handler = State[Machine, (Int, Int)] {
        case m @ Machine(false, candies, coins) ⇒ ((coins, candies), m)
        case m @ Machine(locked, 0, coins) ⇒ ((coins, 0), m)
        case Machine(true, candies, coins) ⇒
            ((coins + 1, candies), Machine(false, candies, coins + 1))
    }

    val turn_handler = State[Machine, (Int, Int)] {
        case m @ Machine(true, candies, coins) ⇒ ((coins, candies), m)
        case m @ Machine(locked, 0, coins) ⇒ ((coins, 0), m)
        case Machine(false, candies, coins) ⇒
            ((coins, candies - 1), Machine(true, candies - 1, coins))
    }

    def simulateMachine(inputs: List[Input]): State[Machine, (Int, Int)] = {
        val states = inputs.map {
            case Coin ⇒ coin_handler
            case Turn ⇒ turn_handler
        }
        State { s ⇒
            val final_trans = sequence(states).run(s)
            (final_trans._1.last, final_trans._2)
        }
    }

    def main(args: Array[String]): Unit = {
        val m = Machine(true, 10, 0)
        val inputs = List(Coin, Turn, Coin, Turn, Coin)
        println(simulateMachine(inputs).run(m))
    }
}