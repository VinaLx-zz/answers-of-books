/**
 * this file contains the functional tree and related problems
 */
package data_structure

sealed trait Tree[+A]

case class Leaf[A](value: A) extends Tree[A]
case class Branch[A](left: Tree[A], right: Tree[A]) extends Tree[A]

object Tree {
    /** ex3.25 */
    def size[A](tree: Tree[A]): Int = tree match {
        case Leaf(_) ⇒ 1
        case Branch(left, right) ⇒ size(left) + size(right) + 1
    }

    /** ex3.26 */
    def maximum(tree: Tree[Int]): Int = tree match {
        case Leaf(value) ⇒ value
        case Branch(left, right) ⇒ maximum(left) max maximum(right)
    }

    /** ex3.27 */
    def depth[A](tree: Tree[A]): Int = tree match {
        case Leaf(value) ⇒ 1
        case Branch(left, right) ⇒ (depth(left) max depth(right)) + 1
    }

    /** ex3.28 */
    def map[A, B](tree: Tree[A])(f: A ⇒ B): Tree[B] = tree match {
        case Leaf(value) ⇒ Leaf(f(value))
        case Branch(left, right) ⇒ Branch(map(left)(f), map(right)(f))
    }

    /** ex3.29 */
    def fold[A, B](tree: Tree[A])(fb: (B, B) ⇒ B)(fl: A ⇒ B): B =
        tree match {
            case Leaf(value) ⇒
                fl(value)
            case Branch(left, right) ⇒
                fb(fold(left)(fb)(fl), fold(right)(fb)(fl))
        }

    def size2[A](tree: Tree[A]) =
        fold(tree)((a: Int, b: Int) ⇒ a + b + 1)(_ ⇒ 1)

    def maximum2(tree: Tree[Int]) =
        fold(tree)((a: Int, b: Int) ⇒ a max b)(_)

    def depth2[A](tree: Tree[A]) =
        fold(tree)((a: Int, b: Int) ⇒ ((a max b) + 1))(_ ⇒ 1)

    def map2[A, B](tree: Tree[A])(f: A ⇒ B) =
        fold[A, Tree[B]](tree)(Branch(_, _))(a ⇒ Leaf(f(a)))
}