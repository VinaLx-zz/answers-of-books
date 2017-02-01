package testing.prop1

trait Prop {
    def check: Boolean
    /** ex8.3 */
    def &&(rhs: Prop): Prop = new Prop {
        def check = Prop.this.check && rhs.check
    }
}