package scala

import org.junit.Assert._

object CharSuite extends tests.Suite {
  test("should_always_be_positive_when_coerced") {
    assertEquals(-3.toByte.toChar.toInt, 65533)
    assertEquals(-100.toShort.toChar.toInt, 65436)
    assertEquals(-66000.toChar.toInt, 65072)
    assertEquals(-4567L.toChar.toInt, 60969)
    assertEquals(-5.3f.toChar.toInt, 65531)
    assertEquals(-7.9.toChar.toInt, 65529)
  }

  test("should_overflow_when_coerced") {
    assertEquals(347876543.toChar.toInt, 11455)
    assertEquals(34234567876543L.toChar.toInt, 57279)
  }

  test("should_overflow_with_times") {
    def test(a: Char, b: Char, expected: Int): Unit =
      assertEquals(a * b, expected)

    // note: expected values are constant-folded by the compiler on the JVM
    test(Char.MaxValue, Char.MaxValue, Char.MaxValue * Char.MaxValue)
  }
}