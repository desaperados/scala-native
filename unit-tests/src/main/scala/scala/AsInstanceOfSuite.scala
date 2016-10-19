package scala

object AsInstanceOfSuite extends tests.Suite {
  test("expects \"\".asInstanceOf[String] succeed") {
    assertNotNull("".asInstanceOf[String])
  }

  test("expects null.asInstanceOf[String] should succeed") {
    assertNull(null.asInstanceOf[String])
  }

  test("expects a.asInstanceOf[String], where a = null should succeed") {
    castNullToString(null)
  }

  def castNullToString(x: AnyRef): Unit = {
    if (x.isInstanceOf[String]) {
      assertNull(x.asInstanceOf[String])
    }

  }

  def assertNull(s: String): Unit = {
    assert(s == null)
  }

  def assertNotNull(s: String): Unit = {
    assert(s != null)
  }

  def shouldNotGetHere(s: String): Unit = {
    assert(false)
  }

  // TODO:
  //  test("expects anyRef.asInstanceOf[String] fail") {
  //    shouldNotGetHere((new AnyRef).asInstanceOf[String])
  //  }
}
