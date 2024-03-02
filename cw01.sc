// CW 1

abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 

// you need to decide whether you proceed with Question 3
// or already use CFUN from Question 4 

case class RANGE(cs: Set[Char]) extends Rexp             // set of characters
case class PLUS(r: Rexp) extends Rexp                    // plus
case class OPTIONAL(r: Rexp) extends Rexp                // optional
case class INTER(r1: Rexp, r2: Rexp) extends Rexp        // intersection &
case class NTIMES(r: Rexp, n: Int) extends Rexp          // n-times
case class UPTO(r: Rexp, n: Int) extends Rexp            // up n-times
case class FROM(r: Rexp, n: Int) extends Rexp            // from n-times
case class BETWEEN(r: Rexp, n: Int, m: Int) extends Rexp // between nm-times
case class NOT(r: Rexp) extends Rexp                     // not
case class CFUN(f: Char => Boolean) extends Rexp         // subsuming CHAR and RANGE


// tests whether a regex can match the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPTIONAL(_) =>  true    
  case INTER(r1, r2) => nullable(r1) && nullable(r2)
  case NTIMES(r, n) => if (n==0) then true else false 
  case UPTO(_, n) => if (n==0) then true else false
  case FROM(_, n) => if (n==0) then true else false
  case BETWEEN(r, n, m) => if (n==0) then true else false
  case NOT(r) => if nullable(r) then false else true
  case CFUN(_) => false
  
}

// the derivative of a regular expression w.r.t. a character
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))
  case RANGE(cs) => if cs contains c then ONE else ZERO
  case PLUS(r) => SEQ(der(c, r), STAR(r)) 
  case OPTIONAL(r) => ALT(der(c, r), ONE)            
  case INTER(r1, r2) => SEQ(der(c, r1), der(c, r2))     
  case NTIMES(r, n) => if (n==0) then ZERO else SEQ(der(c, r), NTIMES(r, n-1))    
  case UPTO(r, n) => if (n==0) then ZERO else ALT(ONE, SEQ(der(c, r), UPTO(r, n-1)))
  case FROM(r, n) => if (n==0) then STAR(r) else SEQ(der(c, r), FROM(r, (n-1)))
  case BETWEEN(r, n, m) => if (n==0) then (if (m==0) then ZERO else SEQ(der(c, r), BETWEEN(r, n, m-1))) else SEQ(der(c, r), BETWEEN(r, n-1, m-1))
  case NOT(r) => NOT(der(c, r))
  case CFUN(f) => if (f(c)) then ONE else ZERO

}

// simplification
def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT (r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case r => r
}

// the derivative w.r.t. a string (iterates der)
def ders(s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, simp(der(c, r)))
}

// the main matcher function
def matcher(r: Rexp, s: String) : Boolean = 
  nullable(ders(s.toList, r))


// Test Cases
//============

// QUESTION 3 TESTS

val optional = OPTIONAL(CHAR('a'))
val not = NOT(CHAR('a'))
val three = NTIMES(CHAR('a'), 3)
val optthree = NTIMES(OPTIONAL(CHAR('a')), 3)
val upto = UPTO(CHAR('a'), 3)
val uptooptionalthree = UPTO(OPTIONAL(CHAR('a')), 3)
val between = BETWEEN(CHAR('a'), 3, 5)
val optionalbetween = BETWEEN(CHAR('a'), 2, 3)

// EXTRA TESTS + EDGE CASES

val from = FROM(CHAR('a'), 3)
val range = RANGE(Set('a', 'b', 'c'))
val plus = PLUS(CHAR('a'))
val inter = INTER(CHAR('a'), CHAR('a'))
val notplus = NOT(PLUS(CHAR('a')))
val zerotimes = NTIMES(CHAR('a'), 0)

/*
@main
def test1() = {
    println(matcher(optional, "")) // true
    println(matcher(optional, "a")) //  true
    println(matcher(optional, "aa")) // false
    println(matcher(optional, "aaa")) // false
    println(matcher(optional, "aaaaa")) //  false
    println(matcher(optional, "aaaaaa")) // false
}

@main
def test2() = {
    println(matcher(not, "")) // true
    println(matcher(not, "a")) // false
    println(matcher(not, "aa")) // true
    println(matcher(not, "aaa")) // true
    println(matcher(not, "aaaaa")) // true
    println(matcher(not, "aaaaaa")) // true
}

@main
def test3() = {
    println(matcher(three, "")) // false
    println(matcher(three, "a")) // false
    println(matcher(three, "aa")) // false
    println(matcher(three, "aaa")) // true
    println(matcher(three, "aaaaa")) // false
    println(matcher(three, "aaaaaa")) // false
}

@main
def test4() = {
    println(matcher(optthree, "")) //tbf // true
    println(matcher(optthree, "a")) // false
    println(matcher(optthree, "aa")) // false
    println(matcher(optthree, "aaa")) // true
    println(matcher(optthree, "aaaaa")) // false
    println(matcher(optthree, "aaaaaa")) // false
}

@main
def test5() = {
    println(matcher(upto, "")) //H // true
    println(matcher(upto, "a")) // true
    println(matcher(upto, "aa")) // true
    println(matcher(upto, "aaa")) // true
    println(matcher(upto, "aaaaa")) // false
    println(matcher(upto, "aaaaaa")) // false
}

@main
def test6() = {
    println(matcher(uptooptionalthree, "")) //tbf // true
    println(matcher(uptooptionalthree, "a")) // true
    println(matcher(uptooptionalthree, "aa")) // true
    println(matcher(uptooptionalthree, "aaa")) // true
    println(matcher(uptooptionalthree, "aaaaa")) // false
    println(matcher(uptooptionalthree, "aaaaaa")) // false
}

@main
def test7() = {
    println(matcher(between, "")) // false  
    println(matcher(between, "a")) // false
    println(matcher(between, "aa")) // false
    println(matcher(between, "aaa")) // true
    println(matcher(between, "aaaaa")) // true
    println(matcher(between, "aaaaaa")) // false
}

@main
def test8() = {
    println(matcher(optionalbetween, "")) //tbf // true
    println(matcher(optionalbetween, "a")) // false
    println(matcher(optionalbetween, "aa"))// tbf // false
    println(matcher(optionalbetween, "aaa")) // true
    println(matcher(optionalbetween, "aaaaa"))// tbf // true
    println(matcher(optionalbetween, "aaaaaa")) // false

}

@main
def test9() = {
    println(matcher(from, "")) // false
    println(matcher(from, "a")) // false
    println(matcher(from, "aa")) // false
    println(matcher(from, "aaa")) // true
    println(matcher(from, "aaaaa")) // true
    println(matcher(from, "aaaaaa")) // true
}

@main
def test10() = {
    println(matcher(range, "a")) // true
    println(matcher(range, "b")) // true
    println(matcher(range, "c")) // true
    println(matcher(range, "d")) // false
    println(matcher(range, "e")) // false
}

@main
def test11() = {
    println(matcher(plus, "")) // false
    println(matcher(plus, "a")) // true
    println(matcher(plus, "aa")) // true
    println(matcher(plus, "aaa")) // true
}

@main
def test12() = {
    println(matcher(inter, "")) // false
    println(matcher(inter, "a")) // true
    println(matcher(inter, "b")) // false
}

@main
def test13() = {
    println(matcher(notplus, "")) // true
    println(matcher(notplus, "a")) // false
    println(matcher(notplus, "aa")) // false
}

@main
def test14() = {
    println(matcher(zerotimes, "")) // true
    println(matcher(zerotimes, "a")) // false
    println(matcher(zerotimes, "aa")) // false
    println(matcher(zerotimes, "aaa")) // false
    println(matcher(zerotimes, "aaaa")) // false
    println(matcher(zerotimes, "aaaaa")) // false
} 

@arg(doc = "All tests.")
@main
def all() = {test1(); test2(); test3(); test4(); test5(); test6(); test7(); test8(); test9(); test10(); test11(); test12(); test13(); test14()}

*/

// some syntactic convenience

def charlist2rexp(s: List[Char]) : Rexp = s match {
 case Nil => ONE
 case c::Nil => CHAR(c)
 case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s: String) : Rexp = charlist2rexp(s.toList)

extension (r: Rexp) {
 def ~ (s: Rexp) = SEQ(r, s)
 def % = STAR(r)
}

// Question 5

// println("EMAIL:")
val LOWERCASE = ('a' to 'z').toSet
val DIGITS = ('0' to '9').toSet
val SYMBOLS1 = ("_.-").toSet
val SYMBOLS2 = (".-").toSet
val EMAIL = { PLUS(CFUN(LOWERCASE | DIGITS | SYMBOLS1)) ~ "@" ~ 
             PLUS(CFUN(LOWERCASE | DIGITS | SYMBOLS2)) ~ "." ~
             BETWEEN(CFUN(LOWERCASE | Set('.')), 2, 6) }

val my_email = "emma.conteh@kcl.ac.uk"

// println(EMAIL);
// println(matcher(EMAIL, my_email))
// println(ders(my_email.toList,EMAIL))

// (((([a-z0-9_.-]* . '.') . [a-z0-9_.-]^{2,6}) + [a-z0-9_.-]^{0,4}) + [a-z0-9_.-]^{0,1})

// Question 6
val ALL = RANGE(LOWERCASE | DIGITS | SYMBOLS1 | SYMBOLS2)
val COMMENT = """/*""" ~ (NOT(ALL.% ~ """*/""" ~ ALL.%)) ~ """*/"""

// println(matcher(COMMENT, """/**/"""))
// println(matcher(COMMENT, """/*foobar*/"""))
// println(matcher(COMMENT, """/*test*/test*/"""))
// println(matcher(COMMENT, """/*test/*test*/"""))

// Question 7
 
val r1 = PLUS(PLUS(SEQ(SEQ(CHAR('a'), CHAR('a')), CHAR('a'))))
val r2 = PLUS(PLUS(SEQ(BETWEEN(CHAR('a'), 19, 19), OPTIONAL(CHAR('a')))))
val s1 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val s2 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val s3 = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

for (s <- List(s1,s2,s3)) {
//  println(matcher(r1, s))
//  println(matcher(r2, s))
}