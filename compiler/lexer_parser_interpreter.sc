//================
// CW2 - Lexer
//================

// Rexp
abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

case class RANGE(s: Set[Char]) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPTIONAL(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp 

// Values
abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val


// Convenience for typing
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}

implicit def string2rexp(s : String) : Rexp = 
  charlist2rexp(s.toList)

extension (r: Rexp) {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

extension (s: String) {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

// nullable
def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true

  case RECD(_, r1) => nullable(r1)
  case RANGE(_) => false
  case PLUS(r1) => nullable(r1)
  case OPTIONAL(_) => true
  case NTIMES(r1, i) => if (i == 0) true else nullable(r1)
}

// der
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))

  case RECD(_, r1) => der(c, r1)
  case RANGE(s) => if (s.contains(c)) ONE else ZERO 
  case PLUS(r1) => SEQ(der(c, r1), STAR(r1))
  case OPTIONAL(r1) => der(c, r1)
  case NTIMES(r, i) => 
    if (i == 0) ZERO else SEQ(der(c, r), NTIMES(r, i - 1))
}

// Flatten
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}

// Env
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// Mkeps
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))

  case PLUS(r) => Stars(List(mkeps(r)))   // the first copy must match the empty string
  case OPTIONAL(r) => if (nullable(r)) Stars(List(mkeps(r))) else Stars(Nil)
  case NTIMES(r, i) => Stars(List.fill(i)(mkeps(r)))
}

// Inj
def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))

  case (RANGE(_), Empty) => Chr(c)
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPTIONAL(r), v1) => Stars(List(inj(r, c, v1)))
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
}

// Rectification functions
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = 
  (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

// Simp
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case r => (r, F_ID)
}

// Lex
def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else 
    { throw new Exception("lexing error") } 
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) = env(lex_simp(r, s.toList))

// Language specific code
val KEYWORD : Rexp = "def" | "val" | "if" | "then" | "else" | "write" 
val OP : Rexp = "+" | "-" | "*" | "%" | "/" | "==" | "!=" | ">" | "<" | ">=" | "<=" | "&&" | "||" | "="
val LET: Rexp = RANGE(('A' to 'Z').toSet ++ ('a' to 'z').toSet)
val SYM : Rexp = "."| "_" | ">" | "<" | "=" | ";"| "," | ":" | ")" | "(" | """\n""" | "\"" | """ " """ 
val PARENS : Rexp = "(" | "{" | ")" | "}"
val SEMI : Rexp = ";"
val WHITESPACE : Rexp = PLUS(" ") | "\n" | "\t" | "\r"
val DIGIT : Rexp = RANGE(('0' to '9').toSet)
val DIGIT1 : Rexp = RANGE(('1' to '9').toSet)
val STRING : Rexp = "\"" ~ (LET | SYM | DIGIT | " " | "\\n").% ~ "\""
val ID : Rexp = LET ~ (LET | "_" | DIGIT).%
val NUM : Rexp = "0" | OPTIONAL("-") ~ (DIGIT1 ~ DIGIT.%)
val EOL : Rexp = "\n" | "\r\n"
val COMMENT : Rexp = "//" ~ (LET | SYM | PARENS | " " | DIGIT).% ~ EOL 
val TYPE : Rexp = "Int" | "Double" | "Void"
val NOTVOID : Rexp = "Int" | "Double"
val FNUM : Rexp = OPTIONAL("-") ~ NUM ~ "." ~ DIGIT ~ DIGIT.%
val COLON : Rexp = ":"
val COMMA : Rexp = ","
val CHARACTER = "'" ~ (LET | SYM | OP | WHITESPACE | DIGIT ) ~ "'"


val FUN_REGS = (("k" $ KEYWORD) | 
                  ("nvt" $ NOTVOID) |
                  ("t" $ TYPE) |
                  ("o" $ OP) | 
                  ("str" $ STRING) |
                  ("p" $ PARENS) |
                  ("s" $ SEMI) | 
                  ("w" $ WHITESPACE) | 
                  ("i" $ ID) | 
                  ("n" $ NUM) |
                  ("f" $ FNUM) |
                  ("col" $ COLON) |
                  ("com" $ COMMA) |
                  ("cha" $ CHARACTER) |
		  ("c" $ COMMENT)).%

def esc(raw: String): String = {
  import scala.reflect.runtime.universe._
  Literal(Constant(raw)).toString
}

def escape(tks: List[(String, String)]) =
  tks.map{ case (s1, s2) => (s1, esc(s2))}

abstract class Token extends Serializable 
case class T_KEYWORD(s: String) extends Token
case class T_OP(s: String) extends Token
case class T_STRING(s: String) extends Token
case class T_PAREN(s: String) extends Token
case object T_SEMI extends Token
case class T_ID(s: String) extends Token
case class T_CHAR(s: String) extends Token
case class T_NUM(n: Int) extends Token
case class T_TYPE(s: String) extends Token
case class T_FNUM(n: Double) extends Token
case object T_COLON extends Token
case object T_COMMA extends Token


val token : PartialFunction[(String, String), Token] = {
  case ("k", s) => T_KEYWORD(s)
  case ("o", s) => T_OP(s)
  case ("str", s) => T_STRING(s)
  case ("p", s) => T_PAREN(s)
  case ("s", _) => T_SEMI
  case ("i", s) => T_ID(s)
  case ("n", s) => T_NUM(s.toInt)
  case ("t", s) => T_TYPE(s)
  case ("f", s) => T_FNUM(s.toDouble)
  case ("nvt", s) => T_TYPE(s)
  case ("col", _) => T_COLON
  case ("com", _) => T_COMMA
  case ("cha", s) => T_CHAR(s)

}

//================
//CW3 - Parser
//================

case class ~[+A, +B](x: A, y: B)

type IsSeq[I] = I => Seq[_]


// parser combinators

abstract class Parser[I, T](using is: I => Seq[_])  {
  def parse(in: I): Set[(T, I)]  

  def parse_all(in: I) : Set[T] =
    for ((hd, tl) <- parse(in); 
        if is(tl).isEmpty) yield hd
}

// parser combinators

// sequence parser
class SeqParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                 q: => Parser[I, S]) extends Parser[I, ~[T, S]] {
  def parse(in: I) = 
    for ((hd1, tl1) <- p.parse(in); 
         (hd2, tl2) <- q.parse(tl1)) yield (new ~(hd1, hd2), tl2)
}

// alternative parser
class AltParser[I : IsSeq, T](p: => Parser[I, T], 
                              q: => Parser[I, T]) extends Parser[I, T] {
  def parse(in: I) = p.parse(in) ++ q.parse(in)
}

// map parser
class MapParser[I : IsSeq, T, S](p: => Parser[I, T], 
                                f: T => S) extends Parser[I, S] {
  def parse(in: I) = for ((hd, tl) <- p.parse(in)) yield (f(hd), tl)
}

// Question 2

case class TokenParser(s: String) extends Parser[List[Token], String] {
  def parse(in: List[Token]): Set[(String, List[Token])] = in match {
    case (T_KEYWORD(str)) :: tail if str == s => Set((str, tail))
    case (T_OP(str)) :: tail if str == s => Set((str, tail))
    case (T_STRING(str)) :: tail if str == s => Set((str, tail))
    case (T_PAREN(str)) :: tail if str == s => Set((str, tail))
    case T_SEMI :: tail if s == ";" => Set((";", tail))
    case T_COLON :: tail if s == ":" => Set((":", tail))
    case T_COMMA :: tail if s == "," => Set((",", tail))
    case (T_ID(str)) :: tail if str == s => Set((str, tail))
    case (T_NUM(n)) :: tail if n.toString == s => Set((n.toString, tail))
    case (T_TYPE(str)) :: tail if str == s => Set((str, tail))
    case (T_FNUM(n)) :: tail if n.toString == s => Set((n.toString, tail))
    case (T_CHAR(str)) :: tail if str == s => Set((str, tail))
    case _ => Set()
  }
}

// atomic parser for identifiers (variable names)
case object IdParser extends Parser[List[Token], String] {
  def parse(in: List[Token]): Set[(String, List[Token])] = in match {
    case (T_ID(str)) :: tail => Set((str, tail))
    case _ => Set()
  }
}

// atomic parser for numbers (transformed into ints)
case object NumParser extends Parser[List[Token], Int] {
  def parse(in: List[Token]): Set[(Int, List[Token])] = in match {
    case (T_NUM(n)) :: tail => Set((n, tail))
    case _ => Set()
  }
}

// atomic parser for strings
case object StrParser extends Parser[List[Token], String] {
  def parse(in: List[Token]): Set[(String, List[Token])] = in match {
    case (T_STRING(str)) :: tail => Set((str, tail))
    case _ => Set()
  }
}

// atomic parser for floats
case object FNumParser extends Parser[List[Token], Double] {
  def parse(in: List[Token]): Set[(Double, List[Token])] = in match {
    case (T_FNUM(n)) :: tail => Set((n, tail))
    case _ => Set()
  }
}

// atomic parser for types
case object TypeParser extends Parser[List[Token], String] {
  def parse(in: List[Token]): Set[(String, List[Token])] = in match {
    case (T_TYPE(str)) :: tail => Set((str, tail))
    case _ => Set()
  }
}

// atomic parser for non-void types
case object NotVoidParser extends Parser[List[Token], String] {
  def parse(in: List[Token]): Set[(String, List[Token])] = in match {
    case (T_TYPE("Int")) :: tail => Set(("Int", tail))
    case (T_TYPE("Double")) :: tail => Set(("Double", tail))
    case _ => Set()
  }
}

// atomic parser for characters
case object CharParser extends Parser[List[Token], String] {
  def parse(in: List[Token]): Set[(String, List[Token])] = in match {
    case (T_CHAR(str)) :: tail => Set((str, tail))
    case _ => Set()
  }
}

def ListParser[I, T, S](p: => Parser[I, T], 
                        q: => Parser[I, S])(implicit ev: I => Seq[_]): Parser[I, List[T]] = {
  (p ~ q ~ ListParser(p, q)).map[List[T]]{ case x ~ _ ~ z => x :: z } ||
  p.map[List[T]]{ case x => List(x) }
}

extension (sc: StringContext) 
  def p(args: Any*) = TokenParser(sc.s(args:_*))


// more convenient syntax for parser combinators
extension [I : IsSeq, T](p: Parser[I, T]) {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

// the abstract syntax trees for the FUN language
abstract class Exp
abstract class BExp
abstract class Decl

case class Def(name: String, args: List[(String, String)], ty: String, body: Exp) extends Decl
case class Main(e: Exp) extends Decl
case class Const(name: String, v: Int) extends Decl
case class FConst(name: String, x: Double) extends Decl

case class Call(name: String, args: List[Exp]) extends Exp
case class If(a: BExp, e1: Exp, e2: Exp) extends Exp
case class Var(s: String) extends Exp
case class Num(i: Int) extends Exp  // integer numbers
case class FNum(i: Double) extends Exp  // float numbers
case class ChConst(c: Int) extends Exp  // character constants
case class Aop(o: String, a1: Exp, a2: Exp) extends Exp
case class Sequence(e1: Exp, e2: Exp) extends Exp  // expressions separated by semicolons
case class Bop(o: String, a1: Exp, a2: Exp) extends BExp
// case class PrintString(name: String, vrs: List[ChConst]) extends Exp


lazy val Exp: Parser[List[Token], Exp] =
  (p"if" ~ BExp ~ p"then" ~ Exp ~ p"else" ~ Exp).map[Exp]{ case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w): Exp } ||
    (p"{" ~ Exp ~ p"}").map{ case _ ~ y ~ _ => y } ||
    (AExp ~ p";" ~ Exp).map[Exp]{ case x ~ _ ~ z => Sequence(x, z): Exp } || AExp
lazy val AExp: Parser[List[Token], Exp] = 
  (Te ~ p"+" ~ Exp).map[Exp]{ case x ~ _ ~ z => Aop("+", x, z): Exp } ||
  (Te ~ p"-" ~ Exp).map[Exp]{ case x ~ _ ~ z => Aop("-", x, z): Exp } || Te
lazy val Te: Parser[List[Token], Exp] = 
  (Fa ~ p"*" ~ Te).map[Exp]{ case x ~ _ ~ z => Aop("*", x, z): Exp } || 
  (Fa ~ p"/" ~ Te).map[Exp]{ case x ~ _ ~ z => Aop("/", x, z): Exp } ||
  (Fa ~ p"%" ~ Te).map[Exp]{ case x ~ _ ~ z => Aop("%", x, z): Exp } ||  Fa  
lazy val Fa: Parser[List[Token], Exp] = 
  (IdParser ~ p"(" ~ ListParser(Exp, p",") ~ p")").map[Exp]{ case y ~ _ ~ u ~ _ => Call(y, u): Exp } ||
  (IdParser ~ p"(" ~ p")").map[Exp]{ case x ~ _ ~ _ => Call(x, List()) : Exp } ||
  (p"skip").map[Exp]{ case _ => Call("skip", List()) : Exp } ||
  (IdParser ~ p"(" ~ StrParser ~ p")").map[Exp]{ case x ~ _ ~ y ~ _ => Call(x, List(Var(y))) : Exp } ||
  // (p"print_string" ~ p"(" ~ StrParser ~ p")").map[Exp]{ case _ ~ _ ~ y ~ _ => 
  // val chConstList = y.toList.map(char => ChConst(char.toInt))
  // PrintString("print_string", chConstList) : Exp } ||
   (p"(" ~ Exp ~ p")").map{ case _ ~ y ~ _ => y: Exp } || 
   (p"{" ~ Exp ~ p"}").map{ case _ ~ u ~ _ => u: Exp } ||
   IdParser.map[Exp]{ case x => Var(x): Exp } ||
   NumParser.map[Exp]{ case x => Num(x): Exp } ||
   FNumParser.map[Exp]{ case x => FNum(x): Exp } ||
   StrParser.map[Exp]{ case x => Var(x): Exp } ||
   CharParser.map[Exp]{ case x => ChConst(((((x).substring(1, x.length()-1))replaceAll("""\\n""", "\n")).charAt(0)).toInt): Exp }

lazy val BExp: Parser[List[Token], BExp] =
   (Exp ~ p"==" ~ Exp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z): BExp } || 
   (Exp ~ p"!=" ~ Exp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z): BExp } || 
   (Exp ~ p"<" ~ Exp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z): BExp } || 
   (Exp ~ p">" ~ Exp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z): BExp } || 
   (Exp ~ p"<=" ~ Exp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z): BExp } ||
   (Exp ~ p">=" ~ Exp).map[BExp]{ case x ~ _ ~ z => Bop(">=", x, z): BExp }

lazy val Defs: Parser[List[Token], Decl] =
    (p"val" ~ IdParser ~ p":" ~ p"Int" ~ p"=" ~ NumParser).map[Decl]{ case _ ~ y ~ _ ~ _ ~ _ ~ u => Const(y, u): Decl } ||
    (p"val" ~ IdParser ~ p":" ~ p"Double" ~ p"=" ~ FNumParser).map[Decl]{ case _ ~ y ~ _ ~ _ ~ _ ~ u => FConst(y, u): Decl } ||
    (p"def" ~ IdParser ~ p"(" ~ p")" ~ p":" ~ TypeParser ~ p"=" ~ Exp).map[Decl]{ case _ ~ y ~ _ ~ _ ~ _ ~ u ~ _ ~ w => Def(y, List(), u, w): Decl } ||
    (p"def" ~ IdParser ~ p"(" ~ ListParser(IdParser ~ p":" ~ NotVoidParser, p",") ~ p")" ~ p":" ~ TypeParser ~ p"=" ~ Exp).map[Decl]{ case _ ~ y ~ _ ~ u ~ _ ~ _ ~ w ~ _ ~ z => Def(y, u.map({case a ~ b ~ c => (a, c)}).toList, w, z): Decl}

lazy val Block: Parser[List[Token], List[Decl]] =
    (Defs ~ p";" ~ Block).map{ case y ~ _ ~ u => y :: u : List[Decl]} ||
    (Exp ~ p";" ~ Block).map{ case y ~ _ ~ u => Main(y) :: u : List[Decl]} ||
    (Exp.map[List[Decl]]{ s => List(Main(s)) })

def tokenise(s: String) : List[Token] = 
  lexing_simp(FUN_REGS, s).collect(token)

// val fact: List[Token] = tokenise(os.read(os.pwd / "fact.fun"))
// println(Block.parse_all(fact))

// val hanoi: List[Token] = tokenise(os.read(os.pwd / "hanoi.fun"))
// println(Block.parse_all(hanoi))

// val mand: List[Token] = tokenise(os.read(os.pwd / "mand.fun"))
// println(Block.parse_all(mand))

// val mand2: List[Token] = tokenise(os.read(os.pwd / "mand2.fun"))
// println(Block.parse_all(mand2))

// val sqr: List[Token] = tokenise(os.read(os.pwd / "sqr.fun"))
// println(Block.parse_all(sqr))