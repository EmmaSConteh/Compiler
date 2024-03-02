// CW3
//=====
//
// The main idea is to extend the parser form the lectures 
// (which processes strings) to a parser that processes
// tokens. For this you need to use the lexer from CW2 and
// possibly adjust the lexing regular expressions accordingly.

import $file.cw02, cw02._
import cw02.Token

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
    case (T_ID(str)) :: tail if str == s => Set((str, tail))
    case (T_NUM(n)) :: tail if n.toString == s => Set((n.toString, tail))
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

extension (sc: StringContext) 
  def p(args: Any*) = TokenParser(sc.s(args:_*))


// more convenient syntax for parser combinators
extension [I : IsSeq, T](p: Parser[I, T]) {
  def ||(q : => Parser[I, T]) = new AltParser[I, T](p, q)
  def ~[S] (q : => Parser[I, S]) = new SeqParser[I, T, S](p, q)
  def map[S](f: => T => S) = new MapParser[I, T, S](p, f)
}

// the abstract syntax trees for the WHILE language
abstract class Stmt
abstract class AExp
abstract class BExp 

type Block = List[Stmt]

case object Skip extends Stmt
case class If(a: BExp, bl1: Block, bl2: Block) extends Stmt
case class While(b: BExp, bl: Block) extends Stmt
case class Assign(s: String, a: AExp) extends Stmt
case class Read(s: String) extends Stmt
case class WriteId(s: String) extends Stmt  // for printing values of variables
case class WriteString(s: String) extends Stmt  // for printing words
case class For(i: String, from: AExp, to: AExp, bl: Block) extends Stmt
case object Break extends Stmt

case class Var(s: String) extends AExp
case class Num(i: Int) extends AExp
case class Aop(o: String, a1: AExp, a2: AExp) extends AExp

case object True extends BExp
case object False extends BExp
case class Bop(o: String, a1: AExp, a2: AExp) extends BExp
case class Lop(o: String, b1: BExp, b2: BExp) extends BExp
case class And(b1: BExp, b2: BExp) extends BExp
case class Or(b1: BExp, b2: BExp) extends BExp

//AExp
lazy val AExp: Parser[List[Token], AExp] = 
  (Te ~ p"+" ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("+", x, z) } ||
  (Te ~ p"-" ~ AExp).map[AExp]{ case x ~ _ ~ z => Aop("-", x, z) } || Te
lazy val Te: Parser[List[Token], AExp] = 
  (Fa ~ p"*" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("*", x, z) } || 
  (Fa ~ p"/" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("/", x, z) } ||
  (Fa ~ p"%" ~ Te).map[AExp]{ case x ~ _ ~ z => Aop("%", x, z) } ||  Fa  
lazy val Fa: Parser[List[Token], AExp] = 
   (p"(" ~ AExp ~ p")").map{ case _ ~ y ~ _ => y } || 
   IdParser.map(Var(_)) || 
   NumParser.map(Num(_))

lazy val BExp: Parser[List[Token], BExp] =
   (BTe ~ p"&&" ~ BExp).map[BExp]{ case x ~ _ ~ z => And(x, z) } ||
   (BTe ~ p"||" ~ BExp).map[BExp]{ case x ~ _ ~ z => Or(x, z) } || BTe
lazy val BTe: Parser[List[Token], BExp] =
   (AExp ~ p"==" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("==", x, z) } || 
   (AExp ~ p"!=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("!=", x, z) } || 
   (AExp ~ p"<" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<", x, z) } || 
   (AExp ~ p">" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">", x, z) } ||
   (AExp ~ p"<=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop("<=", x, z) } ||
   (AExp ~ p">=" ~ AExp).map[BExp]{ case x ~ _ ~ z => Bop(">=", x, z) } || BFa
lazy val BFa: Parser[List[Token], BExp] =
   (p"true".map[BExp]{ _ => True }) || 
   (p"false".map[BExp]{ _ => False }) ||
   (p"(" ~ BExp ~ p")").map{ case _ ~ x ~ _ => x }

// single statement
lazy val Stmt: Parser[List[Token], Stmt] =
  ((p"skip".map[Stmt]{_ => Skip }) ||
   (IdParser ~ p":=" ~ AExp).map[Stmt]{ case x ~ _ ~ z => Assign(x, z) } ||
   (IdParser ~ p":=" ~ IdParser).map[Stmt]{ case x ~ _ ~ z => Assign(x, Var(z)) } ||
   (p"write" ~ p"(" ~ IdParser ~ p")").map[Stmt]{ case _ ~ _ ~ y ~ _ => WriteId(y) } ||
   (p"write(" ~ IdParser ~ p")").map[Stmt]{ case _ ~ y ~ _ => WriteId(y) } ||
   (p"write" ~ IdParser).map[Stmt]{ case _ ~ y => WriteId(y) } ||
   (p"write" ~ p"(" ~ StrParser ~ p")").map[Stmt]{ case _ ~ _ ~ y ~ _ => WriteId(y) } ||
   (p"write(" ~ StrParser ~ p")").map[Stmt]{ case _ ~ y ~ _ => WriteString(y) } ||
   (p"write" ~ StrParser).map[Stmt]{ case _ ~ y => WriteString(y) } ||
   (p"read" ~ p"(" ~ IdParser ~ p")").map[Stmt]{ case _ ~ _ ~ y ~ _ => Read(y) } ||
   (p"read(" ~ IdParser ~ p")").map[Stmt]{ case _ ~ y ~ _ => Read(y) } ||
   (p"read" ~ IdParser).map[Stmt]{ case _ ~ y => Read(y)} ||
   (p"if" ~ BExp ~ p"then" ~ Block ~ p"else" ~ Block)
     .map[Stmt]{ case _ ~ y ~ _ ~ u ~ _ ~ w => If(y, u, w) } ||
   (p"while" ~ BExp ~ p"do" ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ w => While(y, w) } ||
   (p"for" ~ IdParser ~ p":=" ~ AExp ~ p"upto" ~ AExp ~ p"do" ~ Block).map[Stmt]{ case _ ~ y ~ _ ~ u ~ _ ~ w ~ _ ~ x => For(y, u, w, x) } ||
   (p"break".map[Stmt]{_ => Break })
   )
 
 //compound statement
lazy val Stmts: Parser[List[Token], Block] =
  (Stmt ~ p";" ~ Stmts).map[Block]{ case x ~ _ ~ z => x :: z } ||
  (Stmt.map[Block]{ s => List(s) })

// blocks (enclosed in curly braces)
lazy val Block: Parser[List[Token], Block] =
  ((p"{" ~ Stmts ~ p"}").map{ case _ ~ y ~ _ => y } || 
   (Stmt.map(s => List(s))))

// Tests

// val x = "if (a < b) then skip else a := a * b + 1" 
// println("x")
// println((tokenise(x)))

// val inputTokens: List[Token] = List(
//   T_PAREN("("),
//   T_NUM(2),
//   T_OP("+"),
//   T_NUM(3),
//   T_OP("=="),
//   T_NUM(5),
//   T_PAREN(")"),
//   T_OP("&&"),
//   T_PAREN("("),
//   T_NUM(4),
//   T_OP("<"),
//   T_NUM(6),
//   T_PAREN(")")
// )

// val inputTokens2: List[Token] = List(
//   T_ID("n"),
//   T_OP(":="), 
//   T_NUM(2), 
//   T_SEMI, 
//   T_KEYWORD("while"), 
//   T_PAREN("("), 
//   T_ID("n"), 
//   T_OP("<"), 
//   T_ID("end"), 
//   T_PAREN(")"), 
//   T_KEYWORD("do"), 
//   T_PAREN("{"),
//   T_ID("f"), 
//   T_OP(":="), 
//   T_NUM(2),
//   T_PAREN("}")
// )

// println(Stmts.parse_all(inputTokens))
// println(Stmts.parse_all(inputTokens2))

// val primes: List[Token] = tokenise(os.read(os.pwd / "primes.while"))
// val factors: List[Token] = tokenise(os.read(os.pwd / "factors.while"))
// val fib: List[Token] = tokenise(os.read(os.pwd / "fib.while"))
// val loops: List[Token] = tokenise(os.read(os.pwd / "loops.while"))
// val collatz: List[Token] = tokenise(os.read(os.pwd / "collatz.while"))
// val collatz2: List[Token] = tokenise(os.read(os.pwd / "collatz2.while"))

// println(Stmts.parse_all(primes))
// println(Stmts.parse_all(factors))
// println(Stmts.parse_all(fib))
// println(Stmts.parse_all(loops))
// println(Stmts.parse_all(collatz))
// println(Stmts.parse_all(collatz2))

// // Interpreter
// //=============

// // Import needed to take int as input from the user
import scala.io.StdIn.readInt

type Env = Map[String, Int]

def eval_aexp(a: AExp, env: Env) : Int = a match {
  case Num(n) => n
  case Var(id) => env(id)
  case Aop("+", a1, a2) => eval_aexp(a1, env) + eval_aexp(a2, env)
  case Aop("-", a1, a2) => eval_aexp(a1, env) - eval_aexp(a2, env)
  case Aop("*", a1, a2) => eval_aexp(a1, env) * eval_aexp(a2, env)
  case Aop("/", a1, a2) => eval_aexp(a1, env) / eval_aexp(a2, env)
  case Aop("%", a1, a2) => eval_aexp(a1, env) % eval_aexp(a2, env)

}

def eval_bexp(b: BExp, env: Env) : Boolean = b match {
  case Bop("==", b1, b2) => eval_aexp(b1, env) == eval_aexp(b2, env)
  case Bop("!=", b1, b2) => eval_aexp(b1, env) != eval_aexp(b2, env)
  case Bop("<", b1, b2) => eval_aexp(b1, env) < eval_aexp(b2, env)
  case Bop(">", b1, b2) => eval_aexp(b1, env) > eval_aexp(b2, env)
  case Bop("<=", b1, b2) => eval_aexp(b1, env) <= eval_aexp(b2, env)
  case Bop(">=", b1, b2) => eval_aexp(b1, env) >= eval_aexp(b2, env)
  case Lop("&&", b1, b2) => eval_bexp(b1, env) && eval_bexp(b2, env)
  case Lop("||", b1, b2) => eval_bexp(b1, env) || eval_bexp(b2, env)
  case True => true
  case False => false

}

def eval_stmt(s: Stmt, env: Env) : Env = s match {
  case Skip => env
  case Assign(id, a) => env + (id -> eval_aexp(a, env))
  case WriteId(id) => if (env.contains(id)) { println(env(id))} //change to print collatz2.while
    env
  case WriteString(s) => print(StringContext.treatEscapes(s).substring(1, StringContext.treatEscapes(s).length - 1))
    env
  case Read(id) => env + (id -> readInt())
  case If(b, bl, blk) => 
    if (eval_bexp(b, env)) eval_bl(bl, env) 
      else eval_bl(blk, env)
  case While(b, bl) => 
    if (eval_bexp(b, env)) eval_stmt(While(b, bl), eval_bl(bl, env)) 
      else env
}

def eval_bl(bl: Block, env: Env) : Env = bl match{
  case Nil => env
  case s :: bl => eval_bl(bl, eval_stmt(s, env))
}

def eval(bl: Block) : Env = eval_bl(bl, Map())

// val contents = os.read(os.pwd / "primes.while")
// // println(s"Lex $file: ")
// println(tokenise(contents))
// // println(s"Parse $file: ")
// println(Stmts.parse_all(tokenise(contents)).head)
// // println(s"Eval $file: ")
// println(eval(Stmts.parse_all(tokenise(contents)).head))

// tests

// println(eval(Stmts.parse_all(tokenise(os.read(os.pwd / "primes.while"))).head))
// println(eval(Stmts.parse_all(tokenise(os.read(os.pwd / "factors.while"))).head))
// println(eval(Stmts.parse_all(tokenise(os.read(os.pwd / "fib.while"))).head))
// println(eval(Stmts.parse_all(tokenise(os.read(os.pwd / "loops.while"))).head))
// println(eval(Stmts.parse_all(tokenise(os.read(os.pwd / "forloop1.while"))).head))
// println(eval(Stmts.parse_all(tokenise(os.read(os.pwd / "collatz2.while"))).head))

// // sample output for primes.while
// /*
// 2
// 3
// 5
// 7
// 11
// 13
// 17
// 19
// 23
// 29
// 31
// 37
// 41
// 43
// 47
// 53
// 59
// 61
// 67
// 71
// 73
// 79
// 83
// 89
// 97
// Map(end -> 100, n -> 100, f -> 4, tmp -> 1)
// */

