from pyparsing import (
    Forward,
    Keyword,
    Literal,
    delimitedList,
    infixNotation,
    oneOf,
    opAssoc,
    pyparsing_common,
)
from functools import reduce
from typing import Dict, Set, Type
from z3 import (
    And,
    ArithRef,
    BoolRef,
    BoolVal,
    Int,
    IntVal,
    Not,
    Or,
)


# An arith-structure gives meaning to numerals, addition, negation,
# and multiplcation.
class ArithStruct:
    @staticmethod
    def of_numeral(num: int) -> int:
        raise NotImplementedError()

    @staticmethod
    def add(left: int, right: int) -> int:
        raise NotImplementedError()

    @staticmethod
    def negate(expr: int) -> int:
        raise NotImplementedError()

    @staticmethod
    def mul(left: int, right: int) -> int:
        raise NotImplementedError()


class StdInt(ArithStruct):
    """The standard structure over the integers"""
    @staticmethod
    def of_numeral(num: int) -> int:
        return num

    @staticmethod
    def add(left: int, right: int) -> int:
        return left + right

    @staticmethod
    def negate(expr: int) -> int:
        return -expr

    @staticmethod
    def mul(left: int, right: int) -> int:
        return left * right


############################################################################
# Expressions are represented as a tree, where there is a different class for
# each type of node.  For example, an expression (x + 3*4) corresponds to a

#     +                                    ExprPlus
#   /   \                                   /   \
#  x    *     -- corresponding to --  ExprVar ExprMul
#      / \                                     /     \
#     3   4                           ExprNumeral  ExprNumeral
# Each expression class is equipped with the methods:
#    eval: takes in an arith-structure, a state (valuation over that structure), and
#          produces a value in the arith-structure
#    vars: the set of variables used in that expression
# to_term: encode the expression as a Z3 term
# Formulas are similar.
class Expr:
    def __str__(self) -> str:
        raise NotImplementedError()

    def vars(self) -> Set[str]:
        raise NotImplementedError()


class Term(Expr):
    def eval(self, struct: Type[ArithStruct], state: Dict[str, int]) -> int:
        raise NotImplementedError()

    def to_term(self) -> ArithRef:
        raise NotImplementedError()

    def to_time_term(self, times) -> ArithRef:
        raise NotImplementedError()


class Form(Expr):
    def eval(self, state: Dict[str, int]) -> int:
        raise NotImplementedError()

    def to_formula(self) -> BoolRef:
        raise NotImplementedError()

    def to_time_form(self, times: Dict[str, int]) -> BoolRef:
        raise NotImplementedError()


class ExprVar(Term):
    """Variables"""
    def __init__(self, name: str) -> None:
        self.name = name
        self.time = 0

    def eval(self, struct: Type[ArithStruct], state: Dict[str, int]) -> int:
        return state[self.name]

    def __str__(self) -> str:
        return self.name + (str(self.time) if self.time else "")

    def vars(self) -> Set[str]:
        return set([str(self)])

    def to_term(self) -> ArithRef:
        return Int(str(self))


class ExprNumeral(Term):
    """Numerals"""
    def __init__(self, value: int) -> None:
        self.value = value

    def eval(self, struct: Type[ArithStruct], state: Dict[str, int]) -> int:
        return struct.of_numeral(self.value)

    def __str__(self) -> str:
        return str(self.value)

    def vars(self) -> Set[str]:
        return set()

    def to_term(self) -> ArithRef:
        return IntVal(self.value)


class BinaryExpr(Expr):
    """Abstract class representing binary expressions"""
    def __init__(self, left: Expr, right: Expr) -> None:
        self.left = left
        self.right = right

    def vars(self) -> Set[str]:
        return self.left.vars() | self.right.vars()


class BinaryTermTerm(BinaryExpr, Term):
    def __init__(self, left: Term, right: Term) -> None:
        self.left: Term = left
        self.right: Term = right


class BinaryTermForm(BinaryExpr, Form):
    def __init__(self, left: Term, right: Term) -> None:
        self.left: Term = left
        self.right: Term = right


class BinaryFormForm(BinaryExpr, Form):
    def __init__(self, left: Form, right: Form) -> None:
        self.left: Form = left
        self.right: Form = right


class ExprPlus(BinaryTermTerm):
    """Addition"""
    def eval(self, struct: Type[ArithStruct], state: Dict[str, int]) -> int:
        return struct.add(self.left.eval(struct, state), self.right.eval(struct, state))

    def __str__(self) -> str:
        return "(" + str(self.left) + " + " + str(self.right) + ")"

    def to_term(self) -> ArithRef:
        return self.left.to_term() + self.right.to_term()


class ExprNeg(Term):
    """Negation"""
    def __init__(self, expr: Term) -> None:
        self.expr = expr

    def eval(self, struct: Type[ArithStruct], state: Dict[str, int]) -> int:
        return struct.negate(self.expr.eval(struct, state))

    def __str__(self) -> str:
        return "-(" + str(self.expr) + ")"

    def to_term(self) -> ArithRef:
        return -self.expr.to_term()

    def vars(self) -> Set[str]:
        return self.expr.vars()


class ExprMul(BinaryTermTerm):
    """Multiplication"""
    def eval(self, struct: Type[ArithStruct], state: Dict[str, int]) -> int:
        return struct.mul(self.left.eval(struct, state), self.right.eval(struct, state))

    def __str__(self) -> str:
        return "(" + str(self.left) + " * " + str(self.right) + ")"

    def to_term(self) -> ArithRef:
        return self.left.to_term() * self.right.to_term()


class FormLt(BinaryTermForm):
    """Strictly less-than"""
    def eval(self, state: Dict[str, int]) -> int:
        return self.left.eval(StdInt, state) < self.right.eval(StdInt, state)

    def __str__(self) -> str:
        return str(self.left) + " < " + str(self.right)

    def to_formula(self) -> BoolRef:
        return self.left.to_term() < self.right.to_term()


class FormEq(BinaryTermForm):
    """Equal to"""
    def eval(self, state: Dict[str, int]) -> int:
        return self.left.eval(StdInt, state) == self.right.eval(StdInt, state)

    def __str__(self) -> str:
        return str(self.left) + " == " + str(self.right)

    def to_formula(self) -> BoolRef:
        return self.left.to_term() == self.right.to_term()


class FormAnd(BinaryFormForm):
    """And"""
    def eval(self, state: Dict[str, int]) -> int:
        return self.left.eval(state) and self.right.eval(state)

    def __str__(self) -> str:
        return "(" + str(self.left) + " and " + str(self.right) + ")"

    def to_formula(self) -> BoolRef:
        return And(self.left.to_formula(), self.right.to_formula())


class FormOr(BinaryFormForm):
    """Or"""
    def eval(self, state: Dict[str, int]) -> int:
        return self.left.eval(state) or self.right.eval(state)

    def __str__(self) -> str:
        return "(" + str(self.left) + " or " + str(self.right) + ")"

    def to_formula(self) -> BoolRef:
        return Or(self.left.to_formula(), self.right.to_formula())


class FormNot(Form):
    """Not"""
    def __init__(self, phi: Form) -> None:
        self.phi = phi

    def eval(self, state: Dict[str, int]) -> int:
        return not (self.phi.eval(state))

    def __str__(self) -> str:
        return "not(" + str(self.phi) + ")"

    def vars(self) -> Set[str]:
        return self.phi.vars()

    def to_formula(self) -> BoolRef:
        return Not(self.phi.to_formula())


############################################################################
# Control flow
class Command:
    def vars(self) -> Set[str]:
        raise NotImplementedError()

    def __str__(self) -> str:
        raise NotImplementedError()

    def to_time_form(self, times: Dict[str, int]) -> BoolRef:
        raise NotImplementedError()


class CmdAssign(Command):
    """Variable assignment"""
    def __init__(self, lhs: str, rhs: Term) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def vars(self) -> Set[str]:
        return set([self.lhs]) | self.rhs.vars()

    def __str__(self) -> str:
        return "{} := {}".format(self.lhs, self.rhs)

    def to_time_form(self, times: Dict[str, int]) -> BoolRef:
        rhs = self.rhs.to_time_term(times)
        times[self.lhs] += 1
        lhs = mk_var(self.lhs).to_time_term(times)
        return lhs == rhs


class CmdAssume(Command):
    """Guard"""
    def __init__(self, condition: Form) -> None:
        self.condition = condition

    def vars(self) -> Set[str]:
        return self.condition.vars()

    def __str__(self) -> str:
        return "[{}]".format(self.condition)

    def to_time_form(self, times: Dict[str, int]) -> BoolRef:
        self.condition.to_time_form(times)


class CmdPrint(Command):
    """Print to stdout"""
    def __init__(self, expr: Expr) -> None:
        self.expr = expr

    def vars(self) -> Set[str]:
        return self.expr.vars()

    def __str__(self) -> str:
        return "print({})".format(self.expr)

    def to_time_form(self, times: Dict[str, int]) -> BoolRef:
        return BoolVal(False)


############################################################################
# Statements are program phrases that can change the state of the program.
# Again, each statement is equipped with three methods:
#  execute: takes in a state, and produces nothing (but may change the state
#           or print something!)
#       pp: take in an indentation level and pretty-print a string
#           representation of the statement
#   to_cfa: takes in a control flow automaton, a source vertex, and a target
#           vertex, and adds the statement to the control flow automaton
#           connecting source and target
# print_annotation: like pp, but additionally print an annotation
class Stmt:
    """Statements"""
    def __init__(self) -> None:
        self.entry = None

    def pp(self, indent: int) -> str:
        raise NotImplementedError()

    def print_annotation(self, annotation, indent):
        raise NotImplementedError()

    def to_cfa(self, cfa, u, v):
        raise NotImplementedError()

    def execute(self, struct, state):
        raise NotImplementedError()


class StmtAssign(Stmt):
    """Variable assignment"""
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def execute(self, state):
        state[self.lhs] = self.rhs.eval(StdInt, state)

    def pp(self, indent: int) -> str:
        return ("    " * indent) + self.lhs + " = " + str(self.rhs) + "\n"

    def print_annotation(self, annotation, indent):
        print(("    " * indent) + "{" + str(annotation[self.entry]) + "}")
        print(("    " * indent) + self.lhs + " = " + str(self.rhs))

    def to_cfa(self, cfa, u, v):
        self.entry = u
        cfa.add_edge(u, CmdAssign(self.lhs, self.rhs), v)


class StmtIf(Stmt):
    """Conditional statement"""
    def __init__(self, cond, bthen, belse):
        self.cond = cond
        self.bthen = bthen
        self.belse = belse

    def execute(self, state):
        if (self.cond.eval(state)):
            self.bthen.execute(state)
        else:
            self.belse.execute(state)

    def pp(self, indent: int) -> str:
        program = ("    " * indent) + "if " + str(self.cond) + ":\n"
        program += self.bthen.pp(indent + 1)
        program += ("    " * indent) + "else:\n"
        program += self.belse.pp(indent + 1)
        return program

    def print_annotation(self, annotation, indent):
        print(("    " * indent) + "{" + str(annotation[self.entry]) + "}")
        print(("    " * indent) + "if " + str(self.cond) + ":")
        self.bthen.print_annotation(annotation, indent + 1)
        print(("    " * indent) + "else:")
        self.belse.print_annotation(annotation, indent + 1)

    def to_cfa(self, cfa, u, v):
        self.entry = u
        then_target = cfa.fresh_vertex()
        else_target = cfa.fresh_vertex()
        cfa.add_edge(u, CmdAssume(self.cond), then_target)
        cfa.add_edge(u, CmdAssume(FormNot(self.cond)), else_target)
        self.bthen.to_cfa(cfa, then_target, v)
        self.belse.to_cfa(cfa, else_target, v)


class StmtBlock(Stmt):
    """Sequence of statements"""
    def __init__(self, block):
        self.block = block

    def execute(self, state):
        for stmt in self.block:
            stmt.execute(state)

    def pp(self, indent: int) -> str:
        return "".join(map(lambda x: x.pp(indent), self.block))

    def print_annotation(self, annotation, indent):
        for stmt in self.block:
            stmt.print_annotation(annotation, indent)

    def to_cfa(self, cfa, u, v):
        self.entry = u
        last = u
        for i in range(len(self.block) - 1):
            nxt = cfa.fresh_vertex()
            self.block[i].to_cfa(cfa, last, nxt)
            last = nxt
        self.block[len(self.block) - 1].to_cfa(cfa, last, v)


class StmtWhile(Stmt):
    """While loop"""
    def __init__(self, cond, body):
        self.cond = cond
        self.body = body

    def execute(self, state):
        while self.cond.eval(state):
            self.body.execute(state)

    def pp(self, indent: int) -> str:
        program = ("    " * indent) + "while " + str(self.cond) + ":\n"
        program += self.body.pp(indent + 1)
        return program

    def print_annotation(self, annotation, indent):
        print(("    " * indent) + "{" + str(annotation[self.entry]) + "}")
        print(("    " * indent) + "while " + str(self.cond) + ":")
        self.body.print_annotation(annotation, indent + 1)

    def to_cfa(self, cfa, u, v):
        self.entry = u
        w = cfa.fresh_vertex()
        cfa.add_edge(u, CmdAssume(self.cond), w)
        cfa.add_edge(u, CmdAssume(FormNot(self.cond)), v)
        self.body.to_cfa(cfa, w, u)


class StmtPrint(Stmt):
    """Print to stdout"""
    def __init__(self, expr):
        self.expr = expr

    def execute(self, state):
        print(self.expr.eval(StdInt, state))

    def pp(self, indent: int) -> str:
        return ("    " * indent) + "print(" + str(self.expr) + ")\n"

    def to_cfa(self, cfa, u, v):
        self.entry = u
        cfa.add_edge(u, CmdPrint(self.expr), v)

    def print_annotation(self, annotation, indent):
        print(("    " * indent) + "{" + str(annotation[self.entry]) + "}")
        print(("    " * indent) + "print(" + str(self.expr) + ")")
############################################################################


def mk_numeral(toks):
    return [ExprNumeral(int(toks[0]))]


def mk_var(toks):
    return [ExprVar(str(toks[0]))]


def mk_plus_minus(toks):
    curr = toks[0][0]
    for i in range(1, len(toks[0]), 2):
        if toks[0][i] == "+":
            curr = ExprPlus(curr, toks[0][i + 1])
        else:
            curr = ExprPlus(curr, ExprNeg(toks[0][i + 1]))
    return [curr]


def mk_mul(toks):
    return [reduce(ExprMul, toks[0][0::2])]


def mk_neg(toks):
    return [ExprNeg(toks[0][1])]


def mk_not(toks):
    return [FormNot(toks[0][1])]


def mk_and(toks):
    return [reduce(FormAnd, toks[0][0::2])]


def mk_or(toks):
    return [reduce(FormOr, toks[0][0::2])]


def mk_atom(toks):
    if toks[1] == "=":
        return FormEq(toks[0], toks[2])
    elif toks[1] == "<":
        return FormLt(toks[0], toks[2])
    else:
        return FormOr(FormLt(toks[0], toks[2]),
                      FormEq(toks[0], toks[2]))


def mk_assign(toks):
    return StmtAssign(str(toks[0]), toks[2])


def mk_block(toks):
    if len(toks) == 1:
        return toks[0]
    else:
        return StmtBlock(toks)


def mk_while(toks):
    return StmtWhile(toks[1], toks[2])


def mk_if(toks):
    return StmtIf(toks[1], toks[2], toks[3])


def mk_print(toks):
    return StmtPrint(toks[1])


integer = pyparsing_common.signed_integer
varname = pyparsing_common.identifier
var = pyparsing_common.identifier
integer.setParseAction(mk_numeral)
var.setParseAction(mk_var)

expr = infixNotation(integer | var,
                     [('-', 1, opAssoc.RIGHT, mk_neg),
                      ('*', 2, opAssoc.LEFT, mk_mul),
                      (oneOf('+ -'), 2, opAssoc.LEFT, mk_plus_minus)])

atom = expr + (Literal("<=") | Literal("<") | Literal("=")) + expr
atom.setParseAction(mk_atom)

formula = infixNotation(atom,
                        [("not", 1, opAssoc.RIGHT, mk_not),
                         ("and", 2, opAssoc.LEFT, mk_and),
                         ("or", 2, opAssoc.LEFT, mk_or)])


block = Forward()
assign_stmt = varname + ":=" + expr
if_stmt = Keyword("if") + formula + block + Keyword("else").suppress() + block
while_stmt = Keyword("while") + formula + block
print_stmt = Literal("print") + Literal('(').suppress() + expr + Literal(')').suppress()
stmt = if_stmt ^ while_stmt ^ print_stmt ^ assign_stmt
block << Literal('{').suppress() + delimitedList(stmt, delim=';') + Literal('}').suppress()
program = delimitedList(stmt, delim=';')
assign_stmt.setParseAction(mk_assign)
if_stmt.setParseAction(mk_if)
while_stmt.setParseAction(mk_while)
block.setParseAction(mk_block)
print_stmt.setParseAction(mk_print)
program.setParseAction(mk_block)
