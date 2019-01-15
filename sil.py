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
from z3 import (
    And,
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
    def of_numeral(num):
        raise NotImplementedError()

    @staticmethod
    def add(left, right):
        raise NotImplementedError()

    @staticmethod
    def negate(expr):
        raise NotImplementedError()

    @staticmethod
    def mul(left, right):
        raise NotImplementedError()


class StdInt(ArithStruct):
    """The standard structure over the integers"""
    @staticmethod
    def of_numeral(num):
        return num

    @staticmethod
    def add(left, right):
        return left + right

    @staticmethod
    def negate(expr):
        return -expr

    @staticmethod
    def mul(left, right):
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
#    eval: takes in an arith-structure, a state (valuation over that structure),
#          and produces a value in the arith-structure
#    vars: the set of variables used in that expression
# to_term: encode the expression as a Z3 term
# Formulas are similar.
class Expr:
    def __str__(self):
        raise NotImplementedError()

    def vars(self):
        raise NotImplementedError()


class Term(Expr):
    def eval(self, struct, state):
        raise NotImplementedError()

    def __str__(self):
        return str(self.to_term())

    def to_term(self, times=None):
        raise NotImplementedError()


class Form(Expr):
    def eval(self, state):
        raise NotImplementedError()

    def __str__(self):
        return str(self.to_formula())

    def to_formula(self, times=None):
        raise NotImplementedError()


class ExprVar(Term):
    """Variables"""
    def __init__(self, name):
        self.name = name

    def eval(self, struct, state):
        return state[self.name]

    def __str__(self):
        return self.name

    def vars(self):
        return set([str(self)])

    def to_term(self, times=None):
        return Int(str(self) + "'" * (0 if times is None else times[str(self)]))


class ExprNumeral(Term):
    """Numerals"""
    def __init__(self, value):
        self.value = value

    def eval(self, struct, state):
        return struct.of_numeral(self.value)

    def __str__(self):
        return str(self.value)

    def vars(self):
        return set()

    def to_term(self, times=None):
        return IntVal(self.value)


class BinaryExpr(Expr):
    """Abstract class representing binary expressions"""
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def vars(self):
        return self.left.vars() | self.right.vars()


class BinaryTermTerm(BinaryExpr, Term):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class BinaryTermForm(BinaryExpr, Form):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class BinaryFormForm(BinaryExpr, Form):
    def __init__(self, left, right):
        self.left = left
        self.right = right


class ExprPlus(BinaryTermTerm):
    """Addition"""
    def eval(self, struct, state):
        return struct.add(
            self.left.eval(struct, state),
            self.right.eval(struct, state),
        )

    def __str__(self):
        return "(" + str(self.left) + " + " + str(self.right) + ")"

    def to_term(self, times=None):
        return self.left.to_term(times) + self.right.to_term(times)


class ExprNeg(Term):
    """Negation"""
    def __init__(self, expr):
        self.expr = expr

    def eval(self, struct, state):
        return struct.negate(self.expr.eval(struct, state))

    def __str__(self):
        return "-(" + str(self.expr) + ")"

    def to_term(self, times=None):
        return -self.expr.to_term(times)

    def vars(self):
        return self.expr.vars()


class ExprMul(BinaryTermTerm):
    """Multiplication"""
    def eval(self, struct, state):
        return struct.mul(
            self.left.eval(struct, state),
            self.right.eval(struct, state),
        )

    def __str__(self):
        return "(" + str(self.left) + " * " + str(self.right) + ")"

    def to_term(self, times=None):
        return self.left.to_term(times) * self.right.to_term(times)


class FormLt(BinaryTermForm):
    """Strictly less-than"""
    def eval(self, state):
        return self.left.eval(StdInt, state) < self.right.eval(StdInt, state)

    def __str__(self):
        return str(self.left) + " < " + str(self.right)

    def to_formula(self, times=None):
        return self.left.to_term(times) < self.right.to_term(times)


class FormEq(BinaryTermForm):
    """Equal to"""
    def eval(self, state):
        return self.left.eval(StdInt, state) == self.right.eval(StdInt, state)

    def __str__(self):
        return str(self.left) + " == " + str(self.right)

    def to_formula(self, times=None):
        return self.left.to_term(times) == self.right.to_term(times)


class FormAnd(BinaryFormForm):
    """And"""
    def eval(self, state):
        return self.left.eval(state) and self.right.eval(state)

    def __str__(self):
        return "(" + str(self.left) + " and " + str(self.right) + ")"

    def to_formula(self, times=None):
        return And(self.left.to_formula(times), self.right.to_formula(times))


class FormOr(BinaryFormForm):
    """Or"""
    def eval(self, state):
        return self.left.eval(state) or self.right.eval(state)

    def __str__(self):
        return "(" + str(self.left) + " or " + str(self.right) + ")"

    def to_formula(self, times=None):
        return Or(self.left.to_formula(times), self.right.to_formula(times))


class FormNot(Form):
    """Not"""
    def __init__(self, phi):
        self.phi = phi

    def eval(self, state):
        return not (self.phi.eval(state))

    def __str__(self):
        return "not(" + str(self.phi) + ")"

    def vars(self):
        return self.phi.vars()

    def to_formula(self, times=None):
        return Not(self.phi.to_formula(times))


############################################################################
# Control flow
class Command:
    def vars(self):
        raise NotImplementedError()

    def __str__(self):
        raise NotImplementedError()

    def __repr__(self):
        return "{}('{}')".format(self.__class__.__name__, str(self))

    def to_formula(self, times=None):
        raise NotImplementedError()


class CmdAssign(Command):
    """Variable assignment"""
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def vars(self):
        return set([str(self.lhs)]) | self.rhs.vars()

    def __str__(self):
        return "{} := {}".format(self.lhs, self.rhs)

    def to_formula(self, times=None):
        rhs = self.rhs.to_term(times)
        if times is not None:
            times[str(self.lhs)] += 1

        lhs = self.lhs.to_term(times)
        return lhs == rhs


class CmdAssume(Command):
    """Guard"""
    def __init__(self, condition):
        self.condition = condition

    def vars(self):
        return self.condition.vars()

    def __str__(self):
        return "[{}]".format(self.condition)

    def to_formula(self, times=None):
        return self.condition.to_formula(times)


class CmdPanic(Command):
    """Panic!"""
    def vars(self):
        return set()

    def __str__(self):
        return "panic()"

    def to_formula(self, times=None):
        return BoolVal(True)


class CmdPrint(Command):
    """Print to stdout"""
    def __init__(self, expr):
        self.expr = expr

    def vars(self):
        return self.expr.vars()

    def __str__(self):
        return "print({})".format(self.expr)

    def to_formula(self, times=None):
        return BoolVal(False)


# Control flow automaton: directed graph with a command labelling each edge
class ControlFlowAutomaton:
    def __init__(self):
        self.max_loc = 0
        self.succs = {}
        self.labels = {}
        self.entry = 0
        self.loc_entry = self.fresh_vertex()
        self.loc_exit = self.fresh_vertex()
        self.loc_panic = self.fresh_vertex()

    def fresh_vertex(self):
        v = self.max_loc
        self.max_loc = v + 1
        self.succs[v] = set()
        return v

    def add_edge(self, u, cmd, v):
        self.succs[u].add(v)
        self.labels[(u, v)] = cmd

    def successors(self, v):
        """Set of all successors of a given vertex"""
        return self.succs[v]

    def command(self, u, v):
        """The command associated with a given edge"""
        return self.labels[(u, v)]

    def vars(self):
        """The set of variables that appear in the CFA"""
        vars = set()
        for command in self.labels.values():
            vars = vars | command.vars()
        return vars

    def locations(self):
        """The set of locations (vertices) in the CFA"""
        return set(range(self.max_loc))

############################################################################


class Annotation:
    def get_entry(self, loc, indent=0):
        raise NotImplementedError()

    @staticmethod
    def analyze(stmt):
        raise NotImplementedError()


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
    def __init__(self):
        self.entry = None

    def __str__(self, indent=0):
        raise NotImplementedError()

    def annotation(self, annotation, indent=0):
        raise NotImplementedError()

    def to_cfa(self, cfa, u, v):
        raise NotImplementedError()

    def execute(self, state):
        raise NotImplementedError()


class StmtAssign(Stmt):
    """Variable assignment"""
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def execute(self, state):
        state[str(self.lhs)] = self.rhs.eval(StdInt, state)

    def __str__(self, indent=0):
        return ("    " * indent) + str(self.lhs) + " = " + str(self.rhs)

    def annotation(self, annotation, indent=0):
        assert self.entry is not None
        return "{0}{{{1}\n{0}}}\n{2}".format(
            "    " * indent,
            annotation.get_entry(self.entry, indent),
            self.__str__(indent),
        )

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

    def __str__(self, indent=0):
        program = ("    " * indent) + "if " + str(self.cond) + ":\n"
        program += self.bthen.__str__(indent + 1) + "\n"
        program += ("    " * indent) + "else:\n"
        program += self.belse.__str__(indent + 1)
        return program

    def annotation(self, annotation, indent=0):
        assert self.entry is not None
        return "{0}{{{1}\n{0}}}\n{0}if {2}:\n{3}\n{0}else:\n{4}".format(
            "    " * indent,
            annotation.get_entry(self.entry, indent),
            str(self.cond),
            self.bthen.annotation(annotation, indent + 1),
            self.belse.annotation(annotation, indent + 1),
        )

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

    def __str__(self, indent=0):
        return "\n".join(map(lambda x: x.__str__(indent), self.block))

    def annotation(self, annotation, indent=0):
        assert self.entry is not None
        return "\n".join(
            stmt.annotation(annotation, indent)
            for stmt in self.block
        )

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

    def __str__(self, indent=0):
        program = ("    " * indent) + "while " + str(self.cond) + ":\n"
        program += self.body.__str__(indent + 1)
        return program

    def annotation(self, annotation, indent=0):
        assert self.entry is not None
        return "{0}{{{1}\n{0}}}\n{0}while {2}:\n{3}".format(
            "    " * indent,
            str(annotation.get_entry(self.entry, indent)),
            str(self.cond),
            self.body.annotation(annotation, indent + 1),
        )

    def to_cfa(self, cfa, u, v):
        self.entry = u
        w = cfa.fresh_vertex()
        cfa.add_edge(u, CmdAssume(self.cond), w)
        cfa.add_edge(u, CmdAssume(FormNot(self.cond)), v)
        self.body.to_cfa(cfa, w, u)


class StmtPanic(Stmt):
    """Panic"""
    def __str__(self, indent=0):
        return ("    " * indent) + "panic()"

    def annotation(self, annotation, indent=0):
        assert self.entry is not None
        return "{0}{{{1}\n{0}}}\n{0}panic()".format(
            "    " * indent,
            str(annotation.get_entry(self.entry, indent)),
        )

    def to_cfa(self, cfa, u, v):
        self.entry = u
        cfa.add_edge(u, CmdPanic(), cfa.loc_panic)

    def execute(self, state):
        raise RuntimeError("Program threw exception")


class StmtPrint(Stmt):
    """Print to stdout"""
    def __init__(self, expr):
        self.expr = expr

    def execute(self, state):
        print(self.expr.eval(StdInt, state))

    def __str__(self, indent=0):
        return ("    " * indent) + "print(" + str(self.expr) + ")"

    def annotation(self, annotation, indent=0):
        assert self.entry is not None
        return "{0}{{{1}\n{0}}}\n{0}print({2})".format(
            "    " * indent,
            str(annotation.get_entry(self.entry, indent)),
            str(self.expr),
        )

    def to_cfa(self, cfa, u, v):
        self.entry = u
        cfa.add_edge(u, CmdPrint(self.expr), v)
############################################################################


def mk_numeral(toks):
    return [ExprNumeral(int(toks[0]))]


def mk_var(toks):
    return [ExprVar(toks[0])]


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
        return FormOr(
            FormLt(toks[0], toks[2]),
            FormEq(toks[0], toks[2]),
        )


def mk_panic(toks):
    return StmtPanic()


def mk_assign(toks):
    return StmtAssign(toks[0], toks[2])


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

expr = infixNotation(
    integer | var,
    [
        ('-', 1, opAssoc.RIGHT, mk_neg),
        ('*', 2, opAssoc.LEFT, mk_mul),
        (oneOf('+ -'), 2, opAssoc.LEFT, mk_plus_minus),
    ],
)

atom = expr + (Literal("<=") | Literal("<") | Literal("=")) + expr
atom.setParseAction(mk_atom)

formula = infixNotation(
    atom,
    [
        ("not", 1, opAssoc.RIGHT, mk_not),
        ("and", 2, opAssoc.LEFT, mk_and),
        ("or", 2, opAssoc.LEFT, mk_or),
    ],
)


block = Forward()
assign_stmt = varname + ":=" + expr
if_stmt = Keyword("if") + formula + block + Keyword("else").suppress() + block
while_stmt = Keyword("while") + formula + block
panic_stmt = Literal("panic") + Literal('(').suppress() + Literal(')').suppress()
print_stmt = (
    Literal("print")
) + (
    Literal('(').suppress()
) + (
    expr
) + (
    Literal(')').suppress()
)
stmt = if_stmt ^ while_stmt ^ print_stmt ^ assign_stmt ^ panic_stmt
block << (
    Literal('{').suppress()
) + (
    delimitedList(stmt, delim=';')
) + (
    Literal('}').suppress()
)
program = delimitedList(stmt, delim=';')
panic_stmt.setParseAction(mk_panic)
assign_stmt.setParseAction(mk_assign)
if_stmt.setParseAction(mk_if)
while_stmt.setParseAction(mk_while)
block.setParseAction(mk_block)
print_stmt.setParseAction(mk_print)
program.setParseAction(mk_block)
