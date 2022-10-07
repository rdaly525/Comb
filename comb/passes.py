import typing as tp
from .ast import Comb, Expr, Sym, QSym, Stmt, DeclStmt, ASTCombProgram, ASTAssignStmt, ParamDecl, TypeCall, \
    IntType, InDecl, Type, OutDecl, ASTCallExpr, IntValue, _CallExpr, BoolType, Obj, Node, _list_to_str
from .ir import CombProgram, AssignStmt, CallExpr
from DagVisitor import Visitor
from .stdlib import GlobalModules
class SymRes(Visitor):

    def run(self, node: Node):
        assert isinstance(node, Node)
        self._dag_cache = set()
        self.new_node = {}
        self.visit(node)
        return self.new_node[node]

    def generic_visit(self, node):
        Visitor.generic_visit(self, node)
        self.new_node[node] = node

    def visit_DeclStmt(self, node: DeclStmt):
        Visitor.generic_visit(self, node)
        self.new_node[node] = type(node)(node.sym, self.new_node[node.type])

    def visit_QSym(self, qsym: QSym):
        if qsym.module not in GlobalModules:
            raise ValueError("Missing module ", qsym.module)
        self.new_node[qsym] = GlobalModules[qsym.module].comb_from_sym(qsym)

    def visit_ASTCallExpr(self, expr: ASTCallExpr):
        Visitor.generic_visit(self, expr)
        call_comb = self.new_node[expr.qsym]
        new_pargs = [self.new_node[arg] for arg in expr.pargs]
        new_args = [self.new_node[arg] for arg in expr.args]
        new_expr = CallExpr(call_comb, new_pargs, new_args)
        self.new_node[expr] = new_expr

    def visit_TypeCall(self, node: TypeCall):
        Visitor.generic_visit(self, node)
        new_pargs = [self.new_node[parg] for parg in node.pargs]
        new_T = TypeCall(self.new_node[node.type], new_pargs)
        self.new_node[node] = new_T

    def visit_ASTAssignStmt(self, node: ASTAssignStmt):
        Visitor.generic_visit(self, node)
        new_rhss = [self.new_node[rhs] for rhs in node.rhss]
        new_lhss = [self.new_node[lhs] for lhs in node.lhss]
        new_stmt = AssignStmt(new_lhss, new_rhss)
        self.new_node[node] = new_stmt

    def visit_ASTCombProgram(self, acomb: ASTCombProgram):
        Visitor.generic_visit(self, acomb)
        new_stmts = [self.new_node[stmt] for stmt in acomb.stmts]
        self.new_node[acomb] = CombProgram(acomb.name, new_stmts)

    def visit_Obj(self, obj: Obj):
        return Obj([self.new_node[comb] for comb in obj])

class VerifyNoAST(Visitor):
    def run(self, node):
        self._dag_cache = set()
        self.visit(node)

    def generic_visit(self, node):
        Visitor.generic_visit(self, node)
        if isinstance(node, (ASTCallExpr, ASTAssignStmt, ASTCombProgram)):
            raise ValueError("Bad")
