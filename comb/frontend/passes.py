from comb.frontend.ast import Expr, Sym, QSym, DeclStmt, ASTCombProgram, ASTAssignStmt, ParamDecl, TypeCall, \
    IntType, InDecl, OutDecl, ASTCallExpr, IntValue, BoolType, ASTObj, Node
from comb.frontend.ir import CombProgram, AssignStmt, CallExpr, _flat, Obj
from comb.synth.utils import _make_list
from DagVisitor import Visitor
from comb.frontend.stdlib import GlobalModules
import typing as tp

class SymRes(Visitor):

    def __init__(self, modules, objs:tp.List[Obj]=[]):
        self.modules = modules
        self.eobjs = objs

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
        if qsym.module in GlobalModules:
            comb = GlobalModules[qsym.module].comb_from_sym(qsym)
        elif qsym.module in self.modules:
            comb = self.modules[qsym.module].comb_from_sym(qsym)
        else:
            comb = None
            for eobj in self.eobjs:
                comb = eobj.get(qsym.module, qsym.name)
                if comb is not None:
                    break
            if comb is None:
                raise ValueError("Missing qsym ", qsym)
        self.new_node[qsym] = comb

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
        new_T = TypeCall(node.type, new_pargs)
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
        comb = CombProgram(acomb.name, new_stmts)
        self.new_node[acomb] = comb
        #Add comb to module
        assert comb.name.module in self.modules
        self.modules[comb.name.module]._add_comb(comb)

    def visit_ASTObj(self, aobj: ASTObj):
        Visitor.generic_visit(self, aobj)
        new_combs = [self.new_node[comb] for comb in aobj.combs]
        self.new_node[aobj] = Obj(new_combs)

class VerifyNoAST(Visitor):
    def run(self, node):
        self._dag_cache = set()
        self.visit(node)

    def generic_visit(self, node):
        Visitor.generic_visit(self, node)
        if isinstance(node, (ASTCallExpr, ASTAssignStmt, ASTCombProgram)):
            raise ValueError("Bad")


class EvalCombProgram(Visitor):
    def run(self, comb: 'CombProgram', pargs, args):
        self._dag_cache = set()
        self.comb = comb
        self.pargs = pargs
        self.args = args
        self.pi = 0
        self.ai = 0
        self.expr_to_vals = {}
        self.type_to_type = {}
        self.expr_to_types = {}
        self.output_to_type = {}
        self.input_types = []
        self.output_types = []
        self.visit(comb)

    def outputs(self):
        outs = []
        for stmt in self.comb.stmts:
            if isinstance(stmt, OutDecl):
                outs.append(self.expr_to_vals[stmt.sym])
        return _flat(outs)

    def is_constant(self, expr: Expr):
        return isinstance(expr, IntValue)

    def visit_Sym(self, node: Sym):
        assert node in self.expr_to_vals

    def visit_IntValue(self, node: IntValue):
        self.expr_to_vals[node] = [node]
        self.expr_to_types[node] = [IntType()]

    def visit_CallExpr(self, node: CallExpr):
        Visitor.generic_visit(self, node)
        pargs = _flat([self.expr_to_vals[parg] for parg in node.pargs])
        args = _flat([self.expr_to_vals[arg] for arg in node.args])
        vals = _make_list(node.comb.eval(*args, pargs=pargs))
        self.expr_to_vals[node] = vals
        self.expr_to_types[node] = node.comb.get_type(*pargs)[1]

    def visit_IntType(self, node: IntType):
        self.type_to_type[node] = node

    def visit_BoolType(self, node: BoolType):
        self.type_to_type[node] = node

    def visit_TypeCall(self, node: TypeCall):
        Visitor.generic_visit(self, node)
        pargs = _flat([self.expr_to_vals[parg] for parg in node.pargs])
        self.type_to_type[node] = TypeCall(node.type, pargs)

    def visit_ParamDecl(self, node: ParamDecl):
        Visitor.generic_visit(self, node)
        if node.sym in self.expr_to_vals:
            raise ValueError(f"ERROR: {node.sym} used before declared")
        self.expr_to_vals[node.sym] = [self.pargs[self.pi]]
        self.pi += 1
        self.expr_to_types[node.sym] = [self.type_to_type[node.type]]

    def visit_InDecl(self, node: InDecl):
        Visitor.generic_visit(self, node)
        if node.sym in self.expr_to_vals:
            raise ValueError(f"ERROR: {node.sym} used before declared")
        self.expr_to_vals[node.sym] = [self.args[self.ai]]
        self.ai += 1
        new_T = self.type_to_type[node.type]
        self.expr_to_types[node.sym] = [new_T]
        self.input_types.append(new_T)

    def visit_OutDecl(self, node: OutDecl):
        Visitor.generic_visit(self, node)
        new_T = self.type_to_type[node.type]
        self.output_to_type[node.sym] = new_T
        self.output_types.append(new_T)


    def visit_AssignStmt(self, node: AssignStmt):
        Visitor.generic_visit(self, node)
        rhss = _flat([self.expr_to_vals[rhs] for rhs in node.rhss])
        rhss_types = _flat([self.expr_to_types[rhs] for rhs in node.rhss])
        assert len(node.lhss) == len(rhss)
        for lhs, rhs, rhs_type in zip(node.lhss, rhss, rhss_types):
            if lhs in self.expr_to_vals:
                raise ValueError(f"ERROR: {lhs} used before declared")
            self.expr_to_vals[lhs] = [rhs]
            self.expr_to_types[lhs] = [rhs_type]
