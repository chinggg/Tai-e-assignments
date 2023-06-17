/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.NewObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.addReachableMethod(method) == false) return;
        method.getIR().forEach(stmt -> {
            stmt.accept(stmtProcessor);
        });
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        @Override
        public Void visit(New stmt) {
            Pointer pointer = pointerFlowGraph.getVarPtr(stmt.getLValue());
            // NOTE: using heapModel.getObj API seems to be more reasonable than creating new instance,
            // though newStmt here should always create new obj instead of getting existing obj
            PointsToSet pts = new PointsToSet(heapModel.getObj(stmt));
            workList.addEntry(pointer, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            // NOTE: use CopyStmt so no need to check AssignStmt LValue and RValue instanceof Var
            VarPtr dst = pointerFlowGraph.getVarPtr(stmt.getLValue());
            VarPtr src = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(src, dst);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) processEachInvoke(stmt, null);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet objs = propagate(ptr, pts);
            if (ptr instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                objs.forEach(obj -> {
                    // NOTE: some solutions on the Web make extra isStatic() checks for storeField and loadField,
                    // but I finally found that the lack of isStatic checks is not the cause of my wrong answers.
                    // isStatic() checks here may be redundant since var.getFields() should return fields related to the var,
                    // which means these fields are unlikely to be static
                    var.getStoreFields().forEach(storeField -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()), pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve()));
                    });
                    var.getStoreArrays().forEach(storeArray -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()), pointerFlowGraph.getArrayIndex(obj));
                    });
                    var.getLoadFields().forEach(loadField -> {
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve()), pointerFlowGraph.getVarPtr(loadField.getLValue()));
                    });
                    var.getLoadArrays().forEach(loadArray -> {
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                    });
                    processCall(var, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet diff = new PointsToSet();
        pointsToSet.forEach(obj -> {
            // addObject(obj) returns true if pts did not contain obj previously
            if (pointer.getPointsToSet().addObject(obj)) {
                diff.addObject(obj);
            }
        });
        if (diff.isEmpty()) return diff;  // NOTE!: stop if no pointsToSet need to be propagated, otherwise dead loop
        pointerFlowGraph.getSuccsOf(pointer).forEach(suc -> {
            workList.addEntry(suc, diff);
        });
        return diff;
    }

    private void processEachInvoke(Invoke invoke, Obj recv) {
        JMethod callee = resolveCallee(recv, invoke);
        if (recv != null) {  // NOTE: only pass receive object to *this* variable for non-static call
            workList.addEntry(pointerFlowGraph.getVarPtr(callee.getIR().getThis()), new PointsToSet(recv));
        }
        // NOTE!: hasEdge API misuse actually causes failure on OJ hidden test cases
        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, callee))) {
            addReachable(callee);
            for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
                addPFGEdge(pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i)), pointerFlowGraph.getVarPtr(callee.getIR().getParam(i)));
            }
            if (invoke.getLValue() != null) {  // NOTE: when lValue == null, invoke ignores return value, VarPtr cannot be created
                callee.getIR().getReturnVars().forEach(retvar -> {
                    addPFGEdge(pointerFlowGraph.getVarPtr(retvar), pointerFlowGraph.getVarPtr(invoke.getLValue()));
                });
            }
        }
    }
    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        var.getInvokes().forEach(invoke -> {
            processEachInvoke(invoke, recv);
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
