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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new ArrayDeque<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod method = workList.poll();
            if (callGraph.reachableMethods.contains(method)) continue;
            callGraph.addReachableMethod(method);
            callGraph.callSitesIn(method).forEach(callSite -> {
                resolve(callSite).forEach(callee -> {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee));
                    workList.add(callee);
                });
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // NOTE: You are NOT allowed to use ClassHierarchyImpl.resolveMethod(MethodRef) in this assignment
        // so use dispatch to get JMethod
        MethodRef methodRef = callSite.getMethodRef();
        Set<JMethod> res = new HashSet<>();
        JMethod method;  // NOTE: dispatch may return null, store it and check null
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC:
            case SPECIAL:
                method = dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature());
                if (method != null) res.add(method);
                break;
            case VIRTUAL:
            case INTERFACE:
                Queue<JClass> queue = new ArrayDeque<>();
                queue.add(methodRef.getDeclaringClass());
                while (!queue.isEmpty()) {
                    JClass cls = queue.poll();
                    method = dispatch(cls, methodRef.getSubsignature());
                    // NOTE: for virtual call, abstract method should be excluded
                    if (method != null && !method.isAbstract()) res.add(method);
                    queue.addAll(hierarchy.getDirectSubclassesOf(cls));
                    // NOTE: include implementors to dispatch interface correctly
                    queue.addAll(hierarchy.getDirectImplementorsOf(cls));
                }
                break;
        }
        return res;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null) return method;
        JClass superClass = jclass.getSuperClass();
        if (superClass != null) return dispatch(superClass, subsignature);
        return null;
    }
}
