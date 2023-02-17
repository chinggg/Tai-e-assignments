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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        cfg.getIR().getParams().forEach(var -> {
            if (canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((k, v) -> {
            target.update(k, meetValue(target.get(k), v));
        });  // NOTE: Why meetValue here?
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef() || v2.isUndef()) return v1.isUndef() ? v2 : v1;
        // NOTE: When comparing objects for equality, always use .equals() instead of ==
        return v1.equals(v2) ? v1 : Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO: there might be bugs
        boolean hasChange = out.copyFrom(in);
        if (stmt instanceof DefinitionStmt def) {
            if(def.getLValue() instanceof Var var && canHoldInt(var)) {
                Value genVal = evaluate(def.getRValue(), in);
                // NOTE: shouldn't meetValue here, otherwise re-assign will cause NAC, failing testAssign
                // NOTE: change can happen from both IN[s] and GEN[s]
                hasChange |= out.update(var, genVal);
            }
        }
        return hasChange;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // https://tai-e.pascal-lab.net/pa2/exp-subclasses.png
        if (exp instanceof IntLiteral) return Value.makeConstant(((IntLiteral) exp).getValue());
        if (exp instanceof Var) return in.get((Var) exp);
        if (exp instanceof BinaryExp) {
            Value v1 = in.get(((BinaryExp) exp).getOperand1());
            Value v2 = in.get(((BinaryExp) exp).getOperand2());
            // NOTE: similar to meetValue but different when there is UNDEF
            if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
            if (v1.isUndef() || v2.isUndef()) return Value.getUndef();
            if (v1.isConstant() && v2.isConstant()) {
                int c1 = v1.getConstant();
                int c2 = v2.getConstant();
                BinaryExp.Op op = ((BinaryExp) exp).getOperator();
                if (exp instanceof ArithmeticExp) {
                    return switch ((ArithmeticExp.Op) op) {
                        case ADD -> Value.makeConstant(c1 + c2);
                        case SUB -> Value.makeConstant(c1 - c2);
                        case MUL -> Value.makeConstant(c1 * c2);
                        case DIV -> c2 != 0 ? Value.makeConstant(c1 / c2) : Value.getUndef();
                        case REM -> c2 != 0 ? Value.makeConstant(c1 % c2) : Value.getUndef();
                    };  // DIV 0 and REM 0 return UNDEF
                } else if (exp instanceof BitwiseExp) {
                    return Value.makeConstant(switch ((BitwiseExp.Op) op) {
                        case OR -> c1 | c2;
                        case AND -> c1 & c2;
                        case XOR -> c1 ^ c2;
                    });
                } else if (exp instanceof ConditionExp) {
                    return Value.makeConstant(switch ((ConditionExp.Op) op) {
                        case EQ -> c1 == c2;
                        case GE -> c1 >= c2;
                        case GT -> c1 > c2;
                        case LE -> c1 <= c2;
                        case LT -> c1 < c2;
                        case NE -> c1 != c2;
                    } ? 1 : 0);  // true/false -> 1/0
                } else if (exp instanceof ShiftExp) {
                    return Value.makeConstant(switch ((ShiftExp.Op) op) {
                        case SHL -> c1 << c2;
                        case SHR -> c1 >> c2;
                        case USHR -> c1 >>> c2;
                    });
                }
            }
        }
        return Value.getNAC();  // NOTE: evaluate as NAC by default, otherwise testInterprocedural will fail
    }
}
