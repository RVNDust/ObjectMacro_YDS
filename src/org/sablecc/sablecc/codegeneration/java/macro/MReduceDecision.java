/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.sablecc.codegeneration.java.macro;

import java.util.*;

public class MReduceDecision {

    private final MReduce mReduce;

    private final List<Object> eNewTreeClass_NewList = new LinkedList<Object>();

    private final List<Object> eAddLToForest_AddNullToForest_AddNToForest = new LinkedList<Object>();

    private final List<Object> eAddPopToForest = new LinkedList<Object>();

    MReduceDecision(
            MReduce mReduce) {

        if (mReduce == null) {
            throw new NullPointerException();
        }
        this.mReduce = mReduce;
    }

    public MAddPopToForest newAddPopToForest(
            String pElementName,
            String pIndex) {

        MAddPopToForest lAddPopToForest = new MAddPopToForest(pElementName,
                pIndex);
        this.eAddPopToForest.add(lAddPopToForest);
        return lAddPopToForest;
    }

    public MNewTreeClass newNewTreeClass(
            String pElementType,
            String pElementName) {

        MNewTreeClass lNewTreeClass = new MNewTreeClass(pElementType,
                pElementName);
        this.eNewTreeClass_NewList.add(lNewTreeClass);
        return lNewTreeClass;
    }

    public MNewList newNewList(
            String pListName) {

        MNewList lNewList = new MNewList(pListName);
        this.eNewTreeClass_NewList.add(lNewList);
        return lNewList;
    }

    public MAddLToForest newAddLToForest(
            String pElementName) {

        MAddLToForest lAddLToForest = new MAddLToForest(pElementName);
        this.eAddLToForest_AddNullToForest_AddNToForest.add(lAddLToForest);
        return lAddLToForest;
    }

    public MAddNullToForest newAddNullToForest() {

        MAddNullToForest lAddNullToForest = new MAddNullToForest();
        this.eAddLToForest_AddNullToForest_AddNToForest.add(lAddNullToForest);
        return lAddNullToForest;
    }

    public MAddNToForest newAddNToForest(
            String pElementName) {

        MAddNToForest lAddNToForest = new MAddNToForest(pElementName);
        this.eAddLToForest_AddNullToForest_AddNToForest.add(lAddNToForest);
        return lAddNToForest;
    }

    private String rReducedProduction() {

        return this.mReduce.pReducedProduction();
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();
        sb.append("      List<Node> trees = new LinkedList<Node>();");
        sb.append(System.getProperty("line.separator"));
        sb.append("      ");
        for (Object oNewTreeClass_NewList : this.eNewTreeClass_NewList) {
            sb.append(oNewTreeClass_NewList.toString());
        }
        for (Object oAddLToForest_AddNullToForest_AddNToForest : this.eAddLToForest_AddNullToForest_AddNToForest) {
            sb.append(oAddLToForest_AddNullToForest_AddNToForest.toString());
        }
        for (Object oAddPopToForest : this.eAddPopToForest) {
            sb.append(oAddPopToForest.toString());
        }
        sb.append("      stack.push(new AbstractForest(CSTProductionType.");
        sb.append(rReducedProduction());
        sb.append(",trees), stack.getState().getProductionTarget(CSTProductionType.");
        sb.append(rReducedProduction());
        sb.append("));");
        sb.append(System.getProperty("line.separator"));
        sb.append("      return null;");
        sb.append(System.getProperty("line.separator"));
        return sb.toString();
    }

}
