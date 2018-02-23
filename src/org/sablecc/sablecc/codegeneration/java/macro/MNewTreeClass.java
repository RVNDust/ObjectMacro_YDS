/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.sablecc.codegeneration.java.macro;

import java.util.*;

public class MNewTreeClass {

    private final String pElementType;

    private final String pElementName;

    private final MNewTreeClass mNewTreeClass = this;

    private final List<Object> eNewTreeClass_NewList = new LinkedList<Object>();

    private final List<Object> eNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter = new LinkedList<Object>();

    MNewTreeClass(
            String pElementType,
            String pElementName) {

        if (pElementType == null) {
            throw new NullPointerException();
        }
        this.pElementType = pElementType;
        if (pElementName == null) {
            throw new NullPointerException();
        }
        this.pElementName = pElementName;
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

    public MNormalParameter newNormalParameter(
            String pElementType,
            String pElementName,
            String pIndex) {

        MNormalParameter lNormalParameter = new MNormalParameter(pElementType,
                pElementName, pIndex);
        this.eNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter
                .add(lNormalParameter);
        return lNormalParameter;
    }

    public MNullParameter newNullParameter() {

        MNullParameter lNullParameter = new MNullParameter();
        this.eNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter
                .add(lNullParameter);
        return lNullParameter;
    }

    public MSeparatedParameter newSeparatedParameter(
            String pLeftElementType,
            String pRightElementType,
            String pElementName,
            String pIndex) {

        MSeparatedParameter lSeparatedParameter = new MSeparatedParameter(
                pLeftElementType, pRightElementType, pElementName, pIndex);
        this.eNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter
                .add(lSeparatedParameter);
        return lSeparatedParameter;
    }

    public MAlternatedParameter newAlternatedParameter(
            String pLeftElementType,
            String pRightElementType,
            String pElementName,
            String pIndex) {

        MAlternatedParameter lAlternatedParameter = new MAlternatedParameter(
                pLeftElementType, pRightElementType, pElementName, pIndex);
        this.eNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter
                .add(lAlternatedParameter);
        return lAlternatedParameter;
    }

    public MNewParameter newNewParameter(
            String pElementName) {

        MNewParameter lNewParameter = new MNewParameter(pElementName);
        this.eNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter
                .add(lNewParameter);
        return lNewParameter;
    }

    public MEndParameter newEndParameter() {

        MEndParameter lEndParameter = new MEndParameter();
        this.eNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter
                .add(lEndParameter);
        return lEndParameter;
    }

    String pElementType() {

        return this.pElementType;
    }

    String pElementName() {

        return this.pElementName;
    }

    private String rElementType() {

        return this.mNewTreeClass.pElementType();
    }

    private String rElementName() {

        return this.mNewTreeClass.pElementName();
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();
        for (Object oNewTreeClass_NewList : this.eNewTreeClass_NewList) {
            sb.append(oNewTreeClass_NewList.toString());
        }
        sb.append("        N");
        sb.append(rElementType());
        sb.append(" n");
        sb.append(rElementName());
        sb.append(" = new N");
        sb.append(rElementType());
        sb.append(" (-1, -1");
        if (this.eNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter
                .size() > 0) {
            sb.append(", ");
        }
        {
            boolean first = true;
            for (Object oNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter : this.eNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter) {
                if (first) {
                    first = false;
                }
                else {
                    sb.append(", ");
                }
                sb.append(oNormalParameter_NullParameter_SeparatedParameter_AlternatedParameter_NewParameter_EndParameter
                        .toString());
            }
        }
        sb.append(");");
        sb.append(System.getProperty("line.separator"));
        return sb.toString();
    }

}
