/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.scala.macro;

public class MParamParam {

    private final String pName;

    private final MParamParam mParamParam = this;

    public MParamParam(
            String pName) {

        if (pName == null) {
            throw new NullPointerException();
        }
        this.pName = pName;
    }

    String pName() {

        return this.pName;
    }

    private String rName() {

        return this.mParamParam.pName();
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();
        sb.append("p");
        sb.append(rName());
        sb.append(": String");
        return sb.toString();
    }

}
