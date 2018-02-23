/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.sablecc.codegeneration.java.macro;

public class MWalkerCase {

    private final String pTypeName;

    private final MWalkerCase mWalkerCase = this;

    MWalkerCase(
            String pTypeName) {

        if (pTypeName == null) {
            throw new NullPointerException();
        }
        this.pTypeName = pTypeName;
    }

    String pTypeName() {

        return this.pTypeName;
    }

    private String rTypeName() {

        return this.mWalkerCase.pTypeName();
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();
        sb.append("  public void case");
        sb.append(rTypeName());
        sb.append("(N");
        sb.append(rTypeName());
        sb.append(" node) {");
        sb.append(System.getProperty("line.separator"));
        sb.append("    defaultCase(node);");
        sb.append(System.getProperty("line.separator"));
        sb.append("  }");
        sb.append(System.getProperty("line.separator"));
        sb.append(System.getProperty("line.separator"));
        return sb.toString();
    }

}
