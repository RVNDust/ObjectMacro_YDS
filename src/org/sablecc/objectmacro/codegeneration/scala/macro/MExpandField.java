/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.scala.macro;

public class MExpandField {

    private final String pName;

    private final MExpandField mExpandField = this;

    public MExpandField(
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

        return this.mExpandField.pName();
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();
        sb.append("  private val e");
        sb.append(rName());
        sb.append(" = new ListBuffer[Any]()");
        sb.append(System.getProperty("line.separator"));
        return sb.toString();
    }

}
