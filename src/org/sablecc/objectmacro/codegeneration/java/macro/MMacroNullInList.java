/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.java.macro;

public class MMacroNullInList {

  private final String pIndex;
  private final String pParamName;
  private final MMacroNullInList mMacroNullInList = this;

  public MMacroNullInList(String pIndex, String pParamName) {
    if(pIndex == null) throw new NullPointerException();
    this.pIndex = pIndex;
    if(pParamName == null) throw new NullPointerException();
    this.pParamName = pParamName;
  }

  String pIndex() {
    return this.pIndex;
  }

  String pParamName() {
    return this.pParamName;
  }

  private String rIndex() {
    return this.mMacroNullInList.pIndex();
  }

  private String rParamName() {
    return this.mMacroNullInList.pParamName();
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("A macro is null at index ");
    sb.append(rIndex());
    sb.append(" in the list '");
    sb.append(rParamName());
    sb.append("'.");
    sb.append(System.getProperty("line.separator"));
    return sb.toString();
  }

}
