/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.errormessage;

public class MDuplicateMacroRef {

  private final String pParam;
  private final String pMacro;
  private final String pLine;
  private final String pChar;
  private final MDuplicateMacroRef mDuplicateMacroRef = this;

  public MDuplicateMacroRef(String pParam, String pMacro, String pLine, String pChar) {
    if(pParam == null) throw new NullPointerException();
    this.pParam = pParam;
    if(pMacro == null) throw new NullPointerException();
    this.pMacro = pMacro;
    if(pLine == null) throw new NullPointerException();
    this.pLine = pLine;
    if(pChar == null) throw new NullPointerException();
    this.pChar = pChar;
  }

  String pParam() {
    return this.pParam;
  }

  String pMacro() {
    return this.pMacro;
  }

  String pLine() {
    return this.pLine;
  }

  String pChar() {
    return this.pChar;
  }

  private String rLine() {
    return this.mDuplicateMacroRef.pLine();
  }

  private String rChar() {
    return this.mDuplicateMacroRef.pChar();
  }

  private String rParam() {
    return this.mDuplicateMacroRef.pParam();
  }

  private String rMacro() {
    return this.mDuplicateMacroRef.pMacro();
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append(new MSemanticErrorHead().toString());
    sb.append(System.getProperty("line.separator"));
    sb.append("Line: ");
    sb.append(rLine());
    sb.append(System.getProperty("line.separator"));
    sb.append("Char: ");
    sb.append(rChar());
    sb.append(System.getProperty("line.separator"));
    sb.append("Parameter '");
    sb.append(rParam());
    sb.append("' has already referenced Macro '");
    sb.append(rMacro());
    sb.append("'.");
    sb.append(System.getProperty("line.separator"));
    return sb.toString();
  }

}
