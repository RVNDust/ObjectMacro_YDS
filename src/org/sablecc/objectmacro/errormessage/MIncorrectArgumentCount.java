/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.errormessage;

public class MIncorrectArgumentCount {

  private final String pLine;
  private final String pChar;
  private final String pExpectedCount;
  private final String pCurrentCount;
  private final MIncorrectArgumentCount mIncorrectArgumentCount = this;

  public MIncorrectArgumentCount(String pLine, String pChar, String pExpectedCount, String pCurrentCount) {
    if(pLine == null) throw new NullPointerException();
    this.pLine = pLine;
    if(pChar == null) throw new NullPointerException();
    this.pChar = pChar;
    if(pExpectedCount == null) throw new NullPointerException();
    this.pExpectedCount = pExpectedCount;
    if(pCurrentCount == null) throw new NullPointerException();
    this.pCurrentCount = pCurrentCount;
  }

  String pLine() {
    return this.pLine;
  }

  String pChar() {
    return this.pChar;
  }

  String pExpectedCount() {
    return this.pExpectedCount;
  }

  String pCurrentCount() {
    return this.pCurrentCount;
  }

  private String rLine() {
    return this.mIncorrectArgumentCount.pLine();
  }

  private String rChar() {
    return this.mIncorrectArgumentCount.pChar();
  }

  private String rCurrentCount() {
    return this.mIncorrectArgumentCount.pCurrentCount();
  }

  private String rExpectedCount() {
    return this.mIncorrectArgumentCount.pExpectedCount();
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
    sb.append("The macro reference has ");
    sb.append(rCurrentCount());
    sb.append(" arguments, instead of ");
    sb.append(rExpectedCount());
    sb.append(" arguments.");
    sb.append(System.getProperty("line.separator"));
    return sb.toString();
  }

}