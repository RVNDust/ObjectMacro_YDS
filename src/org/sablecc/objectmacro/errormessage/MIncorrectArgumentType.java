/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.errormessage;

public class MIncorrectArgumentType {

  private final String pExpected;
  private final String pFound;
  private final String pLine;
  private final String pChar;
  private final MIncorrectArgumentType mIncorrectArgumentType = this;

  public MIncorrectArgumentType(String pExpected, String pFound, String pLine, String pChar) {
    if(pExpected == null) throw new NullPointerException();
    this.pExpected = pExpected;
    if(pFound == null) throw new NullPointerException();
    this.pFound = pFound;
    if(pLine == null) throw new NullPointerException();
    this.pLine = pLine;
    if(pChar == null) throw new NullPointerException();
    this.pChar = pChar;
  }

  String pExpected() {
    return this.pExpected;
  }

  String pFound() {
    return this.pFound;
  }

  String pLine() {
    return this.pLine;
  }

  String pChar() {
    return this.pChar;
  }

  private String rLine() {
    return this.mIncorrectArgumentType.pLine();
  }

  private String rChar() {
    return this.mIncorrectArgumentType.pChar();
  }

  private String rFound() {
    return this.mIncorrectArgumentType.pFound();
  }

  private String rExpected() {
    return this.mIncorrectArgumentType.pExpected();
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
    sb.append("The parameter type found is \"");
    sb.append(rFound());
    sb.append("\", instead of \"");
    sb.append(rExpected());
    sb.append("\";");
    sb.append(System.getProperty("line.separator"));
    return sb.toString();
  }

}