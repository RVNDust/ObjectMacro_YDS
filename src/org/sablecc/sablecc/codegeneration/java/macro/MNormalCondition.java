/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.sablecc.codegeneration.java.macro;

public class MNormalCondition {

    private final String pAhead;

    private final String pTokenType;

    private final MNormalCondition mNormalCondition = this;

    MNormalCondition(
            String pAhead,
            String pTokenType) {

        if (pAhead == null) {
            throw new NullPointerException();
        }
        this.pAhead = pAhead;
        if (pTokenType == null) {
            throw new NullPointerException();
        }
        this.pTokenType = pTokenType;
    }

    String pAhead() {

        return this.pAhead;
    }

    String pTokenType() {

        return this.pTokenType;
    }

    private String rAhead() {

        return this.mNormalCondition.pAhead();
    }

    private String rTokenType() {

        return this.mNormalCondition.pTokenType();
    }

    @Override
    public String toString() {

        StringBuilder sb = new StringBuilder();
        sb.append("parser.look(");
        sb.append(rAhead());
        sb.append(").getInternalType() == Token.InternalType.T_");
        sb.append(rTokenType());
        return sb.toString();
    }

}
