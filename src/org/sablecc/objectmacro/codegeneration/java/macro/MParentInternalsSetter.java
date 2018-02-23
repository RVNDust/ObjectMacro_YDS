/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.java.macro;

public class MParentInternalsSetter extends Macro{

    private String field_Name;

    public MParentInternalsSetter(String pName){

        this.setPName(pName);
    }

    private void setPName(String pName){
        if(pName == null){
            throw ObjectMacroException.parameterNull("Name");
        }

        this.field_Name = pName;
    }

    private String buildName(){

        return this.field_Name;
    }

    private String getName(){

        return this.field_Name;
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setParentInternalsSetter(this);
    }

    @Override
    public String build(){

        String local_expansion = this.expansion;

        if(local_expansion != null){
            return local_expansion;
        }

        StringBuilder sb0 = new StringBuilder();

        sb0.append("  void set");
        sb0.append(buildName());
        sb0.append("(M");
        sb0.append(buildName());
        sb0.append(" m");
        sb0.append(buildName());
        sb0.append(")");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append("      throw ObjectMacroException.incorrectType(\"M");
        sb0.append(buildName());
        sb0.append("\", this._paramName);");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  }");

        local_expansion = sb0.toString();
        this.expansion = local_expansion;
        return local_expansion;
    }

    @Override
    String build(Context context) {
        return build();
    }
}