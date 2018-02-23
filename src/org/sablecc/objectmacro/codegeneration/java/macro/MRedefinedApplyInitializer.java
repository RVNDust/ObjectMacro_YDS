/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.java.macro;

public class MRedefinedApplyInitializer extends Macro{

    private String field_Name;

    public MRedefinedApplyInitializer(String pName){

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

        internalsInitializer.setRedefinedApplyInitializer(this);
    }

    @Override
    public String build(){

        String local_expansion = this.expansion;

        if(local_expansion != null){
            return local_expansion;
        }

        StringBuilder sb0 = new StringBuilder();

        sb0.append("    @Override");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    void apply(");
        sb0.append(LINE_SEPARATOR);
        sb0.append("            InternalsInitializer internalsInitializer)");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("        internalsInitializer.set");
        sb0.append(buildName());
        sb0.append("(this);");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    }");

        local_expansion = sb0.toString();
        this.expansion = local_expansion;
        return local_expansion;
    }

    @Override
    String build(Context context) {
        return build();
    }
}