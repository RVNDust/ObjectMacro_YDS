/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.java.macro;

public class MParamInsertPart extends Macro{

    private String field_ParamName;

    private String field_IndexBuilder;

    private Macro list_ListContextArg[];

    private final Context ListContextArgContext = new Context();

    public MParamInsertPart(String pParamName, String pIndexBuilder, Macro pListContextArg[]){

        this.setPParamName(pParamName);
        this.setPIndexBuilder(pIndexBuilder);
        this.setPListContextArg(pListContextArg);
    }

    private void setPParamName(String pParamName){
        if(pParamName == null){
            throw ObjectMacroException.parameterNull("ParamName");
        }

        this.field_ParamName = pParamName;
    }

    private void setPIndexBuilder(String pIndexBuilder){
        if(pIndexBuilder == null){
            throw ObjectMacroException.parameterNull("IndexBuilder");
        }

        this.field_IndexBuilder = pIndexBuilder;
    }

    private void setPListContextArg(Macro pListContextArg[]){
        if(pListContextArg == null){
            throw ObjectMacroException.parameterNull("ListContextArg");
        }

        Macro macros[] = pListContextArg;
        this.list_ListContextArg = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListContextArg");
            }

            macro.apply(new InternalsInitializer("ListContextArg"){
@Override
void setContextArg(MContextArg mContextArg){

        }
});

            this.list_ListContextArg[i++] = macro;

        }
    }

    private String buildParamName(){

        return this.field_ParamName;
    }

    private String buildIndexBuilder(){

        return this.field_IndexBuilder;
    }

    private String buildListContextArg(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListContextArgContext;
        Macro macros[] = this.list_ListContextArg;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
                        
            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private String getParamName(){

        return this.field_ParamName;
    }

    private String getIndexBuilder(){

        return this.field_IndexBuilder;
    }

    private Macro[] getListContextArg(){

        return this.list_ListContextArg;
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setParamInsertPart(this);
    }

    @Override
    public String build(){

        String local_expansion = this.expansion;

        if(local_expansion != null){
            return local_expansion;
        }

        StringBuilder sb0 = new StringBuilder();

        sb0.append("        sb");
        sb0.append(buildIndexBuilder());
        sb0.append(".append(build");
        sb0.append(buildParamName());
        sb0.append("(");
        sb0.append(buildListContextArg());
        sb0.append("));");

        local_expansion = sb0.toString();
        this.expansion = local_expansion;
        return local_expansion;
    }

    @Override
    String build(Context context) {
        return build();
    }
}
