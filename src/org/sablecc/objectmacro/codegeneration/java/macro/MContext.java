/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.java.macro;

public class MContext extends Macro{

    private Macro list_ListPackage[];

    private final Context ListPackageContext = new Context();

    public MContext(Macro pListPackage[]){

        this.setPListPackage(pListPackage);
    }

    private void setPListPackage(Macro pListPackage[]){
        if(pListPackage == null){
            throw ObjectMacroException.parameterNull("ListPackage");
        }

        Macro macros[] = pListPackage;
        this.list_ListPackage = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListPackage");
            }

            macro.apply(new InternalsInitializer("ListPackage"){
@Override
void setPackageDeclaration(MPackageDeclaration mPackageDeclaration){

        }
});

            this.list_ListPackage[i++] = macro;

        }
    }

    private String buildListPackage(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListPackageContext;
        Macro macros[] = this.list_ListPackage;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
            if(first){
            sb0.append(LINE_SEPARATOR);
    first = false;
}
            
            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private Macro[] getListPackage(){

        return this.list_ListPackage;
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setContext(this);
    }

    @Override
    public String build(){

        String local_expansion = this.expansion;

        if(local_expansion != null){
            return local_expansion;
        }

        StringBuilder sb0 = new StringBuilder();

        MHeader minsert_1 = new MHeader();
                        sb0.append(minsert_1.build(null));
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListPackage());
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("public class Context ");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("}");

        local_expansion = sb0.toString();
        this.expansion = local_expansion;
        return local_expansion;
    }

    @Override
    String build(Context context) {
        return build();
    }
}
