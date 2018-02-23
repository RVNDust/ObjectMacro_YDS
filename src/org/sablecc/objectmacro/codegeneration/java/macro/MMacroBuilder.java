/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.java.macro;

public class MMacroBuilder extends Macro{

    private Macro list_ListPublic[];

    private Macro list_ListContextParam[];

    private Macro list_ListContextExpansion[];

    private Macro list_ListPart[];

    private Macro list_ListNewContextExpansion[];

    private final Context ListPublicContext = new Context();
    private final Context ListContextParamContext = new Context();
    private final Context ListContextExpansionContext = new Context();
    private final Context ListPartContext = new Context();
    private final Context ListNewContextExpansionContext = new Context();

    public MMacroBuilder(Macro pListPublic[], Macro pListContextParam[], Macro pListContextExpansion[], Macro pListPart[], Macro pListNewContextExpansion[]){

        this.setPListPublic(pListPublic);
        this.setPListContextParam(pListContextParam);
        this.setPListContextExpansion(pListContextExpansion);
        this.setPListPart(pListPart);
        this.setPListNewContextExpansion(pListNewContextExpansion);
    }

    private void setPListPublic(Macro pListPublic[]){
        if(pListPublic == null){
            throw ObjectMacroException.parameterNull("ListPublic");
        }

        Macro macros[] = pListPublic;
        this.list_ListPublic = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListPublic");
            }

            macro.apply(new InternalsInitializer("ListPublic"){
@Override
void setPublic(MPublic mPublic){

        }
});

            this.list_ListPublic[i++] = macro;

        }
    }

    private void setPListContextParam(Macro pListContextParam[]){
        if(pListContextParam == null){
            throw ObjectMacroException.parameterNull("ListContextParam");
        }

        Macro macros[] = pListContextParam;
        this.list_ListContextParam = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListContextParam");
            }

            macro.apply(new InternalsInitializer("ListContextParam"){
@Override
void setContextParam(MContextParam mContextParam){

        }
});

            this.list_ListContextParam[i++] = macro;

        }
    }

    private void setPListContextExpansion(Macro pListContextExpansion[]){
        if(pListContextExpansion == null){
            throw ObjectMacroException.parameterNull("ListContextExpansion");
        }

        Macro macros[] = pListContextExpansion;
        this.list_ListContextExpansion = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListContextExpansion");
            }

            macro.apply(new InternalsInitializer("ListContextExpansion"){
@Override
void setContextExpansion(MContextExpansion mContextExpansion){

        }
});

            this.list_ListContextExpansion[i++] = macro;

        }
    }

    private void setPListPart(Macro pListPart[]){
        if(pListPart == null){
            throw ObjectMacroException.parameterNull("ListPart");
        }

        Macro macros[] = pListPart;
        this.list_ListPart = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListPart");
            }

            macro.apply(new InternalsInitializer("ListPart"){
@Override
void setStringPart(MStringPart mStringPart){

        }
@Override
void setParamInsertPart(MParamInsertPart mParamInsertPart){

        }
@Override
void setEolPart(MEolPart mEolPart){

        }
@Override
void setInsertMacroPart(MInsertMacroPart mInsertMacroPart){

        }
});

            this.list_ListPart[i++] = macro;

        }
    }

    private void setPListNewContextExpansion(Macro pListNewContextExpansion[]){
        if(pListNewContextExpansion == null){
            throw ObjectMacroException.parameterNull("ListNewContextExpansion");
        }

        Macro macros[] = pListNewContextExpansion;
        this.list_ListNewContextExpansion = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListNewContextExpansion");
            }

            macro.apply(new InternalsInitializer("ListNewContextExpansion"){
@Override
void setNewContextExpansion(MNewContextExpansion mNewContextExpansion){

        }
});

            this.list_ListNewContextExpansion[i++] = macro;

        }
    }

    private String buildListPublic(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListPublicContext;
        Macro macros[] = this.list_ListPublic;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
                        
            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private String buildListContextParam(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListContextParamContext;
        Macro macros[] = this.list_ListContextParam;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
                        
            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private String buildListContextExpansion(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListContextExpansionContext;
        Macro macros[] = this.list_ListContextExpansion;
        if(macros.length == 0){
            sb0.append("this.expansion");
}
        boolean first = true;
        int i = 0;

        for(Macro macro : macros){
                        
            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private String buildListPart(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListPartContext;
        Macro macros[] = this.list_ListPart;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
                        if(first) {
  first = false;
}
else {
           sb0.append(LINE_SEPARATOR);
}

            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private String buildListNewContextExpansion(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListNewContextExpansionContext;
        Macro macros[] = this.list_ListNewContextExpansion;
        if(macros.length == 0){
            sb0.append("this.expansion = local_expansion");
}
        boolean first = true;
        int i = 0;

        for(Macro macro : macros){
                        
            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private Macro[] getListPublic(){

        return this.list_ListPublic;
    }

    private Macro[] getListContextParam(){

        return this.list_ListContextParam;
    }

    private Macro[] getListContextExpansion(){

        return this.list_ListContextExpansion;
    }

    private Macro[] getListPart(){

        return this.list_ListPart;
    }

    private Macro[] getListNewContextExpansion(){

        return this.list_ListNewContextExpansion;
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setMacroBuilder(this);
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
        sb0.append("    ");
        sb0.append(buildListPublic());
        sb0.append(" String build(");
        sb0.append(buildListContextParam());
        sb0.append(")");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("        String local_expansion = ");
        sb0.append(buildListContextExpansion());
        sb0.append(";");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("        if(local_expansion != null)");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append("            return local_expansion;");
        sb0.append(LINE_SEPARATOR);
        sb0.append("        }");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("        StringBuilder sb0 = new StringBuilder();");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListPart());
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("        local_expansion = sb0.toString();");
        sb0.append(LINE_SEPARATOR);
        sb0.append("        ");
        sb0.append(buildListNewContextExpansion());
        sb0.append(";");
        sb0.append(LINE_SEPARATOR);
        sb0.append("        return local_expansion;");
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
