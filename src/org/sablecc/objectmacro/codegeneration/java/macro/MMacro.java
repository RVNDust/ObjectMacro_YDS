/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.java.macro;

public class MMacro extends Macro{

    private String field_Name;

    private Macro list_ListPackage[];

    private Macro list_ListField[];

    private Macro list_ListContextField[];

    private Macro list_ListConstructor[];

    private Macro list_ListSetter[];

    private Macro list_ListBuilder[];

    private Macro list_ListRef[];

    private Macro list_ListRedefinedApplyInitializer[];

    private Macro list_ListMacroBuilder[];

    private Macro list_ListEmptyBuilderWithContext[];

    private final Context ListPackageContext = new Context();
    private final Context ListFieldContext = new Context();
    private final Context ListContextFieldContext = new Context();
    private final Context ListConstructorContext = new Context();
    private final Context ListSetterContext = new Context();
    private final Context ListBuilderContext = new Context();
    private final Context ListRefContext = new Context();
    private final Context ListRedefinedApplyInitializerContext = new Context();
    private final Context ListMacroBuilderContext = new Context();
    private final Context ListEmptyBuilderWithContextContext = new Context();

    public MMacro(String pName, Macro pListPackage[], Macro pListField[], Macro pListContextField[], Macro pListConstructor[], Macro pListSetter[], Macro pListBuilder[], Macro pListRef[], Macro pListRedefinedApplyInitializer[], Macro pListMacroBuilder[], Macro pListEmptyBuilderWithContext[]){

        this.setPName(pName);
        this.setPListPackage(pListPackage);
        this.setPListField(pListField);
        this.setPListContextField(pListContextField);
        this.setPListConstructor(pListConstructor);
        this.setPListSetter(pListSetter);
        this.setPListBuilder(pListBuilder);
        this.setPListRef(pListRef);
        this.setPListRedefinedApplyInitializer(pListRedefinedApplyInitializer);
        this.setPListMacroBuilder(pListMacroBuilder);
        this.setPListEmptyBuilderWithContext(pListEmptyBuilderWithContext);
    }

    private void setPName(String pName){
        if(pName == null){
            throw ObjectMacroException.parameterNull("Name");
        }

        this.field_Name = pName;
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

    private void setPListField(Macro pListField[]){
        if(pListField == null){
            throw ObjectMacroException.parameterNull("ListField");
        }

        Macro macros[] = pListField;
        this.list_ListField = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListField");
            }

            macro.apply(new InternalsInitializer("ListField"){
@Override
void setParamMacroField(MParamMacroField mParamMacroField){

        }
@Override
void setParamStringField(MParamStringField mParamStringField){

        }
@Override
void setInternalMacroField(MInternalMacroField mInternalMacroField){

        }
@Override
void setInternalStringField(MInternalStringField mInternalStringField){

        }
});

            this.list_ListField[i++] = macro;

        }
    }

    private void setPListContextField(Macro pListContextField[]){
        if(pListContextField == null){
            throw ObjectMacroException.parameterNull("ListContextField");
        }

        Macro macros[] = pListContextField;
        this.list_ListContextField = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListContextField");
            }

            macro.apply(new InternalsInitializer("ListContextField"){
@Override
void setContextField(MContextField mContextField){

        }
});

            this.list_ListContextField[i++] = macro;

        }
    }

    private void setPListConstructor(Macro pListConstructor[]){
        if(pListConstructor == null){
            throw ObjectMacroException.parameterNull("ListConstructor");
        }

        Macro macros[] = pListConstructor;
        this.list_ListConstructor = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListConstructor");
            }

            macro.apply(new InternalsInitializer("ListConstructor"){
@Override
void setConstructor(MConstructor mConstructor){

        }
});

            this.list_ListConstructor[i++] = macro;

        }
    }

    private void setPListSetter(Macro pListSetter[]){
        if(pListSetter == null){
            throw ObjectMacroException.parameterNull("ListSetter");
        }

        Macro macros[] = pListSetter;
        this.list_ListSetter = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListSetter");
            }

            macro.apply(new InternalsInitializer("ListSetter"){
@Override
void setParamStringSetter(MParamStringSetter mParamStringSetter){

        }
@Override
void setParamMacroSetter(MParamMacroSetter mParamMacroSetter){

        }
@Override
void setInternalStringSetter(MInternalStringSetter mInternalStringSetter){

        }
@Override
void setInternalMacroSetter(MInternalMacroSetter mInternalMacroSetter){

        }
});

            this.list_ListSetter[i++] = macro;

        }
    }

    private void setPListBuilder(Macro pListBuilder[]){
        if(pListBuilder == null){
            throw ObjectMacroException.parameterNull("ListBuilder");
        }

        Macro macros[] = pListBuilder;
        this.list_ListBuilder = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListBuilder");
            }

            macro.apply(new InternalsInitializer("ListBuilder"){
@Override
void setParamStringRefBuilder(MParamStringRefBuilder mParamStringRefBuilder){

        }
@Override
void setParamMacroRefBuilder(MParamMacroRefBuilder mParamMacroRefBuilder){

        }
});

            this.list_ListBuilder[i++] = macro;

        }
    }

    private void setPListRef(Macro pListRef[]){
        if(pListRef == null){
            throw ObjectMacroException.parameterNull("ListRef");
        }

        Macro macros[] = pListRef;
        this.list_ListRef = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListRef");
            }

            macro.apply(new InternalsInitializer("ListRef"){
@Override
void setParamStringRef(MParamStringRef mParamStringRef){

        }
@Override
void setParamMacroRef(MParamMacroRef mParamMacroRef){

        }
});

            this.list_ListRef[i++] = macro;

        }
    }

    private void setPListRedefinedApplyInitializer(Macro pListRedefinedApplyInitializer[]){
        if(pListRedefinedApplyInitializer == null){
            throw ObjectMacroException.parameterNull("ListRedefinedApplyInitializer");
        }

        Macro macros[] = pListRedefinedApplyInitializer;
        this.list_ListRedefinedApplyInitializer = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListRedefinedApplyInitializer");
            }

            macro.apply(new InternalsInitializer("ListRedefinedApplyInitializer"){
@Override
void setRedefinedApplyInitializer(MRedefinedApplyInitializer mRedefinedApplyInitializer){

        }
});

            this.list_ListRedefinedApplyInitializer[i++] = macro;

        }
    }

    private void setPListMacroBuilder(Macro pListMacroBuilder[]){
        if(pListMacroBuilder == null){
            throw ObjectMacroException.parameterNull("ListMacroBuilder");
        }

        Macro macros[] = pListMacroBuilder;
        this.list_ListMacroBuilder = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListMacroBuilder");
            }

            macro.apply(new InternalsInitializer("ListMacroBuilder"){
@Override
void setMacroBuilder(MMacroBuilder mMacroBuilder){

        }
});

            this.list_ListMacroBuilder[i++] = macro;

        }
    }

    private void setPListEmptyBuilderWithContext(Macro pListEmptyBuilderWithContext[]){
        if(pListEmptyBuilderWithContext == null){
            throw ObjectMacroException.parameterNull("ListEmptyBuilderWithContext");
        }

        Macro macros[] = pListEmptyBuilderWithContext;
        this.list_ListEmptyBuilderWithContext = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListEmptyBuilderWithContext");
            }

            macro.apply(new InternalsInitializer("ListEmptyBuilderWithContext"){
@Override
void setEmptyBuilderWithContext(MEmptyBuilderWithContext mEmptyBuilderWithContext){

        }
});

            this.list_ListEmptyBuilderWithContext[i++] = macro;

        }
    }

    private String buildName(){

        return this.field_Name;
    }

    private String buildListPackage(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListPackageContext;
        Macro macros[] = this.list_ListPackage;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
                        
            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private String buildListField(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListFieldContext;
        Macro macros[] = this.list_ListField;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
            if(first){
            sb0.append(LINE_SEPARATOR);
    first = false;
}
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

    private String buildListContextField(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListContextFieldContext;
        Macro macros[] = this.list_ListContextField;
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

    private String buildListConstructor(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListConstructorContext;
        Macro macros[] = this.list_ListConstructor;
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

    private String buildListSetter(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListSetterContext;
        Macro macros[] = this.list_ListSetter;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
            if(first){
            sb0.append(LINE_SEPARATOR);
    first = false;
}
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

    private String buildListBuilder(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListBuilderContext;
        Macro macros[] = this.list_ListBuilder;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
            if(first){
            sb0.append(LINE_SEPARATOR);
    first = false;
}
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

    private String buildListRef(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListRefContext;
        Macro macros[] = this.list_ListRef;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
            if(first){
            sb0.append(LINE_SEPARATOR);
    first = false;
}
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

    private String buildListRedefinedApplyInitializer(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListRedefinedApplyInitializerContext;
        Macro macros[] = this.list_ListRedefinedApplyInitializer;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
                        
            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private String buildListMacroBuilder(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListMacroBuilderContext;
        Macro macros[] = this.list_ListMacroBuilder;
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

    private String buildListEmptyBuilderWithContext(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListEmptyBuilderWithContextContext;
        Macro macros[] = this.list_ListEmptyBuilderWithContext;
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

    private String getName(){

        return this.field_Name;
    }

    private Macro[] getListPackage(){

        return this.list_ListPackage;
    }

    private Macro[] getListField(){

        return this.list_ListField;
    }

    private Macro[] getListContextField(){

        return this.list_ListContextField;
    }

    private Macro[] getListConstructor(){

        return this.list_ListConstructor;
    }

    private Macro[] getListSetter(){

        return this.list_ListSetter;
    }

    private Macro[] getListBuilder(){

        return this.list_ListBuilder;
    }

    private Macro[] getListRef(){

        return this.list_ListRef;
    }

    private Macro[] getListRedefinedApplyInitializer(){

        return this.list_ListRedefinedApplyInitializer;
    }

    private Macro[] getListMacroBuilder(){

        return this.list_ListMacroBuilder;
    }

    private Macro[] getListEmptyBuilderWithContext(){

        return this.list_ListEmptyBuilderWithContext;
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setMacro(this);
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
        MImportJavaUtil minsert_2 = new MImportJavaUtil();
                        sb0.append(minsert_2.build(null));
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("public class M");
        sb0.append(buildName());
        sb0.append(" extends Macro");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListField());
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListContextField());
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListConstructor());
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListSetter());
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListBuilder());
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListRef());
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListRedefinedApplyInitializer());
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListMacroBuilder());
        sb0.append(LINE_SEPARATOR);
        sb0.append(buildListEmptyBuilderWithContext());
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
