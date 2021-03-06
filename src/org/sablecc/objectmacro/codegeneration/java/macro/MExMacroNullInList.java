/* This file was generated by SableCC's ObjectMacro. */

package org.sablecc.objectmacro.codegeneration.java.macro;

public class MExMacroNullInList extends Macro{

    private Macro list_ListPackageDeclaration[];

    private final Context ListPackageDeclarationContext = new Context();

    public MExMacroNullInList(Macro pListPackageDeclaration[]){

        this.setPListPackageDeclaration(pListPackageDeclaration);
    }

    private void setPListPackageDeclaration(Macro pListPackageDeclaration[]){
        if(pListPackageDeclaration == null){
            throw ObjectMacroException.parameterNull("ListPackageDeclaration");
        }

        Macro macros[] = pListPackageDeclaration;
        this.list_ListPackageDeclaration = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "ListPackageDeclaration");
            }

            macro.apply(new InternalsInitializer("ListPackageDeclaration"){
@Override
void setPackageDeclaration(MPackageDeclaration mPackageDeclaration){

        }
});

            this.list_ListPackageDeclaration[i++] = macro;

        }
    }

    private String buildListPackageDeclaration(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ListPackageDeclarationContext;
        Macro macros[] = this.list_ListPackageDeclaration;
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

    private Macro[] getListPackageDeclaration(){

        return this.list_ListPackageDeclaration;
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setExMacroNullInList(this);
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
        sb0.append(buildListPackageDeclaration());
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("public class MMacroNullInList ");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("  private final String pIndex;");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  private final String pParamName;");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  private final MMacroNullInList mMacroNullInList = this;");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("  public MMacroNullInList(String pIndex, String pParamName) ");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    if(pIndex == null) throw new NullPointerException();");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    this.pIndex = pIndex;");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    if(pParamName == null) throw new NullPointerException();");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    this.pParamName = pParamName;");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  }");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("  String pIndex() ");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    return this.pIndex;");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  }");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("  String pParamName() ");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    return this.pParamName;");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  }");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("  private String rIndex() ");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    return this.mMacroNullInList.pIndex();");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  }");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("  private String rParamName() ");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    return this.mMacroNullInList.pParamName();");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  }");
        sb0.append(LINE_SEPARATOR);
        sb0.append(LINE_SEPARATOR);
        sb0.append("  @Override");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  public String toString() ");
        sb0.append("{");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    StringBuilder sb = new StringBuilder();");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    sb.append(\"A macro is null at index \");");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    sb.append(rIndex());");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    sb.append(\" in the list '\");");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    sb.append(rParamName());");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    sb.append(\"'.\");");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    sb.append(System.getProperty(\"line.separator\"));");
        sb0.append(LINE_SEPARATOR);
        sb0.append("    return sb.toString();");
        sb0.append(LINE_SEPARATOR);
        sb0.append("  }");
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
