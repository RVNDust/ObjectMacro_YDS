/* This file was generated by SableCC's ObjectMacro. */
package org.test.back;

import java.util.*;

public class MSemicolonSeparator extends Macro{


    private Map<Context, Macro[]> list_X = new LinkedHashMap<>();

    private final Context XContext = new Context();

    public MSemicolonSeparator(Macro pX[]){

        this.setPX(pX);

    }


    void setX(
            Context context,
            Macro macros[]) {

        if(macros == null){
            throw new RuntimeException("macros cannot be null here");
        }

        Macro[] tempMacros = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){

            if(macro == null){
                throw ObjectMacroException.macroNull(i, "X");
            }

            macro.apply(new InternalsInitializer("X"){
@Override
void setEmptyMacro(MEmptyMacro mEmptyMacro){

            sb0.append(", ");
    
}
});

            tempMacros[i++] = macro;
        }

        this.list_X.put(context, tempMacros);
    }


    private String buildX(Context context){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = XContext;
        Macro macros[] = this.list_X .get(context);
        if(macros.length == 0){
            sb0.append(", ");
}
        boolean first = true;
        int i = 0;

        for(Macro macro : macros){
            
            

            sb0.append(macro.build(local_context));
            i++;

            
        }

        return sb0.toString();
    }


    private Macro[] getX(Context context){

        return this.list_X.get(context);
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setSemicolonSeparator(this);
    }

    @Override
    publicpublic String build(Context contextContext context){

        String local_expansion = this.expansions.get(context);

        if(local_expansion != null){
            return local_expansion;
        }

        StringBuilder sb0 = new StringBuilder();

        sb0.append(", ");
        sb0.append("La liste x : ");
        sb0.append(buildX());
        sb0.append(LINE_SEPARATOR);
        sb0.append("Corps de semicolon : ");
        MSemicolonSeparator minsert_1 = new MSemicolonSeparator();
                sb0.append(", ");        sb0.append("La liste x : ");        sb0.append(buildX());        sb0.append(LINE_SEPARATOR);        sb0.append("Corps de semicolon : ");
        
        sb0.append(minsert_1.build(null));
        sb0.append(".");
        sb0.append("empty");
        sb0.append("; ");
        sb0.append("Le corps de C : ");
        sb0.append(buildX());

        local_expansion = sb0.toString();
        this.expansions.put(context, local_expansion);
        return local_expansion;
}

    @Override
    String build(Context context) {
        return build();
    }    @Override
    String build(Context context) {
        return build();
    }
}