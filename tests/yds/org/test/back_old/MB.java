/* This file was generated by SableCC's ObjectMacro. */

package org.test.back_old;

import java.util.*;

public class MB extends Macro{

    private String field_X;

    private Map<Context, Macro[]> list_Y = new LinkedHashMap<>();

    private final Context YContext = new Context();

    public MB(String pX){

        this.setPX(pX);
    }

    private void setPX(String pX){
        if(pX == null){
            throw ObjectMacroException.parameterNull("X");
        }

        this.field_X = pX;
    }

    void setY(
            Context context,
            Macro macros[]) {

        if(macros == null){
            throw new RuntimeException("macros cannot be null here");
        }

        Macro[] tempMacros = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){

            if(macro == null){
                throw ObjectMacroException.macroNull(i, "Y");
            }

            macro.apply(new InternalsInitializer("Y"){
@Override
void setC(MC mC){

            StringBuilder sb1 = new StringBuilder();

        sb1.append("first argument of c in b");
            mC.setY(YContext, sb1.toString());
        mC.setZ(YContext, getX());
}
});

            tempMacros[i++] = macro;
        }

        this.list_Y.put(context, tempMacros);
    }

    private String buildX(){

        return this.field_X;
    }

    private String buildY(Context context){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = YContext;
        Macro macros[] = this.list_Y.get(context);
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

    private String getX(){

        return this.field_X;
    }

    private Macro[] getY(Context context){

        return this.list_Y.get(context);
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setB(this);
    }

    @Override
     String build(Context context){

        String local_expansion = this.expansions.get(context);

        if(local_expansion != null){
            return local_expansion;
        }

        StringBuilder sb0 = new StringBuilder();

        sb0.append(buildY(context));

        local_expansion = sb0.toString();
        this.expansions.put(context, local_expansion);
        return local_expansion;
    }
}
