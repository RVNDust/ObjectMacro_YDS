/* This file was generated by SableCC's ObjectMacro. */

package org.test.back_old;

public class MA extends Macro{

    private String field_X;

    private Macro list_Y[];

    private Macro list_Z[];

    private final Context YContext = new Context();
    private final Context ZContext = new Context();

    public MA(String pX, Macro pY[], Macro pZ[]){

        this.setPX(pX);
        this.setPZ(pZ);
        this.setPY(pY);
    }

    private void setPX(String pX){
        if(pX == null){
            throw ObjectMacroException.parameterNull("X");
        }

        this.field_X = pX;
    }

    private void setPY(Macro pY[]){
        if(pY == null){
            throw ObjectMacroException.parameterNull("Y");
        }

        Macro macros[] = pY;
        this.list_Y = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "Y");
            }

            macro.apply(new InternalsInitializer("Y"){
@Override
void setB(MB mB){

                mB.setY(YContext, getZ());
}
});

            this.list_Y[i++] = macro;

        }
    }

    private void setPZ(Macro pZ[]){
        if(pZ == null){
            throw ObjectMacroException.parameterNull("Z");
        }

        Macro macros[] = pZ;
        this.list_Z = new Macro[macros.length];
        int i = 0;

        for(Macro macro : macros){
            if(macro == null){
                throw ObjectMacroException.macroNull(i, "Z");
            }

            macro.apply(new InternalsInitializer("Z"){
@Override
void setC(MC mC){

            StringBuilder sb1 = new StringBuilder();

        sb1.append("first argument of c in a");
            mC.setY(ZContext, sb1.toString());
        mC.setZ(ZContext, getX());
}
});

            this.list_Z[i++] = macro;

        }
    }

    private String buildX(){

        return this.field_X;
    }

    private String buildY(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = YContext;
        Macro macros[] = this.list_Y;
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

    private String buildZ(){

        StringBuilder sb0 = new StringBuilder();
        Context local_context = ZContext;
        Macro macros[] = this.list_Z;
                boolean first = true;
        int i = 0;

        for(Macro macro : macros){
                        
            sb0.append(macro.build(local_context));
            i++;

                    }

        return sb0.toString();
    }

    private String getX(){

        return this.field_X;
    }

    private Macro[] getY(){

        return this.list_Y;
    }

    private Macro[] getZ(){

        return this.list_Z;
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setA(this);
    }

    @Override
    public String build(){

        String local_expansion = this.expansion;

        if(local_expansion != null){
            return local_expansion;
        }

        StringBuilder sb0 = new StringBuilder();

        sb0.append(buildY());

        local_expansion = sb0.toString();
        this.expansion = local_expansion;
        return local_expansion;
    }

    @Override
    String build(Context context) {
        return build();
    }
}
