/* This file was generated by SableCC's ObjectMacro. */

package org.test.back_old;

import java.util.*;

public class MC extends Macro{

    private Map<Context, String> field_Y = new LinkedHashMap<>();

    private Map<Context, String> field_Z = new LinkedHashMap<>();

    public MC(){
    }

    void setY(
            Context context,
            String value) {

        if(value == null){
            throw new RuntimeException("value cannot be null here");
        }

        this.field_Y.put(context, value);
    }

    void setZ(
            Context context,
            String value) {

        if(value == null){
            throw new RuntimeException("value cannot be null here");
        }

        this.field_Z.put(context, value);
    }

    private String buildY(Context context){

        return this.field_Y.get(context);
    }

    private String buildZ(Context context){

        return this.field_Z.get(context);
    }

    private String getY(Context context){

        return this.field_Y.get(context);
    }

    private String getZ(Context context){

        return this.field_Z.get(context);
    }

    @Override
    void apply(
            InternalsInitializer internalsInitializer){

        internalsInitializer.setC(this);
    }

    @Override
     String build(Context context){

        String local_expansion = this.expansions.get(context);

        if(local_expansion != null){
            return local_expansion;
        }

        StringBuilder sb0 = new StringBuilder();

        sb0.append(buildY(context));
        sb0.append(" ");
        sb0.append(buildZ(context));

        local_expansion = sb0.toString();
        this.expansions.put(context, local_expansion);
        return local_expansion;
    }
}
