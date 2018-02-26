/* This file is part of SableCC ( http://sablecc.org ).
 *
 * See the NOTICE file distributed with this work for copyright information.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.sablecc.objectmacro.codegeneration.java;

import java.io.*;
import java.util.*;

import org.sablecc.exception.*;
import org.sablecc.objectmacro.codegeneration.*;
import org.sablecc.objectmacro.codegeneration.c.macro.MParam;
import org.sablecc.objectmacro.codegeneration.java.macro.*;
import org.sablecc.objectmacro.codegeneration.java.structure.Macro;
import org.sablecc.objectmacro.codegeneration.java.structure.ParamMacroRefStruct;
import org.sablecc.objectmacro.codegeneration.java.structure.ParamStringStruct;
import org.sablecc.objectmacro.exception.*;
import org.sablecc.objectmacro.intermediate.macro.MInternal;
import org.sablecc.objectmacro.intermediate.syntax3.analysis.*;
import org.sablecc.objectmacro.intermediate.syntax3.node.*;
import org.sablecc.objectmacro.syntax3.node.PStringPart;
import org.sablecc.objectmacro.util.Utils;

public class CodeGenerationWalker
        extends DepthFirstAdapter {

    private static final String CONTEXT_STRING = "Context";

    private static final String INSERT_VAR_NAME = "insert_";

    private static final String SEPARATOR_DIRECTIVE = "separator";

    private static final String AFTER_LAST_DIRECTIVE = "afterlast";

    private static final String NONE_DIRECTIVE = "none";

    private static final String BEFORE_FIRST_DIRECTIVE = "beforefirst";

    private final IntermediateRepresentation ir;

    private final File packageDirectory;

    private MMacro currentMacroToBuild;

    private Macro currentMacro;

    private MConstructor currentConstructor;

    private MSuperMacro superMacro;

    private MInternalsInitializer mInternalsInitializer;

    private MContext mContext;

    private MMacroBuilder currentMacroBuilder;

    private MApplyInternalsInitializer currentApplyInitializer;

    private MRedefinedInternalsSetter currentRedefinedInternalsSetter;

    private Integer indexBuilder = 0;

    private Integer indexInsert = 0;

    private String currentMacroName;

    private Map<String, Macro> macros = new LinkedHashMap<>();

    private Map<String, ParamStringStruct> currentMacroParamString = new LinkedHashMap<>();
    private Map<String, ParamMacroRefStruct> currentMacroParamMacroRef = new LinkedHashMap<>();

    private String currentContext;

    private MInsertMacroPart currentInsertMacroPart;

    private List<String> contextNames = new ArrayList<>();

    private List<String> createdBuilders = new ArrayList<>();

    private List<Integer> createdInserts = new ArrayList<>();

    private MParamMacroRefBuilder currentParamMacroRefBuilder;

    private MPackageDeclaration packageDeclaration;

    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentParamList = new ArrayList<>();

    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentInternalList = new ArrayList<>();

    private MParentInternalsSetter currentInternalParentSetter;

    private MRedefinedApplyInitializer currentRedefinedApplyInitializer;

    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentParamSet = new ArrayList<>();
    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentInternalSet = new ArrayList<>();

    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentContextParam = new ArrayList<>();
    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentContextExpansion = new ArrayList<>();
    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentNewContextExpansion = new ArrayList<>();
    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentPublic = new ArrayList<>();
    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentEmptyBuilderWithContext = new ArrayList<>();
    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentListParts = new ArrayList<>();

    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentSeparators = new ArrayList<>();
    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentBeforeFirst = new ArrayList<>();
    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentAfterLast = new ArrayList<>();
    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentNone = new ArrayList<>();

    private boolean isInAMacroRef = false;


    private MStringParam currentStringParam;
    private MInitStringBuilder currentInitStringBuilder;

    private ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> currentListRedefinedInternalSetter = new ArrayList<>();

    public CodeGenerationWalker(
            IntermediateRepresentation ir,
            File packageDirectory) {

        this.ir = ir;
        this.packageDirectory = packageDirectory;
    }

    private String string(
            TString tString) {

        String string = tString.getText();
        int length = string.length();
        return string.substring(1, length - 1);
    }

    private String escapedString(
            TString tString) {

        StringBuilder sb = new StringBuilder();
        String s = string(tString);
        boolean escaped = false;
        for (char c : s.toCharArray()) {
            if (escaped) {
                escaped = false;

                if (c == '\\') {
                    sb.append('\\');
                    sb.append('\\');
                }
                else if (c == '\'') {
                    sb.append('\'');
                }
                else {
                    throw new InternalException("unhandled case");
                }
            }
            else if (c == '\\') {
                escaped = true;
            }
            else if (c == '\"') {
                sb.append('\\');
                sb.append('\"');
            }
            else {
                sb.append(c);
            }
        }

        if (escaped) {
            throw new InternalException("incomplete escape");
        }

        return sb.toString();
    }

    private String buildNameCamelCase(
            LinkedList<TString> name_parts){

        StringBuilder macroName = new StringBuilder();
        for(TString partName : name_parts){
            macroName.append(Utils.toCamelCase(string(partName)));
        }

        return macroName.toString();
    }

    private String buildName(
            LinkedList<TString> name_parts){

        StringBuilder macroName = new StringBuilder();
        for(TString partName : name_parts){
            macroName.append(string(partName));
        }

        return macroName.toString();
    }

    private void writeFile(
            String fileName,
            String content){

        File destination = new File(this.packageDirectory, fileName);

        try {
            FileWriter fw = new FileWriter(destination);
            fw.write(content);
            fw.close();
        }
        catch (IOException e) {
            throw CompilerException.outputError(destination.toString(), e);
        }
    }

    private String getLetterFromInteger(
            Integer i){

        return i > 0 && i < 27 ? String.valueOf((char) (i + 64)) : null;
    }

    @Override
    public void inAIntermediateRepresentation(
            AIntermediateRepresentation node) {

        if(!this.ir.getDestinationPackage().equals("")){
            String destinationPackage = this.ir.getDestinationPackage();
            packageDeclaration = new MPackageDeclaration(destinationPackage);
        }

        this.superMacro = new MSuperMacro(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.packageDeclaration});
        //this.mInternalsInitializer = new MInternalsInitializer(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.packageDeclaration});
        this.mContext = new MContext(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.packageDeclaration});
    }

    @Override
    public void outAIntermediateRepresentation(
            AIntermediateRepresentation node) {

        this.mInternalsInitializer = new MInternalsInitializer(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.packageDeclaration}
        , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.currentInternalParentSetter});

        writeFile("Macro.java", this.superMacro.build());
        writeFile("Context.java", this.mContext.build());
        writeFile("InternalsInitializer.java", this.mInternalsInitializer.build());

        MExParameterNull mParameterNull = new MExParameterNull(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.packageDeclaration});
        MExIncorrectType mIncorrectType = new MExIncorrectType(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.packageDeclaration});
        MExObjectMacroErrorHead mObjectMacroErrorHead = new MExObjectMacroErrorHead(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.packageDeclaration});
        MExMacroNullInList mMacroNullInList = new MExMacroNullInList(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.packageDeclaration});
        MExObjectMacroException mObjectMacroException = new MExObjectMacroException(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.packageDeclaration});

        if(!this.ir.getDestinationPackage().equals("")){
            String destinationPackage = this.ir.getDestinationPackage();
        }

        writeFile("MIncorrectType.java", mIncorrectType.build());
        writeFile("MParameterNull.java", mParameterNull.build());
        writeFile("MObjectMacroErrorHead.java", mObjectMacroErrorHead.build());
        writeFile("MMacroNullInList.java", mMacroNullInList.build());
        writeFile("ObjectMacroException.java", mObjectMacroException.build());
    }

    @Override
    public void inAMacro(
            AMacro node) {

        String macroName = buildNameCamelCase(node.getNames());

        this.currentMacroName = macroName;

        if(!macros.containsKey(macroName))
            macros.put(macroName, new Macro(macroName, new LinkedList<>(), new LinkedList<>()));
        this.currentMacro = macros.get(macroName);

        this.contextNames = new ArrayList<>();

        if (!this.ir.getDestinationPackage().equals("")) {
            this.currentMacro.getPackages().add(this.packageDeclaration);
        }

        //Définit dans le Out une fois passé dans tous les param et les internals
        /*this.currentConstructor = new MConstructor();*/

        this.currentInternalParentSetter = new MParentInternalsSetter(this.currentMacroName);
        this.currentRedefinedApplyInitializer = new MRedefinedApplyInitializer(this.currentMacroName);
        this.currentMacro.getRedefinedApplyInitializer().add(this.currentRedefinedApplyInitializer);

        this.currentParamSet = new ArrayList<>();
        for(TString string : node.getInitOrder()){
            String param_name = Utils.toCamelCase(string(string));
            this.currentParamSet.add(new MSetParam(param_name, new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] { new MParamArg(param_name)}));
        }

        if(node.getInternals().size() > 0){
            //method build is package protected so a context parameter to build the current macro
            this.currentContextParam.add(new MContextParam());
            this.currentContextExpansion.add(new MContextExpansion());
            this.currentNewContextExpansion.add(new MNewContextExpansion());
        }
        else{
            this.currentPublic.add(new MPublic());
            this.currentEmptyBuilderWithContext.add(new MEmptyBuilderWithContext());
        }

        //Définition dans le OutAMacro pour avoir la liste des parts de la macro (4ème param du constructeur)
        /*this.currentMacroBuilder = new MMacroBuilder(this.currentPublic.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[currentPublic.size()])
            ,this.currentContextParam.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[currentContextParam.size()])
            ,this.currentContextExpansion.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[currentContextExpansion.size()])
            ,
            ,this.currentNewContextExpansion.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[currentNewContextExpansion.size()]));*/
    }

    @Override
    public void caseAInternal(
            AInternal node) {

        String paramName = buildNameCamelCase(node.getNames());

        if(node.getType() instanceof AStringType){
            MInternalStringField mInternalStringField = new MInternalStringField(paramName);
            MInternalStringSetter mInternalStringSetter = new MInternalStringSetter(paramName);

            this.currentMacro.getField().add(mInternalStringField);
            this.currentMacro.getSetter().add(mInternalStringSetter);

            MParamStringRefBuilder mParamStringRefBuilder = new MParamStringRefBuilder(paramName
            , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MContextParam()}
            , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MGetInternalTail()});

            this.currentMacro.getBuilder().add(mParamStringRefBuilder);

            MParamStringRef mParamStringRef = new MParamStringRef(paramName
            , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MContextParam()}
            , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MGetInternalTail()});

            this.currentMacro.getRef().add(mParamStringRef);
        }
        else if(node.getType() instanceof AMacroRefsType){
            MInternalMacroField mInternalMacroField = new MInternalMacroField(paramName);
            MContextField mContextField = new MContextField(paramName);

            this.currentMacro.getField().add(mInternalMacroField);
            this.currentMacro.getContextField().add(mContextField);

            MParamMacroRefBuilder mParamMacroRefBuilder = new MParamMacroRefBuilder(paramName
                    , String.valueOf(this.indexBuilder)
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MContextParam()}
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MContextName(paramName.concat(CONTEXT_STRING))}
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MGetInternalTail()}
                    , this.currentNone.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentNone.size()])
                    , this.currentBeforeFirst.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentBeforeFirst.size()])
                    , this.currentSeparators.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentSeparators.size()])
                    , this.currentAfterLast.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentAfterLast.size()]));

            this.currentMacro.getBuilder().add(mParamMacroRefBuilder);

            MParamMacroRef mParamMacroRef = new MParamMacroRef(paramName
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MContextParam()}
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MGetInternalTail()});

            this.currentMacro.getRef().add(mParamMacroRef);

            //Initialize directives before type because of conflicts with stringBuilder
            for (PDirective directive : node.getDirectives()) {
                directive.apply(this);
            }

            this.indexBuilder = 0;

            this.currentContext = paramName.concat(CONTEXT_STRING);
            this.contextNames.add(currentContext);


            this.currentApplyInitializer = new MApplyInternalsInitializer(paramName
            , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.currentRedefinedInternalsSetter});

            MInternalMacroSetter mInternalMacroSetter = new MInternalMacroSetter(paramName
            , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.currentApplyInitializer});

            this.currentMacro.getSetter().add(mInternalMacroSetter);

        }
        else{
            throw new InternalException("case unhandled");
        }
        node.getType().apply(this);
        outAInternal(node);
    }

    @Override
    public void outAInternal(
            AInternal node) {

        this.currentContext = null;
        this.currentApplyInitializer = null;
        this.indexBuilder = 0;
        this.indexInsert = 0;
        this.currentParamMacroRefBuilder = null;
        this.createdBuilders = new ArrayList<>();
        this.createdInserts = new ArrayList<>();
    }

    @Override
    public void caseAParam(
            AParam node) {

        String paramName = buildNameCamelCase(node.getNames());
        ParamStringStruct paramStringStruct = new ParamStringStruct();
        ParamMacroRefStruct paramMacroRefStruct = new ParamMacroRefStruct();
        MMacroParam mMacroParam = null;
        MMacroArg mMacroArg = null;

        if(node.getType() instanceof AStringType){
            paramStringStruct.mParamStringField = new MParamStringField(paramName);
            paramStringStruct.mParamStringRef = new MParamStringRef(paramName
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[0]
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[0]);
            paramStringStruct.mParamStringRefBuilder = new MParamStringRefBuilder(paramName
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[0]
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[0]);
            this.currentStringParam = new MStringParam(paramName);
            paramStringStruct.mParamStringSetter = new MParamStringSetter(paramName
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.currentStringParam}
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MParamArg(paramName)});

            this.currentParamList.add(this.currentStringParam);
            this.currentMacro.getField().add(paramStringStruct.mParamStringField);
            this.currentMacro.getRef().add(paramStringStruct.mParamStringRef);
            this.currentMacro.getBuilder().add(paramStringStruct.mParamStringRefBuilder);
            this.currentMacro.getSetter().add(paramStringStruct.mParamStringSetter);
            /*this.currentMacroParamString.put(paramName, param);*/
        }
        else if(node.getType() instanceof AMacroRefsType){
            paramMacroRefStruct.mParamMacroField = new MParamMacroField(paramName);
            paramMacroRefStruct.mContextField = new MContextField(paramName);

            this.currentMacro.getContextField().add(paramMacroRefStruct.mContextField);

            for (PDirective directive : node.getDirectives()) {
                directive.apply(this);
            }

            this.currentContext = paramName.concat(CONTEXT_STRING);
            this.indexBuilder = 0;

            mMacroParam = new MMacroParam(paramName);
            mMacroArg = new MMacroArg(paramName);

            this.currentParamList.add(mMacroParam);
            this.contextNames.add(currentContext);
        }
        else{
            throw new InternalException("case unhandled");
        }

        node.getType().apply(this);

        if(node.getType() instanceof AMacroRefsType)
        {
            MContextParam mContextParam = new MContextParam();
            currentContextParam.add(mContextParam);
            paramMacroRefStruct.mParamMacroRefBuilder = new MParamMacroRefBuilder(paramName
                    , String.valueOf(this.indexBuilder)
                    , currentContextParam.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[currentContextParam.size()])
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MContextName(paramName)}
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[0]
                    , this.currentNone.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentNone.size()])
                    , this.currentBeforeFirst.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentBeforeFirst.size()])
                    , this.currentSeparators.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentSeparators.size()])
                    , this.currentAfterLast.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentAfterLast.size()]));

            this.currentApplyInitializer = new MApplyInternalsInitializer(paramName
            , this.currentListRedefinedInternalSetter.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentListRedefinedInternalSetter.size()]));

            paramMacroRefStruct.mParamMacroRef = new MParamMacroRef(paramName
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mContextParam}
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MGetInternalTail()});

            paramMacroRefStruct.mParamMacroSetter = new MParamMacroSetter(paramName
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mMacroParam}
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MParamArg(paramName)}
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.currentApplyInitializer});

            this.currentMacro.getSetter().add(paramMacroRefStruct.mParamMacroSetter);
            this.currentMacro.getField().add(paramMacroRefStruct.mParamMacroField);
            this.currentMacro.getRef().add(paramMacroRefStruct.mParamMacroRef);
            this.currentMacro.getBuilder().add(paramMacroRefStruct.mParamMacroRefBuilder);
        }

        outAParam(node);
    }

    @Override
    public void outAParam(AParam node) {

        this.currentContext = null;
        this.currentApplyInitializer = null;
        this.indexBuilder = 0;
        this.indexInsert = 0;
        this.createdBuilders = new ArrayList<>();
        this.createdInserts = new ArrayList<>();
        this.currentParamMacroRefBuilder = null;
    }

    @Override
    public void inADirective(
            ADirective node) {

        /*String directive_name = buildName(node.getNames());
        switch (directive_name) {

            case SEPARATOR_DIRECTIVE:
            this.currentSeparators.add(new MSeparator())
            break;

            case AFTER_LAST_DIRECTIVE:
                this.currentAfterLast = this.currentParamMacroRefBuilder.newAfterLast();
                break;

            case BEFORE_FIRST_DIRECTIVE:
                this.currentBeforeFirst = this.currentParamMacroRefBuilder
                        .newBeforeFirst();
                break;

            case NONE_DIRECTIVE:
                this.currentNone = this.currentParamMacroRefBuilder.newNone();
                break;

            default:
                throw new InternalException("case unhandled");
        }*/
    }

    @Override
    public void outADirective(
            ADirective node) {

        /*this.currentSeparators = null;
        this.currentAfterLast = null;
        this.currentBeforeFirst = null;
        this.currentNone = null;*/
    }

    @Override
    public void inAMacroRef(
            AMacroRef node) {
        this.isInAMacroRef = true;
        this.currentMacroName = buildNameCamelCase(node.getNames());
        if(this.currentContext != null){
            this.currentRedefinedInternalsSetter = new MRedefinedInternalsSetter(currentMacroName
                    , this.currentListParts.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentListParts.size()])
                    , this.currentInternalSet.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentInternalSet.size()]));
        }

    }

    @Override
    public void outAMacroRef(
            AMacroRef node) {

        this.currentMacroName = buildNameCamelCase(node.getNames());

        this.currentMacroName = null;
        this.isInAMacroRef = false;
    }

    @Override
    public void caseAStringValue(
            AStringValue node) {

        this.indexBuilder++;
        String index_builder = String.valueOf(this.indexBuilder);
        boolean anyContext = this.currentContext != null;

        MInitStringBuilder mInitStringBuilder;
        MSetInternal mSetInternal;
        MStringBuilderBuild mStringBuilderBuild;

        if(anyContext){
            mSetInternal = new MSetInternal(this.currentMacroName
                    ,buildNameCamelCase(node.getParamName())
                    ,this.currentContext
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[0]);

            for(PTextPart part : node.getParts()){
                part.apply(this);
            }

        }
        else{
            index_builder = getLetterFromInteger(this.indexBuilder);

            //Avoid declaring stringbuilder of the same name
            while(this.createdBuilders.contains(index_builder)){
                this.indexBuilder++;
                index_builder = getLetterFromInteger(this.indexBuilder);
            }

            mInitStringBuilder = new MInitStringBuilder(index_builder);
            mStringBuilderBuild = new MStringBuilderBuild(index_builder);

            if(this.isInAMacroRef)
            {
                /*this.currentListParts.add(mInitStringBuilder);*/
            }

            this.createdBuilders.add(index_builder);

            mSetInternal = new MSetInternal(INSERT_VAR_NAME.concat(String.valueOf(this.indexInsert))
                    ,buildNameCamelCase(node.getParamName())
                    ,"null"
                    ,new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mStringBuilderBuild});

            //To avoid modification on indexes
            Integer tempIndexBuilder = this.indexBuilder;
            Integer tempIndexInsert = this.indexInsert;

            for(PTextPart part : node.getParts()){
                part.apply(this);
            }

            this.indexBuilder = tempIndexBuilder;
            this.indexInsert = tempIndexInsert;
        }
        this.currentInternalSet.add(mSetInternal);
    }

    @Override
    public void caseAStringTextPart(
            AStringTextPart node) {

        String index_builder = String.valueOf(this.indexBuilder);

        MStringPart mStringPart = new MStringPart(escapedString(node.getString())
        ,String.valueOf(this.indexBuilder));

        this.currentListParts.add(mStringPart);

        if(this.currentContext != null
                && this.isInAMacroRef){

            this.currentListParts.add(new MStringPart(escapedString(node.getString())
                    , String.valueOf(this.indexBuilder)));
        }
        else {

            String string = escapedString(node.getString());

            if(this.currentInsertMacroPart != null){
                index_builder = getLetterFromInteger(this.indexBuilder);
                this.currentListParts.add(new MStringPart(string, index_builder));
            }
            else if(this.currentNone != null){
                this.currentNone.add(new MNone(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MStringPart(string, index_builder)}));
            }
            else if(this.currentBeforeFirst != null){
                this.currentBeforeFirst.add(new MBeforeFirst(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MStringPart(string, index_builder)}));
            }
            else if(this.currentAfterLast != null){
                this.currentAfterLast.add(new MAfterLast(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MStringPart(string, index_builder)}));
            }
            else if(this.currentSeparators != null){
                this.currentSeparators.add(new MSeparator(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MStringPart(string, index_builder)}));
            }
        }
    }

    @Override
    public void caseAVarTextPart(
            AVarTextPart node) {

        String index_builder = String.valueOf(this.indexBuilder);
        String param_name = buildNameCamelCase(node.getNames());

        if(this.currentContext != null)
        {
            this.currentContextParam.add(new MContextParam());
        }

        MParamInsertPart mParamInsertPart = new MParamInsertPart(param_name
        ,index_builder
        ,new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MContextArg()});

        this.currentListParts.add(mParamInsertPart);

        if(this.currentContext != null
                && this.isInAMacroRef){

            this.currentListParts.add(mParamInsertPart);
        }
        else {

            /*String string = escapedString(node.getString());*/

            if(this.currentInsertMacroPart != null){
                /*index_builder = getLetterFromInteger(this.indexBuilder);*/
                this.currentListParts.add(mParamInsertPart);
            }
            else if(this.currentNone != null){
                this.currentNone.add(new MNone(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mParamInsertPart}));
            }
            else if(this.currentBeforeFirst != null){
                this.currentBeforeFirst.add(new MBeforeFirst(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mParamInsertPart}));
            }
            else if(this.currentAfterLast != null){
                this.currentAfterLast.add(new MAfterLast(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mParamInsertPart}));
            }
            else if(this.currentSeparators != null){
                this.currentSeparators.add(new MSeparator(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mParamInsertPart}));
            }
        }
    }

    @Override
    public void caseAEolTextPart(
            AEolTextPart node) {

        String index_builder = String.valueOf(indexBuilder);

        MEolPart mEolPart = new MEolPart(index_builder);

        this.currentListParts.add(mEolPart);

        if(this.currentContext != null
                && this.isInAMacroRef){

            this.currentListParts.add(mEolPart);
        }
        else {

            /*String string = escapedString(node.getString());*/

            if(this.currentInsertMacroPart != null){
                /*index_builder = getLetterFromInteger(this.indexBuilder);*/
                this.currentListParts.add(mEolPart);
            }
            else if(this.currentNone != null){
                this.currentNone.add(new MNone(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mEolPart}));
            }
            else if(this.currentBeforeFirst != null){
                this.currentBeforeFirst.add(new MBeforeFirst(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mEolPart}));
            }
            else if(this.currentAfterLast != null){
                this.currentAfterLast.add(new MAfterLast(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mEolPart}));
            }
            else if(this.currentSeparators != null){
                this.currentSeparators.add(new MSeparator(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {mEolPart}));
            }
        }
    }

    @Override
    public void caseAInsertTextPart(
            AInsertTextPart node) {

        AMacroRef macroRef = (AMacroRef) node.getMacroRef();
        String macro_name = buildNameCamelCase(macroRef.getNames());
        String index_builder = String.valueOf(this.indexBuilder);

        //Avoid declaring insert of the same name
        while(this.createdInserts.contains(this.indexInsert)){
            this.indexInsert++;
        }

        String index_insert = String.valueOf(this.indexInsert);

        this.createdInserts.add(this.indexInsert);

        String tempContext = this.currentContext;
        String tempMacroName = this.currentMacroName;
        Integer tempIndex = this.indexBuilder;
        Integer tempIndexInsert = this.indexInsert;
        ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> tempListParts = this.currentListParts;
        ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> tempInternalList = this.currentInternalSet;
        this.currentContext = null;

        node.getMacroRef().apply(this);

        this.currentInsertMacroPart = new MInsertMacroPart(macro_name
                ,index_builder
                ,index_insert
                ,this.currentListParts.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentListParts.size()])
                ,this.currentInternalSet.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentInternalSet.size()]));

        if(this.currentContext != null
                && this.isInAMacroRef){

            this.currentListParts.add(this.currentInsertMacroPart);
        }
        else {

            /*String string = escapedString(node.getString());*/

            if(this.currentInsertMacroPart != null){
                /*index_builder = getLetterFromInteger(this.indexBuilder);*/
                this.currentListParts.add(this.currentInsertMacroPart);
            }
            else if(this.currentNone != null){
                this.currentNone.add(new MNone(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.currentInsertMacroPart}));
            }
            else if(this.currentBeforeFirst != null){
                this.currentBeforeFirst.add(new MBeforeFirst(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.currentInsertMacroPart}));
            }
            else if(this.currentAfterLast != null){
                this.currentAfterLast.add(new MAfterLast(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.currentInsertMacroPart}));
            }
            else if(this.currentSeparators != null){
                this.currentSeparators.add(new MSeparator(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {this.currentInsertMacroPart}));
            }
        }

        this.indexBuilder = tempIndex;
        this.indexInsert = tempIndexInsert;
        this.currentContext = tempContext;
        this.currentMacroName = tempMacroName;
        this.currentListParts = tempListParts;
        this.currentInternalSet = tempInternalList;

    }

    @Override
    public void outAVarValue(
            AVarValue node) {

        String var_name = buildNameCamelCase(node.getNames());
        MSetInternal setInternal;
        MParamRef paramRef;

        if(this.currentContext != null){
            paramRef = new MParamRef(var_name
            , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MContextName(this.currentContext)});

            setInternal = new MSetInternal(this.currentMacroName
            , buildNameCamelCase(node.getParamName())
            , this.currentContext
            , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {paramRef});
        }
        else{
            paramRef = new MParamRef(var_name
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {new MContextArg()});

            setInternal = new MSetInternal(INSERT_VAR_NAME.concat(String.valueOf(this.indexInsert))
                    , buildNameCamelCase(node.getParamName())
                    , "null"
                    , new org.sablecc.objectmacro.codegeneration.java.macro.Macro[] {paramRef});
        }
        this.currentInternalSet.add(setInternal);

    }

    @Override
    public void outAMacro(
            AMacro node) {

        String macroName = buildNameCamelCase(node.getNames());

        //Définition du constructeur d'après les paramètres recueillis dans l'arbre
        this.currentConstructor = new MConstructor(macroName
        , this.currentParamSet.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentParamSet.size()])
        , this.currentParamList.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentParamList.size()])
        , this.currentInternalList.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentInternalList.size()]));
        this.currentMacro.getConstructor().add(this.currentConstructor);

        //Définition du MacroBuilder
        this.currentMacroBuilder = new MMacroBuilder(this.currentPublic.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentPublic.size()])
        , this.currentContextParam.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentContextParam.size()])
        , this.currentContextExpansion.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentContextExpansion.size()])
        , this.currentListParts.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentListParts.size()])
        , this.currentNewContextExpansion.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentNewContextExpansion.size()]));
        this.currentMacro.getMacroBuilder().add(this.currentMacroBuilder);

        this.currentMacro.setEmptyBuilderWithContext(this.currentEmptyBuilderWithContext);

        writeFile("DebugListParts", this.currentListParts.toString());
        writeFile("M" + macroName + ".java", this.currentMacro.getMacro().build());

        this.contextNames = null;
        this.currentMacroToBuild = null;
        this.currentConstructor = null;
    }

    @Override
    public void caseAStringMacroPart(AStringMacroPart node) {

        this.currentListParts.add(new MStringPart(escapedString(node.getString())
                , String.valueOf(indexBuilder)));
    }

    @Override
    public void outAEolMacroPart(
            AEolMacroPart node) {

        this.currentListParts.add(new MEolPart(String.valueOf(indexBuilder)));
    }

    @Override
    public void caseAInsertMacroPart(
            AInsertMacroPart node) {

        AMacroRef macroRef = (AMacroRef) node.getMacroRef();
        String macro_name = buildNameCamelCase(macroRef.getNames());
        this.indexInsert++;

        this.createdInserts.add(this.indexInsert);
        Integer tempIndexBuilder = this.indexBuilder;
        Integer tempIndexInsert = this.indexInsert;
        ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> tempListParts = this.currentListParts;
        ArrayList<org.sablecc.objectmacro.codegeneration.java.macro.Macro> tempInternalList = this.currentInternalList;

        node.getMacroRef().apply(this);
        //this.currentListParts.add(this.currentInitStringBuilder);

        this.currentInsertMacroPart = new MInsertMacroPart(macro_name
        , String.valueOf(indexBuilder)
        , String.valueOf(indexInsert)
        , this.currentListParts.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentListParts.size()])
        , this.currentInternalList.toArray(new org.sablecc.objectmacro.codegeneration.java.macro.Macro[this.currentInternalList.size()]));

        this.currentListParts.add(this.currentInsertMacroPart);

        this.indexInsert = tempIndexInsert;
        this.indexBuilder = tempIndexBuilder;
        this.currentInsertMacroPart = null;
        this.currentListParts = tempListParts;
        this.currentInternalList = tempInternalList;
    }

    @Override
    public void outAVarMacroPart(
            AVarMacroPart node) {

        String param_name = buildNameCamelCase(node.getNames());

        org.sablecc.objectmacro.codegeneration.java.macro.Macro[] listContextArgs;

        if(this.currentMacro.getInternals().contains(param_name)){
            listContextArgs = new org.sablecc.objectmacro.codegeneration.java.macro.Macro[1];
            listContextArgs[0] = new MContextArg();
        }
        else
        {
            listContextArgs = new org.sablecc.objectmacro.codegeneration.java.macro.Macro[0];
        }

        MParamInsertPart mParamInsertPart = new MParamInsertPart(param_name
                , String.valueOf(indexBuilder)
                , listContextArgs);

        this.currentListParts.add(mParamInsertPart);
    }
}
