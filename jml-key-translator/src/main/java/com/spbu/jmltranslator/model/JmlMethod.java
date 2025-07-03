package com.spbu.jmltranslator.model;

import java.util.ArrayList;
import java.util.List;

public class JmlMethod {

    
    private String className;
    private String methodName;
    private String signature;
    private String body;
    private List<String> annotations = new ArrayList<>();
    private List<String> ghostVariables = new ArrayList<>();
    private List<String> classFields = new ArrayList<>();

    public JmlMethod(String className, String methodName) {
        this.className = className;
        this.methodName = methodName;
    }

    // Геттеры и сеттеры
    public String getClassName() {
        return className;
    }

     public void setClassFields(List<String> fields) {
        this.classFields = fields;
    }

    public String getMethodName() {
        return methodName;
    }

    public String getSignature() {
        return signature;
    }

    public void setSignature(String signature) {
        this.signature = signature;
    }

    public String getBody() {
        return body;
    }

    public void setBody(String body) {
        this.body = body;
    }

    public List<String> getAnnotations() {
        return annotations;
    }

    public void addAnnotation(String annotation) {
        annotations.add(annotation);
    }
    
    public List<String> getGhostVariables() {
        return ghostVariables;
    }

    public void addGhostVariable(String ghostVar) {
        ghostVariables.add(ghostVar);
    }
    
public String getFullCode() {
    StringBuilder sb = new StringBuilder();
    sb.append("public class ").append(className).append("_").append(methodName).append(" {\n");
    
    // Поля класса
    for (String field : classFields) {
        sb.append("    ").append(field).append("\n");
    }
    sb.append("\n");
    
    // Ghost-переменные
    for (String ghostVar : ghostVariables) {
        sb.append("    ").append(ghostVar).append("\n");
    }
    
    // Аннотации: группируем requires в начало
    boolean seenNonRequires = false;
    for (String annotation : annotations) {
        if (annotation.trim().startsWith("//@ requires ")) {
            if (!seenNonRequires) {
                sb.append("    ").append(annotation).append("\n");
            }
        } else {
            seenNonRequires = true;
            sb.append("    ").append(annotation).append("\n");
        }
    }
    
    // Метод (сохраняем static, если он был)
    String sig = signature;
    if (!sig.contains("static") && signature.contains("static")) {
        sig = signature.replace("static", "static");
    }
    sb.append("    ").append(sig).append(" ").append(body).append("\n");
    
    sb.append("}");
    return sb.toString();
}
    

    public String getOutputFilename() {
        return className + "_" + methodName + ".java";
    }

    // Новый метод: есть ли //@-аннотации
    public boolean hasAnnotations() {
        return annotations != null && !annotations.isEmpty();
    }
}