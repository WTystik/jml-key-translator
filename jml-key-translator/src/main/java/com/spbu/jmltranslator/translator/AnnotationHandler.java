package com.spbu.jmltranslator.translator;

import com.spbu.jmltranslator.model.TranslationConfig;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class AnnotationHandler {
    private final TranslationConfig config;
    private final List<String> ghostVariables = new ArrayList<>();
    private int ghostVarCounter = 0;
    
    public AnnotationHandler(TranslationConfig config) {
        this.config = config;
    }
    
public String transformAnnotation(String annotation) {
    if (annotation.contains("\\old")) {
        return handleOldExpression(annotation);
    }
    
    // Добавляем явные касты типов для Key
    annotation = annotation
        .replace("\\old(balance)", "(int)\\old(balance)")
        .replace("\\old(value)", "(int)\\old(value)");
    
    return annotation;
}
    
private String handleOldExpression(String annotation) {
    Pattern pattern = Pattern.compile("\\\\old\\(\\s*([^)]+)\\s*\\)");
    Matcher matcher = pattern.matcher(annotation);
    StringBuffer sb = new StringBuffer();
    
    while (matcher.find()) {
        String expr = matcher.group(1);
        String varName = generateVarName(expr);
        String type = guessType(expr);
        
        ghostVariables.add("//@ ghost " + type + " " + varName + " = (" + type + ")" + expr + ";");
        
        // Для Key добавляем явное преобразование типа
        matcher.appendReplacement(sb, "((" + type + ")" + varName + ")");
    }
    matcher.appendTail(sb);
    
    return sb.toString();
}
    
    private String sanitizeVarName(String expr) {
        return expr.replaceAll("[^a-zA-Z0-9]", "_")
                   .replaceAll("_{2,}", "_")
                   .replaceAll("^_|_$", "");
    }
    
    private String guessType(String expr) {
        if (expr.contains(".")) return "double";
        if (expr.contains("\"")) return "String";
        if (expr.matches(".*[a-zA-Z].*")) return "int";
        return "int";
    }
    
    public List<String> getGhostVariables() {
        return ghostVariables;
    }

     private String generateVarName(String expr) {
        String baseName = sanitizeVarName(expr);
        return "__old_" + baseName + "_" + (ghostVarCounter++);
    }
    
    public void reset() {
    ghostVariables.clear();
    ghostVarCounter = 0;
}
}