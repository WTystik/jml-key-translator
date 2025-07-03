package com.spbu.jmltranslator.translator;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Генератор ghost-переменных для обработки выражений с \old()
 */
public class GhostVariableGenerator {
    private int ghostVarCounter = 0;
    
    /**
     * Обрабатывает выражения с \old() в аннотации
     * 
     * @param annotation Исходная аннотация
     * @return Результат обработки и сгенерированные ghost-переменные
     */
    public GhostVariableResult handleOldExpression(String annotation) {
        StringBuilder result = new StringBuilder();
        StringBuilder ghostVars = new StringBuilder();
        System.out.println("Processing annotation for old: " + annotation);
        
        Pattern pattern = Pattern.compile("\\\\old\\s*\\(\\s*([^)]+)\\s*\\)");
        Matcher matcher = pattern.matcher(annotation);

        
        while (matcher.find()) {
            String expr = matcher.group(1);
            String varName = generateVarName(expr);
            String type = guessType(expr);
            
            ghostVars.append("//@ ghost ")
                     .append(type)
                     .append(" ")
                     .append(varName)
                     .append(" = ")
                     .append(expr)
                     .append(";\n");
            
            matcher.appendReplacement(result, varName);
        }
        matcher.appendTail(result);
        
        return new GhostVariableResult(result.toString(), ghostVars.toString());
    }
    

    private String generateVarName(String expr) {
        String baseName = sanitizeVarName(expr);
        return "__old_" + baseName + "_" + (ghostVarCounter++);
    }
    
    /**
     * Санитизация имени переменной
     */
    private String sanitizeVarName(String expr) {
        return expr.replaceAll("[^a-zA-Z0-9]", "_")
                   .replaceAll("_{2,}", "_")
                   .replaceAll("^_|_$", "");
    }
    
    /**
     * Определение типа переменной по выражению
     */
private String guessType(String expr) {
    // Улучшенные правила определения типа
    if (expr.matches("\\d+\\.\\d+")) return "double";
    if (expr.matches("\\d+")) return "int";
    if (expr.matches("'.'")) return "char";
    if (expr.contains("\"")) return "String";
    if (expr.equals("true") || expr.equals("false")) return "boolean";
    
    // Контекстно-зависимые правила для полей класса
    if (expr.equals("balance")) return "int";
    if (expr.equals("amount")) return "int";
    if (expr.equals("result")) return "int";
    if (expr.equals("size")) return "int";
    if (expr.equals("length")) return "int";
    if (expr.equals("name")) return "String";
    
    // Анализ выражения
    if (expr.contains(".")) return "double";
    if (expr.contains("length")) return "int";
    if (expr.contains("size")) return "int";
    
    return "int"; // Безопасный тип по умолчанию
}
    
    /**
     * Результат обработки выражения с \old()
     */
    public static class GhostVariableResult {
        private final String transformedAnnotation;
        private final String ghostVariables;
        
        public GhostVariableResult(String transformedAnnotation, String ghostVariables) {
            this.transformedAnnotation = transformedAnnotation;
            this.ghostVariables = ghostVariables;
        }

        public String getTransformedAnnotation() {
            return transformedAnnotation;
        }

        public String getGhostVariables() {
            return ghostVariables;
        }
    }
}