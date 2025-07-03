package com.spbu.jmltranslator.fileio;

import com.spbu.jmltranslator.model.JmlMethod;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.Set;

public class MethodExtractor {
    private static final Pattern CLASS_PATTERN = Pattern.compile(
        "\\bpublic\\s+class\\s+(\\w+)"
    );
    
    private static final Pattern METHOD_PATTERN = Pattern.compile(
        "\\s*(?:(public|protected|private)\\s+)?(static\\s+)?([\\w<>\\[\\]]+)\\s+(\\w+)\\s*\\([^)]*\\)\\s*\\{",
        Pattern.DOTALL
    );

     public static List<String> extractClassFields(String content) {
        List<String> fields = new ArrayList<>();
        // Ищем объявления полей класса: private|protected|public тип имя;
        Pattern fieldPattern = Pattern.compile(
            "\\s*(private|protected|public)\\s+(?:/\\*@.*?@\\*/\\s*)?(\\w+(?:\\[\\])?)\\s+(\\w+)\\s*;"
        );
        
        Matcher fieldMatcher = fieldPattern.matcher(content);
        while (fieldMatcher.find()) {
            fields.add(fieldMatcher.group().trim());
        }
        return fields;
    }
    public static List<JmlMethod> extractMethods(String content) {
        List<JmlMethod> methods = new ArrayList<>();
        Matcher classMatcher = CLASS_PATTERN.matcher(content);
        String className = classMatcher.find() ? classMatcher.group(1) : "UnknownClass";
        List<String> classFields = extractClassFields(content);

        Matcher methodMatcher = METHOD_PATTERN.matcher(content);
        while (methodMatcher.find()) {
            int methodStart = methodMatcher.start();
            String methodName = methodMatcher.group(4);
            String signature = methodMatcher.group(0).replaceFirst("\\{\\s*$", "").trim();
            String paramsPart = signature.substring(signature.indexOf('(') + 1, signature.lastIndexOf(')'));
            List<String> paramNames = new ArrayList<>();
            for (String param : paramsPart.split(",")) {
                String[] parts = param.trim().split(" ");
                if (parts.length > 1) {
                    paramNames.add(parts[parts.length - 1].replaceAll("[\\[\\]]", ""));
                }
            }
            // Извлекаем аннотации перед методом
            String annotations = extractAnnotationsBefore(content, methodStart);
            int start = methodMatcher.end();
            int end = findMethodEnd(content, start);
            if (end == -1) continue;
            String body = content.substring(start - 1, end);
            JmlMethod method = new JmlMethod(className, methodName);
            method.setSignature(signature);
            method.setBody(body);
            method.setClassFields(classFields);
            System.out.println("DEBUG: method " + methodName + " params: " + paramNames);
            System.out.println("DEBUG: method " + methodName + " fields: " + classFields);
            if (annotations != null && !annotations.isEmpty()) {
                for (String line : annotations.split("\n")) {
                    String trimmed = line.trim();
                    if (trimmed.startsWith("//@")) {
                        // Поиск переменных кванторов в аннотации
                        java.util.Set<String> quantVars = new java.util.HashSet<>();
                        java.util.regex.Matcher quantMatcher = java.util.regex.Pattern.compile("\\\\(forall|exists)\\s+\\w+\\s+(\\w+)").matcher(trimmed);
                        while (quantMatcher.find()) {
                            quantVars.add(quantMatcher.group(2));
                        }
                        Set<String> allowedWords = new java.util.HashSet<>(java.util.Arrays.asList(
                            "null", "true", "false", "int", "double", "boolean", "char", "String", "long", "short", "byte", "float",
                            "length", "size", "this", "class", "Object", "void", "return",
                            "requires", "ensures", "assignable", "invariant", "loop_invariant", "decreases"
                        ));
                        java.util.List<String> filteredWords = new java.util.ArrayList<>();
                        boolean add = true;
                        for (String word : trimmed.replaceAll("[^a-zA-Z0-9_\\\\]", " ").split(" ")) {
                            if (word.isEmpty()) continue;
                            if (word.equals("//@")) continue;
                            if (word.startsWith("\\")) continue; // служебные слова JML
                            if (!Character.isLetter(word.charAt(0)) && word.charAt(0) != '_') continue; // не переменная
                            String cleanWord = word.replaceAll("[^a-zA-Z0-9_]", "");
                            if (cleanWord.isEmpty()) continue;
                            if (paramNames.contains(cleanWord)) continue;
                            if (quantVars.contains(cleanWord)) continue;
                            boolean isField = false;
                            for (String field : classFields) {
                                String[] fieldParts = field.split(" ");
                                if (fieldParts.length > 0 && fieldParts[fieldParts.length - 1].replace(";", "").equals(cleanWord)) {
                                    isField = true;
                                    break;
                                }
                            }
                            if (isField) continue;
                            if (allowedWords.contains(cleanWord)) continue;
                            if (cleanWord.matches("\\d+")) continue; // число
                            filteredWords.add(cleanWord);
                            add = false;
                        }
                        if (!filteredWords.isEmpty()) {
                            System.out.println("DEBUG: filtered words in annotation: " + filteredWords);
                        }
                        if (add) method.addAnnotation(trimmed);
                    }
                }
            }
            methods.add(method);
        }
        return methods;
    }

    private static String extractAnnotationsBefore(String content, int methodStart) {
        int pos = methodStart - 1;
        StringBuilder annotations = new StringBuilder();
        boolean foundAny = false;
        while (pos > 0) {
            // Находим начало строки
            int lineEnd = pos + 1;
            while (pos > 0 && content.charAt(pos) != '\n') {
                pos--;
            }
            int lineStart = (pos > 0 && content.charAt(pos) == '\n') ? pos + 1 : pos;
            String line = content.substring(lineStart, lineEnd).trim();
            if (line.isEmpty()) {
                pos--;
                continue;
            }
            if (line.startsWith("//@")) {
                annotations.insert(0, line + "\n");
                foundAny = true;
                pos--;
            } else {
                break;
            }
        }
        // DEBUG вывод
        System.out.println("DEBUG: annotations block for method at pos " + methodStart + ":");
        System.out.println(annotations.toString());
        System.out.println("==== END DEBUG ====");
        // Удаляем лишние пустые строки и пробелы
        String[] annotationLines = annotations.toString().split("\n");
        StringBuilder cleaned = new StringBuilder();
        for (String ann : annotationLines) {
            String trimmed = ann.trim();
            if (!trimmed.isEmpty()) {
                cleaned.append(trimmed).append("\n");
            }
        }
        return cleaned.toString();
    }

    private static int findMethodEnd(String content, int start) {
        int braceCount = 1;
        for (int i = start; i < content.length(); i++) {
            char c = content.charAt(i);
            if (c == '{') braceCount++;
            if (c == '}') braceCount--;
            if (braceCount == 0) return i + 1;
        }
        return -1;
    }
}