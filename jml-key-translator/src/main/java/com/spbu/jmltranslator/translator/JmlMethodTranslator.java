package com.spbu.jmltranslator.translator;

import java.util.ArrayList;
import java.util.List;

import com.spbu.jmltranslator.model.JmlMethod;
import com.spbu.jmltranslator.model.TranslationConfig;

public class JmlMethodTranslator {
    private final TranslationConfig config;
    private final AnnotationHandler annotationHandler;
    
    public JmlMethodTranslator(TranslationConfig config) {
        this.config = config;
        this.annotationHandler = new AnnotationHandler(config);
    }
    
    public void translate(JmlMethod method) {

 System.out.println("Translating method: " + method.getMethodName());
    System.out.println("Original annotations: " + method.getAnnotations());

    // Сброс состояния перед обработкой нового метода
    annotationHandler.reset();
    
    // Создаем копию списка аннотаций для безопасной итерации
    List<String> originalAnnotations = new ArrayList<>(method.getAnnotations());
    
    // Очищаем существующие аннотации
    method.getAnnotations().clear();
    
    // Обрабатываем каждую аннотацию
    for (String annotation : originalAnnotations) {
        String transformed = annotationHandler.transformAnnotation(annotation);
        method.addAnnotation(transformed);
    }
    
    // Добавляем ghost-переменные
    method.getGhostVariables().addAll(annotationHandler.getGhostVariables());



      System.out.println("Transformed annotations: " + method.getAnnotations());
    System.out.println("Ghost variables: " + method.getGhostVariables());
    
}
}


