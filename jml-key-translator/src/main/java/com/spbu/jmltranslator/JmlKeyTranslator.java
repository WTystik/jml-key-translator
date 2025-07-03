package com.spbu.jmltranslator;

import com.spbu.jmltranslator.fileio.MethodExtractor;
import com.spbu.jmltranslator.model.JmlMethod;
import com.spbu.jmltranslator.model.TranslationConfig;
import com.spbu.jmltranslator.translator.JmlMethodTranslator;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

public class JmlKeyTranslator {
    public static void main(String[] args) {
        if (args.length != 2) {
            System.out.println("Usage: java JmlKeyTranslator <inputFile> <outputFile>");
            System.out.println("Example: java JmlKeyTranslator input/MyClass.java output/MyClass_key.java");
            return;
        }

        String inputFilePath = args[0];
        String outputFilePath = args[1];

        try {
            File inputFile = new File(inputFilePath);
            if (!inputFile.exists() || !inputFile.isFile()) {
                System.err.println("Input file does not exist: " + inputFilePath);
                return;
            }

            String content = Files.readString(Paths.get(inputFilePath));
            // Извлекаем методы и поля из файла
            List<JmlMethod> methods = MethodExtractor.extractMethods(content);
            List<String> classFields = MethodExtractor.extractClassFields(content);

            TranslationConfig config = new TranslationConfig()
                .setGenerateGhostVars(true)
                .setHandleNullSafety(true)
                .setAddKeyLemmas(true);
            JmlMethodTranslator translator = new JmlMethodTranslator(config);

            StringBuilder translatedContent = new StringBuilder();
            for (JmlMethod method : methods) {
                method.setClassFields(classFields);
                translator.translate(method);
                translatedContent.append(method.getFullCode()).append(System.lineSeparator());
            }

            // Сохраняем результат
            Files.write(Paths.get(outputFilePath), translatedContent.toString().getBytes());
            System.out.println("Translation complete. Output written to: " + outputFilePath);
        } catch (IOException e) {
            System.err.println("Error during translation: " + e.getMessage());
        }
    }
} 