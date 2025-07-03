package com.spbu.jmltranslator.fileio;

import com.spbu.jmltranslator.model.JmlMethod;
import com.spbu.jmltranslator.model.TranslationConfig;
import com.spbu.jmltranslator.translator.JmlMethodTranslator;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Stream;

public class DirectoryProcessor {
    private final TranslationConfig config;
    private final JmlMethodTranslator translator;

    public DirectoryProcessor(TranslationConfig config) {
        this.config = config;
        this.translator = new JmlMethodTranslator(config);
    }

    public void processDirectory(String inputDirPath, String outputDirPath) throws IOException {
        Path inputDir = Paths.get(inputDirPath);
        Path outputDir = Paths.get(outputDirPath);
        FileUtils.createDirectories(outputDir);
        
        try (Stream<Path> paths = Files.walk(inputDir)) {
            paths.filter(Files::isRegularFile)
                 .filter(p -> p.toString().endsWith(".java"))
                 .forEach(file -> processFile(file, outputDir));
        }
    }

 private void processFile(Path filePath, Path outputDir) {
        try {
            String content = Files.readString(filePath);
            List<JmlMethod> methods = MethodExtractor.extractMethods(content);
            List<String> classFields = MethodExtractor.extractClassFields(content); // Извлекаем поля
            
            for (JmlMethod method : methods) {
                method.setClassFields(classFields); // Добавляем поля в метод
                translator.translate(method);
                if (method.hasAnnotations()) { // Только если есть //@-аннотации
                    Path outputPath = outputDir.resolve(method.getOutputFilename());
                    Files.writeString(outputPath, method.getFullCode());
                    System.out.println("Generated: " + outputPath);
                }
            }
        } catch (IOException e) {
            System.err.println("Error processing file: " + filePath);
            e.printStackTrace();
        }
}
}