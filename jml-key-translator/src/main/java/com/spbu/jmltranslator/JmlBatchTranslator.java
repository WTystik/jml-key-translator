package com.spbu.jmltranslator;

import com.spbu.jmltranslator.fileio.DirectoryProcessor;
import com.spbu.jmltranslator.model.TranslationConfig;

public class JmlBatchTranslator {
    
    public static void main(String[] args) {
        if (args.length < 2) {
            System.out.println("Usage: java JmlBatchTranslator <inputDir> <outputDir>");
            System.out.println("Example: java JmlBatchTranslator src/main/java target/key-code");
            System.exit(1);
        }
        
        TranslationConfig config = new TranslationConfig()
            .setGenerateGhostVars(true)
            .setHandleNullSafety(true)
            .setAddKeyLemmas(true);
        
        DirectoryProcessor processor = new DirectoryProcessor(config);
        try {
            processor.processDirectory(args[0], args[1]);
            System.out.println("Translation completed successfully!");
        } catch (Exception e) {
            System.err.println("Translation failed: " + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        }
    }
}