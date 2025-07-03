package com.spbu.jmltranslator.fileio;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

public class FileUtils {
    public static void createDirectories(Path path) throws IOException {
        if (!Files.exists(path)) {
            Files.createDirectories(path);
        }
    }
    
    public static String readFileToString(Path path) throws IOException {
        return Files.readString(path);
    }
    
    public static void writeStringToFile(Path path, String content) throws IOException {
        Files.writeString(path, content);
    }
}