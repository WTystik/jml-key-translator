package com.spbu.jmltranslator.model;

/**
 * Класс конфигурации параметров трансляции JML аннотаций
 */
public class TranslationConfig {
    private boolean generateGhostVars = true;
    private boolean handleNullSafety = true;
    private boolean addKeyLemmas = true;
    private boolean preserveComments = true;
    private boolean translateQuantifiers = true;
    private boolean processOldExpressions = true;
    private boolean replaceResultKeyword = true;

    // Fluent interface геттеры и сеттеры
    public boolean isGenerateGhostVars() {
        return generateGhostVars;
    }

    public TranslationConfig setGenerateGhostVars(boolean generateGhostVars) {
        this.generateGhostVars = generateGhostVars;
        return this;
    }

    public boolean isHandleNullSafety() {
        return handleNullSafety;
    }

    public TranslationConfig setHandleNullSafety(boolean handleNullSafety) {
        this.handleNullSafety = handleNullSafety;
        return this;
    }

    public boolean isAddKeyLemmas() {
        return addKeyLemmas;
    }

    public TranslationConfig setAddKeyLemmas(boolean addKeyLemmas) {
        this.addKeyLemmas = addKeyLemmas;
        return this;
    }

    public boolean isPreserveComments() {
        return preserveComments;
    }

    public TranslationConfig setPreserveComments(boolean preserveComments) {
        this.preserveComments = preserveComments;
        return this;
    }

    public boolean isTranslateQuantifiers() {
        return translateQuantifiers;
    }

    public TranslationConfig setTranslateQuantifiers(boolean translateQuantifiers) {
        this.translateQuantifiers = translateQuantifiers;
        return this;
    }

    public boolean isProcessOldExpressions() {
        return processOldExpressions;
    }

    public TranslationConfig setProcessOldExpressions(boolean processOldExpressions) {
        this.processOldExpressions = processOldExpressions;
        return this;
    }

    public boolean isReplaceResultKeyword() {
        return replaceResultKeyword;
    }

    public TranslationConfig setReplaceResultKeyword(boolean replaceResultKeyword) {
        this.replaceResultKeyword = replaceResultKeyword;
        return this;
    }

    /**
     * Статический метод для создания конфигурации по умолчанию
     */
    public static TranslationConfig defaultConfig() {
        return new TranslationConfig();
    }

    /**
     * Конфигурация для режима минимальной трансформации
     */
    public static TranslationConfig minimalTransformConfig() {
        return new TranslationConfig()
            .setGenerateGhostVars(false)
            .setAddKeyLemmas(false)
            .setProcessOldExpressions(false);
    }

    /**
     * Конфигурация для полной трансформации
     */
    public static TranslationConfig fullTransformConfig() {
        return new TranslationConfig();
    }

    @Override
    public String toString() {
        return "TranslationConfig{" +
            "generateGhostVars=" + generateGhostVars +
            ", handleNullSafety=" + handleNullSafety +
            ", addKeyLemmas=" + addKeyLemmas +
            ", preserveComments=" + preserveComments +
            ", translateQuantifiers=" + translateQuantifiers +
            ", processOldExpressions=" + processOldExpressions +
            ", replaceResultKeyword=" + replaceResultKeyword +
            '}';
    }
}