JML Key Translator

JML Key Translator — это инструмент для трансляции JML-аннотаций в Java-код, пригодный для верификации в KeY. Поддерживает обработку как отдельных файлов, так и целых директорий.

Структура проекта:

jml-key-translator/
  ├── src/
  │   └── main/
  │       └── java/
  │           └── com/spbu/jmltranslator/
  │               ├── JmlKeyTranslator.java      # Трансляция одного файла
  │               ├── JmlBatchTranslator.java    # Пакетная трансляция
  │               └── ...                        # Остальные классы
  └── target/                  # Сюда Maven кладёт собранные .jar-файлы

Требования:
- Java 11 или новее (JDK)
- Maven (https://maven.apache.org/download.cgi)
- PowerShell (по умолчанию есть в Windows)

Сборка проекта:
1. Откройте PowerShell и перейдите в папку проекта:
   cd путь\к\папке\jml-key-translator
2. Соберите проект с помощью Maven:
   mvn clean package
   После успешной сборки появится файл target/jml-key-translator-1.0.jar

Запуск транслятора:
1. Трансляция одного файла:
   java -cp target/jml-key-translator-1.0.jar com.spbu.jmltranslator.JmlKeyTranslator путь\к\входному\файлу.java путь\к\выходному\файлу.java
   Пример:
   java -cp target/jml-key-translator-1.0.jar com.spbu.jmltranslator.JmlKeyTranslator test_files\Account.java output_test\Account_key.java

2. Пакетная трансляция (всей папки):
   java -cp target/jml-key-translator-1.0.jar com.spbu.jmltranslator.JmlBatchTranslator путь\к\входной\папке путь\к\выходной\папке
   Пример:
   java -cp target/jml-key-translator-1.0.jar com.spbu.jmltranslator.JmlBatchTranslator test_files output_test
   В выходной папке появятся файлы только для тех методов, которые содержат JML-аннотации.

---

Контакты:
Если возникли вопросы по работе транслятора или интеграции с KeY, пишите в Issues на GitHub или напрямую автору (lylyca326@gmail.com).

---

Если нужно добавить или изменить какие-то детали (например, описание опций трансляции, FAQ по KeY, примеры JML-аннотаций) — уточните, и я дополню README.