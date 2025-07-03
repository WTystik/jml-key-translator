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
- PowerShell (по умолчанию есть в Windows)

Сборка и запуск проекта (через консоль)
=====================================================

1. Перейдите в папку с исходниками:
   cd C:\Users\...\summer\jml-key-translator\src\main\java

2. Скомпилируйте все .java-файлы в папку target/classes:
   javac -d ..\..\..\..\target\classes com\spbu\jmltranslator\*.java com\spbu\jmltranslator\fileio\*.java com\spbu\jmltranslator\model\*.java com\spbu\jmltranslator\translator\*.java

3. Перейдите в корень проекта:
   cd C:\Users\...\summer\jml-key-translator

4. Запустите пакетную трансляцию (пример для вашего ПК):
   java -cp target\classes com.spbu.jmltranslator.JmlBatchTranslator C:\Users\...\summer\test_files C:\...\Desktop\summer\output_test

В папке output_test появятся файлы только для тех методов, которые содержат JML-аннотации.

---

Контакты:
Если возникли вопросы по работе транслятора или интеграции с KeY, пишите в Issues на GitHub или напрямую автору (lylyca326@gmail.com).

---

Если нужно добавить или изменить какие-то детали (например, описание опций трансляции, FAQ по KeY, примеры JML-аннотаций) — уточните, и я дополню README.
