# Regorus Java

**Regorus** is

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
   interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

See main [Regorus page](https://github.com/microsoft/regorus) for more details about the project.

Regorus can be used in Java via `com.microsoft.regorus` package. (It is not yet available in Maven Central, but can be manually built.)

## Building

You can build this binding using [Maven](https://maven.apache.org/):
```shell
$ mvn package
$ file target/regorus-java-0.0.1*
target/regorus-java-0.0.1-osx-aarch_64.jar: Zip archive data, at least v1.0 to extract, compression method=deflate
target/regorus-java-0.0.1.jar:              Zip archive data, at least v1.0 to extract, compression method=deflate
```

## Usage

```java
import com.microsoft.regorus.Engine;

public class Test {
    public static void main(String[] args) {
        try (Engine engine = new Engine()) {
            engine.pubAddPolicy(
                "hello.rego",
                "package test\nmessage = concat(\", \", [input.message, data.message])"
            );
            engine.pubAddDataJson("{\"message\":\"World!\"}");
            engine.pubSetInputJson("{\"message\":\"Hello\"}");
            String resJson = engine.pubEvalQuery("data.test.message");

            System.out.println(resJson);
        }
    }
}
```

and run it with:
```shell
$ java -cp target/regorus-java-0.0.1.jar:target/regorus-java-0.0.1-osx-aarch_64.jar Test.java
{"result":[{"expressions":[{"value":"Hello, World!","text":"data.test.message","location":{"row":1,"col":1}}]}]}
```