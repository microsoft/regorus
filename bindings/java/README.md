# Regorus Java

**Regorus** is

  - *Rego*-*Rus(t)*  - A fast, light-weight [Rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
   interpreter written in Rust.
  - *Rigorous* - A rigorous enforcer of well-defined Rego semantics.

See main [Regorus page](https://github.com/microsoft/regorus) for more details about the project.

## Building

Due to operational overhead we don't publish Java bindings to Maven Central
currently (see https://github.com/microsoft/regorus/issues/237) and you need to build from source to use it.

In order to build Regorus Java for a target platform, you need to install Rust target for that platform first:
```bash
$ rustup target add aarch64-apple-darwin
```

Afterwards, you can build native library for that target using:
```bash
$ cargo build --release --target aarch64-apple-darwin
```

You will then have a native library at `../../target/aarch64-apple-darwin/release/libregorus_java.dylib` depending on your target.

You then need to build Java bindings using:
```bash
$ mvn package
```

And you will have a JAR at `./target/regorus-java-0.0.1.jar`.

## Usage

You can use Regorus Java bindings as:

```java
import com.microsoft.regorus.Engine;

public class Test {
    public static void main(String[] args) {
        try (Engine engine = new Engine()) {
            engine.addPolicy(
                "hello.rego",
                "package test\nmessage = concat(\", \", [input.message, data.message])"
            );
            engine.addDataJson("{\"message\":\"World!\"}");
            engine.setInputJson("{\"message\":\"Hello\"}");
            String resJson = engine.evalQuery("data.test.message");

            System.out.println(resJson);
        }
    }
}
```

You need to ensure artifacts built in [previous section](#building) are in Java's classpath.

For example with `java` CLI:
```bash
$ java -Djava.library.path=../../target/aarch64-apple-darwin/release/ -cp target/regorus-java-0.0.1.jar Test.java
```

should gave you the output:
```
{"result":[{"expressions":[{"value":"Hello, World!","text":"data.test.message","location":{"row":1,"col":1}}]}]}
```