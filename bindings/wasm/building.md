
- Install `wasm-pack`
  ```
  cargo install wasm-pack
  ```

- Build `regorusjs` for nodejs.
  ```
  wasm-pack build --target nodejs --release
  ```

- Install [nodejs](https://nodejs.org/en/download)

- Run the test script
  ```
  $ node test.js
  \\{
  \\  "result": [
  \\    {
  \\      "expressions": [
  \\        {
  \\          "value": "Hello, World!",
  \\          "text": "data.test.message",
  \\          "location": {
  \\            "row": 1,
  \\            "col": 1
  \\          }
  \\        }
  \\      ]
  \\    }
  \\   ]
  \\}
  ```
