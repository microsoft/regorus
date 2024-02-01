- Install maturin
  ```
  pipx install maturin
  ```
  See [Maturin User Guide](https://www.maturin.rs)
  
- Build bindings for Python
  ```
  cd bindings/python
  maturin build --release --target-dir wheels
  ```
  
- Install python wheel
  ```
  pip3 install ../../target/wheels/regorus*.whl --force-reinstall
  ```
  
- Run test script
  ```
  python3 test.py
  ```
  
