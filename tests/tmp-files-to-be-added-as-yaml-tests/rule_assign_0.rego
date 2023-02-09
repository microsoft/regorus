package test

no_assign {
  input.date == "12/1/2022"
}

assign_null = null {
  input.date == "12/1/2022"
}

assign_bool = false {
  input.date == "12/1/2022"
}

assign_int = 101 {
  input.date == "12/1/2022"
}

assign_float = 3.14 {
  input.date == "12/1/2022"
}

assign_string = "test_string" {
  input.date == "12/1/2022"
}
