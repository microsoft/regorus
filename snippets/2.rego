Cpackage play

a := {4}

mydoc(x) := path {
  path := "data.play.a"
}

x := [ y |
  y := data.play.a | data.play.b with data.play.a as {5} with data.play.b as {6}
]

r := [ m | m := data.play.p with data.play.p as 5 + 6; true  ]


allow {
	input.x 
    == 5 
    
    input.y == 5
    input.y 
    == 5
}