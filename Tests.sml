structure Tests =
struct
  val testsAdd : (IntInf.int * IntInf.int) list = [
    (4000,3334),
    (4,5),
    (3,2),
    (123, 937),
    (1024,1024),
    (0,0),
    (1023,1)
  ]

  val testsSub : (IntInf.int * IntInf.int) list = [
    (4000,3334),
    (3,2),
    (3,3),
    (1024, 937),
    (1024,1),
    (128,126),
    (884,121),
    (65536,1024),
    (65535,1023)
  ]

  val testsMul : (IntInf.int * IntInf.int) list = [
    (4000,3334),
    (3,2),
    (10,7),
    (123, 937),
    (0,0),
    (0,1),
    (1231231, 1),
    (78758399045,89834590)
  ]

end
